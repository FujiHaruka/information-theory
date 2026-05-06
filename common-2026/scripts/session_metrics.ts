#!/usr/bin/env -S deno run -A
// session_metrics.ts — extract objective metrics from Claude Code JSONL session logs.
//
// Usage:
//   deno run -A scripts/session_metrics.ts <manifest.json> [--render-md] [--out <dir>]
//   deno run -A scripts/session_metrics.ts --discover [--file-prefix <s>] [--logs-dir <dir>]
//   deno run -A scripts/session_metrics.ts --turns <session-id> [--logs-dir <dir>]
//
// Manifest schema (JSON):
//   {
//     "problem": "東大 2026 第1問",
//     "proof_log": "docs/proof-log-todai-2026-q1.md",
//     "sessions": [{
//       "id": "1e57b25f-...",
//       "prompt_ids": ["444dfbd8", "e386bbf9"],   // optional, prefix match supported
//       "note": "作成セッション"
//     }],
//     "filters": { "file_prefix": "Common2026/T_Q1" },
//     "idle_gap_minutes": 5,
//     "logs_dir": "/Users/.../-Users-..."  // optional override
//   }
//
// To discover which prompt_ids correspond to the problem-solving turns within
// a session, run `--turns <session-id>` and pick the rows whose user prompts
// frame the solve. Then list those prompt_id prefixes in the manifest.

const HOME = Deno.env.get("HOME")!;

function defaultLogsDir(): string {
  const cwd = Deno.cwd();
  const encoded = cwd.replaceAll(/[/.]/g, "-");
  return `${HOME}/.claude/projects/${encoded}`;
}

// ──────────────────────────────────────────────────────────────────────────
// Types

interface ManifestSession {
  id: string;
  note?: string;
  /** Prompt-id prefixes (or full UUIDs) that scope this session to specific turns. */
  prompt_ids?: string[];
}

interface Manifest {
  problem: string;
  proof_log?: string;
  sessions: ManifestSession[];
  filters?: { file_prefix?: string };
  idle_gap_minutes?: number;
  logs_dir?: string;
}

interface TokenUsage {
  input: number;
  output: number;
  cache_read: number;
  cache_creation: number;
}

interface SessionMetrics {
  id: string;
  note?: string;
  start: string | null;
  end: string | null;
  wall_time_seconds: number;
  active_time_seconds: number;
  turns: number;
  tool_calls: Record<string, number>;
  bash_breakdown: Record<string, number>;
  bash_total: number;
  edits_by_file: Record<string, number>;
  writes_by_file: Record<string, number>;
  reads_by_file: Record<string, number>;
  matched_edits: number;
  matched_writes: number;
  tool_errors: number;
  tokens: TokenUsage;
  models: string[];
  sidechain_entries: number;
}

interface AggregateMetrics {
  problem: string;
  proof_log?: string;
  generated_at: string;
  filters?: Manifest["filters"];
  idle_gap_minutes: number;
  sessions: SessionMetrics[];
  totals: Omit<SessionMetrics, "id" | "note">;
}

// ──────────────────────────────────────────────────────────────────────────
// Bash classification

function classifyBash(rawCmd: string): string {
  // Strip leading `cd <path> && ` chain so we look at the actual command.
  let cmd = rawCmd.trim();
  while (cmd.startsWith("cd ")) {
    const idx = cmd.indexOf("&&");
    if (idx < 0) break;
    cmd = cmd.slice(idx + 2).trim();
  }
  // Strip transparent wrappers that don't change the command's identity:
  // `time …`, `nohup …`, `command …`, `env VAR=… …`. Loop because they can
  // chain (e.g. `nohup time lake env lean`).
  let stripped = true;
  while (stripped) {
    stripped = false;
    if (/^(time|nohup|command)\s+/.test(cmd)) {
      cmd = cmd.replace(/^(time|nohup|command)\s+/, "");
      stripped = true;
    } else if (/^env\s+[A-Za-z_][A-Za-z0-9_]*=/.test(cmd)) {
      // Drop env VAR=value tokens until we reach the actual command.
      cmd = cmd.replace(/^env(\s+[A-Za-z_][A-Za-z0-9_]*=\S+)+\s+/, "");
      stripped = true;
    }
  }
  // Special: lake subcommands
  if (/^lake\s+env\s+lean\b/.test(cmd)) return "lake_env_lean";
  if (/^lake\s+build\b/.test(cmd)) return "lake_build";
  if (/^lake\b/.test(cmd)) return "lake_other";
  const first = cmd.split(/\s+/, 1)[0] ?? "";
  const known = new Set([
    "grep", "rg", "find", "ls", "git", "cat", "head", "tail",
    "echo", "python3", "python", "node", "deno", "mkdir", "mv",
    "cp", "rm", "awk", "sed", "wc", "diff", "which", "test",
  ]);
  if (known.has(first)) return first;
  return "other";
}

// ──────────────────────────────────────────────────────────────────────────
// Per-session parser

function emptySession(id: string, note?: string): SessionMetrics {
  return {
    id,
    note,
    start: null,
    end: null,
    wall_time_seconds: 0,
    active_time_seconds: 0,
    turns: 0,
    tool_calls: {},
    bash_breakdown: {},
    bash_total: 0,
    edits_by_file: {},
    writes_by_file: {},
    reads_by_file: {},
    matched_edits: 0,
    matched_writes: 0,
    tool_errors: 0,
    tokens: { input: 0, output: 0, cache_read: 0, cache_creation: 0 },
    models: [],
    sidechain_entries: 0,
  };
}

function bumpFile(map: Record<string, number>, fp: string, repoRoot: string) {
  const norm = fp.startsWith(repoRoot + "/")
    ? fp.slice(repoRoot.length + 1)
    : fp;
  map[norm] = (map[norm] ?? 0) + 1;
}

function promptMatches(currentPid: string | null, prefixes: string[] | undefined): boolean {
  if (!prefixes || prefixes.length === 0) return true;
  if (!currentPid) return false;
  return prefixes.some((p) => currentPid.startsWith(p));
}

async function parseSession(
  jsonlPath: string,
  id: string,
  note: string | undefined,
  filePrefix: string | undefined,
  idleGapSec: number,
  repoRoot: string,
  promptIdPrefixes: string[] | undefined,
): Promise<SessionMetrics> {
  const text = await Deno.readTextFile(jsonlPath);
  const m = emptySession(id, note);
  const requestIds = new Set<string>();
  const modelsSet = new Set<string>();
  const timestamps: number[] = [];
  let currentPid: string | null = null;

  for (const line of text.split("\n")) {
    if (!line) continue;
    let d: any;
    try {
      d = JSON.parse(line);
    } catch {
      continue;
    }
    if (typeof d.promptId === "string") currentPid = d.promptId;
    const inScope = promptMatches(currentPid, promptIdPrefixes);
    if (!inScope) continue;

    const ts: string | undefined = d.timestamp;
    if (ts) {
      const t = Date.parse(ts);
      if (!Number.isNaN(t)) timestamps.push(t);
    }
    if (d.isSidechain) m.sidechain_entries += 1;
    if (d.requestId) requestIds.add(d.requestId);

    const msg = d.message ?? {};
    if (d.type === "assistant") {
      if (typeof msg.model === "string") modelsSet.add(msg.model);
      const u = msg.usage ?? {};
      m.tokens.input += u.input_tokens ?? 0;
      m.tokens.output += u.output_tokens ?? 0;
      m.tokens.cache_read += u.cache_read_input_tokens ?? 0;
      m.tokens.cache_creation += u.cache_creation_input_tokens ?? 0;
    }

    const content = msg.content;
    if (Array.isArray(content)) {
      for (const c of content) {
        if (!c || typeof c !== "object") continue;
        if (c.type === "tool_use") {
          const name: string = c.name ?? "?";
          m.tool_calls[name] = (m.tool_calls[name] ?? 0) + 1;
          const input = c.input ?? {};
          if (name === "Bash" && typeof input.command === "string") {
            const cat = classifyBash(input.command);
            m.bash_breakdown[cat] = (m.bash_breakdown[cat] ?? 0) + 1;
            m.bash_total += 1;
          } else if (name === "Edit" && typeof input.file_path === "string") {
            bumpFile(m.edits_by_file, input.file_path, repoRoot);
            if (filePrefix && input.file_path.includes(filePrefix)) m.matched_edits += 1;
          } else if (name === "Write" && typeof input.file_path === "string") {
            bumpFile(m.writes_by_file, input.file_path, repoRoot);
            if (filePrefix && input.file_path.includes(filePrefix)) m.matched_writes += 1;
          } else if (name === "Read" && typeof input.file_path === "string") {
            bumpFile(m.reads_by_file, input.file_path, repoRoot);
          }
        } else if (c.type === "tool_result") {
          if (c.is_error === true) m.tool_errors += 1;
        }
      }
    }
  }

  timestamps.sort((a, b) => a - b);
  if (timestamps.length > 0) {
    m.start = new Date(timestamps[0]).toISOString();
    m.end = new Date(timestamps[timestamps.length - 1]).toISOString();
    m.wall_time_seconds = Math.round((timestamps[timestamps.length - 1] - timestamps[0]) / 1000);
    let active = 0;
    for (let i = 1; i < timestamps.length; i++) {
      const gap = (timestamps[i] - timestamps[i - 1]) / 1000;
      active += Math.min(gap, idleGapSec);
    }
    m.active_time_seconds = Math.round(active);
  }
  m.turns = requestIds.size;
  m.models = [...modelsSet];
  return m;
}

// ──────────────────────────────────────────────────────────────────────────
// Aggregation

function aggregate(sessions: SessionMetrics[]): Omit<SessionMetrics, "id" | "note"> {
  const t: Omit<SessionMetrics, "id" | "note"> = {
    start: null,
    end: null,
    wall_time_seconds: 0,
    active_time_seconds: 0,
    turns: 0,
    tool_calls: {},
    bash_breakdown: {},
    bash_total: 0,
    edits_by_file: {},
    writes_by_file: {},
    reads_by_file: {},
    matched_edits: 0,
    matched_writes: 0,
    tool_errors: 0,
    tokens: { input: 0, output: 0, cache_read: 0, cache_creation: 0 },
    models: [],
    sidechain_entries: 0,
  };
  const modelsSet = new Set<string>();
  const startTs: number[] = [];
  const endTs: number[] = [];
  for (const s of sessions) {
    t.wall_time_seconds += s.wall_time_seconds;
    t.active_time_seconds += s.active_time_seconds;
    t.turns += s.turns;
    t.bash_total += s.bash_total;
    t.matched_edits += s.matched_edits;
    t.matched_writes += s.matched_writes;
    t.tool_errors += s.tool_errors;
    t.sidechain_entries += s.sidechain_entries;
    t.tokens.input += s.tokens.input;
    t.tokens.output += s.tokens.output;
    t.tokens.cache_read += s.tokens.cache_read;
    t.tokens.cache_creation += s.tokens.cache_creation;
    for (const [k, v] of Object.entries(s.tool_calls)) t.tool_calls[k] = (t.tool_calls[k] ?? 0) + v;
    for (const [k, v] of Object.entries(s.bash_breakdown)) t.bash_breakdown[k] = (t.bash_breakdown[k] ?? 0) + v;
    for (const [k, v] of Object.entries(s.edits_by_file)) t.edits_by_file[k] = (t.edits_by_file[k] ?? 0) + v;
    for (const [k, v] of Object.entries(s.writes_by_file)) t.writes_by_file[k] = (t.writes_by_file[k] ?? 0) + v;
    for (const [k, v] of Object.entries(s.reads_by_file)) t.reads_by_file[k] = (t.reads_by_file[k] ?? 0) + v;
    for (const m of s.models) modelsSet.add(m);
    if (s.start) startTs.push(Date.parse(s.start));
    if (s.end) endTs.push(Date.parse(s.end));
  }
  t.models = [...modelsSet];
  if (startTs.length) t.start = new Date(Math.min(...startTs)).toISOString();
  if (endTs.length) t.end = new Date(Math.max(...endTs)).toISOString();
  return t;
}

// ──────────────────────────────────────────────────────────────────────────
// Markdown rendering

function fmtDuration(sec: number): string {
  const h = Math.floor(sec / 3600);
  const m = Math.floor((sec % 3600) / 60);
  const s = sec % 60;
  if (h > 0) return `${h}h ${m}m`;
  if (m > 0) return `${m}m ${s}s`;
  return `${s}s`;
}

function fmtThousands(n: number): string {
  return n.toLocaleString("en-US");
}

function renderMarkdown(agg: AggregateMetrics): string {
  const t = agg.totals;
  const lines: string[] = [];
  lines.push(`# ${agg.problem} — 定量メトリクス（自動生成）`);
  lines.push("");
  lines.push(`Generated: ${agg.generated_at}`);
  lines.push(`Idle gap threshold: ${agg.idle_gap_minutes} min`);
  if (agg.filters?.file_prefix) lines.push(`File prefix filter: \`${agg.filters.file_prefix}\``);
  lines.push("");
  lines.push("## サマリー（合計）");
  lines.push("");
  lines.push("| 項目 | 値 |");
  lines.push("|---|---|");
  lines.push(`| セッション数 | ${agg.sessions.length} |`);
  lines.push(`| 期間 | ${t.start ?? "-"} 〜 ${t.end ?? "-"} |`);
  lines.push(`| Wall time（合計） | ${fmtDuration(t.wall_time_seconds)} |`);
  lines.push(`| Active time（idle 除外） | ${fmtDuration(t.active_time_seconds)} |`);
  lines.push(`| LLM ターン数 | ${t.turns} |`);
  const totalToolCalls = Object.values(t.tool_calls).reduce((a, b) => a + b, 0);
  lines.push(`| ツールコール総数 | ${totalToolCalls} |`);
  lines.push(`| ツール失敗回数 | ${t.tool_errors} |`);
  lines.push(`| サブエージェント側 entries | ${t.sidechain_entries} |`);
  if (agg.filters?.file_prefix) {
    lines.push(`| 対象ファイル Edit 回数 | ${t.matched_edits} |`);
    lines.push(`| 対象ファイル Write 回数 | ${t.matched_writes} |`);
  }
  lines.push(`| Models | ${t.models.join(", ")} |`);
  lines.push("");
  lines.push("## ツールコール内訳");
  lines.push("");
  lines.push("| Tool | Count |");
  lines.push("|---|---|");
  for (const [k, v] of Object.entries(t.tool_calls).sort((a, b) => b[1] - a[1])) {
    lines.push(`| ${k} | ${v} |`);
  }
  lines.push("");
  lines.push("## Bash 内訳");
  lines.push("");
  lines.push("| Category | Count |");
  lines.push("|---|---|");
  for (const [k, v] of Object.entries(t.bash_breakdown).sort((a, b) => b[1] - a[1])) {
    lines.push(`| \`${k}\` | ${v} |`);
  }
  lines.push("");
  lines.push("## 編集ファイル別 Edit/Write 回数");
  lines.push("");
  const files = new Set<string>([
    ...Object.keys(t.edits_by_file),
    ...Object.keys(t.writes_by_file),
  ]);
  if (files.size > 0) {
    lines.push("| File | Edit | Write |");
    lines.push("|---|---|---|");
    for (const f of [...files].sort()) {
      lines.push(`| \`${f}\` | ${t.edits_by_file[f] ?? 0} | ${t.writes_by_file[f] ?? 0} |`);
    }
  } else {
    lines.push("(なし)");
  }
  lines.push("");
  lines.push("## トークン使用量");
  lines.push("");
  lines.push("| 項目 | tokens |");
  lines.push("|---|---|");
  lines.push(`| input | ${fmtThousands(t.tokens.input)} |`);
  lines.push(`| output | ${fmtThousands(t.tokens.output)} |`);
  lines.push(`| cache_read | ${fmtThousands(t.tokens.cache_read)} |`);
  lines.push(`| cache_creation | ${fmtThousands(t.tokens.cache_creation)} |`);
  lines.push("");

  if (agg.sessions.length > 1) {
    lines.push("## セッション別");
    lines.push("");
    lines.push("| Session | Note | Start | Wall | Active | Turns | ToolCalls | Bash | Edit | Write | Errors |");
    lines.push("|---|---|---|---|---|---|---|---|---|---|---|");
    for (const s of agg.sessions) {
      const tc = Object.values(s.tool_calls).reduce((a, b) => a + b, 0);
      const ed = Object.values(s.edits_by_file).reduce((a, b) => a + b, 0);
      const wr = Object.values(s.writes_by_file).reduce((a, b) => a + b, 0);
      lines.push(
        `| \`${s.id.slice(0, 8)}\` | ${s.note ?? ""} | ${s.start ?? "-"} | ${fmtDuration(s.wall_time_seconds)} | ${fmtDuration(s.active_time_seconds)} | ${s.turns} | ${tc} | ${s.bash_total} | ${ed} | ${wr} | ${s.tool_errors} |`,
      );
    }
    lines.push("");
  }
  return lines.join("\n");
}

// ──────────────────────────────────────────────────────────────────────────
// Discover mode

async function discover(filePrefix: string | undefined, logsDir: string) {
  const repoRoot = Deno.cwd();
  const entries: Array<{ id: string; row: SessionMetrics }> = [];
  for await (const e of Deno.readDir(logsDir)) {
    if (!e.isFile || !e.name.endsWith(".jsonl")) continue;
    const id = e.name.replace(/\.jsonl$/, "");
    try {
      const m = await parseSession(`${logsDir}/${e.name}`, id, undefined, filePrefix, 5 * 60, repoRoot, undefined);
      // Only show sessions that have any matched activity, or all if no prefix
      const hits = filePrefix
        ? (m.matched_edits + m.matched_writes +
          Object.keys(m.edits_by_file).filter((k) => k.includes(filePrefix)).length +
          Object.keys(m.reads_by_file).filter((k) => k.includes(filePrefix)).length)
        : 1;
      if (hits > 0) entries.push({ id, row: m });
    } catch (err) {
      console.error(`skip ${id}: ${err}`);
    }
  }
  entries.sort((a, b) => (a.row.start ?? "").localeCompare(b.row.start ?? ""));
  console.log("session   start                wall    edits  writes  reads  bash  tool_calls  models");
  for (const { id, row } of entries) {
    const ed = Object.values(row.edits_by_file).reduce((a, b) => a + b, 0);
    const wr = Object.values(row.writes_by_file).reduce((a, b) => a + b, 0);
    const rd = Object.values(row.reads_by_file).reduce((a, b) => a + b, 0);
    const tc = Object.values(row.tool_calls).reduce((a, b) => a + b, 0);
    console.log(
      `${id.slice(0, 8)}  ${(row.start ?? "").slice(0, 19).padEnd(19)}  ${fmtDuration(row.wall_time_seconds).padStart(6)}  ${String(ed).padStart(5)}  ${String(wr).padStart(6)}  ${String(rd).padStart(5)}  ${String(row.bash_total).padStart(4)}  ${String(tc).padStart(10)}  ${row.models.join(",")}`,
    );
  }
}

// ──────────────────────────────────────────────────────────────────────────
// Turns mode — list per-promptId breakdown of a single session

interface TurnRow {
  prompt_id: string;
  start: string | null;
  end: string | null;
  duration_seconds: number;
  user_text: string | null;
  tool_uses: number;
  bash: number;
  edits: number;
  writes: number;
  matched_edits: number;
  matched_writes: number;
  files_touched: string[];
}

/**
 * Resolve a possibly-abbreviated session id to a full JSONL path. Accepts the
 * full UUID or any prefix that uniquely matches a `*.jsonl` file in `logsDir`,
 * which is what users naturally have at hand from `--discover` (8-char prefix).
 */
async function resolveSessionPath(sessionId: string, logsDir: string): Promise<{ id: string; path: string }> {
  const exact = `${logsDir}/${sessionId}.jsonl`;
  try {
    const stat = await Deno.stat(exact);
    if (stat.isFile) return { id: sessionId, path: exact };
  } catch {
    // fall through to prefix search
  }
  const matches: string[] = [];
  for await (const entry of Deno.readDir(logsDir)) {
    if (!entry.isFile || !entry.name.endsWith(".jsonl")) continue;
    if (entry.name.startsWith(sessionId)) matches.push(entry.name.replace(/\.jsonl$/, ""));
  }
  if (matches.length === 0) {
    throw new Error(`session not found: no JSONL in ${logsDir} matches "${sessionId}"`);
  }
  if (matches.length > 1) {
    throw new Error(
      `session id "${sessionId}" is ambiguous — matches: ${matches.join(", ")}. Use a longer prefix.`,
    );
  }
  return { id: matches[0], path: `${logsDir}/${matches[0]}.jsonl` };
}

async function listTurns(sessionId: string, logsDir: string, filePrefix: string | undefined): Promise<TurnRow[]> {
  const repoRoot = Deno.cwd();
  const { path } = await resolveSessionPath(sessionId, logsDir);
  const text = await Deno.readTextFile(path);
  const turns = new Map<string, TurnRow>();
  let currentPid: string | null = null;

  const ensure = (pid: string): TurnRow => {
    let row = turns.get(pid);
    if (!row) {
      row = {
        prompt_id: pid,
        start: null,
        end: null,
        duration_seconds: 0,
        user_text: null,
        tool_uses: 0,
        bash: 0,
        edits: 0,
        writes: 0,
        matched_edits: 0,
        matched_writes: 0,
        files_touched: [],
      };
      turns.set(pid, row);
    }
    return row;
  };

  const filesPerTurn = new Map<string, Set<string>>();

  for (const line of text.split("\n")) {
    if (!line) continue;
    let d: any;
    try {
      d = JSON.parse(line);
    } catch {
      continue;
    }
    if (typeof d.promptId === "string") currentPid = d.promptId;
    if (!currentPid) continue;
    const row = ensure(currentPid);
    let files = filesPerTurn.get(currentPid);
    if (!files) {
      files = new Set();
      filesPerTurn.set(currentPid, files);
    }

    const ts: string | undefined = d.timestamp;
    if (ts) {
      if (row.start === null || ts < row.start) row.start = ts;
      if (row.end === null || ts > row.end) row.end = ts;
    }

    const msg = d.message ?? {};
    const content = msg.content;
    if (d.type === "user" && typeof content === "string") {
      // Skip system-injected wrapper messages.
      if (content && !content.startsWith("<") && row.user_text === null) {
        row.user_text = content.split("\n")[0].slice(0, 80);
      }
    }
    if (Array.isArray(content)) {
      for (const c of content) {
        if (!c || typeof c !== "object") continue;
        if (c.type === "tool_use") {
          row.tool_uses += 1;
          const name: string = c.name ?? "";
          const input = c.input ?? {};
          if (name === "Bash") row.bash += 1;
          if (name === "Edit") {
            row.edits += 1;
            if (typeof input.file_path === "string") {
              const norm = input.file_path.startsWith(repoRoot + "/")
                ? input.file_path.slice(repoRoot.length + 1)
                : input.file_path;
              files.add(norm);
              if (filePrefix && input.file_path.includes(filePrefix)) row.matched_edits += 1;
            }
          }
          if (name === "Write") {
            row.writes += 1;
            if (typeof input.file_path === "string") {
              const norm = input.file_path.startsWith(repoRoot + "/")
                ? input.file_path.slice(repoRoot.length + 1)
                : input.file_path;
              files.add(norm);
              if (filePrefix && input.file_path.includes(filePrefix)) row.matched_writes += 1;
            }
          }
        }
      }
    }
  }

  for (const [pid, row] of turns) {
    if (row.start && row.end) {
      row.duration_seconds = Math.round((Date.parse(row.end) - Date.parse(row.start)) / 1000);
    }
    row.files_touched = [...(filesPerTurn.get(pid) ?? new Set())].sort();
  }

  return [...turns.values()].sort((a, b) => (a.start ?? "").localeCompare(b.start ?? ""));
}

function printTurns(rows: TurnRow[]) {
  console.log("prompt_id  start             dur     tools  bash  edit  write  user / files");
  for (const r of rows) {
    const startCol = (r.start ?? "").slice(11, 19).padEnd(8);
    const dur = fmtDuration(r.duration_seconds).padStart(6);
    const filesStr = r.files_touched.length > 0 ? `[${r.files_touched.join(", ")}]` : "";
    const userStr = r.user_text ?? "";
    console.log(
      `${r.prompt_id.slice(0, 8)}   ${startCol}          ${dur}  ${String(r.tool_uses).padStart(5)}  ${String(r.bash).padStart(4)}  ${String(r.edits).padStart(4)}  ${String(r.writes).padStart(5)}  ${userStr}`,
    );
    if (filesStr) console.log(`            ${" ".repeat(8)}          ${" ".repeat(6)}                                ${filesStr}`);
  }
}

// ──────────────────────────────────────────────────────────────────────────
// CLI

function parseArgs(argv: string[]) {
  const args: Record<string, string | boolean> = {};
  const positional: string[] = [];
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a.startsWith("--")) {
      const key = a.slice(2);
      const next = argv[i + 1];
      if (next && !next.startsWith("--")) {
        args[key] = next;
        i += 1;
      } else {
        args[key] = true;
      }
    } else {
      positional.push(a);
    }
  }
  return { args, positional };
}

async function main() {
  const { args, positional } = parseArgs(Deno.args);
  const logsDir = (args["logs-dir"] as string | undefined) ?? defaultLogsDir();

  if (args.discover) {
    await discover(args["file-prefix"] as string | undefined, logsDir);
    return;
  }

  if (typeof args.turns === "string") {
    const rows = await listTurns(args.turns, logsDir, args["file-prefix"] as string | undefined);
    if (args.json) {
      console.log(JSON.stringify(rows, null, 2));
    } else {
      printTurns(rows);
    }
    return;
  }

  if (positional.length === 0) {
    console.error("Usage: session_metrics.ts <manifest.json> [--render-md] [--out <dir>]");
    console.error("       session_metrics.ts --discover [--file-prefix <s>] [--logs-dir <dir>]");
    console.error("       session_metrics.ts --turns <session-id> [--file-prefix <s>] [--json]");
    Deno.exit(1);
  }

  const manifestPath = positional[0];
  const manifest: Manifest = JSON.parse(await Deno.readTextFile(manifestPath));
  const idleGapSec = (manifest.idle_gap_minutes ?? 5) * 60;
  const filePrefix = manifest.filters?.file_prefix;
  const sessionsLogsDir = manifest.logs_dir ?? logsDir;
  const repoRoot = Deno.cwd();

  const sessions: SessionMetrics[] = [];
  for (const s of manifest.sessions) {
    const { id: resolvedId, path } = await resolveSessionPath(s.id, sessionsLogsDir);
    const m = await parseSession(path, resolvedId, s.note, filePrefix, idleGapSec, repoRoot, s.prompt_ids);
    sessions.push(m);
  }

  const agg: AggregateMetrics = {
    problem: manifest.problem,
    proof_log: manifest.proof_log,
    generated_at: new Date().toISOString(),
    filters: manifest.filters,
    idle_gap_minutes: manifest.idle_gap_minutes ?? 5,
    sessions,
    totals: aggregate(sessions),
  };

  // Output paths: alongside the manifest, with `.metrics.json` / `.metrics.md` suffix.
  const outDir = (args.out as string | undefined) ??
    (manifestPath.replace(/[^/]+$/, "").replace(/\/$/, "") || ".");
  const base = manifestPath.split("/").pop()!.replace(/\.manifest\.json$/, "").replace(/\.json$/, "");
  const jsonOut = `${outDir}/${base}.metrics.json`;
  await Deno.writeTextFile(jsonOut, JSON.stringify(agg, null, 2) + "\n");
  console.log(`wrote ${jsonOut}`);

  if (args["render-md"]) {
    const mdOut = `${outDir}/${base}.metrics.md`;
    await Deno.writeTextFile(mdOut, renderMarkdown(agg) + "\n");
    console.log(`wrote ${mdOut}`);
  }
}

if (import.meta.main) {
  await main();
}
