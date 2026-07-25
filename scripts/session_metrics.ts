#!/usr/bin/env -S deno run -A
// session_metrics.ts — extract objective metrics from Claude Code JSONL session logs.
//
// Usage:
//   deno run -A scripts/session_metrics.ts <manifest.json> [--render-md] [--out <dir>]
//   deno run -A scripts/session_metrics.ts --discover [--file-prefix <s>] [--logs-dir <dir>]
//   deno run -A scripts/session_metrics.ts --turns <session-id> [--logs-dir <dir>]
//
// Subagent transcripts:
//   The harness writes each dispatched subagent's own transcript to
//   `<logs-dir>/<session-id>/subagents/agent-<name>-<hash>.jsonl` (with a sibling
//   `.meta.json` naming the agent). Those entries never appear in the parent
//   transcript, so an orchestrator-style session that dispatches its work would
//   otherwise measure only supervision effort. They are picked up automatically;
//   pass `--no-subagents` to measure the orchestrator transcript alone.
//
// Manifest schema (JSON):
//   {
//     "problem": "Shannon Ch.7 channel coding theorem",
//     "proof_log": "docs/proof-logs/proof-log-channel-coding.md",
//     "sessions": [{
//       "id": "1e57b25f-...",
//       "prompt_ids": ["444dfbd8", "e386bbf9"],   // optional, prefix match supported
//       "note": "作成セッション"
//     }],
//     "filters": { "file_prefix": "InformationTheory/Shannon/ChannelCoding" },
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
  /** Per-subagent rows for the agents this session dispatched (empty when none). */
  subagents: SubagentMetrics[];
}

/** One dispatched subagent's transcript, annotated from its sibling `.meta.json`. */
interface SubagentMetrics extends SessionMetrics {
  /** Agent name as dispatched (`marton-covering`), from the transcript filename. */
  agent_name: string;
  /** `.meta.json` `agentType` — usually identical to `agent_name`. */
  agent_type?: string;
  /** `.meta.json` `customAgentType` — the agent definition used (`lean-implementer` …). */
  custom_agent_type?: string;
  /** `.meta.json` `description` — the one-line task summary given at dispatch. */
  description?: string;
}

/** The counter-only view of a session, as used for every totals block. */
type Totals = Omit<SessionMetrics, "id" | "note" | "subagents">;

interface AggregateMetrics {
  problem: string;
  proof_log?: string;
  generated_at: string;
  filters?: Manifest["filters"];
  idle_gap_minutes: number;
  sessions: SessionMetrics[];
  /** Orchestrator transcripts only — the historical meaning of this field. */
  totals: Totals;
  /** Dispatched subagent transcripts only. */
  subagent_totals: Totals;
  /**
   * Orchestrator + subagents. Counters are summed; `wall_time_seconds` /
   * `active_time_seconds` are recomputed from the union of all timestamps per
   * session, since a subagent runs inside its parent's wall clock and summing
   * the two would double-count elapsed time.
   */
  combined_totals: Totals;
  /** Number of subagent transcripts folded into `subagent_totals`. */
  subagent_count: number;
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
    subagents: [],
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

/** A parsed transcript plus the raw epoch-ms timestamps behind its time fields. */
interface ParsedSession {
  metrics: SessionMetrics;
  /** Ascending, in-scope entry timestamps — used to union spans across transcripts. */
  timestamps: number[];
}

/** Collapse a sorted timestamp list into wall / active seconds and a start–end span. */
function spanOf(timestamps: number[], idleGapSec: number) {
  if (timestamps.length === 0) {
    return { start: null, end: null, wall_time_seconds: 0, active_time_seconds: 0 };
  }
  const first = timestamps[0];
  const last = timestamps[timestamps.length - 1];
  let active = 0;
  for (let i = 1; i < timestamps.length; i++) {
    active += Math.min((timestamps[i] - timestamps[i - 1]) / 1000, idleGapSec);
  }
  return {
    start: new Date(first).toISOString(),
    end: new Date(last).toISOString(),
    wall_time_seconds: Math.round((last - first) / 1000),
    active_time_seconds: Math.round(active),
  };
}

async function parseSession(
  jsonlPath: string,
  id: string,
  note: string | undefined,
  filePrefix: string | undefined,
  idleGapSec: number,
  repoRoot: string,
  promptIdPrefixes: string[] | undefined,
): Promise<ParsedSession> {
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
  Object.assign(m, spanOf(timestamps, idleGapSec));
  m.turns = requestIds.size;
  m.models = [...modelsSet];
  return { metrics: m, timestamps };
}

// ──────────────────────────────────────────────────────────────────────────
// Subagent transcripts
//
// A dispatched subagent gets its own transcript under `<session>/subagents/`,
// never merged into the parent's. Each entry there carries the *parent's*
// `promptId`, so a manifest's `prompt_ids` scoping applies unchanged.

/** The `.meta.json` fields we surface; the harness writes more than these. */
interface AgentMeta {
  agentType?: string;
  customAgentType?: string;
  description?: string;
  name?: string;
}

/**
 * Display name for one subagent transcript. A named dispatch carries `name`;
 * an unnamed one is identified by its agent definition plus a hash tail, since
 * several dispatches can share that definition.
 */
async function agentLabel(dir: string, base: string): Promise<string> {
  let meta: AgentMeta = {};
  try {
    meta = JSON.parse(await Deno.readTextFile(`${dir}/${base}.meta.json`));
  } catch {
    // meta is a convenience: an unreadable one costs labels, not metrics
  }
  return meta.name ??
    (meta.agentType ? `${meta.agentType}#${base.slice(-6)}` : base.replace(/^agent-/, ""));
}

/**
 * Transcripts of the subagents a session dispatched, sorted by start time.
 * A session with no `subagents/` directory (any run before the harness wrote
 * them, or one that dispatched nothing) yields an empty list rather than an error.
 */
async function parseSubagents(
  sessionJsonlPath: string,
  filePrefix: string | undefined,
  idleGapSec: number,
  repoRoot: string,
  promptIdPrefixes: string[] | undefined,
): Promise<Array<{ metrics: SubagentMetrics; timestamps: number[] }>> {
  const dir = `${sessionJsonlPath.replace(/\.jsonl$/, "")}/subagents`;
  const names: string[] = [];
  try {
    for await (const e of Deno.readDir(dir)) {
      if (e.isFile && e.name.endsWith(".jsonl")) names.push(e.name);
    }
  } catch {
    return []; // no subagents/ directory — degrade silently
  }
  names.sort();
  const out: Array<{ metrics: SubagentMetrics; timestamps: number[] }> = [];
  for (const name of names) {
    const base = name.replace(/\.jsonl$/, "");
    let meta: AgentMeta = {};
    try {
      meta = JSON.parse(await Deno.readTextFile(`${dir}/${base}.meta.json`));
    } catch {
      // meta is a convenience: an unreadable one costs labels, not metrics
    }
    let parsed: ParsedSession;
    try {
      parsed = await parseSession(
        `${dir}/${name}`, base, undefined, filePrefix, idleGapSec, repoRoot, promptIdPrefixes,
      );
    } catch (err) {
      console.error(`skip subagent ${base}: ${err}`);
      continue;
    }
    out.push({
      metrics: {
        ...parsed.metrics,
        agent_name: await agentLabel(dir, base),
        agent_type: meta.agentType,
        custom_agent_type: meta.customAgentType,
        description: meta.description,
      },
      timestamps: parsed.timestamps,
    });
  }
  out.sort((a, b) => (a.metrics.start ?? "").localeCompare(b.metrics.start ?? ""));
  return out;
}

// ──────────────────────────────────────────────────────────────────────────
// Aggregation

/**
 * Sum a set of rows into one totals block. Wall / active seconds are summed,
 * which is right across distinct sessions but wrong for a session and the
 * subagents nested inside it — pass `unionTimestamps` there to recompute the
 * span from the merged timeline instead.
 */
function aggregate(
  sessions: Totals[],
  opts?: { unionTimestamps: number[]; idleGapSec: number },
): Totals {
  const t: Totals = {
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
  if (opts) {
    const sorted = [...opts.unionTimestamps].sort((a, b) => a - b);
    Object.assign(t, spanOf(sorted, opts.idleGapSec));
  }
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
  const s = agg.subagent_totals;
  const c = agg.combined_totals;
  // With no dispatched subagents every split column would repeat the
  // orchestrator column, so the report stays in its original single-column form.
  const split = agg.subagent_count > 0;
  const sum = (r: Record<string, number>) => Object.values(r).reduce((a, b) => a + b, 0);
  /** One summary row: three columns when subagents ran, one otherwise. */
  const row = (label: string, orch: string, sub: string, comb: string) =>
    split ? `| ${label} | ${orch} | ${sub} | ${comb} |` : `| ${label} | ${orch} |`;

  const lines: string[] = [];
  lines.push(`# ${agg.problem} — 定量メトリクス（自動生成）`);
  lines.push("");
  lines.push(`Generated: ${agg.generated_at}`);
  lines.push(`Idle gap threshold: ${agg.idle_gap_minutes} min`);
  if (agg.filters?.file_prefix) lines.push(`File prefix filter: \`${agg.filters.file_prefix}\``);
  lines.push("");
  lines.push("## サマリー（合計）");
  lines.push("");
  if (split) {
    lines.push("オーケストレーター = 親 transcript のみ / サブエージェント = 派遣した agent transcript の合計 /");
    lines.push("合計 = 両者。合計の wall・active time は親子の時間帯が重なるため和ではなく時刻の和集合から再計算する。");
    lines.push("");
    lines.push("| 項目 | オーケストレーター | サブエージェント | 合計 |");
    lines.push("|---|---|---|---|");
  } else {
    lines.push("| 項目 | 値 |");
    lines.push("|---|---|");
  }
  lines.push(row("セッション数", String(agg.sessions.length), String(agg.subagent_count), "-"));
  lines.push(row("期間", `${t.start ?? "-"} 〜 ${t.end ?? "-"}`, `${s.start ?? "-"} 〜 ${s.end ?? "-"}`, `${c.start ?? "-"} 〜 ${c.end ?? "-"}`));
  lines.push(row("Wall time（合計）", fmtDuration(t.wall_time_seconds), fmtDuration(s.wall_time_seconds), fmtDuration(c.wall_time_seconds)));
  lines.push(row("Active time（idle 除外）", fmtDuration(t.active_time_seconds), fmtDuration(s.active_time_seconds), fmtDuration(c.active_time_seconds)));
  lines.push(row("LLM ターン数", String(t.turns), String(s.turns), String(c.turns)));
  lines.push(row("ツールコール総数", String(sum(t.tool_calls)), String(sum(s.tool_calls)), String(sum(c.tool_calls))));
  lines.push(row("ツール失敗回数", String(t.tool_errors), String(s.tool_errors), String(c.tool_errors)));
  if (!split) lines.push(`| サブエージェント側 entries | ${t.sidechain_entries} |`);
  if (agg.filters?.file_prefix) {
    lines.push(row("対象ファイル Edit 回数", String(t.matched_edits), String(s.matched_edits), String(c.matched_edits)));
    lines.push(row("対象ファイル Write 回数", String(t.matched_writes), String(s.matched_writes), String(c.matched_writes)));
  }
  lines.push(row("Models", t.models.join(", "), s.models.join(", "), c.models.join(", ")));
  lines.push("");
  lines.push("## ツールコール内訳");
  lines.push("");
  lines.push(split ? "| Tool | オーケストレーター | サブエージェント | 合計 |" : "| Tool | Count |");
  lines.push(split ? "|---|---|---|---|" : "|---|---|");
  for (const [k, v] of Object.entries(c.tool_calls).sort((a, b) => b[1] - a[1])) {
    lines.push(split ? `| ${k} | ${t.tool_calls[k] ?? 0} | ${s.tool_calls[k] ?? 0} | ${v} |` : `| ${k} | ${v} |`);
  }
  lines.push("");
  lines.push("## Bash 内訳");
  lines.push("");
  lines.push(split ? "| Category | オーケストレーター | サブエージェント | 合計 |" : "| Category | Count |");
  lines.push(split ? "|---|---|---|---|" : "|---|---|");
  for (const [k, v] of Object.entries(c.bash_breakdown).sort((a, b) => b[1] - a[1])) {
    lines.push(split ? `| \`${k}\` | ${t.bash_breakdown[k] ?? 0} | ${s.bash_breakdown[k] ?? 0} | ${v} |` : `| \`${k}\` | ${v} |`);
  }
  lines.push("");
  lines.push("## 編集ファイル別 Edit/Write 回数");
  lines.push("");
  const files = new Set<string>([
    ...Object.keys(c.edits_by_file),
    ...Object.keys(c.writes_by_file),
  ]);
  if (files.size > 0) {
    lines.push(split ? "| File | Edit | Write | うち subagent Edit | うち subagent Write |" : "| File | Edit | Write |");
    lines.push(split ? "|---|---|---|---|---|" : "|---|---|---|");
    for (const f of [...files].sort()) {
      const base = `| \`${f}\` | ${c.edits_by_file[f] ?? 0} | ${c.writes_by_file[f] ?? 0} |`;
      lines.push(split ? `${base} ${s.edits_by_file[f] ?? 0} | ${s.writes_by_file[f] ?? 0} |` : base);
    }
  } else {
    lines.push("(なし)");
  }
  lines.push("");
  lines.push("## トークン使用量");
  lines.push("");
  lines.push(split ? "| 項目 | オーケストレーター | サブエージェント | 合計 |" : "| 項目 | tokens |");
  lines.push(split ? "|---|---|---|---|" : "|---|---|");
  for (const k of ["input", "output", "cache_read", "cache_creation"] as const) {
    lines.push(
      split
        ? `| ${k} | ${fmtThousands(t.tokens[k])} | ${fmtThousands(s.tokens[k])} | ${fmtThousands(c.tokens[k])} |`
        : `| ${k} | ${fmtThousands(t.tokens[k])} |`,
    );
  }
  lines.push("");
  if (split) {
    lines.push("## サブエージェント別");
    lines.push("");
    lines.push("| Agent | 種別 | Wall | Active | Turns | ToolCalls | Bash | Edit | Write | Read | Errors | 内容 |");
    lines.push("|---|---|---|---|---|---|---|---|---|---|---|---|");
    for (const ses of agg.sessions) {
      for (const a of ses.subagents) {
        lines.push(
          `| \`${a.agent_name}\` | ${a.custom_agent_type ?? a.agent_type ?? "-"} | ${fmtDuration(a.wall_time_seconds)} | ${fmtDuration(a.active_time_seconds)} | ${a.turns} | ${sum(a.tool_calls)} | ${a.bash_total} | ${sum(a.edits_by_file)} | ${sum(a.writes_by_file)} | ${sum(a.reads_by_file)} | ${a.tool_errors} | ${a.description ?? ""} |`,
        );
      }
    }
    lines.push("");
  }

  if (agg.sessions.length > 1) {
    lines.push("## セッション別");
    lines.push("");
    const head = "| Session | Note | Start | Wall | Active | Turns | ToolCalls | Bash | Edit | Write | Errors |";
    lines.push(split ? head + " Agents |" : head);
    lines.push(split ? "|---|---|---|---|---|---|---|---|---|---|---|---|" : "|---|---|---|---|---|---|---|---|---|---|---|");
    for (const se of agg.sessions) {
      const base =
        `| \`${se.id.slice(0, 8)}\` | ${se.note ?? ""} | ${se.start ?? "-"} | ${fmtDuration(se.wall_time_seconds)} | ${fmtDuration(se.active_time_seconds)} | ${se.turns} | ${sum(se.tool_calls)} | ${se.bash_total} | ${sum(se.edits_by_file)} | ${sum(se.writes_by_file)} | ${se.tool_errors} |`;
      lines.push(split ? `${base} ${se.subagents.length} |` : base);
    }
    lines.push("");
  }
  return lines.join("\n");
}

// ──────────────────────────────────────────────────────────────────────────
// Discover mode

async function discover(filePrefix: string | undefined, logsDir: string, withSubagents: boolean) {
  const repoRoot = Deno.cwd();
  const entries: Array<{ id: string; row: Totals; agents: number }> = [];
  for await (const e of Deno.readDir(logsDir)) {
    if (!e.isFile || !e.name.endsWith(".jsonl")) continue;
    const id = e.name.replace(/\.jsonl$/, "");
    const path = `${logsDir}/${e.name}`;
    try {
      const parsed = await parseSession(path, id, undefined, filePrefix, 5 * 60, repoRoot, undefined);
      // The work itself usually happens in the dispatched agents, so a session
      // is judged by what it and its agents touched together.
      const subs = withSubagents
        ? await parseSubagents(path, filePrefix, 5 * 60, repoRoot, undefined)
        : [];
      const row = subs.length === 0 ? parsed.metrics : aggregate(
        [parsed.metrics, ...subs.map((s) => s.metrics)],
        {
          unionTimestamps: [...parsed.timestamps, ...subs.flatMap((s) => s.timestamps)],
          idleGapSec: 5 * 60,
        },
      );
      // Only show sessions that have any matched activity, or all if no prefix
      const hits = filePrefix
        ? (row.matched_edits + row.matched_writes +
          Object.keys(row.edits_by_file).filter((k) => k.includes(filePrefix)).length +
          Object.keys(row.reads_by_file).filter((k) => k.includes(filePrefix)).length)
        : 1;
      if (hits > 0) entries.push({ id, row, agents: subs.length });
    } catch (err) {
      console.error(`skip ${id}: ${err}`);
    }
  }
  entries.sort((a, b) => (a.row.start ?? "").localeCompare(b.row.start ?? ""));
  console.log("session   start                wall    edits  writes  reads  bash  tool_calls  agents  models");
  for (const { id, row, agents } of entries) {
    const ed = Object.values(row.edits_by_file).reduce((a, b) => a + b, 0);
    const wr = Object.values(row.writes_by_file).reduce((a, b) => a + b, 0);
    const rd = Object.values(row.reads_by_file).reduce((a, b) => a + b, 0);
    const tc = Object.values(row.tool_calls).reduce((a, b) => a + b, 0);
    console.log(
      `${id.slice(0, 8)}  ${(row.start ?? "").slice(0, 19).padEnd(19)}  ${fmtDuration(row.wall_time_seconds).padStart(6)}  ${String(ed).padStart(5)}  ${String(wr).padStart(6)}  ${String(rd).padStart(5)}  ${String(row.bash_total).padStart(4)}  ${String(tc).padStart(10)}  ${String(agents).padStart(6)}  ${row.models.join(",")}`,
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
  /** Agents dispatched during this turn, by name. */
  agents: string[];
  /** Of the counts above, the share contributed by those agents. */
  sub_tool_uses: number;
  sub_edits: number;
  sub_writes: number;
}

/**
 * Resolve a possibly-abbreviated session id to a full JSONL path. Accepts the
 * full UUID or any prefix that uniquely matches a `*.jsonl` file in `logsDir`,
 * which is what users naturally have at hand from `--discover` (8-char prefix).
 * A subagent transcript is also addressable, either by its path relative to
 * `logsDir` (`<uuid>/subagents/agent-foo-<hash>`) or by an unambiguous prefix
 * of its `agent-…` basename.
 */
async function resolveSessionPath(sessionId: string, logsDir: string): Promise<{ id: string; path: string }> {
  const exact = `${logsDir}/${sessionId}.jsonl`;
  try {
    const stat = await Deno.stat(exact);
    if (stat.isFile) return { id: sessionId, path: exact };
  } catch {
    // fall through to prefix search
  }
  const matches: Array<{ id: string; path: string }> = [];
  for await (const entry of Deno.readDir(logsDir)) {
    if (entry.isFile && entry.name.endsWith(".jsonl") && entry.name.startsWith(sessionId)) {
      const id = entry.name.replace(/\.jsonl$/, "");
      matches.push({ id, path: `${logsDir}/${entry.name}` });
    }
  }
  if (matches.length === 0) {
    // Widen to subagent transcripts, which live one directory down.
    for await (const entry of Deno.readDir(logsDir)) {
      if (!entry.isDirectory) continue;
      const sub = `${logsDir}/${entry.name}/subagents`;
      try {
        for await (const f of Deno.readDir(sub)) {
          if (!f.isFile || !f.name.endsWith(".jsonl")) continue;
          if (f.name.startsWith(sessionId)) {
            matches.push({ id: f.name.replace(/\.jsonl$/, ""), path: `${sub}/${f.name}` });
          }
        }
      } catch {
        // session directory without a subagents/ child
      }
    }
  }
  if (matches.length === 0) {
    throw new Error(`session not found: no JSONL in ${logsDir} matches "${sessionId}"`);
  }
  if (matches.length > 1) {
    throw new Error(
      `session id "${sessionId}" is ambiguous — matches: ${matches.map((m) => m.id).join(", ")}. Use a longer prefix.`,
    );
  }
  return matches[0];
}

async function listTurns(
  sessionId: string,
  logsDir: string,
  filePrefix: string | undefined,
  withSubagents: boolean,
): Promise<TurnRow[]> {
  const repoRoot = Deno.cwd();
  const { path } = await resolveSessionPath(sessionId, logsDir);
  const turns = new Map<string, TurnRow>();

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
        agents: [],
        sub_tool_uses: 0,
        sub_edits: 0,
        sub_writes: 0,
      };
      turns.set(pid, row);
    }
    return row;
  };

  const filesPerTurn = new Map<string, Set<string>>();

  /**
   * Fold one transcript into the per-turn rows. A subagent transcript carries
   * the parent turn's `promptId`, so its work lands on the turn that dispatched
   * it; `agentName` marks the counts as agent-side rather than orchestrator-side.
   */
  const scan = async (jsonlPath: string, agentName: string | null) => {
    const text = await Deno.readTextFile(jsonlPath);
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
      if (!currentPid) continue;
      const row = ensure(currentPid);
      if (agentName && !row.agents.includes(agentName)) row.agents.push(agentName);
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
      if (!agentName && d.type === "user" && typeof content === "string") {
        // Skip system-injected wrapper messages, and the agent's own brief.
        if (content && !content.startsWith("<") && row.user_text === null) {
          row.user_text = content.split("\n")[0].slice(0, 80);
        }
      }
      if (Array.isArray(content)) {
        for (const c of content) {
          if (!c || typeof c !== "object") continue;
          if (c.type === "tool_use") {
            row.tool_uses += 1;
            if (agentName) row.sub_tool_uses += 1;
            const name: string = c.name ?? "";
            const input = c.input ?? {};
            if (name === "Bash") row.bash += 1;
            if (name === "Edit") {
              row.edits += 1;
              if (agentName) row.sub_edits += 1;
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
              if (agentName) row.sub_writes += 1;
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
  };

  await scan(path, null);
  if (withSubagents) {
    const dir = `${path.replace(/\.jsonl$/, "")}/subagents`;
    const names: string[] = [];
    try {
      for await (const e of Deno.readDir(dir)) {
        if (e.isFile && e.name.endsWith(".jsonl")) names.push(e.name);
      }
    } catch {
      // no subagents/ directory — nothing to fold in
    }
    for (const name of names.sort()) {
      const base = name.replace(/\.jsonl$/, "");
      await scan(`${dir}/${name}`, await agentLabel(dir, base));
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
  console.log("prompt_id  start             dur     tools  bash  edit  write  (sub)  user / files / agents");
  for (const r of rows) {
    const startCol = (r.start ?? "").slice(11, 19).padEnd(8);
    const dur = fmtDuration(r.duration_seconds).padStart(6);
    const filesStr = r.files_touched.length > 0 ? `[${r.files_touched.join(", ")}]` : "";
    const userStr = r.user_text ?? "";
    const subStr = r.sub_tool_uses > 0 ? String(r.sub_tool_uses) : "-";
    console.log(
      `${r.prompt_id.slice(0, 8)}   ${startCol}          ${dur}  ${String(r.tool_uses).padStart(5)}  ${String(r.bash).padStart(4)}  ${String(r.edits).padStart(4)}  ${String(r.writes).padStart(5)}  ${subStr.padStart(5)}  ${userStr}`,
    );
    if (r.agents.length > 0) console.log(`            ${" ".repeat(8)}          ${" ".repeat(6)}                                       agents: ${r.agents.join(", ")}`);
    if (filesStr) console.log(`            ${" ".repeat(8)}          ${" ".repeat(6)}                                       ${filesStr}`);
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
  const withSubagents = args["no-subagents"] !== true;

  if (args.discover) {
    await discover(args["file-prefix"] as string | undefined, logsDir, withSubagents);
    return;
  }

  if (typeof args.turns === "string") {
    const rows = await listTurns(args.turns, logsDir, args["file-prefix"] as string | undefined, withSubagents);
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
    console.error("       (any mode) --no-subagents  measure the orchestrator transcript alone");
    Deno.exit(1);
  }

  const manifestPath = positional[0];
  const manifest: Manifest = JSON.parse(await Deno.readTextFile(manifestPath));
  const idleGapSec = (manifest.idle_gap_minutes ?? 5) * 60;
  const filePrefix = manifest.filters?.file_prefix;
  const sessionsLogsDir = manifest.logs_dir ?? logsDir;
  const repoRoot = Deno.cwd();

  const sessions: SessionMetrics[] = [];
  const subagentRows: SubagentMetrics[] = [];
  // One combined row per session: same counters, but with the span recomputed
  // over the session's and its agents' merged timeline.
  const combinedRows: Totals[] = [];
  const seen = new Set<string>();
  for (const s of manifest.sessions) {
    const { id: resolvedId, path } = await resolveSessionPath(s.id, sessionsLogsDir);
    // A manifest may name a subagent transcript directly (as some pre-existing
    // ones do); skip it if the parent session already pulled it in.
    if (seen.has(path)) {
      console.error(`skip duplicate session entry: ${s.id}`);
      continue;
    }
    seen.add(path);
    const parsed = await parseSession(path, resolvedId, s.note, filePrefix, idleGapSec, repoRoot, s.prompt_ids);
    const subs = withSubagents
      ? (await parseSubagents(path, filePrefix, idleGapSec, repoRoot, s.prompt_ids))
        .filter((a) => !seen.has(`${path.replace(/\.jsonl$/, "")}/subagents/${a.metrics.id}.jsonl`))
      : [];
    for (const a of subs) seen.add(`${path.replace(/\.jsonl$/, "")}/subagents/${a.metrics.id}.jsonl`);
    parsed.metrics.subagents = subs.map((a) => a.metrics);
    sessions.push(parsed.metrics);
    subagentRows.push(...parsed.metrics.subagents);
    combinedRows.push(aggregate([parsed.metrics, ...parsed.metrics.subagents], {
      unionTimestamps: [...parsed.timestamps, ...subs.flatMap((a) => a.timestamps)],
      idleGapSec,
    }));
  }

  const agg: AggregateMetrics = {
    problem: manifest.problem,
    proof_log: manifest.proof_log,
    generated_at: new Date().toISOString(),
    filters: manifest.filters,
    idle_gap_minutes: manifest.idle_gap_minutes ?? 5,
    sessions,
    totals: aggregate(sessions),
    subagent_totals: aggregate(subagentRows),
    combined_totals: aggregate(combinedRows),
    subagent_count: subagentRows.length,
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
