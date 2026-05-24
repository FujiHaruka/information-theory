#!/usr/bin/env -S deno run -A
// audit_db.ts — SQLite-backed worklist for a multi-session, *parallel* honesty audit
// of all formalized theorems/lemmas.
//
// Why SQLite: parallel audit agents must (a) not double-audit the same theorem and
// (b) not corrupt each other's writes. WAL mode gives concurrent readers + a single
// serialized writer; `claim` leases a batch of un-audited rows inside a
// `BEGIN IMMEDIATE` transaction, so two agents never grab the same rows. Agents only
// call subcommands here — they never write raw SQL.
//
// Subcommands:
//   build   [paths...] [--db F] [--exclude p1,p2] [--kinds k1,k2]
//             (re)extract statements into the DB; preserves existing verdicts.
//   stats   [--db F]                 counts by status / flag / staleness.
//   claim   --agent A [--n 20] [--db F] [--include-stale] [--status S]
//             atomically lease N rows; prints them as JSON (suspects first).
//             default leases status='unaudited'; --status S re-leases rows in S
//             (e.g. --status suspect for the parallel Opus 2nd wave).
//   list    --status S [--limit N] [--sample N] [--db F]
//             read-only; print rows by status as JSON (id, file:line, verdict, note).
//             feeds the final defect/suspect readout and the suspect 2nd wave.
//             --sample N returns N random rows (ORDER BY RANDOM) for QA spot-checks.
//   show    --id ID [--db F]         print one index record (signature, doc, flags,
//             file:line, body_lines/body_head). NOT the proof body — read file:line.
//   verdict --id ID --status S [--verdict CODE] [--note T] [--agent A] [--db F]
//             record an audit result (status: ok|suspect|defect|skip|unaudited).
//   release --agent A [--minutes M] [--db F]
//             return this agent's (or stale) claimed rows to 'unaudited'.
//   reaudit-stale [--db F]           reset verdicts whose statement changed.
//   refresh-hash [--status S] [--db F]
//             refresh `audited_hash` to current `src_hash` for stale rows;
//             status/verdict/note unchanged. Use after a parser-scope change
//             (e.g. adding 'def' to kinds) that shifts body span without
//             altering audited content. --status filters which subset.
//   scan    [paths...] [--exclude p1,p2] [--format table|list|json]
//           [--check-db [--check-kinds defect,suspect] [--db F]]
//             grep `@audit:KIND(SLUG)` tags from .lean docstrings (code-SoT;
//             see docs/audit/audit-tags.md). Independent of the SQLite DB —
//             tags are the live count, DB is the audit-lease cache.
//             With --check-db, cross-check code tags against DB verdicts;
//             reports MISSING_DB (code tag, DB lags), MISSING_TAG (DB says
//             KIND but no code tag), ORPHAN_TAG (tag maps to no declaration).
//             --check-kinds limits which kinds are checked (default: defect;
//             suspect/ok would generate hundreds of warnings until tagged).
//
// Default DB: docs/audit/honesty.db

import { Database } from "jsr:@db/sqlite@0.12";
import { DEFAULT_KINDS, parse, type Decl } from "./extract_statements.ts";

const DEFAULT_DB = "docs/audit/honesty.db";
const STATUSES = new Set(["unaudited", "claimed", "ok", "suspect", "defect", "skip"]);

// ---------- arg parsing ----------
type Args = { _: string[]; [k: string]: string | boolean | string[] };
function parseArgs(argv: string[]): Args {
  const a: Args = { _: [] };
  for (let i = 0; i < argv.length; i++) {
    const t = argv[i];
    if (t.startsWith("--")) {
      const key = t.slice(2);
      const next = argv[i + 1];
      if (next === undefined || next.startsWith("--")) a[key] = true;
      else { a[key] = next; i++; }
    } else (a._ as string[]).push(t);
  }
  return a;
}
const str = (a: Args, k: string, d = "") => (typeof a[k] === "string" ? a[k] as string : d);
const num = (a: Args, k: string, d: number) => (typeof a[k] === "string" ? Number(a[k]) : d);
const flag = (a: Args, k: string) => a[k] === true;

// ---------- record / flags ----------
function djb2(s: string): string {
  let h = 5381;
  for (let i = 0; i < s.length; i++) h = (((h << 5) + h) ^ s.charCodeAt(i)) >>> 0;
  return h.toString(16).padStart(8, "0");
}

const RE_SORRY = /\bsorry(Ax)?\b/;
const RE_LAUNDER = /(_discharged|_full|_complete|_unconditional)\b/;
const RE_LOADBEAR = /(load[- ]?bearing|not a discharge|🟢ʰ|肩代|核心|sorry-?free)/i;
const RE_TRIVIAL = /^(by\s+)?(exact\s+\S+|trivial|assumption|rfl|[A-Za-z_][\w'.]*)\s*$/;

type Row = {
  id: string; module: string; fqn: string; short_name: string; ns: string;
  kind: string; line: number; signature: string; doc: string | null;
  body_lines: number; body_head: string;
  f_uses_sorry: number; f_trivial_body: number; f_name_laundering: number;
  f_load_bearing_doc: number; f_true_in_sig: number; flag_score: number;
  src_hash: string;
};

function toRow(module: string, d: Decl): Row {
  const fqn = d.ns ? `${d.ns}.${d.name}` : d.name;
  const b = d.body.trim();
  const body_lines = b ? b.split("\n").length : 0;
  const body_head = b.split(/\s+/)[0] ?? "";
  const f_uses_sorry = RE_SORRY.test(d.body) ? 1 : 0;
  const f_trivial_body = body_lines <= 1 && RE_TRIVIAL.test(b) ? 1 : 0;
  const f_name_laundering = RE_LAUNDER.test(d.name) ? 1 : 0;
  const f_load_bearing_doc = d.doc && RE_LOADBEAR.test(d.doc) ? 1 : 0;
  const f_true_in_sig = /\bTrue\b/.test(d.signature) ? 1 : 0;
  const flag_score = f_uses_sorry + f_trivial_body + f_name_laundering +
    f_load_bearing_doc + f_true_in_sig;
  return {
    id: `${module}::${fqn}`, module, fqn, short_name: d.name, ns: d.ns,
    kind: d.kind, line: d.line, signature: d.signature, doc: d.doc,
    body_lines, body_head, f_uses_sorry, f_trivial_body, f_name_laundering,
    f_load_bearing_doc, f_true_in_sig, flag_score, src_hash: djb2(d.signature + "\x00" + d.body),
  };
}

// ---------- db ----------
function openDb(path: string): Database {
  const db = new Database(path);
  db.exec("PRAGMA journal_mode = WAL");
  db.exec("PRAGMA busy_timeout = 5000");
  db.exec(`
    CREATE TABLE IF NOT EXISTS theorems (
      id TEXT PRIMARY KEY, module TEXT NOT NULL, fqn TEXT NOT NULL,
      short_name TEXT NOT NULL, ns TEXT, kind TEXT NOT NULL, line INTEGER NOT NULL,
      signature TEXT NOT NULL, doc TEXT, body_lines INTEGER, body_head TEXT,
      f_uses_sorry INTEGER DEFAULT 0, f_trivial_body INTEGER DEFAULT 0,
      f_name_laundering INTEGER DEFAULT 0, f_load_bearing_doc INTEGER DEFAULT 0,
      f_true_in_sig INTEGER DEFAULT 0, flag_score INTEGER DEFAULT 0,
      src_hash TEXT NOT NULL
    );
    CREATE TABLE IF NOT EXISTS audit (
      id TEXT PRIMARY KEY, status TEXT NOT NULL DEFAULT 'unaudited',
      claimed_by TEXT, claimed_at TEXT, verdict TEXT, note TEXT,
      audited_at TEXT, audited_hash TEXT
    );
    CREATE INDEX IF NOT EXISTS idx_audit_status ON audit(status);
  `);
  // Idempotent schema migrations for defect-cleanup phase
  const existingCols = new Set(
    (db.prepare("PRAGMA table_info(audit)").all() as { name: string }[]).map((r) => r.name)
  );
  for (const [col, type] of [
    ["refs", "INTEGER"],
    ["cluster_id", "TEXT"],
    ["dag_position", "TEXT"],
    ["bucket", "TEXT"],
  ] as [string, string][]) {
    if (!existingCols.has(col)) db.exec(`ALTER TABLE audit ADD COLUMN ${col} ${type}`);
  }
  return db;
}

async function collectLeanFiles(paths: string[], exclude: string[]): Promise<string[]> {
  const out: string[] = [];
  const visit = async (p: string) => {
    if (exclude.some((e) => p.includes(e))) return;
    let info: Deno.FileInfo;
    try { info = await Deno.stat(p); } catch { return; }
    if (info.isFile) { if (p.endsWith(".lean")) out.push(p); return; }
    if (info.isDirectory) {
      for await (const e of Deno.readDir(p)) await visit(`${p}/${e.name}`.replace(/\/+/g, "/"));
    }
  };
  for (const p of paths) await visit(p);
  return out.sort();
}

async function cmdBuild(a: Args) {
  const dbPath = str(a, "db", DEFAULT_DB);
  await Deno.mkdir(dbPath.replace(/\/[^/]*$/, ""), { recursive: true }).catch(() => {});
  const exclude = str(a, "exclude", "Common2026/Exam/").split(",").map((s) => s.trim()).filter(Boolean);
  const kinds = new Set(str(a, "kinds", DEFAULT_KINDS.join(",")).split(",").map((s) => s.trim()).filter(Boolean));
  const paths = (a._ as string[]).length ? (a._ as string[]) : ["Common2026"];

  const files = await collectLeanFiles(paths, exclude);
  const rows: Row[] = [];
  for (const f of files) {
    for (const d of parse(await Deno.readTextFile(f), kinds)) rows.push(toRow(f, d));
  }

  const db = openDb(dbPath);
  const upsert = db.prepare(`
    INSERT OR REPLACE INTO theorems
      (id, module, fqn, short_name, ns, kind, line, signature, doc, body_lines,
       body_head, f_uses_sorry, f_trivial_body, f_name_laundering, f_load_bearing_doc,
       f_true_in_sig, flag_score, src_hash)
    VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)`);
  const ensureAudit = db.prepare("INSERT OR IGNORE INTO audit (id) VALUES (?)");
  db.exec("BEGIN IMMEDIATE");
  db.exec("CREATE TEMP TABLE cur (id TEXT PRIMARY KEY)");
  const insCur = db.prepare("INSERT OR IGNORE INTO cur (id) VALUES (?)");
  for (const r of rows) {
    upsert.run(r.id, r.module, r.fqn, r.short_name, r.ns, r.kind, r.line, r.signature,
      r.doc, r.body_lines, r.body_head, r.f_uses_sorry, r.f_trivial_body,
      r.f_name_laundering, r.f_load_bearing_doc, r.f_true_in_sig, r.flag_score, r.src_hash);
    ensureAudit.run(r.id);
    insCur.run(r.id);
  }
  const removed = db.prepare("DELETE FROM theorems WHERE id NOT IN (SELECT id FROM cur)").run();
  db.exec("DROP TABLE cur");
  db.exec("COMMIT");

  const stale = (db.prepare(`
    SELECT COUNT(*) AS c FROM audit a JOIN theorems t ON a.id=t.id
    WHERE a.status IN ('ok','suspect','defect') AND a.audited_hash IS NOT t.src_hash`).get() as { c: number }).c;
  db.close();
  console.error(
    `build: ${rows.length} decls across ${files.length} files → ${dbPath}` +
      ` (removed ${removed} stale rows, ${stale} verdicts now stale)`,
  );
}

function cmdStats(a: Args) {
  const db = openDb(str(a, "db", DEFAULT_DB));
  const byStatus = db.prepare(`
    SELECT a.status AS status, COUNT(*) AS c FROM audit a JOIN theorems t ON a.id=t.id
    GROUP BY a.status ORDER BY c DESC`).all() as { status: string; c: number }[];
  const total = db.prepare("SELECT COUNT(*) AS c FROM theorems").get() as { c: number };
  const flags = db.prepare(`
    SELECT SUM(f_uses_sorry) sorry, SUM(f_trivial_body) trivial,
           SUM(f_name_laundering) launder, SUM(f_load_bearing_doc) loadbear,
           SUM(f_true_in_sig) trueSig, SUM(CASE WHEN flag_score>0 THEN 1 ELSE 0 END) anyFlag
    FROM theorems`).get() as Record<string, number>;
  const stale = db.prepare(`
    SELECT COUNT(*) AS c FROM audit a JOIN theorems t ON a.id=t.id
    WHERE a.status IN ('ok','suspect','defect') AND a.audited_hash IS NOT t.src_hash`).get() as { c: number };
  db.close();
  console.log(`theorems: ${total.c}`);
  console.log("status:");
  for (const r of byStatus) console.log(`  ${r.status.padEnd(10)} ${r.c}`);
  console.log("flags (theorems with):");
  console.log(`  uses_sorry        ${flags.sorry ?? 0}`);
  console.log(`  trivial_body      ${flags.trivial ?? 0}`);
  console.log(`  name_laundering   ${flags.launder ?? 0}`);
  console.log(`  load_bearing_doc  ${flags.loadbear ?? 0}`);
  console.log(`  true_in_sig       ${flags.trueSig ?? 0}`);
  console.log(`  any flag          ${flags.anyFlag ?? 0}`);
  console.log(`stale verdicts: ${stale.c}`);
}

function cmdClaim(a: Args) {
  const agent = str(a, "agent");
  if (!agent) { console.error("claim: --agent required"); Deno.exit(2); }
  const n = num(a, "n", 20);
  const includeStale = flag(a, "include-stale");
  const fromStatus = str(a, "status");
  if (fromStatus && !STATUSES.has(fromStatus)) {
    console.error(`claim: --status must be one of ${[...STATUSES].join("|")}`); Deno.exit(2);
  }
  const db = openDb(str(a, "db", DEFAULT_DB));
  db.exec("BEGIN IMMEDIATE");
  const where = fromStatus
    ? `a.status=?`
    : includeStale
    ? `a.status='unaudited' OR (a.status IN ('ok','suspect','defect') AND a.audited_hash IS NOT t.src_hash)`
    : `a.status='unaudited'`;
  const pickParams = fromStatus ? [fromStatus, n] : [n];
  const picked = db.prepare(`
    SELECT t.id FROM audit a JOIN theorems t ON a.id=t.id
    WHERE ${where}
    ORDER BY t.flag_score DESC, t.module, t.line LIMIT ?`).all(...pickParams) as { id: string }[];
  const upd = db.prepare(
    "UPDATE audit SET status='claimed', claimed_by=?, claimed_at=datetime('now') WHERE id=?");
  for (const p of picked) upd.run(agent, p.id);
  db.exec("COMMIT");
  const ids = picked.map((p) => p.id);
  const rows = ids.length
    ? db.prepare(`
        SELECT id, module, line, kind, fqn, signature, doc, body_lines, body_head,
               f_uses_sorry, f_trivial_body, f_name_laundering, f_load_bearing_doc,
               f_true_in_sig, flag_score
        FROM theorems WHERE id IN (${ids.map(() => "?").join(",")})
        ORDER BY flag_score DESC, module, line`).all(...ids)
    : [];
  db.close();
  console.log(JSON.stringify(rows, null, 2));
  console.error(`claimed ${rows.length} for agent '${agent}'`);
}

function cmdShow(a: Args) {
  const id = str(a, "id");
  if (!id) { console.error("show: --id required"); Deno.exit(2); }
  const db = openDb(str(a, "db", DEFAULT_DB));
  const t = db.prepare("SELECT * FROM theorems WHERE id=?").get(id);
  const au = db.prepare("SELECT * FROM audit WHERE id=?").get(id);
  db.close();
  if (!t) { console.error(`no such id: ${id}`); Deno.exit(1); }
  console.log(JSON.stringify({ ...t as object, audit: au }, null, 2));
}

function cmdList(a: Args) {
  const status = str(a, "status");
  if (status && !STATUSES.has(status)) {
    console.error(`list: --status must be one of ${[...STATUSES].join("|")}`); Deno.exit(2);
  }
  const limit = num(a, "limit", 0);
  const sample = num(a, "sample", 0);
  const cluster = str(a, "cluster");
  const bucket = str(a, "bucket");
  const dag = str(a, "dag");
  const refsMin = str(a, "refs-min");
  const refsMax = str(a, "refs-max");
  const orderBy = str(a, "order-by");
  const VALID_ORDER = new Set(["refs", "cluster_id", "bucket", "fqn"]);

  const db = openDb(str(a, "db", DEFAULT_DB));
  const params: (string | number)[] = [];
  const wheres: string[] = [];

  if (status) { wheres.push("a.status=?"); params.push(status); }
  if (cluster) {
    if (cluster === "NULL") wheres.push("a.cluster_id IS NULL");
    else { wheres.push("a.cluster_id=?"); params.push(cluster); }
  }
  if (bucket) { wheres.push("a.bucket=?"); params.push(bucket); }
  if (dag) { wheres.push("a.dag_position=?"); params.push(dag); }
  if (refsMin) { wheres.push("a.refs>=?"); params.push(Number(refsMin)); }
  if (refsMax) { wheres.push("a.refs<=?"); params.push(Number(refsMax)); }

  let q = `
    SELECT t.id, t.module, t.line, t.kind, t.fqn, t.flag_score,
           a.status, a.verdict, a.note, a.claimed_by, a.audited_at,
           a.refs, a.cluster_id, a.dag_position, a.bucket
    FROM audit a JOIN theorems t ON a.id=t.id`;
  if (wheres.length) q += ` WHERE ${wheres.join(" AND ")}`;

  if (sample > 0) {
    q += ` ORDER BY RANDOM() LIMIT ?`; params.push(sample);
  } else {
    if (orderBy && VALID_ORDER.has(orderBy)) {
      const col = orderBy === "fqn" ? "t.fqn" : `a.${orderBy}`;
      q += ` ORDER BY ${col}`;
    } else {
      q += ` ORDER BY t.flag_score DESC, t.module, t.line`;
    }
    if (limit > 0) { q += ` LIMIT ?`; params.push(limit); }
  }
  const rows = db.prepare(q).all(...params);
  db.close();
  console.log(JSON.stringify(rows, null, 2));
  console.error(`listed ${rows.length} rows${status ? ` (status=${status})` : ""}`);
}

function cmdVerdict(a: Args) {
  const id = str(a, "id");
  const status = str(a, "status");
  if (!id || !status) { console.error("verdict: --id and --status required"); Deno.exit(2); }
  if (!STATUSES.has(status)) {
    console.error(`verdict: --status must be one of ${[...STATUSES].join("|")}`); Deno.exit(2);
  }
  const db = openDb(str(a, "db", DEFAULT_DB));
  const r = db.prepare(`
    UPDATE audit SET status=?, verdict=?, note=?, audited_at=datetime('now'),
      claimed_by=NULL, audited_hash=(SELECT src_hash FROM theorems WHERE id=?)
    WHERE id=?`).run(status, str(a, "verdict") || null, str(a, "note") || null, id, id);
  db.close();
  if (r === 0) { console.error(`no such id: ${id}`); Deno.exit(1); }
  console.error(`verdict recorded: ${id} → ${status}`);
}

function cmdRelease(a: Args) {
  const agent = str(a, "agent");
  const minutes = num(a, "minutes", 0);
  const db = openDb(str(a, "db", DEFAULT_DB));
  let r: number;
  if (minutes > 0) {
    r = db.prepare(`
      UPDATE audit SET status='unaudited', claimed_by=NULL, claimed_at=NULL
      WHERE status='claimed' AND claimed_at <= datetime('now', ?)`).run(`-${minutes} minutes`);
  } else if (agent) {
    r = db.prepare(`
      UPDATE audit SET status='unaudited', claimed_by=NULL, claimed_at=NULL
      WHERE status='claimed' AND claimed_by=?`).run(agent);
  } else {
    console.error("release: --agent or --minutes required"); Deno.exit(2);
  }
  db.close();
  console.error(`released ${r!} claimed rows`);
}

function cmdRefreshHash(a: Args) {
  const status = str(a, "status");
  if (status && !STATUSES.has(status)) {
    console.error(`refresh-hash: --status must be one of ${[...STATUSES].join("|")}`); Deno.exit(2);
  }
  const db = openDb(str(a, "db", DEFAULT_DB));
  const where = status
    ? "a.status=? AND a.audited_hash IS NOT t.src_hash"
    : "a.status IN ('ok','suspect','defect') AND a.audited_hash IS NOT t.src_hash";
  const params = status ? [status] : [];
  const r = db.prepare(`
    UPDATE audit SET audited_hash=(SELECT src_hash FROM theorems WHERE id=audit.id)
    WHERE id IN (
      SELECT a.id FROM audit a JOIN theorems t ON a.id=t.id
      WHERE ${where})`).run(...params);
  db.close();
  console.error(`refresh-hash: refreshed ${r} hashes${status ? ` (status=${status})` : ""}`);
}

const RE_AUDIT_TAG = /@audit:([a-z][\w-]*)(?:\(([^)]*)\))?/g;

type ScanHit = { file: string; line: number; kind: string; slug: string };

async function cmdScan(a: Args) {
  const exclude = str(a, "exclude", "Common2026/Exam/").split(",").map((s) => s.trim()).filter(Boolean);
  const paths = (a._ as string[]).length ? (a._ as string[]) : ["Common2026"];
  const files = await collectLeanFiles(paths, exclude);

  const hits: ScanHit[] = [];
  for (const f of files) {
    const lines = (await Deno.readTextFile(f)).split("\n");
    for (let i = 0; i < lines.length; i++) {
      for (const m of lines[i].matchAll(RE_AUDIT_TAG)) {
        hits.push({ file: f, line: i + 1, kind: m[1], slug: m[2] ?? "" });
      }
    }
  }

  const byKind: Record<string, Record<string, number>> = {};
  for (const h of hits) {
    (byKind[h.kind] ??= {})[h.slug] = (byKind[h.kind]?.[h.slug] ?? 0) + 1;
  }

  const format = str(a, "format", "table");
  const wantCheck = flag(a, "check-db");

  if (format === "json") {
    const out: Record<string, unknown> = { hits, byKind, total: hits.length };
    if (wantCheck) out.check = computeCheckDb(a, hits);
    console.log(JSON.stringify(out, null, 2));
    return;
  }
  if (format === "list") {
    for (const h of hits) {
      console.log(`${h.file}:${h.line}  @audit:${h.kind}${h.slug ? `(${h.slug})` : ""}`);
    }
    if (wantCheck) { console.log(""); printCheckDb(computeCheckDb(a, hits), a); }
    return;
  }
  // table (default)
  for (const k of Object.keys(byKind).sort()) {
    const slugs = byKind[k];
    const total = Object.values(slugs).reduce((s, n) => s + n, 0);
    console.log(`@audit:${k}  (${total})`);
    for (const s of Object.keys(slugs).sort()) {
      const label = s === "" ? "(no slug)" : s;
      console.log(`  ${slugs[s].toString().padStart(4)}  ${label}`);
    }
  }
  console.log(`---\ntotal tags: ${hits.length}`);

  if (wantCheck) { console.log(""); printCheckDb(computeCheckDb(a, hits), a); }
}

type CheckIssue =
  | { type: "MISSING_DB"; kind: string; file: string; line: number; declFqn: string; declLine: number; declStatus: string }
  | { type: "MISSING_TAG"; kind: string; file: string; line: number; declFqn: string }
  | { type: "ORPHAN_TAG"; kind: string; slug: string; file: string; line: number };

type CheckResult = {
  issues: CheckIssue[];
  counts: { MISSING_DB: number; MISSING_TAG: number; ORPHAN_TAG: number };
  checkedKinds: string[];
};

function computeCheckDb(a: Args, hits: ScanHit[]): CheckResult {
  const checkKinds = new Set(
    str(a, "check-kinds", "defect").split(",").map((s) => s.trim()).filter(Boolean),
  );
  // Only kinds with a 1:1 DB-status counterpart can be cross-checked.
  // 'defer', 'staged', 'retract-candidate' are intent tags, not status values.
  for (const k of checkKinds) {
    if (!STATUSES.has(k)) {
      console.error(`check-db: --check-kinds includes '${k}' which has no DB status counterpart (valid: ${[...STATUSES].join("|")})`);
    }
  }

  const db = openDb(str(a, "db", DEFAULT_DB));
  const decls = db.prepare(`
    SELECT t.id, t.module, t.line, t.fqn, a.status
    FROM audit a JOIN theorems t ON a.id=t.id
    ORDER BY t.module, t.line`).all() as { id: string; module: string; line: number; fqn: string; status: string }[];
  db.close();

  // Group by module, already sorted by (module, line) → in-order per group.
  const byModule = new Map<string, typeof decls>();
  for (const d of decls) {
    const arr = byModule.get(d.module) ?? [];
    arr.push(d);
    byModule.set(d.module, arr);
  }

  // Map each tag → owning decl (smallest decl.line >= tag.line in same module).
  // Track per-decl tags-by-kind in one pass.
  const tagsByDecl = new Map<string, Set<string>>();
  const issues: CheckIssue[] = [];

  for (const h of hits) {
    const ds = byModule.get(h.file);
    let owner: typeof decls[0] | undefined;
    if (ds) {
      for (const d of ds) {
        if (d.line >= h.line) { owner = d; break; }
      }
    }
    if (!owner) {
      issues.push({ type: "ORPHAN_TAG", kind: h.kind, slug: h.slug, file: h.file, line: h.line });
      continue;
    }
    const set = tagsByDecl.get(owner.id) ?? new Set<string>();
    set.add(h.kind);
    tagsByDecl.set(owner.id, set);

    if (checkKinds.has(h.kind) && STATUSES.has(h.kind) && owner.status !== h.kind) {
      issues.push({
        type: "MISSING_DB", kind: h.kind, file: h.file, line: h.line,
        declFqn: owner.fqn, declLine: owner.line, declStatus: owner.status,
      });
    }
  }

  // MISSING_TAG: DB has status=KIND but no code @audit:KIND tag.
  for (const k of checkKinds) {
    if (!STATUSES.has(k)) continue;
    for (const d of decls) {
      if (d.status !== k) continue;
      const tags = tagsByDecl.get(d.id);
      if (!tags || !tags.has(k)) {
        issues.push({ type: "MISSING_TAG", kind: k, file: d.module, line: d.line, declFqn: d.fqn });
      }
    }
  }

  const counts = { MISSING_DB: 0, MISSING_TAG: 0, ORPHAN_TAG: 0 };
  for (const i of issues) counts[i.type]++;
  return { issues, counts, checkedKinds: [...checkKinds] };
}

function printCheckDb(res: CheckResult, _a: Args) {
  console.log("cross-check (code @audit tags vs DB):");
  for (const t of ["MISSING_DB", "MISSING_TAG", "ORPHAN_TAG"] as const) {
    const rows = res.issues.filter((i) => i.type === t);
    if (!rows.length) continue;
    const desc = t === "MISSING_DB"
      ? "code tagged but DB status differs"
      : t === "MISSING_TAG"
      ? "DB status set but no matching code tag"
      : "tag at file:line maps to no declaration";
    console.log(`${t} (${rows.length}): ${desc}`);
    for (const r of rows) {
      if (r.type === "MISSING_DB") {
        console.log(`  ${r.file}:${r.line}  @audit:${r.kind}  ${r.declFqn} (decl@${r.declLine})  [DB: ${r.declStatus}]`);
      } else if (r.type === "MISSING_TAG") {
        console.log(`  ${r.file}:${r.line}  ${r.declFqn}  [expected @audit:${r.kind}]`);
      } else {
        console.log(`  ${r.file}:${r.line}  @audit:${r.kind}${r.slug ? `(${r.slug})` : ""}`);
      }
    }
  }
  const total = res.counts.MISSING_DB + res.counts.MISSING_TAG + res.counts.ORPHAN_TAG;
  if (total === 0) {
    console.log(`✓ no mismatches (kinds: ${res.checkedKinds.join(",")})`);
  } else {
    console.log(`---\ntotal mismatches: ${total} (kinds: ${res.checkedKinds.join(",")})`);
  }
}

function cmdReauditStale(a: Args) {
  const db = openDb(str(a, "db", DEFAULT_DB));
  const r = db.prepare(`
    UPDATE audit SET status='unaudited', claimed_by=NULL, claimed_at=NULL
    WHERE id IN (
      SELECT a.id FROM audit a JOIN theorems t ON a.id=t.id
      WHERE a.status IN ('ok','suspect','defect') AND a.audited_hash IS NOT t.src_hash)`).run();
  db.close();
  console.error(`reset ${r} stale verdicts to 'unaudited'`);
}

async function cmdRefsBulk(a: Args) {
  const fromStatus = str(a, "status", "defect");
  const dbPath = str(a, "db", DEFAULT_DB);
  const db = openDb(dbPath);

  const rows = db.prepare(`
    SELECT a.id, t.short_name, t.module, t.fqn
    FROM audit a JOIN theorems t ON a.id=t.id
    WHERE a.status=?`).all(fromStatus) as { id: string; short_name: string; module: string; fqn: string }[];

  // Build a map from short_name → list of ids (to detect collisions)
  const nameToIds = new Map<string, string[]>();
  for (const r of rows) {
    const arr = nameToIds.get(r.short_name) ?? [];
    arr.push(r.id);
    nameToIds.set(r.short_name, arr);
  }

  // All short_names that appear in the full theorems table (for collision detection)
  const allByName = new Map<string, string[]>();
  for (const r of db.prepare("SELECT short_name, fqn FROM theorems").all() as { short_name: string; fqn: string }[]) {
    const arr = allByName.get(r.short_name) ?? [];
    arr.push(r.fqn);
    allByName.set(r.short_name, arr);
  }

  const hist = { zero: 0, local: 0, mid: 0, hub: 0, null_: 0 };
  const upd = db.prepare("UPDATE audit SET refs=? WHERE id=?");

  for (const row of rows) {
    const allFqns = allByName.get(row.short_name) ?? [];
    const isAmbiguous = allFqns.length > 1;

    let refs: number | null = null;

    if (!isAmbiguous) {
      // Simple count: exclude the module file itself
      refs = await rgCount(row.short_name, row.module);
    } else {
      // Fall back to module-tail qualification
      const tail = moduleTail(row.fqn);
      // Check if tail is unique among all fqns
      const tailMatches = allFqns.filter((fqn) => fqn.endsWith(tail));
      if (tail && tailMatches.length === 1) {
        // Use -w (word boundary) on the escaped tail (dots are literal in rg -F isn't available here,
        // but dots in qualified names like Foo.bar won't false-positive in Lean source context)
        refs = await rgCountPattern(tail, row.module, true);
      } else {
        console.error(`refs-bulk: ambiguous short_name '${row.short_name}' (fqns: ${allFqns.join(", ")}) — leaving refs NULL`);
        refs = null;
      }
    }

    upd.run(refs, row.id);

    if (refs === null) hist.null_++;
    else if (refs === 0) hist.zero++;
    else if (refs <= 4) hist.local++;
    else if (refs <= 14) hist.mid++;
    else hist.hub++;
  }

  db.close();

  console.error(`refs-bulk: processed ${rows.length} rows (status=${fromStatus})`);
  console.error(`refs=0: ${hist.zero}`);
  console.error(`1-4: ${hist.local}`);
  console.error(`5-14: ${hist.mid}`);
  console.error(`≥15: ${hist.hub}`);
  console.error(`NULL: ${hist.null_}`);
}

/** Derive module-tail: last two dot-components of fqn, e.g. Common2026.MAC.Foo.bar → Foo.bar */
function moduleTail(fqn: string): string {
  const parts = fqn.split(".");
  return parts.length >= 2 ? parts.slice(-2).join(".") : fqn;
}

/** Resolve the real rg binary path (handles Claude Code ARGV0 wrapper). */
async function resolveRg(): Promise<string> {
  // If a plain `rg` binary exists in PATH (non-wrapper), use it
  const which = new Deno.Command("which", { args: ["rg"], stdout: "piped", stderr: "null" });
  const { code: wc, stdout: wo } = await which.output();
  if (wc === 0) {
    const p = new TextDecoder().decode(wo).trim();
    // Verify it actually runs as rg (not a shell function hit by `which`)
    const test = new Deno.Command(p, { args: ["--version"], stdout: "piped", stderr: "null" });
    const { code: tc, stdout: to } = await test.output();
    if (tc === 0 && new TextDecoder().decode(to).startsWith("ripgrep")) return p;
  }
  // Fall back: Claude Code bundles rg via ARGV0; the claude binary is at $CLAUDE_CODE_EXECPATH
  // or discoverable via `ps` / known install paths.
  for (const candidate of [
    Deno.env.get("CLAUDE_CODE_EXECPATH") ?? "",
    "/Users/haruka/.local/bin/claude",
    "/usr/local/bin/claude",
  ]) {
    if (!candidate) continue;
    try {
      const s = await Deno.stat(candidate);
      if (s.isFile) return candidate; // will be invoked with ARGV0=rg via wrapper script
    } catch { /* skip */ }
  }
  return "rg"; // last resort
}

let _rgPath: string | null = null;
async function getRgPath(): Promise<string> {
  if (_rgPath === null) _rgPath = await resolveRg();
  return _rgPath;
}

/** Run rg to count cross-file refs of a word, excluding the defining module file. */
async function rgCount(name: string, module: string): Promise<number> {
  return rgCountPattern(name, module, true);
}

async function rgCountPattern(pattern: string, excludeModule: string, wordBoundary = false): Promise<number> {
  const rgPath = await getRgPath();
  // Use a wrapper script so ARGV0=rg is honoured even when the binary is the Claude bundle
  const wrapperArgs = wordBoundary
    ? ["-w", "-c", "--type", "lean", "--glob", `!${excludeModule}`, pattern, "Common2026"]
    : ["-c", "--type", "lean", "--glob", `!${excludeModule}`, pattern, "Common2026"];

  // If rgPath is the Claude binary (not a real rg), we need ARGV0=rg.
  // Deno.Command doesn't support argv0 override, so use a tiny shell wrapper.
  const isClaudeBin = rgPath.includes("claude");
  let cmd: Deno.Command;
  if (isClaudeBin) {
    // Build a one-liner: ARGV0=rg exec <path> <args...>
    const argStr = wrapperArgs.map((a) => `'${a.replace(/'/g, "'\\''")}'`).join(" ");
    cmd = new Deno.Command("sh", {
      args: ["-c", `ARGV0=rg exec '${rgPath}' ${argStr}`],
      stdout: "piped",
      stderr: "null",
    });
  } else {
    cmd = new Deno.Command(rgPath, {
      args: wrapperArgs,
      stdout: "piped",
      stderr: "null",
    });
  }

  const { code, stdout } = await cmd.output();
  if (code !== 0 && code !== 1) return 0; // rg exits 1 when no match
  const text = new TextDecoder().decode(stdout);
  return text.trim().split("\n").filter(Boolean).reduce((sum, line) => {
    const m = line.match(/:(\d+)$/);
    return sum + (m ? parseInt(m[1]) : 0);
  }, 0);
}

function cmdTag(a: Args) {
  const id = str(a, "id");
  if (!id) { console.error("tag: --id required"); Deno.exit(2); }
  const cluster = str(a, "cluster");
  const dag = str(a, "dag");
  const bucket = str(a, "bucket");
  if (!cluster && !dag && !bucket) {
    console.error("tag: at least one of --cluster, --dag, --bucket required"); Deno.exit(2);
  }
  if (dag && !["terminal", "helper"].includes(dag)) {
    console.error("tag: --dag must be terminal|helper"); Deno.exit(2);
  }
  if (bucket && !["retract", "honest-rebrand", "actually-fix"].includes(bucket)) {
    console.error("tag: --bucket must be retract|honest-rebrand|actually-fix"); Deno.exit(2);
  }
  const db = openDb(str(a, "db", DEFAULT_DB));
  const sets: string[] = [];
  const params: (string | null)[] = [];
  if (cluster) { sets.push("cluster_id=?"); params.push(cluster === "NULL" ? null : cluster); }
  if (dag) { sets.push("dag_position=?"); params.push(dag); }
  if (bucket) { sets.push("bucket=?"); params.push(bucket); }
  params.push(id);
  const r = db.prepare(`UPDATE audit SET ${sets.join(", ")} WHERE id=?`).run(...params);
  db.close();
  if (r === 0) { console.error(`tag: no such id: ${id}`); Deno.exit(1); }
  console.error(`tagged: ${id}`);
}

function cmdTagBulk(a: Args) {
  const idsStr = str(a, "ids");
  if (!idsStr) { console.error("tag-bulk: --ids required"); Deno.exit(2); }
  const ids = idsStr.split(",").map((s) => s.trim()).filter(Boolean);
  if (!ids.length) { console.error("tag-bulk: --ids is empty"); Deno.exit(2); }
  const cluster = str(a, "cluster");
  const dag = str(a, "dag");
  const bucket = str(a, "bucket");
  if (!cluster && !dag && !bucket) {
    console.error("tag-bulk: at least one of --cluster, --dag, --bucket required"); Deno.exit(2);
  }
  if (dag && !["terminal", "helper"].includes(dag)) {
    console.error("tag-bulk: --dag must be terminal|helper"); Deno.exit(2);
  }
  if (bucket && !["retract", "honest-rebrand", "actually-fix"].includes(bucket)) {
    console.error("tag-bulk: --bucket must be retract|honest-rebrand|actually-fix"); Deno.exit(2);
  }
  const db = openDb(str(a, "db", DEFAULT_DB));
  const sets: string[] = [];
  const baseParams: (string | null)[] = [];
  if (cluster) { sets.push("cluster_id=?"); baseParams.push(cluster === "NULL" ? null : cluster); }
  if (dag) { sets.push("dag_position=?"); baseParams.push(dag); }
  if (bucket) { sets.push("bucket=?"); baseParams.push(bucket); }
  const stmt = db.prepare(`UPDATE audit SET ${sets.join(", ")} WHERE id=?`);
  db.exec("BEGIN IMMEDIATE");
  let updated = 0;
  for (const id of ids) {
    const r = stmt.run(...baseParams, id);
    updated += r;
  }
  db.exec("COMMIT");
  db.close();
  console.error(`tag-bulk: tagged ${updated}/${ids.length} rows`);
}

async function main() {
  const a = parseArgs(Deno.args);
  const cmd = (a._ as string[]).shift() ?? "build";
  switch (cmd) {
    case "build": await cmdBuild(a); break;
    case "stats": cmdStats(a); break;
    case "claim": cmdClaim(a); break;
    case "show": cmdShow(a); break;
    case "list": cmdList(a); break;
    case "verdict": cmdVerdict(a); break;
    case "release": cmdRelease(a); break;
    case "reaudit-stale": cmdReauditStale(a); break;
    case "refresh-hash": cmdRefreshHash(a); break;
    case "scan": await cmdScan(a); break;
    case "refs-bulk": await cmdRefsBulk(a); break;
    case "tag": cmdTag(a); break;
    case "tag-bulk": cmdTagBulk(a); break;
    default: console.error(`unknown command: ${cmd}`); Deno.exit(2);
  }
}

if (import.meta.main) await main();
