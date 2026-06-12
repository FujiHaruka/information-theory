#!/usr/bin/env -S deno run -A
// plan_lint.ts — detect stale references in docs/**/*-plan.md against InformationTheory/ code.
//
// プランは制御状態・判断履歴・確定事実を混ぜて肥大/stale 化する (CLAUDE.md「Plan / docs hygiene」)。
// この linter は plan のコード参照 (壁 slug / file:line) を現コードと照合し、drift を機械検出する。
// コード走査は純 Deno (rg はシェル関数で Deno.Command から spawn 不可)。git のみ外部コマンド。
//
// Usage:
//   deno run -A scripts/plan_lint.ts                       # docs/**/*-plan.md 全部
//   deno run -A scripts/plan_lint.ts docs/shannon/foo-plan.md ...   # 指定 plan のみ
//   deno run -A scripts/plan_lint.ts --out docs/plan-staleness-report.md
//   deno run -A scripts/plan_lint.ts --hook <staged-plan> ...       # pre-commit 用: STALE のみ WARN, 常に exit 0
//   deno run -A scripts/plan_lint.ts --check-decls          # backtick decl 照合も行う (noisy, 既定 off)
//
// 判定 (CLAUDE.md と整合):
//   STALE (確定)   = (a) file:line の file が存在しない  (b) plan の wall:slug が code に無い
//                    (c) plan 内の '*-plan.md' リンクのリンク先が存在しない (dead 親/子リンク)
//                    ※ (b) は壁解消/改名のほか「未作成 (planning ahead)」も含む — その場合は誤検出
//   SUSPECT (要レビュー) = 行ドリフト (line > file 行数) / git staleness (参照コードが plan より新しい)
//                          / 親子 backlink 欠落 (子の Parent が指す親が子を sub-plan 参照していない)
//                          / 親子 drift (子 plan が親 plan より後に更新 — 親 DAG/状態が stale の疑い)
//                          / [--check-decls] backtick decl が code に無い (heuristic, 誤検出あり)
//   BUDGET         = plan > 600 行 (CLAUDE.md プラン予算)

const CODE_ROOT = "InformationTheory";
const DOCS_ROOT = "docs";
const LINE_BUDGET = 600;

const argv = Deno.args.slice();
const flags = { out: "", hook: false, checkDecls: false };
const paths: string[] = [];
for (let i = 0; i < argv.length; i++) {
  const a = argv[i];
  if (a === "--out") flags.out = argv[++i];
  else if (a === "--hook") flags.hook = true;
  else if (a === "--check-decls") flags.checkDecls = true;
  else paths.push(a);
}

// ── helpers ────────────────────────────────────────────────────────────────

async function git(args: string[]): Promise<string> {
  try {
    const p = new Deno.Command("git", { args, stdout: "piped", stderr: "null" });
    const { stdout } = await p.output();
    return new TextDecoder().decode(stdout);
  } catch {
    return "";
  }
}

async function* walk(dir: string, match: (p: string) => boolean): AsyncGenerator<string> {
  let entries: Deno.DirEntry[];
  try {
    entries = [...Deno.readDirSync(dir)];
  } catch {
    return;
  }
  for (const e of entries) {
    const full = `${dir}/${e.name}`;
    if (e.isDirectory) yield* walk(full, match);
    else if (e.isFile && match(full)) yield full;
  }
}

async function fileExists(path: string): Promise<boolean> {
  try {
    return (await Deno.stat(path)).isFile;
  } catch {
    return false;
  }
}

// ── code-side fact sets (built once, pure Deno) ─────────────────────────────

const WALL_RE = /@residual\(wall:([\w-]+)\)/g;
const DECL_RE =
  /^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+([A-Za-z_][\w'.]*)/gm;

async function scanCode(): Promise<{ wallSlugs: Set<string>; declNames: Set<string> | null }> {
  const wallSlugs = new Set<string>();
  const declNames = flags.checkDecls ? new Set<string>() : null;
  for await (const f of walk(CODE_ROOT, (p) => p.endsWith(".lean"))) {
    let txt: string;
    try {
      txt = await Deno.readTextFile(f);
    } catch {
      continue;
    }
    for (const m of txt.matchAll(WALL_RE)) wallSlugs.add(m[1].toLowerCase());
    if (declNames) for (const m of txt.matchAll(DECL_RE)) declNames.add(m[1]);
  }
  return { wallSlugs, declNames };
}

const gitTimeCache = new Map<string, number | null>();
async function gitTime(path: string): Promise<number | null> {
  if (gitTimeCache.has(path)) return gitTimeCache.get(path)!;
  const out = (await git(["log", "-1", "--format=%ct", "--", path])).trim();
  const t = out ? parseInt(out, 10) : NaN;
  const v = Number.isFinite(t) ? t : null;
  gitTimeCache.set(path, v);
  return v;
}

const lineCountCache = new Map<string, number>();
async function lineCount(path: string): Promise<number> {
  if (lineCountCache.has(path)) return lineCountCache.get(path)!;
  let n = -1;
  try {
    n = (await Deno.readTextFile(path)).split("\n").length;
  } catch { /* missing */ }
  lineCountCache.set(path, n);
  return n;
}

// ── parent/child plan graph helpers ─────────────────────────────────────────
// 子 plan は `**Parent**:` / `**親**:` ヘッダで親を宣言。親は sub-plan テーブルから子に
// link-back する。両端を照合し、親子 drift (handoff/carryon で親 DAG が stale 化) を機械検出。

const PARENT_RE = /\*\*(?:Parent|親)\*\*\s*[:：]\s*\[[^\]]*\]\(([^)\s]+\.md)\)/;

function dirOf(p: string): string {
  const i = p.lastIndexOf("/");
  return i < 0 ? "" : p.slice(0, i);
}
function baseOf(p: string): string {
  const i = p.lastIndexOf("/");
  return i < 0 ? p : p.slice(i + 1);
}
function resolveRel(baseDir: string, rel: string): string {
  const parts = baseDir ? baseDir.split("/") : [];
  for (const seg of rel.split("/")) {
    if (seg === "" || seg === ".") continue;
    else if (seg === "..") parts.pop();
    else parts.push(seg);
  }
  return parts.join("/");
}
function mdLinkTargets(text: string): string[] {
  return [...text.matchAll(/\[[^\]]*\]\(([^)]+)\)/g)].map((m) => m[1]);
}

// ── per-plan lint ────────────────────────────────────────────────────────────

interface Finding {
  kind: "STALE" | "SUSPECT" | "BUDGET";
  msg: string;
}

async function lintPlan(
  plan: string,
  wallSlugs: Set<string>,
  declNames: Set<string> | null,
): Promise<Finding[]> {
  const findings: Finding[] = [];
  let text: string;
  try {
    text = await Deno.readTextFile(plan);
  } catch {
    return [{ kind: "STALE", msg: `plan を読めない` }];
  }

  // (b) wall slug 照合 (フォーマット例の placeholder は除外)
  const IGNORE_SLUGS = new Set(["slug", "foo", "name", "x", "example", "bar"]);
  for (const w of new Set([...text.matchAll(/\bwall:([\w-]+)/g)].map((m) => m[1].toLowerCase()))) {
    if (IGNORE_SLUGS.has(w)) continue;
    if (!wallSlugs.has(w)) {
      findings.push({ kind: "STALE", msg: `wall slug 'wall:${w}' が code に無い (解消/改名 — 未作成なら誤検出)` });
    }
  }

  // (a) file:line 照合 + 行ドリフト
  const refFiles = new Set<string>();
  const seen = new Set<string>();
  for (const m of text.matchAll(/InformationTheory\/[\w/]+\.lean:(\d+)/g)) {
    const full = m[0];
    const file = full.split(":")[0];
    refFiles.add(file);
    if (seen.has(full)) continue;
    seen.add(full);
    if (!(await fileExists(file))) {
      findings.push({ kind: "STALE", msg: `file:line '${full}' — file が存在しない` });
      continue;
    }
    const lc = await lineCount(file);
    const lref = parseInt(m[1], 10);
    if (lc > 0 && lref > lc) {
      findings.push({ kind: "SUSPECT", msg: `'${full}' は ${file} の ${lc} 行を超える (行ドリフト)` });
    }
  }

  // git staleness: 参照コードが plan より新しい
  const planT = await gitTime(plan);
  if (planT !== null) {
    let newest: { file: string; t: number } | null = null;
    for (const f of refFiles) {
      if (!(await fileExists(f))) continue;
      const ct = await gitTime(f);
      if (ct !== null && ct > planT && (!newest || ct > newest.t)) newest = { file: f, t: ct };
    }
    if (newest) {
      findings.push({ kind: "SUSPECT", msg: `plan 最終コミット以降に '${newest.file}' が変更 (sync 要レビュー)` });
    }
  }

  // backtick decl 照合 (noisy, opt-in)
  if (declNames) {
    const toks = new Set(
      [...text.matchAll(/`([A-Za-z_][\w'.]{3,})`/g)].map((m) => m[1]).filter((t) =>
        !t.includes(".lean") &&
        !/^(MeasureTheory|Mathlib|Set|Finset|Real|ENNReal|EReal|NNReal|Filter|Measure|Function|Nat|Int|List)\b/.test(t)
      ),
    );
    for (const t of toks) {
      if (!declNames.has(t)) {
        findings.push({ kind: "SUSPECT", msg: `backtick token \`${t}\` が code の宣言に無い (heuristic)` });
      }
    }
  }

  // budget
  const lc = text.split("\n").length;
  if (lc > LINE_BUDGET) {
    findings.push({ kind: "BUDGET", msg: `${lc} 行 > ${LINE_BUDGET} 予算 (/compact-plan 候補)` });
  }

  return findings;
}

// ── parent/child graph lint ──────────────────────────────────────────────────

async function lintGraph(
  plan: string,
  text: string,
  planSet: Set<string>,
  declaredParent: Map<string, string>,
  planTexts: Map<string, string>,
): Promise<Finding[]> {
  const findings: Finding[] = [];
  const dir = dirOf(plan);

  // (c) dead '*-plan.md' リンク (親リンク・子 sub-plan リンクどちらも拾う)
  const seenLinks = new Set<string>();
  for (const target of mdLinkTargets(text)) {
    const path = target.split("#")[0];
    if (!path.endsWith("-plan.md")) continue;
    if (/^https?:\/\//.test(path)) continue;
    if (path.includes("<") || path.includes(">")) continue; // テンプレ placeholder
    const resolved = resolveRel(dir, path);
    if (seenLinks.has(resolved)) continue;
    seenLinks.add(resolved);
    if (!planSet.has(resolved) && !(await fileExists(resolved))) {
      findings.push({ kind: "STALE", msg: `plan リンク '${target}' のリンク先が存在しない` });
    }
  }

  // 親子整合 (子の Parent ヘッダ起点)。親 file 消失は上の (c) が STALE で拾う。
  // CLOSED (historical) plans are out of the active DAG drift check — skip backlink/drift SUSPECT
  const isClosed = /\*\*(?:Status|状態)\*\*\s*[:：]\s*CLOSED\b/i.test(text);
  const parent = declaredParent.get(plan);
  if (parent && !isClosed) {
    const ptext = planTexts.get(parent);
    if (ptext !== undefined) {
      // backlink: 親が子の slug を本文 (sub-plan テーブル等) で参照しているか
      const slug = baseOf(plan).replace(/\.md$/, "");
      if (!ptext.includes(slug)) {
        findings.push({
          kind: "SUSPECT",
          msg: `親 '${baseOf(parent)}' が子 '${slug}' を sub-plan 参照していない (backlink 欠落)`,
        });
      }
      // drift: 子が親より後にコミット = 親 DAG/状態が子を反映していない疑い (子が SoT)
      const ct = await gitTime(plan);
      const pt = await gitTime(parent);
      if (ct !== null && pt !== null && ct > pt) {
        findings.push({
          kind: "SUSPECT",
          msg: `子が親 '${baseOf(parent)}' より後に更新 — 親の DAG/状態が子を反映しているか確認 (親子 drift)`,
        });
      }
    }
  }

  return findings;
}

// ── main ───────────────────────────────────────────────────────────────────

const { wallSlugs, declNames } = await scanCode();

// 全 plan を読み込み親子グラフを構築する (lint 対象が部分集合でも親の本文が要るため、
// グラフ構築は常に docs/**/*-plan.md 全体で行う)。
const allPlans: string[] = [];
for await (const f of walk(DOCS_ROOT, (p) => p.endsWith("-plan.md"))) allPlans.push(f);
allPlans.sort();
const planSet = new Set(allPlans);
const planTexts = new Map<string, string>();
for (const p of allPlans) {
  try {
    planTexts.set(p, await Deno.readTextFile(p));
  } catch { /* skip */ }
}
const declaredParent = new Map<string, string>();
for (const [p, t] of planTexts) {
  const m = t.match(PARENT_RE);
  if (m) {
    const resolved = resolveRel(dirOf(p), m[1]);
    if (resolved !== p) declaredParent.set(p, resolved);
  }
}

const plans = paths.length ? paths : allPlans;

const all: { plan: string; findings: Finding[] }[] = [];
for (const plan of plans) {
  const f = await lintPlan(plan, wallSlugs, declNames);
  const text = planTexts.get(plan) ?? await Deno.readTextFile(plan).catch(() => "");
  if (text) f.push(...await lintGraph(plan, text, planSet, declaredParent, planTexts));
  if (f.length) all.push({ plan, findings: f });
}

// hook モード: STALE のみ WARN、常に exit 0
if (flags.hook) {
  const lines: string[] = [];
  for (const { plan, findings } of all) {
    for (const f of findings) if (f.kind === "STALE") lines.push(`  ⚠ ${plan}: ${f.msg}`);
  }
  if (lines.length) console.error(`\n[plan_lint] stale plan 参照 (コミットは継続):\n${lines.join("\n")}`);
  Deno.exit(0);
}

// 通常モード: レポート
function render(): string {
  const counts = { STALE: 0, SUSPECT: 0, BUDGET: 0 };
  for (const { findings } of all) for (const f of findings) counts[f.kind]++;
  const L: string[] = [
    `# plan_lint — ${DOCS_ROOT}/**/*-plan.md vs ${CODE_ROOT}/`,
    "",
    `${plans.length} plans 検査 / STALE ${counts.STALE} · SUSPECT ${counts.SUSPECT} · BUDGET ${counts.BUDGET}`,
    "",
  ];
  for (const kind of ["STALE", "SUSPECT", "BUDGET"] as const) {
    const rows = all.flatMap(({ plan, findings }) =>
      findings.filter((f) => f.kind === kind).map((f) => `- \`${plan}\`: ${f.msg}`)
    );
    if (!rows.length) continue;
    L.push(`## ${kind} (${rows.length})`, "", ...rows, "");
  }
  return L.join("\n");
}

const report = render();
if (flags.out) {
  await Deno.writeTextFile(flags.out, report + "\n");
  console.log(`wrote ${flags.out} (${plans.length} plans)`);
} else {
  console.log(report);
}
