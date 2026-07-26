#!/usr/bin/env -S deno run -A
// lean_doc_lint.ts — InformationTheory/**.lean のコード表面規約 (docs/rules/) を機械強制する。
//
// 背景: docstring 規約の一括移行は一度きりでは効かない。docs/rules/docstrings.md 乖離表と
// docs/docstring-tidyup-plan.md Phase 4 → Phase 6 が同じ再発を記録している — 規約を知らない
// 新規宣言が topic ラベル / プロセス語彙 / 日本語散文を書き戻し、数ヶ月後に再スイープになる。
// スイープは「書かれた後」に効く手段しか持たなかったので、この linter は「書いた瞬間」に落とす。
//
// 実装 SoT はここ 1 本で、3 点から同じものを呼ぶ:
//   .claude/hooks/lean-doc-lint.sh   PostToolUse(Edit|Write) — 編集直後に ERROR を差し戻す
//   .githooks/pre-commit             staged file を WARN 表示 (BLOCK しない)
//   .github/workflows/…  job doc-lint  tree 全体で ERROR / ratchet 増加を fail
// 規約の定義は docs/rules/ (docstrings.md / lean-style.md / naming.md) 側。規則を変えるときは
// rules/ を先に直す — ここは規約の実装であって規約ではない。
//
// Usage:
//   deno run -A scripts/lean_doc_lint.ts                    # tree 全体のレポート
//   deno run -A scripts/lean_doc_lint.ts <file.lean> ...    # 指定ファイルのみ
//   deno run -A scripts/lean_doc_lint.ts --hook <file>      # ERROR あれば stderr + exit 2
//   deno run -A scripts/lean_doc_lint.ts --staged           # staged file を WARN, 常に exit 0
//   deno run -A scripts/lean_doc_lint.ts --check            # CI: ERROR / ratchet 増加で exit 1
//   deno run -A scripts/lean_doc_lint.ts --fix [<file> ...] # 自動修正 (fun => ↦ / Main results)
//   deno run -A scripts/lean_doc_lint.ts --baseline         # ratchet 基準を再生成
//
// 規則の 2 クラス:
//   strict  — 個別違反が機械判定できる & tree 全体で既に 0。新規は 1 件でも ERROR。
//   ratchet — 個別違反は機械判定できない (定理固有名の太字か topic ラベルか / name-adequacy)。
//             件数が増えたときだけ ERROR にする = 判定せずに再発機構だけ止める。
//             比較相手は hook/staged では同 file の HEAD 版、--check では baseline の tree 合計。

const CODE_ROOT = "InformationTheory";
const BASELINE_PATH = "scripts/lean_doc_lint.baseline.json";
const CACHE_PATH = ".lake/build/lean_doc_lint.cache.json";
const MAX_LINE = 100;

const argv = Deno.args.slice();
const flags = { hook: false, staged: false, check: false, fix: false, baseline: false };
const paths: string[] = [];
for (const a of argv) {
  if (a === "--hook") flags.hook = true;
  else if (a === "--staged") flags.staged = true;
  else if (a === "--check") flags.check = true;
  else if (a === "--fix") flags.fix = true;
  else if (a === "--baseline") flags.baseline = true;
  else if (a.startsWith("--")) console.error(`unknown flag: ${a}`);
  else paths.push(a);
}

// ── shell / fs helpers ──────────────────────────────────────────────────────

async function git(args: string[]): Promise<string> {
  try {
    const { stdout } = await new Deno.Command("git", { args, stdout: "piped", stderr: "null" })
      .output();
    return new TextDecoder().decode(stdout);
  } catch {
    return "";
  }
}

async function* walk(dir: string): AsyncGenerator<string> {
  let entries: Deno.DirEntry[];
  try {
    entries = [...Deno.readDirSync(dir)];
  } catch {
    return;
  }
  for (const e of entries.sort((a, b) => a.name.localeCompare(b.name))) {
    const full = `${dir}/${e.name}`;
    if (e.isDirectory) yield* walk(full);
    else if (e.isFile && full.endsWith(".lean")) yield full;
  }
}

function relPath(p: string): string {
  const cwd = Deno.cwd();
  if (p.startsWith(cwd + "/")) return p.slice(cwd.length + 1);
  return p.replace(/^\.\//, "");
}

// ── span scanner (comment / docstring / code の切り分け) ──────────────────────
// 規則の適用範囲は span ごとに違う (プロセス語彙は散文だけ、fun ↦ はコードだけ)。Lean の
// ブロックコメントはネストするので depth で追い、文字列リテラルは先に食う (中の `--` を
// コメント開始と誤認しないため)。

type Kind = "code" | "doc" | "moddoc" | "comment";
interface Span {
  kind: Kind;
  start: number;
  end: number;
}

function scanSpans(src: string): Span[] {
  const spans: Span[] = [];
  const push = (kind: Kind, start: number, end: number) => {
    if (end > start) spans.push({ kind, start, end });
  };
  let i = 0;
  let codeStart = 0;
  while (i < src.length) {
    const c = src[i];
    if (c === '"') {
      i++;
      while (i < src.length && src[i] !== '"') {
        if (src[i] === "\\") i++;
        i++;
      }
      i++;
      continue;
    }
    if (c === "-" && src[i + 1] === "-") {
      push("code", codeStart, i);
      const nl = src.indexOf("\n", i);
      const end = nl < 0 ? src.length : nl;
      push("comment", i, end);
      i = end;
      codeStart = i;
      continue;
    }
    if (c === "/" && src[i + 1] === "-") {
      push("code", codeStart, i);
      const third = src[i + 2];
      const kind: Kind = third === "-" ? "doc" : third === "!" ? "moddoc" : "comment";
      let depth = 0;
      let j = i;
      while (j < src.length) {
        if (src[j] === "/" && src[j + 1] === "-") {
          depth++;
          j += 2;
          continue;
        }
        if (src[j] === "-" && src[j + 1] === "/") {
          depth--;
          j += 2;
          if (depth === 0) break;
          continue;
        }
        j++;
      }
      push(kind, i, Math.min(j, src.length));
      i = j;
      codeStart = i;
      continue;
    }
    i++;
  }
  push("code", codeStart, src.length);
  return spans;
}

// span 外を空白で埋めた同長の文字列。offset がそのまま元 src の offset なので、行番号解決と
// 正規表現の ^ $ アンカーがどちらもそのまま使える。
function mask(src: string, spans: Span[], keep: (k: Kind) => boolean): string {
  const out: string[] = new Array(src.length).fill(" ");
  for (const s of spans) {
    if (!keep(s.kind)) continue;
    for (let i = s.start; i < s.end; i++) out[i] = src[i];
  }
  for (let i = 0; i < src.length; i++) if (src[i] === "\n") out[i] = "\n";
  return out.join("");
}

function lineStarts(src: string): number[] {
  const ls = [0];
  for (let i = 0; i < src.length; i++) if (src[i] === "\n") ls.push(i + 1);
  return ls;
}

function lineOf(ls: number[], pos: number): number {
  let lo = 0, hi = ls.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (ls[mid] <= pos) lo = mid;
    else hi = mid - 1;
  }
  return lo + 1;
}

// ── 宣言ヘッダの読み取り ─────────────────────────────────────────────────────

const MODIFIER_RE = /^(?:private|protected|noncomputable|scoped|local|nonrec|partial|unsafe)\b/;
const KEYWORD_RE =
  /^(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|example)\s+([A-Za-z_][\w'.]*)/;

interface DeclHead {
  kw: string;
  name: string;
  attrs: string;
  pos: number;
}

// pos 直後の attribute / modifier を飛ばして宣言ヘッダを読む (docstring とその宣言の紐付け用)。
function declAfter(src: string, pos: number): DeclHead | null {
  let i = pos;
  let attrs = "";
  for (;;) {
    while (i < src.length && /\s/.test(src[i])) i++;
    if (src.startsWith("@[", i)) {
      const close = src.indexOf("]", i);
      if (close < 0) return null;
      attrs += src.slice(i, close + 1);
      i = close + 1;
      continue;
    }
    const m = MODIFIER_RE.exec(src.slice(i, i + 20));
    if (!m) break;
    i += m[0].length;
  }
  const m = KEYWORD_RE.exec(src.slice(i, i + 300));
  if (!m) return null;
  return { kw: m[1], name: m[2], attrs, pos: i };
}

// ── 規則 ────────────────────────────────────────────────────────────────────

type Cls = "strict" | "ratchet";

interface Finding {
  rule: string;
  cls: Cls;
  line: number;
  msg: string;
}

interface Rule {
  name: string;
  cls: Cls;
  why: string;
  // 新規 file (HEAD 版が無い) のとき ratchet の比較相手を 0 とみなすか。違反が一目で機械判定
  // できる規則 (行長 / 宣言名) だけ true。太字や name-adequacy は「新規 file だから 0」とは
  // 言えない (新規 file が named theorem を書くのは正当) ので false = 検査しない。
  newZero?: boolean;
}

const RULES: Rule[] = [
  { name: "cjk", cls: "strict", why: "コード表面の散文は英語 (docstrings.md L64)" },
  { name: "date", cls: "strict", why: "日付は永続記録に書かない (plan / git が履歴)" },
  { name: "audit-narration", cls: "strict", why: "監査プロセスの実況は plan / handoff へ" },
  { name: "process-label", cls: "strict", why: "Phase / Leg / 判断 / 撤退 は plan へ (docstrings.md L66)" },
  { name: "wall-ref", cls: "strict", why: "wall slug は @residual タグ内のみ (退役 slug の散文参照は陳腐化する)" },
  { name: "main-heading", cls: "strict", why: "module doc 見出しは ## Main statements (docstrings.md L58)" },
  { name: "empty-doc", cls: "strict", why: "空 docstring は Mathlib DocString.empty 相当" },
  { name: "fun-arrow", cls: "strict", why: "fun は ↦ を使う (lean-style.md L52)" },
  { name: "retired-decl-ref", cls: "strict", why: "散文が参照する宣言名が HEAD に無い (陳腐化して虚偽になる)" },
  { name: "dead-file-ref", cls: "strict", why: "散文が参照する file / module が存在しない" },
  {
    name: "decl-vocab",
    cls: "ratchet",
    why: "宣言名にプロセス語彙 / 事実に反する接尾辞を入れない (naming.md)",
    newZero: true,
  },
  { name: "bold-start", cls: "ratchet", why: "先頭太字は named theorem のみ許される (docstrings.md item 5)" },
  { name: "long-line", cls: "ratchet", why: "1 行 100 文字以内 (lean-style.md L26)", newZero: true },
  { name: "internal-doc", cls: "ratchet", why: "内部補助補題は bare、名前で語らせる (docstrings.md item 1)" },
];

const CLS = new Map(RULES.map((r) => [r.name, r.cls]));
const WHY = new Map(RULES.map((r) => [r.name, r.why]));
const RATCHET_RULES = RULES.filter((r) => r.cls === "ratchet").map((r) => r.name);
const NEW_ZERO = new Set(RULES.filter((r) => r.newZero).map((r) => r.name));

// ratchet 判定: HEAD 版の件数を基準に増加分だけを返す。新規 file (prev = null) は newZero
// 規則のみ 0 基準で検査する。
function ratchetDeltas(
  now: Finding[],
  prev: string | null,
  facts: Facts,
): { rule: string; before: number; after: number; lines: number[] }[] {
  const after = countByRule(now);
  const before = prev !== null ? countByRule(lintText(prev, facts)) : null;
  const out: { rule: string; before: number; after: number; lines: number[] }[] = [];
  for (const r of RATCHET_RULES) {
    const base = before ? (before[r] ?? 0) : (NEW_ZERO.has(r) ? 0 : null);
    if (base === null) continue;
    const n = after[r] ?? 0;
    if (n <= base) continue;
    out.push({ rule: r, before: base, after: n, lines: now.filter((x) => x.rule === r).map((x) => x.line) });
  }
  return out;
}

const CJK_RE =
  /[　-〿぀-ヿㇰ-ㇿ㐀-䶿一-鿿豈-﫿！-｠￠-￦]/g;
const DATE_RE = /202[0-9]-[0-9]{2}-[0-9]{2}/g;
const AUDIT_RE = /[Aa]udited [0-9]|independent (?:honesty )?audit|audit PASS|auditors?\b/g;
const PROCESS_RE =
  /\bPhase [0-9A-Z]|\bLeg [A-Z][0-9]?\b|\bleg [0-9]|\bwave [0-9]|Retraction log|retreat line/g;
const WALL_RE = /wall:[a-z0-9-]+/g;
const RESIDUAL_RE = /@residual\([a-z-]+:[a-z0-9-]+\)/g;
const MAIN_RESULTS_RE = /^\s*##+\s+Main results\s*$/gm;
// fun の binder 部を挟んで `=>` に至る形だけを拾う。間に `=>` / `↦` / 別の `fun` を挟まない
// ことで入れ子の取り違えを避け、`|` を挟まないことで match alternative (`fun | p => e`、
// これは Lean 構文上 `=>` が必須) を除外する。
const FUN_ARROW_RE = /\bfun\b(?:(?!=>|↦|\||\bfun\b)[\s\S]){0,300}?=>/g;
const DECL_VOCAB_RE = /_unconditional|_uncond\b|_discharged|_wall\b|_v[0-9]\b|_step[0-9]|genuine/i;
const BOLD_START_RE = /\/--\s*\*\*/g;
const DECL_RE =
  /^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+([A-Za-z_][\w'.]*)/gm;
const BACKTICK_RE = /`([A-Za-z_][\w'.]{3,})`/g;
const BACKTICK_SKIP_RE =
  /^(MeasureTheory|Mathlib|Set|Finset|Real|ENNReal|EReal|NNReal|Filter|Measure|Function|Nat|Int|List|Finsupp|Polynomial|Complex|Matrix|Fin|Prod|Sum|Option|Quot|Classical|Topology|Metric|Continuous|Differentiable|Integrable|Summable)\b/;

interface Facts {
  headDecls: Set<string>;
  retired: Set<string>;
  modules: Set<string>;
}

// 引退宣言名索引: git 履歴の追加行から宣言名を集め HEAD に残る分を除く。plan_lint.ts と同じ
// 精度設計 — Mathlib 名 / tactic 名 / 未実装の予定名は履歴に現れないので構造的に除外される。
async function buildFacts(): Promise<Facts> {
  const headDecls = new Set<string>();
  const modules = new Set<string>();
  for await (const f of walk(CODE_ROOT)) {
    modules.add(f.replace(/\.lean$/, "").replaceAll("/", "."));
    let txt: string;
    try {
      txt = await Deno.readTextFile(f);
    } catch {
      continue;
    }
    for (const m of txt.matchAll(DECL_RE)) headDecls.add(m[1]);
  }
  const head = (await git(["rev-parse", "HEAD"])).trim();
  let retired: Set<string> | null = null;
  try {
    const c = JSON.parse(await Deno.readTextFile(CACHE_PATH));
    if (c.head === head && Array.isArray(c.retired)) retired = new Set<string>(c.retired);
  } catch { /* cache 無し / 壊れ — 作り直す */ }
  if (!retired) {
    retired = new Set<string>();
    const out = await git(["log", "-p", "--format=", "--diff-filter=AM", "--", CODE_ROOT]);
    const lineDeclRe = new RegExp(DECL_RE.source);
    for (const raw of out.split("\n")) {
      if (!raw.startsWith("+") || raw.startsWith("+++")) continue;
      const m = lineDeclRe.exec(raw.slice(1));
      if (m) retired.add(m[1]);
    }
    try {
      await Deno.mkdir(".lake/build", { recursive: true });
      await Deno.writeTextFile(CACHE_PATH, JSON.stringify({ head, retired: [...retired] }));
    } catch { /* 書けなくても動作に影響しない */ }
  }
  for (const h of headDecls) retired.delete(h);
  return { headDecls, retired, modules };
}

function successorCandidates(retired: string, headDecls: Set<string>): string[] {
  const matches: string[] = [];
  for (const h of headDecls) {
    if (h.length < 4 || h.length * 2 < retired.length || h === retired) continue;
    if (retired.endsWith(h) || h.endsWith(retired)) matches.push(h);
  }
  matches.sort((a, b) => b.length - a.length);
  return matches.slice(0, 2);
}

function lintText(src: string, facts: Facts): Finding[] {
  const out: Finding[] = [];
  const spans = scanSpans(src);
  const ls = lineStarts(src);
  const prose = mask(src, spans, (k) => k !== "code");
  const code = mask(src, spans, (k) => k === "code");
  const modDoc = mask(src, spans, (k) => k === "moddoc");
  const at = (pos: number) => lineOf(ls, pos);
  const add = (rule: string, pos: number, msg: string) =>
    out.push({ rule, cls: CLS.get(rule)!, line: at(pos), msg });

  const lines = src.split("\n");

  // cjk — 散文もコードも英語 (識別子は元から英語)。1 文字ごとに報告すると 1 行が数十件に
  // 膨らむので行単位に畳む。
  const cjkLines = new Map<number, number>();
  for (const m of src.matchAll(CJK_RE)) {
    const ln = at(m.index!);
    if (!cjkLines.has(ln)) cjkLines.set(ln, m.index!);
  }
  for (const [ln, pos] of cjkLines) {
    add("cjk", pos, `日本語 / 全角文字: '${(lines[ln - 1] ?? "").trim().slice(0, 60)}'`);
  }

  // date / audit-narration / process-label — 散文スコープ
  for (const m of prose.matchAll(DATE_RE)) {
    const line = lines[at(m.index!) - 1] ?? "";
    if (/deprecated|since\s*:=/.test(line)) continue; // @[deprecated (since := "…")] は Lean 必須構文
    add("date", m.index!, `日付 '${m[0]}'`);
  }
  for (const m of prose.matchAll(AUDIT_RE)) add("audit-narration", m.index!, `監査実況 '${m[0]}'`);
  for (const m of prose.matchAll(PROCESS_RE)) add("process-label", m.index!, `プロセス語彙 '${m[0]}'`);

  // wall-ref — @residual(...) の内側は正当、それ以外の wall:slug 参照は退役で陳腐化する
  const tagRanges: [number, number][] = [];
  for (const m of src.matchAll(RESIDUAL_RE)) tagRanges.push([m.index!, m.index! + m[0].length]);
  for (const m of src.matchAll(WALL_RE)) {
    const p = m.index!;
    if (tagRanges.some(([s, e]) => p >= s && p < e)) continue;
    add("wall-ref", p, `@residual タグ外の '${m[0]}'`);
  }

  // main-heading — module doc 見出し
  for (const m of modDoc.matchAll(MAIN_RESULTS_RE)) {
    add("main-heading", m.index!, "'## Main results' (→ '## Main statements')");
  }

  // empty-doc
  for (const s of spans) {
    if (s.kind !== "doc") continue;
    const body = src.slice(s.start + 3, s.end - 2).trim();
    if (body === "") add("empty-doc", s.start, "空 docstring");
  }

  // fun-arrow — コードスコープ
  for (const m of code.matchAll(FUN_ARROW_RE)) {
    add("fun-arrow", m.index!, "`fun … =>` (→ `fun … ↦`)");
  }

  // decl-vocab — 宣言名のプロセス語彙 / 事実に反する接尾辞
  for (const m of code.matchAll(DECL_RE)) {
    if (!DECL_VOCAB_RE.test(m[1])) continue;
    // DECL_RE は先頭の ^\s* が (docstring をマスクした) 空行を食うので、match 開始位置ではなく
    // 名前そのものの位置を報告する。
    add("decl-vocab", m.index! + m[0].lastIndexOf(m[1]), `宣言名 '${m[1]}'`);
  }

  // retired-decl-ref — 散文が参照する宣言名の実在確認。
  // 精度は「引退宣言名索引に載っているものだけ報告する」ことで担保する (plan_lint.ts と同じ設計):
  // Mathlib 補題名 / tactic 名 / 未実装の予定名は git 履歴に一度も現れないので構造的に除外される。
  // 名前空間修飾された参照 (`InformationTheory.Shannon.foo`) は末尾 segment で解決する — DECL_RE が
  // 集めるのは base name なので、修飾ごと引き合わせると全件 miss になる。
  const seenTok = new Set<string>();
  for (const m of prose.matchAll(BACKTICK_RE)) {
    const t = m[1].replace(/\.+$/, "");
    if (t.includes(".lean") || BACKTICK_SKIP_RE.test(t)) continue;
    const base = t.split(".").pop()!;
    if (facts.headDecls.has(base) || facts.modules.has(t) || seenTok.has(t)) continue;
    seenTok.add(t);
    if (!facts.retired.has(base)) continue;
    const cands = successorCandidates(base, facts.headDecls);
    add(
      "retired-decl-ref",
      m.index!,
      `\`${t}\` は HEAD に無い (git 履歴には存在)` +
        (cands.length ? ` — 後継候補: ${cands.join(", ")}` : ""),
    );
  }

  // dead-file-ref — file パス参照だけを見る (曖昧さが無い)。dotted 名は宣言 / 名前空間 / module の
  // どれとも解釈できるので上の retired 索引側に任せる。
  const seenFile = new Set<string>();
  for (const m of prose.matchAll(/(?<!Mathlib\/)InformationTheory\/[\w/]+\.lean/g)) {
    const raw = m[0];
    if (seenFile.has(raw)) continue;
    seenFile.add(raw);
    if (facts.modules.has(raw.replace(/\.lean$/, "").replaceAll("/", "."))) continue;
    add("dead-file-ref", m.index!, `'${raw}' が存在しない`);
  }

  // bold-start (ratchet) — named theorem か topic ラベルかは機械判定できない
  for (const m of prose.matchAll(BOLD_START_RE)) {
    add("bold-start", m.index!, "docstring が太字始まり (named theorem 以外は地の文へ)");
  }

  // long-line (ratchet) — 折り返し位置に判断が要るので件数だけ見張る
  for (let i = 0; i < lines.length; i++) {
    const w = [...lines[i]].length;
    if (w > MAX_LINE) out.push({ rule: "long-line", cls: "ratchet", line: i + 1, msg: `${w} 文字` });
  }

  // internal-doc (ratchet) — entry_point でもタグ持ちでもない補助補題の散文 docstring
  for (const s of spans) {
    if (s.kind !== "doc") continue;
    const body = src.slice(s.start + 3, s.end - 2);
    if (/@residual|@audit:/.test(body)) continue;
    const d = declAfter(src, s.end);
    if (!d || (d.kw !== "theorem" && d.kw !== "lemma")) continue;
    if (d.attrs.includes("entry_point")) continue;
    add("internal-doc", s.start, `補助補題 '${d.name}' に散文 docstring`);
  }

  return out;
}

function countByRule(findings: Finding[]): Record<string, number> {
  const c: Record<string, number> = {};
  for (const f of findings) c[f.rule] = (c[f.rule] ?? 0) + 1;
  return c;
}

// ── 自動修正 ────────────────────────────────────────────────────────────────
// fun => ↦ と Main results 見出しだけ。どちらも意味を変えない機械置換で、それ以外の規則は
// 直し方に判断が要るので触らない。

function applyFix(src: string): { text: string; fixed: Record<string, number> } {
  const fixed: Record<string, number> = {};
  const spans = scanSpans(src);
  const code = mask(src, spans, (k) => k === "code");
  const modDoc = mask(src, spans, (k) => k === "moddoc");
  const edits: { start: number; end: number; to: string; rule: string }[] = [];
  for (const m of code.matchAll(FUN_ARROW_RE)) {
    const end = m.index! + m[0].length;
    edits.push({ start: end - 2, end, to: "↦", rule: "fun-arrow" });
  }
  for (const m of modDoc.matchAll(MAIN_RESULTS_RE)) {
    const s = m.index! + m[0].indexOf("Main results");
    edits.push({ start: s, end: s + "Main results".length, to: "Main statements", rule: "main-heading" });
  }
  edits.sort((a, b) => b.start - a.start);
  let text = src;
  for (const e of edits) {
    text = text.slice(0, e.start) + e.to + text.slice(e.end);
    fixed[e.rule] = (fixed[e.rule] ?? 0) + 1;
  }
  return { text, fixed };
}

// ── baseline ────────────────────────────────────────────────────────────────

interface Baseline {
  head: string;
  totals: Record<string, number>;
}

async function readBaseline(): Promise<Baseline | null> {
  try {
    return JSON.parse(await Deno.readTextFile(BASELINE_PATH));
  } catch {
    return null;
  }
}

// ── main ────────────────────────────────────────────────────────────────────

async function treeFiles(): Promise<string[]> {
  const fs: string[] = [];
  for await (const f of walk(CODE_ROOT)) fs.push(f);
  return fs;
}

async function stagedFiles(): Promise<string[]> {
  const out = await git(["diff", "--cached", "--name-only", "--diff-filter=ACM"]);
  return out.split("\n").map((s) => s.trim()).filter((s) =>
    s.endsWith(".lean") && s.includes(`${CODE_ROOT}/`)
  );
}

async function headText(path: string): Promise<string | null> {
  const out = await git(["show", `HEAD:${path}`]);
  return out === "" ? null : out;
}

const facts = await buildFacts();

// --fix
if (flags.fix) {
  const targets = paths.length ? paths.map(relPath) : await treeFiles();
  const total: Record<string, number> = {};
  let touched = 0;
  for (const f of targets) {
    let src: string;
    try {
      src = await Deno.readTextFile(f);
    } catch {
      continue;
    }
    const { text, fixed } = applyFix(src);
    if (text === src) continue;
    await Deno.writeTextFile(f, text);
    touched++;
    for (const [k, v] of Object.entries(fixed)) total[k] = (total[k] ?? 0) + v;
  }
  console.log(`--fix: ${touched} files`);
  for (const [k, v] of Object.entries(total).sort()) console.log(`  ${k}: ${v}`);
  Deno.exit(0);
}

// --baseline
if (flags.baseline) {
  const totals: Record<string, number> = {};
  for (const f of await treeFiles()) {
    const src = await Deno.readTextFile(f);
    for (const [k, v] of Object.entries(countByRule(lintText(src, facts)))) {
      totals[k] = (totals[k] ?? 0) + v;
    }
  }
  const head = (await git(["rev-parse", "HEAD"])).trim();
  const keep: Record<string, number> = {};
  for (const r of RATCHET_RULES) keep[r] = totals[r] ?? 0;
  await Deno.writeTextFile(
    BASELINE_PATH,
    JSON.stringify({ head, totals: keep }, null, 2) + "\n",
  );
  console.log(`wrote ${BASELINE_PATH} @ ${head.slice(0, 8)}`);
  for (const [k, v] of Object.entries(keep).sort()) console.log(`  ${k}: ${v}`);
  const strictLeft = Object.entries(totals).filter(([k]) => CLS.get(k) === "strict");
  if (strictLeft.length) {
    console.log("\nstrict 規則の残件 (0 にしてから baseline を確定させる):");
    for (const [k, v] of strictLeft.sort()) console.log(`  ${k}: ${v}`);
  }
  Deno.exit(0);
}

// --hook: 1 file、ERROR だけを stderr に出して exit 2 (Claude Code が stderr を差し戻す)
if (flags.hook) {
  const f = relPath(paths[0] ?? "");
  if (!f || !f.endsWith(".lean") || !f.includes(`${CODE_ROOT}/`)) Deno.exit(0);
  let src: string;
  try {
    src = await Deno.readTextFile(f);
  } catch {
    Deno.exit(0);
  }
  const now = lintText(src, facts);
  const msgs: string[] = [];
  for (const x of now.filter((x) => x.cls === "strict")) {
    msgs.push(`  ${f}:${x.line} [${x.rule}] ${x.msg} — ${WHY.get(x.rule)}`);
  }
  for (const d of ratchetDeltas(now, await headText(f), facts)) {
    msgs.push(
      `  ${f}: [${d.rule}] ${d.before} → ${d.after} 件 (行 ${d.lines.join(", ")}) — ${WHY.get(d.rule)}`,
    );
  }
  if (!msgs.length) Deno.exit(0);
  console.error(
    `コード表面規約 (docs/rules/) 違反です。この編集で直してください:\n${msgs.join("\n")}\n` +
      `自動修正できる分: deno run -A ${"scripts/lean_doc_lint.ts"} --fix ${f}`,
  );
  Deno.exit(2);
}

// --staged: pre-commit から。WARN 表示のみで常に exit 0 (BLOCK は編集時に済んでいる)
if (flags.staged) {
  const files = await stagedFiles();
  const msgs: string[] = [];
  for (const f of files) {
    let src: string;
    try {
      src = await Deno.readTextFile(f);
    } catch {
      continue;
    }
    const now = lintText(src, facts);
    for (const x of now.filter((x) => x.cls === "strict")) {
      msgs.push(`  ⚠ ${f}:${x.line} [${x.rule}] ${x.msg}`);
    }
    for (const d of ratchetDeltas(now, await headText(f), facts)) {
      msgs.push(`  ⚠ ${f}: [${d.rule}] ${d.before} → ${d.after} 件`);
    }
  }
  if (msgs.length) {
    console.error(`\n[lean_doc_lint] コード表面規約 (コミットは継続):\n${msgs.join("\n")}`);
  }
  Deno.exit(0);
}

// tree / 指定ファイルのレポート (--check なら判定して exit code を返す)
const files = paths.length ? paths.map(relPath) : await treeFiles();
const perFile = new Map<string, Finding[]>();
const totals: Record<string, number> = {};
for (const f of files) {
  let src: string;
  try {
    src = await Deno.readTextFile(f);
  } catch {
    continue;
  }
  const fs = lintText(src, facts);
  if (fs.length) perFile.set(f, fs);
  for (const [k, v] of Object.entries(countByRule(fs))) totals[k] = (totals[k] ?? 0) + v;
}

const L: string[] = [`# lean_doc_lint — ${files.length} files`, ""];
for (const r of RULES) {
  const n = totals[r.name] ?? 0;
  L.push(`- ${r.cls === "strict" ? "strict " : "ratchet"} \`${r.name}\`: ${n}`);
}
L.push("");
// 明細は strict 全件 + 「tree 合計が小さい ratchet 規則」を出す。internal-doc のように床が
// 大きい規則を明細に混ぜると、実際に直せる指摘が埋もれるため。
const DETAIL_CAP = 100;
const detailRules = new Set([
  ...RULES.filter((r) => r.cls === "strict").map((r) => r.name),
  ...RATCHET_RULES.filter((r) => (totals[r] ?? 0) <= DETAIL_CAP),
]);
for (const [f, fs] of [...perFile].sort()) {
  const shown = fs.filter((x) => detailRules.has(x.rule));
  if (!shown.length) continue;
  L.push(`## ${f}`, "");
  for (const x of shown.slice(0, 40)) L.push(`- ${x.line}: [${x.rule}] ${x.msg}`);
  if (shown.length > 40) L.push(`- … ほか ${shown.length - 40} 件`);
  L.push("");
}
console.log(L.join("\n"));

if (flags.check) {
  const base = await readBaseline();
  const bad: string[] = [];
  for (const r of RULES) {
    const n = totals[r.name] ?? 0;
    if (r.cls === "strict") {
      if (n > 0) bad.push(`${r.name}: ${n} 件 (strict は 0 が要件) — ${r.why}`);
    } else if (base) {
      const b = base.totals[r.name] ?? 0;
      if (n > b) bad.push(`${r.name}: ${n} > baseline ${b} (再発) — ${r.why}`);
    }
  }
  if (!base) console.error(`(baseline ${BASELINE_PATH} が無いので ratchet 判定はスキップ)`);
  if (bad.length) {
    console.error(`\n[lean_doc_lint] FAIL:\n${bad.map((s) => `  ✗ ${s}`).join("\n")}`);
    Deno.exit(1);
  }
  console.error("\n[lean_doc_lint] PASS");
}
