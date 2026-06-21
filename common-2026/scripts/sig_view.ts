#!/usr/bin/env -S deno run -A
// sig_view.ts — Lean ファイルの宣言シグネチャだけを抽出表示する orientation ツール。
//
// 巨大ファイル (1000〜3500 行) の証明本体を読まずに「何があるか / 各補題の型 / 残 sorry と
// その @residual 分類」を一覧する。コーディングエージェントの context 節約用。
//
// なぜ Lean パーサを使わないか: このプロジェクトの型シグネチャは Mathlib 記法を多用し、
// Mathlib を import しないとパーサが落ち、import すると ~5s かかる。署名抽出に elaborate は
// 不要なので、コメント/文字列をマスクし括弧深度で `:=`/`where` 本体境界を切る軽量スキャナで
// 構文的に正確なシグネチャを取り出す (起動 ~0.1s)。正規表現 1 発の素朴版より頑健。
//
// Usage:
//   scripts/sig_view.ts <file.lean> [<file2.lean> ...]   # 既定: シグネチャのみ
//   scripts/sig_view.ts --doc  <file.lean>               # docstring も表示
//   scripts/sig_view.ts --names <file.lean>              # 名前 + 種別 + 行番号のみ (目次)
//   scripts/sig_view.ts --no-context <file.lean>         # namespace/section/variable/open を出さない
//   scripts/sig_view.ts --sorry <file.lean>              # sorry を含む宣言だけに絞る
//
// 色は TTY のときのみ付く (NO_COLOR / パイプ・リダイレクト時は素のテキスト)。
//
// 検証: InformationTheory 全 274 ファイルで宣言数を grep と突合し、差分は全て grep の
// コメント偽陽性 (docstring 内の "theorem."/"structure …" 等) で sig_view 側は 0 取りこぼし。
//
// 既知の限界 (実害は極小、稀): (1) 文字リテラル `'('` は `'` が識別子 prime と衝突するため
// 未処理で括弧深度がずれうる。(2) `:=` を持たないパターンマッチ def (`def f | a => …`) は
// 本体境界が取れず over-inclusive になる。

type Mode = "sig" | "doc" | "names";

interface Decl {
  pos: number;        // キーワード開始位置
  sigStart: number;   // 修飾子込みの署名開始
  kind: string;
  name: string;
  cut: number;        // 本体境界 (:= / where / region end)
  regionEnd: number;  // 次の境界
  hasSorry: boolean;
  residuals: string[];
  doc: string | null;
}

interface Ctx {
  pos: number;
  text: string;
}

const KEYWORDS = [
  "theorem", "lemma", "def", "abbrev", "instance",
  "structure", "inductive", "class", "opaque", "axiom", "example",
];
const MODIFIERS = ["private", "protected", "noncomputable", "partial", "unsafe", "scoped", "local"];
const CTX = ["namespace", "section", "end", "variable", "open", "universe"];
// Lean 識別子継続文字: 文字 (ギリシャ・添字含む) / 数字 / `_ ' ! ?`。
// JS の `\b` は ASCII 前提で、`hC'def` の `'def` を語境界と誤認する → 自前のクラスで境界判定。
const IDC = "\\p{L}\\p{N}_'!?";
const kw = (alts: string[]) => new RegExp(`(?<![${IDC}])(${alts.join("|")})(?![${IDC}])`);
const OPEN_BRACKETS = new Set(["(", "[", "{", "⟨", "⦃"]);
const CLOSE_BRACKETS = new Set([")", "]", "}", "⟩", "⦄"]);

interface Parsed {
  src: string;
  masked: string;
  depth: Int32Array;
  docSpans: { start: number; end: number; text: string }[];
  lineStarts: number[];
}

// コメント (line `--`, block `/- -/` nested, doc `/-- -/`, module `/-! -/`) と
// 文字列リテラルをスペースに潰した masked テキストを作る。docstring は別途中身を記録する。
function maskAndScan(src: string): Parsed {
  const n = src.length;
  const out: string[] = new Array(n);
  const docSpans: { start: number; end: number; text: string }[] = [];
  let i = 0;
  const startsWith = (s: string, at: number) => src.startsWith(s, at);
  while (i < n) {
    // --- NORMAL mode entry points ---
    if (startsWith("/--", i)) {
      // docstring: 中身を記録しつつマスク。block と同様にネスト深度を数える。
      const docStart = i;
      let depth = 1;
      out[i] = " "; out[i + 1] = " "; out[i + 2] = " ";
      i += 3;
      while (i < n && depth > 0) {
        if (startsWith("/-", i)) { depth++; out[i] = " "; out[i + 1] = " "; i += 2; }
        else if (startsWith("-/", i)) { depth--; out[i] = " "; out[i + 1] = " "; i += 2; }
        else { out[i] = src[i] === "\n" ? "\n" : " "; i++; }
      }
      const raw = src.slice(docStart, i);
      const text = raw.replace(/^\/--/, "").replace(/-\/$/, "").trim();
      docSpans.push({ start: docStart, end: i, text });
      continue;
    }
    if (startsWith("/-", i)) {
      let depth = 1;
      out[i] = " "; out[i + 1] = " "; i += 2;
      while (i < n && depth > 0) {
        if (startsWith("/-", i)) { depth++; out[i] = " "; out[i + 1] = " "; i += 2; }
        else if (startsWith("-/", i)) { depth--; out[i] = " "; out[i + 1] = " "; i += 2; }
        else { out[i] = src[i] === "\n" ? "\n" : " "; i++; }
      }
      continue;
    }
    if (startsWith("--", i)) {
      out[i] = " "; out[i + 1] = " "; i += 2;
      while (i < n && src[i] !== "\n") { out[i] = " "; i++; }
      continue;
    }
    if (src[i] === '"') {
      out[i] = " "; i++;
      while (i < n) {
        if (src[i] === "\\") { out[i] = " "; out[i + 1] = " "; i += 2; continue; }
        if (src[i] === '"') { out[i] = " "; i++; break; }
        out[i] = src[i] === "\n" ? "\n" : " "; i++;
      }
      continue;
    }
    out[i] = src[i];
    i++;
  }
  const masked = out.join("");

  // 括弧深度配列
  const depth = new Int32Array(n + 1);
  let d = 0;
  for (let k = 0; k < n; k++) {
    depth[k] = d;
    const c = masked[k];
    if (OPEN_BRACKETS.has(c)) d++;
    else if (CLOSE_BRACKETS.has(c)) { if (d > 0) d--; }
  }
  depth[n] = d;

  const lineStarts = [0];
  for (let k = 0; k < n; k++) if (src[k] === "\n") lineStarts.push(k + 1);

  return { src, masked, depth, docSpans, lineStarts };
}

function lineOf(lineStarts: number[], pos: number): number {
  // 二分探索: pos を含む行 (1-based)
  let lo = 0, hi = lineStarts.length - 1, ans = 0;
  while (lo <= hi) {
    const mid = (lo + hi) >> 1;
    if (lineStarts[mid] <= pos) { ans = mid; lo = mid + 1; }
    else hi = mid - 1;
  }
  return ans + 1;
}

function allMatches(re: RegExp, text: string, depth: Int32Array): number[] {
  const r = new RegExp(re.source, "gu");
  const res: number[] = [];
  let m: RegExpExecArray | null;
  while ((m = r.exec(text)) !== null) {
    if (depth[m.index] === 0) res.push(m.index);
  }
  return res;
}

// 本体境界: キーワード後、最初の depth0 `:=` または `where` (region 内)。なければ regionEnd。
function findCut(p: Parsed, start: number, end: number): number {
  let best = end;
  let q = p.masked.indexOf(":=", start);
  while (q !== -1 && q < end) {
    if (p.depth[q] === 0) { best = Math.min(best, q); break; }
    q = p.masked.indexOf(":=", q + 2);
  }
  const wreg = new RegExp(kw(["where"]).source, "gu");
  wreg.lastIndex = start;
  let m: RegExpExecArray | null;
  while ((m = wreg.exec(p.masked)) !== null) {
    if (m.index >= end) break;
    if (p.depth[m.index] === 0) { best = Math.min(best, m.index); break; }
  }
  return best;
}

function attachDoc(p: Parsed, sigStart: number): string | null {
  // sigStart 直前に docstring があり、間に空白/属性/修飾子しかなければ付ける
  let cand: { end: number; text: string } | null = null;
  for (const ds of p.docSpans) {
    if (ds.end <= sigStart) { if (!cand || ds.end > cand.end) cand = ds; }
  }
  if (!cand) return null;
  const gap = p.src.slice(cand.end, sigStart);
  if (/^\s*(@\[[^\]]*\]\s*)*((private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*$/.test(gap)) {
    return cand.text;
  }
  return null;
}

function extendModifiers(p: Parsed, kwStart: number): number {
  // キーワード直前の修飾子トークンを取り込む
  let s = kwStart;
  for (;;) {
    const before = p.src.slice(0, s);
    const m = before.match(/(private|protected|noncomputable|partial|unsafe|scoped|local)\s+$/);
    if (m) s -= m[0].length; else break;
  }
  return s;
}

function parseDecls(p: Parsed): { decls: Decl[]; ctxs: Ctx[] } {
  const kwRe = kw(KEYWORDS);
  const ctxRe = kw(CTX);
  const declPos = allMatches(kwRe, p.masked, p.depth);
  const ctxPos = allMatches(ctxRe, p.masked, p.depth);

  // 境界 = 宣言開始 + context コマンド位置 (本体は次の境界で切る)
  const boundaries = [...declPos, ...ctxPos].sort((a, b) => a - b);
  const nextBoundary = (pos: number) => {
    for (const b of boundaries) if (b > pos) return b;
    return p.src.length;
  };

  // 第1パス: 宣言の骨格 (ownStart = docstring 起点 or sigStart) を確定
  const raw: (Decl & { ownStart: number })[] = [];
  for (const pos of declPos) {
    const kwMatch = p.masked.slice(pos).match(/^\w+/);
    const kind = kwMatch ? kwMatch[0] : "?";
    const afterKw = pos + kind.length;
    const regionEnd = nextBoundary(pos);
    const cut = findCut(p, afterKw, regionEnd);
    // 名前: キーワード後の最初のトークン
    const nameStr = p.src.slice(afterKw, cut);
    const nm = nameStr.match(/^\s*([^\s(){}\[\]:⦃⦄⟨⟩]+)/);
    const name = nm ? nm[1] : "<anonymous>";
    const sigStart = extendModifiers(p, pos);
    const doc = attachDoc(p, sigStart);
    const body = p.masked.slice(cut, regionEnd);
    const hasSorry = new RegExp(kw(["sorry"]).source, "u").test(body);
    const ownStart = doc !== null
      ? p.docSpans.find((d) => d.text === doc && d.end <= sigStart)?.start ?? sigStart
      : sigStart;
    raw.push({ pos, sigStart, kind, name, cut, regionEnd, hasSorry, residuals: [], doc, ownStart });
  }
  // 第2パス: residual は自分の ownStart 〜 次の宣言の ownStart まで (次宣言の docstring を巻き込まない)
  const decls: Decl[] = raw.map((d, idx) => {
    const resEnd = idx + 1 < raw.length ? raw[idx + 1].ownStart : p.src.length;
    const region = p.src.slice(d.ownStart, resEnd);
    const residuals = [...new Set([...region.matchAll(/@residual\(([^)]*)\)/g)].map((m) => m[1]))];
    return { pos: d.pos, sigStart: d.sigStart, kind: d.kind, name: d.name, cut: d.cut, regionEnd: d.regionEnd, hasSorry: d.hasSorry, residuals, doc: d.doc };
  });

  const ctxs: Ctx[] = [];
  for (const pos of ctxPos) {
    const eol = p.src.indexOf("\n", pos);
    const text = p.src.slice(pos, eol === -1 ? p.src.length : eol).trim();
    ctxs.push({ pos, text });
  }
  return { decls, ctxs };
}

function dedent(s: string): string[] {
  const lines = s.replace(/\s+$/, "").split("\n").map((l) => l.replace(/\s+$/, ""));
  // 先頭の空行除去
  while (lines.length && lines[0].trim() === "") lines.shift();
  const indents = lines.filter((l) => l.trim() !== "").map((l) => l.match(/^\s*/)![0].length);
  const min = indents.length ? Math.min(...indents) : 0;
  return lines.map((l) => l.slice(min));
}

// ANSI 色付け。パイプ/リダイレクト時や NO_COLOR 指定時は素のテキストにする
// (エージェントが出力をキャプチャするときに制御文字を混ぜない)。
const USE_COLOR = !Deno.env.get("NO_COLOR") && Deno.stdout.isTerminal();
const wrap = (code: string, s: string) => USE_COLOR ? `\x1b[${code}m${s}\x1b[0m` : s;
const bold = (s: string) => wrap("1", s);
const dim = (s: string) => wrap("2", s);
const green = (s: string) => wrap("32", s);
const yellow = (s: string) => wrap("33", s);
const cyan = (s: string) => wrap("36", s);

function render(path: string, p: Parsed, decls: Decl[], ctxs: Ctx[], mode: Mode, showCtx: boolean, onlySorry: boolean): string {
  const lines: string[] = [];
  lines.push(bold(path));
  const filtered = onlySorry ? decls.filter((d) => d.hasSorry) : decls;

  // 宣言と context を位置順にマージ
  type Item = { pos: number; kind: "decl"; d: Decl } | { pos: number; kind: "ctx"; c: Ctx };
  const items: Item[] = [];
  for (const d of filtered) items.push({ pos: d.pos, kind: "decl", d });
  if (showCtx && !onlySorry) for (const c of ctxs) items.push({ pos: c.pos, kind: "ctx", c });
  items.sort((a, b) => a.pos - b.pos);

  let nSorry = 0;
  for (const it of items) {
    if (it.kind === "ctx") {
      const ln = lineOf(p.lineStarts, it.c.pos);
      lines.push(dim(`L${ln} · ${it.c.text}`));
      continue;
    }
    const d = it.d;
    const ln = lineOf(p.lineStarts, d.pos);
    const flags: string[] = [];
    if (d.hasSorry) { flags.push(yellow("sorry")); nSorry++; }
    for (const r of d.residuals) flags.push(cyan(`@residual(${r})`));
    const flagStr = flags.length ? "  " + flags.map((f) => `⟨${f}⟩`).join(" ") : "";
    const head = `${bold("L" + ln)} ${d.kind} ${green(d.name)}${flagStr}`;

    if (mode === "names") { lines.push(head); continue; }

    if (mode === "doc" && d.doc) {
      for (const dl of dedent(d.doc)) lines.push(dim(`  ${dl}`));
    }
    lines.push(head);
    const sig = dedent(p.src.slice(d.sigStart, d.cut));
    const cap = 16;
    sig.slice(0, cap).forEach((sl) => lines.push(`    ${sl}`));
    if (sig.length > cap) lines.push(dim(`    … (+${sig.length - cap} 行)`));
    lines.push("");
  }

  lines.push(dim(`— ${filtered.length} decls${onlySorry ? "" : `, ${nSorry} with sorry`}`));
  return lines.join("\n");
}

function main() {
  const args = [...Deno.args];
  let mode: Mode = "sig";
  let showCtx = true;
  let onlySorry = false;
  const files: string[] = [];
  for (const a of args) {
    if (a === "--doc") mode = "doc";
    else if (a === "--names") mode = "names";
    else if (a === "--no-context") showCtx = false;
    else if (a === "--sorry") onlySorry = true;
    else if (a.startsWith("--")) { console.error(`unknown flag: ${a}`); Deno.exit(2); }
    else files.push(a);
  }
  if (files.length === 0) {
    console.error("usage: sig_view.ts [--doc|--names] [--no-context] [--sorry] <file.lean> ...");
    Deno.exit(2);
  }
  const outs: string[] = [];
  let failed = false;
  for (const f of files) {
    let src: string;
    try {
      src = Deno.readTextFileSync(f);
    } catch (e) {
      console.error(`skip ${f}: ${e instanceof Error ? e.message : e}`);
      failed = true;
      continue;
    }
    const p = maskAndScan(src);
    const { decls, ctxs } = parseDecls(p);
    outs.push(render(f, p, decls, ctxs, mode, showCtx, onlySorry));
  }
  console.log(outs.join("\n\n"));
  if (failed) Deno.exit(1);
}

main();
