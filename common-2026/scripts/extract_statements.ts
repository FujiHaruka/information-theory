#!/usr/bin/env -S deno run -A
// extract_statements.ts — extract theorem/lemma statements + doc comments from Lean
// source files, dropping the proof body. Produces a single Markdown "spec sheet".
//
// Usage:
//   deno run -A scripts/extract_statements.ts [paths...] [--out <file>] [--kinds k1,k2]
//
// Defaults:
//   paths    = Common2026
//   --out    = docs/formalized-statements.md
//   --kinds  = theorem,lemma,def   (def included so predicate-level honesty
//             defects — e.g. `def IsFoo : Prop := True` — land in the audit DB)
//   --exclude= Common2026/Exam/   (comma-separated path substrings to skip)
//
// Approach: a small comment/string/bracket-aware scanner over the *original* source
// (so signatures are preserved verbatim). For each declaration whose keyword is in
// --kinds, the signature is everything from the keyword up to the first `:=` that
// occurs at bracket-depth 0 (the proof separator); autoParam `(h : P := by …)` and
// structure-literal `:=` are inside brackets so they are skipped. A `/-- … -/` doc
// comment immediately preceding the declaration (only whitespace / attributes /
// modifiers in between) is attached; `/-! … -/` section docs are not.

const OPEN = new Set(["(", "[", "{", "⦃", "⟨"]);
const CLOSE = new Set([")", "]", "}", "⦄", "⟩"]);
const MODIFIER = new Set([
  "private", "protected", "noncomputable", "nonrec",
  "partial", "unsafe", "scoped", "local", "mutual",
]);

function isWordChar(ch: string | undefined): boolean {
  return ch !== undefined && /[\p{L}\p{N}_'!?]/u.test(ch);
}

function matchKeywordAt(src: string, i: number, kw: string): boolean {
  if (!src.startsWith(kw, i)) return false;
  return !isWordChar(src[i - 1]) && !isWordChar(src[i + kw.length]);
}

// Skip one lexical unit starting at i that is NOT plain code: line comment, block /
// doc comment (nested), or string literal. Returns the index just past it, plus the
// kind of comment found (for doc-attachment). Returns null if src[i] is plain code.
type Skip = { next: number; doc?: string; mod?: boolean };
function skipNonCode(src: string, i: number): Skip | null {
  const c = src[i];
  // line comment  --...
  if (c === "-" && src[i + 1] === "-") {
    let j = i + 2;
    while (j < src.length && src[j] !== "\n") j++;
    return { next: j };
  }
  // block / doc comment  /- ... -/  (nested)
  if (c === "/" && src[i + 1] === "-") {
    const third = src[i + 2];
    const kind = third === "-" ? "doc" : third === "!" ? "mod" : "plain";
    let depth = 0;
    let j = i;
    while (j < src.length) {
      if (src[j] === "/" && src[j + 1] === "-") { depth++; j += 2; }
      else if (src[j] === "-" && src[j + 1] === "/") {
        depth--; j += 2;
        if (depth === 0) break;
      } else j++;
    }
    if (kind === "doc") {
      const inner = src.slice(i + 3, j - 2);
      return { next: j, doc: inner };
    }
    if (kind === "mod") return { next: j, mod: true };
    return { next: j };
  }
  // string literal
  if (c === '"') {
    let j = i + 1;
    while (j < src.length) {
      if (src[j] === "\\") { j += 2; continue; }
      if (src[j] === '"') { j++; break; }
      j++;
    }
    return { next: j };
  }
  return null;
}

// From `start`, find the index of the `:=` that lies at bracket-depth 0 (the proof
// separator). Returns -1 if none before EOF.
function findProofAssign(src: string, start: number): number {
  let i = start;
  let depth = 0;
  while (i < src.length) {
    const sk = skipNonCode(src, i);
    if (sk) { i = sk.next; continue; }
    const c = src[i];
    if (OPEN.has(c)) { depth++; i++; continue; }
    if (CLOSE.has(c)) { depth = Math.max(0, depth - 1); i++; continue; }
    if (depth === 0 && c === ":" && src[i + 1] === "=") return i;
    i++;
  }
  return -1;
}

function gapIsAttachable(gap: string): boolean {
  // Only whitespace, @[...] attributes, and modifier words may sit between a doc
  // comment and the declaration it documents.
  const stripped = gap.replace(/@\[[^\]]*\]/g, " ");
  for (const tok of stripped.split(/\s+/)) {
    if (tok === "") continue;
    if (!MODIFIER.has(tok)) return false;
  }
  return true;
}

function cleanDoc(raw: string): string {
  return raw.replace(/[ \t]+$/gm, "").trim();
}

export const DEFAULT_KINDS = ["theorem", "lemma", "def"];

export type Decl = {
  kind: string;
  name: string;
  ns: string;
  signature: string;
  doc: string | null;
  line: number;
  declStart: number;
  bodyStart: number;
  body: string;
};

export function parse(src: string, kinds: Set<string>): Decl[] {
  const decls: Decl[] = [];
  const nsStack: string[] = [];
  let pendingDoc: { text: string; end: number } | null = null;
  let i = 0;
  let depth = 0;

  const readIdent = (j: number): { id: string; next: number } => {
    while (j < src.length && /\s/.test(src[j])) j++;
    const s = j;
    while (j < src.length && (isWordChar(src[j]) || src[j] === ".")) j++;
    return { id: src.slice(s, j), next: j };
  };

  while (i < src.length) {
    const sk = skipNonCode(src, i);
    if (sk) {
      if (sk.doc !== undefined) pendingDoc = { text: sk.doc, end: sk.next };
      else if (sk.mod) pendingDoc = null;
      i = sk.next;
      continue;
    }
    const c = src[i];
    if (OPEN.has(c)) { depth++; i++; continue; }
    if (CLOSE.has(c)) { depth = Math.max(0, depth - 1); i++; continue; }

    if (depth === 0 && !isWordChar(src[i - 1])) {
      // namespace / end tracking
      if (matchKeywordAt(src, i, "namespace")) {
        const { id, next } = readIdent(i + "namespace".length);
        if (id) nsStack.push(id);
        i = next;
        continue;
      }
      if (matchKeywordAt(src, i, "end")) {
        const { id, next } = readIdent(i + "end".length);
        if (id && nsStack.length && nsStack[nsStack.length - 1] === id) nsStack.pop();
        i = next;
        continue;
      }
      // declaration keyword
      let matched: string | null = null;
      for (const kw of kinds) {
        if (matchKeywordAt(src, i, kw)) { matched = kw; break; }
      }
      if (matched) {
        const declStart = i;
        const { id: name } = readIdent(i + matched.length);
        const sigEnd = findProofAssign(src, i + matched.length);
        if (sigEnd !== -1) {
          const signature = src.slice(declStart, sigEnd).replace(/\s+$/, "");
          let doc: string | null = null;
          if (pendingDoc && gapIsAttachable(src.slice(pendingDoc.end, declStart))) {
            doc = cleanDoc(pendingDoc.text);
          }
          const line = src.slice(0, declStart).split("\n").length;
          decls.push({
            kind: matched,
            name,
            ns: nsStack.join("."),
            signature,
            doc,
            line,
            declStart,
            bodyStart: sigEnd + 2,
            body: "",
          });
          pendingDoc = null;
          i = sigEnd + 2;
          continue;
        }
      }
    }
    i++;
  }
  // Body of each decl spans from just past its `:=` to the start of the next decl
  // (an over-approximation that may include trailing `end`/section lines; fine for
  // the cheap honesty heuristics, which are verified authoritatively when flagged).
  for (let k = 0; k < decls.length; k++) {
    const end = k + 1 < decls.length ? decls[k + 1].declStart : src.length;
    decls[k].body = src.slice(decls[k].bodyStart, end);
  }
  return decls;
}

async function collectLeanFiles(
  paths: string[],
  exclude: string[],
): Promise<string[]> {
  const out: string[] = [];
  const visit = async (p: string) => {
    if (exclude.some((e) => p.includes(e))) return;
    let info: Deno.FileInfo;
    try { info = await Deno.stat(p); } catch { return; }
    if (info.isFile) {
      if (p.endsWith(".lean")) out.push(p);
      return;
    }
    if (info.isDirectory) {
      for await (const e of Deno.readDir(p)) {
        await visit(`${p}/${e.name}`.replace(/\/+/g, "/"));
      }
    }
  };
  for (const p of paths) await visit(p);
  return out.sort();
}

function fence(sig: string): string {
  return "```lean\n" + sig + "\n```";
}

async function main() {
  const args = [...Deno.args];
  let out = "docs/formalized-statements.md";
  let kinds = new Set(DEFAULT_KINDS);
  let exclude = ["Common2026/Exam/"];
  let noDocs = false;
  const paths: string[] = [];
  for (let k = 0; k < args.length; k++) {
    if (args[k] === "--out") { out = args[++k]; continue; }
    if (args[k] === "--no-docs") { noDocs = true; continue; }
    if (args[k] === "--kinds") {
      kinds = new Set(args[++k].split(",").map((s) => s.trim()).filter(Boolean));
      continue;
    }
    if (args[k] === "--exclude") {
      exclude = args[++k].split(",").map((s) => s.trim()).filter(Boolean);
      continue;
    }
    paths.push(args[k]);
  }
  if (paths.length === 0) paths.push("Common2026");

  const files = await collectLeanFiles(paths, exclude);
  const today = new Date().toISOString().slice(0, 10);
  const lines: string[] = [];
  lines.push("# Formalized statements (auto-generated)");
  lines.push("");
  lines.push(
    `_Generated ${today} by \`scripts/extract_statements.ts\`. ` +
      `Statements only — proof bodies omitted. Kinds: ${[...kinds].join(", ")}._`,
  );
  lines.push("");

  let total = 0;
  const perFile: { file: string; decls: Decl[] }[] = [];
  for (const f of files) {
    const src = await Deno.readTextFile(f);
    const decls = parse(src, kinds);
    if (decls.length) {
      perFile.push({ file: f, decls });
      total += decls.length;
    }
  }

  lines.push(`**${total} declarations across ${perFile.length} files.**`);
  lines.push("");

  for (const { file, decls } of perFile) {
    lines.push(`## ${file}`);
    lines.push("");
    for (const d of decls) {
      const full = d.ns ? `${d.ns}.${d.name}` : d.name;
      lines.push(`### \`${full}\` _(${d.kind}, L${d.line})_`);
      lines.push("");
      if (d.doc && !noDocs) {
        lines.push(d.doc);
        lines.push("");
      }
      lines.push(fence(d.signature));
      lines.push("");
    }
  }

  await Deno.writeTextFile(out, lines.join("\n"));
  console.error(`wrote ${out}: ${total} declarations across ${perFile.length} files`);
}

if (import.meta.main) await main();
