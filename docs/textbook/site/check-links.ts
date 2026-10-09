#!/usr/bin/env -S deno run -A
import { existsSync, readdirSync, readFileSync, mkdtempSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { tmpdir } from 'node:os';

const here = dirname(fileURLToPath(import.meta.url));
const dist = resolve(here, 'dist');
const repo = resolve(here, '../../..');
const SOURCE_RE = /^https:\/\/github\.com\/FujiHaruka\/information-theory\/blob\/([^/]+)\/([^#]+)(?:#L(\d+))?$/;
const APIDOC_RE = /^https:\/\/fujiharuka\.github\.io\/information-theory\/([^#]+)\.html#(.+)$/;

if (!existsSync(dist)) {
  console.error('dist/ がありません。先に build.mjs を回してください');
  Deno.exit(2);
}

function run(cmd: string, args: string[]) {
  const p = new Deno.Command(cmd, { args, cwd: repo, stdout: 'piped', stderr: 'piped' }).outputSync();
  const dec = new TextDecoder();
  return { ok: p.success, out: dec.decode(p.stdout), err: dec.decode(p.stderr) };
}
const git = (...args: string[]) => run('git', args);

const decode = (s: string) => s.replace(/&quot;/g, '"').replace(/&#39;/g, "'")
  .replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&');

const pages = readdirSync(dist).filter((f) => f.endsWith('.html'));
const ids = new Map<string, Set<string>>();
const links: { page: string; href: string }[] = [];
for (const f of pages) {
  const html = readFileSync(join(dist, f), 'utf8');
  ids.set(f, new Set([...html.matchAll(/\sid="([^"]*)"/g)].map((m) => decode(m[1]))));
  for (const m of html.matchAll(/\shref="([^"]*)"/g)) links.push({ page: f, href: decode(m[1]) });
}

const failures: string[] = [];
const fail = (page: string, href: string, why: string) => failures.push(`${page}: ${href}\n    ${why}`);

const latestTag = git('describe', '--tags', '--abbrev=0').out.trim();
const lineCounts = new Map<string, number | null>();
function linesAt(ref: string, path: string) {
  const key = `${ref}:${path}`;
  if (!lineCounts.has(key)) {
    const r = git('show', key);
    lineCounts.set(key, r.ok ? r.out.split('\n').length - (r.out.endsWith('\n') ? 1 : 0) : null);
  }
  return lineCounts.get(key)!;
}
const refOk = new Map<string, string | null>();
function checkRef(ref: string) {
  if (!refOk.has(ref)) {
    if (!git('rev-parse', '--verify', '--quiet', `refs/tags/${ref}`).ok) refOk.set(ref, `タグ ${ref} が手元に無い`);
    else if (!git('merge-base', '--is-ancestor', ref, 'origin/main').ok) {
      refOk.set(ref, `タグ ${ref} が origin/main に含まれない（push されていない恐れ）`);
    } else refOk.set(ref, null);
  }
  return refOk.get(ref);
}

const apidoc = new Map<string, { module: string; path: string; uses: string[] }>();
const sourceRefs = new Set<string>();
const counts = { internal: 0, source: 0, apidoc: 0, unchecked: 0 };

for (const { page, href } of links) {
  let m;
  if ((m = href.match(SOURCE_RE))) {
    counts.source++;
    const [, ref, path, line] = m;
    sourceRefs.add(ref);
    const bad = checkRef(ref);
    if (bad) { fail(page, href, bad); continue; }
    const n = linesAt(ref, path);
    if (n === null) fail(page, href, `${ref} に ${path} が無い`);
    else if (line && Number(line) > n) fail(page, href, `${ref} の ${path} は ${n} 行しかない`);
  } else if ((m = href.match(APIDOC_RE))) {
    counts.apidoc++;
    const [, modPath, fqn] = m;
    const path = `${modPath}.lean`;
    if (linesAt(latestTag, path) === null) { fail(page, href, `${latestTag} に ${path} が無い`); continue; }
    const e = apidoc.get(fqn) ?? { module: modPath.replaceAll('/', '.'), path, uses: [] };
    e.uses.push(page);
    apidoc.set(fqn, e);
  } else if (/^[a-z]+:/i.test(href)) {
    counts.unchecked++;
  } else {
    counts.internal++;
    const [file, frag] = href.split('#');
    const target = file === '' ? page : file.replace(/^\.\//, '');
    if (!existsSync(join(dist, target))) { fail(page, href, 'ファイルが dist/ に無い'); continue; }
    if (frag && target.endsWith('.html') && !ids.get(target)?.has(decodeURIComponent(frag))) {
      fail(page, href, `${target} に id「${frag}」が無い`);
    }
  }
}

for (const ref of sourceRefs) {
  if (ref !== latestTag) {
    failures.push(`ソースのリンクは ${ref} に固定されているが、API ドキュメントは最新タグ ${latestTag} のもの`);
  }
}

// API ドキュメントの完全名は build.mjs がテキスト走査で組むので、走査と独立に Lean の環境で確かめる。
if (apidoc.size > 0) {
  const lit = (s: string) => JSON.stringify(s);
  const entries = [...apidoc].map(([fqn, e]) => `  (${lit(fqn)}, ${lit(e.module)})`).join(',\n');
  const dir = mkdtempSync(join(tmpdir(), 'textbook-links-'));
  const file = join(dir, 'CheckPointers.lean');
  writeFileSync(file, `import InformationTheory
open Lean

def pointers : List (String × String) := [
${entries}
]

#eval show CoreM Unit from do
  let env ← getEnv
  for (n, m) in pointers do
    match env.getModuleIdxFor? n.toName with
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      unless mod.toString == m do IO.println s!"MODULE\\t{n}\\t{mod}"
    | none => IO.println s!"MISSING\\t{n}"
`);
  const r = run('lake', ['env', 'lean', file]);
  if (!r.ok) {
    console.error(r.out + r.err);
    console.error('Lean での確認に失敗した（`lake build InformationTheory` で olean を新しくしてから回す）');
    Deno.exit(2);
  }
  for (const row of r.out.trim().split('\n').filter(Boolean)) {
    const [kind, fqn, actual] = row.split('\t');
    const e = apidoc.get(fqn)!;
    const short = fqn.split('.').at(-1)!;
    const declRe = `(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)[[:space:]]+${short.replace(/[.'?!]/g, '.')}([[:space:]]|$)`;
    const atTag = git('grep', '-qE', declRe, latestTag, '--', e.path).ok;
    const atHead = git('grep', '-qE', declRe, 'HEAD', '--', e.path).ok;
    const where = `（使用: ${[...new Set(e.uses)].join(', ')}）`;
    if (atTag && !atHead) {
      console.log(`note: ${fqn} は ${latestTag} 以降に ${e.path} から消えた。${latestTag} の API ドキュメントでは有効${where}`);
    } else if (kind === 'MODULE') {
      failures.push(`${fqn}: リンク先は ${e.module} だが、宣言は ${actual} にある${where}`);
    } else {
      failures.push(`${fqn}: この完全名の宣言が無い（名前空間の取り違えの恐れ）${where}`);
    }
  }
}

console.log(`サイト内 ${counts.internal} 件 / ソース ${counts.source} 件 / API ドキュメント ${counts.apidoc} 件`
  + `（宣言 ${apidoc.size} 個）を検査。その他の外部リンク ${counts.unchecked} 件は対象外`);
if (failures.length) {
  console.log(`\nリンク切れ ${failures.length} 件:\n` + failures.map((f) => `  ${f}`).join('\n'));
  Deno.exit(1);
}
console.log('リンク切れなし');
