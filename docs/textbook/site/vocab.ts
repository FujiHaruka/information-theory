#!/usr/bin/env -S deno run -A
// 原稿の語彙を点検するための候補出し。判定はしない（同義語かどうかは意味の問題で、
// 字面からは決まらない。字面の近さで機械判定を試みると、偽陽性だけが積み上がる）。
//
// 出力は 3 つ。
//   (1) 原語混入 — 訳語があるのに原語で書いた箇所。規則が明確なのでここは判定まで機械が行う
//   (2) 本書が名づけた語 — 判定なし。節タイトル・主張名・定義の太字だけを拾う。原稿が意識して
//       名づけた語はここに全部出るので、1 語ずつ標準名と突き合わせる（執筆原則 §6）
//   (3) 章ごとの初出術語 — 判定なし。目を通して、既出の語と同じ概念を別の語で書いていないかを探す
//
// 使い方: docs/textbook/site/vocab.ts [章スラッグ...]   （既定は全章）
// 揺れを見つけたら `terminology.mjs` に 1 行足す。以後は build.mjs が毎回検査する。

import { TERMS } from './terminology.mjs';
import { chapters } from './chapters.mjs';

const root = new URL('..', import.meta.url).pathname; // docs/textbook

// 章と、その本文ファイル。順序が初出判定に効くので、build.mjs と同じ配列を読む
// （章立ての SoT は chapters.mjs 1 箇所）。
const CHAPTERS: { slug: string; files: string[] }[] = chapters.map((c) => ({
  slug: c.slug,
  files: c.sections ? c.sections.map((s) => s.src) : [c.src],
}));

// 原語混入の検査から外す語。固有名詞・環境タグ・訳語のない術語だけを入れる。
// 訳語がある語をここに入れてはいけない（それは terminology.mjs の avoid 側の仕事）。
const ALLOW = new Set([
  // 人名・書誌（執筆原則 §6: 人名はラテン文字）
  'Cauchy', 'Cover', 'Thomas', 'Elements', 'Information', 'Theory', 'ed.',
  'Fisher', 'Gibbs', 'Jensen', 'Neyman', 'Shannon', 'Fano', 'Markov', 'Kraft',
  'McMillan', 'Breiman', 'Birkhoff', 'Huffman', 'Lempel', 'Ziv', 'Csiszar',
  'Cesàro', 'Lévy', 'Borel', 'Cantelli', 'Weierstrass', 'Chebyshev', 'Lagrange',
  'Legendre', 'Kelly',
  // 環境タグ（:::）
  'definition', 'theorem', 'proposition', 'lemma', 'corollary', 'example',
  'proof', 'formalized', 'formalization-note', 'notation-preview',
  // ツール・言語
  'Lean', 'Mathlib', 'MathJax',
  // 訳語のない術語・標準的な略語
  'i.i.d.', 'pmf', 'AEP', 'KL', 'nat', 'bit',
  // 規格名（訳語がなく、日本語の文献もこの綴りで書く）。数字は上の正規表現に入らないので
  // 「UTF-8」はハイフンまでが 1 語として拾われる
  'UTF-',
  // 本プロジェクトの用語（CLAUDE.md の完成判定）
  'done', 'sorry', 'residual',
]);

function stripCodeAndMath(s: string): string {
  const blank = (m: string) => m.replace(/[^\n]/g, ' ');
  return s
    .replace(/```[\s\S]*?```/g, blank)
    .replace(/\$\$[\s\S]*?\$\$/g, blank)
    .replace(/\\\[[\s\S]*?\\\]/g, blank) // 第2〜5章の LaTeX 括弧デリミタ
    .replace(/\\\([\s\S]*?\\\)/g, blank)
    .replace(/`[^`\n]*`/g, blank)
    .replace(/\$[^$\n]*\$/g, blank);
}

const targets = Deno.args.length ? CHAPTERS.filter((c) => Deno.args.includes(c.slug)) : CHAPTERS;
const knownAvoid = new Set(TERMS.flatMap((t: { avoid: string[] }) => t.avoid));

// --- (1) 原語混入 ---
console.log('## 原語混入（訳語があるなら訳語で書く。執筆原則 §6）\n');
let foreign = 0;
for (const c of targets) {
  for (const f of c.files) {
    const lines = stripCodeAndMath(Deno.readTextFileSync(root + f)).split('\n');
    lines.forEach((line, i) => {
      for (const m of line.matchAll(/[A-Za-zÀ-ÿ][A-Za-zÀ-ÿ\-\.']{2,}/g)) {
        const w = m[0];
        if (ALLOW.has(w) || knownAvoid.has(w)) continue; // 既知の禁止語は build.mjs が報告済み
        // 「記憶のない（memoryless）通信路」のような初出の原語併記は認める（執筆原則 §6）。
        // 併記は「（feature function）」のように複数語のこともあるので、開き括弧から
        // 途切れずに続く欧文の並びを丸ごと外す（間に和文や閉じ括弧が入れば当たらない）。
        if (/[（(][A-Za-zÀ-ÿ\-\.'’ ]*$/.test(line.slice(0, m.index))) continue;
        foreign += 1;
        console.log(`  ${f}:${i + 1}  ${w}`);
      }
    });
  }
}
console.log(foreign === 0 ? '  （なし）\n' : `  計 ${foreign} 件\n`);

// --- (2) 本書が名づけた語 ---
// 原稿が意識して名づけた語だけを拾う。節タイトル（`# N.M …`）、主張・定義のタグ行の名前、
// 定義ブロックの中の太字がその全部で、章あたり 20 語前後にしかならない。ここは既出語との
// 突き合わせではなく、**外の標準名との突き合わせ**をする場所である（本書の中だけを見ていても
// 標準から外れた命名には気づけない。実例: 情報源と書き続けながら定理名だけ「源符号化定理」に
// 縮んでいた——標準は「情報源符号化定理」）。
// 太字は末尾に句点を打つ太字リード（`**面積として読む.**`、執筆原則 §5）を落として拾う。
// 見出しに倣った半角ピリオドと、地の文の全角ピリオド（執筆原則 §9）の両方が末尾に来る。
function coinedTerms(text: string): string[] {
  const out: string[] = [];
  let inDefinition = false;
  for (const line of text.split('\n')) {
    const heading = line.match(/^#\s+(?:\d+(?:\.\d+)*\s+)?(.+?)\s*$/);
    if (heading) { out.push(heading[1]); continue; }
    const tag = line.match(/^:::\s+(\S+)(.*)$/);
    if (tag) {
      inDefinition = tag[1] === 'definition';
      const name = tag[2].trim().replace(/^\d+(?:\.\d+)*\s*/, '');
      if (name && /^(definition|theorem|proposition|lemma|corollary|example)$/.test(tag[1])) {
        out.push(name);
      }
      continue;
    }
    if (/^:::\s*$/.test(line)) { inDefinition = false; continue; }
    if (!inDefinition) continue;
    for (const m of line.matchAll(/\*\*([^*\n]+)\*\*/g)) {
      const w = m[1].trim();
      if (/[.．]$/.test(w) || w.length > 14 || /\s/.test(w)) continue;
      out.push(w);
    }
  }
  return out;
}

console.log('## 本書が名づけた語（判定なし。1 語ずつ、日本語の標準名と突き合わせる。執筆原則 §6）\n');
const named = new Set<string>();
for (const c of CHAPTERS) {
  const words = c.files.flatMap((f) => coinedTerms(stripCodeAndMath(Deno.readTextFileSync(root + f))));
  const fresh = [...new Set(words)].filter((w) => !named.has(w));
  for (const w of words) named.add(w);
  // 章を絞って呼ばれても初出判定は全章の順序で行う（前章で名づけた語を再掲しないため）。
  if (!targets.includes(c)) continue;
  console.log(`### ${c.slug} — 新しく名づけた語 ${fresh.length} 語`);
  console.log('  ' + fresh.join(' / ') + '\n');
}

// --- (3) 章ごとの初出術語 ---
console.log('## 章ごとの初出術語（判定なし。既出の語と同じ概念を別の語で書いていないか探す）\n');
const seen = new Set<string>();
for (const c of targets) {
  const count = new Map<string, number>();
  for (const f of c.files) {
    const text = stripCodeAndMath(Deno.readTextFileSync(root + f));
    for (const w of text.match(/[一-鿿゠-ヿー]{3,}/g) ?? []) {
      count.set(w, (count.get(w) ?? 0) + 1);
    }
  }
  const fresh = [...count.entries()].filter(([w]) => !seen.has(w)).sort((a, b) => b[1] - a[1]);
  for (const [w] of count) seen.add(w);
  console.log(`### ${c.slug} — 初出 ${fresh.length} 語`);
  console.log('  ' + fresh.map(([w, n]) => `${w}(${n})`).join(' ') + '\n');
}
