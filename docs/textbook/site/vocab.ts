#!/usr/bin/env -S deno run -A
// 原稿の語彙を点検するための候補出し。判定はしない（同義語かどうかは意味の問題で、
// 字面からは決まらない。字面の近さで機械判定を試みると、偽陽性だけが積み上がる）。
//
// 出力は 2 つ。
//   (1) 原語混入 — 訳語があるのに原語で書いた箇所。規則が明確なのでここは判定まで機械が行う
//   (2) 章ごとの初出術語 — 判定なし。目を通して、既出の語と同じ概念を別の語で書いていないかを探す
//
// 使い方: docs/textbook/site/vocab.ts [章スラッグ...]   （既定は全章）
// 揺れを見つけたら `terminology.mjs` に 1 行足す。以後は build.mjs が毎回検査する。

import { TERMS } from './terminology.mjs';

const root = new URL('..', import.meta.url).pathname; // docs/textbook

// 章と、その本文ファイル。build.mjs の chapters と揃える（順序が初出判定に効く）。
const CHAPTERS: { slug: string; files: string[] }[] = [
  {
    slug: 'ch01',
    files: [
      'ch01/01-entropy.md', 'ch01/02-joint-conditional-entropy.md',
      'ch01/03-mutual-information.md', 'ch01/04-conditional-mutual-information.md',
      'ch01/05-chain-rules.md', 'ch01/06-information-inequality.md',
      'ch01/07-log-sum-inequality.md', 'ch01/08-data-processing-inequality.md',
      'ch01/09-sufficient-statistics.md', 'ch01/10-fano.md',
    ],
  },
  { slug: 'ch02', files: ['ch02-aep.md'] },
  { slug: 'ch03', files: ['ch03-entropy-rate.md'] },
  { slug: 'ch04', files: ['ch04-channel-capacity.md'] },
  { slug: 'ch05', files: ['ch05-max-entropy.md'] },
];

// 原語混入の検査から外す語。固有名詞・環境タグ・訳語のない術語だけを入れる。
// 訳語がある語をここに入れてはいけない（それは terminology.mjs の avoid 側の仕事）。
const ALLOW = new Set([
  // 人名・書誌（執筆原則 §6: 人名はラテン文字）
  'Cauchy', 'Cover', 'Thomas', 'Elements', 'Information', 'Theory', 'ed.',
  'Fisher', 'Gibbs', 'Jensen', 'Neyman', 'Shannon', 'Fano', 'Markov', 'Kraft',
  'McMillan', 'Breiman', 'Birkhoff', 'Huffman', 'Lempel', 'Ziv', 'Csiszar',
  // 環境タグ（:::）
  'definition', 'theorem', 'proposition', 'lemma', 'corollary', 'example',
  'proof', 'formalized', 'formalization-note', 'notation-preview',
  // ツール・言語
  'Lean', 'Mathlib', 'KaTeX',
  // 訳語のない術語・標準的な略語
  'i.i.d.', 'pmf', 'AEP', 'KL', 'nat', 'bit',
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
      for (const m of line.matchAll(/[A-Za-z][A-Za-z\-\.']{2,}/g)) {
        const w = m[0];
        if (ALLOW.has(w) || knownAvoid.has(w)) continue; // 既知の禁止語は build.mjs が報告済み
        // 「記憶のない（memoryless）通信路」のような初出の原語併記は認める（執筆原則 §6）
        if (/[（(]$/.test(line.slice(0, m.index))) continue;
        foreign += 1;
        console.log(`  ${f}:${i + 1}  ${w}`);
      }
    });
  }
}
console.log(foreign === 0 ? '  （なし）\n' : `  計 ${foreign} 件\n`);

// --- (2) 章ごとの初出術語 ---
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
