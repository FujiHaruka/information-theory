import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import MarkdownIt from 'npm:markdown-it@14';
import * as katexPlugin from 'npm:@vscode/markdown-it-katex@1';

const __dirname = dirname(fileURLToPath(import.meta.url));
const root = resolve(__dirname, '..'); // docs/textbook
const distDir = resolve(__dirname, 'dist');

const katex = katexPlugin.default?.default ?? katexPlugin.default ?? katexPlugin;

const md = new MarkdownIt({ html: true, linkify: true, typographer: false });
md.use(katex, { throwOnError: false });

const siteTitle = 'InformationTheory 教科書（レビュー版）';

// --- chapters to build (順序 = 目次と前後ナビの順序) ---
// 章を足すときはこの配列に 1 行足すだけでよい。
const chapters = [
  {
    slug: 'ch02',
    num: '第2章',
    title: 'エントロピー・相互情報量・データ処理不等式',
    src: 'ch02-entropy.md',
    status: '仕上げ済（読者向けパイロット）',
  },
  {
    slug: 'ch03',
    num: '第3章',
    title: '漸近等分配性 (AEP)',
    src: 'ch03-aep.md',
    status: '草稿（末尾に未形式化項目・作業所見あり）',
  },
  {
    slug: 'ch04',
    num: '第4章',
    title: '確率過程のエントロピーレート',
    src: 'ch04-entropy-rate.md',
    status: '草稿（末尾に未形式化項目・作業所見あり）',
  },
  {
    slug: 'ch07',
    num: '第7章',
    title: '通信路容量',
    src: 'ch07-channel-capacity.md',
    status: '草稿（節番号が原典準拠で飛ぶ／末尾に所見あり）',
  },
  {
    slug: 'ch12',
    num: '第12章',
    title: '最大エントロピー',
    src: 'ch12-max-entropy.md',
    status: '草稿（末尾に未形式化項目・作業所見あり）',
  },
];

// CSS version pinned to match the KaTeX used for server-side rendering (0.16.47).
const cssCdn = `<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.47/dist/katex.min.css" crossorigin="anonymous">`;

const styles = `
:root { color-scheme: light dark; }
html { font-size: 18px; }
body {
  font-family: -apple-system, BlinkMacSystemFont, "Hiragino Sans", "Noto Sans JP", "Segoe UI", sans-serif;
  font-size: 1rem;
  line-height: 1.85; margin: 0; padding: 0;
  background: #fbfbfa; color: #1a1a1a;
}
.container { max-width: 760px; margin: 0 auto; padding: 2.2rem 1.1rem 6rem; }
h1 { font-size: 1.7rem; line-height: 1.4; border-bottom: 2px solid #ddd; padding-bottom: .5rem; }
h2 { font-size: 1.35rem; margin-top: 2.6rem; border-bottom: 1px solid #e3e3e3; padding-bottom: .3rem; }
h3 { font-size: 1.12rem; margin-top: 1.9rem; }
a { color: #0b67d0; }
blockquote { border-left: 3px solid #e3e3e3; margin: 1.1rem 0; padding: .15rem 0 .15rem 1rem; color: #8a8a8a; background: none; }
blockquote p { margin: .4rem 0; }
code { font-family: ui-monospace, "SF Mono", Menlo, monospace; font-size: .88em; background: rgba(0,0,0,.05); color: inherit; padding: .08em .3em; border-radius: 4px; }
pre { background: #f4f4f2; border-radius: 6px; margin: 1rem 0; }
pre code { display: block; padding: .8rem 1rem; overflow-x: auto; background: none; color: inherit; font-size: .85em; }
hr { border: none; border-top: 1px solid #e0e0e0; margin: 2.4rem 0; }
table { border-collapse: collapse; margin: 1rem 0; }
th, td { border: 1px solid #ddd; padding: .4rem .7rem; }
.katex-display { overflow-x: auto; overflow-y: hidden; padding: .2rem 0; }
.katex { font-size: 1.04em; }
.site-note { font-size: .82rem; color: #888; margin-top: 4rem; text-align: center; }

/* --- multi-page navigation --- */
.nav-top {
  font-size: .85rem; color: #888;
  padding-bottom: 1rem; margin-bottom: 1.6rem; border-bottom: 1px solid #e3e3e3;
}
.nav-top a { text-decoration: none; }
.nav-bottom {
  display: flex; justify-content: space-between; gap: 1rem; flex-wrap: wrap;
  font-size: .9rem;
  padding-top: 1.3rem; margin-top: 3.5rem; border-top: 1px solid #e3e3e3;
}
.nav-bottom a { text-decoration: none; }
.nav-bottom .spacer { flex: 1; }
.toc { list-style: none; padding: 0; margin: 2rem 0 0; }
.toc li {
  margin: .85rem 0; padding: .95rem 1.15rem;
  border: 1px solid #e3e3e3; border-radius: 8px; background: #fff;
}
.toc a { font-weight: 600; font-size: 1.05rem; text-decoration: none; }
.toc .status { display: block; font-size: .8rem; color: #8a8a8a; margin-top: .35rem; }

@media (prefers-color-scheme: dark) {
  body { background: #15171a; color: #e6e6e6; }
  a { color: #6cb6ff; }
  blockquote { border-left-color: #333a42; color: #9aa3ad; background: none; }
  code { background: rgba(255,255,255,.08); color: inherit; }
  pre { background: #1c1f24; }
  pre code { background: none; color: #d7dce2; }
  hr { border-color: #2a2e34; }
  th, td { border-color: #2a2e34; }
  .nav-top, .nav-bottom { border-color: #2a2e34; }
  .toc li { border-color: #2a2e34; background: #1a1d21; }
  .toc .status { color: #8b939c; }
}
`;

function escapeHtml(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

// 原稿には KaTeX の $ 記法 (ch02) と LaTeX 括弧デリミタ (ch03 以降) が混在する。
// markdown-it-katex は $ 記法しか解さないため、\\[ \\] / \\( \\) を $$ / $ に寄せてから渡す。
// コードブロック・インラインコードの中身は保護する (Lean コードを壊さないため)。
function normalizeMath(src) {
  const stashed = [];
  const stash = (s) => `\u0000${stashed.push(s) - 1}\u0000`;
  let out = src
    .replace(/```[\s\S]*?```/g, stash)
    .replace(/`[^`\n]*`/g, stash);
  out = out
    .replace(/\\\[([\s\S]*?)\\\]/g, (_, m) => `$$${m}$$`)
    .replace(/\\\(([\s\S]*?)\\\)/g, (_, m) => `$${m}$`);
  return out.replace(/\u0000(\d+)\u0000/g, (_, i) => stashed[Number(i)]);
}

function page({ title, bodyHtml }) {

  return `<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>${escapeHtml(title)}</title>
${cssCdn}
<style>${styles}</style>
</head>
<body>
<div class="container">
${bodyHtml}
<p class="site-note">InformationTheory — 形式化検証つき情報理論教科書（レビュー版）。数式は KaTeX で事前レンダリング。</p>
</div>
</body>
</html>`;
}

function chapterNav(i) {
  const prev = chapters[i - 1];
  const next = chapters[i + 1];
  const left = prev
    ? `<a href="./${prev.slug}.html">← ${escapeHtml(prev.num)} ${escapeHtml(prev.title)}</a>`
    : '<span class="spacer"></span>';
  const right = next
    ? `<a href="./${next.slug}.html">${escapeHtml(next.num)} ${escapeHtml(next.title)} →</a>`
    : '<span class="spacer"></span>';
  return `<nav class="nav-bottom">${left}${right}</nav>`;
}

mkdirSync(distDir, { recursive: true });

// --- chapter pages ---
chapters.forEach((c, i) => {
  const markdown = readFileSync(resolve(root, c.src), 'utf8');
  const navTop = `<nav class="nav-top"><a href="./index.html">${escapeHtml(siteTitle)}</a> ／ ${escapeHtml(c.num)}</nav>`;
  const bodyHtml = navTop + md.render(normalizeMath(markdown)) + chapterNav(i);
  const html = page({ title: `${c.num} ${c.title}`, bodyHtml });
  const outPath = resolve(distDir, `${c.slug}.html`);
  writeFileSync(outPath, html, 'utf8');
  console.log(`built ${c.src} -> dist/${c.slug}.html (${html.length} bytes)`);
});

// --- index (table of contents) ---
const tocItems = chapters
  .map(
    (c) => `  <li>
    <a href="./${c.slug}.html">${escapeHtml(c.num)}　${escapeHtml(c.title)}</a>
    <span class="status">${escapeHtml(c.status)}</span>
  </li>`,
  )
  .join('\n');

const indexBody = `<h1>${escapeHtml(siteTitle)}</h1>
<p>Lean 4 + Mathlib で形式化検証した定理に紐づけて書いている情報理論の教科書原稿です。
掲載順は原典の章番号に従っており、番号は連続していません。各章の末尾には、
その章で未形式化のまま残している項目と執筆時の所見を載せています（レビュー用にそのまま公開）。</p>
<ul class="toc">
${tocItems}
</ul>`;

writeFileSync(resolve(distDir, 'index.html'), page({ title: siteTitle, bodyHtml: indexBody }), 'utf8');
console.log(`built index -> dist/index.html (${chapters.length} chapters)`);

console.log('done');
