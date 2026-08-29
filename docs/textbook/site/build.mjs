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
// 章を足すときはこの配列に 1 要素足すだけでよい。
// `sections` を持つ章は「章トビラ + 節ごとのページ」に分割して出力し、
// 持たない章は 1 章 1 ページで出力する。
const chapters = [
  {
    slug: 'ch01',
    num: '第1章',
    title: 'エントロピー・相互情報量・データ処理不等式',
    status: '仕上げ済（読者向けパイロット）',
    intro: 'ch01/00-intro.md',
    sections: [
      { slug: 'ch01-01', num: '1.1', title: 'エントロピー', src: 'ch01/01-entropy.md' },
      { slug: 'ch01-02', num: '1.2', title: '結合エントロピー・条件付きエントロピーとチェイン則', src: 'ch01/02-joint-conditional-entropy.md' },
      { slug: 'ch01-03', num: '1.3', title: '相互情報量', src: 'ch01/03-mutual-information.md' },
      { slug: 'ch01-04', num: '1.4', title: 'エントロピー・相互情報量のチェイン則', src: 'ch01/04-chain-rules.md' },
      { slug: 'ch01-05', num: '1.5', title: '条件付き相互情報量', src: 'ch01/05-conditional-mutual-information.md' },
      { slug: 'ch01-06', num: '1.6', title: '情報不等式（ジェンセンと相対エントロピー）', src: 'ch01/06-information-inequality.md' },
      { slug: 'ch01-07', num: '1.7', title: '対数和不等式', src: 'ch01/07-log-sum-inequality.md' },
      { slug: 'ch01-08', num: '1.8', title: 'データ処理不等式', src: 'ch01/08-data-processing-inequality.md' },
      { slug: 'ch01-09', num: '1.9', title: '充足統計量', src: 'ch01/09-sufficient-statistics.md' },
      { slug: 'ch01-10', num: '1.10', title: 'ファノの不等式', src: 'ch01/10-fano.md' },
      { slug: 'ch01-notes', title: 'この章で扱わなかったこと（正直な注記）', src: 'ch01/99-notes.md' },
    ],
  },
  {
    slug: 'ch02',
    num: '第2章',
    title: '漸近等分配性 (AEP)',
    src: 'ch02-aep.md',
    status: '草稿（末尾に未形式化項目・作業所見あり）',
  },
  {
    slug: 'ch03',
    num: '第3章',
    title: '確率過程のエントロピーレート',
    src: 'ch03-entropy-rate.md',
    status: '草稿（末尾に未形式化項目・作業所見あり）',
  },
  {
    slug: 'ch04',
    num: '第4章',
    title: '通信路容量',
    src: 'ch04-channel-capacity.md',
    status: '草稿（末尾に未形式化項目・作業所見あり）',
  },
  {
    slug: 'ch05',
    num: '第5章',
    title: '最大エントロピー',
    src: 'ch05-max-entropy.md',
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
/* 宣言名 / ファイルパスの長い識別子が狭い画面で横にはみ出すため、行内 code は折り返す。
   コードブロック (pre code) は Lean コードの整形を保つので折り返さず横スクロールさせる。 */
code { font-family: ui-monospace, "SF Mono", Menlo, monospace; font-size: .88em; background: rgba(0,0,0,.05); color: inherit; padding: .08em .3em; border-radius: 4px; overflow-wrap: anywhere; }
pre { background: #f4f4f2; border-radius: 6px; margin: 1rem 0; }
pre code { display: block; padding: .8rem 1rem; overflow-x: auto; background: none; color: inherit; font-size: .85em; overflow-wrap: normal; }
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
.subtoc { list-style: none; padding: 0; margin: .8rem 0 0; border-top: 1px solid #ececec; }
.subtoc li { margin: 0; padding: .3rem 0 0; }
.subtoc a { font-weight: 400; font-size: .92rem; }

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
  .subtoc { border-top-color: #2a2e34; }
}
`;

function escapeHtml(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

// 原稿には KaTeX の $ 記法 (第1章) と LaTeX 括弧デリミタ (第2章以降) が混在する。
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

// --- 全ページを掲載順に並べた線形リスト（前後ナビはこの順序に従う） ---
// 節分割された章は「章トビラ → 各節」の順に展開する。
const pages = [];
for (const c of chapters) {
  if (c.sections) {
    pages.push({ chapter: c, src: c.intro, slug: c.slug, label: `${c.num} ${c.title}`, isChapterTop: true });
    for (const sec of c.sections) {
      const label = sec.num ? `${sec.num} ${sec.title}` : sec.title;
      pages.push({ chapter: c, section: sec, src: sec.src, slug: sec.slug, label });
    }
  } else {
    pages.push({ chapter: c, src: c.src, slug: c.slug, label: `${c.num} ${c.title}`, isChapterTop: true });
  }
}

function navTop(pg) {
  const crumbs = [`<a href="./index.html">${escapeHtml(siteTitle)}</a>`];
  if (pg.section) {
    crumbs.push(`<a href="./${pg.chapter.slug}.html">${escapeHtml(pg.chapter.num)}</a>`);
    crumbs.push(escapeHtml(pg.section.num ?? pg.section.title));
  } else {
    crumbs.push(escapeHtml(pg.chapter.num));
  }
  return `<nav class="nav-top">${crumbs.join(' ／ ')}</nav>`;
}

function navBottom(i) {
  const prev = pages[i - 1];
  const next = pages[i + 1];
  const left = prev
    ? `<a href="./${prev.slug}.html">← ${escapeHtml(prev.label)}</a>`
    : '<span class="spacer"></span>';
  const right = next
    ? `<a href="./${next.slug}.html">${escapeHtml(next.label)} →</a>`
    : '<span class="spacer"></span>';
  return `<nav class="nav-bottom">${left}${right}</nav>`;
}

// 章トビラに載せる、その章の節一覧。
function sectionToc(c) {
  const items = c.sections
    .map((sec) => {
      const label = sec.num ? `${sec.num}　${sec.title}` : sec.title;
      return `  <li><a href="./${sec.slug}.html">${escapeHtml(label)}</a></li>`;
    })
    .join('\n');
  return `<ul class="toc">\n${items}\n</ul>`;
}

mkdirSync(distDir, { recursive: true });

// --- content pages ---
pages.forEach((pg, i) => {
  const markdown = readFileSync(resolve(root, pg.src), 'utf8');
  let bodyHtml = navTop(pg) + md.render(normalizeMath(markdown));
  if (pg.isChapterTop && pg.chapter.sections) bodyHtml += sectionToc(pg.chapter);
  bodyHtml += navBottom(i);
  const title = pg.section ? `${pg.label} — ${pg.chapter.num}` : pg.label;
  const outPath = resolve(distDir, `${pg.slug}.html`);
  const html = page({ title, bodyHtml });
  writeFileSync(outPath, html, 'utf8');
  console.log(`built ${pg.src} -> dist/${pg.slug}.html (${html.length} bytes)`);
});

// --- index (table of contents) ---
const tocItems = chapters
  .map((c) => {
    const sub = c.sections
      ? `\n    <ol class="subtoc">\n${c.sections
          .map((sec) => {
            const label = sec.num ? `${sec.num}　${sec.title}` : sec.title;
            return `      <li><a href="./${sec.slug}.html">${escapeHtml(label)}</a></li>`;
          })
          .join('\n')}\n    </ol>`
      : '';
    return `  <li>
    <a href="./${c.slug}.html">${escapeHtml(c.num)}　${escapeHtml(c.title)}</a>
    <span class="status">${escapeHtml(c.status)}</span>${sub}
  </li>`;
  })
  .join('\n');

const indexBody = `<h1>${escapeHtml(siteTitle)}</h1>
<p>Lean 4 + Mathlib で形式化検証した定理に紐づけて書いている情報理論の教科書原稿です。
各章の末尾には、その章で未形式化のまま残している項目と執筆時の所見を載せています
（レビュー用にそのまま公開）。</p>
<ul class="toc">
${tocItems}
</ul>`;

writeFileSync(resolve(distDir, 'index.html'), page({ title: siteTitle, bodyHtml: indexBody }), 'utf8');
console.log(`built index -> dist/index.html (${pages.length} pages)`);

console.log('done');
