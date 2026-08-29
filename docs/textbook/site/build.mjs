import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import MarkdownIt from 'npm:markdown-it@14';
import * as katexPlugin from 'npm:@vscode/markdown-it-katex@1';
import mdContainer from 'npm:markdown-it-container@4';

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
      { slug: 'ch01-04', num: '1.4', title: '条件付き相互情報量', src: 'ch01/04-conditional-mutual-information.md' },
      { slug: 'ch01-05', num: '1.5', title: 'エントロピー・相互情報量のチェイン則', src: 'ch01/05-chain-rules.md' },
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

/* --- 定理環境 ---
   原稿 (.claude/rules/textbook-writing.md §5 の決まり文句) は Markdown のままで、
   ブロック化は build 側の decorateStatements() が行う。色は種別の区別だけを担い、
   背景は敷かない (紙の数学書に近い見え方を保つ)。 */
.stmt {
  --stmt-accent: #8a8a8a;
  border-left: 2px solid var(--stmt-accent);
  padding: .05rem 0 .05rem 1.05rem;
  margin: 1.7rem 0;
}
.stmt > :first-child { margin-top: 0; }
.stmt > :last-child { margin-bottom: 0; }
.stmt > p:first-child > strong:first-child { color: var(--stmt-accent); font-weight: 700; }
.stmt-theorem, .stmt-proposition, .stmt-corollary { --stmt-accent: #2f5fa8; }
.stmt-definition { --stmt-accent: #2c7a5a; }
.stmt-lemma { --stmt-accent: #8a8a8a; }
.stmt-example { --stmt-accent: #96702a; }

.proof { margin: 1.3rem 0 1.8rem; padding-left: 1.05rem; color: #2f2f2f; }
.proof::after { content: ""; display: block; clear: both; }
.proof > :first-child { margin-top: 0; }
.proof > p:first-child > em:first-child {
  font-style: normal; font-weight: 600; letter-spacing: .05em; color: #7a7a7a;
}
.qed { float: right; color: #7a7a7a; }
.env-head { margin-bottom: .55rem; }
.qed-line { text-align: right; margin-top: -.6rem; }
.qed-line .qed { float: none; }

/* 形式化ポインタ。主張ブロック (縦罫) とは別の体裁にして取り違えを防ぐ。 */
.formalized {
  font-size: .93rem;
  margin: 1.4rem 0;
  padding: .55rem .95rem;
  background: rgba(42,122,134,.07);
  border-radius: 6px;
  color: #3a3a3a;
}
.formalized > :first-child { margin-top: 0; }
.formalized > :last-child { margin-bottom: 0; }
.formalized strong:first-child { color: #22707c; font-weight: 700; }

/* 読み飛ばしてよい傍注 (形式化上の注記 / 記法の先取り)。 */
.aside {
  font-size: .93rem;
  border-left: 3px solid #e3e3e3;
  margin: 1.4rem 0;
  padding: .1rem 0 .1rem 1rem;
  color: #8a8a8a;
}
.aside > :first-child { margin-top: 0; }
.aside > :last-child { margin-bottom: 0; }
.aside strong:first-child { color: #6f6f6f; }

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
  .stmt-theorem, .stmt-proposition, .stmt-corollary { --stmt-accent: #7ba7e8; }
  .stmt-definition { --stmt-accent: #63b894; }
  .stmt-lemma { --stmt-accent: #9aa3ad; }
  .stmt-example { --stmt-accent: #c9a45e; }
  .proof { color: #c9cdd3; }
  .proof > p:first-child > em:first-child { color: #98a1aa; }
  .qed { color: #98a1aa; }
  .formalized { background: rgba(122,200,212,.09); color: #c9cdd3; }
  .formalized strong:first-child { color: #63b5c2; }
  .aside { border-left-color: #333a42; color: #9aa3ad; }
  .aside strong:first-child { color: #aeb6bf; }
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

// --- 定理環境コンテナ ---
// 原稿は種別・番号・名前だけを宣言し (`::: theorem 1.6.1 情報不等式 / Gibbs`)、
// 「定理 1.6.1（情報不等式 / Gibbs）.」という見出しと証明末尾の ■ はここで組む。
// 記法の SoT は .claude/rules/textbook-writing.md §5。
const ENVS = new Map([
  ['theorem',            { label: '定理',           cls: 'stmt stmt-theorem',       numbered: true }],
  ['proposition',        { label: '命題',           cls: 'stmt stmt-proposition',   numbered: true }],
  ['lemma',              { label: '補題',           cls: 'stmt stmt-lemma',         numbered: true }],
  ['corollary',          { label: '系',             cls: 'stmt stmt-corollary',     numbered: true }],
  ['definition',         { label: '定義',           cls: 'stmt stmt-definition',    numbered: true }],
  ['example',            { label: '例',             cls: 'stmt stmt-example',       numbered: true }],
  ['proof',              { label: '証明',           cls: 'proof' }],
  ['formalized',         { label: '形式化',         cls: 'formalized', sep: ':' }],
  ['formalization-note', { label: '形式化上の注記', cls: 'aside aside-formalization' }],
  ['notation-preview',   { label: '記法の先取り',   cls: 'aside aside-notation' }],
]);

// `theorem 1.6.1 情報不等式 / Gibbs` を {kind, num, name} に割る。
function parseEnv(info) {
  const m = info.trim().match(/^([a-z-]+)\s*(.*)$/s);
  if (!m || !ENVS.has(m[1])) return null;
  const env = ENVS.get(m[1]);
  let rest = m[2].trim();
  let num = '';
  if (env.numbered) {
    const n = rest.match(/^(\d[\d.]*?)\.?(?:\s+|$)/);
    if (n) { num = n[1]; rest = rest.slice(n[0].length).trim(); }
  }
  return { kind: m[1], env, num, name: rest };
}

// 見出しを Markdown 断片として返す（名前に $…$ を書けるよう、生 HTML にはしない）。
function headingMarkdown({ env, num, name }) {
  const paren = name ? `（${name}）` : '';
  if (env.sep) return `**${env.label}**${env.sep}`;
  return `**${env.label}${num ? ' ' + num : ''}${paren}.**`;
}

md.use(mdContainer, 'env', {
  validate: (params) => parseEnv(params) !== null,
  render(tokens, idx) {
    const t = tokens[idx];
    if (t.nesting === 1) {
      const { env } = parseEnv(t.info);
      return `<div class="${env.cls}">\n`;
    }
    return '</div>\n';
  },
});

// 見出しの流し込みと ■ の付与は inline 解析の前に済ませる（見出し中の数式を活かすため）。
md.core.ruler.after('block', 'env_heading', (state) => {
  const toks = state.tokens;
  let lastStmt = null;

  const injectParagraph = (at, content, cls) => {
    const open = new state.Token('paragraph_open', 'p', 1);
    if (cls) open.attrSet('class', cls);
    const inline = new state.Token('inline', '', 0);
    inline.content = content;
    inline.children = [];
    const close = new state.Token('paragraph_close', 'p', -1);
    toks.splice(at, 0, open, inline, close);
  };

  for (let i = 0; i < toks.length; i++) {
    const t = toks[i];
    if (t.type !== 'container_env_open') continue;
    const spec = parseEnv(t.info);
    if (spec.env.cls.startsWith('stmt')) lastStmt = spec.kind;

    // 1. 見出し。最初の段落があればその頭に流し込み、無ければ独立した段落にする。
    const head = headingMarkdown(spec);
    if (toks[i + 1]?.type === 'paragraph_open' && toks[i + 2]?.type === 'inline') {
      const inline = toks[i + 2];
      inline.content = spec.env.sep ? `${head} ${inline.content}` : `${head} ${inline.content}`;
    } else {
      injectParagraph(i + 1, head, 'env-head');
    }

    if (spec.kind !== 'proof') continue;
    // 終端記号は inline 解析のあとで付ける（下の env_qed）。
    // 補題の証明は □、それ以外は ■（textbook-writing.md §5）。
    t.meta = { qed: lastStmt === 'lemma' ? '\\square' : '\\blacksquare' };
  }
});

// 証明末尾の ■ / □。KaTeX プラグインは HTML タグ直後の $…$ を数式と見なさないので、
// 文字列を流し込むのではなくトークンとして組み立てる。
md.core.ruler.after('inline', 'env_qed', (state) => {
  const toks = state.tokens;
  const mk = (type, content, tag = '') => {
    const tok = new state.Token(type, tag, 0);
    tok.content = content;
    return tok;
  };

  for (let i = 0; i < toks.length; i++) {
    const t = toks[i];
    if (t.type !== 'container_env_open' || !t.meta?.qed) continue;

    let close = i + 1;
    while (close < toks.length && toks[close].type !== 'container_env_close') close++;
    if (close >= toks.length) continue;

    const marks = [
      mk('html_inline', '<span class="qed">'),
      mk('math_inline', t.meta.qed, 'math'),
      mk('html_inline', '</span>'),
    ];
    if (toks[close - 1].type === 'paragraph_close' && toks[close - 2]?.type === 'inline') {
      toks[close - 2].children.push(...marks);
    } else {
      // 証明がディスプレイ数式で終わる場合は、記号だけの行を足す。
      const open = new state.Token('paragraph_open', 'p', 1);
      open.attrSet('class', 'qed-line');
      const inline = new state.Token('inline', '', 0);
      inline.content = '';
      inline.children = marks;
      toks.splice(close, 0, open, inline, new state.Token('paragraph_close', 'p', -1));
    }
  }
});

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
