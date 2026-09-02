import { readFileSync, writeFileSync, mkdirSync, rmSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import MarkdownIt from 'npm:markdown-it@14';
import * as katexPlugin from 'npm:@vscode/markdown-it-katex@1';
import mdContainer from 'npm:markdown-it-container@4';
import { TERMS } from './terminology.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const root = resolve(__dirname, '..'); // docs/textbook
const distDir = resolve(__dirname, 'dist');

const katex = katexPlugin.default?.default ?? katexPlugin.default ?? katexPlugin;

const md = new MarkdownIt({ html: true, linkify: true, typographer: false });
md.use(katex, { throwOnError: false });

const siteTitle = 'InformationTheory 教科書（レビュー版）';

// --- chapters to build (順序 = 目次と前後ナビの順序) ---
// 章を足すときはこの配列に 1 要素足すだけでよい。
// `sections` を持つ章は節ごとのページに分割して出力し（`intro` を足した章だけ、その手前に
// 章トビラが 1 枚増える）、持たない章は 1 章 1 ページで出力する。
const chapters = [
  {
    slug: 'ch01',
    num: '第1章',
    title: 'エントロピー・相互情報量・データ処理不等式',
    status: '仕上げ済（読者向けパイロット）',
    sections: [
      { slug: 'ch01-01', num: '1.1', title: 'エントロピー', src: 'ch01/01-entropy.md' },
      { slug: 'ch01-02', num: '1.2', title: '結合エントロピー・条件付きエントロピーとチェイン則', src: 'ch01/02-joint-conditional-entropy.md' },
      { slug: 'ch01-03', num: '1.3', title: '相互情報量', src: 'ch01/03-mutual-information.md' },
      { slug: 'ch01-04', num: '1.4', title: '条件付き相互情報量', src: 'ch01/04-conditional-mutual-information.md' },
      { slug: 'ch01-05', num: '1.5', title: 'エントロピー・相互情報量のチェイン則', src: 'ch01/05-chain-rules.md' },
      { slug: 'ch01-06', num: '1.6', title: '情報不等式（Jensen と相対エントロピー）', src: 'ch01/06-information-inequality.md' },
      { slug: 'ch01-07', num: '1.7', title: '対数和不等式', src: 'ch01/07-log-sum-inequality.md' },
      { slug: 'ch01-08', num: '1.8', title: 'データ処理不等式', src: 'ch01/08-data-processing-inequality.md' },
      { slug: 'ch01-09', num: '1.9', title: '十分統計量', src: 'ch01/09-sufficient-statistics.md' },
      { slug: 'ch01-10', num: '1.10', title: 'ファノの不等式', src: 'ch01/10-fano.md' },
    ],
  },
  {
    slug: 'ch02',
    num: '第2章',
    title: '漸近等分配性とデータ圧縮',
    status: '仕上げ済',
    sections: [
      { slug: 'ch02-01', num: '2.1', title: '漸近等分配性', src: 'ch02/01-aep.md' },
      { slug: 'ch02-02', num: '2.2', title: '典型集合', src: 'ch02/02-typical-set.md' },
      { slug: 'ch02-03', num: '2.3', title: '情報源符号化定理', src: 'ch02/03-source-coding.md' },
      { slug: 'ch02-04', num: '2.4', title: '強典型性', src: 'ch02/04-strong-typicality.md' },
    ],
  },
  {
    slug: 'ch03',
    num: '第3章',
    title: '定常情報源のエントロピーレート',
    status: '仕上げ済',
    sections: [
      { slug: 'ch03-01', num: '3.1', title: '定常情報源', src: 'ch03/01-stationary.md' },
      { slug: 'ch03-02', num: '3.2', title: 'エントロピーレート', src: 'ch03/02-entropy-rate.md' },
      { slug: 'ch03-03', num: '3.3', title: 'マルコフ情報源のエントロピーレート', src: 'ch03/03-markov-rate.md' },
      { slug: 'ch03-04', num: '3.4', title: 'エルゴード性と時間平均', src: 'ch03/04-birkhoff.md' },
      { slug: 'ch03-05', num: '3.5', title: 'Shannon–McMillan–Breiman 定理', src: 'ch03/05-smb.md' },
    ],
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

// --- 相互参照レジストリ ---
// 原稿は参照を番号だけで書く（.claude/rules/textbook-writing.md §8）。番号 → 掲載位置の
// 対応表をビルドの前段で全ページから集め、本文中の「定理 1.2.3」「1.6 節」「第2章」を
// リンクに変える。番号は章.節.通番で本全体を通じて一意なので、対応表は番号で引ける。
const stmtRefs = new Map(); // '1.2.3'  -> { slug, id, label, name }
const secRefs = new Map();  // '1.6'    -> { slug, id, title }
const chapRefs = new Map(); // '2'      -> { slug, title }

let unresolvedRefs = 0;
let duplicateNums = 0;

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
  margin: 1.9rem 0;
}
.stmt > :first-child { margin-top: 0; }
.stmt > :last-child { margin-bottom: 0; }
.stmt > p:first-child > strong:first-child { color: var(--stmt-accent); font-weight: 700; }
.stmt-theorem, .stmt-proposition, .stmt-corollary { --stmt-accent: #2f5fa8; }
.stmt-definition { --stmt-accent: #2c7a5a; }
.stmt-lemma { --stmt-accent: #8a8a8a; }
.stmt-example { --stmt-accent: #96702a; }

.proof { margin: 1.5rem 0 2rem; color: #2f2f2f; }
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

/* --- 相互参照リンク ---
   本文の「定理 1.2.3」「1.6 節」はビルドがリンクに変える。数式と地の文のあいだに置かれる
   ので、リンク色で塗ると本文が騒がしくなる。文字色は地の文のまま、下線の色だけで
   クリックできることを示し、ホバーでリンク色に寄せる。 */
a.xref { color: inherit; text-decoration: none; border-bottom: 1px solid rgba(11,103,208,.42); }
a.xref:hover, a.xref:focus { color: #0b67d0; border-bottom-color: #0b67d0; }

/* 形式化ポインタの行内 code は掲載先へのリンクになる（宣言名は API ドキュメントの項目、
   パスは GitHub のソース）。相互参照と同じで、色ではなく下線でクリックできることを示す。 */
a.srcref { color: inherit; text-decoration: none; border-bottom: 1px solid rgba(34,112,124,.45); }
a.srcref:hover, a.srcref:focus { color: #22707c; border-bottom-color: #22707c; }
a.srcref code { background: rgba(34,112,124,.09); }
.ptr-icon {
  width: .82em; height: .82em; margin-right: .26em; vertical-align: -.09em;
  fill: currentColor; opacity: .62;
}
a.srcref:hover .ptr-icon, a.srcref:focus .ptr-icon { opacity: 1; }

/* 飛んだ先が画面の最上端に貼り付くと、どこに着地したのか読み取れない。余白を空け、
   着地点に薄く色を敷いて示す（box-shadow の spread なので行送りは動かない）。 */
[id] { scroll-margin-top: 1.6rem; }
.stmt:target, .proof:target, .formalized:target, .aside:target,
h1:target, h2:target, h3:target {
  background: rgba(11,103,208,.075);
  box-shadow: 0 0 0 .5rem rgba(11,103,208,.075);
  border-radius: 2px;
}

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
  a.xref { border-bottom-color: rgba(108,182,255,.45); }
  a.xref:hover, a.xref:focus { color: #6cb6ff; border-bottom-color: #6cb6ff; }
  a.srcref { border-bottom-color: rgba(99,181,194,.5); }
  a.srcref:hover, a.srcref:focus { color: #63b5c2; border-bottom-color: #63b5c2; }
  a.srcref code { background: rgba(99,181,194,.14); }
  .stmt:target, .proof:target, .formalized:target, .aside:target,
  h1:target, h2:target, h3:target {
    background: rgba(108,182,255,.1);
    box-shadow: 0 0 0 .5rem rgba(108,182,255,.1);
  }
}
`;

function escapeHtml(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

// --- 和文の soft line break ---
// 原稿は表示幅で改行してある (textbook-writing.md §9) が、CommonMark の soft break は
// HTML では空白になり、和文の語間に不要な空きが出る (「議論を 支える」)。前後どちらかが
// 和文なら空白を落とし、欧文どうしの折り返しでだけ従来どおり空白を残す。
const CJK = /[　-〿぀-ヿ㐀-䶿一-鿿豈-﫿＀-￯]/;

// 改行の隣に立つ文字。タグや content を持たないトークン (link_open など) は読み飛ばす。
function neighborChar(tokens, idx, dir) {
  for (let i = idx + dir; i >= 0 && i < tokens.length; i += dir) {
    const t = tokens[i];
    if (t.type === 'softbreak' || t.type === 'hardbreak') return '';
    if (t.type === 'html_inline' || !t.content) continue;
    return dir < 0 ? t.content.at(-1) : t.content[0];
  }
  return '';
}

md.renderer.rules.softbreak = (tokens, idx) => {
  const glue = CJK.test(neighborChar(tokens, idx, -1)) || CJK.test(neighborChar(tokens, idx, 1));
  // コメントを挟めば、出力 HTML は原稿どおりに折れたまま表示上の空白だけが消える。
  return glue ? '<!--\n-->' : '\n';
};

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

// 番号つき主張の URL 断片。種別を含めるので、リンク先が何かは URL だけで分かる。
const ANCHOR = new Map([
  ['theorem', 'thm'], ['proposition', 'prop'], ['lemma', 'lem'],
  ['corollary', 'cor'], ['definition', 'def'], ['example', 'ex'],
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
// `::: proof 定理 1.1.5` の名乗りは、補題を挟んで主張から離れた位置に置かれる決まりなので
// （textbook-writing.md §4）、見出しの中の番号もリンクにして主張へ戻れるようにする。
function headingMarkdown({ env, num, name }, ctx) {
  const shown = ctx ? linkStatementRefs(name, ctx) : name;
  const paren = shown ? `（${shown}）` : '';
  if (env.sep) return `**${env.label}**${env.sep}`;
  return `**${env.label}${num ? ' ' + num : ''}${paren}.**`;
}

md.use(mdContainer, 'env', {
  validate: (params) => parseEnv(params) !== null,
  render(tokens, idx) {
    const t = tokens[idx];
    if (t.nesting === 1) {
      const { kind, env, num } = parseEnv(t.info);
      const id = num ? ` id="${ANCHOR.get(kind)}-${num}"` : '';
      return `<div class="${env.cls}"${id}>\n`;
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
    const head = headingMarkdown(spec, state.env?.ctx);
    if (toks[i + 1]?.type === 'paragraph_open' && toks[i + 2]?.type === 'inline') {
      const inline = toks[i + 2];
      inline.content = spec.env.sep ? `${head} ${inline.content}` : `${head} ${inline.content}`;
    } else {
      injectParagraph(i + 1, head, 'env-head');
    }

    if (spec.kind !== 'proof') continue;
    // 終端記号は inline 解析のあとで付ける（下の env_qed）。
    // 補題の証明は □、それ以外は ■（textbook-writing.md §5）。証明がどの主張のものかを
    // 名乗っているとき（`::: proof 定理 1.1.5`）は、直前の主張ではなくその名前で決める。
    const named = spec.name.match(/^(定理|命題|補題|系)/);
    const provesLemma = named ? named[1] === '補題' : lastStmt === 'lemma';
    t.meta = { qed: provesLemma ? '\\square' : '\\blacksquare' };
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

// 節見出し (`# 1.6 …` / `## 4.2 …`) に id を振る。第1章は 1 節 1 ページ、第2〜5章は
// 1 章 1 ページなので、節への参照はページ移動になったり同一ページ内の移動になったりする。
// どちらでも同じ id で引けるよう、見出し側の付け方は章の形に依らせない。
md.core.ruler.push('section_anchor', (state) => {
  const toks = state.tokens;
  for (let i = 0; i < toks.length; i++) {
    if (toks[i].type !== 'heading_open') continue;
    const num = toks[i + 1]?.content?.match(/^(\d+\.\d+)\s/);
    if (num) toks[i].attrSet('id', `sec-${num[1]}`);
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

// 章の入口になるページ。章トビラを持たない章（第1章）は最初の節が入口で、章そのものの
// ページは無い。目次・パンくず・「第N章」の参照は、いずれもここを見る。
const chapterHome = (c) => (c.sections && !c.intro ? c.sections[0].slug : c.slug);
const hasChapterPage = (c) => !c.sections || Boolean(c.intro);

// --- 全ページを掲載順に並べた線形リスト（前後ナビはこの順序に従う） ---
// 節分割された章は「（章トビラ →）各節」の順に展開する。
const pages = [];
for (const c of chapters) {
  if (c.sections) {
    if (c.intro) {
      pages.push({ chapter: c, src: c.intro, slug: c.slug, label: `${c.num} ${c.title}`, isChapterTop: true });
    }
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
    crumbs.push(hasChapterPage(pg.chapter)
      ? `<a href="./${pg.chapter.slug}.html">${escapeHtml(pg.chapter.num)}</a>`
      : escapeHtml(pg.chapter.num));
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

// --- 主張と証明の対応チェック ---
// 証明の付いていない主張を列挙する（.claude/rules/textbook-writing.md §4）。読者は証明の
// ない主張を「意図して証明を略した主張」と読むので、地の文に根拠を書いて proof 環境を
// 省いた箇所はここで拾う。主張と証明のあいだに形式化ポインタ・傍注が挟まるのは許す。
const CLAIM_KINDS = new Set(['theorem', 'proposition', 'lemma', 'corollary']);
const BETWEEN_KINDS = new Set(['formalized', 'formalization-note', 'notation-preview']);

function lintProofs(markdown, src) {
  const blocks = [];
  markdown.split('\n').forEach((line, i) => {
    const m = line.match(/^::: +(\S+)(.*)$/);
    if (m && ENVS.has(m[1])) blocks.push({ line: i + 1, kind: m[1], info: (m[1] + m[2]).trim() });
  });

  // `::: proof 定理 1.1.5` のように、どの主張の証明かを名乗るもの（補題を挟むので
  // 主張の直後に置けない場合）は、離れた位置にあっても証明ありと数える。
  const provedByName = new Set();
  for (const b of blocks) {
    if (b.kind !== 'proof') continue;
    const m = parseEnv(b.info).name.match(/^(定理|命題|補題|系)\s*([\d.]+)/);
    if (m) provedByName.add(`${m[1]} ${m[2]}`);
  }

  let missing = 0;
  blocks.forEach((b, i) => {
    if (!CLAIM_KINDS.has(b.kind)) return;
    const { env, num, name } = parseEnv(b.info);
    if (provedByName.has(`${env.label} ${num}`)) return;
    let j = i + 1;
    while (j < blocks.length && BETWEEN_KINDS.has(blocks[j].kind)) j++;
    if (blocks[j]?.kind === 'proof') return;
    missing += 1;
    const title = `${env.label}${num ? ' ' + num : ''}${name ? `（${name}）` : ''}`;
    console.warn(`warn: 証明のない主張 ${src}:${b.line} ${title}`);
  });
  return missing;
}

// 行内 code と数式の中は検査しない（Lean の識別子・パス・LaTeX が語に当たるため）。
// 行番号を保つため、伏せる範囲は改行以外を空白に置き換える。
function stripCodeAndMath(s) {
  const blank = (m) => m.replace(/[^\n]/g, ' ');
  return s
    .replace(/```[\s\S]*?```/g, blank)
    .replace(/\$\$[\s\S]*?\$\$/g, blank)
    .replace(/`[^`\n]*`/g, blank)
    .replace(/\$[^$\n]*\$/g, blank);
}

function lintTerminology(markdown, src) {
  const lines = stripCodeAndMath(markdown).split('\n');
  let found = 0;
  for (const t of TERMS) {
    if (t.except?.some((p) => src.includes(p))) continue;
    // 採用語が禁止語を丸ごと含むことがある（縮約形を禁じるとき——「情報源符号」に対する
    // 「源符号」）。素朴に部分文字列を探すと、正しく書いた側が禁止語に当たってしまうので、
    // 先に採用語を伏せてから探す。
    const masked = lines.map((line) => line.split(t.use).join(' '.repeat(t.use.length)));
    for (const bad of t.avoid) {
      masked.forEach((line, i) => {
        if (!line.includes(bad)) return;
        found += 1;
        console.warn(`warn: 表記ゆれ ${src}:${i + 1} 「${bad}」は使わない（採用: 「${t.use}」）`);
      });
    }
  }
  return found;
}

// --- 参照の自動リンク ---
// 原稿は参照を番号だけで書く（textbook-writing.md §8）。ここで番号 → 掲載位置の対応表を
// 全ページから集め、本文の「定理 1.2.3」「1.6 節」「第2章」をリンクに変える。番号は本
// 全体で一意なので、参照する側は掲載ページを知らなくてよい（節を別ファイルへ移しても、
// 章を 1 ページに畳んでも、原稿には手を入れずに済む）。
// 解決できない番号・種別の食い違い・番号の重複は warn として出す。§8 の「番号を振り直す
// ときに参照元を rg で洗う」手順は、この検査が肩代わりする。

// 参照と番号のあいだは、空白でも改行でも割れる。原稿は表示幅で折り返すので（§9）、
// 「有限 Jensen——補題 / 1.1.6 を」のように参照が 2 行にまたがることがある。読者に改行位置は
// 見えないのだから、そこでリンクが切れる理由はない。区切りに改行を含めて拾う。
const GAP = '[ 　\n]*';
const KIND = '(定理|命題|補題|系|定義|例)';
const REF_RE = new RegExp(
  `${KIND}${GAP}(\\d+\\.\\d+\\.\\d+)|(\\d+\\.\\d+)${GAP}節|第${GAP}(\\d+)${GAP}章`, 'g');
const STMT_RE = new RegExp(`${KIND}${GAP}(\\d+\\.\\d+\\.\\d+)`, 'g');
// 種別を伴わない裸の番号。数値と字面が同じなので機械では参照と区別できない（本文には
// 「約 2.58 ビット」のような数値が出る）。3 成分に限り、かつ実在する番号のときだけ、
// 「種別を書け」と促す（リンクにはしない。種別のない参照は §8 が禁じている）。
const BARE_RE = /(?<![\d.])(\d+\.\d+\.\d+)(?![\d.])/g;

function escapeAttr(s) {
  return escapeHtml(s).replace(/"/g, '&quot;');
}

function register(map, key, value, src, line) {
  if (map.has(key)) {
    duplicateNums += 1;
    console.warn(`warn: 番号の重複 ${src}:${line} 「${key}」は既出`);
    return;
  }
  map.set(key, value);
}

// ページ 1 枚から、参照先になりうるもの（節見出しと番号つき主張）を拾う。
function collectAnchors(pg) {
  pg.markdown.split('\n').forEach((line, i) => {
    const h = line.match(/^#{1,6}\s+(\d+\.\d+)\s+(.+?)\s*$/);
    if (h) {
      register(secRefs, h[1], { slug: pg.slug, id: `sec-${h[1]}`, title: `${h[1]} ${h[2]}` },
        pg.src, i + 1);
      return;
    }
    const m = line.match(/^::: +(\S+)(.*)$/);
    if (!m) return;
    const spec = parseEnv((m[1] + m[2]).trim());
    if (!spec?.num) return;
    register(stmtRefs, spec.num,
      { slug: pg.slug, id: `${ANCHOR.get(spec.kind)}-${spec.num}`, label: spec.env.label, name: spec.name },
      pg.src, i + 1);
  });
}

// 同じページの中なら断片だけ、別ページなら相対パスを付ける。
function href(target, ctx) {
  const frag = target.id ? `#${target.id}` : '';
  if (target.slug === ctx.slug) return frag || `./${target.slug}.html`;
  return `./${target.slug}.html${frag}`;
}

// ホバーで飛び先が分かるよう title を添える（JS を使わない範囲での予告）。名前の中の
// $…$ は素の文字として出てしまうので、記号だけ落とす。
function stmtTitle(num, t) {
  const name = t.name ? `（${t.name.replace(/\$/g, '')}）` : '';
  return `${t.label} ${num}${name}`;
}

function xref(text, target, ctx, title) {
  const attr = title ? ` title="${escapeAttr(title)}"` : '';
  return `<a class="xref" href="${href(target, ctx)}"${attr}>${text}</a>`;
}

function linkStmt(text, kind, num, ctx, lineNo) {
  const t = stmtRefs.get(num);
  if (!t) {
    unresolvedRefs += 1;
    console.warn(`warn: 未解決の参照 ${ctx.src}:${lineNo} 「${text}」`);
    return text;
  }
  if (t.label !== kind) {
    unresolvedRefs += 1;
    console.warn(`warn: 参照の種別ちがい ${ctx.src}:${lineNo} 「${text}」は${t.label}`);
  }
  return xref(text, t, ctx, stmtTitle(num, t));
}

function linkSec(text, num, ctx, lineNo) {
  const t = secRefs.get(num);
  if (!t) {
    unresolvedRefs += 1;
    console.warn(`warn: 未解決の参照 ${ctx.src}:${lineNo} 「${text}」`);
    return text;
  }
  // 自分の節番号を自己参照しない（§8）。リンクにしてもページの先頭へ戻るだけになる。
  if (ctx.section?.num === num) {
    unresolvedRefs += 1;
    console.warn(`warn: 自節への参照 ${ctx.src}:${lineNo} 「${text}」（「本節」と書く）`);
    return text;
  }
  return xref(text, t, ctx, t.title);
}

function linkChap(text, num, ctx) {
  const t = chapRefs.get(num);
  if (!t || t.slug === ctx.chapter.slug) return text; // 自章への言及はリンクにしない
  return xref(text, t, ctx, t.title);
}

// 断片の中の主張参照だけをリンクにする（証明の名乗り `::: proof 定理 1.1.5` 用）。
function linkStatementRefs(text, ctx) {
  if (!text) return text;
  return text.replace(STMT_RE, (m, _kind, num) => {
    const t = stmtRefs.get(num);
    return t ? xref(m, t, ctx, stmtTitle(num, t)) : m;
  });
}

// 行内 code と数式の中は参照ではない（Lean の識別子・LaTeX が番号の形に当たる）。
// 退避に使う U+E000/U+E001 は私用領域で、原稿にもレンダリング結果にも現れない。
const STASH_OPEN = '\uE000';
const STASH_CLOSE = '\uE001';
const STASH_RE = /\uE000(\d+)\uE001/g;

// --- 取りこぼしの監査 (`build.mjs --audit-refs`) ---
// 「2.58 ビット」のような数値と、節番号「1.10」は字面では区別できない。だから判定はせず、
// 参照になりえたのに拾わなかった数字を並べるだけにする。vocab.ts の初出術語リストと同じ
// 考え方で、機械の仕事は目で読めるサイズまで候補を絞るところまでである。
const AUDIT = Deno.args.includes('--audit-refs');
const AUDIT_RE = /(?<![\d.])(\d+\.\d+)(?![\d.])/g;
const auditHits = [];

function auditLeftovers(masked, leftover, ctx, lineOf) {
  if (!AUDIT) return;
  for (const m of leftover.matchAll(AUDIT_RE)) {
    const window = masked.slice(Math.max(0, m.index - 26), m.index + 26).replace(/\n/g, ' ').trim();
    auditHits.push(`  ${ctx.src}:${lineOf(m.index)}  「${m[1]}」  …${window}…`);
  }
}

// 連続する散文行をまとめて受け取る。退避も検査も改行数を変えないので、警告の行番号は
// ブロック先頭からの改行の数で引ける。
function linkInline(text, ctx, startLine) {
  const stashed = [];
  const stash = (m) => `${STASH_OPEN}${stashed.push(m) - 1}${STASH_CLOSE}`;
  const masked = text
    .replace(/`[^`\n]*`/g, stash)
    .replace(/\$\$[^$\n]*\$\$/g, stash)
    .replace(/\$[^$\n]*\$/g, stash);
  const lineOf = (idx) => startLine + (masked.slice(0, idx).match(/\n/g)?.length ?? 0);

  const linked = masked.replace(REF_RE, (m, kind, snum, sec, chap, idx) => {
    const at = lineOf(idx);
    if (snum) return linkStmt(m, kind, snum.replace(/\s/g, ''), ctx, at);
    if (sec) return linkSec(m, sec, ctx, at);
    return linkChap(m, chap, ctx);
  });

  // 参照として拾えた分を伏せた残りから、種別のない番号を探す。
  const leftover = masked.replace(REF_RE, (m) => m.replace(/[^\n]/g, ' '));
  for (const m of leftover.matchAll(BARE_RE)) {
    const t = stmtRefs.get(m[1]);
    if (!t) continue;
    unresolvedRefs += 1;
    console.warn(
      `warn: 種別のない参照 ${ctx.src}:${lineOf(m.index)} 「${m[1]}」（「${t.label} ${m[1]}」と書く）`);
  }
  auditLeftovers(masked, leftover, ctx, lineOf);

  return linked.replace(STASH_RE, (_, i) => stashed[Number(i)]);
}

// 見出しは題であって参照ではない。環境タグ行（`::: theorem 1.6.1 …`）は宣言そのもので、
// 見出しの組み立てに使う文字列なので触らない（名乗りつき証明は headingMarkdown 側で扱う）。
function linkifyRefs(src, ctx) {
  const lines = src.split('\n');
  const out = [...lines];
  let block = [];
  let fence = false;
  let display = false;

  const flush = () => {
    if (!block.length) return;
    const linked = linkInline(block.map((i) => lines[i]).join('\n'), ctx, block[0] + 1).split('\n');
    block.forEach((i, k) => { out[i] = linked[k]; });
    block = [];
  };

  lines.forEach((line, i) => {
    const t = line.trim();
    let prose = true;
    if (t.startsWith('```')) { fence = !fence; prose = false; }
    else if (fence) prose = false;
    else if (display) { if (t === '$$') display = false; prose = false; }
    else if (t === '$$') { display = true; prose = false; }
    else if (/^\s{0,3}#{1,6}\s/.test(line) || t.startsWith(':::')) prose = false;
    if (prose) block.push(i);
    else flush();
  });
  flush();
  return out.join('\n');
}

// --- 形式化ポインタのリンク ---
// 原稿は宣言名とファイルパスを行内 code で書くだけで、URL は書かない（§7）。掲載先は
// ここで組む。宣言名は API ドキュメントの該当項目へ、パスは GitHub のソースへ飛ばす。
// 基準はリリースタグである（TEXTBOOK_REF で上書きできる）。タグ時点のソースから宣言表を
// 作るので、まだリリースに入っていない宣言も、移動して消えたパスも、リンクにならず warn に
// 出る。いったん張ったリンクはタグに固定されているから、あとのリネームでは腐らない。
// API ドキュメントだけは 1 版しか置けず常に最新リリースを指すが、同じブロックにタグ固定の
// ソースリンクが並ぶので、宣言名を変えても行き先は残る。
const REPO_URL = 'https://github.com/FujiHaruka/information-theory';
const APIDOC_URL = 'https://fujiharuka.github.io/information-theory';

function gitOut(...args) {
  try {
    const p = new Deno.Command('git', {
      args, cwd: resolve(root, '../..'), stdout: 'piped', stderr: 'null',
    }).outputSync();
    return p.success ? new TextDecoder().decode(p.stdout).trim() : null;
  } catch {
    return null;
  }
}

const REF = Deno.env.get('TEXTBOOK_REF')?.trim() || gitOut('describe', '--tags', '--abbrev=0') || '';

// 宣言表は Lean を解析せずテキスト走査で作る（sig_view.ts と同じ割り切り）。git grep の
// 正規表現は POSIX ERE で `\s` を解さないので、粗い前置フィルタで候補行を絞り、判定は
// JS 側で行う。
const DECL_PREFILTER = '^(@\\[|theorem|lemma|def|abbrev|structure|class|inductive|instance'
  + '|opaque|namespace|section|end|private|protected|noncomputable|nonrec|scoped|partial|unsafe)';
const MODIFIERS = '(?:(?:private|protected|scoped|noncomputable|nonrec|partial|unsafe)\\s+)*';
const NAME = "[A-Za-z_][A-Za-z0-9_'!?₀-₉ₐ-ₜ.]*";
const DECL_RE = new RegExp(`^(?:@\\[[^\\]]*\\]\\s*)*${MODIFIERS}`
  + `(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque)\\s+(${NAME})`);
// private は他の修飾子より前とは限らない（`noncomputable private def`）。
const PRIVATE_RE = new RegExp(`^(?:@\\[[^\\]]*\\]\\s*)*${MODIFIERS}private\\s`);

// 短い名前 → 宣言。同名は複数ありうる（`condEntropy` は 3 つ）ので、絞り込みは呼び出し側。
function scanDecls() {
  const decls = new Map();
  const files = new Set();
  const raw = REF && gitOut('grep', '-nE', DECL_PREFILTER, REF, '--', 'InformationTheory');
  if (!raw) return { decls, files };

  let scope = [];
  let file = null;
  for (const row of raw.split('\n')) {
    const m = row.match(/^[^:]*:([^:]+):(\d+):(.*)$/);
    if (!m) continue;
    const [, path, line, body] = m;
    if (path !== file) { file = path; scope = []; files.add(path); }

    let g;
    if ((g = body.match(/^namespace\s+(\S+)/))) { scope.push({ ns: true, name: g[1] }); continue; }
    if ((g = body.match(/^section\b\s*(\S*)/))) { scope.push({ ns: false, name: g[1] }); continue; }
    if ((g = body.match(/^end\b\s*(\S*)/))) {
      // 無名の end が閉じるのは無名 section だけで、namespace は名前つきの end でしか
      // 閉じない。ここを取り違えると、以降の宣言の名前空間がまるごとずれる。
      const top = scope[scope.length - 1];
      if (top && (g[1] === top.name || (g[1] === '' && !top.ns))) scope.pop();
      continue;
    }
    const d = body.match(DECL_RE);
    if (!d) continue;
    const fqn = [...scope.filter((s) => s.ns).map((s) => s.name), d[1]].join('.');
    decls.set(d[1], [...(decls.get(d[1]) ?? []),
      { fqn, path, line: Number(line), private: PRIVATE_RE.test(body) }]);
  }
  return { decls, files };
}

const { decls: leanDecls, files: leanFiles } = scanDecls();

// 原稿は `InformationTheory/Shannon/Bridge.lean` とも `MIChainRule.lean:93` とも書く。
// どちらも一意に決まるときだけ拾う。
function resolveLeanPath(spec) {
  const [p, line] = spec.split(':');
  if (leanFiles.has(p)) return { path: p, line };
  const hits = [...leanFiles].filter((f) => f.endsWith(`/${p}`));
  return hits.length === 1 ? { path: hits[0], line } : null;
}

const sourceUrl = ({ path, line }) => `${REPO_URL}/blob/${REF}/${path}${line ? `#L${line}` : ''}`;
const apidocUrl = (d) => `${APIDOC_URL}/${d.path.replace(/\.lean$/, '.html')}#${d.fqn}`;

// 行き先が 2 種類あることは、アイコンで見分けさせる。解説ページには本、GitHub の
// ソースには GitHub のマーク（どちらも octicons, MIT）。アイコンの意味は目次ページで 1 度
// 説明し（執筆原則 §7）、ホバーと読み上げには役割を語で出す。
const ICON_PATHS = {
  doc: [
    'M0 1.75A.75.75 0 0 1 .75 1h4.253c1.227 0 2.317.59 3 1.501A3.743 3.743 0 0 1 11.006',
    '1h4.245a.75.75 0 0 1 .75.75v10.5a.75.75 0 0 1-.75.75h-4.507a2.25 2.25 0 0',
    '0-1.591.659l-.622.621a.75.75 0 0 1-1.06 0l-.622-.621A2.25 2.25 0 0 0 5.258 13H.75a.75.75 0 0',
    '1-.75-.75Zm7.251 10.324.004-5.073-.002-2.253A2.25 2.25 0 0 0 5.003 2.5H1.5v9h3.757a3.75 3.75 0 0',
    '1 1.994.574ZM8.755 4.75l-.004 7.322a3.752 3.752 0 0 1 1.992-.572H14.5v-9h-3.495a2.25 2.25 0 0',
    '0-2.25 2.25Z',
  ].join(' '),
  src: [
    'M8 0c4.42 0 8 3.58 8 8a8.013 8.013 0 0 1-5.45 7.59c-.4.08-.55-.17-.55-.38',
    '0-.27.01-1.13.01-2.2 0-.75-.25-1.23-.54-1.48 1.78-.2 3.65-.88 3.65-3.95',
    '0-.88-.31-1.59-.82-2.15.08-.2.36-1.02-.08-2.12 0 0-.67-.22-2.2.82-.64-.18-1.32-.27-2-.27s-1.36.09-2',
    '.27c-1.53-1.03-2.2-.82-2.2-.82-.44 1.1-.16 1.92-.08 2.12-.51.56-.82 1.27-.82 2.15 0 3.06 1.86 3.75',
    '3.64 3.95-.23.2-.44.55-.51',
    '1.07-.46.21-1.61.55-2.33-.66-.15-.24-.6-.83-1.23-.82-.67.01-.27.38.01.53.34.19.73.9.82',
    '1.13.16.45.68 1.31 2.69.94 0 .67.01 1.3.01 1.49 0 .21-.15.45-.55.38A7.995 7.995 0 0',
    '1 0 8c0-4.42 3.58-8 8-8Z',
  ].join(' '),
};const icon = (kind) => `<svg class="ptr-icon" viewBox="0 0 16 16" aria-hidden="true">`
  + `<path d="${ICON_PATHS[kind]}"/></svg>`;

const LEAN_PATH_RE = /^[A-Za-z][\w/]*\.lean(?::\d+)?$/;
const IDENT_RE = new RegExp(`^${NAME}$`);
const unlinkedCodes = [];
let brokenPointers = 0;

// ブロック 1 つ分の行内 code をリンクに変える。宣言名が複数のファイルにあるときは、同じ
// ブロックが名指ししているパスで絞る（原稿はパスを併記する決まりなので、これで足りる）。
function linkFormalized(state, tokens, ctx, lineNo) {
  const codes = [];
  for (const t of tokens) {
    if (t.type !== 'inline') continue;
    t.children.forEach((c, k) => {
      if (c.type === 'code_inline') codes.push({ inline: t, k, text: c.content.trim() });
    });
  }

  const here = new Set();
  for (const c of codes) {
    if (!LEAN_PATH_RE.test(c.text)) continue;
    const r = resolveLeanPath(c.text);
    if (!r) {
      brokenPointers += 1;
      console.warn(`warn: 形式化ポインタ ${ctx.src}:${lineNo} 「${c.text}」は ${REF} に見つからない`);
      continue;
    }
    c.url = sourceUrl(r);
    c.kind = 'src';
    c.title = r.path;
    here.add(r.path);
  }

  for (const c of codes) {
    if (c.url || !IDENT_RE.test(c.text)) continue;
    const cand = leanDecls.get(c.text) ?? [];
    const narrowed = cand.length > 1 ? cand.filter((d) => here.has(d.path)) : cand;
    if (narrowed.length !== 1) {
      if (cand.length > 1) {
        brokenPointers += 1;
        console.warn(`warn: 形式化ポインタ ${ctx.src}:${lineNo} 「${c.text}」は`
          + ` ${cand.length} 箇所にある（ファイルを併記して絞る）`);
      } else if (AUDIT) {
        unlinkedCodes.push(`  ${ctx.src}:${lineNo}  「${c.text}」`);
      }
      continue;
    }
    const d = narrowed[0];
    // private 宣言は API ドキュメントに載らないので、ソースの該当行へ送る。
    c.kind = d.private ? 'src' : 'doc';
    c.url = d.private ? sourceUrl(d) : apidocUrl(d);
    c.title = d.private ? `${d.path}#L${d.line}` : d.fqn;
  }

  // 差し込みで添字がずれないよう、同じ inline の中を後ろから開く。
  for (const c of codes.filter((c) => c.url).reverse()) {
    const role = c.kind === 'doc' ? '解説ページ' : `ソース ${REF}`;
    const open = new state.Token('link_open', 'a', 1);
    open.attrSet('class', 'srcref');
    open.attrSet('href', c.url);
    open.attrSet('title', `${role}: ${c.title}`);
    open.attrSet('aria-label', `${role}: ${c.title}`);
    const mark = new state.Token('html_inline', '', 0);
    mark.content = icon(c.kind);
    // 宣言名は残す（読者が名前を知る手がかりであり、1 ブロックに 2 つ以上並ぶと互いの
    // 区別も担う）。パスは行の中でいちばん長いのに読者には用がないので、共通の語に寄せ、
    // 原稿が書いたパスはホバーと読み上げに回す（原稿側は書き換えない）。
    let body = c.inline.children[c.k];
    if (c.kind === 'src') {
      body = new state.Token('text', '', 0);
      body.content = 'ソース';
    }
    c.inline.children.splice(c.k, 1, open, mark, body,
      new state.Token('link_close', 'a', -1));
  }
}

// 傍注が名指しした宣言名 / パスの実在確認。リンクには変えない——ポインタは
// `::: formalized` の仕事で（執筆原則 §7）、注記まで行き先だらけにすると本筋との差が
// 消える。ただし名前が腐るのはポインタと同じなので、検査だけは同じものを掛ける。
// パスは一意に決まるので warn、宣言名は Mathlib の名前と区別できないので監査モードの
// 一覧に回す（`--audit-refs` の考え方）。
function checkNoteRefs(tokens, ctx, lineNo) {
  for (const t of tokens) {
    if (t.type !== 'inline') continue;
    for (const c of t.children) {
      if (c.type !== 'code_inline') continue;
      const text = c.content.trim();
      if (LEAN_PATH_RE.test(text)) {
        if (!resolveLeanPath(text)) {
          brokenPointers += 1;
          console.warn(`warn: 注記の形式化ポインタ ${ctx.src}:${lineNo}`
            + ` 「${text}」は ${REF} に見つからない`);
        }
      } else if (AUDIT && IDENT_RE.test(text) && !leanDecls.has(text)) {
        unlinkedCodes.push(`  ${ctx.src}:${lineNo}  「${text}」（注記）`);
      }
    }
  }
}

md.core.ruler.push('formalized_links', (state) => {
  const ctx = state.env?.ctx;
  if (!ctx || !REF) return;
  const toks = state.tokens;
  for (let i = 0; i < toks.length; i++) {
    if (toks[i].type !== 'container_env_open') continue;
    const kind = parseEnv(toks[i].info)?.kind;
    if (kind !== 'formalized' && kind !== 'formalization-note') continue;
    let j = i + 1;
    while (j < toks.length && toks[j].type !== 'container_env_close') j++;
    const line = (toks[i].map?.[0] ?? toks.slice(i, j).find((t) => t.map)?.map?.[0] ?? 0) + 1;
    if (kind === 'formalized') linkFormalized(state, toks.slice(i, j), ctx, line);
    else checkNoteRefs(toks.slice(i, j), ctx, line);
    i = j;
  }
});

let missingProofs = 0;
let termIssues = 0;

// 出力は毎回まっさらから組む。節を消したときに前回の HTML が残ると、目次から辿れない
// ページがデプロイ先で生き続ける。
rmSync(distDir, { recursive: true, force: true });
mkdirSync(distDir, { recursive: true });

// --- 参照先の収集（本文を組む前に、全ページ分の番号を集めきる） ---
for (const c of chapters) {
  chapRefs.set(c.num.replace(/\D/g, ''), { slug: chapterHome(c), title: `${c.num} ${c.title}` });
}
for (const pg of pages) {
  pg.markdown = readFileSync(resolve(root, pg.src), 'utf8');
  collectAnchors(pg);
}

// --- content pages ---
pages.forEach((pg, i) => {
  const markdown = pg.markdown;
  missingProofs += lintProofs(markdown, pg.src);
  termIssues += lintTerminology(markdown, pg.src);
  let bodyHtml = navTop(pg) + md.render(linkifyRefs(normalizeMath(markdown), pg), { ctx: pg });
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
    <a href="./${chapterHome(c)}.html">${escapeHtml(c.num)}　${escapeHtml(c.title)}</a>
    <span class="status">${escapeHtml(c.status)}</span>${sub}
  </li>`;
  })
  .join('\n');

const indexBody = `<h1>${escapeHtml(siteTitle)}</h1>
<p>Lean 4 + Mathlib で機械検証した定理に紐づけて書いている情報理論の教科書原稿です。<!--
-->「形式化」と添えた結果は無条件の検証済み定理に対応しています。宣言名はリンクになっていて、<!--
-->本のアイコンはその定理の解説ページ、GitHub のマークはソースへ飛びます。<!--
-->本文の証明は人間が読みやすい順序で書いているので、Lean がたどる証明ルートとは<!--
-->一致しません。保証されるのは定理の正しさであって、証明手順の一致ではありません。</p>
<ul class="toc">
${tocItems}
</ul>`;

writeFileSync(resolve(distDir, 'index.html'), page({ title: siteTitle, bodyHtml: indexBody }), 'utf8');
console.log(`built index -> dist/index.html (${pages.length} pages)`);

if (missingProofs > 0) console.warn(`warn: 証明のない主張 ${missingProofs} 件`);
if (termIssues > 0) console.warn(`warn: 表記ゆれ ${termIssues} 件`);
if (unresolvedRefs > 0) console.warn(`warn: 参照 ${unresolvedRefs} 件`);
if (duplicateNums > 0) console.warn(`warn: 番号の重複 ${duplicateNums} 件`);
if (brokenPointers > 0) console.warn(`warn: 形式化ポインタ ${brokenPointers} 件`);
if (AUDIT) {
  console.log(`\n--- 参照にならなかった数字 ${auditHits.length} 件（判定なし・目で読む） ---`);
  for (const h of auditHits) console.log(h);
  console.log(
    `\n--- リンクにならなかった形式化ポインタの語 ${unlinkedCodes.length} 件（判定なし・目で読む） ---`);
  for (const h of unlinkedCodes) console.log(h);
}
console.log('done');
