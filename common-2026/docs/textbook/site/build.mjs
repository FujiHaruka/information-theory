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

// --- pages to build (slug → source markdown) ---
const pages = [
  { slug: 'index', title: '第2章 エントロピー・相互情報量・データ処理不等式', src: 'ch02-entropy.md' },
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
@media (prefers-color-scheme: dark) {
  body { background: #15171a; color: #e6e6e6; }
  a { color: #6cb6ff; }
  blockquote { border-left-color: #333a42; color: #9aa3ad; background: none; }
  code { background: rgba(255,255,255,.08); color: inherit; }
  pre { background: #1c1f24; }
  pre code { background: none; color: #d7dce2; }
  hr { border-color: #2a2e34; }
  th, td { border-color: #2a2e34; }
}
`;

function page({ title, bodyHtml }) {
  return `<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>${title}</title>
${cssCdn}
<style>${styles}</style>
</head>
<body>
<div class="container">
${bodyHtml}
<p class="site-note">InformationTheory — 形式化検証つき情報理論教科書（パイロット）。数式は KaTeX で事前レンダリング。</p>
</div>
</body>
</html>`;
}

mkdirSync(distDir, { recursive: true });

for (const p of pages) {
  const srcPath = resolve(root, p.src);
  const markdown = readFileSync(srcPath, 'utf8');
  const bodyHtml = md.render(markdown);
  const html = page({ title: p.title, bodyHtml });
  const outPath = resolve(distDir, `${p.slug}.html`);
  writeFileSync(outPath, html, 'utf8');
  console.log(`built ${p.src} -> dist/${p.slug}.html (${html.length} bytes)`);
}

// surge serves 200.html as SPA fallback; also copy index as 404 target safety
console.log('done');
