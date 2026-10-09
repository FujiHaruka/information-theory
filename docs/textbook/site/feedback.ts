#!/usr/bin/env -S deno run -A
import { chapters } from './chapters.mjs';

const API = 'https://api.hypothes.is/api';
const GROUP = 'Y5Ezjaq5';
const SITE = 'https://info-theory.fuji.land';
const DONE = 'done';

const root = new URL('..', import.meta.url).pathname;

type Selector = { type: string; exact?: string };
type Annotation = {
  id: string;
  uri: string;
  text: string;
  tags: string[];
  user: string;
  created: string;
  group: string;
  links: { incontext?: string };
  target: { selector?: Selector[] }[];
};

const token = Deno.env.get('HYPOTHESIS_TOKEN') ??
  (await Deno.readTextFile(`${Deno.env.get('HOME')}/.config/hypothesis/token`)).trim();

async function api(path: string, init: RequestInit = {}) {
  const res = await fetch(`${API}${path}`, {
    ...init,
    headers: { Authorization: `Bearer ${token}`, 'Content-Type': 'application/json', ...init.headers },
  });
  if (!res.ok) throw new Error(`${init.method ?? 'GET'} ${path}: ${res.status} ${await res.text()}`);
  return res.json();
}

async function search(params: Record<string, string>): Promise<Annotation[]> {
  const out: Annotation[] = [];
  let after = '';
  for (;;) {
    const q = new URLSearchParams({ ...params, limit: '200', sort: 'created', order: 'asc' });
    if (after) q.set('search_after', after);
    const { rows } = await api(`/search?${q}`);
    out.push(...rows);
    if (rows.length < 200) return out;
    after = rows[rows.length - 1].created;
  }
}

const args = Deno.args;

if (args[0] === '--done') {
  for (const id of args.slice(1)) {
    const a: Annotation = await api(`/annotations/${id}`);
    if (!a.tags.includes(DONE)) {
      await api(`/annotations/${id}`, { method: 'PATCH', body: JSON.stringify({ tags: [...a.tags, DONE] }) });
    }
    console.log(`done: ${id}`);
  }
  Deno.exit(0);
}

const srcBySlug = new Map<string, string>();
for (const s of chapters.flatMap((c) => c.sections)) srcBySlug.set(s.slug, s.src);

const slugOf = (uri: string) => new URL(uri).pathname.replace(/^\//, '').replace(/\.html$/, '');

const quoteOf = (a: Annotation) =>
  a.target.flatMap((t) => t.selector ?? []).find((s) => s.type === 'TextQuoteSelector')?.exact ?? '';

// 引用全体で引かないのは、数式の隠れた MathML の文字が混ざって原稿と一致しないため。
function lineHints(src: string, quote: string): number[] {
  const runs = quote.match(/[　-ヿ一-鿿！-～]{4,}/g) ?? [];
  const needle = runs.sort((x, y) => y.length - x.length)[0];
  if (!needle) return [];
  const lines = Deno.readTextFileSync(`${root}${src}`).split('\n');
  return lines.flatMap((l, i) => (l.includes(needle) ? [i + 1] : []));
}

const all = await search({ group: GROUP });
const rows = args.includes('--all') ? all : all.filter((a) => !a.tags.includes(DONE));

const byFile = new Map<string, Annotation[]>();
for (const a of rows) {
  const src = srcBySlug.get(slugOf(a.uri)) ?? `(原稿不明) ${a.uri}`;
  byFile.set(src, [...(byFile.get(src) ?? []), a]);
}

for (const [src, list] of byFile) {
  console.log(`## ${src}\n`);
  for (const a of list) {
    const quote = quoteOf(a).replace(/\s+/g, ' ').trim();
    const hints = src.startsWith('(') ? [] : lineHints(src, quote);
    const at = hints.length ? `docs/textbook/${src}:${hints.join(',')}` : '行は特定できず';
    console.log(`- [${a.id}] ${at}${a.tags.includes(DONE) ? ' (done)' : ''}`);
    if (quote) console.log(`  > ${quote}`);
    console.log(`  ${a.text.replace(/\n/g, '\n  ')}\n`);
  }
}
console.log(`${rows.length} 件（グループ内 ${all.length} 件）`);

const { userid } = await api('/profile');
const stray = (await search({ user: userid, wildcard_uri: `${SITE}/*` })).filter((a) => a.group !== GROUP);
if (stray.length) {
  console.log(`\nwarn: レビュー用グループの外に付いたコメントが ${stray.length} 件ある（サイドバーのグループ選択を確認）`);
  for (const a of stray) console.log(`  [${a.id}] ${a.links.incontext ?? a.uri}`);
}
