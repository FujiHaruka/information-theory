import { mathjax as MathJax } from 'npm:@mathjax/src@4/js/mathjax.js';
import { TeX } from 'npm:@mathjax/src@4/js/input/tex.js';
import { SVG } from 'npm:@mathjax/src@4/js/output/svg.js';
import 'npm:@mathjax/src@4/js/input/tex/base/BaseConfiguration.js';
import 'npm:@mathjax/src@4/js/input/tex/ams/AmsConfiguration.js';
import { MathJaxNewcmFont } from 'npm:@mathjax/mathjax-newcm-font@4/js/svg.js';
import { MathJaxEulerFontExtension } from 'npm:@mathjax/mathjax-euler-font-extension@4/js/svg.js';
import { scaleLinear } from 'npm:d3-scale@4.0.2';
import { line, curveLinear } from 'npm:d3-shape@3.2.0';

MathJaxNewcmFont.addExtension(MathJaxEulerFontExtension);

// 素の import() では読めない: Euler の SVG 版の動的レンジは依存に無い `@mathjax/fonts` を import している。
const EULER_SVG_DYNAMIC = /^npm:@mathjax\/mathjax-euler-font-extension@4\/js\/svg\/dynamic\//;
export async function loadEulerSvgDynamic(spec) {
  if (!EULER_SVG_DYNAMIC.test(spec)) return null;
  const src = (await Deno.readTextFile(new URL(import.meta.resolve(spec))))
    .replace(/^import \{ GenericFont \} from '@mathjax\/fonts\/generic\/mjs\/svg\.js';$/m,
      "import { MathJaxNewcmFont as GenericFont } from 'npm:@mathjax/mathjax-newcm-font@4/js/svg.js';");
  return import(`data:text/javascript;base64,${btoa(unescape(encodeURIComponent(src)))}`);
}

let svgOut = null;
let svgDoc = null;

export async function initFigureKit(adaptor) {
  svgOut = new SVG({ fontData: MathJaxNewcmFont, fontCache: 'none', linebreaks: { inline: false } });
  svgDoc = MathJax.document('', {
    InputJax: new TeX({ packages: ['base', 'ams'] }),
    OutputJax: svgOut,
  });
  await svgOut.font.loadDynamicFiles();
  kit.adaptor = adaptor;
}

const num = (v) => Number(v.toFixed(2));

function tex(latex, { x, y, anchor = 'middle', baseline = 'middle', emSize = 15 } = {}) {
  const html = kit.adaptor.outerHTML(svgDoc.convert(latex, { display: false }));
  if (html.includes('data-mjx-error')) throw new Error(`図の数式を組めない: ${latex}`);
  const m = html.match(/<svg([^>]*)>([\s\S]*)<\/svg>/);
  const attr = (k) => m[1].match(new RegExp(`${k}="([^"]+)"`))[1];
  const ex = emSize / 2;
  const w = parseFloat(attr('width')) * ex;
  const h = parseFloat(attr('height')) * ex;
  const [, minY, , vbH] = attr('viewBox').split(/\s+/).map(Number);
  const ascent = (-minY / vbH) * h;
  const left = anchor === 'start' ? x : anchor === 'end' ? x - w : x - w / 2;
  const top = baseline === 'baseline' ? y - ascent : y - h / 2;
  return `<svg x="${num(left)}" y="${num(top)}" width="${num(w)}" height="${num(h)}" `
    + `viewBox="${attr('viewBox')}" overflow="visible" aria-hidden="true">${m[2]}</svg>`;
}

function text(str, { x, y, anchor = 'middle', size = 13, cls = '' } = {}) {
  const c = cls ? ` class="${cls}"` : '';
  return `<text x="${num(x)}" y="${num(y)}" font-size="${size}" text-anchor="${anchor}" `
    + `dominant-baseline="middle"${c}>${str}</text>`;
}

function path(d, cls) {
  return `<path d="${d}" class="${cls}"/>`;
}

function svg({ width, height }, ...children) {
  return `<svg viewBox="0 0 ${width} ${height}" xmlns="http://www.w3.org/2000/svg" `
    + `role="img">${children.flat().join('')}</svg>`;
}

function plot(f, [a, b], sx, sy, samples = 400) {
  const pts = Array.from({ length: samples + 1 }, (_, i) => {
    const t = a + ((b - a) * i) / samples;
    return [sx(t), sy(f(t))];
  });
  return line().curve(curveLinear)(pts.map(([u, v]) => [num(u), num(v)]));
}

export const kit = { adaptor: null, tex, text, path, svg, plot, scaleLinear, line };
