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

function circle(cx, cy, r, cls) {
  return `<circle cx="${num(cx)}" cy="${num(cy)}" r="${num(r)}" class="${cls}"/>`;
}

function rect(x, y, w, h, cls, rx = 0) {
  return `<rect x="${num(x)}" y="${num(y)}" width="${num(w)}" height="${num(h)}" rx="${rx}" class="${cls}"/>`;
}

function dot(x, y, r = 3.6) {
  return circle(x, y, r, 'f-dot');
}

function arrowHead(x, y, angle, size, cls) {
  const p = (da) => [x - size * Math.cos(angle + da), y - size * Math.sin(angle + da)];
  const [a, b] = [p(0.42), p(-0.42)];
  return `<path d="M${num(x)},${num(y)}L${num(a[0])},${num(a[1])}L${num(b[0])},${num(b[1])}Z" class="${cls}-head"/>`;
}

function arrow(x1, y1, x2, y2, { bend = 0, cls = 'f-arrow', head = 8, trim = 0 } = {}) {
  const mx = (x1 + x2) / 2;
  const my = (y1 + y2) / 2;
  const len = Math.hypot(x2 - x1, y2 - y1);
  const cx = mx - (bend * (y2 - y1)) / len;
  const cy = my + (bend * (x2 - x1)) / len;
  const along = (x, y, tx, ty, d) => {
    const l = Math.hypot(tx - x, ty - y);
    return [x + ((tx - x) * d) / l, y + ((ty - y) * d) / l];
  };
  const [sx, sy] = trim ? along(x1, y1, cx, cy, trim) : [x1, y1];
  const [ex, ey] = trim ? along(x2, y2, cx, cy, trim) : [x2, y2];
  const d = bend
    ? `M${num(sx)},${num(sy)}Q${num(cx)},${num(cy)} ${num(ex)},${num(ey)}`
    : `M${num(sx)},${num(sy)}L${num(ex)},${num(ey)}`;
  const angle = Math.atan2(ey - (bend ? cy : sy), ex - (bend ? cx : sx));
  return path(d, cls) + arrowHead(ex, ey, angle, head, cls);
}

function selfLoop(cx, cy, r, { side = 'left', size = 34, cls = 'f-arrow', head = 8 } = {}) {
  const dir = side === 'left' ? -1 : 1;
  const at = (deg) => [cx + dir * r * Math.cos((deg * Math.PI) / 180), cy - r * Math.sin((deg * Math.PI) / 180)];
  const [sx, sy] = at(35);
  const [ex, ey] = at(-35);
  const c1 = [cx + dir * (r + size * 1.6), cy - size * 1.4];
  const c2 = [cx + dir * (r + size * 1.6), cy + size * 1.4];
  const d = `M${num(sx)},${num(sy)}C${num(c1[0])},${num(c1[1])} ${num(c2[0])},${num(c2[1])} ${num(ex)},${num(ey)}`;
  return path(d, cls) + arrowHead(ex, ey, Math.atan2(ey - c2[1], ex - c2[0]), head, cls);
}

function axes({ sx, sy, xLabel, yLabel, xTicks = [], yTicks = [], emSize = 15 }) {
  const [x0, x1] = sx.range();
  const [y0, y1] = sy.range();
  return [
    path(`M${x0},${y0}H${x1 + 8}`, 'f-axis'),
    path(`M${x0},${y0}V${y1 - 10}`, 'f-axis'),
    ...xTicks.map(([v, l]) => path(`M${num(sx(v))},${y0}v4`, 'f-axis') + tex(l, { x: sx(v), y: y0 + 18, emSize })),
    ...yTicks.map(([v, l]) => path(`M${x0},${num(sy(v))}h-4`, 'f-axis')
      + tex(l, { x: x0 - 9, y: sy(v), anchor: 'end', emSize })),
    xLabel ? tex(xLabel, { x: x1 + 14, y: y0, anchor: 'start', emSize }) : '',
    yLabel ? tex(yLabel, { x: x0, y: y1 - 22, emSize }) : '',
  ];
}

export const kit = {
  adaptor: null, tex, text, path, svg, plot, circle, rect, dot, arrow, selfLoop, axes, scaleLinear, line,
};
