export default function draw({ svg, tex, rect, path }) {
  const q1 = 1 / 4;
  const xs = [1, 0, 1];
  const W = 440;
  const H = 250;
  const left = 40;
  const width = 320;
  const rowY = (i) => 24 + i * 62;
  const h = 18;
  const out = [];
  let [lo, hi] = [0, 1];
  xs.forEach((sym, i) => {
    const y = rowY(i);
    const cut = lo + (hi - lo) * (1 - q1);
    const map = (v) => left + ((v - lo) / (hi - lo)) * width;
    out.push(rect(map(lo), y, map(cut) - map(lo), h, sym === 0 ? 'f-node' : 'f-hollow'));
    out.push(rect(map(cut), y, map(hi) - map(cut), h, sym === 1 ? 'f-node' : 'f-hollow'));
    out.push(tex('0', { x: (map(lo) + map(cut)) / 2, y: y + h / 2, emSize: 13 }));
    out.push(tex('1', { x: (map(cut) + map(hi)) / 2, y: y + h / 2, emSize: 13 }));
    out.push(tex(fmt(lo), { x: map(lo), y: y - 9, emSize: 11 }));
    out.push(tex(fmt(hi), { x: map(hi), y: y - 9, emSize: 11 }));
    const [nlo, nhi] = sym === 0 ? [lo, cut] : [cut, hi];
    out.push(path(`M${map(nlo)},${y + h}L${left},${rowY(i + 1) - 16}M${map(nhi)},${y + h}L${left + width},${rowY(i + 1) - 16}`, 'f-guide'));
    out.push(tex(`x_${i + 1} = ${sym}`, { x: left + width + 14, y: y + h / 2, anchor: 'start', emSize: 13 }));
    [lo, hi] = [nlo, nhi];
  });
  const y = rowY(3);
  out.push(rect(left, y, width, h, 'f-node'));
  out.push(tex(fmt(lo), { x: left, y: y - 9, emSize: 11 }));
  out.push(tex(fmt(hi), { x: left + width, y: y - 9, emSize: 11 }));
  out.push(tex('x = (1,0,1)', { x: left + width / 2, y: y + h / 2, emSize: 13 }));
  return svg({ width: W, height: H }, ...out);
}

function fmt(v) {
  const n = Math.round(v * 64);
  if (n === 0) return '0';
  if (n === 64) return '1';
  let [a, b] = [n, 64];
  while (a % 2 === 0) [a, b] = [a / 2, b / 2];
  return `\\tfrac{${a}}{${b}}`;
}
