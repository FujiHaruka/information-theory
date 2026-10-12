export default function draw({ svg, tex, path, circle, rect }) {
  const W = 440;
  const H = 250;
  const depthY = [30, 85, 140, 195];
  const leafX = (i) => 60 + i * 46;
  const nodes = new Map();
  const place = (word) => {
    const d = word.length;
    const span = 2 ** (3 - d);
    const first = parseInt(word.padEnd(3, '0'), 2);
    return [(leafX(first) + leafX(first + span - 1)) / 2, depthY[d]];
  };
  const words = ['', '0', '1', '00', '01', '10', '11'];
  for (let i = 0; i < 8; i++) words.push(i.toString(2).padStart(3, '0'));
  for (const w of words) nodes.set(w, place(w));
  const code = { '0': 'c(1)', '10': 'c(2)', '110': 'c(3)', '111': 'c(4)' };

  const out = [];
  for (const w of words) {
    if (!w) continue;
    const [x, y] = nodes.get(w);
    const [px, py] = nodes.get(w.slice(0, -1));
    out.push(path(`M${px},${py}L${x},${y}`, 'f-edge'));
    out.push(tex(w.at(-1), { x: (px + x) / 2 + (w.at(-1) === '0' ? -8 : 8), y: (py + y) / 2 - 4, emSize: 12 }));
  }
  for (const c of Object.keys(code)) {
    const first = parseInt(c.padEnd(3, '0'), 2);
    const last = parseInt(c.padEnd(3, '1'), 2);
    out.push(rect(leafX(first) - 19, depthY[3] + 13, leafX(last) - leafX(first) + 38, 18, 'f-area', 4));
  }
  for (const w of words) {
    const [x, y] = nodes.get(w);
    out.push(circle(x, y, code[w] ? 7 : 4, code[w] ? 'f-node' : 'f-hollow'));
    if (code[w]) out.push(tex(code[w], { x: x + 12, y: y - 12, anchor: 'start', emSize: 13 }));
  }
  for (let i = 0; i < 8; i++) {
    const leaf = i.toString(2).padStart(3, '0');
    const [x, y] = nodes.get(leaf);
    out.push(tex(`\\mathtt{${leaf}}`, { x, y: y + 22, emSize: 11 }));
  }
  return svg({ width: W, height: H }, ...out);
}
