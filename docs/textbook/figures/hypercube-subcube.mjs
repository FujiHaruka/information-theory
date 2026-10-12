export default function draw({ svg, tex, path, circle }) {
  const W = 440;
  const H = 260;
  const pos = (x1, x2, x3) => [140 + x2 * 140 + x1 * 70, 200 - x3 * 140 - x1 * 50];
  const verts = [];
  for (let v = 0; v < 8; v++) verts.push([(v >> 2) & 1, (v >> 1) & 1, v & 1]);
  const inA = ([x1]) => x1 === 0;
  const out = [];
  for (const a of verts) {
    for (let i = 0; i < 3; i++) {
      if (a[i] === 1) continue;
      const b = [...a];
      b[i] = 1;
      const hot = inA(a) !== inA(b);
      const [p, q] = [pos(...a), pos(...b)];
      out.push(path(`M${p[0]},${p[1]}L${q[0]},${q[1]}`, hot ? 'f-edge-hot' : 'f-edge'));
    }
  }
  for (const v of verts) {
    const [x, y] = pos(...v);
    out.push(circle(x, y, 6, inA(v) ? 'f-node' : 'f-hollow'));
    out.push(tex(`\\mathtt{${v.join('')}}`, { x: x + (v[1] ? 14 : -14), y: y + (v[2] ? -12 : 14),
      anchor: v[1] ? 'start' : 'end', emSize: 12 }));
  }
  return svg({ width: W, height: H }, ...out);
}
