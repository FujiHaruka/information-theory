export default function draw({ svg, tex, path, circle, dot }) {
  const W = 440;
  const H = 240;
  const [cx, cy] = [190, 120];
  const r = 34;
  const outer = 3 * r;
  const codeword = Math.sqrt(8) * r;
  const centers = [[0, 0], ...[0, 1, 2, 3, 4, 5].map((i) => [2 * r * Math.cos((i * Math.PI) / 3), 2 * r * Math.sin((i * Math.PI) / 3)])];
  const at = (rad, deg) => [cx + rad * Math.cos((deg * Math.PI) / 180), cy - rad * Math.sin((deg * Math.PI) / 180)];
  const [ox, oy] = at(outer, 35);
  const [gx, gy] = at(codeword, 200);
  const [nx, ny] = [cx + 2 * r + r * Math.cos(-Math.PI / 4), cy + r * Math.sin(Math.PI / 4)];
  return svg({ width: W, height: H },
    circle(cx, cy, outer, 'f-box'),
    circle(cx, cy, codeword, 'f-guide'),
    ...centers.map(([dx, dy]) => circle(cx + dx, cy + dy, r, 'f-region-a')),
    ...centers.map(([dx, dy]) => dot(cx + dx, cy + dy, 2.6)),
    path(`M${ox},${oy}L${ox + 34},${oy - 20}`, 'f-leader'),
    tex('\\sqrt{n(P+N)}', { x: ox + 38, y: oy - 22, anchor: 'start' }),
    path(`M${gx},${gy}L${gx - 30},${gy + 26}`, 'f-leader'),
    tex('\\sqrt{nP}', { x: gx - 34, y: gy + 30, anchor: 'end' }),
    path(`M${nx},${ny}L${nx + 60},${ny + 26}`, 'f-leader'),
    tex('\\sqrt{nN}', { x: nx + 64, y: ny + 28, anchor: 'start' }),
  );
}
