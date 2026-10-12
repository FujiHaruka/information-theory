export default function draw({ svg, tex, arrow, dot }) {
  const W = 440;
  const H = 190;
  const xl = 150;
  const xr = 290;
  const yl = [50, 150];
  const yr = [40, 100, 160];
  return svg({ width: W, height: H },
    arrow(xl, yl[0], xr, yr[0], { trim: 10 }),
    arrow(xl, yl[1], xr, yr[2], { trim: 10 }),
    arrow(xl, yl[0], xr, yr[1], { trim: 10, cls: 'f-arrow-muted' }),
    arrow(xl, yl[1], xr, yr[1], { trim: 10, cls: 'f-arrow-muted' }),
    dot(xl, yl[0]), dot(xl, yl[1]), ...yr.map((v) => dot(xr, v)),
    tex('0', { x: xl - 18, y: yl[0] }), tex('1', { x: xl - 18, y: yl[1] }),
    tex('0', { x: xr + 18, y: yr[0] }), tex('\\ast', { x: xr + 18, y: yr[1] }), tex('1', { x: xr + 18, y: yr[2] }),
    tex('1-\\eta', { x: (xl + xr) / 2, y: (yl[0] + yr[0]) / 2 - 15 }),
    tex('1-\\eta', { x: (xl + xr) / 2, y: (yl[1] + yr[2]) / 2 + 17 }),
    tex('\\eta', { x: (xl + xr) / 2 + 4, y: (yl[0] + yr[1]) / 2 + 13 }),
    tex('\\eta', { x: (xl + xr) / 2 + 4, y: (yl[1] + yr[1]) / 2 - 13 }),
    tex('X', { x: xl, y: 14 }), tex('Y', { x: xr, y: 14 }),
  );
}
