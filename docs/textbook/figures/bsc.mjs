export default function draw({ svg, tex, arrow, dot }) {
  const W = 440;
  const H = 170;
  const xl = 150;
  const xr = 290;
  const y = [45, 135];
  return svg({ width: W, height: H },
    arrow(xl, y[0], xr, y[0], { trim: 10 }),
    arrow(xl, y[1], xr, y[1], { trim: 10 }),
    arrow(xl, y[0], xr, y[1], { trim: 10, cls: 'f-arrow-muted' }),
    arrow(xl, y[1], xr, y[0], { trim: 10, cls: 'f-arrow-muted' }),
    dot(xl, y[0]), dot(xl, y[1]), dot(xr, y[0]), dot(xr, y[1]),
    tex('0', { x: xl - 18, y: y[0] }), tex('1', { x: xl - 18, y: y[1] }),
    tex('0', { x: xr + 18, y: y[0] }), tex('1', { x: xr + 18, y: y[1] }),
    tex('1-\\rho', { x: (xl + xr) / 2, y: y[0] - 14 }),
    tex('1-\\rho', { x: (xl + xr) / 2, y: y[1] + 16 }),
    tex('\\rho', { x: xl + 32, y: (y[0] + y[1]) / 2 - 22 }),
    tex('\\rho', { x: xl + 32, y: (y[0] + y[1]) / 2 + 22 }),
    tex('X', { x: xl, y: 14 }), tex('Y', { x: xr, y: 14 }),
  );
}
