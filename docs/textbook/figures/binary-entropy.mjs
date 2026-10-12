export default function draw({ svg, tex, path, plot, scaleLinear }) {
  const W = 440;
  const H = 280;
  const m = { left: 52, right: 24, top: 22, bottom: 44 };
  const sx = scaleLinear([0, 1], [m.left, W - m.right]);
  const sy = scaleLinear([0, 1], [H - m.bottom, m.top]);
  const hb = (p) => (p <= 0 || p >= 1 ? 0 : -(p * Math.log2(p) + (1 - p) * Math.log2(1 - p)));

  const x0 = sx(0);
  const y0 = sy(0);
  return svg({ width: W, height: H },
    path(`M${x0},${y0}H${sx(1) + 8}`, 'f-axis'),
    path(`M${x0},${y0}V${sy(1) - 10}`, 'f-axis'),
    path(`M${sx(0.5)},${y0}V${sy(1)}H${x0}`, 'f-guide'),
    path(plot(hb, [0, 1], sx, sy), 'f-curve'),
    `<circle cx="${sx(0.5)}" cy="${sy(1)}" r="3.6" class="f-dot"/>`,
    `<circle cx="${sx(0)}" cy="${y0}" r="3.6" class="f-dot"/>`,
    `<circle cx="${sx(1)}" cy="${y0}" r="3.6" class="f-dot"/>`,
    tex('0', { x: x0, y: y0 + 18 }),
    tex('\\tfrac12', { x: sx(0.5), y: y0 + 20 }),
    tex('1', { x: sx(1), y: y0 + 18 }),
    tex('p', { x: sx(1) + 20, y: y0 }),
    tex('\\log 2', { x: x0 - 8, y: sy(1), anchor: 'end' }),
    tex('H_b(p)', { x: sx(0.82), y: sy(hb(0.82)) - 22 }),
  );
}
