export default function draw({ svg, tex, path, plot, dot, scaleLinear }) {
  const W = 440;
  const H = 280;
  const sx = scaleLinear([0, 3.2], [40, W - 30]);
  const sy = scaleLinear([-2.4, 2.4], [H - 16, 16]);
  const x0 = sx(0);
  const y0 = sy(0);
  return svg({ width: W, height: H },
    path(`M${x0},${y0}H${sx(3.2) + 6}`, 'f-axis'),
    path(`M${x0},${sy(-2.4)}V${sy(2.4) - 4}`, 'f-axis'),
    path(plot((t) => t - 1, [0, 3.2], sx, sy), 'f-curve-b'),
    path(plot(Math.log, [Math.exp(-2.4), 3.2], sx, sy), 'f-curve'),
    dot(sx(1), y0),
    tex('t', { x: sx(3.2) + 18, y: y0 }),
    tex('1', { x: sx(1) + 2, y: y0 + 16 }),
    tex('0', { x: x0 - 10, y: y0 + 14 }),
    tex('(t-1)\\log e', { x: sx(2.55), y: sy(1.55) - 26 }),
    tex('\\log t', { x: sx(2.75), y: sy(Math.log(2.75)) + 22 }),
  );
}
