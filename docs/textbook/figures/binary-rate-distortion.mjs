export default function draw({ svg, tex, path, plot, dot, axes, scaleLinear }) {
  const hb = (p) => (p <= 0 || p >= 1 ? 0 : -(p * Math.log2(p) + (1 - p) * Math.log2(1 - p)));
  const pi = 0.25;
  const R = (D) => (D < pi ? hb(pi) - hb(D) : 0);
  const W = 440;
  const H = 250;
  const sx = scaleLinear([0, 0.5], [70, W - 50]);
  const sy = scaleLinear([0, 0.9], [H - 40, 16]);
  const marks = [0, 0.05, 0.1];
  return svg({ width: W, height: H },
    axes({ sx, sy, xLabel: 'D', xTicks: [[0, '0'], [0.05, '0.05'], [0.1, '0.1'], [0.25, '\\tfrac14'], [0.5, '\\tfrac12']],
      yTicks: [[R(0), '0.811'], [R(0.05), '0.525'], [R(0.1), '0.342']] }),
    ...marks.map((d) => path(`M${sx(0)},${sy(R(d))}H${sx(d)}V${sy(0)}`, 'f-guide')),
    path(plot(R, [0, 0.5], sx, sy), 'f-curve'),
    ...marks.map((d) => dot(sx(d), sy(R(d)))),
    dot(sx(pi), sy(0)),
    tex('R(D)', { x: sx(0.17), y: sy(R(0.17)) - 22 }),
  );
}
