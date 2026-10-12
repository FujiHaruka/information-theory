export default function draw({ svg, tex, rect, path, plot, dot, axes, scaleLinear }) {
  const hb = (p) => (p <= 0 || p >= 1 ? 0 : -(p * Math.log(p) + (1 - p) * Math.log(1 - p)));
  const D = (s) => Math.log(2) - hb(s);
  const W = 440;
  const H = 250;
  const sx = scaleLinear([0, 1], [70, W - 60]);
  const sy = scaleLinear([0, 0.75], [H - 40, 16]);
  return svg({ width: W, height: H },
    rect(sx(0.7), sy(0.75), sx(1) - sx(0.7), sy(0) - sy(0.75), 'f-area'),
    path(`M${sx(0.7)},${sy(D(0.7))}H${sx(0)}`, 'f-guide'),
    path(plot(D, [0, 1], sx, sy), 'f-curve'),
    dot(sx(0.7), sy(D(0.7))),
    axes({ sx, sy, xLabel: 'P(1)', xTicks: [[0, '0'], [0.5, '\\tfrac12'], [0.7, '0.7'], [1, '1']],
      yTicks: [[D(0.7), '0.0823'], [Math.log(2), '\\log 2']] }),
    tex('\\mathcal E', { x: sx(0.85), y: sy(0.62) }),
    tex('D(P\\,\\|\\,Q)', { x: sx(0.2), y: sy(D(0.2)) - 18, anchor: 'start' }),
  );
}
