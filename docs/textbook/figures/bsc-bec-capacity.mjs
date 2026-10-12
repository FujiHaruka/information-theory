export default function draw({ svg, tex, path, plot, axes, scaleLinear }) {
  const hb = (p) => (p <= 0 || p >= 1 ? 0 : -(p * Math.log2(p) + (1 - p) * Math.log2(1 - p)));
  const W = 440;
  const H = 260;
  const sx = scaleLinear([0, 1], [52, W - 50]);
  const sy = scaleLinear([0, 1], [H - 40, 20]);
  return svg({ width: W, height: H },
    axes({ sx, sy, xTicks: [[0, '0'], [0.5, '\\tfrac12'], [1, '1']], yTicks: [[1, '1']] }),
    path(plot((t) => 1 - t, [0, 1], sx, sy), 'f-curve-b'),
    path(plot((t) => 1 - hb(t), [0, 1], sx, sy), 'f-curve'),
    tex('\\rho,\\ \\eta', { x: sx(1) + 14, y: sy(0), anchor: 'start' }),
    tex('1-\\eta', { x: sx(0.62), y: sy(0.38) - 24 }),
    tex('1-H_b(\\rho)', { x: sx(0.5), y: sy(0.2) }),
  );
}
