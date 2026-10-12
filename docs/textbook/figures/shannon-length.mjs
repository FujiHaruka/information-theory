export default function draw({ svg, tex, path, plot, dot, axes, scaleLinear }) {
  const W = 440;
  const H = 280;
  const m = { left: 52, right: 40, top: 40, bottom: 44 };
  const pMin = 1 / 24;
  const sx = scaleLinear([0, 1], [m.left, W - m.right]);
  const sy = scaleLinear([0, 5.4], [H - m.bottom, m.top]);
  const ideal = (p) => Math.log2(1 / p);
  const steps = [1, 2, 3, 4, 5].map((k) => {
    const lo = Math.max(2 ** -k, pMin);
    const hi = 2 ** -(k - 1);
    return path(`M${sx(lo).toFixed(2)},${sy(k)}H${sx(hi).toFixed(2)}`, 'f-curve-b');
  });
  return svg({ width: W, height: H },
    axes({
      sx, sy, xLabel: 'p(x)',
      xTicks: [[0, '0'], [0.25, '\\tfrac14'], [1 / 3, '\\tfrac13'], [0.5, '\\tfrac12'], [1, '1']],
      yTicks: [[1, '1'], [2, '2'], [3, '3'], [4, '4'], [5, '5']],
    }),
    path(`M${sx(1 / 3)},${sy(0)}V${sy(2)}`, 'f-guide'),
    ...steps,
    path(plot(ideal, [pMin, 1], sx, sy), 'f-curve'),
    dot(sx(1 / 3), sy(ideal(1 / 3))),
    dot(sx(1 / 3), sy(2)),
    tex('\\ell^{\\mathrm S}(x)', { x: sx(0.62), y: sy(1) - 16 }),
    path(`M${sx(0.42)},${sy(ideal(0.42))}L${sx(0.58)},${sy(2.7)}`, 'f-leader'),
    tex('\\log_2\\frac{1}{p(x)}', { x: sx(0.58) + 4, y: sy(2.7) - 10, anchor: 'start' }),
  );
}
