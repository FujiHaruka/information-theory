export default function draw({ svg, tex, path, plot, dot, axes, scaleLinear }) {
  const W = 440;
  const H = 260;
  const m = { left: 60, right: 40, top: 40, bottom: 44 };
  const sx = scaleLinear([-6, 6], [m.left, W - m.right]);
  const sy = scaleLinear([0, 1.1], [H - m.bottom, m.top]);
  const mean = (l) => 1 / (1 + Math.exp(-l));
  return svg({ width: W, height: H },
    path(`M${sx(-6)},${sy(1)}H${sx(6)}`, 'f-guide'),
    path(`M${sx(-6)},${sy(0)}H${sx(6) + 8}`, 'f-axis'),
    path(`M${sx(0)},${sy(0)}V${sy(1.1) - 10}`, 'f-axis'),
    ...[[-4, '-4'], [4, '4']].map(([v, l]) => path(`M${sx(v)},${sy(0)}v4`, 'f-axis') + tex(l, { x: sx(v), y: sy(0) + 18 })),
    tex('0', { x: sx(0) - 9, y: sy(0) + 14, anchor: 'end' }),
    path(`M${sx(0)},${sy(1)}h-4`, 'f-axis'),
    tex('1', { x: sx(0) - 9, y: sy(1) - 8, anchor: 'end' }),
    path(`M${sx(0)},${sy(0.5)}h-4`, 'f-axis'),
    tex('\\tfrac12', { x: sx(0) - 9, y: sy(0.5), anchor: 'end' }),
    tex('\\lambda', { x: sx(6) + 14, y: sy(0), anchor: 'start' }),
    path(plot(mean, [-6, 6], sx, sy), 'f-curve'),
    tex('\\mathbb E_{p^*_\\lambda}[f_1] = \\dfrac{1}{1+e^{-\\lambda}}', { x: sx(1.2), y: sy(0.32), anchor: 'start' }),
  );
}
