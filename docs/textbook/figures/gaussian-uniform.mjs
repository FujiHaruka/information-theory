export default function draw({ svg, tex, text, path, plot, scaleLinear }) {
  const W = 440;
  const H = 260;
  const m = { left: 30, right: 30, top: 40, bottom: 44 };
  const sx = scaleLinear([-3.6, 3.6], [m.left, W - m.right]);
  const sy = scaleLinear([0, 0.45], [H - m.bottom, m.top]);
  const gauss = (x) => Math.exp(-x * x / 2) / Math.sqrt(2 * Math.PI);
  const half = Math.sqrt(3);
  const level = 1 / (2 * half);
  const y0 = sy(0);
  return svg({ width: W, height: H },
    path(`M${m.left},${y0}H${W - m.right + 8}`, 'f-axis'),
    ...[[-half, '-\\sqrt3'], [0, '0'], [half, '\\sqrt3']].map(([v, l]) => path(`M${sx(v)},${y0}v4`, 'f-axis') + tex(l, { x: sx(v), y: y0 + 18 })),
    path(`M${sx(-3.6)},${y0}H${sx(-half)}V${sy(level)}H${sx(half)}V${y0}H${sx(3.6)}`, 'f-curve-b'),
    path(plot(gauss, [-3.6, 3.6], sx, sy), 'f-curve'),
    tex('\\mathcal N(0,1)', { x: sx(0.55), y: sy(gauss(0)) - 10, anchor: 'start' }),
    text('一様分布', { x: sx(half) + 8, y: sy(level) - 12, anchor: 'start' }),
  );
}
