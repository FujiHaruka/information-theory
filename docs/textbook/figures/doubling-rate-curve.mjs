export default function draw({ svg, tex, path, plot, dot, axes, scaleLinear }) {
  const p = 0.8;
  const W2 = (b) => p * Math.log2(2 * b) + (1 - p) * Math.log2(2 * (1 - b));
  const W = 440;
  const H = 270;
  const sx = scaleLinear([0, 1], [70, W - 40]);
  const sy = scaleLinear([-0.6, 0.35], [H - 30, 20]);
  const y0 = sy(0);
  return svg({ width: W, height: H },
    path(`M${sx(0)},${y0}H${sx(1) + 8}`, 'f-axis'),
    path(`M${sx(0)},${sy(-0.6)}V${sy(0.35) - 6}`, 'f-axis'),
    path(`M${sx(0.8)},${sy(W2(0.8))}H${sx(0)}`, 'f-guide'),
    path(`M${sx(0.9)},${sy(W2(0.9))}H${sx(0)}`, 'f-guide'),
    path(`M${sx(0.8)},${sy(W2(0.8))}V${y0}`, 'f-guide'),
    path(`M${sx(0.9)},${sy(W2(0.9))}V${y0}`, 'f-guide'),
    path(plot(W2, [0.28, 0.99], sx, sy), 'f-curve'),
    dot(sx(0.8), sy(W2(0.8))),
    dot(sx(0.9), sy(W2(0.9))),
    tex('0', { x: sx(0) - 10, y: y0 }),
    tex('0.8', { x: sx(0.8) - 4, y: y0 + 14, emSize: 13 }),
    tex('0.9', { x: sx(0.9) + 8, y: y0 + 14, emSize: 13 }),
    tex('1', { x: sx(1), y: y0 + 14, emSize: 13 }),
    tex('b(1)', { x: sx(1) + 12, y: y0 - 14, anchor: 'start' }),
    tex('0.278', { x: sx(0) - 8, y: sy(W2(0.8)) - 6, anchor: 'end', emSize: 13 }),
    tex('0.214', { x: sx(0) - 8, y: sy(W2(0.9)) + 6, anchor: 'end', emSize: 13 }),
  );
}
