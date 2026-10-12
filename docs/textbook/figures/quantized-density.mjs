export default function draw({ svg, tex, path, plot, axes, scaleLinear }) {
  const f = (x) => 6 * x * (1 - x);
  const J = 8;
  const W = 440;
  const H = 240;
  const sx = scaleLinear([0, 1], [52, W - 50]);
  const sy = scaleLinear([0, 1.6], [H - 40, 16]);
  const bins = [];
  for (let i = 0; i < J; i++) {
    const [u, v] = [i / J, (i + 1) / J];
    const top = plot(f, [u, v], sx, sy, 40).replace(/^M/, 'L');
    bins.push(path(`M${sx(u)},${sy(0)}${top}L${sx(v)},${sy(0)}Z`, i % 2 ? 'f-area-b' : 'f-area'));
    bins.push(path(`M${sx(v)},${sy(0)}V${sy(f(v))}`, 'f-guide'));
  }
  return svg({ width: W, height: H },
    ...bins,
    path(plot(f, [0, 1], sx, sy), 'f-curve'),
    axes({ sx, sy, xLabel: 'x', xTicks: [[0, 'a'], [1, 'b']] }),
    path(`M${sx(3 / J)},${sy(0) + 26}H${sx(4 / J)}`, 'f-axis'),
    tex('\\delta_J', { x: sx(3.5 / J), y: sy(0) + 36, emSize: 13 }),
    tex('I_4', { x: sx(3.5 / J), y: sy(0.45), emSize: 13 }),
    tex('f', { x: sx(0.83), y: sy(f(0.83)) - 14 }),
  );
}
