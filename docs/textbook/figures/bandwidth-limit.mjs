export default function draw({ svg, tex, text, path, plot, dot, axes, scaleLinear }) {
  const W = 440;
  const H = 280;
  const m = { left: 90, right: 50, top: 40, bottom: 44 };
  const sx = scaleLinear([-3.3, 2.3], [m.left, W - m.right]);
  const sy = scaleLinear([0, 1.1], [H - m.bottom, m.top]);
  const ratio = (e) => {
    const x = 10 ** e;
    return x * Math.log1p(1 / x);
  };
  const exps = [-3, -2, -1, 0, 1, 2];
  return svg({ width: W, height: H },
    axes({
      sx, sy, xLabel: 'N_0W/P',
      xTicks: exps.map((e) => [e, e === 0 ? '1' : `10^{${e}}`]),
      yTicks: [[1, '\\tfrac{P}{N_0}\\log e']],
    }),
    path(`M${sx(-3.3)},${sy(1)}H${sx(2.3)}`, 'f-guide'),
    path(plot(ratio, [-3.3, 2.3], sx, sy), 'f-curve'),
    dot(sx(-3), sy(ratio(-3))),
    dot(sx(2), sy(ratio(2))),
    text('例 8.5.5', { x: sx(-3) + 8, y: sy(ratio(-3)) - 16, anchor: 'start' }),
    text('例 8.5.6', { x: sx(2), y: sy(ratio(2)) + 20 }),
  );
}
