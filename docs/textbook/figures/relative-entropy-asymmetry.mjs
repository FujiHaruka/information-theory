export default function draw({ svg, tex, path, plot, dot, axes, scaleLinear }) {
  const W = 440;
  const H = 280;
  const m = { left: 70, right: 64, top: 40, bottom: 44 };
  const yMax = 2.5;
  const sx = scaleLinear([0, 1], [m.left, W - m.right]);
  const sy = scaleLinear([0, yMax], [H - m.bottom, m.top]);
  const q = 0.25;
  const term = (u, v) => (u === 0 ? 0 : u * Math.log2(u / v));
  const dPQ = (a) => term(a, q) + term(1 - a, 1 - q);
  const dQP = (a) => term(q, a) + term(1 - q, 1 - a);
  const crossing = (inside, outside) => {
    let [a, b] = [inside, outside];
    for (let i = 0; i < 80; i++) {
      const mid = (a + b) / 2;
      if (dQP(mid) > yMax) b = mid; else a = mid;
    }
    return a;
  };
  const aLo = crossing(q, 0);
  const aHi = crossing(q, 1);
  return svg({ width: W, height: H },
    axes({
      sx, sy, xLabel: 'a',
      xTicks: [[0, '0'], [q, '\\tfrac14'], [1, '1']],
      yTicks: [[1, '\\log 2'], [2, '2\\log 2']],
    }),
    path(plot(dPQ, [0, 1], sx, sy), 'f-curve'),
    path(plot(dQP, [aLo, 0.02], sx, sy, 200), 'f-curve-b'),
    path(plot(dQP, [0.02, aHi], sx, sy), 'f-curve-b'),
    dot(sx(q), sy(0)),
    tex('D(p\\,\\|\\,q)', { x: sx(1) + 6, y: sy(dPQ(1)) + 4, anchor: 'start' }),
    tex('D(q\\,\\|\\,p)', { x: sx(0.03) + 8, y: sy(2.3), anchor: 'start' }),
  );
}
