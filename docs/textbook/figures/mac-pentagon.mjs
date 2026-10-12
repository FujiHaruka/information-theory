export default function draw({ svg, tex, path, axes, scaleLinear }) {
  const hb = (p) => -(p * Math.log2(p) + (1 - p) * Math.log2(1 - p));
  const a = 17 / 20 + hb(0.05) - hb(0.1);
  const s = 17 / 40 + hb(0.475) - hb(0.1);
  const W = 440;
  const H = 300;
  const sx = scaleLinear([0, 1.05], [110, W - 60]);
  const sy = scaleLinear([0, 1.05], [H - 40, 16]);
  const pts = [[0, 0], [a, 0], [a, s - a], [s - a, a], [0, a]];
  const d = `M${pts.map(([u, v]) => `${sx(u)},${sy(v)}`).join('L')}Z`;
  return svg({ width: W, height: H },
    path(d, 'f-region-a'),
    path(`M${sx(s - 1.0)},${sy(1.0)}L${sx(1.0)},${sy(s - 1.0)}`, 'f-guide'),
    axes({ sx, sy, xLabel: 'R_1', yLabel: 'R_2',
      xTicks: [[a, 'I(X_1;Y\\mid X_2)']], yTicks: [[a, 'I(X_2;Y\\mid X_1)']] }),
    tex('R_1 + R_2 = I\\big((X_1,X_2);Y\\big)', { x: sx(s - a) + 10, y: sy(a) - 22, anchor: 'start', emSize: 13 }),
  );
}
