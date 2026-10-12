export default function draw({ svg, tex, path, axes, scaleLinear }) {
  const hx = 1.0;
  const hxy = 0.4;
  const hy = 1.1;
  const hyx = 0.5;
  const top = 1.6;
  const W = 440;
  const H = 300;
  const sx = scaleLinear([0, 1.6], [70, W - 60]);
  const sy = scaleLinear([0, 1.6], [H - 40, 16]);
  const region = [[hxy, top], [hxy, hy], [hx, hyx], [top, hyx], [top, top]];
  const d = `M${region.map(([u, v]) => `${sx(u)},${sy(v)}`).join('L')}Z`;
  const edge = `M${sx(hxy)},${sy(top)}L${sx(hxy)},${sy(hy)}L${sx(hx)},${sy(hyx)}L${sx(top)},${sy(hyx)}`;
  return svg({ width: W, height: H },
    path(d, 'f-area'),
    path(edge, 'f-curve'),
    path(`M${sx(hxy)},${sy(hy)}H${sx(0)}M${sx(hx)},${sy(hyx)}V${sy(0)}M${sx(hx)},${sy(hyx)}H${sx(0)}M${sx(hxy)},${sy(hy)}V${sy(0)}`, 'f-guide'),
    axes({ sx, sy, xLabel: 'R_X', yLabel: 'R_Y',
      xTicks: [[hxy, 'H(X\\mid Y)'], [hx, 'H(X)']], yTicks: [[hyx, 'H(Y\\mid X)'], [hy, 'H(Y)']] }),
    tex('R_X + R_Y = H(X,Y)', { x: sx(0.75) + 8, y: sy(0.8) - 4, anchor: 'start', emSize: 13 }),
  );
}
