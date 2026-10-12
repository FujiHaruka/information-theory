export default function draw({ svg, tex, path, dot, axes, scaleLinear, line }) {
  const hb = (p) => -(p * Math.log(p) + (1 - p) * Math.log(1 - p));
  const dP = (s) => s * Math.log(s / 0.1) + (1 - s) * Math.log((1 - s) / 0.9);
  const E = (s) => Math.log(2) - hb(s);
  const W = 440;
  const H = 280;
  const sx = scaleLinear([0, 0.7], [70, W - 60]);
  const sy = scaleLinear([0, 0.42], [H - 40, 40]);
  const pts = [];
  for (let i = 0; i <= 200; i++) {
    const s = 0.1 + (0.4 * i) / 200;
    pts.push([sx(dP(s)), sy(E(s))]);
  }
  pts.push([sx(0.7), sy(0)]);
  const cstar = E(0.2675);
  return svg({ width: W, height: H },
    path(`M${sx(0)},${sy(0)}L${sx(0.42)},${sy(0.42)}`, 'f-guide'),
    path(line()(pts), 'f-curve'),
    path(`M${sx(cstar)},${sy(cstar)}V${sy(0)}M${sx(cstar)},${sy(cstar)}H${sx(0)}`, 'f-guide'),
    dot(sx(cstar), sy(cstar)),
    dot(sx(0), sy(E(0.1))),
    dot(sx(dP(0.5)), sy(0)),
    axes({ sx, sy, xLabel: 't', yLabel: 'E^*(t)',
      xTicks: [[cstar, '0.112'], [dP(0.5), '0.511']], yTicks: [[E(0.1), '0.368'], [cstar, '0.112']] }),
  );
}
