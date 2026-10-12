export default function draw({ svg, tex, path, plot, dot, scaleLinear }) {
  const W = 440;
  const H = 260;
  const m = { left: 96, right: 40, top: 30, bottom: 30 };
  const logZ = (l) => -l * Math.log(2) + Math.log(0.1 ** (1 - l) + 0.9 ** (1 - l));
  const sx = scaleLinear([0, 1], [m.left, W - m.right]);
  const sy = scaleLinear([-0.13, 0.015], [H - m.bottom, m.top]);
  const lStar = 1 - Math.log(0.73248 / 0.26751) / Math.log(9);
  const minVal = logZ(lStar);
  const y0 = sy(0);
  return svg({ width: W, height: H },
    path(`M${sx(0)},${y0}H${sx(1) + 8}`, 'f-axis'),
    path(`M${sx(0)},${sy(-0.13)}V${sy(0.015) - 6}`, 'f-axis'),
    path(`M${sx(lStar)},${y0}V${sy(minVal)}H${sx(0)}`, 'f-guide'),
    path(`M${sx(1)},${y0}v-4`, 'f-axis'),
    tex('1', { x: sx(1), y: y0 - 14 }),
    tex('\\lambda^*', { x: sx(lStar), y: y0 - 14 }),
    tex('0', { x: sx(0) - 9, y: y0, anchor: 'end' }),
    tex('-C^*(P,Q)', { x: sx(0) - 9, y: sy(minVal), anchor: 'end' }),
    tex('\\lambda', { x: sx(1) + 14, y: y0, anchor: 'start' }),
    path(plot(logZ, [0, 1], sx, sy), 'f-curve'),
    dot(sx(lStar), sy(minVal)),
    tex('\\log\\mathcal Z(\\lambda)', { x: sx(0.72), y: sy(-0.03) }),
  );
}
