export default function draw({ svg, tex, path, dot, rect, axes, scaleLinear }) {
  const W = 440;
  const H = 270;
  const m = { left: 70, right: 40, top: 40, bottom: 44 };
  const hb = (p) => -(p * Math.log2(p) + (1 - p) * Math.log2(1 - p));
  const [alpha, beta] = [0.1, 0.4];
  const mu0 = beta / (alpha + beta);
  const h0 = hb(alpha / (alpha + beta));
  const rate = mu0 * hb(alpha) + (1 - mu0) * hb(beta);
  const nMax = 15;
  const sx = scaleLinear([-0.6, nMax], [m.left, W - m.right]);
  const sy = scaleLinear([0.5, 0.75], [H - m.bottom, m.top]);
  const blockAvg = (n) => (h0 + (n - 1) * rate) / n;
  const increment = (n) => (n === 0 ? h0 : rate);
  const square = (x, y) => rect(x - 4, y - 4, 8, 8, 'f-node-b');
  return svg({ width: W, height: H },
    axes({
      sx, sy, xLabel: 'n',
      xTicks: [[0, '0'], [5, '5'], [10, '10'], [15, '15']],
      yTicks: [[rate, '0.569'], [h0, '0.722']],
    }),
    path(`M${sx(0)},${sy(rate)}H${sx(nMax)}`, 'f-guide'),
    ...Array.from({ length: nMax + 1 }, (_, n) => square(sx(n), sy(increment(n)))),
    ...Array.from({ length: nMax }, (_, i) => dot(sx(i + 1), sy(blockAvg(i + 1)))),
    tex('H_n/n', { x: sx(4.2), y: sy(blockAvg(4)) - 16, anchor: 'start' }),
    tex('H(X_n \\mid X^n)', { x: sx(9), y: sy(rate) + 18 }),
  );
}
