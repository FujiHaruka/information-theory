export default function draw({ svg, tex, path, axes, scaleLinear }) {
  const W = 440;
  const H = 260;
  const m = { left: 56, right: 30, top: 40, bottom: 44 };
  const n = 100;
  const rho = 0.1;
  const logChoose = (k) => {
    let s = 0;
    for (let i = 1; i <= k; i++) s += Math.log(n - k + i) - Math.log(i);
    return s;
  };
  const binom = (k, p) => Math.exp(logChoose(k) + k * Math.log(p) + (n - k) * Math.log(1 - p));
  const sx = scaleLinear([0, 1], [m.left, W - m.right]);
  const sy = scaleLinear([0, 0.14], [H - m.bottom, m.top]);
  const base = sy(0);
  const stems = (p, cls) => Array.from({ length: n + 1 }, (_, k) => binom(k, p))
    .map((v, k) => (v < 1e-4 ? '' : path(`M${sx(k / n).toFixed(2)},${base}V${sy(v).toFixed(2)}`, cls)));
  return svg({ width: W, height: H },
    axes({
      sx, sy, xLabel: 'k/n',
      xTicks: [[0, '0'], [rho, '\\rho'], [0.5, '\\tfrac12'], [1, '1']],
      yTicks: [[0.1, '0.1']],
    }),
    stems(rho, 'f-stem'),
    stems(0.5, 'f-stem-b'),
  );
}
