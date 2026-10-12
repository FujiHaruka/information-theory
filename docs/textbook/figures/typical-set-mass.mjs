export default function draw({ svg, tex, rect, path, axes, scaleLinear }) {
  const n = 200;
  const p = 0.9;
  const eps = 0.15;
  const half = eps / (Math.log2(0.9 / 0.1));
  const logChoose = (k) => {
    let s = 0;
    for (let i = 1; i <= k; i++) s += Math.log((n - k + i) / i);
    return s;
  };
  const mass = (k) => Math.exp(logChoose(k) + k * Math.log(p) + (n - k) * Math.log(1 - p));

  const W = 440;
  const H = 260;
  const sx = scaleLinear([0.75, 1], [52, W - 40]);
  const sy = scaleLinear([0, 0.1], [H - 44, 18]);
  const bw = (sx(1) - sx(0.75)) / (0.25 * n) * 0.8;
  const bars = [];
  for (let k = Math.ceil(0.75 * n); k <= n; k++) {
    const typical = Math.abs(k / n - p) < half;
    bars.push(rect(sx(k / n) - bw / 2, sy(mass(k)), bw, sy(0) - sy(mass(k)), typical ? 'f-node' : 'f-hollow'));
  }
  return svg({ width: W, height: H },
    rect(sx(p - half), sy(0.1), sx(p + half) - sx(p - half), sy(0) - sy(0.1), 'f-area'),
    ...bars,
    axes({ sx, sy, xLabel: 'q', xTicks: [[0.75, '0.75'], [0.9, '0.9'], [1, '1']] }),
  );
}
