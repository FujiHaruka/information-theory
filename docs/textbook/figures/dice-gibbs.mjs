export default function draw({ svg, tex, rect, path, axes, scaleLinear }) {
  const faces = [1, 2, 3, 4, 5, 6];
  const gibbs = (lam) => {
    const w = faces.map((x) => Math.exp(lam * x));
    const z = w.reduce((a, b) => a + b, 0);
    return w.map((v) => v / z);
  };
  const mean = (p) => p.reduce((a, v, i) => a + v * faces[i], 0);
  let [lo, hi] = [0, 2];
  for (let i = 0; i < 80; i++) [lo, hi] = mean(gibbs((lo + hi) / 2)) < 4.5 ? [(lo + hi) / 2, hi] : [lo, (lo + hi) / 2];
  const p = gibbs(lo);

  const W = 440;
  const H = 240;
  const sx = scaleLinear([0.4, 6.6], [60, W - 40]);
  const sy = scaleLinear([0, 0.38], [H - 40, 16]);
  return svg({ width: W, height: H },
    ...p.map((v, i) => rect(sx(faces[i]) - 18, sy(v), 36, sy(0) - sy(v), 'f-node')),
    path(`M${sx(0.5)},${sy(1 / 6)}H${sx(6.5)}`, 'f-guide'),
    axes({ sx, sy, xTicks: faces.map((x) => [x, String(x)]), yTicks: [[1 / 6, '\\tfrac16']] }),
  );
}
