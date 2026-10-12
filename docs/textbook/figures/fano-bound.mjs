export default function draw({ svg, tex, path, plot, dot, axes, scaleLinear }) {
  const M = 4;
  const hb = (p) => (p <= 0 || p >= 1 ? 0 : -(p * Math.log2(p) + (1 - p) * Math.log2(1 - p)));
  const fano = (t) => hb(t) + t * Math.log2(M - 1);
  const peak = 1 - 1 / M;
  const h = 1.2;
  let [lo, hi] = [0, peak];
  for (let i = 0; i < 60; i++) [lo, hi] = fano((lo + hi) / 2) < h ? [(lo + hi) / 2, hi] : [lo, (lo + hi) / 2];
  const a = lo;

  const W = 440;
  const H = 280;
  const sx = scaleLinear([0, 1], [86, W - 40]);
  const sy = scaleLinear([0, 2.1], [H - 44, 22]);
  return svg({ width: W, height: H },
    axes({ sx, sy, xLabel: 't', xTicks: [[0, '0'], [a, 'a'], [peak, '1-1/|\\mathcal X|'], [1, '1']],
      yTicks: [[h, 'H(X\\mid Y)']] }),
    path(`M${sx(0)},${sy(h)}H${sx(a)}V${sy(0)}`, 'f-guide'),
    path(`M${sx(peak)},${sy(fano(peak))}V${sy(0)}`, 'f-guide'),
    path(plot(fano, [0, 1], sx, sy), 'f-curve'),
    dot(sx(a), sy(h)),
  );
}
