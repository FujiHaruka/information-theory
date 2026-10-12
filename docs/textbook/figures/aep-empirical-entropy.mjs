export default function draw({ svg, tex, path, scaleLinear }) {
  const W = 440;
  const H = 330;
  const m = { left: 56, right: 30, top: 30, bottom: 44 };
  const p1 = 0.9;
  const hHat = (n, k) => -(k / n) * Math.log2(p1) - (1 - k / n) * Math.log2(1 - p1);
  const logChoose = (n, k) => {
    let s = 0;
    for (let i = 1; i <= k; i++) s += Math.log(n - k + i) - Math.log(i);
    return s;
  };
  const prob = (n, k) => Math.exp(logChoose(n, k) + k * Math.log(p1) + (n - k) * Math.log(1 - p1));
  const entropy = -p1 * Math.log2(p1) - (1 - p1) * Math.log2(1 - p1);
  const sx = scaleLinear([0, 3.4], [m.left, W - m.right]);
  const panelH = (H - m.top - m.bottom - 30) / 2;
  const panel = (n, top) => {
    const base = top + panelH;
    const sy = scaleLinear([0, 0.4], [base, top]);
    const stems = Array.from({ length: n + 1 }, (_, k) => {
      const x = sx(hHat(n, k)).toFixed(2);
      return path(`M${x},${base}V${sy(prob(n, k)).toFixed(2)}`, 'f-stem');
    });
    return [
      path(`M${m.left},${base}H${W - m.right + 8}`, 'f-axis'),
      path(`M${m.left},${base}V${top - 6}`, 'f-axis'),
      path(`M${m.left},${sy(0.4)}h-4`, 'f-axis'),
      tex('0.4', { x: m.left - 9, y: sy(0.4), anchor: 'end', emSize: 13 }),
      path(`M${sx(entropy)},${base}V${top - 4}`, 'f-guide'),
      ...stems,
      tex(`n = ${n}`, { x: W - m.right, y: top + 8, anchor: 'end' }),
    ];
  };
  const bottom = H - m.bottom;
  return svg({ width: W, height: H },
    panel(10, m.top),
    panel(100, m.top + panelH + 30),
    path(`M${sx(entropy)},${bottom}v4`, 'f-axis'),
    tex('H(X)', { x: sx(entropy), y: bottom + 18 }),
    ...[1, 2, 3].map((v) => path(`M${sx(v)},${bottom}v4`, 'f-axis') + tex(String(v), { x: sx(v), y: bottom + 18 })),
    tex('\\hat H_n', { x: W - m.right + 14, y: bottom, anchor: 'start' }),
  );
}
