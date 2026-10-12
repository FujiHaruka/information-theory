export default function draw({ svg, tex, rect, path, text }) {
  const W = 440;
  const H = 250;
  const base = 210;
  const unit = 30;
  const N = [1, 4];
  const panel = (left, P, nu) => {
    const w = 70;
    const out = [];
    N.forEach((n, i) => {
      const x = left + i * w;
      out.push(rect(x, base - n * unit, w, n * unit, 'f-area-b'));
      if (nu > n) out.push(rect(x, base - nu * unit, w, (nu - n) * unit, 'f-node'));
      out.push(tex(`N_${i + 1} = ${n}`, { x: x + w / 2, y: base - (n * unit) / 2, emSize: 12 }));
    });
    out.push(path(`M${left - 8},${base - nu * unit}H${left + 2 * w + 8}`, 'f-guide'));
    out.push(tex(`\\nu = ${nu}`, { x: left - 12, y: base - nu * unit, anchor: 'end', emSize: 13 }));
    out.push(path(`M${left},${base}H${left + 2 * w}`, 'f-axis'));
    out.push(tex(`P = ${P}`, { x: left + w, y: base + 20, emSize: 13 }));
    return out;
  };
  return svg({ width: W, height: H }, ...panel(70, 2, 3), ...panel(290, 5, 5));
}
