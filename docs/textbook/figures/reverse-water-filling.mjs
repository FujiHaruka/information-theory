export default function draw({ svg, tex, rect, path }) {
  const W = 440;
  const H = 230;
  const base = 200;
  const unit = 40;
  const sigma2 = [1, 4];
  const panel = (left, D, nu) => {
    const w = 70;
    const out = [];
    sigma2.forEach((s, i) => {
      const x = left + i * w;
      const water = Math.min(nu, s);
      out.push(rect(x, base - water * unit, w, water * unit, 'f-node'));
      out.push(path(`M${x},${base}V${base - s * unit}H${x + w}V${base}`, 'f-box'));
      out.push(tex(`\\sigma_${i + 1}^2 = ${s}`, { x: x + w / 2, y: base - s * unit - 12, emSize: 12 }));
    });
    out.push(path(`M${left - 8},${base - nu * unit}H${left + 2 * w + 8}`, 'f-guide'));
    out.push(tex(`\\nu = ${nu === 0.5 ? '\\tfrac12' : nu}`, { x: left - 12, y: base - nu * unit, anchor: 'end', emSize: 13 }));
    out.push(path(`M${left},${base}H${left + 2 * w}`, 'f-axis'));
    out.push(tex(`D = ${D}`, { x: left + w, y: base + 18, emSize: 13 }));
    return out;
  };
  return svg({ width: W, height: H }, ...panel(70, 1, 0.5), ...panel(290, 3, 2));
}
