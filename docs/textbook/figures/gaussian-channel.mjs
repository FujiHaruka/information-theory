export default function draw({ svg, tex, arrow, circle, path }) {
  const W = 440;
  const H = 130;
  const cy = 88;
  const cx = 220;
  return svg({ width: W, height: H },
    arrow(80, cy, cx - 14, cy),
    arrow(cx + 14, cy, 360, cy),
    arrow(cx, 26, cx, cy - 14),
    circle(cx, cy, 14, 'f-box'),
    path(`M${cx - 8},${cy}H${cx + 8}M${cx},${cy - 8}V${cy + 8}`, 'f-axis'),
    tex('X', { x: 66, y: cy, anchor: 'end' }),
    tex('Y = X + Z', { x: 374, y: cy, anchor: 'start' }),
    tex('Z \\sim \\mathcal N(0, N)', { x: cx + 12, y: 22, anchor: 'start' }),
  );
}
