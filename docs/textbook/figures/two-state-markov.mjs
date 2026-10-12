export default function draw({ svg, tex, circle, arrow, selfLoop }) {
  const W = 440;
  const H = 170;
  const r = 24;
  const cy = 88;
  const x0 = 150;
  const x1 = 290;
  return svg({ width: W, height: H },
    arrow(x0, cy, x1, cy, { bend: -34, trim: r + 2 }),
    arrow(x1, cy, x0, cy, { bend: -34, trim: r + 2 }),
    selfLoop(x0, cy, r, { side: 'left' }),
    selfLoop(x1, cy, r, { side: 'right' }),
    circle(x0, cy, r, 'f-node'),
    circle(x1, cy, r, 'f-node'),
    tex('0', { x: x0, y: cy }),
    tex('1', { x: x1, y: cy }),
    tex('\\alpha', { x: (x0 + x1) / 2, y: cy - 46 }),
    tex('\\beta', { x: (x0 + x1) / 2, y: cy + 46 }),
    tex('1-\\alpha', { x: x0 - r - 62, y: cy, anchor: 'end' }),
    tex('1-\\beta', { x: x1 + r + 62, y: cy, anchor: 'start' }),
  );
}
