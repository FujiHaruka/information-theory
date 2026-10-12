export default function draw({ svg, tex, path, block, arrow }) {
  const W = 480;
  const H = 160;
  const y = 60;
  const [xc, xw, xd] = [130, 260, 390];
  const bw = 64;
  const fb = 130;
  return svg({ width: W, height: H },
    arrow(24, y, xc - bw / 2, y),
    tex('m', { x: 36, y: y - 14 }),
    block(xc, y, 'c_i', { w: bw, math: true }),
    arrow(xc + bw / 2, y, xw - bw / 2, y),
    tex('x_i', { x: (xc + xw) / 2, y: y - 14 }),
    block(xw, y, 'W', { w: bw, math: true }),
    arrow(xw + bw / 2, y, xd - bw / 2, y),
    tex('y_i', { x: (xw + xd) / 2 + 12, y: y - 14 }),
    block(xd, y, 'd', { w: bw, math: true }),
    arrow(xd + bw / 2, y, W - 10, y),
    path(`M${(xw + xd) / 2},${y}V${fb}H${xc}`, 'f-arrow'),
    arrow(xc, fb, xc, y + 20),
    tex('y^{<i}', { x: (xc + xw) / 2, y: fb + 14 }),
    `<circle cx="${(xw + xd) / 2}" cy="${y}" r="2.6" class="f-arrow-head"/>`,
  );
}
