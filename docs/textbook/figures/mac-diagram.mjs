export default function draw({ svg, tex, block, arrow }) {
  const W = 480;
  const H = 160;
  const [y1, y2, ym] = [40, 120, 80];
  const [xe, xw, xd] = [120, 280, 400];
  const bw = 60;
  return svg({ width: W, height: H },
    arrow(24, y1, xe - bw / 2, y1), tex('m_1', { x: 40, y: y1 - 14 }),
    arrow(24, y2, xe - bw / 2, y2), tex('m_2', { x: 40, y: y2 - 14 }),
    block(xe, y1, 'c_1', { w: bw, math: true }),
    block(xe, y2, 'c_2', { w: bw, math: true }),
    arrow(xe + bw / 2, y1, xw - bw / 2, ym - 8),
    arrow(xe + bw / 2, y2, xw - bw / 2, ym + 8),
    tex('x_1^n', { x: (xe + xw) / 2, y: y1 - 4 }),
    tex('x_2^n', { x: (xe + xw) / 2, y: y2 + 4 }),
    block(xw, ym, 'W', { w: bw, h: 60, math: true }),
    arrow(xw + bw / 2, ym, xd - bw / 2, ym),
    tex('y^n', { x: (xw + xd) / 2, y: ym - 14 }),
    block(xd, ym, 'd', { w: bw, math: true }),
    arrow(xd + bw / 2, ym, W - 8, ym),
  );
}
