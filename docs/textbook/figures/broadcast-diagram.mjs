export default function draw({ svg, tex, block, arrow }) {
  const W = 480;
  const H = 160;
  const [y1, y2, ym] = [40, 120, 80];
  const [xc, xw, xd] = [140, 260, 400];
  const bw = 60;
  return svg({ width: W, height: H },
    arrow(14, ym, xc - bw / 2, ym), tex('(m_1,m_2)', { x: 56, y: ym - 18 }),
    block(xc, ym, 'c', { w: bw, math: true }),
    arrow(xc + bw / 2, ym, xw - bw / 2, ym), tex('x^n', { x: (xc + xw) / 2, y: ym - 14 }),
    block(xw, ym, 'W', { w: bw, h: 60, math: true }),
    arrow(xw + bw / 2, ym - 8, xd - bw / 2, y1),
    arrow(xw + bw / 2, ym + 8, xd - bw / 2, y2),
    tex('y_1^n', { x: (xw + xd) / 2 + 4, y: y1 - 4 }),
    tex('y_2^n', { x: (xw + xd) / 2 + 4, y: y2 + 4 }),
    block(xd, y1, 'd_1', { w: bw, math: true }),
    block(xd, y2, 'd_2', { w: bw, math: true }),
    arrow(xd + bw / 2, y1, W - 8, y1),
    arrow(xd + bw / 2, y2, W - 8, y2),
  );
}
