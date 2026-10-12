export default function draw({ svg, tex, block, arrow }) {
  const W = 480;
  const H = 190;
  const [yr, ym] = [44, 140];
  const [xc, xw, xd] = [110, 240, 380];
  const bw = 60;
  return svg({ width: W, height: H },
    arrow(14, ym, xc - bw / 2, ym), tex('m', { x: 30, y: ym - 14 }),
    block(xc, ym, 'c', { w: bw, math: true }),
    arrow(xc + bw / 2, ym, xw - bw / 2, ym), tex('x', { x: (xc + xw) / 2, y: ym - 14 }),
    block(xw, ym, 'W', { w: bw, h: 50, math: true }),
    arrow(xw + bw / 2, ym, xd - bw / 2, ym), tex('y', { x: (xw + xd) / 2, y: ym - 14 }),
    block(xd, ym, 'd', { w: bw, math: true }),
    arrow(xd + bw / 2, ym, W - 8, ym),
    block(xw, yr, 'r_i', { w: bw, math: true }),
    arrow(xw + 16, ym - 25, xw + 16, yr + 20),
    tex('y_1', { x: xw + 24, y: (ym - 25 + yr + 20) / 2, anchor: 'start' }),
    arrow(xw - 16, yr + 20, xw - 16, ym - 25),
    tex('x_1', { x: xw - 24, y: (ym - 25 + yr + 20) / 2, anchor: 'end' }),
  );
}
