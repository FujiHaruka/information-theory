export default function draw({ svg, tex, block, arrow }) {
  const W = 480;
  const H = 150;
  const y = 50;
  const ys = 126;
  const [xc, xg] = [130, 300];
  const bw = 64;
  return svg({ width: W, height: H },
    arrow(30, y, xc - bw / 2, y),
    tex('X^n', { x: 54, y: y - 16 }),
    block(xc, y, 'c', { w: bw, math: true }),
    arrow(xc + bw / 2, y, xg - bw / 2, y),
    tex('c(X^n)', { x: (xc + xg) / 2, y: y - 16 }),
    block(xg, y, 'g', { w: bw, math: true }),
    arrow(xg + bw / 2, y, W - 8, y),
    tex('g\\big(c(X^n),\\,Y^n\\big)', { x: xg + bw / 2 + 4, y: y - 18, anchor: 'start' }),
    arrow(xg, ys, xg, y + 20),
    tex('Y^n', { x: xg + 20, y: ys - 8, anchor: 'start' }),
  );
}
