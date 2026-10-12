export default function draw({ svg, tex, block, arrow }) {
  const W = 480;
  const H = 100;
  const y = 62;
  const [xc, xg] = [120, 370];
  const bw = 64;
  return svg({ width: W, height: H },
    arrow(14, y, xc - bw / 2, y),
    tex('X^n', { x: 40, y: y - 16 }),
    block(xc, y, 'c', { w: bw, math: true }),
    arrow(xc + bw / 2, y, xg - bw / 2, y),
    tex('c(X^n) \\in \\{1,\\dots,M\\}', { x: (xc + xg) / 2, y: y - 18 }),
    block(xg, y, 'g', { w: bw, math: true }),
    arrow(xg + bw / 2, y, W - 8, y),
    tex('g\\big(c(X^n)\\big)', { x: xg + bw / 2 + 6, y: y - 18, anchor: 'start' }),
  );
}
