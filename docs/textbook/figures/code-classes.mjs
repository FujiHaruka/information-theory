export default function draw({ svg, tex, text, rect }) {
  const W = 440;
  const H = 240;
  const ring = (x, y, w, h, label, code, codeY) => [
    rect(x, y, w, h, 'f-region-a', 10),
    text(label, { x: x + 12, y: y + 16, anchor: 'start' }),
    tex(code, { x: W / 2, y: codeY }),
  ];
  return svg({ width: W, height: H },
    ring(8, 8, W - 16, H - 16, '符号語が相異なる', 'c = \\{0,\\ 01,\\ 10\\}', H - 28),
    ring(30, 40, W - 60, H - 90, '一意復号可能', 'c = \\{0,\\ 01,\\ 011\\}', H - 70),
    ring(52, 72, W - 104, H - 168, '語頭符号', 'c = \\{0,\\ 10,\\ 110,\\ 111\\}', 120),
  );
}
