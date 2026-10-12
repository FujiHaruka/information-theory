export default function draw({ svg, tex, path }) {
  const W = 440;
  const H = 250;
  const r = 92;
  const cy = 138;
  const c1 = W / 2 - 62;
  const c2 = W / 2 + 62;
  const circle = (cx, cls) => `<circle cx="${cx}" cy="${cy}" r="${r}" class="${cls}"/>`;

  return svg({ width: W, height: H },
    circle(c1, 'f-region-a'),
    circle(c2, 'f-region-b'),
    path(`M${c1 - 40},${cy - r + 4}L${c1 - 58},${cy - r - 10}`, 'f-leader'),
    path(`M${c2 + 40},${cy - r + 4}L${c2 + 58},${cy - r - 10}`, 'f-leader'),
    tex('H(X)', { x: c1 - 62, y: cy - r - 14, anchor: 'end' }),
    tex('H(Y)', { x: c2 + 62, y: cy - r - 14, anchor: 'start' }),
    tex('H(X\\mid Y)', { x: (c1 - r + c2 - r) / 2, y: cy }),
    tex('I(X;Y)', { x: W / 2, y: cy }),
    tex('H(Y\\mid X)', { x: (c1 + r + c2 + r) / 2, y: cy }),
  );
}
