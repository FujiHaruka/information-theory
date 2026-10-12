export default function draw({ svg, tex, path, circle }) {
  const W = 440;
  const H = 268;
  const nodes = {
    '': [220, 26],
    0: [140, 90], 1: [300, 90],
    '00': [92, 154], '01': [188, 154], 10: [252, 154], 11: [348, 154],
    '010': [188, 218],
  };
  const order = ['1', '0', '11', '01', '010', '00', '10'];
  const edge = (child) => {
    const parent = child.slice(0, -1);
    const [x1, y1] = nodes[parent];
    const [x2, y2] = nodes[child];
    const bit = child.at(-1);
    const side = bit === '0' ? -1 : 1;
    return path(`M${x1},${y1}L${x2},${y2}`, 'f-edge')
      + tex(bit, { x: (x1 + x2) / 2 + side * 12, y: (y1 + y2) / 2 - 6, emSize: 13 });
  };
  const node = (s, i) => {
    const [x, y] = nodes[s];
    return circle(x, y, 17, 'f-node') + tex(s, { x, y, emSize: 13 })
      + (s === '01'
        ? tex(`s_{${i + 1}}`, { x: x + 22, y, anchor: 'start', emSize: 13 })
        : tex(`s_{${i + 1}}`, { x, y: y + 30, emSize: 13 }));
  };
  return svg({ width: W, height: H },
    ...order.map(edge),
    circle(...nodes[''], 6, 'f-hollow'),
    ...order.map(node),
  );
}
