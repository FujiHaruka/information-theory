export default function draw({ svg, tex, path, circle }) {
  const W = 440;
  const H = 240;
  const y = [30, 90, 150, 210];
  const nodes = {
    root: [220, y[0], '1'],
    a: [130, y[1], '0.45'],
    b: [310, y[1], '0.55'],
    x3: [85, y[2], '0.2', '3'],
    x1: [175, y[2], '0.25', '1'],
    x2: [265, y[2], '0.25', '2'],
    c: [355, y[2], '0.3'],
    x4: [310, y[3], '0.15', '4'],
    x5: [400, y[3], '0.15', '5'],
  };
  const edges = [['root', 'a'], ['root', 'b'], ['a', 'x3'], ['a', 'x1'], ['b', 'x2'], ['b', 'c'], ['c', 'x4'], ['c', 'x5']];
  return svg({ width: W, height: H },
    ...edges.map(([u, v]) => path(`M${nodes[u][0]},${nodes[u][1]}L${nodes[v][0]},${nodes[v][1]}`, 'f-edge')),
    ...Object.values(nodes).map(([x, yy, w, sym]) => [
      circle(x, yy, sym ? 15 : 5, sym ? 'f-node' : 'f-hollow'),
      sym ? tex(sym, { x, y: yy, emSize: 14 }) : '',
      tex(w, { x: x + (sym ? 20 : 9), y: yy - (sym ? 14 : 10), anchor: 'start', emSize: 12 }),
    ]),
  );
}
