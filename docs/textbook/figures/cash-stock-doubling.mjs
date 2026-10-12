export default function draw({ svg, tex, path, plot, dot, axes, scaleLinear }) {
  const Wb = (b) => 0.5 * Math.log2(1 + b) + 0.5 * Math.log2(1 - b / 2);
  const W = 440;
  const H = 240;
  const sx = scaleLinear([0, 1], [90, W - 60]);
  const sy = scaleLinear([0, 0.1], [H - 40, 20]);
  return svg({ width: W, height: H },
    path(`M${sx(0.5)},${sy(Wb(0.5))}V${sy(0)}M${sx(0.5)},${sy(Wb(0.5))}H${sx(0)}`, 'f-guide'),
    path(plot(Wb, [0, 1], sx, sy), 'f-curve'),
    dot(sx(0), sy(0)), dot(sx(0.5), sy(Wb(0.5))), dot(sx(1), sy(0)),
    axes({ sx, sy, xLabel: 'b(2)', xTicks: [[0, '0'], [0.5, '\\tfrac12'], [1, '1']],
      yTicks: [[Wb(0.5), '\\tfrac12\\log\\tfrac98']] }),
  );
}
