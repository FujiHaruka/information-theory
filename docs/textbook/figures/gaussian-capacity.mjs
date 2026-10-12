export default function draw({ svg, tex, path, plot, axes, scaleLinear }) {
  const C = (s) => 0.5 * Math.log2(1 + s);
  const W = 440;
  const H = 250;
  const sx = scaleLinear([0, 30], [52, W - 60]);
  const sy = scaleLinear([0, 2.6], [H - 40, 16]);
  return svg({ width: W, height: H },
    axes({ sx, sy, xLabel: 'P/N', xTicks: [[0, '0'], [10, '10'], [20, '20'], [30, '30']],
      yTicks: [[1, '1'], [2, '2']] }),
    path(plot(C, [0, 30], sx, sy), 'f-curve'),
    tex('\\tfrac12\\log_2\\!\\big(1 + P/N\\big)', { x: sx(17), y: sy(C(17)) - 26 }),
  );
}
