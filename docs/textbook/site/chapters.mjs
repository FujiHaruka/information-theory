// 章と節の一覧。順序 = 本の順序（目次・前後ナビ・初出術語の判定がこの順に従う）。
// build.mjs と vocab.ts の両方がここを読む（章を足す場所は 1 つだけ）。
//
// 章を足すときはこの配列に 1 要素足す。`sections` を持つ章は節ごとのページに分割して
// 出力し（`intro` を足した章だけ、その手前に章トビラが 1 枚増える）、持たない章は
// 1 章 1 ページで出力する。
export const chapters = [
  {
    slug: 'ch01',
    num: '第1章',
    title: 'エントロピー・相互情報量・データ処理不等式',
    sections: [
      { slug: 'ch01-01', num: '1.1', title: 'エントロピー', src: 'ch01/01-entropy.md' },
      { slug: 'ch01-02', num: '1.2', title: '結合エントロピー・条件付きエントロピーとチェイン則', src: 'ch01/02-joint-conditional-entropy.md' },
      { slug: 'ch01-03', num: '1.3', title: '相互情報量', src: 'ch01/03-mutual-information.md' },
      { slug: 'ch01-04', num: '1.4', title: '条件付き相互情報量', src: 'ch01/04-conditional-mutual-information.md' },
      { slug: 'ch01-05', num: '1.5', title: 'エントロピー・相互情報量のチェイン則', src: 'ch01/05-chain-rules.md' },
      { slug: 'ch01-06', num: '1.6', title: '情報不等式（Jensen と相対エントロピー）', src: 'ch01/06-information-inequality.md' },
      { slug: 'ch01-07', num: '1.7', title: '対数和不等式', src: 'ch01/07-log-sum-inequality.md' },
      { slug: 'ch01-08', num: '1.8', title: 'データ処理不等式', src: 'ch01/08-data-processing-inequality.md' },
      { slug: 'ch01-09', num: '1.9', title: '十分統計量', src: 'ch01/09-sufficient-statistics.md' },
      { slug: 'ch01-10', num: '1.10', title: 'ファノの不等式', src: 'ch01/10-fano.md' },
    ],
  },
  {
    slug: 'ch02',
    num: '第2章',
    title: '漸近等分配性とデータ圧縮',
    sections: [
      { slug: 'ch02-01', num: '2.1', title: '漸近等分配性', src: 'ch02/01-aep.md' },
      { slug: 'ch02-02', num: '2.2', title: '典型集合', src: 'ch02/02-typical-set.md' },
      { slug: 'ch02-03', num: '2.3', title: '情報源符号化定理', src: 'ch02/03-source-coding.md' },
      { slug: 'ch02-04', num: '2.4', title: '強典型性', src: 'ch02/04-strong-typicality.md' },
    ],
  },
  {
    slug: 'ch03',
    num: '第3章',
    title: '定常情報源のエントロピーレート',
    sections: [
      { slug: 'ch03-01', num: '3.1', title: '定常情報源', src: 'ch03/01-stationary.md' },
      { slug: 'ch03-02', num: '3.2', title: 'エントロピーレート', src: 'ch03/02-entropy-rate.md' },
      { slug: 'ch03-03', num: '3.3', title: 'マルコフ情報源のエントロピーレート', src: 'ch03/03-markov-rate.md' },
      { slug: 'ch03-04', num: '3.4', title: 'エルゴード性と時間平均', src: 'ch03/04-birkhoff.md' },
      { slug: 'ch03-05', num: '3.5', title: 'Shannon–McMillan–Breiman 定理', src: 'ch03/05-smb.md' },
    ],
  },
  {
    slug: 'ch04',
    num: '第4章',
    title: '符号語長と最適符号',
    sections: [
      { slug: 'ch04-01', num: '4.1', title: '符号と一意復号可能性', src: 'ch04/01-codes.md' },
      { slug: 'ch04-02', num: '4.2', title: 'Kraft の不等式', src: 'ch04/02-kraft.md' },
      { slug: 'ch04-03', num: '4.3', title: '平均符号長の下界', src: 'ch04/03-lower-bound.md' },
      { slug: 'ch04-04', num: '4.4', title: 'Shannon 符号', src: 'ch04/04-shannon-code.md' },
      { slug: 'ch04-05', num: '4.5', title: 'McMillan の不等式', src: 'ch04/05-mcmillan.md' },
      { slug: 'ch04-06', num: '4.6', title: 'Huffman 符号の最適性', src: 'ch04/06-huffman.md' },
    ],
  },
  {
    slug: 'ch06',
    num: '第6章',
    title: '通信路容量',
    sections: [
      { slug: 'ch06-01', num: '6.1', title: '通信路と通信路容量', src: 'ch06/01-capacity.md' },
      { slug: 'ch06-02', num: '6.2', title: 'ブロック通信路符号と結合典型集合', src: 'ch06/02-joint-typicality.md' },
      { slug: 'ch06-03', num: '6.3', title: 'ランダム符号化と達成可能性', src: 'ch06/03-random-coding.md' },
      { slug: 'ch06-04', num: '6.4', title: '逆定理', src: 'ch06/04-converse.md' },
      { slug: 'ch06-05', num: '6.5', title: 'フィードバックのある通信路', src: 'ch06/05-feedback.md' },
      { slug: 'ch06-06', num: '6.6', title: '強逆定理', src: 'ch06/06-strong-converse.md' },
      { slug: 'ch06-07', num: '6.7', title: '一般の通信路の容量', src: 'ch06/07-general-channel.md' },
    ],
  },
  {
    slug: 'ch10',
    num: '第10章',
    title: '最大エントロピー',
    sections: [
      { slug: 'ch10-01', num: '10.1', title: '最大エントロピー問題', src: 'ch10/01-problem.md' },
      { slug: 'ch10-02', num: '10.2', title: 'モーメント制約と Gibbs 分布', src: 'ch10/02-gibbs.md' },
      { slug: 'ch10-03', num: '10.3', title: '分配関数と Legendre 双対性', src: 'ch10/03-partition-function.md' },
      { slug: 'ch10-04', num: '10.4', title: 'Lagrange 乗数の存在', src: 'ch10/04-multiplier.md' },
    ],
  },
];
