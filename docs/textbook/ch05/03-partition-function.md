# 5.3 分配関数と Legendre 双対性

5.2 節は $\lambda$ を与えられたものとして扱い、その Gibbs 分布が制約を満たすならそれが最大化分布である、と示した。そこで分配関数 $Z(\lambda)$ が果たしたのは、重みの総和を 1 にそろえる分母という役割だけだった。本節はこの分母を主役の位置に移す。

移してみると、$\lambda$ の関数としての $Z$ に最大エントロピー問題の答えが入っていることが分かる。正確には、その対数$\psi(\lambda) = \log Z(\lambda)$ に入っている。最大値そのものが $\psi(\lambda) - \langle \lambda, c\rangle$ という閉じた式で書け（定理 5.3.3）、実行可能な分布のエントロピーはどれもこの式で上から押さえられる（定理 5.3.4）。極限をとる操作も、分布を動かして最大値を探す操作も現れない。$\psi$ と制約の値 $c$ だけから計算できる量として、最大エントロピーが手に入る。

以下、$\mathcal X$ は空でない有限アルファベット、$f_1, \dots, f_k$ はその上の特徴関数、$f(x) = \big(f_1(x), \dots, f_k(x)\big)$、$\langle \lambda, u\rangle = \sum_i \lambda_i u_i$は 5.2 節で置いた記法である。

## 対数分配関数と指数型分布族

::: definition 5.3.1 対数分配関数と指数型分布族
空でない有限アルファベット $\mathcal X$ 上の特徴関数 $f_1, \dots, f_k$ をとり、定義 5.2.1 の分配関数 $Z(\lambda)$ を使って
$$
\psi(\lambda) \;:=\; \log Z(\lambda) \qquad (\lambda \in \mathbb R^k)
$$
と定める。$\psi$ を **対数分配関数** と呼ぶ。また、$\lambda \in \mathbb R^k$ に対する$\mathcal X$ 上の関数
$$
x \;\longmapsto\; \exp\big(\langle \lambda, f(x)\rangle - \psi(\lambda)\big)
$$
を考え、$\lambda$ が $\mathbb R^k$ 全体を動くときに得られるこれらの関数の全体を、特徴関数 $f_1, \dots, f_k$ の定める **指数型分布族** と呼ぶ。
:::

::: formalized
対数分配関数 `logPartitionψ`、指数型分布族の各要素 `expFamilyDist` (`InformationTheory/Shannon/MaxEntropy/ConstrainedKKT.lean`)
:::

指数型分布族の書き方では、$\psi$ が指数の中に引き算として入っている。定義 5.2.1 のGibbs 分布は同じものを割り算で書いていた。二つは同じ分布である。

::: proposition 5.3.2
$\mathcal X$ を空でない有限アルファベット、$f_1, \dots, f_k$ をその上の特徴関数とする。任意の $\lambda \in \mathbb R^k$ と任意の $x \in \mathcal X$ に対して
$$
\exp\big(\langle \lambda, f(x)\rangle - \psi(\lambda)\big) \;=\; p^*_\lambda(x)
$$
が成り立つ。すなわち指数型分布族の各要素は Gibbs 分布であり、逆にどの Gibbs 分布も指数型分布族に属する。
:::

::: proof
指数関数の値はつねに正で $\mathcal X$ は空でないから、定義 5.2.1 の $Z(\lambda)$ は正の数の有限和として正である。よってその対数がとれて$\exp\big(\psi(\lambda)\big) = Z(\lambda)$ である。指数関数が差を商に変えることから
$$
\exp\big(\langle \lambda, f(x)\rangle - \psi(\lambda)\big)
  \;=\; \frac{\exp\big(\langle \lambda, f(x)\rangle\big)}{\exp\big(\psi(\lambda)\big)}
  \;=\; \frac{\exp\big(\langle \lambda, f(x)\rangle\big)}{Z(\lambda)}
$$
となり、右端は定義 5.2.1 の $p^*_\lambda(x)$ そのものである。後半は、$\lambda$ の動く範囲が両側とも $\mathbb R^k$ 全体だから、前半の等式から直ちに従う。
:::

::: formalized
`expFamilyDist_eq_gibbsPmf` (`InformationTheory/Shannon/MaxEntropy/ConstrainedKKT.lean`)
:::

**二つの書き方を使い分ける.** 同じ分布に二つの書き方を用意する理由は、それぞれが別のことを見やすくするところにある。割り算の形は、分子が各点の重み・分母がその総和だから、これが分布であること、すなわち非負で総和が 1 であることが目で見える。命題 5.2.2 の証明が1 行で済んだのはこの形のおかげである。引き算の形は $\psi$ を式の表に出す。両辺の対数をとると
$$
\log p^*_\lambda(x) \;=\; \langle \lambda, f(x)\rangle \;-\; \psi(\lambda)
$$
となって、$\lambda$ に依る部分が $\psi(\lambda)$ という 1 つの数にまとまる。補題 5.2.3の証明が最初にしたのもこの変形だった。本節はこの $\psi$ を追う。

## Legendre 双対性

::: theorem 5.3.3 Legendre 双対性
$\mathcal X$ を空でない有限アルファベットとし、特徴関数 $f_1, \dots, f_k$ と制約の値$c = (c_1, \dots, c_k)$、および $\lambda \in \mathbb R^k$ をとる。Gibbs 分布$p^*_\lambda$ がモーメント制約を満たすとする。このとき
$$
H\big(p^*_\lambda\big) \;=\; \psi(\lambda) \;-\; \langle \lambda, c\rangle .
$$
:::

::: proof
補題 5.2.3 を $Q := p^*_\lambda$ として使う。左辺は $D(p^*_\lambda \,\|\, p^*_\lambda)$であり、定理 1.6.1 の等号条件よりこれは 0 である。右辺に現れる$\mathbb E_{p^*_\lambda}[f]$ は、仮定より $c$ に等しい。したがって
$$
0 \;=\; -H\big(p^*_\lambda\big) \;-\; \langle \lambda, c\rangle \;+\; \log Z(\lambda)
$$
が成り立つ。定義 5.3.1 より $\log Z(\lambda) = \psi(\lambda)$ だから、移項すれば主張を得る。
:::

::: formalized
`entropy_expFamilyDist_eq_legendre` (`InformationTheory/Shannon/MaxEntropy/ConstrainedKKT.lean`)
:::

::: formalization-note
形式化では、$\lambda$ とそれが制約を満たすという証拠を 1 つの対にまとめた`KKTSolution` (`InformationTheory/Shannon/MaxEntropy/ConstrainedKKT.lean`) を仮定に置いている。本文の「Gibbs 分布 $p^*_\lambda$ がモーメント制約を満たすとする」と同じ内容である。
:::

**最大値が計算できる形になった.** 定理 5.2.5 は最大値が $H(p^*_\lambda)$ だと言ったが、その数を知るには $p^*_\lambda$ を各点で書き出して $-\sum_x p\log p$ を足し上げる必要があった。定理 5.3.3 はその手間を消す。$\psi(\lambda)$ を 1 回計算して$\langle \lambda, c\rangle$ を引けばよい。$\mathcal X$ 上の和は $\psi$ の中に 1 度だけ現れる。制約の値 $c$ が結果にどう効くかも、この式なら $-\langle \lambda, c\rangle$ という 1 次の項として見える。

証明が使ったのは補題 5.2.3 を 1 回だけである。しかも代入したのは $Q = p^*_\lambda$、すなわち基準に自分自身を入れただけで、隔たりが 0 になる。5.2 節が「基準を実行可能集合の中にとる」という方針から Gibbs 分布を導いたその方針が、ここで値の計算にまで届いたことになる。

## 変分上界

::: theorem 5.3.4 変分上界
$\mathcal X$ を空でない有限アルファベットとし、特徴関数 $f_1, \dots, f_k$ と制約の値$c = (c_1, \dots, c_k)$ をとる。モーメント制約を満たす任意の分布 $P$ と、任意の$\lambda \in \mathbb R^k$ に対して
$$
H(P) \;\le\; \psi(\lambda) \;-\; \langle \lambda, c\rangle .
$$
:::

::: proof
補題 5.2.3 を $Q := P$ として使うと
$$
D\big(P \,\big\|\, p^*_\lambda\big)
  \;=\; -H(P) \;-\; \big\langle \lambda, \mathbb E_P[f] \big\rangle \;+\; \log Z(\lambda)
$$
である。$P$ はモーメント制約を満たすから各 $i$ で $\mathbb E_P[f_i] = c_i$、すなわち$\langle \lambda, \mathbb E_P[f]\rangle = \langle \lambda, c\rangle$ である。定理 1.6.1 より左辺は 0 以上だから
$$
0 \;\le\; -H(P) \;-\; \langle \lambda, c\rangle \;+\; \psi(\lambda)
$$
となり、定義 5.3.1 を使って移項すれば主張を得る。
:::

::: formalization-note
定理 5.3.4 に対応する単独の宣言はない。名前の近い宣言`entropy_le_logPartition_sub_inner` (`InformationTheory/Shannon/MaxEntropy/ConstrainedKKT.lean`) は、$\lambda$ のGibbs 分布もモーメント制約を満たすという仮定を付けた形で述べられていて、本文の主張より弱い。$\lambda$ に何も仮定しない本文の形は、補題 5.2.3 の形式化と相対エントロピーの非負性 `klDivPmf_nonneg` (`InformationTheory/Shannon/CsiszarProjection.lean`) の合成で得られる。これは本文の証明がしているのと同じ組み方である。
:::

**上界が $\lambda$ ごとに 1 本ずつ立つ.** 定理 5.3.4 は $\lambda$ について何も仮定していない。$\mathbb R^k$ の点を 1 つ選ぶたびに、実行可能集合の上のエントロピー全部にかかる上界が 1 本得られる、というのがこの定理の内容である。$\lambda$ を動かせば上界の束ができる。どの 1 本も無条件に正しいので、どれを選んでも構わない。

定理 5.3.3 が言うのは、$p^*_\lambda$ が制約を満たす $\lambda$ では、その上界が実行可能な分布 1 つ（$p^*_\lambda$ 自身）のエントロピーにちょうど一致する、ということである。束の中のその 1 本は実行可能集合に触れている。定理 5.2.5 が最大値だと言った$H(p^*_\lambda)$ が、ここでは上界の束の 1 本として現れていることになる。

二つを 1 本の式にまとめられる。定理 5.3.4 はどの $\lambda$ でも実行可能な分布のエントロピーが $\psi(\lambda) - \langle \lambda, c\rangle$ 以下だと言い、定理 5.3.3 は制約を満たす $\lambda$ ではその値がちょうど達成されると言っている。だから、制約を満たす$\lambda$ が 1 つでもあれば、実行可能集合の上のエントロピーの最大値は
$$
\min_{\lambda \in \mathbb R^k} \big(\psi(\lambda) - \langle \lambda, c\rangle\big)
$$
に等しく、最小はその制約を満たす $\lambda$ で達成される。分布を動かして最大を探す問題が、$\lambda$ を動かして最小を探す問題に置き換わったことになる。制約を満たす $\lambda$ がいつ存在するのかは 5.4 節が扱う。

この掛け替えを、外の文献では Legendre 変換と呼ぶ。凸関数から、傾きを変数にとった別の関数を作る操作のことで、本節の名前（Legendre 双対性）は、その関係が最大エントロピー問題の設定でそのまま成り立っていることを指している。本書はこの呼び名を言葉として使うだけで、以降の証明はどれもこれに依存しない。

## 例で確かめる

特徴関数が 1 つで、値が記号そのものである場合を書き下しておく。サイコロの目を 0 から始まるように付け替えた一般形である。

::: example 5.3.5 線形な特徴関数と等比の形
$N \ge 0$ を整数、$\mathcal X = \{0, 1, \dots, N\}$、$k = 1$ とし、特徴関数を$f_1(x) = x$ とする。任意の $\lambda \in \mathbb R$ に対し $r := e^{\lambda}$ とおくと、Gibbs 分布は
$$
p^*_\lambda(x) \;=\; \frac{r^{\,x}}{\sum_{y=0}^{N} r^{\,y}}
\qquad (x = 0, 1, \dots, N)
$$
と書ける。とくに隣り合う 2 点の確率の比 $p^*_\lambda(x+1) / p^*_\lambda(x)$ は$x$ によらず $r$ に等しい。
:::

::: proof
$k = 1$ だから $\langle \lambda, f(x)\rangle = \lambda x$ であり、指数法則により$\exp(\lambda x) = (e^{\lambda})^{x} = r^{\,x}$ である。これを定義 5.2.1 の分子と分母に入れると $Z(\lambda) = \sum_{y=0}^{N} r^{\,y}$ となって、最初の式を得る。比については、命題 5.2.2 より $p^*_\lambda(x)$ は正だから商がとれて、$p^*_\lambda(x+1) / p^*_\lambda(x) = r^{\,x+1} / r^{\,x} = r$ である。
:::

::: formalized
`gibbsPmf_linearFeature_eq_geometric`、その特徴関数 `linearFeature` (`InformationTheory/Shannon/MaxEntropy/Constrained.lean`)
:::

::: formalization-note
形式化されているのは等比の形までで、隣り合う 2 点の確率の比についての後半に対応する宣言はない。本節の計算がその保証のすべてである。
:::

**サイコロに戻る.** 例 5.1.4 のサイコロは目を $\{1, \dots, 6\}$ と書いた。例 5.3.5 と同じ計算をこのアルファベットの上で繰り返せば、同じ等比の形が出る。5.2 節で数値を求めた$\lambda = 0.3710\ldots$ に対して比は $r = e^{\lambda} \approx 1.449$ であり、目 $1$ から目 $6$ まで確率は一定の比で増えていく。$\lambda$ が正なら比は 1 より大きく、大きい目ほど確率が大きい。$\lambda = 0$ なら比は 1 で一様分布、$\lambda$ が負なら比は 1 より小さい。最大値のほうも定理 5.3.3 で検算できる。$\psi(0.3710) - 0.3710 \times 4.5 \approx 1.614$ナットとなり、5.2 節で各点の確率から足し上げた値と一致する。

形の絞られ方を見ておきたい。$\{1, \dots, 6\}$ 上の分布は 6 個の数で書けて、総和が 1 という条件で 1 つ減る。制約が言っているのは「平均は $4.5$」という 1 つの数だけだから、それを満たす分布はまだ無数にある。それでも探す先は狭い。$\exp$ の形をした分布のうち平均が $4.5$ になるものを 1 つ見つければ、定理 5.2.5 によりそれが最大化分布だと決まるからである。測定 1 つと原則 1 つで、候補が $\lambda$ ただ 1 つで決まる族（等比の形）に絞られる。このサイコロについて、制約に整合する $\lambda$ が実際に存在することは 5.4 節で示す。

本節までの主張はすべて「その $\lambda$ の Gibbs 分布が制約を満たすなら」という条件のもとにある。$\psi$ を微分すると何が出るかを調べれば、その条件を満たす $\lambda$ がいつ存在するのかが見えてくる。それが 5.4 節である。
