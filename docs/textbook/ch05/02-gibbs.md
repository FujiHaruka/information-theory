# 5.2 モーメント制約と Gibbs 分布

5.1 節は最大エントロピー問題を「一様分布からの隔たりを最小にする」問題に読み替えた。だが例 5.1.4 で見たとおり、一様分布は制約を満たすとは限らない。基準を実行可能集合の中にとれれば話は早い。というのも、隔たりが 0 になる分布は基準そのものだから、隔たりの最小化とエントロピーの最大化が実行可能集合の上で同じことでありつづけるなら、基準がそのまま最大化子になるからである。その「ありつづける」ための条件を書き下してみる。

基準の候補を $p^*$ と書き、$\mathcal X$ 上の分布 $Q$ に対する隔たりを 1.6 節の定義から2 つに分けると
$$
D(Q \,\|\, p^*) \;=\; \sum_{x} Q(x)\log Q(x) \;-\; \sum_{x} Q(x)\log p^*(x)
  \;=\; -H(Q) \;-\; \sum_{x} Q(x)\log p^*(x)
$$
になる（$p^*$ が全点で正なら、この分け方はいつでもできる）。第 1 項は $Q$ のエントロピーそのものである。だから、第 2 項が**実行可能な $Q$ の上で $Q$ に依らない**なら、実行可能集合の上で「隔たりを最小にすること」と「エントロピーを最大にすること」がまた同じことになる。制約が抑えているのは $\mathbb E_Q[f_1], \dots, \mathbb E_Q[f_k]$ の値だけだから、第 2 項がこれらだけで書けていればよい。第 2 項は $Q$ による平均なので、$\log p^*(x)$ が $f_1(x), \dots, f_k(x)$ の一次式でありさえすればそうなる。すなわち定数 $\lambda_1, \dots, \lambda_k$ と $\beta$ をとって$\log p^*(x) = \sum_i \lambda_i f_i(x) - \beta$、言い換えれば
$$
p^*(x) \;\propto\; \exp\Big(\sum_{i=1}^{k} \lambda_i f_i(x)\Big)
$$
の形であればよい。基準の候補として、以下ではこの形を採る。$k$ 個の実数を並べた$\lambda = (\lambda_1, \dots, \lambda_k)$ と $u = (u_1, \dots, u_k)$ に対して$\langle \lambda, u\rangle := \sum_{i=1}^{k} \lambda_i u_i$ と書く。

## 定義

::: definition 5.2.1 分配関数と Gibbs 分布
$k$ 個の実数の組 $\lambda$、$u$ に対して$\langle\lambda, u\rangle := \sum_{i=1}^{k} \lambda_i u_i$ と書く。空でない有限アルファベット $\mathcal X$ 上の特徴関数 $f_1, \dots, f_k$ と$\lambda \in \mathbb R^k$ に対し、$f(x) := \big(f_1(x), \dots, f_k(x)\big)$ とおいて
$$
Z(\lambda) \;:=\; \sum_{y \in \mathcal X} \exp\big(\langle \lambda, f(y)\rangle\big),
\qquad
p^*_\lambda(x) \;:=\;
  \frac{\exp\big(\langle \lambda, f(x)\rangle\big)}{Z(\lambda)}
$$
と定める。$Z(\lambda)$ を **分配関数**、$p^*_\lambda$ を **Gibbs 分布** と呼ぶ。
:::

::: formalized
分配関数 `gibbsZ`、Gibbs 分布 `gibbsPmf` (`InformationTheory/Shannon/MaxEntropy/Constrained.lean`)
:::

Gibbs 分布は、特徴関数の値の一次結合を $\exp$ に通したものを重みにして、総和が 1 になるように割ったものである。$\lambda_i$ が正なら $f_i$ の値が大きい記号ほど重みが大きく、負なら逆になる。$\lambda$ が零ベクトルなら重みはすべて 1 で、$p^*_0$ は一様分布である。分配関数はいまのところ割り算の分母でしかない。ただし $\lambda$ の関数として見ると分布の性質を抱え込んでいて、5.3 節でそれが表に出る。

$\lambda$ の成分の呼び名も決めておく。制約つき最大化を Lagrange の乗数法という古典的な手法で解くと、制約 1 本ごとに乗数という補助の変数が 1 つ現れる。$\lambda$ の成分はその乗数にあたるので、**Lagrange 乗数** と呼ぶ。本書は乗数法を使わないので、名前を借りるだけで、以降の証明はどれもこれに依存しない。

ここで念を押しておきたいのは、**$\lambda$ が制約から決まっているわけではない**ことである。定義 5.2.1 はどんな $\lambda \in \mathbb R^k$ に対しても分布を 1 つ作るだけで、その分布がモーメント制約を満たすかどうかは何も言っていない。以下の主張はすべて「その $\lambda$ の Gibbs 分布が制約を満たすならば」という条件のもとで述べる。与えられた制約の値 $c$ に対してそのような $\lambda$ が存在するかどうかは別の問題であり、5.4 節の主題である。

::: proposition 5.2.2
$\mathcal X$ を空でない有限アルファベット、$f_1, \dots, f_k$ をその上の特徴関数とする。任意の $\lambda \in \mathbb R^k$ に対し、$p^*_\lambda$ は $\mathcal X$ 上の分布であり、すべての $x \in \mathcal X$ で $p^*_\lambda(x) > 0$ である。
:::

::: proof
指数関数の値はつねに正だから、$Z(\lambda)$ は正の数の有限和である。$\mathcal X$ は空でないので項が少なくとも 1 つあり、$Z(\lambda) > 0$ が従う。よって $p^*_\lambda(x)$ は正の数どうしの商で、正である。総和は
$$
\sum_{x} p^*_\lambda(x)
  \;=\; \frac{1}{Z(\lambda)} \sum_{x} \exp\big(\langle \lambda, f(x)\rangle\big)
  \;=\; \frac{Z(\lambda)}{Z(\lambda)} \;=\; 1
$$
である。
:::

::: formalized
全点で正であること `gibbsPmf_pos`、分布であること `gibbsPmf_mem_stdSimplex` (`InformationTheory/Shannon/MaxEntropy/Constrained.lean`)
:::

全点で正であることは、このあと繰り返し効く。1.6 節で見たとおり、基準の分布が 0 をとる点で比べる分布が正の値をとると相対エントロピーは $+\infty$ になる。$p^*_\lambda$ を基準にとるかぎりそれは起きず、$D(Q \,\|\, p^*_\lambda)$ はどんな $Q$ に対しても有限である。

## 隔たりを分解する

::: lemma 5.2.3 Gibbs 分布への隔たりの分解
$\mathcal X$ を空でない有限アルファベット、$f_1, \dots, f_k$ をその上の特徴関数とし、$\lambda \in \mathbb R^k$ をとる。$\mathcal X$ 上の任意の分布 $Q$ に対して
$$
D\big(Q \,\big\|\, p^*_\lambda\big)
  \;=\; -H(Q) \;-\; \big\langle \lambda,\, \mathbb E_Q[f] \big\rangle
  \;+\; \log Z(\lambda)
$$
が成り立つ。ここで特徴関数の平均を並べたものを
$$
\mathbb E_Q[f] \;:=\; \big(\mathbb E_Q[f_1], \dots, \mathbb E_Q[f_k]\big)
$$
と書いた。$Q$ がモーメント制約を満たすことは仮定しない。
:::

::: proof
命題 5.2.2 より $p^*_\lambda$ は全点で正だから、その対数がとれて
$$
\log p^*_\lambda(x) \;=\; \big\langle \lambda, f(x) \big\rangle \;-\; \log Z(\lambda)
$$
である（商の対数を差に開き、$\log \exp t = t$ を使った。自然対数をとったのはこの一行のためである）。これを 1.6 節の定義に代入する。$p^*_\lambda$ が全点で正だからどの項も有限で、和を 2 つに分けてよい：
$$
D\big(Q \,\big\|\, p^*_\lambda\big)
  \;=\; \sum_{x} Q(x)\log Q(x) \;-\; \sum_{x} Q(x)\log p^*_\lambda(x).
$$
第 1 の和は定義 1.1.1 より $-H(Q)$ である。第 2 の和に上の式を入れると
$$
\sum_{x} Q(x)\Big(\big\langle \lambda, f(x)\big\rangle - \log Z(\lambda)\Big)
  \;=\; \sum_{i=1}^{k} \lambda_i \sum_{x} Q(x) f_i(x)
    \;-\; \log Z(\lambda) \sum_{x} Q(x)
$$
となり、$\sum_x Q(x) f_i(x) = \mathbb E_Q[f_i]$ と $\sum_x Q(x) = 1$ より、これは$\langle \lambda, \mathbb E_Q[f]\rangle - \log Z(\lambda)$ に等しい。差をとれば主張の式を得る。
:::

::: formalized
`klDivPmf_gibbsPmf_eq` (`InformationTheory/Shannon/MaxEntropy/Constrained.lean`)
:::

**3 つの項を見分ける.** 右辺の 3 項のうち、$\log Z(\lambda)$ は $Q$ に依らない。$\langle \lambda, \mathbb E_Q[f]\rangle$ は $Q$ に依るが、その依り方が制約の値だけを通っている。というのも、$Q$ が実行可能なら $\mathbb E_Q[f_i] = c_i$ となり、この項は$\langle \lambda, c\rangle$ という定数になるからである。$Q$ に本当に依るのは $-H(Q)$ ただ一つである。つまり実行可能な $Q$ の上では
$$
D\big(Q \,\big\|\, p^*_\lambda\big)
  \;=\; -H(Q) \;+\; \big(\log Z(\lambda) - \langle \lambda, c\rangle\big)
$$
であり、括弧の中は $Q$ に依らない。エントロピーが大きい分布ほど $p^*_\lambda$ に近い、ということである。これは命題 5.1.2 とまったく同じ形をしている。実際、$k = 0$ ととれば $Z(\lambda) = |\mathcal X|$、$p^*_\lambda$ は一様分布で、補題 5.2.3 は命題 5.1.2そのものになる。基準を一様分布から Gibbs 分布に取り替えても読み替えが生き延びる、というのが補題 5.2.3 の内容である。

::: corollary 5.2.4
$\mathcal X$ を空でない有限アルファベット、$f_1, \dots, f_k$ を特徴関数、$c_1, \dots, c_k$ を制約の値とし、$\lambda \in \mathbb R^k$ をとる。$\mathcal X$ 上の分布 $P$ と Gibbs 分布 $p^*_\lambda$ がともにモーメント制約を満たすならば
$$
H\big(p^*_\lambda\big) - H(P) \;=\; D\big(P \,\big\|\, p^*_\lambda\big).
$$
:::

::: proof
補題 5.2.3 を $Q := P$ と $Q := p^*_\lambda$ の 2 度使う。どちらも実行可能だから$\langle \lambda, \mathbb E_Q[f]\rangle$ はどちらの場合も $\langle \lambda, c\rangle$ に等しく、
$$
D\big(P \,\big\|\, p^*_\lambda\big)
  = -H(P) - \langle \lambda, c\rangle + \log Z(\lambda),
\qquad
D\big(p^*_\lambda \,\big\|\, p^*_\lambda\big)
  = -H\big(p^*_\lambda\big) - \langle \lambda, c\rangle + \log Z(\lambda)
$$
となる。定理 1.6.1 の等号条件より$D\big(p^*_\lambda \,\|\, p^*_\lambda\big) = 0$ である。2 つの式の差をとると$\langle \lambda, c\rangle$ と $\log Z(\lambda)$ が消えて、$D(P \,\|\, p^*_\lambda) = H(p^*_\lambda) - H(P)$ を得る。
:::

::: formalization-note
系 5.2.4 に対応する単独の宣言はない。補題 5.2.3 の形式化を $Q = P$ と$Q = p^*_\lambda$ の 2 度使い、自分自身への相対エントロピーが 0 であることと組んだ合成で得られる。その合成は、定理 5.2.5 と定理 5.2.6 が紐付ける宣言の証明の中にある。
:::

**ふたつとも実行可能なら、差がそのまま隔たりになる.** これが本節の重心である。$p^*_\lambda$ 自身も制約を満たしているとき、$p^*_\lambda$ が実行可能な $P$ をどれだけ上回るかは、$P$ が $p^*_\lambda$ からどれだけ離れているかにちょうど等しい。この形からは、最大性も一意性も、隔たりの性質を読むだけで出てくる。

## 最大エントロピー定理

::: theorem 5.2.5 最大エントロピー定理
$\mathcal X$ を空でない有限アルファベットとし、特徴関数 $f_1, \dots, f_k$ と制約の値$c_1, \dots, c_k$、および $\lambda \in \mathbb R^k$ をとる。Gibbs 分布 $p^*_\lambda$ がモーメント制約を満たすとする。このとき、モーメント制約を満たす任意の分布 $P$ に対して
$$
H(P) \;\le\; H\big(p^*_\lambda\big).
$$
:::

::: proof
系 5.2.4 より $H(p^*_\lambda) - H(P) = D(P \,\|\, p^*_\lambda)$ であり、定理 1.6.1 より右辺は 0 以上である。
:::

::: formalized
`entropy_le_gibbs_of_constraints` (`InformationTheory/Shannon/MaxEntropy/Constrained.lean`)
:::

::: theorem 5.2.6
$\mathcal X$ を空でない有限アルファベットとし、特徴関数 $f_1, \dots, f_k$ と制約の値$c_1, \dots, c_k$、および $\lambda \in \mathbb R^k$ をとる。Gibbs 分布 $p^*_\lambda$ がモーメント制約を満たすとする。このとき、モーメント制約を満たす任意の分布 $P$ について、$H(P) = H\big(p^*_\lambda\big)$ であることと $P = p^*_\lambda$ であることは同値である。
:::

::: proof
系 5.2.4 より $H(p^*_\lambda) - H(P) = D(P \,\|\, p^*_\lambda)$ だから、$H(P) = H(p^*_\lambda)$ であることは $D(P \,\|\, p^*_\lambda) = 0$ であることと同じである。定理 1.6.1 の等号条件により、それが起きるのは $P = p^*_\lambda$ のとき、かつそのときに限る。
:::

::: formalized
`entropy_eq_gibbs_iff_of_constraints` (`InformationTheory/Shannon/MaxEntropy/Constrained.lean`)
:::

**定理 1.6.1 だけで閉じている.** 二つの定理が使ったのは、定理 1.6.1（相対エントロピーの非負性とその等号条件）ただ一つである。凸性も、Lagrange の乗数法も、微分も出てこない。補題 5.2.3 が代数だけで隔たりとエントロピーを結んでしまい、あとは 1.6 節の不等式を当てるだけだからである。制約の個数 $k$ にも、特徴関数の形にも、条件は要らない。

**仮定は「$\lambda$ が制約を満たすこと」である.** 二つの定理はどちらも、与えられた$\lambda$ の Gibbs 分布が制約を満たすことを仮定している。これは結論ではなく仮定であり、そのような $\lambda$ が存在するとは主張していない。制約の値を勝手に決めれば、どんな$\lambda$ をとっても $p^*_\lambda$ がそれに合わないことがある。たとえば例 5.1.4 のサイコロで$c_1 = 7$ とすればそもそも実行可能な分布が 1 つもないし、$c_1 = 6$ とすれば実行可能な分布はある（目 $6$ に確率 $1$）のに、どの $\lambda$ の Gibbs 分布もそれには合わない。後者がなぜ起きるか、そして $\lambda$ が存在するのはどういうときでいくつあるのかは、5.4 節で扱う。

## 例で確かめる

::: example 5.2.7 制約が空のとき
$k = 0$、すなわち制約を何も課さないとする（特徴関数がすべて恒等的に 0 で、制約の値もすべて 0 なら同じことである）。このとき $\lambda$ が何であっても$Z(\lambda) = |\mathcal X|$ であり、$p^*_\lambda$ は一様分布で$H\big(p^*_\lambda\big) = \log|\mathcal X|$ である。すべての分布が実行可能だから、定理 5.2.5 が与えるのは「$\mathcal X$ 上の任意の分布 $P$ について$H(P) \le \log|\mathcal X|$」という主張になる。また、$k$ がいくつであっても、$\lambda$ が零ベクトルなら $p^*_\lambda$ は一様分布である。
:::

::: proof
$k = 0$ なら $\langle \lambda, f(x)\rangle$ は空の和で 0 である（特徴関数がすべて恒等的に0 なら、和の各項が 0 で同じく 0 になる）。$\exp 0 = 1$ だから $Z(\lambda)$ は 1 を$|\mathcal X|$ 個足したもの、すなわち $|\mathcal X|$ である。よって$p^*_\lambda(x) = 1/|\mathcal X|$ となり、例 1.1.3 よりそのエントロピーは$\log|\mathcal X|$ である。制約が 0 個ならモーメント制約は条件を何も課さないので、実行可能集合は $\mathcal X$ 上の分布全体である。

最後の主張も同じ 1 行から出る。$\lambda$ が零ベクトルなら、$k$ が何であっても各項$\lambda_i f_i(x)$ が 0 で $\langle \lambda, f(x)\rangle = 0$ となり、あとは上とまったく同じである。
:::

::: formalized
一様分布になること `gibbsPmf_zero_eq_uniform`、そのエントロピー`entropy_gibbsPmf_zero_eq_log_card` (`InformationTheory/Shannon/MaxEntropy/Constrained.lean`)
:::

例 5.2.7 が返してきたのは定理 1.1.5 そのものである。制約がないときの最大エントロピー分布は一様分布で、値は $\log|\mathcal X|$ である。第1章が $\varphi$ の狭義凹性から帰納法で示したことが、本節の一般論の $k = 0$ の場合として落ちてくる。

::: formalization-note
定理 1.1.5 の形式化は確率変数の像測度に対して述べられており、本節が紐付けた宣言はアルファベット上の関数としての分布に対して述べられている。値はどちらも$\log|\mathcal X|$ で一致するが、単独の宣言としては別のものである。
:::

::: example 5.2.8 二値アルファベットと平均の制約
$\mathcal X = \{0, 1\}$、$k = 1$、$f_1(x) = x$ とし、制約の値を $\mu \in (0,1)$ とする。$\lambda \in \mathbb R$ の Gibbs 分布がこの制約を満たすならば$p^*_\lambda(1) = \mu$、$p^*_\lambda(0) = 1 - \mu$ であり、
$$
H\big(p^*_\lambda\big) \;=\; H_b(\mu)
$$
である（$H_b$ は例 1.1.2 の二値エントロピー）。しかも、そのような $\lambda$ は実際に存在する。$\log\dfrac{\mu}{1-\mu}$ がそれである。
:::

::: proof
$f_1$ は $x = 1$ で 1、$x = 0$ で 0 をとるから$\mathbb E_{p^*_\lambda}[f_1] = p^*_\lambda(1)$ である。制約はこれが $\mu$ に等しいと言っているので $p^*_\lambda(1) = \mu$ であり、総和が 1 であることから$p^*_\lambda(0) = 1 - \mu$ となる。定義 1.1.1 よりそのエントロピーは$-\mu\log\mu - (1-\mu)\log(1-\mu)$、すなわち $H_b(\mu)$ である。

後半を確かめる。$\lambda := \log\frac{\mu}{1-\mu}$ とおくと$\exp(\lambda \cdot 1) = \mu/(1-\mu)$、$\exp(\lambda \cdot 0) = 1$ だから
$$
Z(\lambda) \;=\; 1 + \frac{\mu}{1-\mu} \;=\; \frac{1}{1-\mu},
\qquad
p^*_\lambda(1) \;=\; \frac{\mu/(1-\mu)}{1/(1-\mu)} \;=\; \mu
$$
であり、$\mathbb E_{p^*_\lambda}[f_1] = \mu$ が成り立つ。
:::

::: formalized
制約を満たす $\lambda$ のもとで $p^*_\lambda(1) = \mu$ となること`gibbsPmf_bool_true_eq_of_mean`、$p^*_\lambda(0) = 1 - \mu$ となること`gibbsPmf_bool_false_eq_of_mean`、エントロピーが二値エントロピーに等しいこと`entropy_gibbsPmf_bool_eq_binEntropy`、その特徴関数 `boolFeature` (`InformationTheory/Shannon/MaxEntropy/Constrained.lean`)
:::

::: formalization-note
形式化されているのは例 5.2.8 の前半、すなわち制約を満たす $\lambda$ が与えられたときのエントロピーの値までである。$\lambda = \log\frac{\mu}{1-\mu}$ がその制約を満たすという後半に対応する宣言はない。
:::

二値の場合、平均の制約は分布そのものを決めてしまう（$P(1) = \mu$ で$P(0) = 1-\mu$）。実行可能集合が 1 点なので、最大化としては何も言っていないに等しい。それでもこの例を見ておく価値は二つある。Gibbs 分布の形が「制約から決まる分布」をきちんと再現していること、そして $\lambda$ を制約から解く作業がどんなものかが、いちばん小さい場合に見えることである。$\mu = 0.9$ なら $\lambda = \log 9 \approx 2.197$で、そのときのエントロピーは $H_b(0.9) \approx 0.325$ ナット（$\approx 0.469$ ビット）、公平なコインの $\log 2 \approx 0.693$ ナット（1 ビット）よりずっと小さい。

**サイコロに戻る.** 例 5.1.4 の問題に定理 5.2.5 を当てる。$\mathcal X = \{1, \dots, 6\}$、$f_1(x) = x$、$c_1 = 4.5$ だから、Gibbs 分布は
$$
p^*_\lambda(x) \;=\; \frac{e^{\lambda x}}{\sum_{y=1}^{6} e^{\lambda y}}
$$
である。例 5.2.7 のとおり $\lambda = 0$ なら一様分布で、そのとき平均は $3.5$ である。$\lambda$ が正なら大きい目ほど重みが大きい。制約$\mathbb E_{p^*_\lambda}[f_1] = 4.5$ をちょうど満たす $\lambda$ があるとすれば、それは数値では $\lambda = 0.3710\ldots$ であり、そのとき目 $1$ から目 $6$ までの確率は
$$
p^*_\lambda \;\approx\;
  (0.0544,\; 0.0788,\; 0.1142,\; 0.1654,\; 0.2398,\; 0.3475)
$$
となる。この $\lambda$ に定理 5.2.5 を当てると、目の平均が $4.5$ である分布のエントロピーは $H\big(p^*_\lambda\big) \approx 1.614$ ナット（$\approx 2.328$ ビット）を超えない。定理 5.2.6 を当てれば、この値に達するのはこの分布だけである。例 5.1.4 で見た上限 $\log 6 \approx 1.792$ ナット（$\approx 2.585$ ビット）と比べると、平均を 1 つ測ったことで約 $0.18$ ナット（約 $0.26$ ビット）ぶんの不確かさが減ったことになる。

この $\lambda$ は数値で求めた。本節までの議論は、制約に合う $\lambda$ が存在するのか、あるとして 1 つに決まるのかを、何も言っていない。それを扱うのが 5.4 節である。
