# 9.2 レート歪み関数の性質

9.1 節は $R(D)$ を，歪みを $D$ 以下に抑えるという制約のもとでの相互情報量の下限として定め，それが最小値でもあること（命題 9.1.6）まで確かめた．値の計算はまだ一つもしていない．本節では，具体的な情報源を決める前に，$D$ の関数として $R$ がどんな形をしているかを調べる．示すのは四つで，$D$ について非増加であること，凸であること，$D = 0$ での値，そして $R(D)$ が $0$ になる $D$ のうち最小のものである．どれも 9.3 節と 9.4 節で具体的な情報源のレート歪み関数を計算するときに，答え合わせに使える．記号は定義 9.1.1 と定義 9.1.5 のものをそのまま引き継ぐ．

## 歪みを多く許すほど下がる

::: proposition 9.2.1
$\mathcal X$ と $\hat{\mathcal X}$ を空でない有限集合，$p$ を $\mathcal X$ 上の分布，$d$ を歪み尺度（定義 9.1.1）とし，$\mathcal Q(\cdot)$ と $R(\cdot)$ を定義 9.1.5 のとおりとする．実数 $D_1 \le D_2$ について $\mathcal Q(D_1)$ が空でないならば，$\mathcal Q(D_1) \subseteq \mathcal Q(D_2)$ であり，$\mathcal Q(D_2)$ も空でなく
$$
R(D_2) \;\le\; R(D_1)
$$
である．
:::

::: proof
$q \in \mathcal Q(D_1)$ とすると，その期待歪みは $D_1$ 以下であり，$D_1 \le D_2$ だから $D_2$ 以下でもある．よって $q \in \mathcal Q(D_2)$ であり，包含が従う．$\mathcal Q(D_1)$ が空でないので $\mathcal Q(D_2)$ も空でなく，$R(D_2)$ が定まる．

$R(D_2)$ は値の集合 $\{I(p;q) : q \in \mathcal Q(D_2)\}$ の下界である．いま見た包含より $\{I(p;q) : q\in\mathcal Q(D_1)\}$ はその部分集合だから，$R(D_2)$ は後者の下界でもある．下限は下界のうち最大のものだから $R(D_2) \le R(D_1)$ である．
:::

読み方は素直である．歪みを多く許すほど，選べる再現の作り方は増える．増えたぶんだけ小さい値が選べるかもしれず，少なくとも大きくはならない．効いているのは制約集合の包含だけで，相互情報量の性質は一つも使っていない．

::: formalized
`rateDistortionFunction_antitone` (`InformationTheory/Shannon/RateDistortion/ConverseMonotone.lean`)
:::

::: formalization-note
`rateDistortionFunction_antitone` が述べているのは，$R(D)$ を測度の言葉で書いた宣言 `rateDistortionFunction` (`InformationTheory/Shannon/RateDistortion/Converse.lean`) についての非増加性である．定義 9.1.5 に紐付けた `rateDistortionFunctionPmf` (`InformationTheory/Shannon/RateDistortion/Achievability.lean`) とは別の宣言で，二つを結ぶ宣言は無い．あちらは値を拡張非負実数にとり，制約を満たす同時分布が一つも無いときの下限を $\infty$ と定めるので，命題 9.2.1 が置いた「$\mathcal Q(D_1)$ が空でない」という仮定を置かずに述べられている．
:::

## 凸である

凸性は制約集合の包含だけからは出ない．二つの再現の作り方を混ぜたときに相互情報量がどう動くかを知る必要があり，それを先に切り出しておく．道具は第1章 定理 1.7.1 の対数和不等式ひとつである．

::: lemma 9.2.2 条件付き分布についての相互情報量の凸性
$\mathcal X$ と $\hat{\mathcal X}$ を空でない有限集合，$p$ を $\mathcal X$ 上の分布，$q_1$ と $q_2$ を条件付き分布（定義 9.1.5），$\lambda \in [0,1]$ とする．$q_\lambda(\hat x\mid x) := \lambda\, q_1(\hat x\mid x) + (1-\lambda)\, q_2(\hat x\mid x)$ で定まる $q_\lambda$ もまた条件付き分布であり
$$
I(p;q_\lambda) \;\le\; \lambda\, I(p;q_1) + (1-\lambda)\, I(p;q_2)
$$
である．
:::

::: proof
$q_\lambda$ が条件付き分布であることは，非負の数の非負係数の和が非負であることと，各 $x$ について $\sum_{\hat x}q_\lambda(\hat x\mid x) = \lambda + (1-\lambda) = 1$ であることによる．$\lambda = 0$ と $\lambda = 1$ では両辺が一致するので，以下では $0 < \lambda < 1$ とする．

記号を用意する．$j = 1, 2, \lambda$ について，$q_j$ に対応する同時分布を $\pi_j(x,\hat x) := p(x)\,q_j(\hat x\mid x)$，その第 $2$ 周辺分布を $\hat p_j(\hat x) := \sum_{x}\pi_j(x,\hat x)$ と書く．どの $j$ でも第 $1$ 周辺分布は $p$ である．$q_\lambda$ の定め方から $\pi_\lambda = \lambda\pi_1 + (1-\lambda)\pi_2$ であり，$x$ について足して $\hat p_\lambda = \lambda\hat p_1 + (1-\lambda)\hat p_2$ である．

対 $(x,\hat x)$ を一つ固定し，
$$
a_1 := \lambda\,\pi_1(x,\hat x), \quad a_2 := (1-\lambda)\,\pi_2(x,\hat x), \quad
b_1 := \lambda\,p(x)\,\hat p_1(\hat x), \quad b_2 := (1-\lambda)\,p(x)\,\hat p_2(\hat x)
$$
とおく．これらは非負で，$a_1 + a_2 = \pi_\lambda(x,\hat x)$，$b_1 + b_2 = p(x)\,\hat p_\lambda(\hat x)$ である．

$b_j = 0$ となる $j$ があれば，そこでは $a_j = 0$ でもある．実際 $0 < \lambda < 1$ だから，$b_j = 0$ は $p(x) = 0$ または $\hat p_j(\hat x) = 0$ を意味する．前者なら $\pi_j(x,\hat x) = p(x)q_j(\hat x\mid x) = 0$ であり，後者なら $\pi_j(x,\hat x)$ は非負の数の和 $\hat p_j(\hat x)$ の一項だからやはり $0$ である．したがって，$b_j = 0$ である $j$ を落としても $a_1 + a_2$ と $b_1 + b_2$ は変わらない．落とした $j$ については $\pi_j(x,\hat x) = 0$ だから，定義 1.3.1 の和でこの対が $I(p;q_j)$ に与える寄与も $0$ である．

そこで $b_j > 0$ である $j$ だけを残して定理 1.7.1 の対数和不等式を当てる．残る $j$ が一つも無ければ $a_1 = a_2 = 0$，すなわち $\pi_1(x,\hat x) = \pi_2(x,\hat x) = \pi_\lambda(x,\hat x) = 0$ となり，この対が下の不等式の両辺に与える寄与はどちらも $0$ である．一つ以上あれば，落とした $j$ の項を右辺に $0$ として書き足して
$$
\pi_\lambda(x,\hat x)\,\log\frac{\pi_\lambda(x,\hat x)}{p(x)\,\hat p_\lambda(\hat x)}
 \;\le\; \lambda\,\pi_1(x,\hat x)\log\frac{\pi_1(x,\hat x)}{p(x)\,\hat p_1(\hat x)}
 \;+\; (1-\lambda)\,\pi_2(x,\hat x)\log\frac{\pi_2(x,\hat x)}{p(x)\,\hat p_2(\hat x)}
$$
を得る（対数和不等式の右辺の $a_j\log(a_j/b_j)$ では，$a_j$ と $b_j$ に掛かる $\lambda$ と $1-\lambda$ が対数の中で約分される）．

最後に $(x,\hat x)$ について足す．定義 1.3.1 の和は同時分布が正である項についてとるもので，同時分布が $0$ である項の寄与は $0$ だから，上の不等式を $\mathcal X\times\hat{\mathcal X}$ の全体で足し合わせると，左辺は $I(p;q_\lambda)$，右辺は $\lambda I(p;q_1) + (1-\lambda)I(p;q_2)$ になる．
:::

補題 9.2.2 が言っているのは，二つの再現の作り方を混ぜると，情報源との結びつきは混ぜる前の平均より強くならない，ということである．混ぜているのは $q$ だけで，情報源の分布 $p$ は固定していることに注意したい．証明で対数和不等式を当てた位置も見ておくと，まとめているのは「どちらの作り方を使ったか」という区別である．その区別を捨てると，同時分布と周辺の積との隔たりが見えにくくなる，というのが不等号の向きの内容である．

::: formalization-note
補題 9.2.2 にあたる宣言は無い．形式化は条件付き分布を混ぜる形をとらず，相対エントロピーが二つの引数について同時に凸であるという形（`klDiv_joint_convex` (`InformationTheory/Shannon/RateDistortion/Convexity.lean`)）で同じ役割を果たしている．補題 9.2.2 に付した証明が，この主張の保証のすべてである．
:::

::: proposition 9.2.3
$\mathcal X$ と $\hat{\mathcal X}$ を空でない有限集合，$p$ を $\mathcal X$ 上の分布，$d$ を歪み尺度（定義 9.1.1）とし，$\mathcal Q(\cdot)$ と $R(\cdot)$ を定義 9.1.5 のとおりとする．実数 $D_1$，$D_2$ について $\mathcal Q(D_1)$ と $\mathcal Q(D_2)$ がどちらも空でないならば，$\lambda\in[0,1]$ に対して $\mathcal Q\big(\lambda D_1 + (1-\lambda)D_2\big)$ も空でなく
$$
R\big(\lambda D_1 + (1-\lambda)D_2\big) \;\le\; \lambda R(D_1) + (1-\lambda) R(D_2)
$$
である．
:::

::: proof
命題 9.1.6 により，$I(p;\cdot)$ を $\mathcal Q(D_1)$ の上で最小にする $q_1$ と，$\mathcal Q(D_2)$ の上で最小にする $q_2$ をとることができ，$R(D_1) = I(p;q_1)$，$R(D_2) = I(p;q_2)$ である．$q_\lambda := \lambda q_1 + (1-\lambda)q_2$ を補題 9.2.2 のとおりに定める．

$q_\lambda$ が $\mathcal Q(\lambda D_1 + (1-\lambda)D_2)$ に属することを見る．補題 9.2.2 より $q_\lambda$ は条件付き分布である．定義 9.1.5 の期待歪みは $q$ の成分について一次だから
$$
\sum_{x,\hat x}p(x)\,q_\lambda(\hat x\mid x)\,d(x,\hat x)
 \;=\; \lambda\sum_{x,\hat x}p(x)\,q_1(\hat x\mid x)\,d(x,\hat x)
   \;+\; (1-\lambda)\sum_{x,\hat x}p(x)\,q_2(\hat x\mid x)\,d(x,\hat x)
$$
であり，$\lambda \ge 0$ と $1 - \lambda \ge 0$ より右辺は $\lambda D_1 + (1-\lambda)D_2$ 以下である．よって $q_\lambda$ は制約を満たし，とくに $\mathcal Q(\lambda D_1 + (1-\lambda)D_2)$ は空でない．

$R$ は値の集合の下限だから $R(\lambda D_1 + (1-\lambda)D_2) \le I(p;q_\lambda)$ であり，補題 9.2.2 より
$$
I(p;q_\lambda) \;\le\; \lambda I(p;q_1) + (1-\lambda)I(p;q_2) \;=\; \lambda R(D_1) + (1-\lambda)R(D_2)
$$
である．二つを合わせて主張を得る．
:::

命題 9.2.3 は，二つの歪みの上限のあいだを線形に補間した点で，$R$ の値が二つの端を結ぶ弦より下にあることを言っている．証明が使ったのは二つだけで，$D_1$ と $D_2$ で最小を与える作り方を混ぜると，期待歪みは二つの期待歪みを同じ重みで混ぜた値になり（期待歪みが $q$ について一次だから），結びつきは二つの相互情報量の平均より強くならない（補題 9.2.2）ということである．

::: formalized
`rateDistortionFunction_convexOn` (`InformationTheory/Shannon/RateDistortion/Convexity.lean`)
:::

::: formalization-note
`rateDistortionFunction_convexOn` が述べているのも，$R(D)$ を測度の言葉で書いた宣言 `rateDistortionFunction` (`InformationTheory/Shannon/RateDistortion/Converse.lean`) についての凸性で，定義 9.1.5 に紐付けた宣言とは別のものである．二つを結ぶ宣言は無い．またこの宣言は，情報源の分布を第 $1$ 周辺にもつどの同時分布についても歪みが可積分である，という前提を受け取る．命題 9.2.3 が置いた有限のアルファベットのもとでは，$d$ が有限個の値しかとらないのでこの前提は満たされるが，アルファベットを有限に固定した形の宣言は在庫に無い．
:::

## 両端

残るは両端である．左の端では歪みをいっさい許さず，右の端では $R$ が $0$ になる．左の端で $R$ がエントロピーに戻るのは，歪み尺度が「$0$ になるのは一致するときだけ」を満たすときで，この条件は主張の仮定に要る．

::: proposition 9.2.4
$\mathcal X$ と $\hat{\mathcal X}$ を空でない有限集合で $\mathcal X \subseteq \hat{\mathcal X}$ を満たすものとし，$p$ を $\mathcal X$ 上の分布，$X$ を分布 $p$ に従う $\mathcal X$ に値をとる確率変数とする．歪み尺度 $d$（定義 9.1.1）が「$d(x,\hat x) = 0$ となるのは $\hat x = x$ のとき，かつそのときに限る」を満たすとし，$\mathcal Q(\cdot)$ と $R(\cdot)$ を定義 9.1.5 のとおりとする．このとき $\mathcal Q(0)$ は空でなく
$$
R(0) \;=\; H(X)
$$
である．
:::

::: proof
$\mathcal Q(0)$ が空でないことを見る．$\mathcal X\subseteq\hat{\mathcal X}$ だから，$\hat x = x$ のとき $q(\hat x\mid x) := 1$，そうでないとき $q(\hat x\mid x) := 0$ と定めることができ，これは条件付き分布である．仮定より $d(x,x) = 0$ だから，その期待歪みは $\sum_x p(x)\,d(x,x) = 0$ であり，$q \in \mathcal Q(0)$ である．

次に $\mathcal Q(0)$ の元がどれも同じ相互情報量をもつことを見る．$q \in \mathcal Q(0)$ とすると，期待歪み $\sum_{x,\hat x}p(x)q(\hat x\mid x)d(x,\hat x)$ は $0$ 以下であり，各項は非負だから，すべての項が $0$ である．すなわち $p(x)q(\hat x\mid x) > 0$ ならば $d(x,\hat x) = 0$ であり，仮定によりそれは $\hat x = x$ を意味する．よって $p(x) > 0$ である $x$ については，$q(\hat x\mid x) > 0$ となる $\hat x$ が $x$ に限られ，$\sum_{\hat x}q(\hat x\mid x) = 1$ と合わせて $q(x\mid x) = 1$ である．したがって $q$ に対応する同時分布は，$\hat x = x$ のとき $p(x)$，そうでないとき $0$ であり，第 $2$ 周辺分布は $\hat x \in \mathcal X$ のとき $p(\hat x)$，そうでないとき $0$ である．

その相互情報量を定義 1.3.1 で計算する．同時分布が正になるのは $\hat x = x$ かつ $p(x) > 0$ のときだけで，そこでの値は $p(x)$，二つの周辺分布の積は $p(x)\,p(x)$ だから
$$
I(p;q) \;=\; \sum_{x \,:\, p(x) > 0} p(x)\log\frac{p(x)}{p(x)\,p(x)}
 \;=\; -\sum_{x \,:\, p(x) > 0} p(x)\log p(x) \;=\; H(X)
$$
である（最後の等号は，$p(x) = 0$ の項を $0\log 0 = 0$ と約束した定義 1.1.1 による）．

値の集合が一点 $\{H(X)\}$ なので，その下限は $H(X)$ である．
:::

仮定は落とせない．たとえば $d$ が恒等的に $0$ なら，どの条件付き分布も $\mathcal Q(0)$ に属するので，$\hat{\mathcal X}$ の一点に集中する条件付き分布をとれば，情報源と再現は独立になって相互情報量は $0$ になる．相互情報量は非負（命題 1.3.2）だから，このとき $R(0) = 0$ である．$H(X) > 0$ である情報源では，これは命題 9.2.4 の結論と違う値である．

命題 9.2.4 の値は，第2章 定理 2.3.6 の $\inf\mathcal R = H(X)$ と同じ $H(X)$ である．ただし命題 9.2.4 が述べているのは最適化問題の値についてであって，符号については何も言っていない．二つを結ぶには $R(D)$ が符号のレートの限界であることが要り，それが 9.5 節と 9.6 節の内容である．

::: formalization-note
命題 9.2.4 にあたる宣言は無い．レート歪み関数とエントロピーを同じ主張の中で結ぶ宣言が在庫に無いためである．命題 9.2.4 に付した証明が，この主張の保証のすべてである．
:::

::: proposition 9.2.5 $R$ が $0$ になる歪み
$\mathcal X$ と $\hat{\mathcal X}$ を空でない有限集合，$p$ を $\mathcal X$ 上の分布，$d$ を歪み尺度（定義 9.1.1）とし，$\mathcal Q(\cdot)$ と $R(\cdot)$ を定義 9.1.5 のとおりとする．
$$
D_{\max} \;:=\; \min_{\hat x \in \hat{\mathcal X}}\ \sum_{x \in \mathcal X} p(x)\,d(x,\hat x)
$$
とおくと，$\mathcal Q(D_{\max})$ は空でなく $R(D_{\max}) = 0$ である．さらに，$\mathcal Q(D)$ が空でない実数 $D$ について，$R(D) = 0$ となるのは $D \ge D_{\max}$ のとき，かつそのときに限る．
:::

::: proof
$\hat{\mathcal X}$ は空でない有限集合だから $D_{\max}$ は定まる．最小を与える点を一つとって $\hat x_0$ と書き，$\hat x = \hat x_0$ のとき $q_0(\hat x\mid x) := 1$，そうでないとき $q_0(\hat x\mid x) := 0$ と定める．これは条件付き分布であり，その期待歪みは $\sum_x p(x)\,d(x,\hat x_0) = D_{\max}$ である．

$D \ge D_{\max}$ ならば $R(D) = 0$ であることを見る（$D = D_{\max}$ を含む）．$q_0$ の期待歪みは $D_{\max} \le D$ だから $q_0 \in \mathcal Q(D)$ であり，とくに $\mathcal Q(D)$ は空でない．$q_0$ に対応する同時分布は，$\hat x = \hat x_0$ のとき $p(x)$，そうでないとき $0$ であって，これは第 $1$ 周辺分布 $p$ と，$\hat x_0$ に $1$ を置く第 $2$ 周辺分布との積にほかならない．よって $X$ と $\hat X$ は独立で，命題 1.3.2 より $I(p;q_0) = 0$ である．したがって $R(D) \le 0$ である．一方，命題 1.3.2 より $\mathcal Q(D)$ のどの元でも $I(p;q) \ge 0$ だから，$0$ は値の集合の下界であり，下限はそれ以上である．二つを合わせて $R(D) = 0$ を得る．

逆に，$\mathcal Q(D)$ が空でなく $R(D) = 0$ とする．命題 9.1.6 より，$I(p;q^*) = R(D) = 0$ を満たす $q^* \in \mathcal Q(D)$ がある．命題 1.3.2 の等号条件より，$q^*$ に対応する対 $(X,\hat X)$ は独立であり，同時分布は $p(x)\,\hat p(\hat x)$ である（$\hat p$ は第 $2$ 周辺分布）．よってその期待歪みは
$$
\sum_{x,\hat x}p(x)\,\hat p(\hat x)\,d(x,\hat x)
 \;=\; \sum_{\hat x}\hat p(\hat x)\Big(\sum_{x} p(x)\,d(x,\hat x)\Big)
 \;\ge\; \sum_{\hat x}\hat p(\hat x)\,D_{\max} \;=\; D_{\max}
$$
である（不等号は $D_{\max}$ が内側の和の最小値で $\hat p$ が非負なこと，最後の等号は $\sum_{\hat x}\hat p(\hat x) = 1$ による）．$q^* \in \mathcal Q(D)$ よりこの期待歪みは $D$ 以下だから，$D \ge D_{\max}$ である．
:::

命題 9.2.5 により，$R(D) = 0$ となる $D$ のうち最小のものが $D_{\max}$ である．$q_0$ のとり方が読み方を与える．情報源を見ずに，あらかじめ決めた一文字 $\hat x_0$ をいつも出す，というのが「何も送らない」再現であり，その中でいちばん歪みの小さいものが払う歪みが $D_{\max}$ である．それより多くの歪みを許してよいなら，情報源について何も知らなくて済む．

::: formalization-note
命題 9.2.5 にあたる宣言は無い．$D_{\max}$ を定める宣言も，レート歪み関数が $0$ になることを述べる宣言も在庫に無い．形式化には最悪の歪み $\max_{x,\hat x}d(x,\hat x)$ を定める `distortionMax` (`InformationTheory/Shannon/RateDistortion/AchievabilityAsymptoticFailureDecay.lean`) があるが，これは命題 9.2.5 の $D_{\max}$ とは別の量である．命題 9.2.5 に付した証明が，この主張の保証のすべてである．
:::

**両端で確かめる.** 二値の情報源と Hamming 歪み（例 9.1.3）で，二つの端を見ておく．$\mathcal X = \hat{\mathcal X} = \{0,1\}$ とし，$\Pr[X = 1] = \pi$ とする．$d_H(x,\hat x) = 0$ は $\hat x = x$ と同値だから命題 9.2.4 の仮定が満たされ，$R(0) = H(X) = H_b(\pi)$ である（$H_b$ は例 1.1.2 の二値エントロピー）．右の端は，$\hat x = 0$ に対して $\sum_x p(x)d_H(x,0) = \pi$，$\hat x = 1$ に対して $1 - \pi$ だから，命題 9.2.5 より $D_{\max} = \min(\pi, 1-\pi)$ である．公平なコイン（$\pi = 1/2$）なら $R(0) = 1$ ビット，$D_{\max} = 1/2$ になる．後者は，情報源を見ずにいつも $0$ を出せば文字の半分が食い違う，という勘定と合っている．

本節の四つを並べると，$R$ のグラフの形はかなり絞られる．命題 9.2.4 の仮定のもとでは，$D = 0$ で $H(X)$ から始まり，$D$ が増えるにつれて非増加で（命題 9.2.1）凸（命題 9.2.3）であり，$D_{\max}$ で $0$ に達して，その先は $0$ のままである（命題 9.2.5）．残っているのは両端のあいだの形だけで，9.3 節は二値の情報源について，9.4 節はガウス情報源についてそれを決める．
