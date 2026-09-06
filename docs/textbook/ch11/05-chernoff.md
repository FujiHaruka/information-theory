# 11.5 Bayes 誤り確率と Chernoff 情報

前節は二つの誤りを対等に扱わなかった．第一種の誤りを水準 $\varepsilon$ で抑え，そのうえで第二種の誤りだけを小さくしたからである．どちらを帰無仮説にするかを決める理由がないときには，この非対称を持ち込みたくない．そこで立て方を変える．真の分布が $P$ と $Q$ のどちらであるかを先に確率 $1/2$ ずつで選んでおき，出てきた系列を見てそれを当てる．誤る確率は二種類の誤りを $1/2$ ずつの重みで足したものになり，これを小さくすることが目標になる．本節はこの誤り確率も $n$ とともに指数で落ちること，そしてその指数が $D(P\,\|\,Q)$ とは別の量になることを示す．

答え方を一つ決める．事前確率が等しいのだから，系列 $x$ を見て $P^n(\{x\})$ と $Q^n(\{x\})$ を比べ，大きいほうの仮説を答えることにする．真が $P$ で $Q$ と答えてしまうのは $P^n(\{x\}) < Q^n(\{x\})$ となる $x$ が出たときで，その確率は $P^n$ で測る．真が $Q$ で $P$ と答えてしまうのは $P^n(\{x\}) \ge Q^n(\{x\})$ となる $x$ が出たときで，その確率は $Q^n$ で測る．どちらの場合でも，$x$ が誤りに寄与させるのは $P^n(\{x\})$ と $Q^n(\{x\})$ の小さいほうである．事前確率の $1/2$ を掛けて $x$ について足すと，次の形になる．

## Bayes 誤り確率

::: definition 11.5.1 Bayes 誤り確率
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の分布，$P^n$，$Q^n$ をそれぞれの $n$ 重の積分布とし，$n \ge 1$ とする．真の分布が $P$ と $Q$ から事前確率 $1/2$ ずつで選ばれるとし，系列 $x \in \mathcal X^n$ に対して $P^n(\{x\}) \ge Q^n(\{x\})$ ならば $P$ を，そうでなければ $Q$ を答える決定を考える．この決定の **Bayes 誤り確率** を
$$
P_e^{(n)} \;:=\; \frac12\sum_{x \in \mathcal X^n}\min\big(P^n(\{x\}),\,Q^n(\{x\})\big)
$$
で定める．
:::

::: formalized
`bayesErrorMinPmf` (`InformationTheory/Shannon/Chernoff/Basic.lean`)
:::

右辺の各項は，その系列が出たときに払う誤りの確率である．$P$ と $Q$ が離れているほど，どの系列でも二つの確率の一方が他方より格段に小さくなり，小さいほうだけを足した和は小さくなる．逆に $P = Q$ なら各項は $P^n(\{x\})$ そのもので，その総和は $1$ だから $P_e^{(n)} = 1/2$ である．すなわち，二つの仮説がまったく同じで見分けようがないときの誤り確率が，当てずっぽうと同じ $1/2$ になる．この決定がほかのどの決定よりも誤り確率が小さいことは本書では示さない．示すには決定の全体をわたって最小をとる形に問題を立て直す必要があり，本節が測るのは上の決定の誤り確率である．

以下では実数の指数をもつべき乗を使う．正の実数 $u$ と実数 $s$ に対し $u^s := e^{s\log u}$ と定め，$0^s$ は $s > 0$ のとき $0$，$s = 0$ のとき $1$ と約束する（本章の底は自然対数なので，$e$ のべき乗は指数関数そのものである）．定め方から $\log(u^s) = s\log u$ であり，指数法則 $e^{s + s'} = e^{s}e^{s'}$ から，正の $u$ について $u^{s}\,u^{s'} = u^{s+s'}$ と $(u^{s})^{s'} = u^{s s'}$ が従う．

## Chernoff の分配和

::: definition 11.5.2 Chernoff の分配和と Chernoff 情報
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布とする．実数 $\lambda$ に対し
$$
\mathcal Z(\lambda) \;:=\; \sum_{a \in \mathcal X} P(a)^{1-\lambda}\,Q(a)^{\lambda}
$$
を **Chernoff の分配和** と呼ぶ．$\mathcal Z(\lambda)$ は正の数の有限和だから正であり，$\log\mathcal Z(\lambda)$ が定まる．$P$ と $Q$ の **Chernoff 情報** を
$$
C^*(P,Q) \;:=\; -\inf_{0 \le \lambda \le 1}\log\mathcal Z(\lambda)
$$
で定める．
:::

::: formalized
`chernoffZSum`，`chernoffInfo` (`InformationTheory/Shannon/Chernoff/Basic.lean`)
:::

$\mathcal Z(\lambda)$ は，各文字で $P$ と $Q$ の値を重み $1-\lambda$ と $\lambda$ で幾何的に混ぜ，足し合わせたものである．$\lambda$ を $0$ から $1$ へ動かすと重みは $P$ の側から $Q$ の側へ移る．書体は花文字で，第10章 定義 10.2.1 の分配関数 $Z$ とは別の記号である．役割は同じで，重みを付けた和を分布にするための分母になる（違いは，重みを付ける基準が一様分布ではなく $P$ であることである）．その分布が 定義 11.5.8 の中間分布であり，本節の後半で主役になる．$C^*(P,Q)$ の星印は，11.3 節で置いた約束のとおり最適化した値であることを表す（分布には $\star$ を，値には $*$ を使い分ける）．星が付くこの $C^*$ は，第6章 定義 6.1.4 の通信路容量 $C(W)$ や第8章 定義 8.2.1 のガウス通信路の容量とは別の量である．定義 11.5.2 の下限が実際に最小値として達成されること，したがって $C^*(P,Q)$ が実数として定まることは 命題 11.5.6 で示す．

## 二つの道具

::: lemma 11.5.3 加重相加相乗平均
$u \ge 0$，$v \ge 0$ を実数，$\lambda \in [0,1]$ とすると
$$
u^{1-\lambda}\,v^{\lambda} \;\le\; (1-\lambda)\,u \;+\; \lambda\,v
$$
である．また $\min(u,v) \le u^{1-\lambda}v^{\lambda}$ である．
:::

::: proof
どちらの主張も $u$ か $v$ が $0$ の場合を先に片づける．$\lambda = 0$ のときは左辺が $u^1v^0 = u$，右辺が $u$ で，第 $1$ の主張は等号として成り立ち，$\min(u,v) \le u$ より第 $2$ の主張も成り立つ．$\lambda = 1$ のときも同様である．$\lambda \in (0,1)$ で $u = 0$ または $v = 0$ のときは，べき乗の約束から $u^{1-\lambda}v^\lambda = 0$ であり，右辺は非負の数の和だから第 $1$ の主張が成り立ち，$\min(u,v) = 0$ だから第 $2$ の主張も成り立つ．

以下 $u > 0$，$v > 0$ とする．1.1 節で認めた $\log$ の狭義凹性から出た有限 Jensen の不等式（補題 1.1.6）を，$2$ 点 $u$，$v$ と重み $1-\lambda$，$\lambda$ に当てると
$$
(1-\lambda)\log u \;+\; \lambda\log v \;\le\; \log\big((1-\lambda)u + \lambda v\big)
$$
である．左辺は $\log(u^{1-\lambda}) + \log(v^{\lambda}) = \log\big(u^{1-\lambda}v^{\lambda}\big)$ に等しい．ここで，二つの正の数について対数の値が $\le$ ならもとの数も $\le$ である．というのも，もとの数が真に大きければ 補題 8.2.5 より対数も真に大きいからである．これを当てて第 $1$ の主張を得る．

第 $2$ の主張に移る．$u \le v$ の場合を見れば足りる．$u$ と $v$ を入れ替えて $\lambda$ を $1-\lambda$ に取り替えると主張の両辺が同じ形になるので，$v \le u$ の場合はそこから出るからである．$u \le v$ なら 補題 8.2.5 より $\log u \le \log v$ であり，$\lambda \ge 0$ を掛けて $(1-\lambda)\log u$ を足すと
$$
\log u \;=\; (1-\lambda)\log u + \lambda\log u \;\le\; (1-\lambda)\log u + \lambda\log v \;=\; \log\big(u^{1-\lambda}v^{\lambda}\big)
$$
となる．ふたたび対数の値の大小からもとの数の大小に移して $u \le u^{1-\lambda}v^\lambda$ であり，$\min(u,v) = u$ だから主張を得る．
:::

::: formalization-note
補題 11.5.3 の第 $2$ の主張に対応する宣言は `min_le_rpow_mul_rpow` (`InformationTheory/Shannon/Chernoff/Basic.lean`) である．そちらは本文とは道筋が違い，最小値そのもののべき乗を経由して直接示している．第 $1$ の主張に対応する単独の宣言は無い．有限個の項についての同じ不等式は Mathlib の `Real.geom_mean_le_arith_mean_weighted` にあり，形式化はそれを別の箇所で使っている．
:::

::: lemma 11.5.4
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布，$P^n$，$Q^n$ をそれぞれの $n$ 重の積分布とし，$n \ge 1$，$\lambda \in [0,1]$ とする．$\mathcal Z$ を 定義 11.5.2 のとおりとすると
$$
\sum_{x \in \mathcal X^n} P^n\big(\{x\}\big)^{1-\lambda}\,Q^n\big(\{x\}\big)^{\lambda}
  \;=\; \mathcal Z(\lambda)^n
$$
である．
:::

::: proof
有限個の正の数の積のべき乗は，べき乗の積である（両辺の対数をとると，どちらも指数と各因子の対数の積の和になる）．$P$ と $Q$ は全点で正だから $P^n(\{x\}) = \prod_{i<n}P(x_i)$ の因子はどれも正で，この規則が使えて
$$
P^n\big(\{x\}\big)^{1-\lambda}\,Q^n\big(\{x\}\big)^{\lambda}
  \;=\; \prod_{i=0}^{n-1} P(x_i)^{1-\lambda}\,Q(x_i)^{\lambda}
$$
である．これを $x \in \mathcal X^n$ について足す．分配法則を $n$ 回使うと（$n$ についての帰納法），座標ごとに独立に和をとった形になり
$$
\sum_{x \in \mathcal X^n}\ \prod_{i=0}^{n-1} P(x_i)^{1-\lambda}Q(x_i)^{\lambda}
  \;=\; \prod_{i=0}^{n-1}\ \sum_{a \in \mathcal X} P(a)^{1-\lambda}Q(a)^{\lambda}
  \;=\; \mathcal Z(\lambda)^n
$$
を得る．
:::

::: formalized
`sum_prod_rpow_eq_Z_pow` (`InformationTheory/Shannon/Chernoff/Basic.lean`)
:::

## Chernoff 限界

::: theorem 11.5.5 Chernoff 限界
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布とし，$n \ge 1$，$\lambda \in [0,1]$ とする．$P_e^{(n)}$ を 定義 11.5.1，$\mathcal Z$ を 定義 11.5.2 のとおりとすると
$$
P_e^{(n)} \;\le\; \frac12\,\mathcal Z(\lambda)^n
$$
である．
:::

::: proof
定義 11.5.1 の各項に 補題 11.5.3 の第 $2$ の主張を，$u := P^n(\{x\})$，$v := Q^n(\{x\})$ として当てると
$$
\min\big(P^n(\{x\}),\,Q^n(\{x\})\big) \;\le\; P^n\big(\{x\}\big)^{1-\lambda}\,Q^n\big(\{x\}\big)^{\lambda}
$$
である．$x \in \mathcal X^n$ について足し，補題 11.5.4 を当てると右辺の和は $\mathcal Z(\lambda)^n$ になる．両辺に $1/2$ を掛ければ主張を得る．
:::

::: formalized
`bayesErrorMinPmf_le_half_Z_pow` (`InformationTheory/Shannon/Chernoff/Basic.lean`)
:::

この不等式はどの $\lambda \in [0,1]$ でも成り立つから，いちばんよい $\lambda$ を選んでよい．$\mathcal Z(\lambda)^n = e^{\,n\log\mathcal Z(\lambda)}$ だから，選ぶべきは $\log\mathcal Z(\lambda)$ を最小にする $\lambda$ であり，そのときの上界の指数が 定義 11.5.2 の $C^*(P,Q)$ である．Chernoff 情報を最小化の形で定めたのはこのためである．その最小値が実際に達成されることを次に確かめる．そこで最大値定理を借りるので，あとの微分の計算に使う規則もここでまとめて借りておく．

**Weierstrass の最大値定理を借りる.** 借りるのは「有限次元の実ベクトル空間の空でない有界閉集合の上の実数値連続関数は最大値をとる」という形である．当てる相手は二つで，一つは閉区間 $[0,1] \subseteq \mathbb R$ の上の実数値関数 $\lambda \mapsto -\log\mathcal Z(\lambda)$（命題 11.5.6），もう一つは，実ベクトル空間 $\mathbb R^{\mathcal X}$ の部分集合である確率単体の閉部分集合の上の実数値関数 $\tilde P \mapsto -D(\tilde P\,\|\,Q)$（11.6 節の 定理 11.6.2）である．この借用に依存するのは 命題 11.5.6 と 定理 11.6.2 の二つの証明だけで，以降はこの二つの結論だけを使う（11.6 節の 定理 11.6.6 もこの最大値定理を使うが，定理 11.6.2 の結論を通してである）．第6章 6.1 節が通信路容量の達成（定理 6.1.5）のために，第9章 9.1 節がレート歪み関数の下限が最小値であること（命題 9.1.8）のために借りたのと同じ定理である．本書はこの最大値定理を証明しないが，形式化されていないわけではない．定理 11.6.2 の形式化は，Mathlib にある無条件の機械検証済みのこの定理をそのまま呼び出しているからである．

**微分の計算規則を借りる.** 借りるのは微積分の計算規則で，次の三つである．有限個の連続関数（微分可能な関数）の一次結合・積・商（分母が $0$ でないところ）・合成・有限和はふたたび連続（微分可能）であり，導関数は和の法則・積の法則・商の法則・合成関数の微分の法則で与えられること．指数関数と対数関数の導関数が，本章の底のもとで $(e^s)' = e^s$，$(\log s)' = 1/s$ であること．微分係数が差分商の極限であり，極限が広義の不等号を保つこと．当てる相手は，有限アルファベット上の和として書かれた $\lambda \mapsto \mathcal Z(\lambda)$ とその対数（命題 11.5.6・命題 11.5.9），確率単体の上の $\tilde P \mapsto D(\tilde P\,\|\,Q)$（11.6 節の 定理 11.6.2），および二つの分布を結ぶ線分に沿って $D(\cdot\,\|\,Q)$ を制限した $1$ 変数関数（11.6 節の 定理 11.6.3）である．この借用に依存するのは 命題 11.5.6・命題 11.5.9・定理 11.6.2・定理 11.6.3 の四つの証明だけで，以降はこれらの結論だけを使う．第10章 10.4 節が同じ計算規則を借りている．どれも Mathlib にある無条件の機械検証済みの定理として形式化されている．

::: proposition 11.5.6
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布とし，$\mathcal Z$，$C^*$ を 定義 11.5.2 のとおりとする．このとき $\mathcal Z(0) = \mathcal Z(1) = 1$ である．また $\lambda \mapsto \log\mathcal Z(\lambda)$ は $[0,1]$ の上で連続かつ凸であり，$[0,1]$ の上で最小値をとる．とくに 定義 11.5.2 の下限は最小値として達成され，$C^*(P,Q) \ge 0$ である．
:::

::: proof
両端の値から見る．べき乗の約束より $Q(a)^0 = 1$，$P(a)^1 = P(a)$ だから $\mathcal Z(0) = \sum_a P(a) = 1$ であり，同じく $\mathcal Z(1) = \sum_a Q(a) = 1$ である．

連続性を見る．$P$ は全点で正だから，指数法則と $\log(u^s) = s\log u$ より
$$
P(a)^{1-\lambda}Q(a)^{\lambda}
  \;=\; P(a)\,\exp\Big(\lambda\log\frac{Q(a)}{P(a)}\Big)
$$
である．右辺は $\lambda$ の $1$ 次式に指数関数を合成したものに定数を掛けたもので，$\mathcal Z$ はその有限和だから，借用した計算規則より $\mathcal Z$ は連続である．$\mathcal Z(\lambda) > 0$ だから，$\log$ との合成もふたたび連続である．

凸性に移る．$\lambda$，$\lambda'$ を $[0,1]$ の数，$s \in [0,1]$ とし，各文字 $a$ について $c_a := P(a)^{1-\lambda}Q(a)^{\lambda}$，$d_a := P(a)^{1-\lambda'}Q(a)^{\lambda'}$ と置く．どちらも正で，$a$ について足すと $\sum_a c_a = \mathcal Z(\lambda)$，$\sum_a d_a = \mathcal Z(\lambda')$ である．指数法則から
$$
\Big(\frac{c_a}{\mathcal Z(\lambda)}\Big)^{1-s}\Big(\frac{d_a}{\mathcal Z(\lambda')}\Big)^{s}
  \;=\; \frac{P(a)^{1-((1-s)\lambda + s\lambda')}\,Q(a)^{(1-s)\lambda + s\lambda'}}
             {\mathcal Z(\lambda)^{1-s}\,\mathcal Z(\lambda')^{s}}
$$
である．左辺に 補題 11.5.3 の第 $1$ の主張を当て，$a$ について足すと，$c_a/\mathcal Z(\lambda)$ の総和も $d_a/\mathcal Z(\lambda')$ の総和も $1$ だから
$$
\sum_{a}\Big(\frac{c_a}{\mathcal Z(\lambda)}\Big)^{1-s}\Big(\frac{d_a}{\mathcal Z(\lambda')}\Big)^{s}
  \;\le\; \sum_{a}\Big((1-s)\frac{c_a}{\mathcal Z(\lambda)} + s\frac{d_a}{\mathcal Z(\lambda')}\Big)
  \;=\; 1
$$
である．右辺の式と見比べると，これは
$$
\mathcal Z\big((1-s)\lambda + s\lambda'\big) \;\le\; \mathcal Z(\lambda)^{1-s}\,\mathcal Z(\lambda')^{s}
$$
と同じことである．両辺は正だから，補題 8.2.5 より対数をとって $\log\mathcal Z\big((1-s)\lambda + s\lambda'\big) \le (1-s)\log\mathcal Z(\lambda) + s\log\mathcal Z(\lambda')$ を得る．これが凸性である．

最小値の存在に移る．$[0,1]$ は $\mathbb R$ の空でない有界閉集合で，$-\log\mathcal Z$ はその上で連続だから，借りた Weierstrass の最大値定理より $-\log\mathcal Z$ は $[0,1]$ で最大値をとる．すなわち $\log\mathcal Z$ は $[0,1]$ で最小値をとり，定義 11.5.2 の下限はその最小値である．最後に，最小値は $\log\mathcal Z(0) = \log 1 = 0$ 以下だから，符号を変えて $C^*(P,Q) \ge 0$ である．
:::

::: formalization-note
命題 11.5.6 の内容は，形式化ではそれぞれ別の宣言になっている．$\mathcal Z(0) = \mathcal Z(1) = 1$ は `chernoffZSum_lam_zero` と `chernoffZSum_lam_one`，凸性は `convexOn_chernoffLogZ`，最小値が達成されることは `chernoffInfo_attained`，非負性は `chernoffInfo_nonneg`（どれも `InformationTheory/Shannon/Chernoff/Basic.lean`）である．これらを一つにまとめた形の単独の宣言は無い．連続性を単独で述べる宣言も無く，形式化では凸性と最小値の存在の証明の中に現れる．
:::

::: corollary 11.5.7 Chernoff 限界の達成可能性
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布とし，$P_e^{(n)}$ を 定義 11.5.1，$C^*$ を 定義 11.5.2 のとおりとすると
$$
\liminf_{n \to \infty}\Big(-\frac1n\log P_e^{(n)}\Big) \;\ge\; C^*(P,Q)
$$
である．
:::

::: proof
まず $P_e^{(n)} > 0$ を見る．$P$ と $Q$ は全点で正だから，どの $x \in \mathcal X^n$ でも $P^n(\{x\})$ と $Q^n(\{x\})$ は正で，その小さいほうも正である．$\mathcal X^n$ は空でないから，定義 11.5.1 の和は正の数の和で正である．

命題 11.5.6 より $\log\mathcal Z$ は $[0,1]$ で最小値をとる．それを与える $\lambda$ を一つとると $\log\mathcal Z(\lambda) = -C^*(P,Q)$ であり，定理 11.5.5 より
$$
P_e^{(n)} \;\le\; \frac12\,\mathcal Z(\lambda)^n \;=\; \frac12\,e^{-n\,C^*(P,Q)}
$$
である．両辺は正で，補題 8.2.5 より対数は単調だから，対数をとって $-n$ で割ると
$$
-\frac1n\log P_e^{(n)} \;\ge\; C^*(P,Q) + \frac{\log 2}{n} \;\ge\; C^*(P,Q)
$$
である．どの $n \ge 1$ でもこれが成り立つから，下極限も $C^*(P,Q)$ 以上である．
:::

::: formalized
`chernoff_lemma_achievability` (`InformationTheory/Shannon/Chernoff/Basic.lean`)
:::

指数が $C^*(P,Q)$ に届くことは，これで分かった．残るのはそれを超えないことである．超えないことを示すには誤り確率を下から抑えなければならず，そのために $\mathcal Z(\lambda)$ を分母にして作る分布を導入する．

## 中間分布

::: definition 11.5.8 Chernoff の中間分布
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布とし，$\mathcal Z$ を 定義 11.5.2 のとおりとする．実数 $\lambda$ に対し
$$
P_\lambda(a) \;:=\; \frac{P(a)^{1-\lambda}\,Q(a)^{\lambda}}{\mathcal Z(\lambda)}
  \qquad (a \in \mathcal X)
$$
で定まる $\mathcal X$ 上の関数を **Chernoff の中間分布** と呼ぶ．分子は正で，$a$ について足したものが分母 $\mathcal Z(\lambda)$ だから，$P_\lambda$ は $\mathcal X$ 上の全点で正の分布である．
:::

命題 11.5.6 より $\mathcal Z(0) = \mathcal Z(1) = 1$ だから，$\lambda = 0$ では $P_0 = P$，$\lambda = 1$ では $P_1 = Q$ である．$\lambda$ を $0$ から $1$ へ動かすと $P_\lambda$ は $P$ から $Q$ へ移る．移り方は各点での値を幾何的に混ぜるもので，二つの分布を線分で結ぶ混ぜ方とは別である．この中間分布が，次の命題で Chernoff 情報に意味を与える．

::: proposition 11.5.9
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布とし，$\mathcal Z$，$C^*$ を 定義 11.5.2，$P_\lambda$ を 定義 11.5.8 のとおりとする．このとき $\lambda \mapsto \log\mathcal Z(\lambda)$ は微分可能で，その導関数は
$$
\frac{d}{d\lambda}\log\mathcal Z(\lambda)
  \;=\; \sum_{a \in \mathcal X} P_\lambda(a)\log\frac{Q(a)}{P(a)}
$$
である．さらに，$\log\mathcal Z$ の $[0,1]$ 上の最小値を与える $\lambda^*$ が開区間 $(0,1)$ に属するならば，この和は $\lambda = \lambda^*$ で $0$ になり
$$
C^*(P,Q) \;=\; D\big(P_{\lambda^*}\,\big\|\,P\big) \;=\; D\big(P_{\lambda^*}\,\big\|\,Q\big)
$$
である（$D$ は 1.6 節の相対エントロピー）．
:::

::: proof
命題 11.5.6 の証明で見た書き換え $P(a)^{1-\lambda}Q(a)^{\lambda} = P(a)\exp\big(\lambda\log\frac{Q(a)}{P(a)}\big)$ を使う．$Q(a)/P(a)$ は正だから $\log\frac{Q(a)}{P(a)}$ は $\lambda$ に依らない有限な数である．借用した計算規則より，$1$ 次式と指数関数の合成は微分可能で，$\lambda$ についての導関数は同じ関数に $\log\frac{Q(a)}{P(a)}$ を掛けたものである．有限和も微分可能だから
$$
\mathcal Z'(\lambda) \;=\; \sum_{a} P(a)\exp\Big(\lambda\log\frac{Q(a)}{P(a)}\Big)\log\frac{Q(a)}{P(a)}
$$
である．$\mathcal Z(\lambda) > 0$ だから，合成関数の微分の法則と $(\log s)' = 1/s$ より $\log\mathcal Z$ も微分可能で，その導関数は $\mathcal Z'(\lambda)/\mathcal Z(\lambda)$ である．各項を $\mathcal Z(\lambda)$ で割ると 定義 11.5.8 の $P_\lambda(a)$ になるから，導関数は主張の和に等しい．

後半に移る．$\lambda^* \in (0,1)$ が $[0,1]$ 上の最小値を与えるとし，$\log\mathcal Z$ の導関数を $\lambda^*$ で評価する．$0 < s < 1 - \lambda^*$ を満たす実数 $s$ をとると $\lambda^* + s \in [0,1]$ だから $\log\mathcal Z(\lambda^* + s) \ge \log\mathcal Z(\lambda^*)$ であり，差分商 $\big(\log\mathcal Z(\lambda^*+s) - \log\mathcal Z(\lambda^*)\big)/s$ は非負である．$s$ を $0$ に近づけると，借用した規則より差分商の極限は $\lambda^*$ での微分係数であり，極限は広義の不等号を保つから，微分係数は非負である．同じことを $-\lambda^* < s < 0$ で行うと，分子は非負で分母が負だから差分商は非正であり，微分係数は非正である．よって微分係数は $0$，すなわち前半の和は $\lambda^*$ で $0$ になる．

最後に二つの相対エントロピーを計算する．定義 11.5.8 と指数法則から
$$
\frac{P_\lambda(a)}{P(a)} \;=\; \frac{1}{\mathcal Z(\lambda)}\exp\Big(\lambda\log\frac{Q(a)}{P(a)}\Big),
\qquad
\frac{P_\lambda(a)}{Q(a)} \;=\; \frac{1}{\mathcal Z(\lambda)}\exp\Big(-(1-\lambda)\log\frac{Q(a)}{P(a)}\Big)
$$
である．対数をとって $P_\lambda(a)$ を掛け，$a$ について足すと，1.6 節の相対エントロピーの定義と $P_\lambda$ の総和が $1$ であることから
$$
D\big(P_\lambda\,\big\|\,P\big) = \lambda\sum_{a}P_\lambda(a)\log\frac{Q(a)}{P(a)} - \log\mathcal Z(\lambda),
\qquad
D\big(P_\lambda\,\big\|\,Q\big) = -(1-\lambda)\sum_{a}P_\lambda(a)\log\frac{Q(a)}{P(a)} - \log\mathcal Z(\lambda)
$$
である．$\lambda = \lambda^*$ では和が $0$ だから，どちらも $-\log\mathcal Z(\lambda^*)$ に等しい．$\lambda^*$ は最小値を与えるので，定義 11.5.2 より $-\log\mathcal Z(\lambda^*) = C^*(P,Q)$ である．
:::

::: formalization-note
中間分布に対応する宣言は `chernoffMediator`，両端の値は `chernoffMediator_lam_zero` と `chernoffMediator_lam_one`（どれも `InformationTheory/Shannon/Chernoff/Basic.lean`）である．導関数の式は `chernoffLogZ_hasDerivAt`，最小値を与える $\lambda^*$ で和が $0$ になることは `chernoffMediator_balance`，$C^*(P,Q)$ が中間分布から $P$ への相対エントロピーに等しいことは `chernoffInfo_eq_mediator_div`（どれも `InformationTheory/Shannon/Chernoff/Converse.lean`）である．ただし後の二つは，$\lambda^*$ が最小値を与えることを本文とは別の形で仮定に持つので，命題 11.5.9 そのものに紐付く単独の宣言にはならない．
:::

等式 $C^*(P,Q) = D(P_{\lambda^*}\,\|\,P) = D(P_{\lambda^*}\,\|\,Q)$ は，Chernoff 情報の読み方を与える．中間分布のうち $P$ からの隔たりと $Q$ からの隔たりが等しくなる点がとれるとき，その共通の値が Chernoff 情報である．二つの分布のちょうど中ほどまでの距離だ，と読みたくなるが，相対エントロピーは距離ではない（1.6 節）ので，そう読むのは言い過ぎである．言えるのは，二つの隔たりが釣り合う点での値だということである．

## 逆

::: theorem 11.5.10 Chernoff 限界の逆
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布とし，$P_e^{(n)}$ を 定義 11.5.1，$\mathcal Z$，$C^*$ を 定義 11.5.2，$P_\lambda$ を 定義 11.5.8 のとおりとする．$\log\mathcal Z$ の $[0,1]$ 上の最小値を与える $\lambda^*$ が開区間 $(0,1)$ に属するならば
$$
\limsup_{n \to \infty}\Big(-\frac1n\log P_e^{(n)}\Big) \;\le\; C^*(P,Q)
$$
である．
:::

::: proof
$\tilde P := P_{\lambda^*}$ と置く．定義 11.5.8 より $\tilde P$ は $\mathcal X$ 上の全点で正の分布であり，命題 11.5.9 より $D(\tilde P\,\|\,P) = D(\tilde P\,\|\,Q) = C^*(P,Q)$ である．

$\tilde P$ に近い型を作る．$\mathcal X$ は空でないから文字 $a_0$ を一つ選び，$\tilde P_n$ を $a_0$ を端数の引き受け手とする $\tilde P$ の丸め型（定理 11.3.4）とする．$a \ne a_0$ では $n\tilde P_n(a) = \lfloor n\tilde P(a)\rfloor$ が非負整数であり，$a_0$ では $n\tilde P_n(a_0) = n - \sum_{a \ne a_0}\lfloor n\tilde P(a)\rfloor$ が整数で，$\lfloor n\tilde P(a)\rfloor \le n\tilde P(a)$ と $\sum_a \tilde P(a) = 1$ から非負である．総和は $n$ だから，各文字をその個数だけ並べた系列の型は $\tilde P_n$ であり，$\tilde P_n$ は長さ $n$ の型である．また $a \ne a_0$ では $\lfloor n\tilde P(a)\rfloor \le n\tilde P(a) < \lfloor n\tilde P(a)\rfloor + 1$ より $0 \le \tilde P(a) - \tilde P_n(a) < 1/n$ であり，$a_0$ では二つの総和がどちらも $1$ だから差の絶対値は $\lvert\mathcal X\rvert/n$ 以下である．よってどの文字でも $\tilde P_n(a) \to \tilde P(a)$ である．

型類の中の確率で誤り確率を下から抑える．命題 11.1.4 より，$\mathcal T_n(\tilde P_n)$ のどの点でも $P^n(\{x\})$ は同じ値をとり，$Q^n(\{x\})$ も同じ値をとる．したがってその小さいほうも $x$ に依らず，$\mathcal T_n(\tilde P_n)$ にわたる和は要素数にその値を掛けたものである．要素数は非負だから，これは $P^n(\mathcal T_n(\tilde P_n))$ と $Q^n(\mathcal T_n(\tilde P_n))$ の小さいほうに等しい．定義 11.5.1 の和のほかの項は非負だから
$$
P_e^{(n)} \;\ge\; \frac12\min\Big(P^n\big(\mathcal T_n(\tilde P_n)\big),\ Q^n\big(\mathcal T_n(\tilde P_n)\big)\Big)
$$
である．右辺は正だから，補題 8.2.5 より対数をとって $-1/n$ を掛けると，不等号の向きが変わって
$$
-\frac1n\log P_e^{(n)}
  \;\le\; \frac{\log 2}{n}
    + \max\Big(-\frac1n\log P^n\big(\mathcal T_n(\tilde P_n)\big),\ -\frac1n\log Q^n\big(\mathcal T_n(\tilde P_n)\big)\Big)
$$
である（最小値の対数の符号を変えると，符号を変えた二つの対数の最大値になる）．

$\tilde P_n$ は長さ $n$ の型で各文字で $\tilde P$ に収束するから，系 11.2.2 を，参照する分布として $P$ をとって当てると $\frac1n\log P^n(\mathcal T_n(\tilde P_n)) \to -D(\tilde P\,\|\,P)$ であり，$Q$ をとって当てると $\frac1n\log Q^n(\mathcal T_n(\tilde P_n)) \to -D(\tilde P\,\|\,Q)$ である．二つの極限はどちらも $C^*(P,Q)$ に等しい．よってどの $\varepsilon > 0$ についても，十分大きい $n$ では右辺の最大値の中の二つがともに $C^*(P,Q) + \varepsilon$ 未満であり，$\frac{\log 2}{n}$ も $\varepsilon$ 未満である．したがって上極限は $C^*(P,Q) + 2\varepsilon$ 以下であり，$\varepsilon > 0$ は任意だから $C^*(P,Q)$ 以下である．
:::

::: formalized
`chernoff_converse` (`InformationTheory/Shannon/Chernoff/Converse.lean`)
:::

系 11.5.7 と 定理 11.5.10 を合わせると，最小値を与える $\lambda^*$ が内点にとれるときには $-\frac1n\log P_e^{(n)}$ が $C^*(P,Q)$ に収束する．内点にとれるという条件は，落とせない形で残っている．$P \ne Q$ ならつねに内点にとれるかどうかは，本書では示さない．次の例では，その条件を具体的な分布について直接確かめる．

## 数値で見る

::: example 11.5.11 二値の Chernoff 情報
$\mathcal X = \{0,1\}$ とし，$P$ を $P(0) = 0.1$，$P(1) = 0.9$，$Q$ を $Q(0) = Q(1) = 1/2$ で定まる分布とする．$P_e^{(n)}$ を 定義 11.5.1，$\mathcal Z$，$C^*$ を 定義 11.5.2，$P_\lambda$ を 定義 11.5.8 のとおりとすると，次の四つが成り立つ．

1. どの実数 $\lambda$ についても $\mathcal Z(\lambda) = 2^{-\lambda}\big(0.1^{1-\lambda} + 0.9^{1-\lambda}\big)$ である．
2. $\log\mathcal Z$ の $[0,1]$ 上の最小値を与える $\lambda$ はただ一つで，開区間 $(0,1)$ に属する．それを $\lambda^*$ と書くと，$P_{\lambda^*}(0)$ の値は約 $0.2675$，$\lambda^*$ の値は約 $0.5416$ である．
3. $C^*(P,Q)$ の値は約 $0.1124$ ナットである．いっぽう $D(P\,\|\,Q)$ の値は約 $0.3681$ ナット，$D(Q\,\|\,P)$ の値は約 $0.5108$ ナットで，$C^*(P,Q)$ はどちらよりも小さい（$D$ は 1.6 節の相対エントロピー）．
4. $-\frac1n\log P_e^{(n)} \longrightarrow C^*(P,Q)$（$n \to \infty$）である．
:::

::: proof
1. $Q(a) = 1/2$ はどちらの文字でも同じだから $Q(a)^{\lambda} = e^{-\lambda\log 2} = 2^{-\lambda}$ であり，これを 定義 11.5.2 の和からくくり出せばよい．

2. 命題 11.5.6 より $\log\mathcal Z$ は $[0,1]$ で最小値をとる．それを与える $\lambda$ を一つとる．命題 11.5.9 より $\log\mathcal Z$ は微分可能で，$\log\frac{Q(0)}{P(0)} = \log 5$，$\log\frac{Q(1)}{P(1)} = \log\frac59$ だから，$\lambda$ での微分係数は $P_\lambda(0)\log 5 + P_\lambda(1)\log\frac59$ である．$P_\lambda(1) = 1 - P_\lambda(0)$ と $\log\frac59 = \log 5 - \log 9$ を使うと，これは
$$
\log\tfrac59 \;+\; P_\lambda(0)\log 9
$$
に等しい．$P_0 = P$，$P_1 = Q$（定義 11.5.8）だから，$\lambda = 0$ での微分係数は $\sum_a P(a)\log\frac{Q(a)}{P(a)} = -D(P\,\|\,Q)$，$\lambda = 1$ での微分係数は $\sum_a Q(a)\log\frac{Q(a)}{P(a)} = D(Q\,\|\,P)$ である．$P \ne Q$ だから 定理 1.6.1 よりどちらの相対エントロピーも正で，$\lambda = 0$ での微分係数は負，$\lambda = 1$ での微分係数は正である．

最小値を与える $\lambda$ が $0$ だったとすると，$0 < s \le 1$ について $\log\mathcal Z(s) \ge \log\mathcal Z(0)$ だから差分商は非負で，$s$ を $0$ に近づけて $\lambda = 0$ での微分係数が非負となり，上に反する．$1$ だったとすると同じように $\lambda = 1$ での微分係数が非正となって反する．よって最小値を与える $\lambda$ は $(0,1)$ に属し，命題 11.5.9 よりそこで微分係数は $0$ である．

微分係数が $\lambda$ について狭義単調増加であることを見る．上の式と $\log 9 > 0$（補題 8.2.5）より，$P_\lambda(0)$ が狭義単調増加であることを見れば足りる．$Q(0) = Q(1)$ より
$$
\frac{P_\lambda(1)}{P_\lambda(0)} \;=\; \frac{P(1)^{1-\lambda}Q(1)^{\lambda}}{P(0)^{1-\lambda}Q(0)^{\lambda}}
  \;=\; 9^{\,1-\lambda} \;=\; e^{(1-\lambda)\log 9}
$$
であり，$P_\lambda(0) + P_\lambda(1) = 1$ だから $P_\lambda(0) = 1/\big(1 + 9^{\,1-\lambda}\big)$ である．指数関数は狭義単調増加だから（$\log$ が狭義単調増加であること（補題 8.2.5）と $\log e^s = s$ から出る），$9^{\,1-\lambda}$ は $\lambda$ について狭義単調減少で，正の数の逆数をとると向きが変わるから $P_\lambda(0)$ は狭義単調増加である．よって微分係数も狭義単調増加で，それが $0$ になる $\lambda$ は高々一つである．最小値を与える $\lambda$ はすべて $(0,1)$ に属して微分係数を $0$ にするのだから，そのような $\lambda$ はただ一つであり，これを $\lambda^*$ と書く．

数値に移る．微分係数が $\lambda^*$ で $0$ になることは，上の式より $P_{\lambda^*}(0)\log 9 = \log 9 - \log 5$ と同じだから
$$
P_{\lambda^*}(0) \;=\; \frac{\log 9 - \log 5}{\log 9}
  \;=\; \frac{2.19722\ldots - 1.60943\ldots}{2.19722\ldots} \;=\; 0.26751\ldots
$$
である．また $P_{\lambda^*}(0) = 1/(1 + 9^{\,1-\lambda^*})$ を $\lambda^*$ について解くと $9^{\,1-\lambda^*} = 0.73248\ldots/0.26751\ldots = 2.73813\ldots$ であり，対数をとって $1 - \lambda^* = 1.00727\ldots/2.19722\ldots = 0.45843\ldots$，すなわち $\lambda^* = 0.54156\ldots$ である．

3. 命題 11.5.9 より $C^*(P,Q) = D(P_{\lambda^*}\,\|\,Q)$ であり，例 11.3.6 の第 $1$ の主張と 補題 9.3.1 の第 $1$ の主張より，これは $\log 2 - H_b(P_{\lambda^*}(0))$ に等しい（$H_b$ は 例 1.1.2 の二値エントロピー関数）．第 $2$ の主張の値を入れると $H_b(0.26751\ldots) = 0.58077\ldots$，$\log 2 = 0.69314\ldots$ だから $C^*(P,Q) = 0.11237\ldots$ である．次に 例 11.2.4 の第 $1$ の主張より $D(P\,\|\,Q) = \log 2 - H_b(0.1) = 0.69314\ldots - 0.32508\ldots = 0.36806\ldots$ である．いっぽう 1.6 節の定義から
$$
D(Q\,\|\,P) \;=\; \tfrac12\log\frac{0.5}{0.1} + \tfrac12\log\frac{0.5}{0.9}
  \;=\; \tfrac12\big(\log 5 + \log\tfrac59\big)
  \;=\; \tfrac12\big(1.60943\ldots - 0.58778\ldots\big) \;=\; 0.51082\ldots
$$
である．$0.11237\ldots$ はどちらよりも小さい．

4. $P$ と $Q$ はどちらも全点で正だから 系 11.5.7 より下極限は $C^*(P,Q)$ 以上であり，第 $2$ の主張より $\lambda^*$ は $(0,1)$ に属するから 定理 11.5.10 より上極限は $C^*(P,Q)$ 以下である．よってこの数列は収束し，極限は $C^*(P,Q)$ である．
:::

::: formalization-note
例 11.5.11 の数値に対応する宣言は無い．形式化には，具体的な分布を入れて Chernoff 情報を計算した実例が置かれていない．例 11.5.11 に付した証明が，この主張の保証のすべてである．
:::

この $P$ は 例 11.2.4 と同じ偏ったコインである．例 11.5.11 の数を並べると，Bayes 誤り確率の指数 $0.1124$ は，第二種の誤りの指数を下から押さえた値 $D(P\,\|\,Q) = 0.3681$（系 11.4.7）より小さい．この例では，二つの誤りを同時に小さくすることを求めると，片方だけを見たときの速さは出ないということである．二つの立て方の間には，第一種の誤りにも指数を課すという中間の立て方がある．次節はそれを扱う．そこで現れる関数は，第一種の誤りに課す指数が $0$ のとき $D(P\,\|\,Q)$ をとり（命題 11.6.7），例 11.6.9 では $C^*(P,Q)$ もその関数の値として現れる．
