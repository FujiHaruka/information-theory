# 11.3 Sanov の定理

前節は型を一つ指定したときの確率を挟み込んだ（定理 11.2.1）．指数に残るのは相対エントロピーだけで，$Q$ から見て型が $P$ の系列が出る確率は $e^{-nD(P\,\|\,Q)}$ の前後にあった．本節は指定するものを，型一つから分布の集合に替える．$\mathcal X$ 上の分布の集合 $\mathcal E$ を先に決めておき，長さ $n$ の系列を $Q$ から引いたとき，その経験分布が $\mathcal E$ に落ちる確率を問う．

この確率が小さいことは，前節までの二つから見当がつく．$D(P\,\|\,Q)$ が $0$ になるのは $P = Q$ のときに限る（定理 1.6.1）ので，$Q$ 自身から離れたところに $\mathcal E$ を置けば，$\mathcal E$ に属するどの型 $P$ でも $D(P\,\|\,Q)$ は正であり，その型類の確率は 定理 11.2.1 より $n$ とともに指数で落ちる．落ちる速さは型ごとに違うが，型の個数は $n$ の多項式で抑えられている（命題 11.1.3）．有限個の正の数の和は，最大の項以上で，最大の項に項の個数を掛けたもの以下である．したがって $\frac1n\log$ をとって $n$ を大きくすると多項式倍の差は消え，残るのはいちばん大きい項の指数，すなわち $D(\cdot\,\|\,Q)$ がいちばん小さい型の指数だけになる．これが本節の主張で，Sanov の定理と呼ばれる．

示し方は上下に分ける．上界は，型の個数の多項式評価と 定理 11.2.1 の上界を合わせた数え上げで出る．下界は，$\mathcal E$ の中の分布を一つ選び，その型類ぶんだけで確率を下から押さえて出す．二つを合わせると，指数が一点で決まるという主張になる．

## 集合に属する型

::: definition 11.3.1 集合に属する型
$\mathcal X$ を空でない有限アルファベットとし，$\mathcal E$ を $\mathcal X$ 上の分布の集合とする．$n \ge 1$ に対し，$\mathcal E$ に属する長さ $n$ の型（定義 11.1.1）の全体を
$$
\mathcal E_n \;:=\; \big\{\, P \in \mathcal E \;:\; P \text{ は長さ } n \text{ の型} \,\big\}
$$
と書く．
:::

$\mathcal E$ は分布の集合であって，系列の集合ではない．系列の側でこれに対応するのは，型が $\mathcal E$ に入る系列の全体 $\{x \in \mathcal X^n : \hat P_x \in \mathcal E\}$ である．どの系列もただ一つの型をもつ（定義 11.1.1）から，この集合は $\mathcal E_n$ に属する型の型類を重なりなく合わせたものにほかならない．$\mathcal E$ が無限に多くの分布を含んでいてもよいが，長さ $n$ の型は有限個しかない（命題 11.1.3）ので $\mathcal E_n$ は有限集合である．$\mathcal E$ の中に長さ $n$ の型が一つも無いこともあり，そのときこの系列の集合は空になる．本節が測るのは，$\mathcal X$ 上の分布 $Q$ とその $n$ 重の積分布 $Q^n$ に対する，この集合の確率である．

## 上界

定理 11.3.2 の $\gamma$ は $\inf_{P \in \mathcal E}D(P\,\|\,Q)$ と思って読めばよい．条件を $\mathcal E_n$ に属する型についてだけ課しているのは，証明が型の上の和しか使わないからで，例 11.6.4 の制約集合のように $\mathcal E$ が型でない分布を多く含むときには，そのぶん条件が緩くなって効く．

::: theorem 11.3.2 Sanov の上界
$\mathcal X$ を空でない有限アルファベット，$Q$ を $\mathcal X$ 上の全点で正の分布，$Q^n$ をその $n$ 重の積分布とし，$\mathcal E$ を $\mathcal X$ 上の分布の集合，$\mathcal E_n$ を 定義 11.3.1 のとおりとする．$n \ge 1$ とし，実数 $\gamma$ が，$\mathcal E_n$ に属するどの型 $P$ についても $\gamma \le D(P\,\|\,Q)$ を満たすとすると
$$
Q^n\big(\{\, x \in \mathcal X^n \;:\; \hat P_x \in \mathcal E \,\}\big)
  \;\le\; (n+1)^{\lvert\mathcal X\rvert}\,e^{-n\gamma}
$$
であり，左辺が正ならば
$$
\frac1n\log Q^n\big(\{\, x \in \mathcal X^n \;:\; \hat P_x \in \mathcal E \,\}\big)
  \;\le\; -\gamma \;+\; \frac{\lvert\mathcal X\rvert\log(n+1)}{n}
$$
である（$\hat P_x$ は 定義 11.1.1 の型，$D$ は 1.6 節の相対エントロピー）．
:::

::: proof
どの系列もただ一つの型をもつ（定義 11.1.1）から，$\{x \in \mathcal X^n : \hat P_x \in \mathcal E\}$ は $\mathcal E_n$ に属する型 $P$ の型類 $\mathcal T_n(P)$ を重なりなく合わせたものであり
$$
Q^n\big(\{x : \hat P_x \in \mathcal E\}\big) \;=\; \sum_{P \in \mathcal E_n} Q^n\big(\mathcal T_n(P)\big)
$$
である．右辺の各項に 定理 11.2.1 の上界を当てると $Q^n(\mathcal T_n(P)) \le e^{-nD(P\,\|\,Q)}$ であり，仮定より $\gamma \le D(P\,\|\,Q)$ であり，指数関数は単調増加（補題 8.2.5 の $\log$ の単調性と $\log e^s = s$ から出る）だから $Q^n(\mathcal T_n(P)) \le e^{-n\gamma}$ である．項の個数は $\mathcal E$ に属する長さ $n$ の型の個数だから，長さ $n$ の型の総数以下であり，命題 11.1.3 より $(n+1)^{\lvert\mathcal X\rvert}$ 以下である．よって和は $(n+1)^{\lvert\mathcal X\rvert}e^{-n\gamma}$ 以下である．

第 $2$ の不等式は第 $1$ の両辺の対数をとって $n$ で割ったものである．左辺が正なら対数がとれ，補題 8.2.5 より $\log$ は単調だから
$$
\log Q^n\big(\{x : \hat P_x \in \mathcal E\}\big)
  \;\le\; \lvert\mathcal X\rvert\log(n+1) \;-\; n\gamma
$$
であり，両辺を $n$ で割れば主張を得る．
:::

::: formalization-note
定理 11.3.2 に対応する単独の宣言は無い．`typeClassByCount_union_Qn_le_inf` (`InformationTheory/Shannon/Sanov/LDP.lean`) が，型を有限個集めた族について，その合併の確率を「族の要素数に $e^{-n\gamma}$ を掛けたもの」で抑える形を与える．この族の添字は各文字の出現回数の組で，その組の全体の要素数がちょうど $(n+1)^{\lvert\mathcal X\rvert}$ であることを `typeCountIndex_card` (`InformationTheory/Shannon/Sanov/LDP.lean`) が与えるから，族の要素数はこれ以下である．二つの合成である．$n$ を大きくした形の 系 11.3.3 のほうは単独で形式化されている．
:::

型の個数の多項式評価は，ここで初めて本来の役目を果たす．型ごとの上界 $e^{-n\gamma}$ を項の個数だけ足し合わせても，掛かるのは $n$ の多項式だけなので，$\frac1n\log$ をとると $0$ に向かう項しか足されない．そのことを極限の形にしたのが次の系である．

::: corollary 11.3.3
$\mathcal X$ を空でない有限アルファベット，$Q$ を $\mathcal X$ 上の全点で正の分布，$Q^n$ をその $n$ 重の積分布とし，$\mathcal E$ を $\mathcal X$ 上の分布の集合，$\mathcal E_n$ を 定義 11.3.1 のとおりとする．実数 $\gamma$ が，すべての $n \ge 1$ と $\mathcal E_n$ に属するどの型 $P$ についても $\gamma \le D(P\,\|\,Q)$ を満たすとする．このとき，どの $\varepsilon > 0$ についても，ある $n_0$ があって，$n \ge n_0$ かつ $Q^n(\{x \in \mathcal X^n : \hat P_x \in \mathcal E\}) > 0$ を満たすすべての $n$ について
$$
\frac1n\log Q^n\big(\{\, x \in \mathcal X^n \;:\; \hat P_x \in \mathcal E \,\}\big) \;\le\; -\gamma + \varepsilon
$$
が成り立つ．
:::

::: proof
定理 11.3.2 の第 $2$ の不等式より，左辺は $-\gamma + \frac{\lvert\mathcal X\rvert\log(n+1)}{n}$ 以下である．したがって $\frac{\lvert\mathcal X\rvert\log(n+1)}{n}$ が $0$ に収束することを見れば，与えられた $\varepsilon$ に対してその収束から $n_0$ がとれる．

補題 11.2.2 より $\frac{\log(n+1)}{n} \to 0$ であり，$\lvert\mathcal X\rvert$ は $n$ に依らない有限の数だから，$\frac{\lvert\mathcal X\rvert\log(n+1)}{n} \to 0$ である．
:::

::: formalized
`sanov_ldp_upper_bound` (`InformationTheory/Shannon/Sanov/LDP.lean`)
:::

$\gamma$ としてどれだけ大きい値がとれるかで，系 11.3.3 の強さが決まる．とれるのは，すべての $n$ の $\mathcal E_n$ を通して $D(\cdot\,\|\,Q)$ を下から抑える値までである．$\mathcal E$ の上で $D(\cdot\,\|\,Q)$ を最小にする分布があれば，その値は条件を満たす $\gamma$ の一つになる．同じ値が下からの評価でも現れることを，次に見る．

## 下界

下界は，$\mathcal E$ の中の分布を一つ選び，その型類ぶんだけを数えて出す．ただし選んだ分布がそのまま長さ $n$ の型であるとは限らない．長さ $n$ の型がとる値は $0, 1/n, \dots, 1$ に限られる（定義 11.1.1）からである．そこで，選んだ分布に近い型を作って代用する．各文字について $n$ 倍した値を整数に切り下げ，切り下げで足りなくなったぶんを一つの文字にまとめて押し付ければ，個数の総和が $n$ になって型になる．以下，$\lfloor t \rfloor$ で実数 $t$ 以下の最大の整数を表す（$\lfloor t \rfloor \le t < \lfloor t \rfloor + 1$ である）．選ぶ分布は $\tilde P$ と書く．ここで選ぶ分布に最適性は要らないので星印を付けない．星印は本章では最適化して選んだものであることを表す約束で，分布には $\star$ を，値には $*$ を使い分ける．最初に星が付くのは，最小化子であることを仮定に置く 定理 11.3.7 の $P^\star$ である．

::: definition 11.3.4 丸め型
$\mathcal X$ を空でない有限アルファベット，$\tilde P$ を $\mathcal X$ 上の分布，$a_0$ を $\mathcal X$ の文字とし，$n \ge 1$ とする．
$$
\tilde P_n(a) \;:=\; \frac{\lfloor n\tilde P(a)\rfloor}{n} \quad (a \ne a_0),
\qquad
\tilde P_n(a_0) \;:=\; 1 - \sum_{a \ne a_0}\frac{\lfloor n\tilde P(a)\rfloor}{n}
$$
で定まる $\mathcal X$ 上の関数 $\tilde P_n$ を，$a_0$ を端数の引き受け手とする $\tilde P$ の **丸め型** と呼ぶ（$\lfloor t\rfloor$ は $t$ 以下の最大の整数）．
:::

::: formalization-note
丸め型に対応する宣言は `roundedTypeIndex` (`InformationTheory/Shannon/Sanov/RoundedTypeSequence.lean`) であるが，覆っている範囲が本文より狭い．本文は端数の引き受け手 $a_0$ を選べる形にしてあるのに対し，形式化はその文字をアルファベットの中の一つに固定しており，しかもどの文字であるかを述べていない．あとの 例 11.3.8 が示すとおり，丸め型が集合に入るかどうかは引き受け手の選び方で変わるので，この差は形だけのものではない．
:::

::: lemma 11.3.5 丸め型は長さ $n$ の型であり，各文字で元の分布に収束する
$\mathcal X$ を空でない有限アルファベット，$\tilde P$ を $\mathcal X$ 上の分布，$a_0$ を $\mathcal X$ の文字とし，各 $n \ge 1$ について $\tilde P_n$ を $a_0$ を端数の引き受け手とする $\tilde P$ の丸め型（定義 11.3.4）とする．このとき，どの $n \ge 1$ でも $\tilde P_n$ は長さ $n$ の型（定義 11.1.1）であり，どの文字 $a$ についても $\tilde P_n(a) \to \tilde P(a)$（$n \to \infty$）である．
:::

::: proof
まず $\tilde P_n$ が長さ $n$ の型であることを見る．$a \ne a_0$ については $n\tilde P_n(a) = \lfloor n\tilde P(a)\rfloor$ で，これは非負整数である．$a_0$ については $n\tilde P_n(a_0) = n - \sum_{a \ne a_0}\lfloor n\tilde P(a)\rfloor$ で，これも整数であり，$\lfloor t\rfloor \le t$ と $\sum_a \tilde P(a) = 1$ から
$$
\sum_{a \ne a_0}\big\lfloor n\tilde P(a)\big\rfloor \;\le\; \sum_{a \ne a_0} n\tilde P(a) \;\le\; n
$$
なので非負である．よって $\big(n\tilde P_n(a)\big)_{a\in\mathcal X}$ は総和が $n$ の非負整数の組であり，各文字をその個数だけ並べた系列の型は $\tilde P_n$ だから，$\tilde P_n$ は長さ $n$ の型である．

次に $\tilde P_n$ が各文字で $\tilde P$ に収束することを見る．$a \ne a_0$ については $\lfloor t\rfloor \le t < \lfloor t\rfloor + 1$ より $0 \le \tilde P(a) - \tilde P_n(a) < 1/n$ である．$a_0$ については，$\tilde P_n$ と $\tilde P$ の総和がどちらも $1$ だから $\tilde P_n(a_0) - \tilde P(a_0) = \sum_{a \ne a_0}\big(\tilde P(a) - \tilde P_n(a)\big)$ であり，右辺の各項は $0$ 以上 $1/n$ 未満だから，差の絶対値は $\lvert\mathcal X\rvert/n$ 以下である．よってどの文字でも $\tilde P_n(a) \to \tilde P(a)$ である．
:::

::: formalization-note
補題 11.3.5 の二つの主張に対応する宣言は `roundedTypeIndex_sum` と `roundedTypeIndex_tendsto`（どちらも `InformationTheory/Shannon/Sanov/RoundedTypeSequence.lean`）であるが，どちらも端数の引き受け手を固定した丸め型についてのもので，覆っている範囲は本文より狭い．
:::

::: theorem 11.3.6 Sanov の下界
$\mathcal X$ を空でない有限アルファベット，$Q$ を $\mathcal X$ 上の全点で正の分布，$Q^n$ をその $n$ 重の積分布とし，$\mathcal E$ を $\mathcal X$ 上の分布の集合，$\mathcal E_n$ を 定義 11.3.1 のとおりとする．$\tilde P$ を $\mathcal X$ 上の分布，$a_0$ を $\mathcal X$ の文字とし，各 $n \ge 1$ について $\tilde P_n$ を $a_0$ を端数の引き受け手とする $\tilde P$ の丸め型（定義 11.3.4）とする．十分大きいすべての $n$ について $\tilde P_n \in \mathcal E_n$ であるならば，十分大きい $n$ で $Q^n(\{x \in \mathcal X^n : \hat P_x \in \mathcal E\})$ は正であり
$$
\liminf_{n \to \infty}\frac1n\log Q^n\big(\{\, x \in \mathcal X^n \;:\; \hat P_x \in \mathcal E \,\}\big)
  \;\ge\; -D(\tilde P\,\|\,Q)
$$
である（$\hat P_x$ は 定義 11.1.1 の型，$D$ は 1.6 節の相対エントロピー）．
:::

::: proof
補題 11.3.5 より，どの $n \ge 1$ でも $\tilde P_n$ は長さ $n$ の型であり，どの文字でも $\tilde P_n(a) \to \tilde P(a)$ である．

仮定より，ある $n_0$ があって $n \ge n_0$ のとき $\tilde P_n \in \mathcal E_n$，とくに $\tilde P_n \in \mathcal E$ である．型が $\tilde P_n$ である系列は型が $\mathcal E$ に属するから
$$
\mathcal T_n\big(\tilde P_n\big) \;\subseteq\; \big\{\, x \in \mathcal X^n \;:\; \hat P_x \in \mathcal E \,\big\}
$$
であり，包含している側の集合の確率のほうが小さくないから $Q^n(\mathcal T_n(\tilde P_n)) \le Q^n(\{x : \hat P_x \in \mathcal E\})$ である．左辺は 定理 11.2.1 の下界より $(n+1)^{-\lvert\mathcal X\rvert}e^{-nD(\tilde P_n\|Q)}$ 以上で，これは正だから，$n \ge n_0$ では右辺も正である．

補題 8.2.5 より $\log$ は単調だから，$n \ge n_0$ について
$$
\frac1n\log Q^n\big(\{x : \hat P_x \in \mathcal E\}\big)
  \;\ge\; \frac1n\log Q^n\big(\mathcal T_n(\tilde P_n)\big)
$$
である．$\tilde P_n$ は長さ $n$ の型で各文字で $\tilde P$ に収束するから，系 11.2.3 より右辺は $-D(\tilde P\,\|\,Q)$ に収束する．よって左辺の下極限は $-D(\tilde P\,\|\,Q)$ 以上である．
:::

::: formalization-note
定理 11.3.6 に対応する宣言は `sanov_ldp_lower_bound_pointwise` (`InformationTheory/Shannon/Sanov/LiminfBound.lean`) であるが，覆っている範囲が本文より狭い．丸め型の端数の引き受け手が固定されていることに加えて，形式化は $\tilde P$ が全点で正であることも仮定に持つ．
:::

## 二つを合わせる

::: theorem 11.3.7 Sanov の定理
$\mathcal X$ を空でない有限アルファベット，$Q$ を $\mathcal X$ 上の全点で正の分布，$Q^n$ をその $n$ 重の積分布とし，$\mathcal E$ を $\mathcal X$ 上の分布の集合，$\mathcal E_n$ を 定義 11.3.1 のとおりとする．$P^\star$ を $\mathcal X$ 上の分布，$a_0$ を $\mathcal X$ の文字とし，$P^\star_n$ を $a_0$ を端数の引き受け手とする $P^\star$ の丸め型（定義 11.3.4）とする．次の二つが成り立つとする．

1. すべての $n \ge 1$ と $\mathcal E_n$ に属するどの型 $P$ についても $D(P^\star\,\|\,Q) \le D(P\,\|\,Q)$ である．
2. 十分大きいすべての $n$ について $P^\star_n \in \mathcal E_n$ である．

このとき，十分大きい $n$ で $Q^n(\{x \in \mathcal X^n : \hat P_x \in \mathcal E\})$ は正であり
$$
\frac1n\log Q^n\big(\{\, x \in \mathcal X^n \;:\; \hat P_x \in \mathcal E \,\}\big)
  \;\longrightarrow\; -D(P^\star\,\|\,Q) \qquad (n \to \infty)
$$
である（$\hat P_x$ は 定義 11.1.1 の型，$D$ は 1.6 節の相対エントロピー）．
:::

::: proof
第 $2$ の仮定から 定理 11.3.6 が使えて，十分大きい $n$ でこの確率は正であり，その下極限は $-D(P^\star\,\|\,Q)$ 以上である．

上からの評価には 系 11.3.3 を $\gamma := D(P^\star\,\|\,Q)$ ととって当てる．第 $1$ の仮定がその $\gamma$ についての条件そのものだから，どの $\varepsilon > 0$ についても，ある $n_0$ があって，$n \ge n_0$ でこの確率が正であるかぎり
$$
\frac1n\log Q^n\big(\{x : \hat P_x \in \mathcal E\}\big) \;\le\; -D(P^\star\,\|\,Q) + \varepsilon
$$
である．十分大きい $n$ では確率は正なのだから，上極限は $-D(P^\star\,\|\,Q) + \varepsilon$ 以下であり，$\varepsilon > 0$ は任意だから，上極限は $-D(P^\star\,\|\,Q)$ 以下である．

下極限が $-D(P^\star\,\|\,Q)$ 以上で，上極限が $-D(P^\star\,\|\,Q)$ 以下だから，この数列は収束して極限は $-D(P^\star\,\|\,Q)$ である．
:::

::: formalization-note
定理 11.3.7 に対応する宣言は `sanov_ldp_equality` (`InformationTheory/Shannon/Sanov/TendstoSandwich.lean`) である．二つの仮定の置き方は本文と同じで，第 $1$ の仮定が最小化子であること，第 $2$ の仮定が丸め型が最終的に $\mathcal E_n$ に入ることに対応する．ただし 定理 11.3.6 と同じ理由で覆っている範囲が本文より狭い．丸め型の端数の引き受け手が固定されており，$P^\star$ が全点で正であることも仮定に持つ．
:::

読み方は素直である．経験分布が $\mathcal E$ に落ちる確率の指数は，$\mathcal E$ に属する型のうち $Q$ にいちばん近いもの一つで決まり，残りの型は指数の水準では何も寄与しない．第 $1$ の仮定は $P^\star$ がその一つであること，すなわちすべての $n$ の $\mathcal E_n$ を通した最小化子であることを求めている．第 $2$ の仮定は，$\mathcal E$ が型で近づけられる形をしていることを求めている．たとえば $\mathcal E$ が一点だけからなり，その一点がどの $n$ でも長さ $n$ の型でなければ，どの $n$ でも $\mathcal E_n$ は空になり，第 $2$ の仮定は成り立たない．このとき系列の集合も空で，確率は $0$ である．

## 数値で見る

::: example 11.3.8 コインの表が $7$ 割以上出る確率
$\mathcal X = \{0,1\}$ とし，$1$ を表と読む．$Q$ を $Q(0) = Q(1) = 1/2$ で定まる分布，$Q^n$ をその $n$ 重の積分布とし，$\mathcal E := \{\, P : P \text{ は } \mathcal X \text{ 上の分布で } P(1) \ge 0.7 \,\}$ とする．$\hat P_x$ を 定義 11.1.1 の型，$H_b$ を 例 1.1.2 の二値エントロピー関数とし，$P^\star$ を $P^\star(0) = 0.3$，$P^\star(1) = 0.7$ で定まる分布とすると，次の四つが成り立つ．

1. $\mathcal X$ 上のどの分布 $P$ についても $D(P\,\|\,Q) = \log 2 - H_b\big(P(1)\big)$ であり，$P \in \mathcal E$ ならば $D(P^\star\,\|\,Q) \le D(P\,\|\,Q)$ である．
2. $D(P^\star\,\|\,Q) = \log 2 - H_b(0.7)$ であり，その値は約 $0.0823$ ナットである．
3. $\dfrac1n\log Q^n\big(\{x \in \mathcal X^n : \hat P_x \in \mathcal E\}\big) \longrightarrow -\big(\log 2 - H_b(0.7)\big)$（$n \to \infty$）である．
4. 端数の引き受け手を $a_0 := 0$ ととった $P^\star$ の丸め型（定義 11.3.4）は，$n$ が $10$ の倍数でないかぎり $\mathcal E$ に属さない．とくに，その選び方では 定理 11.3.7 の第 $2$ の仮定は成り立たない．
:::

::: proof
1. 相対エントロピーの定義（1.6 節）から，$\mathcal X$ 上の分布 $P$ について
$$
D(P\,\|\,Q) \;=\; \sum_{a}P(a)\log\frac{P(a)}{1/2}
  \;=\; \sum_{a}P(a)\log P(a) \;+\; \log 2 \;=\; \log 2 - H(P)
$$
であり，$H(P) = H_b(P(1))$ は 例 1.1.2 のとおりである．$P \in \mathcal E$ とすると $P(1) \in [0.7, 1]$ であり，$1 - P(1) \in [0, 0.3]$ である．補題 9.3.1 の第 $1$ の主張より $H_b(P(1)) = H_b(1 - P(1))$ であり，$0 \le 1 - P(1) \le 0.3 \le 1/2$ だから第 $3$ の主張より $H_b(1 - P(1)) \le H_b(0.3)$ である．ふたたび第 $1$ の主張より $H_b(0.3) = H_b(0.7)$ だから $H_b(P(1)) \le H_b(0.7)$ であり，$\log 2$ から引く向きに直すと $D(P^\star\,\|\,Q) \le D(P\,\|\,Q)$ を得る．

2. 第 $1$ の主張を $P := P^\star$ に当てると $D(P^\star\,\|\,Q) = \log 2 - H_b(0.7)$ である．$H_b(0.7) = -0.7\log 0.7 - 0.3\log 0.3 = 0.61086\ldots$，$\log 2 = 0.69314\ldots$ だから，差は $0.08228\ldots$ である．

3. 定理 11.3.7 の仮定を，端数の引き受け手を $a_0 := 1$ ととって確かめる．第 $1$ の仮定は，$\mathcal E_n \subseteq \mathcal E$ だから第 $1$ の主張から従う．第 $2$ の仮定を見る．丸め型は $P^\star_n(0) = \lfloor 0.3n\rfloor/n$，$P^\star_n(1) = 1 - \lfloor 0.3n\rfloor/n$ である．$nP^\star_n(0) = \lfloor 0.3n\rfloor$ と $nP^\star_n(1) = n - \lfloor 0.3n\rfloor$ はどちらも非負整数で和は $n$ だから，$0$ を $\lfloor 0.3n\rfloor$ 個並べたあと $1$ を並べた系列の型は $P^\star_n$ であり，$P^\star_n$ は長さ $n$ の型である．また $\lfloor 0.3n\rfloor \le 0.3n$ より $P^\star_n(0) \le 0.3$ だから $P^\star_n(1) \ge 0.7$ であり，$P^\star_n \in \mathcal E$ である．よってどの $n \ge 1$ でも $P^\star_n \in \mathcal E_n$ で，第 $2$ の仮定も成り立つ．$Q$ は全点で正だから 定理 11.3.7 が使えて，第 $2$ の主張と合わせて結論を得る．

4. 端数の引き受け手を $a_0 := 0$ にとると丸め型は $P^\star_n(1) = \lfloor 0.7n\rfloor/n$ である．$0.7n = 7n/10$ は，$7$ と $10$ が互いに素だから $n$ が $10$ の倍数のときに限り整数であり，整数でなければ $\lfloor 0.7n\rfloor < 0.7n$ だから $P^\star_n(1) < 0.7$ で，$P^\star_n \notin \mathcal E$ である．$10$ の倍数でない $n$ はいくらでも大きくとれるから，「十分大きいすべての $n$ で $P^\star_n \in \mathcal E_n$」は成り立たない．
:::

第 $3$ と第 $4$ の主張は，端数の引き受け手の選び方が仮定の成否を左右することを示している．制約 $P(1) \ge 0.7$ が緩む側の文字に端数を押し付ければ丸め型は $\mathcal E$ に入り，きつくなる側に押し付ければ入らない．$n = 11$ が後者の例で，$\lfloor 7.7\rfloor/11 = 7/11$ は $0.7$ より小さい．

指数の値 $0.0823$ が言っているのは，$\frac1n\log$ をとった量が $-0.0823$ に近づくということであって，有限の $n$ での確率そのものを与えるものではない．公平なコインを投げて表が $7$ 割以上出るのはめったに起きないが，その「めったに」の速さは，表の割合を $0.7$ に固定した分布が公平なコインからどれだけ隔たっているかだけで決まる．

::: formalization-note
例 11.3.8 の数値に対応する宣言は無い．形式化には，具体的な分布を入れて Sanov の指数を計算した実例が置かれていない．
:::

本節は，経験分布が指定した集合に落ちる確率を測った．測ったのは $Q$ から引いた系列についてであり，集合 $\mathcal E$ は $Q$ とは関わりなく先に決めておいた．次節は $\mathcal E$ にあたるものを，二つの分布のどちらが真かを当てるという目的から決める．そこでも指数に現れるのは相対エントロピーで，型の方法がそのまま効く．
