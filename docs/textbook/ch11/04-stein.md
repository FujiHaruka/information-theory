# 11.4 仮説検定と Stein の補題

手元に長さ $n$ の系列が一つある．それが分布 $P$ から出たのか，分布 $Q$ から出たのかを当てたい．二つの分布はどちらも分かっていて，分からないのはどちらが真かだけである．この形の問題を **仮説検定** と呼び，$P$ のほうを **帰無仮説**，$Q$ のほうを **対立仮説** と呼ぶ．前節までの道具はそのまま使える．系列を見て決めるとは $\mathcal X^n$ を二つに分けることであり，分けた片方の確率を $P^n$ と $Q^n$ の両方で測るのだから，測る対象は前節までと同じ型の集まりだからである．

答え方を決めると，間違え方は二通り出る．真が $P$ なのに $Q$ と答える誤りと，真が $Q$ なのに $P$ と答える誤りである．どちらも $0$ にはできない（例 11.4.2）ので，一方を一定の水準に抑えたうえで他方を最小にする，という形に問題を立て直す．抑えるほうを固定すると，最小にしたほうは $n$ とともに指数で落ちる．その指数を下から $D(P\,\|\,Q)$ で押さえるのが Stein の補題の達成可能性で，上から押さえるのがその逆である．本節はこの二つを示す．

相対エントロピーの三つめの読み方がここで出る．1.6 節では「$q$ だと思い込んで符号化したために余計に払う符号長」，前節では「$Q$ から見て型 $P$ の系列が出にくい度合い」だった．本節では「$P$ と $Q$ を見分ける難しさ」になる．$D(P\,\|\,Q)$ が大きいほど二つは見分けやすく，第二種の誤りは速く落ちる．本節の主張がその速さを測る．

## 検定と 2 種類の誤り

::: definition 11.4.1 検定と 2 種類の誤り
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の分布，$P^n$，$Q^n$ をそれぞれの $n$ 重の積分布とし，$n \ge 1$ とする．部分集合 $\mathcal A_n \subseteq \mathcal X^n$ を一つ決め，系列 $x$ が $\mathcal A_n$ に属するときに $P$ を，属さないときに $Q$ を答えることにする．この $\mathcal A_n$ を **受容域**，答え方そのものを **検定** と呼ぶ．検定の **第一種の誤り** と **第二種の誤り** を
$$
\alpha_n(\mathcal A_n) \;:=\; P^n\big(\mathcal A_n^{\mathrm c}\big),
\qquad
\beta_n(\mathcal A_n) \;:=\; Q^n\big(\mathcal A_n\big)
$$
で定める（$\mathcal A_n^{\mathrm c} := \mathcal X^n \setminus \mathcal A_n$）．
:::

第一種の誤りは，真の分布が $P$ であるのに $Q$ と答えてしまう確率であり，第二種の誤りは，真の分布が $Q$ であるのに $P$ と答えてしまう確率である．受容域を広げれば $P$ と答えやすくなるので，第一種の誤りは大きくならず，第二種の誤りは小さくならない．二つはこの向きに引き合う．記号 $\alpha$，$\beta$ は仮説検定の標準的な書き方で，第3章 3.1 節が二状態のマルコフ情報源の遷移確率に使ったものと字が重なるが，あちらはつねに裸で現れ，本章のものはつねに長さの添字と受容域の引数をとるので見分けられる．

::: formalized
`steinBetaSet` (`InformationTheory/Shannon/Stein/OptimalExponent.lean`)
:::

::: example 11.4.2 極端な二つの検定
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布，$n \ge 1$ とし，$\alpha_n$，$\beta_n$ を 定義 11.4.1 のとおりとすると，次の三つが成り立つ．

1. $\mathcal A_n := \mathcal X^n$ ととると $\alpha_n(\mathcal A_n) = 0$，$\beta_n(\mathcal A_n) = 1$ である．
2. $\mathcal A_n := \varnothing$ ととると $\alpha_n(\mathcal A_n) = 1$，$\beta_n(\mathcal A_n) = 0$ である．
3. $\alpha_n(\mathcal A_n) = 0$ かつ $\beta_n(\mathcal A_n) = 0$ となる $\mathcal A_n \subseteq \mathcal X^n$ は無い．
:::

::: proof
1. $\mathcal A_n = \mathcal X^n$ なら $\mathcal A_n^{\mathrm c} = \varnothing$ だから $\alpha_n(\mathcal A_n) = P^n(\varnothing) = 0$ であり，$\beta_n(\mathcal A_n) = Q^n(\mathcal X^n) = 1$ である．

2. $\mathcal A_n = \varnothing$ なら $\mathcal A_n^{\mathrm c} = \mathcal X^n$ だから $\alpha_n(\mathcal A_n) = P^n(\mathcal X^n) = 1$ であり，$\beta_n(\mathcal A_n) = Q^n(\varnothing) = 0$ である．

3. $P$ は全点で正だから，どの $x \in \mathcal X^n$ でも $P^n(\{x\}) = \prod_{i<n}P(x_i) > 0$ である．したがって $\alpha_n(\mathcal A_n) = P^n(\mathcal A_n^{\mathrm c}) = 0$ となるのは $\mathcal A_n^{\mathrm c} = \varnothing$ のとき，すなわち $\mathcal A_n = \mathcal X^n$ のときに限る．そのとき第 $1$ の主張より $\beta_n(\mathcal A_n) = 1$ であって $0$ ではない．
:::

第 $3$ の主張は，どちらの誤りも $0$ にする検定が無いことを言っている．そこで一方を一定の水準に抑え，もう一方をできるだけ小さくする．抑えるほうを第一種の誤りにとるのが仮説検定の作法であり，$P$ と $Q$ の扱いはこの時点で非対称になる．帰無仮説と対立仮説という名前の違いも，この非対称に対応している．

::: definition 11.4.3 水準 $\varepsilon$ の最良の第二種の誤り
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の分布，$n \ge 1$，$\varepsilon \ge 0$ とし，$\alpha_n$，$\beta_n$ を 定義 11.4.1 のとおりとする．第一種の誤りを $\varepsilon$ 以下に抑える受容域すべてにわたる第二種の誤りの下限を
$$
\beta^*_n(\varepsilon) \;:=\; \inf\big\{\, \beta_n(\mathcal A_n) \;:\;
  \mathcal A_n \subseteq \mathcal X^n,\ \alpha_n(\mathcal A_n) \le \varepsilon \,\big\}
$$
と書き，**水準 $\varepsilon$ の最良の第二種の誤り** と呼ぶ．
:::

下限をとる集合は空ではない．例 11.4.2 の第 $1$ の主張より $\mathcal A_n = \mathcal X^n$ はどの $\varepsilon \ge 0$ でも条件を満たすからである．$\beta^*_n(\varepsilon)$ の星印は，前節で置いた約束のとおり最適化した値であることを表す（分布には $\star$ を，値には $*$ を使い分ける）．水準 $\varepsilon$ を大きくとるほど条件を満たす受容域は増えるので，$\beta^*_n(\varepsilon)$ は大きくならない．以下では水準を固定したまま $n$ を大きくして，この値がどれだけ速く $0$ に向かうかを測る．

::: formalized
`steinOptimalBeta` (`InformationTheory/Shannon/Stein/OptimalExponent.lean`)
:::

## 達成可能性

まず下から，すなわち $-\frac1n\log\beta^*_n(\varepsilon)$ を $D(P\,\|\,Q)$ にいくらでも近いところまで押し上げる検定があることを示す．受容域は型の方法で作る．長さ $n$ の型 $P'$ ごとに，$P'$ で平均した対数尤度比 $\sum_a P'(a)\log\frac{P(a)}{Q(a)}$ を計算し，それが $D(P\,\|\,Q)$ に近い型の型類だけを集める．型類の中では確率が一定である（命題 11.1.4）ので，この一つの数だけで型類全体の $P^n$ と $Q^n$ の比が決まり，第二種の誤りがそのまま抑えられる．第一種の誤りのほうは，型が真の分布に近い系列の確率が $1$ に近づくこと，すなわち 第2章 定理 2.4.3 から出る．

::: theorem 11.4.4 Stein の補題の達成可能性
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布，$\varepsilon \in (0,1)$，$\delta > 0$ とし，$\beta^*_n$ を 定義 11.4.3 のとおりとする．このとき，どの $n \ge 1$ でも $\beta^*_n(\varepsilon) > 0$ であり，十分大きいすべての $n$ について
$$
-\frac1n\log\beta^*_n(\varepsilon) \;\ge\; D(P\,\|\,Q) - \delta
$$
である（$D$ は 1.6 節の相対エントロピー）．
:::

::: proof
まず $\beta^*_n(\varepsilon)$ が正であることを見る．$\alpha_n(\mathcal A_n) \le \varepsilon$ を満たす受容域 $\mathcal A_n$ をとると，$\varepsilon < 1$ より $P^n(\mathcal A_n) = 1 - \alpha_n(\mathcal A_n) > 0$ だから $\mathcal A_n$ は空でなく，$Q$ が全点で正だから $\beta_n(\mathcal A_n) = Q^n(\mathcal A_n) > 0$ である．$\mathcal X^n$ の部分集合は有限個しかないので，定義 11.4.3 の下限は有限個の正の数の最小値であり，正である．

次に受容域を作る．$P$ と $Q$ は全点で正だから，どの文字でも $\log\frac{P(a)}{Q(a)}$ は有限な数である．長さ $n$ の型 $P'$ のうち
$$
\Big\lvert \sum_{a \in \mathcal X}P'(a)\log\frac{P(a)}{Q(a)} \;-\; D(P\,\|\,Q) \Big\rvert \;\le\; \delta
$$
を満たすものを集め，その型類（定義 11.1.1）を合わせたものを $\mathcal A_n$ とする．

第二種の誤りを抑える．$x \in \mathcal A_n$ をとり $P' := \hat P_x$ とおくと，$P'$ は上の条件を満たす長さ $n$ の型である．命題 11.1.4 を $Q$ について，および $P$ について当てると
$$
Q^n\big(\{x\}\big) = \exp\Big(-n\big(H(P') + D(P'\,\|\,Q)\big)\Big),
\qquad
P^n\big(\{x\}\big) = \exp\Big(-n\big(H(P') + D(P'\,\|\,P)\big)\Big)
$$
であり，比をとると $Q^n(\{x\}) = P^n(\{x\})\exp\big(-n(D(P'\,\|\,Q) - D(P'\,\|\,P))\big)$ である．相対エントロピーの定義（1.6 節）から
$$
D(P'\,\|\,Q) - D(P'\,\|\,P)
  \;=\; \sum_{a}P'(a)\log\frac{P'(a)}{Q(a)} \;-\; \sum_{a}P'(a)\log\frac{P'(a)}{P(a)}
  \;=\; \sum_{a}P'(a)\log\frac{P(a)}{Q(a)}
$$
である（$P'(a) = 0$ の文字では三つの項がすべて $0$ である）．$\mathcal A_n$ の定め方よりこの値は $D(P\,\|\,Q) - \delta$ 以上だから，$Q^n(\{x\}) \le P^n(\{x\})\,e^{-n(D(P\,\|\,Q)-\delta)}$ である．これを $x \in \mathcal A_n$ について足し合わせ，$P^n(\mathcal A_n) \le 1$ を使うと
$$
\beta_n(\mathcal A_n) \;=\; Q^n(\mathcal A_n) \;\le\; e^{-n(D(P\,\|\,Q)-\delta)}
$$
を得る．

第一種の誤りを抑える．正の実数 $t$ を一つとり，第2章の情報源の分布を $P$ として，幅 $t$ の強典型集合 $A^{*(n)}_t$（定義 2.4.1）を考える（$P$ は全点で正だから，2.4 節の設定を満たす）．$x \in A^{*(n)}_t$ ならどの文字でも $\lvert \hat P_x(a) - P(a)\rvert \le t$ であり，$D(P\,\|\,Q) = \sum_a P(a)\log\frac{P(a)}{Q(a)}$ だから，三角不等式より
$$
\Big\lvert \sum_{a}\hat P_x(a)\log\frac{P(a)}{Q(a)} - D(P\,\|\,Q) \Big\rvert
  \;=\; \Big\lvert \sum_{a}\big(\hat P_x(a) - P(a)\big)\log\frac{P(a)}{Q(a)} \Big\rvert
  \;\le\; t\sum_{a}\Big\lvert\log\frac{P(a)}{Q(a)}\Big\rvert
$$
である．右端は $t$ に比例し，和は $P$ と $Q$ だけで決まる有限の数だから，$t$ を小さくとれば右端を $\delta$ 以下にできる．そのような $t$ を一つ選んでおく．すると $x \in A^{*(n)}_t$ の型 $\hat P_x$ は $\mathcal A_n$ を定める条件を満たすので $x \in \mathcal T_n(\hat P_x) \subseteq \mathcal A_n$ であり，$A^{*(n)}_t \subseteq \mathcal A_n$ である．第2章 定理 2.4.3 より $P^n(A^{*(n)}_t) \to 1$ だから
$$
\alpha_n(\mathcal A_n) \;=\; P^n\big(\mathcal A_n^{\mathrm c}\big)
  \;\le\; P^n\big((A^{*(n)}_t)^{\mathrm c}\big) \;\longrightarrow\; 0
$$
であり，十分大きい $n$ で $\alpha_n(\mathcal A_n) \le \varepsilon$ である．

その $n$ については $\mathcal A_n$ が 定義 11.4.3 の下限をとる範囲に入るから
$$
\beta^*_n(\varepsilon) \;\le\; \beta_n(\mathcal A_n) \;\le\; e^{-n(D(P\,\|\,Q)-\delta)}
$$
である．$\beta^*_n(\varepsilon)$ は正だから対数がとれ，$\log$ は単調増加だから $\log\beta^*_n(\varepsilon) \le -n\big(D(P\,\|\,Q)-\delta\big)$ であり，両辺を $-n$ で割れば主張を得る．
:::

::: formalized
`steinOptimalBeta_log_ge_of_achievability` (`InformationTheory/Shannon/Stein/OptimalExponent.lean`)
:::

::: formalization-note
本文の証明は受容域を型の方法で作り，第一種の誤りを 第2章 定理 2.4.3 で押さえた．形式化は別の道筋をとる．対数尤度比の相加平均に大数の強法則を当て，その平均が $D(P\,\|\,Q)$ に近い系列の全体 `steinTypicalSet` (`InformationTheory/Shannon/Stein/Achievability.lean`) を受容域にとる．定理そのものは同じで，証明の道筋だけが違う．なお宣言は情報源を確率変数の列の形で受け取るので，その像が積分布になるという，設定を翻訳するための仮定がいくつか付いている．
:::

右辺に $\varepsilon$ が現れないことに注意しておく．水準を $0$ より大きい範囲でどれだけ厳しくとっても，$-\frac1n\log\beta^*_n(\varepsilon)$ は $D(P\,\|\,Q)$ にいくらでも近いところまで下から押さえられる，というのが 定理 11.4.4 である．水準 $\varepsilon$ が効くのは，この不等式が成り立ちはじめる $n$ の大きさのほうである．上の証明で $\varepsilon$ を使ったのは，第一種の誤りが $\varepsilon$ を下回る $n$ をとるところだけだった．

## 逆

達成可能性は，指数 $D(P\,\|\,Q)$ に届く検定があることを言った．逆は，どの検定もそれを大きくは超えられないことを言う．道具は 定理 1.8.1，すなわち像測度をとると相対エントロピーは増えない，である．受容域に入るかどうかだけを見る写像で $\mathcal X^n$ を二点に潰すと，二点の上の相対エントロピーが $D(P^n\,\|\,Q^n)$ 以下になる．右辺を先に計算しておく．

::: lemma 11.4.5
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布，$P^n$，$Q^n$ をそれぞれの $n$ 重の積分布とし，$n \ge 1$ とすると
$$
D\big(P^n\,\big\|\,Q^n\big) \;=\; n\,D(P\,\|\,Q)
$$
である（$D$ は 1.6 節の相対エントロピー）．
:::

::: proof
$P$ と $Q$ は全点で正だから，どの $x \in \mathcal X^n$ でも $P^n(\{x\}) = \prod_{i<n}P(x_i)$ と $Q^n(\{x\})$ は正で，どの対数も有限な数である．積の対数は和だから，相対エントロピーの定義（1.6 節）より
$$
D\big(P^n\,\big\|\,Q^n\big)
  \;=\; \sum_{x \in \mathcal X^n}P^n\big(\{x\}\big)\sum_{i=0}^{n-1}\log\frac{P(x_i)}{Q(x_i)}
  \;=\; \sum_{i=0}^{n-1}\ \sum_{x \in \mathcal X^n}P^n\big(\{x\}\big)\log\frac{P(x_i)}{Q(x_i)}
$$
である（有限個の項の和なので順序を入れ替えてよい）．$i$ を一つ固定し，内側の和を $x_i$ の値で分類する．$x_i = a$ を満たす $x$ にわたる $P^n(\{x\})$ の和は，$P(a)$ に残りの座標についての和 $\prod_{j \ne i}\sum_{b}P(b) = 1$ を掛けたもの，すなわち $P(a)$ である．よって内側の和は
$$
\sum_{a \in \mathcal X}P(a)\log\frac{P(a)}{Q(a)} \;=\; D(P\,\|\,Q)
$$
に等しい．これが $i$ に依らないので，$i$ について足すと $n\,D(P\,\|\,Q)$ になる．
:::

::: formalized
`klDiv_pi_eq_n_smul` (`InformationTheory/Shannon/Stein/Achievability.lean`)
:::

::: theorem 11.4.6 Stein の補題の逆
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布，$\varepsilon \in (0,1)$，$n \ge 1$ とし，$\beta^*_n$ を 定義 11.4.3 のとおりとすると
$$
-\frac1n\log\beta^*_n(\varepsilon)
  \;\le\; \frac{D(P\,\|\,Q)}{1-\varepsilon} \;+\; \frac{\log 2}{n\,(1-\varepsilon)}
$$
である（$D$ は 1.6 節の相対エントロピー）．
:::

::: proof
まず，$\alpha_n(\mathcal A_n) \le \varepsilon$ を満たす受容域 $\mathcal A_n \subseteq \mathcal X^n$ を一つ固定し，$\beta_n(\mathcal A_n)$ について同じ形の不等式を示す．

$\mathcal A_n = \mathcal X^n$ のときは $\beta_n(\mathcal A_n) = 1$ で $-\frac1n\log\beta_n(\mathcal A_n) = 0$ であり，右辺は 定理 1.6.1 より非負だから不等式は成り立つ．以下 $\mathcal A_n \ne \mathcal X^n$ とする．$\alpha_n(\mathcal A_n) \le \varepsilon < 1$ より $P^n(\mathcal A_n) = 1 - \alpha_n(\mathcal A_n) > 0$ だから $\mathcal A_n$ は空でなく，$Q$ が全点で正だから $Q^n(\mathcal A_n)$ と $Q^n(\mathcal A_n^{\mathrm c})$ はどちらも正である．

受容域に入るかどうかだけを見る写像 $f : \mathcal X^n \to \{0,1\}$ を，$x \in \mathcal A_n$ のとき $f(x) := 1$，そうでないとき $f(x) := 0$ で定める．像測度（定理 1.8.1）は $\{0,1\}$ 上の分布で，$f_*P^n$ は $1$ に $P^n(\mathcal A_n)$，$0$ に $P^n(\mathcal A_n^{\mathrm c})$ を与え，$f_*Q^n$ は $1$ に $Q^n(\mathcal A_n)$，$0$ に $Q^n(\mathcal A_n^{\mathrm c})$ を与える．定理 1.8.1 と 補題 11.4.5 より
$$
P^n(\mathcal A_n)\log\frac{P^n(\mathcal A_n)}{Q^n(\mathcal A_n)}
  \;+\; P^n\big(\mathcal A_n^{\mathrm c}\big)\log\frac{P^n(\mathcal A_n^{\mathrm c})}{Q^n(\mathcal A_n^{\mathrm c})}
  \;=\; D\big(f_*P^n\,\big\|\,f_*Q^n\big)
  \;\le\; D\big(P^n\,\big\|\,Q^n\big) \;=\; n\,D(P\,\|\,Q)
$$
である．

左辺を下から抑える．$Q^n(\mathcal A_n^{\mathrm c}) \le 1$ だから第 $2$ 項は $P^n(\mathcal A_n^{\mathrm c})\log P^n(\mathcal A_n^{\mathrm c})$ 以上であり，第 $1$ 項は $P^n(\mathcal A_n)\log P^n(\mathcal A_n) - P^n(\mathcal A_n)\log Q^n(\mathcal A_n)$ に等しい．$P^n(\mathcal A_n^{\mathrm c}) = 1 - P^n(\mathcal A_n)$ だから，二つを合わせると左辺は
$$
-H_b\big(P^n(\mathcal A_n)\big) \;-\; P^n(\mathcal A_n)\log Q^n(\mathcal A_n)
$$
以上である（$H_b$ は 例 1.1.2 の二値エントロピー関数）．$H_b$ の値は $2$ 点の上の分布のエントロピーだから 定理 1.1.5 より $\log 2$ 以下であり，よって
$$
-P^n(\mathcal A_n)\log Q^n(\mathcal A_n) \;\le\; n\,D(P\,\|\,Q) + \log 2
$$
である．

$Q^n(\mathcal A_n) \le 1$ より $-\log Q^n(\mathcal A_n) \ge 0$ であり，$P^n(\mathcal A_n) = 1 - \alpha_n(\mathcal A_n) \ge 1-\varepsilon > 0$ だから
$$
(1-\varepsilon)\big(-\log Q^n(\mathcal A_n)\big)
  \;\le\; -P^n(\mathcal A_n)\log Q^n(\mathcal A_n)
  \;\le\; n\,D(P\,\|\,Q) + \log 2
$$
である．両辺を $n(1-\varepsilon)$ で割ると，$\beta_n(\mathcal A_n) = Q^n(\mathcal A_n)$ だから
$$
-\frac1n\log\beta_n(\mathcal A_n)
  \;\le\; \frac{D(P\,\|\,Q)}{1-\varepsilon} + \frac{\log 2}{n\,(1-\varepsilon)}
$$
を得る．

最後に $\beta^*_n(\varepsilon)$ に移る．$\mathcal X^n$ の部分集合は有限個しかないから，定義 11.4.3 の下限は最小値であり，$\alpha_n(\mathcal A_n) \le \varepsilon$ を満たすある $\mathcal A_n$ で $\beta_n(\mathcal A_n) = \beta^*_n(\varepsilon)$ となる．その $\mathcal A_n$ に上で示したことを当てればよい．
:::

::: formalized
`steinOptimalBeta_log_le_of_converse` (`InformationTheory/Shannon/Stein/OptimalExponent.lean`)
:::

上界には因子 $\frac1{1-\varepsilon}$ が残っている．出どころは，第一種の誤りを $\varepsilon$ まで許したために，$-\log Q^n(\mathcal A_n)$ に掛かる重み $P^n(\mathcal A_n)$ が $1$ から $1-\varepsilon$ まで下がりうることである．水準を緩めるほどこの因子は大きくなり，上界は $D(P\,\|\,Q)$ から離れる．達成可能性の側（定理 11.4.4）が $\varepsilon$ に依らなかったのと対照的である．

::: corollary 11.4.7 Chernoff–Stein の補題
$\mathcal X$ を空でない有限アルファベット，$P$，$Q$ を $\mathcal X$ 上の全点で正の分布，$\varepsilon \in (0,1)$ とし，$\beta^*_n$ を 定義 11.4.3 のとおりとすると
$$
D(P\,\|\,Q)
  \;\le\; \liminf_{n \to \infty}\Big(-\frac1n\log\beta^*_n(\varepsilon)\Big)
  \;\le\; \limsup_{n \to \infty}\Big(-\frac1n\log\beta^*_n(\varepsilon)\Big)
  \;\le\; \frac{D(P\,\|\,Q)}{1-\varepsilon}
$$
である（$D$ は 1.6 節の相対エントロピー）．
:::

::: proof
定理 11.4.4 より，どの $\delta > 0$ についても，十分大きいすべての $n$ で $-\frac1n\log\beta^*_n(\varepsilon) \ge D(P\,\|\,Q) - \delta$ である．よって下極限は $D(P\,\|\,Q) - \delta$ 以上であり，$\delta > 0$ は任意だから $D(P\,\|\,Q)$ 以上である．

定理 11.4.6 より，どの $n \ge 1$ についても $-\frac1n\log\beta^*_n(\varepsilon) \le \frac{D(P\,\|\,Q)}{1-\varepsilon} + \frac{\log 2}{n(1-\varepsilon)}$ である．第 $2$ 項は $n \to \infty$ で $0$ に収束するから，上極限は $\frac{D(P\,\|\,Q)}{1-\varepsilon}$ 以下である．下極限が上極限以下であることと合わせて，三つの不等式を得る．
:::

::: formalization-note
系 11.4.7 の両側の不等式は 定理 11.4.4 と 定理 11.4.6 の形でそれぞれ単独に形式化されているが，二つを合わせた挟み込みに対応する単独の宣言は無い．上端が $\varepsilon$ に依らず $D(P\,\|\,Q)$ になる形も形式化されていない．それに近いのは `steinOptimalBeta_log_le_of_strong_converse` (`InformationTheory/Shannon/StrongStein.lean`) で，こちらは $\varepsilon$ で割る因子を持たないかわりに，結論の右端に第一種の誤りに関わる補正項が残っている．
:::

本書が示したのは，水準 $\varepsilon$ を固定したときのこの挟み込みまでである．上端が $D(P\,\|\,Q)$ に一致すること，すなわち Chernoff–Stein の補題の通常の述べ方は示していない．$\varepsilon$ を $0$ に近づけると右端は $D(P\,\|\,Q)$ に近づくので，水準を厳しくとるほど上下の隔たりは狭くなる．

## 数値で見る

::: example 11.4.8 二値の数値
$\mathcal X = \{0,1\}$ とし，$P$ を $P(0) = 0.1$，$P(1) = 0.9$ で定まる分布，$Q$ を $Q(0) = Q(1) = 1/2$ で定まる分布，$\varepsilon := 0.05$ とし，$\beta^*_n$ を 定義 11.4.3 のとおりとすると，次の三つが成り立つ．

1. $D(P\,\|\,Q)$ の値は約 $0.3681$ ナットである．
2. $D(P\,\|\,Q) \le \liminf_n\big(-\frac1n\log\beta^*_n(0.05)\big) \le \limsup_n\big(-\frac1n\log\beta^*_n(0.05)\big) \le D(P\,\|\,Q)/0.95$ であり，右端の値は約 $0.3874$ である．
3. $n = 100$ のときの 定理 11.4.6 の右辺の値は約 $0.3947$ である．
:::

::: proof
1. 例 11.2.4 の第 $1$ の主張より $D(P\,\|\,Q) = \log 2 - H_b(0.1)$ である（$H_b$ は 例 1.1.2 の二値エントロピー関数）．$H_b(0.1) = 0.32508\ldots$，$\log 2 = 0.69314\ldots$ だから，値は $0.36806\ldots$ である．

2. $P$ と $Q$ はどちらも全点で正で $0.05 \in (0,1)$ だから，系 11.4.7 を $\varepsilon := 0.05$ ととって当てると挟み込みを得る．右端の値は第 $1$ の主張より $0.36806\ldots/0.95 = 0.38743\ldots$ である．

3. 定理 11.4.6 の右辺は $\frac{D(P\,\|\,Q)}{0.95} + \frac{\log 2}{100 \times 0.95} = 0.38743\ldots + 0.00729\ldots = 0.39473\ldots$ である．
:::

この $P$ は 例 11.2.4 と同じ偏ったコインである．系 11.4.7 が指数に与える上下の隔たりは $0.02$ ほどで，水準 $\varepsilon$ を $0.05$ より緩めるとこの隔たりは広がる．有限の $n$ での上界（第 $3$ の主張）が極限の上界より大きいのは 定理 11.4.6 の第 $2$ 項のぶんで，$n$ を大きくすればその差は $0$ に向かう．

::: formalization-note
例 11.4.8 の数値に対応する宣言は無い．形式化には，具体的な分布を入れて Stein の補題の指数を計算した実例が置かれていない．例 11.4.8 に付した証明が，この主張の保証のすべてである．
:::

本節は第一種の誤りを水準で抑え，第二種の誤りだけを小さくした．二つの誤りを同時に小さくしたいときには，どちらか一方を優先する理由がなくなり，指数も $D(P\,\|\,Q)$ ではない別の量になる．それを次節で扱う．
