# 16.5 超立方体の辺等周

面積を決めておいて周の長さをいちばん短くする図形は何か，と問うのが等周問題である．同じ問いを超立方体の頂点の上で立てるのが本節である．$\{0,1\}^n$ の二つの点は，ちょうど $1$ 座標だけ違うときに辺で結ばれているとみる．頂点の集合 $A$ を選ぶと，端点の一方だけが $A$ に入っている辺が決まり，その本数が $A$ の周にあたる．要素数を決めておいて，この本数がどこまで小さくなりうるかを問う．本節は下からの評価を二つ与え，二つを比べる．以下 $\mathcal X = \{0,1\}$ に固定し，$\{0,1\}^n$ の元はビットの列として書く．

::: definition 16.5.1 辺境界
$n \ge 0$ とし，$A \subseteq \{0,1\}^n$ とする．$x \in \{0,1\}^n$ と $i \in \{1,\dots,n\}$ に対し，$x$ の第 $i$ 座標だけを反転して他の座標を変えない点を $x^{(i)}$ と書く．$x \in A$ かつ $x^{(i)} \notin A$ を満たす対 $(x,i)$ の全体を $\partial_{\mathrm e}A$ と書き，$A$ の **辺境界** と呼ぶ．
:::

$\partial_{\mathrm e}$ は辺境界を表す記号であって，第10章 10.4 節 の偏微分とは別である（偏微分はつねに分数の形で関数に当たり，こちらはつねに添字 $\mathrm e$ を伴って集合に当たる）．対 $(x,i)$ と，端点の一方だけが $A$ に入る辺とは一対一に対応する．そのような辺について，$A$ に入っているほうの端点を $x$，二つの端点が食い違う座標の番号を $i$ とすればよい．だから $\lvert\partial_{\mathrm e}A\rvert$ は「$A$ から外へ出ていく辺の本数」である．

::: formalized
`edgeBoundaryCount` (`InformationTheory/Shannon/HypercubeEdge/Boundary.lean`)
:::

::: formalization-note
形式化は辺境界を集合としてではなく，その要素数として直に定めている（本文が $\lvert\partial_{\mathrm e}A\rvert$ と書く数がそれである）．座標の反転にも `flipCoord` (`InformationTheory/Shannon/HypercubeEdge/Boundary.lean`) という名前が与えられている．
:::

::: proposition 16.5.2
$n \ge 0$ とし，$A \subseteq \{0,1\}^n$ とする．$x \in A$ と $i \in \{1,\dots,n\}$ の対 $(x,i)$ のうち $x^{(i)} \in A$ を満たすものの個数と $\lvert\partial_{\mathrm e}A\rvert$ との和は $n\lvert A\rvert$ に等しい．
:::

::: proof
$x \in A$ と $i \in \{1,\dots,n\}$ の対は，$x$ の選び方が $\lvert A\rvert$ 通り，$i$ の選び方が $n$ 通りで，全部で $n\lvert A\rvert$ 個ある．その各々について $x^{(i)}$ は $A$ に入るか入らないかのどちらか一方だから，全体は $x^{(i)} \in A$ を満たす対と $x^{(i)} \notin A$ を満たす対とに分かれる．後者の個数は 定義 16.5.1 より $\lvert\partial_{\mathrm e}A\rvert$ である．
:::

::: formalized
`edge_total_count` (`InformationTheory/Shannon/HypercubeEdge/Boundary.lean`)
:::

::: formalization-note
形式化は $x^{(i)} \in A$ を満たす対の個数にも `internalEdgePairCount` (`InformationTheory/Shannon/HypercubeEdge/Boundary.lean`) という名前を与えていて，宣言はその数と辺境界の要素数との和が $n\lvert A\rvert$ に等しい，という形で述べられている．
:::

以下，本節の主張ブロックでは $\log$ の底を $2$ にとる．立方体の次元 $n$ と $\log_2\lvert A\rvert$ を同じ物差しで比べるためである．

::: theorem 16.5.3 辺等周不等式
$n \ge 0$ とし，$A \subseteq \{0,1\}^n$ を空でない集合とすると
$$
\lvert A\rvert\big(n - \log_2\lvert A\rvert\big) \;\le\; \lvert\partial_{\mathrm e}A\rvert
$$
である．
:::

::: proof
$n = 0$ のときは $\{0,1\}^0$ の元がただ一つで $A$ はその一点だから，$\lvert A\rvert = 1$ と $\log_2\lvert A\rvert = 0$ より左辺は $0$ であり，対 $(x,i)$ をとる $i$ がないので右辺も $0$ である．以下 $n \ge 1$ とする．

$A$ の上の一様分布に従う確率変数 $X$ をとり，$X_i$ を $X$ の第 $i$ 座標とする．$X_1,\dots,X_n$ は 定義 16.1.1 の設定を満たす族である．$X_{\{1,\dots,n\}}$ は $X$ そのもので，とりうる値は $A$ の元だから，そのアルファベットを $A$ にとって 例 1.1.3 を $M = \lvert A\rvert$ で当てると $H(X_{\{1,\dots,n\}}) = \log_2\lvert A\rvert$ である．

まず上から押さえる．定理 16.1.4 を $S = \{1,\dots,n\}$ に当てると $\sum_{i=1}^{n} H(X_i \mid X_{\{1,\dots,i-1\}}) = \log_2\lvert A\rvert$ である．$\{1,\dots,i-1\}$ は $\{1,\dots,n\}\setminus\{i\}$ に含まれるから，補題 16.1.2 に注意して 定理 1.2.4 を当てると，各 $i$ について $H(X_i \mid X_{\{1,\dots,n\}\setminus\{i\}}) \le H(X_i \mid X_{\{1,\dots,i-1\}})$ である．足し合わせると
$$
\sum_{i=1}^{n} H\big(X_i \,\big|\, X_{\{1,\dots,n\}\setminus\{i\}}\big) \;\le\; \log_2\lvert A\rvert
$$
である．

次に左辺を数え直す．番号 $i$ を固定し，$X_{\{1,\dots,n\}\setminus\{i\}}$ のとる値 $y$ を一つとる．$A$ の元で第 $i$ 座標以外が $y$ に一致するものは $1$ 個か $2$ 個で，$2$ 個ならその二つは互いに第 $i$ 座標を反転した関係にある．$y$ のもとでの条件付きエントロピーを，この二つの場合に分けて見る．

1. $2$ 個のとき．$X$ は $A$ の上で一様だから，$y$ のもとでの $X_i$ の条件付き分布は $\{0,1\}$ の上の一様分布である．例 1.1.3 を $M = 2$ で当てて $H(X_i \mid X_{\{1,\dots,n\}\setminus\{i\}} = y) = 1$ であり，この $y$ の確率は $2/\lvert A\rvert$ である．
2. $1$ 個のとき．条件付き分布は一点に集中するから，定義 1.1.1 の和は $-1\log_2 1$ の一項だけになり，値は $0$ である．

定義 1.2.2 は各 $y$ のもとでの値をその確率で平均したものだから，寄与するのは $2$ 個の場合の $y$ だけで，その寄与は $y$ ひとつにつき $2/\lvert A\rvert$ である．そのような $y$ ひとつには $A$ の元が $2$ 個対応し，それらはちょうど，第 $i$ 座標を反転しても $A$ に留まる $A$ の元だから，そのような $y$ の個数を $2$ 倍したものが，そのような元の個数に等しい．したがって
$$
H\big(X_i \,\big|\, X_{\{1,\dots,n\}\setminus\{i\}}\big) \;=\; \frac{\lvert\{\,x \in A \;:\; x^{(i)} \in A\,\}\rvert}{\lvert A\rvert}
$$
である．$i$ について足すと，分子の和は $x^{(i)} \in A$ を満たす対 $(x,i)$ の個数だから，命題 16.5.2 よりそれは $n\lvert A\rvert - \lvert\partial_{\mathrm e}A\rvert$ である．前段の不等式と合わせて
$$
\frac{n\lvert A\rvert - \lvert\partial_{\mathrm e}A\rvert}{\lvert A\rvert} \;\le\; \log_2\lvert A\rvert
$$
を得る．$\lvert A\rvert > 0$ を両辺に掛けて整理すれば主張である．
:::

::: formalized
`edgeBoundary_entropy_sharp` (`InformationTheory/Shannon/HypercubeEdge/BoundarySharp.lean`)
:::

::: example 16.5.4 部分立方体
$n \ge 0$，$0 \le k \le n$ とする．$F \subseteq \{1,\dots,n\}$ を要素数 $n-k$ の座標の集合，$c$ を $F$ から $\{0,1\}$ への関数とし，
$$
A \;:=\; \{\, x \in \{0,1\}^n \;:\; x_i = c(i) \ \ (i \in F) \,\}
$$
とおく．このとき $\lvert A\rvert = 2^k$ かつ $\lvert\partial_{\mathrm e}A\rvert = 2^k(n-k)$ であり，定理 16.5.3 は等号で成り立つ．
:::

::: proof
$A$ の元は $F$ の外の $k$ 個の座標を自由に選んで得られるから $\lvert A\rvert = 2^k$ である．$x \in A$ と座標 $i$ をとる．$i \notin F$ ならば $x^{(i)}$ も $F$ の上で $c$ に一致するので $A$ に属し，$i \in F$ ならば $x^{(i)}$ の第 $i$ 座標は $c(i)$ と違うので $A$ に属さない．したがって外に出る対は $i \in F$ のものに限り，その個数は $\lvert A\rvert\,\lvert F\rvert = 2^k(n-k)$ である．一方 $\log_2 2^k = k$ だから 定理 16.5.3 の左辺は $2^k(n-k)$ であり，両辺が一致する．
:::

節の冒頭の問いに，要素数が $2$ のべきである場合の答えがこれで出た．$n$ を固定すると 定理 16.5.3 の下界は $\lvert A\rvert$ だけで決まるから，$\lvert A\rvert = 2^k$ ならば外へ出る辺の本数は $2^k(n-k)$ 以上であり，例 16.5.4 の部分立方体がちょうどその本数をとる．すなわち最小値は $2^k(n-k)$ である．要素数が $2$ のべきでないときの最小値を，本書は与えない．

もう一つの下界は，エントロピーを経由せず 定理 16.4.2 から出る．そのために，$n$ 個の非負の数の積の $n$ 乗根が相加平均を超えないという古典的な不等式を用意する．本書はこれを 補題 1.1.6 から証明するので，借用ではない．

::: lemma 16.5.5 相加相乗平均の不等式
$n \ge 1$ とし，$t_1,\dots,t_n$ を非負の実数とすると
$$
\Big(\prod_{i=1}^{n} t_i\Big)^{1/n} \;\le\; \frac1n\sum_{i=1}^{n} t_i
$$
である．
:::

::: proof
どれかの $t_i$ が $0$ ならば左辺は $0$ であり，右辺は非負だから成り立つ．以下すべての $t_i$ が正であるとする．1.1 節 が認めたとおり $\log$ は $(0,\infty)$ の上で狭義凹だから，補題 1.1.6 を，重み $w_i = 1/n$，点 $t_i$ ととって当てると
$$
\frac1n\sum_{i=1}^{n}\log t_i \;\le\; \log\Big(\frac1n\sum_{i=1}^{n} t_i\Big)
$$
である．左辺は $\log\big(\prod_{i=1}^{n} t_i\big)^{1/n}$ に等しい．$\log$ が狭義単調だから主張を得る．
:::

::: formalization-note
この補題だけを述べる宣言はない．積の $n$ 乗根を相加平均で押さえる形で `InformationTheory/` の全体を探しても見つからず，形式化は同じ内容を重みつきの一般形として Mathlib から直に引いている．定理 16.5.7 と 定理 16.6.1 に紐付けた宣言が，それぞれその中でこれを使っている．
:::

::: proposition 16.5.6
$n \ge 0$ とし，$A \subseteq \{0,1\}^n$ とすると
$$
\lvert\partial_{\mathrm e}A\rvert + n\lvert A\rvert \;=\; 2\sum_{i=1}^{n}\lvert\pi_{-i}(A)\rvert
$$
である（$\pi_{-i}(A)$ は 定義 16.4.1 の射影である）．
:::

::: proof
番号 $i$ を固定する．$y \in \pi_{-i}(A)$ に対し，$A$ の元で第 $i$ 座標以外が $y$ に一致するものは $1$ 個か $2$ 個である．$1$ 個であるような $y$ の個数を $a_i$，$2$ 個であるような $y$ の個数を $b_i$ と書くと，$\pi_{-i}(A)$ の元はこの二種類に分かれるから $\lvert\pi_{-i}(A)\rvert = a_i + b_i$ であり，$A$ の元をこの分け方で数えて $\lvert A\rvert = a_i + 2b_i$ である．また $x \in A$ の第 $i$ 座標以外を切り詰めたものを $y$ と書くと，$x^{(i)} \notin A$ であることと $y$ が $1$ 個のほうであることとは同じことだから，第 $i$ 座標の向きに外へ出る対の個数は $a_i$ である．よって
$$
a_i + \lvert A\rvert \;=\; a_i + (a_i + 2b_i) \;=\; 2\lvert\pi_{-i}(A)\rvert
$$
である．$i$ について足すと，左辺の第 $1$ 項の和は $\lvert\partial_{\mathrm e}A\rvert$，第 $2$ 項の和は $n\lvert A\rvert$ だから主張を得る．
:::

::: formalized
`edgeBoundary_count_eq` (`InformationTheory/Shannon/HypercubeEdge/Boundary.lean`)
:::

命題 16.5.6 は，辺境界を射影の要素数の言葉に書き換える．そこに 定理 16.4.2 を当てれば，エントロピーを一度も使わない下界が出る．正の整数 $m$ に対し $u \mapsto u^{1/m}$ が $[0,\infty)$ の上で単調非減少であること（$u \mapsto u^m$ の逆写像である）と，正の実数のべき乗の規則，すなわち正の実数 $u$，$v$ と実数 $s$，$t$ について $(uv)^{s} = u^{s}v^{s}$，$u^{s+t} = u^{s}u^{t}$，$(u^{s})^{t} = u^{st}$ が成り立つことを既知とする．単調性を使うのは 定理 16.5.7 の証明と 例 16.6.2 の二箇所で，べき乗の規則は本節と次節の証明が $1/m$ 乗を積や積のべきに通すところである．

::: theorem 16.5.7
$n \ge 1$ とし，$A \subseteq \{0,1\}^n$ を空でない集合とすると
$$
2n\lvert A\rvert^{(n-1)/n} - n\lvert A\rvert \;\le\; \lvert\partial_{\mathrm e}A\rvert
$$
である．
:::

::: proof
補題 16.5.5 を $t_i = \lvert\pi_{-i}(A)\rvert$ ととって当てると
$$
\sum_{i=1}^{n}\lvert\pi_{-i}(A)\rvert \;\ge\; n\Big(\prod_{i=1}^{n}\lvert\pi_{-i}(A)\rvert\Big)^{1/n}
$$
である．$\mathcal X = \{0,1\}$ として 定理 16.4.2 を当てると $\prod_{i=1}^{n}\lvert\pi_{-i}(A)\rvert \ge \lvert A\rvert^{\,n-1}$ であり，$1/n$ 乗が単調非減少だから右辺は $n\lvert A\rvert^{(n-1)/n}$ 以上である．命題 16.5.6 と合わせると $\lvert\partial_{\mathrm e}A\rvert + n\lvert A\rvert \ge 2n\lvert A\rvert^{(n-1)/n}$ であり，移項すれば主張を得る．
:::

::: formalized
`edgeBoundary_ge_AMGM` (`InformationTheory/Shannon/HypercubeEdge/Boundary.lean`)
:::

::: formalization-note
宣言は移項する前の形（$2n\lvert A\rvert^{(n-1)/n} \le \lvert\partial_{\mathrm e}A\rvert + n\lvert A\rvert$）で述べられている．指数は 定理 16.4.2 の宣言と同じく自然数の引き算で書かれていて $n = 0$ でも両辺が定まる．本文が $n \ge 1$ を仮定するのは，$(n-1)/n$ を分数として読むためである．
:::

下界が二つ出たので，どちらが強いかを決めておく．

::: proposition 16.5.8
$n \ge 1$ とし，$A \subseteq \{0,1\}^n$ を空でない集合とすると
$$
2n\lvert A\rvert^{(n-1)/n} - n\lvert A\rvert \;\le\; \lvert A\rvert\big(n - \log_2\lvert A\rvert\big)
$$
である．すなわち 定理 16.5.3 の下界は 定理 16.5.7 の下界以上である．等号が成り立つのは $\lvert A\rvert = 1$ のときと $\lvert A\rvert = 2^n$ のときに限る．
:::

::: proof
$A$ は空でなく $\{0,1\}^n$ に含まれるから $1 \le \lvert A\rvert \le 2^n$ であり，$s := 1 - \log_2\lvert A\rvert / n$ とおくと $0 \le s \le 1$ である．$\log_2\lvert A\rvert = n(1-s)$ だから $\lvert A\rvert^{-1/n} = 2^{-(1-s)}$ であり，
$$
2n\lvert A\rvert^{(n-1)/n} - n\lvert A\rvert
  \;=\; 2n\lvert A\rvert\,\lvert A\rvert^{-1/n} - n\lvert A\rvert
  \;=\; n\lvert A\rvert\big(2^{s} - 1\big),
\qquad
\lvert A\rvert\big(n - \log_2\lvert A\rvert\big) \;=\; n\lvert A\rvert\,s
$$
である．$n\lvert A\rvert > 0$ だから，示すべきは $0 \le s \le 1$ に対する $2^{s} \le 1 + s$ である．1.1 節 が認めたとおり $\log_2$ は狭義凹だから，補題 1.1.6 を，$2$ 点 $1$ と $2$，重み $1-s$ と $s$ ととって当てると
$$
\log_2(1+s) \;=\; \log_2\big((1-s)\cdot 1 + s\cdot 2\big) \;\ge\; (1-s)\log_2 1 + s\log_2 2 \;=\; s
$$
である．$s = \log_2 2^{s}$ であり $\log_2$ は狭義単調だから，$1 + s \ge 2^{s}$ を得る．等号については，$0 < s < 1$ のときは 補題 1.1.6 の重みが二つとも正で点 $1$ と $2$ が違うから狭義であり，$s = 0$ と $s = 1$ のときは重みの一方が $0$ で等号である．$s = 0$ は $\lvert A\rvert = 2^n$，$s = 1$ は $\lvert A\rvert = 1$ にあたる．
:::

::: formalization-note
二つの下界の強弱を述べる宣言はない．辺境界の要素数を結論に含む宣言をすべて開いて確かめた．機械検証が及ぶのは 定理 16.5.3 と 定理 16.5.7 のそれぞれまでで，二つを比べる段は本文の側にある．
:::

**二つの下界を数で比べる.** $n = 10$ とし，$A$ を $5$ 個の座標を固定して得られる $32$ 点の部分立方体にとる．例 16.5.4 より $\lvert\partial_{\mathrm e}A\rvert = 32 \times 5 = 160$ である．定理 16.5.3 の下界は $32(10-5) = 160$ で真の値に一致し，定理 16.5.7 の下界は $2 \times 10 \times 32^{9/10} - 10 \times 32 = 452.548\ldots - 320 = 132.548\ldots$ で，$27$ ほど届かない．両端では二つは一致する．$\lvert A\rvert = 1$ ではどちらも $n$，$\lvert A\rvert = 2^n$ ではどちらも $0$ である．

二つの下界は道が違う．弱いほうの 定理 16.5.7 は，命題 16.5.6 で辺境界を射影の要素数に書き換えてから 定理 16.4.2 と 補題 16.5.5 に渡すので，最後まで見ているのは要素数だけである．強いほうの 定理 16.5.3 は，射影を経由せずに 定理 16.1.4 の分解をそのまま使い，$1$ 座標だけを残したときの条件付きエントロピーが，条件の値ごとに $0$ か $1$ しかとらないことを数え上げに直す．エントロピーで数えるほうが弱くならない下界を出し，両端の $\lvert A\rvert = 1$ と $\lvert A\rvert = 2^n$ を除けば真に強い，というのが本節の結論である．次節は 補題 16.5.5 のほうをもう一度使う．当てる相手は集合の要素数ではなく，行列の行列式である．
