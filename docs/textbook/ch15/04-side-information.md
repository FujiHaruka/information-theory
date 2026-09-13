# 15.4 副情報の値打ち

第5章 定理 5.4.4 は，賭ける前に副情報 $Y$ を観測できるようになったとき，最適倍加率の増分がちょうど相互情報量 $I(X;Y)$ に等しいと述べた．情報の値打ちがそのまま賭けの取り分になる，という等式である．市場でも同じ問いが立つ．株価比を見る前に何かを知ることができるなら，その知識に応じてポートフォリオを組み替えられるはずで，増分がいくらになるかを一つの数で言いたい．本節が示すのは等式ではなく，増分が $I(X;Y)$ を超えないという上からの評価である．等式が評価に弱まる場所は，証明を第5章のそれと並べると見える．

::: definition 15.4.1 条件付き倍加率
$m \ge 1$ とし，$\mathcal X$ を株価比（定義 15.1.1）からなる空でない有限集合，$\mathcal Y$ を空でない有限集合とする．$p(y)$ を $\mathcal Y$ 上の分布，各 $y \in \mathcal Y$ について $p(\cdot \mid y)$ を $\mathcal X$ 上の分布とし，$(X, Y)$ を $\mathcal X \times \mathcal Y$ に値をとる対で，その同時分布が $p(x,y) = p(y)\,p(x \mid y)$ であるものとする．各 $y \in \mathcal Y$ について $b(\cdot \mid y)$ をポートフォリオ（定義 15.1.2）とし，$y$ を動かしたこの族をまとめて $b$ と書く．**条件付き倍加率** を
$$
W(b \mid Y) \;:=\; \sum_{y \in \mathcal Y} p(y)\, W\big(b(\cdot \mid y),\, p(\cdot \mid y)\big)
$$
で定める（$W$ は 定義 15.1.4 の倍加率である）．$\mathcal Y$ 上の分布と条件付き分布は記号に書かないが，どちらも固定されているものとする．
:::

::: formalized
`condGrowthRate` (`InformationTheory/Shannon/Portfolio/SideInformation.lean`)
:::

$Y$ は第5章 5.4 節 の副情報と同じ役で，その期の株価比 $X$ を見る前に観測できるものである．条件付き倍加率は，$Y = y$ を観測してからその場に応じたポートフォリオで運用したときの倍加率を，$y$ の出方で平均したものであり，第5章 定義 5.4.1 とまったく同じ作り方をしている．違いは二つある．一つは倍加率が 定義 15.1.4 の市場のそれになったことで，もう一つは仮定である．第5章 定義 5.4.1 は同時分布がすべての点で正であることを課したが，本節は課さない．第5章がそれを課したのは，条件付き分布が一点で $0$ をとると条件付きの比例賭けが 定義 5.1.1 の正値性を満たさなくなるからで，本章は正値性をポートフォリオではなく株価比の側に置いた（定義 15.1.1）ので，同じ心配が起きない．いちばん極端な副情報，すなわち株価比を完全に言い当てるものも本節の枠に入る．例 15.4.6 がそれである．

このあとの 定義 15.4.3 は，$y$ ごとの条件付き分布を $y$ の出方で平均して $X$ の分布を作り，その分布について最大の倍加率を置く．平均して作ったものがまた分布であることは，その定義そのものでも，このあとの二つの証明でも使うので，番号で引けるように先に書き留めておく．

::: lemma 15.4.2 条件付き分布の平均は分布である
$\mathcal X$，$\mathcal Y$ を空でない有限集合，$p(y)$ を $\mathcal Y$ 上の分布とし，各 $y \in \mathcal Y$ について $p(\cdot \mid y)$ を $\mathcal X$ 上の分布とする．このとき，$x \in \mathcal X$ に実数
$$
\sum_{y \in \mathcal Y} p(y)\, p(x \mid y)
$$
を返す関数は $\mathcal X$ 上の分布である．
:::

::: proof
どの $y$ でも $p(y) \ge 0$ かつ $p(x \mid y) \ge 0$ だから，各項は非負であり，有限和も非負である．総和は，$x$ についての和と $y$ についての和を入れ替えて
$$
\sum_{x \in \mathcal X} \sum_{y \in \mathcal Y} p(y)\, p(x \mid y)
  \;=\; \sum_{y \in \mathcal Y} p(y) \sum_{x \in \mathcal X} p(x \mid y)
  \;=\; \sum_{y \in \mathcal Y} p(y) \;=\; 1
$$
である（第 $2$ の等号は各 $p(\cdot \mid y)$ が $\mathcal X$ 上の分布であること，第 $3$ の等号は $p(y)$ が $\mathcal Y$ 上の分布であることによる）．
:::

::: formalized
`sideMarginalX_mem_stdSimplex` (`InformationTheory/Shannon/Gambling/SideInformation.lean`)
:::

::: definition 15.4.3 周辺分布と最適倍加率
定義 15.4.1 と同じ記法で，$m \ge 1$，$\mathcal X$ を株価比（定義 15.1.1）からなる空でない有限集合，$\mathcal Y$ を空でない有限集合，$p(y)$ を $\mathcal Y$ 上の分布，各 $y$ について $p(\cdot \mid y)$ を $\mathcal X$ 上の分布とする．$X$ の周辺分布を
$$
p(x) \;:=\; \sum_{y \in \mathcal Y} p(y)\, p(x \mid y)
$$
と書く（補題 15.4.2 よりこれは $\mathcal X$ 上の分布である）．そのうえで
$$
W^{*}(X) \;:=\; \max_{b} W(b, p),
\qquad
W^{*}(X \mid Y) \;:=\; \sum_{y \in \mathcal Y} p(y) \max_{b} W\big(b, p(\cdot \mid y)\big)
$$
と定める．ここに現れる $\max$ はすべてポートフォリオ（定義 15.1.2）全体にわたるもので，命題 15.2.2 よりどれも達成される（$W$ は 定義 15.1.4 の倍加率である）．この二つを第5章 定義 5.4.3 と同じく **最適倍加率** と呼ぶ．
:::

::: formalized
$X$ の周辺分布 `sideMarginalX` (`InformationTheory/Shannon/Gambling/SideInformation.lean`)
:::

::: formalization-note
二つの最適倍加率にあたる宣言はない．$W^{*}(X \mid Y)$ については，各 $y$ で最大を与えるポートフォリオを選んで `condGrowthRate` (`InformationTheory/Shannon/Portfolio/SideInformation.lean`) に渡したものがそれであり，$W^{*}(X)$ については同じく最大を与えるポートフォリオを `growthRate` (`InformationTheory/Shannon/Portfolio/Basic.lean`) に渡したものがそれである．どちらも最大を与えるポートフォリオを外から渡す形で，最大そのものを定めた宣言ではない．
:::

$W^{*}(X)$ は副情報を使わないポートフォリオの中での最大値，$W^{*}(X \mid Y)$ は $y$ ごとに選べるポートフォリオの中での最大値である．二つの最大値の差が，副情報を手に入れたことの値打ちである．

## 増分は相互情報量で抑えられる

::: theorem 15.4.4
$m \ge 1$ とし，$\mathcal X$ を株価比（定義 15.1.1）からなる空でない有限集合，$\mathcal Y$ を空でない有限集合とする．$p(y)$ を $\mathcal Y$ 上の分布，各 $y \in \mathcal Y$ について $p(\cdot \mid y)$ を $\mathcal X$ 上の分布とし，$(X, Y)$ を $\mathcal X \times \mathcal Y$ に値をとる対で，その同時分布が $p(x,y) = p(y)\,p(x \mid y)$ であるものとする．$p(x)$ を 定義 15.4.3 の周辺分布，$b^\circ$ をその分布 $p$ についての対数最適ポートフォリオ（定義 15.2.3）とする．このとき，条件付きポートフォリオのどの族 $b$（定義 15.4.1）についても
$$
W(b \mid Y) - W(b^\circ, p) \;\le\; I(X; Y)
$$
である（$W$ は 定義 15.1.4 の倍加率，$W(\cdot \mid Y)$ は 定義 15.4.1 の条件付き倍加率，$I(X;Y)$ は 定義 1.3.1 の相互情報量である）．
:::

::: proof
筋は三段である．差から相互情報量を引いた残りを一つの和に書き，有限 Jensen の不等式で対数の外に出し，内側の和を $y$ ごとに 定理 15.3.1 で $1$ 以下に抑える．

$x \in \mathcal X$ と $y \in \mathcal Y$ について $s(x) := \sum_{k=1}^{m} b^\circ(k)\,x(k)$，$r_y(x) := \sum_{j=1}^{m} b(j \mid y)\,x(j)$ とおく．補題 15.1.5 よりどちらも正である．

まず差を一つの和にまとめる．定義 15.4.1 と 定義 15.1.4 より $W(b \mid Y) = \sum_{y} \sum_{x} p(y)\,p(x \mid y) \log r_y(x)$ であり，同時分布の定め方からこれは $\sum_{x,y} p(x,y) \log r_y(x)$ に等しい．いっぽう 定義 15.4.3 より $p(x) = \sum_{y} p(x,y)$ だから，$W(b^\circ, p) = \sum_{x} p(x) \log s(x) = \sum_{x,y} p(x,y) \log s(x)$ である．よって
$$
W(b \mid Y) - W(b^\circ, p) \;=\; \sum_{x,y} p(x,y) \log \frac{r_y(x)}{s(x)}
$$
となる．

$A := \{\,(x,y) \mid p(x,y) > 0\,\}$ とおく．$A$ の外の項は $p(x,y) = 0$ で消えるから，上の和は $A$ 上の和である．同時分布の定め方から $\sum_{x} p(x,y) = p(y) \sum_{x} p(x \mid y) = p(y)$ なので $p(y)$ は $Y$ の周辺分布であり，$p(x)$ は 定義 15.4.3 のとおり $X$ の周辺分布である．$(x,y) \in A$ では $p(y) \ge p(x,y) > 0$ かつ $p(x) \ge p(x,y) > 0$ かつ $p(x \mid y) > 0$ であり，$p(x,y)/\big(p(x)p(y)\big) = p(x \mid y)/p(x)$ だから，定義 1.3.1 より
$$
I(X;Y) \;=\; \sum_{A} p(x,y) \log \frac{p(x \mid y)}{p(x)}
$$
である．二つを引き算すると
$$
W(b \mid Y) - W(b^\circ, p) - I(X;Y)
  \;=\; \sum_{A} p(x,y) \log t(x,y),
\qquad
t(x,y) \;:=\; \frac{p(x)\, r_y(x)}{p(x \mid y)\, s(x)}
$$
となる．$A$ の上では $t(x,y) > 0$ である．

補題 1.1.6 を，凹関数として $\log$（第1章 1.1 節が認めた狭義凹性による），重みとして $A$ 上の $p(x,y)$，点として $t(x,y)$ ととって当てる．重みは非負で，総和は $\sum_{A} p(x,y) = \sum_{x,y} p(x,y) = \sum_{y} p(y) \sum_{x} p(x \mid y) = 1$ だから，
$$
\sum_{A} p(x,y) \log t(x,y) \;\le\; \log\Big( \sum_{A} p(x,y)\, t(x,y) \Big)
$$
を得る．

内側の和を抑える．$A$ の上では $p(x,y) = p(y)\,p(x \mid y)$ と $p(x \mid y) > 0$ より
$$
p(x,y)\, t(x,y) \;=\; p(y)\, p(x)\, \frac{r_y(x)}{s(x)}
$$
である．この形の項はどの $(x,y)$ でも非負だから，$A$ の外の項を足しても和は減らず
$$
\sum_{A} p(x,y)\, t(x,y)
  \;\le\; \sum_{y \in \mathcal Y} p(y) \sum_{x \in \mathcal X} p(x)\, \frac{r_y(x)}{s(x)}
$$
となる．ここで $p$ は，補題 15.4.2 より $\mathcal X$ 上の分布である．$y$ を一つ固定し，株価比の分布を $p$ とする市場とポートフォリオ $b^\circ$，$b(\cdot \mid y)$ に 定理 15.3.1 を当てる．$b^\circ$ が分布 $p$ についての対数最適ポートフォリオであることがちょうど同定理の仮定であり，株価比の分布が $p$ だから同定理の左辺は $\sum_{x} p(x)\, r_y(x)/s(x)$ という和である．よってこの内側の和は $1$ 以下で，$\sum_{y} p(y) = 1$ とあわせて右辺は $1$ 以下である．

いっぽう $\sum_{A} p(x,y) = 1$ だから $A$ は空ではなく，$A$ 上の各項 $p(x,y)\,t(x,y)$ は正だから，この和は正である．したがって和は $0$ より大きく $1$ 以下であり，対数の単調性（補題 8.2.5）よりその対数は $\log 1 = 0$ 以下である．以上を合わせて $W(b \mid Y) - W(b^\circ, p) - I(X;Y) \le 0$ を得る．
:::

::: formalized
`sideInfo_growthRate_increment_le_mutualInfo` (`InformationTheory/Shannon/Portfolio/SideInformation.lean`)
:::

::: formalization-note
宣言が $b^\circ$ に課すのは，対数最適性ではなく 15.2 節 の Kuhn–Tucker 条件の $m$ 本の不等式である．本文の対数最適性からその $m$ 本が出ることは 定理 15.2.5 が与え，そちらも無条件の機械検証済みである．宣言が右辺に置く相互情報量は，アルファベット上の関数としての周辺分布と同時分布から組んだ実数値の量 `sideInfoMutualInfo` (`InformationTheory/Shannon/Gambling/SideInformation.lean`) である．第1章 定義 1.3.1 が紐付けた `mutualInfo` (`InformationTheory/Shannon/MutualInfo.lean`) は確率変数の像測度についての拡張非負実数値の量で，値はどちらも $I(X;Y)$ で一致するが，単独の宣言としては別のものである．
:::

**証明のどこが変わったか.** 第5章 定理 5.4.4 の証明は，条件付き倍加率も副情報を使わない倍加率も，どちらも比例賭けの値として閉じた式（定理 5.3.1）に書き換えられることに乗っていた．二つの閉じた式を引き算するとオッズの項が消え，残ったエントロピーの差が 定理 1.3.4 によってちょうど $I(X;Y)$ になる．市場には比例賭けにあたる閉じた式がない（15.2 節）．上の証明が代わりに使ったのは，相互情報量を引いた残りを一つの和にまとめ，有限 Jensen の不等式で上から抑える段である．不等式は一方向にしか効かないので，得られるのも一方向の評価だけになる．どの市場で等号が成り立つかを本書は述べない．

::: corollary 15.4.5 最適な組み替えの増分の上界
$m \ge 1$ とし，$\mathcal X$ を株価比（定義 15.1.1）からなる空でない有限集合，$\mathcal Y$ を空でない有限集合とする．$p(y)$ を $\mathcal Y$ 上の分布，各 $y \in \mathcal Y$ について $p(\cdot \mid y)$ を $\mathcal X$ 上の分布とし，$(X, Y)$ を $\mathcal X \times \mathcal Y$ に値をとる対で，その同時分布が $p(x,y) = p(y)\,p(x \mid y)$ であるものとする．このとき最適倍加率（定義 15.4.3）について
$$
W^{*}(X \mid Y) - W^{*}(X) \;\le\; I(X; Y)
$$
である（$I(X;Y)$ は 定義 1.3.1 の相互情報量である）．
:::

::: proof
各 $y \in \mathcal Y$ について，命題 15.2.2 を分布 $p(\cdot \mid y)$ に当てて $W(\cdot, p(\cdot \mid y))$ の最大を与えるポートフォリオを一つ選び，それを $b(\cdot \mid y)$ とする．$y$ を動かしたこの族 $b$ について，定義 15.4.1 と 定義 15.4.3 より $W(b \mid Y) = W^{*}(X \mid Y)$ である．

次に周辺分布 $p$ に移る．補題 15.4.2 より $p$ は $\mathcal X$ 上の分布である．$b^{*}$ をこの $p$ についての対数最適ポートフォリオ（定義 15.2.3）とすると，命題 15.2.2 よりそのようなものは存在し，定義 15.4.3 より $W(b^{*}, p) = W^{*}(X)$ である．

そこで 定理 15.4.4 を $b^\circ := b^{*}$ とこの族 $b$ に当てると，$W^{*}(X \mid Y) - W^{*}(X) \le I(X;Y)$ を得る．
:::

::: formalization-note
系 15.4.5 に対応する単独の宣言はない．定理 15.4.4 の紐付け先に，各 $y$ で最大を与えるポートフォリオと，周辺分布について最大を与えるポートフォリオとを渡した形で得られる（後者を宣言の求める Kuhn–Tucker 条件に直すのが，定理 15.4.4 の注記に書いた `kuhnTucker_of_logOptimal` (`InformationTheory/Shannon/Portfolio/Basic.lean`) である）．渡す先の宣言はどちらのポートフォリオも仮定として受け取るだけで，それらが存在すること，すなわち 命題 15.2.2 にあたることは述べていない．
:::

::: example 15.4.6 株価比を完全に言い当てる副情報
例 15.1.6 の市場をとる．すなわち $m = 2$，$\mathcal X = \{x_\uparrow, x_\downarrow\}$，$x_\uparrow(1) = x_\downarrow(1) = 1$，$x_\uparrow(2) = 2$，$x_\downarrow(2) = 1/2$ とする．$\mathcal Y := \{\uparrow, \downarrow\}$，$p(\uparrow) = p(\downarrow) = 1/2$ とし，条件付き分布を $p(x_\uparrow \mid \uparrow) = 1$，$p(x_\downarrow \mid \uparrow) = 0$，$p(x_\uparrow \mid \downarrow) = 0$，$p(x_\downarrow \mid \downarrow) = 1$ とする．このとき $X$ の周辺分布（定義 15.4.3）は 例 15.1.6 の $p$ に等しく，最適倍加率（定義 15.4.3）は
$$
W^{*}(X) \;=\; \tfrac12\log\tfrac98 \;=\; 0.0849\ldots,
\qquad
W^{*}(X \mid Y) \;=\; \tfrac12
$$
であり，その差は $\log\frac43 = 0.4150\ldots$ である．いっぽう $I(X;Y) = 1$ である．
:::

::: proof
周辺分布は $p(x_\uparrow) = \frac12 \cdot 1 + \frac12 \cdot 0 = \frac12$，同様に $p(x_\downarrow) = \frac12$ で，例 15.1.6 の $p$ に等しい．例 15.2.6 よりこの市場の対数最適ポートフォリオは $b^{*}(1) = b^{*}(2) = 1/2$ であり，例 15.1.6 よりその倍加率は $\frac12\log\frac98$ だから，定義 15.4.3 より $W^{*}(X) = \frac12\log\frac98$ である．

$y = \uparrow$ のとき，条件付き分布は $x_\uparrow$ の一点に集中するから，定義 15.1.4 の和は $x_\uparrow$ の項だけになり，ポートフォリオ $b$ について $W(b, p(\cdot \mid \uparrow)) = \log\big(b(1) + 2\,b(2)\big) = \log\big(1 + b(2)\big)$ である（$b(1) + b(2) = 1$ による）．$0 \le b(2) \le 1$ の範囲で $1 + b(2)$ は $b(2) = 1$ で最大 $2$ をとるから，補題 8.2.5 の単調性より最大値は $\log 2 = 1$ で，全額を銘柄 $2$ に寄せたポートフォリオがそれを与える．$y = \downarrow$ のときは同様に $W(b, p(\cdot \mid \downarrow)) = \log\big(b(1) + \frac12 b(2)\big) = \log\big(1 - \frac12 b(2)\big)$ で，最大値は $b(2) = 0$ での $\log 1 = 0$ である．定義 15.4.3 より $W^{*}(X \mid Y) = \frac12 \cdot 1 + \frac12 \cdot 0 = \frac12$ である．

差は $\frac12 - \frac12\log\frac98 = \frac12\log 2 - \frac12\log\frac98 = \frac12\log\frac{16}{9} = \log\frac43$ であり，$\log 3 = 1.5849\ldots$ から $\log\frac43 = 2 - \log 3 = 0.4150\ldots$ を得る．

相互情報量を計算する．同時分布は $p(x_\uparrow, \uparrow) = p(x_\downarrow, \downarrow) = \frac12$，残る二点で $0$ である．定義 1.3.1 の和は正の二点についてとるもので，どちらでも $p(x) = p(y) = \frac12$ だから
$$
I(X;Y) \;=\; 2 \cdot \tfrac12 \log \frac{1/2}{(1/2)(1/2)} \;=\; \log 2 \;=\; 1
$$
である．
:::

例 15.4.6 の副情報は株価比を完全に言い当てる．じつは，これより多くを教える副情報はない．どんな副情報 $Y'$ についても，定理 1.3.4 より $I(X;Y') = H(X) - H(X \mid Y')$ であり，条件付きエントロピー（定義 1.2.2）は各条件のもとのエントロピーの平均だから 命題 1.1.4 より非負で，$I(X;Y') \le H(X)$ となる．この市場の $X$ は $2$ 点上の一様分布だから 定理 1.1.5 の等号の場合にあたり $H(X) = 1$ で，例 15.4.6 の $I(X;Y) = 1$ はその値に達しているからである．

それでも増分は $\log\frac43 = 0.4150\ldots$ にとどまり，$I(X;Y) = 1$ には届かない．$y$ を知ったあとにできるいちばん良いことは全額を一つの銘柄に寄せることで，そのときの $1$ 期の資産倍率は上向きで $2$，下向きで $1$ である．その対数を平均した $\frac12$ が $W^{*}(X \mid Y)$ で，$I(X;Y) = 1$ との開きはここから出ている．下向きだと分かっていても，下向きのときに資産を増やす銘柄がこの市場にはない．できるのは減らないこと，すなわち全額を現金に寄せることまでである．この市場が返す倍率の大きさが，副情報の使い道を上から押さえているということである．
