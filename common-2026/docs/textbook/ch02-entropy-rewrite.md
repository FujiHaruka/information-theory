# 第2章 エントロピー・相互情報量・データ処理不等式

> **この原稿について（書き直し版・序盤パイロット）**
>
> 本ファイルは `ch02-entropy.md`（形式証明リファレンス版）を、**独立した教科書として
> 通読できる原稿**へ書き直す試みである。各概念は動機づけ・定義・例・証明を
> 自然言語と LaTeX 数式で展開し、対応する形式化は各結果の末尾に
> 「**形式化**: `定理名` (`Common2026/...`)」として控えめに付す。本文は
> Lean を一切知らない読者が読み通せることを目標とする。
>
> 範囲は離散・有限アルファベットに限る。確率変数 $X$ は有限集合 $\mathcal X$ に
> 値をとり、その分布を $p(x) = \Pr[X = x]$ と書く。対数 $\log$ の底は
> 任意だが、底を 2 にとれば単位はビット、自然対数なら nat である。

---

## 2.1 エントロピー

### 動機

確率変数 $X$ を観測する前、その結果にはどれだけの「不確かさ」があるだろうか。
あるいは観測したとき、私たちはどれだけの「情報」を得るのだろうか。エントロピーは、
この素朴な問いに一つの定量的な答えを与える量である。

良い不確かさの尺度に何を期待するか、条件を並べてみよう。確実な事象（ある値を
確率 1 でとる）は不確かさ 0 であってほしい。とりうる値が多く、かつそれらが
均等に起こりやすいほど不確かさは大きいはずだ。そして独立な二つの実験を同時に
行ったときの不確かさは、それぞれの不確かさの和であってほしい（加法性）。
Shannon は、これらの自然な要請を満たす尺度が本質的に一通りに定まることを示した。
それが次のエントロピーである。

### 定義

**定義 2.1.1（エントロピー）.** 有限アルファベット $\mathcal X$ 上に分布する
離散確率変数 $X$（分布 $p(x)$）の **エントロピー** を
$$
H(X) \;=\; -\sum_{x \in \mathcal X} p(x) \log p(x)
$$
で定める。$p(x) = 0$ の項は $p \log p \to 0$（$p \downarrow 0$）にならい
$0 \log 0 = 0$ と約束する。

エントロピーは $X$ の値そのものではなく分布 $p$ のみに依存する量であることに
注意したい。記号 $H(X)$ は慣用だが、より正確には $H(p)$ と書くべき汎関数である。

> **形式化上の注記.** 本ライブラリでは $-p\log p$ を一つの関数
> `negMulLog p` として扱い、$0 \log 0 = 0$ はこの関数の定義（$p = 0$ で値 0）に
> 組み込んである。確率変数は測度空間上の可測写像として表現し、分布 $p$ は
> 像測度を通じて与えられる。
>
> **形式化**: `entropy` (`Common2026/Shannon/Bridge.lean`)

### 例

**例 2.1.2（ベルヌーイ分布）.** $X$ が確率 $p$ で $1$、確率 $1-p$ で $0$ を
とるとき、
$$
H(X) \;=\; -p \log p - (1-p)\log(1-p) \;=:\; H_b(p).
$$
この $H_b$ を **二値エントロピー関数** と呼ぶ。$H_b(0) = H_b(1) = 0$
（結果が確定していて不確かさがない）であり、$p = 1/2$ で最大値 $\log 2$ を
とる（最も予測しづらい公平なコイン）。$H_b$ は $[0,1]$ 上で凹かつ
$p = 1/2$ を軸に左右対称である。

**例 2.1.3（一様分布）.** $X$ が $\mathcal X$（要素数 $|\mathcal X| = M$）上で
一様、すなわち各 $x$ で $p(x) = 1/M$ のとき、
$$
H(X) \;=\; -\sum_{x} \frac1M \log \frac1M \;=\; \log M.
$$
あとで見るように、これは要素数 $M$ のアルファベット上で達成可能な
エントロピーの **最大値** である。

### 性質1：非負性

**命題 2.1.4.** 任意の離散確率変数 $X$ について $H(X) \ge 0$。等号は $X$ が
ある一点に確率 1 で集中するときに限り成り立つ。

*証明.* 各 $x$ について $0 \le p(x) \le 1$ だから $\log p(x) \le 0$、
したがって $-p(x)\log p(x) \ge 0$。和をとっても非負である（$p(x) = 0$ の項は
約束により 0）。

等号 $H(X) = 0$ は、非負項の和が 0 であることだから、すべての $x$ で
$-p(x)\log p(x) = 0$ を要する。$0 < p(x) < 1$ の $x$ があれば
$-p(x)\log p(x) > 0$ となり矛盾。ゆえに各 $p(x)$ は $0$ または $1$ であり、
総和が 1 という条件と合わせると、ちょうど一つの $x$ で $p(x) = 1$。$\qquad\blacksquare$

直感的には「不確かさが負になることはなく、不確かさ 0 とは結果が確定していること」
という当然の事実を述べている。

> **形式化**: `entropy_nonneg` (`Common2026/Shannon/Bridge.lean`)

### 性質2：一様分布が最大化する（$H(X) \le \log|\mathcal X|$）

> **この節について（Lean 準拠プロトタイプ）.** 本節は試験的に、本文の証明を
> 形式化（Lean）の証明と同じ筋道で書き、各ステップが Lean のどの補題に対応するかを
> 末尾の脚注で示す。対応する Lean 定義は自然対数を採るため、以下で $\log$ は
> 自然対数（単位は nat）と読む。

**定理 2.1.5.** $|\mathcal X| = M$ のとき $H(X) \le \log M$。等号は $X$ が
$\mathcal X$ 上で一様分布のときに限り成り立つ。

「アルファベットの大きさが不確かさの上限を決め、その上限は均等に散らばったときに
達成される」という主張である。証明は、エントロピーの被加数
$\varphi(t) = -t\log t$ が **凹関数** であることに対する Jensen の不等式から
ただちに従う。

まず、$X$ の分布を $p(x)$ と書くと、エントロピーは定義からこの $\varphi$ の和である：
$$
H(X) \;=\; -\sum_{x} p(x)\log p(x) \;=\; \sum_{x} \varphi\big(p(x)\big),
\qquad \varphi(t) := -t\log t.
$$

**信頼の底.** 証明が依拠する純粋に**解析的**な事実はただ一つ、$\varphi(t) = -t\log t$
が $[0,\infty)$ 上で（$\varphi(0) := 0$ と定めて）**狭義凹**であることである。これは
$x\log x$ の凸性という初等的事実で、接線不等式 $\log t \le t-1$ と同じ内容に帰着する。
ここより下は展開しない（Mathlib `Real.strictConcaveOn_negMulLog`）。もう一つの道具で
ある凹関数の **Jensen の不等式** は、それ自体は非自明だが新たな解析を要さず、二つの初等的
事実——(a) 凹関数の**ハイポグラフ**（グラフの下側領域）が**凸集合**であること、(b) 凸集合は
有限個の点の凸結合をすべて含むこと——に帰着する。以下では、形式化（Mathlib）が採る筋を
そのままなぞって補題として証明する。

**補題（有限 Jensen の不等式）.** $\varphi$ を区間 $I$ 上の凹関数とする。有限個の点
$t_1, \dots, t_n \in I$ と重み $w_1, \dots, w_n \ge 0$（$\sum_i w_i = 1$）に対して
$$
\sum_{i} w_i\,\varphi(t_i) \;\le\; \varphi\Big(\sum_{i} w_i\,t_i\Big).
$$
さらに $\varphi$ が $I$ 上で**狭義**凹ならば、等号が成り立つのは、正の重み $w_i > 0$ を
もつ点 $t_i$ がすべて互いに等しいとき、かつそのときに限る。

**証明.** 形式化（Mathlib）と同じ筋でたどる。$\varphi$ の**ハイポグラフ**
$$
\operatorname{hyp}\varphi \;:=\; \{(t, y) \in \mathbb R^2 : t \in I,\ y \le \varphi(t)\}
$$
を考える。「$\varphi$ が $I$ 上で凹」であることは「$\operatorname{hyp}\varphi$ が平面の
**凸集合**である」ことと同値である（凹性の定義の幾何的言い換え。Mathlib では
`ConcaveOn` ⟺ `Convex (hypograph)`）。

*不等式.* 各点 $\big(t_i, \varphi(t_i)\big)$ は（第 2 座標が等号で）$\operatorname{hyp}\varphi$
に属する。凸集合は有限個の点の凸結合をすべて含む（Mathlib `Convex.centerMass_mem`）から、
重み $w_i$ による凸結合
$$
\sum_i w_i\,\big(t_i, \varphi(t_i)\big)
  \;=\; \Big(\sum_i w_i t_i,\ \sum_i w_i\,\varphi(t_i)\Big)
$$
もまた $\operatorname{hyp}\varphi$ に属する。ハイポグラフの定義より、その第 2 座標は
第 1 座標における $\varphi$ 値以下、すなわち
$\sum_i w_i\,\varphi(t_i) \le \varphi\big(\sum_i w_i t_i\big)$。

*等号条件（$\varphi$ 狭義凹）.* 正の重みの点がすべて共通値に等しければ両辺一致で、等号は
明らか。逆を**背理法**で示す。$\varphi$ 狭義凹・全 $w_i > 0$・等号成立を仮定したうえで、
ある 2 点が相異なる（$t_j \ne t_k$）と仮定して矛盾を導く。この 2 点を取り出し、
$c := w_j + w_k > 0$ とおいて両者を 1 点
$q := \tfrac{w_j}{c} t_j + \tfrac{w_k}{c} t_k$ に融合する。残りの添字を
$u := \{\,i : i \ne j, k\,\}$ とし、重み $c$ をもつ点 $q$ と族 $(w_i, t_i)_{i \in u}$ から
なる凸結合に**すでに示した不等式**を適用すると（総重み $c + \sum_{u} w_i = 1$）
$$
c\,\varphi(q) + \sum_{i \in u} w_i\,\varphi(t_i)
  \;\le\; \varphi\Big(c\,q + \sum_{i \in u} w_i t_i\Big)
  \;=\; \varphi\Big(\sum_i w_i t_i\Big).
$$
一方 $t_j \ne t_k$ と狭義凹性から、**2 点厳密不等式**
$$
\varphi(q)
  \;>\; \tfrac{w_j}{c}\,\varphi(t_j) + \tfrac{w_k}{c}\,\varphi(t_k)
$$
が成り立つ。両辺を $c$ 倍して上式へ代入すれば
$$
\sum_i w_i\,\varphi(t_i)
  \;=\; w_j\varphi(t_j) + w_k\varphi(t_k) + \sum_{i \in u} w_i\varphi(t_i)
  \;<\; c\,\varphi(q) + \sum_{i \in u} w_i\varphi(t_i)
  \;\le\; \varphi\Big(\sum_i w_i t_i\Big)
$$
となり厳密不等式が出るが、これは等号の仮定に反する。ゆえにすべての点が等しい。
$\qquad\square$

**証明（定理 2.1.5）.** 上の補題で重みを一様に $w_x = 1/M$、点を $t_x = p(x)$ ととる。
各 $p(x) \ge 0$ は $\varphi$ の定義域 $[0,\infty)$ に入るので、質量 $0$ の記号を除外する
必要はない。$\varphi$ の凹性と $\sum_x p(x) = 1$ から
$$
\frac1M \sum_{x} \varphi\big(p(x)\big)
  \;=\; \sum_{x} \frac1M\,\varphi\big(p(x)\big)
  \;\le\; \varphi\Big(\sum_{x} \frac1M\,p(x)\Big)
  \;=\; \varphi\Big(\frac1M\Big).
$$
左辺は $\tfrac1M H(X)$、右辺は
$\varphi\!\left(\tfrac1M\right) = -\tfrac1M\log\tfrac1M = \tfrac1M\log M$。
したがって $\tfrac1M H(X) \le \tfrac1M\log M$、両辺を $M$ 倍して
$$
H(X) \;\le\; \log M.
$$
等号条件は $\varphi$ が **狭義** 凹であることから従う。狭義凹関数の Jensen が等号に
なるのは全ての点が等しいとき、すなわち $p(x)$ が $x$ によらず一定のときに限る。
$\sum_x p(x) = 1$ と合わせて $p(x) = 1/M$、つまり $X$ が一様分布のときである。
$\qquad\blacksquare$

> **形式化.** 主定理 `entropy_le_log_card`、等号条件 `entropy_eq_log_card_iff`
> (`Common2026/Shannon/MaxEntropy.lean`)。本文の各ステップがそのまま対応する。
> エントロピーが $\sum_x \varphi(p(x))$ という有限和であること（$\varphi$ は Mathlib の
> `Real.negMulLog`、$\mathcal X$ は有限型）は Lean では定義上の等式。$\varphi$ の凹性は
> `Real.concaveOn_negMulLog`（狭義版 `Real.strictConcaveOn_negMulLog`、定義域は
> $[0,\infty)$ ＝ `Set.Ici 0`）、Jensen の不等式は `ConcaveOn.le_map_sum`、等号条件は
> `StrictConcaveOn.map_sum_eq_iff`。本文の補題証明は **Mathlib と同じ筋**をなぞっている：
> 不等式はハイポグラフ（凹側）／エピグラフ（凸側）の凸性と凸結合の所属
> （`Convex.centerMass_mem`、`ConvexOn.map_centerMass_le` 経由）、等号条件は相異なる 2 点を
> 取り出す狭義 Jensen（`StrictConcaveOn.lt_map_sum`）からの背理法（`eq_of_map_sum_eq`）。
> 本文がハイポグラフ／2 点ウィットネスで書かれているのはこの対応を保つためである。
> 唯一そこに帰着しきれない「凸集合が有限凸結合を含む」部分（`Convex.centerMass_mem`）が
> 実質的な帰納の在処で、Mathlib でも独立補題として因数分解されている。
> $\varphi$ が $t=0$ を含む $[0,\infty)$ で凹なので
> $p(x)=0$ の記号を除外する「台」の処理が一切生じないのが、この筋道の利点である。
> 最後に「全 singleton の質量が $1/M$」から測度の一致
> $\mu.\mathrm{map}\,X = \mathrm{uniformOn}$ への橋渡しに `Measure.ext_of_singleton`
> を用いる。
>
> 底にある解析的事実は $\varphi$ の凹性ただ一つで、これは $\log t \le t-1$
> （`Real.log_le_sub_one_of_pos`）と同じ内容に帰着する。なお同じ主張を相対エントロピー
> （KL ダイバージェンス）経由で述べた恒等式 $D(p\,\|\,\text{一様}) = \log M - H(X)$ も
> `klDiv_uniformOn_univ_toReal_eq` として形式化されているが、上の主定理はそれには
> 依存しない（Jensen から直接示している）。

---

## 2.2 結合エントロピー・条件付きエントロピーとチェイン則

### 結合エントロピー

二つの確率変数を同時に考えるとき、対 $(X, Y)$ を一つの確率変数とみなせば、
そのエントロピーがそのまま結合エントロピーである。

**定義 2.2.1（結合エントロピー）.** 同時分布 $p(x,y)$ をもつ $(X, Y)$ の
**結合エントロピー** を
$$
H(X, Y) \;=\; -\sum_{x,y} p(x,y) \log p(x,y)
$$
と定める。これは対 $(X,Y)$ を値域 $\mathcal X \times \mathcal Y$ の
単一の確率変数とみたときの定義 2.1.1 そのものであり、新しい概念ではない。

### 条件付きエントロピー

$Y = y$ を観測したあと、$X$ になお残る不確かさは、条件付き分布
$p(x \mid y)$ のエントロピー $H(X \mid Y=y) = -\sum_x p(x\mid y)\log p(x\mid y)$
で測れる。これを $Y$ の分布で平均したものが条件付きエントロピーである。

**定義 2.2.2（条件付きエントロピー）.**
$$
H(X \mid Y) \;=\; \sum_y p(y)\, H(X \mid Y = y)
  \;=\; -\sum_{y} p(y) \sum_{x} p(x\mid y)\log p(x\mid y)
  \;=\; -\sum_{x,y} p(x,y)\log p(x\mid y).
$$

最後の等号は $p(x,y) = p(y)\,p(x\mid y)$ による書き換えである。$H(X\mid Y)$ は
「$Y$ を知ったうえでなお $X$ に残る平均的な不確かさ」と読む。$H(X\mid Y=y)$ を
特定の $y$ ごとにみれば $H(X)$ より大きくなることもあり得るが、$y$ について
平均した $H(X\mid Y)$ は $H(X)$ を超えない（「条件付けは平均的に不確かさを
減らす」、後述）。

> **形式化上の注記.** 本ライブラリでは条件付き分布を測度論的な
> `condDistrib`（条件付き分布カーネル）で表し、各 $y$ ごとの離散エントロピーを
> 周辺分布 $p(y)$ で積分した形で定義する。定義 2.2.2 の最右辺と一致する。
>
> **形式化**: `condEntropy`
> (`Common2026/Fano/Measure.lean`, 名前空間 `InformationTheory.MeasureFano`)

### チェイン則

**定理 2.2.3（チェイン則）.**
$$
H(X, Y) \;=\; H(X) + H(Y \mid X).
$$

「対 $(X,Y)$ の不確かさは、まず $X$ の不確かさ、次に $X$ を知ったうえでの
$Y$ の不確かさ、の和に分解できる」という、エントロピーのもっとも基本的な
構造である。

*証明.* 同時分布の連鎖律 $p(x,y) = p(x)\,p(y\mid x)$ の両辺の対数をとると
$\log p(x,y) = \log p(x) + \log p(y\mid x)$。両辺に $-p(x,y)$ を掛けて
$(x,y)$ について和をとる：
$$
H(X,Y) \;=\; -\sum_{x,y} p(x,y)\log p(x,y)
  \;=\; -\sum_{x,y} p(x,y)\log p(x) \;-\; \sum_{x,y} p(x,y)\log p(y\mid x).
$$
第2項は定義 2.2.2 によりちょうど $H(Y\mid X)$。第1項は $y$ について先に
和をとると $\sum_y p(x,y) = p(x)$ だから
$$
-\sum_{x,y} p(x,y)\log p(x) \;=\; -\sum_{x} p(x)\log p(x) \;=\; H(X).
$$
合わせて $H(X,Y) = H(X) + H(Y\mid X)$。$\qquad\blacksquare$

対称に $H(X,Y) = H(Y) + H(X\mid Y)$ も成り立つ（証明で $X$ と $Y$ の役割を
入れ替えればよい）。両式を見比べると $H(X) - H(X\mid Y) = H(Y) - H(Y\mid X)$、
すなわち「$Y$ を知って減る $X$ の不確かさ」と「$X$ を知って減る $Y$ の
不確かさ」は等しい。この共通の量が次節の相互情報量 $I(X;Y)$ である。

> **形式化上の注記.** 形式化では結合エントロピーをペア確率変数
> $\omega \mapsto (X(\omega), Y(\omega))$ のエントロピーとして表し、定理 2.2.3 を
> その分解として証明している（添字の都合で $H(X,Y) = H(X) + H(Y\mid X)$ の
> 役割配置になっている）。
>
> **形式化**: `entropy_pair_eq_entropy_add_condEntropy`
> (`Common2026/Shannon/Entropy.lean`)

### 条件付けは不確かさを増やさない

**定理 2.2.4（条件付けの単調性）.**
$$
H(X \mid Y, Z) \;\le\; H(X \mid Y).
$$
すなわち、すでに $Y$ を知っているところへさらに $Z$ を加えても、$X$ に残る
平均的な不確かさは増えない。$Y$ を自明な定数にとれば $H(X\mid Z)\le H(X)$ という
基本形が得られる。

この不等式は「平均的に」という但し書きが本質的であることに注意したい。特定の
観測値 $Z = z$ のもとでは $H(X\mid Y, Z=z) > H(X\mid Y)$ となること（個別の
観測がかえって混乱を増す状況）はあり得る。しかし $Z$ について平均すると、
情報は決して不確かさを増やさない。

*証明.* 後述の条件付き相互情報量 $I(X; Z\mid Y)$ は相対エントロピーの平均として
定義され、つねに非負である（2.5 節・2.6 節）。一方その entropy 表現（2.5 節
定理）は
$$
I(X; Z \mid Y) \;=\; H(X \mid Y) - H(X \mid Y, Z)
$$
であった。左辺 $\ge 0$ より $H(X\mid Y) - H(X\mid Y,Z) \ge 0$、移項して
主張を得る。$\qquad\blacksquare$

> **形式化**: `condEntropy_le_condEntropy_of_pair`
> (`Common2026/Shannon/Entropy.lean`)。証明はここでの説明どおり、条件付き
> 相互情報量の非負性から導いている。

---

## 2.3 相互情報量

### 動機と定義

2.2 節の終わりで、「$Y$ を知って減る $X$ の不確かさ」$H(X) - H(X\mid Y)$ が
$X, Y$ について対称な量であることを見た。これは「一方の変数が他方について
持っている情報量」を測る自然な量であり、相互情報量と呼ばれる。

**定義 2.3.1（相互情報量）.** 同時分布 $p(x,y)$、周辺分布 $p(x), p(y)$ を
もつ $(X, Y)$ について、
$$
I(X; Y) \;=\; \sum_{x,y} p(x,y) \log \frac{p(x,y)}{p(x)\,p(y)}
  \;=\; D\big(p(x,y)\,\big\|\,p(x)p(y)\big).
$$
右端は同時分布 $p(x,y)$ と「もし独立だったら」の分布 $p(x)p(y)$ との
相対エントロピー（KL ダイバージェンス、2.6 節）である。つまり相互情報量とは、
**同時分布が独立からどれだけ隔たっているか** を相対エントロピーで測った量に
ほかならない。

> **形式化上の注記.** 本ライブラリは相互情報量を、いまの「同時分布と周辺積との
> KL ダイバージェンス」という形でそのまま定義する（Mathlib の `klDiv` を用いる）。
> KL ダイバージェンスは $\mathbb R_{\ge 0}^{\infty}$（拡張非負実数）値なので、
> 相互情報量も同じ型をとる。エントロピー表現（後述）との橋渡しでは `.toReal` で
> 実数に落とす一手間が入る。
>
> **形式化**: `mutualInfo` (`Common2026/Shannon/MutualInfo.lean`)

### 基本性質

**命題 2.3.2.** $I(X; Y) \ge 0$、かつ $I(X; Y) = 0$ は $X$ と $Y$ が
独立であることと同値。

*証明.* 相対エントロピーは常に非負（2.6 節、情報不等式）なので、その特別な場合
である相互情報量も非負。等号 $D(p(x,y)\|p(x)p(y)) = 0$ は、相対エントロピーの
等号条件より $p(x,y) = p(x)p(y)$、すなわち独立と同値である。$\qquad\blacksquare$

> **形式化**: 非負性 `mutualInfo_nonneg`、独立との同値
> `mutualInfo_eq_zero_iff_indep` (`Common2026/Shannon/MutualInfo.lean`)

**命題 2.3.3（対称性）.** $I(X; Y) = I(Y; X)$。

*証明.* 定義式の $\dfrac{p(x,y)}{p(x)p(y)}$ は $x, y$ の入れ替えで不変だから。
$\qquad\blacksquare$

> **形式化**: `mutualInfo_comm` (`Common2026/Shannon/MutualInfo.lean`)

有限アルファベット上では $I(X;Y) < \infty$ も成り立つ（各項が有限で和が有限）。

> **形式化**: `mutualInfo_ne_top` (`Common2026/Shannon/MutualInfo.lean`)

### エントロピーとの関係

**定理 2.3.4.**
$$
I(X; Y) \;=\; H(X) - H(X \mid Y) \;=\; H(Y) - H(Y \mid X)
  \;=\; H(X) + H(Y) - H(X, Y).
$$

これが相互情報量の「正体」を示す中心的な等式群である。最初の表現は
「$Y$ を知ることで減る $X$ の不確かさ」、対称形 $H(X)+H(Y)-H(X,Y)$ は
「別々に測った不確かさの和から、まとめて測った不確かさを引いた重複分」と読める。

*証明.* 定義 2.3.1 の対数を分解する。$p(x,y) = p(x\mid y)p(y)$ を使うと
$$
I(X;Y) = \sum_{x,y} p(x,y)\log\frac{p(x\mid y)}{p(x)}
       = \underbrace{-\sum_{x,y}p(x,y)\log p(x)}_{=\,H(X)}
         \;-\;\underbrace{\Big(-\sum_{x,y}p(x,y)\log p(x\mid y)\Big)}_{=\,H(X\mid Y)},
$$
ここで第1項は $y$ について先に和をとって $H(X)$、第2項は定義 2.2.2 により
$H(X\mid Y)$。よって $I(X;Y) = H(X) - H(X\mid Y)$。対称性（命題 2.3.3）から
$I(X;Y) = H(Y) - H(Y\mid X)$ も従う。最後にチェイン則（定理 2.2.3）で
$H(X\mid Y) = H(X,Y) - H(Y)$ を代入すれば $I(X;Y) = H(X)+H(Y)-H(X,Y)$。
$\qquad\blacksquare$

特別な場合として $Y = X$ をとると $H(X\mid X) = 0$ より $I(X;X) = H(X)$。
このため相互情報量はしばしば「自己情報量」としてのエントロピーを含む一般化と
みなされる。

> **形式化上の注記.** 形式化では $I(X;Y)$ が $\mathbb R_{\ge 0}^{\infty}$ 値、
> $H, H(\cdot\mid\cdot)$ が実数値なので、橋渡し定理は左辺に `.toReal` を付けた
> 等式として述べる。これは型をまたぐための技術的処理であり、数学的内容は
> 定理 2.3.4 と同一である。
>
> **形式化**: `mutualInfo_eq_entropy_sub_condEntropy`
> (`Common2026/Shannon/Bridge.lean`)、対称形
> `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy`
> (`Common2026/Shannon/MIChainRule.lean`)

---

*（以降 2.4 チェイン則の一般化、2.5 条件付き相互情報量、2.6 情報不等式 …… も
同じ方針で書き下す。本ファイルは序盤 2.1–2.3 のパイロット。）*
