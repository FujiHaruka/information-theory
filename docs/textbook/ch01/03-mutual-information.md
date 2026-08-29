# 1.3 相互情報量

1.2 節の終わりで、「$Y$ を知って減る $X$ の不確かさ」$H(X) - H(X\mid Y)$ が $X, Y$ に
ついて対称な量であることを見た。これは「一方の変数が他方について持っている情報量」を
測る自然な量であり、相互情報量と呼ばれる。

## 定義

**定義 1.3.1（相互情報量）.** 同時分布 $p(x,y)$、周辺分布 $p(x), p(y)$ をもつ
$(X, Y)$ について、
$$
I(X; Y) \;=\; \sum_{x,y} p(x,y) \log \frac{p(x,y)}{p(x)\,p(y)}
  \;=\; D\big(p(x,y)\,\big\|\,p(x)p(y)\big).
$$
右端は同時分布 $p(x,y)$ と「もし独立だったら」の分布 $p(x)p(y)$ との相対エントロピー
（KL ダイバージェンス、1.6 節）である。つまり相互情報量とは、**同時分布が独立から
どれだけ隔たっているか** を相対エントロピーで測った量にほかならない。

> **形式化上の注記.** 本ライブラリは相互情報量を、いまの「同時分布と周辺積との KL
> ダイバージェンス」という形でそのまま定義する（Mathlib の `klDiv` を用いる）。KL
> ダイバージェンスは $\mathbb R_{\ge 0}^{\infty}$（拡張非負実数）値なので、相互情報量も
> 同じ型をとる。エントロピー表現（後述）との橋渡しでは `.toReal` で実数に落とす一手間が
> 入るが、これは型をまたぐ技術処理で、数学的内容は変わらない。
>
> **形式化**: `mutualInfo` (`InformationTheory/Shannon/MutualInfo.lean`)

## 基本性質

**命題 1.3.2.** $I(X; Y) \ge 0$、かつ $I(X; Y) = 0$ は $X$ と $Y$ が独立であることと
同値。

*証明.* 相対エントロピーは常に非負（1.6 節、情報不等式）なので、その特別な場合である
相互情報量も非負。等号 $D(p(x,y)\|p(x)p(y)) = 0$ は、相対エントロピーの等号条件より
$p(x,y) = p(x)p(y)$、すなわち独立と同値である。$\qquad\blacksquare$

> **形式化上の注記.** 本文の非負性は情報不等式を引く正攻法だが、形式化では重みの
> 置きどころが本文と非対称になる。形式化では相互情報量が拡張非負実数値なので**非負性は
> 型から自明**（`mutualInfo_nonneg` の中身は「最小元以上」一語）で、情報不等式は使わない。
> 実質的な内容は**等号条件の側**（$I(X;Y)=0 \iff$ 独立）に移り、こちらの
> `mutualInfo_eq_zero_iff_indep` は KL の等号条件（`klDiv_eq_zero_iff`）と独立の特徴づけ
> （`indepFun_iff_map_prod_eq_prod_map_map`）の非自明な合成になる。本文で一行の「独立と
> 同値」が形式化では中身をもつ。
>
> **形式化**: 非負性 `mutualInfo_nonneg`、独立との同値 `mutualInfo_eq_zero_iff_indep`
> (`InformationTheory/Shannon/MutualInfo.lean`)

**命題 1.3.3（対称性）.** $I(X; Y) = I(Y; X)$。

*証明.* 定義式の $\dfrac{p(x,y)}{p(x)p(y)}$ は $x, y$ の入れ替えで不変だから。
$\qquad\blacksquare$

> **形式化上の注記.** 見れば自明な対称性が、形式化では測度同型
> `MeasurableEquiv.prodComm` に沿った pushforward になり、「KL は測度同型で値を保つ」と
> いう自作補題 `klDiv_map_measurableEquiv` を要する。
>
> **形式化**: `mutualInfo_comm` (`InformationTheory/Shannon/MutualInfo.lean`)

有限アルファベット上では $I(X;Y) < \infty$ も成り立つ（各項が有限で和が有限）。

> **形式化**: `mutualInfo_ne_top` (`InformationTheory/Shannon/MutualInfo.lean`)。
> 本文一行の有限性が、形式化では結合分布の周辺積への絶対連続性と対数尤度比の可積分性を
> 経て `klDiv_ne_top` に帰着する測度論の補題になる。

## エントロピーとの関係

**定理 1.3.4.**
$$
I(X; Y) \;=\; H(X) - H(X \mid Y) \;=\; H(Y) - H(Y \mid X)
  \;=\; H(X) + H(Y) - H(X, Y).
$$

これが相互情報量の「正体」を示す中心的な等式群である。最初の表現は「$Y$ を知ることで
減る $X$ の不確かさ」、対称形 $H(X)+H(Y)-H(X,Y)$ は「別々に測った不確かさの和から、
まとめて測った不確かさを引いた重複分」と読める。

*証明.* 定義 1.3.1 の対数を $p(x,y) = p(x\mid y)p(y)$ を使って分解する：
$$
I(X;Y) = \sum_{x,y} p(x,y)\log\frac{p(x\mid y)}{p(x)}
       = \underbrace{-\sum_{x,y}p(x,y)\log p(x)}_{=\,H(X)}
         \;-\;\underbrace{\Big(-\sum_{x,y}p(x,y)\log p(x\mid y)\Big)}_{=\,H(X\mid Y)}.
$$
第 1 項は $y$ について先に和をとって $H(X)$、第 2 項は定義 1.2.2 により $H(X\mid Y)$。
よって $I(X;Y) = H(X) - H(X\mid Y)$。対称性（命題 1.3.3）から
$I(X;Y) = H(Y) - H(Y\mid X)$ も従う。最後にチェイン則（定理 1.2.3）で
$H(X\mid Y) = H(X,Y) - H(Y)$ を代入すれば $I(X;Y) = H(X)+H(Y)-H(X,Y)$。$\qquad\blacksquare$

特別な場合として $Y = X$ をとると $H(X\mid X) = 0$ より $I(X;X) = H(X)$。このため
相互情報量はしばしば「自己情報量」としてのエントロピーを含む一般化とみなされる。

> **形式化上の注記.** 形式化では $I(X;Y)$ が拡張非負実数値、$H, H(\cdot\mid\cdot)$ が
> 実数値なので、橋渡し定理は左辺に `.toReal` を付けた等式として述べる。数学的内容は
> 定理 1.3.4 と同一。本文の「$y$ について和をとって $H(X)$」は、共通注記のとおり
> $\mu.\mathrm{map}\,Y$ 上の積分補題（`integral_condDistrib_real_singleton_eq`）に対応する。
>
> **形式化**: `mutualInfo_eq_entropy_sub_condEntropy`
> (`InformationTheory/Shannon/Bridge.lean`)、対称形
> `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy`
> (`InformationTheory/Shannon/MIChainRule.lean`)

