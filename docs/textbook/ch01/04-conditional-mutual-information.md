# 1.4 条件付き相互情報量

1.3 節の相互情報量は「$X$ と $Y$ が共有する情報」を測った。実際の場面では、すでに何かを
知っている状態からこれを問いたいことが多い。たとえば受信語 $Y$ から送信語 $X$ を推定する
とき、途中の中継点 $Z$ の値をすでに握っているなら、そのうえで $X$ と $Y$ がなお共有して
いる情報はいくらか、という問いになる。そこで、条件 $Z = z$ ごとに相互情報量を測り、$Z$ の
分布で平均した量を導入する。これは次節のチェイン則で、変数を 1 個ずつ足したときの
「増分」として現れる主役でもある。

## 定義

条件 $Z = z$ を固定すると、$(X, Y)$ の分布は条件付き同時分布 $p(x,y \mid z)$ に、周辺分布は
$p(x\mid z)$、$p(y\mid z)$ に置き換わる。この分布に定義 1.3.1 をそのまま適用したものを
$I(X; Y \mid Z=z)$ と書く：
$$
I(X; Y \mid Z=z) \;=\; \sum_{x,y} p(x,y \mid z) \log \frac{p(x,y\mid z)}{p(x\mid z)\,p(y\mid z)} .
$$
これを $Z$ の分布で平均する。

**定義 1.4.1（条件付き相互情報量）.**
$$
I(X; Y \mid Z)
  \;=\; \sum_z p(z)\, I(X; Y \mid Z=z)
  \;=\; \sum_{x,y,z} p(x,y,z) \log \frac{p(x,y\mid z)}{p(x\mid z)\,p(y\mid z)} .
$$

条件付きエントロピー（定義 1.2.2）が「各 $y$ ごとのエントロピーを平均したもの」だったのと
まったく同じ作り方である。$Z=z$ ごとに「そのもとでの同時分布が、そのもとで独立だったら
どうだったか、からどれだけ隔たっているか」を測り、$Z$ で平均している。

> **記法の先取り.** 1.6 節の相対エントロピー $D(\cdot\,\|\,\cdot)$ を使えば、各 $z$ の項は
> $D\big(p(x,y \mid z)\,\big\|\,p(x\mid z)p(y\mid z)\big)$ と書ける。本節はこの記法を使わない。

> **形式化上の注記.** 本ライブラリは条件付き分布カーネルの compProd 形に対する KL として
> 定義する（`klDiv` の引数に $\mu.\mathrm{map}\,Z$ と核の合成積を渡す）。値は拡張非負実数。
>
> **形式化**: `condMutualInfo` (`InformationTheory/Shannon/CondMutualInfo.lean`)

## 基本性質

**命題 1.4.2.** $I(X; Y \mid Z) \ge 0$。また $I(X; Y \mid Z) = I(Y; X \mid Z)$（対称性）。

*証明.* 各項 $I(X;Y\mid Z=z)$ は、条件付き分布 $p(\cdot,\cdot\mid z)$ に対する定義 1.3.1 の
相互情報量そのものである。したがって命題 1.3.2 より $I(X;Y\mid Z=z) \ge 0$ で、非負の項を
非負の重み $p(z)$ で平均した $I(X;Y\mid Z)$ も非負。対称性も同様に、各 $z$ で命題 1.3.3 が
成り立つことから従う。$\qquad\blacksquare$

等号条件も各 $z$ に命題 1.3.2 を適用して読める：$I(X;Y\mid Z) = 0$ は、$p(z) > 0$ の各 $z$ で
$X$ と $Y$ が条件付き独立であること（$X \perp Y \mid Z$）と同値である。

> **形式化**: 非負性 `condMutualInfo_nonneg`、対称性 `condMutualInfo_comm`
> (`InformationTheory/Shannon/CondMutualInfo.lean`)。非負性は無条件相互情報量と同じく
> 拡張非負実数値であることからほぼ型レベルで従う。

## エントロピー表現

**定理 1.4.3.**
$$
I(X; Z \mid Y) \;=\; H(X \mid Y) - H(X \mid Y, Z).
$$
無条件版（定理 1.3.4）の $I(X;Z) = H(X) - H(X\mid Z)$ を、すべて「$Y$ を知った
うえで」に読み替えたものである。左辺が非負（命題 1.4.2）であることから
$H(X\mid Y,Z) \le H(X\mid Y)$ が読み取れるので、この等式は 1.2 節の条件付けの単調性
（定理 1.2.4）の別証明にもなっている。

*証明.* 定義 1.4.1 の各 $y$ ごとの項で、被加数の対数比を
$p(x,z\mid y) = p(x\mid y,z)\,p(z\mid y)$ を使って書き換えると
$$
\log\frac{p(x,z\mid y)}{p(x\mid y)\,p(z\mid y)}
  \;=\; \log\frac{p(x\mid y,z)}{p(x\mid y)}.
$$
これを $p(z\mid y)$ および $p(y)$ で重みづけて和をとると、重み
$p(y)\,p(x,z\mid y) = p(x,y,z)$ により
$$
I(X;Z\mid Y)
  \;=\; \sum_{x,y,z} p(x,y,z)\,\log p(x\mid y,z)
     \;-\; \sum_{x,y,z} p(x,y,z)\,\log p(x\mid y).
$$
第 1 項は定義 1.2.2 によりちょうど $-H(X\mid Y,Z)$。第 2 項は $z$ について先に和をとると
$\sum_z p(x,y,z) = p(x,y)$ なので $-\sum_{x,y} p(x,y)\log p(x\mid y) = -H(X\mid Y)$、
符号を込めて $+H(X\mid Y)$。合わせて $I(X;Z\mid Y) = H(X\mid Y) - H(X\mid Y,Z)$。
$\qquad\blacksquare$

> **形式化**: `condMutualInfo_eq_condEntropy_sub_condEntropy`
> (`InformationTheory/Shannon/Entropy.lean`)。形式化では左辺に `.toReal` を付けた等式
> として述べる（条件付き相互情報量が拡張非負実数値、条件付きエントロピーが実数値のため）。

