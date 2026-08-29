# 1.5 条件付き相互情報量

1.4 節のチェイン則に現れた $I(X; Y \mid Z)$ を正面から定義しよう。これは「$Z$ を
すでに知っているという条件のもとで、$X$ と $Y$ がなお共有している情報量」である。
各 $z$ ごとに $X, Y$ の相互情報量を測り、$z$ について平均する。

## 定義

**定義 1.5.1（条件付き相互情報量）.**
$$
I(X; Y \mid Z)
  \;=\; \sum_z p(z)\, D\big(p(x,y \mid z)\,\big\|\,p(x\mid z)\,p(y\mid z)\big).
$$
各 $z$ で「$Z=z$ のもとでの同時分布」が「$Z=z$ のもとで独立だったら」の分布から
どれだけ離れているかを測り、$Z$ で平均した量である。

> **形式化上の注記.** 本ライブラリは条件付き分布カーネルの compProd 形に対する KL として
> 定義する（`klDiv` の引数に $\mu.\mathrm{map}\,Z$ と核の合成積を渡す）。値は拡張非負実数。
>
> **形式化**: `condMutualInfo` (`InformationTheory/Shannon/CondMutualInfo.lean`)

## 基本性質

**命題 1.5.2.** $I(X; Y \mid Z) \ge 0$。また $I(X; Y \mid Z) = I(Y; X \mid Z)$（対称性）。

非負性は各 $z$ で相対エントロピーが非負（1.6 節）であることの平均から、対称性は
1.3.3 と同様に各 $z$ で成り立つことから従う。

> **形式化**: 非負性 `condMutualInfo_nonneg`、対称性 `condMutualInfo_comm`
> (`InformationTheory/Shannon/CondMutualInfo.lean`)。非負性は無条件相互情報量と同じく
> 拡張非負実数値であることからほぼ型レベルで従う。

## エントロピー表現

**定理 1.5.3.**
$$
I(X; Z \mid Y) \;=\; H(X \mid Y) - H(X \mid Y, Z).
$$
無条件版（定理 1.3.4）の $I(X;Z) = H(X) - H(X\mid Z)$ を、すべて「$Y$ を知った
うえで」に読み替えたものである。この等式の左辺が非負であることが、1.2 節の条件付けの
単調性（定理 1.2.4）$H(X\mid Y,Z) \le H(X\mid Y)$ をそのまま与える。

*証明.* 定義 1.5.1 の各 $y$ ごとの相対エントロピーで、被加数の対数比を
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

