# 1.9 充足統計量

データ $X$ からパラメータ $\theta$ を推定するとき、$X$ を要約した統計量 $T(X)$ だけ
持っていれば $\theta$ について $X$ と同じだけ分かる、という状況がある。このとき $T$ を
**充足統計量** という。「生データを捨てて要約だけ残しても情報が落ちない」境界を
特徴づける概念で、データ処理不等式の等号版として自然に位置づく。

## 定義

**定義 1.9.1（充足統計量）.** 統計量 $T(X)$ が $\theta$ に対し**充足的**であるとは、
$\theta \to T(X) \to X$ がマルコフ連鎖をなすこと（同値に $X \perp \theta \mid T(X)$）。

## 情報の保存

**定理 1.9.2.** $T$ が充足的なら
$$
I(\theta; X) \;=\; I\big(\theta; T(X)\big).
$$

*証明.* 一般に後処理不等式（定理 1.8.2）から $I(\theta; T(X)) \le I(\theta; X)$。一方、
充足性すなわちマルコフ連鎖から DPI のマルコフ版（定理 1.8.3）が逆向き
$I(\theta; X) \le I(\theta; T(X))$ を与える。両者を挟めば等号。$\qquad\blacksquare$

**きもち.** 一般のデータ処理は情報を減らしうる（$\le$）。充足統計量はその等号がちょうど
成り立つ「情報を一切落とさない要約」である。十分統計量を使えば、推定の議論を低次元の
$T(X)$ 上で行ってよい、という実用上の御利益がある。

> **形式化上の注記.** 教科書は充足性を因子分解 $p(x\mid\theta) = g(T(x),\theta)\,h(x)$
> （Neyman–Fisher）で導入することが多い。本ライブラリは、定理 1.8.3 の結論に直結する
> **マルコフ連鎖形**でまず定義し（因子分解形を直接 def 化すると条件付き分布の
> $\theta$-非依存性を経由する長い橋渡しを要するため）、因子分解形
> `IsSufficientStatisticFactorized` との**同値** `isSufficient_iff_factorized` を別途
> 形式化している。同値は Mathlib の条件付き独立性補題（標準ボレル機構）を経由する。
>
> **形式化**: 定義 `IsSufficientStatistic`、情報保存 `mutualInfo_eq_of_sufficient`、
> 因子分解形との同値 `isSufficient_iff_factorized`
> (`InformationTheory/Shannon/SufficientStatistic.lean`)

