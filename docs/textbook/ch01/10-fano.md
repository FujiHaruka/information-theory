# 1.10 ファノの不等式

$Y$ を観測して $X$ を推定（復号）したい。$Y$ から $X$ を当てる復号器
$\hat X = g(Y)$ の誤り確率を $P_e = \Pr[\hat X \neq X]$ とする。直感的に、$X$ に
残る不確かさ $H(X\mid Y)$ が大きければ、どんな復号器でも誤りはそう小さくできない
はずだ。ファノの不等式はこの直感を定量化し、**誤り確率を条件付きエントロピーで下から
評価する**。通信路符号化の逆定理（容量を超えるレートでは誤りが消えない）の証明で
中心的役割を果たす。

## 主張と証明

**定理 1.10.1（ファノの不等式）.** $|\mathcal X| \ge 2$ のとき
$$
H(X \mid Y) \;\le\; H_b(P_e) + P_e \log\big(|\mathcal X| - 1\big),
$$
ここで $H_b$ は二値エントロピー関数（例 1.1.2）。

**きもち.** 右辺を読み解くと、$X$ に残る不確かさは「誤ったか否か」の 1 ビット
$H_b(P_e)$ と、「誤ったとき、残り $|\mathcal X|-1$ 個のどれか」の不確かさ
$P_e \log(|\mathcal X|-1)$ で説明しきれる、という上限になっている。裏返せば、
$H(X\mid Y)$ が大きいのに $P_e$ を小さく保つことはできない。$H(X\mid Y) \to$ 大
なら $P_e$ も下から押し上げられる。

*証明.* 誤り指示変数 $E := \mathbf 1[\hat X \neq X]$（$\hat X = g(Y)$）を導入する。これは
$\Pr[E=1] = P_e$ の二値確率変数である。結合量 $H(E, X \mid Y)$ を、$Y$ で条件付けた
チェイン則（定理 1.2.3 を $Y$ のもとで適用）で二通りに展開する：
$$
H(E, X \mid Y) \;=\; H(X\mid Y) + H(E\mid X, Y)
            \;=\; H(E\mid Y) + H(X\mid E, Y).
$$

**左の展開.** $\hat X = g(Y)$ は $Y$ の関数なので、$E = \mathbf 1[g(Y)\neq X]$ は対
$(X,Y)$ から一意に決まる。決定的な量のエントロピーは 0 だから $H(E\mid X,Y) = 0$、
ゆえに $H(E,X\mid Y) = H(X\mid Y)$。

**右の展開を上から評価.** 二項を個別に抑える。

- $H(E\mid Y) \le H(E)$：条件付けは平均エントロピーを増やさない（定理 1.2.4 の基本形）。
  $E$ は成功確率 $P_e$ の二値なので $H(E) = H_b(P_e)$。よって $H(E\mid Y) \le H_b(P_e)$。

- $H(X\mid E, Y)$ を $E$ の二値で分ける：
  $$
  H(X\mid E,Y) = (1-P_e)\,H(X\mid Y, E{=}0) + P_e\,H(X\mid Y, E{=}1).
  $$
  $E=0$ のときは $X = \hat X = g(Y)$ が $Y$ で決まるので $H(X\mid Y, E{=}0) = 0$。
  $E=1$ のときは $X$ が $g(Y)$ 以外、すなわち高々 $|\mathcal X|-1$ 個の値しかとらないので、
  最大エントロピー上界（定理 1.1.5）より $H(X\mid Y, E{=}1) \le \log(|\mathcal X|-1)$。
  したがって $H(X\mid E,Y) \le P_e \log(|\mathcal X|-1)$。

**結合.** 左の展開の等式と右の二つの上界を合わせて
$$
H(X\mid Y) \;=\; H(E\mid Y) + H(X\mid E,Y)
  \;\le\; H_b(P_e) + P_e\log(|\mathcal X|-1).
\qquad\blacksquare
$$

## 形式化されている諸形

本ライブラリは pmf 形と測度論形の両方を形式化している。

**測度論版（決定論的復号器）.** 復号器 $g : \mathcal Y \to \mathcal X$ と
誤り確率 $P_e = \mu\{\omega : X(\omega) \neq g(Y(\omega))\}$ に対し、定理 1.10.1 を
$H(X\mid Y) \le H_b(P_e) + P_e\log(|\mathcal X|-1)$ の形で述べる。

> **形式化**: `fano_inequality_measure_theoretic`
> (`InformationTheory/Fano/Measure.lean`, 名前空間 `InformationTheory.MeasureFano`)

**pmf コア版.** 有限結合 pmf に対する基本形（$\mathrm{qaryEntropy}$ 形）。

> **形式化**: `fano_core` / `fano_inequality` (`InformationTheory/Fano/Core.lean`)

**逆向き（誤り確率の下界）.** ファノの不等式を裏返すと、$H(X\mid Y)$ が大きいときに
$P_e$ が下から評価される。条件付きエントロピーが二値エントロピー境界を超えるなら、
誤り確率は対応する閾値より真に大きい。

> **形式化**: `error_lower_bound` (`InformationTheory/Fano/Core.lean`)

