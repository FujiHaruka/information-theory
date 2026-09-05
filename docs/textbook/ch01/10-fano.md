# 1.10 ファノの不等式

$Y$ を観測して $X$ を推定（復号）したい．$Y$ から $X$ を当てる復号器$\hat X = g(Y)$ の誤り確率を $P_e = \Pr[\hat X \neq X]$ とする．直感的に，$X$ に残る不確かさ $H(X\mid Y)$ が大きければ，どんな復号器でも誤りはそう小さくできないはずだ．ファノの不等式はこの直感を定量化する．

ここまでの節との関係でいうと，本章はずっと**情報量の不等式**を積み上げてきた．しかし最終的に知りたいのは「実際に何回間違えるか」という**確率**である．ファノの不等式は，その二つを結ぶ唯一の橋である．「$H(X\mid Y)$ が大きい」という情報量の言明から「$P_e$ が小さくできない」という確率の言明へ渡れるようになって初めて，通信路符号化の逆定理（容量を超えるレートでは誤りが消えない）が証明できる．橋の向きが片方向であることにも注意したい：不等式は $H(X\mid Y)$ を $P_e$ で**上から**抑える形をしており，これを裏返して $P_e$ の**下界**として使うのが実際の用途である．

## 主張と証明

::: theorem 1.10.1 ファノの不等式
$|\mathcal X| \ge 2$ とし，$g : \mathcal Y \to \mathcal X$ を任意の復号器，$\hat X = g(Y)$，$P_e = \Pr[\hat X \neq X]$ とする．このとき
$$
H(X \mid Y) \;\le\; H_b(P_e) + P_e \log\big(|\mathcal X| - 1\big),
$$
ここで $H_b$ は二値エントロピー関数（例 1.1.2）．
:::

右辺を読み解くと，$X$ に残る不確かさは「誤ったか否か」の 1 ビット$H_b(P_e)$ と，「誤ったとき，残り $|\mathcal X|-1$ 個のどれか」の不確かさ$P_e \log(|\mathcal X|-1)$ で説明しきれる，という上限になっている．裏返せば，$H(X\mid Y)$ が大きいのに $P_e$ を小さく保つことはできない．$H(X\mid Y) \to$ 大なら $P_e$ も下から押し上げられる．

::: proof
誤り指示変数 $E := \mathbf 1[\hat X \neq X]$（$\hat X = g(Y)$）を導入する．これは$\Pr[E=1] = P_e$ の二値確率変数である．結合量 $H(E, X \mid Y)$ を，$Y$ で条件付けたチェイン則（定理 1.2.3 を $Y$ のもとで適用）で二通りに展開する：
$$
H(E, X \mid Y) \;=\; H(X\mid Y) + H(E\mid X, Y)
            \;=\; H(E\mid Y) + H(X\mid E, Y).
$$

左の展開から見る．$\hat X = g(Y)$ は $Y$ の関数なので，$E = \mathbf 1[g(Y)\neq X]$ は対$(X,Y)$ から一意に決まる．決定的な量のエントロピーは 0 だから $H(E\mid X,Y) = 0$，ゆえに $H(E,X\mid Y) = H(X\mid Y)$．

右の展開は，二項を個別に上から抑える．

- $H(E\mid Y) \le H(E)$：条件付けは平均エントロピーを増やさない（定理 1.2.4 の基本形）．$E$ は $\Pr[E = 1] = P_e$ の二値なので $H(E) = H_b(P_e)$．よって$H(E\mid Y) \le H_b(P_e)$．

- $H(X\mid E, Y)$ を $E$ の二値で分ける：
  $$
  H(X\mid E,Y) = (1-P_e)\,H(X\mid Y, E{=}0) + P_e\,H(X\mid Y, E{=}1).
  $$
  ここで $H(X\mid Y, E{=}e)$ は 1.2 節で断った混合記法，すなわち $E = e$ に固定した世界での $H(X\mid Y)$ である（$y$ についての平均は条件付き分布 $p(y\mid E{=}e)$ でとる）．$E=0$ のときは $X = \hat X = g(Y)$ が $Y$ で決まるので $H(X\mid Y, E{=}0) = 0$．$E=1$ のときは $X$ が $g(Y)$ 以外，すなわち高々 $|\mathcal X|-1$ 個の値しかとらないので，最大エントロピー上界（定理 1.1.5）より $H(X\mid Y, E{=}1) \le \log(|\mathcal X|-1)$．したがって $H(X\mid E,Y) \le P_e \log(|\mathcal X|-1)$．

左の展開の等式と右の二つの上界を合わせて
$$
H(X\mid Y) \;=\; H(E\mid Y) + H(X\mid E,Y)
  \;\le\; H_b(P_e) + P_e\log(|\mathcal X|-1).
$$
:::

::: formalization-note 実現が二つある
本ライブラリはこの不等式を，有限結合 pmf に対する形と，測度空間上の確率変数に対する形の二通りで実現している．前者は推定値そのもので条件付けた核（`fano_core` / `fano_inequality`）で，復号器を経る形はそこからデータ処理不等式で復元する（`fano_inequality_decode`）．後者は本文の定理 1.10.1 と同じく復号器 $g$ を引数にとる．数学的内容はどれも同じである．
:::

::: formalized
測度論版 `fano_inequality_measure_theoretic` (`InformationTheory/Fano/Measure.lean`)，pmf 形の核 `fano_core` / `fano_inequality` (`InformationTheory/Fano/Core.lean`)，復号器を明示した pmf 形 `fano_inequality_decode` (`InformationTheory/Fano/DPI.lean`)
:::

## 裏返して使う

ファノの不等式を裏返すと，$H(X\mid Y)$ が大きいときに $P_e$ が下から評価される．これが逆定理で実際に使う向きである．

::: corollary 1.10.2 誤り確率の下界
定理 1.10.1 と同じ設定で，$a$ を $0 \le a \le 1 - 1/|\mathcal X|$ を満たす実数，$P_e$ も同じ範囲にあるとする．このとき
$$
H_b(a) + a\log\big(|\mathcal X| - 1\big) \;<\; H(X\mid Y)
\quad\Longrightarrow\quad
a \;<\; P_e .
$$
:::

::: proof
対偶をとる．$P_e \le a$ とすると，右辺$H_b(t) + t\log(|\mathcal X|-1)$ は $t$ について区間 $[0,\, 1 - 1/|\mathcal X|]$ 上で増加なので（この区間が「$P_e$ が小さい範囲」の正確な意味である），$H_b(P_e) + P_e\log(|\mathcal X|-1) \le H_b(a) + a\log(|\mathcal X|-1)$．定理 1.10.1 と合わせると $H(X\mid Y) \le H_b(a) + a\log(|\mathcal X|-1)$ となり，仮定の狭義不等式に反する．
:::

右辺が増加する範囲に留まっているかぎり，$H(X\mid Y)$ の下界を持っていれば $P_e$ の下界が出る．第6章では，レートが容量を超えるという仮定から $H(X\mid Y)$ が大きいことを導き，ここを通して「誤り確率は 0 に収束しない」を結論する．効いているのは**復号器 $g$ を任意にとれる**ことである．定理 1.10.1 が $g$ について何も仮定していないので，系 1.10.2 もどんな復号器に対しても成り立つ．これが「どんな復号器を設計しても」という逆定理の普遍性の出どころである．$P_e$ 自身に置いた $P_e \le 1 - 1/|\mathcal X|$ という制約は，右辺の増加域に留まるための条件で，逆定理が扱う「誤り確率が小さい」領域では自動的に満たされる．

::: formalized
復号器を明示した形 `error_lower_bound_decode` (`InformationTheory/Fano/DPI.lean`)，その核 `error_lower_bound` (`InformationTheory/Fano/Core.lean`)
:::

