# 1.8 データ処理不等式

「データをいじっても、もとになかった情報は生まれない」——これは情報理論の格率の
一つである。受け取った $Y$ にどんな後処理 $f$ を施しても、$X$ について新たに知れる
ことは増えない。形式的には相互情報量の単調性として述べられ、推定・統計的決定・
通信路符号化の限界を支配する。本節ではこれを段階的に組み立てる。

## KL ダイバージェンスの単調性（土台）

**定理 1.8.1.** 任意の可測写像 $f$ による push-forward で相対エントロピーは増えない：
$$
D\big(\mu\circ f^{-1} \,\big\|\, \nu\circ f^{-1}\big) \;\le\; D(\mu\,\|\,\nu).
$$
「分布を $f$ で粗くまとめると、二つの分布の見分けはつきにくくなる（区別の情報が減る）」
という、1.7 節の対数和不等式の直接の帰結である。これがデータ処理不等式すべての土台になる。

> **形式化**: `klDiv_map_le` (`InformationTheory/Shannon/DPI.lean`)

## 後処理は相互情報量を増やさない

**定理 1.8.2（後処理不等式）.** $Y$ を後処理 $f$ に通すと相互情報量は増えない：
$$
I\big(X; f(Y)\big) \;\le\; I(X; Y).
$$

*証明.* 写像 $g(x,y) := (x, f(y))$ を考え、定理 1.8.1 を $\mu \leftarrow p_{X,Y}$
（同時分布）、$\nu \leftarrow p_X \otimes p_Y$（周辺積）に対して $g$ で適用する。鍵は次の
二つの push-forward 等式である。

(i) $g$ で同時分布を送ると $(X, f(Y))$ の同時分布になる：
$g_*\,p_{X,Y} = p_{X, f(Y)}$。実際 $g(X,Y) = (X, f(Y))$ だから定義どおり。

(ii) $g$ で周辺積を送ると、第 2 成分だけが $f$ で送られて
$g_*\,(p_X \otimes p_Y) = p_X \otimes (f_*\,p_Y) = p_X \otimes p_{f(Y)}$。$f(Y)$ の周辺分布は
$f_*\,p_Y = p_{f(Y)}$ なので、これは $X$ と $f(Y)$ の周辺積にほかならない。

したがって、定理 1.8.1（$D(g_*\mu \,\|\, g_*\nu) \le D(\mu\,\|\,\nu)$）は
$$
\underbrace{D\big(p_{X,f(Y)} \,\big\|\, p_X \otimes p_{f(Y)}\big)}_{=\,I(X;f(Y))}
  \;\le\;
\underbrace{D\big(p_{X,Y} \,\big\|\, p_X \otimes p_Y\big)}_{=\,I(X;Y)}
$$
となり、定義 1.3.1 により $I(X;f(Y)) \le I(X;Y)$。$\qquad\blacksquare$

> **形式化**: `mutualInfo_le_of_postprocess` (`InformationTheory/Shannon/DPI.lean`)

## マルコフ連鎖版

**定理 1.8.3（データ処理不等式・マルコフ版）.** $X \to Z \to Y$ がマルコフ連鎖
（$Z$ を与えると $X$ と $Y$ が条件付き独立）のとき、
$$
I(X; Y) \;\le\; I(Z; Y).
$$
「$X$ の情報が中継変数 $Z$ を経由してしか $Y$ に届かないなら、$Y$ が $X$ について持つ
情報は $Z$ が持つ情報を超えない」。中継地点がボトルネックになる、という直感そのものである。

*証明.* 対 $(X,Z)$ が $Y$ について持つ情報 $I(X,Z;Y)$ を、チェイン則（定理 1.5.1）で
二通りに展開する：
$$
I(X,Z;Y) = I(Z;Y) + I(X;Y\mid Z), \qquad
I(X,Z;Y) = I(X;Y) + I(Z;Y\mid X).
$$
（後者は前者で $X$ と $Z$ の役割を入れ替えたもの。$I(X,Z;Y)$ は対の取り方の順序に
よらない。）マルコフ連鎖 $X\to Z\to Y$ は「$Z$ を与えたとき $X\perp Y$」を意味し、これは
ちょうど条件付き相互情報量がゼロ、$I(X;Y\mid Z) = 0$ ということである。よって第 1 式から
$I(X,Z;Y) = I(Z;Y)$。これを第 2 式に代入すると
$$
I(Z;Y) = I(X;Y) + I(Z;Y\mid X).
$$
条件付き相互情報量の非負性（命題 1.4.2）より $I(Z;Y\mid X) \ge 0$ だから、
$I(Z;Y) \ge I(X;Y)$、すなわち $I(X;Y) \le I(Z;Y)$。$\qquad\blacksquare$

> **形式化上の注記.** 形式化はマルコフ連鎖を、結合分布の条件付き独立分解
> $\mu.\mathrm{map}(Z,X,Y) = (\mu.\mathrm{map}\,Z) \otimes ((K_X) \times (K_Y))$ という
> compProd 等式 `IsMarkovChain` で定義する。教科書の矢印記法 $X\to Z\to Y$ とは表層が
> 異なるが、内容は「$Z$ を与えたとき $X \perp Y$」で同じ。まずマルコフ下で
> $I(X;Y\mid Z)=0$（`condMutualInfo_eq_zero_of_markov`）を示し、そこから本定理を導く。
> なお本ライブラリの結論は $I(X;Y) \le I(Z;Y)$ の形（中継 $Z$ を $Y$ 側と組む配置）で、
> 教科書でよく見る $I(X;Y) \le I(X;Z)$ とは引数配置が異なるが、どちらも DPI の正しい一形態
> である。
>
> **形式化**: 定義 `IsMarkovChain`、本定理 `mutualInfo_le_of_markov`
> (`InformationTheory/Shannon/CondMutualInfo.lean`)

## 応用：記憶のない通信路の per-letter 分解

DPI の代表的な応用として、記憶のない（memoryless）通信路では、$n$ 文字をまとめて
送ったときの相互情報量が 1 文字ずつの寄与の和を超えない：
$$
I(X^n; Y^n) \;\le\; \sum_{i} I(X_i; Y_i).
$$
これは通信路容量が「1 文字あたり」で決まることの根拠で、第 4 章を先取りする結果である。

> **形式化**: `mutualInfo_le_sum_per_letter_of_memoryless_strong`
> (`InformationTheory/Shannon/CondEntropyMemoryless.lean`)。形式化では memoryless 構造を
> 二つの `IsMarkovChain` 仮定（各文字の入力が他文字を経由しないこと、出力が条件付き独立で
> あること）として与える。これらは通信路の構造そのものを表す前提条件で、結論の核心を
> 仮定に抱えさせるものではない。

