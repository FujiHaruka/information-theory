# 1.7 対数和不等式

情報不等式の「部品」をもう一つ独立に切り出しておくと、後の証明が楽になる。非負の
$a_i$ と正の $b_i$ に対し、「比をまとめてから測る」より「個別に測って足す」ほうが
大きい、という不等式である。

**定理 1.7.1（対数和不等式）.** 非負 $a_i$ と正 $b_i$（$i=1,\dots,n$）に対し
$$
\Big(\sum_i a_i\Big) \log\frac{\sum_i a_i}{\sum_i b_i}
  \;\le\; \sum_i a_i \log\frac{a_i}{b_i}.
$$
等号は、すべての比 $a_i/b_i$ が等しいときに限る。

**きもち.** これは $t \mapsto t\log t$ の凸性（＝ $\varphi = -t\log t$ の凹性、1.1.5 の
信頼の底）を、重み $b_i$ つきで述べ直したものである。情報不等式や、相対エントロピーが
「まとめる」操作で減ること（次節のデータ処理不等式の心臓部）が、この一枚から従う。

*証明.* $b := \sum_i b_i > 0$ とおき、$\lambda_i := b_i/b$（$\sum_i \lambda_i = 1$、
$\lambda_i \ge 0$）、$t_i := a_i/b_i \ge 0$ とする。凸関数 $\psi(t) := t\log t$
（$\varphi = -t\log t$ の凹性、1.1.5 の信頼の底の符号反転）に対する有限 Jensen——補題
1.1.6 を $-\psi$ に適用して符号を返したもの——は、重み $\lambda_i$・点 $t_i$ に対し
$$
\psi\Big(\sum_i \lambda_i t_i\Big) \;\le\; \sum_i \lambda_i\, \psi(t_i)
\tag{$\dagger$}
$$
を与える。両辺を具体的に計算する。重心は
$\sum_i \lambda_i t_i = \sum_i \dfrac{b_i}{b}\cdot\dfrac{a_i}{b_i} = \dfrac{\sum_i a_i}{b}$
なので、左辺は
$$
\psi\Big(\frac{\sum_i a_i}{b}\Big)
  = \frac{\sum_i a_i}{b}\,\log\frac{\sum_i a_i}{b}.
$$
右辺は
$$
\sum_i \lambda_i\,\psi(t_i)
  = \sum_i \frac{b_i}{b}\cdot\frac{a_i}{b_i}\log\frac{a_i}{b_i}
  = \frac1b \sum_i a_i \log\frac{a_i}{b_i}.
$$
$(\dagger)$ の両辺を $b$ 倍すると、$b = \sum_i b_i$ より
$$
\Big(\sum_i a_i\Big)\log\frac{\sum_i a_i}{\sum_i b_i}
  \;\le\; \sum_i a_i\log\frac{a_i}{b_i}.
$$
等号は補題 1.1.6 の等号条件（$\psi$ は狭義凸）より、正の重みをもつ $t_i = a_i/b_i$ が
すべて等しいときに限る。$\qquad\blacksquare$

> **形式化**: `log_sum_inequality`
> (`InformationTheory/Shannon/LZ78ZivEntropyBridge.lean`, 名前空間
> `InformationTheory.Shannon`)。絶対連続条件 $b_i = 0 \Rightarrow a_i = 0$ を許す
> `negMulLog` 形 `log_sum_inequality_negMulLog` (`InformationTheory/Fano/DPI.lean`) もある。

