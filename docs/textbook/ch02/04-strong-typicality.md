# 2.4 強典型性

定義 2.2.1 の典型集合は、系列 $x$ について確率 $p(x)$ というただ一つの数しか見て
いない。そのため、まったく違う見た目の系列どうしが同じ典型集合に入りうる。$-\log p(x)$
は文字ごとの $-\log p(x_i)$ の和なので、ある文字が多すぎるぶんを別の文字が少なすぎる
ぶんが打ち消せば、経験的な出現頻度が真の分布からいくら離れていても、和としては
つじつまが合ってしまう。

本節では、この打ち消しを許さない、より細かい典型性を導入する。各文字の出現頻度が
真の確率に一様に近いことを直接要求するもので、**強典型性** と呼ばれる。定義 2.2.1 の
ほうは、区別するときには **弱典型性** と呼ぶ。強いほうを使うと、系列に含まれる文字の
構成そのものが分かるので、確率の値だけでは追えない議論ができる。長さ $n$ のブロックを
一対で扱い、入力側と出力側が「そろって典型的」であることを要求する第4章の通信路
符号化がその例である。

前節までと同じく、周辺分布は全アルファベット上で正とする（定理 2.4.4 で
$\log p(a)$ を各文字について足し上げるので、ここでは技術的にも必要になる）。

## 定義

::: definition 2.4.1 型と強典型集合
系列 $x \in \mathcal X^n$ に含まれる文字 $a$ の個数を $N(a \mid x)$ と書き、
$a \mapsto N(a\mid x)/n$ を $x$ の **型**（経験分布）と呼ぶ。$\varepsilon > 0$ に
対し、長さ $n$ の **強典型集合** を
$$
A^{*(n)}_\varepsilon
  \;:=\; \Big\{\, x \in \mathcal X^n \;:\;
    \Big| \frac{N(a\mid x)}{n} - p(a) \Big| \le \varepsilon
    \ \text{がすべての}\ a \in \mathcal X\ \text{で成り立つ} \,\Big\}
$$
で定める。
:::

弱典型性が $\mathcal X$ 上の和を 1 本とったあとの数を見るのに対し、強典型性は
$\mathcal X$ の各点で条件を課す。要求は文字数ぶんあり、しかもそれぞれが真の確率との
差を直接押さえている。「型」という呼び名は、$x$ をその経験分布で分類したときの
分類名という含みである。

::: example 2.4.2 弱典型だが強典型でない系列
$\mathcal X = \{0, 1, 2\}$、$p(0) = 1/2$、$p(1) = p(2) = 1/4$ とする。驚きの値は
$-\log p(0) = 1$、$-\log p(1) = -\log p(2) = 2$ で、エントロピーは
$$
H(X) \;=\; \tfrac12 \cdot 1 + \tfrac14 \cdot 2 + \tfrac14 \cdot 2 \;=\; 1.5
$$
である。$n$ を偶数とし、$0$ を $n/2$ 個、$1$ を $n/2$ 個含み、$2$ を一つも含まない系列
$x$ をとる。その経験エントロピーは
$$
-\tfrac1n \log p(x)
  \;=\; \tfrac12 \cdot \big(-\log \tfrac12\big) + \tfrac12 \cdot \big(-\log \tfrac14\big)
  \;=\; \tfrac12 \cdot 1 + \tfrac12 \cdot 2 \;=\; 1.5
$$
となり、ちょうど $H(X)$ に一致する。したがって $x$ はどんな $\varepsilon > 0$ に
対しても弱典型である。一方その型 $(1/2,\ 1/2,\ 0)$ は真の分布 $(1/2,\ 1/4,\ 1/4)$ と
第 2・第 3 座標で $1/4$ ずれているので、$\varepsilon < 1/4$ なら強典型ではない。
:::

例 2.4.2 が起きたのは $-\log p(1) = -\log p(2)$ だったからである。$1$ を 1 個増やして
$2$ を 1 個減らしても $-\log p(x)$ はまったく変わらない。弱典型性はこの取り換えに
対して盲目で、強典型性は盲目でない。二値アルファベットではこの現象は起きず、例 2.2.2
で見たように弱典型性の条件は頻度の条件そのものになる。文字が 3 つ以上あって初めて
二つの概念は分かれる。

## 性質1：強典型集合に入る確率も 1 に近づく

::: theorem 2.4.3
任意の $\varepsilon > 0$ に対し
$\Pr\big[X^n \in A^{*(n)}_\varepsilon\big] \to 1$（$n \to \infty$）。
:::

::: proof
文字 $a$ を一つ固定し、指示変数 $Z^{(a)}_i := \mathbf 1[X_i = a]$ を考える。$Z^{(a)}_i$ は
$X_i$ だけの関数だから i.i.d. であり、$\mathbb E[Z^{(a)}_i] = \Pr[X_i = a] = p(a)$、
値は $\{0,1\}$ に収まるので有界である。個数はこの指示変数の和
$N(a \mid X^n) = \sum_{i<n} Z^{(a)}_i$ だから、大数の法則より
$$
\Pr\Big[\ \Big|\frac{N(a\mid X^n)}{n} - p(a)\Big| > \varepsilon\ \Big]
  \;\longrightarrow\; 0 .
$$
$\mathcal X$ は有限なので、この事象を $a$ にわたって合併しても、確率の劣加法性
（合併の確率は和以下）より
$$
\Pr\big[X^n \notin A^{*(n)}_\varepsilon\big]
  \;\le\; \sum_{a \in \mathcal X}
    \Pr\Big[\ \Big|\frac{N(a\mid X^n)}{n} - p(a)\Big| > \varepsilon\ \Big]
  \;\longrightarrow\; 0
$$
であり、有限個の 0 に収束する列の和はやはり 0 に収束する。
:::

証明の形は定理 2.1.4 と同じ——i.i.d. な有界確率変数の相加平均に大数の法則を
当てる——だが、当てる対象が違う。定理 2.1.4 では対数尤度 $-\log p(X_i)$ という
1 本の実数値量に当てたのに対し、ここでは文字ごとの指示変数に文字数ぶん当てて、
最後に合併している。アルファベットが有限であることが、この「文字数ぶん」を
有限個に留めるために効いている。

## 性質2：強典型なら弱典型

::: theorem 2.4.4
$L := \sum_{a \in \mathcal X} \big|\log p(a)\big|$ とおく。$\varepsilon L < \varepsilon'$
ならば
$$
A^{*(n)}_\varepsilon \;\subseteq\; T^{(n)}_{\varepsilon'} .
$$
:::

::: proof
経験エントロピーを型で書き直す。$-\log p(x) = \sum_{i<n}\big(-\log p(x_i)\big)$ の
和を、同じ文字ごとにまとめると
$$
-\frac1n \log p(x)
  \;=\; \sum_{a \in \mathcal X} \frac{N(a\mid x)}{n}\,\big(-\log p(a)\big)
$$
である。一方 $H(X) = \sum_a p(a)\big(-\log p(a)\big)$ だから、差は
$$
-\frac1n\log p(x) - H(X)
  \;=\; \sum_{a\in\mathcal X}
    \Big(\frac{N(a\mid x)}{n} - p(a)\Big)\big(-\log p(a)\big)
$$
と、型の各座標のずれの一次結合になる。$x \in A^{*(n)}_\varepsilon$ なら各座標のずれは
絶対値 $\varepsilon$ 以下だから、三角不等式で
$$
\Big| -\frac1n\log p(x) - H(X) \Big|
  \;\le\; \varepsilon \sum_{a\in\mathcal X}\big|\log p(a)\big| \;=\; \varepsilon L
  \;<\; \varepsilon' ,
$$
すなわち $x \in T^{(n)}_{\varepsilon'}$ である。
:::

この計算は、弱典型性と強典型性の関係をそのまま式にしている。経験エントロピーと
$H(X)$ のずれは、型のずれを係数 $-\log p(a)$ で重みづけて足したものにすぎない。
だから型のずれを全座標で小さくすれば、経験エントロピーのずれも小さくなる——これが
包含の内容である。逆向きが成り立たないのは、この一次結合が符号の違う項どうしで
打ち消しあえるからで、例 2.4.2 はその打ち消しをちょうど起こしてみせた例である。
定数 $L$ は打ち消しを最悪の場合で見積もったときの増幅率にあたり、真の確率に
きわめて小さい値があると大きくなる。

## 性質3：強典型集合の大きさ

::: corollary 2.4.5
$L$ を定理 2.4.4 のものとし、$\delta > 0$、$\eta \in (0,1)$ とする。$n$ が十分大きければ
$$
(1-\eta)\,2^{n(H(X) - \varepsilon L - \delta)}
  \;\le\; \big|A^{*(n)}_\varepsilon\big|
  \;\le\; 2^{n(H(X) + \varepsilon L + \delta)} .
$$
:::

::: proof
$\varepsilon' := \varepsilon L + \delta$ とおくと $\varepsilon L < \varepsilon'$ だから、
定理 2.4.4 より $A^{*(n)}_\varepsilon \subseteq T^{(n)}_{\varepsilon'}$ である。

**上界.** 包含と定理 2.2.5 の上界から
$$
\big|A^{*(n)}_\varepsilon\big| \;\le\; \big|T^{(n)}_{\varepsilon'}\big|
  \;\le\; 2^{n(H(X)+\varepsilon')}
$$
であり、これは任意の $n$ で成り立つ。

**下界.** 定理 2.4.3 より、$n$ を十分大きくとれば
$\Pr[X^n \in A^{*(n)}_\varepsilon] \ge 1-\eta$ にできる。包含より
$A^{*(n)}_\varepsilon$ の元はすべて $T^{(n)}_{\varepsilon'}$ の元だから、定理 2.2.4 の
上界が各元に使えて
$$
1-\eta \;\le\; \sum_{x \in A^{*(n)}_\varepsilon} p(x)
  \;\le\; \big|A^{*(n)}_\varepsilon\big| \cdot 2^{-n(H(X)-\varepsilon')} .
$$
両辺に $2^{n(H(X)-\varepsilon')}$ を掛ければ下界を得る。
:::

系 2.4.5 は定理 2.2.5 とほとんど同じ形をしている。強典型集合も、弱典型集合と同じく
約 $2^{nH}$ 個の元をもつということである。$\varepsilon$ を小さくすれば
$\varepsilon L$ も小さくなるので、指数の肩の幅はいくらでも狭くできる。強典型性は
条件としては弱典型性より真に強いのに、数え上げの粗さでは同じ答えに行き着く。
指数の肩を $1/n$ の精度でしか見ていないので、両者の差はこの尺度には現れない
——差が見えるのは、個数を数えるときではなく、系列に含まれる文字の構成を直接
問うときである。

**弱典型側からの借りもの.** 上界と下界のどちらも、強典型集合そのものを数えたのでは
なく、弱典型集合の評価を包含を通じて借りてきている。系 2.4.5 は強典型性そのものの
性質というより、包含（定理 2.4.4）を通して弱典型集合の勘定が伝わったものである。

::: formalization-note
形式化では定理 2.4.4 の定数 $L$ が `logSumAbs` として明示的に定義されており、
包含 `stronglyTypicalSet_subset_typicalSet` はその値を使って述べられている。

系 2.4.5 の上界に対応する単独の宣言は形式化されていない。本文の証明と同じく、
包含 `stronglyTypicalSet_subset_typicalSet` と弱典型側の上界 `typicalSet_card_le`
（2.2 節）の合成として得られる形になっている。下界のほうは、$n$ の存在を含んだ
`stronglyTypicalSet_card_ge_eventually` として単独で形式化されている。

定理 2.4.3 の形式化は、本文の証明と同じく文字ごとの指示変数 `letterIndicator` に
大数の法則を当てて合併している。この経路は対独立で足りるが、系 2.4.5 の下界は
典型系列の点ごとの確率評価（定理 2.2.4）を経由するため相互独立を要求する。
:::

::: formalized
型 `typeCount` (`InformationTheory/Shannon/Sanov/Basic.lean`)
:::

::: formalized
強典型集合の定義 `stronglyTypicalSet`、可測性
`measurableSet_stronglyTypicalSet`、確率の収束
`stronglyTypicalSet_prob_tendsto_one`、増幅率 `logSumAbs`、弱典型性への包含
`stronglyTypicalSet_subset_typicalSet`、要素数の下界
`stronglyTypicalSet_card_ge_eventually`
(`InformationTheory/Shannon/StrongTypicality.lean`)
:::
