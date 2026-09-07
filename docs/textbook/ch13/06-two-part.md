# 13.6 二部記述と最小記述長

13.4 節と 13.5 節は，一つに固定した機械 $\mathcal V$ について，記述長・重み・停止の三つを調べてきた．本節は記述の作り方のほうに戻る．第12章 定義 12.2.1 の型による二段符号は，系列を「まず型を送り，次に型類の中の位置を送る」と分けて書いた．前半が系列の型を，後半が型だけでは決まらないぶんを担う．同じ分け方を，分布も情報源も持たない一つの自然数に当てるのが本節である．型にあたるのは $x$ を含む有限集合 $S$ で，位置にあたるのは $S$ の中での $x$ の番号である．

分け方を変えても記述の長さは変えられない，というのが本節の結論である．どんな $S$ をとっても二つに分けた記述は $K_{\mathcal V}(x)$ より短くならず（定理 13.6.3），いちばんうまい $S$ をとれば $K_{\mathcal V}(x)$ と定数の差まで縮む（定理 13.6.8）．そのうえで，$S$ が $x$ をどこまで説明していると言えるかを，定数のゆるみを許して定める．

## 有限集合を記述する

::: definition 13.6.1 有限集合の符号と模型の記述長
自然数の有限列に自然数を対応させる符号化を一つ固定する．有限列から自然数を求める手続きと，自然数から有限列を復元する手続きがどちらも書き下せるようなものをとる（たとえば，各項の二進表示の自己限定形（定義 13.4.3）をこの順につなぎ，先頭にもう一つ $1$ を置いたビット列が表す自然数がそれである）．$S \subseteq \mathbb N$ を空でない有限集合とし，$S$ の要素を小さい順に並べた有限列に，固定した符号化が与える自然数を $\langle S\rangle$ と書く（定義 13.3.1 と同じ，有限の対象を自然数に写す符号化である）．$K_{\mathcal V}(\langle S\rangle)$ を $S$ の **模型の記述長** と呼ぶ．
:::

::: formalized
符号 `modelCode`，模型の記述長 `modelComplexity` (`InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean`)
:::

括弧の中に挙げた符号化が実際に読み解けることは，定義 13.4.3 で見たとおりである．自己限定形はどこで終わるかを自分で告げるので，つないだ列を先頭から順に区切っていける．先頭にもう一つ $1$ を置いたのは，全体を一つの自然数の二進表示として読むためで，そうしないと先頭の $0$ の並びが読み落とされる．$S$ の要素を小さい順に並べたのは，同じ集合に二つの列が対応しないようにするためである．

::: definition 13.6.2 二部記述の長さ
$S \subseteq \mathbb N$ を空でない有限集合とし
$$
\ell^{2\mathrm P}(S) \;:=\; K_{\mathcal V}\big(\langle S\rangle\big) \;+\; 4\big\lceil \log_2 \lvert S\rvert \big\rceil
$$
と定め，$S$ による **二部記述の長さ** と呼ぶ（$\lceil\cdot\rceil$ は 4.4 節の天井関数である）．
:::

::: formalized
`twoPartLength` (`InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean`)
:::

$\ell^{2\mathrm P}$ は有限集合を引数にとる．第12章 定義 12.2.1 の $\ell^{\mathrm T}_n$ は系列を引数にとり添字 $n$ を持つので，二つは別の量である．第 $1$ 項が模型の記述長（定義 13.6.1），第 $2$ 項が $S$ の中での位置を書く長さにあたる．位置は $0$ 以上 $\lvert S\rvert$ 未満の自然数だから $\lceil\log_2\lvert S\rvert\rceil$ 桁の二進表示で書けるが，係数はその $4$ 倍になっている．倍率が二度かかるからで，一度目は位置と模型の記述の切れ目が読む側に分かるように位置を自己限定形にするところ，二度目は組み立てた記述を $\mathcal V$ に渡すところで，どちらも長さを $2$ 倍にする．次の定理の証明がその二段である．

::: theorem 13.6.3 二部記述の上界
定数 $c \in \mathbb N$ があって，すべての $x \in \mathbb N$ と，$x$ を含むすべての空でない有限集合 $S \subseteq \mathbb N$ について
$$
K_{\mathcal V}(x) \;\le\; \ell^{2\mathrm P}(S) + c
$$
が成り立つ．
:::

::: proof
復元する手続きを先に書き下す．$\mathcal M(z, y)$ を次のように定める（第 $2$ 引数は使わない）．$z$ の二進表示が空列なら値を持たない．そうでなければ，その二進表示から先頭の $1$ を落とした列を $u$ とし，$u$ の先頭から最初の $0$ までの $1$ の個数を $m$ とする（$u$ に $0$ が現れなければ値を持たない）．その $0$ の直後の $m$ ビットを二進表示として読んだ自然数を $i$，残りのビット列を $e$ とする（$u$ の長さが足りなければ値を持たない）．$\mathcal U(e, 0)$ を求め，その値に固定した符号化の復元を当てて自然数の有限列を得る（得られなければ値を持たない）．その列の第 $i$ 項を返す（項の個数が足りなければ値を持たない）．この対応は，有限個の場合分けと，$\mathcal U$ を走らせるところと，固定した符号化から列を復元するところからなり，どれも計算の手続きで書き下せるから，Church–Turing のテーゼより部分計算可能であり，とくに 定義 13.1.1 の意味で機械である．定理 13.1.5 をこの $\mathcal M$ に当てて定数 $b \in \mathbb N$ をとり，$c := 2b + 4$ と置く．

$x \in \mathbb N$ と，$x$ を含む空でない有限集合 $S \subseteq \mathbb N$ をとる．$S$ の要素を小さい順に並べたときの $x$ の位置を $i$ とすると $0 \le i < \lvert S\rvert$ である．命題 13.1.3 を $y := 0$ に当てて，$\lvert e\rvert = K_{\mathcal U}(\langle S\rangle)$ かつ $\mathcal U(e, 0) = \langle S\rangle$ を満たすビット列 $e$ をとる．$u$ を，$i$ の二進表示の自己限定形（定義 13.4.3）の後ろに $e$ をつないだビット列とし，$s$ を $u$ の先頭に $1$ を置いたビット列とする．先頭が $1$ だから $s$ が表す自然数の二進表示は $s$ そのものであり，$\mathcal M$ の手続きはそこから $i$ と $e$ をこの順に読み取る．よって $\mathcal M(s, 0) = x$ であり，長さは
$$
\lvert s\rvert \;=\; \big(2\lvert i\rvert + 1\big) + K_{\mathcal U}\big(\langle S\rangle\big) + 1
$$
だから，定理 13.1.5 より $K_{\mathcal U}(x) \le 2\lvert i\rvert + K_{\mathcal U}(\langle S\rangle) + b + 2$ である．

位置の桁数を抑える．$A := \lceil \log_2\lvert S\rvert\rceil$ と置くと $A \ge \log_2\lvert S\rvert$ だから $2^{A} \ge \lvert S\rvert > i$ である．$i = 0$ なら $\lvert i\rvert = 0 \le A$ である．$i \ge 1$ なら，$i$ の二進表示の桁数を $j$ として，先頭の桁が $1$ であることから $i \ge 2^{\,j-1}$ であり，$2^{\,j-1} \le i < 2^{A}$ と 補題 8.2.5 より $j \le A$ である．どちらの場合も $\lvert i\rvert \le A$ である．

$K_{\mathcal V}$ に直す．命題 13.4.6 を $x$ と $\langle S\rangle$ のそれぞれに当てると $K_{\mathcal V}(x) = 2K_{\mathcal U}(x) + 1$ と $2K_{\mathcal U}(\langle S\rangle) = K_{\mathcal V}(\langle S\rangle) - 1$ だから
$$
K_{\mathcal V}(x) \;\le\; 2\big(2\lvert i\rvert + K_{\mathcal U}(\langle S\rangle) + b + 2\big) + 1
  \;=\; 4\lvert i\rvert + K_{\mathcal V}\big(\langle S\rangle\big) + 2b + 4
$$
である．$\lvert i\rvert \le A$ と 定義 13.6.2 より右辺は $\ell^{2\mathrm P}(S) + c$ 以下である．
:::

::: formalized
`prefixComplexity_le_twoPartLength` (`InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean`)
:::

定理 13.6.3 は，どんな $S$ をとってもその二部記述より短く書けると言っている．裏を返せば，$S$ をうまく選ぶことで $K_{\mathcal V}(x)$ を下回ることはできない．$S$ を小さくすれば位置を書く桁は減るが，そのぶん $S$ 自身の記述が長くなる．逆に $S$ を大きくすれば $S$ の記述は短くなりうるが，位置を書く桁が増える．そのやりとりが，どちらに寄せても $K_{\mathcal V}(x)$ を超えられないという形で釣り合っている．

::: example 13.6.4 全体を模型にとる
$k \ge 2$ とし $S := \{0, 1, \dots, 2^k - 1\}$ とすると，どの $x \in S$ についても $K_{\mathcal V}(x) \le 2k + 3$ であり，いっぽう $\ell^{2\mathrm P}(S) \ge 4k > 2k + 3$ である．
:::

::: proof
$x \in S$ とすると $x$ は $0$ 以上 $2^k$ 未満の自然数だから，例 13.2.4 の前半より $K_{\mathcal U}(x) \le k + 1$ である．命題 13.4.6 より $K_{\mathcal V}(x) = 2K_{\mathcal U}(x) + 1 \le 2k + 3$ である．

$\lvert S\rvert = 2^k$ だから $\log_2\lvert S\rvert = k$ であり，$k$ は整数だから $\lceil\log_2\lvert S\rvert\rceil = k$ である．よって 定義 13.6.2 より $\ell^{2\mathrm P}(S) = K_{\mathcal V}(\langle S\rangle) + 4k$ であり，$K_{\mathcal V}$ は $0$ 以上だから $\ell^{2\mathrm P}(S) \ge 4k$ である．最後に $4k - (2k + 3) = 2k - 3$ であり，$k \ge 2$ より $2k - 3 \ge 1 > 0$ である．
:::

例 13.6.4 の $S$ は，$k$ ビットで書ける自然数を全部集めたものである．$S$ 自身は $k$ から作れるので $\langle S\rangle$ は短く書けるが，位置を書く桁が $k$ あり，そこに 定義 13.6.2 の係数 $4$ がかかるので，二部記述は $x$ を書き写す記述より $2k - 3$ 以上長くなる．差は $k$ とともに増えるので，定数のゆるみでは埋まらない．この模型が損をするのは，$S$ が $x$ について何も絞っていないからである．次の 命題 13.6.5 は，逆にいちばん絞った模型，すなわち一点集合をとった場合を見る．

::: proposition 13.6.5
定数 $c \in \mathbb N$ があって，すべての $x \in \mathbb N$ について $K_{\mathcal V}(\langle\{x\}\rangle) \le K_{\mathcal V}(x) + c$ が成り立つ（$\langle\cdot\rangle$ は 定義 13.6.1 のとおり）．
:::

::: proof
機械を先に作る．$\mathcal M(z, y)$ を次のように定める（第 $2$ 引数は使わない）．$z$ の二進表示が空列なら値を持たない．そうでなければ，その二進表示から先頭の $1$ を落とした列を $e$ とし，$\mathcal U(e, 0)$ を求めてその値を $w$ とし，$\langle\{w\}\rangle$ を返す．$\mathcal U$ を走らせるところと，一つの自然数からなる列に固定した符号化を当てるところは計算の手続きで書き下せるから，Church–Turing のテーゼより $\mathcal M$ は部分計算可能であり，とくに 定義 13.1.1 の意味で機械である．定理 13.1.5 をこの $\mathcal M$ に当てて定数 $b \in \mathbb N$ をとり，$c := 2b + 2$ と置く．

$x \in \mathbb N$ とする．命題 13.1.3 を $y := 0$ に当てて，$\lvert e\rvert = K_{\mathcal U}(x)$ かつ $\mathcal U(e, 0) = x$ を満たすビット列 $e$ をとり，$s$ を $e$ の先頭に $1$ を置いたビット列とする．先頭が $1$ だから $s$ が表す自然数の二進表示は $s$ そのものであり，$\mathcal M(s, 0) = \langle\{x\}\rangle$ である．よって 定理 13.1.5 より $K_{\mathcal U}(\langle\{x\}\rangle) \le \lvert s\rvert + b = K_{\mathcal U}(x) + b + 1$ である．命題 13.4.6 を $\langle\{x\}\rangle$ と $x$ のそれぞれに当てると
$$
K_{\mathcal V}\big(\langle\{x\}\rangle\big) \;=\; 2K_{\mathcal U}\big(\langle\{x\}\rangle\big) + 1
  \;\le\; 2K_{\mathcal U}(x) + 2b + 3 \;=\; K_{\mathcal V}(x) + c
$$
である．
:::

::: formalized
`modelComplexity_singleton_le` (`InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean`)
:::

## 最小記述長

::: definition 13.6.6 最小記述長
$x \in \mathbb N$ に対し
$$
\ell^{2\mathrm P*}(x) \;:=\; \min\big\{\, \ell^{2\mathrm P}(S) \;:\; S \subseteq \mathbb N \text{ は有限集合で } x \in S \,\big\}
$$
と定め，$x$ の **最小記述長** と呼ぶ．
:::

::: formalized
`mdlComplexity` (`InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean`)
:::

::: proposition 13.6.7
$x \in \mathbb N$ とすると，$x \in S$ かつ $\ell^{2\mathrm P}(S) = \ell^{2\mathrm P*}(x)$ を満たす有限集合 $S \subseteq \mathbb N$ が存在する．
:::

::: proof
一点集合 $\{x\}$ は $x$ を含む有限集合だから，定義 13.6.6 の最小をとる集合は空でない自然数の集合であり，最小元をもつ．その最小元は $\ell^{2\mathrm P*}(x)$ にほかならず，しかも $x$ を含むある有限集合 $S$ についての $\ell^{2\mathrm P}(S)$ だから，その $S$ が求めるものである．
:::

::: formalized
`mdlComplexity_spec` (`InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean`)
:::

::: theorem 13.6.8
定数 $c \in \mathbb N$ があって，すべての $x \in \mathbb N$ について
$$
\ell^{2\mathrm P*}(x) \;\le\; K_{\mathcal V}(x) + c
\qquad\text{かつ}\qquad
K_{\mathcal V}(x) \;\le\; \ell^{2\mathrm P*}(x) + c
$$
が成り立つ．
:::

::: proof
命題 13.6.5 の定数を $c_1$，定理 13.6.3 の定数を $c_2$ とし，$c$ を $c_1$ と $c_2$ の大きいほうとする．$x \in \mathbb N$ とする．

第 $1$ の不等式を示す．$\lvert\{x\}\rvert = 1$ で $\log_2 1 = 0$ だから $\lceil\log_2\lvert\{x\}\rvert\rceil = 0$ であり，定義 13.6.2 より $\ell^{2\mathrm P}(\{x\}) = K_{\mathcal V}(\langle\{x\}\rangle)$ である．一点集合 $\{x\}$ は $x$ を含む有限集合だから 定義 13.6.6 より $\ell^{2\mathrm P*}(x) \le \ell^{2\mathrm P}(\{x\})$ であり，命題 13.6.5 と合わせて $\ell^{2\mathrm P*}(x) \le K_{\mathcal V}(x) + c_1 \le K_{\mathcal V}(x) + c$ である．

第 $2$ の不等式を示す．命題 13.6.7 より $x \in S$ かつ $\ell^{2\mathrm P}(S) = \ell^{2\mathrm P*}(x)$ を満たす有限集合 $S$ がある．$x \in S$ だから $S$ は空でなく，定理 13.6.3 をこの $x$ と $S$ に当てて $K_{\mathcal V}(x) \le \ell^{2\mathrm P}(S) + c_2 = \ell^{2\mathrm P*}(x) + c_2 \le \ell^{2\mathrm P*}(x) + c$ である．
:::

::: formalized
`mdlComplexity_sub_prefixComplexity_le` (`InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean`)
:::

定理 13.6.8 は，記述を二つに分けても損も得もしないと言っている．どんな分け方をしても $K_{\mathcal V}(x)$ より短くはならず，いちばんよい分け方をとれば定数の差まで届く．したがって，二部記述に意味があるとすれば長さそのものではなく，どの $S$ がその長さを実現するかのほうである．$S$ は $x$ について言えることを集めた対象であり，位置のほうは $S$ を知ってもなお残るばらつきである．次の定義は，定数のゆるみを許して「$S$ が $x$ を説明しきっている」という条件を書く．

## コルモゴロフ十分統計量

::: definition 13.6.9 コルモゴロフ十分統計量
$c, x \in \mathbb N$ とする．有限集合 $S \subseteq \mathbb N$ が $x$ の **ゆるみ $c$ のコルモゴロフ十分統計量** であるとは，$x \in S$ かつ $\ell^{2\mathrm P}(S) \le K_{\mathcal V}(x) + c$ が成り立つことをいう．
:::

::: formalized
`IsSufficientStatistic` (`InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean`)
:::

語を一つ断っておく．第1章 1.9 節が十分と呼んだのは，確率変数 $X$ を要約する統計量 $T$ であった．本節が十分と呼ぶのは自然数を含む有限集合であって，確率変数でも統計量でもない．同じ「十分」を冠していても別の対象についての語なので，混ぜて読まないこと．読み方のほうは通じている．第1章では $T(X)$ を知れば $\theta$ について $X$ 以上のことは分からない，というのが十分の内容だった．本節では，$S$ を知ったあとに残るのは $S$ の中での位置だけで，その位置を書くのに要る長さは $S$ の記述と合わせてもゆるみ $c$ の範囲で最短に収まっている，というのが内容である．どちらも「これ以上絞れるものは残っていない」という条件である．

::: proposition 13.6.10
定数 $c \in \mathbb N$ があって，すべての $x \in \mathbb N$ について，一点集合 $\{x\}$ は $x$ のゆるみ $c$ のコルモゴロフ十分統計量である．
:::

::: proof
命題 13.6.5 の定数を $c$ とし，$x \in \mathbb N$ とする．$x \in \{x\}$ である．また $\lvert\{x\}\rvert = 1$ で $\log_2 1 = 0$ だから $\lceil\log_2\lvert\{x\}\rvert\rceil = 0$ であり，定義 13.6.2 より $\ell^{2\mathrm P}(\{x\}) = K_{\mathcal V}(\langle\{x\}\rangle)$ である．命題 13.6.5 より右辺は $K_{\mathcal V}(x) + c$ 以下だから，定義 13.6.9 の二つの条件が満たされる．
:::

::: formalized
`exists_isSufficientStatistic_singleton` (`InformationTheory/Shannon/Kolmogorov/SufficientStatistic.lean`)
:::

命題 13.6.10 は，定義 13.6.9 が単独では何も絞らないことを示している．一点集合はつねに十分統計量なのだから，十分であることに意味を持たせるには模型の大きさか記述長に別の条件を課さなければならない．一点集合は $x$ そのものを書き下しているだけで，$x$ について何かを言い当てたわけではないからである．興味があるのは，模型の記述長が $K_{\mathcal V}(x)$ よりずっと短く，しかも十分であるような $S$ のほうで，そのような $S$ は $x$ の中の規則的な部分だけを取り出したものだと読める．本書はその読みを主張にはしない．模型の記述長に上限を課したうえで位置の桁数を最小化する量については，何も述べない．

::: corollary 13.6.11
定数 $c \in \mathbb N$ があって，すべての $x \in \mathbb N$ について
$$
-\log_2 P_{\mathcal V}(x) - c \;\le\; \ell^{2\mathrm P*}(x) \;\le\; 2\big(-\log_2 P_{\mathcal V}(x)\big) + 1 + c
$$
が成り立つ．
:::

::: proof
定理 13.6.8 の定数を $c$ とし，$x \in \mathbb N$ とする．左の不等式は，定理 13.4.10 の左の不等式と 定理 13.6.8 の第 $2$ の不等式をつないで
$$
-\log_2 P_{\mathcal V}(x) \;\le\; K_{\mathcal V}(x) \;\le\; \ell^{2\mathrm P*}(x) + c
$$
とし，$c$ を移項すれば出る．右の不等式は，定理 13.6.8 の第 $1$ の不等式と 定理 13.4.10 の右の不等式をつないで
$$
\ell^{2\mathrm P*}(x) \;\le\; K_{\mathcal V}(x) + c \;\le\; 2\big(-\log_2 P_{\mathcal V}(x)\big) + 1 + c
$$
とすれば出る．
:::

::: formalization-note
系 13.6.11 に対応する単独の宣言は無い．定理 13.4.10 に紐付けた二つの宣言と 定理 13.6.8 に紐付けた宣言をつなげば得られる．三つはどれも同じ `prefixComplexity` を経由するので，つなぐときに対象を取り替える必要はない．
:::

本章が $K_{\mathcal V}$ を抑えた式を並べておく．命題 13.4.6 の $2K_{\mathcal U}(x) + 1$ は等式だから，いちばん細かい．定理 13.4.10 は $-\log_2 P_{\mathcal V}(x)$ とその $2$ 倍に $1$ を足したもので挟んだ．定理 13.6.8 は $\ell^{2\mathrm P*}(x)$ と定数の差で一致することを言う．系 13.6.11 は後の二つを直接比べたもので，最小記述長と $-\log_2$ をとった万能確率も，やはり係数 $2$ と定数のゆるみの範囲で互いを決める．三つのどれも，値を求める役には立たない．定理 13.2.3 のとおり $K_{\mathcal U}$ を求める手続きは無く，定理 13.5.1 のとおり $K_{\mathcal V}$ についても同じだからである．それでも三つが互いを定数と係数の範囲で決め合うことには意味がある．記述の短さ，でたらめなプログラムが当てる重みの大きさ，そして二つに分けた記述の短さが，同じ一つのことを測っているからである．

本章の出発点は，一本の系列の単純さを分布によらずに測ることだった．13.1 節から 13.3 節は素朴な記述長でそれを測り，1 文字あたりの平均がエントロピーに一致することを見た．13.4 節から本節までは機械を語頭のない形に取り替え，記述長が重みとも二部記述とも定数倍の範囲で同じものを測ることを見た．いっぽう，どの量も値を求める手続きを持たない．測り方が定まっているのに測れない，というのが本章の残す形である．
