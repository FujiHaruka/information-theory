# 13.3 複雑性とエントロピー

13.2 節までの $K_{\mathcal U}$ は一つの自然数についての量で，分布はどこにも現れなかった．いっぽう第2章から第12章までに得た圧縮の限界は，どれも分布から作ったエントロピーで書かれている．二つは測っている相手が違うので，並べただけでは比べられない．本節は，分布 $p$ の情報源が出した長さ $n$ のブロックに $K_{\mathcal U}$ を当て，その平均を $1$ 文字あたりに直したものが $H(p)$ に近づくことを示す．分布についての量と，一本の系列についての量が，そこで同じ値を指す．

そのためにまず，ブロックに自然数の番号を与えなければならない．$K_{\mathcal U}$ は 定義 13.1.2 のとおり自然数についての量なので，$\mathcal X^n$ の元をそのまま渡せないからである．番号づけを置いたあと，上からの評価を第12章の型による二段符号から，下からの評価を 定理 13.2.1 の数え上げと第2章の典型集合から作り，二つを挟み撃ちにする．最後に，個々のブロックについて何が言えるかを見る．

以下，$\mathcal X$ を空でない有限アルファベット，$p$ を $\mathcal X$ 上の全点で正の分布とし，定義 2.1.1 の設定で $X_0, X_1, \dots$ を分布 $p$ の i.i.d. 情報源，$X^n := (X_0, \dots, X_{n-1})$ と書く．$p$ の $n$ 重の積分布は $p^n$ と書く（第11章と同じ肩の書き方で，$p^n(\{x\}) := \prod_{i=0}^{n-1}p(x_i)$ である）．エントロピー $H$（定義 1.1.1）は，第12章と同じく分布に対して書く．すなわち $H(p)$ は $X_0$ のエントロピーであり，単位は 13.1 節で断ったとおりビットである．

## ブロックに番号をつける

::: definition 13.3.1 ブロックの番号
$\mathcal X$ を空でない有限アルファベットとし，$\mathcal X$ の文字に $0, 1, \dots, \lvert\mathcal X\rvert - 1$ の番号を一つずつ与えて固定して，文字 $a$ に与えた番号を $c(a)$ と書く（$c$ は $\mathcal X$ から $\{0, 1, \dots, \lvert\mathcal X\rvert - 1\}$ への全単射である）．$n \ge 1$ と $x = (x_0, \dots, x_{n-1}) \in \mathcal X^n$ に対し
$$
\langle x\rangle \;:=\; \sum_{i=0}^{n-1} c(x_i)\,\lvert\mathcal X\rvert^{\,i}
$$
と定める．
:::

第10章は内積を，二つの引数をとる $\langle\,\cdot\,,\,\cdot\,\rangle$ と書いたが，本章の $\langle\cdot\rangle$ はつねに引数を一つとり，有限の対象を自然数に写す符号化を表す．$\langle x\rangle$ は，$x$ の第 $i$ 文字の番号を第 $i$ 桁とする $\lvert\mathcal X\rvert$ 進の数にほかならない．たとえば $\mathcal X = \{0, 1\}$ に $c(0) = 0$，$c(1) = 1$ と番号を与えれば，$\langle x\rangle$ は $x$ を下の桁から読んだ二進の数である．番号づけを一つ固定したのは，$\langle x\rangle$ の値が $\mathcal X$ の文字の並べ方に依るからで，以下では固定した $c$ についての値をいう．

::: formalized
`encodeBlock` (`InformationTheory/Shannon/Kolmogorov/EntropyRate.lean`)
:::

::: proposition 13.3.2
$\mathcal X$ を空でない有限アルファベット，$n \ge 1$ とし，$\langle\cdot\rangle$ を 定義 13.3.1 のとおりとする．このとき $x \mapsto \langle x\rangle$ は $\mathcal X^n$ の上で単射であり，どの $x \in \mathcal X^n$ についても $\langle x\rangle < \lvert\mathcal X\rvert^{\,n}$ である．
:::

::: proof
上界から示す．どの文字 $a$ についても $c(a) \le \lvert\mathcal X\rvert - 1$ だから，各項を $\big(\lvert\mathcal X\rvert-1\big)\lvert\mathcal X\rvert^{\,i} = \lvert\mathcal X\rvert^{\,i+1} - \lvert\mathcal X\rvert^{\,i}$ で抑えて足すと隣り合う項が打ち消し合い
$$
\langle x\rangle \;\le\; \sum_{i=0}^{n-1}\big(\lvert\mathcal X\rvert^{\,i+1} - \lvert\mathcal X\rvert^{\,i}\big) \;=\; \lvert\mathcal X\rvert^{\,n} - 1
$$
となる．

単射性は $n$ についての帰納法で示す．$n = 1$ のときは $\langle x\rangle = c(x_0)$ で，$c$ が単射だから $\langle x\rangle$ から $x_0$ が定まる．$n$ で成り立つとして $n + 1$ の場合を見る．$x = (x_0, \dots, x_n) \in \mathcal X^{n+1}$ に対し $x^- := (x_1, \dots, x_n) \in \mathcal X^n$ と置くと，定義 13.3.1 の和から第 $0$ 項を外して $\lvert\mathcal X\rvert$ でくくり
$$
\langle x\rangle \;=\; c(x_0) \;+\; \lvert\mathcal X\rvert\,\langle x^-\rangle
$$
である．いま $\langle x\rangle = \langle x'\rangle$ とすると，$c(x_0)$ と $c(x'_0)$ はどちらも $\lvert\mathcal X\rvert$ 未満の自然数で，$\lvert\mathcal X\rvert$ で割った余りが等しいから $c(x_0) = c(x'_0)$ であり，$c$ が単射だから $x_0 = x'_0$ である．残りを引いて $\lvert\mathcal X\rvert \ge 1$ で割ると $\langle x^-\rangle = \langle x'^-\rangle$ となり，帰納法の仮定から $x^- = x'^-$ である．
:::

::: formalized
単射性 `encodeBlock_injective`，上界 `encodeBlock_lt` (`InformationTheory/Shannon/Kolmogorov/EntropyRate.lean`)
:::

命題 13.3.2 の上界は，番号づけが場所を無駄にしていないことを言っている．長さ $n$ のブロックは $\lvert\mathcal X\rvert^{\,n}$ 個あり，それがちょうど $0$ 以上 $\lvert\mathcal X\rvert^{\,n}$ 未満の自然数に重なりなく収まっている．したがって $\langle x\rangle$ の二進表示の長さは $n\log_2\lvert\mathcal X\rvert$ あまりで，ブロックをそのまま書き写すのに要る長さと変わらない．番号づけそのものは何も圧縮していないということで，圧縮は次の 命題 13.3.3 から始まる．

## 型による記述

第12章 定義 12.2.1 は，系列を「まず型を送り，次に型類の中の位置を送る」二段の形で書いたときの長さを $\ell^{\mathrm T}_n$ と置いた．この長さは分布を持ち出さずに系列だけから決まるので，そのまま機械への指示に写せる．写した先で 定理 13.1.5 を当てれば，$K_{\mathcal U}$ の上界が定数の払いで手に入る．記号を一つ引いておく．実数 $t$ に対する天井関数 $\lceil t \rceil$，すなわち $t$ 以上の最小の整数と，その性質 $t \le \lceil t \rceil < t + 1$ は，第4章 4.4 節で既知としたとおりに本節でも使う．

::: proposition 13.3.3 型による記述の上界
$\mathcal X$ を空でない有限アルファベットとし，$\langle\cdot\rangle$ を 定義 13.3.1，$\ell^{\mathrm T}_n$ を 定義 12.2.1 の型による二段符号の符号長とする．このとき定数 $b \in \mathbb N$ があって，すべての $n \ge 1$ とすべての $x \in \mathcal X^n$ について
$$
K_{\mathcal U}\big(\langle x\rangle \,\big\vert\, n\big) \;\le\; \ell^{\mathrm T}_n(x) + b
$$
が成り立つ．
:::

::: proof
$n \ge 1$ と $x \in \mathcal X^n$ から，長さ $\ell^{\mathrm T}_n(x) + 1$ のビット列を組み立てる．$A_n := \big\lceil\lvert\mathcal X\rvert\log_2(n+1)\big\rceil$ と置く（定義 12.2.1 の第 $1$ 項である）．

型を書く桁を作る．各文字 $a \in \mathcal X$ について $N(a\mid x)$（定義 2.4.1）は $0$ 以上 $n$ 以下の整数だから，$N(a\mid x)$ を第 $c(a)$ 桁とする $(n+1)$ 進の数
$$
u \;:=\; \sum_{a \in \mathcal X} N(a\mid x)\,(n+1)^{c(a)}
$$
を作ると，命題 13.3.2 の上界と同じ打ち消しにより $u \le (n+1)^{\lvert\mathcal X\rvert} - 1$ である．いっぽう $A_n \ge \lvert\mathcal X\rvert\log_2(n+1) = \log_2\big((n+1)^{\lvert\mathcal X\rvert}\big)$ だから $2^{A_n} \ge (n+1)^{\lvert\mathcal X\rvert}$ であり，$u$ は $A_n$ 桁の二進表示で書ける（桁が足りなければ先頭を $0$ で埋める）．

型類の中の位置を書く桁を作る．$x$ の型を $\hat P_x$，その型類を $\mathcal T_n(\hat P_x)$（どちらも 定義 11.1.1）と書くと $x \in \mathcal T_n(\hat P_x)$ である．命題 13.3.2 より $\langle\cdot\rangle$ は $\mathcal X^n$ の上で単射だから，$\mathcal T_n(\hat P_x)$ の元を $\langle\cdot\rangle$ の値の小さい順に一列に並べられる．その並びでの $x$ の位置を $i$ とすると $0 \le i < \lvert\mathcal T_n(\hat P_x)\rvert$ であり，$B := \big\lceil\log_2\lvert\mathcal T_n(\hat P_x)\rvert\big\rceil$ と置くと $2^B \ge \lvert\mathcal T_n(\hat P_x)\rvert$ だから，$i$ は $B$ 桁の二進表示で書ける．

二つをつなぐ．$d$ を，$u$ の $A_n$ 桁と $i$ の $B$ 桁をこの順に並べた長さ $A_n + B = \ell^{\mathrm T}_n(x)$ のビット列とし，$s$ を $d$ の先頭に $1$ を置いた長さ $\ell^{\mathrm T}_n(x) + 1$ のビット列とする．先頭が $1$ だから，$s$ が表す自然数の二進表示は $s$ そのものであり，$s$ から $d$ が読み取れる．

復元する手続きを書き下す．$\mathcal M(z, y)$ を，$z \ge 1$ かつ $y \ge 1$ のとき次のように定め，そのほかでは値を持たないとする．$z$ の二進表示から先頭の $1$ を落とした列を $d$ とし，$A_y$ を上と同じ式で計算して，$d$ の先頭 $A_y$ 桁を二進表示として読んだ自然数を $u$ とする．$u$ を $(y+1)$ 進の数として桁に分け（桁が $\lvert\mathcal X\rvert$ 個に足りなければ上の桁を $0$ とし，$\lvert\mathcal X\rvert$ 個を超えるなら値を持たない），第 $c(a)$ 桁を文字 $a$ の個数と読む．個数の総和が $y$ でなければ値を持たない．総和が $y$ なら，$a \mapsto (\text{$a$ の個数})/y$ は長さ $y$ の型（定義 11.1.1）だから，その型類の元を $\langle\cdot\rangle$ の値の小さい順に並べ，$d$ の残りの桁が表す自然数がその要素数より小さければ，その位置にある $x' \in \mathcal X^y$ をとって $\langle x'\rangle$ を返し，小さくなければ値を持たない．この対応は有限個の場合分けと有限回の繰り返しで書き下せているから，Church–Turing のテーゼより部分計算可能であり，定義 13.1.1 の意味で機械である．

作り方から $\mathcal M(s, n) = \langle x\rangle$ である．定理 13.1.5 をこの $\mathcal M$ に当てて定数 $b_0 \in \mathbb N$ をとると
$$
K_{\mathcal U}\big(\langle x\rangle \,\big\vert\, n\big) \;\le\; \lvert s\rvert + b_0 \;=\; \ell^{\mathrm T}_n(x) + 1 + b_0
$$
である．$b_0$ は $\mathcal M$ だけで決まり，$\mathcal M$ は $n$ にも $x$ にも依らないから，$b := b_0 + 1$ と置けば主張を得る．
:::

::: formalization-note
命題 13.3.3 に対応する，一般のアルファベットについての単独の宣言は無い．二値の場合については，型を書く長さ $2\log_2(n+1)$ と型のエントロピーを $n$ 倍したものを直に足した形の上界が `condComplexity_bool_block_le` (`InformationTheory/Shannon/Kolmogorov/Incompressible.lean`) にある．一般のアルファベットについては，同じ上界を強典型集合（定義 2.4.1）の上に限った形の `condComplexity_block_typical_le` (`InformationTheory/Shannon/Kolmogorov/EntropyRate.lean`) があり，そちらには典型性の幅と，長さに比例する余裕が入っている．
:::

条件に $n$ を置いたことに注意したい．この記述は，長さ $n$ を知っている相手に向けて書かれている．長さを知らなければ，型の桁がどこで終わるかも，型類をどう並べるかも決まらないからである．$n$ を書き添える手もあるが，本節は $n$ を条件として渡す形をとり，条件を外した $K_{\mathcal U}(\langle x\rangle)$ については何も述べない．

## 平均は両側からエントロピーに寄る

長さ $n$ のブロックは有限個で，命題 13.1.4 よりどの $K_{\mathcal U}(\langle x\rangle \mid n)$ も有限だから，$K_{\mathcal U}(\langle X^n\rangle \mid n)$ の平均
$$
\mathbb E\big[K_{\mathcal U}\big(\langle X^n\rangle \,\big\vert\, n\big)\big]
  \;=\; \sum_{x \in \mathcal X^n} p^n(\{x\})\,K_{\mathcal U}\big(\langle x\rangle \,\big\vert\, n\big)
$$
は有限個の項の和である．これを $n$ で割った量が本節の主役で，上からは 命題 13.3.3 と第12章が，下からは 定理 13.2.1 と第2章が抑える．

::: lemma 13.3.4
$\mathcal X$ を空でない有限アルファベット，$p$ を $\mathcal X$ 上の全点で正の分布とし，定義 2.1.1 の設定で $X_0, X_1, \dots$ を分布 $p$ の i.i.d. 情報源，$X^n := (X_0, \dots, X_{n-1})$ とする．$\langle\cdot\rangle$ を 定義 13.3.1，$b$ を 命題 13.3.3 の定数とすると，すべての $n \ge 1$ について
$$
\frac1n\,\mathbb E\big[K_{\mathcal U}\big(\langle X^n\rangle \,\big\vert\, n\big)\big]
  \;\le\; H(p) \;+\; \frac{\lvert\mathcal X\rvert\log_2(n+1) + 2 + b}{n}
$$
である（$H$ は 定義 1.1.1 のエントロピー）．
:::

::: proof
第12章の族の設定を，一つの分布に潰して使う．$\Theta$ を $1$ 点集合 $\{\theta_0\}$ とし，$P_{\theta_0} := p$ と置くと，$\Theta$ は空でない有限集合で $P_{\theta_0}$ は全点で正だから，これは 定義 12.1.1 の情報源の族である．$p$ が全点で正であることは 定義 12.1.1 が族に課す条件であり，本補題の仮定でもある．積分布は $P^n_{\theta_0} = p^n$ である．

$n \ge 1$ とする．定理 12.2.4 をこの族の $\theta_0$ に当てると，定義 12.1.2 より
$$
\frac1n\Big(\sum_{x \in \mathcal X^n} p^n(\{x\})\,\ell^{\mathrm T}_n(x) \;-\; H\big(p^n\big)\Big)
  \;\le\; \frac{\lvert\mathcal X\rvert\log_2(n+1) + 2}{n}
$$
である．$p^n$ は分布 $p$ の i.i.d. 情報源の長さ $n$ のブロックの分布だから，補題 2.3.3 より $H(p^n) = n\,H(p)$ である．これを移項して
$$
\frac1n\sum_{x \in \mathcal X^n} p^n(\{x\})\,\ell^{\mathrm T}_n(x)
  \;\le\; H(p) \;+\; \frac{\lvert\mathcal X\rvert\log_2(n+1) + 2}{n}
$$
を得る．

命題 13.3.3 の不等式に $p^n(\{x\})$ を掛けて $x$ について足す．重みは非負で総和が $1$ だから
$$
\mathbb E\big[K_{\mathcal U}\big(\langle X^n\rangle \,\big\vert\, n\big)\big]
  \;\le\; \sum_{x \in \mathcal X^n} p^n(\{x\})\,\ell^{\mathrm T}_n(x) \;+\; b
$$
である．両辺を $n$ で割り，上の評価を入れると主張を得る．
:::

::: formalization-note
補題 13.3.4 の形の宣言は無い．形式化が持つのは，任意の $\varepsilon > 0$ について十分大きい $n$ で平均が $H(p) + \varepsilon$ 以下になるという形の `kolmogorov_entropy_rate_upper` (`InformationTheory/Shannon/Kolmogorov/EntropyRate.lean`) で，本文が書いた $n$ についての明示的な速さは含んでいない．
:::

下からの評価に移る．上からの評価が符号を一つ作って見せたのに対し，下からの評価は符号を作らない．短い記述は本数が限られているという 定理 13.2.1 の数え上げと，実際に現れるブロックはどれも確率が $2^{-nH}$ の近くにあるという 定理 2.2.4 を，そのまま突き合わせる．

::: lemma 13.3.5
$\mathcal X$ を空でない有限アルファベット，$p$ を $\mathcal X$ 上の全点で正の分布とし，定義 2.1.1 の設定で $X_0, X_1, \dots$ を分布 $p$ の i.i.d. 情報源，$X^n := (X_0, \dots, X_{n-1})$ とする．$\langle\cdot\rangle$ を 定義 13.3.1 とすると，任意の $\varepsilon > 0$ について，$n$ が十分大きければ
$$
\frac1n\,\mathbb E\big[K_{\mathcal U}\big(\langle X^n\rangle \,\big\vert\, n\big)\big] \;\ge\; H(p) - \varepsilon
$$
である（$H$ は 定義 1.1.1 のエントロピー）．
:::

::: proof
$\varepsilon > 0$ とする．$H(p) \le \varepsilon$ のときは，$K_{\mathcal U}$ が $0$ 以上だから左辺が $0$ 以上で，右辺は $0$ 以下であり，主張は成り立つ．以下 $H(p) > \varepsilon$ とする．

評価に使う三つの数をここで選ぶ．$\varepsilon_1 := \varepsilon/3$ と置くと $0 < \varepsilon_1 < H(p)$ である．自然数 $m$ を $2^{-m}\,H(p) \le \varepsilon/6$ を満たすようにとる．そして $n \ge 1$ に対し，$k + m \le n\big(H(p) - \varepsilon_1\big)$ を満たす自然数 $k$ の全体を考える．$n(H(p)-\varepsilon_1) \to \infty$ だから，$n$ が十分大きければ $k = 0$ がこれを満たしてこの集合は空でなく，しかも $n(H(p)-\varepsilon_1)$ が上界だから，最大の元をもつ．それを $k_n$ と書く．以下そのような $n$ だけを見る．とり方から
$$
k_n + m \;\le\; n\big(H(p) - \varepsilon_1\big) \;<\; k_n + 1 + m
$$
である（右側は $k_n + 1$ が上の集合に入らないことによる）．

典型集合の上で，記述の短いブロックの確率を抑える．$T^{(n)}_{\varepsilon_1}$ を 定義 2.2.1 の典型集合とする．命題 13.3.2 より $x \mapsto \langle x\rangle$ は $\mathcal X^n$ の上で単射だから，$K_{\mathcal U}(\langle x\rangle \mid n) < k_n$ を満たす $x \in \mathcal X^n$ の個数は，$K_{\mathcal U}(z \mid n) < k_n$ を満たす自然数 $z$ の個数以下であり，定理 13.2.1 より $2^{k_n}$ より小さい．いっぽう $x \in T^{(n)}_{\varepsilon_1}$ なら 定理 2.2.4 より $p^n(\{x\}) \le 2^{-n(H(p)-\varepsilon_1)}$ である．二つを掛け合わせ，$k_n \le n(H(p)-\varepsilon_1) - m$ を使うと
$$
\Pr\Big[X^n \in T^{(n)}_{\varepsilon_1} \ \text{かつ}\ K_{\mathcal U}\big(\langle X^n\rangle \,\big\vert\, n\big) < k_n\Big]
  \;\le\; 2^{k_n}\,2^{-n(H(p)-\varepsilon_1)} \;\le\; 2^{-m}
$$
である．

記述が短くない確率を下から抑える．事象 $\{K_{\mathcal U}(\langle X^n\rangle \mid n) < k_n\}$ は，$X^n$ が典型集合に入らない場合と，入ったうえで記述が短い場合に分かれるから
$$
\Pr\Big[K_{\mathcal U}\big(\langle X^n\rangle \,\big\vert\, n\big) \ge k_n\Big]
  \;\ge\; \Pr\Big[X^n \in T^{(n)}_{\varepsilon_1}\Big] \;-\; 2^{-m}
$$
である．定理 2.2.3 より $\Pr[X^n \in T^{(n)}_{\varepsilon_1}] \to 1$ だから，$n$ が十分大きければ $\big(1 - \Pr[X^n \in T^{(n)}_{\varepsilon_1}]\big)H(p) \le \varepsilon/6$ にできる．

平均を下から抑える．$K_{\mathcal U}$ は $0$ 以上で $k_n$ も $0$ 以上だから，$K_{\mathcal U}(\langle X^n\rangle \mid n) < k_n$ の側の項を落として
$$
\mathbb E\big[K_{\mathcal U}\big(\langle X^n\rangle \,\big\vert\, n\big)\big]
  \;\ge\; k_n\,\Pr\Big[K_{\mathcal U}\big(\langle X^n\rangle \,\big\vert\, n\big) \ge k_n\Big]
$$
である．$k_n/n \le H(p) - \varepsilon_1 < H(p)$ だから，右辺を $n$ で割った値は
$$
\frac{k_n}{n}\;-\;\frac{k_n}{n}\Big(1 - \Pr\Big[K_{\mathcal U}\big(\langle X^n\rangle \,\big\vert\, n\big) \ge k_n\Big]\Big)
  \;\ge\; \frac{k_n}{n} \;-\; H(p)\Big(\big(1 - \Pr\big[X^n \in T^{(n)}_{\varepsilon_1}\big]\big) + 2^{-m}\Big)
$$
以上である．いま $m$ のとり方と直前の段から，右端の括弧に $H(p)$ を掛けたものは $\varepsilon/3$ 以下である．また $k_n$ のとり方の右側の不等式より $k_n/n > H(p) - \varepsilon_1 - (1+m)/n$ だから，$n$ を $(1+m)/n \le \varepsilon/3$ となるまで大きくとれば，全体は $H(p) - \varepsilon_1 - \varepsilon/3 - \varepsilon/3 = H(p) - \varepsilon$ 以上である．
:::

::: formalized
`kolmogorov_entropy_rate_lower` (`InformationTheory/Shannon/Kolmogorov/EntropyRate.lean`)
:::

::: theorem 13.3.6 複雑性とエントロピー
$\mathcal X$ を空でない有限アルファベット，$p$ を $\mathcal X$ 上の全点で正の分布とし，定義 2.1.1 の設定で $X_0, X_1, \dots$ を分布 $p$ の i.i.d. 情報源，$X^n := (X_0, \dots, X_{n-1})$ とする．$\langle\cdot\rangle$ を 定義 13.3.1 とすると
$$
\frac1n\,\mathbb E\big[K_{\mathcal U}\big(\langle X^n\rangle \,\big\vert\, n\big)\big] \;\longrightarrow\; H(p)
\qquad (n \to \infty)
$$
である（$H$ は 定義 1.1.1 のエントロピー）．
:::

::: proof
$\varepsilon > 0$ とする．補題 13.3.5 より，$n$ が十分大きければ左辺は $H(p) - \varepsilon$ 以上である．

上からは 補題 13.3.4 が $H(p) + \big(\lvert\mathcal X\rvert\log_2(n+1) + 2 + b\big)/n$ を与える．この第 $2$ 項は $0$ に収束する．本章の底で読むと 補題 11.2.2 より $\log_2(n+1)/n \to 0$ であり，$\lvert\mathcal X\rvert$ は $n$ に依らない有限の数だからその $\lvert\mathcal X\rvert$ 倍も $0$ に収束し，$(2+b)/n$ も $0$ に収束するからである．よって $n$ が十分大きければ左辺は $H(p) + \varepsilon$ 以下である．

二つの「十分大きい」の大きいほうをとれば，それ以上の $n$ について左辺と $H(p)$ の差は $\varepsilon$ より大きくならない．
:::

::: formalized
`kolmogorov_entropy_rate` (`InformationTheory/Shannon/Kolmogorov/EntropyRate.lean`)
:::

::: formalization-note
形式化の上半は，強典型集合（定義 2.4.1）の上と外に平均を分け，それぞれを別の上界で抑えて組み立てており，本文が引く 定理 12.2.4 は使っていない．下半は本文と同じく，記述の短い対象の数え上げと典型集合（定義 2.2.1）による．保証しているのは定理の正しさであって，紙の証明手順の一致ではない．
:::

定理 13.3.6 が，本節のはじめに述べた二つの量を結んでいる．左辺は，情報源が実際に出した一本のブロックを，分布を知らない機械に書き出させる長さの平均である．右辺は，分布だけから決まる量である．第2章の情報源符号化定理も同じ値を両側から挟んだが，あちらの符号は分布 $p$ を知って作られていた．こちらの $K_{\mathcal U}$ は分布を一度も見ていない．それでも $1$ 文字あたりの長さは同じところへ行く．

::: example 13.3.7 公平なコイン
$\mathcal X = \{0, 1\}$，$p(0) = p(1) = 1/2$ とし，$b$ を 命題 13.3.3 の定数とする．このとき $H(p) = 1$ ビットであり，$n = 1000$ に対する 補題 13.3.4 の右辺は $1.0219344\ldots + b/1000$ ビットである．
:::

::: proof
定義 1.1.1 より $H(p) = -2 \times \tfrac12\log_2\tfrac12 = 1$ である．$\lvert\mathcal X\rvert = 2$ だから，補題 13.3.4 の右辺は $1 + \big(2\log_2 1001 + 2 + b\big)/1000$ である．$\log_2 1001 = 9.9672262\ldots$（第12章 例 12.2.7 と同じ値である）だから $\big(2 \times 9.9672262\ldots + 2\big)/1000 = 0.0219344\ldots$ であり，右辺は $1.0219344\ldots + b/1000$ である．
:::

例 13.3.7 の上界は，$b$ を決めるまで数として読めない．$b$ は 命題 13.3.3 の証明のとおり 定理 13.1.5 の定数から来ており，13.1 節で見たとおりその値は部分計算可能関数の番号づけの取り方に依るからである．第12章 例 12.2.7 が同じ $\lvert\mathcal X\rvert = 2$ と $n = 1000$ について与えた $0.0219\ldots$ ビットは，番号づけを持ち出さずに書けた数だった．機械を一つ固定して一本の系列を測るようにした代償が，この定数として残っている．いっぽう 補題 13.3.5 と 定理 13.3.6 には $b$ が現れない．下からの評価は機械を作らずに数え上げだけで出ており，極限のほうは $b$ を $n$ で割って消してしまうからである．

## 圧縮できないブロック

定理 13.3.6 は平均についての主張で，一本一本のブロックについては何も言っていない．そこで，個々のブロックのうち，これ以上短く書けないものを取り出して調べる．アルファベットは $\{0, 1\}$ にとり，番号は $c(0) = 0$，$c(1) = 1$ と与えて固定する．

::: definition 13.3.8 圧縮できないブロック
$n \ge 1$ とする．$x \in \{0,1\}^n$ が **圧縮できない** とは
$$
K_{\mathcal U}\big(\langle x\rangle \,\big\vert\, n\big) \;\ge\; n
$$
が成り立つことをいう（$\langle\cdot\rangle$ は 定義 13.3.1 を $\mathcal X = \{0,1\}$ に当てたものである）．
:::

13.2 節は「$k$ ビット未満では書き出せない」ことを指して同じ言葉を地の文で使ったが，ここで名前を与えるのは，長さ $n$ のブロックについて $k$ を $n$ ととった場合である．この条件は長さ $n$ のブロック一つについてのもので，長さを伸ばしながら同じ条件を課しても，無限に続く列そのものについての性質を定めたことにはならない．本書は無限列についての同種の概念を扱わない．

::: proposition 13.3.9
各 $n \ge 1$ に $x^{(n)} \in \{0,1\}^n$ を対応させて，どの $n \ge 1$ についても $x^{(n)}$ が 定義 13.3.8 の意味で圧縮できないようにできる．
:::

::: proof
$n \ge 1$ を固定する．定理 13.2.1 を $y := n$，$k := n$ に当てると，$K_{\mathcal U}(z \mid n) < n$ を満たす自然数 $z$ は $2^n$ 個より少ない．いっぽう $\{0,1\}^n$ の要素数は $2^n$ であり，命題 13.3.2 より $x \mapsto \langle x\rangle$ はその上で単射だから，$\{\langle x\rangle : x \in \{0,1\}^n\}$ は $2^n$ 個の相異なる自然数からなる．したがってそのすべてが $K_{\mathcal U}(\langle x\rangle \mid n) < n$ を満たすことはなく，圧縮できない $x \in \{0,1\}^n$ が少なくとも一つある．各 $n \ge 1$ についてそのようなものを一つ選んで $x^{(n)}$ とすればよい．
:::

::: formalized
`exists_incompressible_bool_seq` (`InformationTheory/Shannon/Kolmogorov/Incompressible.lean`)
:::

圧縮できないブロックがあることは分かった．では，そのようなブロックはどんな見た目をしているだろうか．手がかりは 命題 13.3.3 にある．型による記述の長さは型類の要素数で決まり，型類は $0$ と $1$ の個数が偏るほど小さくなる．したがって個数の偏ったブロックには短い記述があり，圧縮できないブロックにはその短さが無いのだから，個数は偏っていないことになる．次の定理はこの筋を不等式にしたものである．

::: theorem 13.3.10 圧縮できないブロックの $1$ の頻度
$\delta > 0$ とする．$n$ が十分大きければ，定義 13.3.8 の意味で圧縮できないどの $x \in \{0,1\}^n$ についても
$$
\Big\lvert\, \frac{N(1\mid x)}{n} - \frac12 \,\Big\rvert \;<\; \delta
$$
である（$N(1\mid x)$ は 定義 2.4.1 の，$x$ に含まれる $1$ の個数）．
:::

::: proof
$N(1\mid x)/n$ は $0$ 以上 $1$ 以下だから，$\delta > 1/2$ のときは左辺が $1/2$ 以下で主張が成り立つ．以下 $0 < \delta \le 1/2$ とする．

型による上界を二値に当てる．$\mathcal X := \{0,1\}$ とし，$b$ を 命題 13.3.3 の定数とする．$n \ge 1$ と $x \in \{0,1\}^n$ をとり，$r := N(1\mid x)/n$ と置く．天井関数の性質 $\lceil t\rceil < t + 1$（4.4 節）を 定義 12.2.1 の二つの項に当てると
$$
\ell^{\mathrm T}_n(x) \;<\; 2\log_2(n+1) + 2 + \log_2\big\lvert\mathcal T_n\big(\hat P_x\big)\big\rvert
$$
である．

型類の要素数を本章の底で読む．第11章は $\log$ の底を自然対数にとっているので，定理 11.1.8 の上界はそこで測ったエントロピーを $\mathrm e$ の肩に乗せた形をしている．自然対数で測ったエントロピーは本章の底で測った $H$ の $\log_{\mathrm e}2$ 倍だから
$$
\mathrm e^{\,n\,H(P)\log_{\mathrm e}2} \;=\; 2^{\,n H(P)}
$$
であり，本章の底では 定理 11.1.8 の上界は $\lvert\mathcal T_n(P)\rvert \le 2^{\,nH(P)}$ と読める（第12章 定理 12.2.4 の証明が置いた読み替えと同じである）．$P := \hat P_x$ ととって両辺の $\log_2$ をとると $\log_2\lvert\mathcal T_n(\hat P_x)\rvert \le n\,H(\hat P_x)$ である．また 定義 11.1.1 より $\hat P_x(1) = r$，$\hat P_x(0) = 1 - r$ だから，例 1.1.2 より $H(\hat P_x) = H_b(r)$ である．

圧縮できないことを不等式にする．$x$ が圧縮できないとすると，定義 13.3.8 と 命題 13.3.3 と上の二つから
$$
n \;\le\; K_{\mathcal U}\big(\langle x\rangle \,\big\vert\, n\big) \;\le\; \ell^{\mathrm T}_n(x) + b
  \;<\; 2\log_2(n+1) + 2 + b + n\,H_b(r)
$$
であり，$n$ で割って移項すると
$$
1 - H_b(r) \;<\; \frac{2\log_2(n+1) + 2 + b}{n}
$$
を得る．

頻度が $1/2$ から離れていると左辺が正の定数以上になることを見る．$\lvert r - 1/2\rvert \ge \delta$ とする．補題 9.3.1 の第 $1$ の主張（二値エントロピー関数の対称性）より $H_b(r) = H_b(1-r)$ だから，$r$ を $1-r$ に取り替えて $r \le 1/2 - \delta$ としてよい．すると $0 \le r \le 1/2 - \delta \le 1/2$ だから，補題 9.3.1 の第 $3$ の主張（区間 $[0,1/2]$ での単調性）より $H_b(r) \le H_b(1/2 - \delta)$ である．いっぽう 定理 1.1.5 を $M = 2$ に当てると $H_b(1/2-\delta) \le \log_2 2 = 1$ で，等号は分布が一様のとき，すなわち $1/2 - \delta = 1/2$ のときに限るが，$\delta > 0$ だからそうではない．よって $1 - H_b(1/2-\delta) > 0$ である．

二つを突き合わせる．いま見たとおり，圧縮できない $x$ が $\lvert r - 1/2\rvert \ge \delta$ を満たすなら
$$
0 \;<\; 1 - H_b\big(\tfrac12 - \delta\big) \;\le\; 1 - H_b(r) \;<\; \frac{2\log_2(n+1) + 2 + b}{n}
$$
である．右辺は，本章の底で読んだ 補題 11.2.2 より $n \to \infty$ で $0$ に収束するから，$n$ を十分大きくとれば $1 - H_b(1/2-\delta)$ 以下になる．そのような $n$ については上の不等式が成り立ちようがないので，圧縮できないどの $x$ も $\lvert r - 1/2\rvert < \delta$ を満たす．
:::

::: formalized
`incompressible_freq_near_half` (`InformationTheory/Shannon/Kolmogorov/Incompressible.lean`)
:::

::: corollary 13.3.11
各 $n \ge 1$ に $x^{(n)} \in \{0,1\}^n$ を一つずつ与え，$n$ が十分大きいところでは $x^{(n)}$ が 定義 13.3.8 の意味で圧縮できないとする．このとき
$$
\frac{N\big(1 \,\big\vert\, x^{(n)}\big)}{n} \;\longrightarrow\; \frac12 \qquad (n \to \infty)
$$
である（$N(1\mid\cdot)$ は 定義 2.4.1 の，系列に含まれる $1$ の個数）．
:::

::: proof
$\varepsilon > 0$ とする．定理 13.3.10 を $\delta := \varepsilon$ に当てると，$n$ が十分大きければ，圧縮できないどの $x \in \{0,1\}^n$ についても $\lvert N(1\mid x)/n - 1/2\rvert < \varepsilon$ である．仮定より $n$ が十分大きいところで $x^{(n)}$ は圧縮できないから，二つの「十分大きい」の大きいほうをとれば，それ以上の $n$ について $\lvert N(1\mid x^{(n)})/n - 1/2\rvert < \varepsilon$ である．
:::

::: formalized
`incompressible_seq_freq_tendsto_half` (`InformationTheory/Shannon/Kolmogorov/Incompressible.lean`)
:::

定理 13.3.10 の証明が $n$ に要求しているのは，$\big(2\log_2(n+1) + 2 + b\big)/n$ が $1 - H_b(1/2-\delta)$ 以下になることだけである．この量は $n$ とともに $0$ へ向かうが，向かい方は $\log_2 n$ を $n$ で割った速さでしかないので，$\delta$ を小さくとると要求が満たされる $n$ はすぐに大きくなる．数で見ておく．

::: example 13.3.12 頻度が効きはじめる規模
$\delta = 1/10$ とし，$b$ を 命題 13.3.3 の定数とする．定理 13.3.10 の証明が $n$ に要求する不等式
$$
\frac{2\log_2(n+1) + 2 + b}{n} \;\le\; 1 - H_b\big(\tfrac25\big)
$$
の右辺は $0.0290494\ldots$ である．左辺を $b = 0$ として読んでも，$n = 722$ ではその値が $0.0290799\ldots$ で不等式は成り立たず，$n = 723$ では $0.0290452\ldots$ となって成り立つ．また $n = 1000$ でこの不等式が成り立つのは $b \le 7$ のときに限る．
:::

::: proof
右辺を計算する．$\log_2 5 = 2.3219280\ldots$，$\log_2 3 = 1.5849625\ldots$ だから $\log_2(2/5) = 1 - \log_2 5 = -1.3219280\ldots$，$\log_2(3/5) = \log_2 3 - \log_2 5 = -0.7369655\ldots$ であり，例 1.1.2 より
$$
H_b\big(\tfrac25\big) \;=\; \tfrac25 \times 1.3219280\ldots \;+\; \tfrac35 \times 0.7369655\ldots \;=\; 0.9709505\ldots
$$
である．よって右辺は $0.0290494\ldots$ である．

左辺に移る．$b$ は自然数だから左辺は $b$ について単調に増え，$b = 0$ のときがいちばん小さい．$\log_2 723 = 9.4978518\ldots$ だから $n = 722$ でのその値は $\big(2 \times 9.4978518\ldots + 2\big)/722 = 0.0290799\ldots$ で，右辺より大きい．$\log_2 724 = 9.4998458\ldots$ だから $n = 723$ でのその値は $\big(2 \times 9.4998458\ldots + 2\big)/723 = 0.0290452\ldots$ で，右辺より小さい．

$n = 1000$ を見る．$\log_2 1001 = 9.9672262\ldots$ だから左辺は $\big(21.9344525\ldots + b\big)/1000$ であり，これが右辺以下であることは $b \le 7.1149\ldots$ と同じで，$b$ が自然数であることと合わせて $b \le 7$ と同じである．
:::

例 13.3.12 の $\delta = 1/10$ は粗い要求で，頻度が $0.4$ から $0.6$ のあいだにあれば満たされる．それでも，定数を $b = 0$ と最も甘く見積もって $n$ が $723$ 以上，例 13.3.7 で見た $n = 1000$ では $b$ が $7$ 以下でなければ，証明は何も言わない．定理 13.3.10 と 系 13.3.11 は $n \to \infty$ での主張であって，手元の長さのブロックについて頻度を保証するものではない．

本節が結んだものを並べておく．平均については 定理 13.3.6 で，分布から決まる $H(p)$ と，分布を見ない機械が一本の系列に払う長さの平均が，$1$ 文字あたりで一致した．個々のブロックについては 定理 13.3.10 で，圧縮できないブロックの $1$ の頻度が $1/2$ に近いことが分かった．後者が言っているのは頻度についてだけである．頻度が $1/2$ に近いブロックが圧縮できるかどうかについては，本節は何も述べていない．
