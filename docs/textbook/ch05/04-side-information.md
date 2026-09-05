# 5.4 副情報の値打ち

賭ける前に何かを知ることができるとしよう．馬の調子でも，当日の天候でも，事情通の予想でもよい．知ってから賭ければ倍加率は上がるはずだが，どれだけ上がるのかを一つの数で言えるだろうか．本節の答えは，上がるぶんがちょうど相互情報量 $I(X;Y)$ に等しいというものである．第1章では相互情報量を「二つの確率変数が共有している量」として定義したが，その量が賭けの場面では「$1$ レースあたり余分に稼げる量」として現れる．情報の値打ちが，そのまま賭けの取り分になる．

観測できるものを $Y$ と書く．$(X, Y)$ を有限アルファベット $\mathcal X \times \mathcal Y$ に値をとる対とし，第1章の慣用に従って同時分布を $p(x,y)$，周辺分布を $p(x)$ と $p(y)$，条件付き分布を $p(x \mid y)$ と書く．$X$ が勝ち馬，$Y$ が賭ける前に観測できる **副情報** である．どの組み合わせも起こりうるとして，すべての $(x,y)$ で $p(x,y) > 0$ を仮定する．賭け手は $Y = y$ を見てから配分を選べるので，配分は $y$ ごとに一つずつ用意することになる．

::: definition 5.4.1 条件付き倍加率
$\mathcal X$，$\mathcal Y$ を有限アルファベット，$(X, Y)$ を $\mathcal X \times \mathcal Y$ に値をとる対で，すべての $(x,y)$ で $p(x,y) > 0$ であるものとする．$o : \mathcal X \to \mathbb R$ をすべての $x \in \mathcal X$ で $o(x) > 0$ であるオッズとし，各 $y \in \mathcal Y$ について $b(\cdot \mid y)$ を $\mathcal X$ 上の賭け金の配分（定義 5.1.1）とする．このとき **条件付き倍加率** を
$$
W(b, o \mid Y) \;:=\; \sum_{y \in \mathcal Y} p(y)\, W\big(b(\cdot \mid y),\, o,\, p(\cdot \mid y)\big)
$$
で定める．
:::

右辺の各項が定まることを確かめておく．$p(x,y) > 0$ だから $p(y) > 0$ であり，条件付き分布 $p(\cdot \mid y)$ はすべての $x$ で正である．したがって $W\big(b(\cdot\mid y), o, p(\cdot\mid y)\big)$ は定義 5.1.3 の倍加率としてそのまま読める．条件付き倍加率は，$Y = y$ を見てからその場に応じた配分で賭けたときの倍加率を，$y$ の出方で平均したものであり，定義 1.2.2 の条件付きエントロピーとまったく同じ作り方をしている．

::: formalized
`condDoublingRate` (`InformationTheory/Shannon/Gambling/SideInformation.lean`)
:::

::: formalization-note
形式化は同時分布を，$Y$ の分布と条件付き分布の対として与える．本文の $p(x,y)$ からは $p(y)$ と $p(x\mid y)$ を取り出せばよく，逆にその対からは積で同時分布が戻るので，どちらから出発しても同じものを指している．$X$ の周辺分布も，形式化では条件付き分布を $p(y)$ で平均する形で別に定めてある（`sideMarginalX`）．
:::

## 条件付きの比例賭け

::: theorem 5.4.2
$\mathcal X$，$\mathcal Y$ を有限アルファベット，$(X, Y)$ を $\mathcal X \times \mathcal Y$ に値をとる対で，すべての $(x,y)$ で $p(x,y) > 0$ であるものとし，$o : \mathcal X \to \mathbb R$ をすべての $x \in \mathcal X$ で $o(x) > 0$ であるオッズとする．各 $y \in \mathcal Y$ について $b(\cdot \mid y)$ が $\mathcal X$ 上の賭け金の配分（定義 5.1.1）ならば，条件付き倍加率（定義 5.4.1）について
$$
W(b, o \mid Y) \;\le\; \sum_{y \in \mathcal Y} p(y)\, W\big(p(\cdot \mid y),\, o,\, p(\cdot \mid y)\big)
$$
である．
:::

::: proof
$y \in \mathcal Y$ を一つ固定する．$p(\cdot \mid y)$ はすべての $x$ で正な $\mathcal X$ 上の分布だから，定理 5.2.1 を分布 $p(\cdot\mid y)$，オッズ $o$，配分 $b(\cdot\mid y)$ に当てて
$$
W\big(b(\cdot\mid y), o, p(\cdot\mid y)\big) \;\le\; W\big(p(\cdot\mid y), o, p(\cdot\mid y)\big)
$$
を得る．両辺に $p(y) > 0$ を掛けて $y$ について足せば，定義 5.4.1 より主張の不等式になる．
:::

::: formalized
`condDoublingRate_le_proportional` (`InformationTheory/Shannon/Gambling/SideInformation.lean`)
:::

定理 5.4.2 は定理 5.2.1 を $y$ ごとに当てただけである．副情報を見たあとの賭け手は，そのとき $X$ が従うと信じている分布，すなわち条件付き分布 $p(\cdot \mid y)$ をそのまま配分にすればよい．副情報のあるなしで賭け方の原則は変わらず，変わるのは「自分が信じている分布」のほうである．

::: definition 5.4.3 最適倍加率
$\mathcal X$，$\mathcal Y$ を有限アルファベット，$(X, Y)$ を $\mathcal X \times \mathcal Y$ に値をとる対で，すべての $(x,y)$ で $p(x,y) > 0$ であるものとし，$o : \mathcal X \to \mathbb R$ をすべての $x \in \mathcal X$ で $o(x) > 0$ であるオッズとする．
$$
W^{*}(X) \;:=\; W(p, o, p),
\qquad
W^{*}(X \mid Y) \;:=\; \sum_{y \in \mathcal Y} p(y)\, W\big(p(\cdot \mid y),\, o,\, p(\cdot \mid y)\big)
$$
と書き，この二つを **最適倍加率** と呼ぶ．オッズ $o$ と同時分布は記号に書かないが，どちらも固定されているものとする．
:::

定理 5.2.1 より $W^{*}(X)$ は副情報を使わない配分の中での最大値であり，定理 5.4.2 より $W^{*}(X \mid Y)$ は $y$ ごとに選べる配分の中での最大値である．$X$ の周辺分布はすべての $x$ で $p(x) = \sum_y p(x,y) > 0$ だから，$W^{*}(X)$ のほうも定義 5.1.3 の倍加率として読める．二つの最大値の差が，副情報を手に入れたことの値打ちである．

## 増分は相互情報量

::: theorem 5.4.4
$\mathcal X$，$\mathcal Y$ を有限アルファベット，$(X, Y)$ を $\mathcal X \times \mathcal Y$ に値をとる対で，すべての $(x,y)$ で $p(x,y) > 0$ であるものとし，$o : \mathcal X \to \mathbb R$ をすべての $x \in \mathcal X$ で $o(x) > 0$ であるオッズとする．このとき
$$
W^{*}(X \mid Y) - W^{*}(X) \;=\; I(X; Y)
$$
である．
:::

::: proof
条件付きのほうを書き直す．$y$ を固定すると $p(\cdot\mid y)$ はすべての $x$ で正な分布だから，定理 5.3.1 をそれに当てて
$$
W\big(p(\cdot\mid y), o, p(\cdot\mid y)\big) \;=\; \sum_{x} p(x \mid y) \log o(x) \;-\; H(X \mid Y = y)
$$
を得る．両辺に $p(y)$ を掛けて $y$ について足す．第 1 項は $\sum_y \sum_x p(y)\,p(x\mid y) \log o(x) = \sum_x p(x)\log o(x)$ であり，第 2 項の和は定義 1.2.2 より $H(X \mid Y)$ である．よって定義 5.4.3 より
$$
W^{*}(X \mid Y) \;=\; \sum_{x} p(x) \log o(x) \;-\; H(X \mid Y)
$$
となる．

副情報を使わないほうは定理 5.3.1 そのもので，$W^{*}(X) = \sum_x p(x)\log o(x) - H(X)$ である．差をとるとオッズの項が消えて $H(X) - H(X \mid Y)$ が残り，定理 1.3.4 よりこれは $I(X;Y)$ に等しい．
:::

::: formalized
`sideInfo_doublingRate_increment_eq_mutualInfo` (`InformationTheory/Shannon/Gambling/SideInformation.lean`)
:::

::: formalization-note
形式化は右辺の相互情報量を $H(X) + H(Y) - H(X, Y)$ の形で書いている．本書の定義 1.3.1 とこの形が一致することは定理 1.3.4 で示してあるので，主張の中身は同じである．
:::

定理 5.4.4 は，第1章で「共有されている量」として定義した $I(X;Y)$ に，値段をつけたものと読める．相互情報量が $1$ ビットなら，副情報を使えるようになったことで倍加率もちょうど $1$ だけ増える．しかも増分の式にオッズは現れない．定理 5.4.4 の証明でオッズの項が引き算で消えるところがそれで，胴元がどんなオッズをつけていても，副情報の値打ちは同時分布だけで決まる．また命題 1.3.2 より $I(X;Y) \ge 0$ だから，副情報を得て損をすることはなく，等号すなわち値打ちが $0$ になるのは $X$ と $Y$ が独立なときに限る．関係のない情報に金を払う価値はない，ということである．

::: example 5.4.5 二値の副情報
$\mathcal X = \mathcal Y = \{1, 2\}$ とし，$Y$ の分布を一様，すなわちすべての $y \in \mathcal Y$ で $p(y) = 1/2$ とする．条件付き分布は $p(x \mid y) = 0.9$（$x = y$ のとき），$p(x \mid y) = 0.1$（$x \ne y$ のとき）とする．オッズを $o(1) = o(2) = 2$ とすると $W^{*}(X) = 0$，$W^{*}(X \mid Y) = 0.5310\ldots$ であり，その差は $I(X;Y) = 0.5310\ldots$ に等しい．
:::

::: proof
$X$ の周辺分布は $p(x) = \frac12 \cdot 0.9 + \frac12 \cdot 0.1 = \frac12$ であり，$H(X) = \log 2 = 1$ である．オッズは $o(x) = \lvert\mathcal X\rvert = 2$ だから，系 5.3.2 より $W^{*}(X) = \log 2 - H(X) = 0$ である．各 $y$ について $p(\cdot \mid y)$ は確率 $0.9$ のベルヌーイ分布だから，例 1.1.2 の二値エントロピー関数を使って $H(X \mid Y = y) = H_b(0.9) = 0.4689\ldots$ であり，系 5.3.2 を $p(\cdot\mid y)$ に当てると $W\big(p(\cdot\mid y), o, p(\cdot\mid y)\big) = \log 2 - H_b(0.9) = 0.5310\ldots$ である．$y$ について平均しても同じ値だから $W^{*}(X \mid Y) = 0.5310\ldots$ になる．定義 1.2.2 より $H(X\mid Y) = H_b(0.9)$ なので，定理 1.3.4 より $I(X;Y) = H(X) - H(X\mid Y) = 1 - 0.4689\ldots = 0.5310\ldots$ である．
:::

例 5.4.5 の副情報は，勝ち馬を $9$ 割の確からしさで当てる予想である．それがないうちは，一様なオッズと一様な分布で稼ぎようがない（系 5.3.2 の等号の場合である）．予想を手に入れると倍加率は $0.5310\ldots$ になり，増えたぶんは $W^{*}(X) = 0$ だったので $I(X;Y)$ ちょうどである．$9$ 割の予想が $1$ ビットに届かないのは，$1$ 割の外れが残っていて $X$ と $Y$ の共有が完全ではないからである．稼ぎの側から言えば，予想を見たあとでも勝ち馬にはまだ $H_b(0.9) = 0.4689\ldots$ の不確かさが残っており，系 5.3.2 のとおり，その残りぶんだけ稼ぎ損ねている．
