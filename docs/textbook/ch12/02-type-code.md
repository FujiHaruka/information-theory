# 12.2 型による万能符号

12.1 節は，族のどれが真かを知らずに符号を作る問題を，冗長度という一つの量に落とした．残っているのは，その量を族によらず小さくする符号長の組を実際に作ることである．手がかりは第11章にある．系列 $x$ の型 $\hat P_x$（定義 11.1.1）は $x$ の中で各文字が何回出たかだけから決まり，真の分布を持ち出さずに計算できる．しかも 定理 11.1.8 が，型類の要素数を型のエントロピーで測っている．そこで，まず型を送り，次に型類の中で何番目かを送る，という二段構えの符号を考える．受け取る側は，前半で型を知り，後半でその型類の中の位置を知るので，二つを合わせれば系列が復元できる．

この構成のどこにも $P_\theta$ が現れないことが要点である．符号を作る側が見るのは送る系列だけで，族についての知識は使わない．それでいて，前半の長さは型の個数で決まり（型は多項式個しかない），後半の長さは型類の要素数で決まる（要素数は型のエントロピーで抑えられる）ので，符号長は自動的にその系列の型のエントロピーに近くなる．この節はその見積もりを最後まで書き下す．

## 二段符号の符号長

::: definition 12.2.1 型による二段符号の符号長
$\mathcal X$ を空でない有限アルファベット，$n \ge 1$ とする．$x \in \mathcal X^n$ の型を $\hat P_x$，長さ $n$ の型 $P$ の型類を $\mathcal T_n(P)$（どちらも 定義 11.1.1）と書き，
$$
\ell^{\mathrm T}_n(x) \;:=\; \big\lceil\, \lvert\mathcal X\rvert\log_2(n+1) \,\big\rceil
  \;+\; \Big\lceil\, \log_2 \big\lvert\mathcal T_n\big(\hat P_x\big)\big\rvert \,\Big\rceil
$$
と定める．$\ell^{\mathrm T}_n$ を **型による二段符号の符号長** と呼ぶ．
:::

第 $1$ 項は型そのものを指すための長さである．長さ $n$ の型は $(n+1)^{\lvert\mathcal X\rvert}$ 個以下しかない（命題 11.1.3）ので，型に通し番号を振れば $\lvert\mathcal X\rvert\log_2(n+1)$ ビットあまりで書ける．第 $2$ 項は，型が決まったあとに型類の中の位置を指すための長さである．どちらも切り上げてあるのは，符号語長が整数でなければならないからで，天井関数とその性質 $t \le \lceil t \rceil < t+1$ は 4.4 節で既知としたとおりに本節でも使う．第 $1$ 項が $x$ に依らないのは，型を書くための場所を，どの系列についても同じだけ確保しているからである．

::: formalization-note
型による二段符号の符号長に対応する宣言は無い．型と型類は 定義 11.1.1 の形式化がそのまま使えるが，それを符号長に組み上げた宣言は無い．
:::

::: proposition 12.2.2
$\mathcal X$ を空でない有限アルファベット，$n \ge 1$ とする．$\ell^{\mathrm T}_n$（定義 12.2.1）は 定義 12.1.1 の意味で長さ $n$ の符号長の組であり，すべての $x \in \mathcal X^n$ で $\ell^{\mathrm T}_n(x) \ge 1$ である．したがって 定理 4.2.2 より，$\mathcal X^n$ 上の二元語頭符号で，各 $x$ の符号語長が $\ell^{\mathrm T}_n(x)$ に等しいものが存在する．
:::

::: proof
$A := \lceil \lvert\mathcal X\rvert\log_2(n+1)\rceil$ と置く．$n \ge 1$ より $\log_2(n+1) \ge 1$ であり，$\mathcal X$ は空でないから $\lvert\mathcal X\rvert \ge 1$ で，$\lvert\mathcal X\rvert\log_2(n+1) \ge 1$ である．天井関数の性質より $A \ge 1$ であり，第 $2$ 項は $0$ 以上だから $\ell^{\mathrm T}_n(x) \ge 1$ である．値が整数であることも天井関数の定義から従う．

Kraft の不等式に移る．どの $x$ もただ一つの型をもつ（定義 11.1.1）から，長さ $n$ の型の型類は $\mathcal X^n$ を重なりなく覆う．$x \in \mathcal T_n(P)$ ならば $\hat P_x = P$ なので，その上で $\ell^{\mathrm T}_n(x) = A + \lceil\log_2\lvert\mathcal T_n(P)\rvert\rceil$ は一定である．よって $P$ が長さ $n$ の型の全体をわたる和として
$$
\sum_{x \in \mathcal X^n} 2^{-\ell^{\mathrm T}_n(x)}
  \;=\; 2^{-A}\sum_{P} \big\lvert\mathcal T_n(P)\big\rvert\,
    2^{-\lceil\log_2\lvert\mathcal T_n(P)\rvert\rceil}
$$
と書ける．長さ $n$ の型の型類は空でないから $\lvert\mathcal T_n(P)\rvert \ge 1$ であり，天井関数の性質より $\lceil\log_2\lvert\mathcal T_n(P)\rvert\rceil \ge \log_2\lvert\mathcal T_n(P)\rvert$ だから，和の各項は
$$
\big\lvert\mathcal T_n(P)\big\rvert\,2^{-\lceil\log_2\lvert\mathcal T_n(P)\rvert\rceil}
  \;\le\; \big\lvert\mathcal T_n(P)\big\rvert\,2^{-\log_2\lvert\mathcal T_n(P)\rvert} \;=\; 1
$$
を満たす．項の個数は 命題 11.1.3 より $(n+1)^{\lvert\mathcal X\rvert}$ 以下である．また $A \ge \lvert\mathcal X\rvert\log_2(n+1)$ より $2^{-A} \le (n+1)^{-\lvert\mathcal X\rvert}$ である．三つを合わせると和は $1$ 以下になる．

最後に 定理 4.2.2 を，アルファベット $\mathcal X^n$，$D = 2$，長さの組 $\ell^{\mathrm T}_n$ に当てる．値が $1$ 以上の整数であることと Kraft の不等式は上で見たとおりである．
:::

第 $1$ 項の $A$ が，型の個数を数えた 命題 11.1.3 の指数をそのまま切り上げた形になっているのが，Kraft の不等式が閉じる仕組みである．型ごとに $2^{-A}$ という同じ大きさの場所を割り当て，その中を型類の要素で分け合う．型の個数が $2^A$ 以下だから，全部足しても $1$ を超えない．なお 命題 12.2.2 が与えるのは，この長さをもつ二元語頭符号が存在することであって，節のはじめに述べた二段の手続きがそのまま符号になっている，ということではない．二段の説明は長さの由来を述べたもので，符号の存在のほうは 定理 4.2.2 が引き受けている．

## 型のエントロピーの平均

::: lemma 12.2.3
$\mathcal X$ を空でない有限アルファベット，$n \ge 1$ とし，$P$ を $\mathcal X$ 上の分布，$P^n$ をその $n$ 重の積分布とする．$x \in \mathcal X^n$ の型を $\hat P_x$（定義 11.1.1）と書くと
$$
\sum_{x \in \mathcal X^n} P^n(\{x\})\,H\big(\hat P_x\big) \;\le\; H(P)
$$
である（$H$ は 定義 1.1.1 のエントロピー）．
:::

::: proof
$\varphi(t) = -t\log_2 t$（$t \ge 0$，$\varphi(0) := 0$）と置くと，定義 1.1.1 より $H(\hat P_x) = \sum_{a \in \mathcal X}\varphi(\hat P_x(a))$ である．$\mathcal X$ も $\mathcal X^n$ も有限だから和の順序を入れ替えてよく
$$
\sum_{x \in \mathcal X^n} P^n(\{x\})\,H\big(\hat P_x\big)
  \;=\; \sum_{a \in \mathcal X}\ \sum_{x \in \mathcal X^n} P^n(\{x\})\,\varphi\big(\hat P_x(a)\big)
$$
となる．文字 $a \in \mathcal X$ を固定して内側の和を評価する．$P^n$ は $\mathcal X^n$ 上の分布だから重み $P^n(\{x\})$ は非負で総和が $1$ であり，点 $\hat P_x(a)$ は $\varphi$ の定義域 $[0,\infty)$ に入る．1.1 節で認めた $\varphi$ の凹性のもと 補題 1.1.6 を当てると
$$
\sum_{x \in \mathcal X^n} P^n(\{x\})\,\varphi\big(\hat P_x(a)\big)
  \;\le\; \varphi\Big(\sum_{x \in \mathcal X^n} P^n(\{x\})\,\hat P_x(a)\Big)
$$
である．

内側の重心を求める．定義 11.1.1 より $\hat P_x(a) = N(a\mid x)/n$ で，$N(a\mid x)$ は $x_i = a$ となる位置 $i$ の個数だから，位置ごとに数えると
$$
\sum_{x \in \mathcal X^n} P^n(\{x\})\,N(a \mid x)
  \;=\; \sum_{i=0}^{n-1}\ \sum_{x\,:\,x_i = a} P^n(\{x\})
  \;=\; \sum_{i=0}^{n-1} P(a) \;=\; n\,P(a)
$$
である（$P^n$ の第 $i$ 成分の周辺分布は $P$ だから，内側の和は $P(a)$ に等しい）．よって重心は $P(a)$ であり，上の不等式の右辺は $\varphi(P(a))$ になる．$a$ について足すと，右辺の和は $\sum_{a}\varphi(P(a)) = H(P)$ であり，主張を得る．
:::

補題 12.2.3 が言っているのは，型のエントロピーは平均すると真の分布のエントロピーを超えない，ということである．長さ $n$ の系列を見て作った型は，真の分布のまわりで揺れている．揺れているぶんだけエントロピーは上にも下にも動きうるが，$\varphi$ が凹であるために，平均をとると下側に寄る．二段符号の後半の長さは型類の要素数で決まり，それが型のエントロピーで抑えられているので，平均符号長を真の分布のエントロピーと比べるときに，この補題がちょうど必要な向きの不等式を与える．

## 冗長度の評価

::: theorem 12.2.4 型による万能符号の冗長度
定義 12.1.1 の設定で $n \ge 1$ とすると，どの $\theta \in \Theta$ についても
$$
\Delta_n\big(\ell^{\mathrm T}_n, \theta\big)
  \;\le\; \frac{\lvert\mathcal X\rvert\log_2(n+1) + 2}{n}
$$
である（$\ell^{\mathrm T}_n$ は 定義 12.2.1 の符号長の組，$\Delta_n$ は 定義 12.1.2 の冗長度）．
:::

::: proof
天井関数の性質 $\lceil t \rceil < t + 1$ を 定義 12.2.1 の二つの項に当てると
$$
\ell^{\mathrm T}_n(x) \;<\; \lvert\mathcal X\rvert\log_2(n+1) + 2
  \;+\; \log_2\big\lvert\mathcal T_n\big(\hat P_x\big)\big\rvert
$$
である．

型類の要素数を本章の底で読み直す．第11章は $\log$ の底を自然対数にとっているので，定理 11.1.8 の上界は，そこで測ったエントロピーを $e$ の肩に乗せた形をしている．エントロピーを底 $b$ で測った値は自然対数で測った値の $1/\log_{\mathrm e}b$ 倍だから，底 $b$ で測ったエントロピーを $b$ の肩に乗せた量は $b$ の取り方に依らない．したがって 定理 11.1.8 の上界は，本章の底では
$$
\big\lvert\mathcal T_n(P)\big\rvert \;\le\; 2^{\,n H(P)}
$$
と読める（$H$ は本章の底で測ったエントロピーである）．この書き換えを落とすと単位が合わない．両辺の $\log_2$ をとると $\log_2\lvert\mathcal T_n(P)\rvert \le n\,H(P)$ であり，$P := \hat P_x$ ととって上の評価に入れると
$$
\ell^{\mathrm T}_n(x) \;<\; \lvert\mathcal X\rvert\log_2(n+1) + 2 + n\,H\big(\hat P_x\big)
$$
となる．

$\theta \in \Theta$ をとり，両辺に $P^n_\theta(\{x\})$ を掛けて $x$ について足す．$\sum_x P^n_\theta(\{x\}) = 1$ と，補題 12.2.3 を $P := P_\theta$ に当てた不等式から
$$
\sum_{x \in \mathcal X^n} P^n_\theta(\{x\})\,\ell^{\mathrm T}_n(x)
  \;<\; \lvert\mathcal X\rvert\log_2(n+1) + 2 + n\,H\big(P_\theta\big)
$$
である．いっぽう $P^n_\theta$ は分布 $P_\theta$ の i.i.d. 情報源の長さ $n$ のブロックの分布だから，補題 2.3.3 より $H(P^n_\theta) = n\,H(P_\theta)$ である．これを引いて $n$ で割ると，定義 12.1.2 より
$$
\Delta_n\big(\ell^{\mathrm T}_n,\theta\big) \;<\; \frac{\lvert\mathcal X\rvert\log_2(n+1) + 2}{n}
$$
となり，主張の不等式が従う．
:::

::: formalization-note
定理 12.2.4 に対応する宣言は無い．使う道具のうち，命題 11.1.3 の `numTypes_le` (`InformationTheory/Shannon/Sanov/MultinomialLowerBound.lean`) と，定理 11.1.8 の上界を与える `typeClassByCount_card_le` (`InformationTheory/Shannon/Sanov/MultinomialLowerBound.lean`)，およびその量を $e^{\,nH(P)}$ に書き換える `pow_div_prod_pow_eq_exp_n_entropyByCount` (`InformationTheory/Shannon/TypeClassLowerBound.lean`) は在庫にあるが，そこから符号長の期待値を評価した宣言は無い．
:::

::: corollary 12.2.5
定義 12.1.1 の設定で $n \ge 1$ とすると
$$
\Delta^*_n \;\le\; \frac{\lvert\mathcal X\rvert\log_2(n+1) + 2}{n}
$$
である（$\Delta^*_n$ は 定義 12.1.5 のミニマックス冗長度）．右辺は $\Theta$ にも $P_\theta$ にも依らず，$n \to \infty$ で $0$ に収束する．
:::

::: proof
命題 12.2.2 より $\ell^{\mathrm T}_n$ は長さ $n$ の符号長の組だから，定義 12.1.5 の下限をとる範囲に入る．よって $\Delta^*_n \le \max_{\theta}\Delta_n(\ell^{\mathrm T}_n,\theta)$ であり，$\Theta$ は有限で，どの $\theta$ でも 定理 12.2.4 の評価が成り立つから，最大も同じ値以下である．

右辺が $\Theta$ にも $P_\theta$ にも依らないことは式の形から見てとれる．収束は 補題 11.2.2 から出る．あちらは第11章の底で述べてあるが，底を取り替えても対数の値は定数倍しか変わらないので $\log_2(n+1)/n \to 0$ であり，$\lvert\mathcal X\rvert$ は $n$ に依らない有限の数だから第 $1$ 項は $0$ に収束する．第 $2$ 項 $2/n$ も $0$ に収束する．
:::

系 12.2.5 が万能符号の存在の主張である．族をどう与えても，$\ell^{\mathrm T}_n$ という一つの符号長の組が，族のすべての $\theta$ に対して同じ上界を満たす．しかもその上界は族の中身を見ずに書けており，$n$ を大きくとれば $0$ に近づく．分布を知っている場合の $1/n$ 未満（例 12.1.4）に比べれば $\log_2 n$ の因子だけ大きいが，$1$ 文字あたりで見れば，どちらも $n \to \infty$ で消える量である．知らないことの代償として 系 12.2.5 が払っているのは，例 12.1.6 の決めつけのような定数ではなく，$\log_2 n$ の因子である．

::: example 12.2.6 二つの偏ったコイン（続き）
例 12.1.6 の族で $n = 1000$ とすると，系 12.2.5 の右辺は
$$
\frac{2\log_2 1001 + 2}{1000} \;=\; 0.02193\ldots
$$
ビットである．
:::

::: proof
$\lvert\mathcal X\rvert = 2$ である．$\log_2 1001 = 9.9672\ldots$ だから，右辺は $(2 \times 9.9672\ldots + 2)/1000 = 21.934\ldots/1000$ である．
:::

::: formalization-note
例 12.2.6 は形式化されていない．例 12.2.6 に付した計算が，この主張の保証のすべてである．
:::

数を並べると差がはっきりする．同じ族で，$\theta = 1$ と決めつけたときの冗長度は $2.535\ldots$ ビット以上であり（例 12.1.6），系列をそのまま書き写したときは $0.531\ldots$ ビットだった．型による二段符号は，$n = 1000$ でそのどちらより小さい $0.0219\ldots$ ビット以下に収まる．どの $\theta$ が真かを知らないまま，知っている場合との差を $0.022$ ビットを下回るところまで詰めたことになる．

上からの評価はこれで得られた．残るのは下からで，冗長度をこれ以上小さくできない理由がどこにあるかである．次節はそれを，族の中の分布どうしの隔たりを測る量として取り出す．
