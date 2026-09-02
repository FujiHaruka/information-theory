# 3.5 Shannon–McMillan–Breiman 定理

第2章の漸近等分配性（定理 2.1.4）は、i.i.d. 情報源で 1 文字あたりの驚きが $H(X)$ に
近づく、という主張だった。本節はそれをエルゴード的な定常情報源に広げる。近づく先は
$H(X)$ ではなくエントロピーレート $H(\mathcal X)$ で、収束は概収束——確率 1 の事象の上で
各点の収束——である。この一般化を Shannon–McMillan–Breiman 定理という。

まず量の名前を用意する。

::: definition 3.5.1 経験エントロピー
定常情報源 $\{X_i\}$ に対し、ブロックの確率を $p(x^n) := \Pr[X^n = x^n]$ と書く。
$n \ge 1$ に対し
$$
\hat H_n \;:=\; -\frac1n \log p\big(X^n\big)
$$
を長さ $n$ の **経験エントロピー** という。
:::

式は定義 2.1.1 とまったく同じで、i.i.d. の仮定を外して同じ量を使う、という宣言である。
違いは使える道具のほうにある。あちらでは独立性から $p(X^n)$ が周辺分布の積にほどけ
（補題 2.1.3）、大数の法則にかけられる形になった。記憶のある情報源ではこのほどきが
使えない。ほどく代わりに何をするかが、本節の中身である。

実現したブロックの確率は正だから、$\hat H_n$ は確率 1 で定まる有限の値をとる。

::: theorem 3.5.2 Shannon–McMillan–Breiman
$\{X_i\}$ をエルゴード的な定常情報源とする。確率 1 で
$$
\hat H_n \;=\; -\frac1n \log p\big(X^n\big) \;\longrightarrow\; H(\mathcal X)
\qquad (n \to \infty).
$$
:::

証明は上下からの挟み撃ちで行う。上からは記憶を有限の深さで打ち切った近似を、下からは
無限の過去まで使った近似を当てる。どちらの側でも働くのは「確率分布どうしの比の期待値は
1 を超えない」という一手だけなので、それを先に補題として切り出しておく。証明本体は
補題 3.5.5 と補題 3.5.6 で、二つがそろったところで定理 3.5.2 の証明に戻る。

## 借りる道具

3.4 節の Birkhoff の個別エルゴード定理に加えて、下界（補題 3.5.6）の証明でだけ次の
二つを借りる。上界（補題 3.5.5）はどちらも使わない。

**両側への拡張.** 定常情報源 $\{X_i\}_{i \ge 0}$ に対し、負の時刻まで延ばした列
$\{X_i\}_{i \in \mathbb Z}$ で、定常であり、かつ非負の時刻の部分の同時分布が元の情報源と
一致するものが存在する。元がエルゴード的なら、延ばした列もシフトについてエルゴード的で
ある。

**無限の過去による条件付け.** 両側に延ばした列について、有限の過去で条件付けた確率
$p(X_0 \mid X_{-1}, \dots, X_{-k})$ は $k \to \infty$ で確率 1 に収束する。その極限を
$p(X_0 \mid X_{-1}, X_{-2}, \dots)$ と書く。さらに期待値も収束し、
$$
\mathbb E\big[-\log p(X_0 \mid X_{-1}, X_{-2}, \dots)\big]
  \;=\; \lim_{k\to\infty} H\big(X_0 \,\big|\, X_{-1}, \dots, X_{-k}\big)
$$
が成り立つ。これは Lévy のマルチンゲール収束定理——増えていく情報で条件付けた期待値は、
その全体で条件付けた期待値に収束する——と収束定理から得られる。

どちらも本書では証明しないが、3.4 節の Birkhoff の定理と同じく、無条件の機械検証済みの
定理として形式化されている。

::: formalized
両側への拡張 `μZ`、シフトの測度保存性 `measurePreserving_shiftZ`、エルゴード性
`ergodic_shiftZ` (`InformationTheory/Probability/TwoSidedExtension/Core.lean`)、
無限の過去で条件付けた負対数の期待値 `integral_pmfLogCondInfty_eq_entropyRate`
(`InformationTheory/Probability/TwoSidedExtension/LogCondIntegral.lean`)
:::

## 比は指数の尺度では見えない

::: lemma 3.5.3
非負の確率変数の列 $(R_n)_{n \ge 1}$ が任意の $n$ で $\mathbb E[R_n] \le 1$ を満たすなら、
確率 1 で
$$
\limsup_{n\to\infty} \frac1n \log R_n \;\le\; 0
$$
である（$R_n = 0$ のときは $\log R_n = -\infty$ と読む）。
:::

::: proof
$A_n := \{R_n \ge n^2\}$ とおく。$R_n \ge 0$ だからマルコフの不等式が使えて
$\Pr[A_n] \le \mathbb E[R_n]/n^2 \le 1/n^2$ である。したがって任意の $N \ge 1$ に対し
$$
\Pr\Big[\bigcup_{n \ge N} A_n\Big] \;\le\; \sum_{n \ge N} \frac1{n^2}
$$
であり、$\sum_n n^{-2}$ が収束するので右辺は $N \to \infty$ で $0$ に向かう。左辺は
$N$ について非増加だから、「$A_n$ が無限回起こる」事象
$\bigcap_N \bigcup_{n\ge N} A_n$ の確率は $0$ である。

すなわち確率 1 で、十分大きなすべての $n$ について $R_n < n^2$、したがって
$$
\frac1n \log R_n \;<\; \frac{2\log n}{n}
$$
である。右辺は $0$ に収束するので、上極限は $0$ 以下である。
:::

補題 3.5.3 が言っているのは、期待値が 1 で抑えられた比は $n^2$ より速くは大きくならず、
$\frac1n\log$ という尺度ではそれが $0$ に潰れる、ということである。第2章の議論が
指数の肩を $1/n$ の精度でしか見ていなかったのと同じ粗さで、この粗さのおかげで
「多項式ぶんのずれ」は最初から見えない。

## 記憶を $k$ 文字で打ち切る

記憶の深さを $k$ 文字に制限した近似分布を作る。$k \ge 0$ と $n > k$ に対し
$$
q_k\big(x^n\big) \;:=\; p\big(x^k\big)
  \prod_{i=k}^{n-1} p\big(x_i \,\big|\, x_{i-k}, \dots, x_{i-1}\big)
$$
と定める。ここで $p(x_i \mid x_{i-k}, \dots, x_{i-1})$ は、定常性により時刻に依らない量
$\Pr[X_k = x_i \mid X^k = (x_{i-k}, \dots, x_{i-1})]$ を表す（$p(x^0) := 1$。条件にあたる
長さ $k$ の並びの確率が $0$ のときは $q_k(x^n) := 0$ と約束する）。$q_k$ は
$\mathcal X^n$ 上で $\sum_{x^n} q_k(x^n) \le 1$ を満たす——後ろの文字から順に和をとると、
各段の条件付き確率の和が 1 以下だからである。

これは「直前の $k$ 文字しか覚えていない情報源」が同じブロックに与える確率である。
$k = 0$ なら 1 文字ずつ独立に出す情報源、$k = 1$ ならマルコフ情報源（3.3 節）にあたる。

::: lemma 3.5.4
$\{X_i\}$ をエルゴード的な定常情報源とする。各 $k \ge 0$ に対し、確率 1 で
$$
-\frac1n \log q_k\big(X^n\big) \;\longrightarrow\; H\big(X_k \,\big|\, X^k\big)
\qquad (n \to \infty).
$$
:::

::: proof
実現した並びの確率は正だから、確率 1 で $p(X^k) > 0$ であり、また $k \le i \le n-1$ の
各 $i$ について $(X_{i-k}, \dots, X_{i-1})$ の確率も正である。よって確率 1 で
$q_k(X^n) > 0$ であり、対数をとって
$$
-\frac1n \log q_k\big(X^n\big)
  \;=\; -\frac1n \log p\big(X^k\big)
    + \frac1n \sum_{i=k}^{n-1} \Big(-\log p\big(X_i \,\big|\, X_{i-k}, \dots, X_{i-1}\big)\Big)
$$
と分かれる。第 1 項は $n$ に依らない確率変数を $n$ で割ったものだから $0$ に収束する。

第 2 項に 3.4 節の Birkhoff の定理を当てる。先頭 $k+1$ 文字だけで決まる関数
$$
f_k(x) \;:=\; -\log p\big(x_k \,\big|\, x_0, \dots, x_{k-1}\big)
$$
をとると、定常性より
$-\log p(X_i \mid X_{i-k}, \dots, X_{i-1}) = f_k(\sigma^{i-k} X)$ である。$j := i-k$ と
置き換えると第 2 項は
$$
\frac1n \sum_{j=0}^{n-k-1} f_k\big(\sigma^j X\big)
  \;=\; \frac{n-k}{n} \cdot \frac{1}{n-k}\sum_{j=0}^{n-k-1} f_k\big(\sigma^j X\big)
$$
になる。$f_k \ge 0$ であり、その期待値は定義 1.2.2 より $H(X_k \mid X^k)$ で、これは
定理 1.2.4 と定理 1.1.5 より $\log|\mathcal X|$ 以下だから、$f_k$ は可積分である
（$f_k$ は確率 $0$ の並びの上で $+\infty$ になりうるが、可積分性には影響しない）。
Birkhoff の定理より第 2 因子は確率 1 で $H(X_k \mid X^k)$ に収束し、
$\frac{n-k}{n} \to 1$ と合わせて主張を得る。
:::

::: formalized
`negLogQk_div_tendsto_condEntropyTail`
(`InformationTheory/Shannon/SMB/AlgoetCover/KMarkovApproximation.lean`)
:::

## 上界

::: lemma 3.5.5
$\{X_i\}$ をエルゴード的な定常情報源とする。確率 1 で
$\limsup_{n} \hat H_n \le H(\mathcal X)$。
:::

::: proof
$k \ge 0$ を固定する。確率 1 で $p(X^n) > 0$ だから
$$
R_n \;:=\; \frac{q_k\big(X^n\big)}{p\big(X^n\big)} \qquad (n > k)
$$
は確率 1 で定まる非負の確率変数である。その期待値は
$$
\mathbb E\big[R_n\big]
  \;=\; \sum_{x^n \,:\, p(x^n) > 0} p\big(x^n\big)\,\frac{q_k(x^n)}{p(x^n)}
  \;=\; \sum_{x^n \,:\, p(x^n) > 0} q_k\big(x^n\big) \;\le\; 1
$$
である。補題 3.5.3 より確率 1 で $\limsup_n \frac1n\log R_n \le 0$、すなわち
$$
\frac1n \log R_n \;=\; \hat H_n - \Big(-\frac1n\log q_k\big(X^n\big)\Big)
$$
と書き直して
$\limsup_n\big(\hat H_n - (-\frac1n\log q_k(X^n))\big) \le 0$ である。補題 3.5.4 より
引かれている側は $H(X_k \mid X^k)$ に収束するから
$$
\limsup_n \hat H_n \;\le\; H\big(X_k \,\big|\, X^k\big).
$$
これが各 $k$ について確率 1 で成り立つ。可算個の確率 1 の事象の共通部分もまた確率 1 だから、
確率 1 ですべての $k$ について同時に成り立つ。そこで $k \to \infty$ とすれば、定理 3.2.6
より右辺は $H(\mathcal X)$ に収束する。
:::

::: formalized
`algoet_cover_limsup_bound` (`InformationTheory/Shannon/SMB/AlgoetCover/Limsup.lean`)
:::

## 下界

::: lemma 3.5.6
$\{X_i\}$ をエルゴード的な定常情報源とする。確率 1 で
$\liminf_{n} \hat H_n \ge H(\mathcal X)$。
:::

::: proof
本節の冒頭で借りた両側への拡張により、以下では $\{X_i\}$ を $i \in \mathbb Z$ に
延ばしたエルゴード的な定常列とみなす。
$$
g(x) \;:=\; -\log p\big(x_0 \,\big|\, x_{-1}, x_{-2}, \dots\big)
$$
とおくと、もう一つの借用と定常性、定理 3.2.6 から
$$
\mathbb E\big[g(X)\big] \;=\; \lim_{k\to\infty} H\big(X_0 \,\big|\, X_{-1},\dots,X_{-k}\big)
  \;=\; \lim_{k\to\infty} H\big(X_k \,\big|\, X^k\big) \;=\; H(\mathcal X)
$$
である。$g \ge 0$ の期待値が有限なのだから、とくに $g$ は可積分である。

**比の期待値を抑える.** 無限の過去を $\mathcal P := (X_{-1}, X_{-2}, \dots)$ と書き、
$$
q_\infty\big(X^n\big) \;:=\; \prod_{i=0}^{n-1} p\big(X_i \,\big|\, X_{i-1}, X_{i-2}, \dots\big)
$$
とおく。条件付き確率の連鎖律より、これは $\mathcal P$ を与えたときの $X^n$ の条件付き確率
$p(X^n \mid \mathcal P)$ にほかならない。$R_n := p(X^n)/q_\infty(X^n)$ とおくと、$\mathcal P$
を固定した条件付き期待値は
$$
\mathbb E\big[R_n \,\big|\, \mathcal P\big]
  \;=\; \sum_{x^n} p\big(x^n \,\big|\, \mathcal P\big)\,
        \frac{p(x^n)}{p(x^n \mid \mathcal P)}
  \;=\; \sum_{x^n \,:\, p(x^n \mid \mathcal P) > 0} p\big(x^n\big) \;\le\; 1
$$
である。両辺の期待値をとって $\mathbb E[R_n] \le 1$ を得る。

**補題 3.5.3 を当てる.**
$\frac1n\log R_n = \big(-\frac1n\log q_\infty(X^n)\big) - \hat H_n$ だから、確率 1 で
$$
\limsup_n \Big(\big(-\tfrac1n\log q_\infty(X^n)\big) - \hat H_n\Big) \;\le\; 0 .
$$
一方 $-\frac1n\log q_\infty(X^n) = \frac1n\sum_{i=0}^{n-1} g(\sigma^i X)$ であり、両側に
延ばした列もエルゴード的な定常列だから、Birkhoff の定理よりこれは確率 1 で
$\mathbb E[g(X)] = H(\mathcal X)$ に収束する。$a_n := \hat H_n$、
$b_n := -\frac1n\log q_\infty(X^n)$ と書くと $a_n = b_n - (b_n - a_n)$ だから
$$
\liminf_n a_n \;\ge\; \lim_n b_n - \limsup_n\big(b_n - a_n\big) \;\ge\; H(\mathcal X)
$$
である。

最後に、主張は $X^n$ だけで決まる量についてのものであり、両側に延ばした列の非負時刻の
部分の分布は元の情報源と一致するから、元の情報源についても成り立つ。
:::

::: formalized
`algoet_cover_liminf_bound` (`InformationTheory/Shannon/SMB/AlgoetCover/Liminf.lean`)
:::

::: proof 定理 3.5.2
補題 3.5.5 と補題 3.5.6 より、確率 1 で
$$
H(\mathcal X) \;\le\; \liminf_n \hat H_n \;\le\; \limsup_n \hat H_n \;\le\; H(\mathcal X)
$$
である。したがって極限が存在し、その値は $H(\mathcal X)$ である。
:::

::: formalized
`shannon_mcmillan_breiman` (`InformationTheory/Shannon/SMB/AlgoetCover/Liminf.lean`)、
経験エントロピーにあたる定義 `blockLogAvg`
(`InformationTheory/Shannon/SMB/McMillanBreiman.lean`)
:::

**二つの近似で挟む.** 上からは記憶を $k$ 文字で打ち切った $q_k$ を、下からは無限の過去まで
使った $q_\infty$ を当てた。$q_k$ は真の情報源より予測が下手で（記憶が浅い）、$q_\infty$ は
上手である（$X^n$ の外にある情報まで使う）。真の分布はそのあいだにあり、$k \to \infty$ で
上からの評価が、Lévy の収束で下からの評価が、どちらも $H(\mathcal X)$ に寄ってくる。

**同じ一手が両側で効く.** 上界では $q_k/p$ を、下界では $p/q_\infty$ を補題 3.5.3 に
入れた。使ったのはどちらも「確率分布どうしの比の期待値は 1 を超えない」だけである。
比が多項式ぶんしか増えないことが分かれば、$\frac1n\log$ の尺度ではそれが消える。証明の
仕事は、比の期待値が 1 以下になるように分母と分子を選ぶところに集中している。

**なぜ無限の過去に出ていくのか.** $q_k$ は $X^n$ だけの関数なので、分母に置いて下界にも
使えそうに見える。しかし $p/q_k$ の期待値は 1 で抑えられない——$q_k$ が極端に小さい並びで
比が爆発しうるからである。$q_\infty$ なら、真の分布より情報が多いぶん $p$ を下から
支えるので、比の期待値がちょうど 1 で抑えられる。負の時刻に出ていく理由はここにあり、
両側への拡張はそのためだけに借りている。

## 期待値のレベルでは何が起きているか

::: proposition 3.5.7
定常情報源（エルゴード性は不要）と $n \ge 1$ に対し
$\mathbb E\big[\hat H_n\big] = H_n / n$ である。
:::

::: proof
定義 1.1.1 より
$H_n = H(X^n) = -\sum_{x^n} p(x^n)\log p(x^n) = \mathbb E\big[-\log p(X^n)\big]$
である。両辺を $n$ で割れば、右辺は定義 3.5.1 の $\hat H_n$ の期待値である。
:::

::: formalized
`expected_blockLogAvg_eq` (`InformationTheory/Shannon/SMB/McMillanBreiman.lean`)
:::

命題 3.5.7 は定義を書き直しただけで、定常性すら使っていない。それでも役に立つのは、
定理 3.2.6 と合わせると $\mathbb E[\hat H_n] \to H(\mathcal X)$ が直ちに出るからである。
つまり「平均すれば $H(\mathcal X)$ に近づく」ところまでは、本節の道具を一つも使わずに
言える。定理 3.5.2 が言い足しているのは「1 本 1 本の実現でもそうなる」という一点であり、
Birkhoff の定理も両側への拡張も、その一点のためだけに要る。

## 第2章の符号化定理はどこまで生き延びるか

::: corollary 3.5.8
$|\mathcal X| \ge 2$ とし、エルゴード的な定常情報源に対して定義 2.3.1 のブロック情報源符号を
考える。

1. $R > H(\mathcal X)$ ならば、$R_n \to R$ かつ $P^{(n)}_e \to 0$ を満たす符号の族が存在する。
2. 逆に、符号の族が $P^{(n)}_e \to 0$ を満たし、レートの列 $(R_n)$ が上に有界ならば
   $H(\mathcal X) \le \liminf_{n} R_n$ である。
:::

::: proof
**(1).** 定義 2.2.1 の典型集合を、$H(X)$ を $H(\mathcal X)$ に、$p$ をブロックの確率に
読み替えて同じ式で定める。定理 3.5.2 は概収束を述べているので確率収束も従い、
定理 2.2.3 の証明は定理 2.1.4 の確率収束しか使っていないから、そのまま通る。定理 2.2.4 は
典型集合の定義の書き直しにすぎず、定理 2.2.5 は定理 2.2.3・定理 2.2.4 と「確率の総和が 1」
しか使わない。したがって定理 2.3.2 の符号の構成がそのまま働く。

**(2).** 定理 2.3.4 の証明が i.i.d. を使っているのは、補題 2.3.3 で
$H(X^n) = n\,H(X)$ と書き換える 1 箇所だけである。そこを $H(X^n) = H_n$ と読み替えると
残りはそのまま通って、各 $n$ で
$$
\frac{H_n}{n} \;\le\; R_n + \delta_n, \qquad \delta_n \to 0
$$
を得る。あとは $H_n / n \ge H(\mathcal X)$ を言えばよい。補題 3.2.4 より数列
$\big(H(X_i \mid X^i)\big)_i$ は非増加であり、定理 3.2.6 よりその極限が $H(\mathcal X)$
だから、各項は $H(\mathcal X)$ 以上である。補題 3.2.3 より $H_n/n$ はその相加平均だから、
やはり $H(\mathcal X)$ 以上である。よって $H(\mathcal X) \le R_n + \delta_n$ となり、
下極限をとれば主張を得る。
:::

系 3.5.8 は、情報源符号化定理（定理 2.3.6）が i.i.d. の仮定なしに成り立つ、と言っている。
置き換わったのは 1 文字のエントロピー $H(X)$ がエントロピーレート $H(\mathcal X)$ に
なったところだけで、圧縮の限界を決めているのが「1 文字あたりの不確かさ」であることは
変わらない。

**どこでエルゴード性が要ったか.** 逆定理 (2) の証明はエルゴード性を使っていない——定常で
ありさえすれば $H_n/n \ge H(\mathcal X)$ が言えるからである。エルゴード性が要るのは
達成可能性 (1) のほう、つまり定理 3.5.2 を経由して典型集合を作るところである。例 3.4.2 の
ような非エルゴードな情報源では、実現ごとに別の「典型集合」ができてしまい、1 つの符号で
両方を覆えない。

::: formalization-note
系 3.5.8 に対応する単独の宣言は形式化されていない。エルゴード的な定常情報源に対する典型集合と
ブロック情報源符号は、第2章の i.i.d. 版とは別に立てる必要があり、そこまでは形式化されて
いないためである。本文の証明が第2章の主張を「そのまま通る」と書いているのは紙の上での
議論で、機械検証されているのは定理 3.5.2 までである。
:::

第2章はエントロピーを、分布から計算する量・長い系列が見せる振る舞い・圧縮率の下限、
という三つの顔で捉えた。本章はその三つがそのままエントロピーレートに引き継がれることを
見たことになる。第4章では情報源ではなく通信路——信号を受け取って別の信号を返すもの——に
目を移し、そこを通せる情報の量にも同じように限界があることを見る。
