# 14.3 相関のある情報源の符号化

第2章は情報源を一つ扱った．列を番号に潰す人が一人いて，番号から列を作り直す人が一人いた．本節では情報源が二つあり，しかも二つは相関している．潰す人は二人に分かれていて，互いの見ているものを知らない．作り直す人は一人で，二つの番号をまとめて受け取り，両方の列を復元する．14.1 節が送り手を二人に分けたのと同じ分け方が，こんどは情報源の側に起きている．通信路は出てこない．本節に現れるのは情報源と符号だけである．

二つの情報源を $X$ と $Y$ と書く．二人が相手を見られない以上，それぞれが単独で圧縮するほかないように見える．そうだとすると，第2章 定理 2.3.6 を二つの情報源それぞれに当てて，$1$ 文字あたり合計で $H(X) + H(Y)$ が要ることになる．ところが節の終わりで借りる達成可能性は，合計を $H(X,Y)$ の近くまで下げられると言う．相関のぶんの重なり，すなわち 定理 1.3.4 が $H(X) + H(Y) - H(X,Y)$ と書いた $I(X;Y)$ は，二人が相談しなくても削れるということである．本節はまず下からの評価，つまりどこまでなら下げられないかを三つの形で証明し，そのうえで上からの評価を借りる．

## 分散符号

::: definition 14.3.1 相関情報源の分散符号
$\mathcal X$ と $\mathcal Y$ を空でない有限アルファベット，$(X, Y)$ を $\mathcal X \times \mathcal Y$ に値をとる確率変数の対とし，$M_X \ge 1$，$M_Y \ge 1$ を整数とする．**分散符号** とは，符号化写像 $f_X : \mathcal X \to \{1,\dots,M_X\}$，$f_Y : \mathcal Y \to \{1,\dots,M_Y\}$ と **共同復号器** $d : \{1,\dots,M_X\} \times \{1,\dots,M_Y\} \to \mathcal X \times \mathcal Y$ の組である．復号の結果 $d\big(f_X(X), f_Y(Y)\big)$ の第 $1$ 成分を $\hat X$，第 $2$ 成分を $\hat Y$ と書き，三つの **誤り確率** を
$$
P_e \;:=\; \Pr\big[(\hat X, \hat Y) \ne (X, Y)\big], \qquad
P_{e,X} \;:=\; \Pr\big[\hat X \ne X\big], \qquad
P_{e,Y} \;:=\; \Pr\big[\hat Y \ne Y\big]
$$
で定める．
:::

第2章 定義 2.3.1 のブロック情報源符号を二つの情報源に広げた形だが，広げ方は左右で対称ではない．符号化は二本に分かれる．$f_X$ は $X$ だけを見て番号を出し，$Y$ の値も相手の出した番号も見ない．いっぽう復号は一本のままで，二つの番号から対を一度に言い当てる．分散と呼ぶのはこの符号化の側の分かれ方を指していて，復号の側は分かれていない．誤り確率を三つ置いたのは，対として当てることと成分ごとに当てることが別の要求だからで，以下の三つの下界はそれぞれ別の誤り確率で書かれる．

長さ $n$ のブロックを扱うときは，定義 14.3.1 の $\mathcal X$ と $\mathcal Y$ に $\mathcal X^n$ と $\mathcal Y^n$ を，対 $(X,Y)$ に $(X^n, Y^n)$ を置いて読む．そのときレートは $\frac1n\log M_X$ と $\frac1n\log M_Y$ になる．定義 14.3.1 自体はアルファベットに何の構造も求めないので，この読み替えに断りは要らない．

::: formalization-note
形式化には符号の三つの写像を束ねた構造体が無く，逆定理の宣言は符号化写像二つと共同復号器を別々の引数として受け取る．誤り確率のほうは二か所にある．全体の誤り確率を長さ $n$ のブロックについて書いた `swErrorProb` (`InformationTheory/Shannon/SlepianWolf/Achievability.lean`) と，逆定理の宣言が使う一般の有限アルファベットについての `errorProb` (`InformationTheory/Fano/Measure.lean`) で，前者のアルファベットを $\mathcal X^n$ と $\mathcal Y^n$ にとれば二つは同じものを測るが，単独の宣言としては別である．
:::

::: example 14.3.2 完全に相関した対
$\mathcal X = \mathcal Y = \{0,1\}$ とし，$X$ を $\mathcal X$ 上の一様分布に従う確率変数，$Y := X$ とする．$M_X := 2$，$M_Y := 1$ とし，$f_X(0) := 1$，$f_X(1) := 2$，すべての $y$ について $f_Y(y) := 1$，$d(1,1) := (0,0)$，$d(2,1) := (1,1)$ と定める．この組は 定義 14.3.1 の分散符号であり，三つの誤り確率はどれも $0$ である．また $\log M_X = 1$，$\log M_Y = 0$ であり，$H(X\mid Y) = 0$，$H(Y\mid X) = 0$，$H(X,Y) = 1$ である．
:::

::: proof
三つの写像はどれも 定義 14.3.1 が求める形をしている．$X = 0$ のときは $f_X(X) = 1$ かつ $f_Y(Y) = 1$ で $d(1,1) = (0,0) = (X,Y)$ であり，$X = 1$ のときは $f_X(X) = 2$ で $d(2,1) = (1,1) = (X,Y)$ である．どちらの場合も対として当たっているから，成分ごとにも当たっており，三つの誤り確率はどれも $0$ である．$M_X = 2$ と $M_Y = 1$ から $\log M_X = 1$ と $\log M_Y = 0$ を得る．

エントロピーを計算する．$Y = X$ だから $Y$ の値が分かれば $X$ の値が決まり，定義 1.2.2 の読み方により $H(X\mid Y) = 0$ である．同じ理由で $H(Y\mid X) = 0$ である．対 $(X,Y)$ については，定理 1.2.3 のチェイン則 $H(X,Y) = H(X) + H(Y\mid X)$ と $H(Y\mid X) = 0$ から $H(X,Y) = H(X)$ であり，$X$ は $2$ 点上の一様分布だから 例 1.1.3 より $H(X) = \log 2 = 1$ である．
:::

$Y$ の側は符号語を一通りしか持たない，つまり何も送っていないのに，復号器は $Y$ の列まで復元している．$Y$ が $X$ で決まってしまうので，$X$ の側さえ送れば足りるからである．相関が極端な場合ではあるが，相手を見られない二人が合計で $H(X) + H(Y) = 2$ ではなく $1$ しか使っていない，という本節の筋はここにそのまま出ている．

## 三つの下界

これから三つの下界を示す．どれもファノの不等式（定理 1.10.1）を使うが，観測の位置に置くのは一つの確率変数ではなく **対** である．定義 1.2.2 が断ったとおり，条件が複数あるときは対を一つの変数とみなして読めばよいので，定理 1.10.1 が観測に置いている変数にその対を，観測のとる値の集合にその対のとる値の集合を置けば，そのまま当たる．どの対を置くかが三つで違い，それが三つの下界の違いを生む．

::: theorem 14.3.3 分散符号の逆定理・$X$ 側
$\mathcal X$ と $\mathcal Y$ を空でない有限アルファベットとし，$\lvert\mathcal X\rvert \ge 2$ とする．$(X,Y)$ を $\mathcal X\times\mathcal Y$ に値をとる確率変数の対，$(M_X, M_Y, f_X, f_Y, d)$ を 定義 14.3.1 の分散符号，$P_{e,X}$ をその $X$ 側の誤り確率とすると
$$
\log M_X \;\ge\; H(X \mid Y) - H_b\big(P_{e,X}\big) - P_{e,X}\log\big(\lvert\mathcal X\rvert - 1\big)
$$
である（$H_b$ は 例 1.1.2 の二値エントロピー関数）．
:::

::: proof
$\hat X$ を 定義 14.3.1 のとおり $d(f_X(X), f_Y(Y))$ の第 $1$ 成分とする．

$\hat X$ が対 $(Y, f_X(X))$ の写像で書けることをまず見る．$g : \mathcal Y \times \{1,\dots,M_X\} \to \mathcal X$ を $g(y, m) := \big(d(m, f_Y(y))\big)_1$（第 $1$ 成分）で定めると，$g\big(Y, f_X(X)\big) = \big(d(f_X(X), f_Y(Y))\big)_1 = \hat X$ である．この写像の誤り確率 $\Pr[\hat X \ne X]$ は 定義 14.3.1 の $P_{e,X}$ にほかならない．そこでファノの不等式（定理 1.10.1）を，観測に対 $(Y, f_X(X))$ を，復号器に $g$ を置いて当てる．$\lvert\mathcal X\rvert \ge 2$ だから
$$
H\big(X \,\big|\, Y, f_X(X)\big) \;\le\; H_b\big(P_{e,X}\big) + P_{e,X}\log\big(\lvert\mathcal X\rvert - 1\big)
$$
を得る．

次に，$Y$ を知っている人にとって番号 $f_X(X)$ が $X$ について持つ情報が $\log M_X$ を超えないことを見る．定理 1.4.3 を，その $Z$ に $f_X(X)$ を置いて当てると
$$
I\big(X; f_X(X) \,\big|\, Y\big) \;=\; H(X\mid Y) - H\big(X \,\big|\, Y, f_X(X)\big)
$$
である．いっぽう 命題 1.4.2 の対称性より $I(X; f_X(X)\mid Y) = I(f_X(X); X\mid Y)$ であり，定理 1.4.3 をこちらの向きに読むと
$$
I\big(f_X(X); X \,\big|\, Y\big) \;=\; H\big(f_X(X)\mid Y\big) - H\big(f_X(X) \,\big|\, Y, X\big)
$$
となる．右辺の第 $2$ 項は条件付きエントロピーだから非負であり（定義 1.2.2 と 命題 1.1.4），$I(X;f_X(X)\mid Y) \le H(f_X(X)\mid Y)$ である．さらに 定理 1.2.4 の基本形より $H(f_X(X)\mid Y) \le H(f_X(X))$ であり，$f_X(X)$ のとりうる値は $M_X$ 個だから 定理 1.1.5 より $H(f_X(X)) \le \log M_X$ である．

二つを合わせる．定理 1.4.3 から出した等式を移項すると $H(X\mid Y) = I(X; f_X(X)\mid Y) + H(X \mid Y, f_X(X))$ であり，右辺の第 $1$ 項にいま見た $\log M_X$ の上界を，第 $2$ 項にファノの不等式から出した上界を当てて
$$
H(X\mid Y)
  \;\le\; \log M_X + H_b\big(P_{e,X}\big) + P_{e,X}\log\big(\lvert\mathcal X\rvert - 1\big)
$$
であり，移項すれば主張を得る．
:::

::: formalized
`slepian_wolf_converse_X` (`InformationTheory/Shannon/SlepianWolf/Basic.lean`)
:::

::: theorem 14.3.4 分散符号の逆定理・$Y$ 側
$\mathcal X$ と $\mathcal Y$ を空でない有限アルファベットとし，$\lvert\mathcal Y\rvert \ge 2$ とする．$(X,Y)$ を $\mathcal X\times\mathcal Y$ に値をとる確率変数の対，$(M_X, M_Y, f_X, f_Y, d)$ を 定義 14.3.1 の分散符号，$P_{e,Y}$ をその $Y$ 側の誤り確率とすると
$$
\log M_Y \;\ge\; H(Y \mid X) - H_b\big(P_{e,Y}\big) - P_{e,Y}\log\big(\lvert\mathcal Y\rvert - 1\big)
$$
である．
:::

::: proof
定理 14.3.3 の証明で，$X$ と $Y$，$\mathcal X$ と $\mathcal Y$，$f_X$ と $f_Y$，$M_X$ と $M_Y$ の役をそれぞれ入れ替え，復号の結果の第 $1$ 成分をとるところを第 $2$ 成分に替えればよい．すなわち $h : \mathcal X \times \{1,\dots,M_Y\} \to \mathcal Y$ を $h(x, m) := \big(d(f_X(x), m)\big)_2$ で定めると $h\big(X, f_Y(Y)\big) = \hat Y$ であり，その誤り確率は 定義 14.3.1 の $P_{e,Y}$ である．以下の運びは 定理 14.3.3 の証明と同じで，ファノの不等式を当てるときに条件に置く対が $(X, f_Y(Y))$ に，最大エントロピー上界を当てる相手が $f_Y(Y)$ に替わるだけである．
:::

::: formalized
`slepian_wolf_converse_Y` (`InformationTheory/Shannon/SlepianWolf/Basic.lean`)
:::

::: theorem 14.3.5 分散符号の逆定理・和レート
$\mathcal X$ と $\mathcal Y$ を空でない有限アルファベットとし，$\lvert\mathcal X \times \mathcal Y\rvert \ge 2$ とする．$(X,Y)$ を $\mathcal X\times\mathcal Y$ に値をとる確率変数の対，$(M_X, M_Y, f_X, f_Y, d)$ を 定義 14.3.1 の分散符号，$P_e$ をその全体の誤り確率とすると
$$
\log M_X + \log M_Y \;\ge\; H(X, Y) - H_b\big(P_e\big)
  - P_e \log\big(\lvert\mathcal X\times\mathcal Y\rvert - 1\big)
$$
である．
:::

::: proof
対 $(X,Y)$ を $\mathcal X\times\mathcal Y$ に値をとる一つの確率変数とみなし，対 $(f_X(X), f_Y(Y))$ を $\{1,\dots,M_X\}\times\{1,\dots,M_Y\}$ に値をとる一つの確率変数とみなす．共同復号器 $d$ は後者から前者の推定を作る写像であり，その誤り確率は 定義 14.3.1 の $P_e$ である．$\lvert\mathcal X\times\mathcal Y\rvert \ge 2$ だから，ファノの不等式（定理 1.10.1）を，当てる対象に $(X,Y)$ を，観測に $(f_X(X), f_Y(Y))$ を，復号器に $d$ を置いて当てると
$$
H\big((X,Y) \,\big|\, f_X(X), f_Y(Y)\big)
  \;\le\; H_b\big(P_e\big) + P_e\log\big(\lvert\mathcal X\times\mathcal Y\rvert - 1\big)
$$
を得る．

番号の対が運べる情報を抑える．定理 1.3.4 のエントロピー表現を二つの対に当てると
$$
I\big((X,Y); (f_X(X), f_Y(Y))\big) \;=\; H(X,Y) - H\big((X,Y) \,\big|\, f_X(X), f_Y(Y)\big)
$$
である．同じ 定理 1.3.4 を逆向きに読むと，右辺の相互情報量は $H(f_X(X), f_Y(Y)) - H(f_X(X), f_Y(Y) \mid X, Y)$ に等しく，第 $2$ 項は条件付きエントロピーだから非負である（定義 1.2.2 と 命題 1.1.4）．よって
$$
I\big((X,Y); (f_X(X), f_Y(Y))\big) \;\le\; H\big(f_X(X), f_Y(Y)\big)
$$
であり，番号の対のとりうる値は高々 $M_X M_Y$ 個だから 定理 1.1.5 より右辺は $\log(M_X M_Y) = \log M_X + \log M_Y$ 以下である．

二つを合わせると $H(X,Y) \le \log M_X + \log M_Y + H_b(P_e) + P_e\log(\lvert\mathcal X\times\mathcal Y\rvert - 1)$ であり，移項すれば主張を得る．
:::

::: formalized
`slepian_wolf_converse_sum` (`InformationTheory/Shannon/SlepianWolf/Basic.lean`)
:::

三つの下界は別のことを言っている．定理 14.3.3 の右辺にある $H(X\mid Y)$ は，$Y$ をまるごと渡されている受け手にとってさえ $X$ に残る不確かさである．$X$ の側のレートはそこより下げられない，ただし誤りを許すぶんだけの余裕が右辺の補正項として付く，と読める．相手の情報源を知っている人を相手にするのだからいちばん甘い要求で，それでも $0$ にはならない．定理 14.3.5 の $H(X,Y)$ は逆に，二人が示し合わせて一人のように潰したとしても番号の総数はこれだけ要る，という要求である．14.1 節の五角形が，片方の利用者だけについての枠と二人を合わせた枠の二種類を持っていたのと，読み方の構造がそのまま対応している．違うのは向きで，あちらは上界，こちらは下界である．

例 14.3.2 の符号で三つを確かめておく．誤り確率がどれも $0$ で，例 1.1.2 より $H_b(0) = 0$ だから，補正項はすべて消える．三つの下界はそれぞれ $\log M_X \ge 0$，$\log M_Y \ge 0$，$\log M_X + \log M_Y \ge 1$ になり，実際の値 $1$，$0$，$1$ と比べると，二つめと三つめは等号で成り立っている．一つめだけは余裕があり，$X$ の側は下界より $1$ だけ多く送っている．

## 長さを伸ばす

三つの下界は長さ $1$ の符号にも長さ $n$ のブロックにも当たるが，右辺の $H$ はブロック全体についてのエントロピーである．情報源が i.i.d. なら，それは $1$ 文字あたりの量の $n$ 倍になり，$n$ で割った形，つまりレートについての下界に直せる．

::: corollary 14.3.6 レートの下界
$\mathcal X$ と $\mathcal Y$ を空でない有限アルファベットで $\lvert\mathcal X\rvert \ge 2$ かつ $\lvert\mathcal Y\rvert \ge 2$ を満たすものとし，$\big((X_i, Y_i)\big)_{i \ge 0}$ を，$\mathcal X\times\mathcal Y$ に値をとる互いに独立で同分布な確率変数の対の列とする．$X^n := (X_0,\dots,X_{n-1})$，$Y^n := (Y_0,\dots,Y_{n-1})$ と書き，各 $n \ge 1$ について $(M_{X,n}, M_{Y,n}, f_{X,n}, f_{Y,n}, d_n)$ を，定義 14.3.1 を $\mathcal X^n$，$\mathcal Y^n$ と対 $(X^n, Y^n)$ に当てた分散符号とし，その全体の誤り確率を $P_{e,n}$ と書く．$P_{e,n} \to 0$ ならば
$$
\liminf_{n\to\infty} \frac1n \log M_{X,n} \;\ge\; H(X_0\mid Y_0), \qquad
\liminf_{n\to\infty} \frac1n \log M_{Y,n} \;\ge\; H(Y_0\mid X_0),
$$
$$
\liminf_{n\to\infty} \frac1n \big(\log M_{X,n} + \log M_{Y,n}\big) \;\ge\; H(X_0, Y_0)
$$
である．
:::

::: proof
第 $1$ の主張を詳しく書き，残りの二つは違うところだけを言う．

三つの誤り確率の関係をまず押さえる．$n$ 番目の符号の $X$ 側と $Y$ 側の誤り確率（定義 14.3.1）を $P_{e,X,n}$，$P_{e,Y,n}$ と書く．復号の結果が対として当たっていれば成分ごとにも当たっているから，どの $n$ でも $P_{e,X,n} \le P_{e,n}$ かつ $P_{e,Y,n} \le P_{e,n}$ である．よって $P_{e,n} \to 0$ から $P_{e,X,n} \to 0$ と $P_{e,Y,n} \to 0$ も従う．

$n \ge 1$ を一つとる．$\lvert\mathcal X^n\rvert = \lvert\mathcal X\rvert^n \ge 2$ だから 定理 14.3.3 が当たり
$$
\log M_{X,n} \;\ge\; H\big(X^n \mid Y^n\big) - H_b\big(P_{e,X,n}\big)
  - P_{e,X,n}\log\big(\lvert\mathcal X\rvert^n - 1\big)
$$
である．

右辺の主要項が $n$ 倍になることを見る．定理 1.2.3 のチェイン則より $H(X^n\mid Y^n) = H(X^n, Y^n) - H(Y^n)$ である．対の列 $\big((X_i,Y_i)\big)$ は $\mathcal X\times\mathcal Y$ 上の i.i.d. 情報源だから，補題 2.3.3 をこの情報源に当てて $H(X^n, Y^n) = n\,H(X_0, Y_0)$ を得る．成分の列 $(Y_i)$ も i.i.d. だから，同じ補題より $H(Y^n) = n\,H(Y_0)$ である．ふたたび 定理 1.2.3 より $H(X_0,Y_0) - H(Y_0) = H(X_0\mid Y_0)$ だから，$H(X^n\mid Y^n) = n\,H(X_0\mid Y_0)$ である．

補正項が消えることを見る．$\Lambda_n := \frac1n\log(\lvert\mathcal X\rvert^n - 1)$ とおく．$\lvert\mathcal X\rvert^n \ge 2$ より $\lvert\mathcal X\rvert^n - 1 \ge 1$ だから $\Lambda_n \ge 0$ であり，$\lvert\mathcal X\rvert^n - 1 \le \lvert\mathcal X\rvert^n$ だから $\Lambda_n \le \log\lvert\mathcal X\rvert$ で，列 $(\Lambda_n)$ は上に有界である．$P_{e,X,n} \to 0$ と合わせて 補題 6.4.7 を当てると
$$
\frac{H_b\big(P_{e,X,n}\big)}{n} + P_{e,X,n}\,\Lambda_n \;\longrightarrow\; 0
$$
である．

極限に移る．上の不等式を $n$ で割ると
$$
\frac1n\log M_{X,n} \;\ge\; H(X_0\mid Y_0)
  - \left( \frac{H_b\big(P_{e,X,n}\big)}{n} + P_{e,X,n}\,\Lambda_n \right)
$$
であり，右辺は $H(X_0\mid Y_0)$ に収束する．左辺はどの $n$ でも右辺以上だから，左辺の下極限は右辺の極限以上であり，第 $1$ の主張を得る．

第 $2$ の主張は，$X$ と $Y$ の役を入れ替えて 定理 14.3.4 を当てれば同じ運びである（ここで $\lvert\mathcal Y\rvert \ge 2$ を使う）．第 $3$ の主張は 定理 14.3.5 を当てる．$\lvert\mathcal X^n\times\mathcal Y^n\rvert = (\lvert\mathcal X\rvert\,\lvert\mathcal Y\rvert)^n \ge 2$ であり，主要項は 補題 2.3.3 より $H(X^n,Y^n) = n\,H(X_0,Y_0)$ で，補正項は $\Lambda'_n := \frac1n\log\big((\lvert\mathcal X\rvert\,\lvert\mathcal Y\rvert)^n - 1\big)$ が $0$ 以上 $\log(\lvert\mathcal X\rvert\,\lvert\mathcal Y\rvert)$ 以下であることと $P_{e,n} \to 0$ から，同じく 補題 6.4.7 で消える．
:::

::: formalization-note
系 14.3.6 に対応する単独の宣言はない．定理 14.3.3・定理 14.3.4・定理 14.3.5 に紐付けた三つの宣言と，i.i.d. 情報源についての 補題 2.3.3 に紐付けた `entropy_jointRV_eq_n_smul` (`InformationTheory/Shannon/AEP/Basic/Converse.lean`) を対の列と成分の列に当てたもの，および 定理 1.2.3 に紐付けた `entropy_pair_eq_entropy_add_condEntropy` (`InformationTheory/Shannon/Entropy.lean`) の合成で得られる．レートの下極限をブロックのエントロピーと結ぶ宣言も，誤り確率が $0$ に向かう符号の族について述べる宣言も，分散符号の側には置かれていない．
:::

## 達成可能性

道具を一つ借りる．**Slepian–Wolf の達成可能性**，すなわち「三つの下界が真に満たされているレートの対は実際に達成できる」という主張である．使う形を書いておく．

$\mathcal X$ と $\mathcal Y$ を空でない有限アルファベットとし，$\big((X_i, Y_i)\big)_{i\ge0}$ を $\mathcal X\times\mathcal Y$ に値をとる確率変数の対の列とする．列 $(X_i)$，列 $(Y_i)$，対の列 $\big((X_i,Y_i)\big)$ のどれもが互いに独立で同分布であるとし，さらに $X_0$ の分布，$Y_0$ の分布，対 $(X_0,Y_0)$ の分布がどれも全点で正であるとする．実数 $R_X$，$R_Y$ が
$$
H(X_0\mid Y_0) < R_X, \qquad H(Y_0\mid X_0) < R_Y, \qquad H(X_0,Y_0) < R_X + R_Y
$$
を満たすならば，各 $n \ge 1$ について 定義 14.3.1 を $\mathcal X^n$，$\mathcal Y^n$ と対 $(X^n, Y^n)$ に当てた分散符号 $(M_{X,n}, M_{Y,n}, f_{X,n}, f_{Y,n}, d_n)$ がとれて，$\frac1n\log M_{X,n} \to R_X$ かつ $\frac1n\log M_{Y,n} \to R_Y$ であり，全体の誤り確率が $0$ に収束する．

当てる対象は 定義 14.3.1 の分散符号だけである．これに依存するのは二箇所で，一つは本節の終わりの地の文，そこが二つの評価を突き合わせる．もう一つは 14.4 節が借りる「副情報つきレート歪みの達成可能性」の筋書きで，そこがこの名前で引く．後者はビニングという作り方を引き合いに出すだけで，主張そのものを当てるわけではない．

借りたままにするので，中で何が起きているかの筋書きだけ書いておく．くじで引くのは符号語ではなく **割り振り** である．$\mathcal X^n$ の系列それぞれに $\{1,\dots,M_{X,n}\}$ の番号を一様に独立に割り当て，$\mathcal Y^n$ の側も同じように $\{1,\dots,M_{Y,n}\}$ の番号を割り当てる．符号化はその割り当てを引くだけで，系列の中身を見ない．復号器は，受け取った二つの番号に割り当てられている系列の組のうち，結合典型（定義 6.2.3 の同時分布を対 $(X,Y)$ のものに取り替えたもの）である組がちょうど一つならそれを答え，そうでなければ誤る．この作り方を **ランダムビニング**（random binning）と呼ぶ．誤りの起こり方は 14.1 節で借りた **多元接続通信路の達成可能性** と同じく三種類に分かれ，$X$ の側だけが紛れ込む，$Y$ の側だけが紛れ込む，両方が紛れ込む，の三つである．同じ番号に落ちる確率がそれぞれ $1/M_{X,n}$，$1/M_{Y,n}$，その積なので，紛れ込みうる系列の本数を数えて掛けたものが $0$ に向かう条件が，三つの不等式そのものになる．

本書はこの主張を証明しない．三種の紛れ込みのうち両方が紛れる場合は，紛れ込みうる組の本数が結合典型な組の全体で抑えられるので，定理 6.2.5 にあたる評価で足りる．ところが $X$ の側だけが紛れる場合に数えるのは，$y^n$ を一つ固定したときにそれと結合典型になる $x^n$ の本数であり，これは結合典型集合の全体ではなくその切り口である．本書はこの切り口の個数を抑える評価を持っていない．本節が借りた主張は，本書が証明を載せないだけで，無条件の機械検証済みの定理として形式化されている．

::: formalized
`slepian_wolf_full_rate_region_achievability` (`InformationTheory/Shannon/SlepianWolf/FullRateRegion/PairBound.lean`)
:::

::: formalization-note
形式化の宣言の仮定は，借りた主張の仮定と一つずつ対応している．三つの列が独立であることと同分布であること，三つの分布が全点で正であること，三つの不等式の，これがすべてである．結論の誤り確率は，定義 14.3.1 に付した注記で触れた `swErrorProb` で測っている．
:::

借りた **Slepian–Wolf の達成可能性** が覆うのは，三つの不等式が **真に** 成り立つ側である．いっぽう 系 14.3.6 が禁じるのは，同じ三つの不等式が逆向きに破れる側である．境界，すなわち三つのどれかが等号で成り立つレートの対については，どちらも何も言っていない．そして本書は，**達成できるレートの対の集合が三つの不等式の定める領域に一致する**，という形の主張を述べない．理由は二つある．一つは，Slepian–Wolf の達成可能性と 系 14.3.6 とで「達成できる」の定め方が違うことで，前者はレートが収束する符号の族を作り，後者は各 $n$ の符号を一つずつ受け取る．二つをそろえるには，定義 14.1.3 のように達成可能性を一つの形に決め，定義 14.2.1 のように境界を閉包で拾う段が要る．もう一つは，領域としての一致を述べる宣言が形式化の側にも無いことである．本節が保証できるのは，三つの不等式のそれぞれについての片側ずつまでである．
