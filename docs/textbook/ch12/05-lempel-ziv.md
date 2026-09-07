# 12.5 Lempel–Ziv 符号

ここまでの符号は，どれも 定義 12.1.1 の枠組みの中にあった．分布の族が与えられていて，そのどれが真かだけが分からない，という設定である．冗長度もミニマックス冗長度も，その族に対して定めた量だった．本節はその枠組みを離れる．情報源の分布を持ち出さず，手元にある一本の系列だけを見て符号を作る．手がかりにするのは，系列の中で同じ並びが繰り返し現れることである．同じ並びが何度も出てくるなら，二度目からはその並びを指し示すだけで済む．どこがどう繰り返しているかは，分布を知らなくても系列そのものから読み取れる．

作り方はこうである．系列を先頭から読み，これまでに切り出した断片のどれとも違う並びが現れたところで区切り，その断片を辞書に加える．次からは辞書にある断片を足がかりにできるので，同じ並びが何度も出てくる系列では，断片がだんだん長くなり，本数が減っていく．断片の本数が減れば，それを書き並べるビット数も減る．これが 1978 年に提案された方式（LZ78 と呼ばれる）で，本書では **Lempel–Ziv 符号** と呼ぶ．本節は分解の性質を三つ（フレーズが相異なること，長さの総和，本数の上界）押さえ，そこから符号長を定めて評価する．

道具を一つ借りる．実数 $t$ に対し，$t$ 以下の最大の整数を $\lfloor t \rfloor$ と書き，床関数と呼ぶ．床関数について $\lfloor t \rfloor \le t < \lfloor t \rfloor + 1$ が成り立つこと，および $s \le t$ ならば $\lfloor s \rfloor \le \lfloor t \rfloor$ であることを既知とする．当てる相手は，補題 12.5.6 の証明で対数の値を整数に切り下げるところ，定義 12.5.9 の符号長，そして 定理 12.5.10 の証明で二つの床関数の値を比べるところである．このうち $\lfloor t \rfloor \le t < \lfloor t \rfloor + 1$ は，第11章 11.3 節が証明の準備として一度置いている．そこでは番号の付いた主張の形になっておらず，引く先にできないので，本節であらためて宣言する．この宣言に依存するのは本節だけである（12.6 節には $\lfloor\cdot\rfloor$ を含む式が現れるが，床関数の性質そのものは使わない）．

## 系列を分解する

::: definition 12.5.1 最長一致の貪欲な分解
$\mathcal X$ を空でない有限アルファベット，$x$ を $\mathcal X$ の文字を並べた有限列とする．**辞書** を空の並び，**区切り候補** を空列として始め，$x$ の文字を先頭から $1$ つずつ読む．読んだ文字を区切り候補の末尾に足した列を $w$ とし，$w$ が辞書にあれば区切り候補を $w$ に置き換え，$w$ が辞書になければ $w$ を **フレーズ** として出力したうえで辞書の末尾に加え，区切り候補を空列に戻す．$x$ を読み終えた時点で区切り候補に残っているものは出力しない．出力されたフレーズを出力順に並べた列を $\mathcal S(x) = (s_1, \dots, s_k)$ と書き，その項数 $k$ を $\lvert\mathcal S(x)\rvert$ と書く．$\mathcal S(x)$ を $x$ の **最長一致の貪欲な分解** と呼ぶ．
:::

::: formalized
`lz78PhraseStrings` (`InformationTheory/Shannon/LZ78/GreedyLongestPrefix.lean`)
:::

定義 12.5.1 の分岐をそのまま読むと，区切り候補は辞書にある列である限り伸び続け，辞書から外れた瞬間に区切られる．すなわち区切り候補は，つねに空列であるか辞書にある列であるかのどちらかで，出力されるフレーズは「辞書にある列（または空列）に $1$ 文字足したもの」である．最長一致という名前は，区切る前に候補をできるところまで伸ばす，というこの動きから来ている．読み終えたところで候補に残った切れ端を出力しないので，フレーズを全部つないでも $x$ に届かないことがある．そのぶんが 命題 12.5.4 の「以下」である．ただし，この切れ端も空列であるか辞書にある列であるかのどちらかだから，フレーズの並びに加えて，切れ端が辞書の何番目かを最後にもう一つ書き添えれば，$x$ 全体が読み取れる．書き添えないと $x$ は決まらない．たとえば $x = 10$ と $x = 101$ は，どちらも分解が $(1, 0)$ で，違いは切れ端が空列か $1$ かというところにしかないからである．

::: example 12.5.2 $13$ 文字の二値系列
$\mathcal X = \{0, 1\}$，$x = 1011010100010$（長さ $13$）とすると
$$
\mathcal S(x) \;=\; (1,\; 0,\; 11,\; 01,\; 010,\; 00,\; 10)
$$
であり，$\lvert\mathcal S(x)\rvert = 7$，フレーズの長さの総和は $13$ である．
:::

::: proof
定義 12.5.1 の手続きを追う．辞書は空，候補は空列から始まる．第 $1$ の文字 $1$ で $w = 1$ となり，辞書は空だから $1$ を出力して辞書に加える．第 $2$ の文字 $0$ で $w = 0$ となり，辞書には $1$ しかないから $0$ を出力して加える．第 $3$ の文字 $1$ で $w = 1$ となり，これは辞書にあるから候補が $1$ になる．第 $4$ の文字 $1$ で $w = 11$ となり，辞書に無いから $11$ を出力して加え，候補を空に戻す．以下同様に，第 $5$・第 $6$ の文字 $0, 1$ で $01$ を，第 $7$ から第 $9$ の文字 $0, 1, 0$ で $010$ を（$0$ も $01$ も辞書にあるので候補が二度伸びる），第 $10$・第 $11$ の文字 $0, 0$ で $00$ を，第 $12$・第 $13$ の文字 $1, 0$ で $10$ を出力する．出力は $7$ 本で，読み終えた時点の候補は空列だから，長さの総和は $x$ の長さ $13$ に等しい．
:::

::: formalization-note
具体的な系列を入れて分解を計算した宣言は無い．定義 12.5.1 の形式化 `lz78PhraseStrings` (`InformationTheory/Shannon/LZ78/GreedyLongestPrefix.lean`) は，辞書と候補を引数にとる補助関数の再帰としてそのまま計算できる形で書かれている．
:::

例 12.5.2 では，$7$ 本のフレーズのうち $5$ 本が $2$ 文字以上である．辞書が育つほど候補が長く伸びられるようになる，というのが 定義 12.5.1 の仕掛けである．逆に，どのフレーズも短いままなら，長さの総和が同じでも本数が増える．本数と長さのこのやりとりが，次の三つの命題で押さえる分解の性質であり，符号長の評価をそのまま決める．

## 分解の性質

::: proposition 12.5.3
$\mathcal X$ を空でない有限アルファベット，$x$ を $\mathcal X$ の文字を並べた有限列とすると，$\mathcal S(x)$（定義 12.5.1）のフレーズはどの二つも相異なる．
:::

::: proof 読んだ文字数についての数学的帰納法
「辞書は，そこまでに出力したフレーズを出力順に並べたものに一致する」という不変量を示す．$0$ 文字読んだ時点では辞書も出力も空であり，定義 12.5.1 の二つの分岐のどちらでも保たれる（第 $1$ の分岐は辞書も出力も変えず，第 $2$ の分岐は同じ列 $w$ を両方の末尾に同時に加える）．

フレーズが出力されるのは $w$ が辞書に無いときだけで，そのとき辞書はそれまでに出力したフレーズの全体だから，出力されるフレーズはそれ以前のどのフレーズとも異なる．出力の順に見れば，どの二つのフレーズも相異なる．
:::

::: formalized
`lz78PhraseStrings_nodup` (`InformationTheory/Shannon/LZ78/GreedyLongestPrefix.lean`)
:::

::: proposition 12.5.4
$\mathcal X$ を空でない有限アルファベット，$x$ を $\mathcal X$ の文字を並べた有限列とする．$\mathcal S(x)$（定義 12.5.1）のフレーズはどれも空列でなく，それらを出力順に連結した列は $x$ の語頭（定義 4.1.2）であり，フレーズの長さの総和は $x$ の長さ以下である．
:::

::: proof 読んだ文字数についての数学的帰納法
フレーズが空列でないことは，出力されるのが区切り候補に読んだ文字を $1$ つ足した列だからである．

残りの二つには，「そこまでに出力したフレーズを出力順に連結した列に，その時点の区切り候補をつないだものは，そこまでに読んだ文字を順に並べた列に等しい」という不変量を立てる．$0$ 文字読んだ時点では三つとも空列であり，読んだ文字を $a$ とすると，定義 12.5.1 の二つの分岐のどちらでも保たれる（第 $1$ の分岐は候補の末尾に $a$ を足し，第 $2$ の分岐は候補に $a$ を足した列を出力へ移して候補を空列に戻すので，どちらもつないだ列の末尾に $a$ を足す）．

$x$ を読み終えた時点で不変量を読むと，フレーズを連結した列に最後の区切り候補をつないだものが $x$ に等しい．よって連結した列は $x$ の語頭であり，その長さ，すなわちフレーズの長さの総和は $x$ の長さ以下である．
:::

::: formalized
`lz78PhraseStrings_forall_ne_nil`，`lz78PhraseStrings_flatten_prefix`，`lz78PhraseStrings_total_length_le` (`InformationTheory/Shannon/LZ78/GreedyLongestPrefix.lean`)
:::

::: corollary 12.5.5
$\mathcal X$ を空でない有限アルファベット，$x$ を $\mathcal X$ の文字を並べた長さ $n$ の有限列とすると $\lvert\mathcal S(x)\rvert \le n$ である（$\mathcal S(x)$ は 定義 12.5.1 の貪欲な分解）．
:::

::: proof
命題 12.5.4 よりフレーズはどれも空列でないから，長さはどれも $1$ 以上であり，本数は長さの総和以下である．同じ命題より長さの総和は $n$ 以下だから，本数も $n$ 以下である．
:::

::: formalized
`lz78PhraseStrings_count_le` (`InformationTheory/Shannon/LZ78/GreedyLongestPrefix.lean`)
:::

系 12.5.5 の評価は，どのフレーズも $1$ 文字のままだった場合，つまり分解が何も学ばなかった場合のものである．命題 12.5.4 より長さの総和は $n$ を超えないから，フレーズが長くなればそのぶん本数は減る．次はその減り方を，系列の中身によらない形で押さえる．効くのは 命題 12.5.3 の「相異なる」だけで，どんな並びであろうと，相異なる列を何本もそろえるには文字数が要る，という一点である．

## フレーズは何本まで作れるか

::: lemma 12.5.6 相異なる列の詰め込み
$\mathcal X$ を空でない有限アルファベット，$k \ge 1$ とし，$s_1, \dots, s_k$ を $\mathcal X$ の文字を並べた空でない有限列で，どの二つも相異なるものとすると
$$
k\log_2 k \;\le\; 3\log_2\big(\lvert\mathcal X\rvert + 1\big)\sum_{j=1}^{k}\lvert s_j\rvert
$$
である．
:::

::: proof
$T := \sum_{j=1}^{k}\lvert s_j\rvert$ と置く．$\mathcal X$ は空でないから $\lvert\mathcal X\rvert + 1 \ge 2$ であり，$\log_2(\lvert\mathcal X\rvert+1) \ge 1$ である．また各 $\lvert s_j\rvert$ は $1$ 以上だから $k \le T$ である．$k = 1$ のときは左辺が $0$ で右辺は $0$ 以上だから，以下 $k \ge 2$ とする．

まず詰め込みを数える．$m$ を $0$ 以上の整数とすると，$\mathcal X$ の文字を並べた長さ $m$ 以下の列は高々 $(\lvert\mathcal X\rvert+1)^m$ 本しかない．実際，$\mathcal X$ に属さない記号 $\ast$ を一つ用意し，長さ $m$ 以下の列に，末尾に $\ast$ を足して長さちょうど $m$ にそろえた組を対応させる．もとの列に $\ast$ は現れないから，組の最初の $\ast$ の手前までを読めばもとの列が復元でき，この対応は単射である．行き先は $\mathcal X$ に $\ast$ を足した $\lvert\mathcal X\rvert+1$ 個の記号を $m$ 個並べた組の全体で，その個数は $(\lvert\mathcal X\rvert+1)^m$ である．

次に長さで分ける．
$$
m_0 \;:=\; \Big\lfloor \frac{\log_2(k/2)}{\log_2(\lvert\mathcal X\rvert+1)} \Big\rfloor
$$
と置く．$k \ge 2$ より $\log_2(k/2) \ge 0$ だから $m_0$ は $0$ 以上の整数であり，床関数の性質と $\log_2(\lvert\mathcal X\rvert+1) > 0$ から $m_0\log_2(\lvert\mathcal X\rvert+1) \le \log_2(k/2)$，すなわち $(\lvert\mathcal X\rvert+1)^{m_0} \le k/2$ である．前段より長さ $m_0$ 以下の $s_j$ は高々 $(\lvert\mathcal X\rvert+1)^{m_0}$ 本，すなわち $k/2$ 本以下だから，長さ $m_0+1$ 以上の $s_j$ が $k/2$ 本以上ある．長さは非負だから
$$
T \;\ge\; (m_0+1)\cdot\frac k2
$$
である．床関数の性質 $\log_2(k/2) < (m_0 + 1)\log_2(\lvert\mathcal X\rvert+1)$ を入れ，$2\log_2(\lvert\mathcal X\rvert+1) > 0$ を掛けると
$$
2\,T\log_2\big(\lvert\mathcal X\rvert+1\big) \;>\; k\big(\log_2 k - 1\big)
$$
となる．

最後にまとめる．$\log_2(\lvert\mathcal X\rvert+1) \ge 1$ と $k \le T$ から $k \le T\log_2(\lvert\mathcal X\rvert+1)$ である．前段の不等式に足して $k\log_2 k < 3\,T\log_2(\lvert\mathcal X\rvert+1)$ を得る．
:::

::: formalization-note
補題 12.5.6 に対応する宣言として `total_length_ge_count_mul_log` (`InformationTheory/Shannon/LZ78/PhraseCounting.lean`) がある．仮定は本文より弱く，本数が $1$ 以上であることを要さない（列が相異なることと空でないことだけを課す）．ただし宣言の定数は $8\log_2(\lvert\mathcal X\rvert+1)$ で，本文の $3\log_2(\lvert\mathcal X\rvert+1)$ より大きい．すなわち宣言が述べているのは本文の主張より弱い不等式なので，形式化ポインタは付けない．機械検証が及んでいるのは定数を $8$ にした形までである．
:::

::: formalization-note 本節と次節の詰め込みの不等式に共通
この形の不等式に対応する宣言は，$\log$ を自然対数にとる．どの不等式も両辺が $\log$ の $1$ 次なので，底を変えると両辺が同じ倍率で変わり，自然対数で書いた宣言と底 $2$ で書いた本文の主張は同じことを述べている．宣言の定数を本文の定数と比べるときも，この読み替えのもとで比べている．
:::

補題 12.5.6 の読み方は素直である．長さをある値以下に抑えた列は，その値で決まる本数しかないので，相異なる列を多く用意するほど，そのうち長いものの割合が増え，文字数の合計が膨らむ．裏返せば，文字数の合計が $n$ しかないところに詰め込める相異なる列の本数には限りがある．次の定理はこれを分解に当てる．

::: theorem 12.5.7 貪欲な分解のフレーズ数
$\mathcal X$ を空でない有限アルファベット，$n \ge 1$，$x \in \mathcal X^n$ とすると
$$
\lvert\mathcal S(x)\rvert\,\log_2\lvert\mathcal S(x)\rvert
  \;\le\; 3\log_2\big(\lvert\mathcal X\rvert + 1\big)\,n
$$
である（$\mathcal S(x)$ は 定義 12.5.1 の貪欲な分解）．
:::

::: proof
$k := \lvert\mathcal S(x)\rvert$ と置く．$n \ge 1$ だから，定義 12.5.1 で最初の文字を読んだ時点で $w$ は $1$ 文字の列になり，そのときの辞書は空だから $w$ は出力される．よって $k \ge 1$ である．命題 12.5.3 よりフレーズはどの二つも相異なり，命題 12.5.4 よりどれも空列でないから，補題 12.5.6 を $s_1, \dots, s_k$ に当てて
$$
k\log_2 k \;\le\; 3\log_2\big(\lvert\mathcal X\rvert + 1\big)\sum_{j=1}^{k}\lvert s_j\rvert
$$
を得る．命題 12.5.4 より右辺の和は $n$ 以下で，$3\log_2(\lvert\mathcal X\rvert+1)$ は正だから，主張が従う．
:::

::: formalization-note
定理 12.5.7 に対応する宣言として `lz78PhraseStrings_mul_log_le` (`InformationTheory/Shannon/LZ78/PhraseCounting.lean`) がある．仮定は本文より弱く，長さが $1$ 以上であること（すなわち $n \ge 1$）を要さない．ただし 補題 12.5.6 と同じ理由で定数が $8\log_2(\lvert\mathcal X\rvert+1)$ であり，本文の主張より弱い不等式を述べている．そのため形式化ポインタは付けない．
:::

::: corollary 12.5.8
$\mathcal X$ を空でない有限アルファベットとすると，$\mathcal X$ にのみ依存する定数 $c > 0$ があって，$n \ge 2$ を満たすすべての $n$ とすべての $x \in \mathcal X^n$ で
$$
\lvert\mathcal S(x)\rvert \;\le\; c\,\frac{n}{\log_2 n}
$$
が成り立つ（$\mathcal S(x)$ は 定義 12.5.1 の貪欲な分解）．
:::

::: proof
$c_0 := 3\log_2(\lvert\mathcal X\rvert+1)$ と置き，$c := \max\big(2\log_2 e,\ 2c_0\big)$ ととる．これは $\mathcal X$ だけで決まる．$n \ge 2$ と $x \in \mathcal X^n$ をとり，$k := \lvert\mathcal S(x)\rvert$ と置く．$\log_2 n \ge 1 > 0$ であり，定理 12.5.7 より $k\log_2 k \le c_0\,n$ である．$k$ と $\sqrt n$ の大小で二つに分ける．

$k \ge \sqrt n$ の場合を見る．$k$ は整数で $\sqrt n > 1$ だから $k \ge 2$ であり，$\log_2 k \ge \frac12\log_2 n > 0$ である．$k\log_2 k \le c_0 n$ の両辺を $\log_2 k$ で割ると
$$
k \;\le\; \frac{c_0\,n}{\log_2 k} \;\le\; \frac{2c_0\,n}{\log_2 n} \;\le\; c\,\frac{n}{\log_2 n}
$$
である．

$k < \sqrt n$ の場合に移る．1.1 節の信頼の底から出した対数不等式 $\log t \le (t-1)\log e$ を底 $2$ のもとで $t := \sqrt n$ に当てると $\frac12\log_2 n \le (\sqrt n - 1)\log_2 e \le \sqrt n\,\log_2 e$ であり，$\log_2 n \le 2\log_2 e\,\sqrt n \le c\sqrt n$ を得る．両辺に $\sqrt n > 0$ を掛けると $\sqrt n\,\log_2 n \le c\,n$ であり，$\log_2 n > 0$ で割ると $\sqrt n \le c\,n/\log_2 n$ を得る．$k < \sqrt n$ と合わせて主張が従う．
:::

::: formalization-note
系 12.5.8 に対応する宣言として `lz78PhraseStrings_count_isBigO` (`InformationTheory/Shannon/LZ78/PhraseCounting.lean`) がある．ただしこれは，各 $n$ に長さ $n$ の系列を一つずつ与えた列に対し，フレーズ数が $n/\log n$ の定数倍で抑えられることを述べたものである．本文は定数を系列の取り方によらずにとれると述べており，宣言のほうが狭い．そのため形式化ポインタは付けない．宣言が使う 定理 12.5.7 の形（`lz78PhraseStrings_mul_log_le`）のほうは系列ごとに成り立つ．機械検証が及んでいないのは，そこから系列に依らない定数を取り出すところである．
:::

系 12.5.8 が言っているのは，分解のフレーズ数が長さに比べて小さい，ということである．系 12.5.5 の $n$ 本という上界に対し，実際には $n/\log_2 n$ の定数倍までしか作れない．しかもこれは系列の中身によらず，どんな並びに対しても成り立つ．この差がそのまま符号長に効く．フレーズ $1$ 本を書くのに要するビット数は，次の定義で見るとおり $\log_2 n$ の水準だからである．次はその勘定を最後まで書き下す．

## 符号長

::: definition 12.5.9 Lempel–Ziv 符号長
$\mathcal X$ を空でない有限アルファベット，$n \ge 0$，$x \in \mathcal X^n$ とし，$k := \lvert\mathcal S(x)\rvert$（定義 12.5.1）と置く．$x$ の **Lempel–Ziv 符号長** を
$$
\ell^{\mathrm{LZ}}_n(x) \;:=\; k\Big(\big\lfloor\log_2(k+1)\big\rfloor
  + \big\lfloor\log_2\lvert\mathcal X\rvert\big\rfloor + 2\Big)
$$
で定める．
:::

::: formalized
$1$ フレーズあたりのビット数 `LZ78Phrase.bitLength` (`InformationTheory/Shannon/LZ78/GreedyParsing.lean`)，符号長 `lz78GreedyEncodingLength` (`InformationTheory/Shannon/LZ78/AsymptoticOptimality/EncodingLength.lean`)
:::

括弧の中は，フレーズ $1$ 本を書くのに割り当てるビット数である．内訳はこうである．定義 12.5.1 の分岐から読んだとおり，各フレーズは辞書にある列（または空列）に $1$ 文字足したものだった．そこで各フレーズを，足す前の列が辞書の何番目かという番号と，足した $1$ 文字との対で書く．番号のほうは，空列の場合を合わせて $k+1$ 通りを区別すればよいので $\lfloor\log_2(k+1)\rfloor + 1$ ビット，文字のほうは $\lvert\mathcal X\rvert$ 通りだから $\lfloor\log_2\lvert\mathcal X\rvert\rfloor + 1$ ビットである．二つを足したものが括弧の中で，どのフレーズにも同じだけ割り当てる（辞書が小さいうちは番号がもっと短く書けるが，本数を掛けたときの見積もりを簡単にするため，最後の大きさにそろえておく）．対の並びを先頭から読めば，番号の指す列に文字を足してフレーズが一本ずつ決まり，辞書もそのつど組み直せるから，フレーズの列はここから復元できる．定義 12.5.1 の直後に見たとおり，$x$ に戻るにはさらに，読み残した切れ端が辞書の何番目かを書き足す必要がある．そのぶんは番号だけで足りるので，フレーズ $1$ 本に割り当てるビット数より少ないが，定義 12.5.9 はこの $1$ 本を数えていない．本書はこれらを主張として述べず，証明もしない．以下の評価は，定義 12.5.9 の右辺を符号長として扱うだけだからである．

::: formalization-note
対を固定長のビット列に書く割り当てが一意復号可能であること，すなわちビット列の並びから対の並びが復元できることは `uniquelyDecodable_lz78TokenCode` (`InformationTheory/Shannon/LZ78/ConverseUDObject.lean`) が述べている．対の並びから系列そのものを復元する側には，対応する宣言が無い．
:::

::: theorem 12.5.10
$\mathcal X$ を空でない有限アルファベット，$n \ge 0$，$x \in \mathcal X^n$ とすると
$$
\ell^{\mathrm{LZ}}_n(x) \;\le\; n\Big(\big\lfloor\log_2(n+1)\big\rfloor
  + \big\lfloor\log_2\lvert\mathcal X\rvert\big\rfloor + 2\Big)
$$
である（$\ell^{\mathrm{LZ}}_n$ は 定義 12.5.9 の符号長）．
:::

::: proof
$k := \lvert\mathcal S(x)\rvert$ と置くと 系 12.5.5 より $k \le n$ である．$\log_2$ は増加し，床関数は $s \le t$ ならば $\lfloor s\rfloor \le \lfloor t\rfloor$ を満たすから $\lfloor\log_2(k+1)\rfloor \le \lfloor\log_2(n+1)\rfloor$ であり，括弧の中は $k$ を $n$ に取り替えても減らない．括弧の中は正だから，$k \le n$ と合わせて，二つの因子をそれぞれ大きくして主張を得る．
:::

::: formalized
`lz78_encoding_length_le_n_log_n_plus_const` (`InformationTheory/Shannon/LZ78/AsymptoticOptimality/EncodingLength.lean`)
:::

::: corollary 12.5.11
$\mathcal X$ を空でない有限アルファベット，$n \ge 1$，$x \in \mathcal X^n$ とすると
$$
\frac{\ell^{\mathrm{LZ}}_n(x)}{n} \;\le\; \big\lfloor\log_2(n+1)\big\rfloor
  + \big\lfloor\log_2\lvert\mathcal X\rvert\big\rfloor + 2
$$
である（$\ell^{\mathrm{LZ}}_n$ は 定義 12.5.9 の符号長）．
:::

::: proof
定理 12.5.10 の両辺を $n > 0$ で割ればよい．
:::

::: formalized
`lz78_encoding_length_per_symbol_le` (`InformationTheory/Shannon/LZ78/AsymptoticOptimality/EncodingLength.lean`)
:::

系 12.5.11 の右辺は $n$ とともに増えるので，これだけでは $1$ 文字あたりの符号長が定数で抑えられたことにならない．$k \le n$ で済ませたのが粗すぎたのであって，定理 12.5.7 のフレーズ数の抑えを 定義 12.5.9 に入れ直せば，増える項が消える．

::: corollary 12.5.12
$\mathcal X$ を空でない有限アルファベット，$n \ge 1$，$x \in \mathcal X^n$ とすると
$$
\frac{\ell^{\mathrm{LZ}}_n(x)}{n} \;\le\; 3\log_2\big(\lvert\mathcal X\rvert+1\big)
  + \big\lfloor\log_2\lvert\mathcal X\rvert\big\rfloor + 3
$$
である（$\ell^{\mathrm{LZ}}_n$ は 定義 12.5.9 の符号長）．右辺は $\mathcal X$ だけで決まり，$n$ にも $x$ にも依らない．
:::

::: proof
$k := \lvert\mathcal S(x)\rvert$ と置く．$n \ge 1$ だから，定義 12.5.1 で最初の文字を読んだ時点で $w$ は $1$ 文字の列になり，そのときの辞書は空だから $w$ は出力される．よって $k \ge 1$ であり，$k + 1 \le 2k$ から $\log_2(k+1) \le \log_2 k + 1$ である．床関数の性質 $\lfloor t\rfloor \le t$ と合わせると
$$
\ell^{\mathrm{LZ}}_n(x) \;\le\; k\log_2 k
  \;+\; k\Big(\big\lfloor\log_2\lvert\mathcal X\rvert\big\rfloor + 3\Big)
$$
である．定理 12.5.7 より第 $1$ 項は $3\log_2(\lvert\mathcal X\rvert+1)\,n$ 以下，系 12.5.5 より第 $2$ 項の $k$ は $n$ 以下だから，両辺を $n > 0$ で割れば主張を得る．
:::

::: formalization-note
系 12.5.12 に対応する宣言として `lz78_rate_le_const` (`InformationTheory/Shannon/LZ78/AsymptoticOptimality/EncodingLength.lean`) がある．仮定は本文より弱く，$n = 0$ の場合も含めて述べている．ただし 補題 12.5.6 と同じ理由で定数の $3\log_2(\lvert\mathcal X\rvert+1)$ のところが $8\log_2(\lvert\mathcal X\rvert+1)$ であり，本文の主張より弱い不等式を述べている．そのため形式化ポインタは付けない．
:::

::: example 12.5.13 $13$ 文字の二値系列の符号長
例 12.5.2 の $x = 1011010100010$（$\mathcal X = \{0,1\}$，$n = 13$）に対し $\ell^{\mathrm{LZ}}_{13}(x) = 42$ ビットである（$\ell^{\mathrm{LZ}}_n$ は 定義 12.5.9 の符号長）．
:::

::: proof
例 12.5.2 より $k = \lvert\mathcal S(x)\rvert = 7$ である．$\lfloor\log_2 8\rfloor = 3$ であり，$\lvert\mathcal X\rvert = 2$ だから $\lfloor\log_2 2\rfloor = 1$ である．よってフレーズ $1$ 本あたりのビット数は $3 + 1 + 2 = 6$ で，$\ell^{\mathrm{LZ}}_{13}(x) = 7 \times 6 = 42$ である．
:::

$13$ 文字を $1$ 文字 $1$ ビットで書き写せば $13$ ビットで済むから，この系列では Lempel–Ziv 符号のほうが $3$ 倍以上長い．フレーズ $1$ 本に $6$ ビットを払って，覆えているのは平均 $13/7$ 文字だからである．短い系列で膨らむのはこのためで，縮むとすれば，辞書が育ってフレーズ $1$ 本の覆う文字数が増えてからである．

系 12.5.12 が抑えたのはそこまでである．$1$ 文字あたりの符号長が定数を超えないことは分かったが，行き着く値が情報源のエントロピーレートかどうかは，ここまでの数え上げでは決まらない．数え上げが見ているのはフレーズが相異なることだけで，どのフレーズがどれだけ起こりやすいかを見ていないからである．次節は，そこに情報源の確率を入れる．
