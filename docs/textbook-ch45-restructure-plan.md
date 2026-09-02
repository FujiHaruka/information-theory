# 第4・5章 全面書き直し 設計図

対象は `docs/textbook/ch04-channel-capacity.md` (562 行) と
`docs/textbook/ch05-max-entropy.md` (420 行)。両方を破棄し、節ファイルに分割して書き直す。
執筆原則の SoT は `.claude/rules/textbook-writing.md`（以下 §N はそこの節番号）。

## 背景と現状の乖離

§11 の乖離表の行に、両章の具体的な違反箇所を対応させる。

| §11 の軸 | 第4章の現状 | 第5章の現状 |
|---|---|---|
| 形式化ポインタ (§7) | `**Verified**: …` の地の文が 14 箇所 | 同じ形が 12 箇所 |
| Lean コード (§7) | ` ```lean ` フェンスが 12 個、シグネチャを丸ごと引用 | 同 13 個 |
| 章の入口 (§3) | 冒頭 30 行が「このファイルについて」＋検証強度＋形式化の枠組み | 同 27 行 |
| 章末 (§10) | 「本章で未形式化の項目」6 項＋「所見」4 項 | 「未形式化の項目」4 項＋「所見」4 項 |
| 番号 (§8) | 番号なし。参照は節見出しへのリンクだけ | 同 |
| 主張と証明 (§4) | `::: proof` ゼロ。証明を Lean の存在で代える | 同 |
| 数式デリミタ (§6) | `\(…\)` / `\[…\]` | 同 |
| 直感 (§5) | 記述が薄い。太字リードもない | 同 |
| 節ファイル分割 (§3) | 1 章 1 ファイル | 同 |
| 前方参照 (§2) | 未検査 | 未検査 |

これに加えて、両章とも **Lean 資産の記述が陳腐化している**。草稿が名指しする
本プロジェクトのファイル 18 本のうち、現在の木に存在するのは
`Shannon/Converse.lean`・`Shannon/DifferentialEntropy.lean`・`Shannon/MaxEntropy/` の
3 ファイル、合わせて 5 本だけである。

## Approach

解の形は 4 つ。

**1. 資産を実コードから引き直し、紐付け方針を「無条件・単独宣言」に絞る。**
草稿のパスと署名は信用しない。全ポインタ候補を `scripts/sig_view.ts` で実物に当て、
`0 sorry` と v1.0.1 収録を機械確認したうえで、仮定が regularity だけかを署名から判定する。
判定の結果、草稿が `Verified` から外した達成可能性の一般形は**外す理由が既に消えており**
（`h_passthrough` は現存しない）、逆に草稿が「別 plan に deferred」と書いた強逆定理の
asymptotic 段は**形式化済み**である。すなわち紐付けの範囲は草稿より広くなる。

**2. 節を「1 節 1 仕事」に割り直す。** 第4章は 6 節案を **7 節** に増やす。理由は 2 つ。
(a) 達成可能性は「結合典型集合の 3 性質」と「ランダム符号化」で道具と論証が分かれ、
第2章が 2.2 節（典型集合）と 2.3 節（符号化定理）に割ったのと同じ形になる。
(b) 強逆定理は容量達成条件（線分微分と鞍点条件）を先に要し、それを 1 節に詰めると
1 節 350 行を超える。第5章は 4 節を維持するが、中身は入れ替える（下記 4）。

**3. 具体例を主役の位置に置く。** 草稿の最大の弱点は、第4章に例が 1 つもないこと。
二元対称通信路と二元消失通信路の容量を、既出の道具（定理 1.1.5・定理 1.3.4・
定理 1.2.3）だけで**証明つきで**計算し、4.1 節に置く。どちらも形式化されていないので、
`::: formalized` は付けず、その場で「本書は証明するが形式化はされていない」と書く（§7）。

**4. 第5章は「相対エントロピーへの読み替え」を背骨にし、乗数の存在を独立の節にする。**
草稿は制約なしの上界（定理 1.1.5）を再掲していたが、これは第1章の主張そのもので、
§8 の番号の一意性に反する。代わりに $D(P\|U) = \log|\mathcal X| - H(P)$ という恒等式
（形式化済み）を 5.1 節の主命題に据えると、「エントロピー最大化＝一様分布からの
相対エントロピー最小化」という視点が章全体の方法になり、5.2 節の核 identity が
その一般化として読める。そして草稿が章末に隠していた「Lagrange 乗数は仮説である」を、
5.4 節「Lagrange 乗数の存在」として正面から扱う。$k = 1$ なら中間値の定理で
**存在と一意性を本書で証明できる**ので、節は否定の列挙ではなく定理をもつ節になる。

## Lean 資産の棚卸し

機械確認したこと（2026-09-02、HEAD = 445ff4b3、タグ = v1.0.1）:
`scripts/sig_view.ts --sorry` で下表の全ファイルが **0 sorry**、`rg` で `@residual` なし、
`git show v1.0.1:<path>` で下表の全 67 宣言がタグに収録済み、
`git diff v1.0.1 HEAD -- <path>` で主要 4 ファイルはタグと HEAD が同一。
再導出コマンドは `scripts/sig_view.ts --sorry <file>` と
`git show v1.0.1:<path> | rg '<name>'`（§7 の「再導出 > キャッシュ」に従い、原稿には書かない）。

### 第4章

仮定の性質欄: **R** = regularity / 構造前提のみ、**S** = 構造前提＋能動的な限定
（読者に見せる必要がある仮定）。全宣言 v1.0.1 収録済み・0 sorry。

| 宣言名 | パス (`InformationTheory/Shannon/` 以下) | 仮定 | 紐付け先 |
|---|---|---|---|
| `Channel` / `jointDistribution` / `outputDistribution` | `ChannelCoding/Basic.lean` | R | 定義 4.1.1 |
| `mutualInfoOfChannel` | `ChannelCoding/Basic.lean` | R | 定義 4.1.2 |
| `mutualInfoOfChannel_eq_mutualInfo_prod` / `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` | `ChannelCoding/Basic.lean` | R | 命題 4.1.3 |
| `capacity` | `ChannelCoding/ShannonTheorem.lean` | R | 定義 4.1.4 |
| `exists_capacity_achiever` / `capacity_bddAbove` / `continuous_mutualInfoOfChannel_left` | `ChannelCoding/ShannonTheorem.lean` | R | 定理 4.1.5 |
| `capacity_nonneg` | `ChannelCoding/ShannonTheorem.lean` | R | 命題 4.1.6 |
| `Code` / `errorProbAt` / `averageErrorProb` | `ChannelCoding/Basic.lean` | R | 定義 4.2.1 |
| `jointlyTypicalSet` | `ChannelCoding/Basic.lean` | R | 定義 4.2.3 |
| `jointlyTypicalSet_card_le` | `ChannelCoding/Basic.lean` | S (全対に正の確率) | 定理 4.2.4 |
| `jointlyTypicalSet_prob_tendsto_one` | `ChannelCoding/Basic.lean` | S (対独立＋同分布) | 定理 4.2.5 |
| `jointlyTypicalSet_indep_prob_le` | `ChannelCoding/Basic.lean` | S (相互独立＋全点正) | 定理 4.2.6 |
| `Codebook` / `jointTypicalDecoder` / `codebookToCode` | `ChannelCoding/Achievability/Core.lean` | R | 定義 4.3.1 |
| `errorProbAt_le_E1_plus_E2` | `ChannelCoding/Achievability/Core.lean` | R | 補題 4.3.2 |
| `random_codebook_average_le` | `ChannelCoding/Achievability/RandomCodebook.lean` | S (入力 full support) | 補題 4.3.3 |
| `exists_codebook_le_avg` | `ChannelCoding/Achievability/Main.lean` | R | 補題 4.3.4 |
| `channel_coding_achievability` | `ChannelCoding/Achievability/Main.lean` | S (入力・通信路 full support) | 補題 4.3.5 |
| `errorProbAt_filter_card_bound` / `exists_subcode_maxError_lt_two_mul` | `ChannelCoding/ShannonTheorem.lean` | R | 補題 4.3.6 |
| `shannon_noisy_channel_coding_theorem_general` | `ChannelCoding/ShannonTheoremMaxError.lean` | **無条件** | 定理 4.3.7 |
| `shannon_converse_single_shot` | `Converse.lean`（`Shannon/` 直下） | S (メッセージ一様・相互情報量有限) | 定理 4.4.1 |
| `shannon_converse_single_shot_markov_encoder` | `Converse.lean` | S (同上＋マルコフ連鎖) | 系 4.4.2 |
| `channel_coding_converse_general_chainRule` | `ChannelCoding/ConverseGeneral.lean` | S (同上) | 定理 4.4.3 |
| `IsMemorylessChannel` | `ChannelCoding/ConverseMemorylessChainRule.lean` | R (定義) | 定義 4.4.4 |
| `channel_coding_converse_general_memoryless_pure` | `ChannelCoding/ConverseMemoryless.lean` | S (無記憶性) | 定理 4.4.5 |
| `IsMemorylessFeedback` | `ChannelCoding/FeedbackMemoryless.lean` | R (定義) | 定義 4.5.2 |
| `feedback_per_letter_bound` | `ChannelCoding/FeedbackMemoryless.lean` | S (無記憶・因果) | 補題 4.5.3 |
| `channel_coding_feedback_converse_memoryless` | `ChannelCoding/FeedbackMemoryless.lean` | S (同上＋各時刻の上界 `C`) | 定理 4.5.4 |
| `mutualInfo_segment_hasDerivAt` | `ChannelCoding/StrongConverseAsymptotic.lean` | S (出力分布が全点正) | 補題 4.6.1 |
| `klDiv_channel_le_capacity` | `ChannelCoding/StrongConverseAsymptotic.lean` | S (最大化子＋全点正) | 命題 4.6.2 |
| `highLLRSet` | `ChannelCoding/StrongConverse.lean` | R | 定義 4.6.4 |
| `channelCoding_per_codeword_decomposition` | `ChannelCoding/StrongConverse.lean` | R | 補題 4.6.5 |
| `channelCoding_average_success_le` | `ChannelCoding/StrongConverse.lean` | R | 定理 4.6.6 |
| `llrUnifBound` / `channelCoding_highLLR_tendsto_zero` | `ChannelCoding/StrongConverseAsymptotic.lean` | S (最大化子＋全点正) | 補題 4.6.7 |
| `channelCoding_strong_converse_asymptotic` | `ChannelCoding/StrongConverseAsymptotic.lean` | S (同上＋レート条件) | 定理 4.6.8 |
| `channelCoding_operational_rate_le_capacity` | `ChannelCoding/StrongConverseAsymptotic.lean` | S (同上) | 系 4.6.9 |
| `BlockwiseChannel` / `BlockwiseChannel.ofMemoryless` / `Channel.toBlock` | `BlockwiseChannel/Definition.lean` | R | 定義 4.7.1 |
| `BlockwiseChannel.capacityN` / `capacityRate` / `capacity_lim` | `BlockwiseChannel/Definition.lean`, `GeneralDMC/Basic.lean` | R | 定義 4.7.2 |
| `capacityRate_ofMemoryless_eventually_const` / `capacity_lim_tendsto_of_memoryless` | `GeneralDMC/Basic.lean` | R | 命題 4.7.3 |
| `capacity_lim_eq_capacity_of_memoryless` | `GeneralDMC/Basic.lean` | R | 定理 4.7.4 |

**草稿の判断のうち覆したもの**（実コードで確認済み）:

- `shannon_noisy_channel_coding_theorem_general` は草稿が「`h_passthrough` に核心を
  bundle」として `Verified` から除外していたが、**現在の署名にその仮定はない**
  （`W`・`R < capacity W`・`ε > 0` だけ）。`rg 'h_passthrough' InformationTheory/` は 0 件。
  よって本設計ではこれを達成可能性の headline に採る。full-support 版
  `shannon_noisy_channel_coding_theorem` は中間段として注記でだけ触れる。
- 強逆定理の asymptotic 段は草稿が「別 plan に deferred」としたが、
  `ChannelCoding/StrongConverseAsymptotic.lean` が存在し、`channelCoding_strong_converse_asymptotic`
  （$P_e \to 1$）と `channelCoding_operational_rate_le_capacity` の両方が 0 sorry・`@audit:ok`。
- 草稿のパスはほぼ全滅（`ChannelCoding.lean` → `ChannelCoding/Basic.lean`,
  `ChannelCodingShannonTheorem.lean` → `ChannelCoding/ShannonTheorem.lean`,
  `ChannelCodingConverseMemorylessPure.lean` → `ChannelCoding/ConverseMemoryless.lean`,
  `ChannelCodingFeedbackComplete.lean` → `ChannelCoding/FeedbackMemoryless.lean`,
  `ChannelCodingStrongConverse.lean` → `ChannelCoding/StrongConverse.lean`,
  `GeneralDMC.lean` → `GeneralDMC/Basic.lean`, `BlockwiseChannel.lean` → 3 ファイルに分割）。
- 草稿が引用した `exists_capacity_achiever` の署名も古い。現行の結論は
  `∃ p ∈ stdSimplex, IsMaxOn …` であって `… = capacity W` ではない。

**草稿の判断のうち維持するもの**: `ChannelCoding/Feedback.lean` の
`channel_coding_feedback_converse` / `_capacity` / `_chain` は現在も
`@audit:retract-candidate(superseded-by-memoryless-form)` が付いており、per-letter 評価を
仮説として受け取る MVP。紐付けない。

### 第5章

全宣言 v1.0.1 収録済み・0 sorry。第5章のファイルはすべて `InformationTheory/Shannon/MaxEntropy/` 以下。

| 宣言名 | ファイル | 仮定 | 紐付け先 |
|---|---|---|---|
| `klDiv_uniformOn_univ_toReal_eq` | `Basic.lean` | R | 命題 5.1.2 |
| `gibbsZ` / `gibbsPmf` | `Constrained.lean` | R | 定義 5.2.1 |
| `gibbsPmf_pos` / `gibbsPmf_mem_stdSimplex` | `Constrained.lean` | R | 命題 5.2.2 |
| `klDivPmf_gibbsPmf_eq` | `Constrained.lean` | R | 補題 5.2.3 |
| `entropy_le_gibbs_of_constraints` | `Constrained.lean` | S (λ の制約整合) | 定理 5.2.5 |
| `entropy_eq_gibbs_iff_of_constraints` | `Constrained.lean` | S (同上) | 定理 5.2.6 |
| `gibbsPmf_zero_eq_uniform` / `entropy_gibbsPmf_zero_eq_log_card` | `Constrained.lean` | R | 例 5.2.7 |
| `boolFeature` / `entropy_gibbsPmf_bool_eq_binEntropy` | `Constrained.lean` | S (平均制約) | 例 5.2.8 |
| `logPartitionψ` / `expFamilyDist` | `ConstrainedKKT.lean` | R | 定義 5.3.1 |
| `expFamilyDist_eq_gibbsPmf` | `ConstrainedKKT.lean` | R | 命題 5.3.2 |
| `KKTSolution` / `entropy_expFamilyDist_eq_legendre` | `ConstrainedKKT.lean` | S (制約整合) | 定理 5.3.3 |
| `entropy_le_logPartition_sub_inner` | `ConstrainedKKT.lean` | S (同上) | 定理 5.3.4 |
| `linearFeature` / `gibbsPmf_linearFeature_eq_geometric` | `Constrained.lean` | R | 例 5.3.5 |

**λ は load-bearing か**: 否。`entropy_le_gibbs_of_constraints` の
`h_gibbs_constraints` は「その λ の Gibbs 分布が同じモーメント制約を満たす」であって、
結論（$H(P) \le H(p^*)$）とは別の命題である。循環でも `:True` でもなく、証明の核は
補題 5.2.3 の恒等式が担っている。したがって紐付けてよい。ただし**主張ブロックに
この仮定を明記する**こと（§5「主張の中の自由変数は主張の中で量化する」）。
存在性は別問題として 5.4 節が扱う。

### 形式化ポインタを付けない主張と、その理由

**(a) 合成でしか得られない**（`::: formalization-note` に「単独の宣言はなく、どれと
どれの合成か」を書く。§7）

- 系 4.4.6「達成可能なレートは容量以下」。定理 4.4.5 の右辺 $\sum_i I(X_i;Y_i)$ を $nC$ に
  換える段が `mutualInfoOfChannel_toReal_le_capacity` にあたるが、これは
  `BlockwiseChannel/MemorylessCapacity.lean` の `private`。注記に書く。
- 系 4.5.5「フィードバックは容量を増やさない」。定理 4.5.4 は各時刻の上界 `C` を
  引数で受け取る形なので、`C = capacity W` に固定する段が同じ理由で単独宣言にならない。
- 系 5.2.4「$H(p^*) - H(P) = D(P\|p^*)$」。補題 5.2.3 を $Q = P$ と $Q = p^*$ で
  2 度評価した差であり、単独の宣言はない。

**(b) load-bearing 仮定を含むので紐付けない**

- `channel_coding_feedback_converse` / `channel_coding_feedback_converse_capacity` /
  `channel_coding_feedback_converse_chain`（`ChannelCoding/Feedback.lean`）。
  per-letter 評価そのものを仮説に取る MVP。原稿はこれらに一切触れない。

**(c) そもそも形式化されていない**（本書は証明する。§7 の「本書が証明しない主張と、
形式化されていない主張を書き分ける」の後者にあたるので、その旨をその場で書く）

- 命題 4.1.7「$C \le \log\min(|\mathcal X|,|\mathcal Y|)$」
- 例 4.1.8「二元対称通信路の容量 $1 - H_b(p)$」、例 4.1.9「二元消失通信路の容量 $1-\varepsilon$」
- 定義 4.2.2「達成可能レート」（通信路側の達成レート集合を定義した宣言はない）
- 5.4 節のすべて（命題 5.4.1・命題 5.4.2・定理 5.4.3・例 5.4.4・例 5.4.5）

## 第4章の設計

### 節分割

`docs/textbook/ch04-channel-capacity.md` を削除し `docs/textbook/ch04/` を作る。

| ファイル | 節 | タイトル | 想定行数 |
|---|---|---|---|
| `ch04/01-capacity.md` | 4.1 | 通信路と通信路容量 | 200 |
| `ch04/02-joint-typicality.md` | 4.2 | 通信路符号と結合典型集合 | 190 |
| `ch04/03-random-coding.md` | 4.3 | ランダム符号化と達成可能性 | 210 |
| `ch04/04-converse.md` | 4.4 | 逆定理 | 190 |
| `ch04/05-feedback.md` | 4.5 | フィードバックのある通信路 | 130 |
| `ch04/06-strong-converse.md` | 4.6 | 強逆定理 | 280 |
| `ch04/07-general-channel.md` | 4.7 | 一般の通信路の容量 | 130 |

合計 1330 行を上限とみる（目安 900–1200 をやや超えるが、7 節は 1 節あたり 190 行で
第1〜3 章の実績（80–290）の中に収まる）。

`build.mjs` の `chapters` 配列で、第4章の `src` を消して `sections` に置き換える:

```
sections: [
  { slug: 'ch04-01', num: '4.1', title: '通信路と通信路容量', src: 'ch04/01-capacity.md' },
  … 以下同様に 4.7 まで …
],
status: '仕上げ済',
```

### 主張の番号表

§8 のとおり節内で種別によらず通し番号。**形ポ**欄は `::: formalized` に書く宣言名
（複数のときは `/` 区切り。パスは「Lean 資産の棚卸し」の表から引く）。

| 番号 | 種別 | 主張 | 形ポ | 証明の方針 |
|---|---|---|---|---|
| 4.1.1 | 定義 | 離散無記憶通信路 $W(y\mid x)$ と、長さ $n$ への積による延長 | `Channel` `jointDistribution` `outputDistribution` | — |
| 4.1.2 | 定義 | 入力分布 $p$ のもとでの通信路の相互情報量 $I(p;W)$ | `mutualInfoOfChannel` | — |
| 4.1.3 | 命題 | $I(p;W) = H(Y) - H(Y\mid X)$ | `mutualInfoOfChannel_eq_mutualInfo_prod` `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` | 定理 1.3.4 を対 $(X,Y)$ に当てる |
| 4.1.4 | 定義 | 通信路容量 $C(W) = \max_p I(p;W)$ | `capacity` | — |
| 4.1.5 | 定理 | 最大値は達成される（達成する入力分布が存在する） | `exists_capacity_achiever` `capacity_bddAbove` `continuous_mutualInfoOfChannel_left` | $I(\cdot;W)$ の連続性＋単体のコンパクト性（借用 B1） |
| 4.1.6 | 命題 | $0 \le C(W)$ | `capacity_nonneg` | 命題 1.3.2 |
| 4.1.7 | 命題 | $C(W) \le \log\min(|\mathcal X|,|\mathcal Y|)$ | なし (c) | 命題 4.1.3 と定理 1.1.5 |
| 4.1.8 | 例 | 二元対称通信路: $C = 1 - H_b(p)$、一様入力で達成 | なし (c) | 命題 4.1.3 で $H(Y\mid X)=H_b(p)$、定理 1.1.5 で $H(Y)\le 1$ |
| 4.1.9 | 例 | 二元消失通信路: $C = 1 - \varepsilon$、一様入力で達成 | なし (c) | 定理 1.2.3 で $H(Y) = H_b(\varepsilon) + (1-\varepsilon)H(X)$ |
| 4.2.1 | 定義 | ブロック通信路符号・レート・誤り確率（最大／平均） | `Code` `errorProbAt` `averageErrorProb` | — |
| 4.2.2 | 定義 | 達成可能レート | なし (c) | — |
| 4.2.3 | 定義 | 結合典型集合 $A^{(n)}_\varepsilon$ | `jointlyTypicalSet` | — |
| 4.2.4 | 定理 | $|A^{(n)}_\varepsilon| \le 2^{n(H(X,Y)+\varepsilon)}$ | `jointlyTypicalSet_card_le` | 定理 2.2.5 を積アルファベットに当てる |
| 4.2.5 | 定理 | 真の組が結合典型に入る確率は 1 に近づく | `jointlyTypicalSet_prob_tendsto_one` | 定理 2.2.3 を 3 軸に当てて共通部分をとる |
| 4.2.6 | 定理 | 独立に選んだ組が結合典型に入る確率は $2^{-n(I-3\varepsilon)}$ 以下 | `jointlyTypicalSet_indep_prob_le` | 定理 2.2.4 の 3 軸版の掛け合わせ |
| 4.3.1 | 定義 | ランダム符号帳と結合典型復号器 | `Codebook` `jointTypicalDecoder` `codebookToCode` | — |
| 4.3.2 | 補題 | 誤り確率 $\le$「真の組が非典型」＋「他の符号語が典型」 | `errorProbAt_le_E1_plus_E2` | 復号規則の場合分け |
| 4.3.3 | 補題 | 符号帳について平均した誤り確率の上界 | `random_codebook_average_le` | 定理 4.2.5・定理 4.2.6 と和の入れ替え |
| 4.3.4 | 補題 | 平均以下の符号帳が少なくとも 1 つある | `exists_codebook_le_avg` | 有限集合上の平均 |
| 4.3.5 | 補題 | 入力分布を固定したときの達成可能性（平均誤り確率） | `channel_coding_achievability` | 補題 4.3.2–4.3.4 の合成 |
| 4.3.6 | 補題 | 誤り確率の大きい符号語を捨てると最大誤り確率が抑えられる | `errorProbAt_filter_card_bound` `exists_subcode_maxError_lt_two_mul` | マルコフの不等式を符号語の数え上げに当てる |
| 4.3.7 | 定理 | 通信路符号化定理（達成可能性）: $R < C$ なら最大誤り確率を任意に小さくできる | `shannon_noisy_channel_coding_theorem_general` | 定理 4.1.5 で最大化子をとり補題 4.3.5・4.3.6 |
| 4.4.1 | 定理 | 単発逆定理 $\log M \le I(\mathrm{Msg};Y) + H_b(P_e) + P_e\log(M-1)$ | `shannon_converse_single_shot` | 定理 1.3.4＋定理 1.10.1＋定理 1.8.2 |
| 4.4.2 | 系 | 符号化器を通した形 $\log M \le I(X;Y) + \dots$ | `shannon_converse_single_shot_markov_encoder` | 定理 1.8.4 |
| 4.4.3 | 定理 | チェイン則分解形 $\log M \le \sum_i I(X_i;Y^n\mid X^{<i}) + \dots$ | `channel_coding_converse_general_chainRule` | 定理 1.5.2 |
| 4.4.4 | 定義 | 記憶のない通信路（条件付き独立の形） | `IsMemorylessChannel` | — |
| 4.4.5 | 定理 | 無記憶完全形 $\log M \le \sum_i I(X_i;Y_i) + H_b(P_e) + P_e\log(M-1)$ | `channel_coding_converse_general_memoryless_pure` | 定理 1.8.5 |
| 4.4.6 | 系 | 弱逆定理: 達成可能なレートは $C$ 以下 | なし (a) | 定理 4.4.5 と命題 4.1.3、$P_e \to 0$ |
| 4.5.1 | 定義 | フィードバック符号（時刻 $i$ の入力が過去の出力に依存してよい） | なし (c) | — |
| 4.5.2 | 定義 | 無記憶・因果フィードバック | `IsMemorylessFeedback` | — |
| 4.5.3 | 補題 | per-letter 評価 $I(\mathrm{Msg};Y_i\mid Y^{<i}) \le I(X_i;Y_i)$ | `feedback_per_letter_bound` | 定理 1.8.4 を $(Y^{<i},\mathrm{Msg}) \to X_i \to Y_i$ に当てる |
| 4.5.4 | 定理 | 各時刻の相互情報量が $C$ 以下なら $\log M \le nC + H_b(P_e) + P_e\log(M-1)$ | `channel_coding_feedback_converse_memoryless` | 補題 4.5.3＋定理 1.5.2＋定理 1.10.1 |
| 4.5.5 | 系 | フィードバックは容量を増やさない | なし (a) | 定理 4.5.4 と定理 4.3.7 |
| 4.6.1 | 補題 | 点質量へ向かう線分に沿った $I$ の右微分は $D(W(\cdot\mid a)\|q_p) - I(p)$ | `mutualInfo_segment_hasDerivAt` | 有限和の項別微分（借用 B5） |
| 4.6.2 | 命題 | 容量達成条件: 最大化子 $p^*$ の出力 $q^*$ に対し $\forall a,\; D(W(\cdot\mid a)\|q^*) \le C$ | `klDiv_channel_le_capacity` | 補題 4.6.1 の右微分が $\le 0$ |
| 4.6.3 | 定義 | 情報密度 $i(x^n;y^n) = \log\frac{W^n(y^n\mid x^n)}{Q^n(y^n)}$ | なし (c) | — |
| 4.6.4 | 定義 | 高情報密度集合 | `highLLRSet` | — |
| 4.6.5 | 補題 | 符号語ごとの分解 $P^n_m(s) \le e^t Q^n(s) + P^n_m(\text{高情報密度})$ | `channelCoding_per_codeword_decomposition` | 集合の分割 |
| 4.6.6 | 定理 | 平均成功確率 $\le e^{\gamma}/M + \frac1M\sum_m P^n_m(\text{高情報密度})$ | `channelCoding_average_success_le` | 復号領域が分割をなすこと |
| 4.6.7 | 補題 | 高情報密度集合の確率は $O(1/n)$ で 0 に向かう | `llrUnifBound` `channelCoding_highLLR_tendsto_zero` | 命題 4.6.2 で平均を $C$ で抑え Chebyshev（借用 B4） |
| 4.6.8 | 定理 | 強逆定理: $R > C$ なら $P_e \to 1$ | `channelCoding_strong_converse_asymptotic` | 定理 4.6.6＋補題 4.6.7 |
| 4.6.9 | 系 | 達成可能レートは容量以下（強逆定理経由） | `channelCoding_operational_rate_le_capacity` | 定理 4.6.8 の対偶 |
| 4.7.1 | 定義 | ブロック通信路（無記憶とは限らない） | `BlockwiseChannel` `BlockwiseChannel.ofMemoryless` `Channel.toBlock` | — |
| 4.7.2 | 定義 | 極限としての容量 $C_\infty = \lim_n \frac1n C_n$ | `BlockwiseChannel.capacityN` `capacityRate` `capacity_lim` | — |
| 4.7.3 | 命題 | 無記憶なら $\frac1n C_n$ は途中から定数 $C$ | `capacityRate_ofMemoryless_eventually_const` `capacity_lim_tendsto_of_memoryless` | 定理 1.8.5＋定理 1.5.3 |
| 4.7.4 | 定理 | 無記憶なら $C_\infty = C$ | `capacity_lim_eq_capacity_of_memoryless` | 命題 4.7.3 |

番号の自己検査: 4.1 は 1–9、4.2 は 1–6、4.3 は 1–7、4.4 は 1–6、4.5 は 1–5、
4.6 は 1–9、4.7 は 1–4。飛びも重複もない。

### 依存関係と前方参照の検査

各節が使う既出番号（本文で `定理 1.2.3` の形で引く。第1〜3章の番号は原稿から確認済み）。

- **4.1** ← 定義 1.1.1、例 1.1.2（$H_b$）、定理 1.1.5、定義 1.2.2、定理 1.2.3、
  命題 1.3.2、定義 1.3.1、定理 1.3.4
- **4.2** ← 4.1（$I(p;W)$、$C$）、定義 2.2.1、定理 2.2.3、定理 2.2.4、定理 2.2.5、
  定義 2.3.1（ブロック情報源符号との対比のためだけに引く）
- **4.3** ← 4.2 全部、定理 4.1.5
- **4.4** ← 定理 1.1.5、定理 1.5.1、定理 1.5.2、定義 1.4.1、命題 1.4.2、定理 1.8.2、
  定理 1.8.4、定理 1.8.5、定理 1.10.1、定義 4.2.1、定義 4.2.2、命題 4.1.3
- **4.5** ← 定義 1.8.3、定理 1.5.2、定理 1.8.4、定理 1.10.1、4.4 の道具、定理 4.3.7
- **4.6** ← 定理 1.6.1、定義 4.1.4、定理 4.1.5、定義 4.2.1、定義 4.2.2
- **4.7** ← 定理 1.5.3、定理 1.8.5、定義 4.1.4

後方（未履修）への依存はゼロ。予告してよいもの（§2 の従の補足）:
4.1 節末で「容量を達成する入力分布の見分け方は 4.6 節で与える」、
4.4 節末で「$P_e \to 0$ を仮定しない形は 4.6 節」。どちらも削っても節が成立する。

### 借用宣言

§1 の 4 点（名前・依存範囲・主張の形・射程）をそろえて書く。

- **B1（4.1 節で宣言）** Weierstrass の最大値定理。形: 「コンパクト集合上の実数値連続
  関数は最大値をとる」。射程: 有限次元実ベクトル空間の有界閉集合＝確率単体
  $\{p : \mathcal X \to \mathbb R_{\ge0} \mid \sum_x p(x) = 1\}$ 上の実数値関数。
  依存範囲: 定理 4.1.5 のみ。$I(\cdot;W)$ の連続性は $\varphi(t) = -t\log t$ の
  $[0,1]$ 上の連続性（1.1 節の信頼の底の一部）から本文で組み立てる。
- **B2（4.2 節で宣言）** 大数の法則は本章では直接使わない。第2章の定理 2.1.4・
  定理 2.2.3 を積アルファベット $\mathcal X\times\mathcal Y$ 上の i.i.d. 情報源に
  当てる形でのみ用いる、と書く（借用ではなく射程の宣言）。
- **B4（4.6 節で宣言）** Chebyshev の不等式。形: 「$\mathbb E[Z]=\mu$、
  $\mathrm{Var}(Z) = \sigma^2$ のとき $\Pr[|Z-\mu| \ge t] \le \sigma^2/t^2$」。
  射程: 有界な独立確率変数の有限和。依存範囲: 補題 4.6.7 のみ。
  （マルコフの不等式は補題 3.5.3 の証明で既に使われているので、新たな宣言は要らない。）
- **B5（4.6 節で宣言）** 有限和の項別微分と片側微分。形: 「有限個の微分可能関数の和は
  微分可能で、導関数は各項の導関数の和」。射程: $t \in [0,1]$ に対する
  $t \mapsto \varphi\big((1-t)q(b) + tW(b\mid a)\big)$ の $t = 0$ での右微分（$q(b) > 0$ が要る）。
  依存範囲: 補題 4.6.1 のみ。

**章を書き終えたら照合する**（§1）: 「Weierstrass」「Chebyshev」「大数」で章内を検索し、
宣言した依存範囲の外に使用がないことを確かめる。

## 第5章の設計

### 節分割

`docs/textbook/ch05-max-entropy.md` を削除し `docs/textbook/ch05/` を作る。

| ファイル | 節 | タイトル | 想定行数 |
|---|---|---|---|
| `ch05/01-problem.md` | 5.1 | 最大エントロピー問題 | 130 |
| `ch05/02-gibbs.md` | 5.2 | モーメント制約と Gibbs 分布 | 220 |
| `ch05/03-partition-function.md` | 5.3 | 分配関数と Legendre 双対 | 160 |
| `ch05/04-multiplier.md` | 5.4 | Lagrange 乗数の存在 | 150 |

合計 660 行。**5.1 節で $\log$ を自然対数に固定する**（§6 の「底を固定する必要が章の
どこかで生じたら、章の最初の節で 1 度だけ断る」）。理由は Gibbs 分布が
$\exp\langle\lambda,f\rangle$ の形をしていて、恒等式が成り立つには $\log$ と $\exp$ が
互いに逆でなければならないため。単位はナット。ビットで読みたい箇所では例の中で換算する。

### 主張の番号表

| 番号 | 種別 | 主張 | 形ポ | 証明の方針 |
|---|---|---|---|---|
| 5.1.1 | 定義 | 特徴 $f_1,\dots,f_k$、モーメント制約 $\mathbb E_P[f_i]=c_i$、実行可能集合 | なし (c) | — |
| 5.1.2 | 命題 | $D(P\|U) = \log|\mathcal X| - H(P)$（$U$ は一様分布） | `klDiv_uniformOn_univ_toReal_eq` | 定義 1.6.x を書き下す |
| 5.1.3 | 系 | 実行可能集合上で $H$ を最大化することは $D(\cdot\|U)$ を最小化することと同じ | なし (a) | 命題 5.1.2 |
| 5.1.4 | 例 | サイコロ: $\mathcal X=\{1,\dots,6\}$、$f(x)=x$、$c=4.5$（問題の設定だけ） | なし (c) | — |
| 5.2.1 | 定義 | 分配関数 $Z(\lambda)$ と Gibbs 分布 $p^*_\lambda$ | `gibbsZ` `gibbsPmf` | — |
| 5.2.2 | 命題 | $p^*_\lambda$ は全点で正の pmf | `gibbsPmf_pos` `gibbsPmf_mem_stdSimplex` | 定義を書き下す |
| 5.2.3 | 補題 | 核の恒等式 $D(Q\|p^*_\lambda) = -H(Q) - \langle\lambda,\mathbb E_Q[f]\rangle + \log Z(\lambda)$ | `klDivPmf_gibbsPmf_eq` | $\log p^*_\lambda$ を代入 |
| 5.2.4 | 系 | 実行可能な $P$ と実行可能な $p^*_\lambda$ に対し $H(p^*_\lambda) - H(P) = D(P\|p^*_\lambda)$ | なし (a) | 補題 5.2.3 を $Q=P$ と $Q=p^*_\lambda$ で評価して差をとる |
| 5.2.5 | 定理 | 最大エントロピー定理: 実行可能な $P$ について $H(P) \le H(p^*_\lambda)$ | `entropy_le_gibbs_of_constraints` | 系 5.2.4 と定理 1.6.1 |
| 5.2.6 | 定理 | 等号は $P = p^*_\lambda$ のときに限る | `entropy_eq_gibbs_iff_of_constraints` | 系 5.2.4 と定理 1.6.1 の等号条件 |
| 5.2.7 | 例 | 制約が空なら $p^* = $ 一様、$H = \log|\mathcal X|$ | `gibbsPmf_zero_eq_uniform` `entropy_gibbsPmf_zero_eq_log_card` | 定義に $f\equiv0$ を代入 |
| 5.2.8 | 例 | 二値・平均制約 $\mu$ なら $p^*=(\mu,1-\mu)$、$H = H_b(\mu)$ | `boolFeature` `entropy_gibbsPmf_bool_eq_binEntropy` | 制約から $p^*(\text{true})=\mu$ |
| 5.3.1 | 定義 | 対数分配関数 $\psi(\lambda)=\log Z(\lambda)$ と指数型族 | `logPartitionψ` `expFamilyDist` | — |
| 5.3.2 | 命題 | 指数型族と Gibbs 分布は各点で一致する | `expFamilyDist_eq_gibbsPmf` | $\exp$ の加法性 |
| 5.3.3 | 定理 | Legendre 恒等式 $H(p^*_\lambda) = \psi(\lambda) - \langle\lambda,c\rangle$ | `KKTSolution` `entropy_expFamilyDist_eq_legendre` | 補題 5.2.3 に $Q=p^*_\lambda$ |
| 5.3.4 | 定理 | 変分上界: 実行可能な $P$ について $H(P) \le \psi(\lambda) - \langle\lambda,c\rangle$ | `entropy_le_logPartition_sub_inner` | 定理 5.2.5＋定理 5.3.3 |
| 5.3.5 | 例 | 線形特徴 $f(x)=x$ の Gibbs 分布は等比の形 $q^x/\sum_y q^y$ | `linearFeature` `gibbsPmf_linearFeature_eq_geometric` | $q := e^{\lambda}$ と置く |
| 5.4.1 | 命題 | $\partial\psi/\partial\lambda_i = \mathbb E_{p^*_\lambda}[f_i]$ | なし (c) | 有限和の項別微分（借用 B7） |
| 5.4.2 | 命題 | $\psi$ は凸。直線 $\lambda + tv$ に沿った 2 階微分は $\mathrm{Var}_{p^*}(\langle v,f\rangle)$ | なし (c) | 命題 5.4.1 をもう一度微分 |
| 5.4.3 | 定理 | $k=1$、$f$ が定数でないとき、$c \in (\min f, \max f)$ なら制約整合な $\lambda$ が唯一存在する | なし (c) | $m(\lambda)=\psi'(\lambda)$ は狭義単調連続、極限が $\min f$ と $\max f$、中間値の定理（借用 B6） |
| 5.4.4 | 例 | 二値・平均 $\mu \in (0,1)$: $\lambda = \log\frac{\mu}{1-\mu}$ | なし (c) | 直接解く |
| 5.4.5 | 例 | 境界 $c = \max f$: Gibbs 形では届かず、最大化分布は $\operatorname{argmax} f$ 上の一様分布 | なし (c) | 実行可能集合が $\operatorname{argmax} f$ 上の分布に限ることを示し、定理 1.1.5 |

番号の自己検査: 5.1 は 1–4、5.2 は 1–8、5.3 は 1–5、5.4 は 1–5。飛びも重複もない。

**数値の確認**（本文に書く前に計算済み）: サイコロ $c=4.5$ に対し $\lambda \approx 0.371$
（自然対数）、$p^* \approx (0.0544, 0.0788, 0.1142, 0.1654, 0.2398, 0.3475)$、
$H(p^*) \approx 1.614$ ナット（$\approx 2.328$ ビット）、一様分布は $\log 6 \approx 1.792$
ナット（$\approx 2.585$ ビット）。二値の $\mu=0.9$ で $\lambda = \log 9 \approx 2.197$、
$H_b(0.9) \approx 0.469$ ビット。第4章側は $H_b(0.1)\approx0.469$ より
二元対称通信路 $p=0.1$ の容量 $\approx 0.531$ ビット、$p=0.11$ で $\approx 0.500$ ビット。

### 依存関係と前方参照の検査

- **5.1** ← 定義 1.1.1、例 1.1.3、定理 1.1.5、1.6 節の相対エントロピーの定義
- **5.2** ← 5.1、定理 1.6.1（非負性と等号条件）
- **5.3** ← 5.2
- **5.4** ← 5.3（$\psi$）、例 1.1.2（$H_b$）、定理 1.1.5（例 5.4.5）

後方への依存はゼロ。**第1章の定理 1.1.5 を第5章で再掲しない**（§8 の番号の一意性）。
5.1 節は既出の定理として引くだけで、新しい番号を与えない。

### 借用宣言

- **B6（5.4 節で宣言）** 中間値の定理。形: 「区間上の連続関数は、両端の値のあいだの
  値をすべてとる」。射程: $\mathbb R$ 全体で定義された実数値関数 $m(\lambda)$。
  依存範囲: 定理 5.4.3 のみ。
- **B7（5.4 節で宣言）** 有限和の項別微分（2 階まで）。形: 「有限個の微分可能関数の和は
  微分可能で、導関数は各項の導関数の和。商の微分も同様」。射程:
  $\lambda \mapsto \sum_x e^{\langle\lambda,f(x)\rangle}$ とその商。
  依存範囲: 命題 5.4.1・命題 5.4.2 のみ。

## 用語

新しく名づける語と、外の標準名との突き合わせ（§6「本書が名づける語」）。
節タイトル・主張名・定義した太字だけを対象にした。

| 本書の語 | 判定 |
|---|---|
| 通信路 / 離散無記憶通信路 / 通信路容量 | 日本語の情報理論の教科書の標準語。そのまま |
| 通信路符号化定理 | 標準。第2章の情報源符号化定理と対になる |
| ブロック通信路符号 | 第2章の「ブロック情報源符号」と同じ形。標準の「(通信路)符号」を縮約していない |
| 二元対称通信路 / 二元消失通信路 | 標準。略語 BSC / BEC は導入しない（§6 規則 4） |
| 結合典型集合 | 「同時典型系列」も流通するが、本書は joint を「結合」で通している（結合エントロピー・結合分布）ので揃える |
| 達成可能レート | 第2章 定義 2.3.5 の語をそのまま通信路側に使う |
| 逆定理 / 弱逆定理 / 強逆定理 | 標準。第2章 定理 2.3.4 が「弱逆定理」なので対になる |
| ランダム符号化 | 標準 |
| 情報密度 | Verdú–Han の information density の標準訳 |
| フィードバック | 情報理論の日本語文献では「帰還」より優勢（§6 規則 2） |
| 最大エントロピー問題 / Gibbs 分布 / 分配関数 / 対数分配関数 / 指数型族 | すべて標準。Gibbs は第1章（定理 1.6.1 の名前）で既にラテン文字 |
| Lagrange 乗数 / Legendre 双対 | 人名はラテン文字（§6 規則 3） |

`terminology.mjs` の追加候補（ファイルは編集しない。原稿を書きながら割れたら足す）:

1. `use: 'Lagrange'`, `avoid: ['ラグランジュ']` — Jensen / Cauchy / Gibbs / Birkhoff と同じ規則。
2. `use: 'Legendre'`, `avoid: ['ルジャンドル']` — 同上。
3. `use: 'フィードバック'`, `avoid: ['帰還']` — 分野の慣行。
4. `use: '結合典型集合'`, `avoid: ['同時典型']` — 本書の joint = 結合 に揃える。
5. `use: 'Lagrange 乗数'`, `avoid: ['KKT']` — 略語を導入しない（§6 規則 4）。
   `KKTSolution` は行内 code なので検査に当たらない。

**既存行の修正が 1 つ必要**: `相対エントロピー` の `except` に
`'ch05-max-entropy.md'` があるが、このファイルは消える。新しい第5章は
相対エントロピーで通すので、この免除を**削除**する（残すと dead な except になる）。

## 執筆エージェントへの申し送り

- **`::: formalized` を付けてよいのは上の番号表の「形ポ」欄に宣言名がある主張だけ。**
  欄が「なし」の主張には絶対に付けない。とくに次を間違えやすい:
  - 系 4.4.6・系 4.5.5・系 5.2.4 は**合成でしか得られない**。`::: formalization-note` に
    「単独の宣言はなく、どれとどれの合成か」を書く（§7）。
  - `channel_coding_feedback_converse` とその仲間（`ChannelCoding/Feedback.lean`）は
    per-letter 評価を仮説に取る MVP。**原稿に名前を出さない**。
  - 5.4 節はどの主張も形式化されていない。節の借用宣言のあとに注記を 1 つ置き、
    「本書は証明するが形式化はされていない」と書く（§7 の書き分け）。
- **`::: formalized` には宣言名とファイルパスを必ず併記する。** `capacity_lim` /
  `capacity_lim_eq_capacity_of_memoryless` / `Channel` / `Code` / `errorProbAt` /
  `averageErrorProb` / `IsMemorylessChannel` は同じ短い名前が repo 内に複数あるので、
  パスがないとビルドが `N 箇所にある` で warn を出す。パスは「Lean 資産の棚卸し」の表からそのまま写す。
- **行番号を書かない。Lean のシグネチャを本文にも数式にも入れない**（§7）。草稿は
  両方をやっている。書き直しでは宣言名とパスだけを行内 code で書く。
- **底の扱いが章で違う。** 第4章は $2^{nR}$ を使うので 4.1 節で $\log$ の底を 2 に固定する
  （第2・3章と同じ）。Lean 側は自然対数・`Real.exp` なので、4.1 節に注記を 1 つ置いて
  「底をそろえれば同じ主張」と書く（ch03/02-entropy-rate.md の注記が前例）。
  第5章は逆に 5.1 節で自然対数に固定する（Gibbs 分布の $\exp$ と噛み合わせるため）。
  **章をまたいで同じ断りを繰り返さない**（§6）。
- **第5章の主張ブロックには λ の仮定を必ず書く**（「その $\lambda$ の Gibbs 分布が同じ
  制約を満たすとき」）。これを落とすと「存在まで証明済み」と読まれる。
  §5 の「主張の中の自由変数は主張の中で量化する」がそのまま効く。
- **第4章の逆定理群はメッセージが一様分布であることを仮定に持つ。** 主張ブロックに
  書く。第2章 定理 2.3.4 が置いていない仮定なので、落とすと第2章との差が見えない。
- **例は数値を確かめてから置く**（§4）。上の「数値の確認」の値は計算済みなので、
  それ以外の数値を足すときは同じことをする。
- **書き終えたら回すもの**: `deno run -A docs/textbook/site/build.mjs`
  （`warn: 証明のない主張` / `未解決の参照` / `種別のない参照` / `番号の重複` /
  `自節への参照` / `表記ゆれ` / `形式化ポインタ` がすべて 0 件）、
  `--audit-refs`（残るのが数値だけであること）、
  `./docs/textbook/site/vocab.ts ch04` と `ch05`（原語混入 0 件、名づけた語を目で読む）。
- **`build.mjs` の `chapters` 配列と、旧 1 ファイル原稿の削除を忘れない。**
  `status` は第1〜3章に合わせて `'仕上げ済'` にする。
- **書き終えたら `.claude/rules/textbook-writing.md` §11 の乖離表から第4・5章の列を消す**
  （全章が基準実装に揃うため）。§0 のとおり、書きながら下した判断は原稿に埋める前に
  §11 ではなく該当の節へ 1 項足す。
