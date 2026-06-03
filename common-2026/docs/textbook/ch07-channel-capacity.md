# 第7章 通信路容量 (Channel Capacity)

> **このファイルについて**
>
> 本章は Cover & Thomas *Elements of Information Theory* (2nd ed.) Chapter 7
> (Channel Capacity) を題材に、**検証済み Lean 定理を骨格にした教科書原稿**である。
> 本文の各主要結果には「**Verified**: `定理名` (`InformationTheory/...`)」という形で、
> その命題に対応する Lean 4 + Mathlib の formal declaration を紐付けてある。
> 第2章 (`ch02-entropy.md`) の形式を踏襲する。
>
> **検証強度の注記** — 本章で `**Verified**` と記した定理はすべて、本プロジェクトの
> 完成判定 **proof done**（当該 declaration のファイルが `0 sorry` かつ `0 @residual`、
> すなわち無条件機械検証済み）を満たす。紐付けた定理が属するファイル
> (`ChannelCoding.lean` / `Converse.lean` / `ChannelCodingConverse.lean` /
> `ChannelCodingConverseGeneral.lean` / `ChannelCodingConverseMemorylessPure.lean` /
> `ChannelCodingStrongConverse.lean` / `ChannelCodingFeedbackComplete.lean` /
> `GeneralDMC.lean` / `BlockwiseChannel.lean`) は本作成時点で `sorry` /
> `@residual` を含まない。
> `ChannelCodingShannonTheorem.lean` の達成可能性主定理 `shannon_noisy_channel_coding_theorem`
> も実体は完全に証明済み（proof done）である（ファイル冒頭 docstring に残る
> 「Phase B-D は skeleton `:= by sorry`」は実コードと乖離した **stale な記述**であり、
> 実際には proof body に `sorry` / `admit` は存在しない。詳細は「所見」を参照）。
>
> **形式化の枠組み** — 本ライブラリでは離散無記憶通信路 (DMC) を Mathlib の
> Markov カーネル `W : Kernel α β` (`[IsMarkovKernel W]`) として表現する
> （`Channel α β := Kernel α β`）。入力分布 `p : Measure α` のもとでの結合分布は
> `p ⊗ₘ W`（`Measure.compProd`）、通信路相互情報量は像測度に対する `klDiv` で定義する。
> ブロック符号 `Code M n α β` は encoder `Fin M → (Fin n → α)` + decoder
> `(Fin n → β) → Fin M` の bundle、ブロック通信路 `W^n` は積測度
> `Measure.pi (fun i => W (c.encoder m i))` で表す。アルファベット `α`, `β` は有限型。
> 対応する Lean library は `InformationTheory/Shannon/` の channel-coding 群。

---

## 7.1 通信路容量の定義 (Channel Capacity of a DMC)

離散無記憶通信路 (DMC) は遷移確率 \(W(y \mid x)\) で与えられ、本ライブラリでは
Markov カーネル `W : Channel α β` として扱う。入力分布 \(p(x)\) のもとでの
結合分布 \((X, Y) \sim p \otimes W\)、出力分布 \(q(y) = \sum_x p(x) W(y \mid x)\)、
通信路相互情報量は

\[
I(X; Y) = D\!\left(p \otimes W \,\big\|\, p \otimes q\right).
\]

**Verified (定義)**: `mutualInfoOfChannel` (`InformationTheory/Shannon/ChannelCoding.lean`,
名前空間 `InformationTheory.Shannon.ChannelCoding`)

```lean
noncomputable def mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞ :=
  klDiv (jointDistribution p W) (p.prod (outputDistribution p W))
```

これは結合座標の標準的相互情報量と一致し、さらに3項エントロピー形に展開できる。

**Verified**: `mutualInfoOfChannel_eq_mutualInfo_prod` /
`mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` (`InformationTheory/Shannon/ChannelCoding.lean`)

```lean
theorem mutualInfoOfChannel_eq_HX_add_HY_sub_HZ
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    (mutualInfoOfChannel p W).toReal
      = InformationTheory.Shannon.entropy (jointDistribution p W) Prod.fst
        + InformationTheory.Shannon.entropy (jointDistribution p W) Prod.snd
        - InformationTheory.Shannon.entropy (jointDistribution p W) id
```

### 通信路容量 \(C = \max_{p(x)} I(X; Y)\)

通信路容量は入力分布上の相互情報量の上限（有限アルファベットでは最大値）として定義する。

\[
C = \max_{p(x)} I(X; Y).
\]

本ライブラリでは入力 pmf を確率単体 `stdSimplex ℝ α` の元として表し、その上の
`I(p; W).toReal` の `sSup` を容量とする。

**Verified (定義)**: `capacity` (`InformationTheory/Shannon/ChannelCodingShannonTheorem.lean`,
名前空間 `InformationTheory.Shannon.ChannelCoding`)

```lean
noncomputable def capacity (W : Channel α β) : ℝ :=
  sSup ((fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal) ''
        stdSimplex ℝ α)
```

容量はwell-defined（値集合が空でなく上に有界）かつ非負であり、最大値を達成する
入力分布が存在する（`sSup` が上限ではなく最大値であること）。

**Verified**: `capacity_nonneg` / `capacity_bddAbove` / `exists_capacity_achiever`
(`InformationTheory/Shannon/ChannelCodingShannonTheorem.lean`)

```lean
theorem capacity_nonneg (W : Channel α β) [IsMarkovKernel W] : 0 ≤ capacity W

theorem capacity_bddAbove (W : Channel α β) [IsMarkovKernel W] :
    BddAbove ((fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal) ''
      stdSimplex ℝ α)

theorem exists_capacity_achiever (W : Channel α β) [IsMarkovKernel W] :
    ∃ p ∈ stdSimplex ℝ α, (mutualInfoOfChannel (pmfToMeasure p) W).toReal = capacity W
```

---

## 7.5 通信路符号化定理 — 達成可能性 (Channel Coding Theorem, Achievability)

シャノンの通信路符号化定理（達成可能性）：レート \(R < C\) であれば、十分大きな
ブロック長 \(n\) に対し、誤り確率を任意に小さくできる符号 \((M, n)\)
（\(M \ge e^{nR}\)）が存在する。

\[
R < C \implies \forall \varepsilon > 0,\ \exists\, n_0,\ \forall n \ge n_0,\
\exists\, \text{code}\ (M \ge e^{nR}, n)\ \text{s.t.}\ P_e^{(n)} < \varepsilon.
\]

本ライブラリでは、入力分布最大化（容量達成 pmf 抽出）+ 相互情報量の連続性
（pmf の平滑化 `pSmooth` による正値化）+ 結合典型集合に対する AEP 評価を組み合わせ、
**最大誤り確率**（メッセージ最悪値）を `ε` 未満にする符号系列を構成する。

**Verified**: `shannon_noisy_channel_coding_theorem`
(`InformationTheory/Shannon/ChannelCodingShannonTheorem.lean`)

```lean
theorem shannon_noisy_channel_coding_theorem
    (W : Channel α β) [IsMarkovKernel W]
    (hW_pos : ∀ a : α, ∀ b : β, 0 < (W a).real {b})
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε
```

ここで仮定 `hW_pos`（通信路が各出力記号に正の確率を割り当てる、full-support）は
AEP/典型集合構成のための **regularity 前提条件** であり、結論の核心を抱えさせる
load-bearing 仮定ではない。`R < capacity W` がレート条件、`errorProbAt` が
点ごとの誤り確率である。

### 達成可能性の道具: 結合典型集合 (Jointly Typical Set)

達成可能性の証明骨格は結合典型集合のサイズ上界（\(\le e^{n(H(X,Y)+\varepsilon)}\)）と、
真の組が典型集合に入る確率が 1 に収束すること、独立な組が典型集合に入る確率が
\(e^{-n(I-3\varepsilon)}\) 程度に抑えられること（誤デコードの確率評価）からなる。

**Verified**: `jointlyTypicalSet_card_le` / `jointlyTypicalSet_prob_tendsto_one` /
`jointlyTypicalSet_indep_prob_le` (`InformationTheory/Shannon/ChannelCoding.lean`)

```lean
theorem jointlyTypicalSet_card_le
    [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hpos : ∀ p : α × β, 0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((jointlyTypicalSet μ Xs Ys n ε).toFinite.toFinset.card : ℝ) ≤
      Real.exp ((n : ℝ) *
        (InformationTheory.Shannon.entropy μ (jointSequence Xs Ys 0) + ε))
```

---

## 7.9 ファノ不等式と逆定理 (Fano's Inequality and the Converse)

逆定理（converse）：信頼できる通信にはレートが容量を超えないこと \(R \le C\) が必要。
証明の核はファノ不等式と相互情報量のデータ処理不等式・チェイン則である。

### 単発逆定理 (Single-shot converse)

一様メッセージ \(\mathrm{Msg}\)、通信路出力 \(Y\)、復号器 \(\hat M = \mathrm{decoder}(Y)\)、
誤り確率 \(P_e\) に対し

\[
\log |M| \le I(\mathrm{Msg}; Y) + H_b(P_e) + P_e \log(|M| - 1).
\]

ファノ不等式 + データ処理不等式（後処理 \(Y \to \hat M\) で相互情報量は減る）+
一様分布のエントロピーが \(\log|M|\) であることから直接導く。

**Verified**: `shannon_converse_single_shot` (`InformationTheory/Shannon/Converse.lean`,
名前空間 `InformationTheory.Shannon`)

```lean
theorem shannon_converse_single_shot
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Yo : Ω → Y) (decoder : Y → M)
    (hMsg : Measurable Msg) (hYo : Measurable Yo) (hdecoder : Measurable decoder)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ Msg Yo ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (mutualInfo μ Msg Yo).toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg Yo decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg Yo decoder *
          Real.log ((Fintype.card M : ℝ) - 1)
```

### i.i.d. 入力の逆定理 (n-letter form)

\(n\) 回使用・i.i.d. 入力では \(I(X^n; Y^n) = n\, I(X_0; Y_0)\) に圧縮され、

\[
\log |M| \le n\, I(X_0; Y_0) + H_b(P_e) + P_e \log(|M| - 1).
\]

**Verified**: `channel_coding_converse_iid`
(`InformationTheory/Shannon/ChannelCodingConverse.lean`, 名前空間 `InformationTheory.Shannon`)

```lean
theorem channel_coding_converse_iid
    {n : ℕ} (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (h_iid_joint : ...) (h_iid_X : ...) (h_iid_Y : ...)
    (h_copy : ...) (h_copy_X : ...) (h_copy_Y : ...)
    (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (n : ℝ) * (mutualInfo μ
        (fun ω => encoder (Msg ω) ⟨0, hn⟩) (Ys ⟨0, hn⟩)).toReal +
        Real.binEntropy (InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1)
```

ここで Markov chain 仮定 `hmarkov` (`Msg → encoder ∘ Msg → Y^n`) と i.i.d. 構造仮定
`h_iid_*` / `h_copy_*` は通信路・入力分布の構造を表す前提条件であり、完全式はソース
`ChannelCodingConverse.lean:58` を参照。

### 一般入力の逆定理 — チェイン則分解 (no i.i.d. assumption)

i.i.d. 仮定を外し、相互情報量のチェイン則で \(I(X^n; Y^n)\) を各時刻の条件付き
相互情報量の和に分解した形：

\[
\log |M| \le \sum_i I(X_i; Y^n \mid X^{<i}) + H_b(P_e) + P_e \log(|M| - 1).
\]

**Verified**: `channel_coding_converse_general_chainRule`
(`InformationTheory/Shannon/ChannelCodingConverseGeneral.lean`,
名前空間 `InformationTheory.Shannon`)

```lean
theorem channel_coding_converse_general_chainRule
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (∑ i : Fin n,
        (condMutualInfo μ
          (fun ω => encoder (Msg ω) i)
          (fun ω j => Ys j ω)
          (fun ω (j : Fin i.val) =>
            encoder (Msg ω) ⟨j.val, j.isLt.trans i.isLt⟩)).toReal) +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1)
```

### 無記憶通信路の完全形 (Cover-Thomas Thm 7.9, memoryless)

無記憶通信路 `IsMemorylessChannel` の仮定を加えると、各和項に対する per-letter 評価
\(I(X_i; Y^n \mid X^{<i}) \le I(X_i; Y_i)\) が成立し、教科書 7.9 の完全形

\[
\log |M| \le \sum_i I(X_i; Y_i) + H_b(P_e) + P_e \log(|M| - 1)
\]

に到達する。per-letter Markov chain は無記憶性から内部で自動派生する。

**Verified**: `channel_coding_converse_general_memoryless_pure`
(`InformationTheory/Shannon/ChannelCodingConverseMemorylessPure.lean`,
名前空間 `InformationTheory.Shannon.ChannelCodingConverseGeneral`)

```lean
theorem channel_coding_converse_general_memoryless_pure
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : Shannon.IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (h_memo : IsMemorylessChannel μ (fun i ω => encoder (Msg ω) i) Ys)
    (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : Shannon.mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (∑ i : Fin n,
        (Shannon.mutualInfo μ
          (fun ω => encoder (Msg ω) i) (Ys i)).toReal) +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1)
```

`h_memo : IsMemorylessChannel ...` は通信路が無記憶であるという構造前提（precondition）
であり、結論の核心を抱えさせる load-bearing 仮定ではない。

---

## 7.12 フィードバック容量 (Feedback Capacity)

フィードバックは DMC の容量を増やさない \(C_{FB} = C\)。逆定理側の核心は、
無記憶・因果的フィードバック下で per-letter 評価 \(I(\mathrm{Msg}; Y_i \mid Y^{<i}) \le I(X_i; Y_i)\)
が成り立つことであり、これとファノ不等式を合成すると \(\log|M| \le nC + H_b(P_e) + P_e\log(|M|-1)\)
が得られる（フィードバックがあってもレートは \(C\) で頭打ち）。

### Per-letter 評価とフィードバック逆定理

無記憶・因果フィードバック `IsMemorylessFeedback`（\((Y^{<i}, \mathrm{Msg}) \to X_i \to Y_i\)
が Markov chain）のもとで per-letter 評価が成立する。

**Verified**: `feedback_per_letter_bound`
(`InformationTheory/Shannon/ChannelCodingFeedbackComplete.lean`,
名前空間 `InformationTheory.Shannon.ChannelCodingFeedback`)

```lean
theorem feedback_per_letter_bound
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hMsg : Measurable Msg)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_memo : IsMemorylessFeedback μ Msg Xs Ys) :
    ∀ i : Fin n,
      Shannon.condMutualInfo μ Msg (Ys i)
          (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        ≤ Shannon.mutualInfo μ (Xs i) (Ys i)
```

per-letter 評価とファノを合成したフィードバック逆定理（無記憶完全形）：

\[
\log |M| \le n\, C + H_b(P_e) + P_e \log(|M| - 1).
\]

**Verified**: `channel_coding_feedback_converse_memoryless`
(`InformationTheory/Shannon/ChannelCodingFeedbackComplete.lean`)

```lean
theorem channel_coding_feedback_converse_memoryless
    {n : ℕ} (C : ℝ≥0∞) (hC_finite : C ≠ ∞)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (h_memo : IsMemorylessFeedback μ Msg Xs Ys)
    (h_capacity : ∀ i : Fin n, Shannon.mutualInfo μ (Xs i) (Ys i) ≤ C)
    (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M) :
    Real.log (Fintype.card M) ≤
      (n : ℝ) * C.toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1)
```

ここで `h_memo : IsMemorylessFeedback ...`（per-letter Markov chain 族）と
`h_capacity`（各時刻の相互情報量が容量 `C` 以下）はフィードバック通信路の
構造前提である。`C` を大域定義 \(\sup_p I(p;W)\) に縛らず任意の有限 `ℝ≥0∞` 値として
受け取り、呼び出し側が具体的容量を渡す設計。

---

## 7.* 強逆定理 — Verdú–Han 単発下界 (Strong Converse, single-shot)

強逆定理（Wolfowitz）：\(R > C\) では誤り確率が \(1\) に収束する。本ライブラリは
その核となる **情報密度 (information density) 型の単発下界**を Verdú–Han Lemma 4.2.2 の
形で形式化する。任意の符号 `c`、任意の参照出力分布 `Q^n`、しきい値
\(t = \log M + \gamma\) に対し、各符号語ごとの分解

\[
P_m^n(s) \le e^{t}\, Q^n(s) + P_m^n(\mathrm{highLLR}_m)
\]

から、平均成功確率の上界

\[
1 - \overline{P_e} \le e^{\gamma} \cdot \frac{1}{M} + \frac{1}{M}\sum_m P_m^n(\mathrm{highLLR}_m)
\]

を導く（第1項は復号領域が \(Q^n\) の分割をなすことで吸収）。

**Verified**: `channelCoding_per_codeword_decomposition` /
`channelCoding_average_success_le`
(`InformationTheory/Shannon/ChannelCodingStrongConverse.lean`,
名前空間 `InformationTheory.Shannon.ChannelCoding`)

```lean
theorem channelCoding_per_codeword_decomposition
    {M n : ℕ} (W : Channel α β) [IsMarkovKernel W] (c : Code M n α β)
    (Q : Measure (Fin n → β)) [IsFiniteMeasure Q]
    (threshold : ℝ) (m : Fin M)
    (s : Set (Fin n → β)) (hs : MeasurableSet s) :
    (Measure.pi (fun i => W (c.encoder m i))).real s
      ≤ Real.exp threshold * Q.real s
        + (Measure.pi (fun i => W (c.encoder m i))).real
            (highLLRSet W c Q threshold m)

theorem channelCoding_average_success_le
    {M : ℕ} (hM : 0 < M) {n : ℕ}
    (W : Channel α β) [IsMarkovKernel W] (c : Code M n α β)
    (Q : Measure (Fin n → β)) [IsProbabilityMeasure Q]
    (threshold : ℝ) :
    (1 - (c.averageErrorProb W).toReal)
      ≤ Real.exp threshold / M + (1 / M : ℝ) *
          ∑ m : Fin M, (Measure.pi (fun i => W (c.encoder m i))).real
            (highLLRSet W c Q threshold m)
```

参照出力分布 `Q^n` は i.i.d. 形に限らず任意の確率測度を取り、Verdú–Han の
deterministic 形を採用する。第2項の tail（high-LLR 集合質量）を \(0\) に飛ばす
asymptotic（\(P_e \to 1\)）は WLLN 段を要し、本ライブラリでは別ファイルに分離・
deferred（「未形式化の項目」参照）。

---

## 7.* 一般 DMC 容量 — 極限形と単一文字容量の一致 (General DMC capacity)

一般（ブロック単位）通信路 `BlockwiseChannel α β` に対し、容量を極限形
\(C_\infty = \lim_{n\to\infty} \frac{1}{n}\sup_p I(p; W_n)\) で定義し、無記憶の場合に
単一文字容量 \(C = \max_p I(X;Y)\) と一致することを示す。

**Verified (定義)**: `capacity_lim` / `capacityRate`
(`InformationTheory/Shannon/GeneralDMC.lean`, 名前空間 `InformationTheory.Shannon.GeneralDMC`)

```lean
noncomputable def capacity_lim (W : BlockwiseChannel α β) : ℝ :=
  BlockwiseChannel.capacity_lim W

noncomputable def capacityRate (W : BlockwiseChannel α β) (n : ℕ) : ℝ :=
  (W.capacityN n).toReal / n
```

無記憶通信路では極限形容量が単一文字容量に一致する（per-letter 容量列が
最終的に定数 `capacity W` に等しいため）。

**Verified**: `capacity_lim_eq_capacity_of_memoryless`
(`InformationTheory/Shannon/GeneralDMC.lean`、本体は
`InformationTheory/Shannon/BlockwiseChannel.lean`)

```lean
theorem capacity_lim_eq_capacity_of_memoryless
    (W : ChannelCoding.Channel α β) [IsMarkovKernel W] :
    capacity_lim (BlockwiseChannel.ofMemoryless W) = capacity W
```

per-letter 容量列の収束（Tendsto 形）も形式化済み：
**Verified**: `capacity_lim_tendsto_of_memoryless` /
`capacityRate_ofMemoryless_eventually_const` (`InformationTheory/Shannon/GeneralDMC.lean`)。

---

## 本章で未形式化の項目

Cover & Thomas Ch.7 のうち、本作成時点で proof done な独立定理を確認できなかった、
あるいは **sorry / load-bearing hypothesis を含むため `Verified` 引用から除外した**
項目を正直に記す。

- **7.5 達成可能性の `hW_pos` 完全除去版**: full-support 仮定 `hW_pos` を平滑化
  (`Channel.smooth W δ`) で除去する版 `shannon_noisy_channel_coding_theorem_general`
  (`ChannelCodingShannonTheoremFull.lean`) は確かにファイル単位では `0 sorry` だが、
  **その達成可能性の核心が load-bearing 仮定 `h_passthrough` に bundle されている**
  （per-`n` 系列の存在を仮定として受け取り、本体は TV bound での glue のみ）。docstring
  自身が `@audit:retract-candidate(superseded-by-full-discharge)` とマークしており、
  hypothesis-pass-through MVP である。本章では正直に `Verified` から除外し、
  full-support 前提付きの genuine な `shannon_noisy_channel_coding_theorem`
  (7.5 節) を達成可能性 headline として採用した。
- **強逆定理の asymptotic 形 \(P_e \to 1\)**: 7.* 節で引用した Verdú–Han 単発下界は
  proof done だが、high-LLR tail を WLLN で \(0\) に飛ばして \(P_e \to 1\) を結論する
  asymptotic 段は本ライブラリでは別 plan に deferred（本章では未形式化）。
- **7.2 対称通信路などの具体例 (二元対称通信路 BSC・二元消失通信路 BEC の容量計算)**:
  具体通信路の容量閉形式（例 \(C_{BSC} = 1 - H_b(p)\)）の独立定理は本章スコープで未確認
  （本章では未形式化）。
- **7.3 / 7.4 対称性・容量の凸性 / 凸最適化条件 (KKT)**: 入力分布上の \(I(p;W)\) の
  凹性や容量達成条件の独立定理化は本章では未確認（本章では未形式化）。
  なお `exists_capacity_achiever` で最大化子の存在のみは形式化済み。
- **7.7 / 7.8 結合典型性の定義・性質の網羅**: 達成可能性に必要な
  `jointlyTypicalSet_*` 3 評価は形式化済みだが、教科書の結合典型性のすべての性質を
  網羅したわけではない。
- **フィードバック逆定理の hypothesis 分離版 `channel_coding_feedback_converse` /
  `channel_coding_feedback_converse_capacity`** (`ChannelCodingFeedback.lean`):
  これらは proof done だが `@audit:retract-candidate(superseded-by-memoryless-form)`
  とマークされた MVP 形（per-letter 評価を仮説として受け取る）。本章では per-letter
  評価を内部派生する完全形 `channel_coding_feedback_converse_memoryless` を採用した。

---

## 所見（原稿生成の課題）

本章で顕在化した、roadmap・docstring ↔ 実コードの乖離と原稿化の課題を記録する。

1. **roadmap 代表名と実 declaration 名の乖離（指示どおり大）**: roadmap の Ch.7 行が
   挙げた `shannon_noisy_..._general_full` / `_feedback_complete` /
   `strong_converse_singleShot` はいずれも実在名ではなかった。実体は
   `shannon_noisy_channel_coding_theorem`（full-support 版、genuine）/
   `shannon_noisy_channel_coding_theorem_general`（`_general_full` ≈ pass-through MVP）/
   `channel_coding_feedback_converse_memoryless`（`_feedback_complete` ≈ 無記憶完全形）/
   `channelCoding_average_success_le` ＋ `..._decomposition`（`strong_converse_singleShot`
   ≈ Verdú–Han 単発下界）であり、すべて grep で実名特定が必須だった。

2. **docstring の stale な「sorry」記述が `rg -c sorry` を汚す**:
   `ChannelCodingShannonTheorem.lean` は冒頭 docstring に「Phase B-D は skeleton
   `:= by sorry`」と書かれており `rg -c 'sorry'` が `1` を返すが、実コードに
   `sorry` / `admit` は一切なく、主定理 `shannon_noisy_channel_coding_theorem`
   (line 1000) は完全証明済みだった。同様に `ChannelCodingFeedbackComplete.lean` /
   `GeneralDMC.lean` の `1` も「0 sorry で publish」「discharged 0-sorry」という
   **完成を主張する docstring** が match したもの。`rg -c` を機械的に honesty 判定に
   使う場合、docstring 内の "sorry" 文字列が偽陽性を生むため、`rg 'by sorry|:= sorry'`
   など proof body 限定パターンとの併用が必要。（roadmap が Ch.7 を「Draft 2 sorry」と
   記すのも、この stale docstring 由来の可能性が高い。）

3. **「0 sorry」と「proof done」が一致しない実例**:
   `shannon_noisy_channel_coding_theorem_general`（`ChannelCodingShannonTheoremFull.lean`）は
   ファイル単位 `0 sorry` だが、達成可能性の核心が load-bearing 仮定 `h_passthrough` に
   bundle されている（CLAUDE.md「load-bearing hypothesis bundling」tell に該当、本人も
   `@audit:retract-candidate` を付与）。本章ではこれを `Verified` から除外し、
   full-support 前提のみの genuine 版を採用した。`0 sorry` だけでは headline 引用の
   十分条件にならないことの実例。

4. **容量定義 `capacity` が「Draft」扱いのファイルに同居**:
   Ch.7 中核の単一文字容量 `capacity` (sSup 形) は、roadmap が「Draft 2 sorry」と
   みなしたファイルに定義されている。実体は proof done だが、章 ↔ ファイルの対応が
   1:1 でなく、stale docstring に惑わされず実コードを Read して確認する必要があった。
