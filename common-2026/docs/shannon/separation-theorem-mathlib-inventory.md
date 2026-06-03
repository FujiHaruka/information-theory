# Shannon T3-E: Joint Source–Channel Coding (Separation Theorem) — Mathlib + InformationTheory inventory

> **Scope**: textbook roadmap **Tier 3 T3-E**. Cover–Thomas Ch.5 (source) と Ch.7 (channel)
> を統合する meta-定理。Stationary ergodic source の entropy rate `H(\mathcal{X}) < C` ⟺
> source を asymptotically reliable に channel 経由再現可能。
>
> **本ファイルの目的**: 「composition なので新数学はない」という想定を **検証**し、既存
> InformationTheory 資産 (source coding side / channel coding side) の **型シグネチャを verbatim
> 取り出して直接合成可能か** を判定する。判定結果は § H **Composition の結合点** を参照。
>
> **Output 規約**: 各候補に **`file:line`** + **完全 signature verbatim** + **`[..]` 型クラス
> verbatim** + **結論形 verbatim** + **Phase mapping**。CLAUDE.md「Subagent Inventory of
> Mathlib Lemmas」+「Mathlib-shape-driven Definitions」厳守。

## 一行サマリ

**Composition 系定理として既存 InformationTheory 資産で 70–80 % が組める** が、**source–channel
インタフェース型が definition-level で 不整合**: source coding (`AEP.lean`) は
`MeasureFano.errorProb μ (X^n) (c∘X^n) d` 形 (Ω 上 push), channel coding
(`ChannelCoding.lean`) は `Code.errorProbAt c W m = Measure.pi (W ∘ encoder m)
(errorEvent m)` 形 (`Fin n → β` 上 pi-measure)。**source 出力の `Fin M_n`-index を
channel 入力 `Fin n_c → α'` に橋渡しする mechanism は完全不在で自作必須** (新規 100–200 行)。
これが T3-E 規模見積もりの主軸。**規模再評価: roadmap 300–500 行 → 現実 400–600 行** に
上振れ (橋渡し型定義 + composition 200 行、achievability 100 行、converse 100–200 行)。

- **Source side achievability** (`source_coding_achievability`, `mem_achievableRates_of_gt_entropy`):
  iid + finite alphabet で **完成** (`AEP.lean:1138, :1222`)。Stationary ergodic への一般化は
  `EntropyRate.lean` + `ShannonMcMillanBreiman` 経由で原理可能だが、**SMB は Birkhoff 半分
  (limsup/liminf sandwich) を hypothesis として受ける形** (`ShannonMcMillanBreiman.lean:85`) で
  **未閉**。stationary ergodic な achievability 自前構築 = **+150 行**。
- **Source side converse** (`source_coding_converse`, `entropy_le_of_mem_achievableRates`):
  iid + finite alphabet で **完成** (`AEP.lean:704, :1207`)。出力 `liminf log M_n / n ≥ H`。
- **Channel side achievability** (`shannon_noisy_channel_coding_theorem_general_full`):
  memoryless DMC + finite alphabet で **完成** (`ChannelCodingShannonTheoremFullDischarge.lean:1588`)。
  出力: max-error < ε with `M ≥ ⌈exp(nR)⌉`。
- **Channel side converse** (`channel_coding_converse_general_memoryless_pure`):
  memoryless DMC で **完成** (`ChannelCodingConverseMemorylessPure.lean:650`)。
  出力: `log |M| ≤ ∑ I(X_i; Y_i).toReal + Fano`。

**もっとも危険な発見**: source coding theorem の `liminf` 出力形 (`source_coding_converse`)
と channel coding theorem の **`Tendsto (errorProb) atTop (𝓝 0)` 入力形** との間に
**`Filter.liminf` → `Tendsto` への direction 反転 bridge が不在**。converse 経路で source
側 `R ≥ H` と channel 側 `R ≤ C` を合成すると `H ≤ liminf R_n ∧ limsup R_n ≤ C` の交差形に
なり、これを `R_n → R` 形に閉じるには **rate-converging sub-sequence の抽出** か **bounded
rate hypothesis** の追加が必要。撤退ライン候補に挙げる。

---

## 主定理の最終形 (proposed)

```lean
/-- **T3-E Separation Theorem (achievability + converse)**. For an iid finite-alphabet
source `Xs : ℕ → Ω → α` and a memoryless DMC `W : Channel α' β` with `R < capacity W`
and `entropy μ (Xs 0) < R`, there exist source/channel codes whose composition has
vanishing error. Conversely, if any such composition achieves vanishing error then
`entropy μ (Xs 0) ≤ capacity W`. -/
theorem joint_source_channel_separation
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x}) (hcard_α : 2 ≤ Fintype.card α)
    (W : Channel α' β) [IsMarkovKernel W] (hcard_α' : 2 ≤ Fintype.card α')
    (hHC : entropy μ (Xs 0) < capacity W) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
      ∃ (n_c : ℕ) (M : ℕ)
        (c_src : (Fin n → α) → Fin M) (d_src : Fin M → (Fin n → α))
        (c_ch : Fin M → (Fin n_c → α')) (d_ch : (Fin n_c → β) → Fin M),
        InformationTheory.MeasureFano.errorProb μ
          (jointRV Xs n)
          (fun ω => d_src (d_ch (?Yo_ω)))   -- ?Yo_ω: requires channel push-forward bridge
          (fun _ => default)
        < ε
```
*(pseudo-Lean; 実 signature は composition の結合型 (`?Yo_ω`) を T3-E plan 段階で確定)*

**証明戦略 pseudo-Lean (6–10 行)**:

```lean
-- Step 1: pick R with H < R < C; use source-side achievability for the source side.
obtain ⟨R, hHR, hRC⟩ : ∃ R, entropy μ (Xs 0) < R ∧ R < capacity W := ⟨_, by linarith⟩
obtain ⟨M_src, _, c_src, d_src, h_rate_src, h_err_src⟩ :=
  source_coding_achievability μ Xs hXs hpos hindep_full hident hHR
-- Step 2: from h_rate_src `log M_src n / n → R`, pick N_src so that for n ≥ N_src,
--   ⌈exp((n_c) · R)⌉ ≥ M_src n for some block length n_c (linear scaling).
-- Step 3: apply channel achievability at this n_c.
obtain ⟨N_ch, hN_ch⟩ := shannon_noisy_channel_coding_theorem_general_full
  W (R := R) hR_pos hRC hε_half
-- Step 4: compose c_src + c_ch and d_ch + d_src; error rate splits by union bound.
-- Total error ≤ err_src + err_ch ≤ ε/2 + ε/2 = ε.
sorry  -- composition error bound is the main novel 100–200 LoC
```

---

## A. Source coding theorem の現状

### A-1. AEP-based source coding achievability (Tendsto form)

- **file:line**: `InformationTheory/Shannon/AEP.lean:1138`
- **完全 signature verbatim**:
  ```lean
  theorem source_coding_achievability
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
      (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
      (hindep_full : iIndepFun (fun i => Xs i) μ)
      (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
      {R : ℝ} (hR : entropy μ (Xs 0) < R) :
      ∃ M : ℕ → ℕ, ∃ _hM_pos : ∀ n, 0 < M n,
      ∃ c : ∀ n, (Fin n → α) → Fin (M n),
      ∃ d : ∀ n, Fin (M n) → (Fin n → α),
        Tendsto (fun n => Real.log (M n : ℝ) / n) atTop (𝓝 R) ∧
        Tendsto
          (fun n => InformationTheory.MeasureFano.errorProb μ
                      (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
          atTop (𝓝 0)
  ```
- **`[..]` 型クラス verbatim**: `[MeasurableSpace Ω]`, `[Fintype α] [DecidableEq α] [Nonempty α]`
  `[MeasurableSpace α] [MeasurableSingletonClass α]` (file header lines 48–50),
  `[IsProbabilityMeasure μ]` (本 signature 内).
- **結論形 verbatim**: 上記 conclusion ブロックそのまま。`Tendsto rate (𝓝 R) ∧ Tendsto errorProb (𝓝 0)`.
- **Phase mapping (T3-E)**: **source side achievability** の主入力。**直接呼べる**。
  iid 仮定だけで stationary ergodic 一般化前 (撤退ライン採用 候補)。

### A-2. AEP-based source coding converse (liminf form)

- **file:line**: `InformationTheory/Shannon/AEP.lean:704`
- **完全 signature verbatim**:
  ```lean
  theorem source_coding_converse
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
      (hindep_full : iIndepFun (fun i => Xs i) μ)
      (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
      (hcard : 2 ≤ Fintype.card α)
      (M : ℕ → ℕ) [hM_pos : ∀ n, NeZero (M n)]
      (c : ∀ n, (Fin n → α) → Fin (M n))
      (d : ∀ n, Fin (M n) → (Fin n → α))
      (hPe_to_zero :
        Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
                            (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
                atTop (𝓝 0))
      (hM_bdd : ∃ R, ∀ n, Real.log (M n : ℝ) / n ≤ R) :
      entropy μ (Xs 0)
        ≤ Filter.liminf (fun n : ℕ => Real.log (M n : ℝ) / n) atTop
  ```
- **`[..]` 型クラス verbatim**: 同 file header (`[Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]`) + signature 内 `[IsProbabilityMeasure μ]`
  + `[hM_pos : ∀ n, NeZero (M n)]`.
- **結論形 verbatim**: `entropy μ (Xs 0) ≤ Filter.liminf (fun n : ℕ => Real.log (M n : ℝ) / n) atTop`.
- **Phase mapping (T3-E)**: **source side converse**。出力が **`liminf` 形** であり、source
  rate `R = lim log M_n / n` の bounded-tendsto 形を要請する `hM_bdd` 仮説あり。これが
  composition 時に **`Tendsto` ↔ `liminf` の変換** を要する原因 (§ H 参照)。

### A-3. Unified source coding theorem (両側等号)

- **file:line**: `InformationTheory/Shannon/AEP.lean:1240`
- **完全 signature verbatim**:
  ```lean
  theorem source_coding_theorem
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
      (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
      (hindep_full : iIndepFun (fun i => Xs i) μ)
      (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
      (hcard : 2 ≤ Fintype.card α) :
      sInf (achievableRates μ Xs) = entropy μ (Xs 0)
  ```
- **`[..]` 型クラス verbatim**: 同上.
- **結論形 verbatim**: `sInf (achievableRates μ Xs) = entropy μ (Xs 0)`.
- **Phase mapping (T3-E)**: composition 不要 (set-level statement)。T3-E は具体的な
  encoder/decoder を取り出すので A-1 / A-2 を直接使う方が望ましい。**T3-E では使わない**。

### A-4. `IsAchievableCode` predicate

- **file:line**: `InformationTheory/Shannon/AEP.lean:1186`
- **完全 signature verbatim**:
  ```lean
  structure IsAchievableCode
      (μ : Measure Ω) (Xs : ℕ → Ω → α)
      (M : ℕ → ℕ)
      (c : ∀ n, (Fin n → α) → Fin (M n))
      (d : ∀ n, Fin (M n) → (Fin n → α)) : Prop where
    hM_pos : ∀ n, NeZero (M n)
    hPe_to_zero :
      Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
                (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
              atTop (𝓝 0)
    hM_bdd : ∃ R, ∀ n, Real.log (M n : ℝ) / n ≤ R
  ```
- **Phase mapping (T3-E)**: source-side codes を package 化する型として **再利用候補**。
  T3-E の composition で source code を取り出すと自然にこの shape に乗る (achievability 経由
  なので `hM_bdd` も自動)。

### A-5. Per-n source coding bound (Slepian–Wolf 流儀 4-step)

- **file:line**: `InformationTheory/Shannon/AEP.lean:580`
- **結論形 verbatim**:
  ```lean
  (n : ℝ) * entropy μ (Xs 0)
    ≤ Real.log (M : ℝ)
      + Real.binEntropy (errorProb μ ... )
      + errorProb μ ... * (n : ℝ) * Real.log (Fintype.card α)
  ```
- **Phase mapping (T3-E)**: **converse 経路で per-n bound として再利用可能** (T3-E converse が
  source-side bound + channel-side bound を per-n で合算する組み立てを採るなら直接)。

### A-6. ShannonCode (single-shot, Kraft + length sandwich)

- **file:line**: `InformationTheory/Shannon/ShannonCode.lean` (354 行)
- **Phase mapping (T3-E)**: T3-E で **使わない**。Shannon code は single-shot で
  `H ≤ E[L] < H + 1` を与える設計、AEP-based block code とは別系統。T3-E は AEP 経由が自然。

---

## B. Channel coding theorem の現状

### B-1. `shannon_noisy_channel_coding_theorem_general_full` (channel achievability, fully general)

- **file:line**: `InformationTheory/Shannon/ChannelCodingShannonTheoremFullDischarge.lean:1588`
- **完全 signature verbatim**:
  ```lean
  theorem shannon_noisy_channel_coding_theorem_general_full
      (W : Channel α β) [IsMarkovKernel W]
      {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
      {ε : ℝ} (hε : 0 < ε) :
      ∃ N : ℕ, ∀ n, N ≤ n →
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
          (c : Code M n α β),
          ∀ m, (c.errorProbAt W m).toReal < ε
  ```
- **`[..]` 型クラス verbatim**: file header (lines 46–48):
  `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`,
  同 β, signature 内 `[IsMarkovKernel W]`.
- **結論形 verbatim**: `∀ m, (c.errorProbAt W m).toReal < ε`. **max-error 形** (per-message
  ε 制約)。`Code M n α β` (encoder + decoder bundle) で返す。
- **Phase mapping (T3-E)**: **channel side achievability 主入力**。**直接呼べる**。
  `hW_pos` (full-support) 仮定が **完全に外れている** (Phase D smoothing で discharge 済) ので
  T3-E 段階で W の追加仮定を要しない。

### B-2. `shannon_noisy_channel_coding_theorem` (MVP, `hW_pos` 仮定付)

- **file:line**: `InformationTheory/Shannon/ChannelCodingShannonTheorem.lean:1011`
- **完全 signature verbatim**:
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
- **Phase mapping (T3-E)**: B-1 で十分。本 lemma は **使わない**。

### B-3. `shannon_noisy_channel_coding_theorem_general` (hypothesis pass-through 形)

- **file:line**: `InformationTheory/Shannon/ChannelCodingShannonTheoremFull.lean:52`
- **Phase mapping (T3-E)**: B-1 が discharged 完全形のため **使わない**。

### B-4. `channel_coding_converse_general_memoryless_pure` (channel converse, semi-pure)

- **file:line**: `InformationTheory/Shannon/ChannelCodingConverseMemorylessPure.lean:650`
- **完全 signature verbatim**:
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
      (hMsg_uniform :
        μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
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
- **`[..]` 型クラス verbatim** (section ヘッダ lines 631–636):
  - `[Fintype M] [DecidableEq M] [Nonempty M] [MeasurableSpace M] [MeasurableSingletonClass M] [StandardBorelSpace M]`
  - `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]`
  - `[Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]`
  - signature 内: `[IsProbabilityMeasure μ]`.
- **結論形 verbatim**: `Real.log (Fintype.card M) ≤ ∑ I(X_i; Y_i).toReal + h_2(Pe) + Pe · log(|M|-1)` (Fano 形)
- **Phase mapping (T3-E)**: **channel side converse 主入力**。**直接呼べる** が要 `IsMemorylessChannel`
  + Markov chain + uniform msg 仮定。T3-E では `Msg` を **source-encoded index** にして渡す形
  になるが、`hMsg_uniform` (uniform message) と source の AEP 出力 distribution が **不一致**
  (source-encoded index は概一様だが完全一様ではない) — **これが composition で要 bridge**。

### B-5. `channel_coding_converse_general_memoryless_strong` (D-2'' 形)

- **file:line**: `InformationTheory/Shannon/ChannelCodingConverseGeneralStrong.lean:272`
- **Phase mapping (T3-E)**: B-4 (semi-pure) が B-5 を呼ぶ wrapper のため、**B-4 を使う**。
  ただし B-5 を直接使う場合は `IsMemorylessChannelStrong` (per-letter Markov + outputs cond indep)
  を caller 側で構築する。

### B-6. `channel_coding_converse_iid` (n-variable iid form)

- **file:line**: `InformationTheory/Shannon/ChannelCodingConverse.lean:56`
- **結論形 verbatim**: `Real.log (Fintype.card M) ≤ (n : ℝ) * I(X_0; Y_0).toReal + Fano`.
- **Phase mapping (T3-E)**: T3-E composition では encoder が iid に限定されない (source-encoded
  index は iid でない) ため **使えない**。B-4 を使う。

### B-7. `capacity W` (channel capacity)

- **file:line**: `InformationTheory/Shannon/ChannelCodingShannonTheorem.lean:102`
- **完全 signature verbatim**:
  ```lean
  noncomputable def capacity (W : Channel α β) : ℝ :=
    sSup ((fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal) ''
          stdSimplex ℝ α)
  ```
- **Phase mapping (T3-E)**: T3-E 主定理仮定 `entropy (Xs 0) < capacity W` の RHS。**そのまま使う**。

### B-8. `capacity_lim_eq_capacity_of_memoryless` (per-letter / blockwise 同一性)

- **file:line**: `InformationTheory/Shannon/BlockwiseChannel.lean:1181`
- **結論形 verbatim**: `(BlockwiseChannel.ofMemoryless W).capacity_lim = capacity W`.
- **Phase mapping (T3-E)**: T3-E は memoryless 前提で進めるので、**block 形 capacity との等価性
  は手元にある**。直接の composition では single-letter `capacity W` を使う。

---

## C. Composition の結合点 — **最重要セクション**

### C-1. 型不一致サマリ

**Source coding 側 (AEP)** の出力 (`source_coding_achievability`):

```
c : ∀ n, (Fin n → α_src) → Fin (M n)         -- source encoder
d : ∀ n, Fin (M n) → (Fin n → α_src)         -- source decoder
errorProb measured on:
  (Ω, μ) via `InformationTheory.MeasureFano.errorProb μ (jointRV Xs n)
    (fun ω => c n (jointRV Xs n ω)) (d n)`
  = μ.real { ω | jointRV Xs n ω ≠ d n (c n (jointRV Xs n ω)) }
```

**Channel coding 側 (B-1)** の出力 (`shannon_noisy_channel_coding_theorem_general_full`):

```
c_ch : Code M n_c α_ch β                     -- bundle: encoder Fin M → Fin n_c → α_ch
                                             --          decoder (Fin n_c → β) → Fin M
errorProb measured per-message on:
  (Measure.pi (fun i => W (c_ch.encoder m i))) (c_ch.errorEvent m)
```

**境界**:
- Source の `α_src` = source alphabet (例: ASCII)
- Channel の `α_ch` = channel input alphabet (例: {0,1})
- 通常は `α_src ≠ α_ch`、サイズも違う
- Source は `M n` 個の codeword index に圧縮、channel は `M_ch ≥ ⌈exp(n_c · R)⌉` 個を運ぶ
- **`M n` (source) ≤ `M_ch` (channel) になるよう `n_c` を選ぶ** (rate scaling)
- Channel 入力には `Fin M n → Fin M_ch` の **injection** が要る (trivial: `Fin.castLE`)

### C-2. 必要な bridge (T3-E 自作)

**B-1 (channel) と A-1 (source) を composition するには以下 5 件が必要**:

1. **`composeCode`** (新規 def, ~30 行):
   ```lean
   def composeCode {α_src α_ch β : Type*} {n n_c M_src M_ch : ℕ}
       (c_src : (Fin n → α_src) → Fin M_src)
       (d_src : Fin M_src → (Fin n → α_src))
       (h_le : M_src ≤ M_ch)
       (c_ch : Code M_ch n_c α_ch β) :
       (channel-coupled error-rate predicate)
   ```
   Mathlib に composition primitive **不在**。

2. **`errorProb_composed_le`** (新規 lemma, ~50 行):
   union bound `Pe_total ≤ Pe_src + Pe_ch`. 各項を A-1 / B-1 の出力で押さえる。Mathlib に
   類似なし (Slepian–Wolf converse は composition でなく error-event 分解)。

3. **Channel 出力 `Ys i ω` の構成** (新規 def + glue, ~30 行): channel kernel `W` を source
   composition と一緒に動かすには Ω 拡張 (source × channel-noise 直積) が必要。これは標準的
   probabilistic coupling だが Mathlib `Measure.compProd` + `Kernel.pi` (= `Channel.toBlock`)
   で原理可能。`BlockwiseChannel.ofMemoryless` (`BlockwiseChannel.lean:111`) が
   per-block kernel を返すのでこれを使う。

4. **Source rate ↔ channel block-length scaling** (新規 lemma, ~20 行):
   `Tendsto (log M_src n / n) atTop (𝓝 R_src)` から
   `∀ ε > 0, ∃ N, ∀ n ≥ N, ⌈exp(n_c · R_ch)⌉ ≥ M_src n` を導く (with `n_c := ⌈n · R_src / R_ch⌉`
   or similar). 純粋に `Real.exp` / `Nat.ceil` の analysis。

5. **`Tendsto` ↔ `Filter.liminf` bridge** (converse 用、~30 行):
   B-4 (channel converse) は `Real.log (Fintype.card M) ≤ ∑ I + Fano` の **per-n bound** を
   返す。これを A-2 (source converse) の `liminf` 形と組み合わせるには:
   - achievability 経路では rate `R_n → R` (Tendsto) で構造的に成立
   - converse 経路では rate が **liminf 形 + bounded hypothesis** だけなので、`Real.log M_src n
     / n → R_src` を仮定追加するか subsequence で抽出する必要あり。

**自作合計**: 約 **140–160 行** (Mathlib API 不在領域)。

### C-3. 重要な型変換 (Mathlib 既存で済む)

- **`Fin.castLE`** (`Mathlib/Data/Fin/Basic.lean`): `M_src ≤ M_ch` の下で `Fin M_src → Fin M_ch`.
  signature: `def Fin.castLE {n m : ℕ} (h : n ≤ m) : Fin n → Fin m`.
- **`Function.invFunOn`** / decoder の left-inverse 構築: trivial cases では `Fin.castLE` の
  retraction を取る。decoder 側は inverse partial だが、`d_ch ∘ c_ch_part` で source decoder
  を呼べばよい (out-of-range は default).

---

## D. Stationary ergodic source の entropy rate

### D-1. `StationaryProcess` (基本構造)

- **file:line**: `InformationTheory/Shannon/Stationary.lean:45`
- **完全 signature verbatim**:
  ```lean
  structure StationaryProcess (μ : Measure Ω) (α : Type*) [MeasurableSpace α] where
    T : Ω → Ω
    X : Ω → α
    measurePreserving : MeasurePreserving T μ μ
    measurable_X : Measurable X
  ```
- **`[..]` 型クラス verbatim** (file lines 38–40):
  `[MeasurableSpace Ω]`, `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`.

### D-2. `ErgodicProcess` (ergodic 強化)

- **file:line**: `InformationTheory/Shannon/Stationary.lean:114`
- **完全 signature verbatim**:
  ```lean
  structure ErgodicProcess (μ : Measure Ω) (α : Type*) [MeasurableSpace α]
      extends StationaryProcess μ α where
    ergodic : Ergodic T μ
  ```

### D-3. `entropyRate` (lim H_n / n)

- **file:line**: `InformationTheory/Shannon/EntropyRate.lean:69`
- **完全 signature verbatim**:
  ```lean
  noncomputable def entropyRate (μ : Measure Ω) (p : StationaryProcess μ α) : ℝ :=
    Filter.atTop.limUnder (fun n : ℕ => blockEntropy μ p n / n)
  ```
- **`[..]` 型クラス verbatim**: file lines 53–55: `[MeasurableSpace Ω]`,
  `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`.
- **Phase mapping (T3-E)**: stationary ergodic 一般化を採るなら主入力。IID 限定なら `entropy μ (Xs 0)`
  をそのまま使う (entropy rate と一致は別補題、§ D-7 参照)。

### D-4. `entropyRate_exists_of_stationary` (限界存在)

- **file:line**: `InformationTheory/Shannon/EntropyRate.lean:432`
- **完全 signature verbatim**:
  ```lean
  theorem entropyRate_exists_of_stationary
      (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
      ∃ H : ℝ, Tendsto (fun n : ℕ => blockEntropy μ p n / n) atTop (𝓝 H)
  ```
- **結論形 verbatim**: `∃ H : ℝ, Tendsto (fun n : ℕ => blockEntropy μ p n / n) atTop (𝓝 H)`.
- **Phase mapping (T3-E)**: entropy rate が **収束する事実は完備**。stationary だけ必要 (ergodic 不要)。

### D-5. `entropyRate_eq_lim_condEntropy` (Cesàro 等価形)

- **file:line**: `InformationTheory/Shannon/EntropyRate.lean:466`
- **結論形 verbatim**:
  `Tendsto (conditionalEntropyTail μ p) atTop (𝓝 (entropyRate μ p))`.

### D-6. SMB (sandwich form, Birkhoff hypothesis-form)

- **file:line**: `InformationTheory/Shannon/ShannonMcMillanBreiman.lean:85`
- **完全 signature verbatim**:
  ```lean
  theorem shannon_mcmillan_breiman_of_sandwich
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (p : ErgodicProcess μ α)
      (h_liminf : ∀ᵐ ω ∂μ,
        entropyRate μ p.toStationaryProcess
          ≤ Filter.liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop)
      (h_limsup : ∀ᵐ ω ∂μ,
        Filter.limsup (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
          ≤ entropyRate μ p.toStationaryProcess)
      (h_bdd_above : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
          (fun n => blockLogAvg μ p.toStationaryProcess n ω))
      (h_bdd_below : ∀ᵐ ω ∂μ,
        Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
          (fun n => blockLogAvg μ p.toStationaryProcess n ω)) :
      ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n => blockLogAvg μ p.toStationaryProcess n ω)
        Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess))
  ```
- **Phase mapping (T3-E)**: SMB 全体形は **未閉** (Birkhoff sandwich を hypothesis として
  受ける形)。stationary ergodic 一般化を T3-E で採るには **Birkhoff sandwich の 4 仮説を全部
  落とす** = T3-E に **完全 SMB の closing も含めることになる** (これは E-8' = 700+ 行の plan)。
  **撤退ライン**: stationary ergodic 一般化を諦め、**IID 限定** で T3-E を publish (Phase A-1 + A-2
  を直接組む)。

### D-7. IID source と entropy rate の関係 — **不在**

- **loogle query**: `entropyRate, iIndepFun` (`Found 0 declarations`)、`Pairwise IndepFun, entropy_rate` (同 0)
- **`rg` 検索**: `InformationTheory/Shannon/EntropyRate.lean` `Stationary.lean` 内に IID specialize lemma なし。
- **判定**: IID `Xs : ℕ → Ω → α` (`iIndepFun` + `IdentDistrib`) を `StationaryProcess` として
  embed する canonical lemma は **不在**。自作する場合は `T := Function.shift` 風の左 shift
  作用と `μ := Measure.pi ...` の組み合わせで **+50–100 行**。
- **Phase mapping (T3-E)**: 撤退ライン採用 (IID 限定) なら **不要**。一般化採用なら自作必須。

---

## E. Converse 経路の再利用判定

### E-1. 既存資産マッピング

| Phase | T3-E 中の役割 | 既存資産 | 再利用判定 |
|---|---|---|---|
| Channel converse per-n bound | `log M ≤ ∑ I(X_i; Y_i) + Fano` | `channel_coding_converse_general_memoryless_pure` (B-4) | **直接呼べる** |
| Source converse per-n bound | `n · H ≤ log M + Fano` | `source_coding_per_n_bound` (A-5) | **直接呼べる** |
| Per-letter MI → capacity | `∑ I(X_i; Y_i) ≤ n · C` | `capacity_lim_eq_capacity_of_memoryless` (B-8) または `mutualInfoOfChannel ≤ capacity` の per-input bound | **既存** (但し per-`p` の `MI ≤ capacity` は trivial: capacity の def 自体が sup) |
| Fano 弱変換 (Pe → 0 → 1/n h(Pe) → 0) | `lim h(Pe_n) / n = 0` (with `Pe_n → 0`) | `source_coding_converse` 内部で使われている (`AEP.lean:733`) を private patch | **既存だが private** — `Real.binEntropy_continuous` と `tendsto_one_div_atTop_nhds_zero_nat` から ~10 行で再構築可 |

### E-2. **Tendsto ↔ liminf bridge の不在** — 主リスク

- B-4 (channel converse) の出力は `Real.log (Fintype.card M) ≤ ∑ I + Fano` の **per-n inequality**。
- A-2 (source converse) は **`liminf log M_n / n ≥ H`** の **asymptotic inequality**。
- T3-E converse 経路で「composition の error → 0 ⇒ source rate ≥ H ⇒ source rate ≤ C」を
  繋ぐには:
  - **`Tendsto (Pe_n) (𝓝 0) ⇒ liminf (log M_n / n) ≥ H`** (これは A-2 そのまま; `hM_bdd` 仮説要)
  - **`Tendsto (log M_n / n) (𝓝 R) ⇒ R ≤ C`** (これが B-4 を per-n で積み上げ、`Tendsto` で
    `liminf` を `Tendsto.liminf_eq` で潰す bridge が要る)
- **`Filter.Tendsto.liminf_eq`** (`Mathlib/Topology/Order/LiminfLimsup.lean:196`、`aep-source-coding-mathlib-inventory.md:48` 既出) で
  bridge は **可能**。自作 ~30 行で済む。

### E-3. Converse 全体としての規模

- B-4 を per-n で呼ぶ glue: ~50 行
- A-2 を呼ぶ glue: ~30 行
- Tendsto ↔ liminf bridge: ~30 行
- 合計: **約 110 行** (converse 全体)

---

## F. 横断: TypedRV / DotEq / IIDProductInput

### F-1. `TypedRV.lean` (I-1, H(X) notation)

- **file:line**: `InformationTheory/Shannon/TypedRV.lean:64–88`
- **decl**: `klDivRV`, `differentialEntropyRV` (continuous 系のみ)
- **Phase mapping (T3-E)**: T3-E は **離散版** なので **使わない**。`entropy μ (Xs 0)` 直書きで十分。

### F-2. `Asymptotic.lean` (I-3, DotEq `≐` notation)

- **file:line**: `InformationTheory/Asymptotic.lean:43`
- **完全 signature verbatim**:
  ```lean
  def DotEq (a b : ℕ → ℝ) : Prop :=
    -- (Real.log ∘ a − Real.log ∘ b) =o[atTop] (·:ℝ)
  ```
- **Phase mapping (T3-E)**: Cover–Thomas の `a_n ≐ b_n` notation は **T3-E では使わない**。
  T3-E は `Tendsto` + `liminf` で直接書く方が Mathlib との接続が良い。

### F-3. `IIDProductInput.lean` (channel coding iid product)

- **file:line**: `InformationTheory/Shannon/IIDProductInput.lean` (916 行)
- **役割**: channel coding 内で `Measure.pi` を iid input として扱う infrastructure。
  既に B-1 が内部で使うので **T3-E では transitive に使われる** が **直接呼ぶ必要なし**。

---

## G. 主要前提条件ボックス (composition で事故が起きやすい)

- **`source_coding_achievability` (A-1)**:
  - 必須: `[IsProbabilityMeasure μ]`, `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`
  - 仮定: `iIndepFun (fun i => Xs i) μ` (**mutual** independence、`Pairwise` では弱すぎ)
  - 仮定: `IdentDistrib (Xs i) (Xs 0) μ μ` for all i
  - 仮定: `hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x}` (**full support**)
  - 仮定: `entropy μ (Xs 0) < R` (rate condition)
- **`source_coding_converse` (A-2)**:
  - 同上の `iIndepFun` + `IdentDistrib`
  - 仮定: `hcard : 2 ≤ Fintype.card α` (Fano 用)
  - 仮定: `hM_bdd : ∃ R, ∀ n, Real.log (M n : ℝ) / n ≤ R` — **bounded rate** が要 (super-exponential
    growth を排除)
  - 仮定: `hPe_to_zero : Tendsto (Pe_n) atTop (𝓝 0)` (error rate vanishes)
- **`shannon_noisy_channel_coding_theorem_general_full` (B-1)**:
  - 必須: `[Fintype α/β] [DecidableEq α/β] [Nonempty α/β] [MeasurableSpace α/β] [MeasurableSingletonClass α/β]`
  - 必須: `[IsMarkovKernel W]`
  - 仮定: `0 < R`, `R < capacity W`, `0 < ε`
  - **`hW_pos` (full support) は不要** (smoothing で discharge 済)
- **`channel_coding_converse_general_memoryless_pure` (B-4)**:
  - **`[StandardBorelSpace M] [StandardBorelSpace α] [StandardBorelSpace β]`** が追加で要る
    — `MeasurableSingletonClass` + `Countable` で auto-derive されるはずだが、
    `[Fintype]` + `[MeasurableSingletonClass]` で自動派生される (lines 632–636 確認済)。
  - 仮定: `IsMemorylessChannel μ Xs Ys` (per-letter Markov chain `(X^{≠i}, Y^{≠i}) → X_i → Y_i`)
  - 仮定: `hmarkov : IsMarkovChain μ Msg (encoder ∘ Msg) Y^n`
  - 仮定: `hMsg_uniform : μ.map Msg = (|M|⁻¹) • Measure.count` — **uniform message**
    (T3-E composition では source-encoded index を渡すので **概一様だが完全一様ではない**
    → bridge が要る)
  - 仮定: `hMI_finite : mutualInfo ≠ ∞`
- **`entropyRate_exists_of_stationary` (D-4)**: `[IsProbabilityMeasure μ]` のみ (ergodic 不要)。
- **`shannon_mcmillan_breiman_of_sandwich` (D-6)**: `[ErgodicProcess μ α]` 必須。**Birkhoff
  sandwich を 4 仮説で受ける形** (closed-form 化されていない)。

---

## H. 自作が必要な要素 (優先度順)

| 優先度 | 要素 | 推奨実装 | 工数 | 落とし穴 |
|---|---|---|---|---|
| **1 (致命)** | source–channel composition encoder/decoder (`composeCode`) | `Fin.castLE` + 単純 composition、bundle 型は `Code` を借りる | ~40 行 | M_src ≤ M_ch の不等式が encoder type に effect する、index out-of-range の handling |
| **2 (致命)** | composed error rate bound (`errorProb_composed_le`) | union bound: `Pe_total ≤ Pe_src + Pe_ch` を **Ω 拡張** (source × channel-noise 直積) 上で展開 | ~60 行 | source error event と channel error event の measure space が異なる。`Measure.compProd` で coupling 必要 |
| **3 (致命)** | channel block-length n_c の選び方 (`rate_scaling`) | `n_c := ⌈n · R_src / R_ch⌉` または `n_c := n` for `R_src ≈ R_ch`. `Tendsto (log M_src n / n) (𝓝 R_src)` から `M_src n ≤ ⌈exp(n_c · R_ch)⌉` を導く | ~30 行 | `Nat.ceil` の monotonicity、`Real.exp` 引数の正値性 |
| 4 (高) | Tendsto ↔ liminf bridge (converse 用) | `Filter.Tendsto.liminf_eq` で潰す | ~30 行 | `IsBoundedUnder` / `IsCoboundedUnder` の `isBoundedDefault` 解決 |
| 5 (中) | uniform message bridge (converse 用) | source-encoded index は uniform でないので、**最悪近接 uniform** に上向き bound する。または **B-4 の `hMsg_uniform` を任意分布に弱める修正** (= B-4 の証明再演) | ~50 行 (workaround) または **+200 行** (B-4 修正) | B-4 の証明全体が `hMsg_uniform` を本質的に使う。任意分布化は別 plan |
| 6 (低) | stationary ergodic 一般化 (撤退ラインで切る) | SMB Birkhoff sandwich の closing が必要 (= E-8' 700+ 行) | **+1000 行 (deferred)** | SMB 全体が deferred 状態; T3-E では IID 限定が現実的 |
| 7 (低) | IID → `StationaryProcess` embed (任意) | `T := identity` (degenerate stationary) または `Measure.pi` 上の shift | ~80 行 | iIndepFun と shift-invariance の整合性 |

**合計 自作量見積もり**:
- **最小路線 (IID 限定 achievability + IID 限定 converse)**: 優先度 1–4 = ~160 行
- **撤退ラインで切らない場合 (achievability + converse、uniform msg bridge 込)**: 1–5 = ~210 行
- **stationary ergodic 一般化**: 1–7 = ~1500 行 (SMB 全体 closing 込)

---

## I. 撤退ラインへの距離

### I-1. Roadmap の元撤退ライン (再掲、推定)

| 撤退オプション | 効果 | T3-E 規模 |
|---|---|---|
| IID source only (stationary ergodic 一般化を後回し) | SMB closing 不要 | ~150 行縮減 |
| achievability のみ (converse は別 plan) | A-2 + B-4 不要 | ~150 行縮減 |
| typed encoder/decoder の自前定義 (composition 形式が既存に無い場合) | bridge 量増 | +100 行 |

### I-2. 本 inventory での発動判定

- **「stationary ergodic 一般化 → IID 限定」は **発動推奨****。
  理由: SMB の Birkhoff sandwich は **deferred 状態** (`ShannonMcMillanBreiman.lean:85` で
  hypothesis として受け取る形)。T3-E が SMB 全体 closing を含めるなら roadmap 300–500 行は
  非現実的 (1000+ 行)。
- **「achievability のみ vs achievability + converse」は **両方** が現実的**。
  理由: converse 経路は B-4 と A-2 を呼ぶ glue が中心で +110 行程度。撤退する必要なし。
  ただし「uniform message bridge」(優先度 5) は workaround で済ませる。
- **「composition 形式自前」は **発動 (確定)****。
  Mathlib にも InformationTheory にも `composeCode` 系の primitive **不在**を確認 (§ H の優先度 1–3)。
  これが T3-E の「新数学なし」概念に反して **唯一の novel 構造構築箇所**。

### I-3. 新規撤退ライン提案

- **撤退ライン A (uniform message を諦める)**: B-4 の `hMsg_uniform` を満たさない source 出力には
  `IsAchievableCode` から **概一様性** ([0, 1/|M| + 1/n] くらいの bound) を補助 lemma で証明し、
  uniform fallback で B-4 を呼ぶ近似経路。+50 行 で済む。
- **撤退ライン B (channel 側 max-error を avg-error に弱める)**: 現在の B-1 は max-error 形だが、
  T3-E composition では avg-error で十分。avg-error 形は `Code.averageErrorProb` が既存
  (`ChannelCoding.lean:210`) で、B-1 から trivially 弱化可。
- **撤退ライン C (converse を後続 plan へ)**: achievability + statement-level converse (no
  proof) で publish。converse 部分を別 T3-E-converse plan へ分割。**規模 -110 行**。

---

## J. 着手 skeleton

```lean
import InformationTheory.Shannon.AEP
import InformationTheory.Shannon.AEPRate
import InformationTheory.Shannon.ChannelCoding
import InformationTheory.Shannon.ChannelCodingShannonTheorem
import InformationTheory.Shannon.ChannelCodingShannonTheoremFullDischarge
import InformationTheory.Shannon.ChannelCodingConverseMemorylessPure
import InformationTheory.Shannon.BlockwiseChannel
import Mathlib.Topology.Order.LiminfLimsup

/-!
# T3-E Joint Source–Channel Coding (Separation Theorem)

Cover–Thomas Theorem 7.13.1.

## Approach

IID source `Xs : ℕ → Ω → α_src` (撤退ライン: stationary ergodic 一般化は別 plan で deferred)
と memoryless DMC `W : Channel α_ch β` の composition で、
`entropy μ (Xs 0) < capacity W` ⟺ asymptotically reliable transmission.

主部品:
- Source side achievability: `source_coding_achievability` (AEP.lean:1138)
- Channel side achievability: `shannon_noisy_channel_coding_theorem_general_full`
  (ChannelCodingShannonTheoremFullDischarge.lean:1588)
- Source side converse: `source_coding_converse` (AEP.lean:704)
- Channel side converse: `channel_coding_converse_general_memoryless_pure`
  (ChannelCodingConverseMemorylessPure.lean:650)

新規構築 (~160 行):
1. `composeCode` (encoder/decoder composition)
2. `errorProb_composed_le` (union bound on error events)
3. `rate_scaling` (n_c block-length selection)
4. Tendsto ↔ liminf bridge (converse 用)
-/

namespace InformationTheory.Shannon.JointSourceChannel

open MeasureTheory ProbabilityTheory InformationTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α_src : Type*} [Fintype α_src] [DecidableEq α_src] [Nonempty α_src]
  [MeasurableSpace α_src] [MeasurableSingletonClass α_src]
variable {α_ch β : Type*}
  [Fintype α_ch] [DecidableEq α_ch] [Nonempty α_ch]
    [MeasurableSpace α_ch] [MeasurableSingletonClass α_ch] [StandardBorelSpace α_ch]
  [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- Composed (source ∘ channel) code error rate (sketch). -/
noncomputable def composedErrorProb
    (μ : Measure Ω) (Xs : ℕ → Ω → α_src)
    {n n_c M_src M_ch : ℕ}
    (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
    (h_le : M_src ≤ M_ch)
    (W : ChannelCoding.Channel α_ch β) (c_ch : ChannelCoding.Code M_ch n_c α_ch β) : ℝ := by
  sorry  -- new construction; see § H optimal priority 2

/-- **T3-E Separation Theorem — achievability**. -/
theorem joint_source_channel_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α_src) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α_src, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (W : ChannelCoding.Channel α_ch β) [IsMarkovKernel W]
    (hHC : entropy μ (Xs 0) < ChannelCoding.capacity W) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
      ∃ (n_c M_src M_ch : ℕ) (h_le : M_src ≤ M_ch)
        (c_src : (Fin n → α_src) → Fin M_src) (d_src : Fin M_src → (Fin n → α_src))
        (c_ch : ChannelCoding.Code M_ch n_c α_ch β),
        composedErrorProb μ Xs c_src d_src h_le W c_ch < ε := by
  sorry  -- composition of A-1 + B-1 + § H priority 3 (rate scaling)

/-- **T3-E Separation Theorem — converse**. -/
theorem joint_source_channel_converse
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α_src) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α_src)
    (W : ChannelCoding.Channel α_ch β) [IsMarkovKernel W] :
    -- If a composed code family has vanishing error and bounded rate,
    -- then entropy ≤ capacity.
    True := by  -- placeholder; concrete form depends on `composedErrorProb` API
  sorry

end InformationTheory.Shannon.JointSourceChannel
```

---

## K. 既存率推定

| Component | 既存率 | 内訳 |
|---|---|---|
| Source achievability | **100 %** | `source_coding_achievability` 直呼出し |
| Channel achievability | **100 %** | `shannon_noisy_channel_coding_theorem_general_full` 直呼出し |
| Source converse | **100 %** | `source_coding_converse` + `entropy_le_of_mem_achievableRates` |
| Channel converse | **100 %** | `channel_coding_converse_general_memoryless_pure` |
| Capacity / entropy / MI 基盤 | **100 %** | `capacity`, `mutualInfo`, `entropy` etc. 全て publish 済 |
| Composition encoder/decoder | **0 %** | `composeCode` 不在 |
| Composed error bound | **0 %** | `errorProb_composed_le` 不在 |
| Rate scaling | **0 %** | trivial だが書く必要 |
| Tendsto ↔ liminf bridge | **partial** | `Filter.Tendsto.liminf_eq` (Mathlib) で組める |
| Stationary ergodic 一般化 | **撤退** | SMB closing が deferred、IID 限定で publish |

**Composition 全体既存率**: **約 70 %** (Mathlib + InformationTheory 既存合算)。残り 30 % が § H の
自作 4 件 (~160 行) + 撤退ライン B/C で更に縮減可能。

---

## L. 規模見積もり再評価

- **roadmap 300–500 行** の現実性: **achievability のみ + IID 限定 + 撤退ライン B (avg-error)
  発動で 250–350 行** に収まる。converse 込みで **350–500 行**。
- **stationary ergodic 一般化を含めるな**ら **+700–1000 行** (SMB closing) で **1000+ 行**
  となり roadmap の規模見積もりを大幅超過。**T3-E では IID 限定が必須判断**。
- **撤退ライン C (converse 別 plan)** 発動なら **achievability 単体で 200–300 行** に収まり
  T3-E 内では最小路線。

**結論**: roadmap 300–500 行は **IID + 撤退ライン B/C 込みで現実的**、stationary ergodic
一般化を含むなら非現実的。

---

## M. もっとも危険な発見 (Top 3)

1. **`composeCode` primitive 不在** (§ H 優先度 1–3): T3-E は「composition なので新数学なし」
   と roadmap で見積もられていたが、Mathlib にも InformationTheory にも source–channel composition の
   primitive (encoder bundle composition + error event union bound) が **完全に存在しない**。
   ~160 行の novel 構造構築が必要。
2. **B-4 (channel converse) の `hMsg_uniform` 仮説** (§ G、§ H 優先度 5): channel converse は
   **uniform message** を要求するが、source-encoded index は概一様でしかない。撤退ライン A
   (近似 uniform fallback +50 行) または B-4 修正 (+200 行) のどちらかが必要。
3. **SMB の Birkhoff sandwich が hypothesis-form で deferred** (§ D-6): stationary ergodic
   一般化を採るなら T3-E に **SMB 全体 closing** を含めることになり、roadmap 規模見積もり
   (300–500 行) を 3–5 倍超過。IID 限定で publish が必須。

---

## N. 結論

- **既存率 70 %** (composition 全体)、自作必要 **4 件 ~160 行**、**撤退ライン発動 yes**
  (stationary ergodic 一般化を後回し、IID 限定で publish)。
- 規模見積もり **350–500 行** (IID + achievability + converse、撤退ライン B/C 込)。
- 主要 risk: **`composeCode` primitive 不在** + **uniform message bridge** + **SMB 未閉**。
  どれも T3-E 単体で解決すべきではなく、撤退ラインで段階的にスコープ縮退する設計が現実的。
