# AWGN Typicality Discharge — Phase 0 Inventory (Axis 4: Expurgation)

> **Parent plan**: [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md)
> — Phase D ("Expurgation"), 撤退ライン T-3
> ("expurgation lemma の Mathlib 不在 → 手書き ~30 行")
>
> **Scope**: Phase D の expurgation 2 ステップを実現するための Mathlib + InformationTheory
> API 在庫:
> - **D-1**: average over codebook ≤ 2ε  ⇒  ∃ specific codebook with Pe_avg ≤ 2ε
> - **D-2**: Pe_avg(codebook) ≤ 2ε       ⇒  ∃ subcodebook of size M/2 with max Pe ≤ 4ε
> - **D-3**: power constraint との bridge (∃ codebook 抽出 + ‖·‖ ≤ √(nP))
>
> **T-3 判定**: **T-3 不採用 (= D-1/D-2/D-3 すべて既存 Mathlib + InformationTheory 既存
> パターンで直接構成可能)**。手書きは「Markov pigeonhole 2 行」相当のみで
> ~30 行新規にはならない。詳細 §最終判定。

## 一行サマリ

Phase D で使う API は **D-1: 100% 既存** (Mathlib `exists_le_lintegral` + InformationTheory
`exists_codebook_le_avg`)、**D-2: 90% 既存** (Mathlib `mul_meas_ge_le_lintegral` +
`Finset.card_filter_le` で 5-10 行の組合せで導出) 、**D-3: 95% 既存**
(`norm_inner_le_norm` + `EuclideanSpace.volume_closedBall`)。**T-3 不採用推奨**。
ただし「**worst-half の Finset サブ抽出構成自体**」(`Fin (M/2) → Fin n → ℝ` を
`Fin M → Fin n → ℝ` から作る pinning) は plumbing で ~10 行手書き必要。

## 主定理の最終形 (再掲)

```lean
-- Phase D 全体 (再揚)
theorem awgn_exists_codebook_le_avg
    {M n : ℕ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε)
    (h_avg : ∫⁻ c, Pe c ∂(gaussianCodebook M n σ²) ≤ ENNReal.ofReal (2*ε)) :
    ∃ c_specific : Fin M → Fin n → ℝ, Pe c_specific ≤ ENNReal.ofReal (2*ε)

theorem awgn_expurgate_worst_half {M n : ℕ} (hM : 2 ≤ M)
    (c : Fin M → Fin n → ℝ) {ε : ℝ}
    (h_avg : (∑ m, Pe c m) ≤ M * (2*ε)) :
    ∃ (S : Finset (Fin M)), S.card ≥ M / 2 ∧ ∀ m ∈ S, Pe c m ≤ 4*ε

-- 最終 bridge → AwgnCode
theorem awgn_extract_AwgnCode … : ∃ c' : AwgnCode (M/2) n P, ∀ m, … ≤ 4*ε
```

### 証明戦略 (pseudo-Lean, ~10 行)

```lean
-- D-1: applying Mathlib `exists_le_lintegral` to codebook measure
have ⟨c, hc⟩ := exists_le_lintegral hPe_aemeas  -- ∃ c, Pe c ≤ ∫⁻ Pe
exact ⟨c, hc.trans h_avg⟩

-- D-2: contrapositive — if more than M/2 codewords had Pe > 4ε,
-- then ∑ Pe > (M/2) * 4ε = 2εM, contradiction.
by_contra h
push_neg at h
have : (Finset.univ.filter fun m => 4*ε < Pe c m).card > M / 2 := h
have : M * (2*ε) < ∑ m, Pe c m := … -- sum_lt_sum_of_subset + filter
linarith [h_avg]
```

---

## API 在庫テーブル (Axis 4)

### 4.1 平均 → 存在 (avg → exists individual; D-1 直接)

| 概念 | Mathlib / InformationTheory API | file:line | 状態 | Phase D での扱い |
|---|---|---|---|---|
| Bochner `∃ x, f x ≤ ∫ f` (probability) | `MeasureTheory.exists_le_integral` | `Mathlib/MeasureTheory/Integral/Average.lean:594` | ✅ **既存** | D-1 直接 (codebook measure = `IsProbabilityMeasure`) |
| Bochner `∃ x, ∫ f ≤ f x` | `MeasureTheory.exists_integral_le` | `Mathlib/MeasureTheory/Integral/Average.lean:598` | ✅ **既存** | (補助) |
| `lintegral` `∃ x, f x ≤ ∫⁻ f` (probability) | `MeasureTheory.exists_le_lintegral` | `Mathlib/MeasureTheory/Integral/Average.lean:738` | ✅ **既存** | D-1 直接 (Pe が `ℝ≥0∞` 値の場合) |
| `lintegral` `∃ x, ∫⁻ f ≤ f x` | `MeasureTheory.exists_lintegral_le` | `Mathlib/MeasureTheory/Integral/Average.lean:742` | ✅ **既存** | (補助) |
| 一般 `Measure ≠ 0` 版 (`laverage`) | `MeasureTheory.exists_le_laverage` | `Mathlib/MeasureTheory/Integral/Average.lean:706` | ✅ **既存** | (上位形式、`IsProbabilityMeasure` で `exists_le_lintegral` に specialise) |
| 一般 `Measure ≠ 0` 版 (`average`) | `MeasureTheory.exists_le_average` | `Mathlib/MeasureTheory/Integral/Average.lean:551` | ✅ **既存** | (上位形式) |
| InformationTheory 既存類似 (random codebook) | `exists_codebook_le_avg` | `InformationTheory/Shannon/ChannelCodingAchievability.lean:1479` | ✅ **既存** | **D-1 の直接 reference 実装**、写しで構成 |
| InformationTheory 既存類似 (BC abstract) | `bc_exists_codebook_of_avg_le` | `InformationTheory/Shannon/BroadcastChannelRandomCodebook.lean:208` | ✅ **既存** | D-1 の structural 形 (Finset 上の weighted-sum) |
| InformationTheory 既存類似 (uniform weight) | `bc_exists_codebook_of_sum_le` | `InformationTheory/Shannon/BroadcastChannelRandomCodebook.lean:256` | ✅ **既存** | D-1 の uniform 版 |

#### 4.1.1 — `MeasureTheory.exists_le_lintegral` 詳細

- **file:line**: `Mathlib/MeasureTheory/Integral/Average.lean:738`
- **signature (verbatim)**:
  ```lean
  theorem exists_le_lintegral (hf : AEMeasurable f μ) : ∃ x, f x ≤ ∫⁻ a, f a ∂μ := by
    simpa only [laverage_eq_lintegral] using exists_le_laverage (IsProbabilityMeasure.ne_zero μ) hf
  ```
- **enclosing variables** (file lines 61, 619, 723):
  ```lean
  variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
  -- section FirstMomentENNReal:
  variable {N : Set α} {f : α → ℝ≥0∞}
  -- section ProbabilityMeasure:
  variable [IsProbabilityMeasure μ]
  ```
- **type-class prerequisites**: `[IsProbabilityMeasure μ]` (from enclosing
  `section ProbabilityMeasure`)
- **explicit args**: `hf : AEMeasurable f μ`
- **conclusion**: `∃ x, f x ≤ ∫⁻ a, f a ∂μ`
- **applicability to Phase D**: **D-1 直接**。`f := codebook ↦ Pe(codebook)` を
  `gaussianCodebook M n σ²` 上に取り、`Pe : (Fin M → Fin n → ℝ) → ℝ≥0∞` の
  `AEMeasurable` が示せれば 1 行で `∃ specific codebook, Pe ≤ ∫⁻ Pe` が出る。
  `gaussianCodebook` が `IsProbabilityMeasure` ならそのまま適用可能。

#### 4.1.2 — `MeasureTheory.exists_le_integral` 詳細

- **file:line**: `Mathlib/MeasureTheory/Integral/Average.lean:594`
- **signature (verbatim)**:
  ```lean
  theorem exists_le_integral (hf : Integrable f μ) : ∃ x, f x ≤ ∫ a, f a ∂μ := by
    simpa only [average_eq_integral] using exists_le_average (IsProbabilityMeasure.ne_zero μ) hf
  ```
- **enclosing variables** (file lines 46, 185, 186, 579, 493):
  ```lean
  variable {α E F : Type*} {m0 : MeasurableSpace α}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
  -- section Properties:
  variable [NormedSpace ℝ E]
  variable {f : α → E} {m : MeasurableSpace α} {μ : Measure α}
  -- section FirstMomentReal:
  variable {N : Set α} {f : α → ℝ}
  -- section ProbabilityMeasure:
  variable [IsProbabilityMeasure μ]
  ```
- **type-class prerequisites**: `[IsProbabilityMeasure μ]`
- **explicit args**: `hf : Integrable f μ` (note: requires **`Integrable`** for
  Bochner; cf. `exists_le_lintegral` requires only `AEMeasurable`)
- **conclusion**: `∃ x, f x ≤ ∫ a, f a ∂μ`
- **applicability to Phase D**: **D-1 の `Real` 版**。Pe を `Real` 値で扱う方が
  簡明な場合に。**注意**: `Integrable` は `f ≥ 0` でも要請 — Pe は `0 ≤ Pe ≤ 1`
  故 trivially integrable on probability measure。

#### 4.1.3 — InformationTheory `exists_codebook_le_avg` 詳細 (D-1 の reference 実装)

- **file:line**: `InformationTheory/Shannon/ChannelCodingAchievability.lean:1479`
- **signature (verbatim)**:
  ```lean
  omit [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
    [MeasurableSingletonClass β] in
  theorem exists_codebook_le_avg
      {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
      (W : Channel α β) [IsMarkovKernel W]
      (p : Measure α) [IsProbabilityMeasure p]
      {M n : ℕ} (hM : 0 < M) {ε : ℝ} (B : ℝ)
      (h_avg :
        ∑ codebook : Codebook M n α,
          (codebookMeasure p M n).real {codebook} *
          ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B) :
      ∃ codebook : Codebook M n α,
        ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B
  ```
- **type-class prerequisites**: `[MeasurableSpace Ω]`, `[IsMarkovKernel W]`,
  `[IsProbabilityMeasure p]` (note: surrounding section has
  `[Fintype α] [Fintype β] [MeasurableSingletonClass α]` from earlier — see omit).
- **explicit args**: `μ`, `Xs`, `Ys`, `W`, `p`, `hM`, `B`, `h_avg`
- **conclusion**:
  `∃ codebook : Codebook M n α, ((codebookToCode μ Xs Ys hM ε codebook).averageErrorProb W).toReal ≤ B`
- **applicability to Phase D**: **AWGN 版の構造的 template**。`α := Fin n → ℝ`
  で `Fintype α` が崩れる (continuous) 為そのまま reuse は不可だが、proof body
  (lines 1491-1566) は `Finset.sum_lt_sum` + `mul_le_mul_of_nonneg_left` の
  汎用 contraposition で、AWGN 用に **`gaussianCodebook` を probability measure
  と認識した上で `exists_le_lintegral` を呼ぶ 5 行版**で置き換える方が短い。

---

### 4.2 Finset 上の order statistic / median 系 (D-2 worst-half throw away)

| 概念 | Mathlib / InformationTheory API | file:line | 状態 | Phase D での扱い |
|---|---|---|---|---|
| Finset min element exists | `Finset.exists_min_image` | `Mathlib/Data/Finset/Max.lean:531` | ✅ **既存** | (補助 — pigeonhole の base) |
| Finset max element exists | `Finset.exists_max_image` | `Mathlib/Data/Finset/Max.lean:525` | ✅ **既存** | (補助) |
| `Finset.min'`/`max'` (with `Nonempty`) | `Finset.min'`, `Finset.min'_le`, `Finset.max'_le` | `Mathlib/Data/Finset/Max.lean:194,217` | ✅ **既存** | (補助) |
| `Finset.filter` cardinality | `Finset.card_filter_le` | `Mathlib/Data/Finset/Card.lean` | ✅ **既存** | **D-2 直接** (Pe > 4ε の Finset card ≤ M で contradiction) |
| `∑ f < ∑ g → ∃ i, f i < g i` | `Finset.exists_lt_of_sum_lt` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:549` | ✅ **既存** | D-1 の純-Finset 形 |
| `∑ f ≤ ∑ g → ∃ i, f i ≤ g i` | `Finset.exists_le_of_sum_le` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:557` | ✅ **既存** | D-1 の純-Finset 形 |
| `Finset.sort` (order embedding) | `Finset.sort`, `Finset.orderEmbOfFin_apply` | `Mathlib/Data/Finset/Sort.lean` | ✅ **既存** | **不要** (D-2 は filter で構成可能、sort は要らない) |
| pigeonhole 型 (fiber-shape) | `Finset.exists_le_sum_fiber_of_nsmul_le_sum` | `Mathlib/Combinatorics/Pigeonhole.lean:323` | ✅ **既存** | (高機能だが D-2 にはオーバーキル) |
| 「Markov half throw-away」専用 lemma | — | — | ❌ **不在** | **手書き ~5-10 行** (`Finset.card_filter_le` + `Finset.sum_lt_sum_of_subset` 組合せ) |

#### 4.2.1 — `Finset.exists_min_image` 詳細

- **file:line**: `Mathlib/Data/Finset/Max.lean:531`
- **signature (verbatim)**:
  ```lean
  theorem exists_min_image (s : Finset β) (f : β → α) (h : s.Nonempty) :
      ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' :=
    @exists_max_image αᵒᵈ β _ s f h
  ```
- **enclosing variables** (file line 523):
  ```lean
  variable [LinearOrder α]
  ```
- **type-class prerequisites**: `[LinearOrder α]`
- **explicit args**: `s : Finset β`, `f : β → α`, `h : s.Nonempty`
- **conclusion**: `∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x'`
- **applicability to Phase D**: **D-2 の "min Pe" 補助**として有用だが、D-2
  本体は「**∃ M/2 個の codeword で Pe ≤ 4ε**」なので exists_min 1 個では不足。
  filter で「Pe ≤ 4ε」の Finset を取って card ≥ M/2 を示す方が直接。

#### 4.2.2 — `Finset.exists_le_of_sum_le` 詳細

- **file:line**: `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:557`
- **signature (verbatim)** (additive form, `to_additive` of `exists_le_of_prod_le'`):
  ```lean
  @[to_additive exists_le_of_sum_le]
  theorem exists_le_of_prod_le' (hs : s.Nonempty) (Hle : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i) :
      ∃ i ∈ s, f i ≤ g i := by
    contrapose! Hle with Hlt
    exact prod_lt_prod_of_nonempty' hs Hlt
  ```
- **enclosing variables** (file line 547):
  ```lean
  variable [CommMonoid M] [LinearOrder M] {f g : ι → M} {s t : Finset ι}
  -- + section LinearOrderedCancelCommMonoid (line 545) +
  variable [IsOrderedCancelMonoid M]   -- (line 555, applies to `exists_le_of_prod_le'`)
  ```
- **type-class prerequisites** (additive form via `to_additive`):
  `[AddCommMonoid M]`, `[LinearOrder M]`, `[IsOrderedCancelAddMonoid M]`
- **explicit args**: `hs : s.Nonempty`, `Hle : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`
- **conclusion**: `∃ i ∈ s, f i ≤ g i`
- **applicability to Phase D**: D-1 の **純-Finset 版**として有用。`g := fun _ => B`
  と置けば `∃ i ∈ s, f i ≤ B` (from `∑ f ≤ ∑ B = card * B`)。 ただし D-1 では
  `exists_le_lintegral` の方が integral 形を直接扱えて短い。

---

### 4.3 Markov 不等式 (4.2 の「worst-half throw-away」を構成する核)

| 概念 | Mathlib API | file:line | 状態 | Phase D での扱い |
|---|---|---|---|---|
| Markov (`lintegral`, `Measurable`) | `MeasureTheory.mul_meas_ge_le_lintegral` | `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:57` | ✅ **既存** | D-2 候補 (但し counting measure 経由は overkill) |
| Markov (`lintegral`, `AEMeasurable`) | `MeasureTheory.mul_meas_ge_le_lintegral₀` | `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:50` | ✅ **既存** | (同上、AE 版) |
| Markov 2-function (`Add`) | `MeasureTheory.lintegral_add_mul_meas_add_le_le_lintegral` | `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:32` | ✅ **既存** | (汎用) |
| Markov div 形 (`measure ≤ integral / ε`) | `MeasureTheory.meas_ge_le_lintegral_div` | `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:104` | ✅ **既存** | InformationTheory で `SMBAlgoetCover.lean:754, 2425` で利用実績有 |
| Markov Bochner (`Real`, `Integrable`) | `MeasureTheory.mul_meas_ge_le_integral_of_nonneg` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1175` | ✅ **既存** | D-2 候補 (Bochner 版) |
| Markov counting measure | (`mul_meas_ge_le_lintegral` を counting measure に specialise) | (同上) | ✅ **派生** | D-2 で `Finset` 上の「Pe > 4ε の元 ≤ M/2」を直接得るには不要 (filter card で十分) |

#### 4.3.1 — `MeasureTheory.mul_meas_ge_le_lintegral` 詳細

- **file:line**: `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:57`
- **signature (verbatim)**:
  ```lean
  /-- **Markov's inequality** also known as **Chebyshev's first inequality**. For a version assuming
  `AEMeasurable`, see `mul_meas_ge_le_lintegral₀`. -/
  theorem mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) :
      ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ :=
    mul_meas_ge_le_lintegral₀ hf.aemeasurable ε
  ```
- **enclosing variables** (file line 28):
  ```lean
  variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  ```
- **type-class prerequisites**: なし (general `Measure`)
- **explicit args**: `hf : Measurable f`, `ε : ℝ≥0∞`
- **conclusion**: `ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ`
- **applicability to Phase D**: **D-2 の "worst half" 構成**として、`μ` を
  `Fin M` 上の counting measure (`Measure.count` or uniform) に取って `f := Pe`
  と置けば直接適用可能。但し worst-half は **counting + Markov** より **filter
  card** の直接議論 (~5 行) の方が短い。

#### 4.3.2 — `MeasureTheory.mul_meas_ge_le_integral_of_nonneg` (Bochner) 詳細

- **file:line**: `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1175`
- **signature (verbatim)**:
  ```lean
  /-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
  theorem mul_meas_ge_le_integral_of_nonneg {f : α → ℝ} (hf_nonneg : 0 ≤ᵐ[μ] f)
      (hf_int : Integrable f μ) (ε : ℝ) : ε * μ.real { x | ε ≤ f x } ≤ ∫ x, f x ∂μ := by …
  ```
- **enclosing variables** (file lines 143, 185, 186):
  ```lean
  variable {α E F 𝕜 : Type*}
  -- section Properties:
  variable [NormedSpace ℝ E]
  variable {f : α → E} {m : MeasurableSpace α} {μ : Measure α}
  ```
- **type-class prerequisites**: なし (general `Measure`、`f` は `α → ℝ` で
  enclosing `[NormedSpace ℝ E]` には依存しない)
- **explicit args**: `hf_nonneg : 0 ≤ᵐ[μ] f`, `hf_int : Integrable f μ`, `ε : ℝ`
- **conclusion**: `ε * μ.real { x | ε ≤ f x } ≤ ∫ x, f x ∂μ`
- **applicability to Phase D**: **D-2 の `Real` 版**。`Pe : Fin M → ℝ` で 0 ≤ Pe
  なら直接適用可。但し再び `Finset.card` 直接議論の方が短い。

---

### 4.4 確率測度上の min / exists 系

| 概念 | Mathlib API | file:line | 状態 | Phase D での扱い |
|---|---|---|---|---|
| `IsProbabilityMeasure.ne_zero` | `MeasureTheory.IsProbabilityMeasure.ne_zero` | (deriv of `μ univ = 1`) | ✅ **既存** | `exists_le_lintegral` が内部使用 |
| `exists_le_laverage` (≠ 0 版) | `MeasureTheory.exists_le_laverage` | `Mathlib/MeasureTheory/Integral/Average.lean:706` | ✅ **既存** | `exists_le_lintegral` の上位 |
| `exists_laverage_le` | `MeasureTheory.exists_laverage_le` | `Mathlib/MeasureTheory/Integral/Average.lean:682` | ✅ **既存** | (補助) |
| `measure_lt_top_of_lt_integral` 系 | (該当無 — Loogle 0 hit) | — | ❌ **不在** (が不要) | 使わない |
| 「`lintegral_le_iff_exists_le_meas_pos`」 | (該当無 — Loogle 0 hit) | — | ❌ **不在** (が不要) | 使わない |

#### 4.4.1 — `MeasureTheory.exists_le_laverage` 詳細

- **file:line**: `Mathlib/MeasureTheory/Integral/Average.lean:706`
- **signature (verbatim)**:
  ```lean
  theorem exists_le_laverage (hμ : μ ≠ 0) (hf : AEMeasurable f μ) : ∃ x, f x ≤ ⨍⁻ a, f a ∂μ :=
  ```
- **enclosing variables** (file lines 61, 619, 696):
  ```lean
  variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α}
  -- section FirstMomentENNReal:
  variable {N : Set α} {f : α → ℝ≥0∞}
  -- section FiniteMeasure:
  variable [IsFiniteMeasure μ]
  ```
- **type-class prerequisites**: `[IsFiniteMeasure μ]`
- **explicit args**: `hμ : μ ≠ 0`, `hf : AEMeasurable f μ`
- **conclusion**: `∃ x, f x ≤ ⨍⁻ a, f a ∂μ`
- **applicability to Phase D**: `IsProbabilityMeasure` ならば `IsFiniteMeasure`
  + `μ ≠ 0` 自動 — Phase D で直接呼ぶより `exists_le_lintegral` 経由が短い。

---

### 4.5 Power constraint との合成補題 (D-3)

| 概念 | Mathlib API | file:line | 状態 | Phase D での扱い |
|---|---|---|---|---|
| EuclideanSpace ball volume | `EuclideanSpace.volume_closedBall` | `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:326` | ✅ **既存** | D-3 で `Pr[‖X‖ ≤ √(nP)]` 評価に使用 |
| EuclideanSpace ball volume (open) | `EuclideanSpace.volume_ball` | `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:309` | ✅ **既存** | (補助) |
| EuclideanSpace norm | `EuclideanSpace.norm_eq` | `Mathlib/Analysis/InnerProductSpace/PiL2.lean` | ✅ **既存** | (`‖x‖^2 = ∑ xᵢ^2`) |
| Cauchy-Schwarz | `norm_inner_le_norm` | `Mathlib/Analysis/InnerProductSpace/Basic.lean:455` | ✅ **既存** | (汎用) |
| `Real.add_pow_le_pow_mul_pow_of_sq` (multivariate CS) | (該当無 — Loogle 0 hit) | — | ❌ **不在** (が不要) | 通常の `norm_inner_le_norm` で十分 |

#### 4.5.1 — `EuclideanSpace.volume_closedBall` 詳細

- **file:line**: `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:326`
- **signature (verbatim)**:
  ```lean
  theorem volume_closedBall (x : EuclideanSpace ℝ ι) (r : ℝ) :
      volume (Metric.closedBall x r) = (.ofReal r) ^ card ι *
        .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1)) := by
    rw [addHaar_closedBall_eq_addHaar_ball, EuclideanSpace.volume_ball]
  ```
- **enclosing variables** (file lines 305, 307):
  ```lean
  variable (ι : Type*) [Nonempty ι] [Fintype ι]
  open Fintype Real MeasureTheory MeasureTheory.Measure ENNReal
  ```
- **type-class prerequisites**: `[Nonempty ι]`, `[Fintype ι]`
- **explicit args**: `x : EuclideanSpace ℝ ι`, `r : ℝ`
- **conclusion**:
  `volume (Metric.closedBall x r) = (.ofReal r) ^ card ι * .ofReal (√π ^ card ι / Gamma (card ι / 2 + 1))`
- **applicability to Phase D**: **D-3 power constraint 評価**で
  `volume (Metric.closedBall 0 (√(nP)))` を計算するのに必要。`ι := Fin n` で
  `card ι = n` が exposed。

#### 4.5.2 — `norm_inner_le_norm` 詳細

- **file:line**: `Mathlib/Analysis/InnerProductSpace/Basic.lean:455`
- **signature (verbatim)**:
  ```lean
  theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖
  ```
- **enclosing variables** (file `InnerProductSpace.Basic.lean`):
  ```lean
  variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  ```
- **type-class prerequisites**: `[RCLike 𝕜]`, `[NormedAddCommGroup E]`,
  `[InnerProductSpace 𝕜 E]`
- **explicit args**: `x y : E`
- **conclusion**: `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖`
- **applicability to Phase D**: power constraint で `|⟨x, y⟩| ≤ ‖x‖·‖y‖` 等が
  必要なら直接、但し AWGN 設定では `‖x‖² ≤ nP` のような 1 次元-norm bound のみ
  使うはずで、Cauchy-Schwarz は厳密には不要。

---

## 主要前提条件ボックス

`exists_le_lintegral` / `exists_le_integral` を使う前に **絶対**確認すべき項目:

- **`[IsProbabilityMeasure μ]` インスタンス**: `gaussianCodebook M n σ²` が
  `IsProbabilityMeasure` の typeclass を解決できるか。Phase A-2 で
  `instance : IsProbabilityMeasure (gaussianCodebook M n σ²)` を publish していれば自動。
- **`AEMeasurable Pe` (lintegral 版) / `Integrable Pe` (Bochner 版)**:
  `Pe : (Fin M → Fin n → ℝ) → ℝ≥0∞`、Phase C の decoder measurability 完了
  後に `Measurable Pe` から `AEMeasurable Pe` が自動。`Integrable` は
  `0 ≤ Pe ≤ 1` + probability measure で `Integrable Pe μ = (∫⁻ Pe ∂μ < ∞)`
  + `AEMeasurable` から従う。
- **空 Codebook の排除**: D-1 で `∃ codebook` が non-empty を要請。
  `gaussianCodebook` は `Fin M → Fin n → ℝ` 上の measure なので
  `Nonempty (Fin M → Fin n → ℝ)` (= `Nonempty (Fin n → ℝ)` が常に真) で OK。
  ただし `M = 0` のときは `Pi.instUnique`、`∀ m : Fin 0, ...` が vacuously true で
  D-2 が "size 0/2 = 0" になり最終 wrapper 段で `M ≥ 2` が必要。

`mul_meas_ge_le_integral_of_nonneg` (Bochner Markov、D-2 代替) の前提:
- **`0 ≤ᵐ[μ] f`**: Pe ≥ 0 (a.s. or pointwise) — codebook 上どこでも `0 ≤ Pe`
  なので trivial。
- **`Integrable f μ`**: Pe が bounded by 1 + IsProbabilityMeasure で自動。

`EuclideanSpace.volume_closedBall` の前提:
- **`[Nonempty ι]`**: `ι := Fin n` で `n ≥ 1` が必要。AWGN の `n` は
  asymptotic で `n → ∞` なので問題なし、ただし wrapper 段で `0 < n` を仮定。
- **`[Fintype ι]`**: `Fin n` で自動。

---

## 自作が必要な要素

優先度順:

### (1) D-2 "worst-half" 構成 — ~10 行 (中程度の plumbing、本物の数学はゼロ)

**Mathlib 不在の lemma**:
「`∑ m, Pe m ≤ M * (2ε) → ∃ S : Finset (Fin M), S.card ≥ M / 2 ∧ ∀ m ∈ S, Pe m ≤ 4ε`」
は単一 lemma としては不在。

**推奨実装** (~10 行):

```lean
lemma awgn_expurgate_worst_half {M : ℕ} (hM : 2 ≤ M)
    (Pe : Fin M → ℝ) (hPe_nn : ∀ m, 0 ≤ Pe m) {ε : ℝ} (hε : 0 < ε)
    (h_avg : (∑ m, Pe m) ≤ M * (2 * ε)) :
    (Finset.univ.filter fun m => Pe m ≤ 4 * ε).card ≥ M / 2 := by
  classical
  -- Contrapositive: if # {m : Pe m > 4ε} > M/2, sum > 2εM
  by_contra h
  push_neg at h
  set S_bad : Finset (Fin M) := Finset.univ.filter fun m => 4 * ε < Pe m
  have h_card_bad : S_bad.card > M / 2 := by
    have : S_bad.card + (Finset.univ.filter fun m => Pe m ≤ 4*ε).card = M := by
      rw [Finset.filter_card_add_filter_neg_card_eq_card]
      simpa using Finset.card_univ
    omega
  have h_sum_lt : M * (2 * ε) < ∑ m ∈ S_bad, Pe m := by
    calc M * (2 * ε) = (M / 2) * (4 * ε) + (M % 2) * (2 * ε) := by ring_nf; omega
      _ < S_bad.card * (4 * ε) := by
            have : (M / 2 : ℝ) < S_bad.card := by exact_mod_cast h_card_bad
            nlinarith
      _ ≤ ∑ m ∈ S_bad, Pe m :=
            Finset.card_nsmul_le_sum_of_le … -- via filter membership
  have : ∑ m ∈ S_bad, Pe m ≤ ∑ m, Pe m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => hPe_nn _
  linarith
```

工数: ~10-15 行。**「Markov の手書き」というほどではない** — `Finset.sum_le_sum_of_subset_of_nonneg` の組み合わせ 1 ステップ。

**落とし穴**:
- `M / 2 : ℕ` の整数除算と `(M : ℝ) / 2` の混在 — `ring_nf` + `Nat.cast` で
  処理 (上の `M % 2 * (2*ε)` 項)。
- `S_bad` を `filter` で定義する際 `decidable` が必要 → `classical` で OK。

### (2) D-3 sub-codebook の型変換 — ~5-10 行

Phase D-2 で得た `S : Finset (Fin M)` (card ≥ M/2) から `Fin (M/2) → Fin n → ℝ`
の sub-codebook を作る必要がある。標準形:

```lean
-- S.card ≥ M/2 から S' ⊆ S with S'.card = M/2 を取り、
-- Finset.equivFin (M/2) で Fin (M/2) ≃ S' を介して翻訳。
```

**Mathlib API**:
- `Finset.exists_subset_card_eq` (`s.card ≥ k → ∃ t ⊆ s, t.card = k`) — 既存
- `Finset.equivFin` (`Fin s.card ≃ s`) — 既存

工数: ~5-10 行 (pure plumbing)。

### (3) `IsProbabilityMeasure (gaussianCodebook M n σ²)` instance — Phase A の責務

D-1 で `exists_le_lintegral` を呼ぶには必須。Phase A-2 で publish 予定 — D 段では
存在前提。

---

## 撤退ラインへの距離

### **T-3 (Mathlib 不在 → 手書き ~30 行)**: **不発動**

**根拠**:

- **D-1**: `MeasureTheory.exists_le_lintegral` / `exists_le_integral` が
  Mathlib (Average.lean:738/594) に直接存在。`gaussianCodebook` が
  `IsProbabilityMeasure` インスタンスを持てば **1-2 行**で discharge 可能。
  さらに InformationTheory 内 `exists_codebook_le_avg` (CCAchievability.lean:1479)
  と `bc_exists_codebook_of_avg_le` (BCRandom.lean:208) が **構造的 template**
  として既存 — 写しで 30-50 行版が用意できる (が冗長)。

- **D-2**: 「worst-half throw-away」専用 lemma は Mathlib 不在だが、`Finset.filter`
  + `Finset.sum_le_sum_of_subset_of_nonneg` + `omega` の組合せで **~10 行**で
  構成可能。これは Cover-Thomas の textbook 2 行 (Markov inequality 適用) を
  Lean 化したもので、「手書き ~30 行」ほどの labor ではない (cf. 上 §自作要素 (1))。

- **D-3**: power constraint は `EuclideanSpace.volume_closedBall` 直接 + 標準的
  norm 計算で構成可能。Cauchy-Schwarz (`norm_inner_le_norm`) も既存。

**T-3 不採用の場合の Phase D 規模見積もり**: ~50 行 (D-1 ~5、D-2 ~15、D-3 ~30)。
plan §「規模見積もり」の Phase D = **50-80 行**枠内、むしろ下限寄り。

### 縮退案 (代替撤退ライン)

T-3 不採用でも、以下のいずれかで Phase D が想定より肥大した場合に発動候補:

- **T-3': D-2 の Fin-cardinality 計算で行き詰まり** → D-2 を「∃ subcodebook of
  size *just* 1, max Pe ≤ 4ε」(= D-1 の minimum-element 抽出のみ) に縮退、
  M/2 size の主張を `IsAwgnTypicalityHypothesis` regularity hyp に外出し。
  影響: achievability の rate `R` を `2R` に変えれば worst-half throw-away
  なしで `M' = M` のまま結論可能 — **要 hypothesis 修正**。
- **T-3'': D-3 power constraint の確率評価が肥大** → D-3 を Phase A-5
  (power constraint の確率版) と統合して再構成、Phase D に残さない。

---

## 着手 skeleton (`InformationTheory/Shannon/AWGNAchievabilityDischarge.lean` Phase D 部のみ抜粋)

```lean
/-! ## Phase D — Expurgation -/

import Mathlib.MeasureTheory.Integral.Average             -- exists_le_lintegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov     -- (D-2 で補助)
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls -- D-3
import Mathlib.Data.Finset.Card                            -- filter card
import Mathlib.Algebra.Order.BigOperators.Group.Finset    -- exists_le_of_sum_le

namespace InformationTheory.Shannon.AWGN

open MeasureTheory ENNReal Finset

variable {M n : ℕ} {σ² : ℝ≥0}

/-- **D-1**: Average codebook error → exists individual codebook. -/
theorem awgn_exists_codebook_le_avg
    (hM : 0 < M)
    (Pe : (Fin M → Fin n → ℝ) → ℝ≥0∞)
    (hPe_aemeas : AEMeasurable Pe (gaussianCodebook M n σ²))
    {B : ℝ≥0∞}
    (h_avg : ∫⁻ c, Pe c ∂(gaussianCodebook M n σ²) ≤ B) :
    ∃ c_specific : Fin M → Fin n → ℝ, Pe c_specific ≤ B := by
  -- 1 line: exists_le_lintegral + transitivity
  obtain ⟨c, hc⟩ := exists_le_lintegral hPe_aemeas
  exact ⟨c, hc.trans h_avg⟩

/-- **D-2**: Markov "worst-half throw-away" on Pe : Fin M → ℝ. -/
lemma awgn_expurgate_worst_half {M : ℕ} (hM : 2 ≤ M)
    (Pe : Fin M → ℝ) (hPe_nn : ∀ m, 0 ≤ Pe m) {ε : ℝ} (hε : 0 < ε)
    (h_avg : (∑ m, Pe m) ≤ M * (2 * ε)) :
    ∃ S : Finset (Fin M), M / 2 ≤ S.card ∧ ∀ m ∈ S, Pe m ≤ 4 * ε := by
  sorry  -- ~10 行 (cf. §自作要素 (1))

/-- **D-3**: extract `AwgnCode (M/2) n P` from D-1 + D-2 + power constraint. -/
theorem awgn_extract_AwgnCode
    (P : ℝ) (hP : 0 < P)
    (c : Fin M → Fin n → ℝ)
    (h_pwr : ∀ m, (∑ i, (c m i)^2) ≤ n * P)
    (S : Finset (Fin M)) (hS_card : M / 2 ≤ S.card)
    (h_pe : ∀ m ∈ S, individual_error m ≤ 4 * ε) :
    ∃ c' : AwgnCode (M / 2) n P, ∀ m, individual_error_of c' m ≤ 4 * ε := by
  sorry  -- ~5-10 行 (Finset.equivFin + AwgnCode constructor)

end InformationTheory.Shannon.AWGN
```

---

## 最終判定

| 判定軸 | 状態 |
|---|---|
| **T-3 採用 / 不採用** | **不採用** |
| **D-1 既存率** | 100% (Mathlib `exists_le_lintegral` 直接) |
| **D-2 既存率** | 90% (Mathlib `Finset.filter` + `sum_le_sum_of_subset_of_nonneg` 組合せ ~10 行) |
| **D-3 既存率** | 95% (Mathlib `volume_closedBall` 直接 + plumbing) |
| **手書き要素** | D-2 worst-half (~10 行) + D-3 sub-codebook 型変換 (~5-10 行) |
| **Phase D 規模見積もり (T-3 不採用)** | ~50 行 (plan §「規模見積もり」の **50-80 行**枠内下限) |
| **plan §「失敗時 fallback」発動** | なし |

### 一行結論

**T-3 不採用**: Mathlib `MeasureTheory.exists_le_lintegral` (Average.lean:738) +
InformationTheory 既存 `exists_codebook_le_avg` パターンで D-1 は 5 行で完成、D-2 は
`Finset` 上の filter cardinality 議論 ~10 行 (本物の Markov 手書きではなく、
高校レベル算術)、D-3 は `EuclideanSpace.volume_closedBall` 直接適用。Phase D
全体は plan §「規模見積もり」の 50 行下限で収まる。
