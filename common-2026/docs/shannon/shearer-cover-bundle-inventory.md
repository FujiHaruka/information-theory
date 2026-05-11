# Shearer cover bundle (B-2 + B-9) — Mathlib API inventory

## loogle 探索結果 (2026-05-11)

- `"Brascamp"`: **0 件**
- `"loomis"`: **0 件**
- `"edgeBoundary"`: **0 件**
- `"BooleanCube"`: **0 件**
- `"hypercube"`: **0 件**

Mathlib に Brascamp-Lieb / Loomis-Whitney / Boolean-cube isoperimetry の既存形式化なし。本 bundle はゼロから定理を述べる必要あり。

## 再利用する既存補題

### Shearer engine
- `Common2026.Shannon.HanDShearer.shearer_inequality`
  - シグネチャ (verbatim from `Common2026/Shannon/HanDShearer.lean:41`):
    ```
    theorem shearer_inequality
        {ι : Type*} [Fintype ι]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
        (S : ι → Finset (Fin n))
        {k : ℕ}
        (hk : ∀ i : Fin n,
          k ≤ (Finset.univ.filter (fun j : ι => i ∈ S j)).card) :
        (k : ℝ) * jointEntropy μ Xs
          ≤ ∑ j : ι, jointEntropySubset μ Xs (S j)
    ```
  - 型クラス前提: `[Fintype ι]`, `[IsProbabilityMeasure μ]`, `[Fintype α]`, `[DecidableEq α]`, `[Nonempty α]`, `[MeasurableSpace α]`, `[MeasurableSingletonClass α]`, `[MeasurableSpace Ω]`。
  - 結論形: `(k : ℝ) * jointEntropy μ Xs ≤ ∑ j : ι, jointEntropySubset μ Xs (S j)` — **任意 ι, 任意 S** で既に汎用。

### Entropy ≤ log #image
- `Common2026.Shannon.entropy_le_log_image_card`
  - シグネチャ (verbatim from `Common2026/Shannon/LoomisWhitney.lean:125`):
    ```
    theorem entropy_le_log_image_card
        {β γ : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
        [MeasurableSpace β] [MeasurableSingletonClass β]
        [Fintype γ] [DecidableEq γ] [Nonempty γ]
        [MeasurableSpace γ] [MeasurableSingletonClass γ]
        {A : Finset β} (hA : A.Nonempty)
        (f : β → γ) (hf : Measurable f) :
        entropy (uniformOn (A : Set β)) f ≤ Real.log (A.image f).card
    ```
  - 結論形: `entropy μ f ≤ Real.log (A.image f).card`。
  - **任意の measurable `f : β → γ`** で適用可能。LW 専用ではない。

### Entropy of uniformOn = log #A
- `Common2026.Shannon.entropy_uniformOn_eq_log_card` (`LoomisWhitney.lean:46`):
  ```
  theorem entropy_uniformOn_eq_log_card
      {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
      {A : Finset β} (hA : A.Nonempty) :
      entropy (uniformOn (A : Set β)) (id : β → β) = Real.log A.card
  ```

### jointEntropySubset
- `Common2026.Shannon.jointEntropySubset` (`HanD.lean:50`):
  ```
  noncomputable def jointEntropySubset
      (μ : Measure Ω) (Xs : Fin n → Ω → α) (S : Finset (Fin n)) : ℝ :=
    entropy μ (fun ω (i : S) => Xs i.val ω)
  ```

## 標準 Mathlib lemmas (使用見込み)

- `Real.log_prod (s : Finset ι) (f : ι → ℝ) : (∀ i ∈ s, f i ≠ 0) → log (∏ i ∈ s, f i) = ∑ i ∈ s, log (f i)`
- `Real.log_pow (n : ℕ) (x : ℝ) : log (x ^ n) = n * log x`
- `Real.log_le_log_iff (hx : 0 < x) (hy : 0 < y) : log x ≤ log y ↔ x ≤ y`
- `Finset.card_image_le : (s.image f).card ≤ s.card`
- `MeasurableEquiv.piCongrLeft (π : β → Type*) (f : α ≃ β) : (∀ a, π (f a)) ≃ᵐ (∀ b, π b)`
- `isProbabilityMeasure_uniformOn` (`MeasureTheory.Probability.UniformOn`)
- `Finset.prod_pos`, `pow_pos`

## 結論

- Mathlib に既存 Brascamp-Lieb なし → ゼロから述べる。
- Shearer engine + `entropy_le_log_image_card` + `entropy_uniformOn_eq_log_card` の 3 つを **任意 cover** で並べるだけ。新規補題は `projectionSubset` 定義 + 1 つの reshape lemma のみ。
