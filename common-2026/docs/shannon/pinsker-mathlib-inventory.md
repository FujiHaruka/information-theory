# Pinsker Mathlib API インベントリ (B-5)

各候補補題は `file:line` / 完全シグネチャ (`[...]` 型クラス verbatim) / 結論形 verbatim で記録。

## 1. KullbackLeibler 系 (Mathlib)

### klFun (`Mathlib/InformationTheory/KullbackLeibler/KLFun.lean`)

- **`InformationTheory.klFun`** (`KLFun.lean:53`)
  ```
  noncomputable def klFun (x : ℝ) : ℝ := x * log x + 1 - x
  ```

- **`InformationTheory.klFun_apply`** (`KLFun.lean:55`)
  `(x : ℝ) : klFun x = x * log x + 1 - x := rfl`

- **`InformationTheory.klFun_zero`** (`KLFun.lean:57`)
  `klFun 0 = 1`

- **`InformationTheory.klFun_one`** (`KLFun.lean:59`)
  `klFun 1 = 0`

- **`InformationTheory.klFun_nonneg`** (`KLFun.lean:149`)
  `(hx : 0 ≤ x) : 0 ≤ klFun x`

- **`InformationTheory.klFun_eq_zero_iff`** (`KLFun.lean:151`)
  `(hx : 0 ≤ x) : klFun x = 0 ↔ x = 1`

- **`InformationTheory.hasDerivAt_klFun`** (`KLFun.lean:89`)
  `(hx : x ≠ 0) : HasDerivAt klFun (log x) x`

- **`InformationTheory.convexOn_klFun`** (`KLFun.lean:67`)
  `: ConvexOn ℝ (Ici 0) klFun`

### klDiv (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`)

- **`InformationTheory.toReal_klDiv_of_measure_eq`** (`Basic.lean:164`)
  ```
  lemma toReal_klDiv_of_measure_eq
      {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}
      [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (h : μ ≪ ν) (h_eq : μ univ = ν univ) :
      (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ
  ```

- **`InformationTheory.klDiv_ne_top`** (`Basic.lean:103`)
  ```
  lemma klDiv_ne_top (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : klDiv μ ν ≠ ∞
  ```

- **`InformationTheory.mul_klFun_le_toReal_klDiv`** (`Basic.lean:338`)
  ```
  lemma mul_klFun_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
      ν.real univ * klFun (μ.real univ / ν.real univ) ≤ (klDiv μ ν).toReal
  ```
  (確率測度 univ = 1 では 0 ≤ klDiv に退化、本シードでは直接使わず参考)

- **`InformationTheory.klDiv_eq_zero_iff`** (`Basic.lean:377`)
  ```
  lemma klDiv_eq_zero_iff
      [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
      klDiv μ ν = 0 ↔ μ = ν
  ```

## 2. negMulLog / log 系

- **`Real.negMulLog`** (`Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`)
  ```
  noncomputable def negMulLog (x : ℝ) : ℝ := -(x * log x)
  ```

- **`Real.negMulLog_le_one_sub_self`** (`NegMulLog.lean`)
  `(hx : 0 ≤ x) : negMulLog x ≤ 1 - x` (上界、Pinsker では使えないが参考)

- **`Real.log_le_sub_one_of_le_one`** / **`Real.log_le_sub_one_of_pos`** 等の log 上界、Pinsker では下界が必要 (使えない、参考)

## 3. Cauchy-Schwarz (Finset)

- **`Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul`** (`Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:126`)
  ```
  lemma sum_sq_le_sum_mul_sum_of_sq_eq_mul
      [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]
      (s : Finset ι) {r f g : ι → R}
      (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
      (ht : ∀ i ∈ s, r i ^ 2 = f i * g i) :
      (∑ i ∈ s, r i) ^ 2 ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i
  ```
  **本シードで使う**。`r_i := |p_i - q_i|`, `f_i := (p_i - q_i)^2 / (p_i + 2 q_i)` (q_x=0 のときは 0 設定), `g_i := p_i + 2 q_i`。

- **`Finset.sum_mul_sq_le_sq_mul_sq`** (`Finset.lean:150`)
  ```
  lemma sum_mul_sq_le_sq_mul_sq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
      [ExistsAddOfLE R] (s : Finset ι) (f g : ι → R) :
      (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2
  ```

## 4. Real.sqrt API (`Mathlib/Data/Real/Sqrt.lean`)

- **`Real.le_sqrt`** (`Sqrt.lean:240`)
  `(hx : 0 ≤ x) (hy : 0 ≤ y) : x ≤ √y ↔ x ^ 2 ≤ y`

- **`Real.le_sqrt_of_sq_le`** (`Sqrt.lean:258`)
  `(h : x ^ 2 ≤ y) : x ≤ √y`

- **`Real.sqrt_le_sqrt`** (`Sqrt.lean:209`)
  `(h : x ≤ y) : √x ≤ √y`

- **`Real.sqrt_nonneg`** (similar location)
  `(x : ℝ) : 0 ≤ √x`

## 5. Measure rnDeriv 系 (`MaxEntropy` から踏襲)

- **`MeasureTheory.Measure.withDensity_rnDeriv_eq`**
  `(μ ν : Measure α) (h : μ ≪ ν) : ν.withDensity (μ.rnDeriv ν) = μ`

- **`MeasureTheory.withDensity_apply`**
  `(s : MeasurableSet) : (ν.withDensity f) s = ∫⁻ x in s, f x ∂ν`

- **`MeasureTheory.lintegral_singleton`**
  `(f) (a) : ∫⁻ x in {a}, f x ∂ν = f a * ν {a}`

- **`MeasureTheory.integral_fintype`** — Bochner ∫ on Fintype を Finset.sum に展開

## 6. 既存 Common2026 API

- **`Common2026/Shannon/MaxEntropy.lean:123`** — Bochner per-element rnDeriv 識別パターンの完全実例
  (Pinsker でほぼ同形を踏襲、`P.real{x} / Q.real{x}` で書き換える)

- **`Common2026/Shannon/Bridge.lean:216`** — `klDiv_discrete_toReal_eq_sum` (private、参考のみ)

## 7. 検証済 0 件 (loogle)

- `Pinsker` (専用 API なし)
- `tvNorm`, `hellinger`, `dataProcessing`, `logSum` (関連 API なし、本ファイル内で定義)
- `klFun, sq` (klFun の二次下界 0 件)
- `klDiv, map` (DPI / pushforward 形 0 件)

⟹ 点別 Pinsker 補題 + TV 定義 + 主定理は全て本シードで新規 (Mathlib 上流 PR の最有力候補 strut)。
