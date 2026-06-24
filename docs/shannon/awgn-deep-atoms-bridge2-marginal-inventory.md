# AWGN bridge ② — marginal-collapse + N₀-threshold 資産棚卸し (atoms d / e / c)

> 親 plan: [`docs/shannon/awgn-achievability-walls-discharge-plan.md`](awgn-achievability-walls-discharge-plan.md)
> (deep atoms ブロック :286-293)。本ファイルは **measure-identity collapse + N₀ template** 部分のみを担当。
> bridge ① (`klDiv_n = n·I` の同定) は別 agent が棚卸し中 — 本ファイルでは term2 の **Q-marginal collapse**
> と **N₀ 構成テンプレート** のみ扱い、exp-decay の `klDiv_n` 中身には踏み込まない。

## 一行サマリ

**3 atom (d=term1 J-marginal / e=term2 Q-marginal / c=N₀ 閾値) が要求する measure-identity
collapse 資産は Mathlib + in-project でほぼ完備 (既存率 ~90%)。唯一の genuine gap は「2点 pi-marginal
`(Measure.pi ν).map (c↦(c m, c m')) = (ν m).prod (ν m')`」だが、これは in-project の
`gaussianCodebook_indepFun_codewords` + Mathlib `indepFun_iff_map_prod_eq_prod_map_map` で
self-build 不要 (既存 IndepFun 経由で直結)。N₀ 閾値 (atom c) は同 file の `N_doubling` 構成
(:1193-1249) が完全な template で、必要算術 (`Nat.le_ceil` / `Real.exp_le_exp`) は全て in-project
既使用。撤退ラインは触れない (deep atom は既に honest sorry+@residual の retreat 出口に着地済み)。**最大の
落とし穴: term1 の `f1` は「per-vector channel = `(Measure.pi noise).map (x+·)`」を経由する必要があり、
これは `pi_map_pi` + `gaussianReal_map_const_add` の合成で、`Measure.compProd_apply` の素直な適用では
ない (channel が `gaussianReal x N` の per-coordinate pi なので、joint J への変換は change-of-variables
を 1 段挟む)。**

---

## 対象 atom の現在形 (consumer 逐語)

`InformationTheory/Shannon/AWGN/AchievabilityDischarge.lean` `awgn_random_coding_union_bound` (:498) 内:

```lean
-- atom (c) :538-540  — N₀ 閾値 (alias-decay threshold)
case N₀ => sorry   -- @residual(plan:awgn-achievability-walls-discharge-plan)

-- atom (d) :773-777 — term1 J-marginal collapse
rw [hpt, ← lintegral_map hf1_meas (measurable_pi_apply m),
    gaussianCodebook_codeword_law M n P.toNNReal m]
-- 残 goal: ∫⁻ x, f1 x ∂(Measure.pi fun _ => gaussianReal 0 P.toNNReal) ≤ ENNReal.ofReal ε
--   where  f1 x = (Measure.pi fun i => awgnChannel N h_meas (x i)) {y | (x, y) ∉ A}
sorry              -- @residual(plan:awgn-achievability-walls-discharge-plan)

-- atom (e) :787-793 — term2 Q-marginal collapse + 和 + exp 算術
-- goal: ∑ m' ∈ univ.erase m, ∫⁻ codebook,
--          (Measure.pi fun i => awgnChannel N h_meas (codebook m i)) {y | (codebook m', y) ∈ A}
--        ∂(gaussianCodebook M n P.toNNReal)  ≤  ENNReal.ofReal ε
sorry              -- @residual(plan:awgn-achievability-walls-discharge-plan)
```

`J` / `Q` の定義 (consumer :545-551, Walls の `continuousAepGaussian_holds` :127-141 と逐語同型):
- `J := ((Measure.pi (gaussianReal 0 P')).prod (Measure.pi (gaussianReal 0 N))).map (fun p => (p.1, fun i => p.1 i + p.2 i))` — joint codebook+noise law (X, X+Z)
- `Q := (Measure.pi (gaussianReal 0 P')).prod (Measure.pi (gaussianReal 0 (P'+N)))` — independent-pair product law (X, X'+Z 独立)
- `Wch codebook := Measure.pi (fun i => awgnChannel N h_meas (codebook m i))` — channel output law
- `E1 codebook := {y | (codebook m, y) ∉ A}` / `E2 codebook m' := {y | (codebook m', y) ∈ A}`

---

## 中核 in-project 定義 (verbatim)

| 定義 | file:line | signature verbatim | 結論形 |
|---|---|---|---|
| `IsAwgnChannelMeasurable` | `AWGN/Basic.lean:66` | `def IsAwgnChannelMeasurable (N : ℝ≥0) : Prop := Measurable (fun x : ℝ => gaussianReal x N)` | `Measurable (fun x : ℝ => gaussianReal x N)` |
| `awgnChannel` | `AWGN/Basic.lean:76` | `noncomputable def awgnChannel (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Channel ℝ ℝ where toFun x := gaussianReal x N; measurable' := h_meas` | kernel, fibre = `gaussianReal x N` |
| `awgnChannel_apply` | `AWGN/Basic.lean:81` | `@[simp] lemma awgnChannel_apply (N) (h_meas) (x : ℝ) : (awgnChannel N h_meas) x = gaussianReal x N := rfl` | `(awgnChannel N h_meas) x = gaussianReal x N` |
| `gaussianCodebook` | `AWGN/AchievabilityDischarge.lean:63` | `noncomputable def gaussianCodebook (M n : ℕ) (σsq : ℝ≥0) : Measure (Fin M → Fin n → ℝ) := Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 σsq))` | 2段 `Measure.pi` |
| `gaussianCodebook_codeword_law` | `AWGN/AchievabilityDischarge.lean:79` | `theorem gaussianCodebook_codeword_law (M n : ℕ) (σsq : ℝ≥0) (m : Fin M) : (gaussianCodebook M n σsq).map (fun c : Fin M → Fin n → ℝ => c m) = Measure.pi (fun _ : Fin n => gaussianReal 0 σsq)` | `…map (·m) = Measure.pi (gaussianReal 0 σsq)` |
| `gaussianCodebook_indepFun_codewords` | `AWGN/AchievabilityDischarge.lean:94` | `theorem gaussianCodebook_indepFun_codewords (M n : ℕ) (σsq : ℝ≥0) {m m' : Fin M} (hmm' : m ≠ m') : IndepFun (fun c => c m) (fun c => c m') (gaussianCodebook M n σsq)` | `IndepFun (·m) (·m') (gaussianCodebook …)` |

`awgnChannel x = gaussianReal x N` で、`gaussianReal x N = (gaussianReal 0 N).map (x + ·)` は Mathlib
`gaussianReal_map_const_add` (μ=0) で 1 行 (`AWGN/F1Discharge.lean:51` で既に使用)。

---

## C1. in-project 既存 joint-law / output-law 資産

| 概念 | API (in-project) | file:line | 状態 | atom での扱い |
|---|---|---|---|---|
| codeword marginal (単一) | `gaussianCodebook_codeword_law` | `AchievabilityDischarge.lean:79` | ✅ 既存 | **atom (d) で既に rw 済** (:774)。term2 でも各成分 marginal に使う |
| 2点独立 (codewords) | `gaussianCodebook_indepFun_codewords` | `AchievabilityDischarge.lean:94` | ✅ 既存 | **atom (e) の中核** — m≠m' で `c m ⊥ c m'` を供給 (Q への分解の起点) |
| channel marginal = noise translate | `awgnChannel_apply` + `gaussianReal_map_const_add` | `Basic.lean:81` / Mathlib | ✅ 既存 | per-letter `(channel x)(B) = (gaussianReal 0 N).map(x+·) B` |
| per-letter Y-law (X+Z) | `gaussianReal_conv_gaussianReal` / `gaussianReal_add_gaussianReal_of_indepFun` | Mathlib (下記 C3) | ✅ 既存 | `μX ∗ μZ = μY = gaussianReal 0 (P'+N)` |
| kernel section measurability | `Kernel.measurable_kernel_prodMk_left` | Mathlib | ✅ 既存 | **既に使用** (`hf1_meas` :770, `hAE_E1` :657) |
| awgnCodebookKernel (m-th 射影 kernel) | private `awgnCodebookKernel` | `AchievabilityDischarge.lean:431` | ✅ 既存 | AE-measurability に既使用 (:653, 672) |

**converse 側資産の再利用性**: converse (`Converse.lean:228`) は
`(μ.map X_i).prod (μ.map Y_i) = perLetterXLaw.prod (outputDistribution …)` を構成しているが、
これは **per-letter (1次元) の product 同定** で、本 atom が要求する **n次元 pi 上の joint J / Q** とは
shape が異なる。`MIBridge.lean:118-126` の `IsAwgnOutputGaussian` (output marginal = `gaussianReal 0 (P+N)`)
も per-letter 形。**直接再利用できる「n次元 joint J = ∫⁻ channel」補題は AWGN family に不在** → atom (d)/(e)
の core は新規 (ただし下記 C2-C4 の Mathlib primitive で素直に組める plumbing)。

---

## C2. Mathlib compProd / prod 資産 (集合測度 ↔ ∫⁻ section)

Prod.lean section context: `variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]`
`variable {μ μ' : Measure α} {ν ν' : Measure β} {τ : Measure γ}` + `variable [SFinite ν]` (prod_apply の直前)。

| API | file:line | signature verbatim (型クラス前提括弧ごと) | 結論形 verbatim |
|---|---|---|---|
| `Measure.prod_apply` | `Mathlib/MeasureTheory/Measure/Prod.lean:223` | `theorem prod_apply [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :` | `μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ` |
| `MeasureTheory.lintegral_prod` | `Mathlib/MeasureTheory/Measure/Prod.lean:996` | `theorem lintegral_prod [SFinite ν] (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :` | `∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ` |
| `Measure.compProd_apply` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:61` | `lemma compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) :` | `(μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ` |
| `Measure.compProd_apply_univ` | `…/MeasureCompProd.lean:66` | `@[simp] lemma compProd_apply_univ [SFinite μ] [IsMarkovKernel κ] :` | `(μ ⊗ₘ κ) univ = μ univ` |
| `Kernel.lintegral_compProd` | `Mathlib/Probability/Kernel/Composition/CompProd.lean:370` | `theorem lintegral_compProd (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ) [IsSFiniteKernel η] {f : β × γ → ℝ≥0∞} (hf : Measurable f) :` | `∫⁻ z, f z ∂(κ ⊗ₖ η) a = ∫⁻ x, ∫⁻ y, f (x, y) ∂η (a, x) ∂κ a` |

**注**: atom (d)/(e) は `Measure.prod`/`Measure.pi` ベースで進めるのが素直 (J/Q が `prod` 形で定義済)。
`compProd_apply` は「`μX ⊗ₘ channel = J` を組む」流派 (plan の表現「μX⊗channel=J」) の場合に使うが、J は
**`(μX.prod μZ).map (x,z)↦(x,x+z)`** 形で定義されているので、`compProd` 経由より下記 C3 の
**change-of-variables** (`Measure.map` + `lintegral_map` / `Measure.map_apply`) の方が J の定義に直結する。

`Measure.pi (gaussianReal 0 …)` は `IsProbabilityMeasure` (autoinfer) → `SFinite` も自動成立、型クラス前提
`[SFinite ν]` / `[SFinite μ]` は全て充足される。

---

## C3. Gaussian 和の law (per-letter Y-marginal) — Mathlib 完備

Gaussian/Real.lean section context: `section Transformations` 直下 `variable {μ : ℝ} {v : ℝ≥0}`;
`gaussianReal_add_gaussianReal_of_indepFun` は独立の `variable {Ω} {mΩ} {P}`。

| API | file:line | signature verbatim | 結論形 verbatim |
|---|---|---|---|
| `gaussianReal_map_const_add` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:292` | `lemma gaussianReal_map_const_add (y : ℝ) :` (section vars `{μ : ℝ} {v : ℝ≥0}`) | `(gaussianReal μ v).map (y + ·) = gaussianReal (μ + y) v` |
| `gaussianReal_map_add_const` | `…/Gaussian/Real.lean:278` | `lemma gaussianReal_map_add_const (y : ℝ) :` | `(gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v` |
| `gaussianReal_conv_gaussianReal` | `…/Gaussian/Real.lean:613` | `lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} :` | `(gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)` |
| `gaussianReal_add_gaussianReal_of_indepFun` | `…/Gaussian/Real.lean:624` | `lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) :` | `P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)` |

**per-letter → pi 持ち上げ**: `Measure.pi (fun i => awgnChannel N h_meas (x i))`
= (各成分 `awgnChannel x_i = gaussianReal x_i N`) = `(Measure.pi (fun _ => gaussianReal 0 N)).map (fun z i => x i + z i)`
via `pi_map_pi` (下記 C4 表) + `gaussianReal_map_const_add` (各成分の `gaussianReal x_i N = (gaussianReal 0 N).map (x_i + ·)`)。
これが atom (d) で `f1` を「noise 上の積分」に書き換える鍵。

| API (pi 持ち上げ) | file:line | signature verbatim | 結論形 |
|---|---|---|---|
| `MeasureTheory.pi_map_pi` | `Mathlib/MeasureTheory/Constructions/Pi.lean:390` | `lemma pi_map_pi {X Y : ι → Type*} {mX : ∀ i, MeasurableSpace (X i)} {μ : (i : ι) → Measure (X i)} [∀ i, MeasurableSpace (Y i)] {f : (i : ι) → X i → Y i} [hμ : ∀ i, SigmaFinite ((μ i).map (f i))] (hf : ∀ i, AEMeasurable (f i) (μ i)) :` | `(Measure.pi μ).map (fun x i ↦ (f i (x i))) = Measure.pi (fun i ↦ (μ i).map (f i))` |

---

## C4. pi の 2点 marginal (atom e の中核) — 名前付き直接補題は不在、IndepFun 経由で完備

Independence/Basic.lean section context (:640): `variable {β β' γ γ' : Type*} {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}`。

| API | file:line | signature verbatim (型クラス前提括弧ごと) | 結論形 verbatim |
|---|---|---|---|
| **`indepFun_iff_map_prod_eq_prod_map_map`** | `Mathlib/Probability/Independence/Basic.lean:701` | `theorem indepFun_iff_map_prod_eq_prod_map_map {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsFiniteMeasure μ] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :` | `f ⟂ᵢ[μ] g ↔ μ.map (fun ω ↦ (f ω, g ω)) = (μ.map f).prod (μ.map g)` |
| `indepFun_iff_map_prod_eq_prod_map_map'` | `…/Independence/Basic.lean:685` | `theorem …' {mβ} {mβ'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) :` | 同上 (有限性なし版) |
| `MeasureTheory.measurePreserving_eval` | `Mathlib/MeasureTheory/Constructions/Pi.lean:407` | `lemma measurePreserving_eval [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :` | `MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i)` |
| `MeasureTheory.measurePreserving_piFinTwo` (参考、Fin 2 のみ) | `…/Constructions/Pi.lean:845` | `theorem measurePreserving_piFinTwo {α : Fin 2 → Type u} {m : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] :` | `MeasurePreserving (MeasurableEquiv.piFinTwo α) (Measure.pi μ) ((μ 0).prod (μ 1))` |

**2点 pi-marginal の直接補題 `(Measure.pi ν).map (c↦(c m, c m')) = (ν m).prod (ν m')` は不在**
(loogle `|- MeasureTheory.Measure.map (MeasureTheory.Measure.pi _) _ = MeasureTheory.Measure.prod _ _` →
**Found 0**)。一般 index pair `(m, m')` 用は `piFinTwo` (Fin 2) / `piFinSuccAbove` のみで非汎用。

**→ self-build 不要。既存 IndepFun 経由で直結:**
```
gaussianCodebook_indepFun_codewords M n σsq hmm'                    -- IndepFun (·m) (·m') (gaussianCodebook …)
  |> (indepFun_iff_map_prod_eq_prod_map_map h_aemeas_m h_aemeas_m').mp
  -- ⊢ (gaussianCodebook …).map (c ↦ (c m, c m')) = (…map(·m)).prod(…map(·m'))
  -- rw [gaussianCodebook_codeword_law, gaussianCodebook_codeword_law]
  -- = (Measure.pi (gaussianReal 0 σsq)).prod (Measure.pi (gaussianReal 0 σsq))
```
`[IsFiniteMeasure (gaussianCodebook …)]` は `gaussianCodebook_isProbabilityMeasure` (:70) から autoinfer。
AEMeasurable `(·m)` / `(·m')` は `(measurable_pi_apply m).aemeasurable`。

---

## C5. 補助算術 (J Aᶜ ≤ ε の導出)

`hA_mass` の形 (consumer :508-509): `J A ≥ ENNReal.ofReal (1 - ε)`。J は probability measure (`Measure.map`
of prod、autoinfer)。`J Aᶜ ≤ ENNReal.ofReal ε` への導出に使う:

| API | file:line | signature verbatim (型クラス前提括弧ごと) | 結論形 verbatim |
|---|---|---|---|
| `prob_compl_eq_one_sub` | `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:150` | `theorem prob_compl_eq_one_sub [IsProbabilityMeasure μ] (hs : MeasurableSet s) :` (section `{μ : Measure α}`) | `μ sᶜ = 1 - μ s` |
| `measure_compl` | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:303` | `theorem measure_compl (h₁ : MeasurableSet s) (h_fin : μ s ≠ ∞) :` | `μ sᶜ = μ univ - μ s` |
| `ENNReal.ofReal_sub` | `Mathlib/Data/ENNReal/Operations.lean:448` | `theorem ofReal_sub (p : ℝ) {q : ℝ} (hq : 0 ≤ q) :` | `ENNReal.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q` |

**導出 chain**: `J Aᶜ = 1 - J A` (`prob_compl_eq_one_sub hA_meas`) `≤ 1 - ofReal(1-ε)` (`tsub_le_tsub_left hA_mass 1`)
`= ofReal 1 - ofReal(1-ε) = ofReal(1 - (1-ε)) = ofReal ε` (`ENNReal.ofReal_one` ▸ `ofReal_sub` 逆、`ε ≤ 1`
が無くても `ofReal` 切詰で OK; 厳密には `1 - ofReal(1-ε) ≤ ofReal ε` を `ENNReal.sub_le_iff_le_add` +
`ofReal_add` で示す)。ℝ≥0∞ の truncated subtraction に注意 (`prob_compl_eq_one_sub` の docstring が明示警告)。

---

## D. N₀ 閾値 template (atom c) — 同 file `N_doubling` (:1193-1249) が完全 template

`AchievabilityDischarge.lean` 同 theorem 内の `N_doubling` 構成 (`obtain ⟨N_doubling, hN_doubling⟩ : ∃ N₀, ∀ n, N₀ ≤ n → …`)
が atom (c) の **そのまま使える 5 行要約 template**:

1. `set N₀ : ℕ := Nat.ceil (Real.log K / g)` — 閾値 = `log(定数)/margin` の ceil (`g = R''−R > 0` / atom c では `g = I−R−3δ`)。
2. `Nat.le_ceil` で `(N₀ : ℝ) ≥ log K / g`、`div_le_iff₀ hg_pos` で `(n:ℝ)·g ≥ log K`。
3. `Real.exp_le_exp.mpr` + `Real.exp_log` で `exp(n·g) ≥ K`。
4. `exp(n·R'') = exp(n·R)·exp(n·g)` (`Real.exp_add`、`ring` で指数分解)。
5. `Nat.ceil_lt_add_one` (`⌈e⌉ < e+1`) + `Nat.le_ceil` で `Nat.ceil` 不等式に cast (`exact_mod_cast`)。

atom (c) の閾値は「`⌈exp(nR)⌉·exp(−n(I−3δ)) ≤ ε`」型 (alias-term decay)。`⌈exp(nR)⌉ ≤ exp(nR)+1 ≤ 2·exp(nR)`
(nR≥0) で `2·exp(nR)·exp(−n(I−3δ)) = 2·exp(−n·g)` (g=I−R−3δ>0、`hslack` 由来)、`≤ ε ⟺ exp(n·g) ≥ 2/ε
⟺ n ≥ log(2/ε)/g`。必要算術 (verbatim、全て in-project 既使用):

| API | file:line | signature verbatim | 結論形 verbatim |
|---|---|---|---|
| `Nat.le_ceil` | `Mathlib/Algebra/Order/Floor/Semiring.lean:178` | `theorem le_ceil (a : R) :` (section `[Semiring R] [LinearOrder R] [FloorSemiring R]` 系の `{a : R}`) | `a ≤ ⌈a⌉₊` |
| `Nat.ceil_lt_add_one` | `…/Floor/Semiring.lean:357` | `theorem ceil_lt_add_one (ha : 0 ≤ a) :` | `(⌈a⌉₊ : R) < a + 1` |
| `Nat.ceil_le` | `Mathlib/Algebra/Order/Floor/Defs.lean:123` | `theorem ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n` | `⌈a⌉₊ ≤ n ↔ a ≤ ↑n` |
| `Real.exp_le_exp` | `Mathlib/Analysis/Complex/Exponential.lean:316` | `theorem exp_le_exp {x y : ℝ} :` | `exp x ≤ exp y ↔ x ≤ y` |
| `Real.exp_lt_exp` | `…/Complex/Exponential.lean:312` | `theorem exp_lt_exp {x y : ℝ} :` | `exp x < exp y ↔ x < y` |
| `Real.exp_add` | Mathlib (`N_doubling:1218` で使用) | `theorem exp_add (x y : ℝ) : exp (x + y) = exp x * exp y` | `exp (x+y) = exp x * exp y` |
| `Real.exp_log` | Mathlib (`N_doubling:1217` で使用) | `theorem exp_log (hx : 0 < x) : exp (log x) = x` | `exp (log x) = x` |
| `Real.exp_neg` | Mathlib | `theorem exp_neg (x : ℝ) : exp (-x) = (exp x)⁻¹` | `exp (-x) = (exp x)⁻¹` |
| `div_le_iff₀` | Mathlib (`N_doubling:1214` で使用) | `theorem div_le_iff₀ (hc : 0 < c) : a / c ≤ b ↔ a ≤ b * c` | `a / c ≤ b ↔ a ≤ b * c` |

**全て `N_doubling` (:1193-1249) で既に同 file 内で使用済 = import / 名前解決の不安ゼロ。atom (c) は
`N_doubling` を `g = I − R − 3δ` / target `ε` に差し替えた構成で、新規 Mathlib 補題 0 件。**

---

## gap 表

| 不在資産 | self-build template (最近接既存補題 file:line) | 概算行数 | blocker 種別 |
|---|---|---|---|
| 2点 pi-marginal `(Measure.pi ν).map(c↦(c m,c m'))=(ν m).prod(ν m')` (loogle Found 0) | **self-build 不要** — `gaussianCodebook_indepFun_codewords` (`AchievabilityDischarge.lean:94`) + `indepFun_iff_map_prod_eq_prod_map_map` (`Independence/Basic.lean:701`) + `gaussianCodebook_codeword_law` ×2 | ~8 行 | plumbing (既存 IndepFun 経由) |
| per-vector channel = noise translate `Measure.pi(awgnChannel·(x i)) = (Measure.pi noise).map(x+·)` | `pi_map_pi` (`Pi.lean:390`) + `gaussianReal_map_const_add` (`Gaussian/Real.lean:292`) + `awgnChannel_apply` (`Basic.lean:81`) | ~12 行 | plumbing |
| n次元 joint identity `∫⁻ x,(channel x)(Aᶜ sec) ∂μX = J Aᶜ` | `lintegral_prod` (`Prod.lean:996`) または `Measure.map_apply` + `Measure.prod_apply` (`Prod.lean:223`) で J=`(μX.prod μZ).map(...)` を change-of-variables 展開 | ~20-25 行 | plumbing (change-of-variables 1 段) |
| Q-marginal collapse `∑_{m'≠m} ∫ Wch(E2 m') = (M−1)·Q A` | C4 chain (2点 pi-marginal) + `lintegral_prod` で section 積分 → Q A、`Finset.sum_const` で `(M−1)·` | ~25-30 行 | plumbing |
| N₀ 閾値 (atom c) | `N_doubling` (`AchievabilityDischarge.lean:1193-1249`) を g/ε 差替 | ~30-40 行 | plumbing (template 流用) |

**genuine gap (= Mathlib に命題が無い) は 0 件**。全て既存 primitive の配線 (plumbing)。2点 pi-marginal の
「Found 0」は名前付き直接補題の不在であって、IndepFun 経由の同値補題 (`indepFun_iff_map_prod_eq_prod_map_map`)
が存在するため wall ではない。

---

## atom (d) = term1 J-marginal collapse — 推奨補題 chain (≤10 行)

```
1. (atom (d) は :773 rw 済) 残 goal: ∫⁻ x, f1 x ∂(Measure.pi (gaussianReal 0 P')) ≤ ofReal ε
2. f1 x = (Measure.pi (awgnChannel·(x i))) {y | (x,y)∉A}
     = (Measure.pi (awgnChannel·(x i))) (Prod.mk x ⁻¹' Aᶜ)      -- section 書換
3. per-vector channel: Measure.pi (awgnChannel·(x i))
     = (Measure.pi (gaussianReal 0 N)).map (fun z i => x i + z i)  -- pi_map_pi + gaussianReal_map_const_add
4. ∫⁻ x, (channel x)(Prod.mk x⁻¹' Aᶜ) ∂μX = J Aᶜ                  -- Measure.prod_apply / lintegral_prod (J の change-of-variables 展開)
   [J = (μX.prod μZ).map (x,z)↦(x,x+z)、map_apply で Aᶜ の preimage に戻す]
5. J Aᶜ = 1 - J A                                                  -- prob_compl_eq_one_sub hA_meas (J prob measure)
6. ≤ 1 - ofReal(1-ε) ≤ ofReal ε                                   -- tsub_le_tsub_left hA_mass + ENNReal.ofReal_sub 算術 (C5)
```

## atom (e) = term2 Q-marginal collapse — 推奨補題 chain (≤10 行)

```
1. goal: ∑ m'∈erase m, ∫⁻ codebook, Wch(codebook)(E2 codebook m') ∂(gaussianCodebook) ≤ ofReal ε
2. 各 summand: integrand は (codebook m, codebook m') の 2 座標のみ依存 (m≠m')
3. 2点 pushforward: (gaussianCodebook).map (c↦(c m, c m'))
     = (Measure.pi (gaussianReal 0 P')).prod (Measure.pi (gaussianReal 0 P'))   -- C4 chain (indepFun_iff_map_prod_eq_prod_map_map + gaussianCodebook_codeword_law ×2)
4. ∫⁻ codebook, … = ∫⁻ (x,x') ∂(prod), (Measure.pi (channel·(x i)))(E2(x',·)) -- lintegral_map (2点 marginal へ)
5. = Q A   [per-vector channel (atom d step3) + lintegral_prod で section 積分 = J/Q 同定; m'≠m で X' ⊥ (X,Z) → Q = X-marginal.prod Y-marginal]
6. 各 summand = Q A → ∑_{m'≠m} = (M−1)·Q A                          -- Finset.sum_const + card_erase
7. (M−1)·Q A ≤ ⌈exp(nR)⌉·exp(−(klDiv_n − 3nδ)) ≤ ofReal ε           -- hA_indep + hM_le + N₀-decay (atom c) + [klDiv_n=n·I は bridge ①、別 agent]
```

**bridge 境界**: atom (e) step 5 までが本ファイル scope (measure-identity collapse)。step 7 後半の
`klDiv_n = n·I` 同定 (exp-decay の中身) は bridge ① (別 agent) 担当。step 7 前半の `⌈exp(nR)⌉·exp(...)` →
`ofReal ε` の N₀-decay 算術は atom (c) = D section の `N_doubling` template で完備。

---

## 撤退ラインとの距離

親 plan `awgn-achievability-walls-discharge-plan.md` の該当 atom 撤退ライン (deep atoms :286-293 /
Phase 4 :247):
> 撤退ライン (達成済): union bound の measure-identity 2 件は `sorry + @residual(plan:…)` で deferred。

**判定: 撤退ラインに触れない (既に retreat 出口に着地済み)。**
- 3 atom は既に honest `sorry + @residual(plan:awgn-achievability-walls-discharge-plan)` 形で type-check
  done 状態 (consumer :540/:777/:793)。本棚卸しは **retreat 出口の中身を埋める plumbing 資産の確認**であり、
  撤退ライン自体の発動可否ではない。
- genuine gap 0 件 (全て既存 primitive の配線) なので、新規の wall / 縮退ラインは不要。
- 仮に term2 step 5 の Q 同定が詰まった場合の degenerate fallback: 該当 atom の body のみ
  `sorry + @residual(plan:awgn-achievability-walls-discharge-plan)` を維持 (現状そのもの)。hypothesis bundling
  は行わない (decoder = `jointTypicalDecoder A` 固定、core は body 側 — 監査確定の modular composition)。

`awgn_random_coding_union_bound` の direct consumers (`scripts/dep_consumers.sh`、term-level 実値): **2 decl / 1 file**
- `AchievabilityDischarge.lean:794` `awgn_avg_error_union_bound`
- `AchievabilityDischarge.lean:1054` `isAwgnTypicalityHypothesis`

本 atom は **theorem body 内の sorry 埋め** であり signature 変更を伴わないため、これら consumer への
ripple は 0 (signature 不変)。

---

## 着手 skeleton (atom 埋めの作業単位、新規 file は作らない)

atom (d)/(e)/(c) は既存 `awgn_random_coding_union_bound` 内の sorry を置換するため、新規 file 不要。
作業は AchievabilityDischarge.lean の以下 3 箇所への直接 fill (consumer 行は signature 不変):

```lean
-- import は既に揃っている (AchievabilityDischarge.lean:1-10):
--   Mathlib.Probability.Distributions.Gaussian.Real  (gaussianReal_map_const_add, _conv_)
--   Mathlib.Probability.Independence.Basic            (indepFun_iff_map_prod_eq_prod_map_map)
--   Mathlib.MeasureTheory.Constructions.Pi            (pi_map_pi, measurePreserving_eval)
-- 追加 import 候補 (現状なければ): Mathlib.MeasureTheory.Measure.Prod (prod_apply, lintegral_prod)

-- (d) :777
  -- chain: f1 → per-vector channel (pi_map_pi + gaussianReal_map_const_add)
  --        → J Aᶜ (Measure.prod_apply / lintegral_prod) → prob_compl_eq_one_sub → ofReal 算術
  sorry  -- → fill (~40 行)

-- (e) :793 (h_term2 body)
  -- chain: 各 summand 2点依存 → indepFun_iff_map_prod_eq_prod_map_map (C4)
  --        → Q A (lintegral_prod) → Finset.sum_const ((M−1)·) → hA_indep + N₀-decay
  sorry  -- → fill (~55 行、step 7 後半 klDiv_n は bridge ① 待ち)

-- (c) :540 (case N₀)
  -- N_doubling (:1193-1249) を g = I − R − 3δ / target ε に差替えた閾値構成
  sorry  -- → fill (~35 行)
```

**作業順**: (c) N₀ → (d) term1 → (e) term2。N₀ が確定すると term2 の N₀-decay が閉じる。term1 は N₀ 非依存
(`J Aᶜ ≤ ε` は全 n で成立) なので独立に埋められる。term2 は bridge ① (`klDiv_n=n·I`) との合流点なので最後。
