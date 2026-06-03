# T2-F Fisher Information + de Bruijn Identity — Mathlib + InformationTheory 在庫調査

> **対象**: `docs/textbook-roadmap.md` §T2-F (Cover-Thomas Ch.17 / EPI 経路の入口、~600-800 行)。
> 着手前の Mathlib + InformationTheory 在庫を構造化テーブルで網羅し、自作要箇所の工数概算を付ける。
> **本ファイルは inventory のみ。実装 / 計画起草は別ファイル**。
>
> **調査日**: 2026-05-19 (subagent 1 ターン)。
>
> **使用ツール**: loogle (`Fisher` / `deBruijn` / `score` / `heat` 等 6 件 +
> Gaussian / convolution / pdf / logDeriv 等 12 件) + `rg` 二次フォロー。

## 一行サマリ

**Fisher information / de Bruijn identity の API は Mathlib に 0 件。Score function は
`logDeriv f := deriv f / f` (`Mathlib/Analysis/Calculus/LogDeriv.lean`) が偶発的に同形で存在**。
Gaussian convolution (`gaussianReal_conv_gaussianReal`)・Lebesgue-PDF (`MeasureTheory.HasPDF` +
`pdf`)・parametric integral differentiation (`hasDerivAt_integral_of_dominated_loc_of_lip` 等)・
real-line IBP (`integral_mul_deriv_eq_deriv_mul_of_integrable`)・差分エントロピー
(`InformationTheory/Shannon/DifferentialEntropy.lean` 1010 行) はすべて既存。

**既存率推定: 60-65%** (primitive 層 90%+ / Fisher info-specific 層 0%)。
**自作必要 6 項目、合計 ~550-820 行** (定義 + score 性質 + 1-parameter 連続性 +
de Bruijn identity 本体 + 適合性整備)。**推奨実装路線**: §H 参照 (短く言えば「**PDF
経由 (`HasPDF` + `gaussianReal_conv_gaussianReal`) で 1-D real 値変数のみ scope、後で
multivariate 拡張**」)。

---

## 主定理の最終形 (T2-F roadmap entry より再掲)

```lean
-- de Bruijn identity (univariate, additive Gaussian noise)
theorem deBruijn_identity
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (hX_hasPDF : HasPDF X P volume) /- 等、Fisher info が定義可能な条件 -/
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (fun ω => X ω + Real.sqrt s * Z ω)))
      ((1/2) * fisherInfo (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      t
```

```text
証明戦略 (pseudo-Lean, ~10 行):
  -- 1. 凸組合せ法則: P.map (X + √t · Z) = (P.map X) ∗ (gaussianReal 0 t)
  --    by IndepFun.map_add_eq_map_conv_map₀' + gaussianReal_const_mul + (X = √t · 標準正規 ⇒ var = t)
  -- 2. AC 化: 上の合成側 measure は volume.withDensity (pdf_X ⋆ₗ gaussianPDF 0 t)
  --    で書ける (convolution PDF identity 自作 — Mathlib 不在)
  -- 3. h(P_t) = -∫ p_t log p_t (既存 differentialEntropy_eq_integral_density)
  -- 4. d/dt p_t = (1/2) ∂²p_t/∂x² (heat eq 自作、convolution 微分 by 部品)
  -- 5. d/dt h(P_t) = -(1/2) ∫ p_t (∂_x log p_t)² dx by IBP
  --                = (1/2) J(P_t)  (definition of J, IBP step 自作)
```

---

## §A. Fisher information 定義 — Mathlib 直接の有無確認

| 概念 | Mathlib API | file:line | 状態 | T2-F での扱い |
|---|---|---|---|---|
| **Fisher information `J(X)`** (univariate) | — | — | ❌ **不在** | **自作必須**。`J(X) := ∫ (logDeriv pdf_X x)² · pdf_X x dx` 形 (textbook 同形) |
| **Fisher information matrix** (multivariate) | — | — | ❌ 不在 | T2-F scope-out (T2-D EPI 経路は 1-D で十分) |
| **Fisher info via score function** | — | — | ❌ 不在 | §B の `logDeriv` で score 部品はある |
| **regular family / Cramér-Rao bound** | — | — | ❌ 不在 | T2-F scope-out |

**loogle 検証**: `loogle "Fisher"` → `unknown identifier 'Fisher'`。
`rg -in "fisher" Mathlib/` → 一件もヒット無し。**Mathlib に Fisher info の概念は完全に存在しない**。

---

## §B. Score function `∇ log p` — primitive 候補

**結論**: Mathlib に "score function" という命名概念はないが、**`logDeriv` が定義として完全に同形**。
1-D 版は `Real.deriv_log` チェーン経由で簡単に展開できる。

| 補題名 | file:line | signature | 状態 | T2-F での扱い |
|---|---|---|---|---|
| **`logDeriv`** (一般版) | `Mathlib/Analysis/Calculus/LogDeriv.lean:34` | `def logDeriv (f : 𝕜 → 𝕜') : 𝕜 → 𝕜' := deriv f / f`  *(`{𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']`)* | ✅ 既存 | **score function そのもの**。`logDeriv pdf_X x = pdf_X'(x) / pdf_X(x)` |
| `logDeriv_apply` | `LogDeriv.lean:37` | `theorem logDeriv_apply (f : 𝕜 → 𝕜') (x : 𝕜) : logDeriv f x = deriv f x / f x := rfl` | ✅ | unfold 用 |
| `Real.deriv_log_comp_eq_logDeriv` | `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:134-136` | `lemma Real.deriv_log_comp_eq_logDeriv {f : ℝ → ℝ} {x : ℝ} (h₁ : DifferentiableAt ℝ f x) (h₂ : f x ≠ 0) : deriv (log ∘ f) x = logDeriv f x` | ✅ | **`deriv (log p) = logDeriv p`** — `f > 0` の点で。Fisher info の被積分関数を `(logDeriv p)²` で書ける |
| `Real.deriv_log` | `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:65-68` | `theorem deriv_log (x : ℝ) : deriv log x = x⁻¹` | ✅ | unfold 補助 |
| `Real.hasDerivAt_log` | `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:52-53` | `theorem hasDerivAt_log {x : ℝ} (hx : x ≠ 0) : HasDerivAt log x⁻¹ x` | ✅ | unfold 補助 |
| `HasDerivAt.log` | `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean:112-115` | `theorem HasDerivAt.log {f : ℝ → ℝ} {x f' : ℝ} (hf : HasDerivAt f f' x) (hx : f x ≠ 0) : HasDerivAt (fun y => log (f y)) (f' / f x) x` | ✅ | **composition rule for log of differentiable density** |

**type-class 補助** (これら全て `Real` で trivial、`[NontriviallyNormedField]` は `Real.denselyNormedField` 経由で自動充足):
`{𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']`

**設計上の含意**: Fisher info の定義時に **`logDeriv` を使うべき** (Mathlib-shape-driven 原則:
`Real.deriv_log_comp_eq_logDeriv` の結論形 `deriv (log ∘ f) = logDeriv f` を直接使うため)。

---

## §C. de Bruijn identity 周辺 — 直接 / Gaussian convolution / heat 方程式

### C-1. de Bruijn identity 直接

| 補題名 | file:line | signature | 状態 | T2-F での扱い |
|---|---|---|---|---|
| **`deBruijn_identity` 系** | — | — | ❌ **不在** | **本 T2-F の主定理として自作**。証明骨格は §H 路線 A 参照 |

**loogle 検証**: `loogle "deBruijn"` → `unknown identifier 'deBruijn'`。
`rg -in "bruijn"` のヒットは全て **de Bruijn index** (meta 系) のみ。

### C-2. Gaussian convolution `X + sqrt(t) Z` の measure 形

| 補題名 | file:line | signature (verbatim) | 状態 | T2-F での扱い |
|---|---|---|---|---|
| **`MeasureTheory.Measure.conv`** (additive) | `Mathlib/MeasureTheory/Group/Convolution.lean:35-36, 42` (def + notation) | `noncomputable def conv (μ ν : Measure M) : Measure M := Measure.map (fun x : M × M => x.1 + x.2) (μ.prod ν)` *(`{M : Type*} [AddMonoid M] [MeasurableSpace M]`)*. notation: `scoped[MeasureTheory] infixr:80 " ∗ " => MeasureTheory.Measure.conv` | ✅ 既存 | `(P.map X) ∗ (P.map (√t · Z))` の measure 形 |
| **`gaussianReal_conv_gaussianReal`** | `Mathlib/Probability/Distributions/Gaussian/Real.lean:613-620` | `lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} : (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | ✅ 既存 | **Gaussian 同士の convolution が Gaussian になる**。`X = X` (固定) ∗ `√t Z ∼ 𝒩(0, t)` の処理に直接使える |
| **`gaussianReal_add_gaussianReal_of_indepFun`** | `Mathlib/Probability/Distributions/Gaussian/Real.lean:624-632` | `lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) : P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | ✅ 既存 | Gaussian iid の場合に Gaussian になる路線。一般の `X` には適用不可、§F 参照 |
| **`IndepFun.map_add_eq_map_conv_map₀'`** (`@[to_additive]` 経由) | `Mathlib/Probability/Independence/Basic.lean:1078-1085` (mul 版 / additive 版が自動生成) | `theorem IndepFun.map_mul_eq_map_mconv_map₀' {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] {f g : Ω → M} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) (hfg : f ⟂ᵢ[μ] g) : μ.map (f * g) = (μ.map f) ∗ₘ (μ.map g)` (additive 版: `M : AddMonoid`, `* → +`, `∗ₘ → ∗`) | ✅ 既存 (`@[to_additive]`) | **独立変数 add の law が convolution measure になる**。`P.map (X + √t · Z) = (P.map X) ∗ (P.map (√t · Z))` が直接出る |
| `Measure.conv_assoc` | `Mathlib/MeasureTheory/Group/Convolution.lean:147-157` | `theorem conv_assoc {M : Type*} [AddCommMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M] (μ ν ρ : Measure M) [SFinite ν] [SFinite ρ] : (μ ∗ ν) ∗ ρ = μ ∗ (ν ∗ ρ)` (`@[to_additive]` from `mconv_assoc`) | ✅ | t をさらに分割するときに必要 (e.g., 半群性) |
| `Measure.conv_absolutelyContinuous` | `Mathlib/MeasureTheory/Group/Convolution.lean` (`loogle` ヒット) | `theorem conv_absolutelyContinuous : ...` (詳細未読、loogle のみ確認) | ⚠️ 部分既存 | **重要**: 一般の `μ ∗ ν` が ν ≪ vol で AC か。詳細確認要 (自作 PDF chain 用) |

### C-3. PDF-level convolution (`pdf (X+Y) = pdf X ⋆ₗ pdf Y`)

| 補題名 | file:line | signature (verbatim) | 状態 | T2-F での扱い |
|---|---|---|---|---|
| **`ProbabilityTheory.IndepFun.pdf_add_eq_lconvolution_pdf'`** (`@[to_additive]` from `pdf_mul_eq_mlconvolution_pdf'`) | `Mathlib/Probability/Density.lean:350-354` (mul 版 / 自動生成 add 版) | `theorem IndepFun.pdf_mul_eq_mlconvolution_pdf' {Ω G : Type*} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [Group G] {mG : MeasurableSpace G} [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure G} [IsMulLeftInvariant μ] {X Y : Ω → G} [SigmaFinite μ] [HasPDF X ℙ μ] [HasPDF Y ℙ μ] (σX : SigmaFinite (ℙ.map X)) (σY : SigmaFinite (ℙ.map Y)) (hXY : IndepFun X Y ℙ) : pdf (X * Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₘₗ[μ] pdf Y ℙ μ` (add 版: `[AddGroup G] [IsAddLeftInvariant μ]`, `⋆ₘₗ → ⋆ₗ`) | ✅ 既存 | **PDF レベルでの convolution 等式**。`ℝ` で `volume` が `IsAddLeftInvariant` 自動 |
| `IndepFun.add_hasPDF'` (`@[to_additive]`) | `Mathlib/Probability/Density.lean:333-342` (mul 版) | 上と類似、`HasPDF (X + Y) ℙ μ` を出す | ✅ | sum の HasPDF を obtain |
| **`MeasureTheory.lconvolution`** (additive 形 def) | `Mathlib/Analysis/LConvolution.lean:50` (mul 版) + `@[to_additive]` 自動展開 | `noncomputable def mlconvolution (f g : G → ℝ≥0∞) (μ : Measure G) : G → ℝ≥0∞ := fun x => ∫⁻ y, (f y) * (g (y⁻¹ * x)) ∂μ`  (add 版: `(f g : G → ℝ≥0∞) (μ : Measure G) : G → ℝ≥0∞ := fun x => ∫⁻ y, (f y) * (g (-y + x)) ∂μ`) *(`{G : Type*} {mG : MeasurableSpace G} [Add G] [Neg G]`)* notation: `⋆ₗ[μ]` | ✅ 既存 | **pdf の convolution 形**。pdf_{X+sqrt(t) Z} = pdf_X ⋆ₗ pdf_{sqrt(t) Z} |
| `Mathlib.MeasureTheory.convolution` (Bochner-valued; `f ⋆[L,μ] g`) | `Mathlib/Analysis/Convolution.lean:401` (`noncomputable def convolution [Sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F) (μ : Measure G) : G → F`) | def 行確認済 | ✅ | `ℝ`-値 density (`Real.exp` 形) の場合の convolution。`ℝ≥0∞`-値の `lconvolution` と並走 |
| `convolution_assoc` | `Mathlib/Analysis/Convolution.lean:880` | `theorem convolution_assoc (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z)) {x₀ : G} ...` (詳細省略) | ✅ | t をさらに分割時 |
| `integral_convolution` | `Mathlib/Analysis/Convolution.lean:843` | `theorem integral_convolution [MeasurableAdd₂ G] [MeasurableNeg G] [NormedSpace ℝ E] ...` (詳細省略) | ✅ | `∫ f ⋆ g = (∫f) * (∫g)` 系。Fisher info 計算ではほとんど不要だが正規化に使える |
| **`Real.hasPDF_iff`** | `Mathlib/Probability/Density.lean` (loogle 出力 `Mathlib.Probability.Density`) | `theorem Real.hasPDF_iff ...` (詳細未読) | ✅ | `ℝ`-値変数の HasPDF 簡易判定 |

### C-4. parametric integral differentiation — `d/dt ∫ f(t, x) dx = ∫ ∂_t f(t, x) dx`

| 補題名 | file:line | signature (verbatim) | 状態 | T2-F での扱い |
|---|---|---|---|---|
| **`hasDerivAt_integral_of_dominated_loc_of_lip`** | `Mathlib/Analysis/Calculus/ParametricIntegral.lean:263-269` | `theorem hasDerivAt_integral_of_dominated_loc_of_lip {α : Type*} [MeasurableSpace α] {μ : Measure α} {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] {F : 𝕜 → α → E} {x₀ : 𝕜} {bound : α → ℝ} {s : Set 𝕜} {F' : α → E} (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ) (hF'_meas : AEStronglyMeasurable F' μ) (h_lipsch : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) s) (bound_integrable : Integrable (bound : α → ℝ) μ) (h_diff : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' a) x₀) : Integrable F' μ ∧ HasDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀` | ✅ 既存 | **de Bruijn の `d/dt`-step 主役**。`F (t, x) := pdf_t x · log pdf_t x` 形に適用 |
| **`hasDerivAt_integral_of_dominated_loc_of_deriv_le`** | `Mathlib/Analysis/Calculus/ParametricIntegral.lean:289-294` | `theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] {F : 𝕜 → α → E} {x₀ : 𝕜} {bound : α → ℝ} {s : Set 𝕜} (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ) {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ) (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ) (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) : Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀` | ✅ 既存 | **bound 経由の方がよく fit する** (Lipschitz より derivative bound の方が確認しやすい) |
| `hasFDerivAt_integral_of_dominated_of_fderiv_le` | `Mathlib/Analysis/Calculus/ParametricIntegral.lean:211-217` | multivariate 版 (Fréchet) | ✅ | T2-F univariate scope ではほぼ不要 |

**前提条件 (事故が起きやすいので明記)**:
- `[RCLike 𝕜]` (`𝕜 := ℝ` で自動充足、`Real.instRCLike`)
- `[NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]` (`E := ℝ` で自動)
- **`F x₀` の Integrable**: `differentialEntropy` の被積分関数 `pdf log pdf` の可積分性 →
  `InformationTheory/Shannon/DifferentialEntropy.lean:81 integrable_density_log_density_of_gaussian` 拡張要
- **bound の Integrable**: t-derivative の上界が µ-Integrable。**ここが一番危険な前提**
  (Fisher info 自体が有限という前提に化ける可能性、§G で討議)
- **AEStronglyMeasurable**: `pdf` は `Measurable (pdf X ℙ μ)` (Mathlib に既存) から自動

### C-5. 真空: heat semigroup / PDE

| 概念 | Mathlib API | 状態 | T2-F での扱い |
|---|---|---|---|
| heat semigroup | — | ❌ 不在 (`loogle "heat"` → `unknown identifier`) | T2-F scope-out。Gaussian convolution `gaussianReal_conv_gaussianReal` で十分代替可能 |
| heat equation / Laplacian on PDF | — | ❌ 不在 | T2-F scope-out。直接 `pdf` を `Real.sqrt t * Z` の convolution として書き、`d/dt` を `hasDerivAt_integral_of_dominated_loc_of_deriv_le` 経由で取る |
| Schwartz functions IBP | `Mathlib/Analysis/Distribution/SchwartzSpace/Deriv.lean:263` | ✅ 既存 | T2-F は Schwartz space まで上がる必要なし、`integral_mul_deriv_eq_deriv_mul_of_integrable` で十分 |

---

## §D. PDF + Radon-Nikodym 経路

| 補題名 | file:line | signature (verbatim) | 状態 | T2-F での扱い |
|---|---|---|---|---|
| **`MeasureTheory.HasPDF`** | `Mathlib/Probability/Density.lean:71-75` | `class HasPDF {Ω E : Type*} [MeasurableSpace E] {m : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) : Prop where protected aemeasurable' : AEMeasurable X ℙ ; protected haveLebesgueDecomposition' : (map X ℙ).HaveLebesgueDecomposition μ ; protected absolutelyContinuous' : map X ℙ ≪ μ` | ✅ 既存 | **`X` が pdf を持つ前提**。Fisher info を定義するための前提条件 |
| **`MeasureTheory.pdf`** | `Mathlib/Probability/Density.lean:123-125` | `def pdf {Ω E : Type*} [MeasurableSpace E] {_ : MeasurableSpace Ω} (X : Ω → E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) : E → ℝ≥0∞ := (map X ℙ).rnDeriv μ` | ✅ 既存 | **pdf の定義そのもの**。Fisher info の被積分関数の主役 |
| `pdf_def` | `Mathlib/Probability/Density.lean:127-128` | `theorem pdf_def {_ : MeasurableSpace Ω} {ℙ : Measure Ω} {μ : Measure E} {X : Ω → E} : pdf X ℙ μ = (map X ℙ).rnDeriv μ := rfl` | ✅ | unfold 補助 |
| `MeasureTheory.map_eq_withDensity_pdf` | `Mathlib/Probability/Density.lean` (loogle ヒット) | `theorem map_eq_withDensity_pdf ...` (詳細未読) | ✅ | `ℙ.map X = volume.withDensity (pdf X ℙ volume)` 形 |
| `MeasureTheory.pdf.integral_pdf_smul` | `Mathlib/Probability/Density.lean` (loogle) | `theorem pdf.integral_pdf_smul ...` (Law of unconscious statistician) | ✅ | `∫ g(X) dℙ = ∫ g(x) · pdf x dx` |
| `MeasureTheory.HasPDF.absolutelyContinuous` | `Mathlib/Probability/Density.lean:96` | `theorem HasPDF.absolutelyContinuous [HasPDF X ℙ μ] : map X ℙ ≪ μ` | ✅ | `HasPDF ⇒ AC` を自動引き出す |
| `Real.hasPDF_iff_of_aemeasurable` | `Mathlib/Probability/Density.lean` (loogle ヒット) | `theorem Real.hasPDF_iff_of_aemeasurable ...` (詳細未読) | ✅ | `ℝ`-値変数の AC ↔ HasPDF 簡易判定 |
| `Measure.rnDeriv_pos`, `Measure.rnDeriv_lt_top` | `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` | (既知、InformationTheory DifferentialEntropy.lean:825 で使用) | ✅ | `pdf > 0` a.e., `pdf < ∞` a.e. — Fisher info の `1/pdf` 安全性 |
| `Measure.rnDeriv_mul_rnDeriv` | (既知、DifferentialEntropy.lean:818 で使用) | (cf. InformationTheory 内で実証済) | ✅ | チェイン RN |

**type-class 前提条件 (verbatim)**:
- `[MeasurableSpace E]` — `E := ℝ` で `Real.measurableSpace` 自動
- `(μ : Measure E := by volume_tac)` — 省略時 `volume`、`ℝ` で `MeasureTheory.volume` 自動
- `{m : MeasurableSpace Ω}` (HasPDF) — ambient
- **`HasPDF` instance を `X + √t · Z` (合成側) に伝搬する手段** — Mathlib `IndepFun.add_hasPDF'` (Density.lean:333 add 版) が存在、`SigmaFinite (ℙ.map X)` + `SigmaFinite (ℙ.map (√t · Z))` の前提あり

---

## §E. Differential entropy 微分可能性 (InformationTheory 既存) — DifferentialEntropy.lean 再利用候補

`InformationTheory/Shannon/DifferentialEntropy.lean` (1010 行) から T2-F 再利用候補のみ抜粋。

| 補題名 | file:line | signature (要点) | 状態 | T2-F での扱い |
|---|---|---|---|---|
| **`differentialEntropy`** | `InformationTheory/Shannon/DifferentialEntropy.lean:42-43` | `noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | ✅ InformationTheory 既存 | **`h(P_t)` の定義そのもの**。T2-F で再利用 |
| **`differentialEntropy_eq_integral_density`** | `InformationTheory/Shannon/DifferentialEntropy.lean:60-72` | `theorem differentialEntropy_eq_integral_density {f : ℝ → ℝ} (hf : Measurable f) (hf_nn : ∀ x, 0 ≤ f x) (μ : Measure ℝ) (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) : differentialEntropy μ = -∫ x, f x * Real.log (f x) ∂volume` | ✅ InformationTheory 既存 | **`h(P_t) = -∫ p_t log p_t dx`** 形書き換え。これが de Bruijn の `d/dt` を取る対象 |
| `differentialEntropy_eq_integral_withDensity` | `InformationTheory/Shannon/DifferentialEntropy.lean:47-55` | `theorem ... {f : ℝ → ℝ≥0∞} (hf : Measurable f) : differentialEntropy (volume.withDensity f) = ∫ x, Real.negMulLog (f x).toReal ∂volume` | ✅ | `ℝ≥0∞`-density 形 |
| `differentialEntropy_dirac` | `InformationTheory/Shannon/DifferentialEntropy.lean:149-150` | `theorem differentialEntropy_dirac (m : ℝ) : differentialEntropy (Measure.dirac m) = 0` | ✅ | `t = 0` の boundary 処理 |
| `differentialEntropy_map_add_const`, `..._mul_const`, `..._affine` | `InformationTheory/Shannon/DifferentialEntropy.lean:165, 195, 344` | translation / scaling | ✅ | `Real.sqrt t · Z` の scaling 処理 |
| `integrable_density_log_density_of_gaussian` | `InformationTheory/Shannon/DifferentialEntropy.lean:81-83` | `theorem ... (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Integrable (fun x => gaussianPDFReal m v x * Real.log (gaussianPDFReal m v x)) volume` | ✅ | **Gaussian PDF の log-product 可積分性**。Fisher info の有限性 (Gaussian の場合) の核 |
| `log_gaussianPDFReal_eq` | `InformationTheory/Shannon/DifferentialEntropy.lean:391-403` | `theorem ... (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : Real.log (gaussianPDFReal m v x) = -(1/2) * Real.log (2 * Real.pi * v) - (x - m)^2 / (2 * v)` | ✅ | Gaussian の log 展開 (score 計算で `deriv` を取ると `-(x - m)/v` が出る、Gaussian の Fisher info `J = 1/v` の根拠) |
| `differentialEntropy_gaussianReal` | `InformationTheory/Shannon/DifferentialEntropy.lean:406-409` | `theorem ... (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | ✅ | **`h(𝒩) = (1/2) log(2πev)`** — de Bruijn を `X = 0` で sanity check |
| `klDiv_gaussianReal_gaussianReal_eq` | `InformationTheory/Shannon/DifferentialEntropy.lean:791-795` | `theorem ... (m₁ m₂ : ℝ) {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) : (klDiv (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)).toReal = (1/2) * (Real.log ((v₂ : ℝ) / v₁) + (v₁ : ℝ) / v₂ + (m₁ - m₂)^2 / v₂ - 1)` | ✅ | de Bruijn の検算 (`d/dt` を 2 重で取ると Fisher info) |
| **`deriv_t (differentialEntropy (P.map (X + √t · Z))) = (1/2) · J(P_t)`** | — | — | ❌ **T2-F 主定理** | **自作必須 — 本 seed のゴール** |

---

## §F. Gaussian distribution / convolution (Mathlib + InformationTheory 既存)

| 補題名 | file:line | signature (verbatim) | 状態 | T2-F での扱い |
|---|---|---|---|---|
| **`ProbabilityTheory.gaussianReal`** | `Mathlib/Probability/Distributions/Gaussian/Real.lean:200-201` | `noncomputable def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ := if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)` | ✅ 既存 | `Z ∼ 𝒩(0, 1)` の law |
| **`ProbabilityTheory.gaussianPDFReal`** | `Mathlib/Probability/Distributions/Gaussian/Real.lean:48-49` | `noncomputable def gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ := (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))` | ✅ 既存 | Gaussian PDF (real-valued) |
| **`ProbabilityTheory.gaussianPDF`** | `Mathlib/Probability/Distributions/Gaussian/Real.lean:157` | `noncomputable def gaussianPDF (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gaussianPDFReal μ v x)` | ✅ | `ℝ≥0∞` 版 |
| **`rnDeriv_gaussianReal`** | `Mathlib/Probability/Distributions/Gaussian/Real.lean:240-247` | `lemma rnDeriv_gaussianReal (μ : ℝ) (v : ℝ≥0) : ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v` | ✅ | `(gaussianReal μ v).rnDeriv volume = gaussianPDF μ v` |
| `gaussianReal_const_mul`, `gaussianReal_map_const_mul` | `Mathlib/Probability/Distributions/Gaussian/Real.lean` (loogle ヒット) | (verbatim 未読、loogle に存在確認のみ) | ✅ | `√t · Z` の law を計算 |
| `IsGaussian` | `Mathlib/Probability/Distributions/Gaussian/Basic.lean:45-47` | `class IsGaussian {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] {mE : MeasurableSpace E} (μ : Measure E) : Prop where map_eq_gaussianReal (L : StrongDual ℝ E) : μ.map L = gaussianReal (μ[L]) (Var[L; μ]).toNNReal` | ✅ 既存 | 多変量 Gaussian 抽象。T2-F univariate では不要だが、後の T2-D EPI 拡張で使う可能性 |
| `isGaussian_gaussianReal` (instance) | `Mathlib/Probability/Distributions/Gaussian/Basic.lean:58` | `instance isGaussian_gaussianReal (m : ℝ) (v : ℝ≥0) : IsGaussian (gaussianReal m v)` | ✅ | univariate Gaussian は IsGaussian |
| **InformationTheory 既存 Gaussian-related** | — | — | — | **T2-F 着手前は `DifferentialEntropy.lean` 内のみ**。`Gaussian.lean` という独立ファイルは無い |

---

## §G. 自作要 (Mathlib + InformationTheory ともに無いもの) — 自作工数概算付き

優先度順、各項目に **±50% の行数見積** を付ける。

### G-1. `fisherInfo : Measure ℝ → ℝ≥0∞` 定義 — **~30-60 行**

```lean
noncomputable def fisherInfo (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x)^2)
    * μ.rnDeriv volume x ∂volume
```

**設計判断**:
- **`logDeriv` を直接使う** (§B `Real.deriv_log_comp_eq_logDeriv` の結論形に合わせる)
- **`ℝ≥0∞`-valued** — 「Fisher info が無限大」のケース (irregular family) を捌くため。`fisherInfoReal` 派生 `.toReal` 形は補助で出す
- **`pdf` を直接呼ばず `μ.rnDeriv volume` で書く** — `HasPDF X ℙ volume` を要求するか `μ : Measure ℝ` 引数 mid-level かは設計判断。後者の方が `differentialEntropy : Measure ℝ → ℝ` と整合 (cf. InformationTheory 既存 §E)
- **工数**: 30〜60 行。定義 + nonneg + 基本書き換え (`fisherInfo_eq_integral_logDeriv_sq`)

**落とし穴**: `(logDeriv f x)^2` を `ℝ≥0∞` に持ち上げる際、`f x = 0` の点で `deriv f x / 0` が `Real` で `0` になり、二乗も `0` で OK だが、**実は Lebesgue density は a.e. > 0 ではない**。台外で `0` になる扱いは `negMulLog` の `0 log 0 = 0` 慣行と整合させる必要あり。

### G-2. `fisherInfo (gaussianReal m v) = 1 / v` — **~80-120 行**

```lean
theorem fisherInfo_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfo (gaussianReal m v) = ENNReal.ofReal (1 / v)
```

**経路**:
1. `rnDeriv_gaussianReal` で密度を `gaussianPDFReal` に書き換え
2. `logDeriv gaussianPDFReal m v x = -(x - m) / v` を `log_gaussianPDFReal_eq` + `deriv` で出す
3. `∫ ((x - m)/v)² · gaussianPDFReal m v x dx = v / v² = 1/v` (variance による)

**工数**: 80〜120 行。**Gaussian の Variance 計算 (`variance_id_gaussianReal`) と直結するので
InformationTheory `DifferentialEntropy.lean` の Gaussian 補助インフラを大量に流用できる**。

### G-3. `IndepFun.map_add_eq_volume_withDensity_lconvolution` (PDF-level convolution bridge) — **~40-80 行**

```lean
-- 既存 IndepFun.pdf_add_eq_lconvolution_pdf' は pdf を pdf の lconvolution に書くだけ。
-- 我々が欲しいのは `ℙ.map (X + Y) = volume.withDensity (pdf X ⋆ₗ pdf Y)` 形 (measure 形)。
-- 後者は MeasureTheory.map_eq_withDensity_pdf + Density.lean:350 の合成で出る (はず)。
theorem map_add_eq_volume_withDensity_lconvolution
    {X Y : Ω → ℝ} [HasPDF X ℙ volume] [HasPDF Y ℙ volume]
    (hXY : IndepFun X Y ℙ) :
    ℙ.map (X + Y) = volume.withDensity (pdf X ℙ volume ⋆ₗ pdf Y ℙ volume)
```

**経路**: `map_eq_withDensity_pdf` (X+Y の HasPDF instance を `IndepFun.add_hasPDF'` から取る) +
`pdf_add_eq_lconvolution_pdf'`。

**工数**: 40〜80 行 (bridge lemma 自体は 10〜20 行で書けるが、HasPDF instance の伝搬 plumbing が要)。
**SigmaFinite (ℙ.map X)** 前提が要 — `IsFiniteMeasure ℙ` (我々は `[IsProbabilityMeasure P]`) から
`Measure.IsFiniteMeasure.toSigmaFinite` で自動。

### G-4. Score function 性質: 期待値 0、convolution 形 — **~60-120 行**

```lean
-- Cover-Thomas 17.7 (i): E[score] = 0 (条件: pdf differentiable + smooth tail)
theorem integral_logDeriv_pdf_eq_zero
    (X : Ω → ℝ) [HasPDF X ℙ volume] (h_diff : Differentiable ℝ (fun x => (pdf X ℙ volume x).toReal))
    (h_tail : Tendsto (fun x => (pdf X ℙ volume x).toReal) atBot (𝓝 0))
    (h_tail' : Tendsto (fun x => (pdf X ℙ volume x).toReal) atTop (𝓝 0)) :
    ∫ x, logDeriv (fun y => (pdf X ℙ volume y).toReal) x * (pdf X ℙ volume x).toReal ∂volume = 0
```

**経路**: `∫ p' = ∫ d/dx p = p(∞) - p(-∞) = 0` — 直接 `integral_deriv_mul_eq_sub` の左半分形で。
あるいは `MeasureTheory.integral_deriv_mul_eq_sub` (IntegralEqImproper.lean:1296) を `u := 1, v := pdf`
の特殊化で。

**工数**: 60〜120 行。**最大の障壁は smooth tail 前提の定式化** (`Tendsto atBot/atTop`)。
Gaussian は手で示せるが、一般 X は条件付きで残す形になる。

### G-5. de Bruijn identity 本体 — **~250-400 行**

```lean
theorem deBruijn_identity ... : HasDerivAt (fun s => h(P_s)) ((1/2) · J(P_t)) t
```

**証明 5 ステップ**:
1. **convolution 表現**: `P.map (X + √s · Z) = (P.map X) ∗ gaussianReal 0 s` (~30-60 行)
   - `gaussianReal_const_mul` で `√s · Z ∼ 𝒩(0, s)`
   - `IndepFun.map_add_eq_map_conv_map₀'` (additive 版)
   - 適切な scale: `√s · Z` の場合 `X` と `√s Z` の独立性は `X ⟂ Z` から従う (composition-with-measurable)
2. **PDF representation**: `(P.map (X+√s · Z)).rnDeriv volume = pdf X ⋆ₗ gaussianPDF 0 s` (~50-80 行)
   - §G-3 の bridge + `Mathlib.Probability.Density:350`
3. **`d/ds`-step**: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` を `F (s, x) := -p_s(x) log p_s(x)` で
   適用 (~80-120 行)
   - dominated 条件: `s ∈ (t/2, 2t)` で `|F'_s| ≤ bound(x)`、bound は Gaussian tail から integrable
   - これは `t > 0` 前提を要する (Gaussian の正則性が崩れる `t = 0` を避ける)
4. **`d/ds p_s` の同定**: `(d/ds) (p_X ⋆ₗ gaussianPDF 0 s) x = (1/2) ∂²/∂x² (p_X ⋆ₗ gaussianPDF 0 s) x` (~50-80 行)
   - heat equation。convolution 微分の繰返し: `∂_x (f ⋆ g) = f ⋆ g' = f' ⋆ g`
   - `∂_s gaussianPDF 0 s x = (1/2) ∂²_x gaussianPDF 0 s x` を手動 verification (Gaussian 直接計算)
5. **IBP**: `-∫ p_s · (d/ds log p_s) dx = -∫ p_s · (∂_s p_s / p_s) dx = ... = (1/2) ∫ p_s · (∂_x log p_s)² dx`
   (~40-60 行)
   - `integral_mul_deriv_eq_deriv_mul_of_integrable` (IntegralEqImproper.lean:1318)

**工数**: 250〜400 行。**ステップ 4 が最大の難所** — Gaussian heat equation の `(1/2) ∂²_x = ∂_s` を
Lean で形式化するのは記号操作量が大きい。

**代替案 (より短い)**: 凸組合せ法則を一旦 `gaussianReal m₁ v₁ ∗ gaussianReal m₂ v₂ =
gaussianReal (m₁+m₂) (v₁+v₂)` (Mathlib §C-2) に **Gaussian の場合のみ閉じる** ことで、`s ↦ s+ε`
の semigroup 構造を直接使う路線。これだと `d/ds` を半群微分にできるが、一般の `X` で
`X + √s Z` の表現の dynamics が非自明になる ⇒ 結局 Step 4 を再現する形になる。

### G-6. 整合: `differentialEntropy` ↔ `(P.map (X+√t Z))` 表現の橋渡し — **~80-160 行**

```lean
-- HasPDF を仮定すると differentialEntropy (P.map Y) = -∫ pdf(y) log pdf(y) dy 形
theorem differentialEntropy_map_eq_integral_pdf_log_pdf
    (Y : Ω → ℝ) [HasPDF Y ℙ volume] :
    differentialEntropy (ℙ.map Y) = -∫ x, (pdf Y ℙ volume x).toReal * Real.log (pdf Y ℙ volume x).toReal ∂volume
```

**経路**: `pdf Y ℙ volume = (ℙ.map Y).rnDeriv volume` (`pdf_def`) +
`differentialEntropy_eq_integral_density` (InformationTheory §E) — ただし `f := (pdf Y ℙ volume).toReal`
は `ℝ`-値、Measurable / nonneg / `ℝ≥0∞.ofReal ∘ .toReal = id` ae の plumbing で 30〜50 行。

**工数**: 80〜160 行 (基本 bridge ~30 + AC 系の補助 ~50 + Integrable 系の補強 ~30-80)。

### 自作要 合計

| 項目 | 行数見積 |
|---|---|
| G-1 `fisherInfo` 定義 + 基本性質 | 30-60 |
| G-2 `fisherInfo_gaussianReal = 1/v` | 80-120 |
| G-3 `IndepFun.map_add_eq_volume_withDensity_lconvolution` | 40-80 |
| G-4 score function 期待値 0 | 60-120 |
| G-5 de Bruijn identity 本体 | 250-400 |
| G-6 differentialEntropy ↔ pdf 橋渡し | 80-160 |
| 計 | **540-940** |

T2-F roadmap entry の規模目安 "**~600-800 行**" と整合 (中央値 ~740 vs ~700)。

---

## §H. 設計判断 — 既存率 (%), 推奨実装路線

### 既存率推定 (primitive layer / Fisher info-specific layer 分解)

| 層 | Mathlib 既存率 | 内訳 |
|---|---|---|
| **Differentiation infrastructure** | **95%** | `ParametricIntegral`, `LogDeriv`, `Real.deriv_log`, `integral_mul_deriv_eq_deriv_mul`, parametric derivatives |
| **Probability density** | **90%** | `HasPDF`, `pdf`, `Real.hasPDF_iff`, RN チェイン、`map_eq_withDensity_pdf` |
| **Gaussian / convolution** | **95%** | `gaussianReal`, `gaussianPDF`, `rnDeriv_gaussianReal`, `gaussianReal_conv_gaussianReal`, `Measure.conv`, `lconvolution`, `IndepFun.map_add_eq_map_conv_map₀'`, `IndepFun.pdf_add_eq_lconvolution_pdf'` |
| **Differential entropy (InformationTheory)** | **80%** | `differentialEntropy`, `..._eq_integral_density`, `..._gaussianReal`, `integrable_density_log_density_of_gaussian`, `klDiv_gaussianReal_gaussianReal_eq` |
| **Fisher info 概念** | **0%** | Mathlib 不在、InformationTheory 不在 |
| **de Bruijn identity** | **0%** | Mathlib 不在、InformationTheory 不在 |
| **score function 期待値 0** | **0%** | Mathlib に独立 lemma 無し (IBP + tail から手動構成) |
| **総合** (重み付き mean) | **~60-65%** | primitive 高、Fisher info-specific 0 |

### 推奨実装路線 — **路線 A: PDF 経由 + 1-D scope**

**結論**: **`HasPDF X ℙ volume` を仮定して 1-D 実数値変数のみを scope に、`fisherInfo : Measure ℝ → ℝ≥0∞`
を `logDeriv` ベースで定義する。multivariate / general process は本 seed scope-out**。

**根拠**:

1. **§B の `logDeriv` が score function と定義同形** — Mathlib-shape-driven 原則に従い、
   `logDeriv` の結論形 `deriv f / f` を流用するのが最短経路 (50-100 行の bridge を回避)
2. **§C-2/C-3 で convolution measure ↔ convolution PDF の対応が完備** — `IndepFun.pdf_add_eq_lconvolution_pdf'`
   と `gaussianReal_conv_gaussianReal` で `X + √t · Z` の law と pdf が両方計算可能
3. **§C-4 の `hasDerivAt_integral_of_dominated_loc_of_deriv_le` が de Bruijn の中核**ステップを完全
   サポート — bound の dominated 条件が天敵だが、Gaussian tail で押さえられる
4. **§E の InformationTheory 既存 `differentialEntropy` が再利用可能** — 主定理の左辺は
   `differentialEntropy (P.map (X + √t Z))` の形で書ける
5. **multivariate は EPI (T2-D) で必要になるが、univariate de Bruijn だけで EPI の証明骨格は出る**
   (Cover-Thomas 17.7 の証明は univariate convolution を取りスカラー化する形)

**路線 B (score function 直接定義) との対比**:
- 路線 B: `def score (X : Ω → ℝ) (ℙ : Measure Ω) (x : ℝ) : ℝ := logDeriv (fun y => (pdf X ℙ volume y).toReal) x`
- 路線 A の `fisherInfo` に内蔵された `logDeriv` で十分。score を独立に名付ける必要は無い (path A の方が抽象層が少なく済む)

**路線 C (heat semigroup 経由) との対比**:
- heat semigroup は Mathlib に 0 (§C-5)。自作すると +200-300 行。**完全に scope-out**

### 撤退ライン (T2-F に新規提案)

T2-F roadmap entry には撤退ライン定義無し。**本 inventory で以下を提案** (T2-F plan 起草時に moonshot-plan-template.md に組み入れる):

| 段階 | 撤退条件 | 縮退案 |
|---|---|---|
| **L1**: de Bruijn Step 4 (heat eq for Gaussian convolution) が 1 週間で書けない | Step 4 を `axiom` 化 / `sorry` 残留 | Step 4 を仮定 axiom 化した形で残る Step 5 IBP のみ formalize。proof-log で「Step 4 が Mathlib gap」と記録 |
| **L2**: §G-4 score function 期待値 0 の smooth tail 条件が一般 X で書けない | tail 条件付き形に hypothesis pass-through | Cover-Thomas 17.7 conditions を `IsRegularFamily` predicate に括り出し、Gaussian の場合のみ instance を出す形に縮退 |
| **L3**: §G-5 全体が 1 月で 600 行に収まらない | Gaussian-only 形に縮退 | `X ∼ 𝒩(m, v)` 限定の de Bruijn (`d/dt h(𝒩(m, v+t)) = (1/2) · 1/(v+t)`) のみ formalize。一般 X は scope-out で plan v2 に切り出し |

---

## 主要前提条件ボックス

de Bruijn identity の式を組み立てる際、**型クラス前提が事故源**になるものを列挙:

- **`hasDerivAt_integral_of_dominated_loc_of_deriv_le`** (§C-4):
  - `[RCLike 𝕜]` — `𝕜 := ℝ` で `Real.instRCLike` 自動充足
  - `[NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]` — `E := ℝ` で全部自動
  - **`Integrable (F x₀) μ`** — `F (t, x) := -p_t(x) log p_t(x)` の `t = t₀` での可積分性。
    Gaussian convolution の場合 `InformationTheory/Shannon/DifferentialEntropy.lean:81`
    `integrable_density_log_density_of_gaussian` を拡張で出すしか無い
  - **`bound_integrable : Integrable bound μ`** — bound として何を取るかが本 seed 最大の設計判断。
    Gaussian の場合 `c · |x| · exp(-x²/(4 v_max))` 形で押さえる
  - **`AEStronglyMeasurable F'`** — `F'` は `-(1 + log p_t(x)) · ∂_t p_t(x)` 形、measurability は
    convolution の measurability から `fun_prop` で出るはず
- **`MeasureTheory.HasPDF`** (§D): `[MeasurableSpace E] (μ : Measure E := by volume_tac)` — `E := ℝ`,
  `μ := volume` で全自動。**Notably no `[StandardBorelSpace]`** (cf. Fano §B では `condDistrib` で
  StandardBorel が要だった、Fisher info ではこの罠は無い)
- **`IndepFun.pdf_add_eq_lconvolution_pdf'`** (§C-3):
  - `[Group G]` (add 版: `[AddGroup G]`) — `G := ℝ` で自動
  - `[MeasurableMul₂ G]` (add 版: `[MeasurableAdd₂ G]`) — `ℝ` で `Real.measurableMul₂` /
    `Real.measurableAdd₂` instance 自動
  - **`[SigmaFinite μ]` (= volume)** — ℝ の volume は SigmaFinite、自動
  - **`[HasPDF X ℙ μ] [HasPDF Y ℙ μ]`** — `X` と `√t · Z` 両方が HasPDF。後者は Gaussian なので OK、
    前者は主定理仮定として要求する
  - `[IsAddLeftInvariant μ]` (add 版) — volume は OK
  - `(σX : SigmaFinite (ℙ.map X))` — `IsProbabilityMeasure ℙ` から自動
- **`integral_mul_deriv_eq_deriv_mul_of_integrable`** (`Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1318`):
  - `[NormedRing A] [NormedAlgebra ℝ A]` — `A := ℝ` で自動
  - `[CompleteSpace A]` — `A := ℝ` で自動
  - **`(hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)`** — `u` の differentiability を `v` の台で要求。
    `v := pdf` の台が全 `ℝ` (Gaussian convolution は support 全体) なので `u := log p_t` の
    differentiability を全点で要求 ⇒ `p_t > 0` a.e. が必要

---

## 着手 skeleton (`InformationTheory/Shannon/FisherInfo.lean`)

```lean
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Density
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.LConvolution
import InformationTheory.Shannon.DifferentialEntropy

/-!
# Fisher information + de Bruijn identity (T2-F)

Cover-Thomas Ch.17 の Fisher info 定義 + de Bruijn identity。InformationTheory T2-F
ムーンショット ([`docs/shannon/fisher-info-mathlib-inventory.md`])。

## 主シグネチャ

* `fisherInfo` — Phase A 定義 (logDeriv ベース、ℝ≥0∞ 値)
* `fisherInfo_eq_integral_score_sq` — score² 積分形書き換え
* `fisherInfo_gaussianReal` — Gaussian の Fisher info = 1/v
* `integral_logDeriv_pdf_eq_zero` — score の期待値 0 (smooth tail 条件付き)
* `deBruijn_identity` — Phase D 主定理 `(d/dt) h(P_{X+√t Z}) = (1/2) J(P_{X+√t Z})`
-/

namespace InformationTheory.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Phase A — `fisherInfo` 定義 -/

/-- **Fisher information** of a measure `μ` on `ℝ` with density `p := μ.rnDeriv volume`.
Defined as `J(μ) := ∫ (logDeriv p x)² · p x dx` where `logDeriv f := deriv f / f`. -/
noncomputable def fisherInfo (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x) ^ 2)
    * μ.rnDeriv volume x ∂volume

theorem fisherInfo_nonneg (μ : Measure ℝ) : 0 ≤ fisherInfo μ := by sorry

theorem fisherInfo_eq_integral_logDeriv_sq (μ : Measure ℝ) [SFinite μ]
    (hμ : μ ≪ volume) :
    fisherInfo μ
      = ∫⁻ x, ENNReal.ofReal ((logDeriv (fun y => (μ.rnDeriv volume y).toReal) x) ^ 2)
          * μ.rnDeriv volume x ∂volume := by sorry

/-! ## Phase B — Gaussian Fisher info -/

theorem fisherInfo_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfo (gaussianReal m v) = ENNReal.ofReal (1 / v) := by sorry

/-! ## Phase C — score function 性質 -/

theorem integral_logDeriv_pdf_eq_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (X : Ω → ℝ) [HasPDF X ℙ volume]
    (h_diff : Differentiable ℝ (fun x => (pdf X ℙ volume x).toReal))
    (h_pos : ∀ x, 0 < (pdf X ℙ volume x).toReal)
    (h_tail_bot : Tendsto (fun x => (pdf X ℙ volume x).toReal) atBot (𝓝 0))
    (h_tail_top : Tendsto (fun x => (pdf X ℙ volume x).toReal) atTop (𝓝 0)) :
    ∫ x, logDeriv (fun y => (pdf X ℙ volume y).toReal) x * (pdf X ℙ volume x).toReal ∂volume
      = 0 := by sorry

/-! ## Phase D — de Bruijn identity (主定理) -/

theorem deBruijn_identity
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z ℙ)
    [HasPDF X ℙ volume]
    (hZ_law : ℙ.map Z = gaussianReal 0 1)
    -- regularity hypotheses (pass-through, dischargable for Gaussian X)
    (h_reg : RegularDeBruijnHyp X Z ℙ /- placeholder predicate -/)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => differentialEntropy (ℙ.map (fun ω => X ω + Real.sqrt s * Z ω)))
      ((1/2) * (fisherInfo (ℙ.map (fun ω => X ω + Real.sqrt t * Z ω))).toReal)
      t := by sorry

end InformationTheory.Shannon
```

---

## 撤退ラインへの距離 (再評価)

T2-F roadmap entry に撤退ライン定義は無いが、本 inventory で 3 段階 (L1/L2/L3、§H 撤退ライン項) を
提案。**現時点の見積では撤退ライン発動は no** — primitive layer の既存率が 90%+ で、自作必須は
Fisher info-specific 層 (≤ 940 行、roadmap entry の上限 800 行+ 17% 程度) に閉じている。

**最大の発見リスク**: §G-5 Step 4 (Gaussian heat equation `(1/2) ∂²_x p_t = ∂_t p_t`) の formalization
コストが想定の 80 行を超えて 200-300 行になる可能性。**Mathlib に Gaussian PDF の `x`-second derivative
の明示 lemma が存在しないため、ゼロから組み立てる必要がある**。

---

## 参照

- 親 roadmap: [`docs/textbook-roadmap.md`](../textbook-roadmap.md) §T2-F
- 前提 inventory: `InformationTheory/Shannon/DifferentialEntropy.lean` (1010 行、InformationTheory 既存)
- 関連 future seed: T2-D EPI (本 T2-F の主消費者)、T2-E Brunn-Minkowski
- Mathlib primary deps: `Mathlib/Analysis/Calculus/LogDeriv.lean`,
  `Mathlib/Analysis/Calculus/ParametricIntegral.lean`,
  `Mathlib/Probability/Density.lean`,
  `Mathlib/Probability/Distributions/Gaussian/Real.lean`,
  `Mathlib/MeasureTheory/Group/Convolution.lean`,
  `Mathlib/Analysis/LConvolution.lean`,
  `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
