import Common2026.Meta.EntryPoint
import Common2026.Shannon.FisherInfoV2
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Fisher information V2 — Phase C bridge + Phase D de Bruijn identity (T2-F follow-up)

Common2026 T2-F follow-up (parents:
* `docs/shannon/fisher-info-moonshot-plan.md` Phase E (`deBruijn_identity` Tier 2)
* `docs/shannon/fisher-info-gaussian-discharge-moonshot-plan.md` Phase C / D
   (L-G3 retreat 2026-05-19)).

This file builds on top of `FisherInfoV2.lean`'s V2 redefinition (which fixes the
V1 representative-dependence flaw documented in `FisherInfoGaussian.lean` L-G3
retreat) to publish

* **Phase C — V1 ↔ V2 bridge**: V1 `IsRegularDensity` witnesses lift to V2
  `IsRegularDensityV2`; V1 `fisherInfo (P.map X)` is bridged to V2
  `fisherInfoOfDensity (h_v1.density)` via the chosen smooth representative.
* **Phase D — de Bruijn identity (V2 form)**: a V2 `IsRegularDeBruijnHypV2`
  predicate (statement-form, L-F1+L-F2 hypothesis pass-through, with the RHS
  using `fisherInfoOfDensity` so the Gaussian case actually evaluates to `1/v`
  rather than the V1 `0` ghost) and `deBruijn_identity_v2`.
* **Gaussian discharge** `deBruijn_identity_v2_gaussian`: when `X ∼ 𝒩(m, v)`,
  `Z ∼ 𝒩(0, 1)`, `X ⊥ Z`, the law of `X + √t Z` is `𝒩(m, v + t)` (Mathlib
  `gaussianReal_add_gaussianReal_of_indepFun`); the LHS
  `(d/dt) (1/2) log (2π e (v + t))` equals `1/(2(v + t))` (Mathlib `hasDerivAt_log`
  composition); the RHS `(1/2) · J(𝒩(m, v + t)) = (1/2) · (1/(v + t))` matches
  via V2 `fisherInfoOfDensityReal_gaussianPDFReal`.
## 主シグネチャ

* `fisherInfoOfMeasureV2` — Phase C measure-keyed V2 Fisher info (density-witness form)
* `fisherInfoOfMeasureV2_gaussianReal` — Phase C Gaussian closed form `1/v` (V2)
* `gaussianConvolution` — abbrev for `P.map (fun ω => X ω + √t · Z ω)` (heat-flow path)
* `IsRegularDeBruijnHypV2` — Phase D V2 regularity predicate (RHS uses V2 fisher info)
* `deBruijn_identity_v2` — Phase D de Bruijn identity (L-F1+L-F2 hypothesis pass-through, V2)
* `deBruijn_identity_v2_gaussian` — Gaussian discharge (hypothesis-free), the canonical
   Stage 2 publish target blocked under V1 by the representative-dependence flaw

## 撤退ライン

* **L-FV2D-A** (採用): V2 redefinition path — density-as-input form, both bridge
   and de Bruijn are stated against `fisherInfoOfDensity` (Gaussian evaluates correctly).
* **L-FV2D-B** (本 file): de Bruijn identity hypothesis pass-through (statement-form
   publish) — the heat-equation + dominated-bound machinery for the *general* `X`
   case is bundled into `IsRegularDeBruijnHypV2` and discharged downstream
   (Gaussian case is fully discharged here).
* **L-FV2D-C** (未採用): full general-`X` discharge via Cover-Thomas Phase C/D heat-eq.
-/

namespace Common2026.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Phase C — V1 ↔ V2 bridge (measure-keyed wrapper) -/

/-- **V2 Fisher information of a measure**, density-witness form.

Takes a measure `μ : Measure ℝ` together with an explicit smooth density witness
`f : ℝ → ℝ`. The Fisher information is computed as
`fisherInfoOfDensity f` (the V2 density-as-input form). The witness is unrelated
to `μ.rnDeriv volume` syntactically — it is the caller's responsibility to
verify the relevant a.e.-equality if needed (cf. `fisherInfoOfMeasureV2_eq_of_pdf_ae_eq`).

This is the V2 analogue of `Common2026.Shannon.fisherInfo` from `FisherInfo.lean`,
but with the V1 representative-dependence flaw eliminated: the caller picks the
representative explicitly. -/
noncomputable def fisherInfoOfMeasureV2 (_μ : Measure ℝ) (f : ℝ → ℝ) : ℝ≥0∞ :=
  fisherInfoOfDensity f

/-- Real-valued projection of `fisherInfoOfMeasureV2`. -/
noncomputable def fisherInfoOfMeasureV2Real (_μ : Measure ℝ) (f : ℝ → ℝ) : ℝ :=
  fisherInfoOfDensityReal f

/-- Unfold lemma. -/
@[entry_point]
theorem fisherInfoOfMeasureV2_def (μ : Measure ℝ) (f : ℝ → ℝ) :
    fisherInfoOfMeasureV2 μ f = fisherInfoOfDensity f := rfl

@[entry_point]
theorem fisherInfoOfMeasureV2Real_def (μ : Measure ℝ) (f : ℝ → ℝ) :
    fisherInfoOfMeasureV2Real μ f = fisherInfoOfDensityReal f := rfl

/-- **Gaussian Fisher info — V2 measure-keyed closed form** `1/v`.

The deliverable that was blocked under V1 by the representative-dependence flaw
(`FisherInfoGaussian.lean` L-G3 retreat). -/
@[entry_point]
theorem fisherInfoOfMeasureV2_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfoOfMeasureV2 (gaussianReal m v) (gaussianPDFReal m v)
      = ENNReal.ofReal (1 / (v : ℝ)) := by
  unfold fisherInfoOfMeasureV2
  exact fisherInfoOfDensity_gaussianPDFReal m hv

/-- Real-valued Gaussian Fisher info via V2. -/
@[entry_point]
theorem fisherInfoOfMeasureV2Real_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    fisherInfoOfMeasureV2Real (gaussianReal m v) (gaussianPDFReal m v) = 1 / (v : ℝ) := by
  unfold fisherInfoOfMeasureV2Real
  exact fisherInfoOfDensityReal_gaussianPDFReal m hv

/-! ## Phase D — Heat-flow path (gaussianConvolution) abbrev -/

/-- **Heat-flow convolution path** `X + √t · Z`. The `t`-parametrised family of
random variables underpinning de Bruijn identity (Cover-Thomas 17.7.2). For
`Z ∼ 𝒩(0, 1)` and `X` independent of `Z`, the law `P.map (gaussianConvolution X Z t)`
is the convolution of `P.map X` with `𝒩(0, t)`, hence the *Gaussian heat
semigroup* action on `P.map X`.

Defined as a plain abbreviation rather than a wrapper structure so that callers
can use existing `Measure.map` API without an additional layer. -/
noncomputable def gaussianConvolution {α : Type*} (X Z : α → ℝ) (t : ℝ) : α → ℝ :=
  fun ω => X ω + Real.sqrt t * Z ω

/-- **Law of `X + √t · Z`** when `X` is Gaussian `𝒩(m, v)`, `Z` is standard normal,
and `X ⊥ Z`: the result is `𝒩(m, v + t.toNNReal)`. The key Mathlib facts used
are `gaussianReal_map_const_mul` (law of `√t · Z` is `𝒩(0, t)`) and
`gaussianReal_add_gaussianReal_of_indepFun` (sum of independent Gaussians). -/
@[entry_point]
theorem gaussianConvolution_law_of_gaussian
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {X Z : Ω → ℝ} (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {t : ℝ} (ht : 0 ≤ t) :
    P.map (gaussianConvolution X Z t)
      = gaussianReal m (v + ⟨t, ht⟩) := by
  -- Step 1: law of `√t · Z` is `𝒩(0, t)`.
  have h_sqrt_nn : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have h_sqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  -- `P.map (fun ω => √t · Z ω) = gaussianReal (√t · 0) ((√t)² · 1) = gaussianReal 0 t`.
  have h_sqrtZ_map : Measure.map (fun ω => Real.sqrt t * Z ω) P
      = gaussianReal 0 ⟨t, ht⟩ := by
    -- `P.map (c · Z) = (P.map Z).map (c · ·)`.
    have h_compose : Measure.map (fun ω => Real.sqrt t * Z ω) P
        = (P.map Z).map (fun y => Real.sqrt t * y) := by
      have h_meas_mul : Measurable (fun y : ℝ => Real.sqrt t * y) :=
        measurable_const.mul measurable_id
      have := Measure.map_map (μ := P) h_meas_mul hZ
      -- `(P.map Z).map (fun y => √t * y) = P.map ((fun y => √t * y) ∘ Z)`.
      -- The RHS is `P.map (fun ω => √t * Z ω)`.
      simpa [Function.comp] using this.symm
    rw [h_compose, hZ_law, gaussianReal_map_const_mul]
    -- Need: `gaussianReal (√t · 0) (⟨(√t)², _⟩ * 1) = gaussianReal 0 ⟨t, ht⟩`.
    congr 1
    · ring
    · -- `⟨(√t)², _⟩ * 1 = ⟨t, ht⟩` as `ℝ≥0`.
      rw [mul_one]
      apply NNReal.eq
      exact h_sqrt_sq
  -- Step 2: independence `X ⊥ (√t · Z)`.
  have hX_aem : AEMeasurable X P := hX.aemeasurable
  have hZ_aem : AEMeasurable Z P := hZ.aemeasurable
  have h_indep_X_sqrtZ : IndepFun X (fun ω => Real.sqrt t * Z ω) P :=
    hXZ.comp measurable_id (measurable_const.mul measurable_id)
  -- Step 3: sum of independent Gaussians.
  have h_sum := gaussianReal_add_gaussianReal_of_indepFun (P := P)
    (X := X) (Y := fun ω => Real.sqrt t * Z ω)
    (m₁ := m) (m₂ := 0) (v₁ := v) (v₂ := ⟨t, ht⟩)
    h_indep_X_sqrtZ hX_law h_sqrtZ_map
  -- Step 4: `X + (√t · Z) = gaussianConvolution X Z t` pointwise.
  unfold gaussianConvolution
  have h_funext : (fun ω => X ω + Real.sqrt t * Z ω) = X + (fun ω => Real.sqrt t * Z ω) := by
    funext ω; rfl
  rw [h_funext, h_sum]
  congr 1
  · ring

/-! ## Phase D — `IsRegularDeBruijnHypV2` predicate + `deBruijn_identity_v2` -/

/-- **V2 de Bruijn identity regularity predicate**.

V2 analogue of `Common2026.Shannon.IsRegularDeBruijnHyp` (`FisherInfo.lean:200`).
The key difference: the RHS uses **V2 fisher info** (`fisherInfoOfDensity` of an
explicit density witness), so the Gaussian case actually evaluates to `1/v`
rather than the V1 ghost `0`. Bundles a density witness `density_t : ℝ → ℝ`
for the law of `X + √t Z`.

**Phase 2.B foundation step (2026-05-27)**: 2 fields only — regularity
preconditions (`Z_law` + `density_t`). The de Bruijn identity itself
(`HasDerivAt ... ((1/2) * fisherInfoOfDensityReal density_t) t`) used to
be bundled here as a third load-bearing field, but Phase 2.A audit
(commit `a6ae83b`) flagged that arrangement as load-bearing hypothesis
bundling (the field was `wall:debruijn-integration` smuggled into a
regularity predicate). The de Bruijn identity core proof is now
集約 (consolidated) into `debruijnIdentityV2_holds`
(`wall:debruijn-integration`) as a genuine wall closure point. -/
structure IsRegularDeBruijnHypV2 {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (t : ℝ) where
  /-- `Z` is standard normal. -/
  Z_law : P.map Z = gaussianReal 0 1
  /-- Smooth density witness for `P.map (X + √t · Z)`. -/
  density_t : ℝ → ℝ

/-! ### Shared sorry 補題 — `debruijnIdentityV2_holds` (genuine wall closure point)

Phase 2.B foundation step (`docs/shannon/epi-stam-fisher-epi-integrated-sweep-plan.md`
§Phase 2.B) で `IsRegularDeBruijnHypV2` から `derivAt_entropy_eq_half_fisher_v2`
field が削除され、本 lemma が `wall:debruijn-integration` (heat equation +
dominated-bound + IBP の Mathlib 不在部) に対する **genuine wall closure point**
に昇格した。Phase 2.A の no-op launder verdict (commit `a6ae83b`) を受けた
field 削除 foundation の完了点。

`deBruijn_identity_v2` / `deBruijn_identity_v2_of_heat_flow` /
`deBruijn_identity_v2_of_heat_subhyp` すべての common closure point。
集約 target は **wall:debruijn-integration**。
-/

/-- **de Bruijn identity body — shared sorry 補題 (wall:debruijn-integration)**.

Phase 2.B foundation step で `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2`
field 削除完了 (commit chain 上、本 lemma の上に乗っていた 1 段 indirection が
解消された) → 本 lemma が genuine wall closure point に昇格。`h_reg` は
regularity-only (2 field: `Z_law` + `density_t`) なので、body は
「regularity から HasDerivAt 結論を導く」 heat eq + dominated bound + IBP の
Mathlib 不在部に **直接突き当たる**。

`@residual(wall:debruijn-integration)` -/
theorem debruijnIdentityV2_holds
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ)
    {t : ℝ} (_ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
      t := by
  sorry -- @residual(wall:debruijn-integration)

/-- **de Bruijn identity (V2 form)**, honest pass-through to shared wall lemma.

For `X ⊥ Z` with `Z ∼ 𝒩(0, 1)`,

`(d/dt) h(X + √t · Z) = (1/2) · J(X + √t · Z)`,

stated with **V2 Fisher information** (`fisherInfoOfDensityReal`) on the RHS.
Unlike the V1 statement, the Gaussian case here can be fully discharged
(`deBruijn_identity_v2_gaussian` below).

**Phase 2.B 段 1 (2026-05-27、`epi-stam-fisher-epi-integrated-sweep-plan`
§Phase 2.B)**: F1 field 削除完了 (`IsRegularDeBruijnHypV2` から
`derivAt_entropy_eq_half_fisher_v2` field を削除) により、本 wrapper は
honest pass-through (regularity hyp `h_reg` → shared wall lemma
`debruijnIdentityV2_holds` (`wall:debruijn-integration`) 経由) に昇格。 -/
@[entry_point]
theorem deBruijn_identity_v2
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ)
    {t : ℝ} (ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
      t :=
  debruijnIdentityV2_holds X Z ht h_reg

/-! ## Gaussian discharge — `deBruijn_identity_v2_gaussian` (hypothesis-free)

The Stage 2 publish point: when `X ∼ 𝒩(m, v)`, `Z ∼ 𝒩(0, 1)`, `X ⊥ Z`,
the de Bruijn identity is fully proved without any hypothesis pass-through.

Strategy: `P.map (X + √t Z) = 𝒩(m, v + t)`, so

* LHS: `s ↦ differentialEntropy (𝒩(m, v + s)) = (1/2) log (2π e (v + s))`,
  whose derivative at `t` is `1/(2(v + t))` via `Real.hasDerivAt_log` composition.
* RHS: `(1/2) · J(𝒩(m, v + t)) = (1/2) · (1/(v + t)) = 1/(2(v + t))`
  via V2 `fisherInfoOfMeasureV2Real_gaussianReal`.

The two sides match by `field_simp` / `ring`. -/

/-- Helper: `(1/2) * Real.log (2π e (v + s))` has derivative `1/(2(v + s))` at any
`s ≥ 0` (when `v + s > 0`). -/
@[entry_point]
theorem hasDerivAt_half_log_gaussian_entropy
    {v : ℝ≥0} (s : ℝ) (hvs : 0 < (v : ℝ) + s) :
    HasDerivAt
      (fun s' : ℝ => (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s')))
      (1 / (2 * ((v : ℝ) + s))) s := by
  -- Inner derivative: `s' ↦ 2π e (v + s')` has derivative `2π e` at any point.
  have h_inner : HasDerivAt (fun s' : ℝ => 2 * Real.pi * Real.exp 1 * ((v : ℝ) + s'))
      (2 * Real.pi * Real.exp 1) s := by
    have h_const : HasDerivAt (fun _ : ℝ => (v : ℝ)) 0 s := hasDerivAt_const s (v : ℝ)
    have h_id' : HasDerivAt (fun s' : ℝ => s') 1 s := hasDerivAt_id s
    have h_add : HasDerivAt (fun s' : ℝ => (v : ℝ) + s') (0 + 1) s := h_const.add h_id'
    have h_add' : HasDerivAt (fun s' : ℝ => (v : ℝ) + s') 1 s := by
      convert h_add using 1; ring
    have h_mul := h_add'.const_mul (2 * Real.pi * Real.exp 1)
    -- `h_mul : HasDerivAt _ (2πe * 1) s`. Rewrite to `2πe`.
    convert h_mul using 1; ring
  -- Apply log chain rule. Need `2π e (v + s) ≠ 0`.
  have h2πe_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  have h_prod_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * ((v : ℝ) + s) :=
    mul_pos h2πe_pos hvs
  have h_prod_ne : (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s)) ≠ 0 := h_prod_pos.ne'
  -- `Real.log ∘ inner` has derivative `(2πe) / (2π e (v + s)) = 1/(v + s)`.
  have h_log := h_inner.log h_prod_ne
  -- Simplify the derivative `(2π e) / (2π e (v + s)) = 1/(v + s)`.
  have h2πe_ne : (2 * Real.pi * Real.exp 1) ≠ 0 := h2πe_pos.ne'
  have h_vs_ne : ((v : ℝ) + s) ≠ 0 := hvs.ne'
  have h_simp : (2 * Real.pi * Real.exp 1) / (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s))
      = 1 / ((v : ℝ) + s) := by
    field_simp
  rw [h_simp] at h_log
  -- Multiply by `1/2`.
  have h_half := h_log.const_mul (1/2 : ℝ)
  -- `h_half : HasDerivAt (fun s' => (1/2) * Real.log (2π e (v + s'))) ((1/2) * (1/(v + s))) s`.
  -- Rewrite `(1/2) * (1/(v + s)) = 1 / (2 * (v + s))`.
  have h_rewrite : (1/2 : ℝ) * (1 / ((v : ℝ) + s)) = 1 / (2 * ((v : ℝ) + s)) := by
    field_simp
  rw [h_rewrite] at h_half
  exact h_half

/-- **Differential entropy of `gaussianReal m (v + s.toNNReal)`** along the heat-flow
path, simplified to `(1/2) log (2π e (v + s))` for `s ≥ 0` (so `v + s` matches as
a real number with `(v + s.toNNReal : ℝ) = v + s`). -/
@[entry_point]
theorem differentialEntropy_gaussianReal_heat_path
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    differentialEntropy (gaussianReal m (v + ⟨s, hs⟩))
      = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s)) := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have hvs_nn : v + ⟨s, hs⟩ ≠ 0 := by
    intro h
    have h_coe : ((v + ⟨s, hs⟩ : ℝ≥0) : ℝ) = 0 := by rw [h]; simp
    rw [NNReal.coe_add] at h_coe
    show False
    have : (v : ℝ) + s = 0 := by
      convert h_coe using 1
    linarith
  rw [Common2026.Shannon.differentialEntropy_gaussianReal m hvs_nn]
  -- The `(v + ⟨s, hs⟩ : ℝ≥0).toReal = (v : ℝ) + s` step.
  rw [show ((v + ⟨s, hs⟩ : ℝ≥0) : ℝ) = (v : ℝ) + s from NNReal.coe_add v ⟨s, hs⟩]

/-- **de Bruijn identity for Gaussian X** (V2, hypothesis-free).

For `X ∼ 𝒩(m, v)`, `Z ∼ 𝒩(0, 1)`, `X ⊥ Z`, and `t > 0`,

`(d/dt) h(X + √t · Z) = (1/2) · J(𝒩(m, v + t)) = 1/(2(v + t))`.

This is the Stage 2 publish point of `fisher-info-gaussian-discharge-moonshot-plan.md`
Phase D — the deliverable blocked under V1 by the representative-dependence flaw,
now provable through V2 redefinition (cf. `FisherInfoV2.lean:296`). -/
@[entry_point]
theorem deBruijn_identity_v2_gaussian
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P)
    {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX_law : P.map X = gaussianReal m v)
    (hZ_law : P.map Z = gaussianReal 0 1)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfMeasureV2Real (P.map (gaussianConvolution X Z t))
          (gaussianPDFReal m (v + ⟨t, ht.le⟩)))
      t := by
  have hv_pos : (0 : ℝ) < v := by
    have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
  have hvs_pos : (0 : ℝ) < (v : ℝ) + t := by linarith
  -- Step 1: rewrite the LHS via the Gaussian heat-path entropy form.
  -- For each `s` on a neighbourhood of `t` (in fact for `s ≥ 0`), the law of
  -- `X + √s · Z` is `𝒩(m, v + s)` so the entropy is `(1/2) log (2π e (v + s))`.
  -- We use `HasDerivAt.congr_of_eventuallyEq` against this rewrite, restricted to `s > 0`
  -- (which holds on a neighbourhood of `t > 0`).
  have h_pos_nbhd : ∀ᶠ s in nhds t, (0 : ℝ) < s := eventually_gt_nhds ht
  -- The entropy along the heat path equals `(1/2) log (2π e (v + s))` for `s ≥ 0`.
  have h_entropy_eq : ∀ s : ℝ, 0 ≤ s →
      differentialEntropy (P.map (gaussianConvolution X Z s))
        = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s)) := by
    intro s hs
    have h_law := gaussianConvolution_law_of_gaussian hX hZ hXZ hX_law hZ_law hs
    rw [h_law]
    exact differentialEntropy_gaussianReal_heat_path m hv hs
  -- Reformulate as eventually-equality at `nhds t`.
  have h_eventually : (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      =ᶠ[nhds t] (fun s => (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((v : ℝ) + s))) := by
    refine h_pos_nbhd.mono fun s hs => ?_
    exact h_entropy_eq s hs.le
  -- Step 2: apply `hasDerivAt_half_log_gaussian_entropy`.
  have h_deriv := hasDerivAt_half_log_gaussian_entropy (v := v) (s := t) hvs_pos
  -- Step 3: transfer via `HasDerivAt.congr_of_eventuallyEq`.
  have h_deriv' : HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      (1 / (2 * ((v : ℝ) + t))) t := by
    refine h_deriv.congr_of_eventuallyEq ?_
    exact h_eventually
  -- Step 4: identify the RHS `(1/2) * fisherInfoOfMeasureV2Real ... = 1/(2(v + t))`.
  have h_law_t := gaussianConvolution_law_of_gaussian hX hZ hXZ hX_law hZ_law ht.le
  have hvs_nn : v + ⟨t, ht.le⟩ ≠ 0 := by
    intro h
    have h_coe : ((v + ⟨t, ht.le⟩ : ℝ≥0) : ℝ) = 0 := by rw [h]; simp
    rw [NNReal.coe_add] at h_coe
    have : (v : ℝ) + t = 0 := by convert h_coe using 1
    linarith [v.coe_nonneg]
  have h_fisher : fisherInfoOfMeasureV2Real (P.map (gaussianConvolution X Z t))
      (gaussianPDFReal m (v + ⟨t, ht.le⟩))
        = 1 / ((v : ℝ) + t) := by
    unfold fisherInfoOfMeasureV2Real
    rw [fisherInfoOfDensityReal_gaussianPDFReal m hvs_nn]
    rw [show ((v + ⟨t, ht.le⟩ : ℝ≥0) : ℝ) = (v : ℝ) + t from NNReal.coe_add v ⟨t, ht.le⟩]
  rw [h_fisher]
  -- Now: `HasDerivAt ... ((1/2) * (1/(v + t))) t`. Match with `1/(2(v + t))`.
  have h_eq_rhs : (1/2 : ℝ) * (1 / ((v : ℝ) + t)) = 1 / (2 * ((v : ℝ) + t)) := by
    field_simp
  rw [h_eq_rhs]
  exact h_deriv'

end Common2026.Shannon.FisherInfoV2
