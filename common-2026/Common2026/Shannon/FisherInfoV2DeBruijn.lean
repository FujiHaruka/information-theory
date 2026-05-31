import Common2026.Meta.EntryPoint
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.EPIConvDensity
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
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)
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
  /-- **X-density witness fields (§5A, `epi-debruijn-pertime-closure-plan` Phase 5)**:
  the `pX` series (4 fields) supplies a Real density witness for `X` itself, which is
  the input required by the Phase 1b density-identification atom
  `pPath_eq_convDensityAdd` (the law of `X + √s·Z` is the convolution of `P.map X`
  with a Gaussian, expressed via `convDensityAdd pX g_σ`). It is also the smooth
  representative to which `density_t` is pinned by `density_t_eq` below.

  All four are **regularity preconditions**, NOT load-bearing: they assert that `X`
  has a Lebesgue density `pX` (nonnegativity + measurability + the external-shape
  equation `P.map X = withDensity (ofReal∘pX)`). They do not bundle the analytic
  core (`HasDerivAt` / heat equation / Fisher); same series as `Z_law` / `density_t_eq`.

  These fields are declared **before** `density_t_eq` so the latter's conv-pin RHS
  can reference `pX` (structure fields cannot forward-reference). -/
  pX : ℝ → ℝ
  /-- Nonnegativity of the X density witness (regularity precondition). -/
  pX_nn : ∀ x, 0 ≤ pX x
  /-- Measurability of the X density witness (regularity precondition). -/
  pX_meas : Measurable pX
  /-- External-shape equation: `X` has Lebesgue density `pX` (regularity
  precondition, same form as `density_t_eq`; not load-bearing). -/
  pX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x))
  /-- **Density-pin field (conv-pin redesign, 2026-05-31, plan §Phase 5-F 案 1)**: the
  density witness `density_t` is pinned to the *smooth* representative
  `convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)` — the convolution of the `X`
  density `pX` with the time-`t` Gaussian heat kernel. This is the genuine density of
  the pushforward `P.map (X + √t · Z)` (Phase 1b `pPath_eq_convDensityAdd`), written as
  an explicit smooth function.

  **Why conv-pin and not rnDeriv-pin**: the previous field pinned `density_t` pointwise
  to `(rnDeriv (P.map (X+√t·Z)) volume).toReal`. `Measure.rnDeriv` is the
  `Classical.choose` representative of the Lebesgue decomposition, generically
  non-differentiable on a co-null set, forcing `logDeriv ((rnDeriv).toReal) = 0` a.e.
  and hence `fisherInfoOfDensity density_t = 0` — the same false-statement defect as
  `density_t := 0` (RHS `(1/2)·fisherInfoOfDensityReal density_t` forced to `0`,
  contradicting the Gaussian derivative `1/(2(v+t)) ≠ 0`). Pinning instead to the
  smooth convolution representative makes `logDeriv` genuine and the statement true.
  The pin is the special case form needed by the Gaussian constructor
  (`convDensityAdd_gaussian_closed_form`) and by `_fisher_match` (now genuine, both
  sides are `fisherInfoOfDensityReal` of the *same* function, closed by `funext`).

  This is a **regularity precondition** (an external-shape equation
  `density_t x = convDensityAdd pX g_t x`), NOT load-bearing: it does not bundle the
  analytic core (`HasDerivAt` / heat equation / IBP). The RHS is an explicit smooth
  function, not a `HasDerivAt`/Fisher claim. Same series as `Z_law` / `pX_law`. The
  `0 < t` is received field-internally (`∀ (ht : 0 < t)`) since the structure does not
  carry positivity of `t`. -/
  density_t_eq : ∀ (ht : 0 < t) (x : ℝ),
    density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x
  /-- **Second-moment regularity precondition** (§Phase 5-G, hpX_mom threading 2026-05-31):
  the X density `pX` has a finite second moment, i.e. `y ↦ y²·pX y` is volume-integrable.
  This is a regularity precondition (NOT load-bearing): it asserts finite variance of `X`,
  required by the §5G-2 domination's route-II Tonelli even-moment envelope
  (`_chain_domination` → `convKernel_envelope_integrable` on `y²·pX`). It does NOT bundle any
  `HasDerivAt` / Fisher analytic core. Same regularity series as `pX_law` / `density_t_eq`. -/
  pX_mom : Integrable (fun y => y ^ 2 * pX y) volume

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

/-- **de Bruijn identity body — shared sorry 補題 (plan:epi-debruijn-pertime-closure)**.

**Conv-pin redesign (2026-05-31, `epi-debruijn-pertime-closure-plan` §Phase 5-F 案 1)**:

1. `IsRegularDeBruijnHypV2` の density-pin field `density_t_eq` を **rnDeriv pin から
   conv pin に差し替えた** (`density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t,ht.le⟩) x`)。
   旧 rnDeriv pin (`density_t x = (rnDeriv (P.map (X+√t·Z)) volume x).toReal`) は
   `Classical.choose` 代表元への pointwise pin で `logDeriv = 0` a.e. → `fisherInfoOfDensity = 0`
   を強制し、RHS を `0` に退化させて命題を FALSE にしていた (`density_t := 0` と同型の
   false-statement defect)。smooth 畳み込み代表元 `convDensityAdd pX g_t` に pin し直すと
   `logDeriv` が genuine になり、RHS が正しい Fisher 値を取って命題は **true statement** になる。
2. wall content (heat eq + IBP on density of `P.map (X + √t Z)`) に semantic 必要な
   regularity hyp `_hX` / `_hZ` / `_hXZ` を underscore-prefixed args として復元 (Phase
   2.B 段 1 で削除されていた forward-looking 負債、plan §0-b 案 (a))。

**再分類根拠 (`wall:debruijn-integration` → `plan:epi-debruijn-pertime-closure`)**:
Wave 1 独立再評価 (inventory §0/§12) で、これは「hard absence」ではなく「big plumbing」と
確定した。Mathlib API は揃っている — 無限区間 IBP (`integral_mul_deriv_eq_deriv_mul_of_integrable`,
`IntegralEqImproper.lean:1318`) は PRESENT、parametric diff
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) 完備、rnDeriv↔withDensity 軸
完備、convolution density (`EPIConvDensity.lean` の `@audit:ok` 資産) 完備。唯一の
Mathlib 不在は Gaussian heat semigroup closed-form だが density-route で迂回可
(self-build 見積 ~250 行、Phase 1+ で closure 予定)。Gaussian case は
`deBruijn_identity_v2_gaussian` で既に genuine。

body は依然 `sorry` (解析核は Phase 1+ の別タスク)。命題は true、tier 2 honest 残課題。

**Phase 5 assembly (2026-05-31)**: import 循環回避のため、6 genuine atom
(`FisherInfoV2DeBruijnPerTime.lean`) を組んだ genuine 版 assembly は別 file
`FisherInfoV2DeBruijnAssembly.debruijnIdentityV2_holds_assembled` (同 signature) にある
(atom file が本 file を import するので、本 file から atom を import できない逆依存)。
本 wall lemma 自身の body は wall sorry のまま残置 (循環回避)。assembly 版は main body が
genuine で、残 gap は 2 named regularity-plumbing lemma (entropy-chain 段 2-7 +
fisher value match) の honest sorry に局所化 (PR-level、plan L-PT-γ/δ)。

Honesty sign-off (conv-pin redesign, 2026-05-31):
(1) **signature true 化**: RHS は `fisherInfoOfDensityReal h_reg.density_t` で、
`density_t_eq` が `density_t` を smooth 代表元 `convDensityAdd pX g_t` に pin する。旧
rnDeriv pin は `logDeriv = 0` a.e. で RHS を `0` に退化させ命題を FALSE にしていたが、
smooth conv 代表元では `logDeriv` が genuine で RHS が正しい Fisher 値を取るため命題は
genuine な de Bruijn identity (true statement)。
(2) **`density_t_eq` は regularity precondition (NOT load-bearing)**: core-
reconstruction test — `density_t_eq` を granted しても `(d/dt)h = (1/2)J` (heat eq +
IBP) は供給されない (pin は「witness = explicit smooth conv 関数」と言うだけで
`HasDerivAt` を渡さない)。RHS は explicit smooth 関数で `HasDerivAt`/Fisher core を
bundle しない。解析核は全て本 `sorry` body 内に残る。
(3) **`wall:` → `plan:` 再分類を確認**: loogle 裏取りで IBP
(`integral_mul_deriv_eq_deriv_mul_of_integrable`) + parametric diff
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) PRESENT、heat semigroup
(`Mehler`/`heatKernel`/`OrnsteinUhlenbeck`) `Found 0`。唯一の不在は density-route で
迂回可 (`convDensityAdd_hasDerivAt` = `@audit:ok` 資産)。docstring は「big not hard」と
主張し「blocked by Mathlib」とは言わない → mathlib_wall_misuse ではない。plan
`epi-debruijn-pertime-closure-plan.md` 実在 (6 Phase)。再分類妥当。

`@residual(plan:epi-debruijn-pertime-closure)` -/
theorem debruijnIdentityV2_holds
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ)
    (_hX : Measurable X) (_hZ : Measurable Z) (_hXZ : IndepFun X Z P)
    {t : ℝ} (_ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
      t := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)

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
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {t : ℝ} (ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
      t :=
  debruijnIdentityV2_holds X Z hX hZ hXZ ht h_reg

/-! ### Shared sorry 補題 — `debruijnIntegrationIdentity_holds` (積分形, wall:debruijn-integration)

Cover-Thomas Lemma 17.7.2 の **積分形** (integration identity along the heat-flow path)。
`debruijnIdentityV2_holds` は per-time の `HasDerivAt` を返すのみで、その deriv を FTC
(`intervalIntegral`) で積分して得られる差分恒等式

    `h(X + √T·Z) − h(X) = ∫_0^T (1/2)·J(X + √t·Z) dt`

は一般 `X` では Mathlib 未整備 (一般 heat-flow path の積分可能性 + FTC の bounded/unbounded
interval 形が無い)。Gaussian 限定なら `bounded_T_ftc_gaussian` (`EPIL3Integration`) が同型を
実演するが、本 lemma は density witness `fPath` を bundle した存在形で一般 `X` の壁に直接
突き当たる。consumer (`EPIStamDischarge.IsDeBruijnIntegrationHyp` の witness 生成) は本 lemma を
普通の lemma call として使う (各 use site で `sorry` を書かない)。

結論 shape は `IsDeBruijnIntegrationHyp X Z P T` の body (`∃ fPath, ∀ h_X h_target, ...
= ∫ t in Set.Ioo 0 T, (1/2)·(fisherInfoOfMeasureV2 ...).toReal ∂volume`) に合わせてある
(CLAUDE.md「Mathlib-shape-driven Definitions」)。`IsDeBruijnIntegrationHyp` は downstream file
で定義されるため (import cycle 回避) ここでは raw 積分形で述べ、consumer 側で predicate に
畳み込む。 -/

/-- **Path regularity bundle for the de Bruijn integration identity**.

Phase 4 structural-closure precondition (`epi-debruijn-integration-phaseD-plan`
follow-up): packages the FTC ingredients needed to integrate the per-time
`debruijnIdentityV2_holds` derivative along the heat-flow path `(0, T)`. All
four fields are **regularity preconditions** (which `X` is admissible / how
regular the heat-flow path is), NOT the de Bruijn analytic core — the core
(heat equation + IBP) stays localized in the per-time wall lemma
`debruijnIdentityV2_holds` (`@residual(wall:debruijn-integration)`), which each
`reg_t` field invokes.

* `fPath` — density witness path: `fPath t` is the density of
  `P.map (gaussianConvolution X Z t)`.
* `reg_t` — per-time V2 de Bruijn regularity at each interior `t ∈ (0, T)`,
  with `density_t = fPath t` (so the per-time `HasDerivAt` value matches the
  integrand). This is what feeds `debruijnIdentityV2_holds` per time-point.
* `cont` — continuity of the heat-flow entropy on the closed interval `[0, T]`
  (a path-regularity precondition; cf. the Gaussian instance
  `continuousOn_differentialEntropy_heat_flow_gaussian`).
* `integrable` — the path integrand `(1/2) · J(X + √t·Z)` is interval-integrable
  on `(0, T)` (path integrability precondition).

@audit:ok — independent honesty audit (2026-05-31): all 4 fields are genuine
regularity preconditions, NOT load-bearing. Core-reconstruction test: granting
`fPath` (bare data) + `reg_t` + `cont` + `integrable` does NOT yield the
integration identity directly — `reg_t` only supplies per-time
`IsRegularDeBruijnHypV2` inputs (2 fields `Z_law` + `density_t`, the
`derivAt_entropy_eq_half_fisher_v2` field having been removed Phase 2.B), so the
de Bruijn analytic core `(d/dt)h = (1/2)J` (heat eq + IBP) is NOT bundled here;
it is produced only by calling the per-time wall `debruijnIdentityV2_holds`
(`@residual(wall:debruijn-integration)`) inside the consumer body. `cont` /
`integrable` are standard FTC preconditions. Non-vacuous: Gaussian instance
(`continuousOn_differentialEntropy_heat_flow_gaussian`, `bounded_T_ftc_gaussian`
in EPIL3Integration) satisfies all fields. -/
structure IsDeBruijnPathRegular {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) where
  /-- Density witness path. -/
  fPath : ℝ → ℝ → ℝ
  /-- Per-time V2 de Bruijn regularity at each interior time, with the density
  witness pinned to `fPath t`. -/
  reg_t : ∀ t ∈ Set.Ioo (0 : ℝ) T,
    ∃ h_reg : IsRegularDeBruijnHypV2 X Z P t, h_reg.density_t = fPath t
  /-- Continuity of the heat-flow entropy on `[0, T]`. -/
  cont : ContinuousOn
    (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
    (Set.Icc 0 T)
  /-- The path integrand is interval-integrable. -/
  integrable : IntervalIntegrable
    (fun t => (1/2) * fisherInfoOfDensityReal (fPath t)) volume 0 T

/-- **de Bruijn 積分恒等式 — 構造的 closure (per-time wall への reduction)**.

per-time の `debruijnIdentityV2_holds` (`@residual(wall:debruijn-integration)`)
を FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`) で積分した差分
恒等式の存在形。Phase 4 structural closure (2026-05-31): 旧 independent `sorry`
を path-regularity precondition `IsDeBruijnPathRegular` + FTC で genuine 化。本
lemma 自身に local `sorry` は無く、唯一の wall (`debruijnIdentityV2_holds` の
per-time sorry) に transitively 依存するだけ。

`hT : 0 ≤ T` と path-regularity bundle `h_path` は regularity / 積分可能性の
precondition であり、de Bruijn 不等式の核 (heat eq IBP) は per-time wall lemma
側に残る (load-bearing bundling ではない)。

Independent honesty audit (2026-05-31): body genuine — Step 1 calls the per-time
wall `debruijnIdentityV2_holds` (`@residual(wall:debruijn-integration)`) for each
`t ∈ Ioo 0 T`, Step 2 assembles via Mathlib FTC
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, Steps 3-5 convert the
interval integral to `Set.Ioo`/`Set.Ioc` and fix the boundary `f 0 = h(P.map X)`.
No `:= sorry` / `:True` disguise. `h_path : IsDeBruijnPathRegular` is a genuine
regularity precondition (not load-bearing — see that structure's audit note).
Honesty improvement: this replaced 2 independent `sorry`s with a single
transitive dependency on the per-time wall (`#print axioms` shows `sorryAx`
solely via that wall + standard `propext`/`Classical.choice`/`Quot.sound`).
Verdict honest_residual: local 0 sorry, transitive `wall:debruijn-integration`. -/
theorem debruijnIntegrationIdentity_holds
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (T : ℝ) (hT : 0 ≤ T)
    (h_path : IsDeBruijnPathRegular X Z P T) :
    ∃ (fPath : ℝ → ℝ → ℝ),
      ∀ (h_X h_target : ℝ),
        h_X = differentialEntropy (P.map X) →
        h_target = differentialEntropy (P.map (gaussianConvolution X Z T)) →
        h_target - h_X
          = ∫ t in Set.Ioo 0 T, (1/2)
            * (fisherInfoOfMeasureV2
                (P.map (gaussianConvolution X Z t)) (fPath t)).toReal ∂volume := by
  refine ⟨h_path.fPath, ?_⟩
  intro h_X h_target hX_def htarget_def
  -- The integrand `(1/2) * (fisherInfoOfMeasureV2 _ (fPath t)).toReal` is defeq to
  -- `(1/2) * fisherInfoOfDensityReal (fPath t)`.
  set f : ℝ → ℝ :=
    fun s => differentialEntropy (P.map (gaussianConvolution X Z s)) with hf_def
  set f' : ℝ → ℝ := fun t => (1/2) * fisherInfoOfDensityReal (h_path.fPath t) with hf'_def
  -- Step 1: per-time `HasDerivAt f (f' t) t` for `t ∈ Ioo 0 T`, via the wall lemma.
  have h_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt f (f' t) t := by
    intro t ht
    obtain ⟨h_reg, h_dens⟩ := h_path.reg_t t ht
    have h := debruijnIdentityV2_holds X Z hX hZ hXZ ht.1 h_reg
    -- `h : HasDerivAt f ((1/2) * fisherInfoOfDensityReal h_reg.density_t) t`.
    rw [h_dens] at h
    exact h
  -- Step 2: Mathlib FTC.
  have h_ftc : ∫ t in (0 : ℝ)..T, f' t = f T - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT h_path.cont h_deriv
      h_path.integrable
  -- Step 3: convert `intervalIntegral` (0..T) → `Set.Ioo 0 T ∂volume`.
  have h_ioc : ∫ t in (0 : ℝ)..T, f' t = ∫ t in Set.Ioc (0 : ℝ) T, f' t ∂volume :=
    intervalIntegral.integral_of_le hT
  have h_ioo_eq_ioc :
      ∫ t in Set.Ioc (0 : ℝ) T, f' t ∂volume = ∫ t in Set.Ioo (0 : ℝ) T, f' t ∂volume :=
    MeasureTheory.integral_Ioc_eq_integral_Ioo
  -- Step 4: boundary `f 0 = differentialEntropy (P.map X)`.
  have h_f0 : f 0 = differentialEntropy (P.map X) := by
    have h_path0 : gaussianConvolution X Z 0 = X := by
      funext ω; simp [gaussianConvolution]
    simp only [hf_def, h_path0]
  -- Step 5: identify the goal integrand with `f'` (defeq).
  have h_integrand :
      (fun t => (1/2)
        * (fisherInfoOfMeasureV2 (P.map (gaussianConvolution X Z t)) (h_path.fPath t)).toReal)
      = f' := rfl
  -- Assemble.
  rw [hX_def, htarget_def]
  show differentialEntropy (P.map (gaussianConvolution X Z T))
        - differentialEntropy (P.map X)
      = ∫ t in Set.Ioo 0 T, f' t ∂volume
  rw [← h_f0, ← h_ftc, h_ioc, h_ioo_eq_ioc]

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
