import Common2026.Shannon.FisherInfoV2DeBruijnAssembly

/-!
# de Bruijn identity (V2) — genuine wiring of `debruijnIdentityV2_holds_assembled`

`FisherInfoV2DeBruijn.lean` originally housed the per-time wall shim
`debruijnIdentityV2_holds` (`sorry` body, `@residual(plan:epi-debruijn-pertime-closure)`)
together with its two consumers `deBruijn_identity_v2` and
`debruijnIntegrationIdentity_holds`. The shim could not be made genuine in-place
because the genuine same-signature proof `debruijnIdentityV2_holds_assembled`
lives in `FisherInfoV2DeBruijnAssembly.lean`, which transitively imports
`FisherInfoV2DeBruijn.lean` (via `FisherInfoV2DeBruijnPerTime` and via
`FisherConvBound`) — so `FisherInfoV2DeBruijn` cannot call `_assembled` without
creating an import cycle.

**Resolution (Strategy B — relocate consumers downstream)**: the per-time shim
is deleted from `FisherInfoV2DeBruijn.lean`, and its two consumers are moved here,
downstream of the assembly. They now delegate to the genuine sorryAx-free
`debruijnIdentityV2_holds_assembled` (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`), so the de Bruijn pipeline carries no
`sorry` for the per-time identity anymore.

The surviving definitions (`gaussianConvolution`, `IsRegularDeBruijnHypV2`,
`IsDeBruijnPathRegular`, the Gaussian discharge, etc.) stay in
`FisherInfoV2DeBruijn.lean` and are available here transitively.
-/

namespace Common2026.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)
open scoped ENNReal NNReal Real

/-- **de Bruijn identity (V2 form)**, genuine delegation to the assembled lemma.

For `X ⊥ Z` with `Z ∼ 𝒩(0, 1)`,

`(d/dt) h(X + √t · Z) = (1/2) · J(X + √t · Z)`,

stated with **V2 Fisher information** (`fisherInfoOfDensityReal`) on the RHS.

This delegates to `debruijnIdentityV2_holds_assembled`
(`FisherInfoV2DeBruijnAssembly.lean`), which is proven **sorryAx-free**
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`). It is no longer a
pass-through to a per-time wall shim: the per-time identity is genuine
end-to-end. `h_reg` is the V2 de Bruijn regularity precondition. -/
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
  debruijnIdentityV2_holds_assembled X Z hX hZ hXZ ht h_reg

/-- **de Bruijn 積分恒等式 — genuine (assembled per-time identity + FTC)**.

The per-time identity `debruijnIdentityV2_holds_assembled` is integrated along the
heat-flow path `(0, T)` via Mathlib FTC
(`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`) to produce the difference
identity

    `h(X + √T·Z) − h(X) = ∫_0^T (1/2)·J(X + √t·Z) dt`.

`hT : 0 ≤ T` and the path-regularity bundle `h_path : IsDeBruijnPathRegular` are
regularity / integrability preconditions; the de Bruijn analytic core (heat eq +
IBP) is fully discharged by the genuine `debruijnIdentityV2_holds_assembled`
(sorryAx-free), not bundled here.

This is now genuine: the body Step 1 calls the genuine per-time identity
`debruijnIdentityV2_holds_assembled` for each `t ∈ Ioo 0 T`, Step 2 assembles via
Mathlib FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, Steps 3-5
convert the interval integral to `Set.Ioo`/`Set.Ioc` and fix the boundary
`f 0 = h(P.map X)`. No `:= sorry` / `:True` disguise. `h_path : IsDeBruijnPathRegular`
is a genuine regularity precondition (not load-bearing — see that structure's
audit note in `FisherInfoV2DeBruijn.lean`). -/
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
  -- Step 1: per-time `HasDerivAt f (f' t) t` for `t ∈ Ioo 0 T`, via the genuine assembled identity.
  have h_deriv : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt f (f' t) t := by
    intro t ht
    obtain ⟨h_reg, h_dens⟩ := h_path.reg_t t ht
    have h := debruijnIdentityV2_holds_assembled X Z hX hZ hXZ ht.1 h_reg
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

end Common2026.Shannon.FisherInfoV2
