import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.DeBruijnAssembly

/-!
# de Bruijn identity (V2)

The per-time de Bruijn identity and its integrated form, delegating to the assembled
per-time identity `debruijnIdentityV2_holds_assembled`. These consumers live downstream of
the assembly file because the assembly transitively imports `FisherInfoDeBruijn.lean`,
so they cannot call the assembled identity from there without an import cycle.

## Main statements

* `deBruijn_identity_v2` — the per-time de Bruijn identity
  `(d/dt) h(X + √t · Z) = (1/2) · J(X + √t · Z)` with the V2 Fisher information.
* `debruijnIntegrationIdentity_holds` — its integrated form along the heat-flow path.
-/

namespace InformationTheory.Shannon.FisherInfo

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)
open scoped ENNReal NNReal Real

/-- The de Bruijn identity (V2 form): for `X ⊥ Z` with `Z ∼ 𝒩(0, 1)`,
`(d/dt) h(X + √t · Z) = (1/2) · J(X + √t · Z)`, stated with the V2 Fisher information
`fisherInfoOfDensityReal` on the right. Delegates to `debruijnIdentityV2_holds_assembled`;
`h_reg` is the regularity precondition. -/
@[entry_point]
theorem deBruijn_identity_v2
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {t : ℝ} (ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt
      (fun s ↦ differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
      t :=
  debruijnIdentityV2_holds_assembled X Z hX hZ hXZ ht h_reg

/-- The integrated de Bruijn identity: integrating the per-time identity
`debruijnIdentityV2_holds_assembled` along the heat-flow path `(0, T)` via FTC gives
`h(X + √T·Z) − h(X) = ∫₀ᵀ (1/2)·J(X + √t·Z) dt`. Here `hT : 0 ≤ T` and the path-regularity
bundle `h_path : IsDeBruijnPathRegular` are regularity and integrability preconditions. -/
@[entry_point]
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
    fun s ↦ differentialEntropy (P.map (gaussianConvolution X Z s)) with hf_def
  set f' : ℝ → ℝ := fun t ↦ (1/2) * fisherInfoOfDensityReal (h_path.fPath t) with hf'_def
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
      (fun t ↦ (1/2)
        * (fisherInfoOfMeasureV2 (P.map (gaussianConvolution X Z t)) (h_path.fPath t)).toReal)
      = f' := rfl
  -- Assemble.
  rw [hX_def, htarget_def]
  show differentialEntropy (P.map (gaussianConvolution X Z T))
        - differentialEntropy (P.map X)
      = ∫ t in Set.Ioo 0 T, f' t ∂volume
  rw [← h_f0, ← h_ftc, h_ioc, h_ioo_eq_ioc]

end InformationTheory.Shannon.FisherInfo
