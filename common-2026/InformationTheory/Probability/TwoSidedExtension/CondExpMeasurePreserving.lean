import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stationary.Basic
import InformationTheory.Shannon.EntropyRate
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Dynamics.Ergodic.Ergodic

namespace InformationTheory.Shannon.TwoSided

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology symmDiff

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Mathlib-gap: `condExp` commutes with measure-preserving transforms

For a measure-preserving `T : Ω₁ → Ω₂` and `n` a sub-σ-algebra of `m₂`,
`(μ₂[f | n]) ∘ T =ᵐ μ₁[f ∘ T | n.comap T]`. Mathlib provides no direct named
version; proved via `ae_eq_condExp_of_forall_setIntegral_eq`. Used by
`integral_MRatioLowerZ_le_one` to identify shifted `condProbInfty` with a
condExp w.r.t. `shifted(negPastSigma)`. -/

section MeasurePreservingCondExp

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
@[entry_point]
lemma condExp_comp_measurePreserving
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    {T : Ω₁ → Ω₂} (h_mp : MeasurePreserving T μ₁ μ₂)
    {f : Ω₂ → ℝ} (hf : Integrable f μ₂)
    (n : MeasurableSpace Ω₂) (hn : n ≤ m₂) :
    (fun x ↦ (μ₂[f | n]) (T x)) =ᵐ[μ₁] μ₁[f ∘ T | n.comap T] := by
  -- KEY TYPECLASS WORKAROUND: hide `n` behind `letI` so it stops competing for synthesis.
  -- After this point, any "synthesize MeasurableSpace Ω₂" picks `m₂` (the only `[..]` instance).
  letI : MeasurableSpace Ω₂ := m₂
  -- Pull the structure fields.
  have hT_meas : Measurable T := h_mp.measurable
  have h_mp_eq : Measure.map T μ₁ = μ₂ := h_mp.map_eq
  -- `n.comap T ≤ m₁`.
  have hcomap_le : n.comap T ≤ m₁ := fun s ⟨t, ht_n, hts⟩ ↦ hts ▸ hT_meas (hn _ ht_n)
  -- `SigmaFinite (μ₁.trim hcomap_le)` from finiteness.
  haveI : IsFiniteMeasure (μ₁.trim hcomap_le) := isFiniteMeasure_trim _
  -- Integrability of pulled-back functions.
  have h_cE_int : Integrable (μ₂[f | n]) μ₂ := integrable_condExp
  have h_cE_comp_int : Integrable ((μ₂[f | n]) ∘ T) μ₁ :=
    h_mp.integrable_comp_of_integrable h_cE_int
  have hf_comp : Integrable (f ∘ T) μ₁ :=
    h_mp.integrable_comp_of_integrable hf
  -- Goal: `(μ₂[f|n]) ∘ T =ᵐ μ₁[f∘T | n.comap T]`.
  -- Direct from `ae_eq_condExp_of_forall_setIntegral_eq`.
  have h_rev : (fun x ↦ (μ₂[f | n]) (T x)) =ᵐ[μ₁] μ₁[f ∘ T | n.comap T] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hcomap_le hf_comp ?_ ?_ ?_
    · intro s _ _; exact h_cE_comp_int.integrableOn
    · intro s hs _
      obtain ⟨B, hB_n, rfl⟩ := hs
      have hB_m₂ : MeasurableSet B := hn _ hB_n
      -- Cache `g := μ₂[f|n]` so rewrites in `μ₂ → μ₁.map T` don't touch the inner `μ₂` of g.
      set g : Ω₂ → ℝ := μ₂[f | n] with hg_def
      have h_g_meas_m₂ : Measurable g :=
        (stronglyMeasurable_condExp.mono hn).measurable
      have h_g_int : Integrable g μ₂ := h_cE_int
      have h_g_comp_int : Integrable (g ∘ T) μ₁ := h_cE_comp_int
      have h_lhs : ∫ x in T ⁻¹' B, g (T x) ∂μ₁ = ∫ y in B, g y ∂μ₂ := by
        conv_rhs => rw [← h_mp_eq]
        rw [setIntegral_map hB_m₂ h_g_meas_m₂.aestronglyMeasurable hT_meas.aemeasurable]
      have h_mid : ∫ y in B, g y ∂μ₂ = ∫ y in B, f y ∂μ₂ := by
        rw [hg_def]; exact setIntegral_condExp hn hf hB_n
      have h_rhs : ∫ y in B, f y ∂μ₂ = ∫ x in T ⁻¹' B, (f ∘ T) x ∂μ₁ := by
        have h_asm : AEStronglyMeasurable f (Measure.map T μ₁) := by
          rw [h_mp_eq]; exact hf.aestronglyMeasurable
        conv_lhs => rw [← h_mp_eq]
        rw [setIntegral_map hB_m₂ h_asm hT_meas.aemeasurable]
        rfl
      show ∫ x in T ⁻¹' B, g (T x) ∂μ₁ = ∫ x in T ⁻¹' B, (f ∘ T) x ∂μ₁
      rw [h_lhs, h_mid, h_rhs]
    · refine StronglyMeasurable.aestronglyMeasurable ?_
      have h_sm_m₂ : StronglyMeasurable[n] (μ₂[f | n]) := stronglyMeasurable_condExp
      -- `T : (Ω₁, n.comap T) → (Ω₂, n)` is measurable by definition of comap.
      have hT_comap : @Measurable Ω₁ Ω₂ (n.comap T) n T := fun s hs ↦ ⟨s, hs, rfl⟩
      exact h_sm_m₂.comp_measurable hT_comap
  exact h_rev

end MeasurePreservingCondExp

end InformationTheory.Shannon.TwoSided
