import InformationTheory.Meta.EntryPoint
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# The de la Vallée-Poussin criterion for uniform integrability

A general-purpose, measure-agnostic de la Vallée-Poussin criterion: if there is a
*superlinear* control function `G : ℝ≥0∞ → ℝ≥0∞` (meaning `G t / t → ∞` as `t → ∞`)
whose composition with the norm has a *uniform* finite integral bound
`∀ i, ∫⁻ x, G ‖f i x‖ₑ ∂μ ≤ C < ∞`, then the family `f` is `UnifIntegrable` at
exponent `1`.

This is the classical "forward" direction of the de la Vallée-Poussin theorem.
Mathlib does not have this lemma (loogle `UnifIntegrable, ConvexOn = Found 0`), but
the proof is short and reduces to `MeasureTheory.unifIntegrable_of` — crucially that
gateway does not require `[IsFiniteMeasure μ]`, so the criterion applies to
infinite measures such as `volume`.

The intended downstream consumer is the EPI G2 Vitali witness chain for the approximate-identity
L¹ convergence of a density under vanishing-variance Gaussian convolution, where `μ = volume` and
`f n = negMulLog (pX ∗ g_{u n})`.

`@audit:ok`
-/

open MeasureTheory ENNReal NNReal Filter Topology Set

namespace InformationTheory.Shannon

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {ι : Type*}

/-- Superlinear growth control, the genuine de la Vallée-Poussin hypothesis on
`G : ℝ≥0∞ → ℝ≥0∞`: for every slope `K` there is a finite threshold `M` beyond which
`K * t ≤ G t`. This is the non-degenerate `ℝ≥0∞` reading of "`G t / t → ∞`" — note
that `Filter.atTop` on `ℝ≥0∞` collapses to the singleton `{∞}` (since `∞` is the top),
so the literal `Tendsto (G ·/·) atTop atTop` would be vacuous; this threshold form is
the usable statement. -/
def Superlinear (G : ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ∀ K : ℝ≥0∞, ∃ M : ℝ≥0, ∀ t : ℝ≥0∞, (M : ℝ≥0∞) ≤ t → K * t ≤ G t

/-- The **de la Vallée-Poussin criterion** (forward direction).

If `G : ℝ≥0∞ → ℝ≥0∞` is superlinear (`Superlinear G`, i.e. `K * t ≤ G t` eventually for
every slope `K`) and the family `f` satisfies a uniform bound
`∀ i, ∫⁻ x, G ‖f i x‖ₑ ∂μ ≤ C` with `C ≠ ∞`, then `f` is uniformly integrable at
exponent `1`.

The measure `μ` is arbitrary — no `[IsFiniteMeasure μ]` is needed (the proof goes
through `MeasureTheory.unifIntegrable_of`, which is finite-measure-free), so this
applies to `volume`. -/
@[entry_point]
theorem unifIntegrable_of_superlinear_lintegral
    {f : ι → α → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (G : ℝ≥0∞ → ℝ≥0∞)
    (hG_superlinear : Superlinear G)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ i, ∫⁻ x, G (‖f i x‖ₑ) ∂μ ≤ C) :
    UnifIntegrable f 1 μ := by
  -- Effective bound: replace `C` by `C' := max C 1` so that `C' ≠ 0` and `C' ≠ ∞`.
  set C' : ℝ≥0∞ := max C 1 with hC'def
  have hC'_top : C' ≠ ∞ := by simp [hC'def, hC]
  have hC'_pos : C' ≠ 0 := by
    have : (1 : ℝ≥0∞) ≤ C' := le_max_right _ _
    exact (lt_of_lt_of_le one_pos this).ne'
  have hbound' : ∀ i, ∫⁻ x, G (‖f i x‖ₑ) ∂μ ≤ C' := fun i ↦ (hbound i).trans (le_max_left _ _)
  -- Reduce to the indicator-tail estimate via `unifIntegrable_of` (no `[IsFiniteMeasure]`).
  refine unifIntegrable_of (le_refl 1) (by norm_num) hf ?_
  intro ε hε
  set εE : ℝ≥0∞ := ENNReal.ofReal ε with hεE
  have hεE_pos : εE ≠ 0 := by rw [hεE]; simpa using hε
  have hεE_top : εE ≠ ∞ := by simp [hεE]
  -- Slope `K := C' / εE` and multiplier `θ := εE / C' = K⁻¹`.
  set K : ℝ≥0∞ := C' / εE with hKdef
  set θ : ℝ≥0∞ := εE / C' with hθdef
  have hK_pos : K ≠ 0 := by rw [hKdef]; exact ENNReal.div_ne_zero.mpr ⟨hC'_pos, hεE_top⟩
  have hK_top : K ≠ ∞ := by rw [hKdef]; exact ENNReal.div_ne_top hC'_top hεE_pos
  -- Extract the de la Vallée-Poussin threshold for slope `K`.
  obtain ⟨M, hM⟩ := hG_superlinear K
  refine ⟨M, fun i ↦ ?_⟩
  -- Pointwise: on the tail `{M ≤ ‖f i x‖ₑ}`, `‖f i x‖ₑ ≤ θ * G ‖f i x‖ₑ`.
  -- Bound the indicator `eLpNorm` by `∫⁻ (θ * G ‖f i‖ₑ)` and conclude `≤ εE`.
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc
    ∫⁻ x, ‖({ x | M ≤ ‖f i x‖₊ }.indicator (f i)) x‖ₑ ∂μ
        ≤ ∫⁻ x, θ * G (‖f i x‖ₑ) ∂μ := by
          refine lintegral_mono fun x ↦ ?_
          rw [enorm_indicator_eq_indicator_enorm]
          by_cases hx : x ∈ { x | M ≤ ‖f i x‖₊ }
          · rw [Set.indicator_of_mem hx]
            -- `M ≤ ‖f i x‖₊` gives `(M:ℝ≥0∞) ≤ ‖f i x‖ₑ`; apply the threshold bound.
            have ht : (M : ℝ≥0∞) ≤ ‖f i x‖ₑ := by
              rw [enorm_eq_nnnorm]; exact_mod_cast hx
            have hKt : K * ‖f i x‖ₑ ≤ G (‖f i x‖ₑ) := hM _ ht
            -- `‖f i x‖ₑ ≤ θ * G ‖f i x‖ₑ`: multiply `hKt` by `θ = K⁻¹` and cancel `θ * K = 1`.
            have hθK : θ * K = 1 := by
              have hθeq : θ = K⁻¹ := by
                rw [hθdef, hKdef, ENNReal.inv_div (Or.inl hεE_top) (Or.inl hεE_pos)]
              rw [hθeq, ENNReal.inv_mul_cancel hK_pos hK_top]
            calc ‖f i x‖ₑ = (θ * K) * ‖f i x‖ₑ := by rw [hθK, one_mul]
              _ = θ * (K * ‖f i x‖ₑ) := by rw [mul_assoc]
              _ ≤ θ * G (‖f i x‖ₑ) := by gcongr
          · rw [Set.indicator_of_notMem hx]; positivity
    _ = θ * ∫⁻ x, G (‖f i x‖ₑ) ∂μ := by
          have hθ_top : θ ≠ ∞ := by rw [hθdef]; exact ENNReal.div_ne_top hεE_top hC'_pos
          rw [lintegral_const_mul' θ _ hθ_top]
    _ ≤ θ * C' := by gcongr; exact hbound' i
    _ = εE := by
          rw [hθdef, ENNReal.div_mul_cancel hC'_pos hC'_top]


end InformationTheory.Shannon
