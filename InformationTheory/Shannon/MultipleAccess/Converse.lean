import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.Basic
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.MutualInfo

/-!
# Multiple access channel — converse (outer bound)

The converse to the MAC coding theorem (Cover–Thomas Thm 15.3.1, eq. 15.85–15.90):
for uniformly distributed, independent messages decoded by a joint decoder, the rate pair
satisfies the three corner-point inequalities of `InMACCapacityRegion`.

Each of the three bounds is the **message-level Fano converse**, obtained from the
encoder-free single-shot converse `shannon_converse_single_shot` by placing the
conditioning message in the *output* slot:

* user 1: `log |M₁| ≤ I(M₁; (M₂, Yⁿ)) + h(Pe₁) + Pe₁ log(|M₁| − 1)`
* user 2: `log |M₂| ≤ I(M₂; (M₁, Yⁿ)) + h(Pe₂) + Pe₂ log(|M₂| − 1)`
* sum:    `log |M₁| + log |M₂| ≤ I((M₁, M₂); Yⁿ) + h(Pe) + Pe log(|M₁·M₂| − 1)`

Here `I(M₁; (M₂, Yⁿ)) = I(M₁; Yⁿ | M₂)` under message independence, the standard converse
intermediate. The single-letterization to the channel quantities `I(X₁; Y | X₂)` etc. is a
separate refinement, tracked in `mac-moonshot-plan.md` (Phase A2).

## Main statements

* `mac_converse_bound₁` / `mac_converse_bound₂` / `mac_converse_bound_sum` — the three
  corner-point inequalities.
* `mac_converse_message_level` — the packaged `InMACCapacityRegion` outer bound.
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}
  [MeasurableSpace α₁] [MeasurableSpace α₂]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
variable {M₁ M₂ n : ℕ}

/-- **MAC converse, user-1 corner bound** (message level): under a uniform message `Msg₁`,
`log |M₁| ≤ I(M₁; (M₂, Yⁿ)) + h(Pe₁) + Pe₁ · log(|M₁| − 1)`, where the user-1 error
probability `Pe₁` is measured against the joint decoder's first component. -/
theorem mac_converse_bound₁
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (hMsg₁ : Measurable Msg₁) (hMsg₂ : Measurable Msg₂) (hYs : ∀ i, Measurable (Ys i))
    (hMsg₁_uniform : μ.map Msg₁ = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₁ : 2 ≤ M₁) :
    Real.log (M₁ : ℝ) ≤
      (mutualInfo μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).1))
        + MeasureFano.errorProb μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).1) * Real.log ((M₁ : ℝ) - 1) := by
  classical
  haveI : Nonempty (Fin M₁) := ⟨⟨0, by omega⟩⟩
  set Yo : Ω → Fin M₂ × (Fin n → β) := fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω) with hYo_def
  have hYo : Measurable Yo := hMsg₂.prodMk (measurable_pi_iff.mpr hYs)
  have hdec : Measurable (fun p : Fin M₂ × (Fin n → β) ↦ (c.decoder p.2).1) :=
    measurable_of_countable _
  have hcard : 2 ≤ Fintype.card (Fin M₁) := by rw [Fintype.card_fin]; exact hcard₁
  have hMI_fin : mutualInfo μ Msg₁ Yo ≠ ∞ := mutualInfo_ne_top μ Msg₁ Yo hMsg₁ hYo
  have h := shannon_converse_single_shot μ Msg₁ Yo
    (fun p ↦ (c.decoder p.2).1) hMsg₁ hYo hdec hMsg₁_uniform hcard hMI_fin
  rw [Fintype.card_fin] at h
  exact h

/-- **MAC converse, user-2 corner bound** (message level): symmetric to
`mac_converse_bound₁`. -/
theorem mac_converse_bound₂
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (hMsg₁ : Measurable Msg₁) (hMsg₂ : Measurable Msg₂) (hYs : ∀ i, Measurable (Ys i))
    (hMsg₂_uniform : μ.map Msg₂ = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₂ : 2 ≤ M₂) :
    Real.log (M₂ : ℝ) ≤
      (mutualInfo μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).2))
        + MeasureFano.errorProb μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).2) * Real.log ((M₂ : ℝ) - 1) := by
  classical
  haveI : Nonempty (Fin M₂) := ⟨⟨0, by omega⟩⟩
  set Yo : Ω → Fin M₁ × (Fin n → β) := fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω) with hYo_def
  have hYo : Measurable Yo := hMsg₁.prodMk (measurable_pi_iff.mpr hYs)
  have hdec : Measurable (fun p : Fin M₁ × (Fin n → β) ↦ (c.decoder p.2).2) :=
    measurable_of_countable _
  have hcard : 2 ≤ Fintype.card (Fin M₂) := by rw [Fintype.card_fin]; exact hcard₂
  have hMI_fin : mutualInfo μ Msg₂ Yo ≠ ∞ := mutualInfo_ne_top μ Msg₂ Yo hMsg₂ hYo
  have h := shannon_converse_single_shot μ Msg₂ Yo
    (fun p ↦ (c.decoder p.2).2) hMsg₂ hYo hdec hMsg₂_uniform hcard hMI_fin
  rw [Fintype.card_fin] at h
  exact h

/-- **MAC converse, sum-rate bound** (message level): treating the pair `(M₁, M₂)` as a
single uniform message decoded jointly,
`log |M₁| + log |M₂| ≤ I((M₁, M₂); Yⁿ) + h(Pe) + Pe · log(|M₁·M₂| − 1)`. -/
theorem mac_converse_bound_sum
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (hMsg₁ : Measurable Msg₁) (hMsg₂ : Measurable Msg₂) (hYs : ∀ i, Measurable (Ys i))
    (hMsg₁₂_uniform :
      μ.map (fun ω ↦ (Msg₁ ω, Msg₂ ω))
        = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ) ≤
      (mutualInfo μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)
              c.decoder)
        + MeasureFano.errorProb μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)
              c.decoder * Real.log (((M₁ * M₂ : ℕ) : ℝ) - 1) := by
  classical
  haveI : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  set Msg : Ω → Fin M₁ × Fin M₂ := fun ω ↦ (Msg₁ ω, Msg₂ ω) with hMsg_def
  set Yo : Ω → Fin n → β := fun ω i ↦ Ys i ω with hYo_def
  have hMsg : Measurable Msg := hMsg₁.prodMk hMsg₂
  have hYo : Measurable Yo := measurable_pi_iff.mpr hYs
  have hdec : Measurable c.decoder := measurable_of_countable _
  have hcard : 2 ≤ Fintype.card (Fin M₁ × Fin M₂) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; nlinarith [hcard₁, hcard₂]
  have hMI_fin : mutualInfo μ Msg Yo ≠ ∞ := mutualInfo_ne_top μ Msg Yo hMsg hYo
  have h := shannon_converse_single_shot μ Msg Yo c.decoder hMsg hYo hdec
    hMsg₁₂_uniform hcard hMI_fin
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  have hM₁ne : (M₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hM₂ne : (M₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : Real.log ((M₁ * M₂ : ℕ) : ℝ) = Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hM₁ne hM₂ne]
  rw [hlog] at h
  exact h

/-- **MAC converse — message-level Fano outer bound**: for uniform messages decoded by a
joint decoder, the rate pair `(log |M₁|, log |M₂|)` satisfies the three message-level Fano
information bounds, packaged as `InMACCapacityRegion`.

This is the **message-level step only**: the information slots are the n-letter
message–output mutual informations, not the single-letter channel quantities
`I(X₁; Y | X₂)` etc. The single-letterization that turns this into the textbook MAC
converse (Cover–Thomas Thm 15.3.1) is not yet done; it is tracked in
`mac-moonshot-plan.md` (Phase A2). -/
@[entry_point]
theorem mac_converse_message_level
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg₁ : Ω → Fin M₁) (Msg₂ : Ω → Fin M₂) (Ys : Fin n → Ω → β)
    (c : MACCode M₁ M₂ n α₁ α₂ β)
    (hMsg₁ : Measurable Msg₁) (hMsg₂ : Measurable Msg₂) (hYs : ∀ i, Measurable (Ys i))
    (hMsg₁_uniform : μ.map Msg₁ = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count)
    (hMsg₂_uniform : μ.map Msg₂ = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (hMsg₁₂_uniform :
      μ.map (fun ω ↦ (Msg₁ ω, Msg₂ ω))
        = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InMACCapacityRegion (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((mutualInfo μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).1))
        + MeasureFano.errorProb μ Msg₁ (fun ω ↦ (Msg₂ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).1) * Real.log ((M₁ : ℝ) - 1))
      ((mutualInfo μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).2))
        + MeasureFano.errorProb μ Msg₂ (fun ω ↦ (Msg₁ ω, fun i ↦ Ys i ω))
              (fun p ↦ (c.decoder p.2).2) * Real.log ((M₂ : ℝ) - 1))
      ((mutualInfo μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)
              c.decoder)
        + MeasureFano.errorProb μ (fun ω ↦ (Msg₁ ω, Msg₂ ω)) (fun ω i ↦ Ys i ω)
              c.decoder * Real.log (((M₁ * M₂ : ℕ) : ℝ) - 1)) :=
  ⟨mac_converse_bound₁ μ Msg₁ Msg₂ Ys c hMsg₁ hMsg₂ hYs hMsg₁_uniform hcard₁,
   mac_converse_bound₂ μ Msg₁ Msg₂ Ys c hMsg₁ hMsg₂ hYs hMsg₂_uniform hcard₂,
   mac_converse_bound_sum μ Msg₁ Msg₂ Ys c hMsg₁ hMsg₂ hYs hMsg₁₂_uniform hcard₁ hcard₂⟩

end InformationTheory.Shannon.MAC
