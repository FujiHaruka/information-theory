import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Basic

/-!
# Multiple access channel — primitive definitions

Two-user multiple access channel (MAC) primitives, following the single-user
`InformationTheory.Shannon.ChannelCoding.Basic` conventions (Cover–Thomas §15.3).

## Main definitions

* `MACChannel α₁ α₂ β := Kernel (α₁ × α₂) β` — a discrete MAC with two inputs and one
  output.
* `MACCode M₁ M₂ n α₁ α₂ β` — a two-user block code: two encoders and a joint pair
  decoder.
* `MACCode.errorProbAt` / `MACCode.averageErrorProb` — the pointwise and uniform-average
  block-decoding error probabilities.
* `InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth` — the corner-point capacity-region predicate:
  `R₁ ≤ I₁`, `R₂ ≤ I₂`, `R₁ + R₂ ≤ Iboth`.
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {α₁ α₂ β : Type*}
  [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- A discrete memoryless multiple access channel: a Markov kernel from the joint input
`α₁ × α₂` to the output `β`. -/
abbrev MACChannel (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] :=
  Kernel (α₁ × α₂) β

/-- A two-user MAC block code of length `n`: an encoder for each user and a joint pair
decoder.  As in the single-user `Code`, no measurability fields are bundled (all functions
on finite alphabets are automatically measurable). -/
structure MACCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] where
  /-- Encoder for user 1. -/
  encoder₁ : Fin M₁ → (Fin n → α₁)
  /-- Encoder for user 2. -/
  encoder₂ : Fin M₂ → (Fin n → α₂)
  /-- Joint pair decoder. -/
  decoder  : (Fin n → β) → Fin M₁ × Fin M₂

namespace MACCode

variable {M₁ M₂ n : ℕ}

/-- Decoding region for the message pair `m`: outputs `y` decoded as `m`. -/
def decodingRegion (c : MACCode M₁ M₂ n α₁ α₂ β) (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β) :=
  { y | c.decoder y = m }

/-- The joint error event for the pair `m`: outputs decoded as anything other than `m`.
A single event captures all three MAC error types (user 1 wrong, user 2 wrong, both
wrong). -/
def errorEvent (c : MACCode M₁ M₂ n α₁ α₂ β) (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β) :=
  (c.decodingRegion m)ᶜ

@[simp] lemma mem_errorEvent (c : MACCode M₁ M₂ n α₁ α₂ β)
    (m : Fin M₁ × Fin M₂) (y : Fin n → β) :
    y ∈ c.errorEvent m ↔ c.decoder y ≠ m := by
  simp [errorEvent, decodingRegion]

/-- Pointwise error probability when the pair `m = (m₁, m₂)` is sent: the memoryless block
output law is `Measure.pi (i ↦ W (encoder₁ m₁ i, encoder₂ m₂ i))`. -/
noncomputable def errorProbAt
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β)
    (m : Fin M₁ × Fin M₂) : ℝ≥0∞ :=
  (Measure.pi (fun i ↦ W (c.encoder₁ m.1 i, c.encoder₂ m.2 i))) (c.errorEvent m)

/-- Average error probability under a uniform message pair: `(1/(M₁·M₂)) ∑ m, errorProbAt`.
For `M₁·M₂ = 0` we set this to `0`. -/
noncomputable def averageErrorProb
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) : ℝ≥0∞ :=
  if M₁ * M₂ = 0 then 0
  else ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : Fin M₁ × Fin M₂, c.errorProbAt W m

/-- Each pointwise error probability is at most `1` (the block output law is a probability
measure for a Markov kernel). -/
theorem errorProbAt_le_one
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (m : Fin M₁ × Fin M₂) :
    c.errorProbAt W m ≤ 1 := by
  have : IsProbabilityMeasure
      (Measure.pi (fun i ↦ W (c.encoder₁ m.1 i, c.encoder₂ m.2 i))) := by infer_instance
  exact prob_le_one

/-- The average error probability is at most `1`. -/
@[entry_point]
theorem averageErrorProb_le_one
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    c.averageErrorProb W ≤ 1 := by
  unfold averageErrorProb
  by_cases hM : M₁ * M₂ = 0
  · simp [hM]
  · simp only [hM, if_false]
    have h_sum_le :
        (∑ m : Fin M₁ × Fin M₂, c.errorProbAt W m) ≤ ((M₁ * M₂ : ℕ) : ℝ≥0∞) := by
      calc (∑ m : Fin M₁ × Fin M₂, c.errorProbAt W m)
          ≤ ∑ _m : Fin M₁ × Fin M₂, (1 : ℝ≥0∞) :=
            Finset.sum_le_sum fun m _ ↦ c.errorProbAt_le_one W m
        _ = ((M₁ * M₂ : ℕ) : ℝ≥0∞) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
              Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_mul]
    have hM_pos : (0 : ℝ≥0∞) < ((M₁ * M₂ : ℕ) : ℝ≥0∞) := by
      rw [show (0 : ℝ≥0∞) = ((0 : ℕ) : ℝ≥0∞) from by simp, Nat.cast_lt (α := ℝ≥0∞)]
      exact Nat.pos_of_ne_zero hM
    have hM_ne_top : ((M₁ * M₂ : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
    calc (((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : Fin M₁ × Fin M₂, c.errorProbAt W m)
        ≤ ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ((M₁ * M₂ : ℕ) : ℝ≥0∞) :=
          mul_le_mul_of_nonneg_left h_sum_le bot_le
      _ = 1 := ENNReal.inv_mul_cancel hM_pos.ne' hM_ne_top

/-- The average error probability is finite. -/
theorem averageErrorProb_ne_top
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    c.averageErrorProb W ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (c.averageErrorProb_le_one W)

end MACCode

/-! ## Corner-point capacity region -/

/-- The corner-point MAC capacity-region predicate for a fixed product input: the rate pair
`(R₁, R₂)` lies in the region cut out by the three single-letterized informations
`I₁ = I(X₁; Y | X₂)`, `I₂ = I(X₂; Y | X₁)`, `Iboth = I(X₁, X₂; Y)`. -/
structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where
  /-- User-1 rate bound. -/
  bound₁   : R₁ ≤ I₁
  /-- User-2 rate bound. -/
  bound₂   : R₂ ≤ I₂
  /-- Sum-rate bound. -/
  boundSum : R₁ + R₂ ≤ Iboth

/-- Monotonicity of the region in the information bounds: enlarging `I₁`, `I₂`, `Iboth`
keeps the rate pair inside. -/
theorem InMACCapacityRegion.mono {R₁ R₂ I₁ I₂ Iboth I₁' I₂' Iboth' : ℝ}
    (h : InMACCapacityRegion R₁ R₂ I₁ I₂ Iboth)
    (h₁ : I₁ ≤ I₁') (h₂ : I₂ ≤ I₂') (hsum : Iboth ≤ Iboth') :
    InMACCapacityRegion R₁ R₂ I₁' I₂' Iboth' :=
  ⟨h.bound₁.trans h₁, h.bound₂.trans h₂, h.boundSum.trans hsum⟩

end InformationTheory.Shannon.MAC
