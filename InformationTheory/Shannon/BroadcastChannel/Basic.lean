import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.Basic

/-!
# Broadcast channel — primitive definitions

Two-receiver broadcast channel (BC) primitives, following the single-user
`InformationTheory.Shannon.ChannelCoding.Basic` and the multiple-access
`InformationTheory.Shannon.MultipleAccess.Basic` conventions (Cover–Thomas §15.6).

## Main definitions

* `BCChannel α β₁ β₂ := Kernel α (β₁ × β₂)` — a discrete BC with one input and a pair
  of outputs.
* `BroadcastCode M₁ M₂ n α β₁ β₂` — a two-receiver block code: one joint encoder for the
  message pair and a separate decoder per receiver.
* `BroadcastCode.errorProbAt₁` / `errorProbAt₂` — the pointwise per-receiver block-decoding
  error probabilities.
* `InBCCapacityRegion R₁ R₂ I₁ I₂` — the auxiliary-variable capacity-region predicate
  bundling the two corner inequalities `R₁ ≤ I₁`, `R₂ ≤ I₂` (degraded BC, Cover–Thomas
  Thm 15.6.2: `I₁ = I(X; Y₁ | U)`, `I₂ = I(U; Y₂)`).
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {α β₁ β₂ : Type*}
  [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- A discrete broadcast channel: a Markov kernel from the input `α` to the output pair
`β₁ × β₂` (receiver 1 sees the first coordinate, receiver 2 the second). -/
abbrev BCChannel (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] :=
  Kernel α (β₁ × β₂)

/-- A two-receiver BC block code of length `n`: a joint encoder for the message pair and a
separate decoder for each receiver.  As in the single-user `Code`, no measurability fields
are bundled (all functions on finite alphabets are automatically measurable). -/
structure BroadcastCode (M₁ M₂ n : ℕ) (α β₁ β₂ : Type*)
    [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] where
  /-- Joint encoder of the message pair into an input codeword. -/
  encoder : Fin M₁ × Fin M₂ → (Fin n → α)
  /-- Decoder for receiver 1 (sees only the `β₁` outputs). -/
  decoder₁ : (Fin n → β₁) → Fin M₁
  /-- Decoder for receiver 2 (sees only the `β₂` outputs). -/
  decoder₂ : (Fin n → β₂) → Fin M₂

namespace BroadcastCode

variable {M₁ M₂ n : ℕ}

/-- Memoryless block output law for the message pair `m`: each letter `i` is sent through the
channel `W (encoder m i)`, with letters independent. -/
noncomputable def blockOutputLaw
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    (m : Fin M₁ × Fin M₂) : Measure (Fin n → β₁ × β₂) :=
  Measure.pi (fun i ↦ W (c.encoder m i))

/-- Receiver-1 error event for the pair `m`: outputs whose `β₁`-projection decodes to
something other than `m.1`. -/
def errorEvent₁ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β₁ × β₂) :=
  { y | c.decoder₁ (fun i ↦ (y i).1) ≠ m.1 }

/-- Receiver-2 error event for the pair `m`: outputs whose `β₂`-projection decodes to
something other than `m.2`. -/
def errorEvent₂ (c : BroadcastCode M₁ M₂ n α β₁ β₂) (m : Fin M₁ × Fin M₂) :
    Set (Fin n → β₁ × β₂) :=
  { y | c.decoder₂ (fun i ↦ (y i).2) ≠ m.2 }

/-- Pointwise receiver-1 error probability when the pair `m` is sent. -/
noncomputable def errorProbAt₁
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    (m : Fin M₁ × Fin M₂) : ℝ≥0∞ :=
  c.blockOutputLaw W m (c.errorEvent₁ m)

/-- Pointwise receiver-2 error probability when the pair `m` is sent. -/
noncomputable def errorProbAt₂
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    (m : Fin M₁ × Fin M₂) : ℝ≥0∞ :=
  c.blockOutputLaw W m (c.errorEvent₂ m)

/-- Average receiver-1 error probability under a uniform message pair. For `M₁·M₂ = 0` we set
this to `0`. -/
noncomputable def averageErrorProb₁
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) : ℝ≥0∞ :=
  if M₁ * M₂ = 0 then 0
  else ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : Fin M₁ × Fin M₂, c.errorProbAt₁ W m

/-- Average receiver-2 error probability under a uniform message pair. For `M₁·M₂ = 0` we set
this to `0`. -/
noncomputable def averageErrorProb₂
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) : ℝ≥0∞ :=
  if M₁ * M₂ = 0 then 0
  else ((M₁ * M₂ : ℕ) : ℝ≥0∞)⁻¹ * ∑ m : Fin M₁ × Fin M₂, c.errorProbAt₂ W m

/-- Each pointwise receiver-1 error probability is at most `1`. -/
theorem errorProbAt₁_le_one
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (m : Fin M₁ × Fin M₂) :
    c.errorProbAt₁ W m ≤ 1 := by
  have : IsProbabilityMeasure (c.blockOutputLaw W m) := by
    unfold blockOutputLaw; infer_instance
  exact prob_le_one

/-- Each pointwise receiver-2 error probability is at most `1`. -/
theorem errorProbAt₂_le_one
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (m : Fin M₁ × Fin M₂) :
    c.errorProbAt₂ W m ≤ 1 := by
  have : IsProbabilityMeasure (c.blockOutputLaw W m) := by
    unfold blockOutputLaw; infer_instance
  exact prob_le_one

end BroadcastCode

/-! ## Auxiliary-variable capacity region (degraded BC) -/

/-- The degraded-BC capacity-region predicate: a bundle of the two corner inequalities
`R₁ ≤ I₁`, `R₂ ≤ I₂` on four real numbers. The slots `I₁, I₂` are abstract information bounds
— the predicate does **not** fix their meaning. Two instantiations are intended:

* **message level** (`bc_converse_message_level`): `I₁ = I(W₁; (W₂, Y₁ⁿ))`,
  `I₂ = I(W₂; Y₂ⁿ)` plus Fano terms.
* **single letter** (the standard Cover–Thomas Thm 15.6.2 form, `bc_converse`): with an
  auxiliary `U`, `I₁ = ∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)`, `I₂ = ∑ᵢ I(Uᵢ; Y_{2,i})`.

Unlike the symmetric MAC region, the two receivers are asymmetric (receiver 2 is the degraded
one), so there is no role-swap symmetry — only monotonicity in the information bounds
(`InBCCapacityRegion.mono`). -/
structure InBCCapacityRegion (R₁ R₂ I₁ I₂ : ℝ) : Prop where
  /-- Receiver-1 (strong) rate bound. -/
  bound₁ : R₁ ≤ I₁
  /-- Receiver-2 (degraded) rate bound. -/
  bound₂ : R₂ ≤ I₂

/-- Monotonicity of the region in the information bounds: enlarging `I₁`, `I₂` keeps the rate
pair inside. This is the bridge from the message-level form to the single-letter form. -/
theorem InBCCapacityRegion.mono {R₁ R₂ I₁ I₂ I₁' I₂' : ℝ}
    (h : InBCCapacityRegion R₁ R₂ I₁ I₂)
    (h₁ : I₁ ≤ I₁') (h₂ : I₂ ≤ I₂') :
    InBCCapacityRegion R₁ R₂ I₁' I₂' :=
  ⟨h.bound₁.trans h₁, h.bound₂.trans h₂⟩

end InformationTheory.Shannon.BroadcastChannel
