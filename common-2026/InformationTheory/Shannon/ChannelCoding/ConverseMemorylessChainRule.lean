import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ChannelCoding.ConverseGeneral
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.MutualInfo

/-!
# Channel coding converse (general input) — memoryless per-summand bound

A memoryless predicate for a discrete memoryless channel together with the conditional
mutual-information chain-rule lemmas it needs, used to derive the per-summand inequality of
the general-input channel coding converse (Cover–Thomas 7.9) from memorylessness alone.

## Main definitions

* `IsMemorylessChannel μ Xs Ys` — a memoryless DMC (without feedback), formalized by the
  per-time-step Markov chain `(X^{≠i}, Y^{≠i}) → X_i → Y_i`, i.e. given `X_i`, the output
  `Y_i` is independent of all other inputs and outputs. No explicit channel kernel `W` is
  referenced.

## Main statements

* `condMutualInfo_le_of_markov_joint` — under the joint Markov chain
  `(Wc, Xs) → (Wc, Zc) → Yo`, `I(Xs; Yo | Wc) ≤ I(Zc; Yo | Wc)`.
* `condMutualInfo_chain_rule_X_2var` / `condMutualInfo_chain_rule_Y_2var` — two-variable
  conditional chain rules for `condMutualInfo` along each axis.

## Implementation notes

The conditional chain-rule lemmas are kept here in local sections rather than in
`CondMutualInfo.lean`, which they leave unmodified; they live in
`namespace InformationTheory.Shannon`, so promoting them to the general API later is easy.

`condMutualInfo_le_of_markov_joint` does not follow from the bare Markov chain
`Xs → Zc → Yo` alone, since `Wc` may break that Markov structure; the augmented chain
`(Wc, Xs) → (Wc, Zc) → Yo` is assumed instead, and the common term `I(Wc; Yo)` is cancelled
via the chain rule, which requires `I(Wc; Yo) ≠ ∞` (an `ENNReal` subtraction).
-/

namespace InformationTheory.Shannon.ChannelCodingConverseGeneral

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## The memoryless-channel predicate -/

section Memoryless

variable {n : ℕ}
variable {α : Type*} [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
variable {β : Type*} [MeasurableSpace β] [Nonempty β] [StandardBorelSpace β]

/-- A memoryless DMC (without feedback) is formalized by the per-time-step Markov
chain property: for each `i : Fin n`, the random variables form a Markov chain

```
(X^{≠i}, Y^{≠i}) → X_i → Y_i
```

That is, given `X_i`, the output `Y_i` is independent of all other inputs `X^{≠i}` and
all other outputs `Y^{≠i}`. This captures the textbook memoryless DMC property without
referring to an explicit channel kernel `W`. This is the feedback-free counterpart of
`IsMemorylessFeedback` (no message argument). -/
def IsMemorylessChannel (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) : Prop :=
  ∀ i : Fin n,
    Shannon.IsMarkovChain μ
      (fun ω ↦
        ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
         (fun (j : {j : Fin n // j ≠ i}) ↦ Ys j.val ω)))
      (Xs i) (Ys i)

/-- Accessor: extract the `i`-th Markov chain from `IsMemorylessChannel`. -/
@[entry_point]
lemma IsMemorylessChannel.markovChain (μ : Measure Ω) [IsFiniteMeasure μ]
    {Xs : Fin n → Ω → α} {Ys : Fin n → Ω → β}
    (h : IsMemorylessChannel μ Xs Ys) (i : Fin n) :
    Shannon.IsMarkovChain μ
      (fun ω ↦
        ((fun (j : {j : Fin n // j ≠ i}) ↦ Xs j.val ω),
         (fun (j : {j : Fin n // j ≠ i}) ↦ Ys j.val ω)))
      (Xs i) (Ys i) :=
  h i

end Memoryless

/-! ## Conditional mutual-information chain-rule lemmas -/

section CondMIAuxiliary

variable {X Y Z W : Type*}
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

/-- Conditional version of `mutualInfo_le_of_markov` (augmented form).

Under the joint Markov chain `(Wc, Xs) → (Wc, Zc) → Yo` (i.e., `Markov` holds with
`Wc` carried on both sides), and assuming `I(Wc; Yo) ≠ ∞`, we have

```
I(Xs; Yo | Wc) ≤ I(Zc; Yo | Wc).
```

This is the natural conditional generalization of `mutualInfo_le_of_markov`. The single
Markov chain `Xs → Zc → Yo` alone is not sufficient — `Wc` may break the Markov property
unless it is also conditionally compatible, hence the augmented form. The finiteness
`I(Wc; Yo) ≠ ∞` is needed to cancel the common term after the chain rule. -/
@[entry_point]
theorem condMutualInfo_le_of_markov_joint
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (Wc : Ω → W)
    (hXs : Measurable Xs) (hZc : Measurable Zc)
    (hYo : Measurable Yo) (hWc : Measurable Wc)
    (hmarkov :
      Shannon.IsMarkovChain μ
        (fun ω ↦ (Wc ω, Xs ω)) (fun ω ↦ (Wc ω, Zc ω)) Yo)
    (hWcYo_fin : Shannon.mutualInfo μ Wc Yo ≠ ∞) :
    Shannon.condMutualInfo μ Xs Yo Wc ≤ Shannon.condMutualInfo μ Zc Yo Wc := by
  have hWX : Measurable (fun ω ↦ (Wc ω, Xs ω)) := hWc.prodMk hXs
  have hWZ : Measurable (fun ω ↦ (Wc ω, Zc ω)) := hWc.prodMk hZc
  -- Chain rule for Xs: I((Wc, Xs); Yo) = I(Wc; Yo) + I(Xs; Yo | Wc).
  have h_chain_X :
      Shannon.mutualInfo μ (fun ω ↦ (Wc ω, Xs ω)) Yo
        = Shannon.mutualInfo μ Wc Yo + Shannon.condMutualInfo μ Xs Yo Wc :=
    Shannon.mutualInfo_chain_rule μ Xs Yo Wc hXs hYo hWc
  -- Chain rule for Zc: I((Wc, Zc); Yo) = I(Wc; Yo) + I(Zc; Yo | Wc).
  have h_chain_Z :
      Shannon.mutualInfo μ (fun ω ↦ (Wc ω, Zc ω)) Yo
        = Shannon.mutualInfo μ Wc Yo + Shannon.condMutualInfo μ Zc Yo Wc :=
    Shannon.mutualInfo_chain_rule μ Zc Yo Wc hZc hYo hWc
  -- Augmented Markov ⇒ I((Wc, Xs); Yo) ≤ I((Wc, Zc); Yo).
  have h_aug :
      Shannon.mutualInfo μ (fun ω ↦ (Wc ω, Xs ω)) Yo
        ≤ Shannon.mutualInfo μ (fun ω ↦ (Wc ω, Zc ω)) Yo :=
    Shannon.mutualInfo_le_of_markov μ
      (fun ω ↦ (Wc ω, Xs ω)) (fun ω ↦ (Wc ω, Zc ω)) Yo
      hWX hWZ hYo hmarkov
  -- Rewrite and cancel I(Wc; Yo).
  rw [h_chain_X, h_chain_Z] at h_aug
  exact (ENNReal.add_le_add_iff_left hWcYo_fin).mp h_aug

end CondMIAuxiliary

section CondChainRule2Var

variable {X X' Y W : Type*}
  [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X']
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableSpace W] [StandardBorelSpace W] [Nonempty W]

omit [StandardBorelSpace W] [Nonempty W] in
/-- 2-variable X-axis conditional chain rule for `condMutualInfo`.

```
I((X, X'); Y | Wc) = I(X; Y | Wc) + I(X'; Y | (Wc, X))
```

Derived from three applications of the bare 2-variable chain rule
`mutualInfo_chain_rule` together with a `prodAssoc` reshape on the left, then
cancellation of the common term `I(Wc; Y)` (requires `I(Wc; Y) ≠ ∞`). -/
theorem condMutualInfo_chain_rule_X_2var
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X_RV : Ω → X) (X'_RV : Ω → X') (Yo : Ω → Y) (Wc : Ω → W)
    (hX : Measurable X_RV) (hX' : Measurable X'_RV)
    (hYo : Measurable Yo) (hWc : Measurable Wc)
    (hWcY_fin : Shannon.mutualInfo μ Wc Yo ≠ ∞) :
    Shannon.condMutualInfo μ (fun ω ↦ (X_RV ω, X'_RV ω)) Yo Wc
      = Shannon.condMutualInfo μ X_RV Yo Wc
        + Shannon.condMutualInfo μ X'_RV Yo (fun ω ↦ (Wc ω, X_RV ω)) := by
  have hXX' : Measurable (fun ω ↦ (X_RV ω, X'_RV ω)) := hX.prodMk hX'
  have hWX : Measurable (fun ω ↦ (Wc ω, X_RV ω)) := hWc.prodMk hX
  -- Step (A): I((Wc, (X, X')); Y) = I(Wc; Y) + condMI (X, X') Y Wc.
  have hA :
      Shannon.mutualInfo μ (fun ω ↦ (Wc ω, X_RV ω, X'_RV ω)) Yo
        = Shannon.mutualInfo μ Wc Yo
          + Shannon.condMutualInfo μ (fun ω ↦ (X_RV ω, X'_RV ω)) Yo Wc :=
    Shannon.mutualInfo_chain_rule μ (fun ω ↦ (X_RV ω, X'_RV ω)) Yo Wc hXX' hYo hWc
  -- Step (B): Reshape (Wc, (X, X')) ↔ ((Wc, X), X') via prodAssoc.
  -- prodAssoc : (Wc × X) × X' ≃ᵐ Wc × (X × X')
  -- so prodAssoc.symm : Wc × (X × X') → (Wc × X) × X'.
  let eAssoc : W × (X × X') ≃ᵐ (W × X) × X' :=
    (MeasurableEquiv.prodAssoc (α := W) (β := X) (γ := X')).symm
  have h_eAssoc_apply : ∀ ω,
      eAssoc (Wc ω, X_RV ω, X'_RV ω) = ((Wc ω, X_RV ω), X'_RV ω) := fun _ ↦ rfl
  have h_reshape :
      Shannon.mutualInfo μ
          (fun ω ↦ ((Wc ω, X_RV ω), X'_RV ω)) Yo
        = Shannon.mutualInfo μ (fun ω ↦ (Wc ω, X_RV ω, X'_RV ω)) Yo := by
    have h_RV_meas : Measurable (fun ω ↦ (Wc ω, X_RV ω, X'_RV ω)) :=
      hWc.prodMk hXX'
    have hMap :
        Shannon.mutualInfo μ
            (fun ω ↦ eAssoc (Wc ω, X_RV ω, X'_RV ω)) Yo
          = Shannon.mutualInfo μ (fun ω ↦ (Wc ω, X_RV ω, X'_RV ω)) Yo :=
      Shannon.mutualInfo_map_left_measurableEquiv μ
        (fun ω ↦ (Wc ω, X_RV ω, X'_RV ω)) Yo h_RV_meas hYo eAssoc
    -- The two sides are pointwise-equal as functions of ω.
    have : (fun ω ↦ eAssoc (Wc ω, X_RV ω, X'_RV ω))
        = (fun ω ↦ ((Wc ω, X_RV ω), X'_RV ω)) := funext h_eAssoc_apply
    rw [this] at hMap
    exact hMap
  -- Step (C): I(((Wc, X), X'); Y) = I((Wc, X); Y) + condMI X' Y (Wc, X).
  have hC :
      Shannon.mutualInfo μ (fun ω ↦ ((Wc ω, X_RV ω), X'_RV ω)) Yo
        = Shannon.mutualInfo μ (fun ω ↦ (Wc ω, X_RV ω)) Yo
          + Shannon.condMutualInfo μ X'_RV Yo (fun ω ↦ (Wc ω, X_RV ω)) :=
    Shannon.mutualInfo_chain_rule μ X'_RV Yo (fun ω ↦ (Wc ω, X_RV ω))
      hX' hYo hWX
  -- Step (D): I((Wc, X); Y) = I(Wc; Y) + condMI X Y Wc.
  have hD :
      Shannon.mutualInfo μ (fun ω ↦ (Wc ω, X_RV ω)) Yo
        = Shannon.mutualInfo μ Wc Yo + Shannon.condMutualInfo μ X_RV Yo Wc :=
    Shannon.mutualInfo_chain_rule μ X_RV Yo Wc hX hYo hWc
  -- Combine: chain reshape + C + D gives the same LHS as A.
  rw [hD] at hC
  -- hC: I(((Wc, X), X'); Y) = (I(Wc; Y) + condMI X Y Wc) + condMI X' Y (Wc, X)
  rw [h_reshape] at hC
  -- hC: I((Wc, (X, X')); Y) = I(Wc; Y) + condMI X Y Wc + condMI X' Y (Wc, X)
  rw [hA] at hC
  -- hC: I(Wc; Y) + condMI (X, X') Y Wc
  --   = I(Wc; Y) + condMI X Y Wc + condMI X' Y (Wc, X)
  -- Cancel I(Wc; Y) from both sides.
  have hC' :
      Shannon.mutualInfo μ Wc Yo
          + Shannon.condMutualInfo μ (fun ω ↦ (X_RV ω, X'_RV ω)) Yo Wc
        = Shannon.mutualInfo μ Wc Yo
          + (Shannon.condMutualInfo μ X_RV Yo Wc
            + Shannon.condMutualInfo μ X'_RV Yo (fun ω ↦ (Wc ω, X_RV ω))) := by
    rw [← add_assoc]; exact hC
  exact WithTop.add_left_cancel hWcY_fin hC'

omit [StandardBorelSpace W] [Nonempty W] in
/-- 2-variable Y-axis conditional chain rule for `condMutualInfo`.

```
I(X; (A, B) | Wc) = I(X; A | Wc) + I(X; B | (Wc, A))
```

Derived from the X-axis 2-var conditional chain rule by `condMutualInfo_comm`.
Requires `I(Wc; X) ≠ ∞` (post-comm: the "Y" of the X-axis becomes the original `X`). -/
theorem condMutualInfo_chain_rule_Y_2var
    {α' β' : Type*}
    [MeasurableSpace α'] [StandardBorelSpace α'] [Nonempty α']
    [MeasurableSpace β'] [StandardBorelSpace β'] [Nonempty β']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X_RV : Ω → X) (A : Ω → α') (B : Ω → β') (Wc : Ω → W)
    (hX : Measurable X_RV) (hA : Measurable A)
    (hB : Measurable B) (hWc : Measurable Wc)
    (hWcX_fin : Shannon.mutualInfo μ Wc X_RV ≠ ∞) :
    Shannon.condMutualInfo μ X_RV (fun ω ↦ (A ω, B ω)) Wc
      = Shannon.condMutualInfo μ X_RV A Wc
        + Shannon.condMutualInfo μ X_RV B (fun ω ↦ (Wc ω, A ω)) := by
  have hAB : Measurable (fun ω ↦ (A ω, B ω)) := hA.prodMk hB
  have hWA : Measurable (fun ω ↦ (Wc ω, A ω)) := hWc.prodMk hA
  -- LHS: condMI X (A,B) Wc = condMI (A,B) X Wc (by comm).
  rw [Shannon.condMutualInfo_comm μ X_RV (fun ω ↦ (A ω, B ω)) Wc hX hAB hWc]
  -- Term 1: condMI X A Wc = condMI A X Wc.
  rw [Shannon.condMutualInfo_comm μ X_RV A Wc hX hA hWc]
  -- Term 2: condMI X B (Wc, A) = condMI B X (Wc, A).
  rw [Shannon.condMutualInfo_comm μ X_RV B (fun ω ↦ (Wc ω, A ω)) hX hB hWA]
  -- Now reduce to X-axis 2-var.
  exact condMutualInfo_chain_rule_X_2var μ A B X_RV Wc hA hB hX hWc hWcX_fin

end CondChainRule2Var



end InformationTheory.Shannon.ChannelCodingConverseGeneral
