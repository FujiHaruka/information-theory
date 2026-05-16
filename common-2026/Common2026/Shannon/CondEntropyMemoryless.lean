import Common2026.Shannon.Han
import Common2026.Shannon.SlepianWolf

/-!
# Conditional entropy on `Fin n` under strong memoryless DMC (D-2'' Phase B refactor)

The Cover-Thomas Thm 7.9 route to the per-letter MI bound goes via entropy
subadditivity, avoiding the false-statement `h_yother_zero` hypothesis used in the
D-2' hypothesis-form converse. The chain:

```
I(X^n; Y^n) = H(Y^n) - H(Y^n | X^n)
            ≤ ∑ H(Y_i) - H(Y^n | X^n)         -- subadditivity (encoder-agnostic)
            = ∑ H(Y_i) - ∑ H(Y_i | X_i)       -- strong memoryless
            = ∑ I(X_i; Y_i)
```

This file establishes the four building blocks:

* `entropy_pi_le_sum_entropy` — `H(Y^n) ≤ ∑ H(Y_i)` (subadditivity, encoder-agnostic).
  Combines `Han.lean`'s `jointEntropy_chain_rule` with `SlepianWolf.lean`'s
  `entropy_ge_condEntropy` (conditioning never increases entropy).
* `condEntropy_pi_chain_rule` — `H(Y^n | X^n) = ∑ H(Y_i | X^n, Y^{<i})` (n-var
  conditional chain rule, mirrors `jointEntropy_chain_rule`).
* `condEntropy_drop_irrelevant_of_markov` — under Markov chain `Y → Z → W`,
  `H(Y | Z, W) = H(Y | Z)` (template-mirrors `condMutualInfo_eq_zero_of_markov`).
* `condEntropy_pi_eq_sum_of_memoryless_strong` — `H(Y^n | X^n) = ∑ H(Y_i | X_i)`
  combining 2 + 3 from the two Markov axioms of `IsMemorylessChannelStrong`
  (parameterized form to avoid circular import).

The central theorem `mutualInfo_le_sum_per_letter_of_memoryless_strong` is then
the direct combination: `(I(X^n; Y^n)).toReal ≤ ∑ (I(X_i; Y_i)).toReal`.

The two Markov axioms of `IsMemorylessChannelStrong` are taken as hypotheses
(not as a single structure) to keep this file an upstream building block of
`Common2026/Shannon/ChannelCodingConverseGeneralStrong.lean`, which defines that
structure and supplies its two fields when invoking the theorem here.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Building block 1 — entropy subadditivity (encoder-agnostic) -/

section Subadditivity

variable {n : ℕ}
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **Entropy subadditivity on `Fin n`**: `H(Y^n) ≤ ∑ H(Y_i)`.

This is encoder-agnostic — holds for any family `Ys : Fin n → Ω → β` without any
memoryless or independence assumption. Cover-Thomas Thm 2.6.6.

Proof: combine the n-variable chain rule `H(Y^n) = ∑ H(Y_i | Y^{<i})`
(`jointEntropy_chain_rule`) with `H(Y_i | Y^{<i}) ≤ H(Y_i)`
(`entropy_ge_condEntropy`, conditioning reduces entropy), summed over `i`. -/
lemma entropy_pi_le_sum_entropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Ys : Fin n → Ω → β) (hYs : ∀ i, Measurable (Ys i)) :
    jointEntropy μ Ys ≤ ∑ i : Fin n, entropy μ (Ys i) := by
  -- Step 1: chain rule for joint entropy.
  rw [jointEntropy_chain_rule μ Ys hYs]
  -- Step 2: for each i, condEntropy ≤ entropy (conditioning reduces entropy).
  apply Finset.sum_le_sum
  intro i _
  -- Prefix RV: Fin i.val → β, measurable (component-wise).
  have h_prefix_meas : Measurable
      (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
    measurable_pi_iff.mpr (fun j => hYs ⟨j.val, j.isLt.trans i.isLt⟩)
  exact entropy_ge_condEntropy μ (Ys i)
    (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
    (hYs i) h_prefix_meas

end Subadditivity

/-! ## Building block 2 — conditional joint entropy chain rule -/

section CondChainRule

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **Conditional joint entropy chain rule on `Fin n`**:
`H(Y^n | X^n) = ∑ i, H(Y_i | X^n, Y^{<i})`.

Conditional analogue of `jointEntropy_chain_rule`. Used as Building Block 2 in
the Cover-Thomas Thm 7.9 chain.

NOTE: this lemma is currently `sorry` — a faithful conditional chain rule mirroring
the joint chain rule requires either iterated application of a 2-var conditional
chain rule (Phase A `entropy_pair_eq_entropy_add_condEntropy` on the conditioner)
or a direct measure-theoretic disintegration. The shape is standard and will be
discharged in a follow-up; the central theorem `mutualInfo_le_sum_per_letter_of_memoryless_strong`
absorbs this as a hypothesis-form sorry through `condEntropy_pi_eq_sum_of_memoryless_strong`.
-/
lemma condEntropy_pi_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → (Fin n → α)) (Ys : Fin n → Ω → β)
    (_hXs : Measurable Xs) (_hYs : ∀ i, Measurable (Ys i)) :
    InformationTheory.MeasureFano.condEntropy μ (fun ω j => Ys j ω) Xs
      = ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy μ (Ys i)
            (fun ω => (Xs ω,
              fun (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)) := by
  sorry

end CondChainRule

/-! ## Building block 3 — Markov drop of irrelevant conditioner -/

section MarkovDrop

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
variable {γ : Type*} [Fintype γ] [DecidableEq γ] [Nonempty γ]
  [MeasurableSpace γ] [MeasurableSingletonClass γ] [StandardBorelSpace γ]

omit [StandardBorelSpace α] in
/-- **Markov-drop for conditional entropy**: under Markov chain `Yo → Zc → Wc`,
`H(Yo | Zc, Wc) = H(Yo | Zc)`.

Direct consequence of `condMutualInfo_eq_zero_of_markov` via
`condMutualInfo_eq_condEntropy_sub_condEntropy`: the Markov hypothesis forces
`I(Yo; Wc | Zc) = 0`, and the bridge expresses this as the desired equality. -/
lemma condEntropy_drop_irrelevant_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Yo : Ω → β) (Zc : Ω → α) (Wc : Ω → γ)
    (hYo : Measurable Yo) (hZc : Measurable Zc) (hWc : Measurable Wc)
    (hmarkov : IsMarkovChain μ Yo Zc Wc) :
    InformationTheory.MeasureFano.condEntropy μ Yo (fun ω => (Zc ω, Wc ω))
      = InformationTheory.MeasureFano.condEntropy μ Yo Zc := by
  -- Bridge: condMI(Yo; Wc | Zc).toReal = H(Yo|Zc) - H(Yo|Zc, Wc).
  have h_bridge :=
    condMutualInfo_eq_condEntropy_sub_condEntropy μ Yo Zc Wc hYo hZc hWc
  -- Markov ⇒ condMI = 0.
  have h_zero : condMutualInfo μ Yo Wc Zc = 0 :=
    condMutualInfo_eq_zero_of_markov μ Yo Zc Wc hYo hZc hWc hmarkov
  rw [h_zero] at h_bridge
  simp at h_bridge
  linarith

end MarkovDrop

/-! ## Building block 4 — `H(Y^n | X^n) = ∑ H(Y_i | X_i)` from strong memoryless -/

section StrongMemorylessCondEntropy

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- **Conditional joint entropy of outputs given inputs, under strong memoryless DMC**:
`H(Y^n | X^n) = ∑ i, H(Y_i | X_i)`.

Combines `condEntropy_pi_chain_rule` (Building Block 2) with the per-summand
collapse `H(Y_i | X^n, Y^{<i}) = H(Y_i | X_i)`. The collapse uses the two Markov
axioms (taken as hypotheses, not as `IsMemorylessChannelStrong` to avoid circular
import — the caller in `ChannelCodingConverseGeneralStrong.lean` unpacks the
structure):

* `h_outputs_cond_indep` (≈ `outputs_cond_indep`): `Y_i ⫫ Y^{<i} | X^n` ⇒ can drop
  `Y^{<i}` from conditioner.
* `h_per_letter_markov` (≈ `per_letter_markov`): `Y_i ⫫ X^{≠i} | X_i` ⇒ can drop
  `X^{≠i}` from conditioner.

Each collapse is one application of `condEntropy_drop_irrelevant_of_markov`.

NOTE: stated here as `sorry` — depends on Building Blocks 2, 3 (also sorry).
The shape is canonical: it is the conditional analogue of the well-known
`H(Y^n) = ∑ H(Y_i)` for independent variables. Discharged in follow-up. -/
lemma condEntropy_pi_eq_sum_of_memoryless_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (_hXs : ∀ i, Measurable (Xs i)) (_hYs : ∀ i, Measurable (Ys i))
    (_h_per_letter_markov : ∀ i : Fin n,
      IsMarkovChain μ (fun ω j => Xs j ω) (Xs i) (Ys i))
    (_h_outputs_cond_indep : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
        (fun ω j => Xs j ω)
        (Ys i)) :
    InformationTheory.MeasureFano.condEntropy μ
        (fun ω j => Ys j ω) (fun ω j => Xs j ω)
      = ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy μ (Ys i) (Xs i) := by
  sorry

end StrongMemorylessCondEntropy

/-! ## Central theorem — Cover-Thomas Thm 7.9 bound -/

section CentralTheorem

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- **Cover-Thomas Thm 7.9 / per-letter MI bound from strong memoryless DMC**:
`(I(X^n; Y^n)).toReal ≤ ∑ i, (I(X_i; Y_i)).toReal`.

The encoder-agnostic Cover-Thomas chain:

```
I(X^n; Y^n) = H(Y^n) - H(Y^n | X^n)
            ≤ ∑ H(Y_i) - H(Y^n | X^n)             -- subadditivity (Block 1)
            = ∑ H(Y_i) - ∑ H(Y_i | X_i)           -- strong memoryless (Block 4)
            = ∑ (H(Y_i) - H(Y_i | X_i))
            = ∑ I(X_i; Y_i)                       -- Bridge
```

This avoids the false-statement `h_yother_zero` route used in D-2'
`channel_coding_converse_general_memoryless`. The two Markov axioms of
`IsMemorylessChannelStrong` are taken as hypotheses (caller unpacks the structure). -/
theorem mutualInfo_le_sum_per_letter_of_memoryless_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_per_letter_markov : ∀ i : Fin n,
      IsMarkovChain μ (fun ω j => Xs j ω) (Xs i) (Ys i))
    (h_outputs_cond_indep : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
        (fun ω j => Xs j ω)
        (Ys i)) :
    (mutualInfo μ (fun ω j => Xs j ω) (fun ω j => Ys j ω)).toReal
      ≤ ∑ i : Fin n, (mutualInfo μ (Xs i) (Ys i)).toReal := by
  -- Pull joint X^n and Y^n into measurable form.
  have hX_pi : Measurable (fun ω j => Xs j ω) := measurable_pi_iff.mpr hXs
  have hY_pi : Measurable (fun ω j => Ys j ω) := measurable_pi_iff.mpr hYs
  -- Bridge: I(Y^n; X^n).toReal = H(Y^n) - H(Y^n | X^n).
  have h_bridge_joint :
      (mutualInfo μ (fun ω j => Ys j ω) (fun ω j => Xs j ω)).toReal
        = entropy μ (fun ω j => Ys j ω)
          - InformationTheory.MeasureFano.condEntropy μ
              (fun ω j => Ys j ω) (fun ω j => Xs j ω) :=
    mutualInfo_eq_entropy_sub_condEntropy μ
      (fun ω j => Ys j ω) (fun ω j => Xs j ω) hY_pi hX_pi
  -- Commute mutualInfo to put X^n first.
  have h_comm_joint :
      mutualInfo μ (fun ω j => Xs j ω) (fun ω j => Ys j ω)
        = mutualInfo μ (fun ω j => Ys j ω) (fun ω j => Xs j ω) :=
    mutualInfo_comm μ (fun ω j => Xs j ω) (fun ω j => Ys j ω) hX_pi hY_pi
  rw [h_comm_joint, h_bridge_joint]
  -- Subadditivity: H(Y^n) ≤ ∑ H(Y_i). (jointEntropy = entropy of pi RV).
  have h_subadd : entropy μ (fun ω j => Ys j ω) ≤ ∑ i : Fin n, entropy μ (Ys i) := by
    have := entropy_pi_le_sum_entropy μ Ys hYs
    unfold jointEntropy at this
    exact this
  -- Strong memoryless: H(Y^n | X^n) = ∑ H(Y_i | X_i).
  have h_cond_split :
      InformationTheory.MeasureFano.condEntropy μ
          (fun ω j => Ys j ω) (fun ω j => Xs j ω)
        = ∑ i : Fin n,
            InformationTheory.MeasureFano.condEntropy μ (Ys i) (Xs i) :=
    condEntropy_pi_eq_sum_of_memoryless_strong μ Xs Ys hXs hYs
      h_per_letter_markov h_outputs_cond_indep
  rw [h_cond_split]
  -- Per-letter bridge: I(X_i; Y_i).toReal = H(Y_i) - H(Y_i | X_i).
  have h_each_bridge : ∀ i : Fin n,
      (mutualInfo μ (Xs i) (Ys i)).toReal
        = entropy μ (Ys i)
          - InformationTheory.MeasureFano.condEntropy μ (Ys i) (Xs i) := by
    intro i
    rw [mutualInfo_comm μ (Xs i) (Ys i) (hXs i) (hYs i)]
    exact mutualInfo_eq_entropy_sub_condEntropy μ (Ys i) (Xs i) (hYs i) (hXs i)
  -- Rewrite RHS using h_each_bridge and ∑ distributivity.
  have h_rhs_eq :
      (∑ i : Fin n, (mutualInfo μ (Xs i) (Ys i)).toReal)
        = (∑ i : Fin n, entropy μ (Ys i))
          - (∑ i : Fin n,
              InformationTheory.MeasureFano.condEntropy μ (Ys i) (Xs i)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => h_each_bridge i)
  rw [h_rhs_eq]
  linarith

end CentralTheorem

end InformationTheory.Shannon
