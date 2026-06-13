import InformationTheory.Draft.Shannon.ChannelCodingConverseGeneralComplete
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.CondEntropyMemoryless
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Channel coding converse — strong memoryless DMC variant

## Main definitions

* `IsMemorylessChannelStrong`: two Markov axioms characterizing a strongly memoryless DMC:
  per-letter `X^n → X_i → Y_i` and output conditional independence `Y^{≠i} → X^n → Y_i`.
* `measurableEquivExtract i`: measurable equivalence `Fin n → β ≃ᵐ β × ({j // j ≠ i} → β)`.

## Main statements

* `h_markov_xprefix_of_strong`: augmented prefix Markov chain from `IsMemorylessChannelStrong`.
* `h_split_of_strong`: conditional mutual information two-variable chain rule reshape.
* `channel_coding_converse_general_memoryless_strong`: Cover-Thomas Thm 7.9 converse
  via entropy subadditivity, yielding `log |M| ≤ ∑ I(X_i; Y_i).toReal + Fano`.

## Implementation notes

The D-2' hypothesis `h_yother_zero : condMI X_i Y^{≠i} (Xprefix, Y_i) = 0` fails for
arbitrary encoders (counterexample: n = 2, i = 0, `X_1 := X_0`). The proof therefore
takes the entropy-subadditivity route (`mutualInfo_le_sum_per_letter_of_memoryless_strong`),
which holds for any encoder and bypasses `h_yother_zero`. The lemmas `h_markov_xprefix_of_strong`
and `h_split_of_strong` are not called in the main proof but are retained for potential future use.
-/

namespace InformationTheory.Shannon.ChannelCodingConverseGeneral

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Strong memoryless predicate -/

section StrongMemoryless

variable {n : ℕ}
variable {α : Type*} [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
variable {β : Type*} [MeasurableSpace β] [Nonempty β] [StandardBorelSpace β]

/-- **Strong memoryless DMC predicate** (two Markov axioms):

* `per_letter_markov`: for each `i`, `X^n → X_i → Y_i` (per-letter channel).
* `outputs_cond_indep`: for each `i`, `Y^{≠i} → X^n → Y_i` (outputs conditionally
  independent given the full input). -/
structure IsMemorylessChannelStrong (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) : Prop where
  /-- Per-letter Markov: `Y_i` depends on `X^n` only through `X_i`. -/
  per_letter_markov : ∀ i : Fin n,
    Shannon.IsMarkovChain μ (fun ω j => Xs j ω) (Xs i) (Ys i)
  /-- Outputs are conditionally independent across `i` given the full input `X^n`. -/
  outputs_cond_indep : ∀ i : Fin n,
    Shannon.IsMarkovChain μ
      (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
      (fun ω j => Xs j ω)
      (Ys i)

end StrongMemoryless

/-! ## MeasurableEquiv plumbing -/

section MeasurableEquivPlumbing

variable {n : ℕ}
variable {β : Type*} [MeasurableSpace β]

/-- `Fin n → β ≃ᵐ β × ({j : Fin n // j ≠ i} → β)`: extracts the `i`-th component
and pairs it with the rest.

Uses `MeasurableEquiv.piEquivPiSubtypeProd` followed by `MeasurableEquiv.funUnique`
to collapse `{j // j = i} → β` to `β`. -/
noncomputable def measurableEquivExtract (i : Fin n) :
    (Fin n → β) ≃ᵐ β × ({j : Fin n // j ≠ i} → β) :=
  -- (∀ j, β) ≃ᵐ ({j // j = i} → β) × ({j // j ≠ i} → β)
  (MeasurableEquiv.piEquivPiSubtypeProd (π := fun _ : Fin n => β) (fun j => j = i)).trans
    -- collapse {j // j = i} → β to β
    ((MeasurableEquiv.funUnique {j : Fin n // j = i} β).prodCongr (.refl _))

end MeasurableEquivPlumbing

/-! ## Discharge lemmas -/

section Discharge

variable {n : ℕ}
variable {α : Type*} [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
variable {β : Type*} [MeasurableSpace β] [Nonempty β] [StandardBorelSpace β]

/-- Augmented prefix Markov chain `(X^{<i}, X_i) → X_i → Y_i` derived from
`IsMemorylessChannelStrong.per_letter_markov` via `isMarkovChain_map_left`. -/
@[entry_point]
lemma h_markov_xprefix_of_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_strong : IsMemorylessChannelStrong μ Xs Ys) :
    ∀ i : Fin n,
      Shannon.IsMarkovChain μ
        (fun ω => (
          (fun (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω),
          Xs i ω))
        (Xs i) (Ys i) := by
  intro i
  -- Post-process the full input X^n: extract (Xprefix, X_i).
  have h_full_meas : Measurable (fun ω j => Xs j ω) := measurable_pi_iff.mpr hXs
  have hf : Measurable
      (fun (x : Fin n → α) =>
        ((fun (j : Fin i.val) => x ⟨j.val, j.isLt.trans i.isLt⟩), x i)) := by
    refine Measurable.prodMk ?_ (measurable_pi_apply _)
    exact measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
  exact Shannon.isMarkovChain_map_left
    μ (fun ω j => Xs j ω) (Xs i) (Ys i)
    h_full_meas (hXs i) (hYs i) hf (h_strong.per_letter_markov i)

/-- Conditional mutual information reshape (independent of memorylessness):
`condMI X_i Y^n Xprefix = condMI X_i Y_i Xprefix + condMI X_i Y^{≠i} (Xprefix, Y_i)`.

Reshapes `Y^n` to `(Y_i, Y^{≠i})` via `condMutualInfo_map_middle_measurableEquiv`,
then applies `condMutualInfo_chain_rule_Y_2var`. -/
@[entry_point]
lemma h_split_of_strong
    [Fintype α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i)) :
    ∀ i : Fin n,
      Shannon.condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
          (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        = Shannon.condMutualInfo μ (Xs i) (Ys i)
            (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          + Shannon.condMutualInfo μ (Xs i)
              (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
              (fun ω => (
                (fun (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω),
                Ys i ω)) := by
  intro i
  -- Set up the prefix RV.
  set Xprefix : Ω → (Fin i.val → α) :=
    fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω with hXprefix_def
  have hXprefix : Measurable Xprefix :=
    measurable_pi_iff.mpr (fun j => hXs ⟨j.val, j.isLt.trans i.isLt⟩)
  have hYall : Measurable (fun ω (j : Fin n) => Ys j ω) :=
    measurable_pi_iff.mpr hYs
  have hYother : Measurable
      (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω) :=
    measurable_pi_iff.mpr (fun j => hYs j.val)
  -- Reshape Y^n via the measurable equiv (Y^n ≃ᵐ Y_i × Y^{≠i}).
  -- Define the equiv's symm so post-composing on (Y_i, Y^{≠i}) gives Y^n.
  let e : (Fin n → β) ≃ᵐ β × ({j : Fin n // j ≠ i} → β) :=
    measurableEquivExtract (β := β) i
  -- LHS of split: rewrite Y^n as e.symm (Y_i, Y^{≠i}).
  have h_pointwise : ∀ ω,
      e.symm (Ys i ω, fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
        = (fun j => Ys j ω) := by
    intro ω
    -- e is piEquivPiSubtypeProd ∘ funUnique on first factor.
    -- e.symm collapses (β × ({j // j ≠ i} → β)) back to (Fin n → β):
    --   if j = i, returns Ys i ω; else returns Ys j ω.
    -- We verify by `funext`.
    funext j
    by_cases hj : j = i
    · -- j = i case
      subst hj
      simp [e, measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.trans, MeasurableEquiv.prodCongr]
    · -- j ≠ i case
      simp [e, measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.trans, MeasurableEquiv.prodCongr, hj]
  -- Pair RV: Measurable.
  have hYpair : Measurable
      (fun ω => (Ys i ω, fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω)) :=
    (hYs i).prodMk hYother
  -- Step A: rewrite Y^n via e.symm.
  have hLHS_eq :
      Shannon.condMutualInfo μ (Xs i) (fun ω j => Ys j ω) Xprefix
        = Shannon.condMutualInfo μ (Xs i)
            (fun ω => e.symm
              (Ys i ω, fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω))
            Xprefix := by
    congr 1
    funext ω
    exact (h_pointwise ω).symm
  rw [hLHS_eq]
  -- Step B: peel off e.symm via condMutualInfo_map_middle_measurableEquiv.
  -- Note: signature is condMutualInfo_map_middle_measurableEquiv μ Xs Yo Zc hXs hYo hZc e.
  rw [Shannon.condMutualInfo_map_middle_measurableEquiv μ
      (Xs i)
      (fun ω => (Ys i ω, fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω))
      Xprefix (hXs i) hYpair hXprefix e.symm]
  -- Step C: 2-var Y-axis chain rule.
  -- Need finiteness side condition: I(Xprefix; X_i) ≠ ∞ (finite alphabet).
  have h_fin : Shannon.mutualInfo μ Xprefix (Xs i) ≠ ∞ :=
    Shannon.mutualInfo_ne_top μ Xprefix (Xs i) hXprefix (hXs i)
  exact condMutualInfo_chain_rule_Y_2var μ (Xs i) (Ys i)
    (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω) Xprefix
    (hXs i) (hYs i) hYother hXprefix h_fin

/- **Architectural note**: an earlier session attempted to derive the D-2'
hypothesis `h_yother_zero : condMI X_i Y^{≠i} (Xprefix, Y_i) = 0` from
`IsMemorylessChannelStrong`. A counterexample (n = 2, i = 0, X_1 := X_0
degenerate encoder + iid Bernoulli(1/4) noise) showed the claim is **false**
under arbitrary encoders — the joint distribution of `(X_i, X^{≠i})` is
unconstrained, so `Y^{≠i} ⊥/ X_i | Y_i` in general.

The fix is the entropy-subadditivity route of Cover-Thomas Thm 7.9
(see `mutualInfo_le_sum_per_letter_of_memoryless_strong` in the next section,
backed by `InformationTheory/Shannon/CondEntropyMemoryless.lean`), which bypasses
`h_yother_zero` entirely and works for any encoder. -/

end Discharge

/-! ## Main converse theorem — strong memoryless form -/

section MainConverseStrong

variable {n : ℕ}
variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M] [StandardBorelSpace M]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

omit [DecidableEq M] [DecidableEq α] [DecidableEq β] in
/-- **Channel coding converse, strong memoryless DMC (Cover-Thomas Thm 7.9)**:
under `IsMemorylessChannelStrong`,
`log |M| ≤ ∑ I(X_i; Y_i).toReal + h(Pe) + Pe · log(|M| - 1)`.

The proof combines the single-shot Markov-encoder converse with
`mutualInfo_le_sum_per_letter_of_memoryless_strong` (entropy subadditivity route).
The argument `_h_memo : IsMemorylessChannel` is unused in the current proof but
retained for API compatibility. -/
@[entry_point]
theorem channel_coding_converse_general_memoryless_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : Shannon.IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (_h_memo : IsMemorylessChannel μ (fun i ω => encoder (Msg ω) i) Ys)
    (h_strong : IsMemorylessChannelStrong μ
      (fun i ω => encoder (Msg ω) i) Ys)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : Shannon.mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (∑ i : Fin n,
        (Shannon.mutualInfo μ
          (fun ω => encoder (Msg ω) i) (Ys i)).toReal) +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1) := by
  classical
  -- Set up per-letter and joint X RVs.
  set Xs : Fin n → Ω → α := fun i ω => encoder (Msg ω) i with hXs_def
  have h_encoder : Measurable encoder := measurable_of_countable _
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i =>
    (measurable_pi_apply i).comp (h_encoder.comp hMsg)
  have hY_pi : Measurable (fun ω (i : Fin n) => Ys i ω) :=
    measurable_pi_iff.mpr hYs
  -- Step 1: single-shot Markov-encoder converse on (X = Fin n → α, Y = Fin n → β).
  have h_single :=
    Shannon.shannon_converse_single_shot_markov_encoder (X := Fin n → α)
      μ Msg encoder (fun ω i => Ys i ω) decoder
      hMsg hY_pi h_encoder hdecoder hmarkov hMsg_uniform hcard hMI_finite
  -- Normalize `(encoder ∘ Msg)` to `fun ω => encoder (Msg ω)`.
  rw [show (encoder ∘ Msg) = fun ω => encoder (Msg ω) from rfl] at h_single
  -- Step 2: Cover-Thomas Thm 7.9 — per-letter MI bound.
  -- `fun ω => encoder (Msg ω) = fun ω j => Xs j ω` (definitional).
  have h_pi_eq : (fun ω => encoder (Msg ω)) = (fun ω j => Xs j ω) := by
    funext ω j; rfl
  rw [h_pi_eq] at h_single
  have h_per_letter :=
    Shannon.mutualInfo_le_sum_per_letter_of_memoryless_strong μ Xs Ys hXs_meas hYs
      h_strong.per_letter_markov h_strong.outputs_cond_indep
  -- Combine: log |M| ≤ I(X^n; Y^n).toReal + Fano ≤ ∑ I(X_i; Y_i).toReal + Fano.
  linarith

end MainConverseStrong

end InformationTheory.Shannon.ChannelCodingConverseGeneral
