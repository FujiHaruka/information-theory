import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.Basic

/-!
# Multiple access channel — three-way jointly typical set

The three-way jointly typical set for a two-user MAC, following the single-user
`InformationTheory.Shannon.ChannelCoding.jointlyTypicalSet` conventions
(Cover–Thomas §15.3.1).

## Design

The single-user typical set `InformationTheory.Shannon.typicalSet` is an
*entropy*-typicality set (empirical entropy within `ε` of the true entropy), not a
strong / letter-typicality set.  Consequently a three-way `(X₁, X₂, Y)`-joint-typical
triple does **not** by itself entail any of the pairwise-typical facts (e.g.
`(X₂, Y)`-pair-typical).  The achievability error analysis needs those pairwise facts to
bound the conditional-fibre masses, so `macJointlyTypicalSet` is defined as the
intersection of **all** the single-axis, pairwise, and three-way typicality conditions.

This shape makes each of the three "one user uses a wrong codeword" reductions a
syntactic instance of the single-user jointly-typical set under regrouping:

* user 1 wrong: `X₁ ⟂ (X₂, Y)` reduces to `jointlyTypicalSet μ X₁s (jointSequence X₂s Ys)`,
* user 2 wrong: `X₂ ⟂ (X₁, Y)` reduces to `jointlyTypicalSet μ X₂s (jointSequence X₁s Ys)`,
* both wrong: `(X₁, X₂) ⟂ Y` reduces to `jointlyTypicalSet μ (jointSequence X₁s X₂s) Ys`.

## Main definitions

* `macJointSequence X₁s X₂s Ys` — the three-way joint sequence `i ω ↦ (X₁s i ω, X₂s i ω, Ys i ω)`.
* `macJointlyTypicalSet μ X₁s X₂s Ys n ε` — the three-way jointly typical set, the
  intersection of the three single-axis, three pairwise, and one three-way typicality
  conditions.
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The three-way joint sequence over the product alphabet `α₁ × α₂ × β`.  Definitionally
equal to `jointSequence X₁s (jointSequence X₂s Ys)` (right-associated nesting). -/
noncomputable def macJointSequence
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β) :
    ℕ → Ω → α₁ × α₂ × β :=
  fun i ω ↦ (X1s i ω, X2s i ω, Ys i ω)

omit [MeasurableSpace Ω]
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma macJointSequence_eq
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β) :
    macJointSequence X1s X2s Ys = jointSequence X1s (jointSequence X2s Ys) := rfl

omit [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
lemma measurable_macJointSequence
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i)) (i : ℕ) :
    Measurable (macJointSequence X1s X2s Ys i) :=
  (hX1s i).prodMk ((hX2s i).prodMk (hYs i))

/-- The three-way jointly typical set `A_ε^n ⊆ (Fin n → α₁) × (Fin n → α₂) × (Fin n → β)`:
triples `(x₁, x₂, y)` that are simultaneously typical along every single axis, every pair
of axes, and the three-way joint axis.  The seven conditions are exactly what the three
achievability error events `E1`/`E2`/`E3` require.

@audit:ok -/
noncomputable def macJointlyTypicalSet
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
  { p |
    (p.1 ∈ InformationTheory.Shannon.typicalSet μ X1s n ε)
    ∧ (p.2.1 ∈ InformationTheory.Shannon.typicalSet μ X2s n ε)
    ∧ (p.2.2 ∈ InformationTheory.Shannon.typicalSet μ Ys n ε)
    ∧ ((fun i ↦ (p.1 i, p.2.1 i)) ∈
        InformationTheory.Shannon.typicalSet μ (jointSequence X1s X2s) n ε)
    ∧ ((fun i ↦ (p.1 i, p.2.2 i)) ∈
        InformationTheory.Shannon.typicalSet μ (jointSequence X1s Ys) n ε)
    ∧ ((fun i ↦ (p.2.1 i, p.2.2 i)) ∈
        InformationTheory.Shannon.typicalSet μ (jointSequence X2s Ys) n ε)
    ∧ ((fun i ↦ (p.1 i, (p.2.1 i, p.2.2 i))) ∈
        InformationTheory.Shannon.typicalSet μ (macJointSequence X1s X2s Ys) n ε) }

omit [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
@[entry_point]
lemma mem_macJointlyTypicalSet_iff
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x1 : Fin n → α₁) (x2 : Fin n → α₂) (y : Fin n → β) :
    (x1, x2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε ↔
      (x1 ∈ InformationTheory.Shannon.typicalSet μ X1s n ε)
      ∧ (x2 ∈ InformationTheory.Shannon.typicalSet μ X2s n ε)
      ∧ (y ∈ InformationTheory.Shannon.typicalSet μ Ys n ε)
      ∧ ((fun i ↦ (x1 i, x2 i)) ∈
          InformationTheory.Shannon.typicalSet μ (jointSequence X1s X2s) n ε)
      ∧ ((fun i ↦ (x1 i, y i)) ∈
          InformationTheory.Shannon.typicalSet μ (jointSequence X1s Ys) n ε)
      ∧ ((fun i ↦ (x2 i, y i)) ∈
          InformationTheory.Shannon.typicalSet μ (jointSequence X2s Ys) n ε)
      ∧ ((fun i ↦ (x1 i, (x2 i, y i))) ∈
          InformationTheory.Shannon.typicalSet μ (macJointSequence X1s X2s Ys) n ε) :=
  Iff.rfl

omit [DecidableEq α₁] [Nonempty α₁]
  [DecidableEq α₂] [Nonempty α₂]
  [DecidableEq β] [Nonempty β] in
theorem measurableSet_macJointlyTypicalSet
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    MeasurableSet (macJointlyTypicalSet μ X1s X2s Ys n ε) :=
  (Set.toFinite _).measurableSet

omit [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
lemma macJointlyTypicalSet_finite
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    (macJointlyTypicalSet μ X1s X2s Ys n ε).Finite := Set.toFinite _

-- Helper: if two events each have measure tending to 1, so does their intersection.
-- (Complement-union bound: P((A ∩ B)ᶜ) ≤ P(Aᶜ) + P(Bᶜ) → 0.)
private theorem measure_inter2_tendsto_one {Ω' : Type*} [MeasurableSpace Ω']
    (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (A B : ℕ → Set Ω')
    (hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n))
    (hA1 : Filter.Tendsto (fun n ↦ μ' (A n)) Filter.atTop (𝓝 1))
    (hB1 : Filter.Tendsto (fun n ↦ μ' (B n)) Filter.atTop (𝓝 1)) :
    Filter.Tendsto (fun n ↦ μ' (A n ∩ B n)) Filter.atTop (𝓝 1) := by
  -- For any measurable E with μ'(E) → 1, the complement → 0.
  have h_bad : ∀ (E : ℕ → Set Ω') (_ : ∀ n, MeasurableSet (E n))
      (_ : Filter.Tendsto (fun n ↦ μ' (E n)) Filter.atTop (𝓝 1)),
      Filter.Tendsto (fun n ↦ μ' ((E n)ᶜ)) Filter.atTop (𝓝 0) := by
    intro E hE h
    have h_id : ∀ n, μ' ((E n)ᶜ) = 1 - μ' (E n) := fun n ↦ by
      rw [measure_compl (hE n) (measure_ne_top μ' _), measure_univ]
    refine Filter.Tendsto.congr (fun n ↦ (h_id n).symm) ?_
    have h_cont : Continuous (fun x : ℝ≥0∞ ↦ (1 : ℝ≥0∞) - x) :=
      ENNReal.continuous_sub_left (by simp)
    have h_step : Filter.Tendsto (fun n ↦ (1 : ℝ≥0∞) - μ' (E n)) Filter.atTop
        (𝓝 ((1 : ℝ≥0∞) - 1)) := h_cont.tendsto _ |>.comp h
    simpa using h_step
  have h_badA := h_bad A hA hA1
  have h_badB := h_bad B hB hB1
  -- Bound μ'((A∩B)ᶜ) by the sum of the two complement measures.
  have h_bound : ∀ n, μ' ((A n ∩ B n)ᶜ) ≤ μ' ((A n)ᶜ) + μ' ((B n)ᶜ) := by
    intro n
    rw [Set.compl_inter]
    exact measure_union_le _ _
  -- The sum of the two complement measures → 0.
  have h_sum : Filter.Tendsto (fun n ↦ μ' ((A n)ᶜ) + μ' ((B n)ᶜ)) Filter.atTop (𝓝 0) := by
    have h_all := h_badA.add h_badB
    simpa using h_all
  -- Squeeze to conclude μ'((A∩B)ᶜ) → 0.
  have h_compl : Filter.Tendsto (fun n ↦ μ' ((A n ∩ B n)ᶜ)) Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_sum (fun n ↦ bot_le) h_bound
  -- μ'(A∩B) = 1 − μ'((A∩B)ᶜ) → 1 − 0 = 1.
  have h_meas : ∀ n, MeasurableSet (A n ∩ B n) := fun n ↦ (hA n).inter (hB n)
  have h_id : ∀ n, μ' (A n ∩ B n) = 1 - μ' ((A n ∩ B n)ᶜ) := fun n ↦ by
    rw [measure_compl (h_meas n) (measure_ne_top μ' _), measure_univ]
    exact (ENNReal.sub_sub_cancel (by simp) prob_le_one).symm
  refine Filter.Tendsto.congr (fun n ↦ (h_id n).symm) ?_
  have h_cont : Continuous (fun x : ℝ≥0∞ ↦ (1 : ℝ≥0∞) - x) :=
    ENNReal.continuous_sub_left (by simp)
  have h_step : Filter.Tendsto (fun n ↦ (1 : ℝ≥0∞) - μ' ((A n ∩ B n)ᶜ))
      Filter.atTop (𝓝 ((1 : ℝ≥0∞) - 0)) := h_cont.tendsto _ |>.comp h_compl
  simpa using h_step

omit [DecidableEq α₁] [Nonempty α₁] [DecidableEq α₂] [Nonempty α₂]
  [DecidableEq β] [Nonempty β] in
/-- Bound (a): three-way joint AEP probability.  The probability that the correct
codeword triple `(X₁ⁿ, X₂ⁿ, Yⁿ)` lies in the three-way jointly typical set tends to `1`.

The seven typicality conditions (three single-axis, three pairwise, one three-way) each
hold with probability tending to `1` by the single-sequence AEP
(`InformationTheory.Shannon.typicalSet_prob_tendsto_one`); their intersection then tends
to `1` by the complement-union bound.  The independence / identical-distribution
hypotheses are stated separately for each of the seven sub-sequences, matching the
single-user `jointlyTypicalSet_prob_tendsto_one` template. -/
@[entry_point]
theorem macJointlyTypicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i))
    (hindep1 : Pairwise fun i j ↦ X1s i ⟂ᵢ[μ] X1s j)
    (hident1 : ∀ i, IdentDistrib (X1s i) (X1s 0) μ μ)
    (hindep2 : Pairwise fun i j ↦ X2s i ⟂ᵢ[μ] X2s j)
    (hident2 : ∀ i, IdentDistrib (X2s i) (X2s 0) μ μ)
    (hindep3 : Pairwise fun i j ↦ Ys i ⟂ᵢ[μ] Ys j)
    (hident3 : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindep4 : Pairwise fun i j ↦
      jointSequence X1s X2s i ⟂ᵢ[μ] jointSequence X1s X2s j)
    (hident4 : ∀ i,
      IdentDistrib (jointSequence X1s X2s i) (jointSequence X1s X2s 0) μ μ)
    (hindep5 : Pairwise fun i j ↦
      jointSequence X1s Ys i ⟂ᵢ[μ] jointSequence X1s Ys j)
    (hident5 : ∀ i,
      IdentDistrib (jointSequence X1s Ys i) (jointSequence X1s Ys 0) μ μ)
    (hindep6 : Pairwise fun i j ↦
      jointSequence X2s Ys i ⟂ᵢ[μ] jointSequence X2s Ys j)
    (hident6 : ∀ i,
      IdentDistrib (jointSequence X2s Ys i) (jointSequence X2s Ys 0) μ μ)
    (hindep7 : Pairwise fun i j ↦
      macJointSequence X1s X2s Ys i ⟂ᵢ[μ] macJointSequence X1s X2s Ys j)
    (hident7 : ∀ i,
      IdentDistrib (macJointSequence X1s X2s Ys i)
        (macJointSequence X1s X2s Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ ↦
        μ {ω | (jointRV X1s n ω, jointRV X2s n ω, jointRV Ys n ω) ∈
                macJointlyTypicalSet μ X1s X2s Ys n ε})
      Filter.atTop
      (𝓝 1) := by
  -- Measurability of the three pairwise and the three-way joint sequences.
  have hX12 : ∀ i, Measurable (jointSequence X1s X2s i) := fun i ↦
    measurable_jointSequence X1s X2s hX1s hX2s i
  have hX1Y : ∀ i, Measurable (jointSequence X1s Ys i) := fun i ↦
    measurable_jointSequence X1s Ys hX1s hYs i
  have hX2Y : ∀ i, Measurable (jointSequence X2s Ys i) := fun i ↦
    measurable_jointSequence X2s Ys hX2s hYs i
  have hZ3 : ∀ i, Measurable (macJointSequence X1s X2s Ys i) := fun i ↦
    measurable_macJointSequence X1s X2s Ys hX1s hX2s hYs i
  -- Each of the seven "good" events has probability tending to 1 (single-sequence AEP).
  have t1 := InformationTheory.Shannon.typicalSet_prob_tendsto_one μ X1s hX1s hindep1 hident1 hε
  have t2 := InformationTheory.Shannon.typicalSet_prob_tendsto_one μ X2s hX2s hindep2 hident2 hε
  have t3 := InformationTheory.Shannon.typicalSet_prob_tendsto_one μ Ys hYs hindep3 hident3 hε
  have t4 := InformationTheory.Shannon.typicalSet_prob_tendsto_one μ (jointSequence X1s X2s)
    hX12 hindep4 hident4 hε
  have t5 := InformationTheory.Shannon.typicalSet_prob_tendsto_one μ (jointSequence X1s Ys)
    hX1Y hindep5 hident5 hε
  have t6 := InformationTheory.Shannon.typicalSet_prob_tendsto_one μ (jointSequence X2s Ys)
    hX2Y hindep6 hident6 hε
  have t7 := InformationTheory.Shannon.typicalSet_prob_tendsto_one μ
    (macJointSequence X1s X2s Ys) hZ3 hindep7 hident7 hε
  -- Each good event is measurable (finite product alphabet).
  have m1 : ∀ n, MeasurableSet {ω | jointRV X1s n ω ∈
      InformationTheory.Shannon.typicalSet μ X1s n ε} := fun n ↦
    (InformationTheory.Shannon.measurable_jointRV X1s hX1s n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ X1s n ε)
  have m2 : ∀ n, MeasurableSet {ω | jointRV X2s n ω ∈
      InformationTheory.Shannon.typicalSet μ X2s n ε} := fun n ↦
    (InformationTheory.Shannon.measurable_jointRV X2s hX2s n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ X2s n ε)
  have m3 : ∀ n, MeasurableSet {ω | jointRV Ys n ω ∈
      InformationTheory.Shannon.typicalSet μ Ys n ε} := fun n ↦
    (InformationTheory.Shannon.measurable_jointRV Ys hYs n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ Ys n ε)
  have m4 : ∀ n, MeasurableSet {ω | jointRV (jointSequence X1s X2s) n ω ∈
      InformationTheory.Shannon.typicalSet μ (jointSequence X1s X2s) n ε} := fun n ↦
    (InformationTheory.Shannon.measurable_jointRV (jointSequence X1s X2s) hX12 n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ (jointSequence X1s X2s) n ε)
  have m5 : ∀ n, MeasurableSet {ω | jointRV (jointSequence X1s Ys) n ω ∈
      InformationTheory.Shannon.typicalSet μ (jointSequence X1s Ys) n ε} := fun n ↦
    (InformationTheory.Shannon.measurable_jointRV (jointSequence X1s Ys) hX1Y n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ (jointSequence X1s Ys) n ε)
  have m6 : ∀ n, MeasurableSet {ω | jointRV (jointSequence X2s Ys) n ω ∈
      InformationTheory.Shannon.typicalSet μ (jointSequence X2s Ys) n ε} := fun n ↦
    (InformationTheory.Shannon.measurable_jointRV (jointSequence X2s Ys) hX2Y n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ (jointSequence X2s Ys) n ε)
  have m7 : ∀ n, MeasurableSet {ω | jointRV (macJointSequence X1s X2s Ys) n ω ∈
      InformationTheory.Shannon.typicalSet μ (macJointSequence X1s X2s Ys) n ε} := fun n ↦
    (InformationTheory.Shannon.measurable_jointRV (macJointSequence X1s X2s Ys) hZ3 n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ (macJointSequence X1s X2s Ys) n ε)
  -- The correct-triple event is the intersection of the seven good events.
  have h_decomp : ∀ n,
      {ω | (jointRV X1s n ω, jointRV X2s n ω, jointRV Ys n ω) ∈
            macJointlyTypicalSet μ X1s X2s Ys n ε}
        = {ω | jointRV X1s n ω ∈ InformationTheory.Shannon.typicalSet μ X1s n ε} ∩
          ({ω | jointRV X2s n ω ∈ InformationTheory.Shannon.typicalSet μ X2s n ε} ∩
          ({ω | jointRV Ys n ω ∈ InformationTheory.Shannon.typicalSet μ Ys n ε} ∩
          ({ω | jointRV (jointSequence X1s X2s) n ω ∈
              InformationTheory.Shannon.typicalSet μ (jointSequence X1s X2s) n ε} ∩
          ({ω | jointRV (jointSequence X1s Ys) n ω ∈
              InformationTheory.Shannon.typicalSet μ (jointSequence X1s Ys) n ε} ∩
          ({ω | jointRV (jointSequence X2s Ys) n ω ∈
              InformationTheory.Shannon.typicalSet μ (jointSequence X2s Ys) n ε} ∩
           {ω | jointRV (macJointSequence X1s X2s Ys) n ω ∈
              InformationTheory.Shannon.typicalSet μ (macJointSequence X1s X2s Ys) n ε}))))) := by
    intro n
    ext ω
    rw [Set.mem_setOf_eq, mem_macJointlyTypicalSet_iff]
    constructor
    · rintro ⟨c1, c2, c3, c4, c5, c6, c7⟩
      exact ⟨c1, c2, c3, c4, c5, c6, c7⟩
    · rintro ⟨c1, c2, c3, c4, c5, c6, c7⟩
      exact ⟨c1, c2, c3, c4, c5, c6, c7⟩
  -- Fold the binary complement-union bound from the inside out.
  have T67 := measure_inter2_tendsto_one μ _ _ m6 m7 t6 t7
  have m67 := fun n ↦ (m6 n).inter (m7 n)
  have T567 := measure_inter2_tendsto_one μ _ _ m5 m67 t5 T67
  have m567 := fun n ↦ (m5 n).inter (m67 n)
  have T4567 := measure_inter2_tendsto_one μ _ _ m4 m567 t4 T567
  have m4567 := fun n ↦ (m4 n).inter (m567 n)
  have T34567 := measure_inter2_tendsto_one μ _ _ m3 m4567 t3 T4567
  have m34567 := fun n ↦ (m3 n).inter (m4567 n)
  have T234567 := measure_inter2_tendsto_one μ _ _ m2 m34567 t2 T34567
  have m234567 := fun n ↦ (m2 n).inter (m34567 n)
  have T1234567 := measure_inter2_tendsto_one μ _ _ m1 m234567 t1 T234567
  exact T1234567.congr (fun n ↦ congrArg μ (h_decomp n).symm)

end InformationTheory.Shannon.MAC
