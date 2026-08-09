/-
N18 adversarial independent audit — probes.

Independent re-derivation for the N18 audit. Nothing here calls the audited leg's own probes
(`preflight.lean` / `continuity.lean` / `kill-lines.lean` / `axioms.lean`); the only shared
surface is the in-tree module under audit.

Sections:
* A1 — the four clauses of `IsThm7Law`, isolated.
* A2 — clause 1 is vacuous at `kv = 0`.
* A3 — the binder direction of the three nested levels.
* A4 — `[IsMarkovKernel W]` is necessary: the region is empty for the zero channel.
* A5 — all twenty-five slots vanish on the degenerate law.
* C  — the entropy reduction on a pair-conditioned slot.
-/
import InformationTheory.Shannon.BroadcastChannel.Thm7Region
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel
open InformationTheory.Shannon.BroadcastChannel.Marton

universe u

namespace AuditN18

variable {α β₁ β₂ : Type u} [Fintype α] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [Fintype β₁] [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [Fintype β₂] [MeasurableSpace β₂] [StandardBorelSpace β₂] [Nonempty β₂]

/-! ## A1 — the four clauses, isolated -/

example {kv : Thm7AuxIdx → ℕ} {kJ : ℕ} (W : BCChannel α β₁ β₂)
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) (p : Measure α)
    (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) [IsFiniteMeasure ν]
    (h : IsThm7Law W TJ p ν) :
    ν.map (fun q ↦ (q.2.1, q.2.2.1, q.2.2.2.1)) = (ν.map (fun q ↦ q.2.1)) ⊗ₘ W
      ∧ ν.map (fun q ↦ ((q.2.1, q.2.2.1, q.2.2.2.1), q.2.2.2.2))
          = (ν.map (fun q ↦ (q.2.1, q.2.2.1, q.2.2.2.1))) ⊗ₘ TJ
      ∧ ν.map (fun q ↦ q.2.1) = p :=
  ⟨h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## A2 — clause 1 is vacuous at `kv = 0` -/

example : Fintype.card (bcAuxAlphabet.{u} 0) = 1 := rfl

/-- At `kv = 0` the first clause drops out: `IsThm7Law` is equivalent to its last three
clauses, for every joint law. -/
example {kJ : ℕ} (W : BCChannel α β₁ β₂)
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) (p : Measure α)
    (ν : Measure (Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂)) [IsProbabilityMeasure ν] :
    IsThm7Law W TJ p ν ↔
      (ν.map (fun q ↦ (q.2.1, q.2.2.1, q.2.2.2.1)) = (ν.map (fun q ↦ q.2.1)) ⊗ₘ W
        ∧ ν.map (fun q ↦ ((q.2.1, q.2.2.1, q.2.2.2.1), q.2.2.2.2))
            = (ν.map (fun q ↦ (q.2.1, q.2.2.1, q.2.2.2.1))) ⊗ₘ TJ
        ∧ ν.map (fun q ↦ q.2.1) = p) := by
  constructor
  · rintro ⟨-, h2, h3, h4⟩
    exact ⟨h2, h3, h4⟩
  · rintro ⟨h2, h3, h4⟩
    exact ⟨iCondIndepFun_of_subsingleton_codomain _ (fun _ ↦ by fun_prop) _ _, h2, h3, h4⟩

/-! ## A3 — the binder direction of the three nested levels -/

example (W : BCChannel α β₁ β₂) (R : ℝ × ℝ × ℝ) :
    R ∈ thm7Region W ↔
      ∃ p : ProbabilityMeasure α, ∀ (kJ : ℕ)
        (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)), IsMarkovKernel TJ →
          R ∈ thm7RegionOfAuxReceiver W (p : Measure α) TJ := by
  simp [thm7Region, thm7RegionOfInput, Set.mem_iUnion, Set.mem_iInter]

example (W : BCChannel α β₁ β₂) (p : Measure α) {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) (R : ℝ × ℝ × ℝ) :
    R ∈ thm7RegionOfAuxReceiver W p TJ ↔
      ∃ kv : Thm7AuxIdx → ℕ, (∀ i, kv i < thm7Cap α i) ∧
        ∃ ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂),
          IsThm7Law W TJ p (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) ∧
            R ∈ thm7RegionOfLaw (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) := by
  simp [thm7RegionOfAuxReceiver, Set.mem_iUnion, Prod.forall]

/-! ## A4 — the zero channel gives an empty region -/

omit [Fintype β₁] [Fintype β₂] in
lemma thm7RegionOfAuxReceiver_zero (p : Measure α) {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) :
    thm7RegionOfAuxReceiver (0 : BCChannel α β₁ β₂) p TJ = ∅ := by
  ext R
  simp only [thm7RegionOfAuxReceiver, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false,
    not_exists]
  rintro kv hkv ν hlaw
  exfalso
  have h2 := hlaw.2.1
  rw [Measure.compProd_zero_right] at h2
  haveI : IsProbabilityMeasure
      (((ν : Measure (Thm7Ambient kv kJ α β₁ β₂)).map
        (fun q ↦ (q.2.1, q.2.2.1, q.2.2.2.1)))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have h1 : ((ν : Measure (Thm7Ambient kv kJ α β₁ β₂)).map
      (fun q ↦ (q.2.1, q.2.2.1, q.2.2.2.1))) Set.univ = 1 := measure_univ
  rw [h2] at h1
  simp at h1

omit [Fintype β₁] [Fintype β₂] in
theorem thm7Region_zero_eq_empty : thm7Region (0 : BCChannel α β₁ β₂) = ∅ := by
  ext R
  simp only [thm7Region, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_exists]
  intro p hp
  simp only [thm7RegionOfInput, Set.mem_iInter] at hp
  have h := hp 0 (Kernel.const _ (Measure.dirac (default : bcAuxAlphabet.{u} 0))) inferInstance
  rw [thm7RegionOfAuxReceiver_zero] at h
  exact h

example : ¬ (thm7Region (0 : BCChannel α β₁ β₂)).Nonempty := by
  rw [thm7Region_zero_eq_empty]
  exact Set.not_nonempty_empty

/-- The closedness headline is vacuous on the zero channel. -/
example : IsClosed (thm7Region (0 : BCChannel α β₁ β₂)) := by
  rw [thm7Region_zero_eq_empty]
  exact isClosed_empty

/-! ## A5 — all twenty-five slots vanish -/

example (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α)
    (i : Fin 25) : thm7Slots (thm7DegenerateLaw W TJ x₀) i = 0 := by
  rw [thm7Slots_thm7DegenerateLaw]
  rfl

/-- The witness set of the degenerate law is a whole cone, not the origin alone. -/
example (t : ℝ) (ht : 0 ≤ t) :
    InThm7 (0 : Fin 25 → ℝ) (0, -t, -t) ∧ IsThm7Eligible (0 : Fin 25 → ℝ) := by
  norm_num [InThm7, IsThm7Eligible, ht]

/-! ## C — the entropy reduction on a pair-conditioned slot (slot 15) -/

example {kv : Thm7AuxIdx → ℕ} {kJ : ℕ} (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))
    [IsProbabilityMeasure ν] :
    condMutualInfoReal ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.1)
        (fun q ↦ (q.1 (0, 1), q.1 (0, 2)))
      = InformationTheory.MeasureFano.condEntropy ν (fun q ↦ q.2.1)
          (fun q ↦ (q.1 (0, 1), q.1 (0, 2)))
        - InformationTheory.MeasureFano.condEntropy ν (fun q ↦ q.2.1)
            (fun q ↦ ((q.1 (0, 1), q.1 (0, 2)), q.2.2.1)) :=
  condMutualInfo_eq_condEntropy_sub_condEntropy ν _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)

/-- The conditional entropy of the second step reduces to a difference of two entropies, so a
pair-conditioned slot lands on four entropies. -/
example {kv : Thm7AuxIdx → ℕ} {kJ : ℕ} (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))
    [IsProbabilityMeasure ν] :
    InformationTheory.MeasureFano.condEntropy ν (fun q ↦ q.2.1)
        (fun q ↦ (q.1 (0, 1), q.1 (0, 2)))
      = entropy ν (fun q ↦ ((q.1 (0, 1), q.1 (0, 2)), q.2.1))
        - entropy ν (fun q ↦ (q.1 (0, 1), q.1 (0, 2))) := by
  have h := entropy_pair_eq_entropy_add_condEntropy ν
    (fun q : Thm7Ambient kv kJ α β₁ β₂ ↦ (q.1 (0, 1), q.1 (0, 2)))
    (fun q : Thm7Ambient kv kJ α β₁ β₂ ↦ q.2.1) (by fun_prop) (by fun_prop)
  linarith

/-- The single continuity atom covers pair-valued observables as well, so a slot that
conditions on a pair needs no further atom. -/
example {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [DiscreteTopology Ω]
    [CompactSpace Ω] [OpensMeasurableSpace Ω] {S T : Type*}
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype T] [MeasurableSpace T] [MeasurableSingletonClass T]
    (f : Ω → S) (g : Ω → T) (hf : Measurable f) (hg : Measurable g) :
    Continuous fun ν : ProbabilityMeasure Ω ↦
      entropy (ν : Measure Ω) (fun ω ↦ (f ω, g ω)) :=
  continuous_entropy_of_discrete _ (hf.prodMk hg)

/-! ## The nearest asset to the missing weak-topology step -/

#check @MeasureTheory.ProbabilityMeasure.continuous_map

/-! ## Axioms -/

#print axioms thm7Region_nonempty
#print axioms origin_mem_thm7Region
#print axioms thm7DegenerateLaw_isThm7Law
#print axioms thm7Slots_thm7DegenerateLaw
#print axioms iCondIndepFun_of_subsingleton_codomain
#print axioms continuous_entropy_of_discrete
#print axioms continuous_measureReal_of_discrete
#print axioms isClosed_thm7RegionOfInput
#print axioms isClosed_thm7Region
#print axioms thm7Region_zero_eq_empty

end AuditN18
