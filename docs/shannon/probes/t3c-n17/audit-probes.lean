/-
PROBE — not an in-project asset (nothing under `InformationTheory/` imports this file).
Written by the N17 independent honesty audit of `Thm7Region.lean` (commit `d1b78af9`).

It exists to settle, against the compiler, three claims that the N17 self-report
(`docs/shannon/bc-t3c-n17-unit-b.md`) left in prose:

  P1  the constraint system is satisfiable at all (so the closedness of a fiber is not a
      statement about `∅` by accident);
  P2  the binder swap `(ν : Measure _) (hν : IsFiniteMeasure ν)` → `(ν : ProbabilityMeasure _)`
      loses nothing: the fourth clause of `IsThm7Law` already forces the total mass;
  P3  `thm7Region W` contains the origin as soon as one law with vanishing slots exists.

Run:  lake env lean docs/shannon/probes/t3c-n17/audit-probes.lean
-/
import InformationTheory.Shannon.BroadcastChannel.Thm7Region

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel
open InformationTheory.Shannon.BroadcastChannel.Marton

namespace AuditThm7N17

universe u

variable {α β₁ β₂ : Type u} [Fintype α] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [Fintype β₁] [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [Fintype β₂] [MeasurableSpace β₂] [StandardBorelSpace β₂] [Nonempty β₂]

/- P1: the all-zero slot vector is eligible and admits the origin. -/
example : IsThm7Eligible (fun _ ↦ (0 : ℝ)) := by norm_num [IsThm7Eligible]

example : InThm7 (fun _ ↦ (0 : ℝ)) (0, 0, 0) := by norm_num [InThm7]

/- P2: a finite measure obeying `IsThm7Law` over a probability input law is a probability
measure. -/
example {kv : Thm7AuxIdx → ℕ} {kJ : ℕ} (W : BCChannel α β₁ β₂)
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) (p : ProbabilityMeasure α)
    (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) [IsFiniteMeasure ν]
    (h : IsThm7Law W TJ (p : Measure α) ν) : IsProbabilityMeasure ν := by
  have hmeas : Measurable (fun q : Thm7Ambient kv kJ α β₁ β₂ ↦ q.2.1) :=
    measurable_fst.comp measurable_snd
  constructor
  have hmap := h.2.2.2
  have : ν.map (fun q : Thm7Ambient kv kJ α β₁ β₂ ↦ q.2.1) Set.univ = 1 := by
    rw [hmap]; exact measure_univ
  rwa [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ] at this


/- P3: the two binder shapes cut out the same set. The left-hand side is what `Thm7Region.lean`
declares; the right-hand side rebuilds the shape the N2 probe used, over finite measures with the
finiteness bound as an explicit binder. -/
set_option maxHeartbeats 1000000 in
example {kv : Thm7AuxIdx → ℕ} {kJ : ℕ} (W : BCChannel α β₁ β₂)
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) (p : ProbabilityMeasure α) :
    (⋃ (ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂))
        (_ : IsThm7Law W TJ (p : Measure α) (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))),
        thm7RegionOfLaw (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)))
      = ⋃ (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) (hν : IsFiniteMeasure ν)
          (_ : letI := hν; IsThm7Law W TJ (p : Measure α) ν), letI := hν; thm7RegionOfLaw ν := by
  ext R
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨ν, hlaw, hR⟩
    have hfin : IsFiniteMeasure ((ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂)) :
        Measure (Thm7Ambient kv kJ α β₁ β₂)) := inferInstance
    exact ⟨(ν : Measure (Thm7Ambient kv kJ α β₁ β₂)), hfin, hlaw, hR⟩
  · rintro ⟨ν, hν, hlaw, hR⟩
    letI := hν
    have hp : IsProbabilityMeasure ν := by
      have hmeas : Measurable (fun q : Thm7Ambient kv kJ α β₁ β₂ ↦ q.2.1) :=
        measurable_fst.comp measurable_snd
      constructor
      have hmap := hlaw.2.2.2
      have h1 : ν.map (fun q : Thm7Ambient kv kJ α β₁ β₂ ↦ q.2.1) Set.univ = 1 := by
        rw [hmap]; exact measure_univ
      rwa [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ] at h1
    exact ⟨⟨ν, hp⟩, hlaw, hR⟩

/- P4: the region contains the origin as soon as one law with vanishing slots exists, for every
auxiliary receiver. The hypothesis is what a degenerate input law is expected to supply; it is
assumed here, not built. -/
example (W : BCChannel α β₁ β₂) (p : ProbabilityMeasure α)
    (h : ∀ (kJ : ℕ) (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)), IsMarkovKernel TJ →
      ∃ kv : Thm7AuxIdx → ℕ, (∀ i, kv i < thm7Cap α i) ∧
        ∃ ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂),
          IsThm7Law W TJ (p : Measure α) (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) ∧
            thm7Slots (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) = 0) :
    ((0, 0, 0) : ℝ × ℝ × ℝ) ∈ thm7Region W := by
  simp only [thm7Region, Set.mem_iUnion]
  refine ⟨p, ?_⟩
  simp only [thm7RegionOfInput, Set.mem_iInter]
  intro kJ TJ hTJ
  obtain ⟨kv, hkv, ν, hlaw, hs⟩ := h kJ TJ hTJ
  simp only [thm7RegionOfAuxReceiver, Set.mem_iUnion]
  refine ⟨kv, hkv, ν, hlaw, ?_⟩
  simp only [thm7RegionOfLaw, Set.mem_setOf_eq, hs]
  norm_num [InThm7, IsThm7Eligible]

/- N1 (negative, kept as a comment because it does not compile): the fixed-input-law ladder does
not discharge the headline. Verbatim rejection:

  error(lean.synthInstanceFailed): failed to synthesize instance of type class
    AlexandrovDiscrete (ℝ × ℝ × ℝ)

example (W : BCChannel α β₁ β₂) : IsClosed (thm7Region W) := by
  rw [thm7Region]
  exact isClosed_iUnion fun p ↦ isClosed_thm7RegionOfInput W p
-/

end AuditThm7N17
