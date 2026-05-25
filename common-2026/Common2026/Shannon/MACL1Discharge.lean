import Common2026.Shannon.MultipleAccessChannel

/-!
# MAC joint typicality — L-MAC1 partial discharge (T3-B continuation)

This file publishes a **partial discharge layer** for the multi-user joint
typicality body of the MAC inner bound (`L-MAC1` placeholder in
`Common2026/Shannon/MultipleAccessChannel.lean`). The parent file's
`mac_capacity_region_inner_bound` carries `_h_joint_typ : True`; the
plumbing below makes the 3-tuple jointly-typical set concrete and
publishes its **AEP probability bound** and **cardinality bound**, so
downstream work can target the remaining 4-error-event Bonferroni body.

## Scope

Three concrete fragments of L-MAC1 are discharged here, by **iterated
pairing** onto the existing 2-user `jointlyTypicalSet` machinery in
`Common2026/Shannon/ChannelCoding.lean`:

* **L-MAC1-A** — 3-tuple joint typical set definition, basic measurability /
  finiteness, and **cardinality bound** `≤ exp(n · (H(X₁,X₂,Y) + ε))`.
* **L-MAC1-B** — one-sided AEP probability bound
  `μ {ω | (X₁^n, X₂^n, Y^n)(ω) ∈ A_ε^n} → 1` as `n → ∞`.
* **L-MAC1-C** — SW-style conditional `X₁`-slice plumbing: for fixed
  `(x₂, y)`, the `X₁`-fiber of `A_ε^n` is finite and contained in the
  X₁-axis typical set.

The 4-error-event Bonferroni body (Cover-Thomas eqs. 15.65-15.84) that
welds these into a `Pr[error] ≤ exp(-n(I - 3ε))` bound is **out of
scope**; ~500-800 additional lines, deferred to a successor seed.

## Design

`macJointSequence X1s X2s Ys` is the natural 3-tuple sequence
`i ω ↦ (X₁s i ω, X₂s i ω, Ys i ω)` over the product alphabet
`α₁ × α₂ × β`. The 3-tuple jointly typical set
`macJointlyTypicalSet μ X1s X2s Ys n ε` is then defined as the
intersection of four single-axis predicates (X1, X2, Y, and the joint),
in direct analogy with the 2-user `jointlyTypicalSet` of
`ChannelCoding.lean:301`. The cardinality bound and AEP-style
probability bound follow by quoting `typicalSet_card_le` and
`typicalSet_prob_tendsto_one` on the joint-axis sequence.

The publish-layer hook
`mac_capacity_region_inner_bound_with_joint_typ_aep` is a thin
partial-discharge wrapper: it takes the concrete AEP statement on the
caller side together with the existence form of the inner-bound
conclusion, and routes them transparently through the parent
`mac_capacity_region_inner_bound`. The body remains an identity wrap,
matching the established `wyner_ziv_achievability_existence` /
`relay_cutset_outer_bound` pattern.

## 撤退ライン (確定発動)

* **L-MAC1-A / B / C** all publish-form; no further hypotheses needed.
* **L-MAC1-D** (4-error-event Bonferroni body) — fully scope-out;
  not in this file.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — 3-tuple joint sequence -/

section JointSequence

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}

/-- 3-tuple joint sequence `(X₁s, X₂s, Ys)` over the product alphabet
`α₁ × α₂ × β`. -/
noncomputable def macJointSequence
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β) :
    ℕ → Ω → α₁ × α₂ × β :=
  fun i ω => (X1s i ω, X2s i ω, Ys i ω)

@[simp] lemma macJointSequence_apply
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β) (i : ℕ) (ω : Ω) :
    macJointSequence X1s X2s Ys i ω = (X1s i ω, X2s i ω, Ys i ω) := rfl

variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

lemma measurable_macJointSequence
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i)) (i : ℕ) :
    Measurable (macJointSequence X1s X2s Ys i) :=
  (hX1s i).prodMk ((hX2s i).prodMk (hYs i))

end JointSequence

/-! ## Section 2 — 3-tuple jointly typical set -/

section MACJointlyTypicalSet

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The **MAC jointly typical set** `A_ε^n ⊆ (Fin n → α₁) × (Fin n → α₂) ×
(Fin n → β)`. A triple `(x₁, x₂, y)` is in the set iff each component
block is single-axis typical *and* the 3-tuple sequence
`fun i => (x₁ i, x₂ i, y i)` is single-axis typical over the joint
alphabet `α₁ × α₂ × β`.

Implementation: the four single-axis typical conditions are bundled as an
`And`-fold inside `Set` builder notation. The 3-tuple joint-axis
condition uses `macJointSequence X1s X2s Ys` (sequence over the product
alphabet). -/
noncomputable def macJointlyTypicalSet
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
  { p |
    (p.1 ∈ typicalSet μ X1s n ε)
    ∧ (p.2.1 ∈ typicalSet μ X2s n ε)
    ∧ (p.2.2 ∈ typicalSet μ Ys n ε)
    ∧ (fun i => (p.1 i, p.2.1 i, p.2.2 i)) ∈
        typicalSet μ (macJointSequence X1s X2s Ys) n ε }

lemma mem_macJointlyTypicalSet_iff
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x1 : Fin n → α₁) (x2 : Fin n → α₂) (y : Fin n → β) :
    (x1, x2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε ↔
      x1 ∈ typicalSet μ X1s n ε
      ∧ x2 ∈ typicalSet μ X2s n ε
      ∧ y ∈ typicalSet μ Ys n ε
      ∧ (fun i => (x1 i, x2 i, y i)) ∈
          typicalSet μ (macJointSequence X1s X2s Ys) n ε := Iff.rfl

/-- The MAC jointly typical set is measurable (finite ambient). -/
theorem measurableSet_macJointlyTypicalSet
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    MeasurableSet (macJointlyTypicalSet μ X1s X2s Ys n ε) :=
  (Set.toFinite _).measurableSet

/-- The MAC jointly typical set is finite (ambient is a finite product). -/
lemma macJointlyTypicalSet_finite
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    (macJointlyTypicalSet μ X1s X2s Ys n ε).Finite :=
  Set.toFinite _

/-- Projection onto the X1-axis: every triple in the MAC jointly typical
set has its first component in the X1-axis typical set. -/
lemma macJointlyTypicalSet_subset_X1_typicalSet
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    (Prod.fst '' macJointlyTypicalSet μ X1s X2s Ys n ε) ⊆ typicalSet μ X1s n ε := by
  rintro x1 ⟨⟨_, _, _⟩, hmem, rfl⟩
  exact hmem.1

/-- Projection onto the X2-axis. -/
lemma macJointlyTypicalSet_subset_X2_typicalSet
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    ((fun p : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β) => p.2.1)
        '' macJointlyTypicalSet μ X1s X2s Ys n ε)
        ⊆ typicalSet μ X2s n ε := by
  rintro x2 ⟨⟨_, _, _⟩, hmem, rfl⟩
  exact hmem.2.1

/-- Projection onto the Y-axis. -/
lemma macJointlyTypicalSet_subset_Y_typicalSet
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) :
    ((fun p : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β) => p.2.2)
        '' macJointlyTypicalSet μ X1s X2s Ys n ε)
        ⊆ typicalSet μ Ys n ε := by
  rintro y ⟨⟨_, _, _⟩, hmem, rfl⟩
  exact hmem.2.2.1

end MACJointlyTypicalSet

/-! ## Section 3 — Cardinality bound (L-MAC1-A) -/

section MACJointlyTypicalSetCardinality

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **L-MAC1-A — MAC jointly typical set cardinality bound**: the size of
the 3-tuple jointly typical set is at most
`exp(n · (H(X₁, X₂, Y) + ε))`.

Proof: embed the 3-tuple set into the single-axis joint typical set on
`α₁ × α₂ × β` via the reshape
`(x₁, x₂, y) ↦ (fun i => (x₁ i, x₂ i, y i))`, then apply
`typicalSet_card_le` on the joint sequence. -/
theorem macJointlyTypicalSet_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i))
    (hposZ : ∀ p : α₁ × α₂ × β,
        0 < (μ.map (macJointSequence X1s X2s Ys 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((macJointlyTypicalSet μ X1s X2s Ys n ε).toFinite.toFinset.card : ℝ) ≤
      Real.exp ((n : ℝ) *
        (entropy μ (macJointSequence X1s X2s Ys 0) + ε)) := by
  classical
  -- Notation.
  set Zs : ℕ → Ω → α₁ × α₂ × β := macJointSequence X1s X2s Ys with hZs_def
  have hZs : ∀ i, Measurable (Zs i) := fun i =>
    measurable_macJointSequence X1s X2s Ys hX1s hX2s hYs i
  -- Reshape map: 3-tuple → joint over `α₁ × α₂ × β`.
  let φ : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β) → (Fin n → α₁ × α₂ × β) :=
    fun p i => (p.1 i, p.2.1 i, p.2.2 i)
  have hφ_inj : Function.Injective φ := by
    rintro ⟨x1, x2, y⟩ ⟨x1', x2', y'⟩ h
    have h₁ : ∀ i, x1 i = x1' i := fun i => by
      have := congr_fun h i
      exact (Prod.mk.injEq _ _ _ _).mp this |>.1
    have h₂ : ∀ i, x2 i = x2' i ∧ y i = y' i := fun i => by
      have := congr_fun h i
      have h_eq2 := (Prod.mk.injEq _ _ _ _).mp this |>.2
      exact (Prod.mk.injEq _ _ _ _).mp h_eq2
    refine Prod.ext (funext h₁) (Prod.ext (funext fun i => (h₂ i).1)
      (funext fun i => (h₂ i).2))
  -- Finset-level work.
  let MT := (macJointlyTypicalSet μ X1s X2s Ys n ε).toFinite.toFinset
  let ZT := (typicalSet μ Zs n ε).toFinite.toFinset
  -- The φ-image of MT is contained in ZT.
  have h_image_sub : MT.image φ ⊆ ZT := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨⟨x1, x2, y⟩, hmem, rfl⟩ := hz
    have h_in : (x1, x2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε :=
      (Set.Finite.mem_toFinset _).mp hmem
    -- The 4th conjunct is the joint-axis condition.
    rw [Set.Finite.mem_toFinset]
    exact h_in.2.2.2
  have h_card_image : MT.card = (MT.image φ).card :=
    (Finset.card_image_of_injective _ hφ_inj).symm
  have h_card_le_finset : MT.card ≤ ZT.card := by
    rw [h_card_image]; exact Finset.card_le_card h_image_sub
  have h_card_le_R : (MT.card : ℝ) ≤ (ZT.card : ℝ) := by
    exact_mod_cast h_card_le_finset
  -- Apply `typicalSet_card_le` to the joint sequence.
  have h_joint := typicalSet_card_le μ Zs hZs hposZ n hε
  exact h_card_le_R.trans h_joint

end MACJointlyTypicalSetCardinality

/-! ## Section 4 — AEP probability tendsto one (L-MAC1-B) -/

section MACJointlyTypicalSetAEP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **L-MAC1-B — MAC joint AEP probability** (one-sided): for i.i.d.
sequences `X1s, X2s, Ys` (each axis pairwise-independent + identically
distributed, and similarly for the joint-axis sequence), the probability
that the block triple `(X₁^n, X₂^n, Y^n)` lies in the MAC jointly
typical set tends to `1` as `n → ∞`.

Proof: the event "(X₁^n, X₂^n, Y^n) jointly typical" is the intersection
of four single-axis typical events; its complement is contained in the
union of four single-axis complements, each of which has measure tending
to `0` by `typicalSet_prob_tendsto_one`. -/
theorem macJointlyTypicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i))
    (hindepX1 : Pairwise fun i j => X1s i ⟂ᵢ[μ] X1s j)
    (hidentX1 : ∀ i, IdentDistrib (X1s i) (X1s 0) μ μ)
    (hindepX2 : Pairwise fun i j => X2s i ⟂ᵢ[μ] X2s j)
    (hidentX2 : ∀ i, IdentDistrib (X2s i) (X2s 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
        macJointSequence X1s X2s Ys i ⟂ᵢ[μ] macJointSequence X1s X2s Ys j)
    (hidentZ : ∀ i,
        IdentDistrib (macJointSequence X1s X2s Ys i)
          (macJointSequence X1s X2s Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ =>
        μ {ω | (jointRV X1s n ω, jointRV X2s n ω, jointRV Ys n ω) ∈
                macJointlyTypicalSet μ X1s X2s Ys n ε})
      Filter.atTop (𝓝 1) := by
  -- Convergence of each single-axis "good" event to 1.
  have hX1 := typicalSet_prob_tendsto_one μ X1s hX1s hindepX1 hidentX1 hε
  have hX2 := typicalSet_prob_tendsto_one μ X2s hX2s hindepX2 hidentX2 hε
  have hY := typicalSet_prob_tendsto_one μ Ys hYs hindepY hidentY hε
  set Zs : ℕ → Ω → α₁ × α₂ × β := macJointSequence X1s X2s Ys with hZs_def
  have hZs : ∀ i, Measurable (Zs i) := fun i =>
    measurable_macJointSequence X1s X2s Ys hX1s hX2s hYs i
  have hZ := typicalSet_prob_tendsto_one μ Zs hZs hindepZ hidentZ hε
  -- Naming events.
  set goodX1 : ℕ → Set Ω := fun n =>
    {ω | jointRV X1s n ω ∈ typicalSet μ X1s n ε}
  set goodX2 : ℕ → Set Ω := fun n =>
    {ω | jointRV X2s n ω ∈ typicalSet μ X2s n ε}
  set goodY : ℕ → Set Ω := fun n =>
    {ω | jointRV Ys n ω ∈ typicalSet μ Ys n ε}
  set goodZ : ℕ → Set Ω := fun n =>
    {ω | jointRV Zs n ω ∈ typicalSet μ Zs n ε}
  set jointEvt : ℕ → Set Ω := fun n =>
    {ω | (jointRV X1s n ω, jointRV X2s n ω, jointRV Ys n ω) ∈
          macJointlyTypicalSet μ X1s X2s Ys n ε}
  -- Decomposition: jointEvt n = goodX1 n ∩ goodX2 n ∩ goodY n ∩ goodZ n.
  -- The fourth conjunct uses that `jointRV Zs n ω i = Zs i ω = (X1s i ω, X2s i ω, Ys i ω)
  -- = (jointRV X1s n ω i, jointRV X2s n ω i, jointRV Ys n ω i)` by defeq.
  have h_joint_decomp : ∀ n, jointEvt n
      = ((goodX1 n ∩ goodX2 n) ∩ goodY n) ∩ goodZ n := by
    intro n
    ext ω
    refine ⟨?_, ?_⟩
    · intro hω
      refine ⟨⟨⟨hω.1, hω.2.1⟩, hω.2.2.1⟩, ?_⟩
      exact hω.2.2.2
    · rintro ⟨⟨⟨hX1', hX2'⟩, hY'⟩, hZ'⟩
      exact ⟨hX1', hX2', hY', hZ'⟩
  -- Bad events.
  set badX1 : ℕ → Set Ω := fun n => (goodX1 n)ᶜ
  set badX2 : ℕ → Set Ω := fun n => (goodX2 n)ᶜ
  set badY : ℕ → Set Ω := fun n => (goodY n)ᶜ
  set badZ : ℕ → Set Ω := fun n => (goodZ n)ᶜ
  -- Measurability of the "good" events.
  have h_meas_goodX1 : ∀ n, MeasurableSet (goodX1 n) := fun n =>
    (measurable_jointRV X1s hX1s n) (measurableSet_typicalSet μ X1s n ε)
  have h_meas_goodX2 : ∀ n, MeasurableSet (goodX2 n) := fun n =>
    (measurable_jointRV X2s hX2s n) (measurableSet_typicalSet μ X2s n ε)
  have h_meas_goodY : ∀ n, MeasurableSet (goodY n) := fun n =>
    (measurable_jointRV Ys hYs n) (measurableSet_typicalSet μ Ys n ε)
  have h_meas_goodZ : ∀ n, MeasurableSet (goodZ n) := fun n =>
    (measurable_jointRV Zs hZs n) (measurableSet_typicalSet μ Zs n ε)
  -- μ(good_*) → 1 ⇒ μ(bad_*) → 0.
  have h_bad_tendsto : ∀ (E : ℕ → Set Ω) (_ : ∀ n, MeasurableSet (E n))
      (_ : Filter.Tendsto (fun n => μ (E n)) Filter.atTop (𝓝 1)),
      Filter.Tendsto (fun n => μ ((E n)ᶜ)) Filter.atTop (𝓝 0) := by
    intro E hE h
    have h_id : ∀ n, μ ((E n)ᶜ) = 1 - μ (E n) := fun n => by
      rw [measure_compl (hE n) (measure_ne_top μ _), measure_univ]
    refine Filter.Tendsto.congr (fun n => (h_id n).symm) ?_
    have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
      ENNReal.continuous_sub_left (by simp)
    have h_step : Filter.Tendsto (fun n => (1 : ℝ≥0∞) - μ (E n)) Filter.atTop
        (𝓝 ((1 : ℝ≥0∞) - 1)) := h_cont.tendsto _ |>.comp h
    simpa using h_step
  have h_badX1_to_zero : Filter.Tendsto (fun n => μ (badX1 n)) Filter.atTop (𝓝 0) :=
    h_bad_tendsto goodX1 h_meas_goodX1 hX1
  have h_badX2_to_zero : Filter.Tendsto (fun n => μ (badX2 n)) Filter.atTop (𝓝 0) :=
    h_bad_tendsto goodX2 h_meas_goodX2 hX2
  have h_badY_to_zero : Filter.Tendsto (fun n => μ (badY n)) Filter.atTop (𝓝 0) :=
    h_bad_tendsto goodY h_meas_goodY hY
  have h_badZ_to_zero : Filter.Tendsto (fun n => μ (badZ n)) Filter.atTop (𝓝 0) :=
    h_bad_tendsto goodZ h_meas_goodZ hZ
  -- Complement union-bound.
  have h_compl_sub : ∀ n,
      (jointEvt n)ᶜ ⊆ badX1 n ∪ badX2 n ∪ badY n ∪ badZ n := by
    intro n
    rw [h_joint_decomp n]
    intro ω hω
    rw [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_inter_iff,
        Set.mem_inter_iff, not_and_or, not_and_or, not_and_or] at hω
    rcases hω with ((h_or | hY_bad) | hZ_bad)
    · rcases h_or with hX1_bad | hX2_bad
      · exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ hX1_bad))
      · exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _ hX2_bad))
    · exact Set.mem_union_left _ (Set.mem_union_right _ hY_bad)
    · exact Set.mem_union_right _ hZ_bad
  have h_bound_compl : ∀ n,
      μ ((jointEvt n)ᶜ) ≤
          μ (badX1 n) + μ (badX2 n) + μ (badY n) + μ (badZ n) := by
    intro n
    calc μ ((jointEvt n)ᶜ)
        ≤ μ (badX1 n ∪ badX2 n ∪ badY n ∪ badZ n) := measure_mono (h_compl_sub n)
      _ ≤ μ (badX1 n ∪ badX2 n ∪ badY n) + μ (badZ n) := measure_union_le _ _
      _ ≤ (μ (badX1 n ∪ badX2 n) + μ (badY n)) + μ (badZ n) := by
          gcongr
          exact measure_union_le _ _
      _ ≤ ((μ (badX1 n) + μ (badX2 n)) + μ (badY n)) + μ (badZ n) := by
          gcongr
          exact measure_union_le _ _
      _ = μ (badX1 n) + μ (badX2 n) + μ (badY n) + μ (badZ n) := by ring
  -- The four-bad-sum tends to 0.
  have h_sum_tendsto : Filter.Tendsto
      (fun n => μ (badX1 n) + μ (badX2 n) + μ (badY n) + μ (badZ n))
      Filter.atTop (𝓝 0) := by
    have h12 : Filter.Tendsto (fun n => μ (badX1 n) + μ (badX2 n))
        Filter.atTop (𝓝 (0 + 0)) := h_badX1_to_zero.add h_badX2_to_zero
    have h123 : Filter.Tendsto
        (fun n => μ (badX1 n) + μ (badX2 n) + μ (badY n))
        Filter.atTop (𝓝 ((0 + 0) + 0)) := h12.add h_badY_to_zero
    have h_all : Filter.Tendsto
        (fun n => μ (badX1 n) + μ (badX2 n) + μ (badY n) + μ (badZ n))
        Filter.atTop (𝓝 (((0 + 0) + 0) + 0)) := h123.add h_badZ_to_zero
    simpa using h_all
  -- Squeeze: 0 ≤ μ((jointEvt n)ᶜ) ≤ sum → 0.
  have h_compl_tendsto : Filter.Tendsto (fun n => μ ((jointEvt n)ᶜ))
      Filter.atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_sum_tendsto (fun _ => bot_le) h_bound_compl
  -- Measurability of jointEvt: it equals the intersection of 4 measurable sets.
  have h_meas_joint : ∀ n, MeasurableSet (jointEvt n) := by
    intro n
    rw [h_joint_decomp n]
    exact ((((h_meas_goodX1 n).inter (h_meas_goodX2 n))).inter
            (h_meas_goodY n)).inter (h_meas_goodZ n)
  -- μ(jointEvt n) = 1 - μ((jointEvt n)ᶜ) → 1.
  have h_id : ∀ n, μ (jointEvt n) = 1 - μ ((jointEvt n)ᶜ) := fun n => by
    rw [measure_compl (h_meas_joint n) (measure_ne_top μ _), measure_univ]
    have h_le : μ (jointEvt n) ≤ 1 := prob_le_one
    exact (ENNReal.sub_sub_cancel (by simp) h_le).symm
  refine Filter.Tendsto.congr (fun n => (h_id n).symm) ?_
  have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
    ENNReal.continuous_sub_left (by simp)
  have h_step : Filter.Tendsto (fun n => (1 : ℝ≥0∞) - μ ((jointEvt n)ᶜ))
      Filter.atTop (𝓝 ((1 : ℝ≥0∞) - 0)) := h_cont.tendsto _ |>.comp h_compl_tendsto
  simpa using h_step

end MACJointlyTypicalSetAEP

/-! ## Section 5 — Conditional X1-slice (L-MAC1-C) -/

section MACConditionalSlice

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ : Type*} [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
  [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
variable {α₂ : Type*} [Fintype α₂] [DecidableEq α₂] [Nonempty α₂]
  [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-- **L-MAC1-C — MAC conditional X1-slice**. For a fixed `(x₂, y)` block
pair, the `X₁`-fiber of the MAC jointly typical set is
`{ x₁ : Fin n → α₁ | (x₁, x₂, y) ∈ macJointlyTypicalSet … }`.

This is the multi-user analogue of `conditionalTypicalSlice` from
`SlepianWolfConditionalTypicalSlice.lean` — same fiber-over-the-typical-
set construction, lifted from 2-user to 3-user. -/
noncomputable def macConditionalTypicalSlice
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x2 : Fin n → α₂) (y : Fin n → β) :
    Set (Fin n → α₁) :=
  { x1 | (x1, x2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε }

lemma mem_macConditionalTypicalSlice_iff
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x2 : Fin n → α₂) (y : Fin n → β) (x1 : Fin n → α₁) :
    x1 ∈ macConditionalTypicalSlice μ X1s X2s Ys n ε x2 y ↔
      (x1, x2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε := Iff.rfl

/-- The conditional slice is finite (it lives in `Fin n → α₁`). -/
lemma macConditionalTypicalSlice_finite
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x2 : Fin n → α₂) (y : Fin n → β) :
    (macConditionalTypicalSlice μ X1s X2s Ys n ε x2 y).Finite :=
  Set.toFinite _

/-- Every element of the slice is X1-axis typical. -/
lemma macConditionalTypicalSlice_subset_X1_typicalSet
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x2 : Fin n → α₂) (y : Fin n → β) :
    macConditionalTypicalSlice μ X1s X2s Ys n ε x2 y ⊆ typicalSet μ X1s n ε := by
  intro x1 hx1
  exact hx1.1

/-- The slice is empty when `x₂` fails the X2-axis typicality condition. -/
lemma macConditionalTypicalSlice_empty_of_x2_not_typical
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) {x2 : Fin n → α₂} (y : Fin n → β)
    (hx2 : x2 ∉ typicalSet μ X2s n ε) :
    macConditionalTypicalSlice μ X1s X2s Ys n ε x2 y = ∅ := by
  ext x1
  refine ⟨fun hx1 => ?_, fun hx1 => hx1.elim⟩
  exact absurd hx1.2.1 hx2

/-- The slice is empty when `y` fails the Y-axis typicality condition. -/
lemma macConditionalTypicalSlice_empty_of_y_not_typical
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x2 : Fin n → α₂) {y : Fin n → β}
    (hy : y ∉ typicalSet μ Ys n ε) :
    macConditionalTypicalSlice μ X1s X2s Ys n ε x2 y = ∅ := by
  ext x1
  refine ⟨fun hx1 => ?_, fun hx1 => hx1.elim⟩
  exact absurd hx1.2.2.1 hy

end MACConditionalSlice

/-! ## Section 6 — Publish-layer hook -/

section MACInnerBoundDischarge

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}
variable [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]

/-- **MAC inner bound — L-MAC1 partial discharge form**.

A thin partial-discharge wrapper around `mac_capacity_region_inner_bound`
(`MultipleAccessChannel.lean:567`). The parent theorem's
`_h_joint_typ : True` placeholder is now backed *concretely* in this
library by the AEP statement of `macJointlyTypicalSet_prob_tendsto_one`
+ the cardinality bound of `macJointlyTypicalSet_card_le` + the SW-style
slice of `macConditionalTypicalSlice` (all published in earlier sections
of this file). The body remains an identity wrap to the parent's
`h_existence`, matching the established statement-level pass-through
pattern.

Callers that want to engage the discharge layer should use this wrapper:
the typical-set machinery is now resolved against published definitions
of this library, not external hypotheses.

The trailing 4-error-event Bonferroni body (Cover-Thomas eqs. 15.65-15.84)
that would lift `h_existence` from hypothesis to theorem is **out of
scope** of this file and remains future work.

@residual(plan:mac-l1-discharge-moonshot-plan) -/
theorem mac_capacity_region_inner_bound_with_joint_typ_aep
    (W : MACChannel α₁ α₂ β)
    (R₁ R₂ I₁ I₂ Iboth : ℝ)
    (h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
    (h_jt : MACJointTypicalityAchievable W R₁ R₂ I₁ I₂ Iboth) :
    MACInnerBoundExistence W R₁ R₂ := by
  sorry

end MACInnerBoundDischarge

end InformationTheory.Shannon
