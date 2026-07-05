import InformationTheory.Shannon.WynerZiv.Basic
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.Entropy
import InformationTheory.Shannon.ConditionalMethodOfTypes.Core

/-!
# Wyner–Ziv operational achievability predicate

This file provides the operational-achievability predicate `WynerZivAchievable`
shared by the Wyner–Ziv converse and achievability legs, together with the
single-letter pmf-to-measure bridge relating the pmf-form mutual informations
`wzMutualInfoXU` / `wzMutualInfoYU` to the measure-form `mutualInfo`.

## Main definitions

* `WynerZivAchievable` — a rate `R` is achievable at distortion `D` for the
  i.i.d. source `P_XY` if there is a sequence of Wyner–Ziv block codes whose
  log-cardinality rate tends to `R` and whose expected block distortion is
  eventually within `D + ε` for every `ε > 0`.

## Main statements

* `wzMutualInfoXU_eq_mutualInfo` — the pmf-form `I(X;U)` of the joint pmf
  induced by a measure equals the measure-form `(mutualInfo μ X U).toReal`.
* `wzMutualInfoYU_eq_mutualInfo` — the analogous identity for `I(Y;U)`.

## Implementation notes

The distortion component of `WynerZivAchievable` uses the **distortion-only**
"eventually within `D + ε`" form (equivalently `limsup ≤ D`), matching the
distortion-only rate-distortion achievability/converse templates
(`rate_distortion_achievability`, `rate_distortion_converse_single_shot`); the
`WynerZivCode` structure exposes no codeword, so no error-probability component
is bundled here — error probability is an achievability-internal device deferred
to the achievability leg. The predicate is a pure existential with the two limit
conditions; no proof core is carried inside it.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
-- The shared alphabet variable block carries `DecidableEq` for downstream use
-- (converse/achievability legs); the declarations here need it only via `classical`.
set_option linter.unusedDecidableInType false

variable {α β γ U : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]

/-! ## Operational achievability predicate -/

/-- A rate `R` is Wyner–Ziv achievable at distortion `D` for the i.i.d. source
`P_XY` on `α × β` (side information `Y` at the decoder only) if there is a
sequence of Wyner–Ziv block codes `c n : WynerZivCode (M n) n α β γ` such that:

* the log-cardinality rate `log (M n) / n` tends to `R`, and
* for every `ε > 0`, the expected block distortion of `c n` is eventually
  (in `n`) within `D + ε`.

The distortion condition is the distortion-only "eventually `≤ D + ε`" form
(equivalently `limsup ≤ D`). This is a pure existential over code sequences plus
the two limit conditions; no proof content is carried in the predicate.
@audit:ok -/
def WynerZivAchievable
    (P_XY : Measure (α × β)) (d : DistortionFn α γ) (R D : ℝ) : Prop :=
  ∃ (M : ℕ → ℕ) (_hM : ∀ n, 0 < M n) (c : ∀ n, WynerZivCode (M n) n α β γ),
    Filter.Tendsto (fun n ↦ Real.log (M n : ℝ) / n) Filter.atTop (nhds R) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop,
        (c n).expectedBlockDistortion P_XY d ≤ D + ε)

/-! ## pmf-to-measure bridge for the single-letter mutual informations

The bridge relates the pmf-form `wzMutualInfoXU`/`wzMutualInfoYU` (finite-sum
`negMulLog` form of `I(X;U)`/`I(Y;U)`) of the empirical joint pmf induced by a
measure to the measure-form `mutualInfo`. Internally it factors through a fully
general two-variable identity `mutualInfoPmf_empirical_eq_mutualInfo` plus a
marginalization of the three-variable empirical pmf down to a two-variable one.
-/

/-- The second (right) marginal of a finite joint measure recovers the
`Prod.snd`-pushforward mass. Companion to
`sum_real_prod_singleton_of_map_fst_eq`, obtained via `Prod.swap`. -/
private lemma sum_real_prod_singleton_snd
    {A B : Type*}
    [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [DecidableEq B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure (A × B)) [IsProbabilityMeasure ν] (νY : Measure B)
    (hmarg : ν.map Prod.snd = νY) (b : B) :
    (∑ a : A, ν.real {(a, b)}) = νY.real {b} := by
  classical
  haveI : IsProbabilityMeasure (ν.map Prod.swap) :=
    Measure.isProbabilityMeasure_map measurable_swap.aemeasurable
  have hfst : (ν.map Prod.swap).map Prod.fst = νY := by
    rw [Measure.map_map measurable_fst measurable_swap]; exact hmarg
  have hkey := sum_real_prod_singleton_of_map_fst_eq (ν.map Prod.swap) νY hfst b
  rw [← hkey]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_measureReal_apply measurable_swap (measurableSet_singleton (b, a))]
  congr 1
  ext ⟨a', b'⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage, Prod.swap_prod_mk, Prod.mk.injEq]
  tauto

/-- Summing out the middle coordinate of a three-variable finite joint measure
recovers the `(fst, snd.snd)`-pushforward mass. -/
private lemma sum_real_triple_mid_of_map_eq
    (ν : Measure (α × β × U)) [IsFiniteMeasure ν] (νXU : Measure (α × U))
    (hmarg : ν.map (fun p : α × β × U ↦ (p.1, p.2.2)) = νXU) (x : α) (u : U) :
    (∑ y : β, ν.real {(x, y, u)}) = νXU.real {(x, u)} := by
  classical
  have hg : Measurable (fun p : α × β × U ↦ (p.1, p.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have h_pre : ((fun p : α × β × U ↦ (p.1, p.2.2)) ⁻¹' ({(x, u)} : Set (α × U)))
      = ⋃ y ∈ (Finset.univ : Finset β), ({(x, y, u)} : Set (α × β × U)) := by
    ext p
    obtain ⟨x', y', u'⟩ := p
    constructor
    · intro hp
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hp
      obtain ⟨hx, hu⟩ := hp
      subst hx; subst hu
      exact Set.mem_biUnion (Finset.mem_univ y') rfl
    · intro hp
      rw [Set.mem_iUnion₂] at hp
      obtain ⟨y, _, hy⟩ := hp
      simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hy
      obtain ⟨hx, hy', hu⟩ := hy
      subst hx; subst hy'; subst hu
      simp
  have h_map : νXU.real {(x, u)} = ν.real ((fun p : α × β × U ↦ (p.1, p.2.2)) ⁻¹' {(x, u)}) := by
    rw [← hmarg]; exact map_measureReal_apply hg (measurableSet_singleton _)
  have h_disj : (↑(Finset.univ : Finset β) : Set β).PairwiseDisjoint
      (fun y ↦ ({(x, y, u)} : Set (α × β × U))) := by
    intro y₁ _ y₂ _ hy s hs1 hs2 p hp
    have hp1 := hs1 hp; have hp2 := hs2 hp
    simp only [Set.mem_singleton_iff] at hp1 hp2
    have hpe : (x, y₁, u) = (x, y₂, u) := hp1.symm.trans hp2
    exact absurd (congrArg (fun q : α × β × U ↦ q.2.1) hpe) hy
  have h_meas : ∀ y ∈ (Finset.univ : Finset β),
      MeasurableSet ({(x, y, u)} : Set (α × β × U)) := fun _ _ ↦ measurableSet_singleton _
  rw [h_map, h_pre, measureReal_biUnion_finset h_disj h_meas]

/-- **General two-variable pmf-to-measure bridge.** For finite alphabets `A`, `B`
and a probability measure `μ` with measurable coordinates `Xs : Ω → A`,
`Uo : Ω → B`, the pmf-form mutual information of the empirical joint pmf equals
the measure-form `(mutualInfo μ Xs Uo).toReal`. Proved by identifying the three
`negMulLog` sums with `entropy μ Xs`, `entropy μ Uo`, `entropy μ (Xs, Uo)` and
combining the entropy chain rule with `mutualInfo = H − H|·`. -/
private lemma mutualInfoPmf_empirical_eq_mutualInfo
    {Ω : Type*} [MeasurableSpace Ω]
    {A B : Type*}
    [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [DecidableEq B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → A) (Uo : Ω → B)
    (hXs : Measurable Xs) (hUo : Measurable Uo) :
    mutualInfoPmf (fun p : A × B ↦ (μ.map (fun ω ↦ (Xs ω, Uo ω))).real {p})
      = (mutualInfo μ Xs Uo).toReal := by
  classical
  have hpair : Measurable (fun ω ↦ (Xs ω, Uo ω)) := hXs.prodMk hUo
  haveI : IsProbabilityMeasure (μ.map (fun ω ↦ (Xs ω, Uo ω))) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  have hmap_fst : (μ.map (fun ω ↦ (Xs ω, Uo ω))).map Prod.fst = μ.map Xs := by
    rw [Measure.map_map measurable_fst hpair]; rfl
  have hmap_snd : (μ.map (fun ω ↦ (Xs ω, Uo ω))).map Prod.snd = μ.map Uo := by
    rw [Measure.map_map measurable_snd hpair]; rfl
  have hF : ∀ a : A,
      marginalFst (fun p : A × B ↦ (μ.map (fun ω ↦ (Xs ω, Uo ω))).real {p}) a
        = (μ.map Xs).real {a} := by
    intro a
    change (∑ b : B, (μ.map (fun ω ↦ (Xs ω, Uo ω))).real {(a, b)}) = (μ.map Xs).real {a}
    exact sum_real_prod_singleton_of_map_fst_eq _ (μ.map Xs) hmap_fst a
  have hS : ∀ b : B,
      marginalSnd (fun p : A × B ↦ (μ.map (fun ω ↦ (Xs ω, Uo ω))).real {p}) b
        = (μ.map Uo).real {b} := by
    intro b
    change (∑ a : A, (μ.map (fun ω ↦ (Xs ω, Uo ω))).real {(a, b)}) = (μ.map Uo).real {b}
    exact sum_real_prod_singleton_snd _ (μ.map Uo) hmap_snd b
  unfold mutualInfoPmf
  simp_rw [hF, hS]
  change entropy μ Xs + entropy μ Uo - entropy μ (fun ω ↦ (Xs ω, Uo ω))
      = (mutualInfo μ Xs Uo).toReal
  rw [entropy_pair_eq_entropy_add_condEntropy μ Xs Uo hXs hUo,
      mutualInfo_comm μ Xs Uo hXs hUo,
      mutualInfo_eq_entropy_sub_condEntropy μ Uo Xs hUo hXs]
  ring

/-- The pmf-form mutual information `I(X;U)` of the three-variable joint pmf
induced by a probability measure `μ` with coordinates `X`, `Y`, `U` equals the
measure-form `(mutualInfo μ X U).toReal`. Stated in `.toReal` form so it composes
with the single-letterization of the converse leg. -/
lemma wzMutualInfoXU_eq_mutualInfo
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (Uc : Ω → U)
    (hX : Measurable X) (hY : Measurable Y) (hU : Measurable Uc) :
    wzMutualInfoXU U (fun p : α × β × U ↦
        (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))).real {p})
      = (mutualInfo μ X Uc).toReal := by
  classical
  have hpair3 : Measurable (fun ω ↦ (X ω, Y ω, Uc ω)) := hX.prodMk (hY.prodMk hU)
  haveI : IsProbabilityMeasure (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))) :=
    Measure.isProbabilityMeasure_map hpair3.aemeasurable
  have hg : Measurable (fun p : α × β × U ↦ (p.1, p.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hmid : (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))).map (fun p : α × β × U ↦ (p.1, p.2.2))
      = μ.map (fun ω ↦ (X ω, Uc ω)) := by
    rw [Measure.map_map hg hpair3]; rfl
  have hmargXU : wzMarginalXU U (fun p : α × β × U ↦ (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))).real {p})
      = fun p : α × U ↦ (μ.map (fun ω ↦ (X ω, Uc ω))).real {p} := by
    funext p
    obtain ⟨x, u⟩ := p
    change (∑ y : β, (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))).real {(x, y, u)})
        = (μ.map (fun ω ↦ (X ω, Uc ω))).real {(x, u)}
    exact sum_real_triple_mid_of_map_eq _ (μ.map (fun ω ↦ (X ω, Uc ω))) hmid x u
  unfold wzMutualInfoXU
  rw [hmargXU]
  exact mutualInfoPmf_empirical_eq_mutualInfo μ X Uc hX hU

/-- The pmf-form mutual information `I(Y;U)` of the three-variable joint pmf
induced by a probability measure `μ` with coordinates `X`, `Y`, `U` equals the
measure-form `(mutualInfo μ Y U).toReal`. Stated in `.toReal` form so it composes
with the single-letterization of the converse leg. -/
lemma wzMutualInfoYU_eq_mutualInfo
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β) (Uc : Ω → U)
    (hX : Measurable X) (hY : Measurable Y) (hU : Measurable Uc) :
    wzMutualInfoYU U (fun p : α × β × U ↦
        (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))).real {p})
      = (mutualInfo μ Y Uc).toReal := by
  classical
  have hpair3 : Measurable (fun ω ↦ (X ω, Y ω, Uc ω)) := hX.prodMk (hY.prodMk hU)
  haveI : IsProbabilityMeasure (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))) :=
    Measure.isProbabilityMeasure_map hpair3.aemeasurable
  have hsnd : (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))).map Prod.snd
      = μ.map (fun ω ↦ (Y ω, Uc ω)) := by
    rw [Measure.map_map measurable_snd hpair3]; rfl
  have hmargYU : wzMarginalYU U (fun p : α × β × U ↦ (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))).real {p})
      = fun p : β × U ↦ (μ.map (fun ω ↦ (Y ω, Uc ω))).real {p} := by
    funext p
    obtain ⟨y, u⟩ := p
    change (∑ x : α, (μ.map (fun ω ↦ (X ω, Y ω, Uc ω))).real {(x, y, u)})
        = (μ.map (fun ω ↦ (Y ω, Uc ω))).real {(y, u)}
    exact sum_real_prod_singleton_snd _ (μ.map (fun ω ↦ (Y ω, Uc ω))) hsnd (y, u)
  unfold wzMutualInfoYU
  rw [hmargYU]
  exact mutualInfoPmf_empirical_eq_mutualInfo μ Y Uc hY hU

end InformationTheory.Shannon
