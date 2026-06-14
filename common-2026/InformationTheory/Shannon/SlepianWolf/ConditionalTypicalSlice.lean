import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AEP.Basic
import InformationTheory.Shannon.ChannelCoding.Basic

/-!
# Slepian–Wolf conditional typical slice

This file publishes the **conditional typical slice size bound**, the key new
ingredient for the full Slepian–Wolf rate region (Cover–Thomas Theorem 15.4.1).
For a fixed `Y`-block `y : Fin n → β`, the `X`-fiber of the jointly typical set
is bounded in size by `exp(n · (H(X|Y) + 2ε))`, where `H(X|Y) := H(X, Y) - H(Y)`.

## Main definitions

* `conditionalTypicalSlice μ Xs Ys n ε y` —
  the fiber `{x : Fin n → α | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε}`.

## Main statements

* `conditionalTypicalSlice_card_le` — the slice size is bounded by
  `exp(n · (H(X, Y) - H(Y) + 2ε))`.

## Implementation notes

* Each fiber element `x` makes `(x, y)` jointly typical, so the joint sequence
  `i ↦ (x i, y i)` lies in `typicalSet μ (jointSequence Xs Ys) n ε` and each
  sample has probability at least `exp(-n · (H(X, Y) + ε))` by
  `typicalSet_prob_ge`. Summed over the fiber this is at most `Pr[Yⁿ = y]`, which
  for `Y`-typical `y` is at most `exp(-n · (H(Y) - ε))` by `typicalSet_prob_le`.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ## Definition of the conditional typical slice -/

/-- The **conditional typical slice** at `y`: the X-fiber of the jointly
typical set `jointlyTypicalSet μ Xs Ys n ε` at the Y-block `y`. Each
element `x` of this slice forms a jointly typical pair `(x, y)`. -/
noncomputable def conditionalTypicalSlice
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (y : Fin n → β) : Set (Fin n → α) :=
  { x | (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε }

omit [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
lemma mem_conditionalTypicalSlice_iff
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (y : Fin n → β) (x : Fin n → α) :
    x ∈ conditionalTypicalSlice μ Xs Ys n ε y ↔
      (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε := Iff.rfl

omit [DecidableEq α] [DecidableEq β] in
/-- The slice is finite (it lives in the finite ambient space `Fin n → α`). -/
lemma conditionalTypicalSlice_finite
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (y : Fin n → β) :
    (conditionalTypicalSlice μ Xs Ys n ε y).Finite :=
  Set.toFinite _

omit [DecidableEq α] [DecidableEq β] [Nonempty α] [Nonempty β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- The slice is empty when `y` is not Y-typical. -/
lemma conditionalTypicalSlice_empty_of_y_not_typical
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) {y : Fin n → β}
    (hy : y ∉ typicalSet μ Ys n ε) :
    conditionalTypicalSlice μ Xs Ys n ε y = ∅ := by
  ext x
  constructor
  · intro hx
    exact absurd hx.2.1 hy
  · intro hx
    exact hx.elim

/-! ## Main bound — fiber cardinality -/

-- If `c * exp(-a) ≤ exp(-b)`, then `c ≤ exp(a - b)` (for any reals `a b` and `c ≥ 0`).
private lemma le_exp_sub_of_mul_exp_neg_le_exp_neg (c a b : ℝ) (_ : 0 ≤ c)
    (h : c * Real.exp (-a) ≤ Real.exp (-b)) : c ≤ Real.exp (a - b) := by
  have hea : 0 < Real.exp a := Real.exp_pos a
  have := mul_le_mul_of_nonneg_right h hea.le
  have hlhs : c * Real.exp (-a) * Real.exp a = c := by
    rw [mul_assoc, ← Real.exp_add]; simp
  have hrhs : Real.exp (-b) * Real.exp a = Real.exp (a - b) := by
    rw [← Real.exp_add, show -b + a = a - b from by ring]
  linarith [hlhs ▸ hrhs ▸ this]

-- Bridge equality: pushing `proj_Y ⁻¹' {y}` through `μ.map (jointRV (jointSequence Xs Ys) n)`
-- reduces to pushing `{y}` through `μ.map (jointRV Ys n)`.
private lemma jointRV_jointSequence_proj_measureReal_eq
    {Ω' α' β' : Type*} [MeasurableSpace Ω']
    [Fintype α'] [MeasurableSpace α'] [MeasurableSingletonClass α']
    [Fintype β'] [MeasurableSpace β'] [MeasurableSingletonClass β']
    (μ' : Measure Ω')
    (Xs' : ℕ → Ω' → α') (Ys' : ℕ → Ω' → β')
    (hYs' : ∀ i, Measurable (Ys' i))
    (hZs' : ∀ i, Measurable (jointSequence Xs' Ys' i))
    (n' : ℕ) (y' : Fin n' → β') :
    let proj_Y' : (Fin n' → α' × β') → (Fin n' → β') := fun z i => (z i).2
    (μ'.map (jointRV (jointSequence Xs' Ys') n')).real
        (proj_Y' ⁻¹' ({y'} : Set (Fin n' → β')))
      = (μ'.map (jointRV Ys' n')).real ({y'} : Set (Fin n' → β')) := by
  intro proj_Y'
  have hproj_meas : Measurable proj_Y' := measurable_pi_lambda _ fun i =>
    (measurable_pi_apply i).snd
  have h_meas_y : MeasurableSet ({y'} : Set (Fin n' → β')) := measurableSet_singleton y'
  have h_meas_pre : MeasurableSet (proj_Y' ⁻¹' ({y'} : Set (Fin n' → β'))) :=
    hproj_meas h_meas_y
  have hZmeas : Measurable (jointRV (jointSequence Xs' Ys') n') :=
    measurable_jointRV _ hZs' n'
  have hYmeas : Measurable (jointRV Ys' n') := measurable_jointRV Ys' hYs' n'
  have hpre_eq :
      jointRV (jointSequence Xs' Ys') n' ⁻¹' (proj_Y' ⁻¹' ({y'} : Set (Fin n' → β')))
        = jointRV Ys' n' ⁻¹' ({y'} : Set (Fin n' → β')) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hω; funext i; exact congr_fun hω i
    · intro hω; funext i; exact congr_fun hω i
  unfold MeasureTheory.Measure.real
  rw [Measure.map_apply hZmeas h_meas_pre, Measure.map_apply hYmeas h_meas_y, hpre_eq]

omit [DecidableEq α] [DecidableEq β] in
/-- **Conditional typical slice size bound**: for any `Y`-block `y`, the
cardinality of the `X`-fiber of the jointly typical set at `y` is at most
`exp(n · (H(X, Y) - H(Y) + 2ε))`, equivalently `exp(n · (H(X|Y) + 2ε))`. -/
@[entry_point]
theorem conditionalTypicalSlice_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ_full : iIndepFun (fun i => jointSequence Xs Ys i) μ)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε : ℝ}
    (y : Fin n → β) :
    ((conditionalTypicalSlice μ Xs Ys n ε y).toFinite.toFinset.card : ℝ)
      ≤ Real.exp ((n : ℝ) *
          (entropy μ (jointSequence Xs Ys 0) - entropy μ (Ys 0) + 2 * ε)) := by
  classical
  -- Notation.
  set Zs : ℕ → Ω → α × β := jointSequence Xs Ys with hZs_def
  have hZs : ∀ i, Measurable (Zs i) := fun i =>
    measurable_jointSequence Xs Ys hXs hYs i
  set HZ : ℝ := entropy μ (Zs 0) with hHZ_def
  set HY : ℝ := entropy μ (Ys 0) with hHY_def
  set F : Finset (Fin n → α) :=
    (conditionalTypicalSlice μ Xs Ys n ε y).toFinite.toFinset with hF_def
  -- Step 0: split on whether `y ∈ typicalSet μ Ys n ε`.
  by_cases hyT : y ∈ typicalSet μ Ys n ε
  · -- Y-typical: full argument.
    -- Embedding `embed : (Fin n → α) → (Fin n → α × β)`, `embed x i := (x i, y i)`.
    let embed : (Fin n → α) → (Fin n → α × β) := fun x i => (x i, y i)
    have hembed_inj : Function.Injective embed := by
      intro x x' hxx
      funext i
      have := congr_fun hxx i
      exact (Prod.mk.injEq _ _ _ _).mp this |>.1
    -- For each `x ∈ F`, `embed x ∈ typicalSet μ Zs n ε`.
    have hF_embed_typ : ∀ x ∈ F, embed x ∈ typicalSet μ Zs n ε := by
      intro x hx
      have hx_set : x ∈ conditionalTypicalSlice μ Xs Ys n ε y :=
        (Set.Finite.mem_toFinset _).mp hx
      exact hx_set.2.2
    -- Step 1: point-wise mass lower bound via `typicalSet_prob_ge` on `Zs`.
    have hε_pos : 0 < ε := by
      rcases F.eq_empty_or_nonempty with _ | ⟨x0, hx0⟩
      · rw [mem_typicalSet_iff] at hyT; exact (abs_nonneg _).trans_lt hyT
      · have h := hF_embed_typ x0 hx0
        rw [mem_typicalSet_iff] at h; exact (abs_nonneg _).trans_lt h
    have hpoint_ge : ∀ x ∈ F,
        Real.exp (-(n : ℝ) * (HZ + ε)) ≤
            (μ.map (jointRV Zs n)).real {embed x} := by
      intro x hx
      have hxT : embed x ∈ typicalSet μ Zs n ε := hF_embed_typ x hx
      exact typicalSet_prob_ge μ Zs hZs hindepZ_full hidentZ hposZ n (embed x) hxT
    -- Step 2: sum over `F`.
    have hsum_ge :
        (F.card : ℝ) * Real.exp (-(n : ℝ) * (HZ + ε)) ≤
            ∑ x ∈ F, (μ.map (jointRV Zs n)).real {embed x} := by
      calc (F.card : ℝ) * Real.exp (-(n : ℝ) * (HZ + ε))
          = ∑ _x ∈ F, Real.exp (-(n : ℝ) * (HZ + ε)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ F, (μ.map (jointRV Zs n)).real {embed x} :=
            Finset.sum_le_sum hpoint_ge
    -- Step 3: rewrite the sum as the measure of `embed '' F`.
    have hMprobZ : IsProbabilityMeasure (μ.map (jointRV Zs n)) :=
      Measure.isProbabilityMeasure_map (measurable_jointRV Zs hZs n).aemeasurable
    have hMprobY : IsProbabilityMeasure (μ.map (jointRV Ys n)) :=
      Measure.isProbabilityMeasure_map (measurable_jointRV Ys hYs n).aemeasurable
    set FimgZ : Finset (Fin n → α × β) := F.image embed with hFimgZ_def
    have hFimg_card : FimgZ.card = F.card :=
      Finset.card_image_of_injective _ hembed_inj
    have hsum_eq :
        (∑ x ∈ F, (μ.map (jointRV Zs n)).real {embed x})
          = ∑ z ∈ FimgZ, (μ.map (jointRV Zs n)).real {z} := by
      symm
      rw [hFimgZ_def]
      apply Finset.sum_image
      intro a _ b _ hab
      exact hembed_inj hab
    have hFimg_measure_eq :
        (∑ z ∈ FimgZ, (μ.map (jointRV Zs n)).real {z})
          = (μ.map (jointRV Zs n)).real (FimgZ : Set (Fin n → α × β)) :=
      sum_measureReal_singleton (μ := μ.map (jointRV Zs n)) FimgZ
    -- Step 4: `FimgZ ⊆ proj_Y ⁻¹' {y}`, so its measure ≤ (μ.map (jointRV Ys n)).real {y}.
    let proj_Y : (Fin n → α × β) → (Fin n → β) := fun z i => (z i).2
    have hproj_subset :
        (FimgZ : Set (Fin n → α × β)) ⊆ proj_Y ⁻¹' ({y} : Set (Fin n → β)) := by
      intro z hz
      rw [Finset.coe_image, Set.mem_image] at hz
      obtain ⟨x, _, hxz⟩ := hz
      -- proj_Y (embed x) = y by defeq (both are `fun i => y i`).
      show proj_Y z = y
      rw [← hxz]
    have hbound_image :
        (μ.map (jointRV Zs n)).real (FimgZ : Set (Fin n → α × β))
          ≤ (μ.map (jointRV Zs n)).real (proj_Y ⁻¹' ({y} : Set (Fin n → β))) :=
      measureReal_mono (μ := μ.map (jointRV Zs n)) hproj_subset
    -- Step 5: relate `(μ.map (jointRV Zs n))` of `proj_Y ⁻¹' {y}` to `(μ.map (jointRV Ys n)) {y}`.
    have hbridge :
        (μ.map (jointRV Zs n)).real (proj_Y ⁻¹' ({y} : Set (Fin n → β)))
          = (μ.map (jointRV Ys n)).real ({y} : Set (Fin n → β)) :=
      jointRV_jointSequence_proj_measureReal_eq μ Xs Ys hYs hZs n y
    -- Step 6: Y-typical bound on `(μ.map (jointRV Ys n)).real {y}`.
    have hYbd : (μ.map (jointRV Ys n)).real ({y} : Set (Fin n → β))
        ≤ Real.exp (-(n : ℝ) * (HY - ε)) :=
      typicalSet_prob_le μ Ys hYs hindepY_full hidentY hposY n y hyT
    -- Step 7: chain the bounds.
    have hchain :
        (F.card : ℝ) * Real.exp (-(n : ℝ) * (HZ + ε))
          ≤ Real.exp (-(n : ℝ) * (HY - ε)) := by
      calc (F.card : ℝ) * Real.exp (-(n : ℝ) * (HZ + ε))
          ≤ ∑ x ∈ F, (μ.map (jointRV Zs n)).real {embed x} := hsum_ge
        _ = ∑ z ∈ FimgZ, (μ.map (jointRV Zs n)).real {z} := hsum_eq
        _ = (μ.map (jointRV Zs n)).real (FimgZ : Set (Fin n → α × β)) := hFimg_measure_eq
        _ ≤ (μ.map (jointRV Zs n)).real (proj_Y ⁻¹' ({y} : Set (Fin n → β))) :=
            hbound_image
        _ = (μ.map (jointRV Ys n)).real ({y} : Set (Fin n → β)) := hbridge
        _ ≤ Real.exp (-(n : ℝ) * (HY - ε)) := hYbd
    -- Step 8: isolate `F.card`.
    -- hchain : F.card * exp(-n(HZ+ε)) ≤ exp(-n(HY-ε)).
    -- With the ring identity -n*(HZ+ε) = -(n*(HZ+ε)), apply the exp helper.
    have hchain_rw : (F.card : ℝ) * Real.exp (-((n : ℝ) * (HZ + ε)))
        ≤ Real.exp (-((n : ℝ) * (HY - ε))) := by
      rw [show -((n : ℝ) * (HZ + ε)) = -(n : ℝ) * (HZ + ε) from by ring,
          show -((n : ℝ) * (HY - ε)) = -(n : ℝ) * (HY - ε) from by ring]
      exact hchain
    have hstep8 : (F.card : ℝ) ≤ Real.exp ((n : ℝ) * (HZ + ε) - (n : ℝ) * (HY - ε)) :=
      le_exp_sub_of_mul_exp_neg_le_exp_neg _ _ _ (Nat.cast_nonneg _) hchain_rw
    calc (F.card : ℝ) ≤ Real.exp ((n : ℝ) * (HZ + ε) - (n : ℝ) * (HY - ε)) := hstep8
      _ = Real.exp ((n : ℝ) * (HZ - HY + 2 * ε)) := by
          rw [show (n : ℝ) * (HZ + ε) - (n : ℝ) * (HY - ε)
              = (n : ℝ) * (HZ - HY + 2 * ε) from by ring]
  · -- Y not typical: F = ∅, cardinality 0, RHS ≥ 0.
    have hempty :
        conditionalTypicalSlice μ Xs Ys n ε y = ∅ :=
      conditionalTypicalSlice_empty_of_y_not_typical μ Xs Ys n ε hyT
    have hF_empty : F = ∅ := by
      rw [hF_def]
      rw [hempty]
      simp
    rw [hF_empty]
    simp only [Finset.card_empty, CharP.cast_eq_zero, ge_iff_le]
    exact (Real.exp_pos _).le

end InformationTheory.Shannon.ChannelCoding
