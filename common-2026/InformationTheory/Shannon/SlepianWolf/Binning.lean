import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SlepianWolf.Achievability
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Slepian–Wolf random binning machinery

This file introduces the **random-binning measure** `binningMeasure α n M` on the
hash-function space `(Fin n → α) → Fin M`, plus the **collision-probability**
collapse `𝔼_f[1_{f x = f x'}] = 1/M` for `x ≠ x'` (and `= 1` for `x = x'`).

## Main definitions

* `binningMeasure α n M` — `Measure.pi (fun _ : (Fin n → α) => uniformOn univ)`
  on `(Fin n → α) → Fin M`.

## Main statements

* `binningMeasure_singleton_real` — `(binningMeasure α n M).real {f} = (1/M)^{|α|^n}`.
* `binning_collision_prob` — for `x ≠ x'`,
  `(binningMeasure α n M).real {f | f x = f x'} = 1/M`.

## Implementation notes

* This is the encoder-side mirror of `ChannelCodingAchievability.codebookMeasure`
  (`Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))`): the index of
  the outer `Measure.pi` is swapped from `Fin M` (codeword count) to `(Fin n → α)`
  (input-sequence space).
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## The random binning measure and basic instances -/

/-- **Random binning measure.** Each input sequence `x ∈ (Fin n → α)` is hashed
independently to a uniformly random bin index in `Fin M`. The total law on the
hash-function space `(Fin n → α) → Fin M` is the product of `|α|^n` copies of
`uniformOn (Set.univ : Set (Fin M))`.

Encoder-side mirror of `ChannelCodingAchievability.codebookMeasure`:
* `codebookMeasure p M n` = `Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => p))`
  ("`Fin M` codewords drawn i.i.d. from `p^n`").
* `binningMeasure α n M` = `Measure.pi (fun _ : (Fin n → α) => uniformOn univ)`
  ("`|α|^n` hash bins drawn uniformly").

The outer-`Measure.pi` index is the **input-sequence space** `(Fin n → α)`,
which is a `Fintype` because `α` is finite. -/
noncomputable def binningMeasure
    (α : Type*) [Fintype α] [MeasurableSpace α]
    (n M : ℕ) [NeZero M] :
    Measure ((Fin n → α) → Fin M) :=
  Measure.pi (fun _ : (Fin n → α) => uniformOn (Set.univ : Set (Fin M)))

/-- The random binning measure is a probability measure. -/
instance binningMeasure.instIsProbabilityMeasure
    (n M : ℕ) [NeZero M] :
    IsProbabilityMeasure (binningMeasure α n M) := by
  unfold binningMeasure
  infer_instance

/-- **Singleton mass.** For any hash function `f : (Fin n → α) → Fin M`,
its `binningMeasure`-mass is `(1/M)^{|α|^n}` (each of the `|α|^n` input
sequences independently picks one of `M` bins). -/
@[entry_point]
lemma binningMeasure_singleton_real
    (n M : ℕ) [NeZero M] (f : (Fin n → α) → Fin M) :
    (binningMeasure α n M).real {f}
      = (((M : ℝ))⁻¹) ^ (Fintype.card (Fin n → α)) := by
  classical
  haveI : MeasurableSingletonClass ((Fin n → α) → Fin M) :=
    Pi.instMeasurableSingletonClass
  unfold binningMeasure
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  -- Each factor is `uniformOn univ {f x}` = `1 / Fintype.card (Fin M)`.
  have h_factor : ∀ x : (Fin n → α),
      ((uniformOn (Set.univ : Set (Fin M))) {f x}).toReal = (M : ℝ)⁻¹ := by
    intro x
    rw [uniformOn_univ]
    -- = (Measure.count {f x} / Fintype.card (Fin M)).toReal.
    rw [Measure.count_singleton, Fintype.card_fin]
    rw [ENNReal.toReal_div]
    simp
  rw [Finset.prod_congr rfl (fun x _ => h_factor x)]
  rw [Finset.prod_const]
  rfl

/-! ## Collision probability collapse `𝔼[1_{f x = f x'}] = 1/M` -/

/-- For random binning at rate `1/M` per input sequence, two distinct sequences
`x ≠ x'` collide with probability exactly `1/M` (Cover–Thomas Theorem 15.4.1). -/
@[entry_point]
theorem binning_collision_prob
    {n M : ℕ} [NeZero M]
    {x x' : Fin n → α} (h : x ≠ x') :
    (binningMeasure α n M).real {f | f x = f x'} = (M : ℝ)⁻¹ := by
  classical
  haveI : MeasurableSingletonClass ((Fin n → α) → Fin M) :=
    Pi.instMeasurableSingletonClass
  haveI : MeasurableSingletonClass (Fin n → α) := Pi.instMeasurableSingletonClass
  -- Step 1: decompose the collision event by the shared hash value.
  -- {f | f x = f x'} = ⋃_{j : Fin M} {f | f x = j ∧ f x' = j} (disjoint union over j).
  -- Step 2: each piece has `Measure.pi`-mass `(1/M)^2 * (Π_{y ≠ x, y ≠ x'} 1) = (1/M)^2`.
  -- Step 3: sum over `j : Fin M` gives `M * (1/M)^2 = 1/M`.
  --
  -- We carry this out by expanding the indicator sum over `Finset.univ`.
  -- The hash-function space `(Fin n → α) → Fin M` is `Fintype`, so we can write:
  --   measure {f | P f} = ∑ f, measure {f} * 1_{P f}.
  set HashFn : Type _ := (Fin n → α) → Fin M with hHashFn_def
  haveI : DecidableEq (Fin n → α) := Classical.decEq _
  haveI : DecidableEq (Fin M) := Classical.decEq _
  haveI : Fintype HashFn := Pi.instFintype
  haveI : DecidableEq HashFn := Classical.decEq _
  -- Expand the measure of the collision event as a finite sum.
  have h_collision_sum :
      (binningMeasure α n M).real {f : HashFn | f x = f x'}
        = ∑ f : HashFn, (binningMeasure α n M).real {f} *
            (if f x = f x' then (1 : ℝ) else 0) := by
    -- {f | f x = f x'} = (Finset.univ.filter (fun f => f x = f x')).toSet.
    -- Use sum_measureReal_singleton.
    have h_finite : {f : HashFn | f x = f x'}.Finite := Set.toFinite _
    set S : Finset HashFn := (Finset.univ : Finset HashFn).filter (fun f => f x = f x')
    have h_S_eq : (S : Set HashFn) = {f : HashFn | f x = f x'} := by
      ext f; simp [S]
    rw [← h_S_eq, ← sum_measureReal_singleton (μ := binningMeasure α n M) S]
    -- Convert filter sum back to univ sum with indicator.
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    split_ifs with hfx
    · rw [mul_one]
    · rw [mul_zero]
  rw [h_collision_sum]
  -- Substitute singleton mass.
  have h_sub : ∀ f : HashFn,
      (binningMeasure α n M).real {f} * (if f x = f x' then (1 : ℝ) else 0)
        = ((M : ℝ)⁻¹) ^ (Fintype.card (Fin n → α)) *
            (if f x = f x' then (1 : ℝ) else 0) := by
    intro f
    rw [binningMeasure_singleton_real n M f]
  rw [Finset.sum_congr rfl (fun f _ => h_sub f)]
  rw [← Finset.mul_sum]
  -- Count #{f : HashFn | f x = f x'}.
  -- These functions are arbitrary on the `|α|^n - 1` indices other than `x'`
  -- and `f x'` is forced to equal `f x`. Equivalently, they correspond to
  -- functions `(Fin n → α) → Fin M` modulo the constraint, which has
  -- `M^{|α|^n - 1}` elements.
  -- Cleaner: count via bijection `{f | f x = f x'} ≃ {g : (Fin n → α) → Fin M | true (no constraint, but reindexed)}`.
  -- Concretely: removing the constraint at one coordinate, the constraint
  -- `f x' = f x` makes `f x'` determined by `f x`. So
  -- `#{f | f x = f x'} = M^{|α|^n - 1}` (free choices at all coords except `x'`).
  --
  -- We give an Equiv: `{f : HashFn // f x = f x'} ≃ ({y : (Fin n → α) // y ≠ x'} → Fin M)`.
  -- The function `y ↦ f y` for `y ≠ x'` is free, and `f x'` is forced = `f x`.
  -- Compute the indicator sum as a cardinality.
  have h_sum_indicator :
      (∑ f : HashFn, (if f x = f x' then (1 : ℝ) else 0))
        = (Fintype.card {f : HashFn // f x = f x'} : ℝ) := by
    rw [Fintype.card_subtype]
    rw [← Finset.sum_filter]
    rw [Finset.sum_const]
    simp
  rw [h_sum_indicator]
  -- Count S' = M^{|α|^n - 1}.
  -- Bijection: `S' ≃ ({y : Fin n → α // y ≠ x'} → Fin M)`.
  --   (forward) f ↦ restriction of f to `{y ≠ x'}`.
  --   (backward) g ↦ define f y := g ⟨y, hyp⟩ if `y ≠ x'`, and f x' := f x = g ⟨x, h.symm⟩.
  let toFun : {f : HashFn // f x = f x'} → ({y : Fin n → α // y ≠ x'} → Fin M) :=
    fun ⟨f, _⟩ y => f y.1
  let invFun : ({y : Fin n → α // y ≠ x'} → Fin M) → {f : HashFn // f x = f x'} :=
    fun g => ⟨fun y => if hy : y = x' then g ⟨x, h⟩ else g ⟨y, hy⟩, by
      -- Need: (if hyp : x = x' then g ⟨x, h⟩ else g ⟨x, hyp⟩) = (if h_x_eq_x' : x' = x' then g ⟨x, h⟩ else g ⟨x', h_x_eq_x'⟩).
      -- LHS: x = x' iff false (h : x ≠ x'), so LHS = g ⟨x, h⟩.
      -- RHS: x' = x' iff true, so RHS = g ⟨x, h⟩.
      simp [h]⟩
  have left_inv : ∀ p, invFun (toFun p) = p := by
    intro ⟨f, hf⟩
    apply Subtype.ext
    funext y
    by_cases hy : y = x'
    · subst hy
      show (if hyy : y = y then f x else f y) = f y
      simp [hf.symm]
    · show (if hyy : y = x' then f x else f y) = f y
      simp [hy]
  have right_inv : ∀ g, toFun (invFun g) = g := by
    intro g
    funext ⟨y, hy⟩
    show (if hy_eq : y = x' then g ⟨x, h⟩ else g ⟨y, hy_eq⟩) = g ⟨y, hy⟩
    simp [hy]
  set e : {f : HashFn // f x = f x'} ≃ ({y : Fin n → α // y ≠ x'} → Fin M) :=
    { toFun := toFun, invFun := invFun, left_inv := left_inv, right_inv := right_inv }
  -- Fintype.card {f // f x = f x'} = Fintype.card ({y // y ≠ x'} → Fin M).
  rw [Fintype.card_congr e]
  -- Compute Fintype.card ({y : Fin n → α // y ≠ x'} → Fin M) = M^{|α|^n - 1}.
  have h_card_pi :
      Fintype.card ({y : Fin n → α // y ≠ x'} → Fin M)
        = M ^ (Fintype.card (Fin n → α) - 1) := by
    rw [Fintype.card_pi, Finset.prod_const, Fintype.card_fin]
    congr 1
    -- Goal: Finset.univ.card = Fintype.card (Fin n → α) - 1.
    rw [Finset.card_univ, Fintype.card_subtype_compl]
    simp
  rw [h_card_pi]
  -- (1/M)^{|α|^n} * (M : ℝ)^{|α|^n - 1} = 1/M.
  -- = (1/M)^{|α|^n} * M^{|α|^n} / M = 1/M, using (1/M)^k * M^k = 1.
  set N : ℕ := Fintype.card (Fin n → α) with hN_def
  -- Goal: ((M : ℝ)⁻¹) ^ N * (M : ℝ) ^ (N - 1) = (M : ℝ)⁻¹.
  -- Need N ≥ 1 (since α nonempty, |α|^n ≥ 1 when n possibly 0?).
  -- Actually N = |α|^n. If n = 0, then |α|^0 = 1. And actually (Fin 0 → α) ≃ Unit (one element).
  -- So N ≥ 1 always.
  have hN_pos : 1 ≤ N := by
    rw [hN_def]
    exact Fintype.card_pos
  -- ((1/M))^N * M^(N-1) = M^(N-1) / M^N = 1/M (using M ≠ 0).
  have hM_ne : (M : ℝ) ≠ 0 := by
    have : NeZero M := inferInstance
    exact_mod_cast NeZero.ne M
  -- Push the cast out.
  push_cast
  -- Goal: ((M : ℝ)⁻¹) ^ N * (M : ℝ) ^ (N - 1) = (M : ℝ)⁻¹.
  rw [inv_pow]
  -- Goal: ((M : ℝ) ^ N)⁻¹ * (M : ℝ) ^ (N - 1) = (M : ℝ)⁻¹.
  -- Use pow_sub₀ to express M^N as M^(N-1) * M directly.
  have hN_eq : (M : ℝ) ^ N = (M : ℝ) ^ (N - 1) * (M : ℝ) := by
    conv_lhs => rw [show N = (N - 1) + 1 from (Nat.sub_add_cancel hN_pos).symm]
    rw [pow_succ]
  rw [hN_eq, mul_inv, mul_comm ((M : ℝ) ^ (N - 1))⁻¹ _, mul_assoc]
  rw [inv_mul_cancel₀ (pow_ne_zero _ hM_ne), mul_one]

end InformationTheory.Shannon
