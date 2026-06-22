import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Sanov.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Sanov's theorem — LDP upper bound (B form)

Cover-Thomas Theorem 11.4.1: for any family `E n ⊆ TypeCountIndex α n`,

```
(1/n) log Q^n({x | typeCount x ∈ E n}) ≤ -D* + ε   (eventually)
```

where `D* = inf_{c ∈ E n} klDivIndex c n Q`.

## Main definitions

* `TypeCountIndex α n` — abbreviation for `α → Fin (n+1)`, the type used to index
  empirical count vectors.
* `typeClassByCount c` — the type class `{x | ∀ a, typeCount x a = c a}`.
* `klDivIndex c n Q` — KL divergence of the rational distribution `c/n` from `Q`,
  defined as `∑ a, (c a / n) * (log (c a / n) - log Q.real {a})`.

## Main statements

* `typeCountIndex_card` — `|TypeCountIndex α n| = (n+1)^|α|` (polynomial cardinality bound).
* `typeClassByCount_Qn_le` — `Q^n(typeClassByCount c) ≤ exp(-n · klDivIndex c n Q)`.
* `typeClassByCount_union_Qn_le_inf` — union-form bound:
  `Q^n(⋃ c ∈ F, T_c) ≤ |F| · exp(-n · D*)`.
* `sanov_ldp_upper_bound` — LDP upper bound with `o(1)` slack via `|α| log(n+1)/n → 0`.

## Implementation notes

* The bound on `typeClassByCount c` is proved self-containedly (index form) rather than
  by reducing to the A-form `typeClass_Qn_le`, because the rational distribution `c/n` may
  have zero components when `c a = 0`, violating the full-support hypothesis.
* The polynomial slack `(|α| log(n+1))/n → 0` is extracted from
  `Real.isLittleO_log_id_atTop`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory Real Filter Asymptotics
open scoped ENNReal NNReal Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Type-count index + polynomial bound -/

/-- Type-count index: `α → Fin (n+1)`, indexing empirical count vectors.
Inconsistent indices (∑ ≠ n) yield an empty type class. -/
abbrev TypeCountIndex (α : Type*) [Fintype α] (n : ℕ) : Type _ := α → Fin (n+1)

instance [Fintype α] (n : ℕ) : Fintype (TypeCountIndex α n) := by
  unfold TypeCountIndex; infer_instance

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Polynomial cardinality bound**: `|TypeCountIndex α n| = (n+1)^|α|`. -/
lemma typeCountIndex_card (n : ℕ) :
    Fintype.card (TypeCountIndex α n) = (n+1) ^ Fintype.card α := by
  show Fintype.card (α → Fin (n+1)) = (n+1) ^ Fintype.card α
  have h := @Fintype.card_fun α (Fin (n+1)) _ _ _
  -- h : Fintype.card (α → Fin (n + 1)) = Fintype.card (Fin (n + 1)) ^ Fintype.card α
  -- but instance may differ; convert.
  convert h using 2
  exact (Fintype.card_fin _).symm


/-! ### Type class by integer counts + Sanov bound -/

/-- **Type class by integer counts** `T(c) := {x | ∀ a, typeCount x a = c a}`. -/
def typeClassByCount {n : ℕ} (c : α → ℕ) : Set (Fin n → α) :=
  { x | ∀ a, typeCount x a = c a }


/-- **KL divergence at an empirical type** (rational form):
`klDivIndex c n Q := ∑ a, (c a / n) · (log (c a / n) - log Q.real{a})`. -/
noncomputable def klDivIndex (c : α → ℕ) (n : ℕ) (Q : Measure α) : ℝ :=
  ∑ a : α, ((c a : ℝ) / n) * (Real.log ((c a : ℝ) / n) - Real.log (Q.real {a}))

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma sum_const_aggr_of_mem_typeClassByCount
    {n : ℕ} {c : α → ℕ} {x : Fin n → α} (hx : x ∈ typeClassByCount c) (f : α → ℝ) :
    (∑ i : Fin n, f (x i)) = ∑ a : α, (c a : ℝ) * f a := by
  classical
  have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ (Finset.univ : Finset α) :=
    fun i _ => Finset.mem_univ _
  have h := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset α)) h_maps f
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  -- typeCount x a = c a (from hx a) ⇒ ((typeCount x a) : ℝ) = (c a : ℝ)
  have h_count : typeCount x a = c a := hx a
  unfold typeCount at h_count
  rw [show ((Finset.univ.filter fun j : Fin n => x j = a).card : ℝ) = (c a : ℝ) by
    exact_mod_cast h_count]

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **Per-point identity** (index form): `x ∈ typeClassByCount c` implies
`∏ i, Q.real {x i} = (∏ a, ((c a : ℝ)/n)^(c a)) · exp(-n · klDivIndex c n Q)`. -/
lemma typeClassByCount_prod_eq
    (Q : Measure α)
    (hQpos : ∀ a : α, 0 < Q.real {a})
    {n : ℕ} (hn : 0 < n) {c : α → ℕ} {x : Fin n → α}
    (hx : x ∈ typeClassByCount c) :
    (∏ i : Fin n, Q.real {x i})
      = (∏ a : α, ((c a : ℝ) / n) ^ (c a)) * Real.exp (-((n : ℝ) * klDivIndex c n Q)) := by
  classical
  -- `c (x i) > 0` for every i, since `x i` itself contributes to `typeCount x (x i) = c (x i)`.
  have hc_xi : ∀ i : Fin n, 0 < c (x i) := by
    intro i
    have : typeCount x (x i) ≥ 1 := by
      unfold typeCount
      have hi_mem : i ∈ (Finset.univ.filter fun j : Fin n => x j = x i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      exact Finset.card_pos.mpr ⟨i, hi_mem⟩
    rw [hx (x i)] at this
    omega
  -- log-difference identity: -(log (c a / n) - log Q.real {a}) = log Q.real {a} - log (c a / n)
  -- valid for `c a > 0` (and Q.real {a} > 0 always).
  -- For each i, exp(-(log (c (x i) / n) - log (Q.real {x i})))
  --        = Q.real {x i} / (c (x i) / n).
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hp_xi_pos : ∀ i : Fin n, 0 < (c (x i) : ℝ) / n :=
    fun i => div_pos (by exact_mod_cast hc_xi i) hn_pos
  have h_exp_neg_diff : ∀ i : Fin n,
      Real.exp (-(Real.log ((c (x i) : ℝ) / n) - Real.log (Q.real {x i})))
        = Q.real {x i} / ((c (x i) : ℝ) / n) := by
    intro i
    have h_neg : -(Real.log ((c (x i) : ℝ) / n) - Real.log (Q.real {x i}))
        = Real.log (Q.real {x i}) - Real.log ((c (x i) : ℝ) / n) := by ring
    rw [h_neg, ← Real.log_div (hQpos (x i)).ne' (hp_xi_pos i).ne']
    exact Real.exp_log (div_pos (hQpos (x i)) (hp_xi_pos i))
  -- aggregate the per-point log into n · klDivIndex.
  -- For each a, define f a := log (c a / n) - log Q.real {a}.
  -- Then sum over i of f(x_i) = ∑ a, c a · f a (by sum_const_aggr).
  -- BUT klDivIndex = ∑ a, (c a / n) · f a = (1/n) · ∑ a, c a · f a.
  -- So sum over i of f(x_i) = n · klDivIndex.
  have h_sum_logdiff :
      (∑ i : Fin n, (Real.log ((c (x i) : ℝ) / n) - Real.log (Q.real {x i})))
        = (n : ℝ) * klDivIndex c n Q := by
    set f : α → ℝ := fun a => Real.log ((c a : ℝ) / n) - Real.log (Q.real {a}) with hf_def
    have h1 : (∑ i : Fin n, f (x i)) = ∑ a : α, (c a : ℝ) * f a :=
      sum_const_aggr_of_mem_typeClassByCount hx f
    rw [h1]
    unfold klDivIndex
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rcases eq_or_ne (c a) 0 with h0 | hc_pos
    · simp [h0]
    · have hc_pos_real : (c a : ℝ) > 0 := by
        have : c a ≥ 1 := Nat.one_le_iff_ne_zero.mpr hc_pos
        exact_mod_cast this
      field_simp
      ring
  -- ∏ Q(x_i) / ∏ (c (x_i) / n) = exp(-n · klDivIndex).
  have h_prod_ratio : (∏ i : Fin n, Q.real {x i} / ((c (x i) : ℝ) / n))
      = Real.exp (-((n : ℝ) * klDivIndex c n Q)) := by
    have h_rhs : Real.exp (-(∑ i : Fin n,
          (Real.log ((c (x i) : ℝ) / n) - Real.log (Q.real {x i}))))
        = ∏ i : Fin n, Q.real {x i} / ((c (x i) : ℝ) / n) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => h_exp_neg_diff i
    rw [← h_rhs, h_sum_logdiff]
  -- ∏ Q(x_i) = (∏ (c (x_i) / n)) · exp(-n · klDivIndex).
  have h_split : (∏ i : Fin n, Q.real {x i})
      = (∏ i : Fin n, Q.real {x i} / ((c (x i) : ℝ) / n))
        * ∏ i : Fin n, ((c (x i) : ℝ) / n) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_mul_cancel₀ _ (hp_xi_pos i).ne']
  rw [h_split, h_prod_ratio]
  -- ∏ i, (c (x i) / n) = ∏ a, (c a / n)^(c a) by `Finset.prod_fiberwise_of_maps_to'`.
  have h_prod_to_count :
      (∏ i : Fin n, ((c (x i) : ℝ) / n)) = ∏ a : α, ((c a : ℝ) / n) ^ (c a) := by
    -- Use `Finset.prod_fiberwise_of_maps_to'` for products
    have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ (Finset.univ : Finset α) :=
      fun i _ => Finset.mem_univ _
    have h := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset α)) h_maps (fun a : α => ((c a : ℝ) / n))
    rw [← h]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Finset.prod_const]
    have : (Finset.univ.filter fun j : Fin n => x j = a).card = c a := hx a
    rw [this]
  rw [h_prod_to_count]
  ring

set_option linter.unusedSectionVars false in
/-- **Sanov upper bound (index form)**: for `c : α → ℕ` with `∑ c a = n`,
`Q^n(typeClassByCount c) ≤ exp(-n · klDivIndex c n Q)`. -/
@[entry_point]
theorem typeClassByCount_Qn_le
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    {n : ℕ} (hn : 0 < n) (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    ((Measure.pi (fun _ : Fin n => Q)) (typeClassByCount (α := α) c)).toReal
      ≤ Real.exp (-((n : ℝ) * klDivIndex c n Q)) := by
  classical
  set T : Finset (Fin n → α) := (typeClassByCount (α := α) c).toFinite.toFinset with hT_def
  have hT_coe : (T : Set (Fin n → α)) = typeClassByCount c := by simp [hT_def]
  set q : α → ℝ := fun a => Q.real {a} with hq_def
  -- Step 1: pi-measure of T as ∑ over T of point-mass.
  have h_pi_singleton_Q : ∀ x : Fin n → α,
      ((Measure.pi (fun _ : Fin n => Q)).real {x}) = ∏ i : Fin n, q (x i) := by
    intro x
    show ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal = ∏ i : Fin n, q (x i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  have h_pi_eq_sum :
      ((Measure.pi (fun _ : Fin n => Q)) (typeClassByCount (α := α) c)).toReal
        = ∑ x ∈ T, ∏ i : Fin n, q (x i) := by
    have h_step : ((Measure.pi (fun _ : Fin n => Q)) (T : Set (Fin n → α))).toReal
        = ∑ x ∈ T, ((Measure.pi (fun _ : Fin n => Q)).real {x}) := by
      rw [← MeasureTheory.measureReal_def]
      rw [← MeasureTheory.sum_measureReal_singleton
        (μ := Measure.pi (fun _ : Fin n => Q)) T]
    rw [← hT_coe, h_step]
    refine Finset.sum_congr rfl fun x _ => h_pi_singleton_Q x
  rw [h_pi_eq_sum]
  -- Step 2: per-`x ∈ T`, ∏ Q(x_i) = (∏ a, (c a / n)^(c a)) · exp(-n · klDivIndex).
  have h_per_point : ∀ x ∈ T,
      ∏ i : Fin n, q (x i)
        = (∏ a : α, ((c a : ℝ) / n) ^ (c a)) * Real.exp (-((n : ℝ) * klDivIndex c n Q)) := by
    intro x hx
    have hxT : x ∈ typeClassByCount c := (Set.Finite.mem_toFinset _).mp hx
    exact typeClassByCount_prod_eq Q hQpos hn hxT
  -- Step 3: factor + bound by `|T_c| · (∏ a, (c a / n)^(c a)) ≤ 1` is NOT what we want;
  -- instead use that `∑ x ∈ T, (∏ a, (c a / n)^(c a)) = |T| · (∏ a, (c a / n)^(c a))` and
  -- this `|T| · ∏ ...` equals `P_c^n(T_c) ≤ P_c^n(univ) = 1` where P_c is the rational measure.
  -- Actually simpler: bound by the multinomial sum over the FULL `Fin n → α` space.
  -- The point: ∑_{x : Fin n → α} ∏_i (c (x i) / n) = (∑ a, c a / n)^n = 1^n = 1 (when ∑ c a = n).
  -- But each `x ∈ T_c` contributes (∏ a, (c a / n)^(c a)), which equals ∏ i, (c (x i) / n).
  -- We bound `∑_{x ∈ T_c} ∏ i, (c (x i) / n) ≤ ∑_{x : Fin n → α} ∏ i, (c (x i) / n) = 1`.
  -- 1) constant-on-T value:
  have h_const_on_T : ∀ x ∈ T,
      (∏ a : α, ((c a : ℝ) / n) ^ (c a)) = ∏ i : Fin n, ((c (x i) : ℝ) / n) := by
    intro x hx
    have hxT : x ∈ typeClassByCount c := (Set.Finite.mem_toFinset _).mp hx
    -- This is the same fiberwise identity as in `typeClassByCount_prod_eq`.
    have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ (Finset.univ : Finset α) :=
      fun i _ => Finset.mem_univ _
    have h := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset α)) h_maps (fun a : α => ((c a : ℝ) / n))
    rw [← h]
    refine (Finset.prod_congr rfl fun a _ => ?_).symm
    rw [Finset.prod_const]
    have : (Finset.univ.filter fun j : Fin n => x j = a).card = c a := hxT a
    rw [this]
  calc (∑ x ∈ T, ∏ i : Fin n, q (x i))
      = ∑ x ∈ T,
          (∏ a : α, ((c a : ℝ) / n) ^ (c a)) * Real.exp (-((n : ℝ) * klDivIndex c n Q)) :=
            Finset.sum_congr rfl h_per_point
    _ = ∑ x ∈ T,
          (∏ i : Fin n, ((c (x i) : ℝ) / n)) * Real.exp (-((n : ℝ) * klDivIndex c n Q)) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            rw [h_const_on_T x hx]
    _ = (∑ x ∈ T, ∏ i : Fin n, ((c (x i) : ℝ) / n))
          * Real.exp (-((n : ℝ) * klDivIndex c n Q)) := by
            rw [← Finset.sum_mul]
    _ ≤ 1 * Real.exp (-((n : ℝ) * klDivIndex c n Q)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          -- ∑_{x ∈ T} ∏ i, (c (x i) / n) ≤ ∑_{x : Fin n → α} ∏ i, (c (x i) / n) = 1.
          have h_total : (∑ x : Fin n → α, ∏ i : Fin n, ((c (x i) : ℝ) / n)) = 1 := by
            classical
            have hsum_one : (∑ a : α, ((c a : ℝ) / n)) = 1 := by
              rw [← Finset.sum_div]
              have : (∑ a : α, (c a : ℝ)) = n := by exact_mod_cast hc_sum
              rw [this]
              field_simp
            -- Use Finset.sum_pow' or equivalently sum_prod_piFinset:
            -- ∑ x : (Fin n → α), ∏ i, g i (x i) = ∏ i, ∑ a, g i a, with g i a := (c a / n).
            have h := Finset.sum_prod_piFinset (ι := Fin n) (κ := α) (R := ℝ)
              (Finset.univ : Finset α) (fun _ a => (c a : ℝ) / n)
            -- h : ∑ f ∈ piFinset (fun _ => Finset.univ), ∏ i, (c (f i) : ℝ) / n
            --    = ∏ i, ∑ a ∈ univ, (c a / n)
            rw [← Fintype.piFinset_univ]
            rw [h]
            rw [show (∏ _i : Fin n, ∑ a : α, ((c a : ℝ) / n)) = 1 by
              rw [Finset.prod_const]
              rw [hsum_one]
              exact one_pow _]
          have h_nonneg : ∀ x : Fin n → α, 0 ≤ ∏ i : Fin n, ((c (x i) : ℝ) / n) := by
            intro x
            exact Finset.prod_nonneg fun i _ => by positivity
          calc (∑ x ∈ T, ∏ i : Fin n, ((c (x i) : ℝ) / n))
              ≤ ∑ x : Fin n → α, ∏ i : Fin n, ((c (x i) : ℝ) / n) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro x _; exact Finset.mem_univ x
                · intro x _ _; exact h_nonneg x
            _ = 1 := h_total
    _ = Real.exp (-((n : ℝ) * klDivIndex c n Q)) := one_mul _

/-! ### Union form upper bound + LDP main statement -/

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- If `∑ c a ≠ n` then `typeClassByCount c = ∅`. -/
lemma typeClassByCount_empty_of_sum_ne {n : ℕ} {c : α → ℕ} (h : (∑ a, c a) ≠ n) :
    (typeClassByCount (α := α) (n := n) c) = ∅ := by
  classical
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  apply h
  -- ∑ a, typeCount x a = n (sum of fiber sizes equals universe size).
  have h_count_sum : (∑ a : α, typeCount x a) = n := by
    unfold typeCount
    have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        x i ∈ (Finset.univ : Finset α) := fun i _ => Finset.mem_univ _
    have h := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset α)) h_maps (fun _ : Fin n => (1 : ℕ))
    -- h : ∑ a, ∑ i ∈ univ with x i = a, 1 = ∑ i, 1
    -- but we want ∑ a, (filter ... ).card = Finset.univ.card.
    have h_filter_card : ∀ a : α,
        ((Finset.univ : Finset (Fin n)).filter fun i => x i = a).card
          = ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter fun i => x i = a), (1 : ℕ) := by
      intro a
      rw [Finset.sum_const, Nat.smul_one_eq_cast]
      rfl
    rw [show (∑ a : α, ((Finset.univ : Finset (Fin n)).filter fun i => x i = a).card)
          = ∑ a : α, ∑ i ∈ ((Finset.univ : Finset (Fin n)).filter fun i => x i = a), (1 : ℕ)
        from Finset.sum_congr rfl fun a _ => h_filter_card a]
    rw [h]
    simp
  rw [← h_count_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (hx a).symm

/-- Union form upper bound: for any `F : Finset (TypeCountIndex α n)`,
`Q^n(⋃ c ∈ F, typeClassByCount c) ≤ ∑ c ∈ F, exp(-n · klDivIndex c n Q)`. -/
theorem typeClassByCount_union_Qn_le
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    {n : ℕ} (hn : 0 < n) (F : Finset (TypeCountIndex α n)) :
    ((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ F, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal
      ≤ ∑ c ∈ F, Real.exp (-((n : ℝ) * klDivIndex (fun a => (c a : ℕ)) n Q)) := by
  classical
  -- Step 1: bound by sum (union-bound on finite union).
  have h_union :
      ((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ F, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal
        ≤ ∑ c ∈ F, ((Measure.pi (fun _ : Fin n => Q))
            (typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal := by
    -- Convert .toReal to measureReal then apply union bound.
    have := MeasureTheory.measureReal_biUnion_finset_le
      (μ := Measure.pi (fun _ : Fin n => Q)) (s := F)
      (f := fun c : TypeCountIndex α n =>
        typeClassByCount (α := α) (fun a => (c a : ℕ)))
    -- this : (Measure.pi ...).real (⋃ c ∈ F, ...) ≤ ∑ c ∈ F, (Measure.pi ...).real (...)
    simpa [MeasureTheory.measureReal_def] using this
  refine h_union.trans ?_
  -- Step 2: each term ≤ exp(-n · klDivIndex).
  refine Finset.sum_le_sum fun c _ => ?_
  -- Case split on whether ∑ c a = n.
  by_cases h_sum : (∑ a : α, ((c a : ℕ))) = n
  · exact typeClassByCount_Qn_le Q hQpos hn _ h_sum
  · -- inconsistent: typeClassByCount = ∅, measure = 0, exp ≥ 0.
    rw [typeClassByCount_empty_of_sum_ne h_sum]
    simp [Real.exp_nonneg]

/-- **inf-form upper bound**: if `∀ c ∈ F, D ≤ klDivIndex c n Q` then
`Q^n(⋃ c ∈ F, typeClassByCount c) ≤ |F| · exp(-n · D)`. -/
@[entry_point]
theorem typeClassByCount_union_Qn_le_inf
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    {n : ℕ} (hn : 0 < n) (F : Finset (TypeCountIndex α n))
    (D : ℝ) (hD : ∀ c ∈ F, D ≤ klDivIndex (fun a => (c a : ℕ)) n Q) :
    ((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ F, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal
      ≤ (F.card : ℝ) * Real.exp (-((n : ℝ) * D)) := by
  classical
  refine (typeClassByCount_union_Qn_le Q hQpos hn F).trans ?_
  -- ∑ c ∈ F, exp(-n · klDivIndex) ≤ ∑ c ∈ F, exp(-n · D) = |F| · exp(-n · D).
  calc (∑ c ∈ F, Real.exp (-((n : ℝ) * klDivIndex (fun a => (c a : ℕ)) n Q)))
      ≤ ∑ c ∈ F, Real.exp (-((n : ℝ) * D)) := by
        refine Finset.sum_le_sum fun c hc => ?_
        -- exp is monotone, and -(n · D) ≥ -(n · klDivIndex) iff D ≤ klDivIndex iff hD.
        apply Real.exp_le_exp.mpr
        have h_n_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        have := hD c hc
        nlinarith [this, h_n_nonneg]
    _ = (F.card : ℝ) * Real.exp (-((n : ℝ) * D)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- `Real.log (n+1) / n → 0` as `n → ∞`. -/
lemma log_succ_div_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
  -- Strategy: log(n+1)/n = (log(n+1)/(n+1)) * ((n+1)/n) → 0 * 1 = 0.
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  -- Compose with (fun n : ℕ => (n : ℝ) + 1).
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop := by
    have := tendsto_natCast_atTop_atTop (R := ℝ)
    exact this.atTop_add tendsto_const_nhds
  have h3 : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    h1.comp h2
  -- We want log(n+1)/n. Show (log(n+1)/n - log(n+1)/(n+1)) → 0, i.e. the difference is small.
  -- log(n+1)/n = log(n+1)/(n+1) · ((n+1)/n) and (n+1)/n → 1.
  have h_ratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    -- (n+1)/n = 1 + 1/n → 1 + 0.
    have h_inv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
        h1.comp tendsto_natCast_atTop_atTop
      convert h2 using 1
      ext n; rw [one_div]
    have h_one : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h_sum : Tendsto (fun n : ℕ => (1 : ℝ) + (1 / (n : ℝ))) atTop (𝓝 (1 + 0)) :=
      h_one.add h_inv
    -- (n+1)/n = 1 + 1/n eventually (for n > 0).
    refine h_sum.congr' ?_ |>.trans ?_
    · refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      field_simp
    · simp
  -- Now (log(n+1)/(n+1)) * ((n+1)/n) → 0 · 1 = 0
  have h4 : Tendsto (fun n : ℕ =>
      (Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1)) * (((n : ℝ) + 1) / (n : ℝ)))
      atTop (𝓝 (0 * 1)) := h3.mul h_ratio
  rw [zero_mul] at h4
  -- Identify the product with log(n+1)/n for n > 0.
  refine h4.congr' ?_
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  field_simp

/-- **Sanov LDP upper bound** (Cover-Thomas Theorem 11.4.1):
`(1/n) log Q^n({x | typeCount x ∈ E n}) ≤ -D + ε` for all large `n`,
provided every `c ∈ E n` satisfies `D ≤ klDivIndex c n Q`.

The bound follows from `polynomial type count · exp(-n D)` via `(|α| log(n+1))/n → 0`. -/
@[entry_point]
theorem sanov_ldp_upper_bound
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (E : ∀ n, Finset (TypeCountIndex α n))
    (D : ℝ)
    (hD : ∀ n, ∀ c ∈ E n, D ≤ klDivIndex (fun a => (c a : ℕ)) n Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, 0 < n →
      0 < ((Measure.pi (fun _ : Fin n => Q))
            (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal →
      (1 / (n : ℝ)) * Real.log (((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal)
        ≤ -D + ε := by
  classical
  -- Goal: find N such that for n ≥ N and the measure of the union is positive,
  -- (1/n) log Q^n(...) ≤ -D + ε.
  -- Strategy: |α| · log(n+1) / n → 0, so eventually it is ≤ ε.
  set K : ℝ := (Fintype.card α : ℝ)
  -- Tendsto K · log(n+1)/n → 0.
  have h_K_log_tendsto : Tendsto (fun n : ℕ => K * (Real.log ((n : ℝ) + 1) / (n : ℝ)))
      atTop (𝓝 (K * 0)) := log_succ_div_tendsto_zero.const_mul K
  rw [mul_zero] at h_K_log_tendsto
  -- Eventually K · log(n+1)/n < ε ⇒ ≤ ε.
  have h_eventually : ∀ᶠ n : ℕ in atTop,
      K * (Real.log ((n : ℝ) + 1) / (n : ℝ)) < ε :=
    h_K_log_tendsto.eventually (gt_mem_nhds hε)
  rw [Filter.eventually_atTop] at h_eventually
  obtain ⟨N, hN⟩ := h_eventually
  refine ⟨N, fun n hn hn_pos hμ_pos => ?_⟩
  have hN_n : N ≤ n := hn
  have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  -- The crux: Q^n(⋃ ∈ E n) ≤ (n+1)^|α| · exp(-n · D).
  have h_card_le : ((E n).card : ℝ) ≤ ((n : ℝ) + 1) ^ Fintype.card α := by
    have h1 : (E n).card ≤ Fintype.card (TypeCountIndex α n) :=
      Finset.card_le_univ _
    have h2 : Fintype.card (TypeCountIndex α n) = (n + 1) ^ Fintype.card α :=
      typeCountIndex_card n
    calc ((E n).card : ℝ)
        ≤ (Fintype.card (TypeCountIndex α n) : ℝ) := by exact_mod_cast h1
      _ = ((n + 1) ^ Fintype.card α : ℝ) := by exact_mod_cast h2
      _ = ((n : ℝ) + 1) ^ Fintype.card α := by norm_cast
  have h_meas_le :
      ((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal
        ≤ ((n : ℝ) + 1) ^ Fintype.card α * Real.exp (-((n : ℝ) * D)) := by
    have hF := typeClassByCount_union_Qn_le_inf Q hQpos hn_pos (E n) D (hD n)
    -- hF : Q^n(⋃) ≤ |E n| · exp(-n · D)
    refine hF.trans ?_
    apply mul_le_mul_of_nonneg_right h_card_le (Real.exp_pos _).le
  -- Take log on both sides (Q^n > 0 by hypothesis). RHS positive.
  have h_rhs_pos : 0 < ((n : ℝ) + 1) ^ Fintype.card α * Real.exp (-((n : ℝ) * D)) := by
    apply mul_pos
    · positivity
    · exact Real.exp_pos _
  have h_log_le : Real.log (((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal)
      ≤ Real.log (((n : ℝ) + 1) ^ Fintype.card α * Real.exp (-((n : ℝ) * D))) := by
    exact Real.log_le_log hμ_pos h_meas_le
  -- log of RHS = |α| log(n+1) - n · D.
  have h_log_rhs : Real.log (((n : ℝ) + 1) ^ Fintype.card α * Real.exp (-((n : ℝ) * D)))
      = K * Real.log ((n : ℝ) + 1) + (-((n : ℝ) * D)) := by
    have hpow_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ Fintype.card α := by positivity
    rw [Real.log_mul hpow_pos.ne' (Real.exp_pos _).ne']
    rw [Real.log_pow, Real.log_exp]
  rw [h_log_rhs] at h_log_le
  -- Now (1/n) · log Q^n ≤ (1/n) · (K log(n+1) - n D) = K log(n+1)/n - D.
  -- We need this ≤ -D + ε, i.e. K log(n+1)/n ≤ ε.
  have h_K_log_eps : K * (Real.log ((n : ℝ) + 1) / (n : ℝ)) ≤ ε := (hN n hN_n).le
  have h_one_div_pos : 0 < (1 / (n : ℝ)) := by positivity
  calc (1 / (n : ℝ)) * Real.log (((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal)
      ≤ (1 / (n : ℝ)) * (K * Real.log ((n : ℝ) + 1) + -((n : ℝ) * D)) :=
          mul_le_mul_of_nonneg_left h_log_le h_one_div_pos.le
    _ = K * (Real.log ((n : ℝ) + 1) / (n : ℝ)) - D := by
          field_simp
          ring
    _ ≤ ε - D := by linarith [h_K_log_eps]
    _ = -D + ε := by ring

end InformationTheory.Shannon
