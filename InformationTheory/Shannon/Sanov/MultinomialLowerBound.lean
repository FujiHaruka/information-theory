import InformationTheory.Shannon.Sanov.RoundedTypeSequence
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Multinomial lower bound (Stirling-free)

The Stirling-free multinomial lower bound for the type class cardinality
(Cover-Thomas 11.1.3):
`(n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ |T_c|`.

## Main statements

* `typeClassByCount_card_ge` — multinomial lower bound (Stirling-free):
  `(n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ |T_c|`.
* `typeClassByCount_Qn_ge` — lower bound on `Q^n(T_c)`:
  `Q^n(T_c) ≥ (n+1)^{-|α|} · exp(-n · klDivIndex c n Q)`.

## Implementation notes

* The multinomial lower bound is proved without Stirling's approximation, using only
  the per-letter inequality `c! · c^k ≤ k! · c^c`.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.),
  Wiley, 2006. Theorem 11.1.3.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Multinomial lower bound (Stirling-free) -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- Per-letter factorial-power inequality:
`c! · c^k ≤ k! · c^c` for all c, k ∈ ℕ. -/
private lemma factorial_pow_swap_le (c k : ℕ) :
    Nat.factorial c * c ^ k ≤ Nat.factorial k * c ^ c := by
  rcases Nat.lt_or_ge k c with hk | hk
  · -- k < c, so k ≤ c.
    have hkc : k ≤ c := hk.le
    have h_desc : c.descFactorial (c - k) ≤ c ^ (c - k) :=
      Nat.descFactorial_le_pow c (c - k)
    have h_fact_eq : Nat.factorial c = Nat.factorial k * c.descFactorial (c - k) := by
      have h := Nat.factorial_mul_descFactorial (n := c) (k := c - k) (Nat.sub_le _ _)
      rw [Nat.sub_sub_self hkc] at h
      exact h.symm
    calc Nat.factorial c * c ^ k
        = Nat.factorial k * c.descFactorial (c - k) * c ^ k := by rw [h_fact_eq]
      _ ≤ Nat.factorial k * c ^ (c - k) * c ^ k :=
            Nat.mul_le_mul_right (c ^ k) (Nat.mul_le_mul_left _ h_desc)
      _ = Nat.factorial k * c ^ c := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hkc]
  · -- c ≤ k: use Nat.factorial_mul_pow_sub_le_factorial.
    have h := Nat.factorial_mul_pow_sub_le_factorial hk
    have h_pow_split : Nat.factorial c * c ^ k
        = (Nat.factorial c * c ^ (k - c)) * c ^ c := by
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
    rw [h_pow_split]
    exact Nat.mul_le_mul_right (c ^ c) h

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- Product over α of per-letter factorial-power inequality.
`(∏ Nat.factorial (c a)) · (∏ (c a)^{k a}) ≤ (∏ (k a)!) · (∏ (c a)^{c a})`. -/
private lemma prod_factorial_pow_swap_le (c k : α → ℕ) :
    (∏ a, Nat.factorial (c a)) * (∏ a, c a ^ k a)
      ≤ (∏ a, Nat.factorial (k a)) * (∏ a, c a ^ c a) := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
    (fun a _ ↦ factorial_pow_swap_le (c a) (k a))

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Max-likelihood for the multinomial coefficient: for c, k both summing to n,
`multinomial univ k · ∏ c(a)^{k a} ≤ multinomial univ c · ∏ c(a)^{c a}`.

(In ratio form: `multinomial univ k / multinomial univ c ≤ ∏ c(a)^{c a - k a}` after div.) -/
private lemma multinomial_pow_le {n : ℕ} (c k : α → ℕ)
    (hc_sum : (∑ a, c a) = n) (hk_sum : (∑ a, k a) = n) :
    Nat.multinomial Finset.univ k * (∏ a, c a ^ k a)
      ≤ Nat.multinomial Finset.univ c * (∏ a, c a ^ c a) := by
  -- (∏ c!)·multinomial c = n! = (∏ k!)·multinomial k.
  have h_c : (∏ a, Nat.factorial (c a)) * Nat.multinomial Finset.univ c
        = Nat.factorial n := by
    rw [Nat.multinomial_spec, hc_sum]
  have h_k : (∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ k
        = Nat.factorial n := by
    rw [Nat.multinomial_spec, hk_sum]
  have h_swap := prod_factorial_pow_swap_le (α := α) c k
  have h_pos : 0 < Nat.factorial n := Nat.factorial_pos _
  -- Multiply h_swap by `multinomial univ c`:
  have step :
      (∏ a, Nat.factorial (c a)) * (∏ a, c a ^ k a) * Nat.multinomial Finset.univ c
        ≤ (∏ a, Nat.factorial (k a)) * (∏ a, c a ^ c a) * Nat.multinomial Finset.univ c :=
    Nat.mul_le_mul_right _ h_swap
  have hL : (∏ a, Nat.factorial (c a)) * (∏ a, c a ^ k a)
        * Nat.multinomial Finset.univ c
      = Nat.factorial n * (∏ a, c a ^ k a) := by
    rw [show (∏ a, Nat.factorial (c a)) * (∏ a, c a ^ k a)
              * Nat.multinomial Finset.univ c
          = ((∏ a, Nat.factorial (c a)) * Nat.multinomial Finset.univ c)
              * (∏ a, c a ^ k a) by ring,
        h_c]
  have hR : (∏ a, Nat.factorial (k a)) * (∏ a, c a ^ c a)
        * Nat.multinomial Finset.univ c
      = (∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ c
        * (∏ a, c a ^ c a) := by ring
  rw [hL, hR] at step
  -- step : n! · (∏ c^k) ≤ (∏ k!) · multinomial univ c · (∏ c^c)
  -- Multiply step by multinomial univ k:
  have step2 :
      Nat.factorial n * (∏ a, c a ^ k a) * Nat.multinomial Finset.univ k
        ≤ (∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ c
            * (∏ a, c a ^ c a) * Nat.multinomial Finset.univ k :=
    Nat.mul_le_mul_right _ step
  have hL2 : Nat.factorial n * (∏ a, c a ^ k a) * Nat.multinomial Finset.univ k
      = Nat.factorial n * (Nat.multinomial Finset.univ k * (∏ a, c a ^ k a)) := by ring
  have hR2 : (∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ c
        * (∏ a, c a ^ c a) * Nat.multinomial Finset.univ k
      = Nat.factorial n * (Nat.multinomial Finset.univ c * (∏ a, c a ^ c a)) := by
    rw [show (∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ c
              * (∏ a, c a ^ c a) * Nat.multinomial Finset.univ k
          = ((∏ a, Nat.factorial (k a)) * Nat.multinomial Finset.univ k)
              * (Nat.multinomial Finset.univ c * (∏ a, c a ^ c a)) by ring,
        h_k]
  rw [hL2, hR2] at step2
  exact Nat.le_of_mul_le_mul_left step2 h_pos

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `multinomial univ c ≤ |T_c|` (the bridge to the multinomial coefficient). -/
private lemma multinomial_le_typeClass_card {n : ℕ} (c : α → ℕ)
    (hc_sum : (∑ a, c a) = n) :
    Nat.multinomial Finset.univ c
      ≤ (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card := by
  classical
  -- Strategy: construct an injection Ψ : Perm (Fin n) → T_c × (Π a, Perm (Fin (c a))).
  -- Then n! = |Perm (Fin n)| ≤ |T_c| · ∏ Nat.factorial (c a). Combined with multinomial_spec
  -- (multinomial · ∏ Nat.factorial (c a) = n!), we get multinomial ≤ |T_c|.
  obtain ⟨x₀, hx₀⟩ := typeClassByCount_nonempty_of_sum c hc_sum
  -- Generic reference equiv  Fin (typeCount x a) ≃ {i // x i = a}.
  have hcard_typeCount : ∀ (x : Fin n → α) (a : α),
      Fintype.card (Fin (typeCount x a)) = Fintype.card {i : Fin n // x i = a} := by
    intro x a
    rw [Fintype.card_fin, Fintype.card_subtype]
    rfl
  let ePos : (x : Fin n → α) → (a : α) → Fin (typeCount x a) ≃ {i : Fin n // x i = a} :=
    fun x a ↦ Fintype.equivOfCardEq (hcard_typeCount x a)
  -- For x ∈ T_c, derive  Fin (c a) ≃ {i // x i = a}.
  let eFibOf : (x : Fin n → α) → (∀ a, typeCount x a = c a) →
      (a : α) → Fin (c a) ≃ {i : Fin n // x i = a} :=
    fun x h a ↦ (Equiv.cast (by rw [h a])).trans (ePos x a)
  let eFib₀ : (a : α) → Fin (c a) ≃ {i : Fin n // x₀ i = a} := eFibOf x₀ hx₀
  -- Given σ, derive x σ ∈ T_c.
  let xOf : Equiv.Perm (Fin n) → (Fin n → α) := fun σ i ↦ x₀ (σ.symm i)
  have h_xOf_mem : ∀ σ : Equiv.Perm (Fin n), xOf σ ∈ typeClassByCount c := by
    intro σ a
    show (Finset.univ.filter (fun i ↦ xOf σ i = a)).card = c a
    have h_eq : Finset.univ.filter (fun i : Fin n ↦ xOf σ i = a)
        = (Finset.univ.filter (fun j : Fin n ↦ x₀ j = a)).map σ.toEmbedding := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.coe_toEmbedding]
      refine ⟨fun h_xi ↦ ⟨σ.symm i, h_xi, Equiv.apply_symm_apply σ i⟩, ?_⟩
      rintro ⟨j, hj, rfl⟩
      show x₀ (σ.symm (σ j)) = a
      rw [Equiv.symm_apply_apply]; exact hj
    rw [h_eq, Finset.card_map]; exact hx₀ a
  let xMem : Equiv.Perm (Fin n) → (typeClassByCount (α := α) (n := n) c) :=
    fun σ ↦ ⟨xOf σ, h_xOf_mem σ⟩
  -- Restriction σ : {j // x₀ j = a} → {i // xOf σ i = a}.
  have h_restrict_mem : ∀ (σ : Equiv.Perm (Fin n)) (a : α) (j : Fin n) (hj : x₀ j = a),
      xOf σ (σ j) = a := fun σ a j hj ↦ by
    show x₀ (σ.symm (σ j)) = a
    rw [Equiv.symm_apply_apply]; exact hj
  -- τOf σ a : Fin (c a) ≃ Fin (c a).
  let τOf : (σ : Equiv.Perm (Fin n)) → (∀ a, Equiv.Perm (Fin (c a))) := fun σ a ↦
    let e1 : Fin (c a) ≃ {j : Fin n // x₀ j = a} := eFib₀ a
    let e2 : {j : Fin n // x₀ j = a} ≃ {i : Fin n // xOf σ i = a} :=
      { toFun := fun j ↦ ⟨σ j.val, h_restrict_mem σ a j.val j.property⟩,
        invFun := fun i ↦ ⟨σ.symm i.val, by
          show x₀ (σ.symm i.val) = a; exact i.property⟩,
        left_inv := fun j ↦ Subtype.ext (Equiv.symm_apply_apply σ j.val),
        right_inv := fun i ↦ Subtype.ext (Equiv.apply_symm_apply σ i.val) }
    let e3 : {i : Fin n // xOf σ i = a} ≃ Fin (c a) := (eFibOf (xOf σ) (h_xOf_mem σ) a).symm
    (e1.trans e2).trans e3
  let Ψ : Equiv.Perm (Fin n) →
      (typeClassByCount (α := α) (n := n) c) × (∀ a, Equiv.Perm (Fin (c a))) :=
    fun σ ↦ (xMem σ, τOf σ)
  -- Recovery formula:
  --   σ j = (eFibOf (xOf σ) ... (x₀ j) (τOf σ (x₀ j) ((eFib₀ (x₀ j)).symm ⟨j, rfl⟩))).val
  have h_recovery : ∀ (σ : Equiv.Perm (Fin n)) (j : Fin n),
      σ j = ((eFibOf (xOf σ) (h_xOf_mem σ) (x₀ j))
              (τOf σ (x₀ j) ((eFib₀ (x₀ j)).symm ⟨j, rfl⟩))).val := by
    intro σ j
    set a := x₀ j
    set k : Fin (c a) := (eFib₀ a).symm ⟨j, (rfl : x₀ j = a)⟩
    -- Unfold τOf σ a applied to k.
    show σ j = ((eFibOf (xOf σ) (h_xOf_mem σ) a) (τOf σ a k)).val
    have hk_eq : (eFib₀ a) k = ⟨j, rfl⟩ := Equiv.apply_symm_apply _ _
    have hτ_unfold : τOf σ a k =
        (eFibOf (xOf σ) (h_xOf_mem σ) a).symm
          ⟨σ j, h_restrict_mem σ a j rfl⟩ := by
      show ((eFib₀ a).trans _).trans _ k = _
      simp only [Equiv.trans_apply]
      rw [hk_eq]
      rfl
    rw [hτ_unfold, Equiv.apply_symm_apply]
  -- Ψ injective.
  have hΨ_inj : Function.Injective Ψ := by
    intro σ σ' hσ
    have hxMem_eq : xMem σ = xMem σ' := (Prod.mk.injEq ..).mp hσ |>.1
    have hx_eq : xOf σ = xOf σ' := congrArg Subtype.val hxMem_eq
    have hτ_eq : τOf σ = τOf σ' := (Prod.mk.injEq ..).mp hσ |>.2
    refine Equiv.ext (fun j ↦ ?_)
    rw [h_recovery σ j, h_recovery σ' j]
    -- Goal: ((eFibOf (xOf σ) (h_xOf_mem σ) (x₀ j)) (τOf σ ...)).val
    --     = ((eFibOf (xOf σ') (h_xOf_mem σ') (x₀ j)) (τOf σ' ...)).val.
    -- Use hxMem_eq and hτ_eq to align both sides as members of the same Subtype.
    -- The most robust way: show the result via `Subtype.ext` after using the membership-coercion.
    -- The Subtype-valued LHS RHS, after taking .val, only require equality at the value level.
    -- We use the fact that `eFibOf x hx a m` as a Subtype's `.val` is independent of `hx`
    --   (only x matters), and depends on x via Fintype.equivOfCardEq.
    -- The cleanest path: substitute xOf σ with xOf σ'
    --   (then membership proofs become equal by Subsingleton).
    set j₀ := (⟨j, (rfl : x₀ j = x₀ j)⟩ : {i : Fin n // x₀ i = x₀ j})
    set k := (eFib₀ (x₀ j)).symm j₀
    -- After unfolding the τ-applications, replace τOf σ with τOf σ' via hτ_eq.
    have h_tau_at : τOf σ (x₀ j) k = τOf σ' (x₀ j) k := by rw [hτ_eq]
    rw [h_tau_at]
    -- Now both sides:
    --   (eFibOf (xOf σ) (h_xOf_mem σ) a (τOf σ' a k)).val vs (eFibOf (xOf σ') ...).val.
    -- The pair `(xOf σ, h_xOf_mem σ)` equals `(xOf σ', h_xOf_mem σ')` via `hxMem_eq`.
    -- Use Sigma to consolidate the dependency.
    have h_pair_eq : (⟨xOf σ, h_xOf_mem σ⟩ : (typeClassByCount c)) = ⟨xOf σ', h_xOf_mem σ'⟩ :=
      hxMem_eq
    -- Apply this via `congr` of the auxiliary function.
    let g : (typeClassByCount (α := α) (n := n) c) → Fin n := fun y ↦
      ((eFibOf y.val y.property (x₀ j)) (τOf σ' (x₀ j) k)).val
    have hg_eq : g ⟨xOf σ, h_xOf_mem σ⟩ = g ⟨xOf σ', h_xOf_mem σ'⟩ := by
      congr 1
    exact hg_eq
  -- Cardinality calculation.
  have h_card_le := Fintype.card_le_of_injective Ψ hΨ_inj
  have hL : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hR : Fintype.card ((typeClassByCount (α := α) (n := n) c)
        × (∀ a, Equiv.Perm (Fin (c a))))
      = (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card
          * ∏ a, Nat.factorial (c a) := by
    rw [Fintype.card_prod, Fintype.card_pi]
    congr 1
    · exact (Set.Finite.card_toFinset _).symm
    · refine Finset.prod_congr rfl fun a _ ↦ ?_
      rw [Fintype.card_perm, Fintype.card_fin]
  rw [hL, hR] at h_card_le
  -- h_card_le : n! ≤ |T_c| · ∏ Nat.factorial (c a).
  have h_spec : (∏ a, Nat.factorial (c a)) * Nat.multinomial Finset.univ c = Nat.factorial n := by
    rw [Nat.multinomial_spec, hc_sum]
  have h_prod_pos : 0 < ∏ a, Nat.factorial (c a) :=
    Finset.prod_pos fun _ _ ↦ Nat.factorial_pos _
  -- multinomial · ∏ Nat.factorial (c a) = n! ≤ |T_c| · ∏ Nat.factorial (c a).
  -- So multinomial ≤ |T_c|.
  have h_mul_le : (∏ a, Nat.factorial (c a)) * Nat.multinomial Finset.univ c
      ≤ (∏ a, Nat.factorial (c a)) *
        (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card := by
    rw [h_spec]
    -- |T_c| · ∏ Nat.factorial (c a) ≥ n! = ∏ Nat.factorial (c a) · multinomial.
    -- h_card_le : n! ≤ |T_c| · ∏ Nat.factorial (c a).
    calc Nat.factorial n ≤
          (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card *
            ∏ a, Nat.factorial (c a) :=
          h_card_le
      _ = (∏ a, Nat.factorial (c a))
            * (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card := by ring
  exact Nat.le_of_mul_le_mul_left h_mul_le h_prod_pos

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- ℝ form of `multinomial_pow_le`. -/
private lemma multinomial_pow_le_real {n : ℕ} (c k : α → ℕ)
    (hc_sum : (∑ a, c a) = n) (hk_sum : (∑ a, k a) = n) :
    (Nat.multinomial Finset.univ k : ℝ) * (∏ a, (c a : ℝ) ^ k a)
      ≤ (Nat.multinomial Finset.univ c : ℝ) * (∏ a, (c a : ℝ) ^ c a) := by
  have h := multinomial_pow_le (α := α) c k hc_sum hk_sum
  have :
      ((Nat.multinomial Finset.univ k * (∏ a, c a ^ k a) : ℕ) : ℝ)
        ≤ ((Nat.multinomial Finset.univ c * (∏ a, c a ^ c a) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at this
  exact this

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The number of types (count vectors `c : α → ℕ` with `∑ a, c a = n`, equivalently the
elements of `piAntidiag univ n`) is at most `(n+1)^{|α|}`. -/
theorem numTypes_le (n : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset α) n).card
      ≤ (n + 1) ^ Fintype.card α := by
  classical
  -- Build embedding piAntidiag univ n ↪ (α → Fin (n+1)).
  have h_bound : ∀ k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
      ∀ a, k a ≤ n := by
    intros k hk_mem a
    have hk_sum := (Finset.mem_piAntidiag.mp hk_mem).1
    have hka : k a ≤ ∑ a', k a' := Finset.single_le_sum (f := k)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    rw [hk_sum] at hka
    exact hka
  let φ : (α → ℕ) → (α → Fin (n+1)) :=
    fun k a ↦ ⟨min (k a) n, by
      have hmin : min (k a) n ≤ n := Nat.min_le_right _ _
      omega⟩
  have h_inj_on : Set.InjOn φ (Finset.piAntidiag (Finset.univ : Finset α) n) := by
    intros k₁ hk₁ k₂ hk₂ heq
    funext a
    have heqa := congrFun heq a
    have h_min1 : k₁ a = min (k₁ a) n := by
      have := h_bound k₁ hk₁ a; omega
    have h_min2 : k₂ a = min (k₂ a) n := by
      have := h_bound k₂ hk₂ a; omega
    have : min (k₁ a) n = min (k₂ a) n := by
      have := Fin.mk.inj_iff.mp heqa
      exact this
    omega
  have h_card_pow : Fintype.card (α → Fin (n+1)) = (n+1) ^ Fintype.card α := by
    have h := @Fintype.card_fun α (Fin (n+1)) _ _ _
    rw [Fintype.card_fin] at h
    exact h
  calc (Finset.piAntidiag (Finset.univ : Finset α) n).card
      = ((Finset.piAntidiag (Finset.univ : Finset α) n).image φ).card :=
        (Finset.card_image_of_injOn h_inj_on).symm
    _ ≤ (Finset.univ : Finset (α → Fin (n+1))).card := Finset.card_le_card (by
        intros _ _; exact Finset.mem_univ _)
    _ = Fintype.card (α → Fin (n+1)) := by rw [Finset.card_univ]
    _ = (n+1) ^ Fintype.card α := h_card_pow

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem prod_div_pow_eq_prod_pow_div_npow_of_sum
    {n : ℕ} (c k : α → ℕ) (hk_sum : (∑ a, k a) = n) :
    ∏ a, ((c a : ℝ) / n) ^ (k a) = (∏ a, (c a : ℝ) ^ (k a)) / (n : ℝ) ^ n := by
  rw [show ∏ a, ((c a : ℝ) / n) ^ (k a)
          = ∏ a, ((c a : ℝ) ^ (k a) / (n : ℝ) ^ (k a)) from
      Finset.prod_congr rfl (fun a _ ↦ div_pow _ _ _)]
  rw [Finset.prod_div_distrib]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum, hk_sum]

theorem inv_mul_div_le_of_one_le_mul_mul_div
    {B M P x : ℝ} (hB : 0 < B) (hP : 0 < P) (hx : 0 < x)
    (h : (1 : ℝ) ≤ B * (M * (P / x))) :
    B⁻¹ * (x / P) ≤ M := by
  have h_npow_le : x ≤ B * M * P := by
    have := mul_le_mul_of_nonneg_right h hx.le
    rw [one_mul] at this
    have h_rhs_eq : B * (M * (P / x)) * x = B * M * P := by field_simp
    rw [h_rhs_eq] at this
    exact this
  have h_div : x / P ≤ B * M := by
    rw [div_le_iff₀ hP]
    linarith [h_npow_le]
  rw [← div_le_iff₀' hB] at h_div
  rw [show B⁻¹ * (x / P) = (x / P) / B by field_simp]
  exact h_div

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem multinomial_mul_prod_ratio_pow_le
    {n : ℕ} (c k : α → ℕ) (hc_sum : (∑ a, c a) = n) (hk_sum : (∑ a, k a) = n) :
    (Nat.multinomial Finset.univ k : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (k a)
      ≤ (Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a) := by
  rw [prod_div_pow_eq_prod_pow_div_npow_of_sum c k hk_sum,
    prod_div_pow_eq_prod_pow_div_npow_of_sum c c hc_sum]
  rw [show (Nat.multinomial Finset.univ k : ℝ)
          * ((∏ a, (c a : ℝ) ^ (k a)) / (n : ℝ) ^ n)
        = ((Nat.multinomial Finset.univ k : ℝ) * (∏ a, (c a : ℝ) ^ (k a)))
            / (n : ℝ) ^ n by ring]
  rw [show (Nat.multinomial Finset.univ c : ℝ)
          * ((∏ a, (c a : ℝ) ^ (c a)) / (n : ℝ) ^ n)
        = ((Nat.multinomial Finset.univ c : ℝ) * (∏ a, (c a : ℝ) ^ (c a)))
            / (n : ℝ) ^ n by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact multinomial_pow_le_real c k hc_sum hk_sum

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Multinomial lower bound:
`(n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ |T_c|`. -/
theorem typeClassByCount_card_ge
    {n : ℕ} (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹ *
        ((n : ℝ) ^ n / ∏ a : α, ((c a : ℝ) ^ (c a)))
      ≤ ((typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card : ℝ) := by
  classical
  -- Goal: (n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ |T_c|.
  -- Chain: multinomial univ c ≤ |T_c| ; (n+1)^{-|α|} · n^n / ∏ c^c ≤ multinomial univ c.
  have h_main : ((Nat.multinomial Finset.univ c : ℝ))
        ≤ ((typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card : ℝ) := by
    have h := multinomial_le_typeClass_card (α := α) c hc_sum
    exact_mod_cast h
  refine le_trans ?_ h_main
  -- Now: (n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ multinomial univ c.
  -- This is equivalent to: n^n ≤ multinomial univ c · ∏ c(a)^{c(a)} · (n+1)^{|α|}.
  -- Equivalent (dividing by n^n on both sides): 1 ≤ (n+1)^{|α|} · multinomial univ c · ∏ (c/n)^c.
  -- This follows from 1 = ∑_k multinomial univ k · ∏ (c/n)^k ≤ (n+1)^{|α|} · max term.
  -- Edge case: n = 0. Then c = 0 everywhere, ∏ c(a)^{c(a)} = 1, n^n = 0^0 = 1.
  -- multinomial univ 0 = 1, LHS = 1, RHS = 1. OK.
  -- General path.
  by_cases hn : n = 0
  · -- n = 0: c a = 0 for all a, multinomial univ c = 1.
    subst hn
    have hc_zero : ∀ a, c a = 0 := fun a ↦ by
      have : c a ≤ ∑ a', c a' := Finset.single_le_sum (f := c)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
      omega
    have h_prod_one : ∏ a : α, ((c a : ℝ) ^ (c a)) = 1 := by
      refine Finset.prod_eq_one fun a _ ↦ ?_
      rw [hc_zero a]; simp
    -- multinomial univ c = 1, so the goal `... ≤ multinomial univ c` is `1 ≤ 1`.
    have h_multinomial_one : Nat.multinomial Finset.univ c = 1 := by
      unfold Nat.multinomial
      have h_facts : ∀ a, Nat.factorial (c a) = 1 := fun a ↦ by
        rw [hc_zero a]; rfl
      rw [Finset.prod_congr rfl (fun a _ ↦ h_facts a), Finset.prod_const_one]
      rw [hc_sum]
      decide
    rw [h_prod_one]
    have h_mc : (Nat.multinomial Finset.univ c : ℝ) = 1 := by
      exact_mod_cast h_multinomial_one
    rw [h_mc]
    simp
  · -- n ≥ 1.
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
    have hn_real_succ_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    -- Step 1: ∑_a (c a / n) = 1 (in ℝ).
    have h_sum_one : (∑ a, (c a : ℝ) / n) = 1 := by
      rw [← Finset.sum_div]
      have h_cast : (∑ a, (c a : ℝ)) = (n : ℝ) := by exact_mod_cast hc_sum
      rw [h_cast]; field_simp
    -- Step 2: (∑_a (c a / n))^n = 1.
    have h_pow_one : (∑ a, (c a : ℝ) / n) ^ n = 1 := by rw [h_sum_one]; simp
    -- Step 3: Apply multinomial theorem.
    have h_mn := Finset.sum_pow_eq_sum_piAntidiag (R := ℝ)
      (Finset.univ : Finset α) (fun a ↦ (c a : ℝ) / n) n
    -- h_mn: (∑ a, (c a)/n)^n = ∑ k ∈ piAntidiag univ n, multinomial univ k · ∏ (c/n)^{k a}
    rw [h_pow_one] at h_mn
    -- h_mn : 1 = ∑ k ∈ piAntidiag univ n, multinomial univ k * ∏ (c/n)^{k a}
    -- Step 4: c ∈ piAntidiag univ n.
    have hc_mem : c ∈ Finset.piAntidiag (Finset.univ : Finset α) n := by
      rw [Finset.mem_piAntidiag]
      refine ⟨hc_sum, fun a _ ↦ Finset.mem_univ a⟩
    -- Step 5: each term ≤ multinomial univ c · ∏ (c/n)^{c a} (max-likelihood).
    have h_term_max : ∀ k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
        (Nat.multinomial Finset.univ k : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (k a)
          ≤ (Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a) := by
      intros k hk_mem
      have hk_sum := (Finset.mem_piAntidiag.mp hk_mem).1
      exact multinomial_mul_prod_ratio_pow_le c k hc_sum hk_sum
    -- Step 6: all terms ≥ 0.
    have h_term_nn : ∀ k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
        0 ≤ (Nat.multinomial Finset.univ k : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (k a) := by
      intros k _
      refine mul_nonneg (by positivity) (Finset.prod_nonneg fun a _ ↦ by positivity)
    -- Step 7: sum ≤ card · max.
    have h_card_bound :
        (1 : ℝ) ≤ ((Finset.piAntidiag (Finset.univ : Finset α) n).card : ℝ)
          * ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)) := by
      rw [h_mn]
      calc (∑ k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
              (Nat.multinomial Finset.univ k : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (k a))
          ≤ ∑ _k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
              ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)) :=
            Finset.sum_le_sum h_term_max
        _ = ((Finset.piAntidiag (Finset.univ : Finset α) n).card : ℝ)
              * ((Nat.multinomial Finset.univ c : ℝ)
                * ∏ a, ((c a : ℝ) / n) ^ (c a)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    -- Step 8: card ≤ (n+1)^|α|.
    have h_card_le : ((Finset.piAntidiag (Finset.univ : Finset α) n).card : ℝ)
        ≤ ((n : ℝ) + 1) ^ Fintype.card α := by
      have := numTypes_le (α := α) n
      have h_cast : (((n + 1) ^ Fintype.card α : ℕ) : ℝ)
          = ((n : ℝ) + 1) ^ Fintype.card α := by push_cast; ring
      have := (Nat.cast_le (α := ℝ)).mpr this
      rwa [h_cast] at this
    -- Step 9: combine.
    -- From h_card_bound: 1 ≤ K · M (where K = card piAntidiag, M = mult · ∏(c/n)^c).
    -- From h_card_le: K ≤ (n+1)^|α|.
    -- So 1 ≤ (n+1)^|α| · M, i.e., (n+1)^{-|α|} ≤ M = mult · ∏(c/n)^c.
    have h_M_nn : 0 ≤ (Nat.multinomial Finset.univ c : ℝ)
        * ∏ a, ((c a : ℝ) / n) ^ (c a) := h_term_nn c hc_mem
    have h_chain : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ Fintype.card α
        * ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)) := by
      calc (1 : ℝ) ≤ ((Finset.piAntidiag (Finset.univ : Finset α) n).card : ℝ)
              * ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)) :=
            h_card_bound
        _ ≤ ((n : ℝ) + 1) ^ Fintype.card α
              * ((Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)) :=
            mul_le_mul_of_nonneg_right h_card_le h_M_nn
    -- Step 10: turn into the goal.
    -- Goal: (n+1)^{-|α|} · n^n / ∏ c(a)^{c(a)} ≤ multinomial univ c.
    -- We have: 1 ≤ (n+1)^|α| · multinomial univ c · ∏ (c/n)^c
    --          = (n+1)^|α| · multinomial univ c · ∏ c^c / n^n.
    -- ⟹ n^n ≤ (n+1)^|α| · multinomial univ c · ∏ c^c.
    -- ⟹ n^n / (∏ c^c) ≤ (n+1)^|α| · multinomial univ c.
    -- ⟹ (n+1)^{-|α|} · n^n / ∏ c^c ≤ multinomial univ c.
    -- First rewrite ∏ (c/n)^c = ∏ c^c / n^n.
    have h_prod_split : ∏ a, ((c a : ℝ) / n) ^ (c a)
        = (∏ a, (c a : ℝ) ^ (c a)) / (n : ℝ) ^ n :=
      prod_div_pow_eq_prod_pow_div_npow_of_sum c c hc_sum
    rw [h_prod_split] at h_chain
    -- h_chain : 1 ≤ (n+1)^|α| · multinomial · (∏ c^c / n^n).
    -- Multiply by n^n / ∏ c^c (positive).
    -- But first: need ∏ c^c > 0? Could be 0 if some c(a) = 0 — no, 0^0 = 1, so each factor ≥ 1
    -- when c(a) ≥ 1. When c(a) = 0, factor = 0^0 = 1. So all factors ≥ 1.
    -- Actually for c(a) = 0, (c a : ℝ)^(c a) = 0^0 = 1 in ℝ (Real convention).
    -- So ∏ ≥ 1 > 0.
    have h_prod_cc_pos : (0 : ℝ) < ∏ a, (c a : ℝ) ^ (c a) := by
      refine Finset.prod_pos fun a _ ↦ ?_
      rcases Nat.eq_zero_or_pos (c a) with h0 | hp
      · rw [h0]; simp
      · exact pow_pos (by exact_mod_cast hp) _
    -- Manipulate h_chain into the goal:
    -- from 1 ≤ (n+1)^|α| · (M · (P / n^n)) derive (n+1)^{-|α|} · (n^n / P) ≤ M.
    exact inv_mul_div_le_of_one_le_mul_mul_div
      (pow_pos hn_real_succ_pos _) h_prod_cc_pos (pow_pos hn_real_pos _) h_chain

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Reverse bridge to the multinomial coefficient: `|T_c| ≤ multinomial univ c`. -/
private lemma typeClass_card_le_multinomial {n : ℕ} (c : α → ℕ)
    (hc_sum : (∑ a, c a) = n) :
    (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card
      ≤ Nat.multinomial Finset.univ c := by
  classical
  -- Strategy: build an injection Φ : T_c × (Π a, Perm (Fin (c a))) → Perm (Fin n).
  -- Then |T_c| · ∏ (c a)! ≤ n!, and with multinomial_spec (∏ (c a)! · multinomial = n!)
  -- we get |T_c| ≤ multinomial.
  obtain ⟨x₀, hx₀⟩ := typeClassByCount_nonempty_of_sum c hc_sum
  have hcard_typeCount : ∀ (x : Fin n → α) (a : α),
      Fintype.card (Fin (typeCount x a)) = Fintype.card {i : Fin n // x i = a} := by
    intro x a
    rw [Fintype.card_fin, Fintype.card_subtype]
    rfl
  let ePos : (x : Fin n → α) → (a : α) → Fin (typeCount x a) ≃ {i : Fin n // x i = a} :=
    fun x a ↦ Fintype.equivOfCardEq (hcard_typeCount x a)
  let eFibOf : (x : Fin n → α) → (∀ a, typeCount x a = c a) →
      (a : α) → Fin (c a) ≃ {i : Fin n // x i = a} :=
    fun x h a ↦ (Equiv.cast (by rw [h a])).trans (ePos x a)
  let eFib₀ : (a : α) → Fin (c a) ≃ {i : Fin n // x₀ i = a} := eFibOf x₀ hx₀
  -- Shared opening `A : Fin n ≃ Σ a, Fin (c a)` (depends only on the reference `x₀`).
  let A : Fin n ≃ (Σ a, Fin (c a)) :=
    (Equiv.sigmaFiberEquiv x₀).symm.trans (Equiv.sigmaCongrRight (fun a ↦ (eFib₀ a).symm))
  -- Closing `Cof x : Σ a, Fin (c a) ≃ Fin n`, depending on `x ∈ T_c`.
  let Cof : (x : typeClassByCount (α := α) (n := n) c) → ((Σ a, Fin (c a)) ≃ Fin n) :=
    fun x ↦ (Equiv.sigmaCongrRight (eFibOf x.val x.property)).trans
      (Equiv.sigmaFiberEquiv (x.val : Fin n → α))
  let Φ : (typeClassByCount (α := α) (n := n) c) × (∀ a, Equiv.Perm (Fin (c a)))
      → Equiv.Perm (Fin n) :=
    fun p ↦ A.trans ((Equiv.sigmaCongrRight p.2).trans (Cof p.1))
  -- `Cof x` lands in the fiber tagged by the first coordinate.
  have key : ∀ (x : typeClassByCount (α := α) (n := n) c) (s : Σ a, Fin (c a)),
      x.val (Cof x s) = s.1 := fun x s ↦ (eFibOf x.val x.property s.1 s.2).2
  -- Recovery of `x` from `σ = Φ p`: `x.val (Φ p j) = x₀ j`.
  have hΦ_x : ∀ (p : (typeClassByCount (α := α) (n := n) c) × (∀ a, Equiv.Perm (Fin (c a))))
      (j : Fin n), p.1.val (Φ p j) = x₀ j := by
    intro p j
    have e1 : Φ p j = Cof p.1 (Equiv.sigmaCongrRight p.2 (A j)) := rfl
    rw [e1, key p.1 (Equiv.sigmaCongrRight p.2 (A j))]
    rfl
  -- Left cancellation of `A`.
  have cancelA : ∀ (P Q : (Σ a, Fin (c a)) ≃ Fin n), A.trans P = A.trans Q → P = Q := by
    intro P Q h
    have := congrArg (fun e ↦ A.symm.trans e) h
    simpa only [← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans] using this
  -- Injectivity of `Φ`.
  have hΦ_inj : Function.Injective Φ := by
    rintro ⟨x, τ⟩ ⟨x', τ'⟩ hΦ
    have hxx : x = x' := by
      apply Subtype.ext
      funext i
      have h1 : x.val i = x₀ ((Φ (x, τ)).symm i) := by
        have h := hΦ_x (x, τ) ((Φ (x, τ)).symm i)
        rwa [Equiv.apply_symm_apply] at h
      have h2 : x'.val i = x₀ ((Φ (x', τ')).symm i) := by
        have h := hΦ_x (x', τ') ((Φ (x', τ')).symm i)
        rwa [Equiv.apply_symm_apply] at h
      rw [h1, h2, hΦ]
    have hΦ' : A.trans ((Equiv.sigmaCongrRight τ).trans (Cof x))
        = A.trans ((Equiv.sigmaCongrRight τ').trans (Cof x')) := hΦ
    rw [hxx] at hΦ'
    have hP : (Equiv.sigmaCongrRight τ).trans (Cof x')
        = (Equiv.sigmaCongrRight τ').trans (Cof x') := cancelA _ _ hΦ'
    -- Right cancellation of `Cof x'`.
    have hSCR : Equiv.sigmaCongrRight τ = Equiv.sigmaCongrRight τ' := by
      have := congrArg (fun e ↦ e.trans (Cof x').symm) hP
      simpa only [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] using this
    have hτ : τ = τ' :=
      Equiv.Perm.sigmaCongrRightHom_injective (β := fun a ↦ Fin (c a))
        (by simpa only [Equiv.Perm.sigmaCongrRightHom_apply] using hSCR)
    exact Prod.ext hxx hτ
  -- Cardinality bookkeeping.
  have h_card_le := Fintype.card_le_of_injective Φ hΦ_inj
  have hL : Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial n := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have hR : Fintype.card ((typeClassByCount (α := α) (n := n) c)
        × (∀ a, Equiv.Perm (Fin (c a))))
      = (typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card
          * ∏ a, Nat.factorial (c a) := by
    rw [Fintype.card_prod, Fintype.card_pi]
    congr 1
    · exact (Set.Finite.card_toFinset _).symm
    · refine Finset.prod_congr rfl fun a _ ↦ ?_
      rw [Fintype.card_perm, Fintype.card_fin]
  rw [hR, hL] at h_card_le
  -- h_card_le : |T_c| · ∏ (c a)! ≤ n!.
  have h_spec : (∏ a, Nat.factorial (c a)) * Nat.multinomial Finset.univ c = Nat.factorial n := by
    rw [Nat.multinomial_spec, hc_sum]
  have h_prod_pos : 0 < ∏ a, Nat.factorial (c a) :=
    Finset.prod_pos fun _ _ ↦ Nat.factorial_pos _
  rw [← h_spec, mul_comm (∏ a, Nat.factorial (c a)) (Nat.multinomial Finset.univ c)] at h_card_le
  exact Nat.le_of_mul_le_mul_right h_card_le h_prod_pos

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Single-term multinomial bound: `multinomial univ c ≤ n^n / ∏ c(a)^{c(a)}`. -/
private lemma multinomial_le_pow_div_prod {n : ℕ} (c : α → ℕ)
    (hc_sum : (∑ a, c a) = n) :
    (Nat.multinomial Finset.univ c : ℝ)
      ≤ (n : ℝ) ^ n / ∏ a : α, ((c a : ℝ) ^ (c a)) := by
  classical
  have h_prod_cc_pos : (0 : ℝ) < ∏ a : α, (c a : ℝ) ^ (c a) := by
    refine Finset.prod_pos fun a _ ↦ ?_
    rcases Nat.eq_zero_or_pos (c a) with h0 | hp
    · rw [h0]; simp
    · exact pow_pos (by exact_mod_cast hp) _
  have hN_pos : (0 : ℝ) < (n : ℝ) ^ n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]; simp
    · exact pow_pos (by exact_mod_cast hn) _
  -- (∑ a, c a / n)^n = 1 for all n (n = 0 via `_ ^ 0 = 1`, n > 0 via ∑ = 1).
  have h_base_one : (∑ a, (c a : ℝ) / n) ^ n = 1 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]; simp
    · have h_sum : (∑ a, (c a : ℝ) / n) = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ a, (c a : ℝ)) = (n : ℝ) from by exact_mod_cast hc_sum]
        have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
      rw [h_sum, one_pow]
  -- Multinomial theorem: 1 = ∑ k ∈ piAntidiag univ n, multinomial univ k · ∏ (c/n)^{k a}.
  have h_mn := Finset.sum_pow_eq_sum_piAntidiag (R := ℝ)
    (Finset.univ : Finset α) (fun a ↦ (c a : ℝ) / n) n
  rw [h_base_one] at h_mn
  -- c ∈ piAntidiag univ n.
  have hc_mem : c ∈ Finset.piAntidiag (Finset.univ : Finset α) n := by
    rw [Finset.mem_piAntidiag]
    refine ⟨hc_sum, fun a _ ↦ Finset.mem_univ a⟩
  -- Single term ≤ sum (all terms nonneg).
  have h_single : (Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a)
      ≤ ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset α) n,
          (Nat.multinomial Finset.univ k : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (k a) :=
    Finset.single_le_sum
      (f := fun k ↦ (Nat.multinomial Finset.univ k : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (k a))
      (fun k _ ↦ mul_nonneg (by positivity)
        (Finset.prod_nonneg fun a _ ↦ by positivity))
      hc_mem
  have h_le_one : (Nat.multinomial Finset.univ c : ℝ) * ∏ a, ((c a : ℝ) / n) ^ (c a) ≤ 1 :=
    h_single.trans (le_of_eq h_mn.symm)
  rw [prod_div_pow_eq_prod_pow_div_npow_of_sum c c hc_sum] at h_le_one
  rw [← mul_div_assoc, div_le_one hN_pos] at h_le_one
  rw [le_div_iff₀ h_prod_cc_pos]
  exact h_le_one

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Multinomial upper bound (method of types):
`|T_c| ≤ n^n / ∏ c(a)^{c(a)}`. -/
theorem typeClassByCount_card_le {n : ℕ} (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    ((typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card : ℝ)
      ≤ (n : ℝ) ^ n / ∏ a : α, ((c a : ℝ) ^ (c a)) := by
  have h1 : ((typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card : ℝ)
      ≤ (Nat.multinomial Finset.univ c : ℝ) := by
    exact_mod_cast typeClass_card_le_multinomial c hc_sum
  exact h1.trans (multinomial_le_pow_div_prod c hc_sum)

omit [Nonempty α] in
/-- Lower bound on `Q^n(T_c)`: `Q^n(T_c) ≥ (n+1)^{-|α|} · exp(-n · klDivIndex c n Q)`. -/
theorem typeClassByCount_Qn_ge
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    {n : ℕ} (hn : 0 < n) (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹ * Real.exp (-((n : ℝ) * klDivIndex c n Q))
      ≤ ((Measure.pi (fun _ : Fin n ↦ Q)) (typeClassByCount (α := α) c)).toReal := by
  classical
  -- Setup.
  set T : Finset (Fin n → α) := (typeClassByCount (α := α) c).toFinite.toFinset with hT_def
  have hT_coe : (T : Set (Fin n → α)) = typeClassByCount c := by simp [hT_def]
  set qm : α → ℝ := fun a ↦ Q.real {a} with hqm_def
  set N : ℝ := (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹ with hN_def
  -- Step 1: Q^n(T_c) (set form) = sum over T of ∏ Q(x_i).
  have h_pi_singleton_Q : ∀ x : Fin n → α,
      ((Measure.pi (fun _ : Fin n ↦ Q)).real {x}) = ∏ i : Fin n, qm (x i) := by
    intro x
    show ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal = ∏ i : Fin n, qm (x i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  have h_pi_eq_sum :
      ((Measure.pi (fun _ : Fin n ↦ Q)) (typeClassByCount (α := α) c)).toReal
        = ∑ x ∈ T, ∏ i : Fin n, qm (x i) := by
    have h_step : ((Measure.pi (fun _ : Fin n ↦ Q)) (T : Set (Fin n → α))).toReal
        = ∑ x ∈ T, ((Measure.pi (fun _ : Fin n ↦ Q)).real {x}) := by
      rw [← MeasureTheory.measureReal_def]
      rw [← MeasureTheory.sum_measureReal_singleton
        (μ := Measure.pi (fun _ : Fin n ↦ Q)) T]
    rw [← hT_coe, h_step]
    refine Finset.sum_congr rfl fun x _ ↦ h_pi_singleton_Q x
  -- Step 2: For each x ∈ T, ∏ Q(x_i) = ∏ Q(a)^c(a).
  have h_per_point : ∀ x ∈ T,
      (∏ i : Fin n, qm (x i)) = ∏ a : α, qm a ^ (c a) := by
    intro x hx
    have hxT : x ∈ typeClassByCount c := (Set.Finite.mem_toFinset _).mp hx
    -- ∏_i qm (x_i) = ∏ a, qm(a)^c(a) via fiberwise.
    have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ (Finset.univ : Finset α) :=
      fun i _ ↦ Finset.mem_univ _
    have h := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset α)) h_maps (fun a : α ↦ qm a)
    rw [← h]
    refine Finset.prod_congr rfl fun a _ ↦ ?_
    rw [Finset.prod_const]
    have : (Finset.univ.filter fun j : Fin n ↦ x j = a).card = c a := hxT a
    rw [this]
  -- Step 3: ∑_{x ∈ T} ∏ Q(x_i) = |T| · ∏ Q(a)^c(a).
  have h_sum_eq : (∑ x ∈ T, ∏ i : Fin n, qm (x i))
      = (T.card : ℝ) * ∏ a : α, qm a ^ (c a) := by
    rw [Finset.sum_congr rfl h_per_point]
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h_pi_eq_sum, h_sum_eq]
  -- Now need: N · exp(-n · klDivIndex) ≤ |T| · ∏ Q(a)^c(a).
  -- Use typeClassByCount_card_ge: |T| ≥ N · n^n / ∏ c(a)^c(a).
  have h_card_ge := typeClassByCount_card_ge c hc_sum
  -- Show: N · exp(-n klDivIndex c n Q) = N · n^n · ∏ Q(a)^c(a) / ∏ c(a)^c(a).
  -- This requires computing exp(-n klDivIndex) = ∏ (c(a)/n · Q(a) / (c(a)/n))^c(a) ...
  -- Easier: exp(-n klDivIndex) = exp(∑ c(a) · log Q(a) - ∑ c(a) log (c(a)/n)) (n × klDivIndex)
  --                          = (∏ Q(a)^c(a)) / (∏ (c(a)/n)^c(a))
  --                          = n^n · ∏ Q(a)^c(a) / ∏ c(a)^c(a) (when c(a) > 0; 0 terms cancel)
  -- For c(a) = 0: 0^0 = 1, so (c(a)/n)^0 = 1, contribution unchanged.
  have h_exp_eq : Real.exp (-((n : ℝ) * klDivIndex c n Q))
      = ((n : ℝ) ^ n / ∏ a : α, ((c a : ℝ) ^ (c a))) * ∏ a : α, qm a ^ (c a) := by
    -- (n × klDivIndex) = ∑ a, c(a) · (log (c(a)/n) - log Q(a))
    have h_n_klDiv : (n : ℝ) * klDivIndex c n Q
        = ∑ a : α, (c a : ℝ) * (Real.log ((c a : ℝ) / n) - Real.log (qm a)) := by
      unfold klDivIndex
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rcases eq_or_ne (c a) 0 with h0 | h_pos
      · simp [h0]
      · have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn
        have hc_real_pos : (0 : ℝ) < (c a : ℝ) := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h_pos)
        show (n : ℝ) * ((c a : ℝ) / (n : ℝ) *
              (Real.log ((c a : ℝ) / (n : ℝ)) - Real.log (Q.real {a})))
            = (c a : ℝ) * (Real.log ((c a : ℝ) / (n : ℝ)) - Real.log (qm a))
        rw [hqm_def]
        field_simp
    rw [h_n_klDiv]
    rw [show -∑ a : α, (c a : ℝ) * (Real.log ((c a : ℝ) / n) - Real.log (qm a))
        = ∑ a : α, (c a : ℝ) * (Real.log (qm a) - Real.log ((c a : ℝ) / n)) by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      ring]
    rw [Real.exp_sum]
    -- ∏ a, exp(c(a) · (log Q(a) - log (c(a)/n))) = ∏ a, (Q(a) / (c(a)/n))^c(a)
    -- (when c(a) > 0; when c(a) = 0: exp(0) = 1 = 1).
    -- Also = ∏ a, Q(a)^c(a) / (c(a)/n)^c(a)
    -- = ∏ Q(a)^c(a) / ∏ (c(a)/n)^c(a)
    -- = ∏ Q(a)^c(a) · n^c(a) / c(a)^c(a) ... by individual letter.
    -- ∏ n^c(a) = n^(∑c) = n^n.
    -- So result = n^n · ∏ Q(a)^c(a) / ∏ c(a)^c(a).
    have h_per_letter : ∀ a : α,
        Real.exp ((c a : ℝ) * (Real.log (qm a) - Real.log ((c a : ℝ) / n)))
          = qm a ^ (c a) * ((n : ℝ) ^ (c a) / (c a : ℝ) ^ (c a)) := by
      intro a
      rcases eq_or_ne (c a) 0 with h0 | h_pos
      · simp [h0]
      have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn
      have hc_real_pos : (0 : ℝ) < (c a : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h_pos)
      have hqm_a_pos : 0 < qm a := hQpos a
      have h_div_pos : 0 < (c a : ℝ) / n := div_pos hc_real_pos hn_real_pos
      -- Expand: c(a) · (log Q - log (c/n)) = c(a) log Q - c(a) log (c/n)
      --   = log Q^c(a) - log (c/n)^c(a)
      --   = log (Q^c(a) / (c/n)^c(a))
      rw [show (c a : ℝ) * (Real.log (qm a) - Real.log ((c a : ℝ) / n))
            = Real.log (qm a ^ (c a)) - Real.log (((c a : ℝ) / n) ^ (c a)) by
            rw [Real.log_pow, Real.log_pow]; ring]
      rw [← Real.log_div (pow_pos hqm_a_pos _).ne' (pow_pos h_div_pos _).ne']
      rw [Real.exp_log (div_pos (pow_pos hqm_a_pos _) (pow_pos h_div_pos _))]
      rw [div_pow]
      -- qm a ^ c a / ((c a)^c a / n^c a) = qm a ^ c a · (n^c a / c a^c a)
      field_simp
    rw [show (∏ a : α, Real.exp ((c a : ℝ) * (Real.log (qm a) - Real.log ((c a : ℝ) / n))))
          = ∏ a : α, qm a ^ (c a) * ((n : ℝ) ^ (c a) / (c a : ℝ) ^ (c a)) from
        Finset.prod_congr rfl fun a _ ↦ h_per_letter a]
    -- Now: ∏ a, qm a ^ c a · n^c(a) / c(a)^c(a)
    -- = (∏ qm^c) · (∏ n^c / c^c)
    -- = (∏ qm^c) · (∏ n^c) / (∏ c^c)
    -- ∏ n^c(a) = n^(∑ c(a)) = n^n.
    rw [Finset.prod_mul_distrib]
    rw [show (∏ a : α, (n : ℝ) ^ (c a) / (c a : ℝ) ^ (c a))
          = (∏ a : α, (n : ℝ) ^ (c a)) / ∏ a : α, ((c a : ℝ) ^ (c a)) by
        rw [Finset.prod_div_distrib]]
    rw [show (∏ a : α, (n : ℝ) ^ (c a)) = (n : ℝ) ^ n by
      rw [Finset.prod_pow_eq_pow_sum, hc_sum]]
    ring
  rw [h_exp_eq]
  -- Now: N · n^n / ∏ c^c · ∏ qm^c ≤ |T| · ∏ qm^c.
  -- Equivalent to: (|T| - N · n^n / ∏ c^c) · ∏ qm^c ≥ 0, which holds if ∏ qm^c ≥ 0
  -- AND |T| ≥ N · n^n / ∏ c^c (the card lower bound).
  have h_qm_prod_nn : 0 ≤ ∏ a : α, qm a ^ (c a) :=
    Finset.prod_nonneg fun a _ ↦ pow_nonneg (hQpos a).le _
  have h_T_card : (T.card : ℝ) =
      ((typeClassByCount (α := α) (n := n) c).toFinite.toFinset.card : ℝ) := by
    rfl
  rw [h_T_card] at *
  -- Goal: N · ((n^n / ∏ c^c) · ∏ qm^c) ≤ |T| · ∏ qm^c.
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right h_card_ge h_qm_prod_nn

end InformationTheory.Shannon
