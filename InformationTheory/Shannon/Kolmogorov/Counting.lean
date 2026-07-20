import InformationTheory.Shannon.Kolmogorov.UniversalMachine
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting and the existence of incompressible strings

There are fewer than `2 ^ k` natural numbers of complexity below `k`, because
each such `x` is produced by a program shorter than `k` bits and the map sending
`x` to its shortest program is injective (a program's output is determined by the
program). Since there are only finitely many programs of length below `k`, only
finitely many `x` can be that simple, and — the type of naturals being infinite —
an incompressible `x` with `k ≤ complexity x` always exists.

## Main results

* `incompressible_count` — `#{x | complexity x < k} < 2 ^ k`.
* `exists_incompressible` — for every `k` some `x` has `k ≤ complexity x`.
-/

namespace InformationTheory.Kolmogorov

/-- Encode a bit string as a positive natural number by reading it as the binary
digits below a leading sentinel `1`. The sentinel makes the encoding injective
(the length is recoverable) and keeps a length-`n` string below `2 ^ (n + 1)`. -/
def progNat : List Bool → ℕ
  | [] => 1
  | (b :: bs) => 2 * progNat bs + b.toNat

theorem progNat_pos (p : List Bool) : 0 < progNat p := by
  induction p with
  | nil => simp [progNat]
  | cons b bs ih => simp only [progNat]; omega

theorem progNat_lt (p : List Bool) : progNat p < 2 ^ (p.length + 1) := by
  induction p with
  | nil => simp only [progNat, List.length_nil]; decide
  | cons b bs ih =>
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    have hpow : (2 : ℕ) ^ (bs.length + 1 + 1) = 2 * 2 ^ (bs.length + 1) := by
      rw [pow_succ]; exact Nat.mul_comm _ 2
    simp only [progNat, List.length_cons]
    rw [hpow]
    omega

theorem progNat_injective : Function.Injective progNat := by
  intro p q h
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons c cs =>
      exfalso
      have := progNat_pos cs
      simp only [progNat] at h
      omega
  | cons b bs ih =>
    cases q with
    | nil =>
      exfalso
      have := progNat_pos bs
      simp only [progNat] at h
      omega
    | cons c cs =>
      simp only [progNat] at h
      have hb : b.toNat ≤ 1 := by cases b <;> simp
      have hc : c.toNat ≤ 1 := by cases c <;> simp
      have hbs : progNat bs = progNat cs := by omega
      have hbc : b = c := by
        have : b.toNat = c.toNat := by omega
        cases b <;> cases c <;> simp_all
      rw [ih hbs, hbc]

/-- A shortest program for `x` (attained by `condComplexity_spec`). -/
noncomputable def shortestProg (x : ℕ) : List Bool := (condComplexity_spec x 0).choose

/-- The natural-number code of `x`'s shortest program. -/
noncomputable def shortestNat (x : ℕ) : ℕ := progNat (shortestProg x)

theorem shortestProg_length (x : ℕ) : (shortestProg x).length = condComplexity x 0 :=
  (condComplexity_spec x 0).choose_spec.1

theorem shortestProg_mem (x : ℕ) : x ∈ universalEval (shortestProg x) 0 :=
  (condComplexity_spec x 0).choose_spec.2

theorem shortestNat_injective : Function.Injective shortestNat := by
  intro x₁ x₂ h
  have hp : shortestProg x₁ = shortestProg x₂ := progNat_injective h
  have h1 : x₁ ∈ universalEval (shortestProg x₁) 0 := shortestProg_mem x₁
  have h2 : x₂ ∈ universalEval (shortestProg x₂) 0 := shortestProg_mem x₂
  rw [hp] at h1
  exact Part.mem_unique h1 h2

theorem shortestNat_lt_of_lt {x k : ℕ} (hx : complexity x < k) : shortestNat x < 2 ^ k := by
  have hlen : (shortestProg x).length < k := by rw [shortestProg_length]; exact hx
  calc shortestNat x = progNat (shortestProg x) := rfl
    _ < 2 ^ ((shortestProg x).length + 1) := progNat_lt _
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)

theorem complexity_lt_finite (k : ℕ) : {x : ℕ | complexity x < k}.Finite := by
  have himg : (shortestNat '' {x : ℕ | complexity x < k}).Finite := by
    apply Set.Finite.subset (Set.finite_Iio (2 ^ k))
    rintro _ ⟨x, hx, rfl⟩
    exact shortestNat_lt_of_lt hx
  exact himg.of_finite_image shortestNat_injective.injOn

/-- Fewer than `2 ^ k` naturals have complexity below `k`. -/
theorem incompressible_count (k : ℕ) : {x : ℕ | complexity x < k}.ncard < 2 ^ k := by
  have hsub : shortestNat '' {x : ℕ | complexity x < k} ⊆ ↑(Finset.Ico 1 (2 ^ k)) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [Finset.coe_Ico, Set.mem_Ico]
    exact ⟨progNat_pos _, shortestNat_lt_of_lt hx⟩
  calc {x : ℕ | complexity x < k}.ncard
      = (shortestNat '' {x : ℕ | complexity x < k}).ncard :=
        (Set.ncard_image_of_injective _ shortestNat_injective).symm
    _ ≤ (↑(Finset.Ico 1 (2 ^ k)) : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Finset.Ico 1 (2 ^ k)).finite_toSet
    _ = (Finset.Ico 1 (2 ^ k)).card := Set.ncard_coe_finset _
    _ = 2 ^ k - 1 := Nat.card_Ico 1 (2 ^ k)
    _ < 2 ^ k := by have : 0 < 2 ^ k := pow_pos (by decide) k; omega

/-- For every bound `k` there is an incompressible `x` with `k ≤ complexity x`. -/
theorem exists_incompressible (k : ℕ) : ∃ x, k ≤ complexity x := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hfin := complexity_lt_finite k
  have huniv : {x : ℕ | complexity x < k} = Set.univ := Set.eq_univ_of_forall h
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

end InformationTheory.Kolmogorov
