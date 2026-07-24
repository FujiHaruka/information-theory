import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Kolmogorov.Invariance
import InformationTheory.Shannon.Kolmogorov.Counting
import Mathlib.Computability.Partrec

/-!
# Kolmogorov complexity is not computable

`complexity` grows unboundedly (`exists_incompressible`) yet, were it computable, one
could search for the least string whose complexity reaches a given bound `k`. That
search is a partial recursive description of an incompressible string using only the
`natLen k` bits of `k`, so the invariance theorem bounds its complexity by
`natLen k + O(1)`. Since `natLen` is the binary length and grows logarithmically, the
two facts collide: the searched string has complexity at least `k` but at most
`natLen k + O(1) < k` for large `k` (Berry's paradox).

## Main results

* `complexity_not_computable` — `complexity` is not a computable function.
-/

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code
open Computability (encodeNat decodeNat)

theorem exists_condIncompressible (y k : ℕ) : ∃ x, k ≤ condComplexity x y := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hfin := condComplexity_lt_finite y k
  have huniv : {x : ℕ | condComplexity x y < k} = Set.univ := Set.eq_univ_of_forall h
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

/-- Conditional Kolmogorov complexity is not computable, for any fixed condition `y`
(Berry's paradox): a computable `C(· | y)` would let one search for the least string
of complexity at least `k`, describing it in only `natLen k` bits.
@audit:ok -/
@[entry_point]
theorem condComplexity_not_computable (y : ℕ) :
    ¬ Computable (fun x ↦ condComplexity x y) := by
  intro hcomp
  -- The search machine: on input `k`, find the least `x` with `k ≤ C(x | y)`.
  have hA : Partrec₂
      (fun (k _ : ℕ) ↦ Nat.rfind fun x ↦ Part.some (decide (k ≤ condComplexity x y))) := by
    have hg : Computable (fun t : (ℕ × ℕ) × ℕ ↦ decide (t.1.1 ≤ condComplexity t.2 y)) :=
      (Primrec.nat_le.decide.to_comp : Computable₂ (fun a b : ℕ ↦ decide (a ≤ b))).comp
        (Computable.fst.comp Computable.fst) (hcomp.comp Computable.snd)
    exact Partrec.rfind (Computable₂.partrec₂ hg)
  obtain ⟨b, hb⟩ := invariance _ hA
  -- Each `k` describes an incompressible string in `natLen k` bits.
  have key : ∀ k, k ≤ natLen k + b := by
    intro k
    obtain ⟨w, hw⟩ := exists_condIncompressible y k
    obtain ⟨fk, hfk_mem, -⟩ :=
      Nat.rfind_min' (p := fun x ↦ decide (k ≤ condComplexity x y)) (m := w) (by simpa using hw)
    have hspec := Nat.rfind_spec hfk_mem
    simp only [PFun.coe_val, Part.mem_some_iff] at hspec
    have hge : k ≤ condComplexity fk y := of_decide_eq_true hspec.symm
    have hmemA : fk ∈ (fun (a _ : ℕ) ↦
        Nat.rfind fun x ↦ Part.some (decide (a ≤ condComplexity x y)))
        (decodeNat (encodeNat k)) y := by
      simp only [Computability.decode_encodeNat]
      exact hfk_mem
    have hup : condComplexity fk y ≤ natLen k + b := hb fk y (encodeNat k) hmemA
    omega
  -- Growth collision at `k = 2 ^ (b + 2)`.
  have hL := key (2 ^ (b + 2))
  have hbound := natLen_le (2 ^ (b + 2)) Nat.one_le_two_pow
  have h23 : 2 * 2 ^ (b + 2) = 2 ^ (b + 3) := by
    have e : (2 : ℕ) ^ (b + 3) = 2 ^ (b + 2) * 2 := pow_succ 2 (b + 2)
    omega
  rw [h23] at hbound
  have hLle : natLen (2 ^ (b + 2)) ≤ b + 3 := (Nat.pow_le_pow_iff_right (by decide)).1 hbound
  have hbb : b < 2 ^ b := Nat.lt_two_pow_self
  have h4 : (2 : ℕ) ^ 2 = 4 := by decide
  have hpow : (2 : ℕ) ^ (b + 2) = 2 ^ b * 4 := by rw [pow_add, h4]
  omega

/-- Kolmogorov complexity is not computable (Berry's paradox).
@audit:ok -/
@[entry_point]
theorem complexity_not_computable : ¬ Computable complexity :=
  condComplexity_not_computable 0

end InformationTheory.Kolmogorov
