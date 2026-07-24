import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Kolmogorov.Counting
import InformationTheory.Shannon.Kolmogorov.PrefixMachine

/-!
# Chaitin's halting probability

Cover–Thomas (2nd ed.) §14.9. The halting probability of the self-delimiting
machine is the total weight `∑ 2^{-|p|}` of its halting programs. Because the
halting set is prefix-free, the Kraft bound applies to every finite subsum, so
`Ω` is a subprobability; the literal echo program halts, so `Ω` is positive.

The second half of the section is that the prefix world is not computable. The
Berry argument of the plain machine transfers: a computable `K` would let one
search for the least string of prefix complexity at least `k`, and the
self-delimiting interpreter describes that string in `2 · natLen k + O(1)` bits.

## Main definitions

* `chaitinOmega` — the halting probability `Ω` in `ℝ≥0∞`.
* `prefixInterpretProg` — the self-delimited interpretation program.

## Main results

* `chaitinOmega_le_one` — `Ω ≤ 1`, the Kraft bound on the halting set.
* `chaitinOmega_pos` — `0 < Ω`.
* `prefixComplexity_not_computable` — `K` is not a computable function.
-/

open scoped ENNReal

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code
open Computability (encodeNat decodeNat)

/-- Chaitin's halting probability `Ω = ∑_{p halts} 2^{-|p|}` in `ℝ≥0∞`, the
weight of the halting programs of the self-delimiting machine. -/
noncomputable def chaitinOmega : ℝ≥0∞ :=
  ∑' p : { p : List Bool // (prefixUniversalEval p).Dom }, (2 : ℝ≥0∞)⁻¹ ^ (p : List Bool).length

/-- The halting probability is a subprobability: `Ω ≤ 1`, because the halting
programs form a prefix-free set and every finite subsum is a Kraft sum. -/
@[entry_point]
theorem chaitinOmega_le_one : chaitinOmega ≤ 1 := by
  rw [chaitinOmega]
  exact tsum_inv_two_pow_length_le_one fun _ hp ↦ hp

theorem chaitinOmega_pos : 0 < chaitinOmega := by
  have hdom : (prefixUniversalEval (prefixLiteralProg 0)).Dom := by
    rw [prefixUniversalEval_literal]; trivial
  have hle : (2 : ℝ≥0∞)⁻¹ ^ (prefixLiteralProg 0).length ≤ chaitinOmega := by
    rw [chaitinOmega]
    exact ENNReal.le_tsum (f := fun q : { q : List Bool // (prefixUniversalEval q).Dom } ↦
      (2 : ℝ≥0∞)⁻¹ ^ (q : List Bool).length) ⟨prefixLiteralProg 0, hdom⟩
  exact lt_of_lt_of_le (ENNReal.pow_pos (by simp) _) hle

theorem chaitinOmega_ne_top : chaitinOmega ≠ ⊤ :=
  (chaitinOmega_le_one.trans_lt ENNReal.one_lt_top).ne

/-! ## Non-computability of prefix complexity -/

/-- A shortest self-delimiting program for `x` (attained by
`prefixComplexity_spec`). -/
noncomputable def shortestPrefixProg (x : ℕ) : List Bool := (prefixComplexity_spec x).choose

/-- The natural-number code of `x`'s shortest self-delimiting program. -/
noncomputable def shortestPrefixNat (x : ℕ) : ℕ := progNat (shortestPrefixProg x)

theorem shortestPrefixProg_length (x : ℕ) :
    (shortestPrefixProg x).length = prefixComplexity x :=
  (prefixComplexity_spec x).choose_spec.1

theorem shortestPrefixProg_mem (x : ℕ) : x ∈ prefixUniversalEval (shortestPrefixProg x) :=
  (prefixComplexity_spec x).choose_spec.2

theorem shortestPrefixNat_injective : Function.Injective shortestPrefixNat := by
  intro x₁ x₂ h
  have hp : shortestPrefixProg x₁ = shortestPrefixProg x₂ := progNat_injective h
  have h1 : x₁ ∈ prefixUniversalEval (shortestPrefixProg x₁) := shortestPrefixProg_mem x₁
  have h2 : x₂ ∈ prefixUniversalEval (shortestPrefixProg x₂) := shortestPrefixProg_mem x₂
  rw [hp] at h1
  exact Part.mem_unique h1 h2

theorem shortestPrefixNat_lt_of_lt {x k : ℕ} (hx : prefixComplexity x < k) :
    shortestPrefixNat x < 2 ^ k := by
  have hlen : (shortestPrefixProg x).length < k := by rw [shortestPrefixProg_length]; exact hx
  calc shortestPrefixNat x = progNat (shortestPrefixProg x) := rfl
    _ < 2 ^ ((shortestPrefixProg x).length + 1) := progNat_lt _
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)

theorem prefixComplexity_lt_finite (k : ℕ) : {x : ℕ | prefixComplexity x < k}.Finite := by
  have himg : (shortestPrefixNat '' {x : ℕ | prefixComplexity x < k}).Finite := by
    apply Set.Finite.subset (Set.finite_Iio (2 ^ k))
    rintro _ ⟨x, hx, rfl⟩
    exact shortestPrefixNat_lt_of_lt hx
  exact himg.of_finite_image shortestPrefixNat_injective.injOn

theorem exists_prefixIncompressible (k : ℕ) : ∃ x, k ≤ prefixComplexity x := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hfin := prefixComplexity_lt_finite k
  have huniv : {x : ℕ | prefixComplexity x < k} = Set.univ := Set.eq_univ_of_forall h
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

/-- The self-delimited interpretation program for code index `idx` running on
the description `q`: the interpret flag, then `idx` in unary terminated by
`false`, then `q`, all wrapped by the self-delimiting length prefix. -/
def prefixInterpretProg (idx : ℕ) (q : List Bool) : List Bool :=
  selfDelimit (true :: (List.replicate idx true ++ (false :: q)))

theorem prefixInterpretProg_length (idx : ℕ) (q : List Bool) :
    (prefixInterpretProg idx q).length = 2 * q.length + (2 * idx + 5) := by
  simp only [prefixInterpretProg, selfDelimit, List.length_append, List.length_replicate,
    List.length_cons]
  omega

theorem prefixUniversalEval_interpret (idx : ℕ) (q : List Bool) :
    prefixUniversalEval (prefixInterpretProg idx q)
      = eval (Denumerable.ofNat Code idx) (Nat.pair (decodeNat q) 0) := by
  rw [prefixInterpretProg, prefixUniversalEval, parseUnary_selfDelimit]
  simp [decodePayload, parseUnary_replicate]

theorem prefix_invariance_code (c : Code) :
    ∃ b : ℕ, ∀ (x : ℕ) (q : List Bool),
      x ∈ eval c (Nat.pair (decodeNat q) 0) → prefixComplexity x ≤ 2 * q.length + b := by
  refine ⟨2 * encodeCode c + 5, fun x q hx ↦ ?_⟩
  have hcode : Denumerable.ofNat Code (encodeCode c) = c := by
    rw [← encodeCode_eq]; exact Denumerable.ofNat_encode c
  have hrun : x ∈ prefixUniversalEval (prefixInterpretProg (encodeCode c) q) := by
    rw [prefixUniversalEval_interpret, hcode]; exact hx
  have hmem : (prefixInterpretProg (encodeCode c) q).length ∈
      { l | ∃ p : List Bool, p.length = l ∧ x ∈ prefixUniversalEval p } :=
    ⟨prefixInterpretProg (encodeCode c) q, rfl, hrun⟩
  have hle : prefixComplexity x ≤ (prefixInterpretProg (encodeCode c) q).length := Nat.sInf_le hmem
  rwa [prefixInterpretProg_length] at hle

theorem prefix_invariance (A : ℕ → ℕ → Part ℕ) (hA : Partrec₂ A) :
    ∃ b : ℕ, ∀ (x : ℕ) (q : List Bool),
      x ∈ A (decodeNat q) 0 → prefixComplexity x ≤ 2 * q.length + b := by
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec₂.unpaired'.2 hA)
  obtain ⟨b, hb⟩ := prefix_invariance_code c
  refine ⟨b, fun x q hx ↦ ?_⟩
  apply hb x q
  rw [hc]
  simpa [Nat.unpaired, Nat.unpair_pair] using hx

/-- Prefix Kolmogorov complexity is not computable (Berry's paradox): a
computable `K` would let one search for the least string of prefix complexity at
least `k`, which the self-delimiting interpreter then describes in
`2 · natLen k + O(1)` bits. -/
@[entry_point]
theorem prefixComplexity_not_computable : ¬ Computable prefixComplexity := by
  intro hcomp
  -- The search machine: on input `k`, find the least `x` with `k ≤ K x`.
  have hA : Partrec₂
      (fun (k _ : ℕ) ↦ Nat.rfind fun x ↦ Part.some (decide (k ≤ prefixComplexity x))) := by
    have hg : Computable (fun t : (ℕ × ℕ) × ℕ ↦ decide (t.1.1 ≤ prefixComplexity t.2)) :=
      (Primrec.nat_le.decide.to_comp : Computable₂ (fun a b : ℕ ↦ decide (a ≤ b))).comp
        (Computable.fst.comp Computable.fst) (hcomp.comp Computable.snd)
    exact Partrec.rfind (Computable₂.partrec₂ hg)
  obtain ⟨b, hb⟩ := prefix_invariance _ hA
  -- Each `k` describes an incompressible string in `2 · natLen k` bits.
  have key : ∀ k, k ≤ 2 * natLen k + b := by
    intro k
    obtain ⟨w, hw⟩ := exists_prefixIncompressible k
    obtain ⟨fk, hfk_mem, -⟩ :=
      Nat.rfind_min' (p := fun x ↦ decide (k ≤ prefixComplexity x)) (m := w) (by simpa using hw)
    have hspec := Nat.rfind_spec hfk_mem
    simp only [PFun.coe_val, Part.mem_some_iff] at hspec
    have hge : k ≤ prefixComplexity fk := of_decide_eq_true hspec.symm
    have hmemA : fk ∈ (fun (a _ : ℕ) ↦
        Nat.rfind fun x ↦ Part.some (decide (a ≤ prefixComplexity x)))
        (decodeNat (encodeNat k)) 0 := by
      simp only [Computability.decode_encodeNat]
      exact hfk_mem
    have hup : prefixComplexity fk ≤ 2 * natLen k + b := hb fk (encodeNat k) hmemA
    omega
  -- Growth collision at `k = 2 ^ (b + 4)`.
  have hL := key (2 ^ (b + 4))
  have hbound := natLen_le (2 ^ (b + 4)) Nat.one_le_two_pow
  have h25 : 2 * 2 ^ (b + 4) = 2 ^ (b + 5) := by
    have e : (2 : ℕ) ^ (b + 5) = 2 ^ (b + 4) * 2 := pow_succ 2 (b + 4)
    omega
  rw [h25] at hbound
  have hLle : natLen (2 ^ (b + 4)) ≤ b + 5 := (Nat.pow_le_pow_iff_right (by decide)).1 hbound
  have hbb : b < 2 ^ b := Nat.lt_two_pow_self
  have h16 : (2 : ℕ) ^ 4 = 16 := by decide
  have hpow : (2 : ℕ) ^ (b + 4) = 2 ^ b * 16 := by rw [pow_add, h16]
  omega

end InformationTheory.Kolmogorov
