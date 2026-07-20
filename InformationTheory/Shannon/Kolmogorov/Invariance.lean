import InformationTheory.Shannon.Kolmogorov.UniversalMachine

/-!
# Invariance and the literal upper bound

* `complexity_le_natLen` — the literal echo program gives `C(x) ≤ natLen x + O(1)`.
* `invariance_code` — for any fixed code `c`, a description of `x` via `c`
  is matched by the universal machine up to a constant number of extra bits.
* `invariance` — the same for an arbitrary partial recursive description
  method `A`, obtained from `invariance_code` through `exists_code`.

The additive constant is explicit: prepending the interpret selector for a code
index `idx` costs `idx + 2` bits, and the literal flag costs one bit.
-/

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code
open Computability (encodeNat decodeNat)

/-- Literal upper bound: the echo program `false :: encodeNat x` describes `x`,
so `C(x) ≤ natLen x + 1`.
@audit:ok -/
theorem complexity_le_natLen : ∃ c : ℕ, ∀ x, complexity x ≤ natLen x + c := by
  refine ⟨1, fun x ↦ ?_⟩
  have hmem : (literalProg x).length ∈
      { l | ∃ p : List Bool, p.length = l ∧ x ∈ universalEval p 0 } :=
    ⟨literalProg x, rfl, by rw [universalEval_literal]; exact Part.mem_some x⟩
  have hle : complexity x ≤ (literalProg x).length := Nat.sInf_le hmem
  rwa [literalProg_length] at hle

/-- Invariance against a fixed code `c`: any bit-string description `q` with
`x ∈ eval c (Nat.pair (decodeNat q) y)` yields `C(x | y) ≤ q.length + b`, with
`b = encodeCode c + 2` independent of `x`, `y`, `q`.
@audit:ok -/
theorem invariance_code (c : Code) :
    ∃ b : ℕ, ∀ (x y : ℕ) (q : List Bool),
      x ∈ eval c (Nat.pair (decodeNat q) y) → condComplexity x y ≤ q.length + b := by
  refine ⟨encodeCode c + 2, fun x y q hx ↦ ?_⟩
  have hcode : Denumerable.ofNat Code (encodeCode c) = c := by
    rw [← encodeCode_eq]; exact Denumerable.ofNat_encode c
  have hrun : x ∈ universalEval (interpretProg (encodeCode c) q) y := by
    rw [universalEval_interpret, hcode]; exact hx
  have hmem : (interpretProg (encodeCode c) q).length ∈
      { l | ∃ p : List Bool, p.length = l ∧ x ∈ universalEval p y } :=
    ⟨interpretProg (encodeCode c) q, rfl, hrun⟩
  have hle : condComplexity x y ≤ (interpretProg (encodeCode c) q).length := Nat.sInf_le hmem
  rwa [interpretProg_length] at hle

/-- Invariance against an arbitrary partial recursive description method `A`:
`C(x | y) ≤ (A-description length) + b` for a constant `b`.
@audit:ok -/
theorem invariance (A : ℕ → ℕ → Part ℕ) (hA : Partrec₂ A) :
    ∃ b : ℕ, ∀ (x y : ℕ) (q : List Bool),
      x ∈ A (decodeNat q) y → condComplexity x y ≤ q.length + b := by
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec₂.unpaired'.2 hA)
  obtain ⟨b, hb⟩ := invariance_code c
  refine ⟨b, fun x y q hx ↦ ?_⟩
  apply hb x y q
  rw [hc]
  simpa [Nat.unpaired, Nat.unpair_pair] using hx

end InformationTheory.Kolmogorov
