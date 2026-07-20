import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Encoding
import Mathlib.Order.Lattice.Nat

/-!
# A length-additive universal machine for plain Kolmogorov complexity

Programs are bit strings (`List Bool`) and their length is `List.length`, so
concatenating a fixed prefix is length-additive with no edge cases (unlike the
binary length `Nat.size` of a natural number, which loses leading zeros).

The fixed universal machine `universalEval` parses a program in two modes:

* literal `false :: bs` — outputs `decodeNat bs`, so the echo program
  `false :: encodeNat x` describes `x` in `natLen x + 1` bits. This gives the
  `C(x) ≤ natLen x + O(1)` upper bound and, being total, makes the defining set
  of `condComplexity` nonempty (so the infimum is attained).
* interpret `true :: unary(idx) ++ [false] ++ q` — runs
  `eval (ofNat Code idx) (Nat.pair (decodeNat q) y)`, delegating to Mathlib's
  universal interpreter `Nat.Partrec.Code.eval`. Prepending the fixed selector
  for a machine's code index costs a constant number of bits, which yields the
  invariance theorem.

## Main definitions

* `universalEval` — the fixed universal machine.
* `condComplexity` / `complexity` — conditional / plain Kolmogorov complexity.
-/

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code
open Computability (encodeNat decodeNat)

/-- Read a leading run of `true`s (a unary natural number) terminated by the
first `false`, returning the count together with the remaining bits. -/
def parseUnary : List Bool → ℕ × List Bool
  | [] => (0, [])
  | (false :: rest) => (0, rest)
  | (true :: rest) => ((parseUnary rest).1 + 1, (parseUnary rest).2)

/-- The echo program describing `x`: flag bit `false` followed by the binary
digits of `x`. -/
def literalProg (x : ℕ) : List Bool := false :: encodeNat x

/-- The interpretation program for code index `idx` running on the description
`q`: flag bit `true`, then `idx` in unary terminated by `false`, then `q`. -/
def interpretProg (idx : ℕ) (q : List Bool) : List Bool :=
  true :: (List.replicate idx true ++ (false :: q))

/-- The fixed universal machine. A program is a bit string; the leading bit
selects the literal or interpret mode. `y` is the conditioning input. -/
noncomputable def universalEval : List Bool → ℕ → Part ℕ
  | [], _ => Part.none
  | (false :: bs), _ => Part.some (decodeNat bs)
  | (true :: bs), y =>
      eval (Denumerable.ofNat Code (parseUnary bs).1)
        (Nat.pair (decodeNat (parseUnary bs).2) y)

/-- Bit length of `x`, the length of the echo program payload. -/
def natLen (x : ℕ) : ℕ := (encodeNat x).length

/-- Conditional Kolmogorov complexity `C(x | y)`: the length of the shortest
program that, run under condition `y`, outputs `x`. The literal mode makes the
set nonempty, so this infimum is attained (`condComplexity_spec`). -/
noncomputable def condComplexity (x y : ℕ) : ℕ :=
  sInf { l | ∃ p : List Bool, p.length = l ∧ x ∈ universalEval p y }

/-- Plain Kolmogorov complexity `C(x) := C(x | 0)`. -/
noncomputable def complexity (x : ℕ) : ℕ := condComplexity x 0

theorem parseUnary_replicate (n : ℕ) (q : List Bool) :
    parseUnary (List.replicate n true ++ (false :: q)) = (n, q) := by
  induction n with
  | zero => simp [parseUnary]
  | succ m ih => simp [List.replicate_succ, parseUnary, ih]

theorem literalProg_length (x : ℕ) : (literalProg x).length = natLen x + 1 := by
  simp [literalProg, natLen]

theorem interpretProg_length (idx : ℕ) (q : List Bool) :
    (interpretProg idx q).length = q.length + (idx + 2) := by
  simp [interpretProg]
  omega

theorem universalEval_literal (x y : ℕ) :
    universalEval (literalProg x) y = Part.some x := by
  simp [literalProg, universalEval, Computability.decode_encodeNat]

theorem universalEval_interpret (idx : ℕ) (q : List Bool) (y : ℕ) :
    universalEval (interpretProg idx q) y
      = eval (Denumerable.ofNat Code idx) (Nat.pair (decodeNat q) y) := by
  simp only [interpretProg, universalEval, parseUnary_replicate]

theorem condComplexity_set_nonempty (x y : ℕ) :
    { l | ∃ p : List Bool, p.length = l ∧ x ∈ universalEval p y }.Nonempty :=
  ⟨(literalProg x).length, literalProg x, rfl, by
    rw [universalEval_literal]; exact Part.mem_some x⟩

/-- The infimum defining `condComplexity` is attained by an actual program.
@audit:ok -/
theorem condComplexity_spec (x y : ℕ) :
    ∃ p : List Bool, p.length = condComplexity x y ∧ x ∈ universalEval p y :=
  Nat.sInf_mem (condComplexity_set_nonempty x y)

end InformationTheory.Kolmogorov
