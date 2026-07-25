import Mathlib.Computability.Halting
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Kolmogorov.Omega
import InformationTheory.Shannon.Kolmogorov.SufficientStatistic

/-!
# Computability of the self-delimiting machine

The self-delimiting machine `prefixUniversalEval` is a partial recursive
function, and its halting set is undecidable. The first statement assembles the
machine from the primitive recursive parser `parseUnary` and the partial
recursive payload decoder `decodePayload`. The second reduces the halting
problem of Mathlib's universal interpreter to it along the interpret-mode entry
`prefixInterpretProg`.

## Main statements

* `prefixUniversalEval_partrec` — the machine is partial recursive.
* `prefixUniversalEval_dom_not_computablePred` — its halting set is undecidable.
-/

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code
open Computability (decodeNat)

theorem primrec_replicate_true : Primrec fun n : ℕ ↦ List.replicate n true := by
  have hiter : ∀ n : ℕ, (fun l : List Bool ↦ true :: l)^[n] [] = List.replicate n true := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, ← List.replicate_succ]
  exact (Primrec.nat_iterate Primrec.id (Primrec.const [])
    ((Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂)).of_eq hiter

theorem primrec_prefixInterpretProg_nil :
    Primrec fun idx : ℕ ↦ prefixInterpretProg idx [] := by
  have hbs : Primrec fun idx : ℕ ↦ (true :: (List.replicate idx true ++ [false]) : List Bool) :=
    Primrec.list_cons.comp (Primrec.const true)
      (Primrec.list_append.comp primrec_replicate_true (Primrec.const [false]))
  refine (Primrec.list_append.comp
    (primrec_replicate_true.comp (Primrec.list_length.comp hbs))
    (Primrec.list_cons.comp (Primrec.const false) hbs)).of_eq fun idx ↦ ?_
  simp [prefixInterpretProg, selfDelimit]

/-- The self-delimiting machine is partial recursive: its length guard is
primitive recursive through `parseUnary`, and the payload it hands on is decoded
by the partial recursive `decodePayload`. -/
theorem prefixUniversalEval_partrec : Partrec prefixUniversalEval := by
  have hguard : Computable fun p : List Bool ↦
      (if (parseUnary p).1 = (parseUnary p).2.length then some (parseUnary p).2
        else none : Option (List Bool)) := by
    refine (Primrec.ite ?_ ?_ (Primrec.const none)).to_comp
    · exact PrimrecRel.comp Primrec.eq (Primrec.fst.comp parseUnary_primrec)
        (Primrec.list_length.comp (Primrec.snd.comp parseUnary_primrec))
    · exact Primrec.option_some.comp (Primrec.snd.comp parseUnary_primrec)
  have hbind : Partrec₂ fun (_ : List Bool) (d : List Bool) ↦ decodePayload d :=
    (decodePayload_partrec.comp Computable.snd).to₂
  refine (Partrec.bind (Computable.ofOption hguard) hbind).of_eq fun p ↦ ?_
  by_cases hg : (parseUnary p).1 = (parseUnary p).2.length
  · simp [prefixUniversalEval, hg]
  · simp [prefixUniversalEval, hg]

/-- The halting set of the self-delimiting machine is undecidable: a decision
procedure for it would decide the halting problem of Mathlib's universal
interpreter, which the interpret-mode entry `prefixInterpretProg` embeds into it.
@audit:ok -/
@[entry_point]
theorem prefixUniversalEval_dom_not_computablePred :
    ¬ ComputablePred fun p : List Bool ↦ (prefixUniversalEval p).Dom := by
  rintro ⟨hdec, hcomp⟩
  have hf : Computable fun c : Code ↦ prefixInterpretProg (encodeCode c) [] := by
    refine (primrec_prefixInterpretProg_nil.comp ?_).to_comp
    exact (Primrec.encode (α := Code)).of_eq fun c ↦ (encodeCode_eq ▸ rfl)
  have h2 : ComputablePred fun c : Code ↦
      (prefixUniversalEval (prefixInterpretProg (encodeCode c) [])).Dom :=
    ⟨fun c ↦ hdec _, hcomp.comp hf⟩
  refine ComputablePred.halting_problem 0 (h2.of_eq fun c ↦ ?_)
  have hcode : Denumerable.ofNat Code (encodeCode c) = c := by
    rw [← encodeCode_eq]; exact Denumerable.ofNat_encode c
  have hnil : Nat.pair (decodeNat []) 0 = 0 := by
    simp [Computability.decodeNat, Computability.decodeNum, Nat.pair]
  rw [prefixUniversalEval_interpret, hcode, hnil]

end InformationTheory.Kolmogorov
