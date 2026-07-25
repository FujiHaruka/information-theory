import InformationTheory.Shannon.Kolmogorov.PrefixComputability

/-!
# A step-bounded evaluator for the self-delimiting machine

Cover–Thomas (2nd ed.) §14.9. Running the self-delimiting machine
`prefixUniversalEval` with a finite budget yields a total function
`prefixEvaln`, primitive recursive in the budget and the program, which is sound
and complete for the unbounded machine. It is the computable skeleton behind the
approximation of the halting probability `Ω` from below.

The section also fixes the notion of a computable nonnegative extended real used
to state that `Ω` is not one: a computable sequence of dyadic numerators whose
values approximate the target within `2 ^ (-n)`.

## Main definitions

* `IsComputableENNReal` — computability of an extended nonnegative real by a
  computable sequence of dyadic rationals with error `2 ^ (-n)`.
* `prefixEvaln` — the step-bounded evaluator of the self-delimiting machine.

## Main results

* `prefixEvaln_primrec` — the bounded evaluator is primitive recursive.
* `prefixEvaln_complete` — a value is output by the machine exactly when some
  finite budget already produces it.
-/

open scoped ENNReal

namespace InformationTheory.Kolmogorov

open Nat.Partrec Nat.Partrec.Code

/-- A computable nonnegative extended real: a computable sequence of dyadic
numerators `a n`, whose value `a n / 2 ^ n` is within `2 ^ (-n)` of `x`. The two
bounds are stated additively, so no truncated subtraction occurs.

The standard notion — a computable sequence of rationals converging to `x` with
error `2 ^ (-n)` — implies this one: rounding a sufficiently accurate rational
approximation to a multiple of `2 ^ (-n)` produces such a numerator sequence. The
converse-facing strict form `a n * 2 ^ (-n) ≤ x ≤ (a n + 1) * 2 ^ (-n)` is
deliberately avoided: deciding which side of a dyadic grid point `x` falls on is
not computable, so that form is a strictly stronger predicate. -/
def IsComputableENNReal (x : ℝ≥0∞) : Prop :=
  ∃ a : ℕ → ℕ, Computable a ∧ ∀ n : ℕ,
    x ≤ (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n + (2 : ℝ≥0∞)⁻¹ ^ n ∧
      (a n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ n ≤ x + (2 : ℝ≥0∞)⁻¹ ^ n

/-- The step-bounded evaluator: the self-delimiting machine run with budget `k`,
following `decodePayload_eq_dispatch` with `eval` replaced by `evaln k`. -/
noncomputable def prefixEvaln (k : ℕ) (p : List Bool) : Option ℕ :=
  if (parseUnary p).1 = (parseUnary p).2.length then
    (payloadDispatch (parseUnary p).2).bind fun q ↦ evaln k q.1 q.2
  else none

theorem prefixEvaln_mono {k₁ k₂ : ℕ} {p : List Bool} {x : ℕ}
    (h : k₁ ≤ k₂) (hx : x ∈ prefixEvaln k₁ p) : x ∈ prefixEvaln k₂ p := by
  by_cases hg : (parseUnary p).1 = (parseUnary p).2.length
  · rw [prefixEvaln, if_pos hg] at hx ⊢
    obtain ⟨q, hq, hxq⟩ := Option.mem_bind_iff.mp hx
    exact Option.mem_bind_iff.mpr ⟨q, hq, evaln_mono h hxq⟩
  · rw [prefixEvaln, if_neg hg] at hx
    simp at hx

theorem prefixEvaln_sound {k : ℕ} {p : List Bool} {x : ℕ}
    (hx : x ∈ prefixEvaln k p) : x ∈ prefixUniversalEval p := by
  by_cases hg : (parseUnary p).1 = (parseUnary p).2.length
  · rw [prefixEvaln, if_pos hg] at hx
    obtain ⟨q, hq, hxq⟩ := Option.mem_bind_iff.mp hx
    rw [prefixUniversalEval, if_pos hg, decodePayload_eq_dispatch]
    exact Part.mem_bind_iff.mpr ⟨q, Part.mem_coe.mpr hq, evaln_sound hxq⟩
  · rw [prefixEvaln, if_neg hg] at hx
    simp at hx

theorem prefixEvaln_complete {p : List Bool} {x : ℕ} :
    x ∈ prefixUniversalEval p ↔ ∃ k, x ∈ prefixEvaln k p := by
  refine ⟨fun hx ↦ ?_, fun ⟨_, hk⟩ ↦ prefixEvaln_sound hk⟩
  by_cases hg : (parseUnary p).1 = (parseUnary p).2.length
  · rw [prefixUniversalEval, if_pos hg, decodePayload_eq_dispatch] at hx
    obtain ⟨q, hq, hxq⟩ := Part.mem_bind_iff.mp hx
    obtain ⟨k, hk⟩ := evaln_complete.mp hxq
    refine ⟨k, ?_⟩
    rw [prefixEvaln, if_pos hg]
    exact Option.mem_bind_iff.mpr ⟨q, Part.mem_coe.mp hq, hk⟩
  · rw [prefixUniversalEval, if_neg hg] at hx
    simp at hx

theorem prefixEvaln_dom_iff {p : List Bool} :
    (prefixUniversalEval p).Dom ↔ ∃ k, (prefixEvaln k p).isSome := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := prefixEvaln_complete.mp (Part.get_mem h)
    exact ⟨k, Option.isSome_iff_exists.mpr ⟨_, hk⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hk
    exact Part.dom_iff_mem.mpr ⟨x, prefixEvaln_sound hx⟩

theorem prefixEvaln_primrec : Primrec fun a : ℕ × List Bool ↦ prefixEvaln a.1 a.2 := by
  have hpu : Primrec fun a : ℕ × List Bool ↦ parseUnary a.2 :=
    parseUnary_primrec.comp Primrec.snd
  have hguard : PrimrecPred fun a : ℕ × List Bool ↦
      (parseUnary a.2).1 = (parseUnary a.2).2.length :=
    PrimrecRel.comp Primrec.eq (Primrec.fst.comp hpu)
      (Primrec.list_length.comp (Primrec.snd.comp hpu))
  have hevaln : Primrec₂ fun (a : ℕ × List Bool) (q : Code × ℕ) ↦ evaln a.1 q.1 q.2 :=
    (primrec_evaln.comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd))).to₂
  have hbind : Primrec fun a : ℕ × List Bool ↦
      (payloadDispatch (parseUnary a.2).2).bind fun q ↦ evaln a.1 q.1 q.2 :=
    Primrec.option_bind (payloadDispatch_primrec.comp (Primrec.snd.comp hpu)) hevaln
  exact Primrec.ite hguard hbind (Primrec.const none)

end InformationTheory.Kolmogorov
