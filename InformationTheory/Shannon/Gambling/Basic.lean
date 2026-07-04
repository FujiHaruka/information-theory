import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.CsiszarProjection
import InformationTheory.Shannon.MaxEntropy.Constrained
import InformationTheory.Shannon.Hoeffding.TradeoffExp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Kelly gambling and the doubling rate (Cover–Thomas Theorem 6.1.2)

For a horse race on a finite alphabet `α` with true win probabilities `p : α → ℝ`,
betting fractions `b : α → ℝ`, and odds `o : α → ℝ` (payoff per unit staked on `x`),
the **doubling rate** of the bet `b` is the expected log-wealth growth per race,

  `W(b, o, p) = ∑ x, p x · log (b x · o x)`.

The main result is that the proportional (Kelly) bet `b = p` maximizes the doubling
rate, and does so uniquely.

## Main definitions

* `doublingRate` — the doubling rate `∑ x, p x · log (b x · o x)`.

## Main statements

* `doublingRate_le_proportional` — Theorem 6.1.2: `W(b, o, p) ≤ W(p, o, p)` for any
  full-support bet `b`, i.e. proportional betting is optimal.
* `doublingRate_eq_proportional_iff` — equality holds iff `b = p`.
* `doublingRate_proportional_eq` — the optimal doubling rate in closed form,
  `W(p, o, p) = ∑ x, p x · log (o x) − H(p)`.
* `doublingRate_proportional_add_entropy` — the conservation law
  `W(p, o, p) + H(p) = ∑ x, p x · log (o x)`.

## Implementation notes

Everything reduces to the finite-alphabet KL divergence `klDivPmf` of
`InformationTheory.Shannon.CsiszarProjection`, mirroring the maximum-entropy proof
`entropy_le_gibbs_of_constraints`. The key identity is

  `W(p, o, p) − W(b, o, p) = ∑ x, p x · (log (p x) − log (b x)) = klDivPmf p b ≥ 0`,

where the `log (o x)` terms cancel. Non-negativity of the gap is `klDivPmf_nonneg`,
and the equality condition is `klDivPmf_eq_zero_iff_pmf`.

The argument order `klDivPmf p b` (true distribution first, bet second) is load-bearing:
the log-difference and vanishing lemmas require the *second* argument to be positive,
which is provided by the full-support bet hypothesis `hb_pos`, not by `p`.

Positivity of `b` is a genuine correctness precondition, not a bundling of the proof
core: since Lean sets `Real.log 0 = 0`, a zero bet on a live horse (`b x = 0`, `p x > 0`)
would contribute `0` instead of the true `−∞` (ruin), which would make the inequality
false. It plays the same role as the full-support reference pmf in the maximum-entropy
theorems.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 6.1.2.
-/

namespace InformationTheory.Shannon.Gambling

open Real
open InformationTheory.Shannon.CsiszarProjection (klDivPmf klDivPmf_nonneg)
open InformationTheory.Shannon.MaxEntropyConstrained (klDivPmf_eq_zero_iff_pmf)
open InformationTheory.Shannon.HoeffdingTradeoffExp (klDivPmf_eq_log_diff_sum_of_Q_pos)
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- The **doubling rate** of a bet `b` under odds `o` when the true win law is `p`:
the expected log growth of wealth per race, `∑ x, p x · log (b x · o x)`. -/
noncomputable def doublingRate (b o p : α → ℝ) : ℝ :=
  ∑ x, p x * Real.log (b x * o x)

/-- Closed form for the doubling rate of the proportional (Kelly) bet `b = p`:
`W(p, o, p) = ∑ x, p x · log (o x) − H(p)`, where `H(p) = ∑ x, negMulLog (p x)`. -/
theorem doublingRate_proportional_eq (p o : α → ℝ) (hp : p ∈ stdSimplex ℝ α)
    (ho : ∀ x, 0 < o x) :
    doublingRate p o p = (∑ x, p x * Real.log (o x)) - ∑ x, Real.negMulLog (p x) := by
  unfold doublingRate
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rcases eq_or_lt_of_le (hp.1 x) with hx0 | hxpos
  · have hpx : p x = 0 := hx0.symm
    rw [hpx]; simp
  · rw [Real.log_mul hxpos.ne' (ho x).ne', Real.negMulLog]
    ring

/-- The gap between the optimal and an arbitrary doubling rate is a KL divergence:
`W(p, o, p) − W(b, o, p) = klDivPmf p b`. The `log (o x)` terms cancel. -/
lemma doublingRate_gap_eq_klDivPmf (p b o : α → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (hb : b ∈ stdSimplex ℝ α)
    (hb_pos : ∀ x, 0 < b x) (ho : ∀ x, 0 < o x) :
    doublingRate p o p - doublingRate b o p = klDivPmf p b := by
  -- `p` sums to `1`, so the alphabet is nonempty (needed by the log-difference lemma).
  haveI : Nonempty α := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hp.2
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    norm_num at this
  -- The log-difference lemma also leaks a `MeasurableSpace`/`MeasurableSingletonClass`
  -- requirement from its section, irrelevant to the measure-free conclusion; supply the
  -- discrete structure.
  letI : MeasurableSpace α := ⊤
  haveI : MeasurableSingletonClass α := ⟨fun _ ↦ trivial⟩
  rw [klDivPmf_eq_log_diff_sum_of_Q_pos hp.1 hp.2 hb.2 hb_pos]
  unfold doublingRate
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ ↦ ?_)
  rcases eq_or_lt_of_le (hp.1 x) with hx0 | hxpos
  · have hpx : p x = 0 := hx0.symm
    rw [hpx]; ring
  · rw [Real.log_mul hxpos.ne' (ho x).ne', Real.log_mul (hb_pos x).ne' (ho x).ne']
    ring

/-- **Theorem 6.1.2** (Cover–Thomas): proportional (Kelly) betting maximizes the
doubling rate. For any full-support bet `b` and positive odds `o`,
`W(b, o, p) ≤ W(p, o, p)`.
@audit:ok — independent audit 2026-07-04: sorryAx-free (`[propext, Classical.choice,
Quot.sound]`); `hb_pos` is a genuine correctness precondition (counterexample without it:
`p=(1/2,1/2)`, `o=(2,2)`, `b=(1,0)` gives `W(b,o,p)=(1/2)log 2 > 0 = W(p,o,p)` since
`log 0 = 0` erases ruin), not load-bearing; gap = `klDivPmf p b ≥ 0` genuine. -/
@[entry_point]
theorem doublingRate_le_proportional (p b o : α → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (hb : b ∈ stdSimplex ℝ α)
    (hb_pos : ∀ x, 0 < b x) (ho : ∀ x, 0 < o x) :
    doublingRate b o p ≤ doublingRate p o p := by
  have hgap := doublingRate_gap_eq_klDivPmf p b o hp hb hb_pos ho
  have hnn := klDivPmf_nonneg p b hp.1 (fun a ↦ (hb_pos a).le)
  linarith

/-- The doubling rate is maximized by `b` iff `b` is the proportional (Kelly) bet
`b = p`.
@audit:ok — independent audit 2026-07-04: sorryAx-free (`[propext, Classical.choice,
Quot.sound]`); equality direction genuine via `klDivPmf_eq_zero_iff_pmf hp hb hb_pos`
(`klDivPmf p b = 0 ↔ p = b`) flipped by `eq_comm`, non-circular. -/
@[entry_point]
theorem doublingRate_eq_proportional_iff (p b o : α → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (hb : b ∈ stdSimplex ℝ α)
    (hb_pos : ∀ x, 0 < b x) (ho : ∀ x, 0 < o x) :
    doublingRate b o p = doublingRate p o p ↔ b = p := by
  have hgap := doublingRate_gap_eq_klDivPmf p b o hp hb hb_pos ho
  rw [show (doublingRate b o p = doublingRate p o p ↔ klDivPmf p b = 0) from
      ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩,
    klDivPmf_eq_zero_iff_pmf hp hb hb_pos]
  exact eq_comm

/-- Conservation law: the optimal doubling rate plus the entropy of `p` equals the
expected log-odds, `W(p, o, p) + H(p) = ∑ x, p x · log (o x)`. -/
theorem doublingRate_proportional_add_entropy (p o : α → ℝ)
    (hp : p ∈ stdSimplex ℝ α) (ho : ∀ x, 0 < o x) :
    doublingRate p o p + ∑ x, Real.negMulLog (p x) = ∑ x, p x * Real.log (o x) := by
  have h := doublingRate_proportional_eq p o hp ho
  linarith

end InformationTheory.Shannon.Gambling
