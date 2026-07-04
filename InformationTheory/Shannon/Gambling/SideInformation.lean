import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Gambling.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Gambling with side information (Cover–Thomas Theorem 6.1.3)

A horse race on a finite alphabet `α` (the outcome `X`) is run while a gambler observes
side information `Y` on a finite alphabet `γ`. The joint law is presented in factored
form `(pY, pXgivenY)`: `pY` is the law of `Y` and `pXgivenY y` is the conditional law of
`X` given `Y = y`. Betting a proportional (Kelly) strategy that depends on the observed
side information, the increment of the doubling rate obtained from `Y` equals the mutual
information `I(X; Y)`.

## Main definitions

* `sideMarginalX` — the `X`-marginal pmf `pX x = ∑ y, pY y · pXgivenY y x`.
* `sideInfoJoint` — the joint pmf `q (x, y) = pY y · pXgivenY y x` on `α × γ`.
* `condDoublingRate` — the conditional doubling rate `W(b | Y) = ∑ y, pY y · W(b y, o, pXgivenY y)`.
* `sideInfoMutualInfo` — the mutual information in symmetric form `I(X; Y) = H(X) + H(Y) − H(X, Y)`.

## Main statements

* `condDoublingRate_le_proportional` — conditional Kelly optimality: proportional betting on
  each observed `y` maximizes the conditional doubling rate.
* `sideInfo_doublingRate_increment_eq_mutualInfo` — Theorem 6.1.3: the increment of the
  optimal doubling rate due to the side information `Y` equals `I(X; Y)`.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Theorem 6.1.3.
-/

namespace InformationTheory.Shannon.Gambling

open Real
open scoped BigOperators

variable {α : Type*} [Fintype α] {γ : Type*} [Fintype γ]

/-- The `X`-marginal pmf obtained from the side-information factored law:
`pX x = ∑ y, pY y · pXgivenY y x`. -/
noncomputable def sideMarginalX (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) : α → ℝ :=
  fun x ↦ ∑ y, pY y * pXgivenY y x

/-- The joint pmf on `α × γ` of the outcome and the side information:
`q (x, y) = pY y · pXgivenY y x`. -/
noncomputable def sideInfoJoint (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) : α × γ → ℝ :=
  fun p ↦ pY p.2 * pXgivenY p.2 p.1

/-- The conditional (side-information) doubling rate of a strategy `b` that may depend on
the observed side information `y`:
`W(b | Y) = ∑ y, pY y · W(b y, o, pXgivenY y)`. -/
noncomputable def condDoublingRate
    (b : γ → α → ℝ) (o : α → ℝ) (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) : ℝ :=
  ∑ y, pY y * doublingRate (b y) o (pXgivenY y)

/-- The mutual information `I(X; Y)` in symmetric pmf form
`I(X; Y) = H(X) + H(Y) − H(X, Y)`, where the entropies are the finite-alphabet Shannon
entropies of the marginals and the joint.
@audit:ok — independent audit 2026-07-04: the symmetric form carries the joint entropy
`H(X, Y)` as an independent term, so it is not crafted to match the Phase-5 increment
`H(X) − H(X|Y)`; recognizing it as that increment forces a genuine detour through the
chain-rule bridge (`sideInfoJointEntropy_eq_chain`). Not trivial-circular. -/
noncomputable def sideInfoMutualInfo (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) : ℝ :=
  (∑ x, Real.negMulLog (sideMarginalX pY pXgivenY x))
    + (∑ y, Real.negMulLog (pY y))
    - (∑ p, Real.negMulLog (sideInfoJoint pY pXgivenY p))

lemma sideMarginalX_mem_stdSimplex {pY : γ → ℝ} {pXgivenY : γ → α → ℝ}
    (hpY : pY ∈ stdSimplex ℝ γ) (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α) :
    sideMarginalX pY pXgivenY ∈ stdSimplex ℝ α := by
  refine ⟨fun x ↦ ?_, ?_⟩
  · exact Finset.sum_nonneg (fun y _ ↦ mul_nonneg (hpY.1 y) ((hcond y).1 x))
  · simp only [sideMarginalX]
    rw [Finset.sum_comm]
    calc ∑ y, ∑ x, pY y * pXgivenY y x
        = ∑ y, pY y * ∑ x, pXgivenY y x :=
          Finset.sum_congr rfl (fun y _ ↦ by rw [Finset.mul_sum])
      _ = ∑ y, pY y * 1 := Finset.sum_congr rfl (fun y _ ↦ by rw [(hcond y).2])
      _ = 1 := by simp [hpY.2]

lemma sideInfoJoint_mem_stdSimplex {pY : γ → ℝ} {pXgivenY : γ → α → ℝ}
    (hpY : pY ∈ stdSimplex ℝ γ) (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α) :
    sideInfoJoint pY pXgivenY ∈ stdSimplex ℝ (α × γ) := by
  refine ⟨fun p ↦ ?_, ?_⟩
  · exact mul_nonneg (hpY.1 p.2) ((hcond p.2).1 p.1)
  · simp only [sideInfoJoint, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    calc ∑ y, ∑ x, pY y * pXgivenY y x
        = ∑ y, pY y * ∑ x, pXgivenY y x :=
          Finset.sum_congr rfl (fun y _ ↦ by rw [Finset.mul_sum])
      _ = ∑ y, pY y * 1 := Finset.sum_congr rfl (fun y _ ↦ by rw [(hcond y).2])
      _ = 1 := by simp [hpY.2]

lemma sideInfo_logOdds_cancel (o : α → ℝ) (pY : γ → ℝ) (pXgivenY : γ → α → ℝ) :
    (∑ y, pY y * (∑ x, pXgivenY y x * Real.log (o x)))
      = ∑ x, (sideMarginalX pY pXgivenY x) * Real.log (o x) := by
  simp only [sideMarginalX, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ ↦ ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ ↦ by ring)

lemma condDoublingRate_proportional_eq (o : α → ℝ) (pY : γ → ℝ) (pXgivenY : γ → α → ℝ)
    (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α) (ho : ∀ x, 0 < o x) :
    condDoublingRate pXgivenY o pY pXgivenY
      = (∑ x, (sideMarginalX pY pXgivenY x) * Real.log (o x))
        - ∑ y, pY y * (∑ x, Real.negMulLog (pXgivenY y x)) := by
  have key : condDoublingRate pXgivenY o pY pXgivenY
      = (∑ y, pY y * (∑ x, pXgivenY y x * Real.log (o x)))
        - ∑ y, pY y * (∑ x, Real.negMulLog (pXgivenY y x)) := by
    unfold condDoublingRate
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    rw [doublingRate_proportional_eq (pXgivenY y) o (hcond y) ho, mul_sub]
  rw [key, sideInfo_logOdds_cancel]

/-- Chain rule bridge `H(X, Y) = H(Y) + H(X | Y)` in pmf form (the honesty linchpin of
Theorem 6.1.3: it lets the symmetric `sideInfoMutualInfo` be recognized as the doubling-rate
increment without defining the latter to match).
@audit:ok — independent audit 2026-07-04: sorryAx-free (`[propext, Classical.choice,
Quot.sound]`); a genuine independent identity via the unconditional `Real.negMulLog_mul`
plus each row sum `∑ x, pXgivenY y x = 1`, and does not assume the conclusion. -/
lemma sideInfoJointEntropy_eq_chain (pY : γ → ℝ) (pXgivenY : γ → α → ℝ)
    (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α) :
    (∑ p, Real.negMulLog (sideInfoJoint pY pXgivenY p))
      = (∑ y, Real.negMulLog (pY y))
        + ∑ y, pY y * (∑ x, Real.negMulLog (pXgivenY y x)) := by
  have per_y : ∀ y, (∑ x, Real.negMulLog (pY y * pXgivenY y x))
      = Real.negMulLog (pY y) + pY y * (∑ x, Real.negMulLog (pXgivenY y x)) := by
    intro y
    calc ∑ x, Real.negMulLog (pY y * pXgivenY y x)
        = ∑ x, (pXgivenY y x * Real.negMulLog (pY y)
            + pY y * Real.negMulLog (pXgivenY y x)) :=
          Finset.sum_congr rfl (fun x _ ↦ by rw [Real.negMulLog_mul])
      _ = (∑ x, pXgivenY y x * Real.negMulLog (pY y))
            + ∑ x, pY y * Real.negMulLog (pXgivenY y x) := by rw [Finset.sum_add_distrib]
      _ = (∑ x, pXgivenY y x) * Real.negMulLog (pY y)
            + pY y * ∑ x, Real.negMulLog (pXgivenY y x) := by
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = Real.negMulLog (pY y) + pY y * (∑ x, Real.negMulLog (pXgivenY y x)) := by
          rw [(hcond y).2, one_mul]
  calc ∑ p, Real.negMulLog (sideInfoJoint pY pXgivenY p)
      = ∑ y, ∑ x, Real.negMulLog (pY y * pXgivenY y x) := by
        simp only [sideInfoJoint, Fintype.sum_prod_type]
        rw [Finset.sum_comm]
    _ = ∑ y, (Real.negMulLog (pY y) + pY y * (∑ x, Real.negMulLog (pXgivenY y x))) :=
        Finset.sum_congr rfl (fun y _ ↦ per_y y)
    _ = (∑ y, Real.negMulLog (pY y))
          + ∑ y, pY y * (∑ x, Real.negMulLog (pXgivenY y x)) := by
        rw [Finset.sum_add_distrib]

/-- **Conditional Kelly optimality** (Cover–Thomas, towards Theorem 6.1.3): proportional
betting on each observed value of the side information maximizes the conditional doubling
rate. For any full-support strategy `b` and positive odds `o`,
`W(b | Y) ≤ W(pXgivenY | Y)`.
@audit:ok — independent audit 2026-07-04: sorryAx-free (`[propext, Classical.choice,
Quot.sound]`); genuine per-`y` reuse of `doublingRate_le_proportional` weighted by
`pY y ≥ 0`, no bundling. All hypotheses are regularity preconditions (`hpY`/`hcond` pmf,
`hb`/`hb_pos` full-support bet, `ho` positive odds), none load-bearing. -/
@[entry_point]
theorem condDoublingRate_le_proportional
    (b : γ → α → ℝ) (o : α → ℝ) (pY : γ → ℝ) (pXgivenY : γ → α → ℝ)
    (hpY : pY ∈ stdSimplex ℝ γ)
    (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α)
    (hb : ∀ y, b y ∈ stdSimplex ℝ α) (hb_pos : ∀ y x, 0 < b y x)
    (ho : ∀ x, 0 < o x) :
    condDoublingRate b o pY pXgivenY ≤ condDoublingRate pXgivenY o pY pXgivenY := by
  unfold condDoublingRate
  refine Finset.sum_le_sum (fun y _ ↦ ?_)
  exact mul_le_mul_of_nonneg_left
    (doublingRate_le_proportional (pXgivenY y) (b y) o (hcond y) (hb y) (hb_pos y) ho)
    (hpY.1 y)

/-- **Theorem 6.1.3** (Cover–Thomas, gambling with side information): the increment of the
optimal doubling rate obtained from the side information `Y` equals the mutual information
`I(X; Y)`. Writing `W*(X | Y)` for the optimal conditional doubling rate and `W*(X)` for
the optimal doubling rate of the `X`-marginal, `W*(X | Y) − W*(X) = I(X; Y)`.
@audit:ok — independent audit 2026-07-04: sorryAx-free (`[propext, Classical.choice,
Quot.sound]`). Not trivial-circular: the increment reduces to `H(X) − H(X|Y)`, but the RHS
`sideInfoMutualInfo` is the symmetric `H(X) + H(Y) − H(X, Y)`, so the closing `linarith`
genuinely consumes the chain-rule bridge `sideInfoJointEntropy_eq_chain` to cancel the joint
entropy term (dropping it leaves the goal underdetermined). All hypotheses
(`hpY`/`hcond` pmf, `ho` positive odds) are regularity preconditions, none load-bearing. -/
@[entry_point]
theorem sideInfo_doublingRate_increment_eq_mutualInfo
    (o : α → ℝ) (pY : γ → ℝ) (pXgivenY : γ → α → ℝ)
    (hpY : pY ∈ stdSimplex ℝ γ)
    (hcond : ∀ y, pXgivenY y ∈ stdSimplex ℝ α)
    (ho : ∀ x, 0 < o x) :
    condDoublingRate pXgivenY o pY pXgivenY
      - doublingRate (sideMarginalX pY pXgivenY) o (sideMarginalX pY pXgivenY)
      = sideInfoMutualInfo pY pXgivenY := by
  have h1 := condDoublingRate_proportional_eq o pY pXgivenY hcond ho
  have h2 := doublingRate_proportional_eq (sideMarginalX pY pXgivenY) o
    (sideMarginalX_mem_stdSimplex hpY hcond) ho
  have h3 := sideInfoJointEntropy_eq_chain pY pXgivenY hcond
  simp only [sideInfoMutualInfo]
  linarith

end InformationTheory.Shannon.Gambling
