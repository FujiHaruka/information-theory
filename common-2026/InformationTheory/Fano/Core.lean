import InformationTheory.Fano
import InformationTheory.Fano.Entropy
import InformationTheory.Fano.BinaryJensen
import InformationTheory.Fano.CondEntropy
import InformationTheory.Meta.EntryPoint
import Mathlib.Algebra.BigOperators.Field

/-!
# Fano core proof: error indicator + chain-rule glue (Markov form)

Markov-form variant of the Fano core: the joint PMF lives on `(X, Xh)` where
both coordinates take values in the same finite alphabet `X`, and the error
event is `{(x, xh) : x ≠ xh}` rather than `{(x, y) : x ≠ decode y}`. The
deterministic-decoder form `decode : Y → X` is recovered downstream via the
data processing inequality.

* `errIndicator : X → X → Bool` — `decide (x ≠ xh)`.
* `withErr P : X → Bool → X → ℝ` — the 3-variable mass extending a finite
  joint PMF on `(X, Xh)` with the deterministic indicator coordinate.
* Bridge lemmas connecting `withErr`'s `Joint3.*` quantities to the
  original `FiniteJointPMF` ones, plus the specialization
  `withErr_condE_XY_zero` of M2's deterministic-collapse lemma.
* `withErr_marginalEY_true_sum` recovers the error probability from the
  `(E, Xh)` marginal at `E = true`.
-/

namespace InformationTheory

open scoped BigOperators
open Finset

/-! ## Joint3-level rearrangement for binary `E`

`H(E | Y)` of a 3-variable mass with `E = Bool` collapses to a weighted
sum of `binEntropy` over `Y`, where the weights are the `Y` marginal and
the points are the conditional probabilities `P(E = 1 | Y = y)`. -/

namespace Joint3

noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

lemma condE_Y_eq_sum_marginalY_mul_binEntropy
    (μ : X → Bool → Y → ℝ) (h_nn : ∀ x e y, 0 ≤ μ x e y) :
    condE_Y μ
      = ∑ y, marginalY μ y *
          Real.binEntropy (marginalEY μ true y / marginalY μ y) := by
  unfold condE_Y eyEntropy yEntropy
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Fintype.sum_bool, marginalY_eq_marginalEY_true_add_false]
  exact negMulLog_pair_sub_negMulLog_sum_eq_binEntropy _ _
    (marginalEY_nonneg μ h_nn true y)
    (marginalEY_nonneg μ h_nn false y)

/-- Per-`(e, y)` decomposition of `condX_EY`:

`H(X | E, Y) = ∑ e, ∑ y, [(∑ x, negMulLog μ(x, e, y)) - negMulLog (marginalEY μ e y)]`. -/
lemma condX_EY_eq_sum_per_ey
    {X E Y : Type*} [Fintype X] [Fintype E] [Fintype Y]
    (μ : X → E → Y → ℝ) :
    condX_EY μ
      = ∑ e, ∑ y, ((∑ x, (μ x e y).negMulLog)
                      - (marginalEY μ e y).negMulLog) := by
  unfold condX_EY jointEntropy eyEntropy
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]

end

end Joint3

/-! ## Non-normalized maximum-entropy bound

`(∑ a, negMulLog μ a) - negMulLog (∑ a, μ a) ≤ (∑ a, μ a) * log |S|` whenever
the support of `μ` is contained in a Finset `S`. This is M1's
`entropyOfFn_le_log_supportCard` re-expressed for an un-normalized mass,
obtained by scaling the normalized form by the total mass `m`. -/

noncomputable section

lemma sum_negMulLog_sub_le_sum_mul_log_card
    {α : Type*} [Fintype α] (μ : α → ℝ) (h_nn : ∀ a, 0 ≤ μ a)
    {S : Finset α} (h_supp : ∀ a ∉ S, μ a = 0) :
    (∑ a, (μ a).negMulLog) - (∑ a, μ a).negMulLog
      ≤ (∑ a, μ a) * Real.log S.card := by
  by_cases hm : (∑ a, μ a) = 0
  · have h_all_zero : ∀ a, μ a = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => h_nn a)).mp hm a (Finset.mem_univ a)
    have h_sum_neg : (∑ a, (μ a).negMulLog) = 0 :=
      Finset.sum_eq_zero (fun a _ => by rw [h_all_zero a, Real.negMulLog_zero])
    rw [h_sum_neg, hm]
    simp
  · have hm_nn : 0 ≤ (∑ a, μ a) := Finset.sum_nonneg (fun a _ => h_nn a)
    have hm_pos : 0 < (∑ a, μ a) := hm_nn.lt_of_ne (Ne.symm hm)
    set m := ∑ a, μ a with hm_def
    set q : α → ℝ := fun a => μ a / m with hq_def
    have hq_nn : ∀ a, 0 ≤ q a := fun a => div_nonneg (h_nn a) hm_pos.le
    have hq_sum : ∑ a, q a = 1 := by
      simp only [hq_def]
      rw [← Finset.sum_div, ← hm_def]
      exact div_self hm
    have hq_supp : ∀ a ∉ S, q a = 0 := fun a ha => by
      simp [hq_def, h_supp a ha]
    have hq_bound := entropyOfFn_le_log_supportCard q hq_nn hq_sum hq_supp
    have h_translate :
        (∑ a, (μ a).negMulLog) - m.negMulLog = m * entropyOfFn q := by
      unfold entropyOfFn
      rw [Finset.mul_sum]
      have hkey : ∀ a, m * (q a).negMulLog
                       = (μ a).negMulLog + μ a * Real.log m := by
        intro a
        simp only [hq_def]
        exact mul_negMulLog_div m (μ a) hm
      rw [Finset.sum_congr rfl (fun a _ => hkey a)]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← hm_def]
      unfold Real.negMulLog
      ring
    rw [h_translate]
    exact mul_le_mul_of_nonneg_left hq_bound hm_pos.le

end

namespace FiniteJointPMF

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Decoding-error indicator (Markov form): `errIndicator x xh = true`
iff the estimator `xh` differs from the source `x`. -/
def errIndicator : X → X → Bool :=
  fun x xh => decide (x ≠ xh)

/-- The 3-variable mass extending `P` with the decoding-error coordinate.

The point `(x, e, xh)` carries mass `P.mass x xh` exactly when `e` agrees
with `errIndicator x xh`, and `0` otherwise. -/
def withErr (P : FiniteJointPMF X X) :
    X → Bool → X → ℝ :=
  fun x e xh => if e = errIndicator x xh then P.mass x xh else 0

variable (P : FiniteJointPMF X X)

/-! ### Bridge to `Joint3` quantities -/

/-- The `(X, Xh)` marginal of `withErr` recovers the original 2-variable mass. -/
lemma withErr_marginalXY (x xh : X) :
    Joint3.marginalXY P.withErr x xh = P.mass x xh := by
  unfold Joint3.marginalXY withErr
  rw [Finset.sum_eq_single (errIndicator x xh)]
  · simp
  · intro e _ he
    simp [if_neg he]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The `Xh` marginal of `withErr` agrees with the original `marginalY`. -/
lemma withErr_marginalY (xh : X) :
    Joint3.marginalY P.withErr xh = P.marginalY xh := by
  unfold Joint3.marginalY marginalY
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact P.withErr_marginalXY x xh

lemma withErr_xyEntropy :
    Joint3.xyEntropy P.withErr = P.jointEntropy := by
  unfold Joint3.xyEntropy jointEntropy
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun xh _ => ?_)
  rw [P.withErr_marginalXY]

lemma withErr_yEntropy :
    Joint3.yEntropy P.withErr = P.yEntropy := by
  unfold Joint3.yEntropy yEntropy
  refine Finset.sum_congr rfl (fun xh _ => ?_)
  rw [P.withErr_marginalY]

/-- `H(X | Xh)` for the original PMF agrees with `Joint3.condX_Y` of the
3-variable extension. -/
lemma withErr_condX_Y :
    Joint3.condX_Y P.withErr = P.condEntropy := by
  unfold Joint3.condX_Y condEntropy
  rw [P.withErr_xyEntropy, P.withErr_yEntropy]

/-! ### `withErr` is deterministic in the `E` coordinate -/

lemma withErr_isDeterministic (x : X) (e : Bool) (xh : X) :
    P.withErr x e xh =
      if e = errIndicator x xh
        then Joint3.marginalXY P.withErr x xh
        else 0 := by
  rw [P.withErr_marginalXY]
  rfl

/-- `H(E | X, Xh) = 0` for the deterministic indicator extension. -/
theorem withErr_condE_XY_zero :
    Joint3.condE_XY P.withErr = 0 :=
  Joint3.condE_XY_zero_of_deterministic
    (μ := P.withErr)
    (f := fun x xh => errIndicator x xh)
    (fun x e xh => P.withErr_isDeterministic x e xh)

/-! ### Marginal of `E = true` equals the error probability -/

lemma withErr_marginalEY_true_sum :
    (∑ xh, Joint3.marginalEY P.withErr true xh) = P.errorProb := by
  unfold Joint3.marginalEY errorProb
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun xh _ => ?_)
  unfold withErr errIndicator
  by_cases hx : x = xh
  · simp [hx]
  · simp [hx]

/-! ### M5(2): `H(E | Xh) ≤ binEntropy Pe` -/

lemma withErr_nonneg : ∀ x e xh, 0 ≤ P.withErr x e xh := by
  intro x e xh
  unfold withErr
  split_ifs
  · exact P.mass_nonneg x xh
  · exact le_refl 0

/-- The `Xh`-marginal sum on `withErr` equals 1 (since `P` is a PMF). -/
lemma withErr_marginalY_sum :
    (∑ xh, Joint3.marginalY P.withErr xh) = 1 := by
  simp only [P.withErr_marginalY]
  show (∑ xh, P.marginalY xh) = 1
  unfold marginalY
  rw [Finset.sum_comm]
  exact P.sum_mass

/-- The conditional entropy `H(E | Xh)` of the indicator extension is
bounded above by `binEntropy` of the estimator's error probability. -/
theorem withErr_condE_Y_le_binEntropy_errorProb :
    Joint3.condE_Y P.withErr ≤ Real.binEntropy P.errorProb := by
  rw [Joint3.condE_Y_eq_sum_marginalY_mul_binEntropy
        P.withErr P.withErr_nonneg]
  -- Step: weights, points, Jensen.
  have h_nn := P.withErr_nonneg
  have h_w_nn : ∀ xh, 0 ≤ Joint3.marginalY P.withErr xh :=
    Joint3.marginalY_nonneg _ h_nn
  have h_w_sum := P.withErr_marginalY_sum
  have h_p_mem : ∀ xh,
      Joint3.marginalEY P.withErr true xh /
      Joint3.marginalY P.withErr xh ∈ Set.Icc (0 : ℝ) 1 := by
    intro xh
    refine ⟨div_nonneg
      (Joint3.marginalEY_nonneg _ h_nn _ _) (h_w_nn _), ?_⟩
    by_cases hm : Joint3.marginalY P.withErr xh = 0
    · rw [hm, div_zero]; exact zero_le_one
    · apply div_le_one_of_le₀
      · rw [Joint3.marginalY_eq_marginalEY_true_add_false]
        linarith [Joint3.marginalEY_nonneg _ h_nn false xh]
      · exact h_w_nn _
  have hjensen := binEntropy_jensen_finset
    (fun xh => Joint3.marginalY P.withErr xh)
    (fun xh => Joint3.marginalEY P.withErr true xh /
              Joint3.marginalY P.withErr xh)
    h_w_nn h_w_sum h_p_mem
  -- Show ∑ xh, m_xh * (t_xh / m_xh) = ∑ xh, t_xh = errorProb.
  have h_per_y : ∀ xh,
      Joint3.marginalY P.withErr xh *
      (Joint3.marginalEY P.withErr true xh /
       Joint3.marginalY P.withErr xh)
      = Joint3.marginalEY P.withErr true xh := by
    intro xh
    by_cases hm : Joint3.marginalY P.withErr xh = 0
    · have hsum := Joint3.marginalY_eq_marginalEY_true_add_false
        P.withErr xh
      rw [hm] at hsum
      have h_t_nn := Joint3.marginalEY_nonneg _ h_nn true xh
      have h_f_nn := Joint3.marginalEY_nonneg _ h_nn false xh
      have h_t_zero : Joint3.marginalEY P.withErr true xh = 0 :=
        le_antisymm (by linarith) h_t_nn
      rw [hm, h_t_zero]; simp
    · field_simp
  have h_inner_sum :
      (∑ xh, Joint3.marginalY P.withErr xh *
            (Joint3.marginalEY P.withErr true xh /
             Joint3.marginalY P.withErr xh))
        = P.errorProb := by
    calc (∑ xh, _) = ∑ xh, Joint3.marginalEY P.withErr true xh :=
          Finset.sum_congr rfl (fun xh _ => h_per_y xh)
      _ = P.errorProb := P.withErr_marginalEY_true_sum
  rw [h_inner_sum] at hjensen
  exact hjensen

/-! ### M5(3): `H(X | E, Xh) ≤ Pe * log(|X| - 1)` -/

/-- The conditional entropy `H(X | E, Xh)` of the indicator extension is
bounded above by `Pe * log(|X| - 1)`. -/
theorem withErr_condX_EY_le
    (hcard : 1 ≤ Fintype.card X) :
    Joint3.condX_EY P.withErr
      ≤ P.errorProb * Real.log ((Fintype.card X : ℝ) - 1) := by
  rw [Joint3.condX_EY_eq_sum_per_ey, Fintype.sum_bool]
  -- After Fintype.sum_bool: (∑ xh, true_term) + (∑ xh, false_term).
  -- Bound each per-xh term using sum_negMulLog_sub_le_sum_mul_log_card.
  have h_nn := P.withErr_nonneg
  -- Per-xh bound for e = false: support = {xh}, log 1 = 0.
  have h_false_per_y : ∀ xh,
      (∑ x, (P.withErr x false xh).negMulLog)
        - (Joint3.marginalEY P.withErr false xh).negMulLog ≤ 0 := by
    intro xh
    have h := sum_negMulLog_sub_le_sum_mul_log_card
      (μ := fun x => P.withErr x false xh)
      (h_nn := fun x => h_nn x false xh)
      (S := ({xh} : Finset X))
      (h_supp := fun x hx => by
        simp only [Finset.mem_singleton] at hx
        unfold withErr errIndicator
        have hd : decide (x ≠ xh) = true := decide_eq_true hx
        simp [hd])
    rw [Finset.card_singleton, Nat.cast_one, Real.log_one, mul_zero] at h
    show (∑ x, (P.withErr x false xh).negMulLog)
          - (Joint3.marginalEY P.withErr false xh).negMulLog ≤ 0
    exact h
  -- Per-xh bound for e = true: support = univ \ {xh}, |S| = |X| - 1.
  have h_true_per_y : ∀ xh,
      (∑ x, (P.withErr x true xh).negMulLog)
        - (Joint3.marginalEY P.withErr true xh).negMulLog
      ≤ Joint3.marginalEY P.withErr true xh *
            Real.log ((Fintype.card X : ℝ) - 1) := by
    intro xh
    have h := sum_negMulLog_sub_le_sum_mul_log_card
      (μ := fun x => P.withErr x true xh)
      (h_nn := fun x => h_nn x true xh)
      (S := (Finset.univ \ ({xh} : Finset X)))
      (h_supp := fun x hx => by
        have hxd : x = xh := by
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
            true_and, not_not] at hx
          exact hx
        unfold withErr errIndicator
        have hd : decide (x ≠ xh) = false :=
          decide_eq_false (fun hne => hne hxd)
        simp [hd])
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_univ, Finset.card_singleton,
        Nat.cast_sub hcard, Nat.cast_one] at h
    show (∑ x, (P.withErr x true xh).negMulLog)
          - (Joint3.marginalEY P.withErr true xh).negMulLog
        ≤ Joint3.marginalEY P.withErr true xh *
              Real.log ((Fintype.card X : ℝ) - 1)
    exact h
  -- Combine the per-xh bounds.
  have h_true_total :
      (∑ xh, ((∑ x, (P.withErr x true xh).negMulLog)
              - (Joint3.marginalEY P.withErr true xh).negMulLog))
        ≤ P.errorProb * Real.log ((Fintype.card X : ℝ) - 1) := by
    calc (∑ xh, _)
        ≤ ∑ xh, Joint3.marginalEY P.withErr true xh *
                  Real.log ((Fintype.card X : ℝ) - 1) :=
          Finset.sum_le_sum (fun xh _ => h_true_per_y xh)
      _ = (∑ xh, Joint3.marginalEY P.withErr true xh) *
              Real.log ((Fintype.card X : ℝ) - 1) := by
            rw [← Finset.sum_mul]
      _ = P.errorProb * Real.log ((Fintype.card X : ℝ) - 1) := by
            rw [P.withErr_marginalEY_true_sum]
  have h_false_total :
      (∑ xh, ((∑ x, (P.withErr x false xh).negMulLog)
              - (Joint3.marginalEY P.withErr false xh).negMulLog))
        ≤ 0 := by
    calc (∑ xh, _) ≤ ∑ xh, (0 : ℝ) :=
            Finset.sum_le_sum (fun xh _ => h_false_per_y xh)
      _ = 0 := by simp
  linarith

/-! ### M6: assembled Fano core inequality -/

/-- Fano's core inequality (Markov form):
`H(X | Xh) ≤ qaryEntropy |X| P.errorProb`. -/
@[entry_point]
theorem fano_core (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ Real.qaryEntropy (Fintype.card X) P.errorProb := by
  rw [← P.withErr_condX_Y]
  -- Decompose: condX_Y = condE_Y + condX_EY (via chain rules + H(E | X, Xh) = 0).
  have h_chain1 :
      Joint3.condXE_Y P.withErr
        = Joint3.condX_Y P.withErr + Joint3.condE_XY P.withErr :=
    Joint3.chain_rule_X_first P.withErr
  have h_chain2 :
      Joint3.condXE_Y P.withErr
        = Joint3.condE_Y P.withErr + Joint3.condX_EY P.withErr :=
    Joint3.chain_rule_E_first P.withErr
  have h_zero := P.withErr_condE_XY_zero
  have h_decompose :
      Joint3.condX_Y P.withErr
        = Joint3.condE_Y P.withErr + Joint3.condX_EY P.withErr := by
    have hsum :
        Joint3.condXE_Y P.withErr = Joint3.condX_Y P.withErr := by
      rw [h_chain1, h_zero, add_zero]
    linarith [h_chain2]
  rw [h_decompose]
  -- Bound each summand by M5(2) and M5(3).
  have h2 := P.withErr_condE_Y_le_binEntropy_errorProb
  have h3 := P.withErr_condX_EY_le (by linarith : 1 ≤ Fintype.card X)
  -- Identify the sum with `qaryEntropy`.
  have h_qary :
      Real.binEntropy P.errorProb
          + P.errorProb * Real.log ((Fintype.card X : ℝ) - 1)
        = Real.qaryEntropy (Fintype.card X) P.errorProb :=
    (qaryEntropy_eq_binEntropy_add_log _ _).symm
  linarith

/-- The error probability is non-negative. -/
lemma errorProb_nonneg : 0 ≤ P.errorProb := by
  unfold errorProb
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro xh _
  split_ifs
  · exact le_refl 0
  · exact P.mass_nonneg x xh

/-- Fano's inequality (Markov form) in the textbook `fanoBoundRHS` form,
with no external `hcore` hypothesis. -/
@[entry_point]
theorem fano_inequality (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ fanoBoundRHSOfAlphabet X P.errorProb :=
  fano_inequality_of_core P (P.fano_core hcard)

/-- Strict inverse form of Fano's inequality on the increasing branch
(Markov form), with no external `hcore` hypothesis (and `errorProb`
non-negativity absorbed into the proof). -/
@[entry_point]
theorem error_lower_bound (hcard : 2 ≤ Fintype.card X) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 - 1 / (Fintype.card X : ℝ))
    (hPe1 : P.errorProb ≤ 1 - 1 / (Fintype.card X : ℝ))
    (haH : Real.qaryEntropy (Fintype.card X) a < P.condEntropy) :
    a < P.errorProb :=
  error_lower_bound_of_core P hcard ha0 ha1
    P.errorProb_nonneg hPe1
    (P.fano_core hcard) haH

end

end FiniteJointPMF
end InformationTheory
