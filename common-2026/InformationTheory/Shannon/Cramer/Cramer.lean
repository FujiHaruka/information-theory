import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import InformationTheory.Meta.EntryPoint

/-!
# Cramér's theorem

The Legendre transform of a real-valued function and the Cramér rate
function (`I(a) = Λ^*(a)` for `Λ = cgf X μ`), together with the upper bound of
Cramér's large deviation theorem (Cover–Thomas, Theorem 11.4.1, upper half) in
per-`n` Chernoff, log, and limsup forms. The lower bound is developed downstream
in `CramerGeneralLower.lean`.

## Main definitions

* `legendre Λ a` — the Legendre transform `Λ^*(a) := sup_λ (λ·a − Λ(λ))`.
* `cramerRate X μ a` — the Cramér rate function `I(a) := (cgf X μ)^*(a)`.

## Main statements

* `cramerRate_apply_le`, `cramerRate_nonneg` — basic bounds on the rate function.
* `chernoff_bound_n_iid` — per-`n` Chernoff bound for the upper tail of an i.i.d.
  bounded sum.
* `cramer_upper`, `cramer_upper_legendre` — the limsup-form upper bound.
* `integral_tilted_eq_deriv_cgf`, `klDiv_tilted_eq` — tilted change-of-measure
  identities used by the lower bound.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006. Theorem 11.4.1.
-/

namespace InformationTheory.Shannon.Cramer

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## `legendre` and `cramerRate`: definitions and basic properties -/

/-- The Legendre transform of `Λ : ℝ → ℝ` at `a`: `Λ^*(a) := sup_λ (λ·a − Λ(λ))`.

Mathlib has no general Legendre-transform / convex-conjugate API, so this is the
textbook `sSup` form. When the image set is not `BddAbove`, Mathlib returns
`sSup = 0`, so the basic properties below take an explicit `BddAbove` hypothesis. -/
noncomputable def legendre (Λ : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun lam : ℝ ↦ lam * a - Λ lam) '' Set.univ)

/-- Cramér rate function `I(a) := Λ^*(a)` for `Λ := cgf X μ`. -/
noncomputable def cramerRate (X : Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ :=
  legendre (cgf X μ) a

/-- Each linear-minus-`Λ` value is ≤ the Legendre transform. -/
lemma legendre_apply_le (Λ : ℝ → ℝ) (a : ℝ)
    (h_bdd : BddAbove ((fun lam : ℝ ↦ lam * a - Λ lam) '' Set.univ))
    (lam : ℝ) :
    lam * a - Λ lam ≤ legendre Λ a := by
  refine le_csSup h_bdd ?_
  exact Set.mem_image_of_mem _ (Set.mem_univ lam)

/-- If `Λ 0 = 0` (e.g. `Λ = cgf X μ` for a probability measure), the Legendre
transform is non-negative whenever the supremum exists. -/
lemma legendre_nonneg (Λ : ℝ → ℝ) (hΛ0 : Λ 0 = 0) (a : ℝ)
    (h_bdd : BddAbove ((fun lam : ℝ ↦ lam * a - Λ lam) '' Set.univ)) :
    0 ≤ legendre Λ a := by
  have h := legendre_apply_le Λ a h_bdd 0
  simpa [hΛ0] using h

/-- Cramér rate-function version of `legendre_apply_le`. -/
@[entry_point]
lemma cramerRate_apply_le (X : Ω → ℝ) (μ : Measure Ω) (a : ℝ)
    (h_bdd : BddAbove ((fun lam : ℝ ↦ lam * a - cgf X μ lam) '' Set.univ))
    (lam : ℝ) :
    lam * a - cgf X μ lam ≤ cramerRate X μ a :=
  legendre_apply_le _ a h_bdd lam

/-- Cramér rate function is non-negative whenever the Legendre supremum exists
for a probability measure (then `cgf X μ 0 = 0`). -/
@[entry_point]
lemma cramerRate_nonneg [IsProbabilityMeasure μ] (X : Ω → ℝ) (a : ℝ)
    (h_bdd : BddAbove ((fun lam : ℝ ↦ lam * a - cgf X μ lam) '' Set.univ)) :
    0 ≤ cramerRate X μ a :=
  legendre_nonneg _ (cgf_zero) a h_bdd

/-! ## `cgf` sum and bounded-RV integrability helpers -/

/-- For a bounded real random variable on a finite measure space, the
exponential moment `exp (t * Y)` is integrable for every `t`. This is the
hypothesis-eliminator the Cramér chain uses to remove `Integrable` premises
from the main statements. -/
lemma integrable_exp_mul_of_bounded
    [IsFiniteMeasure μ] {Y : Ω → ℝ}
    (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * Y ω)) μ := by
  obtain ⟨M, hM⟩ := h_bdd
  have hC : ∀ ω, |Real.exp (t * Y ω)| ≤ Real.exp (|t| * M) := by
    intro ω
    have h_abs : |t * Y ω| ≤ |t| * M := by
      rw [abs_mul]
      have hM_nn : 0 ≤ M := (abs_nonneg _).trans (hM ω)
      exact mul_le_mul_of_nonneg_left (hM ω) (abs_nonneg _)
    have h_le : t * Y ω ≤ |t| * M := (le_abs_self _).trans h_abs
    have h_exp_nonneg : 0 ≤ Real.exp (t * Y ω) := (Real.exp_pos _).le
    rw [abs_of_nonneg h_exp_nonneg]
    exact Real.exp_le_exp.mpr h_le
  have h_meas : AEStronglyMeasurable (fun ω ↦ Real.exp (t * Y ω)) μ :=
    ((measurable_const.mul hY_meas).exp).aestronglyMeasurable
  refine Integrable.mono' (integrable_const (Real.exp (|t| * M))) h_meas ?_
  exact Filter.Eventually.of_forall hC

/-- i.i.d. CGF sum formula: for an i.i.d. family `X : ℕ → Ω → ℝ` (with `X i`
identically distributed to `X 0` and the exponential moments integrable for
every `i`), `cgf (∑ i ∈ range n, X i) μ t = n · cgf (X 0) μ t`. -/
lemma cgf_sum_eq_nsmul {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_int : ∀ t i, Integrable (fun ω ↦ Real.exp (t * X i ω)) μ)
    (t : ℝ) (n : ℕ) :
    cgf (∑ i ∈ Finset.range n, X i) μ t = (n : ℝ) * cgf (X 0) μ t := by
  -- Step 1: i.i.d. cgf-sum identity gives `∑ i ∈ range n, cgf (X i) μ t`.
  have h_sum :
      cgf (∑ i ∈ Finset.range n, X i) μ t = ∑ i ∈ Finset.range n, cgf (X i) μ t := by
    refine h_indep.cgf_sum h_meas (s := Finset.range n) ?_
    intro i _
    exact h_int t i
  -- Step 2: each `cgf (X i) μ t = cgf (X 0) μ t` via `IdentDistrib`.
  have h_each : ∀ i ∈ Finset.range n, cgf (X i) μ t = cgf (X 0) μ t := by
    intro i _
    -- `mgf X μ = mgf Y μ'` from `IdentDistrib`, then `cgf` follows.
    have h_mgf : mgf (X i) μ = mgf (X 0) μ := mgf_congr_identDistrib (h_ident i)
    have : mgf (X i) μ t = mgf (X 0) μ t := congrArg (fun f ↦ f t) h_mgf
    simp [cgf, this]
  rw [h_sum, Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/-! ## Cramér upper bound: per-`n` Chernoff bound (i.i.d. strengthening) -/

/-- Per-`n` Chernoff bound for the upper tail of an i.i.d. sum of bounded real
random variables: tilting by any `lam ≥ 0`, the upper-tail probability decays
exponentially with rate at least `lam * a − Λ(lam)`. -/
lemma chernoff_bound_n_iid [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
    (a : ℝ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}
      ≤ Real.exp (-(n : ℝ) * (lam * a - cgf (X 0) μ lam)) := by
  -- Hypothesis pass-through: bounded RVs ⇒ all exponential moments integrable.
  have h_int : ∀ t i, Integrable (fun ω ↦ Real.exp (t * X i ω)) μ := by
    intro t i
    obtain ⟨M, hM⟩ := h_bdd
    exact integrable_exp_mul_of_bounded (h_meas i) ⟨M, hM i⟩ t
  -- Build the integrability of `exp (lam * (∑ X i))` directly.
  have h_sum_meas_pt : Measurable (fun ω ↦ ∑ i ∈ Finset.range n, X i ω) :=
    Finset.measurable_sum _ (fun i _ ↦ h_meas i)
  have h_sum_bdd_pt :
      ∃ M', ∀ ω, |∑ i ∈ Finset.range n, X i ω| ≤ M' := by
    obtain ⟨M, hM⟩ := h_bdd
    refine ⟨(n : ℝ) * M, ?_⟩
    intro ω
    have h_le : |∑ i ∈ Finset.range n, X i ω| ≤ ∑ i ∈ Finset.range n, |X i ω| :=
      Finset.abs_sum_le_sum_abs _ _
    have h_each : ∑ i ∈ Finset.range n, |X i ω| ≤ ∑ _i ∈ Finset.range n, M :=
      Finset.sum_le_sum (fun i _ ↦ hM i ω)
    have h_const : ∑ _i ∈ Finset.range n, M = (n : ℝ) * M := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact h_le.trans (h_each.trans h_const.le)
  have h_int_sum_pt :
      Integrable (fun ω ↦ Real.exp (lam * ∑ i ∈ Finset.range n, X i ω)) μ :=
    integrable_exp_mul_of_bounded h_sum_meas_pt h_sum_bdd_pt lam
  -- Apply Mathlib Chernoff bound to the pointwise-sum at threshold `ε := a * n`.
  -- Convert `(∑ Xi) ω` and `∑ Xi ω` freely via `Finset.sum_apply`.
  have h_fun_eq :
      (fun ω ↦ (∑ i ∈ Finset.range n, X i) ω)
        = fun ω ↦ ∑ i ∈ Finset.range n, X i ω := by
    funext ω; rw [Finset.sum_apply]
  have h_int_sum : Integrable
      (fun ω ↦ Real.exp (lam * (∑ i ∈ Finset.range n, X i) ω)) μ := by
    have : (fun ω ↦ Real.exp (lam * (∑ i ∈ Finset.range n, X i) ω))
        = fun ω ↦ Real.exp (lam * ∑ i ∈ Finset.range n, X i ω) := by
      funext ω; rw [Finset.sum_apply]
    rw [this]; exact h_int_sum_pt
  have h_chernoff :
      μ.real {ω | (a : ℝ) * n ≤ (∑ i ∈ Finset.range n, X i) ω}
        ≤ Real.exp (-lam * ((a : ℝ) * n) + cgf (∑ i ∈ Finset.range n, X i) μ lam) :=
    measure_ge_le_exp_cgf (X := ∑ i ∈ Finset.range n, X i) (μ := μ)
      ((a : ℝ) * n) hlam h_int_sum
  -- Translate measure set: `(∑ X i) ω = ∑ X i ω`.
  have h_set_eq :
      {ω | (a : ℝ) * n ≤ (∑ i ∈ Finset.range n, X i) ω}
        = {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω} := by
    ext ω
    simp [Finset.sum_apply]
  rw [h_set_eq] at h_chernoff
  -- Rewrite the exponent using the i.i.d. cgf-sum identity.
  have h_cgf_sum :
      cgf (∑ i ∈ Finset.range n, X i) μ lam = (n : ℝ) * cgf (X 0) μ lam :=
    cgf_sum_eq_nsmul h_indep h_meas h_ident h_int lam n
  -- Combine and refactor the exponent:
  -- `-lam * (a * n) + n * Λ(lam) = -n * (lam * a - Λ(lam))`.
  refine h_chernoff.trans ?_
  rw [h_cgf_sum]
  apply Real.exp_le_exp.mpr
  linarith

/-- Per-`n` Cramér upper bound, log form: for each `n ≥ 1` with positive tail
probability, `(1/n) · log P[a·n ≤ Sₙ] ≤ -(lam · a − Λ(lam))` for every
`lam ≥ 0`. -/
lemma cramer_log_bound_n_iid [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
    (a : ℝ) {n : ℕ} (hn : 0 < n)
    (h_pos : 0 < μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})
    (lam : ℝ) (hlam : 0 ≤ lam) :
    (1 / (n : ℝ)) * Real.log
        (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})
      ≤ -(lam * a - cgf (X 0) μ lam) := by
  have h_cb := chernoff_bound_n_iid (μ := μ) h_indep h_meas h_ident h_bdd a n lam hlam
  -- Take `log` on both sides; `log` is monotone on positives.
  have h_log_le :
      Real.log (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})
        ≤ -(n : ℝ) * (lam * a - cgf (X 0) μ lam) := by
    have h := Real.log_le_log h_pos h_cb
    rwa [Real.log_exp] at h
  -- Divide by `n > 0`.
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h_one_div_pos : 0 < (1 / (n : ℝ)) := by positivity
  have h_div :
      (1 / (n : ℝ)) * Real.log
        (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})
        ≤ (1 / (n : ℝ)) * (-(n : ℝ) * (lam * a - cgf (X 0) μ lam)) :=
    mul_le_mul_of_nonneg_left h_log_le h_one_div_pos.le
  refine h_div.trans (le_of_eq ?_)
  field_simp

/-! ## Cramér upper bound: limsup form -/

/-- **Cramér's theorem** (upper bound, limsup form): for each `lam ≥ 0`, the
upper-tail probability of the i.i.d. sample sum decays at exponential rate at
least `lam * a − Λ(lam)`:

`limsup_n (1/n) log P[a·n ≤ Sₙ] ≤ -(lam · a − Λ(lam))`.

Two technical hypotheses make the result clean:
* `h_pos` — the tail probability is eventually positive (e.g. when `a ≤ ess sup
  X`), so that `log` is finite.
* `h_cobdd` — the resulting log-rate sequence is cobounded below in the limsup
  sense. This holds whenever the sequence does not blow up to `-∞`, e.g. when
  the tail probabilities admit any sub-exponential lower bound. -/
theorem cramer_upper [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
    (a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (h_pos : ∀ᶠ n : ℕ in atTop,
      0 < μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})
    (h_cobdd : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}))) :
    limsup (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop
      ≤ -(lam * a - cgf (X 0) μ lam) := by
  -- Eventually `(1/n) log P ≤ -(lam · a − Λ(lam))` via `cramer_log_bound_n_iid`.
  have h_eventually :
      ∀ᶠ n : ℕ in atTop,
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})
          ≤ -(lam * a - cgf (X 0) μ lam) := by
    filter_upwards [eventually_gt_atTop 0, h_pos] with n hn h_pos_n
    exact cramer_log_bound_n_iid (μ := μ) h_indep h_meas h_ident h_bdd a hn h_pos_n
      lam hlam
  exact Filter.limsup_le_of_le h_cobdd h_eventually

/-- **Cramér's theorem** (upper bound, Legendre form): if the Legendre transform
of `Λ = cgf (X 0) μ` at `a` is attained by some non-negative `lam` (`hlam_opt`),
then

`limsup_n (1/n) log P[a·n ≤ Sₙ] ≤ -cramerRate (X 0) μ a`.

`hlam_opt` is a regularity precondition (it holds for `a ≥ 𝔼[X]` by convexity of
the Legendre transform), not part of the proof core.

See also `cramer_upper`. -/
theorem cramer_upper_legendre [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
    (a : ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hlam_opt : lam * a - cgf (X 0) μ lam = cramerRate (X 0) μ a)
    (h_pos : ∀ᶠ n : ℕ in atTop,
      0 < μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})
    (h_cobdd : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}))) :
    limsup (fun n : ℕ ↦
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop
      ≤ -cramerRate (X 0) μ a := by
  have h := cramer_upper (μ := μ) h_indep h_meas h_ident h_bdd a lam hlam h_pos h_cobdd
  rw [← hlam_opt]; exact h

/-! ## Cramér lower bound: tilted change-of-measure identities

The lower bound uses an exponential change-of-measure to the tilted measure
`μ_lam := μ.tilted (lam * X ·)`, where `lam` is chosen so that `Λ'(lam) = a`.
Under the tilted measure the mean of `X` equals `a`, a tilted-side law of large
numbers concentrates the sample mean near `a`, and converting back to `μ` via the
Radon–Nikodym derivative of `tilted` picks up an
`exp(-n · (lam · a − Λ(lam))) = exp(-n · cramerRate)` factor.

This file publishes the change-of-measure building blocks — `klDiv_tilted_eq`
(the KL-of-tilted identity) and `integral_tilted_eq_deriv_cgf` — that the
downstream lower bound consumes. -/

/-- Universal integrability for bounded RVs: a bounded random variable has
every `t ∈ ℝ` in its `integrableExpSet`, hence the whole real line lies in the
interior. This kills the `interior (integrableExpSet X μ)` hypothesis of
`integral_tilted_mul_self` / `variance_tilted_mul` in the bounded-RV setting. -/
lemma mem_interior_integrableExpSet_of_bounded
    [IsFiniteMeasure μ] {Y : Ω → ℝ}
    (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (t : ℝ) :
    t ∈ interior (integrableExpSet Y μ) := by
  have h_univ : integrableExpSet Y μ = Set.univ := by
    ext s
    simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact integrable_exp_mul_of_bounded hY_meas h_bdd s
  rw [h_univ, interior_univ]
  exact Set.mem_univ t

/-- The tilted measure of a bounded random variable is a probability measure. -/
lemma isProbabilityMeasure_tilted_of_bounded [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    IsProbabilityMeasure (μ.tilted (fun ω ↦ lam * Y ω)) :=
  isProbabilityMeasure_tilted (integrable_exp_mul_of_bounded hY_meas h_bdd lam)

/-- For a bounded random variable `Y`, the expectation of `Y` under
`μ.tilted (lam * Y ·)` equals the first derivative of `cgf Y μ` at `lam`. -/
@[entry_point]
lemma integral_tilted_eq_deriv_cgf [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    ∫ ω, Y ω ∂(μ.tilted (fun ω ↦ lam * Y ω)) = deriv (cgf Y μ) lam :=
  integral_tilted_mul_self (mem_interior_integrableExpSet_of_bounded hY_meas h_bdd lam)

/-- KL-of-tilted identity.

For a bounded real random variable `X : Ω → ℝ` on a probability measure `μ`,
the (integral form of the) Kullback-Leibler divergence between `μ.tilted (lam * X ·)`
and `μ` admits the closed form

`∫ ω, log (rnDeriv (μ.tilted (lam * X ·)) μ ω).toReal ∂(μ.tilted (lam * X ·))
  = lam * (μ.tilted (lam * X ·))[X] - cgf X μ lam`.

We work directly with the `∫ log (rnDeriv)` representation rather than the
`ℝ≥0∞`-valued `klDiv` to keep the algebraic identity transparent. -/
@[entry_point]
lemma klDiv_tilted_eq [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX_meas : Measurable X)
    (h_bdd : ∃ M, ∀ ω, |X ω| ≤ M)
    (lam : ℝ) :
    ∫ ω, Real.log ((μ.tilted (fun ω' ↦ lam * X ω')).rnDeriv μ ω).toReal
        ∂(μ.tilted (fun ω' ↦ lam * X ω'))
      = lam * ∫ ω, X ω ∂(μ.tilted (fun ω' ↦ lam * X ω')) - cgf X μ lam := by
  -- The function `f` in `Measure.tilted` is `(fun ω => lam * X ω)`.
  set f : Ω → ℝ := fun ω ↦ lam * X ω with hf_def
  have h_int : Integrable (fun ω ↦ Real.exp (f ω)) μ :=
    integrable_exp_mul_of_bounded hX_meas h_bdd lam
  -- Bounded RV ⇒ lam in interior of integrableExpSet X μ.
  have h_mem : lam ∈ interior (integrableExpSet X μ) :=
    mem_interior_integrableExpSet_of_bounded hX_meas h_bdd lam
  -- Step 1: `log rnDeriv = f − log (∫ exp f ∂μ)` μ-a.e.
  have h_rn_eq : (fun ω ↦ Real.log ((μ.tilted f).rnDeriv μ ω).toReal)
      =ᵐ[μ] fun ω ↦ f ω - Real.log (∫ x, Real.exp (f x) ∂μ) :=
    log_rnDeriv_tilted_left_self h_int
  -- Step 2: transfer the a.e.-equality from `μ` to `μ.tilted f`.
  have h_ac : μ.tilted f ≪ μ := tilted_absolutelyContinuous μ f
  have h_rn_eq' : (fun ω ↦ Real.log ((μ.tilted f).rnDeriv μ ω).toReal)
      =ᵐ[μ.tilted f] fun ω ↦ f ω - Real.log (∫ x, Real.exp (f x) ∂μ) :=
    h_ac.ae_eq h_rn_eq
  -- Step 3: rewrite the LHS integral using h_rn_eq'.
  have h_lhs :
      ∫ ω, Real.log ((μ.tilted f).rnDeriv μ ω).toReal ∂(μ.tilted f)
        = ∫ ω, f ω - Real.log (∫ x, Real.exp (f x) ∂μ) ∂(μ.tilted f) :=
    integral_congr_ae h_rn_eq'
  -- Step 4: tilted is a probability measure.
  haveI h_prob : IsProbabilityMeasure (μ.tilted f) := isProbabilityMeasure_tilted h_int
  -- Step 5: split the integral.
  have h_int_X : Integrable X (μ.tilted f) := by
    have h_memLp : MemLp X 1 (μ.tilted f) := memLp_tilted_mul h_mem 1
    exact memLp_one_iff_integrable.mp h_memLp
  have h_int_f : Integrable f (μ.tilted f) := by
    show Integrable (fun ω ↦ lam * X ω) (μ.tilted f)
    exact h_int_X.const_mul lam
  rw [h_lhs, integral_sub h_int_f (integrable_const _), integral_const,
    probReal_univ, one_smul]
  -- Now LHS = (∫ f ∂tilted) − log (∫ exp f ∂μ) = lam · ∫ X − cgf X μ lam.
  have h_f_split : ∫ ω, f ω ∂(μ.tilted f) = lam * ∫ ω, X ω ∂(μ.tilted f) := by
    show ∫ ω, lam * X ω ∂(μ.tilted f) = lam * ∫ ω, X ω ∂(μ.tilted f)
    rw [integral_const_mul]
  rw [h_f_split]
  -- cgf X μ lam = log (mgf X μ lam) = log (∫ exp (lam * X) ∂μ).
  have h_cgf : cgf X μ lam = Real.log (∫ x, Real.exp (f x) ∂μ) := by
    unfold cgf mgf
    rfl
  rw [h_cgf]

/- NOTE: the Cramér lower-bound chain (`cramer_lower` / `cramer_lower_legendre` /
`cramer_tendsto`) has been relocated downstream to
`InformationTheory/Shannon/CramerGeneralLower.lean` (same namespace
`InformationTheory.Shannon.Cramer`), where it can be discharged against the
CLT-boundary headline `cramer_lower_boundary_unconditional` without an import
cycle.  The chain uses `cramer_upper_legendre` (above, stays here) on the upper
side. -/

end InformationTheory.Shannon.Cramer
