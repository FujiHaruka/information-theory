import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup

/-!
# Cramér's theorem (T1-C, Tier 0 baseline)

This file publishes the **Legendre transform** of a real-valued function and the
**Cramér rate function** (`I(a) = Λ^*(a)` for `Λ = cgf X μ`), together with the
basic properties needed for the upper / lower bounds of Cramér's large deviation
theorem.

The full Cover-Thomas Theorem 11.4.1 (the upper and lower bounds on
`(1/n) log P[Sₙ ≥ na]` as `n → ∞`) is left as Tier 1 / Tier 2 follow-ups; this
file keeps the surface minimal so it can be shipped as a stable foundation.

## 主定義

* `legendre Λ a := sSup ((fun lam => lam * a - Λ lam) '' Set.univ)` — Mathlib
  に Legendre / convex conjugate API は存在しないため自前で定義する。
* `cramerRate X μ a := legendre (cgf X μ) a` — Cramér rate function.

## Tier 0 publish 内容

* `legendre_apply_le` — `BddAbove` 仮定下で `lam * a - Λ lam ≤ legendre Λ a`.
* `legendre_nonneg` — `Λ 0 = 0` + `BddAbove` 仮定下で `0 ≤ legendre Λ a`.
* `cramerRate_apply_le` — Cramér rate に翻訳した `legendre_apply_le`.
* `cramerRate_nonneg` — 確率測度では `cgf · μ 0 = 0` なので非負。
* `cgf_sum_eq_nsmul` — i.i.d. + 同分布なら `cgf (∑ Xᵢ) μ t = n · cgf (X 0) μ t`.
* `integrable_exp_mul_of_bounded` — bounded RV ⇒ 全 `t` で `exp (t * X)` integrable.
-/

namespace InformationTheory.Shannon.Cramer

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Tier 0 — `legendre` + `cramerRate` 定義 + 基本性質 -/

/-- **Legendre transform** of `Λ : ℝ → ℝ` at `a`: `Λ^*(a) := sup_λ (λ·a − Λ(λ))`.

Mathlib に Legendre 変換 / convex conjugate の汎用 API は (本稿時点で) 存在しない
ため、ここでは textbook 形そのまま `sSup` で定義する。`BddAbove` でない場合は
Mathlib 規約により `sSup = 0` 返却となるため、本ファイルの基本性質には
`BddAbove` 仮定を明示的に付ける。 -/
noncomputable def legendre (Λ : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)

/-- **Cramér rate function** `I(a) := Λ^*(a)` for `Λ := cgf X μ`. -/
noncomputable def cramerRate (X : Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ :=
  legendre (cgf X μ) a

/-- Each linear-minus-`Λ` value is ≤ the Legendre transform. -/
lemma legendre_apply_le (Λ : ℝ → ℝ) (a : ℝ)
    (h_bdd : BddAbove ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ))
    (lam : ℝ) :
    lam * a - Λ lam ≤ legendre Λ a := by
  refine le_csSup h_bdd ?_
  exact Set.mem_image_of_mem _ (Set.mem_univ lam)

/-- If `Λ 0 = 0` (e.g. `Λ = cgf X μ` for a probability measure), the Legendre
transform is non-negative whenever the supremum exists. -/
lemma legendre_nonneg (Λ : ℝ → ℝ) (hΛ0 : Λ 0 = 0) (a : ℝ)
    (h_bdd : BddAbove ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)) :
    0 ≤ legendre Λ a := by
  have h := legendre_apply_le Λ a h_bdd 0
  simpa [hΛ0] using h

/-- Cramér rate-function version of `legendre_apply_le`. -/
lemma cramerRate_apply_le (X : Ω → ℝ) (μ : Measure Ω) (a : ℝ)
    (h_bdd : BddAbove ((fun lam : ℝ => lam * a - cgf X μ lam) '' Set.univ))
    (lam : ℝ) :
    lam * a - cgf X μ lam ≤ cramerRate X μ a :=
  legendre_apply_le _ a h_bdd lam

/-- Cramér rate function is non-negative whenever the Legendre supremum exists
for a probability measure (then `cgf X μ 0 = 0`). -/
lemma cramerRate_nonneg [IsProbabilityMeasure μ] (X : Ω → ℝ) (a : ℝ)
    (h_bdd : BddAbove ((fun lam : ℝ => lam * a - cgf X μ lam) '' Set.univ)) :
    0 ≤ cramerRate X μ a :=
  legendre_nonneg _ (cgf_zero) a h_bdd

/-! ## Tier 0 — `cgf` sum + bounded-RV integrability helpers -/

/-- For a bounded real random variable on a finite measure space, the
exponential moment `exp (t * Y)` is integrable for every `t`. This is the
hypothesis-eliminator the Cramér chain uses to remove `Integrable` premises
from the main statements. -/
lemma integrable_exp_mul_of_bounded
    [IsFiniteMeasure μ] {Y : Ω → ℝ}
    (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * Y ω)) μ := by
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
  have h_meas : AEStronglyMeasurable (fun ω => Real.exp (t * Y ω)) μ :=
    ((measurable_const.mul hY_meas).exp).aestronglyMeasurable
  refine Integrable.mono' (integrable_const (Real.exp (|t| * M))) h_meas ?_
  exact Filter.Eventually.of_forall hC

/-- **i.i.d. CGF sum formula**: for an i.i.d. family `X : ℕ → Ω → ℝ` (with `X i`
identically distributed to `X 0` and the exponential moments integrable for
every `i`), `cgf (∑ i ∈ range n, X i) μ t = n · cgf (X 0) μ t`. -/
lemma cgf_sum_eq_nsmul {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_int : ∀ t i, Integrable (fun ω => Real.exp (t * X i ω)) μ)
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
    have : mgf (X i) μ t = mgf (X 0) μ t := congrArg (fun f => f t) h_mgf
    simp [cgf, this]
  rw [h_sum, Finset.sum_congr rfl h_each, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/-! ## Tier 1 — Cramér upper bound (per-n Chernoff bound, i.i.d. strengthening) -/

/-- **Per-n Chernoff bound** for the upper tail of an i.i.d. sum of bounded real
random variables (Cover-Thomas 11.4.1 upper half, point-wise in `n`).

We specialise Mathlib's single-variable Chernoff bound `measure_ge_le_exp_cgf`
at `X := ∑ i ∈ range n, X i` and fold in the i.i.d. cgf-sum identity
`cgf_sum_eq_nsmul`. The resulting bound is the headline statement of
Cover-Thomas's upper Cramér: tilt by any `lam ≥ 0` and the upper-tail
probability decays exponentially with rate at least `lam * a − Λ(lam)`. -/
lemma chernoff_bound_n_iid [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
    (a : ℝ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}
      ≤ Real.exp (-(n : ℝ) * (lam * a - cgf (X 0) μ lam)) := by
  -- Hypothesis pass-through: bounded RVs ⇒ all exponential moments integrable.
  have h_int : ∀ t i, Integrable (fun ω => Real.exp (t * X i ω)) μ := by
    intro t i
    obtain ⟨M, hM⟩ := h_bdd
    exact integrable_exp_mul_of_bounded (h_meas i) ⟨M, hM i⟩ t
  -- Build the integrability of `exp (lam * (∑ X i))` directly.
  have h_sum_meas_pt : Measurable (fun ω => ∑ i ∈ Finset.range n, X i ω) :=
    Finset.measurable_sum _ (fun i _ => h_meas i)
  have h_sum_bdd_pt :
      ∃ M', ∀ ω, |∑ i ∈ Finset.range n, X i ω| ≤ M' := by
    obtain ⟨M, hM⟩ := h_bdd
    refine ⟨(n : ℝ) * M, ?_⟩
    intro ω
    have h_le : |∑ i ∈ Finset.range n, X i ω| ≤ ∑ i ∈ Finset.range n, |X i ω| :=
      Finset.abs_sum_le_sum_abs _ _
    have h_each : ∑ i ∈ Finset.range n, |X i ω| ≤ ∑ _i ∈ Finset.range n, M :=
      Finset.sum_le_sum (fun i _ => hM i ω)
    have h_const : ∑ _i ∈ Finset.range n, M = (n : ℝ) * M := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact h_le.trans (h_each.trans h_const.le)
  have h_int_sum_pt :
      Integrable (fun ω => Real.exp (lam * ∑ i ∈ Finset.range n, X i ω)) μ :=
    integrable_exp_mul_of_bounded h_sum_meas_pt h_sum_bdd_pt lam
  -- Apply Mathlib Chernoff bound to the pointwise-sum at threshold `ε := a * n`.
  -- Convert `(∑ Xi) ω` and `∑ Xi ω` freely via `Finset.sum_apply`.
  have h_fun_eq :
      (fun ω => (∑ i ∈ Finset.range n, X i) ω)
        = fun ω => ∑ i ∈ Finset.range n, X i ω := by
    funext ω; rw [Finset.sum_apply]
  have h_int_sum : Integrable
      (fun ω => Real.exp (lam * (∑ i ∈ Finset.range n, X i) ω)) μ := by
    have : (fun ω => Real.exp (lam * (∑ i ∈ Finset.range n, X i) ω))
        = fun ω => Real.exp (lam * ∑ i ∈ Finset.range n, X i ω) := by
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

/-- **Per-n Cramér upper bound, log form**: for each `n ≥ 1` with positive tail
probability, `(1/n) · log P[a·n ≤ Sₙ] ≤ -(lam · a − Λ(lam))` for every
`lam ≥ 0`.

This is the log-form rearrangement of `chernoff_bound_n_iid`; taking the
supremum over `lam ≥ 0` would give `(1/n) log P ≤ -legendre Λ a` (provided the
Legendre transform is well-defined), but the supremum is left as a Tier 2
follow-up. -/
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

/-! ## Tier 2 — Cramér upper bound (limsup form) -/

/-- **Cramér upper bound, limsup form** (Cover-Thomas 11.4.1 upper half).

For each `lam ≥ 0`, the upper-tail probability of the i.i.d. sample sum decays
at exponential rate at least `lam * a − Λ(lam)`:

`limsup_n (1/n) log P[a·n ≤ Sₙ] ≤ -(lam · a − Λ(lam))`.

Taking the supremum over `lam ≥ 0` (and then justifying the agreement with the
unrestricted Legendre transform under `a ≥ 𝔼[X]`) recovers the textbook
`-cramerRate (X 0) μ a`; that supremum step is left for follow-up work.

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
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}))) :
    limsup (fun n : ℕ =>
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

end InformationTheory.Shannon.Cramer
