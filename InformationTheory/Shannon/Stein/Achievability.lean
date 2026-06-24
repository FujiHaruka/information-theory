import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AEP.Basic
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.MutualInfo
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Stein's lemma: achievability

Stein's lemma for binary hypothesis testing (Cover–Thomas, Theorem 11.8.3): the optimal
type-II error of an `n`-sample test with type-I error at most `ε` decays exponentially in `n`
at the rate of the Kullback–Leibler divergence `klDiv P Q`. This file develops the achievability
(lower bound) side: the log-likelihood-ratio plumbing, the Stein-typical set, and the
tensorization of the KL divergence.

## Main definitions

* `llrPmf P Q` — the alphabet-side log-likelihood ratio `log P{x} − log Q{x}`.
* `logLikelihoodRatio P Q Xs i` — the per-sample log-likelihood ratio along a process `Xs`.
* `steinTypicalSet P Q n ε` — blocks whose empirical log-likelihood ratio is within `ε` of
  `klDiv P Q`.

## Main statements

* `stein_strong_law` — the empirical mean of the log-likelihood ratio converges almost surely
  to `(klDiv P Q).toReal`.
* `stein_inProbability` — the same convergence holds in probability.
* `stein_achievability` — there exist `ε`-level tests whose type-II error decays at rate
  `klDiv P Q`.

## Implementation notes

* The log-likelihood-ratio plumbing is obtained as the two-distribution specialization of the
  AEP development, which lets most measurability, identical-distribution, and independence
  lemmas be reused rather than reproved.
* Over a finite alphabet `α` with `0 < Q.real {x}` for every `x`, all quantities are expanded
  point-wise, avoiding the general Radon–Nikodym derivative machinery for product measures.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.),
  Wiley, 2006. Theorem 11.8.3.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Log-likelihood ratio plumbing -/

/-- The alphabet-side log-likelihood ratio `log P{x} − log Q{x}`. On the support of `P` and
assuming `Q{x} > 0` for all `x`, this equals `Real.log ((P.rnDeriv Q x).toReal)`. -/
noncomputable def llrPmf (P Q : Measure α) : α → ℝ :=
  fun x ↦ Real.log (P.real {x}) - Real.log (Q.real {x})

omit [DecidableEq α] [Nonempty α] in
lemma measurable_llrPmf (P Q : Measure α) : Measurable (llrPmf P Q) :=
  measurable_of_finite _

/-- Per-symbol log-likelihood ratio: `llrPmf P Q (Xs i ω)`. -/
noncomputable def logLikelihoodRatio
    (P Q : Measure α) (Xs : ℕ → Ω → α) (i : ℕ) : Ω → ℝ :=
  fun ω ↦ llrPmf P Q (Xs i ω)

omit [MeasurableSpace Ω] [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSingletonClass α] in
@[entry_point]
lemma logLikelihoodRatio_eq_comp
    (P Q : Measure α) (Xs : ℕ → Ω → α) (i : ℕ) :
    logLikelihoodRatio P Q Xs i = llrPmf P Q ∘ Xs i := rfl

omit [DecidableEq α] [Nonempty α] in
lemma measurable_logLikelihoodRatio
    (P Q : Measure α) (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (i : ℕ) :
    Measurable (logLikelihoodRatio P Q Xs i) :=
  (measurable_llrPmf P Q).comp (hXs i)

omit [DecidableEq α] [Nonempty α] in
lemma integrable_logLikelihoodRatio
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α)
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (i : ℕ) :
    Integrable (logLikelihoodRatio P Q Xs i) μ := by
  have : IsProbabilityMeasure (μ.map (Xs i)) :=
    Measure.isProbabilityMeasure_map (hXs i).aemeasurable
  -- Any function on a finite discrete space is integrable for any finite measure.
  have h_int : Integrable (llrPmf P Q) (μ.map (Xs i)) := Integrable.of_finite
  exact h_int.comp_measurable (hXs i)

omit [DecidableEq α] [Nonempty α] in
/-- The expected log-likelihood ratio under `P` equals `(klDiv P Q).toReal`. -/
theorem integral_logLikelihoodRatio_under_P
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) :
    ∫ ω, logLikelihoodRatio P Q Xs 0 ω ∂μ = (klDiv P Q).toReal := by
  -- Step 1: push forward via `Xs 0`, replace `μ.map (Xs 0)` by `P`.
  have h_push : ∫ ω, logLikelihoodRatio P Q Xs 0 ω ∂μ = ∫ x, llrPmf P Q x ∂P := by
    have h1 : ∫ ω, logLikelihoodRatio P Q Xs 0 ω ∂μ
        = ∫ x, llrPmf P Q x ∂(μ.map (Xs 0)) := by
      rw [integral_map (hXs 0).aemeasurable
        (measurable_llrPmf P Q).aestronglyMeasurable]
      rfl
    rw [h1, hMap]
  rw [h_push]
  -- Step 2: collapse the integral to a finite sum over α.
  rw [integral_fintype (μ := P) Integrable.of_finite]
  -- Step 3: expand `(klDiv P Q).toReal` via `toReal_klDiv` (using `P ≪ Q` and
  -- integrability of `llr P Q` on a Fintype).
  have h_int_llr : Integrable (llr P Q) P := by
    refine ⟨(measurable_llr P Q).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ ↦
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  rw [toReal_klDiv hPQ h_int_llr]
  -- Both sides are now in `Real`. The KL side has shape
  -- `(∫ x, llr P Q x ∂P) + Q.real univ - P.real univ`.
  -- Since `P, Q` are probability measures, `Q.real univ = P.real univ = 1`,
  -- and the additive correction vanishes.
  have hPunivR : P.real Set.univ = 1 := probReal_univ
  have hQunivR : Q.real Set.univ = 1 := probReal_univ
  rw [hPunivR, hQunivR]
  -- Need: `∑ x, P.real {x} • llrPmf P Q x = ∫ x, llr P Q x ∂P + 1 - 1`.
  rw [add_sub_cancel_right]
  -- Now express RHS as `∫ x, llr P Q x ∂P` via `integral_fintype`.
  rw [integral_fintype (μ := P) h_int_llr]
  -- Per-`x` rewrite: `P.real {x} • llrPmf P Q x = P.real {x} • llr P Q x`.
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  -- Case split on whether `P.real {x} = 0`.
  by_cases hPx0 : P.real {x} = 0
  · simp [hPx0]
  · have hPx_pos : 0 < P.real {x} :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hPx0)
    have hQx_pos : 0 < Q.real {x} := hQpos x
    -- `(P.rnDeriv Q x).toReal = P.real {x} / Q.real {x}` at supported x.
    have h_rnD_div : (P.rnDeriv Q x).toReal = P.real {x} / Q.real {x} := by
      have h_wd : Q.withDensity (P.rnDeriv Q) = P :=
        Measure.withDensity_rnDeriv_eq P Q hPQ
      have h_eq : (Q.withDensity (P.rnDeriv Q)) {x} = P {x} := by rw [h_wd]
      rw [withDensity_apply _ (measurableSet_singleton x),
        lintegral_singleton] at h_eq
      have h_rnD_real : (P.rnDeriv Q x).toReal * Q.real {x} = P.real {x} := by
        rw [Measure.real, Measure.real, ← ENNReal.toReal_mul, h_eq]
      field_simp
      linarith [h_rnD_real]
    -- Now: `llr P Q x = log ((P.rnDeriv Q x).toReal) = log (P.real{x} / Q.real{x})`
    --      `= log (P.real{x}) - log (Q.real{x}) = llrPmf P Q x`.
    have h_llr_eq : llr P Q x = llrPmf P Q x := by
      show Real.log (P.rnDeriv Q x).toReal = Real.log (P.real {x}) - Real.log (Q.real {x})
      rw [h_rnD_div, Real.log_div hPx_pos.ne' hQx_pos.ne']
    show P.real {x} • llrPmf P Q x = P.real {x} • llr P Q x
    rw [h_llr_eq]

omit [DecidableEq α] [Nonempty α] in
lemma identDistrib_logLikelihoodRatio
    (μ : Measure Ω) (P Q : Measure α) (Xs : ℕ → Ω → α)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (i : ℕ) :
    IdentDistrib (logLikelihoodRatio P Q Xs i) (logLikelihoodRatio P Q Xs 0) μ μ := by
  simpa [logLikelihoodRatio_eq_comp] using (hident i).comp (measurable_llrPmf P Q)

omit [DecidableEq α] [Nonempty α] in
lemma indepFun_logLikelihoodRatio
    (μ : Measure Ω) (P Q : Measure α) (Xs : ℕ → Ω → α)
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j) :
    Pairwise fun i j ↦
      logLikelihoodRatio P Q Xs i ⟂ᵢ[μ] logLikelihoodRatio P Q Xs j := by
  intro i j hij
  have h := hindep hij
  have hpf := measurable_llrPmf P Q
  simpa [logLikelihoodRatio_eq_comp] using h.comp hpf hpf

omit [DecidableEq α] [Nonempty α] in
/-- The empirical mean of the per-sample log-likelihood ratio converges almost surely to
`(klDiv P Q).toReal`. -/
@[entry_point]
theorem stein_strong_law
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ ↦ (∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n)
      atTop
      (𝓝 (klDiv P Q).toReal) := by
  have hint : Integrable (logLikelihoodRatio P Q Xs 0) μ :=
    integrable_logLikelihoodRatio μ P Q Xs hXs 0
  have hindLR : Pairwise fun i j ↦
      logLikelihoodRatio P Q Xs i ⟂ᵢ[μ] logLikelihoodRatio P Q Xs j :=
    indepFun_logLikelihoodRatio μ P Q Xs hindep
  have hidLR : ∀ i, IdentDistrib (logLikelihoodRatio P Q Xs i)
      (logLikelihoodRatio P Q Xs 0) μ μ :=
    identDistrib_logLikelihoodRatio μ P Q Xs hident
  have h_lln := strong_law_ae_real (logLikelihoodRatio P Q Xs) hint hindLR hidLR
  have h_int_eq := integral_logLikelihoodRatio_under_P μ P Q Xs hXs hMap hPQ hQpos
  filter_upwards [h_lln] with ω hω
  simpa [h_int_eq] using hω

omit [DecidableEq α] [Nonempty α] in
/-- The empirical mean of the log-likelihood ratio converges to `(klDiv P Q).toReal` in
probability. -/
@[entry_point]
theorem stein_inProbability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ ↦ μ {ω | ε ≤ |((∑ i ∈ Finset.range n,
                                  logLikelihoodRatio P Q Xs i ω) / n)
                                - (klDiv P Q).toReal|})
      atTop
      (𝓝 0) := by
  set f : ℕ → Ω → ℝ :=
    fun n ω ↦ (∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n with hf_def
  set g : Ω → ℝ := fun _ ↦ (klDiv P Q).toReal with hg_def
  have h_meas_f : ∀ n, AEStronglyMeasurable (f n) μ := by
    intro n
    have h_sum_meas : Measurable
        (fun ω ↦ ∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) :=
      Finset.measurable_sum _ fun i _ ↦ measurable_logLikelihoodRatio P Q Xs hXs i
    have h_meas : Measurable (f n) := by
      change Measurable (fun ω ↦ (∑ i ∈ Finset.range n,
        logLikelihoodRatio P Q Xs i ω) / n)
      exact h_sum_meas.div_const _
    exact h_meas.aestronglyMeasurable
  have h_ae := stein_strong_law μ P Q Xs hXs hindep hident hMap hPQ hQpos
  have h_ae' : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f n ω) atTop (𝓝 (g ω)) := h_ae
  have h_inm : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_ae h_meas_f h_ae'
  rw [tendstoInMeasure_iff_dist] at h_inm
  have h_target := h_inm ε hε
  refine Tendsto.congr (fun n ↦ ?_) h_target
  apply congrArg μ
  ext ω
  show ε ≤ dist (f n ω) (g ω) ↔ ε ≤ |f n ω - g ω|
  rw [Real.dist_eq]

/-! ### Stein-typical set and achievability -/

/-- The Stein-typical set: blocks `x : Fin n → α` whose empirical log-likelihood ratio is within
`ε` of `(klDiv P Q).toReal`. -/
noncomputable def steinTypicalSet
    (P Q : Measure α) (n : ℕ) (ε : ℝ) : Set (Fin n → α) :=
  { x | |(∑ i : Fin n, llrPmf P Q (x i)) / n - (klDiv P Q).toReal| < ε }

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma mem_steinTypicalSet_iff
    (P Q : Measure α) (n : ℕ) (ε : ℝ) (x : Fin n → α) :
    x ∈ steinTypicalSet P Q n ε ↔
      |(∑ i : Fin n, llrPmf P Q (x i)) / n - (klDiv P Q).toReal| < ε := Iff.rfl

omit [DecidableEq α] [Nonempty α] in
theorem measurableSet_steinTypicalSet
    (P Q : Measure α) (n : ℕ) (ε : ℝ) :
    MeasurableSet (steinTypicalSet P Q n ε) :=
  (Set.toFinite (steinTypicalSet P Q n ε)).measurableSet

omit [DecidableEq α] in
set_option linter.unusedSectionVars false in
/-- Under `P`, the probability that a block lands in the Stein-typical set tends to `1`. -/
theorem steinTypicalSet_P_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ ↦ μ {ω | jointRV Xs n ω ∈ steinTypicalSet P Q n ε})
      atTop (𝓝 1) := by
  -- The "bad" event (from `stein_inProbability`).
  set bad : ℕ → Set Ω :=
    fun n ↦ {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n)
                       - (klDiv P Q).toReal|} with hbad_def
  -- Typical event = complement of `bad n`.
  have h_event_eq : ∀ n, {ω | jointRV Xs n ω ∈ steinTypicalSet P Q n ε} = (bad n)ᶜ := by
    intro n
    ext ω
    simp only [hbad_def, Set.mem_setOf_eq, Set.mem_compl_iff, mem_steinTypicalSet_iff,
      not_le, jointRV_apply]
    -- Convert the Fin-sum to a range-sum.
    have h_sum : (∑ i : Fin n, llrPmf P Q (Xs i ω))
        = ∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω :=
      Fin.sum_univ_eq_sum_range (fun i ↦ llrPmf P Q (Xs i ω)) n
    rw [h_sum]
  have h_bad : Tendsto (fun n ↦ μ (bad n)) atTop (𝓝 0) :=
    stein_inProbability μ P Q Xs hXs hindep hident hMap hPQ hQpos hε
  have h_meas_bad : ∀ n, MeasurableSet (bad n) := by
    intro n
    have h_sum_meas : Measurable
        (fun ω ↦ ∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) :=
      Finset.measurable_sum _ fun i _ ↦ measurable_logLikelihoodRatio P Q Xs hXs i
    have h_div : Measurable
        (fun ω ↦ (∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n) :=
      h_sum_meas.div_const _
    have h_diff : Measurable
        (fun ω ↦ (∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n
                    - (klDiv P Q).toReal) :=
      h_div.sub_const _
    have h_abs : Measurable
        (fun ω ↦ |((∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n
                    - (klDiv P Q).toReal)|) :=
      _root_.continuous_abs.measurable.comp h_diff
    exact measurableSet_le measurable_const h_abs
  have h_compl : Tendsto (fun n ↦ μ (bad n)ᶜ) atTop (𝓝 1) := by
    have h_id : ∀ n, μ ((bad n)ᶜ) = 1 - μ (bad n) := by
      intro n
      rw [measure_compl (h_meas_bad n) (measure_ne_top μ _), measure_univ]
    refine Tendsto.congr (fun n ↦ (h_id n).symm) ?_
    have h_cont : Continuous (fun x : ℝ≥0∞ ↦ (1 : ℝ≥0∞) - x) :=
      ENNReal.continuous_sub_left (by simp)
    have h_step : Tendsto (fun n ↦ (1 : ℝ≥0∞) - μ (bad n)) atTop
        (𝓝 ((1 : ℝ≥0∞) - 0)) := h_cont.tendsto _ |>.comp h_bad
    simpa using h_step
  refine Tendsto.congr (fun n ↦ ?_) h_compl
  rw [h_event_eq n]

omit [DecidableEq α] [Nonempty α] in
/-- The `Qⁿ`-mass of the Stein-typical set is at most `exp(-n · ((klDiv P Q).toReal − ε))`. -/
theorem steinTypicalSet_Q_prob_le
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hQpos : ∀ x : α, 0 < Q.real {x})
    (n : ℕ) (ε : ℝ) :
    ((Measure.pi (fun _ : Fin n ↦ Q)) (steinTypicalSet P Q n ε)).toReal
      ≤ Real.exp (-((n : ℝ) * ((klDiv P Q).toReal - ε))) := by
  classical
  -- Notation: `K = (klDiv P Q).toReal`, `T = T_ε^n` as a Finset.
  set K : ℝ := (klDiv P Q).toReal with hK_def
  set T : Finset (Fin n → α) := (steinTypicalSet P Q n ε).toFinite.toFinset with hT_def
  have hT_coe : (T : Set (Fin n → α)) = steinTypicalSet P Q n ε := by
    simp [hT_def]
  -- Pointwise marginal masses.
  set p : α → ℝ := fun x ↦ P.real {x} with hp_def
  set q : α → ℝ := fun x ↦ Q.real {x} with hq_def
  have hp_pos : ∀ x, 0 < p x := hPpos
  have hq_pos : ∀ x, 0 < q x := hQpos
  -- Sum-of-marginals = 1.
  have hsum_p : (∑ x : α, p x) = 1 := by
    have h1 : (∑ x : α, p x) = P.real (Finset.univ : Finset α) := by
      simp [hp_def, sum_measureReal_singleton]
    rw [h1]
    show P.real ↑(Finset.univ : Finset α) = 1
    rw [Finset.coe_univ]
    exact probReal_univ
  -- (Measure.pi Q).real {x} = ∏ i, Q.real {x i}.
  have h_pi_singleton_Q : ∀ x : Fin n → α,
      ((Measure.pi (fun _ : Fin n ↦ Q)).real {x}) = ∏ i : Fin n, q (x i) := by
    intro x
    show ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal = ∏ i : Fin n, q (x i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  have h_pi_singleton_P : ∀ x : Fin n → α,
      ((Measure.pi (fun _ : Fin n ↦ P)).real {x}) = ∏ i : Fin n, p (x i) := by
    intro x
    show ((Measure.pi (fun _ : Fin n ↦ P)) {x}).toReal = ∏ i : Fin n, p (x i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  -- Step 1: rewrite the Pi-measure of `T` (set form) as the sum over `T` (Finset form).
  have h_pi_real_eq_sum :
      ((Measure.pi (fun _ : Fin n ↦ Q)) (steinTypicalSet P Q n ε)).toReal
        = ∑ x ∈ T, ∏ i : Fin n, q (x i) := by
    have h_step : ((Measure.pi (fun _ : Fin n ↦ Q)) (T : Set (Fin n → α))).toReal
        = ∑ x ∈ T, ((Measure.pi (fun _ : Fin n ↦ Q)).real {x}) := by
      rw [← MeasureTheory.measureReal_def]
      rw [← MeasureTheory.sum_measureReal_singleton
        (μ := Measure.pi (fun _ : Fin n ↦ Q)) T]
    rw [← hT_coe]
    rw [h_step]
    refine Finset.sum_congr rfl fun x _ ↦ h_pi_singleton_Q x
  rw [h_pi_real_eq_sum]
  -- Step 2: per-`x ∈ T`, `∏ i, q (x i) ≤ (∏ i, p (x i)) · exp(-(n · (K - ε)))`.
  have h_per_point : ∀ x ∈ T,
      ∏ i : Fin n, q (x i) ≤ (∏ i : Fin n, p (x i)) * Real.exp (-((n : ℝ) * (K - ε))) := by
    intro x hx
    have hxT : x ∈ steinTypicalSet P Q n ε := (Set.Finite.mem_toFinset _).mp hx
    rw [mem_steinTypicalSet_iff] at hxT
    -- From `|S/n - K| < ε` extract `S/n > K - ε`, where `S = ∑ i, llrPmf P Q (x i)`.
    have hlower : K - ε < (∑ i : Fin n, llrPmf P Q (x i)) / n := by
      have h_abs := abs_lt.mp hxT
      linarith [h_abs.1]
    -- Multiply by `n`. Cases: `n = 0` and `n > 0`.
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      -- `Fin 0`: empty product = 1. Goal: `1 ≤ 1 · exp(-(0 · (K - ε)))` = `1 ≤ 1`.
      simp
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hsum_lower : (n : ℝ) * (K - ε) < ∑ i : Fin n, llrPmf P Q (x i) := by
      have := (lt_div_iff₀ hn_pos_R).mp hlower
      linarith
    -- `exp` monotone: `exp(-(∑ llrPmf)) < exp(-(n(K-ε)))`.
    have hneg : -(∑ i : Fin n, llrPmf P Q (x i)) < -((n : ℝ) * (K - ε)) := by linarith
    have hexp_lt : Real.exp (-(∑ i : Fin n, llrPmf P Q (x i)))
        < Real.exp (-((n : ℝ) * (K - ε))) :=
      Real.exp_lt_exp.mpr hneg
    -- Express `exp(-(∑ llrPmf))` as a product of `q(x i)/p(x i)`.
    -- llrPmf P Q (x i) = log p (x i) - log q (x i)
    -- ⇒ -llrPmf = log q - log p = log (q/p) ⇒ exp(-llrPmf) = q/p.
    have h_exp_neg_llr : ∀ i : Fin n,
        Real.exp (-(llrPmf P Q (x i))) = q (x i) / p (x i) := by
      intro i
      have h_neg_llr : -(llrPmf P Q (x i))
          = Real.log (q (x i)) - Real.log (p (x i)) := by
        unfold llrPmf
        ring
      rw [h_neg_llr]
      rw [← Real.log_div (hq_pos (x i)).ne' (hp_pos (x i)).ne']
      exact Real.exp_log (div_pos (hq_pos (x i)) (hp_pos (x i)))
    have h_prod_ratio :
        Real.exp (-(∑ i : Fin n, llrPmf P Q (x i)))
          = ∏ i : Fin n, q (x i) / p (x i) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ ↦ h_exp_neg_llr i
    rw [h_prod_ratio] at hexp_lt
    have hexp_lt_le : ∏ i : Fin n, q (x i) / p (x i)
        ≤ Real.exp (-((n : ℝ) * (K - ε))) := hexp_lt.le
    -- Now multiply both sides by `∏ i, p (x i)` (positive).
    have hprod_p_pos : 0 < ∏ i : Fin n, p (x i) :=
      Finset.prod_pos (fun i _ ↦ hp_pos (x i))
    have h_eq_split : ∏ i : Fin n, q (x i)
        = (∏ i : Fin n, q (x i) / p (x i)) * ∏ i : Fin n, p (x i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [div_mul_cancel₀ _ (hp_pos (x i)).ne']
    rw [h_eq_split]
    have hp_nn : (0 : ℝ) ≤ ∏ i : Fin n, p (x i) := hprod_p_pos.le
    -- `(q/p) ≤ exp(...)` ⇒ `(q/p) * p ≤ exp(...) * p`.
    have h_mul_le : (∏ i : Fin n, q (x i) / p (x i)) * (∏ i : Fin n, p (x i))
        ≤ Real.exp (-((n : ℝ) * (K - ε))) * (∏ i : Fin n, p (x i)) :=
      mul_le_mul_of_nonneg_right hexp_lt_le hp_nn
    -- Reorder factors to match goal `(∏ p) * exp(...)`.
    rw [mul_comm (Real.exp _) _] at h_mul_le
    exact h_mul_le
  -- Step 3: sum the per-point bounds, factor out `exp(-n(K-ε))`, bound `∑ x ∈ T, ∏ p ≤ 1`.
  have h_sum_le : (∑ x ∈ T, ∏ i : Fin n, q (x i))
      ≤ Real.exp (-((n : ℝ) * (K - ε))) := by
    calc (∑ x ∈ T, ∏ i : Fin n, q (x i))
        ≤ ∑ x ∈ T, (∏ i : Fin n, p (x i)) * Real.exp (-((n : ℝ) * (K - ε))) :=
            Finset.sum_le_sum h_per_point
      _ = (∑ x ∈ T, ∏ i : Fin n, p (x i)) * Real.exp (-((n : ℝ) * (K - ε))) := by
            rw [← Finset.sum_mul]
      _ ≤ 1 * Real.exp (-((n : ℝ) * (K - ε))) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            -- `∑ x ∈ T, ∏ p ≤ ∑ x : Fin n → α, ∏ p = 1`.
            have h_total : (∑ x : Fin n → α, ∏ i : Fin n, p (x i)) = 1 := by
              classical
              rw [← Fintype.piFinset_univ, Finset.sum_prod_piFinset]
              simp [hsum_p]
            have h_nonneg : ∀ x : Fin n → α, 0 ≤ ∏ i : Fin n, p (x i) := by
              intro x
              exact Finset.prod_nonneg (fun i _ ↦ (hp_pos (x i)).le)
            calc (∑ x ∈ T, ∏ i : Fin n, p (x i))
                ≤ ∑ x : Fin n → α, ∏ i : Fin n, p (x i) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro x _; exact Finset.mem_univ x
                  · intro x _ _; exact h_nonneg x
              _ = 1 := h_total
      _ = Real.exp (-((n : ℝ) * (K - ε))) := one_mul _
  exact h_sum_le

omit [DecidableEq α] in
/-- **Stein's lemma** (achievability): eventually there exist `ε`-level tests whose type-II
error decays as `exp(-n · ((klDiv P Q).toReal − δ))`. The statement is in product-measure form;
the translation from the random-variable form is supplied by the hypothesis
`hMapJoint : μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P)`. -/
@[entry_point]
theorem stein_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n ↦ P))
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε δ : ℝ} (hε : 0 < ε) (_hε1 : ε < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ∃ s : Set (Fin n → α), MeasurableSet s ∧
        ((Measure.pi (fun _ : Fin n ↦ P)) sᶜ).toReal ≤ ε ∧
        -((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n ↦ Q)) s).toReal
          ≥ (klDiv P Q).toReal - δ := by
  classical
  -- Use the Stein-typical set with slack `δ` as the rejection region.
  -- (1) `μ{ω | jointRV Xs n ω ∈ steinTypicalSet} → 1` (B.2),
  --     translated to `P^n(steinTypicalSet) → 1` via `hMapJoint`.
  -- (2) `Q^n(steinTypicalSet) ≤ exp(-n(klDiv - δ))` — from B.3.
  set K : ℝ := (klDiv P Q).toReal with hK_def
  -- Translate via `hMapJoint`: `μ{ω | jointRV ∈ T} = P^n(T)` for measurable T.
  have h_translate : ∀ (n : ℕ) (T : Set (Fin n → α)), MeasurableSet T →
      μ {ω | jointRV Xs n ω ∈ T} = (Measure.pi (fun _ : Fin n ↦ P)) T := by
    intro n T hT
    have hjoint_meas : Measurable (jointRV Xs n) := measurable_jointRV Xs hXs n
    have h_preimg : {ω | jointRV Xs n ω ∈ T} = jointRV Xs n ⁻¹' T := rfl
    rw [h_preimg, ← Measure.map_apply hjoint_meas hT, hMapJoint n]
  -- The P-typicality theorem (μ-form).
  have h_P_mu_to_one := steinTypicalSet_P_prob_tendsto_one μ P Q Xs hXs hindep hident hMap
    hPQ hQpos (ε := δ) hδ
  -- Translate to pi form (still ENNReal).
  have h_P_pi_to_one : Tendsto
      (fun n : ℕ ↦ (Measure.pi (fun _ : Fin n ↦ P)) (steinTypicalSet P Q n δ))
      atTop (𝓝 1) := by
    refine Tendsto.congr (fun n ↦ ?_) h_P_mu_to_one
    exact h_translate n _ (measurableSet_steinTypicalSet P Q n δ)
  -- Eventually `P^n(steinTypicalSet) > 0` (since it tends to 1).
  -- This will give us `steinTypicalSet ≠ ∅` and hence `Q^n(steinTypicalSet) > 0`.
  have h_P_eventually_pos : ∀ᶠ n : ℕ in atTop,
      0 < (Measure.pi (fun _ : Fin n ↦ P)) (steinTypicalSet P Q n δ) := by
    have : ∀ᶠ x : ℝ≥0∞ in 𝓝 (1 : ℝ≥0∞), (0 : ℝ≥0∞) < x := by
      apply eventually_gt_nhds
      simp
    exact h_P_pi_to_one this
  -- Pass `P^n(T) → 1` (in ENNReal) to `(P^n(T)).toReal → 1` (in ℝ).
  have h_P_pi_to_one_R : Tendsto
      (fun n : ℕ ↦ ((Measure.pi (fun _ : Fin n ↦ P))
        (steinTypicalSet P Q n δ)).toReal)
      atTop (𝓝 1) := by
    have h_cont : ContinuousAt ENNReal.toReal 1 :=
      ENNReal.continuousAt_toReal (by simp)
    have := h_cont.tendsto.comp h_P_pi_to_one
    simpa using this
  -- Hence `P^n(steinTypicalSetᶜ).toReal = 1 - P^n(steinTypicalSet).toReal → 0`.
  have h_P_compl_R_to_zero : Tendsto
      (fun n : ℕ ↦ ((Measure.pi (fun _ : Fin n ↦ P))
        (steinTypicalSet P Q n δ)ᶜ).toReal) atTop (𝓝 0) := by
    have h_id : ∀ n : ℕ,
        ((Measure.pi (fun _ : Fin n ↦ P)) (steinTypicalSet P Q n δ)ᶜ).toReal
          = 1 - ((Measure.pi (fun _ : Fin n ↦ P))
              (steinTypicalSet P Q n δ)).toReal := by
      intro n
      have h_meas := measurableSet_steinTypicalSet P Q n δ
      show (Measure.pi (fun _ : Fin n ↦ P)).real (steinTypicalSet P Q n δ)ᶜ
        = 1 - (Measure.pi (fun _ : Fin n ↦ P)).real (steinTypicalSet P Q n δ)
      rw [measureReal_compl h_meas, probReal_univ]
    refine Tendsto.congr (fun n ↦ (h_id n).symm) ?_
    have h_sub : Tendsto (fun n : ℕ ↦
        (1 : ℝ) - ((Measure.pi (fun _ : Fin n ↦ P))
            (steinTypicalSet P Q n δ)).toReal) atTop (𝓝 (1 - 1)) := by
      exact (tendsto_const_nhds).sub h_P_pi_to_one_R
    simpa using h_sub
  -- Step 2: `P^n(steinTypicalSetᶜ).toReal ≤ ε` eventually.
  have h_alpha_le : ∀ᶠ n : ℕ in atTop,
      ((Measure.pi (fun _ : Fin n ↦ P))
        (steinTypicalSet P Q n δ)ᶜ).toReal ≤ ε := by
    have : ∀ᶠ x : ℝ in 𝓝 0, x ≤ ε := by
      apply eventually_le_nhds
      exact hε
    exact h_P_compl_R_to_zero this
  -- Step 3: Combine with `h_P_eventually_pos`. Both events eventually hold.
  filter_upwards [h_P_eventually_pos, h_alpha_le, eventually_gt_atTop 0]
    with n h_pos h_alpha hn_pos
  -- We choose s = steinTypicalSet P Q n δ.
  refine ⟨steinTypicalSet P Q n δ, measurableSet_steinTypicalSet P Q n δ, h_alpha, ?_⟩
  -- Step 4: lower bound on `-(1/n) * log Q^n(steinTypicalSet)`.
  -- From B.3: `Q^n(s).toReal ≤ exp(-(n · (K - δ)))`. So `log Q^n(s).toReal ≤ -(n(K-δ))`,
  -- so `-(1/n) log Q^n(s).toReal ≥ K - δ`. Need `Q^n(s) > 0` for log to be meaningful.
  have h_Q_le := steinTypicalSet_Q_prob_le P Q hPpos hQpos n δ
  -- `Q^n(steinTypicalSet) > 0`: since `P^n(s) > 0` and `s` non-empty (singletons in `s`),
  -- and every singleton has positive Q^n mass (because hQpos).
  have h_Q_pos : 0 < ((Measure.pi (fun _ : Fin n ↦ Q))
      (steinTypicalSet P Q n δ)).toReal := by
    -- Pick a witness `x ∈ steinTypicalSet`. From `h_pos`, `P^n(s) > 0`, so `s ≠ ∅`.
    have h_s_nonempty : (steinTypicalSet P Q n δ).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h_empty
      rw [h_empty] at h_pos
      simp at h_pos
    obtain ⟨x, hx⟩ := h_s_nonempty
    -- `Q^n({x}) > 0` because all singletons of α have positive Q-mass (hQpos).
    have h_Q_x_pos : 0 < ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal := by
      rw [show ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal
        = ∏ i : Fin n, Q.real {x i} from by
          rw [Measure.pi_singleton, ENNReal.toReal_prod]; rfl]
      exact Finset.prod_pos (fun i _ ↦ hQpos (x i))
    -- And `Q^n({x}) ≤ Q^n(steinTypicalSet)` by monotonicity.
    have h_subset : ({x} : Set (Fin n → α)) ⊆ steinTypicalSet P Q n δ := by
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      rw [hy]; exact hx
    have h_meas_sub : ((Measure.pi (fun _ : Fin n ↦ Q)) {x}).toReal
        ≤ ((Measure.pi (fun _ : Fin n ↦ Q)) (steinTypicalSet P Q n δ)).toReal :=
      MeasureTheory.measureReal_mono h_subset
    linarith
  -- Now apply log monotonicity.
  -- From `Q^n(s).toReal ≤ exp(-(n(K-δ)))`, by `Real.log` monotonicity (and Q^n s > 0),
  -- `log Q^n(s).toReal ≤ -(n(K-δ))`.
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have h_log_le : Real.log ((Measure.pi (fun _ : Fin n ↦ Q))
      (steinTypicalSet P Q n δ)).toReal ≤ -((n : ℝ) * (K - δ)) := by
    calc Real.log ((Measure.pi (fun _ : Fin n ↦ Q))
            (steinTypicalSet P Q n δ)).toReal
        ≤ Real.log (Real.exp (-((n : ℝ) * (K - δ)))) :=
          Real.log_le_log h_Q_pos h_Q_le
      _ = -((n : ℝ) * (K - δ)) := Real.log_exp _
  -- Multiply by -(1/n) (negative ⇒ flips inequality).
  have h_inv_pos : 0 < (1 / n : ℝ) := one_div_pos.mpr hn_R_pos
  have h_neg_inv_neg : -(1 / n : ℝ) < 0 := by linarith
  -- `-(1/n) * log Q^n s ≥ -(1/n) * (-(n(K-δ))) = (K - δ)`.
  have h_step : -(1 / n : ℝ) * Real.log
      ((Measure.pi (fun _ : Fin n ↦ Q)) (steinTypicalSet P Q n δ)).toReal
      ≥ -(1 / n : ℝ) * (-((n : ℝ) * (K - δ))) := by
    apply mul_le_mul_of_nonpos_left h_log_le
    linarith
  -- Simplify `-(1/n) * (-(n(K-δ))) = K - δ`.
  have h_simp : -(1 / n : ℝ) * (-((n : ℝ) * (K - δ))) = K - δ := by
    field_simp
  rw [h_simp] at h_step
  exact h_step

/-! ### Tensorization of the KL divergence

The KL divergence between i.i.d. product measures factorizes as `n` times the single-sample KL
divergence: `klDiv (Π_{Fin n} P) (Π_{Fin n} Q) = n · klDiv P Q`. -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Base case of the KL tensorization: the product measures over `Fin 0 → α` agree, so their KL
divergence is `0`. -/
theorem klDiv_pi_zero
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    klDiv (Measure.pi (fun _ : Fin 0 ↦ P)) (Measure.pi (fun _ : Fin 0 ↦ Q)) = 0 := by
  -- Both Pi measures equal `Measure.dirac isEmptyElim` via `pi_of_empty`.
  rw [Measure.pi_of_empty (fun _ : Fin 0 ↦ P), Measure.pi_of_empty (fun _ : Fin 0 ↦ Q)]
  exact klDiv_self _

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Step case of the KL tensorization:
`klDiv (Π_{n+1} P) (Π_{n+1} Q) = klDiv P Q + klDiv (Π_n P) (Π_n Q)`. -/
theorem klDiv_pi_succ
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n : ℕ) :
    klDiv (Measure.pi (fun _ : Fin (n + 1) ↦ P)) (Measure.pi (fun _ : Fin (n + 1) ↦ Q))
      = klDiv P Q + klDiv (Measure.pi (fun _ : Fin n ↦ P))
                          (Measure.pi (fun _ : Fin n ↦ Q)) := by
  -- (1) reshape via piFinSuccAbove with i = 0:
  --     Measure.pi (Fin (n+1) → P) = (P).prod (Measure.pi (Fin n → P)) (after map)
  set e : ((i : Fin (n + 1)) → (fun _ ↦ α) i) ≃ᵐ
            α × ((j : Fin n) → (fun _ ↦ α) ((0 : Fin (n + 1)).succAbove j)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ α) 0 with he_def
  have hP_pres : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) ↦ P))
      (P.prod (Measure.pi (fun j : Fin n ↦ P))) := by
    have := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ P) (0 : Fin (n + 1))
    -- `(0 : Fin (n+1)).succAbove j` for `j : Fin n` is `j.succ`, so the resulting
    -- Pi measure is over the constant `P` family: this is defeq.
    exact this
  have hQ_pres : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) ↦ Q))
      (Q.prod (Measure.pi (fun j : Fin n ↦ Q))) := by
    have := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ Q) (0 : Fin (n + 1))
    exact this
  have hP_map : (Measure.pi (fun _ : Fin (n + 1) ↦ P)).map e
      = P.prod (Measure.pi (fun j : Fin n ↦ P)) := hP_pres.map_eq
  have hQ_map : (Measure.pi (fun _ : Fin (n + 1) ↦ Q)).map e
      = Q.prod (Measure.pi (fun j : Fin n ↦ Q)) := hQ_pres.map_eq
  -- (2) `klDiv (Pi (n+1) P) (Pi (n+1) Q) = klDiv (P.prod Pi^n P) (Q.prod Pi^n Q)`.
  have h_reshape :
      klDiv (Measure.pi (fun _ : Fin (n + 1) ↦ P))
            (Measure.pi (fun _ : Fin (n + 1) ↦ Q))
        = klDiv (P.prod (Measure.pi (fun j : Fin n ↦ P)))
                (Q.prod (Measure.pi (fun j : Fin n ↦ Q))) := by
    rw [← hP_map, ← hQ_map, klDiv_map_measurableEquiv e]
  rw [h_reshape]
  -- (3) Convert `prod` to `compProd const`.
  have hP_compProd : P.prod (Measure.pi (fun j : Fin n ↦ P))
      = P ⊗ₘ Kernel.const α (Measure.pi (fun j : Fin n ↦ P)) :=
    (Measure.compProd_const).symm
  have hQ_compProd : Q.prod (Measure.pi (fun j : Fin n ↦ Q))
      = Q ⊗ₘ Kernel.const α (Measure.pi (fun j : Fin n ↦ Q)) :=
    (Measure.compProd_const).symm
  rw [hP_compProd, hQ_compProd]
  -- (4) Apply `klDiv_compProd_eq_add`:
  --     klDiv (P ⊗ const Pi^n P) (Q ⊗ const Pi^n Q)
  --       = klDiv P Q + klDiv (P ⊗ const Pi^n P) (P ⊗ const Pi^n Q)
  rw [klDiv_compProd_eq_add P Q (Kernel.const α (Measure.pi (fun j : Fin n ↦ P)))
        (Kernel.const α (Measure.pi (fun j : Fin n ↦ Q)))]
  -- (5) The right summand is `klDiv (P ⊗ const Pi^n P) (P ⊗ const Pi^n Q)`.
  -- Convert both sides back to `prod` form using `compProd_const`, then apply
  -- `klDiv_prod_const_left` to cancel the common left factor `P`.
  congr 1
  rw [Measure.compProd_const, Measure.compProd_const]
  exact klDiv_prod_const_left P (Measure.pi (fun j : Fin n ↦ P))
    (Measure.pi (fun j : Fin n ↦ Q))

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- KL tensorization: `klDiv (Π_{Fin n} P) (Π_{Fin n} Q) = n · klDiv P Q`. -/
theorem klDiv_pi_eq_n_smul
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n : ℕ) :
    klDiv (Measure.pi (fun _ : Fin n ↦ P)) (Measure.pi (fun _ : Fin n ↦ Q))
      = (n : ℝ≥0∞) * klDiv P Q := by
  induction n with
  | zero => rw [klDiv_pi_zero P Q]; simp
  | succ k ih =>
    rw [klDiv_pi_succ P Q k, ih]
    push_cast
    ring

end InformationTheory.Shannon
