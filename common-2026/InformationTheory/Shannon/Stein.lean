import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AEP.Basic
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.MutualInfo
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Stein の補題 — Phase A〜B (achievability) スコープ

仮説検定の最適 type-II error が KL の指数で減衰することを示す Stein の補題
(Cover-Thomas Theorem 11.8.3) のうち、**lower bound (achievability)** までを
スコープとする。Phase C (converse, upper bound) と Phase D (統合形 `Tendsto`)
は本ファイルでは未着手。

## 構成

* **Phase A** — log-likelihood ratio plumbing:
  * `llrPmf P Q : α → ℝ`、`logLikelihoodRatio P Q Xs i : Ω → ℝ`
  * 期待値 LR = KL: `integral_logLikelihoodRatio_under_P = (klDiv P Q).toReal`
  * Stein 強法則 `stein_strong_law` (AEP `aep_ae` の 2 分布化)
  * 確率収束 `stein_inProbability` (AEP `aep_inProbability` の 2 分布化)
* **Phase B** — Stein lower bound:
  * Stein-typical set `steinTypicalSet P Q n ε`
  * P-side typicality → 1 (`steinTypicalSet_P_prob_tendsto_one`)
  * Q-side mass bound (`steinTypicalSet_Q_prob_le`)
  * `stein_achievability` — typicality test の存在 (撤退ライン到達)

## 設計メモ

* AEP plumbing の **2 分布化** で 70〜80% の補題を再利用。新規構築は 2〜3 本のみ
* Phase A.7 の `klDiv_pi_eq_n_smul` は Phase C で必要だが Phase B では不要、
  本ファイルでは未実装 (Phase C 着手時に追加)
* `α : Fintype` + `[MeasurableSingletonClass α]` + `hQpos : ∀ x, 0 < Q.real {x}`
  のもとで全て point-wise に展開、Pi 値 RN 微分の汎用 plumbing を回避
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Phase A — log-likelihood ratio plumbing -/

/-- Alphabet-side log-likelihood ratio `log P(x) − log Q(x)`. AEP `pmfLog` の 2 分布化。
On the support of `P` (where `P{x} > 0`) and assuming `Q{x} > 0` for all `x`, this
equals `Real.log ((P.rnDeriv Q x).toReal)`. -/
noncomputable def llrPmf (P Q : Measure α) : α → ℝ :=
  fun x => Real.log (P.real {x}) - Real.log (Q.real {x})

omit [DecidableEq α] [Nonempty α] in
lemma measurable_llrPmf (P Q : Measure α) : Measurable (llrPmf P Q) :=
  measurable_of_finite _

/-- Per-symbol log-likelihood ratio: `llrPmf P Q (Xs i ω)`. -/
noncomputable def logLikelihoodRatio
    (P Q : Measure α) (Xs : ℕ → Ω → α) (i : ℕ) : Ω → ℝ :=
  fun ω => llrPmf P Q (Xs i ω)

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
/-- Integrability of the per-symbol LR on a finite alphabet. -/
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
/-- The expected log-likelihood ratio under `P` equals `(klDiv P Q).toReal`.
This is the 2-distribution analogue of AEP `integral_logLikelihood_zero`.

**Hypotheses**: `μ.map (Xs 0) = P`, `P ≪ Q`, and `0 < Q.real {x}` for every `x`
(the latter gives `(P.rnDeriv Q x).toReal = P.real {x} / Q.real {x}` pointwise).
-/
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
    exact ENNReal.sum_lt_top.mpr fun _ _ =>
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
  refine Finset.sum_congr rfl fun x _ => ?_
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
/-- Composition lift of `IdentDistrib` to `logLikelihoodRatio`. -/
lemma identDistrib_logLikelihoodRatio
    (μ : Measure Ω) (P Q : Measure α) (Xs : ℕ → Ω → α)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (i : ℕ) :
    IdentDistrib (logLikelihoodRatio P Q Xs i) (logLikelihoodRatio P Q Xs 0) μ μ := by
  simpa [logLikelihoodRatio_eq_comp] using (hident i).comp (measurable_llrPmf P Q)

omit [DecidableEq α] [Nonempty α] in
/-- Composition lift of pairwise `IndepFun` to `logLikelihoodRatio`. -/
lemma indepFun_logLikelihoodRatio
    (μ : Measure Ω) (P Q : Measure α) (Xs : ℕ → Ω → α)
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) :
    Pairwise fun i j =>
      logLikelihoodRatio P Q Xs i ⟂ᵢ[μ] logLikelihoodRatio P Q Xs j := by
  intro i j hij
  have h := hindep hij
  have hpf := measurable_llrPmf P Q
  simpa [logLikelihoodRatio_eq_comp] using h.comp hpf hpf

omit [DecidableEq α] [Nonempty α] in
/-- **Stein 強法則** (Cover-Thomas LR-side): the empirical mean of the per-symbol
log-likelihood ratio converges almost surely to `(klDiv P Q).toReal`. AEP `aep_ae`
の 2 分布化。 -/
@[entry_point]
theorem stein_strong_law
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n)
      atTop
      (𝓝 (klDiv P Q).toReal) := by
  have hint : Integrable (logLikelihoodRatio P Q Xs 0) μ :=
    integrable_logLikelihoodRatio μ P Q Xs hXs 0
  have hindLR : Pairwise fun i j =>
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
/-- **Stein convergence in probability**: the empirical mean of the LR converges
to `(klDiv P Q).toReal` in probability. -/
@[entry_point]
theorem stein_inProbability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | ε ≤ |((∑ i ∈ Finset.range n,
                                  logLikelihoodRatio P Q Xs i ω) / n)
                                - (klDiv P Q).toReal|})
      atTop
      (𝓝 0) := by
  set f : ℕ → Ω → ℝ :=
    fun n ω => (∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n with hf_def
  set g : Ω → ℝ := fun _ => (klDiv P Q).toReal with hg_def
  have h_meas_f : ∀ n, AEStronglyMeasurable (f n) μ := by
    intro n
    have h_sum_meas : Measurable
        (fun ω => ∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) :=
      Finset.measurable_sum _ fun i _ => measurable_logLikelihoodRatio P Q Xs hXs i
    have h_meas : Measurable (f n) := by
      change Measurable (fun ω => (∑ i ∈ Finset.range n,
        logLikelihoodRatio P Q Xs i ω) / n)
      exact h_sum_meas.div_const _
    exact h_meas.aestronglyMeasurable
  have h_ae := stein_strong_law μ P Q Xs hXs hindep hident hMap hPQ hQpos
  have h_ae' : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := h_ae
  have h_inm : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_ae h_meas_f h_ae'
  rw [tendstoInMeasure_iff_dist] at h_inm
  have h_target := h_inm ε hε
  refine Tendsto.congr (fun n => ?_) h_target
  apply congrArg μ
  ext ω
  show ε ≤ dist (f n ω) (g ω) ↔ ε ≤ |f n ω - g ω|
  rw [Real.dist_eq]

/-! ### Phase B — Stein-typical set and Stein lower bound (achievability) -/

/-- **Stein-typical set**: blocks `x : Fin n → α` whose empirical LR is within `ε`
of the true KL divergence. AEP `typicalSet` の 2 分布化。 -/
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
/-- **P-side typicality probability tends to 1**: `μ {ω | jointRV Xs n ω ∈ T} → 1`. -/
theorem steinTypicalSet_P_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ steinTypicalSet P Q n ε})
      atTop (𝓝 1) := by
  -- The "bad" event (from `stein_inProbability`).
  set bad : ℕ → Set Ω :=
    fun n => {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n)
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
      Fin.sum_univ_eq_sum_range (fun i => llrPmf P Q (Xs i ω)) n
    rw [h_sum]
  have h_bad : Tendsto (fun n => μ (bad n)) atTop (𝓝 0) :=
    stein_inProbability μ P Q Xs hXs hindep hident hMap hPQ hQpos hε
  have h_meas_bad : ∀ n, MeasurableSet (bad n) := by
    intro n
    have h_sum_meas : Measurable
        (fun ω => ∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) :=
      Finset.measurable_sum _ fun i _ => measurable_logLikelihoodRatio P Q Xs hXs i
    have h_div : Measurable
        (fun ω => (∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n) :=
      h_sum_meas.div_const _
    have h_diff : Measurable
        (fun ω => (∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n
                    - (klDiv P Q).toReal) :=
      h_div.sub_const _
    have h_abs : Measurable
        (fun ω => |((∑ i ∈ Finset.range n, logLikelihoodRatio P Q Xs i ω) / n
                    - (klDiv P Q).toReal)|) :=
      _root_.continuous_abs.measurable.comp h_diff
    exact measurableSet_le measurable_const h_abs
  have h_compl : Tendsto (fun n => μ (bad n)ᶜ) atTop (𝓝 1) := by
    have h_id : ∀ n, μ ((bad n)ᶜ) = 1 - μ (bad n) := by
      intro n
      rw [measure_compl (h_meas_bad n) (measure_ne_top μ _), measure_univ]
    refine Tendsto.congr (fun n => (h_id n).symm) ?_
    have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
      ENNReal.continuous_sub_left (by simp)
    have h_step : Tendsto (fun n => (1 : ℝ≥0∞) - μ (bad n)) atTop
        (𝓝 ((1 : ℝ≥0∞) - 0)) := h_cont.tendsto _ |>.comp h_bad
    simpa using h_step
  refine Tendsto.congr (fun n => ?_) h_compl
  rw [h_event_eq n]

omit [DecidableEq α] [Nonempty α] in
/-- **Q-side mass bound**: `Q^n(T_ε^n) ≤ exp(-n · (klDiv - ε))`.

The textbook Stein-typicality argument: on `T_ε^n`, the empirical LR is at least
`klDiv - ε`, so each block `x ∈ T_ε^n` has `Π_i Q.real{x_i} ≤ Π_i P.real{x_i} ·
exp(-(klDiv - ε))`. Summing over `T` and using `∑ Π_i P.real{x_i} = 1` gives the
bound. AEP `typicalSet_card_le` の Q 測度版。 -/
theorem steinTypicalSet_Q_prob_le
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hQpos : ∀ x : α, 0 < Q.real {x})
    (n : ℕ) (ε : ℝ) :
    ((Measure.pi (fun _ : Fin n => Q)) (steinTypicalSet P Q n ε)).toReal
      ≤ Real.exp (-((n : ℝ) * ((klDiv P Q).toReal - ε))) := by
  classical
  -- Notation: `K = (klDiv P Q).toReal`, `T = T_ε^n` as a Finset.
  set K : ℝ := (klDiv P Q).toReal with hK_def
  set T : Finset (Fin n → α) := (steinTypicalSet P Q n ε).toFinite.toFinset with hT_def
  have hT_coe : (T : Set (Fin n → α)) = steinTypicalSet P Q n ε := by
    simp [hT_def]
  -- Pointwise marginal masses.
  set p : α → ℝ := fun x => P.real {x} with hp_def
  set q : α → ℝ := fun x => Q.real {x} with hq_def
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
      ((Measure.pi (fun _ : Fin n => Q)).real {x}) = ∏ i : Fin n, q (x i) := by
    intro x
    show ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal = ∏ i : Fin n, q (x i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  have h_pi_singleton_P : ∀ x : Fin n → α,
      ((Measure.pi (fun _ : Fin n => P)).real {x}) = ∏ i : Fin n, p (x i) := by
    intro x
    show ((Measure.pi (fun _ : Fin n => P)) {x}).toReal = ∏ i : Fin n, p (x i)
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    rfl
  -- Step 1: rewrite the Pi-measure of `T` (set form) as the sum over `T` (Finset form).
  have h_pi_real_eq_sum :
      ((Measure.pi (fun _ : Fin n => Q)) (steinTypicalSet P Q n ε)).toReal
        = ∑ x ∈ T, ∏ i : Fin n, q (x i) := by
    have h_step : ((Measure.pi (fun _ : Fin n => Q)) (T : Set (Fin n → α))).toReal
        = ∑ x ∈ T, ((Measure.pi (fun _ : Fin n => Q)).real {x}) := by
      rw [← MeasureTheory.measureReal_def]
      rw [← MeasureTheory.sum_measureReal_singleton
        (μ := Measure.pi (fun _ : Fin n => Q)) T]
    rw [← hT_coe]
    rw [h_step]
    refine Finset.sum_congr rfl fun x _ => h_pi_singleton_Q x
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
      exact Finset.prod_congr rfl fun i _ => h_exp_neg_llr i
    rw [h_prod_ratio] at hexp_lt
    have hexp_lt_le : ∏ i : Fin n, q (x i) / p (x i)
        ≤ Real.exp (-((n : ℝ) * (K - ε))) := hexp_lt.le
    -- Now multiply both sides by `∏ i, p (x i)` (positive).
    have hprod_p_pos : 0 < ∏ i : Fin n, p (x i) :=
      Finset.prod_pos (fun i _ => hp_pos (x i))
    have h_eq_split : ∏ i : Fin n, q (x i)
        = (∏ i : Fin n, q (x i) / p (x i)) * ∏ i : Fin n, p (x i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
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
              exact Finset.prod_nonneg (fun i _ => (hp_pos (x i)).le)
            calc (∑ x ∈ T, ∏ i : Fin n, p (x i))
                ≤ ∑ x : Fin n → α, ∏ i : Fin n, p (x i) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro x _; exact Finset.mem_univ x
                  · intro x _ _; exact h_nonneg x
              _ = 1 := h_total
      _ = Real.exp (-((n : ℝ) * (K - ε))) := one_mul _
  exact h_sum_le

omit [DecidableEq α] in
/-- **Stein achievability (lower bound)**: there exists a sequence of α-level tests
whose type-II error decays as `exp(-n · (klDiv P Q - δ))`.

Statement is in pi-measure form (the lifting from RV-form requires
`iIndepFun` → `Measure.pi` translation, which is recorded as the hypothesis
`hMapJoint : μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P)`). -/
@[entry_point]
theorem stein_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P))
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε δ : ℝ} (hε : 0 < ε) (_hε1 : ε < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      ∃ s : Set (Fin n → α), MeasurableSet s ∧
        ((Measure.pi (fun _ : Fin n => P)) sᶜ).toReal ≤ ε ∧
        -((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal
          ≥ (klDiv P Q).toReal - δ := by
  classical
  -- Use the Stein-typical set with slack `δ` as the rejection region.
  -- (1) `μ{ω | jointRV Xs n ω ∈ steinTypicalSet} → 1` (B.2),
  --     translated to `P^n(steinTypicalSet) → 1` via `hMapJoint`.
  -- (2) `Q^n(steinTypicalSet) ≤ exp(-n(klDiv - δ))` — from B.3.
  set K : ℝ := (klDiv P Q).toReal with hK_def
  -- Translate via `hMapJoint`: `μ{ω | jointRV ∈ T} = P^n(T)` for measurable T.
  have h_translate : ∀ (n : ℕ) (T : Set (Fin n → α)), MeasurableSet T →
      μ {ω | jointRV Xs n ω ∈ T} = (Measure.pi (fun _ : Fin n => P)) T := by
    intro n T hT
    have hjoint_meas : Measurable (jointRV Xs n) := measurable_jointRV Xs hXs n
    have h_preimg : {ω | jointRV Xs n ω ∈ T} = jointRV Xs n ⁻¹' T := rfl
    rw [h_preimg, ← Measure.map_apply hjoint_meas hT, hMapJoint n]
  -- The P-typicality theorem (μ-form).
  have h_P_mu_to_one := steinTypicalSet_P_prob_tendsto_one μ P Q Xs hXs hindep hident hMap
    hPQ hQpos (ε := δ) hδ
  -- Translate to pi form (still ENNReal).
  have h_P_pi_to_one : Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P)) (steinTypicalSet P Q n δ))
      atTop (𝓝 1) := by
    refine Tendsto.congr (fun n => ?_) h_P_mu_to_one
    exact h_translate n _ (measurableSet_steinTypicalSet P Q n δ)
  -- Eventually `P^n(steinTypicalSet) > 0` (since it tends to 1).
  -- This will give us `steinTypicalSet ≠ ∅` and hence `Q^n(steinTypicalSet) > 0`.
  have h_P_eventually_pos : ∀ᶠ n : ℕ in atTop,
      0 < (Measure.pi (fun _ : Fin n => P)) (steinTypicalSet P Q n δ) := by
    have : ∀ᶠ x : ℝ≥0∞ in 𝓝 (1 : ℝ≥0∞), (0 : ℝ≥0∞) < x := by
      apply eventually_gt_nhds
      simp
    exact h_P_pi_to_one this
  -- Pass `P^n(T) → 1` (in ENNReal) to `(P^n(T)).toReal → 1` (in ℝ).
  have h_P_pi_to_one_R : Tendsto
      (fun n : ℕ => ((Measure.pi (fun _ : Fin n => P))
        (steinTypicalSet P Q n δ)).toReal)
      atTop (𝓝 1) := by
    have h_cont : ContinuousAt ENNReal.toReal 1 :=
      ENNReal.continuousAt_toReal (by simp)
    have := h_cont.tendsto.comp h_P_pi_to_one
    simpa using this
  -- Hence `P^n(steinTypicalSetᶜ).toReal = 1 - P^n(steinTypicalSet).toReal → 0`.
  have h_P_compl_R_to_zero : Tendsto
      (fun n : ℕ => ((Measure.pi (fun _ : Fin n => P))
        (steinTypicalSet P Q n δ)ᶜ).toReal) atTop (𝓝 0) := by
    have h_id : ∀ n : ℕ,
        ((Measure.pi (fun _ : Fin n => P)) (steinTypicalSet P Q n δ)ᶜ).toReal
          = 1 - ((Measure.pi (fun _ : Fin n => P))
              (steinTypicalSet P Q n δ)).toReal := by
      intro n
      have h_meas := measurableSet_steinTypicalSet P Q n δ
      show (Measure.pi (fun _ : Fin n => P)).real (steinTypicalSet P Q n δ)ᶜ
        = 1 - (Measure.pi (fun _ : Fin n => P)).real (steinTypicalSet P Q n δ)
      rw [measureReal_compl h_meas, probReal_univ]
    refine Tendsto.congr (fun n => (h_id n).symm) ?_
    have h_sub : Tendsto (fun n : ℕ =>
        (1 : ℝ) - ((Measure.pi (fun _ : Fin n => P))
            (steinTypicalSet P Q n δ)).toReal) atTop (𝓝 (1 - 1)) := by
      exact (tendsto_const_nhds).sub h_P_pi_to_one_R
    simpa using h_sub
  -- Step 2: `P^n(steinTypicalSetᶜ).toReal ≤ ε` eventually.
  have h_alpha_le : ∀ᶠ n : ℕ in atTop,
      ((Measure.pi (fun _ : Fin n => P))
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
  have h_Q_pos : 0 < ((Measure.pi (fun _ : Fin n => Q))
      (steinTypicalSet P Q n δ)).toReal := by
    -- Pick a witness `x ∈ steinTypicalSet`. From `h_pos`, `P^n(s) > 0`, so `s ≠ ∅`.
    have h_s_nonempty : (steinTypicalSet P Q n δ).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h_empty
      rw [h_empty] at h_pos
      simp at h_pos
    obtain ⟨x, hx⟩ := h_s_nonempty
    -- `Q^n({x}) > 0` because all singletons of α have positive Q-mass (hQpos).
    have h_Q_x_pos : 0 < ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal := by
      rw [show ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal
        = ∏ i : Fin n, Q.real {x i} from by
          rw [Measure.pi_singleton, ENNReal.toReal_prod]; rfl]
      exact Finset.prod_pos (fun i _ => hQpos (x i))
    -- And `Q^n({x}) ≤ Q^n(steinTypicalSet)` by monotonicity.
    have h_subset : ({x} : Set (Fin n → α)) ⊆ steinTypicalSet P Q n δ := by
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      rw [hy]; exact hx
    have h_meas_sub : ((Measure.pi (fun _ : Fin n => Q)) {x}).toReal
        ≤ ((Measure.pi (fun _ : Fin n => Q)) (steinTypicalSet P Q n δ)).toReal :=
      MeasureTheory.measureReal_mono h_subset
    linarith
  -- Now apply log monotonicity.
  -- From `Q^n(s).toReal ≤ exp(-(n(K-δ)))`, by `Real.log` monotonicity (and Q^n s > 0),
  -- `log Q^n(s).toReal ≤ -(n(K-δ))`.
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have h_log_le : Real.log ((Measure.pi (fun _ : Fin n => Q))
      (steinTypicalSet P Q n δ)).toReal ≤ -((n : ℝ) * (K - δ)) := by
    calc Real.log ((Measure.pi (fun _ : Fin n => Q))
            (steinTypicalSet P Q n δ)).toReal
        ≤ Real.log (Real.exp (-((n : ℝ) * (K - δ)))) :=
          Real.log_le_log h_Q_pos h_Q_le
      _ = -((n : ℝ) * (K - δ)) := Real.log_exp _
  -- Multiply by -(1/n) (negative ⇒ flips inequality).
  have h_inv_pos : 0 < (1 / n : ℝ) := one_div_pos.mpr hn_R_pos
  have h_neg_inv_neg : -(1 / n : ℝ) < 0 := by linarith
  -- `-(1/n) * log Q^n s ≥ -(1/n) * (-(n(K-δ))) = (K - δ)`.
  have h_step : -(1 / n : ℝ) * Real.log
      ((Measure.pi (fun _ : Fin n => Q)) (steinTypicalSet P Q n δ)).toReal
      ≥ -(1 / n : ℝ) * (-((n : ℝ) * (K - δ))) := by
    apply mul_le_mul_of_nonpos_left h_log_le
    linarith
  -- Simplify `-(1/n) * (-(n(K-δ))) = K - δ`.
  have h_simp : -(1 / n : ℝ) * (-((n : ℝ) * (K - δ))) = K - δ := by
    field_simp
  rw [h_simp] at h_step
  exact h_step

/-! ### Phase C — Pi 化 KL chain rule (`klDiv_pi_eq_n_smul`)

i.i.d. Pi 測度間の KL は片サンプルの KL の `n` 倍に分解する:
`klDiv (Π_{Fin n} P) (Π_{Fin n} Q) = n · klDiv P Q`.

Mathlib に直接補題は不在 (loogle 0 件、`docs/shannon/stein-converse-mathlib-inventory.md` 軸 1)。
`klDiv_compProd_eq_add` + `klDiv_compProd_left` + `MeasurableEquiv.piFinSuccAbove`
で induction で構築する。Stein converse の Phase B (Bernoulli reduction の DPI) で
右辺 `klDiv P^n Q^n = n · klDiv P Q` を扱うために必要。 -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Pi 化 KL chain rule の base case (`n = 0`): `Fin 0 → α` は empty 上の関数型、Pi 測度は
共に `dirac isEmptyElim` (`Measure.pi_of_empty`)、KL = 0。 -/
theorem klDiv_pi_zero
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    klDiv (Measure.pi (fun _ : Fin 0 => P)) (Measure.pi (fun _ : Fin 0 => Q)) = 0 := by
  -- Both Pi measures equal `Measure.dirac isEmptyElim` via `pi_of_empty`.
  rw [Measure.pi_of_empty (fun _ : Fin 0 => P), Measure.pi_of_empty (fun _ : Fin 0 => Q)]
  exact klDiv_self _

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Pi 化 KL chain rule の step case: `klDiv (Π_{n+1} P) (Π_{n+1} Q) = klDiv P Q + klDiv (Π_n P) (Π_n Q)`.

`measurePreserving_piFinSuccAbove` で `(Fin (n+1) → α) ≃ᵐ α × (Fin n → α)` の reshape、
`klDiv_map_measurableEquiv` で KL を保ち、`Measure.compProd_const` (`prod = compProd const`) で
compProd 形に乗せ、`klDiv_compProd_eq_add` + `klDiv_prod_const_left` で展開。 -/
theorem klDiv_pi_succ
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n : ℕ) :
    klDiv (Measure.pi (fun _ : Fin (n + 1) => P)) (Measure.pi (fun _ : Fin (n + 1) => Q))
      = klDiv P Q + klDiv (Measure.pi (fun _ : Fin n => P))
                          (Measure.pi (fun _ : Fin n => Q)) := by
  -- (1) reshape via piFinSuccAbove with i = 0:
  --     Measure.pi (Fin (n+1) → P) = (P).prod (Measure.pi (Fin n → P)) (after map)
  set e : ((i : Fin (n + 1)) → (fun _ => α) i) ≃ᵐ
            α × ((j : Fin n) → (fun _ => α) ((0 : Fin (n + 1)).succAbove j)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0 with he_def
  have hP_pres : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => P))
      (P.prod (Measure.pi (fun j : Fin n => P))) := by
    have := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) (0 : Fin (n + 1))
    -- `(0 : Fin (n+1)).succAbove j` for `j : Fin n` is `j.succ`, so the resulting
    -- Pi measure is over the constant `P` family: this is defeq.
    exact this
  have hQ_pres : MeasurePreserving e
      (Measure.pi (fun _ : Fin (n + 1) => Q))
      (Q.prod (Measure.pi (fun j : Fin n => Q))) := by
    have := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Q) (0 : Fin (n + 1))
    exact this
  have hP_map : (Measure.pi (fun _ : Fin (n + 1) => P)).map e
      = P.prod (Measure.pi (fun j : Fin n => P)) := hP_pres.map_eq
  have hQ_map : (Measure.pi (fun _ : Fin (n + 1) => Q)).map e
      = Q.prod (Measure.pi (fun j : Fin n => Q)) := hQ_pres.map_eq
  -- (2) `klDiv (Pi (n+1) P) (Pi (n+1) Q) = klDiv (P.prod Pi^n P) (Q.prod Pi^n Q)`.
  have h_reshape :
      klDiv (Measure.pi (fun _ : Fin (n + 1) => P))
            (Measure.pi (fun _ : Fin (n + 1) => Q))
        = klDiv (P.prod (Measure.pi (fun j : Fin n => P)))
                (Q.prod (Measure.pi (fun j : Fin n => Q))) := by
    rw [← hP_map, ← hQ_map, klDiv_map_measurableEquiv e]
  rw [h_reshape]
  -- (3) Convert `prod` to `compProd const`.
  have hP_compProd : P.prod (Measure.pi (fun j : Fin n => P))
      = P ⊗ₘ Kernel.const α (Measure.pi (fun j : Fin n => P)) :=
    (Measure.compProd_const).symm
  have hQ_compProd : Q.prod (Measure.pi (fun j : Fin n => Q))
      = Q ⊗ₘ Kernel.const α (Measure.pi (fun j : Fin n => Q)) :=
    (Measure.compProd_const).symm
  rw [hP_compProd, hQ_compProd]
  -- (4) Apply `klDiv_compProd_eq_add`:
  --     klDiv (P ⊗ const Pi^n P) (Q ⊗ const Pi^n Q)
  --       = klDiv P Q + klDiv (P ⊗ const Pi^n P) (P ⊗ const Pi^n Q)
  rw [klDiv_compProd_eq_add P Q (Kernel.const α (Measure.pi (fun j : Fin n => P)))
        (Kernel.const α (Measure.pi (fun j : Fin n => Q)))]
  -- (5) The right summand is `klDiv (P ⊗ const Pi^n P) (P ⊗ const Pi^n Q)`.
  -- Convert both sides back to `prod` form using `compProd_const`, then apply
  -- `klDiv_prod_const_left` to cancel the common left factor `P`.
  congr 1
  rw [Measure.compProd_const, Measure.compProd_const]
  exact klDiv_prod_const_left P (Measure.pi (fun j : Fin n => P))
    (Measure.pi (fun j : Fin n => Q))

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Pi 化 KL chain rule**: `klDiv (Π_{Fin n} P) (Π_{Fin n} Q) = n · klDiv P Q`. -/
theorem klDiv_pi_eq_n_smul
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (n : ℕ) :
    klDiv (Measure.pi (fun _ : Fin n => P)) (Measure.pi (fun _ : Fin n => Q))
      = (n : ℝ≥0∞) * klDiv P Q := by
  induction n with
  | zero => rw [klDiv_pi_zero P Q]; simp
  | succ k ih =>
    rw [klDiv_pi_succ P Q k, ih]
    push_cast
    ring

/-! ### Phase D — Stein converse (Phase B of the converse plan)

任意の α-level 検定 `s : Set (Fin n → α)` の type-II error は
`exp(-n · klDiv P Q - δ_n)` 以上 (= log を取って `-(1/n) log Q^n s ≤ klDiv P Q + δ_n`)。
証明戦略: Bernoulli reduction + DPI + Bool KL の sum 形展開 + α-level 補正 (`docs/shannon/
stein-converse-plan.md` Phase B)。 -/

omit [DecidableEq α] [Nonempty α] in
/-- Bool 上の確率測度の KL 値 (`toReal`) を 2 点 sum 形に展開する。
`klDiv (μ : Measure Bool) (ν : Measure Bool)` で `μ ≪ ν` のとき、
`(klDiv μ ν).toReal = (μ {true}).toReal * log((μ {true}).toReal / (ν {true}).toReal)
                    + (μ {false}).toReal * log((μ {false}).toReal / (ν {false}).toReal)`.

`Bridge.lean` の private `klDiv_discrete_toReal_eq_sum` の Bool 版 (Fintype.sum_bool で展開). -/
private lemma klDiv_bool_toReal_eq_sum
    (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal
      = (μ.real {true}) * (Real.log (μ.real {true}) - Real.log (ν.real {true}))
      + (μ.real {false}) * (Real.log (μ.real {false}) - Real.log (ν.real {false})) := by
  -- Use the same proof skeleton as Bridge.lean's `klDiv_discrete_toReal_eq_sum`,
  -- specialized to `Bool` (Fintype with 2 elements).
  have h_univ : μ Set.univ = ν Set.univ := by
    rw [measure_univ, measure_univ]
  rw [toReal_klDiv_of_measure_eq hμν h_univ]
  have h_int : Integrable (llr μ ν) μ := by
    refine ⟨(measurable_llr μ ν).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ =>
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  rw [integral_fintype h_int]
  -- Now expand the Fintype sum over `Bool = {true, false}` and per-point rewrite.
  -- `Fintype.sum_bool` gives `∑ b : Bool, f b = f true + f false`.
  rw [show (∑ b : Bool, μ.real {b} • llr μ ν b)
      = μ.real {true} • llr μ ν true + μ.real {false} • llr μ ν false from by
        rw [Fintype.sum_bool]]
  -- Per-point rewrite: `μ.real {b} • llr μ ν b = μ.real {b} * (log μ.real{b} - log ν.real{b})`
  have h_per_point : ∀ b : Bool,
      μ.real {b} • llr μ ν b = μ.real {b} * (Real.log (μ.real {b}) - Real.log (ν.real {b})) := by
    intro b
    show μ.real {b} * Real.log (μ.rnDeriv ν b).toReal
      = μ.real {b} * (Real.log (μ.real {b}) - Real.log (ν.real {b}))
    by_cases hμb : μ.real {b} = 0
    · simp [hμb]
    -- `μ.real {b} > 0` ⇒ `ν.real {b} > 0` and rnDeriv equals their ratio.
    have hμ_ne : μ {b} ≠ 0 := by
      intro h
      apply hμb
      rw [Measure.real, h]; rfl
    have hν_ne : ν {b} ≠ 0 := fun h => hμ_ne (hμν h)
    have hνb_pos : 0 < ν.real {b} := by
      refine lt_of_le_of_ne measureReal_nonneg (Ne.symm ?_)
      intro hνb
      apply hν_ne
      rwa [Measure.real, ENNReal.toReal_eq_zero_iff,
        or_iff_left (measure_ne_top ν {b})] at hνb
    have hμb_pos : 0 < μ.real {b} :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hμb)
    -- ENNReal identity: `(μ.rnDeriv ν b) * ν {b} = μ {b}`.
    have h_rnD_enn : (μ.rnDeriv ν b) * ν {b} = μ {b} := by
      have h_wd : ν.withDensity (μ.rnDeriv ν) = μ :=
        Measure.withDensity_rnDeriv_eq μ ν hμν
      have h1 : (ν.withDensity (μ.rnDeriv ν)) {b} = μ {b} := by rw [h_wd]
      rw [withDensity_apply _ (measurableSet_singleton b),
        lintegral_singleton] at h1
      exact h1
    have h_rnD_real : (μ.rnDeriv ν b).toReal * ν.real {b} = μ.real {b} := by
      rw [Measure.real, Measure.real, ← ENNReal.toReal_mul, h_rnD_enn]
    have h_rnD_div : (μ.rnDeriv ν b).toReal = μ.real {b} / ν.real {b} := by
      field_simp
      linarith [h_rnD_real]
    rw [h_rnD_div, Real.log_div hμb_pos.ne' hνb_pos.ne']
  rw [h_per_point true, h_per_point false]

omit [DecidableEq α] [Nonempty α] in
/-- 検定 `s : Set (Fin n → α)` の Bool 値 indicator 関数。 -/
private noncomputable def steinTestFn (n : ℕ) (s : Set (Fin n → α)) :
    (Fin n → α) → Bool :=
  fun x => @decide (x ∈ s) (Classical.dec _)

omit [DecidableEq α] [Nonempty α] in
private lemma measurable_steinTestFn (n : ℕ) (s : Set (Fin n → α)) :
    Measurable (steinTestFn n s) := measurable_of_finite _

omit [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- 検定 indicator の preimage of `{true}` is `s`. -/
private lemma steinTestFn_preimage_true (n : ℕ) (s : Set (Fin n → α)) :
    steinTestFn n s ⁻¹' {true} = s := by
  ext x
  simp [steinTestFn]

omit [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- 検定 indicator の preimage of `{false}` is `sᶜ`. -/
private lemma steinTestFn_preimage_false (n : ℕ) (s : Set (Fin n → α)) :
    steinTestFn n s ⁻¹' {false} = sᶜ := by
  ext x
  simp [steinTestFn]

omit [DecidableEq α] [Nonempty α] in
/-- 検定 indicator pushforward の Bool {true} 値は `μ s`. -/
private lemma steinTestFn_map_true (n : ℕ) (s : Set (Fin n → α)) (μ : Measure (Fin n → α)) :
    (μ.map (steinTestFn n s)) {true} = μ s := by
  rw [Measure.map_apply (measurable_steinTestFn n s) (measurableSet_singleton _),
      steinTestFn_preimage_true]

omit [DecidableEq α] [Nonempty α] in
private lemma steinTestFn_map_false (n : ℕ) (s : Set (Fin n → α)) (μ : Measure (Fin n → α)) :
    (μ.map (steinTestFn n s)) {false} = μ sᶜ := by
  rw [Measure.map_apply (measurable_steinTestFn n s) (measurableSet_singleton _),
      steinTestFn_preimage_false]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Pi 化 absolute continuity: `P ≪ Q` ⇒ `Π_{Fin n} P ≪ Π_{Fin n} Q`.
`piFinSuccAbove` reshape + `AbsolutelyContinuous.prod` で induction。 -/
private theorem absolutelyContinuous_pi
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (n : ℕ) :
    Measure.pi (fun _ : Fin n => P) ≪ Measure.pi (fun _ : Fin n => Q) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => P), Measure.pi_of_empty (fun _ : Fin 0 => Q)]
  | succ k ih =>
    -- Use `piFinSuccAbove 0` to go via `α × (Fin k → α)`.
    set e : ((i : Fin (k + 1)) → (fun _ => α) i) ≃ᵐ
              α × ((j : Fin k) → (fun _ => α) ((0 : Fin (k + 1)).succAbove j)) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => α) 0 with he_def
    have hP_pres : MeasurePreserving e
        (Measure.pi (fun _ : Fin (k + 1) => P))
        (P.prod (Measure.pi (fun _ : Fin k => P))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => P) (0 : Fin (k + 1))
    have hQ_pres : MeasurePreserving e
        (Measure.pi (fun _ : Fin (k + 1) => Q))
        (Q.prod (Measure.pi (fun _ : Fin k => Q))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => Q) (0 : Fin (k + 1))
    have hP_map : (Measure.pi (fun _ : Fin (k + 1) => P)).map e
        = P.prod (Measure.pi (fun _ : Fin k => P)) := hP_pres.map_eq
    have hQ_map : (Measure.pi (fun _ : Fin (k + 1) => Q)).map e
        = Q.prod (Measure.pi (fun _ : Fin k => Q)) := hQ_pres.map_eq
    -- Step 1: AC for product measures from coordinate-wise AC.
    have h_prod_ac : (P.prod (Measure.pi (fun _ : Fin k => P)))
        ≪ (Q.prod (Measure.pi (fun _ : Fin k => Q))) :=
      Measure.AbsolutelyContinuous.prod hPQ ih
    -- Step 2: Lift back via `e.symm` (also measure-preserving).
    have h_e_sym_meas : Measurable e.symm := e.symm.measurable
    have h_e_meas : Measurable e := e.measurable
    -- Use `e` is a MeasurableEquiv, so `(map e μ ≪ map e ν) ↔ (μ ≪ ν)`.
    have hPe : Measure.pi (fun _ : Fin (k + 1) => P)
        = (P.prod (Measure.pi (fun _ : Fin k => P))).map e.symm := by
      rw [← hP_map, Measure.map_map h_e_sym_meas h_e_meas, e.symm_comp_self, Measure.map_id]
    have hQe : Measure.pi (fun _ : Fin (k + 1) => Q)
        = (Q.prod (Measure.pi (fun _ : Fin k => Q))).map e.symm := by
      rw [← hQ_map, Measure.map_map h_e_sym_meas h_e_meas, e.symm_comp_self, Measure.map_id]
    rw [hPe, hQe]
    exact h_prod_ac.map h_e_sym_meas

omit [DecidableEq α] [Nonempty α] in
/-- **Stein converse (Bool KL ≤ n · klDiv P Q form)**: any α-level test `s` satisfies
    `klDiv ((Pi P).map (testFn s)) ((Pi Q).map (testFn s)) ≤ n · klDiv P Q`.
    DPI + Pi 化 chain rule の合成。 -/
theorem stein_converse_bool_kl_le
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (s : Set (Fin n → α)) :
    klDiv ((Measure.pi (fun _ : Fin n => P)).map (steinTestFn n s))
          ((Measure.pi (fun _ : Fin n => Q)).map (steinTestFn n s))
      ≤ (n : ℝ≥0∞) * klDiv P Q := by
  rw [← klDiv_pi_eq_n_smul P Q n]
  exact klDiv_map_le (measurable_steinTestFn n s) _ _

omit [DecidableEq α] [Nonempty α] in
/-- **Stein converse (post-DPI sum-form bound)**: under α-level `P^n sᶜ ≤ ε`, the
Bernoulli sum-form lower bound on `klDiv ((P^n).map test) ((Q^n).map test)` gives
the `(P^n s) log((P^n s)/(Q^n s)) + (P^n sᶜ) log((P^n sᶜ)/(Q^n sᶜ)) ≤ n · klDiv P Q`
inequality. -/
theorem stein_converse_sum_form
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (n : ℕ) (s : Set (Fin n → α)) :
    let Pn := Measure.pi (fun _ : Fin n => P)
    let Qn := Measure.pi (fun _ : Fin n => Q)
    (Pn.real s) * (Real.log (Pn.real s) - Real.log (Qn.real s))
    + (Pn.real sᶜ) * (Real.log (Pn.real sᶜ) - Real.log (Qn.real sᶜ))
    ≤ (n : ℝ) * (klDiv P Q).toReal := by
  classical
  intro Pn Qn
  have hPnQn : Pn ≪ Qn := absolutelyContinuous_pi P Q hPQ n
  have hf := measurable_steinTestFn n s
  have hPn_map_ac : Pn.map (steinTestFn n s) ≪ Qn.map (steinTestFn n s) := hPnQn.map hf
  -- Probability measure instances on Pi-pushforward.
  have h_Pn_map_prob : IsProbabilityMeasure (Pn.map (steinTestFn n s)) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have h_Qn_map_prob : IsProbabilityMeasure (Qn.map (steinTestFn n s)) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  -- Translation lemmas: pushforward Bool masses = original measures of `s` / `sᶜ`.
  have h_P_true : (Pn.map (steinTestFn n s)).real {true} = Pn.real s := by
    show ((Pn.map (steinTestFn n s)) {true}).toReal = (Pn s).toReal
    rw [steinTestFn_map_true n s Pn]
  have h_P_false : (Pn.map (steinTestFn n s)).real {false} = Pn.real sᶜ := by
    show ((Pn.map (steinTestFn n s)) {false}).toReal = (Pn sᶜ).toReal
    rw [steinTestFn_map_false n s Pn]
  have h_Q_true : (Qn.map (steinTestFn n s)).real {true} = Qn.real s := by
    show ((Qn.map (steinTestFn n s)) {true}).toReal = (Qn s).toReal
    rw [steinTestFn_map_true n s Qn]
  have h_Q_false : (Qn.map (steinTestFn n s)).real {false} = Qn.real sᶜ := by
    show ((Qn.map (steinTestFn n s)) {false}).toReal = (Qn sᶜ).toReal
    rw [steinTestFn_map_false n s Qn]
  -- Sum-form expansion of LHS = the post-DPI Bool KL.
  have h_sum_eq : (klDiv (Pn.map (steinTestFn n s)) (Qn.map (steinTestFn n s))).toReal
      = (Pn.real s) * (Real.log (Pn.real s) - Real.log (Qn.real s))
      + (Pn.real sᶜ) * (Real.log (Pn.real sᶜ) - Real.log (Qn.real sᶜ)) := by
    rw [klDiv_bool_toReal_eq_sum _ _ hPn_map_ac]
    rw [h_P_true, h_P_false, h_Q_true, h_Q_false]
  -- DPI bound on the ENNReal side.
  have h_dpi := stein_converse_bool_kl_le P Q n s
  -- Lift to toReal using `klDiv P Q ≠ ∞`.
  have h_int_llr : Integrable (llr P Q) P := by
    refine ⟨(measurable_llr P Q).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ =>
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  have h_kl_ne_top : klDiv P Q ≠ ∞ := klDiv_ne_top hPQ h_int_llr
  have h_n_kl_ne_top : (n : ℝ≥0∞) * klDiv P Q ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) h_kl_ne_top
  have h_dpi_real : (klDiv (Pn.map (steinTestFn n s)) (Qn.map (steinTestFn n s))).toReal
      ≤ ((n : ℝ≥0∞) * klDiv P Q).toReal :=
    ENNReal.toReal_mono h_n_kl_ne_top h_dpi
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h_dpi_real
  rw [← h_sum_eq]
  exact h_dpi_real

/-! ### Phase E — Stein converse (final inequality form)

`stein_converse_sum_form` (Bool sum-form bound) を α-level + sign analysis で整理し、
`-(1/n) log Q^n s ≤ klDiv P Q / (1-ε) + log 2 / (n(1-ε))` の形に到達する。

Key bounds (ε ∈ (0,1) fixed, `s` α-level, `Pn s ≥ 1-ε`, `Qn s ∈ (0, 1]`, `Qn sᶜ ∈ (0,1]`):
* Term 1 lower bound: `(Pn s)(log Pn s - log Qn s)
    ≥ (Pn s) log Pn s + (1-ε)(-log Qn s)
    = -negMulLog(Pn s) + (1-ε)(-log Qn s)`
* Term 2 lower bound: `(Pn sᶜ)(log Pn sᶜ - log Qn sᶜ)
    ≥ (Pn sᶜ) log Pn sᶜ + 0   (since `-(Pn sᶜ) log Qn sᶜ ≥ 0`)
    = -negMulLog(Pn sᶜ)`
* Sum: `S ≥ -binEntropy(Pn s) + (1-ε)(-log Qn s) ≥ -log 2 + (1-ε)(-log Qn s)`. -/

omit [DecidableEq α] [Nonempty α] in
/-- **Stein converse (concrete inequality)**: for any measurable α-level test `s`
(`P^n sᶜ ≤ ε`) with `0 < n`, the type-II error satisfies
`-(1/n) log Q^n s ≤ klDiv P Q / (1-ε) + log 2 / (n(1-ε))`.

Proof: Bool sum-form bound `S ≤ n · klDiv P Q` combined with the algebraic inequality
`S ≥ -log 2 + (1-ε)(-log Q^n s)` (uses α-level + `binEntropy ≤ log 2` + sign of `log Q^n sᶜ`). -/
@[entry_point]
theorem stein_converse_finite_n
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (_hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (_hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn_pos : 0 < n) (s : Set (Fin n → α)) (hs : MeasurableSet s)
    (hPn_sc_le : ((Measure.pi (fun _ : Fin n => P)) sᶜ).toReal ≤ ε) :
    -((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal
      ≤ (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε)) := by
  classical
  set Pn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => P) with hPn_def
  set Qn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => Q) with hQn_def
  set K : ℝ := (klDiv P Q).toReal with hK_def
  have h_one_sub_eps_pos : (0 : ℝ) < 1 - ε := by linarith
  have h_n_R_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have h_Pn_prob : IsProbabilityMeasure Pn := by infer_instance
  have h_Qn_prob : IsProbabilityMeasure Qn := by infer_instance
  -- Step A: positivity of Pn univ = Qn univ = 1; complements of measurable sets.
  have hsc : MeasurableSet sᶜ := hs.compl
  -- Pn s + Pn sᶜ = 1.
  have h_Pn_total : Pn.real s + Pn.real sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hs]
    exact probReal_univ
  have h_Pn_sc_eq : Pn.real sᶜ = (Pn sᶜ).toReal := rfl
  have h_Pn_s_ge : Pn.real s ≥ 1 - ε := by
    have := hPn_sc_le
    rw [← h_Pn_sc_eq] at this
    linarith
  have h_Pn_s_R_nn : 0 ≤ Pn.real s := measureReal_nonneg
  have h_Pn_sc_R_nn : 0 ≤ Pn.real sᶜ := measureReal_nonneg
  -- Step B: positivity of Qn s and Qn sᶜ.
  -- Pick any x ∈ Fin n → α; then `{x}` has positive Qn-mass since hQpos.
  -- Pn s ≥ 1 - ε > 0 implies s nonempty, so Qn s > 0.
  have h_Pn_s_pos : 0 < Pn.real s := by linarith
  -- s nonempty (from Pn.real s > 0).
  have h_s_nonempty : s.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h_empty
    rw [h_empty] at h_Pn_s_pos
    simp at h_Pn_s_pos
  obtain ⟨x_witness, hx_in_s⟩ := h_s_nonempty
  -- Qn {x_witness} > 0 from hQpos.
  have h_Qn_x_pos : 0 < (Qn.real {x_witness}) := by
    rw [hQn_def]
    show ((Measure.pi (fun _ : Fin n => Q)) {x_witness}).toReal > 0
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    exact Finset.prod_pos (fun i _ => hQpos (x_witness i))
  have h_Qn_s_pos : 0 < Qn.real s := by
    have h_subset : ({x_witness} : Set (Fin n → α)) ⊆ s := by
      intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact hx_in_s
    have : Qn.real {x_witness} ≤ Qn.real s := MeasureTheory.measureReal_mono h_subset
    linarith
  -- Qn sᶜ > 0: similarly, but only if sᶜ is nonempty. If s = univ, Qn sᶜ = 0;
  -- but the case Pn sᶜ = 0 is consistent with sᶜ having empty support.
  -- We handle the case Qn sᶜ = 0 separately using `log 0 = 0` convention.
  -- Step C: Bool sum-form bound from `stein_converse_sum_form`.
  have h_sum_bound := stein_converse_sum_form P Q hPQ n s
  simp only at h_sum_bound
  -- (Pn s)(log Pn s - log Qn s) + (Pn sᶜ)(log Pn sᶜ - log Qn sᶜ) ≤ n · K.
  -- Step D: Algebraic lower bound on the LHS (let `S` denote it).
  -- Key bounds:
  --   (i) Qn.real sᶜ ≤ 1, so log Qn.real sᶜ ≤ 0, so -(Pn.real sᶜ)(log Qn.real sᶜ) ≥ 0.
  --   (ii) Qn.real s ≤ 1, so log Qn.real s ≤ 0, so -log Qn.real s ≥ 0.
  --   (iii) (Pn.real s) log Pn.real s + (Pn.real sᶜ) log Pn.real sᶜ = -binEntropy(Pn.real s) ≥ -log 2.
  have h_Qn_sc_le_one : Qn.real sᶜ ≤ 1 := by
    have : Qn.real sᶜ ≤ Qn.real Set.univ := MeasureTheory.measureReal_mono (Set.subset_univ _)
    rw [show Qn.real Set.univ = 1 from probReal_univ] at this
    exact this
  have h_log_Qn_sc_nonpos : Real.log (Qn.real sᶜ) ≤ 0 :=
    Real.log_nonpos measureReal_nonneg h_Qn_sc_le_one
  have h_Qn_s_le_one : Qn.real s ≤ 1 := by
    have : Qn.real s ≤ Qn.real Set.univ := MeasureTheory.measureReal_mono (Set.subset_univ _)
    rw [show Qn.real Set.univ = 1 from probReal_univ] at this
    exact this
  have h_log_Qn_s_nonpos : Real.log (Qn.real s) ≤ 0 :=
    Real.log_nonpos measureReal_nonneg h_Qn_s_le_one
  have h_neg_log_Qn_s_nn : 0 ≤ -Real.log (Qn.real s) := by linarith
  -- Term -(Pn.real sᶜ) log Qn.real sᶜ = Pn.real sᶜ * (- log Qn.real sᶜ) ≥ 0.
  have h_term_sc_nn : 0 ≤ -(Pn.real sᶜ * Real.log (Qn.real sᶜ)) := by
    have : Pn.real sᶜ * (- Real.log (Qn.real sᶜ)) ≥ 0 :=
      mul_nonneg h_Pn_sc_R_nn (by linarith)
    linarith
  -- (Pn.real s) log Pn.real s + (Pn.real sᶜ) log Pn.real sᶜ = -binEntropy (Pn.real s).
  -- Use Pn.real sᶜ = 1 - Pn.real s.
  have h_Pn_sc_eq_1m : Pn.real sᶜ = 1 - Pn.real s := by linarith
  have h_neg_binE_eq :
      Pn.real s * Real.log (Pn.real s) + Pn.real sᶜ * Real.log (Pn.real sᶜ)
        = -Real.binEntropy (Pn.real s) := by
    rw [h_Pn_sc_eq_1m]
    -- binEntropy p = p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹ = -(p log p + (1-p) log(1-p)).
    rw [Real.binEntropy]
    rw [Real.log_inv, Real.log_inv]
    ring
  have h_binE_le_log2 : Real.binEntropy (Pn.real s) ≤ Real.log 2 :=
    Real.binEntropy_le_log_two
  -- Build S ≥ -log 2 + (Pn.real s) * (-log Qn.real s).
  have h_S_lower :
      Pn.real s * (Real.log (Pn.real s) - Real.log (Qn.real s))
      + Pn.real sᶜ * (Real.log (Pn.real sᶜ) - Real.log (Qn.real sᶜ))
        ≥ -Real.log 2 + Pn.real s * (-Real.log (Qn.real s)) := by
    have h_expand :
        Pn.real s * (Real.log (Pn.real s) - Real.log (Qn.real s))
          + Pn.real sᶜ * (Real.log (Pn.real sᶜ) - Real.log (Qn.real sᶜ))
        = (Pn.real s * Real.log (Pn.real s) + Pn.real sᶜ * Real.log (Pn.real sᶜ))
          + Pn.real s * (-Real.log (Qn.real s))
          + (-(Pn.real sᶜ * Real.log (Qn.real sᶜ))) := by ring
    rw [h_expand, h_neg_binE_eq]
    linarith
  -- Build (Pn.real s) * (-log Qn.real s) ≥ (1-ε) * (-log Qn.real s).
  have h_term1_lower :
      Pn.real s * (-Real.log (Qn.real s)) ≥ (1 - ε) * (-Real.log (Qn.real s)) :=
    mul_le_mul_of_nonneg_right h_Pn_s_ge h_neg_log_Qn_s_nn
  -- Combine: S ≥ -log 2 + (1-ε)(-log Qn s).
  have h_S_lower_final :
      Pn.real s * (Real.log (Pn.real s) - Real.log (Qn.real s))
      + Pn.real sᶜ * (Real.log (Pn.real sᶜ) - Real.log (Qn.real sᶜ))
        ≥ -Real.log 2 + (1 - ε) * (-Real.log (Qn.real s)) := by linarith
  -- Step E: Combine S ≤ n · K with S ≥ -log 2 + (1-ε)(-log Qn s).
  have h_chain : -Real.log 2 + (1 - ε) * (-Real.log (Qn.real s)) ≤ (n : ℝ) * K :=
    le_trans h_S_lower_final h_sum_bound
  have h_div : (1 - ε) * (-Real.log (Qn.real s)) ≤ (n : ℝ) * K + Real.log 2 := by linarith
  have h_neg_log_le : -Real.log (Qn.real s) ≤ ((n : ℝ) * K + Real.log 2) / (1 - ε) := by
    rw [le_div_iff₀ h_one_sub_eps_pos]
    linarith
  -- Convert `-(1/n) log Qn s = (1/n) * (-log Qn s)`.
  have h_target_eq : -((1 : ℝ) / n) * Real.log (Qn.real s) = (1 / n) * (-Real.log (Qn.real s)) := by
    ring
  -- Multiply by 1/n (positive) on both sides.
  have h_one_div_n_pos : 0 < (1 : ℝ) / n := by positivity
  have h_div_n : (1 / (n : ℝ)) * (-Real.log (Qn.real s))
      ≤ (1 / n) * (((n : ℝ) * K + Real.log 2) / (1 - ε)) := by
    exact mul_le_mul_of_nonneg_left h_neg_log_le h_one_div_n_pos.le
  -- Simplify (1/n) * ((n*K + log 2) / (1-ε)) = K/(1-ε) + log 2 / (n(1-ε)).
  have h_simp_R : (1 / (n : ℝ)) * (((n : ℝ) * K + Real.log 2) / (1 - ε))
      = K / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε)) := by
    field_simp
  -- Convert `Pn.real s = (Pn s).toReal` etc. to expected statement form.
  have h_target : -((1 : ℝ) / n) * Real.log (Qn.real s)
      ≤ K / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε)) := by
    rw [h_target_eq]
    rw [← h_simp_R]
    exact h_div_n
  -- Unfold Qn.real and conclude.
  show -((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal
      ≤ (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε))
  exact h_target

/-! ### Phase C — Tendsto 形統合: `steinOptimalBeta` + liminf/limsup sandwich

`stein_achievability` (lower side, eventually) と `stein_converse_finite_n`
(upper side, pointwise) を `steinOptimalBeta P Q n ε` 経由で liminf / limsup に
持ち上げる:

```
(klDiv P Q).toReal ≤ liminf_n -(1/n) * log (steinOptimalBeta P Q n ε)
limsup_n -(1/n) * log (steinOptimalBeta P Q n ε) ≤ (klDiv P Q).toReal / (1 - ε)
```

Converse の `1/(1-ε)` 補正は本 plan の `stein_converse_finite_n` の DPI + log-sum
下界 routes で構造的に残るため、strict `Tendsto → klDiv` ではなく sandwich 形に
なる (strong Stein には strong converse が必要)。`ε → 0+` の極限を取ると上限が
`klDiv` に押し戻る (`inf_{ε ∈ (0,1)} K/(1-ε) = K`)。 -/

/-- The set of type-II error probabilities of α-level tests at level `ε`. -/
noncomputable def steinBetaSet
    (P Q : Measure α) (n : ℕ) (ε : ℝ) : Set ℝ :=
  { β : ℝ | ∃ (s : Set (Fin n → α)), MeasurableSet s ∧
        ((Measure.pi (fun _ : Fin n => P)) sᶜ).toReal ≤ ε ∧
        β = ((Measure.pi (fun _ : Fin n => Q)) s).toReal }

/-- The optimal type-II error subject to type-I ≤ ε. -/
@[entry_point]
noncomputable def steinOptimalBeta
    (P Q : Measure α) (n : ℕ) (ε : ℝ) : ℝ :=
  sInf (steinBetaSet P Q n ε)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `s := Set.univ` is always an α-level test (its complement has measure 0). -/
lemma one_mem_steinBetaSet
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (1 : ℝ) ∈ steinBetaSet P Q n ε := by
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · rw [Set.compl_univ]
    simp only [measure_empty, ENNReal.toReal_zero]
    exact hε
  · show 1 = ((Measure.pi (fun _ : Fin n => Q)) Set.univ).toReal
    rw [show ((Measure.pi (fun _ : Fin n => Q)) Set.univ).toReal
      = (Measure.pi (fun _ : Fin n => Q)).real Set.univ from rfl, probReal_univ]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma steinBetaSet_nonempty
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (steinBetaSet P Q n ε).Nonempty :=
  ⟨1, one_mem_steinBetaSet P Q n ε hε⟩

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma steinBetaSet_bddBelow
    (P Q : Measure α) (n : ℕ) (ε : ℝ) :
    BddBelow (steinBetaSet P Q n ε) := by
  refine ⟨0, ?_⟩
  rintro β ⟨s, _, _, rfl⟩
  exact ENNReal.toReal_nonneg

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
@[entry_point]
lemma steinOptimalBeta_nonneg
    (P Q : Measure α) (n : ℕ) (ε : ℝ) :
    0 ≤ steinOptimalBeta P Q n ε := by
  by_cases h : (steinBetaSet P Q n ε).Nonempty
  · exact le_csInf h fun _ ⟨_, _, _, hβ⟩ => hβ ▸ ENNReal.toReal_nonneg
  · simp [steinOptimalBeta, Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
@[entry_point]
lemma steinOptimalBeta_le_one
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    steinOptimalBeta P Q n ε ≤ 1 :=
  csInf_le (steinBetaSet_bddBelow P Q n ε) (one_mem_steinBetaSet P Q n ε hε)

omit [DecidableEq α] [Nonempty α] in
/-- Pointwise converse bound in exponential form: for any α-level test `s`,
`Q^n s ≥ exp(-n * (K/(1-ε) + log 2 / (n(1-ε))))`. Derived from
`stein_converse_finite_n` by taking `exp` of both sides. -/
lemma exp_le_Qn_of_alpha_level
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 0 < n)
    (s : Set (Fin n → α)) (hs : MeasurableSet s)
    (hα : ((Measure.pi (fun _ : Fin n => P)) sᶜ).toReal ≤ ε) :
    Real.exp (-((n : ℝ) * ((klDiv P Q).toReal / (1 - ε)
        + Real.log 2 / ((n : ℝ) * (1 - ε)))))
      ≤ ((Measure.pi (fun _ : Fin n => Q)) s).toReal := by
  -- Q^n s > 0: reproduce the argument from stein_converse_finite_n.
  set Qn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => Q)
  set Pn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => P)
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_one_sub_eps_pos : (0 : ℝ) < 1 - ε := by linarith
  -- P^n s ≥ 1 - ε > 0, hence s nonempty, hence Q^n s ≥ Q^n {x_witness} > 0.
  have h_Pn_total : Pn.real s + Pn.real sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hs]
    exact probReal_univ
  have h_Pn_sc_eq : Pn.real sᶜ = (Pn sᶜ).toReal := rfl
  have h_Pn_s_pos : 0 < Pn.real s := by rw [h_Pn_sc_eq] at h_Pn_total; linarith
  have h_s_nonempty : s.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h_empty
    rw [h_empty] at h_Pn_s_pos; simp at h_Pn_s_pos
  obtain ⟨x_w, hx_in_s⟩ := h_s_nonempty
  have h_Qn_x_pos : 0 < Qn.real {x_w} := by
    show 0 < ((Measure.pi (fun _ : Fin n => Q)) {x_w}).toReal
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    exact Finset.prod_pos (fun i _ => hQpos (x_w i))
  have h_Qn_s_pos : 0 < Qn.real s := by
    have h_subset : ({x_w} : Set (Fin n → α)) ⊆ s := by
      intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact hx_in_s
    have := MeasureTheory.measureReal_mono (μ := Qn) h_subset
    linarith
  have h_Qn_s_real_pos : 0 < ((Measure.pi (fun _ : Fin n => Q)) s).toReal := h_Qn_s_pos
  -- Apply stein_converse_finite_n.
  have h_conv := stein_converse_finite_n P Q hPpos hPQ hQpos hε hε1 hn s hs hα
  -- h_conv : -(1/n) * log Q^n s ≤ K/(1-ε) + log 2/(n(1-ε))
  -- Multiply both sides by -n: log Q^n s ≥ -n * (K/(1-ε) + log 2/(n(1-ε)))
  set B : ℝ := (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε))
  have h_log_ge : Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal ≥ -((n : ℝ) * B) := by
    have h_neg_inv_lt : -((1 : ℝ) / n) < 0 := by
      have : (0 : ℝ) < 1 / n := one_div_pos.mpr hn_R_pos
      linarith
    -- From -(1/n) * x ≤ B and -(1/n) < 0, we get x ≥ -nB.
    -- More directly: -(1/n) * x ≤ B ⟺ x * (-(1/n)) ≤ B ⟺ x ≥ B / (-(1/n)) = -nB.
    have h_eq : -((n : ℝ) * B) = -n * B := by ring
    -- Multiply h_conv by -n (negative) flips: log Q^n s ≥ -n * B.
    -- Concretely: log Q^n s = (-n) * (-(1/n) * log Q^n s) and -(1/n) log Q^n s ≤ B.
    have h_step : (-(n : ℝ)) * (-((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal)
        ≥ (-(n : ℝ)) * B := by
      apply mul_le_mul_of_nonpos_left h_conv
      linarith
    have h_simp : (-(n : ℝ)) * (-((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal)
        = Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal := by
      field_simp
    rw [h_simp] at h_step
    linarith
  -- exp_le_exp + Real.exp_log h_Qn_s_real_pos:
  have h_exp_chain :
      Real.exp (-((n : ℝ) * B))
        ≤ Real.exp (Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal) :=
    Real.exp_le_exp.mpr h_log_ge
  rw [Real.exp_log h_Qn_s_real_pos] at h_exp_chain
  exact h_exp_chain

omit [DecidableEq α] [Nonempty α] in
/-- The set `steinBetaSet` is bounded below by `exp(-n * (K/(1-ε) + log 2/(n(1-ε))))`,
hence `steinOptimalBeta` is also. -/
lemma exp_le_steinOptimalBeta
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 0 < n) :
    Real.exp (-((n : ℝ) * ((klDiv P Q).toReal / (1 - ε)
        + Real.log 2 / ((n : ℝ) * (1 - ε)))))
      ≤ steinOptimalBeta P Q n ε := by
  apply le_csInf (steinBetaSet_nonempty P Q n ε hε.le)
  rintro β ⟨s, hs, hα, rfl⟩
  exact exp_le_Qn_of_alpha_level P Q hPpos hPQ hQpos hε hε1 hn s hs hα

omit [DecidableEq α] [Nonempty α] in
/-- `steinOptimalBeta` is strictly positive (under our hypotheses). -/
lemma steinOptimalBeta_pos
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 0 < n) :
    0 < steinOptimalBeta P Q n ε :=
  lt_of_lt_of_le (Real.exp_pos _) (exp_le_steinOptimalBeta P Q hPpos hPQ hQpos hε hε1 hn)

omit [DecidableEq α] [Nonempty α] in
/-- Converse-side upper bound on the rate:
`-(1/n) log steinOptimalBeta ≤ K/(1-ε) + log 2/(n(1-ε))`. -/
@[entry_point]
theorem steinOptimalBeta_log_le_of_converse
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} (hn : 0 < n) :
    -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε)
      ≤ (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε)) := by
  have h_pos := steinOptimalBeta_pos P Q hPpos hPQ hQpos hε hε1 hn
  have h_exp_le := exp_le_steinOptimalBeta P Q hPpos hPQ hQpos hε hε1 hn
  set B : ℝ := (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε))
  -- exp(-nB) ≤ steinOptimalBeta ⟹ -nB ≤ log steinOptimalBeta ⟹ -(1/n) log ≤ B.
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have h_log_ge : -((n : ℝ) * B) ≤ Real.log (steinOptimalBeta P Q n ε) := by
    have h_log_mono := Real.log_le_log (Real.exp_pos _) h_exp_le
    rwa [Real.log_exp] at h_log_mono
  -- Multiply by -(1/n) < 0, flips inequality.
  have h_neg_inv_neg : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h_step : -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε)
      ≤ -((1 : ℝ) / n) * (-((n : ℝ) * B)) :=
    mul_le_mul_of_nonpos_left h_log_ge h_neg_inv_neg
  have h_simp : -((1 : ℝ) / n) * (-((n : ℝ) * B)) = B := by field_simp
  linarith

omit [DecidableEq α] in
/-- Achievability-side lower bound on the rate: eventually
`K - δ ≤ -(1/n) log steinOptimalBeta`. -/
@[entry_point]
theorem steinOptimalBeta_log_ge_of_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P)
    (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P))
    (hPpos : ∀ x : α, 0 < P.real {x})
    (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x})
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (klDiv P Q).toReal - δ
        ≤ -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε) := by
  have h_ach := stein_achievability μ P Q Xs hXs hindep hident hMap hMapJoint
    hPpos hPQ hQpos hε hε1 hδ
  filter_upwards [h_ach, eventually_gt_atTop 0] with n h_ex hn_pos
  obtain ⟨s, hs_meas, hs_alpha, hs_log⟩ := h_ex
  -- hs_log : K - δ ≤ -(1/n) log Q^n s
  -- (Q^n s).toReal ∈ steinBetaSet, so steinOptimalBeta ≤ Q^n s.
  set Qn_s : ℝ := ((Measure.pi (fun _ : Fin n => Q)) s).toReal with hQns_def
  have h_in_set : Qn_s ∈ steinBetaSet P Q n ε := ⟨s, hs_meas, hs_alpha, rfl⟩
  have h_optBeta_le : steinOptimalBeta P Q n ε ≤ Qn_s :=
    csInf_le (steinBetaSet_bddBelow P Q n ε) h_in_set
  -- Both sides positive: steinOptimalBeta > 0 (from converse-side bound) and Qn_s > 0.
  have h_opt_pos := steinOptimalBeta_pos P Q hPpos hPQ hQpos hε hε1 hn_pos
  -- Qn_s > 0: reproduce from the achievability proof's argument (Q^n s ≥ Q^n {x} > 0).
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  set Pn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => P)
  set Qn : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => Q)
  have h_Pn_total : Pn.real s + Pn.real sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hs_meas]; exact probReal_univ
  have h_Pn_sc_eq : Pn.real sᶜ = (Pn sᶜ).toReal := rfl
  have h_Pn_s_pos : 0 < Pn.real s := by
    rw [h_Pn_sc_eq] at h_Pn_total
    have : Pn.real sᶜ = (Pn sᶜ).toReal := rfl
    linarith [hs_alpha, h_Pn_total]
  have h_s_nonempty : s.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]; intro h_empty
    rw [h_empty] at h_Pn_s_pos; simp at h_Pn_s_pos
  obtain ⟨x_w, hx_in_s⟩ := h_s_nonempty
  have h_Qn_x_pos : 0 < Qn.real {x_w} := by
    show 0 < ((Measure.pi (fun _ : Fin n => Q)) {x_w}).toReal
    rw [Measure.pi_singleton, ENNReal.toReal_prod]
    exact Finset.prod_pos (fun i _ => hQpos (x_w i))
  have h_Qns_pos : 0 < Qn_s := by
    have h_subset : ({x_w} : Set (Fin n → α)) ⊆ s := by
      intro y hy; simp only [Set.mem_singleton_iff] at hy; rw [hy]; exact hx_in_s
    have := MeasureTheory.measureReal_mono (μ := Qn) h_subset
    -- Qn.real {x_w} ≤ Qn.real s = Qn_s
    have h_eq : Qn.real s = Qn_s := rfl
    linarith
  -- log monotonicity: log steinOptimalBeta ≤ log Qn_s.
  have h_log_le : Real.log (steinOptimalBeta P Q n ε) ≤ Real.log Qn_s :=
    Real.log_le_log h_opt_pos h_optBeta_le
  -- Multiply by -(1/n) ≤ 0 flips:
  have h_neg_inv_nonpos : -((1 : ℝ) / n) ≤ 0 := by
    have : (0 : ℝ) ≤ 1 / n := by positivity
    linarith
  have h_rate_ge : -((1 : ℝ) / n) * Real.log Qn_s
      ≤ -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε) :=
    mul_le_mul_of_nonpos_left h_log_le h_neg_inv_nonpos
  -- Conclude from hs_log : K - δ ≤ -(1/n) log Qn_s ≤ -(1/n) log steinOptimalBeta.
  linarith


end InformationTheory.Shannon
