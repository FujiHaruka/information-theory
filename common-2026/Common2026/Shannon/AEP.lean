import Common2026.Shannon.Bridge
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# AEP — Asymptotic Equipartition Property (Phase A〜C)

漸近等分配性の形式化。Cover-Thomas 教科書 Theorem 3.1.1〜3.1.2 の Phase A〜C
(AEP 本体 + typical set の 3 主定理) をスコープとし、Phase D / E (源符号化定理)
は別ファイル。

## 構成

* **Phase A** — i.i.d. 列 `Xs : ℕ → Ω → α` から block `jointRV : Ω → (Fin n → α)`
  の定義 + 基本 measurability
* **Phase B** — probability AEP:
  `(1/n) ∑ i, (-Real.log ((μ.map (Xs 0)).real {Xs i ω}))` が `entropy μ (Xs 0)`
  に a.s. / 確率収束 (`strong_law_ae_real` を `Y i := −log P(Xs i ω)` で適用)
* **Phase C** — typical set `T_ε^n` の measurability + size bound + 確率 → 1

## i.i.d. 仮定の流儀

Mathlib に `IsIID` predicate は無いため、`strong_law_ae_real` と同じ 2 仮定形
`Pairwise (fun i j => Xs i ⟂ᵢ[μ] Xs j)` + `∀ i, IdentDistrib (Xs i) (Xs 0) μ μ`
を直接受ける。`(· ⟂ᵢ[μ] ·) on Xs` 形の `(· · ·)` anonymous lambda は `on` と
組み合わさったときに parsing 失敗するので、明示的な `fun i j => …` で書く。

## 撤退ライン (本シード)

Phase A〜C 緑通過 = AEP 単体 publish ライン。Phase D / E は次セッション。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Phase A — i.i.d. 列 と block joint RV -/

/-- Block joint random variable: `jointRV Xs n ω = (Xs 0 ω, Xs 1 ω, …, Xs (n-1) ω)`. -/
def jointRV (Xs : ℕ → Ω → α) (n : ℕ) : Ω → (Fin n → α) :=
  fun ω i => Xs i ω

@[simp] lemma jointRV_apply (Xs : ℕ → Ω → α) (n : ℕ) (ω : Ω) (i : Fin n) :
    jointRV Xs n ω i = Xs i ω := rfl

lemma measurable_jointRV (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (n : ℕ) :
    Measurable (jointRV Xs n) :=
  measurable_pi_lambda _ fun i => hXs i

/-! ### Phase B — probability AEP

The per-symbol log-likelihood is `−Real.log ((μ.map (Xs 0)).real {Xs i ω})`. We
bundle it via the alphabet-side function `pmfLog μ Xs : α → ℝ` so that
`logLikelihood μ Xs i ω = pmfLog μ Xs (Xs i ω)`. This shape lets us lift
`IdentDistrib (Xs i) (Xs 0)` and `IndepFun (Xs i) (Xs j)` to the `logLikelihood`
sequence by composition with the (always-measurable, finite-domain) `pmfLog`.
-/

/-- Alphabet-side `−log p(x)` function (independent of `i`). -/
noncomputable def pmfLog (μ : Measure Ω) (Xs : ℕ → Ω → α) : α → ℝ :=
  fun x => -Real.log ((μ.map (Xs 0)).real {x})

lemma measurable_pmfLog (μ : Measure Ω) (Xs : ℕ → Ω → α) :
    Measurable (pmfLog μ Xs) := by
  -- α is a discrete measurable space (`MeasurableSingletonClass α`), and α is `Fintype`
  -- ⇒ every function `α → ℝ` is measurable.
  exact measurable_of_finite _

/-- Per-symbol log-likelihood: `(−log P(Xs i ω))`. -/
noncomputable def logLikelihood
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (i : ℕ) : Ω → ℝ :=
  fun ω => pmfLog μ Xs (Xs i ω)

lemma logLikelihood_eq_comp (μ : Measure Ω) (Xs : ℕ → Ω → α) (i : ℕ) :
    logLikelihood μ Xs i = pmfLog μ Xs ∘ Xs i := rfl

lemma measurable_logLikelihood
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (i : ℕ) :
    Measurable (logLikelihood μ Xs i) :=
  (measurable_pmfLog μ Xs).comp (hXs i)

/-- `pmfLog μ Xs` is integrable on a finite alphabet (any function on a finite
discrete space is bounded, hence integrable for any finite measure). -/
lemma integrable_logLikelihood
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (i : ℕ) :
    Integrable (logLikelihood μ Xs i) μ := by
  -- `μ.map (Xs i)` is a probability measure, hence finite.
  have : IsProbabilityMeasure (μ.map (Xs i)) :=
    Measure.isProbabilityMeasure_map (hXs i).aemeasurable
  -- Any function on a finite discrete space is integrable for any finite measure.
  have h_int : Integrable (pmfLog μ Xs) (μ.map (Xs i)) := Integrable.of_finite
  -- Pull back through `Xs i`.
  exact h_int.comp_measurable (hXs i)

/-- The expectation of `logLikelihood μ Xs 0` is the entropy of `Xs 0`. -/
lemma integral_logLikelihood_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    ∫ ω, logLikelihood μ Xs 0 ω ∂μ = entropy μ (Xs 0) := by
  have hM0 : IsProbabilityMeasure (μ.map (Xs 0)) :=
    Measure.isProbabilityMeasure_map (hXs 0).aemeasurable
  -- Step 1: push forward via `Xs 0`.
  have h_push : ∫ ω, logLikelihood μ Xs 0 ω ∂μ
      = ∫ x, pmfLog μ Xs x ∂(μ.map (Xs 0)) := by
    rw [integral_map (hXs 0).aemeasurable
      (measurable_pmfLog μ Xs).aestronglyMeasurable]
    rfl
  rw [h_push]
  -- Step 2: collapse to a finite sum.
  rw [integral_fintype (μ := μ.map (Xs 0)) Integrable.of_finite]
  -- Step 3: rewrite each summand `(μ.map Xs 0).real {x} • pmfLog μ Xs x`
  -- as `Real.negMulLog ((μ.map Xs 0).real {x})`.
  unfold entropy
  refine Finset.sum_congr rfl fun x _ => ?_
  show (μ.map (Xs 0)).real {x} • pmfLog μ Xs x
      = Real.negMulLog ((μ.map (Xs 0)).real {x})
  rw [pmfLog, Real.negMulLog]
  simp [smul_eq_mul]

/-- Composition lift of `IdentDistrib` to `logLikelihood`. -/
lemma identDistrib_logLikelihood
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (i : ℕ) :
    IdentDistrib (logLikelihood μ Xs i) (logLikelihood μ Xs 0) μ μ := by
  simpa [logLikelihood_eq_comp] using (hident i).comp (measurable_pmfLog μ Xs)

/-- Composition lift of pairwise `IndepFun` to `logLikelihood`. -/
lemma indepFun_logLikelihood
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) :
    Pairwise fun i j =>
      logLikelihood μ Xs i ⟂ᵢ[μ] logLikelihood μ Xs j := by
  intro i j hij
  have h := hindep hij
  have hpf := measurable_pmfLog μ Xs
  simpa [logLikelihood_eq_comp] using h.comp hpf hpf

/-- **Probability AEP — almost sure version**: for an i.i.d. discrete sequence
`Xs : ℕ → Ω → α` with finite alphabet `α`, the empirical entropy estimator
`(1/n) ∑ i, (−log P(Xs i ω))` converges almost surely to the entropy `H(Xs 0)`. -/
theorem aep_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
      atTop
      (𝓝 (entropy μ (Xs 0))) := by
  -- Apply `strong_law_ae_real` with `Y i := logLikelihood μ Xs i`, then rewrite the
  -- limit using `integral_logLikelihood_zero`.
  have hint : Integrable (logLikelihood μ Xs 0) μ :=
    integrable_logLikelihood μ Xs hXs 0
  have hindLL : Pairwise fun i j =>
      logLikelihood μ Xs i ⟂ᵢ[μ] logLikelihood μ Xs j :=
    indepFun_logLikelihood μ Xs hindep
  have hidLL : ∀ i, IdentDistrib (logLikelihood μ Xs i) (logLikelihood μ Xs 0) μ μ :=
    identDistrib_logLikelihood μ Xs hident
  have h_lln := strong_law_ae_real (logLikelihood μ Xs) hint hindLL hidLL
  -- Replace `μ[logLikelihood μ Xs 0]` with `entropy μ (Xs 0)`.
  have h_int_eq := integral_logLikelihood_zero μ Xs hXs
  -- `μ[logLikelihood μ Xs 0]` notation expands to `∫ ω, logLikelihood μ Xs 0 ω ∂μ`.
  filter_upwards [h_lln] with ω hω
  simpa [h_int_eq] using hω

/-- **Probability AEP — convergence in probability**: the empirical entropy estimator
converges to `entropy μ (Xs 0)` in probability. -/
theorem aep_inProbability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
                                  - entropy μ (Xs 0)|})
      atTop
      (𝓝 0) := by
  -- Set up the Cesàro mean and the constant limit as functions of ω.
  set f : ℕ → Ω → ℝ :=
    fun n ω => (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n with hf_def
  set g : Ω → ℝ := fun _ => entropy μ (Xs 0) with hg_def
  -- AEStronglyMeasurable for `f n` and `g`.
  have h_meas_f : ∀ n, AEStronglyMeasurable (f n) μ := by
    intro n
    have h_sum_meas : Measurable
        (fun ω => ∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) :=
      Finset.measurable_sum _ fun i _ => measurable_logLikelihood μ Xs hXs i
    have h_meas : Measurable (f n) := by
      change Measurable (fun ω => (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
      exact h_sum_meas.div_const _
    exact h_meas.aestronglyMeasurable
  -- a.s. convergence from `aep_ae`.
  have h_ae := aep_ae μ Xs hXs hindep hident
  have h_ae' : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := h_ae
  -- Convert to convergence in measure.
  have h_inm : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_ae h_meas_f h_ae'
  -- Express in `dist` (= `|⋅|`) form.
  rw [tendstoInMeasure_iff_dist] at h_inm
  have h_target := h_inm ε hε
  -- Rewrite `dist (f n ω) (g ω)` as `|f n ω - g ω|`.
  refine Tendsto.congr (fun n => ?_) h_target
  apply congrArg μ
  ext ω
  show ε ≤ dist (f n ω) (g ω) ↔ ε ≤ |f n ω - g ω|
  rw [Real.dist_eq]

/-! ### Phase C — typical set `T_ε^n` -/

/-- **Typical set**: blocks `x : Fin n → α` whose empirical entropy is within `ε`
of the true entropy `H(Xs 0)`. -/
noncomputable def typicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    Set (Fin n → α) :=
  { x | |(∑ i : Fin n, pmfLog μ Xs (x i)) / n - entropy μ (Xs 0)| < ε }

lemma mem_typicalSet_iff
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) (x : Fin n → α) :
    x ∈ typicalSet μ Xs n ε ↔
      |(∑ i : Fin n, pmfLog μ Xs (x i)) / n - entropy μ (Xs 0)| < ε := Iff.rfl

/-- Measurability of the typical set. -/
theorem measurableSet_typicalSet
    (μ : Measure Ω)
    (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    MeasurableSet (typicalSet μ Xs n ε) := by
  -- `Fin n → α` is a finite discrete space (`Fintype` + `MeasurableSingletonClass`),
  -- so every subset is measurable.
  exact (Set.toFinite (typicalSet μ Xs n ε)).measurableSet

/-- **Size bound**: `|T_ε^n| ≤ exp (n · (H + ε))`. We state the bound with
`Real.exp` rather than `2^x` to avoid the `log 2` plumbing — the textbook
form follows by re-basing the logarithm.

**注**: 本補題は本シードの撤退ラインに該当 (`docs/proof-logs/proof-log-aep.md`
判断ログ参照)。証明には (a) `pmfLog` の sum を `log (∏ P(x i))` に展開、
(b) Phase A の `μ.map (jointRV) = Measure.pi` (= i.i.d. 直積分布) で全 typical
ブロックの確率和を上界、(c) `Real.exp` への往復、の 3 段が必要。Phase A の
Pi 構築 + サポート外点 (`P(x) = 0`) handling が最大の plumbing。次セッションで
再開予定。 -/
theorem typicalSet_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ) ≤
      Real.exp ((n : ℝ) * (entropy μ (Xs 0) + ε)) := by
  sorry

/-- **Typicality probability**: `P(jointRV Xs n ∈ T_ε^n) → 1`.

The event `{ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}` is the complement of
`{ω | ε ≤ |...|}` from `aep_inProbability`, so the probability tends to
`1 − 0 = 1`. -/
theorem typicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε})
      atTop
      (𝓝 1) := by
  -- The "bad" event from `aep_inProbability`.
  set bad : ℕ → Set Ω :=
    fun n => {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
                       - entropy μ (Xs 0)|} with hbad_def
  -- The typical event = complement of `bad n`. We rewrite the sum from
  -- `Finset.range n` (via `pmfLog ∘ Xs i`) to `Finset.univ` over `Fin n`
  -- (via `pmfLog ∘ jointRV Xs n`), which matches the typical-set definition.
  have h_event_eq : ∀ n, {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε} = (bad n)ᶜ := by
    intro n
    ext ω
    simp only [hbad_def, Set.mem_setOf_eq, Set.mem_compl_iff, mem_typicalSet_iff,
      not_le, jointRV_apply]
    -- ∑ i : Fin n, pmfLog … (Xs i ω) = ∑ i ∈ Finset.range n, logLikelihood μ Xs i ω
    have h_sum : (∑ i : Fin n, pmfLog μ Xs (Xs i ω))
        = ∑ i ∈ Finset.range n, logLikelihood μ Xs i ω :=
      Fin.sum_univ_eq_sum_range (fun i => pmfLog μ Xs (Xs i ω)) n
    rw [h_sum]
  -- Reduce to `μ (bad n) → 0`.
  have h_bad : Tendsto (fun n => μ (bad n)) atTop (𝓝 0) :=
    aep_inProbability μ Xs hXs hindep hident hε
  -- Each `bad n` is measurable.
  have h_meas_bad : ∀ n, MeasurableSet (bad n) := by
    intro n
    have h_sum_meas : Measurable
        (fun ω => ∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) :=
      Finset.measurable_sum _ fun i _ => measurable_logLikelihood μ Xs hXs i
    have h_div : Measurable
        (fun ω => (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n) :=
      h_sum_meas.div_const _
    have h_diff : Measurable
        (fun ω => (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n
                    - entropy μ (Xs 0)) :=
      h_div.sub_const _
    have h_abs : Measurable
        (fun ω => |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n
                    - entropy μ (Xs 0))|) :=
      _root_.continuous_abs.measurable.comp h_diff
    exact measurableSet_le measurable_const h_abs
  -- Pass from `μ (bad n) → 0` to `μ (bad n)ᶜ → 1`.
  have h_compl : Tendsto (fun n => μ (bad n)ᶜ) atTop (𝓝 1) := by
    have h_id : ∀ n, μ ((bad n)ᶜ) = 1 - μ (bad n) := by
      intro n
      rw [measure_compl (h_meas_bad n) (measure_ne_top μ _),
        measure_univ]
    refine Tendsto.congr (fun n => (h_id n).symm) ?_
    -- (1 - ·) is continuous on ℝ≥0∞, and `1 - 0 = 1`.
    have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
      ENNReal.continuous_sub_left (by simp)
    have h_step : Tendsto (fun n => (1 : ℝ≥0∞) - μ (bad n)) atTop
        (𝓝 ((1 : ℝ≥0∞) - 0)) := h_cont.tendsto _ |>.comp h_bad
    simpa using h_step
  -- Rewrite the goal via `h_event_eq`.
  refine Tendsto.congr (fun n => ?_) h_compl
  rw [h_event_eq n]

end InformationTheory.Shannon
