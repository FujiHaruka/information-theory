import Common2026.Shannon.Bridge
import Common2026.Shannon.Han
import Common2026.Shannon.Pi
import Common2026.Shannon.DPI
import Common2026.Shannon.SlepianWolf
import Common2026.Fano.Measure
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecificLimits.Basic

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

**仮定 `hpos`**: 教科書 statement (Cover-Thomas Theorem 3.1.2) は暗黙に
"support 全体" を仮定している。Mathlib `Real.log 0 = 0` 規約のもとでも、
サポート外点を含む typical block の card は和で評価できないため (`pmfLog x i = 0`
for `P(x_i) = 0` ⇒ $\exp(-\sum \text{pmfLog})$ が $P^n(x) = 0$ より厳密に大きくなり
下界として使えない)、`[∀ x, P(x) > 0]` を追加で受ける。 -/
theorem typicalSet_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ) ≤
      Real.exp ((n : ℝ) * (entropy μ (Xs 0) + ε)) := by
  -- Notation: write `P x := (μ.map (Xs 0)).real {x}` for the marginal pmf.
  set P : α → ℝ := fun x => (μ.map (Xs 0)).real {x} with hP_def
  -- Key fact 1: `pmfLog μ Xs x = -Real.log (P x)`, so `exp (-pmfLog μ Xs x) = P x`
  -- (using `hpos x` so `P x > 0` and `Real.exp_log` applies).
  have hP_pos : ∀ x, 0 < P x := hpos
  have hexp_pmfLog : ∀ x, Real.exp (-(pmfLog μ Xs x)) = P x := by
    intro x
    have : -(pmfLog μ Xs x) = Real.log (P x) := by
      simp [pmfLog, hP_def]
    rw [this, Real.exp_log (hP_pos x)]
  -- Key fact 2: `∑ x, P x = 1` (since `μ.map (Xs 0)` is a probability measure).
  have hMprob : IsProbabilityMeasure (μ.map (Xs 0)) :=
    Measure.isProbabilityMeasure_map (hXs 0).aemeasurable
  have hsum_P : (∑ x : α, P x) = 1 := by
    have h1 : (∑ x : α, P x) = (μ.map (Xs 0)).real (Finset.univ : Finset α) := by
      simp [hP_def, sum_measureReal_singleton]
    rw [h1]
    show (μ.map (Xs 0)).real ↑(Finset.univ : Finset α) = 1
    rw [Finset.coe_univ]
    exact probReal_univ
  -- Key fact 3: lower bound on `∏ i, P (x i)` for `x ∈ typicalSet`.
  -- From `x ∈ T_ε^n` we get `(∑ i, pmfLog μ Xs (x i)) / n - H < ε`,
  -- i.e. `∑ i, pmfLog μ Xs (x i) < n * (H + ε)` (when `n > 0`).
  -- Hence `exp (-(∑ i, pmfLog (x i))) > exp (-n * (H + ε))`, i.e.
  -- `∏ i, P (x i) ≥ exp (-n * (H + ε))`.
  set H : ℝ := entropy μ (Xs 0) with hH_def
  -- Bound the cardinality. Two cases: `n = 0` (trivial) and `n > 0` (main case).
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- n = 0: `Fin 0 → α` has a unique element, card ≤ 1 ≤ exp _.
    subst hn0
    have hcard_le : ((typicalSet μ Xs 0 ε).toFinite.toFinset.card : ℝ) ≤ 1 := by
      have h_le : (typicalSet μ Xs 0 ε).toFinite.toFinset.card ≤ 1 := by
        have h_sub : (typicalSet μ Xs 0 ε).toFinite.toFinset ⊆ (Finset.univ : Finset (Fin 0 → α)) :=
          fun x _ => Finset.mem_univ x
        calc (typicalSet μ Xs 0 ε).toFinite.toFinset.card
            ≤ (Finset.univ : Finset (Fin 0 → α)).card := Finset.card_le_card h_sub
          _ = Fintype.card (Fin 0 → α) := rfl
          _ = 1 := by rw [Fintype.card_fun, Fintype.card_fin]; simp
      exact_mod_cast h_le
    calc ((typicalSet μ Xs 0 ε).toFinite.toFinset.card : ℝ)
        ≤ 1 := hcard_le
      _ = Real.exp ((0 : ℕ) * (H + ε)) := by
          rw [Nat.cast_zero, zero_mul, Real.exp_zero]
  · -- n > 0: use the typical-set inequality.
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hnpos
    -- Step 1: lower bound on `∏ i, P (x i)` for `x ∈ T_ε^n`.
    have h_prod_lb : ∀ x ∈ (typicalSet μ Xs n ε).toFinite.toFinset,
        Real.exp (-((n : ℝ) * (H + ε))) ≤ ∏ i : Fin n, P (x i) := by
      intro x hx
      have hxT : x ∈ typicalSet μ Xs n ε :=
        (Set.Finite.mem_toFinset _).mp hx
      rw [mem_typicalSet_iff] at hxT
      -- Extract `(∑ i, pmfLog (x i)) / n < H + ε`.
      have hupper : (∑ i : Fin n, pmfLog μ Xs (x i)) / n - H < ε :=
        (abs_lt.mp hxT).2
      have hupper' : (∑ i : Fin n, pmfLog μ Xs (x i)) / n < H + ε := by linarith
      have hsum_lt : (∑ i : Fin n, pmfLog μ Xs (x i)) < (n : ℝ) * (H + ε) := by
        have := (div_lt_iff₀ hn_pos_R).mp hupper'
        linarith
      have hneg : -((n : ℝ) * (H + ε)) < -(∑ i : Fin n, pmfLog μ Xs (x i)) := by linarith
      -- `exp` is monotone.
      have hexp_lt : Real.exp (-((n : ℝ) * (H + ε)))
          < Real.exp (-(∑ i : Fin n, pmfLog μ Xs (x i))) := Real.exp_lt_exp.mpr hneg
      -- Rewrite RHS as `∏ i, P (x i)`.
      have h_rhs : Real.exp (-(∑ i : Fin n, pmfLog μ Xs (x i)))
          = ∏ i : Fin n, P (x i) := by
        rw [← Finset.sum_neg_distrib, Real.exp_sum]
        exact Finset.prod_congr rfl fun i _ => hexp_pmfLog (x i)
      rw [h_rhs] at hexp_lt
      exact hexp_lt.le
    -- Step 2: `∑ x ∈ T, ∏ i, P (x i) ≤ ∑ x : Fin n → α, ∏ i, P (x i) = 1`.
    have h_total : (∑ x : Fin n → α, ∏ i : Fin n, P (x i)) = 1 := by
      classical
      rw [← Fintype.piFinset_univ, Finset.sum_prod_piFinset]
      simp [hsum_P]
    have h_nonneg : ∀ x : Fin n → α, 0 ≤ ∏ i : Fin n, P (x i) := by
      intro x
      exact Finset.prod_nonneg (fun i _ => (hP_pos (x i)).le)
    have h_sum_T_le : (∑ x ∈ (typicalSet μ Xs n ε).toFinite.toFinset,
        ∏ i : Fin n, P (x i)) ≤ 1 := by
      calc (∑ x ∈ (typicalSet μ Xs n ε).toFinite.toFinset, ∏ i : Fin n, P (x i))
          ≤ ∑ x : Fin n → α, ∏ i : Fin n, P (x i) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro x _; exact Finset.mem_univ x
              · intro x _ _; exact h_nonneg x
        _ = 1 := h_total
    -- Step 3: `|T| · exp(-n(H+ε)) ≤ ∑ x ∈ T, ∏ i, P (x i) ≤ 1`.
    have h_card_lb : ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
        * Real.exp (-((n : ℝ) * (H + ε)))
        ≤ ∑ x ∈ (typicalSet μ Xs n ε).toFinite.toFinset, ∏ i : Fin n, P (x i) := by
      have h_const : (∑ _x ∈ (typicalSet μ Xs n ε).toFinite.toFinset,
            Real.exp (-((n : ℝ) * (H + ε))))
          = ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
              * Real.exp (-((n : ℝ) * (H + ε))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [← h_const]
      exact Finset.sum_le_sum h_prod_lb
    have h_combined : ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
        * Real.exp (-((n : ℝ) * (H + ε))) ≤ 1 := h_card_lb.trans h_sum_T_le
    -- Step 4: divide by `exp(-n(H+ε)) > 0`.
    have hexp_pos' : 0 < Real.exp ((n : ℝ) * (H + ε)) := Real.exp_pos _
    have h_rewrite : Real.exp (-((n : ℝ) * (H + ε)))
        = (Real.exp ((n : ℝ) * (H + ε)))⁻¹ := Real.exp_neg _
    rw [h_rewrite, mul_inv_le_iff₀ hexp_pos'] at h_combined
    linarith

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

/-! ### Phase D — 源符号化定理 weak converse

Phase D は source-coding converse (Cover-Thomas Theorem 5.4.1) を `Filter.liminf` 形で
立てる。Phase A〜C の `Pairwise IndepFun` 仮定では block entropy の `H(X^n) = n · H(X)`
が出ないため、Phase D は `iIndepFun` (mutual independence) を新規仮定として受ける。

詳細: [`docs/shannon/aep-source-coding-plan.md`](../../docs/shannon/aep-source-coding-plan.md).
-/

/-! #### Phase A補助 — i.i.d. block entropy chain rule -/

/-- 独立条件付き ⇒ `condEntropy = entropy`. `mutualInfo_eq_zero_iff_indep` +
`mutualInfo_eq_entropy_sub_condEntropy` の合成。 -/
lemma condEntropy_eq_entropy_of_indepFun
    {β : Type*} [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y)
    (hindep : IndepFun X Y μ) :
    InformationTheory.MeasureFano.condEntropy μ X Y = entropy μ X := by
  have h_bridge :
      (mutualInfo μ X Y).toReal
        = entropy μ X - InformationTheory.MeasureFano.condEntropy μ X Y :=
    mutualInfo_eq_entropy_sub_condEntropy μ X Y hX hY
  have h_zero : mutualInfo μ X Y = 0 :=
    (mutualInfo_eq_zero_iff_indep μ X Y hX hY).mpr hindep
  rw [h_zero, ENNReal.toReal_zero] at h_bridge
  linarith

/-- `IdentDistrib` ⇒ entropy 等. `μ.map X = ν.map Y` ⟹ pointwise singleton mass 等から
entropy の有限和定義が一致。 -/
lemma entropy_eq_of_identDistrib
    {Ω' : Type*} [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') (X : Ω → α) (Y : Ω' → α)
    (h : IdentDistrib X Y μ ν) :
    entropy μ X = entropy ν Y := by
  unfold entropy
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show (μ.map X).real {x} = (ν.map Y).real {x} from by rw [h.map_eq]]

/-- Block jointRV を `Fin n` 形に restrict した family. -/
private noncomputable def jointFamily (Xs : ℕ → Ω → α) (n : ℕ) : Fin n → Ω → α :=
  fun i ω => Xs i.val ω

private lemma measurable_jointFamily (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (n : ℕ) (i : Fin n) : Measurable (jointFamily Xs n i) := hXs i.val

/-- Independence of `Xs i` and the prefix `(Xs 0, ..., Xs (i-1))` from `iIndepFun`.
直接 `iIndepFun.indepFun_finset` を `S = {i}`, `T = Finset.range i` over `ℕ` で適用し、
両辺を `IndepFun.comp` で `Xs i` および `Fin i → α` 型に潰す。 -/
private lemma indepFun_Xs_prefix_of_iIndepFun
    (μ : Measure Ω)
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ) (i : ℕ) :
    IndepFun (Xs i) (fun ω (j : Fin i) => Xs j.val ω) μ := by
  -- Apply `iIndepFun.indepFun_finset` with `S = {i}`, `T = Finset.range i`.
  set S : Finset ℕ := {i} with hS_def
  set T : Finset ℕ := Finset.range i with hT_def
  have hST_disj : Disjoint S T := by
    rw [Finset.disjoint_singleton_left, Finset.mem_range]
    exact lt_irrefl i
  have h_pair_indep := hindep_full.indepFun_finset S T hST_disj hXs
  -- h_pair_indep : IndepFun (fun a (k : S) => Xs k.val a) (fun a (k : T) => Xs k.val a) μ.
  -- Project: S → Unit → α, T → Fin i → α via measurable functions.
  -- LHS projection: (S → α) → α, "evaluate at i".
  let projS : (S → α) → α := fun f => f ⟨i, Finset.mem_singleton.mpr rfl⟩
  have hprojS_meas : Measurable projS := by
    show Measurable (fun (f : S → α) => f ⟨i, _⟩)
    exact measurable_pi_apply _
  -- RHS projection: (T → α) → (Fin i → α) by reindexing.
  let projT : (T → α) → (Fin i → α) :=
    fun f j => f ⟨j.val, Finset.mem_range.mpr j.isLt⟩
  have hprojT_meas : Measurable projT := by
    refine measurable_pi_iff.mpr ?_
    intro j
    show Measurable (fun (f : T → α) => f ⟨j.val, _⟩)
    exact measurable_pi_apply _
  have h_lifted := h_pair_indep.comp hprojS_meas hprojT_meas
  -- h_lifted : IndepFun (projS ∘ ...) (projT ∘ ...) = IndepFun (Xs i) (fun ω j => Xs j.val ω).
  exact h_lifted

/-- **Pi 化 entropy chain rule for i.i.d. blocks**: `H(X^n) = n · H(X_0)`.

戦略 (Han 路線): `Han.jointEntropy_chain_rule` を `Fin n` 上で適用、各 summand
`condEntropy μ (X_i) prefix_i` を `condEntropy_eq_entropy_of_indepFun` で `entropy μ (X_i)`
に潰し、`entropy_eq_of_identDistrib` で `entropy μ (X_0)` に統一、`Finset.sum_const` で
`n · H(X_0)` を出す。 -/
theorem entropy_jointRV_eq_n_smul
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (n : ℕ) :
    entropy μ (jointRV Xs n) = (n : ℝ) * entropy μ (Xs 0) := by
  -- jointRV は jointFamily の joint と defeq.
  set F : Fin n → Ω → α := jointFamily Xs n with hF_def
  have hF_meas : ∀ i, Measurable (F i) := measurable_jointFamily Xs hXs n
  -- jointEntropy μ F = entropy μ (jointRV Xs n) by defeq.
  have h_je_eq : jointEntropy μ F = entropy μ (jointRV Xs n) := rfl
  -- Apply `jointEntropy_chain_rule`.
  have h_chain := jointEntropy_chain_rule μ F hF_meas
  -- 各 summand: condEntropy μ (F i) prefix_i = entropy μ (F i) (independence).
  have h_each : ∀ i : Fin n,
      InformationTheory.MeasureFano.condEntropy μ (F i)
          (fun ω (j : Fin i.val) => F ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        = entropy μ (Xs 0) := by
    intro i
    -- prefix is the tuple of `F j` for `j : Fin i.val` (which is `Xs j.val`).
    set prefix_i : Ω → (Fin i.val → α) :=
      fun ω j => F ⟨j.val, j.isLt.trans i.isLt⟩ ω with hprefix_def
    have hprefix_meas : Measurable prefix_i :=
      measurable_pi_iff.mpr fun j => hF_meas _
    -- prefix_i = fun ω j => Xs j.val ω (defeq via F = jointFamily).
    have hprefix_eq : prefix_i = fun ω (j : Fin i.val) => Xs j.val ω := rfl
    -- F i = Xs i.val (defeq).
    have hFi_eq : F i = Xs i.val := rfl
    -- Independence of F i and prefix_i.
    have h_FI_prefix : IndepFun (F i) prefix_i μ := by
      rw [hFi_eq, hprefix_eq]
      exact indepFun_Xs_prefix_of_iIndepFun μ Xs hXs hindep_full i.val
    -- Now condEntropy μ (F i) prefix_i = entropy μ (F i).
    have h_cond_eq :=
      condEntropy_eq_entropy_of_indepFun μ (F i) prefix_i (hF_meas i) hprefix_meas h_FI_prefix
    rw [h_cond_eq]
    -- entropy μ (F i) = entropy μ (Xs 0) via IdentDistrib.
    rw [hFi_eq]
    exact entropy_eq_of_identDistrib μ μ (Xs i.val) (Xs 0) (hident i.val)
  -- Combine: jointEntropy = ∑ i, H(Xs 0) = n · H(Xs 0).
  rw [← h_je_eq, h_chain]
  rw [Finset.sum_congr rfl (fun i _ => h_each i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! #### Phase B — per-n converse bound (Slepian-Wolf 流儀 4-step) -/

/-- per-n source coding converse bound:
`(n : ℝ) · H(Xs 0) ≤ log M + h(Pe_n) + Pe_n · n · log |α|`.

Slepian-Wolf converse 流儀の 4-step (entropy_le_log_card + bridge + DPI + Fano) を
`X^n := jointRV Xs n` 上で再演し、Phase A の `entropy_jointRV_eq_n_smul` で LHS を
`n · H(X_0)` に換算する。 -/
theorem source_coding_per_n_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α)
    (n : ℕ) (hn : 1 ≤ n)
    {M : ℕ} [NeZero M]
    (c : (Fin n → α) → Fin M)
    (d : Fin M → (Fin n → α)) :
    (n : ℝ) * entropy μ (Xs 0)
      ≤ Real.log (M : ℝ)
        + Real.binEntropy
            (InformationTheory.MeasureFano.errorProb μ
              (jointRV Xs n) (fun ω => c (jointRV Xs n ω)) d)
        + InformationTheory.MeasureFano.errorProb μ
            (jointRV Xs n) (fun ω => c (jointRV Xs n ω)) d
          * (n : ℝ) * Real.log (Fintype.card α) := by
  -- ## B.0 Setup
  set Xn : Ω → (Fin n → α) := jointRV Xs n with hXn_def
  set Yn : Ω → Fin M := fun ω => c (Xn ω) with hYn_def
  set Pe : ℝ := InformationTheory.MeasureFano.errorProb μ Xn Yn d with hPe_def
  have hXn_meas : Measurable Xn := measurable_jointRV Xs hXs n
  have hc_meas : Measurable c := measurable_of_countable _
  have hd_meas : Measurable d := measurable_of_countable _
  have hYn_meas : Measurable Yn := hc_meas.comp hXn_meas
  -- Pi 化 Fintype card 算: Fintype.card (Fin n → α) = (Fintype.card α)^n.
  have hcard_Pi : (Fintype.card (Fin n → α) : ℝ) = (Fintype.card α : ℝ)^n := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rfl
  -- Pi 化 alphabet で Fano が呼べる: 2 ≤ Fintype.card (Fin n → α).
  have hcard_Pi_ge_2 : 2 ≤ Fintype.card (Fin n → α) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    have h2n : 2 ≤ 2^n := by
      have : (2 : ℕ)^1 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
      simpa using this
    exact h2n.trans (Nat.pow_le_pow_left hcard n)
  -- ## B.1 Step A: entropy μ Yn ≤ log M.
  have hcard_Fin : (Fintype.card (Fin M) : ℝ) = (M : ℝ) := by rw [Fintype.card_fin]
  have h_step_A : entropy μ Yn ≤ Real.log (M : ℝ) := by
    have := entropy_le_log_card μ Yn hYn_meas
    rwa [hcard_Fin] at this
  -- ## B.2 Step B: I(Xn; Yn) ≤ entropy μ Yn  (= H(Yn) - H(Yn|Xn) ≤ H(Yn))
  have h_bridge_B :
      (mutualInfo μ Yn Xn).toReal
        = entropy μ Yn - InformationTheory.MeasureFano.condEntropy μ Yn Xn :=
    mutualInfo_eq_entropy_sub_condEntropy μ Yn Xn hYn_meas hXn_meas
  have h_comm_B : mutualInfo μ Xn Yn = mutualInfo μ Yn Xn :=
    mutualInfo_comm μ Xn Yn hXn_meas hYn_meas
  have h_step_B : (mutualInfo μ Xn Yn).toReal ≤ entropy μ Yn := by
    rw [h_comm_B, h_bridge_B]
    have h_nn := condEntropy_nonneg μ Yn Xn
    linarith
  -- ## B.3 Step C (skip): not needed in this assembly path; Fano applies directly to
  -- `condEntropy μ Xn Yn` with decoder `d`, no DPI postprocess needed.
  -- ## B.4 Step D: Fano on (Xn, d∘Yn) — `condEntropy μ Xn (d∘Yn)` bounded.
  -- Note: condEntropy is over the conditioner; we want a bound on `H(Xn | Yn)` via Fano.
  have h_step_D :
      InformationTheory.MeasureFano.condEntropy μ Xn Yn ≤
        Real.binEntropy Pe + Pe * Real.log ((Fintype.card (Fin n → α) : ℝ) - 1) := by
    have := InformationTheory.MeasureFano.fano_inequality_measure_theoretic
      μ Xn Yn d hXn_meas hYn_meas hd_meas hcard_Pi_ge_2
    exact this
  -- ## B.5 Step E: log ((|α|^n) - 1) ≤ n · log |α|.
  have hcard_pos : 0 < (Fintype.card α : ℝ) := by
    have : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast this
  have hcard_ge_one : 1 ≤ (Fintype.card α : ℝ) := by
    have : 1 ≤ Fintype.card α := Fintype.card_pos
    exact_mod_cast this
  have hcardPi_ge_one : 1 ≤ (Fintype.card α : ℝ)^n :=
    one_le_pow₀ hcard_ge_one
  have h_log_pow : Real.log ((Fintype.card (Fin n → α) : ℝ) - 1)
        ≤ (n : ℝ) * Real.log (Fintype.card α) := by
    rw [hcard_Pi]
    have h_le : (Fintype.card α : ℝ)^n - 1 ≤ (Fintype.card α : ℝ)^n := by linarith
    have h_nonneg_sub : 0 ≤ (Fintype.card α : ℝ)^n - 1 :=
      sub_nonneg.mpr hcardPi_ge_one
    rcases lt_or_eq_of_le h_nonneg_sub with hpos | hzero
    · calc Real.log ((Fintype.card α : ℝ)^n - 1)
          ≤ Real.log ((Fintype.card α : ℝ)^n) :=
            Real.log_le_log hpos h_le
        _ = (n : ℝ) * Real.log (Fintype.card α) := by
            rw [Real.log_pow]
    · rw [← hzero, Real.log_zero]
      have : 0 ≤ (n : ℝ) * Real.log (Fintype.card α) := by
        apply mul_nonneg (Nat.cast_nonneg n)
        exact Real.log_nonneg hcard_ge_one
      linarith
  -- ## B.6 Combine: H(X^n) = I(Xn; Yn) + H(Xn | Yn) ≤ log M + h(Pe) + Pe · n log |α|.
  have h_HXn_decomp :
      entropy μ Xn = (mutualInfo μ Xn Yn).toReal
        + InformationTheory.MeasureFano.condEntropy μ Xn Yn := by
    have h := mutualInfo_eq_entropy_sub_condEntropy μ Xn Yn hXn_meas hYn_meas
    linarith
  -- LHS = n · H(Xs 0) via Phase A.
  have h_LHS : (n : ℝ) * entropy μ (Xs 0) = entropy μ Xn := by
    rw [hXn_def]
    exact (entropy_jointRV_eq_n_smul μ Xs hXs hindep_full hident n).symm
  -- Pe ≥ 0 to push the Fano bound through monotonicity of `* log |α|`.
  have h_Pe_nn : 0 ≤ Pe := by
    rw [hPe_def, InformationTheory.MeasureFano.errorProb]
    exact measureReal_nonneg
  -- Pe * log(|α|^n - 1) ≤ Pe * n * log |α|.
  have h_Pe_mul : Pe * Real.log ((Fintype.card (Fin n → α) : ℝ) - 1)
      ≤ Pe * (n : ℝ) * Real.log (Fintype.card α) := by
    have := mul_le_mul_of_nonneg_left h_log_pow h_Pe_nn
    linarith [this]
  -- Final assembly: linarith on Steps A-E + decomp.
  rw [h_LHS, h_HXn_decomp]
  linarith [h_step_A, h_step_B, h_step_D, h_Pe_mul]

/-! #### Phase C — `Filter.liminf` 形主定理 -/

/-- **Source coding theorem, weak converse**:
For any block code `(c_n, d_n)` with `M_n` codewords and i.i.d. discrete source,
if the error probability vanishes then the rate is at least the entropy.

The boundedness assumption `hM_bdd` (rate bounded above) captures the practical
setting: it rules out the pathological case `M n` growing super-exponentially in
`n` (where `liminf log M_n / n` would collapse to junk in the conditionally
complete real lattice). For rate-bounded codes `M n = 2^⌈n R⌉` this is automatic
with `R'` any constant `> R`. -/
theorem source_coding_converse
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α)
    (M : ℕ → ℕ) [hM_pos : ∀ n, NeZero (M n)]
    (c : ∀ n, (Fin n → α) → Fin (M n))
    (d : ∀ n, Fin (M n) → (Fin n → α))
    (hPe_to_zero :
      Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
                          (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
              atTop (𝓝 0))
    (hM_bdd : ∃ R, ∀ n, Real.log (M n : ℝ) / n ≤ R) :
    entropy μ (Xs 0)
      ≤ Filter.liminf (fun n : ℕ => Real.log (M n : ℝ) / n) atTop := by
  set H : ℝ := entropy μ (Xs 0) with hH_def
  set Pe : ℕ → ℝ := fun n => InformationTheory.MeasureFano.errorProb μ
    (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n) with hPe_def
  -- δ_n := h(Pe_n) / n + Pe_n · log |α|.
  set δ : ℕ → ℝ := fun n => Real.binEntropy (Pe n) / n + Pe n * Real.log (Fintype.card α)
    with hδ_def
  -- (C.1) Tendsto δ atTop (𝓝 0).
  have h_binEntropy_tendsto : Tendsto (fun n => Real.binEntropy (Pe n)) atTop (𝓝 0) := by
    have := Real.binEntropy_continuous.tendsto 0
    rw [Real.binEntropy_zero] at this
    exact this.comp hPe_to_zero
  have h_one_div_n : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h_binEntropy_div : Tendsto (fun n => Real.binEntropy (Pe n) / n) atTop (𝓝 0) := by
    have hprod := h_binEntropy_tendsto.mul h_one_div_n
    simp only [mul_zero] at hprod
    have h_eq : ∀ n : ℕ, Real.binEntropy (Pe n) * (1 / (n : ℝ))
        = Real.binEntropy (Pe n) / n := fun n => by ring
    exact (Tendsto.congr h_eq hprod)
  have h_Pe_log : Tendsto (fun n => Pe n * Real.log (Fintype.card α)) atTop (𝓝 0) := by
    have h_const : Tendsto (fun _ : ℕ => Real.log (Fintype.card α)) atTop
        (𝓝 (Real.log (Fintype.card α))) := tendsto_const_nhds
    have hprod := hPe_to_zero.mul h_const
    simpa using hprod
  have h_δ : Tendsto δ atTop (𝓝 0) := by
    have h_add := h_binEntropy_div.add h_Pe_log
    simpa [δ] using h_add
  -- (C.2) per-n bound /n: H ≤ log M_n / n + δ_n eventually.
  have h_per_n : ∀ᶠ n in atTop, H ≤ Real.log (M n : ℝ) / n + δ n := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
    have h_bound := source_coding_per_n_bound μ Xs hXs hindep_full hident hcard n hn (c n) (d n)
    -- h_bound : n · H ≤ log M + h(Pe) + Pe · n · log |α|.
    -- divide by n.
    have hn_ne : (n : ℝ) ≠ 0 := hn_pos_R.ne'
    -- Divide h_bound by n.
    have h_div : H ≤
        (Real.log (M n : ℝ) + Real.binEntropy (Pe n)
          + Pe n * (n : ℝ) * Real.log (Fintype.card α)) / (n : ℝ) := by
      have := (div_le_div_iff_of_pos_right hn_pos_R).mpr h_bound
      have h_lhs : (n : ℝ) * H / (n : ℝ) = H := by field_simp
      rw [h_lhs] at this
      exact this
    -- Now expand the RHS.
    have h_target : (Real.log (M n : ℝ) + Real.binEntropy (Pe n)
        + Pe n * (n : ℝ) * Real.log (Fintype.card α)) / (n : ℝ)
        = Real.log (M n : ℝ) / n + δ n := by
      simp only [δ]
      field_simp
      ring
    linarith [h_target ▸ h_div]
  -- (C.3) Apply liminf_le_liminf via `H = liminf (H + 0)` + `(log M_n/n + δ_n) → ?`.
  -- Strategy: `H - δ_n ≤ log M_n / n` eventually, take liminf both sides.
  -- `liminf (H - δ_n) = H` since `(H - δ_n) → H`.
  have h_per_n' : ∀ᶠ n in atTop, H - δ n ≤ Real.log (M n : ℝ) / n := by
    filter_upwards [h_per_n] with n hn
    linarith
  have h_LHS_tendsto : Tendsto (fun n => H - δ n) atTop (𝓝 H) := by
    have := (tendsto_const_nhds (x := H) (f := atTop)).sub h_δ
    simpa using this
  have h_LHS_liminf : Filter.liminf (fun n => H - δ n) atTop = H :=
    h_LHS_tendsto.liminf_eq
  -- IsCoboundedUnder for log M_n / n: from `hM_bdd` (eventual upper bound R) we get
  -- frequent (in fact universal) `log M_n / n ≤ R`, hence `IsCoboundedUnder (· ≥ ·)`.
  obtain ⟨R, hR⟩ := hM_bdd
  have h_cobdd : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ => Real.log (M n : ℝ) / n) :=
    Filter.IsCoboundedUnder.of_frequently_le (a := R)
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hR))
  -- liminf monotone via `liminf_le_liminf`.
  have h_LHS_bdd : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => H - δ n) :=
    h_LHS_tendsto.isBoundedUnder_ge
  have h_liminf_mono :
      Filter.liminf (fun n => H - δ n) atTop ≤
        Filter.liminf (fun n : ℕ => Real.log (M n : ℝ) / n) atTop :=
    Filter.liminf_le_liminf h_per_n' h_LHS_bdd h_cobdd
  rw [h_LHS_liminf] at h_liminf_mono
  exact h_liminf_mono

/-! ### Phase E — 源符号化定理 achievability

Phase E は source-coding achievability (Cover-Thomas Theorem 5.4.2) を `Tendsto` 形で
立てる。`M_n := ⌈exp(n · R)⌉` を取り、typical set ↔ `Fin M_n` の bijection で encoder /
decoder を構成、`typicalSet_prob_tendsto_one` で error rate → 0、`Nat.le_ceil` /
`Nat.ceil_lt_add_one` の squeeze で `log M_n / n → R`。

詳細: [`docs/shannon/aep-achievability-plan.md`](../../docs/shannon/aep-achievability-plan.md).
-/

/-- The codebook size used in the achievability proof: `M_n := ⌈exp(n · R)⌉`. -/
noncomputable def codebookSize (R : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (Real.exp ((n : ℝ) * R))

/-- `M_n ≥ 1` (so `Fin M_n` is `Nonempty`). -/
lemma codebookSize_pos (R : ℝ) (n : ℕ) : 0 < codebookSize R n := by
  unfold codebookSize
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

instance codebookSize_neZero (R : ℝ) (n : ℕ) : NeZero (codebookSize R n) :=
  ⟨(codebookSize_pos R n).ne'⟩

/-- Cardinality of typical set is ≤ `M_n` (provided `H + ε ≤ R` and `hpos`). -/
lemma typicalSet_card_le_codebookSize
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε R : ℝ} (hε : 0 < ε) (h_le : entropy μ (Xs 0) + ε ≤ R) :
    (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n := by
  -- card ≤ exp(n(H+ε)) ≤ exp(nR) ≤ ⌈exp(nR)⌉ = M_n.
  have h_card_le_exp := typicalSet_card_le μ Xs hXs hpos n hε
  have h_mono_arg : (n : ℝ) * (entropy μ (Xs 0) + ε) ≤ (n : ℝ) * R := by
    exact mul_le_mul_of_nonneg_left h_le (Nat.cast_nonneg n)
  have h_exp_mono : Real.exp ((n : ℝ) * (entropy μ (Xs 0) + ε))
      ≤ Real.exp ((n : ℝ) * R) := Real.exp_le_exp.mpr h_mono_arg
  have h_chain : ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
      ≤ Real.exp ((n : ℝ) * R) := h_card_le_exp.trans h_exp_mono
  have h_le_ceil : Real.exp ((n : ℝ) * R) ≤ (codebookSize R n : ℝ) := by
    unfold codebookSize
    exact Nat.le_ceil _
  have h_card_le_R : ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
      ≤ (codebookSize R n : ℝ) := h_chain.trans h_le_ceil
  exact_mod_cast h_card_le_R

/-- The encoder: typical blocks → `Fin M_n` index, non-typical → 0. -/
noncomputable def aepEncoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ)
    (h_card_le : (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n) :
    (Fin n → α) → Fin (codebookSize R n) := by
  classical
  intro x
  by_cases hx : x ∈ (typicalSet μ Xs n ε).toFinite.toFinset
  · -- typical: equivFin index, cast into Fin M_n.
    exact Fin.castLE h_card_le ((typicalSet μ Xs n ε).toFinite.toFinset.equivFin ⟨x, hx⟩)
  · -- non-typical: default index 0.
    exact ⟨0, codebookSize_pos R n⟩

/-- The decoder: `Fin M_n` index → typical block (out of range → default). -/
noncomputable def aepDecoder
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ) :
    Fin (codebookSize R n) → (Fin n → α) := by
  classical
  intro k
  by_cases hk : k.val < (typicalSet μ Xs n ε).toFinite.toFinset.card
  · -- in range: pull back via equivFin.symm, then take subtype value.
    exact ((typicalSet μ Xs n ε).toFinite.toFinset.equivFin.symm ⟨k.val, hk⟩).val
  · -- out of range: arbitrary block.
    exact fun _ => Classical.arbitrary α

omit [MeasurableSingletonClass α] in
/-- **Round-trip lemma**: `d_n ∘ c_n = id` on typical set. -/
lemma aepDecoder_aepEncoder_of_mem_typicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ)
    (h_card_le : (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n)
    (x : Fin n → α) (hx : x ∈ typicalSet μ Xs n ε) :
    aepDecoder μ Xs n ε R (aepEncoder μ Xs n ε R h_card_le x) = x := by
  classical
  -- x is in toFinset via Set.Finite.mem_toFinset.
  have hxF : x ∈ (typicalSet μ Xs n ε).toFinite.toFinset :=
    (Set.Finite.mem_toFinset _).mpr hx
  -- Unfold encoder on the `hxF` branch.
  unfold aepEncoder
  rw [dif_pos hxF]
  -- The cast preserves val, so it lands in range; equivFin.symm undoes equivFin.
  set s : Finset (Fin n → α) := (typicalSet μ Xs n ε).toFinite.toFinset with hs_def
  set k0 : Fin s.card := s.equivFin ⟨x, hxF⟩ with hk0_def
  -- Note: `(Fin.castLE h_card_le k0).val = k0.val < s.card`.
  have hcast_val : (Fin.castLE h_card_le k0).val = k0.val := rfl
  have hk0_lt : k0.val < s.card := k0.isLt
  -- Now unfold decoder on the in-range branch.
  unfold aepDecoder
  rw [dif_pos (by rw [hcast_val]; exact hk0_lt)]
  -- Show s.equivFin.symm ⟨k0.val, _⟩ = ⟨x, hxF⟩ (subtype) then take .val.
  have hsymm : s.equivFin.symm ⟨k0.val, hk0_lt⟩ = ⟨x, hxF⟩ := by
    have h1 : s.equivFin.symm (s.equivFin ⟨x, hxF⟩) = ⟨x, hxF⟩ :=
      s.equivFin.symm_apply_apply ⟨x, hxF⟩
    -- s.equivFin ⟨x, hxF⟩ has the same .val as k0, hence the input subtypes match.
    have heq : (⟨k0.val, hk0_lt⟩ : Fin s.card) = s.equivFin ⟨x, hxF⟩ := by
      apply Fin.ext
      rfl
    rw [heq]; exact h1
  -- Conclude: target is `(s.equivFin.symm ⟨(Fin.castLE … k0).val, …⟩).val = x`.
  show ((s.equivFin.symm ⟨(Fin.castLE h_card_le k0).val, _⟩) : ↑s).val = x
  -- After rewriting `Fin.castLE` val, we can apply `hsymm`.
  have : ((s.equivFin.symm ⟨k0.val, hk0_lt⟩ : ↑s) : Fin n → α) = x := by
    rw [hsymm]
  exact this

/-! #### Phase B — error rate Tendsto -/

omit [MeasurableSingletonClass α] in
/-- error event ⊆ {jointRV Xs n ∉ typicalSet}. The orientation matches
`errorProb`: `Xs ω ≠ decoder (encoder (Xs ω))`. -/
lemma error_subset_compl_typicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (n : ℕ) (ε R : ℝ)
    (h_card_le : (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n) :
    {ω | jointRV Xs n ω
            ≠ aepDecoder μ Xs n ε R (aepEncoder μ Xs n ε R h_card_le (jointRV Xs n ω))}
      ⊆ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hmem
  apply hω
  exact (aepDecoder_aepEncoder_of_mem_typicalSet μ Xs n ε R h_card_le _ hmem).symm

/-- error rate → 0. -/
lemma aep_errorProb_tendsto_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε R : ℝ} (hε : 0 < ε) (h_le : entropy μ (Xs 0) + ε ≤ R) :
    Tendsto
      (fun n => InformationTheory.MeasureFano.errorProb μ
                  (jointRV Xs n)
                  (fun ω => aepEncoder μ Xs n ε R
                              (typicalSet_card_le_codebookSize μ Xs hXs hpos n hε h_le)
                              (jointRV Xs n ω))
                  (aepDecoder μ Xs n ε R))
      atTop (𝓝 0) := by
  -- Sandwich: 0 ≤ errorProb n ≤ μ.real { ω | jointRV Xs n ω ∉ typicalSet ... } → 0.
  set h_card : ∀ n, (typicalSet μ Xs n ε).toFinite.toFinset.card ≤ codebookSize R n :=
    fun n => typicalSet_card_le_codebookSize μ Xs hXs hpos n hε h_le with h_card_def
  -- Upper-bound: error event ⊆ ∁ typicalSet (orientation matches `errorProb`).
  have h_subset : ∀ n,
      {ω | jointRV Xs n ω
              ≠ aepDecoder μ Xs n ε R
                  ((fun ω => aepEncoder μ Xs n ε R (h_card n) (jointRV Xs n ω)) ω)}
        ⊆ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε} := by
    intro n
    exact error_subset_compl_typicalSet μ Xs n ε R (h_card n)
  -- typicalSet measurable, complement measurable.
  have h_meas_T : ∀ n, MeasurableSet {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε} := by
    intro n
    exact (measurable_jointRV Xs hXs n) (measurableSet_typicalSet μ Xs n ε)
  -- complement of typical
  have h_meas_comp : ∀ n, MeasurableSet {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε} := by
    intro n; exact (h_meas_T n).compl
  -- μ {ω | not in typicalSet} → 0 (from typicalSet_prob_tendsto_one).
  have h_compl_tendsto :
      Tendsto (fun n => (μ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}).toReal)
        atTop (𝓝 0) := by
    have h_pos := typicalSet_prob_tendsto_one μ Xs hXs hindep hident hε
    -- μ {... ∉ T} = 1 - μ {... ∈ T}, hence its toReal tends to 0.
    have h_id : ∀ n,
        μ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}
          = 1 - μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε} := by
      intro n
      have h_compl_eq :
          {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}
            = {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}ᶜ := rfl
      rw [h_compl_eq, measure_compl (h_meas_T n) (measure_ne_top μ _), measure_univ]
    -- toReal of the difference → 0.
    have h_toReal_tendsto :
        Tendsto (fun n => (1 - μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}).toReal)
          atTop (𝓝 0) := by
      have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
        ENNReal.continuous_sub_left (by simp)
      have h_step : Tendsto (fun n => (1 : ℝ≥0∞) -
            μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε}) atTop
          (𝓝 ((1 : ℝ≥0∞) - 1)) := h_cont.tendsto _ |>.comp h_pos
      simp only [tsub_self] at h_step
      have h_toReal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h_step
      simpa using h_toReal
    refine Tendsto.congr (fun n => ?_) h_toReal_tendsto
    rw [h_id n]
  -- errorProb n = μ.real {error event} ≤ μ.real {... ∉ T} which → 0.
  have h_error_le : ∀ n,
      InformationTheory.MeasureFano.errorProb μ
          (jointRV Xs n)
          (fun ω => aepEncoder μ Xs n ε R (h_card n) (jointRV Xs n ω))
          (aepDecoder μ Xs n ε R)
        ≤ (μ {ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}).toReal := by
    intro n
    unfold InformationTheory.MeasureFano.errorProb Measure.real
    exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (h_subset n))
  have h_error_nn : ∀ n,
      0 ≤ InformationTheory.MeasureFano.errorProb μ
            (jointRV Xs n)
            (fun ω => aepEncoder μ Xs n ε R (h_card n) (jointRV Xs n ω))
            (aepDecoder μ Xs n ε R) := by
    intro n
    unfold InformationTheory.MeasureFano.errorProb
    exact measureReal_nonneg
  exact squeeze_zero h_error_nn h_error_le h_compl_tendsto

/-! #### Phase C — rate Tendsto + main theorem -/

/-- `log M_n / n → R` (squeeze via `Nat.le_ceil` and `Nat.ceil_lt_add_one`). -/
lemma codebookSize_log_div_tendsto
    {R : ℝ} (hR : 0 < R) :
    Tendsto (fun n : ℕ => Real.log (codebookSize R n : ℝ) / n) atTop (𝓝 R) := by
  -- Lower bound: R ≤ log M_n / n (for n ≥ 1).
  -- Upper bound: log M_n / n ≤ log (exp(nR) + 1) / n → R.
  set f : ℕ → ℝ := fun n => Real.log (codebookSize R n : ℝ) / n with hf_def
  -- Show ∀ᶠ n in atTop, R ≤ f n ≤ log (exp(nR) + 1) / n.
  -- Lower: R ≤ log M_n / n.
  have h_lower : ∀ᶠ n in atTop, R ≤ f n := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
    have hexp_pos : 0 < Real.exp ((n : ℝ) * R) := Real.exp_pos _
    have h_le : Real.exp ((n : ℝ) * R) ≤ (codebookSize R n : ℝ) := by
      unfold codebookSize
      exact Nat.le_ceil _
    have h_log : Real.log (Real.exp ((n : ℝ) * R)) ≤ Real.log (codebookSize R n : ℝ) :=
      Real.log_le_log hexp_pos h_le
    rw [Real.log_exp] at h_log
    -- (n : ℝ) * R ≤ log (M_n) ⟹ R ≤ log (M_n) / n (n > 0).
    have h_div := (div_le_div_iff_of_pos_right hn_pos_R).mpr h_log
    have h_simp : (n : ℝ) * R / (n : ℝ) = R := by field_simp
    rw [h_simp] at h_div
    exact h_div
  -- Upper: f n ≤ log (exp(nR) + 1) / n.
  set g : ℕ → ℝ := fun n => Real.log (Real.exp ((n : ℝ) * R) + 1) / n with hg_def
  have h_upper : ∀ᶠ n in atTop, f n ≤ g n := by
    rw [Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
    have h_ceil_lt :
        (codebookSize R n : ℝ) < Real.exp ((n : ℝ) * R) + 1 := by
      unfold codebookSize
      exact Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h_ceil_pos : 0 < (codebookSize R n : ℝ) := by
      have := codebookSize_pos R n
      exact_mod_cast this
    have h_log_le :
        Real.log (codebookSize R n : ℝ) ≤ Real.log (Real.exp ((n : ℝ) * R) + 1) :=
      (Real.log_le_log h_ceil_pos h_ceil_lt.le)
    exact (div_le_div_iff_of_pos_right hn_pos_R).mpr h_log_le
  -- g n → R.
  -- log (exp(nR) + 1) = log (exp(nR) (1 + exp(-nR))) = nR + log (1 + exp(-nR)).
  -- so g n = R + log (1 + exp(-nR)) / n. Both R is constant, second → 0.
  have h_g_tendsto : Tendsto g atTop (𝓝 R) := by
    have h_eq : ∀ n : ℕ, 1 ≤ n →
        g n = R + Real.log (1 + Real.exp (-((n : ℝ) * R))) / n := by
      intro n hn
      have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
      have hnR_pos : 0 < Real.exp ((n : ℝ) * R) := Real.exp_pos _
      have h_inv : Real.exp ((n : ℝ) * R) + 1
          = Real.exp ((n : ℝ) * R) * (1 + Real.exp (-((n : ℝ) * R))) := by
        rw [mul_add, mul_one, ← Real.exp_add,
          show (((n : ℝ) * R) + -((n : ℝ) * R)) = 0 from by ring, Real.exp_zero]
      have h_inner_pos : 0 < 1 + Real.exp (-((n : ℝ) * R)) := by
        have := Real.exp_pos (-((n : ℝ) * R))
        linarith
      have h_log_mul : Real.log (Real.exp ((n : ℝ) * R) + 1)
          = (n : ℝ) * R + Real.log (1 + Real.exp (-((n : ℝ) * R))) := by
        rw [h_inv, Real.log_mul hnR_pos.ne' h_inner_pos.ne', Real.log_exp]
      show Real.log (Real.exp ((n : ℝ) * R) + 1) / n
        = R + Real.log (1 + Real.exp (-((n : ℝ) * R))) / n
      rw [h_log_mul, add_div]
      have h_div_n : (n : ℝ) * R / (n : ℝ) = R := by field_simp
      rw [h_div_n]
    -- Use squeeze on |g n - R| ≤ log 2 / n.
    -- Reduce target to: g n - R → 0, i.e. log(1 + exp(-nR))/n → 0.
    -- Direct sandwich: 0 ≤ log(1 + exp(-nR))/n ≤ log 2 / n.
    have h_bound_nn : ∀ n : ℕ, 1 ≤ n →
        0 ≤ Real.log (1 + Real.exp (-((n : ℝ) * R))) / n := by
      intro n hn
      have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
      have h_pos_exp : 0 < Real.exp (-((n : ℝ) * R)) := Real.exp_pos _
      have h_one_le : 1 ≤ 1 + Real.exp (-((n : ℝ) * R)) := by linarith
      have h_log_nn : 0 ≤ Real.log (1 + Real.exp (-((n : ℝ) * R))) :=
        Real.log_nonneg h_one_le
      exact div_nonneg h_log_nn hn_pos_R.le
    have h_bound : ∀ n : ℕ, 1 ≤ n →
        Real.log (1 + Real.exp (-((n : ℝ) * R))) / n ≤ Real.log 2 / n := by
      intro n hn
      have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn
      have h_exp_le_one : Real.exp (-((n : ℝ) * R)) ≤ 1 := by
        have hnR_nn : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg n) hR.le
        have : -((n : ℝ) * R) ≤ 0 := by linarith
        calc Real.exp (-((n : ℝ) * R))
            ≤ Real.exp 0 := Real.exp_le_exp.mpr this
          _ = 1 := Real.exp_zero
      have h_one_le : 1 ≤ 1 + Real.exp (-((n : ℝ) * R)) := by
        have := Real.exp_pos (-((n : ℝ) * R)); linarith
      have h_le_two : 1 + Real.exp (-((n : ℝ) * R)) ≤ 2 := by linarith
      have h_log_le_log2 : Real.log (1 + Real.exp (-((n : ℝ) * R))) ≤ Real.log 2 :=
        Real.log_le_log (by linarith) h_le_two
      exact div_le_div_of_nonneg_right h_log_le_log2 hn_pos_R.le
    -- Use squeeze on log(1 + exp(-nR))/n.
    have h_log2_div : Tendsto (fun n : ℕ => Real.log 2 / n) atTop (𝓝 0) := by
      have h_one_div : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h_mul := h_one_div.const_mul (Real.log 2)
      simp only [mul_zero] at h_mul
      refine Tendsto.congr (fun n => ?_) h_mul
      ring
    have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    have h_inner_tendsto :
        Tendsto (fun n : ℕ => Real.log (1 + Real.exp (-((n : ℝ) * R))) / n) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_log2_div
      · exact Filter.eventually_atTop.mpr ⟨1, fun n hn => h_bound_nn n hn⟩
      · exact Filter.eventually_atTop.mpr ⟨1, fun n hn => h_bound n hn⟩
    -- g n = R + (small term), and small → 0, so g → R + 0 = R.
    have h_step :
        Tendsto (fun n : ℕ => R + Real.log (1 + Real.exp (-((n : ℝ) * R))) / n) atTop
          (𝓝 (R + 0)) := tendsto_const_nhds.add h_inner_tendsto
    rw [add_zero] at h_step
    -- Congr g with this representation eventually.
    refine Tendsto.congr' ?_ h_step
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    refine ⟨1, fun n hn => ?_⟩
    exact (h_eq n hn).symm
  -- Squeeze: R ≤ f n ≤ g n eventually, R → R and g → R, hence f → R.
  have h_const : Tendsto (fun _ : ℕ => R) atTop (𝓝 R) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_const h_g_tendsto h_lower h_upper

/-- **Source coding theorem, achievability**:
For any rate `R > entropy μ (Xs 0)`, there exists a block code with rate `R` and
vanishing error. -/
theorem source_coding_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {R : ℝ} (hR : entropy μ (Xs 0) < R) :
    ∃ M : ℕ → ℕ, ∃ _hM_pos : ∀ n, 0 < M n,
    ∃ c : ∀ n, (Fin n → α) → Fin (M n),
    ∃ d : ∀ n, Fin (M n) → (Fin n → α),
      Tendsto (fun n => Real.log (M n : ℝ) / n) atTop (𝓝 R) ∧
      Tendsto
        (fun n => InformationTheory.MeasureFano.errorProb μ
                    (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
        atTop (𝓝 0) := by
  -- Take ε := (R - H) / 2, so H + ε < R (in particular H + ε ≤ R).
  set H : ℝ := entropy μ (Xs 0) with hH_def
  set ε : ℝ := (R - H) / 2 with hε_def
  have hε : 0 < ε := by simp only [hε_def]; linarith
  have h_le : H + ε ≤ R := by simp only [hε_def]; linarith
  -- R > 0: H ≥ 0 (entropy_nonneg) + R > H ≥ 0.
  have h_R_pos : 0 < R := by
    have hH_nn : 0 ≤ H := InformationTheory.Shannon.entropy_nonneg μ (Xs 0) (hXs 0)
    linarith
  -- Pairwise independence from iIndepFun.
  have hindep_pair : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j :=
    fun _ _ hij => hindep_full.indepFun hij
  -- Provide existentials.
  refine ⟨codebookSize R, fun n => codebookSize_pos R n,
    fun n => aepEncoder μ Xs n ε R
                (typicalSet_card_le_codebookSize μ Xs hXs hpos n hε h_le),
    fun n => aepDecoder μ Xs n ε R, ?_, ?_⟩
  · exact codebookSize_log_div_tendsto h_R_pos
  · exact aep_errorProb_tendsto_zero μ Xs hXs hpos hindep_pair hident hε h_le

/-! ### Phase F — Unified source coding theorem (両側等号)

Combining Phase D (weak converse) and Phase E (achievability) yields
`sInf (achievableRates μ Xs) = entropy μ (Xs 0)`. An "achievable code" is a family
`(M_n, c_n, d_n)` whose error probability vanishes and whose rate `log M_n / n`
is universally bounded (the `hM_bdd` hypothesis of Phase D). The achievability
witnesses produced by Phase E satisfy this universally-bounded condition because
`Tendsto rate atTop (𝓝 R)` implies `BddAbove (Set.range rate)`
(`Filter.Tendsto.bddAbove_range`).
-/

/-- An achievable block source code: each `M_n > 0`, error probability vanishes,
and the rate is universally bounded. -/
structure IsAchievableCode
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (M : ℕ → ℕ)
    (c : ∀ n, (Fin n → α) → Fin (M n))
    (d : ∀ n, Fin (M n) → (Fin n → α)) : Prop where
  hM_pos : ∀ n, NeZero (M n)
  hPe_to_zero :
    Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
              (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
            atTop (𝓝 0)
  hM_bdd : ∃ R, ∀ n, Real.log (M n : ℝ) / n ≤ R

/-- The set of asymptotic rates (`liminf log M_n / n`) of achievable codes. -/
noncomputable def achievableRates
    (μ : Measure Ω) (Xs : ℕ → Ω → α) : Set ℝ :=
  { r | ∃ (M : ℕ → ℕ) (c : ∀ n, (Fin n → α) → Fin (M n))
        (d : ∀ n, Fin (M n) → (Fin n → α)),
        IsAchievableCode μ Xs M c d ∧
        Filter.liminf (fun n : ℕ => Real.log (M n : ℝ) / n) atTop = r }

/-- (Phase D lifted) Every achievable rate is at least the entropy. -/
theorem entropy_le_of_mem_achievableRates
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α)
    {r : ℝ} (hr : r ∈ achievableRates μ Xs) :
    entropy μ (Xs 0) ≤ r := by
  obtain ⟨M, c, d, hAch, hlim⟩ := hr
  haveI : ∀ n, NeZero (M n) := hAch.hM_pos
  rw [← hlim]
  exact source_coding_converse μ Xs hXs hindep_full hident hcard M c d
    hAch.hPe_to_zero hAch.hM_bdd

/-- (Phase E lifted) Any rate strictly above the entropy is achievable. -/
theorem mem_achievableRates_of_gt_entropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {R : ℝ} (hR : entropy μ (Xs 0) < R) :
    R ∈ achievableRates μ Xs := by
  obtain ⟨M, hM_pos, c, d, hRate, hPe⟩ :=
    source_coding_achievability μ Xs hXs hpos hindep_full hident hR
  refine ⟨M, c, d, ⟨fun n => ⟨(hM_pos n).ne'⟩, hPe, ?_⟩, hRate.liminf_eq⟩
  -- hM_bdd: Tendsto rate (𝓝 R) ⟹ BddAbove (Set.range rate) ⟹ ∃ R', ∀ n, rate n ≤ R'.
  obtain ⟨R', hR'⟩ := hRate.bddAbove_range
  exact ⟨R', fun n => hR' (Set.mem_range_self n)⟩

/-- **Source coding theorem (両側等号)**:
The infimum of asymptotic rates of achievable block source codes equals the
entropy of the source. -/
theorem source_coding_theorem
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α) :
    sInf (achievableRates μ Xs) = entropy μ (Xs 0) := by
  set H : ℝ := entropy μ (Xs 0) with hH_def
  -- Lower bound H is a lower bound for achievableRates.
  have h_lb : ∀ r ∈ achievableRates μ Xs, H ≤ r := fun r hr =>
    entropy_le_of_mem_achievableRates μ Xs hXs hindep_full hident hcard hr
  have h_bddBelow : BddBelow (achievableRates μ Xs) := ⟨H, h_lb⟩
  -- Achievability gives nonemptyness (use R = H + 1).
  have h_nonempty : (achievableRates μ Xs).Nonempty :=
    ⟨H + 1, mem_achievableRates_of_gt_entropy μ Xs hXs hpos hindep_full hident
      (by linarith : H < H + 1)⟩
  apply le_antisymm
  · -- sInf ≤ H: for every a > H, a ∈ achievableRates ⟹ sInf ≤ a; dense argument.
    refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
    exact csInf_le_of_le h_bddBelow
      (mem_achievableRates_of_gt_entropy μ Xs hXs hpos hindep_full hident ha) le_rfl
  · -- H ≤ sInf: H is a lower bound and achievableRates is nonempty.
    exact le_csInf h_nonempty h_lb

end InformationTheory.Shannon
