import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Bridge
import InformationTheory.Shannon.Han.Basic
import InformationTheory.Shannon.Pi
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.SlepianWolf.Basic
import InformationTheory.Fano.Measure
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecificLimits.Basic

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

@[entry_point]
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
@[entry_point]
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
@[entry_point]
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
@[entry_point]
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
@[entry_point]
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
@[entry_point]
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
