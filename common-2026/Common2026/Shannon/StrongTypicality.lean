import Common2026.Shannon.AEP
import Common2026.Shannon.Sanov
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Strong typicality (E-7) — Cover-Thomas 11.2

シードカード E-7 ([`docs/shannon/strong-typicality-plan.md`](../../docs/shannon/strong-typicality-plan.md))。
Cover-Thomas Theorem 11.2 — strongly typical set

  `A^{*n}_ε := { x : Fin n → α | ∀ a, |(N(a|x^n) : ℝ)/n - P(a)| ≤ ε }`

の 3 主定理:
1. `stronglyTypicalSet_prob_tendsto_one`: `μ {ω | jointRV ∈ A^*} → 1` (WLLN on indicators).
2. `stronglyTypicalSet_card_le`: `|A^*| ≤ exp(n(H + ε·L))` (Strong ⊆ Weak typical 経由).
3. `stronglyTypicalSet_card_ge_eventually`: `∃ N, ∀ n ≥ N, (1-η)·exp(n(H - ε·L)) ≤ |A^*|`.

ここで `L := ∑ a, |log P(a)|` (`logSumAbs μ Xs`)、`N(a|x^n) := typeCount x a`、
`P(a) := (μ.map (Xs 0)).real {a}`、`H := entropy μ (Xs 0)`。

## 設計メモ

* 既存 weak typicality (`AEP.lean`、1599 行) と並立。Strong ⟹ Weak (with `ε·L`) を
  Phase 3 bridge で示し、Phase 4 size bound は weak typical の既存 bound を呼ぶだけ。
* WLLN は per-letter indicator `Y_a i ω := 𝟙(Xs i ω = a)` に `strong_law_ae_real` を
  letter 毎に n 本回し、`α` 有限の union bound で「全 letter 同時に concentration」を得る。
* `α` generic — `α := α' × β` で instantiate すれば joint strong typical 形が得られる
  (E-5 Slepian–Wolf achievability 前段で再利用可能、本 plan では single-variable 形のみ)。
* full support `hpos : ∀ a, 0 < P(a)` は size bound の Phase 3 bridge で必須
  (`L = ∑ a, |log P(a)|` の有限性 + Phase G `typicalSet_prob_le` の `hpos` 仮定)。
  prob_tendsto_one (Phase 2) には `hpos` 不要。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Real
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Phase 1 — `stronglyTypicalSet` 定義 -/

/-- **Strongly typical set** (Cover-Thomas 11.2):
`A^*_ε^n := { x : Fin n → α | ∀ a, |(typeCount x a : ℝ)/n - P(a)| ≤ ε }`. -/
noncomputable def stronglyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    Set (Fin n → α) :=
  { x | ∀ a : α,
      |(typeCount x a : ℝ) / n - (μ.map (Xs 0)).real {a}| ≤ ε }

lemma mem_stronglyTypicalSet_iff
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) (x : Fin n → α) :
    x ∈ stronglyTypicalSet μ Xs n ε ↔
      ∀ a : α, |(typeCount x a : ℝ) / n - (μ.map (Xs 0)).real {a}| ≤ ε := Iff.rfl

/-- Measurability of the strongly typical set (finite ambient). -/
theorem measurableSet_stronglyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    MeasurableSet (stronglyTypicalSet μ Xs n ε) :=
  (Set.toFinite _).measurableSet

/-! ### Phase 2 — `stronglyTypicalSet_prob_tendsto_one` — WLLN on indicators -/

/-- Letter-indicator: `letterIndicator Xs a i ω = 1 if Xs i ω = a else 0`. -/
noncomputable def letterIndicator (Xs : ℕ → Ω → α) (a : α) (i : ℕ) : Ω → ℝ :=
  fun ω => if Xs i ω = a then (1 : ℝ) else 0

lemma measurable_letterIndicator
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (a : α) (i : ℕ) :
    Measurable (letterIndicator Xs a i) := by
  unfold letterIndicator
  exact Measurable.ite (hXs i (measurableSet_singleton a)) measurable_const measurable_const

/-- For each fixed `a`, the indicator sequence `(letterIndicator Xs a i)_i` is pairwise
independent given the same for `Xs`. -/
lemma indepFun_letterIndicator
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) (a : α) :
    Pairwise fun i j =>
      letterIndicator Xs a i ⟂ᵢ[μ] letterIndicator Xs a j := by
  intro i j hij
  -- letterIndicator Xs a i = (fun x => if x = a then 1 else 0) ∘ (Xs i)
  set f : α → ℝ := fun x => if x = a then (1 : ℝ) else 0 with hf_def
  have hf_meas : Measurable f := measurable_of_finite _
  have h := (hindep hij).comp hf_meas hf_meas
  exact h

/-- For each fixed `a`, the indicator sequence `(letterIndicator Xs a i)_i` is
identically distributed when `Xs` is. -/
lemma identDistrib_letterIndicator
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (a : α) (i : ℕ) :
    IdentDistrib (letterIndicator Xs a i) (letterIndicator Xs a 0) μ μ := by
  set f : α → ℝ := fun x => if x = a then (1 : ℝ) else 0 with hf_def
  have hf_meas : Measurable f := measurable_of_finite _
  -- letterIndicator Xs a i = f ∘ Xs i
  exact (hident i).comp hf_meas

/-- The expected value of `letterIndicator Xs a 0` under `μ` equals `P(a)`. -/
lemma integral_letterIndicator
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (a : α) :
    ∫ ω, letterIndicator Xs a 0 ω ∂μ = (μ.map (Xs 0)).real {a} := by
  -- Push forward via Xs 0.
  set f : α → ℝ := fun x => if x = a then (1 : ℝ) else 0 with hf_def
  have hf_meas : Measurable f := measurable_of_finite _
  have h_push : ∫ ω, letterIndicator Xs a 0 ω ∂μ
      = ∫ x, f x ∂(μ.map (Xs 0)) := by
    rw [integral_map (hXs 0).aemeasurable hf_meas.aestronglyMeasurable]
    rfl
  rw [h_push]
  -- ∫ x, f x = ∑ x, P(x) · f(x) on a finite space.
  rw [integral_fintype (μ := μ.map (Xs 0)) Integrable.of_finite]
  -- ∑ x, P(x) · f(x) — only the `x = a` term survives.
  have h_sum :
      (∑ x : α, (μ.map (Xs 0)).real {x} • f x)
        = (μ.map (Xs 0)).real {a} := by
    rw [show (∑ x : α, (μ.map (Xs 0)).real {x} • f x)
          = (μ.map (Xs 0)).real {a} • f a + 0 from by
          rw [Finset.sum_eq_single a]
          · simp [hf_def, smul_eq_mul]
          · intro b _ hba
            simp [hf_def, hba, smul_eq_mul]
          · intro h_notin
            exact absurd (Finset.mem_univ a) h_notin]
    simp [hf_def, smul_eq_mul]
  exact h_sum

/-- Integrability of `letterIndicator a 0` on a probability measure (it is bounded). -/
lemma integrable_letterIndicator
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (a : α) :
    Integrable (letterIndicator Xs a 0) μ := by
  -- The indicator is bounded (∈ {0, 1}), hence integrable on a probability measure.
  refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1) ?_ ?_
  · exact (measurable_letterIndicator Xs hXs a 0).aestronglyMeasurable
  · filter_upwards with ω
    unfold letterIndicator
    split_ifs <;> simp

/-- Per-letter empirical-mean identity: for `x : Fin n → α`,
`(typeCount x a : ℝ) / n = (1/n) · ∑ i : Fin n, indicator(x_i = a)`. -/
lemma typeCount_eq_sum_indicator
    {n : ℕ} (x : Fin n → α) (a : α) :
    (typeCount x a : ℝ) = ∑ i : Fin n, if x i = a then (1 : ℝ) else 0 := by
  unfold typeCount
  classical
  rw [show (∑ i : Fin n, if x i = a then (1 : ℝ) else 0)
        = ∑ i ∈ (Finset.univ.filter fun i : Fin n => x i = a), (1 : ℝ) from by
        rw [← Finset.sum_filter]]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- WLLN for per-letter indicators: `μ {ω | |.../n - P(a)| > ε} → 0`. -/
lemma letterIndicator_inProbability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (a : α) {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | ε ≤ |(∑ i ∈ Finset.range n, letterIndicator Xs a i ω) / n
                              - (μ.map (Xs 0)).real {a}|})
      atTop (𝓝 0) := by
  -- Apply strong_law_ae_real then tendstoInMeasure_of_tendsto_ae.
  have hint : Integrable (letterIndicator Xs a 0) μ :=
    integrable_letterIndicator μ Xs hXs a
  have hindLI : Pairwise fun i j =>
      letterIndicator Xs a i ⟂ᵢ[μ] letterIndicator Xs a j :=
    indepFun_letterIndicator μ Xs hXs hindep a
  have hidLI : ∀ i, IdentDistrib (letterIndicator Xs a i)
      (letterIndicator Xs a 0) μ μ :=
    fun i => identDistrib_letterIndicator μ Xs hident a i
  have h_lln := strong_law_ae_real (letterIndicator Xs a) hint hindLI hidLI
  have h_int_eq := integral_letterIndicator μ Xs hXs a
  -- a.s. convergence with constant limit P(a).
  have h_ae : ∀ᵐ ω ∂μ,
      Tendsto
        (fun n : ℕ => (∑ i ∈ Finset.range n, letterIndicator Xs a i ω) / n)
        atTop (𝓝 ((μ.map (Xs 0)).real {a})) := by
    filter_upwards [h_lln] with ω hω
    simpa [h_int_eq] using hω
  -- Convergence in measure via tendstoInMeasure_of_tendsto_ae.
  set f : ℕ → Ω → ℝ :=
    fun n ω => (∑ i ∈ Finset.range n, letterIndicator Xs a i ω) / n with hf_def
  set g : Ω → ℝ := fun _ => (μ.map (Xs 0)).real {a} with hg_def
  have h_meas_f : ∀ n, AEStronglyMeasurable (f n) μ := by
    intro n
    have h_sum_meas : Measurable
        (fun ω => ∑ i ∈ Finset.range n, letterIndicator Xs a i ω) :=
      Finset.measurable_sum _ fun i _ => measurable_letterIndicator Xs hXs a i
    have h_meas : Measurable (f n) := by
      change Measurable (fun ω => (∑ i ∈ Finset.range n, letterIndicator Xs a i ω) / n)
      exact h_sum_meas.div_const _
    exact h_meas.aestronglyMeasurable
  have h_inm : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_ae h_meas_f h_ae
  rw [tendstoInMeasure_iff_dist] at h_inm
  have h_target := h_inm ε hε
  refine Tendsto.congr (fun n => ?_) h_target
  apply congrArg μ
  ext ω
  show ε ≤ dist (f n ω) (g ω) ↔ ε ≤ |f n ω - g ω|
  rw [Real.dist_eq]

/-- **Strong typicality probability tendsto one**: for `Xs` i.i.d. with finite alphabet,
`μ {ω | jointRV Xs n ω ∈ A^*_ε^n} → 1`. -/
theorem stronglyTypicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε})
      atTop (𝓝 1) := by
  classical
  -- Strategy:
  --   bad_a n := {ω | ε ≤ |(1/n) ∑ Y_a i ω - P(a)|} → 0 (per-letter WLLN)
  --   bad n := ⋃ a, bad_a n → 0 (finite union over α)
  --   good n := (bad n)ᶜ = {ω | ∀ a, |.../n - P(a)| < ε}  ⊆ stronglyTypicalSet (with ≤)
  -- Then μ (good n) = 1 - μ (bad n) → 1.
  set P : α → ℝ := fun a => (μ.map (Xs 0)).real {a} with hP_def
  -- Per-letter "bad" event.
  set bad_a : α → ℕ → Set Ω :=
    fun a n => {ω | ε ≤ |(∑ i ∈ Finset.range n, letterIndicator Xs a i ω) / n - P a|}
      with hbad_a_def
  -- Each bad_a a n → 0.
  have h_bad_a : ∀ a, Tendsto (fun n : ℕ => μ (bad_a a n)) atTop (𝓝 0) :=
    fun a => letterIndicator_inProbability μ Xs hXs hindep hident a hε
  -- Each bad_a a n is measurable (for the union-bound sum).
  have h_meas_bad_a : ∀ a n, MeasurableSet (bad_a a n) := by
    intro a n
    have h_sum_meas : Measurable
        (fun ω => ∑ i ∈ Finset.range n, letterIndicator Xs a i ω) :=
      Finset.measurable_sum _ fun i _ => measurable_letterIndicator Xs hXs a i
    have h_diff : Measurable
        (fun ω => (∑ i ∈ Finset.range n, letterIndicator Xs a i ω) / n - P a) :=
      (h_sum_meas.div_const _).sub_const _
    have h_abs : Measurable
        (fun ω => |(∑ i ∈ Finset.range n, letterIndicator Xs a i ω) / n - P a|) :=
      (Measurable.abs (f := fun ω => (∑ i ∈ Finset.range n, letterIndicator Xs a i ω) / n - P a)
        h_diff)
    exact h_abs measurableSet_Ici
  -- Union bound: μ (⋃ a, bad_a a n) ≤ ∑ a, μ (bad_a a n) → 0.
  set bad : ℕ → Set Ω := fun n => ⋃ a : α, bad_a a n with hbad_def
  have h_meas_bad : ∀ n, MeasurableSet (bad n) := by
    intro n
    exact MeasurableSet.iUnion fun a => h_meas_bad_a a n
  have h_bad_le : ∀ n, μ (bad n) ≤ ∑ a : α, μ (bad_a a n) := by
    intro n
    -- measure_iUnion_fintype_le or measure_biUnion_finset_le
    exact (MeasureTheory.measure_iUnion_fintype_le μ (fun a => bad_a a n))
  -- ∑ a, μ (bad_a a n) → 0 (finite sum of sequences each → 0).
  have h_sum_tendsto : Tendsto (fun n : ℕ => ∑ a : α, μ (bad_a a n)) atTop (𝓝 0) := by
    have h_tend_sum : Tendsto (fun n : ℕ => ∑ a : α, μ (bad_a a n)) atTop
        (𝓝 (∑ a : α, (0 : ℝ≥0∞))) :=
      tendsto_finsetSum (Finset.univ : Finset α) fun a _ => h_bad_a a
    simpa using h_tend_sum
  have h_bad_tendsto : Tendsto (fun n : ℕ => μ (bad n)) atTop (𝓝 0) := by
    -- Sandwich: 0 ≤ μ (bad n) ≤ ∑ a, μ (bad_a a n) → 0.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := (0 : ℝ≥0∞))) h_sum_tendsto ?_ ?_
    · refine Filter.Eventually.of_forall (fun n : ℕ => ?_)
      show (0 : ℝ≥0∞) ≤ μ (bad n)
      exact bot_le
    · exact Filter.Eventually.of_forall (fun n => h_bad_le n)
  -- Subset: good n ⊆ {ω | jointRV ∈ stronglyTypicalSet}.
  have h_subset : ∀ n, (bad n)ᶜ ⊆ {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε} := by
    intro n ω hω
    simp only [hbad_def, Set.mem_compl_iff, Set.mem_iUnion, not_exists, hbad_a_def,
      Set.mem_setOf_eq, not_le] at hω
    -- hω : ∀ a, |.../n - P a| < ε
    show jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε
    rw [mem_stronglyTypicalSet_iff]
    intro a
    -- (typeCount (jointRV ω) a : ℝ)/n = (∑ i : Fin n, indicator)/n = (∑ i ∈ range n, indicator)/n
    have h_eq : (typeCount (jointRV Xs n ω) a : ℝ) / n
        = (∑ i ∈ Finset.range n, letterIndicator Xs a i ω) / n := by
      congr 1
      rw [typeCount_eq_sum_indicator]
      -- ∑ i : Fin n, (if jointRV Xs n ω i = a ...) = ∑ i ∈ range n, letterIndicator Xs a i ω
      have h_jr : ∀ i : Fin n,
          (if jointRV Xs n ω i = a then (1 : ℝ) else 0)
            = letterIndicator Xs a i.val ω := by
        intro i
        unfold letterIndicator
        rfl
      rw [show (∑ i : Fin n, if jointRV Xs n ω i = a then (1 : ℝ) else 0)
          = ∑ i : Fin n, letterIndicator Xs a i.val ω from
            Finset.sum_congr rfl fun i _ => h_jr i]
      exact Fin.sum_univ_eq_sum_range (fun i => letterIndicator Xs a i ω) n
    rw [h_eq]
    exact (hω a).le
  -- Measure-monotone: μ (good n) ≥ μ ((bad n)ᶜ).
  -- Actually, μ (good n) = μ ({ω | jointRV ∈ stronglyTypicalSet}).
  -- We have μ (good n) ≥ 1 - μ (bad n) and ≤ 1 (probability), then squeeze.
  have h_event_meas : ∀ n,
      MeasurableSet {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε} := by
    intro n
    exact (measurable_jointRV Xs hXs n) (measurableSet_stronglyTypicalSet μ Xs n ε)
  have h_one_sub : ∀ n,
      μ (bad n)ᶜ = 1 - μ (bad n) := by
    intro n
    rw [MeasureTheory.prob_compl_eq_one_sub (h_meas_bad n)]
  -- μ (jointRV ∈ stronglyTypicalSet) ≥ μ ((bad n)ᶜ) = 1 - μ (bad n).
  have h_ge : ∀ n, 1 - μ (bad n)
      ≤ μ {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε} := by
    intro n
    rw [← h_one_sub n]
    exact measure_mono (h_subset n)
  -- μ (jointRV ∈ stronglyTypicalSet) ≤ 1.
  have h_le : ∀ n, μ {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε} ≤ 1 :=
    fun n => prob_le_one
  -- Sandwich.
  -- ENNReal subtraction is not continuous in general, but `(1 : ℝ≥0∞) - · ` is continuous
  -- at `0` because `μ (bad n) → 0` lives in `[0, 1]` where subtraction is continuous.
  -- Use `ENNReal.Tendsto.const_sub`.
  have h_bad_ne_top : ∀ n, μ (bad n) ≠ ∞ := fun n => measure_ne_top _ _
  have h_sub_tendsto : Tendsto (fun n : ℕ => (1 : ℝ≥0∞) - μ (bad n)) atTop (𝓝 (1 - 0)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds h_bad_tendsto (Or.inr (by simp))
  rw [tsub_zero] at h_sub_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_sub_tendsto
    (tendsto_const_nhds (x := (1 : ℝ≥0∞))) ?_ ?_
  · exact Filter.Eventually.of_forall h_ge
  · exact Filter.Eventually.of_forall h_le

/-! ### Phase 3 — Strong ⟹ Weak typical (bridge identity) -/

/-- `logSumAbs μ Xs := ∑ a, |log P(a)|` — the "Lipschitz constant" of the
strong-to-weak typicality bridge. Finite for any finite alphabet. -/
noncomputable def logSumAbs (μ : Measure Ω) (Xs : ℕ → Ω → α) : ℝ :=
  ∑ a : α, |Real.log ((μ.map (Xs 0)).real {a})|

lemma logSumAbs_nonneg (μ : Measure Ω) (Xs : ℕ → Ω → α) :
    0 ≤ logSumAbs μ Xs :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- **Key bridge identity**: for `x : Fin n → α` with `n > 0`,
`(∑ i, pmfLog (x i))/n - H = ∑ a, (P(a) - (typeCount x a)/n) · log P(a)`.

This rewrites the "weak typicality" displacement as a sum of "strong typicality"
per-letter displacements, weighted by `log P(a)`. -/
lemma weak_displacement_eq_strong_sum
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {n : ℕ} (hn : 0 < n) (x : Fin n → α) :
    (∑ i : Fin n, pmfLog μ Xs (x i)) / n - entropy μ (Xs 0)
      = ∑ a : α,
          ((μ.map (Xs 0)).real {a} - (typeCount x a : ℝ) / n)
            * Real.log ((μ.map (Xs 0)).real {a}) := by
  classical
  set P : α → ℝ := fun a => (μ.map (Xs 0)).real {a} with hP_def
  -- Step 1: aggregate ∑ i, pmfLog (x i) = -∑ a, (typeCount x a) · log P(a).
  have h_pmfLog_eq : ∀ a : α, pmfLog μ Xs a = -Real.log (P a) := by
    intro a
    show (-Real.log ((μ.map (Xs 0)).real {a})) = -Real.log (P a)
    rfl
  -- Use sum_fiberwise: ∑ i, f (x i) = ∑ a, (typeCount x a) · f a, with f a := -log P a.
  set f : α → ℝ := fun a => -Real.log (P a) with hf_def
  have h_agg : (∑ i : Fin n, pmfLog μ Xs (x i)) = ∑ a : α, (typeCount x a : ℝ) * f a := by
    have h_pmf_eq_f : ∀ i, pmfLog μ Xs (x i) = f (x i) := fun i => h_pmfLog_eq (x i)
    rw [show (∑ i : Fin n, pmfLog μ Xs (x i)) = ∑ i : Fin n, f (x i) from
          Finset.sum_congr rfl fun i _ => h_pmf_eq_f i]
    -- Now: ∑ i, f (x i) = ∑ a, (typeCount x a) · f a via fiberwise.
    have h_maps : ∀ i ∈ (Finset.univ : Finset (Fin n)), x i ∈ (Finset.univ : Finset α) :=
      fun i _ => Finset.mem_univ _
    have h := Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset α)) h_maps f
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    -- (typeCount x a : ℝ) * f a, with typeCount x a from filter.card
    unfold typeCount
    rfl
  -- Step 2: entropy μ (Xs 0) = ∑ a, negMulLog (P a) = -∑ a, P a · log P a.
  have h_entropy_eq : entropy μ (Xs 0) = ∑ a : α, P a * (-Real.log (P a)) := by
    unfold entropy
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Real.negMulLog, hP_def]
    ring
  -- Step 3: put together.
  have hn_R_pos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [h_agg, h_entropy_eq]
  -- (∑ a, (typeCount x a : ℝ) · f a) / n - ∑ a, P a · (-log P a)
  -- = ∑ a, ((typeCount x a)/n · f a - P a · (-log P a))
  -- = ∑ a, ((typeCount x a)/n · (-log P a) - P a · (-log P a))
  -- = ∑ a, ((typeCount x a)/n - P a) · (-log P a)
  -- = ∑ a, (P a - (typeCount x a)/n) · log P a.
  rw [Finset.sum_div]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  show ((typeCount x a : ℝ) * f a) / n - P a * (-Real.log (P a))
      = (P a - (typeCount x a : ℝ) / n) * Real.log (P a)
  rw [hf_def]
  field_simp
  ring

/-- **Strong ⟹ Weak typicality**: `x ∈ A^*_ε ⟹ |.../n - H| ≤ ε · L`. -/
lemma stronglyTypical_implies_weakly_typical_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (x : Fin n → α) (hx : x ∈ stronglyTypicalSet μ Xs n ε) :
    |(∑ i : Fin n, pmfLog μ Xs (x i)) / n - entropy μ (Xs 0)|
      ≤ ε * logSumAbs μ Xs := by
  classical
  set P : α → ℝ := fun a => (μ.map (Xs 0)).real {a} with hP_def
  rw [weak_displacement_eq_strong_sum μ Xs hXs hn x]
  rw [mem_stronglyTypicalSet_iff] at hx
  -- |∑ a, (P a - typeCount x a / n) · log P a| ≤ ∑ a, |P a - typeCount x a / n| · |log P a|
  --   ≤ ∑ a, ε · |log P a| = ε · ∑ a, |log P a| = ε · logSumAbs.
  calc |∑ a : α, (P a - (typeCount x a : ℝ) / n) * Real.log (P a)|
      ≤ ∑ a : α, |(P a - (typeCount x a : ℝ) / n) * Real.log (P a)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : α, |P a - (typeCount x a : ℝ) / n| * |Real.log (P a)| := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [abs_mul]
    _ ≤ ∑ a : α, ε * |Real.log (P a)| := by
          refine Finset.sum_le_sum fun a _ => ?_
          have h_abs_le : |P a - (typeCount x a : ℝ) / n| ≤ ε := by
            rw [show P a - (typeCount x a : ℝ) / n = -((typeCount x a : ℝ) / n - P a) from by ring,
              abs_neg]
            exact hx a
          exact mul_le_mul_of_nonneg_right h_abs_le (abs_nonneg _)
    _ = ε * ∑ a : α, |Real.log (P a)| := by
          rw [← Finset.mul_sum]
    _ = ε * logSumAbs μ Xs := by
          rfl

/-- **Strong ⟹ Weak (set inclusion)** with strict-form weak target `< ε'`:
if `ε · L < ε'`, then `A^*_ε ⊆ T_{ε'}`. -/
lemma stronglyTypicalSet_subset_typicalSet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {n : ℕ} (hn : 0 < n) {ε ε' : ℝ}
    (h_bound : ε * logSumAbs μ Xs < ε') :
    stronglyTypicalSet μ Xs n ε ⊆ typicalSet μ Xs n ε' := by
  intro x hx
  rw [mem_typicalSet_iff]
  -- |...| ≤ ε · L < ε'.
  exact lt_of_le_of_lt
    (stronglyTypical_implies_weakly_typical_bound μ Xs hXs hn x hx) h_bound

/-! ### Phase 4 — Size sandwich -/

/-- **Size upper bound**: `|A^*_ε^n| ≤ exp(n · (H + ε·L + δ))` for any `δ > 0`.

We need a small slack `δ > 0` because the bridge to weak typicality is non-strict
(`≤ ε · L`) but the weak-typical card bound uses strict `< ε'`. Taking
`ε' := ε · L + δ` recovers the desired form. -/
theorem stronglyTypicalSet_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a})
    {n : ℕ} (hn : 0 < n) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) :
    ((stronglyTypicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
      ≤ Real.exp ((n : ℝ) * (entropy μ (Xs 0) + ε * logSumAbs μ Xs + δ)) := by
  classical
  set ε' : ℝ := ε * logSumAbs μ Xs + δ with hε'_def
  have hL_nn : 0 ≤ logSumAbs μ Xs := logSumAbs_nonneg μ Xs
  have hε_L_nn : 0 ≤ ε * logSumAbs μ Xs := mul_nonneg hε hL_nn
  have hε'_pos : 0 < ε' := by
    show 0 < ε * logSumAbs μ Xs + δ
    linarith
  -- Subset bound: A^*_ε ⊆ T_{ε'}.
  have h_subset : stronglyTypicalSet μ Xs n ε ⊆ typicalSet μ Xs n ε' := by
    apply stronglyTypicalSet_subset_typicalSet μ Xs hXs hn
    show ε * logSumAbs μ Xs < ε * logSumAbs μ Xs + δ
    linarith
  -- Card monotonicity.
  have h_card_mono :
      ((stronglyTypicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
        ≤ ((typicalSet μ Xs n ε').toFinite.toFinset.card : ℝ) := by
    have h_finset_sub :
        (stronglyTypicalSet μ Xs n ε).toFinite.toFinset
          ⊆ (typicalSet μ Xs n ε').toFinite.toFinset := by
      intro x hx
      have : x ∈ stronglyTypicalSet μ Xs n ε :=
        (Set.Finite.mem_toFinset _).mp hx
      exact (Set.Finite.mem_toFinset _).mpr (h_subset this)
    exact_mod_cast Finset.card_le_card h_finset_sub
  -- Apply typicalSet_card_le with ε'.
  refine h_card_mono.trans ?_
  have h := typicalSet_card_le μ Xs hXs hpos n hε'_pos
  -- h : |T_{ε'}| ≤ exp(n · (H + ε'))
  -- Goal: |T_{ε'}| ≤ exp(n · (H + ε · L + δ))
  -- Since ε' = ε · L + δ, these are equal.
  have h_eq : (n : ℝ) * (entropy μ (Xs 0) + ε * logSumAbs μ Xs + δ)
      = (n : ℝ) * (entropy μ (Xs 0) + ε') := by
    show (n : ℝ) * (entropy μ (Xs 0) + ε * logSumAbs μ Xs + δ)
        = (n : ℝ) * (entropy μ (Xs 0) + (ε * logSumAbs μ Xs + δ))
    ring
  rw [h_eq]
  exact h

/-- **Size lower bound (eventually-N form)**: for any `η > 0`,
eventually `|A^*_ε^n| ≥ (1-η) · exp(n · (H - ε·L - δ))`. -/
theorem stronglyTypicalSet_card_ge_eventually
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hindep_pair : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a})
    {ε δ η : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 - η) * Real.exp ((n : ℝ) * (entropy μ (Xs 0) - ε * logSumAbs μ Xs - δ))
        ≤ ((stronglyTypicalSet μ Xs n ε).toFinite.toFinset.card : ℝ) := by
  classical
  set H : ℝ := entropy μ (Xs 0) with hH_def
  set L : ℝ := logSumAbs μ Xs with hL_def
  set ε' : ℝ := ε * L + δ with hε'_def
  have hL_nn : 0 ≤ L := logSumAbs_nonneg μ Xs
  have hε_L_nn : 0 ≤ ε * L := mul_nonneg hε.le hL_nn
  have hε'_pos : 0 < ε' := by show 0 < ε * L + δ; linarith
  -- Step 1: from Phase 2, eventually μ {jointRV ∈ A^*_ε} ≥ 1-η as ℝ≥0∞.
  have h_tend := stronglyTypicalSet_prob_tendsto_one μ Xs hXs hindep_pair hident hε
  -- Bridge to ℝ-tendsto: μ.real (T) = (μ A).toReal.
  have h_eq : ∀ n : ℕ,
      (μ.map (jointRV Xs n)).real (stronglyTypicalSet μ Xs n ε)
        = (μ {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε}).toReal := by
    intro n
    show ((μ.map (jointRV Xs n)) (stronglyTypicalSet μ Xs n ε)).toReal = _
    congr 1
    exact Measure.map_apply (measurable_jointRV Xs hXs n)
      (measurableSet_stronglyTypicalSet μ Xs n ε)
  -- Apply .toReal to the ℝ≥0∞-tendsto.
  have h_tend_R :
      Tendsto (fun n : ℕ =>
          (μ.map (jointRV Xs n)).real (stronglyTypicalSet μ Xs n ε))
        atTop (𝓝 1) := by
    refine Tendsto.congr (fun n => (h_eq n).symm) ?_
    have h_comp :
        Tendsto (fun n : ℕ =>
            (μ {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε}).toReal)
          atTop (𝓝 (1 : ℝ≥0∞).toReal) :=
      (ENNReal.continuousAt_toReal ENNReal.one_ne_top).tendsto.comp h_tend
    simpa using h_comp
  -- Eventually 1 - η ≤ μ.real(A^*_ε).
  have h_lt : (1 - η : ℝ) < 1 := by linarith
  have h_event :
      ∀ᶠ n in atTop,
        (1 - η) ≤ (μ.map (jointRV Xs n)).real (stronglyTypicalSet μ Xs n ε) := by
    filter_upwards [h_tend_R.eventually_const_lt h_lt] with n hn
    exact hn.le
  rcases Filter.eventually_atTop.mp h_event with ⟨N, hN⟩
  -- Take max(N, 1) to also have n ≥ 1.
  refine ⟨max N 1, fun n hn => ?_⟩
  have hN_n : N ≤ n := le_of_max_le_left hn
  have hn_pos : 1 ≤ n := le_of_max_le_right hn
  have hμ : (1 - η) ≤ (μ.map (jointRV Xs n)).real (stronglyTypicalSet μ Xs n ε) := hN n hN_n
  -- Step 2: A^*_ε ⊆ T_{ε'} (Phase 3).
  have hn_pos' : 0 < n := hn_pos
  have h_subset : stronglyTypicalSet μ Xs n ε ⊆ typicalSet μ Xs n ε' := by
    apply stronglyTypicalSet_subset_typicalSet μ Xs hXs hn_pos'
    show ε * L < ε * L + δ
    linarith
  -- Step 3: for x ∈ A^*_ε, p(x) ≤ exp(-n(H - ε')).
  set p : (Fin n → α) → ℝ := fun x => (μ.map (jointRV Xs n)).real {x} with hp_def
  set T : Finset (Fin n → α) := (stronglyTypicalSet μ Xs n ε).toFinite.toFinset
    with hT_def
  have h_coe : (T : Set (Fin n → α)) = stronglyTypicalSet μ Xs n ε :=
    (stronglyTypicalSet μ Xs n ε).toFinite.coe_toFinset
  have h_each_le : ∀ x ∈ T, p x ≤ Real.exp (-(n : ℝ) * (H - ε')) := by
    intro x hx
    have hxA : x ∈ stronglyTypicalSet μ Xs n ε := (Set.Finite.mem_toFinset _).mp hx
    have hxT : x ∈ typicalSet μ Xs n ε' := h_subset hxA
    exact typicalSet_prob_le μ Xs hXs hindep_full hident hpos n x hxT
  -- Step 4: μ.real(A^*_ε) = ∑ x ∈ T, p x ≤ |T| · exp(-n(H-ε')).
  have hMprob_joint : IsProbabilityMeasure (μ.map (jointRV Xs n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV Xs hXs n).aemeasurable
  have h_sum_T :
      (μ.map (jointRV Xs n)).real (stronglyTypicalSet μ Xs n ε) = ∑ x ∈ T, p x := by
    rw [← h_coe]
    exact (sum_measureReal_singleton (μ := μ.map (jointRV Xs n)) T).symm
  have h_sum_T_le :
      (∑ x ∈ T, p x) ≤ (T.card : ℝ) * Real.exp (-(n : ℝ) * (H - ε')) := by
    calc (∑ x ∈ T, p x)
        ≤ ∑ x ∈ T, Real.exp (-(n : ℝ) * (H - ε')) := Finset.sum_le_sum h_each_le
      _ = (T.card : ℝ) * Real.exp (-(n : ℝ) * (H - ε')) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 5: chain.
  have h_combined :
      (1 - η) ≤ (T.card : ℝ) * Real.exp (-(n : ℝ) * (H - ε')) := by
    calc (1 - η)
        ≤ (μ.map (jointRV Xs n)).real (stronglyTypicalSet μ Xs n ε) := hμ
      _ = ∑ x ∈ T, p x := h_sum_T
      _ ≤ (T.card : ℝ) * Real.exp (-(n : ℝ) * (H - ε')) := h_sum_T_le
  -- Step 6: multiply by exp(n(H-ε')).
  have hexp_pos : 0 < Real.exp ((n : ℝ) * (H - ε')) := Real.exp_pos _
  have h_exp_cancel :
      Real.exp (-(n : ℝ) * (H - ε')) * Real.exp ((n : ℝ) * (H - ε')) = 1 := by
    rw [show -(n : ℝ) * (H - ε') = -((n : ℝ) * (H - ε')) from by ring,
        ← Real.exp_add]
    simp
  have h_mul := mul_le_mul_of_nonneg_right h_combined hexp_pos.le
  have h_rhs :
      (T.card : ℝ) * Real.exp (-(n : ℝ) * (H - ε')) * Real.exp ((n : ℝ) * (H - ε'))
        = (T.card : ℝ) := by
    rw [mul_assoc, h_exp_cancel, mul_one]
  rw [h_rhs] at h_mul
  -- Step 7: reshape exponent to match the goal: H - ε' = H - ε · L - δ.
  have h_eq_exp : (n : ℝ) * (H - ε') = (n : ℝ) * (H - ε * L - δ) := by
    show (n : ℝ) * (H - (ε * L + δ)) = (n : ℝ) * (H - ε * L - δ)
    ring
  rw [h_eq_exp] at h_mul
  exact h_mul

end InformationTheory.Shannon
