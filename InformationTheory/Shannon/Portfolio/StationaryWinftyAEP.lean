import InformationTheory.Shannon.Portfolio.StationaryWinfty

/-!
# Growing-memory `W_∞` AEP for stationary markets (Cover–Thomas §16.5)

Upper half of Theorem 16.5.1: the growing-memory log-wealth average `growingMemoryLogAvg` is
eventually below the infinite-past optimal growth rate `W_∞ = condOptGrowthInfty` up to any margin,
almost surely. Split out of `StationaryWinfty.lean` (measurable selection, monotone convergence, and
the conditional Kuhn–Tucker gateway) to keep each file under the size budget.
-/

namespace InformationTheory.Shannon.Portfolio

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal

section CondOptimalGrowth

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {m : ℕ}

/-- Growing-memory log-wealth average (Cover–Thomas §16.5): the time average up to horizon `n` of
the per-epoch log returns of the stagewise conditional log-optimal portfolios `bstar i` along the
shift orbit of `T`. At epoch `i` the causal strategy uses the `i`-past optimal portfolio `bstar i`,
so `growingMemoryLogAvg X bstar T n ω = (1/(n+1)) log S*_n` where `S*_n = ∏ᵢ (bstar i · Xᵢ)` is the
growing-memory wealth. This is the object whose `limsup` is bounded above by `W_∞` (upper half of
the Algoet–Cover sandwich) and whose `liminf` is bounded below by each finite-memory rate. -/
noncomputable def growingMemoryLogAvg (X : Ω → Fin m → ℝ) (bstar : ℕ → Ω → Fin m → ℝ)
    (T : Ω → Ω) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range (n + 1), causalLogReturn X (bstar i) (T^[i] ω)) / (n + 1 : ℝ)

-- Wealth-ratio process `M_n ω = ∏ᵢ (bstar i · Xᵢ)/(bstarInf · Xᵢ)` along the shift orbit: the ratio
-- of the growing-memory wealth to the fixed infinite-past optimal wealth. A nonnegative
-- supermartingale (its integral stays `≤ 1`); `(1/n) log M_n → 0` drives the limsup upper bound.
private noncomputable def wealthRatioProcess (X : Ω → Fin m → ℝ) (bstar : ℕ → Ω → Fin m → ℝ)
    (bstarInf : Ω → Fin m → ℝ) (T : Ω → Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range (n + 1),
    (∑ j, bstar i (T^[i] ω) j * X (T^[i] ω) j) / (∑ j, bstarInf (T^[i] ω) j * X (T^[i] ω) j)

-- The wealth-ratio process is positive (a product of positive ratios).
private theorem wealthRatioProcess_pos {X : Ω → Fin m → ℝ} {bstar : ℕ → Ω → Fin m → ℝ}
    {bstarInf : Ω → Fin m → ℝ} {T : Ω → Ω}
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    (hInf_simplex : ∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m)) (n : ℕ) (ω : Ω) :
    0 < wealthRatioProcess X bstar bstarInf T n ω := by
  unfold wealthRatioProcess
  refine Finset.prod_pos fun i _ ↦ div_pos ?_ ?_
  · exact hpos (T^[i] ω) (bstar i (T^[i] ω)) (hbstar_simplex i (T^[i] ω))
  · exact hpos (T^[i] ω) (bstarInf (T^[i] ω)) (hInf_simplex (T^[i] ω))

-- `log M_n` is the sum of the per-epoch log-return differences (numerator − denominator).
private theorem wealthRatioProcess_log_eq {X : Ω → Fin m → ℝ} {bstar : ℕ → Ω → Fin m → ℝ}
    {bstarInf : Ω → Fin m → ℝ} {T : Ω → Ω}
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    (hInf_simplex : ∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m)) (n : ℕ) (ω : Ω) :
    Real.log (wealthRatioProcess X bstar bstarInf T n ω)
      = ∑ i ∈ Finset.range (n + 1),
        (causalLogReturn X (bstar i) (T^[i] ω) - causalLogReturn X bstarInf (T^[i] ω)) := by
  unfold wealthRatioProcess
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hnum : (0:ℝ) < ∑ j, bstar i (T^[i] ω) j * X (T^[i] ω) j :=
      hpos (T^[i] ω) (bstar i (T^[i] ω)) (hbstar_simplex i (T^[i] ω))
    have hden : (0:ℝ) < ∑ j, bstarInf (T^[i] ω) j * X (T^[i] ω) j :=
      hpos (T^[i] ω) (bstarInf (T^[i] ω)) (hInf_simplex (T^[i] ω))
    rw [Real.log_div hnum.ne' hden.ne']
    rfl
  · intro i _
    have hnum : (0:ℝ) < ∑ j, bstar i (T^[i] ω) j * X (T^[i] ω) j :=
      hpos (T^[i] ω) (bstar i (T^[i] ω)) (hbstar_simplex i (T^[i] ω))
    have hden : (0:ℝ) < ∑ j, bstarInf (T^[i] ω) j * X (T^[i] ω) j :=
      hpos (T^[i] ω) (bstarInf (T^[i] ω)) (hInf_simplex (T^[i] ω))
    exact div_ne_zero hnum.ne' hden.ne'

/-- Supermartingale integral bound for the wealth-ratio process (Cover–Thomas §16.5): the mean
wealth ratio `E[M_n]` stays at most `1`. The base case `n = 0` is proved here: the conditional
Kuhn–Tucker inequality `condKuhnTucker_infPast` (the `⨆ⱼℱⱼ`-conditional mean of the one-step ratio
is `≤ 1`) plus the tower property `integral_condExp` give `∫ M₀ ≤ 1`, hence `∫⁻ ofReal M₀ ≤ 1`. The
inductive step (`∫⁻ M_{k+1} ≤ ∫⁻ M_k`) factors `M_{k+1} = M_k · (ρ_{k+1} ∘ Tᵏ⁺¹)` and needs the
increment's conditional mean `≤ 1` given the growing history, then pulls `M_k` out. The increment
bound is available: transporting `condKuhnTucker_infPast` (conditioned on `⨆ⱼℱⱼ` at the base point)
to epoch `k+1` under the measure-preserving shift via the in-project
`InformationTheory.Shannon.TwoSided.condExp_comp_measurePreserving` gives
`μ[ρ_{k+1} ∘ Tᵏ⁺¹ | (⨆ⱼℱⱼ).comap Tᵏ⁺¹] ≤ᵐ 1`. The **missing** piece is the pull-out's adaptedness:
`M_k` must be `(⨆ⱼℱⱼ).comap Tᵏ⁺¹`-measurable. The abstract `ℱ`/`T`/`X` hypotheses assert no
compatibility (`ℱ` is an arbitrary filtration, `X` an arbitrary measurable map, `T` an arbitrary
measure-preserving map), so this adaptedness does not hold abstractly — it is exactly the concrete
past-filtration/shift coherence (R3-a in the closure plan, where `ℱ := pastFiltration` and
`T := shift` make `M_k` a function of coordinates `≤ k`, hence `(past).comap Tᵏ⁺¹`-measurable). The
closure therefore depends on R3-a, not merely on file size. `hpos`/`hint`/`hint_coord` are
market-regularity preconditions; `hInf_dom` is the KT dominance of `bstarInf`, received (not the
proof core), mirroring `condKuhnTucker_infPast`.
@residual(plan:portfolio-stationary-woo-plan) -/
private theorem wealthRatioProcess_lintegral_le_one [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {X : Ω → Fin m → ℝ}
    [Nonempty (Fin m)] (hX : Measurable X) {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ)
    {bstar : ℕ → Ω → Fin m → ℝ} (hbstar_meas : ∀ k, StronglyMeasurable[ℱ k] (bstar k))
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    {bstarInf : Ω → Fin m → ℝ} (hInf_meas : StronglyMeasurable[⨆ j, ℱ j] bstarInf)
    (hInf_simplex : ∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m))
    (hint_coord : ∀ i, Integrable (fun ω ↦ X ω i / (∑ j, bstarInf ω j * X ω j)) μ)
    (hInf_dom : ∀ (c : Ω → Fin m → ℝ), StronglyMeasurable[⨆ j, ℱ j] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ⨆ j, ℱ j] ≤ᵐ[μ] μ[causalLogReturn X bstarInf | ⨆ j, ℱ j])
    (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T n ω) ∂μ ≤ 1 := by
  classical
  induction n with
  | zero =>
    have hsup_le : (⨆ j, ℱ j) ≤ m0 := iSup_le ℱ.le
    have hSb : ∀ ω, (0:ℝ) < ∑ j, bstarInf ω j * X ω j :=
      fun ω ↦ hpos ω (bstarInf ω) (hInf_simplex ω)
    have hSc : ∀ ω, (0:ℝ) < ∑ j, bstar 0 ω j * X ω j :=
      fun ω ↦ hpos ω (bstar 0 ω) (hbstar_simplex 0 ω)
    have hc : StronglyMeasurable[⨆ j, ℱ j] (bstar 0) :=
      (hbstar_meas 0).mono (le_iSup (fun j ↦ ℱ j) 0)
    have hKT := condKuhnTucker_infPast μ ℱ X hX hpos hint bstarInf hInf_meas hInf_simplex
      hint_coord hInf_dom (bstar 0) hc (hbstar_simplex 0)
    set r : Ω → ℝ := fun ω ↦ (∑ j, bstar 0 ω j * X ω j) / (∑ j, bstarInf ω j * X ω j) with hr_def
    have hr_pos : ∀ ω, 0 < r ω := fun ω ↦ div_pos (hSc ω) (hSb ω)
    have hr_meas : Measurable r := by
      rw [hr_def]
      exact (Finset.measurable_sum _ fun j _ ↦
          ((measurable_pi_apply j).comp ((hbstar_meas 0).mono (ℱ.le 0)).measurable).mul
            ((measurable_pi_apply j).comp hX)).div
        (Finset.measurable_sum _ fun j _ ↦
          ((measurable_pi_apply j).comp (hInf_meas.mono hsup_le).measurable).mul
            ((measurable_pi_apply j).comp hX))
    have hr_int : Integrable r μ := by
      have hbound : Integrable (fun ω ↦ ∑ i, X ω i / (∑ j, bstarInf ω j * X ω j)) μ :=
        integrable_finsetSum Finset.univ fun i _ ↦ hint_coord i
      refine Integrable.mono' hbound hr_meas.aestronglyMeasurable (Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hr_pos ω))]
      simp only [hr_def]
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [mul_div_assoc]
      refine mul_le_of_le_one_left (le_of_lt (div_pos (market_pos hpos ω i) (hSb ω))) ?_
      exact stdSimplex_component_le_one (hbstar_simplex 0 ω) i
    have hint_r : ∫ ω, r ω ∂μ ≤ 1 := by
      rw [← integral_condExp hsup_le]
      calc ∫ ω, (μ[r | ⨆ j, ℱ j]) ω ∂μ
          ≤ ∫ _, (1:ℝ) ∂μ := integral_mono_ae integrable_condExp (integrable_const 1) hKT
        _ = 1 := by simp
    have hM0 : ∀ ω, wealthRatioProcess X bstar bstarInf T 0 ω = r ω := fun ω ↦ by
      simp only [wealthRatioProcess, zero_add, Finset.prod_range_one, Function.iterate_zero,
        id_eq, hr_def]
    simp_rw [hM0]
    rw [← ofReal_integral_eq_lintegral_ofReal hr_int
      (Eventually.of_forall fun ω ↦ le_of_lt (hr_pos ω))]
    exact ENNReal.ofReal_le_one.mpr hint_r
  | succ k ih =>
    -- Inductive step: `∫⁻ M_{k+1} ≤ ∫⁻ M_k ≤ 1`. The increment factor `ρ_{k+1} ∘ Tᵏ⁺¹` has
    -- conditional mean `≤ 1` given `(⨆ⱼℱⱼ).comap Tᵏ⁺¹` (transport `condKuhnTucker_infPast` via
    -- `condExp_comp_measurePreserving`), but pulling `M_k` out of that conditional mean needs
    -- `M_k` to be `(⨆ⱼℱⱼ).comap Tᵏ⁺¹`-measurable (growing-history adaptedness). The abstract
    -- `ℱ`/`T`/`X` hypotheses state no compatibility, so this adaptedness is unavailable here; it is
    -- supplied by the concrete past-filtration/shift instantiation (R3-a in the closure plan).
    -- @residual(plan:portfolio-stationary-woo-plan)
    sorry

-- The time-averaged log wealth ratio is eventually below any positive threshold a.e. (Markov +
-- Borel–Cantelli on the integral bound `E[M_n] ≤ 1`, then `(1/n) log M_n ≤ 2 log(n+1)/(n+1) → 0`).
-- This eventual-upper-bound form is the honest content of `limsup ≤ 0`, avoiding the `ℝ`-limsup
-- junk value on paths where `M_n → 0` super-exponentially (there `(1/n) log M_n → -∞`).
private theorem wealthRatio_logAvg_eventually_le [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {X : Ω → Fin m → ℝ}
    [Nonempty (Fin m)] (hX : Measurable X) {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ)
    {bstar : ℕ → Ω → Fin m → ℝ} (hbstar_meas : ∀ k, StronglyMeasurable[ℱ k] (bstar k))
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    {bstarInf : Ω → Fin m → ℝ} (hInf_meas : StronglyMeasurable[⨆ j, ℱ j] bstarInf)
    (hInf_simplex : ∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m))
    (hint_coord : ∀ i, Integrable (fun ω ↦ X ω i / (∑ j, bstarInf ω j * X ω j)) μ)
    (hInf_dom : ∀ (c : Ω → Fin m → ℝ), StronglyMeasurable[⨆ j, ℱ j] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ⨆ j, ℱ j] ≤ᵐ[μ] μ[causalLogReturn X bstarInf | ⨆ j, ℱ j]) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (wealthRatioProcess X bstar bstarInf T n ω) / (n + 1 : ℝ) ≤ ε := by
  classical
  have hbInf_m : Measurable bstarInf := (hInf_meas.mono (iSup_le ℱ.le)).measurable
  have hbstar_m : ∀ i, Measurable (bstar i) := fun i ↦ ((hbstar_meas i).mono (ℱ.le i)).measurable
  have hTi : ∀ i, Measurable (T^[i] : Ω → Ω) := fun i ↦ hT.measurable.iterate i
  have hM_meas : ∀ n, Measurable (wealthRatioProcess X bstar bstarInf T n) := by
    intro n
    refine Finset.measurable_prod _ fun i _ ↦ Measurable.div ?_ ?_
    · exact Finset.measurable_sum _ fun j _ ↦
        ((measurable_pi_apply j).comp ((hbstar_m i).comp (hTi i))).mul
          ((measurable_pi_apply j).comp (hX.comp (hTi i)))
    · exact Finset.measurable_sum _ fun j _ ↦
        ((measurable_pi_apply j).comp (hbInf_m.comp (hTi i))).mul
          ((measurable_pi_apply j).comp (hX.comp (hTi i)))
  have hApos : ∀ n ω, 0 < wealthRatioProcess X bstar bstarInf T n ω :=
    fun n ω ↦ wealthRatioProcess_pos hpos hbstar_simplex hInf_simplex n ω
  -- Summable `p`-series majorant `∑ 1/(n+1)²`.
  have hsummable : Summable (fun n : ℕ ↦ (((n:ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    refine ((summable_nat_add_iff 1).mpr h2).congr fun n ↦ ?_
    push_cast
    rw [one_div]
  -- Markov: `μ {(n+1)² ≤ Mₙ} ≤ ofReal (1/(n+1)²)`.
  have hmarkov : ∀ n : ℕ, μ {ω | ((n:ℝ) + 1) ^ 2 ≤ wealthRatioProcess X bstar bstarInf T n ω}
      ≤ ENNReal.ofReal ((((n:ℝ) + 1) ^ 2)⁻¹) := by
    intro n
    have hcrux := wealthRatioProcess_lintegral_le_one μ ℱ hX hT hpos hint hbstar_meas hbstar_simplex
      hInf_meas hInf_simplex hint_coord hInf_dom n
    have ht_pos : (0 : ℝ) < ((n:ℝ) + 1) ^ 2 := by positivity
    have hmk := mul_meas_ge_le_lintegral₀ (μ := μ)
      (f := fun ω ↦ ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T n ω))
      ((ENNReal.measurable_ofReal.comp (hM_meas n)).aemeasurable) (ENNReal.ofReal (((n:ℝ) + 1) ^ 2))
    have hset : {ω | ENNReal.ofReal (((n:ℝ) + 1) ^ 2)
          ≤ ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T n ω)}
        = {ω | ((n:ℝ) + 1) ^ 2 ≤ wealthRatioProcess X bstar bstarInf T n ω} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [ENNReal.ofReal_le_ofReal_iff (le_of_lt (hApos n ω))]
    rw [hset] at hmk
    have hle1 : ENNReal.ofReal (((n:ℝ) + 1) ^ 2)
        * μ {ω | ((n:ℝ) + 1) ^ 2 ≤ wealthRatioProcess X bstar bstarInf T n ω} ≤ 1 :=
      le_trans hmk hcrux
    have hofpos : ENNReal.ofReal (((n:ℝ) + 1) ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact ht_pos
    rw [ENNReal.ofReal_inv_of_pos ht_pos, inv_eq_one_div,
      ENNReal.le_div_iff_mul_le (Or.inl hofpos) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hle1
  -- Borel–Cantelli: a.e. only finitely many `n` have `(n+1)² ≤ Mₙ`.
  have hsum_ne : ∑' (n : ℕ), μ {ω | ((n:ℝ) + 1) ^ 2 ≤ wealthRatioProcess X bstar bstarInf T n ω}
      ≠ ∞ := by
    have hb : ∑' (n : ℕ), μ {ω | ((n:ℝ) + 1) ^ 2 ≤ wealthRatioProcess X bstar bstarInf T n ω}
        ≤ ENNReal.ofReal (∑' (n : ℕ), (((n:ℝ) + 1) ^ 2)⁻¹) :=
      calc ∑' (n : ℕ), μ {ω | ((n:ℝ) + 1) ^ 2 ≤ wealthRatioProcess X bstar bstarInf T n ω}
          ≤ ∑' (n : ℕ), ENNReal.ofReal ((((n:ℝ) + 1) ^ 2)⁻¹) := ENNReal.tsum_le_tsum hmarkov
        _ = ENNReal.ofReal (∑' (n : ℕ), (((n:ℝ) + 1) ^ 2)⁻¹) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsummable).symm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hbc := ae_finite_setOf_mem (μ := μ)
    (s := fun (n : ℕ) ↦ {ω | ((n:ℝ) + 1) ^ 2 ≤ wealthRatioProcess X bstar bstarInf T n ω}) hsum_ne
  -- Majorant limit `2 log(n+1)/(n+1) → 0`.
  have hbase : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hnat : Tendsto (fun n : ℕ ↦ (n:ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hmaj : Tendsto (fun n : ℕ ↦ 2 * (Real.log ((n:ℝ) + 1) / ((n:ℝ) + 1))) atTop (𝓝 0) := by
    have := (hbase.comp hnat).const_mul 2
    simpa using this
  filter_upwards [hbc] with ω hω_fin
  intro ε hε
  have hmaj_ev := hmaj.eventually (Iic_mem_nhds hε)
  have hlt_ev : ∀ᶠ n in atTop, wealthRatioProcess X bstar bstarInf T n ω < ((n:ℝ) + 1) ^ 2 := by
    obtain ⟨N, hN⟩ := hω_fin.bddAbove
    rw [eventually_atTop]
    refine ⟨N + 1, fun n hn ↦ ?_⟩
    rw [← not_le]
    intro hcon
    have : n ≤ N := hN hcon
    omega
  filter_upwards [hlt_ev, hmaj_ev] with n hn_lt hn_maj
  have hMpos := hApos n ω
  have hlog : Real.log (wealthRatioProcess X bstar bstarInf T n ω) ≤ 2 * Real.log ((n:ℝ) + 1) := by
    have h := Real.log_lt_log hMpos hn_lt
    rw [Real.log_pow, Nat.cast_ofNat] at h
    exact le_of_lt h
  have hn1pos : (0 : ℝ) < (n:ℝ) + 1 := by positivity
  calc Real.log (wealthRatioProcess X bstar bstarInf T n ω) / ((n:ℝ) + 1)
      ≤ 2 * Real.log ((n:ℝ) + 1) / ((n:ℝ) + 1) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hlog (le_of_lt (inv_pos.mpr hn1pos))
    _ = 2 * (Real.log ((n:ℝ) + 1) / ((n:ℝ) + 1)) := by ring
    _ ≤ ε := hn_maj

/-- Upper half of the growing-memory `W_∞` AEP (Cover–Thomas Theorem 16.5.1): the growing-memory
log-wealth average is eventually below `W_∞ = condOptGrowthInfty` up to any margin `ε`, almost
surely. The proof decomposes `growingMemoryLogAvg n = (1/n) log Mₙ + (1/n) ∑ᵢ log(bstarInf · Xᵢ)`:
the first term is eventually below any positive threshold (`wealthRatio_logAvg_eventually_le`, from
the supermartingale integral bound) and the second converges to `∫ log(bstarInf · X) = W_∞` by
Birkhoff's ergodic theorem (`birkhoff_ergodic_ae`) and the gateway identity
`condOptGrowthInfty_eq_integral_infPast`. The eventual-upper-bound form is the honest content of
`limsup ≤ W_∞`; combined with the Birkhoff lower half it yields the almost-sure convergence
(the `ℝ`-`limsup` value is junk on paths where the growing memory underperforms to `−∞`, which only
the lower half rules out). `bstar`/`bstarInf` and their conditional-dominance properties
(`hbstar_dom`/`hInf_dom`) are received as the stagewise/infinite-past conditional log-optimal
selections (constructed separately, e.g. via `exists_condLogOptimalSeq` /
`exists_infPast_condLogOptimal`); the remaining hypotheses are market-regularity/ergodicity
preconditions. -/
theorem growingMemory_eventually_le_condOptGrowthInfty [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    (ℱ : Filtration ℕ m0) (X : Ω → Fin m → ℝ) [Nonempty (Fin m)] (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ)
    (bstar : ℕ → Ω → Fin m → ℝ) (hbstar_meas : ∀ k, StronglyMeasurable[ℱ k] (bstar k))
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    (hbstar_dom : ∀ (k : ℕ) (c : Ω → Fin m → ℝ), StronglyMeasurable[ℱ k] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ℱ k] ≤ᵐ[μ] μ[causalLogReturn X (bstar k) | ℱ k])
    (bstarInf : Ω → Fin m → ℝ) (hInf_meas : StronglyMeasurable[⨆ j, ℱ j] bstarInf)
    (hInf_simplex : ∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m))
    (hint_coord : ∀ i, Integrable (fun ω ↦ X ω i / (∑ j, bstarInf ω j * X ω j)) μ)
    (hInf_dom : ∀ (c : Ω → Fin m → ℝ), StronglyMeasurable[⨆ j, ℱ j] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ⨆ j, ℱ j] ≤ᵐ[μ] μ[causalLogReturn X bstarInf | ⨆ j, ℱ j]) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      growingMemoryLogAvg X bstar T n ω ≤ condOptGrowthInfty μ X bstar + ε := by
  have hbstarInf_measurable : Measurable bstarInf := (hInf_meas.mono (iSup_le ℱ.le)).measurable
  have hid : ∫ ω, causalLogReturn X bstarInf ω ∂μ = condOptGrowthInfty μ X bstar :=
    condOptGrowthInfty_eq_integral_infPast μ ℱ X hX hpos hint bstar hbstar_meas hbstar_simplex
      hbstar_dom bstarInf hInf_meas hInf_simplex hInf_dom
  have hbirk := birkhoff_ergodic_ae hT hT_erg (hint bstarInf hbstarInf_measurable hInf_simplex)
  have hupper := wealthRatio_logAvg_eventually_le μ ℱ hX hT hpos hint hbstar_meas hbstar_simplex
    hInf_meas hInf_simplex hint_coord hInf_dom
  filter_upwards [hbirk, hupper] with ω hbirk_ω hupper_ω
  intro ε hε
  -- Decompose the growing-memory average into the log wealth ratio plus the `bstarInf` average.
  have hdecomp : ∀ n : ℕ, growingMemoryLogAvg X bstar T n ω
      = Real.log (wealthRatioProcess X bstar bstarInf T n ω) / (n + 1 : ℝ)
        + (∑ i ∈ Finset.range (n + 1), causalLogReturn X bstarInf (T^[i] ω)) / (n + 1 : ℝ) := by
    intro n
    unfold growingMemoryLogAvg
    rw [wealthRatioProcess_log_eq hpos hbstar_simplex hInf_simplex, ← add_div,
      ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- The fixed-`bstarInf` Birkhoff average converges to `W_∞`, hence is eventually `≤ W_∞ + ε/2`.
  have hbirk_sum : Tendsto (fun n ↦
      (∑ i ∈ Finset.range (n + 1), causalLogReturn X bstarInf (T^[i] ω)) / (n + 1 : ℝ)) atTop
      (𝓝 (condOptGrowthInfty μ X bstar)) := by
    rw [← hid]; exact hbirk_ω
  have hlt_half : condOptGrowthInfty μ X bstar < condOptGrowthInfty μ X bstar + ε / 2 := by linarith
  have hbirk_ev := hbirk_sum.eventually (Iic_mem_nhds hlt_half)
  have hlog_ev := hupper_ω (ε / 2) (by linarith)
  filter_upwards [hbirk_ev, hlog_ev] with n hb hl
  rw [hdecomp n]
  linarith

end CondOptimalGrowth

end InformationTheory.Shannon.Portfolio
