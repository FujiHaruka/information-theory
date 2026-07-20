import InformationTheory.Shannon.Portfolio.StationaryWinfty
import InformationTheory.Probability.TwoSidedExtension.CondExpMeasurePreserving
import Mathlib.MeasureTheory.Function.ConditionalLExpectation

/-!
# Growing-memory `W_∞` AEP for stationary markets (Cover–Thomas §16.5)

Theorem 16.5.1: the growing-memory log-wealth average `growingMemoryLogAvg` converges almost surely
to the infinite-past optimal growth rate `W_∞ = condOptGrowthInfty`
(`growingMemory_logWealth_tendsto_condOptGrowthInfty`). The proof is the Algoet–Cover sandwich: the
eventual upper bound `≤ W_∞ + ε` from the wealth-ratio supermartingale against the infinite-past
optimal portfolio, and the eventual lower bound `≥ W_∞ − ε` from the finite-memory Birkhoff rates
rising to `W_∞`. Split out of `StationaryWinfty.lean` (measurable selection, monotone convergence,
and the conditional Kuhn–Tucker gateway) to keep each file under the size budget.
-/

namespace InformationTheory.Shannon.Portfolio

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal

section CondLExpPullOut

-- General ENNReal conditional-Lebesgue-expectation pull-out, copied from
-- `InformationTheory.Shannon.lintegral_mul_eq_lintegral_mul_condLExp`
-- (`SMB/AlgoetCover/TwoSidedRatio.lean`). The original lives in the heavy finite-alphabet
-- SMB machinery; both statements are alphabet-free, so we replicate them privately here to keep
-- the portfolio file's import surface light rather than pull in McMillan–Breiman.

-- Indicator special case of the pull-out property for the conditional Lebesgue expectation.
private lemma lintegral_indicator_mul_eq
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : @Measure Ω m₀)
    [SigmaFinite (μ.trim hm)]
    {B : Set Ω} (hB : MeasurableSet[m] B) (f : Ω → ℝ≥0∞) :
    ∫⁻ x, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * f x ∂μ
      = ∫⁻ x, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * μ⁻[f|m] x ∂μ := by
  have h_rw : ∀ (h : Ω → ℝ≥0∞),
      ∫⁻ x, B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * h x ∂μ = ∫⁻ x in B, h x ∂μ := by
    intro h
    rw [show (fun x ↦ B.indicator (fun _ ↦ (1 : ℝ≥0∞)) x * h x)
          = B.indicator (fun x ↦ 1 * h x) from ?_]
    · rw [MeasureTheory.lintegral_indicator (hm _ hB)]
      simp
    · funext x
      by_cases hx : x ∈ B
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
  rw [h_rw, h_rw, MeasureTheory.setLIntegral_condLExp hm μ f hB]

-- ENNReal pull-out (general): for `m`-measurable `g` and `m₀`-measurable `f`,
-- `∫⁻ x, g · f dμ = ∫⁻ x, g · μ⁻[f|m] dμ`.
private lemma lintegral_mul_eq_lintegral_mul_condLExp
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : @Measure Ω m₀)
    [SigmaFinite (μ.trim hm)]
    {g : Ω → ℝ≥0∞} (hg : Measurable[m] g)
    {f : Ω → ℝ≥0∞} (hf : @Measurable Ω ℝ≥0∞ m₀ _ f) :
    ∫⁻ x, g x * f x ∂μ = ∫⁻ x, g x * μ⁻[f|m] x ∂μ := by
  classical
  set sn : ℕ → @SimpleFunc Ω m ℝ≥0∞ := SimpleFunc.eapprox g with hsn_def
  have h_sn_mono : ∀ x, Monotone (fun n ↦ (sn n : Ω → ℝ≥0∞) x) :=
    fun x i j hij ↦ SimpleFunc.monotone_eapprox _ hij x
  have h_g_iSup : ∀ x, g x = ⨆ n, (sn n : Ω → ℝ≥0∞) x :=
    fun x ↦ (SimpleFunc.iSup_eapprox_apply hg x).symm
  have h_sn_meas_m₀ : ∀ n, @Measurable Ω ℝ≥0∞ m₀ _ (sn n : Ω → ℝ≥0∞) :=
    fun n ↦ ((sn n).measurable).mono hm le_rfl
  have h_cL_meas : Measurable[m] (μ⁻[f|m]) := MeasureTheory.measurable_condLExp m μ f
  have h_cL_meas_m₀ : @Measurable Ω ℝ≥0∞ m₀ _ (μ⁻[f|m]) := h_cL_meas.mono hm le_rfl
  have h_g_mul_iSup : ∀ (h : Ω → ℝ≥0∞), (fun x ↦ g x * h x)
      = fun x ↦ ⨆ n, (sn n : Ω → ℝ≥0∞) x * h x := by
    intro h
    funext x
    rw [h_g_iSup, ENNReal.iSup_mul]
  have h_mono_mul : ∀ (h : Ω → ℝ≥0∞) x, Monotone (fun n ↦ (sn n : Ω → ℝ≥0∞) x * h x) := by
    intro h x i j hij
    have h_nn : (0 : ℝ≥0∞) ≤ h x := bot_le
    exact mul_le_mul_of_nonneg_right (h_sn_mono x hij) h_nn
  have h_meas_mul : ∀ (h : Ω → ℝ≥0∞), @Measurable Ω ℝ≥0∞ m₀ _ h →
      ∀ n, @Measurable Ω ℝ≥0∞ m₀ _ (fun x ↦ (sn n : Ω → ℝ≥0∞) x * h x) :=
    fun h hh n ↦ Measurable.mul (h_sn_meas_m₀ n) hh
  have h_step : ∀ n, ∫⁻ x, (sn n : Ω → ℝ≥0∞) x * f x ∂μ
      = ∫⁻ x, (sn n : Ω → ℝ≥0∞) x * μ⁻[f|m] x ∂μ := by
    intro n
    have h_sn_decomp : ∀ x, (sn n : Ω → ℝ≥0∞) x
        = ∑ c ∈ (sn n).range, c * ((sn n) ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
      intro x
      rw [Finset.sum_eq_single (sn n x)]
      · simp
      · intro c _ hc
        have h_notmem : x ∉ (sn n) ⁻¹' {c} := fun hx ↦ hc hx.symm
        simp [Set.indicator_of_notMem h_notmem]
      · intro hcontra
        exact absurd (SimpleFunc.mem_range_self _ x) hcontra
    have h_decomp : ∀ x (h : Ω → ℝ≥0∞), (sn n : Ω → ℝ≥0∞) x * h x
        = ∑ c ∈ (sn n).range, (c * ((sn n) ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ≥0∞)) x) * h x := by
      intro x h
      rw [h_sn_decomp x, Finset.sum_mul]
    have h_preim_meas : ∀ c, MeasurableSet[m] ((sn n) ⁻¹' {c}) :=
      fun c ↦ (sn n).measurableSet_fiber c
    have h_preim_lt_top : ∀ c ∈ (sn n).range, c ≠ ∞ := by
      intro c hc
      rcases SimpleFunc.mem_range.mp hc with ⟨x, rfl⟩
      exact (SimpleFunc.eapprox_lt_top g n x).ne
    have h_per_c_LHS : ∀ c (h : Ω → ℝ≥0∞), c ≠ ∞ →
        ∫⁻ x, (c * ((sn n) ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ≥0∞)) x) * h x ∂μ
          = c * ∫⁻ x, ((sn n) ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ≥0∞)) x * h x ∂μ := by
      intro c h hc_ne_top
      rw [show (fun x ↦ c * ((sn n) ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ≥0∞)) x * h x)
          = fun x ↦ c * (((sn n) ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ≥0∞)) x * h x) from
            funext (fun _ ↦ by ring)]
      rw [MeasureTheory.lintegral_const_mul' _ _ hc_ne_top]
    rw [show (fun x ↦ (sn n : Ω → ℝ≥0∞) x * f x)
        = fun x ↦ ∑ c ∈ (sn n).range,
          (c * ((sn n) ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ≥0∞)) x) * f x from
            funext (fun x ↦ h_decomp x f)]
    rw [show (fun x ↦ (sn n : Ω → ℝ≥0∞) x * μ⁻[f|m] x)
        = fun x ↦ ∑ c ∈ (sn n).range,
          (c * ((sn n) ⁻¹' {c}).indicator (fun _ ↦ (1 : ℝ≥0∞)) x) * μ⁻[f|m] x from
            funext (fun x ↦ h_decomp x _)]
    rw [MeasureTheory.lintegral_finsetSum _ (fun c _ ↦
      ((Measurable.indicator measurable_const (hm _ (h_preim_meas c))).const_mul c).mul hf)]
    rw [MeasureTheory.lintegral_finsetSum _ (fun c _ ↦
      ((Measurable.indicator measurable_const (hm _ (h_preim_meas c))).const_mul c).mul
        h_cL_meas_m₀)]
    refine Finset.sum_congr rfl (fun c hc ↦ ?_)
    rw [h_per_c_LHS c f (h_preim_lt_top c hc),
        h_per_c_LHS c (μ⁻[f|m]) (h_preim_lt_top c hc),
        lintegral_indicator_mul_eq hm μ (h_preim_meas c) f]
  rw [h_g_mul_iSup f, h_g_mul_iSup (μ⁻[f|m])]
  rw [MeasureTheory.lintegral_iSup (fun n ↦ h_meas_mul f hf n)
        (fun i j hij x ↦ h_mono_mul f x hij)]
  rw [MeasureTheory.lintegral_iSup (fun n ↦ h_meas_mul (μ⁻[f|m]) h_cL_meas_m₀ n)
    (fun i j hij x ↦ h_mono_mul _ x hij)]
  exact iSup_congr h_step

-- Bridge from a real conditional-expectation upper bound to the ENNReal conditional Lebesgue
-- expectation: a nonnegative integrable `f` with `μ[f|m] ≤ᵐ 1` satisfies `μ⁻[ofReal ∘ f|m] ≤ᵐ 1`.
-- Both `μ⁻[·|·]` and `μ[·|·]` integrate `f` the same way over `m`-measurable sets, and `ofReal`
-- transports the real set-integral bound (`f` nonnegative and integrable) to the ENNReal one.
private lemma condLExp_ofReal_le_one_of_condExp_le_one
    {Ω : Type*} {m0 mG : MeasurableSpace Ω} (hm : mG ≤ m0) (μ : @Measure Ω m0)
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf_int : Integrable f μ)
    (hf_nn : ∀ ω, 0 ≤ f ω) (hbound : μ[f | mG] ≤ᵐ[μ] 1) :
    μ⁻[fun ω ↦ ENNReal.ofReal (f ω) | mG] ≤ᵐ[μ] 1 := by
  haveI : SigmaFinite (μ.trim hm) := by
    haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  apply ae_le_of_ae_le_trim
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (measurable_condLExp _ _ _) ?_
  intro s hs _
  rw [setLIntegral_condLExp_trim hm _ _ hs]
  have hRHS : ∫⁻ x in s, (1 : Ω → ℝ≥0∞) x ∂(μ.trim hm) = μ s := by
    simp only [Pi.one_apply]
    rw [setLIntegral_one, trim_measurableSet_eq hm hs]
  rw [hRHS, ← ofReal_integral_eq_lintegral_ofReal hf_int.integrableOn
    (ae_restrict_of_ae (Eventually.of_forall hf_nn)), ← setIntegral_condExp hm hf_int hs]
  have hle : ∫ x in s, (μ[f | mG]) x ∂μ ≤ (μ s).toReal := by
    calc ∫ x in s, (μ[f | mG]) x ∂μ
        ≤ ∫ _ in s, (1 : ℝ) ∂μ :=
          setIntegral_mono_ae integrable_condExp.integrableOn (integrable_const 1).integrableOn
            hbound
      _ = (μ s).toReal := by rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  calc ENNReal.ofReal (∫ x in s, (μ[f | mG]) x ∂μ)
      ≤ ENNReal.ofReal ((μ s).toReal) := ENNReal.ofReal_le_ofReal hle
    _ = μ s := ENNReal.ofReal_toReal (measure_ne_top μ s)

end CondLExpPullOut

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
wealth ratio `E[M_n]` stays at most `1`. The base case `n = 0` uses the conditional Kuhn–Tucker
inequality `condKuhnTucker_infPast` (the `⨆ⱼℱⱼ`-conditional mean of the one-step ratio is `≤ 1`)
plus the tower property `integral_condExp` to get `∫ M₀ ≤ 1`, hence `∫⁻ ofReal M₀ ≤ 1`. The
inductive step (`∫⁻ M_{k+1} ≤ ∫⁻ M_k`) factors `M_{k+1} = M_k · (ρ_{k+1} ∘ Tᵏ⁺¹)`, pulls `M_k` out
of the conditional Lebesgue expectation over `(⨆ⱼℱⱼ).comap Tᵏ⁺¹`, and uses the increment bound
`μ[ρ_{k+1} ∘ Tᵏ⁺¹ | (⨆ⱼℱⱼ).comap Tᵏ⁺¹] ≤ᵐ 1` (transporting `condKuhnTucker_infPast` to epoch `k+1`
under the measure-preserving shift via `condExp_comp_measurePreserving`). The pull-out needs `M_k`
to be `(⨆ⱼℱⱼ).comap Tᵏ⁺¹`-measurable, which the abstract `ℱ`/`T`/`X` do not supply, so it is
received through `hcoh`: a component-level shift/past coherence stating only that the primitive maps
`X`, `bstar i`, `bstarInf` composed with `T^[i]` (`i ≤ k`) are measurable w.r.t. the epoch-`k+1`
conditioning σ-algebra. `hcoh` is a structural regularity precondition (measurability only; it
encodes no integral, bound, or conditional-expectation inequality), discharged by the concrete
past-filtration/shift instantiation (where `ℱ := pastFiltration` and
`T := shift` make each coordinate `≤ k` measurable w.r.t. `(past).comap Tᵏ⁺¹`). `hpos`/`hint`/
`hint_coord` are market-regularity preconditions; `hInf_dom` is the KT dominance of `bstarInf`,
received (not the proof core), mirroring `condKuhnTucker_infPast`. -/
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
    (hcoh : ∀ k, ∀ i, i ≤ k →
        StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ X (T^[i] ω)) ∧
          StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ bstar i (T^[i] ω)) ∧
            StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ bstarInf (T^[i] ω)))
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
    -- Inductive step: `∫⁻ M_{k+1} ≤ ∫⁻ M_k ≤ 1`, mirroring the Algoet–Cover tower argument
    -- `integral_MRatioLowerZ_le_one` (`SMB/AlgoetCover/TwoSidedRatio.lean`).
    -- Conditioning σ-algebra for epoch `k+1` is `(⨆ⱼℱⱼ).comap (T^[k+1])` (kept as an explicit
    -- expression, not a local instance, to avoid shadowing the ambient `m0`).
    have hsup_le : (⨆ j, ℱ j) ≤ m0 := iSup_le ℱ.le
    have hTmeas : Measurable (T^[k + 1] : Ω → Ω) := hT.measurable.iterate (k + 1)
    have hG_le : (⨆ j, ℱ j).comap (T^[k + 1]) ≤ m0 := by
      intro s ⟨B, hB, hBs⟩
      rw [← hBs]
      exact hTmeas (hsup_le _ hB)
    haveI hSF : SigmaFinite (μ.trim hG_le) := by
      haveI : IsFiniteMeasure (μ.trim hG_le) := isFiniteMeasure_trim hG_le
      infer_instance
    -- The unshifted one-step ratio for competitor `bstar (k+1)` (the KT-form).
    set r : Ω → ℝ := fun ω ↦ (∑ j, bstar (k + 1) ω j * X ω j) / (∑ j, bstarInf ω j * X ω j)
      with hr_def
    have hSb : ∀ ω, (0 : ℝ) < ∑ j, bstarInf ω j * X ω j :=
      fun ω ↦ hpos ω (bstarInf ω) (hInf_simplex ω)
    have hSc : ∀ ω, (0 : ℝ) < ∑ j, bstar (k + 1) ω j * X ω j :=
      fun ω ↦ hpos ω (bstar (k + 1) ω) (hbstar_simplex (k + 1) ω)
    have hr_pos : ∀ ω, 0 < r ω := fun ω ↦ div_pos (hSc ω) (hSb ω)
    have hc' : StronglyMeasurable[⨆ j, ℱ j] (bstar (k + 1)) :=
      (hbstar_meas (k + 1)).mono (le_iSup (fun j ↦ ℱ j) (k + 1))
    have hbInf_m : Measurable bstarInf := (hInf_meas.mono hsup_le).measurable
    have hr_meas : Measurable r := by
      rw [hr_def]
      exact (Finset.measurable_sum _ fun j _ ↦
          ((measurable_pi_apply j).comp (hc'.mono hsup_le).measurable).mul
            ((measurable_pi_apply j).comp hX)).div
        (Finset.measurable_sum _ fun j _ ↦
          ((measurable_pi_apply j).comp hbInf_m).mul ((measurable_pi_apply j).comp hX))
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
      exact stdSimplex_component_le_one (hbstar_simplex (k + 1) ω) i
    -- KT one-step bound at the base point, then transported to epoch `k+1`.
    have hKT : μ[r | ⨆ j, ℱ j] ≤ᵐ[μ] 1 :=
      condKuhnTucker_infPast μ ℱ X hX hpos hint bstarInf hInf_meas hInf_simplex hint_coord hInf_dom
        (bstar (k + 1)) hc' (hbstar_simplex (k + 1))
    have hmp : MeasurePreserving (T^[k + 1]) μ μ := hT.iterate (k + 1)
    have htrans : (fun x ↦ (μ[r | ⨆ j, ℱ j]) (T^[k + 1] x)) =ᵐ[μ]
        μ[fun ω ↦ r (T^[k + 1] ω) | (⨆ j, ℱ j).comap (T^[k + 1])] :=
      InformationTheory.Shannon.TwoSided.condExp_comp_measurePreserving hmp hr_int
        (⨆ j, ℱ j) hsup_le
    have htrans_le : ∀ᵐ x ∂μ, (μ[r | ⨆ j, ℱ j]) (T^[k + 1] x) ≤ 1 := by
      filter_upwards [hmp.quasiMeasurePreserving.ae hKT] with x hx
      simpa using hx
    have hcond_le : μ[fun ω ↦ r (T^[k + 1] ω) | (⨆ j, ℱ j).comap (T^[k + 1])] ≤ᵐ[μ] 1 := by
      filter_upwards [htrans, htrans_le] with x hx_eq hx_le
      rw [← hx_eq]; exact hx_le
    -- Bridge to the ENNReal conditional Lebesgue expectation.
    have hrshift_int : Integrable (fun ω ↦ r (T^[k + 1] ω)) μ :=
      hmp.integrable_comp_of_integrable hr_int
    have hcondL_le : μ⁻[fun ω ↦ ENNReal.ofReal (r (T^[k + 1] ω)) |
        (⨆ j, ℱ j).comap (T^[k + 1])] ≤ᵐ[μ] 1 :=
      condLExp_ofReal_le_one_of_condExp_le_one hG_le μ hrshift_int
        (fun ω ↦ le_of_lt (hr_pos (T^[k + 1] ω))) hcond_le
    -- Growing-history adaptedness of `M_k` from `hcoh`.
    have hMk_meas : Measurable[(⨆ j, ℱ j).comap (T^[k + 1])]
        (wealthRatioProcess X bstar bstarInf T k) := by
      refine Finset.measurable_prod _ fun i hi ↦ ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      obtain ⟨hX_i, hb_i, hInf_i⟩ := hcoh k i hik
      refine Measurable.div ?_ ?_
      · exact Finset.measurable_sum _ fun j _ ↦
          ((measurable_pi_apply j).comp hb_i.measurable).mul
            ((measurable_pi_apply j).comp hX_i.measurable)
      · exact Finset.measurable_sum _ fun j _ ↦
          ((measurable_pi_apply j).comp hInf_i.measurable).mul
            ((measurable_pi_apply j).comp hX_i.measurable)
    -- ρ_{k+1} as an m₀-measurable ENNReal function.
    have hf_meas : Measurable (fun ω ↦ ENNReal.ofReal (r (T^[k + 1] ω))) :=
      ENNReal.measurable_ofReal.comp (hr_meas.comp hTmeas)
    -- Factorization `ofReal M_{k+1} = ofReal M_k · ofReal (r ∘ Tᵏ⁺¹)`.
    have hfact : ∀ ω, ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T (k + 1) ω)
        = ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T k ω)
          * ENNReal.ofReal (r (T^[k + 1] ω)) := by
      intro ω
      have hMprod : wealthRatioProcess X bstar bstarInf T (k + 1) ω
          = wealthRatioProcess X bstar bstarInf T k ω * r (T^[k + 1] ω) := by
        simp only [wealthRatioProcess, hr_def, Finset.prod_range_succ]
      rw [hMprod, ENNReal.ofReal_mul
        (le_of_lt (wealthRatioProcess_pos hpos hbstar_simplex hInf_simplex k ω))]
    -- Assemble: pull `M_k` out, bound the increment condLExp by `1`, apply the IH.
    calc ∫⁻ ω, ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T (k + 1) ω) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T k ω)
            * ENNReal.ofReal (r (T^[k + 1] ω)) ∂μ := by
          exact lintegral_congr fun ω ↦ hfact ω
      _ = ∫⁻ ω, ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T k ω)
            * (μ⁻[fun ω ↦ ENNReal.ofReal (r (T^[k + 1] ω)) |
                (⨆ j, ℱ j).comap (T^[k + 1])]) ω ∂μ :=
          lintegral_mul_eq_lintegral_mul_condLExp hG_le μ
            (ENNReal.measurable_ofReal.comp hMk_meas) hf_meas
      _ ≤ ∫⁻ ω, ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T k ω) * 1 ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hcondL_le] with ω hω
          exact mul_le_mul' le_rfl hω
      _ = ∫⁻ ω, ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T k ω) ∂μ := by
          simp
      _ ≤ 1 := ih

-- Generic Markov + Borel–Cantelli scaffold: a sequence of positive measurable functions whose
-- `ENNReal.ofReal` integrals stay `≤ 1` has `(1/n) log Mₙ` eventually below any positive threshold
-- a.e. Markov gives `μ {(n+1)² ≤ Mₙ} ≤ 1/(n+1)²`; summability of the majorant + Borel–Cantelli
-- yield `Mₙ < (n+1)²` eventually, whence `(1/n) log Mₙ ≤ 2 log(n+1)/(n+1) → 0`.
-- Process-independent: both the upper (`wealthRatioProcess`) and lower (`lowerRatioProcess`)
-- wealth ratios consume it.
private theorem logAvg_eventually_le_of_lintegral_le_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → Ω → ℝ) (hMpos : ∀ n ω, 0 < M n ω) (hMmeas : ∀ n, Measurable (M n))
    (hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal (M n ω) ∂μ ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (M n ω) / (n + 1 : ℝ) ≤ ε := by
  classical
  -- Summable `p`-series majorant `∑ 1/(n+1)²`.
  have hsummable : Summable (fun n : ℕ ↦ (((n:ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    refine ((summable_nat_add_iff 1).mpr h2).congr fun n ↦ ?_
    push_cast
    rw [one_div]
  -- Markov: `μ {(n+1)² ≤ Mₙ} ≤ ofReal (1/(n+1)²)`.
  have hmarkov : ∀ n : ℕ, μ {ω | ((n:ℝ) + 1) ^ 2 ≤ M n ω}
      ≤ ENNReal.ofReal ((((n:ℝ) + 1) ^ 2)⁻¹) := by
    intro n
    have hcrux := hbound n
    have ht_pos : (0 : ℝ) < ((n:ℝ) + 1) ^ 2 := by positivity
    have hmk := mul_meas_ge_le_lintegral₀ (μ := μ)
      (f := fun ω ↦ ENNReal.ofReal (M n ω))
      ((ENNReal.measurable_ofReal.comp (hMmeas n)).aemeasurable) (ENNReal.ofReal (((n:ℝ) + 1) ^ 2))
    have hset : {ω | ENNReal.ofReal (((n:ℝ) + 1) ^ 2) ≤ ENNReal.ofReal (M n ω)}
        = {ω | ((n:ℝ) + 1) ^ 2 ≤ M n ω} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [ENNReal.ofReal_le_ofReal_iff (le_of_lt (hMpos n ω))]
    rw [hset] at hmk
    have hle1 : ENNReal.ofReal (((n:ℝ) + 1) ^ 2)
        * μ {ω | ((n:ℝ) + 1) ^ 2 ≤ M n ω} ≤ 1 :=
      le_trans hmk hcrux
    have hofpos : ENNReal.ofReal (((n:ℝ) + 1) ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact ht_pos
    rw [ENNReal.ofReal_inv_of_pos ht_pos, inv_eq_one_div,
      ENNReal.le_div_iff_mul_le (Or.inl hofpos) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hle1
  -- Borel–Cantelli: a.e. only finitely many `n` have `(n+1)² ≤ Mₙ`.
  have hsum_ne : ∑' (n : ℕ), μ {ω | ((n:ℝ) + 1) ^ 2 ≤ M n ω} ≠ ∞ := by
    have hb : ∑' (n : ℕ), μ {ω | ((n:ℝ) + 1) ^ 2 ≤ M n ω}
        ≤ ENNReal.ofReal (∑' (n : ℕ), (((n:ℝ) + 1) ^ 2)⁻¹) :=
      calc ∑' (n : ℕ), μ {ω | ((n:ℝ) + 1) ^ 2 ≤ M n ω}
          ≤ ∑' (n : ℕ), ENNReal.ofReal ((((n:ℝ) + 1) ^ 2)⁻¹) := ENNReal.tsum_le_tsum hmarkov
        _ = ENNReal.ofReal (∑' (n : ℕ), (((n:ℝ) + 1) ^ 2)⁻¹) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsummable).symm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hbc := ae_finite_setOf_mem (μ := μ)
    (s := fun (n : ℕ) ↦ {ω | ((n:ℝ) + 1) ^ 2 ≤ M n ω}) hsum_ne
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
  have hlt_ev : ∀ᶠ n in atTop, M n ω < ((n:ℝ) + 1) ^ 2 := by
    obtain ⟨N, hN⟩ := hω_fin.bddAbove
    rw [eventually_atTop]
    refine ⟨N + 1, fun n hn ↦ ?_⟩
    rw [← not_le]
    intro hcon
    have : n ≤ N := hN hcon
    omega
  filter_upwards [hlt_ev, hmaj_ev] with n hn_lt hn_maj
  have hMpos' := hMpos n ω
  have hlog : Real.log (M n ω) ≤ 2 * Real.log ((n:ℝ) + 1) := by
    have h := Real.log_lt_log hMpos' hn_lt
    rw [Real.log_pow, Nat.cast_ofNat] at h
    exact le_of_lt h
  have hn1pos : (0 : ℝ) < (n:ℝ) + 1 := by positivity
  calc Real.log (M n ω) / ((n:ℝ) + 1)
      ≤ 2 * Real.log ((n:ℝ) + 1) / ((n:ℝ) + 1) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hlog (le_of_lt (inv_pos.mpr hn1pos))
    _ = 2 * (Real.log ((n:ℝ) + 1) / ((n:ℝ) + 1)) := by ring
    _ ≤ ε := hn_maj

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
        μ[causalLogReturn X c | ⨆ j, ℱ j] ≤ᵐ[μ] μ[causalLogReturn X bstarInf | ⨆ j, ℱ j])
    (hcoh : ∀ k, ∀ i, i ≤ k →
        StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ X (T^[i] ω)) ∧
          StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ bstar i (T^[i] ω)) ∧
            StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ bstarInf (T^[i] ω))) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (wealthRatioProcess X bstar bstarInf T n ω) / (n + 1 : ℝ) ≤ ε := by
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
  have hbound : ∀ n, ∫⁻ ω, ENNReal.ofReal (wealthRatioProcess X bstar bstarInf T n ω) ∂μ ≤ 1 :=
    fun n ↦ wealthRatioProcess_lintegral_le_one μ ℱ hX hT hpos hint hbstar_meas hbstar_simplex
      hInf_meas hInf_simplex hint_coord hInf_dom hcoh n
  exact logAvg_eventually_le_of_lintegral_le_one μ (wealthRatioProcess X bstar bstarInf T)
    hApos hM_meas hbound

-- Lower wealth-ratio process `N_n^{(K)} ω = ∏_{i=K}^{n} (bstar K · Xᵢ)/(bstar i · Xᵢ)` along the
-- shift orbit: the ratio of the fixed finite-memory wealth (strategy `bstar K` at every epoch) to
-- the growing-memory wealth. Tail from epoch `K`; numerator fixed `bstar K`, denominator growing
-- `bstar i`. A nonnegative supermartingale (`∫⁻ Nₙ ≤ 1`); `(1/n) log Nₙ → 0` bounds the shortfall
-- of the growing memory below the fixed-`K` Birkhoff rate, driving the liminf lower bound.
private noncomputable def lowerRatioProcess (X : Ω → Fin m → ℝ) (bstar : ℕ → Ω → Fin m → ℝ)
    (K : ℕ) (T : Ω → Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.Icc K n,
    (∑ j, bstar K (T^[i] ω) j * X (T^[i] ω) j) / (∑ j, bstar i (T^[i] ω) j * X (T^[i] ω) j)

-- The lower wealth-ratio process is positive (a product of positive ratios).
private theorem lowerRatioProcess_pos {X : Ω → Fin m → ℝ} {bstar : ℕ → Ω → Fin m → ℝ} {K : ℕ}
    {T : Ω → Ω}
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m)) (n : ℕ) (ω : Ω) :
    0 < lowerRatioProcess X bstar K T n ω := by
  unfold lowerRatioProcess
  refine Finset.prod_pos fun i _ ↦ div_pos ?_ ?_
  · exact hpos (T^[i] ω) (bstar K (T^[i] ω)) (hbstar_simplex K (T^[i] ω))
  · exact hpos (T^[i] ω) (bstar i (T^[i] ω)) (hbstar_simplex i (T^[i] ω))

-- `log N_n^{(K)}` is the sum of the per-epoch log-return differences (fixed-`K` minus growing).
private theorem lowerRatioProcess_log_eq {X : Ω → Fin m → ℝ} {bstar : ℕ → Ω → Fin m → ℝ} {K : ℕ}
    {T : Ω → Ω}
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m)) (n : ℕ) (ω : Ω) :
    Real.log (lowerRatioProcess X bstar K T n ω)
      = ∑ i ∈ Finset.Icc K n,
        (causalLogReturn X (bstar K) (T^[i] ω) - causalLogReturn X (bstar i) (T^[i] ω)) := by
  unfold lowerRatioProcess
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hnum : (0:ℝ) < ∑ j, bstar K (T^[i] ω) j * X (T^[i] ω) j :=
      hpos (T^[i] ω) (bstar K (T^[i] ω)) (hbstar_simplex K (T^[i] ω))
    have hden : (0:ℝ) < ∑ j, bstar i (T^[i] ω) j * X (T^[i] ω) j :=
      hpos (T^[i] ω) (bstar i (T^[i] ω)) (hbstar_simplex i (T^[i] ω))
    rw [Real.log_div hnum.ne' hden.ne']
    rfl
  · intro i _
    have hnum : (0:ℝ) < ∑ j, bstar K (T^[i] ω) j * X (T^[i] ω) j :=
      hpos (T^[i] ω) (bstar K (T^[i] ω)) (hbstar_simplex K (T^[i] ω))
    have hden : (0:ℝ) < ∑ j, bstar i (T^[i] ω) j * X (T^[i] ω) j :=
      hpos (T^[i] ω) (bstar i (T^[i] ω)) (hbstar_simplex i (T^[i] ω))
    exact div_ne_zero hnum.ne' hden.ne'

-- Stagewise conditional Kuhn–Tucker (fixed-`K` competitor form): at epoch `i` the growing-memory
-- portfolio `bstar i` is conditionally log-optimal over `ℱ i`, so it dominates the earlier
-- `bstar K` (`K ≤ i`, hence `ℱ i`-measurable) and the one-step ratio `(bstar K · X)/(bstar i · X)`
-- has `ℱ i`-conditional mean `≤ 1`. Obtained from `condKuhnTucker_infPast` instantiated at the
-- constant filtration `Filtration.const ℕ (ℱ i)` (whose `⨆` collapses to `ℱ i`), with `bstar i`
-- as the base optimal and `bstar K` as the competitor.
private theorem stagewise_condKuhnTucker [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {X : Ω → Fin m → ℝ}
    [Nonempty (Fin m)] (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ)
    {bstar : ℕ → Ω → Fin m → ℝ} (hbstar_meas : ∀ k, StronglyMeasurable[ℱ k] (bstar k))
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    (hbstar_dom : ∀ (k : ℕ) (c : Ω → Fin m → ℝ), StronglyMeasurable[ℱ k] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ℱ k] ≤ᵐ[μ] μ[causalLogReturn X (bstar k) | ℱ k])
    (hint_coord : ∀ i coord, Integrable (fun ω ↦ X ω coord / (∑ j, bstar i ω j * X ω j)) μ)
    {K i : ℕ} (hKi : K ≤ i) :
    μ[fun ω ↦ (∑ j, bstar K ω j * X ω j) / (∑ j, bstar i ω j * X ω j) | ℱ i] ≤ᵐ[μ] 1 := by
  set ℱ' : Filtration ℕ m0 := Filtration.const ℕ (ℱ i) (ℱ.le i) with hℱ'def
  have hconst : (⨆ j, ℱ' j) = ℱ i := by
    simp only [hℱ'def, Filtration.const_apply, iSup_const]
  have hdom' : ∀ (c : Ω → Fin m → ℝ), StronglyMeasurable[⨆ j, ℱ' j] c →
      (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      μ[causalLogReturn X c | ⨆ j, ℱ' j] ≤ᵐ[μ] μ[causalLogReturn X (bstar i) | ⨆ j, ℱ' j] := by
    intro c hc hcs
    rw [hconst]
    exact hbstar_dom i c (hc.mono (le_of_eq hconst)) hcs
  have hkt := condKuhnTucker_infPast μ ℱ' X hX hpos hint (bstar i)
    ((hbstar_meas i).mono (le_of_eq hconst.symm)) (hbstar_simplex i)
    (fun coord ↦ hint_coord i coord) hdom' (bstar K)
    ((hbstar_meas K).mono (le_trans (ℱ.mono hKi) (le_of_eq hconst.symm))) (hbstar_simplex K)
  rwa [hconst] at hkt

-- Supermartingale integral bound for the lower wealth-ratio process (Cover–Thomas §16.5): the mean
-- fixed-to-growing wealth ratio `E[Nₙ]` stays at most `1`. Mirrors the tower argument of
-- `wealthRatioProcess_lintegral_le_one`, but the per-epoch conditioning σ-algebra is `ℱ i` (not
-- `⨆ⱼℱⱼ`) and the increment bound is the stagewise Kuhn–Tucker `stagewise_condKuhnTucker`
-- (`K ≤ i`), transported to epoch `k+1` via `condExp_comp_measurePreserving`. `hcoh` is the
-- shift/past coherence (measurability only) letting the growing history `N_k` be pulled out of the
-- epoch-`k+1` conditional Lebesgue expectation over `(ℱ (k+1)).comap Tᵏ⁺¹`.
private theorem lowerRatioProcess_lintegral_le_one [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {X : Ω → Fin m → ℝ}
    [Nonempty (Fin m)] (hX : Measurable X) {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ)
    {bstar : ℕ → Ω → Fin m → ℝ} (hbstar_meas : ∀ k, StronglyMeasurable[ℱ k] (bstar k))
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    (hbstar_dom : ∀ (k : ℕ) (c : Ω → Fin m → ℝ), StronglyMeasurable[ℱ k] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ℱ k] ≤ᵐ[μ] μ[causalLogReturn X (bstar k) | ℱ k])
    (hint_coord : ∀ i coord, Integrable (fun ω ↦ X ω coord / (∑ j, bstar i ω j * X ω j)) μ)
    (K : ℕ)
    (hcoh : ∀ k, ∀ i, K ≤ i → i ≤ k →
        StronglyMeasurable[(ℱ (k + 1)).comap (T^[k + 1])] (fun ω ↦ X (T^[i] ω)) ∧
          StronglyMeasurable[(ℱ (k + 1)).comap (T^[k + 1])] (fun ω ↦ bstar i (T^[i] ω)) ∧
            StronglyMeasurable[(ℱ (k + 1)).comap (T^[k + 1])] (fun ω ↦ bstar K (T^[i] ω)))
    (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (lowerRatioProcess X bstar K T n ω) ∂μ ≤ 1 := by
  classical
  induction n with
  | zero =>
    -- `N_0 = ∏_{Icc K 0}`: the empty product (`K > 0`) or the single self-ratio `ρ_K = 1`
    -- (`K = 0`).
    have hN0 : ∀ ω, lowerRatioProcess X bstar K T 0 ω = 1 := by
      intro ω
      unfold lowerRatioProcess
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · subst hK0
        rw [Finset.Icc_self, Finset.prod_singleton]
        exact div_self (ne_of_gt (hpos (T^[0] ω) (bstar 0 (T^[0] ω)) (hbstar_simplex 0 (T^[0] ω))))
      · rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    simp_rw [hN0]
    simp
  | succ k ih =>
    by_cases hKk1 : K ≤ k + 1
    · -- Peel the top factor `Finset.prod_Icc_succ_top`, then KT + pull-out + IH.
      have hTmeas : Measurable (T^[k + 1] : Ω → Ω) := hT.measurable.iterate (k + 1)
      have hℱk1_le : ℱ (k + 1) ≤ m0 := ℱ.le (k + 1)
      have hG_le : (ℱ (k + 1)).comap (T^[k + 1]) ≤ m0 := by
        intro s ⟨B, hB, hBs⟩
        rw [← hBs]
        exact hTmeas (hℱk1_le _ hB)
      haveI hSF : SigmaFinite (μ.trim hG_le) := by
        haveI : IsFiniteMeasure (μ.trim hG_le) := isFiniteMeasure_trim hG_le
        infer_instance
      -- The unshifted one-step ratio (numerator `bstar K`, denominator `bstar (k+1)`).
      set r : Ω → ℝ := fun ω ↦ (∑ j, bstar K ω j * X ω j) / (∑ j, bstar (k + 1) ω j * X ω j)
        with hr_def
      have hSb : ∀ ω, (0 : ℝ) < ∑ j, bstar (k + 1) ω j * X ω j :=
        fun ω ↦ hpos ω (bstar (k + 1) ω) (hbstar_simplex (k + 1) ω)
      have hSc : ∀ ω, (0 : ℝ) < ∑ j, bstar K ω j * X ω j :=
        fun ω ↦ hpos ω (bstar K ω) (hbstar_simplex K ω)
      have hr_pos : ∀ ω, 0 < r ω := fun ω ↦ div_pos (hSc ω) (hSb ω)
      have hbK_m : Measurable (bstar K) := ((hbstar_meas K).mono (ℱ.le K)).measurable
      have hbk1_m : Measurable (bstar (k + 1)) :=
        ((hbstar_meas (k + 1)).mono (ℱ.le (k + 1))).measurable
      have hr_meas : Measurable r := by
        rw [hr_def]
        exact (Finset.measurable_sum _ fun j _ ↦
            ((measurable_pi_apply j).comp hbK_m).mul ((measurable_pi_apply j).comp hX)).div
          (Finset.measurable_sum _ fun j _ ↦
            ((measurable_pi_apply j).comp hbk1_m).mul ((measurable_pi_apply j).comp hX))
      have hr_int : Integrable r μ := by
        have hbound : Integrable (fun ω ↦ ∑ i, X ω i / (∑ j, bstar (k + 1) ω j * X ω j)) μ :=
          integrable_finsetSum Finset.univ fun i _ ↦ hint_coord (k + 1) i
        refine Integrable.mono' hbound hr_meas.aestronglyMeasurable
          (Eventually.of_forall fun ω ↦ ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hr_pos ω))]
        simp only [hr_def]
        rw [Finset.sum_div]
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [mul_div_assoc]
        refine mul_le_of_le_one_left (le_of_lt (div_pos (market_pos hpos ω i) (hSb ω))) ?_
        exact stdSimplex_component_le_one (hbstar_simplex K ω) i
      -- Stagewise KT one-step bound at the base point, transported to epoch `k+1`.
      have hKT : μ[r | ℱ (k + 1)] ≤ᵐ[μ] 1 :=
        stagewise_condKuhnTucker μ ℱ hX hpos hint hbstar_meas hbstar_simplex hbstar_dom
          hint_coord hKk1
      have hmp : MeasurePreserving (T^[k + 1]) μ μ := hT.iterate (k + 1)
      have htrans : (fun x ↦ (μ[r | ℱ (k + 1)]) (T^[k + 1] x)) =ᵐ[μ]
          μ[fun ω ↦ r (T^[k + 1] ω) | (ℱ (k + 1)).comap (T^[k + 1])] :=
        InformationTheory.Shannon.TwoSided.condExp_comp_measurePreserving hmp hr_int
          (ℱ (k + 1)) hℱk1_le
      have htrans_le : ∀ᵐ x ∂μ, (μ[r | ℱ (k + 1)]) (T^[k + 1] x) ≤ 1 := by
        filter_upwards [hmp.quasiMeasurePreserving.ae hKT] with x hx
        simpa using hx
      have hcond_le : μ[fun ω ↦ r (T^[k + 1] ω) | (ℱ (k + 1)).comap (T^[k + 1])] ≤ᵐ[μ] 1 := by
        filter_upwards [htrans, htrans_le] with x hx_eq hx_le
        rw [← hx_eq]; exact hx_le
      have hrshift_int : Integrable (fun ω ↦ r (T^[k + 1] ω)) μ :=
        hmp.integrable_comp_of_integrable hr_int
      have hcondL_le : μ⁻[fun ω ↦ ENNReal.ofReal (r (T^[k + 1] ω)) |
          (ℱ (k + 1)).comap (T^[k + 1])] ≤ᵐ[μ] 1 :=
        condLExp_ofReal_le_one_of_condExp_le_one hG_le μ hrshift_int
          (fun ω ↦ le_of_lt (hr_pos (T^[k + 1] ω))) hcond_le
      -- Growing-history adaptedness of `N_k` from `hcoh`.
      have hNk_meas : Measurable[(ℱ (k + 1)).comap (T^[k + 1])]
          (lowerRatioProcess X bstar K T k) := by
        refine Finset.measurable_prod _ fun i hi ↦ ?_
        rw [Finset.mem_Icc] at hi
        obtain ⟨hKi, hik⟩ := hi
        obtain ⟨hX_i, hb_i, hbK_i⟩ := hcoh k i hKi hik
        refine Measurable.div ?_ ?_
        · exact Finset.measurable_sum _ fun j _ ↦
            ((measurable_pi_apply j).comp hbK_i.measurable).mul
              ((measurable_pi_apply j).comp hX_i.measurable)
        · exact Finset.measurable_sum _ fun j _ ↦
            ((measurable_pi_apply j).comp hb_i.measurable).mul
              ((measurable_pi_apply j).comp hX_i.measurable)
      have hf_meas : Measurable (fun ω ↦ ENNReal.ofReal (r (T^[k + 1] ω))) :=
        ENNReal.measurable_ofReal.comp (hr_meas.comp hTmeas)
      -- Factorization `ofReal N_{k+1} = ofReal N_k · ofReal (r ∘ Tᵏ⁺¹)`.
      have hfact : ∀ ω, ENNReal.ofReal (lowerRatioProcess X bstar K T (k + 1) ω)
          = ENNReal.ofReal (lowerRatioProcess X bstar K T k ω)
            * ENNReal.ofReal (r (T^[k + 1] ω)) := by
        intro ω
        have hMprod : lowerRatioProcess X bstar K T (k + 1) ω
            = lowerRatioProcess X bstar K T k ω * r (T^[k + 1] ω) := by
          simp only [lowerRatioProcess, hr_def]
          rw [Finset.prod_Icc_succ_top hKk1]
        rw [hMprod, ENNReal.ofReal_mul
          (le_of_lt (lowerRatioProcess_pos hpos hbstar_simplex k ω))]
      calc ∫⁻ ω, ENNReal.ofReal (lowerRatioProcess X bstar K T (k + 1) ω) ∂μ
          = ∫⁻ ω, ENNReal.ofReal (lowerRatioProcess X bstar K T k ω)
              * ENNReal.ofReal (r (T^[k + 1] ω)) ∂μ := lintegral_congr fun ω ↦ hfact ω
        _ = ∫⁻ ω, ENNReal.ofReal (lowerRatioProcess X bstar K T k ω)
              * (μ⁻[fun ω ↦ ENNReal.ofReal (r (T^[k + 1] ω)) |
                  (ℱ (k + 1)).comap (T^[k + 1])]) ω ∂μ :=
            lintegral_mul_eq_lintegral_mul_condLExp hG_le μ
              (ENNReal.measurable_ofReal.comp hNk_meas) hf_meas
        _ ≤ ∫⁻ ω, ENNReal.ofReal (lowerRatioProcess X bstar K T k ω) * 1 ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hcondL_le] with ω hω
            exact mul_le_mul' le_rfl hω
        _ = ∫⁻ ω, ENNReal.ofReal (lowerRatioProcess X bstar K T k ω) ∂μ := by simp
        _ ≤ 1 := ih
    · -- `K > k+1` ⟹ `Icc K (k+1) = ∅` ⟹ `N_{k+1} = 1`.
      have hN : ∀ ω, lowerRatioProcess X bstar K T (k + 1) ω = 1 := by
        intro ω
        unfold lowerRatioProcess
        rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty]
      simp_rw [hN]
      simp

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
preconditions. `hcoh` is the shift/past coherence (measurability only) letting the wealth-ratio
supermartingale bound pull the growing history out of the epoch-`k+1` conditional expectation;
it holds for the concrete past-filtration/shift instantiation. -/
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
        μ[causalLogReturn X c | ⨆ j, ℱ j] ≤ᵐ[μ] μ[causalLogReturn X bstarInf | ⨆ j, ℱ j])
    (hcoh : ∀ k, ∀ i, i ≤ k →
        StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ X (T^[i] ω)) ∧
          StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ bstar i (T^[i] ω)) ∧
            StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ bstarInf (T^[i] ω))) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      growingMemoryLogAvg X bstar T n ω ≤ condOptGrowthInfty μ X bstar + ε := by
  have hbstarInf_measurable : Measurable bstarInf := (hInf_meas.mono (iSup_le ℱ.le)).measurable
  have hid : ∫ ω, causalLogReturn X bstarInf ω ∂μ = condOptGrowthInfty μ X bstar :=
    condOptGrowthInfty_eq_integral_infPast μ ℱ X hX hpos hint bstar hbstar_meas hbstar_simplex
      hbstar_dom bstarInf hInf_meas hInf_simplex hInf_dom
  have hbirk := birkhoff_ergodic_ae hT hT_erg (hint bstarInf hbstarInf_measurable hInf_simplex)
  have hupper := wealthRatio_logAvg_eventually_le μ ℱ hX hT hpos hint hbstar_meas hbstar_simplex
    hInf_meas hInf_simplex hint_coord hInf_dom hcoh
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

/-- Lower half of the growing-memory `W_∞` AEP (Cover–Thomas Theorem 16.5.1): the growing-memory
log-wealth average is eventually above `W_∞ = condOptGrowthInfty` down to any margin `ε`, almost
surely. For a fixed finite memory `K`, the growing-memory returns dominate the fixed-`K` strategy up
to the lower wealth ratio: `growingMemoryLogAvg n = (1/n) ∑ᵢ log(bstar K · Xᵢ) + (head)/n
− (1/n) log Nₙ^{(K)}`, where the first term converges to
`∫ log(bstar K · X) = condOptGrowth K = W*_K` by Birkhoff's ergodic theorem, the head (a finite
`ω`-constant) vanishes, and `(1/n) log Nₙ^{(K)}` is eventually below any positive threshold
(`logAvg_eventually_le_of_lintegral_le_one`, from the lower-ratio supermartingale bound
`lowerRatioProcess_lintegral_le_one`). Since `W*_K ↑ W_∞` (`condOptGrowth_monotone` +
`condOptGrowth_bddAbove`, the monotone convergence for this `bstar`), choosing `K` with
`W*_K > W_∞ − ε/2` yields `growingMemoryLogAvg n ≥ W_∞ − ε` eventually. `W_∞` is not
received as a hypothesis: it is pinned constructively as the supremum of the `W*_K`, and the `K` for
each `ε` is chosen deterministically (`ω`-independent) from the monotone limit, so the almost-sure
set is the countable intersection over `K ∈ ℕ` of the Birkhoff and lower-ratio a.e. sets. `hcoh` is
the shift/past coherence (measurability only). Combined with the upper half
(`growingMemory_eventually_le_condOptGrowthInfty`) this gives almost-sure convergence to `W_∞`. -/
theorem growingMemory_eventually_ge_condOptGrowthInfty [StandardBorelSpace Ω] [Nonempty Ω]
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
    (hint_coord : ∀ i coord, Integrable (fun ω ↦ X ω coord / (∑ j, bstar i ω j * X ω j)) μ)
    (hUB : ∃ C : ℝ, ∀ c : Ω → Fin m → ℝ, (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ → ∫ ω, causalLogReturn X c ω ∂μ ≤ C)
    (hcoh : ∀ (K : ℕ), ∀ k, ∀ i, K ≤ i → i ≤ k →
        StronglyMeasurable[(ℱ (k + 1)).comap (T^[k + 1])] (fun ω ↦ X (T^[i] ω)) ∧
          StronglyMeasurable[(ℱ (k + 1)).comap (T^[k + 1])] (fun ω ↦ bstar i (T^[i] ω)) ∧
            StronglyMeasurable[(ℱ (k + 1)).comap (T^[k + 1])] (fun ω ↦ bstar K (T^[i] ω))) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      condOptGrowthInfty μ X bstar - ε ≤ growingMemoryLogAvg X bstar T n ω := by
  have hintb : ∀ k, Integrable (causalLogReturn X (bstar k)) μ := fun k ↦
    hint (bstar k) ((hbstar_meas k).mono (ℱ.le k)).measurable (hbstar_simplex k)
  -- `W*_K ↑ W_∞`: monotone convergence for this `bstar`.
  have hmono := condOptGrowth_monotone μ ℱ X bstar hbstar_meas hbstar_simplex hbstar_dom
  have hbdd := condOptGrowth_bddAbove μ X bstar hbstar_simplex hintb hUB
  have hWconv : Tendsto (condOptGrowth μ X bstar) atTop (𝓝 (condOptGrowthInfty μ X bstar)) :=
    tendsto_atTop_ciSup hmono hbdd
  -- Countable a.e. intersection over `K`: Birkhoff convergence + lower-ratio eventual bound.
  have hcombined : ∀ᵐ ω ∂μ, ∀ K : ℕ,
      Tendsto (fun n ↦ (∑ i ∈ Finset.range (n + 1),
          causalLogReturn X (bstar K) (T^[i] ω)) / (n + 1 : ℝ)) atTop
        (𝓝 (condOptGrowth μ X bstar K))
      ∧ (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          Real.log (lowerRatioProcess X bstar K T n ω) / (n + 1 : ℝ) ≤ ε) := by
    rw [ae_all_iff]
    intro K
    have hbstar_m : ∀ a, Measurable (bstar a) := fun a ↦ ((hbstar_meas a).mono (ℱ.le a)).measurable
    have hTi : ∀ i, Measurable (T^[i] : Ω → Ω) := fun i ↦ hT.measurable.iterate i
    have hNmeas : ∀ n, Measurable (lowerRatioProcess X bstar K T n) := by
      intro n
      refine Finset.measurable_prod _ fun i _ ↦ Measurable.div ?_ ?_
      · exact Finset.measurable_sum _ fun j _ ↦
          ((measurable_pi_apply j).comp ((hbstar_m K).comp (hTi i))).mul
            ((measurable_pi_apply j).comp (hX.comp (hTi i)))
      · exact Finset.measurable_sum _ fun j _ ↦
          ((measurable_pi_apply j).comp ((hbstar_m i).comp (hTi i))).mul
            ((measurable_pi_apply j).comp (hX.comp (hTi i)))
    have hbirk_K := birkhoff_ergodic_ae hT hT_erg (hintb K)
    have hlow_K := logAvg_eventually_le_of_lintegral_le_one μ (lowerRatioProcess X bstar K T)
      (fun n ω ↦ lowerRatioProcess_pos hpos hbstar_simplex n ω) hNmeas
      (fun n ↦ lowerRatioProcess_lintegral_le_one μ ℱ hX hT hpos hint hbstar_meas
        hbstar_simplex hbstar_dom hint_coord K (hcoh K) n)
    filter_upwards [hbirk_K, hlow_K] with ω h1 h2
    refine ⟨?_, h2⟩
    have heq : condOptGrowth μ X bstar K = ∫ x, causalLogReturn X (bstar K) x ∂μ := rfl
    rw [heq]
    exact h1
  filter_upwards [hcombined] with ω hω
  intro ε hε
  -- Choose `K` with `W*_K > W_∞ − ε/2` (deterministic, `ω`-independent).
  obtain ⟨K, hK⟩ := (hWconv.eventually (Ioi_mem_nhds
    (show condOptGrowthInfty μ X bstar - ε / 2 < condOptGrowthInfty μ X bstar by linarith))).exists
  obtain ⟨hbirk_ω, hlow_ω⟩ := hω K
  set head : ℝ := ∑ i ∈ Finset.range K,
    (causalLogReturn X (bstar i) (T^[i] ω) - causalLogReturn X (bstar K) (T^[i] ω)) with hhead
  have hhead_tendsto : Tendsto (fun n : ℕ ↦ head / (n + 1 : ℝ)) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    exact tendsto_const_nhds.div_atTop hnat
  have hA_ev := hbirk_ω.eventually (Ioi_mem_nhds
    (show condOptGrowth μ X bstar K - ε / 6 < condOptGrowth μ X bstar K by linarith))
  have hhead_ev := hhead_tendsto.eventually (Ioi_mem_nhds (show -(ε / 6) < (0 : ℝ) by linarith))
  have hC_ev := hlow_ω (ε / 6) (by linarith)
  have hKn_ev : ∀ᶠ n in atTop, K ≤ n := eventually_atTop.mpr ⟨K, fun n hn ↦ hn⟩
  filter_upwards [hA_ev, hhead_ev, hC_ev, hKn_ev] with n hA hHead hC hKn
  -- Decompose the growing-memory average into the fixed-`K` Birkhoff sum, head, and lower ratio.
  have hpa : ∑ i ∈ Finset.range (n + 1), causalLogReturn X (bstar i) (T^[i] ω)
      = ∑ i ∈ Finset.range K, causalLogReturn X (bstar i) (T^[i] ω)
        + ∑ i ∈ Finset.Icc K n, causalLogReturn X (bstar i) (T^[i] ω) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, ← Finset.Ico_add_one_right_eq_Icc K n]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le K) (by omega)).symm
  have hpf : ∑ i ∈ Finset.range (n + 1), causalLogReturn X (bstar K) (T^[i] ω)
      = ∑ i ∈ Finset.range K, causalLogReturn X (bstar K) (T^[i] ω)
        + ∑ i ∈ Finset.Icc K n, causalLogReturn X (bstar K) (T^[i] ω) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico, ← Finset.Ico_add_one_right_eq_Icc K n]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le K) (by omega)).symm
  have hnum : ∑ i ∈ Finset.range (n + 1), causalLogReturn X (bstar i) (T^[i] ω)
      = (∑ i ∈ Finset.range (n + 1), causalLogReturn X (bstar K) (T^[i] ω)) + head
        - Real.log (lowerRatioProcess X bstar K T n ω) := by
    rw [lowerRatioProcess_log_eq hpos hbstar_simplex, hhead]
    simp only [Finset.sum_sub_distrib]
    rw [hpa, hpf]
    ring
  have hdecomp : growingMemoryLogAvg X bstar T n ω
      = (∑ i ∈ Finset.range (n + 1), causalLogReturn X (bstar K) (T^[i] ω)) / (n + 1 : ℝ)
        + head / (n + 1 : ℝ)
        - Real.log (lowerRatioProcess X bstar K T n ω) / (n + 1 : ℝ) := by
    unfold growingMemoryLogAvg
    rw [hnum]
    ring
  rw [hdecomp]
  linarith

/-- Growing-memory `W_∞` AEP (Cover–Thomas Theorem 16.5.1): the growing-memory log-wealth average
converges almost surely to the infinite-past optimal growth rate `W_∞ = condOptGrowthInfty`. This
is the Algoet–Cover sandwich: the eventual upper bound `≤ W_∞ + ε`
(`growingMemory_eventually_le_condOptGrowthInfty`, from the wealth-ratio supermartingale against the
infinite-past optimal `bstarInf`) and the eventual lower bound `≥ W_∞ − ε`
(`growingMemory_eventually_ge_condOptGrowthInfty`, from the fixed-memory Birkhoff rates rising to
`W_∞`) pinch the average to `W_∞`. `bstar`/`bstarInf` are the stagewise/infinite-past conditional
log-optimal selections (constructed separately via `exists_condLogOptimalSeq` /
`exists_infPast_condLogOptimal`); the remaining hypotheses are market-regularity/ergodicity
preconditions and the two measurability-only shift/past coherences (`hcoh_inf` at `⨆ⱼℱⱼ` for the
upper half, `hcoh` at each `ℱ (k+1)` for the lower). -/
theorem growingMemory_logWealth_tendsto_condOptGrowthInfty [StandardBorelSpace Ω] [Nonempty Ω]
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
    (hint_coord : ∀ i coord, Integrable (fun ω ↦ X ω coord / (∑ j, bstar i ω j * X ω j)) μ)
    (hUB : ∃ C : ℝ, ∀ c : Ω → Fin m → ℝ, (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ → ∫ ω, causalLogReturn X c ω ∂μ ≤ C)
    (hcoh : ∀ (K : ℕ), ∀ k, ∀ i, K ≤ i → i ≤ k →
        StronglyMeasurable[(ℱ (k + 1)).comap (T^[k + 1])] (fun ω ↦ X (T^[i] ω)) ∧
          StronglyMeasurable[(ℱ (k + 1)).comap (T^[k + 1])] (fun ω ↦ bstar i (T^[i] ω)) ∧
            StronglyMeasurable[(ℱ (k + 1)).comap (T^[k + 1])] (fun ω ↦ bstar K (T^[i] ω)))
    (bstarInf : Ω → Fin m → ℝ) (hInf_meas : StronglyMeasurable[⨆ j, ℱ j] bstarInf)
    (hInf_simplex : ∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m))
    (hint_coord_inf : ∀ i, Integrable (fun ω ↦ X ω i / (∑ j, bstarInf ω j * X ω j)) μ)
    (hInf_dom : ∀ (c : Ω → Fin m → ℝ), StronglyMeasurable[⨆ j, ℱ j] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ⨆ j, ℱ j] ≤ᵐ[μ] μ[causalLogReturn X bstarInf | ⨆ j, ℱ j])
    (hcoh_inf : ∀ k, ∀ i, i ≤ k →
        StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ X (T^[i] ω)) ∧
          StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ bstar i (T^[i] ω)) ∧
            StronglyMeasurable[(⨆ j, ℱ j).comap (T^[k + 1])] (fun ω ↦ bstarInf (T^[i] ω))) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ growingMemoryLogAvg X bstar T n ω) atTop
        (𝓝 (condOptGrowthInfty μ X bstar)) := by
  have hup := growingMemory_eventually_le_condOptGrowthInfty μ hT hT_erg ℱ X hX hpos hint bstar
    hbstar_meas hbstar_simplex hbstar_dom bstarInf hInf_meas hInf_simplex hint_coord_inf hInf_dom
    hcoh_inf
  have hlo := growingMemory_eventually_ge_condOptGrowthInfty μ hT hT_erg ℱ X hX hpos hint bstar
    hbstar_meas hbstar_simplex hbstar_dom hint_coord hUB hcoh
  filter_upwards [hup, hlo] with ω hup_ω hlo_ω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Filter.Eventually.and (hup_ω (ε / 2) (by linarith)) (hlo_ω (ε / 2) (by linarith)))
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨hhi, hlo2⟩ := hN n hn
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end CondOptimalGrowth

end InformationTheory.Shannon.Portfolio
