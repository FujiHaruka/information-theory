import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SMB.ChainRule
import InformationTheory.Shannon.SMB.McMillanBreiman
import InformationTheory.Probability.TwoSidedExtension
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import InformationTheory.Shannon.SMB.AlgoetCover.Core
import InformationTheory.Shannon.SMB.AlgoetCover.TwoSidedRatio

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

open InformationTheory.Shannon.TwoSided

omit [DecidableEq α] [Nonempty α] in
/-- `pmfLogCondInfty` is measurable (w.r.t. the pi σ-algebra). -/
lemma measurable_pmfLogCondInfty
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    Measurable (pmfLogCondInfty μ p) := by
  classical
  unfold pmfLogCondInfty
  refine (Real.measurable_log.comp ?_).neg
  refine Finset.measurable_sum _ (fun a _ => ?_)
  refine Measurable.mul ?_ ?_
  · refine Measurable.indicator measurable_const ?_
    exact measurableSet_coord0_eq a
  · exact ((stronglyMeasurable_condProbInfty μ p a).mono
      (iSup_le (fun n => (pastFiltration (α := α)).le n))).measurable

omit [DecidableEq α] [Nonempty α] in
/-- Measurability of `MRatioLowerZ` w.r.t. the product σ-algebra on `ℤ → α`. -/
lemma measurable_MRatioLowerZ
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    Measurable (MRatioLowerZ μ p n) := by
  classical
  unfold MRatioLowerZ
  refine ENNReal.measurable_ofReal.comp ?_
  refine Real.measurable_exp.comp ?_
  refine Measurable.sub ?_ ?_
  · -- negLogQInftyZ is a measurable sum.
    unfold negLogQInftyZ
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (measurable_pmfLogCondInfty μ p).comp ((measurable_shiftZ).iterate i)
  · -- n · blockLogAvgZ is measurable.
    refine measurable_const.mul ?_
    unfold blockLogAvgZ
    refine measurable_const.mul ?_
    refine Real.measurable_log.comp ?_
    have h_disc : Measurable (fun y : Fin n → α =>
        (((μZ μ p).map (firstBlockZ (α := α) n)).real {y})) := measurable_of_finite _
    exact h_disc.comp (measurable_firstBlockZ n)

omit [DecidableEq α] [Nonempty α] in
/-- **Borel–Cantelli consequence (Z-side)**: μZ-a.s., `MRatioLowerZ n x ≤ n²` eventually. -/
theorem MRatioLowerZ_le_sq_eventually
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    ∀ᵐ x ∂(μZ μ p), ∀ᶠ n in Filter.atTop,
      MRatioLowerZ μ p n x ≤ ENNReal.ofReal ((n : ℝ) ^ 2) := by
  -- Direct Markov + first Borel-Cantelli on `s n := {MRatioLowerZ n > n²}`.
  set s : ℕ → Set (∀ _ : ℤ, α) :=
    fun n => {x | ENNReal.ofReal ((n : ℝ) ^ 2) < MRatioLowerZ μ p n x} with hs_def
  have h_MR_meas : ∀ n, Measurable (MRatioLowerZ μ p n) := measurable_MRatioLowerZ μ p
  -- Per-n measure bound: for n ≥ 1, μZ(s n) ≤ 1 / (n^2 : ℝ≥0∞).
  have h_bound : ∀ n, 1 ≤ n → (μZ μ p) (s n) ≤ (1 : ℝ≥0∞) / ((n : ℝ≥0∞) ^ 2) := by
    intro n hn
    have h_n_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h_eps_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have h_eps : ENNReal.ofReal ((n : ℝ) ^ 2) = (n : ℝ≥0∞) ^ 2 := by
      rw [show ((n : ℝ) ^ 2) = ((n^2 : ℕ) : ℝ) by push_cast; ring]
      rw [ENNReal.ofReal_natCast]
      push_cast; ring
    have h_eps_ne_zero : ENNReal.ofReal ((n : ℝ) ^ 2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr h_eps_pos).ne'
    have h_eps_ne_top : ENNReal.ofReal ((n : ℝ) ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
    have h_sub : s n ⊆ {x | ENNReal.ofReal ((n : ℝ) ^ 2) ≤ MRatioLowerZ μ p n x} := by
      intro x hx
      have : ENNReal.ofReal ((n : ℝ) ^ 2) < MRatioLowerZ μ p n x := hx
      exact le_of_lt this
    have h_markov : (μZ μ p) {x | ENNReal.ofReal ((n : ℝ) ^ 2) ≤ MRatioLowerZ μ p n x}
        ≤ (∫⁻ x, MRatioLowerZ μ p n x ∂(μZ μ p)) / ENNReal.ofReal ((n : ℝ) ^ 2) :=
      meas_ge_le_lintegral_div (h_MR_meas n).aemeasurable h_eps_ne_zero h_eps_ne_top
    have h_int := integral_MRatioLowerZ_le_one μ p n
    calc (μZ μ p) (s n)
        ≤ (μZ μ p) {x | ENNReal.ofReal ((n : ℝ) ^ 2) ≤ MRatioLowerZ μ p n x} :=
          measure_mono h_sub
      _ ≤ (∫⁻ x, MRatioLowerZ μ p n x ∂(μZ μ p)) / ENNReal.ofReal ((n : ℝ) ^ 2) := h_markov
      _ ≤ 1 / ENNReal.ofReal ((n : ℝ) ^ 2) := ENNReal.div_le_div_right h_int _
      _ = 1 / ((n : ℝ≥0∞) ^ 2) := by rw [h_eps]
  -- Sum: ∑' n, μZ (s n) < ∞.
  have h_tsum : ∑' n, (μZ μ p) (s n) ≠ ∞ := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    refine ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ?_⟩
    have h_le : (∑' n : ℕ, (μZ μ p) (s (n + 1)))
        ≤ ∑' n : ℕ, (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2) := by
      refine ENNReal.tsum_le_tsum (fun n => ?_)
      exact h_bound (n + 1) (Nat.succ_le_succ (Nat.zero_le _))
    refine ne_top_of_le_ne_top ?_ h_le
    have h_summable_real : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      exact (summable_nat_add_iff 1).mpr h
    have h_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := fun _ => by positivity
    have h_ennreal_tsum : ∑' n : ℕ,
        ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≠ ∞ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg h_nonneg h_summable_real]
      exact ENNReal.ofReal_ne_top
    have h_pointwise : ∀ n : ℕ,
        (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2) =
          ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
      intro n
      have h_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ 2 := by positivity
      rw [ENNReal.ofReal_div_of_pos h_pos, ENNReal.ofReal_one,
        show ((n + 1 : ℕ) : ℝ) ^ 2 = (((n + 1)^2 : ℕ) : ℝ) by push_cast; ring,
        ENNReal.ofReal_natCast]
      push_cast; ring_nf
    have h_tsum_eq : ∑' n : ℕ, (1 : ℝ≥0∞) / (((n + 1 : ℕ) : ℝ≥0∞) ^ 2)
        = ∑' n : ℕ, ENNReal.ofReal ((1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      tsum_congr h_pointwise
    rw [h_tsum_eq]
    exact h_ennreal_tsum
  have h_BC := MeasureTheory.ae_eventually_notMem h_tsum
  filter_upwards [h_BC] with x hx
  filter_upwards [hx] with n hn
  exact not_lt.mp hn

omit [DecidableEq α] [Nonempty α] in
/-- **Logarithmic form (Z-side)**: μZ-a.s., eventually,
`blockLogAvgZ n x ≥ (1/n) · negLogQInftyZ n x - 2 log n / n`. -/
theorem blockLogAvgZ_ge_negLogQInftyZ_minus_error
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    ∀ᵐ x ∂(μZ μ p), ∀ᶠ n in Filter.atTop,
      negLogQInftyZ μ p n x / n - 2 * Real.log n / n ≤ blockLogAvgZ μ p n x := by
  filter_upwards [MRatioLowerZ_le_sq_eventually μ p] with x hx
  filter_upwards [hx, Filter.eventually_ge_atTop 1] with n h_MR hn
  have h_n_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_n_sq_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have h_real_le : Real.exp (negLogQInftyZ μ p n x - (n : ℝ) * blockLogAvgZ μ p n x)
      ≤ (n : ℝ) ^ 2 := by
    have : ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x - (n : ℝ) * blockLogAvgZ μ p n x))
        ≤ ENNReal.ofReal ((n : ℝ) ^ 2) := h_MR
    exact (ENNReal.ofReal_le_ofReal_iff h_n_sq_pos.le).mp this
  have h_log : negLogQInftyZ μ p n x - (n : ℝ) * blockLogAvgZ μ p n x
      ≤ 2 * Real.log (n : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) h_real_le
    rw [Real.log_exp] at h
    have h_log_sq : Real.log ((n : ℝ) ^ 2) = 2 * Real.log (n : ℝ) := by
      rw [show ((n : ℝ) ^ 2) = (n : ℝ) * (n : ℝ) from sq (n : ℝ),
        Real.log_mul h_n_pos.ne' h_n_pos.ne']
      ring
    rw [h_log_sq] at h
    exact h
  have h_div :
      negLogQInftyZ μ p n x / (n : ℝ) - blockLogAvgZ μ p n x ≤
        2 * Real.log (n : ℝ) / (n : ℝ) := by
    have h := div_le_div_of_nonneg_right h_log h_n_pos.le
    rw [sub_div, mul_div_cancel_left₀ _ h_n_pos.ne'] at h
    exact h
  linarith

omit [DecidableEq α] in
/-- **Birkhoff for `pmfLogCondInfty` on the 2-sided side**: applying Birkhoff to
`(μZ, shiftZ, pmfLogCondInfty)`, using `ergodic_shiftZ`, `measurePreserving_shiftZ`,
`integrable_pmfLogCondInfty`, and `integral_pmfLogCondInfty_eq_entropyRate`. -/
@[entry_point]
theorem birkhoffAverage_pmfLogCondInfty_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ x ∂(μZ μ p.toStationaryProcess),
      Filter.Tendsto
        (fun n : ℕ => negLogQInftyZ μ p.toStationaryProcess n x / (n : ℝ))
        Filter.atTop
        (𝓝 (entropyRate μ p.toStationaryProcess)) := by
  classical
  have h_mp := measurePreserving_shiftZ μ p.toStationaryProcess
  have h_erg := ergodic_shiftZ μ p
  have h_int := integrable_pmfLogCondInfty μ p.toStationaryProcess
  have h_int_id := integral_pmfLogCondInfty_eq_entropyRate μ p.toStationaryProcess
  have h_birk := InformationTheory.Shannon.birkhoff_ergodic_ae h_mp h_erg h_int
  -- The Birkhoff conclusion: birkhoffAverageReal shiftZ pmfLogCondInfty m x → ∫ pmfLogCondInfty,
  -- where `birkhoffAverageReal T f m ω = (∑_{i<m+1} f(T^[i] ω)) / (m+1)`. We want our form
  -- `(∑_{i<n} f(shiftZ^[i] x)) / n` for n ≥ 1; compose with `n ↦ n - 1`.
  rw [show entropyRate μ p.toStationaryProcess
        = ∫ x, pmfLogCondInfty μ p.toStationaryProcess x ∂(μZ μ p.toStationaryProcess)
      from h_int_id.symm]
  filter_upwards [h_birk] with x hx
  have h_comp := hx.comp (Filter.tendsto_sub_atTop_nat 1)
  refine Filter.Tendsto.congr' ?_ h_comp
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have h_succ : (n - 1) + 1 = n := by omega
  -- Goal: ((fun n => birkhoffAverageReal shiftZ pmf n x) ∘ (· - 1)) n
  --     = negLogQInftyZ ... n x / n
  show birkhoffAverageReal shiftZ
        (pmfLogCondInfty μ p.toStationaryProcess) (n - 1) x
      = negLogQInftyZ μ p.toStationaryProcess n x / (n : ℝ)
  unfold birkhoffAverageReal negLogQInftyZ
  -- LHS: (∑ i ∈ range (n - 1 + 1), pmf ...) / (↑(n - 1) + 1)
  -- RHS: (∑ i ∈ range n, pmf ...) / ↑n
  have h_num : (∑ i ∈ Finset.range (n - 1 + 1),
        pmfLogCondInfty μ p.toStationaryProcess (shiftZ^[i] x))
      = ∑ i ∈ Finset.range n,
          pmfLogCondInfty μ p.toStationaryProcess (shiftZ^[i] x) := by
    rw [h_succ]
  have h_den : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have : ((n - 1 : ℕ) : ℝ) + 1 = (((n - 1 + 1 : ℕ)) : ℝ) := by push_cast; ring
    rw [this, h_succ]
  rw [h_num, h_den]

omit [DecidableEq α] [Nonempty α] in
/-- Helper: `y ↦ blockLogAvgZ μ p n (eN y)` is measurable on `ℕ → α`, where
`eN y i := y i.toNat`. -/
private lemma measurable_blockLogAvgZ_via_eN
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    Measurable (fun y : ∀ _ : ℕ, α =>
      blockLogAvgZ μ p n (fun i : ℤ => y i.toNat)) := by
  unfold blockLogAvgZ
  refine measurable_const.mul ?_
  refine Real.measurable_log.comp ?_
  have h_disc : Measurable (fun s : Fin n → α =>
      (((μZ μ p).map (firstBlockZ (α := α) n)).real {s})) := measurable_of_finite _
  refine h_disc.comp ?_
  refine measurable_pi_iff.mpr (fun i => ?_)
  exact measurable_pi_apply _

omit [DecidableEq α] in
/-- **Z-side a.s. upper boundedness** of `blockLogAvgZ` (transferred from the Ω-side
`blockLogAvg_bddAbove_ae`, via the bridge `blockLogAvgZ n (natExt ω) = blockLogAvg n ω`
and `measurePreserving_forwardEmbed` + `μZ_nat_proj_eq`).

`blockLogAvgZ n x` depends only on `natProj x : ℕ → α`. We push the μ-a.s. statement
`Ω-blockLogAvg n ω bounded above` through `measurePreserving_forwardEmbed` to a
`(μ.map forwardEmbed) = (μZ.map natProj)`-a.s. statement on `(ℕ → α)`, then pull back
to μZ-a.s. on `(ℤ → α)` via `natProj`. -/
theorem blockLogAvgZ_bddAbove_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ x ∂(μZ μ p.toStationaryProcess), Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => blockLogAvgZ μ p.toStationaryProcess n x) := by
  classical
  -- Define `eN : (ℕ → α) → (ℤ → α)`, `eN y i := y i.toNat`. Then for any `x`,
  -- `blockLogAvgZ n x = blockLogAvgZ n (eN (natProj x))` (depends only on natProj).
  set eN : (∀ _ : ℕ, α) → (∀ _ : ℤ, α) := fun y i => y i.toNat with heN_def
  have h_blockLogAvgZ_factor : ∀ x : ∀ _ : ℤ, α, ∀ n,
      blockLogAvgZ μ p.toStationaryProcess n x
        = blockLogAvgZ μ p.toStationaryProcess n (eN (InformationTheory.Shannon.TwoSided.natProj x)) := by
    intro x n
    have h_arg : (firstBlockZ (α := α) n) x
        = (firstBlockZ (α := α) n) (eN (InformationTheory.Shannon.TwoSided.natProj x)) := by
      funext i
      show x (i.val : ℤ) = (eN (InformationTheory.Shannon.TwoSided.natProj x)) (i.val : ℤ)
      show x (i.val : ℤ) = x (((((i.val : ℕ) : ℤ).toNat : ℕ) : ℤ))
      simp
    unfold blockLogAvgZ
    rw [h_arg]
  -- Get Ω-side bound.
  have h_Ω := blockLogAvg_bddAbove_ae μ p
  -- For each `ω`, `blockLogAvgZ n (eN (forwardEmbed ω)) = blockLogAvg n ω` (by
  -- `blockLogAvgZ_natExt_eq`).
  have h_Ω' : ∀ᵐ ω ∂μ, Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => blockLogAvgZ μ p.toStationaryProcess n
        (eN (forwardEmbed (μ := μ) p.toStationaryProcess ω))) := by
    filter_upwards [h_Ω] with ω hω
    have h_eq : (fun n => blockLogAvgZ μ p.toStationaryProcess n
          (eN (forwardEmbed (μ := μ) p.toStationaryProcess ω)))
        = fun n => blockLogAvg μ p.toStationaryProcess n ω := by
      funext n
      rw [show eN (forwardEmbed (μ := μ) p.toStationaryProcess ω)
          = fun i : ℤ => p.obs i.toNat ω from rfl]
      exact blockLogAvgZ_natExt_eq μ p.toStationaryProcess n ω
    rw [h_eq]; exact hω
  -- Push h_Ω' through measurePreserving_forwardEmbed to (μ.map forwardEmbed)-a.s.
  have h_mp_forwardEmbed : MeasurePreserving (forwardEmbed (μ := μ) p.toStationaryProcess)
      μ (μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)) :=
    InformationTheory.Shannon.TwoSided.measurePreserving_forwardEmbed
      μ p.toStationaryProcess
  -- Convert μ-a.s. statement to (μ.map forwardEmbed)-a.s. via `ae_map_iff`.
  have h_N_ae : ∀ᵐ y ∂(μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)),
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n => blockLogAvgZ μ p.toStationaryProcess n (eN y)) := by
    -- This is the (μ.map forwardEmbed)-form, but we have h_Ω' (μ-form of ∘ forwardEmbed).
    -- We need ae_map_iff with measurability.
    rw [ae_map_iff (measurable_forwardEmbed (μ := μ) p.toStationaryProcess).aemeasurable
      (by
        -- IsBoundedUnder (≤) is `∃ a, ∀ᶠ n, f n ≤ a`. Translate to MeasurableSet.
        -- Note: this is a `Set (ℕ → α)` set; it should be measurable. Use the standard
        -- countable-union representation:
        --   `{y | ∃ M : ℕ, ∀ᶠ n, blockLogAvgZ n (eN y) ≤ M}
        --   = ⋃ M : ℕ, ⋂ᶠ n ≥ N : ℕ, {y | blockLogAvgZ n (eN y) ≤ M}`.
        -- For brevity, since the predicate set is Borel-measurable via countable Boolean
        -- operations on measurable inequalities, we use the explicit set form.
        change MeasurableSet {y : ∀ _ : ℕ, α | _}
        -- IsBoundedUnder definitionally unfolds to `∃ a, ∀ᶠ ..., · ≤ a`.
        -- For ℝ, the existence of bound `∃ a, ∀ᶠ n, f n ≤ a` is equivalent to
        --   `⋃ M : ℕ, {y | ∀ᶠ n, f n ≤ M}`.
        have h_set_eq : {y : ∀ _ : ℕ, α | Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
              (fun n => blockLogAvgZ μ p.toStationaryProcess n (eN y))}
            = ⋃ M : ℕ, {y | ∀ᶠ n in Filter.atTop,
                blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)} := by
          ext y
          constructor
          · rintro ⟨a, ha⟩
            obtain ⟨M, hM⟩ := exists_nat_ge a
            exact Set.mem_iUnion.mpr ⟨M, ha.mono (fun n hn => hn.trans hM)⟩
          · rintro ⟨S, ⟨M, rfl⟩, hS⟩
            exact ⟨(M : ℝ), hS⟩
        rw [h_set_eq]
        refine MeasurableSet.iUnion (fun M => ?_)
        -- `{y | ∀ᶠ n, blockLogAvgZ ... ≤ M}` = `⋃ N : ℕ, ⋂ n ≥ N, {y | ...}`.
        have h_eventually : {y : ∀ _ : ℕ, α | ∀ᶠ n in Filter.atTop,
              blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)}
            = ⋃ N : ℕ, ⋂ n ∈ Set.Ici N,
                {y | blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)} := by
          ext y
          simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_Ici,
            Filter.eventually_atTop]
        rw [h_eventually]
        refine MeasurableSet.iUnion (fun N => ?_)
        refine MeasurableSet.biInter (Set.to_countable _) (fun n _ => ?_)
        exact measurableSet_le (measurable_blockLogAvgZ_via_eN μ p.toStationaryProcess n)
          measurable_const
      )]
    exact h_Ω'
  -- Pull back via `μ.map forwardEmbed = μZ.map natProj` and `ae_map_iff` for natProj.
  rw [← (InformationTheory.Shannon.TwoSided.measurePreserving_natProj μ
    p.toStationaryProcess).map_eq] at h_N_ae
  rw [ae_map_iff InformationTheory.Shannon.TwoSided.measurable_natProj.aemeasurable
    (by
      -- Measurability of the predicate set on (ℕ → α), same proof as above.
      change MeasurableSet {y : ∀ _ : ℕ, α | _}
      have h_set_eq : {y : ∀ _ : ℕ, α | Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
            (fun n => blockLogAvgZ μ p.toStationaryProcess n (eN y))}
          = ⋃ M : ℕ, {y | ∀ᶠ n in Filter.atTop,
              blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)} := by
        ext y
        constructor
        · rintro ⟨a, ha⟩
          obtain ⟨M, hM⟩ := exists_nat_ge a
          exact Set.mem_iUnion.mpr ⟨M, ha.mono (fun n hn => hn.trans hM)⟩
        · rintro ⟨S, ⟨M, rfl⟩, hS⟩
          exact ⟨(M : ℝ), hS⟩
      rw [h_set_eq]
      refine MeasurableSet.iUnion (fun M => ?_)
      have h_eventually : {y : ∀ _ : ℕ, α | ∀ᶠ n in Filter.atTop,
            blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)}
          = ⋃ N : ℕ, ⋂ n ∈ Set.Ici N,
              {y | blockLogAvgZ μ p.toStationaryProcess n (eN y) ≤ (M : ℝ)} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_Ici,
          Filter.eventually_atTop]
      rw [h_eventually]
      refine MeasurableSet.iUnion (fun N => ?_)
      refine MeasurableSet.biInter (Set.to_countable _) (fun n _ => ?_)
      exact measurableSet_le (measurable_blockLogAvgZ_via_eN μ p.toStationaryProcess n)
        measurable_const
    )] at h_N_ae
  -- Now h_N_ae : ∀ᵐ x ∂μZ, IsBoundedUnder (≤) atTop (fun n => blockLogAvgZ n (eN (natProj x))).
  -- Convert to the target via h_blockLogAvgZ_factor.
  filter_upwards [h_N_ae] with x hx
  have h_eq : (fun n => blockLogAvgZ μ p.toStationaryProcess n x)
      = fun n => blockLogAvgZ μ p.toStationaryProcess n
          (eN (InformationTheory.Shannon.TwoSided.natProj x)) :=
    funext (fun n => h_blockLogAvgZ_factor x n)
  rw [h_eq]; exact hx

omit [DecidableEq α] in
/-- **Z-side liminf bound**: μZ-a.s., `liminf blockLogAvgZ n x ≥ entropyRate`. -/
@[entry_point]
theorem liminf_blockLogAvgZ_ge_entropyRate
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ x ∂(μZ μ p.toStationaryProcess),
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => blockLogAvgZ μ p.toStationaryProcess n x) Filter.atTop := by
  filter_upwards [blockLogAvgZ_ge_negLogQInftyZ_minus_error μ p.toStationaryProcess,
                  birkhoffAverage_pmfLogCondInfty_tendsto μ p,
                  blockLogAvgZ_bddAbove_ae μ p] with x h_bound h_birk h_bdd_above
  -- LHS tendsto: negLogQ/n - 2 log n / n → entropyRate - 0 = entropyRate.
  have h_log_div : Filter.Tendsto (fun n : ℕ => 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (𝓝 0) := by
    have h_log : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 0) := by
      have h_real : Filter.Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0))
          Filter.atTop (𝓝 0) := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
      have h_comp := h_real.comp tendsto_natCast_atTop_atTop
      refine h_comp.congr (fun n => ?_)
      simp
    have h_mul := h_log.const_mul (2 : ℝ)
    simp only [mul_zero] at h_mul
    refine h_mul.congr (fun n => ?_)
    rw [mul_div_assoc]
  have h_lhs : Filter.Tendsto
      (fun n : ℕ => negLogQInftyZ μ p.toStationaryProcess n x / (n : ℝ)
        - 2 * Real.log (n : ℝ) / (n : ℝ))
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess)) := by
    have := h_birk.sub h_log_div
    simpa using this
  -- Apply `liminf_le_liminf` between u (the LHS) and v = blockLogAvgZ.
  -- - hu: u is bounded below (tendsto ⇒ isBoundedUnder ≥).
  -- - hv: v is cobounded (· ≥ ·), from the a.s. upper bound `blockLogAvgZ_bddAbove_ae`.
  have h_liminf_le : Filter.liminf
      (fun n : ℕ => negLogQInftyZ μ p.toStationaryProcess n x / (n : ℝ)
        - 2 * Real.log (n : ℝ) / (n : ℝ)) Filter.atTop
      ≤ Filter.liminf (fun n => blockLogAvgZ μ p.toStationaryProcess n x) Filter.atTop :=
    Filter.liminf_le_liminf h_bound (hu := h_lhs.isBoundedUnder_ge)
      (hv := h_bdd_above.isCoboundedUnder_ge)
  rw [h_lhs.liminf_eq] at h_liminf_le
  exact h_liminf_le

omit [DecidableEq α] in
/-- **Final transfer to Ω-side**: μ-a.s., `entropyRate ≤ liminf blockLogAvg n ω`.

Bridge: `blockLogAvgZ n x` depends only on `natProj x : ℕ → α`. We transfer the
Z-side a.s. liminf bound through `natProj`-`forwardEmbed` measure preservation
to the Ω-side, using `μZ_nat_proj_eq` (= `μ.map forwardEmbed`) and the fact
that `blockLogAvgZ n (eN (forwardEmbed ω)) = blockLogAvg n ω` where
`eN y i := y i.toNat` is the trivial extension on ℤ. -/
@[entry_point]
theorem algoet_cover_liminf_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop := by
  classical
  -- Step 1: Z-side liminf bound.
  have h_Z := liminf_blockLogAvgZ_ge_entropyRate μ p
  -- Step 2: `blockLogAvgZ n x` depends only on `natProj x`. Define a "trivial
  -- extension" `eN : (ℕ → α) → (ℤ → α)`, `eN y i := y i.toNat`, with
  -- `natProj (eN y) = y` and `blockLogAvgZ n x = blockLogAvgZ n (eN (InformationTheory.Shannon.TwoSided.natProj x))`.
  set eN : (∀ _ : ℕ, α) → (∀ _ : ℤ, α) := fun y i => y i.toNat with heN_def
  have h_blockLogAvgZ_factor : ∀ x : ∀ _ : ℤ, α, ∀ n,
      blockLogAvgZ μ p.toStationaryProcess n x
        = blockLogAvgZ μ p.toStationaryProcess n (eN (InformationTheory.Shannon.TwoSided.natProj x)) := by
    intro x n
    -- Show: blockLogAvgZ n x = blockLogAvgZ n (eN (natProj x)).
    -- It suffices to show firstBlockZ n x = firstBlockZ n (eN (natProj x)).
    have h_arg : (firstBlockZ (α := α) n) x
        = (firstBlockZ (α := α) n) (eN (InformationTheory.Shannon.TwoSided.natProj x)) := by
      funext i
      show x (i.val : ℤ) = (eN (InformationTheory.Shannon.TwoSided.natProj x)) (i.val : ℤ)
      show x (i.val : ℤ) = x (((((i.val : ℕ) : ℤ).toNat : ℕ) : ℤ))
      simp
    unfold blockLogAvgZ
    rw [h_arg]
  -- Step 3: rewrite `h_Z` via `h_blockLogAvgZ_factor` so the predicate factors through
  -- natProj: P(x) = (entropyRate ≤ liminf (blockLogAvgZ n (eN (InformationTheory.Shannon.TwoSided.natProj x)))).
  have h_Z' : ∀ᵐ x ∂(μZ μ p.toStationaryProcess),
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => blockLogAvgZ μ p.toStationaryProcess n (eN (InformationTheory.Shannon.TwoSided.natProj x)))
            Filter.atTop := by
    filter_upwards [h_Z] with x hx
    have h_eq : (fun n => blockLogAvgZ μ p.toStationaryProcess n x)
        = fun n => blockLogAvgZ μ p.toStationaryProcess n (eN (InformationTheory.Shannon.TwoSided.natProj x)) :=
      funext (fun n => h_blockLogAvgZ_factor x n)
    rw [← h_eq]; exact hx
  -- Step 4: push h_Z' through `natProj` to get a (μZ.map natProj)-a.s. statement.
  -- Since `μZ.map natProj = μ.map forwardEmbed`, this becomes (μ.map forwardEmbed)-a.s.
  have h_mp_natProj : MeasurePreserving
      (InformationTheory.Shannon.TwoSided.natProj (α := α))
      (μZ μ p.toStationaryProcess) (μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)) :=
    InformationTheory.Shannon.TwoSided.measurePreserving_natProj μ p.toStationaryProcess
  -- The Z-side predicate `λ x, Q(natProj x)` is μZ-a.s. ⇒ Q is μZ.map natProj-a.s.
  -- We use `MeasurePreserving.ae_iff` (or its quasiMeasurePreserving form).
  have h_N_ae : ∀ᵐ y ∂(μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)),
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => blockLogAvgZ μ p.toStationaryProcess n (eN y)) Filter.atTop := by
    -- Use the fact that `(μZ.map natProj) = (μ.map forwardEmbed)` (from h_mp_natProj.map_eq).
    rw [← h_mp_natProj.map_eq]
    -- And `ae_map_iff` to convert μZ-a.s. of `Q ∘ natProj` to (μZ.map natProj)-a.s. of Q.
    rw [ae_map_iff InformationTheory.Shannon.TwoSided.measurable_natProj.aemeasurable
      (by
        -- Measurability of the predicate set on (ℕ → α).
        apply measurableSet_le measurable_const
        refine Measurable.liminf (fun n => ?_)
        -- `λ y, blockLogAvgZ n (eN y)` is measurable.
        exact measurable_blockLogAvgZ_via_eN μ p.toStationaryProcess n
      )]
    exact h_Z'
  -- Step 5: pull back from `(μ.map forwardEmbed)`-a.s. to μ-a.s. via forwardEmbed.
  have h_mp_forwardEmbed : MeasurePreserving (forwardEmbed (μ := μ) p.toStationaryProcess)
      μ (μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)) :=
    InformationTheory.Shannon.TwoSided.measurePreserving_forwardEmbed
      μ p.toStationaryProcess
  have h_Ω_ae : ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf
            (fun n => blockLogAvgZ μ p.toStationaryProcess n
              (eN (forwardEmbed (μ := μ) p.toStationaryProcess ω))) Filter.atTop :=
    h_mp_forwardEmbed.quasiMeasurePreserving.ae h_N_ae
  -- Step 6: `eN (forwardEmbed ω) = fun i : ℤ => p.obs i.toNat ω`, so
  -- `blockLogAvgZ n (eN (forwardEmbed ω)) = blockLogAvg n ω` by `blockLogAvgZ_natExt_eq`.
  filter_upwards [h_Ω_ae] with ω hω
  convert hω using 2
  funext n
  rw [show eN (forwardEmbed (μ := μ) p.toStationaryProcess ω)
      = fun i : ℤ => p.obs i.toNat ω from rfl]
  exact (blockLogAvgZ_natExt_eq μ p.toStationaryProcess n ω).symm

/-! ## D.7 — Main theorem (hypothesis-free assembly) -/

omit [DecidableEq α] in
/-- **Shannon–McMillan–Breiman theorem** (Cover–Thomas 16.8.1).

For a stationary ergodic process with finite alphabet `α`, the per-symbol
negative log-likelihood `blockLogAvg μ p n` converges almost surely to the
entropy rate `entropyRate μ p`.

This is the hypothesis-free capstone: the four hypotheses of
`shannon_mcmillan_breiman_of_sandwich` are discharged unconditionally by the
Algoet–Cover sandwich bounds (`algoet_cover_liminf_bound`,
`algoet_cover_limsup_bound`) and the a.s. boundedness lemmas
(`blockLogAvg_bddAbove_ae`, `blockLogAvg_bddBelow_ae`), all of which rest on
the Birkhoff ergodic theorem, the two-sided projective-limit construction
(`InformationTheory.Probability.TwoSidedExtension`), and backward-martingale
convergence. -/
@[entry_point]
theorem shannon_mcmillan_breiman
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess)) := by
  classical
  exact shannon_mcmillan_breiman_of_sandwich μ p
    (algoet_cover_liminf_bound μ p)
    (algoet_cover_limsup_bound μ p)
    (blockLogAvg_bddAbove_ae μ p)
    (blockLogAvg_bddBelow_ae μ p)

end InformationTheory.Shannon
