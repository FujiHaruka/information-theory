import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stationary.Basic
import InformationTheory.Shannon.EntropyRate
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Dynamics.Ergodic.Ergodic
import InformationTheory.Probability.TwoSidedExtension.Core
import InformationTheory.Probability.TwoSidedExtension.Backward

namespace InformationTheory.Shannon.TwoSided

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology symmDiff

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

section Backward

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)

/-! ### Integrability of `pmfLogCondPast` and `pmfLogCondInfty`

The integrand has the pointwise decomposition
`pmfLogCondPast μ p k x = ∑ a, 1_{coord0=a}(x) * (-log condProbPast a k x)`
(indicators partition unity on the singleton `{coord0=a}`, so the inner sum has
a single nonzero summand at `a = coord0 x`).

For each `a`, the summand `1_{coord0=a} * (-log condProbPast a k)` is integrable
via the L¹ tower (`condExp_stronglyMeasurable_mul_of_bound` with a truncated
`-log` factor) + monotone convergence. The truncated bound `F_M := min(M, (-log g)⁺)`
satisfies `∫ (1_{coord0=a}) * F_M = ∫ g * F_M ≤ ∫ negMulLog g ≤ 1`, uniformly in
`M`, so by MCT `∫ (1_{coord0=a}) * (-log g)⁺ ≤ 1`. -/

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Pointwise decomposition: `pmfLogCondPast μ p k = ∑_a 1_{coord0=a} * (-log condProbPast a k)`.
The inner sum collapses to a single nonzero term at `a = coord0 x`. -/
private lemma pmfLogCondPast_eq_sum_indicator_neg_log (k : ℕ) (x : (∀ _ : ℤ, α)) :
    pmfLogCondPast μ p k x
      = ∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbPast μ p a k x)) := by
  classical
  unfold pmfLogCondPast
  have h_inner :
      (∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * condProbPast μ p a k x) = condProbPast μ p (coord0 x) k x :=
    pmfLogCondPast_inner_eq_self (fun a => condProbPast μ p a k x) x
  have h_sum :
      (∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbPast μ p a k x)))
        = -Real.log (condProbPast μ p (coord0 x) k x) :=
    pmfLogCondPast_inner_eq_self (fun a => -Real.log (condProbPast μ p a k x)) x
  rw [h_inner, h_sum]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Analogous decomposition for `pmfLogCondInfty`. -/
private lemma pmfLogCondInfty_eq_sum_indicator_neg_log (x : (∀ _ : ℤ, α)) :
    pmfLogCondInfty μ p x
      = ∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbInfty μ p a x)) := by
  classical
  unfold pmfLogCondInfty
  have h_inner :
      (∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * condProbInfty μ p a x) = condProbInfty μ p (coord0 x) x :=
    pmfLogCondPast_inner_eq_self (fun a => condProbInfty μ p a x) x
  have h_sum :
      (∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbInfty μ p a x)))
        = -Real.log (condProbInfty μ p (coord0 x) x) :=
    pmfLogCondPast_inner_eq_self (fun a => -Real.log (condProbInfty μ p a x)) x
  rw [h_inner, h_sum]

lemma tendsto_min_posPart_natCast (t : ℝ) :
    Tendsto (fun M : ℕ => min (t⁺) (M : ℝ)) atTop (𝓝 (t⁺)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (t⁺)
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨N, fun M hM => ?_⟩
  have hMbig : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h_pos_part_le_M : t⁺ ≤ (M : ℝ) := hN.trans hMbig
  have hFM : min (t⁺) (M : ℝ) = t⁺ := min_eq_left h_pos_part_le_M
  rw [hFM]; simp [hε]

lemma norm_min_posPart_natCast_le (t : ℝ) (M : ℕ) :
    ‖min (t⁺) (M : ℝ)‖ ≤ (M : ℝ) := by
  have h_nn : 0 ≤ min (t⁺) (M : ℝ) := le_min (le_max_right _ _) M.cast_nonneg
  have h_bound : min (t⁺) (M : ℝ) ≤ (M : ℝ) := min_le_right _ _
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, h_bound⟩

lemma min_posPart_neg_log_mul_le_negMulLog {y : ℝ} (hy_nn : 0 ≤ y) (hy_le : y ≤ 1)
    (M : ℕ) : min ((-Real.log y)⁺) (M : ℝ) * y ≤ Real.negMulLog y := by
  have hlog_np : Real.log y ≤ 0 := Real.log_nonpos hy_nn hy_le
  have hneg_log_nn : 0 ≤ -Real.log y := neg_nonneg.mpr hlog_np
  have h_pos_part : (-Real.log y)⁺ = -Real.log y := max_eq_left hneg_log_nn
  have h_FM_le : min ((-Real.log y)⁺) (M : ℝ) ≤ -Real.log y :=
    le_trans (min_le_left _ _) (le_of_eq h_pos_part)
  calc min ((-Real.log y)⁺) (M : ℝ) * y ≤ (-Real.log y) * y :=
        mul_le_mul_of_nonneg_right h_FM_le hy_nn
    _ = Real.negMulLog y := by rw [Real.negMulLog]; ring

lemma enorm_mul_neg_log_eq_ofReal {c y : ℝ} (hc : 0 ≤ c) (hy_nn : 0 ≤ y)
    (hy_le : y ≤ 1) :
    (‖c * (-Real.log y)‖ₑ : ENNReal) = ENNReal.ofReal (c * (-Real.log y)⁺) := by
  have hlog_np : Real.log y ≤ 0 := Real.log_nonpos hy_nn hy_le
  have hneg_log_nn : 0 ≤ -Real.log y := neg_nonneg.mpr hlog_np
  have h_pos_part : (-Real.log y)⁺ = -Real.log y := max_eq_left hneg_log_nn
  have hprod_nn : 0 ≤ c * (-Real.log y) := mul_nonneg hc hneg_log_nn
  rw [h_pos_part]
  exact Real.enorm_eq_ofReal hprod_nn

lemma integrable_negMulLog_of_mem_Icc {β : Type*} {mβ : MeasurableSpace β}
    {ν : Measure β} [IsFiniteMeasure ν] {g : β → ℝ}
    (hg_meas : AEStronglyMeasurable g ν) (hg_nn : 0 ≤ᵐ[ν] g)
    (hg_le : g ≤ᵐ[ν] fun _ => (1 : ℝ)) :
    Integrable (fun x => Real.negMulLog (g x)) ν := by
  refine Integrable.mono (integrable_const (1 : ℝ))
    (Real.continuous_negMulLog.comp_aestronglyMeasurable hg_meas) ?_
  filter_upwards [hg_nn, hg_le] with x hx_nn hx_le
  have hx_nn' : (0 : ℝ) ≤ g x := hx_nn
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg hx_nn' hx_le),
    Real.norm_eq_abs, abs_of_nonneg zero_le_one]
  have h1 : Real.negMulLog (g x) ≤ 1 - g x := Real.negMulLog_le_one_sub_self hx_nn'
  linarith

lemma integral_negMulLog_le_one {β : Type*} {mβ : MeasurableSpace β}
    {ν : Measure β} [IsProbabilityMeasure ν] {g : β → ℝ}
    (hg_meas : AEStronglyMeasurable g ν) (hg_nn : 0 ≤ᵐ[ν] g)
    (hg_le : g ≤ᵐ[ν] fun _ => (1 : ℝ)) :
    ∫ x, Real.negMulLog (g x) ∂ν ≤ 1 := by
  have h_bd : (fun x => Real.negMulLog (g x)) ≤ᵐ[ν] fun _ => (1 : ℝ) := by
    filter_upwards [hg_nn, hg_le] with x hx_nn hx_le
    have hx_nn' : (0 : ℝ) ≤ g x := hx_nn
    have : Real.negMulLog (g x) ≤ 1 - g x := Real.negMulLog_le_one_sub_self hx_nn'
    linarith
  calc ∫ x, Real.negMulLog (g x) ∂ν
      ≤ ∫ _, (1 : ℝ) ∂ν :=
        integral_mono_ae (integrable_negMulLog_of_mem_Icc hg_meas hg_nn hg_le)
          (integrable_const _) h_bd
    _ = 1 := by rw [integral_const, smul_eq_mul]; simp

lemma lintegral_ofReal_le_one_of_integral_le_one {β : Type*} {mβ : MeasurableSpace β}
    {ν : Measure β} {φ : β → ℝ} (hφ_int : Integrable φ ν) (hφ_nn : 0 ≤ᵐ[ν] φ)
    (hφ_le : ∫ x, φ x ∂ν ≤ 1) : ∫⁻ x, ENNReal.ofReal (φ x) ∂ν ≤ 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal hφ_int hφ_nn]
  exact_mod_cast ENNReal.ofReal_le_one.mpr hφ_le

lemma lintegral_lt_top_of_monotone_tendsto_le {β : Type*} {mβ : MeasurableSpace β}
    {ν : Measure β} {f : ℕ → β → ENNReal} {ψ : β → ENNReal} {C : ENNReal}
    (hf_meas : ∀ M, Measurable (f M)) (hf_mono : ∀ x, Monotone fun M => f M x)
    (hf_tendsto : ∀ x, Tendsto (fun M => f M x) atTop (𝓝 (ψ x)))
    (hf_bound : ∀ M, ∫⁻ x, f M x ∂ν ≤ C) (hC : C < ⊤) :
    ∫⁻ x, ψ x ∂ν < ⊤ := by
  have h_supr_eq : ∫⁻ x, ψ x ∂ν = ⨆ M, ∫⁻ x, f M x ∂ν := by
    rw [show ψ = fun x => ⨆ M, f M x by
      funext x
      exact (iSup_eq_of_tendsto (hf_mono x) (hf_tendsto x)).symm]
    exact lintegral_iSup hf_meas (fun M N hMN x => hf_mono x hMN)
  rw [h_supr_eq]
  exact lt_of_le_of_lt (iSup_le hf_bound) hC

omit [DecidableEq α] [Nonempty α] in
/-- **Auxiliary integrability** (key technical lemma for both integrability theorems).

For any `m`-strongly-measurable `g : (∀ _ : ℤ, α) → ℝ` with `g ∈ [0, 1]` a.s. and
`g =ᵐ μZ[1_{coord0=a} | m]`, the function `1_{coord0=a} · (-log g)` is `μZ`-integrable.

Proof: truncate `(-log g)⁺` to `F_M := min M (-log g)⁺`. Each `F_M` is `m`-measurable and bounded
by `M`. By `condExp_stronglyMeasurable_mul_of_bound`, `μZ[ind · F_M | m] =ᵐ F_M · g` (using
`μZ[ind | m] = g`). Integrating: `∫ ind · F_M = ∫ F_M · g ≤ ∫ negMulLog g ≤ 1`.
Apply MCT (Lebesgue MCT on the `lintegral` form) as `M → ∞`. -/
private lemma integrable_indicator_mul_negLog_of_condExp
    (m : MeasurableSpace (∀ _ : ℤ, α)) (hm : m ≤ MeasurableSpace.pi)
    (a : α) (g : (∀ _ : ℤ, α) → ℝ)
    (hg_meas_m : StronglyMeasurable[m] g)
    (hg_eq_ce : g =ᵐ[μZ μ p]
      (μZ μ p)[(coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) | m])
    (hg_nn : 0 ≤ᵐ[μZ μ p] g)
    (hg_le : g ≤ᵐ[μZ μ p] (fun _ => (1 : ℝ))) :
    Integrable (fun x => (coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) x
      * (-Real.log (g x))) (μZ μ p) := by
  classical
  set ind : (∀ _ : ℤ, α) → ℝ :=
    (coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) with hind_def
  have h_g_m : Measurable[m] g := hg_meas_m.measurable
  have h_meas_g : @Measurable _ _ MeasurableSpace.pi _ g :=
    @Measurable.mono _ _ m MeasurableSpace.pi _ _ g h_g_m hm le_rfl
  have h_meas_log_g : @Measurable _ _ MeasurableSpace.pi _ (fun x => Real.log (g x)) :=
    Real.measurable_log.comp h_meas_g
  have h_meas_ind : @Measurable _ _ MeasurableSpace.pi _ ind := by
    refine Measurable.indicator measurable_const ?_
    exact measurableSet_coord0_eq a
  have h_int_ind : Integrable ind (μZ μ p) := integrable_indicator_coord0_eq μ p a
  have h_ind_nn : ∀ x, 0 ≤ ind x := indicator_coord0_eq_nonneg a
  have h_ind_le : ∀ x, ind x ≤ 1 := indicator_coord0_eq_le_one a
  -- Truncated factor `F_M(x) := min ((-log g x)⁺) M`. m-measurable and bounded by M.
  set F : ℕ → (∀ _ : ℤ, α) → ℝ := fun M x => min ((-Real.log (g x))⁺) M with hF_def
  have h_neg_log_m : Measurable[m] (fun x => -Real.log (g x)) :=
    (Real.measurable_log.comp h_g_m).neg
  have h_pos_part_m : Measurable[m] (fun x => (-Real.log (g x))⁺) :=
    h_neg_log_m.max measurable_const
  have hF_meas_m : ∀ M, StronglyMeasurable[m] (F M) := by
    intro M
    exact (h_pos_part_m.min measurable_const).stronglyMeasurable
  have hF_nn : ∀ M x, 0 ≤ F M x := fun M x =>
    le_min (le_max_right _ _) M.cast_nonneg
  have hF_bound : ∀ M x, F M x ≤ M := fun M x => min_le_right _ _
  have hF_mono : ∀ x, Monotone (fun M : ℕ => F M x) := by
    intro x M N hMN
    exact min_le_min le_rfl (by exact_mod_cast hMN)
  have hF_tendsto : ∀ x, Tendsto (fun M : ℕ => F M x) atTop (𝓝 ((-Real.log (g x))⁺)) := by
    intro x
    simp only [hF_def]
    exact tendsto_min_posPart_natCast (-Real.log (g x))
  -- F M is bounded by M (as a real norm), hence integrable; ind * F M integrable via
  -- `Integrable.bdd_mul` (with bounded factor F M).
  have hF_norm_bound : ∀ M x, ‖F M x‖ ≤ (M : ℝ) := by
    intro M x
    simp only [hF_def]
    exact norm_min_posPart_natCast_le (-Real.log (g x)) M
  have hF_meas : ∀ M, @Measurable _ _ MeasurableSpace.pi _ (F M) :=
    fun M => ((hF_meas_m M).mono hm).measurable
  -- Pull-out for each M: μZ[ind * F M | m] =ᵐ F M * g. We compute via
  -- `condExp_stronglyMeasurable_mul_of_bound` applied to (F M * ind) (F M is the bounded
  -- m-measurable factor); then commute *.
  have h_pullout_step1 : ∀ M,
      (μZ μ p)[fun x => F M x * ind x | m] =ᵐ[μZ μ p]
        fun x => F M x * (μZ μ p)[ind | m] x := by
    intro M
    refine condExp_stronglyMeasurable_mul_of_bound hm (hF_meas_m M) h_int_ind (M : ℝ) ?_
    filter_upwards with x using hF_norm_bound M x
  have h_pullout : ∀ M,
      (μZ μ p)[fun x => F M x * ind x | m] =ᵐ[μZ μ p] fun x => F M x * g x := by
    intro M
    refine (h_pullout_step1 M).trans ?_
    filter_upwards [hg_eq_ce] with x hxg
    rw [hxg]
  -- Integrability of ind * F M (and F M * ind).
  have h_int_FM_ind : ∀ M, Integrable (fun x => ind x * F M x) (μZ μ p) := by
    intro M
    refine Integrable.mul_bdd (c := (M : ℝ)) h_int_ind (hF_meas M).aestronglyMeasurable ?_
    filter_upwards with x using hF_norm_bound M x
  have h_int_FM_ind' : ∀ M, Integrable (fun x => F M x * ind x) (μZ μ p) := by
    intro M
    refine (h_int_FM_ind M).congr ?_
    filter_upwards with x using by ring
  -- Bound F M x * g x ≤ negMulLog (g x) a.s. (key inequality).
  have h_bound : ∀ M, ∀ᵐ x ∂(μZ μ p), F M x * g x ≤ Real.negMulLog (g x) := by
    intro M
    filter_upwards [hg_nn, hg_le] with x hx_nn hx_le
    simp only [hF_def]
    exact min_posPart_neg_log_mul_le_negMulLog hx_nn hx_le M
  -- Integrability of negMulLog g (bounded by 1 - g ≤ 1).
  have h_int_negMulLog : Integrable (fun x => Real.negMulLog (g x)) (μZ μ p) :=
    integrable_negMulLog_of_mem_Icc h_meas_g.aestronglyMeasurable hg_nn hg_le
  have h_int_FM_g : ∀ M, Integrable (fun x => F M x * g x) (μZ μ p) := by
    intro M
    refine Integrable.mono h_int_negMulLog
      (((hF_meas M).mul h_meas_g).aestronglyMeasurable) ?_
    filter_upwards [h_bound M, hg_nn, hg_le] with x hx_b hx_nn hx_le
    have hx_nn' : (0 : ℝ) ≤ g x := hx_nn
    have h_nn' : 0 ≤ F M x * g x := mul_nonneg (hF_nn M x) hx_nn'
    rw [Real.norm_eq_abs, abs_of_nonneg h_nn',
      Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg hx_nn' hx_le)]
    exact hx_b
  -- Integral identity per M: ∫ F M * ind = ∫ μZ[F M * ind | m] = ∫ F M * g.
  have h_int_eq : ∀ M,
      ∫ x, F M x * ind x ∂(μZ μ p) = ∫ x, F M x * g x ∂(μZ μ p) := by
    intro M
    have h1 : ∫ x, F M x * ind x ∂(μZ μ p)
        = ∫ x, ((μZ μ p)[fun x => F M x * ind x | m]) x ∂(μZ μ p) :=
      (integral_condExp hm).symm
    rw [h1]
    exact integral_congr_ae (h_pullout M)
  -- ∫ negMulLog g ≤ 1 (probability measure).
  have h_negMulLog_le_one :
      ∫ x, Real.negMulLog (g x) ∂(μZ μ p) ≤ 1 :=
    integral_negMulLog_le_one h_meas_g.aestronglyMeasurable hg_nn hg_le
  -- Uniform integral bound per M: ∫ ind * F M ≤ 1.
  have h_uniform_bound : ∀ M, ∫ x, ind x * F M x ∂(μZ μ p) ≤ 1 := by
    intro M
    have h_comm : ∫ x, ind x * F M x ∂(μZ μ p) = ∫ x, F M x * ind x ∂(μZ μ p) := by
      refine integral_congr_ae ?_; filter_upwards with x using by ring
    rw [h_comm, h_int_eq]
    refine le_trans ?_ h_negMulLog_le_one
    exact integral_mono_ae (h_int_FM_g M) h_int_negMulLog (h_bound M)
  -- Now build Integrable via lintegral bound + MCT.
  -- ‖ind(x) * (-log g(x))‖ₑ = ENNReal.ofReal (ind(x) * (-log g)⁺) a.s.
  have h_eq_pos_part : (fun x => (‖ind x * (-Real.log (g x))‖ₑ : ENNReal))
      =ᵐ[μZ μ p] fun x => ENNReal.ofReal (ind x * (-Real.log (g x))⁺) := by
    filter_upwards [hg_nn, hg_le] with x hx_nn hx_le
    exact enorm_mul_neg_log_eq_ofReal (h_ind_nn x) hx_nn hx_le
  -- The product ind * (-log g) is AEStronglyMeasurable.
  have h_meas_prod_pi : @Measurable _ _ MeasurableSpace.pi _
      (fun x => ind x * (-Real.log (g x))) :=
    h_meas_ind.mul h_meas_log_g.neg
  have h_meas_prod : AEStronglyMeasurable[MeasurableSpace.pi]
      (fun x => ind x * (-Real.log (g x))) (μZ μ p) :=
    h_meas_prod_pi.aestronglyMeasurable
  refine ⟨h_meas_prod, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_congr_ae h_eq_pos_part]
  -- ENNReal-of-real-integral bound per M.
  have h_lintegral_bound : ∀ M,
      ∫⁻ x, ENNReal.ofReal (ind x * F M x) ∂(μZ μ p) ≤ 1 := fun M =>
    lintegral_ofReal_le_one_of_integral_le_one (h_int_FM_ind M)
      (Filter.Eventually.of_forall fun x => mul_nonneg (h_ind_nn x) (hF_nn M x))
      (h_uniform_bound M)
  -- MCT (monotone increasing supremum).
  have h_mono : ∀ x, Monotone (fun M => ENNReal.ofReal (ind x * F M x)) := by
    intro x M N hMN
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_left (hF_mono x hMN) (h_ind_nn x)
  refine lintegral_lt_top_of_monotone_tendsto_le
    (C := 1)
    (fun M => ENNReal.continuous_ofReal.measurable.comp (h_meas_ind.mul (hF_meas M)))
    h_mono (fun x => ?_) h_lintegral_bound ENNReal.one_lt_top
  refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
  exact (hF_tendsto x).const_mul (ind x)

omit [DecidableEq α] [Nonempty α] in
/-- Integrability of `pmfLogCondPast k`.

The integrand `-log(condProbPast (coord0 x) k x)` decomposes as `∑_a 1_{coord0=a}(x)
* (-log condProbPast a k x)`. Each summand is integrable via
`integrable_indicator_mul_negLog_of_condExp` applied at `m := pastFiltration k`,
using the defining identity `condProbPast a k = μZ[1_{coord0=a} | pastFiltration k]`
and the `[0,1]` bound. The sum of finitely many integrable functions is integrable. -/
@[entry_point]
theorem integrable_pmfLogCondPast (k : ℕ) :
    Integrable (pmfLogCondPast μ p k) (μZ μ p) := by
  classical
  have h_eq : pmfLogCondPast μ p k = fun x =>
      ∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbPast μ p a k x)) := by
    funext x
    exact pmfLogCondPast_eq_sum_indicator_neg_log μ p k x
  rw [h_eq]
  refine integrable_finsetSum _ (fun a _ => ?_)
  refine integrable_indicator_mul_negLog_of_condExp μ p
    ((pastFiltration (α := α)) k)
    ((pastFiltration (α := α)).le _)
    a (condProbPast μ p a k)
    (stronglyMeasurable_condProbPast μ p a k)
    ?_ (ae_zero_le_condProbPast μ p a k) (ae_condProbPast_le_one μ p a k)
  exact Filter.EventuallyEq.refl _ _

omit [DecidableEq α] [Nonempty α] in
/-- Integrability of `pmfLogCondInfty`.

Same argument as `integrable_pmfLogCondPast`, but applied to the infinite-past
limit `condProbInfty a`, which is by definition the condExp of the indicator
w.r.t. the σ-algebra `⨆ k, pastFiltration k` of the infinite past. -/
@[entry_point]
theorem integrable_pmfLogCondInfty :
    Integrable (pmfLogCondInfty μ p) (μZ μ p) := by
  classical
  have h_eq : pmfLogCondInfty μ p = fun x =>
      ∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbInfty μ p a x)) := by
    funext x
    exact pmfLogCondInfty_eq_sum_indicator_neg_log μ p x
  rw [h_eq]
  refine integrable_finsetSum _ (fun a _ => ?_)
  -- `condProbInfty a := μZ[ind | ⨆ k, pastFiltration k]` by definition.
  refine integrable_indicator_mul_negLog_of_condExp μ p
    (⨆ n : ℕ, (pastFiltration (α := α)) n)
    (iSup_le (fun n => (pastFiltration (α := α)).le n))
    a (condProbInfty μ p a)
    (stronglyMeasurable_condProbInfty μ p a) ?_
    (ae_zero_le_condProbInfty μ p a) (ae_condProbInfty_le_one μ p a)
  exact condProbInfty_eq_condExp_tail μ p a

omit [DecidableEq α] [Nonempty α] in
/-- **AE positivity of the realized conditional probability**.

Almost surely under `μZ`, the infinite-past conditional probability of the
realized `coord0` value is strictly positive. This is a standard fact: the
indicator `1_{coord0 = coord0 x}` is exactly 1 at `x`, and the conditional
expectation w.r.t. `⨆ k, pastFiltration k` of an indicator-of-a-set has total
mass equal to that set's measure. Positivity on a full-measure set follows from
the integral identity `∫_E condProbInfty (coord0 x) = (μZ μ p)({coord0 = a} ∩ E)`.

Used inside `pmfLogCondPast_tendsto_pmfLogCondInfty` to handle `Real.log`
discontinuity at 0. -/
lemma ae_condProbInfty_coord0_pos :
    ∀ᵐ x ∂(μZ μ p), 0 < condProbInfty μ p (coord0 x) x := by
  classical
  -- Infinite-past σ-algebra.
  set m_inf : MeasurableSpace (∀ _ : ℤ, α) :=
    ⨆ n : ℕ, (pastFiltration (α := α)) n with hm_inf_def
  have hm_inf_le : m_inf ≤ MeasurableSpace.pi :=
    iSup_le (fun n => (pastFiltration (α := α)).le n)
  -- For each `a`, the "bad" set `E_a := {coord0 = a} ∩ {condProbInfty a ≤ 0}` has μZ-measure 0.
  have h_bad_zero : ∀ a : α,
      (μZ μ p) ((coord0 ⁻¹' {a}) ∩ {x | condProbInfty μ p a x ≤ 0}) = 0 := by
    intro a
    set E : Set (∀ _ : ℤ, α) := {x | condProbInfty μ p a x ≤ 0} with hE_def
    set indf : (∀ _ : ℤ, α) → ℝ :=
      (coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) with hindf_def
    have h_sm : StronglyMeasurable[m_inf] (condProbInfty μ p a) :=
      stronglyMeasurable_condProbInfty μ p a
    have hE_m : MeasurableSet[m_inf] E :=
      h_sm.measurableSet_le stronglyMeasurable_const
    have hE_pi : @MeasurableSet _ MeasurableSpace.pi E := hm_inf_le _ hE_m
    have h_coord_pi : @MeasurableSet _ MeasurableSpace.pi (coord0 ⁻¹' {a}) :=
      measurableSet_coord0_eq a
    have h_int_indf : Integrable indf (μZ μ p) := integrable_indicator_coord0_eq μ p a
    -- Step 1: ∫_E indf dμZ = ∫_E condProbInfty a dμZ.
    have h_setInt_E :
        ∫ x in E, indf x ∂(μZ μ p) = ∫ x in E, condProbInfty μ p a x ∂(μZ μ p) := by
      have h1 : ∫ x in E, indf x ∂(μZ μ p)
          = ∫ x in E, ((μZ μ p)[indf | m_inf]) x ∂(μZ μ p) :=
        (setIntegral_condExp hm_inf_le h_int_indf hE_m).symm
      have h2 : ∫ x in E, ((μZ μ p)[indf | m_inf]) x ∂(μZ μ p)
          = ∫ x in E, condProbInfty μ p a x ∂(μZ μ p) := by
        refine setIntegral_congr_ae (hm_inf_le _ hE_m) ?_
        filter_upwards [condProbInfty_eq_condExp_tail μ p a] with x hx _
        exact hx.symm
      exact h1.trans h2
    -- Step 2: LHS = μZ ({coord0=a} ∩ E) (as real). Use integral_indicator.
    have h_lhs : ∫ x in E, indf x ∂(μZ μ p)
        = (μZ μ p).real ((coord0 ⁻¹' {a}) ∩ E) := by
      rw [hindf_def, integral_indicator h_coord_pi, integral_const, smul_eq_mul, mul_one,
        Measure.restrict_restrict h_coord_pi, Measure.real, Measure.real]
      simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    -- Step 3: RHS ≤ 0 since condProbInfty a ≤ 0 on E.
    have h_rhs_le_zero : ∫ x in E, condProbInfty μ p a x ∂(μZ μ p) ≤ 0 := by
      refine MeasureTheory.setIntegral_nonpos hE_pi (fun x hx => hx)
    -- Step 4: RHS ≥ 0 since condProbInfty a ≥ 0 a.s.
    have h_rhs_nonneg : 0 ≤ ∫ x in E, condProbInfty μ p a x ∂(μZ μ p) := by
      refine MeasureTheory.integral_nonneg_of_ae ?_
      filter_upwards [ae_restrict_of_ae (ae_zero_le_condProbInfty μ p a)] with x hx
      exact hx
    -- Step 5: RHS = 0, hence LHS = 0, hence μZ ({coord0=a} ∩ E).real = 0.
    have h_rhs_zero : ∫ x in E, condProbInfty μ p a x ∂(μZ μ p) = 0 :=
      le_antisymm h_rhs_le_zero h_rhs_nonneg
    have h_lhs_zero : (μZ μ p).real ((coord0 ⁻¹' {a}) ∩ E) = 0 := by
      rw [← h_lhs, h_setInt_E, h_rhs_zero]
    -- Conclude `μZ (E_a) = 0` (ENNReal).
    have h_lt_top : (μZ μ p) ((coord0 ⁻¹' {a}) ∩ E) < ⊤ :=
      measure_lt_top _ _
    rw [Measure.real, ENNReal.toReal_eq_zero_iff] at h_lhs_zero
    exact h_lhs_zero.resolve_right h_lt_top.ne
  -- Now combine: μZ {x | condProbInfty (coord0 x) x ≤ 0} ≤ ∑_a μZ E_a = 0.
  rw [ae_iff]
  have h_set_eq : {x : (∀ _ : ℤ, α) | ¬ 0 < condProbInfty μ p (coord0 x) x}
      = ⋃ a : α, (coord0 ⁻¹' {a}) ∩ {x | condProbInfty μ p a x ≤ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, not_lt, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun hx => ⟨coord0 x, rfl, hx⟩, ?_⟩
    rintro ⟨a, ⟨ha, hle⟩⟩
    rw [show coord0 x = a from ha]
    exact hle
  rw [h_set_eq]
  refine measure_iUnion_null_iff.mpr fun a => ?_
  exact h_bad_zero a

omit [DecidableEq α] [Nonempty α] in
/-- **Forward Lévy upward convergence**: per-step conditional log-likelihood on
longer-and-longer finite past converges to `pmfLogCondInfty`. Application of
`MeasureTheory.tendsto_ae_condExp` (one application per `a : α`, combined
by continuity of `-log` and the inner-sum identity
`∑ a, indicator(coord0=a) * f a = f (coord0 x)`).

**Caveat**: convergence holds on the AE set where
`condProbInfty (coord0 x) x > 0` (provided by `ae_condProbInfty_coord0_pos`);
on the null set where the conditional probability of the realized coord0
value is `0`, `Real.log` is discontinuous, and we report
`pmfLogCondPast/pmfLogCondInfty` as `0` by convention (`Real.log 0 = 0`). -/
@[entry_point]
theorem pmfLogCondPast_tendsto_pmfLogCondInfty :
    ∀ᵐ x ∂(μZ μ p),
      Tendsto (fun k => pmfLogCondPast μ p k x) atTop
        (𝓝 (pmfLogCondInfty μ p x)) := by
  classical
  -- Combine the `α`-many a.s. convergences `condProbPast a k x → condProbInfty a x`.
  have h_all : ∀ᵐ x ∂(μZ μ p), ∀ a : α,
      Tendsto (fun k : ℕ => condProbPast μ p a k x) atTop
        (𝓝 (condProbInfty μ p a x)) := by
    rw [ae_all_iff]
    exact fun a => condProbPast_tendsto_condProbInfty μ p a
  -- AE positivity of the realized conditional probability `condProbInfty (coord0 x) x`.
  have h_pos := ae_condProbInfty_coord0_pos μ p
  filter_upwards [h_all, h_pos] with x hx hxpos
  -- The realized atom.
  set a₀ : α := coord0 x with ha₀
  -- pmfLogCondPast and pmfLogCondInfty simplify pointwise via `pmfLogCondPast_inner_eq_self`.
  have h_simp_past : ∀ k, pmfLogCondPast μ p k x = -Real.log (condProbPast μ p a₀ k x) := by
    intro k
    unfold pmfLogCondPast
    rw [pmfLogCondPast_inner_eq_self (fun a => condProbPast μ p a k x) x]
  have h_simp_infty :
      pmfLogCondInfty μ p x = -Real.log (condProbInfty μ p a₀ x) := by
    unfold pmfLogCondInfty
    rw [pmfLogCondPast_inner_eq_self (fun a => condProbInfty μ p a x) x]
  rw [h_simp_infty]
  simp_rw [h_simp_past]
  -- Goal: `(fun k => -log (condProbPast a₀ k x)) → -log (condProbInfty a₀ x)`.
  have hlimit : Tendsto (fun k : ℕ => condProbPast μ p a₀ k x) atTop
      (𝓝 (condProbInfty μ p a₀ x)) := hx a₀
  -- `Real.log` is continuous at any positive point.
  have hcont : ContinuousAt Real.log (condProbInfty μ p a₀ x) :=
    Real.continuousAt_log (ne_of_gt hxpos)
  exact (hcont.tendsto.comp hlimit).neg

omit [DecidableEq α] [Nonempty α] in
/-- **Pull-out identity for `pmfLogCondPast`**: integrating
`1_{coord_0=a} * (-log condProbPast a k)` equals integrating
`negMulLog(condProbPast a k)`.

Proof: `(-log condProbPast a k)` is `pastSigma k`-measurable; the indicator
`1_{coord_0=a}` is integrable. By the tower property
(`integral_condExp`) and the pull-out property
(`condExp_mul_of_aestronglyMeasurable_left`), pulling the `m`-measurable
factor out of the conditional expectation gives the result. -/
private lemma integral_indicator_mul_negLog_condProbPast (k : ℕ) (a : α) :
    ∫ x, (coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbPast μ p a k x)) ∂(μZ μ p)
      = ∫ x, Real.negMulLog (condProbPast μ p a k x) ∂(μZ μ p) := by
  classical
  set ind : (∀ _ : ℤ, α) → ℝ :=
    (coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) with hind_def
  set g : (∀ _ : ℤ, α) → ℝ := condProbPast μ p a k with hg_def
  set m : MeasurableSpace (∀ _ : ℤ, α) := (pastFiltration (α := α)) k with hm_def
  have hm_le : m ≤ MeasurableSpace.pi := (pastFiltration (α := α)).le k
  have h_int_ind : Integrable ind (μZ μ p) := integrable_indicator_coord0_eq μ p a
  have h_int_prod : Integrable (fun x => ind x * (-Real.log (g x))) (μZ μ p) := by
    refine integrable_indicator_mul_negLog_of_condExp μ p m hm_le a g ?_ ?_ ?_ ?_
    · exact stronglyMeasurable_condProbPast μ p a k
    · exact Filter.EventuallyEq.refl _ _
    · exact ae_zero_le_condProbPast μ p a k
    · exact ae_condProbPast_le_one μ p a k
  -- `(-log g)` is `m`-measurable.
  have h_g_meas_m : Measurable[m] g := (stronglyMeasurable_condProbPast μ p a k).measurable
  have h_neglog_g_meas_m : Measurable[m] (fun x => -Real.log (g x)) :=
    (Real.measurable_log.comp h_g_meas_m).neg
  have h_neglog_g_asm : AEStronglyMeasurable[m] (fun x => -Real.log (g x)) (μZ μ p) :=
    h_neglog_g_meas_m.stronglyMeasurable.aestronglyMeasurable
  -- Pull-out: μZ[(-log g) * ind | m] =ᵐ (-log g) * μZ[ind | m] = (-log g) * g.
  have h_pullout :
      (μZ μ p)[fun x => (-Real.log (g x)) * ind x | m]
        =ᵐ[μZ μ p] fun x => (-Real.log (g x)) * g x := by
    have h_prod' : Integrable (fun x => (-Real.log (g x)) * ind x) (μZ μ p) := by
      refine h_int_prod.congr ?_
      filter_upwards with x using by ring
    have h_pull :
        (μZ μ p)[fun x => (-Real.log (g x)) * ind x | m]
          =ᵐ[μZ μ p] fun x => (-Real.log (g x)) * (μZ μ p)[ind | m] x :=
      condExp_mul_of_aestronglyMeasurable_left h_neglog_g_asm h_prod' h_int_ind
    refine h_pull.trans ?_
    -- (μZ μ p)[ind | m] = g (by definition of g = condProbPast a k = μZ[ind | m]).
    filter_upwards with x
    rfl
  -- Apply `integral_condExp` to relate `∫ (-log g) * ind` and `∫ μZ[(-log g) * ind | m]`.
  have h1 : ∫ x, ind x * (-Real.log (g x)) ∂(μZ μ p)
      = ∫ x, (-Real.log (g x)) * ind x ∂(μZ μ p) := by
    refine integral_congr_ae ?_
    filter_upwards with x using by ring
  have h2 : ∫ x, (-Real.log (g x)) * ind x ∂(μZ μ p)
      = ∫ x, ((μZ μ p)[fun x => (-Real.log (g x)) * ind x | m]) x ∂(μZ μ p) :=
    (integral_condExp hm_le).symm
  have h3 : ∫ x, ((μZ μ p)[fun x => (-Real.log (g x)) * ind x | m]) x ∂(μZ μ p)
      = ∫ x, (-Real.log (g x)) * g x ∂(μZ μ p) :=
    integral_congr_ae h_pullout
  have h4 : ∫ x, (-Real.log (g x)) * g x ∂(μZ μ p)
      = ∫ x, Real.negMulLog (g x) ∂(μZ μ p) := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [Real.negMulLog]; ring
  rw [h1, h2, h3, h4]

omit [DecidableEq α] [Nonempty α] in
/-- The integral of `pmfLogCondPast k` decomposes as a finite sum of `negMulLog`
integrals of the per-atom conditional probabilities. -/
private lemma integral_pmfLogCondPast_eq_sum (k : ℕ) :
    ∫ x, pmfLogCondPast μ p k x ∂(μZ μ p)
      = ∑ a, ∫ x, Real.negMulLog (condProbPast μ p a k x) ∂(μZ μ p) := by
  classical
  -- Expand pmfLogCondPast pointwise as a finite sum.
  have h_eq : pmfLogCondPast μ p k = fun x =>
      ∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbPast μ p a k x)) := by
    funext x
    exact pmfLogCondPast_eq_sum_indicator_neg_log μ p k x
  rw [h_eq]
  -- Each summand is integrable.
  have h_int_a : ∀ a : α, Integrable
      (fun x => Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbPast μ p a k x))) (μZ μ p) := by
    intro a
    refine integrable_indicator_mul_negLog_of_condExp μ p
      ((pastFiltration (α := α)) k) ((pastFiltration (α := α)).le _) a
      (condProbPast μ p a k) (stronglyMeasurable_condProbPast μ p a k)
      ?_ (ae_zero_le_condProbPast μ p a k) (ae_condProbPast_le_one μ p a k)
    exact Filter.EventuallyEq.refl _ _
  rw [integral_finsetSum _ (fun a _ => h_int_a a)]
  refine Finset.sum_congr rfl ?_
  intro a _
  exact integral_indicator_mul_negLog_condProbPast μ p k a

/-! ### Bridge to `conditionalEntropyTail`

The remaining piece of the integral identity is matching the `μZ`-side condExp
formulation of `condProbPast` with the `μ`-side `condDistrib` formulation of
`conditionalEntropyTail`. We bridge through:
* `pastBlock k : (∀ _ : ℤ, α) → (Fin k → α)`, the projection
  `x ↦ (x(-k), x(-k+1), …, x(-1))`; viewing the finite past as a finite-dimensional
  RV;
* `condDistrib_ae_eq_condExp` to identify `condProbPast a k` with
  `(condDistrib coord0 (pastBlock k) (μZ) (pastBlock k x)).real {a}`;
* a stationarity-driven joint-law equality between the `μZ`-pushforward of
  `(coord0, pastBlock k)` and the `μ`-pushforward of `(obs k, blockRV k)`,
  which transports `condEntropy` between the two sides via
  `condEntropy_eq_pushforward`. -/

/-- The "past block" projection: `pastBlock k x i := x (i.val - k)`.
Maps `x : ℤ → α` to its restriction at indices `{-k, -k+1, …, -1}`, viewed
as a function `Fin k → α`. -/
def pastBlock (k : ℕ) : (∀ _ : ℤ, α) → (Fin k → α) :=
  fun x i => x ((i.val : ℤ) - k)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The past block projection is measurable. -/
lemma measurable_pastBlock (k : ℕ) :
    Measurable (pastBlock k : (∀ _ : ℤ, α) → (Fin k → α)) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  exact measurable_pi_apply _

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The comap of `MeasurableSpace.pi` along `pastBlock k` equals `pastSigma k`.
This is the algebraic identification of the "past block" σ-algebra with the
generator-form `pastSigma k`. -/
lemma comap_pastBlock_eq_pastSigma (k : ℕ) :
    (MeasurableSpace.pi : MeasurableSpace (Fin k → α)).comap (pastBlock k)
      = pastSigma (α := α) k := by
  -- `MeasurableSpace.pi (Fin k → α) = ⨆ i : Fin k, m_α.comap (·i)`.
  -- comap pulls back: `(⨆ M).comap f = ⨆ M.comap f`.
  -- So LHS = `⨆ i : Fin k, m_α.comap (fun x => x ((i.val : ℤ) - k))`.
  -- RHS = `cylinderEvents {j : ℤ | -k ≤ j ∧ j ≤ -1} = ⨆ j ∈ {-k,…,-1}, m_α.comap (·j)`.
  -- A `Fin k`-indexed iSup over `i.val - k` and a `ℤ`-indexed (restricted) iSup over
  -- `j ∈ {-k,…,-1}` are the same family.
  -- Use `measurable_iff_comap_le`/`measurable_pi_iff` style: a σ-algebra ≤ another
  -- iff the identity map is measurable. Equivalent direct comap rewriting:
  apply le_antisymm
  · -- LHS ≤ RHS: rewrite `MeasurableSpace.pi` as iSup of coordinate comaps,
    -- pull comap through iSup, identify each `Fin k → α` coord with a ℤ index.
    change MeasurableSpace.comap (pastBlock k) MeasurableSpace.pi ≤ _
    rw [show (MeasurableSpace.pi : MeasurableSpace (Fin k → α))
        = ⨆ i : Fin k, MeasurableSpace.comap (fun x : Fin k → α => x i) inferInstance from rfl,
      MeasurableSpace.comap_iSup]
    refine iSup_le (fun i => ?_)
    rw [MeasurableSpace.comap_comp]
    -- Goal: `m_α.comap (fun x => x ((i.val : ℤ) - k)) ≤ pastSigma k`.
    have hi_mem : ((i.val : ℤ) - k) ∈ ({j : ℤ | -(k : ℤ) ≤ j ∧ j ≤ -1} : Set ℤ) := by
      refine ⟨?_, ?_⟩
      · have h1 : (0 : ℤ) ≤ (i.val : ℤ) := Int.natCast_nonneg _
        linarith
      · have h2 : (i.val : ℤ) ≤ k - 1 := by
          have hh : i.val < k := i.2
          have : (i.val : ℤ) < (k : ℤ) := by exact_mod_cast hh
          linarith
        linarith
    -- `pastSigma k` reduces to the cylinderEvents iSup.
    change MeasurableSpace.comap (fun x : (∀ _ : ℤ, α) => x ((i.val : ℤ) - k))
        inferInstance ≤ cylinderEvents (X := fun _ : ℤ => α) _
    show _ ≤ ⨆ j ∈ ({j : ℤ | -(k : ℤ) ≤ j ∧ j ≤ -1} : Set ℤ),
            MeasurableSpace.comap (fun x : (∀ _ : ℤ, α) => x j) inferInstance
    exact le_iSup₂ (f := fun j _ =>
      MeasurableSpace.comap (fun x : (∀ _ : ℤ, α) => x j) inferInstance)
      ((i.val : ℤ) - k) hi_mem
  · -- RHS ≤ LHS.
    change cylinderEvents (X := fun _ : ℤ => α) _
          ≤ MeasurableSpace.comap (pastBlock k) MeasurableSpace.pi
    show ⨆ j ∈ ({j : ℤ | -(k : ℤ) ≤ j ∧ j ≤ -1} : Set ℤ),
            MeasurableSpace.comap (fun x : (∀ _ : ℤ, α) => x j) inferInstance
          ≤ MeasurableSpace.comap (pastBlock k) MeasurableSpace.pi
    refine iSup₂_le (fun j hj => ?_)
    obtain ⟨h_lo, h_hi⟩ := hj
    -- j ∈ [-k, -1], so j + k ∈ [0, k-1], cast to Fin k.
    have hj_plus_k_nn : (0 : ℤ) ≤ j + k := by linarith
    set i : ℕ := (j + k).toNat with hi_def
    have hi_eq_int : (i : ℤ) = j + k := Int.toNat_of_nonneg hj_plus_k_nn
    have hi_lt : i < k := by
      have : (i : ℤ) < (k : ℤ) := by rw [hi_eq_int]; linarith
      exact_mod_cast this
    let i' : Fin k := ⟨i, hi_lt⟩
    have hj_eq : j = (i'.val : ℤ) - k := by
      show j = ((i : ℤ)) - k
      rw [hi_eq_int]; ring
    rw [hj_eq]
    -- Goal: `m_α.comap (fun x => x ((i'.val : ℤ) - k)) ≤ (m_pi).comap (pastBlock k)`.
    rw [show (MeasurableSpace.pi : MeasurableSpace (Fin k → α))
        = ⨆ ii : Fin k, MeasurableSpace.comap (fun x : Fin k → α => x ii) inferInstance from rfl,
      MeasurableSpace.comap_iSup]
    refine le_trans ?_ (le_iSup _ i')
    rw [MeasurableSpace.comap_comp]
    -- (m_α.comap (fun x : Fin k → α => x i')).comap (pastBlock k)
    --   = m_α.comap (fun x => pastBlock k x i')
    --   = m_α.comap (fun x => x ((i'.val : ℤ) - k))
    -- which matches LHS.
    rfl

/-! ### Joint-law identification via stationarity -/

omit [DecidableEq α] [Nonempty α] in
lemma mapZ_coord0_pastBlock_apply_singleton (k : ℕ) (a : α) (s : Fin k → α) :
    (μZ μ p).map (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x)) {(a, s)}
      = (μ.map (p.blockRV (k + 1))) {Fin.snoc s a} := by
  classical
  have hpair_meas_Z : Measurable (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x)) :=
    (measurable_coord0).prodMk (measurable_pastBlock k)
  set s_full : Fin (k + 1) → α := Fin.snoc s a with hs_full_def
  -- Step LHS-1: rewrite the LHS as μZ of a set, then split into shifted-marginal.
  rw [Measure.map_apply hpair_meas_Z (measurableSet_singleton _)]
  -- Preimage rewrite: { x | (x 0 = a) ∧ pastBlock k x = s }
  --   = { x | ∀ i : Fin (k+1), x ((i.val:ℤ) - k) = s_full i }
  have hpre : (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x)) ⁻¹' {(a, s)}
      = { x : (∀ _ : ℤ, α) | ∀ i : Fin (k + 1), x ((i.val : ℤ) - k) = s_full i } := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hcoord, hpast⟩
      intro i
      -- Cases on i: either i = Fin.last k or i = j.castSucc for j : Fin k.
      refine Fin.lastCases ?_ ?_ i
      · -- i = Fin.last k: x ((k:ℤ) - k) = x 0 = a = s_full (Fin.last k).
        have h_int_last : ((Fin.last k).val : ℤ) - k = 0 := by
          show ((k : ℤ)) - k = 0; ring
        rw [h_int_last, hs_full_def, Fin.snoc_last]
        exact hcoord
      · intro j
        -- i = j.castSucc: x (j.val - k) = (pastBlock k x) j = s j = s_full j.castSucc.
        have hj_cast_val : (j.castSucc : Fin (k+1)).val = j.val := rfl
        rw [hs_full_def, Fin.snoc_castSucc]
        show x ((j.val : ℤ) - k) = s j
        have : pastBlock k x j = s j := congr_fun hpast _
        exact this
    · intro hall
      refine ⟨?_, ?_⟩
      · -- coord0 x = a: extract `i = Fin.last k`.
        have h_int_last : ((Fin.last k).val : ℤ) - k = 0 := by
          show ((k : ℤ)) - k = 0; ring
        have hlast := hall (Fin.last k)
        rw [h_int_last, hs_full_def, Fin.snoc_last] at hlast
        exact hlast
      · funext j
        have h := hall j.castSucc
        rw [hs_full_def, Fin.snoc_castSucc] at h
        show x ((j.val : ℤ) - k) = s j
        have hcast_val : (j.castSucc : Fin (k+1)).val = j.val := rfl
        rw [hcast_val] at h
        exact h
  rw [hpre]
  -- A cylinder on the index set `J := { (i.val:ℤ) - k | i : Fin (k+1) }`.
  set J : Finset ℤ :=
    (Finset.univ.image (fun i : Fin (k + 1) => (i.val : ℤ) - k))
    with hJ_def
  have hi_mem : ∀ i : Fin (k + 1), ((i.val : ℤ) - k) ∈ J := by
    intro i
    rw [hJ_def, Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩
  set S_J : Set (∀ _ : J, α) :=
    { f | ∀ i : Fin (k + 1), f ⟨((i.val : ℤ) - k), hi_mem i⟩ = s_full i } with hS_J
  have hS_J_meas : MeasurableSet S_J := by
    have h_inter : S_J = ⋂ i : Fin (k + 1),
        { f : ∀ _ : J, α | f ⟨((i.val : ℤ) - k), hi_mem i⟩ = s_full i } := by
      ext f; simp [hS_J]
    rw [h_inter]
    refine MeasurableSet.iInter (fun i => ?_)
    have hpre' : { f : ∀ _ : J, α | f ⟨((i.val : ℤ) - k), hi_mem i⟩ = s_full i }
        = (fun f : ∀ _ : J, α => f ⟨((i.val : ℤ) - k), hi_mem i⟩) ⁻¹' {s_full i} := rfl
    rw [hpre']
    exact (measurable_pi_apply _) (measurableSet_singleton _)
  have h_set_eq :
      { x : (∀ _ : ℤ, α) | ∀ i : Fin (k + 1), x ((i.val : ℤ) - k) = s_full i }
        = cylinder J S_J := by
    ext x
    simp only [Set.mem_setOf_eq, cylinder, Set.mem_preimage, Finset.restrict, hS_J]
  rw [h_set_eq, μZ_cylinder μ p hS_J_meas]
  have hJ_shift : ∀ j ∈ J, (0 : ℤ) ≤ j + k := by
    intro j hj
    rw [hJ_def, Finset.mem_image] at hj
    obtain ⟨i, _, rfl⟩ := hj
    have h1 : (0 : ℤ) ≤ (i.val : ℤ) := Int.natCast_nonneg _
    linarith
  rw [shiftedMarginal_eq_of_shift μ p J k hJ_shift,
      Measure.map_apply (measurable_obsZ μ p k J) hS_J_meas]
  rw [Measure.map_apply (p.measurable_blockRV (k+1)) (measurableSet_singleton _)]
  apply congrArg
  ext ω
  simp only [Set.mem_preimage, hS_J, Set.mem_setOf_eq, obsZ, Set.mem_singleton_iff]
  constructor
  · intro hf
    funext i
    have := hf i
    have hcast : ((((i.val : ℤ) - k) + ((k : ℕ) : ℤ)).toNat) = i.val := by
      have : ((i.val : ℤ) - k) + ((k : ℕ) : ℤ) = (i.val : ℤ) := by ring
      rw [this]
      exact_mod_cast Int.toNat_natCast _
    show p.blockRV (k+1) ω i = s_full i
    rw [hcast] at this
    exact this
  · intro hf i
    have hcast : ((((i.val : ℤ) - k) + ((k : ℕ) : ℤ)).toNat) = i.val := by
      have : ((i.val : ℤ) - k) + ((k : ℕ) : ℤ) = (i.val : ℤ) := by ring
      rw [this]
      exact_mod_cast Int.toNat_natCast _
    rw [hcast]
    exact congr_fun hf i

omit [Fintype α] [DecidableEq α] [Nonempty α] [IsProbabilityMeasure μ] in
lemma map_obs_blockRV_apply_singleton (k : ℕ) (a : α) (s : Fin k → α) :
    μ.map (fun ω : Ω => (p.obs k ω, p.blockRV k ω)) {(a, s)}
      = (μ.map (p.blockRV (k + 1))) {Fin.snoc s a} := by
  classical
  have hpair_meas_Ω : Measurable (fun ω : Ω => (p.obs k ω, p.blockRV k ω)) :=
    (p.measurable_obs k).prodMk (p.measurable_blockRV k)
  set s_full : Fin (k + 1) → α := Fin.snoc s a with hs_full_def
  rw [Measure.map_apply hpair_meas_Ω (measurableSet_singleton _),
      Measure.map_apply (p.measurable_blockRV (k+1)) (measurableSet_singleton _)]
  apply congrArg
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hobs, hblock⟩
    funext i
    refine Fin.lastCases ?_ ?_ i
    · -- i = Fin.last k.
      rw [hs_full_def, Fin.snoc_last]
      show p.obs (Fin.last k) ω = a
      show p.obs k ω = a
      exact hobs
    · intro j
      -- i = j.castSucc.
      rw [hs_full_def, Fin.snoc_castSucc]
      show p.obs j.castSucc.val ω = s j
      have h1 : (j.castSucc : Fin (k+1)).val = j.val := rfl
      rw [h1]
      show p.obs j.val ω = s j
      have h2 : p.blockRV k ω j = p.obs j.val ω := rfl
      rw [← h2, hblock]
  · intro hblock_full
    refine ⟨?_, ?_⟩
    · -- p.obs k ω = a (extract Fin.last k).
      have hlast := congr_fun hblock_full (Fin.last k)
      rw [hs_full_def, Fin.snoc_last] at hlast
      show p.obs k ω = a
      show p.obs (Fin.last k) ω = a
      exact hlast
    · funext j
      have hj := congr_fun hblock_full j.castSucc
      rw [hs_full_def, Fin.snoc_castSucc] at hj
      show p.obs j.val ω = s j
      have h1 : (j.castSucc : Fin (k+1)).val = j.val := rfl
      have h2 : p.blockRV (k + 1) ω j.castSucc = p.obs j.castSucc.val ω := rfl
      rw [h2] at hj
      rw [h1] at hj
      exact hj

omit [DecidableEq α] [Nonempty α] in
/-- **Joint-law equality** (the key bridge for the integral identity).

The pushforward of `μZ` under the joint map `x ↦ (coord0 x, pastBlock k x)`
equals the pushforward of `μ` under `ω ↦ (p.obs k ω, p.blockRV k ω)`.

Proof: both sides are probability measures on `α × (Fin k → α)`. We show they
agree on rectangles `{a} ×ˢ {s}`, which is enough since the spaces are finite.
The LHS rectangle reduces, via stationarity (shift by `k`), to the marginal at
the index set `{0, 1, …, k}`, which equals the ℕ-side block.
The RHS rectangle is exactly the singleton mass of `μ.map (p.blockRV (k+1))`
at the corresponding `Fin (k+1) → α`. -/
@[entry_point]
theorem joint_pastBlock_coord0_eq (k : ℕ) :
    (μZ μ p).map (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x))
      = μ.map (fun ω : Ω => (p.obs k ω, p.blockRV k ω)) := by
  classical
  -- Both are probability measures on `α × (Fin k → α)` (finite × finite).
  have hpair_meas_Z : Measurable (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x)) :=
    (measurable_coord0).prodMk (measurable_pastBlock k)
  have hpair_meas_Ω : Measurable (fun ω : Ω => (p.obs k ω, p.blockRV k ω)) :=
    (p.measurable_obs k).prodMk (p.measurable_blockRV k)
  -- Both are probability measures (in particular, finite).
  haveI : IsProbabilityMeasure
      ((μZ μ p).map (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x))) :=
    Measure.isProbabilityMeasure_map hpair_meas_Z.aemeasurable
  haveI : IsProbabilityMeasure
      (μ.map (fun ω : Ω => (p.obs k ω, p.blockRV k ω))) :=
    Measure.isProbabilityMeasure_map hpair_meas_Ω.aemeasurable
  -- It suffices to show equality on singletons (finite types).
  refine Measure.ext_of_singleton ?_
  rintro ⟨a, s⟩
  -- Both LHS and RHS singletons reduce to `μ.map (blockRV (k+1)) {Fin.snoc s a}`.
  rw [mapZ_coord0_pastBlock_apply_singleton μ p k a s,
    map_obs_blockRV_apply_singleton μ p k a s]

omit [DecidableEq α] in
/-- **Conditional expectation identification**: `condProbPast a k` agrees a.s.
with the `condDistrib`-form regular conditional probability built from
`(coord0, pastBlock k)`. -/
lemma condProbPast_ae_eq_condDistrib (a : α) (k : ℕ) :
    condProbPast μ p a k =ᵐ[μZ μ p]
      fun x => (ProbabilityTheory.condDistrib coord0 (pastBlock k) (μZ μ p)
        (pastBlock k x)).real {a} := by
  -- Apply `condDistrib_ae_eq_condExp` with Y := coord0, X := pastBlock k, s := {a}.
  -- This gives:
  --   `(condDistrib coord0 pastBlock μZ (pastBlock k x)).real {a}
  --      =ᵐ[μZ] μZ⟦coord0 ⁻¹' {a} | (m_α^Fin k).comap (pastBlock k)⟧`
  -- and we identify the σ-algebra via `comap_pastBlock_eq_pastSigma`.
  -- `condProbPast a k x` is defined as `μZ[indicator(coord0=a) | pastFiltration k]
  --   = μZ[indicator | pastSigma k]`, so we need to relate to `μZ⟦coord0⁻¹{a} | pastSigma k⟧`.
  -- Recall: `μZ⟦S | m⟧ = μZ[indicator(S) | m]` by definition. So both formulas agree.
  have h_ae := ProbabilityTheory.condDistrib_ae_eq_condExp (μ := μZ μ p)
    (X := pastBlock k) (Y := coord0)
    (measurable_pastBlock k) measurable_coord0 (measurableSet_singleton a)
  -- h_ae : (fun x => (condDistrib coord0 (pastBlock k) μZ (pastBlock k x)).real {a})
  --   =ᵐ[μZ] μZ⟦coord0 ⁻¹' {a} | (m_α).comap (pastBlock k)⟧
  --   = μZ⟦coord0 ⁻¹' {a} | pastSigma k⟧  (after rewriting the comap)
  -- Note: `μ⟦s | m⟧ := μ[s.indicator (fun _ => (1 : ℝ)) | m]`.
  -- So `μZ⟦coord0 ⁻¹' {a} | pastSigma k⟧ = μZ[indicator | pastSigma k] = condProbPast a k`.
  symm
  have h_sigma_eq : (inferInstance : MeasurableSpace (Fin k → α)).comap (pastBlock k)
      = (pastFiltration (α := α)) k := comap_pastBlock_eq_pastSigma k
  -- Rewrite the conditional expectation σ-algebra.
  refine h_ae.trans ?_
  -- Goal: μZ⟦coord0 ⁻¹' {a} | _.comap (pastBlock k)⟧ =ᵐ condProbPast a k.
  unfold condProbPast
  show (μZ μ p)⟦coord0 ⁻¹' {a} | (inferInstance : MeasurableSpace (Fin k → α)).comap (pastBlock k)⟧
      =ᵐ[μZ μ p] (μZ μ p)[(coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ))
          | (pastFiltration (α := α)) k]
  rw [h_sigma_eq]

/-! ### Integral identity proof -/

omit [DecidableEq α] in
/-- The integral `∫_μZ negMulLog(condProbPast a k x) dμZ` equals the integral
`∫_μZ negMulLog((condDistrib coord0 pastBlock μZ (pastBlock k x)).real {a}) dμZ`. -/
private lemma integral_negMulLog_condProbPast_eq (a : α) (k : ℕ) :
    ∫ x, Real.negMulLog (condProbPast μ p a k x) ∂(μZ μ p)
      = ∫ x, Real.negMulLog
          ((ProbabilityTheory.condDistrib coord0 (pastBlock k) (μZ μ p)
            (pastBlock k x)).real {a}) ∂(μZ μ p) := by
  classical
  refine integral_congr_ae ?_
  filter_upwards [condProbPast_ae_eq_condDistrib μ p a k] with x hx
  rw [hx]

omit [DecidableEq α] in
/-- The sum of per-atom integrals collapses via `integral_map` into a single
integral over the pushforward `μZ.map (pastBlock k)` of `condEntropy` integrand.
This is the key bridge between `pmfLogCondPast` and `MeasureFano.condEntropy`. -/
private lemma sum_integral_negMulLog_condDistrib_eq_condEntropy (k : ℕ) :
    (∑ a, ∫ x, Real.negMulLog
        ((ProbabilityTheory.condDistrib coord0 (pastBlock k) (μZ μ p)
          (pastBlock k x)).real {a}) ∂(μZ μ p))
      = InformationTheory.MeasureFano.condEntropy
          (μZ μ p) coord0 (pastBlock k) := by
  classical
  -- Each summand: push through integral_map (since coord0 (pastBlock k x) is well-defined).
  -- The bound function `y ↦ negMulLog ((condDistrib coord0 pastBlock μZ y).real {a})`
  -- is measurable (composition of measurable_of_finite on the kernel y ↦ measure
  -- and continuous Real.negMulLog).
  -- After integral_map, sum the result over a; the sum-of-integrals = integral-of-sum.
  have hpast_meas : Measurable (pastBlock k : (∀ _ : ℤ, α) → (Fin k → α)) :=
    measurable_pastBlock k
  -- Define f_a : (Fin k → α) → ℝ.
  set f : α → (Fin k → α) → ℝ := fun a y =>
    Real.negMulLog ((ProbabilityTheory.condDistrib coord0 (pastBlock k) (μZ μ p) y).real {a})
    with hf_def
  have hf_meas : ∀ a, Measurable (f a) := fun a => measurable_of_finite _
  -- Step 1: each summand = ∫ y, f a y ∂(μZ.map pastBlock).
  have h_per_a : ∀ a, ∫ x, Real.negMulLog
      ((ProbabilityTheory.condDistrib coord0 (pastBlock k) (μZ μ p)
        (pastBlock k x)).real {a}) ∂(μZ μ p)
        = ∫ y, f a y ∂((μZ μ p).map (pastBlock k)) := by
    intro a
    rw [integral_map hpast_meas.aemeasurable (hf_meas a).aestronglyMeasurable]
  simp_rw [h_per_a]
  -- Step 2: sum-of-integrals = integral-of-sum (for finite sums and integrable terms;
  -- finite alphabet + bounded integrand makes this trivial via integral_finsetSum).
  rw [← integral_finsetSum (s := (Finset.univ : Finset α)) (f := f)
        (fun a _ => Integrable.of_finite)]
  -- Now the goal is exactly the definition of MeasureFano.condEntropy.
  unfold InformationTheory.MeasureFano.condEntropy
  rfl

omit [DecidableEq α] in
/-- The `μZ`-side `condEntropy` of `(coord0, pastBlock k)` equals the `μ`-side
`condEntropy` of `(obs k, blockRV k)` via the joint-law equality. -/
private lemma condEntropy_μZ_eq_condEntropy_μ (k : ℕ) :
    InformationTheory.MeasureFano.condEntropy (μZ μ p) coord0 (pastBlock k)
      = InformationTheory.MeasureFano.condEntropy μ (p.obs k) (p.blockRV k) := by
  classical
  -- Apply condEntropy_eq_pushforward symmetrically; the joint pushforwards agree
  -- by joint_pastBlock_coord0_eq.
  rw [InformationTheory.Shannon.condEntropy_eq_pushforward (μZ μ p) coord0 (pastBlock k)
        measurable_coord0 (measurable_pastBlock k),
      InformationTheory.Shannon.condEntropy_eq_pushforward μ (p.obs k) (p.blockRV k)
        (p.measurable_obs k) (p.measurable_blockRV k)]
  congr 1
  exact joint_pastBlock_coord0_eq μ p k

omit [DecidableEq α] in
/-- **Per-step integral identity**: integrating `pmfLogCondPast k` against `μZ`
gives `conditionalEntropyTail μ p k`.

The proof structure:
1. Decompose `∫ pmfLogCondPast k dμZ` into a finite sum of
   `∫ negMulLog(condProbPast a k) dμZ` (via `integral_pmfLogCondPast_eq_sum`).
2. Identify each `condProbPast a k` with the `condDistrib`-form regular
   conditional probability (via `condProbPast_ae_eq_condDistrib`).
3. Bridge the sum to `condEntropy μZ coord0 (pastBlock k)` via `integral_map`
   and the definition of `MeasureFano.condEntropy`.
4. Transport to the `μ`-side via `condEntropy_μZ_eq_condEntropy_μ` (joint-law
   equality + `condEntropy_eq_pushforward`). -/
@[entry_point]
theorem integral_pmfLogCondPast_eq_conditionalEntropyTail (k : ℕ) :
    ∫ x, pmfLogCondPast μ p k x ∂(μZ μ p) = conditionalEntropyTail μ p k := by
  classical
  -- Step 1: decompose.
  rw [integral_pmfLogCondPast_eq_sum μ p k]
  -- Step 2: each summand: switch from condProbPast to condDistrib-form.
  rw [show (∑ a, ∫ x, Real.negMulLog (condProbPast μ p a k x) ∂(μZ μ p))
        = ∑ a, ∫ x, Real.negMulLog
            ((ProbabilityTheory.condDistrib coord0 (pastBlock k) (μZ μ p)
              (pastBlock k x)).real {a}) ∂(μZ μ p) from
      Finset.sum_congr rfl (fun a _ => integral_negMulLog_condProbPast_eq μ p a k)]
  -- Step 3: collapse sum + integrals into condEntropy μZ.
  rw [sum_integral_negMulLog_condDistrib_eq_condEntropy μ p k]
  -- Step 4: transport via joint-law equality.
  rw [condEntropy_μZ_eq_condEntropy_μ μ p k]
  rfl

omit [DecidableEq α] [Nonempty α] in
/-- **Pull-out identity for `pmfLogCondInfty`** (analogue of
`integral_indicator_mul_negLog_condProbPast` for the infinite-past condExp):
integrating `1_{coord_0=a} * (-log condProbInfty a)` equals integrating
`negMulLog(condProbInfty a)`. -/
private lemma integral_indicator_mul_negLog_condProbInfty (a : α) :
    ∫ x, (coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbInfty μ p a x)) ∂(μZ μ p)
      = ∫ x, Real.negMulLog (condProbInfty μ p a x) ∂(μZ μ p) := by
  classical
  set ind : (∀ _ : ℤ, α) → ℝ :=
    (coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) with hind_def
  set g : (∀ _ : ℤ, α) → ℝ := condProbInfty μ p a with hg_def
  set m : MeasurableSpace (∀ _ : ℤ, α) := ⨆ n : ℕ, (pastFiltration (α := α)) n with hm_def
  have hm_le : m ≤ MeasurableSpace.pi :=
    iSup_le (fun n => (pastFiltration (α := α)).le n)
  have h_int_ind : Integrable ind (μZ μ p) := integrable_indicator_coord0_eq μ p a
  have h_int_prod : Integrable (fun x => ind x * (-Real.log (g x))) (μZ μ p) := by
    refine integrable_indicator_mul_negLog_of_condExp μ p m hm_le a g ?_ ?_ ?_ ?_
    · exact stronglyMeasurable_condProbInfty μ p a
    · exact condProbInfty_eq_condExp_tail μ p a
    · exact ae_zero_le_condProbInfty μ p a
    · exact ae_condProbInfty_le_one μ p a
  -- `(-log g)` is `m`-measurable.
  have h_g_meas_m : Measurable[m] g := (stronglyMeasurable_condProbInfty μ p a).measurable
  have h_neglog_g_meas_m : Measurable[m] (fun x => -Real.log (g x)) :=
    (Real.measurable_log.comp h_g_meas_m).neg
  have h_neglog_g_asm : AEStronglyMeasurable[m] (fun x => -Real.log (g x)) (μZ μ p) :=
    h_neglog_g_meas_m.stronglyMeasurable.aestronglyMeasurable
  -- Pull-out: μZ[(-log g) * ind | m] =ᵐ (-log g) * μZ[ind | m] =ᵐ (-log g) * g.
  have h_pullout :
      (μZ μ p)[fun x => (-Real.log (g x)) * ind x | m]
        =ᵐ[μZ μ p] fun x => (-Real.log (g x)) * g x := by
    have h_prod' : Integrable (fun x => (-Real.log (g x)) * ind x) (μZ μ p) := by
      refine h_int_prod.congr ?_
      filter_upwards with x using by ring
    have h_pull :
        (μZ μ p)[fun x => (-Real.log (g x)) * ind x | m]
          =ᵐ[μZ μ p] fun x => (-Real.log (g x)) * (μZ μ p)[ind | m] x :=
      condExp_mul_of_aestronglyMeasurable_left h_neglog_g_asm h_prod' h_int_ind
    refine h_pull.trans ?_
    filter_upwards [condProbInfty_eq_condExp_tail μ p a] with x hx
    -- hx : condProbInfty μ p a x = (μZ μ p)[ind | m] x
    -- Goal: (-log g x) * μZ[ind | m] x = (-log g x) * g x
    rw [hg_def, hx]
  have h1 : ∫ x, ind x * (-Real.log (g x)) ∂(μZ μ p)
      = ∫ x, (-Real.log (g x)) * ind x ∂(μZ μ p) := by
    refine integral_congr_ae ?_
    filter_upwards with x using by ring
  have h2 : ∫ x, (-Real.log (g x)) * ind x ∂(μZ μ p)
      = ∫ x, ((μZ μ p)[fun x => (-Real.log (g x)) * ind x | m]) x ∂(μZ μ p) :=
    (integral_condExp hm_le).symm
  have h3 : ∫ x, ((μZ μ p)[fun x => (-Real.log (g x)) * ind x | m]) x ∂(μZ μ p)
      = ∫ x, (-Real.log (g x)) * g x ∂(μZ μ p) :=
    integral_congr_ae h_pullout
  have h4 : ∫ x, (-Real.log (g x)) * g x ∂(μZ μ p)
      = ∫ x, Real.negMulLog (g x) ∂(μZ μ p) := by
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [Real.negMulLog]; ring
  rw [h1, h2, h3, h4]

omit [DecidableEq α] [Nonempty α] in
/-- The integral of `pmfLogCondInfty` decomposes as a finite sum of `negMulLog`
integrals of the per-atom infinite-past conditional probabilities. -/
private lemma integral_pmfLogCondInfty_eq_sum :
    ∫ x, pmfLogCondInfty μ p x ∂(μZ μ p)
      = ∑ a, ∫ x, Real.negMulLog (condProbInfty μ p a x) ∂(μZ μ p) := by
  classical
  have h_eq : pmfLogCondInfty μ p = fun x =>
      ∑ a, Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbInfty μ p a x)) := by
    funext x
    exact pmfLogCondInfty_eq_sum_indicator_neg_log μ p x
  rw [h_eq]
  have h_int_a : ∀ a : α, Integrable
      (fun x => Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) x
        * (-Real.log (condProbInfty μ p a x))) (μZ μ p) := by
    intro a
    refine integrable_indicator_mul_negLog_of_condExp μ p
      (⨆ n : ℕ, (pastFiltration (α := α)) n)
      (iSup_le (fun n => (pastFiltration (α := α)).le n)) a
      (condProbInfty μ p a) (stronglyMeasurable_condProbInfty μ p a) ?_
      (ae_zero_le_condProbInfty μ p a) (ae_condProbInfty_le_one μ p a)
    exact condProbInfty_eq_condExp_tail μ p a
  rw [integral_finsetSum _ (fun a _ => h_int_a a)]
  refine Finset.sum_congr rfl ?_
  intro a _
  exact integral_indicator_mul_negLog_condProbInfty μ p a

omit [DecidableEq α] [Nonempty α] in
/-- **DCT step for each summand**: by forward Lévy a.s. convergence of
`condProbPast a k → condProbInfty a` and the uniform bound `negMulLog ∈ [0, 1]`
on `[0, 1]`, the integral `∫ negMulLog(condProbPast a k)` converges to
`∫ negMulLog(condProbInfty a)`. -/
private lemma tendsto_integral_negMulLog_condProbPast (a : α) :
    Tendsto (fun k : ℕ => ∫ x, Real.negMulLog (condProbPast μ p a k x) ∂(μZ μ p))
      atTop (𝓝 (∫ x, Real.negMulLog (condProbInfty μ p a x) ∂(μZ μ p))) := by
  classical
  -- Use DCT with constant bound `Real.exp (-1)` (= max of negMulLog on [0,1] at 1/e).
  -- AE: condProbPast a k x → condProbInfty a x.
  have h_ae : ∀ᵐ x ∂(μZ μ p),
      Tendsto (fun k : ℕ => Real.negMulLog (condProbPast μ p a k x)) atTop
        (𝓝 (Real.negMulLog (condProbInfty μ p a x))) := by
    filter_upwards [condProbPast_tendsto_condProbInfty μ p a] with x hx
    exact (Real.continuous_negMulLog.tendsto _).comp hx
  -- Each negMulLog(condProbPast a k x) is in [0, 1] ae (since negMulLog x ≤ 1 - x ≤ 1 on [0,1]).
  have h_bound : ∀ k : ℕ, ∀ᵐ x ∂(μZ μ p),
      ‖Real.negMulLog (condProbPast μ p a k x)‖ ≤ 1 := by
    intro k
    filter_upwards [ae_zero_le_condProbPast μ p a k, ae_condProbPast_le_one μ p a k]
      with x hx_nn hx_le
    have hx_nn' : (0 : ℝ) ≤ condProbPast μ p a k x := hx_nn
    have hx_le' : condProbPast μ p a k x ≤ 1 := hx_le
    have h_nn : 0 ≤ Real.negMulLog (condProbPast μ p a k x) :=
      Real.negMulLog_nonneg hx_nn' hx_le'
    have h_le_sub : Real.negMulLog (condProbPast μ p a k x) ≤ 1 - condProbPast μ p a k x :=
      Real.negMulLog_le_one_sub_self hx_nn'
    have h_le_one : Real.negMulLog (condProbPast μ p a k x) ≤ 1 := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg h_nn]
    exact h_le_one
  -- Bound function is constant (integrable on finite measure).
  have h_bound_int : Integrable (fun _ : (∀ _ : ℤ, α) => (1 : ℝ)) (μZ μ p) :=
    integrable_const _
  -- Each F_k is AEStronglyMeasurable: negMulLog ∘ condProbPast a k.
  have h_meas : ∀ k : ℕ, AEStronglyMeasurable
      (fun x : (∀ _ : ℤ, α) => Real.negMulLog (condProbPast μ p a k x)) (μZ μ p) := by
    intro k
    refine Real.continuous_negMulLog.measurable.comp_aemeasurable ?_
      |>.aestronglyMeasurable
    refine ((stronglyMeasurable_condProbPast μ p a k).mono
      ((pastFiltration (α := α)).le k)).measurable.aemeasurable
  exact tendsto_integral_of_dominated_convergence (F := fun k => fun x =>
    Real.negMulLog (condProbPast μ p a k x))
    (f := fun x => Real.negMulLog (condProbInfty μ p a x))
    (bound := fun _ => (1 : ℝ))
    h_meas h_bound_int h_bound h_ae

omit [DecidableEq α] in
/-- **The SMB integral identity** `∫ pmfLogCondInfty dμZ = entropyRate μ p`.

Combines:
* `integral_pmfLogCondPast_eq_conditionalEntropyTail` — the per-step identity;
* DCT (forward Lévy a.s. limit + `Real.exp (-1)` uniform bound on `negMulLog`)
  applied per atom — `∫ negMulLog(condProbPast a k) → ∫ negMulLog(condProbInfty a)`;
* `entropyRate_eq_lim_condEntropy` — `conditionalEntropyTail μ p k → entropyRate`. -/
@[entry_point]
theorem integral_pmfLogCondInfty_eq_entropyRate :
    ∫ x, pmfLogCondInfty μ p x ∂(μZ μ p) = entropyRate μ p := by
  classical
  -- The sequence `n ↦ ∫ pmfLogCondPast n dμZ` converges to both
  -- `∫ pmfLogCondInfty dμZ` (by DCT applied to each summand) and `entropyRate μ p`
  -- (by the per-step identity + `entropyRate_eq_lim_condEntropy`). Apply
  -- `tendsto_nhds_unique`.
  -- Step 1: `∫ pmfLogCondPast k → ∫ pmfLogCondInfty`.
  have h_lim1 : Tendsto (fun k : ℕ => ∫ x, pmfLogCondPast μ p k x ∂(μZ μ p))
      atTop (𝓝 (∫ x, pmfLogCondInfty μ p x ∂(μZ μ p))) := by
    -- Rewrite both sides as finite sums.
    have h_LHS : ∀ k : ℕ, ∫ x, pmfLogCondPast μ p k x ∂(μZ μ p)
        = ∑ a, ∫ x, Real.negMulLog (condProbPast μ p a k x) ∂(μZ μ p) :=
      integral_pmfLogCondPast_eq_sum μ p
    have h_RHS : ∫ x, pmfLogCondInfty μ p x ∂(μZ μ p)
        = ∑ a, ∫ x, Real.negMulLog (condProbInfty μ p a x) ∂(μZ μ p) :=
      integral_pmfLogCondInfty_eq_sum μ p
    rw [h_RHS]
    refine Tendsto.congr (fun k => (h_LHS k).symm) ?_
    -- Finite sum of convergent sequences converges to the sum.
    exact tendsto_finsetSum _ (fun a _ => tendsto_integral_negMulLog_condProbPast μ p a)
  -- Step 2: `∫ pmfLogCondPast k = conditionalEntropyTail k → entropyRate μ p`.
  have h_step : ∀ k : ℕ,
      ∫ x, pmfLogCondPast μ p k x ∂(μZ μ p) = conditionalEntropyTail μ p k :=
    fun k => integral_pmfLogCondPast_eq_conditionalEntropyTail μ p k
  have h_lim2 : Tendsto (fun k : ℕ => ∫ x, pmfLogCondPast μ p k x ∂(μZ μ p))
      atTop (𝓝 (entropyRate μ p)) := by
    refine Tendsto.congr (fun k => (h_step k).symm) ?_
    exact entropyRate_eq_lim_condEntropy μ p
  -- Step 3: uniqueness of limit.
  exact tendsto_nhds_unique h_lim1 h_lim2

end Backward

end InformationTheory.Shannon.TwoSided
