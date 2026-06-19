import InformationTheory.Shannon.EntropyPower.Ext
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.InformationTheory.KullbackLeibler.Basic
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Core
import InformationTheory.Shannon.EPI.Unconditional.TruncationLimit.Mono

/-!
# TruncationLimit — limit part

a.e. convergence of truncated densities, divergence `h(W_n) → ⊤`, the `⊤`-branch assembly, and the
unconditional gateway monotonicity together with its `entropyPower` lift.

## Main statements

* `differentialEntropyExt_truncW_tendsto_top` — `h(W) = ⊤ ⟹ h(W_n) → ⊤` along the truncations.
* `differentialEntropyExt_top_of_indep_add_unconditional` — the unconditional `⊤`-branch
  `h(W) = ⊤ ⟹ h(W+V) = ⊤`.
* `differentialEntropyExt_mono_add_unconditional` — unconditional gateway monotonicity
  `W` a.c. and `W ⊥ V ⟹ h(W) ≤ h(W+V)`.
* `entropyPowerExt_mono_add_unconditional` — its `entropyPowerExt` lift.

Depends on the `Core` and `Mono` parts; re-exported by the umbrella
`InformationTheory.Shannon.EPI.Unconditional.TruncationLimit`.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The truncated W-marginal density converges a.e. (volume) to the full W-marginal density:
`(((truncW P W n).map W).rnDeriv volume x).toReal → ((P.map W).rnDeriv volume x).toReal` as
`n → ∞`. Uses `(truncW P W n).map W = cond (P.map W) Sn` with `Sn n = {r | |r| ≤ n}`, the conditioned
density formula `rnDeriv_cond_eq`, and the pointwise limit (no weak convergence).

@audit:ok -/
theorem truncW_map_density_tendsto_ae
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (_hW_ac : (P.map W) ≪ volume) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n => (((truncW P W n).map W).rnDeriv volume x).toReal) atTop
        (𝓝 (((P.map W).rnDeriv volume x).toReal)) := by
  classical
  haveI hWmap_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  -- truncation set in the W-marginal and its mass.
  set Sn : ℕ → Set ℝ := fun n => {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : ∀ n, MeasurableSet (Sn n) := fun n =>
    measurableSet_le measurable_norm measurable_const
  have hSn_mono : Monotone Sn := by
    intro n m hnm r hr
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    exact le_trans hr this
  have hSn_union : ⋃ n, Sn n = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro r
    obtain ⟨k, hk⟩ := exists_nat_ge |r|
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  set c : ℕ → ℝ≥0∞ := fun n => (P.map W) (Sn n) with hc_def
  -- `c n → 1` (union is everything).
  have hc_lim : Tendsto c atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := P.map W) hSn_mono
    rw [hSn_union, measure_univ] at h
    exact h
  -- `(truncW P W n).map W = cond (P.map W) (Sn n)` for every `n` (direct measure equality).
  have hmap_eq : ∀ n, ((truncW P W n).map W) = ProbabilityTheory.cond (P.map W) (Sn n) := by
    intro n
    set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
    have hE_meas : MeasurableSet E := hW.abs measurableSet_Iic
    have hE_eq : E = W ⁻¹' (Sn n) := by ext ω; simp [hE_def, hSn_def]
    refine Measure.ext (fun A hA => ?_)
    have hLHS : ((truncW P W n).map W) A = ((P.map W) (Sn n))⁻¹ * (P.map W) (Sn n ∩ A) := by
      rw [Measure.map_apply hW hA, truncW, ProbabilityTheory.cond_apply hE_meas P, hE_eq,
        Measure.map_apply hW (hSn_meas n), Measure.map_apply hW ((hSn_meas n).inter hA),
        Set.preimage_inter]
    have hRHS : (ProbabilityTheory.cond (P.map W) (Sn n)) A
        = ((P.map W) (Sn n))⁻¹ * (P.map W) (Sn n ∩ A) := by
      rw [ProbabilityTheory.cond_apply (hSn_meas n) (P.map W) A]
    rw [hLHS, hRHS]
  -- real-valued mass and its inverse converge to 1.
  set cr : ℕ → ℝ := fun n => (c n).toReal with hcr_def
  have hcr_lim : Tendsto cr atTop (𝓝 1) := by
    have := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hc_lim
    simpa [hcr_def, Function.comp] using this
  -- eventually `c n ≠ 0`.
  have hc_ne : ∀ᶠ n in atTop, c n ≠ 0 := by
    have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
    exact hc_lim.eventually_mem h_nhds
  -- the inverse mass (real) converges to 1.
  have hcbar_lim : Tendsto (fun n => ((c n)⁻¹).toReal) atTop (𝓝 1) := by
    have heq : (fun n => (cr n)⁻¹) =ᶠ[atTop] fun n => ((c n)⁻¹).toReal := by
      filter_upwards [hc_ne] with n hn
      rw [hcr_def]; simp only; rw [ENNReal.toReal_inv]
    refine Tendsto.congr' heq ?_
    have : Tendsto (fun n => (cr n)⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
      (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hcr_lim
    simpa using this
  -- on the tail (`c n ≠ 0`), the cond density formula:
  -- `fn_n =ᵐ (c n)⁻¹ · 1_{Sn n} · μW.rnDeriv vol`.
  have h_rn : ∀ n, c n ≠ 0 → ((truncW P W n).map W).rnDeriv volume
      =ᵐ[volume] fun x => (c n)⁻¹ * (Sn n).indicator ((P.map W).rnDeriv volume) x := by
    intro n hcn
    have hrn := rnDeriv_cond_eq (P.map W) (hSn_meas n) hcn
    rw [hmap_eq n]; exact hrn
  -- assemble: an a.e. set of `x` where (i) all tail density formulas hold and (ii) `μW.rnDeriv x < ⊤`.
  -- Then `fn_n x → fW x`.
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hc_ne
  -- the a.e. set: tail density formulas hold simultaneously (countable conjunction) + finite density.
  have h_all : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n, N₀ ≤ n →
      ((truncW P W n).map W).rnDeriv volume x
        = (c n)⁻¹ * (Sn n).indicator ((P.map W).rnDeriv volume) x := by
    rw [ae_all_iff]; intro n
    by_cases hn : N₀ ≤ n
    · filter_upwards [h_rn n (hN₀ n hn)] with x hx _; exact hx
    · filter_upwards with x h; exact absurd h hn
  filter_upwards [h_all, (P.map W).rnDeriv_lt_top volume] with x hx hx_fin
  -- abbreviations.
  set fWe : ℝ≥0∞ := (P.map W).rnDeriv volume x with hfWe_def
  have hfWe_ne : fWe ≠ ⊤ := hx_fin.ne
  -- `x ∈ Sn n` eventually (when `|x| ≤ n`).
  obtain ⟨Nx, hNx⟩ := exists_nat_ge |x|
  -- the tail formula simplifies (on `n ≥ max N₀ Nx`) to `(c n)⁻¹.toReal * fWe.toReal`.
  have hev : ∀ᶠ n in atTop, (((truncW P W n).map W).rnDeriv volume x).toReal
      = ((c n)⁻¹).toReal * fWe.toReal := by
    filter_upwards [Filter.eventually_ge_atTop N₀, Filter.eventually_ge_atTop Nx] with n hnN₀ hnNx
    have hxSn : x ∈ Sn n := le_trans hNx (by exact_mod_cast hnNx)
    rw [hx n hnN₀, Set.indicator_of_mem hxSn, ENNReal.toReal_mul, ← hfWe_def]
  -- the product `(c n)⁻¹.toReal * fWe.toReal → 1 * fWe.toReal = fWe.toReal`.
  refine Tendsto.congr' (Filter.EventuallyEq.symm hev) ?_
  have hprod : Tendsto (fun n => ((c n)⁻¹).toReal * fWe.toReal) atTop (𝓝 (1 * fWe.toReal)) :=
    hcbar_lim.mul tendsto_const_nhds
  simpa using hprod

/-- `h(μ) = ⊤ ⟹ A(μ) = ⊤`: the positive-part `lintegral` diverges when the a.c.-branch differential
entropy is `⊤`. Since `h μ = (A : EReal) - (B : EReal) = ⊤` is impossible for finite `A`, we get
`A = ⊤`; no hypothesis on `B(μ)` is needed.

@audit:ok -/
theorem posPart_lintegral_eq_top_of_diffEntExt_top {μ : Measure ℝ} (hac : μ ≪ volume)
    (htop : differentialEntropyExt μ = ⊤) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume) = ⊤ := by
  rw [differentialEntropyExt_of_ac hac] at htop
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB_def
  -- `htop : (A : EReal) - (B : EReal) = ⊤`.  Suppose `A ≠ ⊤`; derive a contradiction.
  by_contra hA
  -- `A` finite ⟹ `(A : EReal) = ((A.toReal : ℝ) : EReal)`, a real coe.
  have hAcoe : (A : EReal) = ((A.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hA).symm
  rcases eq_or_ne B (⊤ : ℝ≥0∞) with hBtop | hBfin
  · -- `B = ⊤`: `(A:EReal) - ⊤ = ⊥ ≠ ⊤`.
    rw [hBtop, EReal.coe_ennreal_top, EReal.sub_top] at htop
    exact absurd htop (by simp)
  · -- `B ≠ ⊤`: difference of two finite reals is finite (`≠ ⊤`).
    have hBcoe : (B : EReal) = ((B.toReal : ℝ) : EReal) := (EReal.coe_ennreal_toReal hBfin).symm
    rw [hAcoe, hBcoe, ← EReal.coe_sub] at htop
    exact (EReal.coe_ne_top _ htop)

/-- `h(μ) = ⊤ ⟹ B(μ) ≠ ⊤`: the negative-part `lintegral` is finite when the a.c.-branch differential
entropy is `⊤` (the symmetric counterpart of `posPart_lintegral_eq_top_of_diffEntExt_top`). If
`B = ⊤`, then `(A : EReal) - ⊤ = ⊥ ≠ ⊤`. This lets the assembly derive `B(P.map W) ≠ ⊤` from
`h(W) = ⊤` without adding a hypothesis to the signature.

@audit:ok -/
theorem negPart_lintegral_ne_top_of_diffEntExt_top {μ : Measure ℝ} (hac : μ ≪ volume)
    (htop : differentialEntropyExt μ = ⊤) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume) ≠ ⊤ := by
  rw [differentialEntropyExt_of_ac hac] at htop
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB_def
  -- `htop : (A : EReal) - (B : EReal) = ⊤`.  If `B = ⊤`, then `(A:EReal) - ⊤ = ⊥ ≠ ⊤`.
  intro hBtop
  rw [hBtop, EReal.coe_ennreal_top, EReal.sub_top] at htop
  exact absurd htop (by simp)

/-- Explicit upper bound on the negative-part `lintegral` of the truncated W-marginal: when `c_n ≠ 0`,
`B(W_n) ≤ ofReal |cbar_n · log cbar_n| + ofReal cbar_n · B(W)`, where `cbar_n := ((P.map W) (Sn n))⁻¹`
and `Sn n = {r | |r| ≤ n}`. Obtained from the `negMulLog`-product decomposition of the truncated
density `fn = cbar_n · 1_{Sn n} · fW` and the probability normalization `∫⁻ ofReal fW = 1`.

@audit:ok -/
theorem truncW_map_negPart_lintegral_le
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume) (n : ℕ)
    (hcn : (P.map W) {r : ℝ | |r| ≤ (n : ℝ)} ≠ 0) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)))
        ∂volume)
      ≤ ENNReal.ofReal (|(((P.map W) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal
          * Real.log ((((P.map W) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal)|)
        + ENNReal.ofReal ((((P.map W) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal)
          * (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
              ∂volume) := by
  classical
  haveI hWmap_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn := measurableSet_le measurable_norm measurable_const
  set fW : ℝ → ℝ := fun x => ((P.map W).rnDeriv volume x).toReal with hfW_def
  set c : ℝ≥0∞ := (P.map W) Sn with hc_def
  set cbar : ℝ := (c⁻¹).toReal with hcbar_def
  have hcbar_nn : 0 ≤ cbar := ENNReal.toReal_nonneg
  -- `(truncW P W n).map W = cond (P.map W) Sn` and its density.
  have hmap_eq : ((truncW P W n).map W) = ProbabilityTheory.cond (P.map W) Sn := by
    set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
    have hE_meas : MeasurableSet E := hW.abs measurableSet_Iic
    have hE_eq : E = W ⁻¹' Sn := by ext ω; simp [hE_def, hSn_def]
    refine Measure.ext (fun A hA => ?_)
    have hLHS : ((truncW P W n).map W) A = ((P.map W) Sn)⁻¹ * (P.map W) (Sn ∩ A) := by
      rw [Measure.map_apply hW hA, truncW, ProbabilityTheory.cond_apply hE_meas P, hE_eq,
        Measure.map_apply hW hSn_meas, Measure.map_apply hW (hSn_meas.inter hA),
        Set.preimage_inter]
    have hRHS : (ProbabilityTheory.cond (P.map W) Sn) A = ((P.map W) Sn)⁻¹ * (P.map W) (Sn ∩ A) := by
      rw [ProbabilityTheory.cond_apply hSn_meas (P.map W) A]
    rw [hLHS, hRHS]
  set fn : ℝ → ℝ := fun x => (((truncW P W n).map W).rnDeriv volume x).toReal with hfn_def
  have h_rn : ((truncW P W n).map W).rnDeriv volume
      =ᵐ[volume] fun x => c⁻¹ * Sn.indicator ((P.map W).rnDeriv volume) x := by
    rw [hmap_eq]; exact rnDeriv_cond_eq (P.map W) hSn_meas hcn
  have hfW_meas : Measurable (fun x => ENNReal.ofReal (fW x)) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.ennreal_ofReal
  have hfW_lint : (∫⁻ x, ENNReal.ofReal (fW x) ∂volume) = 1 := by
    have hae_eq : (fun x => ENNReal.ofReal (fW x)) =ᵐ[volume] (P.map W).rnDeriv volume := by
      filter_upwards [(P.map W).rnDeriv_ne_top volume] with x hx
      rw [hfW_def]; exact ENNReal.ofReal_toReal hx
    rw [lintegral_congr_ae hae_eq, Measure.lintegral_rnDeriv hW_ac, measure_univ]
  -- pointwise `=ᵐ`: `-(negMulLog fn) = 1_Sn · ((cbar log cbar)·fW + cbar·(-(negMulLog fW)))`.
  have h_int_eq : (fun x => ENNReal.ofReal (-(Real.negMulLog (fn x))))
      =ᵐ[volume] fun x => ENNReal.ofReal (Sn.indicator
        (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x) := by
    filter_upwards [h_rn] with x hx
    rw [hfn_def]; simp only; rw [hx]
    by_cases hxs : x ∈ Sn
    · rw [Set.indicator_of_mem hxs (f := (P.map W).rnDeriv volume),
        Set.indicator_of_mem hxs
          (f := fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))),
        ENNReal.toReal_mul]
      congr 1
      show -(Real.negMulLog (cbar * fW x))
        = cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))
      rw [Real.negMulLog_mul cbar (fW x)]
      ring_nf
      rw [Real.negMulLog]
      ring
    · rw [Set.indicator_of_notMem hxs (f := (P.map W).rnDeriv volume),
        Set.indicator_of_notMem hxs
          (f := fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x))))]
      simp [Real.negMulLog]
  rw [hfn_def] at *
  rw [show (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)))
      ∂volume)
    = ∫⁻ x, ENNReal.ofReal (Sn.indicator
        (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x) ∂volume from
    lintegral_congr_ae h_int_eq]
  -- Bound the indicator integrand by two finite-integral pieces (`≤`, then evaluate).
  have hbound : ∀ x, ENNReal.ofReal (Sn.indicator
        (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x)
      ≤ ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)
        + ENNReal.ofReal cbar * ENNReal.ofReal (-(Real.negMulLog (fW x))) := by
    intro x
    by_cases hxs : x ∈ Sn
    · rw [Set.indicator_of_mem hxs]
      refine le_trans ENNReal.ofReal_add_le ?_
      refine add_le_add ?_ ?_
      · rw [← ENNReal.ofReal_mul (abs_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) ?_)
        have hfW_nn : (0 : ℝ) ≤ fW x := ENNReal.toReal_nonneg
        rw [abs_mul, abs_of_nonneg hfW_nn]
      · rw [← ENNReal.ofReal_mul hcbar_nn]
    · rw [Set.indicator_of_notMem hxs]; simp
  have hnegm_meas : Measurable (fun x => ENNReal.ofReal (-(Real.negMulLog (fW x)))) :=
    ((Real.continuous_negMulLog.measurable.comp
      ((Measure.measurable_rnDeriv _ _).ennreal_toReal)).neg).ennreal_ofReal
  have hg1_meas : Measurable
      (fun x => ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)) :=
    measurable_const.mul hfW_meas
  calc (∫⁻ x, ENNReal.ofReal (Sn.indicator
          (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x) ∂volume)
      ≤ ∫⁻ x, (ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)
          + ENNReal.ofReal cbar * ENNReal.ofReal (-(Real.negMulLog (fW x)))) ∂volume :=
        lintegral_mono hbound
    _ = ENNReal.ofReal (|cbar * Real.log cbar|) + ENNReal.ofReal cbar
          * (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (fW x))) ∂volume) := by
        rw [lintegral_add_left hg1_meas, lintegral_const_mul _ hfW_meas, hfW_lint, mul_one,
          lintegral_const_mul _ hnegm_meas]

/-- `⊤`-divergence of the W-marginal entropy: if `h(W) = ⊤`, then `h(W_n) → ⊤` along the
truncations `W_n := truncW P W n`. The argument has three steps: a.e. convergence of the truncated
densities (`truncW_map_density_tendsto_ae`), `A(P.map W) = ⊤`
(`posPart_lintegral_eq_top_of_diffEntExt_top`) combined via Fatou
(`differentialEntropyExt_posPart_le_liminf_of_ae_tendsto`) to force `A(W_n) → ⊤`, and a uniform
bound on `B(W_n)` (`truncW_map_negPart_lintegral_le`), so that `h(W_n) = A - B → ⊤`. Closes by
a.e. convergence of densities alone, with no weak-convergence portmanteau.

@audit:ok -/
theorem differentialEntropyExt_truncW_tendsto_top
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume)
    (hW_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    Tendsto (fun n => differentialEntropyExt ((truncW P W n).map W)) atTop
      (𝓝 (⊤ : EReal)) := by
  classical
  haveI hWmap_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  -- Abbreviations for the positive / negative parts of `Q_n.map W := (truncW P W n).map W`.
  set μW : Measure ℝ := P.map W with hμW_def
  set A : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map W).rnDeriv volume x).toReal)))
      ∂volume with hB_def
  -- each truncated W-marginal is a.c. (`cond` preserves a.c.).
  have hQac : ∀ n, ((truncW P W n).map W) ≪ volume := by
    intro n
    refine (Measure.AbsolutelyContinuous.trans ?_ hW_ac)
    rw [truncW]; exact (ProbabilityTheory.cond_absolutelyContinuous).map hW
  -- **Step (2b): `A(μW) = ⊤`** (positive-part divergence from `h(μW) = ⊤`, `B(μW) < ⊤`).
  have hA_top : (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μW.rnDeriv volume x).toReal)) ∂volume) = ⊤ :=
    posPart_lintegral_eq_top_of_diffEntExt_top hW_ac hW_top
  -- **Step (2a)+(2c): Fatou ⟹ `liminf A = ⊤`**.
  have hfatou := differentialEntropyExt_posPart_le_liminf_of_ae_tendsto μW
    (fun n => (truncW P W n).map W)
    (truncW_map_density_tendsto_ae W P hW hW_ac)
  -- `⊤ = A(μW) ≤ liminf A` ⟹ `liminf A = ⊤`.
  have hliminf_top : Filter.liminf A atTop = ⊤ := by
    rw [hA_def]
    rw [hA_top] at hfatou
    exact top_le_iff.mp hfatou
  -- `A n → ⊤` in ℝ≥0∞ (liminf = ⊤ ⟹ tendsto ⊤).
  have hA_tendsto : Tendsto A atTop (𝓝 (⊤ : ℝ≥0∞)) := by
    apply ENNReal.tendsto_nhds_top
    intro k
    have hk_lt : (k : ℝ≥0∞) < Filter.liminf A atTop := by rw [hliminf_top]; exact ENNReal.coe_lt_top
    exact Filter.eventually_lt_of_lt_liminf hk_lt
  -- **`B n` eventually bounded by a fixed finite constant `C`.**
  -- `C := 1 + 2 * B(μW)` (finite since `B(μW) = hW_negPart_fin < ⊤`).
  set Bμ : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μW.rnDeriv volume x).toReal))) ∂volume with hBμ_def
  set C : ℝ≥0∞ := 1 + 2 * Bμ with hC_def
  have hC_fin : C ≠ ⊤ := by
    rw [hC_def]
    refine ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (by simp) hW_negPart_fin⟩
  have hB_bound : ∀ᶠ n in atTop, B n ≤ C := by
    -- mass of the truncation set and its inverse (real) both → 1.
    set Sn : ℕ → Set ℝ := fun n => {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
    have hSn_mono : Monotone Sn := by
      intro p q hpq r hr
      have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
      exact le_trans hr this
    have hSn_union : ⋃ k, Sn k = Set.univ := by
      rw [Set.eq_univ_iff_forall]; intro r
      obtain ⟨k, hk⟩ := exists_nat_ge |r|
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    set cc : ℕ → ℝ≥0∞ := fun n => μW (Sn n) with hcc_def
    have hcc_lim : Tendsto cc atTop (𝓝 1) := by
      have h := tendsto_measure_iUnion_atTop (μ := μW) hSn_mono
      rw [hSn_union, measure_univ] at h
      exact h
    have hcc_ne : ∀ᶠ n in atTop, cc n ≠ 0 := by
      have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
      exact hcc_lim.eventually_mem h_nhds
    -- inverse-mass (real) `cbar n := (cc n)⁻¹.toReal → 1`.
    have hcbar_lim : Tendsto (fun n => ((cc n)⁻¹).toReal) atTop (𝓝 1) := by
      have hcr_lim : Tendsto (fun n => (cc n).toReal) atTop (𝓝 1) := by
        have := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hcc_lim
        simpa [Function.comp] using this
      have heq : (fun n => ((cc n).toReal)⁻¹) =ᶠ[atTop] fun n => ((cc n)⁻¹).toReal := by
        filter_upwards [hcc_ne] with n hn; rw [ENNReal.toReal_inv]
      refine Tendsto.congr' heq ?_
      have : Tendsto (fun n => ((cc n).toReal)⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
        (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hcr_lim
      simpa using this
    -- eventually `cbar n ≤ 2` and `|cbar n · log (cbar n)| ≤ 1`.
    have hcbar_le : ∀ᶠ n in atTop, ((cc n)⁻¹).toReal ≤ 2 :=
      hcbar_lim.eventually_le_const (by norm_num : (1 : ℝ) < 2)
    have hlog_le : ∀ᶠ n in atTop,
        |((cc n)⁻¹).toReal * Real.log (((cc n)⁻¹).toReal)| ≤ 1 := by
      -- `t ↦ |t · log t|` is continuous and `→ 0` at `1` (`log 1 = 0`); so eventually `≤ 1`.
      have hcont : Tendsto (fun n => |((cc n)⁻¹).toReal * Real.log (((cc n)⁻¹).toReal)|)
          atTop (𝓝 |(1 : ℝ) * Real.log 1|) := by
        apply Tendsto.abs
        exact (hcbar_lim.mul ((Real.continuousAt_log (by norm_num)).tendsto.comp hcbar_lim))
      rw [Real.log_one, mul_zero, abs_zero] at hcont
      exact hcont.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hcc_ne, hcbar_le, hlog_le] with n hcn hcbar2 hlog1
    -- combine the per-`n` bound with the two eventual estimates.
    have hbnd := truncW_map_negPart_lintegral_le W P hW hW_ac n hcn
    calc B n
        ≤ ENNReal.ofReal (|((μW (Sn n))⁻¹).toReal * Real.log (((μW (Sn n))⁻¹).toReal)|)
            + ENNReal.ofReal (((μW (Sn n))⁻¹).toReal) * Bμ := hbnd
      _ ≤ 1 + 2 * Bμ := by
          refine add_le_add ?_ ?_
          · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hlog1
          · refine mul_le_mul' ?_ (le_refl Bμ)
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
            exact ENNReal.ofReal_le_ofReal hcbar2
      _ = C := by rw [hC_def]
  -- **Final EReal Tendsto** via `tendsto_nhds_top_iff_real`.
  rw [EReal.tendsto_nhds_top_iff_real]
  intro M
  -- coe `A n → ⊤` to EReal.
  have hAE_tendsto : Tendsto (fun n => ((A n : EReal))) atTop (𝓝 (⊤ : EReal)) := by
    have : Tendsto (fun n => ((A n : ℝ≥0∞) : EReal)) atTop (𝓝 ((⊤ : ℝ≥0∞) : EReal)) :=
      (continuous_coe_ennreal_ereal.tendsto _).comp hA_tendsto
    rwa [EReal.coe_ennreal_top] at this
  -- eventually `(M + C.toReal : EReal) < A n`.
  have hev_A : ∀ᶠ n in atTop, ((M + C.toReal : ℝ) : EReal) < (A n : EReal) := by
    rw [EReal.tendsto_nhds_top_iff_real] at hAE_tendsto
    exact hAE_tendsto (M + C.toReal)
  -- combine with the `B`-bound and a.c. expansion of `differentialEntropyExt`.
  filter_upwards [hev_A, hB_bound] with n hAn hBn
  -- expand `differentialEntropyExt (Q_n.map W) = (A n : EReal) - (B n : EReal)`.
  rw [differentialEntropyExt_of_ac (hQac n)]
  show ((M : ℝ) : EReal) < (A n : EReal) - (B n : EReal)
  -- `(B n : EReal) ≤ (C.toReal : EReal)`.
  have hBn_fin : B n ≠ ⊤ := ne_top_of_le_ne_top hC_fin hBn
  have hBn_le : (B n : EReal) ≤ ((C.toReal : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_toReal hBn_fin]
    exact_mod_cast (ENNReal.toReal_le_toReal hBn_fin hC_fin).mpr hBn
  -- `M < A n - B n` ⟸ `M + B n < A n` ⟸ `M + C.toReal < A n` and `B n ≤ C.toReal`.
  rw [EReal.lt_sub_iff_add_lt (Or.inl (EReal.coe_ennreal_ne_bot _))
    (Or.inr (EReal.coe_ne_bot _))]
  calc ((M : ℝ) : EReal) + (B n : EReal)
      ≤ ((M : ℝ) : EReal) + ((C.toReal : ℝ) : EReal) := add_le_add (le_refl _) hBn_le
    _ = ((M + C.toReal : ℝ) : EReal) := by rw [← EReal.coe_add]
    _ < (A n : EReal) := hAn

/-- **Step-0 helper for the ⊤-branch assembly — `B(ν_n) ≠ ⊤`** (negative part of the truncated sum
law). `ν_n := (truncW P W n).map (W+V)`. Decomposes `ν_n = (Q_n.map W) ∗ (Q_n.map V)` (independence
preserved under conditioning on the `W`-event `{|W| ≤ n}`), bounds `B(Q_n.map W) ≠ ⊤` via the per-n
explicit bound `truncW_map_negPart_lintegral_le` (finite since `B(W) < ⊤` and `c_n ≠ 0`), then lifts
to the sum law via the single-component finiteness `negPart_negMulLog_conv_single_ne_top`.

@audit:ok -/
private theorem negPart_lintegral_map_truncW_add_ne_top
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hBW : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (n : ℕ) (hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((((truncW P W n).map (fun ω => W ω + V ω)).rnDeriv
        volume x).toReal))) ∂volume) ≠ ⊤ := by
  classical
  set Q : Measure Ω := truncW P W n with hQ_def
  haveI hQ_prob : IsProbabilityMeasure Q := by
    rw [hQ_def, truncW]; exact ProbabilityTheory.cond_isProbabilityMeasure hn
  haveI hQW_prob : IsProbabilityMeasure (Q.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hQV_prob : IsProbabilityMeasure (Q.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  -- W stays a.c. under conditioning.
  have hW_ac_Q : (Q.map W) ≪ volume := by
    refine (Measure.AbsolutelyContinuous.trans ?_ hW_ac)
    rw [hQ_def, truncW]
    exact (ProbabilityTheory.cond_absolutelyContinuous).map hW
  -- W ⊥ V under `Q` (conditioning on a `W`-event preserves independence).
  have hE_meas : MeasurableSet {ω : Ω | |W ω| ≤ (n : ℝ)} := hW.abs measurableSet_Iic
  set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
  have hindep : IndepFun W V Q := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    have hEW : E ∩ W ⁻¹' s = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := by
      ext ω; simp [hE_def, Set.mem_inter_iff, and_comm]
    have hIcc_meas : MeasurableSet {r : ℝ | |r| ≤ (n : ℝ)} :=
      (_root_.continuous_abs.measurable measurableSet_Iic)
    have hAW : MeasurableSet ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := hIcc_meas.inter hs
    rw [hQ_def, truncW, cond_apply hE_meas, cond_apply hE_meas, cond_apply hE_meas]
    have hjoint : E ∩ (W ⁻¹' s ∩ V ⁻¹' t) = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t := by
      rw [← Set.inter_assoc, hEW]
    rw [hjoint, hEW]
    have hfac1 : P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t)
        = P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s)) * P (V ⁻¹' t) :=
      hWV.measure_inter_preimage_eq_mul _ _ hAW ht
    have hEV : E ∩ V ⁻¹' t = W ⁻¹' {r : ℝ | |r| ≤ (n : ℝ)} ∩ V ⁻¹' t := by
      ext ω; simp [hE_def]
    have hfac2 : P (E ∩ V ⁻¹' t) = P E * P (V ⁻¹' t) := by
      rw [hEV, hWV.measure_inter_preimage_eq_mul _ _ hIcc_meas ht, hE_def]; rfl
    rw [hfac1, hfac2]
    have hPE_ne : P E ≠ 0 := by rw [hE_def]; exact hn
    have hPE_ne_top : P E ≠ ∞ := measure_ne_top P E
    have hcancel : (P E)⁻¹ * (P E * P (V ⁻¹' t)) = P (V ⁻¹' t) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hPE_ne hPE_ne_top, one_mul]
    rw [hcancel]; ring
  -- the sum law equals the convolution of the marginals.
  have hsum_conv : Q.map (fun ω => W ω + V ω) = (Q.map W) ∗ (Q.map V) := by
    have := hindep.map_add_eq_map_conv_map hW hV
    simpa [Pi.add_apply] using this
  -- `B(Q.map W) ≠ ⊤` via the explicit per-n bound (finite under `B(W) < ⊤` and `c_n ≠ 0`).
  have hcn' : (P.map W) {r : ℝ | |r| ≤ (n : ℝ)} ≠ 0 := by
    have hmeas : MeasurableSet {r : ℝ | |r| ≤ (n : ℝ)} :=
      _root_.continuous_abs.measurable measurableSet_Iic
    rw [Measure.map_apply hW hmeas]
    have : W ⁻¹' {r : ℝ | |r| ≤ (n : ℝ)} = {ω | |W ω| ≤ (n : ℝ)} := by ext ω; simp
    rw [this]; exact hn
  have hBQW : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((Q.map W).rnDeriv volume x).toReal)))
      ∂volume) ≠ ⊤ := by
    have hbnd := truncW_map_negPart_lintegral_le W P hW hW_ac n hcn'
    rw [← hQ_def] at hbnd
    refine ne_top_of_le_ne_top ?_ hbnd
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBW⟩
  -- lift to the sum law.
  rw [hsum_conv]
  exact negPart_negMulLog_conv_single_ne_top (Q.map W) (Q.map V) hW_ac_Q hBQW

-- Per-`n` upper bound: `h(ν_n) ≤ (2 * Aν : EReal)`, established via per-`n` Gibbs and measure
-- domination. Self-contained block extracted from the `⊤`-branch proof to keep the
-- parent body under the footprint limit.
private theorem differentialEntropyExt_truncW_add_le_two_mul_Aν
    {Ω : Type*} [MeasurableSpace Ω]
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hBW : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (ν : Measure ℝ) (hν_def : ν = P.map (fun ω => W ω + V ω))
    (hν_ac : ν ≪ volume)
    (hBν : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((ν.rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (Aν : ℝ≥0∞)
    (hAν_def : Aν
        = ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((ν.rnDeriv volume x).toReal)) ∂volume)
    [IsProbabilityMeasure ν]
    (hcn_ev : ∀ᶠ n : ℕ in atTop, P {ω | |W ω| ≤ (n : ℝ)} ≠ 0)
    (hcinv_ev : ∀ᶠ n : ℕ in atTop, ((P {ω | |W ω| ≤ (n : ℝ)})⁻¹).toReal ≤ 2) :
    ∀ᶠ n in atTop,
        differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω))
          ≤ ((2 * Aν : ℝ≥0∞) : EReal) := by
  filter_upwards [hcn_ev, hcinv_ev] with n hn hcinv
  set νn : Measure ℝ := (truncW P W n).map (fun ω => W ω + V ω) with hνn_def
  set cinv : ℝ≥0∞ := (P {ω | |W ω| ≤ (n : ℝ)})⁻¹ with hcinv_def
  -- mass `c_n ∈ (0, 1]` so `cinv ∈ [1, ⊤)`.
  have hcinv_top : cinv ≠ ⊤ := by
    rw [hcinv_def]; exact ENNReal.inv_ne_top.mpr hn
  have hcinv_le_two : cinv ≤ (2 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_toReal hcinv_top, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hcinv
  -- measure domination `ν_n ≤ cinv • ν` (atom 1).
  have hdom : νn ≤ cinv • ν := by
    rw [hνn_def, hcinv_def, hν_def]
    exact map_truncW_add_le_smul_map_add W V P hW hV n hn
  -- `ν_n ≪ ν ≪ volume`.
  have hνn_ν : νn ≪ ν := by
    rw [hνn_def, hν_def]
    exact map_truncW_add_absolutelyContinuous_map_add W V P hW hV n hn
  have hνn_ac : νn ≪ volume := hνn_ν.trans hν_ac
  haveI hQ_prob : IsProbabilityMeasure (truncW P W n) := by
    rw [truncW]; exact ProbabilityTheory.cond_isProbabilityMeasure hn
  haveI hνn_prob : IsProbabilityMeasure νn := by
    rw [hνn_def]
    exact Measure.isProbabilityMeasure_map (hW.add hV).aemeasurable
  -- `B(ν_n) ≠ ⊤`.
  have hBνn : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((νn.rnDeriv volume x).toReal)))
      ∂volume) ≠ ⊤ := by
    rw [hνn_def]
    exact negPart_lintegral_map_truncW_add_ne_top W V P hW hV hWV hW_ac hBW n hn
  -- `crossNeg ν_n ν ≤ cinv * crossNeg ν ν = cinv * B(ν)`, hence `≠ ⊤`.
  have hCNνn_dom : crossNeg νn ν ≤ cinv * crossNeg ν ν := by
    rw [crossNeg, crossNeg]
    calc (∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂νn)
        ≤ ∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂(cinv • ν) :=
          lintegral_mono' hdom (le_refl _)
      _ = cinv * ∫⁻ x, ENNReal.ofReal (Real.log ((ν.rnDeriv volume x).toReal)) ∂ν := by
          rw [lintegral_smul_measure]; rfl
  have hCNν_eq : crossNeg ν ν
      = ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume :=
    crossNeg_self ν hν_ac
  have hCNνn_fin : crossNeg νn ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hCNνn_dom
    exact ENNReal.mul_ne_top hcinv_top (by rw [hCNν_eq]; exact hBν)
  -- Gibbs (consumer form): `A(ν_n) + crossNeg ≤ crossPos + B(ν_n)`.
  have hgibbs := ennreal_gibbs_rearranged hνn_ac hν_ac hνn_ν hBνn hCNνn_fin
  -- `A(ν_n) ≤ crossPos ν_n ν + B(ν_n)`  (drop the nonneg `crossNeg`).
  have hA_le : (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((νn.rnDeriv volume x).toReal)) ∂volume)
      ≤ crossPos νn ν
        + ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((νn.rnDeriv volume x).toReal))) ∂volume :=
    le_trans (le_add_right (le_refl _)) hgibbs
  -- `h(ν_n) = (A(ν_n):EReal) - (B(ν_n):EReal) ≤ (crossPos ν_n ν : EReal)`.
  have hh_le : differentialEntropyExt νn ≤ ((crossPos νn ν : ℝ≥0∞) : EReal) := by
    rw [differentialEntropyExt_of_ac hνn_ac]
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ennreal_ne_bot _))
      (Or.inl ((EReal.coe_ennreal_eq_top_iff).not.mpr hBνn))]
    rw [← EReal.coe_ennreal_add]
    exact_mod_cast hA_le
  -- domination of the positive cross-entropy: `crossPos ν_n ν ≤ cinv * Aν ≤ 2 * Aν`.
  have hCPνn_dom : crossPos νn ν ≤ (2 : ℝ≥0∞) * Aν := by
    have hstep : crossPos νn ν ≤ cinv * crossPos ν ν := by
      rw [crossPos, crossPos]
      calc (∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂νn)
          ≤ ∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂(cinv • ν) :=
            lintegral_mono' hdom (le_refl _)
        _ = cinv * ∫⁻ x, ENNReal.ofReal (-Real.log ((ν.rnDeriv volume x).toReal)) ∂ν := by
            rw [lintegral_smul_measure]; rfl
    have hCPν_eq : crossPos ν ν = Aν := by
      rw [hAν_def]; exact crossPos_self ν hν_ac
    calc crossPos νn ν ≤ cinv * crossPos ν ν := hstep
      _ = cinv * Aν := by rw [hCPν_eq]
      _ ≤ (2 : ℝ≥0∞) * Aν := by exact mul_le_mul' hcinv_le_two (le_refl _)
  -- chain: `h(ν_n) ≤ (crossPos ν_n ν : EReal) ≤ (2 * Aν : EReal)`.
  calc differentialEntropyExt νn ≤ ((crossPos νn ν : ℝ≥0∞) : EReal) := hh_le
    _ ≤ ((2 * Aν : ℝ≥0∞) : EReal) := by exact_mod_cast hCPνn_dom

/-- Unconditional `⊤`-branch of gateway monotonicity: `h(W) = ⊤ ⟹ h(W+V) = ⊤`. Combines per-`n`
monotonicity `h(W_n) ≤ h(W_n + V)` (`differentialEntropyExt_mono_add_truncW`) with the divergence
`h(W_n) → ⊤` (`differentialEntropyExt_truncW_tendsto_top`) to squeeze `h(W_n + V) → ⊤`, then derives
`A(ν) = ⊤` via per-`n` Gibbs and measure domination. The only hypotheses are the regularity
preconditions `hW`/`hV`/`hWV`/`hW_ac` together with the case condition `hW_top`.

@audit:ok -/
theorem differentialEntropyExt_top_of_indep_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  classical
  -- ν := P.map(W+V),  ν_n := (truncW P W n).map(W+V),  c_n := P{|W| ≤ n}.
  set ν : Measure ℝ := P.map (fun ω => W ω + V ω) with hν_def
  haveI hμW_prob : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hμV_prob : IsProbabilityMeasure (P.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  haveI hν_prob : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (hW.add hV).aemeasurable
  -- **Step 0 — regularity.**
  -- ν = (P.map W) ∗ (P.map V) (independence).
  have hconv : ν = (P.map W) ∗ (P.map V) := by
    rw [hν_def]; exact hWV.map_add_eq_map_conv_map hW hV
  -- B(P.map W) ≠ ⊤ from h(W) = ⊤  (Step-0 helper, avoids adding a hypothesis to the signature).
  have hBW : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
      ∂volume) ≠ ⊤ := negPart_lintegral_ne_top_of_diffEntExt_top hW_ac hW_top
  -- ν ≪ volume (convolution with an a.c. left factor is a.c.).
  have hν_ac : ν ≪ volume := by
    rw [hconv, conv_eq_withDensity_translate_average (P.map W) (P.map V) hW_ac]
    exact withDensity_absolutelyContinuous _ _
  -- B(ν) ≠ ⊤ (single-component negative-part finiteness of the sum law).
  have hBν : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume)
      ≠ ⊤ := by
    rw [hconv]
    exact negPart_negMulLog_conv_single_ne_top (P.map W) (P.map V) hW_ac hBW
  -- **Step 1 — `h(ν_n) → ⊤`** (squeeze: per-n monotone below a tendsto-⊤ sequence).
  -- `h(Q_n.map W) → ⊤`.
  have hW_tendsto : Tendsto (fun n => differentialEntropyExt ((truncW P W n).map W)) atTop
      (𝓝 (⊤ : EReal)) :=
    differentialEntropyExt_truncW_tendsto_top W P hW hW_ac hBW hW_top
  -- eventually positive mass `c_n ≠ 0`.
  have hcn_ev : ∀ᶠ n : ℕ in atTop, P {ω | |W ω| ≤ (n : ℝ)} ≠ 0 := by
    set E : ℕ → Set Ω := fun n => {ω | |W ω| ≤ (n : ℝ)} with hE_def
    have hE_mono : Monotone E := by
      intro p q hpq ω hω
      have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
      exact le_trans hω this
    have hE_union : ⋃ k, E k = Set.univ := by
      rw [Set.eq_univ_iff_forall]; intro ω
      obtain ⟨k, hk⟩ := exists_nat_ge |W ω|
      exact Set.mem_iUnion.2 ⟨k, hk⟩
    have hlim : Tendsto (fun n => P (E n)) atTop (𝓝 1) := by
      have h := tendsto_measure_iUnion_atTop (μ := P) hE_mono
      rw [hE_union, measure_univ] at h
      exact h
    have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
    exact hlim.eventually_mem h_nhds
  -- per-n monotone (eventually): `h(Q_n.map W) ≤ h(ν_n)`.
  have hmono_ev : ∀ᶠ n in atTop,
      differentialEntropyExt ((truncW P W n).map W)
        ≤ differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)) := by
    filter_upwards [hcn_ev] with n hn
    exact differentialEntropyExt_mono_add_truncW W V P hW hV hWV hW_ac hBW n hn
  -- squeeze to get `h(ν_n) → ⊤`.
  have hνn_tendsto : Tendsto (fun n => differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)))
      atTop (𝓝 (⊤ : EReal)) := by
    rw [EReal.tendsto_nhds_top_iff_real]
    intro M
    rw [EReal.tendsto_nhds_top_iff_real] at hW_tendsto
    filter_upwards [hW_tendsto M, hmono_ev] with n hMn hmn
    exact lt_of_lt_of_le hMn hmn
  -- **Steps 2–4 — `A(ν) = ⊤`** (by_contra + per-n Gibbs + measure domination).
  set Aν : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((ν.rnDeriv volume x).toReal)) ∂volume
    with hAν_def
  have hAν_top : Aν = ⊤ := by
    by_contra hAν_ne
    -- eventually `c_n⁻¹ ≤ 2`.
    have hcinv_ev : ∀ᶠ n : ℕ in atTop, ((P {ω | |W ω| ≤ (n : ℝ)})⁻¹).toReal ≤ 2 := by
      set E : ℕ → Set Ω := fun n => {ω | |W ω| ≤ (n : ℝ)} with hE_def
      have hE_mono : Monotone E := by
        intro p q hpq ω hω
        have : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
        exact le_trans hω this
      have hE_union : ⋃ k, E k = Set.univ := by
        rw [Set.eq_univ_iff_forall]; intro ω
        obtain ⟨k, hk⟩ := exists_nat_ge |W ω|
        exact Set.mem_iUnion.2 ⟨k, hk⟩
      have hlim : Tendsto (fun n => P (E n)) atTop (𝓝 1) := by
        have h := tendsto_measure_iUnion_atTop (μ := P) hE_mono
        rw [hE_union, measure_univ] at h
        exact h
      -- `(P (E n))⁻¹.toReal → 1`.
      have hcinv_lim : Tendsto (fun n => ((P (E n))⁻¹).toReal) atTop (𝓝 1) := by
        have hr_lim : Tendsto (fun n => (P (E n)).toReal) atTop (𝓝 1) := by
          have := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞) ≠ ⊤)).comp hlim
          simpa [Function.comp] using this
        have heq : (fun n => ((P (E n)).toReal)⁻¹) =ᶠ[atTop] fun n => ((P (E n))⁻¹).toReal := by
          filter_upwards [hcn_ev] with n hn; rw [ENNReal.toReal_inv]
        refine Tendsto.congr' heq ?_
        have : Tendsto (fun n => ((P (E n)).toReal)⁻¹) atTop (𝓝 (1 : ℝ)⁻¹) :=
          (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr_lim
        simpa using this
      exact hcinv_lim.eventually_le_const (by norm_num : (1 : ℝ) < 2)
    -- the finite EReal upper bound `(2 * Aν : EReal)`.
    -- eventually `h(ν_n) ≤ (2 * Aν : EReal)`.
    have hub : ∀ᶠ n in atTop,
        differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω))
          ≤ ((2 * Aν : ℝ≥0∞) : EReal) :=
      differentialEntropyExt_truncW_add_le_two_mul_Aν W V P hW hV hWV hW_ac hBW
        ν hν_def hν_ac hBν Aν hAν_def hcn_ev hcinv_ev
    -- contradiction with `h(ν_n) → ⊤`.
    rw [EReal.tendsto_nhds_top_iff_real] at hνn_tendsto
    have h2Aν_fin : (2 * Aν) ≠ ⊤ := ENNReal.mul_ne_top (by simp) hAν_ne
    -- pick `M` larger than `(2 * Aν).toReal` and derive `(M:EReal) < h(ν_n) ≤ (2*Aν:EReal) ≤ (M:EReal)`.
    have hcontra := hνn_tendsto ((2 * Aν).toReal)
    obtain ⟨n, hMn, hubn⟩ := (hcontra.and hub).exists
    have : ((2 * Aν : ℝ≥0∞) : EReal) = (((2 * Aν).toReal : ℝ) : EReal) :=
      (EReal.coe_ennreal_toReal h2Aν_fin).symm
    rw [this] at hubn
    exact absurd (lt_of_lt_of_le hMn hubn) (by simp)
  -- **conclude `h(ν) = ⊤`** : `h(ν) = (Aν:EReal) - (B(ν):EReal) = ⊤ - fin = ⊤`.
  rw [differentialEntropyExt_of_ac hν_ac, ← hAν_def, hAν_top, EReal.coe_ennreal_top,
    ← EReal.coe_ennreal_toReal hBν, EReal.top_sub_coe]

/-! ## Unconditional gateway monotonicity

Gateway monotonicity is assembled unconditionally from three pieces: the `⊥` branch (`bot_le`), the
finite branch (`differentialEntropyExt_mono_add_of_integrable`, per-fibre Gibbs), and the `⊤` branch
(`differentialEntropyExt_top_of_indep_add_unconditional`). The finite branch goes through the
finiteness-to-integrability bridge `differentialEntropyExt_integrable_of_finite`. -/

/-- Finite differential entropy implies integrability of `negMulLog ∘ density` (the converse of
`differentialEntropyExt_of_ac_integrable`): from `μ ≪ volume`, `h(μ) ≠ ⊤`, and `h(μ) ≠ ⊥`, the
function `negMulLog ((μ.rnDeriv volume ·).toReal)` is `volume`-integrable. Both `A` and `B` (the
positive- and negative-part `lintegral`s) are then finite, giving `HasFiniteIntegral`.

@audit:ok -/
theorem differentialEntropyExt_integrable_of_finite {μ : Measure ℝ} (hac : μ ≪ volume)
    (hne_top : differentialEntropyExt μ ≠ ⊤) (hne_bot : differentialEntropyExt μ ≠ ⊥) :
    Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume := by
  -- positive- and negative-part lintegrals of the density's `negMulLog`.
  set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume
    with hA_def
  set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal))) ∂volume
    with hB_def
  -- `h(μ) = (A : EReal) - (B : EReal)`.
  have hsplit : differentialEntropyExt μ = (A : EReal) - (B : EReal) := by
    rw [differentialEntropyExt_of_ac hac]
  -- **`A ≠ ⊤`**: otherwise `⊤ - B` is `⊤` (B≠⊤) or `⊥` (B=⊤), both excluded.
  have hA_ne_top : A ≠ ⊤ := by
    intro hAtop
    by_cases hBtop : (B : EReal) = ⊤
    · -- `⊤ - ⊤ = ⊥` contradicts `hne_bot`.
      apply hne_bot
      rw [hsplit, hAtop, EReal.coe_ennreal_top, hBtop, EReal.sub_top]
    · -- `⊤ - (coe) = ⊤` contradicts `hne_top`.
      apply hne_top
      rw [hsplit, hAtop, EReal.coe_ennreal_top, EReal.top_sub hBtop]
  -- **`B ≠ ⊤`**: with `A < ⊤`, `(A : EReal) - ⊤ = ⊥` contradicts `hne_bot`.
  have hB_ne_top : B ≠ ⊤ := by
    intro hBtop
    apply hne_bot
    rw [hsplit, hBtop, EReal.coe_ennreal_top, EReal.sub_top]
  -- assemble integrability from the two finite lintegrals + measurability.
  refine integrable_of_lintegral_ofReal_pos_neg_ne_top ?_ hA_ne_top hB_ne_top
  exact (Real.continuous_negMulLog.measurable.comp
    (μ.measurable_rnDeriv volume).ennreal_toReal).aestronglyMeasurable

/-- Unconditional gateway monotonicity: `W` a.c. and `W ⊥ V ⟹ h(W) ≤ h(W+V)`. The proof splits into
the `⊥` branch (`bot_le`), the finite branch (`differentialEntropyExt_mono_add_of_integrable` via the
finiteness-to-integrability bridge), and the `⊤` branch
(`differentialEntropyExt_top_of_indep_add_unconditional`).

@audit:ok -/
theorem differentialEntropyExt_mono_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) :
    differentialEntropyExt (P.map W) ≤ differentialEntropyExt (P.map (fun ω => W ω + V ω)) := by
  -- **⊥ branch**: `h(W) = ⊥ ≤ anything`.
  rcases eq_bot_or_bot_lt (differentialEntropyExt (P.map W)) with hbot | hpos
  · rw [hbot]; exact bot_le
  · have hne_bot : differentialEntropyExt (P.map W) ≠ ⊥ := hpos.ne'
    by_cases htop : differentialEntropyExt (P.map W) = ⊤
    · -- **⊤ branch**: route β' gives `h(W+V) = ⊤`, so `⊤ ≤ ⊤`.
      rw [htop, differentialEntropyExt_top_of_indep_add_unconditional W V P hW hV hWV hW_ac htop]
    · -- **finite branch**: bridge finiteness → integrability, then per-fibre Gibbs.
      exact differentialEntropyExt_mono_add_of_integrable W V P hW hV hWV hW_ac
        (differentialEntropyExt_integrable_of_finite hW_ac htop hne_bot)

/-- Unconditional gateway atom: `W` a.c. and `W ⊥ V ⟹ N(W+V) ≥ N(W)`. Lifts
`differentialEntropyExt_mono_add_unconditional` along `EReal.exp_monotone` to `entropyPowerExt`.

@audit:ok -/
theorem entropyPowerExt_mono_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume) :
    entropyPowerExt (P.map (fun ω => W ω + V ω)) ≥ entropyPowerExt (P.map W) := by
  unfold entropyPowerExt
  apply EReal.exp_monotone
  exact mul_le_mul_of_nonneg_left
    (differentialEntropyExt_mono_add_unconditional W V P hW hV hWV hW_ac) (by norm_num)


end InformationTheory.Shannon
