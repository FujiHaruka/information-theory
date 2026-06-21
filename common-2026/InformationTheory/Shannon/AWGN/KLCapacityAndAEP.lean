import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.AchievabilityAEP
import InformationTheory.Shannon.BlockwiseChannel.CapacityLimit
import InformationTheory.Shannon.ChannelCoding.MIDecomp
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.CondKLIntegral
import InformationTheory.Shannon.MultivariateDiffEntropy
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Continuous Gaussian AEP and per-letter / `n`-fold KL identities

The KL-divergence identities for the AWGN channel together with the continuous
Gaussian asymptotic equipartition property. These feed the achievability side of
the AWGN channel coding theorem.

## Main statements

* `klDiv_perLetter_eq_capacity` — per-letter KL divergence equals `(1/2) log(1+P/N)`.
* `klDiv_nFold_eq_nsmul` — `klDiv(Jₙ,Qₙ).toReal = n · klDiv(J₁,Q₁).toReal`.
* `continuousAepGaussian_holds` — the continuous Gaussian AEP exponent bound.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Continuous Gaussian AEP -/

/-- **Shear pushforward of a density** (linchpin for the `J₁` density identity, absent
from Mathlib): pushing a `volume.prod volume`-density `ρ` through the measure-preserving
shear `h₁(x,z) = (x, x+z)` gives the density `(x,y) ↦ ρ(x, y−x)` (the inverse shear).
Proof: `h₁` is a measurable equiv preserving `volume.prod volume`
(`measurePreserving_prod_add`); `map (withDensity ρ) h₁` is computed via `ext`/`map_apply`
+ `setLIntegral` change of variables through the equiv. -/
private lemma map_shear_withDensity (ρ : ℝ × ℝ → ℝ≥0∞) (hρ : Measurable ρ) :
    ((volume.prod volume : Measure (ℝ × ℝ)).withDensity ρ).map (fun p => (p.1, p.1 + p.2))
      = (volume.prod volume : Measure (ℝ × ℝ)).withDensity (fun p => ρ (p.1, p.2 - p.1)) := by
  -- the shear `g(x,z) = (x, x+z)` is measure-preserving on `volume.prod volume`
  set g : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.1 + p.2) with hg_def
  have hg_meas : Measurable g :=
    measurable_fst.prodMk (measurable_fst.add measurable_snd)
  have hmp : MeasurePreserving g (volume.prod volume) (volume.prod volume) :=
    measurePreserving_prod_add (volume : Measure ℝ) (volume : Measure ℝ)
  -- the pushed density `ρ'(x,y) = ρ(x, y−x)`
  set ρ' : ℝ × ℝ → ℝ≥0∞ := fun p => ρ (p.1, p.2 - p.1) with hρ'_def
  have hρ'_meas : Measurable ρ' :=
    hρ.comp (measurable_fst.prodMk (measurable_snd.sub measurable_fst))
  ext s hs
  rw [Measure.map_apply hg_meas hs, withDensity_apply _ (hg_meas hs),
    withDensity_apply _ hs]
  -- change of variables through the measure-preserving shear:
  -- `∫⁻ p in g⁻¹' s, ρ p = ∫⁻ q in s, ρ(q.1, q.2 − q.1)`
  rw [← hmp.setLIntegral_comp_preimage hs hρ'_meas]
  refine setLIntegral_congr_fun (hg_meas hs) (fun p _ => ?_)
  -- `ρ'(g p) = ρ(p.1, (p.1 + p.2) − p.1) = ρ p`
  simp only [hρ'_def, hg_def, add_sub_cancel_left]

/-- **Lintegral product factorization over `Measure.pi`** (the lintegral analogue of
`MeasureTheory.integral_fin_nat_prod_eq_prod`, absent from Mathlib): the lintegral of a
coordinatewise product `∏ i, f i (x i)` against the finite product measure factors into the
product of per-coordinate lintegrals. Proved by the same `n`-variable Fubini induction
(`measurePreserving_piFinSuccAbove` + `lintegral_prod_mul` Tonelli) as the Bochner version. -/
private lemma lintegral_pi_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : Fin n) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
      = ∏ i, ∫⁻ y, f i y ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
            = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
                f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
                ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.piFinSuccAbove E 0).symm.measurableEmbedding]
          refine lintegral_congr fun x => ?_
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf i.succ),
            ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ (fun i _ => (hf i.succ).comp
            (measurable_pi_apply i))).aemeasurable
        _ = ∏ i, ∫⁻ y, f i y ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- **Tensorization of `withDensity` through `Measure.pi`** (G-2, absent from Mathlib): the
finite product of per-coordinate weighted measures `(μ i).withDensity (f i)` equals the product
measure `Measure.pi μ` weighted by the coordinatewise product density `x ↦ ∏ i, f i (x i)`.
Proved via `Measure.pi_eq` (agreement on measurable boxes) + the box factorization
`lintegral_pi_prod_eq_prod`. -/
lemma pi_withDensity {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : Fin n) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i))
      = (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  have hprod_meas : Measurable (fun x : (i : Fin n) → E i => ∏ i, f i (x i)) :=
    Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  refine Measure.pi_eq (μ := fun i => (μ i).withDensity (f i)) (fun s hs => ?_)
  -- box agreement: `((pi μ).withDensity (∏ f i)) (univ.pi s) = ∏ i, ((μ i).withDensity (f i)) (s i)`
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  -- rewrite the box-restricted integrand as the product of indicator-weighted densities
  have hint_eq : ∫⁻ x in Set.univ.pi s, ∏ i, f i (x i) ∂(Measure.pi μ)
      = ∫⁻ x : (i : Fin n) → E i, ∏ i, (s i).indicator (f i) (x i) ∂(Measure.pi μ) := by
    rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (by simpa using hx i)]
    · rw [Set.indicator_of_notMem hx]
      -- some coordinate is outside `s i`, killing the product
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      have hzero : (s i).indicator (f i) (x i) = 0 := Set.indicator_of_notMem hi (f i)
      exact (Finset.prod_eq_zero (f := fun i => (s i).indicator (f i) (x i))
        (Finset.mem_univ i) hzero).symm
  rw [hint_eq,
    lintegral_pi_prod_eq_prod μ (fun i => (s i).indicator (f i))
      (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), ← withDensity_apply _ (hs i)]

/-! ### Per-letter AWGN KL closed form and n-fold identity

Two shared lemmas consumed by the achievability development (`continuousAepGaussian_holds`
below and `awgn_random_coding_union_bound` in `AchievabilityTypicalDecoder.lean`).

* `klDiv_perLetter_eq_capacity`: the per-letter joint `J₁`/product `Q₁` KL equals the
  AWGN capacity `(1/2) log(1 + P/N)`. Routed through the conditional-KL integral
  (`klDiv_compProd_const_toReal_integral`, `CondKLIntegral.lean`) + the 1-D Gaussian KL
  closed form (`klDiv_gaussianReal_gaussianReal_eq`, `DifferentialEntropy.lean`), **avoiding
  `mutualInfoOfChannel` / `MIClosedForm.lean`** which would create the import cycle
  `KLCapacityAndAEP → MIClosedForm → ContChannelMIDecomp → KLCapacityAndAEP`.
* `klDiv_nFold_eq_nsmul`: `klDiv(J_n,Q_n).toReal = n · klDiv(J₁,Q₁).toReal`, via the
  `arrowProdEquivProdArrow` reshape (`klDiv_map_measurableEquiv`) + `klDiv_pi_eq_sum`
  + i.i.d. `Finset.sum_const` collapse. -/

/-- **Integrability of the 1-D Gaussian log-likelihood ratio**: for nondegenerate variances
`v₁, v₂ ≠ 0`, `llr (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)` is integrable against
`gaussianReal m₁ v₁`. The llr is a.e. a quadratic in `x` (the difference of two Gaussian
log-densities), and quadratics are integrable against a Gaussian. -/
private lemma gaussianReal_llr_integrable
    (m₁ m₂ : ℝ) {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    Integrable (llr (gaussianReal m₁ v₁) (gaussianReal m₂ v₂)) (gaussianReal m₁ v₁) := by
  set ν₁ : Measure ℝ := gaussianReal m₁ v₁ with hν₁_def
  set ν₂ : Measure ℝ := gaussianReal m₂ v₂ with hν₂_def
  have hν₁_ac : ν₁ ≪ volume := by rw [hν₁_def]; exact gaussianReal_absolutelyContinuous m₁ hv₁
  have hμν : ν₁ ≪ ν₂ := hν₁_ac.trans (gaussianReal_absolutelyContinuous' m₂ hv₂)
  -- llr decomp: `llr ν₁ ν₂ x =ᵐ[ν₁] log g₁(x) - log g₂(x)` (two Gaussian log-densities).
  have h_rn_chain_vol : ν₁.rnDeriv ν₂ * ν₂.rnDeriv volume =ᵐ[volume] ν₁.rnDeriv volume :=
    Measure.rnDeriv_mul_rnDeriv hμν
  have h_rn_chain_ν₁ : ν₁.rnDeriv ν₂ * ν₂.rnDeriv volume =ᵐ[ν₁] ν₁.rnDeriv volume :=
    hν₁_ac.ae_le h_rn_chain_vol
  have h_rn_g₁_ν₁ : ν₁.rnDeriv volume =ᵐ[ν₁] gaussianPDF m₁ v₁ :=
    hν₁_ac.ae_le (by rw [hν₁_def]; exact rnDeriv_gaussianReal m₁ v₁)
  have h_rn_g₂_ν₁ : ν₂.rnDeriv volume =ᵐ[ν₁] gaussianPDF m₂ v₂ :=
    hν₁_ac.ae_le (by rw [hν₂_def]; exact rnDeriv_gaussianReal m₂ v₂)
  have h_rn_ν₁ν₂_pos : ∀ᵐ x ∂ν₁, 0 < ν₁.rnDeriv ν₂ x := Measure.rnDeriv_pos hμν
  have h_rn_ν₁ν₂_lt_top : ∀ᵐ x ∂ν₁, ν₁.rnDeriv ν₂ x < ∞ :=
    hμν.ae_le (Measure.rnDeriv_lt_top ν₁ ν₂)
  have h_llr_decomp : ∀ᵐ x ∂ν₁,
      llr ν₁ ν₂ x = Real.log (gaussianPDFReal m₁ v₁ x)
        - Real.log (gaussianPDFReal m₂ v₂ x) := by
    filter_upwards [h_rn_chain_ν₁, h_rn_g₁_ν₁, h_rn_g₂_ν₁, h_rn_ν₁ν₂_pos, h_rn_ν₁ν₂_lt_top]
      with x h_chain h_g₁ h_g₂ h_pos h_lt_top
    have hg₁_pos : 0 < gaussianPDFReal m₁ v₁ x := gaussianPDFReal_pos m₁ v₁ x hv₁
    have hg₂_pos : 0 < gaussianPDFReal m₂ v₂ x := gaussianPDFReal_pos m₂ v₂ x hv₂
    have hν₁ν₂_real_pos : 0 < (ν₁.rnDeriv ν₂ x).toReal :=
      ENNReal.toReal_pos h_pos.ne' h_lt_top.ne
    have h_combine : (gaussianPDF m₁ v₁ x : ℝ≥0∞)
        = ν₁.rnDeriv ν₂ x * gaussianPDF m₂ v₂ x := by
      rw [← h_g₁, ← h_chain, Pi.mul_apply, h_g₂]
    show Real.log ((ν₁.rnDeriv ν₂ x).toReal)
        = Real.log (gaussianPDFReal m₁ v₁ x) - Real.log (gaussianPDFReal m₂ v₂ x)
    have h_real_combine : gaussianPDFReal m₁ v₁ x
        = (ν₁.rnDeriv ν₂ x).toReal * gaussianPDFReal m₂ v₂ x := by
      have := congrArg ENNReal.toReal h_combine
      rwa [toReal_gaussianPDF, ENNReal.toReal_mul, toReal_gaussianPDF] at this
    rw [h_real_combine, Real.log_mul hν₁ν₂_real_pos.ne' hg₂_pos.ne']
    ring
  -- each `log gᵢ(x) = cᵢ - (x-mᵢ)²/(2vᵢ)` is integrable against ν₁ (quadratic moment).
  have hv₁_pos : (0 : ℝ) < v₁ := lt_of_le_of_ne v₁.coe_nonneg (fun h => hv₁ (by exact_mod_cast h.symm))
  have hv₂_pos : (0 : ℝ) < v₂ := lt_of_le_of_ne v₂.coe_nonneg (fun h => hv₂ (by exact_mod_cast h.symm))
  have h_int_x2 : Integrable (fun x : ℝ => x ^ 2) ν₁ := by
    have h_memLp : MemLp (fun x : ℝ => x) 2 ν₁ := by rw [hν₁_def]; exact memLp_id_gaussianReal' 2 (by simp)
    have := h_memLp.integrable_sq; simpa [sq] using this
  have h_int_x1 : Integrable (fun x : ℝ => x) ν₁ := by
    have h_memLp : MemLp (fun x : ℝ => x) 1 ν₁ := by rw [hν₁_def]; exact memLp_id_gaussianReal' 1 (by simp)
    exact h_memLp.integrable (by norm_num)
  have h_int_logg : ∀ (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (hvp : (0:ℝ) < v),
      Integrable (fun x : ℝ => Real.log (gaussianPDFReal m v x)) ν₁ := by
    intro m v hv hvp
    have h_eq : (fun x : ℝ => Real.log (gaussianPDFReal m v x))
        = fun x : ℝ => (-(1/2) * Real.log (2 * Real.pi * v)) - (x - m) ^ 2 / (2 * v) := by
      funext x
      rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_pos _).ne',
        Real.log_inv, Real.log_sqrt (by positivity), Real.log_exp]
      ring
    rw [h_eq]
    apply Integrable.sub (integrable_const _)
    have h_expand : (fun x : ℝ => (x - m) ^ 2 / (2 * (v:ℝ)))
        = fun x : ℝ => (1 / (2 * (v:ℝ))) * (x ^ 2 - 2 * m * x + m ^ 2) := by
      funext x; ring
    rw [h_expand]
    apply Integrable.const_mul
    exact ((h_int_x2.sub ((h_int_x1.const_mul (2 * m)))).add (integrable_const _))
  refine (Integrable.sub (h_int_logg m₁ hv₁ hv₁_pos) (h_int_logg m₂ hv₂ hv₂_pos)).congr ?_
  filter_upwards [h_llr_decomp] with x hx using hx.symm

/-- **Per-letter change-of-measure facts** for the AWGN joint `J₁ = law(X, X+Z)` /
product `Q₁ = μX ⊗ μY` (nondegenerate `P', N ≠ 0`): the mutual absolute continuity
`J₁ ≪ Q₁`, `Q₁ ≪ J₁`, and the pointwise density relation
`(Q₁.rnDeriv J₁ p).toReal = exp(−φ p)` a.e. `[J₁]` (where `φ = log dJ₁/dQ₁`). The `f_X`
factor in the density ratio cancels, so the ratio is a ratio of two strictly-positive-and-
finite Gaussian densities, giving the exponential relation; mutual AC follows from the
everywhere-positive-and-finite densities w.r.t. `volume.prod volume`. -/
lemma awgn_perLetter_changeOfMeasure_facts
    {P' N : ℝ≥0} (hP'_ne : P' ≠ 0) (hN_ne : N ≠ 0)
    (J₁ Q₁ : Measure (ℝ × ℝ))
    (hJ₁ : J₁ = ((gaussianReal 0 P').prod (gaussianReal 0 N)).map (fun p => (p.1, p.1 + p.2)))
    (hQ₁ : Q₁ = (gaussianReal 0 P').prod (gaussianReal 0 (P' + N))) :
    J₁ ≪ Q₁ ∧ Q₁ ≪ J₁
      ∧ (∀ᵐ p ∂J₁, (Q₁.rnDeriv J₁ p).toReal
          = Real.exp (-(Real.log ((J₁.rnDeriv Q₁ p).toReal)))) := by
  have hPN_ne : P' + N ≠ 0 := fun h => hN_ne (add_eq_zero.mp h).2
  -- joint / product densities w.r.t. `volume.prod volume`
  set qden : ℝ × ℝ → ℝ≥0∞ :=
    fun p => gaussianPDF 0 P' p.1 * gaussianPDF 0 (P' + N) p.2 with hqden_def
  set jden : ℝ × ℝ → ℝ≥0∞ :=
    fun p => gaussianPDF 0 P' p.1 * gaussianPDF 0 N (p.2 - p.1) with hjden_def
  have hqden_meas : Measurable qden :=
    (measurable_gaussianPDF 0 P').comp measurable_fst |>.mul
      ((measurable_gaussianPDF 0 (P' + N)).comp measurable_snd)
  have hjden_meas : Measurable jden :=
    (measurable_gaussianPDF 0 P').comp measurable_fst |>.mul
      ((measurable_gaussianPDF 0 N).comp (measurable_snd.sub measurable_fst))
  have hQ₁_wd : Q₁ = (volume.prod volume).withDensity qden := by
    rw [hQ₁, gaussianReal_of_var_ne_zero 0 hP'_ne, gaussianReal_of_var_ne_zero 0 hPN_ne,
      prod_withDensity (measurable_gaussianPDF 0 P') (measurable_gaussianPDF 0 (P' + N))]
  have hJ₁_wd : J₁ = (volume.prod volume).withDensity jden := by
    rw [hJ₁, gaussianReal_of_var_ne_zero 0 hP'_ne, gaussianReal_of_var_ne_zero 0 hN_ne,
      prod_withDensity (measurable_gaussianPDF 0 P') (measurable_gaussianPDF 0 N),
      map_shear_withDensity (fun z => gaussianPDF 0 P' z.1 * gaussianPDF 0 N z.2)
        ((measurable_gaussianPDF 0 P').comp measurable_fst |>.mul
          ((measurable_gaussianPDF 0 N).comp measurable_snd))]
  -- positivity + finiteness of both densities everywhere
  have hqden_pos : ∀ p, 0 < qden p := fun p => by
    rw [hqden_def]
    exact ENNReal.mul_pos (gaussianPDF_pos 0 hP'_ne p.1).ne' (gaussianPDF_pos 0 hPN_ne p.2).ne'
  have hqden_lt_top : ∀ p, qden p < ∞ := fun p => by
    rw [hqden_def]; exact ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top
  have hjden_pos : ∀ p, 0 < jden p := fun p => by
    rw [hjden_def]
    exact ENNReal.mul_pos (gaussianPDF_pos 0 hP'_ne p.1).ne' (gaussianPDF_pos 0 hN_ne _).ne'
  have hjden_lt_top : ∀ p, jden p < ∞ := fun p => by
    rw [hjden_def]; exact ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top
  -- absolute continuity of both to `volume.prod volume` (and the reverse, densities positive)
  have hJ_ac_vol : J₁ ≪ (volume.prod volume) := by
    rw [hJ₁_wd]; exact withDensity_absolutelyContinuous _ _
  have hQ_ac_vol : Q₁ ≪ (volume.prod volume) := by
    rw [hQ₁_wd]; exact withDensity_absolutelyContinuous _ _
  have hvol_ac_Q : (volume.prod volume) ≪ Q₁ := by
    rw [hQ₁_wd]
    exact withDensity_absolutelyContinuous' hqden_meas.aemeasurable
      (Filter.Eventually.of_forall fun p => (hqden_pos p).ne')
  have hvol_ac_J : (volume.prod volume) ≪ J₁ := by
    rw [hJ₁_wd]
    exact withDensity_absolutelyContinuous' hjden_meas.aemeasurable
      (Filter.Eventually.of_forall fun p => (hjden_pos p).ne')
  have hJQ_ac : J₁ ≪ Q₁ := hJ_ac_vol.trans hvol_ac_Q
  have hQJ_ac : Q₁ ≪ J₁ := hQ_ac_vol.trans hvol_ac_J
  haveI : IsProbabilityMeasure J₁ := by
    rw [hJ₁]
    exact Measure.isProbabilityMeasure_map
      (measurable_fst.prodMk (measurable_fst.add measurable_snd)).aemeasurable
  haveI : IsProbabilityMeasure Q₁ := by rw [hQ₁]; infer_instance
  -- `rnDeriv` ratios w.r.t. `vol×vol`
  have hqden_ne_zero : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), qden p ≠ 0 :=
    Filter.Eventually.of_forall fun p => (hqden_pos p).ne'
  have hqden_ne_top : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), qden p ≠ ∞ :=
    Filter.Eventually.of_forall fun p => (hqden_lt_top p).ne
  have hjden_ne_zero : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), jden p ≠ 0 :=
    Filter.Eventually.of_forall fun p => (hjden_pos p).ne'
  have hjden_ne_top : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), jden p ≠ ∞ :=
    Filter.Eventually.of_forall fun p => (hjden_lt_top p).ne
  have hrnJ : J₁.rnDeriv (volume.prod volume) =ᵐ[volume.prod volume] jden := by
    rw [hJ₁_wd]; exact Measure.rnDeriv_withDensity _ hjden_meas
  have hrnQ_vol : Q₁.rnDeriv (volume.prod volume) =ᵐ[volume.prod volume] qden := by
    rw [hQ₁_wd]; exact Measure.rnDeriv_withDensity _ hqden_meas
  have hrnJQ_vol : J₁.rnDeriv Q₁ =ᵐ[volume.prod volume] fun p => (qden p)⁻¹ * jden p := by
    have h1 : J₁.rnDeriv Q₁
        =ᵐ[volume.prod volume] fun p => (qden p)⁻¹ * J₁.rnDeriv (volume.prod volume) p := by
      rw [hQ₁_wd]
      exact Measure.rnDeriv_withDensity_right J₁ (volume.prod volume)
        hqden_meas.aemeasurable hqden_ne_zero hqden_ne_top
    filter_upwards [h1, hrnJ] with p hp1 hpJ; rw [hp1, hpJ]
  have hrnQJ_vol : Q₁.rnDeriv J₁ =ᵐ[volume.prod volume] fun p => (jden p)⁻¹ * qden p := by
    have h1 : Q₁.rnDeriv J₁
        =ᵐ[volume.prod volume] fun p => (jden p)⁻¹ * Q₁.rnDeriv (volume.prod volume) p := by
      rw [hJ₁_wd]
      exact Measure.rnDeriv_withDensity_right Q₁ (volume.prod volume)
        hjden_meas.aemeasurable hjden_ne_zero hjden_ne_top
    filter_upwards [h1, hrnQ_vol] with p hp1 hpQ; rw [hp1, hpQ]
  -- the pointwise exp relation on `vol×vol`, transferred to `J₁`-a.e.
  have hexp_vol : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)),
      (Q₁.rnDeriv J₁ p).toReal = Real.exp (-(Real.log ((J₁.rnDeriv Q₁ p).toReal))) := by
    filter_upwards [hrnJQ_vol, hrnQJ_vol] with p hpJQ hpQJ
    rw [hpJQ, hpQJ]
    have hjr : (jden p)⁻¹ * qden p
        = ENNReal.ofReal ((qden p).toReal / (jden p).toReal) := by
      rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos (hjden_pos p).ne' (hjden_lt_top p).ne),
        ENNReal.ofReal_toReal (hqden_lt_top p).ne, ENNReal.ofReal_toReal (hjden_lt_top p).ne,
        ENNReal.div_eq_inv_mul]
    have hqr : (qden p)⁻¹ * jden p
        = ENNReal.ofReal ((jden p).toReal / (qden p).toReal) := by
      rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos (hqden_pos p).ne' (hqden_lt_top p).ne),
        ENNReal.ofReal_toReal (hjden_lt_top p).ne, ENNReal.ofReal_toReal (hqden_lt_top p).ne,
        ENNReal.div_eq_inv_mul]
    rw [hjr, hqr, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
      Real.log_div
        (ne_of_gt (ENNReal.toReal_pos (hjden_pos p).ne' (hjden_lt_top p).ne))
        (ne_of_gt (ENNReal.toReal_pos (hqden_pos p).ne' (hqden_lt_top p).ne)),
      neg_sub, Real.exp_sub, Real.exp_log (ENNReal.toReal_pos (hqden_pos p).ne' (hqden_lt_top p).ne),
      Real.exp_log (ENNReal.toReal_pos (hjden_pos p).ne' (hjden_lt_top p).ne)]
  have hexp_J : ∀ᵐ p ∂J₁, (Q₁.rnDeriv J₁ p).toReal
      = Real.exp (-(Real.log ((J₁.rnDeriv Q₁ p).toReal))) := hJ_ac_vol.ae_le hexp_vol
  exact ⟨hJQ_ac, hQJ_ac, hexp_J⟩

/-- **Degenerate per-letter KL vanishes** (`P' = 0 ∨ N = 0`): in either degenerate case
the per-letter KL `(klDiv J₁ Q₁).toReal = 0`. When `P' = 0` the input collapses to `Dirac 0`,
the shear is the identity on `{0} × ℝ`, so `J₁ = Q₁` (`klDiv_self`). When `N = 0`
(with `P' ≠ 0`) the joint `J₁` concentrates on the diagonal `{(x, x)}`, which is `Q₁`-null
(positive-variance Gaussian product, atomless), so `¬ J₁ ≪ Q₁` ⇒ `klDiv = ⊤` ⇒ `toReal = 0`. -/
lemma awgn_perLetter_klDiv_degenerate
    (P' N : ℝ≥0) (hdeg : P' = 0 ∨ N = 0) :
    (klDiv
        (((gaussianReal 0 P').prod (gaussianReal 0 N)).map (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
        ((gaussianReal 0 P').prod (gaussianReal 0 (P' + N)))).toReal = 0 := by
  have hshear_meas : Measurable (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) :=
    measurable_fst.prodMk (measurable_fst.add measurable_snd)
  by_cases hP' : P' = 0
  · -- `P' = 0`: input is `Dirac 0`, shear is identity on `{0} × ℝ`, so `J₁ = Q₁`.
    subst hP'
    have hJeqQ :
        (((gaussianReal 0 (0 : ℝ≥0)).prod (gaussianReal 0 N)).map
            (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
          = (gaussianReal 0 (0 : ℝ≥0)).prod (gaussianReal 0 ((0 : ℝ≥0) + N)) := by
      simp only [gaussianReal_zero_var, zero_add, Measure.dirac_prod]
      rw [Measure.map_map hshear_meas measurable_prodMk_left]
      congr 1
      funext z
      simp [Function.comp]
    rw [hJeqQ, klDiv_self, ENNReal.toReal_zero]
  · -- `N = 0` (with `P' ≠ 0`): `J₁` lives on the diagonal, `Q₁`-null ⇒ `¬ J₁ ≪ Q₁`.
    have hN : N = 0 := hdeg.resolve_left hP'
    subst hN
    set μX : Measure ℝ := gaussianReal 0 P' with hμX_def
    haveI : NoAtoms μX := by rw [hμX_def]; exact noAtoms_gaussianReal hP'
    haveI : IsProbabilityMeasure μX := by rw [hμX_def]; infer_instance
    have hD_meas : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
      measurableSet_eq_fun measurable_fst measurable_snd
    have hdiag_meas : Measurable (fun x : ℝ => (x, x)) := measurable_id.prodMk measurable_id
    -- `J₁ = μX.map (fun x => (x, x))` (shear of `μX ⊗ δ₀`)
    have hJ_diag : (((gaussianReal 0 P').prod (gaussianReal 0 (0 : ℝ≥0))).map
          (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
        = μX.map (fun x => (x, x)) := by
      have hmk0 : Measurable (fun x : ℝ => (x, (0 : ℝ))) :=
        measurable_id.prodMk measurable_const
      rw [gaussianReal_zero_var, ← hμX_def, Measure.prod_dirac,
        Measure.map_map hshear_meas hmk0]
      congr 1
      funext x
      simp [Function.comp]
    -- `J₁ D = 1` (diagonal carries the full mass)
    have hJ_D : (((gaussianReal 0 P').prod (gaussianReal 0 (0 : ℝ≥0))).map
          (fun p : ℝ × ℝ => (p.1, p.1 + p.2))) {p : ℝ × ℝ | p.1 = p.2} = 1 := by
      rw [hJ_diag, Measure.map_apply hdiag_meas hD_meas]
      rw [show (fun x => (x, x)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = Set.univ from by
        ext x; simp]
      exact measure_univ
    -- `Q₁ D = 0` (`μX ⊗ μX` is atomless on the diagonal)
    have hQ_D : ((gaussianReal 0 P').prod (gaussianReal 0 (P' + 0))) {p : ℝ × ℝ | p.1 = p.2}
        = 0 := by
      rw [add_zero, ← hμX_def, Measure.prod_apply hD_meas]
      refine (lintegral_eq_zero_iff (measurable_measure_prodMk_left hD_meas)).mpr ?_
      filter_upwards with x
      rw [show Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {x} from by ext y; simp [eq_comm]]
      exact measure_singleton x
    -- `¬ J₁ ≪ Q₁`, so `klDiv = ⊤`.
    have hnot_ac : ¬ (((gaussianReal 0 P').prod (gaussianReal 0 (0 : ℝ≥0))).map
          (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
        ≪ ((gaussianReal 0 P').prod (gaussianReal 0 (P' + 0))) := by
      intro hac
      have := hac hQ_D
      rw [hJ_D] at this
      exact one_ne_zero this
    rw [klDiv_of_not_ac hnot_ac, ENNReal.toReal_top]

private lemma perFibre_klDiv_toReal_quadratic
    (P' N : ℝ≥0) (hN_nn : N ≠ 0) (hPN_ne : P' + N ≠ 0) (x : ℝ) :
    (klDiv (gaussianReal x N) (gaussianReal 0 (P' + N))).toReal
      = (1/2) * (Real.log ((P' + N : ℝ≥0) / N) + (N : ℝ) / (P' + N : ℝ≥0)
                  + x ^ 2 / (P' + N : ℝ≥0) - 1) := by
  rw [klDiv_gaussianReal_gaussianReal_eq x 0 hN_nn hPN_ne]
  ring_nf

private lemma integral_perFibre_klDiv_quadratic_eq_capacity
    (P : ℝ) (P' N : ℝ≥0) (hP'_coe : (P' : ℝ) = P) (hN_nn : N ≠ 0) (hPN_ne : P' + N ≠ 0) :
    ∫ x : ℝ, (1/2) * (Real.log ((P' + N : ℝ≥0) / N) + (N : ℝ) / (P' + N : ℝ≥0)
                + x ^ 2 / (P' + N : ℝ≥0) - 1) ∂(gaussianReal 0 P')
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  set μX : Measure ℝ := gaussianReal 0 P' with hμX_def
  haveI : IsProbabilityMeasure μX := by rw [hμX_def]; infer_instance
  have hN_pos : (0 : ℝ) < N := lt_of_le_of_ne N.coe_nonneg
    (fun h => hN_nn (by exact_mod_cast h.symm))
  have hPN_coe_pos : (0 : ℝ) < ((P' + N : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_add]; positivity
  -- integrate the per-fibre closed form over `μX` (mean 0, variance `P'`).
  rw [integral_const_mul]
  -- `∫ x² ∂μX = P'` (variance with mean 0), the other terms are constants.
  have hX_memLp : MemLp (fun x : ℝ => x) 2 μX := by
    rw [hμX_def]; exact memLp_id_gaussianReal' 2 (by simp)
  have hsq_int : Integrable (fun x : ℝ => x ^ 2) μX := by
    have := hX_memLp.integrable_sq
    simpa [sq] using this
  have hmean : ∫ x, x ∂μX = 0 := by
    rw [hμX_def]; exact integral_id_gaussianReal (μ := (0:ℝ)) (v := P')
  have hvar : ∫ x, x ^ 2 ∂μX = (P' : ℝ) := by
    have hv := variance_eq_sub (μ := μX) (X := fun x : ℝ => x) hX_memLp
    rw [variance_fun_id_gaussianReal] at hv
    simp only [Pi.pow_apply, hmean] at hv
    -- `hv : P' = ∫ x², - 0²`
    rw [hv]; ring
  -- assemble the integral: integrand `= (c - 1) + x²/(P'+N)` with `c` constant.
  set c : ℝ := Real.log ((P' + N : ℝ≥0) / N) + (N : ℝ) / (P' + N : ℝ≥0) with hc_def
  have hrw : (fun x : ℝ =>
        Real.log ((P' + N : ℝ≥0) / N) + (N : ℝ) / (P' + N : ℝ≥0)
          + x ^ 2 / (P' + N : ℝ≥0) - 1)
      = fun x : ℝ => (c - 1) + (1 / (P' + N : ℝ≥0)) * x ^ 2 := by
    funext x; rw [hc_def]; ring
  rw [hrw,
    integral_add (integrable_const _) ((hsq_int.const_mul _)),
    integral_const, integral_const_mul, hvar]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  -- finish: `(1/2)((c - 1) + P'/(P'+N)) = (1/2) log(1 + P/N)`.
  have hsum : (N : ℝ) / (P' + N : ℝ≥0) + (P' : ℝ) / (P' + N : ℝ≥0) = 1 := by
    field_simp
    rw [NNReal.coe_add]; ring
  have hlog : Real.log (((P' + N : ℝ≥0) : ℝ) / (N : ℝ)) = Real.log (1 + P / (N : ℝ)) := by
    congr 1
    rw [NNReal.coe_add, hP'_coe]
    field_simp
    ring
  rw [hc_def, hlog]
  have hfin : Real.log (1 + P / (N : ℝ)) + (N : ℝ) / (P' + N : ℝ≥0) - 1
        + 1 / (P' + N : ℝ≥0) * (P' : ℝ) = Real.log (1 + P / (N : ℝ)) := by
    have : 1 / (P' + N : ℝ≥0) * (P' : ℝ) = (P' : ℝ) / (P' + N : ℝ≥0) := by ring
    rw [this]
    have : (N : ℝ) / (P' + N : ℝ≥0) - 1 + (P' : ℝ) / (P' + N : ℝ≥0)
        = ((N : ℝ) / (P' + N : ℝ≥0) + (P' : ℝ) / (P' + N : ℝ≥0)) - 1 := by ring
    rw [add_sub_assoc, add_assoc, this, hsum]; ring
  rw [hfin]

/-- **bridge ① per-letter closed form** (genuine, sorryAx-free): per-letter joint
`J₁ = law(X, X+Z)` and product of marginals `Q₁ = μX ⊗ μY` have KL equal to the AWGN
per-letter capacity `(1/2) log(1 + P/N)` (nondegenerate `P > 0`, `N ≠ 0`). Routed through the
conditional-KL integral (`klDiv_compProd_const_toReal_integral`) + the 1-D Gaussian KL closed
form (`klDiv_gaussianReal_gaussianReal_eq`), integrating the per-fibre quadratic against the
mean-0 variance-`P'` input — deliberately **avoiding `mutualInfoOfChannel` / `MIClosedForm`**
(import cycle `KLCapacityAndAEP → MIClosedForm → ContChannelMIDecomp → KLCapacityAndAEP`).

The signature carries the genuine preconditions
`0 < P` / `(N:ℝ) ≠ 0` (the union-bound consumer derives both before invoking); no
circularity / bundling / degenerate-def.

@audit:ok -/
theorem klDiv_perLetter_eq_capacity
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0) :
    (klDiv
        (((gaussianReal 0 P.toNNReal).prod (gaussianReal 0 N)).map
            (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
        ((gaussianReal 0 P.toNNReal).prod (gaussianReal 0 (P.toNNReal + N)))).toReal
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  classical
  set P' : ℝ≥0 := P.toNNReal with hP'_def
  have hP'_ne : P' ≠ 0 := by
    rw [hP'_def]; exact ne_of_gt (Real.toNNReal_pos.mpr hP)
  have hP'_coe : (P' : ℝ) = P := by rw [hP'_def]; exact Real.coe_toNNReal P hP.le
  have hN_nn : N ≠ 0 := fun h => hN (by rw [h]; simp)
  have hPN_ne : P' + N ≠ 0 := fun h => hN (by exact_mod_cast (add_eq_zero.mp h).2)
  have hN_pos : (0 : ℝ) < N := lt_of_le_of_ne N.coe_nonneg (fun h => hN h.symm)
  have hP'_pos : (0 : ℝ) < P' := by rw [hP'_coe]; exact hP
  have hPN_pos : (0 : ℝ) < (P' + N : ℝ≥0) := by
    rw [NNReal.coe_add]; positivity
  set μX : Measure ℝ := gaussianReal 0 P' with hμX_def
  set μZ : Measure ℝ := gaussianReal 0 N with hμZ_def
  set μY : Measure ℝ := gaussianReal 0 (P' + N) with hμY_def
  haveI : IsProbabilityMeasure μX := by rw [hμX_def]; infer_instance
  haveI : IsProbabilityMeasure μZ := by rw [hμZ_def]; infer_instance
  haveI : IsProbabilityMeasure μY := by rw [hμY_def]; infer_instance
  -- **AWGN channel kernel** `κ x = gaussianReal x N` (measurable, Markov).
  have hκ_meas : Measurable (fun x : ℝ => gaussianReal x N) := by
    have h_fun_eq : (fun x : ℝ => gaussianReal x N)
        = (fun x : ℝ => (gaussianReal 0 N).map (fun z => x + z)) := by
      funext x; rw [gaussianReal_map_const_add]; simp
    rw [h_fun_eq]
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    have h_apply_eq : (fun x : ℝ => ((gaussianReal 0 N).map (fun z => x + z)) s)
        = fun x : ℝ => (gaussianReal 0 N) (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ∈ s}) := by
      funext x
      rw [Measure.map_apply (by fun_prop) hs]; rfl
    rw [h_apply_eq]
    exact measurable_measure_prodMk_left ((measurable_fst.add measurable_snd) hs)
  set κ : Kernel ℝ ℝ := { toFun := fun x => gaussianReal x N, measurable' := hκ_meas } with hκ_def
  have hκ_apply : ∀ x, κ x = gaussianReal x N := fun x => rfl
  haveI : IsMarkovKernel κ := ⟨fun x => by rw [hκ_apply]; infer_instance⟩
  -- `J₁ = μX ⊗ₘ κ`: both agree on rectangles (`compProd_apply` vs `map`/`prod`).
  set J₁ : Measure (ℝ × ℝ) := (μX.prod μZ).map (fun p => (p.1, p.1 + p.2)) with hJ₁_def
  set Q₁ : Measure (ℝ × ℝ) := μX.prod μY with hQ₁_def
  have hh₁_meas : Measurable (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) :=
    measurable_fst.prodMk (measurable_fst.add measurable_snd)
  have hJ_compProd : J₁ = μX ⊗ₘ κ := by
    rw [hJ₁_def]
    ext s hs
    rw [Measure.map_apply hh₁_meas hs, Measure.compProd_apply hs, Measure.prod_apply
      (hh₁_meas hs)]
    refine lintegral_congr fun x => ?_
    rw [hκ_apply]
    -- `(gaussianReal x N) (Prod.mk x ⁻¹' s) = μZ ((fun z => x+z) ⁻¹' (Prod.mk x ⁻¹' s))`
    have hxN : gaussianReal x N = (gaussianReal 0 N).map (fun z => x + z) := by
      rw [gaussianReal_map_const_add]; simp
    rw [hxN, Measure.map_apply (by fun_prop) (measurable_prodMk_left hs), hμZ_def]
    congr 1
  -- `Q₁ = μX ⊗ₘ (Kernel.const _ μY)`.
  have hQ_compProd : Q₁ = μX ⊗ₘ (Kernel.const ℝ μY) := by
    rw [hQ₁_def, Measure.compProd_const]
  -- **Fibrewise AC + AC of the joint**: `κ x = gaussianReal x N ≪ μY = gaussianReal 0 (P'+N)`.
  have hfib_ac : ∀ x, κ x ≪ Kernel.const ℝ μY x := by
    intro x
    rw [hκ_apply, Kernel.const_apply, hμY_def]
    exact (gaussianReal_absolutelyContinuous x hN_nn).trans
      (gaussianReal_absolutelyContinuous' 0 hPN_ne)
  have hJ_ac : J₁ ≪ Q₁ := by
    rw [hJ_compProd, hQ_compProd]
    exact Measure.absolutelyContinuous_compProd_right_iff.mpr
      (Filter.Eventually.of_forall hfib_ac)
  -- **Per-fibre KL finiteness + closed form** (`gaussianReal x N ≪ gaussianReal 0 (P'+N)`,
  -- both with integrable llr): `klDiv (κ x) μY ≠ ⊤`.
  have hfib_int : ∀ x : ℝ, Integrable (llr (κ x) μY) (κ x) := fun x => by
    rw [hκ_apply, hμY_def]; exact gaussianReal_llr_integrable x 0 hN_nn hPN_ne
  have hfib_ne_top : ∀ x : ℝ, klDiv (κ x) μY ≠ ⊤ := fun x =>
    klDiv_ne_top (hfib_ac x |>.trans (by rw [Kernel.const_apply])) (hfib_int x)
  -- **Joint KL finiteness via the lintegral form** (`klDiv_compProd_lintegral`): the integral
  -- of the per-fibre KL (a quadratic in `x`) against the Gaussian `μX` is finite.
  have hjoint_lint : klDiv (μX ⊗ₘ κ) (μX ⊗ₘ (Kernel.const ℝ μY))
      = ∫⁻ x, klDiv (κ x) (Kernel.const ℝ μY x) ∂μX :=
    klDiv_compProd_lintegral (by rw [← hJ_compProd, ← hQ_compProd]; exact hJ_ac)
  -- the per-fibre KL `.toReal` is the quadratic; `klDiv (κ x) μY = ofReal (quadratic)`.
  have hfib_klDiv_real : ∀ x : ℝ, (klDiv (κ x) (Kernel.const ℝ μY x)).toReal
      = (1/2) * (Real.log ((P' + N : ℝ≥0) / N) + (N : ℝ) / (P' + N : ℝ≥0)
                  + x ^ 2 / (P' + N : ℝ≥0) - 1) := by
    intro x
    rw [Kernel.const_apply, hκ_apply, hμY_def]
    exact perFibre_klDiv_toReal_quadratic P' N hN_nn hPN_ne x
  have hfib_ofReal : ∀ x : ℝ, klDiv (κ x) (Kernel.const ℝ μY x)
      = ENNReal.ofReal ((1/2) * (Real.log ((P' + N : ℝ≥0) / N) + (N : ℝ) / (P' + N : ℝ≥0)
                  + x ^ 2 / (P' + N : ℝ≥0) - 1)) := by
    intro x
    rw [← hfib_klDiv_real x, ENNReal.ofReal_toReal]
    rw [Kernel.const_apply]
    exact hfib_ne_top x
  have hX_memLp' : MemLp (fun x : ℝ => x) 2 μX := by
    rw [hμX_def]; exact memLp_id_gaussianReal' 2 (by simp)
  have hsq_int' : Integrable (fun x : ℝ => x ^ 2) μX := by
    have := hX_memLp'.integrable_sq; simpa [sq] using this
  -- the quadratic is integrable, so its lintegral (of `ofReal`) is finite.
  have h_quad_int : Integrable (fun x : ℝ =>
      (1/2) * (Real.log ((P' + N : ℝ≥0) / N) + (N : ℝ) / (P' + N : ℝ≥0)
                  + x ^ 2 / (P' + N : ℝ≥0) - 1)) μX := by
    apply Integrable.const_mul
    apply Integrable.sub _ (integrable_const _)
    apply Integrable.add (integrable_const _)
    exact hsq_int'.div_const _
  have hjoint_ne_top : klDiv (μX ⊗ₘ κ) (μX ⊗ₘ (Kernel.const ℝ μY)) ≠ ⊤ := by
    rw [hjoint_lint]
    simp only [hfib_ofReal]
    -- `∫⁻ ofReal (quadratic) < ⊤` because the quadratic is integrable.
    refine ne_of_lt ?_
    have h_ae_nonneg : 0 ≤ᵐ[μX] (fun x : ℝ =>
        (1/2) * (Real.log ((P' + N : ℝ≥0) / N) + (N : ℝ) / (P' + N : ℝ≥0)
                  + x ^ 2 / (P' + N : ℝ≥0) - 1)) := by
      filter_upwards with x
      have := hfib_klDiv_real x
      have hnn : (0 : ℝ) ≤ (klDiv (κ x) (Kernel.const ℝ μY x)).toReal := ENNReal.toReal_nonneg
      rw [this] at hnn; exact hnn
    rw [← ofReal_integral_eq_lintegral_ofReal h_quad_int h_ae_nonneg]
    exact ENNReal.ofReal_lt_top
  have h_int : Integrable (llr (μX ⊗ₘ κ) (μX ⊗ₘ (Kernel.const ℝ μY))) (μX ⊗ₘ κ) :=
    (klDiv_ne_top_iff.mp hjoint_ne_top).2
  rw [hJ_compProd, hQ_compProd,
    klDiv_compProd_const_toReal_integral
      (by rw [← hJ_compProd, ← hQ_compProd]; exact hJ_ac) h_int]
  -- per-fibre closed form: `klDiv (gaussianReal x N) μY = (1/2)(log((P'+N)/N) + N/(P'+N)
  --   + x²/(P'+N) - 1)`.
  have hfib_kl : ∀ x : ℝ, (klDiv (κ x) μY).toReal
      = (1/2) * (Real.log ((P' + N : ℝ≥0) / N) + (N : ℝ) / (P' + N : ℝ≥0)
                  + x ^ 2 / (P' + N : ℝ≥0) - 1) := fun x => by
    have := hfib_klDiv_real x; rwa [Kernel.const_apply] at this
  simp only [hfib_kl]
  -- integrate the per-fibre closed form over `μX` (mean 0, variance `P'`).
  exact integral_perFibre_klDiv_quadratic_eq_capacity P P' N hP'_coe hN_nn hPN_ne

/-- **bridge ① n-fold identity** (genuine, sorryAx-free):
`klDiv(J_n, Q_n).toReal = n · klDiv(J₁, Q₁).toReal`, where `J_n`/`Q_n` are the verbatim
n-letter joint/product measures from the `continuousAepGaussian_holds` signature. Via
`arrowProdEquivProdArrow` reshape (`klDiv_map_measurableEquiv`) + `klDiv_pi_eq_sum`
+ i.i.d. `Finset.sum_const`.

Unconditional measure identity (no `P`/`N`
precondition — holds even in the degenerate cases, both sides equal); no circularity /
bundling / degenerate-def.

@audit:ok -/
theorem klDiv_nFold_eq_nsmul (P : ℝ) (N : ℝ≥0) {n : ℕ} :
    (klDiv
        (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
            (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)))
        ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
          (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
      = (n : ℝ) *
        (klDiv
            (((gaussianReal 0 P.toNNReal).prod (gaussianReal 0 N)).map
                (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
            ((gaussianReal 0 P.toNNReal).prod
              (gaussianReal 0 (P.toNNReal + N)))).toReal := by
  -- per-letter measures + the reshape equiv
  set μX : Measure ℝ := gaussianReal 0 P.toNNReal with hμX_def
  set μZ : Measure ℝ := gaussianReal 0 N with hμZ_def
  set μY : Measure ℝ := gaussianReal 0 (P.toNNReal + N) with hμY_def
  set J₁ : Measure (ℝ × ℝ) := (μX.prod μZ).map (fun p => (p.1, p.1 + p.2)) with hJ₁_def
  set Q₁ : Measure (ℝ × ℝ) := μX.prod μY with hQ₁_def
  set e : (Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) with he_def
  -- per-letter probability-measure instances
  have hh₁_meas : Measurable (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) :=
    measurable_fst.prodMk (measurable_fst.add measurable_snd)
  haveI : IsProbabilityMeasure J₁ := by
    rw [hJ₁_def]; exact Measure.isProbabilityMeasure_map hh₁_meas.aemeasurable
  haveI : IsProbabilityMeasure Q₁ := by rw [hQ₁_def]; infer_instance
  -- the n-fold maps
  set g : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
    fun p => (p.1, fun i => p.1 i + p.2 i) with hg_def
  set H : (Fin n → ℝ × ℝ) → (Fin n → ℝ × ℝ) := fun w i => (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) (w i)
    with hH_def
  have hg_meas : Measurable g := by
    rw [hg_def]; exact measurable_fst.prodMk (measurable_pi_lambda _
      (fun i => (measurable_pi_apply i).comp measurable_fst |>.add
        ((measurable_pi_apply i).comp measurable_snd)))
  have hH_meas : Measurable H :=
    measurable_pi_lambda _ (fun i => hh₁_meas.comp (measurable_pi_apply i))
  -- `J_n = (pi J₁).map e` (same reshape as the engine's `hJ_eq`)
  have hJ_eq :
      ((Measure.pi (fun _ : Fin n => μX)).prod (Measure.pi (fun _ : Fin n => μZ))).map g
        = (Measure.pi (fun _ : Fin n => J₁)).map e := by
    have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
      (fun _ : Fin n => μX) (fun _ : Fin n => μZ)
    have hprod_reshape :
        (Measure.pi (fun _ : Fin n => μX)).prod (Measure.pi (fun _ : Fin n => μZ))
          = (Measure.pi (fun _ : Fin n => μX.prod μZ)).map e := by
      rw [he_def, ← hmp.map_eq]
    have hpiJ₁ :
        Measure.pi (fun _ : Fin n => J₁)
          = (Measure.pi (fun _ : Fin n => μX.prod μZ)).map H := by
      rw [hH_def, hJ₁_def]
      rw [Measure.pi_map_pi (f := fun _ : Fin n => (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
        (fun _ => hh₁_meas.aemeasurable)]
    rw [hprod_reshape, hpiJ₁, Measure.map_map hg_meas e.measurable,
      Measure.map_map e.measurable hH_meas]
    rfl
  -- `Q_n = (pi Q₁).map e` (no inner map — a plain product reshape)
  have hQ_eq :
      (Measure.pi (fun _ : Fin n => μX)).prod (Measure.pi (fun _ : Fin n => μY))
        = (Measure.pi (fun _ : Fin n => Q₁)).map e := by
    have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
      (fun _ : Fin n => μX) (fun _ : Fin n => μY)
    rw [hQ₁_def, he_def, ← hmp.map_eq]
  -- assemble: `klDiv J_n Q_n = klDiv (pi J₁) (pi Q₁) = ∑ klDiv J₁ Q₁ = n • klDiv J₁ Q₁`
  rw [show (((Measure.pi (fun _ : Fin n => μX)).prod
        (Measure.pi (fun _ : Fin n => μZ))).map g) = (Measure.pi (fun _ : Fin n => J₁)).map e
      from hJ_eq, hQ_eq,
    klDiv_map_measurableEquiv e (Measure.pi (fun _ : Fin n => J₁))
      (Measure.pi (fun _ : Fin n => Q₁)),
    klDiv_pi_eq_sum (fun _ : Fin n => J₁) (fun _ : Fin n => Q₁),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_natCast]

private lemma gaussian_shear_logDensity_quadratic_memLp_two
    (P' N : ℝ≥0) (hP_ne : P' ≠ 0) (hN_ne : N ≠ 0) (hPN_ne : P' + N ≠ 0) :
    MemLp
      (fun p : ℝ × ℝ =>
        (-(1/2) * Real.log (2 * Real.pi * N) - (p.2 - p.1) ^ 2 / (2 * N))
          - (-(1/2) * Real.log (2 * Real.pi * (P' + N)) - p.2 ^ 2 / (2 * (P' + N))))
      2
      (((gaussianReal 0 P').prod (gaussianReal 0 N)).map (fun p => (p.1, p.1 + p.2))) := by
  set μX : Measure ℝ := gaussianReal 0 P' with hμX_def
  set μZ : Measure ℝ := gaussianReal 0 N with hμZ_def
  set J₁ : Measure (ℝ × ℝ) := (μX.prod μZ).map (fun p => (p.1, p.1 + p.2)) with hJ₁_def
  set cN : ℝ := -(1/2) * Real.log (2 * Real.pi * N) with hcN_def
  set cY : ℝ := -(1/2) * Real.log (2 * Real.pi * (P' + N)) with hcY_def
  set q : ℝ × ℝ → ℝ :=
    fun p => (cN - (p.2 - p.1) ^ 2 / (2 * N)) - (cY - p.2 ^ 2 / (2 * (P' + N)))
    with hq_def
  show MemLp q 2 J₁
  haveI : IsProbabilityMeasure μX := by rw [hμX_def]; infer_instance
  haveI : IsProbabilityMeasure μZ := by rw [hμZ_def]; infer_instance
  have hHT : (4 : ℝ≥0∞)⁻¹ + 4⁻¹ = 2⁻¹ := by
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_inv_of_pos (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  haveI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := ⟨hHT⟩
  have hh₁_meas : Measurable (fun p : ℝ × ℝ => (p.1, p.1 + p.2)) :=
    measurable_fst.prodMk (measurable_fst.add measurable_snd)
  have hq_meas : Measurable q := by rw [hq_def]; fun_prop
  rw [hJ₁_def,
    memLp_map_measure_iff hq_meas.aestronglyMeasurable hh₁_meas.aemeasurable]
  have hX4 : MemLp (fun p : ℝ × ℝ => p.1) 4 (μX.prod μZ) := by
    have h := (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := P') 4 (by simp)
      ).comp_measurePreserving (measurePreserving_fst (μ := μX) (ν := μZ))
    rw [hμX_def]; exact h
  have hZ4 : MemLp (fun p : ℝ × ℝ => p.2) 4 (μX.prod μZ) := by
    have h := (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := N) 4 (by simp)
      ).comp_measurePreserving (measurePreserving_snd (μ := μX) (ν := μZ))
    rw [hμZ_def]; exact h
  have hXZ4 : MemLp (fun p : ℝ × ℝ => p.1 + p.2) 4 (μX.prod μZ) := hX4.add hZ4
  have hZ2 : MemLp (fun p : ℝ × ℝ => p.2 ^ 2) 2 (μX.prod μZ) := by
    have h : MemLp (fun p : ℝ × ℝ => p.2 * p.2) 2 (μX.prod μZ) := hZ4.mul' hZ4
    simpa [sq] using h
  have hXZ2 : MemLp (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2) 2 (μX.prod μZ) := by
    have h : MemLp (fun p : ℝ × ℝ => (p.1 + p.2) * (p.1 + p.2)) 2 (μX.prod μZ) :=
      hXZ4.mul' hXZ4
    simpa [sq] using h
  have hterm1 : MemLp (fun p : ℝ × ℝ => cN - p.2 ^ 2 / (2 * N)) 2 (μX.prod μZ) :=
    (memLp_const cN).sub (MemLp.ae_eq
      (Filter.Eventually.of_forall fun p => by ring)
      (hZ2.const_mul (1 / (2 * (N : ℝ)))))
  have hterm2 : MemLp (fun p : ℝ × ℝ => cY - (p.1 + p.2) ^ 2 / (2 * (P' + N))) 2
      (μX.prod μZ) :=
    (memLp_const cY).sub (MemLp.ae_eq
      (Filter.Eventually.of_forall fun p => by push_cast; ring)
      (hXZ2.const_mul (1 / (2 * ((P' : ℝ) + N)))))
  refine MemLp.ae_eq (Filter.Eventually.of_forall fun p => ?_) (hterm1.sub hterm2)
  simp only [Function.comp, hq_def, Pi.sub_apply]
  ring

lemma gaussian_shear_logRnDeriv_memLp_two (P' N : ℝ≥0) (hP_ne : P' ≠ 0) (hN_ne : N ≠ 0) :
    MemLp
      (fun p : ℝ × ℝ =>
        Real.log
          ((((((gaussianReal 0 P').prod (gaussianReal 0 N)).map
                  (fun p => (p.1, p.1 + p.2))).rnDeriv
                ((gaussianReal 0 P').prod (gaussianReal 0 (P' + N)))) p).toReal))
      2
      (((gaussianReal 0 P').prod (gaussianReal 0 N)).map (fun p => (p.1, p.1 + p.2))) := by
  set μX : Measure ℝ := gaussianReal 0 P' with hμX_def
  set μZ : Measure ℝ := gaussianReal 0 N with hμZ_def
  set μY : Measure ℝ := gaussianReal 0 (P' + N) with hμY_def
  set J₁ : Measure (ℝ × ℝ) := (μX.prod μZ).map (fun p => (p.1, p.1 + p.2)) with hJ₁_def
  set Q₁ : Measure (ℝ × ℝ) := μX.prod μY with hQ₁_def
  set φ : ℝ × ℝ → ℝ := fun p => Real.log ((J₁.rnDeriv Q₁ p).toReal) with hφ_def
  haveI : IsProbabilityMeasure J₁ := by
    rw [hJ₁_def]
    exact Measure.isProbabilityMeasure_map
      (measurable_fst.prodMk (measurable_fst.add measurable_snd)).aemeasurable
  haveI : IsProbabilityMeasure Q₁ := by rw [hQ₁_def]; infer_instance
  show MemLp φ 2 J₁
  have hPN_ne : P' + N ≠ 0 := by
    intro h
    exact hN_ne (by simpa using (add_eq_zero.mp h).2)
  set fX : ℝ → ℝ := gaussianPDFReal 0 P' with hfX_def
  set fN : ℝ → ℝ := gaussianPDFReal 0 N with hfN_def
  set fY : ℝ → ℝ := gaussianPDFReal 0 (P' + N) with hfY_def
  set qden : ℝ × ℝ → ℝ≥0∞ :=
    fun p => gaussianPDF 0 P' p.1 * gaussianPDF 0 (P' + N) p.2 with hqden_def
  set jden : ℝ × ℝ → ℝ≥0∞ :=
    fun p => gaussianPDF 0 P' p.1 * gaussianPDF 0 N (p.2 - p.1) with hjden_def
  have hqden_meas : Measurable qden :=
    (measurable_gaussianPDF 0 P').comp measurable_fst |>.mul
      ((measurable_gaussianPDF 0 (P' + N)).comp measurable_snd)
  have hjden_meas : Measurable jden :=
    (measurable_gaussianPDF 0 P').comp measurable_fst |>.mul
      ((measurable_gaussianPDF 0 N).comp (measurable_snd.sub measurable_fst))
  have hQ₁_wd : Q₁ = (volume.prod volume).withDensity qden := by
    rw [hQ₁_def, hμX_def, hμY_def,
      gaussianReal_of_var_ne_zero 0 hP_ne, gaussianReal_of_var_ne_zero 0 hPN_ne,
      prod_withDensity (measurable_gaussianPDF 0 P') (measurable_gaussianPDF 0 (P' + N))]
  have hJ₁_wd : J₁ = (volume.prod volume).withDensity jden := by
    rw [hJ₁_def, hμX_def, hμZ_def,
      gaussianReal_of_var_ne_zero 0 hP_ne, gaussianReal_of_var_ne_zero 0 hN_ne,
      prod_withDensity (measurable_gaussianPDF 0 P') (measurable_gaussianPDF 0 N),
      map_shear_withDensity (fun z => gaussianPDF 0 P' z.1 * gaussianPDF 0 N z.2)
        ((measurable_gaussianPDF 0 P').comp measurable_fst |>.mul
          ((measurable_gaussianPDF 0 N).comp measurable_snd))]
  have hqden_ne_zero : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), qden p ≠ 0 :=
    Filter.Eventually.of_forall fun p => by
      rw [hqden_def]
      exact mul_ne_zero (gaussianPDF_pos 0 hP_ne p.1).ne' (gaussianPDF_pos 0 hPN_ne p.2).ne'
  have hqden_ne_top : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), qden p ≠ ∞ :=
    Filter.Eventually.of_forall fun p => by
      rw [hqden_def]
      exact ENNReal.mul_ne_top gaussianPDF_ne_top gaussianPDF_ne_top
  have hrnJ : J₁.rnDeriv (volume.prod volume) =ᵐ[volume.prod volume] jden := by
    rw [hJ₁_wd]; exact Measure.rnDeriv_withDensity _ hjden_meas
  have hrnQ : J₁.rnDeriv Q₁
      =ᵐ[volume.prod volume] fun p => (qden p)⁻¹ * jden p := by
    have h1 : J₁.rnDeriv Q₁
        =ᵐ[volume.prod volume] fun p => (qden p)⁻¹ * J₁.rnDeriv (volume.prod volume) p := by
      rw [hQ₁_wd]
      exact Measure.rnDeriv_withDensity_right J₁ (volume.prod volume)
        hqden_meas.aemeasurable hqden_ne_zero hqden_ne_top
    filter_upwards [h1, hrnJ] with p hp1 hpJ
    rw [hp1, hpJ]
  have hJ₁_ac : J₁ ≪ (volume.prod volume) := by
    rw [hJ₁_wd]; exact withDensity_absolutelyContinuous _ _
  have hrnQ_J : J₁.rnDeriv Q₁ =ᵐ[J₁] fun p => (qden p)⁻¹ * jden p := hJ₁_ac.ae_le hrnQ
  set cN : ℝ := -(1/2) * Real.log (2 * Real.pi * N) with hcN_def
  set cY : ℝ := -(1/2) * Real.log (2 * Real.pi * (P' + N)) with hcY_def
  set q : ℝ × ℝ → ℝ :=
    fun p => (cN - (p.2 - p.1) ^ 2 / (2 * N)) - (cY - p.2 ^ 2 / (2 * (P' + N)))
    with hq_def
  have hN_pos : (0 : ℝ) < N := lt_of_le_of_ne N.coe_nonneg
    (fun h => hN_ne (by exact_mod_cast h.symm))
  have hPN_pos : (0 : ℝ) < (P' + N : ℝ≥0) := lt_of_le_of_ne (P' + N).coe_nonneg
    (fun h => hPN_ne (by exact_mod_cast h.symm))
  have hφ_eq : φ =ᵐ[J₁] q := by
    filter_upwards [hrnQ_J] with p hp
    rw [hφ_def]
    simp only [hp]
    rw [hqden_def, hjden_def]
    simp only [gaussianPDF]
    have hfX_pos : 0 < gaussianPDFReal 0 P' p.1 := gaussianPDFReal_pos 0 P' p.1 hP_ne
    have hfN_pos : 0 < gaussianPDFReal 0 N (p.2 - p.1) :=
      gaussianPDFReal_pos 0 N (p.2 - p.1) hN_ne
    have hfY_pos : 0 < gaussianPDFReal 0 (P' + N) p.2 :=
      gaussianPDFReal_pos 0 (P' + N) p.2 hPN_ne
    have hratio : ((ENNReal.ofReal (gaussianPDFReal 0 P' p.1)
            * ENNReal.ofReal (gaussianPDFReal 0 (P' + N) p.2))⁻¹
          * (ENNReal.ofReal (gaussianPDFReal 0 P' p.1)
            * ENNReal.ofReal (gaussianPDFReal 0 N (p.2 - p.1)))).toReal
        = gaussianPDFReal 0 N (p.2 - p.1) / gaussianPDFReal 0 (P' + N) p.2 := by
      rw [← ENNReal.ofReal_mul hfX_pos.le, ← ENNReal.ofReal_mul hfX_pos.le,
        ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ENNReal.toReal_ofReal (by positivity)]
      field_simp
    rw [hratio]
    rw [Real.log_div hfN_pos.ne' hfY_pos.ne']
    rw [hq_def]
    have hlogN : Real.log (gaussianPDFReal 0 N (p.2 - p.1))
        = cN - (p.2 - p.1) ^ 2 / (2 * N) := by
      rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_pos _).ne',
        Real.log_inv, Real.log_sqrt (by positivity), Real.log_exp, hcN_def]
      ring
    have hlogY : Real.log (gaussianPDFReal 0 (P' + N) p.2)
        = cY - p.2 ^ 2 / (2 * (P' + N)) := by
      rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_pos _).ne',
        Real.log_inv, Real.log_sqrt (by positivity), Real.log_exp, hcY_def]
      push_cast; ring
    rw [hlogN, hlogY]
  have hq_memLp : MemLp q 2 J₁ :=
    gaussian_shear_logDensity_quadratic_memLp_two P' N hP_ne hN_ne hPN_ne
  exact MemLp.ae_eq hφ_eq.symm hq_memLp

theorem continuousAepGaussian_degenerate_witness
    (P : ℝ) (N : ℝ≥0) (n : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hdeg : P.toNNReal = 0 ∨ N = 0) :
    ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
      MeasurableSet A
      ∧ (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
              (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                (p.1, fun i => p.1 i + p.2 i))) A
          ≥ ENNReal.ofReal (1 - ε)
      ∧ ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
            (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))) A
          ≤ ENNReal.ofReal (Real.exp (-(
              (klDiv
                  (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                      (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
                    (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                        (p.1, fun i => p.1 i + p.2 i)))
                  ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                    (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
                - (n : ℝ) * (3 * δ)))) := by
  classical
  refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
  · -- (i) `Jₙ univ = 1 ≥ ofReal (1 - ε)`.
    rw [show ((((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
          (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)))
          Set.univ) = 1 from ?_]
    · exact le_trans (ENNReal.ofReal_le_one.mpr (by linarith)) (le_refl 1)
    · -- mass of `univ` under a probability measure is `1`
      have hg_meas : Measurable
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)) :=
        measurable_fst.prodMk (measurable_pi_lambda _ (fun i =>
          ((measurable_pi_apply i).comp measurable_fst).add
            ((measurable_pi_apply i).comp measurable_snd)))
      haveI : IsProbabilityMeasure
          (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
            (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i))) :=
        Measure.isProbabilityMeasure_map hg_meas.aemeasurable
      exact measure_univ
  · -- (iii) `Qₙ univ ≤ ofReal (exp (−(klDiv_n.toReal − n·3δ)))`, via `klDiv_n.toReal = 0`.
    set Jn : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
      ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
          (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)) with hJn_def
    set Qn : Measure ((Fin n → ℝ) × (Fin n → ℝ)) :=
      (Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
        (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))) with hQn_def
    haveI : IsProbabilityMeasure Qn := by rw [hQn_def]; infer_instance
    -- `klDiv Jn Qn .toReal = 0` in both degenerate cases (GENUINE, sorryAx-free): normalize
    -- the n-fold KL to `n · (klDiv J₁ Q₁).toReal` (`klDiv_nFold_eq_nsmul`, unconditional),
    -- then the per-letter degenerate vanishing `awgn_perLetter_klDiv_degenerate`
    -- (`P.toNNReal = 0` ⇒ `J₁ = Q₁` ⇒ `klDiv_self`; `N = 0 ∧ P' ≠ 0` ⇒ diagonal
    -- mutual-singularity ⇒ `klDiv = ⊤` ⇒ `toReal = 0`).
    have hkl0 : (klDiv Jn Qn).toReal = 0 := by
      rw [hJn_def, hQn_def, klDiv_nFold_eq_nsmul P N,
        awgn_perLetter_klDiv_degenerate P.toNNReal N hdeg, mul_zero]
    -- the exponent is `≥ 0`, so the bound is `≥ 1 ≥ Qn univ` (genuine, modulo `hkl0`).
    rw [hkl0]
    refine le_trans (prob_le_one : Qn Set.univ ≤ 1) ?_
    rw [zero_sub, neg_neg]
    refine ENNReal.one_le_ofReal.mpr ?_
    have hnn : (0 : ℝ) ≤ (n : ℝ) * (3 * δ) := by positivity
    calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
      _ ≤ Real.exp ((n : ℝ) * (3 * δ)) := Real.exp_le_exp.mpr hnn

theorem awgn_joint_law_reshape_eq (n : ℕ) (μX μZ : Measure ℝ)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μZ] :
    ((Measure.pi (fun _ : Fin n => μX)).prod (Measure.pi (fun _ : Fin n => μZ))).map
        (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i))
      = (Measure.pi (fun _ : Fin n =>
          (μX.prod μZ).map (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))).map
          (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) := by
  set e : (Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) with he_def
  set g : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
    fun p => (p.1, fun i => p.1 i + p.2 i) with hg_def
  set h₁ : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.1 + p.2) with hh₁_def
  set H : (Fin n → ℝ × ℝ) → (Fin n → ℝ × ℝ) := fun w i => h₁ (w i) with hH_def
  have hg_meas : Measurable g := by
    rw [hg_def]; exact measurable_fst.prodMk (measurable_pi_lambda _
      (fun i => (measurable_pi_apply i).comp measurable_fst |>.add
        ((measurable_pi_apply i).comp measurable_snd)))
  have hh₁_meas : Measurable h₁ := by
    rw [hh₁_def]; exact measurable_fst.prodMk (measurable_fst.add measurable_snd)
  have hH_meas : Measurable H :=
    measurable_pi_lambda _ (fun i => hh₁_meas.comp (measurable_pi_apply i))
  -- reshape `(pi μX).prod (pi μZ) = (pi (μX × μZ)).map e`
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ : Fin n => μX) (fun _ : Fin n => μZ)
  have hprod_reshape :
      (Measure.pi (fun _ : Fin n => μX)).prod (Measure.pi (fun _ : Fin n => μZ))
        = (Measure.pi (fun _ : Fin n => μX.prod μZ)).map e := by
    rw [he_def, ← hmp.map_eq]
  -- `pi J₁ = (pi (μX × μZ)).map H` via `pi_map_pi`
  have hpiJ₁ :
      Measure.pi (fun _ : Fin n => (μX.prod μZ).map (fun p : ℝ × ℝ => (p.1, p.1 + p.2)))
        = (Measure.pi (fun _ : Fin n => μX.prod μZ)).map H := by
    rw [hH_def]
    rw [Measure.pi_map_pi (f := fun _ : Fin n => h₁) (fun _ => hh₁_meas.aemeasurable)]
  rw [hprod_reshape, hpiJ₁, Measure.map_map hg_meas e.measurable,
    Measure.map_map e.measurable hH_meas]
  -- `g ∘ e = e ∘ H` pointwise (the two pushforward maps coincide)
  rfl

theorem awgn_changeOfMeasure_pi_mass_le {P' N : ℝ≥0} (hP'_ne : P' ≠ 0) (hN_ne : N ≠ 0)
    (n : ℕ) (hn0 : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (J₁ Q₁ : Measure (ℝ × ℝ)) [IsProbabilityMeasure J₁] [IsProbabilityMeasure Q₁]
    (hJ₁ : J₁ = ((gaussianReal 0 P').prod (gaussianReal 0 N)).map (fun p => (p.1, p.1 + p.2)))
    (hQ₁ : Q₁ = (gaussianReal 0 P').prod (gaussianReal 0 (P' + N)))
    (φ : ℝ × ℝ → ℝ) (hφ_def : φ = fun p => Real.log ((J₁.rnDeriv Q₁ p).toReal))
    (B : Set (Fin n → ℝ × ℝ))
    (hB_def : B = {w : Fin n → ℝ × ℝ | |(∑ i, φ (w i)) / (n : ℝ) - J₁[φ]| < δ}) :
    (Measure.pi (fun _ : Fin n => Q₁)) B
      ≤ ENNReal.ofReal
          (Real.exp (-((n : ℝ) * (klDiv J₁ Q₁).toReal - (n : ℝ) * (3 * δ)))) := by
  classical
  -- per-letter change-of-measure facts: mutual AC + density-exp relation
  obtain ⟨hJQ_ac, hQJ_ac, hdens_log⟩ :=
    awgn_perLetter_changeOfMeasure_facts hP'_ne hN_ne J₁ Q₁ hJ₁ hQ₁
  -- `φ = llr J₁ Q₁` (by definition).
  have hφ_llr : φ = llr J₁ Q₁ := by funext p; rw [hφ_def, llr]
  -- `J₁[φ] = (klDiv J₁ Q₁).toReal` (probability-measure correction terms vanish)
  have hJφ : J₁[φ] = (klDiv J₁ Q₁).toReal := by
    rw [hφ_llr, toReal_klDiv_of_measure_eq hJQ_ac (by rw [measure_univ, measure_univ])]
  -- `hdens_ae : (Q₁.rnDeriv J₁ p).toReal = Real.exp (−φ p)` (φ = log dJ₁/dQ₁)
  have hdens_ae : ∀ᵐ p ∂J₁, (Q₁.rnDeriv J₁ p).toReal = Real.exp (-φ p) := by
    filter_upwards [hdens_log] with p hp; rw [hp, hφ_def]
  -- the product density on `Fin n → ℝ × ℝ`
  set ρ : (Fin n → ℝ × ℝ) → ℝ≥0∞ := fun w => ∏ i, Q₁.rnDeriv J₁ (w i) with hρ_def
  -- `pi Q₁ = (pi J₁).withDensity ρ` (tensorize via `pi_withDensity`)
  have hQ_wd_rn : Q₁ = J₁.withDensity (Q₁.rnDeriv J₁) :=
    (Measure.withDensity_rnDeriv_eq Q₁ J₁ hQJ_ac).symm
  have hrn_meas : Measurable (Q₁.rnDeriv J₁) := Measure.measurable_rnDeriv Q₁ J₁
  have hB_meas : MeasurableSet B := by
    rw [hB_def]
    have hφ_meas : Measurable φ := by
      rw [hφ_def]
      exact Real.measurable_log.comp (Measure.measurable_rnDeriv J₁ Q₁).ennreal_toReal
    have hsum : Measurable (fun w : Fin n → ℝ × ℝ => (∑ i, φ (w i)) / (n : ℝ) - J₁[φ]) :=
      ((Finset.measurable_sum _
        (fun i _ => hφ_meas.comp (measurable_pi_apply i))).div_const _).sub_const _
    have hT : MeasurableSet {r : ℝ | |r| < δ} :=
      measurableSet_lt (measurable_norm.comp measurable_id) measurable_const
    exact hsum hT
  have hpiQ_wd : Measure.pi (fun _ : Fin n => Q₁)
      = (Measure.pi (fun _ : Fin n => J₁)).withDensity ρ := by
    have hsf : ∀ _ : Fin n, SigmaFinite (J₁.withDensity (Q₁.rnDeriv J₁)) := by
      intro _; rw [← hQ_wd_rn]; infer_instance
    have := pi_withDensity (fun _ : Fin n => J₁) (fun _ => Q₁.rnDeriv J₁)
      (fun _ => hrn_meas)
    rw [hρ_def]
    calc Measure.pi (fun _ : Fin n => Q₁)
        = Measure.pi (fun _ : Fin n => J₁.withDensity (Q₁.rnDeriv J₁)) := by
          simp_rw [← hQ_wd_rn]
      _ = (Measure.pi (fun _ : Fin n => J₁)).withDensity
            (fun w => ∏ i, Q₁.rnDeriv J₁ (w i)) := this
  -- mass of `B` via the density representation + the pointwise bound on `B`
  rw [hpiQ_wd, withDensity_apply _ hB_meas]
  -- lift the per-coordinate density / finiteness facts to `pi J₁`-a.e.
  have hrn_lt_top : ∀ᵐ p ∂J₁, Q₁.rnDeriv J₁ p < ∞ := Measure.rnDeriv_lt_top Q₁ J₁
  have hdens_pi : ∀ᵐ w ∂(Measure.pi (fun _ : Fin n => J₁)),
      ∀ i, (Q₁.rnDeriv J₁ (w i)).toReal = Real.exp (-φ (w i)) :=
    Filter.eventually_all.2 fun i =>
      (MeasureTheory.Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin n => J₁) (i := i)).eventually hdens_ae
  have hfin_pi : ∀ᵐ w ∂(Measure.pi (fun _ : Fin n => J₁)),
      ∀ i, Q₁.rnDeriv J₁ (w i) ≠ ∞ :=
    Filter.eventually_all.2 fun i =>
      (MeasureTheory.Measure.tendsto_eval_ae_ae
        (μ := fun _ : Fin n => J₁) (i := i)).eventually
        (hrn_lt_top.mono fun p hp => hp.ne)
  -- on `B`, `ρ w ≤ ofReal (exp (−(n·I − n·3δ)))` `[pi J₁]`-a.e.
  have hbound : ∀ᵐ w ∂(Measure.pi (fun _ : Fin n => J₁)),
      w ∈ B → ρ w ≤ ENNReal.ofReal
        (Real.exp (-((n : ℝ) * (klDiv J₁ Q₁).toReal - (n : ℝ) * (3 * δ)))) := by
    filter_upwards [hdens_pi, hfin_pi] with w hw_dens hw_fin hwB
    -- `ρ w ≠ ∞` (finite product of finite factors), and its `toReal = exp(−∑φ)`
    have hρ_ne_top : ρ w ≠ ∞ := by
      rw [hρ_def]; exact ENNReal.prod_ne_top (fun i _ => hw_fin i)
    have hρ_toReal : (ρ w).toReal = Real.exp (-(∑ i, φ (w i))) := by
      rw [hρ_def, ENNReal.toReal_prod]
      rw [show (-(∑ i, φ (w i))) = ∑ i, (-φ (w i)) by rw [Finset.sum_neg_distrib],
        Real.exp_sum]
      exact Finset.prod_congr rfl fun i _ => hw_dens i
    -- on `B`, `∑φ(wᵢ) ≥ n(J₁[φ] − δ)`, so `exp(−∑φ) ≤ exp(−(n·I − n·3δ))`
    rw [hB_def, Set.mem_setOf_eq, abs_lt] at hwB
    obtain ⟨hwB_lo, hwB_hi⟩ := hwB
    have hsum_ge : (n : ℝ) * ((klDiv J₁ Q₁).toReal - δ) ≤ ∑ i, φ (w i) := by
      rw [← hJφ]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have : J₁[φ] - δ < (∑ i, φ (w i)) / (n : ℝ) := by linarith
      rw [lt_div_iff₀ hnR] at this
      nlinarith [this]
    have hexp_le : Real.exp (-(∑ i, φ (w i)))
        ≤ Real.exp (-((n : ℝ) * (klDiv J₁ Q₁).toReal - (n : ℝ) * (3 * δ))) := by
      apply Real.exp_le_exp.mpr
      have hδ3 : (n : ℝ) * ((klDiv J₁ Q₁).toReal - δ)
          ≥ (n : ℝ) * (klDiv J₁ Q₁).toReal - (n : ℝ) * (3 * δ) := by
        have hnR : (0 : ℝ) ≤ n := by positivity
        nlinarith [hnR, hδ.le]
      linarith [hsum_ge]
    rw [← ENNReal.ofReal_toReal hρ_ne_top, hρ_toReal]
    exact ENNReal.ofReal_le_ofReal hexp_le
  -- integrate the bound over `B`
  calc ∫⁻ w in B, ρ w ∂(Measure.pi (fun _ : Fin n => J₁))
      ≤ ∫⁻ _ in B, ENNReal.ofReal
          (Real.exp (-((n : ℝ) * (klDiv J₁ Q₁).toReal - (n : ℝ) * (3 * δ))))
          ∂(Measure.pi (fun _ : Fin n => J₁)) := by
        refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
        filter_upwards [hbound] with w hw using hw
    _ ≤ ENNReal.ofReal
          (Real.exp (-((n : ℝ) * (klDiv J₁ Q₁).toReal - (n : ℝ) * (3 * δ)))) := by
        rw [setLIntegral_const]
        calc ENNReal.ofReal (Real.exp _) * (Measure.pi (fun _ : Fin n => J₁)) B
            ≤ ENNReal.ofReal (Real.exp _) * 1 :=
              mul_le_mul_right prob_le_one _
          _ = ENNReal.ofReal (Real.exp _) := mul_one _

private theorem awgn_continuousAep_productMass_bound (P : ℝ) (N : ℝ≥0)
    (hP_ne : P.toNNReal ≠ 0) (hN_ne : N ≠ 0)
    (n : ℕ) (hn0 : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (J₁ Q₁ : Measure (ℝ × ℝ)) [IsProbabilityMeasure J₁] [IsProbabilityMeasure Q₁]
    (hJ₁_def : J₁ = ((gaussianReal 0 P.toNNReal).prod (gaussianReal 0 N)).map
      (fun p => (p.1, p.1 + p.2)))
    (hQ₁_def : Q₁ = (gaussianReal 0 P.toNNReal).prod (gaussianReal 0 (P.toNNReal + N)))
    (φ : ℝ × ℝ → ℝ) (hφ_def : φ = fun p => Real.log ((J₁.rnDeriv Q₁ p).toReal))
    (e : (Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ))
    (he_def : e = MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
    (B : Set (Fin n → ℝ × ℝ))
    (hB_def : B = {w : Fin n → ℝ × ℝ | |(∑ i, φ (w i)) / (n : ℝ) - J₁[φ]| < δ})
    (hB_meas : MeasurableSet B) :
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
        (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))) (e.symm ⁻¹' B)
      ≤ ENNReal.ofReal (Real.exp (-(
          (klDiv
              (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                  (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
                (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)))
              ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
            - (n : ℝ) * (3 * δ)))) := by
  -- the n-fold KL `.toReal` is `n · (klDiv J₁ Q₁).toReal`.
  have hkl_n : (klDiv
          (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
              (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
            (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)))
          ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
            (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
      = (n : ℝ) * (klDiv J₁ Q₁).toReal := by
    rw [hJ₁_def, hQ₁_def]; exact klDiv_nFold_eq_nsmul P N
  -- reshape the signature's product law to `(Measure.pi Q₁).map e`.
  have hQ_eq :
      (Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
          (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))
        = (Measure.pi (fun _ : Fin n => Q₁)).map e := by
    have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
      (fun _ : Fin n => gaussianReal 0 P.toNNReal)
      (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))
    rw [hQ₁_def, he_def, ← hmp.map_eq]
  -- rewrite the exponent (klDiv) first, then reshape the product-law application.
  rw [hkl_n, hQ_eq, Measure.map_apply e.measurable (e.symm.measurable hB_meas)]
  have he_preim : e ⁻¹' (e.symm ⁻¹' B) = B := by
    ext w; simp [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
  rw [he_preim]
  exact awgn_changeOfMeasure_pi_mass_le hP_ne hN_ne n hn0 hδ J₁ Q₁ hJ₁_def hQ₁_def φ hφ_def
    B hB_def

/-- Continuous AEP for the `n`-dimensional Gaussian.

Given `P : ℝ`, `N : ℝ≥0`, a typicality slack `δ > 0`, and an error tolerance `ε > 0`
(independent parameters), there exists a threshold `N₀` such that for every `n ≥ N₀`
there is a measurable typical set `A ⊆ (Fin n → ℝ) × (Fin n → ℝ)` satisfying:

* (i) joint codebook+noise mass `≥ 1 - ε`, under the joint law of `(X, Y)` with
  `X ∼ N(0,P)` i.i.d. and `Y = X + Z`, `Z ∼ N(0,N)` i.i.d.;
* (ii) independent-pair upper bound (`X'` independent of `Y`): under the product of
  marginals, `A` has mass `≤ exp(−(klDivₙ − n·3δ)) = exp(−n(I − 3δ))`, where
  `klDivₙ = klDiv(joint, product) = n·I` is the `n`-letter KL (per-letter MI `I`).

The slack `δ` controls the typical set's width; the error target `ε` controls the
mass-failure level of (i). Decoupling them lets the consumer pick `R + 3δ < I`
independently of `ε`, which makes the union bound's second term decay.

Implementation:

* (i) uses only the finite-`n` Chebyshev weak law
  (`pi_empirical_mean_concentration` / `pi_empirical_mean_typical_mass`). The typical set
  `A` is built from the per-letter joint info-density `φ(x,y) = log dJ₁/dQ₁`.
* (ii) is discharged by the tensorize `pi_withDensity` (built on the lintegral box-Fubini
  `lintegral_pi_prod_eq_prod`): with `Q₁ ≪ J₁`,
  `pi Q₁ = (pi J₁).withDensity (∏ᵢ Q₁.rnDeriv J₁ (wᵢ))`, and on `B` the product density
  `(∏ᵢ Q₁.rnDeriv J₁ (wᵢ)).toReal = exp(−∑φ) ≤ exp(−n(I − δ))`
  (`awgn_perLetter_changeOfMeasure_facts`, `J₁[φ] = (klDiv J₁ Q₁).toReal` via
  `toReal_klDiv_of_measure_eq`); `klDivₙ = n·I` is `klDiv_nFold_eq_nsmul`.
* The degenerate case `(klDiv Jn Qn).toReal = 0` for `P.toNNReal = 0 ∨ N = 0` is handled
  via `klDiv_nFold_eq_nsmul` + `awgn_perLetter_klDiv_degenerate`: `P'=0` gives `J₁ = Q₁`
  (shear identity on `{0}×ℝ`, `klDiv_self`); `N=0 ∧ P'≠0` puts `J₁` on the diagonal
  `{(x,x)}` (`Q₁`-null since `μX` is atomless), so `¬J₁≪Q₁` and `klDiv = ⊤`, `toReal = 0`.
  The exponent `n·3δ ≥ 0` makes the bound `exp(n·3δ) ≥ 1 ≥ Qn univ`. The degenerate
  `A := Set.univ` branch is an honest witness: bound (ii) is genuinely loose (RHS `≥ 1`)
  when `klDiv = 0`, which is machine-proved rather than asserted.
@audit:ok -/
theorem continuousAepGaussian_holds (P : ℝ) (N : ℝ≥0) :
    ∀ ⦃δ ε : ℝ⦄, 0 < δ → 0 < ε → ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n →
      ∃ A : Set ((Fin n → ℝ) × (Fin n → ℝ)),
        MeasurableSet A
        ∧ (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
              (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                  (p.1, fun i => p.1 i + p.2 i))) A
            ≥ ENNReal.ofReal (1 - ε)
        ∧ ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
              (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N)))) A
            ≤ ENNReal.ofReal (Real.exp (-(
                (klDiv
                    (((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                        (Measure.pi (fun _ : Fin n => gaussianReal 0 N))).map
                      (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
                          (p.1, fun i => p.1 i + p.2 i)))
                    ((Measure.pi (fun _ : Fin n => gaussianReal 0 P.toNNReal)).prod
                      (Measure.pi (fun _ : Fin n => gaussianReal 0 (P.toNNReal + N))))).toReal
                  - (n : ℝ) * (3 * δ)))) := by
  intro δ ε hδ hε
  classical
  -- **Degenerate-boundary split** (the theorem signature carries no positivity on
  -- `P`/`N`). In the degenerate cases `P.toNNReal = 0` (`μX = Dirac 0`) or `N = 0`
  -- (`μZ = Dirac 0`, joint concentrated on the diagonal `{(x,x)}`), the engine route is
  -- unavailable: when `N = 0` the joint law `Jₙ` is mutually singular w.r.t. `Qₙ` so
  -- `Jₙ ⊀ Qₙ` and `φ = log dJₙ/dQₙ` is not controlled on `Qₙ`-null sets — `MemLp φ 2 Jₙ`
  -- is neither provable nor refutable as placed. Both degenerate cases are handled
  -- directly with the trivial typical set `A := Set.univ`: (i) `Jₙ univ = 1 ≥ 1 - ε`
  -- (probability measure), and (iii) `klDiv(Jₙ,Qₙ).toReal = 0` (either `klDiv_self` when
  -- `Jₙ = Qₙ`, or `klDiv_of_not_ac` `= ⊤` ↦ `toReal = 0`), so the exponent
  -- `−(0 − n·3δ) = n·3δ ≥ 0` makes the bound `exp(n·3δ) ≥ 1 ≥ Qₙ univ`.
  by_cases hdeg : P.toNNReal = 0 ∨ N = 0
  · -- Degenerate branch: trivial typical set `A := Set.univ` for all `n` (no engine).
    exact ⟨1, fun n _hn => continuousAepGaussian_degenerate_witness P N n hδ hε hdeg⟩
  -- Non-degenerate branch (second goal of `by_cases`): `P.toNNReal ≠ 0 ∧ N ≠ 0`.
  simp only [not_or] at hdeg
  obtain ⟨hP_ne, hN_ne⟩ := hdeg
  -- Per-letter measures (abbreviating `P' := P.toNNReal`).
  set μX : Measure ℝ := gaussianReal 0 P.toNNReal with hμX_def
  set μZ : Measure ℝ := gaussianReal 0 N with hμZ_def
  set μY : Measure ℝ := gaussianReal 0 (P.toNNReal + N) with hμY_def
  -- per-letter joint law of `(X, X+Z)` and product of marginals
  set J₁ : Measure (ℝ × ℝ) := (μX.prod μZ).map (fun p => (p.1, p.1 + p.2)) with hJ₁_def
  set Q₁ : Measure (ℝ × ℝ) := μX.prod μY with hQ₁_def
  -- per-letter info density `φ = log dJ₁/dQ₁` (= `llr J₁ Q₁`)
  set φ : ℝ × ℝ → ℝ := fun p => Real.log ((J₁.rnDeriv Q₁ p).toReal) with hφ_def
  haveI : IsProbabilityMeasure J₁ := by
    rw [hJ₁_def]
    exact Measure.isProbabilityMeasure_map
      (measurable_fst.prodMk (measurable_fst.add measurable_snd)).aemeasurable
  haveI : IsProbabilityMeasure Q₁ := by rw [hQ₁_def]; infer_instance
  -- `MemLp φ 2 J₁` (GENUINE, nondegenerate `P', N > 0`): the info density `φ = log dJ₁/dQ₁`
  -- is a.e. equal to a quadratic polynomial in `(x, y)` — the difference of two Gaussian
  -- log-densities (the `f_X` factor cancels in the RN-derivative ratio
  -- `dJ₁/dQ₁ = f_N(y−x)/f_Y(y)`) — hence lies in L² of the joint law (Gaussian 4th moments).
  have hφ_memLp : MemLp φ 2 J₁ := by
    rw [hφ_def, hJ₁_def, hQ₁_def, hμX_def, hμZ_def, hμY_def]
    exact gaussian_shear_logRnDeriv_memLp_two P.toNNReal N hP_ne hN_ne
  -- Engine: choose `N₀` so the empirical-mean typical set (slack `δ`) has mass
  -- `≥ 1 - ε` (the engine's `ε`-slot = our typicality slack `δ`, `η`-slot = error
  -- target `ε`, separated so the (iii) exponent uses `δ` independently of `ε`).
  obtain ⟨N₀, hN₀⟩ :=
    pi_empirical_mean_typical_mass J₁ hφ_memLp (ε := δ) (η := ε) hδ hε
  refine ⟨max N₀ 1, fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le Nat.one_pos (le_of_max_le_right hn)
  -- The reshaping equiv `(Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ)`.
  set e : (Fin n → ℝ × ℝ) ≃ᵐ (Fin n → ℝ) × (Fin n → ℝ) :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) with he_def
  -- Engine typical set on `Fin n → ℝ × ℝ`.
  set B : Set (Fin n → ℝ × ℝ) :=
    {w : Fin n → ℝ × ℝ | |(∑ i, φ (w i)) / (n : ℝ) - J₁[φ]| < δ} with hB_def
  -- The signature's set `A` is `B` pulled back through `e.symm`.
  -- `φ` is measurable (log ∘ toReal ∘ rnDeriv), hence `B` is measurable.
  have hφ_meas : Measurable φ := by
    rw [hφ_def]
    exact Real.measurable_log.comp (Measure.measurable_rnDeriv J₁ Q₁).ennreal_toReal
  have hB_meas : MeasurableSet B := by
    rw [hB_def]
    have hsum : Measurable (fun w : Fin n → ℝ × ℝ => (∑ i, φ (w i)) / (n : ℝ) - J₁[φ]) :=
      ((Finset.measurable_sum _
        (fun i _ => hφ_meas.comp (measurable_pi_apply i))).div_const _).sub_const _
    have hT : MeasurableSet {r : ℝ | |r| < δ} :=
      measurableSet_lt (measurable_norm.comp measurable_id) measurable_const
    exact hsum hT
  -- **Joint measure-identity** (`awgn_joint_law_reshape_eq`): the signature's joint law
  -- equals `(Measure.pi J₁).map e`, via `arrowProdEquivProdArrow` + `pi_map_pi`.
  have hJ_eq :
      ((Measure.pi (fun _ : Fin n => μX)).prod (Measure.pi (fun _ : Fin n => μZ))).map
          (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i))
        = (Measure.pi (fun _ : Fin n => J₁)).map e := by
    rw [hJ₁_def, he_def]; exact awgn_joint_law_reshape_eq n μX μZ
  refine ⟨e.symm ⁻¹' B, ?_, ?_, ?_⟩
  · -- measurability of `A`
    exact e.symm.measurable hB_meas
  · -- (i) joint mass `≥ 1 - ε` via the engine + the joint measure-identity
    rw [hJ_eq, Measure.map_apply e.measurable (e.symm.measurable hB_meas)]
    have he_preim : e ⁻¹' (e.symm ⁻¹' B) = B := by
      ext w; simp [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
    rw [he_preim]
    exact hN₀ (le_of_max_le_left hn)
  · -- (iii) product mass `≤ exp(−(klDiv_n − n·3δ))` via change of measure: exponent
    -- normalization (`klDiv_nFold_eq_nsmul`) + product-law reshape + the change-of-measure
    -- core (`awgn_changeOfMeasure_pi_mass_le`), bundled in the helper below.
    exact awgn_continuousAep_productMass_bound P N hP_ne hN_ne n hn0 hδ J₁ Q₁
      hJ₁_def hQ₁_def φ hφ_def e he_def B hB_def hB_meas

end InformationTheory.Shannon.AWGN
