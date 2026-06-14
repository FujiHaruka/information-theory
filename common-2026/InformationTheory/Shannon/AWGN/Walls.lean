import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Basic
import InformationTheory.Shannon.AWGN.AchievabilityAEP
import InformationTheory.Shannon.BlockwiseChannel
import InformationTheory.Shannon.ChannelCoding.MIDecomp
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.CondKLIntegral
import InformationTheory.Shannon.MultivariateDiffEntropy
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# AWGN shared analytic lemmas

The analytic core lemmas of the AWGN channel coding theorem, collected in one file so
they can be shared by the achievability and converse developments. They cover the
per-letter and `n`-fold KL identities, the continuous Gaussian AEP, the per-codeword
power constraint, and the converse-side Markov / chain-rule / integrability facts.

## Main statements

* `klDiv_perLetter_eq_capacity` — per-letter KL divergence equals `(1/2) log(1+P/N)`.
* `klDiv_nFold_eq_nsmul` — `klDiv(Jₙ,Qₙ).toReal = n · klDiv(J₁,Q₁).toReal`.
* `continuousAepGaussian_holds` — the continuous Gaussian AEP exponent bound.
* `awgnPowerConstraintPerCodeword_holds` — the per-codeword power constraint.

## Implementation notes

* `continuousAepGaussian_holds` is stated in the inline two-stage `Measure.pi` form
  rather than via `gaussianCodebook`, and connects to consumers through the defeq
  `gaussianCodebook ≡` two-stage `Measure.pi`. The slack `δ` is kept separate from the
  error target `ε`.
* `ChannelCoding.Code` / `errorEvent` are reachable transitively through the base file,
  so no explicit import of them is needed (this file never writes `Code.mk` directly).
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
below and `awgn_random_coding_union_bound` in `AchievabilityDischarge.lean`).

* `klDiv_perLetter_eq_capacity`: the per-letter joint `J₁`/product `Q₁` KL equals the
  AWGN capacity `(1/2) log(1 + P/N)`. Routed through the conditional-KL integral
  (`klDiv_compProd_const_toReal_integral`, `CondKLIntegral.lean`) + the 1-D Gaussian KL
  closed form (`klDiv_gaussianReal_gaussianReal_eq`, `DifferentialEntropy.lean`), **avoiding
  `mutualInfoOfChannel` / `MIClosedForm.lean`** which would create the import cycle
  `Walls → MIClosedForm → ContChannelMIDecomp → Walls`.
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

/-- **bridge ① per-letter closed form** (genuine, sorryAx-free): per-letter joint
`J₁ = law(X, X+Z)` and product of marginals `Q₁ = μX ⊗ μY` have KL equal to the AWGN
per-letter capacity `(1/2) log(1 + P/N)` (nondegenerate `P > 0`, `N ≠ 0`). Routed through the
conditional-KL integral (`klDiv_compProd_const_toReal_integral`) + the 1-D Gaussian KL closed
form (`klDiv_gaussianReal_gaussianReal_eq`), integrating the per-fibre quadratic against the
mean-0 variance-`P'` input — deliberately **avoiding `mutualInfoOfChannel` / `MIClosedForm`**
(import cycle `Walls → MIClosedForm → ContChannelMIDecomp → Walls`).

Independently audited 2026-06-12: sorryAx-free (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`); signature carries the genuine preconditions
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
  have hfib_int : ∀ x : ℝ, Integrable (llr (κ x) μY) (κ x) := by
    intro x
    rw [hκ_apply, hμY_def]
    exact gaussianReal_llr_integrable x 0 hN_nn hPN_ne
  have hfib_ne_top : ∀ x : ℝ, klDiv (κ x) μY ≠ ⊤ := by
    intro x
    exact klDiv_ne_top (hfib_ac x |>.trans (by rw [Kernel.const_apply])) (hfib_int x)
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
    rw [Kernel.const_apply, hκ_apply, hμY_def, klDiv_gaussianReal_gaussianReal_eq x 0 hN_nn hPN_ne]
    ring_nf
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
                  + x ^ 2 / (P' + N : ℝ≥0) - 1) := by
    intro x
    rw [hκ_apply, hμY_def, klDiv_gaussianReal_gaussianReal_eq x 0 hN_nn hPN_ne]
    ring_nf
  simp only [hfib_kl]
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
  have hPN_coe_pos : (0 : ℝ) < ((P' + N : ℝ≥0) : ℝ) := hPN_pos
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

/-- **bridge ① n-fold identity** (genuine, sorryAx-free):
`klDiv(J_n, Q_n).toReal = n · klDiv(J₁, Q₁).toReal`, where `J_n`/`Q_n` are the verbatim
n-letter joint/product measures from the `continuousAepGaussian_holds` signature. Via
`arrowProdEquivProdArrow` reshape (`klDiv_map_measurableEquiv`) + `klDiv_pi_eq_sum`
+ i.i.d. `Finset.sum_const`.

Independently audited 2026-06-12: sorryAx-free (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`); unconditional measure identity (no `P`/`N`
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
  have hq_memLp : MemLp q 2 J₁ := by
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
  · -- (iii) product mass `≤ exp(−(klDiv_n − n·3δ))` via change of measure.
    -- **Reduction wiring (sorryAx-free):** the n-letter KL exponent is normalized to
    -- `n·(klDiv J₁ Q₁).toReal` via the shared `klDiv_nFold_eq_nsmul`, and the signature's
    -- product law `Q_n (e.symm ⁻¹' B)` is reshaped to `(Measure.pi Q₁) B` exactly as the
    -- joint identity `hJ_eq` (Q side has no inner map). The remaining **change-of-measure
    -- core** (the n-fold RN-derivative tensorization `d(pi Q₁)/d(pi J₁) =ᵐ exp(−∑φ)`, then
    -- `(pi Q₁) B = ∫_B exp(−∑φ) d(pi J₁) ≤ exp(−n(J₁[φ]−δ))`) is the genuine Mathlib-absent
    -- atom (loogle `rnDeriv (pi _) (pi _)` → Found 0 in all forms; G-2 of
    -- `awgn-deep-atoms-bridge1-kldiv-inventory.md`), isolated below.
    -- the n-fold KL `.toReal` is `n · (klDiv J₁ Q₁).toReal`.
    have hkl_n : (klDiv
            (((Measure.pi (fun _ : Fin n => μX)).prod (Measure.pi (fun _ : Fin n => μZ))).map
              (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1, fun i => p.1 i + p.2 i)))
            ((Measure.pi (fun _ : Fin n => μX)).prod
              (Measure.pi (fun _ : Fin n => μY)))).toReal
        = (n : ℝ) * (klDiv J₁ Q₁).toReal := by
      rw [hμX_def, hμZ_def, hμY_def, hJ₁_def, hQ₁_def, hμX_def, hμY_def]
      exact klDiv_nFold_eq_nsmul P N
    -- reshape the signature's product law to `(Measure.pi Q₁).map e`.
    have hQ_eq :
        (Measure.pi (fun _ : Fin n => μX)).prod (Measure.pi (fun _ : Fin n => μY))
          = (Measure.pi (fun _ : Fin n => Q₁)).map e := by
      have hmp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
        (fun _ : Fin n => μX) (fun _ : Fin n => μY)
      rw [hQ₁_def, he_def, ← hmp.map_eq]
    -- rewrite the exponent (klDiv) first, then reshape the product-law application.
    rw [hkl_n, hQ_eq, Measure.map_apply e.measurable (e.symm.measurable hB_meas)]
    have he_preim : e ⁻¹' (e.symm ⁻¹' B) = B := by
      ext w; simp [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
    rw [he_preim]
    -- **Change-of-measure core** (`awgn_changeOfMeasure_pi_mass_le`, G-2 via `pi_withDensity`):
    -- `Q₁ ≪ J₁`, so `pi Q₁ = (pi J₁).withDensity (∏ᵢ Q₁.rnDeriv J₁ (wᵢ))`; on `B` the
    -- product density `= exp(−∑φ) ≤ exp(−n(J₁[φ]−δ))` with `J₁[φ] = (klDiv J₁ Q₁).toReal`,
    -- giving `(pi Q₁) B ≤ exp(−(n·I − n·3δ))` since `δ ≤ 3δ`.
    exact awgn_changeOfMeasure_pi_mass_le hP_ne hN_ne n hn0 hδ J₁ Q₁ hJ₁_def hQ₁_def φ hφ_def
      B hB_def

/-! ## Per-codeword power constraint -/

/-- Per-codeword power-constraint expurgation bound.

For a codebook drawn from the 2-stage Gaussian product law at codeword variance
`P_cb`, and a power target `P_target` with strict slack `P_cb < P_target`, each
*individual* codeword `m` violates the power budget `∑ᵢ (c m i)² > n · P_target`
on a codebook set of mass `≤ ε` (for all `n` past a threshold `N₀`).

This is the **per-codeword marginal** form: unlike the false `∀ m`-form (mass of
the all-codewords-OK set `≥ 1 − ε`, which decays like `q^M ≈ exp(−exp(n(R−ψ)))`),
the per-codeword marginal mass is `M`-independent (the `m`-th coordinate marginal
of `Measure.pi (fun _ : Fin M => νₙ)` is `νₙ`), so no exponential rate / capacity
rate bound is needed. It is exactly the WLLN/Markov fact the Cover–Thomas
expurgation argument consumes.

Proof: the `m`-th coordinate marginal is `νₙ = Measure.pi (fun _ : Fin n =>
gaussianReal 0 P_cb.toNNReal)` (`measurePreserving_eval`), reducing the codebook
mass to the single-codeword chi-square upper-tail mass. Apply the abstract
Chebyshev engine `pi_empirical_mean_concentration` with statistic `φ x = x²`,
`μ[φ] = (P_cb.toNNReal : ℝ)` (centred Gaussian second moment = variance), and the
deviation level `δ = P_target − (P_cb.toNNReal : ℝ) > 0`: the violating set
`{x | n·P_target < ∑ᵢ xᵢ²}` is contained in the deviation set
`{x | δ ≤ |(∑ᵢ φ(xᵢ))/n − μ[φ]|}`, whose mass is `≤ variance(φ)/(n·δ²)`; choosing
`N₀ > variance(φ)/(ε·δ²)` gives `≤ ε`. `MemLp φ 2` holds because the Gaussian has a
finite 4th moment (`memLp_id_gaussianReal 4`, polynomial — no log). -/
theorem awgnPowerConstraintPerCodeword_holds
    (P_cb P_target : ℝ) (hP_slack : (P_cb.toNNReal : ℝ) < P_target) (N : ℝ≥0) :
    ∀ ⦃ε : ℝ⦄, 0 < ε →
      ∃ N₀ : ℕ, ∀ ⦃n : ℕ⦄, N₀ ≤ n → ∀ ⦃M : ℕ⦄ (_hM_pos : 0 < M),
        ∀ m : Fin M,
          (Measure.pi
              (fun _ : Fin M => Measure.pi (fun _ : Fin n => gaussianReal 0 P_cb.toNNReal)))
            {c : Fin M → Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (c m i) ^ 2}
          ≤ ENNReal.ofReal ε := by
  classical
  -- Abbreviations: codeword law `μ`, statistic `φ = x²`, mean `μ[φ] = variance = P_cb`.
  set v : ℝ≥0 := P_cb.toNNReal with hv_def
  set μ : Measure ℝ := gaussianReal 0 v with hμ_def
  set φ : ℝ → ℝ := fun x => x ^ 2 with hφ_def
  -- `φ ∈ MemLp 2` via finite 4th moment of the Gaussian.
  have hφ_mem : MemLp φ 2 μ := by
    have hmeas : AEStronglyMeasurable φ μ := by
      rw [hφ_def]; exact (measurable_id.pow_const 2).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmeas]
    -- `Integrable (fun x => (x²)²) = Integrable (fun x => x⁴)`, from `MemLp id 4`.
    have hmem4 : MemLp (id : ℝ → ℝ) 4 μ := by
      rw [hμ_def]; exact memLp_id_gaussianReal' 4 (by simp)
    have hint4 : Integrable (fun x : ℝ => ‖(id : ℝ → ℝ) x‖ ^ 4) μ :=
      hmem4.integrable_norm_pow (by norm_num)
    refine hint4.congr ?_
    filter_upwards with x
    rw [hφ_def]
    simp only [id_eq, Real.norm_eq_abs]
    rw [← abs_pow, abs_of_nonneg (by positivity)]
    ring
  -- `μ[φ] = (v : ℝ)` (centred Gaussian second moment = variance).
  have hμφ : μ[φ] = (v : ℝ) := by
    have hmem_id : MemLp (id : ℝ → ℝ) 2 μ := by
      rw [hμ_def]; exact memLp_id_gaussianReal' 2 (by simp)
    have hvar : variance (id : ℝ → ℝ) μ = (v : ℝ) := by
      rw [hμ_def]; exact variance_id_gaussianReal
    have hsub := variance_eq_sub hmem_id
    have hmean : μ[(id : ℝ → ℝ)] = 0 := by
      rw [hμ_def]; simp [integral_id_gaussianReal (μ := (0 : ℝ)) (v := v)]
    rw [hvar, hmean] at hsub
    -- `hsub : (v : ℝ) = μ[id ^ 2] - 0 ^ 2`.
    have hid2 : (μ[(id : ℝ → ℝ) ^ 2]) = μ[φ] := by
      congr 1
    rw [hid2] at hsub
    simpa using hsub.symm
  -- The strict deviation level.
  set δ : ℝ := P_target - (v : ℝ) with hδ_def
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith [hP_slack]
  intro ε hε
  -- Choose `N₀` so that `variance φ μ / (N₀ · δ²) ≤ ε`, mirroring the engine's own
  -- existence construction.
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (variance φ μ / (ε * δ ^ 2))
  refine ⟨N₀ + 1, fun n hn M _hM_pos m => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.succ_pos N₀) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  -- The `m`-th coordinate marginal of the codebook law is `νₙ = Measure.pi μ`.
  have hmarg :
      (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => μ)))
          {c : Fin M → Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (c m i) ^ 2}
        = (Measure.pi (fun _ : Fin n => μ))
            {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2} := by
    have hmp :
        MeasurePreserving (Function.eval m)
          (Measure.pi (fun _ : Fin M => Measure.pi (fun _ : Fin n => μ)))
          (Measure.pi (fun _ : Fin n => μ)) :=
      measurePreserving_eval (fun _ : Fin M => Measure.pi (fun _ : Fin n => μ)) m
    have hmeasSet :
        MeasurableSet {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2} := by
      apply measurableSet_lt measurable_const
      exact Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).pow_const 2)
    have hpre :
        {c : Fin M → Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (c m i) ^ 2}
          = (Function.eval m) ⁻¹' {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2} := by
      rfl
    rw [hpre, hmp.measure_preimage hmeasSet.nullMeasurableSet]
  rw [hmarg]
  -- The violating set is contained in the level-`δ` deviation set.
  have hsubset :
      {x : Fin n → ℝ | (n : ℝ) * P_target < ∑ i, (x i) ^ 2}
        ⊆ {x : Fin n → ℝ | δ ≤ |(∑ i, φ (x i)) / (n : ℝ) - μ[φ]|} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    -- `∑ᵢ φ(xᵢ) = ∑ᵢ xᵢ²` since `φ = (·)²`.
    have hsumφ : (∑ i, φ (x i)) = ∑ i, (x i) ^ 2 := by simp [hφ_def]
    rw [hsumφ, hμφ]
    -- From `n·P_target < ∑ xᵢ²` and `n > 0`: `δ < (∑ xᵢ²)/n − v`.
    have hkey : δ < (∑ i, (x i) ^ 2) / (n : ℝ) - (v : ℝ) := by
      have hdiv : P_target < (∑ i, (x i) ^ 2) / (n : ℝ) := by
        rw [lt_div_iff₀ hnR]; linarith [hx]
      show P_target - (v : ℝ) < (∑ i, (x i) ^ 2) / (n : ℝ) - (v : ℝ)
      linarith
    exact le_of_lt (lt_of_lt_of_le hkey (le_abs_self _))
  -- Mass of the violating set ≤ mass of the deviation set ≤ variance/(n·δ²) ≤ ε.
  have hdev := pi_empirical_mean_concentration μ hφ_mem hδ_pos hn0
  have hviol_le := measure_mono (μ := Measure.pi (fun _ : Fin n => μ)) hsubset
  refine le_trans (le_trans hviol_le hdev) ?_
  -- `variance φ μ / (n · δ²) ≤ ε`.
  apply ENNReal.ofReal_le_ofReal
  have hVarnn : (0 : ℝ) ≤ variance φ μ := variance_nonneg φ μ
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hεδ : (0 : ℝ) < ε * δ ^ 2 := by positivity
  -- `variance / (ε·δ²) < N₀ ≤ n`.
  have hNn : variance φ μ / (ε * δ ^ 2) < (n : ℝ) := by
    calc variance φ μ / (ε * δ ^ 2) < (N₀ : ℝ) := hN₀
      _ ≤ (n : ℝ) := by exact_mod_cast le_trans (Nat.le_succ N₀) hn
  rw [div_le_iff₀ (by positivity)]
  rw [div_lt_iff₀ hεδ] at hNn
  nlinarith [hNn, hVarnn, hδ2, hnR]

/-! ## Converse-side shared lemmas

The converse-side analytic facts: per-letter log-density integrability, the memoryless
MI chain rule, and the deterministic-encoder Markov factorization.

The old predicate bodies referenced `awgnConverseJoint` / `perLetterYLaw` / `perLetterMI`
/ `jointMIXnYn`, all defined in `AWGNConverseDischarge.lean`. Referencing those named defs
from this file directly would create the import cycle
`Walls → ConverseDischarge → Walls`, so the body of `awgnConverseJoint` is inlined here as
the private mirror def `converseJointInline`. The two defs share the same RHS, so they are
definitionally equal: on the consumer side `unfold awgnConverseJoint perLetterYLaw …`
reduces the goal to the inline form here, where the shared lemmas apply. -/

/-- Mirror of the `awgnConverseJoint` body, inlined here to break the would-be import
cycle. Defeq to `awgnConverseJoint h_meas c` (both `def`s share the same RHS, so
consumer-side `unfold awgnConverseJoint` reduces to this form). -/
private noncomputable def converseJointInline
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    Measure (Fin M × (Fin n → ℝ)) :=
  ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) •
    ∑ m : Fin M,
      (Measure.dirac m).prod
        (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i)))

/-- `converseJointInline` is a probability measure for `M ≥ 1` (mixture with weights
`1/M` summing to 1). Mirror of `awgnConverseJoint.instIsProbabilityMeasure`
(`AWGNConverseDischarge.lean:77`); needed so `IsMarkovChain`'s `[IsFiniteMeasure μ]`
prerequisite resolves on the inlined joint. -/
private instance converseJointInline.instIsProbabilityMeasure
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsProbabilityMeasure (converseJointInline h_meas c) := by
  refine ⟨?_⟩
  unfold converseJointInline
  rw [Measure.smul_apply, Measure.finsetSum_apply _ _ Set.univ]
  have h_summand : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
            Set.univ = 1 := fun _ => measure_univ
  simp only [h_summand, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  have hM_ne_zero : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hM_ne_top : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
  exact ENNReal.inv_mul_cancel hM_ne_zero hM_ne_top

/-! ### Per-letter log-density integrability

The goal is a 1-dimensional integrability against `volume` on `ℝ`. The per-letter output
law `Y_i` is a finite mixture of shifted 1-D Gaussians `(1/M) ∑ₘ 𝒩(encoder m i, N)`, so
its `rnDeriv volume` is the finite Gaussian-mixture density
`(1/M) ∑ₘ gaussianPDF (encoder m i) N`. `negMulLog` of that density is dominated by a
Gaussian moment integrand — pure 1-D measure-theoretic domination. The proof mirrors the
continuous-input analogue `AwgnCapacityConverseMaxent.outputDistribution_logDensity_integrable`
(not importable here, due to the import cycle), but is simpler: the finite mixture needs no
Chebyshev concentration (the lower bound comes from a single component). -/

/-- The finite per-letter Gaussian-mixture density at coordinate `i`:
`(1/M) ∑ₘ gaussianPDF (encoder m i) N y` (`ℝ≥0∞`-valued). For `M ≥ 1` and `N ≠ 0` this is
the `rnDeriv volume` of the per-letter output law `(converseJointInline h_meas c).map (·.2 i)`. -/
private noncomputable def perLetterMixtureDensity
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (y : ℝ) : ℝ≥0∞ :=
  ((M : ℝ≥0∞))⁻¹ * ∑ m : Fin M, gaussianPDF (c.encoder m i) N y

private lemma perLetterMixtureDensity_measurable
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    Measurable (perLetterMixtureDensity N c i) := by
  unfold perLetterMixtureDensity
  refine Measurable.const_mul ?_ _
  exact Finset.measurable_sum _ (fun m _ => measurable_gaussianPDF (c.encoder m i) N)

/-- The per-letter output law equals the explicit finite Gaussian mixture
`(1/M) • ∑ₘ 𝒩(encoder m i, N)` (the decisive atom: pushforward of the inlined joint
mixture-of-diracs⊗pi through `ω ↦ ω.2 i`, marginalizing the `pi` to its `i`-th factor). -/
private lemma perLetterLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    (converseJointInline h_meas c).map (fun ω => ω.2 i)
      = ((M : ℝ≥0∞))⁻¹ • ∑ m : Fin M, gaussianReal (c.encoder m i) N := by
  classical
  have hf_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  unfold converseJointInline
  rw [Measure.map_smul, Measure.map_finset_sum hf_meas.aemeasurable]
  simp only [Fintype.card_fin]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  -- `((dirac m).prod (pi μ_m)).map (·.2 i) = gaussianReal (encoder m i) N`
  -- via `map ((eval i) ∘ snd) = (map snd).map (eval i)`.
  have h_comp : (fun ω : Fin M × (Fin n → ℝ) => ω.2 i)
      = (Function.eval i) ∘ (Prod.snd : Fin M × (Fin n → ℝ) → (Fin n → ℝ)) := rfl
  rw [h_comp, ← Measure.map_map (measurable_pi_apply i) measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul,
    Measure.pi_map_eval]
  -- `∏ j ∈ erase i, (awgnChannel N (encoder m j)) univ = 1` (each fibre is a prob measure)
  have h_prod_one : (∏ j ∈ Finset.univ.erase i,
      (awgnChannel N h_meas (c.encoder m j)) Set.univ) = 1 := by
    refine Finset.prod_eq_one (fun j _ => ?_)
    rw [awgnChannel_apply]; exact measure_univ
  rw [h_prod_one, one_smul, awgnChannel_apply]

/-- For `M ≥ 1` and `N ≠ 0`, the per-letter output law is
`volume.withDensity (perLetterMixtureDensity c i)`. -/
private lemma perLetterLaw_withDensity
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    (converseJointInline h_meas c).map (fun ω => ω.2 i)
      = volume.withDensity (perLetterMixtureDensity N c i) := by
  classical
  rw [perLetterLaw_eq_mixture h_meas c i]
  -- Each component: `gaussianReal μ N = volume.withDensity (gaussianPDF μ N)`.
  have h_comp : ∀ m : Fin M,
      gaussianReal (c.encoder m i) N
        = volume.withDensity (gaussianPDF (c.encoder m i) N) :=
    fun m => gaussianReal_of_var_ne_zero (c.encoder m i) hN
  -- Sum of withDensity = withDensity of sum (finset induction).
  have h_sum : ∀ s : Finset (Fin M),
      (∑ m ∈ s, gaussianReal (c.encoder m i) N)
        = volume.withDensity (∑ m ∈ s, gaussianPDF (c.encoder m i) N) := by
    intro s
    induction s using Finset.induction with
    | empty => simp [withDensity_zero]
    | insert m s hms ih =>
        rw [Finset.sum_insert hms, Finset.sum_insert hms, ih, h_comp m,
          withDensity_add_left (measurable_gaussianPDF _ _)]
  rw [h_sum Finset.univ]
  -- `M⁻¹ • volume.withDensity g = volume.withDensity (M⁻¹ • g)`.
  have hM_ne_top : (M : ℝ≥0∞)⁻¹ ≠ ∞ := by
    simp
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hM)
  rw [← withDensity_smul' _ _ hM_ne_top]
  -- `M⁻¹ • (∑ₘ gaussianPDF ...) = perLetterMixtureDensity N c i` (pointwise = M⁻¹ * ∑).
  congr 1
  funext y
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, perLetterMixtureDensity]

/-- The mixture density is bounded above by `(√(2πN))⁻¹` (each component is, and the
weights `1/M` sum to ≤ 1). -/
private lemma perLetterMixtureDensity_le_sup
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (y : ℝ) :
    perLetterMixtureDensity N c i y ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
  -- each Gaussian component pdf is `≤ ofReal (√(2πN))⁻¹`
  have h_comp : ∀ m : Fin M,
      gaussianPDF (c.encoder m i) N y ≤ ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
    intro m
    rw [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    -- `gaussianPDFReal μ N y ≤ (√(2πN))⁻¹` (exp factor ≤ 1)
    rw [gaussianPDFReal]
    have h_const_nonneg : 0 ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ := by positivity
    have h_exp_le_one : Real.exp (-(y - c.encoder m i) ^ 2 / (2 * N)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have : 0 ≤ (y - c.encoder m i) ^ 2 / (2 * (N : ℝ)) := by positivity
      linarith
    calc (Real.sqrt (2 * Real.pi * N))⁻¹ * Real.exp (-(y - c.encoder m i) ^ 2 / (2 * N))
        ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h_exp_le_one h_const_nonneg
      _ = (Real.sqrt (2 * Real.pi * N))⁻¹ := mul_one _
  unfold perLetterMixtureDensity
  -- `M⁻¹ * ∑ₘ (≤ B) ≤ M⁻¹ * (M • B) = M⁻¹ * (M * B) = B`
  calc (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, gaussianPDF (c.encoder m i) N y
      ≤ (M : ℝ≥0∞)⁻¹ * ∑ _m : Fin M, ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
        gcongr with m _
        exact h_comp m
    _ = (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal (Real.sqrt (2 * Real.pi * N))⁻¹ := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast (Nat.pos_iff_ne_zero.mp hM))
          (ENNReal.natCast_ne_top M), one_mul]

/-- Lower bound on `log` of the mixture density (no Chebyshev needed — a single component
suffices): there are `c₀ c₁` with `|log (f y).toReal| ≤ c₀ + c₁ y²`. -/
private lemma perLetterMixtureDensity_log_abs_le
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ y : ℝ,
      |Real.log ((perLetterMixtureDensity N c i y).toReal)| ≤ c₀ + c₁ * y ^ 2 := by
  classical
  have hN_pos : (0 : ℝ) < N := lt_of_le_of_ne N.coe_nonneg (fun h => hN (by exact_mod_cast h.symm))
  set sup : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hsup_def
  have hsup_nonneg : 0 ≤ sup := by rw [hsup_def]; positivity
  -- a fixed representative message `m₀`
  set m₀ : Fin M := ⟨0, hM⟩ with hm₀_def
  set μ₀ : ℝ := c.encoder m₀ i with hμ₀_def
  -- The mixture density never exceeds `sup` (real form via `le_sup`).
  have h_up_real : ∀ y, (perLetterMixtureDensity N c i y).toReal ≤ sup := by
    intro y
    have h := perLetterMixtureDensity_le_sup N c i hM y
    rw [← hsup_def] at h
    calc (perLetterMixtureDensity N c i y).toReal
        ≤ (ENNReal.ofReal sup).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = sup := ENNReal.toReal_ofReal hsup_nonneg
  -- upper bound on `log f(y)`: `≤ max (log sup) 0`.
  have h_up : ∀ y, Real.log ((perLetterMixtureDensity N c i y).toReal) ≤ max (Real.log sup) 0 := by
    intro y
    rcases le_or_gt (perLetterMixtureDensity N c i y).toReal 0 with h0 | h0
    · have : (perLetterMixtureDensity N c i y).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
      rw [this, Real.log_zero]; exact le_max_right _ _
    · exact le_trans (Real.log_le_log h0 (h_up_real y)) (le_max_left _ _)
  -- single-component lower bound: `f(y).toReal ≥ M⁻¹ * gaussianPDFReal μ₀ N y`.
  have h_low_real : ∀ y, ((M : ℝ)⁻¹) * gaussianPDFReal μ₀ N y
      ≤ (perLetterMixtureDensity N c i y).toReal := by
    intro y
    -- `f y = M⁻¹ * ∑ₘ ofReal (gaussianPDFReal · ) ≥ M⁻¹ * ofReal (gaussianPDFReal μ₀)`
    have h_ne_top : perLetterMixtureDensity N c i y ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (perLetterMixtureDensity_le_sup N c i hM y)
    have h_ge : ENNReal.ofReal ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        ≤ perLetterMixtureDensity N c i y := by
      unfold perLetterMixtureDensity
      rw [ENNReal.ofReal_mul (by positivity)]
      have h_inv : ENNReal.ofReal ((M : ℝ)⁻¹) = (M : ℝ≥0∞)⁻¹ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hM)]
      rw [h_inv]
      gcongr
      -- `ofReal (gaussianPDFReal μ₀ N y) = gaussianPDF μ₀ N y ≤ ∑ₘ gaussianPDF · `
      rw [← gaussianPDF]
      exact Finset.single_le_sum (f := fun m => gaussianPDF (c.encoder m i) N y)
        (fun m _ => zero_le') (Finset.mem_univ m₀)
    calc ((M : ℝ)⁻¹) * gaussianPDFReal μ₀ N y
        = (ENNReal.ofReal ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)).toReal := by
          rw [ENNReal.toReal_ofReal (mul_nonneg (by positivity) (gaussianPDFReal_nonneg μ₀ N y))]
      _ ≤ (perLetterMixtureDensity N c i y).toReal := ENNReal.toReal_mono h_ne_top h_ge
  -- lower bound on `log f(y)`: `-log f(y) ≤ (1/N) y² + b` from the single-component bound.
  -- `M⁻¹ · gaussianPDFReal μ₀ N y = M⁻¹ · sup · exp(-(y-μ₀)²/(2N))`, so
  -- `-log(M⁻¹ gaussianPDFReal) = log M - log sup + (y-μ₀)²/(2N) ≤ a y² + b`.
  have hgpos : ∀ y, 0 < gaussianPDFReal μ₀ N y := fun y => gaussianPDFReal_pos μ₀ N y hN
  set bLow : ℝ := Real.log M - Real.log sup + μ₀ ^ 2 / (N : ℝ) with hbLow_def
  refine ⟨max (Real.log sup) 0 + max bLow 0, 1 / (N : ℝ), by positivity, fun y => ?_⟩
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- `-(c₀ + c₁ y²) ≤ log f(y)`: use single-component lower bound + log algebra.
    have h_low := h_low_real y
    have hlow_pos : 0 < (M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y :=
      mul_pos (by positivity) (hgpos y)
    have h_log_low : Real.log ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        ≤ Real.log ((perLetterMixtureDensity N c i y).toReal) :=
      Real.log_le_log hlow_pos h_low
    -- compute `log (M⁻¹ gaussianPDFReal μ₀ N y)`
    have h_log_eq : Real.log ((M : ℝ)⁻¹ * gaussianPDFReal μ₀ N y)
        = -Real.log M + (Real.log sup - (y - μ₀) ^ 2 / (2 * N)) := by
      rw [Real.log_mul (by positivity) (hgpos y).ne', Real.log_inv, gaussianPDFReal,
        Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp, ← hsup_def, neg_div]
      ring
    rw [h_log_eq] at h_log_low
    -- `(y-μ₀)²/(2N) ≤ (y²+μ₀²)/N` (cleared division)
    have h_quad : (y - μ₀) ^ 2 / (2 * (N : ℝ)) ≤ (y ^ 2 + μ₀ ^ 2) / (N : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hN_pos]
      nlinarith [sq_nonneg (y + μ₀), hN_pos]
    have h_split : (y ^ 2 + μ₀ ^ 2) / (N : ℝ) = y ^ 2 / (N : ℝ) + μ₀ ^ 2 / (N : ℝ) := by
      rw [add_div]
    have h_max1 : (0 : ℝ) ≤ max (Real.log sup) 0 := le_max_right _ _
    have h_max2 : bLow ≤ max bLow 0 := le_max_left _ _
    have h_c1 : 1 / (N : ℝ) * y ^ 2 = y ^ 2 / (N : ℝ) := by rw [div_mul_eq_mul_div, one_mul]
    rw [h_c1]
    -- unfold `bLow` so linarith sees the same atom `μ₀²/N`
    simp only [hbLow_def] at *
    linarith [h_log_low, h_quad, h_split, h_max1, h_max2]
  · -- `log f(y) ≤ c₀ + c₁ y²`: from the upper bound.
    have h := h_up y
    have h_sq : (0 : ℝ) ≤ 1 / (N : ℝ) * y ^ 2 := by positivity
    have h_max2 : (0 : ℝ) ≤ max bLow 0 := le_max_right _ _
    linarith [h, h_sq, h_max2]

/-- `y²` is integrable against the per-letter output law (finite mixture of Gaussians,
each with finite second moment). -/
private lemma perLetterLaw_sq_integrable
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) (hM : 0 < M) (hN : N ≠ 0) :
    Integrable (fun y : ℝ => y ^ 2)
      ((converseJointInline h_meas c).map (fun ω => ω.2 i)) := by
  rw [perLetterLaw_eq_mixture h_meas c i]
  -- each component Gaussian has integrable `y²`
  have h_comp : ∀ m : Fin M, Integrable (fun y : ℝ => y ^ 2) (gaussianReal (c.encoder m i) N) := by
    intro m
    have h := (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
    simpa using h
  have hM_ne_top : (M : ℝ≥0∞)⁻¹ ≠ ∞ := by
    simp only [ne_eq, ENNReal.inv_eq_top, Nat.cast_eq_zero]
    exact Nat.pos_iff_ne_zero.mp hM
  refine Integrable.smul_measure ?_ hM_ne_top
  exact integrable_finsetSum_measure.mpr (fun m _ => h_comp m)

/-- Per-letter `Y_i` log-density integrability.

For every coordinate `i`, the per-letter output law `Y_i` (here the pushforward of the
inlined joint along `ω ↦ ω.2 i`) has Lebesgue-integrable `negMulLog (rnDeriv · vol)`.
Consumer-side `unfold perLetterYLaw awgnConverseJoint` reduces `perLetterYLaw h_meas c i`
to `(converseJointInline h_meas c).map (fun ω => ω.2 i)` (defeq).

The per-letter law is a finite Gaussian mixture; `negMulLog` of its `rnDeriv` is
dominated by a Gaussian-moment integrand (`perLetterMixtureDensity_log_abs_le` +
`perLetterLaw_sq_integrable`). The degenerate `M = 0` / `N = 0` cases give a singular
law (`rnDeriv = 0` a.e., `negMulLog 0 = 0`, constant, integrable), so the boundary is
discharged by a genuine singular-law argument rather than a vacuity exploit.
@audit:ok -/
@[entry_point]
theorem awgnPerLetterIntegrability_holds
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) :
    ∀ i : Fin n,
      MeasureTheory.Integrable (fun y : ℝ =>
          Real.negMulLog
            (((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv
                MeasureTheory.volume y).toReal)
        MeasureTheory.volume := by
  classical
  intro i
  set ν : Measure ℝ := (converseJointInline h_meas c).map (fun ω => ω.2 i) with hν_def
  -- Degenerate cases (`M = 0` or `N = 0`): `ν ⟂ volume`, so `rnDeriv =ᵐ 0` and the
  -- integrand is a.e. `negMulLog 0 = 0`, hence integrable.
  by_cases hMN : 0 < M ∧ N ≠ 0
  · obtain ⟨hM, hN⟩ := hMN
    haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM⟩
    -- `ν` is a probability measure (pushforward of the probability mixture)
    haveI hν_prob : IsProbabilityMeasure ν := by
      rw [hν_def]
      exact Measure.isProbabilityMeasure_map ((measurable_pi_apply i).comp measurable_snd).aemeasurable
    -- main case: `ν = volume.withDensity f`, `f := perLetterMixtureDensity N c i`.
    set f : ℝ → ℝ≥0∞ := perLetterMixtureDensity N c i with hf_def
    have hf_meas : Measurable f := perLetterMixtureDensity_measurable N c i
    have hν_wd : ν = volume.withDensity f := by
      rw [hν_def, hf_def]; exact perLetterLaw_withDensity h_meas c i hM hN
    -- `ν.rnDeriv volume =ᵐ[volume] f`
    have h_rn_ae : ν.rnDeriv volume =ᵐ[volume] f := by
      rw [hν_wd]; exact Measure.rnDeriv_withDensity volume hf_meas
    -- `f y < ∞` a.e. (bounded above)
    have hf_lt_top : ∀ᵐ y ∂(volume : Measure ℝ), f y < ∞ :=
      Filter.Eventually.of_forall (fun y =>
        lt_of_le_of_lt (perLetterMixtureDensity_le_sup N c i hM y) ENNReal.ofReal_lt_top)
    -- quadratic abs bound on `log f`
    obtain ⟨c₀, c₁, hc₁, h_abs⟩ := perLetterMixtureDensity_log_abs_le N c i hM hN
    -- `c₀ + c₁ y²` integrable against ν, transport to `(f y).toReal • (c₀+c₁y²)` on volume
    have h_dom_ν : Integrable (fun y : ℝ => c₀ + c₁ * y ^ 2) ν :=
      (integrable_const c₀).add ((perLetterLaw_sq_integrable h_meas c i hM hN).const_mul c₁)
    have h_dom_vol : Integrable (fun y : ℝ => (f y).toReal • (c₀ + c₁ * y ^ 2)) volume :=
      (integrable_withDensity_iff_integrable_smul' hf_meas hf_lt_top).mp
        (by rw [← hν_wd]; exact h_dom_ν)
    -- dominate `negMulLog (rnDeriv)` by `(f y).toReal · (c₀ + c₁ y²)`
    refine Integrable.mono' h_dom_vol ?_ ?_
    · have h_rn_meas : Measurable (fun y => (ν.rnDeriv volume y).toReal) :=
        (Measure.measurable_rnDeriv ν volume).ennreal_toReal
      exact (Real.continuous_negMulLog.measurable.comp h_rn_meas).aestronglyMeasurable
    · filter_upwards [h_rn_ae] with y hy
      rw [hy, smul_eq_mul, Real.norm_eq_abs]
      set t : ℝ := (f y).toReal with ht_def
      have ht_nonneg : 0 ≤ t := ENNReal.toReal_nonneg
      rw [Real.negMulLog_def, abs_mul, abs_neg, abs_of_nonneg ht_nonneg]
      exact mul_le_mul_of_nonneg_left (h_abs y) ht_nonneg
  · -- degenerate: `ν ⟂ volume`, so `rnDeriv =ᵐ 0`; integrand a.e. `0`.
    have h_rn_zero : ν.rnDeriv volume =ᵐ[volume] 0 := by
      rcases not_and_or.mp hMN with hM0 | hN0
      · -- `M = 0`: `ν = 0` measure
        have hM_eq : M = 0 := Nat.le_zero.mp (Nat.not_lt.mp hM0)
        have hν_zero : ν = 0 := by
          rw [hν_def, perLetterLaw_eq_mixture h_meas c i]
          subst hM_eq
          simp
        rw [hν_zero]; exact Measure.rnDeriv_zero volume
      · -- `N = 0`: `ν` is a finite sum of Diracs, mutually singular with volume
        have hN_eq : N = 0 := not_not.mp hN0
        have hν_dirac : ν = ((M : ℝ≥0∞))⁻¹ • ∑ m : Fin M, Measure.dirac (c.encoder m i) := by
          rw [hν_def, perLetterLaw_eq_mixture h_meas c i]
          subst hN_eq
          simp only [gaussianReal_zero_var]
        have h_sum_sing : ∀ s : Finset (Fin M),
            (∑ m ∈ s, Measure.dirac (c.encoder m i)) ⟂ₘ (volume : Measure ℝ) := by
          intro s
          induction s using Finset.induction with
          | empty => simp [Measure.MutuallySingular.zero_left]
          | insert m s hms ih =>
              rw [Finset.sum_insert hms]
              exact (mutuallySingular_dirac (c.encoder m i) volume).add_left ih
        have h_sing : ν ⟂ₘ volume := by
          rw [hν_dirac]
          exact (h_sum_sing Finset.univ).smul _
        exact h_sing.rnDeriv_ae_eq_zero
    -- integrand a.e. equals `negMulLog 0 = 0`
    refine (integrable_zero ℝ ℝ volume).congr ?_
    filter_upwards [h_rn_zero] with y hy
    rw [hy]; simp

/-! ### Memoryless MI chain rule

The chain rule `I(X^n;Y^n) ≤ ∑ᵢ I(X_i;Y_i)` is the textbook argument
`I(W;Y^n) = h(Y^n) − n·h(noise) ≤ ∑ h(Y_i) − n·h(noise) = ∑ I(X_i;Y_i)`, combined with the
deterministic data-processing inequality `I(X^n;Y^n) ≤ I(W;Y^n)` (since `X^n = encoder ∘ W`
is a measurable post-processing of `W`, via `mutualInfo_le_of_postprocess` — no Markov-chain
machinery needed). The `I(W;Y^n)` decomposition uses the discrete-input block kernel
`blockKernelInline : Channel (Fin M) (Fin n → ℝ)` whose measurability is free
(`measurable_of_countable`, input `Fin M`), so the parallel-Gaussian kernel-measurability
gap (X-input route) is sidestepped. Pieces:

* the generic n-D continuous-channel MI decomposition
  `ChannelCoding.mutualInfoOfChannel_toReal_eq_log_density_sub` (the gateway atom, output
  type `β := Fin n → ℝ`, reference `volume`; genuine, no wall), giving
  `I(W;Y^n).toReal = h(Y^n) − n·h(noise)`;
* the n-D subadditivity `Shannon.jointDifferentialEntropyPi_le_sum` (genuine);
* the per-letter 1-D decomposition `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (genuine),
  giving `I(X_i;Y_i).toReal = h(Y_i) − h(noise)`.

The block regularity machinery mirrors the per-letter Wall-4 closure above and the
`AWGNConverseDischarge.lean` block infrastructure. -/

/-- Discrete-input block kernel `K m := pi (gaussianReal (encoder m i) N)` (`Fin M → Y^n`).
Measurability is free (`measurable_of_countable`, input `Fin M`). -/
private noncomputable def blockKernelInline
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) :
    ChannelCoding.Channel (Fin M) (Fin n → ℝ) :=
  { toFun := fun m => Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
    measurable' := measurable_of_countable _ }

private instance blockKernelInline_isMarkov
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) :
    ProbabilityTheory.IsMarkovKernel (blockKernelInline N c) :=
  ⟨fun m => by
    show IsProbabilityMeasure (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N))
    infer_instance⟩

/-- Uniform message law `msgLawInline := (M⁻¹ : ℝ≥0∞) • count` on `Fin M`. -/
private noncomputable def msgLawInline (M : ℕ) : Measure (Fin M) :=
  (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count

private instance msgLawInline_isProb (M : ℕ) [NeZero M] :
    IsProbabilityMeasure (msgLawInline M) := by
  refine ⟨?_⟩
  rw [msgLawInline, Measure.smul_apply, smul_eq_mul, Fintype.card_fin]
  have h_count : (Measure.count : Measure (Fin M)) Set.univ = (M : ℝ≥0∞) := by
    rw [Measure.count_apply_finite _ (Set.finite_univ)]
    simp [Fintype.card_fin]
  rw [h_count, ENNReal.inv_mul_cancel (by exact_mod_cast (NeZero.ne M))
    (ENNReal.natCast_ne_top M)]

/-- Block output law `Y^n` = `(converseJointInline).map snd` (= mixture of product
Gaussians). This is `outputDistribution msgLawInline blockKernelInline`. -/
private noncomputable def blockYLawInline
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) : Measure (Fin n → ℝ) :=
  (converseJointInline h_meas c).map Prod.snd

/-- Real-valued block mixture density `M⁻¹ ∑ₘ ∏ᵢ gaussianPDFReal (encoder m i) N (yᵢ)`. -/
private noncomputable def blockRealDensityInline
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) (y : Fin n → ℝ) : ℝ :=
  (1 / (M : ℝ)) * ∑ m : Fin M, ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)

/-- `blockYLawInline = M⁻¹ • ∑ₘ pi (gaussianReal (encoder m i) N)` (closed mixture form). -/
private lemma blockYLawInline_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLawInline h_meas c
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
          ∑ m : Fin M, Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) := by
  classical
  unfold blockYLawInline converseJointInline
  have h_meas_snd :
      Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  rw [Measure.map_smul,
    Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      h_meas_snd.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro m _
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  refine congrArg (Measure.pi) ?_
  funext i
  rw [awgnChannel_apply]

private lemma blockRealDensityInline_pos
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (y : Fin n → ℝ) :
    0 < blockRealDensityInline N c y := by
  classical
  obtain ⟨m₀⟩ : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩⟩
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  unfold blockRealDensityInline
  refine mul_pos (by positivity) ?_
  refine Finset.sum_pos (fun m _ => Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hN)) ?_
  exact ⟨m₀, Finset.mem_univ m₀⟩

private lemma blockRealDensityInline_measurable
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) :
    Measurable (blockRealDensityInline N c) := by
  unfold blockRealDensityInline
  refine measurable_const.mul ?_
  refine Finset.measurable_sum _ (fun m _ => ?_)
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_gaussianPDFReal (c.encoder m i) N).comp (measurable_pi_apply i))

private lemma blockComponentInline_withDensity
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0)
    {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
  have h_each : ∀ i, gaussianReal (c.encoder m i) N
      = (MeasureTheory.volume : Measure ℝ).withDensity (gaussianPDF (c.encoder m i) N) :=
    fun i => gaussianReal_of_var_ne_zero (c.encoder m i) hN
  haveI : ∀ i, SigmaFinite ((MeasureTheory.volume : Measure ℝ).withDensity
      (gaussianPDF (c.encoder m i) N)) := by
    intro i; rw [← h_each i]; infer_instance
  rw [show (fun i : Fin n => gaussianReal (c.encoder m i) N)
        = (fun i => (MeasureTheory.volume : Measure ℝ).withDensity
            (gaussianPDF (c.encoder m i) N)) from funext h_each,
    InformationTheory.Shannon.pi_withDensity_fin (fun _ => (MeasureTheory.volume : Measure ℝ))
      (fun i => measurable_gaussianPDF (c.encoder m i) N), ← volume_pi]

private lemma blockYLawInline_withDensity_real
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLawInline h_meas c
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y => ENNReal.ofReal (blockRealDensityInline N c y)) := by
  classical
  rw [blockYLawInline_eq_mixture h_meas c]
  have h_comp := fun m : Fin M => blockComponentInline_withDensity hN c m
  have h_sum : ∀ s : Finset (Fin M),
      (∑ m ∈ s, Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N))
        = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
            (fun y => ∑ m ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert m s hms ih =>
        have h_density_eq :
            (fun y : Fin n → ℝ => ∑ m' ∈ insert m s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i))
              = (fun y : Fin n → ℝ => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
                + (fun y : Fin n → ℝ => ∑ m' ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i)) := by
          funext y; simp only [Pi.add_apply]; rw [Finset.sum_insert hms]
        rw [Finset.sum_insert hms, ih, h_comp m, h_density_eq]
        rw [withDensity_add_left
            (μ := (MeasureTheory.volume : Measure (Fin n → ℝ)))
            (f := fun y : Fin n → ℝ => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
            (Finset.measurable_prod _ (fun i _ =>
              (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i)))
            (fun y : Fin n → ℝ => ∑ m' ∈ s, ∏ i : Fin n, gaussianPDF (c.encoder m' i) N (y i))]
  rw [h_sum Finset.univ]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  rw [← withDensity_smul' _ _ hM_inv_ne_top]
  congr 1
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, blockRealDensityInline, Fintype.card_fin]
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  · rw [one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)),
      ENNReal.ofReal_natCast]
  · rw [ENNReal.ofReal_sum_of_nonneg
          (fun m _ => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _))]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [gaussianPDF]

private lemma blockYLawInline_ac_volume
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    blockYLawInline h_meas c ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
  rw [blockYLawInline_withDensity_real hN h_meas c]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

private lemma volume_ac_blockYLawInline
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (MeasureTheory.volume : Measure (Fin n → ℝ)) ≪ blockYLawInline h_meas c := by
  rw [blockYLawInline_withDensity_real hN h_meas c]
  refine withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp (blockRealDensityInline_measurable c)).aemeasurable ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact blockRealDensityInline_pos hN c y

private instance blockYLawInline_isProb
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsProbabilityMeasure (blockYLawInline h_meas c) := by
  rw [blockYLawInline]
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

/-- The block component `pi (gaussianReal (encoder m i) N) ≪ blockYLawInline`
(`νₘ ≪ vol ≪ blockYLaw`). -/
private lemma blockComponentInline_ac_blockYLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c := by
  have h1 : Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
      ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  exact h1.trans (volume_ac_blockYLawInline hN h_meas c)

/-- Per-component lower bound:
`blockRealDensityInline y ≥ M⁻¹ · ∏ᵢ gaussianPDFReal (encoder m i) N (yᵢ)`. -/
private lemma blockRealDensityInline_ge_component
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) (y : Fin n → ℝ) :
    (1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ blockRealDensityInline N c y := by
  unfold blockRealDensityInline
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine Finset.single_le_sum
    (f := fun m => ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i))
    (fun m _ => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _))
    (Finset.mem_univ m)

/-- Sup upper bound: `blockRealDensityInline y ≤ ∏ᵢ (√(2πN))⁻¹`. -/
private lemma blockRealDensityInline_le_sup
    {P : ℝ} {N : ℝ≥0} {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (y : Fin n → ℝ) :
    blockRealDensityInline N c y ≤ ∏ _i : Fin n, (Real.sqrt (2 * Real.pi * N))⁻¹ := by
  classical
  unfold blockRealDensityInline
  set Bpeak : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hBpeak
  have hBpeak_nonneg : (0 : ℝ) ≤ Bpeak := by rw [hBpeak]; positivity
  have h_comp_le : ∀ (a x : ℝ), gaussianPDFReal a N x ≤ Bpeak := by
    intro a x
    rw [gaussianPDFReal, hBpeak]
    have h_exp_le_one : Real.exp (-(x - a) ^ 2 / (2 * N)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have : 0 ≤ (x - a) ^ 2 / (2 * (N : ℝ)) := by positivity
      linarith
    calc (Real.sqrt (2 * Real.pi * N))⁻¹ * Real.exp (-(x - a) ^ 2 / (2 * N))
        ≤ (Real.sqrt (2 * Real.pi * N))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left h_exp_le_one (by positivity)
      _ = (Real.sqrt (2 * Real.pi * N))⁻¹ := mul_one _
  have h_prod_le : ∀ m : Fin M,
      (∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)) ≤ ∏ _i : Fin n, Bpeak := by
    intro m
    refine Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg _ _ _) (fun i _ => ?_)
    exact h_comp_le (c.encoder m i) (y i)
  calc (1 / (M : ℝ)) * ∑ m : Fin M, ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ (1 / (M : ℝ)) * ∑ _m : Fin M, ∏ _i : Fin n, Bpeak := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun m _ => h_prod_le m)
    _ = (1 / (M : ℝ)) * ((M : ℝ) * ∏ _i : Fin n, Bpeak) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∏ _i : Fin n, Bpeak := by
        have : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
        field_simp

/-- Per-component output log-density integrability (n-dim) against the m-th product-Gaussian
fibre `pi (gaussianReal (encoder m i) N)`. Mirror of
`AWGNConverseDischarge.integrable_log_blockYLaw_on_component`. -/
private lemma integrable_log_blockYLawInline_on_component
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y => Real.log ((blockYLawInline h_meas c).rnDeriv MeasureTheory.volume y).toReal)
      (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)) := by
  classical
  set q := blockYLawInline h_meas c with hq_def
  set νm := Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) with hνm_def
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i => inferInstance
  haveI hνm_prob : IsProbabilityMeasure νm := by rw [hνm_def]; infer_instance
  have hq_wd : q = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
      (fun y => ENNReal.ofReal (blockRealDensityInline N c y)) := by
    rw [hq_def]; exact blockYLawInline_withDensity_real hN h_meas c
  have hDR_meas : Measurable (fun y => ENNReal.ofReal (blockRealDensityInline N c y)) :=
    ENNReal.measurable_ofReal.comp (blockRealDensityInline_measurable c)
  have hνm_ac : νm ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [hνm_def, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_rn_vol : q.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[(MeasureTheory.volume : Measure (Fin n → ℝ))]
      (fun y => ENNReal.ofReal (blockRealDensityInline N c y)) := by
    rw [hq_wd]; exact Measure.rnDeriv_withDensity _ hDR_meas
  have h_rn_νm : q.rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[νm] (fun y => ENNReal.ofReal (blockRealDensityInline N c y)) :=
    hνm_ac.ae_le h_rn_vol
  have h_log_ae : (fun y => Real.log (q.rnDeriv MeasureTheory.volume y).toReal)
      =ᵐ[νm] (fun y => Real.log (blockRealDensityInline N c y)) := by
    filter_upwards [h_rn_νm] with y hy
    rw [hy, ENNReal.toReal_ofReal (blockRealDensityInline_pos hN c y).le]
  refine (Integrable.congr ?_ h_log_ae.symm)
  set Bpeak : ℝ := (Real.sqrt (2 * Real.pi * N))⁻¹ with hBpeak
  have hBpeak_pos : 0 < Bpeak := by rw [hBpeak]; positivity
  have hD_le : ∀ y, blockRealDensityInline N c y ≤ ∏ _i : Fin n, Bpeak :=
    blockRealDensityInline_le_sup c
  have hD_ge : ∀ y, (1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)
      ≤ blockRealDensityInline N c y := fun y => blockRealDensityInline_ge_component c m y
  set c₀ : ℝ := -(1 / 2) * Real.log (2 * Real.pi * N) with hc₀
  set c₁ : ℝ := -(1 / (2 * (N : ℝ))) with hc₁
  set Aconst : ℝ := |Real.log (∏ _i : Fin n, Bpeak)|
      + |Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀| with hAconst
  set Bcoef : ℝ := |c₁| with hBcoef
  have h_dom : Integrable
      (fun y : Fin n → ℝ => Aconst + Bcoef * ∑ i : Fin n, (y i - c.encoder m i) ^ 2) νm := by
    refine (integrable_const Aconst).add (Integrable.const_mul ?_ Bcoef)
    rw [hνm_def]
    refine integrable_finsetSum _ (fun i _ => ?_)
    have h_1d : Integrable (fun y : ℝ => (y - c.encoder m i) ^ 2)
        (gaussianReal (c.encoder m i) N) := by
      have h_id : Integrable (fun y : ℝ => y) (gaussianReal (c.encoder m i) N) := by
        simpa using (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 1).integrable (by norm_num)
      have h_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal (c.encoder m i) N) :=
        (memLp_id_gaussianReal (μ := c.encoder m i) (v := N) 2).integrable_sq
      have hrw : (fun y : ℝ => (y - c.encoder m i) ^ 2)
          = fun y => y ^ 2 - 2 * (c.encoder m i) * y + (c.encoder m i) ^ 2 := by funext y; ring
      rw [hrw]
      exact ((h_sq.sub (h_id.const_mul (2 * c.encoder m i))).add
        (integrable_const ((c.encoder m i) ^ 2)))
    exact integrable_comp_eval (μ := fun i : Fin n => gaussianReal (c.encoder m i) N)
      (i := i) h_1d
  refine Integrable.mono' h_dom ?_ ?_
  · exact (Real.measurable_log.comp (blockRealDensityInline_measurable c)).aestronglyMeasurable
  · filter_upwards with y
    have hDy_pos : 0 < blockRealDensityInline N c y := blockRealDensityInline_pos hN c y
    set S : ℝ := ∑ i : Fin n, (y i - c.encoder m i) ^ 2 with hS
    have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hc₁_nonpos : c₁ ≤ 0 := by rw [hc₁]; simp only [neg_nonpos]; positivity
    have h_upper : Real.log (blockRealDensityInline N c y) ≤ Real.log (∏ _i : Fin n, Bpeak) :=
      Real.log_le_log hDy_pos (hD_le y)
    have h_lower : Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S
        ≤ Real.log (blockRealDensityInline N c y) := by
      have hMinv_pos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
      have hprod_pos : (0 : ℝ) < ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i) :=
        Finset.prod_pos (fun i _ => gaussianPDFReal_pos _ _ _ hN)
      have h_log_prod : Real.log ((1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i))
          = Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S := by
        rw [Real.log_mul hMinv_pos.ne' hprod_pos.ne', Real.log_prod (fun i _ =>
          (gaussianPDFReal_pos (c.encoder m i) N (y i) hN).ne')]
        have h_each : ∀ i : Fin n, Real.log (gaussianPDFReal (c.encoder m i) N (y i))
            = c₀ + c₁ * (y i - c.encoder m i) ^ 2 := by
          intro i
          rw [InformationTheory.Shannon.log_gaussianPDFReal_eq (c.encoder m i) hN (y i), hc₀, hc₁]
          ring
        rw [Finset.sum_congr rfl (fun i _ => h_each i), hS, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
        ring
      calc Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S
          = Real.log ((1 / (M : ℝ)) * ∏ i : Fin n, gaussianPDFReal (c.encoder m i) N (y i)) :=
            h_log_prod.symm
        _ ≤ Real.log (blockRealDensityInline N c y) :=
            Real.log_le_log (mul_pos hMinv_pos hprod_pos) (hD_ge y)
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, ?_⟩
    · have hc₁S : c₁ * S = -(Bcoef * S) := by rw [hBcoef, abs_of_nonpos hc₁_nonpos]; ring
      have hlb : -(Aconst + Bcoef * S)
          ≤ Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀ + c₁ * S := by
        rw [hAconst, hc₁S]
        have h1 := neg_abs_le (Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀)
        have h2 := abs_nonneg (Real.log (∏ _i : Fin n, Bpeak))
        linarith
      exact le_trans hlb h_lower
    · have hub : Real.log (∏ _i : Fin n, Bpeak) ≤ Aconst + Bcoef * S := by
        rw [hAconst]
        have h1 := le_abs_self (Real.log (∏ _i : Fin n, Bpeak))
        have h2 := abs_nonneg (Real.log (1 / (M : ℝ)) + (n : ℝ) * c₀)
        have h3 : 0 ≤ Bcoef * S := mul_nonneg (abs_nonneg _) hS_nonneg
        linarith
      exact le_trans h_upper hub

/-- The proxy density `g z := ∏ᵢ gaussianPDF (encoder z.1 i) N (z.2 i)`, jointly measurable. -/
private noncomputable def blockProxy
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P)
    (z : (Fin M) × (Fin n → ℝ)) : ℝ≥0∞ :=
  ∏ i : Fin n, gaussianPDF (c.encoder z.1 i) N (z.2 i)

private lemma blockProxy_measurable
    {P : ℝ} (N : ℝ≥0) {M n : ℕ} (c : AwgnCode M n P) :
    Measurable (blockProxy N c) := by
  -- `Fin M` (input) is countable: measurability reduces to measurability in `y` for each `m`.
  refine measurable_from_prod_countable_right (fun m => ?_)
  show Measurable (fun y : Fin n → ℝ => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i))
  exact Finset.measurable_prod _ (fun i _ =>
    (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i))

/-- Per-fibre a.e. agreement: `(blockKernelInline m).rnDeriv volume =ᵐ blockProxy (m, ·)`. -/
private lemma blockProxy_ae
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    (fun y => ((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y)
      =ᵐ[(blockKernelInline N c) m] fun y => blockProxy N c (m, y) := by
  -- `blockKernelInline m = vol.withDensity (∏ᵢ gaussianPDF (encoder m i)(·i))`, so its
  -- rnDeriv =ᵐ[vol] that density; transport to `=ᵐ[blockKernelInline m]` since fibre ≪ vol.
  have hfibre_eq : (blockKernelInline N c) m
      = (MeasureTheory.volume : Measure (Fin n → ℝ)).withDensity
          (fun y => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    show Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) = _
    exact blockComponentInline_withDensity hN c m
  have h_dens_meas : Measurable (fun y : Fin n → ℝ =>
      ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) :=
    Finset.measurable_prod _ (fun i _ =>
      (measurable_gaussianPDF (c.encoder m i) N).comp (measurable_pi_apply i))
  have h_fibre_ac : (blockKernelInline N c) m ≪ (MeasureTheory.volume : Measure (Fin n → ℝ)) := by
    rw [hfibre_eq]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_rn_vol : ((blockKernelInline N c) m).rnDeriv (MeasureTheory.volume : Measure (Fin n → ℝ))
      =ᵐ[(MeasureTheory.volume : Measure (Fin n → ℝ))]
      (fun y => ∏ i : Fin n, gaussianPDF (c.encoder m i) N (y i)) := by
    conv_lhs => rw [hfibre_eq]
    exact Measure.rnDeriv_withDensity _ h_dens_meas
  filter_upwards [h_fibre_ac.ae_le h_rn_vol] with y hy
  simpa [blockProxy] using hy

/-- Fibre log-density integral identity: the proxy log-density integrates the same as the
rnDeriv log-density against the m-th fibre (used to feed `h_fibre_self`). -/
private lemma fibre_log_proxy_integral
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    ∫ y, Real.log (blockProxy N c (m, y)).toReal ∂((blockKernelInline N c) m)
      = ∫ y, Real.log
          (((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y).toReal
          ∂((blockKernelInline N c) m) := by
  refine integral_congr_ae ?_
  filter_upwards [blockProxy_ae hN c m] with y hy
  rw [hy]

/-- Per-Gaussian log-density integrability (mirror of
`ParallelGaussian.gaussianReal_logRnDeriv_integrable`, inaccessible downstream). -/
private lemma gaussianReal_logRnDeriv_integrable_inline (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun y => Real.log ((gaussianReal m v).rnDeriv volume y).toReal)
      (gaussianReal m v) := by
  have h_memLp : MemLp (fun y : ℝ => y - m) 2 (gaussianReal m v) :=
    (memLp_id_gaussianReal 2).sub (memLp_const m)
  have h_sq_int : Integrable (fun y => (y - m) ^ 2) (gaussianReal m v) := h_memLp.integrable_sq
  have h_rn : ∀ᵐ y ∂(gaussianReal m v),
      Real.log ((gaussianReal m v).rnDeriv volume y).toReal
        = -(1/2) * Real.log (2 * Real.pi * v) - (y - m) ^ 2 / (2 * v) := by
    have h_ac : gaussianReal m v ≪ volume := gaussianReal_absolutelyContinuous m hv
    filter_upwards [h_ac.ae_le (rnDeriv_gaussianReal m v)] with y hy
    rw [hy, toReal_gaussianPDF, log_gaussianPDFReal_eq m hv y]
  have h_affine_int : Integrable
      (fun y => -(1/2) * Real.log (2 * Real.pi * v) - (y - m) ^ 2 / (2 * v))
      (gaussianReal m v) :=
    (integrable_const _).sub (h_sq_int.div_const (2 * v))
  refine h_affine_int.congr ?_
  filter_upwards [h_rn] with y hy
  exact hy.symm

/-- Per-fibre log-density integrability: `log (rnDeriv (blockKernelInline m) vol)` is
integrable against the m-th product-Gaussian fibre `blockKernelInline m`. -/
private lemma integrable_log_fibre_rnDeriv
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y => Real.log (((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y).toReal)
      ((blockKernelInline N c) m) := by
  classical
  set νp := Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) with hνp
  have hfibre : (blockKernelInline N c) m = νp := rfl
  rw [hfibre]
  haveI : IsProbabilityMeasure νp := by rw [hνp]; infer_instance
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i => inferInstance
  -- `log (rnDeriv νp vol) =ᵐ[νp] ∑ᵢ log gaussianPDFReal (encoder m i) (·i)`
  set a : Fin n → ℝ → ℝ≥0∞ := fun i => (gaussianReal (c.encoder m i) N).rnDeriv volume with ha
  have ha_meas : ∀ i, Measurable (a i) := fun i => Measure.measurable_rnDeriv _ _
  have hac : ∀ i, gaussianReal (c.encoder m i) N ≪ (volume : Measure ℝ) :=
    fun i => gaussianReal_absolutelyContinuous (c.encoder m i) hN
  have hνp_ac : νp ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hνp, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have h_rn_pi : (νp.rnDeriv volume) =ᵐ[νp] fun z => ∏ i, a i (z i) := by
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (a i) = gaussianReal (c.encoder m i) N :=
      fun i => Measure.withDensity_rnDeriv_eq _ volume (hac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (a i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_wd : νp = (volume : Measure (Fin n → ℝ)).withDensity (fun z => ∏ i, a i (z i)) := by
      rw [hνp, ← (funext h_eq : (fun i => (volume : Measure ℝ).withDensity (a i))
          = fun i => gaussianReal (c.encoder m i) N)]
      rw [InformationTheory.Shannon.pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) ha_meas,
        volume_pi]
    have h_prod_meas : Measurable (fun z : Fin n → ℝ => ∏ i, a i (z i)) :=
      Finset.measurable_prod _ (fun i _ => (ha_meas i).comp (measurable_pi_apply i))
    have h_rn_vol : (νp.rnDeriv volume) =ᵐ[volume] fun z => ∏ i, a i (z i) := by
      conv_lhs => rw [h_pi_wd]
      exact Measure.rnDeriv_withDensity volume h_prod_meas
    exact hνp_ac.ae_le h_rn_vol
  have h_pos : ∀ i, ∀ᵐ z ∂νp, 0 < a i (z i) := by
    intro i
    have h1d : ∀ᵐ y ∂(gaussianReal (c.encoder m i) N), 0 < a i y := Measure.rnDeriv_pos (hac i)
    exact (Measure.quasiMeasurePreserving_eval (μ := fun i => gaussianReal (c.encoder m i) N) i).ae h1d
  have h_lt : ∀ i, ∀ᵐ z ∂νp, a i (z i) < ∞ := by
    intro i
    have h1d : ∀ᵐ y ∂(gaussianReal (c.encoder m i) N), a i y < ∞ :=
      (hac i).ae_le (Measure.rnDeriv_lt_top _ volume)
    exact (Measure.quasiMeasurePreserving_eval (μ := fun i => gaussianReal (c.encoder m i) N) i).ae h1d
  have h_log_split : (fun z => Real.log ((νp.rnDeriv volume z).toReal))
      =ᵐ[νp] fun z => ∑ i, Real.log ((a i (z i)).toReal) := by
    filter_upwards [h_rn_pi, eventually_countable_forall.mpr h_pos,
      eventually_countable_forall.mpr h_lt] with z hz hpos hlt
    rw [hz, ENNReal.toReal_prod, Real.log_prod]
    intro i _
    exact (ENNReal.toReal_pos (hpos i).ne' (hlt i).ne).ne'
  refine (Integrable.congr ?_ h_log_split.symm)
  refine integrable_finsetSum _ (fun i _ => ?_)
  -- each `log (a i (z i))` integrable against νp = pi gaussian via `integrable_comp_eval`
  have h_1d : Integrable (fun y => Real.log ((a i y).toReal)) (gaussianReal (c.encoder m i) N) :=
    gaussianReal_logRnDeriv_integrable_inline (c.encoder m i) hN
  rw [hνp]
  exact integrable_comp_eval (μ := fun i : Fin n => gaussianReal (c.encoder m i) N) (i := i) h_1d

/-- Product entropy additivity (mirror of `ParallelGaussian.jointDifferentialEntropyPi_pi_eq_sum`,
inaccessible downstream): `h(∏ᵢ νᵢ) = ∑ᵢ h(νᵢ)` for component-`≪ volume`, log-density-integrable
factors. -/
private lemma jointDifferentialEntropyPi_pi_eq_sum_inline {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (h_ac : ∀ i, μ i ≪ (volume : Measure ℝ))
    (h_int : ∀ i, Integrable (fun y => Real.log ((μ i).rnDeriv volume y).toReal) (μ i)) :
    InformationTheory.Shannon.jointDifferentialEntropyPi (Measure.pi μ)
      = ∑ i, InformationTheory.Shannon.differentialEntropy (μ i) := by
  classical
  set Pm := Measure.pi μ with hP
  set a : Fin n → ℝ → ℝ≥0∞ := fun i => (μ i).rnDeriv volume with ha_def
  have ha_meas : ∀ i, Measurable (a i) := fun i => Measure.measurable_rnDeriv (μ i) volume
  have hP_ac : Pm ≪ (volume : Measure (Fin n → ℝ)) := by
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (a i) = μ i :=
      fun i => Measure.withDensity_rnDeriv_eq (μ i) volume (h_ac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (a i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_eq : Measure.pi μ
        = (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
            (fun z => ∏ i, a i (z i)) := by
      rw [← (funext h_eq : (fun i => (volume : Measure ℝ).withDensity (a i)) = μ)]
      exact InformationTheory.Shannon.pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) ha_meas
    rw [hP, h_pi_eq, volume_pi]
    exact withDensity_absolutelyContinuous _ _
  have h_step1 : InformationTheory.Shannon.jointDifferentialEntropyPi Pm
      = -∫ z, Real.log ((Pm.rnDeriv volume z).toReal) ∂Pm := by
    rw [InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg hP_ac, neg_neg]; rfl
  have h_rn_pi : (Pm.rnDeriv volume) =ᵐ[Pm] fun z => ∏ i, a i (z i) := by
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (a i) = μ i :=
      fun i => Measure.withDensity_rnDeriv_eq (μ i) volume (h_ac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (a i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_wd : Pm = (volume : Measure (Fin n → ℝ)).withDensity (fun z => ∏ i, a i (z i)) := by
      rw [hP, ← (funext h_eq : (fun i => (volume : Measure ℝ).withDensity (a i)) = μ)]
      rw [InformationTheory.Shannon.pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) ha_meas,
        volume_pi]
    have h_prod_meas : Measurable (fun z : Fin n → ℝ => ∏ i, a i (z i)) :=
      Finset.measurable_prod _ (fun i _ => (ha_meas i).comp (measurable_pi_apply i))
    have h_rn_vol : (Pm.rnDeriv volume) =ᵐ[volume] fun z => ∏ i, a i (z i) := by
      conv_lhs => rw [h_pi_wd]
      exact Measure.rnDeriv_withDensity volume h_prod_meas
    exact hP_ac.ae_le h_rn_vol
  have h_pos : ∀ i, ∀ᵐ z ∂Pm, 0 < a i (z i) := by
    intro i
    have h1d : ∀ᵐ y ∂(μ i), 0 < a i y := Measure.rnDeriv_pos (h_ac i)
    exact (Measure.quasiMeasurePreserving_eval (μ := μ) i).ae h1d
  have h_lt : ∀ i, ∀ᵐ z ∂Pm, a i (z i) < ∞ := by
    intro i
    have h1d : ∀ᵐ y ∂(μ i), a i y < ∞ := (h_ac i).ae_le (Measure.rnDeriv_lt_top (μ i) volume)
    exact (Measure.quasiMeasurePreserving_eval (μ := μ) i).ae h1d
  have h_log_split : (fun z => Real.log ((Pm.rnDeriv volume z).toReal))
      =ᵐ[Pm] fun z => ∑ i, Real.log ((a i (z i)).toReal) := by
    filter_upwards [h_rn_pi, eventually_countable_forall.mpr h_pos,
      eventually_countable_forall.mpr h_lt] with z hz hpos hlt
    rw [hz, ENNReal.toReal_prod, Real.log_prod]
    intro i _
    have : (0 : ℝ) < (a i (z i)).toReal := ENNReal.toReal_pos (hpos i).ne' (hlt i).ne
    exact this.ne'
  have h_int_P : ∀ i, Integrable (fun z => Real.log ((a i (z i)).toReal)) Pm := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) Pm (μ i) := by
      rw [hP]; exact MeasureTheory.measurePreserving_eval μ i
    have hcomp : (fun z : Fin n → ℝ => Real.log ((a i (z i)).toReal))
        = (fun y => Real.log ((a i y).toReal)) ∘ (Function.eval i) := rfl
    rw [hcomp]
    exact (hmp.integrable_comp
      ((((ha_meas i).ennreal_toReal.log).aestronglyMeasurable))).mpr (h_int i)
  have h_marg : ∀ i, (∫ z, Real.log ((a i (z i)).toReal) ∂Pm)
      = -InformationTheory.Shannon.differentialEntropy (μ i) := by
    intro i
    have hmp : MeasurePreserving (Function.eval i) Pm (μ i) := by
      rw [hP]; exact MeasureTheory.measurePreserving_eval μ i
    have hGmeas : AEStronglyMeasurable (fun y => Real.log ((a i y).toReal)) (μ i) :=
      ((ha_meas i).ennreal_toReal.log).aestronglyMeasurable
    have h_map : (∫ z, Real.log ((a i (z i)).toReal) ∂Pm)
        = ∫ y, Real.log ((a i y).toReal) ∂(μ i) := by
      rw [← hmp.map_eq]
      exact (MeasureTheory.integral_map (measurable_pi_apply i).aemeasurable
        (by rw [hmp.map_eq]; exact hGmeas)).symm
    rw [h_map, ha_def, InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg (h_ac i)]
    rfl
  rw [h_step1, integral_congr_ae h_log_split, integral_finsetSum _ (fun i _ => h_int_P i)]
  rw [show (∑ i, ∫ z, Real.log ((a i (z i)).toReal) ∂Pm)
        = ∑ i, -InformationTheory.Shannon.differentialEntropy (μ i) from
    Finset.sum_congr rfl (fun i _ => h_marg i)]
  rw [Finset.sum_neg_distrib, neg_neg]

/-- Fibre neg-entropy value: `∫ y, log (rnDeriv (blockKernelInline m) vol) ∂(blockKernelInline m)
= -n·h(gaussianReal 0 N)`. -/
private lemma fibre_neg_entropy
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} (c : AwgnCode M n P) (m : Fin M) :
    ∫ y, Real.log
        (((blockKernelInline N c) m).rnDeriv MeasureTheory.volume y).toReal
        ∂((blockKernelInline N c) m)
      = -((n : ℝ) * InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N)) := by
  -- the m-th fibre is the product Gaussian `pi (gaussianReal (encoder m i) N)`
  have hfibre : (blockKernelInline N c) m
      = Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) := rfl
  rw [hfibre]
  set νp := Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) with hνp
  haveI : IsProbabilityMeasure νp := by rw [hνp]; infer_instance
  have h_ac : νp ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hνp, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  -- `jointDifferentialEntropyPi νp = ∑ᵢ h(gaussian (encoder m i) N) = n·h(gaussian 0 N)`
  have h_sum : InformationTheory.Shannon.jointDifferentialEntropyPi νp
      = ∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
          (gaussianReal (c.encoder m i) N) := by
    rw [hνp]
    exact jointDifferentialEntropyPi_pi_eq_sum_inline
      (fun i => gaussianReal (c.encoder m i) N)
      (fun i => gaussianReal_absolutelyContinuous (c.encoder m i) hN)
      (fun i => gaussianReal_logRnDeriv_integrable_inline (c.encoder m i) hN)
  have h_inv : ∀ i : Fin n,
      InformationTheory.Shannon.differentialEntropy (gaussianReal (c.encoder m i) N)
        = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
    intro i
    rw [InformationTheory.Shannon.differentialEntropy_gaussianReal (c.encoder m i) hN,
      InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hN]
  rw [show (∫ y, Real.log (νp.rnDeriv volume y).toReal ∂νp)
        = -InformationTheory.Shannon.jointDifferentialEntropyPi νp from by
    rw [InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg h_ac]; rfl]
  rw [h_sum, Finset.sum_congr rfl (fun i _ => h_inv i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- `count = ∑ₐ dirac a` on a `Fintype` (mirror of `count_eq_finset_sum_dirac`). -/
private lemma count_eq_finset_sum_dirac_inline (α : Type*) [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (Measure.count : Measure α) = ∑ a : α, Measure.dirac a := by
  have h_one : ∀ a : α, (Measure.count : Measure α) {a} = 1 := fun a =>
    Measure.count_singleton a
  have h_sum : Measure.sum (fun a : α => Measure.dirac a)
      = (Measure.count : Measure α) := by
    have h := Measure.sum_smul_dirac (μ := (Measure.count : Measure α))
    simp_rw [h_one, one_smul] at h
    exact h
  rw [← h_sum, Measure.sum_fintype]

/-- **Elementary discrete-input factorization** (mixture-of-diracs):
`converseJointInline = msgLawInline ⊗ₘ blockKernelInline`. -/
private lemma converseJointInline_eq_compProd
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    converseJointInline h_meas c = msgLawInline M ⊗ₘ blockKernelInline N c := by
  classical
  unfold converseJointInline msgLawInline
  rw [Measure.compProd_smul_left]
  congr 1
  rw [count_eq_finset_sum_dirac_inline (Fin M), ← Measure.sum_fintype
        (fun a : Fin M => Measure.dirac a),
    Measure.compProd_sum_left, Measure.sum_fintype]
  symm
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show (Measure.dirac m) ⊗ₘ blockKernelInline N c
        = (Measure.dirac m).prod (blockKernelInline N c m) by
      ext s hs
      rw [Measure.dirac_compProd_apply hs, Measure.dirac_prod,
        Measure.map_apply measurable_prodMk_left hs]]
  refine congrArg ((Measure.dirac m).prod) ?_
  show Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))
      = Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)
  refine congrArg Measure.pi ?_
  funext i
  rw [awgnChannel_apply]

/-- **Output law identification**: `outputDistribution msgLawInline blockKernelInline
= blockYLawInline`. -/
private lemma outputDistribution_msgLawInline_eq
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    ChannelCoding.outputDistribution (msgLawInline M) (blockKernelInline N c)
      = blockYLawInline h_meas c := by
  -- `outputDistribution p W = (p ⊗ₘ W).snd = (p ⊗ₘ W).map snd`
  show (msgLawInline M ⊗ₘ blockKernelInline N c).map Prod.snd = blockYLawInline h_meas c
  rw [← converseJointInline_eq_compProd h_meas c]
  rfl

/-- `mutualInfo μ fst snd = mutualInfoOfChannel msgLawInline blockKernelInline`. -/
private lemma mutualInfo_fst_snd_eq_channel
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd
      = ChannelCoding.mutualInfoOfChannel (msgLawInline M) (blockKernelInline N c) := by
  rw [ChannelCoding.mutualInfoOfChannel_eq_mutualInfo_prod]
  -- `jointDistribution msgLaw blockKernel = msgLaw ⊗ₘ blockKernel = converseJointInline`
  congr 1
  rw [ChannelCoding.jointDistribution_def, ← converseJointInline_eq_compProd h_meas c]

/-- **Deterministic DPI**: `I(X^n;Y^n) ≤ I(W;Y^n)` (`X^n = encoder ∘ fst` is a
post-processing of `W = fst`). -/
private lemma mutualInfo_encoder_le_fst
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (converseJointInline h_meas c) (fun ω => c.encoder ω.1) Prod.snd
      ≤ mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd := by
  set μ := converseJointInline h_meas c with hμ
  have hfst : Measurable (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) := measurable_fst
  have hsnd : Measurable (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := measurable_snd
  have henc : Measurable (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1) :=
    (measurable_of_countable c.encoder).comp measurable_fst
  -- `encoder ∘ fst = encoder ∘ (id) ∘ fst`; post-process the FIRST argument via comm + 2nd DPI.
  rw [mutualInfo_comm μ (fun ω => c.encoder ω.1) Prod.snd henc hsnd,
    mutualInfo_comm μ Prod.fst Prod.snd hfst hsnd]
  -- now: `I(Y; encoder∘fst) ≤ I(Y; fst)`; `encoder∘fst = encoder ∘ fst`
  have h_comp : (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1)
      = c.encoder ∘ (Prod.fst : Fin M × (Fin n → ℝ) → Fin M) := rfl
  rw [h_comp]
  exact mutualInfo_le_of_postprocess μ Prod.snd Prod.fst hsnd hfst
    (measurable_of_countable c.encoder)

/-- `converseJointInline.map fst = msgLawInline` (uniform message marginal). -/
private lemma converseJointInline_map_fst_eq_msgLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (converseJointInline h_meas c).map (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      = msgLawInline M := by
  classical
  unfold converseJointInline msgLawInline
  rw [Measure.map_smul, Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      measurable_fst.aemeasurable]
  rw [count_eq_finset_sum_dirac_inline (Fin M)]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- Marginals product `(μ.map fst).prod (μ.map snd) = msgLaw ⊗ₘ const blockYLaw`. -/
private lemma converseJointInline_prod_marginals_eq
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    ((converseJointInline h_meas c).map Prod.fst).prod ((converseJointInline h_meas c).map Prod.snd)
      = msgLawInline M ⊗ₘ Kernel.const (Fin M) (blockYLawInline h_meas c) := by
  rw [converseJointInline_map_fst_eq_msgLaw h_meas c,
    show (converseJointInline h_meas c).map Prod.snd = blockYLawInline h_meas c from rfl,
    Measure.compProd_const]

/-- Per-fibre log-likelihood-ratio integrability:
`log (νₘ.rnDeriv blockYLaw)` integrable against the m-th block component `νₘ`. -/
private lemma integrable_log_component_rnDeriv_blockYLawInline
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (m : Fin M) :
    Integrable
      (fun y => Real.log
        ((Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)).rnDeriv
          (blockYLawInline h_meas c) y).toReal)
      (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)) := by
  classical
  set νm := Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) with hνm
  set q := blockYLawInline h_meas c with hq
  haveI : ∀ i, IsProbabilityMeasure (gaussianReal (c.encoder m i) N) := fun i => inferInstance
  haveI hνm_prob : IsProbabilityMeasure νm := by rw [hνm]; infer_instance
  haveI hq_prob : IsProbabilityMeasure q := by rw [hq]; infer_instance
  have hνm_q : νm ≪ q := by rw [hνm, hq]; exact blockComponentInline_ac_blockYLaw hN h_meas c m
  have hq_vol : q ≪ (volume : Measure (Fin n → ℝ)) := by rw [hq]; exact blockYLawInline_ac_volume hN h_meas c
  have hνm_vol : νm ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hνm, blockComponentInline_withDensity hN c m]
    exact MeasureTheory.withDensity_absolutelyContinuous _ _
  -- `log(νₘ/q) =ᵐ[νₘ] log(νₘ/vol) − log(q/vol)`; both terms integrable.
  have h_split : (fun y => Real.log ((νm.rnDeriv q y).toReal))
      =ᵐ[νm] (fun y => Real.log ((νm.rnDeriv volume y).toReal)
                - Real.log ((q.rnDeriv volume y).toReal)) :=
    ChannelCoding.log_rnDeriv_split_gen hνm_q hq_vol
  refine Integrable.congr ?_ h_split.symm
  -- term A: `log(νₘ.rnDeriv vol)` integrable against νₘ (product-Gaussian log-density)
  have hA : Integrable (fun y => Real.log ((νm.rnDeriv volume y).toReal)) νm := by
    rw [hνm]; exact integrable_log_fibre_rnDeriv hN c m
  -- term B: `log(q.rnDeriv vol)` integrable against νₘ (= component output log-density)
  have hB : Integrable (fun y => Real.log ((q.rnDeriv volume y).toReal)) νm := by
    rw [hνm, hq]; exact integrable_log_blockYLawInline_on_component hN h_meas c m
  exact hA.sub hB

/-- `I(W;Y^n) ≠ ∞` (finiteness, so `.toReal` is monotone). -/
private lemma mutualInfo_fst_snd_ne_top
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd ≠ ∞ := by
  classical
  rw [mutualInfo]
  have h_joint : (converseJointInline h_meas c).map
      (fun ω : Fin M × (Fin n → ℝ) => (ω.1, ω.2)) = msgLawInline M ⊗ₘ blockKernelInline N c := by
    rw [show (fun ω : Fin M × (Fin n → ℝ) => (ω.1, ω.2)) = id from rfl, Measure.map_id]
    exact converseJointInline_eq_compProd h_meas c
  rw [h_joint, converseJointInline_prod_marginals_eq h_meas c]
  refine klDiv_ne_top ?_ ?_
  · -- AC: msgLaw ⊗ₘ K ≪ msgLaw ⊗ₘ const blockY
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    filter_upwards with m
    show blockKernelInline N c m ≪ (Kernel.const (Fin M) (blockYLawInline h_meas c)) m
    rw [Kernel.const_apply]
    show Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c
    exact blockComponentInline_ac_blockYLaw hN h_meas c m
  · -- integrable llr
    set K := blockKernelInline N c with hK
    set ηc := Kernel.const (Fin M) (blockYLawInline h_meas c) with hηc
    have h_ac : msgLawInline M ⊗ₘ K ≪ msgLawInline M ⊗ₘ ηc := by
      refine Measure.AbsolutelyContinuous.compProd_right ?_
      filter_upwards with m
      rw [hηc, Kernel.const_apply]
      show Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c
      exact blockComponentInline_ac_blockYLaw hN h_meas c m
    have h_llr_ae : (fun p => llr (msgLawInline M ⊗ₘ K) (msgLawInline M ⊗ₘ ηc) p)
        =ᵐ[msgLawInline M ⊗ₘ K]
        (fun p : Fin M × (Fin n → ℝ) => Real.log ((K.rnDeriv ηc p.1 p.2)).toReal) := by
      have h1 : (msgLawInline M ⊗ₘ K).rnDeriv (msgLawInline M ⊗ₘ ηc)
          =ᵐ[msgLawInline M ⊗ₘ K] fun p => K.rnDeriv ηc p.1 p.2 :=
        h_ac.ae_le (ChannelCoding.rnDeriv_compProd_fibre h_ac)
      simp only [llr_def]
      filter_upwards [h1] with p hp1
      rw [hp1]
    refine Integrable.congr ?_ h_llr_ae.symm
    refine (Measure.integrable_compProd_iff ?_).mpr ⟨?_, ?_⟩
    · exact ((Kernel.measurable_rnDeriv K ηc).ennreal_toReal.log).aestronglyMeasurable
    · filter_upwards with m
      have h_fibre_ae : (fun y => Real.log ((K.rnDeriv ηc m y)).toReal)
          =ᵐ[K m] (fun y => Real.log (((K m).rnDeriv (blockYLawInline h_meas c) y)).toReal) := by
        have hKm_blockY : K m ≪ blockYLawInline h_meas c := by
          rw [hK]
          show Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) ≪ blockYLawInline h_meas c
          exact blockComponentInline_ac_blockYLaw hN h_meas c m
        have h_meas_eq : K m ≪ ηc m := by rw [hηc, Kernel.const_apply]; exact hKm_blockY
        filter_upwards [h_meas_eq.ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := K) (η := ηc) (a := m))] with y hy
        rw [hy]; simp only [hηc, Kernel.const_apply]
      refine Integrable.congr ?_ h_fibre_ae.symm
      show Integrable
        (fun y => Real.log
          ((Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N)).rnDeriv
            (blockYLawInline h_meas c) y).toReal)
        (Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N))
      exact integrable_log_component_rnDeriv_blockYLawInline hN h_meas c m
    · exact Integrable.of_finite

/-- **Block MI decomposition**: `I(W;Y^n).toReal = h(Y^n) − n·h(noise)`. -/
private lemma blockMI_decomp
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd).toReal
      = InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c)
        - (n : ℝ) * InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  classical
  set p := msgLawInline M with hp
  set W := blockKernelInline N c with hW
  -- output distribution identification
  have hq_eq : ChannelCoding.outputDistribution p W = blockYLawInline h_meas c :=
    outputDistribution_msgLawInline_eq h_meas c
  -- regularity (in the generic decomp's `outputDistribution` form)
  have hWx_q : ∀ m, W m ≪ ChannelCoding.outputDistribution p W := by
    intro m; rw [hq_eq]
    exact blockComponentInline_ac_blockYLaw hN h_meas c m
  have hq_ref : ChannelCoding.outputDistribution p W ≪ (volume : Measure (Fin n → ℝ)) := by
    rw [hq_eq]; exact blockYLawInline_ac_volume hN h_meas c
  haveI : (ChannelCoding.outputDistribution p W).HaveLebesgueDecomposition
      (volume : Measure (Fin n → ℝ)) := by infer_instance
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod (ChannelCoding.outputDistribution p W) := by
    rw [← Measure.compProd_const]
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    exact Filter.Eventually.of_forall (fun m => by
      simpa only [Kernel.const_apply] using hWx_q m)
  -- proxy
  set g : (Fin M) × (Fin n → ℝ) → ℝ≥0∞ := blockProxy N c with hg
  have hg_meas : Measurable g := blockProxy_measurable N c
  have hg_ae : ∀ m, (fun y => (W m).rnDeriv volume y) =ᵐ[W m] fun y => g (m, y) :=
    fun m => blockProxy_ae hN c m
  -- compProd-level integrabilities (msgLaw is finite-support → norm-integrability free)
  have h_int_fibre_self : ∀ m, Integrable (fun y => Real.log (g (m, y)).toReal) (W m) := by
    intro m
    refine (integrable_log_fibre_rnDeriv hN c m).congr ?_
    filter_upwards [hg_ae m] with y hy
    rw [hy]
  have h_int_fibre : Integrable (fun z : (Fin M) × (Fin n → ℝ) => Real.log (g z).toReal) (p ⊗ₘ W) := by
    rw [Measure.integrable_compProd_iff ((hg_meas.ennreal_toReal.log).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun m => h_int_fibre_self m), ?_⟩
    -- `p = msgLaw` is a finite measure on the finite type `Fin M` → integrable for free
    exact Integrable.of_finite
  have h_out_self : Integrable
      (fun y => Real.log ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal)
      (ChannelCoding.outputDistribution p W) := by
    rw [hq_eq]
    -- integrate the fixed function against the mixture measure (rewrite only the measure)
    set F : (Fin n → ℝ) → ℝ :=
      fun y => Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal with hF
    have h_mix : blockYLawInline h_meas c
        = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ •
            ∑ m : Fin M, Measure.pi (fun i : Fin n => gaussianReal (c.encoder m i) N) :=
      blockYLawInline_eq_mixture h_meas c
    rw [h_mix]
    have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
      rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
    refine Integrable.smul_measure ?_ hM_inv_ne_top
    refine integrable_finsetSum_measure.mpr (fun m _ => ?_)
    exact integrable_log_blockYLawInline_on_component hN h_meas c m
  have h_int_out : Integrable
      (fun z : (Fin M) × (Fin n → ℝ) => Real.log
          ((ChannelCoding.outputDistribution p W).rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    set ψ : (Fin n → ℝ) → ℝ := fun y => Real.log
      ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal with hψ
    have hψ_meas : Measurable ψ :=
      (Real.measurable_log.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal)
    show Integrable (fun z : (Fin M) × (Fin n → ℝ) => ψ z.2) (p ⊗ₘ W)
    rw [Measure.integrable_compProd_iff
      (f := fun z : (Fin M) × (Fin n → ℝ) => ψ z.2)
      ((hψ_meas.comp measurable_snd).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun m => ?_), ?_⟩
    · -- per-fibre: `ψ` integrable against `W m = pi gaussian`; via output id + on-component
      have : Integrable
          (fun y => Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal) (W m) :=
        integrable_log_blockYLawInline_on_component hN h_meas c m
      refine this.congr ?_
      filter_upwards with y; rw [hψ, hq_eq]
    · exact Integrable.of_finite
  have h_fibre_self : ∀ m, ∫ y, Real.log (g (m, y)).toReal ∂(W m)
      = ∫ y, Real.log ((W m).rnDeriv volume y).toReal ∂(W m) := fun m => fibre_log_proxy_integral hN c m
  -- apply the generic decomposition
  rw [mutualInfo_fst_snd_eq_channel h_meas c]
  rw [ChannelCoding.mutualInfoOfChannel_toReal_eq_log_density_sub
    (volume : Measure (Fin n → ℝ)) hWx_q hq_ref h_joint_ac g hg_meas hg_ae
    h_int_fibre h_int_out h_fibre_self h_out_self]
  -- fibre term: `∫ m, (∫ y, log(rnDeriv (W m) vol) ∂(W m)) ∂msgLaw = -n·h(noise)`
  have h_fibre_val : (∫ m, (∫ y, Real.log ((W m).rnDeriv volume y).toReal ∂(W m)) ∂p)
      = -((n : ℝ) * InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall (fun m => fibre_neg_entropy hN c m)),
      integral_const, probReal_univ, one_smul]
  -- output term: `∫ y, log(rnDeriv blockYLaw vol) ∂blockYLaw = -jointDiff`
  have h_out_val : (∫ y, Real.log
        ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal
        ∂(ChannelCoding.outputDistribution p W))
      = -InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c) := by
    rw [hq_eq, InformationTheory.Shannon.integral_log_rnDeriv_self_eq_neg
      (blockYLawInline_ac_volume hN h_meas c)]
    rfl
  rw [h_fibre_val, h_out_val]
  ring

/-- Joint measurability of `(x, y) ↦ gaussianPDF x N y` (mean × point). -/
private lemma gaussianPDF_joint_measurable (N : ℝ≥0) :
    Measurable (fun p : ℝ × ℝ => gaussianPDF p.1 N p.2) := by
  unfold gaussianPDF
  refine ENNReal.measurable_ofReal.comp ?_
  unfold gaussianPDFReal
  refine Measurable.mul measurable_const ?_
  refine Real.measurable_exp.comp ?_
  refine Measurable.div ?_ measurable_const
  refine (Measurable.pow ?_ measurable_const).neg
  exact (measurable_snd.sub measurable_fst)

/-- Per-letter input law `μ.map (encoder · i)` (discrete, real-valued). -/
private noncomputable def perLetterInputLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) : Measure ℝ :=
  (converseJointInline h_meas c).map (fun ω => c.encoder ω.1 i)

private instance perLetterInputLaw_isProb
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    IsProbabilityMeasure (perLetterInputLaw h_meas c i) := by
  rw [perLetterInputLaw]
  exact Measure.isProbabilityMeasure_map
    (((measurable_of_countable (fun m : Fin M => c.encoder m i)).comp measurable_fst).aemeasurable)

/-- `perLetterInputLaw_i = (1/M) • ∑ₘ δ_{encoder m i}` (mixture-of-diracs form). -/
private lemma perLetterInputLaw_eq_mixture
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    perLetterInputLaw h_meas c i
      = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • ∑ m : Fin M, Measure.dirac (c.encoder m i) := by
  classical
  unfold perLetterInputLaw converseJointInline
  have henc_i : Measurable (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1 i) :=
    (measurable_of_countable (fun m : Fin M => c.encoder m i)).comp measurable_fst
  rw [Measure.map_smul, Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      henc_i.aemeasurable]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  -- `((δ_m).prod ν).map (fun ω => encoder ω.1 i) = (δ_m).map (encoder · i) = δ_{encoder m i}`
  rw [show (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1 i)
        = (fun a : Fin M => c.encoder a i) ∘ Prod.fst from rfl,
    ← Measure.map_map (measurable_of_countable _) measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul, MeasureTheory.Measure.map_dirac' (measurable_of_countable _)]

/-- **Per-letter X-input factorization** (mixture-of-diracs, holds with collisions):
`μ.map (fun ω => (encoder ω.1 i, ω.2 i)) = perLetterInputLaw_i ⊗ₘ awgnChannel`. -/
private lemma perLetter_map_eq_compProd
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (converseJointInline h_meas c).map (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i))
      = perLetterInputLaw h_meas c i ⊗ₘ awgnChannel N h_meas := by
  classical
  -- RHS: explicit mixture of diracs ⊗ₘ awgnChannel = (1/M) ∑ₘ δ_{encoder m i} ⊗ awgn
  rw [perLetterInputLaw_eq_mixture h_meas c i, Measure.compProd_smul_left]
  rw [← Measure.sum_fintype (fun m : Fin M => Measure.dirac (c.encoder m i)),
    Measure.compProd_sum_left, Measure.sum_fintype, Fintype.card_fin]
  -- LHS: distribute the map over the mixture
  unfold converseJointInline
  have hmap_fn : Measurable (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i)) :=
    ((measurable_of_countable (fun m : Fin M => c.encoder m i)).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  rw [Measure.map_smul, Measure.map_finset_sum (s := Finset.univ)
      (m := fun m => (Measure.dirac m).prod
        (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j))))
      hmap_fn.aemeasurable]
  have h_per : ∀ m : Fin M,
      ((Measure.dirac m).prod
          (Measure.pi (fun j : Fin n => awgnChannel N h_meas (c.encoder m j)))).map
            (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i))
        = (Measure.dirac (c.encoder m i)) ⊗ₘ awgnChannel N h_meas := by
    intro m
    -- per-message: `((δ_m).prod (pi gaussian)).map (encoder·i, ·.2 i) = δ_{encoder m i} ⊗ₘ awgn`
    rw [show (Measure.dirac (c.encoder m i)) ⊗ₘ awgnChannel N h_meas
          = (Measure.dirac (c.encoder m i)).prod (awgnChannel N h_meas (c.encoder m i)) by
        ext s hs
        rw [Measure.dirac_compProd_apply hs, Measure.dirac_prod,
          Measure.map_apply measurable_prodMk_left hs]]
    -- LHS per-message
    rw [show (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i))
          = Prod.map (fun a : Fin M => c.encoder a i) (fun y : Fin n → ℝ => y i) from rfl]
    rw [← Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_pi_apply i)]
    rw [MeasureTheory.Measure.map_dirac' (measurable_of_countable _)]
    congr 1
    -- `(pi (gaussian (encoder m j))).map (·i) = gaussian (encoder m i) = awgnChannel (encoder m i)`
    rw [Measure.pi_map_eval]
    have h_prod_one : (∏ j ∈ Finset.univ.erase i,
        (awgnChannel N h_meas (c.encoder m j)) Set.univ) = 1 := by
      refine Finset.prod_eq_one (fun j _ => ?_)
      rw [awgnChannel_apply]; exact measure_univ
    rw [h_prod_one, one_smul, awgnChannel_apply]
  rw [Finset.sum_congr rfl (fun m _ => h_per m), Fintype.card_fin]

/-- Positivity of the per-letter mixture density (single full-support component suffices). -/
private lemma perLetterMixtureDensity_pos
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) {M n : ℕ} [NeZero M] (c : AwgnCode M n P)
    (i : Fin n) (y : ℝ) :
    0 < (perLetterMixtureDensity N c i y).toReal := by
  classical
  obtain ⟨m₀⟩ : Nonempty (Fin M) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne M)⟩⟩
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have h_ne_top : perLetterMixtureDensity N c i y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (perLetterMixtureDensity_le_sup N c i hM_pos y)
  rw [ENNReal.toReal_pos_iff]
  refine ⟨?_, lt_of_le_of_ne le_top h_ne_top⟩
  unfold perLetterMixtureDensity
  refine ENNReal.mul_pos ?_ ?_
  · simp only [ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.natCast_ne_top M
  · -- `∑ₘ gaussianPDF ... ≠ 0` (single component positive)
    have h_comp_pos : 0 < gaussianPDF (c.encoder m₀ i) N y := by
      rw [gaussianPDF, ENNReal.ofReal_pos]
      exact gaussianPDFReal_pos (c.encoder m₀ i) N y hN
    refine (lt_of_lt_of_le h_comp_pos (Finset.single_le_sum
      (f := fun m => gaussianPDF (c.encoder m i) N y) (fun m _ => zero_le')
      (Finset.mem_univ m₀))).ne'

/-- `perLetterYLaw_i ≪ volume` (mixture of full-support Gaussians). -/
private lemma perLetterLaw_ac_volume
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (converseJointInline h_meas c).map (fun ω => ω.2 i) ≪ (volume : Measure ℝ) := by
  rw [perLetterLaw_withDensity h_meas c i (Nat.pos_of_ne_zero (NeZero.ne M)) hN]
  exact MeasureTheory.withDensity_absolutelyContinuous _ _

/-- `volume ≪ perLetterYLaw_i` (mixture density everywhere positive). -/
private lemma volume_ac_perLetterLaw
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (volume : Measure ℝ) ≪ (converseJointInline h_meas c).map (fun ω => ω.2 i) := by
  rw [perLetterLaw_withDensity h_meas c i (Nat.pos_of_ne_zero (NeZero.ne M)) hN]
  refine withDensity_absolutelyContinuous'
    (perLetterMixtureDensity_measurable N c i).aemeasurable ?_
  refine Filter.Eventually.of_forall (fun y => ?_)
  have := perLetterMixtureDensity_pos hN c i y
  simp only [ne_eq]
  intro h0
  rw [h0] at this; simp at this

/-- **Marginal identification**: `blockYLawInline.map (· i) = (converseJointInline).map (·.2 i)`
= the per-letter law `Y_i`. -/
private lemma blockYLawInline_map_eval
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} (c : AwgnCode M n P) (i : Fin n) :
    (blockYLawInline h_meas c).map (fun y => y i)
      = (converseJointInline h_meas c).map (fun ω => ω.2 i) := by
  show ((converseJointInline h_meas c).map Prod.snd).map (fun y => y i)
      = (converseJointInline h_meas c).map (fun ω => ω.2 i)
  rw [Measure.map_map (measurable_pi_apply i) measurable_snd]
  rfl

/-- Per-letter MI = channel MI: `mutualInfo μ X_i Y_i = mutualInfoOfChannel inputLaw_i awgn`. -/
private lemma perLetterMI_eq_channel
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    mutualInfo (converseJointInline h_meas c)
        (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)
      = ChannelCoding.mutualInfoOfChannel (perLetterInputLaw h_meas c i) (awgnChannel N h_meas) := by
  classical
  set μ := converseJointInline h_meas c with hμ
  set p := perLetterInputLaw h_meas c i with hp
  set W := awgnChannel N h_meas with hW
  have hX_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1 i) :=
    (measurable_of_countable (fun m : Fin M => c.encoder m i)).comp measurable_fst
  have hY_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hpair_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i)) :=
    hX_meas.prodMk hY_meas
  -- `mutualInfoOfChannel = klDiv (p ⊗ₘ W) (p.prod (outputDistribution p W))`
  rw [ChannelCoding.mutualInfoOfChannel_def, ChannelCoding.jointDistribution_def]
  -- `mutualInfo μ X_i Y_i = klDiv (μ.map (X_i,Y_i)) ((μ.map X_i).prod (μ.map Y_i))`
  unfold mutualInfo
  -- joint: `μ.map (X_i,Y_i) = p ⊗ₘ W`
  have h_joint : μ.map (fun ω => (c.encoder ω.1 i, ω.2 i)) = p ⊗ₘ W := by
    rw [hμ, hp, hW]; exact perLetter_map_eq_compProd h_meas c i
  -- input marginal: `μ.map X_i = p`
  have h_in : μ.map (fun ω => c.encoder ω.1 i) = p := by rw [hp, perLetterInputLaw]
  -- output marginal: `μ.map Y_i = outputDistribution p W`
  have h_out : μ.map (fun ω => ω.2 i) = ChannelCoding.outputDistribution p W := by
    show μ.map (fun ω => ω.2 i) = (p ⊗ₘ W).map Prod.snd
    rw [← h_joint, Measure.map_map measurable_snd hpair_meas]
    rfl
  rw [h_joint, h_in, h_out]

/-- Any measurable real function is integrable against the finite-support `perLetterInputLaw`
(a `(1/M)`-weighted sum of `M` Diracs). -/
private lemma integrable_of_perLetterInputLaw
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n)
    {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f (perLetterInputLaw h_meas c i) := by
  classical
  rw [perLetterInputLaw_eq_mixture h_meas c i]
  have hM_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  refine Integrable.smul_measure ?_ hM_ne_top
  refine integrable_finsetSum_measure.mpr (fun m _ => ?_)
  exact integrable_dirac (enorm_lt_top)

/-- Per-fibre output log-density integrability (1-D): `log (rnDeriv perLetterYLaw_i vol)`
integrable against each Gaussian fibre `gaussian x N`. -/
private lemma integrable_log_perLetterLaw_on_fibre
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) (x : ℝ) :
    Integrable
      (fun y => Real.log
        (((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv volume y).toReal)
      (gaussianReal x N) := by
  classical
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set q := (converseJointInline h_meas c).map (fun ω => ω.2 i) with hq
  set f : ℝ → ℝ≥0∞ := perLetterMixtureDensity N c i with hf_def
  have hf_meas : Measurable f := perLetterMixtureDensity_measurable N c i
  have hq_wd : q = volume.withDensity f := by
    rw [hq, hf_def]; exact perLetterLaw_withDensity h_meas c i hM_pos hN
  have hgx_ac : gaussianReal x N ≪ (volume : Measure ℝ) := gaussianReal_absolutelyContinuous x hN
  have h_rn_vol : q.rnDeriv volume =ᵐ[volume] f := by
    rw [hq_wd]; exact Measure.rnDeriv_withDensity volume hf_meas
  have h_log_ae : (fun y => Real.log (q.rnDeriv volume y).toReal)
      =ᵐ[gaussianReal x N] (fun y => Real.log ((perLetterMixtureDensity N c i y).toReal)) := by
    filter_upwards [hgx_ac.ae_le h_rn_vol] with y hy
    rw [hy]
  refine (Integrable.congr ?_ h_log_ae.symm)
  obtain ⟨c₀, c₁, hc₁, h_abs⟩ := perLetterMixtureDensity_log_abs_le N c i hM_pos hN
  have h_sq_int : Integrable (fun y : ℝ => y ^ 2) (gaussianReal x N) :=
    (memLp_id_gaussianReal (μ := x) (v := N) 2).integrable_sq
  have h_dom : Integrable (fun y : ℝ => c₀ + c₁ * y ^ 2) (gaussianReal x N) :=
    (integrable_const c₀).add (h_sq_int.const_mul c₁)
  refine Integrable.mono' h_dom ?_ ?_
  · exact (Real.measurable_log.comp
      (perLetterMixtureDensity_measurable N c i).ennreal_toReal).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs]
    exact h_abs y

/-- **Per-letter MI decomposition**: `I(X_i;Y_i).toReal = h(Y_i) − h(noise)`. -/
private lemma perLetterMI_decomp
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    (mutualInfo (converseJointInline h_meas c)
        (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)).toReal
      = InformationTheory.Shannon.differentialEntropy
          ((converseJointInline h_meas c).map (fun ω => ω.2 i))
        - InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  classical
  have hM_pos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set p := perLetterInputLaw h_meas c i with hp
  set W := awgnChannel N h_meas with hW
  have hpair_meas : Measurable (fun ω : Fin M × (Fin n → ℝ) => (c.encoder ω.1 i, ω.2 i)) :=
    ((measurable_of_countable (fun m : Fin M => c.encoder m i)).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  -- output distribution `q = perLetterYLaw_i`
  have hq_eq : ChannelCoding.outputDistribution p W
      = (converseJointInline h_meas c).map (fun ω => ω.2 i) := by
    show ((p ⊗ₘ W).map Prod.snd) = _
    rw [hp, hW, ← perLetter_map_eq_compProd h_meas c i]
    rw [Measure.map_map measurable_snd hpair_meas]
    rfl
  -- regularity
  have hW_ac : ∀ x, W x ≪ (volume : Measure ℝ) := by
    intro x; rw [hW, awgnChannel_apply]; exact gaussianReal_absolutelyContinuous x hN
  have hq_ac : ChannelCoding.outputDistribution p W ≪ (volume : Measure ℝ) := by
    rw [hq_eq]; exact perLetterLaw_ac_volume hN h_meas c i
  have hvol_ac_q : (volume : Measure ℝ) ≪ ChannelCoding.outputDistribution p W := by
    rw [hq_eq]; exact volume_ac_perLetterLaw hN h_meas c i
  have hWx_q : ∀ x, W x ≪ ChannelCoding.outputDistribution p W :=
    fun x => (hW_ac x).trans hvol_ac_q
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod (ChannelCoding.outputDistribution p W) := by
    rw [← Measure.compProd_const]
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Kernel.const_apply] using hWx_q x)
  -- proxy `g (x, y) := gaussianPDF x N y`
  set g : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF z.1 N z.2 with hg
  have hg_meas : Measurable g := gaussianPDF_joint_measurable N
  have hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y) := by
    intro x
    rw [hW, awgnChannel_apply]
    filter_upwards [(gaussianReal_absolutelyContinuous x hN).ae_le (rnDeriv_gaussianReal x N)]
      with y hy
    rw [hy]
  -- per-fibre log-density integrability against `W x = gaussian x N`
  have h_int_fibre_self : ∀ x, Integrable (fun y => Real.log (g (x, y)).toReal) (W x) := by
    intro x
    have hint := gaussianReal_logRnDeriv_integrable_inline x hN
    have hWx : W x = gaussianReal x N := by rw [hW, awgnChannel_apply]
    rw [hWx]
    refine hint.congr ?_
    filter_upwards [(gaussianReal_absolutelyContinuous x hN).ae_le (rnDeriv_gaussianReal x N)]
      with y hy
    rw [hg]; simp only; rw [hy]
  -- `h_fibre_self` (proxy integral = rnDeriv integral, per fibre)
  have h_fibre_self : ∀ x, ∫ y, Real.log (g (x, y)).toReal ∂(W x)
      = ∫ y, Real.log ((W x).rnDeriv volume y).toReal ∂(W x) := by
    intro x
    refine integral_congr_ae ?_
    filter_upwards [hg_ae x] with y hy
    rw [← hy]
  -- output log-density integrability against q (= perLetterYLaw_i)
  have h_out_self : Integrable
      (fun y => Real.log ((ChannelCoding.outputDistribution p W).rnDeriv volume y).toReal)
      (ChannelCoding.outputDistribution p W) := by
    rw [hq_eq]
    set ν : Measure ℝ := (converseJointInline h_meas c).map (fun ω => ω.2 i) with hν
    haveI hν_prob : IsProbabilityMeasure ν := by
      rw [hν]
      exact Measure.isProbabilityMeasure_map
        (((measurable_pi_apply i).comp measurable_snd).aemeasurable)
    set f : ℝ → ℝ≥0∞ := perLetterMixtureDensity N c i with hf_def
    have hf_meas : Measurable f := perLetterMixtureDensity_measurable N c i
    have hν_wd : ν = volume.withDensity f := by
      rw [hν, hf_def]; exact perLetterLaw_withDensity h_meas c i hM_pos hN
    have hν_ac : ν ≪ (volume : Measure ℝ) := by
      rw [hν_wd]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
    have h_rn_vol : ν.rnDeriv volume =ᵐ[volume] f := by
      conv_lhs => rw [hν_wd]
      exact Measure.rnDeriv_withDensity volume hf_meas
    have h_log_ae : (fun y => Real.log (ν.rnDeriv volume y).toReal)
        =ᵐ[ν] (fun y => Real.log ((perLetterMixtureDensity N c i y).toReal)) := by
      filter_upwards [hν_ac.ae_le h_rn_vol] with y hy
      rw [hy]
    refine (Integrable.congr ?_ h_log_ae.symm)
    obtain ⟨c₀, c₁, hc₁, h_abs⟩ := perLetterMixtureDensity_log_abs_le N c i hM_pos hN
    have h_dom : Integrable (fun y : ℝ => c₀ + c₁ * y ^ 2) ν :=
      (integrable_const c₀).add (((by rw [hν]; exact perLetterLaw_sq_integrable h_meas c i hM_pos hN)
        : Integrable (fun y : ℝ => y ^ 2) ν).const_mul c₁)
    refine Integrable.mono' h_dom ?_ ?_
    · exact (Real.measurable_log.comp
        (perLetterMixtureDensity_measurable N c i).ennreal_toReal).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs]
      exact h_abs y
  -- compProd-level integrabilities (the `p`-norm-integrability is free: `p` is finite-support)
  have h_int_fibre : Integrable (fun z : ℝ × ℝ => Real.log (g z).toReal) (p ⊗ₘ W) := by
    rw [Measure.integrable_compProd_iff
      ((hg_meas.ennreal_toReal.log).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun x => h_int_fibre_self x), ?_⟩
    rw [hp]
    refine integrable_of_perLetterInputLaw h_meas c i ?_
    -- measurability of `x ↦ ∫ y, ‖log g(x,y)‖ ∂(W x)`
    have : StronglyMeasurable
        (fun x => ∫ y, ‖Real.log (g (x, y)).toReal‖ ∂(W x)) :=
      (StronglyMeasurable.integral_kernel_prod_right' (κ := W)
        (f := fun z : ℝ × ℝ => ‖Real.log (g z).toReal‖)
        (hg_meas.ennreal_toReal.log.norm.stronglyMeasurable))
    exact this.measurable
  have h_int_out : Integrable
      (fun z : ℝ × ℝ => Real.log
          ((ChannelCoding.outputDistribution p W).rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    rw [hq_eq]
    set ψ : ℝ → ℝ := fun y => Real.log
      (((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv volume y).toReal with hψ
    have hψ_meas : Measurable ψ :=
      (Real.measurable_log.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal)
    show Integrable (fun z : ℝ × ℝ => ψ z.2) (p ⊗ₘ W)
    rw [Measure.integrable_compProd_iff
      (f := fun z : ℝ × ℝ => ψ z.2) ((hψ_meas.comp measurable_snd).aestronglyMeasurable)]
    refine ⟨Filter.Eventually.of_forall (fun x => ?_), ?_⟩
    · -- per-fibre: `ψ` integrable against `W x = gaussian x N`
      have hWx : W x = gaussianReal x N := by rw [hW, awgnChannel_apply]
      rw [hWx]
      exact integrable_log_perLetterLaw_on_fibre hN h_meas c i x
    · -- `p`-norm-integrability (finite support)
      rw [hp]
      refine integrable_of_perLetterInputLaw h_meas c i ?_
      have : StronglyMeasurable (fun x => ∫ y, ‖ψ y‖ ∂(W x)) :=
        (StronglyMeasurable.integral_kernel_prod_right' (κ := W)
          (f := fun z : ℝ × ℝ => ‖ψ z.2‖)
          ((hψ_meas.comp measurable_snd).norm.stronglyMeasurable))
      exact this.measurable
  -- apply the generic 1-D decomposition
  rw [perLetterMI_eq_channel h_meas c i]
  rw [ChannelCoding.mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    hW_ac hWx_q hq_ac h_joint_ac g hg_meas hg_ae h_int_fibre h_int_out]
  rw [hq_eq]
  -- fibre term: `∫ x, h(W x) ∂p = ∫ x, h(gaussian 0 N) ∂p = h(gaussian 0 N)`
  have h_fibre_ent : ∀ x, InformationTheory.Shannon.differentialEntropy (W x)
      = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
    intro x
    rw [hW, awgnChannel_apply,
      InformationTheory.Shannon.differentialEntropy_gaussianReal x hN,
      InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hN]
  rw [integral_congr_ae (Filter.Eventually.of_forall h_fibre_ent), integral_const,
    probReal_univ, one_smul]

/-- `log(blockYLaw.rnDeriv vol)` integrable against `blockYLaw` itself (mixture of components). -/
private lemma integrable_log_blockYLawInline_self
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    Integrable
      (fun y => Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal)
      (blockYLawInline h_meas c) := by
  classical
  set F : (Fin n → ℝ) → ℝ :=
    fun y => Real.log ((blockYLawInline h_meas c).rnDeriv volume y).toReal with hF
  rw [blockYLawInline_eq_mixture h_meas c]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  refine Integrable.smul_measure ?_ hM_inv_ne_top
  refine integrable_finsetSum_measure.mpr (fun m _ => ?_)
  exact integrable_log_blockYLawInline_on_component hN h_meas c m

/-- `log(perLetterYLaw_i.rnDeriv vol (y i))` integrable against `blockYLaw` (per-coord marginal
log-density against the joint). -/
private lemma integrable_log_marg_on_blockYLawInline
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) (i : Fin n) :
    Integrable
      (fun y => Real.log
        ((((converseJointInline h_meas c).map (fun ω => ω.2 i))).rnDeriv volume (y i)).toReal)
      (blockYLawInline h_meas c) := by
  classical
  set F : (Fin n → ℝ) → ℝ := fun y => Real.log
      ((((converseJointInline h_meas c).map (fun ω => ω.2 i))).rnDeriv volume (y i)).toReal with hF
  rw [blockYLawInline_eq_mixture h_meas c]
  have hM_inv_ne_top : (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ ≠ ∞ := by
    rw [Fintype.card_fin]; simp; exact_mod_cast (NeZero.ne M)
  refine Integrable.smul_measure ?_ hM_inv_ne_top
  refine integrable_finsetSum_measure.mpr (fun m _ => ?_)
  -- `F y = (ψ ∘ eval i) y` where `ψ = log(perLetterYLaw_i.rnDeriv vol)`, integrable against the
  -- i-th 1-D Gaussian factor via `integrable_comp_eval`
  rw [hF]
  show Integrable (fun y : Fin n → ℝ => Real.log
      (((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv volume (y i)).toReal)
    (Measure.pi (fun j : Fin n => gaussianReal (c.encoder m j) N))
  exact integrable_comp_eval (μ := fun j : Fin n => gaussianReal (c.encoder m j) N) (i := i)
    (integrable_log_perLetterLaw_on_fibre hN h_meas c i (c.encoder m i))

/-- **n-D subadditivity for the block output law**: `h(Y^n) ≤ ∑ᵢ h(Y_i)`. -/
private lemma jointDifferentialEntropyPi_blockYLawInline_le_sum
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c)
      ≤ ∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
          ((converseJointInline h_meas c).map (fun ω => ω.2 i)) := by
  classical
  set q := blockYLawInline h_meas c with hq
  haveI : IsProbabilityMeasure q := by rw [hq]; infer_instance
  -- marginal identification: `q.map (·i) = perLetterYLaw_i`
  have h_marg_eq : ∀ i, q.map (fun y => y i) = (converseJointInline h_meas c).map (fun ω => ω.2 i) :=
    fun i => blockYLawInline_map_eval h_meas c i
  haveI : ∀ i, IsProbabilityMeasure (q.map (fun z => z i)) := by
    intro i; rw [h_marg_eq i]
    exact Measure.isProbabilityMeasure_map (((measurable_pi_apply i).comp measurable_snd).aemeasurable)
  have h_marg_ac : ∀ i, (q.map (fun z => z i)) ≪ (volume : Measure ℝ) := by
    intro i; rw [h_marg_eq i]; exact perLetterLaw_ac_volume hN h_meas c i
  have hμ_ac : q ≪ (volume : Measure (Fin n → ℝ)) := by rw [hq]; exact blockYLawInline_ac_volume hN h_meas c
  -- `q ≪ pi(marginals)` via `q ≪ vol` and `vol ≪ pi(marginals)`
  have hvol_ac_pi : (volume : Measure (Fin n → ℝ)) ≪ Measure.pi (fun i => q.map (fun z => z i)) := by
    have h_rev : ∀ i, (volume : Measure ℝ) ≪ q.map (fun z => z i) := by
      intro i; rw [h_marg_eq i]; exact volume_ac_perLetterLaw hN h_meas c i
    -- mirror of `pi_absolutelyContinuous_reverse`
    set f : Fin n → ℝ → ℝ≥0∞ := fun i => (q.map (fun z => z i)).rnDeriv volume with hf_def
    have hf_meas : ∀ i, Measurable (f i) := fun i => Measure.measurable_rnDeriv _ _
    have h_eq : ∀ i, (volume : Measure ℝ).withDensity (f i) = q.map (fun z => z i) :=
      fun i => Measure.withDensity_rnDeriv_eq _ volume (h_marg_ac i)
    haveI : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity (f i)) := by
      intro i; rw [h_eq i]; infer_instance
    have h_pi_eq : Measure.pi (fun i => q.map (fun z => z i))
        = (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).withDensity
            (fun z => ∏ i, f i (z i)) := by
      rw [← (funext h_eq : (fun i => (volume : Measure ℝ).withDensity (f i))
          = fun i => q.map (fun z => z i))]
      exact InformationTheory.Shannon.pi_withDensity_fin (fun _ : Fin n => (volume : Measure ℝ)) hf_meas
    rw [h_pi_eq, ← volume_pi]
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (Finset.measurable_prod _ (fun i _ => (hf_meas i).comp (measurable_pi_apply i))).aemeasurable
    · -- each `f i (z i)` a.e.-positive on `volume` (from `volume ≪ q.map(·i)`)
      have h_pos : ∀ i, ∀ᵐ y ∂(volume : Measure ℝ), f i y ≠ 0 := by
        intro i
        have := Measure.rnDeriv_pos' (h_rev i)
        filter_upwards [this] with y hy using hy.ne'
      filter_upwards [eventually_countable_forall.mpr
        (fun i => (Measure.quasiMeasurePreserving_eval
          (μ := fun _ : Fin n => (volume : Measure ℝ)) i).ae (h_pos i))] with z hz
      simp only [ne_eq, Finset.prod_eq_zero_iff, not_exists, not_and]
      intro i _
      exact hz i
  have h_joint_ac : q ≪ Measure.pi (fun i => q.map (fun z => z i)) := hμ_ac.trans hvol_ac_pi
  -- integrability
  have h_int_joint : Integrable (fun z => Real.log ((q.rnDeriv volume z).toReal)) q := by
    rw [hq]; exact integrable_log_blockYLawInline_self hN h_meas c
  have h_int_marg : ∀ i, Integrable
      (fun z => Real.log (((q.map (fun z => z i)).rnDeriv volume (z i)).toReal)) q := by
    intro i
    have h_eq : (fun z : Fin n → ℝ => Real.log (((q.map (fun z => z i)).rnDeriv volume (z i)).toReal))
        = (fun z => Real.log
            ((((converseJointInline h_meas c).map (fun ω => ω.2 i)).rnDeriv volume (z i)).toReal)) := by
      funext z; rw [h_marg_eq i]
    rw [h_eq, hq]
    exact integrable_log_marg_on_blockYLawInline hN h_meas c i
  -- apply the n-D subadditivity bridge, then rewrite marginals
  have h_sub := InformationTheory.Shannon.jointDifferentialEntropyPi_le_sum
    (μ := q) h_marg_ac hμ_ac h_joint_ac h_int_joint h_int_marg
  rw [Finset.sum_congr rfl (fun i _ => congrArg InformationTheory.Shannon.differentialEntropy
    (h_marg_eq i))] at h_sub
  exact h_sub

/-- Memoryless AWGN continuous MI chain rule.

`I(X^n; Y^n) ≤ ∑ᵢ I(X_i; Y_i)` on the inlined joint. The route:
`I(X^n;Y^n) ≤ I(W;Y^n)` (deterministic DPI) `= h(Y^n) − n·h(noise) ≤ ∑ h(Y_i) − n·h(noise)
= ∑ I(X_i;Y_i)`, combining `mutualInfo_encoder_le_fst`, `blockMI_decomp`,
`jointDifferentialEntropyPi_blockYLawInline_le_sum`, and `perLetterMI_decomp`.
Consumer-side `unfold jointMIXnYn perLetterMI awgnConverseJoint` gives defeq.

`[NeZero M]` (`M ≥ 1`, so the uniform message law is a probability measure) and `hN : N ≠ 0`
(full-support Gaussian fibres ⇒ blockYLaw absolutely continuous) are regularity
preconditions, both supplied by the converse consumer. They are not load-bearing: the MI
inequality is proved from the entropy chain, not encoded in the hypotheses (at the
degenerate boundary `N = 0` the Gaussian fibres collapse to Diracs, breaking only the
density route, while the MI inequality itself stays true since it is KL≥0-backed).
@audit:ok -/
@[entry_point]
theorem awgnContinuousMIChainRule_holds
    {P : ℝ} {N : ℝ≥0} (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    (mutualInfo (converseJointInline h_meas c)
        (fun ω => c.encoder ω.1) Prod.snd).toReal
      ≤ ∑ i : Fin n,
          (mutualInfo (converseJointInline h_meas c)
            (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)).toReal := by
  classical
  set h := InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) with hh
  -- LHS ≤ I(W;Y^n).toReal via deterministic DPI + finiteness.
  have h_dpi := mutualInfo_encoder_le_fst h_meas c
  have h_fin := mutualInfo_fst_snd_ne_top hN h_meas c
  have h_lhs_le :
      (mutualInfo (converseJointInline h_meas c) (fun ω => c.encoder ω.1) Prod.snd).toReal
        ≤ (mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd).toReal :=
    ENNReal.toReal_mono h_fin h_dpi
  -- I(W;Y^n).toReal = h(Y^n) − n·h(noise).
  have h_block := blockMI_decomp hN h_meas c
  -- h(Y^n) ≤ ∑ᵢ h(Y_i).
  have h_sub := jointDifferentialEntropyPi_blockYLawInline_le_sum hN h_meas c
  -- ∑ᵢ I(X_i;Y_i).toReal = (∑ᵢ h(Y_i)) − n·h(noise).
  have h_sum_perletter :
      ∑ i : Fin n,
          (mutualInfo (converseJointInline h_meas c)
            (fun ω => c.encoder ω.1 i) (fun ω => ω.2 i)).toReal
        = (∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
              ((converseJointInline h_meas c).map (fun ω => ω.2 i))) - (n : ℝ) * h := by
    rw [Finset.sum_congr rfl (fun i _ => perLetterMI_decomp hN h_meas c i)]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Combine.
  rw [h_sum_perletter]
  calc
    (mutualInfo (converseJointInline h_meas c) (fun ω => c.encoder ω.1) Prod.snd).toReal
        ≤ (mutualInfo (converseJointInline h_meas c) Prod.fst Prod.snd).toReal := h_lhs_le
    _ = InformationTheory.Shannon.jointDifferentialEntropyPi (blockYLawInline h_meas c)
          - (n : ℝ) * h := h_block
    _ ≤ (∑ i : Fin n, InformationTheory.Shannon.differentialEntropy
            ((converseJointInline h_meas c).map (fun ω => ω.2 i))) - (n : ℝ) * h := by
        gcongr

/-! ### Markov factorization -/

/-- Markov chain `W → encoder ∘ W → Y^n` factorization.

`IsMarkovChain (converseJointInline h_meas c) Prod.fst (encoder ∘ fst) Prod.snd`, the
joint factorization.

The argument starts from the identity `μ = (μ.map fst) ⊗ₘ (W.comap encoder)` (with `μ` the
message-space marginal and `W := Channel.toBlock (awgnChannel N) n` the noise block kernel),
established on the mixture-of-diracs via `ext_of_lintegral` (`h_marginalA`). From it,
`condDistrib Yo Zc μ =ᵐ W` (`condDistrib_ae_eq_of_measure_eq_compProd`); then `condDistrib Xs Zc μ`
is absorbed via `compProd_map_condDistrib`, and the triple-joint factorization is verified by
`ext_of_lintegral` + the `h_marginalA` reduction (precedent:
`BlockwiseChannel.isMarkovChain_per_letter_input`).
@audit:ok -/
@[entry_point]
theorem awgnConverseMarkov_holds
    {P : ℝ} {N : ℝ≥0} (h_meas : IsAwgnChannelMeasurable N)
    {M n : ℕ} [NeZero M] (c : AwgnCode M n P) :
    IsMarkovChain (converseJointInline h_meas c)
      (Prod.fst : Fin M × (Fin n → ℝ) → Fin M)
      (fun ω : Fin M × (Fin n → ℝ) => c.encoder ω.1)
      (Prod.snd : Fin M × (Fin n → ℝ) → Fin n → ℝ) := by
  set μ : Measure (Fin M × (Fin n → ℝ)) := converseJointInline h_meas c with hμ_def
  -- The three RVs.
  set Xs : Fin M × (Fin n → ℝ) → Fin M := Prod.fst with hXs_def
  set Zc : Fin M × (Fin n → ℝ) → (Fin n → ℝ) := fun ω => c.encoder ω.1 with hZc_def
  set Yo : Fin M × (Fin n → ℝ) → (Fin n → ℝ) := Prod.snd with hYo_def
  -- The noise block kernel `W^{⊗n}` of the AWGN channel.
  set W : Kernel (Fin n → ℝ) (Fin n → ℝ) :=
    ChannelCoding.Channel.toBlock (awgnChannel N h_meas) n with hW_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- Measurability of the three RVs.
  have hXs_meas : Measurable Xs := measurable_fst
  have hZc_meas : Measurable Zc := by
    rw [hZc_def]; exact (Measurable.of_discrete).comp measurable_fst
  have hYo_meas : Measurable Yo := measurable_snd
  have hg_meas : Measurable c.encoder := Measurable.of_discrete
  -- `W.comap encoder`: the channel kernel reindexed from message to codeword.
  set Wg : Kernel (Fin M) (Fin n → ℝ) := W.comap c.encoder hg_meas with hWg_def
  -- **Fundamental message-space marginal (A)**: `μ = (μ.map Xs) ⊗ₘ (W.comap encoder)`.
  -- Since `(Xs ω, Yo ω) = ω`, this says the converse joint factors as
  -- `uniform(W) ⊗ₘ (∏ᵢ awgnChannel (encoder · i))`. Proved by `ext_of_lintegral` on the
  -- mixture-of-diracs.
  -- `μ.map Xs = (1/M) • ∑ₘ δ_m` (uniform message law).
  have h_map_Xs : μ.map Xs
      = ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M, (Measure.dirac m) := by
    rw [hμ_def, hXs_def, converseJointInline]
    rw [Measure.map_smul]
    congr 1
    rw [Measure.map_finset_sum (measurable_fst.aemeasurable)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Measure.map_fst_prod]
    simp
  have h_marginalA : μ = (μ.map Xs) ⊗ₘ Wg := by
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    -- RHS via compProd, then h_map_Xs (do RHS first, before unfolding μ on LHS).
    rw [Measure.lintegral_compProd hf, h_map_Xs, lintegral_smul_measure,
      lintegral_finsetSum_measure]
    have hRHS_summand : ∀ m : Fin M,
        ∫⁻ a : Fin M, ∫⁻ y : Fin n → ℝ, f (a, y) ∂(Wg a) ∂(Measure.dirac m)
          = ∫⁻ y : Fin n → ℝ, f (m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_dirac]
      rfl
    simp_rw [hRHS_summand]
    -- LHS over the mixture.
    rw [hμ_def, converseJointInline, lintegral_smul_measure,
      lintegral_finsetSum_measure]
    have hLHS_summand : ∀ m : Fin M,
        ∫⁻ ω : Fin M × (Fin n → ℝ), f ω
            ∂((Measure.dirac m).prod
              (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
          = ∫⁻ y : Fin n → ℝ, f (m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_prod _ hf.aemeasurable, lintegral_dirac]
    simp_rw [hLHS_summand]
  -- `μ.map Zc = (1/M) • ∑ₘ δ_(encoder m)` (codeword law).
  have h_map_Zc : μ.map Zc
      = ((Fintype.card (Fin M) : ℝ≥0∞)⁻¹) • ∑ m : Fin M, (Measure.dirac (c.encoder m)) := by
    have hZc_comp : Zc = c.encoder ∘ Xs := rfl
    rw [hZc_comp, ← Measure.map_map Measurable.of_discrete hXs_meas, h_map_Xs,
      Measure.map_smul]
    congr 1
    rw [Measure.map_finset_sum' Measurable.of_discrete.aemeasurable]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Measure.map_dirac' Measurable.of_discrete]
  -- Linchpin marginal: `μ.map (Zc, Yo) = (μ.map Zc) ⊗ₘ W`.
  have h_pair_eq : μ.map (fun ω => (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ W := by
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    -- RHS via compProd + h_map_Zc.
    rw [Measure.lintegral_compProd hf, h_map_Zc, lintegral_smul_measure,
      lintegral_finsetSum_measure]
    have hRHS_summand : ∀ m : Fin M,
        ∫⁻ z : Fin n → ℝ, ∫⁻ y : Fin n → ℝ, f (z, y) ∂(W z) ∂(Measure.dirac (c.encoder m))
          = ∫⁻ y : Fin n → ℝ, f (c.encoder m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_dirac' _
        (Measurable.lintegral_kernel_prod_right' (κ := W) hf)]
      rfl
    simp_rw [hRHS_summand]
    -- LHS over the mixture.
    rw [lintegral_map hf (hZc_meas.prodMk hYo_meas), hμ_def, converseJointInline,
      lintegral_smul_measure, lintegral_finsetSum_measure]
    have hLHS_summand : ∀ m : Fin M,
        ∫⁻ ω : Fin M × (Fin n → ℝ), f (Zc ω, Yo ω)
            ∂((Measure.dirac m).prod
              (Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))))
          = ∫⁻ y : Fin n → ℝ, f (c.encoder m, y)
              ∂(Measure.pi (fun i : Fin n => awgnChannel N h_meas (c.encoder m i))) := by
      intro m
      rw [lintegral_prod (fun ω : Fin M × (Fin n → ℝ) => f (Zc ω, Yo ω))
        (hf.comp (hZc_meas.prodMk hYo_meas)).aemeasurable, lintegral_dirac]
    simp_rw [hLHS_summand]
  -- Identify `condDistrib Yo Zc μ =ᵐ[μ.map Zc] W`.
  haveI : IsProbabilityMeasure (μ.map Zc) := Measure.isProbabilityMeasure_map hZc_meas.aemeasurable
  have hK_Y_eq : condDistrib Yo Zc μ =ᵐ[μ.map Zc] W :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hYo_meas.aemeasurable h_pair_eq
  -- Unfold IsMarkovChain and substitute condDistrib Yo Zc → W on the RHS.
  unfold IsMarkovChain
  set K_X : Kernel (Fin n → ℝ) (Fin M) := condDistrib Xs Zc μ with hK_X_def
  have h_compProd_eq :
      (μ.map Zc) ⊗ₘ (K_X ×ₖ condDistrib Yo Zc μ) = (μ.map Zc) ⊗ₘ (K_X ×ₖ W) := by
    refine Measure.compProd_congr ?_
    filter_upwards [hK_Y_eq] with a ha
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, ha]
  rw [h_compProd_eq]
  -- Triple-joint factorization via ext_of_lintegral.
  have h_LHS_meas : Measurable (fun ω => (Zc ω, Xs ω, Yo ω)) :=
    hZc_meas.prodMk (hXs_meas.prodMk hYo_meas)
  -- `compProd_map_condDistrib`: fold K_X back into `μ.map (Zc, Xs)`.
  have hKX_fold : (μ.map Zc) ⊗ₘ K_X = μ.map (fun ω => (Zc ω, Xs ω)) :=
    compProd_map_condDistrib (μ := μ) (X := Zc) (Y := Xs) hXs_meas.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  -- LHS: ∫⁻ ω, f (Zc ω, Xs ω, Yo ω) ∂μ.
  rw [lintegral_map hf h_LHS_meas]
  -- RHS: unfold the outer compProd over (μ.map Zc), then the inner product kernel.
  rw [Measure.lintegral_compProd hf]
  -- RHS inner: ∫⁻ p ∂((K_X ×ₖ W) z), f (z, p.1, p.2)
  --          = ∫⁻ x ∂(K_X z), ∫⁻ y ∂(W z), f (z, x, y).
  have h_inner_split : ∀ z : Fin n → ℝ,
      ∫⁻ p : Fin M × (Fin n → ℝ), f (z, p.1, p.2) ∂((K_X ×ₖ W) z)
        = ∫⁻ x : Fin M, ∫⁻ y : Fin n → ℝ, f (z, x, y) ∂(W z) ∂(K_X z) := by
    intro z
    rw [Kernel.prod_apply]
    rw [lintegral_prod (fun p : Fin M × (Fin n → ℝ) => f (z, p.1, p.2))
      (hf.comp (measurable_const.prodMk
        (measurable_fst.prodMk measurable_snd))).aemeasurable]
  simp_rw [h_inner_split]
  -- Define G (z, x) := ∫⁻ y ∂(W z), f (z, x, y), so RHS = ∫⁻ z ∂(μ.map Zc), ∫⁻ x ∂(K_X z), G (z, x).
  set G : (Fin n → ℝ) × Fin M → ℝ≥0∞ :=
    fun p => ∫⁻ y : Fin n → ℝ, f (p.1, p.2, y) ∂(W p.1) with hG_def
  have hG_meas : Measurable G := by
    let K' : Kernel ((Fin n → ℝ) × Fin M) (Fin n → ℝ) :=
      W.comap (Prod.fst : (Fin n → ℝ) × Fin M → (Fin n → ℝ)) measurable_fst
    have h_eq_K' : G = fun p : (Fin n → ℝ) × Fin M =>
        ∫⁻ y : Fin n → ℝ, f (p.1, p.2, y) ∂(K' p) := by
      funext p; simp [G, K', Kernel.comap_apply]
    rw [h_eq_K']
    exact Measurable.lintegral_kernel_prod_right' (κ := K')
      (f := fun pp : ((Fin n → ℝ) × Fin M) × (Fin n → ℝ) => f (pp.1.1, pp.1.2, pp.2))
      (hf.comp (((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  have h_RHS_is_G : ∀ z : Fin n → ℝ, ∀ x : Fin M,
      ∫⁻ y : Fin n → ℝ, f (z, x, y) ∂(W z) = G (z, x) := fun _ _ => rfl
  simp_rw [h_RHS_is_G]
  -- RHS = ∫⁻ z ∂(μ.map Zc), ∫⁻ x ∂(K_X z), G (z, x) = ∫⁻ p ∂((μ.map Zc) ⊗ₘ K_X), G p.
  rw [← Measure.lintegral_compProd hG_meas, hKX_fold]
  -- RHS = ∫⁻ p ∂(μ.map (Zc, Xs)), G p = ∫⁻ ω ∂μ, G (Zc ω, Xs ω).
  rw [lintegral_map hG_meas (hZc_meas.prodMk hXs_meas)]
  -- Now goal: ∫⁻ ω, f (Zc ω, Xs ω, Yo ω) ∂μ = ∫⁻ ω, G (Zc ω, Xs ω) ∂μ.
  rw [← hμ_def]
  -- Reduce any `∫⁻ ω, H ω ∂μ` through message-space marginal (A).
  have h_reduce : ∀ H : Fin M × (Fin n → ℝ) → ℝ≥0∞, Measurable H →
      ∫⁻ ω, H ω ∂μ
        = ∫⁻ a : Fin M, ∫⁻ y : Fin n → ℝ, H (a, y) ∂(Wg a) ∂(μ.map Xs) := by
    intro H hH
    conv_lhs => rw [h_marginalA]
    rw [Measure.lintegral_compProd hH]
  rw [h_reduce (fun ω => f (Zc ω, Xs ω, Yo ω)) (hf.comp h_LHS_meas),
    h_reduce (fun ω => G (Zc ω, Xs ω)) (hG_meas.comp (hZc_meas.prodMk hXs_meas))]
  -- Both inner integrals over `Wg a`. For each message `a`:
  refine lintegral_congr fun a => ?_
  have hWg_eq : Wg a = W (c.encoder a) := by rw [hWg_def, Kernel.comap_apply]
  haveI : IsProbabilityMeasure (Wg a) := by rw [hWg_eq]; infer_instance
  -- LHS inner: ∫⁻ y ∂(Wg a), f (encoder a, a, y).  `(Zc (a,y), Xs (a,y), Yo (a,y)) = (encoder a, a, y)`.
  -- RHS inner: ∫⁻ y ∂(Wg a), G (encoder a, a), constant in y, value `∫⁻ y' ∂(W (encoder a)), f (encoder a, a, y')`.
  have hRHS_eval : (fun y : Fin n → ℝ => G (Zc (a, y), Xs (a, y)))
      = (fun _ : Fin n → ℝ => ∫⁻ y' : Fin n → ℝ, f (c.encoder a, a, y') ∂(Wg a)) := by
    funext y
    show G (c.encoder a, a) = _
    rw [hG_def, hWg_eq]
  rw [hRHS_eval, lintegral_const, measure_univ, mul_one]

end InformationTheory.Shannon.AWGN
