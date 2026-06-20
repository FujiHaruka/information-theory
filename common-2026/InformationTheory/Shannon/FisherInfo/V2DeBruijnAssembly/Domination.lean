import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.V2DeBruijnPerTime
import InformationTheory.Shannon.FisherConvBound
import InformationTheory.Shannon.EPI.Conv.DensitySecondDeriv
import InformationTheory.Shannon.FisherInfo.V2DeBruijnAssembly.Core

namespace InformationTheory.Shannon.FisherInfoV2

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAddDeriv)

variable {Ω : Type*} {_mΩ : MeasurableSpace Ω}

/-- For `s ∈ (t/2, 2t)`, the spatial second derivative of the convolution density is dominated
by the convolution of `pX` against the `s`-uniform Gaussian-Hessian kernel majorant
`gaussHessMaj t`: `‖∂²_x (pX ∗ g_s) x‖ ≤ ∫ y, pX y · gaussHessMaj t (x − y) ∂volume`.

@audit:ok -/
private theorem convDensityAdd_deriv2_le_gaussHessMaj_conv
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) (x : ℝ) {s : ℝ}
    (hs : s ∈ Set.Ioo (t/2) (2*t)) :
    ‖deriv (deriv (convDensityAdd pX
        (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩))) x‖
      ≤ ∫ y, pX y * gaussHessMaj t (x - y) ∂volume := by
  have hspos : (0:ℝ) < s := by have := hs.1; linarith
  -- kernel continuity (for measurability of the bridge integrands).
  have hker_cont : Continuous (fun u : ℝ => heatFlow_density_heat_equation_kernel s u) := by
    unfold heatFlow_density_heat_equation_kernel
    fun_prop
  have hker_meas : Measurable (fun u : ℝ => heatFlow_density_heat_equation_kernel s u) :=
    hker_cont.measurable
  -- global sup constants of the kernel spatial derivatives.
  set M1 : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * ((1 + 2 * s * Real.exp (-1)) / (2 * s)) with hM1
  set M2 : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ * ((2 * Real.exp (-1) + 1) / s) with hM2
  have hM1_nn : (0:ℝ) ≤ M1 := by rw [hM1]; positivity
  have hM2_nn : (0:ℝ) ≤ M2 := by rw [hM2]; positivity
  have hF1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume := by
    intro ξ
    exact (hpX_meas.aestronglyMeasurable).mul
      ((hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hker_le : ∀ v : ℝ, |heatFlow_density_heat_equation_kernel s v|
      ≤ (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹ := by
    intro v
    rw [heatFlow_density_heat_equation_kernel_eq hspos v,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 _ v)]
    exact gaussianPDFReal_le_prefactor' ⟨s, hspos.le⟩ v
  have hF1_int : ∀ ξ : ℝ,
      Integrable (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume := by
    intro ξ
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs]; exact hker_le (ξ - y))
  have hF1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))) volume := by
    intro ξ
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact ((measurable_const.sub measurable_id).div_const s).neg.aestronglyMeasurable
  have hb1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))‖ ≤ (fun y => |pX y| * M1) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv1_global_bound hspos (ξ - y)
    rwa [hM1]
  have hb1_int : Integrable (fun y => |pX y| * M1) volume := hpX_int.abs.mul_const _
  have hF2'_meas : AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (x - y)
        * ((x - y) ^ 2 / s ^ 2 - 1 / s))) volume := by
    refine (hpX_meas.aestronglyMeasurable).mul ?_
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (hker_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · exact (((measurable_const.sub measurable_id).pow_const 2).div_const _).sub
        measurable_const |>.aestronglyMeasurable
  have hb2 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * ((ξ - y) ^ 2 / s ^ 2 - 1 / s))‖ ≤ (fun y => |pX y| * M2) y := by
    refine Filter.Eventually.of_forall (fun y ξ _ => ?_)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := kernel_x_deriv2_global_bound hspos (ξ - y)
    rwa [hM2]
  have hb2_int : Integrable (fun y => |pX y| * M2) volume := hpX_int.abs.mul_const _
  have hF2_int : Integrable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (x - y)
        * (-((x - y) / s)))) volume := by
    refine Integrable.mono' hb1_int (hF1'_meas x) (Filter.Eventually.of_forall (fun y => ?_))
    have := kernel_x_deriv1_global_bound hspos (x - y)
    rw [norm_mul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rwa [hM1]
  have hbridge :=
    InformationTheory.Shannon.EPIConvDensitySecondDeriv.convDensityAdd_deriv2_eq_gaussian
    pX hpX_nn hpX_int hspos x
    (fun y => |pX y| * M1) hb1_int hF1_meas hF1_int hF1'_meas hb1
    (fun y => |pX y| * M2) hb2_int hF2_int hF2'_meas hb2
  rw [show (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩)
      = gaussianPDFReal 0 ⟨s, hspos.le⟩ from rfl, hbridge]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => norm_nonneg _)) ?_
    (Filter.Eventually.of_forall (fun y => ?_))
  · have hMmeas : Measurable (gaussHessMaj t) := by unfold gaussHessMaj; fun_prop
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t)) ?_ ?_
    · exact (hMmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussHessMaj_nonneg ht (x - y))]
      exact gaussHessMaj_bdd ht (x - y)
  · simp only []
    have hg_nn : (0:ℝ) ≤ gaussianPDFReal 0 ⟨s, hspos.le⟩ (x - y) := gaussianPDFReal_nonneg 0 _ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hpX_nn y),
      Real.norm_eq_abs, abs_of_nonneg hg_nn, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (hpX_nn y)
    exact gaussianHess_le_gaussHessMaj ht hs (x - y)

/-- On the neighborhood `Set.Ioo (t/2) (2*t)`, the spatial second derivative
`∂²_x p_s x = deriv (deriv (convDensityAdd pX g_s)) x` admits a single Lebesgue-integrable
envelope `bound : ℝ → ℝ` uniform in `s`: `‖∂²_x p_s x‖ ≤ bound x` for all `s ∈ (t/2, 2t)`,
with `Integrable bound volume`. The envelope is `bound x = ∫ y, pX y · gaussHessMaj t (x − y)`,
the convolution of `pX` against the `s`-uniform Gaussian-Hessian kernel majorant; it keeps the
Gaussian factor inside the convolution rather than dropping it, so it is finite for any
finite-variance `pX` (a Gaussian-tail bound on the Hessian would be false for polynomial-tail
densities).

@audit:ok -/
private theorem convDensityAdd_deriv2_poly_moment_majorant
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (_hpX_mass : (∫ y, pX y ∂volume) = 1)
    (_hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      ∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖deriv (deriv (convDensityAdd pX
            (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩))) x‖
          ≤ bound x := by
  -- The concrete envelope: `bound x = ∫ y, pX y · gaussHessMaj t (x − y)` — the convolution of
  -- the integrable density `pX` against the `s`-uniform Gaussian-Hessian kernel majorant.
  -- Integrability via Tonelli (`convKernel_envelope_integrable`), pointwise domination via the
  -- extracted concrete lemma `convDensityAdd_deriv2_le_gaussHessMaj_conv` (reused by `_chain_domination`).
  refine ⟨fun x => ∫ y, pX y * gaussHessMaj t (x - y) ∂volume, ?_, ?_⟩
  · have hMmeas : Measurable (gaussHessMaj t) := by unfold gaussHessMaj; fun_prop
    exact convKernel_envelope_integrable pX (gaussHessMaj t) hpX_int hpX_meas
      (gaussHessMaj_integrable ht) hMmeas
  · refine Filter.Eventually.of_forall (fun x s hs => ?_)
    exact convDensityAdd_deriv2_le_gaussHessMaj_conv pX hpX_nn hpX_meas hpX_int ht x hs

private theorem convDensityAdd_jointMajorant_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) (A B : ℝ) :
    Integrable (fun x => (A + B * x ^ 2)
        * ((1/2) * (∫ y, pX y * gaussHessMaj t (x - y) ∂volume))) volume := by
  set E : ℝ → ℝ := fun x => ∫ y, pX y * gaussHessMaj t (x - y) ∂volume with hE_def
  have hg_meas : Measurable (gaussHessMaj t) := by unfold gaussHessMaj; fun_prop
  have hg_nn : ∀ u, (0:ℝ) ≤ gaussHessMaj t u := gaussHessMaj_nonneg ht
  -- **route II = Tonelli + g_s moment** (the only honest route).
  -- The dominating function: `H x = ∫ pX y·G(x−y) + 2|B|·∫ (y²·pX y)·g(x−y)`, where
  -- `G(u) = (|A| + 2|B|·u²)·gaussHessMaj t u` (Gaussian × quartic) and `g = gaussHessMaj t`.
  -- Both summands are `convKernel_envelope_integrable` envelopes (`pX` / `y²·pX` integrable,
  -- `G` / `g` integrable). Pointwise `‖(A+Bx²)·(1/2)E x‖ ≤ H x` via `x² ≤ 2(x−y)²+2y²` (NO odd
  -- cross-term, so only even Gaussian moments needed). `hpX_mom` is genuinely used (it supplies
  -- integrability of `y²·pX`, the heavy-tail-controlling density). `integrable_natPow_mul_exp_neg_mul_sq`
  -- (route I = deleted case-A defect, false for polynomial-tail pX) is NOT used.
  set G : ℝ → ℝ := fun u => (|A| + 2 * |B| * u ^ 2) * gaussHessMaj t u with hG_def
  have hG_int : Integrable G volume := gaussHessMaj_polyWeight_integrable ht |A| (2 * |B|)
  have hG_meas : Measurable G := by rw [hG_def]; fun_prop
  have hG_nn : ∀ u, (0:ℝ) ≤ G u := fun u => by
    rw [hG_def]; exact mul_nonneg (by positivity) (hg_nn u)
  -- `y²·pX` integrable (= `hpX_mom`) and measurable.
  have hmomPX_int : Integrable (fun y => y ^ 2 * pX y) volume := hpX_mom
  have hmomPX_meas : Measurable (fun y => y ^ 2 * pX y) := by fun_prop
  -- the two convolution envelopes.
  have hEnv1_int : Integrable (fun x => ∫ y, pX y * G (x - y) ∂volume) volume :=
    convKernel_envelope_integrable pX G hpX_int hpX_meas hG_int hG_meas
  have hEnv2_int : Integrable (fun x => ∫ y, (y ^ 2 * pX y) * gaussHessMaj t (x - y) ∂volume)
      volume :=
    convKernel_envelope_integrable (fun y => y ^ 2 * pX y) (gaussHessMaj t)
      hmomPX_int hmomPX_meas (gaussHessMaj_integrable ht) hg_meas
  -- dominating function `H x` integrable.
  have hH_int : Integrable (fun x => (∫ y, pX y * G (x - y) ∂volume)
      + 2 * |B| * (∫ y, (y ^ 2 * pX y) * gaussHessMaj t (x - y) ∂volume)) volume :=
    hEnv1_int.add (hEnv2_int.const_mul _)
  -- measurability of the target (poly × convolution envelope).
  have hE_meas : AEStronglyMeasurable E volume := by
    rw [hE_def]
    exact (convKernel_envelope_integrable pX (gaussHessMaj t) hpX_int hpX_meas
      (gaussHessMaj_integrable ht) hg_meas).aestronglyMeasurable
  have htarget_meas : AEStronglyMeasurable
      (fun x => (A + B * x ^ 2) * ((1/2) * E x)) volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · fun_prop
    · exact hE_meas.const_mul _
  -- pointwise domination `‖(A+Bx²)·(1/2)·E x‖ ≤ H x`.
  refine Integrable.mono' hH_int htarget_meas (Filter.Eventually.of_forall (fun x => ?_))
  -- nonneg of `E x` (= `∫ pX y·g(x−y)`, integrand `≥ 0`).
  have hEnv_pos_int : Integrable (fun y => pX y * gaussHessMaj t (x - y)) volume := by
    have hMmeas := hg_meas
    refine hpX_int.mul_bdd
      (c := (Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t)) ?_ ?_
    · exact (hMmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn (x - y))]
      exact gaussHessMaj_bdd ht (x - y)
  have hE_nn : (0:ℝ) ≤ E x := by
    rw [hE_def]
    exact integral_nonneg (fun y => mul_nonneg (hpX_nn y) (hg_nn (x - y)))
  -- `‖(A+Bx²)·(1/2)·E x‖ = |A+Bx²|·(1/2)·E x ≤ (|A|+|B|x²)·E x`.
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have h12 : |(1/2 : ℝ)| = 1/2 := by rw [abs_of_pos]; norm_num
  rw [h12, abs_of_nonneg hE_nn]
  -- step 1: `|A+Bx²|·(1/2)·E x ≤ (|A|+|B|x²)·E x`.
  have hstep1 : |A + B * x ^ 2| * (1/2 * E x) ≤ (|A| + |B| * x ^ 2) * E x := by
    have hbound : |A + B * x ^ 2| ≤ |A| + |B| * x ^ 2 := by
      calc |A + B * x ^ 2| ≤ |A| + |B * x ^ 2| := abs_add_le _ _
        _ = |A| + |B| * x ^ 2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
    calc |A + B * x ^ 2| * (1/2 * E x)
        ≤ (|A| + |B| * x ^ 2) * (1/2 * E x) :=
          mul_le_mul_of_nonneg_right hbound (by positivity)
      _ ≤ (|A| + |B| * x ^ 2) * E x := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [hE_nn]
  -- step 2: `(|A|+|B|x²)·E x = ∫ (|A|+|B|x²)·pX y·g(x−y) ≤ ∫ pX y·G(x−y) + 2|B|∫(y²pX)·g(x−y) = H x`.
  refine le_trans hstep1 ?_
  -- pull the constant `(|A|+|B|x²)` into the integral.
  have hpull : (|A| + |B| * x ^ 2) * E x
      = ∫ y, (|A| + |B| * x ^ 2) * (pX y * gaussHessMaj t (x - y)) ∂volume := by
    rw [hE_def, ← integral_const_mul]
  rw [hpull]
  -- per-`y` fibre integrability of the two dominating pieces.
  -- (1) `fun y => pX y · G(x−y)`: `G` globally bounded (`gaussHessMaj_polyWeight_bdd`) × `pX` integ.
  have hfib1_int : Integrable (fun y => pX y * G (x - y)) volume := by
    refine hpX_int.mul_bdd
      (c := |A| * ((Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t))
        + 2 * |B| * ((Real.sqrt (Real.pi * t))⁻¹
            * (256 * Real.exp (-1) ^ 2 + 8 * Real.exp (-1)))) ?_ ?_
    · exact (hG_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, hG_def, abs_of_nonneg (hG_nn (x - y))]
      exact gaussHessMaj_polyWeight_bdd ht (abs_nonneg A) (by positivity) (x - y)
  -- (2) `fun y => (y²·pX y)·g(x−y)`: `g` globally bounded (`gaussHessMaj_bdd`) × `y²·pX` integ.
  have hfib2_int : Integrable (fun y => (y ^ 2 * pX y) * gaussHessMaj t (x - y)) volume := by
    refine hmomPX_int.mul_bdd
      (c := (Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t)) ?_ ?_
    · exact (hg_meas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn (x - y))]
      exact gaussHessMaj_bdd ht (x - y)
  -- target integrand integrability (for the LHS of `integral_mono`).
  have hlhs_int : Integrable
      (fun y => (|A| + |B| * x ^ 2) * (pX y * gaussHessMaj t (x - y))) volume :=
    hEnv_pos_int.const_mul _
  -- the dominating integrand: `pX y·G(x−y) + 2|B|·((y²pX)·g(x−y))`.
  have hdom_int : Integrable
      (fun y => pX y * G (x - y) + 2 * |B| * ((y ^ 2 * pX y) * gaussHessMaj t (x - y)))
      volume :=
    hfib1_int.add (hfib2_int.const_mul _)
  -- `H x = ∫ pX y·G(x−y) + 2|B|·∫(y²pX)·g(x−y) = ∫ [pX y·G(x−y) + 2|B|·(y²pX)·g(x−y)]`.
  have hH_eq : (∫ y, pX y * G (x - y) ∂volume)
        + 2 * |B| * (∫ y, (y ^ 2 * pX y) * gaussHessMaj t (x - y) ∂volume)
      = ∫ y, (pX y * G (x - y)
          + 2 * |B| * ((y ^ 2 * pX y) * gaussHessMaj t (x - y))) ∂volume := by
    rw [integral_add hfib1_int (hfib2_int.const_mul _), integral_const_mul]
  rw [hH_eq]
  -- pointwise: `(|A|+|B|x²)·pX y·g(x−y) ≤ pX y·G(x−y) + 2|B|·(y²pX)·g(x−y)`.
  refine integral_mono hlhs_int hdom_int (fun y => ?_)
  -- `(|A|+|B|x²) ≤ |A| + 2|B|(x−y)² + 2|B|y²` via `x² ≤ 2(x−y)²+2y²`, then multiply by `pX y·g ≥ 0`.
  have hpXg_nn : (0:ℝ) ≤ pX y * gaussHessMaj t (x - y) :=
    mul_nonneg (hpX_nn y) (hg_nn (x - y))
  have hx2 : x ^ 2 ≤ 2 * (x - y) ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - 2 * y), sq_nonneg x]
  have hcoef : (|A| + |B| * x ^ 2)
      ≤ (|A| + 2 * |B| * (x - y) ^ 2) + 2 * |B| * y ^ 2 := by
    have hBabs : (0:ℝ) ≤ |B| := abs_nonneg B
    nlinarith [mul_le_mul_of_nonneg_left hx2 hBabs]
  -- `G(x−y) = (|A|+2|B|(x−y)²)·g(x−y)`.
  have hGval : G (x - y) = (|A| + 2 * |B| * (x - y) ^ 2) * gaussHessMaj t (x - y) := by
    rw [hG_def]
  calc (|A| + |B| * x ^ 2) * (pX y * gaussHessMaj t (x - y))
      ≤ ((|A| + 2 * |B| * (x - y) ^ 2) + 2 * |B| * y ^ 2) * (pX y * gaussHessMaj t (x - y)) :=
        mul_le_mul_of_nonneg_right hcoef hpXg_nn
    _ = pX y * G (x - y) + 2 * |B| * ((y ^ 2 * pX y) * gaussHessMaj t (x - y)) := by
        rw [hGval]; ring

/-- Produces an integrable majorant `bound` dominating the full entropy σ-derivand
`(- log (pPath s x) - 1) · ((1/2) · ∂²_x pPath s x)` uniformly over `s ∈ Set.Ioo (t/2) (2*t)`.
The majorant is the product `(A + B·x²) · ((1/2) · hessBound x)` of an `s`-uniform polynomial
majorant for the log factor (`convDensityAdd_logFactor_poly_majorant`) and the `s`-uniform
integrable Hessian envelope (`convDensityAdd_deriv2_poly_moment_majorant`). Its integrability is
established by Tonelli against the Gaussian moments of the kernel, which collapses the outer
integral to the mass, first, and second moments of `pX` — all finite under `hpX_mass` and
`hpX_mom`.

@audit:ok -/
theorem debruijnIdentityV2_holds_assembled_chain_domination
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      (∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖(- Real.log (convDensityAdd pX
              (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩) x) - 1)
            * ((1/2) * deriv (deriv (convDensityAdd pX
              (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩))) x)‖
          ≤ bound x) := by
  -- Joint domination: the σ-derivand at `s` is the product
  --   LogFactor(s,x) = - log (p_s x) - 1     (poly-in-x growth, `A + B·x²`)
  --   (1/2)·Hess(s,x) = (1/2)·∂²_x p_s x     (integrable envelope `(1/2)·hessBound x`).
  -- GAP① gives an `s`-uniform polynomial majorant for the log factor;
  -- GAP② (poly-moment restate) gives an `s`-uniform integrable envelope `hessBound` for the Hessian.
  obtain ⟨A, B, _hB_nn, hLog⟩ :=
    convDensityAdd_logFactor_poly_majorant pX hpX_nn hpX_meas hpX_int hpX_mass ht
  -- The **concrete** envelope `E x = ∫ y, pX y · gaussHessMaj t (x − y)` (= GAP②'s in-body envelope),
  -- used directly here so that route II Tonelli sees the convolution shape (not an abstract `∃`).
  set E : ℝ → ℝ := fun x => ∫ y, pX y * gaussHessMaj t (x - y) ∂volume with hE_def
  -- the joint majorant: (A + B·x²) · ((1/2)·E x).
  refine ⟨fun x => (A + B * x ^ 2) * ((1/2) * E x), ?_, ?_⟩
  · -- the joint majorant integrability, extracted to `convDensityAdd_jointMajorant_integrable`.
    -- `E` is a `set` variable defeq to its expansion `∫ y, pX y · gaussHessMaj t (x − y)`.
    exact convDensityAdd_jointMajorant_integrable pX hpX_nn hpX_meas hpX_int hpX_mom ht A B
  · -- domination: `‖LogFactor · (1/2 · Hess)‖ ≤ (A + B·x²)·((1/2)·E x)`, genuine via norm_mul.
    --   the Hessian bound `‖∂²p_s x‖ ≤ E x` is the concrete pointwise lemma.
    filter_upwards [hLog] with x hLogx
    intro s hs
    have hspos : (0:ℝ) < s := by have := hs.1; linarith
    -- `‖a·b‖ = ‖a‖·‖b‖`, then bound each factor.
    rw [norm_mul]
    have hlf := hLogx s hs
    have hhf : ‖deriv (deriv (convDensityAdd pX
        (gaussianPDFReal 0 ⟨s, hspos.le⟩))) x‖ ≤ E x := by
      have := convDensityAdd_deriv2_le_gaussHessMaj_conv pX hpX_nn hpX_meas hpX_int ht x hs
      rwa [show (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩)
        = gaussianPDFReal 0 ⟨s, hspos.le⟩ from rfl] at this
    -- E x ≥ ‖Hess‖ ≥ 0, so the envelope is nonneg.
    have hE_nn : (0:ℝ) ≤ E x := le_trans (norm_nonneg _) hhf
    -- ‖(1/2)·Hess‖ = (1/2)·‖Hess‖ ≤ (1/2)·E x.
    have hhalf : ‖(1/2 : ℝ) * deriv (deriv (convDensityAdd pX
        (gaussianPDFReal 0 ⟨s, hspos.le⟩))) x‖
        ≤ (1/2) * E x := by
      rw [norm_mul]
      have hhn : ‖(1/2 : ℝ)‖ = 1/2 := by rw [Real.norm_eq_abs]; rw [abs_of_pos]; norm_num
      rw [hhn]
      exact mul_le_mul_of_nonneg_left hhf (by norm_num)
    -- combine: ‖LogFactor‖·‖(1/2)Hess‖ ≤ (A+B·x²)·((1/2)·E x).
    have hLog_nn : (0:ℝ) ≤ A + B * x ^ 2 := le_trans (norm_nonneg _) hlf
    calc ‖(- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hspos.le⟩) x) - 1)‖
            * ‖(1/2 : ℝ) * deriv (deriv (convDensityAdd pX
                (gaussianPDFReal 0 ⟨s, hspos.le⟩))) x‖
          ≤ (A + B * x ^ 2) * ((1/2) * E x) := by
            apply mul_le_mul hlf hhalf (norm_nonneg _) hLog_nn

end InformationTheory.Shannon.FisherInfoV2
