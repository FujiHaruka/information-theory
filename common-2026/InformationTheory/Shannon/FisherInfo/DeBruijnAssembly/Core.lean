import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.FisherInfo.DeBruijnPerTime
import InformationTheory.Shannon.FisherConvBound
import InformationTheory.Shannon.EPI.Conv.DensitySecondDeriv

namespace InformationTheory.Shannon.FisherInfo

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAddDeriv)

variable {Ω : Type*} {_mΩ : MeasurableSpace Ω}

/-! ## Chain-rule and regularity helpers for the per-time assembly

The named lemmas below are the regularity and chain-rule plumbing the assembly calls to
build each atom of `debruijnIdentityV2_holds_assembled`. Convention:
`pPath σ x := convDensityAdd pX (gaussianPDFReal 0 ⟨σ, _⟩) x`. -/

/-- The per-`x` entropy-integrand chain rule: at `x` with `pPath t x ≠ 0`,
`(d/ds) negMulLog (pPath s x)|_{s=t} = (- log (pPath t x) - 1) · D`, where `D` is the
σ-derivative `∂_s pPath t x` supplied as a `HasDerivAt` witness. Derived via `HasDerivAt.comp`
from `Real.hasDerivAt_negMulLog`.

@audit:ok -/
theorem debruijnIdentityV2_holds_assembled_chain_entDeriv_formula
    (pX : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) (D : ℝ)
    (hpos : convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ≠ 0)
    (hpath_deriv : HasDerivAt
      (fun s : ℝ => convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) D t) :
    HasDerivAt
      (fun s : ℝ => Real.negMulLog
        (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x))
      ((- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1) * D)
      t := by
  -- the inner path value at `t` is `pPath t x` (since `max t 0 = t`).
  have hmaxt : (⟨max t 0, le_max_right t 0⟩ : ℝ≥0) = ⟨t, ht.le⟩ := by
    apply NNReal.eq; exact max_eq_left ht.le
  -- `negMulLog` is differentiable at `pPath t x ≠ 0`, with derivative `-log(pPath t x) - 1`.
  have hneg : HasDerivAt Real.negMulLog
      (- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) - 1)
      (convDensityAdd pX (gaussianPDFReal 0 ⟨max t 0, le_max_right t 0⟩) x) := by
    rw [hmaxt]
    exact Real.hasDerivAt_negMulLog hpos
  -- chain rule: `negMulLog ∘ (fun s => pPath s x)`.
  exact hneg.comp t hpath_deriv

/-- `x ↦ x^k · exp(-b · x²)` is Lebesgue-integrable for any `k : ℕ` and `b > 0`.

@audit:ok -/
private theorem integrable_natPow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) volume := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hrpow := integrable_rpow_mul_exp_neg_mul_sq hb hk
  -- bridge `x ^ (k:ℝ)` (rpow) to `x ^ k` (pow): equal everywhere by `Real.rpow_natCast`.
  have hcongr : (fun x : ℝ => x ^ (k : ℝ) * Real.exp (-b * x ^ 2))
      = fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2) := by
    funext x; rw [Real.rpow_natCast]
  rwa [hcongr] at hrpow

/-- The centered Gaussian density is bounded above by its normalizing prefactor `(√(2πv))⁻¹`.

@audit:ok -/
theorem gaussianPDFReal_le_prefactor' (v : ℝ≥0) (u : ℝ) :
    gaussianPDFReal 0 v u ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal]
  have hpref_nn : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  have hexp_le : Real.exp (-(u - 0) ^ 2 / (2 * v)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (u - 0) ^ 2 / (2 * v) := by positivity
    linarith [neg_div (2 * (v : ℝ)) ((u - 0) ^ 2)]
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(u - 0) ^ 2 / (2 * v))
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp_le hpref_nn
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ := mul_one _

/-- For a probability density `pX`, the convolution density `p_s x = ∫ pX y · g_s(x − y)` is
bounded above by the Gaussian prefactor `(√(2πs))⁻¹`, uniformly in `x`.

@audit:ok -/
private theorem convDensityAdd_le_prefactor
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {s : ℝ} (hs : 0 < s) (x : ℝ) :
    convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x
      ≤ (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹ := by
  set pref : ℝ := (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹ with hpref
  have hpref_nn : 0 ≤ pref := by rw [hpref]; positivity
  -- integrand `F y := pX y * g_s(x-y)` integrable; majorant `pX y * pref` integrable.
  have hF_int : Integrable (fun y => pX y * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y)) volume := by
    refine hpX_int.mul_bdd (c := pref) ?_ ?_
    · exact ((measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ (x - y))]
      exact gaussianPDFReal_le_prefactor' ⟨s, hs.le⟩ (x - y)
  have hmaj_int : Integrable (fun y => pX y * pref) volume := hpX_int.mul_const _
  -- `∫ F ≤ ∫ (pX · pref) = pref · ∫ pX = pref`.
  have hle : (∫ y, pX y * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y) ∂volume)
      ≤ ∫ y, pX y * pref ∂volume := by
    refine integral_mono hF_int hmaj_int (fun y => ?_)
    exact mul_le_mul_of_nonneg_left (gaussianPDFReal_le_prefactor' ⟨s, hs.le⟩ (x - y)) (hpX_nn y)
  rwa [integral_mul_const, hpX_mass, one_mul] at hle

/-- Monotonicity of the centered Gaussian pdf in `|·|`: if `|u| ≤ |w|` then `g_v(w) ≤ g_v(u)`.

@audit:ok -/
private theorem gaussianPDFReal_antitone_abs'
    (v : ℝ≥0) {u w : ℝ} (huw : |u| ≤ |w|) :
    gaussianPDFReal 0 v w ≤ gaussianPDFReal 0 v u := by
  simp only [gaussianPDFReal, sub_zero]
  have hpref_nn : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpref_nn
  rw [Real.exp_le_exp]
  have hsq : u ^ 2 ≤ w ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg u) huw 2
    rwa [sq_abs, sq_abs] at this
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ 2 * v from by positivity) with hv0 | hvpos
  · rw [← hv0]; simp
  · rw [neg_div, neg_div, neg_le_neg_iff]; gcongr

/-- A single tightness radius `R > 0`, independent of `s`, with
`(1/2) · g_s(|x| + R) ≤ convDensityAdd pX g_s x` for every `s > 0` and `x`. The tightness
condition `∫_{[-R,R]} pX ≥ 1/2` depends only on `pX`, so the radius is reused across all `s`.

@audit:ok -/
private theorem convDensityAdd_lower_bound_gaussian_uniformR
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    (hpX_mass : (∫ y, pX y ∂volume) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ (s : ℝ) (hs : 0 < s) (x : ℝ),
      (1/2) * gaussianPDFReal 0 ⟨s, hs.le⟩ (|x| + R)
        ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x := by
  classical
  -- STEP 1 (tightness, `s`-independent): `∃ R > 0, ∫_{[-R,R]} pX ≥ 1/2`.
  obtain ⟨R, hR_pos, hR_mass⟩ :
      ∃ R : ℝ, 0 < R ∧ (1:ℝ)/2 ≤ ∫ y in Set.Icc (-R) R, pX y ∂volume := by
    set sN : ℕ → Set ℝ := fun n => Set.Icc (-(n:ℝ)) (n:ℝ) with hsN_def
    have hsN_meas : ∀ n, MeasurableSet (sN n) := fun n => measurableSet_Icc
    have hsN_mono : Monotone sN := by
      intro m n hmn
      apply Set.Icc_subset_Icc
      · exact neg_le_neg (by exact_mod_cast hmn)
      · exact_mod_cast hmn
    have hsN_union : (⋃ n, sN n) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro y
      obtain ⟨n, hn⟩ := exists_nat_ge |y|
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      rw [hsN_def]; simp only [Set.mem_Icc]
      rw [abs_le] at hn; exact ⟨hn.1, hn.2⟩
    have hfi : IntegrableOn pX (⋃ n, sN n) volume := by
      rw [hsN_union]; exact hpX_int.integrableOn
    have htends := tendsto_setIntegral_of_monotone hsN_meas hsN_mono hfi
    rw [hsN_union, setIntegral_univ, hpX_mass] at htends
    have hev : ∀ᶠ n in Filter.atTop, (1:ℝ)/2 < ∫ y in sN n, pX y ∂volume :=
      htends.eventually (eventually_gt_nhds (by norm_num : (1:ℝ)/2 < 1))
    obtain ⟨N, hN⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
    refine ⟨(N:ℝ), by exact_mod_cast hN.2, ?_⟩
    rw [hsN_def] at hN; exact hN.1.le
  refine ⟨R, hR_pos, fun s hs x => ?_⟩
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨s, hs.le⟩ with hg_def
  -- integrand `F y := pX y * g (x - y)` nonnegative + integrable.
  set F : ℝ → ℝ := fun y => pX y * g (x - y) with hF_def
  have hF_nn : ∀ y, 0 ≤ F y := fun y => mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ (x - y))
  have hF_int : Integrable F volume := by
    refine hpX_int.mul_bdd (c := (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact ((measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ (x - y))]
      exact gaussianPDFReal_le_prefactor' ⟨s, hs.le⟩ (x - y)
  -- STEP 2: drop the integral to the box `Icc (-R) R`.
  have hbox_le : (∫ y in Set.Icc (-R) R, F y ∂volume) ≤ ∫ y, F y ∂volume :=
    setIntegral_le_integral hF_int (Filter.Eventually.of_forall hF_nn)
  -- STEP 3: on the box, `g (x-y) ≥ g (|x| + R)`.
  have hbox_lb : (1/2) * g (|x| + R) ≤ ∫ y in Set.Icc (-R) R, F y ∂volume := by
    have hxR_nn : 0 ≤ |x| + R := add_nonneg (abs_nonneg x) hR_pos.le
    have hpt : ∀ y ∈ Set.Icc (-R) R, pX y * g (|x| + R) ≤ F y := by
      intro y hy
      have hy_abs : |x - y| ≤ |x| + R := by
        have h1 : |x - y| ≤ |x| + |y| := abs_sub _ _
        have h2 : |y| ≤ R := abs_le.mpr ⟨hy.1, hy.2⟩
        linarith
      have hmono : g (|x| + R) ≤ g (x - y) := by
        rw [hg_def]
        refine gaussianPDFReal_antitone_abs' ⟨s, hs.le⟩ ?_
        rwa [abs_of_nonneg hxR_nn]
      exact mul_le_mul_of_nonneg_left hmono (hpX_nn y)
    have hlb_int : IntegrableOn (fun y => pX y * g (|x| + R)) (Set.Icc (-R) R) volume :=
      hpX_int.integrableOn.mul_const _
    have hstep : (∫ y in Set.Icc (-R) R, pX y * g (|x| + R) ∂volume)
        ≤ ∫ y in Set.Icc (-R) R, F y ∂volume :=
      setIntegral_mono_on hlb_int hF_int.integrableOn measurableSet_Icc hpt
    rw [integral_mul_const] at hstep
    have hg_nn : 0 ≤ g (|x| + R) := by rw [hg_def]; exact gaussianPDFReal_nonneg 0 _ _
    have hhalf : g (|x| + R) * (1/2) ≤ g (|x| + R) * ∫ y in Set.Icc (-R) R, pX y ∂volume :=
      mul_le_mul_of_nonneg_left hR_mass hg_nn
    calc (1/2) * g (|x| + R)
        = g (|x| + R) * (1/2) := by ring
      _ ≤ g (|x| + R) * ∫ y in Set.Icc (-R) R, pX y ∂volume := hhalf
      _ = (∫ y in Set.Icc (-R) R, pX y ∂volume) * g (|x| + R) := by rw [mul_comm]
      _ ≤ ∫ y in Set.Icc (-R) R, F y ∂volume := hstep
  calc (1/2) * g (|x| + R)
      ≤ ∫ y in Set.Icc (-R) R, F y ∂volume := hbox_lb
    _ ≤ ∫ y, F y ∂volume := hbox_le
    _ = convDensityAdd pX g x := rfl

/-- On the neighborhood `Set.Ioo (t/2) (2*t)`, the entropy log-factor `- log (p_s x) - 1` of the
convolution density `p_s = convDensityAdd pX g_s` admits an `s`-uniform polynomial-in-`x²`
majorant `‖- log (p_s x) - 1‖ ≤ A + B·x²` with `B ≥ 0`. The upper bound comes from the
`s`-uniform Gaussian lower bound on `p_s` (`convDensityAdd_lower_bound_gaussian_uniformR`); the
lower bound from the prefactor upper bound on `p_s` (`convDensityAdd_le_prefactor`).

@audit:ok -/
theorem convDensityAdd_logFactor_poly_majorant
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (_hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {t : ℝ} (ht : 0 < t) :
    ∃ A B : ℝ, 0 ≤ B ∧
      ∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖- Real.log (convDensityAdd pX
            (gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩) x) - 1‖
          ≤ A + B * x ^ 2 := by
  -- positive mass from `∫ pX = 1` (for `convDensityAdd_pos`).
  have hpX_pos : 0 < ∫ y, pX y ∂volume := by rw [hpX_mass]; norm_num
  -- `s`-uniform tightness radius `R > 0` and the Gaussian lower bound.
  obtain ⟨R, hR_pos, hLB⟩ :=
    convDensityAdd_lower_bound_gaussian_uniformR pX hpX_nn hpX_int hpX_mass
  -- constants for the two-sided bound (`B = 2/t`; `A` covers both the upper polynomial
  -- offset and the lower constant, uniform over `s ∈ Ioo (t/2, 2t)`).
  set A_up : ℝ := Real.log 2 + (1/2) * Real.log (4 * Real.pi * t) + 2 * R ^ 2 / t - 1 with hA_up
  set A_lo : ℝ := 1 - (1/2) * Real.log (Real.pi * t) with hA_lo
  refine ⟨max A_up A_lo, 2 / t, by positivity, ?_⟩
  -- the bound is pointwise in `x`, holds for every `x` (so trivially a.e.).
  refine Filter.Eventually.of_forall (fun x s hs => ?_)
  have hspos : (0:ℝ) < s := by have := hs.1; linarith
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨s, hspos.le⟩ with hg_def
  set p : ℝ := convDensityAdd pX g x with hp_def
  -- `p > 0` and a closed form for `log` of the Gaussian prefactor.
  have hp_pos : 0 < p := by
    rw [hp_def, hg_def]; exact convDensityAdd_pos pX hpX_nn hpX_int hpX_pos hspos x
  have h2pis_pos : (0:ℝ) < 2 * Real.pi * s := by positivity
  have hpref_pos : (0:ℝ) < (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹ := by positivity
  have hcoe : ((⟨s, hspos.le⟩ : ℝ≥0) : ℝ) = s := rfl
  -- `log pref_s = -(1/2)·log(2πs)`.
  have hlog_pref : Real.log (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹
      = -((1/2) * Real.log (2 * Real.pi * s)) := by
    rw [Real.log_inv, hcoe, Real.log_sqrt h2pis_pos.le]; ring
  -- ============ upper side: `- log p - 1 ≤ A_up + (2/t)·x²` ============
  have hxR_nn : (0:ℝ) ≤ |x| + R := add_nonneg (abs_nonneg x) hR_pos.le
  -- lower bound on `p`: `(1/2)·g(|x|+R) ≤ p`, and `(1/2)·g(|x|+R) > 0`.
  have hlb := hLB s hspos x
  rw [← hg_def, ← hp_def] at hlb
  have hg_xR_pos : 0 < g (|x| + R) := by
    rw [hg_def]; exact gaussianPDFReal_pos 0 _ _ (by
      intro h; exact hspos.ne' (congrArg NNReal.toReal h))
  have hhalf_pos : (0:ℝ) < (1/2) * g (|x| + R) := by positivity
  -- `log p ≥ log ((1/2)·g(|x|+R))`.
  have hlog_lb : Real.log ((1/2) * g (|x| + R)) ≤ Real.log p := Real.log_le_log hhalf_pos hlb
  -- closed form: `log((1/2)·g(|x|+R)) = log(1/2) + log pref_s - (|x|+R)²/(2s)`.
  -- proved via the defeq natural unfold (RHS keeps the `- 0` and NNReal cast verbatim),
  -- then reshaped by the `s`-form equation `hlog_reshape`.
  have hlog_nat : Real.log ((1/2) * g (|x| + R))
      = Real.log (1/2) + (Real.log ((Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹)
        + -(|x| + R - 0) ^ 2 / (2 * s)) := by
    rw [hg_def]
    simp only [gaussianPDFReal]
    rw [Real.log_mul (by norm_num) (ne_of_gt (by positivity)),
      Real.log_mul (ne_of_gt (by positivity)) (Real.exp_ne_zero _), Real.log_exp]
    rfl
  have hlog_half : Real.log ((1/2) * g (|x| + R))
      = Real.log (1/2) + Real.log (Real.sqrt (2 * Real.pi * (⟨s, hspos.le⟩ : ℝ≥0)))⁻¹
        - (|x| + R) ^ 2 / (2 * s) := by
    rw [hlog_nat]; ring
  -- `(|x|+R)²/(2s) ≤ (2/t)·x² + 2R²/t` (using `s > t/2` and `2|x|R ≤ x²+R²`).
  have hquad : (|x| + R) ^ 2 / (2 * s) ≤ (2 / t) * x ^ 2 + 2 * R ^ 2 / t := by
    have h2s : t ≤ 2 * s := by have := hs.1; linarith
    have hnum : (|x| + R) ^ 2 ≤ 2 * x ^ 2 + 2 * R ^ 2 := by
      have hcross : 2 * |x| * R ≤ x ^ 2 + R ^ 2 := by
        nlinarith [sq_nonneg (|x| - R), sq_abs x]
      have hsplit : (|x| + R) ^ 2 = x ^ 2 + 2 * |x| * R + R ^ 2 := by
        rw [add_sq]; rw [sq_abs]
      rw [hsplit]; linarith
    calc (|x| + R) ^ 2 / (2 * s)
        ≤ (|x| + R) ^ 2 / t := div_le_div_of_nonneg_left (sq_nonneg _) ht h2s
      _ ≤ (2 * x ^ 2 + 2 * R ^ 2) / t := div_le_div_of_nonneg_right hnum ht.le
      _ = (2 / t) * x ^ 2 + 2 * R ^ 2 / t := by ring
  -- `(1/2)·log(2πs) ≤ (1/2)·log(4πt)` (using `s < 2t`).
  have hlog_2pis_up : (1/2) * Real.log (2 * Real.pi * s) ≤ (1/2) * Real.log (4 * Real.pi * t) := by
    have hle : 2 * Real.pi * s ≤ 4 * Real.pi * t := by
      have := hs.2; nlinarith [Real.pi_pos]
    have := Real.log_le_log h2pis_pos hle; linarith
  -- assemble the upper bound: `- log p ≤ log 2 + (1/2)log(2πs) + (|x|+R)²/(2s)`.
  have hupper : - Real.log p - 1 ≤ max A_up A_lo + (2 / t) * x ^ 2 := by
    have hstep : - Real.log p
        ≤ Real.log 2 + (1/2) * Real.log (2 * Real.pi * s) + (|x| + R) ^ 2 / (2 * s) := by
      have := hlog_lb
      rw [hlog_half, hlog_pref] at this
      have hlog2 : Real.log (1/2) = - Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]; ring
      rw [hlog2] at this
      linarith
    have : - Real.log p - 1
        ≤ Real.log 2 + (1/2) * Real.log (4 * Real.pi * t) + ((2 / t) * x ^ 2 + 2 * R ^ 2 / t) - 1 :=
      by linarith [hquad, hlog_2pis_up]
    have hAup : A_up + (2 / t) * x ^ 2
        = Real.log 2 + (1/2) * Real.log (4 * Real.pi * t) + ((2 / t) * x ^ 2 + 2 * R ^ 2 / t) - 1 :=
      by rw [hA_up]; ring
    calc - Real.log p - 1
        ≤ Real.log 2 + (1/2) * Real.log (4 * Real.pi * t) + ((2 / t) * x ^ 2 + 2 * R ^ 2 / t) - 1 :=
          this
      _ = A_up + (2 / t) * x ^ 2 := hAup.symm
      _ ≤ max A_up A_lo + (2 / t) * x ^ 2 := by
          gcongr; exact le_max_left _ _
  -- ============ lower side: `-(A + (2/t)x²) ≤ - log p - 1` ============
  -- `p ≤ pref_s` ⇒ `log p ≤ log pref_s = -(1/2)log(2πs)` ⇒ `- log p ≥ (1/2)log(2πs)`.
  have hp_le := convDensityAdd_le_prefactor pX hpX_nn hpX_int hpX_mass hspos x
  rw [← hg_def, ← hp_def] at hp_le
  have hlog_p_up : Real.log p ≤ -((1/2) * Real.log (2 * Real.pi * s)) := by
    have := Real.log_le_log hp_pos hp_le
    rwa [hlog_pref] at this
  -- `(1/2)log(πt) ≤ (1/2)log(2πs)` (using `2πs > πt`, i.e. `s > t/2`).
  have hlog_lo : (1/2) * Real.log (Real.pi * t) ≤ (1/2) * Real.log (2 * Real.pi * s) := by
    have hpit_pos : (0:ℝ) < Real.pi * t := by positivity
    have hle : Real.pi * t ≤ 2 * Real.pi * s := by
      have := hs.1; nlinarith [Real.pi_pos]
    have := Real.log_le_log hpit_pos hle; linarith
  have hlower : -(max A_up A_lo + (2 / t) * x ^ 2) ≤ - Real.log p - 1 := by
    -- `- log p ≥ (1/2)log(2πs) ≥ (1/2)log(πt)`, so `- log p - 1 ≥ (1/2)log(πt) - 1 = -A_lo`.
    have hge : (1/2) * Real.log (Real.pi * t) ≤ - Real.log p := by linarith [hlog_p_up, hlog_lo]
    have hAlo : -A_lo ≤ - Real.log p - 1 := by rw [hA_lo]; linarith
    have hnonpos : (0:ℝ) ≤ (2 / t) * x ^ 2 := by positivity
    calc -(max A_up A_lo + (2 / t) * x ^ 2)
        ≤ - max A_up A_lo := by linarith
      _ ≤ - A_lo := by apply neg_le_neg (le_max_right _ _)
      _ ≤ - Real.log p - 1 := hAlo
  -- combine into the `‖·‖` bound.
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hlower, hupper⟩

/-! ### The `s`-uniform Gaussian-Hessian majorant `gaussHessMaj t` -/

/-- The `s`-uniform Gaussian-Hessian kernel majorant on the window `s ∈ (t/2, 2t)`:
`g_s(u) · |u²/s² − 1/s| ≤ gaussHessMaj t u := (√(πt))⁻¹ · exp(−u²/(4t)) · (4u²/t² + 2/t)`,
a Gaussian times a quadratic.

@audit:ok -/
noncomputable def gaussHessMaj (t : ℝ) (u : ℝ) : ℝ :=
  (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2 + 2 / t)

/-- `gaussHessMaj t` is nonnegative.
@audit:ok -/
theorem gaussHessMaj_nonneg {t : ℝ} (ht : 0 < t) (u : ℝ) : 0 ≤ gaussHessMaj t u := by
  unfold gaussHessMaj
  have h1 : (0:ℝ) ≤ (Real.sqrt (Real.pi * t))⁻¹ := by positivity
  have h2 : (0:ℝ) ≤ Real.exp (-u ^ 2 / (4 * t)) := (Real.exp_pos _).le
  have h3 : (0:ℝ) ≤ 4 * u ^ 2 / t ^ 2 + 2 / t := by positivity
  positivity

/-- `gaussHessMaj t` is globally bounded.

@audit:ok -/
theorem gaussHessMaj_bdd {t : ℝ} (ht : 0 < t) :
    ∀ u : ℝ, gaussHessMaj t u
      ≤ (Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t) := by
  intro u
  unfold gaussHessMaj
  set P : ℝ := (Real.sqrt (Real.pi * t))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (4 * t)) := (Real.exp_pos _).le
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hP_nn
  -- `u²·exp(-u²/(4t)) ≤ 4t·exp(-1)` via `mul_exp_neg_le_exp_neg_one (u²/(4t))`.
  have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (4 * t))
  have hexp_eq : Real.exp (-(u ^ 2 / (4 * t))) = Real.exp (-u ^ 2 / (4 * t)) := by congr 1; ring
  rw [hexp_eq] at hmul
  have h4t : (0:ℝ) < 4 * t := by linarith
  have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) ≤ 4 * t * Real.exp (-1) := by
    have hmul' := mul_le_mul_of_nonneg_left hmul h4t.le
    have heq : (4 * t) * ((u ^ 2 / (4 * t)) * Real.exp (-u ^ 2 / (4 * t)))
        = u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) := by field_simp
    rw [heq] at hmul'; linarith [hmul']
  have hexp_le1 : Real.exp (-u ^ 2 / (4 * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ u ^ 2 / (4 * t) := by positivity
    linarith [neg_div (4 * t) (u ^ 2)]
  -- `exp·(4u²/t²+2/t) = 4/t²·(u²·exp) + 2/t·exp ≤ 4/t²·4t·exp(-1) + 2/t = 16·exp(-1)/t + 2/t`.
  have ht1 : Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2) ≤ 16 * Real.exp (-1) / t := by
    have heq : Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2)
        = (4 / t ^ 2) * (u ^ 2 * Real.exp (-u ^ 2 / (4 * t))) := by ring
    rw [heq]
    have h4t2 : (0:ℝ) ≤ 4 / t ^ 2 := by positivity
    calc (4 / t ^ 2) * (u ^ 2 * Real.exp (-u ^ 2 / (4 * t)))
        ≤ (4 / t ^ 2) * (4 * t * Real.exp (-1)) :=
          mul_le_mul_of_nonneg_left hu2 h4t2
      _ = 16 * Real.exp (-1) / t := by rw [pow_two]; field_simp; ring
  have ht2 : Real.exp (-u ^ 2 / (4 * t)) * (2 / t) ≤ 2 / t := by
    have h2t : (0:ℝ) ≤ 2 / t := by positivity
    calc Real.exp (-u ^ 2 / (4 * t)) * (2 / t) ≤ 1 * (2 / t) := by gcongr
      _ = 2 / t := one_mul _
  calc Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2 + 2 / t)
      = Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2)
        + Real.exp (-u ^ 2 / (4 * t)) * (2 / t) := by ring
    _ ≤ 16 * Real.exp (-1) / t + 2 / t := by linarith [ht1, ht2]

/-- `gaussHessMaj t` is Lebesgue-integrable (Gaussian × quadratic).
@audit:ok -/
theorem gaussHessMaj_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (gaussHessMaj t) volume := by
  have hb : (0:ℝ) < 1 / (4 * t) := by positivity
  -- the two Gaussian building blocks: `exp(-b u²)` and `|u|² · exp(-b u²)`.
  have hexp : Integrable (fun u : ℝ => Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
    integrable_exp_neg_mul_sq hb
  have hsq : Integrable (fun u : ℝ => u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume := by
    have := integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1:ℝ) < 2)
    refine this.congr (Filter.Eventually.of_forall (fun u => ?_))
    simp only [Real.rpow_two]
  -- assemble `gaussHessMaj` as a linear combination of the two.
  have hcomb : Integrable
      (fun u : ℝ => (Real.sqrt (Real.pi * t))⁻¹ * (4 / t ^ 2)
            * (u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2))
          + (Real.sqrt (Real.pi * t))⁻¹ * (2 / t)
            * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
    (hsq.const_mul _).add (hexp.const_mul _)
  refine hcomb.congr (Filter.Eventually.of_forall (fun u => ?_))
  -- pointwise: `gaussHessMaj t u = ` the combination.
  unfold gaussHessMaj
  have hexp_eq : Real.exp (-u ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * u ^ 2) := by
    congr 1; field_simp
  rw [hexp_eq]; ring

/-- For any constants `a b : ℝ`, the polynomial-weighted majorant `(a + b·u²) · gaussHessMaj t u`
is Lebesgue-integrable (a Gaussian times a quartic).

@audit:ok -/
theorem gaussHessMaj_polyWeight_integrable {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    Integrable (fun u : ℝ => (a + b * u ^ 2) * gaussHessMaj t u) volume := by
  have hbpos : (0:ℝ) < 1 / (4 * t) := by positivity
  -- the three Gaussian moment building blocks: `exp`, `u²·exp`, `u⁴·exp`.
  have hexp : Integrable (fun u : ℝ => Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
    integrable_exp_neg_mul_sq hbpos
  have hsq : Integrable (fun u : ℝ => u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume := by
    have := integrable_rpow_mul_exp_neg_mul_sq hbpos (by norm_num : (-1:ℝ) < 2)
    refine this.congr (Filter.Eventually.of_forall (fun u => ?_))
    simp only [Real.rpow_two]
  have hquart : Integrable (fun u : ℝ => u ^ 4 * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume := by
    have := integrable_rpow_mul_exp_neg_mul_sq hbpos (by norm_num : (-1:ℝ) < 4)
    refine this.congr (Filter.Eventually.of_forall (fun u => ?_))
    simp only []
    rw [show ((4:ℝ)) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  -- `(a+b·u²)·gaussHessMaj t u = c·exp·[(a + b·u²)·(4u²/t² + 2/t)]`
  --   = c·[ (4a/t² + 4b/t²·u² )·u² + (2a/t + 2b/t·u²) ]·exp  — a linear combo of exp, u²·exp, u⁴·exp.
  set c : ℝ := (Real.sqrt (Real.pi * t))⁻¹ with hc
  have hcomb : Integrable
      (fun u : ℝ =>
          c * (4 * b / t ^ 2) * (u ^ 4 * Real.exp (-(1 / (4 * t)) * u ^ 2))
        + (c * (4 * a / t ^ 2) + c * (2 * b / t))
            * (u ^ 2 * Real.exp (-(1 / (4 * t)) * u ^ 2))
        + c * (2 * a / t) * Real.exp (-(1 / (4 * t)) * u ^ 2)) volume :=
    ((hquart.const_mul _).add (hsq.const_mul _)).add (hexp.const_mul _)
  refine hcomb.congr (Filter.Eventually.of_forall (fun u => ?_))
  simp only []
  unfold gaussHessMaj
  have hexp_eq : Real.exp (-u ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * u ^ 2) := by
    congr 1; field_simp
  rw [hexp_eq, hc]; ring

/-- For nonneg constants `a b`, the polynomial-weighted majorant `(a + b·u²) · gaussHessMaj t u`
is globally bounded by an explicit constant.

@audit:ok -/
theorem gaussHessMaj_polyWeight_bdd {t : ℝ} (ht : 0 < t) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ u : ℝ, (a + b * u ^ 2) * gaussHessMaj t u
      ≤ a * ((Real.sqrt (Real.pi * t))⁻¹ * (16 * Real.exp (-1) / t + 2 / t))
        + b * ((Real.sqrt (Real.pi * t))⁻¹ * (256 * Real.exp (-1) ^ 2 + 8 * Real.exp (-1))) := by
  intro u
  set P : ℝ := (Real.sqrt (Real.pi * t))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  have hg_nn : (0:ℝ) ≤ gaussHessMaj t u := gaussHessMaj_nonneg ht u
  -- term `a·gaussHessMaj ≤ a·(P·(16e⁻¹/t+2/t))`.
  have hterm_a : a * gaussHessMaj t u ≤ a * (P * (16 * Real.exp (-1) / t + 2 / t)) :=
    mul_le_mul_of_nonneg_left (by rw [hP]; exact gaussHessMaj_bdd ht u) ha
  -- term `b·u²·gaussHessMaj ≤ b·(P·(256e⁻²+8e⁻¹))`.
  have hsqg : u ^ 2 * gaussHessMaj t u ≤ P * (256 * Real.exp (-1) ^ 2 + 8 * Real.exp (-1)) := by
    unfold gaussHessMaj
    rw [← hP]
    -- `u²·(P·exp(-u²/4t)·(4u²/t²+2/t)) = P·exp·(4u⁴/t² + 2u²/t)`.
    have h4t : (0:ℝ) < 4 * t := by linarith
    have h8t : (0:ℝ) < 8 * t := by linarith
    -- `u²·exp(-u²/4t) ≤ 4t·e⁻¹`.
    have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) ≤ 4 * t * Real.exp (-1) := by
      have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (4 * t))
      have hexp_eq : Real.exp (-(u ^ 2 / (4 * t))) = Real.exp (-u ^ 2 / (4 * t)) := by
        congr 1; ring
      rw [hexp_eq] at hmul
      have hmul' := mul_le_mul_of_nonneg_left hmul h4t.le
      have heq : (4 * t) * ((u ^ 2 / (4 * t)) * Real.exp (-u ^ 2 / (4 * t)))
          = u ^ 2 * Real.exp (-u ^ 2 / (4 * t)) := by field_simp
      rw [heq] at hmul'; linarith [hmul']
    -- `u²·exp(-u²/8t) ≤ 8t·e⁻¹`, then square to get `u⁴·exp(-u²/4t) ≤ (8t·e⁻¹)²`.
    have hu2_8 : u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) ≤ 8 * t * Real.exp (-1) := by
      have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (8 * t))
      have hexp_eq : Real.exp (-(u ^ 2 / (8 * t))) = Real.exp (-u ^ 2 / (8 * t)) := by
        congr 1; ring
      rw [hexp_eq] at hmul
      have hmul' := mul_le_mul_of_nonneg_left hmul h8t.le
      have heq : (8 * t) * ((u ^ 2 / (8 * t)) * Real.exp (-u ^ 2 / (8 * t)))
          = u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) := by field_simp
      rw [heq] at hmul'; linarith [hmul']
    have hu2_8_nn : (0:ℝ) ≤ u ^ 2 * Real.exp (-u ^ 2 / (8 * t)) := by positivity
    have hsplit : Real.exp (-u ^ 2 / (8 * t)) * Real.exp (-u ^ 2 / (8 * t))
        = Real.exp (-u ^ 2 / (4 * t)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have hu4 : u ^ 4 * Real.exp (-u ^ 2 / (4 * t)) ≤ (8 * t * Real.exp (-1)) ^ 2 := by
      have hsq := mul_le_mul hu2_8 hu2_8 hu2_8_nn (by positivity)
      have heq : (u ^ 2 * Real.exp (-u ^ 2 / (8 * t))) * (u ^ 2 * Real.exp (-u ^ 2 / (8 * t)))
          = u ^ 4 * Real.exp (-u ^ 2 / (4 * t)) := by
        rw [show u ^ 4 = u ^ 2 * u ^ 2 by ring, ← hsplit]; ring
      rw [heq] at hsq
      calc u ^ 4 * Real.exp (-u ^ 2 / (4 * t)) ≤ (8 * t * Real.exp (-1)) * (8 * t * Real.exp (-1)) :=
            hsq
        _ = (8 * t * Real.exp (-1)) ^ 2 := by ring
    -- assemble: `P·exp·(4u⁴/t²+2u²/t) = P·(4/t²·(u⁴·exp) + 2/t·(u²·exp))`
    --   ≤ P·(4/t²·64t²e⁻² + 2/t·4t·e⁻¹) = P·(256e⁻²+8e⁻¹).
    have hexpr : u ^ 2 * (P * Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2 + 2 / t))
        = P * ((4 / t ^ 2) * (u ^ 4 * Real.exp (-u ^ 2 / (4 * t)))
              + (2 / t) * (u ^ 2 * Real.exp (-u ^ 2 / (4 * t)))) := by
      rw [show u ^ 4 = u ^ 2 * u ^ 2 by ring]; ring
    rw [hexpr]
    apply mul_le_mul_of_nonneg_left _ hP_nn
    have h4t2 : (0:ℝ) ≤ 4 / t ^ 2 := by positivity
    have h2t : (0:ℝ) ≤ 2 / t := by positivity
    have hb1 : (4 / t ^ 2) * (u ^ 4 * Real.exp (-u ^ 2 / (4 * t)))
        ≤ (4 / t ^ 2) * (8 * t * Real.exp (-1)) ^ 2 := mul_le_mul_of_nonneg_left hu4 h4t2
    have hb2 : (2 / t) * (u ^ 2 * Real.exp (-u ^ 2 / (4 * t)))
        ≤ (2 / t) * (4 * t * Real.exp (-1)) := mul_le_mul_of_nonneg_left hu2 h2t
    have heval1 : (4 / t ^ 2) * (8 * t * Real.exp (-1)) ^ 2 = 256 * Real.exp (-1) ^ 2 := by
      rw [pow_two]; field_simp; ring
    have heval2 : (2 / t) * (4 * t * Real.exp (-1)) = 8 * Real.exp (-1) := by
      field_simp; ring
    rw [heval1] at hb1; rw [heval2] at hb2
    linarith [hb1, hb2]
  have hterm_b : b * (u ^ 2 * gaussHessMaj t u)
      ≤ b * (P * (256 * Real.exp (-1) ^ 2 + 8 * Real.exp (-1))) :=
    mul_le_mul_of_nonneg_left hsqg hb
  calc (a + b * u ^ 2) * gaussHessMaj t u
      = a * gaussHessMaj t u + b * (u ^ 2 * gaussHessMaj t u) := by ring
    _ ≤ a * (P * (16 * Real.exp (-1) / t + 2 / t))
          + b * (P * (256 * Real.exp (-1) ^ 2 + 8 * Real.exp (-1))) := by
        linarith [hterm_a, hterm_b]

/-- `s`-uniform pointwise majorant: for `s ∈ (t/2, 2t)`,
`g_s(u)·|u²/s² − 1/s| ≤ gaussHessMaj t u`.
@audit:ok -/
theorem gaussianHess_le_gaussHessMaj {t : ℝ} (ht : 0 < t) {s : ℝ}
    (hs : s ∈ Set.Ioo (t/2) (2*t)) (u : ℝ) :
    gaussianPDFReal 0 ⟨s, le_of_lt (by have := hs.1; linarith : (0:ℝ) < s)⟩ u
        * |u ^ 2 / s ^ 2 - 1 / s|
      ≤ gaussHessMaj t u := by
  have hspos : (0:ℝ) < s := by have := hs.1; linarith
  have ht2s : t < 2 * s := by have := hs.1; linarith
  have hs2t : s ≤ 2 * t := hs.2.le
  -- unfold the Gaussian: `(√(2πs))⁻¹ · exp(-u²/(2s))`.
  rw [gaussianPDFReal]
  simp only [sub_zero]
  -- prefactor bound: `(√(2πs))⁻¹ ≤ (√(πt))⁻¹`.
  have hpref : (Real.sqrt (2 * Real.pi * s))⁻¹ ≤ (Real.sqrt (Real.pi * t))⁻¹ := by
    apply inv_anti₀ (by positivity)
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_pos]
  -- exponent bound: `exp(-u²/(2s)) ≤ exp(-u²/(4t))`.
  have hexp : Real.exp (-u ^ 2 / (2 * s)) ≤ Real.exp (-u ^ 2 / (4 * t)) := by
    apply Real.exp_le_exp.2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg u]
  -- polynomial factor bound: `|u²/s² − 1/s| ≤ 4u²/t² + 2/t`.
  have hpoly : |u ^ 2 / s ^ 2 - 1 / s| ≤ 4 * u ^ 2 / t ^ 2 + 2 / t := by
    have h1 : u ^ 2 / s ^ 2 ≤ 4 * u ^ 2 / t ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have ht2 : t ^ 2 ≤ 4 * s ^ 2 := by nlinarith [hspos, ht]
      nlinarith [sq_nonneg u, ht2, mul_nonneg (sq_nonneg u) (sub_nonneg.2 ht2)]
    have h2 : 1 / s ≤ 2 / t := by
      rw [div_le_div_iff₀ hspos ht]; nlinarith
    have h3 : (0:ℝ) ≤ u ^ 2 / s ^ 2 := by positivity
    have h4 : (0:ℝ) ≤ 1 / s := by positivity
    rw [abs_le]
    constructor
    · nlinarith [h1, h2, h3, h4]
    · nlinarith [h1, h2, h3, h4]
  -- nonnegativity of all factors, then multiply the three bounds.
  have hpref_nn : (0:ℝ) ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ := by positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (2 * s)) := (Real.exp_pos _).le
  have habs_nn : (0:ℝ) ≤ |u ^ 2 / s ^ 2 - 1 / s| := abs_nonneg _
  have hprefT_nn : (0:ℝ) ≤ (Real.sqrt (Real.pi * t))⁻¹ := by positivity
  have hexpT_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (4 * t)) := (Real.exp_pos _).le
  unfold gaussHessMaj
  calc (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-u ^ 2 / (2 * s)) * |u ^ 2 / s ^ 2 - 1 / s|
      ≤ (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-u ^ 2 / (4 * t)) * (4 * u ^ 2 / t ^ 2 + 2 / t) := by
        apply mul_le_mul (mul_le_mul hpref hexp hexp_nn hprefT_nn) hpoly habs_nn
        exact mul_nonneg hprefT_nn hexpT_nn

/-- For an integrable kernel `K` and an integrable density `pX`, the convolution-shaped function
`x ↦ ∫ y, pX y · K (x − y)` is Lebesgue-integrable, via Tonelli on the product measure.

@audit:ok -/
theorem convKernel_envelope_integrable
    (pX K : ℝ → ℝ) (hpX_int : Integrable pX volume) (hpX_meas : Measurable pX)
    (hK_int : Integrable K volume) (hK_meas : Measurable K) :
    Integrable (fun x => ∫ y, pX y * K (x - y) ∂volume) volume := by
  -- the 2D integrand `f (x,y) = pX y · K (x − y)`.
  set f : ℝ × ℝ → ℝ := fun p => pX p.2 * K (p.1 - p.2) with hf_def
  -- a.e.-strong measurability of `f` on the product measure.
  have hf_meas : AEStronglyMeasurable f (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => pX p.2) (volume.prod volume) :=
      (hpX_meas.comp measurable_snd).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => K (p.1 - p.2)) (volume.prod volume) := by
      have hsub : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := measurable_fst.sub measurable_snd
      exact (hK_meas.comp hsub).aestronglyMeasurable
    exact h1.mul h2
  -- `f` is integrable on the product via `integrable_prod_iff'`.
  have hf_int : Integrable f (volume.prod volume) := by
    rw [integrable_prod_iff' hf_meas]
    refine ⟨?_, ?_⟩
    · -- for each `y`, `x ↦ pX y · K (x − y)` is integrable.
      refine Filter.Eventually.of_forall (fun y => ?_)
      exact (hK_int.comp_sub_right y).const_mul (pX y)
    · -- `y ↦ ∫ x ‖pX y · K(x−y)‖ dx = (∫‖K‖) · ‖pX y‖` is integrable.
      have hKnorm : Integrable (fun x => ‖K x‖) volume := hK_int.norm
      have heq : (fun y => ∫ x, ‖f (x, y)‖ ∂volume)
          = (fun y => ‖pX y‖ * ∫ x, ‖K x‖ ∂volume) := by
        funext y
        simp only [hf_def, norm_mul]
        rw [integral_const_mul]
        congr 1
        rw [← integral_sub_right_eq_self (fun x => ‖K x‖) y]
      rw [heq]
      exact (hpX_int.norm.mul_const _)
  -- conclude via `Integrable.integral_prod_left`.
  exact hf_int.integral_prod_left

/-- Public re-export of `convKernel_envelope_integrable` on the `convDensityAdd` shape, so
downstream `IsRegularDensityV2` producers can reuse it without the `private` helper:
`Integrable (convDensityAdd pX K) volume`.

@audit:ok -/
@[entry_point]
theorem convDensityAdd_envelope_integrable
    (pX K : ℝ → ℝ) (hpX_int : Integrable pX volume) (hpX_meas : Measurable pX)
    (hK_int : Integrable K volume) (hK_meas : Measurable K) :
    Integrable (convDensityAdd pX K) volume :=
  convKernel_envelope_integrable pX K hpX_int hpX_meas hK_int hK_meas

/-! ### Global sup bounds of the Gaussian kernel spatial derivatives -/

/-- Global sup bound of the kernel spatial first derivative `g_s(u) · (-(u/s))`.

@audit:ok -/
theorem kernel_x_deriv1_global_bound {s : ℝ} (hs : 0 < s) :
    ∀ u : ℝ, ‖heatFlow_density_heat_equation_kernel s u * (-(u / s))‖
      ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * ((1 + 2 * s * Real.exp (-1)) / (2 * s)) := by
  intro u
  unfold heatFlow_density_heat_equation_kernel
  set P : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (2 * s)) := (Real.exp_pos _).le
  -- ‖P·exp·(-(u/s))‖ = P·exp·(|u|/s)
  rw [norm_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hP_nn, abs_of_nonneg hexp_nn,
    Real.norm_eq_abs, abs_neg, abs_div, abs_of_pos hs]
  -- reduce to `exp·|u| ≤ (1+2s·exp(-1))/2`
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hP_nn
  -- key: `exp(-u²/(2s))·|u| ≤ (1+2s·exp(-1))/2`, then divide by `s`.
  have hkey : Real.exp (-u ^ 2 / (2 * s)) * |u| ≤ (1 + 2 * s * Real.exp (-1)) / 2 := by
    -- `2|u| ≤ 1 + u²`
    have h2u : 2 * |u| ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (|u| - 1), sq_abs u]
    -- `u²·exp(-u²/(2s)) ≤ 2s·exp(-1)` via `mul_exp_neg_le_exp_neg_one (u²/(2s))`
    have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (2 * s))
    have hexp_eq : Real.exp (-(u ^ 2 / (2 * s))) = Real.exp (-u ^ 2 / (2 * s)) := by
      congr 1; ring
    rw [hexp_eq] at hmul
    -- so `u²·exp ≤ 2s·exp(-1)`
    have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (2 * s)) ≤ 2 * s * Real.exp (-1) := by
      have h2s : (0:ℝ) < 2 * s := by linarith
      have hmul' := mul_le_mul_of_nonneg_left hmul h2s.le
      -- `2s·((u²/(2s))·exp) = u²·exp` and `2s·exp(-1)`
      have heq : (2 * s) * ((u ^ 2 / (2 * s)) * Real.exp (-u ^ 2 / (2 * s)))
          = u ^ 2 * Real.exp (-u ^ 2 / (2 * s)) := by field_simp
      rw [heq] at hmul'
      linarith [hmul']
    -- `exp ≤ 1`
    have hexp_le1 : Real.exp (-u ^ 2 / (2 * s)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ u ^ 2 / (2 * s) := by positivity
      linarith [neg_div (2 * s) (u ^ 2)]
    -- combine: `exp·|u| = exp·(2|u|)/2 ≤ exp·(1+u²)/2 = (exp + u²·exp)/2 ≤ (1 + 2s·exp(-1))/2`
    nlinarith [mul_le_mul_of_nonneg_left h2u hexp_nn, hu2, hexp_le1, abs_nonneg u]
  -- divide hkey by `s`
  calc Real.exp (-u ^ 2 / (2 * s)) * (|u| / s)
      = (Real.exp (-u ^ 2 / (2 * s)) * |u|) / s := by ring
    _ ≤ ((1 + 2 * s * Real.exp (-1)) / 2) / s := by gcongr
    _ = (1 + 2 * s * Real.exp (-1)) / (2 * s) := by ring

/-- Global sup bound of the kernel spatial 2nd derivative `g_s(u)·(u²/s²-1/s)`.
@audit:ok -/
theorem kernel_x_deriv2_global_bound {s : ℝ} (hs : 0 < s) :
    ∀ u : ℝ, ‖heatFlow_density_heat_equation_kernel s u * (u ^ 2 / s ^ 2 - 1 / s)‖
      ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * ((2 * Real.exp (-1) + 1) / s) := by
  intro u
  unfold heatFlow_density_heat_equation_kernel
  set P : ℝ := (Real.sqrt (2 * Real.pi * s))⁻¹ with hP
  have hP_nn : (0:ℝ) ≤ P := by rw [hP]; positivity
  have hexp_nn : (0:ℝ) ≤ Real.exp (-u ^ 2 / (2 * s)) := (Real.exp_pos _).le
  -- ‖P·exp·(u²/s²-1/s)‖ = P·exp·|u²/s²-1/s|
  rw [norm_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hP_nn, abs_of_nonneg hexp_nn,
    Real.norm_eq_abs]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hP_nn
  -- bound: exp·|u²/s²-1/s| ≤ exp·(u²/s²+1/s) ≤ (2·exp(-1)+1)/s
  -- `u²·exp(-u²/(2s)) ≤ 2s·exp(-1)`
  have hmul := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (2 * s))
  have hexp_eq : Real.exp (-(u ^ 2 / (2 * s))) = Real.exp (-u ^ 2 / (2 * s)) := by congr 1; ring
  rw [hexp_eq] at hmul
  have h2s : (0:ℝ) < 2 * s := by linarith
  have hu2 : u ^ 2 * Real.exp (-u ^ 2 / (2 * s)) ≤ 2 * s * Real.exp (-1) := by
    have hmul' := mul_le_mul_of_nonneg_left hmul h2s.le
    have heq : (2 * s) * ((u ^ 2 / (2 * s)) * Real.exp (-u ^ 2 / (2 * s)))
        = u ^ 2 * Real.exp (-u ^ 2 / (2 * s)) := by field_simp
    rw [heq] at hmul'; linarith [hmul']
  have hexp_le1 : Real.exp (-u ^ 2 / (2 * s)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ u ^ 2 / (2 * s) := by positivity
    linarith [neg_div (2 * s) (u ^ 2)]
  -- abs split + termwise bounds, all divided by appropriate powers of s
  have habs : |u ^ 2 / s ^ 2 - 1 / s| ≤ u ^ 2 / s ^ 2 + 1 / s := by
    have h1 : (0:ℝ) ≤ u ^ 2 / s ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ 1 / s := by positivity
    rw [abs_le]; constructor <;> nlinarith [h1, h2]
  -- `exp · u²/s² ≤ 2·exp(-1)/s` and `exp · 1/s ≤ 1/s`
  have hssq : (0:ℝ) < s ^ 2 := by positivity
  have ht1 : Real.exp (-u ^ 2 / (2 * s)) * (u ^ 2 / s ^ 2) ≤ 2 * Real.exp (-1) / s := by
    have : Real.exp (-u ^ 2 / (2 * s)) * (u ^ 2 / s ^ 2)
        = (u ^ 2 * Real.exp (-u ^ 2 / (2 * s))) / s ^ 2 := by ring
    rw [this]
    calc (u ^ 2 * Real.exp (-u ^ 2 / (2 * s))) / s ^ 2
        ≤ (2 * s * Real.exp (-1)) / s ^ 2 := by gcongr
      _ = 2 * Real.exp (-1) / s := by
            rw [pow_two, mul_comm s s, ← div_div]
            congr 1
            field_simp
  have ht2 : Real.exp (-u ^ 2 / (2 * s)) * (1 / s) ≤ 1 / s := by
    have : (0:ℝ) ≤ 1 / s := by positivity
    calc Real.exp (-u ^ 2 / (2 * s)) * (1 / s) ≤ 1 * (1 / s) := by gcongr
      _ = 1 / s := one_mul _
  calc Real.exp (-u ^ 2 / (2 * s)) * |u ^ 2 / s ^ 2 - 1 / s|
      ≤ Real.exp (-u ^ 2 / (2 * s)) * (u ^ 2 / s ^ 2 + 1 / s) :=
        mul_le_mul_of_nonneg_left habs hexp_nn
    _ = Real.exp (-u ^ 2 / (2 * s)) * (u ^ 2 / s ^ 2)
          + Real.exp (-u ^ 2 / (2 * s)) * (1 / s) := by ring
    _ ≤ 2 * Real.exp (-1) / s + 1 / s := by linarith [ht1, ht2]
    _ = (2 * Real.exp (-1) + 1) / s := by ring

end InformationTheory.Shannon.FisherInfo
