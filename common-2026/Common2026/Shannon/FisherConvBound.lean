import Common2026.Shannon.EPIConvDensity
import Common2026.Shannon.EPIConvDensitySecondDeriv          -- convDensityAdd_deriv1_gaussian_eq
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoV2DeBruijn   -- V2 Gaussian 閉形 J(𝒩(0,s))=1/s
import Common2026.Shannon.FisherInfoV2DeBruijnPerTime        -- convDensityAdd_pos / fisher_from_logDeriv
import Common2026.Shannon.StamGaussianBound       -- stam_fisher_arith
import Mathlib.MeasureTheory.Integral.Bochner.Basic          -- integral_mul_le_Lp_mul_Lq_of_nonneg
import Mathlib.MeasureTheory.Measure.Prod                    -- lintegral_lintegral_swap
import Mathlib.Probability.Distributions.Gaussian.Real       -- variance_fun_id_gaussianReal / integral_gaussianReal_eq_integral_smul

/-!
# Shared Mathlib wall — Stam convolution Fisher bound `J(pX ∗ g_s) ≤ 1/s`

EPI per-time de Bruijn line の shared 壁集約点 (`wall:fisher-finiteness`,
`docs/audit/audit-tags.md:70`)。Stam/Blachman の score-of-convolution monotonicity
`J(X + √s·Z) ≤ J(√s·Z) = J(𝒩(0,s)) = 1/s` を任意確率密度 `pX` (重い裾含む) で述べる。

## closure route (pointwise Cauchy-Schwarz, 2026-06-01)

closure plan の「conditional expectation / disintegration」framing を経由せず、
各 `x` を固定した elementary Hölder (p=q=2) で genuine 閉じる:

1. `convDensityAdd_deriv1_gaussian_eq` で `deriv p_s x = ∫ y, pX y · g_s(x-y)·(-(x-y)/s)`。
2. 各 `x` で `(∫ pX y (x-y) g_s(x-y))² ≤ p_s(x) · ∫ pX y (x-y)² g_s(x-y)` (CS)。
   ÷`p_s(x)>0` で `(logDeriv p_s x)²·p_s x ≤ (1/s²)·∫ pX y (x-y)² g_s(x-y)`。
3. lintegrand へ持ち上げ + merge。
4. Tonelli + Gaussian 2次モーメント `∫ u² g_s(u) du = s` ⇒ `(1/s²)·s·∫pX = 1/s`。

`hpX_mass : (∫ pX = 1)` を追加 (probability density の正規化、regularity precondition):
`convDensityAdd_pos` の `0 < ∫ pX` と最終段の `∫ pX = 1` に要る。

## consumer (2 件、`FisherInfoV2DeBruijnAssembly.lean`)

`convDensityAdd_fisher_integrable` (Step 3 plumbing で有限上界を `< ⊤` に使う) と、
それ経由の `_chain_ibp_fisher`。
-/

namespace Common2026.Shannon.FisherInfoV2

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)

/-- **Gaussian second moment over `volume`**: `∫ u, u² · g_s(u) du = s`
(`g_s = gaussianPDFReal 0 ⟨s,_⟩`, variance `s`).

Via `variance_fun_id_gaussianReal` (`Var[id; gaussianReal 0 s] = s`) +
`variance_eq_integral` (centered, mean `0`) + `integral_gaussianReal_eq_integral_smul`
(withDensity 橋). -/
theorem integral_sq_mul_gaussianPDFReal {s : ℝ} (hs : 0 < s) :
    ∫ u, u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u ∂volume = s := by
  have hv_ne : (⟨s, hs.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact hs.ne' (congrArg NNReal.toReal h)
  -- Var[id; 𝒩(0,s)] = ∫ (ω - 0)² ∂𝒩(0,s) = ∫ ω² ∂𝒩(0,s) = (s : ℝ).
  have hvar : Var[fun x => x; gaussianReal 0 ⟨s, hs.le⟩] = ((⟨s, hs.le⟩ : ℝ≥0) : ℝ) :=
    variance_fun_id_gaussianReal (μ := 0) (v := ⟨s, hs.le⟩)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hvar
  -- chain: `∫ u² g_s u du = ∫ u² ∂𝒩 = ∫ (u-0)² ∂𝒩 = s`.
  calc ∫ u, u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u ∂volume
      = ∫ u, gaussianPDFReal 0 ⟨s, hs.le⟩ u • u ^ 2 ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp [smul_eq_mul, mul_comm]
    _ = ∫ u, u ^ 2 ∂(gaussianReal 0 ⟨s, hs.le⟩) :=
        (integral_gaussianReal_eq_integral_smul (μ := 0) (f := fun u => u ^ 2) hv_ne).symm
    _ = ∫ u, (u - 0) ^ 2 ∂(gaussianReal 0 ⟨s, hs.le⟩) := by simp
    _ = s := by rw [hvar]

/-- **Per-`x` second-moment integrability**: `y ↦ (x-y)² · pX y · g_s(x-y)` is integrable
(`(x-y)² g_s(x-y)` is a bounded poly×Gaussian, hence `≤ C·|pX y|`, integrable). -/
theorem convSecondMoment_integrand_integrable
    (pX : ℝ → ℝ) (hpX_meas : Measurable pX) (hpX_int : Integrable pX volume)
    {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Integrable (fun y => (x - y) ^ 2 * (pX y * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y))) volume := by
  -- global bound for `u ↦ u² · g_s(u)`: `u² exp(-u²/(2s)) = 2s·(u²/(2s))·exp(-u²/(2s)) ≤ 2s·exp(-1)`.
  set C : ℝ := (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹ * (2 * s * Real.exp (-1)) with hC
  have hcoe : ((⟨s, hs.le⟩ : ℝ≥0) : ℝ) = s := rfl
  have hbnd : ∀ u : ℝ, u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u ≤ C := by
    intro u
    have h2s : (0 : ℝ) < 2 * s := by positivity
    -- `(u²/(2s)) · exp(-(u²/(2s))) ≤ exp(-1)`
    have hexp := Real.mul_exp_neg_le_exp_neg_one (u ^ 2 / (2 * s))
    have hpref_nn : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹ := by positivity
    -- unfold gaussianPDFReal (centered): `(√(2πs))⁻¹ · exp(-u²/(2s))`; coercion `↑⟨s,_⟩ = s` is defeq.
    rw [hC]
    show u ^ 2 * ((Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(u - 0) ^ 2 / (2 * s)))
      ≤ (Real.sqrt (2 * Real.pi * s))⁻¹ * (2 * s * Real.exp (-1))
    rw [sub_zero,
      show u ^ 2 * ((Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-u ^ 2 / (2 * s)))
          = (Real.sqrt (2 * Real.pi * s))⁻¹ * (u ^ 2 * Real.exp (-u ^ 2 / (2 * s))) from by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    -- `u² · exp(-u²/(2s)) ≤ 2s · exp(-1)`
    have heq : u ^ 2 * Real.exp (-u ^ 2 / (2 * s))
        = 2 * s * ((u ^ 2 / (2 * s)) * Real.exp (-(u ^ 2 / (2 * s)))) := by
      rw [neg_div]; field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hexp h2s.le
  -- now: integrand = `pX y · ((x-y)² · g_s(x-y))`, bounded factor measurable + ≤ C.
  have hgmeas : Measurable (fun y => (x - y) ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y)) := by
    refine (Measurable.pow_const (measurable_const.sub measurable_id) 2).mul ?_
    exact (measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp (measurable_const.sub measurable_id)
  have hint : Integrable
      (fun y => pX y * ((x - y) ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y))) volume := by
    refine hpX_int.mul_bdd (c := C) hgmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hnn : (0 : ℝ) ≤ (x - y) ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y) :=
      mul_nonneg (sq_nonneg _) (gaussianPDFReal_nonneg 0 _ _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hbnd (x - y)
  refine (integrable_congr (Filter.Eventually.of_forall fun y => ?_)).mpr hint
  ring

/-- **Pointwise Cauchy-Schwarz** (Hölder `p=q=2` over `volume`, per fixed `x`):
`(∫ pX y (x-y) g_s(x-y))² ≤ p_s(x) · ∫ pX y (x-y)² g_s(x-y)`. -/
theorem convScore_sq_le_pointwise
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    (∫ y, pX y * (x - y) * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y) ∂volume) ^ 2
      ≤ (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x)
        * (∫ y, (x - y) ^ 2 * (pX y * gaussianPDFReal 0 ⟨s, hs.le⟩ (x - y)) ∂volume) := by
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨s, hs.le⟩ with hg_def
  -- nonneg integrand `w y := pX y · g(x-y) ≥ 0`.
  have hw_nn : ∀ y, 0 ≤ pX y * g (x - y) := fun y =>
    mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- Hölder functions `a := |x-·|·√w`, `b := √w` (both nonneg).
  set a : ℝ → ℝ := fun y => |x - y| * Real.sqrt (pX y * g (x - y)) with ha_def
  set b : ℝ → ℝ := fun y => Real.sqrt (pX y * g (x - y)) with hb_def
  have ha_nn : 0 ≤ᵐ[volume] a :=
    Filter.Eventually.of_forall fun y => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hb_nn : 0 ≤ᵐ[volume] b :=
    Filter.Eventually.of_forall fun y => Real.sqrt_nonneg _
  -- measurability of `w` and its sqrt.
  have hw_meas : Measurable (fun y => pX y * g (x - y)) :=
    hpX_meas.mul ((measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp (measurable_const.sub measurable_id))
  -- integrability of `w := pX(x-·)·g` (= the convolution integrand, `pX` integrable × bounded Gaussian).
  have hw_int : Integrable (fun y => pX y * g (x - y)) volume := by
    refine hpX_int.mul_bdd (c := (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹) ?_ ?_
    · exact ((measurable_gaussianPDFReal 0 ⟨s, hs.le⟩).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 _ (x - y))]
      -- `g_s(u) = (√(2πs))⁻¹·exp(...) ≤ (√(2πs))⁻¹` since `exp(neg) ≤ 1`.
      rw [gaussianPDFReal]
      refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
      rw [neg_div]
      exact neg_nonpos.mpr (by positivity)
  -- `a·b = |x-y|·w`, `a² = (x-y)²·w`, `b² = w`.
  have hab : ∀ y, a y * b y = |x - y| * (pX y * g (x - y)) := by
    intro y
    simp only [ha_def, hb_def]
    rw [mul_assoc, Real.mul_self_sqrt (hw_nn y)]
  have ha_sq : ∀ y, a y ^ 2 = (x - y) ^ 2 * (pX y * g (x - y)) := by
    intro y
    simp only [ha_def, mul_pow, sq_abs, Real.sq_sqrt (hw_nn y)]
  have hb_sq : ∀ y, b y ^ 2 = pX y * g (x - y) := by
    intro y
    simp only [hb_def, Real.sq_sqrt (hw_nn y)]
  -- L² memberships.
  have hb_int : Integrable (fun y => b y ^ 2) volume :=
    (integrable_congr (Filter.Eventually.of_forall hb_sq)).mpr hw_int
  have ha_int : Integrable (fun y => a y ^ 2) volume := by
    refine (integrable_congr (Filter.Eventually.of_forall ha_sq)).mpr ?_
    simpa [hg_def] using convSecondMoment_integrand_integrable pX hpX_meas hpX_int hs x
  have ha_memLp : MemLp a (ENNReal.ofReal 2) volume := by
    rw [show (ENNReal.ofReal 2) = (2 : ℝ≥0∞) from by norm_num]
    refine (memLp_two_iff_integrable_sq ?_).mpr ?_
    · exact ((measurable_const.sub measurable_id).abs.mul
        (hw_meas.sqrt)).aestronglyMeasurable
    · exact ha_int
  have hb_memLp : MemLp b (ENNReal.ofReal 2) volume := by
    rw [show (ENNReal.ofReal 2) = (2 : ℝ≥0∞) from by norm_num]
    refine (memLp_two_iff_integrable_sq hw_meas.sqrt.aestronglyMeasurable).mpr hb_int
  -- Hölder (p = q = 2).
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq ha_nn hb_nn ha_memLp hb_memLp
  -- rewrite the three integrals to the `w`-form. Hölder's `^ p` are real powers `^ (2:ℝ)`;
  -- bridge them to the nat-power `^ 2` form via `a y ≥ 0`.
  have ha_rpow : ∀ y, a y ^ (2 : ℝ) = (x - y) ^ 2 * (pX y * g (x - y)) := by
    intro y
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast (a y) 2, ha_sq y]
  have hb_rpow : ∀ y, b y ^ (2 : ℝ) = pX y * g (x - y) := by
    intro y
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast (b y) 2, hb_sq y]
  simp only [hab, ha_rpow, hb_rpow] at hholder
  -- abbreviations for the two nonneg moment integrals.
  set I0 : ℝ := ∫ y, pX y * g (x - y) ∂volume with hI0
  set I2 : ℝ := ∫ y, (x - y) ^ 2 * (pX y * g (x - y)) ∂volume with hI2
  have hI0_nn : 0 ≤ I0 := integral_nonneg hw_nn
  have hI2_nn : 0 ≤ I2 := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hw_nn y)
  -- `hholder : ∫ |x-y|·w ≤ I2^(1/2)·I0^(1/2)`.
  -- LHS² ≥ (∫ pX(x-y)g)² and RHS² = I2·I0.
  have hconv_eq : convDensityAdd pX g x = I0 := by
    rw [hI0]; rfl
  -- `(∫ pX(x-y)g)² ≤ (∫ |x-y|·w)²`
  have habs_le : |∫ y, pX y * (x - y) * g (x - y) ∂volume|
      ≤ ∫ y, |x - y| * (pX y * g (x - y)) ∂volume := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    rw [show pX y * (x - y) * g (x - y) = (x - y) * (pX y * g (x - y)) from by ring,
      abs_mul, abs_of_nonneg (hw_nn y)]
  -- assemble.
  have hLHS_sq : (∫ y, pX y * (x - y) * g (x - y) ∂volume) ^ 2
      ≤ (∫ y, |x - y| * (pX y * g (x - y)) ∂volume) ^ 2 := by
    rw [← sq_abs (∫ y, pX y * (x - y) * g (x - y) ∂volume)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs_le 2
  refine hLHS_sq.trans ?_
  -- `(∫|x-y|·w)² ≤ (I2^½·I0^½)² = I2·I0`
  have hRHS : (∫ y, |x - y| * (pX y * g (x - y)) ∂volume) ^ 2 ≤ I2 * I0 := by
    have hint_nn : 0 ≤ ∫ y, |x - y| * (pX y * g (x - y)) ∂volume :=
      integral_nonneg fun y => mul_nonneg (abs_nonneg _) (hw_nn y)
    calc (∫ y, |x - y| * (pX y * g (x - y)) ∂volume) ^ 2
        ≤ (I2 ^ (1/2 : ℝ) * I0 ^ (1/2 : ℝ)) ^ 2 := by
          exact pow_le_pow_left₀ hint_nn hholder 2
      _ = I2 * I0 := by
          rw [mul_pow, ← Real.rpow_natCast (I2 ^ (1/2:ℝ)) 2, ← Real.rpow_natCast (I0 ^ (1/2:ℝ)) 2,
            ← Real.rpow_mul hI2_nn, ← Real.rpow_mul hI0_nn]
          norm_num
  rw [hconv_eq, mul_comm I0 I2]
  exact hRHS

/-- **Shared Mathlib wall: Stam convolution Fisher bound** `J(pX ∗ g_s) ≤ 1/s`.
任意確率密度 pX (重い裾含む) で成立。EPI per-time line の 2 consumer を gate
(`convDensityAdd_fisher_integrable` / `_chain_ibp_fisher` via それ)。

closure route: pointwise Cauchy-Schwarz (file docstring 参照)。
@residual(wall:fisher-finiteness) -/
theorem gaussianConv_fisher_le_inv_var
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    {s : ℝ} (hs : 0 < s) :
    fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      ≤ ENNReal.ofReal (1 / s) := by
  sorry -- @residual(wall:fisher-finiteness)

end Common2026.Shannon.FisherInfoV2
