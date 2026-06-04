import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EPIConvDensity
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# EPI G2 層1 — 近似単位元の L¹ 収束 (`wall:approx-identity-L1` の核)

一般 L¹ 密度 `pX` (非負可測 + 有限2次モーメント) に対し、消えゆくガウス核との畳み込み
`convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩)` が `t→0⁺` で `pX` に **L¹ 収束** する
(`eLpNorm (conv − pX) 1 volume → 0`)。EPI G2 端点連続性を Vitali ルートで攻める際の
真の入力 (`docs/shannon/epi-g2-layer1-approx-identity-inventory.md`)。

数学的証明:
1. `∫ g_t = 1` (`integral_gaussianPDFReal_eq_one`) で差分表示
   `(pX ∗ g_t − pX)(z) = ∫ (pX(z−y) − pX(z)) g_t(y) dy`。
2. **連続版 Minkowski (L¹, Fubini 迂回)**: `‖∫ y, F(·,y) dν‖₁ ≤ ∫ y, ‖F(·,y)‖₁ dν`、
   `norm_integral_le_integral_norm` + `integral_integral_swap` (Tonelli)。
3. **L¹ 平行移動連続性**: `y ↦ ‖τ_y pX − pX‖₁ → 0` (`Lp.compMeasurePreserving_continuous`
   + `measurePreserving_sub_right` の翻訳)。
4. `g_t` の集中 (`t→0⁺`, 二次モーメント→0) で右辺 →0 (DCT)。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

/-- 右平行移動 `x ↦ x - y` を `C(ℝ, ℝ)` 元として束ねたもの。 -/
noncomputable def subRightCM (y : ℝ) : C(ℝ, ℝ) := ⟨fun x => x - y, by fun_prop⟩

/-- 平行移動族 `y ↦ subRightCM y` は `C(ℝ, ℝ)` の位相で連続。 -/
theorem continuous_subRightCM : Continuous subRightCM := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  unfold subRightCM
  simp only [ContinuousMap.coe_mk]
  fun_prop

/-- 各 `subRightCM y` は volume を保つ。 -/
theorem measurePreserving_subRightCM (y : ℝ) :
    MeasurePreserving (subRightCM y) volume volume :=
  measurePreserving_sub_right volume y

/-- **層1 補助 (genuine)**: L¹ 平行移動連続性。
`y ↦ eLpNorm (fun x => pX (x - y) - pX x) 1 volume` は `y → 0` で `→ 0`。
`Lp.compMeasurePreserving_continuous` + `measurePreserving_sub_right` の翻訳。
@audit:ok -/
theorem translation_continuous_L1
    {pX : ℝ → ℝ} (hpX_int : Integrable pX volume) :
    Tendsto (fun y : ℝ => eLpNorm (fun x => pX (x - y) - pX x) 1 volume) (𝓝 0) (𝓝 0) := by
  have hp : (1 : ℝ≥0∞) ≠ ∞ := by simp
  -- `pX` を `Lp ℝ 1 volume` の元に lift。
  have hmem : MemLp pX 1 volume := (memLp_one_iff_integrable).2 hpX_int
  set f₀ : Lp ℝ 1 volume := hmem.toLp pX with hf₀
  -- 平行移動族 `Lp.compMeasurePreserving (subRightCM y) (mp y) f₀` の `y` 連続性。
  have hcomp :
      Tendsto (fun y : ℝ =>
          Lp.compMeasurePreserving (subRightCM y) (measurePreserving_subRightCM y) f₀)
        (𝓝 0)
        (𝓝 (Lp.compMeasurePreserving (subRightCM 0) (measurePreserving_subRightCM 0) f₀)) := by
    have hf : Tendsto (fun _ : ℝ => f₀) (𝓝 0) (𝓝 f₀) := tendsto_const_nhds
    have hg : Tendsto subRightCM (𝓝 0) (𝓝 (subRightCM 0)) :=
      continuous_subRightCM.tendsto 0
    exact hf.compMeasurePreservingLp hg measurePreserving_subRightCM
      (measurePreserving_subRightCM 0) hp
  -- `compMeasurePreserving (subRightCM 0) ... f₀ = f₀` (subRightCM 0 = id, a.e.)。
  -- edist 連続性で `edist (g_y) (g_0)` の `→ 0` を得る。
  have hedist :
      Tendsto (fun y : ℝ =>
          edist (Lp.compMeasurePreserving (subRightCM y) (measurePreserving_subRightCM y) f₀)
            (Lp.compMeasurePreserving (subRightCM 0) (measurePreserving_subRightCM 0) f₀))
        (𝓝 0) (𝓝 0) := by
    have := hcomp.edist
      (tendsto_const_nhds (x :=
        Lp.compMeasurePreserving (subRightCM 0) (measurePreserving_subRightCM 0) f₀))
    simpa using this
  -- edist を eLpNorm に翻訳し、被積分を a.e. で `pX (x - y) - pX x` に同定。
  refine hedist.congr' ?_
  filter_upwards with y
  rw [Lp.edist_def]
  refine eLpNorm_congr_ae ?_
  have hy := Lp.coeFn_compMeasurePreserving f₀ (measurePreserving_subRightCM y)
  have h0 := Lp.coeFn_compMeasurePreserving f₀ (measurePreserving_subRightCM 0)
  have hc := hmem.coeFn_toLp
  -- `f₀ =ᵐ pX` を平行移動 `· - y` (測度保存) で押して `f₀ (· - y) =ᵐ pX (· - y)` を得る。
  have hcy : (fun x => (f₀ : ℝ → ℝ) (x - y)) =ᵐ[volume] (fun x => pX (x - y)) := by
    have := (measurePreserving_subRightCM y).quasiMeasurePreserving.ae_eq_comp hc
    simpa [subRightCM, Function.comp] using this
  filter_upwards [hy, h0, hc, hcy] with x hyx h0x hcx hcyx
  simp only [Pi.sub_apply]
  rw [hyx, h0x]
  simp only [Function.comp_apply, subRightCM, ContinuousMap.coe_mk, sub_zero]
  rw [hcx, hcyx]

/-- **層1 補助 (genuine)**: 平行移動 L¹ ノルムの有界性 `≤ 2 ‖pX‖₁`。
@audit:ok -/
theorem translation_eLpNorm_bound
    {pX : ℝ → ℝ} (hpX_int : Integrable pX volume) (y : ℝ) :
    eLpNorm (fun x => pX (x - y) - pX x) 1 volume ≤ 2 * eLpNorm pX 1 volume := by
  have hmeas : AEStronglyMeasurable pX volume := hpX_int.aestronglyMeasurable
  -- `τ_y pX = pX ∘ (· - y)`、平行移動は測度保存なので eLpNorm 不変。
  have hmeasy : AEStronglyMeasurable (fun x => pX (x - y)) volume :=
    hmeas.comp_measurePreserving (measurePreserving_subRightCM y)
  have htri := eLpNorm_sub_le (μ := volume) (p := 1) hmeasy hmeas le_rfl
  have hinv : eLpNorm (fun x => pX (x - y)) 1 volume = eLpNorm pX 1 volume :=
    eLpNorm_comp_measurePreserving (p := 1) hmeas (measurePreserving_subRightCM y)
  have hsub : (fun x => pX (x - y) - pX x) = (fun x => pX (x - y)) - pX := by
    funext x; simp [Pi.sub_apply]
  rw [hinv] at htri
  rw [hsub]
  calc eLpNorm ((fun x => pX (x - y)) - pX) 1 volume
      ≤ eLpNorm pX 1 volume + eLpNorm pX 1 volume := htri
    _ = 2 * eLpNorm pX 1 volume := by ring

/-- **層1 補助 (genuine)**: 差分表示。`∫ g = 1` のとき
`(pX ∗ g − pX)(z) = ∫ y, (pX(z−y) − pX(z)) · g y`。
`hi1`/`hi2` は被積分の可積分性 (regularity precondition)。
@audit:ok -/
theorem convDensityAdd_sub_self_eq
    {pX : ℝ → ℝ} (g : ℝ → ℝ) (hg_one : ∫ y, g y = 1) (z : ℝ)
    (hi1 : Integrable (fun y => pX (z - y) * g y) volume)
    (hi2 : Integrable (fun y => pX z * g y) volume) :
    EPIConvDensity.convDensityAdd pX g z - pX z
      = ∫ y, (pX (z - y) - pX z) * g y := by
  unfold EPIConvDensity.convDensityAdd
  have hrefl : ∫ x, pX x * g (z - x) = ∫ y, pX (z - y) * g y := by
    have h := MeasureTheory.integral_sub_left_eq_self
        (fun y => pX (z - y) * g y) (μ := volume) z
    simpa [sub_sub_cancel] using h
  have hsplit : ∫ y, (pX (z - y) - pX z) * g y
      = (∫ y, pX (z - y) * g y) - ∫ y, pX z * g y := by
    rw [← integral_sub hi1 hi2]; congr 1; funext y; rw [sub_mul]
  rw [hrefl, hsplit]
  have hpz : ∫ y, pX z * g y = pX z := by
    rw [integral_const_mul, hg_one, mul_one]
  rw [hpz]

/-- **層1 補助 (genuine)**: 連続版 Minkowski (L¹, Fubini 迂回, ℝ≥0∞ 形)。
`‖∫ y, F(·,y) dν‖₁ ≤ ∫⁻ y, ‖F(·,y)‖₁ dν`。`norm_integral_le_lintegral_norm` (enorm 形) +
`lintegral_lintegral_swap` (Tonelli) で初等。`hF` は joint 可測性 (regularity precondition)。
@audit:ok -/
theorem eLpNorm_integral_le_lintegral
    (F : ℝ → ℝ → ℝ) (ν : Measure ℝ) [SFinite ν]
    (hF : AEMeasurable (Function.uncurry F) (volume.prod ν)) :
    eLpNorm (fun z => ∫ y, F z y ∂ν) 1 volume
      ≤ ∫⁻ y, eLpNorm (fun z => F z y) 1 volume ∂ν := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  calc ∫⁻ z, ‖∫ y, F z y ∂ν‖ₑ ∂volume
      ≤ ∫⁻ z, ∫⁻ y, ‖F z y‖ₑ ∂ν ∂volume := by
        refine lintegral_mono fun z => enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ∫⁻ z, ‖F z y‖ₑ ∂volume ∂ν := by
        rw [lintegral_lintegral_swap]; exact hF.enorm
    _ = ∫⁻ y, eLpNorm (fun z => F z y) 1 volume ∂ν := by
        congr 1; funext y; rw [eLpNorm_one_eq_lintegral_enorm]

/-- **層1 核命題 (壁、組上げで genuine 化目標)**: 近似単位元 L¹ 収束。
平行移動連続 + 連続 Minkowski + Gauss 集中 (二次モーメント DCT) の組上げ。
仮説 hpX_nn/meas/int/mom は density regularity precondition (load-bearing でない、
結論の核を bundle していない)。wall 分類 honest (loogle: convolution+eLpNorm(+Tendsto)
= Found 0、独立 audit 2026-06-04 機械確認)。
@residual(wall:approx-identity-L1) -/
theorem convDensityAdd_tendsto_L1_zero
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) :
    Tendsto (fun t : ℝ =>
      eLpNorm (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) - pX) 1 volume)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  sorry

end InformationTheory.Shannon
