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

/-- 平行移動 L¹ ノルム `φ y := ‖τ_y pX − pX‖₁` (ℝ≥0∞ 値)。 -/
private noncomputable def translL1 (pX : ℝ → ℝ) (y : ℝ) : ℝ≥0∞ :=
  eLpNorm (fun z => pX (z - y) - pX z) 1 volume

/-- ガウス核 `g_v` の prefactor 一様上界 `g_v y ≤ (√(2πv))⁻¹` (elementary)。
@audit:ok -/
private theorem gaussianPDFReal_le_pref (v : ℝ≥0) (y : ℝ) :
    gaussianPDFReal 0 v y ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDFReal_def]
  have hc : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by positivity
  calc (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(y - 0) ^ 2 / (2 * v))
      ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        refine Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg ?_ ?_)
        · simp only [neg_nonpos]; positivity
        · positivity
    _ = (Real.sqrt (2 * Real.pi * v))⁻¹ := mul_one _

/-- **層1 補助 (genuine)**: 各 `t>0` で eLpNorm を `ψ t = ∫⁻ y, ofReal(g_t y) · φ y` で上から押さえる。
`convDensityAdd_sub_self_eq` による差分表示 + 連続版 Minkowski + 定数 `g_t y ≥ 0` の括り出し。
@audit:ok -/
private theorem convDensityAdd_eLpNorm_le_psi
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    eLpNorm (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) - pX) 1 volume
      ≤ ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 t.toNNReal y) * translL1 pX y ∂volume := by
  set v : ℝ≥0 := t.toNNReal with hv_def
  set g : ℝ → ℝ := gaussianPDFReal 0 v with hg_def
  have hv : v ≠ 0 := by
    rw [hv_def]; exact (Real.toNNReal_eq_zero.not.2 (not_le.2 ht))
  have hg_one : ∫ y, g y = 1 := integral_gaussianPDFReal_eq_one 0 hv
  have hg_meas : Measurable g := measurable_gaussianPDFReal 0 v
  have hg_int : Integrable g volume := integrable_gaussianPDFReal 0 v
  have hg_nn : ∀ y, 0 ≤ g y := gaussianPDFReal_nonneg 0 v
  -- prefactor bound for `g`.
  set Cg : ℝ := (Real.sqrt (2 * Real.pi * v))⁻¹ with hCg_def
  have hg_bdd : ∀ y, ‖g y‖ ≤ Cg := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn y)]; exact gaussianPDFReal_le_pref v y
  -- `pX (z - ·)` is integrable (translation+reflection of `pX`).
  have hpXrefl_int : ∀ z : ℝ, Integrable (fun y => pX (z - y)) volume := fun z =>
    (Measure.measurePreserving_sub_left volume z).integrable_comp_of_integrable hpX_int
  -- per-`z` integrability of the two summands.
  have hi1 : ∀ z : ℝ, Integrable (fun y => pX (z - y) * g y) volume := fun z =>
    (hpXrefl_int z).mul_bdd hg_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall hg_bdd)
  have hi2 : ∀ z : ℝ, Integrable (fun y => pX z * g y) volume := fun z =>
    hg_int.const_mul (pX z)
  -- difference representation `(conv - pX)(z) = ∫ y, (pX(z-y)-pX z)·g y`.
  set F : ℝ → ℝ → ℝ := fun z y => (pX (z - y) - pX z) * g y with hF_def
  have hdiff : (EPIConvDensity.convDensityAdd pX g - pX)
      = fun z => ∫ y, F z y := by
    funext z
    simp only [Pi.sub_apply, hF_def]
    exact convDensityAdd_sub_self_eq g hg_one z (hi1 z) (hi2 z)
  -- joint measurability of `uncurry F`.
  have hFmeas : AEMeasurable (Function.uncurry F) (volume.prod volume) := by
    have hm : Measurable (Function.uncurry F) := by
      simp only [hF_def]
      apply Measurable.mul
      · exact (hpX_meas.comp (measurable_fst.sub measurable_snd)).sub
          (hpX_meas.comp measurable_fst)
      · exact hg_meas.comp measurable_snd
    exact hm.aemeasurable
  -- apply continuous Minkowski.
  calc eLpNorm (EPIConvDensity.convDensityAdd pX g - pX) 1 volume
      = eLpNorm (fun z => ∫ y, F z y) 1 volume := by rw [hdiff]
    _ ≤ ∫⁻ y, eLpNorm (fun z => F z y) 1 volume ∂volume :=
        eLpNorm_integral_le_lintegral F volume hFmeas
    _ = ∫⁻ y, ENNReal.ofReal (g y) * translL1 pX y ∂volume := by
        refine lintegral_congr fun y => ?_
        -- pull constant `g y ≥ 0` out of the inner eLpNorm.
        have hrw : (fun z => F z y) = (g y) • (fun z => pX (z - y) - pX z) := by
          funext z; simp only [hF_def, Pi.smul_apply, smul_eq_mul, mul_comm]
        rw [hrw, eLpNorm_const_smul, translL1]
        congr 1
        rw [Real.enorm_eq_ofReal (hg_nn y)]

/-- **Gaussian 二次モーメント** `∫ u² · g_s u = s` (`g_s = gaussianPDFReal 0 ⟨s,_⟩`、分散 `s`)。
`variance_fun_id_gaussianReal` + `integral_gaussianReal_eq_integral_smul` (Mathlib)。
NOTE: `FisherConvBound.integral_sq_mul_gaussianPDFReal` (`:56`, `@audit:ok`) と同一証明の
local 複製 (heavy import 回避目的)。将来 dedup 候補 (共通 lemma を軽量 module に切出し)。
@audit:ok -/
private theorem integral_sq_mul_gaussianPDFReal_local {s : ℝ} (hs : 0 < s) :
    ∫ u, u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u ∂volume = s := by
  have hv_ne : (⟨s, hs.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact hs.ne' (congrArg NNReal.toReal h)
  have hvar : Var[fun x => x; gaussianReal 0 ⟨s, hs.le⟩] = ((⟨s, hs.le⟩ : ℝ≥0) : ℝ) :=
    variance_fun_id_gaussianReal (μ := 0) (v := ⟨s, hs.le⟩)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at hvar
  calc ∫ u, u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u ∂volume
      = ∫ u, gaussianPDFReal 0 ⟨s, hs.le⟩ u • u ^ 2 ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp [smul_eq_mul, mul_comm]
    _ = ∫ u, u ^ 2 ∂(gaussianReal 0 ⟨s, hs.le⟩) :=
        (integral_gaussianReal_eq_integral_smul (μ := 0) (f := fun u => u ^ 2) hv_ne).symm
    _ = ∫ u, (u - 0) ^ 2 ∂(gaussianReal 0 ⟨s, hs.le⟩) := by simp
    _ = s := by rw [hvar]

/-- **Gaussian 二次モーメント可積分性** `Integrable (u ↦ u² · g_s u)`。
`u² = id² ∈ L²(gaussianReal)` を withDensity 橋で `volume` に移送。
@audit:ok -/
private theorem integrable_sq_mul_gaussianPDFReal_local {s : ℝ} (hs : 0 < s) :
    Integrable (fun u => u ^ 2 * gaussianPDFReal 0 ⟨s, hs.le⟩ u) volume := by
  have hv_ne : (⟨s, hs.le⟩ : ℝ≥0) ≠ 0 := by
    intro h; exact hs.ne' (congrArg NNReal.toReal h)
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 ⟨s, hs.le⟩) := memLp_id_gaussianReal 2
  have hsq_int : Integrable (fun u => u ^ 2) (gaussianReal 0 ⟨s, hs.le⟩) := by
    have := (memLp_two_iff_integrable_sq (μ := gaussianReal 0 ⟨s, hs.le⟩)
      (f := (id : ℝ → ℝ)) measurable_id.aestronglyMeasurable).mp hmem
    simpa using this
  rw [gaussianReal_of_var_ne_zero _ hv_ne] at hsq_int
  rw [integrable_withDensity_iff (measurable_gaussianPDF _ _)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hsq_int
  refine hsq_int.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]

/-- **Gaussian tail (Chebyshev)**: `∫⁻_{δ ≤ |y|} ofReal(g_t y) ≤ ofReal (t / δ²)`。
`{δ ≤ |y|}` 上 `1 ≤ y²/δ²` を使い、二次モーメント `∫ y² g_t = t` で押さえる。
@audit:ok -/
private theorem gaussianTail_lintegral_le {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) :
    ∫⁻ y in {y : ℝ | δ ≤ |y|}, ENNReal.ofReal (gaussianPDFReal 0 t.toNNReal y) ∂volume
      ≤ ENNReal.ofReal (t / δ ^ 2) := by
  have hv : t.toNNReal = (⟨t, ht.le⟩ : ℝ≥0) := by
    ext; exact Real.coe_toNNReal _ ht.le
  rw [hv]
  set g : ℝ → ℝ := gaussianPDFReal 0 ⟨t, ht.le⟩ with hg_def
  have hg_nn : ∀ y, 0 ≤ g y := gaussianPDFReal_nonneg 0 _
  -- on the tail set, `g y ≤ (y²/δ²) · g y` pointwise.
  have hpt : ∀ y ∈ {y : ℝ | δ ≤ |y|},
      ENNReal.ofReal (g y) ≤ ENNReal.ofReal (y ^ 2 / δ ^ 2 * g y) := by
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    apply ENNReal.ofReal_le_ofReal
    have h1 : 1 ≤ y ^ 2 / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      nlinarith [sq_abs y, abs_nonneg y, pow_le_pow_left₀ hδ.le hy 2]
    calc g y = 1 * g y := (one_mul _).symm
      _ ≤ (y ^ 2 / δ ^ 2) * g y := mul_le_mul_of_nonneg_right h1 (hg_nn y)
  calc ∫⁻ y in {y : ℝ | δ ≤ |y|}, ENNReal.ofReal (g y) ∂volume
      ≤ ∫⁻ y in {y : ℝ | δ ≤ |y|}, ENNReal.ofReal (y ^ 2 / δ ^ 2 * g y) ∂volume :=
        setLIntegral_mono' (by measurability) hpt
    _ ≤ ∫⁻ y, ENNReal.ofReal (y ^ 2 / δ ^ 2 * g y) ∂volume :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (t / δ ^ 2) := by
        have hint : Integrable (fun y => y ^ 2 / δ ^ 2 * g y) volume := by
          have := integrable_sq_mul_gaussianPDFReal_local (s := t) ht
          simpa [hg_def, div_eq_inv_mul, mul_assoc] using this.const_mul (δ ^ 2)⁻¹
        have hnn : 0 ≤ᵐ[volume] fun y => y ^ 2 / δ ^ 2 * g y :=
          Filter.Eventually.of_forall fun y =>
            mul_nonneg (by positivity) (hg_nn y)
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
        congr 1
        have hmom : ∫ u, u ^ 2 * g u ∂volume = t :=
          integral_sq_mul_gaussianPDFReal_local (s := t) ht
        calc ∫ y, y ^ 2 / δ ^ 2 * g y ∂volume
            = (δ ^ 2)⁻¹ * ∫ y, y ^ 2 * g y ∂volume := by
              rw [← integral_const_mul]; congr 1; funext y; ring
          _ = (δ ^ 2)⁻¹ * t := by rw [hmom]
          _ = t / δ ^ 2 := by ring

/-- **層1 補助 (genuine)**: `ψ t → 0` (`t→0⁺`)。Gauss 集中 (二次モーメント Chebyshev) + 平行移動連続性の DCT。
@audit:ok -/
private theorem psi_tendsto_zero
    {pX : ℝ → ℝ} (hpX_int : Integrable pX volume) :
    Tendsto (fun t : ℝ =>
        ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 t.toNNReal y) * translL1 pX y ∂volume)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  set φ : ℝ → ℝ≥0∞ := translL1 pX with hφ_def
  -- `C := ‖pX‖₁ < ∞`; `φ` is bounded by `2C` and `φ → 0` at `0`.
  set C : ℝ≥0∞ := eLpNorm pX 1 volume with hC_def
  have hC_ne : C ≠ ∞ := ((memLp_one_iff_integrable).2 hpX_int).eLpNorm_ne_top
  have hφ_bdd : ∀ y, φ y ≤ 2 * C := fun y => translation_eLpNorm_bound hpX_int y
  have hφ_tendsto : Tendsto φ (𝓝 0) (𝓝 0) := translation_continuous_L1 hpX_int
  have h2C_ne : (2 : ℝ≥0∞) * C ≠ ∞ := by
    simp [ENNReal.mul_ne_top, hC_ne]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- split `ε = ε/2 + ε/2`; pick δ so that `|y| < δ ⇒ φ y ≤ ε/2`.
  have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' (by simp)
  have hδ_ex : ∃ δ > (0 : ℝ), ∀ y : ℝ, |y| < δ → φ y ≤ ε / 2 := by
    have hball := (ENNReal.tendsto_nhds_zero.1 hφ_tendsto _ hε2)
    rw [Metric.eventually_nhds_iff] at hball
    obtain ⟨δ, hδ, hδ_le⟩ := hball
    exact ⟨δ, hδ, fun y hy => hδ_le (by rwa [Real.dist_eq, sub_zero])⟩
  obtain ⟨δ, hδ, hδ_le⟩ := hδ_ex
  -- the tail factor `2C · ofReal(t/δ²) → 0`, so eventually `≤ ε/2`.
  have htail_tendsto :
      Tendsto (fun t : ℝ => (2 * C) * ENNReal.ofReal (t / δ ^ 2)) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => ENNReal.ofReal (t / δ ^ 2)) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => t / δ ^ 2) (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
        have := (continuous_id.div_const (δ ^ 2)).continuousWithinAt (x := (0 : ℝ))
          (s := Set.Ioi 0)
        simpa using this.tendsto
      have hcont : Continuous fun r : ℝ => ENNReal.ofReal r := ENNReal.continuous_ofReal
      simpa using (hcont.tendsto 0).comp this
    have := ENNReal.Tendsto.const_mul (a := 2 * C) h0 (Or.inr h2C_ne)
    simpa using this
  have htail_ev : ∀ᶠ t in 𝓝[Set.Ioi 0] 0, (2 * C) * ENNReal.ofReal (t / δ ^ 2) ≤ ε / 2 :=
    ENNReal.tendsto_nhds_zero.1 htail_tendsto _ hε2
  -- assemble: on `𝓝[Ioi 0] 0`, `ψ t ≤ ε/2 + ε/2 = ε`.
  filter_upwards [htail_ev, self_mem_nhdsWithin] with t htail ht
  set g : ℝ → ℝ := gaussianPDFReal 0 t.toNNReal with hg_def
  have hv : t.toNNReal ≠ 0 := Real.toNNReal_eq_zero.not.2 (not_le.2 ht)
  have hg_meas : Measurable g := measurable_gaussianPDFReal 0 _
  -- measurable split set `A = {|y| < δ}` (open ⇒ measurable).
  set A : Set ℝ := {y : ℝ | |y| < δ} with hA_def
  have hA_meas : MeasurableSet A := by
    have : A = (fun y : ℝ => |y|) ⁻¹' Set.Iio δ := by ext y; simp [hA_def]
    rw [this]; exact (continuous_abs.measurable measurableSet_Iio)
  have hAc_eq : Aᶜ = {y : ℝ | δ ≤ |y|} := by
    ext y; simp [hA_def, not_lt]
  -- split the lintegral.
  have hsplit :
      (∫⁻ y, ENNReal.ofReal (g y) * φ y ∂volume)
        = (∫⁻ y in A, ENNReal.ofReal (g y) * φ y ∂volume)
          + ∫⁻ y in Aᶜ, ENNReal.ofReal (g y) * φ y ∂volume :=
    (lintegral_add_compl _ hA_meas).symm
  -- bound on `A`: `φ y ≤ ε/2`, and `∫_A ofReal(g) ≤ 1`.
  have hboundA :
      ∫⁻ y in A, ENNReal.ofReal (g y) * φ y ∂volume ≤ ε / 2 := by
    calc ∫⁻ y in A, ENNReal.ofReal (g y) * φ y ∂volume
        ≤ ∫⁻ y in A, ENNReal.ofReal (g y) * (ε / 2) ∂volume := by
          refine setLIntegral_mono_ae (by measurability) ?_
          refine Filter.Eventually.of_forall fun y hy => ?_
          exact mul_le_mul_left' (hδ_le y hy) _
      _ = (∫⁻ y in A, ENNReal.ofReal (g y) ∂volume) * (ε / 2) := by
          rw [lintegral_mul_const'' _ (hg_meas.ennreal_ofReal.aemeasurable)]
      _ ≤ 1 * (ε / 2) := by
          refine mul_le_mul_right' ?_ _
          calc ∫⁻ y in A, ENNReal.ofReal (g y) ∂volume
              ≤ ∫⁻ y, ENNReal.ofReal (g y) ∂volume := setLIntegral_le_lintegral _ _
            _ = 1 := lintegral_gaussianPDFReal_eq_one 0 hv
      _ = ε / 2 := one_mul _
  -- bound on `Aᶜ`: `φ y ≤ 2C`, and Chebyshev tail `∫_{Aᶜ} ofReal(g) ≤ ofReal(t/δ²)`.
  have hboundAc :
      ∫⁻ y in Aᶜ, ENNReal.ofReal (g y) * φ y ∂volume ≤ ε / 2 := by
    calc ∫⁻ y in Aᶜ, ENNReal.ofReal (g y) * φ y ∂volume
        ≤ ∫⁻ y in Aᶜ, ENNReal.ofReal (g y) * (2 * C) ∂volume := by
          refine setLIntegral_mono_ae (by measurability) ?_
          refine Filter.Eventually.of_forall fun y _ => ?_
          exact mul_le_mul_left' (hφ_bdd y) _
      _ = (∫⁻ y in Aᶜ, ENNReal.ofReal (g y) ∂volume) * (2 * C) := by
          rw [lintegral_mul_const'' _ (hg_meas.ennreal_ofReal.aemeasurable)]
      _ ≤ ENNReal.ofReal (t / δ ^ 2) * (2 * C) := by
          refine mul_le_mul_right' ?_ _
          rw [hAc_eq]
          exact gaussianTail_lintegral_le ht hδ
      _ = (2 * C) * ENNReal.ofReal (t / δ ^ 2) := mul_comm _ _
      _ ≤ ε / 2 := htail
  calc ∫⁻ y, ENNReal.ofReal (g y) * φ y ∂volume
      = (∫⁻ y in A, ENNReal.ofReal (g y) * φ y ∂volume)
          + ∫⁻ y in Aᶜ, ENNReal.ofReal (g y) * φ y ∂volume := hsplit
    _ ≤ ε / 2 + ε / 2 := add_le_add hboundA hboundAc
    _ = ε := ENNReal.add_halves ε

/-- **層1 核命題 (genuine closure)**: 近似単位元 L¹ 収束。
平行移動連続 (`translation_continuous_L1`) + 連続版 Minkowski (`eLpNorm_integral_le_lintegral`) +
Gauss 集中 (二次モーメント Chebyshev `gaussianTail_lintegral_le`) の squeeze で組上げ。
内部分解: `convDensityAdd_eLpNorm_le_psi` (各 t で `eLpNorm ≤ ψ t`) + `psi_tendsto_zero`
(`ψ t → 0`、ε-δ 分割 `{|y|<δ}`/`{δ≤|y|}` + tail `2C·ofReal(t/δ²)→0`)。
仮説 hpX_nn/meas/int/mom は density regularity precondition (load-bearing でない、
結論の核を bundle していない; hpX_nn/hpX_mom は実体不要だが public signature 上の正規化前提として保持)。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free、2026-06-04 機械確認)。
旧壁 `wall:approx-identity-L1` を genuine 化、もはや壁ではない。
@audit:ok -/
theorem convDensityAdd_tendsto_L1_zero
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) :
    Tendsto (fun t : ℝ =>
      eLpNorm (EPIConvDensity.convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) - pX) 1 volume)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  -- squeeze: `0 ≤ eLpNorm(...) ≤ ψ t → 0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (psi_tendsto_zero hpX_int) (Filter.Eventually.of_forall fun _ => zero_le') ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact convDensityAdd_eLpNorm_le_psi hpX_nn hpX_meas hpX_int ht

end InformationTheory.Shannon
