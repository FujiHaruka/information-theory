import InformationTheory.Shannon.EntropyPowerExt
import InformationTheory.Shannon.EPIUncondCondEntropyExt
import InformationTheory.Shannon.EPIUncondMonotone
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# EPI 無条件化 W-Y2 — route β' (truncation + monotone-limit) skeleton

無限エントロピー a.c. 入力 (`h(W) = ⊤` の a.c.) で gateway 単調性の ⊤ 伝播
`differentialEntropyExt_top_of_indep_add` を **無条件** (整数 truncation 近似経由) で
genuine 着地させるための skeleton。route T (`EPIInfiniteVarianceTruncation` /
`EPIInfiniteVarianceCapstone`、sorryAx-free CLOSED) の機構を `W` 単独 truncation に
読み替えて再利用する。

ターゲットは無条件版② chain rule の等式 (finiteness-free 証明不能確定) でなく、
gateway 単調性の ⊤ 枝不等式 (`h(W) = ⊤ ⟹ h(W+V) = ⊤`)。LSC/liminf は `≤` しか出さないが、
⊤ 枝は `le_top` 一発で閉じるため極限と相性が良い。

route β' Phase 1 skeleton (本 file は signature 確定のみ、本体は Phase 2-4)。

SoT 計画: `docs/shannon/epi-uncond-truncation-lsc-plan.md`
(Parent: `docs/shannon/epi-unconditional-moonshot-plan.md` §S5 W-Y2)。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **W 単独 truncation の構成** (route T `condTrunc` を W 単独に読み替え)。
`truncW P W n := P[| {ω | |W ω| ≤ n}]` (`W` の値が `[-n, n]` に入る事象での条件付け)。
各 `truncW P W n` は compact support (有界) → 有限分散・有限エントロピーを満たし、a.c.
(`cond_absolutelyContinuous` 保存) を保つ。route T の joint `truncSet X Y n` と違い W 単独。

独立 honesty audit 2026-06-08 (skeleton Phase 1): `ProbabilityTheory.cond` を直接呼ぶ
genuine def、退化定義悪用なし (cond は well-defined、mass≠0 scope は consumer の `hn`)。
sorry なし・@residual なし。@audit:ok -/
noncomputable def truncW (P : Measure Ω) (W : Ω → ℝ) (n : ℕ) : Measure Ω :=
  ProbabilityTheory.cond P {ω | |W ω| ≤ (n : ℝ)}

/-- **cond density formula** (route T `rnDeriv_cond_eq` を W 単独 truncation 用に再掲、heavy
import 回避のため local 再証明): 確率測度 `μ : Measure ℝ` を可測集合 `s` (positive mass) で
条件付けた測度の Radon-Nikodym 微分は `(cond μ s).rnDeriv volume =ᵐ (μ s)⁻¹ · 1_s · μ.rnDeriv volume`。
`cond μ s = (μ s)⁻¹ • μ.restrict s` の scalar mul + restrict の rnDeriv (`rnDeriv_smul_left_of_ne_top`
+ `rnDeriv_restrict`、共に Mathlib) で組立。route T と完全同型 (集約漏れでなく import cycle/cost 回避)。
独立 honesty audit 2026-06-08: Mathlib 2 補題の機械的合成、循環/bundling なし。@audit:ok -/
private theorem rnDeriv_cond_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Set ℝ}
    (hs : MeasurableSet s) (hpos : μ s ≠ 0) :
    (ProbabilityTheory.cond μ s).rnDeriv volume
      =ᵐ[volume] fun x => (μ s)⁻¹ * s.indicator (μ.rnDeriv volume) x := by
  have hr : (μ s)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hpos
  have h1 : (ProbabilityTheory.cond μ s).rnDeriv volume
      =ᵐ[volume] (μ s)⁻¹ • (μ.restrict s).rnDeriv volume := by
    show ((μ s)⁻¹ • μ.restrict s).rnDeriv volume =ᵐ[volume] (μ s)⁻¹ • (μ.restrict s).rnDeriv volume
    exact Measure.rnDeriv_smul_left_of_ne_top (μ.restrict s) volume hr
  have h2 : (μ.restrict s).rnDeriv volume =ᵐ[volume] s.indicator (μ.rnDeriv volume) :=
    Measure.rnDeriv_restrict μ volume hs
  refine h1.trans ?_
  filter_upwards [h2] with x hx
  simp only [Pi.smul_apply, hx, smul_eq_mul]

/-- **per-fibre entropy integrability の translation 不変性**: `ν ≪ volume` で
`negMulLog (rnDeriv ν)` が可積分なら、平行移動 `ν.map (· + y)` でも可積分。Lebesgue 平行移動不変
(`map_add_right_eq_self`) + measure-preserving 合成 (`MeasurePreserving.integrable_comp_emb`) +
`MeasurableEmbedding.rnDeriv_map` で shift 後の rnDeriv を shift 前に同定。
独立 honesty audit 2026-06-08: Mathlib 機械的合成、循環/bundling なし。@audit:ok -/
private theorem integrable_negMulLog_rnDeriv_map_add_const
    {ν : Measure ℝ} [SigmaFinite ν] (y : ℝ)
    (hν_ent : Integrable (fun x => Real.negMulLog ((ν.rnDeriv volume x).toReal)) volume) :
    Integrable
      (fun x => Real.negMulLog (((ν.map (fun x => x + y)).rnDeriv volume x).toReal)) volume := by
  have hf : MeasurableEmbedding (fun x : ℝ => x + y) := measurableEmbedding_addRight y
  have h_map_vol : (volume : Measure ℝ).map (fun x => x + y) = volume :=
    MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) y
  -- `(· + y)` is measure-preserving on Lebesgue.
  have hmp : MeasurePreserving (fun x : ℝ => x + y) volume volume :=
    ⟨hf.measurable, h_map_vol⟩
  -- rnDeriv after the shift, evaluated at `x + y`, equals rnDeriv before the shift.
  have h_rn := hf.rnDeriv_map ν (volume : Measure ℝ)
  rw [h_map_vol] at h_rn
  -- It suffices to prove integrability of the composition `g ∘ (· + y)` and then transfer.
  have hcomp_int : Integrable
      (fun x => Real.negMulLog ((((ν.map (fun x => x + y)).rnDeriv volume) (x + y)).toReal))
      volume := by
    refine hν_ent.congr ?_
    filter_upwards [h_rn] with x hx
    rw [hx]
  -- transfer along the measure-preserving embedding `(· + y)`.
  exact (hmp.integrable_comp_emb hf).mp hcomp_int

/-- **convolution density as translate-average** (only the LEFT factor a.c.): for `μW ≪ volume`
the sum law `μW ∗ μV` is `volume.withDensity (z ↦ ∫⁻ v, f_W (z - v) ∂μV)` where `f_W = μW.rnDeriv vol`.
Unlike the route-T `convDensityAdd` machinery (`EPIConvDensity`, which requires **both** components
a.c.), this only needs `μW` a.c.; `μV` is a general (probability) measure. `lintegral_conv` (Tonelli)
+ `withDensity_rnDeriv_eq` (recover `μW = vol.withDensity f_W`) + translation invariance.

独立 honesty audit 2026-06-08 (sum-marginal crux supply): genuine, Mathlib 機械合成 (Tonelli +
平行移動不変)、結論は a.e. 測度等式 (regularity)、循環/bundling なし。@audit:ok -/
private theorem conv_eq_withDensity_translate_average
    (μW μV : Measure ℝ) [SFinite μW] [SFinite μV] (hμW : μW ≪ volume) :
    μW ∗ μV
      = (volume : Measure ℝ).withDensity (fun z => ∫⁻ v, μW.rnDeriv volume (z - v) ∂μV) := by
  set g : ℝ → ℝ≥0∞ := μW.rnDeriv volume with hg_def
  have hg_meas : Measurable g := Measure.measurable_rnDeriv _ _
  have hμW_wd : μW = (volume : Measure ℝ).withDensity g :=
    (Measure.withDensity_rnDeriv_eq μW volume hμW).symm
  refine Measure.ext fun A hA => ?_
  have hind : Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hA
  have hinner_meas : Measurable (fun x => ∫⁻ v, A.indicator 1 (x + v) ∂μV) :=
    (hind.comp (measurable_fst.add measurable_snd)).lintegral_prod_right'
  have hL : (μW ∗ μV) A = ∫⁻ x, (∫⁻ v, A.indicator 1 (x + v) ∂μV) ∂μW := by
    rw [← lintegral_indicator_one hA, Measure.lintegral_conv hind]
  have hR : ((volume : Measure ℝ).withDensity (fun z => ∫⁻ v, g (z - v) ∂μV)) A
      = ∫⁻ z, A.indicator 1 z * (∫⁻ v, g (z - v) ∂μV) ∂volume := by
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    apply lintegral_congr; intro z
    by_cases hz : z ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [hL, hR, hμW_wd,
    lintegral_withDensity_eq_lintegral_mul₀ hg_meas.aemeasurable hinner_meas.aemeasurable]
  calc ∫⁻ x, (g * fun x => ∫⁻ v, A.indicator 1 (x + v) ∂μV) x ∂volume
      = ∫⁻ x, ∫⁻ v, g x * A.indicator 1 (x + v) ∂μV ∂volume := by
        apply lintegral_congr; intro x
        rw [Pi.mul_apply]
        exact (lintegral_const_mul (g x)
          (hind.comp ((measurable_const (a := x)).add measurable_id))).symm
    _ = ∫⁻ v, ∫⁻ x, g x * A.indicator 1 (x + v) ∂volume ∂μV := by
        rw [lintegral_lintegral_swap]
        exact ((hg_meas.comp measurable_fst).mul
          (hind.comp (measurable_fst.add measurable_snd))).aemeasurable
    _ = ∫⁻ v, ∫⁻ z, g (z - v) * A.indicator 1 z ∂volume ∂μV := by
        apply lintegral_congr; intro v
        rw [← lintegral_add_right_eq_self
          (μ := (volume : Measure ℝ)) (fun z => g (z - v) * A.indicator 1 z) v]
        apply lintegral_congr; intro x; rw [add_sub_cancel_right]
    _ = ∫⁻ v, ∫⁻ z, A.indicator 1 z * g (z - v) ∂volume ∂μV := by
        apply lintegral_congr; intro v; apply lintegral_congr; intro z; rw [mul_comm]
    _ = ∫⁻ z, A.indicator 1 z * (∫⁻ v, g (z - v) ∂μV) ∂volume := by
        rw [lintegral_lintegral_swap
          (by exact ((hind.comp measurable_snd).mul
            (hg_meas.comp (measurable_snd.sub measurable_fst))).aemeasurable)]
        apply lintegral_congr; intro z
        exact lintegral_const_mul (A.indicator 1 z)
          (hg_meas.comp ((measurable_const (a := z)).sub measurable_id))

/-- **translate of an a.c. measure as withDensity**: `(vol.withDensity f).map (·+z) =
vol.withDensity (f (·-z))`. Lebesgue translation invariance. Used to express the
affine-shift fibre `(Q.map W).map(·+z)` as a `withDensity` for the per-fibre a.c. argument.
独立 honesty audit 2026-06-08: genuine, ext + 平行移動不変、循環/bundling なし。@audit:ok -/
private theorem map_add_const_withDensity (f : ℝ → ℝ≥0∞) (z : ℝ) :
    ((volume : Measure ℝ).withDensity f).map (fun x => x + z)
      = (volume : Measure ℝ).withDensity (fun x => f (x - z)) := by
  have hmap : Measurable (fun x : ℝ => x + z) := measurable_id.add_const z
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hmap hA, withDensity_apply _ (hmap hA), withDensity_apply _ hA,
    ← lintegral_indicator (hmap hA), ← lintegral_indicator hA]
  rw [← lintegral_add_right_eq_self
    (μ := (volume : Measure ℝ)) (fun x => A.indicator (fun y => f (y - z)) x) z]
  apply lintegral_congr; intro x
  by_cases hx : x + z ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (by simpa using hx), add_sub_cancel_right]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (by simpa using hx)]

/-- **per-fibre a.c. (continuous disintegration, sum structure)**: for `W ⊥ V` under `Q` with
`Q.map W ≪ volume`, the affine-shift fibre `(Q.map W).map (·+z)` (= the per-fibre conditional law
of `W+V` given `V=z`, via `affineShiftKernel`) is a.c. w.r.t. the sum marginal `(Q.map W) ∗ (Q.map V)`
for a.e. `z ∂(Q.map V)`. This is the **continuous** version of the general disintegration fact
`condDistrib z ≪ μ.map X` (Mathlib's general/non-discrete version is absent; the in-tree
`Bridge.condDistrib_ae_absolutelyContinuous_map` is `[Countable X]`-only, unusable for `X = ℝ`).

機構: 和密度 `r(x) = ∫⁻ v, f_W(x-v) ∂μ_V` (= `conv_eq_withDensity_translate_average`)、translate 密度
`f_W(·-z)`。Fubini で `(μ_V × vol)({(z,x) : r(x)=0 ∧ 0<f_W(x-z)}) = 0` (各 x で `r(x)=0 ⟹ f_W(x-v)=0`
μ_V-a.e.)、swap で a.e. z に `{r=0} ⊆ {f_W(·-z)=0}` vol-a.e. を出し、withDensity 間 a.c. に変換。

独立 honesty audit 2026-06-08 (sum-marginal crux supply, 4-check): (1) 非循環 — 結論 (a.e. per-fibre
a.c.) は仮説 (indep + a.c. regularity) と非同型。(2) 非バンドル — `hindep`/`hμW_ac` は regularity
precondition、a.c. の核を encode せず。(3) 非退化 — `:True` slot なし。(4) sufficiency — Fubini +
support 包含で genuine、Z=X 退化 (Dirac fibre) は **sum 構造で除外** (translate of a.c. は a.c.、
Dirac でない)。

**独立 auditor 確認 (fresh subagent, 2026-06-08, 実装者 self-report と独立、4-check 再検証 PASS)**:
sorryAx-free 機械裏取り済 (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)。
under-hypothesized でない (核心検証): `hμW_ac` を落とすと反例で偽 (μW=δ_a, μV=Unif[0,1] ⟹
δ_{a+z} ⋘ Unif[a,a+1]) = 仮説必要 = honest。退化境界: μV=δ_0 で trivial (δ_0 で μW≪μW)、Dirac fibre
病理 (一般 disintegration `condDistrib z ≪ μ.map X` は Z=X で偽) は **fibre が translate-of-a.c. =
それ自身 a.c. ＋ marginal が convolution = 全 translate を mixing** ゆえ排除 (sum 構造が本質、generic
condDistrib でない)。in-tree `Bridge.condDistrib_ae_absolutelyContinuous_map` は per-singleton vanishing
proof = 離散 alphabet 限定 (`X=ℝ` 構造的に不可) を確認 ⇒ 本 continuous 自前 build は集約漏れでなく
genuine distinct asset。@audit:ok -/
private theorem condDistrib_ae_absolutelyContinuous_indep_add
    {μW μV : Measure ℝ} [SFinite μW] [SFinite μV] [IsProbabilityMeasure μV] (hμW_ac : μW ≪ volume) :
    ∀ᵐ z ∂μV, (μW.map (fun x => x + z)) ≪ (μW ∗ μV) := by
  have hconv : μW ∗ μV
      = (volume : Measure ℝ).withDensity (fun z => ∫⁻ v, μW.rnDeriv volume (z - v) ∂μV) :=
    conv_eq_withDensity_translate_average μW μV hμW_ac
  have htrans : ∀ z : ℝ, μW.map (fun x => x + z)
      = (volume : Measure ℝ).withDensity (fun x => μW.rnDeriv volume (x - z)) := by
    intro z
    conv_lhs => rw [show μW = (volume : Measure ℝ).withDensity (μW.rnDeriv volume) from
      (Measure.withDensity_rnDeriv_eq μW volume hμW_ac).symm]
    rw [map_add_const_withDensity (μW.rnDeriv volume) z]
  set f : ℝ → ℝ≥0∞ := μW.rnDeriv volume with hf_def
  have hf_meas : Measurable f := Measure.measurable_rnDeriv _ _
  set r : ℝ → ℝ≥0∞ := fun z => ∫⁻ v, f (z - v) ∂μV with hr_def
  have hr_meas : Measurable r :=
    (hf_meas.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | r p.2 = 0 ∧ 0 < f (p.2 - p.1)} with hS_def
  have hSmeas : MeasurableSet S :=
    ((hr_meas.comp measurable_snd) (measurableSet_singleton 0)).inter
      (measurableSet_lt measurable_const (hf_meas.comp (measurable_snd.sub measurable_fst)))
  have hslice_x : ∀ x : ℝ, μV {v | r x = 0 ∧ 0 < f (x - v)} = 0 := by
    intro x
    by_cases hrx : r x = 0
    · have hfae : ∀ᵐ v ∂μV, f (x - v) = 0 :=
        (lintegral_eq_zero_iff (hf_meas.comp (measurable_const.sub measurable_id))).mp hrx
      have hfzero : μV {v | ¬ (f (x - v) = 0)} = 0 := hfae
      exact measure_mono_null (fun v hv => pos_iff_ne_zero.mp hv.2) hfzero
    · have : {v | r x = 0 ∧ 0 < f (x - v)} = ∅ := by ext v; simp [hrx]
      rw [this]; simp
  have hkey : ∫⁻ z, (volume : Measure ℝ) (Prod.mk z ⁻¹' S) ∂μV = 0 := by
    rw [← Measure.prod_apply hSmeas, Measure.prod_apply_symm hSmeas]
    simp_rw [show ∀ x : ℝ, (fun v => (v, x)) ⁻¹' S = {v | r x = 0 ∧ 0 < f (x - v)} from fun _ => rfl,
      hslice_x, lintegral_zero]
  have hae_slice : ∀ᵐ z ∂μV, (volume : Measure ℝ) (Prod.mk z ⁻¹' S) = 0 :=
    (lintegral_eq_zero_iff (measurable_measure_prodMk_left hSmeas)).mp hkey
  filter_upwards [hae_slice] with z hz
  rw [htrans z, hconv]
  have hfz_meas : Measurable (fun x : ℝ => f (x - z)) := hf_meas.comp (measurable_id.sub_const z)
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  rw [withDensity_apply _ hA] at hA0 ⊢
  rw [setLIntegral_eq_zero_iff hA hr_meas] at hA0
  rw [setLIntegral_eq_zero_iff hA hfz_meas]
  have hnull2 : ∀ᵐ x ∂volume, ¬ (r x = 0 ∧ 0 < f (x - z)) := by
    rw [ae_iff]; convert (hz : (volume : Measure ℝ) (Prod.mk z ⁻¹' S) = 0) using 2; ext x; simp [hS_def]
  filter_upwards [hA0, hnull2] with x hx0 hxsub hxA
  by_contra hne
  exact hxsub ⟨hx0 hxA, pos_iff_ne_zero.mpr hne⟩

/-- **single-component negative-part finiteness of the sum law** — `B(μW ∗ μV) < ⊤` from
`B(μW) < ⊤`. The single-component generalization of route-T
`integrable_negPart_negMulLog_map_condTrunc_sum` (`EPIInfiniteVarianceTruncation.lean:600`),
which averages over the X-marginal `pn·vol` (requires both components a.c.) and bounds the
Y-marginal negative part. Here the averaging is over the **general probability measure** `μV`
(no a.c. on `μV` needed, so it works even when `V` is non-a.c.), bounding the **W-marginal**
negative part `B(μW)`.

機構 (route-T:600 を下敷きに、averaging measure を `pn·vol → μV` に差し替え):
- `r := ((μW ∗ μV).rnDeriv vol).toReal`, `fW := (μW.rnDeriv vol).toReal`, `φ t := t·log t`.
  目標 `∫⁻ ofReal(-(negMulLog r)) = ∫⁻ ofReal(φ r) ≤ ∫⁻ ofReal(max (φ r) 0)`。
- 収束密度: `r =ᵐ[vol] fun z => ∫ v, fW(z-v) ∂μV` (`conv_eq_withDensity_translate_average` の
  `Measure.rnDeriv_withDensity` + `integral_toReal`)。`μV` 確率測度ゆえ平均。
- per-z Jensen: `φ(r z) ≤ ∫ v, max (φ (fW(z-v))) 0 ∂μV` (`Real.convexOn_mul_log.map_integral_le`,
  `μ := μV` 確率測度)。
- Tonelli + 平行移動不変: `∫⁻ z, ofReal(max (φ (r z)) 0) ≤ ∫⁻ z ∫⁻ v ofReal(max(φ(fW(z-v)))0) ∂μV
  = ∫⁻ v ∫⁻ z ofReal(Cq(z-v)) ∂vol ∂μV = (μV univ)·C = 1·C = C = B(μW) < ⊤`.

@residual(plan:epi-uncond-truncation-lsc-plan) -/
private theorem negPart_negMulLog_conv_single_ne_top
    (μW μV : Measure ℝ) [IsFiniteMeasure μW] [IsProbabilityMeasure μV] (hμW : μW ≪ volume)
    (hμW_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μW.rnDeriv volume x).toReal))) ∂volume) ≠ ⊤) :
    (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((μW ∗ μV).rnDeriv volume x).toReal)))
      ∂volume) ≠ ⊤ := by
  -- densities and `φ t = t log t = -(negMulLog t)`.
  set fW : ℝ → ℝ := fun x => (μW.rnDeriv volume x).toReal with hfW_def
  set r : ℝ → ℝ := fun x => ((μW ∗ μV).rnDeriv volume x).toReal with hr_def
  set φ : ℝ → ℝ := fun t => t * Real.log t with hφ_def
  have hφ_eq : ∀ t, -(Real.negMulLog t) = φ t := by
    intro t; show -(-t * Real.log t) = t * Real.log t; ring
  -- basic measurability / nonnegativity.
  have hfW_meas : Measurable fW := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hfW_nn : ∀ x, 0 ≤ fW x := fun _ => ENNReal.toReal_nonneg
  have hr_meas : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hr_nn : ∀ x, 0 ≤ r x := fun _ => ENNReal.toReal_nonneg
  have hφ_meas : Measurable φ := measurable_id.mul (Real.measurable_log.comp measurable_id)
  -- `Cq w = (φ (fW w))⁺`.  `C = ∫⁻ ofReal Cq = ∫⁻ ofReal (-(negMulLog fW)) = hμW_negPart_fin`.
  set Cq : ℝ → ℝ := fun w => max (φ (fW w)) 0 with hCq_def
  have hCq_nn : ∀ w, 0 ≤ Cq w := fun _ => le_max_right _ _
  have hCq_meas : Measurable Cq := (hφ_meas.comp hfW_meas).max measurable_const
  set C : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (Cq w) ∂volume with hC_def
  -- `∫⁻ ofReal Cq = ∫⁻ ofReal (-(negMulLog fW))`  (the `max ... 0` is killed by `ofReal`).
  have hC_eq : C = ∫⁻ w, ENNReal.ofReal (-(Real.negMulLog (fW w))) ∂volume := by
    rw [hC_def]; apply lintegral_congr; intro w
    show ENNReal.ofReal (max (φ (fW w)) 0) = ENNReal.ofReal (-(Real.negMulLog (fW w)))
    rw [← hφ_eq (fW w)]
    rcases le_or_gt 0 (-(Real.negMulLog (fW w))) with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h.le, ENNReal.ofReal_of_nonpos h.le, ENNReal.ofReal_of_nonpos (le_refl 0)]
  have hC_lt_top : C ≠ ⊤ := by rw [hC_eq]; exact hμW_negPart_fin
  -- the sum law is `vol.withDensity (z ↦ ∫⁻ v, f_W(z-v) ∂μV)` (left-factor a.c. only).
  set fWe : ℝ → ℝ≥0∞ := μW.rnDeriv volume with hfWe_def
  have hfWe_meas : Measurable fWe := Measure.measurable_rnDeriv _ _
  have hconv : μW ∗ μV
      = (volume : Measure ℝ).withDensity (fun z => ∫⁻ v, fWe (z - v) ∂μV) :=
    conv_eq_withDensity_translate_average μW μV hμW
  have hrho_meas : Measurable (fun z => ∫⁻ v, fWe (z - v) ∂μV) :=
    (hfWe_meas.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'
  -- `r =ᵐ[vol] fun z => ∫ v, fW (z-v) ∂μV`  (toReal of the convolution density, μV is a prob measure).
  have hr_conv : r =ᵐ[volume] fun z => ∫ v, fW (z - v) ∂μV := by
    have h_rn : (μW ∗ μV).rnDeriv volume =ᵐ[volume] fun z => ∫⁻ v, fWe (z - v) ∂μV := by
      rw [hconv]; exact Measure.rnDeriv_withDensity volume hrho_meas
    have h_lt : ∀ᵐ z ∂volume, (μW ∗ μV).rnDeriv volume z < ∞ :=
      Measure.rnDeriv_lt_top (μW ∗ μV) volume
    filter_upwards [h_rn, h_lt] with z hz hz_lt
    show ((μW ∗ μV).rnDeriv volume z).toReal = ∫ v, fW (z - v) ∂μV
    -- `∫⁻ v, fWe(z-v) ∂μV < ∞` ⟹ `fWe(z-v) < ∞` μV-a.e. (finite integral ⟹ a.e. finite).
    have hfWe_z_meas : Measurable (fun v => fWe (z - v)) := by fun_prop
    have hint_lt : (∫⁻ v, fWe (z - v) ∂μV) < ∞ := hz ▸ hz_lt
    have hae_lt : ∀ᵐ v ∂μV, fWe (z - v) < ∞ :=
      ae_lt_top' hfWe_z_meas.aemeasurable hint_lt.ne
    rw [hz]
    exact (integral_toReal hfWe_z_meas.aemeasurable hae_lt).symm
  -- ============================================================================
  -- Tonelli identity:  `∫⁻ z ∫⁻ v ofReal (g (z - v)) ∂μV ∂vol = (μV univ)·(∫⁻ ofReal g)`,
  -- for nonneg measurable `g`, via translation invariance + swap.
  -- ============================================================================
  have hkernel_lint : ∀ g : ℝ → ℝ, Measurable g → (∀ w, 0 ≤ g w) →
      ∫⁻ z, ∫⁻ v, ENNReal.ofReal (g (z - v)) ∂μV ∂volume
        = (μV Set.univ) * (∫⁻ w, ENNReal.ofReal (g w) ∂volume) := by
    intro g hg hg_nn
    -- swap to `∫⁻ v ∫⁻ z`, translate `z ↦ z + v`, factor.
    have hswap : ∫⁻ z, ∫⁻ v, ENNReal.ofReal (g (z - v)) ∂μV ∂volume
        = ∫⁻ v, ∫⁻ z, ENNReal.ofReal (g (z - v)) ∂volume ∂μV := by
      rw [lintegral_lintegral_swap]
      exact (hg.comp (measurable_fst.sub measurable_snd)).ennreal_ofReal.aemeasurable
    rw [hswap]
    have hinner : ∀ v, ∫⁻ z, ENNReal.ofReal (g (z - v)) ∂volume
        = ∫⁻ w, ENNReal.ofReal (g w) ∂volume := fun v =>
      lintegral_sub_right_eq_self (fun w => ENNReal.ofReal (g w)) v
    simp_rw [hinner]
    rw [lintegral_const, mul_comm]
  -- product-measure integrability of `K (z, v) = fW (z - v)` (needed for the per-z section
  -- integrability of `v ↦ Cq (z - v)`).
  have hkernel_int : ∀ g : ℝ → ℝ, Measurable g → (∀ w, 0 ≤ g w) →
      (∫⁻ w, ENNReal.ofReal (g w) ∂volume) ≠ ⊤ →
      Integrable (fun p : ℝ × ℝ => g (p.1 - p.2)) (volume.prod μV) := by
    intro g hg hg_nn hg_fin
    have hgp_meas : Measurable (fun p : ℝ × ℝ => g (p.1 - p.2)) :=
      hg.comp (measurable_fst.sub measurable_snd)
    refine ⟨hgp_meas.aestronglyMeasurable, ?_⟩
    have hnn : ∀ᵐ p : ℝ × ℝ ∂(volume.prod μV), 0 ≤ g (p.1 - p.2) :=
      Filter.Eventually.of_forall (fun p => hg_nn _)
    rw [hasFiniteIntegral_iff_ofReal hnn,
      lintegral_prod _ hgp_meas.ennreal_ofReal.aemeasurable,
      hkernel_lint g hg hg_nn, measure_univ, one_mul]
    exact lt_of_le_of_ne le_top hg_fin
  -- per-`z` section integrability: `v ↦ Cq (z - v)` integrable w.r.t. `μV`  (a.e. `z`).
  have hsec_Cq : ∀ᵐ z ∂volume, Integrable (fun v => Cq (z - v)) μV := by
    have := (hkernel_int Cq hCq_meas hCq_nn (by rw [← hC_def]; exact hC_lt_top)).prod_right_ae
    exact this
  -- per-`z` section integrability of `v ↦ fW (z - v)` (the Jensen integrand `f`).
  have hsec_fW : ∀ᵐ z ∂volume, Integrable (fun v => fW (z - v)) μV := by
    have := (hkernel_int fW hfW_meas hfW_nn (by
      -- `∫⁻ ofReal fW = μW univ = 1`  (probability density of `μW`).
      have hae_eq : (fun x => ENNReal.ofReal (fW x)) =ᵐ[volume] μW.rnDeriv volume := by
        filter_upwards [μW.rnDeriv_ne_top volume] with x hx
        rw [hfW_def]; exact ENNReal.ofReal_toReal hx
      rw [lintegral_congr_ae hae_eq, Measure.lintegral_rnDeriv hμW]
      exact measure_ne_top _ _)).prod_right_ae
    exact this
  -- ============================================================================
  -- per-`z` Jensen bound:  `max (φ (r z)) 0 ≤ ∫ v, Cq (z - v) ∂μV`  (a.e. `z`).
  -- ============================================================================
  set G : ℝ → ℝ := fun z => max (φ (r z)) 0 with hG_def
  have hG_nn : ∀ z, 0 ≤ G z := fun _ => le_max_right _ _
  have hjensen : ∀ᵐ z ∂volume, G z ≤ ∫ v, Cq (z - v) ∂μV := by
    filter_upwards [hr_conv, hsec_Cq, hsec_fW] with z hz hzCq hzfW
    -- abbreviation `f v = fW (z - v)`.
    set f : ℝ → ℝ := fun v => fW (z - v) with hf_def
    have hf_nn : ∀ v, 0 ≤ f v := fun _ => hfW_nn _
    -- `max (φ (f v)) 0 = Cq (z - v)` and `(φ∘f)⁻ = Cm (z - v)`.
    have hCqf_int : Integrable (fun v => max (φ (f v)) 0) μV := hzCq
    set Cm : ℝ → ℝ := fun v => max (-(φ (f v))) 0 with hCm_def
    -- `Cm v = (negMulLog (f v))⁺ ≤ 1` pointwise (since `negMulLog t ≤ 1 - t ≤ 1` for `t ≥ 0`),
    -- and constant `1` is integrable over the **probability** measure `μV`.
    have hCm_meas : Measurable Cm :=
      ((hφ_meas.comp (hfW_meas.comp (measurable_const.sub measurable_id))).neg).max measurable_const
    have hCm_le_one : ∀ v, Cm v ≤ 1 := by
      intro v
      rw [hCm_def]
      refine max_le ?_ (by norm_num)
      have hnml : -(φ (f v)) = Real.negMulLog (f v) := by rw [← hφ_eq (f v), neg_neg]
      rw [hnml]
      calc Real.negMulLog (f v) ≤ 1 - f v := Real.negMulLog_le_one_sub_self (hf_nn v)
        _ ≤ 1 := by have := hf_nn v; linarith
    have hCm_int : Integrable Cm μV := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hCm_meas.aestronglyMeasurable ?_
      filter_upwards with v
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact hCm_le_one v
    -- `φ ∘ f = (φ∘f)⁺ - (φ∘f)⁻`, hence integrable.
    have hφf_eq : (fun v => φ (f v)) = fun v => max (φ (f v)) 0 - Cm v := by
      funext v
      show φ (f v) = max (φ (f v)) 0 - max (-(φ (f v))) 0
      rcases le_or_gt 0 (φ (f v)) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith : -(φ (f v)) ≤ 0)]; ring
      · rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(φ (f v)))]; ring
    have hf_int : Integrable f μV := hzfW
    have hφf_int : Integrable (fun v => φ (f v)) μV := by
      rw [hφf_eq]; exact hCqf_int.sub hCm_int
    -- Jensen:  `φ (∫ f ∂μV) ≤ ∫ φ∘f ∂μV`.
    have hjz : φ (∫ v, f v ∂μV) ≤ ∫ v, φ (f v) ∂μV := by
      have := Real.convexOn_mul_log.map_integral_le
        (μ := μV) (f := f) (g := φ)
        Real.continuous_mul_log.continuousOn
        isClosed_Ici
        (Filter.Eventually.of_forall (fun v => hf_nn v))
        hf_int hφf_int
      simpa only [hφ_def] using this
    -- `r z = ∫ v, f v ∂μV`  (the convolution-density identity `hz`).
    have hrz_eq : r z = ∫ v, f v ∂μV := hz
    have hstep1 : φ (r z) ≤ ∫ v, φ (f v) ∂μV := by rw [hrz_eq]; exact hjz
    have hstep2 : (∫ v, φ (f v) ∂μV) ≤ ∫ v, max (φ (f v)) 0 ∂μV :=
      integral_mono hφf_int hCqf_int (fun v => le_max_left _ _)
    have hstep3 : (∫ v, max (φ (f v)) 0 ∂μV) = ∫ v, Cq (z - v) ∂μV := rfl
    have hCq_int_z : (0 : ℝ) ≤ ∫ v, Cq (z - v) ∂μV :=
      integral_nonneg (fun v => hCq_nn _)
    rw [hG_def]
    exact max_le (by rw [← hstep3]; exact le_trans hstep1 hstep2) hCq_int_z
  -- ============================================================================
  -- assemble:  `∫⁻ ofReal(-(negMulLog r)) = ∫⁻ ofReal(φ r) ≤ ∫⁻ ofReal G ≤ 1·C < ⊤`.
  -- ============================================================================
  have hgoal_le : (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (r x))) ∂volume)
      ≤ ∫⁻ z, ENNReal.ofReal (G z) ∂volume := by
    apply lintegral_mono; intro z
    show ENNReal.ofReal (-(Real.negMulLog (r z))) ≤ ENNReal.ofReal (G z)
    rw [hφ_eq (r z)]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  refine ne_top_of_le_ne_top ?_ hgoal_le
  have hfinal : (∫⁻ z, ENNReal.ofReal (G z) ∂volume) ≤ (μV Set.univ) * C :=
    calc ∫⁻ z, ENNReal.ofReal (G z) ∂volume
        ≤ ∫⁻ z, ENNReal.ofReal (∫ v, Cq (z - v) ∂μV) ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [hjensen] with z hz
          exact ENNReal.ofReal_le_ofReal hz
      _ ≤ ∫⁻ z, ∫⁻ v, ENNReal.ofReal (Cq (z - v)) ∂μV ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [hsec_Cq] with z hz
          calc ENNReal.ofReal (∫ v, Cq (z - v) ∂μV)
              = ∫⁻ v, ENNReal.ofReal (Cq (z - v)) ∂μV := by
                rw [ofReal_integral_eq_lintegral_ofReal hz
                  (Filter.Eventually.of_forall (fun v => hCq_nn _))]
            _ ≤ _ := le_refl _
      _ = (μV Set.univ) * C := by rw [hkernel_lint Cq hCq_meas hCq_nn, hC_def]
  refine ne_top_of_le_ne_top ?_ hfinal
  rw [measure_univ, one_mul]; exact hC_lt_top

/-- **negMulLog-Fatou helper** — 正部 lintegral `A` の Fatou lift。
density の toReal a.e. 収束 `f_{μ_n} → f_μ` から `A_μ ≤ liminf A_{μ_n}` を Fatou で出す
(`A μ := ∫⁻ x, ofReal (negMulLog (rnDeriv μ vol x).toReal) ∂volume` = `differentialEntropyExt`
の a.c. 枝の正部、`EntropyPowerExt.lean:61`)。

`klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean:112`、`@audit:ok`) と完全同型で、
`klFun`→`negMulLog` 差替のみ (両者 continuous)。骨格 = `lintegral_liminf_le` +
`ENNReal.continuous_ofReal` + `Tendsto.liminf_eq` + `lintegral_mono_ae`。Phase 0 scratch
(`/tmp/route_beta_phase0.lean` `A_le_liminf_of_ae_tendsto`) で骨格実証済 (0 sorry)、本 file
では Phase 3 で埋める skeleton として sorry。

独立 honesty audit 2026-06-08 (skeleton, 4-check PASS → honest_residual): (1) 非循環 — 結論
(正部 lintegral の liminf 下界) は仮説 `h_ae` (density a.e. 収束) と非同型。(2) 非バンドル —
`h_ae` は a.e. 収束 input precondition、Fatou 不等式の核を encode せず。(3) 非退化 — `:True`
slot なし。(4) sufficiency — Fatou (`lintegral_liminf_le`、非負被積分関数列で `∫ liminf ≤
liminf ∫`) が正しい向き: `ofReal(negMulLog ...)` で負部を 0 clamp した正部 A に対し成立する
向きで、収束列の極限 = liminf を使う (`klDiv_le_liminf_of_ae_tendsto` body と同構造)。
classification: `klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean:112`) と **別物**
(参照測度 γ 有限 vs volume 無限、klFun vs negMulLog) ゆえ集約漏れでない。`plan:` 妥当
(Mathlib 1本不在の壁でなく既存同型骨格の差替で closeable、対応 plan 実在)。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_posPart_le_liminf_of_ae_tendsto
    (μ : Measure ℝ) (μ_n : ℕ → Measure ℝ)
    (h_ae : ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n => ((μ_n n).rnDeriv volume x).toReal) atTop
        (𝓝 ((μ.rnDeriv volume x).toReal))) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume)
      ≤ Filter.liminf
          (fun n => ∫⁻ x, ENNReal.ofReal
            (Real.negMulLog (((μ_n n).rnDeriv volume x).toReal)) ∂volume) atTop := by
  sorry

/-- **per-n finite-entropy 単調性**: 各 n で `h(W_n) ≤ h(W_n + V)` を finite ②
(`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite`、11 regularity 仮説、`@audit:ok`) or
有限枝単調性経由で建てる。`truncW P W n` は compact support ゆえ有限分散・有限エントロピーで、
finite ② の 11 仮説 (joint 密度可測 / per-fibre KL 有限 等) を condDistrib で供給する。

route β' Phase 2 で埋める。`hn` (positive mass) は条件付けが well-defined な n を選ぶ scope
(load-bearing でない)。

**`hW_negPart_fin` の追加理由 (2026-06-08 Phase 2 案 F)**: `B(W) := ∫⁻ ofReal(-(negMulLog f_W)) < ⊤`
(= h(W) の負部 lintegral 有限性) を表す **regularity precondition**。truncated `B(W_n) < ⊤` を
密度分解 `f_n = c⁻¹·1_{[-n,n]}·f_W` (`restrict_map` + `rnDeriv_smul_left` + `rnDeriv_restrict`)
+ `negMulLog_mul` で `B(W)` から供給するための入力で、`hW_ne_bot`/`hWV_ne_bot` 系の `≠⊥`
(= 負部有限) closure に使う。**load-bearing でない**: 単調性 `h(W_n) ≤ h(W_n+V)` の核は body 側の
finite ② (`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite`) が担い、`hW_negPart_fin` は
h(W) の負部有限性 (正則性条件) で単調性の核を encode しない。name-laundering でない (核を仮説に
packing せず、body sorry は `@residual` で正直にマーク)。

**Phase 2 progress (2026-06-08, 後半)**: body は genuine 配線済 (IndepFun 保存 / fibre 同定 / 等式→
単調性 calc)。finite ② の 11 仮説 supply のうち **genuine 着地**: `hWV_ac_Q` / `hκ_ac` /
`hκ_logp_int` (fibre = `Q.map W` の平行移動ゆえ `integrable_negMulLog_rnDeriv_map_add_const` で
還元) / `hW_ne_bot` (= `hW_ent_Q` 経由、`hAn_fin` compact-support 正部 + `hBn_fin` = `hW_negPart_fin`
由来負部、両部有限 ⟹ 全エントロピー可積分) / **`h_ac` (sum-marginal、CLOSED 2026-06-08 後半)**:
`absolutelyContinuous_compProd_right_iff` で per-fibre a.c. に還元 → 連続 disintegration a.c. 自前 build
`condDistrib_ae_absolutelyContinuous_indep_add` (Mathlib 一般版不在、`[Countable X]` Bridge は `X=ℝ` 不可)
で closure。後者は 和密度 = translate-average (`conv_eq_withDensity_translate_average`、左因子のみ a.c.
で十分、route-T `convDensityAdd` は両 a.c. 要求のため別 build) + Fubini で `{r=0}⊆{f_W(·-z)=0}` a.e. z
+ withDensity 間 a.c. 変換。**honest sorry 残 (3 件)**: sum-marginal `Q.map(W+V)` の mixture log を参照する
`hWV_ne_bot` (= mixture 負部 Jensen+Tonelli、route-T-scale Bochner Jensen を単独成分 over μ_V 版で再 build
要、~120 行) / `hκ_cross_int` (= cross-entropy domination、mixture log の支配) / `hκ_KL` (= `hκ_cross_int`
の下流、a.c. 部は `h_ac` と同供給で取れるが llr 可積分が cross-term 依存) + Mathlib 不在の `hκ_dens_meas`
(joint 密度可測、真 gap、touch 対象外)。前者 3 件は route-T-scale Jensen/DCT 再 build ゆえ別 fill / escalate へ。

独立 honesty audit 2026-06-08 (skeleton, 4-check PASS → honest_residual): (1) 非循環 — 結論
(単調不等式 `h(W_n) ≤ h(W_n+V)`) は 7 仮説と非同型。(2) 非バンドル — `hW`/`hV`/`hWV`/`hW_ac`
は可測/独立/絶対連続の regularity、`hW_negPart_fin` は h(W) 負部有限性の regularity、`hn` は cond
well-defined の scope precondition、いずれも単調性の核を encode せず (供給元 finite ② =
`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite` が body 側に来る)。(3) 非退化 — `:True`
slot なし。(4) sufficiency — compact support (`{|W|≤n}` 条件付け) の有限分散・有限エントロピー
measure で単調性が立つのは正しい (route T が同 truncation で sorryAx-free 実証済)。`plan:` 妥当。

**独立 auditor 確認 (fresh subagent、2026-06-08、実装者の self-report と独立)**:
- `hW_negPart_fin` = **regularity precondition、NOT load-bearing** (core-reconstruction test FAIL: B(W)<⊤
  を grant しても単調性 `h(W_n)≤h(W_n+V)` は出ない。仮説は h(W) 負部 lintegral の **有限性** のみ = finiteness
  category = OK。consumer 検証: body で `hBn_fin` (truncated 負部有限) 経由 `hW_ne_bot`/`hW_ent_Q` の ≠⊥
  regularity にのみ消費、単調性の核 = 別 file finite ② `..._of_finite` `@audit:ok` が body 側で担う)。
- genuine closure 検証 (機械: file は 0 error / 4 sorry のみ = helper 群 sorry なし):
  `hAn_fin` (compact-support `negMulLog_le_one_sub_self` + `volume Sn<⊤`)、`hBn_fin` (`negMulLog_mul`
  分解 + `hW_negPart_fin` bound、両 Mathlib 補題 loogle 実在確認)、`hW_ent_Q` (両部有限⟹可積分)、
  `hW_ne_bot` (`differentialEntropyExt_of_ac_integrable` sig 照合済)、`hκ_logp_int` (`Q.map W` 平行移動
  還元) いずれも genuine、退化定義悪用 (exfalso/vacuous) なし。private helper 2 本 (`rnDeriv_cond_eq` /
  `integrable_negMulLog_rnDeriv_map_add_const`) signature 非 under-hypothesized、body Mathlib 機械合成。
- skeleton 監査時点の 4 honest sorry (`hWV_ne_bot`/`h_ac`/`hκ_cross_int`/`hκ_KL`) のうち **`h_ac` は
  Phase 2 後半で genuine CLOSED** (上記 progress 参照、自前 build `condDistrib_ae_absolutelyContinuous_indep_add`
  + `conv_eq_withDensity_translate_average` + `map_add_const_withDensity`、いずれも `@audit:ok`、`#print axioms`
  で transitive sorry が残 3 件のみ確認)。残 3 honest sorry (`hWV_ne_bot`/`hκ_cross_int`/`hκ_KL`) の `plan:`
  分類妥当 (wall: 化不要): route-T 負部補題 `integrable_negPart_negMulLog_map_condTrunc_sum` は両成分 entropy
  (`hX_ent`+`hY_ent`) 要求のため再利用不可確認 (V entropy 仮説なし)、単独成分 Jensen を over μ_V 版で再 build
  すれば closeable (真 gap でない、route-T-scale)。
  in-tree `Bridge.condDistrib_ae_absolutelyContinuous_map` は `[Fintype X]` 専用 (`X=ℝ` 不可) 確認。
- 注記: `hκ_dens_meas` (joint 密度可測、loogle Found 0) は実装者も `plan:` だが plan 判断ログ #3 が
  「唯一の真 gap、wall 化候補」と認識済 = plan owner 判断に委ねる (本監査の focus 4 件外、現状 `plan:` 許容)。
- 4-check PASS → **honest_residual** (tier 2)。signature honest、`@residual(plan:...)` 分類正確、
  deprecated タグ (`@audit:suspect`/`@audit:staged`/`🟢ʰ`) なし。

**独立 auditor 確認 (fresh subagent, 2026-06-08, Phase 2 後半 = h_ac genuine CLOSED state)**:
file は 0 error / 4 declaration sorry (#259 Phase3-skeleton + 本 #3 の sum-marginal crux 3 本
`hWV_ne_bot`/`hκ_cross_int`/`hκ_KL` + `hκ_dens_meas` + #689/#730 skeleton) のみ、private helper 5 本
(`rnDeriv_cond_eq`/`integrable_negMulLog_rnDeriv_map_add_const`/`conv_eq_withDensity_translate_average`/
`map_add_const_withDensity`/`condDistrib_ae_absolutelyContinuous_indep_add`) は全て sorry-free +
sorryAx-free 機械裏取り済 (`#print axioms` = 標準 3 公理)。`h_ac` 配線 (`absolutelyContinuous_compProd_right_iff`
Mathlib 実在 + per-fibre 自前 build genuine 消費、`hsum_conv`/`hae`/`affineShiftKernel` 正しく threading、
silent leak なし) genuine CLOSED 確認。残 3 sorry の `plan:` 分類 = **妥当 (wall: 昇格不要)**: route-T
`integrable_negPart_negMulLog_map_condTrunc_sum` は両成分 entropy (`hX_ent`+`hY_ent`) + joint `condTrunc`
要求のため V-entropy 仮説なしの本 setting で直接再利用不可を verbatim 確認、ただし closure tool
(Jensen `ConvexOn.map_integral_le` / `klDiv_ne_top` / `klDiv_ne_top_iff`) は Mathlib 実在 = 単独成分版
re-derivation で closeable (真 gap でない)。`hκ_KL` の `≪`-part = `h_ac` 供給済、llr-part = `hκ_cross_int`
transitive 依存の分析正確。**verdict = all OK (honest_residual)**。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_mono_add_truncW
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (n : ℕ) (hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    differentialEntropyExt ((truncW P W n).map W)
      ≤ differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)) := by
  -- The truncated measure `Q := truncW P W n = P[| {|W| ≤ n}]` is a probability measure.
  set Q : Measure Ω := truncW P W n with hQ_def
  haveI hQ_prob : IsProbabilityMeasure Q := by
    rw [hQ_def, truncW]; exact ProbabilityTheory.cond_isProbabilityMeasure hn
  -- W stays a.c. under conditioning: `Q.map W ≪ P.map W ≪ volume`.
  have hW_ac_Q : (Q.map W) ≪ volume := by
    refine (Measure.AbsolutelyContinuous.trans ?_ hW_ac)
    rw [hQ_def, truncW]
    exact (ProbabilityTheory.cond_absolutelyContinuous).map hW
  -- W ⊥ V is preserved under conditioning on a W-event `{|W| ≤ n}` (the event is a function of
  -- W only, so V is unaffected). Self-built from `indepFun_iff_measure_inter_preimage_eq_mul`:
  -- the conditioning event `E = W⁻¹' {r | |r| ≤ n}` absorbs into the W-preimage, and `hWV`
  -- factors the joint measure of W- and V-preimages.
  have hE_meas : MeasurableSet {ω : Ω | |W ω| ≤ (n : ℝ)} :=
    hW.abs measurableSet_Iic
  set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
  have hindep : IndepFun W V Q := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    -- `E ∩ W⁻¹' s = W⁻¹' (Icc⁻¹ ∩ s)` is itself a W-preimage of a measurable set.
    have hEW : E ∩ W ⁻¹' s = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := by
      ext ω; simp [hE_def, Set.mem_inter_iff, and_comm]
    have hIcc_meas : MeasurableSet {r : ℝ | |r| ≤ (n : ℝ)} :=
      (_root_.continuous_abs.measurable measurableSet_Iic)
    have hAW : MeasurableSet ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := hIcc_meas.inter hs
    -- Expand each `cond` term via `cond_apply hE_meas`.
    rw [hQ_def, truncW, cond_apply hE_meas, cond_apply hE_meas, cond_apply hE_meas]
    -- The joint preimage: `E ∩ (W⁻¹s ∩ V⁻¹t) = (E ∩ W⁻¹s) ∩ V⁻¹t = W⁻¹(..) ∩ V⁻¹t`.
    have hjoint : E ∩ (W ⁻¹' s ∩ V ⁻¹' t) = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t := by
      rw [← Set.inter_assoc, hEW]
    rw [hjoint, hEW]
    -- Factor `P` on the W- and V-preimages via the original independence `hWV`.
    have hfac1 : P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t)
        = P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s)) * P (V ⁻¹' t) :=
      hWV.measure_inter_preimage_eq_mul _ _ hAW ht
    -- For the V-term: `E ∩ V⁻¹t = W⁻¹(Icc) ∩ V⁻¹t`, again factored by `hWV`.
    have hEV : E ∩ V ⁻¹' t = W ⁻¹' {r : ℝ | |r| ≤ (n : ℝ)} ∩ V ⁻¹' t := by
      ext ω; simp [hE_def]
    have hfac2 : P (E ∩ V ⁻¹' t) = P E * P (V ⁻¹' t) := by
      rw [hEV, hWV.measure_inter_preimage_eq_mul _ _ hIcc_meas ht, hE_def]; rfl
    rw [hfac1, hfac2]
    -- Arithmetic: `c·(a·v) = (c·a)·(c·(P E·v))` where `c = (P E)⁻¹`, since `c·P E = 1`.
    have hPE_ne : P E ≠ 0 := by rw [hE_def]; exact hn
    have hPE_ne_top : P E ≠ ∞ := measure_ne_top P E
    have hcancel : (P E)⁻¹ * (P E * P (V ⁻¹' t)) = P (V ⁻¹' t) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hPE_ne hPE_ne_top, one_mul]
    rw [hcancel]
    ring
  -- W + V is a.c. under `Q` (`hW_ac_Q` + independence).
  have hWV_ac_Q : (Q.map (fun ω => W ω + V ω)) ≪ volume :=
    map_add_absolutelyContinuous W V Q hW hV hindep hW_ac_Q
  -- Probability-measure instances on the relevant marginals.
  haveI hWmap_prob : IsProbabilityMeasure (Q.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hVmap_prob : IsProbabilityMeasure (Q.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  -- The sum law equals the convolution of the W- and V-marginals (independence).
  have hsum_conv : Q.map (fun ω => W ω + V ω) = (Q.map W) ∗ (Q.map V) := by
    have := hindep.map_add_eq_map_conv_map hW hV
    simpa [Pi.add_apply] using this
  -- **Set-up shared by the `≠ ⊥` / entropy blocks**: `Q.map W = cond (P.map W) Sn` (single-variable
  -- truncation), so its density is `c⁻¹ · 1_Sn · f_W` with `c = (P.map W) Sn = P E`.
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn := measurableSet_le measurable_norm measurable_const
  -- `(truncW P W n).map W = cond (P.map W) Sn` (direct: conditioning on `W⁻¹' Sn` then pushing
  -- forward by `W` equals conditioning the law of `W` on `Sn`).
  have hE_eq : E = W ⁻¹' Sn := by ext ω; simp [hE_def, hSn_def]
  have hQW_eq : (Q.map W) = ProbabilityTheory.cond (P.map W) Sn := by
    refine Measure.ext (fun A hA => ?_)
    -- LHS: `(Q.map W) A = Q (W⁻¹A) = (P E)⁻¹ * P (E ∩ W⁻¹A)`.
    have hLHS : (Q.map W) A = (P E)⁻¹ * P (W ⁻¹' Sn ∩ W ⁻¹' A) := by
      rw [Measure.map_apply hW hA, hQ_def, truncW, ← hE_def,
        ProbabilityTheory.cond_apply hE_meas P, hE_eq]
    -- RHS: `cond (P.map W) Sn A = ((P.map W) Sn)⁻¹ * (P.map W)(Sn ∩ A)`.
    have hRHS : (ProbabilityTheory.cond (P.map W) Sn) A
        = (P E)⁻¹ * P (W ⁻¹' Sn ∩ W ⁻¹' A) := by
      rw [ProbabilityTheory.cond_apply hSn_meas (P.map W) A,
        Measure.map_apply hW hSn_meas, Measure.map_apply hW (hSn_meas.inter hA),
        Set.preimage_inter, hE_eq]
    rw [hLHS, hRHS]
  -- positive mass of `Sn` under `P.map W`.
  have hWmap_prob' : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  have hSn_pos : (P.map W) Sn ≠ 0 := by
    rw [Measure.map_apply hW hSn_meas]
    have : W ⁻¹' Sn = E := by ext ω; simp [hE_def, hSn_def]
    rw [this, hE_def]; exact hn
  -- **density formula for `Q.map W`** (cond density, reusable across the `≠⊥` / entropy blocks).
  set fW : ℝ → ℝ := fun x => ((P.map W).rnDeriv volume x).toReal with hfW_def
  set c : ℝ≥0∞ := (P.map W) Sn with hc_def
  have hc_top : c ≠ ∞ := measure_ne_top _ _
  set cbar : ℝ := (c⁻¹).toReal with hcbar_def
  have hcbar_nn : 0 ≤ cbar := ENNReal.toReal_nonneg
  have h_rn : (Q.map W).rnDeriv volume
      =ᵐ[volume] fun x => c⁻¹ * Sn.indicator ((P.map W).rnDeriv volume) x := by
    rw [hQW_eq]; exact rnDeriv_cond_eq (P.map W) hSn_meas hSn_pos
  -- abbreviation: `fn x := ((Q.map W).rnDeriv volume x).toReal` (the truncated density, real).
  set fn : ℝ → ℝ := fun x => ((Q.map W).rnDeriv volume x).toReal with hfn_def
  have hfn_meas : Measurable fn := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  -- `∫⁻ ofReal(fW) = 1` (probability density of `P.map W`).
  have hfW_meas : Measurable (fun x => ENNReal.ofReal (fW x)) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.ennreal_ofReal
  have hfW_lint : (∫⁻ x, ENNReal.ofReal (fW x) ∂volume) = 1 := by
    have hae_eq : (fun x => ENNReal.ofReal (fW x)) =ᵐ[volume] (P.map W).rnDeriv volume := by
      filter_upwards [(P.map W).rnDeriv_ne_top volume] with x hx
      rw [hfW_def]; exact ENNReal.ofReal_toReal hx
    rw [lintegral_congr_ae hae_eq, Measure.lintegral_rnDeriv hW_ac, measure_univ]
  -- **negative-part lintegral `B(W_n) < ⊤`** (from `hW_negPart_fin = B(W) < ⊤`).
  have hBn_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (fn x))) ∂volume) ≠ ⊤ := by
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
        show -(Real.negMulLog (cbar * fW x)) = cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))
        rw [Real.negMulLog_mul cbar (fW x)]
        ring_nf
        rw [Real.negMulLog]
        ring
      · rw [Set.indicator_of_notMem hxs (f := (P.map W).rnDeriv volume),
          Set.indicator_of_notMem hxs
            (f := fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x))))]
        simp [Real.negMulLog]
    rw [lintegral_congr_ae h_int_eq]
    -- Bound the indicator integrand by two finite-integral pieces.
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
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hbound)
    have hg1_meas : Measurable
        (fun x => ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)) :=
      measurable_const.mul hfW_meas
    have hnegm_meas : Measurable (fun x => ENNReal.ofReal (-(Real.negMulLog (fW x)))) :=
      ((Real.continuous_negMulLog.measurable.comp
        ((Measure.measurable_rnDeriv _ _).ennreal_toReal)).neg).ennreal_ofReal
    rw [lintegral_add_left hg1_meas]
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · rw [lintegral_const_mul _ hfW_meas, hfW_lint, mul_one]; exact ENNReal.ofReal_ne_top
    · rw [lintegral_const_mul _ hnegm_meas]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW_negPart_fin
  -- **positive-part lintegral `A(W_n) < ⊤`** (compact support: `negMulLog fn ≤ 1` on `Sn`,
  -- `fn = 0` off `Sn`, and `volume Sn < ⊤`).
  have hAn_fin :
      (∫⁻ x, ENNReal.ofReal (Real.negMulLog (fn x)) ∂volume) ≠ ⊤ := by
    -- `ofReal(negMulLog fn) ≤ 1_Sn` pointwise (a.e.), and `∫⁻ 1_Sn = volume Sn < ⊤`.
    have hbound : (fun x => ENNReal.ofReal (Real.negMulLog (fn x)))
        ≤ᵐ[volume] fun x => Sn.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      filter_upwards [h_rn] with x hx
      by_cases hxs : x ∈ Sn
      · rw [Set.indicator_of_mem hxs]
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_one.le
        calc Real.negMulLog (fn x) ≤ 1 - fn x := Real.negMulLog_le_one_sub_self ENNReal.toReal_nonneg
          _ ≤ 1 := by have : (0 : ℝ) ≤ fn x := ENNReal.toReal_nonneg; linarith
      · rw [Set.indicator_of_notMem hxs]
        -- off `Sn`, `fn x = 0`, so `negMulLog 0 = 0`, `ofReal 0 = 0`.
        have hfn0 : fn x = 0 := by
          rw [hfn_def]; simp only; rw [hx, Set.indicator_of_notMem hxs]; simp
        rw [hfn0]; simp [Real.negMulLog]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
    rw [lintegral_indicator hSn_meas, setLIntegral_const, one_mul]
    -- `volume Sn < ⊤` since `Sn ⊆ Icc (-n) n` is bounded.
    have hSn_sub : Sn ⊆ Set.Icc (-(n : ℝ)) (n : ℝ) := by
      intro r hr; rw [hSn_def, Set.mem_setOf_eq, abs_le] at hr; exact ⟨hr.1, hr.2⟩
    exact ne_top_of_le_ne_top (measure_Icc_lt_top.ne) (measure_mono hSn_sub)
  -- **full differential-entropy integrability of `Q.map W`** (both parts finite ⟹ integrable).
  have hW_ent_Q : Integrable (fun x => Real.negMulLog (fn x)) volume := by
    refine ⟨(Real.continuous_negMulLog.measurable.comp hfn_meas).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    -- `∫⁻ ofReal‖negMulLog fn‖ = ∫⁻ ofReal(negMulLog fn) + ∫⁻ ofReal(-(negMulLog fn)) = A + B < ∞`.
    have h_abs_eq : (fun x => ENNReal.ofReal ‖Real.negMulLog (fn x)‖)
        = fun x => ENNReal.ofReal (Real.negMulLog (fn x))
          + ENNReal.ofReal (-(Real.negMulLog (fn x))) := by
      funext x
      rw [Real.norm_eq_abs]
      rcases le_total 0 (Real.negMulLog (fn x)) with h | h
      · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -(Real.negMulLog (fn x)) ≤ 0),
          add_zero]
      · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
    have hposm : Measurable (fun x => ENNReal.ofReal (Real.negMulLog (fn x))) :=
      (Real.continuous_negMulLog.measurable.comp hfn_meas).ennreal_ofReal
    rw [h_abs_eq, lintegral_add_left hposm]
    exact lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hAn_fin, hBn_fin⟩)
  -- `h(W_n) ≠ ⊥` (compact-support ⟹ finite differential entropy ⟹ `= (real : EReal) ≠ ⊥`).
  have hW_ne_bot : differentialEntropyExt (Q.map W) ≠ ⊥ := by
    rw [differentialEntropyExt_of_ac_integrable hW_ac_Q hW_ent_Q]
    exact EReal.coe_ne_bot _
  -- abbreviations for the sum law `ν := Q.map (W+V) = (Q.map W) ∗ (Q.map V)` and its density.
  set ν : Measure ℝ := Q.map (fun ω => W ω + V ω) with hν_def
  set rfun : ℝ → ℝ := fun x => (ν.rnDeriv volume x).toReal with hrfun_def
  -- **`B(ν) < ⊤`** (sum-marginal negative-part), via the single-component helper
  -- `negPart_negMulLog_conv_single_ne_top` averaging over the probability measure `Q.map V`
  -- (no a.c. on `V` needed).  `B(Q.map W) < ⊤` is `hBn_fin` (= `hW_negPart_fin` truncated).
  have hBn_fin' :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((Q.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤ := hBn_fin
  have hν_conv : ν = (Q.map W) ∗ (Q.map V) := hsum_conv
  have hBnu_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (rfun x))) ∂volume) ≠ ⊤ := by
    have hconv_fin := negPart_negMulLog_conv_single_ne_top (Q.map W) (Q.map V) hW_ac_Q hBn_fin'
    rw [hrfun_def, hν_conv]; exact hconv_fin
  -- **Case split on whether the sum entropy integrand is integrable.**
  by_cases hent_sum : Integrable (fun x => Real.negMulLog (rfun x)) volume
  · -- **Case B (finite branch)**: descend to the workhorse `differentialEntropy` and prove the
    -- real inequality `h(Q.map W) ≤ h(ν)` via per-fibre translate Gibbs.
    have hν_ac : ν ≪ volume := hWV_ac_Q
    have hent_sum' : Integrable
        (fun x => Real.negMulLog ((ν.rnDeriv volume x).toReal)) volume := hent_sum
    rw [differentialEntropyExt_of_ac_integrable hν_ac hent_sum',
      differentialEntropyExt_of_ac_integrable hW_ac_Q hW_ent_Q]
    refine EReal.coe_le_coe_iff.mpr ?_
    -- **per-fibre translate Gibbs**.  Set `μWz z := (Q.map W).map (·+z)` (the per-fibre conditional
    -- law of `W+V` given `V=z`, by independence).  Each `μWz z ≪ ν` (a.e. z), so per-fibre Gibbs gives
    -- `h(μWz z) ≤ -∫ x, log(r x) ∂(μWz z)`, and translation invariance gives `h(μWz z) = h(Q.map W)`.
    -- Integrating over `μV` and collapsing the RHS by Tonelli (`r(x) = ∫ fW(x-z) ∂μV`) yields `h(ν)`.
    haveI hν_prob : IsProbabilityMeasure ν := by
      rw [hν_def]; exact Measure.isProbabilityMeasure_map (hW.add hV).aemeasurable
    set μV : Measure ℝ := Q.map V with hμV_def
    set fW : ℝ → ℝ := fun x => ((Q.map W).rnDeriv volume x).toReal with hfWb_def
    -- the per-fibre translated measure.
    set μWz : ℝ → Measure ℝ := fun z => (Q.map W).map (fun x => x + z) with hμWz_def
    -- (a) per-fibre a.c. `μWz z ≪ ν`  (a.e. z ∂μV).
    have hμWz_ac_ν : ∀ᵐ z ∂μV, μWz z ≪ ν := by
      have hper := condDistrib_ae_absolutelyContinuous_indep_add
        (μW := Q.map W) (μV := Q.map V) hW_ac_Q
      filter_upwards [hper] with z hz
      show (Q.map W).map (fun x => x + z) ≪ ν
      rw [hν_conv]; exact hz
    -- (b) per-fibre a.c. `μWz z ≪ volume`  (translation invariance).
    have hμWz_ac_vol : ∀ z, μWz z ≪ volume := by
      intro z
      show (Q.map W).map (fun x => x + z) ≪ volume
      have hshift : Measurable fun x : ℝ => x + z := by fun_prop
      have h_map_vol : (volume : Measure ℝ).map (fun x : ℝ => x + z) = volume :=
        MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) z
      have := hW_ac_Q.map hshift
      rwa [h_map_vol] at this
    haveI hμWz_prob : ∀ z, IsProbabilityMeasure (μWz z) := by
      intro z
      show IsProbabilityMeasure ((Q.map W).map (fun x => x + z))
      exact Measure.isProbabilityMeasure_map (by fun_prop : Measurable fun x : ℝ => x + z).aemeasurable
    -- (c) per-fibre finite entropy.
    have hμWz_ent : ∀ z, Integrable
        (fun x => Real.negMulLog ((μWz z).rnDeriv volume x).toReal) volume := by
      intro z
      show Integrable (fun x => Real.negMulLog
        (((Q.map W).map (fun x => x + z)).rnDeriv volume x).toReal) volume
      exact integrable_negMulLog_rnDeriv_map_add_const (ν := Q.map W) z hW_ent_Q
    -- (d) per-fibre cross-integrability `Integrable (log r) (μWz z)`  (a.e. z), from the Tonelli
    -- finiteness `∫ r |log r| < ∞` (= `hent_sum` rewritten via `negMulLog r = -r log r`).
    have hcross_int : ∀ᵐ z ∂μV, Integrable
        (fun x => Real.log (rfun x)) (μWz z) := by
      sorry
    -- (e) per-fibre Gibbs:  `h(μWz z) ≤ -∫ x, log(r x) ∂(μWz z)`  (a.e. z).
    have hgibbs : ∀ᵐ z ∂μV,
        differentialEntropy (μWz z) ≤ - ∫ x, Real.log (rfun x) ∂(μWz z) := by
      filter_upwards [hμWz_ac_ν, hcross_int] with z hz_ac hz_cross
      exact EPIInfiniteVarianceTruncation.differentialEntropy_le_cross_entropy
        (hμWz_ac_vol z) hν_ac hz_ac (hμWz_ent z) hz_cross
    -- (f) translation invariance:  `h(μWz z) = h(Q.map W)`.
    have htrans_ent : ∀ z, differentialEntropy (μWz z) = differentialEntropy (Q.map W) := by
      intro z
      show differentialEntropy ((Q.map W).map (fun x => x + z)) = differentialEntropy (Q.map W)
      exact differentialEntropy_map_add_const hW_ac_Q z
    -- (g) the cross-entropy term collapses (after integration over μV) to `-h(ν)`.
    -- the μV-integrability of `z ↦ -∫ x, log(r x) ∂(μWz z)` (for `integral_mono_ae`).
    have hRHS_int : Integrable (fun z => - ∫ x, Real.log (rfun x) ∂(μWz z)) μV := by
      sorry
    -- (h) `∫ z, (-∫ x, log(r x) ∂(μWz z)) ∂μV = - ∫ x, r x · log(r x) ∂volume = h(ν)`.
    have hRHS_eq : (∫ z, (- ∫ x, Real.log (rfun x) ∂(μWz z)) ∂μV)
        = differentialEntropy ν := by
      sorry
    -- assemble:  `h(Q.map W) = ∫ z, h(Q.map W) ∂μV ≤ ∫ z, (-∫ log r ∂μWz) ∂μV = h(ν)`.
    calc differentialEntropy (Q.map W)
        = ∫ _z, differentialEntropy (Q.map W) ∂μV := by
          rw [integral_const, probReal_univ, one_smul]
      _ ≤ ∫ z, (- ∫ x, Real.log (rfun x) ∂(μWz z)) ∂μV := by
          apply integral_mono_ae (integrable_const _) hRHS_int
          filter_upwards [hgibbs] with z hz
          calc differentialEntropy (Q.map W) = differentialEntropy (μWz z) := (htrans_ent z).symm
            _ ≤ _ := hz
      _ = differentialEntropy ν := hRHS_eq
  · -- **Case A (infinite branch)**: `¬ hent_sum` and `B(ν) < ⊤` ⟹ `A(ν) = ⊤` ⟹
    -- `differentialEntropyExt ν = ⊤`, then `h(Q.map W) ≤ ⊤` by `le_top`.
    set g : ℝ → ℝ := fun x => Real.negMulLog (rfun x) with hg_def
    have hg_meas : Measurable g :=
      Real.continuous_negMulLog.measurable.comp
        ((Measure.measurable_rnDeriv _ _).ennreal_toReal)
    set Aint : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (g x) ∂volume with hA_def
    set Bint : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(g x)) ∂volume with hB_def
    have hB_lt_top : Bint ≠ ⊤ := by rw [hB_def]; exact hBnu_fin
    have hA_top : Aint = ⊤ := by
      have hnotfin : ¬ HasFiniteIntegral g volume := fun hfin =>
        hent_sum ⟨hg_meas.aestronglyMeasurable, hfin⟩
      have henorm_top : (∫⁻ x, ‖g x‖ₑ ∂volume) = ⊤ := by
        by_contra h
        exact hnotfin (hasFiniteIntegral_iff_enorm.mpr (lt_of_le_of_ne le_top h))
      have hsplit : (∫⁻ x, ‖g x‖ₑ ∂volume) = Aint + Bint := by
        rw [hA_def, hB_def, ← lintegral_add_left
          (Measurable.ennreal_ofReal hg_meas) (fun x => ENNReal.ofReal (-(g x)))]
        apply lintegral_congr; intro x
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        rcases le_or_gt 0 (g x) with h | h
        · have hneg : ENNReal.ofReal (-(g x)) = 0 :=
            ENNReal.ofReal_of_nonpos (by linarith)
          rw [abs_of_nonneg h, hneg, add_zero]
        · have hpos : ENNReal.ofReal (g x) = 0 :=
            ENNReal.ofReal_of_nonpos h.le
          rw [abs_of_neg h, hpos, zero_add]
      rw [hsplit] at henorm_top
      by_contra hA
      exact (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hA, lt_of_le_of_ne le_top hB_lt_top⟩).ne
        henorm_top
    have hdiff_top : differentialEntropyExt ν = ⊤ := by
      rw [differentialEntropyExt_of_ac hWV_ac_Q]
      show ((Aint : EReal) - (Bint : EReal)) = ⊤
      rw [hA_def, hB_def, ← hg_def] at *
      rw [hA_top, EReal.coe_ennreal_top]
      exact EReal.top_sub (by
        rw [Ne, EReal.coe_ennreal_eq_top_iff]; exact hB_lt_top)
    rw [hdiff_top]; exact le_top

/-- **`h(W_n) → h(W)` の極限**: truncation 緩和で entropy 単調増加 → 極限。`h(W) = ⊤` のときは
`h(W_n) ↑ ⊤` の単調発散 (有界増加列の ⊤ への発散) で、weak-convergence portmanteau を経由しない。
route T が `tendsto_measure_iUnion_atTop` (`EPIInfiniteVarianceTruncation.lean:110`) ベースの
極限を実証済。

route β' Phase 3 で埋める。極限が density a.e. 収束 (`differentialEntropyExt_posPart_le_liminf_of_ae_tendsto`
適用可) or 単調収束のみで閉じ、weak-conv 定義を使わないことを担保する。

独立 honesty audit 2026-06-08 (skeleton, 4-check PASS → honest_residual): (1) 非循環 — 結論
(極限 `h(W_n) → h(W)`) は仮説 `hW`/`hW_ac` と非同型。(2) 非バンドル — 両仮説は可測/絶対連続の
regularity precondition、極限の核を encode せず。(3) 非退化 — `:True` slot なし。(4) sufficiency
— truncation 緩和列の entropy 単調増加 → 極限 (`h(W)=⊤` で `h(W_n)↑⊤`) は正しい (route T が
`tendsto_measure_iUnion_atTop` で同型極限を実証)。`plan:` 妥当。
**独立 auditor 確認 (fresh subagent、2026-06-08)**: 4-check PASS、honest_residual。`plan:` slug 実在。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_truncW_tendsto
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume) :
    Tendsto (fun n => differentialEntropyExt ((truncW P W n).map W)) atTop
      (𝓝 (differentialEntropyExt (P.map W))) := by
  sorry

/-- **gateway ⊤ 枝 (無条件)**: `h(W) = ⊤ ⟹ h(W+V) = ⊤`、無条件版② (i-a) を bypass。
per-n 単調性 `h(W_n) ≤ h(W_n + V)` (`differentialEntropyExt_mono_add_truncW`) と `h(W_n) ↑ ⊤`
(`differentialEntropyExt_truncW_tendsto`) を組み、`h(W_n + V) ≥ h(W_n) → ⊤` で `h(W+V) = ⊤`。
route T capstone Case 2 (`EPIInfiniteVarianceCapstone.lean:343`、`entropyPowerExt = ⊤` を
`le_top`) と同型の「⊤ 枝は EReal ⊤ 表現で trivial に閉じる」を再利用する。

**⊤ 枝のみ無条件、有限枝は別 lemma** (finite ② / coe 枝)。`_unconditional` 命名は本 ⊤ 枝が真に
無条件 (regularity precondition `hW`/`hV`/`hWV`/`hW_ac` のみ、無条件版② sorry を継承しない) なため
honest。`hW_top` (h(W)=⊤) は場合分け precondition で load-bearing でない。

route β' Phase 4 で埋める。

独立 honesty audit 2026-06-08 (skeleton, 4-check + name-laundering PASS → honest_residual):
**`_unconditional` 命名 = NOT name-laundering**。signature は既存 `differentialEntropyExt_top_of_indep_add`
(`EPIUncondMonotone.lean:153`、(i-a) `differentialEntropyExt_indep_add_eq_add_klDiv` の transitive
sorry を継承) と **完全同一の仮説群** (`hW`/`hV`/`hWV`/`hW_ac`/`hW_top`、結論も同一)。新規 load-bearing
hypothesis を threading していない — `_unconditional` は「(i-a) sorry を継承しない別 route (truncation
近似) で同結論を建てる」という proof-route の主張で、「仮説が無い」主張ではない (CORE doctrine の
name_laundering は「open load-bearing hyp or 完成偽装 sorry-body」、本件は body sorry が `@residual`
で正直にマーク済 = 偽装でない)。**`hW_top` load-bearing 判定**: `h(W)=⊤` は ⊤ 枝の場合分け
precondition、結論の核 (= h(W+V)=⊤) を encode せず。hard core = 単調性 `h(W)≤h(W+V)` (#3 が供給)、
`hW_top` + 単調性 → `h(W+V)≥⊤` → `=⊤` (`le_top`)。`le_top` は退化定義悪用でなく EReal ⊤ 表現の
genuine 利用 (route T capstone Case 2 と同型)。(4) sufficiency — `h(W)=⊤` + 単調性で `h(W+V)=⊤` は
正しい含意 (反例なし: 単調性が無条件で成立する以上 ⊤ 入力は ⊤ 出力)。`plan:` 妥当。

**独立 auditor 確認 (fresh subagent、2026-06-08)**: `_unconditional` 命名 = **NOT name-laundering**。
CORE doctrine の name_laundering は「open load-bearing hyp を残したまま / 完成偽装 sorry-body で _full
等を名乗る」だが、本件は (a) load-bearing hyp なし (`hW`/`hV`/`hWV`/`hW_ac` は regularity、`hW_top` は
場合分け precondition で結論核 = h(W+V)=⊤ を encode せず)、(b) body sorry は `@residual(plan:...)` で
正直にマーク済 = 偽装でない。命名は「(i-a) sorry を継承しない別 route で同結論を建てる」proof-route の
主張で正当。⚠ 本 ⊤ 枝 closure (body) は #3 の単調性 (4 sorry 残) + #2/#3 極限に transitive 依存ゆえ
**現状 #4 自体が未着手 sorry**、proof-done でない (honest_residual)。honest sorry、4-check + name-laundering
PASS。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_top_of_indep_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  sorry

end InformationTheory.Shannon
