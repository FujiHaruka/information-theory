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
  -- ① fibre identification (c = 1): `condDiffEntExt (W + V | V) Q = h_ext(Q.map W)`.
  have hone : (fun ω => W ω + (1 : ℝ) * V ω) = (fun ω => W ω + V ω) := by
    funext ω; rw [one_mul]
  have hfibre : condDifferentialEntropyExt (fun ω => W ω + V ω) V Q
      = differentialEntropyExt (Q.map W) := by
    have := condDifferentialEntropyExt_indep_add_eq W V Q 1 hW hV hindep hW_ac_Q
    rwa [hone] at this
  -- W + V is a.c. under `Q` (`hW_ac_Q` + independence).
  have hWV_ac_Q : (Q.map (fun ω => W ω + V ω)) ≪ volume :=
    map_add_absolutelyContinuous W V Q hW hV hindep hW_ac_Q
  -- Probability-measure instances on the relevant marginals (needed for the fibre identification
  -- and the finite ②).
  haveI hWmap_prob : IsProbabilityMeasure (Q.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hVmap_prob : IsProbabilityMeasure (Q.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  -- **fibre identification** (c = 1): `condDistrib (W+V) V Q =ᵐ[Q.map V] affineShiftKernel (Q.map W) 1`.
  -- Mirror of `condDifferentialEntropyExt_indep_add_eq` (Step 1-2): the joint `(V, W+V)` is the
  -- affine push of the product law (independence), so the regular conditional kernel is the
  -- z-dependent affine shift of `Q.map W`.
  have hjoint_VW : Q.map (fun ω => (V ω, W ω + V ω))
      = (Q.map V) ⊗ₘ (affineShiftKernel (Q.map W) 1) := by
    have hZX : IndepFun V W Q := hindep.symm
    have hjoint_VX : Q.map (fun ω => (V ω, W ω)) = (Q.map V).prod (Q.map W) :=
      (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hW.aemeasurable).mp hZX
    have hg : Measurable fun p : ℝ × ℝ => (p.1, p.2 + (1 : ℝ) * p.1) := by fun_prop
    have hcomp : (fun ω => (V ω, W ω + V ω))
        = (fun p : ℝ × ℝ => (p.1, p.2 + (1 : ℝ) * p.1)) ∘ (fun ω => (V ω, W ω)) := by
      funext ω; simp [one_mul, add_comm]
    rw [hcomp, ← Measure.map_map hg (hV.prodMk hW), hjoint_VX,
      prod_map_affine_eq_compProd]
  have hae : condDistrib (fun ω => W ω + V ω) V Q
      =ᵐ[Q.map V] affineShiftKernel (Q.map W) 1 :=
    condDistrib_ae_eq_of_measure_eq_compProd V (hW.add hV).aemeasurable hjoint_VW
  -- The marginal / conditional extended entropies are `≠ ⊥` (compact support ⟹ finite
  -- differential entropy ⟹ ≠ −∞). Localized: the two ⊥-exclusions on `Q.map W` and `Q.map (W+V)`.
  -- **Set-up shared by the `≠ ⊥` blocks**: `Q.map W = cond (P.map W) Sn` (single-variable
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
  -- **`hWV_ne_bot` (sum-marginal negative-part)** = `B(W_n+V) < ⊤`. NOT a translate of `Q.map W`:
  -- `Q.map(W+V)` is the mixture/convolution `f_{W_n} ∗ μ_V`, whose negative-part finiteness needs
  -- the route-T Jensen + Tonelli argument (`(g log g)⁺ ≤ ∫ f_{W_n}(·−v) log f_{W_n}(·−v))⁺ dμ_V`,
  -- Tonelli + 平行移動不変で `≤ B(W_n) = hBn_fin`)。route T `integrable_negPart_negMulLog_map_condTrunc_sum`
  -- (`EPIInfiniteVarianceTruncation.lean:600`、~250 行 genuine) は joint `condTrunc` 専用 + 両成分
  -- 有限エントロピー前提のため直接再利用不可 (V のエントロピー仮説なし)。単独成分 (W_n) 版への一般化が
  -- 必要 = route-T-scale self-build、本 fill の予算超過 (≥150 行)。escalate 候補。
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have hWV_ne_bot : differentialEntropyExt (Q.map (fun ω => W ω + V ω)) ≠ ⊥ := by sorry
  have hcond_ne_bot : condDifferentialEntropyExt (fun ω => W ω + V ω) V Q ≠ ⊥ := by
    rw [hfibre]; exact hW_ne_bot
  -- ② finite chain rule with `X := W + V`, `Z := V`:
  -- `h_ext(W+V) = h_ext(W+V | V) + I(W+V; V)`.
  -- The eleven regularity hypotheses of the finite ② are supplied below.  The genuine ones
  -- (`hWV_ac_Q` / `hκ_ac` / `hκ_logp_int`) reduce to `Q.map W` via the fibre identification `hae`
  -- (each fibre a translate of `Q.map W`); the four that reference the **sum marginal**
  -- `Q.map(W+V)` (`h_ac` / `hκ_cross_int` / `hκ_KL` / `hWV_ne_bot`) are the genuine analytic crux
  -- (mixture/convolution, no full-support reference) and stay as honest sorry.
  -- **`h_ac` (joint ≪ product)**: reduce to per-fibre `condDistrib (W+V) V Q z ≪ Q.map(W+V)` a.e. z
  -- via `absolutelyContinuous_compProd_right_iff`, then close it from the **continuous** disintegration
  -- a.c. self-build `condDistrib_ae_absolutelyContinuous_indep_add` (Mathlib general/non-discrete 版は
  -- 不在、in-tree `Bridge.condDistrib_ae_absolutelyContinuous_map` は `[Countable X]` 専用で `X=ℝ` 不可)。
  -- The fibre is identified by `hae` as `(Q.map W).map (·+z)`, and the sum marginal as the convolution
  -- `(Q.map W) ∗ (Q.map V)`.
  -- The sum law equals the convolution of the W- and V-marginals (independence).
  have hsum_conv : Q.map (fun ω => W ω + V ω) = (Q.map W) ∗ (Q.map V) := by
    have := hindep.map_add_eq_map_conv_map hW hV
    simpa [Pi.add_apply] using this
  have h_ac : (Q.map V) ⊗ₘ condDistrib (fun ω => W ω + V ω) V Q
      ≪ (Q.map V) ⊗ₘ Kernel.const ℝ (Q.map (fun ω => W ω + V ω)) := by
    rw [Measure.absolutelyContinuous_compProd_right_iff]
    -- per-fibre a.c. of the translate `(Q.map W).map (·+1·z)` w.r.t. the sum marginal.
    have hper := condDistrib_ae_absolutelyContinuous_indep_add
      (μW := Q.map W) (μV := Q.map V) hW_ac_Q
    filter_upwards [hae, hper] with z hz hper_z
    rw [Kernel.const_apply, hz, affineShiftKernel_apply, one_mul]
    rw [hsum_conv]
    -- `hper_z : (Q.map W).map (·+z) ≪ (Q.map W) ∗ (Q.map V)`, but the fibre shift is `·+1·z`.
    simpa [one_mul] using hper_z
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have hκ_dens_meas : Measurable
      (fun p : ℝ × ℝ => ((condDistrib (fun ω => W ω + V ω) V Q p.1).rnDeriv volume p.2)) := by
    sorry
  -- per-fibre a.c.: each fibre `condDistrib (W+V) V Q z =ᵐ (Q.map W).map (·+z)`, a translation
  -- of the a.c. measure `Q.map W` (translation-invariance of Lebesgue ⟹ a.c. is preserved).
  -- No finiteness needed; supplied genuinely from the fibre identification `hae`.
  have hκ_ac : ∀ᵐ z ∂(Q.map V), condDistrib (fun ω => W ω + V ω) V Q z ≪ volume := by
    filter_upwards [hae] with z hz
    rw [hz, affineShiftKernel_apply]
    have hshift : Measurable fun x : ℝ => x + (1 : ℝ) * z := by fun_prop
    have h_map_vol : (volume : Measure ℝ).map (fun x : ℝ => x + (1 : ℝ) * z) = volume :=
      MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) ((1 : ℝ) * z)
    have := hW_ac_Q.map hshift
    rwa [h_map_vol] at this
  -- per-fibre entropy integrability `Integrable (fκz · log fκz)`: each fibre is a translate of
  -- `Q.map W`, and `t·log t = -(negMulLog t)`, so this transfers from `hW_ent_Q` by translation
  -- invariance (`integrable_negMulLog_rnDeriv_map_add_const`).
  have hκ_logp_int : ∀ᵐ z ∂(Q.map V), Integrable
      (fun x => ((condDistrib (fun ω => W ω + V ω) V Q z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => W ω + V ω) V Q z).rnDeriv volume x).toReal)) volume := by
    filter_upwards [hae] with z hz
    have hbase := (integrable_negMulLog_rnDeriv_map_add_const (ν := Q.map W) ((1 : ℝ) * z)
      hW_ent_Q).neg
    refine hbase.congr ?_
    filter_upwards with x
    rw [hz, affineShiftKernel_apply]
    show -(Real.negMulLog (((((Q.map W).map (fun x => x + (1 : ℝ) * z)).rnDeriv volume x)).toReal))
      = (((((Q.map W).map (fun x => x + (1 : ℝ) * z)).rnDeriv volume x)).toReal)
        * Real.log ((((((Q.map W).map (fun x => x + (1 : ℝ) * z)).rnDeriv volume x)).toReal))
    rw [Real.negMulLog]; ring
  -- **`hκ_cross_int` (cross-entropy term)**: couples the fibre density `fκz` (translate of `Q.map W`)
  -- with `log(f_{Q.map(W+V)})` (= the **sum-marginal** log-density). The marginal factor is NOT a
  -- translate of `Q.map W`, so this does not reduce by the `integrable_negMulLog_rnDeriv_map_add_const`
  -- pattern; it needs a domination argument against the mixture density (route-T cross-entropy DCT
  -- style). Sum-marginal analytic crux, 予算超過。
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have hκ_cross_int : ∀ᵐ z ∂(Q.map V), Integrable
      (fun x => ((condDistrib (fun ω => W ω + V ω) V Q z).rnDeriv volume x).toReal
        * Real.log (((Q.map (fun ω => W ω + V ω)).rnDeriv volume x).toReal)) volume := by
    sorry
  -- **`hκ_KL` (per-fibre KL ≠ ∞)**: per finite ② docstring, `klDiv κz ν ≠ ∞ ↔ κz ≪ ν ∧
  -- Integrable (llr κz ν) κz` (`klDiv_ne_top`). The a.c. `κz ≪ ν` is now genuinely available
  -- (`condDistrib_ae_absolutelyContinuous_indep_add`, same supply as the closed `h_ac`), but the
  -- llr integrability `Integrable (log(fκz/r)) κz = ∫ fκz·(log fκz - log r)` requires the
  -- **cross-term** `hκ_cross_int` (sum-marginal log-density `log r`), which is still the open crux.
  -- So `hκ_KL` stays sorry until `hκ_cross_int` lands (transitive dependence on the cross-entropy
  -- domination, not on `h_ac` which is now closed).
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have hκ_KL : ∀ᵐ z ∂(Q.map V),
      klDiv (condDistrib (fun ω => W ω + V ω) V Q z) (Q.map (fun ω => W ω + V ω)) ≠ ∞ := by sorry
  have hchain := differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite
    (fun ω => W ω + V ω) V Q (hW.add hV) hV hWV_ac_Q h_ac hκ_dens_meas hκ_ac hκ_logp_int
    hκ_cross_int hκ_KL hcond_ne_bot hWV_ne_bot
  -- Equality → monotonicity: `h(W_n+V) = h(W_n) + I`, `I ≥ 0` ⟹ `h(W_n) ≤ h(W_n+V)`.
  rw [hchain, hfibre]
  have hi : (0 : EReal) ≤
      (((InformationTheory.klDiv ((Q.map V) ⊗ₘ condDistrib (fun ω => W ω + V ω) V Q)
            ((Q.map V) ⊗ₘ Kernel.const ℝ (Q.map (fun ω => W ω + V ω)))) : ℝ≥0∞) : EReal) := by
    exact_mod_cast (bot_le : (⊥ : ℝ≥0∞) ≤ _)
  calc differentialEntropyExt (Q.map W)
      = differentialEntropyExt (Q.map W) + 0 := (add_zero _).symm
    _ ≤ differentialEntropyExt (Q.map W) + _ := add_le_add_right hi _

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
