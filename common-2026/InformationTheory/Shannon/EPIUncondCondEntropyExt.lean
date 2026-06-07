import InformationTheory.Shannon.EntropyPowerExt
import InformationTheory.Shannon.EPIG2ConvEntropyMonotone
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# EReal 条件付き微分エントロピー + crux 恒等式 (i-a) の分解

EPI 無条件化 方針 Y の crux 恒等式 (i-a)
`differentialEntropyExt_indep_add_eq_add_klDiv` (`EPIUncondMonotone.lean`) を 2 部品に分解する:

- **① fibre 同定 (genuine)** `condDifferentialEntropyExt_indep_add_eq`:
  `condDifferentialEntropyExt (W + c·V | V) = differentialEntropyExt (P.map W)` (独立和、定数 fibre)。
  Real 版 `condDifferentialEntropy_indep_add_eq` (`EPIG2ConvEntropyMonotone.lean:328`) +
  `differentialEntropy_map_add_const` (`DifferentialEntropy.lean:171`) の lintegral 版ミラー。
- **② chain rule (sorry、本 chunk の唯一の crux)** `differentialEntropyExt_eq_condEntExt_add_klDiv`:
  `h_ext(X) = condDifferentialEntropyExt (X | Z) + I(X;Z)`、`I = klDiv(joint ‖ product) ≥ 0`。
  Real bridge `differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv` の sum 形・
  finiteness-free 持ち上げ (multi-session moonshot、次 chunk で攻略)。

これらを合成して (i-a) の sorry を埋める (genuine modulo ②)。

`condDifferentialEntropyExt` は `differentialEntropyExt` の正部・負部 EReal 差を lintegral でミラー
した shape (Mathlib-shape-driven、§7-6 道 A の制約1 = 定数 fibre で EReal Bochner 積分を組まない)。

SoT 計画: `docs/shannon/epi-uncond-deffix-monotone-plan.md` §7-6 (道 A)。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

/-- **EReal 条件付き微分エントロピー** (`differentialEntropyExt` の lintegral ミラー)。

各 fibre `condDistrib X Z μ z` (= `X` の `Z = z` 条件付き law) に対し、`differentialEntropyExt`
の正部 `A_z := ∫⁻ ofReal(negMulLog (density))` と負部 `B_z := ∫⁻ ofReal(-(negMulLog (density)))`
を取り、`μ.map Z` 上で平均した `(∫⁻ z A_z) − (∫⁻ z B_z)` を EReal 差で返す。

設計 (Mathlib-shape-driven、§7-6 道 A): `differentialEntropyExt` の正部・負部 A/B 構造を lintegral
でミラーする (EReal は normed space でないので EReal Bochner 積分は組まない、`∫⁻ z (ℝ≥0∞ 値) ∂(μ.map Z)`
は well-defined)。この shape を選ぶ理由: (a) ① の定数 fibre 評価が `lintegral_const` + `measure_univ`
で clean に出る、(b) ② の statement `h_ext(X) = condEntExt + klDiv` が EReal 和で well-typed
(差分 `⊤−⊤` を RHS に作らない sum 形)。`[IsFiniteMeasure μ]` は `μ.map Z` を有限にするため (Real 版 def
`condDifferentialEntropy` と同じ)。

独立 honesty audit 2026-06-07: **genuine** (退化定義悪用なし)。`differentialEntropyExt` (`@audit:ok`、def-fix で
退化トラップ除去機械検証済) の正部 A_z / 負部 B_z lintegral を `μ.map Z` 上で平均した honest な EReal 差。
`:True`/vacuous shape なし、各 fibre は条件付き法 `condDistrib X Z μ z` の正則密度を反映する非自明な値。 -/
noncomputable def condDifferentialEntropyExt
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsFiniteMeasure μ] : EReal :=
  ((∫⁻ z, (∫⁻ x, ENNReal.ofReal (Real.negMulLog
        (((condDistrib X Z μ z).rnDeriv volume x).toReal)) ∂volume) ∂(μ.map Z) : ℝ≥0∞) : EReal)
    - ((∫⁻ z, (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog
        (((condDistrib X Z μ z).rnDeriv volume x).toReal))) ∂volume) ∂(μ.map Z) : ℝ≥0∞) : EReal)

/-- **lintegral 版 translation 不変性** (`differentialEntropy_map_add_const` の lintegral ミラー)。
`ν ≪ volume` のとき、shift 後 measure `ν.map (· + y)` の `±negMulLog(rnDeriv)` の lintegral は
shift 前と等しい。`sign` で正部 (`id`) / 負部 (`Neg.neg`) を引数化した 1 本。

機構 (Real `differentialEntropy_map_add_const:174-195` の `∫` → `∫⁻` ミラー):
`measurableEmbedding_addRight` + `map_add_right_eq_self` (Lebesgue 平行移動不変) +
`MeasurableEmbedding.rnDeriv_map` で shift 後の rnDeriv を shift 前に同定し、
`MeasureTheory.lintegral_add_right_eq_self` で積分を不変化、`lintegral_congr_ae` で integrand を書換。
`sign` は a.e. 等式を保つので連続性不要、`hν` (a.c.) も `rnDeriv_map` は不要 (`SigmaFinite ν` のみ要)。 -/
theorem lintegral_ofReal_signed_negMulLog_rnDeriv_map_add_const
    {ν : Measure ℝ} [SigmaFinite ν] (y : ℝ) (sign : ℝ → ℝ) :
    (∫⁻ x, ENNReal.ofReal (sign (Real.negMulLog (((ν.map (· + y)).rnDeriv volume x).toReal)))
        ∂volume)
      = ∫⁻ x, ENNReal.ofReal (sign (Real.negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume := by
  -- `f := (· + y)` is a measurable embedding; Lebesgue is translation-invariant.
  have hf : MeasurableEmbedding (fun x : ℝ => x + y) := measurableEmbedding_addRight y
  have h_map_vol : (volume : Measure ℝ).map (· + y) = volume :=
    MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) y
  -- rnDeriv after the shift, evaluated at `x + y`, equals rnDeriv before the shift.
  have h_rn := hf.rnDeriv_map ν (volume : Measure ℝ)
  rw [h_map_vol] at h_rn
  -- Substitute `x ↦ x + y` inside the lintegral (translation invariance of `∫⁻`).
  rw [← MeasureTheory.lintegral_add_right_eq_self
      (fun x => ENNReal.ofReal
        (sign (Real.negMulLog (((ν.map (· + y)).rnDeriv volume x).toReal)))) y]
  -- Rewrite the integrand using the a.e. identification of the rnDeriv.
  refine lintegral_congr_ae ?_
  filter_upwards [h_rn] with x hx
  rw [hx]

/-- **(①) EReal fibre 同定** (genuine): `X ⊥ Z` のとき
`condDifferentialEntropyExt (X + c·Z | Z) = differentialEntropyExt (μ.map X)` (独立和の fibre は
z 非依存定数 `h_ext(μ.map X)`)。

Real 版 `condDifferentialEntropy_indep_add_eq` (`EPIG2ConvEntropyMonotone.lean:328`、`@audit:ok`) +
`differentialEntropy_map_add_const` (`DifferentialEntropy.lean:171`) の lintegral ミラー。fibre 同定
`condDistrib (X + c·Z) Z μ =ᵐ[μ.map Z] affineShiftKernel (μ.map X) c` を `prod_map_affine_eq_compProd`
+ `condDistrib_ae_eq_of_measure_eq_compProd` で得て、各 fibre を `lintegral_ofReal_signed_negMulLog_rnDeriv_map_add_const`
で `μ.map X` に落とす。

仮説は全 regularity precondition (measurability / `IndepFun` / a.c.)、load-bearing でない。
独立 honesty audit 2026-06-07: **genuine** (PASS)。body は Real 版 `condDifferentialEntropy_indep_add_eq`
(`@audit:ok`) の機械的 `∫`→`∫⁻` ミラー、独立 sorry なし (file の sorry warning は ② のみ = 本定理 sorryAx-free)。
循環/バンドル/退化なし。@audit:ok -/
theorem condDifferentialEntropyExt_indep_add_eq
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropyExt (fun ω => X ω + c * Z ω) Z μ
      = differentialEntropyExt (μ.map X) := by
  set W : Ω → ℝ := fun ω => X ω + c * Z ω with hW_def
  have hW : Measurable W := hX.add ((measurable_const).mul hZ)
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hsf : SigmaFinite (μ.map X) := inferInstance
  -- Step 1: joint `(Z, X)` is the product law (independence).
  have hZX : IndepFun Z X μ := hXZ.symm
  have hjoint_ZX : μ.map (fun ω => (Z ω, X ω)) = (μ.map Z).prod (μ.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hX.aemeasurable).mp hZX
  -- Step 1': push the product through the affine map `g (z, x) = (z, x + c·z)`.
  have hg : Measurable fun p : ℝ × ℝ => (p.1, p.2 + c * p.1) := by fun_prop
  have hjoint_ZW : μ.map (fun ω => (Z ω, W ω))
      = (μ.map Z) ⊗ₘ (affineShiftKernel (μ.map X) c) := by
    have hcomp : (fun ω => (Z ω, W ω))
        = (fun p : ℝ × ℝ => (p.1, p.2 + c * p.1)) ∘ (fun ω => (Z ω, X ω)) := by
      funext ω; simp [hW_def]
    rw [hcomp, ← Measure.map_map hg (hZ.prodMk hX), hjoint_ZX,
      prod_map_affine_eq_compProd]
  -- Step 2: uniqueness of the regular conditional distribution.
  have hae : condDistrib W Z μ =ᵐ[μ.map Z] affineShiftKernel (μ.map X) c :=
    condDistrib_ae_eq_of_measure_eq_compProd Z hW.aemeasurable hjoint_ZW
  -- Step 3: unfold both sides and reduce the inner fibre integrals to the constant
  -- `A_X / B_X` via translation invariance, then average the constant over `μ.map Z`.
  rw [condDifferentialEntropyExt, differentialEntropyExt_of_ac hX_ac]
  -- Reduce each (positive / negative part) `∫⁻ z` to the constant `μ.map X` integral.
  have hpart : ∀ sign : ℝ → ℝ,
      (∫⁻ z, (∫⁻ x, ENNReal.ofReal (sign (Real.negMulLog
          (((condDistrib W Z μ z).rnDeriv volume x).toReal))) ∂volume) ∂(μ.map Z))
        = ∫⁻ x, ENNReal.ofReal (sign (Real.negMulLog (((μ.map X).rnDeriv volume x).toReal)))
            ∂volume := by
    intro sign
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ x, ENNReal.ofReal
        (sign (Real.negMulLog (((μ.map X).rnDeriv volume x).toReal))) ∂volume) ?_]
    · rw [lintegral_const, measure_univ, mul_one]
    · filter_upwards [hae] with z hz
      rw [hz, affineShiftKernel_apply]
      exact lintegral_ofReal_signed_negMulLog_rnDeriv_map_add_const (c * z) sign
  rw [hpart (fun r => r), hpart (fun r => -r)]

/-- **(②) EReal chain rule** (finiteness-free、crux 本体、未証明)。
`h_ext(X) = h_ext(X | Z) + I(X;Z)`、`I = klDiv(joint ‖ product)` (ℝ≥0∞ → EReal coe、非負)。

`hcond_ne_bot` (`condDifferentialEntropyExt X Z μ ≠ ⊥`) 制限必須: ⊥ fibre で恒等式 FALSE
(`⊥ + klDiv = ⊥ ≠ 有限/⊤` LHS)。`hX_ac` は `h_ext(X)` が密度を反映する precondition (非 a.c. で
LHS=⊥ となり恒等式が崩れる)。これらは regularity scope であり結論の核 (klDiv 項 = 結論 RHS の一部) を
仮説に encode していない (load-bearing でない、non-bundle)。

最終証明の候補資産 (本 chunk では未使用、次 chunk の足掛かり): Mathlib に finiteness-free な KL chain
rule `InformationTheory.klDiv_compProd_eq_add`
(`Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204`、`klDiv (μ⊗κ) (ν⊗η) = klDiv μ ν +
klDiv (μ⊗κ) (μ⊗η)`、無仮定) が存在 (loogle/Read 機械確認、`ℝ≥0∞` 値・無仮定で成立)。Real bridge
`differentialEntropy_sub_condDifferentialEntropy_eq_toReal_klDiv`
(`EPIG2ConvEntropyMonotone.lean:124`、`@audit:ok`、差分 `.toReal` 形、8 integrability precondition) の
sum 形・finiteness-free 持ち上げが本体。

独立 honesty audit 2026-06-07 (crux ②): **honest_residual** (PASS、tier 2)。4-check:
(1) 非循環 — 結論 = entropy 分解恒等式、いずれの仮説型 (Measurable/≪/≠⊥) とも非同型、body は素の sorry。
(2) 非バンドル — 全仮説が regularity (可測性・絶対連続 `hX_ac`・有限側 `hcond_ne_bot`)、`*Hypothesis`/`IsXxxClaim`
predicate 不在。**klDiv 項 = 結論 RHS の一部** (I(X;Z)、`InformationTheory.klDiv : Measure→Measure→ℝ≥0∞` を EReal
coe)、仮説に不等式核を抱えていない (core-reconstruction 不発火、load-bearing でない)。
(3) 非退化 — `hcond_ne_bot` は vacuous truth 化でなく h(X|Z)=−∞ の **偽になる枝を除外** する honest scope
(EReal: `condEntExt=⊥ ⟹ ⊥+klDiv=⊥` ≠ 有限/⊤ LHS)、body に exfalso 退化悪用なし (素の sorry)。
V≡0(Dirac) 退化: W+V=W・joint=product・klDiv=0 → `h(W)=h(W)+0` ✓。
(4) sufficiency — finiteness-free 成立性を退化境界 3 試行で精査・棄却:
  • `klDiv=∞` (joint 非 a.c. or llr 非可積分) で RHS = `condEntExt+⊤ = ⊤` (`add_top_of_ne_bot`、`hcond_ne_bot` 経由)
    → 要 `h_ext(X)=⊤`。連続 MI 恒等式で `I=∞ ⟹ (h(X)=⊤ ∨ h(X|Z)=−∞)`、後者 (=`condEntExt=⊥`) は `hcond_ne_bot`
    が除外 → `h(X)=⊤` で整合 ✓。
  • `h_ext(X)=⊥` (h(X)=−∞、負部発散) 退化境界: LHS=`⊥` だが RHS=`condEntExt+(非負 klDiv)` は `hcond_ne_bot` 下で `⊥`
    にならない → 一見 FALSE だが、conditioning 単調 `h(X|Z)≤h(X)=−∞ ⟹ h(X|Z)=−∞ ⟹ condEntExt=⊥` で `hcond_ne_bot`
    が **この枝を正しく除外** ✓ (sufficiency は `hcond_ne_bot` に決定的依存、その scope は honest)。
  • `condEntExt=⊤` (h(X|Z)=+∞) + klDiv 有限: 非負 MI で `h(X)≥h(X|Z)=+∞ ⟹ h_ext(X)=⊤`、RHS=`⊤+I=⊤`=LHS ✓。
  8 integrability を全部落とせる機構は **EReal `∫⁻` 形 (常に well-defined・`⊤` 許容) が Bochner `∫` (integrability
  必須) を回避するため** = 正当な finiteness-free 化。under-hypothesized でない: `hX_ac`+`hcond_ne_bot` が反例枝を全閉。
classification `plan:` **妥当** (PASS): plan 実在 (`docs/shannon/epi-uncond-deffix-monotone-plan.md` §7-2/§7-6 が
道 A closure 所有)、機構 2 lemma の Real 版が genuine 既存 (`EPIG2ConvEntropyMonotone.lean:328` fibre 同定 / `:124`
chain rule bridge、共に `@audit:ok`)、残務 = それらの EReal 版 self-build = known-shape。`wall:` 過大評価でない:
finiteness-free KL chain rule `klDiv_compProd_eq_add` は Mathlib 存在 (無仮定、機械確認)、道 A は既存 Real 資産の
EReal lift で回避可。conclusion-shape 反証義務充足 (足掛かり部品 genuine 在庫)。

@residual(plan:epi-uncond-deffix-monotone-plan) -/
theorem differentialEntropyExt_eq_condEntExt_add_klDiv
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume)
    (hcond_ne_bot : condDifferentialEntropyExt X Z μ ≠ ⊥) :
    differentialEntropyExt (μ.map X)
      = condDifferentialEntropyExt X Z μ
        + (((InformationTheory.klDiv ((μ.map Z) ⊗ₘ condDistrib X Z μ)
              ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X))) : ℝ≥0∞) : EReal) := by
  sorry

end InformationTheory.Shannon
