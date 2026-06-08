import InformationTheory.Shannon.EntropyPower.Ext
import InformationTheory.Shannon.EPI.G2.ConvEntropyMonotone
import InformationTheory.Shannon.CondKLIntegral
import InformationTheory.Shannon.EPI.G2.BridgeDensityHelpers
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

/-- **EReal balance 補題** (crux ② finite 版 assemble の closure step)。
ℝ≥0∞ 5 項 balance `a1 + b2 = a2 + k + b1` (b1, b2 有限) から、EReal の差分形
`(a1:E) - (b1:E) = ((a2:E) - (b2:E)) + (k:E)` を得る。

機構: b1, b2 を `EReal.coe_ennreal_toReal` で Real-coe `↑b1.toReal` / `↑b2.toReal` 化して
finite subtrahend にし、`EReal.sub_add_cancel` / `EReal.add_sub_cancel_right` で両辺を
`(a1:E) + (b2:E) = ((a2:E) + (k:E)) + (b1:E)` の cancel 形に持ち込み、`EReal.coe_ennreal_add`
で coe をまとめ `EReal.coe_ennreal_eq_coe_ennreal_iff` で ℝ≥0∞ 等式 `hbal` に還元する。
a1 / a2 / k が `⊤` でも b1, b2 finite なので cancellation は通る (casework 不要)。

独立 honesty audit 2026-06-08 (4-check, PASS): (1) 非循環 — 結論 (EReal 差分等式) は仮説
`hbal` (ℝ≥0∞ レベル等式) と型が異なり非同型、body は `coe_ennreal_toReal`/`coe_ennreal_add`/
`add_sub_cancel_right` の純 EReal 算術、`:= h` でない。(2) 非バンドル — core-reconstruction:
`hbal` を grant しても結論は手に入らない、EReal の finite-subtrahend cancellation (b1,b2 有限を
使う `EReal.sub_top` 回避) + coe 移送は body が担う、`hbal` は「ℝ≥0∞ で先に示すべき自明部分」の
分離で load-bearing でない (呼出元 finite ② が `hbal` を step a'/b'/c' 結線で genuine に供給)。
(3) 非退化 — `:True` slot なし、a1/a2/k が ⊤ でも通る casework-free 設計。(4) sufficiency —
b1,b2 有限が cancellation に honest に必要 (⊤ subtrahend だと `(a1:E)-⊤=⊥` で LHS 潰れ FALSE)、
`hb1`/`hb2` がこの枝を除外、含意は EReal AddCommMonoid で semantic に follow (反例棄却済)。
sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`、機械確認)。
@audit:ok -/
theorem ereal_sub_eq_sub_add_of_ennreal_balance
    (a1 b1 a2 b2 k : ℝ≥0∞) (hb1 : b1 ≠ ∞) (hb2 : b2 ≠ ∞)
    (hbal : a1 + b2 = a2 + k + b1) :
    ((a1 : EReal) - (b1 : EReal)) = (((a2 : EReal) - (b2 : EReal)) + (k : EReal)) := by
  -- b1, b2 finite: rewrite their EReal-coe as the Real-coe of `.toReal` (finite subtrahends).
  rw [← EReal.coe_ennreal_toReal hb1, ← EReal.coe_ennreal_toReal hb2]
  -- It suffices to prove the cancel form `(a1:E) + ↑b2.toReal = ((a2:E) + (k:E)) + ↑b1.toReal`,
  -- because adding ↑b1.toReal then subtracting ↑b2.toReal recovers the goal (finite cancels).
  have key : (a1 : EReal) + (b2.toReal : EReal) = (((a2 : EReal) + (k : EReal)) + (b1.toReal : EReal)) := by
    -- Reduce to the ℝ≥0∞ balance via `coe_ennreal_add`.
    rw [EReal.coe_ennreal_toReal hb1, EReal.coe_ennreal_toReal hb2,
      ← EReal.coe_ennreal_add, ← EReal.coe_ennreal_add, ← EReal.coe_ennreal_add,
      EReal.coe_ennreal_eq_coe_ennreal_iff]
    -- Goal: `a1 + b2 = a2 + k + b1` (= hbal).
    exact hbal
  -- From `key`, isolate `↑a1` by subtracting the finite `↑b2.toReal` (cancellation, b2 finite).
  have ha1 : (a1 : EReal) = (((a2 : EReal) + (k : EReal)) + (b1.toReal : EReal)) - (b2.toReal : EReal) := by
    rw [← key, EReal.add_sub_cancel_right]
  -- Now compute the goal `↑a1 - ↑b1.toReal = (↑a2 - ↑b2.toReal) + ↑k`.
  rw [ha1]
  -- Goal: `↑a2 + ↑k + ↑b1.toReal - ↑b2.toReal - ↑b1.toReal = (↑a2 - ↑b2.toReal) + ↑k`.
  -- All `± ↑(·.toReal)` summands are finite; convert to `+(-·)` form and reorganise in
  -- the AddCommMonoid `EReal`, then cancel `↑b1.toReal + (-↑b1.toReal)`.
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
  -- Goal: `↑a2 + ↑k + ↑b1.toReal + (-↑b2.toReal) + (-↑b1.toReal) = ↑a2 + (-↑b2.toReal) + ↑k`.
  -- Bring `↑b1.toReal` and `-↑b1.toReal` adjacent and cancel.
  rw [add_right_comm (((a2 : EReal) + (k : EReal)) + (b1.toReal : EReal)) (-(b2.toReal : EReal))
        (-(b1.toReal : EReal)),
    add_assoc ((a2 : EReal) + (k : EReal)) (b1.toReal : EReal) (-(b1.toReal : EReal)),
    ← EReal.coe_neg, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero,
    add_right_comm (a2 : EReal) (k : EReal) (-(b2.toReal : EReal))]

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

⚠ 2026-06-08 更新: finiteness-free 版は (☆) per-fibre 恒等式の mass 相殺依存により本ルートでは証明
不能と確定 (`ℝ≥0∞` に減算が無く step b' が fibre 有限性必須)。genuine な finite-entropy 版は
`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite` (`:262`、`@audit:ok`、独立監査 2026-06-08
PASS、step a'/b'/c' + EReal balance helper 結線、sorryAx-free)。本無条件版の residual は truncation+LSC
route β' (有限エントロピー近似の極限) で別途攻略。下記旧 sufficiency 解析 (2026-06-07) は循環論法を
含み (枝閉じ `I=∞⟹h(X)=⊤` / conditioning 単調 `h(X|Z)≤h(X)` が ② = chain rule 自身に依存) stale =
参考情報。`@residual(plan:...)` 分類は statement が真 (proof が hard) で無条件版が route β' で生きるため
維持。

旧 honesty audit 2026-06-07 (crux ②、stale 注記済、参考情報): **honest_residual** (tier 2)。4-check:
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

/-- **(②-finite) EReal chain rule, fibre-finiteness 版** (genuine、finite ② headline)。
`h_ext(X) = h_ext(X | Z) + I(X;Z)` を **per-fibre 有限性 regularity** を取って genuine に建てる。

finiteness-free 版 (`differentialEntropyExt_eq_condEntExt_add_klDiv`、`:191`、sorry) は per-fibre
恒等式が mass 相殺に依存し、`ℝ≥0∞` に減算が無いため **証明不能と確定済**。本版は各 fibre `condDistrib X Z μ z`
の有限性 (a.c. / 可積分 / KL 有限) を仮説に取り、step a' (`klDiv_compProd_lintegral`) / step b'
(`klDiv_negMulLog_cross_balance_ennreal`) / step c' (`lintegral_condDistrib_cross_eq`、いずれも
`@audit:ok`) を結線して closure する。

全 11 仮説は regularity precondition (可測性 / 絶対連続性 / 可積分性 / KL 有限性 / ⊥ 除外) であり
load-bearing でない: 結論 RHS の核 (klDiv 項 = I(X;Z)) を仮説に encode していない。`hκ_KL`
(`klDiv (κz) ν ≠ ∞` a.e. z) は `hκ_ac` + `hκ_logp_int` + `hκ_cross_int` + (κz ≪ ν、`h_ac` 由来) から
導出可能だが、step b' の `hKL` precondition を per-fibre で供給するための tractability 用に明示で取る
(**redundant regularity、非 load-bearing**; 導出可能性が結論の核ではない)。`hcond_ne_bot` / `hX_ne_bot`
は ⊥ 退化枝 (h(X|Z) = −∞ / h(X) = −∞) を honest に除外する scope (`⊥ + klDiv = ⊥` で恒等式が崩れる枝)。

独立 honesty audit 2026-06-08 (4-check, PASS — genuine 完成、tier 1): (1) 非循環 — 結論
(entropy 分解恒等式 `h_ext(X) = condEntExt + I(X;Z)`) は 11 仮説 (Measurable/≪/Integrable/≠∞/≠⊥)
のいずれとも非同型、body (`:284-410`) は step a'/b'/c' + helper の genuine 配線 (hfib→hk_eq→
hCpos_eq/hCneg_eq→hbal→hb1_ne/hb2_ne→`ereal_sub_eq_sub_add_of_ennreal_balance`)、`:= h` でない。
(2) 非バンドル (各仮説 core-reconstruction test) — 全 11 仮説が regularity precondition:
hX/hZ (可測)、hX_ac/h_ac/hκ_ac (絶対連続)、hκ_dens_meas (joint 密度可測)、hκ_logp_int/hκ_cross_int
(fibre 可積分)、hκ_KL (fibre KL ≠ ∞)、hcond_ne_bot/hX_ne_bot (⊥ 除外)。**hκ_KL 弁明検証**: body
`:328-330` で step b' (`klDiv_negMulLog_cross_balance_ennreal`、`@audit:ok`) の `hKL` 引数として
per-fibre 供給、step b' 内で klDiv-term の有限性 (`add_ne_top`/`toReal_add` side-condition) にのみ
使われ恒等式の核 (`klDiv.toReal=−h(P)−cross`) は step b' in-body Real sibling が担う ⟹ hκ_KL は
klDiv-term finiteness の regularity で結論の klDiv 項を encode しない、redundant (他 3 仮説 + κz≪ν
から導出可能) だが redundant regularity は defect でなく「導出可能なのに核を仮説化」でない (核は body)。
**klDiv 項 = 結論 RHS の一部** (I(X;Z)、measure-level `InformationTheory.klDiv`) だが仮説に不等式核を
抱えず、`hbal` 内で step a' (`klDiv_compProd_lintegral`) により `∫⁻ fibre KL` に genuine 展開 (`:332`/
`:391`)、core-reconstruction 不発火。(3) 非退化 — `:True` slot なし、V≡0(Dirac Z): condDistrib=μ.map X・
joint=product・klDiv=0 → `h(X)=h(X)+0` ✓。(4) sufficiency — finiteness-free 版 (現②) が per-fibre
mass 相殺で証明不能なのに本版が genuine なのは fibre 有限性 (hκ_ac/hκ_logp_int/hκ_cross_int/hκ_KL) を
**honest に補強したから** = 「選択 big を blocked と偽る」の逆、honest regularity 補強。反例枝全閉:
b1=∞(h(X)=−∞)→hX_ne_bot 除外、b2=∞(h(X|Z)=−∞)→hcond_ne_bot 除外、fibre KL=∞→hκ_KL 除外。
under-hypothesized でない。classification: `@residual` なし (sorryAx-free `[propext, Classical.choice,
Quot.sound]` 機械確認)、step a'/b'/c'/helper の全 `@audit:ok` 配線と整合 ⟹ `@audit:ok` 付与妥当。
@audit:ok -/
theorem differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace.CountableOrCountablyGenerated α ℝ]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume)
    (h_ac : (μ.map Z) ⊗ₘ condDistrib X Z μ ≪ (μ.map Z) ⊗ₘ Kernel.const α (μ.map X))
    (hκ_dens_meas : Measurable
      (fun p : α × ℝ => ((condDistrib X Z μ p.1).rnDeriv volume p.2)))
    (hκ_ac : ∀ᵐ z ∂(μ.map Z), condDistrib X Z μ z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((condDistrib X Z μ z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map X).rnDeriv volume x).toReal)) volume)
    (hκ_KL : ∀ᵐ z ∂(μ.map Z), klDiv (condDistrib X Z μ z) (μ.map X) ≠ ∞)
    (hcond_ne_bot : condDifferentialEntropyExt X Z μ ≠ ⊥)
    (hX_ne_bot : differentialEntropyExt (μ.map X) ≠ ⊥) :
    differentialEntropyExt (μ.map X)
      = condDifferentialEntropyExt X Z μ
        + (((InformationTheory.klDiv ((μ.map Z) ⊗ₘ condDistrib X Z μ)
              ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X))) : ℝ≥0∞) : EReal) := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  -- abbreviations
  set μZ := μ.map Z with hμZ
  set ν := μ.map X with hν
  set κ := condDistrib X Z μ with hκ
  -- positive / negative part lintegrals of the marginal `ν = μ.map X`
  set a1 : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (Real.negMulLog ((ν.rnDeriv volume x).toReal)) ∂volume with ha1
  set b1 : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((ν.rnDeriv volume x).toReal))) ∂volume with hb1
  -- conditional positive / negative part lintegrals
  set a2 : ℝ≥0∞ :=
    ∫⁻ z, (∫⁻ x, ENNReal.ofReal (Real.negMulLog (((κ z).rnDeriv volume x).toReal)) ∂volume) ∂μZ
    with ha2
  set b2 : ℝ≥0∞ :=
    ∫⁻ z, (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((κ z).rnDeriv volume x).toReal))) ∂volume) ∂μZ
    with hb2
  -- joint KL
  set k : ℝ≥0∞ := InformationTheory.klDiv (μZ ⊗ₘ κ) (μZ ⊗ₘ Kernel.const α ν) with hk
  -- z-measurability of the four fibre lintegrals
  -- z-measurability of the four fibre lintegrals (via `lintegral_prod_right'` on the joint
  -- density measurability `hκ_dens_meas`).
  have hpz_toReal : Measurable
      (fun p : α × ℝ => (((κ p.1).rnDeriv volume p.2).toReal)) := hκ_dens_meas.ennreal_toReal
  have hAz_meas : Measurable
      (fun z => ∫⁻ x, ENNReal.ofReal (Real.negMulLog (((κ z).rnDeriv volume x).toReal)) ∂volume) :=
    (((Real.continuous_negMulLog.measurable.comp hpz_toReal)).ennreal_ofReal).lintegral_prod_right'
  have hBz_meas : Measurable
      (fun z => ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((κ z).rnDeriv volume x).toReal))) ∂volume) :=
    ((((Real.continuous_negMulLog.measurable.comp hpz_toReal)).neg).ennreal_ofReal).lintegral_prod_right'
  -- per-fibre balance (step b'), a.e. z
  have hfib : ∀ᵐ z ∂μZ,
      (∫⁻ x, ENNReal.ofReal (Real.negMulLog (((κ z).rnDeriv volume x).toReal)) ∂volume)
        + InformationTheory.klDiv (κ z) ν
        + (∫⁻ x, ENNReal.ofReal (((κ z).rnDeriv volume x).toReal
              * Real.log ((ν.rnDeriv volume x).toReal)) ∂volume)
      = (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((κ z).rnDeriv volume x).toReal))) ∂volume)
        + (∫⁻ x, ENNReal.ofReal (-(((κ z).rnDeriv volume x).toReal
              * Real.log ((ν.rnDeriv volume x).toReal))) ∂volume) := by
    -- per-fibre absolute continuity `κ z ≪ ν` from the joint a.c. `h_ac`.
    have hκν : ∀ᵐ z ∂μZ, κ z ≪ ν := by
      filter_upwards [Measure.absolutelyContinuous_compProd_right_iff.mp h_ac] with z hz
      simpa only [Kernel.const_apply] using hz
    filter_upwards [hκ_ac, hκν, hκ_logp_int, hκ_cross_int, hκ_KL]
      with z hzv hzν hzlogp hzcross hzKL
    exact klDiv_negMulLog_cross_balance_ennreal (κ z) ν hzv hX_ac hzν hzlogp hzcross hzKL
  -- joint KL = ∫⁻ fibre KL (step a')
  have hk_eq : k = ∫⁻ z, InformationTheory.klDiv (κ z) ν ∂μZ := by
    rw [hk, klDiv_compProd_lintegral h_ac]
    refine lintegral_congr fun z => ?_
    rw [Kernel.const_apply]
  -- cross-term marginal collapse (step c', positive part: Cpos integrates to b1)
  have hCpos_eq :
      (∫⁻ z, (∫⁻ x, ENNReal.ofReal (((κ z).rnDeriv volume x).toReal
            * Real.log ((ν.rnDeriv volume x).toReal)) ∂volume) ∂μZ) = b1 := by
    -- step c' with `sign := id` (positive part), then fold `qν·log qν = -(negMulLog qν)`.
    rw [lintegral_condDistrib_cross_eq X Z μ hX hZ hX_ac hκ_ac (fun r => r) measurable_id
          (fun a b => rfl), hb1]
    refine lintegral_congr fun x => ?_
    congr 1
    rw [Real.negMulLog_eq_neg]; ring
  -- cross-term marginal collapse (step c', negative part: Cneg integrates to a1)
  have hCneg_eq :
      (∫⁻ z, (∫⁻ x, ENNReal.ofReal (-(((κ z).rnDeriv volume x).toReal
            * Real.log ((ν.rnDeriv volume x).toReal))) ∂volume) ∂μZ) = a1 := by
    -- step c' with `sign := Neg.neg` (negative part), then fold `-(qν·log qν) = negMulLog qν`.
    rw [lintegral_condDistrib_cross_eq X Z μ hX hZ hX_ac hκ_ac (fun r => -r) measurable_neg
          (fun a b => by ring), ha1]
    refine lintegral_congr fun x => ?_
    congr 1
    rw [Real.negMulLog_eq_neg]
  -- z-measurability of the cross positive part `Cpos_z` (needed for the LHS split below).
  have hCpos_z_meas : Measurable
      (fun z => ∫⁻ x, ENNReal.ofReal (((κ z).rnDeriv volume x).toReal
          * Real.log ((ν.rnDeriv volume x).toReal)) ∂volume) := by
    have hcross_meas : Measurable
        (fun p : α × ℝ => ((κ p.1).rnDeriv volume p.2).toReal
            * Real.log ((ν.rnDeriv volume p.2).toReal)) :=
      hpz_toReal.mul ((Real.measurable_log.comp
        (Measure.measurable_rnDeriv ν volume).ennreal_toReal).comp measurable_snd)
    exact hcross_meas.ennreal_ofReal.lintegral_prod_right'
  -- (★) ℝ≥0∞ balance `a1 + b2 = a2 + k + b1`
  have hbal : a1 + b2 = a2 + k + b1 := by
    -- Integrate the per-fibre balance `hfib` over `μZ`.
    have hint_eq :
        (∫⁻ z, ((∫⁻ x, ENNReal.ofReal (Real.negMulLog (((κ z).rnDeriv volume x).toReal)) ∂volume)
            + InformationTheory.klDiv (κ z) ν
            + (∫⁻ x, ENNReal.ofReal (((κ z).rnDeriv volume x).toReal
                  * Real.log ((ν.rnDeriv volume x).toReal)) ∂volume)) ∂μZ)
          = ∫⁻ z, ((∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((κ z).rnDeriv volume x).toReal))) ∂volume)
              + (∫⁻ x, ENNReal.ofReal (-(((κ z).rnDeriv volume x).toReal
                    * Real.log ((ν.rnDeriv volume x).toReal))) ∂volume)) ∂μZ :=
      lintegral_congr_ae hfib
    -- LHS: regroup `A_z + KL_z + Cpos_z = (A_z + Cpos_z) + KL_z`, then split twice
    -- (KL_z stays on the arbitrary side, so its measurability is not needed).
    rw [lintegral_congr (g := fun z =>
          ((∫⁻ x, ENNReal.ofReal (Real.negMulLog (((κ z).rnDeriv volume x).toReal)) ∂volume)
            + (∫⁻ x, ENNReal.ofReal (((κ z).rnDeriv volume x).toReal
                  * Real.log ((ν.rnDeriv volume x).toReal)) ∂volume))
            + InformationTheory.klDiv (κ z) ν)
          (fun z => by rw [add_right_comm]),
        lintegral_add_left (hAz_meas.add hCpos_z_meas),
        lintegral_add_left hAz_meas,
        lintegral_add_left hBz_meas] at hint_eq
    -- Identify each piece: `∫⁻ Cpos_z = b1`, `∫⁻ Cneg_z = a1`, `∫⁻ KL_z = k`,
    -- and fold `∫⁻ A_z = a2`, `∫⁻ B_z = b2` (post-`rw` terms not auto-folded by `set`).
    rw [hCpos_eq, hCneg_eq, ← hk_eq, ← ha2, ← hb2] at hint_eq
    -- `hint_eq : a2 + b1 + k = b2 + a1`. Reassemble to the balance form (ℝ≥0∞ CommMonoid).
    rw [add_right_comm a2 k b1, hint_eq, add_comm b2 a1]
  -- b1, b2 ≠ ∞ from the ⊥-exclusion hypotheses (h(X) ≠ −∞, h(X|Z) ≠ −∞).
  -- If `b1 = ∞`, then `(a1:E) - ⊤ = ⊥`, contradicting `differentialEntropyExt ν ≠ ⊥`.
  have hb1_ne : b1 ≠ ∞ := by
    intro h
    rw [differentialEntropyExt_of_ac hX_ac, ← ha1, ← hb1, h,
      EReal.coe_ennreal_eq_top_iff.mpr rfl, EReal.sub_top] at hX_ne_bot
    exact hX_ne_bot rfl
  -- If `b2 = ∞`, then `(a2:E) - ⊤ = ⊥`, contradicting `condDifferentialEntropyExt ≠ ⊥`.
  have hb2_ne : b2 ≠ ∞ := by
    intro h
    rw [condDifferentialEntropyExt, ← ha2, ← hb2, h,
      EReal.coe_ennreal_eq_top_iff.mpr rfl, EReal.sub_top] at hcond_ne_bot
    exact hcond_ne_bot rfl
  -- unfold both differential entropies into positive/negative part EReal differences
  rw [differentialEntropyExt_of_ac hX_ac, condDifferentialEntropyExt]
  -- close via the EReal balance helper
  exact ereal_sub_eq_sub_add_of_ennreal_balance a1 b1 a2 b2 k hb1_ne hb2_ne hbal

end InformationTheory.Shannon
