import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# 拡張 entropyPower (二層定義 + coercion bridge)

EPI 無条件化 (moonshot S1) のための再型付け定義。退化トラップ
(特異測度 → 旧 `entropyPower = exp 0 = 1`) を、`EReal` 上位レイヤで
特異測度を `⊥` に落とすことで除去する。

- `differentialEntropyExt : Measure ℝ → EReal`: 特異で `⊥`、`μ ≪ volume`
  で **真の拡張微分エントロピー** (正部・負部の `EReal` 差) を返す。
  これにより `h = +∞` (裾の重い a.c. 密度) で `⊤`、`h = −∞` (背の高いピーク
  密度) で `⊥`、有限で workhorse `differentialEntropy` 値に一致する。
- `entropyPowerExt : Measure ℝ → ℝ≥0∞`: **非分岐** `EReal.exp (2 * differentialEntropyExt μ)`。
  `EReal.exp` が `exp ⊥ = 0` (特異 / `h = −∞`) / `exp ⊤ = ∞` (`h = +∞`) /
  `exp ↑x = ofReal (exp x)` (有限 a.c.) を 1 関数で吸収。

**⚠ 設計ノート (honesty-critical, `docs/shannon/epi-uncond-deffix-monotone-plan.md` §1)**:
a.c. 枝を `(differentialEntropy μ : EReal)` で coerce する旧定義は **infinite-entropy a.c. 入力で
FALSE-as-stated** だった (Bochner `differentialEntropy` は非可積分時 garbage `0` を返し、`h = ±∞` を
`entropyPowerExt = 1` に潰す → 無条件 EPI が偽)。正しい修正は「非可積分 → `⊤`」の素朴版**ではない**
(`h = −∞` のピーク密度を `∞` に飛ばし別の偽命題を作る)。符号判別必須 = **正部 `∫⁻ ofReal(negMulLog f)`
と負部 `∫⁻ ofReal(-(negMulLog f))` の `EReal` 差**で `+∞` / `−∞` / 有限を正しく出す。

SoT 計画: `docs/shannon/epi-unconditional-moonshot-plan.md` (傘) +
`docs/shannon/epi-uncond-deffix-monotone-plan.md` (def-fix campaign)。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

open Classical in
/-- 拡張微分エントロピー: 特異測度で `⊥`、`μ ≪ volume` で正部・負部の `EReal` 差。

a.c. 枝の値 `A − B`（`A := ∫⁻ ofReal(negMulLog f)`, `B := ∫⁻ ofReal(-(negMulLog f))`,
`f := density`）は `EReal` で評価する:
- `A, B` 有限（= `negMulLog∘f` 可積分）→ workhorse `differentialEntropy μ` に一致。
- `A = ⊤, B < ⊤`（正部発散 = 裾）→ `⊤`（`h = +∞`）。
- `A < ⊤, B = ⊤`（負部発散 = ピーク）→ `⊥`（`h = −∞`、`fin − ⊤ = ⊥`）。
- `A = ⊤, B = ⊤`（両発散、未定義）→ `⊥`（`⊤ − ⊤ = ⊥`、EPI に安全側）。

`klDiv` (Mathlib) を precedent に `open Classical in` + `irreducible_def` で a.c. 判定を
definitional 化する（`Decidable (μ ≪ volume)` 不在ゆえ classical instance を供給）。
@audit:ok -/
noncomputable irreducible_def differentialEntropyExt (μ : Measure ℝ) : EReal :=
  if μ ≪ volume then
    (((∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume : ℝ≥0∞) : EReal)
      - ((∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal)))
          ∂volume : ℝ≥0∞) : EReal))
  else ⊥

/-- 拡張エントロピーパワー (ℝ≥0∞): 特異 / `h=−∞` で `0`、`h=+∞` で `∞`、有限 a.c. で `ofReal (exp (2h))`。
`EReal.exp` が `exp ⊥ = 0` / `exp ⊤ = ∞` / `exp ↑x = ofReal (exp x)` を 1 関数で供給する非分岐定義。 -/
noncomputable def entropyPowerExt (μ : Measure ℝ) : ℝ≥0∞ :=
  EReal.exp (2 * differentialEntropyExt μ)

/-- a.c. 枝での `differentialEntropyExt` の raw value（正部・負部の `EReal` 差）。
@audit:ok -/
theorem differentialEntropyExt_of_ac {μ : Measure ℝ} (h : μ ≪ volume) :
    differentialEntropyExt μ
      = (((∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume : ℝ≥0∞)
            : EReal)
        - ((∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((μ.rnDeriv volume x).toReal)))
            ∂volume : ℝ≥0∞) : EReal)) := by
  rw [differentialEntropyExt]; exact if_pos h

/-- a.c. かつ `negMulLog∘density` 可積分（= 有限微分エントロピー）のとき、`differentialEntropyExt`
は workhorse `differentialEntropy` に一致。

正部・負部の `EReal` 差を `MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part`
（Bochner = `toReal A − toReal B`）+ `EReal.coe_sub` + `EReal.coe_ennreal_toReal` で workhorse に橋渡し。
正部/負部 lintegral 有限性は `Integrable.hasFiniteIntegral` + `ofReal(g) ≤ ‖g‖ₑ` の `lintegral_mono`。
@audit:ok -/
theorem differentialEntropyExt_of_ac_integrable {μ : Measure ℝ} (hac : μ ≪ volume)
    (hint : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropyExt μ = (differentialEntropy μ : EReal) := by
  rw [differentialEntropyExt_of_ac hac]
  set g : ℝ → ℝ := fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal) with hg
  have hbound : ∀ (f : ℝ → ℝ), Integrable f volume →
      (∫⁻ x, ENNReal.ofReal (f x) ∂volume) ≠ ⊤ := by
    intro f hf
    refine ne_top_of_le_ne_top hf.hasFiniteIntegral.ne (lintegral_mono fun x => ?_)
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hAfin : (∫⁻ x, ENNReal.ofReal (g x) ∂volume) ≠ ⊤ := hbound g hint
  have hBfin : (∫⁻ x, ENNReal.ofReal (-(g x)) ∂volume) ≠ ⊤ := hbound _ hint.neg
  have hwork : differentialEntropy μ
      = ENNReal.toReal (∫⁻ x, ENNReal.ofReal (g x) ∂volume)
        - ENNReal.toReal (∫⁻ x, ENNReal.ofReal (-(g x)) ∂volume) := by
    rw [differentialEntropy]
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint
  rw [hwork, EReal.coe_sub, EReal.coe_ennreal_toReal hAfin, EReal.coe_ennreal_toReal hBfin]

/-- 特異枝での `differentialEntropyExt` の値 (`⊥`)。
@audit:ok -/
theorem differentialEntropyExt_singular {μ : Measure ℝ} (h : ¬ μ ≪ volume) :
    differentialEntropyExt μ = ⊥ := by
  rw [differentialEntropyExt]
  exact if_neg h

/-- 有限 a.c. 枝での `entropyPowerExt` の値 (`ENNReal.ofReal (exp (2h))`)。
@audit:ok -/
theorem entropyPowerExt_of_ac_integrable {μ : Measure ℝ} (hac : μ ≪ volume)
    (hint : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    entropyPowerExt μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ)) := by
  unfold entropyPowerExt
  rw [differentialEntropyExt_of_ac_integrable hac hint,
    show (2 : EReal) = ((2 : ℝ) : EReal) by norm_cast, ← EReal.coe_mul,
    EReal.exp_coe]

/-- `differentialEntropyExt μ = ⊤` (`h = +∞`) のとき `entropyPowerExt μ = ⊤ = ∞`。
無限エントロピー a.c. 入力で EPI が `∞ ≥ ...` の `le_top` で閉じるための bridge。
@audit:ok -/
theorem entropyPowerExt_eq_top_of_diffEntExt_top {μ : Measure ℝ}
    (h : differentialEntropyExt μ = ⊤) : entropyPowerExt μ = ⊤ := by
  unfold entropyPowerExt
  rw [h, EReal.mul_top_of_pos (by norm_num), EReal.exp_top]

/-- 特異枝（および `h = −∞`）での `entropyPowerExt` の値 (`0`、退化トラップ除去)。
@audit:ok -/
theorem entropyPowerExt_singular {μ : Measure ℝ} (h : ¬ μ ≪ volume) :
    entropyPowerExt μ = 0 := by
  unfold entropyPowerExt
  rw [differentialEntropyExt_singular h, EReal.mul_bot_of_pos (by norm_num), EReal.exp_bot]

/-- **退化トラップ除去の verbatim 検証**: Dirac 測度のエントロピーパワーは `0`。
旧 Real `entropyPower (dirac m) = exp 0 = 1` (誤) → 新 `entropyPowerExt (dirac m) = 0` (正)。
@audit:ok -/
theorem entropyPowerExt_dirac (m : ℝ) : entropyPowerExt (Measure.dirac m) = 0 := by
  apply entropyPowerExt_singular
  intro h_ac
  have h_sing : Measure.dirac m ⟂ₘ (volume : Measure ℝ) := mutuallySingular_dirac m volume
  have h_zero : (Measure.dirac m : Measure ℝ) = 0 :=
    Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h_ac h_sing
  exact (NeZero.ne' (Measure.dirac m)).symm h_zero

/-- Gaussian 密度の `negMulLog` は volume 可積分（有限微分エントロピー）。
`negMulLog(gaussianPDF) =ᵐ gaussianPDF·c₁ + gaussianPDF·(x-m)²/(2v)`、前者は密度可積分、
後者は Gaussian 2 次モーメント有限（`memLp_id_gaussianReal`）から。sanity gate `_gaussianReal` 用。
@audit:ok -/
theorem integrable_negMulLog_gaussianReal_density (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => Real.negMulLog ((gaussianReal m v).rnDeriv volume x).toReal) volume := by
  -- pointwise: negMulLog(pdf) = pdf · (c₁ + (x-m)²/(2v))  (a.e. via density identification)
  have h_ae : (fun x => Real.negMulLog ((gaussianReal m v).rnDeriv volume x).toReal)
      =ᵐ[volume] (fun x => gaussianPDFReal m v x * ((1/2) * Real.log (2 * Real.pi * v))
        + gaussianPDFReal m v x * ((x - m)^2 / (2 * v))) := by
    filter_upwards [rnDeriv_gaussianReal m v] with x hx
    rw [hx, toReal_gaussianPDF]
    unfold Real.negMulLog
    rw [log_gaussianPDFReal_eq m hv x]
    ring
  rw [integrable_congr h_ae]
  -- term 1: pdf · const
  have h_pdf : Integrable (gaussianPDFReal m v) volume := integrable_gaussianPDFReal m v
  have h_t1 : Integrable
      (fun x => gaussianPDFReal m v x * ((1/2) * Real.log (2 * Real.pi * v))) volume :=
    h_pdf.mul_const _
  -- term 2: pdf · (x-m)²/(2v).  `pdf · (x-m)²` integrable against volume = `(x-m)²` integrable
  -- against `gaussianReal = volume.withDensity (ofReal ∘ pdf)`.
  have h2mom : Integrable (fun x => (x - m)^2) (gaussianReal m v) := by
    have h_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal m v) :=
      (memLp_id_gaussianReal (μ := m) (v := v) 2).integrable_sq
    have h_id : Integrable (fun y : ℝ => y) (gaussianReal m v) := by
      simpa using (memLp_id_gaussianReal (μ := m) (v := v) 1).integrable (by norm_num)
    have h_eq : (fun y : ℝ => (y - m) ^ 2) = fun y => y ^ 2 - 2 * m * y + m ^ 2 := by
      funext y; ring
    rw [h_eq]
    exact ((h_sq.sub (h_id.const_mul (2 * m))).add (integrable_const (m ^ 2)))
  have hgvol : gaussianReal m v
      = volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal m v x)) :=
    gaussianReal_of_var_ne_zero m hv
  rw [hgvol, integrable_withDensity_iff (by measurability)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)] at h2mom
  have h_t2 : Integrable (fun x => gaussianPDFReal m v x * ((x - m)^2 / (2 * v))) volume := by
    have hc := (h2mom.const_mul (1 / (2 * (v : ℝ))))
    refine hc.congr (Filter.Eventually.of_forall fun x => ?_)
    show 1 / (2 * (v : ℝ)) * ((x - m) ^ 2 * (ENNReal.ofReal (gaussianPDFReal m v x)).toReal)
        = gaussianPDFReal m v x * ((x - m) ^ 2 / (2 * v))
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg m v x)]
    ring
  exact h_t1.add h_t2

/-- **a.c. 非自明値 ≠ 0 の sanity gate**: Gaussian (`v ≠ 0`、a.c.) のエントロピーパワーは
`2πe·v` で `0` に潰れない (a.c. 判定が常時 false に転ぶ退化定義悪用の検出)。
@audit:ok -/
theorem entropyPowerExt_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    entropyPowerExt (gaussianReal m v)
      = ENNReal.ofReal (2 * Real.pi * Real.exp 1 * (v : ℝ)) := by
  have h_ac : gaussianReal m v ≪ volume := gaussianReal_absolutelyContinuous m hv
  rw [entropyPowerExt_of_ac_integrable h_ac (integrable_negMulLog_gaussianReal_density m hv)]
  congr 1
  rw [differentialEntropy_gaussianReal m hv]
  rw [show (2 : ℝ) * ((1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)))
        = Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) by ring]
  rw [Real.exp_log]
  positivity

end InformationTheory.Shannon
