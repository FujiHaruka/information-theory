import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# 拡張 entropyPower (二層定義 + coercion bridge)

EPI 無条件化 (moonshot S1) のための再型付け定義。退化トラップ
(特異測度 → 旧 `entropyPower = exp 0 = 1`) を、`EReal` 上位レイヤで
特異測度を `⊥` に落とすことで除去する。

- `differentialEntropyExt : Measure ℝ → EReal`: 特異で `⊥`、`μ ≪ volume`
  で Real workhorse `differentialEntropy` を coerce。case-split はこの層に一元化。
- `entropyPowerExt : Measure ℝ → ℝ≥0∞`: **非分岐** `EReal.exp (2 * differentialEntropyExt μ)`。
  `EReal.exp` が `exp ⊥ = 0` (特異 → 0) / `exp ↑x = ofReal (exp x)` (a.c.) を 1 関数で吸収。

SoT 計画: `docs/shannon/epi-entropypower-retype-plan.md`。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

open Classical in
/-- 拡張微分エントロピー: 特異測度で `⊥`、`μ ≪ volume` で Real workhorse を coerce。

`klDiv` (Mathlib `InformationTheory/KullbackLeibler/Basic.lean`) を precedent に
`open Classical in` + `irreducible_def` で a.c. 判定を definitional 化する
(`Decidable (μ ≪ volume)` は Mathlib 不在なので classical instance を供給、
downstream の意図しない unfold は展開 lemma 経由で防ぐ)。 -/
noncomputable irreducible_def differentialEntropyExt (μ : Measure ℝ) : EReal :=
  if μ ≪ volume then (differentialEntropy μ : EReal) else ⊥

/-- 拡張エントロピーパワー (ℝ≥0∞): 特異で `0`、a.c. で `ofReal (exp (2h))`。
`EReal.exp` が `exp ⊥ = 0` / `exp ↑x = ofReal (exp x)` を 1 関数で供給する非分岐定義。 -/
noncomputable def entropyPowerExt (μ : Measure ℝ) : ℝ≥0∞ :=
  EReal.exp (2 * differentialEntropyExt μ)

/-- a.c. 枝での `differentialEntropyExt` の値 (Real workhorse の coercion)。 -/
theorem differentialEntropyExt_of_ac {μ : Measure ℝ} (h : μ ≪ volume) :
    differentialEntropyExt μ = (differentialEntropy μ : EReal) := by
  rw [differentialEntropyExt]
  exact if_pos h

/-- 特異枝での `differentialEntropyExt` の値 (`⊥`)。 -/
theorem differentialEntropyExt_singular {μ : Measure ℝ} (h : ¬ μ ≪ volume) :
    differentialEntropyExt μ = ⊥ := by
  rw [differentialEntropyExt]
  exact if_neg h

/-- a.c. 枝での `entropyPowerExt` の値 (`ENNReal.ofReal (exp (2h))`)。 -/
theorem entropyPowerExt_of_ac {μ : Measure ℝ} (h : μ ≪ volume) :
    entropyPowerExt μ = ENNReal.ofReal (Real.exp (2 * differentialEntropy μ)) := by
  unfold entropyPowerExt
  rw [differentialEntropyExt_of_ac h,
    show (2 : EReal) = ((2 : ℝ) : EReal) by norm_cast, ← EReal.coe_mul,
    EReal.exp_coe]

/-- 特異枝での `entropyPowerExt` の値 (`0`、退化トラップ除去)。 -/
theorem entropyPowerExt_singular {μ : Measure ℝ} (h : ¬ μ ≪ volume) :
    entropyPowerExt μ = 0 := by
  unfold entropyPowerExt
  rw [differentialEntropyExt_singular h, EReal.mul_bot_of_pos (by norm_num), EReal.exp_bot]

/-- **退化トラップ除去の verbatim 検証**: Dirac 測度のエントロピーパワーは `0`。
旧 Real `entropyPower (dirac m) = exp 0 = 1` (誤) → 新 `entropyPowerExt (dirac m) = 0` (正)。 -/
theorem entropyPowerExt_dirac (m : ℝ) : entropyPowerExt (Measure.dirac m) = 0 := by
  apply entropyPowerExt_singular
  intro h_ac
  have h_sing : Measure.dirac m ⟂ₘ (volume : Measure ℝ) := mutuallySingular_dirac m volume
  have h_zero : (Measure.dirac m : Measure ℝ) = 0 :=
    Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h_ac h_sing
  exact (NeZero.ne' (Measure.dirac m)).symm h_zero

/-- **a.c. 非自明値 ≠ 0 の sanity gate**: Gaussian (`v ≠ 0`、a.c.) のエントロピーパワーは
`2πe·v` で `0` に潰れない (a.c. 判定が常時 false に転ぶ退化定義悪用の検出)。 -/
theorem entropyPowerExt_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    entropyPowerExt (gaussianReal m v)
      = ENNReal.ofReal (2 * Real.pi * Real.exp 1 * (v : ℝ)) := by
  have h_ac : gaussianReal m v ≪ volume := gaussianReal_absolutelyContinuous m hv
  rw [entropyPowerExt_of_ac h_ac]
  congr 1
  rw [differentialEntropy_gaussianReal m hv]
  rw [show (2 : ℝ) * ((1 / 2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)))
        = Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) by ring]
  rw [Real.exp_log]
  positivity

end InformationTheory.Shannon
