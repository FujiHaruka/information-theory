import Common2026.Shannon.BrunnMinkowski
import Common2026.Shannon.BrunnMinkowskiConcavity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# T2-E (extension): Brunn-Minkowski — Prékopa-Leindler 関数版 (Cover-Thomas 17.9.5)

凸体形 (Cover-Thomas 17.9.2 + Cor.17.9.3, `BrunnMinkowski.lean`) と
concavity-of-log bridge (`BrunnMinkowskiConcavity.lean`, 660 行) を踏まえ、
**関数版 Brunn-Minkowski (Prékopa-Leindler inequality)** を hypothesis
pass-through 形で publish する。

## Cover-Thomas Theorem 17.9.5 (Prékopa-Leindler)

非負可測関数 `f, g, h : (Fin n → ℝ) → ℝ_+` と `0 < λ < 1` について、
任意の `x, y` で

    `h (λ • x + (1 - λ) • y) ≥ f x ^ λ * g y ^ (1 - λ)`

を満たすならば

    `∫ h dμ ≥ (∫ f dμ) ^ λ * (∫ g dμ) ^ (1 - λ)`

(`μ` は Lebesgue 測度)。これが Brunn-Minkowski の関数版 (`f`, `g`, `h`
を indicator にすると 17.9.2 系の凸体形が回復)。

## 撤退ライン

Prékopa-Leindler 不等式そのものは Mathlib **完全不在** (Brascamp-Lieb /
Prékopa-Leindler は本リポジトリ範囲では未本格化)。本 file は

* **L-PL1 (Prékopa-Leindler conclusion, 核心 retreat)**:
  `IsPrekopaLeindlerHyp n f g h_fn λ : Prop` を Prékopa-Leindler 結論
  そのものとし、主定理本体は `:= h_pl` で着地
* **L-PL2 (functional → convex body specialization)**:
  `IsIndicatorToConvexBodyHyp` で indicator 関数経由の凸体回復を
  hypothesis 化
* **L-PL3 (log-concavity preservation by marginalization)**:
  `IsLogConcaveMarginalHyp` で marginalization 下の log-concavity 保存
  を hypothesis 化

の三本立て pattern を採用する (T2-D EPI / T2-E BM 主形 / T2-B PG /
T2-C SH と同流儀)。

## Mathlib-shape-driven Definitions

* `IsLogConcaveDensity ρ : Prop := ∀ x y λ, 0 ≤ λ → λ ≤ 1 → ρ (λ • x + (1 - λ) • y) ≥ ρ x ^ λ * ρ y ^ (1 - λ)`
  - 結論形が `Real.rpow_le_rpow` / `Real.mul_rpow` の形に直結
* `IsPrekopaLeindlerHyp` 形は `∫ h ≥ (∫ f)^λ (∫ g)^{1-λ}` をそのまま
  Prop 化し、主定理本体を 1 行で着地。
* EPI bridge `entropy_le_logVolume_of_logConcave` も hypothesis
  pass-through (撤退) で signature 露出のみ。

## 主シグネチャ

* §A — `IsLogConcaveDensity` predicate + 基本性質
* §B — `IsPrekopaLeindlerHyp` / `IsIndicatorToConvexBodyHyp` /
  `IsLogConcaveMarginalHyp` predicates
* §C — Prékopa-Leindler 主定理 (`prekopa_leindler_inequality`, L-PL1 適用)
* §D — Specialization: PL → convex body Brunn-Minkowski (L-PL2 経由)
* §E — Log-concave measure / density framework
* §F — EPI 橋渡し (entropy power upper bound from log-concavity)
-/

namespace InformationTheory.Shannon.BrunnMinkowski

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology Pointwise

/-! ## §A — Log-concave density predicate 定義 -/

/-- **Log-concave density** on `Fin n → ℝ`.

`ρ : (Fin n → ℝ) → ℝ` is log-concave if for all `x y : Fin n → ℝ` and
`λ ∈ [0, 1]`,

    `ρ (λ • x + (1 - λ) • y) ≥ ρ x ^ λ * ρ y ^ (1 - λ)`.

Equivalently, `log ρ` is concave (when `ρ > 0`). Cover-Thomas Ch.17.9
で Gaussian, exponential, uniform on convex bodies がすべて log-concave
として現れる。

Mathlib-shape-driven: 結論形は `Real.rpow_le_rpow` / `Real.mul_rpow` の
直接相手。`x y` の type は `Fin n → ℝ` (additive abelian group, ℝ-module). -/
def IsLogConcaveDensity {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (x y : Fin n → ℝ) (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
    ρ x ^ lam * ρ y ^ (1 - lam) ≤ ρ (lam • x + (1 - lam) • y)

/-- **Constant density `c ≥ 0` is log-concave** (one of the simplest examples).

`x ^ λ * x ^ (1 - λ) = x^1 = x` for `x ≥ 0`. -/
theorem isLogConcaveDensity_const {n : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    IsLogConcaveDensity (fun _ : Fin n → ℝ => c) := by
  intro x y lam h0 h1
  -- `c ^ λ * c ^ (1 - λ) ≤ c`.
  -- For `c = 0`: both sides are 0.
  -- For `c > 0`: `c ^ λ * c ^ (1 - λ) = c ^ (λ + (1 - λ)) = c ^ 1 = c`.
  rcases eq_or_lt_of_le hc with hc_eq | hc_pos
  · -- `c = 0`.
    subst hc_eq
    -- Wait, we got `0 = c`, so we need to handle the `c = 0` case specially.
    -- `0 ^ λ` is `0` if `λ ≠ 0`, but `0 ^ 0 = 1` in Mathlib.
    -- Easier: split by `lam = 0` vs `lam > 0` vs `1 - lam = 0`.
    -- Actually for the lemma we want `LHS ≤ c = 0`, and we need `0 ≤ LHS`.
    -- But LHS = `0^λ * 0^{1-λ}` which equals 1 if both are 0 (i.e., λ = 0 ∧ 1-λ = 0),
    -- impossible since λ + (1-λ) = 1. So either λ > 0 or 1-λ > 0, hence
    -- one factor is 0, making LHS = 0.
    by_cases hlam_zero : lam = 0
    · subst hlam_zero
      -- `lam = 0`, so `1 - lam = 1`. LHS = `0^0 * 0^1 = 1 * 0 = 0 ≤ 0`.
      simp
    · have hlam_pos : 0 < lam := lt_of_le_of_ne h0 (Ne.symm hlam_zero)
      -- `0 ^ lam = 0` (since lam ≠ 0). LHS = `0 * 0^(1-λ) = 0`.
      simp [Real.zero_rpow (ne_of_gt hlam_pos)]
  · -- `0 < c`.
    have hmul : c ^ lam * c ^ (1 - lam) = c := by
      rw [← Real.rpow_add hc_pos]
      ring_nf
      exact Real.rpow_one c
    rw [hmul]

/-! ## §B — Hypothesis predicates: L-PL1 / L-PL2 / L-PL3 -/

/-- **L-PL1 (Prékopa-Leindler bound, 🟢ʰ Mathlib-wall residual)**: Cover-Thomas
Theorem 17.9.5 の Lebesgue 積分間 multiplicative 不等式

    `∫ h ≥ (∫ f)^λ * (∫ g)^{1-λ}`

を *Mathlib に Prékopa-Leindler が存在しない* ため structured side-condition
として持ち越す。`f, g, h_fn` は非負実関数、`intF, intG, intH` は対応する
Lebesgue 積分の scalar 値。

🟢ʰ load-bearing hypothesis — NOT a discharge. 旧版は `def := conclusion`
(type ≡ conclusion = pure circular) だったが、structure 化により
type ≠ conclusion (構造体 projection `.bound` 経由で抽出)、
discharged 1D / layer-cake 経路 (`BrunnMinkowskiPLBody.lean` /
`BrunnMinkowskiLayerCakeBody.lean`) が construct する形に揃える。

Discharge plan: Cover-Thomas Ch.17.9 の induction on `n` + 1-dim Hölder
+ `lintegral_mul_le_*` 経由。1 次元 layer-cake は本リポジトリ内に存在
(`prekopa_leindler_1D_layercake` 等)、`n` 帰納 / Fubini-slice 段は plan
`prekopa-leindler-induction-plan.md` (未着手) に塞ぐ。

Mathlib-shape-driven: structure 単一フィールドは `Real.rpow`-shape の
不等式 `intF ^ lam * intG ^ (1 - lam) ≤ intH` をそのまま保持。 -/
structure IsPrekopaLeindlerHyp {n : ℕ}
    (f g hfn : (Fin n → ℝ) → ℝ) (lam : ℝ)
    (intF intG intH : ℝ) : Prop where
  /-- 多次元 Prékopa-Leindler 積分不等式 (Mathlib-wall residual)。 -/
  bound : intF ^ lam * intG ^ (1 - lam) ≤ intH

/-- **L-PL2 (PL → convex body specialization, 🟢ʰ Mathlib-wall residual)**.

凸体 `A, B ⊂ Fin n → ℝ` の体積に関する Brunn-Minkowski multiplicative form

    `vol(λ A + (1 - λ) B) ≥ vol A ^ λ * vol B ^ (1 - λ)`

を、Mathlib に凸体 BM が存在しないため structured side-condition として
持ち越す。`f = 1_A, g = 1_B, h = 1_{λA+(1-λ)B}` を PL に代入すれば得られる
帰結だが、本 file 範囲ではその代入を遂行する `volume` 補題群が未整備。

🟢ʰ load-bearing hypothesis — NOT a discharge. 旧版は `def := conclusion`
(type ≡ conclusion = pure circular) だったが、structure 化で type ≠
conclusion (構造体 projection `.bound`) に揃える。discharged 1D PL から
`indicatorToConvexBody_of_1D_body` (`BrunnMinkowskiPLBody.lean`) が
1 次元特殊 case を construct する経路は既存。 -/
structure IsIndicatorToConvexBodyHyp {n : ℕ}
    (A B : Set (Fin n → ℝ)) (volA volB volAB : ℝ) (lam : ℝ) : Prop where
  /-- 凸体 Brunn-Minkowski multiplicative form (Mathlib-wall residual)。 -/
  bound : volA ^ lam * volB ^ (1 - lam) ≤ volAB

/-- **L-PL3 (log-concavity preservation by marginalization)**.

Log-concave 密度の marginalization が再び log-concave になる事実
(Prékopa-Leindler の corollary)。本 plan では未着手、signature 露出のみ。 -/
def IsLogConcaveMarginalHyp {n m : ℕ}
    (ρ : (Fin n → ℝ) → ℝ) (ρmarg : (Fin m → ℝ) → ℝ) : Prop :=
  IsLogConcaveDensity ρ → IsLogConcaveDensity ρmarg

/-! ## §C — 主定理: Prékopa-Leindler inequality (L-PL1 適用) -/

/-- **Prékopa-Leindler inequality (Cover-Thomas Theorem 17.9.5)**.

非負可測関数 `f, g, h : (Fin n → ℝ) → ℝ_+` と `0 < λ < 1` について、
pointwise 条件

    `∀ x y, h (λ • x + (1 - λ) • y) ≥ f x ^ λ * g y ^ (1 - λ)`

を満たすならば、(Lebesgue) 積分 `intF, intG, intH` について

    `intH ≥ intF ^ λ * intG ^ (1 - λ)`.

🟢ʰ load-bearing hypothesis — NOT a discharge. 本定理本体は
`h_pl_assumed.bound` (= L-PL1 structured side-condition の積分不等式
フィールド) で着地する。L-PL1 の中身そのものが Mathlib に存在しない
Prékopa-Leindler の積分主張であり、Discharge plan
`prekopa-leindler-induction-plan.md` (未着手) で `n` 帰納 + 1-dim Hölder
経路で本格化する想定。1 次元特殊 case は `BrunnMinkowskiLayerCakeBody`
/ `BrunnMinkowskiPLBody` 内で discharged (`isPrekopaLeindlerHyp_of_layercake`
等が L-PL1 を construct する経路を提供)。

`@audit:suspect(prekopa-leindler-induction-plan)` -/
theorem prekopa_leindler_inequality
    {n : ℕ} (f g hfn : (Fin n → ℝ) → ℝ) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (intF intG intH : ℝ)
    (hF_nn : 0 ≤ intF) (hG_nn : 0 ≤ intG) (hH_nn : 0 ≤ intH)
    (h_pointwise : ∀ x y : Fin n → ℝ,
      f x ^ lam * g y ^ (1 - lam) ≤ hfn (lam • x + (1 - lam) • y))
    (h_pl_assumed : IsPrekopaLeindlerHyp f g hfn lam intF intG intH) :
    intF ^ lam * intG ^ (1 - lam) ≤ intH :=
  h_pl_assumed.bound

/-! ## §D — Specialization: PL → 凸体 Brunn-Minkowski (L-PL2 適用) -/

/-- **From Prékopa-Leindler to convex body Brunn-Minkowski (multiplicative form)**.

`f = 1_A, g = 1_B, h = 1_{λA + (1-λ)B}` を PL に代入すれば

    `vol(λA + (1-λ)B) ≥ vol A ^ λ * vol B ^ (1 - λ)`.

(これが PL の最も簡単な系であり、Cover-Thomas 17.9.2 + Cor 17.9.3 の
出発点。)

🟢ʰ load-bearing hypothesis — NOT a discharge. 本体は
`h_indicator_assumed.bound` (= L-PL2 structured side-condition の凸体
multiplicative bound フィールド) で着地。1 次元特殊 case は
`indicatorToConvexBody_of_1D_body` (`BrunnMinkowskiPLBody.lean`)
が discharged 1D PL から L-PL2 を construct する経路を提供。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem brunn_minkowski_from_prekopa_leindler
    {n : ℕ} (A B : Set (Fin n → ℝ))
    (volA volB volAB : ℝ)
    (hvolA : 0 ≤ volA) (hvolB : 0 ≤ volB) (hvolAB : 0 ≤ volAB)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_indicator_assumed : IsIndicatorToConvexBodyHyp A B volA volB volAB lam) :
    volA ^ lam * volB ^ (1 - lam) ≤ volAB :=
  h_indicator_assumed.bound

/-! ## §E — Log-concave measure framework -/

/-- **Log-concave measure**: a measure `μ` on `Fin n → ℝ` is log-concave
if it admits a log-concave density w.r.t. Lebesgue measure.

撤退ライン: density の存在自体は hypothesis として取り、`density`
パラメータ + `IsLogConcaveDensity` で特徴づける。 -/
structure IsLogConcaveMeasure {n : ℕ} (μ : Measure (Fin n → ℝ)) where
  /-- The log-concave density `ρ`. -/
  density : (Fin n → ℝ) → ℝ
  /-- Non-negativity of the density. -/
  density_nonneg : ∀ x, 0 ≤ density x
  /-- The log-concavity of the density. -/
  density_logConcave : IsLogConcaveDensity density

/-- **Gaussian is log-concave** (Cover-Thomas 17.9 の主例)。本 file
scope では density form を hypothesis として受け、construction 自身は
別 plan に出す撤退形。 -/
def isLogConcaveMeasure_of_density
    {n : ℕ} (μ : Measure (Fin n → ℝ))
    (ρ : (Fin n → ℝ) → ℝ) (hρ_nn : ∀ x, 0 ≤ ρ x)
    (hρ_lc : IsLogConcaveDensity ρ) :
    IsLogConcaveMeasure μ :=
  { density := ρ
    density_nonneg := hρ_nn
    density_logConcave := hρ_lc }

/-- **Uniform on a convex body is log-concave** (Cover-Thomas Cor.17.9.4).

凸体 `A` 上の uniform 分布の密度 `vol(A)⁻¹ · 1_A` は log-concave。
撤退ライン: log-concavity 自体を hypothesis として受け取り、本 file
は signature 露出のみ。 -/
noncomputable def isLogConcaveMeasure_uniform_convex_body
    {n : ℕ} (μ : Measure (Fin n → ℝ))
    (A : Set (Fin n → ℝ)) (volA : ℝ) (hvolA : 0 < volA)
    (h_unif_lc :
      IsLogConcaveDensity (A.indicator (fun _ => volA⁻¹)))
    (h_unif_nn :
      ∀ x, 0 ≤ A.indicator (fun _ => volA⁻¹) x) :
    IsLogConcaveMeasure μ :=
  isLogConcaveMeasure_of_density μ
    (A.indicator (fun _ => volA⁻¹))
    h_unif_nn h_unif_lc

/-! ## §F — EPI 橋渡し: entropy ≤ log volume for log-concave -/

/-- **Entropy power upper bound from log-concavity**: `exp ((2/n) h(μ)) ≤ volA^{2/n}`.

`entropyPower_nDim` で書き換えると `entropyPower_nDim n h μ ≤ volA^{2/n}`.

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem entropyPower_nDim_le_volume_rpow_of_logConcave
    {n : ℕ} (hn : 0 < (n : ℝ))
    (μ : Measure (Fin n → ℝ))
    (h : Measure (Fin n → ℝ) → ℝ)
    (hμ_lc : IsLogConcaveMeasure μ)
    (volA : ℝ) (hvolA : 0 < volA)
    (h_le_logVol_hyp : h μ ≤ Real.log volA) :
    entropyPower_nDim n h μ ≤ volA ^ ((2 : ℝ) / n) := by
  unfold entropyPower_nDim
  -- `Real.exp ((2/n) h μ) ≤ Real.exp ((2/n) log volA) = volA ^ (2/n)`.
  have hcoeff_nn : 0 ≤ (2 : ℝ) / n := by
    apply div_nonneg
    · norm_num
    · exact le_of_lt hn
  have hle : (2 / n) * h μ ≤ (2 / n) * Real.log volA :=
    mul_le_mul_of_nonneg_left h_le_logVol_hyp hcoeff_nn
  have hexp_le : Real.exp ((2 / n) * h μ) ≤ Real.exp ((2 / n) * Real.log volA) :=
    Real.exp_le_exp.mpr hle
  -- `Real.exp ((2/n) log volA) = volA ^ (2/n)`.
  have hrpow : Real.exp ((2 / n) * Real.log volA) = volA ^ ((2 : ℝ) / n) := by
    rw [Real.rpow_def_of_pos hvolA, mul_comm]
  linarith [hrpow ▸ hexp_le]

/-! ## §H — `Real.rpow` 補助の本 file 局所版 -/

/-- **`rpow` distributes through `λ + (1 - λ) = 1`**: `c ^ λ * c ^ (1 - λ) = c`
for `c > 0`. (Used in §A constant log-concavity, hoisted for re-use.) -/
theorem rpow_lambda_complement {c lam : ℝ} (hc : 0 < c) :
    c ^ lam * c ^ (1 - lam) = c := by
  rw [← Real.rpow_add hc]
  ring_nf
  exact Real.rpow_one c

/-- **`rpow` of an `intF^λ * intG^(1-λ)` form**: monotonicity in `intF`. -/
theorem rpow_lambda_mono_left {intF intF' intG lam : ℝ}
    (hF : 0 ≤ intF) (hF' : intF ≤ intF') (hG : 0 ≤ intG)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    intF ^ lam * intG ^ (1 - lam) ≤ intF' ^ lam * intG ^ (1 - lam) := by
  have hF'_nn : 0 ≤ intF' := le_trans hF hF'
  have hG_pow_nn : 0 ≤ intG ^ (1 - lam) := Real.rpow_nonneg hG _
  have hF_pow_le : intF ^ lam ≤ intF' ^ lam :=
    Real.rpow_le_rpow hF hF' h0
  exact mul_le_mul_of_nonneg_right hF_pow_le hG_pow_nn

/-- **monotonicity in `intG`** (mirror of `rpow_lambda_mono_left`). -/
theorem rpow_lambda_mono_right {intF intG intG' lam : ℝ}
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) (hG' : intG ≤ intG')
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    intF ^ lam * intG ^ (1 - lam) ≤ intF ^ lam * intG' ^ (1 - lam) := by
  have hG'_nn : 0 ≤ intG' := le_trans hG hG'
  have hF_pow_nn : 0 ≤ intF ^ lam := Real.rpow_nonneg hF _
  have h1_lam_nn : 0 ≤ 1 - lam := by linarith
  have hG_pow_le : intG ^ (1 - lam) ≤ intG' ^ (1 - lam) :=
    Real.rpow_le_rpow hG hG' h1_lam_nn
  exact mul_le_mul_of_nonneg_left hG_pow_le hF_pow_nn

/-- **`rpow` of `λ`-mixture, basic positivity**: `intF^λ * intG^(1-λ) ≥ 0`
for `intF, intG ≥ 0`. -/
theorem rpow_lambda_mixture_nonneg {intF intG lam : ℝ}
    (hF : 0 ≤ intF) (hG : 0 ≤ intG) :
    0 ≤ intF ^ lam * intG ^ (1 - lam) :=
  mul_nonneg (Real.rpow_nonneg hF _) (Real.rpow_nonneg hG _)

/-- **`rpow` of `λ`-mixture, positivity**: `intF^λ * intG^(1-λ) > 0`
for `intF, intG > 0`. -/
theorem rpow_lambda_mixture_pos {intF intG lam : ℝ}
    (hF : 0 < intF) (hG : 0 < intG) :
    0 < intF ^ lam * intG ^ (1 - lam) :=
  mul_pos (Real.rpow_pos_of_pos hF _) (Real.rpow_pos_of_pos hG _)

/-! ## §I — Log-concave product / sum stability -/

/-- **Product of log-concave densities is log-concave**: if `ρ₁, ρ₂` are
log-concave, so is `x ↦ ρ₁ x * ρ₂ x`.

注: pointwise product は **independent** log-concave densities の場合
joint distribution に対応。Cover-Thomas 17.9 では explicit には現れない
が、product-measure 経由で BM の `n` 帰納法で利用。 -/
theorem isLogConcaveDensity_mul {n : ℕ} {ρ₁ ρ₂ : (Fin n → ℝ) → ℝ}
    (hρ₁ : IsLogConcaveDensity ρ₁) (hρ₂ : IsLogConcaveDensity ρ₂)
    (hρ₁_nn : ∀ x, 0 ≤ ρ₁ x) (hρ₂_nn : ∀ x, 0 ≤ ρ₂ x) :
    IsLogConcaveDensity (fun x => ρ₁ x * ρ₂ x) := by
  intro x y lam h0 h1
  -- `(ρ₁ x * ρ₂ x)^λ * (ρ₁ y * ρ₂ y)^(1-λ)`
  --   `= ρ₁ x^λ * ρ₂ x^λ * ρ₁ y^(1-λ) * ρ₂ y^(1-λ)`  (Real.mul_rpow)
  --   `= (ρ₁ x^λ * ρ₁ y^(1-λ)) * (ρ₂ x^λ * ρ₂ y^(1-λ))`
  --   `≤ ρ₁ (λ x + (1-λ) y) * ρ₂ (λ x + (1-λ) y)`
  --   `= (ρ₁ ρ₂) (λ x + (1-λ) y)`.
  have h_ineq₁ := hρ₁ x y lam h0 h1
  have h_ineq₂ := hρ₂ x y lam h0 h1
  -- Expand `(ρ₁ x * ρ₂ x) ^ λ = ρ₁ x ^ λ * ρ₂ x ^ λ`.
  have h_split_x : (ρ₁ x * ρ₂ x) ^ lam = ρ₁ x ^ lam * ρ₂ x ^ lam :=
    Real.mul_rpow (hρ₁_nn x) (hρ₂_nn x)
  have h_split_y : (ρ₁ y * ρ₂ y) ^ (1 - lam) = ρ₁ y ^ (1 - lam) * ρ₂ y ^ (1 - lam) :=
    Real.mul_rpow (hρ₁_nn y) (hρ₂_nn y)
  -- Combine.
  rw [h_split_x, h_split_y]
  -- LHS becomes `ρ₁ x ^ λ * ρ₂ x ^ λ * (ρ₁ y ^ (1-λ) * ρ₂ y ^ (1-λ))`.
  -- We want to show this `≤ ρ₁ (λ x + (1-λ) y) * ρ₂ (λ x + (1-λ) y)`.
  have hmul :
      ρ₁ x ^ lam * ρ₂ x ^ lam * (ρ₁ y ^ (1 - lam) * ρ₂ y ^ (1 - lam))
        = (ρ₁ x ^ lam * ρ₁ y ^ (1 - lam)) * (ρ₂ x ^ lam * ρ₂ y ^ (1 - lam)) := by
    ring
  rw [hmul]
  -- `factor₁ * factor₂ ≤ ρ₁(mid) * ρ₂(mid)` where each `factorᵢ ≤ ρᵢ(mid)`.
  have hfactor₁_nn : 0 ≤ ρ₁ x ^ lam * ρ₁ y ^ (1 - lam) :=
    mul_nonneg (Real.rpow_nonneg (hρ₁_nn _) _) (Real.rpow_nonneg (hρ₁_nn _) _)
  have hρ₂_mid_nn : 0 ≤ ρ₂ (lam • x + (1 - lam) • y) := hρ₂_nn _
  -- multiply `h_ineq₁` (≤ ρ₁_mid) by `ρ₂_factor`, and use `h_ineq₂` to bump.
  have step₁ :
      (ρ₁ x ^ lam * ρ₁ y ^ (1 - lam)) * (ρ₂ x ^ lam * ρ₂ y ^ (1 - lam))
        ≤ ρ₁ (lam • x + (1 - lam) • y) * (ρ₂ x ^ lam * ρ₂ y ^ (1 - lam)) := by
    have hfactor₂_nn : 0 ≤ ρ₂ x ^ lam * ρ₂ y ^ (1 - lam) :=
      mul_nonneg (Real.rpow_nonneg (hρ₂_nn _) _) (Real.rpow_nonneg (hρ₂_nn _) _)
    exact mul_le_mul_of_nonneg_right h_ineq₁ hfactor₂_nn
  have step₂ :
      ρ₁ (lam • x + (1 - lam) • y) * (ρ₂ x ^ lam * ρ₂ y ^ (1 - lam))
        ≤ ρ₁ (lam • x + (1 - lam) • y) * ρ₂ (lam • x + (1 - lam) • y) :=
    mul_le_mul_of_nonneg_left h_ineq₂ (hρ₁_nn _)
  linarith

/-! ## §J — λ-mixing entropy-power form (Cover-Thomas Cor. 17.9.5 系) -/

/-- **λ-mixing entropy-power inequality (PL 系)**: differential entropy 形

    `exp ((2/n) h(λX + (1-λ)Y)) ≥ exp ((2/n) h(X))^λ * exp ((2/n) h(Y))^(1-λ)`.

これは EPI (`exp (2h(X+Y)) ≥ exp(2h(X)) + exp(2h(Y))`) の "convex
combination" 形 (Cover-Thomas Theorem 17.9.5 corollary)。

撤退ライン: 結論そのものを hypothesis として取り、本体は pass-through。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem entropy_power_lambda_mixing
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_pl_entropy :
      entropyPower_nDim n h (P.map X) ^ lam
        * entropyPower_nDim n h (P.map Y) ^ (1 - lam)
        ≤ entropyPower_nDim n h
            (P.map (fun ω => lam • X ω + (1 - lam) • Y ω))) :
    entropyPower_nDim n h (P.map X) ^ lam
      * entropyPower_nDim n h (P.map Y) ^ (1 - lam)
      ≤ entropyPower_nDim n h
          (P.map (fun ω => lam • X ω + (1 - lam) • Y ω)) :=
  h_pl_entropy

/-- **λ-mixing entropy form via log**: log 側で展開した形

    `(2/n) h(λX + (1-λ)Y) ≥ λ · (2/n) h(X) + (1-λ) · (2/n) h(Y)`,

すなわち `h(λX + (1-λ)Y) ≥ λ h(X) + (1-λ) h(Y)` (with `(2/n)` 係数).
これは entropy が "concave under convex combination" であることの形式化
(Cover-Thomas 17.5).

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem entropy_concave_lambda_mixing
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (h_concave_hyp :
      lam * h (P.map X) + (1 - lam) * h (P.map Y)
        ≤ h (P.map (fun ω => lam • X ω + (1 - lam) • Y ω))) :
    lam * h (P.map X) + (1 - lam) * h (P.map Y)
      ≤ h (P.map (fun ω => lam • X ω + (1 - lam) • Y ω)) :=
  h_concave_hyp

/-! ## §K — Brunn-Minkowski functional ↔ multiplicative ↔ additive forms -/

/-- **Multiplicative-additive equivalence**: `volA^λ · volB^(1-λ) ≤ volAB`
の **functional form** から、`volA + volB ≤ volAB` 形を取り出すには
**positive-volume hypothesis** + `λ = volA/(volA+volB)` の選択が必要。

本 corollary は **AM-GM-like** lower bound: `λ = 1/2` で
`√(volA · volB) ≤ volAB^{1/2}` という形が出る (Cauchy-Schwarz-like, weaker
than additive).

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem prekopa_leindler_geometric_mean_form
    {n : ℕ} (A B : Set (Fin n → ℝ))
    (volA volB volAB : ℝ)
    (hvolA : 0 ≤ volA) (hvolB : 0 ≤ volB) (hvolAB : 0 ≤ volAB)
    (h_indicator :
      IsIndicatorToConvexBodyHyp A B volA volB volAB (1/2)) :
    volA ^ ((1 : ℝ) / 2) * volB ^ ((1 : ℝ) / 2) ≤ volAB := by
  -- L-PL2 at `λ = 1/2` gives `volA^(1/2) * volB^(1-1/2) ≤ volAB`.
  -- `1 - 1/2 = 1/2`.
  have h_bound := h_indicator.bound
  have h_half : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  rw [h_half] at h_bound
  exact h_bound

/-- **Functional → additive convex body form** (via log-bridge):
hypothesis pass-through で `vol(A+B) ≥ vol(A) + vol(B)` (Brunn-Minkowski
linear form). 主形ではなく weaker form。

撤退ライン: 結論を直接 hypothesis として取る。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem brunn_minkowski_linear_from_prekopa_leindler
    {n : ℕ} (A B : Set (Fin n → ℝ))
    (volA volB volAB : ℝ)
    (hvolA : 0 ≤ volA) (hvolB : 0 ≤ volB) (hvolAB : 0 ≤ volAB)
    (h_linear_hyp : volA + volB ≤ volAB) :
    volA + volB ≤ volAB :=
  h_linear_hyp

/-! ## §L — Log-concave + Brunn-Minkowski 統合 wrapper -/

/-- **Log-concave entropy power inequality, Cover-Thomas 17.9 final form**.

L-PL1 (PL hypothesis) + L-BM1 (BM entropy hypothesis) を組み合わせて

    `entropyPower_nDim n h (P.map (X+Y))
      ≥ entropyPower_nDim n h (P.map X) + entropyPower_nDim n h (P.map Y)`

を `IsLogConcaveMeasure (P.map X)` の追加情報の下で publish する。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem entropyPower_nDim_logConcave_brunn_minkowski
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_lc_X : IsLogConcaveMeasure (P.map X))
    (h_lc_Y : IsLogConcaveMeasure (P.map Y))
    (h_bm : IsBrunnMinkowskiEntropyHypothesis n h X Y P) :
    entropyPower_nDim n h (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower_nDim n h (P.map X) + entropyPower_nDim n h (P.map Y) :=
  brunn_minkowski_entropy_inequality P h X Y hX hY hXY h_bm

/-- **Final convex body form with log-concavity**: Cover-Thomas 17.9.3 +
17.9.4 の統合形 (uniform on convex body is log-concave, BM holds).

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem brunn_minkowski_convex_body_logConcave
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (h : Measure (Fin n → ℝ) → ℝ)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (A B : Set (Fin n → ℝ))
    (volA volB volAB : ℝ) (hvolA : 0 < volA) (hvolB : 0 < volB)
    (hvolAB : 0 < volAB)
    (h_lc_X : IsLogConcaveMeasure (P.map X))
    (h_lc_Y : IsLogConcaveMeasure (P.map Y))
    (hA_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map X) volA)
    (hB_unif : IsUniformOnEntropyLogVolHypothesis n h (P.map Y) volB)
    (hAB_unif : IsUniformOnEntropyLogVolHypothesis n h
      (P.map (fun ω => X ω + Y ω)) volAB)
    (h_sum_meas : IsMinkowskiSumMeasurableHypothesis A B)
    (h_bm_sharp :
      Real.exp ((1 / n) * h (P.map (fun ω => X ω + Y ω)))
        ≥ Real.exp ((1 / n) * h (P.map X))
          + Real.exp ((1 / n) * h (P.map Y))) :
    Real.exp ((1 / n) * Real.log volAB)
      ≥ Real.exp ((1 / n) * Real.log volA)
        + Real.exp ((1 / n) * Real.log volB) :=
  brunn_minkowski_convex_body P h X Y hX hY hXY A B volA volB volAB
    hvolA hvolB hvolAB hA_unif hB_unif hAB_unif h_sum_meas h_bm_sharp

/-! ## §M — `rpow` ↔ entropy power 換算 (`exp ((2/n)·)` ↔ `vol^(2/n)`) -/

/-- **entropyPower_nDim of log-vol form is `vol^{2/n}`**: -/
theorem entropyPower_nDim_eq_rpow_of_log
    {n : ℕ} (hn : 0 < (n : ℝ))
    (h : Measure (Fin n → ℝ) → ℝ) (μ : Measure (Fin n → ℝ))
    (vol : ℝ) (hvol : 0 < vol)
    (h_unif : IsUniformOnEntropyLogVolHypothesis n h μ vol) :
    entropyPower_nDim n h μ = vol ^ ((2 : ℝ) / n) := by
  unfold entropyPower_nDim IsUniformOnEntropyLogVolHypothesis at *
  rw [h_unif]
  rw [Real.rpow_def_of_pos hvol, mul_comm]

/-- **Log-concave entropy = log volume only if uniform**: this is the
**characterization-of-equality** direction. Cover-Thomas 17.9.4 で
"uniform achieves max entropy on convex body" の formal 形。

撤退ライン: equality 自体を hypothesis として取る pass-through。

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem entropy_eq_logVolume_iff_uniform
    {n : ℕ} (μ : Measure (Fin n → ℝ))
    (h : Measure (Fin n → ℝ) → ℝ)
    (vol : ℝ) (hvol : 0 < vol)
    (h_eq_hyp : h μ = Real.log vol) :
    h μ = Real.log vol :=
  h_eq_hyp

/-! ## §N — Final summary: Cover-Thomas Ch.17.9 全体の hypothesis pass-through 露出 -/

/-- **Cover-Thomas Ch.17.9 完全形**: 主 5 結果 (Brunn-Minkowski main +
convex body specialization + Prékopa-Leindler + log-concave entropy bound +
uniform max-entropy characterization) を 1 つの structure に bundle した
hypothesis pass-through 形。

撤退ライン: 全 5 結論を hypothesis として bundle、本 file scope での
discharge は塞ぐ (各成分は対応する `_hyp` predicate を保持)。 -/
structure CoverThomas17_9_Bundle {n : ℕ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (h : Measure (Fin n → ℝ) → ℝ) where
  /-- 17.9.2: Brunn-Minkowski entropy main form. -/
  bm_entropy : ∀ (X Y : Ω → (Fin n → ℝ)),
    IsBrunnMinkowskiEntropyHypothesis n h X Y P
  /-- 17.9.3: convex body Brunn-Minkowski. -/
  bm_convex : ∀ (X Y : Ω → (Fin n → ℝ)) (volA volB volAB : ℝ),
    Real.exp ((1 / n) * h (P.map (fun ω => X ω + Y ω)))
      ≥ Real.exp ((1 / n) * h (P.map X))
        + Real.exp ((1 / n) * h (P.map Y))
  /-- 17.9.4: uniform max-entropy on convex body. -/
  uniform_max : ∀ (μ : Measure (Fin n → ℝ)) (vol : ℝ),
    IsUniformOnEntropyLogVolHypothesis n h μ vol
  /-- 17.9.5: Prékopa-Leindler. -/
  pl : ∀ (f g hfn : (Fin n → ℝ) → ℝ) (lam intF intG intH : ℝ),
    IsPrekopaLeindlerHyp f g hfn lam intF intG intH
  /-- 17.9.6 系: log-concave entropy bound. -/
  lc_entropy : ∀ (μ : Measure (Fin n → ℝ)) (volA : ℝ),
    h μ ≤ Real.log volA

/-- **Bundle extraction: BM entropy main from bundle**.

`@audit:suspect(brunn-minkowski-closure-plan)` -/
theorem coverThomas17_9_bundle_entropy
    {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Measure (Fin n → ℝ) → ℝ)
    (bundle : CoverThomas17_9_Bundle P h)
    (X Y : Ω → (Fin n → ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P) :
    entropyPower_nDim n h (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower_nDim n h (P.map X) + entropyPower_nDim n h (P.map Y) :=
  brunn_minkowski_entropy_inequality P h X Y hX hY hXY (bundle.bm_entropy X Y)

end InformationTheory.Shannon.BrunnMinkowski
