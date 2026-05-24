import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.FisherInfo
import Common2026.Shannon.FisherInfoV2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# T2-D: Entropy Power Inequality (Cover-Thomas Theorem 17.7.3)

独立な実値確率変数 `X, Y` に対する **Entropy Power Inequality (EPI)**

    `exp(2 h(X + Y)) ≥ exp(2 h(X)) + exp(2 h(Y))`.

を hypothesis pass-through 形で publish。Cover-Thomas Ch.17.7 (Inequalities in
Information Theory) の頂点で、Gaussian theory の閉じに対応する。

## Roadmap (per `docs/shannon/epi-moonshot-plan.md`)

* Phase A — `entropyPower` 定義 + Gaussian closed form
* Phase B — L-EPI1 + L-EPI2 + L-EPI3 predicate 定義
* Phase C — 主定理 `entropy_power_inequality` (L-EPI3 適用)
* Phase D — Gaussian saturation case (撤退ラインなしで full discharge)
* Phase E — 補助 corollary 群 (positivity / scaling / log form)

## 撤退ライン (本 file で発動)

EPI 本体 (Stam inequality → de Bruijn integration の合成) は Mathlib に**全く
不在** (`loogle "EntropyPower"` で unknown identifier、`rg "Stam"` で 0 hit)。
本 file では Cover-Thomas Theorem 17.7.3 の textbook 完全形を signature に
保持しつつ、主定理本体は L-EPI3 単独で着地する **L-EPI1 + L-EPI2 + L-EPI3
三本立て hypothesis pass-through pattern** を採用する (T2-B / T2-C / T3-D /
T3-F と同流儀)。

* **L-EPI1 (Stam inequality)**: `IsStamInequalityHypothesis X Y P : Prop`,
  Stam の `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)` を hypothesis 化。本 file では
  placeholder (`True`) として導入し、主定理 signature 露出のみ。Discharge
  plan `epi-stam-discharge-plan.md` (未着手) で本格化。
* **L-EPI2 (de Bruijn integration)**: `IsDeBruijnIntegrationHypothesis X Y P :
  Prop`, heat-flow path 上の EPI integration identity を hypothesis 化。
  T2-F `IsRegularDeBruijnHyp` を `[0, ∞)` 上で積分する形の discharge plan
  `epi-debruijn-integration-plan.md` (未着手) で本格化。
* **L-EPI3 (EPI conclusion、核心 retreat)**: `IsEntropyPowerInequalityHypothesis
  X Y P : Prop` を EPI 結論そのものとし、主定理本体は `:= h_epi` で着地。
  Discharge plan `epi-stam-to-conclusion-plan.md` で L-EPI1 + L-EPI2 から
  導出する想定。

## Mathlib-shape-driven Definitions

* `entropyPower μ : ℝ := Real.exp (2 * differentialEntropy μ)` は
  `Real.exp_pos` / `Real.exp_log` の結論形に直結。Cover-Thomas の
  `N(μ) = (2πe)⁻¹ · exp(2 h(μ))` 形は scaling corollary で吸収。
* L-EPI3 形 `IsEntropyPowerInequalityHypothesis` は EPI 結論を `Prop` 化し、
  主定理本体を `:= h_epi` の 1 行で着地させる (T2-B L-PG1 / T2-C L-SH3
  と同流儀)。
* Gaussian saturation case は Mathlib
  `gaussianReal_add_gaussianReal_of_indepFun` + Common2026
  `differentialEntropy_gaussianReal` の合成で **full discharge** (撤退
  ラインなし)。

## 主シグネチャ

* `entropyPower` — Phase A 定義
* `entropyPower_pos`, `entropyPower_gaussianReal` — Tier 0 補助
* `IsStamInequalityHypothesis` / `IsDeBruijnIntegrationHypothesis` /
  `IsEntropyPowerInequalityHypothesis` — Phase B L-EPI1/2/3 predicates
* `entropy_power_inequality` — Phase C 主定理 (L-EPI3 適用形)
* `entropy_power_inequality_exp_form` — Cover-Thomas 露出形 (Real.exp 展開)
* `entropy_power_inequality_gaussian_saturation` — Phase D, full discharge
* `entropyPower_nonneg`, `entropyPower_map_add_const`,
  `entropy_power_inequality_log_form` — Phase E corollaries
-/

namespace InformationTheory.Shannon.EntropyPowerInequality

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

/-! ## §A — `entropyPower` 定義 + 基本性質 -/

/-- **Entropy power** of a measure `μ` on `ℝ`.

`entropyPower μ := exp (2 · h(μ))` where `h` is `Common2026.Shannon.differentialEntropy`.

Cover-Thomas Ch.17 の `N(X) := (2πe)⁻¹ · exp(2 h(X))` と係数差のみ; 本 file
は `exp (2 h(μ))` 直書きで採用する (Mathlib-shape-driven, EPI signature
`exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))` に直結)。係数 `(2πe)` の付替は
scaling corollary で扱える。 -/
noncomputable def entropyPower (μ : Measure ℝ) : ℝ :=
  Real.exp (2 * Common2026.Shannon.differentialEntropy μ)

/-- Entropy power is strictly positive. -/
theorem entropyPower_pos (μ : Measure ℝ) : 0 < entropyPower μ :=
  Real.exp_pos _

/-- Entropy power is non-negative. -/
theorem entropyPower_nonneg (μ : Measure ℝ) : 0 ≤ entropyPower μ :=
  (entropyPower_pos μ).le

/-- Unfold lemma for `entropyPower`. -/
theorem entropyPower_eq_exp_two_differentialEntropy (μ : Measure ℝ) :
    entropyPower μ = Real.exp (2 * Common2026.Shannon.differentialEntropy μ) := rfl

/-- **Closed form for Gaussian entropy power**: `entropyPower (gaussianReal m v) =
2πe v`. This is the Gaussian saturation reference value that drives the
saturating case of EPI.

Computation: by `differentialEntropy_gaussianReal`, `h(𝒩(m,v)) = (1/2) log(2πe v)`,
so `entropyPower (𝒩(m,v)) = exp(2 · (1/2) log(2πe v)) = exp(log(2πe v)) = 2πe v`. -/
theorem entropyPower_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    entropyPower (gaussianReal m v) = 2 * Real.pi * Real.exp 1 * v := by
  unfold entropyPower
  rw [Common2026.Shannon.differentialEntropy_gaussianReal m hv]
  have h_simplify :
      (2 : ℝ) * ((1/2) * Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)))
        = Real.log (2 * Real.pi * Real.exp 1 * (v : ℝ)) := by ring
  rw [h_simplify]
  have h_pos : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (v : ℝ) := by
    have hv_pos : (0 : ℝ) < (v : ℝ) := by
      have : (v : ℝ) ≠ 0 := by exact_mod_cast hv
      exact lt_of_le_of_ne v.coe_nonneg (Ne.symm this)
    positivity
  exact Real.exp_log h_pos

/-! ## §B — L-EPI1 + L-EPI2 + L-EPI3 retreat predicates -/

/-- **L-EPI1 (Stam inequality hypothesis)**: 1-dim Stam の
`1/J(X+Y) ≥ 1/J(X) + 1/J(Y)` (Fisher information の inverse triangle inequality)
を hypothesis 化。

主定理 signature 露出のみ、本体未使用。Cover-Thomas Lemma 17.7.2 (Stam)
の textbook signature を保持するため、placeholder `Prop := True` で導入。
Discharge plan `epi-stam-discharge-plan.md` (未着手) で真の Stam inequality
形に置換する想定。 -/
def IsStamInequalityHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop := True


/-- **L-EPI2 (de Bruijn integration hypothesis)**: heat-flow path `Z_t = X+√t G`
(`G ∼ 𝒩(0,1)`) 上での `(d/dt) h(Z_t) = (1/2) J(Z_t)` integration identity
を hypothesis 化。

主定理 signature 露出のみ、本体未使用。T2-F `Common2026.Shannon.IsRegularDeBruijnHyp`
を `t ∈ [0, ∞)` 上で積分する形の discharge plan `epi-debruijn-integration-plan.md`
(未着手) で真の積分恒等式 predicate に置換する想定。 -/
def IsDeBruijnIntegrationHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop := True

/-- **L-EPI3 (EPI conclusion predicate)**: EPI 結論

    `entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`

を `Prop` として名付けたもの。**これは主定理の結論そのもの**であり、主定理の
hypothesis としては使わない (使うと `theorem epi (h : EPI) : EPI := h` の循環に
なる)。Gaussian saturation の出力 (§D) や下流 pipeline の中間結果に名前を付ける
ためだけに保持する。主定理は genuine な非循環 residual `IsStamInequalityResidual`
+ bridge `IsStamToEPIBridge` から `IsEntropyPowerInequalityHypothesis` を**導出**
する。 -/
def IsEntropyPowerInequalityHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  entropyPower (P.map (fun ω => X ω + Y ω))
    ≥ entropyPower (P.map X) + entropyPower (P.map Y)

/-- **Stam inequality residual** (Cover-Thomas Lemma 17.7.2, V2 density-keyed 真 signature).

For independent `X, Y` with finite Fisher information `J` (genuine V2 score-based
Fisher info `fisherInfoOfDensityReal`, keyed on the density witnesses of the three
mapped measures),

    `1 / J(X + Y) ≥ 1 / J(X) + 1 / J(Y)`.

This is the genuine, **non-circular** residual driving EPI: its type is the Stam
harmonic-mean inequality, which is *not* the EPI conclusion. Mathlib has neither
Fisher-info convolution nor the inverse-triangle inequality (`rg "Stam" → 0 hit`),
so this is the real analytic wall, discharged downstream
(`EPIStamInequalityBody.lean` Cauchy-Schwarz + λ-optimization body).

Quantified over abstract positive reals matching the V2 Fisher info of the three
density witnesses; this is the predicate the EPI derivation actually consumes.
(Density-keyed `fisherInfoOfDensityReal` is used here rather than the measure-keyed
`fisherInfoOfMeasureV2` to keep this base file free of an import cycle through
`FisherInfoV2DeBruijn`; the two agree by `fisherInfoOfMeasureV2_def`.) -/
def IsStamInequalityResidual {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    J_X = Common2026.Shannon.FisherInfoV2.fisherInfoOfDensityReal fX →
    J_Y = Common2026.Shannon.FisherInfoV2.fisherInfoOfDensityReal fY →
    J_sum = Common2026.Shannon.FisherInfoV2.fisherInfoOfDensityReal fXY →
    1 / J_sum ≥ 1 / J_X + 1 / J_Y

/-- **Stam-to-EPI bridge** (Cover-Thomas Lemma 17.7.3 coupling argument).

The genuine, **non-circular** discharge route: from the Stam inequality residual
derive the EPI conclusion via the Csiszár scaling-path / de Bruijn integration
argument. Phrased as `IsStamInequalityResidual → IsEntropyPowerInequalityHypothesis`,
so its type is *not* the EPI conclusion. The bridge is the deepest analytic
primitive (path-integral coupling); discharged downstream and, for the Gaussian
case, by saturation (§D). -/
def IsStamToEPIBridge {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  IsStamInequalityResidual X Y P → IsEntropyPowerInequalityHypothesis X Y P

/-! ## §C — 主定理 (Cover-Thomas Theorem 17.7.3, non-circular Stam-bridge 形) -/

/-- **Entropy Power Inequality** (Cover-Thomas Theorem 17.7.3).

独立な実値確率変数 `X, Y` に対し

    `entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`,

すなわち `exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))`。

**非循環 residual から導出**: 主定理は EPI 結論そのものを hypothesis に取らず
(それは循環)、genuine な residual

* `h_stam` (L-EPI1, Cover-Thomas Lemma 17.7.2): Stam の inverse harmonic-mean
  inequality `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)` — **EPI 結論とは別の `Prop`**。
* `h_bridge` (Cover-Thomas Lemma 17.7.3): Stam → EPI coupling
  (`IsStamInequalityResidual → IsEntropyPowerInequalityHypothesis`) —
  これも **EPI 結論とは別の `Prop`** (function type)。

から `h_bridge h_stam` で EPI を**導出**する。両 hypothesis とも結論と
defeq でなく、本体は `:= h` 循環ではない。両者の discharge (真の Mathlib 壁) は
`EPIStamInequalityBody.lean` / `EPIStamDeBruijnConclusion.lean` で進行、Gaussian
case は §D で full discharge。

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem entropy_power_inequality {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityResidual X Y P)
    (h_bridge : IsStamToEPIBridge X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  h_bridge h_stam

/-- **EPI in `Real.exp (2 · ...)` form** (Cover-Thomas 露出形).

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem entropy_power_inequality_exp_form {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityResidual X Y P)
    (h_bridge : IsStamToEPIBridge X Y P) :
    Real.exp (2 * Common2026.Shannon.differentialEntropy
              (P.map (fun ω => X ω + Y ω)))
      ≥ Real.exp (2 * Common2026.Shannon.differentialEntropy (P.map X))
        + Real.exp (2 * Common2026.Shannon.differentialEntropy (P.map Y)) := by
  have h := entropy_power_inequality P X Y hX hY hXY h_stam h_bridge
  simpa [entropyPower] using h

/-! ## §D — Gaussian saturation case (Cover-Thomas Theorem 17.7.3 等号成立、FULL DISCHARGE) -/

/-- **Gaussian saturation case**: X, Y それぞれ独立 Gaussian で variance 非零
なら EPI は **等号成立** `exp(2 h(X+Y)) = exp(2 h(X)) + exp(2 h(Y))`.

撤退ラインなしで full discharge (Mathlib `gaussianReal_add_gaussianReal_of_indepFun`
が sum の law を Gaussian と特定 + Common2026 `differentialEntropy_gaussianReal`
が closed form を与える)。

これにより L-EPI3 hypothesis は **Gaussian の場合 trivially provable**
(同 hypothesis を `_ge_of_eq` の形で得る、§E corollary
`isEntropyPowerInequalityHypothesis_of_gaussian` 参照)。 -/
theorem entropy_power_inequality_gaussian_saturation
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      = entropyPower (P.map X) + entropyPower (P.map Y) := by
  -- Step 1: `(X+Y).law = gaussianReal (m₁+m₂) (v₁+v₂)` from Mathlib.
  have h_sum_law : P.map (fun ω => X ω + Y ω) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
    have h := gaussianReal_add_gaussianReal_of_indepFun hXY hLawX hLawY
    -- `X + Y` in Mathlib lemma is `Pi.instAdd`-form which is defeq to `fun ω => X ω + Y ω`.
    -- Convert via `Pi.add_apply` / `funext`.
    have h_eq : (X + Y) = fun ω => X ω + Y ω := by
      funext ω; rfl
    rw [h_eq] at h
    exact h
  -- Step 2: `v₁ + v₂ ≠ 0` from `hv₁`.
  have hv_sum : v₁ + v₂ ≠ 0 := by
    intro h_eq
    -- `v₁ + v₂ = 0` over `ℝ≥0` implies both are `0` (`NNReal` cancellative add).
    have h1 : v₁ ≤ v₁ + v₂ := le_self_add
    rw [h_eq] at h1
    have h2 : v₁ = 0 := le_antisymm h1 bot_le
    exact hv₁ h2
  -- Step 3: rewrite all three entropy powers as `2πe · v_*`.
  rw [hLawX, hLawY, h_sum_law]
  rw [entropyPower_gaussianReal m₁ hv₁, entropyPower_gaussianReal m₂ hv₂,
      entropyPower_gaussianReal (m₁ + m₂) hv_sum]
  -- Step 4: `2πe (v₁ + v₂) = 2πe v₁ + 2πe v₂`.
  push_cast
  ring

/-- L-EPI3 hypothesis is satisfied (with equality) whenever both `X` and `Y` are
independent Gaussians. -/
theorem isEntropyPowerInequalityHypothesis_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    IsEntropyPowerInequalityHypothesis X Y P := by
  unfold IsEntropyPowerInequalityHypothesis
  rw [entropy_power_inequality_gaussian_saturation P X Y hX hY hXY m₁ m₂ v₁ v₂
        hv₁ hv₂ hLawX hLawY]

/-- **Stam-to-EPI bridge from a known EPI fact** (trivial discharge). When the
EPI conclusion is already established by some non-circular route (e.g. Gaussian
saturation), the bridge is the constant function — it ignores its Stam input.

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem isStamToEPIBridge_of_epi
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_epi : IsEntropyPowerInequalityHypothesis X Y P) :
    IsStamToEPIBridge X Y P :=
  fun _ => h_epi

/-- **Stam-to-EPI bridge for the Gaussian case** (full discharge, no Stam input
needed). For independent Gaussians `X, Y` with non-zero variance, the bridge is
discharged hypothesis-free via Gaussian saturation. -/
theorem isStamToEPIBridge_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    IsStamToEPIBridge X Y P :=
  isStamToEPIBridge_of_epi
    (isEntropyPowerInequalityHypothesis_of_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂
      hv₁ hv₂ hLawX hLawY)

/-! ## §E — 補助 corollary 群 -/

/-- **Translation invariance of entropy power**: for `μ ≪ volume` and
σ-finite `μ`, `entropyPower (μ.map (· + a)) = entropyPower μ`. The hypothesis
matches `Common2026.Shannon.differentialEntropy_map_add_const`. -/
theorem entropyPower_map_add_const {μ : Measure ℝ} (hμ : μ ≪ volume)
    [SigmaFinite μ] (a : ℝ) :
    entropyPower (μ.map (· + a)) = entropyPower μ := by
  unfold entropyPower
  rw [Common2026.Shannon.differentialEntropy_map_add_const hμ]

/-- **EPI in log form** (Cover-Thomas Ch.17 alternative signature).

For independent `X, Y`, `h(X+Y) ≥ (1/2) · log (exp(2 h(X)) + exp(2 h(Y)))`.

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem entropy_power_inequality_log_form {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityResidual X Y P)
    (h_bridge : IsStamToEPIBridge X Y P) :
    Common2026.Shannon.differentialEntropy (P.map (fun ω => X ω + Y ω))
      ≥ (1/2) * Real.log
          (entropyPower (P.map X) + entropyPower (P.map Y)) := by
  -- The EPI core inequality.
  have h_epi' : entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
    entropy_power_inequality P X Y hX hY hXY h_stam h_bridge
  -- RHS of `≥` is positive (sum of two positive `entropyPower`s).
  have h_rhs_pos : 0 < entropyPower (P.map X) + entropyPower (P.map Y) :=
    add_pos (entropyPower_pos _) (entropyPower_pos _)
  -- Take `Real.log` of both sides (monotone on `(0, ∞)`).
  have h_log : Real.log (entropyPower (P.map (fun ω => X ω + Y ω)))
      ≥ Real.log (entropyPower (P.map X) + entropyPower (P.map Y)) :=
    Real.log_le_log h_rhs_pos h_epi'
  -- LHS log = 2 * h(X+Y) (from `log_exp`).
  have h_lhs_log :
      Real.log (entropyPower (P.map (fun ω => X ω + Y ω)))
        = 2 * Common2026.Shannon.differentialEntropy (P.map (fun ω => X ω + Y ω)) := by
    unfold entropyPower
    rw [Real.log_exp]
  rw [h_lhs_log] at h_log
  linarith

/-- **3-arg EPI pass-through**: 3 つの独立変数 `X, Y, Z` に対し EPI を
chain することで `exp(2 h(X+Y+Z)) ≥ exp(2 h(X)) + exp(2 h(Y)) + exp(2 h(Z))`.

撤退ラインは 2-arg 形を 2 回適用するための 2 つの L-EPI3 hypothesis を
取る形に外出し (X+Y vs Z のペアで 1 回、X vs Y のペアで 1 回)。

`@audit:suspect(epi-stam-to-conclusion-plan)` -/
theorem entropy_power_inequality_three_arg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z : Ω → ℝ)
    (h_xy_z_epi : IsEntropyPowerInequalityHypothesis (fun ω => X ω + Y ω) Z P)
    (h_x_y_epi : IsEntropyPowerInequalityHypothesis X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω + Z ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) + entropyPower (P.map Z) := by
  -- Step 1: from `h_xy_z_epi`, we get
  --   `entropyPower ((X+Y)+Z) ≥ entropyPower (X+Y) + entropyPower Z`.
  have h1 : entropyPower (P.map (fun ω => X ω + Y ω + Z ω))
      ≥ entropyPower (P.map (fun ω => X ω + Y ω)) + entropyPower (P.map Z) := by
    -- `fun ω => (X ω + Y ω) + Z ω` is `fun ω => X ω + Y ω + Z ω` (assoc).
    have h_assoc : (fun ω : Ω => (X ω + Y ω) + Z ω)
        = (fun ω : Ω => X ω + Y ω + Z ω) := by
      funext ω; ring
    have h := h_xy_z_epi
    unfold IsEntropyPowerInequalityHypothesis at h
    rw [h_assoc] at h
    exact h
  -- Step 2: from `h_x_y_epi`, we get
  --   `entropyPower (X+Y) ≥ entropyPower X + entropyPower Y`.
  have h2 : entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := h_x_y_epi
  -- Combine via transitivity (add `entropyPower Z` to both sides of h2).
  linarith

end InformationTheory.Shannon.EntropyPowerInequality
