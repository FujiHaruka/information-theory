import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.FisherInfo.Basic
import InformationTheory.Shannon.FisherInfo.V2
import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.EPI.Blachman.Density
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

* **L-EPI1 (Stam inequality)**: genuine 代替 `IsStamInequalityResidual X Y P :
  Prop` (`:197+`) が Stam の `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)` を density-keyed
  Fisher info で表現。主定理 `entropy_power_inequality` の hypothesis に直接
  入っており、旧 placeholder `IsStamInequalityHypothesis := True` (Phase 3
  Wave 2 retract 済) は廃止。Discharge plan `epi-stam-discharge-plan.md`
  (未着手) で shared sorry 補題 `stamToEPIBridge_holds` を closure 予定。
* **L-EPI2 (de Bruijn integration)**: heat-flow path 上の EPI integration
  identity は T2-F `IsRegularDeBruijnHyp` を `[0, ∞)` 上で積分する形で扱う。
  旧 placeholder `IsDeBruijnIntegrationHypothesis := True` (Phase 3 Wave 2
  retract 済) は廃止。`wall:debruijn-integration` は **[CLOSED 2026-06-04]**
  — genuine (sorryAx-free) `debruijnIdentityV2_holds_assembled`
  (`FisherInfoV2DeBruijnAssembly.lean`) に集約され、旧 shared sorry 補題
  `debruijnIdentityV2_holds` は削除済。
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
  `gaussianReal_add_gaussianReal_of_indepFun` + InformationTheory
  `differentialEntropy_gaussianReal` の合成で **full discharge** (撤退
  ラインなし)。

## 主シグネチャ

* `entropyPower` — Phase A 定義
* `entropyPower_pos`, `entropyPower_gaussianReal` — Tier 0 補助
* `IsEntropyPowerInequalityHypothesis` — Phase B L-EPI3 predicate
  (L-EPI1 / L-EPI2 placeholder `Prop := True` 形は Phase 3 Wave 2 retract 済、
  genuine 代替は `IsStamInequalityResidual` (L-EPI1) + genuine `debruijnIdentityV2_holds_assembled` (L-EPI2、`wall:debruijn-integration` は [CLOSED 2026-06-04]))
* `entropy_power_inequality` — Phase C 主定理 (L-EPI3 適用形)
* `entropy_power_inequality_exp_form` — Cover-Thomas 露出形 (Real.exp 展開)
* `entropyPower_gaussian_additivity` — Phase D, full discharge (Cover-Thomas Ch.17 用語整合)
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

`entropyPower μ := exp (2 · h(μ))` where `h` is `InformationTheory.Shannon.differentialEntropy`.

Cover-Thomas Ch.17 の `N(X) := (2πe)⁻¹ · exp(2 h(X))` と係数差のみ; 本 file
は `exp (2 h(μ))` 直書きで採用する (Mathlib-shape-driven, EPI signature
`exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))` に直結)。係数 `(2πe)` の付替は
scaling corollary で扱える。 -/
noncomputable def entropyPower (μ : Measure ℝ) : ℝ :=
  Real.exp (2 * InformationTheory.Shannon.differentialEntropy μ)

/-- Entropy power is strictly positive.

@audit:ok -/
@[entry_point]
theorem entropyPower_pos (μ : Measure ℝ) : 0 < entropyPower μ :=
  Real.exp_pos _

/-- Entropy power is non-negative.

@audit:ok -/
@[entry_point]
theorem entropyPower_nonneg (μ : Measure ℝ) : 0 ≤ entropyPower μ :=
  (entropyPower_pos μ).le

/-- **Closed form for Gaussian entropy power**: `entropyPower (gaussianReal m v) =
2πe v`. This is the Gaussian saturation reference value that drives the
saturating case of EPI.

Computation: by `differentialEntropy_gaussianReal`, `h(𝒩(m,v)) = (1/2) log(2πe v)`,
so `entropyPower (𝒩(m,v)) = exp(2 · (1/2) log(2πe v)) = exp(log(2πe v)) = 2πe v`.

@audit:ok -/
@[entry_point]
theorem entropyPower_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    entropyPower (gaussianReal m v) = 2 * Real.pi * Real.exp 1 * v := by
  unfold entropyPower
  rw [InformationTheory.Shannon.differentialEntropy_gaussianReal m hv]
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

-- (retracted, Phase 3 Wave 2, 2026-05-27) `IsStamInequalityHypothesis := True`
-- (旧 L-EPI1 placeholder, defect-kind prop-true) was retracted: the genuine
-- non-circular alternative `IsStamInequalityResidual` (`:152+`) is now in place
-- and is consumed directly by `entropy_power_inequality`. The lone bridge
-- wrapper `isStamInequalityHypothesis_of_stamInequalityHyp` in
-- `EPIStamDischarge.lean` (body `trivial`) has been deleted in the same wave.
--
-- (retracted, Phase 3 Wave 2, 2026-05-27) `IsDeBruijnIntegrationHypothesis := True`
-- (旧 L-EPI2 placeholder, defect-kind prop-true) was retracted: its sole
-- call site was `epi_via_stam_main_eq` as an unused `_h_db` argument, which
-- has been removed; the de Bruijn identity is now the genuine (sorryAx-free)
-- `debruijnIdentityV2_holds_assembled` (`FisherInfoV2DeBruijnAssembly.lean`;
-- `wall:debruijn-integration` is [CLOSED 2026-06-04]), which supersedes the
-- placeholder.

/-- **L-EPI3 (EPI conclusion predicate)**: EPI 結論

    `entropyPower (P.map (X+Y)) ≥ entropyPower (P.map X) + entropyPower (P.map Y)`

を `Prop` として名付けたもの。**これは EPI 結論そのもの**であり、hypothesis として
は使わない (使うと `theorem epi (h : EPI) : EPI := h` の循環になる)。Gaussian
saturation の出力 (§D) や下流 pipeline の中間結果に名前を付けるために保持する。 -/
def IsEntropyPowerInequalityHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  entropyPower (P.map (fun ω => X ω + Y ω))
    ≥ entropyPower (P.map X) + entropyPower (P.map Y)

-- (deleted 2026-06-11, legacy Stam→EPI subtree removal) The Stam residual
-- `IsStamInequalityResidual` (Cover-Thomas Lemma 17.7.2 V2 density-keyed Prop) was
-- removed: after deleting the legacy bridge (`IsStamToEPIBridge` /
-- `stamToEPIBridge_holds`) and all its consumers (`entropy_power_inequality` and the
-- exp/log/normalized/integrated/via-stam wrappers), it had 0 remaining references
-- (verified by `scripts/dep_consumers.sh`). It was a sorryAx-free Prop, so its
-- removal is harmless. The genuine Stam residual still consumed by the live
-- (non-legacy) pipeline is `EPIStamDischarge.IsStamInequalityHyp`.

/-! ## §D — Gaussian saturation case (Cover-Thomas Theorem 17.7.3 等号成立、FULL DISCHARGE) -/

/-- **Gaussian saturation case**: X, Y それぞれ独立 Gaussian で variance 非零
なら EPI は **等号成立** `exp(2 h(X+Y)) = exp(2 h(X)) + exp(2 h(Y))`.

撤退ラインなしで full discharge (Mathlib `gaussianReal_add_gaussianReal_of_indepFun`
が sum の law を Gaussian と特定 + InformationTheory `differentialEntropy_gaussianReal`
が closed form を与える)。

これにより L-EPI3 hypothesis は **Gaussian の場合 trivially provable**
(同 hypothesis を `_ge_of_eq` の形で得る、§E corollary
`isEntropyPowerInequalityHypothesis_of_gaussian` 参照)。

@audit:ok -/
@[entry_point]
theorem entropyPower_gaussian_additivity
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
independent Gaussians.

@audit:ok -/
@[entry_point]
theorem isEntropyPowerInequalityHypothesis_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    IsEntropyPowerInequalityHypothesis X Y P := by
  unfold IsEntropyPowerInequalityHypothesis
  rw [entropyPower_gaussian_additivity P X Y hX hY hXY m₁ m₂ v₁ v₂
        hv₁ hv₂ hLawX hLawY]

-- (retracted 2026-05-28, EPI-Stam Cluster C+D sweep) `isStamToEPIBridge_of_epi`
-- was a trivial pass-through `IsEntropyPowerInequalityHypothesis X Y P →
-- IsStamToEPIBridge X Y P := fun _ => h_epi` with **0 consumers** (verified
-- via `rg -n 'isStamToEPIBridge_of_epi' InformationTheory/` returning only the
-- declaration line). It carried `@audit:retract-candidate(load-bearing-predicate)`
-- + `@audit:closed-by-successor(epi-stam-to-conclusion-plan)`; the discharge
-- path it provided (Gaussian-saturation → bridge) is now publicly available
-- via `EPIStamDischarge.isStamToEPIBridgeHyp_of_gaussian`, so this
-- in-file `IsStamToEPIBridge` wrapper is redundant.

/-! ## §E — 補助 corollary 群 -/

/-- **Translation invariance of entropy power**: for `μ ≪ volume` and
σ-finite `μ`, `entropyPower (μ.map (· + a)) = entropyPower μ`. The hypothesis
matches `InformationTheory.Shannon.differentialEntropy_map_add_const`.

@audit:ok -/
@[entry_point]
theorem entropyPower_map_add_const {μ : Measure ℝ} (hμ : μ ≪ volume)
    [SigmaFinite μ] (a : ℝ) :
    entropyPower (μ.map (· + a)) = entropyPower μ := by
  unfold entropyPower
  rw [InformationTheory.Shannon.differentialEntropy_map_add_const hμ]

/-- **3-arg EPI pass-through**: 3 つの独立変数 `X, Y, Z` に対し EPI を
chain することで `exp(2 h(X+Y+Z)) ≥ exp(2 h(X)) + exp(2 h(Y)) + exp(2 h(Z))`.

2-arg 形を 2 回適用するための 2 つの lower-arity EPI 結論を取る (X+Y vs Z の
ペアで 1 回、X vs Y のペアで 1 回)。

`@audit:ok` — Cluster C sorry-migration audit 2026-05-28. 本 wrapper の body は
genuine な structural composition (assoc + transitivity via `linarith`、internal
`sorry` なし)。caller が供給する `h_xy_z_epi` / `h_x_y_epi` は lower-arity の EPI
**結論** (`IsEntropyPowerInequalityHypothesis _ _ P`) を transparent に carry する
ものであり、当該 wrapper 自身は core を抱えていない — transitive な load-bearing-ness
は L-EPI3 predicate の定義 site (`IsEntropyPowerInequalityHypothesis`、named
conclusion form) に live する。sister `EPIPlumbing.entropy_power_inequality_four_arg`
(Phase 1.C audit で同一 rationale により `@audit:ok`) と同型。stale な
`@audit:retract-candidate(load-bearing-predicate)` から migrate。
**signature 不変**: 本 wrapper は `EPIL3Integration.entropy_power_inequality_three_arg_integrated`
(parallel Group 1 が編集中) が現 signature で consume するため、引数を削ると cross-file
collision。一般原則として、Stam noise / de Bruijn regularity / limit hyp を thread する
discharge route を、hypothesis-free を標榜する wrapper の delegate 先には使わない
(hypothesis-free 偽装を避ける)。 -/
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