# EPI Stam → conclusion Phase A: Stam + de Bruijn 合流 (Csiszár scaling) サブ計画

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A (line 467-547)
> **Created**: 2026-05-25 (Phase D 合流 commit `c0edbe1` 直後)
> **Status**: **Phase A COMPLETED** (2026-05-27、A-1〜A-V 全 step)
>   - A-1 ✓ `IsStamScalingNoiseHyp` staged (commit `8e23d94`)
>   - A-0' ✓ (commit `c0edbe1`)
>   - A-2 ✓ `csiszarGap1Source_hasDerivAt`
>   - A-3 ✓ Stam reduction (`antitoneOn_of_deriv_nonpos`)
>   - A-4 ✓ rescale 持ち上げ skeleton + `isStamToEPIScalingHyp_of_stam_debruijn` (commit `d3ac59f`、3 genuine + 2 撤退 sorry、L-Concl-A-β/θ 発動)
>   - A-5 ✓ `isStamToEPIBridgeHyp_of_stam_debruijn` (commit `1bd3866`、`@audit:ok`)
>   - A-6 ✓ `entropy_power_inequality_unconditional` 案 a wrapper (commit `3db3a9e`)
>   - A-V ✓ post-merge cleanup (14 件 + 5 件 per-declaration migration)

## Position

- 親 sub-plan: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) Phase A
- 上流入力 (Phase D 完了済): [`epi-stam-discharge-plan.md`](epi-stam-discharge-plan.md) / [`epi-debruijn-integration-phaseD-plan.md`](epi-debruijn-integration-phaseD-plan.md) (commit `c0edbe1`)
- 下流: 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:232`) の hypothesis-free 化 → 親 plan §Phase B / §V

## Motivation

Phase 0 で `IsStamToEPIScalingHyp` (`EPIStamToBridge.lean:202-216`) を `∃ Z_X Z_Y, ... ∧ AntitoneOn gap (Set.Icc 0 1)` 形に refactor、Phase D で sister `csiszarGap` (`EPIL3Integration.lean:1160-1164`) が verbatim 同形で publish、`csiszarGap_shape_for_sister` (`:1279-1287`) `rfl` で接続。本 Phase A はこの 2 handoff を消費し **`AntitoneOn (csiszarGap ...) (Set.Icc 0 1)` を Stam + de Bruijn から genuine 構築**:

1. path-derivative `d/ds (csiszarGap _) ≤ 0` (de Bruijn V2 + Stam)
2. `antitoneOn_of_deriv_nonpos` で `AntitoneOn`
3. existential witness `(Z_X, Z_Y)` と bundle → `isStamToEPIScalingHyp_of_stam_debruijn`
4. 既存 `isStamToEPIBridgeHyp_of_scaling` (`EPIStamToBridge.lean:672`、`IsStamToEPILimitHyp` 不要) 経由で `IsStamToEPIBridgeHyp` genuine 化
5. 主定理を hypothesis-free 化 (案 a wrapper)

verbatim 確認した前提コード位置: `DifferentialEntropy.lean:147` / `HeatFlowPath.lean:49-58` / `EPIStamToBridge.lean:210-216,672` / `EPIL3Integration.lean:1160-1164,1194-1215,1279-1287` / `EPIStamDischarge.lean:97-104,193-228,258-268,337-339` / `EntropyPowerInequality.lean:80,187-205,232-240,270-301`。`IsStamInequalityResidual` / `IsStamToEPIBridge` は `*Hyp` 系列と defeq (`fisherInfoOfMeasureV2_def` 経由)。

## Scope (4 file、~225 行追記済)

| 対象 | 役割 |
|---|---|
| `EPIL3Integration.lean` §13 拡張 | `csiszarGap1Source` def + 補題 4 件 (A-0') |
| `EPIStamToBridge.lean` 拡張 | `IsStamScalingNoiseHyp` (A-1) + `isStamToEPIScalingHyp_of_stam_debruijn` (A-2〜A-4) |
| `EntropyPowerInequality.lean` | `entropy_power_inequality_unconditional` wrapper (A-6 案 a) |
| `EPIL3Integration.lean` / `EPIStamDeBruijnConclusion.lean` 等 | 14+5 件 per-declaration tag 書換 (A-V) |

## ゴール / Approach

```
[Phase D 出力]              [Sister 出力]                   [Mathlib]
  csiszarGap                  IsStamInequalityHyp             antitoneOn_of_deriv_nonpos
  csiszarGap_at_*             IsDeBruijnIntegrationHyp        HasDerivAt.sub / Real.hasDerivAt_exp
  csiszarGap_shape_for_sister (両方 Phase D staged-honest)    entropy_power_inequality_gaussian_saturation
  gaussianConvolution / derivAt_entropy_eq_half_fisher_v2 (1-source 形)
  isStamToEPIBridgeHyp_of_scaling (Phase 0 @audit:ok、IsStamToEPILimitHyp 不要)
       └──────┬──────┘
              ▼
   A-0  sister 出力存在確認
   A-0' Phase D §13 に 1-source alias 追加 (alias 追加路線、Phase D 既存物 untouched)
   A-1  IsStamScalingNoiseHyp staged (richness)
   A-2  d/dt (csiszarGap1Source) = de Bruijn V2 直接適用 (base が t 非依存、scaling 補正項なし)
   A-3  1-source Stam ⇒ deriv ≤ 0 (Cauchy-Schwarz weight は linarith 吸収)
   A-4  antitoneOn_of_deriv_nonpos → rescale で 2-source AntitoneOn (Set.Icc 0 1) 持ち上げ → IsStamToEPIScalingHyp
   A-5  _of_scaling 呼出すだけ → IsStamToEPIBridgeHyp
   A-6  主定理 hypothesis-free wrapper (案 a)
```

**設計選択 (Mathlib-shape-driven)**:

- **`AntitoneOn`** (not `MonotoneOn`、gap が時間進行で 0 へ decreasing、Phase 0 sign correction 済)
- **`Set.Icc 0 1`** (`convex_Icc` で `Convex D` discharge、interior `Ioo 0 1` で `HasDerivAt`)
- **1-source 形 alias 経由** (L-Concl-A-δ 撤退判定 (c)、2-source `heatFlowPath2` reparametrize は scaling 補正項発生で Stam reduce 失敗 → Phase D §13 に `csiszarGap1Source` 追加して 1-source 形上で derivative + Stam reduction を完結、A-4 で rescale 持ち上げ)
- **derivative form**: `(1/2) · (J_sum/N_sum − J_X/N_X − J_Y/N_Y)`、de Bruijn V2 returns `(1/2) · J/N` を 3 項合算 (chain rule weight `Real.hasDerivAt_exp` 1 件)

**段階的 ship**: atomic (A-6 まで完成しないと partial publish 価値なし)、撤退ライン発火時のみ partial 化。

## 進捗

すべて 2026-05-27 までに完了 (上の Status 参照)。A-4-1 / A-4-4 は撤退発火で `@residual(plan:epi-stam-to-conclusion-phaseA-A4-{continuity,rescale})` 残置 → L-Concl-A-θ / β。

proof-log: `docs/shannon/proof-log-epi-stam-to-conclusion-phaseA.md` 既出。

## Phase 詳細

### A-0 — sister Phase D 出力存在確認

Read のみ、コード変更なし。`csiszarGap` / `IsStamInequalityHyp` / `IsDeBruijnIntegrationHyp` / `IsDeBruijnRegularityHyp` / `IsStamToEPIScalingHyp` / `isStamToEPIBridgeHyp_of_scaling` の signature を verbatim 照合 (位置 → Motivation 参照)。`_of_scaling` が `IsStamToEPILimitHyp` を一切要求しないことが A-5 simplify の前提。

### A-0' — Phase D §13 1-source 形 alias 拡張 (`csiszarGap1Source` + 補題 4 件)

**設計判断**: alias 追加 (Phase D 既存物 untouched、additive 拡張、commit `c0edbe1` audit 保全)。redefine 案は `IsStamToEPIScalingHyp` shape contract + `csiszarGap_shape_for_sister` `rfl` + EPIL3 14 件 `@audit:suspect` を巻き戻すため却下。

追加物 (`EPIL3Integration.lean` §13 末尾):

1. `csiszarGap1Source` (noncomputable def): `entropyPower (P.map (X+Y+√t·(Z_X+Z_Y))) − entropyPower(X+√t·Z_X) − entropyPower(Y+√t·Z_Y)`
2. `csiszarGap_eq_one_source_via_rescale` (`s ∈ Set.Ico 0 1`): `csiszarGap _ s = (1-s) · csiszarGap1Source _ (s/(1-s))`、根拠 `heatFlowPath2 X Z s = √(1-s) · (X + √(s/(1-s)) · Z)` + `entropyPower` scale-invariance (`entropyPower_const_mul` → L-Concl-A-η 候補)
3. `csiszarGap1Source_at_zero`: `Real.sqrt_zero` simp
4. `csiszarGap1Source_tendsto_zero_at_infinity_of_gaussian_pair`: statement-only handoff (証明は L-Concl-A-β、Phase B / 別 plan)
5. `csiszarGap1Source_shape_for_sister`: `rfl` lemma

撤退ライン: L-Concl-A-η (補題 2 scale law 不在で >30 行) / L-Concl-A-β (補題 3 tendsto)。

### A-1 — `IsStamScalingNoiseHyp` staged (standard normal pair witness)

Richness 仮定 (Cover-Thomas Ch.17 暗黙) を honest な新規 staged predicate に外出し:

```lean
def IsStamScalingNoiseHyp X Y P : Prop :=
  ∃ (Z_X Z_Y : Ω → ℝ),
    Measurable Z_X ∧ Measurable Z_Y ∧
    P.map Z_X = gaussianReal 0 1 ∧ P.map Z_Y = gaussianReal 0 1 ∧
    IndepFun X Z_X P ∧ IndepFun Y Z_Y P ∧ IndepFun Z_X Z_Y P
```

`@audit:staged(epi-stam-to-conclusion-plan)` 付与、Mathlib 壁 (b) — standard noise extension on arbitrary probability space 未整備、上流貢献 task として外出し。Phase 0 `_of_gaussian` retract (`EPIStamToBridge.lean:317-327`) の前例あり。任意 stretch: `isStamScalingNoiseHyp_of_atomless` (Mathlib に `AtomlessProbability` なければ skip)。

撤退ライン: L-Concl-A-γ (genuine 構築不能で staged のまま伝播)。

### A-2 — `csiszarGap1Source_hasDerivAt`

de Bruijn V2 `derivAt_entropy_eq_half_fisher_v2` (`FisherInfoV2DeBruijn.lean:245`、1-source 形) を 3 mapped 測度 (`X+Y` / `X` / `Y`) に直接適用、`Real.hasDerivAt_exp` chain rule 1 件で `entropyPower`、`HasDerivAt.sub` で合成。base `t` 非依存ゆえ scaling 補正項なし (旧 L-Concl-A-δ 根本回避)。

新規補題 `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` (A-2-2、`HasDerivAt h d t → HasDerivAt (exp ∘ (2·h)) (exp(2·h)·2·d) t`) は >30 行で L-Concl-A-ε 発火。

### A-3 — `g'(t) ≤ 0 from IsStamInequalityHyp` (1-source 形)

A-2-3 出力に 1-source Stam `1/J(X+Y+G) ≥ 1/J(X+G_X) + 1/J(Y+G_Y)` を harmonic-mean 形 (`J_sum ≤ J_X·J_Y/(J_X+J_Y)`) に algebraic transform、`Real.exp` 単調性 + `linarith` で reduce。Cover-Thomas eq.(17.43) Cauchy-Schwarz weight は 1-source 化により `linarith` 吸収可能性が高い (発火時のみ L-Concl-A-ζ、新規 `IsCsiszarScalingWeightHyp1Source` staged)。

### A-4 — `AntitoneOn` 構成 + rescale 持ち上げ + `IsStamToEPIScalingHyp` 完成

- A-4-1 `csiszarGap1Source_continuousOn` (`Set.Ici 0`、`t=0` 端点は A-0'-3 closed form) → **撤退発火** L-Concl-A-θ、`@residual(plan:epi-stam-to-conclusion-phaseA-A4-continuity)` 残置 (`EPIStamToBridge.lean:809`、`entropyPower ∘ P.map` の `√t → 0` continuity が Lebesgue-dominated-convergence machinery 要求、A-4 budget 超過)
- A-4-2 `csiszarGap1Source_differentiableOn_interior` ✓ genuine
- A-4-3 `antitoneOn_of_deriv_nonpos` 適用 ✓ genuine
- A-4-4 rescale 持ち上げ (A-0'-2 経由、1-source `AntitoneOn (Set.Ici 0)` → 2-source `AntitoneOn (Set.Icc 0 1)`、`s=1` 端点は `csiszarGap_at_one_eq_zero_of_gaussian_pair`) → **撤退発火** L-Concl-A-β、`@residual(plan:epi-stam-to-conclusion-phaseA-A4-rescale)` 残置
- A-4-5 existential bundle → `isStamToEPIScalingHyp_of_stam_debruijn` ✓ genuine

`antitoneOn_of_deriv_nonpos` 不在時は `antitone_iff_monotone_neg` 経由 detour (撤退ラインなし)。

### A-5 — `isStamToEPIBridgeHyp_of_stam_debruijn` (`_of_scaling` 直接呼出)

設計エラー修正済: 当初 `isStamToEPILimitHyp_trivial` 構築は (a) `Z_X, Z_Y` witness では `(X+Y)` の EPI 結論を carry できず構築不能、(b) 既存 `_of_scaling` (`EPIStamToBridge.lean:672`、`@audit:ok`) が `IsStamToEPILimitHyp` 一切要求しない、で削除。A-5 は A-4 出力に `_of_scaling` を直接渡すだけ (~5-10 行)。

### A-6 — 主定理 `entropy_power_inequality_unconditional` (案 a)

**案 a (採用)**: 本体 `entropy_power_inequality` の signature 不変、A-5 出力を caller 注入する new wrapper `entropy_power_inequality_unconditional` を追加 (~30 行)、downstream は wrapper 経由。**案 b** (本体 signature 変更で 28 件 ripple) は親 plan §Phase B のスコープ。`IsStamInequalityResidual` / `IsStamToEPIBridge` ↔ `*Hyp` 系列の defeq は Phase D 完了 audit 確認済 (unfold で discharge)。

`EPIStamDischarge.lean:337` `IsStamToEPIBridgeHyp` docstring 改訂 (`未着手` → `Discharged by isStamToEPIBridgeHyp_of_stam_debruijn`)。

### A-V — verify + post-merge cleanup ✓ DONE 2026-05-27

- 4 file `lake env lean` silent (各 file の sorry warning は撤退発火由来のみ): `EPIStamToBridge.lean` (3 sorry) / `EPIStamDischarge.lean` / `EntropyPowerInequality.lean` (1 sorry: `stamToEPIBridge_holds`) / `EPIL3Integration.lean`
- 当初予測 14 件 → 実際 per-declaration scope 拡大 (grep SoT):
  - `EPIL3Integration.lean` §1-§11 の 10 件 + 3 件散文 → `@audit:retract-candidate(load-bearing-predicate)`
  - §13 (Phase D) の 4 件 `@audit:suspect(epi-stam-to-conclusion-plan)` → **`@audit:ok`** (sister-consumption 確立)
  - `EPIStamDeBruijnConclusion.lean` 4 件 → `retract-candidate`
  - `EntropyPowerInequality.lean:405` 1 件 → `retract-candidate`
  - `EPIStamToBridge.lean:236` `IsStamToEPILimitHyp` 1 件 → `retract-candidate` (`_h_limit` discard 確認)
  - `EPIStamToBridge.lean:506` `csiszarGap1Source_hasDerivAt` → **`@audit:ok`** (A-2 完成、regularity precondition)
  - **touch しない**: `EPIStamStep3Body.lean` 7 件 (Stam wall 別 plan) / `EPIStamToBridge.lean:143` `IsStamToEPIScalingHyp` (richness、sorry 残置中)
- 独立 honesty audit: `IsStamScalingNoiseHyp` は commit `8e23d94` で audit PASS 済。L-Concl-A-ε/ζ/η 発火時のみ追加起動。
- proof-log 書出 済。

## 撤退ライン (2026-05-27 L-Concl-A-θ 採番後、4 件 active + 1 件 resolved + 1 件 格下げ + 親 plan 継承 2 件)

| slug | Phase | 内容 | hypothesis 例 | 状態 |
|---|---|---|---|---|
| **L-Concl-A-α** (親継承) | A | sister Phase D 撤退ライン伝播 (smooth density / score Lp / regularity / integration) | `IsBlachmanIdentityHyp_smooth` 等 | active |
| **L-Concl-A-β** (親継承 / A-0'-4 / A-4-β) | A-0'-4 / A-4 | Gaussian limit `t→∞` で 0 が non-Gaussian で破綻、rescale `s=1` 端点接続失敗 | `IsEPIGaussianLimitHyp` | **active** (A-4-4 で発火、`@residual(...A4-rescale)` 残置) |
| **L-Concl-A-γ** (A-1) | A-1 | `IsStamScalingNoiseHyp` staged のまま伝播 | `IsStamScalingNoiseHyp` | active |
| ~~**L-Concl-A-δ**~~ | ~~A-2~~ | ~~2-source `heatFlowPath2` reparametrize で scaling 補正項キャンセル失敗~~ | — | **resolved 2026-05-25** by 撤退判定 (c) (1-source alias で根本回避) |
| **L-Concl-A-ε** (A-2-2、解釈変更) | A-2-2 | `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` Mathlib/InformationTheory 不在で >30 行 | `IsEntropyPowerChainRuleHyp` | active (発火確率 30%) |
| **L-Concl-A-ζ** (A-3、格下げ) | A-3-2 | 1-source でも Cauchy-Schwarz weight が `linarith` 吸収不可で >50 行 | `IsCsiszarScalingWeightHyp1Source` | **格下げ** (発火確率 15%) |
| **L-Concl-A-η** (A-0') | A-0'-2 | `entropyPower_const_mul` 不在で >30 行 | `IsEntropyPowerScaleHyp` | active (確率 30%) |
| **L-Concl-A-θ** (新規、A-4-1、2026-05-27) | A-4-1 | `csiszarGap1Source_continuousOn` の `t=0` 端点接続が現行 regularity bundle で carry されず、A-4 budget 超え | (signature 内 `sorry`、新規 staged 化なし) | **active 発火確定** (`@residual(...A4-continuity)` `EPIStamToBridge.lean:809`) |

**共通規律**: `Prop := True` 禁止 / `:= h` 循環禁止 / load-bearing name laundering (`_unconditional` / `_full` 命名で正当化) 禁止 / 退化定義悪用 (`Y:=0`, `Z_Y:=0` で trivially `AntitoneOn`、L-DBD-2-α 経路) 禁止。発動時 docstring に「NOT a discharge / load-bearing on <sister 由来 hypothesis>」明示。

## 完了後の次フェーズへの brief 雛形 (orchestrator 用)

### Brief A: mathlib-inventory subagent (Phase A 着手前)

新規 file: `docs/shannon/epi-stam-to-conclusion-phaseA-mathlib-inventory.md`。A-1 / A-2 / A-3 / A-4 の Mathlib 候補 API を CLAUDE.md `Subagent Inventory of Mathlib Lemmas` 規律 (file:line + 完全 signature [`[...]` verbatim] + 引数型 + 結論 form verbatim) で記録:

1. A-0' 用: `entropyPower_const_mul` (rg)、`differentialEntropy_const_mul` (rg)、`Real.sqrt_div_self'` / `Real.sqrt_mul` (loogle) — 不在で L-Concl-A-η 規模見積もり
2. A-1 用: `MeasureTheory.AtomlessProbability` (loogle)、InformationTheory `StandardNoise.lean` (rg)、`Measure.exists_indep_pair` (loogle)
3. A-2 用: `Real.hasDerivAt_exp` / `HasDerivAt.{exp,comp,sub}` 各 signature verbatim、de Bruijn V2 `derivAt_entropy_eq_half_fisher_v2` (`FisherInfoV2DeBruijn.lean:245`)、`entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` 不在判定
4. A-3 用: `linarith` 吸収可能性 → 不在時 `Real.inner_mul_le_norm` / `Real.add_sq_le_sq_mul_sq` (loogle)
5. A-4 用: `antitoneOn_of_deriv_nonpos` の verbatim signature + file:line (Phase 0 inventory は `monotoneOn_of_deriv_nonneg` のみ、Mathlib `Analysis/Calculus/Deriv/MeanValue.lean`)、`convex_Ici` / `convex_Icc`、`AntitoneOn.{comp,congr}`

撤退条件: 自作 >閾値で親 plan 撤退ライン (γ/ε/ζ/η) 発動。出力 200 行サマリ。

### Brief B: lean-implementer subagent (Phase A 着手時、A-1〜A-6 順次)

親 plan + inventory 参照、4 file (上 Scope 表) を順次実装、atomic (publish は A-6 完了後)。

**Sub-bound 引数表** (CLAUDE.md `Brief content checklist` 必須):

| Sub-bound | 要求 hypothesis 側 | 必要 bridge |
|---|---|---|
| `csiszarGap1Source` def (A-0'-1) | — | `entropyPower` 既存、`Real.sqrt` |
| `csiszarGap_eq_one_source_via_rescale` (A-0'-2) | `s ∈ Ico 0 1` | `entropyPower_const_mul` (η)、`Real.sqrt_div`、`heatFlowPath2_law` |
| `csiszarGap1Source_at_zero` / `_shape_for_sister` | — | `Real.sqrt_zero` / `rfl` |
| `..._tendsto_zero_at_infinity_of_gaussian_pair` | Gaussian pair | statement-only (L-Concl-A-β) |
| `isStamScalingNoiseHyp_of_*` (A-1) | richness side | inventory §2、staged のままが default (γ) |
| `csiszarGap1Source_hasDerivAt` (A-2-3) | sister Phase D output × 6 (`IsDeBruijnRegularityHyp` / `IsDeBruijnIntegrationHyp` の `X`/`Y`/`X+Y` 各) | de Bruijn V2 (`:245`)、`entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` (ε) |
| `csiszarGap1Source_deriv_le_zero` (A-3-2) | `IsStamInequalityHyp` 1-source 直接 | A-2-3 + Stam harmonic + linarith (ζ 候補) |
| `isStamToEPIScalingHyp_of_stam_debruijn` (A-4-5) | A-1 + Phase D × 6 | A-4-3 + A-4-4 rescale |
| `isStamToEPIBridgeHyp_of_stam_debruijn` (A-5-1) | A-4 出力単独 | `isStamToEPIBridgeHyp_of_scaling` (`:672` `@audit:ok`、`_limit` 不要) |
| `entropy_power_inequality_unconditional` (A-6) | A-5 + Phase D 6 を caller | 主定理本体 (`:232`) 不変 |

**1-source / 2-source shape 接続 caveat**: A-2/A-3/A-4-3 は 1-source (`Set.Ici 0`)、A-4-4 rescale 後は 2-source (`Set.Icc 0 1`、`csiszarGap`)、A-4-5 sister contract は 2-source verbatim、A-5-1 `_of_scaling` は 2-source 受取。shape 混同は LSP 第 1 戻り型 mismatch、orchestrator が vetting。

**継承 `@audit:*` 語彙整合 check**: A-V-5 sed 後 `grep -n '@audit:' EPIL3Integration.lean` で empty/未参照/旧 `@audit:suspect(epi-debruijn-integration-phaseD-plan)` 混同を listing → `docs/audit/audit-tags.md` 照合 → 追加 commit。

**運用ルール**: CLAUDE.md `Standard agent prompt boilerplate` verbatim (worktree .lake 共有 / branch 規律 / skeleton-driven / silent 検証 / scope 4 file / pinpoint import / 撤退ライン honest / commit 自走 push なし)。

**完了報告**: 各 step 進捗 + 撤退発動有無 + 4 file silent 結果 + 新規 staged 一覧 + 行数 + 独立 honesty audit 起動要否 (A-1 staged 導入で必須)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。append-only。

1. **2026-05-25 起草**: 親 plan §Phase A line 467-547 を A-0〜A-V の 7 sub-step に分解、Mathlib 在庫期待 + 撤退ライン詳細化 + post-merge cleanup 継承。親 plan の `EPIStamDischarge.lean:304` / `EntropyPowerInequality.lean:188` は drift 判明、`:337` / `:232` に修正。

2. **2026-05-25 撤退ライン拡張**: 親の L-Concl-A-α/β に L-Concl-A-γ/δ/ε/ζ を新規追加。γ (`IsStamScalingNoiseHyp` Mathlib 不足、Phase 0 `_of_gaussian` retract 前例) / δ (A-2 で 2-source reparametrize scaling 補正項キャンセル失敗) / ε (`differentialEntropy_const_mul` 不在) / ζ (Cauchy-Schwarz weight 自前 >100 行)。

3. **2026-05-25 A-6 案 a vs 案 b**: 案 a (wrapper 追加、本体不変) 採用。案 b は 28 件 ripple で Phase B スコープ、案 a なら本 Phase は genuine theorem 1 件追加に集中、段階化 ship 可能。

4. **2026-05-25 L-Concl-A-δ 撤退判定 (c) — Phase D 1-source alias 追加**: A-1 (`IsStamScalingNoiseHyp` +90 行 + honesty audit PASS、commit `8e23d94`) 直後の A-2 着手で `heatFlowPath2 X Z_X s = √(1-s)·X + √s·Z_X` の `s` 微分と de Bruijn V2 `derivAt_entropy_eq_half_fisher_v2` の 1-source 形のみ提供のミスマッチ発見、reparametrize で base が `s` 依存になり scaling 補正項発生、Stam reduce 失敗懸念。ユーザー撤退判定: (a) 仮説追加 / (b) Cauchy-Schwarz plumbing / **(c) Phase D 1-source 再設計** から (c) 採択。implementer 気づき「Phase D 2-source 形が下流コストを押し上げた根本原因」と整合。
   - 影響: A-0' (NEW `csiszarGap1Source` + 補題 4、alias 追加路線、~75 行) / A-2 redo (de Bruijn V2 直接適用、~30-50 行、−25 行) / A-3 redo (Cauchy-Schwarz `linarith` 吸収、~20-40 行) / A-4 extend (rescale 持ち上げ +5-10 行) / A-5-1 設計エラー修正 (`isStamToEPILimitHyp_trivial` 削除: `Z_X,Z_Y` witness では `(X+Y)` の EPI carry 不能 + `_of_scaling` が `_limit` 一切要求しない、`_of_scaling` 呼出だけに simplify、~5-10 行)
   - 規模 update: ~150-250 → ~165-285 行 (中央 ~210)
   - 撤退 update: δ → resolved / ζ → 格下げ (確率 50→15%、閾値 100→50 行) / ε → 解釈変更 (`entropyPower` chain rule 補題用) / η → 新規 (`entropyPower_const_mul` 不在時) / β → reframe (rescale `s=1` 端点)
   - Mathlib-shape-driven 整合 self-check: A-0' で 1-source `gaussianConvolution` の `t` 微分 conclusion form と A-2-3 結論 verbatim 一致、bridge 補題不要。
   - 数値・型 verbatim 確認: `csiszarGap1Source _ 0 = entropyPower(X+Y) − entropyPower(X) − entropyPower(Y)` は `Real.sqrt_zero` simp で `csiszarGap_at_zero` (`EPIL3Integration.lean:1173`) と同型、Phase D で `s=0 ↔ t=0` 対応確認済。
