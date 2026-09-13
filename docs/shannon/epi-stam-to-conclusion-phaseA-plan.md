# EPI Stam → conclusion Phase A: Stam + de Bruijn 合流 (Csiszár scaling) サブ計画

**Status**: CLOSED ✅ / 履歴記録 — 本 plan の Csiszár-scaling route は放棄され、親は 3-noise lift + two-time route に載せ替え済。当時「完了」とした成果物は現在 HEAD にない (下の ⚠ ブロック)。一般 EPI 自体は別ルートで無条件に閉じている (`entropyPowerExt_add_ge`)。

> **⚠ SUPERSEDED (2026-06-09) — 以降の本文全体は履歴記録であって、現在の進捗ではない**:
> 本 sub-plan が 2026-05-27 に「A-1〜A-V 完了」とした内容は **difference-form / Csiszár-scaling route 固有**で、
> 親 `epi-stam-to-conclusion-plan.md` は判断ログ #5 で **3-noise lift + two-time route** に載せ替え済
> (sum-instance 𝒩(0,2) の uninhabitable 構造制約)。以下の Scope / Phase 詳細 / 撤退ライン / 判断ログは
> 当時の route 設計をそのまま残したもので、✓ や行番号を現状の主張として読んではならない。
>
> **当時の成果物は HEAD に残っていない。** 本文が名前を挙げる次は、いずれも現在 `rg` で 0 件:
> `csiszarGap` / `csiszarGap1Source` とその補題群 (`_at_zero` / `_hasDerivAt` / `_continuousOn` /
> `_differentiableOn_interior` / `_deriv_le_zero` / `_shape_for_sister` / `_eq_one_source_via_rescale` /
> `_tendsto_zero_at_infinity_of_gaussian_pair` / `csiszarGap_at_one_eq_zero_of_gaussian_pair`)、
> `heatFlowPath2` / `heatFlowPath2_law`、`derivAt_entropy_eq_half_fisher_v2`、
> `IsStamScalingNoiseHyp` (commit `4cd6b12` で削除、joint-indep は caller 側 5-tuple `iIndepFun` inline 自己導出へ)、
> `IsStamToEPIScalingHyp` / `isStamToEPIScalingHyp_of_stam_debruijn`、`IsStamToEPILimitHyp`、
> `isStamToEPIBridgeHyp_of_scaling` / `isStamToEPIBridgeHyp_of_stam_debruijn`、`stamToEPIBridge_holds`、
> `entropy_power_inequality` / `entropy_power_inequality_unconditional`、`IsStamInequalityResidual` / `IsStamToEPIBridge`。
> **`IsDeBruijnIntegrationHyp` も削除済** — 非固定の `∃ fPath` 形だったため撤回され、
> 積分形の恒等式は `FisherInfo.debruijnIntegrationIdentity_holds` (密度パス固定) に一本化。
> 生存しているのは `IsStamInequalityHyp` / `IsDeBruijnRegularityHyp` / `IsStamToEPIBridgeHyp` /
> `entropyPower_hasDerivAt_of_diffEnt_hasDerivAt` など一部だけで、file も `InformationTheory/Shannon/EPI/**` へ
> 再編済。本文の `<file>.lean:<行>` は当時の座標であり、**在否と sorry の有無は都度 `rg` /
> `#print axioms` で引き直す** (plan 散文は再導出の代わりにならない)。
>
> **Stam ⇒ EPI の現状 (cold session がここから始めるとき)**: `IsStamToEPIBridgeHyp X Y P` は定義上
> `IsStamInequalityHyp → IsEntropyPowerInequalityHypothesis` で、後件は EPI の結論そのもの。HEAD の producer は
> いずれも EPI を別ルートで出して Stam の前件を捨てており、**Stam ⇒ EPI の導出を実行している宣言は
> in-tree に無い**。一般 EPI 自体は `entropyPowerExt_add_ge` (可測性と独立性のみ) として無条件に閉じている。
> bridge wrapper 群は `@audit:retract-candidate(load-bearing-predicate)` へ格下げ + `@[entry_point]` 除去済で、
> **この判断の SoT はコード側のタグと docstring** (`InformationTheory/Shannon/EPI/Stam/` を `rg`)。
>
> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §要点
> **Created**: 2026-05-25 (Phase D 合流 commit `c0edbe1` 直後)
> **当時の作業 commit** (履歴は git 側): `c0edbe1` (A-0') / `8e23d94` (A-1) / `d3ac59f` (A-4) /
> `1bd3866` (A-5) / `3db3a9e` (A-6)

## Position

- 親 sub-plan: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §要点 (親も CLOSED)
- 上流入力 (Phase D 完了済): [`epi-stam-discharge-plan.md`](epi-stam-discharge-plan.md) / [`epi-debruijn-integration-phaseD-plan.md`](epi-debruijn-integration-phaseD-plan.md) (commit `c0edbe1`)
- 当時の下流目標: 主定理 `entropy_power_inequality` の hypothesis-free 化 → 親 plan §Phase B (その主定理は現在 HEAD にない)

## Motivation

Phase 0 で `IsStamToEPIScalingHyp` (`EPIStamToBridge.lean:202-216`) を `∃ Z_X Z_Y, ... ∧ AntitoneOn gap (Set.Icc 0 1)` 形に refactor、Phase D で sister `csiszarGap` (`EPIL3Integration.lean:1160-1164`) が verbatim 同形で publish、`csiszarGap_shape_for_sister` (`:1279-1287`) `rfl` で接続。本 Phase A の狙いは、この 2 handoff を消費して **`AntitoneOn (csiszarGap ...) (Set.Icc 0 1)` を Stam + de Bruijn から genuine 構築**することだった (以下 5 項はいずれも当時の計画で、現在それを実現している宣言は無い):

1. path-derivative `d/ds (csiszarGap _) ≤ 0` (de Bruijn V2 + Stam)
2. `antitoneOn_of_deriv_nonpos` で `AntitoneOn`
3. existential witness `(Z_X, Z_Y)` と bundle → `isStamToEPIScalingHyp_of_stam_debruijn`
4. 既存 `isStamToEPIBridgeHyp_of_scaling` (`EPIStamToBridge.lean:672`、`IsStamToEPILimitHyp` 不要) 経由で `IsStamToEPIBridgeHyp` genuine 化
5. 主定理を hypothesis-free 化 (案 a wrapper)

verbatim 確認した前提コード位置: `DifferentialEntropy.lean:147` / `HeatFlowPath.lean:49-58` / `EPIStamToBridge.lean:210-216,672` / `EPIL3Integration.lean:1160-1164,1194-1215,1279-1287` / `EPIStamDischarge.lean:97-104,193-228,258-268,337-339` / `EntropyPowerInequality.lean:80,187-205,232-240,270-301`。`IsStamInequalityResidual` / `IsStamToEPIBridge` は `*Hyp` 系列と defeq (`fisherInfoOfMeasureV2_def` 経由)。

## Scope (当時の 4 file — いずれも現在の path ではない)

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
  isStamToEPIBridgeHyp_of_scaling (当時 Phase 0 で audit 済とされた、IsStamToEPILimitHyp 不要)
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

当時は A-1〜A-V を完了扱いとし、A-4-1 / A-4-4 のみ撤退発火で `@residual(plan:...-A4-continuity/-rescale)` を残置した
(→ L-Concl-A-θ / β)。**その残置 sorry も担い手の宣言も、当時の proof-log も現在は存在しない** — 本 plan の slug を
名乗る `@residual` がコードに残っていないことは `rg` で引ける。route ごと放棄されたため、closure 対象も無い。

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

### A-4 — `AntitoneOn` 構成 + rescale 持ち上げ + `IsStamToEPIScalingHyp` 構成

- A-4-1 `csiszarGap1Source_continuousOn` (`Set.Ici 0`、`t=0` 端点は A-0'-3 closed form) → 撤退発火 L-Concl-A-θ (`entropyPower ∘ P.map` の `√t → 0` continuity が Lebesgue-dominated-convergence machinery 要求、A-4 budget 超過)
- A-4-4 rescale 持ち上げ (A-0'-2 経由、1-source `AntitoneOn (Set.Ici 0)` → 2-source `AntitoneOn (Set.Icc 0 1)`、`s=1` 端点は `csiszarGap_at_one_eq_zero_of_gaussian_pair`) → 撤退発火 L-Concl-A-β
- A-4-2 `csiszarGap1Source_differentiableOn_interior` / A-4-3 `antitoneOn_of_deriv_nonpos` 適用 / A-4-5 existential bundle → `isStamToEPIScalingHyp_of_stam_debruijn`: 当時はここまで組んだとされた (いずれも現在 HEAD になし)

`antitoneOn_of_deriv_nonpos` 不在時は `antitone_iff_monotone_neg` 経由 detour (撤退ラインなし)。

### A-5 — `isStamToEPIBridgeHyp_of_stam_debruijn` (`_of_scaling` 直接呼出)

設計エラー修正済: 当初 `isStamToEPILimitHyp_trivial` 構築は (a) `Z_X, Z_Y` witness では `(X+Y)` の EPI 結論を carry できず構築不能、(b) 当時 audit 済とされた既存 `_of_scaling` が `IsStamToEPILimitHyp` を一切要求しない、で削除。A-5 は A-4 出力に `_of_scaling` を直接渡すだけ (~5-10 行)。

### A-6 — 主定理 `entropy_power_inequality_unconditional` (案 a)

**案 a (採用)**: 本体 `entropy_power_inequality` の signature 不変、A-5 出力を caller 注入する new wrapper `entropy_power_inequality_unconditional` を追加 (~30 行)、downstream は wrapper 経由。**案 b** (本体 signature 変更で 28 件 ripple) は親 plan §Phase B のスコープ。`IsStamInequalityResidual` / `IsStamToEPIBridge` ↔ `*Hyp` 系列の defeq は Phase D 完了 audit 確認済 (unfold で discharge)。

当時はあわせて `IsStamToEPIBridgeHyp` の docstring を「未着手」→「`isStamToEPIBridgeHyp_of_stam_debruijn` で
discharge 済」に書き換えた。**現在の docstring はこれと逆のことを述べている** (producer は EPI を別ルートで出して
Stam の前件を捨てる、と明記) → 冒頭 ⚠ ブロックの「Stam ⇒ EPI の現状」。

### A-V — verify + post-merge cleanup (当時)

当時は 4 file を `lake env lean` silent にしたうえで、EPIL3Integration / EPIStamToBridge / EPIStamDischarge /
EPIStamDeBruijnConclusion / EntropyPowerInequality の per-declaration `@audit:*` を一括書換し、うち数件を
`@audit:ok` に上げた。**その分類はその後の独立 honesty 監査で再判定されている**ので、ここに書かれた
`@audit:ok` / `retract-candidate` の内訳を現状として引かないこと — タグの現況はコード側が SoT
(`InformationTheory/Shannon/EPI/` を `rg '@audit:'`)。

## 撤退ライン (当時の採番。slug は他文書が参照しうるので番号ごと残す)

「状態」列は 2026-05-27 時点の評価であって現況ではない。route ごと放棄されたため、**ここに書かれた
active / 発火確定はいずれも現在 closure 対象ではなく**、担い手の `@residual` もコードに残っていない。

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

## 当時の subagent brief 雛形 — 撤去済

route 放棄にともない、mathlib-inventory / lean-implementer 向けの brief 雛形 (Sub-bound 引数表、
1-source / 2-source shape 接続 caveat、`@audit:*` 語彙整合 check) は本文から落とした。表が名指していた
宣言・file はすべて上の ⚠ ブロックの「HEAD に残っていない」側にあり、そのまま発注できる内容ではない。
本文は git が履歴を持つ。当時の在庫調査だけは
[`epi-stam-to-conclusion-phaseA-mathlib-inventory.md`](epi-stam-to-conclusion-phaseA-mathlib-inventory.md)
に残っている。

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
