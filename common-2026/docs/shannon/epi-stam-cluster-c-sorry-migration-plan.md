# EPI-Stam Cluster C — true sorry-based migration plan (Path 1)

> **Parent**: [`epi-moonshot-plan.md`](epi-moonshot-plan.md)
> + [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md)
> + [`epi-stam-to-conclusion-phaseA-plan.md`](epi-stam-to-conclusion-phaseA-plan.md)
> + [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md)
>
> **Sister precedent**:
> [`awgn-m5-sorry-migration-plan.md`](awgn-m5-sorry-migration-plan.md)
> (AWGN M5、同型 Path 1。Phase 3-β achievability が完全 proof done に到達)
> + commit [`34e17bc`](../../) EPI-Stam Cluster C+D の Tier 4 → Tier 3
> bookkeeping migration (本 plan の **入口**)。
>
> **Predecessor (bookkeeping-only)**: commit `34e17bc` が 4 file
> (`EPIL3Integration` / `EPIStamDischarge` / `EPIStamToBridge` /
> `EntropyPowerInequality`) の load-bearing predicate を **signature 改変なし** で
> legacy `@audit:staged` / `@audit:suspect` → `@audit:retract-candidate(load-bearing-predicate)`
> (Tier 3 bookkeeping) に移行済み。
>
> 本 plan はその scope を **意図的に超え** て、declaration-level load-bearing
> predicate を Honesty 階層 Tier 3 (`@audit:retract-candidate(load-bearing-predicate)`、
> bookkeeping) → **Tier 2** (`sorry` + `@residual(<class>:<slug>)`、新規実装の唯一の
> honest 撤退口) に格上げする。Path 1 = 「**真の sorry-based migration**」。
>
> `@residual(plan:...)` slug は本 plan filename stem
> `epi-stam-cluster-c-sorry-migration-plan` と一致。

## 進捗

- [x] Phase 0 — verbatim 棚卸し + 既存 shared wall 流用判定 + Approach 確定 ✅ (2026-05-28、判断ログ 1〜5 参照)
- [x] Phase 1 — Wall name register 確認 ✅ (`epi-noise-extension` 不採用、デフォルト plan slug 採用、`docs/audit/audit-tags.md` 無変更、判断ログ 6 参照)
- [x] Phase 2 — shared sorry 補題の補充 ✅ (新規 shared sorry 補題 4 件補充、新規 wall file 0 / 新規 wall name 0、判断ログ 6 参照)
- [x] Phase 3-α — pipeline bundle の `bridge` field 非 load-bearing 化 (L-EPISC-3-α 採用) + consumer 書換 (`EPIL3Integration`、Group 1 = Agent X) ✅ (commit `eeea99b`)
- [x] Phase 3-β — Stam-scaling 系 predicate の wall 委任 + consumer 書換 (`EPIStamToBridge`、Group 2 = Agent Y) ✅ (commit `e95b3e2`)
- [x] Phase 3-γ — de Bruijn regularity / integration predicate の wall 委任 (`EPIStamDischarge` + `FisherInfoV2DeBruijn`、Group 3 = Agent Z) ✅ (commit `487547f`)
- [x] Phase 3-δ — empty-consumers predicate の純削除 (3 件: #4 #17 #19) ✅ (Group 1/2 に内包、判断ログ 6 参照)
- [x] Phase V — 検証 + honesty audit + roadmap update ✅ (独立 honesty audit commit `4b3d165` 全 8 項 OK / DEFECT 0、判断ログ 7 参照)

> **Phase 0 確定 scope = 6 file** (brief の 4 file から拡張)。
> `EPIStamDeBruijnConclusion.lean` **in** + `EPIStamInequalityBody.lean` **in**
> (両 file が `IsEPIL3IntegratedPipeline` 構成子を持つ)。bundle は **削除せず**
> `bridge` field 非 load-bearing 化 (L-EPISC-3-α 採用)。並列分割は下記
> 「Phase 3 並列実装ルーティング表」参照。

## Context — verbatim 棚卸し (2026-05-28、`34e17bc` 時点コード)

`rg -n '@audit:retract-candidate\(load-bearing-predicate'` は対象 4 file で **計 25 hit** を
返すが、**大半は docstring/narrative の文字列リテラル mention** であり declaration-level
tag ではない。各 hit を Read で確認し、(a) declaration-level の load-bearing predicate /
consumer tag、(b) docstring/narrative の散文 mention、(c) `-empty-consumers` variant
(consumer 0、純削除候補) の 3 種に分離した。

### 表 A — declaration-level tag 一覧 (本 plan の移行対象)

`@audit:retract-candidate(load-bearing-predicate)` (-empty-consumers variant を含む) が
**実 declaration の docstring** に付いているもの。種別 / 既存タグ / consumer 数を verbatim
列挙。consumer 数は `rg -nc '<name>' InformationTheory/Shannon/` の全 file 合計 (hypothesis-form /
`.field` extract / 構成子 / docstring mention をまだ分離していない粗数。Phase 0-2 で分離)。

| # | file:line | declaration | 種別 | 移行 Route | consumer 粗数 (全 file 合計) |
|---|---|---|---|---|---|
| 1 | `EPIStamDischarge.lean:206` | `structure IsDeBruijnRegularityHyp` | de Bruijn heat-flow regularity bundle (load-bearing、genuine `HasDerivAt` content) | **B** (`wall:debruijn-integration`) | 50 (`EPIStamToBridge` 45 / `EPIStamDischarge` 3 / `EPIL3Integration` 2) |
| 2 | `EPIStamDischarge.lean:286` | `def IsDeBruijnIntegrationHyp` | de Bruijn 積分恒等式 `∃ fPath, ∫...` (Cover-Thomas 17.7.2、load-bearing) | **B** (`wall:debruijn-integration`) | 17 (`EPIStamDischarge` 11 / `EPIL3Integration` 4 / `EntropyPowerInequality` 2) |
| 3 | `EPIStamToBridge.lean:222` | `def IsStamToEPIScalingHyp` | `IsStamInequalityHyp → ∃ Z_X Z_Y, ... ∧ AntitoneOn ...` (Csiszár scaling、load-bearing) | **B** (`wall:csiszar`) | 24 (`EPIStamToBridge` 18 / `EPIL3Integration` 4 / `EPIStamDeBruijnConclusion` 1 / `HeatFlowPath` 1) |
| 4 | `EPIStamToBridge.lean:265` | `def IsStamToEPILimitHyp` | `∃ g1, g1 = 0 ∧ ...` (限界 hyp) | **A** (純削除候補) | 17 (`EPIStamToBridge` 17 のみ) |
| 5 | `EPIStamToBridge.lean:459` | `def IsStamScalingNoiseHyp` | `∃ Z_X Z_Y, Measurable ∧ ... ∧ IndepFun` (noise-extension richness、load-bearing) | **B** (`wall:csiszar` or `epi-n-dim`?) | 16 (`EPIStamToBridge` 16 のみ) |
| 6 | `EntropyPowerInequality.lean:416` | `theorem entropy_power_inequality_three_arg` | consumer (2 件 `IsEntropyPowerInequalityHypothesis` hyp を thread) | **C** (consumer 書換) | 7 (`EPIPlumbing` 3 / `EPIStamDischarge` 2 / `EPIL3Integration` 1 / 自 file 1) |
| 7 | `EPIL3Integration.lean:129` | `theorem epi_l3_of_integrated_pipeline` | `IsEPIL3IntegratedPipeline → L-EPI3` (bundle consumer) | **C** | (pipeline 系で集約、下記) |
| 8 | `EPIL3Integration.lean:147` | `theorem entropy_power_inequality_integrated` | pipeline consumer (main) | **C** | 同上 |
| 9 | `EPIL3Integration.lean:211` | `theorem entropy_power_inequality_log_form_integrated` | pipeline consumer | **C** | 同上 |
| 10 | `EPIL3Integration.lean:226` | `theorem entropy_power_inequality_exp_form_integrated` | pipeline consumer | **C** | 同上 |
| 11 | `EPIL3Integration.lean:242` | `theorem entropy_power_inequality_normalized_integrated` | pipeline consumer | **C** | 同上 |
| 12 | `EPIL3Integration.lean:259` | `theorem entropy_power_inequality_three_arg_integrated` | pipeline consumer (chain) | **C** | 同上 |
| 13 | `EPIL3Integration.lean:275` | `theorem entropy_power_inequality_four_arg_integrated` | pipeline consumer (chain) | **C** | 同上 |
| 14 | `EPIL3Integration.lean:327` | `theorem entropy_power_inequality_reduced` | pipeline consumer (hyp-reduced) | **C** | 同上 |
| 15 | `EPIL3Integration.lean:341` | `theorem entropy_power_inequality_exp_form_reduced` | pipeline consumer | **C** | 同上 |
| 16 | `EPIL3Integration.lean:401` | `theorem entropy_power_inequality_three_forms_equiv` | pipeline consumer (3 form 連言) | **C** | 同上 |
| 17 | `EPIL3Integration.lean:512` | `structure IsHeatFlowFamilyHyp` | heat-flow family regularity bundle | **A** (純削除、`-empty-consumers`) | 7 (`EPIL3Integration` 7 のみ、hypothesis-form **0**) |
| 18 | `EPIL3Integration.lean:971` | `theorem bounded_T_ftc_gaussian` | **genuine** bounded-T FTC (0 sorry、`@entry_point`) — tag は「feed 先 pipeline が load-bearing」を述べる bookkeeping、本体は honest | **(要再判定)** tag 妥当性 | 自 file 内のみ |
| 19 | `EPIL3Integration.lean:1607` | `def IsCsiszarGap1SourceTendsToZeroAtInfinity` | Csiszár tail bound `... → Tendsto ... atTop (𝓝 0)` | **A** (純削除、`-empty-consumers`) | 3 (`EPIL3Integration` 3 のみ、active consumer **0**) |

### 表 A' — consumer 精数 (Phase 0-2 分解結果、2026-05-28 verbatim)

表 A の「consumer 粗数」を 4 種に分解した。**hypothesis-form** = `(h : Pred ...)` を
引数に取る consumer (load-bearing、削除すると signature が壊れる) / **field** = structure
の field 型 / **construct** = 当該 predicate を結論型に持つ構成子 (`where`/`{...}`) /
**mention** = docstring の文字列リテラル。verbatim grep
(`rg -n '[(:] *(NS\.)?<Pred> '` + 各 hit を Read) で照合。

| # | declaration | hyp-form | field | construct | mention | 純削除可? | 確定 Route |
|---|---|---:|---:|---:|---:|---|---|
| 1 | `IsDeBruijnRegularityHyp` | **10** (`EPIStamToBridge` `h_reg_X`/`h_reg_Y` 等 :554/555/751/752/850/851/863/864/891/892) | 0 | 0 | 残 (docstring) | ✗ active load-bearing | **B** (`debruijnIdentityV2_holds`、regularity precond 残置) |
| 2 | `IsDeBruijnIntegrationHyp` | **0** (hyp-form 引数 0) | 0 | `isDeBruijnIntegrationHyp_at_zero` 等 self-file 構成子 | 残 | △ (consumer は構成子/自 file `∃` 使用) | **B** (積分形、L-EPISC-1-α 該当 — 後述) |
| 3 | `IsStamToEPIScalingHyp` | **2** (`EPIStamToBridge:292` `h_scaling`、`:1158` structure `IsEPIScalingDecomposedPipeline.scaling` field) | 1 | `isStamToEPIScalingHyp_of_stam_debruijn` (`@audit:ok`) | `EPIStamDeBruijnConclusion:115`、`HeatFlowPath:14` (docstring) | ✗ active | **B** (`AntitoneOn` → L-EPISC-2-β、新規 wall or phaseA-plan slug) |
| 4 | `IsStamToEPILimitHyp` | 4 だが **load-bearing 0** (`:293` `_h_limit` discard / `:1100`/`:1231` `h_limit` も `_of_scaling_limit` で `_` discard / `:1160` field) | 1 (`IsEPIScalingDecomposedPipeline.limit`) | `isStamToEPIBridgeHyp_of_scaling_limit` | 残 | ◯ docstring 自己申告 non-load-bearing | **A** 純削除 + `_limit` slot 除去 |
| 5 | `IsStamScalingNoiseHyp` | **3** (`EPIStamToBridge:978`/`:1070`/`:1201` `h_noise`) | 0 | `isStamScalingNoiseHyp_symm` (`@audit:ok`) | 残 | ✗ active load-bearing | **B** (noise-extension 壁、`csiszar` 不適 — 後述) |
| 6 | `entropy_power_inequality_three_arg` | (consumer 側、本体が 2 `IsEntropyPowerInequalityHypothesis` hyp を取る) | — | — | `EPIPlumbing:251`/`EPIStamDischarge:498` が body で呼出 | — | **C** (unconditional route 委任) |
| 7-16 | `IsEPIL3IntegratedPipeline` 消費系 | **14** (`EPIL3Integration:132/152/216/231/247/263/264/279/280/281/297/332/346/406`) | 2 field (`IsEPIL3IntegratedPipeline.{stam,bridge}`) | `_of_gaussian` `_of_stam_bridge` (EPIL3) / `isEPIL3IntegratedPipeline_of_stamDeBruijn` (Conclusion:210) / `isStamInequalityHyp_via_body_to_pipeline` (InequalityBody:405) | — | ✗ bundle 削除は多 file | **C** (`bridge` field 非 load-bearing 化、bundle 残置) |
| 17 | `IsHeatFlowFamilyHyp` | **0** | 0 | `isHeatFlowFamilyHyp_of_gaussian` (構成子のみ、witness 生成) | 残 (docstring) | ◯ 純削除 | **A** (`-empty-consumers`) |
| 18 | `bounded_T_ftc_gaussian` | (genuine theorem、body 0 sorry、`@entry_point`) | — | — | — | — | tag を `@audit:ok` に修正 (本体 honest、feed 先 bundle 残るが bridge 非 load-bearing 化後は tag 不要) |
| 19 | `IsCsiszarGap1SourceTendsToZeroAtInfinity` | **0** | 0 | 0 (構成子なし) | 残 (docstring) | ◯ 純削除 | **A** (`-empty-consumers`、`csiszar` 経路は rescale 代替) |

**純削除確定 3 件 (Route A)**: #4 #17 #19 — いずれも load-bearing hypothesis-form
consumer 0。#4 のみ `_of_scaling_limit` 構成子の `_limit` slot 除去が連動 (`EPIStamToBridge`
内、cross-file ではない)。

**declaration-level 実件数 = 19**。内訳:
- **`IsEPIL3IntegratedPipeline` 消費系 (#7-16、計 10)** — Route C。bundle structure
  `IsEPIL3IntegratedPipeline` (`EPIL3Integration.lean:112`、本 plan の中核) の
  load-bearing field `bridge : IsStamToEPIBridgeHyp` を thread する wrapper 群。
- **de Bruijn predicate 2 件 (#1, #2)** — Route B。既存 shared wall lemma
  `debruijnIdentityV2_holds` (下記) に委任。
- **Stam-scaling predicate 3 件 (#3, #4, #5)** — Route B / A。
- **empty-consumers 3 件 (#4, #17, #19)** — Route A 純削除候補
  (`IsStamToEPILimitHyp` は表 A で重複計上、下記 §Route A で確定)。
- **consumer-with-hyps 1 件 (#6)** — Route C。
- **genuine theorem 1 件 (#18)** — tag 妥当性の再判定対象。

### 表 B — narrative / 散文 mention (本 plan scope 外、削除も移行も不要)

| file:line | 文脈 | 分類根拠 |
|---|---|---|
| `EntropyPowerInequality.lean:350` | 既削除 `isStamToEPIBridge_of_epi` の retraction comment (0 consumer、2026-05-28 削除済) | declaration は既に存在しない。retraction 説明 prose |
| `EPIL3Integration.lean:466` | §12 section header の「14 wrapper migration」説明 prose | section comment、declaration docstring ではない |
| `EPIL3Integration.lean:477` | §12 section header tag「grep aggregate 用」と明記 | 自己申告で bookkeeping-only |
| `EPIL3Integration.lean:1028` | §13 Phase D closure note の migration 説明 prose | section comment |
| `EPIL3Integration.lean:1036` | 同上 (deprecation table 引用) | section comment |
| `EPIStamToBridge.lean:1056` | `isStamToEPIBridgeHyp_of_stam_debruijn` (`@audit:ok`) docstring 内の `IsStamToEPILimitHyp` 言及 (文字列リテラル) | 当該 theorem は `@audit:ok`、tag は引用 |
| `EPIStamDischarge.lean:151/183/226/271` | `@residual(wall:debruijn-integration)` への言及 prose | shared wall lemma 説明、tag mention |

### 表 C — 既に存在する shared wall lemma (Route B の流用先)

EPI-Stam family の Mathlib 壁は **既に shared sorry 補題化済み** であることが verbatim
確認された (AWGN M5 sister と最大の違い — AWGN では wall file を新設したが、EPI-Stam は
新設不要の見込み)。

| shared wall lemma | file:line | 既存タグ | 担当壁 |
|---|---|---|---|
| `theorem debruijnIdentityV2_holds` | `FisherInfoV2DeBruijn.lean:245` | `@residual(wall:debruijn-integration)`、body `sorry` | de Bruijn heat-flow identity |
| `theorem stamToEPIBridge_holds` | `EntropyPowerInequality.lean:223` | `@residual(plan:epi-stam-to-conclusion-plan)`、body `sorry` | Stam → EPI bridge coupling |

→ **`debruijnIdentityV2_holds` + `stamToEPIBridge_holds` の 2 補題が EPI-Stam family の
壁を既に集約している**。本 plan の Route B は「新規 wall lemma を書く」ではなく
「**既存 shared wall lemma を consumer body から呼ぶ**」になる見込み。Phase 0-3 で
各 predicate の「結論」が既存 wall lemma で discharge 可能か verbatim 照合する。

### 表 C' — Phase 0-4 既存 wall lemma 流用照合 (2026-05-28 verbatim、結論型 Read 済)

各 Route B predicate の「結論」を既存 2 wall lemma が直接供給できるか照合した。
verbatim 確認した結論型:

- `debruijnIdentityV2_holds` (`FisherInfoV2DeBruijn.lean:245`、`@residual(wall:debruijn-integration)`):
  結論 `HasDerivAt (fun s => differentialEntropy (P.map (gaussianConvolution X Z s))) ((1/2) * fisherInfoOfDensityReal h_reg.density_t) t`。
  引数 `(h_reg : IsRegularDeBruijnHypV2 X Z P t)` (regularity-only)。→ **per-time `HasDerivAt`** を返す。
- `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:223`、`@residual(plan:epi-stam-to-conclusion-plan)`):
  結論 `IsStamToEPIBridge X Y P` = `IsStamInequalityResidual X Y P → IsEntropyPowerInequalityHypothesis X Y P`。
  → **Stam residual → EPI 結論** の含意を返す。

| # | predicate | predicate の結論型 (verbatim) | 既存 wall で供給可? | 判定 |
|---|---|---|---|---|
| 1 | `IsDeBruijnRegularityHyp` (structure) | `reg_at : ∀ t > 0, IsRegularDeBruijnHypV2 X Z P t` 他 4 field の per-`t` `HasDerivAt`/`IntervalIntegrable` | **◯ 供給可** — `debruijnIdentityV2_holds X Z ht h_reg.reg_at` が per-`t` `HasDerivAt` を直接返す。整合 (`deBruijn_identity_v2:272` が既にこの pass-through を実演) | **L-EPISC-1-α 不発**。既存 wall で OK |
| 2 | `IsDeBruijnIntegrationHyp` (def `Prop`) | `∃ fPath, ∀..., h_target - h_X = ∫ t in Set.Ioo 0 T, (1/2)*(fisherInfoOfMeasureV2 ...).toReal ∂volume` | **✗ 供給不可** — wall は **per-time `HasDerivAt`** を返すのみ。**積分形 `∫...` は FTC (intervalIntegral) で per-time deriv を積分する bridge が別途必要**。Gaussian 限定なら `bounded_T_ftc_gaussian` (`EPIL3Integration:971`、body 0 sorry) が同型を実演するが一般 `X` では不在 | **L-EPISC-1-α 発火** → 新規 shared wall lemma `debruijnIntegrationIdentity_holds` (積分形に shape 合わせ) を Phase 2 で補充。wall name は既存 `debruijn-integration` 流用 (壁 0 増) |
| 3 | `IsStamToEPIScalingHyp` (def `Prop`) | `IsStamInequalityHyp → ∃ Z_X Z_Y, Measurable ∧ ... ∧ AntitoneOn (fun s => entropyPower(...) - ... - ...) (Set.Icc 0 1)` | **✗ 供給不可** — `stamToEPIBridge_holds` は `IsEntropyPowerInequalityHypothesis` を返し `AntitoneOn` ではない。`csiszarGap_antitoneOn_*` (Phase A、`@residual(plan:epi-stam-to-conclusion-phaseA-plan)`) が `AntitoneOn` 系を担当 | **L-EPISC-2-β 発火** → consumer body は `csiszarGap_antitoneOn_*` (phaseA-plan slug) 経由 or 新規 wall。slug は `epi-stam-to-conclusion-phaseA-plan` |
| 5 | `IsStamScalingNoiseHyp` (def `Prop`) | `∃ Z_X Z_Y, Measurable ∧ ... ∧ IndepFun Z_X Z_Y P` (noise-extension richness) | **✗ 供給不可** — docstring 自己申告: 「noise extension on arbitrary probability space」は Mathlib 0 件 (loogle/rg 確認済)、`csiszar` でも `debruijn-integration` でもない別の壁。closure plan = `epi-stam-to-conclusion-phaseA-plan` L-Concl-A-γ | **新規 wall lemma 補充要** (`csiszar` 流用不適、judgement 下記 Phase 1-3) |

**0-4 結論 (Phase 2 への確定記入)**:
- #1 → 既存 `debruijnIdentityV2_holds` 流用、補充不要。
- #2 → **新規 shared wall lemma `debruijnIntegrationIdentity_holds` (積分形) を補充要** (wall name `debruijn-integration` 流用、壁数 0 増)。
- #3 → 既存 Phase A `csiszarGap_antitoneOn_*` 経路を consumer body から呼ぶ (新規補題不要、plan slug `epi-stam-to-conclusion-phaseA-plan`)。
- #5 → **新規 shared wall lemma `stamScalingNoise_exists` (noise-extension 存在) を補充要**。wall name は `csiszar` 不適 — 新規 wall 候補 `epi-noise-extension` を `docs/audit/audit-tags.md` Proposed 表に提案 (promote は後続)。当面 plan slug `epi-stam-to-conclusion-phaseA-plan` (L-Concl-A-γ) 流用も可。

→ **新規 shared wall 補題は計 2 件補充要** (#2 積分形 + #5 noise-extension)。新規 wall **name** 追加は #5 の `epi-noise-extension` 候補 1 件のみ (Proposed 表、promote 留保)。新規 wall **file** 新設は不要見込み — #2 は `FisherInfoV2DeBruijn.lean` (既存 wall file)、#5 は `EPIStamToBridge.lean` 内 or `EntropyPowerInequality.lean` に補充可 (L-EPISC-4-γ 不発見込み、import cycle は下記 0-5 で否定済)。

### 表 C'' — Phase 0-5 import 依存方向照合 (2026-05-28 verbatim、cycle check)

InformationTheory 内 import を verbatim 確認 (各 file の `^import` 行を Read)。依存 DAG (上流 → 下流):

```
FisherInfoV2  →  FisherInfoV2DeBruijn  (debruijnIdentityV2_holds 提供)
              ↘  EntropyPowerInequality (stamToEPIBridge_holds 提供)
                    →  EPIStamDischarge  →  EPIL3Integration  →  EPIStamToBridge  →  EPIStamDeBruijnConclusion
                    →  EPIPlumbing      ↗                         ↑ EPIStamInequalityBody (IsEPIL3IntegratedPipeline 構成子)
HeatFlowPath (最上流、InformationTheory 内 import は Meta.EntryPoint のみ)
```

| consumer file | `debruijnIdentityV2_holds` 提供 file (`FisherInfoV2DeBruijn`) を import 済? | `stamToEPIBridge_holds` 提供 file (`EntropyPowerInequality`) を import 済? | cycle リスク |
|---|---|---|---|
| `EPIStamDischarge` | ◯ (import line 5) | ◯ (line 2) | なし |
| `EPIL3Integration` | ◯ (line 5) | ◯ (line 2) | なし |
| `EPIStamDeBruijnConclusion` | ◯ (line 9) | ◯ (line 2) | なし |
| `EntropyPowerInequality` | **✗ 未 import** | (自 file) | `FisherInfoV2DeBruijn` を import 追加は cycle になる? → `FisherInfoV2DeBruijn` は `EntropyPowerInequality` を import **していない** ので逆方向追加は cycle にならない。ただし base file の import policy 上、追加は避けたい (docstring `IsStamInequalityResidual:188` が「base file free of import cycle through FisherInfoV2DeBruijn」と明示) |
| `EPIStamToBridge` | **✗ 未 import** | ◯ (line 2) | `FisherInfoV2DeBruijn` を import 追加 → cycle check: `FisherInfoV2DeBruijn` は `FisherInfoV2` のみ依存、`EPIStamToBridge` を import していない → **追加可、cycle にならない**。ただし #1 は既に `IsDeBruijnRegularityHyp` 経由 (`EPIStamDischarge` から transitive) で wall に到達できるため、`EPIStamToBridge` 内で wall を直接呼ぶ必要は薄い |
| `EPIPlumbing` | ✗ (#6 three_arg consumer のみ、wall 直接呼出不要) | ◯ (line 2) | なし |
| `EPIStamInequalityBody` | (要確認: scope 内、bundle 構成子 :405 のみ) | (要確認) | bundle 構成子書換のみ、wall 直接呼出は最小 |

**0-5 結論**: `debruijnIdentityV2_holds` / `stamToEPIBridge_holds` を呼ぶ主たる consumer file
(`EPIStamDischarge` / `EPIL3Integration` / `EPIStamDeBruijnConclusion`) は **既に両 wall 提供 file
を import 済**。import cycle は発生しない。例外: `EPIStamToBridge` は `FisherInfoV2DeBruijn` 未 import
だが、#5 noise-extension 補題を **`EPIStamToBridge.lean` 自身に集約** すれば import 追加不要
(L-EPISC-4-γ 不発、新規 wall file 不要)。`EntropyPowerInequality` base file に `FisherInfoV2DeBruijn`
を import 追加するのは avoid (#2 積分形補題は `FisherInfoV2DeBruijn.lean` 側に置く)。

### 表 D — 周辺 predicate (本 plan の前提、移行 scope 外だが Route 設計の土台)

| predicate | file:line | タグ | 役割 |
|---|---|---|---|
| `structure IsEPIL3IntegratedPipeline` | `EPIL3Integration.lean:112` | (タグ無し、本体は `{ stam, bridge }` の 2 field) | #7-16 が thread する bundle。`bridge : IsStamToEPIBridgeHyp` が load-bearing |
| `def IsStamInequalityHyp` | `EPIStamDischarge.lean:100` | (genuine Fisher-info Stam 形) | bundle `.stam` field の型 |
| `def IsStamToEPIBridgeHyp` | `EPIStamDischarge.lean:365` | `@audit:ok` | bundle `.bridge` field の型。`stamToEPIBridge_holds` で discharge 可能 |
| `def IsStamInequalityResidual` | `EntropyPowerInequality.lean:190` | (`IsStamInequalityHyp` と defeq) | non-circular residual 形 |

## Context — consumer graph + blast radius (verbatim、要 Phase 0 精査)

`rg -nc '<predname>' InformationTheory/Shannon/` (2026-05-28) で確認した **重大な scope 境界
findings**:

```
EPIStamDischarge.lean  (de Bruijn predicate 2 件: #1 #2)
EntropyPowerInequality.lean (stamToEPIBridge_holds + three_arg #6)
EPIStamToBridge.lean   (Stam-scaling predicate 3 件: #3 #4 #5)
EPIL3Integration.lean  (pipeline bundle + consumer 10 件 #7-16 + empty 2 件 #17 #19 + genuine #18)
   ↑ ここまでが brief の 4-file scope
─────────────────────────────────────────────────
EPIStamDeBruijnConclusion.lean  ★ brief scope 外だが Cluster C consumer graph 内
   - isStamInequalityHyp_of_primitives (164)            @audit:retract-candidate(load-bearing-predicate)
   - isStamInequalityHyp_of_stamDeBruijn (197)          同上
   - isEPIL3IntegratedPipeline_of_stamDeBruijn (210)    同上 (IsEPIL3IntegratedPipeline 構成子)
   - entropy_power_inequality_via_stamDeBruijn (227)    同上 (pipeline consumer)
   - structure IsEPIStamDeBruijnPipeline (181)          (bundle、IsEPIL3IntegratedPipeline へ橋渡し)
EPIStamInequalityBody.lean   (IsEPIL3IntegratedPipeline 1 mention)
HeatFlowPath.lean            (IsStamToEPIScalingHyp 1 mention)
EPIPlumbing.lean             (entropy_power_inequality_three_arg 3 mention)
```

→ **brief の「4 file」は移行対象 declaration の **存在場所** としては正しいが、
predicate 削除 / consumer 書換の **blast radius** は最低でも `EPIStamDeBruijnConclusion.lean`
+ `EPIStamInequalityBody.lean` + `HeatFlowPath.lean` + `EPIPlumbing.lean` に及ぶ**
(各 file が pipeline bundle / Stam-scaling / three_arg を thread しているため)。
特に `EPIStamDeBruijnConclusion.lean` は **同型の 4 declaration-level load-bearing tag**
を持ち、`IsEPIL3IntegratedPipeline` の構成子 (`isEPIL3IntegratedPipeline_of_stamDeBruijn`)
を提供する **Cluster C の不可分の一部**。これを scope 外に置くと pipeline bundle 削除が
不可能になる (構成子が孤児化)。**Phase 0 で scope 拡張判定** (下記 L-EPISC-0-honest-defect)。

## ゴール / Approach

### 全体方針 — Tier 3 → Tier 2 への 3 段分類 (AWGN M5 と同型、ただし wall は既存流用)

CLAUDE.md「sorry を書けない箇所での対処順序」第一選択 (定義書換で `sorry` を proof body
に逃がす) を 19 declaration それぞれに適用。AWGN M5 sister との **最大の相違点**:
EPI-Stam family の Mathlib 壁 (`debruijn-integration` / `csiszar` / Stam bridge) は
**既に shared sorry 補題化済み** (表 C)。よって本 plan の Route B は「新規 wall file 新設」
ではなく「**既存 wall lemma を consumer body から呼ぶ**」。新規 `EpiStamWalls.lean` は
原則不要 (L-EPISC-4-γ で例外判定)。

各 declaration は以下の 3 ルート分類:

- **Route A — predicate 純削除 (consumer 連動なし or empty-consumers)**: hypothesis-form
  active consumer が 0 で、削除しても他 declaration の signature を壊さない predicate。
  - `IsHeatFlowFamilyHyp` (#17、hypothesis-form consumer 0、Gaussian 構成子のみ)
  - `IsCsiszarGap1SourceTendsToZeroAtInfinity` (#19、active consumer 0、rescale 経路が代替)
  - `IsStamToEPILimitHyp` (#4、limit 引数が `_` binder で discard される非 load-bearing、
    docstring 自己申告「non-load-bearing in the active pipeline」)
  → これらは Tier 3 `-empty-consumers` の sister 34e17bc precedent。**純削除して
    `_of_scaling_limit` 構成子の `_limit` slot を除去** (Phase 0' future work が本 plan で着地)。

- **Route B — 既存 shared wall lemma に委任 (`docs/audit/audit-tags.md`「共有 Mathlib 壁」)**:
  predicate を削除し、その「結論」を **既存** shared sorry 補題で discharge する。
  - de Bruijn 系 (#1 `IsDeBruijnRegularityHyp` / #2 `IsDeBruijnIntegrationHyp`)
    → `debruijnIdentityV2_holds` (`@residual(wall:debruijn-integration)`)
  - Stam-scaling 系 (#3 `IsStamToEPIScalingHyp` / #5 `IsStamScalingNoiseHyp`)
    → `stamToEPIBridge_holds` (`@residual(plan:epi-stam-to-conclusion-plan)`) または
    Phase A 内部 `csiszarGap_antitoneOn_*` の `@residual(wall:csiszar)` 経路
  - **regularity precondition (`Measurable` / `IndepFun` / `IsProbabilityMeasure` /
    Gaussian law) は残す**。これらは前提条件であり load-bearing ではない (CLAUDE.md
    「判定の一言」)。

- **Route C — bundle 削除 + consumer signature 書換 (`@residual(plan:epi-stam-cluster-c-sorry-migration-plan)`)**:
  bundle `IsEPIL3IntegratedPipeline` (`EPIL3Integration.lean:112`) を削除し、consumer
  (#6-16 + `EPIStamDeBruijnConclusion` の pipeline consumer) の signature から
  `(h_pipeline : IsEPIL3IntegratedPipeline ...)` 引数を除去、body は既存 genuine 経路
  `entropy_power_inequality_unconditional` (Phase A が publish 済の hypothesis-free route)
  への delegation または `stamToEPIBridge_holds` + `debruijnIdentityV2_holds` の thread に
  置換。

**設計判断 (sister 34e17bc / AWGN M5 precedent との整合)**: AWGN M5 では Route A の
sub-bound predicate を Route B (新規 shared sorry 補題) に置換したが、EPI-Stam は
**Route B の置換先が既に存在する** ため、consumer は「既存 wall lemma を呼ぶ普通の
lemma call」に縮約される。pipeline bundle 削除後、各 wrapper は
`entropy_power_inequality_unconditional` (hypothesis-free) への delegate になり、
`@residual` を持たず **proof done 判定可能** になる見込み (壁は `debruijnIdentityV2_holds`
+ `stamToEPIBridge_holds` の 2 file に局所化)。

### genuine theorem の扱い (#18 `bounded_T_ftc_gaussian`)

`bounded_T_ftc_gaussian` (#18) は **body 0 sorry の genuine FTC** で `@entry_point`。
docstring tag は「この lemma が feed する `IsEPIL3IntegratedPipeline.bridge` field が
load-bearing」と述べる **mis-applied bookkeeping**。本 plan では (a) tag を `@audit:ok`
に修正 (本体は honest)、(b) pipeline bundle 削除後は feed 先が消えるので tag 自体不要、と
判定する。Phase 0-4 で honesty-auditor に妥当性を諮る。

### Phase 構成

- **Phase 0** — verbatim 棚卸し (本 plan 完了済、再確認のみ) + **scope 拡張判定**
  (`EPIStamDeBruijnConclusion.lean` を含めるか) + 既存 wall lemma 流用可否照合
- **Phase 1 — Wall name register 確認**: 表 C の `debruijn-integration` / `csiszar` は
  既存 register 登録済 (`docs/audit/audit-tags.md` line 57/67)。**新規 wall は原則不要**。
  Stam noise-extension (#5) が `csiszar` で足りるか `epi-n-dim` 系が要るかのみ判定。
- **Phase 2 — shared sorry 補題の補充判定**: 表 C の 2 補題で全 Route B declaration を
  discharge 可能か確認。不足分があれば既存 wall file (`StamGaussianBound.lean` 等) に
  補充、新規 `EpiStamWalls.lean` 新設は L-EPISC-4-γ 例外時のみ。
- **Phase 3-α (`EPIL3Integration` pipeline 系 13 declaration)**: bundle
  `IsEPIL3IntegratedPipeline` 削除 + consumer #7-16 signature 書換 + empty 2 件純削除
- **Phase 3-β (`EPIStamToBridge` Stam-scaling 3 件)**: #3 #5 を wall 委任、#4 純削除
- **Phase 3-γ (`EPIStamDischarge` de Bruijn 2 件)**: #1 #2 を `debruijnIdentityV2_holds`
  委任 + regularity precondition 残置
- **Phase 3-δ (empty-consumers 3 件 + `EntropyPowerInequality` #6)**: #4 #17 #19 純削除、
  #6 `three_arg` を unconditional route 委任
- **Phase V — 検証 + honesty audit + roadmap update**

## Phase 0 — verbatim 棚卸し + scope 拡張判定 + 既存 wall 照合 ✅ (2026-05-28 完了)

- [x] **0-1**: 表 A の 19 declaration の signature + docstring + 既存タグを verbatim
      再確認。**line drift 検出**: 表 A の line 番号は概ね正確だが、`EPIL3Integration`
      の bundle は `:112` (正)、#17 `IsHeatFlowFamilyHyp` は `:512` (正)、#19
      `IsCsiszarGap1...` は `:1607` (正)。実装時は `rg -n '<decl>'` で再確認のこと。
- [x] **0-2**: consumer 精数分解完了 → **表 A'** 参照。純削除確定 3 件 (#4 #17 #19、
      hyp-form load-bearing 0)。残 16 件は active hyp-form / construct / field 経由で
      consumer に接続。
- [x] **0-3 (★ scope 拡張判定)**: **`EPIStamDeBruijnConclusion.lean` を scope に含める
      (in)**。`isEPIL3IntegratedPipeline_of_stamDeBruijn` (`:210`) は `IsEPIL3IntegratedPipeline`
      の構成子 (`where stam := ...; bridge := h.bridge`) で verbatim 確認済。さらに
      `EPIStamInequalityBody.lean:405` `isStamInequalityHyp_via_body_to_pipeline` も同 bundle
      の構成子 (`{ stam := ...; bridge := h_bridge }`)、`EPIL3Integration` 内にも `_of_gaussian`
      `_of_stam_bridge` `_symm` の構成子あり。→ **bundle 削除は 3+ file に跨る大手術**。
      代わりに **L-EPISC-3-α 採用** = bundle structure `IsEPIL3IntegratedPipeline` は
      **残し**、`bridge : IsStamToEPIBridgeHyp` field を除去 (stam field のみ残す)、
      consumer body は `stamToEPIBridge_holds` 内部呼出に書換。根拠: `entropy_power_inequality_integrated`
      (#8) は **既に body で `.bridge` を使っていない** (`.stam` のみ、docstring が
      「bridge field is now internally discharged via the shared sorry lemma
      `stamToEPIBridge_holds`」と明記、`EPIL3Integration:155-159` verbatim 確認)。
      唯一 `.bridge` を load-bearing に使うのは `epi_l3_of_integrated_pipeline` (#7、
      `h.bridge h.stam`) と `isEPIL3IntegratedPipeline_symm` (#=`bridge := isStamToEPIBridgeHyp_symm h.bridge`)。
      これらを `stamToEPIBridge_holds` 内部呼出に書換すれば field 除去可。
- [x] **0-4**: 表 C の 2 wall lemma の結論型を verbatim Read → **表 C'** 参照。
      #1 ◯ (既存流用)、#2 ✗ (積分形、L-EPISC-1-α 発火 → 新規補題)、#3 ✗ (`AntitoneOn`、
      L-EPISC-2-β 発火 → phaseA-plan slug)、#5 ✗ (noise-extension、新規補題 + 新 wall name 候補)。
      **新規 shared wall 補題 2 件補充確定** (#2 積分形 + #5 noise-extension)。
- [x] **0-5**: import 依存方向 verbatim 確認 → **表 C''** 参照。主たる consumer file
      (`EPIStamDischarge` / `EPIL3Integration` / `EPIStamDeBruijnConclusion`) は両 wall 提供
      file を既に import 済、cycle なし。`EPIStamToBridge` は `FisherInfoV2DeBruijn` 未 import
      だが #5 補題を自 file 集約すれば不要、`EntropyPowerInequality` base への
      `FisherInfoV2DeBruijn` import 追加は avoid (#2 補題は wall file 側に置く)。
      **L-EPISC-4-γ (新規 wall file 新設) 不発見込み**。

## Phase 1 — Wall name register 確認 (`docs/audit/audit-tags.md`) 🔄 (0-4 結果反映)

**0-4 確定: 既存 wall name で #1 #2 を覆う、#3 は plan slug、#5 のみ新規 wall name 候補**。

- [x] **1-1**: `debruijn-integration` (register) が #1 #2 を覆う。#2 は積分形のため
      新規補題 `debruijnIntegrationIdentity_holds` を補充するが **wall name は流用**
      (壁数 0 増)。`debruijnIdentityV2_holds` に既存タグ `@residual(wall:debruijn-integration)`。
- [x] **1-2**: #3 `IsStamToEPIScalingHyp` の `AntitoneOn` 結論は **wall ではなく plan slug**
      委任。Phase A 内部 `csiszarGap_antitoneOn_*` が `@residual(plan:epi-stam-to-conclusion-phaseA-plan)`
      を持つので、#3 consumer body は phaseA-plan slug 経由 (L-EPISC-2-β)。`csiszar` wall
      は使わない。
- [ ] **1-3**: #5 `IsStamScalingNoiseHyp` (noise-extension richness `∃ Z_X Z_Y, ... ∧ IndepFun Z_X Z_Y P`)
      は **`csiszar` 不適** (semantic 別物 — `csiszar` は projection 系、本件は arbitrary
      probability space 上の独立 standard normal pair 存在で `MeasureTheory.IsAtomless`
      系の Mathlib 未整備部、loogle/rg 0 件)。docstring 自己申告 closure plan は
      `epi-stam-to-conclusion-phaseA-plan` L-Concl-A-γ。**選択肢 2 つ**:
      (a) 新規 wall name `epi-noise-extension` を `docs/audit/audit-tags.md` **Proposed 表**
      に提案 (promote 留保、register 本表入りは後続 PR)、補題は `@residual(wall:epi-noise-extension)`、
      または (b) 当面 plan slug `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` 流用。
      **デフォルト = (b)** (本 plan のデフォルト方針「plan-slug で揃え、wall 化は後続」、
      Proposed 表追加は別 PR)。`docs/audit/audit-tags.md` は **無変更** が目標。

## Phase 2 — shared sorry 補題の補充 🔄 (0-4 確定: 新規補題 2 件補充要)

**0-4 確定: 既存 2 補題では不足、新規 shared sorry 補題 2 件を既存 file に補充**
(新規 wall **file** 新設は不要、L-EPISC-4-γ 不発)。

- [x] **2-1**: 表 C の 2 補題では #2 (積分形) と #5 (noise-extension) を discharge できない
      (表 C' 照合済)。#1 は既存 `debruijnIdentityV2_holds` 流用、#3 は phaseA-plan slug。
- [ ] **2-2 (補充 1 — #2 積分形)**: `FisherInfoV2DeBruijn.lean` (既存 wall file、`#1` 補題と
      同 file、cycle なし) に新規 shared sorry 補題を追加:
      ```
      /-- de Bruijn 積分恒等式 (Cover-Thomas 17.7.2 積分形)。per-time HasDerivAt を
      FTC で積分した形。一般 X では Mathlib 未整備 (一般 heat-flow path の積分可能性)。
      @residual(wall:debruijn-integration) -/
      theorem debruijnIntegrationIdentity_holds (X Z : Ω → ℝ) (P) [...] (T : ℝ) :
          h_target - h_X = ∫ t in Set.Ioo 0 T, (1/2)*(fisherInfoOfMeasureV2 ...).toReal ∂volume := by
        sorry
      ```
      結論は #2 `IsDeBruijnIntegrationHyp` の body (`∃ fPath` を剥がした non-existential 形、
      または `∃ fPath` 込みの形) に shape を合わせる。wall name は `debruijn-integration` 流用。
- [ ] **2-3 (補充 2 — #5 noise-extension)**: `EPIStamToBridge.lean` 内 (#5 predicate と同 file、
      import cycle なし) に新規 shared sorry 補題を追加:
      ```
      /-- noise-extension richness: 任意の確率空間上に 2 つの独立 standard normal pair が
      存在 (arbitrary probability space 上の独立性、Mathlib 未整備、MeasureTheory.IsAtomless 系)。
      @residual(plan:epi-stam-to-conclusion-phaseA-plan) -/  -- ← Phase 1-3 (b) デフォルト
      theorem stamScalingNoise_exists (X Y : Ω → ℝ) (P) [...] : IsStamScalingNoiseHyp X Y P := by
        sorry
      ```
      `@residual` slug は Phase 1-3 の判定に従う (デフォルト = plan slug `epi-stam-to-conclusion-phaseA-plan`、
      wall 化採用時のみ `wall:epi-noise-extension` + Proposed 表追加)。
- [ ] **2-4**: `InformationTheory.lean` import は **無変更** (両補題とも既存 file に追加、新規 file 無し)。
- [ ] **2-5**: 補充した 2 file (`FisherInfoV2DeBruijn.lean` / `EPIStamToBridge.lean`) を
      `lake env lean` で 0 errors / sorry warning のみ確認。

## Phase 3 並列実装ルーティング表 (★ 並列 dispatch 用、2026-05-28 確定)

Phase 0 の cross-file 依存照合に基づく **disjoint file 分割**。bundle
`IsEPIL3IntegratedPipeline` の `bridge` field 除去 (L-EPISC-3-α) は **定義 file +
構成子 file** が同時に変わるため逐次 (1 agent)。de Bruijn 系と Stam-scaling 系は
bundle field と独立に進められるため並列可能。

### cross-file 依存の核心 findings (verbatim 確認済)

- `IsEPIL3IntegratedPipeline.bridge` を **load-bearing に触る**のは: `EPIL3Integration`
  (#7 `epi_l3_of_integrated_pipeline` の `h.bridge h.stam`、`isEPIL3IntegratedPipeline_symm`
  の `bridge := ...`) + **構成子** `EPIStamDeBruijnConclusion:216/321` (`bridge := h.bridge`)
  + **構成子** `EPIStamInequalityBody:405` (`{ bridge := h_bridge }`) + `EPIL3Integration`
  内 `_of_gaussian`/`_of_stam_bridge`。→ **field 除去はこの 3 file が同時変更必須** = **Group 1 (逐次)**。
- `EPIStamToBridge` は `IsEPIL3IntegratedPipeline.bridge` を **触らない** (docstring mention のみ、
  `:55`/`:1150`)。自 file の別 bundle `IsEPIScalingDecomposedPipeline` (`:1153`、field
  `stam`/`scaling`/`limit`) は独立。→ Stam-scaling 系は Group 1 と並列可能 = **Group 2**。
- `EPIStamDischarge` は `IsEPIL3IntegratedPipeline` / `.bridge` を **触らない**。de Bruijn 系は
  独立 = **Group 3** (ただし #1 の wall lemma 補充は Group 3、#2 の積分形補題 (`FisherInfoV2DeBruijn`)
  は最上流なので **先行**)。
- `EPIPlumbing` は `.bridge` 触らない、#6 `three_arg` を body で呼ぶ consumer (`:251`)。
- `EntropyPowerInequality` は bundle / Stam-scaling predicate を **触らない** (#6 `three_arg` の
  定義のみ自 file `:416`)。

### 並列分割 (3 Agent、Group 1 のみ 3 file 逐次)

| Agent | touch する file (disjoint) | 担当 declaration | 依存 / 順序 |
|---|---|---|---|
| **Agent X (Group 1 — pipeline bundle)** | `EPIL3Integration.lean` + `EPIStamDeBruijnConclusion.lean` + `EPIStamInequalityBody.lean` (3 file 逐次、同一 agent) | bundle `IsEPIL3IntegratedPipeline` の `bridge` field 除去 (L-EPISC-3-α) + #7-16 consumer 書換 + 構成子書換 (Conclusion #210/321、InequalityBody #405、EPIL3 `_of_gaussian`/`_of_stam_bridge`/`_symm`) + #17 #19 純削除 + #18 tag 修正 + §12/§13 narrative tag 整理 | Phase 2-3 (#5 noise 補題、Agent Y) に依存しない (bridge は `stamToEPIBridge_holds` 既存で discharge)。**Phase 2-2 (#2 積分形補題) 完了後に開始推奨** だが #2 は EPIStamDischarge 経由 transitive なので blocking ではない |
| **Agent Y (Group 2 — Stam-scaling)** | `EPIStamToBridge.lean` + `HeatFlowPath.lean` (docstring 整合のみ) | #3 `IsStamToEPIScalingHyp` wall/plan 委任 (phaseA-plan slug、L-EPISC-2-β) + #4 `IsStamToEPILimitHyp` 純削除 + `_of_scaling_limit` の `_limit` slot 除去 + #5 `IsStamScalingNoiseHyp` wall 委任 + **新規補題 `stamScalingNoise_exists` 補充 (Phase 2-3)** + `isStamScalingNoiseHyp_symm` 連動 + `IsEPIScalingDecomposedPipeline` の `limit` field 連動 | Group 1 と独立 (bundle field 触らず)。新規 #5 補題は自 file に集約 (import cycle なし) |
| **Agent Z (Group 3 — de Bruijn)** | `EPIStamDischarge.lean` + `FisherInfoV2DeBruijn.lean` (新規 #2 補題) | #1 `IsDeBruijnRegularityHyp` を `debruijnIdentityV2_holds` 委任 (regularity precond 残置) + #2 `IsDeBruijnIntegrationHyp` を **新規補題 `debruijnIntegrationIdentity_holds` (Phase 2-2)** 委任 + consumer 書換 | Group 1/2 と独立。**`FisherInfoV2DeBruijn` は最上流** なので #2 補題補充は他 agent と衝突しない。ただし `EntropyPowerInequality` (#2 consumer 2 件、`:?`) を touch する場合は Agent Z が担当 (base file、他 agent は触らない) |

### 並列不可 / 逐次部 (明示)

- **Group 1 内の 3 file は逐次** (同一 agent): bundle 定義 (`EPIL3Integration`) を変えると
  構成子 (`EPIStamDeBruijnConclusion` / `EPIStamInequalityBody`) が即 type error になるため、
  3 file を 1 agent が一括編集 + 1 回の `lake env lean` で検証する。
- **`EntropyPowerInequality.lean` (#6 `three_arg` + #2 consumer 2 件)**: base file。#6 は
  unconditional route 委任 (Route C)、#2 consumer は新 signature 整合。**Agent Z が touch**
  (de Bruijn #2 と #6 が同 file に近接、base file の二重編集を避けるため 1 agent に集約)。
  `EPIPlumbing.lean` (#6 consumer `:251`) も Agent Z 担当 (#6 signature 変更の ripple)。
- **Agent 間 file 所有権 (disjoint 確認)**: Agent X = {EPIL3Integration, EPIStamDeBruijnConclusion,
  EPIStamInequalityBody}、Agent Y = {EPIStamToBridge, HeatFlowPath}、Agent Z = {EPIStamDischarge,
  FisherInfoV2DeBruijn, EntropyPowerInequality, EPIPlumbing}。**重複なし**。

### routing 上の注意 (orchestrator brief に転記)

- 並列前提 (worktree 隔離 + boilerplate) は実装系 `lean-implementer` の並列 dispatch
  なので CLAUDE.md「Parallel orchestration」boilerplate 必須。
- Agent X の bundle field 除去で `entropy_power_inequality_integrated` (#8) は **既に
  `.stam` のみ使用** なので body 変更は最小。`epi_l3_of_integrated_pipeline` (#7) と
  `isEPIL3IntegratedPipeline_symm` のみ `stamToEPIBridge_holds` 内部呼出に書換が必要。
- 各 Agent の sub-bound 引数表は本 plan 表 A' + 表 C' で供給済 (どの predicate がどの wall/plan
  slug に委任されるか確定)。implementer に再判定させない。
- Agent Z の #2 積分形補題は **shape を `IsDeBruijnIntegrationHyp` の body に合わせる** こと
  (CLAUDE.md「Mathlib-shape-driven Definitions」、`∫ t in Set.Ioo 0 T, (1/2)*(...).toReal ∂volume` 形)。

## Phase 3-α — `EPIL3Integration` pipeline 系 13 declaration 📋

`EPIL3Integration.lean` を touch (Phase 0-3 で `EPIStamDeBruijnConclusion.lean` を scope に
含めた場合はそちらも)。

- [ ] **3α-1**: bundle `structure IsEPIL3IntegratedPipeline` (`:112`) を削除するか、
      `bridge` field の load-bearing を除去するか Phase 0-3 結果で確定
- [ ] **3α-2**: pipeline consumer #7-16 (10 件) の signature から
      `(h_pipeline : IsEPIL3IntegratedPipeline ...)` 引数を除去、body を
      `entropy_power_inequality_unconditional` (hypothesis-free、Phase A publish 済) への
      delegation に置換。delegate 不可な変種は `stamToEPIBridge_holds` thread +
      `@residual(plan:epi-stam-cluster-c-sorry-migration-plan)` を 1 件残置
- [ ] **3α-3**: `IsHeatFlowFamilyHyp` (#17、`:512`) 純削除 (hypothesis-form consumer 0、
      Gaussian 構成子 `isHeatFlowFamilyHyp_of_gaussian` も連動削除 or 単独 lemma に格下げ)
- [ ] **3α-4**: `IsCsiszarGap1SourceTendsToZeroAtInfinity` (#19、`:1607`) 純削除
      (active consumer 0、docstring 自己申告「safe to retract outright」)
- [ ] **3α-5**: `bounded_T_ftc_gaussian` (#18、`:971`) の tag を `@audit:ok` に修正
      (本体 genuine、feed 先 bundle が消えるため bookkeeping tag 不要)
- [ ] **3α-6**: §12 / §13 narrative tag (466 / 477 / 1028 / 1036) を整理
      (declaration が無い section comment、grep-aggregate 用 tag は削除して
      実 declaration tag のみ残す)
- [ ] **3α-7**: `lake env lean InformationTheory/Shannon/EPIL3Integration.lean` 0 errors

## Phase 3-β — `EPIStamToBridge` Stam-scaling 3 件 📋

`EPIStamToBridge.lean` を touch (+ `HeatFlowPath.lean` consumer 1)。

- [ ] **3β-1**: `IsStamToEPIScalingHyp` (#3、`:222`) wall/plan 委任 — Phase 0-4 で
      `stamToEPIBridge_holds` or `csiszarGap_antitoneOn_*` (plan slug) のどちらで
      discharge するか確定。predicate 削除、consumer (`isStamToEPIScalingHyp_of_stam_debruijn`
      = `@audit:ok` constructor) は wall lemma 呼出に書換
- [ ] **3β-2**: `IsStamToEPILimitHyp` (#4、`:265`) 純削除 + `isStamToEPIBridgeHyp_of_scaling_limit`
      構成子の `_h_limit` slot 除去 (docstring 自己申告「ready for retraction once that
      constructor's `_limit` slot is removed」を本 plan で着地)
- [ ] **3β-3**: `IsStamScalingNoiseHyp` (#5、`:459`) wall 委任 (Phase 1-3 で確定した
      `csiszar` or 新規 wall)、`isStamScalingNoiseHyp_symm` 連動書換
- [ ] **3β-4**: `HeatFlowPath.lean` の `IsStamToEPIScalingHyp` mention 1 件を整合
- [ ] **3β-5**: `lake env lean InformationTheory/Shannon/EPIStamToBridge.lean`
      + `lake env lean InformationTheory/Shannon/HeatFlowPath.lean` 0 errors

## Phase 3-γ — `EPIStamDischarge` de Bruijn 2 件 📋

`EPIStamDischarge.lean` を touch。

- [ ] **3γ-1**: `IsDeBruijnRegularityHyp` (#1、`:206`、structure) を削除し、その genuine
      `HasDerivAt` content を `debruijnIdentityV2_holds` で discharge。
      **regularity precondition** (`IsProbabilityMeasure` / density data) は consumer
      signature に残す (load-bearing ではない)。consumer
      (`EPIStamToBridge` 45 mention の大半は `.field` extract — Phase 0-2 で精査) を
      wall lemma 呼出に書換
- [ ] **3γ-2**: `IsDeBruijnIntegrationHyp` (#2、`:286`、def `∃ fPath, ∫...`) を削除し、
      `debruijnIdentityV2_holds` の積分形を呼出。consumer (`EPIStamDischarge` 11 /
      `EPIL3Integration` 4 / `EntropyPowerInequality` 2) を書換
- [ ] **3γ-3**: `lake env lean InformationTheory/Shannon/EPIStamDischarge.lean` 0 errors

## Phase 3-δ — `EntropyPowerInequality` #6 + 残 empty-consumers 統合検証 📋

`EntropyPowerInequality.lean` + `EPIPlumbing.lean` を touch。

- [ ] **3δ-1**: `entropy_power_inequality_three_arg` (#6、`:416`) の 2 hyp
      `IsEntropyPowerInequalityHypothesis` を除去、body を
      `entropy_power_inequality_unconditional` 2 回適用 (docstring 自己申告
      「Phase A ships a genuine alternative discharge route that no longer requires
      L-EPI3 as an input」) に置換
- [ ] **3δ-2**: tag@350 narrative (既削除 decl の retraction comment) を確認のみ (touch 不要)
- [ ] **3δ-3**: `EPIPlumbing.lean` の `entropy_power_inequality_three_arg` mention 3 件を
      新 signature に整合
- [ ] **3δ-4**: `lake env lean InformationTheory/Shannon/EntropyPowerInequality.lean`
      + `lake env lean InformationTheory/Shannon/EPIPlumbing.lean` 0 errors

## Phase V — closure 📋

- [ ] **V-1**: 全 touched file の `lake env lean` 検証 0 errors:
      `EPIL3Integration` / `EPIStamToBridge` / `HeatFlowPath` / `EPIStamDischarge` /
      `EntropyPowerInequality` / `EPIPlumbing` (+ scope 拡張時 `EPIStamDeBruijnConclusion`
      / `EPIStamInequalityBody`) / 補充時の wall file / `InformationTheory.lean`
- [ ] **V-2**: 各 file の `sorry` 件数を verbatim 確認:
      - **期待値**: consumer file は **0 migration-由来 sorry** (既存 wall lemma 呼出に
        置換、`@residual` を持たず proof done 判定可能)。残 sorry は本 plan 委任分
        (`@residual(plan:epi-stam-cluster-c-sorry-migration-plan)`) と pre-existing
        (`debruijnIdentityV2_holds` / `stamToEPIBridge_holds` の壁 sorry はそのまま)
      - 壁は `FisherInfoV2DeBruijn.lean` + `EntropyPowerInequality.lean` の 2 file に
        局所化 (新規 wall file 無しが目標)
- [ ] **V-3**: CLAUDE.md「Independent honesty audit」必須条件発動: 既存 declaration の
      signature 改変 (predicate hyp 引数削除) + predicate 純削除 + 新規 `@residual` 導入
      → `honesty-auditor` subagent を fresh 起動。**特に #18 `bounded_T_ftc_gaussian` の
      tag 修正 (`@audit:ok`) の妥当性 + empty-consumers 純削除の安全性を諮る**
- [ ] **V-4**: auditor verdict 反映 (DEFECT 検出時は当該 declaration 撤回 + sorry-based
      書換、questionable は docstring refine、全 OK は session 完了)
- [ ] **V-5**: `docs/shannon/epi-moonshot-plan.md` 進捗ブロック + 判断ログ更新
      (Cluster C declaration の Tier 3 → Tier 2 移行完了実績)
- [ ] **V-6**: `docs/textbook-roadmap.md` Ch.17 EPI 行 update
      (`debruijn-integration` / `csiszar` wall の active sorry 件数、
      pipeline wrapper 群が unconditional route 委任で proof done 化した状態)

## 撤退ライン

- **L-EPISC-0-honest-defect** — Phase 0-3 scope 拡張判定で
  `EPIStamDeBruijnConclusion.lean` の `isEPIL3IntegratedPipeline_of_stamDeBruijn`
  (構成子) が pipeline bundle 削除に必須と判明 (= bundle を残すと load-bearing
  `bridge` field が除去できない、削除すると構成子が孤児化)。
  **対処**: `EPIStamDeBruijnConclusion.lean` を本 plan scope に **正式拡張**
  (4 declaration + `IsEPIStamDeBruijnPipeline` bundle を Route C に追加)。
  brief の「4 file」を 5 file に拡張する旨を判断ログに記録。

- **L-EPISC-1-α** — Phase 0-4 で既存 `debruijnIdentityV2_holds` の結論型が
  `IsDeBruijnIntegrationHyp` の `∃ fPath, ∫...` 形を **直接供給できない** (再 shaping
  bridge が必要) と判明。
  **撤退**: CLAUDE.md「Mathlib-shape-driven Definitions」の red flag。新規 shared wall
  lemma `debruijnIntegrationIdentity_holds` (積分形に shape 合わせ) を Phase 2 で補充
  (`@residual(wall:debruijn-integration)`)、壁件数は 0 増 (既存 wall name 流用)。

- **L-EPISC-2-β** — Phase 3-β で `IsStamToEPIScalingHyp` (#3) の `AntitoneOn` 結論が
  `stamToEPIBridge_holds` でも `csiszarGap_antitoneOn_*` (plan slug) でも discharge
  できない (両者とも別の結論型を返す)。
  **撤退**: consumer body に `sorry` + `@residual(plan:epi-stam-to-conclusion-phaseA-plan)`
  を 1 件残置 (Phase A の既存 closure plan に委任、本 plan slug ではなく phaseA-plan slug)。
  Tier 2 移行は完遂 (honest sorry を既存 plan で抱える)。

- **L-EPISC-3-α** — Phase 0-3 で `EPIStamDeBruijnConclusion` を scope 外に維持し、かつ
  pipeline bundle 削除も不可と確定 (構成子依存が解けない)。
  **撤退**: Route C を「bundle 削除」から「bundle の `bridge` field を非 load-bearing 化」に
  降格 — `IsEPIL3IntegratedPipeline` は残すが `bridge : IsStamToEPIBridgeHyp` を削除し
  consumer が `stamToEPIBridge_holds` を内部呼出する形に。bundle structure は残るが
  load-bearing field が消えるので Tier 2 達成 (sister `entropy_power_inequality_integrated`
  の `:158` 既存コメント「bridge field is now internally discharged via the shared sorry
  lemma `stamToEPIBridge_holds`」が既にこの形を示唆 — verbatim 確認済)。

- **L-EPISC-4-γ** — Phase 1-3 / Phase 2 で既存 2 shared wall lemma + 既存 file への補充
  では足りず、**新規 `EpiStamWalls.lean` 新設が必要**と判明 (補充先 file が import cycle に
  なる等)。
  **撤退**: AWGN M5 の `AwgnWalls.lean` precedent に倣い新規 file
  `InformationTheory/Shannon/EpiStamWalls.lean` を新設、shared sorry 補題を集約。
  `InformationTheory.lean` に import 1 行追加。wall name は既存 `debruijn-integration` / `csiszar`
  流用 (新規 wall name 増は別判定)。

- **L-EPISC-5-honest-defect** — Phase 3 の consumer 書換中に **新規 honesty defect** 発見
  (例: pipeline consumer の body が実は別の load-bearing predicate を内部 consume している、
  または `entropy_power_inequality_unconditional` が hypothesis-free と申告されているのに
  実は Stam residual を load-bearing で取っている)。
  **撤退**: CLAUDE.md「検証の誠実性」inline alert 発動 + 該当 declaration の上に build
  しない、本 plan を **段階完了** で closure (完了した Phase のみ landing、残りを別 plan に
  分割)、新規 defect 用 sub-plan filename `epi-stam-cluster-c-followup-plan` を予約。

## scope-out (本 plan で扱わない)

- **AWGN M5 9-10 declaration** (`AWGN*.lean`) — sister `awgn-m5-sorry-migration-plan.md`
  で同型 Path 1 着地済 (achievability 完全 proof done)。本 plan の直接の precedent。
- **Stam 本体の壁 closure** (`debruijnIdentityV2_holds` / `stamToEPIBridge_holds` の
  `sorry` を埋める) — 本 plan は壁を **集約する consumer 側** の Tier 2 移行であり、壁
  本体の discharge は `epi-stam-to-conclusion-plan` / `epi-debruijn-integration-plan` の
  責務。本 plan 完了後も `wall:debruijn-integration` / `plan:epi-stam-to-conclusion-plan`
  の sorry は残る (これは正しい — Tier 2 honest sorry)。
- **`EPIStamStep12Body.lean` / `EPIStamStep3Body.lean` / `StamGaussianBound.lean`** —
  Stam 本体の step-by-step 構築 file。本 plan の consumer graph に load-bearing predicate
  経由で接続していない限り touch 不要 (Phase 0-2 で接続確認)。
- **`IsStamInequalityHyp` / `IsStamToEPIBridgeHyp` predicate 自体の retract** — これらは
  bundle の field 型 (表 D)。`IsStamToEPIBridgeHyp` は `@audit:ok`、`IsStamInequalityHyp`
  は genuine Fisher-info 形。本 plan は bundle wrapper を消すのであって field 型 def 自体を
  消すわけではない (field 型は `stamToEPIBridge_holds` の引数型として残る)。
- **`brunn-minkowski-from-epi-discharge-plan` / `epi-convolution-density-plan`** — EPI を
  consume する下流 family。本 plan の Tier 2 移行で signature が変わると影響を受ける可能性
  があるが、調整は別 session (orchestrator 管理)。

## 報告フォーマット (本 plan を消費する implementer / orchestrator 向け)

本 plan の完了時、orchestrator は以下を確認:

1. 表 A の 19 declaration (+ scope 拡張時 `EPIStamDeBruijnConclusion` 4-5 件) から
   load-bearing predicate hyp が **完全除去** (= predicate 削除 / bundle field 除去 +
   consumer signature 書換)。empty-consumers 3 件 (#4 #17 #19) は純削除。
2. 壁は既存 `debruijnIdentityV2_holds` + `stamToEPIBridge_holds` の 2 file に局所化
   (新規 wall file 無しが目標、L-EPISC-4-γ 発動時のみ `EpiStamWalls.lean` 新設)。
3. `lake env lean` 全 touched file 0 errors。consumer file は migration-由来 sorry 0。
4. `honesty-auditor` verdict = 全 OK or questionable (DEFECT は L-EPISC-5 発動で段階完了)。
   特に #18 `bounded_T_ftc_gaussian` tag 修正 + empty-consumers 純削除の安全性が PASS。
5. `docs/shannon/epi-moonshot-plan.md` 進捗ブロック + 判断ログ更新済。
6. `docs/audit/audit-tags.md` Wall name register は **無変更が目標**
   (既存 `debruijn-integration` / `csiszar` 流用)。新規 wall 追加は L-EPISC-4-γ 例外時のみ。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **Phase 0-3 scope 確定 = 6 file (L-EPISC-0-honest-defect + L-EPISC-3-α 併発、2026-05-28)**:
   `EPIStamDeBruijnConclusion.lean:210` `isEPIL3IntegratedPipeline_of_stamDeBruijn` が
   `IsEPIL3IntegratedPipeline` の構成子 (`where stam := ...; bridge := h.bridge`) と
   verbatim 確認。さらに `EPIStamInequalityBody.lean:405` `isStamInequalityHyp_via_body_to_pipeline`
   も同 bundle 構成子 (`{ stam := ...; bridge := h_bridge }`)。bundle **削除** は構成子が
   3+ file に散在するため大手術 → **bundle は削除せず `bridge` field のみ除去** (L-EPISC-3-α
   採用)。根拠: `entropy_power_inequality_integrated` (#8) は既に body で `.bridge` 不使用
   (`EPIL3Integration:155-159` docstring「bridge field is now internally discharged via
   `stamToEPIBridge_holds`」)。scope = brief の 4 file (`EPIL3Integration` / `EPIStamToBridge` /
   `EPIStamDischarge` / `EntropyPowerInequality`) + **`EPIStamDeBruijnConclusion` + `EPIStamInequalityBody`**
   (構成子) + ripple `EPIPlumbing` / `HeatFlowPath` (docstring/consumer 整合)、wall 補充 file
   `FisherInfoV2DeBruijn`。新規 wall **file** は不要 (L-EPISC-4-γ 不発)。
2. **Phase 0-4 既存 wall 流用照合 — 既存 2 補題では不足、新規 2 件補充確定 (2026-05-28)**:
   verbatim 結論型照合 (表 C') の結果、当初の楽観 (「既存 2 補題で全 Route B discharge」) を
   修正。#1 `IsDeBruijnRegularityHyp` のみ `debruijnIdentityV2_holds` (per-time `HasDerivAt`)
   で直接供給可。#2 `IsDeBruijnIntegrationHyp` は **積分形 `∫...`** で wall の per-time deriv を
   FTC でつなぐ bridge が別途必要 (L-EPISC-1-α 発火) → 新規補題 `debruijnIntegrationIdentity_holds`
   補充。#3 `IsStamToEPIScalingHyp` の `AntitoneOn` は `stamToEPIBridge_holds` (含意形) で供給
   不可 (L-EPISC-2-β 発火) → Phase A `csiszarGap_antitoneOn_*` (`@residual(plan:epi-stam-to-conclusion-phaseA-plan)`)
   委任。#5 `IsStamScalingNoiseHyp` の noise-extension richness は `csiszar` でも `debruijn-integration`
   でもない別の壁 (arbitrary probability space 上の独立 standard normal pair 存在、Mathlib 0 件、
   `MeasureTheory.IsAtomless` 系) → 新規補題 `stamScalingNoise_exists` 補充。
3. **Phase 0-5 import cycle 否定 (2026-05-28)**: 主たる consumer file
   (`EPIStamDischarge` / `EPIL3Integration` / `EPIStamDeBruijnConclusion`) は wall 提供 file
   `FisherInfoV2DeBruijn` / `EntropyPowerInequality` を既に import 済 (各 `^import` 行 verbatim)。
   cycle なし。新規補題は #2 → `FisherInfoV2DeBruijn` (最上流)、#5 → `EPIStamToBridge` 自 file に
   集約することで import 追加ゼロ。`EntropyPowerInequality` base file への `FisherInfoV2DeBruijn`
   import 追加は avoid (`IsStamInequalityResidual:188` docstring が「base file free of import cycle」
   と明示、density-keyed `fisherInfoOfDensityReal` 採用理由)。
4. **新規 shared wall 補題 = 2 件 (#2 積分形 + #5 noise-extension)、新規 wall name 候補 = 1 件
   (`epi-noise-extension`、Proposed 表、promote 留保)**: wall **file** 新設不要 (L-EPISC-4-γ 不発)。
   `docs/audit/audit-tags.md` Wall name register 本表は **無変更が目標** — #2 は既存
   `debruijn-integration` 流用、#5 はデフォルト plan slug `epi-stam-to-conclusion-phaseA-plan` 流用
   (wall 化採用時のみ Proposed 表に `epi-noise-extension` 追加、本表 promote は後続 PR)。
5. **Phase 3 並列分割 = 3 Agent disjoint (2026-05-28)**: Agent X (Group 1、pipeline bundle、
   3 file 逐次: `EPIL3Integration` + `EPIStamDeBruijnConclusion` + `EPIStamInequalityBody`)、
   Agent Y (Group 2、Stam-scaling: `EPIStamToBridge` + `HeatFlowPath`)、Agent Z (Group 3、
   de Bruijn + base: `EPIStamDischarge` + `FisherInfoV2DeBruijn` + `EntropyPowerInequality` +
   `EPIPlumbing`)。cross-file 依存 verbatim 確認: `EPIStamToBridge` / `EPIStamDischarge` /
   `EPIPlumbing` / `EntropyPowerInequality` はいずれも `IsEPIL3IntegratedPipeline.bridge` を
   触らない (Agent X の field 除去と独立) → 3 Group 並列可。Group 1 内のみ bundle 定義変更が
   構成子を即 type error にするため逐次 (同一 agent 一括編集)。撤退ライン発動: L-EPISC-0
   (scope 6 file 確定の形で着地、純粋撤退ではなく当初想定通り) + L-EPISC-1-α (#2 積分形補題補充) +
   L-EPISC-2-β (#3 phaseA-plan slug 委任)、いずれも対処済で Phase 3 実装に渡せる状態。
   L-EPISC-3-α (bridge field 非 load-bearing 化) は撤退ではなく **採用方針**として確定。
   L-EPISC-4-γ (新規 wall file) / L-EPISC-5 (新規 defect) は不発。

6. **Phase 1-3 実装完了 — 3 並列グループ landing 済 (2026-05-28、commit `487547f` Z / `eeea99b` X / `e95b3e2` Y)**:
   Phase 3 並列分割 (判断ログ 5) の 3 Agent が全 landing。**新規 shared sorry 補題 = 計 4 件**、
   **新規 wall file 0 / 新規 wall name 0** (`epi-noise-extension` は採用せずデフォルト plan slug、
   `docs/audit/audit-tags.md` 無変更 → L-EPISC-4-γ 不発確定)。各 Group の着地内容:

   - **Group 1 (Agent X — `EPIL3Integration` + `EPIStamDeBruijnConclusion` + `EPIStamInequalityBody`、commit `eeea99b`)**:
     bundle `IsEPIL3IntegratedPipeline` の `bridge` field を除去 (L-EPISC-3-α 採用)。`bridge` を使っていた
     `epi_l3_of_integrated_pipeline` / `isEPIL3IntegratedPipeline_symm` を `stamToEPIBridge_holds` 内部呼出に書換、
     構成子 `_of_stam_bridge` → `_of_stam` に改名。#17 `IsHeatFlowFamilyHyp` / #19
     `IsCsiszarGap1SourceTendsToZeroAtInfinity` は純削除。#18 `bounded_T_ftc_gaussian` を `@audit:ok` に修正。
     **これら 3 file は 0 新規 sorry / 0 新規 @residual** (proof done 寄り、壁は他 file 局所)。

   - **Group 2 (Agent Y — `EPIStamToBridge` + `HeatFlowPath`、commit `e95b3e2`)**:
     #3 `IsStamToEPIScalingHyp` を新規 shared sorry `stamToEPIScaling_holds`
     (`@residual(plan:epi-stam-to-conclusion-phaseA-plan)`) に body 委任 (predicate def は field 型として残置)。
     #4 `IsStamToEPILimitHyp` は純削除 (`_of_scaling_limit` → `_of_scaling`、`_limit` slot 除去)。
     #5 `IsStamScalingNoiseHyp` を新規 shared sorry `stamScalingNoise_exists` (同 slug) に委任。
     **honesty fix**: `entropy_power_inequality_unconditional` は旧「`@audit:ok` を名乗りつつ #1/#4/#5 を
     load-bearing thread」(tier 5 overstatement) を、`@audit:ok` 除去 +
     `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` + docstring で `_unconditional` を legacy misnomer
     明示、に修正。

   - **Group 3 (Agent Z — `EPIStamDischarge` + `FisherInfoV2DeBruijn` + `EntropyPowerInequality` + `EPIPlumbing`、commit `487547f`)**:
     #2 用に新規 shared sorry `debruijnIntegrationIdentity_holds` (積分形、`@residual(wall:debruijn-integration)`、
     `FisherInfoV2DeBruijn` 最上流に配置) を補充。#1 / #2 は predicate を削除せず regularity bundle として残し
     load-bearing 部分のみ wall 委任 (cross-file 衝突回避)。#6 `entropy_power_inequality_three_arg` を `@audit:ok`。
     署名改変 0。

   **新規 shared sorry 補題 4 件の内訳**: `debruijnIntegrationIdentity_holds` (積分形) + 委任 witness
   `isDeBruijnIntegrationHyp_holds` [`wall:debruijn-integration`] / `stamToEPIScaling_holds` /
   `stamScalingNoise_exists` [両者 `plan:epi-stam-to-conclusion-phaseA-plan`]。L-EPISC-4-γ 不発。

7. **Phase V 独立 honesty audit 全 OK (2026-05-28、commit `4b3d165`)**: fresh `honesty-auditor` subagent が
   **全 8 項 OK / DEFECT 0** 判定。核心の verdict: `stam` / `h_stam` (Stam 不等式) の threading は
   **honest precondition** と判定 — Stam 本体壁は upstream `epi-stam-to-conclusion-plan` の責務であり、
   本 plan の scope-out (§scope-out) 通り。Cluster C declaration の Tier 3 → Tier 2 移行は完遂。
   **残課題 (handoff 追跡用)**: (a) `IsEPIStamDeBruijnPipeline.bridge` field がまだ load-bearing
   (後続 group が同型 L-EPISC-3-α で処理予定)、(b) `stamScalingNoise_exists` + `isDeBruijnIntegrationHyp_holds`
   は published-but-unconsumed (Phase A 実装が consumer を生むか追跡)。
