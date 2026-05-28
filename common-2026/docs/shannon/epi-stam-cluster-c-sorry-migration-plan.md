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

- [ ] Phase 0 — verbatim 棚卸し + 既存 shared wall 流用判定 + Approach 確定 📋
- [ ] Phase 1 — Wall name register 確認 (新規 wall 不要見込み、要確認) 📋
- [ ] Phase 2 — shared sorry 補題の流用 / 補充 (新規 wall file 不要見込み) 📋
- [ ] Phase 3-α — pipeline bundle 消費系の純削除 + consumer 書換 (`EPIL3Integration`) 📋
- [ ] Phase 3-β — Stam-scaling 系 predicate の wall 委任 + consumer 書換 (`EPIStamToBridge`) 📋
- [ ] Phase 3-γ — de Bruijn regularity / integration predicate の wall 委任 (`EPIStamDischarge`) 📋
- [ ] Phase 3-δ — empty-consumers predicate の純削除 (3 件) 📋
- [ ] Phase V — 検証 + honesty audit + roadmap update 📋

## Context — verbatim 棚卸し (2026-05-28、`34e17bc` 時点コード)

`rg -n '@audit:retract-candidate\(load-bearing-predicate'` は対象 4 file で **計 25 hit** を
返すが、**大半は docstring/narrative の文字列リテラル mention** であり declaration-level
tag ではない。各 hit を Read で確認し、(a) declaration-level の load-bearing predicate /
consumer tag、(b) docstring/narrative の散文 mention、(c) `-empty-consumers` variant
(consumer 0、純削除候補) の 3 種に分離した。

### 表 A — declaration-level tag 一覧 (本 plan の移行対象)

`@audit:retract-candidate(load-bearing-predicate)` (-empty-consumers variant を含む) が
**実 declaration の docstring** に付いているもの。種別 / 既存タグ / consumer 数を verbatim
列挙。consumer 数は `rg -nc '<name>' Common2026/Shannon/` の全 file 合計 (hypothesis-form /
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

### 表 D — 周辺 predicate (本 plan の前提、移行 scope 外だが Route 設計の土台)

| predicate | file:line | タグ | 役割 |
|---|---|---|---|
| `structure IsEPIL3IntegratedPipeline` | `EPIL3Integration.lean:112` | (タグ無し、本体は `{ stam, bridge }` の 2 field) | #7-16 が thread する bundle。`bridge : IsStamToEPIBridgeHyp` が load-bearing |
| `def IsStamInequalityHyp` | `EPIStamDischarge.lean:100` | (genuine Fisher-info Stam 形) | bundle `.stam` field の型 |
| `def IsStamToEPIBridgeHyp` | `EPIStamDischarge.lean:365` | `@audit:ok` | bundle `.bridge` field の型。`stamToEPIBridge_holds` で discharge 可能 |
| `def IsStamInequalityResidual` | `EntropyPowerInequality.lean:190` | (`IsStamInequalityHyp` と defeq) | non-circular residual 形 |

## Context — consumer graph + blast radius (verbatim、要 Phase 0 精査)

`rg -nc '<predname>' Common2026/Shannon/` (2026-05-28) で確認した **重大な scope 境界
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

## Phase 0 — verbatim 棚卸し + scope 拡張判定 + 既存 wall 照合 📋

- [ ] **0-1**: 表 A の 19 declaration の signature + docstring + 既存タグを verbatim
      再確認 (本 plan で完了済、drift チェックのみ)
- [ ] **0-2**: 各 declaration の **hypothesis-form consumer** を
      `rg -n '<PredName>' Common2026/Shannon/` で列挙し、`.field` extract / 構成子 /
      docstring mention と分離 (表 A の「consumer 粗数」を hypothesis-form / extract /
      construct / mention に分解した精数表に更新)
- [ ] **0-3 (★ scope 拡張判定、L-EPISC-0-honest-defect の前段)**:
      `EPIStamDeBruijnConclusion.lean` の 4 declaration-level tag
      (`isStamInequalityHyp_of_primitives` 164 / `isStamInequalityHyp_of_stamDeBruijn` 197 /
      `isEPIL3IntegratedPipeline_of_stamDeBruijn` 210 / `entropy_power_inequality_via_stamDeBruijn` 227)
      + `structure IsEPIStamDeBruijnPipeline` (181) を本 plan scope に **含める**か判定:
      - `isEPIL3IntegratedPipeline_of_stamDeBruijn` は `IsEPIL3IntegratedPipeline` の
        **構成子** → bundle 削除時に連動必須 → **含める** がデフォルト
      - 含めない場合は pipeline bundle 削除が不可能 (構成子孤児化) なので、その場合
        Route C を「bundle を削除せず field 経由の load-bearing を除去」に降格
        (L-EPISC-3-α)
- [ ] **0-4**: 表 C の 2 shared wall lemma の **結論型** を verbatim Read で確認し、
      Route B 各 declaration (#1 #2 #3 #5) の「結論」を discharge 可能か照合
      (`debruijnIdentityV2_holds` の結論が `IsDeBruijnIntegrationHyp` の `∃ fPath, ∫...`
      を供給できるか / `stamToEPIBridge_holds` が `IsStamToEPIScalingHyp` の
      `AntitoneOn` を供給できるか)。**できない場合は新規 shared wall lemma を Phase 2 で補充**
- [ ] **0-5**: import 依存 verbatim 確認 —
      `FisherInfoV2DeBruijn.lean` (`debruijnIdentityV2_holds` 提供) /
      `EntropyPowerInequality.lean` (`stamToEPIBridge_holds` 提供) が各 consumer file から
      既に import 可能か (import cycle check)。`EPIStamToBridge` → `EntropyPowerInequality`
      の依存方向を verbatim 確認 (逆方向だと wall lemma 呼出に import 追加が必要)

## Phase 1 — Wall name register 確認 (`docs/audit/audit-tags.md`) 📋

**原則: 新規 wall 追加は不要** (`debruijn-integration` / `csiszar` 既存登録済)。

- [ ] **1-1**: `debruijn-integration` (register line 67) が #1 #2 を覆うことを確認
      (既存タグ `@residual(wall:debruijn-integration)` が `debruijnIdentityV2_holds` に
      付いている)
- [ ] **1-2**: `csiszar` (register line 57) が #3 を覆うか確認。Phase A 内部の
      `csiszarGap_antitoneOn_*` が既に `@residual(plan:epi-stam-to-conclusion-phaseA-plan)`
      を持つので、#3 は wall ではなく **plan slug** 委任の可能性 (Phase 0-4 結果次第)
- [ ] **1-3**: #5 `IsStamScalingNoiseHyp` (noise-extension richness `∃ Z_X Z_Y, ...`) が
      `csiszar` で足りるか、別 wall (`epi-n-dim` register line 64) が要るか判定。
      原則 `csiszar` 流用、不足時のみ Proposed 表に提案 (L-EPISC-4-γ)

## Phase 2 — shared sorry 補題の補充判定 📋

**原則: 新規 wall file (`EpiStamWalls.lean`) 新設は不要** (表 C の 2 補題で足りる見込み)。

- [ ] **2-1**: 表 C の `debruijnIdentityV2_holds` + `stamToEPIBridge_holds` で全 Route B
      declaration (#1 #2 #3 #5) が discharge 可能か Phase 0-4 結果で確定
- [ ] **2-2**: 不足分があれば既存 file (`StamGaussianBound.lean` / `FisherInfoV2DeBruijn.lean`
      / `EntropyPowerInequality.lean`) に shared sorry 補題を **補充**
      (`sorry` 1 + `@residual(wall:<name>)` 1)。新規 file 新設は L-EPISC-4-γ 例外時のみ
- [ ] **2-3**: 補充した場合のみ `Common2026.lean` import は既存 (新規 file 無しなら不要)
- [ ] **2-4**: 補充した補題の file を `lake env lean` で 0 errors / sorry warning のみ確認

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
- [ ] **3α-7**: `lake env lean Common2026/Shannon/EPIL3Integration.lean` 0 errors

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
- [ ] **3β-5**: `lake env lean Common2026/Shannon/EPIStamToBridge.lean`
      + `lake env lean Common2026/Shannon/HeatFlowPath.lean` 0 errors

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
- [ ] **3γ-3**: `lake env lean Common2026/Shannon/EPIStamDischarge.lean` 0 errors

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
- [ ] **3δ-4**: `lake env lean Common2026/Shannon/EntropyPowerInequality.lean`
      + `lake env lean Common2026/Shannon/EPIPlumbing.lean` 0 errors

## Phase V — closure 📋

- [ ] **V-1**: 全 touched file の `lake env lean` 検証 0 errors:
      `EPIL3Integration` / `EPIStamToBridge` / `HeatFlowPath` / `EPIStamDischarge` /
      `EntropyPowerInequality` / `EPIPlumbing` (+ scope 拡張時 `EPIStamDeBruijnConclusion`
      / `EPIStamInequalityBody`) / 補充時の wall file / `Common2026.lean`
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
  `Common2026/Shannon/EpiStamWalls.lean` を新設、shared sorry 補題を集約。
  `Common2026.lean` に import 1 行追加。wall name は既存 `debruijn-integration` / `csiszar`
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

<!-- 例:
1. **Phase 0-3 scope 拡張 (L-EPISC-0-honest-defect)**: `EPIStamDeBruijnConclusion.lean`
   の `isEPIL3IntegratedPipeline_of_stamDeBruijn` 構成子が pipeline bundle 削除に必須と
   判明、brief の 4 file を 5 file に正式拡張。
2. **Phase 0-4 既存 wall 流用確定**: `debruijnIdentityV2_holds` の結論型が
   `IsDeBruijnIntegrationHyp` の `∃ fPath, ∫...` を直接供給可能と verbatim 確認、
   L-EPISC-1-α 不発、新規 wall lemma 補充不要。
-->
