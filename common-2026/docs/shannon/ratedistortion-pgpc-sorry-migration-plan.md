# Shannon: RateDistortion + ParallelGaussianPerCoord `@audit:suspect` / `@audit:closed-by-successor` → sorry-based migration plan

> **Parents**:
> - RateDistortion 系: [`rate-distortion-achievability-plan.md`](rate-distortion-achievability-plan.md) /
>   [`rate-distortion-achievability-phase-e-strong-plan.md`](rate-distortion-achievability-phase-e-strong-plan.md) /
>   [`rate-distortion-convexity-plan.md`](rate-distortion-convexity-plan.md) /
>   [`rate-distortion-converse-plan.md`](rate-distortion-converse-plan.md)
> - PGPC 系: [`parallel-gaussian-l-pg1-discharge-plan.md`](parallel-gaussian-l-pg1-discharge-plan.md)
>   (✅ closed 2026-05-25) / [`parallel-gaussian-moonshot-plan.md`](parallel-gaussian-moonshot-plan.md)
>
> **SoT**: [`../audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) +
> [`../audit/audit-tags.md`](../audit/audit-tags.md)。Pilot reference: [`hoeffding-sorry-migration-plan.md`](hoeffding-sorry-migration-plan.md)。
>
> 本 plan は **proof completion ではなく** `@audit:suspect` / `@audit:closed-by-successor` 語彙の
> honesty 強化 (sorry-based 移行) を目的とする独立 workstream。Round 3 (大規模 + dependency 注意)
> の **逆検証結果** で escalate された 2 sub-family を統合する。

## Context

### 在庫差分 (verbatim 確認結果、2026-05-26)

**RateDistortion** — 5 file / 6 declarations、すべて `@audit:suspect()` (空 slug):

| file:line | decl 名 | tag |
|---|---|---|
| `RateDistortionConverseNLetter.lean:261` | `rate_distortion_converse_n_letter_singleLetter` | `@audit:suspect()` |
| `RateDistortionConvexity.lean:137` | `rateDistortionFunction_convexOn` | `@audit:suspect()` |
| `RateDistortionAchievabilityPhaseE.lean:86` | `rate_distortion_achievability_witness_form` | `@audit:suspect()` |
| `RateDistortionAchievabilityPhaseEDischarge.lean:284` | `rate_distortion_achievability_partial_discharge` | `@audit:suspect()` |
| `RateDistortionAchievabilityPhaseEStrongFinal.lean:736` | `codebookAvgFailureStrong_tendsto_zero` | `@audit:suspect()` |
| `RateDistortionAchievabilityPhaseEStrongFinal.lean:1638` | `rate_distortion_achievability` | `@audit:suspect()` |

合計 RateDistortion: **6 suspect**。空 slug `@audit:suspect()` は **plan slug 未記載 = closure 担当 plan 暗黙** のレガシー形態。

**ParallelGaussianPerCoord (PGPC)** — 2 file:

| file:line | decl 名 | tag |
|---|---|---|
| `ParallelGaussianPerCoord.lean:187` | `parallelGaussianCapacity_ge_sum` | `@audit:closed-by-successor(parallel-gaussian-l-pg1-discharge)` |
| `ParallelGaussianPerCoord.lean:207` | `parallelGaussianCapacity_le_sum` | `@audit:closed-by-successor(parallel-gaussian-l-pg1-discharge)` |
| `ParallelGaussianPerCoord.lean:256` | `parallelGaussian_max_ent_le_of_subadditivity` | `@audit:closed-by-successor(parallel-gaussian-l-pg1-discharge)` |
| `ParallelGaussianPerCoord.lean:302` | `isParallelGaussianPerCoordReduction_discharged` | `@audit:closed-by-successor(parallel-gaussian-l-pg1-discharge)` |
| `ParallelGaussianPerCoord.lean:366` | `parallel_gaussian_capacity_formula` | `@audit:closed-by-successor(parallel-gaussian-l-pg1-discharge)` |
| `ParallelGaussianPerCoordRegularity.lean:91` | `isParallelGaussianPerCoordRegularity_of_pieces` | `@audit:ok(parallel-gaussian-l-pg1-discharge)` |
| `ParallelGaussianPerCoordRegularity.lean:142` | `parallel_gaussian_capacity_formula_minimal` | `@audit:ok(parallel-gaussian-l-pg1-discharge)` |

PGPC 散文 `🟢ʰ` — 5 件 (`:45/:147/:153/:300/:358`)、全て docstring 内の **散文表現** で wrapper の honesty 状態を説明 (load-bearing tag そのものではなく、`IsParallelGaussianPerCoordRegularity` 構造体への参照ラベル)。

合計 PGPC: **5 `@audit:closed-by-successor` + 2 `@audit:ok` + 5 散文 🟢ʰ**。inventory 計測の「1 staged」は誤計数 (`ParallelGaussianPerCoordRegularity.lean:31` の `staged` は docstring 内文字列 "No new `@audit:staged(...)` predicate is introduced" の引用形)。

**既存 `sorry` 件数 (word-boundary 計測)**: `rg -nw 'sorry' <7 files>` で 5 hit、全 docstring 内文字列リテラル ⇒ **実 sorry 0 件**。Hoeffding pilot Pattern D と同型の誤計数なし。

**HONESTY ALERT / FALSE predicate**: `rg '⚠|HONESTY ALERT|FALSE'` で 0 hit (Pattern H scope 外)。

### Round 3 dependency 逆検証

`sorry-migration-runbook.md`「並列実行候補 family」Round 3 設計時に **PGPC は EPI/Stam 依存ありの可能性** と注記されていたが、実コード `rg -n 'import Common2026.Shannon.EPI|import Common2026.Shannon.Stam|wall:stam|wall:n-dim-gaussian-aep' Common2026/Shannon/ParallelGaussianPerCoord*.lean` で **0 hit**。逆方向 `rg -n 'ParallelGaussianPerCoord' Common2026/Shannon/EPI*.lean Common2026/Shannon/Stam*.lean` も 0 hit。

⇒ PGPC は EPI/Stam に **依存しない**。verbatim 確認で Round 3 仮定は否定された。
PGPC を独立 sweep として本 plan に統合できる (escalate 不要)。

ただし PGPC 内部の `IsParallelGaussianPerCoordRegularity` 構造体は同 family の **`ParallelGaussianKKT.lean` / `ParallelGaussianWFCertBody.lean` / `ParallelGaussianWFStationarityBody.lean` / `ParallelGaussianL_PG0Discharge.lean` から間接消費** されており、その点は cross-family ではなく **同 family 内の S2 import 実依存**として後述 Phase 2.PGPC で散文 transitive 化対応する。

### RateDistortion cross-family

`rg -n 'rate_distortion_converse_n_letter_singleLetter|rateDistortionFunction_convexOn|rate_distortion_achievability_witness_form|rate_distortion_achievability_partial_discharge|codebookAvgFailureStrong_tendsto_zero|rate_distortion_achievability\b' Common2026/ --type=lean | grep -v RateDistortion` で **1 hit**:

- `Common2026/Shannon/WynerZivConverseChain.lean:10` — docstring 散文 `... in the same style as rate_distortion_converse_n_letter_singleLetter ...` (import なし)。これは runbook Pattern G 3-段判定の **S1 (散文 reference)** = 本 sweep 単独で実施可能、Phase 2.RD で散文を更新するのみ (実際には WynerZiv 側のみが該当 declaration 名に言及しているので RD sweep が deprecate / signature 変更しても WynerZiv 側 prose の更新だけで済む)。

⇒ RateDistortion は cross-family escalate **不要**。S1 のみ。

### 上位 moonshot plan との関係

- **RateDistortion achievability plan** (`rate-distortion-achievability-plan.md`): すでに DONE-HONEST-HYPS で landing 済 (進捗 📋 は stale との明記、headline `rate_distortion_achievability` は `RateDistortionAchievabilityPhaseEStrongFinal.lean:1635` に publish、0 sorry / 0 axiom)。本 plan は **その landing 状態を変えない** — `@audit:suspect()` 空 slug を closure 担当 plan に紐付けた `@residual(plan:<slug>)` 形に置換する書換であって proof completion ではない。残る honest pass-through hyp (`h_jts_subset_dts` / rate-gap / KL-dominate / `hqStar_pos`) は本 plan で touch しない (load-bearing 性の判定は honesty-auditor 委任)。
- **RateDistortion convexity plan** (`rate-distortion-convexity-plan.md`): 同じく Phase B 主補題 + 有限アルファベット discharge 完了済 (`rateDistortionFunction_convexOn` は `h_klDiv_conv` を honest hyp 化した subnormal 形、0 sorry)。`RateDistortionConvexityDischarge.lean:694` で finite-alphabet 形が完全 discharge → 有限アルファベットでは DONE-UNCOND。
- **RateDistortion converse plan** (`rate-distortion-converse-plan.md` / `RateDistortionConverseNLetter.lean`): `h_super` (MI tensorization) + `h_jensen_antitone` (n-way Jensen + antitonicity) を hypothesis pass-through 形で受け、本体は計算 chain。
- **PGPC L-PG1 discharge plan** (`parallel-gaussian-l-pg1-discharge-plan.md`): ✅ closed 2026-05-25。`ParallelGaussianPerCoordRegularity.lean` の constructor + headline-minimal を提供し、`IsParallelGaussianPerCoordRegularity` 構造体の 3 field を honest pieces から組み立てる構造を確立。PGPC の 5 `@audit:closed-by-successor` タグは **後継 plan が完結した結果残された legacy tier-4 marker** であり、現状 sorry-based 移行で `@residual(plan:parallel-gaussian-l-pg1-discharge)` 形には変換しない (sorry は 0 件のため `@residual` 不要、closed-by-successor タグそのものが Deprecated 表上の対象)。

### Honesty workflow と DoD

`CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:
- 各 file `lake env lean Common2026/Shannon/<file>.lean` が 0 errors、
- 新規 `sorry` がある場合は `@residual(<class>:<slug>)` タグ付き、
- 各 Phase 完了時に `honesty-auditor` を起動して classification を独立検証。

`@audit:ok` (proof done) は **本 plan の出力にはならない** — `rate_distortion_achievability_witness_form` / `rate_distortion_achievability_partial_discharge` / `codebookAvgFailureStrong_tendsto_zero` の load-bearing predicate hypothesis (= mathematical Mathlib gap、e.g. `h_codebook_avg_failure` / `h_klDiv_conv` / `h_jts_subset_dts`) の analytical closure は別 workstream。

## Approach

**file 単位 sweep を 2 sub-family に分割**、共有 wall lemma は **集約しない** (理由は下記)。

### 戦略の選択軸

`sorry-migration-runbook.md`「並列度の判断軸」+ Hoeffding pilot Approach に従い、本 family について次のように決める:

1. **file 単位 sweep を採用** (incidental ではなく一括)。理由:
   - RateDistortion 6 declarations は **5 file に分散**しているが、それぞれが独立 predicate hypothesis (`h_super` / `h_jensen_antitone` / `h_klDiv_conv` / `h_codebook_avg_failure` / `h_jts_subset_dts` etc.) を取る独立 wrapper。incidental migration では空 slug `@audit:suspect()` の closure 担当 plan 紐付けが file 間で drift しやすい。
   - PGPC 5 declarations は **2 file** にまとまっており、後継 plan (`parallel-gaussian-l-pg1-discharge`) が既に closure 完了済の **legacy tier-4 tag のみ**。一括処理が機械的かつ低 risk。

2. **共有 sorry 補題に集約しない**。理由:
   - RateDistortion: `@audit:suspect()` 空 slug は closure 担当 plan が **複数候補** (achievability plan / convexity plan / converse plan / phase-e-strong plan)。declaration 単位で plan 紐付けを判定する (在庫表参照)。Mathlib 壁 (`wall:stam` 等) には該当せず、`audit-tags.md`「Wall name register」に登録された wall 名がない。「Proposed wall」表にも RateDistortion 系候補なし。
   - PGPC: 既に L-PG1 discharge plan が完結済で、5 件すべて同一の後継 plan slug。後継 plan は **既に in-tree で discharge 完了** (`isParallelGaussianPerCoordRegularity_of_pieces` + `parallel_gaussian_capacity_formula_minimal` で hypothesis-minimal headline まで提供済) なので、wall lemma 集約は二重実装。

⇒ 全件 `@residual` class は `plan:` で揃え、shared wall lemma の新規 file は不要。

### 移行レシピ (declaration 単位、3 パターン)

`audit-tags.md`「移行レシピ」+ Hoeffding pilot Pattern P/V/C をベースに、本 family では以下 3 パターン:

- **パターン P (load-bearing predicate hypothesis)**: signature が plan の **核心 claim** を hypothesis 形で取り、body は destructure / 計算 chain に組み込むだけ。
  - 移行: hypothesis を **削除**、結論型は変えない、body `sorry` + `@residual(plan:<closure 担当 slug>)`。
  - 注意: Mathlib 壁 candidate (Cover-Thomas 2.7.2 joint klDiv convexity、conditional method-of-types) に該当するが、本 plan では shared sorry 補題化せず plan slug で集約する。

- **パターン V (variational / regularity pass-through)**: signature が `IsProbabilityMeasure` / measurability / `hqStar_pos` / 量化 hypothesis を取り、body はそれらを passive に消費するだけ。
  - 移行: tag を `@audit:suspect()` から **削除**するだけ (residual を新規に作らない、type-check done のまま)。

- **パターン S (superseded-by-completed-plan、PGPC 専用)**: 後継 plan が既に完結済で hypothesis-minimal な後続版が in-tree で提供されている `@audit:closed-by-successor(<plan-slug>)` declaration。
  - 移行: `audit-tags.md`「Deprecated」表のレシピに従い `@audit:closed-by-successor` を **削除**するだけ (declaration 自身に sorry 無し → `@residual` 不要、依存先の sorry も無し → transitive 散文も不要)。
  - 後継版 `parallel_gaussian_capacity_formula_minimal` (`ParallelGaussianPerCoordRegularity.lean:142`) への migration 経路は既に L-PG1 discharge plan で提供済。

詳細な per-declaration の pattern 判定は次セクション「在庫」で示す。

### Phase 分割

- **Phase 0 — Inventory** (本 plan 起草で実施済): 7 file の verbatim 確認、cross-family / Round 3 dependency の S1/S2/S3 判定、wall name register 突合。
- **Phase 1 — V cleanup pass** (低 risk): パターン V に該当する declarations の `@audit:suspect()` タグ削除。signature 改変なし。
- **Phase 1.4 — audit-1** (`honesty-auditor` 起動、Phase 1 全件)。
- **Phase 2.RD.1 — RateDistortion file A**: `RateDistortionConverseNLetter.lean` の P retreat (1 declaration、`h_super` + `h_jensen_antitone` 削除予定)。
- **Phase 2.RD.2 — RateDistortion file B**: `RateDistortionConvexity.lean` の P retreat (1 declaration、`h_klDiv_conv` 削除予定)。
- **Phase 2.RD.3 — RateDistortion file C**: `RateDistortionAchievabilityPhaseE.lean` の P retreat (1 declaration、`h_codebook_avg_failure` + `h_failure_tendsto_zero` 削除予定)。
- **Phase 2.RD.4 — RateDistortion file D**: `RateDistortionAchievabilityPhaseEDischarge.lean` の P retreat (1 declaration、`rate_distortion_achievability_partial_discharge`、上記同様 codebook-avg-failure pass-through)。
- **Phase 2.RD.5 — RateDistortion file E**: `RateDistortionAchievabilityPhaseEStrongFinal.lean` の P/V retreat (2 declarations: `codebookAvgFailureStrong_tendsto_zero` 解析実体あり、`rate_distortion_achievability` 1638 は wrapper alias)。
- **Phase 2.PGPC — PGPC S cleanup**: `ParallelGaussianPerCoord.lean` 5 件 + `ParallelGaussianPerCoordRegularity.lean` 2 件の `@audit:closed-by-successor` / `@audit:ok` タグ整理 (Deprecated 表に従う)。
- **Phase 2.X — retract**: 必要に応じて load-bearing predicate を `@audit:retract-candidate(load-bearing-predicate)` 化 (本 family では predicate そのものが in-tree で defined されていないので **predicate 削除は対象外**、in-line hypothesis のみが対象)。
- **Phase 2.audit** (`honesty-auditor` 起動、Phase 2 全件)。
- **Phase V — verify**: 全 file `lake env lean` 0 errors + 親 plan banner + handoff 反映。

Phase 順を選んだ理由: Hoeffding pilot と同じく Phase 1 (低 risk、V のみ) を先行する。`RateDistortionAchievabilityPhaseEStrongFinal.lean:1638` (`rate_distortion_achievability` wrapper alias) は **Phase 1 V** に分類されるが、`:736` (`codebookAvgFailureStrong_tendsto_zero`) は **Phase 2.RD.5 P** に分類される。同一 file 内で V と P が共存するため、Phase 1 → Phase 2 順を守ると olean refresh のタイミングが明確 (Pilot Pattern A 対策)。

## 在庫: 6 + 5 declarations の verbatim 分類

各 declaration の `path:line` は `@audit:*` タグ行 (docstring 末尾)。declaration 名はその直後。「suspect の核」は 1 行散文要約 (verbatim docstring + signature 1-2 行を読込済)。

### RateDistortion 系 (6 declarations)

| file:line | decl 名 | suspect の核 (1 行) | パターン | 移行後 class:slug | 備考 |
|---|---|---|---|---|---|
| `RateDistortionConverseNLetter.lean:261` | `rate_distortion_converse_n_letter_singleLetter` | `h_super` (MI tensorization `∑ I(Xᵢ;X̂ᵢ) ≤ I(X^n;X̂^n)`) + `h_jensen_antitone` (n-way Jensen + antitonicity bundle) を hypothesis pass-through、body の calc chain で直接消費 | **P** | `plan:rate-distortion-converse-plan` | `h_super` は Mathlib 不在 (MI tensorization for finite block; Pattern G 候補ではない)、`h_jensen_antitone` は antitonicity + Jensen の compose hypothesis。signature 改変で 2 hyp 削除、body `sorry`。`WynerZivConverseChain.lean:10` の散文 reference は本 declaration 名を mention のみで S1。Phase 2.RD.1 |
| `RateDistortionConvexity.lean:137` | `rateDistortionFunction_convexOn` | `h_klDiv_conv` (joint klDiv convexity Cover-Thomas 2.7.2、Mathlib gap) + `h_int_witness` (feasible witness の integrability) を hypothesis 化した **subnormal 形**。body は per-pair bound + RHS factorization (genuine constructive)。convexity 主補題自身が hypothesis bundle | **P** | `plan:rate-distortion-convexity-plan` | `RateDistortionConvexityDischarge.lean:694` `rateDistortionFunction_convexOn_pmf` が **完全 discharge** 済 (有限アルファベット形、0 sorry / 0 axiom)。`h_klDiv_conv` は load-bearing で削除対象、`h_int_witness` は regularity hyp として残す候補 (auditor 判定)。Phase 2.RD.2 |
| `RateDistortionAchievabilityPhaseE.lean:86` | `rate_distortion_achievability_witness_form` | witness-form (MVP)、`h_codebook_avg_failure` (Phase C-style Fubini bridge) + `h_failure_tendsto_zero` (random-coding failure decay) を hypothesis pass-through。body は failure_seq → 0 を介した witness 構成 (genuine pigeon-hole + bound chain) | **P** | `plan:rate-distortion-achievability-phase-e-strong-plan` | `h_codebook_avg_failure` が load-bearing (Phase C-style closure 待ち)。`h_failure_tendsto_zero` も typically load-bearing だが strong-typicality track では in-tree で discharge 済 (`codebookAvgFailureStrong_tendsto_zero` 経由)。signature 改変で 2 hyp 削除候補。Phase 2.RD.3 |
| `RateDistortionAchievabilityPhaseEDischarge.lean:284` | `rate_distortion_achievability_partial_discharge` | `rate_distortion_achievability_witness_form` の partial discharge wrapper (ambient i.i.d. internally discharged)、外部 hyp は `h_codebook_avg_failure` + `h_failure_tendsto_zero` のみ。body は witness_form への delegation | **P** | `plan:rate-distortion-achievability-phase-e-strong-plan` | 上記 file C と同形のため同じ slug。Phase 2.RD.4 |
| `RateDistortionAchievabilityPhaseEStrongFinal.lean:736` | `codebookAvgFailureStrong_tendsto_zero` | strong-encoder failure sequence の `tendsto_zero` 主補題。body は ~870 行の **genuine probabilistic analysis** (conditional method-of-types AEP, joint typicality, etc.)。`@audit:suspect()` は `hqStar_pos` (strict positivity、perturbation 未着手) + `h_jts_subset_dts` (strong-JTS ⊆ distortion-typical bridge) + rate-gap/KL-dominate caller-supplied bounds の **load-bearing 度合いの境界例** を表明 | **P / V 境界例** | `plan:rate-distortion-achievability-phase-e-strong-plan` (P 部分) | body は genuine だが、hypothesis 群の **どれが load-bearing か** は honesty-auditor 判定対象。デフォルト判断: (a) `hqStar_pos` = regularity (V)、(b) `h_jts_subset_dts` = load-bearing (P、削除 + sorry)、(c) rate-gap/KL-dominate = caller-supplied bound (V、削除不要)。デフォルトでは tag 削除 + 残存 `h_jts_subset_dts` は **保持** (auditor で削除すべきか判定)、本体は genuine のままなので **sorry 不要** 候補。Phase 2.RD.5 |
| `RateDistortionAchievabilityPhaseEStrongFinal.lean:1638` | `rate_distortion_achievability` | **public alias wrapper**、body は `rate_distortion_achievability_strong` (`:1377` 等)への直接 delegation。conclusion 型 ≡ `_strong` の conclusion、hypothesis は同型を passive 受け渡し | **V (wrapper alias)** | (タグ削除のみ) | `_strong` 版が genuine closure 提供済 (`hqStar_pos` 等を内部で消費)。本 wrapper は API 公開のための rename。Phase 1 で `@audit:suspect()` タグ削除のみ |

集計 (パターン別):
- P (predicate / load-bearing hyp 削除 + `sorry` 化): **4 件** (Phase 2.RD.1〜2.RD.4)
- P/V 境界例 (auditor 判定): **1 件** (`codebookAvgFailureStrong_tendsto_zero`、Phase 2.RD.5、デフォルト V 寄り)
- V (純 wrapper alias / pass-through): **1 件** (`rate_distortion_achievability` :1638、Phase 1)

### ParallelGaussianPerCoord 系 (5 + 2 declarations)

| file:line | decl 名 | tag / 核 (1 行) | パターン | 移行後 | 備考 |
|---|---|---|---|---|---|
| `ParallelGaussianPerCoord.lean:187` | `parallelGaussianCapacity_ge_sum` | 後継 plan (L-PG1 discharge) で `h_reg : IsParallelGaussianPerCoordRegularity` を honest pieces から組み立てる経路が確立済。body は `le_csSup` + achiever feasibility (genuine constructive) | **S (superseded by completed plan)** | (タグ削除のみ) | `audit:closed-by-successor` Deprecated 表に従い**タグ削除**。declaration 自身に sorry 無し、依存先 (`IsParallelGaussianPerCoordRegularity`) も後継 plan で hypothesis-minimal 化済 ⇒ `@residual` 不要。Phase 2.PGPC |
| `ParallelGaussianPerCoord.lean:207` | `parallelGaussianCapacity_le_sum` | 上記同様、`h_reg.max_ent` + L-WF2 を消費した csSup_le。body は genuine | **S** | (タグ削除のみ) | 同上。Phase 2.PGPC |
| `ParallelGaussianPerCoord.lean:256` | `parallelGaussian_max_ent_le_of_subadditivity` | `jointDifferentialEntropyPi_le_sum` (genuine subadditivity) を介した max_ent reduction。`h_decomp` / `h_perCoord` 等 honest pieces を hypothesis 化、body は subadditivity 適用 (genuine) | **S** | (タグ削除のみ) | 同上。Phase 2.PGPC |
| `ParallelGaussianPerCoord.lean:302` | `isParallelGaussianPerCoordReduction_discharged` | 段 1 — `IsParallelGaussianPerCoordReduction` の sup-sandwich 形 closure。body は `le_antisymm` of `_le_sum` / `_ge_sum` (genuine) | **S** | (タグ削除のみ) | 同上。Phase 2.PGPC |
| `ParallelGaussianPerCoord.lean:366` | `parallel_gaussian_capacity_formula` | 段 2 — non-circular capacity 公式 headline。body は `isParallelGaussianPerCoordReduction_discharged` への delegation (genuine `le_antisymm`、`:= h_per_coord` ではない) | **S** | (タグ削除のみ) | 同上。Phase 2.PGPC |
| `ParallelGaussianPerCoordRegularity.lean:91` | `isParallelGaussianPerCoordRegularity_of_pieces` | constructor、honest 3 pieces から `IsParallelGaussianPerCoordRegularity` を組み立てる (Phase 1-4 完了済の constructor、body は `refine { ... }` で 3 field 充填、0 sorry) | (タグそのまま) | (タグそのまま、変更不要) | 既に `@audit:ok(...)` で proof done 表明。本 plan で touch しない |
| `ParallelGaussianPerCoordRegularity.lean:142` | `parallel_gaussian_capacity_formula_minimal` | hypothesis-minimal headline、`h_reg` を unfold 化、body は constructor + headline へ delegation (genuine) | (タグそのまま) | (タグそのまま、変更不要) | 同上 |

集計 (パターン別):
- S (PGPC superseded、タグ削除のみ): **5 件** (Phase 2.PGPC)
- 変更不要 (`@audit:ok` 既に proof done): **2 件**

### PGPC 散文 🟢ʰ — 5 件 (本 plan touch なし)

`ParallelGaussianPerCoord.lean:45/:147/:153/:300/:358` の 🟢ʰ は **docstring 散文表現**で `IsParallelGaussianPerCoordRegularity` 構造体への参照ラベルとして使用。Hoeffding pilot Pattern (`🟢ʰ load-bearing hypothesis`) とは異なり、独立の audit tag ではない (= load-bearing 表明ではなく、honest pieces への解説テキスト)。本 plan では **touch しない** (Deprecated 表「散文 🟢ʰ」の対象外 — 既に後継 plan で honest pieces として正式 publish 済)。

### S2 同 family 内 import 依存 (Phase 2.PGPC で確認)

`IsParallelGaussianPerCoordRegularity` 構造体 (`ParallelGaussianPerCoord.lean:156`) を hypothesis として消費する 同 family file:

- `ParallelGaussianKKT.lean:289` `isParallelGaussianPerCoordReduction_of_bundle` — `bundle : IsParallelGaussianPerCoordReduction` を hypothesis 形に取る (Reduction predicate そのものを passthrough)
- `ParallelGaussianKKT.lean:307` `bundle_of_isParallelGaussianPerCoordReduction` — 逆方向 reduction wrapper
- `ParallelGaussianWFCertBody.lean:355` / `ParallelGaussianWFStationarityBody.lean:170` / `ParallelGaussianL_PG0Discharge.lean:151` — 上記 KKT wrapper を消費

これら **同 family 内の S2 import 依存**は、本 plan の Phase 2.PGPC でタグ削除 (signature 改変なし) だけを行うため**波及なし**。olean refresh も不要 (signature 維持)。Pattern A (stale olean) 回避策は formally 不要だが、念のため Phase V で `lake env lean Common2026/Shannon/ParallelGaussianKKT.lean` 1 件のみ再 verify。

## Phase 詳細

### Phase 0 — Inventory ✅

- [x] 7 file の verbatim 確認 (本 plan 起草で実施済、上記「在庫差分」参照)
- [x] cross-family 判定: RateDistortion = S1 のみ (`WynerZivConverseChain.lean:10` 散文 mention のみ)、PGPC = 同 family 内 S2 (波及なし)
- [x] Round 3 PGPC EPI/Stam dependency 仮定の逆検証 — **依存なし** を確認
- [x] wall name register 突合: 該当 wall なし (`stam` / `csiszar` / `n-dim-gaussian-aep` 等いずれも該当しない)
- [x] HONESTY ALERT / FALSE predicate 0 件確認
- [x] 既存 sorry word-boundary 計測: 0 件

**proof-log**: no (inventory のみ)。

### Phase 1 — V cleanup pass (低 risk、新規 sorry なし) 📋

- [ ] **1.1** `RateDistortionAchievabilityPhaseEStrongFinal.lean:1638` `rate_distortion_achievability` (V wrapper alias) の `@audit:suspect()` タグ削除。signature 改変不要、`_strong` 版へ delegation する body もそのまま。
  - `lake env lean Common2026/Shannon/RateDistortionAchievabilityPhaseEStrongFinal.lean` で type-check done 確認。
- [ ] **1.2** PGPC 5 declarations の **Phase 2.PGPC** で行う `@audit:closed-by-successor` タグ削除は技術的には Phase 1 と同型の低 risk 操作だが、PGPC sub-family として独立 sweep するため Phase 2.PGPC に分離 (本 plan の sub-family 設計上の整理)。

**Phase 1 DoD**: 1 件で `@audit:suspect()` 0 件、新規 `sorry` 0 件、`lake env lean Common2026/Shannon/RateDistortionAchievabilityPhaseEStrongFinal.lean` 0 errors。

**proof-log**: no (mechanical tag removal、interesting なし)。

### Phase 1.4 — audit-1 📋

- [ ] `honesty-auditor` (general-purpose with audit-tags.md SoT brief) 起動。対象: Phase 1 で touch した 1 declaration。`@audit:suspect()` 空 slug 削除の妥当性 (= wrapper alias であり load-bearing でない) を独立検証。verdict 確認後 commit。

**proof-log**: no。

### Phase 2.RD.1 — `RateDistortionConverseNLetter.lean` P retreat 📋

- [ ] **2.RD.1.a** `rate_distortion_converse_n_letter_singleLetter` (`:262`):
  - signature 改変: `h_super` (MI tensorization) + `h_jensen_antitone` (n-way Jensen + antitonicity bundle) を **削除**。結論型は変えない (`R.toReal ≤ (1/n) * log M` のまま)。
  - 残す hyp (regularity / passive): `[Fintype α]` / `[Fintype β]` / measurability (`hencoder` / `hdecoder` / `hXs`) / `hXs_law` (i.i.d. distribution) / `h_MI_block_finite` / `h_MI_perletter_finite`。
  - body: `sorry` + docstring 末尾に `@residual(plan:rate-distortion-converse-plan)` を **書き込む** (旧 `@audit:suspect()` 行を置換)。
  - `lake env lean Common2026/Shannon/RateDistortionConverseNLetter.lean` 0 errors 確認。

**Phase 2.RD.1 DoD**: 1 件で `@audit:suspect()` 0 件、`@residual(plan:rate-distortion-converse-plan)` タグ付き `sorry` 1 件、`lake env lean` 0 errors。

**proof-log**: no (signature 改変 mechanical)。

### Phase 2.RD.2 — `RateDistortionConvexity.lean` P retreat 📋

- [ ] **2.RD.2.a** `rateDistortionFunction_convexOn` (`:138`):
  - signature 改変: `h_klDiv_conv` (joint klDiv convexity、Cover-Thomas 2.7.2) を **削除**。`h_int_witness` は regularity hyp 候補で残す (auditor 判定対象、Phase 2.audit で再評価)。
  - 残す hyp: `[Fintype α]` / `[Fintype β]` / `(d : α → β → ℝ)` / `(P : Measure α) [IsProbabilityMeasure P]` / `(hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)` / `(D₁ D₂ : ℝ)`。
  - 結論型: `rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂) ≤ ENNReal.ofReal lam * R(D₁) + ENNReal.ofReal (1 - lam) * R(D₂)` のまま。
  - body: `sorry` + docstring 末尾に `@residual(plan:rate-distortion-convexity-plan)` を書き込む。
  - `RateDistortionConvexityDischarge.lean:694` の `rateDistortionFunction_convexOn_pmf` が finite-alphabet で完全 discharge 済 → Phase 2.audit で「declaration 単独で見ると plan slug closure 候補が複数 (convexity-plan / phase-b22-plan)」の境界判定対象。デフォルト convexity-plan。
  - `lake env lean Common2026/Shannon/RateDistortionConvexity.lean` 0 errors 確認。

**Phase 2.RD.2 DoD**: 1 件で `@audit:suspect()` 0 件、`@residual(plan:rate-distortion-convexity-plan)` タグ付き `sorry` 1 件、`lake env lean` 0 errors。

**proof-log**: no。

### Phase 2.RD.3 — `RateDistortionAchievabilityPhaseE.lean` P retreat 📋

- [ ] **2.RD.3.a** `rate_distortion_achievability_witness_form` (`:87`):
  - signature 改変: `h_codebook_avg_failure` (Phase C-style Fubini bridge) + `h_failure_tendsto_zero` (random-coding failure decay) を **削除**。`failure_seq` 量化引数 + `h_failure_nn` も bundle として削除。
  - 残す hyp: ambient probability space (`μ` / `Xs` / `Ys` / measurability / `IsProbabilityMeasure`) / `qStar` membership in `RDConstraint` / rate `R > mutualInfoPmf qStar` / slack `ε'` / distortion bridge `h_dist_eq` / slack budget `h_slack` / `δ_typ`。
  - 結論型: `∃ N, ∀ n ≥ N, ∃ M c, c.expectedBlockDistortion ≤ D + ε'` のまま。
  - body: `sorry` + `@residual(plan:rate-distortion-achievability-phase-e-strong-plan)` を書き込む。
  - `lake env lean Common2026/Shannon/RateDistortionAchievabilityPhaseE.lean` 0 errors 確認。

**Phase 2.RD.3 DoD**: 1 件で `@audit:suspect()` 0 件、`@residual(plan:rate-distortion-achievability-phase-e-strong-plan)` タグ付き `sorry` 1 件、`lake env lean` 0 errors。

**proof-log**: no。

### Phase 2.RD.4 — `RateDistortionAchievabilityPhaseEDischarge.lean` P retreat 📋

- [ ] **2.RD.4.a** `rate_distortion_achievability_partial_discharge` (`:285`):
  - signature 改変: `h_codebook_avg_failure` + `h_failure_tendsto_zero` + `h_failure_nn` + `failure_seq` を **削除** (witness_form と同形)。`ε` / `δ_typ` / `hδ_typ` は残す (passive bound)。
  - 残す hyp: `P_X_pmf` / `d` / `D` / `qStar` membership / `R` / `ε'` / `h_slack` / `ε` / `δ_typ`。
  - 結論型: `∃ N, ∀ n ≥ N, ∃ M c, ... ≤ D + ε'` のまま。
  - body: 元 body は `rate_distortion_achievability_witness_form` への delegation だったが、signature 改変で hypotheses 不足になるため **body 全体を `sorry`** に置換。`@residual(plan:rate-distortion-achievability-phase-e-strong-plan)` を書き込む。
  - **Pattern C (transitive sorry) の散文化**: upstream `rate_distortion_achievability_witness_form` も sorry になるため、本 declaration の sorry は transitive。docstring 散文に「Transitive sorry via `rate_distortion_achievability_witness_form` (Phase 2 retreat)」を明示。本 declaration に `@residual` を **付与する** (transitive ではあるが、本 wrapper は partial-discharge の独立 statement なので独自の `@residual(plan:...)` を持つ — Hoeffding pilot Pattern C は "tag 付与しない" を推奨するが、ここでは declaration が独立 publish される statement のため `@residual` 付与する判断、honesty-auditor で再評価)。
  - `lake env lean Common2026/Shannon/RateDistortionAchievabilityPhaseEDischarge.lean` 0 errors 確認。

**Phase 2.RD.4 DoD**: 1 件で `@audit:suspect()` 0 件、`@residual(plan:rate-distortion-achievability-phase-e-strong-plan)` タグ付き `sorry` 1 件、`lake env lean` 0 errors。

**proof-log**: yes (`docs/shannon/proof-log-ratedistortion-pgpc-sorry-migration-phase2-rd4.md`)。理由: Pattern C transitive sorry の `@residual` 付与可否判定が **既存 pilot と異なる**判断 (Hoeffding は付与しない、本 plan は付与提案)、判断理由を残す。

### Phase 2.RD.5 — `RateDistortionAchievabilityPhaseEStrongFinal.lean` P/V retreat 📋

- [ ] **2.RD.5.a** `codebookAvgFailureStrong_tendsto_zero` (`:737`):
  - body は ~870 行の genuine probabilistic analysis のため **body は touch しない**。
  - signature 改変対象: `h_jts_subset_dts` (strong-JTS ⊆ distortion-typical bridge、load-bearing) のみ削除候補。`hqStar_pos` (strict positivity、perturbation = regularity) / rate-gap / KL-dominate (caller-supplied bounds、passive) は残す。
  - **デフォルト判断**: `h_jts_subset_dts` 削除すると body の typicality 推論が崩れる可能性が高く、Phase 2.audit で auditor 判定対象。delete せず **tag 削除のみ** (V 寄り扱い) で進める案を採用。`@audit:suspect()` を削除して `@residual` を新規付与しない。
  - 代替案 (L-MIG-1 発動時): `h_jts_subset_dts` 削除 + body 全体 `sorry` + `@residual(plan:rate-distortion-achievability-phase-e-strong-plan)`。
  - `lake env lean Common2026/Shannon/RateDistortionAchievabilityPhaseEStrongFinal.lean` 0 errors 確認。

- [ ] **2.RD.5.b** Phase 1 で削除済の `rate_distortion_achievability` (`:1639`) を再確認 (Phase 1 と Phase 2.RD.5 が同 file を touch するため olean refresh 確認、Pilot Pattern A 対策)。

**Phase 2.RD.5 DoD**: 1 件で `@audit:suspect()` 0 件 (`codebookAvgFailureStrong_tendsto_zero` から削除のみ)、新規 `sorry` 0 件 (デフォルト判断時)、`lake env lean` 0 errors。

**proof-log**: yes (`docs/shannon/proof-log-ratedistortion-pgpc-sorry-migration-phase2-rd5.md`)。理由: P/V 境界例 (`codebookAvgFailureStrong_tendsto_zero`) の判定理由を残す。auditor 判定が DEFECT なら L-MIG-1 発動。

### Phase 2.PGPC — PGPC S cleanup 📋

- [ ] **2.PGPC.a** `ParallelGaussianPerCoord.lean` 5 declarations の `@audit:closed-by-successor(parallel-gaussian-l-pg1-discharge)` タグ削除:
  - `:188` `parallelGaussianCapacity_ge_sum`
  - `:208` `parallelGaussianCapacity_le_sum`
  - `:257` `parallelGaussian_max_ent_le_of_subadditivity`
  - `:303` `isParallelGaussianPerCoordReduction_discharged`
  - `:367` `parallel_gaussian_capacity_formula`
  - **タグ削除のみ**、signature / body 改変なし。`audit-tags.md`「Deprecated」表 `@audit:closed-by-successor(SLUG)` 行に従い「wrapper 自身に sorry があれば `@residual(plan:<SLUG>)` に置換、無ければタグ削除」のうち **後者** (sorry 無し ⇒ タグ削除)。

- [ ] **2.PGPC.b** `ParallelGaussianPerCoordRegularity.lean` 2 declarations はそのまま (`@audit:ok` 既に proof done 表明、Deprecated 対象外)。本 plan で touch しない。

- [ ] **2.PGPC.c** PGPC 散文 🟢ʰ (5 件、`:45/:147/:153/:300/:358`) は docstring 散文表現として残置。L-PG1 discharge plan が確立した「honest pieces への解説テキスト」であり、Deprecated 表「散文 🟢ʰ / 🟢ʰ load-bearing hypothesis」は load-bearing hyp 表明用語であって、本 PGPC の文脈 (structure field への参照ラベル) とは異なる用法。Phase 2.audit で auditor が tier-4 deprecated 表現として detect する可能性あり、その場合 docstring を refine。

- [ ] **2.PGPC.d** `lake env lean Common2026/Shannon/ParallelGaussianPerCoord.lean` + `Common2026/Shannon/ParallelGaussianPerCoordRegularity.lean` 0 errors 確認。同 family 内 S2 import 依存 file の olean refresh: `lake env lean Common2026/Shannon/ParallelGaussianKKT.lean` 1 件のみ念のため再 verify (タグ削除のみで signature 変更なし、波及は想定上 0)。

**Phase 2.PGPC DoD**: 5 件で `@audit:closed-by-successor(...)` 0 件、新規 `sorry` 0 件、`lake env lean` 0 errors。`Common2026.lean` import 行変更なし。

**proof-log**: no (mechanical tag removal)。

### Phase 2.X — retract 📋

- [ ] 本 family では in-tree で defined された load-bearing predicate / structure は **存在しない** (Hoeffding pilot の `IsHoeffdingInteriorMinimizer` / `IsHoeffdingLagrangeHyp` 相当なし)。`IsParallelGaussianPerCoordRegularity` は structure であり、L-PG1 discharge plan で hypothesis-minimal 後継版がすでに publish 済 (`parallel_gaussian_capacity_formula_minimal`) — `@audit:retract-candidate` 付与は不要 (既に retract path が確立済)。`RDConstraint` / `mutualInfoPmf` / `LossyCode` 等の RateDistortion data structure は **proof done の primitive** であり retract 対象外。
- [ ] **Phase 2.X は no-op** で close。

**proof-log**: no。

### Phase 2.audit 📋

- [ ] `honesty-auditor` 起動。対象: Phase 2.RD.1〜2.RD.5 + Phase 2.PGPC で touch した 11 declaration。
  - signature の honesty (循環 `:= h` / `:True` slot / 退化定義悪用 / load-bearing hyp bundling) の structural check
  - `@residual(plan:<slug>)` classification の妥当性 (closure 担当 plan 紐付けが正しいか、特に Phase 2.RD.2 convexity-plan vs phase-b22-plan の judgement、Phase 2.RD.4 transitive `@residual` 付与の判断)
  - shared sorry 補題の集約状態 (本 family では集約しない判断、auditor で再評価)
  - deprecated タグの残置 (PGPC 散文 🟢ʰ 5 件の扱い、Phase 2.PGPC.c の refine 判断)
  - **Phase 2.RD.5 P/V 境界例 (`codebookAvgFailureStrong_tendsto_zero`)** の load-bearing 判定 — DEFECT なら L-MIG-1 発動
- [ ] verdict 確認後 commit。

**proof-log**: no (auditor 独立判定)。

### Phase V — verify + plan の集約 📋

- [ ] **V.1** 全 7 file で `lake env lean` 確認。Phase 2.RD で signature 改変 4 件 (Phase 2.RD.1〜2.RD.4) があったため、dependent file の olean refresh:
  ```bash
  lake build Common2026.Shannon.RateDistortionConverseNLetter
  lake build Common2026.Shannon.RateDistortionConvexity
  lake build Common2026.Shannon.RateDistortionAchievabilityPhaseE
  lake build Common2026.Shannon.RateDistortionAchievabilityPhaseEDischarge
  ```
  その後 `RateDistortionAchievabilityPhaseEStrongFinal.lean` (Phase 2.RD.5 の上流) を再 verify。
- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg '@audit:suspect' Common2026/Shannon/RateDistortion*.lean | wc -l   # = 0
  rg '@audit:closed-by-successor' Common2026/Shannon/ParallelGaussianPerCoord*.lean | wc -l   # = 0
  rg '@residual\(plan:rate-distortion-' Common2026/Shannon/RateDistortion*.lean | wc -l
  rg -nw 'sorry' Common2026/Shannon/RateDistortion*.lean Common2026/Shannon/ParallelGaussianPerCoord*.lean
  ```
- [ ] **V.3** 親 plan banner 更新:
  - `rate-distortion-achievability-plan.md` 冒頭に sorry-based 移行完了の追記
  - `rate-distortion-convexity-plan.md` 冒頭に同
  - `rate-distortion-converse-plan.md` 冒頭に同
  - `rate-distortion-achievability-phase-e-strong-plan.md` 冒頭に同
  - `parallel-gaussian-l-pg1-discharge-plan.md` 冒頭 (✅ closed 済) に「Phase 5 legacy tag 削除完了」追記
- [ ] **V.4** 発見 finding を `.claude/handoff-sorry-migration.md` または後続 family plan 用テンプレートに反映:
  - `@audit:suspect()` **空 slug** の closure 担当 plan 推定方法 (本 plan では declaration 単位 verbatim 確認 + 親 plan match で確定、後続 family で同パターンあれば同手順)
  - `@audit:closed-by-successor(SLUG)` の **後継 plan 完結後** タグ削除 vs `@residual(plan:<SLUG>)` 置換の判断軸 (本 plan は sorry 無し ⇒ タグ削除を採用、Deprecated 表「sorry が同 file にあれば置換、無ければ削除」に準拠)
  - **Round 3 dependency 仮定の verbatim 逆検証** が PGPC で実証されたパターン (runbook の Round 3 設計時 dependency 仮定 → 実コード `rg` 逆検証で否定、独立 sweep 可能と判明) — 後続の大規模 family (EPI/Stam / AWGN 200+ 行 bundle) でも同手順を推奨

**proof-log**: no (verify + bookkeeping)。

## 撤退ライン

- **L-MIG-1 (Phase 2.RD.5 `codebookAvgFailureStrong_tendsto_zero` の `h_jts_subset_dts` が auditor で load-bearing 判定された場合)**: デフォルト判断 (タグ削除のみ) を撤回し、`h_jts_subset_dts` 削除 + body 全体 `sorry` + `@residual(plan:rate-distortion-achievability-phase-e-strong-plan)` に降格。同 file 内の `rate_distortion_achievability_strong` (`:1377` 等) 等 ~870 行の genuine body は失われるが、honesty 優先。

- **L-MIG-2 (Phase 2.RD.4 transitive `@residual` 付与判断が auditor で questionable)**: Hoeffding pilot Pattern C「transitive sorry には `@residual` 付与しない」を採用し直し、本 plan の `@residual(plan:rate-distortion-achievability-phase-e-strong-plan)` を削除 + docstring 散文で transitive 性のみ明示。`audit-tags.md` EBNF 拡張提案 (transitive suffix) は本 plan の scope 外、別 PR 候補。

- **L-MIG-3 (Phase 2.RD.2 `rateDistortionFunction_convexOn` の plan slug 紐付けが auditor で questionable)**: `plan:rate-distortion-convexity-plan` vs `plan:rate-distortion-achievability-phase-b22-plan` の境界例。auditor が phase-b22 plan 紐付けが正しいと判定した場合は slug 置換 (mechanical refine、L-MIG 発動とは別)。

- **L-MIG-4 (Phase 2.PGPC で同 family S2 file の type drift)**: `ParallelGaussianPerCoord.lean` 5 件のタグ削除のみで signature 変更なしのため波及 0 が想定だが、もし `ParallelGaussianKKT.lean` / `ParallelGaussianWFCertBody.lean` / `ParallelGaussianWFStationarityBody.lean` / `ParallelGaussianL_PG0Discharge.lean` で type error が出た場合は Phase 2.PGPC を一旦 revert、再調査。

- **L-MIG-5 (Approach 変更: pilot scope を縮める)**: Phase 2 が 1 セッションで完走しない / honesty-auditor が DEFECT を多発させる場合、RateDistortion sub-family のみで pilot を close し、PGPC sub-family は後続 family sweep として別 plan に分離。

## 未決事項

1. **`@audit:suspect()` 空 slug の closure 担当 plan 紐付け**: 在庫表でデフォルト紐付けを示した:
   - `RateDistortionConverseNLetter.lean:261` → `rate-distortion-converse-plan`
   - `RateDistortionConvexity.lean:137` → `rate-distortion-convexity-plan`
   - `RateDistortionAchievabilityPhaseE.lean:86` → `rate-distortion-achievability-phase-e-strong-plan`
   - `RateDistortionAchievabilityPhaseEDischarge.lean:284` → `rate-distortion-achievability-phase-e-strong-plan`
   - `RateDistortionAchievabilityPhaseEStrongFinal.lean:736` → デフォルト V 扱い (タグ削除のみ)、auditor 判定で P 化なら `rate-distortion-achievability-phase-e-strong-plan`
   - `RateDistortionAchievabilityPhaseEStrongFinal.lean:1638` → V wrapper alias、タグ削除のみ

   Phase 2.audit で auditor が plan 紐付けの妥当性を verify。L-MIG-3 候補 (convexity vs phase-b22) は judgement border 例。

2. **Phase 2.RD.4 transitive sorry の `@residual` 付与方針**: Hoeffding pilot Pattern C は付与しない方針だったが、本 plan の `rate_distortion_achievability_partial_discharge` は独立 publish される statement のため独自 `@residual` を持つ判断をデフォルトとした。Phase 2.audit で再評価。L-MIG-2 候補。

3. **`codebookAvgFailureStrong_tendsto_zero` の V/P 判定 (Phase 2.RD.5)**: デフォルト V (タグ削除のみ) で進めるが、`h_jts_subset_dts` の load-bearing 度合いは auditor 委任。L-MIG-1 候補。

4. **PGPC 散文 🟢ʰ 5 件 (`ParallelGaussianPerCoord.lean:45/:147/:153/:300/:358`) の扱い**: 本 plan ではそのまま残置 (L-PG1 discharge plan が確立した解説テキスト)、L-PG1 plan が完結済のため独立 retain 判断可能。Phase 2.audit で deprecated 表現として refine 推奨が出た場合のみ docstring 文言調整 (mechanical)。

5. **proof done を本 plan で目指さない方針の明示確認**: 本 plan の DoD は **type-check done** のみ。RateDistortion achievability / convexity / converse の analytical closure (Cover-Thomas 2.7.2 / Phase C-style Fubini / MI tensorization 等) は **未着手のまま**で本 plan は close する。各親 plan の defer 状態は変えない。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-26 plan 起草** (lean-planner agent): 7 file (`RateDistortion*.lean` 5 + `ParallelGaussianPerCoord*.lean` 2) の verbatim 読込で `@audit:suspect()` 6 件 + `@audit:closed-by-successor(parallel-gaussian-l-pg1-discharge)` 5 件 + `@audit:ok` 2 件を確認。runbook 「並列実行候補 family」表の集計 (RateDistortion 2 suspect、PGPC 0 suspect + 1 staged + 5 closed + 5 🟢ʰ) と実際の verbatim 確認結果に差異あり (RateDistortion 6 件 / PGPC 5 closed-by-successor + 0 staged の修正)、handoff 計測の **更新が必要**。「既存 sorry 5 件」相当の hit はすべて docstring 文字列リテラルで実数 0 件 (Pattern D 同型誤計数なし)。

2. **2026-05-26 Round 3 PGPC dependency 仮定の verbatim 逆検証**: runbook が Round 3 設計時に「PGPC は EPI/Stam dependency 要確認」と注記していたが、`Common2026/Shannon/ParallelGaussianPerCoord*.lean` の `import` 文 + 逆方向 `rg` で **依存 0** と verbatim 確認。PGPC は独立 sweep 可能、escalate 不要と判定。`CLAUDE.md`「同じ verbatim 確認義務は依存方向 / Phase 順序 / wrapper 呼出方向 / import cycle にも適用」の実例として handoff finding に反映。

3. **2026-05-26 cross-family S1 判定 (WynerZiv → RateDistortion)**: `WynerZivConverseChain.lean:10` が docstring 散文で `rate_distortion_converse_n_letter_singleLetter` を mention するのみ (import なし) を verbatim 確認、Pattern G 3-段判定の S1 と確定。Phase 2.RD.1 で signature 改変しても WynerZiv 側の prose 更新のみで済む。

4. **2026-05-26 sub-family 分割の判断**: RateDistortion (6 件、closure 担当 plan が file 単位で異なる) と PGPC (5 件、後継 plan 完結済 legacy tag) は同質性が低いため、Phase 2 を 2.RD.* + 2.PGPC に **sub-family 分割**して並列実行可能に設計。Hoeffding pilot は単一 family 5 file sweep だったが、本 plan では各 sub-family の Phase 2 を独立 commit 単位とすることで auditor が sub-family 単位で verdict を出せる。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
5. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
