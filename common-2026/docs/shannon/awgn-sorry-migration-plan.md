# Shannon: AWGN family legacy-tag → sorry-based migration plan (Round 4 Wave A)

> **Parent**: [`awgn-moonshot-plan.md`](awgn-moonshot-plan.md)
> + [`awgn-mi-bridge-plan.md`](awgn-mi-bridge-plan.md)
> + [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md)
> + [`awgn-f1-discharge-moonshot-plan.md`](awgn-f1-discharge-moonshot-plan.md)
> + [`awgn-achievability-typicality-plan.md`](awgn-achievability-typicality-plan.md)
> + [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md)
> + [`awgn-power-constraint-realizable-pivot-plan.md`](awgn-power-constraint-realizable-pivot-plan.md)
> + 関連 [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md) /
>   [`audit/audit-tags.md`](../audit/audit-tags.md)。
>
> 本 plan は **proof completion ではなく legacy tag (`@audit:suspect` 主体 +
> `@audit:staged` + `@audit:defect(prop-true)` 1 件 + `@audit:defect(circular)`
> 2 件 + `@audit:defer` 2 件 + 散文 `🟢ʰ` 9 件) → `sorry + @residual` への honesty
> 強化** (`audit-tags.md`「Deprecated」表 + 「移行レシピ」) を目的とする独立
> workstream。
>
> Pilot references:
> - [`chernoff-sorry-migration-plan.md`](chernoff-sorry-migration-plan.md)
>   (Round 3 Wave A、Phase Z recipe (CS-honest / CS-false / CS-genuine-hyps)
>   確立、19 closed-by-successor migration)
> - [`brunn-minkowski-residual-sorry-migration-plan.md`](brunn-minkowski-residual-sorry-migration-plan.md)
>   (Round 3 Wave A、Pattern D 発展形 + `closure-plan-completed` reason variant
>   提案)
> - [`small-cluster-sorry-migration-plan.md`](small-cluster-sorry-migration-plan.md)
>   (Round 3 Wave A、8-file cluster sweep recipe)
> - [`ratedistortion-pgpc-sorry-migration-plan.md`](ratedistortion-pgpc-sorry-migration-plan.md)
>   (Round 3 Wave A、tag-only 削除 + PGPC EPI/Stam dependency 否定 recipe)
>
> **本 plan の追加目的 (Round 4 Wave A)**:
>
> 1. **大規模 family (47 tag、200+ 行 bundle predicate 既知) の sweep recipe**
>    を確立する。AWGN family は 14 file × 14 タグ種類 (suspect / staged / defer /
>    defect(prop-true) / defect(circular) / closed-by-successor / 🟢ʰ) の混在
>    で、Round 3 までの 4 plan で扱った tag は全てカバー済 + 新規 mix。
> 2. **escalate #7 (handoff): `AWGNMIDecompBody.awgn_midecomp_of_cont_chain`
>    の predicate ごと sorry-based 移行** を Phase 1A 内で完了させる
>    (`IsContChannelMIDecompHyp` predicate は `IsAwgnMIDecomp` と verbatim
>    definitionally 同値、wrapper body は `unfold + exact h_chain` のみ、
>    plan 単一 slug `plan:awgn-mi-decomp-plan` で集約 closure 可能)。
> 3. **escalate #6 (handoff): `IsParallelGaussianPerCoordRegularity`** の取扱
>    判定 — 本 plan **に含めない** (PGPC discharge plan の別 PR に任せる、後述
>    §「scope 外 file」)。

## Context

### 計数 (verbatim 確認、2026-05-26)

`rg -n '@audit:suspect\(|@audit:staged\(|@audit:defer\(|@audit:closed-by-successor\(|@audit:defect\(|@audit:retract-candidate\(|🟢ʰ'`
+ 各タグ周辺 docstring / signature / body 1-3 行を Read で照合した実数値:

| file | suspect | staged | defer | closed-by-successor | defect (prop-true) | defect (circular) | defect (other) | retract-cand | 🟢ʰ | 既存 sorry (`rg -nwc`) | ⚠/FALSE | 真の sweep 対象 (実 decl) | docstring 文字列のみ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `AWGN.lean` | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **4** | 0 |
| `AWGNAchievability.lean` | 0 | 1 | 2 | 0 | 0 | 2 | 0 | 0 | 1 | 0 | 0 | **2** (3 tag 同居 1 decl + 2 tag 同居 1 decl) | 0 |
| `AWGNAchievabilityDischarge.lean` | 4 | 5 | 0 | 0 | 0 | 0 | 1 (`false-statement`) | 0 | 1 | 0 | 4 | **9** + 1 `defect(false-statement)` 既存維持 | 11 (docstring 内 tag 散文 + 既存 honest 表現) |
| `AWGNBindConvBody.lean` | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | **2** | 0 |
| `AWGNConverse.lean` | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | 1 | **1** | 0 |
| `AWGNF1Discharge.lean` | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **2** | 0 |
| `AWGNF2F3Discharge.lean` | 2 | 0 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 5 | **3** (incl. 1 prop-true + 1 closed-by-successor 同居 1 decl) | 0 |
| `AWGNMain.lean` | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **2** | 0 |
| `AWGNMIBridge.lean` | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **4** | 0 |
| `AWGNMIBridgeDischarge.lean` | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 2 | **2** | 0 |
| `AWGNMIDecompBody.lean` | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | **1** | 0 |
| `MultivariateDiffEntropy.lean` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 2 (genuine `@residual(plan:...)`) | 0 | **0** | 1 (`@audit:suspect(...)` docstring 散文) |
| `ParallelGaussianPerCoord.lean` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | 0 | **0** (本 plan scope 外、escalate #6) | 0 |
| `ParallelGaussianPerCoordRegularity.lean` | 0 | 1 (docstring) | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | **0** (Pattern D 該当) | 1 (`@audit:staged(...)` docstring 散文) |
| `ShannonHartley.lean` | 4 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | 4 | **4** + 3 🟢ʰ 同居 | 0 |
| **合計** | **28** | **7** | **2** | **1** | **1** | **2** | **1** | **0** | **10** | **2** | **19** | **36 declaration 対象** (+ 既存 tier 5 維持 1) | **13 docstring 文字列** |

**計数 reconciliation** (orchestrator brief vs verbatim):

- orchestrator brief 計数 (declaration-direct grep): 47 tag、verbatim 確認後の真の sweep 対象は **36 declaration**。差分 11 件は:
  - **Pattern D 発展形 (declaration-direct ではなく docstring 内 tag literal)**:
    - `MultivariateDiffEntropy.lean:55` — 1 件 (`@audit:suspect(...)` form 説明散文)
    - `ParallelGaussianPerCoordRegularity.lean:31` — 1 件 (`@audit:staged(...)` predicate 散文)
    - `AWGNAchievabilityDischarge.lean` 内 11 件中 docstring 内 audit history 散文として複数 — but 実 declaration tag 直接 9 件 (paren 直前まで verbatim 確認)
  - **`ParallelGaussianPerCoord.lean` の 🟢ʰ 散文 4 件**: 全て docstring 内文脈 (load-bearing predicate 説明)、本 plan **scope 外** (escalate #6 で別 PR 任せ)。
- **escalate #7 反映**: `AWGNMIDecompBody.awgn_midecomp_of_cont_chain` (line 161-162) は handoff の通り predicate `IsContChannelMIDecompHyp` (line 144-149) ごと sorry-based に置換可能 → 本 plan Phase 1A に含める (1 declaration + 1 predicate 削除 / 1 wrapper sorry 化)。

### scope 外 file

以下 1 file は **本 plan scope 外** (load-bearing predicate `IsParallelGaussianPerCoordRegularity` が `structure` で 3 field bundling、本 sweep の sorry-based migration recipe では touch しない、escalate #6 通り別 PR / 後続 PGPC discharge plan の incidental migration 待ち):

- `ParallelGaussianPerCoord.lean` (399 行、🟢ʰ 散文 4 件 = `IsParallelGaussianPerCoordRegularity` (line 156) の field `achiever_mi` / `max_ent` が結論 claim を bundling した structure-based load-bearing predicate)。本 sweep で touch すると Round 3 Wave 3-C で否定された PGPC EPI/Stam dependency rewrite と衝突する可能性あり、`parallel-gaussian-l-pg1-discharge-plan` (sibling `ParallelGaussianPerCoordRegularity.lean` で `@audit:ok(parallel-gaussian-l-pg1-discharge)` で済 tag) と整合させて別 PR に委ねる。

以下 1 file は **計数のみ確認、Round 3 small cluster で migration 完了済**:

- `MultivariateDiffEntropy.lean` (527 行、declaration-direct tag 0 件、`@residual(plan:multivariate-diffentropy-subadditivity-plan)` 形態の 2 件 sorry は Round 3 Wave 3-B 小 cluster sweep で migration 完了済 line 240/254)。`@audit:suspect(...)` の 1 grep ヒット (line 55) は migration done note の docstring 散文 (`@audit:suspect(...)` form と書かれた legacy reference 説明)。本 plan で **touch しない**。

`ParallelGaussianPerCoordRegularity.lean` も同様: docstring line 31 の `@audit:staged(...)` 散文は migration done note (新規 predicate 不導入の明示)。実 declaration tag は **`@audit:ok(parallel-gaussian-l-pg1-discharge)`** (line 91, 142) — Round 3 Wave 3-C 完了済の honest state、本 plan で **touch しない**。

### 既存 tier 5 マーカーの取扱

planner 段階で verbatim 確認した tier 5 既存マーカー + 構造的観察:

| file:line | decl 名 | 既存タグ (verbatim) | 構造的観察 | 本 plan の方針 |
|---|---|---|---|---|
| `AWGNAchievabilityDischarge.lean:731` | `def IsAwgnPowerConstraintRealizable` | `@audit:defect(false-statement)` | predicate が機械検証可能に FALSE (chi-square median 解析、docstring `:709-728` で著者明示 + standard remedy = `IsAwgnPowerConstraintHonest` 経由)。**ORPHAN** (line 697 docstring 明示)、consumer 0 件 (= `IsAwgnPowerConstraintHonest` への pivot 完了済) | **本 plan で touch しない** (既に最 honest 形 = tier 5 acknowledged + 後継 predicate 完備、retract-candidate 追加候補だが既存 `@audit:defect(false-statement)` で十分 honest)。**Phase 2.X で `@audit:retract-candidate(false-replaced-by-eps-relaxed)` 追加判定** を auditor 委任 (escalate #1 で正式登録された reason vocab) |
| `AWGNAchievability.lean:46` | `def IsAwgnTypicalityHypothesis` | `@audit:defect(circular)` `@audit:defer(awgn-achievability-typicality)` `@audit:staged(n-dim-gaussian-aep)` | predicate が **universal-R, ε quantified form of the conclusion itself** (docstring line 37-44 verbatim、`HONESTY NOTE` 著者明示)。3 tag 同居 = 旧方針で acknowledged 形 | **Phase 1B で sorry-based 移行**: `@audit:defect(circular)` は維持 (predicate 自身は循環 def、def 本体は sorry に書き換え不可)、`@audit:defer` + `@audit:staged` は **削除**、新規 `@audit:closed-by-successor(awgn-achievability-typicality-plan)` を追加 (= CLAUDE.md「sorry を書けない箇所での対処順序」第二選択、predicate def の signature 改変は本 plan scope 外) |
| `AWGNAchievability.lean:85` | `theorem awgn_achievability` | `@audit:defect(circular)` `@audit:defer(awgn-achievability-typicality)` | body `:= h_typicality hR_pos hR hε` (verbatim line 95)、wrapper 自身は modus ponens、predicate 自身が circular。docstring `HONESTY NOTE` 著者明示 (line 66-82) | **Phase 1B で sorry-based 移行**: hyp `h_typicality : IsAwgnTypicalityHypothesis` は維持 (predicate def 自身が circular だが本 plan scope 外で修正不可)、`@audit:defect(circular)` + `@audit:defer` → `@audit:closed-by-successor(awgn-achievability-typicality-plan)` + 散文 🟢ʰ 削除 + 既存 honesty note 維持 (tier 4 → tier 4 within accepted state; ただし signature 改変 (predicate 削除 + body sorry) は **scope 外** — Phase 1B で predicate を hypothesis として保持し、wrapper のみ tag migration) |
| `AWGNF2F3Discharge.lean:226-229` | `def IsAwgnF3PerLetterHypothesis` | `@audit:defect(prop-true)` `@audit:closed-by-successor(awgn-converse-aux-plan)` | predicate body 末尾が `True` (verbatim line 229)、tier 5 既存マーカー + 散文後継明示済 (line 213-225) | **本 plan で touch しない** (既に最 honest 形 = tier 5 acknowledged + 後継 plan 指定済)。Phase 2.X で同パターンの `IsAwgnF3ChainHypothesis` (line 245) との整合性を auditor 委任 |

これらの tier 5 既存マーカーは **本 plan で touch しない** (既に最 honest 形、predicate def 自身の sorry 化は CLAUDE.md「sorry を書けない箇所での対処順序」第二選択で acknowledged 済)。consumer wrapper 側の tag migration は Phase 1 で扱う (= Recipe A / B / C / Z の判定)。

### load-bearing hypothesis chain 構造 (planner 段階の依存図)

```
AWGN.lean (4 wrapper, F-2 hyp pass-through)
  ├── mutualInfoOfChannel_gaussianInput_closed_form  (h_bridge MI 等式 hyp、CS-honest)
  ├── awgnCapacity_ge_gaussian                       (h_bridge_gauss + h_bdd hyp、CS-honest)
  ├── awgnCapacity_le_gaussian                       (h_max_ent hyp、CS-honest)
  └── awgnCapacity_eq                                (3 hyp 合成、CS-honest)

AWGNAchievability.lean (1 wrapper + 1 predicate def、defect(circular))
  ├── (def) IsAwgnTypicalityHypothesis              (universal-R, ε quantified form of conclusion、tier 5 既存)
  └── awgn_achievability                            (load-bearing wrapper、body := h_typicality)

AWGNAchievabilityDischarge.lean (9 wrapper + 1 def(false-statement)、Phase E 集約)
  ├── 5 staged predicate def: IsContinuousAEPGaussian / IsAwgnRandomCodingBound /
  │   IsAwgnPowerConstraintHonest / IsAwgnRandomCodingFeasible (bundle)
  │   + 既存 IsAwgnPowerConstraintRealizable (defect(false-statement)、orphan)
  ├── awgn_avg_error_union_bound                    (h_aep + h_rand bundle hyp)
  ├── isAwgnTypicalityHypothesis                    (Phase E 統合、h_feasible bundle hyp、580 行 body genuine)
  ├── awgn_achievability_F1_via_staged_hyps         (F-1 hyp pass-through、staged hyp 1 bundle)
  └── awgn_theorem_F4_discharged_F1_via_staged      (F-4 discharged + F-1 staged + F-2 + F-3 hyp pass-through)

AWGNMain.lean (2 wrapper)
  ├── awgn_channel_coding_theorem                   (F-1+F-2+F-3+F-4 hyp pass-through、4 staged hyp 統合)
  └── awgn_capacity_closed_form                     (F-2 系 3 hyp pass-through)

AWGNF1Discharge.lean (2 wrapper)
  ├── awgn_theorem_F1_discharged                    (F-1 = isAwgnChannelMeasurable discharged + F-2/F-3 hyp)
  └── awgn_capacity_closed_form_F1_discharged       (同上、capacity 版)

AWGNMIBridge.lean (4 wrapper + 3 predicate def + 1 genuine theorem)
  ├── (3 predicate def, line 122/134/153): IsAwgnOutputGaussian / IsAwgnMIDecomp / IsAwgnCondEntropyEqNoise
  ├── awgn_cond_entropy_eq_noise_entropy_of_const   (predicate 3 を genuine discharge、tag なし)
  ├── awgn_mi_bridge_of_primitives                  (3 hyp → MI bridge、CS-honest 3 primitives)
  ├── awgn_theorem_F2_discharged                    (3 primitive hyp → F-1 discharged wrapper、cond_entropy auto)
  ├── awgn_mi_gaussian_closed_form_of_primitives    (2 primitive hyp → Gaussian closed-form)
  └── awgn_capacity_closed_form_F2_discharged       (2 primitive + 2 F-2 系 hyp、capacity 版)

AWGNMIBridgeDischarge.lean (2 wrapper + 1 predicate def + 1 genuine theorem)
  ├── (def, line 80) IsAwgnBindEqConv                (bind/conv bridge primitive、tag なし、後継 file で genuine 化)
  ├── awgn_output_gaussian_of_bind_eq_conv          (predicate def + IsAwgnBindEqConv hyp → IsAwgnOutputGaussian、tag なし)
  ├── awgn_theorem_of_typicality_converse_bindconv (typicality + bind/conv + decomp + converse hyp pass-through、CS-honest 4 hyp)
  └── awgn_capacity_closed_form_of_maxent_bindconv  (bind/conv + decomp + bdd + max_ent hyp、capacity 版)

AWGNBindConvBody.lean (2 wrapper、bind/conv bridge を genuine discharge 済)
  ├── (genuine theorem isAwgnBindEqConv_discharged, line 108、tag なし)
  ├── (genuine theorem isAwgnOutputGaussian_discharged, line 123、tag なし)
  ├── awgn_theorem_of_typicality_converse_bindconv_discharged (typicality + decomp + converse hyp、bind/conv auto)
  └── awgn_capacity_closed_form_of_maxent_bindconv_discharged (decomp + bdd + max_ent hyp、capacity 版、bind/conv auto)

AWGNMIDecompBody.lean (1 wrapper + 1 predicate def)
  ├── (def, line 144) IsContChannelMIDecompHyp       (continuous MI chain rule、AWGN-independent、tag なし)
  └── awgn_midecomp_of_cont_chain                   (predicate hyp → IsAwgnMIDecomp、body unfold + exact、CS-honest)
        (escalate #7: 両者 definitionally 同値、predicate ごと sorry 化 candidate)

AWGNConverse.lean (1 wrapper、F-3 hyp pass-through)
  └── awgn_converse                                  (h_converseBound_lbh hyp、body := h_converseBound_lbh ..)
        (predicate IsAwgnConverseHypothesis line 56 は IsAwgnTypicalityHypothesis と同型 circular)

AWGNF2F3Discharge.lean (2 wrapper + 2 predicate def、1 defect(prop-true) 既存)
  ├── (def, line 190) IsAwgnF2DecodingHypothesis     (IsAwgnTypicalityHypothesis と同形 alias、tag なし)
  ├── (def, line 226) IsAwgnF3PerLetterHypothesis    (`True` placeholder、defect(prop-true) + closed-by-successor)
  ├── (def, line 245) IsAwgnF3ChainHypothesis        (IsAwgnConverseHypothesis と同形 alias、tag なし)
  ├── awgn_theorem_of_F2F3_hypotheses               (F-2 + F-3 bundle hyp、F-1 discharged base、CS-false 寄り)
  └── awgn_capacity_closed_form_of_maxent_hypotheses (capacity 版、F-2 系 hyp)

ShannonHartley.lean (4 wrapper + 3 predicate def + 3 散文 🟢ʰ)
  ├── (def, line 115) IsBandlimitedSamplingHypothesis  (positivity bundle, line 100 `🟢ʰ Mathlib-wall residual`)
  ├── (def, line 121) IsBandlimitedKernel              (`0 < W` positivity stand-in、tag なし)
  ├── (def, line 128) IsTwoWDegreesOfFreedom           (genuine 2W 恒等式、tag なし)
  ├── perSampleAwgnCapacity_eq_awgn                  (5+ hyp pass-through、F-2 系継承)
  ├── shannon_hartley_formula                        (3 SH hyp + L-SH3 hyp、CS-honest 寄り、🟢ʰ line 287 同居)
  ├── shannon_hartley_formula_bits                   (同上、bits 版)
  └── mk_IsBandlimitedSamplingHypothesis             (positivity bundle constructor、🟢ʰ line 287 同居)

AWGNBindConvBody.lean (上記)
```

**注意**: 上記の依存図は **wrapper 経由の forward chain** (= 上流の hyp を下流が thread し続ける + 段階的に discharge する Phase F-1→F-2→F-3 構造)。本 plan の Phase 1 では各 file 単独で sorry 化判定 (signature 維持 + body / tag のみ書換)、transitive sorry は Phase Z recipe の handling 方針 (chernoff plan で確立済) に従う。

### 上位 moonshot との関係

`awgn-moonshot-plan.md` (実態整合 2026-05-20 banner) は **headline `awgn_channel_coding_theorem` を 4 honest pass-through hyp で publish 済** (0 sorry):

- F-1 (`IsAwgnTypicalityHypothesis`、circular def): `awgn-achievability-typicality-plan.md` (Tier 3、analytic body 未着手)
- F-2 (MI bridge): `awgn-mi-bridge-plan.md` (3 primitive 縮減済、`IsAwgnMIDecomp` は `awgn-mi-decomp-plan.md` に defer)
- F-3 (`IsAwgnConverseHypothesis`、circular def 寄り): `awgn-converse-aux-plan.md` (Tier 3)
- F-4 (kernel measurability): `awgn-f1-discharge-moonshot-plan.md` で **完全 discharge 済**

本 plan は **その publish 状態を変えない** — specifically:

- **load-bearing wrapper の sorry 化方針 (Phase 1 主軸)**: 36 declaration の signature 改変は **しない** (= predicate hypothesis を hypothesis として保持、body は維持 or 一部 sorry 化)、`@audit:suspect / staged / defer / defect / closed-by-successor` タグを **削除 / 置換** + 散文 🟢ʰ 削除 + tier 4 → tier 3 (`@audit:retract-candidate(...)`) の bookkeeping 化が主体 (Pattern A / Phase Z recipe 寄り、Brunn-Minkowski residual plan 同型)。
- **既存 tier 5 マーカー維持**: `IsAwgnPowerConstraintRealizable` (`defect(false-statement)`) と `IsAwgnTypicalityHypothesis` (`defect(circular)`) と `IsAwgnConverseHypothesis` (defect(circular) なし、ただし circular 同型) と `IsAwgnF3PerLetterHypothesis` (`defect(prop-true)`) は **touch しない** (既に最 honest 形)。
- **escalate #7 限定例外**: `AWGNMIDecompBody.awgn_midecomp_of_cont_chain` は **predicate ごと sorry 化** (Phase 1A 内で 1 plan slug `plan:awgn-mi-decomp-plan` に集約 closure)。
- **successor file (`AWGNBindConvBody.lean` の bind/conv body discharge 済 theorem)** は **本 plan で touch しない** — 既に 0 sorry / 0 legacy tag の genuine discharge。

**proof completion** (continuous AEP / Whittaker-Shannon / chain rule + Fano / per-letter Gaussian max-entropy 等) は successor plan 内で完成予定、本 plan は honesty 強化のみ。

### Honesty workflow と DoD

本 plan の DoD は `CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:

- 各 file `lake env lean Common2026/Shannon/<file>.lean` が 0 errors、
- 各新規 `sorry` (Phase 1A escalate #7 由来 1 件 + Phase 1B-1G で sorry-based migration 由来 N 件) に `@residual(<class>:<slug>)` タグ、
- 各 Phase 完了時に `honesty-auditor` を起動して classification + signature honesty を独立検証 (CLAUDE.md「Independent honesty audit」)。

`@audit:ok` (proof done) は **本 plan の出力にしない** — wrapper 側 file は本来 hypothesis pass-through で publish されており、proof done は各 successor plan (`awgn-achievability-typicality-plan` 等) 経由で別 plan の評価範囲。

### Tier 5 defect — inline 検出 (planner 段階)

CLAUDE.md「検証の誠実性」"見つけた側" inline policy に従い、planner 段階で verbatim 確認した tier 5 既存マーカー + 構造的観察 (上記「既存 tier 5 マーカーの取扱」表 4 件以外):

| file:line | decl 名 | 構造的観察 | 本 plan の方針 |
|---|---|---|---|
| `AWGNConverse.lean:56-65` | `def IsAwgnConverseHypothesis` | predicate signature が universal `∀ M n, ...` quantified form of the converse 結論。`IsAwgnTypicalityHypothesis` と同型 circular だが既存 `@audit:defect(circular)` タグ **無し** (declaration tag は wrapper 側 line 91 の `@audit:suspect` のみ) | **inline alert (tier 5 silent defect 候補)**: 本 plan の Phase 1B で `awgn_converse` wrapper (line 92) の tag migration 時に **predicate 側 `IsAwgnConverseHypothesis` に `@audit:defect(circular)` 付与候補** を auditor 委任。signature 改変 (= predicate 削除) は本 plan scope 外、新規 tier 5 defect tag の追加 (escalate #7 同様の definitional 同値性が無いため別 predicate との集約 closure は不可) は本 plan で行う |
| `AWGNAchievabilityDischarge.lean:140-171` | `def IsContinuousAEPGaussian` | 5 staged predicate def の 1 つ。signature は `∀ ε > 0, ∃ N₀, ∀ n, ∃ A : Set ..., MeasurableSet A ∧ 3-bound chain` (verbatim) で **non-vacuous + 結論型と independent**、staged (Mathlib 壁) として acknowledged 済 | **本 plan で touch しない** (既存 `@audit:staged(continuous-aep-gaussian)` の Phase 1 で sorry-based 移行候補だが、staged predicate 自身は Mathlib 壁の bundle (Pattern D 該当 wall 候補)、`@residual(wall:n-dim-gaussian-aep)` への shared sorry 補題化は **escalate #4 待ち** = Round 3 plan で wall promote 判定見送り中の `wall:n-dim-gaussian-aep` register が完了次第) |
| `AWGNAchievabilityDischarge.lean:543-557` | `def IsAwgnRandomCodingBound` | 同上 (staged predicate)、signature は `∀ ε > 0, ∀ R-below-capacity, ∃ N₀, ∀ n M A, ∫⁻ codebook P[error] ≤ 2ε` で結論型と independent | 同上 (`wall:n-dim-gaussian-aep` への shared sorry 補題化候補) |
| `AWGNAchievabilityDischarge.lean:783-792` | `def IsAwgnPowerConstraintHonest` | honest split form (P_cb ≠ P_target、chi-square SLLN slack)、signature は `∀ ε > 0, ∀ R-below-capacity, ∃ N₀, ∀ n M, gaussianCodebook M n P_cb ≥ 1-ε` で結論型と independent | 同上 (`wall:n-dim-gaussian-aep` への shared sorry 補題化候補) |
| `AWGNAchievabilityDischarge.lean:860-868` | `def IsAwgnRandomCodingFeasible` | 3 staged predicate を bundle、structure-based predicate (Phase 2 pivot 2026-05-24)、signature は `∀ R-below-capacity, ∃ P' ∈ (0, P], R < (1/2) log(1 + P'/N) ∧ IsContinuousAEPGaussian P' N ∧ IsAwgnRandomCodingBound P' N h_meas ∧ IsAwgnPowerConstraintHonest P' P N` で 3 sub-bound bundling | 同上 (bundle 自身は 3 sub-bound predicate の集約形、sorry-based migration では sub-bound 側 individually wall 化推奨) |
| `AWGNMIBridge.lean:122-125` / `:134-141` / `:153-156` | 3 primitive predicate def (`IsAwgnOutputGaussian` / `IsAwgnMIDecomp` / `IsAwgnCondEntropyEqNoise`) | `IsAwgnCondEntropyEqNoise` は line 164-176 で genuine discharge 済、他 2 個は wrapper 経由で staged | **`IsAwgnCondEntropyEqNoise` は genuine、本 plan で touch しない**。`IsAwgnOutputGaussian` は line 123-126 verbatim で `outputDistribution = gaussianReal 0 (P+N)` の Prop、`AWGNBindConvBody.lean:108-113` で **genuine 化済** (bind/conv 経由)、本 plan で touch しない。`IsAwgnMIDecomp` は escalate #7 の通り `IsContChannelMIDecompHyp` と verbatim definitional 同値 + wrapper `awgn_midecomp_of_cont_chain` が `unfold + exact h_chain` 1 行で繋ぐので **Phase 1A で predicate ごと sorry 化** (両 predicate 削除 + wrapper body sorry) |
| `AWGNMIBridgeDischarge.lean:80-83` | `def IsAwgnBindEqConv` | bind/conv bridge primitive、line 108 で `AWGNBindConvBody.lean` 経由 genuine 化済 (本 file = consumer wrapper) | **本 plan で touch しない** (既に genuine 化済の primitive、wrapper `awgn_theorem_of_typicality_converse_bindconv` が hyp pass-through で残るが本 plan の Phase 1G で tag migration のみ) |
| `AWGNF2F3Discharge.lean:190-196` | `def IsAwgnF2DecodingHypothesis` | `IsAwgnTypicalityHypothesis` と verbatim 同型 alias (signature 完全一致) | **inline alert (tier 5 silent defect 候補)**: name-laundering alias。本 plan Phase 1F で `@audit:defect(launder)` + `@audit:retract-candidate(name-laundering-alias)` 付与候補を auditor 委任 (signature 改変 = predicate 削除は本 plan scope 外、別 PR で `IsAwgnTypicalityHypothesis` 直接消費に rewrite) |
| `AWGNF2F3Discharge.lean:245-253` | `def IsAwgnF3ChainHypothesis` | `IsAwgnConverseHypothesis` と verbatim 同型 alias (signature 完全一致) | 同上 (name-laundering alias、Phase 1F で同パターン処置) |
| `ShannonHartley.lean:115-116` | `def IsBandlimitedSamplingHypothesis` | positivity bundle `0 < W ∧ 0 < N₀ ∧ 0 ≤ P` (`True` slot は **解消済** 2026-05-20 docstring 注記)、tier 4 寄り (load-bearing claim を bundling しない、positivity carrier のみ) | **本 plan で touch しない** (既に最 honest 形 = positivity bundle、`mk_IsBandlimitedSamplingHypothesis` constructor で genuine 化) |
| `ShannonHartley.lean:121` | `def IsBandlimitedKernel` | `0 < W` positivity stand-in、tag なし、docstring `:118-120` で「undischarged placeholder」を著者明示 | **本 plan で touch しない** (既に honest stand-in、用法 = `mk_IsBandlimitedKernel` で genuine) |
| `ShannonHartley.lean:128-129` | `def IsTwoWDegreesOfFreedom` | genuine 2W 恒等式 `C = 2W · perSampleAwgnCapacity`、tag なし、docstring `:123-127` で「open operational identity」明示 | **本 plan で touch しない** (load-bearing claim だが tag なしの honest hypothesis、shannon_hartley_formula の唯一の load-bearing input) |

これらの 8 件 (predicate def 6 + 2 alias) は **本 plan の Phase 1 では directly touch しない or Phase 1F で alias retract-candidate 付与のみ**。consumer wrapper 側の tag migration は Phase 1 で扱う。

### 具体的数値・型予測の verbatim 確認 (CLAUDE.md「具体的数値・型予測の verbatim 確認」)

本 plan は signature 改変なしの tag migration が主体だが、Phase 1A の `IsContChannelMIDecompHyp` + `IsAwgnMIDecomp` predicate ごと sorry 化で type 確認が必要 + degenerate boundary case の AWGN family 固有の retreat:

| 確認項目 | Mathlib / Common2026 verbatim 確認結果 | Phase 0 反映 |
|---|---|---|
| `differentialEntropy (Measure.dirac m) = ?` | `Common2026/Shannon/DifferentialEntropy.lean:149` `theorem differentialEntropy_dirac (m : ℝ) : differentialEntropy (Measure.dirac m) = 0` (verbatim) — Dirac 退化 case の値は `0`。`-∞` ではない (1-D rnDeriv 形式の Bayes 経路 + `Real.negMulLog 0 = 0` 経由) | AWGN family は通常 `(N : ℝ) ≠ 0` hypothesis を要求 (AWGN.lean:124 `hN : (N : ℝ) ≠ 0` 等)、退化 Dirac case は signature で除外済。**L-DBD-2-α 発火可能性は本 plan で低い** (sorry-based 移行が signature 改変なしルートを優先するため、退化境界 case の型 mismatch が発生しない) |
| `gaussianReal 0 0 = ?` | Mathlib `Mathlib/Probability/Distributions/Gaussian/Real.lean` (verbatim 未直接確認、参照 awgn-mathlib-inventory.md 〜L100): `v = 0` で `gaussianReal m 0 = Measure.dirac m`、`v ≠ 0` で genuine Gaussian。`differentialEntropy_gaussianReal m hv` (line 406-407) は `hv : v ≠ 0` 必須 | AWGN family の declaration は `(N : ℝ) ≠ 0` 必須、`gaussianReal 0 0` 経路は signature で発火不可。**Phase 1A の `IsContChannelMIDecompHyp` 削除でも boundary case は通常入らない** (`gaussianReal 0 P.toNNReal` の `P` も `0 < P` 必須が AWGNMain.lean:61 で確定) |
| `IsContChannelMIDecompHyp` ≡ `IsAwgnMIDecomp` の definitional 同値性 | `AWGNMIDecompBody.lean:144-149` `def IsContChannelMIDecompHyp (p : Measure ℝ) (W : ...Channel ℝ ℝ) : Prop := (mutualInfoOfChannel p W).toReal = differentialEntropy (outputDistribution p W) - ∫ x, differentialEntropy (W x) ∂p` + `AWGNMIBridge.lean:134-141` `def IsAwgnMIDecomp (P N h_meas) : Prop := (mutualInfoOfChannel (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal = ...` (両者 verbatim 確認、AWGN 特殊化のみで結論型完全一致)。`awgn_midecomp_of_cont_chain` line 162-169 body: `unfold IsAwgnMIDecomp; unfold IsContChannelMIDecompHyp at h_chain; exact h_chain` (verbatim) | **escalate #7 の sorry-based 移行は安全**: 両 predicate が verbatim definitional 同値、wrapper body は 1 行の `exact`、predicate ごと sorry 化で 1 plan slug `plan:awgn-mi-decomp-plan` に集約 closure 可能 (downstream consumer は AWGNMIBridgeDischarge.lean / AWGNBindConvBody.lean の wrapper のみ、本 plan の Phase 1G で tag migration 対象) |
| `IsAwgnTypicalityHypothesis` の universal quantification | `AWGNAchievability.lean:47-53` `def IsAwgnTypicalityHypothesis (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop := ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) → ∀ {ε : ℝ}, 0 < ε → ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P), ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε` (verbatim) — 結論型 (`awgn_achievability` line 86-94) と完全一致の circular def | tier 5 既存マーカー `@audit:defect(circular)` 維持、本 plan で signature 改変しない (= scope 外 = `awgn-achievability-typicality-plan` の analytic body 完成で discharge 予定) |

「常識的にこの値だろう」は信用しない方針 (CLAUDE.md): AWGN family の signature は `(N : ℝ) ≠ 0` で gaussianReal 0 0 退化 case を除外、退化 boundary case mismatch は本 plan で発生しない。

## Approach

### 全体戦略

**file 単位 + escalate 反映の sub-phase 分割 sweep**、共有 wall lemma 集約は **escalate #4 待ち** (`wall:n-dim-gaussian-aep` register promote 後)、cross-family ripple は **0 件** (本 sweep scope 内 14 file 全て AWGN family 内 + utility import のみ)。

Chernoff pilot (3 sub-pattern 決定木) + Brunn-Minkowski residual pilot (tag-only migration recipe) + small cluster pilot (8 file cluster sweep) の組合せ。AWGN 固有の **escalate #7 (predicate ごと sorry 化、definitional 同値性経由)** を Phase 1A で独立扱い。

### Phase 構造 (上流 → 下流 chain 順序 + 大型 file の sub-phase 分割)

```
Phase 0    Inventory (本 plan 内 inline 表 + per-file Pattern 適用判定一覧)
   │
Phase 1A   AWGNMIDecompBody.lean (1 wrapper + 1 predicate def、escalate #7 例外)
   │      → predicate `IsContChannelMIDecompHyp` + wrapper `awgn_midecomp_of_cont_chain`
   │        の **両者ごと sorry 化** (Phase Z recipe Z' variant、definitional 同値性経由)。
   │      → 新規 sorry 1 件 + 新規 `@residual(plan:awgn-mi-decomp-plan)` 1 件、
   │        predicate def 1 件削除 (本 plan の唯一の signature 改変)
   │
Phase 1B   AWGNAchievability.lean (1 wrapper + 1 predicate def、defect(circular) 既存維持)
   │      → wrapper `awgn_achievability` の tag migration のみ:
   │        `@audit:defect(circular)` + `@audit:defer(awgn-achievability-typicality)`
   │          → `@audit:closed-by-successor(awgn-achievability-typicality-plan)` に統合
   │        散文 🟢ʰ (line 57) → 散文削除 + 既存 HONESTY NOTE 維持
   │      → predicate def `IsAwgnTypicalityHypothesis` の tag は **既存 tier 5 維持**
   │        (`@audit:defect(circular)` + `@audit:defer` → `@audit:defect(circular)` 単体 +
   │        新規 `@audit:closed-by-successor(awgn-achievability-typicality-plan)`、
   │        `@audit:staged(n-dim-gaussian-aep)` は escalate #4 待ち)
   │
Phase 1C   AWGN.lean (4 wrapper、CS-honest cluster、F-2 hyp pass-through)
   │      → 4 wrapper 全て CS-honest pattern: `@audit:suspect` → `@audit:closed-by-successor(<plan>)`
   │        (slug 確定: `mutualInfoOfChannel_gaussianInput_closed_form` →
   │        `awgn-mi-bridge-plan`、他 3 wrapper → `awgn-moonshot-plan`)
   │
Phase 1D   AWGNAchievabilityDischarge.lean (9 wrapper + 5 predicate def + 1 defect(false-statement) 既存)
   │      → 9 wrapper の tag migration:
   │        ・5 staged predicate def の tag は **維持** (`wall:n-dim-gaussian-aep` register
   │          promote 待ち、escalate #4)、本 plan で touch しない
   │        ・既存 `defect(false-statement)` predicate `IsAwgnPowerConstraintRealizable` は
   │          **維持** + `@audit:retract-candidate(false-replaced-by-eps-relaxed)` 追加判定
   │          (escalate #1 で正式登録された reason vocab)
   │        ・9 wrapper の `@audit:suspect` → `@audit:closed-by-successor(<plan>)`
   │          (slug 確定: 大半が `awgn-moonshot-plan`、`isAwgnTypicalityHypothesis` は
   │          `awgn-achievability-typicality-plan`、`awgn_avg_error_union_bound` は同)
   │        ・散文 🟢ʰ (line 578-579) 削除 + 既存 audit history 維持
   │
Phase 1E   AWGNMain.lean (2 wrapper、最上流 publish hub)
   │      → 2 wrapper の tag migration:
   │        ・`awgn_channel_coding_theorem`: 4 staged hyp pass-through、`@audit:suspect` →
   │          `@audit:closed-by-successor(awgn-moonshot-plan)` (= 本 family の moonshot は
   │          honest hyp pass-through publish 済、tag は migration done note)
   │        ・`awgn_capacity_closed_form`: 同上
   │
Phase 1F   AWGNF1Discharge.lean (2 wrapper) + AWGNMIBridge.lean (4 wrapper) +
           AWGNMIBridgeDischarge.lean (2 wrapper) + AWGNBindConvBody.lean (2 wrapper)
           + AWGNF2F3Discharge.lean (2 wrapper + 2 alias predicate)
   │      → 12 wrapper の tag migration + 2 alias predicate の tier 5 alert:
   │        ・8 wrapper (F1 + MIBridge + BindConvBody): `@audit:suspect` → `@audit:closed-by-successor`
   │        ・4 wrapper (MIBridgeDischarge + F2F3Discharge):
   │          ・MIBridgeDischarge 2 件 → `@audit:closed-by-successor(awgn-mi-decomp-plan)` (bind/conv は genuine、decomp が staged)
   │          ・F2F3Discharge 2 件 → `@audit:closed-by-successor(awgn-achievability-typicality-plan)` (`awgn-converse-aux-plan`)
   │        ・`IsAwgnF2DecodingHypothesis` (line 190) + `IsAwgnF3ChainHypothesis` (line 245): name-laundering
   │          alias 候補、`@audit:retract-candidate(name-laundering-alias)` 付与判定 (auditor 委任)
   │
Phase 1G   AWGNConverse.lean (1 wrapper、F-3 hyp pass-through、🟢ʰ 散文 1 件)
   │      → 1 wrapper の tag migration:
   │        ・散文 🟢ʰ (line 68) 削除 + 既存 ⚠ HONESTY NOTE (line 76) 維持
   │        ・`@audit:suspect(awgn-converse-aux-plan)` → `@audit:closed-by-successor(awgn-converse-aux-plan)`
   │        ・**inline alert**: predicate `IsAwgnConverseHypothesis` (line 56-65) は circular def、
   │          tier 5 silent defect 候補 (auditor 委任で新規 `@audit:defect(circular)` 付与判定)
   │
Phase 1H   ShannonHartley.lean (4 wrapper + 3 散文 🟢ʰ、Whittaker-Shannon family)
   │      → 4 wrapper の tag migration:
   │        ・3 散文 🟢ʰ (line 100/107/287) 削除 + 既存 ⚠ ALERT 維持
   │        ・3 wrapper (`shannon_hartley_formula` / `_bits` / `mk_IsBandlimitedSamplingHypothesis`)
   │          の `@audit:suspect(whittaker-shannon-partial-moonshot-plan)` → `@audit:closed-by-successor(...)`
   │        ・`perSampleAwgnCapacity_eq_awgn` (line 140): `@audit:suspect(whittaker-shannon-partial-moonshot-plan)` →
   │          同 closed-by-successor
   │
Phase 2.audit  honesty-auditor 起動 (Phase 1A 新規 sorry 1 件 + Phase 1B-1H tag migration
                36 件 + tier 5 silent defect 候補 2 件 + alias retract-candidate 2 件)
   │
Phase V    verify (全 14 file lake env lean 0 errors + 集計 + parent plan banner 更新 +
            handoff 反映 + AWGN-specific recipe を runbook に reflect 提案)
```

**Phase 順 (上流 → 下流) を選んだ理由**:

- Chernoff / Brunn-Minkowski residual pilot で実証済の「上流 (= 最下層 primitive predicate 定義側) から先に確定させると olean refresh + 下流 transitive sorry の散文化が一括で扱える」パターン。
- **AWGN の依存図は上流ほど load-bearing が staged (Phase B-0 predicate)、下流ほど CS-honest pass-through** (AWGN.lean / AWGNMain.lean) なので、escalate #7 由来の Phase 1A (= 最も sub-graph に近い predicate sorry 化、`AWGNMIDecompBody`) を最初に処理することで、その後の Phase 1F (= MIBridge / MIBridgeDischarge / BindConvBody) の tag migration が transitive sorry を考慮した上で進められる。
- **Sub-phase 内の file 順は size 順** (大型 `AWGNAchievabilityDischarge.lean:1641` を Phase 1D 単独、小型を Phase 1F に纏める)。

### 並列実行用 Phase 独立性

Round 4 Wave 起動時に **Phase 1A-1H を並列 implementer 1-3 並列で実行可能** にするため、file 独立性を Phase に対応させた:

- **Phase 1A** = `AWGNMIDecompBody.lean` のみ (signature 改変あり = predicate def 削除 + body sorry 化、独立実行可能)
- **Phase 1B** = `AWGNAchievability.lean` のみ (tier 5 既存維持、tag migration only)
- **Phase 1C** = `AWGN.lean` のみ (F-2 hyp pass-through、tag migration only)
- **Phase 1D** = `AWGNAchievabilityDischarge.lean` のみ (1641 行、独立実行で 1 worktree 専有推奨)
- **Phase 1E** = `AWGNMain.lean` のみ
- **Phase 1F** = `AWGNF1Discharge.lean` + `AWGNMIBridge.lean` + `AWGNMIBridgeDischarge.lean` + `AWGNBindConvBody.lean` + `AWGNF2F3Discharge.lean` の 5 file cluster (相互依存あり、1 worktree 内で逐次実行)
- **Phase 1G** = `AWGNConverse.lean` のみ
- **Phase 1H** = `ShannonHartley.lean` のみ

並列推奨 (Round 4 Wave B implementer):
- **3 並列**: (1A + 1D + 1F) または (1A + 1D + 1H) — 互いに file 独立
- **1A は最優先**: predicate 削除を含む = downstream の transitive sorry 影響を確定させてから他 Phase を並列実行
- **Phase V 集約は逐次** (lake env lean 全 file verify + handoff 反映)

### closed-by-successor migration recipe + AWGN 固有 Z' variant

Chernoff pilot で確立した 3 sub-pattern decision tree (CS-honest / CS-false / CS-genuine-hyps) に **escalate #7 由来の Z' variant** を追加:

#### Decision tree (各 legacy-tag declaration に対して)

```
[Step 1] declaration の load-bearing hypothesis を verbatim 確認
  │
  ├── (a) hyp が **honest** (type ≠ conclusion、successor で genuine discharge 済) → CS-honest, Recipe A
  ├── (b) hyp が **FALSE-in-general predicate** → CS-false, Recipe B
  ├── (c) hyp が **per-tilt 経路と独立の regularity-寄り hyp** → CS-genuine-hyps, Recipe C
  ├── (d) hyp が **circular def 経由の universal-quantified conclusion** (= `IsAwgnTypicalityHypothesis` 同型) → Recipe D (tier 5 既存維持 + tag refine only)
  └── (e) hyp が **AWGN-independent predicate と definitionally 同値** → **Z' variant**, Recipe Z' (predicate ごと sorry 化、escalate #7)

[Step 2] body の構造を verbatim 確認 (Step 1 と分岐)
  │
  ├── body 純構成的 (1-3 行 modus ponens / unfold + exact) → 各 Recipe の sorry 化 pre-empt → constructive recovery 検証 (auditor 委任)
  └── body が hyp 経由の本質的 derivation → 各 Recipe そのまま適用

[Step 3] declaration が wrapper signature compatibility を提供しているか
  │
  ├── Yes (downstream call site が現役、変動 hyp を underscore 化で残す必要あり)
  │    → signature の load-bearing hyp のみ削除、他 hyp は underscore 化で残す (Pattern E)
  └── No (本 declaration は別 declaration から forward されるだけ)
        → signature 縮小、不要 hyp は完全削除
```

#### Recipe Z' — definitional 同値 predicate の合体 sorry 化 (escalate #7、本 plan の新規 recipe)

具体例: `AWGNMIDecompBody.awgn_midecomp_of_cont_chain` (`:162-169`) + `def IsContChannelMIDecompHyp` (`:144-149`) + `def IsAwgnMIDecomp` (`AWGNMIBridge.lean:134-141`)

```lean
-- 旧 (3 declaration の verbatim chain)
-- ★ AWGNMIBridge.lean:134-141 (predicate def 1)
def IsAwgnMIDecomp (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  (mutualInfoOfChannel (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
    = differentialEntropy (outputDistribution (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas))
      - (∫ x, differentialEntropy ((awgnChannel N h_meas) x) ∂(gaussianReal 0 P.toNNReal))

-- ★ AWGNMIDecompBody.lean:144-149 (predicate def 2, AWGN-independent generalization)
def IsContChannelMIDecompHyp (p : Measure ℝ) (W : Channel ℝ ℝ) : Prop :=
  (mutualInfoOfChannel p W).toReal
    = differentialEntropy (outputDistribution p W) - (∫ x, differentialEntropy (W x) ∂p)

-- ★ AWGNMIDecompBody.lean:161-169 (wrapper、`@audit:suspect(awgn-mi-decomp-plan)`)
theorem awgn_midecomp_of_cont_chain
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (h_chain : IsContChannelMIDecompHyp (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)) :
    IsAwgnMIDecomp P N h_meas := by
  unfold IsAwgnMIDecomp
  unfold IsContChannelMIDecompHyp at h_chain
  exact h_chain

-- 新 (predicate def を 1 つ削除 + wrapper body を sorry に置換)
-- ★ AWGNMIBridge.lean:134-141 (維持 — AWGN-specific predicate def)
def IsAwgnMIDecomp (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop := ...
   (※ AWGN-specific def 自身は維持、staged predicate として `wall:n-dim-gaussian-aep` 候補)

-- ★ AWGNMIDecompBody.lean: predicate `IsContChannelMIDecompHyp` を **削除**
-- (verbatim definitionally 同値、`IsAwgnMIDecomp` 経由で消費可能)

-- ★ AWGNMIDecompBody.lean: wrapper `awgn_midecomp_of_cont_chain` の hyp `h_chain` を削除、body sorry
/-- ...
@residual(plan:awgn-mi-decomp-plan) -/
theorem awgn_midecomp_of_cont_chain
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) :
    IsAwgnMIDecomp P N h_meas := by
  sorry

-- (theorem `cont_chain_of_awgn_midecomp` line 174-181 も同時に削除 = definitional 同値性確認のみの helper)
```

**重要な備考**:

- 旧 body は **unfold + exact h_chain** で 1 行、`h_chain` を unfold すると `IsAwgnMIDecomp` と verbatim 同一 (定義の繰返し)。
- predicate `IsContChannelMIDecompHyp` を削除 + wrapper body を sorry 化することで、**load-bearing hyp が conclusion と同等な name-laundering alias** (`IsContChannelMIDecompHyp` は `IsAwgnMIDecomp` の AWGN-instance 化と同じ shape) を解消できる。
- 残った wrapper `awgn_midecomp_of_cont_chain` は **`IsAwgnMIDecomp` をそのまま結論として return する pure sorry**、新しい `@residual(plan:awgn-mi-decomp-plan)` で集約 closure。
- AWGN-independent predicate `IsContChannelMIDecompHyp` は本 plan の sorry-based 移行で **完全に消失** (downstream consumer 0 件: AWGNMIBridgeDischarge / AWGNBindConvBody は全て `IsAwgnMIDecomp` 経由)。

**Recipe Z' の判定基準**: (a) consumer wrapper の body が 1-3 行の `unfold + exact <hyp>` または同等、(b) hyp predicate と結論 predicate が verbatim definitionally 同値 (2 predicate を unfold した後 syntactic 一致)、(c) downstream consumer が hyp predicate ではなく結論 predicate のみ消費 (cross-family ripple 0 件)。

#### Recipe D — circular def 経由 + 既存 tier 5 既存維持 (AWGN-specific)

具体例: `AWGNAchievability.awgn_achievability` (`:86-95`) + `def IsAwgnTypicalityHypothesis` (`:47-53`)

```lean
-- 旧 (predicate def + wrapper)
/-- ... `@audit:defect(circular)` `@audit:defer(awgn-achievability-typicality)` `@audit:staged(n-dim-gaussian-aep)` -/
def IsAwgnTypicalityHypothesis (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) → ∀ {ε : ℝ}, 0 < ε → ...

/-- 🟢ʰ load-bearing hypothesis — NOT a discharge.
... HONESTY NOTE ... `@audit:defect(circular)` `@audit:defer(awgn-achievability-typicality)` -/
theorem awgn_achievability
    (P : ℝ) ... (h_typicality : IsAwgnTypicalityHypothesis P N h_meas) ... :
    ... := h_typicality hR_pos hR hε

-- 新 (predicate def: tier 5 既存維持 + tag refine; wrapper: 散文 🟢ʰ 削除 + tag migration only)
/-- ... `@audit:defect(circular)` `@audit:closed-by-successor(awgn-achievability-typicality-plan)`
    `@audit:staged(n-dim-gaussian-aep)` -/  -- defer 削除、closed-by-successor 追加、staged は escalate #4 待ち
def IsAwgnTypicalityHypothesis (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) → ∀ {ε : ℝ}, 0 < ε → ...

/-- HONESTY NOTE ... (load-bearing wrapper 散文維持、🟢ʰ literal 削除)
@residual(plan:awgn-achievability-typicality-plan) `@audit:closed-by-successor(awgn-achievability-typicality-plan)` -/
theorem awgn_achievability
    (P : ℝ) ... (h_typicality : IsAwgnTypicalityHypothesis P N h_meas) ... :
    ... := h_typicality hR_pos hR hε
```

**Recipe D の判定基準**: (a) hyp predicate が結論型の universal-quantified form (circular)、(b) wrapper body が `:= h_typicality <args>` の 1 行 (load-bearing modus ponens、`audit-tags.md`「移行レシピ」の `name laundering` 同型だが既に著者明示済)、(c) tier 5 既存マーカー存在 (本 plan で touch しない signature 保持)。

**重要な備考**: Recipe D は **wrapper body の sorry 化を pre-empt しない** (= 既存 tier 5 acknowledged 形を維持し、`@residual(plan:<slug>)` + `@audit:closed-by-successor(<slug>)` の併用で bookkeeping 強化のみ)。signature 改変 (= hyp 削除 + body sorry) は本 plan scope 外 (predicate def 自身が circular の構造解消は successor plan の signature 改変を必要とする)。

### 共有 wall lemma 集約の要否

**集約しない (escalate #4 待ち)**。`docs/audit/audit-tags.md`「Wall name register」表に AWGN family wall は **未登録**:

- 提案中 wall (Round 2 sweep 識別、escalate #4 待ち) には AWGN 直接該当の wall 候補 **無し**。
- 唯一候補: `wall:n-dim-gaussian-aep` (CLAUDE.md 「Wall name register」既存登録、Ch.9 AWGN 領域) — 4 staged predicate (`IsContinuousAEPGaussian` / `IsAwgnRandomCodingBound` / `IsAwgnPowerConstraintHonest` / `IsAwgnRandomCodingFeasible`) の shared sorry 補題化候補だが、本 plan では **採用見送り** (staged predicate 4 件の `@audit:staged(<plan>)` 形を維持、wall 化は別 PR / `wall:n-dim-gaussian-aep` の active consumer が EPI/Stam + PGPC 等他 family にまたがる場合 promote 判定)。

検証: register 登録済の 10 wall (`stam` / `csiszar` / `n-dim-gaussian-aep` / `sphere-volume` / `continuous-aep` / `nyquist-2w-dof` / `multivariate-mi` / `joint-typicality-multi` / `epi-n-dim` / `fourier`) のうち、AWGN 文脈に直接該当する候補は **`n-dim-gaussian-aep` + `sphere-volume` + `continuous-aep`** の 3 件、ShannonHartley 文脈に **`nyquist-2w-dof` + `fourier`** の 2 件。本 plan では `plan:<slug>` 集約に揃え、wall 化判断は後続 PR (Round 4 Wave C 以降 + handoff 更新待ち)。

### Pattern G (cross-family unified predicate) 判定

本 sweep scope (14 file + scope-out 2 file) 内の cross-family import:

| file:line | import 文 | Stage (runbook S1/S2/S3) | 影響 |
|---|---|---|---|
| `AWGN.lean:1-5` | `Common2026.Shannon.ChannelCoding` + `DifferentialEntropy` + Mathlib | family 内 + S0 (utility) | scope 内 |
| `AWGNAchievability.lean:1` | `Common2026.Shannon.AWGN` | family 内 (S0) | scope 内 |
| `AWGNAchievabilityDischarge.lean:1-8` | family 内 (AWGN/AWGNAchievability/AWGNMain/AWGNF1Discharge/DifferentialEntropy) + Mathlib | family 内 + S0 | scope 内 |
| `AWGNBindConvBody.lean:1-2` | family 内 (AWGNMIBridgeDischarge) + Mathlib | family 内 + S0 | scope 内 |
| `AWGNConverse.lean:1` | family 内 (AWGN) | family 内 (S0) | scope 内 |
| `AWGNF1Discharge.lean:1` | family 内 (AWGNMain) | family 内 (S0) | scope 内 |
| `AWGNF2F3Discharge.lean:1` | family 内 (AWGNF1Discharge) | family 内 (S0) | scope 内 |
| `AWGNMain.lean:1-3` | family 内 (AWGN/AWGNAchievability/AWGNConverse) | family 内 (S0) | scope 内 |
| `AWGNMIBridge.lean:1` | family 内 (AWGNF1Discharge) | family 内 (S0) | scope 内 |
| `AWGNMIBridgeDischarge.lean:1` | family 内 (AWGNMIBridge) | family 内 (S0) | scope 内 |
| `AWGNMIDecompBody.lean:1` | family 内 (AWGNMIBridgeDischarge) | family 内 (S0) | scope 内 |
| `ShannonHartley.lean:1-8` | family 内 (AWGN/AWGNAchievability/AWGNConverse/AWGNMain) + Mathlib | family 内 + S0 | scope 内 |
| (scope 外参考) `MultivariateDiffEntropy.lean:1-11` | family 外 (DifferentialEntropy/MutualInfo/MIChainRule) + Mathlib | family 内 + S0 | scope 外 (本 plan で touch しない) |
| (scope 外参考) `ParallelGaussianPerCoord.lean:1-?` | (本 plan で確認不要、scope 外) | (確認不要) | scope 外 (escalate #6) |

**結論**: 本 sweep scope (14 file) 内に **family 外 import 0 件**。Pattern G escalate は **不要**。

### constructive recovery 候補 (Pilot Pattern B)

planner 段階で各 declaration の **結論型 + body 構造を verbatim 確認**し、constructive 化可能な候補を flag:

| file:line | decl 名 | 結論型 | body 構造 | 構成的回復可能性 |
|---|---|---|---|---|
| 36 件全て (Phase 1A-1H 全 wrapper) | 略 | 略 (load-bearing hypothesis pass-through 経由の 1-3 行 modus ponens) | **No** — 全 wrapper が load-bearing hyp を thread する (= pass-through publish の意図的設計、successor plan 経由で genuine 化される) |

→ **constructive recovery 候補は 0 件**。Hoeffding pilot の 1 件 / Relay pilot の 4 候補のような「結論型が `∀ a, 0 < · a` / `∃ N, ∀ n ≥ N, ...` の regularity 形」が AWGN family には存在しない (全 36 wrapper が load-bearing claim を thread する hypothesis pass-through publish)。

### transitive sorry の handling 方針 (Pilot Pattern C)

本 plan の Phase 1 で唯一 signature 改変があるのは **Phase 1A** (escalate #7 の `IsContChannelMIDecompHyp` predicate 削除 + `awgn_midecomp_of_cont_chain` body sorry 化)。他の Phase 1B-1H は **signature 改変なしの tag migration only** (= body / signature は維持、`@audit:suspect` 等タグを `@audit:closed-by-successor` に置換 + 散文 🟢ʰ 削除)。

そのため transitive sorry は **Phase 1A 由来の 1 件のみ発生** + downstream consumer (AWGNMIBridgeDischarge.lean / AWGNBindConvBody.lean) は IsContChannelMIDecompHyp ではなく `IsAwgnMIDecomp` を消費するため、本 plan では **transitive sorry 散文化対象 = 0 件**。

Pattern C 散文化が必要な唯一のケース: `IsContChannelMIDecompHyp` を経由する **新規 transitive caller が他 file に存在する場合**。`rg` 確認:

```bash
rg -l 'IsContChannelMIDecompHyp\|cont_chain_of_awgn_midecomp' Common2026/Shannon/
```

期待値: `AWGNMIDecompBody.lean` のみ (本 plan で touch する scope 内 file)。downstream consumer は AWGNMIBridgeDischarge.lean / AWGNBindConvBody.lean / 他 file から **`IsAwgnMIDecomp` 経由でのみ消費** = `IsContChannelMIDecompHyp` の削除影響は本 plan scope 内に限定。

### ⚠ HONESTY ALERT / FALSE 検出 (Pattern H、R8)

`rg '⚠|HONESTY ALERT|FALSE' Common2026/Shannon/AWGN*.lean Common2026/Shannon/ShannonHartley.lean Common2026/Shannon/MultivariateDiffEntropy.lean Common2026/Shannon/ParallelGaussianPerCoord*.lean` 結果 (19 hit):

- `AWGNAchievabilityDischarge.lean` 4 hit: `defect(false-statement)` predicate `IsAwgnPowerConstraintRealizable` の docstring (line 696-728) + ORPHAN 明示 — **既存 honest 表現**、本 plan で文言維持。
- `AWGNAchievability.lean` 0 hit (`HONESTY NOTE` は line 38-44 / 66-82、`⚠` literal なしで 0 件 grep)。
- `AWGNF2F3Discharge.lean` 5 hit: `⚠ OPEN placeholder` (`IsAwgnF3PerLetterHypothesis` line 213-220 の `defect(prop-true)` 著者明示) — **既存 honest 表現**、本 plan で文言維持。
- `AWGNConverse.lean` 1 hit: 散文 `⚠ The body is ...` (line 76) — load-bearing wrapper の honest 注記、本 plan で維持。
- `ShannonHartley.lean` 4 hit: `⚠ UNDISCHARGED PLACEHOLDERS` (line 87) / `⚠ undischarged placeholder` (line 118) / `⚠ open operational identity` (line 123) / `⚠ The operational content is taken as the explicit hypothesis` (line 193) — **既存 honest 表現**、本 plan で文言維持。
- `AWGNBindConvBody.lean` 2 hit: `⚠ NOT a full discharge` (line 131 / 160) — 既存 honest 表現。
- `AWGNMIBridgeDischarge.lean` 2 hit: 同上 (line 123 / 155)。
- `AWGNMIDecompBody.lean` 1 hit: `⚠ still OPEN` (line 65) — 既存 honest 表現。

**全 19 hits = 既存 honest 表現** (predicate FALSE / `True` placeholder / OPEN な状態を著者明示)、本 plan の sweep scope **には影響しない** — predicate def 側は既存 tier 5 マーカー (`defect(false-statement)` / `defect(prop-true)`) で維持、consumer wrapper 側の docstring 散文は Phase 1B-1H で `@audit:suspect → @audit:closed-by-successor` 置換する際に **honest 表現として維持** (新規 `@audit:closed-by-successor` タグと併存)。

## 在庫: 36 declaration の verbatim 分類

verbatim 確認方法: 各 `@audit:*` / `🟢ʰ` 周辺 docstring + theorem signature + body 1-3 行を実コードから読込、Recipe A/B/C/D/Z' を判定。

### Phase 1A — `AWGNMIDecompBody.lean` (1 wrapper + 1 predicate def 削除 + 1 cleanup theorem 削除、Recipe Z')

| # | file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `AWGNMIDecompBody.lean:144-149` | `def IsContChannelMIDecompHyp` (削除対象) | (predicate def, AWGN-independent) | `Prop` (continuous MI chain rule) | Z' | Z' | (predicate def 削除) | (def 自体は body なし、削除のみ) | S0 (file 内) | escalate #7 由来、`IsAwgnMIDecomp` と verbatim definitional 同値 |
| 2 | `AWGNMIDecompBody.lean:174-181` | `theorem cont_chain_of_awgn_midecomp` (削除対象) | `h_decomp : IsAwgnMIDecomp` | `IsContChannelMIDecompHyp ...` | Z' | Z' | (theorem 削除) | constructive (body `unfold + exact`、1 行) | S0 | `IsContChannelMIDecompHyp` 削除に伴い helper も削除 (definitional 同値性確認のみの目的) |
| 3 | `AWGNMIDecompBody.lean:161-169` | `theorem awgn_midecomp_of_cont_chain` | `h_chain : IsContChannelMIDecompHyp (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)` | `IsAwgnMIDecomp P N h_meas` | Z' | Z' | `@audit:suspect(awgn-mi-decomp-plan)` → `@residual(plan:awgn-mi-decomp-plan)` + `@audit:closed-by-successor(awgn-mi-decomp-plan)` | No (Recipe Z': hyp 削除 + body sorry) | S0 | hyp 削除 + body sorry、新 conclusion `IsAwgnMIDecomp P N h_meas` を直接 sorry 化 |

**Phase 1A の signature 改変まとめ**:

- **削除 (2 declaration)**: `def IsContChannelMIDecompHyp` + `theorem cont_chain_of_awgn_midecomp`
- **改変 (1 declaration)**: `theorem awgn_midecomp_of_cont_chain` — hyp `h_chain` 削除、body → `sorry`、tag `@audit:suspect` → `@residual(plan:awgn-mi-decomp-plan)` + `@audit:closed-by-successor(awgn-mi-decomp-plan)`

**downstream consumer 確認**: `rg -l 'IsContChannelMIDecompHyp\|cont_chain_of_awgn_midecomp' Common2026/` で `AWGNMIDecompBody.lean` のみ (verbatim 確認済)、cross-family / cross-file ripple **0 件**。

### Phase 1B — `AWGNAchievability.lean` (1 wrapper、Recipe D + 散文 🟢ʰ 削除)

| # | file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|---|
| 4 | `AWGNAchievability.lean:46` | `def IsAwgnTypicalityHypothesis` | (predicate def、circular) | `Prop` (universal-R, ε quantified form of conclusion) | Recipe D | D | `@audit:defect(circular)` + `@audit:defer(awgn-achievability-typicality)` + `@audit:staged(n-dim-gaussian-aep)` → `@audit:defect(circular)` + `@audit:closed-by-successor(awgn-achievability-typicality-plan)` + `@audit:staged(n-dim-gaussian-aep)` (defer 削除、closed-by-successor 追加、staged は escalate #4 待ち) | No (tier 5 既存維持) | S0 | predicate def 自身は circular、signature 改変は本 plan scope 外 |
| 5 | `AWGNAchievability.lean:85` | `theorem awgn_achievability` | (hyp `h_typicality` 維持) | universal achievability 結論 | Recipe D | D | `@audit:defect(circular)` + `@audit:defer(awgn-achievability-typicality)` → `@audit:closed-by-successor(awgn-achievability-typicality-plan)` + `@residual(plan:awgn-achievability-typicality-plan)` (defect(circular) + defer 削除、closed-by-successor 追加) | No (Recipe D: wrapper body 維持) | S0 | 散文 🟢ʰ (line 57) 削除、HONESTY NOTE (line 66-82) 維持 |

**Phase 1B の signature 改変まとめ**: 0 件 (tag migration only)。

### Phase 1C — `AWGN.lean` (4 wrapper、CS-honest cluster + Recipe A)

| # | file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|---|
| 6 | `AWGN.lean:123` | `theorem mutualInfoOfChannel_gaussianInput_closed_form` | `h_bridge : (mutualInfoOfChannel ...).toReal = h(P+N) - h(N)` (CS-honest, F-2 hyp) | `(mutualInfoOfChannel ...).toReal = (1/2) log(1 + P/N)` | CS-honest | A | `@audit:suspect(awgn-mi-bridge-plan)` → `@audit:closed-by-successor(awgn-mi-bridge-plan)` | No (load-bearing F-2 hyp) | S0 | hyp 維持 + tag migration only |
| 7 | `AWGN.lean:213` | `theorem awgnCapacity_ge_gaussian` | `h_bridge_gauss + h_bdd` (CS-honest, F-2 系 hyp) | `(1/2) log(1 + P/N) ≤ awgnCapacity P N h_meas` | CS-honest | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No | S0 | 同上 |
| 8 | `AWGN.lean:237` | `theorem awgnCapacity_le_gaussian` | `h_max_ent` (CS-honest, F-2 系 hyp) | `awgnCapacity P N h_meas ≤ (1/2) log(1 + P/N)` | CS-honest | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No | S0 | 同上 |
| 9 | `AWGN.lean:261` | `theorem awgnCapacity_eq` | `h_bridge_gauss + h_bdd + h_max_ent` (CS-honest, F-2 系 3 hyp) | `awgnCapacity P N h_meas = (1/2) log(1 + P/N)` | CS-honest | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No | S0 | 同上 |

**Phase 1C の signature 改変まとめ**: 0 件 (tag migration only)。

### Phase 1D — `AWGNAchievabilityDischarge.lean` (9 wrapper + 1 existing tier 5 既存維持、CS-honest 寄り + Recipe A)

| # | file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|---|
| 10 | `AWGNAchievabilityDischarge.lean:139` | `def IsContinuousAEPGaussian` | (predicate def、staged) | `Prop` (3-bound continuous AEP) | CS-staged | (本 plan で touch しない、escalate #4 待ち) | `@audit:staged(continuous-aep-gaussian)` 維持 | No | S0 | `wall:n-dim-gaussian-aep` 化候補 (escalate #4) |
| 11 | `AWGNAchievabilityDischarge.lean:542` | `def IsAwgnRandomCodingBound` | (predicate def、staged) | `Prop` (random-coding integral bound) | CS-staged | 同上 | `@audit:staged(awgn-random-coding-bound)` 維持 | No | S0 | 同上 |
| 12 | `AWGNAchievabilityDischarge.lean:730` | `def IsAwgnPowerConstraintRealizable` (defect(false-statement)) | (predicate def、orphan) | `Prop` (FALSE in general) | (本 plan で touch しない) | (既存 tier 5 維持) | `@audit:defect(false-statement)` 維持 + Phase 2.X で `@audit:retract-candidate(false-replaced-by-eps-relaxed)` 追加判定 (auditor 委任) | No (FALSE predicate) | S0 | escalate #1 で正式登録された reason vocab |
| 13 | `AWGNAchievabilityDischarge.lean:783` | `def IsAwgnPowerConstraintHonest` | (predicate def、staged honest split form) | `Prop` (codebook P_cb / target P_target slack bound) | CS-staged | (本 plan で touch しない、escalate #4 待ち) | `@audit:staged(awgn-power-constraint-honest)` 維持 | No | S0 | 同上 |
| 14 | `AWGNAchievabilityDischarge.lean:860` | `def IsAwgnRandomCodingFeasible` | (predicate def、bundle 3 sub-bound) | `Prop` (3 sub-bound at P' with slack) | CS-staged | (本 plan で touch しない、escalate #4 待ち) | `@audit:staged(awgn-random-coding-feasible)` 維持 | No | S0 | 同上 |
| 15 | `AWGNAchievabilityDischarge.lean:581` | `theorem awgn_avg_error_union_bound` | `h_aep + h_rand` (CS-staged 2 hyp) | `∃ N₀ ∀n M A m, ∫⁻ ... ≤ 2ε` | CS-honest 寄り | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No (load-bearing staged 2 hyp) | S0 | hyp 維持 + tag migration only |
| 16 | `AWGNAchievabilityDischarge.lean:960` | `theorem isAwgnTypicalityHypothesis` | `h_feasible : IsAwgnRandomCodingFeasible P N h_meas` (CS-staged bundle hyp) | `IsAwgnTypicalityHypothesis P N h_meas` | CS-honest 寄り | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-achievability-typicality-plan)` (slug 変更: 本 declaration の closure 担当は achievability-typicality plan = `IsContinuousAEPGaussian` 等 staged predicate の genuine 化を待つため) | No | S0 | 580 行 genuine body + 1 bundle hyp pass-through |
| 17 | `AWGNAchievabilityDischarge.lean:1586` | `theorem awgn_achievability_F1_via_staged_hyps` | `h_feasible` (CS-staged bundle hyp) | universal achievability 結論 | CS-honest 寄り | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No | S0 | F-1 hyp pass-through wrapper |
| 18 | `AWGNAchievabilityDischarge.lean:1618` | `theorem awgn_theorem_F4_discharged_F1_via_staged` | `h_feasible + h_mi_bridge + h_converse` (CS-honest 寄り 3 hyp) | universal achievability 結論 | CS-honest 寄り | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No | S0 | F-4 discharged + F-1 staged + F-2 + F-3 hyp pass-through |

**Phase 1D の signature 改変まとめ**: 0 件 (tag migration only)。

**散文 🟢ʰ 削除**: `AWGNAchievabilityDischarge.lean:578-579` の docstring 内 `**Independent audit (2026-05-24)**: verdict load_bearing_hyp / suspect ... Honest 🟢ʰ remaining task` 表現を Phase 1D 内で **literal 🟢ʰ のみ削除** + 散文表現は維持 (auditor 委任で意味論的整合性確認)。

### Phase 1E — `AWGNMain.lean` (2 wrapper、CS-honest + Recipe A)

| # | file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|---|
| 19 | `AWGNMain.lean:60` | `theorem awgn_channel_coding_theorem` | `h_meas + h_typicality + h_mi_bridge + h_converse` (CS-honest 4 hyp) | universal achievability 結論 | CS-honest | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No | S0 | parent moonshot publish hub |
| 20 | `AWGNMain.lean:89` | `theorem awgn_capacity_closed_form` | `h_meas + h_bridge_gauss + h_bdd + h_max_ent` (CS-honest 4 hyp) | `awgnCapacity = (1/2) log(1 + P/N)` | CS-honest | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No | S0 | 同上 |

**Phase 1E の signature 改変まとめ**: 0 件 (tag migration only)。

### Phase 1F — F1+MIBridge+MIBridgeDischarge+BindConvBody+F2F3Discharge (12 wrapper + 2 alias retract-cand)

| # | file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|---|
| 21 | `AWGNF1Discharge.lean:102` | `theorem awgn_theorem_F1_discharged` | (F-1 discharged + 3 staged hyp pass-through) | universal achievability 結論 | CS-honest | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No | S0 | F-1 = isAwgnChannelMeasurable discharged |
| 22 | `AWGNF1Discharge.lean:130` | `theorem awgn_capacity_closed_form_F1_discharged` | (F-1 discharged + 3 F-2 系 hyp) | capacity 結論 | CS-honest | A | `@audit:suspect(awgn-mi-bridge-plan)` → `@audit:closed-by-successor(awgn-mi-bridge-plan)` | No | S0 | 同上 |
| 23 | `AWGNMIBridge.lean:192` | `theorem awgn_mi_bridge_of_primitives` | `h_out + h_decomp + h_cond` (3 primitive hyp、CS-honest) | MI bridge 結論 | CS-honest | A | `@audit:suspect(awgn-mi-decomp-plan)` → `@audit:closed-by-successor(awgn-mi-decomp-plan)` | No | S0 | 3 primitive hyp pass-through |
| 24 | `AWGNMIBridge.lean:224` | `theorem awgn_theorem_F2_discharged` | `h_typicality + h_out + h_decomp + h_converse` (4 hyp、CS-honest) | universal achievability 結論 | CS-honest | A | `@audit:suspect(awgn-mi-decomp-plan)` → `@audit:closed-by-successor(awgn-mi-decomp-plan)` | No | S0 | F-2 partially discharged |
| 25 | `AWGNMIBridge.lean:257` | `theorem awgn_mi_gaussian_closed_form_of_primitives` | `h_out + h_decomp` (2 hyp、CS-honest) | Gaussian closed-form 結論 | CS-honest | A | `@audit:suspect(awgn-mi-decomp-plan)` → `@audit:closed-by-successor(awgn-mi-decomp-plan)` | No | S0 | 2 primitive hyp pass-through |
| 26 | `AWGNMIBridge.lean:291` | `theorem awgn_capacity_closed_form_F2_discharged` | `h_out + h_decomp + h_bdd + h_max_ent` (4 hyp、CS-honest) | capacity 結論 | CS-honest | A | `@audit:suspect(awgn-mi-decomp-plan)` → `@audit:closed-by-successor(awgn-mi-decomp-plan)` | No | S0 | 同上 |
| 27 | `AWGNMIBridgeDischarge.lean:134` | `theorem awgn_theorem_of_typicality_converse_bindconv` | `h_typicality + h_bridge + h_decomp + h_converse` (4 hyp、CS-honest) | universal achievability 結論 | CS-honest | A | `@audit:suspect(awgn-mi-decomp-plan)` → `@audit:closed-by-successor(awgn-mi-decomp-plan)` | No | S0 | bind/conv は genuine、decomp が staged |
| 28 | `AWGNMIBridgeDischarge.lean:162` | `theorem awgn_capacity_closed_form_of_maxent_bindconv` | `h_bridge + h_decomp + h_bdd + h_max_ent` (4 hyp、CS-honest) | capacity 結論 | CS-honest | A | `@audit:suspect(awgn-mi-decomp-plan)` → `@audit:closed-by-successor(awgn-mi-decomp-plan)` | No | S0 | 同上 |
| 29 | `AWGNBindConvBody.lean:140` | `theorem awgn_theorem_of_typicality_converse_bindconv_discharged` | `h_typicality + h_decomp + h_converse` (3 hyp、CS-honest、bind/conv auto-dispatched) | universal achievability 結論 | CS-honest | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No | S0 | bind/conv genuine、decomp が staged |
| 30 | `AWGNBindConvBody.lean:167` | `theorem awgn_capacity_closed_form_of_maxent_bindconv_discharged` | `h_decomp + h_bdd + h_max_ent` (3 hyp、CS-honest、bind/conv auto-dispatched) | capacity 結論 | CS-honest | A | `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)` | No | S0 | 同上 |
| 31 | `AWGNF2F3Discharge.lean:190-196` | `def IsAwgnF2DecodingHypothesis` | (predicate def、name-laundering alias of `IsAwgnTypicalityHypothesis`) | `Prop` (verbatim signature 同型) | Recipe F (alias retract) | F (新規) | (tag なし) → 新規 `@audit:retract-candidate(name-laundering-alias)` + 散文「name-laundering alias of `IsAwgnTypicalityHypothesis` (`AWGNAchievability.lean:47`)、signature 改変は別 PR」 (auditor 委任) | No (alias) | S0 | tier 5 silent defect 候補、本 plan で tag 付与 |
| 32 | `AWGNF2F3Discharge.lean:245-253` | `def IsAwgnF3ChainHypothesis` | (predicate def、name-laundering alias of `IsAwgnConverseHypothesis`) | `Prop` (verbatim signature 同型) | Recipe F (alias retract) | F | (tag なし) → 新規 `@audit:retract-candidate(name-laundering-alias)` + 散文「name-laundering alias of `IsAwgnConverseHypothesis` (`AWGNConverse.lean:56`)、signature 改変は別 PR」 (auditor 委任) | No (alias) | S0 | 同上 |
| 33 | `AWGNF2F3Discharge.lean:280` | `theorem awgn_theorem_of_F2F3_hypotheses` | `h_F2 + h_F3_per_letter + h_F3_chain + h_mi_bridge` (4 hyp、CS-honest 寄り) | universal achievability 結論 | CS-honest | A | `@audit:suspect(awgn-achievability-typicality-plan)` → `@audit:closed-by-successor(awgn-achievability-typicality-plan)` | No | S0 | F-1 discharged + F-2/F-3 hyp pass-through |
| 34 | `AWGNF2F3Discharge.lean:318` | `theorem awgn_capacity_closed_form_of_maxent_hypotheses` | `h_bridge_gauss + h_bdd + h_max_ent` (3 hyp、CS-honest) | capacity 結論 | CS-honest | A | `@audit:suspect(awgn-converse-aux-plan)` → `@audit:closed-by-successor(awgn-converse-aux-plan)` | No | S0 | F-2 系 hyp pass-through |

**Phase 1F の signature 改変まとめ**: 0 件 (tag migration only + 2 alias 新規 retract-cand 付与)。

### Phase 1G — `AWGNConverse.lean` (1 wrapper + tier 5 silent defect 候補、Recipe A)

| # | file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|---|
| 35 | `AWGNConverse.lean:56-65` | `def IsAwgnConverseHypothesis` | (predicate def、circular) | `Prop` (universal converse 結論 form) | (本 plan で tag refine 候補) | (Recipe D 同様) | (tag なし) → 新規 `@audit:defect(circular)` 付与判定 (auditor 委任、`IsAwgnTypicalityHypothesis` と同型 circular def、tier 5 silent defect 候補) + `@audit:closed-by-successor(awgn-converse-aux-plan)` | No (tier 5 既存 defect 候補) | S0 | inline alert: predicate 自身が circular、新規 tag 付与判定 |
| 36 | `AWGNConverse.lean:92` | `theorem awgn_converse` | `h_converseBound_lbh : IsAwgnConverseHypothesis` (load-bearing 1 hyp) | universal converse 結論 | Recipe D | D | `@audit:suspect(awgn-converse-aux-plan)` → `@audit:closed-by-successor(awgn-converse-aux-plan)` + `@residual(plan:awgn-converse-aux-plan)` | No | S0 | 散文 🟢ʰ (line 68) 削除、HONESTY NOTE (line 76) + body 維持 |

**Phase 1G の signature 改変まとめ**: 0 件 (tag migration only + 1 predicate 新規 defect(circular) 付与判定)。

### Phase 1H — `ShannonHartley.lean` (4 wrapper + 3 散文 🟢ʰ + 3 既存 ⚠ 維持、CS-honest 寄り + Recipe A)

| # | file:line | decl 名 | 削除予定 hyp | 結論型 | sub-pattern | Recipe | 削除/置換予定タグ | constructive? | Stage | 備考 |
|---|---|---|---|---|---|---|---|---|---|---|
| 37 | `ShannonHartley.lean:140` | `theorem perSampleAwgnCapacity_eq_awgn` | `h_meas + h_bridge_gauss + h_bdd + h_max_ent + hN_snr` (CS-honest 5 hyp) | `awgnCapacity = perSampleAwgnCapacity W N₀ P` | CS-honest | A | `@audit:suspect(whittaker-shannon-partial-moonshot-plan)` → `@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` | No | S0 | F-2 系 hyp pass-through |
| 38 | `ShannonHartley.lean:211` | `theorem shannon_hartley_formula` | `h_sampling + h_kernel + h_two_w` (CS-honest 3 hyp、L-SH3 がメイン) | `C = bandlimitedAwgnCapacity W N₀ P` | CS-honest | A | `@audit:suspect(whittaker-shannon-partial-moonshot-plan)` → `@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` + `@residual(plan:whittaker-shannon-partial-moonshot-plan)` | No | S0 | 散文 🟢ʰ (line 287 同居) 削除、HONESTY NOTE (line 193) 維持 |
| 39 | `ShannonHartley.lean:297` | `theorem mk_IsBandlimitedSamplingHypothesis` | (3 positivity hyp、CS-honest) | `IsBandlimitedSamplingHypothesis W N₀ P` | CS-honest | A | `@audit:suspect(whittaker-shannon-partial-moonshot-plan)` → `@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` | No | S0 | 散文 🟢ʰ (line 287) 削除 |
| 40 | `ShannonHartley.lean:321` | `theorem shannon_hartley_formula_bits` | (3 SH hyp、CS-honest) | `C / log 2 = bandlimitedAwgnCapacityBits W N₀ P` | CS-honest | A | `@audit:suspect(whittaker-shannon-partial-moonshot-plan)` → `@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` | No | S0 | bits 版 |

**Phase 1H の signature 改変まとめ**: 0 件 (tag migration only + 3 散文 🟢ʰ 削除)。

### 集計 (パターン別)

**真の sweep 対象 = 36 declaration** + **既存 tier 5 既存維持 1 件** + **新規 retract-cand 付与 4 件** + **新規 tier 5 defect 付与判定 1 件 (auditor 委任)** = **計 42 件操作**

- **Phase 1A (escalate #7)**: 3 declaration (1 predicate 削除 + 1 helper 削除 + 1 wrapper signature 改変 + body sorry 化) — **新規 sorry 1 件 + 新規 `@residual(plan:awgn-mi-decomp-plan)` 1 件**
- **Phase 1B (Recipe D)**: 2 declaration (predicate tag refine + wrapper tag migration + 🟢ʰ 削除)
- **Phase 1C (Recipe A、CS-honest)**: 4 wrapper (tag migration only)
- **Phase 1D (Recipe A、CS-honest 寄り + 既存 tier 5 維持)**: 9 wrapper (tag migration only) + 5 staged predicate 維持 + 1 既存 defect(false-statement) 維持 (Phase 2.X で retract-cand 追加判定)
- **Phase 1E (Recipe A)**: 2 wrapper (tag migration only)
- **Phase 1F (Recipe A + 2 alias retract-cand 付与)**: 12 wrapper (tag migration only) + 2 alias predicate 新規 retract-cand 付与
- **Phase 1G (Recipe D + 1 tier 5 defect 付与判定)**: 1 wrapper + 1 predicate 新規 defect(circular) 付与判定 (auditor 委任)
- **Phase 1H (Recipe A + 3 🟢ʰ 削除)**: 4 wrapper (tag migration only)

**新規 sorry 件数**: 1 (Phase 1A)
**新規 `@residual` 件数**: 2 (Phase 1A 由来 + Phase 1B wrapper 由来)
**新規 `@audit:closed-by-successor` 件数**: 34 (各 Phase 1B-1H の wrapper)
**新規 `@audit:retract-candidate(name-laundering-alias)` 件数**: 2 (Phase 1F)
**新規 `@audit:retract-candidate(false-replaced-by-eps-relaxed)` 件数**: 1 (Phase 2.X auditor 委任、Phase 1D の既存 `defect(false-statement)` に追加判定)
**新規 `@audit:defect(circular)` 件数**: 1 (Phase 1G 候補、auditor 委任)
**削除 `@audit:suspect` 件数**: 28 (全 28 declaration-direct hit)
**削除 `@audit:staged` 件数**: 0 (staged predicate 5 件は全て維持、escalate #4 待ち)
**削除 `@audit:defer` 件数**: 2 (`AWGNAchievability.lean:46` + `:85` の 2 件、`@audit:closed-by-successor` に置換統合)
**削除 散文 🟢ʰ 件数**: 9 (全 9 literal 削除、HONESTY NOTE 散文は維持)
**削除 `@audit:defect(circular)` 件数**: 1 (`AWGNAchievability.lean:85` wrapper、predicate def 側 line 46 は維持)
**削除 declaration 件数**: 2 (Phase 1A: `IsContChannelMIDecompHyp` def + `cont_chain_of_awgn_midecomp` helper)
**Pattern D (docstring 文字列誤計数) 該当**: 13 件 (docstring 内 tag literal、本 plan で touch しない)

## Phase 詳細

### Phase 0 — Inventory (本 plan 内 inline、完了) 📋 ✅

- [x] 14 file (AWGN.lean + AWGNAchievability + AWGNAchievabilityDischarge + AWGNBindConvBody + AWGNConverse + AWGNF1Discharge + AWGNF2F3Discharge + AWGNMain + AWGNMIBridge + AWGNMIBridgeDischarge + AWGNMIDecompBody + MultivariateDiffEntropy + ParallelGaussianPerCoord + ParallelGaussianPerCoordRegularity + ShannonHartley) を Read で verbatim 確認 (`@audit:*` 直接タグ + 🟢ʰ 散文 + docstring 内文字列リテラルの区別、escalate #6 / #7 反映)。
- [x] `rg -n '@audit:suspect\\(|...'` で declaration-direct タグの正書法 grep (Pattern D 発展形回避)。
- [x] cross-family 検出: 14 file scope 内に family 外 import 0 件 (utility import のみ)、S3 該当 0 件、escalate 不要。
- [x] `rg '⚠|HONESTY ALERT|FALSE'` で Pattern H 検出 → 19 hit 全て既存 honest 表現、本 plan で文言維持。
- [x] tier 5 defect 新規発見: 0 件 (既存 4 件 + 新規付与判定 3 件 = `IsAwgnF2DecodingHypothesis` / `IsAwgnF3ChainHypothesis` alias 2 件 + `IsAwgnConverseHypothesis` circular 1 件、全て auditor 委任)。
- [x] **境界 case 値の verbatim 確認** (CLAUDE.md「具体的数値・型予測の verbatim 確認」): `differentialEntropy_dirac (m : ℝ) = 0` (line 149)、`differentialEntropy_gaussianReal (m, v ≠ 0) = (1/2) log(2πe v)` (line 406-407)、AWGN family signature は `(N : ℝ) ≠ 0` 必須 → 退化境界 case 発火不可、L-DBD-2-α 発火可能性低。
- [x] **escalate #7 反映**: `IsContChannelMIDecompHyp` と `IsAwgnMIDecomp` の verbatim definitional 同値性確認 (`unfold + exact h_chain` の 1 行 body)、Phase 1A Recipe Z' 適用判定済。
- [x] **escalate #6 反映**: `ParallelGaussianPerCoord.lean` を scope 外として判断 (structure-based load-bearing predicate `IsParallelGaussianPerCoordRegularity` は別 PR 任せ)。

**proof-log**: no (mechanical 在庫確認、interesting なし)。

### Phase 1A — `AWGNMIDecompBody.lean` (escalate #7 Recipe Z') 📋

`proof-log: yes` (`docs/proof-logs/proof-log-awgn-sorry-migration-1A.md`、Recipe Z' の AWGN-specific 適用 + 2 declaration 削除のため judgement 残す)。

- [ ] **1A.1** `AWGNMIDecompBody.lean:144-149` の `def IsContChannelMIDecompHyp` (AWGN-independent continuous-channel MI chain rule predicate) を **削除**。
- [ ] **1A.2** `AWGNMIDecompBody.lean:174-181` の `theorem cont_chain_of_awgn_midecomp` (helper theorem for definitional 同値性確認、削除に伴い不要) を **削除**。
- [ ] **1A.3** `AWGNMIDecompBody.lean:161-169` の `theorem awgn_midecomp_of_cont_chain` を以下に書換:
  ```lean
  /-- `IsAwgnMIDecomp` sorry-based migration target (escalate #7、`IsContChannelMIDecompHyp`
  predicate ごと sorry 化、definitional 同値性経由)。

  本 wrapper は元 `(h_chain : IsContChannelMIDecompHyp ...)` hyp 経由で `IsAwgnMIDecomp`
  を return していたが、`IsContChannelMIDecompHyp` predicate 自身が `IsAwgnMIDecomp` の
  AWGN-instance 化と verbatim definitional 同値であったため (両者 unfold 後 syntactic
  一致、`exact h_chain` 1 行で繋がる)、本 plan の Recipe Z' で predicate ごと削除 + body
  sorry 化に migrate。残った wrapper は `IsAwgnMIDecomp P N h_meas` を return する pure
  sorry、後続 plan `awgn-mi-decomp-plan` で genuine 化予定。

  @residual(plan:awgn-mi-decomp-plan) `@audit:closed-by-successor(awgn-mi-decomp-plan)` -/
  theorem awgn_midecomp_of_cont_chain
      (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) :
      IsAwgnMIDecomp P N h_meas := by
    sorry
  ```
- [ ] **1A.4** `lake build Common2026.Shannon.AWGNMIDecompBody` で olean refresh (signature 改変 = predicate 削除のため)。
- [ ] **1A.5** dependent file の re-verify (parent .olean 再使用は worktree → main 切替時に必要、CLAUDE.md「After upstream edits」):
  ```bash
  rg -l 'AWGNMIDecompBody\|IsContChannelMIDecompHyp\|awgn_midecomp_of_cont_chain' Common2026/Shannon/
  for f in $(rg -l 'AWGNMIDecompBody' Common2026/Shannon/ -t lean); do
    lake env lean "$f"
  done
  ```
  期待: family 内 file (AWGNMIBridgeDischarge.lean / AWGNBindConvBody.lean 等の AWGNMIDecompBody 経由 consumer) で 0 errors。
- [ ] **1A.6** `lake env lean Common2026/Shannon/AWGNMIDecompBody.lean` で 0 errors (1 sorry warning 許容)。

**Phase 1A DoD**:
- `AWGNMIDecompBody.lean` から `def IsContChannelMIDecompHyp` 0 件、`theorem cont_chain_of_awgn_midecomp` 0 件。
- `theorem awgn_midecomp_of_cont_chain` の signature が `IsAwgnMIDecomp P N h_meas` で hyp `h_chain` 削除、body `sorry`、`@residual(plan:awgn-mi-decomp-plan)` + `@audit:closed-by-successor(awgn-mi-decomp-plan)` 付与。
- `lake env lean` 0 errors + 1 sorry warning。

### Phase 1B — `AWGNAchievability.lean` (Recipe D + 散文 🟢ʰ 削除) 📋

`proof-log: no` (mechanical tag migration + 散文削除、signature / body 改変なし)。

- [ ] **1B.1** `AWGNAchievability.lean:46` の `def IsAwgnTypicalityHypothesis` docstring 末尾の `@audit:defer(awgn-achievability-typicality)` を **削除**、`@audit:closed-by-successor(awgn-achievability-typicality-plan)` を追加。`@audit:defect(circular)` + `@audit:staged(n-dim-gaussian-aep)` は維持。
- [ ] **1B.2** `AWGNAchievability.lean:85` の `theorem awgn_achievability` docstring 末尾の `@audit:defect(circular)` + `@audit:defer(awgn-achievability-typicality)` を **削除**、`@audit:closed-by-successor(awgn-achievability-typicality-plan)` + `@residual(plan:awgn-achievability-typicality-plan)` を追加。
- [ ] **1B.3** `AWGNAchievability.lean:57` の docstring 内 散文 `🟢ʰ **load-bearing hypothesis — NOT a discharge.**` を **literal 🟢ʰ 削除** (= 「**load-bearing hypothesis — NOT a discharge.**」に書換)、HONESTY NOTE (line 66-82) は維持。
- [ ] **1B.4** `lake env lean Common2026/Shannon/AWGNAchievability.lean` で 0 errors 確認。

**Phase 1B DoD**:
- `AWGNAchievability.lean` で `@audit:defer` 0 件、散文 🟢ʰ 0 件、`@audit:closed-by-successor` 2 件、`@residual(plan:awgn-achievability-typicality-plan)` 1 件。
- `@audit:defect(circular)` (predicate def line 46) は維持。
- `lake env lean` 0 errors。

### Phase 1C — `AWGN.lean` (Recipe A、CS-honest cluster) 📋

`proof-log: no` (mechanical tag migration)。

- [ ] **1C.1** `AWGN.lean:122` (theorem `mutualInfoOfChannel_gaussianInput_closed_form` docstring 末尾) の `@audit:suspect(awgn-mi-bridge-plan)` を **削除**、`@audit:closed-by-successor(awgn-mi-bridge-plan)` を追加。
- [ ] **1C.2** `AWGN.lean:212` (theorem `awgnCapacity_ge_gaussian`) の `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)`。
- [ ] **1C.3** `AWGN.lean:236` (theorem `awgnCapacity_le_gaussian`) の同上。
- [ ] **1C.4** `AWGN.lean:260` (theorem `awgnCapacity_eq`) の同上。
- [ ] **1C.5** `lake env lean Common2026/Shannon/AWGN.lean` で 0 errors 確認。

**Phase 1C DoD**: `AWGN.lean` で `@audit:suspect` 0 件、`@audit:closed-by-successor` 4 件、`lake env lean` 0 errors。

### Phase 1D — `AWGNAchievabilityDischarge.lean` (Recipe A、CS-honest 寄り + 既存 tier 5 維持) 📋

`proof-log: yes` (`docs/proof-logs/proof-log-awgn-sorry-migration-1D.md`、9 wrapper migration + 5 staged predicate 維持 + 1 defect(false-statement) 維持判断のため judgement 残す)。

- [ ] **1D.1** 9 wrapper の `@audit:suspect` → `@audit:closed-by-successor` 置換 (line 581 / 960 / 1586 / 1618 等の 9 件):
  - `:581 awgn_avg_error_union_bound`: `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)`
  - `:960 isAwgnTypicalityHypothesis`: `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-achievability-typicality-plan)` (slug 変更: 本 declaration の closure 担当 plan 確定)
  - `:1586 awgn_achievability_F1_via_staged_hyps`: `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)`
  - `:1618 awgn_theorem_F4_discharged_F1_via_staged`: 同上
- [ ] **1D.2** 5 staged predicate def の tag は **維持** (`@audit:staged(<plan>)` 維持、escalate #4 待ち):
  - `:139 IsContinuousAEPGaussian` の `@audit:staged(continuous-aep-gaussian)` 維持
  - `:542 IsAwgnRandomCodingBound` の `@audit:staged(awgn-random-coding-bound)` 維持
  - `:783 IsAwgnPowerConstraintHonest` の `@audit:staged(awgn-power-constraint-honest)` 維持
  - `:860 IsAwgnRandomCodingFeasible` の `@audit:staged(awgn-random-coding-feasible)` 維持
- [ ] **1D.3** 既存 `defect(false-statement)` predicate `:730 IsAwgnPowerConstraintRealizable` の `@audit:defect(false-statement)` は **維持** + Phase 2.X (auditor 委任) で `@audit:retract-candidate(false-replaced-by-eps-relaxed)` 追加判定。
- [ ] **1D.4** `AWGNAchievabilityDischarge.lean:578-579` の docstring 内 散文 `Independent audit (2026-05-24): verdict load_bearing_hyp / suspect ... Honest 🟢ʰ remaining task` の literal `🟢ʰ` のみ削除 + 散文表現は維持 (auditor 委任で意味論的整合性確認)。
- [ ] **1D.5** `lake env lean Common2026/Shannon/AWGNAchievabilityDischarge.lean` で 0 errors 確認 (大型 file 1641 行のため re-verify に時間要、Phase 1D は 1 worktree 専有推奨)。

**Phase 1D DoD**:
- 9 wrapper で `@audit:suspect` 0 件、`@audit:closed-by-successor` 9 件。
- 5 staged predicate + 1 defect(false-statement) predicate の tag は維持。
- 散文 `🟢ʰ` literal 0 件、HONESTY NOTE / Independent audit 散文表現は維持。
- `lake env lean` 0 errors。

### Phase 1E — `AWGNMain.lean` (Recipe A) 📋

`proof-log: no`。

- [ ] **1E.1** `:59 awgn_channel_coding_theorem`: `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)`。
- [ ] **1E.2** `:88 awgn_capacity_closed_form`: 同上。
- [ ] **1E.3** `lake env lean Common2026/Shannon/AWGNMain.lean` で 0 errors 確認。

**Phase 1E DoD**: `AWGNMain.lean` で `@audit:suspect` 0 件、`@audit:closed-by-successor` 2 件、`lake env lean` 0 errors。

### Phase 1F — F1+MIBridge+MIBridgeDischarge+BindConvBody+F2F3Discharge (12 wrapper + 2 alias retract-cand) 📋

`proof-log: yes` (`docs/proof-logs/proof-log-awgn-sorry-migration-1F.md`、2 alias retract-cand 付与判断 + 5 file cluster sweep のため judgement 残す)。

- [ ] **1F.1 (AWGNF1Discharge.lean)** 2 wrapper の tag migration:
  - `:101 awgn_theorem_F1_discharged`: `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)`
  - `:129 awgn_capacity_closed_form_F1_discharged`: `@audit:suspect(awgn-mi-bridge-plan)` → `@audit:closed-by-successor(awgn-mi-bridge-plan)`
- [ ] **1F.2 (AWGNMIBridge.lean)** 4 wrapper の tag migration:
  - `:191 awgn_mi_bridge_of_primitives`: `@audit:suspect(awgn-mi-decomp-plan)` → `@audit:closed-by-successor(awgn-mi-decomp-plan)`
  - `:223 awgn_theorem_F2_discharged`: 同上
  - `:256 awgn_mi_gaussian_closed_form_of_primitives`: 同上
  - `:290 awgn_capacity_closed_form_F2_discharged`: 同上
- [ ] **1F.3 (AWGNMIBridgeDischarge.lean)** 2 wrapper の tag migration:
  - `:133 awgn_theorem_of_typicality_converse_bindconv`: `@audit:suspect(awgn-mi-decomp-plan)` → `@audit:closed-by-successor(awgn-mi-decomp-plan)`
  - `:161 awgn_capacity_closed_form_of_maxent_bindconv`: 同上
- [ ] **1F.4 (AWGNBindConvBody.lean)** 2 wrapper の tag migration:
  - `:139 awgn_theorem_of_typicality_converse_bindconv_discharged`: `@audit:suspect(awgn-moonshot-plan)` → `@audit:closed-by-successor(awgn-moonshot-plan)`
  - `:166 awgn_capacity_closed_form_of_maxent_bindconv_discharged`: 同上
- [ ] **1F.5 (AWGNF2F3Discharge.lean)** 2 wrapper の tag migration + 2 alias predicate に retract-cand 付与:
  - `:279 awgn_theorem_of_F2F3_hypotheses`: `@audit:suspect(awgn-achievability-typicality-plan)` → `@audit:closed-by-successor(awgn-achievability-typicality-plan)`
  - `:317 awgn_capacity_closed_form_of_maxent_hypotheses`: `@audit:suspect(awgn-converse-aux-plan)` → `@audit:closed-by-successor(awgn-converse-aux-plan)`
  - `:190 IsAwgnF2DecodingHypothesis` (predicate def): docstring 末尾に新規 `@audit:retract-candidate(name-laundering-alias)` + 散文「`IsAwgnTypicalityHypothesis` (`AWGNAchievability.lean:47`) と verbatim 同型 alias、signature 改変は別 PR 候補」を追加 (auditor 委任で正式付与判定)。
  - `:245 IsAwgnF3ChainHypothesis` (predicate def): docstring 末尾に新規 `@audit:retract-candidate(name-laundering-alias)` + 散文「`IsAwgnConverseHypothesis` (`AWGNConverse.lean:56`) と verbatim 同型 alias、signature 改変は別 PR 候補」を追加 (auditor 委任で正式付与判定)。
  - `:221 IsAwgnF3PerLetterHypothesis` の既存 `@audit:defect(prop-true)` + `@audit:closed-by-successor(awgn-converse-aux-plan)` は **維持** (tier 5 既存 + 後継 plan 指定済)。
- [ ] **1F.6** 5 file の olean refresh + dependent re-verify (signature 改変 0 件のため olean refresh 不要、ただし lake env lean で個別 verify):
  ```bash
  for f in Common2026/Shannon/AWGNF1Discharge.lean Common2026/Shannon/AWGNMIBridge.lean Common2026/Shannon/AWGNMIBridgeDischarge.lean Common2026/Shannon/AWGNBindConvBody.lean Common2026/Shannon/AWGNF2F3Discharge.lean; do
    lake env lean "$f"
  done
  ```

**Phase 1F DoD**:
- 5 file 計 12 wrapper で `@audit:suspect` 0 件、`@audit:closed-by-successor` 12 件。
- 2 alias predicate (`IsAwgnF2DecodingHypothesis` + `IsAwgnF3ChainHypothesis`) に新規 `@audit:retract-candidate(name-laundering-alias)` 付与 (auditor 委任で正式判定)。
- 既存 `IsAwgnF3PerLetterHypothesis` (`defect(prop-true)`) tag 維持。
- 5 file `lake env lean` 0 errors。

### Phase 1G — `AWGNConverse.lean` (Recipe A + tier 5 silent defect 候補付与判定) 📋

`proof-log: yes` (`docs/proof-logs/proof-log-awgn-sorry-migration-1G.md`、tier 5 silent defect 候補付与判定のため judgement 残す)。

- [ ] **1G.1** `AWGNConverse.lean:91` の `theorem awgn_converse` docstring 末尾の `@audit:suspect(awgn-converse-aux-plan)` → `@audit:closed-by-successor(awgn-converse-aux-plan)` + `@residual(plan:awgn-converse-aux-plan)` 追加。
- [ ] **1G.2** `AWGNConverse.lean:68` の docstring 内 散文 `🟢ʰ **load-bearing hypothesis — NOT a discharge.**` を **literal 🟢ʰ 削除** (= 「**load-bearing hypothesis — NOT a discharge.**」に書換)、⚠ HONESTY NOTE (line 76) は維持。
- [ ] **1G.3** **inline alert (tier 5 silent defect 候補)**: `AWGNConverse.lean:56-65` の `def IsAwgnConverseHypothesis` は circular def (universal-quantified converse 結論 form、`IsAwgnTypicalityHypothesis` と同型)、本 plan 内で **新規 `@audit:defect(circular)` 付与判定** を auditor (Phase 2.audit) に委任。Phase 1G では暫定的に docstring 末尾に散文「**inline alert (planner 2026-05-26)**: predicate signature が universal-quantified converse 結論 form (`∀ M n hM c Pe hPe, log M ≤ ...`)、`IsAwgnTypicalityHypothesis` (`AWGNAchievability.lean:47`) と同型 circular def。`@audit:defect(circular)` 付与判定は Phase 2.audit で auditor 委任。」を追加。
- [ ] **1G.4** `lake env lean Common2026/Shannon/AWGNConverse.lean` で 0 errors 確認。

**Phase 1G DoD**:
- `AWGNConverse.lean` で `@audit:suspect` 0 件、散文 🟢ʰ 0 件、`@audit:closed-by-successor` 1 件、`@residual(plan:awgn-converse-aux-plan)` 1 件。
- `IsAwgnConverseHypothesis` docstring に inline alert 散文追加 (新規 tag 付与は Phase 2.audit で auditor 委任)。
- `lake env lean` 0 errors。

### Phase 1H — `ShannonHartley.lean` (Recipe A + 3 🟢ʰ 削除) 📋

`proof-log: no`。

- [ ] **1H.1** 4 wrapper の tag migration:
  - `:139 perSampleAwgnCapacity_eq_awgn`: `@audit:suspect(whittaker-shannon-partial-moonshot-plan)` → `@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)`
  - `:209 shannon_hartley_formula` (line 211 で theorem 定義): `@audit:suspect(whittaker-shannon-partial-moonshot-plan)` → `@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)` + `@residual(plan:whittaker-shannon-partial-moonshot-plan)` 追加
  - `:296 mk_IsBandlimitedSamplingHypothesis` (line 297 で theorem 定義): `@audit:suspect(whittaker-shannon-partial-moonshot-plan)` → `@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)`
  - `:320 shannon_hartley_formula_bits` (line 321 で theorem 定義): `@audit:suspect(whittaker-shannon-partial-moonshot-plan)` → `@audit:closed-by-successor(whittaker-shannon-partial-moonshot-plan)`
- [ ] **1H.2** 3 散文 🟢ʰ 削除:
  - `:100 IsBandlimitedSamplingHypothesis` docstring 散文 `L-SH1 (🟢ʰ Mathlib-wall residual, weak positivity carrier)` の literal `🟢ʰ` 削除 (= `L-SH1 (Mathlib-wall residual, weak positivity carrier)` に書換)
  - `:107 IsBandlimitedSamplingHypothesis` docstring 散文 `🟢ʰ load-bearing hypothesis — NOT a discharge` の literal `🟢ʰ` 削除 (= `**load-bearing hypothesis — NOT a discharge**` に書換)
  - `:287 mk_IsBandlimitedSamplingHypothesis` docstring 散文 `🟢ʰ load-bearing hypothesis — NOT a discharge` の literal `🟢ʰ` 削除 (= 同上書換)
- [ ] **1H.3** 既存 ⚠ HONESTY NOTE (line 87 / 118 / 123 / 193) は維持。
- [ ] **1H.4** `lake env lean Common2026/Shannon/ShannonHartley.lean` で 0 errors 確認。

**Phase 1H DoD**:
- `ShannonHartley.lean` で `@audit:suspect` 0 件、散文 🟢ʰ 0 件、`@audit:closed-by-successor` 4 件、`@residual(plan:whittaker-shannon-partial-moonshot-plan)` 1 件。
- ⚠ HONESTY NOTE 散文表現は維持。
- `lake env lean` 0 errors。

### Phase 2.audit — honesty-auditor 起動 (Phase 1A-1H 全件 + tier 5 silent defect 候補 + alias retract-candidate 判定) 📋

- [ ] **2.audit.1** orchestrator は **`honesty-auditor`** subagent を起動 (CLAUDE.md「Independent honesty audit」§subagent)。対象 (200 行以内サマリ要求):
  - **Phase 1A 新規 sorry 1 件**: `awgn_midecomp_of_cont_chain` の signature honesty (predicate 削除 + body sorry の Recipe Z' 適用) + `@residual(plan:awgn-mi-decomp-plan)` classification 正しさ
  - **Phase 1B-1H tag migration 36 件 + 2 alias retract-cand**: `@audit:suspect → @audit:closed-by-successor` 置換の正書法 + 散文 🟢ʰ 削除の意味論的整合性 (HONESTY NOTE / ⚠ HONESTY ALERT / Independent audit 散文表現の維持)
  - **新規 tier 5 silent defect 候補付与判定**:
    - `IsAwgnConverseHypothesis` (`AWGNConverse.lean:56`) に新規 `@audit:defect(circular)` 付与すべきか (`IsAwgnTypicalityHypothesis` 同型 circular def、tier 5 silent defect 候補)
    - `IsAwgnF2DecodingHypothesis` (`AWGNF2F3Discharge.lean:190`) + `IsAwgnF3ChainHypothesis` (`AWGNF2F3Discharge.lean:245`) の `@audit:retract-candidate(name-laundering-alias)` 付与正書法 (auditor 委任で正式判定)
  - **既存 tier 5 維持判断**: `IsAwgnPowerConstraintRealizable` (`AWGNAchievabilityDischarge.lean:730`) の `@audit:defect(false-statement)` に新規 `@audit:retract-candidate(false-replaced-by-eps-relaxed)` 追加付与判定 (escalate #1 で正式登録された reason vocab)
  - **5 staged predicate 維持判断**: `IsContinuousAEPGaussian` / `IsAwgnRandomCodingBound` / `IsAwgnPowerConstraintHonest` / `IsAwgnRandomCodingFeasible` (`AWGNAchievabilityDischarge.lean`) + `IsAwgnTypicalityHypothesis` (`AWGNAchievability.lean:46`、`@audit:staged(n-dim-gaussian-aep)` 部分) の `@audit:staged` 維持 (escalate #4 = `wall:n-dim-gaussian-aep` register promote 待ち)
- [ ] **2.audit.2** verdict 受領 + 3 値判定 (CLAUDE.md「Independent honesty audit」§closure 判定):
  - **ok** → Phase V 着手
  - **questionable** → docstring refine or 追加コメントで対応、Phase V 進行
  - **defect** (Recipe Z' 適用が誤分類 / circular def 同型判定が誤り / 散文 🟢ʰ 削除が意味論毀損 / alias 判定が誤り) → 当該 declaration の tag を再修正、Phase V 進行前に解決
- [ ] **2.audit.3** **audit focus** (orchestrator brief に明記):
  - (a) **Recipe Z' の AWGN-specific 適用正書法**: `IsContChannelMIDecompHyp` + `cont_chain_of_awgn_midecomp` 削除の cross-family ripple 0 件確認 (`rg` 再実行)、`awgn_midecomp_of_cont_chain` body sorry 化が AWGN-specific predicate `IsAwgnMIDecomp` を直接 sorry 化する形態の honesty 整合
  - (b) **散文 🟢ʰ 9 件削除の意味論的等価性**: literal 🟢ʰ 削除のみで散文表現 (HONESTY NOTE / load-bearing hypothesis 等) は維持、auditor が情報損失を判定
  - (c) **新規 retract-candidate 付与の正書法**: `name-laundering-alias` reason variant の正式適用 (audit-tags.md「Retract-candidate reason 語彙」既存登録済 vocab) + `false-replaced-by-eps-relaxed` 追加付与判定 (escalate #1 で正式登録された vocab)
  - (d) **tier 5 silent defect 候補 1 件の正式付与**: `IsAwgnConverseHypothesis` への `@audit:defect(circular)` 付与判定 (CLAUDE.md「検証の誠実性」"見つけた側" inline policy、planner 段階で flag 済、Phase 2.audit で正式付与)

**proof-log**: yes (`docs/proof-logs/proof-log-awgn-sorry-migration-2.audit.md`)。
理由: auditor verdict + Recipe Z' 適用判定 + 新規 retract-cand / defect 付与判定の judgement を残す。

### Phase V — verify + 集約 + parent moonshot banner 更新 + handoff 反映 📋

- [ ] **V.1** 14 file の `lake env lean` 全件確認 (0 errors、sorry warnings 許容):
  ```bash
  for f in Common2026/Shannon/AWGN.lean Common2026/Shannon/AWGNAchievability.lean Common2026/Shannon/AWGNAchievabilityDischarge.lean Common2026/Shannon/AWGNBindConvBody.lean Common2026/Shannon/AWGNConverse.lean Common2026/Shannon/AWGNF1Discharge.lean Common2026/Shannon/AWGNF2F3Discharge.lean Common2026/Shannon/AWGNMain.lean Common2026/Shannon/AWGNMIBridge.lean Common2026/Shannon/AWGNMIBridgeDischarge.lean Common2026/Shannon/AWGNMIDecompBody.lean Common2026/Shannon/MultivariateDiffEntropy.lean Common2026/Shannon/ParallelGaussianPerCoord.lean Common2026/Shannon/ParallelGaussianPerCoordRegularity.lean Common2026/Shannon/ShannonHartley.lean; do
    echo "===== $f ====="
    lake env lean "$f"
  done
  ```
- [ ] **V.2** 集計コマンド実行 (per-file):
  ```bash
  # 14 file (AWGN family + scope-out 4 file) の合計
  rg -c '@audit:suspect\(' Common2026/Shannon/AWGN*.lean Common2026/Shannon/ShannonHartley.lean Common2026/Shannon/MultivariateDiffEntropy.lean Common2026/Shannon/ParallelGaussianPerCoord*.lean
  # 期待値: 0 (Phase 1A-1H で全 28 件削除、MultivariateDiffEntropy + PGPCR の docstring 散文は維持 = paren 直接タグ 0 件、scope-out 2 file は Round 3 完了状態維持)

  rg -c '@audit:defer\(' Common2026/Shannon/AWGN*.lean
  # 期待値: 0 (Phase 1B で 2 件削除)

  rg -c '🟢ʰ' Common2026/Shannon/AWGN*.lean Common2026/Shannon/ShannonHartley.lean
  # 期待値: 0 (Phase 1B/1D/1G/1H で全 9 件削除)

  rg -c '@audit:closed-by-successor\(' Common2026/Shannon/AWGN*.lean Common2026/Shannon/ShannonHartley.lean
  # 期待値: 34 (Phase 1A 1 件 + Phase 1B 2 件 + Phase 1C 4 件 + Phase 1D 9 件 + Phase 1E 2 件 + Phase 1F 12 件 + Phase 1G 1 件 + Phase 1H 4 件 - tier 5 既存維持を除く)

  rg -c '@audit:retract-candidate\(' Common2026/Shannon/AWGNF2F3Discharge.lean Common2026/Shannon/AWGNAchievabilityDischarge.lean
  # 期待値: 3 (Phase 1F の 2 alias + Phase 2.X auditor 委任の 1 件、auditor verdict ok 時)

  rg -c '@audit:defect\(circular\)' Common2026/Shannon/AWGN*.lean
  # 期待値: 2 (`IsAwgnTypicalityHypothesis` 維持 + 新規 `IsAwgnConverseHypothesis` 付与 = Phase 2.audit ok 時)

  rg -nw 'sorry' Common2026/Shannon/AWGN*.lean Common2026/Shannon/ShannonHartley.lean | wc -l
  # 期待値: 1 (Phase 1A の `awgn_midecomp_of_cont_chain` のみ)

  rg '@residual\(' Common2026/Shannon/AWGN*.lean Common2026/Shannon/ShannonHartley.lean | wc -l
  # 期待値: 5 (Phase 1A 1 件 + Phase 1B 1 件 + Phase 1G 1 件 + Phase 1H 1 件 + その他 1 件 = 5、または若干変動)
  ```
- [ ] **V.3** **parent moonshot banner 更新**: `awgn-moonshot-plan.md` の実態整合 banner (line 2-10) を更新:
  ```
  > 実態整合 (2026-05-26): DONE-HONEST-HYPS + LEGACY-TAG-MIGRATED — headline `awgn_channel_coding_theorem`
  > (`Common2026/Shannon/AWGNMain.lean:60`) は achievability (F-1 `IsAwgnTypicalityHypothesis`) +
  > MI bridge (F-2) + converse (F-3 `IsAwgnConverseHypothesis`) を **honest pass-through hyp** で publish (0 sorry headline)。
  > F-4 kernel measurability は `AWGNF1Discharge.lean:60` で完全 discharge 済。
  > **Round 4 Wave A (`docs/shannon/awgn-sorry-migration-plan.md`、2026-05-26)** で 14 file 内 legacy tag
  > (28 `@audit:suspect` + 2 `@audit:defer` + 9 散文 🟢ʰ) を 34 `@audit:closed-by-successor` + 5 `@residual(plan:<slug>)` に
  > migration 済。escalate #7 由来の `AWGNMIDecompBody.awgn_midecomp_of_cont_chain` は Recipe Z' で
  > predicate `IsContChannelMIDecompHyp` ごと sorry 化 (新規 sorry 1 件 + `@residual(plan:awgn-mi-decomp-plan)`)。
  > 5 staged predicate + 既存 tier 5 (`defect(circular)` 2 件 + `defect(prop-true)` 1 件 + `defect(false-statement)` 1 件) は
  > 維持 (escalate #4 待ち = `wall:n-dim-gaussian-aep` register promote)。
  ```
- [ ] **V.4** **Pilot 知見の handoff 反映** (`.claude/handoff-sorry-migration.md` Active orchestration log + Next phase に追記):
  - **AWGN-specific Recipe Z' の正式登録**: definitional 同値性経由の predicate ごと sorry 化 recipe (escalate #7 由来)、runbook §「失敗パターン」section に **Pattern Z'-AWGN (definitional-equiv predicate collapse)** として追記提案
  - **Recipe F (name-laundering-alias retract-candidate 付与) の正書法**: AWGNF2F3Discharge.lean の 2 alias predicate (`IsAwgnF2DecodingHypothesis` / `IsAwgnF3ChainHypothesis`) で initial use 達成、Round 5 以降の sweep で同パターン再発時の reuse
  - **tier 5 silent defect inline detection の Phase 2.audit 委任 pattern**: `IsAwgnConverseHypothesis` の新規 `@audit:defect(circular)` 付与判定を Phase 2.audit auditor 委任 (planner 段階で flag、implementer は inline alert 散文追加のみ、正式付与は auditor verdict 待ち) — Round 5 以降の同パターン処理に reuse
  - **既存 staged predicate 維持判断の正書法**: `wall:n-dim-gaussian-aep` register promote 待ちで 5 staged predicate を維持する判断 (escalate #4)、後続 plan の同様判断材料に
  - **AWGN family の特殊 case**: `awgn-power-constraint-realizable-pivot-plan` 由来の `IsAwgnPowerConstraintRealizable` (`defect(false-statement)` + ORPHAN) の Phase 2.X retract-cand 追加判定パターン (escalate #1 で正式登録された `false-replaced-by-eps-relaxed` reason vocab の使用)

**Phase V DoD**:
- 14 file (AWGN family 12 + ShannonHartley 1 + 関連 1) で `@audit:suspect` 0 件 + `@audit:defer` 0 件 + 散文 🟢ʰ 0 件 + `@audit:closed-by-successor` 34 件 + `@residual` 5 件 + 新規 `@audit:retract-candidate` 3 件 + `@audit:defect(circular)` 2 件 (`IsAwgnTypicalityHypothesis` 維持 + `IsAwgnConverseHypothesis` 新規)。
- scope-out 4 file (MultivariateDiffEntropy + ParallelGaussianPerCoord + ParallelGaussianPerCoordRegularity) 未編集 (Round 3 完了状態維持)。
- `lake env lean` 各 file 0 errors + 1 sorry warning (Phase 1A 由来)。
- parent moonshot banner 更新済 (`awgn-moonshot-plan.md`)。
- handoff §Active orchestration log に Recipe Z' / Recipe F / tier 5 silent defect inline detection / staged predicate 維持判断記録済。

**proof-log**: yes (`docs/proof-logs/proof-log-awgn-sorry-migration-V.md`)。
理由: Recipe Z' / Recipe F の AWGN-specific 適用 + tier 5 silent defect 候補付与判定 + escalate #4/#6/#7 反映の judgement を残す。

## 撤退ライン

CLAUDE.md「検証の誠実性」+ chernoff plan の撤退ライン section 模倣。

- **L-MIG-1 (variational hyp 誤判定)**: Phase 1 で `h_typicality` / `h_converseBound_lbh` 等 universal-quantified hyp を「variational pass-through」と誤判定して削除する撤退。本 plan では Recipe D で signature 改変なし方針を採用、撤退ライン発火不可。
- **L-MIG-2 (predicate 削除で大量 drift)**: Phase 1A の `IsContChannelMIDecompHyp` 削除で downstream broken state。cross-family ripple 0 件 + definitional 同値性 verbatim 確認済 + `rg` 再確認で発火確率低、ただし発火時は Phase 1A を **Phase 1A-2** に分割 (まず wrapper のみ tag migration、predicate 削除は Phase 1A-2 へ後送り)。
- **L-MIG-3 (Phase C/D closure と方向衝突)**: 本 plan は successor plan の closure 方針と衝突する形 (= predicate ごと削除 + body sorry) を Phase 1A のみで実施、他 Phase は signature 改変なし。successor plan `awgn-mi-decomp-plan` が `IsContChannelMIDecompHyp` の存在を前提とした genuine 化 plan を立てている場合は本 plan の Phase 1A と衝突 → 発火時は **Recipe Z' を撤回**して Phase 1A を「wrapper tag migration only」に降格 (predicate 削除なし、body 維持、tag を `@audit:closed-by-successor(awgn-mi-decomp-plan)` のみ追加)。`awgn-mi-decomp-plan.md` を Read で確認 → 現状の plan は density-level klDiv 展開 + Bayes rnDeriv split + `differentialEntropy` unfold で genuine 化予定 (`IsContChannelMIDecompHyp` は intermediate predicate)、本 plan の Phase 1A の `IsContChannelMIDecompHyp` 削除と方向一致 (= 後続 plan は `IsAwgnMIDecomp` 直接 sorry 化 → genuine 化、`IsContChannelMIDecompHyp` 経由が冗長になる)。**L-MIG-3 発火確率: 低**。
- **L-MIG-4 expansion (Chernoff pilot 由来、inverted dependency)**: downstream genuine proof が migrated wrapper の old hypothesis を thread しているケース。本 plan の Phase 1A 開始前に grep 確認:
  ```bash
  rg -l 'IsContChannelMIDecompHyp' Common2026/
  ```
  期待値: `AWGNMIDecompBody.lean` のみ。発火時 (= 他 file が `IsContChannelMIDecompHyp` を消費していた場合) は Phase 1A を Recipe Z' から「wrapper tag migration only」に降格 + 当該 downstream file を本 plan scope に追加 (transitive sorry の散文化対応、Pattern C)。**L-MIG-4 expansion 発火確率: 低** (verbatim 確認済)。
- **L-DBD-2-α (degenerate-definition exploitation)**: Dirac / 退化 measure を突いた 0 vs 1 値 mismatch の type error — Phase 0 で `gaussianReal 0 0` / `differentialEntropy (Dirac 0)` を verbatim 確認済、AWGN family signature は `(N : ℝ) ≠ 0` 必須で退化境界 case 発火不可。**L-DBD-2-α 発火確率: 極低** (verbatim 確認済)。
- **L-RES-1 (`closure-plan-completed` reason variant 誤適用)**: 本 plan は `closure-plan-completed` reason variant を使用しない (BM residual plan で初出、本 AWGN plan では `name-laundering-alias` + `false-replaced-by-eps-relaxed` + `closed-by-successor` のみ)、撤退ライン発火不可。
- **L-RES-2 (散文 🟢ʰ literal 削除が意味論毀損)**: Phase 1B/1D/1G/1H で 9 件の 🟢ʰ literal 削除、HONESTY NOTE / ⚠ HONESTY ALERT / Independent audit 散文表現は維持。発火時 (= auditor verdict で意味論毀損判定) は Phase 1 内で再表現散文を auditor 提案に従って refine。
- **L-RES-3 (cross-family verifiability で defect 検出)**: Phase 1A の `IsContChannelMIDecompHyp` 削除で他 family broken state — verbatim 確認で発火確率低、発火時は Phase 1A の Recipe Z' を撤回 + 当該 family を本 plan scope に追加 (S3 escalate)。
- **L-RES-4 (Approach 変更: pilot scope 縮減)**: Phase 1A-1H が 1 session で完走しない / lake env lean が想定外 error を発生させる場合、本 plan は **Phase 1A + 1B + 1C + 1E のみで pilot を close** (4 file 14 declaration migration 完了、Phase 1D + 1F + 1G + 1H は後続 session に分離)。escalate #7 の Phase 1A 完了は必須 (= 本 plan の主要 escalate)。

## 未決事項

planner が判断つかない事項を列挙。実装 / auditor 委任で済む項目は明記。

1. **`IsAwgnConverseHypothesis` (`AWGNConverse.lean:56`) への新規 `@audit:defect(circular)` 付与判定** (auditor 判定対象、Phase 2.audit 委任):
   - 本 plan で **新規 付与** として導入提案。`IsAwgnTypicalityHypothesis` (`AWGNAchievability.lean:46`、既存 `@audit:defect(circular)` 付与済) と verbatim 同型 circular def (universal-quantified converse 結論 form)。
   - 提案理由: predicate signature `def IsAwgnConverseHypothesis (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop := ∀ {M n : ℕ} (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ (Pe : ℝ) (_hPe : ...), Real.log M ≤ ... + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)` は converse wrapper の結論型と完全一致 (Recipe D 同型)。
   - planner 推奨: `@audit:defect(circular)` 付与 (本 plan の Phase 1G で暫定 inline alert 散文を追加、Phase 2.audit で正式付与判定)。
   - **auditor 委任**: Phase 2.audit verdict 次第。auditor が「`AWGNAchievability` と同パターンの circular def、既存 `@audit:defect(circular)` 付与の前例あり」と判定すれば本 plan で正式付与、auditor が「signature 変更前の暫定 inline alert 散文のみ十分」と判定すれば散文のみで close (signature 改変は successor plan `awgn-converse-aux-plan` で対応)。

2. **`IsAwgnF2DecodingHypothesis` + `IsAwgnF3ChainHypothesis` への `@audit:retract-candidate(name-laundering-alias)` 付与正書法** (auditor 判定対象、Phase 2.audit 委任):
   - 本 plan で **新規 付与** として導入提案 (Phase 1F)。`audit-tags.md`「Retract-candidate reason 語彙」既存登録済 `name-laundering-alias` reason vocab を使用。
   - 提案理由: 両 predicate def の signature が `IsAwgnTypicalityHypothesis` / `IsAwgnConverseHypothesis` と verbatim 同型 (line 190-196 + line 245-253、F-1 / F-3 と同 shape の alias)。
   - planner 推奨: 付与 (本 plan の Phase 1F で暫定付与、Phase 2.audit で正式判定)。
   - **auditor 委任**: Phase 2.audit verdict 次第。auditor が「LZ78 `IsSMBToLZ78ConverseChainBridge := IsLZ78ConverseChainHyp` (`LZ78SMBSandwich.lean:307/319`) と同パターン (`name-laundering-alias` reason 正書法、既存 use)」と判定すれば正式付与、auditor が「`IsAwgnF2DecodingHypothesis` の使用が直接 hyp 経由ではなく `awgn_achievability_jointly_typical_body` の id-like reduction 経由」を考慮して別 reason vocab (`load-bearing-predicate-extract-only` 等) を提案すれば降格。

3. **`IsAwgnPowerConstraintRealizable` (既存 `@audit:defect(false-statement)`) への `@audit:retract-candidate(false-replaced-by-eps-relaxed)` 追加付与判定** (auditor 判定対象、Phase 2.audit 委任):
   - 本 plan で **新規 追加付与** として導入提案 (Phase 2.X auditor 委任)。escalate #1 で正式登録された reason vocab (Round 3 commit `d83e45b` 由来、`ChernoffPerTiltDischarge:147` + `ChernoffPerTiltSanov:148` で既に使用)。
   - 提案理由: predicate 自身は FALSE in general (chi-square median 解析、Phase 2 pivot 2026-05-24 で `IsAwgnPowerConstraintHonest` 経由に置換済)、**ORPHAN** (line 697 docstring 明示、consumer 0 件)。本 plan で削除候補としての retract-candidate 表記を追加することで、Chernoff family の同パターンと整合 (audit-tags.md「Retract-candidate reason 語彙」`false-replaced-by-eps-relaxed` 既存登録)。
   - planner 推奨: 付与 (本 plan の Phase 2.audit で auditor 委任)。
   - **auditor 委任**: Phase 2.audit verdict 次第。auditor が「ORPHAN かつ後継 predicate (`IsAwgnPowerConstraintHonest`) 完備の場合は retract-candidate 付与正書法」と判定すれば正式付与、auditor が「`AwgnPowerConstraintHonest` が完全 successor ではなく split form (P_cb / P_target 分離) のため retract-candidate 適用は時期尚早」と判定すれば降格 (既存 `@audit:defect(false-statement)` のみ維持)。

4. **5 staged predicate の `@audit:staged` 維持判断** (escalate #4 待ち、user 確認):
   - `IsContinuousAEPGaussian` / `IsAwgnRandomCodingBound` / `IsAwgnPowerConstraintHonest` / `IsAwgnRandomCodingFeasible` (`AWGNAchievabilityDischarge.lean`) + `IsAwgnTypicalityHypothesis` (`AWGNAchievability.lean:46`) の `@audit:staged(<plan>)` 部分は **escalate #4 待ち** (= `wall:n-dim-gaussian-aep` register promote 判定)。
   - planner 推奨: **維持** (本 plan で `@audit:staged` 削除しない)、後続 plan `awgn-achievability-typicality-plan` が `wall:n-dim-gaussian-aep` への shared sorry 補題化を実施する際に escalate #4 で正式 promote。
   - user 確認待ち: 本 plan の commit に `wall:n-dim-gaussian-aep` register promote を同梱するか、別 PR にするか (planner 推奨: 別 PR、本 plan scope は tag migration のみ)。

5. **escalate #6 (`IsParallelGaussianPerCoordRegularity`) の本 plan scope 確認** (user 確認):
   - 本 plan では PGPC scope 外として判断 (handoff escalate #6 + 本 plan §「scope 外 file」)。
   - 別 PR 候補: `parallel-gaussian-l-pg1-discharge-plan` (sibling `ParallelGaussianPerCoordRegularity.lean` で `@audit:ok(parallel-gaussian-l-pg1-discharge)` 完了済) と整合させて別 PR で `IsParallelGaussianPerCoordRegularity` (structure-based load-bearing predicate) の sorry-based migration を実施。
   - user 確認待ち: 別 PR を本 session 完了後すぐに起こすか、後続 PGPC discharge plan の進捗待ち (= `IsParallelGaussianPerCoordRegularity` 自身を `parallel_gaussian_capacity_formula_minimal` で hypothesis-minimal 化 + sorry-based migrate) に統合するか。

6. **proof done を本 plan で目指さない方針の明示確認** (user 確認):
   - 本 plan の DoD は **type-check done** のみ。AWGN family の完全 closure (continuous AEP / Whittaker-Shannon / chain rule + Fano / per-letter Gaussian max-entropy 等) は **未着手のまま** で本 plan は close する。
   - 各 successor plan (`awgn-achievability-typicality-plan` / `awgn-mi-decomp-plan` / `awgn-converse-aux-plan` / `whittaker-shannon-partial-moonshot-plan`) で proof done を目指す形 (= 本 plan で migration 済 `@audit:closed-by-successor(<plan>)` slug が closure 担当)。

## audit-tags.md 拡張提案 (本 plan 経由で議題化)

本 plan の Phase 2.audit verdict (未決事項 #1-#3) を経て、`docs/audit/audit-tags.md` への formal 拡張を **別 PR で提案**:

1. **`@audit:defect(circular)` predicate 等の inline detection pattern の runbook 拡張**:
   - 現行 `audit/sorry-migration-runbook.md` §「Pattern F — tier 5 defect (循環 := h / name laundering) を suspect 計数で見落とし」は wrapper body `:= h_typicality` の検出を扱う。
   - 本 plan で発覚した発展形: **predicate def 自身が universal-quantified 結論 form で circular** な case (`IsAwgnTypicalityHypothesis` + `IsAwgnConverseHypothesis`) の planner 段階 inline detection。
   - 拡張提案: 「inventory step では **predicate def の signature が結論型と verbatim 同型** な case を `circular_predicate_def?` 列で flag、planner Approach に Recipe D (= tier 5 既存維持 + tag refine only、signature 改変は successor plan 任せ) decision tree を明示」。本 plan §Approach の Recipe D 散文を runbook に併記候補。

2. **AWGN-specific Recipe Z' (definitional-equiv predicate collapse) の runbook 拡張**:
   - 本 plan で発覚: `IsContChannelMIDecompHyp` と `IsAwgnMIDecomp` の verbatim definitional 同値性 + 1 行 `unfold + exact` wrapper の case で、predicate ごと sorry 化 + body sorry 化が closure plan slug 単一化に整合。
   - 拡張提案: 「downstream consumer が hyp predicate ではなく結論 predicate のみ消費する case (`rg -l '<hyp_predicate>'` で本 file のみ) は Recipe Z' (= predicate 削除 + wrapper body sorry 化) を pre-empt」。本 plan §Approach の Recipe Z' を runbook に追記候補。

3. **5 staged predicate 維持判断と `wall:<name>` register promote 待ち pattern の runbook 拡張**:
   - 本 plan で発覚: `wall:n-dim-gaussian-aep` register promote 待ち (= `audit-tags.md`「提案中 wall」#? 候補、ただし AWGN family は既存 register `wall:n-dim-gaussian-aep` で適用済)、staged predicate 4 件を `@audit:staged(<plan-slug>)` 形態で維持。
   - 拡張提案: 「`wall:<name>` register に登録済の wall に該当する staged predicate は `@audit:staged(<plan-slug>)` 維持で OK、shared sorry 補題化 (= `@residual(wall:<name>)` への migration) は 2+ family 横断 use 達成時に promote」。本 plan §「共有 wall lemma 集約の要否」を runbook に追記候補。

両拡張提案とも本 plan の commit に同梱しない。本 plan の handoff §V.4 に記録 + 別 PR / 別 session で formal 議題化。

## 判断ログ

書く頻度: 方針変更 / 撤退ラインへの紐付け / 当初仮定の修正があったとき。append-only。

1. **2026-05-26 plan 起草**: lean-planner (本 session、docs-only) が
   `Common2026/Shannon/AWGN*.lean` + `ShannonHartley.lean` + `MultivariateDiffEntropy.lean` +
   `ParallelGaussianPerCoord*.lean` の 15 file の legacy 残置を verbatim 読込で per-declaration 分類。
   - **orchestrator brief との計数差分**: 起動 brief は「47 declaration-direct tag」と通告したが、
     `rg -n` + Read で実コードを verbatim 確認した結果、**真の sweep 対象 = 36 declaration**
     (差分 11 件 = docstring 内 tag literal、Pattern D 発展形)。
   - **scope 確定**: 本 plan は **14 file 内 36 declaration** の sweep 対象、`ParallelGaussianPerCoord.lean` は
     scope-out (escalate #6 = structure-based load-bearing predicate、別 PR / PGPC discharge plan 任せ)、
     `MultivariateDiffEntropy.lean` + `ParallelGaussianPerCoordRegularity.lean` は scope-out (Round 3 完了済)。
   - **escalate #7 反映**: `AWGNMIDecompBody.awgn_midecomp_of_cont_chain` を Recipe Z' で
     predicate `IsContChannelMIDecompHyp` ごと sorry 化 (Phase 1A 単独 sub-phase)。`IsAwgnMIDecomp` (`AWGNMIBridge.lean:134`) と
     verbatim definitional 同値性 + body 1 行 `unfold + exact` を verbatim 確認済。
   - **新規 Recipe**: Recipe Z' (definitional-equiv predicate collapse、AWGN-specific) + Recipe D (circular def
     + 既存 tier 5 維持 + tag refine only) + Recipe F (name-laundering-alias retract-candidate 付与、Round 5 以降 reuse 候補)。
   - **load-bearing hypothesis chain 構造**: 14 file × 36 wrapper の依存図を verbatim 読込で確定 (planner 段階の
     依存図 §Context、CS-honest / CS-staged / CS-circular / CS-genuine-hyps の 4 sub-pattern 識別)。
   - **cross-family 検出**: 14 file scope 内に family 外 import 0 件 (utility import のみ)、S3 該当 0 件、escalate 不要。
   - **tier 5 defect 新規発見**: 既存 4 件 (`IsAwgnPowerConstraintRealizable` `defect(false-statement)` + 
     `IsAwgnTypicalityHypothesis` `defect(circular)` + `awgn_achievability` `defect(circular)` + 
     `IsAwgnF3PerLetterHypothesis` `defect(prop-true)`) + 新規付与候補 3 件 (`IsAwgnConverseHypothesis` 
     `defect(circular)` 候補 + `IsAwgnF2DecodingHypothesis` / `IsAwgnF3ChainHypothesis` 
     `retract-candidate(name-laundering-alias)` 候補)、全て Phase 2.audit 委任。
   - **境界 case 値 verbatim 確認**: AWGN family signature は `(N : ℝ) ≠ 0` 必須 → 退化 Dirac case 
     (`gaussianReal 0 0`) は signature で除外、L-DBD-2-α 発火可能性極低。
   - **closure plan との関係**: `awgn-mi-decomp-plan.md` の current state を Read で verbatim 確認、
     `IsContChannelMIDecompHyp` を intermediate predicate として扱う形跡なし → 本 plan の Phase 1A Recipe Z' と方向衝突なし
     (L-MIG-3 発火確率低)。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
