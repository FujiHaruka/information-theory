# Shannon: small-cluster legacy-tag → sorry-based migration plan

> **Parents (per file)**:
> [`multivariate-diffentropy-subadditivity-plan.md`](multivariate-diffentropy-subadditivity-plan.md) /
> [`whittaker-shannon-partial-moonshot-plan.md`](whittaker-shannon-partial-moonshot-plan.md) /
> [`awgn-mi-decomp-plan.md`](awgn-mi-decomp-plan.md) /
> [`epi-convolution-density-plan.md`](epi-convolution-density-plan.md) /
> (LZ78 cluster — closed-by-successor) /
> [`separation-theorem-moonshot-plan.md`](separation-theorem-moonshot-plan.md) /
> [`birkhoff-ergodic-plan.md`](birkhoff-ergodic-plan.md) /
> [`channel-coding-shannon-theorem-full-plan.md`](channel-coding-shannon-theorem-full-plan.md)
> + [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md)
> + [`audit/audit-tags.md`](../audit/audit-tags.md).
>
> Pilot references:
> [`hoeffding-sorry-migration-plan.md`](hoeffding-sorry-migration-plan.md) /
> [`cramer-sorry-migration-plan.md`](cramer-sorry-migration-plan.md) /
> [`wynerziv-sorry-migration-plan.md`](wynerziv-sorry-migration-plan.md) /
> [`lz78-sorry-migration-plan.md`](lz78-sorry-migration-plan.md) /
> [`huffman-sorry-migration-plan.md`](huffman-sorry-migration-plan.md) /
> [`relay-sorry-migration-plan.md`](relay-sorry-migration-plan.md) /
> [`mac-bc-sorry-migration-plan.md`](mac-bc-sorry-migration-plan.md) /
> [`brunn-minkowski-sorry-migration-plan.md`](brunn-minkowski-sorry-migration-plan.md).
>
> 本 plan は **8 個の小規模 file (declaration 数 1-2 件)** をまとめて 1 plan で
> sweep する。family ごとに plan を起こすと overhead が大きいため、Phase 2.x で
> file 単位の独立 dispatch が可能なように設計しつつ、Phase 0 / 1 / 1.x audit /
> V の共通骨格を共有する。
>
> 本 plan は **proof completion ではなく legacy tag (`@audit:suspect`) →
> `sorry + @residual(...)` への honesty 強化** (`audit-tags.md`「Deprecated」+
> 「移行レシピ」) を目的とする独立 workstream。proof done は本 plan の出力に
> しない。

## 進捗

- [ ] Phase 0 — Inventory (本 plan 内 inline、verbatim 確認済) ✅
- [ ] Phase 1 — V/C cleanup 📋 → 件数は実質ゼロ予測、Phase 1.x audit に直行
- [ ] Phase 1.4 — audit-1 📋
- [ ] Phase 2.1 — MultivariateDiffEntropy (2 件) 📋
- [ ] Phase 2.2 — WhittakerShannonFull (2 件) 📋
- [ ] Phase 2.3 — ContChannelMIDecomp (2 件) 📋
- [ ] Phase 2.4 — EPIConvolutionDensity (1 件) 📋
- [ ] Phase 2.5 — StationaryKernel (1 件、closed-by-successor 路線) 📋
- [ ] Phase 2.6 — SeparationTheorem (1 件) 📋
- [ ] Phase 2.7 — BirkhoffErgodic (1 件、closed-by-successor 路線) 📋
- [ ] Phase 2.8 — ChannelCodingConverseGeneralComplete (2 件) 📋
- [ ] Phase 2.x — ripple (caller drift、散文 transitive) 📋
- [ ] Phase 2.audit — audit-2 (honesty-auditor) 📋
- [ ] Phase V — verify + 親 plan banner 反映 📋

## Context

### なぜ 1 plan で 8 file をまとめるか

`docs/audit/sorry-migration-runbook.md`「並列実行候補 family」表は各 file の
件数 (大 / 中 / 小) を集計するが、本 cluster の 8 file は **各 1-2 件の超小型**
で、family ごとに 4-section の plan を起こすと plan 文書のほうが本体より重く
なる。pilot Hoeffding (19 件 / 9 file)、Cramer (12 件 / 3 file)、WynerZiv
(22 件 / 8 file)、LZ78 (30 件 / 13 file) 等の plan 構成と比較して、本 cluster
の 12 declaration / 8 file は **per-plan overhead が non-trivial**。

そこで本 plan では:
- **Phase 0 / 1 / 1.x audit / 2.audit / V を共通骨格に集約** (各 file ごとの
  plan で同じ section を書き直すのを避ける)
- **Phase 2.x を file 単位に分離** (各 file が独立 dispatch 可能、worktree
  並列での implementer 配置と整合)
- **cross-family entanglement の有無を Phase 0 で 1 表に集約**

### 在庫 (verbatim 確認、Phase 0)

各 file の `@audit:suspect | @audit:staged | @audit:defer | @audit:closed-by-successor
| 🟢ʰ` を `rg -n` で計数 + Read で declaration tag vs docstring 散文 mention を
分離 (Pilot Pattern D 適用)。

| file | declaration suspect | prose mention (`@audit:suspect` 文字列の docstring 内引用) | 🟢ʰ declaration | 🟢ʰ prose | 既存 sorry (wb) |
|---|---:|---:|---:|---:|---:|
| `MultivariateDiffEntropy.lean` | **2** (lines 237 / 302) | 2 (lines 51 / 586) | 0 | 0 | 0 |
| `WhittakerShannonFull.lean` | **2** (lines 372 / 393) | 0 | 0 | 0 | 0 |
| `ContChannelMIDecomp.lean` | **2** (lines 247 / 649) | 0 | 0 | **2** (lines 47 / 242) | 0 |
| `EPIConvolutionDensity.lean` | **1** (line 67) | 0 | 0 | 0 | 0 |
| `StationaryKernel.lean` | **1** (line 115、**空 slug** `@audit:suspect()`) | 0 | 0 | 0 | 0 |
| `SeparationTheorem.lean` | **1** (line 446) | 0 | 0 | 0 | 0 |
| `BirkhoffErgodic.lean` | **1** (line 1002) | 0 | 0 | 0 | 0 |
| `ChannelCodingConverseGeneralComplete.lean` | **2** (lines 372 / 477) | 0 | 0 | 0 | 0 |
| **合計** | **12** | 2 | 0 | 2 | **0** |

**ブリーフ計数 (14 + 2 🟢ʰ) との差分** (verbatim 義務、CLAUDE.md「具体的数値・
型予測の verbatim 確認」):

- ブリーフは `MultivariateDiffEntropy.lean` の `@audit:suspect` rg ヒット 4 件を
  そのまま declaration 数として計上したが、`rg -nB1 -A2 '@audit:suspect'` の
  verbatim 確認で line 51 / 586 は **docstring 散文内の引用** (`@audit:superseded-by`
  の説明 / Phase B retention rationale)、declaration tag は line 237 / 302 の **2
  件**のみ。
- ブリーフは `ContChannelMIDecomp.lean` の 🟢ʰ 2 件を「declaration の 🟢ʰ load-bearing
  marker」として計上したが、実態は **docstring 内散文** ("body 🟢ʰ genuine" 等の
  prose marker for honesty narrative、deprecated vocabulary の名残)。declaration
  自身に 🟢ʰ marker は付与されていない。本 plan で 🟢ʰ prose は Phase 2.3 (ContChannelMIDecomp)
  で incidental に削除する (CLAUDE.md「Deprecated」表 + 移行レシピ)。
- **既存 `sorry` word-boundary 計数 = 0 件**全 file 共通 (Pilot Pattern D 適用済)。
- **空 slug `@audit:suspect()` 発見**: `StationaryKernel.lean:115` `factor_of_complete_of_pos`
  の `@audit:suspect()` (= slug 未指定)。これは audit-tags.md の `@audit:suspect(PLAN)`
  規約違反 (tier 4 defect-寄り)。後継 `isLZ78PerPathParsingFactorization_of_pos`
  (`StationaryKernel.lean:257`) が a.s. regularity 仮説のみから genuine 構成済の
  ため、`factor_of_complete_of_pos` は **closed-by-successor 路線で retract-candidate
  化** (Phase 2.5)。consumer 0 件 (`rg -n 'factor_of_complete_of_pos\b' Common2026/`
  = 1 hit = 自身 definition のみ)。

実 declaration suspect = **12 件**、内訳 P pattern 10 + closed-by-successor 2 件。

### legacy tag の plan-slug 分布

`@audit:suspect(<slug>)` の slug 別内訳 (verbatim 計数):

| slug | 件数 | 対応 docs file 存在 |
|---|---:|---|
| `multivariate-diffentropy-subadditivity-plan` | 2 | ✅ `docs/shannon/multivariate-diffentropy-subadditivity-plan.md` |
| `whittaker-shannon-partial-moonshot-plan` | 2 | ✅ `docs/shannon/whittaker-shannon-partial-moonshot-plan.md` |
| `awgn-mi-decomp-plan` | 2 | ✅ `docs/shannon/awgn-mi-decomp-plan.md` |
| `epi-convolution-density-plan` | 1 | ✅ `docs/shannon/epi-convolution-density-plan.md` |
| (空 slug `()`) | 1 | ⚠ slug 規約違反、closed-by-successor 路線 |
| `separation-theorem-moonshot-plan` | 1 | ✅ `docs/shannon/separation-theorem-moonshot-plan.md` |
| `birkhoff-ergodic-plan` | 1 | ✅ `docs/shannon/birkhoff-ergodic-plan.md` |
| `channel-coding-shannon-theorem-full-plan` | 2 | ✅ `docs/shannon/channel-coding-shannon-theorem-full-plan.md` |

合計 12 件、空 slug 1 件を除き 11 件は対応 docs file 存在確認済。

### Cross-family 検出 (runbook S1/S2/S3 三段階判定)

各 file の `import` 確認 (`rg -n '^import Common2026' <file>`) + consumer 検出
(`rg -nl '<file の export>'`) の verbatim 結果:

| file | import 関係 (in-tree consumer) | Stage | 判定 |
|---|---|---|---|
| `MultivariateDiffEntropy.lean` | consumer = `ParallelGaussianPerCoord` / `ParallelGaussianPerCoordRegularity` / `ContChannelMIDecomp` / `AWGNMIDecompBody` (Round 3 AWGN cluster 候補) | **S2** | sweep 単独実施 OK。signature 改変は ripple 散文化対象。本 plan scope 内 |
| `WhittakerShannonFull.lean` | consumer = `WhittakerShannonPartial` (parent moonshot 内) のみ | **S1** | 本 plan scope 内 |
| `ContChannelMIDecomp.lean` | consumer = `AWGNMIDecompBody` / `ParallelGaussianPerCoord` / `ParallelGaussianPerCoordRegularity` / `MultivariateDiffEntropy` (AWGN cluster + Multivariate cluster); slug `awgn-mi-decomp-plan` は将来 AWGN sweep (Round 3) の対象になる可能性 | **S2 (AWGN-leaning)** | 本 plan scope 内、ただし AWGN cluster sweep が起きたら drift 可能性、Phase V banner で「将来 AWGN sweep が re-touch する場合は incidental incremental」と注記 (未決事項 #1) |
| `EPIConvolutionDensity.lean` | consumer = self のみ (`rg -nl` 確認、`FisherInfoV2` を import するが consumer 0 件) | **S1** | 本 plan scope 内。**注**: ファイル名 `EPI` prefix だが Round 3 EPI/Stam cluster (`EPIL3Integration` / `EPIStamStep3Body` / `EPIPlumbing` 等、`wall:stam` 集約 family) とは namespace + import で独立 (本 file の namespace は `InformationTheory.Shannon.EPIConvolutionDensity`、EPI/Stam cluster は別 namespace + 別 file)。S3 entanglement 無し |
| `StationaryKernel.lean` | consumer = `LZ78AchievabilityLimsup` / `LZ78TreeInducedAEP` / `LZ78ZivCombinatorics` / `LZ78ZivEntropyBridge` (LZ78 cluster、Round 2 で sweep 完了済 `lz78-sorry-migration-plan.md`)。ただし対象 declaration `factor_of_complete_of_pos` (line 116) の consumer は **0 件** (後継 `isLZ78PerPathParsingFactorization_of_pos` が in-tree successor) | **closed-by-successor (LZ78 cluster 既 sweep 済、孤立 declaration)** | 本 plan scope 内、Phase 2.5 で retract-candidate 化 |
| `SeparationTheorem.lean` | consumer = self のみ (`rg -nl 'SeparationTheorem|separation_converse_iid'` = 1 hit、self only) | **S1** | 本 plan scope 内 |
| `BirkhoffErgodic.lean` | consumer = `SMBAlgoetCover` / `SMBChainRule` (SMB infrastructure family、ただし `birkhoff_ergodic_ae` unconditional 形を consumer。対象 declaration `birkhoff_ergodic_ae_of_limit` (line 1003) は historical wrapper で **consumer 0 件**) | **closed-by-successor** | 本 plan scope 内、Phase 2.7 で retract-candidate 化 |
| `ChannelCodingConverseGeneralComplete.lean` | consumer = `ChannelCodingConverseGeneralStrong` / `ChannelCodingConverseMemorylessPure` / `CondEntropyMemoryless` / `SeparationTheorem` (ChannelCoding cluster) | **S2** | 本 plan scope 内、ripple 散文化対象 |

**S3 entanglement = 0 件**確定。すべて S1/S2/closed-by-successor で本 plan
scope 内で完結可能。Round 3 sweep (EPI/Stam / AWGN) との衝突は **EPIConvolutionDensity
は無関係** (S1)、**ContChannelMIDecomp は将来 AWGN cluster が re-touch する
可能性のみ** (未決事項 #1 に escalate)。

### Honesty workflow と DoD

本 plan の DoD は CLAUDE.md「Definition of Done — 2 段階」の **type-check done**:

- 各 file `lake env lean Common2026/Shannon/<file>.lean` が 0 errors、
- 各新規 `sorry` に `@residual(<class>:<slug>)` タグ、
- 各 Phase 完了時に `honesty-auditor` を起動して classification + signature
  honesty を独立検証。

`@audit:ok` (proof done) は **本 plan の出力にしない**。各親 moonshot plan
(MultivariateDiffEntropy subadditivity / WhittakerShannon partial / etc.) の
analytical closure は別 workstream に残る。

## Approach

**file 単位 sweep を Phase 2.1〜2.8 に分割、Phase 1 (V/C) は skip、Phase 1.4 /
2.audit / V を共通骨格として共有**。Phase 2.x は file 単位で独立 dispatch 可能
(worktree 並列での implementer 配置候補、ただし declaration 数が少ないため逐次
でも 1 セッション完走可)。共有 wall lemma は集約しない (`audit-tags.md` Wall
name register に該当 wall 無し、各 declaration は plan-slug 形で揃える)。

### 戦略の選択軸

`docs/audit/sorry-migration-runbook.md`「並列実行プロトコル」+ pilot 7 件
(Hoeffding / Cramer / Wyner-Ziv / LZ78 / Huffman / Relay / MAC-BC / BrunnMinkowski)
を踏まえた 2 軸決定:

1. **1 plan で 8 file 一括 sweep を採用** (per-file plan ではない)。理由:
   - 各 file 1-2 件の超小型 declaration で、per-file plan を起こすと plan の
     overhead が本体を上回る。Phase 0 inventory + Phase 1.4/2.audit/V を 8 重複
     書くのは無駄。
   - Phase 2.x を file 単位に分離することで、各 file は独立 dispatch 可能 (1
     implementer agent が 1 file 担当、worktree 隔離下で並列実行可)。
   - 8 file 合計 12 declaration は pilot Cramer (12 件 / 3 file) と同等規模で
     1-2 セッション完走可能。

2. **共有 sorry 補題に集約しない**。理由:
   - `docs/audit/audit-tags.md`「Wall name register」表に本 8 file 関連の wall
     (`multivariate-mi` / `nyquist-2w-dof` / `awgn-channel-density` /
     `epi-convolution-pdf` 等は **未登録** または「multivariate-mi」は parallel
     gaussian dependency 用) は **対応 declaration が小規模で wall 集約より
     plan-slug 集約のほうが closure plan と整合**。
   - 12 件の closure 担当は 7 plan slug + 2 closed-by-successor で identified、
     shared wall lemma の置き場所 (新規 `SmallClusterWalls.lean` 等) は不要。

### 移行レシピ (declaration 単位)

pilot 7 family と同様、出現する subpattern を分類:

- **パターン P (load-bearing hypothesis / predicate consumer)**: signature が
  density-split (`h_llr_split`) / channel-converse rate hyp (`hM_ch_bdd` +
  `hR_ch_le_C`) / load-bearing predicate (`IsBandlimitedFull` / `IsAwgnOutputGaussian`
  / `IsPdfAddConvDensityHyp` precursor) / Markov-chain triple
  (`h_yother_zero` + `h_split` + `h_markov_xprefix`) を取り、body はそれを
  destructure / chain composition で使う。
  - 移行: load-bearing hypothesis を **削除**、結論型は変えない、body `sorry`
    + `@residual(plan:<slug>)`。
  - regularity (`IsProbabilityMeasure` / `Measurable` / `IsMarkovChain` の
    `hmarkov` 自身 / SigmaFinite 等) は precondition なので残す。
  - 該当: 10 件 (`MultivariateDiffEntropy` 2 / `WhittakerShannonFull` 2 /
    `ContChannelMIDecomp` 2 / `EPIConvolutionDensity` 1 / `SeparationTheorem`
    1 / `ChannelCodingConverseGeneralComplete` 2)。

- **パターン closed-by-successor (= retract-candidate via in-file successor)**:
  declaration の後継 unconditional 形が **同 file 内に既に存在**し、対象
  declaration の consumer 0 件 (`rg -n '<decl>\b' Common2026/` で
  self-definition line のみ hit)。
  - 移行: `@audit:suspect` 削除 + `@audit:retract-candidate(load-bearing-predicate)`
    付与 + docstring に「後継 `<successor decl name>` (line N)」を明示。
    sorry は付与せず (body は既に constructive)。
  - 該当: 2 件 (`StationaryKernel.lean:116` `factor_of_complete_of_pos` →
    後継 `isLZ78PerPathParsingFactorization_of_pos` (line 257); `BirkhoffErgodic.lean:1003`
    `birkhoff_ergodic_ae_of_limit` → 後継 `birkhoff_ergodic_ae` (line 1033、
    unconditional))。

- **パターン V (variational pass-through、タグ削除のみ)**: 該当 0 件 (現時点
  予測、implementer が inline detection で `constructive recovery` を検証する
  方式は Pilot Pattern B、本 cluster は predicate consumer が主体で V 該当
  なし)。

- **パターン C (in-tree constructive primitive 経由、タグ削除のみ)**: 該当 0
  件 (現時点予測)。

### constructive recovery 候補 (Pilot Pattern B)

| file:line | decl 名 | 結論型 | 構成的回復可能性 |
|---|---|---|---|
| (現時点予測なし) | — | — | implementer step で結論型を再確認、constructive recovery 可能なら sorry を作らず V/C 降格 |

ただし implementer は Phase 2.x 着手前に inline detection (結論型 read +
本来の constructive closure 候補確認) を **必ず** 行うこと。

### transitive sorry の handling 方針 (Pilot Pattern C)

各 file は consumer が他 file (S2 entanglement) に広がるため、Phase 2.x で
sorry 化された declaration は caller side で transitive sorry を生む。pilot 7
family と同様、**transitive sorry に `@residual` を新規付与しない** — 各
declaration の自身の load-bearing hypothesis 削除に対して `@residual(plan:<slug>)`
を 1 つ持ち、上流 sorry への依存は docstring 散文で明示する。即興 `:transitive`
suffix vocabulary は使わない (`audit-tags.md` 未登録)。

caller side で本 plan touch 対象外の file (Round 3 候補 AWGN / EPI/Stam 等)
が transitive sorry を引き継ぐ場合は **Phase 2.x ripple で散文化のみ実施**、
sweep は将来 family 単独 sweep に委ねる。

### HONESTY ALERT / FALSE 検出 — Pattern H 適用なし

CLAUDE.md「検証の誠実性」inline policy + runbook Pattern H に従い、planner
段階で著者明示済 HONESTY ALERT / FALSE predicate を集計:

```bash
rg -n '⚠|HONESTY ALERT|FALSE' Common2026/Shannon/MultivariateDiffEntropy.lean \
  Common2026/Shannon/WhittakerShannonFull.lean \
  Common2026/Shannon/ContChannelMIDecomp.lean \
  Common2026/Shannon/EPIConvolutionDensity.lean \
  Common2026/Shannon/StationaryKernel.lean \
  Common2026/Shannon/SeparationTheorem.lean \
  Common2026/Shannon/BirkhoffErgodic.lean \
  Common2026/Shannon/ChannelCodingConverseGeneralComplete.lean
```

- `StationaryKernel.lean:130-140` の "false equality `boundary c = n`" /
  "*genuinely false* in general" / "the *false* equality `factor`" は **既に
  後継 `_of_pos` で genuine fix 済** (closed-by-successor、Phase 2.5 で retract-
  candidate 化対象)。Pattern H 適用ではなく **closed-by-successor 路線**で処理。

Pattern H (FALSE predicate-conditioned vacuously-true wrapper) 該当 = 0 件。

### Tier 5 defect — inline 検出 (planner 段階)

planner 段階で以下の honesty defect 兆候を verbatim 確認:

- **空 slug** `@audit:suspect()` (`StationaryKernel.lean:115`): audit-tags.md
  「`@audit:suspect(PLAN)`」slug 規約違反、tier 4-寄り (Tier 5 defect ではない
  が slug 未指定で classification 不能)。Phase 2.5 で `@audit:retract-candidate(load-bearing-predicate)`
  付与 + closed-by-successor 路線で処理。

- **循環 `:= h` / `:True` slot / 退化定義悪用 / load-bearing predicate bundling
  / name laundering**: 該当 0 件 (verbatim 確認、各対象 declaration の body は
  constructive transformation または load-bearing hypothesis のまっとうな
  destructure)。

tier 5 defect 該当 = 0 件、tier 4 legacy = 12 件 + 🟢ʰ prose 2 件 + 空 slug 1
件 (重複) で総計 14 個の tag-related cleanup。

## Phase 詳細

### Phase 0 — Inventory (本 plan 内 inline、完了) 📋 ✅

- [x] 各 12 件 declaration suspect + 2 件 prose mention + 2 件 🟢ʰ prose marker
  + 1 件空 slug を verbatim 確認 (`rg -n` + 該当 docstring + signature 1-3
  行を実コード Read)。
- [x] パターン分類 (P / closed-by-successor / V / C)。該当: P=10、closed-by-successor=2、
  V=0、C=0。
- [x] cross-family 依存 確認 (`rg -n '^import Common2026' <file>` + consumer
  検出 `rg -nl '<export>'`)。**S3 entanglement = 0 件、S1=4 / S2=2 /
  closed-by-successor=2**。
- [x] 既存 sorry word-boundary 計数 `0` 件全 file 確定 (Pilot Pattern D 適用済)。
- [x] HONESTY ALERT / FALSE 検出 (`rg -n '⚠|HONESTY ALERT|FALSE'`) → Pattern
  H 該当 0 件 (`StationaryKernel.lean` の FALSE-related 散文は closed-by-successor
  路線で処理)。
- [x] Tier 5 defect 検出 → 0 件 (空 slug 1 件は tier 4-寄り、Phase 2.5 retract-
  candidate 化)。

**proof-log**: no (mechanical 在庫確認、interesting なし)。

### Phase 1 — V/C cleanup (低 risk、新規 sorry なし) 📋

- [ ] **1.1** 現時点予測で V/C 該当ゼロ。Phase 1 は実質 skip。
- [ ] **1.2** implementer は Phase 2.x 着手前に **inline detection (Pilot
  Pattern B)** で各 declaration の結論型を再確認、constructive recovery 可能性
  を判定。可能なら Phase 1 V 扱い (タグ削除のみ)、判断ログに append。

**Phase 1 DoD**: V/C 0-2 件、新規 `sorry` 0 件、`lake env lean` 0 errors。
件数次第で Phase 2.x 件数が ±1-2 変動。

**proof-log**: no (skip 同等、結果のみ判断ログに append)。

### Phase 1.4 — audit-1 (Phase 1 全件 + Phase 0 在庫検証) 📋

- [ ] **1.4.1** orchestrator は `honesty-auditor` (または `general-purpose` +
  brief、CLAUDE.md「Independent honesty audit」) を起動。対象:
  - Phase 0 在庫の verbatim 整合 (cross-family stage 判定、ブリーフ計数差分の
    確認)
  - Phase 1: 0-2 件 (V/C 降格があれば validation)
  - tier 5 defect 検出 0 件の確認
  - Pattern H 該当 0 件の確認 (`StationaryKernel.lean` の FALSE-related 散文
    が closed-by-successor 路線で正しく処理されるかの事前確認)

- [ ] **1.4.2** verdict 受領:
  - `ok` → Phase 2.x 着手
  - `questionable` → docstring refine、Phase 2.x 進行
  - `defect` → 当該 declaration を撤回 / 修正、Phase 2.x 進行前に解決

**proof-log**: yes (auditor verdict 記録、本 cluster で初の「8 file 1 plan」
形式の audit 経験を反映)。

### Phase 2.1 — MultivariateDiffEntropy (2 件、`multivariate-diffentropy-subadditivity-plan`) 📋

対象 declarations (verbatim 確認、`Common2026/Shannon/MultivariateDiffEntropy.lean`):

| line | decl 名 | suspect の核 | パターン | 移行後 |
|---|---|---|---|---|
| 238 | `klDiv_pi_marginals_toReal_eq_sum_sub_joint` | `h_llr_split` (n-variable Bayes density split、`pi_withDensity` を absent in Mathlib として absorb) + 4 integrability hyp + `h_marg_id` (marginal identification) | P (load-bearing density split) | signature 改変 + body sorry + `@residual(plan:multivariate-diffentropy-subadditivity-plan)` |
| 303 | `jointDifferentialEntropyPi_le_sum` | 上の wrapper、`klDiv ≥ 0 + bridge` を linarith で合成、同じ load-bearing hyp を pass-through | P (transitive via line 238) | signature 改変 + body sorry + `@residual(plan:multivariate-diffentropy-subadditivity-plan)` |

- [ ] **2.1.1** `klDiv_pi_marginals_toReal_eq_sum_sub_joint` (line 238):
  - signature から `h_llr_split` (line 245-249)、`h_int_marg` (line 250-251)、
    `h_int_joint` (line 252-253)、`h_marg_id` (line 254-258) を **削除**。
  - 残す: paramter (`{n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μ.map (fun z => z i))]` + `h_marg_ac` (regularity:
    absolute continuity)、`hμ_ac`、`h_joint_ac`)。
  - body: 既存の 5-step proof (h_kl / h_split / h_sub / h_jt / h_mg) を **全削除**
    し `:= by sorry` に置換 + docstring 末尾 `@audit:suspect(...)` →
    `@residual(plan:multivariate-diffentropy-subadditivity-plan)`。
- [ ] **2.1.2** `jointDifferentialEntropyPi_le_sum` (line 303):
  - 同様に load-bearing hyp 削除、body `:= by sorry` + `@residual(plan:multivariate-diffentropy-subadditivity-plan)`。
- [ ] **2.1.3** docstring 内 prose mention (`@audit:suspect` 文字列が含まれる
  line 51 / 586) は **書き換えない** — file header の honesty status 記述 +
  Phase B "撤退条件" 記述。tag そのものではないので migration 対象外。ただし
  該当散文が "the residual discharge target" と書く部分は事実上維持 (本 plan
  で sorry 化することで discharge target の意味は変わらない)。
- [ ] **2.1.4** `lake build Common2026.Shannon.MultivariateDiffEntropy` で olean
  refresh + dependent (`ParallelGaussianPerCoord` / `ParallelGaussianPerCoordRegularity`
  / `ContChannelMIDecomp` / `AWGNMIDecompBody` の caller) 再 verify (Pilot
  Pattern A)。S2 caller の type drift は Phase 2.x ripple で散文化対応。

**Phase 2.1 DoD**:
- `MultivariateDiffEntropy.lean` で `@audit:suspect` declaration tag 0 件 (prose
  mention 2 件は維持)、`@residual(plan:multivariate-diffentropy-subadditivity-plan)`
  2 件、新規 sorry 2 件、
- `lake env lean Common2026/Shannon/MultivariateDiffEntropy.lean` 0 errors。

**proof-log**: no (mechanical sorry 化、prose mention 維持の判断記録のみ判断ログ append)。

### Phase 2.2 — WhittakerShannonFull (2 件、`whittaker-shannon-partial-moonshot-plan`) 📋

対象 declarations (verbatim 確認、`Common2026/Shannon/WhittakerShannonFull.lean`):

| line | decl 名 | suspect の核 | パターン | 移行後 |
|---|---|---|---|---|
| 373 | `shannon_hartley_via_full` | `h_full : IsBandlimitedFull f W` + `h_id` (2W·perSampleAwgnCapacity identity) + 3 regularity (hW / hN₀ / hP) | P (load-bearing `IsBandlimitedFull` consumer) | signature 改変 + body sorry + `@residual(plan:whittaker-shannon-partial-moonshot-plan)` |
| 394 | `shannon_hartley_via_full_bits` | 上の bits/sec variant、`/log 2` で normalize、同じ load-bearing hyp | P (sibling) | 同上 |

- [ ] **2.2.1** `shannon_hartley_via_full` (line 373):
  - signature から `h_full : IsBandlimitedFull f W` を **削除**。残す: `(f : ℝ → ℝ)
    (W N₀ P C : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀) (hP : 0 ≤ P) (h_id : ...)`。
  - body: 既存の `InformationTheory.Shannon.ShannonHartley.shannon_hartley_formula
    W N₀ P hW hN₀ hP C (ShannonHartley_IsBandlimitedSamplingHypothesis_of_full
    ...) (ShannonHartley_IsBandlimitedKernel_of_full f W hW h_full) h_id` を
    削除して `:= by sorry` + `@residual(plan:whittaker-shannon-partial-moonshot-plan)`。
- [ ] **2.2.2** `shannon_hartley_via_full_bits` (line 394):
  - 同様、body `:= by sorry` + `@residual(plan:whittaker-shannon-partial-moonshot-plan)`。
- [ ] **2.2.3** `lake build Common2026.Shannon.WhittakerShannonFull` で olean
  refresh + dependent (`WhittakerShannonPartial`) 再 verify (S1、影響範囲小)。

**Phase 2.2 DoD**:
- 2 件で `@audit:suspect` 0 件、`@residual(plan:whittaker-shannon-partial-moonshot-plan)`
  2 件、新規 sorry 2 件、
- `lake env lean Common2026/Shannon/WhittakerShannonFull.lean` 0 errors。

**proof-log**: no (mechanical sorry 化)。

### Phase 2.3 — ContChannelMIDecomp (2 件、`awgn-mi-decomp-plan`) 📋

対象 declarations (verbatim 確認、`Common2026/Shannon/ContChannelMIDecomp.lean`):

| line | decl 名 | suspect の核 | パターン | 移行後 |
|---|---|---|---|---|
| 248 | `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` | `h_llr_split` (Bayes density split for fibre kernel) + `g`/`hg_meas`/`hg_ae` (measurable PDF proxy) + 3 integrability hyp + 3 ac regularity (hW_ac / hq_ac / h_joint_ac) | P (load-bearing density split + proxy chain) | signature 改変 + body sorry + `@residual(plan:awgn-mi-decomp-plan)` |
| 650 | `awgn_capacity_closed_form_of_out` | `h_out : IsAwgnOutputGaussian` + `h_bdd` (BddAbove) + `h_max_ent` (∀ p, MI ≤ ...) + 3 regularity (P / hP / N / hN) | P (load-bearing `IsAwgnOutputGaussian` consumer + capacity-bound hyp) | 同上 |

- [ ] **2.3.1** `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` (line 248):
  - signature から `g`/`_hg_meas`/`hg_ae`/`h_llr_split`/`h_int_fibre_joint`/
    `h_int_out_joint`/`h_int_out_marg` を **削除**。残す: `(p : Measure ℝ)
    [IsProbabilityMeasure p] (W : Kernel ℝ ℝ) (hW_ac : ∀ x, W x ≪ volume)
    (hq_ac : outputDistribution p W ≪ volume) (h_joint_ac : (p ⊗ₘ W) ≪ p.prod
    (outputDistribution p W))` (regularity)。
  - body: 既存の 8-step proof 削除、`:= by sorry` + `@residual(plan:awgn-mi-decomp-plan)`。
- [ ] **2.3.2** `awgn_capacity_closed_form_of_out` (line 650):
  - signature から `h_out`/`h_bdd`/`h_max_ent` を **削除**。残す: regularity
    (`P / hP / N / hN`)。
  - body: 既存の `h_decomp + awgn_capacity_closed_form_F2_discharged` 合成削除、
    `:= by sorry` + `@residual(plan:awgn-mi-decomp-plan)`。
- [ ] **2.3.3** 🟢ʰ prose marker (line 47 / 242) の **incidental cleanup** (CLAUDE.md
  「Deprecated」表 + 移行レシピ): docstring 内 "🟢ʰ honest" / "🟢ʰ genuine" を
  「genuine 散文」("honest" / "load-bearing" を散文表現) に書換 (`audit-tags.md`
  Deprecated 表「散文 🟢ʰ → @audit:suspect 相当の移行レシピ」を本 plan で
  sorry-based 化済の散文に書換)。
- [ ] **2.3.4** `lake build Common2026.Shannon.ContChannelMIDecomp` で olean
  refresh + dependent (`AWGNMIDecompBody` / `ParallelGaussianPerCoord` /
  `ParallelGaussianPerCoordRegularity` / `MultivariateDiffEntropy`) 再 verify。
  S2 caller の type drift は Phase 2.x ripple で散文化対応。

**Phase 2.3 DoD**:
- `ContChannelMIDecomp.lean` で `@audit:suspect` 0 件、🟢ʰ prose 0 件 (incidental
  migration)、`@residual(plan:awgn-mi-decomp-plan)` 2 件、新規 sorry 2 件、
- `lake env lean Common2026/Shannon/ContChannelMIDecomp.lean` 0 errors。

**proof-log**: yes (🟢ʰ prose incidental migration の判断記録 + 将来 AWGN
sweep が re-touch する場合の方針を proof-log に明示)。

### Phase 2.4 — EPIConvolutionDensity (1 件、`epi-convolution-density-plan`) 📋

対象 declaration (verbatim 確認、`Common2026/Shannon/EPIConvolutionDensity.lean`):

| line | decl 名 | suspect の核 | パターン | 移行後 |
|---|---|---|---|---|
| 68 | `convDensityReal_pos` | `h_pos : 0 < ∫ y, f (z - y) * g y ∂volume` (load-bearing positivity hypothesis、本来 density product の positivity を別途 discharge する必要あり) | P (load-bearing positivity) | signature 改変 + body sorry + `@residual(plan:epi-convolution-density-plan)` |

- [ ] **2.4.1** `convDensityReal_pos` (line 68):
  - signature から `h_pos : 0 < ∫ y, f (z - y) * g y ∂volume` を **削除**。残す:
    `{f g : ℝ → ℝ} (z : ℝ)` (parameter)。
  - body: `rw [convDensityReal_def]; exact h_pos` を削除、`:= by sorry` +
    `@residual(plan:epi-convolution-density-plan)`。
- [ ] **2.4.2** `lake env lean Common2026/Shannon/EPIConvolutionDensity.lean` 0
  errors 確認。S1 (consumer = self のみ) のため dependent 再 verify 不要。
- [ ] **2.4.3** **EPI/Stam cluster との独立性確認** (planner 段階で済、再
  確認用):
  - `EPIConvolutionDensity.lean` は namespace `InformationTheory.Shannon.EPIConvolutionDensity`、
    Round 3 EPI/Stam cluster (`EPIL3Integration` / `EPIStamStep3Body` /
    `EPIPlumbing` / `EPIStamToBridge` / `EPIStamDeBruijnConclusion` /
    `EPIStamDischarge`、`wall:stam` 集約 family) とは namespace + import で
    独立。
  - `rg -n 'EPIConvolutionDensity' Common2026/Shannon/EPIStam*.lean
    Common2026/Shannon/EPIL3Integration.lean Common2026/Shannon/EPIPlumbing.lean
    Common2026/Shannon/EPIStamToBridge.lean Common2026/Shannon/EPIStamDeBruijnConclusion.lean
    Common2026/Shannon/EPIStamDischarge.lean` で 0 hit 確認 (planner 段階確認済)。
  - 本 plan scope 内で sweep 完結、Round 3 EPI/Stam sweep に escalate 不要。

**Phase 2.4 DoD**:
- `EPIConvolutionDensity.lean` で `@audit:suspect` 0 件、`@residual(plan:epi-convolution-density-plan)`
  1 件、新規 sorry 1 件、
- `lake env lean Common2026/Shannon/EPIConvolutionDensity.lean` 0 errors。

**proof-log**: no (mechanical sorry 化、EPI/Stam 独立性は本 plan docstring 明示済)。

### Phase 2.5 — StationaryKernel (1 件、closed-by-successor) 📋

対象 declaration (verbatim 確認、`Common2026/Shannon/StationaryKernel.lean`):

| line | decl 名 | suspect の核 | パターン | 移行後 |
|---|---|---|---|---|
| 116 | `factor_of_complete_of_pos` | `hcomplete` (parse-completeness `boundary c = n`、後に判明した **genuinely false** in general) + `hpos` (regularity)、現 docstring に「false equality」明示済 | closed-by-successor (in-file successor `isLZ78PerPathParsingFactorization_of_pos` line 257 が a.s. regularity のみから genuine 構成) | `@audit:suspect()` 削除 + `@audit:retract-candidate(load-bearing-predicate)` 付与 + docstring に「closed by successor `isLZ78PerPathParsingFactorization_of_pos` (line 257)」明示 |

- [ ] **2.5.1** `factor_of_complete_of_pos` (line 116):
  - **空 slug `@audit:suspect()` を削除**。
  - `@audit:retract-candidate(load-bearing-predicate)` を docstring 末尾に **新規
    付与** + 既存 docstring に「Phase 2.5 retract-candidate: 後継 unconditional
    版 `isLZ78PerPathParsingFactorization_of_pos` (line 257) が a.s. regularity
    のみから genuine 構成済。`hcomplete` (`boundary c = n`) は LZ78 greedy parse
    で **genuinely false** in general (`lz78PhraseStrings_total_length_le` は `≤`
    で `=` ではない) 。LZ78 Round 2 sweep (`docs/shannon/lz78-sorry-migration-plan.md`)
    完了済、consumer 0 件 (verbatim)」を明示。
  - body **改変なし** (constructive proof は維持、closed-by-successor 路線の
    bookkeeping のみ)、sorry 化なし。
- [ ] **2.5.2** consumer 0 件の verbatim 再確認: `rg -n 'factor_of_complete_of_pos\b'
  Common2026/` で self-definition 1 hit のみ。

**Phase 2.5 DoD**:
- `StationaryKernel.lean` で `@audit:suspect` 0 件 (空 slug 含む)、`@audit:retract-candidate(load-bearing-predicate)`
  1 件、新規 sorry **0 件** (closed-by-successor 路線)、
- `lake env lean Common2026/Shannon/StationaryKernel.lean` 0 errors。

**proof-log**: yes (closed-by-successor 路線の判断記録 + 空 slug `@audit:suspect()`
の slug 規約違反扱いの記録 + LZ78 cluster との関係明示)。

### Phase 2.6 — SeparationTheorem (1 件、`separation-theorem-moonshot-plan`) 📋

対象 declaration (verbatim 確認、`Common2026/Shannon/SeparationTheorem.lean`):

| line | decl 名 | suspect の核 | パターン | 移行後 |
|---|---|---|---|---|
| 447 | `separation_converse_iid` | `hM_ch_bdd : ∀ n, Real.log (M_ch n : ℝ) / n ≤ R_ch` + `hR_ch_le_C : R_ch ≤ capacity W` (channel-side rate hyp、docstring に "passed through as a hypothesis" + "the published black-box from a future channel converse plan" 明示) + regularity (IID source / Measurable / IdentDistrib / hcard / hPe_to_zero / hM_src_bdd) | P (load-bearing channel-side rate hyp、composition glue) | signature 改変 + body sorry + `@residual(plan:separation-theorem-moonshot-plan)` |

- [ ] **2.6.1** `separation_converse_iid` (line 447):
  - signature から `hM_ch_bdd : ∀ n, Real.log (M_ch n : ℝ) / n ≤ R_ch` +
    `hR_ch_le_C : R_ch ≤ ChannelCoding.capacity W` を **削除**。残す: IID source
    parameters (`Xs` / `hXs` / `hindep_full` / `hident` / `hcard`)、code family
    parameters (`M_src` / `M_ch` / `c_src` / `d_src` / `h_le` / `W` / `c_ch`)、
    `hPe_to_zero`、`hM_src_bdd`。
  - body: 既存の Step 1 (sourceError_tendsto_zero_of_composed) + Step 2
    (source_coding_converse) + Step 3 (liminf inequality via h_le) + 後続 sandwich
    削除、`:= by sorry` + `@residual(plan:separation-theorem-moonshot-plan)`。
- [ ] **2.6.2** `lake build Common2026.Shannon.SeparationTheorem` で olean
  refresh。S1 (consumer = self) のため dependent 再 verify 不要。

**Phase 2.6 DoD**:
- `SeparationTheorem.lean` で `@audit:suspect` 0 件、`@residual(plan:separation-theorem-moonshot-plan)`
  1 件、新規 sorry 1 件、
- `lake env lean Common2026/Shannon/SeparationTheorem.lean` 0 errors。

**proof-log**: no (mechanical sorry 化)。

### Phase 2.7 — BirkhoffErgodic (1 件、closed-by-successor) 📋

対象 declaration (verbatim 確認、`Common2026/Shannon/BirkhoffErgodic.lean`):

| line | decl 名 | suspect の核 | パターン | 移行後 |
|---|---|---|---|---|
| 1003 | `birkhoff_ergodic_ae_of_limit` | `gInf` (a.e. limit function、`hg_meas` strong measurability + `hg_inv` T-invariance + `hg_int` integral 一致 + `hg_lim` 既存 a.e. Tendsto) の 4 hypothesis pack (= the limit function 自身を hypothesis として渡す load-bearing 形) | closed-by-successor (in-file successor `birkhoff_ergodic_ae` line 1033 が **unconditional**、Mathlib's ergodic theory + `ae_eq_const_of_ae_eq_comp_ae` で純構成的 closure 済) | `@audit:suspect` 削除 + `@audit:retract-candidate(load-bearing-predicate)` 付与 + docstring に「closed by successor `birkhoff_ergodic_ae` (line 1033、unconditional)」明示 |

- [ ] **2.7.1** `birkhoff_ergodic_ae_of_limit` (line 1003):
  - `@audit:suspect(birkhoff-ergodic-plan)` を削除。
  - `@audit:retract-candidate(load-bearing-predicate)` を docstring 末尾に新規
    付与 + 「Phase 2.7 retract-candidate: 後継 unconditional 版 `birkhoff_ergodic_ae`
    (line 1033) が Mathlib's `Ergodic.ae_eq_const_of_ae_eq_comp_ae` 経由で純構成的
    closure 済。本 wrapper は historical hypothesis-form pass-through で、consumer
    0 件 (verbatim、`rg -n 'birkhoff_ergodic_ae_of_limit\b' Common2026/` で
    self-definition 1 hit のみ)」を明示。
  - body **改変なし** (constructive proof は維持、closed-by-successor 路線の
    bookkeeping のみ)、sorry 化なし。
- [ ] **2.7.2** consumer 0 件の verbatim 再確認: `rg -n 'birkhoff_ergodic_ae_of_limit\b'
  Common2026/` で self-definition 1 hit のみ。

**Phase 2.7 DoD**:
- `BirkhoffErgodic.lean` で `@audit:suspect` 0 件、`@audit:retract-candidate(load-bearing-predicate)`
  1 件、新規 sorry **0 件** (closed-by-successor 路線)、
- `lake env lean Common2026/Shannon/BirkhoffErgodic.lean` 0 errors。

**proof-log**: yes (closed-by-successor 路線の判断記録 — 後継 `birkhoff_ergodic_ae`
が unconditional に discharge 済の事実は Phase 0 planner 段階で verbatim 確認、
本 declaration が legacy wrapper として残存する理由を bookkeeping)。

### Phase 2.8 — ChannelCodingConverseGeneralComplete (2 件、`channel-coding-shannon-theorem-full-plan`) 📋

対象 declarations (verbatim 確認、`Common2026/Shannon/ChannelCodingConverseGeneralComplete.lean`):

| line | decl 名 | suspect の核 | パターン | 移行後 |
|---|---|---|---|---|
| 373 | `memoryless_per_summand_bound` | Phase C lemma、`h_yother_zero` (Step 2: Yother 項零) + `h_split` (Step 1: Y-axis 2-var conditional chain rule split) + `h_markov_xprefix` (Step 3: augmented Markov chain) の **Markov-chain manipulation triple** (docstring に "Markov-chain manipulations not yet in `CondMutualInfo.lean`" 明示) | P (load-bearing Markov triple) | signature 改変 + body sorry + `@residual(plan:channel-coding-shannon-theorem-full-plan)` |
| 478 | `channel_coding_converse_general_memoryless` | Phase D main theorem、同じ Markov triple (h_yother_zero / h_split / h_markov_xprefix) を pass-through + `h_memo : IsMemorylessChannel` + standard regularity (Msg / encoder / Ys / decoder / hMsg / hYs / hdecoder / hmarkov) | P (Phase C consumer、同じ Markov triple) | 同上 |

- [ ] **2.8.1** `memoryless_per_summand_bound` (line 373):
  - signature から `h_yother_zero` (line 379-384)、`h_split` (line 387-396)、
    `h_markov_xprefix` (line 400-405) を **削除**。残す: `μ` + `IsProbabilityMeasure
    μ` + `Xs` / `Ys` / `hXs` / `hYs` + `_h_memo : IsMemorylessChannel μ Xs Ys`
    (precondition、本来 Markov triple を derive する base hyp)。
  - body: 既存の Step 1+2+3+4 proof (h_chain / h_aug_le / h_condMI_le_aug) 削除、
    `:= by sorry` + `@residual(plan:channel-coding-shannon-theorem-full-plan)`。
- [ ] **2.8.2** `channel_coding_converse_general_memoryless` (line 478):
  - signature から `h_yother_zero` (line 487-492)、`h_split` (line 493-505)、
    `h_markov_xprefix` (line 506+) を **削除**。残す: Msg / encoder / Ys /
    decoder / hMsg / hYs / hdecoder / hmarkov / h_memo / 他 standard regularity。
  - body: 既存の D-2 既存 chain-rule decomposition + Phase C per-summand bound +
    Fano sum + linarith 合成削除、`:= by sorry` + `@residual(plan:channel-coding-shannon-theorem-full-plan)`。
- [ ] **2.8.3** `lake build Common2026.Shannon.ChannelCodingConverseGeneralComplete`
  で olean refresh + dependent (`ChannelCodingConverseGeneralStrong` /
  `ChannelCodingConverseMemorylessPure` / `CondEntropyMemoryless` /
  `SeparationTheorem`) 再 verify。S2 caller の type drift は Phase 2.x ripple
  で散文化対応 (特に Phase 2.6 `SeparationTheorem` で sorry 化済の
  `separation_converse_iid` との関係: transitive ではなく **independent**
  load-bearing — 両方の declaration がそれぞれ別個の load-bearing hyp を持つ)。

**Phase 2.8 DoD**:
- `ChannelCodingConverseGeneralComplete.lean` で `@audit:suspect` 0 件、
  `@residual(plan:channel-coding-shannon-theorem-full-plan)` 2 件、新規 sorry 2
  件、
- `lake env lean Common2026/Shannon/ChannelCodingConverseGeneralComplete.lean` 0
  errors。

**proof-log**: no (mechanical sorry 化、ChannelCoding cluster の他 file との
独立性は Phase 0 planner 段階で確認済)。

### Phase 2.x — ripple (caller drift handling, 散文 transitive 明示) 📋

Phase 2.1-2.8 の signature 改変結果として、以下 caller が transitive sorry を
引き継ぐ可能性を `rg` で再確認:

- **MultivariateDiffEntropy (Phase 2.1)** → `ParallelGaussianPerCoord` /
  `ParallelGaussianPerCoordRegularity` / `ContChannelMIDecomp` / `AWGNMIDecompBody`
- **ContChannelMIDecomp (Phase 2.3)** → `AWGNMIDecompBody` /
  `ParallelGaussianPerCoord` / `ParallelGaussianPerCoordRegularity` /
  `MultivariateDiffEntropy`
- **ChannelCodingConverseGeneralComplete (Phase 2.8)** → `ChannelCodingConverseGeneralStrong`
  / `ChannelCodingConverseMemorylessPure` / `CondEntropyMemoryless` /
  `SeparationTheorem`
- (Phase 2.2 WhittakerShannonFull は WhittakerShannonPartial が consumer、S1)
- (Phase 2.4 EPIConvolutionDensity は S1)
- (Phase 2.5 StationaryKernel は closed-by-successor、新規 sorry 0 件で ripple
  なし)
- (Phase 2.6 SeparationTheorem は S1)
- (Phase 2.7 BirkhoffErgodic は closed-by-successor、ripple なし)

- [ ] **2.x.1** Phase 2.1 / 2.3 / 2.8 の caller drift を `rg -l` で列挙:
  ```bash
  rg -l 'klDiv_pi_marginals_toReal_eq_sum_sub_joint|jointDifferentialEntropyPi_le_sum' Common2026/Shannon/ | grep -v MultivariateDiffEntropy
  rg -l 'mutualInfoOfChannel_toReal_eq_diffEntropy_sub|awgn_capacity_closed_form_of_out' Common2026/Shannon/ | grep -v ContChannelMIDecomp
  rg -l 'memoryless_per_summand_bound|channel_coding_converse_general_memoryless' Common2026/Shannon/ | grep -v ChannelCodingConverseGeneralComplete
  ```

- [ ] **2.x.2** 各 caller に transitive sorry が発生したか `lake env lean
  <caller>` で確認。発生した場合は docstring に **transitive sorry の散文** を
  追加 (Pilot Pattern C):
  ```
  Transitive `sorry` via `<upstream decl>` (Phase 2.x retreat, small-cluster
  sorry-migration). No `@residual` tag is attached — the closure responsibility
  belongs to the upstream declaration's `@residual(<class>:<slug>)`.
  ```
  即興 `(<class>:<slug>, transitive)` vocabulary 禁止 (audit-tags.md 未登録)。

- [ ] **2.x.3** 当該 caller が本 plan touch 対象外の file (例: Round 3 候補
  AWGN cluster の `AWGNMIDecompBody` / Parallel Gaussian cluster の
  `ParallelGaussianPerCoord`) の場合、**docstring 散文追加のみ**、当該 caller
  自身の sorry-based migration は **将来 family 単独 sweep に委ねる** (Round 3
  AWGN sweep または別 cluster sweep の対象)。

- [ ] **2.x.4** ripple 完了時 全 file (本 plan touch 8 file + ripple 範囲の
  caller) で `lake env lean` 再 verify。olean refresh は各 file 単位で済ませる
  (Pilot Pattern A、CLAUDE.md「After upstream edits」)。

**Phase 2.x DoD**:
- 全 caller の transitive sorry が散文化済 (本 plan touch 対象外の caller を
  含む)、即興 vocabulary 0 件、
- 各 file `lake env lean` 0 errors。

**proof-log**: yes (ripple 範囲 + 本 plan touch 対象外 caller の散文化判断記録
+ 将来 AWGN / ParallelGaussian sweep への引き継ぎ事項)。

### Phase 2.audit — audit-2 (Phase 2.1-2.8 + 2.x 全件) 📋

- [ ] **2.audit.1** orchestrator は `honesty-auditor` を起動。対象:
  - Phase 2.1-2.4 / 2.6 / 2.8: 10 declarations の P retreat (load-bearing
    hypothesis 削除 + body sorry 化 + `@residual(plan:...)` 付与) の signature
    honesty + classification 正しさ
  - Phase 2.5 / 2.7: 2 declarations の closed-by-successor 路線
    (`@audit:retract-candidate(load-bearing-predicate)` 付与 + 後継 successor
    docstring 明示) の妥当性 + consumer 0 件の再 verify
  - Phase 2.3: 🟢ʰ prose incidental migration の妥当性 (CLAUDE.md「Deprecated」
    表 + 移行レシピ準拠)
  - Phase 2.5: 空 slug `@audit:suspect()` の retract-candidate 化が tier 4
    legacy の正しい救済方法か (slug 規約違反からの retract 経路の vocabulary
    整合)
  - Phase 2.x: 全 caller の transitive 散文の vocabulary 整合 + 即興 tag 不在
    確認

- [ ] **2.audit.2** verdict 受領 + 修正対応:
  - `ok` → Phase V 着手
  - `questionable` → docstring refine、Phase V 進行
  - `defect` → 当該 declaration を撤回 / 修正、Phase V 進行前に解決

**proof-log**: yes (auditor verdict + 修正対応記録、8 file 1 plan 形式の audit
経験を pilot 7 family と比較した知見)。

### Phase V — verify + 親 plan banner 反映 📋

- [ ] **V.1** 全 8 file で `lake env lean` 確認 (signature 改変があった file は
  事前 olean refresh、Pilot Pattern A):
  ```bash
  for f in Common2026/Shannon/MultivariateDiffEntropy.lean \
           Common2026/Shannon/WhittakerShannonFull.lean \
           Common2026/Shannon/ContChannelMIDecomp.lean \
           Common2026/Shannon/EPIConvolutionDensity.lean \
           Common2026/Shannon/StationaryKernel.lean \
           Common2026/Shannon/SeparationTheorem.lean \
           Common2026/Shannon/BirkhoffErgodic.lean \
           Common2026/Shannon/ChannelCodingConverseGeneralComplete.lean; do
    echo "=== $f ==="
    lake env lean "$f"
  done
  ```

- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg -c '@audit:suspect' Common2026/Shannon/{MultivariateDiffEntropy,WhittakerShannonFull,ContChannelMIDecomp,EPIConvolutionDensity,StationaryKernel,SeparationTheorem,BirkhoffErgodic,ChannelCodingConverseGeneralComplete}.lean | awk -F: '{s+=$2} END {print "declaration suspect:", s}'
  # 期待: 2 (MultivariateDiffEntropy.lean の prose mention line 51 / 586 のみ、
  #       他 file は 0)。declaration tag は 0 件。

  rg -c '@residual\(plan:multivariate-diffentropy-subadditivity-plan\)' Common2026/Shannon/MultivariateDiffEntropy.lean   # = 2
  rg -c '@residual\(plan:whittaker-shannon-partial-moonshot-plan\)' Common2026/Shannon/WhittakerShannonFull.lean   # = 2
  rg -c '@residual\(plan:awgn-mi-decomp-plan\)' Common2026/Shannon/ContChannelMIDecomp.lean   # = 2
  rg -c '@residual\(plan:epi-convolution-density-plan\)' Common2026/Shannon/EPIConvolutionDensity.lean   # = 1
  rg -c '@residual\(plan:separation-theorem-moonshot-plan\)' Common2026/Shannon/SeparationTheorem.lean   # = 1
  rg -c '@residual\(plan:channel-coding-shannon-theorem-full-plan\)' Common2026/Shannon/ChannelCodingConverseGeneralComplete.lean   # = 2

  rg -c '@audit:retract-candidate' Common2026/Shannon/StationaryKernel.lean Common2026/Shannon/BirkhoffErgodic.lean   # = 1 + 1 = 2

  rg -c '🟢ʰ' Common2026/Shannon/ContChannelMIDecomp.lean   # = 0 (incidental migration 後)

  rg -nw 'sorry' Common2026/Shannon/{MultivariateDiffEntropy,WhittakerShannonFull,ContChannelMIDecomp,EPIConvolutionDensity,StationaryKernel,SeparationTheorem,BirkhoffErgodic,ChannelCodingConverseGeneralComplete}.lean | wc -l
  # 期待: 10 件 (P pattern 各 1 sorry: MD 2 + WS 2 + CC 2 + EPI 1 + Sep 1 + ChC 2 = 10、
  #             closed-by-successor 2 件は sorry なし)
  ```
  期待値: declaration suspect 0、prose mention 2 (MultivariateDiffEntropy 維持)、
  residual 合計 10 (各 plan-slug)、retract-candidate 2、🟢ʰ 0、新規 sorry 10
  件。

- [ ] **V.3** 親 plan banner 更新 (7 plan):
  - `multivariate-diffentropy-subadditivity-plan.md` 冒頭 banner に「sorry-based
    移行完了 (`docs/shannon/small-cluster-sorry-migration-plan.md` Phase 2.1 参
    照)、`n`-variable load-bearing hyp は本 plan の closure 待ち」追記。
  - `whittaker-shannon-partial-moonshot-plan.md` 冒頭 banner に「sorry-based 移
    行完了 (Phase 2.2)」追記。
  - `awgn-mi-decomp-plan.md` 冒頭 banner に「sorry-based 移行完了 (Phase 2.3)、
    将来 AWGN cluster sweep が re-touch する可能性あり (未決事項 #1)」追記。
  - `epi-convolution-density-plan.md` 冒頭 banner に「sorry-based 移行完了
    (Phase 2.4)、EPI/Stam cluster (Round 3 候補) とは独立」追記。
  - `separation-theorem-moonshot-plan.md` 冒頭 banner に「sorry-based 移行完了
    (Phase 2.6)」追記。
  - `birkhoff-ergodic-plan.md` 冒頭 banner に「sorry-based 移行完了 (Phase 2.7、
    closed-by-successor 路線: `birkhoff_ergodic_ae` unconditional が in-file
    successor)」追記。
  - `channel-coding-shannon-theorem-full-plan.md` 冒頭 banner に「sorry-based
    移行完了 (Phase 2.8、Phase C + D の Markov triple は本 plan の closure 待
    ち)」追記。

- [ ] **V.4** Pilot 知見を `.claude/handoff-sorry-migration.md` または後続
  family sweep 用テンプレートに反映:
  - **8 file 1 plan 形式** (per-file plan overhead を避けるための共通骨格
    集約形式) の手順を runbook 化候補。本 cluster は 8 file × 1-2 件で実証。
    Round 3 候補表に「small-cluster」分類を追加する PR を別途検討 (`docs/audit/sorry-migration-runbook.md`
    並列実行候補 family 表)。
  - **closed-by-successor 路線** (in-file successor が unconditional / a.s.
    regularity-only で genuine discharge 済の場合、retract-candidate 化 + sorry
    なし) の手順を pilot として記録。本 cluster は 2 件で実証 (StationaryKernel
    / BirkhoffErgodic)。
  - **空 slug `@audit:suspect()` の発見** (StationaryKernel.lean:115) — slug
    規約違反 (tier 4-寄り) の発見と retract-candidate 化への救済経路。
  - **🟢ʰ prose incidental migration** (ContChannelMIDecomp.lean 2 件) — declaration
    tag ではなく docstring 内 prose marker を「genuine / load-bearing」散文に
    書換する手順。

## 撤退ライン

- **L-MIG-1 (variational hyp / regularity hyp の load-bearing 判定が auditor で
  変動)**: 本 cluster は予測 V/C 0 件 (P pattern 10 + closed-by-successor 2 の
  みで構成)。auditor が「~~load-bearing と判定した hyp は実は variational pass-
  through~~」と判定したら、当該 declaration を Phase 1 V 扱いに降格 (タグ削除
  のみ、`@residual` 削除)。実装段階 inline detection (Pilot Pattern B) で
  implementer が事前検証する想定だが、Phase 1.4 audit-1 で確定。

- **L-MIG-2 (signature 改変で外部 consumer drift が大量発生)**: 本 cluster の
  10 declaration (closed-by-successor 2 件を除く) のうち、S2 caller を持つのは
  6 declaration (MultivariateDiffEntropy 2 + ContChannelMIDecomp 2 +
  ChannelCodingConverseGeneralComplete 2)。caller drift は Phase 2.x ripple で
  散文化対応 (本 plan touch 対象外 caller は将来 family 単独 sweep に委ねる
  方針)。drift が **大量** (>10 caller / file) になる場合は L-MIG-2 を発動して
  該当 Phase 2.x を **中断** し未決事項 #1 / #2 を user に escalate。

- **L-MIG-3 (closed-by-successor 路線で auditor pushback)**: Phase 2.5 / 2.7 で
  declaration を `@audit:retract-candidate(load-bearing-predicate)` 付与のみ
  (sorry なし) で済ませる方針だが、auditor が「retract-candidate ではなく
  `@audit:closed-by-successor(<slug>)` 形が正しい」と判定したら、後者に書換
  (`@audit:closed-by-successor(<successor name>)`)。`audit-tags.md` Deprecated
  表に `@audit:closed-by-successor` 移行レシピ既登録、本 plan のデフォルトは
  retract-candidate 形だが、auditor 判定を優先 (Pilot Pattern F 同等の inline
  detection)。

- **L-MIG-4 (Approach 変更: cluster scope を縮める)**: 全 Phase が 1-2 セッション
  で完走しない / honesty-auditor が DEFECT を多発させる場合、Phase 2.1-2.4 +
  2.5 + 2.7 (= 6 file、最も小さい file 群) のみで pilot を close し、Phase 2.6
  + 2.8 (SeparationTheorem + ChannelCodingConverseGeneralComplete、相対的に
  大きい signature 改変が必要な 2 file) は後続 session に分離。

## 未決事項 (auditor / user 委任可)

1. **ContChannelMIDecomp と将来 AWGN cluster sweep の関係** (user 判断):
   `ContChannelMIDecomp.lean` の 2 declaration (`mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
   + `awgn_capacity_closed_form_of_out`) は slug `awgn-mi-decomp-plan` で識別、
   将来 `docs/audit/sorry-migration-runbook.md` 並列実行候補表の Round 3
   「AWGN」cluster (200+ 行 bundle predicate 既知) の sweep が起きる場合、本
   plan で sorry 化した 2 declaration を re-touch する可能性。**本 plan の
   デフォルト**: 本 plan で sorry 化し、AWGN sweep が起きたら incidental に
   refine。**代替案**: AWGN sweep 完了を待ち、本 plan では ContChannelMIDecomp
   を scope 外として deferred。user 確認待ち。

2. **8 file 1 plan 形式の runbook 反映** (user 判断、Phase V.4 連動):
   本 plan は per-family plan ではなく **「small cluster (各 file 1-2 件)」
   分類**で 8 file を 1 plan に集約。同様の cluster (RateDistortion 2 件 /
   ChannelCodingFeedback 3 件 / ChernoffInformation 8 件 等) が今後発生した場合、
   本 plan の形式を runbook に「Round 4 small-cluster sweep」として追加すべきか
   user 判断対象。**本 plan の Phase V.4** で runbook 拡張 PR 候補として
   handoff 反映予定。

3. **closed-by-successor 路線の vocabulary 確定** (auditor 判定対象、L-MIG-3
   連動): Phase 2.5 / 2.7 で `@audit:retract-candidate(load-bearing-predicate)`
   付与方針だが、`audit-tags.md` Deprecated 表に `@audit:closed-by-successor(SLUG)`
   形が既登録 + 移行レシピあり。**本 plan のデフォルト**: retract-candidate
   形 (より精確に「後継により closure 済 + 削除候補」を表現)。**代替案**:
   `@audit:closed-by-successor(<successor decl name>)` 形 (history record を
   明示)。auditor 判定優先。

4. **空 slug `@audit:suspect()` の救済経路** (auditor 判定対象):
   `StationaryKernel.lean:115` の `@audit:suspect()` は slug 規約違反 (tier 4-
   寄り)。本 plan のデフォルトは Phase 2.5 で retract-candidate 化 (closed-by-
   successor 路線)、但し auditor が「slug を後付けして `@audit:suspect(lz78-blockrv-refactor-plan)`
   (歴史的に LZ78 cluster の一部) で記録すべき」と判定する可能性。**auditor 判定**:
   空 slug をどう処理するかは audit-tags.md「`@audit:suspect(PLAN)` の slug 規約」
   解釈問題、auditor verdict 委任。

5. **🟢ʰ prose marker の incidental cleanup 強度** (auditor 判定対象):
   Phase 2.3 で `ContChannelMIDecomp.lean` の 🟢ʰ 2 件 (line 47 / 242、docstring
   内 prose marker) を「genuine / load-bearing」散文に書換するが、auditor が
   「prose marker は触らずに本 plan scope を最小化すべき」と判定したら incidental
   migration を skip + 散文維持。本 plan のデフォルトは incidental cleanup (CLAUDE.md
   「Deprecated」表 + 移行レシピ準拠)、auditor 判定優先。

6. **proof done を本 plan で目指さない方針の明示確認** (user 確認):
   本 plan の DoD は **type-check done** のみ。各親 moonshot plan の analytical
   closure (Multivariate `n`-variable `pi_withDensity` discharge / WhittakerShannon
   `IsBandlimitedFull` discharge / AWGN `IsAwgnOutputGaussian` discharge /
   EPIConvolution `convDensityReal_pos` discharge / Separation channel-converse
   black-box / ChannelCoding Markov-chain manipulations) は **未着手のまま** で
   本 plan は close する。各親 plan の closure 状態を変えない。user の合意確認
   のため明示。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-26 plan 起草**: lean-planner (本 session、docs-only) が `Common2026/Shannon/{MultivariateDiffEntropy,WhittakerShannonFull,ContChannelMIDecomp,EPIConvolutionDensity,StationaryKernel,SeparationTheorem,BirkhoffErgodic,ChannelCodingConverseGeneralComplete}.lean` 8 file の legacy tag を verbatim 読込で per-declaration 分類。
   - **計数誤差発見** (Pilot Pattern D 適用):
     - ブリーフ「14 + 2 🟢ʰ」は実測 declaration suspect 12 件 + prose mention 2 件
       + 🟢ʰ prose 2 件に修正 (`rg -nB1 -A2 '@audit:suspect'` verbatim 確認)。
     - ブリーフ MultivariateDiffEntropy "4 件" は declaration tag 2 件 + docstring 散文 mention 2 件 (line 51 = `@audit:superseded-by` 説明文中の引用 / line 586 = Phase B retention rationale)。declaration tag は line 237 / 302 の 2 件のみ。
     - ブリーフ ContChannelMIDecomp "🟢ʰ 2 件" は declaration tag ではなく docstring 内 prose marker (line 47 = "body 🟢ʰ genuine"、line 242 = "🟢ʰ honest") で declaration の 🟢ʰ tag ではない。
   - **既存 sorry 計数**: word-boundary `rg -nw 'sorry'` で全 file 0 hit 確定、実 sorry 0 件 (Pilot Pattern D 適用済)。
   - **空 slug 発見** (planner 段階 inline 検出): `StationaryKernel.lean:115` `factor_of_complete_of_pos` の `@audit:suspect()` (slug 未指定、audit-tags.md 規約違反、tier 4-寄り)。後継 `isLZ78PerPathParsingFactorization_of_pos` (line 257) が a.s. regularity 仮説のみから genuine 構成済の事実を verbatim 確認、consumer 0 件 (`rg -n 'factor_of_complete_of_pos\b' Common2026/` = self-definition 1 hit のみ)。Phase 2.5 で closed-by-successor 路線で処理。
   - **BirkhoffErgodic closed-by-successor 確認** (planner 段階 inline 検出): `birkhoff_ergodic_ae_of_limit` (line 1003) の後継 `birkhoff_ergodic_ae` (line 1033) が unconditional に in-file 構成済の事実を verbatim 確認 (line 1037-1107、Mathlib's `Ergodic.ae_eq_const_of_ae_eq_comp_ae` + 4-step proof で純構成的 closure)、consumer 0 件 (`rg -n 'birkhoff_ergodic_ae_of_limit\b' Common2026/` = self-definition 1 hit のみ)。Phase 2.7 で closed-by-successor 路線。
   - **cross-family entanglement = S3 0 件確定**: 8 file の `import` を verbatim 確認、`Common2026/Shannon/<file>.lean` の export を `rg -nl` で consumer 検出。すべて S1 (4 件) / S2 (2 件) / closed-by-successor (2 件) で本 plan scope 内完結可能。**EPI/Stam cluster との独立性**: `EPIConvolutionDensity.lean` は namespace `InformationTheory.Shannon.EPIConvolutionDensity` + import は `FisherInfoV2` のみ、Round 3 EPI/Stam cluster (`EPIStam*` / `EPIL3Integration` / `EPIPlumbing` 等) との entanglement 0 件 verbatim 確認。
   - **戦略決定**: 8 file 1 plan 一括 sweep + Phase 2.x を file 単位に分離 (独立 dispatch 可能) + 共有 wall lemma 集約しない (`audit-tags.md` Wall register 未登録) + 並列実行は dispatch 可だが declaration 数が少ないため逐次でも 1 セッション完走可。Phase 順序: 0 → 1 (V/C cleanup 候補 0 件予測 → skip) → 1.4 audit-1 → 2.1-2.8 (file 単位 sweep、closed-by-successor 2 件含む) → 2.x ripple → 2.audit audit-2 → V verify。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
