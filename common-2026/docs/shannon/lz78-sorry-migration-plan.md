# Shannon: LZ78 legacy-tag → sorry-based migration plan

> **Parent**: [`lz78-moonshot-plan.md`](lz78-moonshot-plan.md) +
> [`lz78-residual-discharge-plan.md`](lz78-residual-discharge-plan.md) +
> [`lz78-ziv-inequality-discharge-moonshot-plan.md`](lz78-ziv-inequality-discharge-moonshot-plan.md) +
> [`lz78-blockrv-refactor-plan.md`](lz78-blockrv-refactor-plan.md) +
> [`lz78-achievability-converse-plan.md`](lz78-achievability-converse-plan.md)
> + [`audit/sorry-migration-runbook.md`](../audit/sorry-migration-runbook.md)
> + [`audit/audit-tags.md`](../audit/audit-tags.md)。
> Pilot references:
> [`hoeffding-sorry-migration-plan.md`](hoeffding-sorry-migration-plan.md) /
> [`cramer-sorry-migration-plan.md`](cramer-sorry-migration-plan.md) /
> [`wynerziv-sorry-migration-plan.md`](wynerziv-sorry-migration-plan.md).
>
> 本 plan は **proof completion ではなく legacy tag (`@audit:suspect` /
> 散文 `🟢ʰ` / 残存 `@audit:defect(*)`) → `sorry + @residual(...)` への
> honesty 強化** (`audit-tags.md`「Deprecated」+「移行レシピ」) を目的とする
> 独立 workstream。proof done は本 plan の出力にしない。

## Context

### なぜ LZ78 が次の sweep family か

`docs/audit/sorry-migration-runbook.md`「並列実行候補 family (2026-05-25
集計)」表で LZ78 は **Round 2 中規模 (26 件概算 / shared wall なし)**。
verbatim 再計数:

| 計数項目 | runbook 推定 | 実測 (2026-05-25 verbatim) | 検証コマンド |
|---|---:|---:|---|
| `@audit:suspect` total | 26 | **30** | `rg -c '@audit:suspect' InformationTheory/Shannon/LZ78*.lean InformationTheory/Shannon/LempelZiv78.lean` |
| `@audit:staged` total | 0 | **0** | `rg -c '@audit:staged' InformationTheory/Shannon/LZ78*.lean` |
| 散文 `🟢ʰ` | 0 | **1** | `rg -c '🟢ʰ' InformationTheory/Shannon/LZ78*.lean` (`LZ78ZivTreeNode.lean:631`) |
| `@audit:defect(*)` 残存 | (未集計) | **3** | `rg -nc '@audit:defect' InformationTheory/Shannon/LZ78*.lean` (`LZ78ZivTreeNode.lean:651/712` `degenerate` + `LZ78SMBSandwich.lean:298` `launder`) |
| `@audit:defer` / `@audit:closed-by-successor` | 0 | 0 | (該当なし) |
| 既存 word-boundary `sorry` (実 body) | 0 | **0** | `rg -nw 'sorry' InformationTheory/Shannon/LZ78*.lean InformationTheory/Shannon/LempelZiv78.lean` — 該当 0、Pilot Pattern D 計数 |

**ブリーフ計数との照合差分** (verbatim 確認義務、CLAUDE.md「具体的数値・型予測
の verbatim 確認」適用):

- ブリーフは `LempelZiv78.lean (3)` を 34 件中 3 件として記載していたが、実測
  `LempelZiv78.lean` の `@audit:suspect` は **0 件**。1-line 計数ミス。本 plan
  scope から `LempelZiv78.lean` を**除外**する (legacy tag が無いため touch 不要)。
- ブリーフ `LZ78ZivTreeNode.lean (4)` は実測 `suspect=3 + 🟢ʰ=1 = 4` (内訳一致)。
- 残り file 件数はブリーフ verbatim と一致 (5+5+5+4+4+2+2+1+1+1+1=31、🟢ʰ 1 件
  を含めて 31 件、または `defect` 共存を別計上すれば 31+3=34 件相当)。

実計数 = **31 declarations** (`@audit:suspect` 30 + 🟢ʰ 1 declaration、うち 3
declarations は既に `@audit:defect(*)` を併持)。

### legacy tag の plan-slug 分布

`@audit:suspect(<slug>)` の slug 別内訳 (verbatim 計数):

| slug | 件数 | 対応 docs |
|---|---:|---|
| `lz78-residual-discharge-plan` | **15** | [`lz78-residual-discharge-plan.md`](lz78-residual-discharge-plan.md) |
| `lz78-ziv-inequality-discharge-moonshot-plan` | **7** | [`lz78-ziv-inequality-discharge-moonshot-plan.md`](lz78-ziv-inequality-discharge-moonshot-plan.md) (うち 2 件は `@audit:defect(degenerate)` 併持) |
| `lz78-blockrv-refactor-plan` | **4** | [`lz78-blockrv-refactor-plan.md`](lz78-blockrv-refactor-plan.md) |
| `lz78-achievability-converse-plan` | **4** | [`lz78-achievability-converse-plan.md`](lz78-achievability-converse-plan.md) |

合計 30 件 (`@audit:suspect`)、🟢ʰ 1 件 (`LZ78ZivTreeNode.lean:631`)、defect 3 件
(うち 2 件は suspect と併持なので独立計数せず、`LZ78SMBSandwich.lean:298` の 1 件は
`launder`)。

### 上位 moonshot との関係

`lz78-moonshot-plan.md` (T4-A genuine Cover–Thomas Theorem 13.5.3 の type-check
done) と `lz78-completion-roadmap.md` は L-LZ1〜L-LZ5 (combinatorial core / SMB
sandwich / encoding-length boundedness / chain-rule pass-through / two-sided
sandwich) で **すべて hypothesis-form** publishing 済 (現状 closure 待ち)。
4 つの discharge plan (`-residual-discharge` / `-ziv-inequality-discharge` /
`-blockrv-refactor` / `-achievability-converse`) は各 wave の closure 担当。

本 plan は **これらの pass-through 設計を変えない**:
- load-bearing predicate (`IsLZ78AchievabilityChainHyp` / `IsLZ78ConverseChainHyp`
  / `IsLZ78AchievabilityZivUpperBound` / `IsLZ78ConverseCodingLowerBound` /
  `IsLZ78ZivCombinatorialCore` / `IsLZ78ZivCombinatorialCoreOverhead` (FALSE!) /
  `IsLZ78EncodingLengthLowerBound` / `IsLZ78ZivAsEventual`) を Phase 2 で削除し
  body sorry 化する。conclusion 型は変えない。
- regularity (`hreg : ∀ n ω m, m ≤ n → 0 < prefixBlockProb μ p ω m`、
  `IsLZ78PerPathParsingFactorization` (regularity-constructible)) は precondition
  なので残す。
- **proof completion** (Cover–Thomas Lemma 13.5.5 distinct-phrase combinatorial
  core の正しい a.s.-eventual 形 / Eq. 13.124 / 13.130 chain-rule の n-letter
  本実装 / Algoet-Cover sandwich) は別 workstream に残る。

### Honesty workflow と DoD

本 plan の DoD は CLAUDE.md「Definition of Done — 2 段階」の **type-check done**:
- 各 file `lake env lean InformationTheory/Shannon/LZ78<X>.lean` が 0 errors、
- 各新規 `sorry` に `@residual(<class>:<slug>)` タグ、
- 各 Phase 完了時に `honesty-auditor` を起動して classification + signature
  honesty を独立検証。

`@audit:ok` (proof done) は **本 plan の出力にしない**。

### ⚠ HONESTY ALERT / FALSE 検出 — Pattern H 適用必須

CLAUDE.md「検証の誠実性」inline policy + runbook Pattern H に従い、planner
段階で既存著者が明示済の HONESTY ALERT / FALSE predicate を集計
(`rg -n '⚠|HONESTY ALERT|FALSE' InformationTheory/Shannon/LZ78*.lean`):

| file:line | 配置 | 著者明示の文言 | 関連 declaration |
|---|---|---|---|
| `LZ78AsEventualAchievability.lean:17-411` | file 全体 (`§1 概要` + 各定理 docstring 16 hits) | "FALSE per-block combinatorial core" を `IsLZ78ZivAsEventual` (satisfiable a.s.-eventual hypothesis) で **置換する rewire layer** であることを明示 | §5 `lz78_two_sided_optimality_distinct_aseventual` (line 418、`@audit:suspect(lz78-achievability-converse-plan)`) — replacement headline、本 plan で sorry 化対象 |
| `LZ78ZivTreeNode.lean:364-693` | predicate 定義 docstring + theorem docstring (3 hits) | `IsLZ78ZivCombinatorialCoreOverhead` は **mathematically FALSE** (constant process 反例 `n=16, Pₙ=1, c=5`)、依存定理は **vacuously conditioned** | `def IsLZ78ZivCombinatorialCoreOverhead` (line 391、定義); `isLZ78AchievabilityZivUpperBound_distinctOverhead` (line 652、`@audit:defect(degenerate)` 併持); `lz78_two_sided_optimality_distinct_ziv_overhead_core_wired` (line 713、`@audit:defect(degenerate)` 併持) |
| `LZ78ZivTreeBridge.lean:16, 111` | docstring + 定理 (2 hits) | `not_isLZ78ZivCombinatorialCoreOverhead` — 上記 FALSE predicate の **genuine, sorryAx-free refutation** | `theorem not_isLZ78ZivCombinatorialCoreOverhead` (line 111、本 plan touch 対象外、proof done済の genuine refutation) |

**Pattern H 処理方針**:
- `LZ78AsEventualAchievability.lean` の 2 suspect (line 334 / 417) — **rewire**
  layer であり、HONESTY ALERT は既に著者 docstring に明示済。本 sweep は
  rewire の **wrapper 部分 (load-bearing predicate consumer)** を sorry 化
  する一般プロセスを通常通り適用 (rewire の意味論を壊さない、Phase 1.5 で
  通常の S+P 化)。
- `LZ78ZivTreeNode.lean:391` の **FALSE predicate `IsLZ78ZivCombinatorialCoreOverhead`
  自身は def なので sorry 化不可** + 既に `not_isLZ78ZivCombinatorialCoreOverhead`
  で refutation 済 + `LZ78AsEventualAchievability.lean` が後継 rewire を提供。
  本 sweep では当該 predicate definition には touch せず、依存 declaration
  (line 652 / 713) を Phase 2.0 で **`@residual(defect:false-hypothesis)` 付き
  sorry 化** する (defect kind 語彙拡張: `false-hypothesis` は audit-tags.md
  既存登録済)。同時に既存の `@audit:defect(degenerate)` 表記は本 plan で
  **`false-hypothesis` に rename** (`degenerate` は kind 語彙としては「退化定義
  悪用」を指すが、ここでの実態は「仮説が偽 = `false-hypothesis`」のため、より
  精確な kind に置換)。
- `LZ78ZivTreeBridge.lean:111` の refutation は **proof done 状態**で本 sweep
  touch 対象外。

未決事項 #2 に「`@audit:defect(degenerate)` → `(false-hypothesis)` 改名の auditor
verify」を escalate。

### Tier 5 defect — inline 検出済 (planner 段階)

`LZ78SMBSandwich.lean:299` `def IsSMBToLZ78ConverseChainBridge` は **literally
alias** (`:= IsLZ78ConverseChainHyp μ p lz78EncodingLength`)、既に
`@audit:defect(launder)` 付与済。name laundering の典型 (`Bridge` suffix だが
bridge ではない、predicate そのものの再 export)。本 plan の Phase 1.5 で
`@audit:defect(launder)` + `@audit:retract-candidate(name-laundering-alias)` を
明示 + alias を **使用している consumer (`lz78_converse_lower_bound_ergodic_of_bridge`
line 420) が unique** であることを確認、consumer 側で `IsLZ78ConverseChainHyp`
直接受領に書換 + alias 自身を `@audit:retract-candidate` 付与。

### Cross-family entanglement の有無

`rg -n '^import InformationTheory' InformationTheory/Shannon/LZ78*.lean InformationTheory/Shannon/LempelZiv78.lean`
verbatim 確認結果:

- LZ78 group の全 `import` は `InformationTheory.Shannon.*` 内部のみ (他 family
  namespace への直接 import なし)。
- `LZ78ConverseDischarge.lean` / `LZ78SMBSandwich.lean` / `LempelZiv78.lean`
  は `InformationTheory.Shannon.ShannonMcMillanBreiman` / `SMBAlgoetCover` /
  `SMBChainRule` を import。SMB は **Shannon-internal 汎用 infrastructure**
  (Chapter 16 の SMB は LZ78 / EPI / その他 ergodic theory 全般で共有)。
  これは **cross-family entanglement ではない** — brief 明示済 (handoff-epi
  の EPI Phase A SMB と独立な汎用 wall workstream)。
- `LZ78ConverseDischarge.lean:67` docstring に WynerZiv 言及あり → verbatim
  Read で「`itself adapted from WynerZivDischarge.lean (T3-D L-WZ3 partial).`」
  と確認、**散文 reference のみで `import` なし** (brief 明示の既知例)。
- `McMillanKraftBridge.lean` (line 38, 45, 177, 210, 218) / `StationaryKernel.lean`
  (line 11, 93, 108, 132, 241, 253, 261) は LZ78 predicate を参照するが、
  前者は **docstring 内散文のみ** (LZ78 converse は McMillan で discharge できない
  ことの説明) + 後者は **regularity → `IsLZ78PerPathParsingFactorization` の
  genuine 構成子** (LZ78 internal infrastructure、LZ78 family の一部とみなす)。
  どちらも cross-family ではない。

**cross-family entanglement 該当 = 0 件**。

## Approach

**file 単位 sweep を Phase 1 / 1.5 / 2.0 / 2.1 / 2.2 / 2.3 / 2.x / 2.4 / V に
分割**、共有 wall lemma は集約しない、FALSE predicate 由来の vacuously-conditioned
wrapper を `defect:false-hypothesis` で明示する。並列実行は **採用しない**
(legacy tag が `lz78-residual-discharge-plan` 等 4 つの slug に分散していて、各
file 内の依存 chain が密、逐次 sweep の方が drift 制御しやすい)。

### 戦略 (4 slug + Pattern H 統合 sweep)

```
Phase 0  inventory (本 plan 内 inline、verbatim 確認済)
   │
Phase 1  V/C cleanup ─ pure variational / constructive pass-through wrapper
   │      ├─ V: variational pass-through (sandwich `tendsto_of_le_liminf_of_limsup_le` 等)
   │      └─ C: in-tree constructive primitive 経由 (regularity → predicate 構成)
   │     (該当数は in-Phase で再検証、現時点予測: 0-2 件)
   │
Phase 1.5  S (= load-bearing predicate consumer) migration
   │      ├─ tag `@audit:suspect(<slug>)` → `@residual(plan:<slug>)` で body sorry 化
   │      ├─ signature 維持 (Phase 2 で predicate retract、本 phase は body のみ書換)
   │      └─ defect(launder) alias `IsSMBToLZ78ConverseChainBridge` の retract-candidate 化
   │
Phase 2.0  Pattern H — FALSE predicate-conditioned wrappers
   │      ├─ `LZ78ZivTreeNode.lean:652/713` (現 `@audit:defect(degenerate)` + suspect)
   │      ├─ defect kind rename: `degenerate` → `false-hypothesis` (audit-tags.md 既登録)
   │      └─ body sorry + `@residual(defect:false-hypothesis)`、signature 改変なし
   │
Phase 2.1  P retreat — `LZ78ConverseDischarge.lean` + `LZ78FinalGlue.lean` (10 件)
   │      ├─ predicate hypothesis 削除 (`IsLZ78ConverseChainHyp` / `IsLZ78AchievabilityChainHyp` 等)
   │      └─ body sorry + `@residual(plan:lz78-residual-discharge-plan)`
   │
Phase 2.2  P retreat — `LZ78SMBSandwich.lean` + `LZ78ConverseKraft.lean` (5 件)
   │      ├─ predicate / SMB-bridge hypothesis 削除
   │      └─ body sorry + `@residual(plan:lz78-residual-discharge-plan)`
   │
Phase 2.3  P retreat — `LZ78ZivCombinatorics.lean` + `LZ78ZivTreeNode.lean` 残 (8 件)
   │      ├─ Ziv combinatorial core / overhead core consumer
   │      └─ body sorry + `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)`
   │
Phase 2.x  ripple — caller drift handling (Pilot Pattern C 散文化)
   │
Phase 2.4  audit-2 (honesty-auditor)
   │
Phase V   verify + 集計 + banner 反映
```

### 戦略の選択軸

`docs/audit/sorry-migration-runbook.md`「並列実行プロトコル」+ pilot 3 件
(Hoeffding / Cramer / Wyner–Ziv) を踏まえた 2 軸決定:

1. **file 単位 sweep を採用** (incidental ではなく一括)。理由:
   - 30 件の suspect + 1 🟢ʰ + 3 defect(*) が 4 つの plan slug + 1 file の
     Pattern H に分散しているが、**file 間で chain dependency が密** — 例えば
     `lz78_two_sided_optimality_ergodic` (`LZ78FinalGlue.lean:215`) は
     `lz78_converse_lower_bound_with_chain` (`LZ78ConverseDischarge.lean:275`)
     + `lz78_achievability_upper_bound_ergodic` (`LZ78FinalGlue.lean:167`) +
     `algoet_cover_*` を呼ぶ。incidental だと中間 wrapper が drift する。
   - 30+1+3 件 = 中規模 (Wyner–Ziv 22 件、Hoeffding 19 件 と同等)。1-2 session
     で sweep 可能 (各 file 4 件以下が中央値、Pilot 同等規模)。

2. **共有 sorry 補題に集約しない**。理由:
   - `docs/audit/audit-tags.md`「Wall name register」表に LZ78 関連 wall
     (`lz78-ziv-inequality` / `lz78-combinatorial-core` / `lz78-aseventual` 等)
     は **未登録**。後続 Wall register 拡張提案 (R4) として下記「Wall name
     register 拡張提案」section で候補を 1 件 escalate するが、本 plan では
     plan-slug 形で 4 slug に揃える。
   - 30+3 件の closure 担当は 4 plan slug + Pattern H 1 件で identified、shared
     wall lemma の置き場所 (新規 `LZ78Walls.lean` 等) は不要。

### 移行レシピ (declaration 単位)

Pilot 3 family と同様、出現する subpattern を分類:

- **パターン V (variational pass-through)**: signature が `h_lower` / `h_upper`
  / `h_bdd_above` / `h_bdd_below` 等の sandwich precondition のみ取り、body は
  `tendsto_of_le_liminf_of_limsup_le` 一発、または `le_antisymm` 合成。
  - 移行: signature **変えない**、`@audit:suspect` タグだけ削除し `@residual` も
    付与しない (= regularity / variational pass-through hyp 扱い)。
  - LZ78 family での候補 (Phase 1 候補): `lz78_asymptotic_optimality_with_greedy_encoding`
    (`LZ78GreedyParsing.lean:519`) / `lz78_asymptotic_optimality_with_greedy_impl`
    (`LZ78GreedyParsingImpl.lean:423`) — variational sandwich pass-through に近い
    が、`IsLZ78AchievabilityChainHyp` / `IsLZ78ConverseChainHyp` が依然 hypothesis
    として残るため**「純 V」**ではない (P+V mix)、auditor 委任で再判定。

- **パターン C (constructive bridge)**: signature が in-tree primitive (例:
  `IsLZ78PerPathParsingFactorization`、これは `StationaryKernel.lean:257` の
  `isLZ78PerPathParsingFactorization_of_pos` で **constructive discharge 済**) を
  取る。
  - 移行: tag を `@audit:suspect` から **削除**するだけ。
  - LZ78 family では `IsLZ78PerPathParsingFactorization` を hypothesis に取る
    declaration が複数あるが、これらは Ziv combinatorial core hypothesis を
    **同時に**取るため C 単独パターンには該当しない (P+C mix)。Phase 1 候補
    なし、auditor 委任 (現時点予測: 0 件)。

- **パターン S (staged-equivalent = load-bearing predicate consumer)**: signature
  が load-bearing predicate hypothesis (`IsLZ78AchievabilityChainHyp` /
  `IsLZ78ConverseChainHyp` 等) を取り、body はそれを field destructure / chain
  composition で使う。
  - 移行: signature **維持** (predicate 削除は Phase 2.3 retract-candidate で
    判断、現 Phase は body のみ書換)、body を `sorry` に置換、`@audit:suspect(<slug>)`
    を `@residual(plan:<slug>)` に書換。
  - LZ78 family での該当: 30 件中 ~20-22 件 (Phase 1.5 で sweep)。

- **パターン P (suspect、predicate 削除 = signature 改変必要)**: 当該 family
  の固有事情で predicate 削除して body sorry 化する declaration。本 family で
  は Phase 1.5 (S) と Phase 2.1/2.2/2.3 (P) の区別は **load-bearing predicate を
  hypothesis に持ち、かつそれが本 plan で deprecate 候補かどうか**。

- **パターン H (false-hypothesis-conditioned)**: `IsLZ78ZivCombinatorialCoreOverhead`
  (mathematically FALSE) を hypothesis に取る 2 declarations。**defect kind
  `false-hypothesis`** で明示。

- **defect (existing)**: 既に `@audit:defect(*)` 付与済の 3 declarations。

詳細な per-declaration pattern 判定は次セクション「在庫」表で示す。

### constructive recovery 候補 (Pilot Pattern B)

Pilot Hoeffding で `isHoeffdingMinimizerFullSupport_of_lagrange` が
`IsHoeffdingMinimizerFullSupport (hoeffdingTilt P₁ P₂ lam) = ∀ a, 0 < hoeffdingTilt ...`
に reduce 可能で constructive 化した先例。LZ78 family で同パターン候補:

| file:line | decl 名 | 結論型 | 構成的回復可能性 |
|---|---|---|---|
| (なし、現時点予測) | — | — | implementer step で結論型を再確認、planner デフォルトは「30 件全 sorry 化」 |

→ Phase 1 候補なし (予測)、Phase 2 で implementer が inline detection (Pilot
Pattern B) を適用、不要 sorry を作らない。

### transitive sorry の handling 方針 (Pilot Pattern C)

LZ78 family は **chain dependency が密**:

```
LZ78FinalGlue (sorry: 5 件)
  ├─ ← LZ78ConverseDischarge (sorry: 5 件)
  │     └─ ← LZ78SMBSandwich (sorry: 4 件)
  ├─ ← LZ78AchievabilityLimsup (sorry: 2 件)
  │     └─ ← LZ78ZivCombinatorics (sorry: 5 件)
  │           └─ ← LZ78ZivTreeNode (sorry: 3 + 🟢ʰ 1 件)
  ├─ ← LempelZiv78.lz78_asymptotic_optimality (本 plan touch 対象外)
  └─ ← LZ78GreedyParsing / LZ78GreedyParsingImpl (sorry: 1+1 件)

LZ78AsEventualAchievability (sorry: 2 件)
  └─ ← LZ78ZivCombinatorics + LZ78ConverseKraft (sorry: 1 件)

LZ78DistinctEncoding (sorry: 1 件) ← LZ78GreedyParsing chain
```

各 wrapper を Phase 1.5 / 2.0 / 2.1 / 2.2 / 2.3 で個別に sorry 化するため transitive
性が発生。pilot Hoeffding / Cramer / WynerZiv と同様、**transitive sorry に
`@residual` を新規付与しない** — 各 declaration の自身の load-bearing hypothesis
削除に対して `@residual(plan:<slug>)` を 1 つ持ち、上流 sorry への依存は
docstring 散文で明示する。audit-tags.md vocabulary 未登録の `:transitive`
suffix 等は使わない。

## 在庫: 30 + 1 + 3 件の verbatim 分類

verbatim 確認方法: 各 `@audit:suspect | @audit:defect(*) | 🟢ʰ` 周辺 docstring
+ theorem signature + body 1-3 行を実コードから読込、「signature の hypothesis
が load-bearing か regularity か」「結論型が load-bearing predicate を返すか」
を 1 件ずつ判定。`path:line` はタグ行。declaration 名はその直後。

### `LZ78ConverseDischarge.lean` (5 件、全 `lz78-residual-discharge-plan`)

| file:line | decl 名 | suspect の核 (1 行 docstring) | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78ConverseDischarge.lean:198` | `lz78_converse_lower_bound_pmfBased` | `IsLZ78ConverseChainHyp` + SMB-lower-bound hypothesis → liminf 結論 (transitivity 1 行) | S (predicate consumer + SMB hyp consumer) | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 1.5 (S)。signature 維持、body sorry |
| `LZ78ConverseDischarge.lean:223` | `lz78_converse_lower_bound_of_pointwise` | `IsLZ78EncodingLengthLowerBound` + 4 regularity bdd/cobdd hyp + SMB-lower → liminf 結論 (`Filter.liminf_le_liminf` 経由) | S | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 1.5 (S)。`IsLZ78EncodingLengthLowerBound` consumer |
| `LZ78ConverseDischarge.lean:274` | `lz78_converse_lower_bound_with_chain` | `IsLZ78ConverseChainHyp` (ergodic-process specialized) + SMB-lower → liminf。**headline export** | S | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 1.5 (S)。pmfBased の wrapper、上流 sorry を継承 |
| `LZ78ConverseDischarge.lean:304` | `lz78_converse_lower_bound_discharge` | alias of `_with_chain` (line 275) — backwards-compatible call site | S (純 wrapper) | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 1.5 (S)、alias |
| `LZ78ConverseDischarge.lean:347` | `lz78_converse_lower_bound_greedy` | `_with_chain` を `lz78GreedyEncodingLength` で specialize | S (純 specialization wrapper) | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 1.5 (S) |

### `LZ78FinalGlue.lean` (5 件、全 `lz78-residual-discharge-plan`)

| file:line | decl 名 | suspect の核 | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78FinalGlue.lean:166` | `lz78_achievability_upper_bound_ergodic` | `IsLZ78AchievabilityChainHyp` + `algoet_cover_limsup_bound` (in-tree, discharged SMB) → limsup ≤ entropyRate | S | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 2.1 (S)。Ziv-side mirror of `lz78_converse_lower_bound_with_chain` |
| `LZ78FinalGlue.lean:214` | `lz78_two_sided_optimality_ergodic` | `IsLZ78AchievabilityChainHyp` + `IsLZ78ConverseChainHyp` + 2 boundedness hyp → Tendsto | S + V (bdd hyp は variational) | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 2.1 (S+V)。S19 headline、SMB internally discharged |
| `LZ78FinalGlue.lean:258` | `lz78_two_sided_optimality_ergodic_of_bounds` | 上の bundled `_of_bounds` form (2 bdd hyp が conjunction)、refine + split | S + V (純 wrapper) | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 2.1 (S+V) |
| `LZ78FinalGlue.lean:332` | `lz78_two_sided_optimality_greedy_impl` | 上の greedy-impl specialization、`IsLZ78AchievabilityChainHyp` + converse + 2 bdd hyp | S + V (純 specialization) | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 2.1 (S+V) |
| `LZ78FinalGlue.lean:384` | `lz78_two_sided_optimality_greedy_impl_bdd_below_free` | 上の `h_bdd_below` 内部 discharge 版 (`lz78GreedyImpl_isBoundedUnder_ge` 経由) | S + V | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 2.1 (S+V)。残り 3 honest input (`h_achiev` / `h_converse` / `h_bdd_above`) |

### `LZ78ZivCombinatorics.lean` (5 件、全 `lz78-ziv-inequality-discharge-moonshot-plan`)

| file:line | decl 名 | suspect の核 | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78ZivCombinatorics.lean:266` | `ziv_count_mul_log_le_neg_log_blockProb` | `IsLZ78ZivCombinatorialCore` + `IsLZ78PerPathParsingFactorization` (regularity-constructible) + `hPn > 0` 経由で nat-log Ziv inequality | S (`IsLZ78ZivCombinatorialCore` = load-bearing combinatorial core) | `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` | No | Phase 2.3 (S)。`hfac` は constructive (Phase B)、`hcore` が load-bearing |
| `LZ78ZivCombinatorics.lean:286` | `ziv_count_mul_logb_le_neg_logb_blockProb` | nat-log → base-2 logb への純算術変換 (div by `log 2 > 0`) | S (transitive via line 266) | `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` | No | Phase 2.3 (S transitive)、上流 sorry 継承 |
| `LZ78ZivCombinatorics.lean:411` | `lz78DistinctRate_le_blockLogAvg₂_add_slack` | per-block per-path Ziv upper bound、`IsLZ78ZivCombinatorialCore` + `IsLZ78PerPathParsingFactorization` + `hPn > 0` 経由 | S | `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` | No | Phase 2.3 (S) |
| `LZ78ZivCombinatorics.lean:625` | `isLZ78AchievabilityZivUpperBound_distinct` | `IsLZ78ZivCombinatorialCore` + regularity `hreg` → `IsLZ78AchievabilityZivUpperBound` (structure 構築) | S (predicate producer) | `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` | No | Phase 2.3 (S, producer-side)、Phase 2.3 で `IsLZ78ZivCombinatorialCore` retract-candidate 判定 |
| `LZ78ZivCombinatorics.lean:687` | `lz78_two_sided_optimality_distinct_ziv_core_wired` | `IsLZ78ZivCombinatorialCore` + `hreg` + `IsLZ78ConverseCodingLowerBound` → Tendsto headline | S | `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` | No | Phase 2.3 (S)。T4-A intermediate headline |

### `LZ78SMBSandwich.lean` (4 件、全 `lz78-residual-discharge-plan`)

| file:line | decl 名 | suspect の核 | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78SMBSandwich.lean:298` | `def IsSMBToLZ78ConverseChainBridge` | **既に `@audit:defect(launder)` 付与済**。`def := IsLZ78ConverseChainHyp ...` (literally alias、bridge ではない) | **defect(launder)** + S | `@residual(defect:launder)` 付き sorry **不可** (def なので) → `@audit:retract-candidate(name-laundering-alias)` + 既存 `@audit:defect(launder)` 維持 + 唯一 consumer (`lz78_converse_lower_bound_ergodic_of_bridge` line 420) を直接 `IsLZ78ConverseChainHyp` 受領に書換 | No | Phase 1.5 (defect-retract)。CLAUDE.md「sorry を書けない箇所での対処順序」(1) 第一選択 = 定義書換 (alias 廃止) を採用 |
| `LZ78SMBSandwich.lean:397` | `lz78_converse_lower_bound_ergodic` | `IsLZ78ConverseChainHyp` + SMB internally discharged → liminf 結論 (hypothesis-free SMB form) | S | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 2.2 (S) |
| `LZ78SMBSandwich.lean:419` | `lz78_converse_lower_bound_ergodic_of_bridge` | 上の `IsSMBToLZ78ConverseChainBridge` (defect-launder alias) を hypothesis に取る純 alias-rename wrapper | S + defect(launder transitive) | `@residual(plan:lz78-residual-discharge-plan)` + signature を `IsLZ78ConverseChainHyp` に書換 (alias 廃止) | No | Phase 1.5 (defect-retract incidental)。alias 廃止後は素の S |
| `LZ78SMBSandwich.lean:470` | `lz78_converse_lower_bound_ergodic_greedy` | `_ergodic` を `lz78GreedyEncodingLength` で specialize | S | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 2.2 (S)、純 specialization wrapper |

### `LZ78ZivTreeNode.lean` (3 + 🟢ʰ 1 = 4 件、全 `lz78-ziv-inequality-discharge-moonshot-plan`)

| file:line | decl 名 | suspect の核 | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78ZivTreeNode.lean:428` | `lz78DistinctRate_le_blockLogAvg₂_add_slackOverhead` | `IsLZ78ZivCombinatorialCoreOverhead` (= **mathematically FALSE**、後述 def) + `hPn > 0` → per-block per-path overhead-aware Ziv upper bound。**docstring に著者 `⚠ DEFECT` 明示済** | **Pattern H** (false-hypothesis-conditioned, vacuously conditioned) | `@residual(defect:false-hypothesis)` (defect kind を audit-tags.md 既登録の `false-hypothesis` に rename、現 `@audit:defect(degenerate)` 不在だが docstring に FALSE 明示) | No | Phase 2.0 (Pattern H)。文脈上 line 428 自体は `defect` tag 未付与だが、依存する `IsLZ78ZivCombinatorialCoreOverhead` が FALSE のため vacuously conditioned。本 plan で `@residual(defect:false-hypothesis)` を新規付与 |
| `LZ78ZivTreeNode.lean:651` | `isLZ78AchievabilityZivUpperBound_distinctOverhead` | 🟢ʰ load-bearing hypothesis + `IsLZ78ZivCombinatorialCoreOverhead` (FALSE) + `hreg` → `IsLZ78AchievabilityZivUpperBound` (predicate 構築)。**既に `@audit:defect(degenerate)` + `@audit:suspect(lz78-ziv-inequality-discharge-moonshot-plan)` 併持** + 直前 docstring の 🟢ʰ marker (`LZ78ZivTreeNode.lean:631`) | **Pattern H** + 既存 defect | `@residual(defect:false-hypothesis)` (defect kind rename: `degenerate` → `false-hypothesis`、より精確な kind) + 旧 `@audit:suspect` 削除 | No | Phase 2.0 (Pattern H)。著者 docstring `⚠ unsatisfiable` + `LZ78ZivTreeBridge.not_isLZ78ZivCombinatorialCoreOverhead` で genuine refutation 済 |
| `LZ78ZivTreeNode.lean:712` | `lz78_two_sided_optimality_distinct_ziv_overhead_core_wired` | T4-A overhead-aware headline、`IsLZ78ZivCombinatorialCoreOverhead` (FALSE) + `hreg` + `IsLZ78ConverseCodingLowerBound` → Tendsto。**既に `@audit:defect(degenerate)` + suspect 併持** | **Pattern H** + 既存 defect | 同上 `@residual(defect:false-hypothesis)` + 旧 suspect 削除 | No | Phase 2.0 (Pattern H) |

注: 🟢ʰ 1 件 (line 631) は **直前 line の docstring 内 prose marker** で declaration
自身ではない (line 652 `isLZ78AchievabilityZivUpperBound_distinctOverhead` の
docstring 内)。Phase 2.0 で declaration を `defect:false-hypothesis` 化する際に
docstring 内 🟢ʰ prose を削除 (deprecated vocabulary、`audit-tags.md` の Deprecated
表 + migration recipe)。

### `LempelZiv78.lean` (0 件、本 plan scope 外)

ブリーフは LempelZiv78.lean に 3 件記載していたが verbatim 確認で 0 件 (`rg -c '@audit:suspect' InformationTheory/Shannon/LempelZiv78.lean` = 0)。本 plan touch 対象外。

### `LZ78AchievabilityLimsup.lean` (2 件、全 `lz78-achievability-converse-plan`)

| file:line | decl 名 | suspect の核 | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78AchievabilityLimsup.lean:154` | `lz78_achievability_limsup_le₂` | `IsLZ78AchievabilityZivUpperBound` + cobdd regularity + `shannon_mcmillan_breiman₂` (in-tree) → limsup ≤ entropyRate₂。"only non-genuine input is load-bearing `IsLZ78AchievabilityZivUpperBound`" 明示 | S | `@residual(plan:lz78-achievability-converse-plan)` | No | Phase 1.5 (S) |
| `LZ78AchievabilityLimsup.lean:236` | `lz78_two_sided_optimality_distinct_genuine` | T4-A base-2 distinct headline、`IsLZ78AchievabilityZivUpperBound` + `IsLZ78ConverseCodingLowerBound` → Tendsto。"two remaining inputs are load-bearing" 明示 | S | `@residual(plan:lz78-achievability-converse-plan)` | No | Phase 1.5 (S) |

### `LZ78AsEventualAchievability.lean` (2 件、全 `lz78-achievability-converse-plan`)

| file:line | decl 名 | suspect の核 | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78AsEventualAchievability.lean:334` | `lz78_achievability_limsup_le₂_aseventual` | `IsLZ78ZivAsEventual` (**satisfiable** a.s.-eventual replacement of FALSE `IsLZ78ZivCombinatorialCore`) + cobdd regularity → limsup ≤ entropyRate₂ | S (load-bearing predicate consumer、ただし predicate is satisfiable) | `@residual(plan:lz78-achievability-converse-plan)` | No | Phase 1.5 (S)。HONESTY ALERT layer の rewire wrapper、predicate satisfiable (Pattern H 適用外、通常 S 処理) |
| `LZ78AsEventualAchievability.lean:417` | `lz78_two_sided_optimality_distinct_aseventual` | T4-A headline rewire、`IsLZ78ZivAsEventual` + `IsLZ78ConverseCodingLowerBound` → Tendsto。"genuine honesty improvement (no longer vacuously conditioned)" 明示 | S | `@residual(plan:lz78-achievability-converse-plan)` | No | Phase 1.5 (S) |

### `LZ78ConverseKraft.lean` (1 件、`lz78-residual-discharge-plan`)

| file:line | decl 名 | suspect の核 | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78ConverseKraft.lean:170` | `lz78_converse_le_liminf₂` | `IsLZ78ConverseCodingLowerBound` + cobdd regularity + `shannon_mcmillan_breiman₂` → entropyRate₂ ≤ liminf。"only non-genuine input is load-bearing `IsLZ78ConverseCodingLowerBound`" 明示 | S | `@residual(plan:lz78-residual-discharge-plan)` | No | Phase 2.2 (S) — `LZ78ConverseKraft.lean` は `LZ78ConverseDischarge.lean` を import するため Phase 2.2 へ |

### `LZ78DistinctEncoding.lean` (1 件、`lz78-blockrv-refactor-plan`)

| file:line | decl 名 | suspect の核 | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78DistinctEncoding.lean:413` | `lz78_two_sided_optimality_distinct_bdd_free` | T4-A headline for distinct code、`IsLZ78AchievabilityChainHyp` + `IsLZ78ConverseChainHyp` + 2 boundedness internally discharged → Tendsto | S | `@residual(plan:lz78-blockrv-refactor-plan)` | No | Phase 1.5 (S) — Distinct encoding chain |

### `LZ78GreedyParsing.lean` (1 件、`lz78-blockrv-refactor-plan`)

| file:line | decl 名 | suspect の核 | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78GreedyParsing.lean:518` | `lz78_asymptotic_optimality_with_greedy_encoding` | concrete `lz78GreedyEncodingLength` + 4 genuine sandwich ingredients (lower / upper / 2 bdd) → Tendsto。"genuine application, not an identity wrap" 明示 | V + S (4 sandwich hyp は variational pass-through、ただし上流 sorry chain あり) | `@residual(plan:lz78-blockrv-refactor-plan)` | No | Phase 1.5 (V+S 境界)、auditor 委任 (Pilot Hoeffding variational wrapper と同等の境界判定対象) |

### `LZ78GreedyParsingImpl.lean` (1 件、`lz78-blockrv-refactor-plan`)

| file:line | decl 名 | suspect の核 | パターン | 移行後 class:slug | cross-family? | 備考 |
|---|---|---|---|---|---|---|
| `LZ78GreedyParsingImpl.lean:422` | `lz78_asymptotic_optimality_with_greedy_impl` | greedy-impl specialization、4 genuine sandwich ingredients + `lz78_asymptotic_optimality` 呼出 | V + S | `@residual(plan:lz78-blockrv-refactor-plan)` | No | Phase 1.5 (V+S 境界)、auditor 委任 |

### 集計 (パターン別)

- **V** (純 variational pass-through、タグ削除のみ): **0 件** (現時点予測、auditor 確認で 0-2 件)
- **C** (in-tree constructive primitive 経由、タグ削除のみ): **0 件** (現時点予測)
- **S** (load-bearing predicate consumer、body sorry + `@residual(plan:...)`): **22 件** (Phase 1.5)
- **S (chain dependent, transitive)**: **5 件** (Phase 2.1 / 2.2 / 2.3 で chain 上流 sorry を継承)
- **Pattern H** (FALSE predicate-conditioned、`@residual(defect:false-hypothesis)`): **3 件** (Phase 2.0)
- **defect(launder)** alias (sorry 不可、def 廃止 + retract-candidate): **1 件** (`IsSMBToLZ78ConverseChainBridge` Phase 1.5)
- **境界判定** (V+S mix、auditor 委任): **2 件** (`lz78_asymptotic_optimality_with_greedy_encoding` / `lz78_asymptotic_optimality_with_greedy_impl`)

総計 30 (suspect) + 1 (🟢ʰ-as-prose-of-line-652) + 3 (`@audit:defect(*)` 併持
2 件 + alias 1 件) = 30 + 3 distinct 件 (🟢ʰ は line 652 の docstring 内 prose
なので独立計数せず)。

## Phase 詳細

### Phase 0 — Inventory (本 plan 内 inline、完了) 📋 ✅

- [x] 各 30 件 (`@audit:suspect`) + 1 🟢ʰ (prose-of-line-652) + 3 `@audit:defect(*)`
  併持 declarations を verbatim 確認 (`rg -c` + 該当 docstring + signature 1-3
  行を実コード Read)
- [x] パターン分類 (V / C / S / P / H + defect 細分)
- [x] cross-family 依存 確認 (`rg '^import InformationTheory' InformationTheory/Shannon/LZ78*.lean InformationTheory/Shannon/LempelZiv78.lean`) → **0 件、`LZ78ConverseDischarge.lean:67` は散文 reference のみで非 entanglement**
- [x] 既存 sorry word-boundary 計数 `0` 件確定 (Pilot Pattern D 適用済)
- [x] ⚠ HONESTY ALERT / FALSE 検出 (`rg -n '⚠|HONESTY ALERT|FALSE'`) →
  **`LZ78AsEventualAchievability.lean` (rewire layer、scope 内通常処理) +
  `LZ78ZivTreeNode.lean` (Pattern H 適用、3 件) +
  `LZ78ZivTreeBridge.lean` (genuine refutation、touch 対象外)**

**proof-log**: no (mechanical 在庫確認)。

### Phase 1 — V/C cleanup (低 risk、新規 sorry なし) 📋

- [ ] **1.1** 現時点予測で V/C 該当ゼロ。Phase 1 は実質 skip 可。
  judging logged: Cramer pilot と同形 (Phase 1 候補ゼロ → skip)。
- [ ] **1.2** ただし implementer は Phase 1.5 に進む前に **inline detection
  (Pilot Pattern B)** で `lz78_asymptotic_optimality_with_greedy_encoding`
  (line 519) / `lz78_asymptotic_optimality_with_greedy_impl` (line 423) の
  結論型 + body 再確認、constructive recovery 可能性 (= 4 sandwich ingredient
  すべて in-tree / in-file で discharge できるか) を判定。可能なら Phase 1
  V 扱い (タグ削除のみ)。

**Phase 1 DoD**: V/C 0-2 件、新規 `sorry` 0 件、`lake env lean` 0 errors。
件数次第で Phase 1.5 件数が `22 → 20` 等に変動。

**proof-log**: no (skip 同等、結果のみ判断ログに append)。

### Phase 1.5 — S+defect(launder) migration (22 件 body sorry + 1 alias 廃止) 📋

ファイル ASC 順:

- [ ] **1.5.1** `LZ78AchievabilityLimsup.lean` 2 件 (line 154 / 236) 書換:
  - `@audit:suspect(lz78-achievability-converse-plan)` → `@residual(plan:lz78-achievability-converse-plan)`、body を `sorry` に置換。
  - signature **改変しない** (`IsLZ78AchievabilityZivUpperBound` / `IsLZ78ConverseCodingLowerBound` 等の predicate hypothesis 維持)。
  - `lake env lean InformationTheory/Shannon/LZ78AchievabilityLimsup.lean` で 0 errors 確認。

- [ ] **1.5.2** `LZ78AsEventualAchievability.lean` 2 件 (line 334 / 417) 書換:
  - 同上 (slug `lz78-achievability-converse-plan`)、signature 維持。
  - rewire layer なので **HONESTY ALERT を維持** (docstring 内 FALSE-core
    discussion はそのまま、`@audit:suspect` のみ書換)。

- [ ] **1.5.3** `LZ78DistinctEncoding.lean` 1 件 (line 413) 書換:
  - `@audit:suspect(lz78-blockrv-refactor-plan)` → `@residual(plan:lz78-blockrv-refactor-plan)`、body sorry、signature 維持。

- [ ] **1.5.4** `LZ78GreedyParsing.lean` 1 件 (line 518) 書換:
  - 同上 slug、signature 維持。V+S 境界判定対象。
  - Pilot Pattern B (constructive recovery) inline 適用、不要 sorry なら Phase 1 V に降格。

- [ ] **1.5.5** `LZ78GreedyParsingImpl.lean` 1 件 (line 422) 書換:
  - 同上、V+S 境界判定対象。

- [ ] **1.5.6** `LZ78SMBSandwich.lean` の `IsSMBToLZ78ConverseChainBridge` (line 299) defect(launder) alias の処理 (CLAUDE.md「sorry を書けない箇所での対処順序」第一選択 = 定義書換):
  - **alias 廃止**: `def IsSMBToLZ78ConverseChainBridge := IsLZ78ConverseChainHyp` の 1-line alias を削除する代わりに **`@audit:retract-candidate(name-laundering-alias)`** を docstring 末尾に付与 + `@simp lemma isSMBToLZ78ConverseChainBridge_def` (line 304) は同時 retract-candidate 化 (どちらも load-bearing でなく後方互換の alias)。
  - **唯一 consumer `lz78_converse_lower_bound_ergodic_of_bridge` (line 420) を `IsLZ78ConverseChainHyp` 直接受領に書換** + signature を `(h_chain : IsLZ78ConverseChainHyp ...)` に修正 (alias 経由廃止) + body は `lz78_converse_lower_bound_ergodic μ p lz78EncodingLength h_chain` (引数名 rename のみ)、その後 line 420 を Phase 2.2 で通常 S sorry 化対象に含める。
  - **alias 自身は file から削除しない** (history record として `@audit:retract-candidate` 付き残置 + docstring に「Phase 1.5 で sorry-based migration により consumer 全削除済、API 後方互換のため alias 残置」と明記)。

- [ ] **1.5.7** Phase 1.5 完了時 各 file で `lake env lean` 確認 + 集計:
  ```bash
  rg -c '@audit:suspect' InformationTheory/Shannon/LZ78AchievabilityLimsup.lean \
                         InformationTheory/Shannon/LZ78AsEventualAchievability.lean \
                         InformationTheory/Shannon/LZ78DistinctEncoding.lean \
                         InformationTheory/Shannon/LZ78GreedyParsing.lean \
                         InformationTheory/Shannon/LZ78GreedyParsingImpl.lean \
                         InformationTheory/Shannon/LZ78SMBSandwich.lean   # = 6 file の合計が次 phase 件数まで段階 0 可能
  rg -c '@residual\(plan:lz78-achievability-converse-plan\)' InformationTheory/Shannon/LZ78*.lean
  rg -c '@residual\(plan:lz78-blockrv-refactor-plan\)' InformationTheory/Shannon/LZ78*.lean
  rg -c '@audit:retract-candidate' InformationTheory/Shannon/LZ78SMBSandwich.lean   # ≥ 2 (alias + @simp lemma)
  ```

**Phase 1.5 DoD**:
- 上記 6 file で `@audit:suspect` 0 件、対応 `@residual(plan:...)` 付き sorry 6 件
  (V 降格があれば数件少なめ)、
- `LZ78SMBSandwich.lean` の alias `IsSMBToLZ78ConverseChainBridge` に
  `@audit:retract-candidate(name-laundering-alias)` 付与済、
- 各 file `lake env lean` 0 errors。

**proof-log**: yes (`docs/proof-logs/proof-log-lz78-sorry-migration-phase-1.5.md`)。
理由: alias 廃止 + 境界判定 (greedy V+S) の判断記録 + Pattern H 隣接 file の
HONESTY ALERT 維持判断。

### Phase 1.6 — audit-1 (Phase 1 + 1.5 全件) 📋

- [ ] **1.6.1** orchestrator は `honesty-auditor` (または `general-purpose` + brief)
  を起動。対象:
  - Phase 1: 0-2 件 (V 降格があれば validation)
  - Phase 1.5: 6 declarations の `@residual` classification 正しさ + signature honesty
  - `LZ78SMBSandwich.lean` の alias retract-candidate 正しさ + name-laundering-alias kind 妥当性
- [ ] **1.6.2** verdict 受領 (`ok` / `questionable` / `defect`):
  - `ok` → Phase 2.0 着手
  - `questionable` → docstring refine、Phase 2 進行
  - `defect` → 当該 declaration を撤回 / 修正、Phase 2 進行前に解決

**proof-log**: yes (auditor verdict 記録)。

### Phase 2.0 — Pattern H (FALSE-conditioned wrapper、defect kind rename + sorry 化) 📋

- [ ] **2.0.1** `LZ78ZivTreeNode.lean:428` `lz78DistinctRate_le_blockLogAvg₂_add_slackOverhead`:
  - signature 改変: `(hcore : IsLZ78ZivCombinatorialCoreOverhead μ p)` を **削除**。
    残す: `(μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) (hn : 2 ≤ n) (ω : Ω) (hPn : 0 < (μ.map (p.blockRV n)).real {p.blockRV n ω})` (precondition + regularity)。
  - body: `sorry` + docstring 末尾に **`@residual(defect:false-hypothesis)`** 新規付与
    (旧 `@audit:suspect(lz78-ziv-inequality-discharge-moonshot-plan)` 削除)。
  - docstring 散文: 「Phase 2.0 retreat — old hypothesis `IsLZ78ZivCombinatorialCoreOverhead` is mathematically FALSE (refuted by `LZ78ZivTreeBridge.not_isLZ78ZivCombinatorialCoreOverhead`). Body retreated to `sorry` because the genuine a.s.-eventual replacement is provided by `LZ78AsEventualAchievability.lean` (track: `lz78-achievability-converse-plan`).」と明示。

- [ ] **2.0.2** `LZ78ZivTreeNode.lean:651` `isLZ78AchievabilityZivUpperBound_distinctOverhead`:
  - signature 改変: `(hcore_lbh : IsLZ78ZivCombinatorialCoreOverhead μ p)` を **削除**。残す: `(μ : Measure Ω) (p : StationaryProcess μ α) (hreg : ∀ n ω m, m ≤ n → 0 < prefixBlockProb μ p ω m)` (regularity)。
  - body: `sorry` + docstring 末尾を **`@residual(defect:false-hypothesis)`** に置換 (旧 `@audit:defect(degenerate)` + `@audit:suspect` 両削除、defect kind を `degenerate` → `false-hypothesis` に rename)。
  - **🟢ʰ marker (line 631 docstring 内 prose) を削除** (deprecated vocabulary、audit-tags.md「Deprecated」表で migration recipe 既登録、本 plan は incidental migration として処理)。
  - docstring 散文: 「Phase 2.0 retreat + defect kind rename `degenerate` → `false-hypothesis` (more precise: the hypothesis is mathematically false, not merely a degenerate-definition exploit). Witness: `LZ78ZivTreeBridge.not_isLZ78ZivCombinatorialCoreOverhead`. Successor (a.s.-eventual reformulation): `LZ78AsEventualAchievability.lean`.」

- [ ] **2.0.3** `LZ78ZivTreeNode.lean:712` `lz78_two_sided_optimality_distinct_ziv_overhead_core_wired`:
  - signature 改変: `(hcore : IsLZ78ZivCombinatorialCoreOverhead p.toStationaryProcess)` を **削除**。残す: regularity `hreg` + `(h_lb : IsLZ78ConverseCodingLowerBound ...)` + `(slackLow : ℕ → ℝ)` (`h_lb` は別 plan の load-bearing predicate consumer なので残し、後段 Phase 2.3 で当該 predicate の retract 判断時に再評価)。
  - body: `sorry` + `@residual(defect:false-hypothesis)` (旧 defect + suspect 両削除、kind rename)。
  - docstring 散文: 同上 + 「`h_lb` is preserved (separate `lz78-residual-discharge-plan` workstream, distinct false-hypothesis defect)」。

- [ ] **2.0.4** **`def IsLZ78ZivCombinatorialCoreOverhead` (line 391) 自身は touch しない** (def なので sorry 不可、CLAUDE.md「sorry を書けない箇所での対処順序」第二選択 → 暫定で defect 形のまま残置)。docstring に既に著者 ⚠ DEFECT 明示済 + `LZ78ZivTreeBridge.not_isLZ78ZivCombinatorialCoreOverhead` で genuine refutation 済。本 plan で **`@audit:retract-candidate(false-hypothesis)`** を新規付与 + `@audit:closed-by-successor(lz78-aseventual-achievability-plan)` で後継 plan slug を明示 (該当 docs file 存在確認済、`docs/shannon/lz78-aseventual-achievability-plan.md`)。

- [ ] **2.0.5** Phase 2.0 完了時 `lake env lean InformationTheory/Shannon/LZ78ZivTreeNode.lean` 確認 + olean refresh (`lake build InformationTheory.Shannon.LZ78ZivTreeNode`) + dependent file (`LZ78ZivTreeBridge.lean` / `LZ78AsEventualAchievability.lean` / `LZ78ZivCombinatorics.lean`) 再 verify (Pilot Pattern A)。

**Phase 2.0 DoD**:
- 3 declarations で `@audit:defect(degenerate)` 0 件、`@audit:suspect(lz78-ziv-inequality-discharge-moonshot-plan)` 0 件 (該当 3 件のみ)、`@residual(defect:false-hypothesis)` 3 件、新規 sorry 3 件、
- `IsLZ78ZivCombinatorialCoreOverhead` def に `@audit:retract-candidate(false-hypothesis)` + `@audit:closed-by-successor(lz78-aseventual-achievability-plan)` 付与済、
- 🟢ʰ marker (line 631) 削除済、
- `lake env lean InformationTheory/Shannon/LZ78ZivTreeNode.lean` 0 errors。

**proof-log**: yes (`docs/proof-logs/proof-log-lz78-sorry-migration-phase-2.0.md`)。理由: defect kind rename + Pattern H 適用判断 + def-level vs theorem-level 撤退の使い分け。

### Phase 2.1 — P retreat (`LZ78ConverseDischarge.lean` + `LZ78FinalGlue.lean`、10 件) 📋

順序: 上流 `LZ78ConverseDischarge.lean` を先に sweep、続いて caller の `LZ78FinalGlue.lean`。

#### Phase 2.1.A — `LZ78ConverseDischarge.lean` 5 件

- [ ] **2.1.A.1** `lz78_converse_lower_bound_pmfBased` (line 199):
  - signature から `(h_chain : IsLZ78ConverseChainHyp ...)` + `(h_smb_lower : ∀ᵐ ω ∂μ, entropyRate μ p ≤ liminf ...)` 2 仮説を **削除**。
  - 残す: `(μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)` (paramter のみ)。
  - body: `filter_upwards [h_chain, h_smb_lower] with ...` → `:= by sorry`。
  - 旧 `@audit:suspect(lz78-residual-discharge-plan)` → `@residual(plan:lz78-residual-discharge-plan)` (docstring 末尾)。

- [ ] **2.1.A.2** `lz78_converse_lower_bound_of_pointwise` (line 224):
  - signature から `(h_lower : IsLZ78EncodingLengthLowerBound ...)` + 4 regularity bdd/cobdd hyp + `(h_smb_f_lower : ...)` を **削除**。
  - 残す: paramter + `f : Ω → ℕ → ℝ` (precondition、本来 bdd hyp の意味論的根拠を残す)。
  - body: `sorry` + `@residual(plan:lz78-residual-discharge-plan)`。

- [ ] **2.1.A.3** `lz78_converse_lower_bound_with_chain` (line 275):
  - signature から `(h_chain : IsLZ78ConverseChainHyp ...)` + `(h_smb_lower : ...)` を **削除**。
  - body: `lz78_converse_lower_bound_pmfBased μ p.toStationaryProcess lz78EncodingLength h_chain h_smb_lower` → `:= by sorry`。
  - 旧 tag → `@residual(plan:lz78-residual-discharge-plan)`。

- [ ] **2.1.A.4** `lz78_converse_lower_bound_discharge` (line 305):
  - 同上 (alias of `_with_chain`)、signature 改変 + body sorry + tag 書換。

- [ ] **2.1.A.5** `lz78_converse_lower_bound_greedy` (line 348):
  - 同上 (specialization to `lz78GreedyEncodingLength`)、signature 改変 + body sorry。

- [ ] **2.1.A.6** `lake build InformationTheory.Shannon.LZ78ConverseDischarge` で olean refresh、`lake env lean InformationTheory/Shannon/LZ78ConverseDischarge.lean` 0 errors 確認。
- [ ] **2.1.A.7** dependent file (`LZ78FinalGlue.lean` / `LZ78SMBSandwich.lean` / `LZ78ConverseKraft.lean` 等) の type drift を `rg -l 'lz78_converse_lower_bound_(pmfBased|of_pointwise|with_chain|discharge|greedy)' InformationTheory/Shannon/` で列挙 + 個別 `lake env lean` 再 verify (Pilot Pattern A)。

#### Phase 2.1.B — `LZ78FinalGlue.lean` 5 件

- [ ] **2.1.B.1** `lz78_achievability_upper_bound_ergodic` (line 167):
  - signature から `(h_chain : IsLZ78AchievabilityChainHyp ...)` を **削除**。
  - body: `:= by sorry` + `@residual(plan:lz78-residual-discharge-plan)`。

- [ ] **2.1.B.2** `lz78_two_sided_optimality_ergodic` (line 215):
  - signature から `(h_achiev : IsLZ78AchievabilityChainHyp ...)` + `(h_converse : IsLZ78ConverseChainHyp ...)` を **削除**。残す: 2 boundedness hyp (variational pass-through、Sandwich Tendsto に必要 regularity)。
  - body: `lz78_converse_lower_bound_with_chain ...` + `lz78_achievability_upper_bound_ergodic ...` + `tendsto_of_le_liminf_of_limsup_le ...` → `:= by sorry`。
  - `@residual(plan:lz78-residual-discharge-plan)`。

- [ ] **2.1.B.3** `lz78_two_sided_optimality_ergodic_of_bounds` (line 259):
  - 同上 (bundled bounded form)、signature 改変 + body sorry。

- [ ] **2.1.B.4** `lz78_two_sided_optimality_greedy_impl` (line 333):
  - 同上 (greedy specialization)、signature 改変 + body sorry。

- [ ] **2.1.B.5** `lz78_two_sided_optimality_greedy_impl_bdd_below_free` (line 385):
  - 同上 (`h_bdd_below` internally discharged 版)、signature 改変 + body sorry。
  - `lz78GreedyImpl_isBoundedUnder_ge` (line 308、suspect なし) は touch しない (構成的、in-tree primitive)。

- [ ] **2.1.B.6** `lake build InformationTheory.Shannon.LZ78FinalGlue` で olean refresh、`lake env lean InformationTheory/Shannon/LZ78FinalGlue.lean` 0 errors 確認。
- [ ] **2.1.B.7** dependent file (`LZ78GreedyParsing.lean` / `LZ78GreedyParsingImpl.lean` / `LZ78ConverseKraft.lean`) 再 verify (Pilot Pattern A)。

**Phase 2.1 DoD**:
- 上記 2 file で `@audit:suspect` 0 件、`@residual(plan:lz78-residual-discharge-plan)` 10 件、新規 sorry 10 件、
- `lake env lean` 各 file 0 errors。

**proof-log**: yes。理由: signature 改変 10 件 + dependent caller drift 範囲記録。

### Phase 2.2 — P retreat (`LZ78SMBSandwich.lean` + `LZ78ConverseKraft.lean`、5 件) 📋

- [ ] **2.2.1** `LZ78SMBSandwich.lean:397` `lz78_converse_lower_bound_ergodic`:
  - signature から `(h_chain : IsLZ78ConverseChainHyp ...)` を **削除**。
  - body: `lz78_converse_lower_bound_with_chain ...` + `lz78_smb_sandwich_ergodic_liminf ...` → `:= by sorry` + `@residual(plan:lz78-residual-discharge-plan)`。

- [ ] **2.2.2** `LZ78SMBSandwich.lean:420` `lz78_converse_lower_bound_ergodic_of_bridge` (Phase 1.5.6 で alias 廃止後の素 S):
  - Phase 1.5.6 で `IsSMBToLZ78ConverseChainBridge` 直接受領 → `IsLZ78ConverseChainHyp` 直接受領に書換済。
  - signature から `(h_chain : IsLZ78ConverseChainHyp ...)` を **削除**、body sorry + `@residual(plan:lz78-residual-discharge-plan)`。
  - alias 自身 (line 299) は Phase 1.5.6 で retract-candidate 化済、本 Phase で再変更なし。

- [ ] **2.2.3** `LZ78SMBSandwich.lean:471` `lz78_converse_lower_bound_ergodic_greedy`:
  - 同上 (greedy specialization)、signature 改変 + body sorry。

- [ ] **2.2.4** `LZ78ConverseKraft.lean:171` `lz78_converse_le_liminf₂`:
  - signature から `(h_lb : IsLZ78ConverseCodingLowerBound ...)` を **削除**。残す: cobdd regularity hyp。
  - body: `filter_upwards [h_lb.lower, shannon_mcmillan_breiman₂ μ p, h_lz_cobdd]` → `:= by sorry` + `@residual(plan:lz78-residual-discharge-plan)`。

- [ ] **2.2.5** `lake build InformationTheory.Shannon.LZ78SMBSandwich` + `lake build InformationTheory.Shannon.LZ78ConverseKraft` で olean refresh、`lake env lean` 0 errors 確認 + dependent (`LZ78AchievabilityLimsup.lean` 等) 再 verify。

**Phase 2.2 DoD**:
- 2 file で `@audit:suspect` 0 件、`@residual(plan:lz78-residual-discharge-plan)` 4 件、新規 sorry 4 件、
- `LZ78SMBSandwich.lean` の alias retract-candidate 維持済、
- 各 file `lake env lean` 0 errors。

**proof-log**: no (mechanical sorry 化、Phase 2.1 と同形)。

### Phase 2.3 — P retreat (`LZ78ZivCombinatorics.lean`、5 件) 📋

- [ ] **2.3.1** `ziv_count_mul_log_le_neg_log_blockProb` (line 267):
  - signature から `(hcore : IsLZ78ZivCombinatorialCore μ p)` + `(hfac : IsLZ78PerPathParsingFactorization μ p)` を **削除**。残す: `(n : ℕ) (ω : Ω) (hPn : 0 < ...)` (precondition + regularity)。
  - body: `(hcore n ω).trans (blockProb_neg_log_ge_sum μ p hfac n ω hPn)` → `:= by sorry` + `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)`。

- [ ] **2.3.2** `ziv_count_mul_logb_le_neg_logb_blockProb` (line 287):
  - 同上 (base-2 logb 変換)、signature 改変 + body sorry + `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)`。

- [ ] **2.3.3** `lz78DistinctRate_le_blockLogAvg₂_add_slack` (line 412):
  - signature から `(hcore : IsLZ78ZivCombinatorialCore μ p)` + `(hfac : IsLZ78PerPathParsingFactorization μ p)` を **削除**。残す: `(n : ℕ) (hn : 2 ≤ n) (ω : Ω) (hPn : 0 < ...)`。
  - body: `sorry` + `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)`。

- [ ] **2.3.4** `isLZ78AchievabilityZivUpperBound_distinct` (line 626):
  - signature から `(hcore : IsLZ78ZivCombinatorialCore μ p)` を **削除**。残す: `(hreg : ∀ n ω m, m ≤ n → 0 < prefixBlockProb μ p ω m)` (regularity)。
  - 結論型は `IsLZ78AchievabilityZivUpperBound μ p (@lz78DistinctEncodingLength α _ _ _) (lz78AchievSlack (α := α))` (structure 構築) を維持。
  - body: `refine ⟨?_, lz78AchievSlack_tendsto_zero⟩; ...` → `:= by sorry` + `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)`。

- [ ] **2.3.5** `lz78_two_sided_optimality_distinct_ziv_core_wired` (line 688):
  - signature から `(hcore : IsLZ78ZivCombinatorialCore p.toStationaryProcess)` を **削除**。残す: `(slackLow : ℕ → ℝ)` + `hreg` + `(h_lb : IsLZ78ConverseCodingLowerBound ...)` (`h_lb` は別 plan の load-bearing、本 Phase 対象外)。
  - body: `lz78_two_sided_optimality_distinct_genuine μ p (lz78AchievSlack (α := α)) slackLow (isLZ78AchievabilityZivUpperBound_distinct μ p.toStationaryProcess hcore hreg) h_lb` → `:= by sorry` + `@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)`。

- [ ] **2.3.6** `lake build InformationTheory.Shannon.LZ78ZivCombinatorics` で olean refresh、`lake env lean InformationTheory/Shannon/LZ78ZivCombinatorics.lean` 0 errors 確認 + dependent (`LZ78ZivTreeNode.lean` / `LZ78AchievabilityLimsup.lean` 等) 再 verify。

**Phase 2.3 DoD**:
- `LZ78ZivCombinatorics.lean` で `@audit:suspect` 0 件、`@residual(plan:lz78-ziv-inequality-discharge-moonshot-plan)` 5 件、新規 sorry 5 件、
- `lake env lean` 0 errors。

**proof-log**: no (Phase 2.1 / 2.2 と同形 mechanical 化)。

### Phase 2.x — ripple (caller drift handling, 散文 transitive 明示) 📋

- [ ] **2.x.1** Phase 2.0-2.3 の signature 改変結果として、以下 caller が transitive sorry を引き継ぐ可能性を `rg` で再確認:
  - `LempelZiv78.lean` (本 plan touch 対象外、ただし上流の `lz78_two_sided_optimality_*` を呼ぶ可能性)
  - `LZ78ConverseAsymptotic.lean` (本 plan suspect 0 件、touch 対象外)
  - `LZ78GreedyLongestPrefix.lean` (本 plan suspect 0 件、touch 対象外)
  - `LZ78PhraseCountAsymptoticBody.lean` (本 plan suspect 0 件、touch 対象外)
  - `LZ78TreeInducedAEP.lean` (本 plan suspect 0 件、touch 対象外)
  - `LZ78ConverseUDObject.lean` (本 plan suspect 0 件、touch 対象外)
  - `LZ78ZivCountingBody.lean` / `LZ78ZivEntropyBridge.lean` / `LZ78ZivInequality.lean` / `LZ78ZivTreeBridge.lean` (本 plan suspect 0 件、touch 対象外)

- [ ] **2.x.2** transitive sorry を引き継ぐ caller を `rg -l 'lz78_two_sided_optimality_(ergodic|greedy_impl|distinct_genuine|distinct_aseventual|distinct_ziv_core_wired)' InformationTheory/Shannon/` で列挙、各 caller の docstring に **transitive sorry の散文** を追加 (Pilot Pattern C):
  ```
  Transitive `sorry` via `<upstream decl>` (Phase 2.x retreat). No `@residual`
  tag is attached — the closure responsibility belongs to the upstream
  declaration's `@residual(<class>:<slug>)`.
  ```
  即興 `(<class>:<slug>, transitive)` vocabulary 禁止 (audit-tags.md 未登録)。

- [ ] **2.x.3** ripple 完了時 全 file で `lake env lean` 再 verify。olean refresh は各 file 単位で済ませる。

**Phase 2.x DoD**:
- 全 caller の transitive sorry が散文化済、即興 vocabulary 0 件、
- 各 file `lake env lean` 0 errors。

**proof-log**: no (mechanical 散文追加)。

### Phase 2.4 — audit-2 (Phase 2.0-2.3 + 2.x 全件) 📋

- [ ] **2.4.1** orchestrator は `honesty-auditor` を起動。対象:
  - Phase 2.0: 3 declarations (Pattern H FALSE-conditioned wrapper の defect kind rename + `@residual(defect:false-hypothesis)` classification 正しさ + def-level retract-candidate 妥当性)
  - Phase 2.1 / 2.2 / 2.3: 19 declarations の load-bearing predicate consumer の sorry 化判定 + 境界判定 (Phase 1.5 / 2.x で残った V+S 境界例も再評価)
  - Phase 2.x: 全 caller の transitive 散文の vocabulary 整合 + 即興 tag 不在確認
  - alias retract: `IsSMBToLZ78ConverseChainBridge` の retract-candidate 付与正しさ + `name-laundering-alias` kind の audit-tags.md 整合 (未決事項 #3)

- [ ] **2.4.2** verdict 受領 + 修正対応:
  - `ok` → Phase V 着手
  - `questionable` → docstring refine、Phase V 進行
  - `defect` → 当該 declaration を撤回 / 修正、Phase V 進行前に解決

**proof-log**: yes (auditor verdict + 修正対応記録)。

### Phase V — verify + 計画反映 📋

- [ ] **V.1** 全 LZ78 file で `lake env lean` 確認 (signature 改変があった file は事前 olean refresh、Pilot Pattern A):
  ```bash
  for f in InformationTheory/Shannon/LZ78*.lean; do
    echo "=== $f ==="
    lake env lean "$f"
  done
  ```

- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg -c '@audit:suspect' InformationTheory/Shannon/LZ78*.lean | awk -F: '{s+=$2} END {print "suspect:", s}'                       # = 0
  rg -c '@audit:defect\(degenerate\)' InformationTheory/Shannon/LZ78*.lean | awk -F: '{s+=$2} END {print "defect(degen):", s}'  # = 0 (rename 完了確認)
  rg -c '@audit:defect\(launder\)' InformationTheory/Shannon/LZ78*.lean | awk -F: '{s+=$2} END {print "defect(laund):", s}'      # = 1 (alias 残置のため)
  rg -c '🟢ʰ' InformationTheory/Shannon/LZ78*.lean | awk -F: '{s+=$2} END {print "🟢ʰ:", s}'                                       # = 0
  rg -c '@residual\(plan:lz78-residual-discharge-plan\)' InformationTheory/Shannon/LZ78*.lean | awk -F: '{s+=$2} END {print "residual(residual):", s}'
  rg -c '@residual\(plan:lz78-ziv-inequality-discharge-moonshot-plan\)' InformationTheory/Shannon/LZ78*.lean | awk -F: '{s+=$2} END {print "residual(ziv-ineq):", s}'
  rg -c '@residual\(plan:lz78-blockrv-refactor-plan\)' InformationTheory/Shannon/LZ78*.lean | awk -F: '{s+=$2} END {print "residual(blockrv):", s}'
  rg -c '@residual\(plan:lz78-achievability-converse-plan\)' InformationTheory/Shannon/LZ78*.lean | awk -F: '{s+=$2} END {print "residual(achiev-conv):", s}'
  rg -c '@residual\(defect:false-hypothesis\)' InformationTheory/Shannon/LZ78*.lean | awk -F: '{s+=$2} END {print "residual(false-hyp):", s}'   # = 3
  rg -c '@audit:retract-candidate' InformationTheory/Shannon/LZ78*.lean | awk -F: '{s+=$2} END {print "retract-candidate:", s}'   # ≥ 4 (alias + @simp lemma + IsLZ78ZivCombinatorialCoreOverhead def + load-bearing predicate retract判断)
  rg -nw 'sorry' InformationTheory/Shannon/LZ78*.lean | wc -l
  ```
  期待値: suspect 0、defect(degenerate) 0、🟢ʰ 0、residual 合計 30 (rough: 15 + 7 + 4 + 4 = 30、ただし V 降格や transitive 散文化分の差分は ±5 程度)、新規 sorry 30 件 (各 residual 1 sorry)、retract-candidate ≥ 4 件。

- [ ] **V.3** 親 plan banner 更新:
  - `lz78-moonshot-plan.md` 冒頭 banner に「sorry-based 移行完了 (`docs/shannon/lz78-sorry-migration-plan.md` 参照)、L-LZ1〜L-LZ5 の pass-through 設計は変更なし」追記。
  - `lz78-residual-discharge-plan.md` / `lz78-ziv-inequality-discharge-moonshot-plan.md` / `lz78-blockrv-refactor-plan.md` / `lz78-achievability-converse-plan.md` 各 plan に「sorry-based 移行完了 (N 件)」追記。

- [ ] **V.4** Pilot 知見を `.claude/handoff-sorry-migration.md` (または後続 family 用テンプレート) に反映:
  - **Pattern H sweep** (FALSE predicate-conditioned wrapper の defect kind rename + `@residual(defect:false-hypothesis)`) の手順を runbook 化候補。本 family は 3 件で実証。
  - **alias 廃止 (CLAUDE.md「sorry を書けない箇所での対処順序」第一選択)** の実例: `IsSMBToLZ78ConverseChainBridge` の def-level retract + consumer 直接書換。
  - LZ78 family が 4 plan slug + Pattern H の 5 path で sweep 完了した sequence。
  - 4 plan slug の中で **`lz78-residual-discharge-plan` が最も多くの consumer (15 件)** を持つ事実 → 上流 SMB sandwich + chain-rule discharge の完成が当該 family の closure に直結。

## 撤退ライン

- **L-MIG-1 (variational hyp / regularity hyp の load-bearing 判定が auditor で変動)**: Phase 1.5 境界判定 2 件 (`lz78_asymptotic_optimality_with_greedy_encoding` / `lz78_asymptotic_optimality_with_greedy_impl`) について auditor が「4 sandwich ingredient は achievability/converse 本体と等価」と判定したら、Phase 1.5 暫定の `@residual(plan:lz78-blockrv-refactor-plan)` を維持。逆に「pure variational pass-through wrapper」と判定したら `@residual` 削除 + 純タグ削除に降格 (Phase 1 V 扱い)。Phase 1.6 audit-1 で確定。

- **L-MIG-2 (Phase 2.x で load-bearing predicate retract-candidate 化すると外部 consumer drift)**: 本 family の 8 load-bearing predicate (`IsLZ78AchievabilityChainHyp` / `IsLZ78ConverseChainHyp` / `IsLZ78AchievabilityZivUpperBound` / `IsLZ78ConverseCodingLowerBound` / `IsLZ78ZivCombinatorialCore` / `IsLZ78ZivCombinatorialCoreOverhead` (FALSE) / `IsLZ78EncodingLengthLowerBound` / `IsLZ78ZivAsEventual`) は **全て LZ78 family 内 closed** (verbatim cross-family 検証済、Wyner–Ziv `IsWynerZivBinning*` の Relay CF 再利用のような外部 consumer は無い)。**predicate 削除は本 plan 範囲外** (retract-candidate 付与のみ)、L-MIG-2 発動条件は事実上空 (cross-family 0 件のため)。ただし `LempelZiv78.lean` (本 plan touch 対象外) が `IsLZ78AchievabilityChainHyp` 等を consumer として持つ可能性は要 Phase 2.x で `rg` 確認。残存 consumer がある場合は **predicate 削除しない / retract-candidate 付与のみ** + 散文注記。

- **L-MIG-3 (Pattern H defect kind rename `degenerate` → `false-hypothesis` の auditor pushback)**: Phase 2.0 で `LZ78ZivTreeNode.lean:651` / `:712` の `@audit:defect(degenerate)` を `@audit:defect(false-hypothesis)` (より精確) に rename するが、auditor が「degenerate-definition 悪用と false-hypothesis は audit-tags.md kind 語彙では区別不要、現状の `degenerate` 維持」と判定したら、Phase 2.0 の rename を **巻き戻し** + `@audit:defect(degenerate)` を維持 + `@residual(defect:degenerate)` で sorry 化。本 plan のデフォルトは rename だが auditor 判定優先 (Pattern F 同等の inline detection)。

- **L-MIG-4 (Approach 変更: sweep scope を縮める)**: 全 Phase が 1-2 session で完走しない / honesty-auditor が DEFECT を多発させる場合、`LZ78ZivTreeNode.lean` の Pattern H 3 件 (Phase 2.0) + `LZ78ConverseDischarge.lean` 5 件 (Phase 2.1.A) のみで pilot を close し、残り 22 件は後続 session に分離 (Hoeffding pilot の L-MIG-4 相当)。

## 未決事項 (auditor / user 委任可)

1. **8 load-bearing predicate の deprecate 方針** (user 確認):
   Phase 2.x ripple で 8 predicate (`IsLZ78AchievabilityChainHyp` 等) の consumer
   が全て sorry 化されるが、predicate 定義自身は **削除しない / retract-candidate
   付与のみ** が本 plan のデフォルト。cross-family 0 件のため Wyner–Ziv のような
   外部依存問題はないが、LZ78 family 内の other (本 plan touch 対象外) file が
   依然 consumer の可能性あり。**auditor 判定対象** + user 確認待ち。

2. **Pattern H defect kind rename の auditor verify** (auditor 判定対象、L-MIG-3 連動):
   `LZ78ZivTreeNode.lean:651/712` の `@audit:defect(degenerate)` を
   `@audit:defect(false-hypothesis)` に rename するが、`degenerate` (退化定義悪用)
   と `false-hypothesis` (仮説自体が偽) の境界判定を auditor 委任。本 plan の
   デフォルトは rename (FALSE predicate を hyp に取る wrapper は「仮説が偽」が
   精確であり、退化定義悪用とは別物)、auditor pushback あれば L-MIG-3 発動。

3. **`IsSMBToLZ78ConverseChainBridge` alias の `name-laundering-alias` retract-candidate kind**:
   audit-tags.md「`@audit:retract-candidate(<reason>)`」表で
   `circular-passthrough` / `load-bearing-predicate` 等は登録済だが
   `name-laundering-alias` は未登録 (新規 reason 候補)。**auditor 判定**:
   既存 reason variant で代替可能なら従う (例: `circular-passthrough` で代用)、
   不可なら audit-tags.md の `@audit:retract-candidate` reason variant 拡充 PR
   候補として handoff 反映。

4. **🟢ʰ marker (LZ78ZivTreeNode.lean:631) の inline 削除** (auditor 確認):
   line 631 の docstring 内 prose `🟢ʰ` を Phase 2.0.2 で削除 (deprecated
   vocabulary、audit-tags.md 移行 recipe 適用)。削除時に散文を「load-bearing
   hypothesis (FALSE)」と書換 (HONESTY ALERT は維持)。**auditor 判定**: 散文
   refine の強度。

5. **proof done を本 plan で目指さない方針の明示確認** (user 確認):
   本 plan の DoD は **type-check done** のみ。LZ78 系の analytical closure
   (Cover–Thomas Lemma 13.5.5 distinct-phrase combinatorial core の a.s.-eventual
   reformulation / Eq. 13.124 / 13.130 n-letter chain-rule 本実装 /
   Algoet-Cover sandwich) は **未着手のまま** で本 plan は close する。
   `lz78-moonshot-plan.md` の L-LZ1〜L-LZ5 pass-through 状態を変えない。

6. **Wall name register 拡張提案** (user 判断対象、R4):
   本 plan は plan-slug 形で 4 slug に揃えるが、本 sweep を通して以下 wall
   候補が浮上 — `audit-tags.md`「Wall name register」拡張 PR の候補として
   handoff 反映:
   - **`wall:lz78-combinatorial-core`** — Cover–Thomas Lemma 13.5.5
     distinct-phrase 組合せ核 `c·log c ≤ ∑ⱼ -log qⱼ` の Mathlib 不在性。
     LZ78 内 closed なため当面 register 追加は不要だが、後続 LZ77 / 他 universal
     coding family で再出現する可能性あり。
   - **`wall:lz78-aseventual-ziv`** — a.s.-eventual Ziv inequality
     `limsup (c·log₂ c / n) ≤ H₂` (genuine, FALSE per-block core の honesty
     replacement)。`IsLZ78ZivAsEventual` の satisfiability (ergodic process で
     成立) は別途証明されており、wall 化 vs plan-slug 化の境界例。
   - 共有 sorry 補題集約しない方針で本 plan は処理、Wall register 拡張 PR は
     後続セッションで検討。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 plan 起草**: lean-planner (本 session、docs-only) が
   `InformationTheory/Shannon/LZ78*.lean` 20 file + `LempelZiv78.lean` 1 file の
   legacy tag を verbatim 読込で per-declaration 分類。
   - **計数誤差発見** (Pilot Pattern D 適用):
     - ブリーフ「LempelZiv78.lean (3)」は誤 (verbatim suspect = 0)。本 plan
       scope から除外。
     - ブリーフ合計 34 件は実測 30 suspect + 1 🟢ʰ (prose-of-line-652) +
       3 `@audit:defect(*)` 併持 = 30+3 distinct 件に修正。
   - **既存 sorry 計数**: word-boundary `rg -nw 'sorry'` で 0 hit、実 sorry 0
     件。Pilot Pattern D 適用済。
   - **Pattern H 発見** (planner 段階 inline 検出):
     `LZ78ZivTreeNode.lean:391` の `def IsLZ78ZivCombinatorialCoreOverhead` が
     mathematically FALSE (`LZ78ZivTreeBridge.not_isLZ78ZivCombinatorialCoreOverhead`
     で genuine refutation 済) + 依存 2 declarations (line 651 / 712) が
     vacuously conditioned + 既に `@audit:defect(degenerate)` 付与済 + 著者
     ⚠ DEFECT 明示済。本 plan で `defect:false-hypothesis` に rename + Phase 2.0
     で sorry 化。後継 plan slug `lz78-aseventual-achievability-plan` を
     `@audit:closed-by-successor` で明示。
   - **defect(launder) alias 発見** (planner 段階 inline 検出):
     `LZ78SMBSandwich.lean:298` `def IsSMBToLZ78ConverseChainBridge` が literally
     alias (`:= IsLZ78ConverseChainHyp`) + 既に `@audit:defect(launder)` 付与済
     + 唯一 consumer (`line 420 lz78_converse_lower_bound_ergodic_of_bridge`)
     のみ。CLAUDE.md「sorry を書けない箇所での対処順序」第一選択 = 定義書換
     (alias 廃止 + consumer 直接書換 + retract-candidate 付与) を採用。
   - **cross-family 0 件確定**: `rg -n '^import InformationTheory' InformationTheory/Shannon/LZ78*.lean InformationTheory/Shannon/LempelZiv78.lean` で全 import が `InformationTheory.Shannon.*` 内部のみ。`LZ78ConverseDischarge.lean:67` の WynerZiv 言及は散文 reference のみ (`import` 無し、brief 明示の既知例)。`McMillanKraftBridge.lean` (docstring 散文) + `StationaryKernel.lean` (LZ78 internal regularity constructor) も非 entanglement。
   - **戦略決定**: file 単位 sweep + plan-slug 4 種 + Pattern H 1 path、共有 wall lemma 集約しない (audit-tags.md Wall register 未登録)、並列実行しない (chain dependency 密)。Phase 順序: 0 → 1 (V/C cleanup 候補 0 件予測 → skip) → 1.5 (S+alias retract 22+1 件) → 1.6 audit-1 → 2.0 (Pattern H 3 件) → 2.1 (10 件) → 2.2 (4 件) → 2.3 (5 件) → 2.x ripple → 2.4 audit-2 → V verify。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
