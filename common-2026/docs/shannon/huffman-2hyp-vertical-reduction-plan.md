# Huffman 2-hypothesis vertical reduction — 集約計画 🌙

> **Status (2026-05-24)**: 起草 (Wave 1.5-c)、Phase 設計は未着手 (後続 `lean-planner` agent
> による Phase 起草待ち)。本 plan は **既存 Huffman 3 plan の 2 hypothesis 共有部分** を
> 1 SoT に集約するための統合 stub. 本 plan 自身は新規実装を含まない (既存 publish 物
> 30 declaration の slug 集約と vertical reduction primitive `MergedHuffmanAuxIdentHypothesis`
> の整理が主目的).
>
> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A''. Huffman 最適性 (2 hypothesis 完全 discharge)」
> - 既存 3 plan (本 plan に集約される 2 hypothesis 関連の suspect/staged tag):
>   - [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md) (Phase 3 完遂、T1-A' 系の vertical
>     reduction body 9 件が slug `huffman-moonshot-plan` のまま誤付与) →
>     本 plan に slug 移管 (8 件 → `staged(huffman-2hyp)`、1 件 → `staged(huffman-aux-ident)`)
>   - [`huffman-optimality-moonshot-plan.md`](./huffman-optimality-moonshot-plan.md) (weak form
>     publish、2 hypothesis の `∀…∃…` predicate 引数受け取り完成) →
>     本 plan に slug 移管 (2 件 → `staged(huffman-2hyp)` + `closed-by-successor(huffman-2hyp-vertical-reduction)`)
>   - [`huffman-t1apprime-partial-moonshot-plan.md`](./huffman-t1apprime-partial-moonshot-plan.md)
>     (plumbing 補題 publish、Section C-M + Wave 4-H/J/K/P で extractor / wrapper 拡張) →
>     本 plan に slug 移管 (19 件 → `staged(huffman-2hyp)`)
> - 監査根拠: [`docs/audit/wave1-plan-sync-source-coding.md`](../audit/wave1-plan-sync-source-coding.md)
>   §Recommendations 1+2、[`docs/audit/defect-inventory-2026-05-24.md`](../audit/defect-inventory-2026-05-24.md) §7.3 item #6.

## 動機 (Motivation)

Cover-Thomas Theorem 5.8.1 (Huffman 最適性) の formalization は、**本 plan 起草時点で 3 つの
plan に分散して管理**されていた:

| 既存 plan | scope | suspect tag 件数 (2026-05-24) |
|---|---|---|
| `huffman-moonshot-plan` (Phase 3 完遂) | `huffmanLength` 構成 + Kraft 充足. T1-A' / T1-A'' は scope-out | **9** (T1-A' 系の vertical reduction body が誤って slug 継承) |
| `huffman-optimality-moonshot-plan` (T1-A') | weak form `huffmanLength_optimal_with_hypotheses` (2 hyp 引数受け取り) を publish | **2** (主定理 + 内部 induction motor) |
| `huffman-t1apprime-partial-moonshot-plan` (T1-A'' partial) | plumbing 補題 + Section C-M + Wave 4-H/J/K/P で extractor / wrapper を publish | **19** (plan は 119 行で predicate API scope が plan 想定を大幅超過) |
| **合計** | — | **30** |

問題:

1. **同じ 2 hypothesis** (`SwapNormalizationHypothesis` `HuffmanOptimality.lean:759` /
   `HuffmanMergedIdentificationHypothesis` `:776`) を **3 plan が chain で扱う**. 本質 load-bearing
   は **2 hypothesis のみ**で、30 件の suspect の大半は extractor / wrapper / vertical reduction
   primitive 経由の repackaging.
2. **slug mis-attribution**: `huffman-moonshot-plan` (Phase 3 まで scope) に T1-A' 系の vertical
   reduction (Hyp1 discharge 経路、strong form) の suspect が流れ込んでいる. plan scope と
   suspect が乖離.
3. **plan-side stale**: `huffman-t1apprime-partial-moonshot-plan` は 119 行 / DoD ~175 行で publish
   完了とあるが、実装ファイル `HuffmanT1APPrimeBody.lean` は Section C-M + Wave 4 群を追加で
   publish 済 (`SwapNormalizationHypothesis_apply_witness` 群 / Section J combined hypothesis 投影
   etc.). plan ドキュメントが追従していない.

本 plan は **30 件 → 2 件相当に visibility を圧縮** することを主目的とし、コード本体は不変、
docstring 内 `@audit:KIND(SLUG)` タグの slug 集約 + 既存 3 plan の status 注記のみで完了する.

## Scope

### 2 load-bearing hypothesis (本 plan SoT)

1. **`SwapNormalizationHypothesis`** (`Common2026/Shannon/HuffmanOptimality.lean:759`)
   - Cover-Thomas Lemma 5.8.1 (i) Kraft = 1 shortening 込み swap normalization.
   - genuine analytic Prop (`∀…∃…` で `:= True` ではない).
   - 縦分解候補: `EqualizingPermHypothesis` (FALSE と判定済、`HuffmanSwapNormalizationBody.lean:`
     judgement log #3 参照) / `EqualizingSwapTargetHypothesis` (同 FALSE).
   - 残タスク: 上記縦分解とは独立な discharge 経路の探索 (`swap_normalization_proof`
     `HuffmanSwapNormProof.lean` が Hyp1 を **完全 discharge 済**であり、本 hypothesis は
     `HuffmanStrongForm.lean:176` `huffmanLength_optimal_modulo_aux_ident` で T1-A' weak form
     から **strong form (Hyp1 free)** への昇格に既に使われている).

2. **`HuffmanMergedIdentificationHypothesis`** (`Common2026/Shannon/HuffmanOptimality.lean:776`)
   - α/α' (`{y // y ≠ b}` Subtype) structural correspondence — `huffmanLength` 再帰の
     2 carrier 間整合.
   - 縦分解 primitive: `MergedHuffmanAuxIdentHypothesis` (`HuffmanMergedAuxIdent.lean`) で
     `huffmanLengthAux` レベルの combinatorial 恒等式に縮約済 (vertical reduction primitive,
     下記 §「1 vertical reduction primitive」).
   - 残タスク: `MergedHuffmanAuxIdentHypothesis` の本格 discharge — `huffmanStep` の
     `Classical.choose` 非決定性 (min 選択の tie 破り) を carrier 横断で対応付ける必要があり,
     judgement log #3 で「真の壁」と特定済.

### 1 vertical reduction primitive

- **`MergedHuffmanAuxIdentHypothesis`** (`Common2026/Shannon/HuffmanMergedAuxIdent.lean`)
  - 原 `HuffmanMergedIdentificationHypothesis` を `huffmanLength` (measure 層) ではなく
    `huffmanLengthAux` (multiset 層) の combinatorial 恒等式に下げた primitive.
  - 縦分解 publish: `huffmanMergedIdentification_of_aux`
    (`HuffmanMergedIdentBody.lean:155`) で原 hypothesis を完全証明で導く.
  - 用途: `huffmanLength_optimal_modulo_aux_ident` (`HuffmanStrongForm.lean:176`) で
    Hyp1 (`swap_normalization_proof`) discharge 済 + Hyp2 を primitive 経由で残す
    strong form (= 残 hypothesis 1 件のみ) を実現.

### 集約される 30 declaration (slug 移管対象)

source: [`wave1-plan-sync-source-coding.md`](../audit/wave1-plan-sync-source-coding.md)
§Per-plan analysis (huffman-* 3 plan).

| file | line | declaration | 旧 slug | 新 slug |
|---|---|---|---|---|
| `HuffmanOptimality.lean` | 778 | `huffmanLength_optimal_aux_with_hypotheses` (private induction motor) | `huffman-optimality-moonshot-plan` | `staged(huffman-2hyp)` + `closed-by-successor(huffman-2hyp-vertical-reduction)` |
| `HuffmanOptimality.lean` | 1028 | `huffmanLength_optimal_with_hypotheses` (主定理 weak form) | `huffman-optimality-moonshot-plan` | `staged(huffman-2hyp)` + `closed-by-successor(huffman-2hyp-vertical-reduction)` |
| `HuffmanT1APPrimeBody.lean` | 157, 178, 200, 224, 280, 297, 378, 400, 419, 439, 459, 524, 531, 538, 608 (15 件) | Section C (ident extractor) / D (dichotomy) / F (combined wrapper) / H (witness extraction) / J (combined hyp 投影) / M (terminal wrapper) / Wave 4 各種 | `huffman-t1apprime-partial-moonshot-plan` | `staged(huffman-2hyp)` |
| `HuffmanT1APPrimePartial.lean` | 597, 613, 839, 854 (4 件) | universe-relaxed / tuple / contraposition wrapper | `huffman-t1apprime-partial-moonshot-plan` | `staged(huffman-2hyp)` |
| `HuffmanMergedIdentBody.lean` | 154, 171 | `huffmanMergedIdentification_of_aux` (vertical reduction primitive → 原) / `huffmanLength_optimal_with_swap_and_aux` (primitive 経由 wrapper) | `huffman-moonshot-plan` | `staged(huffman-2hyp)` |
| `HuffmanSwapNormalizationBody.lean` | 132, 208, 238, 251 (4 件) | `EqualizingPermHypothesis` / `EqualizingSwapTargetHypothesis` 経由の vertical reduction (両 primitive は FALSE と判定済、dead end) | `huffman-moonshot-plan` | `staged(huffman-2hyp)` |
| `HuffmanSwapStepChainBody.lean` | 343, 359 | chain hypothesis 経由の triple/2-way wrapper | `huffman-moonshot-plan` | `staged(huffman-2hyp)` |
| `HuffmanStrongForm.lean` | 175 | `huffmanLength_optimal_modulo_aux_ident` (Hyp1 discharged via `swap_normalization_proof`、Hyp2 のみ load-bearing) | `huffman-moonshot-plan` | `staged(huffman-aux-ident)` |

**集計**:
- `staged(huffman-2hyp)`: **29 件** (2 load-bearing hypothesis 経由の wrapper / extractor 群)
  - うち 2 件 (`HuffmanOptimality.lean:778, :1028`) は `closed-by-successor(huffman-2hyp-vertical-reduction)` 併用
- `staged(huffman-aux-ident)`: **1 件** (Hyp1 discharged、Hyp2 のみ残の strong form 1 件)

## Approach

本 plan は **3 段階の集約** を行う:

1. **slug 集約** (本 wave 1.5-c で完遂): 既存 30 件の docstring 内 `@audit:suspect(<old-slug>)` を
   上記 cheatsheet に従って `@audit:staged(huffman-2hyp)` / `staged(huffman-aux-ident)` /
   `closed-by-successor(huffman-2hyp-vertical-reduction)` に書換. コード本体 / signature / body
   は不変.
2. **既存 3 plan の status 注記** (本 wave 1.5-c で完遂): 各 plan の Status block 直下に
   「2026-05-24 Wave 1.5: 2 hypothesis 共有部分を `huffman-2hyp-vertical-reduction-plan.md` に
   集約」と 1-2 行追記. 既存 plan は archive 化せず、本 plan からの cross-ref で生存.
3. **discharge 戦略 Phase 起草** (後続 `lean-planner` agent 仕事、本 plan では TBD): 2 hypothesis
   + 1 primitive の完全 discharge ルートを Phase 設計. judgement log では
   `MergedHuffmanAuxIdentHypothesis` の `Classical.choose` 非決定性が真の壁と特定済.

## DoD (Definition of Done)

### 短期 (本 wave 1.5-c 完了時)

- [x] 30 declaration の slug 集約完了 (本 plan stub 生成と同 commit)
- [x] 既存 3 plan の Status block 注記完了 (cross-ref 明示)
- [x] `audit-tags.md` 語彙拡張 (`closed-by-successor` / `superseded-by`) 追加完了
- [x] 触った各 `.lean` ファイルで `lake env lean Common2026/Shannon/Huffman*.lean` silent

### 中期 (Phase 起草後)

- [ ] `MergedHuffmanAuxIdentHypothesis` の discharge 戦略 Phase 設計 (`lean-planner` 仕事)
- [ ] `SwapNormalizationHypothesis` の `swap_normalization_proof` (`HuffmanSwapNormProof.lean`)
      による完全 discharge の verbatim 文書化 (現状コード本体に既存だが plan documentation 化)
- [ ] vertical reduction primitive `MergedHuffmanAuxIdentHypothesis` の Phase 別 step-by-step
      discharge plan

### 最終 DoD (本 plan ゴール、まだ遠い)

- [ ] **`huffmanLength_optimal` hypothesis-free** の publish: 2 hypothesis 完全 discharge + Phase 4-5
      (sibling property + 主定理 optimality) 完成 + strong form
      `huffmanLength_optimal_modulo_aux_ident` の Hyp2 discharge → unconditional 主定理.
- [ ] `T1-A''` ステータスを `textbook-roadmap.md` で `DONE` に昇格.

達成時、本 plan は **`@audit:staged(huffman-2hyp)` 29 件 + `staged(huffman-aux-ident)` 1 件 を
全件 closure** し、`huffman-2hyp-vertical-reduction-plan` slug の suspect/staged は 0 件になる.

## 残タスク (Phase 設計は後続 `lean-planner` 仕事、本 plan では TBD)

1. **TBD**: `MergedHuffmanAuxIdentHypothesis` の本格 discharge 経路設計
   - judgement log #3 で `huffmanStep` の `Classical.choose` 非決定性 (min 選択の tie 破り) が
     真の壁と判定済. carrier 横断 (`α` ↔ `{y // y ≠ b}` Subtype) で対応付ける戦略.
2. **TBD**: `SwapNormalizationHypothesis` の現状 discharge コードの整理
   - `HuffmanSwapNormProof.lean` の `swap_normalization_proof` が **既存コードで完全 discharge 済**
     (`HuffmanStrongForm.lean:176` でその discharge を経由して strong form を構築). plan
     documentation が未整備.
3. **TBD**: Wave 1 で同定された `huffman-t1apprime-partial-moonshot-plan` の plan-side stale
   (Wave 4-H/J/K/P 追記漏れ) を本 plan の cross-ref で代替するか、別途 update するかの判断.
4. **TBD**: Phase 4-5 (sibling property + 主定理 optimality) の T1-A''' における再開計画.
   既存 3 plan が「scope-out」と書いた残作業の本 plan への移管整理.

## 制約

- 既存 3 plan ファイル (`huffman-moonshot-plan.md` / `huffman-optimality-moonshot-plan.md` /
  `huffman-t1apprime-partial-moonshot-plan.md`) は archive 化しない (Status block 注記 +
  cross-ref のみ追加、本文不変).
- 既存 Lean code (signature / body) は不変. docstring 内タグ書換のみ.
- 本 plan stub は Phase 設計を含まない (skeleton, 後続 `lean-planner` 仕事). 実装計画は TBD.

## 判断ログ

1. **2026-05-30 — Hyp2 (`HuffmanMergedIdentificationHypothesis`) は FALSE STATEMENT と確定、本 plan の discharge target は dead**:
   本 plan の SoT 2 load-bearing hypothesis のうち Hyp2 `HuffmanMergedIdentificationHypothesis`
   (`HuffmanOptimality.lean:777`) は、`MergedHuffmanAuxIdentHypothesis` と同一 statement
   (measure-level、`initMultiset_mergedMeasure_eq` 経由で aux 形に帰着) であり、**universal statement
   として機械的に FALSE と確定**。
   - **反例** (`docs/shannon/verify/merged_huffman_aux_ident_counterexample.py`、機械検証済):
     β={0,1,2,3} (card 4)、weights `[1,2,1,1]`、`a=0`, `b=2`。全強前提充足 + a,b first-merged でも
     x=0 で恒等式失敗 (merged depth 2 vs 期待 `huffmanLength Q a - 1 = 1`)。根本原因は決定的 colex
     tie-break の merge 不安定性 (詳細は `huffman-strong-form-completion-plan.md` 判断ログ #5)。
   - **帰結**: 本 plan の discharge target (Hyp2 wall `huffman_merged_identification_hypothesis_holds`
     を constructive に閉じる) は **dead**。`Draft/HuffmanWalls.lean` で当該 wall は
     `@audit:defect(false-statement) @audit:retract-candidate(deterministic-colex-merge-instability)`
     に reclassify 済 (sorry は false-statement の honest marker として残置)。Hyp1
     (`SwapNormalizationHypothesis`) は `swap_normalization_proof` で既に genuine discharge 済のため
     本 plan の 2-hyp のうち閉じる余地があるのは Hyp1 のみ。
   - **pivot 要**: per-symbol depth identity 経路全体が dead。tie-invariant な cost-level merge identity
     (`expectedLength(huffman Q) = expectedLength(huffman mergedMeasure) + (Q{a}+Q{b})`) へ pivot。
     本 plan の vertical-reduction 集約構造 (30 declaration の slug 移管) は維持しつつ、discharge target を
     cost-level に差し替える後続 plan 設計が必要。

## 関連 audit / planning 文書

- 集約根拠: [`docs/audit/wave1-plan-sync-source-coding.md`](../audit/wave1-plan-sync-source-coding.md)
  §Per-plan analysis (huffman-* 3 plan) + §Recommendations 1+2.
- inventory: [`docs/audit/defect-inventory-2026-05-24.md`](../audit/defect-inventory-2026-05-24.md)
  §7.3 item #6.
- audit 語彙: [`docs/audit/audit-tags.md`](../audit/audit-tags.md) §「語彙」
  (`closed-by-successor` / `superseded-by` 拡張は本 wave で追加).
- mathlib inventory (既存 3 plan 共通): [`huffman-mathlib-inventory.md`](./huffman-mathlib-inventory.md) /
  [`huffman-optimality-mathlib-inventory.md`](./huffman-optimality-mathlib-inventory.md) /
  [`huffman-optimality-t1apprime-mathlib-inventory.md`](./huffman-optimality-t1apprime-mathlib-inventory.md).
