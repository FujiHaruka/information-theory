# Shannon: Huffman `@audit:staged` → sorry-based migration plan

> **Parent**: [`huffman-moonshot-plan.md`](huffman-moonshot-plan.md) (T1-A Phase 4-5 scope-out)
> + 関連 [`huffman-2hyp-vertical-reduction-plan.md`](huffman-2hyp-vertical-reduction-plan.md) /
> [`huffman-optimality-t1apprime-moonshot-plan.md`](huffman-optimality-t1apprime-moonshot-plan.md) /
> [`huffman-t1apprime-partial-moonshot-plan.md`](huffman-t1apprime-partial-moonshot-plan.md) /
> [`huffman-strong-form-completion-plan.md`](huffman-strong-form-completion-plan.md) /
> [`huffman-fullB-structure-plan.md`](huffman-fullB-structure-plan.md) /
> [`huffman-colex-determinism-plan.md`](huffman-colex-determinism-plan.md)。
> 本 plan は **proof completion ではなく `@audit:staged` 語彙の honesty 強化**
> (`docs/audit/audit-tags.md`「Deprecated」+「移行レシピ」) を目的とする独立 workstream。

## Context

### なぜ Huffman が staged migration pilot か

`docs/audit/sorry-migration-runbook.md`「並列実行候補 family」表は Huffman を次のように位置付ける:

> `@audit:staged` × 30 (suspect / defer ほぼ 0)。staged の migration recipe を pilot で確立する candidate。

Hoeffding pilot (`hoeffding-sorry-migration-plan.md`, commits `29dabff` / `51fca41`) は **`@audit:suspect` 19 件** の sweep を確立したが、`@audit:staged` 件数は 0 だった。Huffman は反対に **`@audit:staged` 中心**であり、本 plan は `staged → sorry+@residual` 変換規則を初めて実地で確立する。

verbatim 確認 (2026-05-25):

```bash
# rg -c '@audit:staged' Common2026/Shannon/Huffman*.lean
HuffmanT1APPrimeBody.lean:           15
HuffmanSwapNormalizationBody.lean:    4
HuffmanT1APPrimePartial.lean:         4
HuffmanSwapStepChainBody.lean:        2
HuffmanMergedIdentBody.lean:          2
HuffmanOptimality.lean:               2
HuffmanStrongForm.lean:               1
                              total: 30
```

```bash
# 既存 @audit:suspect / @audit:defer / 散文 🟢ʰ
suspect / defer / 🟢ʰ: 0 / 0 / 0

# @audit:closed-by-successor (HuffmanOptimality 重畳タグ)
HuffmanOptimality.lean: 2 (両件とも @audit:staged と同居)

# 既存 sorry 件数 (word-boundary 計数、Pattern D)
$ rg -nw 'sorry' Common2026/Shannon/Huffman*.lean
HuffmanT1APPrimePartial.lean:7:  "`Common2026/Shannon/HuffmanOptimality.lean` (T1-A' weak form publish, 1054 行 / 0 sorry)"
HuffmanOptimality.lean:714:     "T1-A' 主定理を完全な 0 sorry で publish するために、..."
# 2 hit はすべて docstring 内文字列、実 sorry 0 件 (Hoeffding pilot と同じ Pattern D)
```

slug は 2 種に集中:

- `huffman-2hyp`: 29 件 (`HuffmanOptimality.lean` 2 件は `closed-by-successor(huffman-2hyp-vertical-reduction)` と併用)
- `huffman-aux-ident`: 1 件 (`HuffmanStrongForm.lean:175`、Hyp1 discharged strong form)

これに加え、本 plan を起こす過程で **2 つの "honesty alert" コメント付き偽 predicate** が判明 (`HuffmanSwapNormalizationBody.lean:181` / `:91`):

- `EqualizingSwapTargetHypothesis` (line 190) — `eqSwapTarget_length_part_false` で **機械検証済の偽** 述語
- `EqualizingPermHypothesis` (line 110) — 上記の更なる縦分解、同じく **機械検証済の偽** 述語 (反例 `β = Fin 3, ll = ![1,2,3]`)

両者は **vacuously-true な含意 `(偽前提) → 結論`** を構成するために導入された predicate であり、本体実装内に既に「⚠ HONESTY ALERT — この述語は FALSE であり discharge 不能 (dead end)」と明記されている。本 plan は **circular bypass / hidden defect ではない** (genuine な含意定理として宣言済) ことを尊重しつつ、migration 過程で「false-hypothesis defect 上に積まれた構造物」として処理する判定軸を Phase 2.5 で確立する。

### 上位 moonshot plan との関係

`huffman-moonshot-plan.md` は **Phase 3 完遂 (4 件 publish: `huffmanLength` / `huffmanLength_pos` / `huffmanLength_kraft_le_one` / `exists_huffman_prefix_code`、953 行 / 0 sorry)** で DONE-UNCOND。撤退ライン §H-2 発動で Phase 4-5 (主定理 optimality) は後続 seed `T1-A'` に分離。

その T1-A' chain (T1-A' weak form / T1-A'' vertical reduction) は **2 hypothesis weak form** (`SwapNormalizationHypothesis` + `HuffmanMergedIdentificationHypothesis`) を残したまま publish され、それを各 file で **partial wrapper / extractor / re-publish wrapper** として消費する設計になっている。30 件の `@audit:staged(huffman-2hyp)` はその consumer 群に相当する。

本 plan は **その weak form を変えない**。sorry-based 移行は

- 仮説束 (`SwapNormalizationHypothesis` / `HuffmanMergedIdentificationHypothesis` / `HuffmanCombinedHypothesis` / `HuffmanChainCombinedHypothesis` / `MergedHuffmanAuxIdentHypothesis`) の中の **load-bearing claim** を仮説から外して **本文 `sorry`** に降ろす、
- 純構造的 pass-through (chain hypothesis projection / 偽 predicate からの vacuous-true 含意) は **タグ削除のみ** で `sorry` を新規に作らない、

という書換であり、**proof completion** (Cover-Thomas Theorem 5.8.1 strong form の analytical closure) は別 workstream (`huffman-2hyp-vertical-reduction-plan.md` 等) に残る。

### Honesty workflow と DoD

本 plan の DoD は `CLAUDE.md`「Definition of Done — 2 段階」の **type-check done**:

- 各 file `lake env lean Common2026/Shannon/<file>.lean` が 0 errors、
- 各新規 `sorry` に `@residual(<class>:<slug>)` タグが付き、
- 各 Phase 完了時に `honesty-auditor` を起動して classification を独立検証する。

`@audit:ok` (proof done) は **本 plan の出力にはならない** — Hyp1 (swap normalization) の analytical closure (= ~550 行 moonshot、`huffman-moonshot-plan.md` judgement log #3 で確認) と Hyp2 (huffman merged identification) の carrier-crossing 対応 (`huffman-strong-form-completion-plan.md` judgement log #3) はいずれも本 plan scope 外。

## Approach

**file 単位 sweep を 3 Phase + 1 wall mini-phase に分割**、共有 sorry 補題は **5 種に集約**。

### `@audit:staged` migration recipe の確立 (本 plan の主役)

`docs/audit/audit-tags.md`「Deprecated」表は `@audit:staged(WALL)` の移行先を:

> predicate 削除 → 共有 sorry 補題に置換 → `@residual(wall:<WALL>)`

と規定している。Huffman の場合 **`WALL` slug は Mathlib 壁ではなく plan slug** (`huffman-2hyp` = `huffman-2hyp-vertical-reduction-plan` 略形、`huffman-aux-ident` = `huffman-strong-form-completion-plan` 略形) であり、`audit-tags.md`「Wall name register」表には登録されていない。よって class は **`wall:` ではなく `plan:`** で揃える:

| 旧タグ | 新タグ | 共有 sorry 補題 (Wall slug 候補) |
|---|---|---|
| `@audit:staged(huffman-2hyp)` | `@residual(plan:huffman-2hyp-vertical-reduction)` | `HuffmanWalls.swap_normalization_hypothesis_holds` / `HuffmanWalls.huffman_merged_identification_hypothesis_holds` |
| `@audit:staged(huffman-aux-ident)` | `@residual(plan:huffman-strong-form-completion)` | `HuffmanWalls.merged_huffman_aux_ident_hypothesis_holds` |
| `@audit:closed-by-successor(huffman-2hyp-vertical-reduction)` | (削除、上記 `@residual(plan:huffman-2hyp-vertical-reduction)` に統合) | 上に同じ |

staged の **`reason` (元の壁) は docstring 散文で保存**する。例: `huffmanLength_optimal_with_hypotheses` (HuffmanOptimality.lean:1029) の旧 docstring 末尾の `@audit:staged(huffman-2hyp)` + `@audit:closed-by-successor(huffman-2hyp-vertical-reduction)` を `@residual(plan:huffman-2hyp-vertical-reduction)` に書き換える際、docstring 中段の「Weak form として swap normalization と identification の 2 hypothesis を引数で受け取る. 完全な discharge は後継 seed `T1-A''` で予定.」は **そのまま残す** (これが reason の保存)。

### 戦略の選択軸

`docs/audit/sorry-migration-runbook.md`「並列度の判断軸」+ Hoeffding pilot の「2 軸 (incidental migration / family sweep、shared wall 集約の要否)」を本 family について次のように決める:

1. **family sweep を採用** (incidental ではなく一括)。理由:
   - 30 件の staged が **5 つの hypothesis predicate** (`SwapNormalizationHypothesis` / `HuffmanMergedIdentificationHypothesis` / `HuffmanCombinedHypothesis` / `HuffmanChainCombinedHypothesis` / `MergedHuffmanAuxIdentHypothesis`) に集中。これらは **abbrev + And** で互いに reduce 可能 (`HuffmanCombinedHypothesis := Hyp1 ∧ Hyp2` 等)、ある file の predicate を deprecate すると依存 file の signature が機械的に更新を要する。incidental だと file 間 drift が起きやすい。
   - 30 件は 1 Phase 規模だが、`HuffmanT1APPrimeBody.lean` 単独で 15 件と偏りが大きいので Phase 2 を 2-3 sub-phase に分割可能 (sub-phase 別 file)。
   - Hoeffding pilot (suspect 19 件) と同程度の規模で 1-2 セッションで完走見込み。

2. **共有 sorry 補題に集約する**。Hoeffding は集約しなかったが、Huffman は集約する。理由:
   - 5 hypothesis predicate のうち上位 2 つ (`SwapNormalizationHypothesis` / `HuffmanMergedIdentificationHypothesis`) は **`HuffmanOptimality.lean:734` / `:758`** で abbrev 定義されており、本 plan migration 後の **唯一の closure 道筋** (`huffman-2hyp-vertical-reduction-plan` 完遂) は両 hypothesis を holds 化することに集約する。複数 file で同じ `Hyp1.holds` / `Hyp2.holds` を sorry 化すると wall の重複が起き、後続 plan 完遂で全 file を再 verify する必要が出る。
   - 集約先として **新規 file `Common2026/Shannon/HuffmanWalls.lean`** を提案 (但し本 plan で書込みはしない、Phase 1.5 で skeleton 提案、実装 agent が判断)。alternative: 各 hypothesis predicate の直後 (= 既存 `HuffmanOptimality.lean` 内 or `HuffmanMergedIdentBody.lean` 内) に `*_holds : <Hyp> := by sorry` を 1 件追加する集約方式 (= shared wall lemma の最小実装、Hoeffding と同様の per-file 配置)。

   `audit-tags.md`「Wall name register」拡張は **本 plan では行わない** (slug が `plan:` で揃うため不要)。後続 family (EPI/Stam 等) で wall register 拡張が必要なら別 PR。

3. **constructive recovery 候補の事前 identify (Pilot Pattern B)**。本 plan の対象 30 件のうち以下は **load-bearing predicate consumer ではなく純構造的 pass-through** であり、Phase 1 で **タグ削除のみ** で processing 可能と暫定判定。最終判定は Phase 0 inventory step で auditor が verify する:

   - `HuffmanSwapStepChainBody.lean:343` `huffmanLength_optimal_with_chain_combined` — chain hypothesis を捨てて 2-way reduce、`huffmanLength_optimal_with_combined` を呼ぶ slim wrapper
   - `HuffmanSwapStepChainBody.lean:359` `huffmanLength_optimal_via_chain_lift` — 上の逆 lift、同様
   - `HuffmanSwapNormalizationBody.lean:132` `swapNormalizationHypothesis_of_equalizingPerm` — `EqualizingPermHypothesis` (= 偽 predicate) からの vacuous-true 含意、body は genuine な構造で sorry 不要
   - `HuffmanSwapNormalizationBody.lean:208` `equalizingPerm_of_swapTarget` — 同上、偽 predicate からの含意
   - `HuffmanSwapNormalizationBody.lean:238` `swapNormalizationHypothesis_of_swapTarget` — 上 2 つの合成
   - `HuffmanT1APPrimeBody.lean:524`-`:538` `huffmanCombinedHypothesis_swap` / `huffmanCombinedHypothesis_ident` / `huffmanLength_optimal_with_combined` — abbrev `HuffmanCombinedHypothesis := And` の field projection 3 件
   - `HuffmanT1APPrimeBody.lean:280` / `:297` / `:608` `huffmanLength_optimal_via_partial_swap_when_eq` / `..._wrapper_explicit` / `..._terminal` — terminal wrappers (本来 P だが、Hyp1/Hyp2 を **削除せず** caller に押し出す形なら C で済む可能性、Phase 0 で判定)

   これらは「Hyp1/Hyp2 を消費するが、自身は **更に upstream の `huffmanLength_optimal_with_hypotheses`** を呼ぶ pass-through wrapper」であり、Hyp1/Hyp2 を残したまま `@audit:staged` タグだけ削除して **transitive sorry** (`huffmanLength_optimal_with_hypotheses` の sorry 化が transitive に流れる) で済む可能性が高い。Pilot Pattern C (= 散文で transitive 性を明示、`@residual` タグなし) を活用。

4. **transitive sorry の handling 方針 (Pilot Pattern C)**: `huffmanLength_optimal_with_hypotheses` (= 5 predicate consumer の上流) を Phase 2 で sorry 化したあと、上記 constructive recovery 候補 wrapper はすべて **transitive sorry** を持つ。即興 suffix (`@residual(plan:huffman-2hyp-vertical-reduction, transitive)`) は禁止 (audit-tags.md 未登録 vocabulary)、docstring 散文で次を明示:

   ```
   Transitive `sorry` via `huffmanLength_optimal_with_hypotheses` (Phase 2 retreat).
   No `@residual` tag is attached — the closure responsibility belongs to the upstream
   declaration's `@residual(plan:huffman-2hyp-vertical-reduction)`.
   ```

### 移行レシピ (declaration 単位、Hoeffding pilot との差分)

`docs/audit/audit-tags.md`「移行レシピ」を Huffman 用に拡張し、declaration ごとに **4 つのパターン** が出現する:

- **パターン P (predicate consumer)**: signature が `SwapNormalizationHypothesis` / `HuffmanMergedIdentificationHypothesis` / `HuffmanCombinedHypothesis` / `HuffmanChainCombinedHypothesis` / `MergedHuffmanAuxIdentHypothesis` のいずれかを hypothesis に取り、body はそれを destructure or 直接 forward する。
  - 移行: predicate hypothesis を **削除**、結論型は変えない、body `sorry` + `@residual(plan:huffman-2hyp-vertical-reduction)` (or `huffman-strong-form-completion` for aux-ident)。
  - 注意: 5 predicate のうち本 plan で signature 削除するのは **terminal declaration のみ** (= 他の declaration から呼ばれていない最下流 wrapper)。中間 wrapper は P→P 形を維持し、最終的に `huffmanLength_optimal_with_hypotheses` に統合される transitive sorry chain を作る。

- **パターン V (variational pass-through)**: Hoeffding では `tendsto_of_le_liminf_of_limsup_le` 仮説 (`h_liminf` / `h_limsup`) を pass-through する wrapper 群があったが、**Huffman の 30 件には該当なし** (verbatim 確認、Huffman の wrapper は variational hyp ではなく predicate hypothesis 一様)。よってパターン V は本 plan で発生しない。

- **パターン C (constructive bridge)**: 上記 §「constructive recovery 候補」7-9 件。signature 不変、body 不変、`@audit:staged` タグ削除のみ。
  - 移行先: `@residual` 付与なし、docstring 散文で「transitive `sorry` via `<upstream>`」を明示。

- **パターン S (`@audit:staged` メタ)**: 全 30 件は最終的に P / C のいずれかに resolve する。staged は「tier 4 legacy 語彙の代名詞」であり、resolve 後はパターン名と reason の組で扱う。

  - パターン S → C は Phase 1 (タグ削除のみ)
  - パターン S → P は Phase 2 (signature 改変 + body sorry)

### Phase 分割

- **Phase 0 — Inventory**: 30 件すべてを Read で verbatim 確認し、本 plan の §「在庫表」に P / C 分類を append (本 plan 起草時の事前判定を auditor が verify)。
- **Phase 1 — Cleanup pass (パターン C、低 risk)**: Constructive recovery 候補 ~9 件の `@audit:staged` タグ削除 + transitive 散文書込み。`@audit:closed-by-successor` も併用 (HuffmanOptimality.lean:778/:1028 の 2 件) を Phase 1.5 で別途処理 (これは bookkeeping、`@residual` に統合)。signature 改変なし、新規 `sorry` 0 件。
- **Phase 1.5 — Shared wall lemma 集約 (新規 file or per-file `*_holds` sorry)**: 5 hypothesis predicate それぞれに `*_holds : <Hyp> := by sorry` を **1 件ずつ** 追加 (集約方式は実装 agent 判断、両方 OK)。各 `*_holds` に `@residual(plan:huffman-2hyp-vertical-reduction)` (or `huffman-strong-form-completion` for aux-ident)。
- **Phase 1.6 — honesty-auditor #1**: Phase 1 / 1.5 全件 audit。verdict 確認後 commit。
- **Phase 2.1 — Predicate retreat (パターン P、terminal declaration)**: `huffmanLength_optimal_with_hypotheses` (HuffmanOptimality.lean:1029) と `huffmanLength_optimal_aux_with_hypotheses` (private, line 779) を **削除しない** (これらは weak form の publish そのもの、削除すると T1-A' weak form の API が消える)。代わりに body を:
  ```lean
  -- 旧
  huffmanLength_optimal_aux_with_hypotheses (Fintype.card α) h_swap h_ident P hP l hl_pos hl_kraft rfl
  -- 新
  huffmanLength_optimal_aux_with_hypotheses (Fintype.card α)
    swap_normalization_hypothesis_holds huffman_merged_identification_hypothesis_holds
    P hP l hl_pos hl_kraft rfl
  ```
  と書換、`h_swap` / `h_ident` 引数を signature から **削除** (sorry 化ではなく shared wall に置換)。これで `huffmanLength_optimal_with_hypotheses` 自身は signature 改変済 + body 0 sorry (wall に依存)、shared wall が `@residual(plan:...)` を保有。
- **Phase 2.2 — Predicate retreat (上流 wrapper)**: `huffmanLength_optimal_with_combined` / `huffmanLength_optimal_terminal` / `huffmanLength_optimal_modulo_aux_ident` 等の terminal wrapper を Phase 2.1 と同様に shared wall 経由に書換。
- **Phase 2.3 — Predicate retract-candidate (中間 abbrev)**: 5 hypothesis predicate のうち全 consumer が Phase 2.1 / 2.2 で shared wall 経由になった場合、abbrev 定義に `@audit:retract-candidate(load-bearing-predicate)` を付与 (削除はしない、後続 plan 完遂時の interface 互換用)。
- **Phase 2.4 — honesty-auditor #2**: Phase 2 全件 + predicate 監査。verdict 確認後 commit。
- **Phase V — Verify**: 全 13 file (Huffman.lean 含む) `lake env lean` 0 errors、`Common2026.lean` import 不変。集計コマンドで確認。

Phase 順を選んだ理由: Phase 1 (低 risk) → Phase 1.5 (shared wall 設置) を先行することで、Phase 2.1 で `huffmanLength_optimal_with_hypotheses` の body 書換が **既存 sorry-free な wall** に依存できる (sorry-on-sorry の連鎖を Phase 1.5 で安全弁化)。逆順だと Phase 2 で signature 改変中に shared wall が未設置で各 wrapper の sorry が独立に発生し、後で集約する余計な refactor が発生する。

## 在庫: 30 件の `@audit:staged` の verbatim 分類

verbatim 確認方法: `Common2026/Shannon/Huffman*.lean` 13 file を Read で
`@audit:staged` 周辺 docstring + 直後 `theorem` signature + body 1-3 行を実コードから読み込み、
「signature の hypothesis が load-bearing predicate か pure structural pass-through か」を 1 件ずつ判定。

各 declaration の `path:line` は `@audit:staged` タグ行 (docstring 末尾)。declaration 名はその直後。Phase 0 で完全 verify 必要。

### `HuffmanT1APPrimeBody.lean` (15 件 — 最大集中、Phase 2.x 分割推奨)

| line | decl 名 | staged の核 (1 行) | パターン | 移行後 class:slug | constructive recovery? |
|---:|---|---|---|---|---|
| 157 | `huffmanMergedIdentification_at_a` | `HuffmanMergedIdentificationHypothesis` の point-wise extractor (`x.val = a` case) | P | `plan:huffman-2hyp-vertical-reduction` | no (Hyp2 を直接消費) |
| 178 | `huffmanMergedIdentification_at_other` | 同 extractor (`x.val ≠ a` case) | P | `plan:huffman-2hyp-vertical-reduction` | no |
| 200 | `huffmanMergedIdentification_combined` | `if`-form alias (= `h_ident` の結論そのまま) | P | `plan:huffman-2hyp-vertical-reduction` | no |
| 224 | `huffmanMergedIdentification_dichotomy` | dichotomy form (`x.val = a` / `≠ a` の Or) | P | `plan:huffman-2hyp-vertical-reduction` | no |
| 280 | `huffmanLength_optimal_via_partial_swap_when_eq` | `h_swap` + `h_ident` の terminal wrapper | P | `plan:huffman-2hyp-vertical-reduction` | candidate (transitive via shared wall) |
| 297 | `huffmanLength_optimal_wrapper_explicit` | 上に `(_a _b : α)` explicit 引数追加 | P | `plan:huffman-2hyp-vertical-reduction` | candidate |
| 378 | `SwapNormalizationHypothesis_apply_witness` | hypothesis 結論の witness tuple 抽出 | P | `plan:huffman-2hyp-vertical-reduction` | no (Hyp1 を直接消費) |
| 400 | `SwapNormalizationHypothesis_witness_pos` | positivity だけ抽出 | P | `plan:huffman-2hyp-vertical-reduction` | no |
| 419 | `SwapNormalizationHypothesis_witness_kraft` | Kraft だけ抽出 | P | `plan:huffman-2hyp-vertical-reduction` | no |
| 439 | `SwapNormalizationHypothesis_witness_eq` | sibling eq だけ抽出 | P | `plan:huffman-2hyp-vertical-reduction` | no |
| 459 | `SwapNormalizationHypothesis_witness_expL` | expectedLength `≤` だけ抽出 | P | `plan:huffman-2hyp-vertical-reduction` | no |
| 524 | `huffmanCombinedHypothesis_swap` | abbrev `And` の `.1` projection | C | (タグ削除のみ) | YES |
| 531 | `huffmanCombinedHypothesis_ident` | abbrev `And` の `.2` projection | C | (タグ削除のみ) | YES |
| 538 | `huffmanLength_optimal_with_combined` | `HuffmanCombinedHypothesis → huffmanLength_optimal_with_hypotheses` | P | `plan:huffman-2hyp-vertical-reduction` | candidate (transitive) |
| 608 | `huffmanLength_optimal_terminal` | 上の alias (`H : HuffmanCombinedHypothesis` 1 引数) | P | `plan:huffman-2hyp-vertical-reduction` | candidate (transitive) |

### `HuffmanT1APPrimePartial.lean` (4 件)

| line | decl 名 | staged の核 (1 行) | パターン | 移行後 class:slug | constructive recovery? |
|---:|---|---|---|---|---|
| 597 | `huffmanLength_optimal_with_hypotheses_at` | universe-relaxed wrapper (`{α : Type v}` で `{α : Type u}` 形を呼ぶ) | P | `plan:huffman-2hyp-vertical-reduction` | candidate (transitive) |
| 613 | `huffmanLength_optimal_with_combined_hypothesis` | tuple 形 (`h : Hyp1 ∧ Hyp2`) wrapper | P | `plan:huffman-2hyp-vertical-reduction` | candidate (transitive) |
| 839 | `huffmanLength_optimal_with_pair_hypothesis` | `PProd` 形 wrapper | P | `plan:huffman-2hyp-vertical-reduction` | candidate (transitive) |
| 854 | `huffmanLength_optimal_with_hypotheses_contra` | contraposition form (`False` 結論) | P | `plan:huffman-2hyp-vertical-reduction` | candidate (transitive) |

### `HuffmanSwapNormalizationBody.lean` (4 件 — FALSE predicate 由来)

`EqualizingPermHypothesis` / `EqualizingSwapTargetHypothesis` は **機械検証済の偽** predicate。これらを hypothesis に取る含意は **vacuously-true な genuine 定理** であり、body は構造的に sorry 不要。

| line | decl 名 | staged の核 (1 行) | パターン | 移行後 class:slug | constructive recovery? |
|---:|---|---|---|---|---|
| 132 | `swapNormalizationHypothesis_of_equalizingPerm` | 偽 `EqualizingPermHypothesis` → `Hyp1` の含意、body genuine | C | (タグ削除のみ) | YES |
| 208 | `equalizingPerm_of_swapTarget` | 偽 `EqualizingSwapTargetHypothesis` → 偽 `EqualizingPermHypothesis` の含意 | C | (タグ削除のみ) | YES |
| 238 | `swapNormalizationHypothesis_of_swapTarget` | 上 2 つの合成 | C | (タグ削除のみ) | YES |
| 251 | `huffmanLength_optimal_via_equalizing_perm` | 偽 `EqualizingPermHypothesis` 経由で `huffmanLength_optimal_with_hypotheses` 呼出 | P (transitive) | (タグ削除のみ + transitive 散文) | candidate (transitive via `huffmanLength_optimal_with_hypotheses` Phase 2 retreat) |

### `HuffmanSwapStepChainBody.lean` (2 件)

| line | decl 名 | staged の核 (1 行) | パターン | 移行後 class:slug | constructive recovery? |
|---:|---|---|---|---|---|
| 343 | `huffmanLength_optimal_with_chain_combined` | triple → 2-way reduce + `huffmanLength_optimal_with_combined` 呼出 | C (transitive) | (タグ削除のみ + transitive 散文) | YES |
| 359 | `huffmanLength_optimal_via_chain_lift` | 2-way → triple lift + `huffmanLength_optimal_with_chain_combined` 呼出 | C (transitive) | (タグ削除のみ + transitive 散文) | YES |

### `HuffmanMergedIdentBody.lean` (2 件)

| line | decl 名 | staged の核 (1 行) | パターン | 移行後 class:slug | constructive recovery? |
|---:|---|---|---|---|---|
| 154 | `huffmanMergedIdentification_of_aux` | `MergedHuffmanAuxIdentHypothesis` → `HuffmanMergedIdentificationHypothesis` (measure 層を defeq + `initMultiset_mergedMeasure_eq` で discharge、body 完全証明) | P | `plan:huffman-strong-form-completion` | no (Hyp_aux を直接消費、ただし body は constructive で aux → Hyp2 は genuine) |
| 171 | `huffmanLength_optimal_with_swap_and_aux` | `MergedHuffmanAuxIdentHypothesis` 経由で `huffmanLength_optimal_with_hypotheses` 呼出 | P | `plan:huffman-strong-form-completion` | candidate (transitive) |

注: 154 の body は **genuine constructive** (`rw [initMultiset_mergedMeasure_eq Q a b hab]; exact h_aux Q hQ h_card ...`) で、`h_aux` 仮説を **load-bearing として消費する** が同時に **proof は閉じている**。これは pattern P (predicate consumer) であって sorry 化対象ではない、ただし `@audit:staged` タグが付いているのは「`MergedHuffmanAuxIdentHypothesis` が外部 hypothesis として未 discharge」という事情の遺存。Phase 1 で **タグ削除のみ + `@residual` 不要** にできる候補。Phase 0 inventory で auditor 確認対象。

### `HuffmanOptimality.lean` (2 件 + `@audit:closed-by-successor` 重畳)

| line | decl 名 | staged の核 (1 行) | パターン | 移行後 class:slug | constructive recovery? |
|---:|---|---|---|---|---|
| 778 | `huffmanLength_optimal_aux_with_hypotheses` (private) | weak form induction motor、`h_swap` + `h_ident` を strong induction の各 step で消費 | P | `plan:huffman-2hyp-vertical-reduction` (shared wall 経由で書換) | no (body は 200+ 行の non-trivial induction proof、Hyp1/Hyp2 を真に消費) |
| 1028 | `huffmanLength_optimal_with_hypotheses` | 上の public wrapper (`Fintype.card α = n` rfl 付け) | P | `plan:huffman-2hyp-vertical-reduction` (shared wall 経由で書換) | no |

両件とも `@audit:closed-by-successor(huffman-2hyp-vertical-reduction)` を併用。移行後は `@residual(plan:huffman-2hyp-vertical-reduction)` に**統合** (`closed-by-successor` は `audit-tags.md`「Deprecated」表で `@residual(plan:<slug>)` に置換規定済)。

**重要**: 778 / 1028 の body は `h_swap` / `h_ident` を消費するが、body 自身が 200+ 行の **genuine induction proof** (Cover-Thomas Theorem 5.8.1 standard proof の Lean 化) で、Phase 2.1 で `h_swap` / `h_ident` を引数から削除して shared wall (`swap_normalization_hypothesis_holds` / `huffman_merged_identification_hypothesis_holds`) で置換する **mechanical rewrite** で済む (body の構造は変えない、引数名置換のみ)。これは Hoeffding pilot にはなかった **「P → P-with-wall」変換** で、shared wall lemma の集約 (Approach §2) が前提条件。

### `HuffmanStrongForm.lean` (1 件)

| line | decl 名 | staged の核 (1 行) | パターン | 移行後 class:slug | constructive recovery? |
|---:|---|---|---|---|---|
| 175 | `huffmanLength_optimal_modulo_aux_ident` | Hyp1 discharged strong form、`MergedHuffmanAuxIdentHypothesis` を **唯一の load-bearing hypothesis** として受ける | P | `plan:huffman-strong-form-completion` (shared wall 経由で書換) | no |

docstring に既に「**`h_aux` は load-bearing — NOT a discharge / NOT trivial.**」と明記され、これは tier 4 legacy 散文の典型例。Phase 2.2 で shared wall 経由に書換、散文「NOT a discharge」は migration 後に削除 (= `@residual(plan:huffman-strong-form-completion)` タグが同じ意味を担う)。

### 集計 (パターン別)

verbatim 確認後の事前判定 (Phase 0 で auditor が refine):

- **C (constructive bridge、タグ削除のみ + transitive 散文)**: **8 件** = `HuffmanT1APPrimeBody.lean` 524 / 531 + `HuffmanSwapNormalizationBody.lean` 132 / 208 / 238 / 251 + `HuffmanSwapStepChainBody.lean` 343 / 359 (+ 候補 `HuffmanMergedIdentBody.lean:154` は genuine constructive なので C 入りも、Phase 0 で再判定)
- **P (load-bearing predicate consumer、Phase 2 で signature 改変 or shared wall 置換)**: **22 件** (15 - 2 C + 4 + 2 - 1 P→C 候補 + 2 + 1 = 22)。うち:
  - **Terminal declaration (shared wall 経由置換)**: 4 件 (`HuffmanOptimality.lean:778/:1028` + `HuffmanStrongForm.lean:175` + `HuffmanMergedIdentBody.lean:154` — 後者は P→C 候補)
  - **Witness extractor (Hyp 直接消費)**: 5 件 (`SwapNormalizationHypothesis_*_witness_*` 4 件 + `SwapNormalizationHypothesis_apply_witness` 1 件)
  - **Identification extractor**: 4 件 (`huffmanMergedIdentification_at_a` / `_at_other` / `_combined` / `_dichotomy`)
  - **Terminal wrapper (transitive via terminal declaration)**: 残り

→ Phase 1 で 8 件処理 (タグ削除のみ、新規 `sorry` 0 件)、Phase 1.5 で shared wall 5 件設置 (5 件の新規 `sorry`)、Phase 2.1 + 2.2 で 22 件処理 (declaration の body は shared wall に依存するため新規 `sorry` 0 件、ただし 1 件 = 178 行の induction motor body は再 verify 必要)。

## Phase 詳細

### Phase 0 — Inventory (verbatim refine) 📋

- [ ] **0.1** 本 plan §「在庫表」を実装 agent (or auditor) が `Read` で再確認、特に以下を verify:
  - `HuffmanMergedIdentBody.lean:154` `huffmanMergedIdentification_of_aux` が genuine constructive (= P→C 候補) かどうか
  - `HuffmanT1APPrimeBody.lean:524/:531` の field projection が **abbrev `And` の `.1` / `.2`** 同等で `:= h.1` / `:= h.2` の構造的書換だけで完結するか
  - `HuffmanSwapNormalizationBody.lean:132/:208/:238` が `EqualizingPermHypothesis` / `EqualizingSwapTargetHypothesis` (偽 predicate) を hypothesis に取る vacuously-true 含意であり、body が genuine な構造的書換のみで完結するか
- [ ] **0.2** Phase 1 / 1.5 / 2.x の Phase 配置を必要に応じて refine。本 plan §「在庫表」の P / C 分類を更新 (judgement log #1 で確定)。

**Phase 0 DoD**: 30 件の P / C 分類が judgement log #1 で確定。Phase 1 / 1.5 / 2.x の配置が固定。

**proof-log**: no (verbatim 確認 + 表更新のみ)。

### Phase 1 — Cleanup pass (パターン C、新規 sorry なし) 📋

- [ ] **1.1** `HuffmanT1APPrimeBody.lean` Phase 1 候補 2 件 (`huffmanCombinedHypothesis_swap` / `huffmanCombinedHypothesis_ident`) の `@audit:staged` 削除。
  - `HuffmanCombinedHypothesis` は `abbrev := Hyp1 ∧ Hyp2` で `.1` / `.2` の field projection のみ。signature 改変不要、body 不変。
  - `lake env lean Common2026/Shannon/HuffmanT1APPrimeBody.lean` で type-check done 確認。
- [ ] **1.2** `HuffmanSwapNormalizationBody.lean` Phase 1 候補 3-4 件 (`swapNormalizationHypothesis_of_equalizingPerm` / `equalizingPerm_of_swapTarget` / `swapNormalizationHypothesis_of_swapTarget` / `huffmanLength_optimal_via_equalizing_perm`) の `@audit:staged` 削除。
  - 偽 predicate (`EqualizingPermHypothesis` / `EqualizingSwapTargetHypothesis`) を仮説に取る vacuously-true 含意。body は構造的に sorry 不要。
  - 251 (`huffmanLength_optimal_via_equalizing_perm`) は body 内で `huffmanLength_optimal_with_hypotheses` を呼ぶため transitive sorry が Phase 2 完了後に生じる、docstring 散文で明示 (Pilot Pattern C)。
- [ ] **1.3** `HuffmanSwapStepChainBody.lean` Phase 1 候補 2 件 (`huffmanLength_optimal_with_chain_combined` / `huffmanLength_optimal_via_chain_lift`) の `@audit:staged` 削除。
  - chain hypothesis を捨てて 2-way reduce or lift して `huffmanLength_optimal_with_combined` を呼ぶ slim wrapper。body 不変、transitive sorry が Phase 2 完了後に生じる、docstring 散文で明示。
- [ ] **1.4** Phase 0 で P→C 判定された候補 (推定: `HuffmanMergedIdentBody.lean:154` `huffmanMergedIdentification_of_aux`) があれば Phase 1 に追加処理。

**Phase 1 DoD**: 上記 7-8 件で `@audit:staged` 0 件、新規 `sorry` 0 件、`lake env lean` 各 file 0 errors。

**proof-log**: no (mechanical tag removal、interesting なし)。

### Phase 1.5 — Shared wall lemma 集約 📋

実装 agent が以下 2 案から選択 (両方 OK、各 1 セッションで完走見込み):

**案 A — 新規 file `Common2026/Shannon/HuffmanWalls.lean`** を Write:

```lean
import Common2026.Shannon.HuffmanOptimality
import Common2026.Shannon.HuffmanMergedIdentBody

namespace InformationTheory.Shannon.Huffman

universe u

/-- **Wall lemma (Hyp1)**: swap normalization の存在主張。
@residual(plan:huffman-2hyp-vertical-reduction) -/
theorem swap_normalization_hypothesis_holds : SwapNormalizationHypothesis.{u} := by
  sorry

/-- **Wall lemma (Hyp2)**: huffmanLength identification on mergedMeasure。
@residual(plan:huffman-2hyp-vertical-reduction) -/
theorem huffman_merged_identification_hypothesis_holds :
    HuffmanMergedIdentificationHypothesis.{u} := by
  sorry

/-- **Wall lemma (combined)**: 上記 2 つの conjunction、abbrev wrapper。
@residual(plan:huffman-2hyp-vertical-reduction) -/
theorem huffman_combined_hypothesis_holds : HuffmanCombinedHypothesis.{u} :=
  ⟨swap_normalization_hypothesis_holds, huffman_merged_identification_hypothesis_holds⟩

/-- **Wall lemma (chain combined)**: 上 + trivially-true chain hypothesis。
@residual(plan:huffman-2hyp-vertical-reduction) -/
theorem huffman_chain_combined_hypothesis_holds : HuffmanChainCombinedHypothesis.{u} :=
  ⟨swap_normalization_hypothesis_holds, huffman_merged_identification_hypothesis_holds,
   swapStepLeChainHypothesis_holds⟩

/-- **Wall lemma (aux ident)**: merged measure 上の huffmanLengthAux 識別の primitive 形。
@residual(plan:huffman-strong-form-completion) -/
theorem merged_huffman_aux_ident_hypothesis_holds : MergedHuffmanAuxIdentHypothesis.{u} := by
  sorry

end InformationTheory.Shannon.Huffman
```

`Common2026.lean` に `import Common2026.Shannon.HuffmanWalls` 追加。3 件の direct sorry + 2 件の constructive composition で計 5 hypothesis predicate を集約。

**案 B — Per-file `*_holds`**: 各 hypothesis predicate の **定義 file の直後** (= `HuffmanOptimality.lean` 内 `Hyp1` / `Hyp2` 定義の直後、`HuffmanMergedIdentBody.lean` 内 `MergedHuffmanAuxIdentHypothesis` 定義の直後) に `*_holds` を追加。`Common2026.lean` の import 不変。

**判断**: 案 A を default、案 B は実装 agent が `HuffmanOptimality.lean` の規模 (1042 行) を考慮して file 内 augmentation を避けたい場合に選択可。

- [ ] **1.5.1** 案 A or 案 B を選択、shared wall lemma 5 件を追加 (3 件 direct sorry + 2 件 constructive composition)。
- [ ] **1.5.2** 各 sorry に `@residual(plan:huffman-2hyp-vertical-reduction)` (or `huffman-strong-form-completion` for aux-ident) を付与。
- [ ] **1.5.3** `lake env lean Common2026/Shannon/HuffmanWalls.lean` (or 追加先 file) で type-check done 確認。

**Phase 1.5 DoD**: 5 hypothesis predicate に `*_holds` lemma が対応、各々 `@residual` 付き sorry を 3 件保有 (2 件は constructive composition で sorry 不要)。

**proof-log**: no (集約は mechanical)。

### Phase 1.6 — honesty-auditor #1 📋

- [ ] **1.6.1** Phase 1 + Phase 1.5 全件 (7-8 + 5 = ~13 件 + 5 predicate) について `honesty-auditor` agent を起動。verdict 確認後 commit。
- [ ] **1.6.2** verdict が `ok` 多数 + `questionable` で散文 refine 提案あれば即時適用。`defect` の場合は当該 declaration を撤回 or 修正。
- [ ] **1.6.3** Phase 1 / 1.5 commit を `Phase 1 V/C+wall cleanup` 1 つに squash 可 (orchestrator 判断)。

**Phase 1.6 DoD**: Phase 1 + Phase 1.5 全件で auditor verdict `defect 0`。

### Phase 2.1 — Terminal declaration retreat (shared wall 経由置換) 📋

- [ ] **2.1.1** `HuffmanOptimality.lean:1028` `huffmanLength_optimal_with_hypotheses` の signature から `h_swap` / `h_ident` 引数を削除、body を:
  ```lean
  huffmanLength_optimal_aux_with_hypotheses (Fintype.card α)
    swap_normalization_hypothesis_holds huffman_merged_identification_hypothesis_holds
    P hP l hl_pos hl_kraft rfl
  ```
  に書換。docstring 末尾の `@audit:staged(huffman-2hyp)` + `@audit:closed-by-successor(huffman-2hyp-vertical-reduction)` を `@residual(plan:huffman-2hyp-vertical-reduction)` 1 件に置換。signature の `(h_swap : SwapNormalizationHypothesis.{u})` / `(h_ident : HuffmanMergedIdentificationHypothesis.{u})` 削除。
- [ ] **2.1.2** `HuffmanOptimality.lean:778` `huffmanLength_optimal_aux_with_hypotheses` (private) も同様に signature 削除 + body 内の `h_swap` / `h_ident` 参照を shared wall に置換。body の 200+ 行 induction proof は構造不変、`h_swap` → `swap_normalization_hypothesis_holds` / `h_ident` → `huffman_merged_identification_hypothesis_holds` の **名前置換のみ**。
- [ ] **2.1.3** `HuffmanStrongForm.lean:175` `huffmanLength_optimal_modulo_aux_ident` の signature から `h_aux` 削除、body 内の `huffmanMergedIdentification_of_aux h_aux` を `huffmanMergedIdentification_of_aux merged_huffman_aux_ident_hypothesis_holds` に置換。docstring の散文「**`h_aux` は load-bearing — NOT a discharge / NOT trivial.**」(166-173 行) を削除 (`@residual(plan:huffman-strong-form-completion)` がその意味を担う)。
- [ ] **2.1.4** `HuffmanMergedIdentBody.lean:171` `huffmanLength_optimal_with_swap_and_aux` も同様に shared wall 経由に書換 (`h_swap` + `h_aux` 削除)。
- [ ] **2.1.5** Phase 2.1 完了後、CLAUDE.md「After upstream edits」に従い `lake build Common2026.Shannon.HuffmanOptimality` + `Common2026.Shannon.HuffmanStrongForm` + `Common2026.Shannon.HuffmanMergedIdentBody` の **olean refresh** (Pilot Pattern A 対策)。dependent file (`HuffmanT1APPrimePartial.lean` / `HuffmanT1APPrimeBody.lean` / `HuffmanSwapStepChainBody.lean` / `HuffmanSwapNormalizationBody.lean`) を `lake env lean` で再 verify。

**Phase 2.1 DoD**: terminal declaration 4 件で signature 改変 + body shared wall 経由、`@audit:staged` 0 件、`@residual(plan:...)` 4 件、`lake env lean` 各 file 0 errors (新規 `sorry` 発生は **Phase 1.5 で設置済の shared wall に集約済**、本 Phase で新規 sorry 0 件)。

**proof-log**: yes (`docs/shannon/proof-log-huffman-sorry-migration-phase2-1.md`)。理由: `huffmanLength_optimal_aux_with_hypotheses` の body 200+ 行 rewrite は引数名置換だけだが、Lean の binder scoping / induction tactic の generalize で意外な type error が出る可能性、判断記録を残す。

### Phase 2.2 — Upstream wrapper retreat (transitive or direct retreat) 📋

- [ ] **2.2.1** `HuffmanT1APPrimeBody.lean` の hypothesis-extracting wrapper 13 件:
  - **Identification extractor 4 件** (157 / 178 / 200 / 224): signature から `h_ident` 削除 → shared wall 経由置換 (`huffman_merged_identification_hypothesis_holds`)、body 不変。
  - **Witness extractor 5 件** (378 / 400 / 419 / 439 / 459): signature から `h_swap` 削除 → shared wall 経由置換 (`swap_normalization_hypothesis_holds`)、body 不変。
  - **Terminal wrapper 4 件** (280 / 297 / 538 / 608): signature から hypothesis 引数削除 → shared wall 経由置換、body 不変。
- [ ] **2.2.2** `HuffmanT1APPrimePartial.lean` の partial wrapper 4 件 (597 / 613 / 839 / 854): 同様に signature 改変 + body shared wall 経由。
- [ ] **2.2.3** Phase 1 で `@audit:staged` 削除のみ済の wrapper 3-4 件 (`HuffmanSwapNormalizationBody.lean:251` / `HuffmanSwapStepChainBody.lean:343/:359`) の body が **transitive sorry** に変わったかを確認 (Phase 2.1 完了で `huffmanLength_optimal_with_hypotheses` が shared wall 依存になったため)。docstring 散文で transitive 性を明示 (Pilot Pattern C):
  ```
  Transitive `sorry` via `huffmanLength_optimal_with_hypotheses` (Phase 2.1
  retreat to shared wall `swap_normalization_hypothesis_holds`
  / `huffman_merged_identification_hypothesis_holds`). No `@residual` tag —
  closure belongs to the wall lemmas.
  ```
- [ ] **2.2.4** olean refresh (`lake build Common2026.Shannon.HuffmanT1APPrimeBody` / `HuffmanT1APPrimePartial` / `HuffmanSwapStepChainBody` / `HuffmanSwapNormalizationBody`) + dependent 再 verify。

**Phase 2.2 DoD**: 22 件で signature 改変 (hypothesis 削除) + body shared wall 経由、`@audit:staged` 0 件、`@residual(plan:...)` 17-18 件 (Phase 2.1 + 2.2 合算)、`lake env lean` 各 file 0 errors。新規 sorry は Phase 1.5 の wall に集約済。

**proof-log**: yes (`docs/shannon/proof-log-huffman-sorry-migration-phase2-2.md`)。理由: 22 件の機械的 rewrite で名前 collision (`HuffmanCombinedHypothesis.{u}` の universe variable + `[Fintype β]` 等の instance 引数の order 依存) が頻発する可能性、判断記録を残す。

### Phase 2.3 — Predicate retract-candidate (5 hypothesis abbrev) 📋

- [ ] **2.3.1** Phase 2.1 / 2.2 完了後、5 hypothesis predicate の利用者を `rg -n 'SwapNormalizationHypothesis|HuffmanMergedIdentificationHypothesis|HuffmanCombinedHypothesis|HuffmanChainCombinedHypothesis|MergedHuffmanAuxIdentHypothesis' Common2026/` で再確認。
- [ ] **2.3.2** **依存ゼロ** (= 全 consumer が shared wall 経由に書換済) の predicate には `@audit:retract-candidate(load-bearing-predicate)` を docstring 末尾に付与 (削除はしない、後続 plan 完遂時の interface 互換用)。
- [ ] **2.3.3** **依然依存あり** (= shared wall 経由でない consumer が残存) の predicate は「未決事項」セクション #1 参照 → user 判断仰ぐ。
- [ ] **2.3.4** Pilot Pattern E (extract-only consumer 見落とし) に倣い、docstring に「all *hypothesis-form load-bearing* consumers were retreated to shared wall. N extract-only consumers remain (pass-through, no load-bearing claim injected): ...」と明示。

**Phase 2.3 DoD**: 5 hypothesis predicate が `@audit:retract-candidate(load-bearing-predicate)` または「未決」マーク付き。

### Phase 2.4 — honesty-auditor #2 📋

- [ ] **2.4.1** Phase 2.1 / 2.2 / 2.3 全件 (22 件 + 5 predicate) について `honesty-auditor` agent を起動。verdict 確認後 commit。
- [ ] **2.4.2** verdict が `defect` の場合は当該 declaration を撤回 or 修正 (sorry-based に書換、Phase 2.x の rewrite 失敗)。`questionable` は docstring refine で対応。

**Phase 2.4 DoD**: Phase 2 全件で auditor verdict `defect 0`。

### Phase V — verify + plan の集約 📋

- [ ] **V.1** 全 13 file (Huffman.lean 含む) で `lake env lean` 確認。Phase 2 で signature 改変があったため dependent file の olean refresh が必要 (CLAUDE.md「After upstream edits」参照、Pilot Pattern A)。
- [ ] **V.2** 集計コマンド実行:
  ```bash
  rg '@audit:staged' Common2026/Shannon/Huffman*.lean | wc -l                            # = 0
  rg '@audit:closed-by-successor' Common2026/Shannon/Huffman*.lean | wc -l               # = 0
  rg '@residual\(plan:huffman-2hyp-vertical-reduction\)' Common2026/Shannon/Huffman*.lean | wc -l
  rg '@residual\(plan:huffman-strong-form-completion\)' Common2026/Shannon/Huffman*.lean | wc -l
  rg -nw 'sorry' Common2026/Shannon/Huffman*.lean                                        # 期待値: 3 (shared wall direct sorry)
  rg '@audit:retract-candidate' Common2026/Shannon/Huffman*.lean
  ```
- [ ] **V.3** `huffman-moonshot-plan.md` / `huffman-2hyp-vertical-reduction-plan.md` / `huffman-strong-form-completion-plan.md` 冒頭 banner 更新 (sorry-based 移行完了の追記)。
- [ ] **V.4** Pilot 知見を `docs/audit/sorry-migration-runbook.md` または `.claude/handoff-sorry-migration.md` に反映:
  - **`@audit:staged` migration recipe**: slug が Mathlib 壁ではなく plan slug の場合は class `plan:` を採用、staged reason は docstring 散文で保存 (削除しない)。
  - **`@audit:closed-by-successor` 重畳タグ**: 同一 declaration で `@audit:staged(<slug>)` と `@audit:closed-by-successor(<slug>)` が併用されている場合は `@residual(plan:<slug>)` 1 件に統合 (`audit-tags.md`「Deprecated」表に従う)。
  - **shared wall lemma 集約**: Hoeffding と異なり Huffman は集約方式 (案 A 新規 file or 案 B per-file augmentation)。集約方針は wall の数 + consumer 数 + file 跨ぎ の組合せで判断。
  - **false-hypothesis 起源の vacuously-true wrapper**: `EqualizingPermHypothesis` / `EqualizingSwapTargetHypothesis` のように偽 predicate からの含意 wrapper は **タグ削除のみ** で P でなく C 扱い (predicate 自身は `@audit:defect(false-hypothesis)` 候補だが本 plan scope 外、未決事項 #4 で別途扱う)。

**Phase V DoD**: 全 13 file `lake env lean` 0 errors、`@audit:staged` / `@audit:closed-by-successor` / 散文「load-bearing — NOT a discharge」が 0 件、shared wall 由来の `sorry` 3 件 (Hyp1 / Hyp2 / Hyp_aux) のみ。

## 撤退ライン

### L-MIG-1 (constructive recovery 候補が auditor で load-bearing 判定された場合)

Phase 1 の 8 件 (constructive C 候補) について auditor が「実際は P (load-bearing) で transitive ではない」と判定したら、それらを Phase 2 相当の処理 (body `sorry` + `@residual(plan:huffman-2hyp-vertical-reduction)`、signature の hypothesis 引数は削除 or shared wall 置換) に降格。Phase 1 のタグ削除のみは undo。

特に **`HuffmanSwapNormalizationBody.lean:132/:208/:238`** の vacuously-true 含意は「偽前提 → 結論」の含意で genuine な定理だが、auditor が「実質的に何も主張していない (= name laundering 候補)」と判定する可能性。その場合は Phase 1 ではなく Phase 2.x で扱い、`@residual(defect:false-hypothesis)` 付与を検討。

### L-MIG-2 (Phase 2.1 で `huffmanLength_optimal_aux_with_hypotheses` body の rewrite が壊れる)

`HuffmanOptimality.lean:778` の private theorem は 200+ 行の non-trivial induction proof。body 内で `h_swap` / `h_ident` を多数回参照する `Nat.strong_induction_on generalizing` の context で、引数名を shared wall lemma 名 (`swap_normalization_hypothesis_holds` 等) に置換する mechanical rewrite が、Lean の binder scoping / universe variable で型 error を起こす可能性 (`SwapNormalizationHypothesis.{u}` の universe annotation の一致が必要)。

**発動条件**: Phase 2.1.2 で `lake env lean Common2026/Shannon/HuffmanOptimality.lean` が rewrite 後に **3 ターン以上 error 残**。
**対応**: Phase 2.1.2 を pause、`huffmanLength_optimal_aux_with_hypotheses` の signature を **「Hyp1 / Hyp2 残存」のまま** にし、`huffmanLength_optimal_with_hypotheses` (line 1029、public wrapper) のみ shared wall 経由に書換。private 側は本 plan scope 外として handoff、後続 session で再 attempt。

### L-MIG-3 (Phase 2.2 で predicate 削除時に大量 caller drift)

5 hypothesis predicate の使用箇所を Phase 2.3 で再確認後、依存先が **想定外に多い** (例: テストファイル / docs / 他 family の file から hypothesis 形で参照) なら、未決事項 #1 を user に escalate して **Phase 2.3 を中断** (Phase 2.1 / 2.2 は close 可)。

**推定 caller 数**: `rg -c 'SwapNormalizationHypothesis' Common2026/` で本 plan 起草時点の依存数を 5+ file (= `HuffmanOptimality.lean` 定義 + 4-5 consumer file) と推定。Phase 2.2 完了後に再計測。

### L-MIG-4 (`huffman-2hyp-vertical-reduction-plan` 完遂と方向衝突)

本 plan の `@residual(plan:huffman-2hyp-vertical-reduction)` 化が、後続 plan (`huffman-2hyp-vertical-reduction-plan.md`) の completion 設計と衝突 (例: 後続 plan が hypothesis を residual に押し出した signature を closure の入口として使う設計) した場合、本 plan は Phase 2 を pause、後続 plan 側の signature を変更しない範囲で predicate を residual 化する別レシピを検討。

特に **`huffmanLength_optimal_aux_with_hypotheses` (private induction motor) の signature を shared wall 経由にする** ことが後続 plan 完遂時の interface 変更を強いる可能性。Phase 2.1.2 着手前に `huffman-2hyp-vertical-reduction-plan.md` を確認、interface 整合性を auditor 経由で確認。

### L-MIG-5 (pilot scope を縮める)

Phase 2 が 1 セッションで完走しない / honesty-auditor が DEFECT を多発させる場合、`HuffmanT1APPrimeBody.lean` 15 件のみで pilot を close し、`HuffmanT1APPrimePartial.lean` / `HuffmanSwapNormalizationBody.lean` / `HuffmanSwapStepChainBody.lean` / `HuffmanMergedIdentBody.lean` / `HuffmanOptimality.lean` / `HuffmanStrongForm.lean` は後続 family sweep として別 plan に分離。

Hoeffding pilot (L-MIG-4 同条件) と異なり、Huffman は **30 件 + 5 predicate + 13 file** で 1 セッション完走難易度が高い。Phase 2.1 単独完走 → Phase 2.2 別セッション、の split を default 計画とする。

## 未決事項

1. **5 hypothesis predicate の deprecate 方針**: Phase 2 で全 consumer が shared wall 経由になった場合、predicate 定義は (a) 削除する / (b) `@audit:retract-candidate(load-bearing-predicate)` 付きで残す / (c) public API として残し続ける、のどれを選ぶか。本 plan のデフォルトは (b)。user の確認待ち (`@audit:superseded-by` 候補が無いため、削除より retract-candidate 推奨)。**Auditor 判定対象**。

2. **shared wall lemma の配置 (案 A 新規 file vs 案 B per-file augmentation)**: 本 plan のデフォルトは案 A (`Common2026/Shannon/HuffmanWalls.lean` 新規)。実装 agent が `HuffmanOptimality.lean` (1042 行) を更に膨らませたくない場合は案 A、Huffman 系全体の import graph を簡素に保ちたい場合は案 B (per-file)。**実装 agent 判断**。

3. **proof done を本 plan で目指さない方針の明示確認**: 本 plan の DoD は **type-check done** のみ。Hyp1 (swap normalization) と Hyp2 (huffman merged identification) の analytical closure は **未着手のまま**で本 plan は close する。`huffman-moonshot-plan.md` の Phase 4-5 scope-out 状態は変えない。user の合意確認のため明示。

4. **`EqualizingPermHypothesis` / `EqualizingSwapTargetHypothesis` の false-hypothesis defect 処理**: 両 predicate は **機械検証済の偽** と既に明示されている。これらは tier 5 (defect) 寄りで、`@audit:defect(false-hypothesis)` 付与候補。本 plan は scope 外として touch しない方針 (predicate 自身は consumer wrapper 4 件の signature に残るため)、ただし当該 predicate の docstring に既存の honesty alert 散文を保存し、後続 family sweep (= 別 plan) で扱う。**Auditor 判定対象**。

5. **`HuffmanMergedIdentBody.lean:154` `huffmanMergedIdentification_of_aux` の P / C 判定**: docstring + body 1-3 行から「`MergedHuffmanAuxIdentHypothesis` を load-bearing として消費するが body は constructive で aux → Hyp2 は genuine」と判定したが、auditor 経由で「`h_aux` 受取自体は Hyp_aux が closure 待ちで実質 load-bearing transitively」と判定される可能性。Phase 0 inventory で判定確定、本 plan §「在庫表」を update。**Auditor 判定対象**。

## 判断ログ

書く頻度: 方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 plan 起草**: lean-planner agent (本セッション) が `Common2026/Shannon/Huffman*.lean` 13 file の `@audit:staged` 30 件 + `@audit:closed-by-successor` 2 件 (重畳) を verbatim 読込で per-declaration 分類。「既存 sorry 2 件」(handoff の brief 記述) は Pattern D による誤計数で **実数 0 件** であることを `rg -nw 'sorry'` で確認 (2 hit は docstring 内の文字列 ``sorry`` / `0 sorry`)。pilot 戦略を「file 単位 sweep + shared wall 集約あり (5 hypothesis predicate のうち 3 件で direct sorry)」に確定。Approach の 2 軸決定 (Hoeffding と異なり集約あり) + パターン S → P/C resolve の判定根拠を在庫表で示した。

   `@audit:staged` migration recipe の主要発見:
   - slug は **Mathlib 壁ではなく plan slug** (`huffman-2hyp` = `huffman-2hyp-vertical-reduction-plan` 略形、`huffman-aux-ident` = `huffman-strong-form-completion-plan` 略形)。class は `plan:` で揃え、`audit-tags.md`「Wall name register」拡張は本 plan で不要。
   - staged の reason (元の壁) は docstring 散文で保存 (削除しない)、新タグ `@residual(plan:...)` がその意味を引き継ぐ。
   - `@audit:closed-by-successor` との重畳は `@residual(plan:<slug>)` 1 件に統合 (`audit-tags.md`「Deprecated」表に従う)。
   - `EqualizingPermHypothesis` / `EqualizingSwapTargetHypothesis` の false-hypothesis defect は **本 plan scope 外**として handoff、未決事項 #4 で別 plan に分離。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
