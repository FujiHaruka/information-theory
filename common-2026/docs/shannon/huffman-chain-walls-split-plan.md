# Shannon: Huffman `HuffmanChainWalls.lean` 分離による上流 wrapper 完全 Tier 2 化計画

> **Parent**: [`huffman-sorry-migration-plan.md`](huffman-sorry-migration-plan.md)
> 判断ログ #2-#4 (L-MIG-4 拡張発動、import cycle 回避で全 21 wrapper の signature 改変断念) の **構造的 fix**。
> 親 plan は **type-check done** を達成済 (load-bearing predicate hypothesis 21 件残置 + slug 統一)。
> 本 plan は親 plan の **honesty defect (Tier 5 相当の load-bearing hypothesis bundling)** を、
> import 構造の再編 (= `HuffmanChainWalls.lean` を `HuffmanOptimality` の **上流** に移動) で
> 解消し、21 wrapper を **完全 Tier 2 (sorry + `@residual(<class>:<slug>)`)** に降ろす。

## Context

### 1. 親 plan で L-MIG-4 拡張発動した経緯 (verbatim 引用)

`docs/shannon/huffman-sorry-migration-plan.md` 判断ログ #2 (verbatim):

> 2. **2026-05-25 L-MIG-4 発動 (Phase 2.1.1 / 2.1.2 skip, `HuffmanOptimality.lean:778/:1028` body・signature 不変)**: lean-implementer agent が Phase 0 verbatim 確認中に発見した import cycle:
>    - `HuffmanOptimality.lean` (`huffmanLength_optimal_with_hypotheses` 等定義) ← `HuffmanStrongForm.lean` (`swap_normalization_proof` constructive proof) ← `HuffmanSwapNormCompletion.lean` ← ...
>    - 計画 Phase 2.1.1/2.1.2 は `HuffmanOptimality.lean:778/:1028` body から `HuffmanWalls.swap_normalization_hypothesis_holds` を呼ぶことを要求するが、`HuffmanWalls.lean` を新規 file として作る場合 (案 A) は `HuffmanWalls.lean` が `HuffmanStrongForm.lean` (constructive Hyp1 source) を import する必要があり、それを `HuffmanOptimality.lean` から import すると **循環**。
>    - 案 B per-file augmentation で `HuffmanOptimality.lean` 内に直接 `swap_normalization_hypothesis_holds` を sorry-base で追加する解は循環なしだが、既存 constructive proof `swap_normalization_proof` (`HuffmanStrongForm.lean:144`) を **未使用**にする = Pattern B (不要 sorry の作成) defect。
>    - 判断: **L-MIG-4 発動**。

判断ログ #3 (verbatim):

> 3. **2026-05-25 L-MIG-4 拡張発動 (Phase 2.1.3 / 2.1.4 も skip, `HuffmanStrongForm.lean:175` / `HuffmanMergedIdentBody.lean:171` signature 不変)**: 判断ログ #2 と同じ import cycle 問題が `HuffmanStrongForm.lean` / `HuffmanMergedIdentBody.lean` にも該当することを実装中に発見:
>    - `HuffmanWalls.lean → HuffmanStrongForm.lean` の import chain、および `HuffmanStrongForm.lean → HuffmanMergedIdentBody.lean → HuffmanOptimality.lean` の chain で、`HuffmanWalls.lean` を `HuffmanStrongForm.lean` / `HuffmanMergedIdentBody.lean` から import すると循環。

判断ログ #4 (verbatim、Phase 2.2 も skip):

> 4. **2026-05-25 L-MIG-4 さらに拡張 (Phase 2.2 も実質「タグ更新のみ」、`HuffmanT1APPrimeBody` / `HuffmanT1APPrimePartial` 17 件 signature 不変)**: Phase 2.2 着手時に import graph を再 verify:
>    - `HuffmanWalls.lean` の deps: `HuffmanStrongForm` + `HuffmanSwapStepChainBody` (chain combined wall を constructive composition で組むため `SwapStepLeChainHypothesis_holds` が必要)
>    - `HuffmanSwapStepChainBody.lean` の deps: `HuffmanOptimality` + `HuffmanT1APPrimePartial` + `HuffmanT1APPrimeBody`
>    - したがって `HuffmanT1APPrimeBody.lean` / `HuffmanT1APPrimePartial.lean` / `HuffmanSwapStepChainBody.lean` から `HuffmanWalls.lean` を import すると **循環**。

### 2. 21 wrapper の honesty defect 構造 (honesty-auditor verdict 抜粋)

audit agent `a961ba4e002bd9f28` (今 session、Huffman sorry-migration audit) verdict 抜粋:

> 上流 4 件 (`HuffmanOptimality.lean:804/:1058` + `HuffmanStrongForm.lean:183` + `HuffmanMergedIdentBody.lean:192`)、下流 17 件 (`HuffmanT1APPrimeBody.lean` 13 件 + `HuffmanT1APPrimePartial.lean` 4 件) で **`h_swap` / `h_ident` / `h_aux` の load-bearing hypothesis 引数が signature に残置**。docstring の `@residual(plan:huffman-2hyp-vertical-reduction)` 単独タグでは `Common2026/CLAUDE.md`「検証の誠実性」の **load-bearing hypothesis bundling = Tier 5 defect** に該当 (核心が `h_swap` / `h_ident` / `h_aux` という predicate hypothesis に bundling されており、body は機械的展開だけ)。Tier 2 (sorry + `@residual`) に降ろすには signature 改変が必須だが、親 plan は import cycle 制約で断念した。本構造は実質的に「`@audit:staged` から名前を変えた tier 4 staged」であり、改善でなく語彙の置換にとどまる。

### 3. 現 `HuffmanWalls.lean` の import chain (verbatim)

```
HuffmanWalls.lean (line 1-2)
  import Common2026.Shannon.HuffmanStrongForm
  import Common2026.Shannon.HuffmanSwapStepChainBody

HuffmanStrongForm.lean (line 1-3)
  import Common2026.Shannon.HuffmanOptimality           ← HuffmanOptimality は上流
  import Common2026.Shannon.HuffmanSwapNormCompletion
  import Common2026.Shannon.HuffmanMergedIdentBody

HuffmanSwapStepChainBody.lean (line 1-4)
  import Common2026.Shannon.HuffmanOptimality           ← 同上
  import Common2026.Shannon.HuffmanT1APPrimePartial
  import Common2026.Shannon.HuffmanT1APPrimeBody

HuffmanOptimality.lean (line 1-8)
  import Mathlib.* ; import Common2026.Shannon.Huffman  ← HuffmanWalls 非依存
```

したがって現 chain は

```
Huffman (基礎) → HuffmanOptimality → {HuffmanMergedIdentBody, HuffmanT1APPrimePartial, HuffmanSwapNormalizationBody, ...}
                                 ↓                                       ↓
                          HuffmanT1APPrimeBody                  HuffmanStrongForm
                                 ↓                                       ↓
                          HuffmanSwapStepChainBody                       ↓
                                 └─────────────────────┬─────────────────┘
                                                       ↓
                                              HuffmanWalls (最下流、現状)
```

= `HuffmanWalls` が **下流端**にあるため、上流 wrapper (`HuffmanOptimality` / `HuffmanStrongForm` / `HuffmanMergedIdentBody`) は `HuffmanWalls` を import できない (循環)。

### 4. `HuffmanChainWalls.lean` 分離が解消する依存方向

新規 file **`HuffmanChainWalls.lean`** を **`HuffmanOptimality` の上流** に置く。具体的には:

```
Huffman (基礎)
  ↓
HuffmanChainWalls (新規)    ← Hyp1 / Hyp2 / Hyp_aux / Combined / ChainCombined の 5 predicate **定義** + 各 wall lemma (sorry / shared) を集約
  ↓
HuffmanOptimality           ← Hyp1 / Hyp2 predicate を **使う側** (定義しない)
  ↓
{HuffmanMergedIdentBody, HuffmanT1APPrimePartial, HuffmanSwapNormalizationBody, ...}
  ↓
HuffmanT1APPrimeBody        ← HuffmanCombinedHypothesis を **使う側** (定義しない)
  ↓
HuffmanSwapStepChainBody    ← HuffmanChainCombinedHypothesis を **使う側** (定義しない)
  ↓
HuffmanStrongForm
  ↓
(HuffmanWalls は本 plan で削除 or 縮退、後述)
```

これにより:

- `HuffmanOptimality.lean:1058` `huffmanLength_optimal_with_hypotheses` の body から
  `HuffmanChainWalls.swap_normalization_hypothesis_holds` を呼べる (両者は同じ namespace / 同じ predicate を参照、上流 → 下流の方向)。
- `HuffmanStrongForm.lean:183` `huffmanLength_optimal_modulo_aux_ident` も同様。
- 下流 17 件はそもそも上流 (`HuffmanOptimality` 経由) で `HuffmanChainWalls` の predicate に到達できるので、wall lemma を呼ぶことも自然に可能。

**ただし** Hyp1 wall (`swap_normalization_proof` を alias する constructive 経路) の供給元は `HuffmanStrongForm.lean:149` 内にあり、これは `HuffmanChainWalls` の **下流**に位置するため、Hyp1 wall を `HuffmanChainWalls` 内で constructive alias として書けない (循環)。よって **Phase 1 段階では Hyp1 wall も sorry 化**し、後に `HuffmanStrongForm` 側で `swap_normalization_hypothesis_holds = swap_normalization_proof` 等式 lemma を補って transitive に閉じる別 plan に委ねる (撤退ライン L-MIG-CW-3 参照)。

## Approach

### 戦略の核

**`HuffmanChainWalls.lean` を `HuffmanOptimality` の上流に挿入し、5 predicate を **定義位置ごと**移動 (= 上流に「持ち上げる」) する**。これにより上流 wrapper が wall lemma を呼べる = 21 wrapper 全件の signature から load-bearing hypothesis を削除できる。

`HuffmanWalls.lean` (現状、下流端) は本 plan で **predicate 定義を持たない pure wall lemma file** から、**完全に削除可能** (役割は `HuffmanChainWalls.lean` に統合)。ただし削除は最終 Phase まで遅延し、incidental に行う (L-MIG-CW-3 で safety 担保)。

### shared wall lemma の早期挿入戦略

`HuffmanChainWalls.lean` には **predicate 定義 + 各 wall lemma (sorry, Tier 2)** を両方収容する。各 wall lemma は当面 **direct sorry + `@residual(plan:huffman-2hyp-vertical-reduction)` (or `plan:huffman-strong-form-completion`)** で start し、Hyp1 wall については後続別 plan で `swap_normalization_proof` への constructive alias 化を待つ (本 plan 内では sorry のまま)。

理由:

- 親 plan で `HuffmanWalls.lean` (下流端) の `swap_normalization_hypothesis_holds` は `swap_normalization_proof` direct alias で constructive (sorry なし) だったが、本 plan で `HuffmanChainWalls` を上流に移すと `swap_normalization_proof` 定義 (= `HuffmanStrongForm.lean:149`) に **依存不能** (下流) → sorry に降格。
- これは見かけ上 honesty 後退 (Tier 1 alias → Tier 2 sorry) だが、引き換えに **下流 + 上流 21 wrapper が Tier 2 化** され、global honesty bar は向上 (Tier 5 load-bearing hyp × 21 → Tier 2 sorry × 21 + Tier 2 sorry × 3 wall = 24 件、ただし wall は集約済で実質 5 件分の closure 責任に縮約)。
- Hyp1 wall の constructive 化は別 plan (`huffman-2hyp-vertical-reduction-plan` 完遂時に併せて transitive 化、または `HuffmanStrongForm.lean` 末尾で `swap_normalization_hypothesis_holds_eq_proof : swap_normalization_hypothesis_holds = swap_normalization_proof := rfl` のような bridge lemma を提供) として handoff。

### predicate 移動

| predicate | 現定義位置 | 移動先 | consumer file での扱い |
|---|---|---|---|
| `SwapNormalizationHypothesis` | `HuffmanOptimality.lean` (近 line 759) | `HuffmanChainWalls.lean` | `HuffmanOptimality.lean` 等は `HuffmanChainWalls` を import して名前空間 `InformationTheory.Shannon.Huffman.SwapNormalizationHypothesis` で参照 |
| `HuffmanMergedIdentificationHypothesis` | `HuffmanOptimality.lean:775` | `HuffmanChainWalls.lean` | 同上 |
| `MergedHuffmanAuxIdentHypothesis` | `HuffmanMergedIdentBody.lean:143` | `HuffmanChainWalls.lean` | `HuffmanMergedIdentBody.lean` は `HuffmanChainWalls` を import (`HuffmanOptimality` 経由なので自動) |
| `HuffmanCombinedHypothesis` | `HuffmanT1APPrimeBody.lean:524` (abbrev := And) | `HuffmanChainWalls.lean` | 同上 |
| `HuffmanChainCombinedHypothesis` | `HuffmanSwapStepChainBody.lean:322` (abbrev := And) | `HuffmanChainWalls.lean` | 同上 |

5 predicate を全て `HuffmanChainWalls.lean` に move する理由:

- abbrev `:= And` 形は consumer file 内に残しても import 問題は起きないが (上流に居る `HuffmanCombinedHypothesis` の定義から下流の Hyp1 / Hyp2 を見ているわけではない)、**1 ヶ所に集約する** ことで wall lemma 群 (`huffman_combined_hypothesis_holds` 等) も同 file 内で constructive composition で組める。
- 親 `HuffmanWalls.lean` の現構造 (= 5 predicate + 5 wall lemma) を踏襲、ただし位置を上流端に移すだけ。

**alternative**: `HuffmanCombinedHypothesis` / `HuffmanChainCombinedHypothesis` は consumer file (`HuffmanT1APPrimeBody` / `HuffmanSwapStepChainBody`) 内に残し、`HuffmanChainWalls` 側で **alias** (`HuffmanChainWalls.HuffmanCombinedHypothesis := T1APPrimeBody.HuffmanCombinedHypothesis`) を提供する案も検討したが、abbrev の forward declaration が Lean では機能しないため棄却。集約 move が最も無理がない。

### signature 改変順序

**下流 17 件 → 上流 4 件** の順で改変する。理由:

- 各 wrapper の signature 改変は「`h_swap`/`h_ident`/`h_aux` 引数削除 + body 内呼出を `swap_normalization_hypothesis_holds` 等に置換」のローカル変更。caller 側は **新 signature (引数なし)** を呼ぶように同時に書換える必要がある。
- 上流 (`HuffmanOptimality.lean:1058` `huffmanLength_optimal_with_hypotheses`) が下流 17 件から呼ばれているか? — 確認: 下流 17 件はすべて **`huffmanLength_optimal_with_hypotheses` を body で呼ぶ** (witness extractor 5 件は除き、body は `h_swap` / `h_ident` を直接消費)。よって:
  - **下流 17 件のうち body が `huffmanLength_optimal_with_hypotheses` を呼ぶもの**: 親が新 signature (引数削除済) になるまで書換できない → **上流先行が必要**。
  - **下流 17 件のうち body が predicate を直接 destructure するだけのもの** (witness extractor 5 件 + identification extractor 4 件 + combined projection 2 件 + 計 11 件): caller が変わるだけなので、自身の signature 改変は上流に依存せず先行可能。

混乱を避けるため、**Phase 順は上流 4 件先行 → 下流 17 件後続** に再整理する (Approach 当初予定の「下流先行」から修正)。理由: 上流 `huffmanLength_optimal_aux_with_hypotheses` (private induction motor、200+ 行) で `h_swap` / `h_ident` を `swap_normalization_hypothesis_holds` / `huffman_merged_identification_hypothesis_holds` に置換するのが本 plan の最大 risk (L-MIG-CW-2)、ここを先に閉じる方が他 Phase の design refine の余地が広がる。

(注: brief 内では「下流先行」とユーザから指示があったが、verbatim 検証の結果、下流 wrapper の body が `huffmanLength_optimal_with_hypotheses` を呼ぶケース多数で上流先行が必要なため修正。判断ログ #1 参照。)

### 既存 `HuffmanWalls.lean` の継承

- Hyp1 wall (`swap_normalization_hypothesis_holds`): 現状 `swap_normalization_proof` direct alias (Tier 1)。本 plan で **sorry に降格** (Tier 1 → Tier 2) — `HuffmanChainWalls.lean` が `HuffmanStrongForm.lean` (上流) の `swap_normalization_proof` に依存できないため。撤退ライン L-MIG-CW-3 で safety 担保。
- Hyp2 / Hyp_aux wall: sorry + `@residual(plan:...)` 維持。位置だけ `HuffmanWalls.lean` → `HuffmanChainWalls.lean` に移動。
- combined / chain combined wall: Hyp1 wall + Hyp2 wall の constructive composition で組む (sorry なし、ただし Hyp1 が sorry 化のため transitive sorry 持ち)。
- `HuffmanWalls.lean` 自体は本 plan 終了時点で **空 file 化** (= predicate 定義 + wall lemma 全件が `HuffmanChainWalls.lean` に移行)、最終 Phase で削除候補。

21 wrapper では:

- `@residual(plan:huffman-2hyp-vertical-reduction)` 単独タグは **削除** (sorry なしになるため honest bookkeeping 不要)。
- 必要なら `@audit:ok` 付与 (transitive proof done = wall lemma が closure 済になれば自動的に閉じる構造)、ただし wall lemma 自身が sorry を持つ限り `@audit:ok` は不可 (proof done は wall closure 待ち)。Phase 4 で tag 整理。

## Phase 詳細

### Phase 0 — Inventory (21 wrapper の signature verbatim 表)

- [ ] **0.1** 以下 21 wrapper の現 signature を `Read` で verbatim 確認し、Phase 2/3 で削除する引数 + body 内置換対象を per-declaration 表で固定。本 plan §「在庫表」が一次出力。

#### 在庫表 — 21 wrapper の signature 改変計画 (verbatim 確認済、2026-05-25)

| # | file:line | decl 名 | 削除する hypothesis 引数 | body 内置換 (h_swap → / h_ident → / h_aux →) | 改変後タグ |
|---:|---|---|---|---|---|
| **上流 4 件** ||||||
| 1 | `HuffmanOptimality.lean:804` | `huffmanLength_optimal_aux_with_hypotheses` (private induction motor) | `h_swap : SwapNormalizationHypothesis.{u}` / `h_ident : HuffmanMergedIdentificationHypothesis.{u}` | body 内全箇所 `h_swap` → `swap_normalization_hypothesis_holds` / `h_ident` → `huffman_merged_identification_hypothesis_holds` (200+ 行 induction motor 内、参照箇所は L-MIG-CW-2 で別途精査) | tag 削除 (sorry なしへ) |
| 2 | `HuffmanOptimality.lean:1058` | `huffmanLength_optimal_with_hypotheses` (public wrapper) | 同上 (`h_swap` / `h_ident`) | body の呼出 `huffmanLength_optimal_aux_with_hypotheses (Fintype.card α) h_swap h_ident P hP l hl_pos hl_kraft rfl` を `huffmanLength_optimal_aux_with_hypotheses (Fintype.card α) P hP l hl_pos hl_kraft rfl` に書換 | tag 削除 |
| 3 | `HuffmanStrongForm.lean:183` | `huffmanLength_optimal_modulo_aux_ident` | `h_aux : MergedHuffmanAuxIdentHypothesis.{u}` | body `huffmanLength_optimal_with_hypotheses swap_normalization_proof (huffmanMergedIdentification_of_aux h_aux) P hP l hl_pos hl_kraft` を `huffmanLength_optimal_with_hypotheses P hP l hl_pos hl_kraft` に書換 (= 2 hypothesis 引数とも削除済、`huffmanMergedIdentification_of_aux` 経由は不要、wall が直接供給) | tag 削除 |
| 4 | `HuffmanMergedIdentBody.lean:192` | `huffmanLength_optimal_with_swap_and_aux` | `h_swap : SwapNormalizationHypothesis.{u}` / `h_aux : MergedHuffmanAuxIdentHypothesis.{u}` | body 全体を `huffmanLength_optimal_with_hypotheses P hP l hl_pos hl_kraft` に置換 (= 上流先行で改変済の引数なし version を呼ぶ) | tag 削除 |
| **下流 13 件 — `HuffmanT1APPrimeBody.lean`** ||||||
| 5 | `HuffmanT1APPrimeBody.lean:158` | `huffmanMergedIdentification_at_a` | `h_ident` | body `h_ident Q hQ h_card ... x` を `huffman_merged_identification_hypothesis_holds Q hQ h_card ... x` に置換 | tag 削除 |
| 6 | `:179` | `huffmanMergedIdentification_at_other` | 同上 | 同上 | tag 削除 |
| 7 | `:201` | `huffmanMergedIdentification_combined` | 同上 | body も同様の置換 (alias 形) | tag 削除 |
| 8 | `:225` | `huffmanMergedIdentification_dichotomy` | 同上 | body 内の `huffmanMergedIdentification_at_a/_at_other h_ident` を `huffman_merged_identification_hypothesis_holds` に置換 (alias 経由) | tag 削除 |
| 9 | `:281` | `huffmanLength_optimal_via_partial_swap_when_eq` | `h_swap` / `h_ident` | body `huffmanLength_optimal_with_hypotheses h_swap h_ident P hP l hl_pos hl_kraft` を上流改変後 signature `huffmanLength_optimal_with_hypotheses P hP l hl_pos hl_kraft` に置換 | tag 削除 |
| 10 | `:298` | `huffmanLength_optimal_wrapper_explicit` | 同上 | 同上 | tag 削除 |
| 11 | `:379` | `SwapNormalizationHypothesis_apply_witness` | `h_swap` | body `h_swap Q ll ...` を `swap_normalization_hypothesis_holds Q ll ...` に置換 | tag 削除 |
| 12 | `:401` | `SwapNormalizationHypothesis_witness_pos` | 同上 | 同上 (body 内 `obtain ⟨...⟩ := h_swap ...`) | tag 削除 |
| 13 | `:420` | `SwapNormalizationHypothesis_witness_kraft` | 同上 | 同上 | tag 削除 |
| 14 | `:440` | `SwapNormalizationHypothesis_witness_eq` | 同上 | 同上 | tag 削除 |
| 15 | `:460` | `SwapNormalizationHypothesis_witness_expL` | 同上 | 同上 | tag 削除 |
| 16 | `:540` | `huffmanLength_optimal_with_combined` | `h : HuffmanCombinedHypothesis.{u}` | body `huffmanLength_optimal_with_hypotheses h.1 h.2 P hP l hl_pos hl_kraft` を `huffmanLength_optimal_with_hypotheses P hP l hl_pos hl_kraft` に置換 | tag 削除 |
| 17 | `:610` | `huffmanLength_optimal_terminal` | `H : HuffmanCombinedHypothesis.{u}` | body `huffmanLength_optimal_with_combined H P hP l hl_pos hl_kraft` を `huffmanLength_optimal_with_combined P hP l hl_pos hl_kraft` (上流改変後) に置換 | tag 削除 |
| **下流 4 件 — `HuffmanT1APPrimePartial.lean`** ||||||
| 18 | `HuffmanT1APPrimePartial.lean:598` | `huffmanLength_optimal_with_hypotheses_at` | `h_swap` / `h_ident` (universe `v`) | body `huffmanLength_optimal_with_hypotheses h_swap h_ident P hP l hl_pos hl_kraft` を `huffmanLength_optimal_with_hypotheses P hP l hl_pos hl_kraft` に置換 | tag 削除 |
| 19 | `:614` | `huffmanLength_optimal_with_combined_hypothesis` | `h : SwapNormalizationHypothesis.{u} ∧ HuffmanMergedIdentificationHypothesis.{u}` (= `HuffmanCombinedHypothesis` の inline 形) | body `huffmanLength_optimal_with_hypotheses h.1 h.2 P hP l hl_pos hl_kraft` を `huffmanLength_optimal_with_hypotheses P hP l hl_pos hl_kraft` に置換 | tag 削除 |
| 20 | `:840` | `huffmanLength_optimal_with_pair_hypothesis` | `h : PProd (SwapNormalizationHypothesis.{u}) (HuffmanMergedIdentificationHypothesis.{u})` | body `huffmanLength_optimal_with_hypotheses h.fst h.snd P hP l hl_pos hl_kraft` を `huffmanLength_optimal_with_hypotheses P hP l hl_pos hl_kraft` に置換 | tag 削除 |
| 21 | `:855` | `huffmanLength_optimal_with_hypotheses_contra` | `h_swap` / `h_ident` | body 内呼出を引数なし version に置換 (本宣言は contraposition 形で body も再 verify 必要) | tag 削除 |

- [ ] **0.2** Cross-family 確認: 5 predicate を移動して他 family の use site が壊れないか `rg` で確認 (本 plan 起草時点で `rg` 確認済 = ゼロ件、Phase 0 で再 verify)。
- [ ] **0.3** `HuffmanT1APPrimeBody.lean:528` `huffmanCombinedHypothesis_swap` / `:533` `huffmanCombinedHypothesis_ident` (projection 2 件) は本 plan scope **外** (現状 `@residual` 単独タグなし、Phase 1 で親 plan が処理済の constructive bridge)。`@audit:retract-candidate` 候補として handoff。

**Phase 0 DoD**: 在庫表 21 件が Read で verbatim 再確認済 + 判断ログ #1 で確定。cross-family ゼロ件再 verify 済。

**proof-log**: no (verbatim 確認 + 表更新のみ)。

### Phase 1 — `HuffmanChainWalls.lean` 新規 file 作成 + predicate move

- [ ] **1.1** `Common2026/Shannon/HuffmanChainWalls.lean` を Write。skeleton:
  ```lean
  import Common2026.Shannon.Huffman   -- huffmanLength, huffmanLengthAux, mergedMeasure 等の基礎

  namespace InformationTheory.Shannon.Huffman
  universe u

  -- predicate 定義 5 件 (verbatim move from HuffmanOptimality / HuffmanMergedIdentBody /
  -- HuffmanT1APPrimeBody / HuffmanSwapStepChainBody。各 docstring も保存)
  abbrev SwapNormalizationHypothesis : Prop := ...
  abbrev HuffmanMergedIdentificationHypothesis : Prop := ...
  abbrev MergedHuffmanAuxIdentHypothesis : Prop := ...
  abbrev HuffmanCombinedHypothesis : Prop :=
    SwapNormalizationHypothesis.{u} ∧ HuffmanMergedIdentificationHypothesis.{u}
  abbrev HuffmanChainCombinedHypothesis : Prop :=
    SwapNormalizationHypothesis.{u} ∧ HuffmanMergedIdentificationHypothesis.{u}

  -- wall lemma 5 件 (Hyp1 は本 plan では sorry 化、L-MIG-CW-3 で別 plan に handoff)
  /-- @residual(plan:huffman-2hyp-vertical-reduction) -/
  theorem swap_normalization_hypothesis_holds : SwapNormalizationHypothesis.{u} := by sorry

  /-- @residual(plan:huffman-2hyp-vertical-reduction) -/
  theorem huffman_merged_identification_hypothesis_holds :
      HuffmanMergedIdentificationHypothesis.{u} := by sorry

  /-- @residual(plan:huffman-strong-form-completion) -/
  theorem merged_huffman_aux_ident_hypothesis_holds : MergedHuffmanAuxIdentHypothesis.{u} := by sorry

  theorem huffman_combined_hypothesis_holds : HuffmanCombinedHypothesis.{u} :=
    ⟨swap_normalization_hypothesis_holds, huffman_merged_identification_hypothesis_holds⟩

  theorem huffman_chain_combined_hypothesis_holds : HuffmanChainCombinedHypothesis.{u} :=
    ⟨swap_normalization_hypothesis_holds, huffman_merged_identification_hypothesis_holds⟩

  end InformationTheory.Shannon.Huffman
  ```
- [ ] **1.2** `HuffmanOptimality.lean` から `SwapNormalizationHypothesis` / `HuffmanMergedIdentificationHypothesis` の **abbrev 定義を削除** (`import Common2026.Shannon.HuffmanChainWalls` を 1 行追加、本来 file 内 `:759` まわり / `:775` の 2 abbrev block 削除)。docstring は `HuffmanChainWalls.lean` 側に move 済なので問題なし。
- [ ] **1.3** `HuffmanMergedIdentBody.lean` から `MergedHuffmanAuxIdentHypothesis` の **abbrev 定義を削除** (`HuffmanChainWalls` import は `HuffmanOptimality` 経由で自動)。
- [ ] **1.4** `HuffmanT1APPrimeBody.lean` から `HuffmanCombinedHypothesis` の **abbrev 定義を削除** (同上)。
- [ ] **1.5** `HuffmanSwapStepChainBody.lean` から `HuffmanChainCombinedHypothesis` の **abbrev 定義を削除** (同上)。
- [ ] **1.6** `Common2026.lean` に `import Common2026.Shannon.HuffmanChainWalls` を追加 (`HuffmanOptimality` import 行の **直前**、L256 まわり)。
- [ ] **1.7** `lake env lean Common2026/Shannon/HuffmanChainWalls.lean` + `HuffmanOptimality.lean` + `HuffmanMergedIdentBody.lean` + `HuffmanT1APPrimeBody.lean` + `HuffmanSwapStepChainBody.lean` を sequential に再 verify (CLAUDE.md 「After upstream edits」、`lake build Common2026.Shannon.HuffmanChainWalls` で olean refresh も併用)。

**Phase 1 DoD**: 5 predicate が `HuffmanChainWalls.lean` 1 ヶ所に集約、5 wall lemma が direct sorry × 3 (Hyp1 + Hyp2 + Hyp_aux) + constructive composition × 2 (Combined + ChainCombined)、`lake env lean` 5 file が 0 errors (`sorry` warning は許容)。

**proof-log**: yes (`docs/shannon/proof-log-huffman-chain-walls-split-phase1.md`)。理由: predicate move は file 跨ぎの構造変更で abbrev の universe / Fintype binder の継承が壊れる risk あり。

### Phase 2 — 上流 4 件 signature 改変

- [ ] **2.1** `HuffmanOptimality.lean:804` `huffmanLength_optimal_aux_with_hypotheses` (private):
  - signature から `(h_swap : SwapNormalizationHypothesis.{u})` / `(h_ident : HuffmanMergedIdentificationHypothesis.{u})` を削除。
  - body 内の `h_swap` / `h_ident` 参照箇所 (200+ 行 strong induction motor 内、`rg -n 'h_swap\|h_ident' :804-:1027` で確認後) を `swap_normalization_hypothesis_holds` / `huffman_merged_identification_hypothesis_holds` に置換。
  - 失敗時 L-MIG-CW-2 発動。
- [ ] **2.2** `HuffmanOptimality.lean:1058` `huffmanLength_optimal_with_hypotheses` (public):
  - signature から同 2 引数を削除。
  - body の `huffmanLength_optimal_aux_with_hypotheses (Fintype.card α) h_swap h_ident P hP l hl_pos hl_kraft rfl` を `huffmanLength_optimal_aux_with_hypotheses (Fintype.card α) P hP l hl_pos hl_kraft rfl` に書換。
- [ ] **2.3** `HuffmanStrongForm.lean:183` `huffmanLength_optimal_modulo_aux_ident`:
  - signature から `(h_aux : MergedHuffmanAuxIdentHypothesis.{u})` を削除。
  - body を `huffmanLength_optimal_with_hypotheses P hP l hl_pos hl_kraft` に置換 (新 signature)。`swap_normalization_proof` / `huffmanMergedIdentification_of_aux h_aux` を引数で渡す必要なし (上流改変後 wall が自動供給)。
  - 注: 旧 docstring の「Hyp1 is `swap_normalization_proof` で discharge 済」「`h_aux` は load-bearing」の散文は **削除** (本 plan で wall に集約済、redundant)。
- [ ] **2.4** `HuffmanMergedIdentBody.lean:192` `huffmanLength_optimal_with_swap_and_aux`:
  - signature から `(h_swap : SwapNormalizationHypothesis.{u})` / `(h_aux : MergedHuffmanAuxIdentHypothesis.{u})` を削除。
  - body を `huffmanLength_optimal_with_hypotheses P hP l hl_pos hl_kraft` に置換。
- [ ] **2.5** 全 4 件で olean refresh (`lake build Common2026.Shannon.HuffmanOptimality` 等) 後、 `lake env lean` で 0 errors 確認。

**Phase 2 DoD**: 上流 4 件で signature から load-bearing hypothesis 削除、body 内呼出が wall lemma 経由、`lake env lean` 0 errors。

**proof-log**: yes (`docs/shannon/proof-log-huffman-chain-walls-split-phase2.md`)。理由: induction motor 200+ 行内の `h_swap` / `h_ident` 置換は universe / binder scoping で型 error が出やすい (L-MIG-CW-2 発動条件の主舞台)。

### Phase 3 — 下流 17 件 signature 改変

- [ ] **3.1** `HuffmanT1APPrimeBody.lean` 13 件 (在庫表 #5-#17):
  - 各 wrapper の signature から `h_swap` / `h_ident` / `h : HuffmanCombinedHypothesis` / `H : HuffmanCombinedHypothesis` 引数を削除。
  - body 内呼出を wall lemma 経由 (`swap_normalization_hypothesis_holds` / `huffman_merged_identification_hypothesis_holds` / `huffman_combined_hypothesis_holds`) または上流改変済 signature に置換。
  - 各 wrapper 完了後 `lake env lean` 0 errors。
- [ ] **3.2** `HuffmanT1APPrimePartial.lean` 4 件 (在庫表 #18-#21):
  - 同様の signature 改変 + body 置換。`huffmanLength_optimal_with_hypotheses_at` (universe `v`) は universe variable 注意。
- [ ] **3.3** olean refresh + 全 file 再 verify。

**Phase 3 DoD**: 下流 17 件で signature 改変済、`lake env lean` 0 errors、新規 sorry 0 件 (上流 + wall に集約済)。

**proof-log**: yes (`docs/shannon/proof-log-huffman-chain-walls-split-phase3.md`)。理由: 17 件の mechanical rewrite だが、`HuffmanCombinedHypothesis` の `.1` / `.2` projection (現 abbrev := And) を wall version に置換する際の name collision、`PProd.fst` / `.snd` の差異など型 error の可能性。

### Phase 4 — タグ整理 + 既存 `HuffmanWalls.lean` の handling

- [ ] **4.1** 21 wrapper の docstring 末尾 `@residual(plan:huffman-2hyp-vertical-reduction)` (or `huffman-strong-form-completion`) 単独タグを **削除** (sorry なしになるため honest bookkeeping 不要)。`@audit:ok` は付与しない (wall lemma に sorry が残り transitive proof done 未達のため)。代わりに docstring 散文で「wall lemma `HuffmanChainWalls.swap_normalization_hypothesis_holds` 等が closure を担当」と明示。
- [ ] **4.2** 5 predicate の `@audit:retract-candidate(load-bearing-predicate)` タグを **削除** (5 predicate は genuine な命題で、wall lemma が closure すれば自動的に proved、retract 候補ではなくなる)。代わりに「`HuffmanChainWalls.lean` 内 wall lemma が discharge を担当」散文を docstring に保存。
- [ ] **4.3** 旧 `Common2026/Shannon/HuffmanWalls.lean` の現状確認:
  - Hyp1 wall (`swap_normalization_proof` direct alias、`@audit:ok`、現状 line 49-55) → 本 plan で `HuffmanChainWalls.swap_normalization_hypothesis_holds` (sorry) に置換済 → 旧 wall lemma は **dead code** に。
  - Hyp2 / Hyp_aux wall (sorry + `@residual`、line 60-70) → 本 plan で `HuffmanChainWalls` に同等品を新設済 → dead code。
  - combined / chain combined wall (constructive composition、line 75-83) → 同上、dead code。
  - 判断: `HuffmanWalls.lean` 全 wall lemma を `HuffmanChainWalls` に **完全移行済** として、`HuffmanWalls.lean` を **削除** (`Common2026.lean` の `import Common2026.Shannon.HuffmanWalls` 行 L256 も削除)。
- [ ] **4.4** Hyp1 wall の constructive 化を後続 plan に handoff:
  - 別 plan `docs/shannon/huffman-chain-walls-hyp1-bridge-plan.md` (本 plan 完了後に起草) で `HuffmanStrongForm.lean` 末尾に `swap_normalization_hypothesis_holds_eq_proof : @swap_normalization_hypothesis_holds = swap_normalization_proof := rfl` 等の bridge lemma + `HuffmanChainWalls.lean` 内 sorry の constructive 置換を行う。本 plan scope 外。
- [ ] **4.5** Phase 4 全 file (主に `HuffmanT1APPrimeBody` / `HuffmanT1APPrimePartial` / `HuffmanStrongForm` / `HuffmanMergedIdentBody` / `HuffmanOptimality`) で `lake env lean` 0 errors。

**Phase 4 DoD**: 21 wrapper + 5 predicate の旧 `@residual` 単独タグ / `@audit:retract-candidate` 削除済、`HuffmanWalls.lean` 削除済 (or skeleton 空 file、L-MIG-CW-3 で safety 担保された場合は維持)。

**proof-log**: no (tag 整理 + 削除のみ、mechanical)。

### Phase 5 — honesty-auditor 起動

- [ ] **5.1** `honesty-auditor` agent を 1 件起動。監査対象:
  - `HuffmanChainWalls.lean` の 3 direct sorry (Hyp1 + Hyp2 + Hyp_aux) の `@residual(<class>:<slug>)` classification の正しさ。
  - 21 wrapper の signature が load-bearing hypothesis を持たないことの確認 (signature の honesty 監査)。
  - 5 predicate 定義の move 後の docstring / classification 整合性。
- [ ] **5.2** verdict が `defect 0` を確認後、Phase V へ。`questionable` で散文 refine 提案あれば即時適用、`defect` の場合は当該 declaration 撤回 or sorry-based に書換。

**Phase 5 DoD**: honesty-auditor verdict `defect 0`。

### Phase V — verify

- [ ] **V.1** 全 13 file (Huffman.lean 含む) で `lake env lean` 確認 (`HuffmanWalls.lean` は削除済なら除外)。
- [ ] **V.2** 集計コマンド:
  ```bash
  rg -nw 'sorry' Common2026/Shannon/Huffman*.lean | wc -l               # 期待値: 3 (HuffmanChainWalls 内 wall 3 件)
  rg '@residual\(plan:huffman-2hyp-vertical-reduction\)' Common2026/Shannon/Huffman*.lean | wc -l   # 期待値: 2 (HuffmanChainWalls 内 Hyp1 + Hyp2)
  rg '@residual\(plan:huffman-strong-form-completion\)' Common2026/Shannon/Huffman*.lean | wc -l    # 期待値: 1 (HuffmanChainWalls 内 Hyp_aux)
  rg '@audit:retract-candidate' Common2026/Shannon/Huffman*.lean | wc -l                           # 期待値: 0 (predicate retract タグ削除済)
  rg 'load-bearing.*hypothesis' Common2026/Shannon/Huffman*.lean | wc -l                          # 期待値: 散文ゼロ
  # 21 wrapper の signature 改変確認: 各 file で h_swap / h_ident / h_aux が `theorem` の binder list に出現しないこと
  rg -n '(h_swap|h_ident|h_aux)\s*:\s*(SwapNormalization|HuffmanMergedIdent|MergedHuffmanAux)' Common2026/Shannon/Huffman*.lean
  # 期待値: ゼロ件
  ```
- [ ] **V.3** `huffman-sorry-migration-plan.md` 冒頭 banner に「**L-MIG-4 拡張発動の構造的 fix 完了**: `HuffmanChainWalls.lean` 分離により上流 4 + 下流 17 = 21 wrapper を完全 Tier 2 化、`huffman-chain-walls-split-plan.md` 参照」を追記。
- [ ] **V.4** 次セッション handoff: Hyp1 wall constructive 化 (`huffman-chain-walls-hyp1-bridge-plan.md`) + Hyp2 / Hyp_aux closure (既存 `huffman-2hyp-vertical-reduction-plan.md` / `huffman-strong-form-completion-plan.md`)。

**Phase V DoD**: 全 file `lake env lean` 0 errors、`@residual` 3 件 (wall 3 件)、`sorry` 3 件 (同上)、21 wrapper の signature から load-bearing hypothesis ゼロ件。

## 撤退ライン (L-MIG-CW-X)

### L-MIG-CW-1 (predicate move で他 family から参照あり)

5 predicate (`SwapNormalizationHypothesis` / `HuffmanMergedIdentificationHypothesis` / `MergedHuffmanAuxIdentHypothesis` / `HuffmanCombinedHypothesis` / `HuffmanChainCombinedHypothesis`) のいずれかが Huffman 以外 (= 他 family、`Common2026/Han/` / `Common2026/Shannon/AWGN*.lean` 等) から参照されていたら、predicate move (= 定義位置の移動) は他 family の use site を壊す risk あり。

**発動条件**: Phase 0.2 で `rg -n '<predicate name>' Common2026/ | grep -v Huffman` が **1 件以上** 出力する。

**対応**: 該当 predicate の move を放棄、`HuffmanChainWalls.lean` 側に **alias 定義**:
```lean
abbrev SwapNormalizationHypothesis : Prop := _root_.InformationTheory.Shannon.Huffman.SwapNormalizationHypothesis
```
で wall lemma だけ持たせる (定義は元位置に残置)。consumer の signature 改変は alias 経由でも可能。

**本 plan 起草時点 (2026-05-25) の確認**: `rg` で Huffman 外参照ゼロ件、L-MIG-CW-1 不発動見込み。Phase 0.2 で再 verify。

### L-MIG-CW-2 (induction motor body 200+ 行 rewrite で型 error)

`huffmanLength_optimal_aux_with_hypotheses` (`HuffmanOptimality.lean:804`) の body 内 `h_swap` / `h_ident` の universe / instance 引数を shared wall lemma 名 (`swap_normalization_hypothesis_holds` / `huffman_merged_identification_hypothesis_holds`) に置換する mechanical rewrite が機能しない可能性:

- 旧 `h_swap : SwapNormalizationHypothesis.{u}` は **明示的に universe `u` 注釈** あり。wall lemma は `theorem ... : SwapNormalizationHypothesis.{u}` 形で同様に universe `u` 注釈付き → 置換後の universe 推論で `u` が `Type u` 外に逃げる risk。
- induction motor は `Nat.strong_induction_on generalizing α with` で `α` / `P` / `l` を `generalizing` するが、wall lemma 側の universe `u` は `α : Type u` の `u` と同期する必要があり、`generalizing` 後に universe variable が free になる可能性。

**発動条件**: Phase 2.1 で `lake env lean Common2026/Shannon/HuffmanOptimality.lean` が rewrite 後に **3 ターン以上 error 残**。typical error: `universe mismatch` / `failed to synthesize SwapNormalizationHypothesis.{?u}`。

**対応**: Phase 2.1 を pause、`huffmanLength_optimal_aux_with_hypotheses` (private induction motor) のみ **signature 不変・body 内で wall 呼出のために `have h_swap := swap_normalization_hypothesis_holds; have h_ident := huffman_merged_identification_hypothesis_holds` を冒頭に挿入** する代替策に降格 (= signature には引数残置だが、wall 由来の値を local hypothesis として bind して旧 body と互換)。

- 効果: private 側は load-bearing hypothesis 引数残置だが、`HuffmanOptimality.lean:1058` `huffmanLength_optimal_with_hypotheses` (public) は 引数なし、wall 経由で `huffmanLength_optimal_aux_with_hypotheses ... (h_swap := swap_normalization_hypothesis_holds) (h_ident := huffman_merged_identification_hypothesis_holds) ...` を呼ぶ形に。public wrapper のみ Tier 2 化、private は Tier 4 残置 (= 部分後退、ただし下流 17 件 + 上流 3 件 (public + StrongForm + MergedIdentBody) は完全 Tier 2 化可能)。
- 完全 Tier 2 化は別 plan で。本 plan は **「public + 下流 = 20 件 Tier 2 化、private = 1 件 Tier 4 残置」** を accepted state として close。

### L-MIG-CW-3 (Hyp1 wall の `@audit:ok` が破られる)

現 `HuffmanWalls.lean:49-55` `swap_normalization_hypothesis_holds` は `swap_normalization_proof` direct alias で `@audit:ok` (Tier 1)。本 plan で `HuffmanChainWalls.lean` (上流) に移すと `swap_normalization_proof` (下流 `HuffmanStrongForm.lean:149`) に依存不能 → **Tier 1 → Tier 2 (sorry) 降格**。

これは見かけ上 honesty 後退だが、引き換えに 21 wrapper の Tier 5 → Tier 2 改善が得られるので net 改善。ただし honesty-auditor (Phase 5) が降格を **`questionable`** で flag する可能性。

**発動条件**: Phase 5 で auditor が「Hyp1 wall の Tier 1 → Tier 2 降格は acceptable か?」を `questionable` で問う。

**対応**: 以下のいずれか:

1. **降格 accepted**: docstring 散文で「`swap_normalization_proof` (`HuffmanStrongForm.lean:149`) は constructive proof として既存、ただし import 方向の関係で `HuffmanChainWalls.lean` 内では呼出不能。bridge lemma を別 plan (`huffman-chain-walls-hyp1-bridge-plan.md`) で提供予定」と明示。auditor verdict を `ok` に refine。
2. **降格不可**: 本 plan の Phase 1 で **`HuffmanWalls.lean` を残置** (Hyp1 wall constructive alias as is)、`HuffmanChainWalls.lean` は Hyp2 / Hyp_aux のみ持つ (Hyp1 wall は下流端 `HuffmanWalls.lean` のまま)。consumer の Hyp1 wall 呼出は `HuffmanWalls.swap_normalization_hypothesis_holds` (下流) に依存 → 上流 wrapper は呼出不能 → 上流 4 件の Tier 2 化を放棄、下流 17 件のみ Tier 2 化。

L-MIG-CW-3 case 2 発動時の expected DoD: 下流 17 件 Tier 2 化、上流 4 件 Tier 4 残置 (= 本 plan の改善幅が縮小、ただし「無策」よりはまし)。

### 撤退ライン発動の組み合わせ

3 ライン同時発動 (worst case): L-MIG-CW-1 + L-MIG-CW-2 + L-MIG-CW-3 → 本 plan を Phase 1 で pause、`huffman-sorry-migration-plan.md` 状態を維持 (= 親 plan の type-check done を save 状態)、再起案。

## 未決事項

1. **`HuffmanCombinedHypothesis` / `HuffmanChainCombinedHypothesis` の abbrev move 方針**: 本 plan §「predicate 移動」表で **5 件全 move** をデフォルトとしたが、abbrev `:= And` 形は consumer file に残しても import 問題を起こさない。consumer file 内に残す案 (`HuffmanT1APPrimeBody.lean:524` / `HuffmanSwapStepChainBody.lean:322` のまま) も検討余地あり。実装 agent が Phase 1 で判断:
   - 残す → `HuffmanChainWalls.lean` 側で alias (`abbrev HuffmanCombinedHypothesis := _root_.InformationTheory.Shannon.Huffman.HuffmanCombinedHypothesis`) または `HuffmanCombinedHypothesis.holds` を本 file 内で declaration 作成、5 件統一の honest さは保たれる。
   - 全 move → 集約感は高いが下流 file の abbrev 定義 1 行を削除する手間あり。
2. **既存 `HuffmanWalls.lean` 内の 2 件 sorry (Hyp2 + Hyp_aux) は本 plan で touch しない**: Phase 4.3 で `HuffmanWalls.lean` 全 wall lemma が `HuffmanChainWalls` に移行済として **削除** をデフォルト。代替: 削除せず empty `namespace InformationTheory.Shannon.Huffman end` skeleton として残置 (`Common2026.lean` の import 行を保つ) も可。実装 agent 判断 + Phase 0 inventory で再評価。
3. **cross-family ripple (Hoeffding / WynerZiv 系で同様 predicate 移動戦略が必要か)**: 本 plan scope **外**。別 family の sorry-migration plan で同様の L-MIG-4 拡張発動 (= import cycle で signature 改変断念) が観察された場合、本 plan を template に同様の `<family>ChainWalls.lean` 分離 plan を別途起草。runbook (`docs/audit/sorry-migration-runbook.md`)「失敗パターン」に Pattern I (= load-bearing hyp 残置の構造的 fix としての ChainWalls 分離) として追記候補。
4. **Phase 2.1 / 2.2 順序**: 本 plan §「signature 改変順序」で「**上流 4 件先行 → 下流 17 件後続**」に再整理した。brief 内ユーザ指示の「下流先行」と異なる。下流先行案では下流 17 件が `huffmanLength_optimal_with_hypotheses` (上流) を新 signature で呼ぶことができず詰む。Approach 採用前に user に判断仰ぐべき項目 (本 plan は上流先行 default、user が他意あれば反証 OK)。
5. **Hyp1 wall の constructive 復活 plan**: L-MIG-CW-3 で言及した別 plan (`huffman-chain-walls-hyp1-bridge-plan.md`) は本 plan 完了後に起草、scope は (a) `HuffmanStrongForm.lean` 末尾に bridge lemma `swap_normalization_hypothesis_holds_eq_proof` 追加 + (b) `HuffmanChainWalls.lean` 内 Hyp1 sorry を `swap_normalization_proof` への constructive alias に置換 (import 方向は逆だが etale な等式 lemma で bridging)。実現可能性は別途検証要。

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退ライン発動 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 plan 起草**: orchestrator (今 session) が Huffman sorry-migration audit verdict (agent `a961ba4e002bd9f28`) を受けて起草。L-MIG-4 拡張発動 (親 plan 判断ログ #2-#4、verbatim Context §1 引用) を回避する構造的 fix として `HuffmanChainWalls.lean` 分離 + 上流配置による signature 改変アプローチを採用。21 wrapper の per-declaration signature 改変表を verbatim 確認後固定 (Phase 0 §「在庫表」)。
   - **アプローチの本質**: `HuffmanWalls.lean` を import chain の **下流端から上流端** に移動 (= `HuffmanOptimality` より前に位置するように `HuffmanChainWalls.lean` を新設、predicate 5 件 + wall lemma 5 件を move)。これにより上流 wrapper (`HuffmanOptimality` / `HuffmanStrongForm` / `HuffmanMergedIdentBody`) が wall lemma を呼べる = 親 plan で L-MIG-4 拡張で断念した signature 改変が解禁。
   - **トレードオフ**: Hyp1 wall (`HuffmanStrongForm.lean:149` `swap_normalization_proof` 経由) の constructive alias 状態 (Tier 1 `@audit:ok`) が import 方向の関係で維持できず → 本 plan 内では Hyp1 wall も sorry に降格 (Tier 1 → Tier 2)。引き換えに 21 wrapper を Tier 5 (load-bearing hyp bundling) → Tier 2 (sorry + `@residual`) に降格、net honest 改善。Hyp1 constructive 化は別 plan (`huffman-chain-walls-hyp1-bridge-plan`) に handoff。
   - **Phase 順序の判断修正**: brief 内ユーザ指示の「下流 17 件先行 → 上流 4 件後続」は、verbatim 検証 (下流 wrapper の body 多数が `huffmanLength_optimal_with_hypotheses` を呼ぶ事実) と整合せず、**上流先行 → 下流後続** に修正 (未決事項 #4)。
   - **cross-family 確認**: 5 predicate を `rg` で Huffman 外 use site 検索、本 plan 起草時点でゼロ件 = L-MIG-CW-1 不発動見込み。

<!-- 後続セッションで判断変更があれば下記に追記 (append-only):
2. **YYYY-MM-DD <要点>**: <変更理由 + 撤退ラインへの紐付け>。
-->
