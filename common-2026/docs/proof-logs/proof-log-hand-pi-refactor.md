# HanD / Pi reshape を Mathlib `MeasurableEquiv.piFinsetUnion` ベースに refactor — ボトルネック分析

将来 (a) Mathlib 上流補題への置換時の「前提形ギャップ」見積もりツール、および (b) `subst` の発火条件を事前判定するツール、の必要性を判断するベースライン記録。

**定量データ**: [docs/metrics/hand-pi-refactor.metrics.md](../metrics/hand-pi-refactor.metrics.md)

## 0. 対象問題と成果物

`Common2026/Shannon/Pi.lean` 内の自前 `subsetIdxEquiv` / `subsetSplitMEquiv` / `subsetSplitMEquiv_apply` (計 50+ 行) を Mathlib 上流補題 `MeasurableEquiv.piFinsetUnion` ベースに置換する保守 refactor。Polymatroid moonshot (`docs/han/polymatroid-moonshot-plan.md`) の inventory で派生した「Mathlib 標準補題で自前 plumbing を subsume できる可能性」(C 横断改善) の本実装。

成果物:

- `Common2026/Shannon/Pi.lean` — `MeasurableEquiv.coe_piFinsetUnion` / `_apply_left` / `_apply_right` の 3 bridge lemma を追加、`subsetSplitMEquivAux` (disjoint+union 形) に統一、subset-form 撤去
- `Common2026/Shannon/HanD.lean` — `condEntropy_subset_anti` の call site を `Finset.disjoint_sdiff` + `Finset.union_sdiff_of_subset h` の 2 行 inline 導出に書き換え
- `Common2026/Shannon/Polymatroid.lean` — `jointEntropySubset_mono` / `jointEntropySubset_disjoint_union` / `condEntropy_reshape_disjoint_union` を aux 直接呼び出しに migrate
- 4 ファイル (上記 3 + 依存先 `SlepianWolf.lean`) すべて `lake env lean` silent (0 errors / 0 warnings / 0 sorry)
- 行数差分: net **-12 行** (target -30〜-45 行は未達、後述)

## 1. 問題のキャラクター

新規証明はゼロ。「自前 plumbing と Mathlib 上流補題の signature gap をどう吸収するか」の設計判断に支配された refactor。本質は 3 点:

1. Mathlib `MeasurableEquiv.piFinsetUnion` の前提形 (`Disjoint s t`) と自前 `subsetSplitMEquiv` の前提形 (`T₁ ⊆ T₂`) のギャップ
2. ギャップを吸収する cast (`↥(T₁ ∪ (T₂ \ T₁)) → α` ↔ `↥T₂ → α`) を defeq で潰せるか
3. 削減すべき自前 plumbing の真の call site 数

過去 proof-log との比較: 数学的アイデアが本体の Loomis–Whitney / Polymatroid 系 ([proof-log-loomis-whitney.md](proof-log-loomis-whitney.md), [proof-log-polymatroid.md](proof-log-polymatroid.md)) と異なり、本セッションは「signature 変換 + 行数収縮」のみ。tactic 詰まり / 補題探索の試行回数はいずれも極小。

## 2. 数学的方針

数学的アイデアはなし。設計判断のみ。

### (1) 2 段ストラテジー: 内部書き換え + 外形温存 (初回実装の方針)

Mathlib `MeasurableEquiv.piFinsetUnion` は drop-in ではない (前提 `Disjoint`, 結論 `↥(s ∪ t)`)。素朴に call site 4 ヶ所を書き換えると `Disjoint` / `union` の cast を毎度書くことになる。代わりに Pi.lean に「subset-form ラッパー」を残し、内部実装だけ Mathlib に書き換える 2 段ストラテジーで開始。HanD `condEntropy_subset_anti` と Polymatroid `jointEntropySubset_mono` の call site は無変更を狙った。

### (2) subset-form 撤去への pivot (収縮判断)

初回実装は構造目標を全達成したが、行数 target (-30〜-45 行) を **+5 行** で完全 miss。原因は §4.1 の subst 失敗で必要になった `subsetSplitMEquivAux` (~30 行、apply lemma 含む)。call site 側で `Finset.disjoint_sdiff` + `Finset.union_sdiff_of_subset h` を 2 行 inline 導出する形に書き換え、subset-form を完全撤去するように pivot。+5 → -12 で 17 行改善 (この主因は §4.3 の見落とし site)。

## 3. Mathlib 補題探索の実録

| 必要だったもの | クエリ | 試行 | 結果 |
|---|---|---|---|
| `MeasurableEquiv.piFinsetUnion` の存否 | loogle `MeasurableEquiv.piFinsetUnion` (indexed) | 1 | `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:612` |
| `Equiv.piFinsetUnion_left/_right` apply lemma | loogle `Equiv.piFinsetUnion_left` | 1 | `Mathlib/Data/Finset/Basic.lean:641-654` |
| `T₁ ⊆ T₂ → Disjoint T₁ (T₂ \ T₁)` | rg `Finset.disjoint_sdiff` | 1 | 既存 |
| `T₁ ∪ (T₂ \ T₁) = T₂` (for `T₁ ⊆ T₂`) | rg `Finset.union_sdiff_of_subset` | 1 | 既存 |

「Mathlib に無かった」もの (Mathlib bridge として Pi.lean に追加):

- **`MeasurableEquiv.coe_piFinsetUnion`** — `MeasurableEquiv` 版の `coe` が `Equiv.piFinsetUnion` に等しい補題は不在。Pi.lean に `rfl` の 1 行で追加。意外に通った (§5 で詳述)。
- **`MeasurableEquiv.piFinsetUnion_apply_left` / `_right`** — 同様に `Equiv` 版にしか存在せず。`coe_piFinsetUnion` 経由で 3 行ずつ導出。

これらは upstream 化 (Mathlib PR) 候補。

## 4. 試行錯誤と後戻り

### 4.1 `subst hU` の構造的失敗

**症状**: 自前 `subsetSplitMEquiv (h : T₁ ⊆ T₂)` を `MeasurableEquiv.piFinsetUnion (Finset.disjoint_sdiff)` で再構築する際、`hU : T₁ ∪ (T₂ \ T₁) = T₂` に対して `subst hU` を試みた。発火せず。

**原因**: `T₂` が hypothesis の RHS にあると同時に LHS の `T₂ \ T₁` にも出現するため、Lean の `subst` (片側から変数を完全消去する操作) が依存解析で fail する。`generalize T₂ \ T₁` を試したが、結果型が `subsetSplitMEquiv` の return type に依存しているため well-typed にならず同じく fail。

**抜け方**: `subsetSplitMEquivAux (T₁ R U) (hd : Disjoint T₁ R) (hU : T₁ ∪ R = U)` のように `R` を free にした aux def を経由。`subst hU` は `R` を含まない LHS (`T₁ ∪ R`) で clean に発火 (`U → T₁ ∪ R` への置換が無回帰)。

**教訓**: Mathlib API の前提形と自前 def の前提形にギャップがあるとき、cast 経由が defeq で潰れない場合の定石は「free variable を増やした aux def を中間に挟む」。`subst` の発火条件 (= 当該変数が hypothesis の片側から完全消去可能 / 依存型を壊さない) を事前に判定できるツールがあれば、aux 設計判断を待たずに最初から aux 経由を選べた。

### 4.2 行数見積もりの楽観バイアス

**症状**: Plan 段階で target -30〜-45 行と見積もり。初回実装で +5 行 (target 完全 miss)。

**原因**: 「subset-form ラッパー (5 行 def + 5 行 apply) で済む」前提が楽観的すぎた。実際は §4.1 の subst 失敗で `subsetSplitMEquivAux` (~30 行) が必要となり、subset-form ラッパーと併存することで +30 行のオフセット。Plan のリスク表は「`subsetSplitMEquiv` 内部の cast が defeq でなく `MeasurableEquiv.cast` も使えない」ケースを想定していたが、見積もり影響は「-10〜-20 行で部分達成」とだけ書かれており、+ 方向に振れる可能性は記述されていなかった。

**抜け方**: pivot で subset-form ラッパー自体を撤去し、call site 側で 2 行 inline 導出する形に書き換え。net +5 → -12 で 17 行改善。

**教訓**: drop-in でない Mathlib API への置換 refactor の line-count 見積もりは、「前提形ギャップを埋める bridge コスト (= aux def + apply lemma)」を必ず +20〜30 行で計上した上で、削減側を計算すべき。Plan 段階の楽観バイアスを補正するツール (refactor 規模見積もりに「signature gap penalty」を機械的に加算) があれば、初回から pivot 後の形 (subset-form 撤去 + call site inline) を提案できた。

### 4.3 Polymatroid 3 番目の call site 見落とし

**症状**: Phase 0 inventory subagent が「Polymatroid の subset-form 利用は `disjoint_union` 系 2 ヘルパーのみ、`jointEntropySubset_mono` は別経路」と報告。pivot 実装中に 3 site 目 (`jointEntropySubset_mono` line 84) を発見し追加 migrate。

**原因**: inventory subagent が「subset-form 直接利用」と「`disjoint_union` 系経由」を独立軸として分類したが、`jointEntropySubset_mono` を後者カテゴリに誤分類。実際は subset-form を直接呼んでいた。

**抜け方**: pivot 実装中の subagent が grep `subsetSplitMEquiv` で全件再列挙して発見、同 pattern (`Finset.disjoint_sdiff` + `Finset.union_sdiff_of_subset h` の 2 行 inline) で migrate。line saving の主因はこの 1 site (-13 行)。

**教訓**: 「ファイル内で同じ補題を複数 site が呼ぶ」inventory はカテゴリ分類ではなく `rg <lemma>` 全件 grep で実数を確認させるべき。CLAUDE.md の「Subagent Inventory of Mathlib Lemmas」ルールは Mathlib 側の API inventory には適用されているが、自前 plumbing 側の call site inventory にも同様の verbatim 縛りを書くべき (今回 plan に書かれていなかった)。

## 5. ボトルネックではなかったもの

- **`MeasurableEquiv.coe_piFinsetUnion : rfl` の defeq 透過性** — Plan のリスク表で「中」と評価していたが実際は「低」。Mathlib 内部の `Equiv.piFinsetUnion_left` proof に付いている `set_option backward.isDefEq.respectTransparency false` (defeq fragility のシグナル) は、`MeasurableEquiv` 層に lift した時点で問題にならなかった。1 行 (`rfl`) で通った。
- **Mathlib API 検索** — loogle indexed binary で 1 query 8.5s × 2 query。事前準備 (CLAUDE.md ルール、index 既存) のおかげ。
- **証明 tactic の選択** — 各 bridge lemma の proof は 3〜5 行 (`coe_piFinsetUnion` 経由で `Equiv` 版の apply lemma を呼ぶだけ)。`simp` / `rfl` / `rw` 以外の出番なし。
- **call site 4 ヶ所の `Finset.disjoint_sdiff` + `union_sdiff_of_subset h` 書き換え** — pivot 後の 4 ヶ所すべてで proof bottleneck ゼロ、機械的置換。
- **コンテキスト長** — 1M context + subagent 委任で圧迫感なし。proof-log 執筆時に subagent 出力をすべてオーケストレータが保持していた。
- **作業者の数学的負荷** — 数学的アイデアが要らない refactor だったため、subagent 委任で完結 (オーケストレータは plan レビュー + pivot 判断のみ)。

## 6. ツール開発への示唆

| 優先度 | 機能 | このセッションで節約できたコスト |
|---|---|---|
| 高 | `subst` 発火条件の事前判定 (依存解析で「変数が片側から完全消去可能か」「依存型を壊さないか」を tactic 起動前に判定) | aux def 設計判断 1 ターン (§4.1) |
| 高 | Mathlib 上流補題への置換 refactor の line-count 見積もり (signature gap penalty を機械的に加算) | 楽観バイアスによる pivot ターン 1 つ (§4.2) |
| 中 | Mathlib `Equiv.<X>` から `MeasurableEquiv.coe_<X>` / apply lemma を機械的に lift 提案 | Pi.lean 手書き 3 lemma 分 (~10 行) |
| 中 | 自前 plumbing 撤去 refactor 時の call site inventory に「`rg <lemma>` 全件 grep」縛りを subagent prompt に強制 | §4.3 の見落とし site (1 site = -13 行の line saving 機会) |
| 低 | 1M context での subagent 連携基盤 | 既に十分 |

## 7. 補足

- 本 proof-log は subagent (planning + 1st implementation + pivot implementation の 3 体) の return summary をオーケストレータが集約して書いた。sub-session の transcript には直接アクセスせず。
- 採らなかった代替案: 「subset-form `subsetSplitMEquiv` を維持したまま `subsetSplitMEquiv_apply` の中身だけ Mathlib `_left/_right` 経由に書き直す」mini-refactor (Plan 撤退ライン #1)。pivot の方が line saving が大きいため不採用。
- 上流 PR 候補: `MeasurableEquiv.coe_piFinsetUnion` / `_apply_left` / `_apply_right` の 3 lemma は Mathlib 本体に上げる価値あり (本 project 単独で抱える必然性なし)。
