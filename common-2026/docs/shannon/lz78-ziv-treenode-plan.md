# LZ78 Ziv combinatorial core — tree-node-context discharge サブ計画 ⛔ PARKED / STALE

> **Parent**:
> - [`lz78-completion-roadmap.md`](lz78-completion-roadmap.md) §1 M3
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「achievability core / 撤退ライン」
>
> **後継 (route 移行先)**: [`lz78-m2-plan.md`](lz78-m2-plan.md) — length-grouping route A

## ⛔ 本計画は PARKED (route B = node-grouping、reject 確定)

**leg 4 の独立調査（inventory [`lz78-m3-treenode-inventory.md`](lz78-m3-treenode-inventory.md) + proof-pivot-advisor、両者機械裏取り）で、本計画の node-grouping route (T1-T5) は reject 確定**。M3 achievability 壁 `ziv_aseventual_le_blockLogAvg₂`（`@residual(wall:lz78-aseventual-ziv)`）の攻略は **length-grouping route A（`lz78-m2-plan.md`）に移行済**。本計画は park（旧 Approach / Phase 詳細は git 履歴に残置、CLAUDE.md plan hygiene）。

### reject 理由 1 — D3 trap で数学的に死ぬ（機械裏取り）

node-grouping の overhead は `c·log(#nodes)`。LZ tree では **#nodes ≈ c**（distinct phrase = node）なので overhead `c·log(#nodes) ≈ c·log c`。sorryAx-free 組合せ核 `lz78PhraseStrings_mul_log_le`（`c·log c ≤ K·n`、`ZivCountingBody.lean:357`）より `(c·log c)/n` は **定数 = main term と同オーダー**で、分母 `n` に対し **vanish しない**。`c = O(n/log n)` を入れても order が残り `entropyRate₂` を超過する誤差を残す → **数学的に細工不能**。これは本計画 旧判断 3（「`c·log c ≤ ∑_v k_v log k_v + c·log(#nodes)` 形」）/ feasibility リスク #1 が `#nodes≈c` で実際に殺される、という確認。

length-grouping route A は overhead が `c·log(#groups)` で **#groups = O(log n)**（同じ長さ ℓ の distinct phrase ≤ |α|^ℓ → 長さ別に分類）なので `(c·log log n)/n = O((log log n)/log n) → 0` で vanish（D3 クリア）。これが唯一の genuine route。

### reject 理由 2 — 「再利用、転記主体」資産は削除済（STALE）

本計画 旧本文が「転記 ~中規模で再利用できる genuine 黒箱」と書いた資産は **commit `f67ec8a`/`602b1ad` で in-tree 削除済（disk 不在、`rg` 0-hit で確認）**:

- `extendCylinder*`（`extendCylinder_measureReal_sum_eq` / `_pairwiseDisjoint` / `iUnion_*` / `measurableSet_*`）= T2 の measure-theoretic 核心
- `condNextSymbol_sum_eq_one`（per-symbol sub-distribution）
- `IsLZ78ZivCombinatorialCore`（旧 core hyp predicate）
- ファイル `LZ78ZivCombinatorics.lean` / `LZ78ZivEntropyBridge.lean`（現行は `LZ78/ZivCountingBody.lean` / `LZ78/ZivEntropyBridge.lean` に再編、内容も別）

= resurrection は転記でなく **~750-1100 行のゼロ再構築 + phantom 依存**。さらに現行 `condPhraseProb`（`ZivEntropyBridge.lean:167`）は **固定 tuple `v` でなく観測 `ω` で parametrize された path-prefix 比**なので、route B が要求する node-context 横断 sub-distribution `∑_a q(node·a|node) ≤ 1` を既存資産から抽出できない（inventory §A finding 1）。worker 不変条件「emit 時 `cur ∈ dict`」も docstring の prose のみで未 lemma 化（inventory §E）、`isLZ78PerPathParsingFactorization_of_pos` は phantom = 未実装（inventory §A finding 3）。

### 凍結 Phase 番号（他文書参照用、本文は git 履歴）

旧 T1（context モデル化 + parent-prefix 抽出）/ T2（per-node sub-distribution）/ T3（distinct → `c log c`、二段 Jensen）/ T4（`-log₂Pₙ` 接続、telescoping）/ T5（core 構築 + headline 再配線）/ V（編入 + 検証）。**T3 の抽象 Jensen grouping atom（`c·log c ≤ ∑_g c_g·log c_g + c·log(#groups)`、`Real.convexOn_mul_log` + `ConvexOn.map_sum_le`）は route A でも decisive gateway atom として再利用される**（group key を node でなく length にすれば D3 を回避する）— 唯一 route A に引き継がれた成果。それ以外（node-context 基盤一式）は破棄。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **route B reject（leg 4、機械裏取り、`lz78-m2-plan.md` 判断ログ #4 と同期）**: node-grouping は D3 trap（overhead `c·log(#nodes) ≈ c·log c` 非vanish）で数学的に死ぬ + 「再利用」資産は `f67ec8a`/`602b1ad` で削除済（STALE）。攻略は length-grouping route A（`lz78-m2-plan.md`、抽象 Jensen gateway atom = `ZivLengthGrouping.lean`）に移行。本計画 park。
