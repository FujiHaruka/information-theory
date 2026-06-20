# LZ78 Ziv combinatorial core — tree-node-context discharge サブ計画 ⚠ 部分 UN-PARK

> **Parent**:
> - [`lz78-completion-roadmap.md`](lz78-completion-roadmap.md) §1 M3
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md) §「achievability core / 撤退ライン」
>
> **本線 (route 統合先)**: [`lz78-m2-plan.md`](lz78-m2-plan.md) — Phase 2c conditional-context (length, finite-context) AEP

## ⚠ 部分 UN-PARK (leg 4 後半 gateway-atom-first probe による精密 characterization)

leg 4 後半の probe で M3 achievability 壁 `ziv_aseventual_le_blockLogAvg₂`（`@residual(wall:lz78-aseventual-ziv)`）は **genuine research-level** と機械裏取りされ、**2 つの単純 grouping が両方 machine-ruled-out** された。これにより本計画は「完全 park」から **部分 un-park** に修正される:

- **un-park: per-node conditional sub-distribution `∑_a q(node·a|node) ≤ 1`（旧 T2）は genuine に必要な核**。leg 4 で確認 — path-prefix `condPhraseProb`（D4 trap）でも marginal（方向逆）でも届かない **第三の量**で、conditional chain rule で `-log Pₙ` に到達するための measure-theoretic 核（codebase + Mathlib 不在）。
- **dead: 旧 T3 の naive node-grouping assembly（`c·log c ≤ ∑_v k_v·log k_v + c·log #nodes`）は D3 trap で死ぬ**。LZ tree で #nodes≈c なので overhead `c·log #nodes ≈ c·log c` = main term と同オーダーで vanish しない。`sorryAx-free 組合せ核 `lz78PhraseStrings_mul_log_le`（`c·log c ≤ K·n`、`ZivCountingBody.lean:357`）で order が残り `entropyRate₂` 超過 = 細工不能。「再利用」と書いた node-context 基盤資産も削除済（dead、下記）。
- **正しい assembly = (length, finite-context)-grouping + conditional q(symbol|context) + AEP**（= `lz78-m2-plan.md` Phase 2c）: conditional sub-distribution（旧 T2 の un-park 核）を length × finite-context で grouping し、finite-context で #contexts 有界にして convexity overhead を vanish（naive node-grouping = #nodes≈c の D3 を回避）、context 深さ→∞ の近似誤差を AEP で制御。= handoff 原典の「variable-depth tree-node AEP」framing は **正しかった**（leg 4 前半が一時 plumbing と誤読したのを再是正）。

本計画は本線でなく、本線 `lz78-m2-plan.md` Phase 2c の core 部品（conditional sub-distribution）の出所を記録する補助計画。攻略の進行は本線で管理する。

### dead: 「再利用、転記主体」資産は削除済（STALE）

本計画 旧本文が「転記 ~中規模で再利用できる genuine 黒箱」と書いた node-context 基盤資産は **commit `f67ec8a`/`602b1ad` で in-tree 削除済（disk 不在、`rg` 0-hit）**:

- `extendCylinder*`（measure-theoretic 核心）/ `condNextSymbol_sum_eq_one`（per-symbol sub-distribution）/ `IsLZ78ZivCombinatorialCore`（旧 core hyp predicate）/ ファイル `LZ78ZivCombinatorics.lean` / `LZ78ZivEntropyBridge.lean`（現行は `LZ78/ZivCountingBody.lean` / `LZ78/ZivEntropyBridge.lean` に再編、内容も別）

= resurrection は転記でなく **~750-1100 行のゼロ再構築 + phantom 依存**。現行 `condPhraseProb`（`ZivEntropyBridge.lean:167`）は固定 tuple `v` でなく観測 `ω` で parametrize された path-prefix 比なので、un-park 核が要求する node-context 横断 conditional sub-distribution `∑_a q(node·a|node) ≤ 1` を既存資産から抽出できない（=ゼロ再構築）。`isLZ78PerPathParsingFactorization_of_pos` は phantom = 未実装。

### un-park / dead の橋渡し（leg 4 後半 sorryAx-free 足場）

旧 T2 の un-park 核に向けた leg 4 の sorryAx-free 足場（本線 `lz78-m2-plan.md` Phase 2a/2b）:

- `ZivLengthGrouping.lean`（commit `c472518`）: 抽象 Jensen grouping（旧 T3 の convexity atom を length-fiber で再利用 = D3 を回避する唯一の形）。
- `ZivMeasureBridge.lean`（commit `d1d55db`）: per-length **marginal** sub-distribution `sum_marginal_real_le_one` + log-sum 機構。marginal なので方向不一致だが、disjoint-cylinder 論法は **conditional cylinder 比** へ拡張可能 = 旧 T2 un-park 核の入口。

### 凍結 Phase 番号（他文書参照用、本文は git 履歴）

旧 T1（context モデル化 + parent-prefix 抽出）/ T2（per-node sub-distribution = **un-park、genuine 核**）/ T3（distinct → `c log c`、二段 Jensen = convexity atom は length-fiber で本線に引継、naive node-grouping assembly は **D3 で dead**）/ T4（`-log₂Pₙ` 接続、telescoping）/ T5（core 構築 + headline 再配線）/ V（編入 + 検証）。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **部分 un-park（leg 4 後半 gateway-atom-first probe、機械裏取り、`lz78-m2-plan.md` 判断ログ #4 と同期）**: 2 つの単純 grouping が両方 machine-ruled-out — (1) node-position-grouping（= 旧 T3 naive assembly）は D3 trap（overhead `c·log #nodes ≈ c·log c` 非 vanish）で dead、(2) marginal-length-grouping は方向不一致（`∑ -log P_marginal ≥ -log Pₙ`、FKG loogle 0-hit）。残る genuine core = conditional-context AEP（旧 T2 per-node conditional sub-distribution `∑_a q(node·a|node) ≤ 1` を中心に、(length, finite-context)-grouping + AEP）= handoff 原典の variable-depth tree-node AEP framing 通り。攻略は本線 `lz78-m2-plan.md` Phase 2c に統合。本計画は旧 T2 核の出所記録の補助計画として un-park（旧 T3 assembly + 削除済 node-context 基盤は dead）。
