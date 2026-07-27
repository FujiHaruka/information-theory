# BC family — settled-facts ledger

> family `bc` (broadcast channel) の確定事実の**単一の真実源**。フォーマット規約 →
> `CLAUDE.md`「Plan / docs hygiene」。列 = claim / confidence / 再検証コマンド /
> last-verified (commit) / notes。
> confidence: `machine` (axiom/sorry 機械検証、再検証コマンド必須) / `loogle-neg` (Found 0、query 併記) /
> `human-judgment` (解析的判断・数値実験、低信頼、独立 pivot で再確認)。
> **再導出が高価なものだけ**を置く。`#print axioms` / `rg` / `dep_consumers.sh` で安く引けるもの
> (どの宣言が sorryAx-free か、どの包含が無条件か等) は**キャッシュせず毎回引き直す** (re-derive > cache)。
> 親 plan: [`bc-general-region-plan.md`](bc-general-region-plan.md)。

## 負の判定 (目標命題が偽 — 再導出が高価ゆえ台帳に置く)

| claim | confidence | 再検証コマンド | last-verified | notes |
|---|---|---|---|---|
| **`martonRegionUnion` (共通補助変数 `U₀` を持たない Marton 内界) は劣化 BSC 対ですら `bcCapacityRegion` より真に小さい。したがって `bcOuterRegionUV W ⊆ martonRegionUnionFS W` は偽** | `human-judgment` | `python3 docs/shannon/bc-marton-union-gap-check.py` (要 numpy / scipy、**全体で 5 分超** — 多点再スタートの Nelder–Mead を補助アルファベットごとに回すため。sim の閉形式照合だけなら `check_sim()` 単体で数秒)。確認するのは (1) 閉形式照合 4 項目が 10 桁一致、(2) 劣化 BSC 対の表で最小スラックが全 `β` / 全補助アルファベットで負、(3) 退化境界 2 本でちょうど 0 | `9a41c3b7` | 数値実験であって Lean の機械検証ではない (CLAUDE.md の 3 値のうち最も保守的な `human-judgment` を採る)。実験設計と結果表は [`bc-lessnoisy-equality-inventory.md`](bc-lessnoisy-equality-inventory.md) §Q1。要点: 劣化 BSC 対 (`q=0.1`, `p=0.25`) の superposition corner `(I(X;Y₁∣U), I(U;Y₂))` は `bc_capacity_subset_uv` により外界に入るが、`martonRegionUnion` の 3 制約の最小スラックが補助アルファベット `(2,2)`〜`(5,5)` で一様に約 `-0.013` に頭打ちし、closure でも跨げない (union の任意の点との距離 ≥ `0.0129/√2`)。sim は Lean の def (`Marton/Setup.lean` の `martonInfo₁/₂/V₁V₂`、`Achievability/Setup.lean` の `bcInfo₁/₂`、`Shannon/Bridge.lean` の `entropy`) から逐語対応させ、閉形式と 10 桁一致することを先に確認済 (CLAUDE.md「小ケースの sim で FALSE を判定するときは先に実 def と照合する」)。構造的な原因は `martonRegionUnion` が EGK Thm 8.3 (private message のみ) の形で共通補助 `U₀` を持たないこと。**この判定が撤退ライン L-BCO8 を無効化し、内界を superposition へ差し替えさせた** (親 plan 判断ログ 18) |
