# LZ78 passthrough scaffolding consolidation plan

**Parent**: `docs/textbook-roadmap.md` (Ch.13 Universal Coding)

## Context

LZ78 漸近最適性の核心 (Ziv achievability 上界 / converse 下界 / SMB sandwich) が現状 **2 形で重複 publish** されている:

- **(A)** `Basic.lean` §2 passthrough predicate 3本 — statement-only `def : Prop`、tier-4 legacy `@audit:closed-by-successor(textbook-roadmap-m3-m4-scope-out)`:
  - `IsZivInequalityPassthrough` (`Basic.lean:246`) = `∀ᵐ ω, limsup (lz/n) ≤ entropyRate`
  - `IsLZ78ConversePassthrough` (`:275`) = `∀ᵐ ω, entropyRate ≤ liminf (lz/n)`
  - `IsSMBSandwichPassthrough` (`:302`) = `∀ᵐ ω, Tendsto (blockLogAvg) (𝓝 entropyRate)`
- **(B)** `GreedyParsingImpl.lean` 新 sorry lemma 2本 (doctrine-proper tier-2、commit `3ff5b79`):
  - `lz78GreedyImpl_converse_ae` — `@residual(wall:lz78-converse-aseventual)`
  - `lz78GreedyImpl_achievability_ae` — `@residual(wall:lz78-aseventual-ziv)`

(B) が doctrine-proper 後継。2026-06-20 監査 + consumer graph (`dep_consumers.sh`) で **(A) は全て dead scaffolding** と確定:

- `IsLZ78ConversePassthrough` / `IsSMBSandwichPassthrough` = **direct consumer 0 (dead)**
- `IsZivInequalityPassthrough` = 唯一の consumer `IsLZ78PhraseCountAsymptotic.of_passthrough` (`ConverseAsymptotic.lean:175`、`@[entry_point]`) が `_h` を **discard して `IsLZ78PhraseCountAsymptotic.refl` を返す dead-hyp + trivial-結論 bridge** (`_h` は使われない)

## Approach

dead scaffolding を物理削除し、scope-out statement を (B) の sorry lemma 2本に一本化する。2 predicate は consumer 0 で直接削除、3つ目は唯一の consumer (dead-hyp bridge) ごと削除。SMB sandwich は SMB 完成済み (`shannon_mcmillan_breiman`) なので独立 predicate 不要。これは proof-done を進めない **honesty hygiene cleanup** — tier-4 legacy 除去 + (A)/(B) drift 防止。**実 sorry 数は不変 (2)**、entry_point 数は `of_passthrough` 削除分だけ減る。

## Steps

1. `IsLZ78PhraseCountAsymptotic.of_passthrough` (`ConverseAsymptotic.lean:174-181`) 削除 — `_h` discard の dead-hyp scaffolding。結論 refl は `IsLZ78PhraseCountAsymptotic.refl` で直接得られる。下流に `of_passthrough` の term-level consumer があれば refl 直接呼びに書換 (削除前に `dep_consumers.sh` 確認)。
2. `IsZivInequalityPassthrough` (`Basic.lean:246`) 削除 — (1) で唯一の consumer 消失。
3. `IsLZ78ConversePassthrough` (`:275`) / `IsSMBSandwichPassthrough` (`:302`) 削除 — consumer 0。
4. `Basic.lean` §2 docstring (file-level line 30-39 + statement-level 49-90 周辺) 更新 — passthrough 群削除を反映、漸近最適性核心は GreedyParsingImpl の sorry lemma 2本が SoT と明記。
5. `ZivInequality.lean:298` / `GreedyParsing.lean` §7 の passthrough 言及 bridge (`.of*`) が同型 dead-hyp か `dep_consumers.sh` で確認 → 削除 or 整理。
6. 検証: `lake env lean` (LZ78 file 群 silent)、`#print axioms` で entry_point 群が不変 (base 汎用補題 sorryAx-free / `_with_greedy_impl` honest sorry)、実 sorry 数 = 2 不変 (`rg "^\s*sorry\s*$|:= by sorry$|by sorry$|:= sorry$" InformationTheory/Shannon/LZ78/ | wc -l`)。

## Blast radius / 注意

- 全て LZ78 file 内。外部 consumer なし (2 predicate は consumer 0、`IsZivInequalityPassthrough` は dead-hyp bridge のみ)。
- `of_passthrough` は `@[entry_point]` なので削除で entry_point カウントが減る。下流呼び出しがあれば `IsLZ78PhraseCountAsymptotic.refl` 直接呼びに書換。
- ステップ 5 の ZivInequality/GreedyParsing bridge は構造未確認 — 実装時に `dep_consumers.sh` で dead 確認してから削除。dead でなければ scope 縮小 (本 plan は dead 部分のみ)。

## Honesty 利点

scope-out statement が GreedyParsingImpl の sorry lemma 2本に一本化 → tier-4 legacy passthrough 3本 + dead-hyp bridge を消去、(A)/(B) の drift 防止、`rg '@residual(wall:lz78'` 集計が 2 sorry に集約されて綺麗。漸近最適性の「honest 残課題マーカー」が単一 SoT になる。
