# LZ78 確定事実台帳

> family `lz78` の確定事実の**単一の真実源**。フォーマット規約 → `CLAUDE.md`「Plan / docs hygiene」。
> プラン本文に同じ事実を再記述しない (散在防止)。プランからはこの台帳の行にリンクする。
> **確信度**: `machine` (機械検証可、コマンド併記) / `loogle-neg` (Found 0、query 併記) / `human-judgment` (解析的壁判断、**過大/過小評価しうる低信頼**)。

## 壁 (未解消、コード `@residual(wall:slug)` が SoT)

slug が code に存在する = 壁未解消。`plan_lint` はこれを照合し「plan が壁扱いだが slug 消失」を STALE 判定する。壁の真偽 (本当に Mathlib 壁か / 実は通れるか) は `human-judgment` なので独立 pivot で再確認する (→ CLAUDE.md「Verification」)。

| 壁 (slug) | 確信度 | 再検証コマンド (slug 存在 = 未解消) | last-verified | 場所 / 備考 |
|---|---|---|---|---|
| `wall:lz78-aseventual-ziv` | human-judgment | `rg '@residual\(wall:lz78-aseventual-ziv\)' InformationTheory/` | 6accdd2 | `GreedyParsingImpl.lean` `ziv_aseventual_le_blockLogAvg₂` (achievability)。**残る genuine core = Ziv (k-state,length)-grouping (Cover-Thomas Lemma 13.5.5) + k(n)→∞ diagonal の grafting**。Q_k measure/AEP/sub-dist 資産 + per-context conditional 資産は **既存 sorry-free** (下記達成テーブル) → 「Q_k from scratch research-level」は**過大評価だった** (leg 5 で是正) |
| `wall:lz78-converse-aseventual` | human-judgment | `rg '@residual\(wall:lz78-converse-aseventual\)' InformationTheory/` | 6accdd2 | `GreedyParsingImpl.lean` `lz78GreedyImpl_converse_ae` (M4 Barron a.s. lift)。本台帳の achievability 是正対象外、依然 high risk |

## 達成 (proof-done / sorryAx-free — キャッシュでなく再導出レシピ)

P1 規約により「X は sorryAx-free」を prose で確定キャッシュしない。下の行は**再検証レシピ + 最後に通った commit**であって、信用する代わりに必要時に再実行する。各 `#print axioms` の期待出力 = `[propext, Classical.choice, Quot.sound]`。

### Q_k 資産 (kth-order Markov 測度、`SMB/AlgoetCover/Core.lean`、SMB 内部足場として既存)

| 主張 | 確信度 | 再検証コマンド | last-verified | 場所 / 型・備考 |
|---|---|---|---|---|
| `markovFactor` = k-Markov per-step conditional kernel mass | machine | `rg -n 'def markovFactor' InformationTheory/Shannon/SMB/AlgoetCover/Core.lean` | 6accdd2 | `Core.lean:243`、`(μ p k n) (y : Fin (n+1) → α) : ℝ≥0∞`、`[IsFiniteMeasure μ]` `(p : StationaryProcess μ α)`。`n≤k` は full prefix、`n>k` は last-k window |
| `qkSingleton` = k-Markov joint mass `∏ markovFactor` (recursive) | machine | `rg -n 'def qkSingleton' InformationTheory/Shannon/SMB/AlgoetCover/Core.lean` | 6accdd2 | `Core.lean:258`、`(μ p k) : (n:ℕ) → (Fin n → α) → ℝ≥0∞`、`[IsFiniteMeasure μ]` `(p : StationaryProcess μ α)` |
| `sum_qkSingleton_le_one` = per-path sub-distribution `∑_y qk n y ≤ 1` | machine | `#print axioms sum_qkSingleton_le_one` | 6accdd2 | `Core.lean:267`、`[IsProbabilityMeasure μ]` `(p : StationaryProcess μ α)`、`ℝ≥0∞`-値。内部 (327-361) に per-state `∑_a markovFactor(snoc z a)=1` (`IsMarkovKernel`) |
| `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` = joint↔AEP 橋 | machine | `#print axioms qkSingleton_blockRV_eq_ofReal_exp_negLogQk` | 6accdd2 | `Core.lean:461`、`[IsProbabilityMeasure μ]` `(p : StationaryProcess μ α)`、a.s. `qk(blockRV n ω) = ofReal(exp(-negLogQk))` |
| `negLogQk` = `-log Q_k(blockRV n ω)` = `∑_{i<n} pmfLogCondMarkov` | machine | `rg -n 'def negLogQk' InformationTheory/Shannon/SMB/AlgoetCover/Core.lean` | 6accdd2 | `Core.lean:200`、`[IsFiniteMeasure μ]` `(p : StationaryProcess μ α)` |
| `negLogQk_div_tendsto_condEntropyTail` = H_k AEP (`negLogQk/n → H_k` a.s.) | machine | `#print axioms negLogQk_div_tendsto_condEntropyTail` | 6accdd2 | `Core.lean:208`、`@[entry_point]`、`[IsProbabilityMeasure μ]` **`(p : ErgodicProcess μ α)`** |
| `entropyRate_eq_lim_condEntropy` = H_k → H (`Tendsto (conditionalEntropyTail μ p) atTop (𝓝 (entropyRate μ p))`) | machine | `#print axioms entropyRate_eq_lim_condEntropy` | 6accdd2 | `EntropyRate.lean:484` (ファイルは `InformationTheory/Shannon/EntropyRate.lean`)、`@[entry_point]`、`[IsProbabilityMeasure μ]` `(p : StationaryProcess μ α)`。**nat 単位** (`entropyRate`、`entropyRate₂` ではない) |
| `markovFactor_sum_eq_one` = per-state markovFactor は genuine 確率分布 (`∑_a markovFactor(snoc z a) = 1`、任意 prefix `z` で start 非依存) | machine | `#print axioms markovFactor_sum_eq_one` | 2374ecd | `Core.lean:271`、`[IsProbabilityMeasure μ]` `(p : StationaryProcess μ α)`。`sum_qkSingleton_le_one` 内部 `h_inner` を standalone 抽出 (leg 6 gateway atom)。**conditional log-sum の正方向 enabler** (start 非依存ゆえ非空起点でも効く) |
| `markovFactor_sum_subset_le_one` = per-state subset sub-dist (`∑_{a∈T} markovFactor ≤ 1`) | machine | `#print axioms markovFactor_sum_subset_le_one` | 2374ecd | `Core.lean:447`、subset sum ≤ full sum = 1 |
| `condQk` = fixed-prefix conditional product (`∏ markovFactor` from prefix `z : Fin start → α`) | machine | `rg -n 'def condQk' InformationTheory/Shannon/SMB/AlgoetCover/Core.lean` | 2374ecd | `Core.lean:345`、`(μ p k start) (z : Fin start → α) : (ℓ)→(Fin ℓ→α)→ℝ≥0∞`、recursive (qkSingleton と同型) |
| `condQk_sum_le_one` = fixed-prefix conditional product sub-distribution (`∑_w condQk z ℓ w ≤ 1`) | machine | `#print axioms condQk_sum_le_one` | 2374ecd | `Core.lean:364`、`[IsProbabilityMeasure μ]`。`sum_qkSingleton_le_one` の**非空起点一般化** (induction on ℓ、各ステップ markovFactor_sum_eq_one)。**(k-state,length) grouping が instantiate する per-fixed-context sub-dist** |

### 条件付き context 資産 (`LZ78/ZivCondContext.lean`、leg 5 で建つ — node-context conditional の「第三の量」)

| 主張 | 確信度 | 再検証コマンド | last-verified | 場所 / 型・備考 |
|---|---|---|---|---|
| `condContextProb` = 固定 tuple の conditional `q(symbol\|context)` (cylinder 比) | machine | `rg -n 'def condContextProb' InformationTheory/Shannon/LZ78/ZivCondContext.lean` | cfe518b | `ZivCondContext.lean:151`、`(μ p) {m} (v : Fin m → α) (a : α) : ℝ`。marginal でも path-prefix でもない第三の量 |
| `condContext_sum_le_one` = node-context sub-distribution `∑_a q(v·a\|v) ≤ 1` | machine | `#print axioms condContext_sum_le_one` | cfe518b | `ZivCondContext.lean:174`、`[IsProbabilityMeasure μ]` `(hpos : 0 < P(blockRV m = v))`。**= plan が「次の genuine atom」と呼んでいた量、既に sorry-free 完成**。Kolmogorov consistency `sum_extend_marginal_real_eq` から |
| `condContext_card_mul_log_le_sum_neg_log` = per-context log-sum step | machine | `#print axioms condContext_card_mul_log_le_sum_neg_log` | cfe518b | `ZivCondContext.lean:193`、`(S : Finset α)` `(hPpos)` `(hPsum : ∑ ≤ 1)`。conditional 版 log-sum 不等式 (`group_card_mul_log_le_sum_neg_log` の conditional analogue) |
| `sum_neg_log_condContextProb_path_eq_blockLogAvg` = chain-rule backbone (`∑_{m<n} -log q_cond = n·blockLogAvg`) | machine | `#print axioms sum_neg_log_condContextProb_path_eq_blockLogAvg` | 6accdd2 | `ZivCondContext.lean:292`、`[IsProbabilityMeasure μ]` `(hn : 0<n)` `(hpos)`。**但し full-history context (全 distinct) ゆえ fiber size 1 で trivial → Ziv grouping vehicle にはならない。k=∞ reference として保持** |

### LZ78 組合せ核 + 足場 (既存、sorry-free)

| 主張 | 確信度 | 再検証コマンド | last-verified | 場所 / 備考 |
|---|---|---|---|---|
| `lz78PhraseStrings_mul_log_le` (`c·log c ≤ K·n`) sorryAx-free | machine | `#print axioms lz78PhraseStrings_mul_log_le` | 6accdd2 | `ZivCountingBody.lean`、Ziv 組合せ核 (overhead `c·log #nodes ≈ c·log c` 非 vanish = D3 を実際に殺す) |
| `entropyRate₂ = entropyRate / Real.log 2` は実 def (units fix `55e1cd9`) | machine | `rg -n 'def entropyRate₂' InformationTheory/Shannon/EntropyRate.lean` | 6accdd2 | `EntropyRate.lean:76`、`@[entry_point]`、`(p : StationaryProcess μ α)`。headline + 2壁の target |

## Mathlib 不在 / route 確定 (loogle Found 0 / 機械裏取り)

| 主張 | 確信度 | query / コマンド | last-verified | 備考 |
|---|---|---|---|---|
| FKG/positive-association (marginal で `-log Pₙ` を上から押さえる) は Mathlib 不在 | loogle-neg | FKG/positive-association loogle 0-hit | — | D8 (marginal-length-grouping 方向不一致) の根拠。`∑ -log P_marginal ≥ -log Pₙ` (memory で逆向き)、conditional 必須 |
| marginal-length-grouping = 方向不一致 (`∑ -log P_marginal ≥ -log Pₙ`) | human-judgment | chain rule `q_cond ≥ P_marginal` + 上記 FKG 0-hit | — | iid で等号、memory で逆、Dirac で両 0 alive。D8 |
| node-position-grouping = D3 trap (overhead `c·log #nodes ≈ c·log c` 非 vanish) | machine | `#print axioms lz78PhraseStrings_mul_log_le` (`c·log c ≤ K·n`) | 6accdd2 | #nodes≈c が D3 を実際に殺す |
| path-prefix `condPhraseProb` route = dead-start (`∑ⱼ qⱼ ≈ c`、0 consumers) | machine | `scripts/dep_consumers.sh InformationTheory.Shannon.condPhraseProb` | — | D4。orphan 確認済 |

## 判断ログ (この台帳固有)

1. **seed 作成 (2026-06-20、leg 5 後)**: M3 achievability の route 是正を記録。`audit-tags.md` register の旧 prose「Q_k を一から構築する必要があり genuine research-level・数 leg」は**過大評価**。実際には Q_k measure/AEP/sub-dist (Core.lean 7 件) + node-context conditional 資産 (ZivCondContext.lean 4 件、leg 5 `cfe518b`/`6accdd2`) が**全て既存 sorry-free**。残る genuine core は Ziv (k-state,length)-grouping (Cover-Thomas Lemma 13.5.5) + k(n)→∞ diagonal の **grafting** に絞られた (~150–300 行、medium)。
2. **ブリーフ提供の decl 名 2 件を機械裏取りで訂正**: (a) ブリーフの `conditionalEntropyTail_tendsto_entropyRate` は実在せず、真の名は `entropyRate_eq_lim_condEntropy` (`EntropyRate.lean:484`、ファイルは `Shannon/EntropyRate.lean` で `SMB/AlgoetCover/` 配下ではない)。(b) `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` / `sum_qkSingleton_le_one` の process 型は **`StationaryProcess`** (`negLogQk_div_tendsto_condEntropyTail` のみ `ErgodicProcess` 要求)。
3. **route LOCK = markovFactor (condContextProb は不採用、2026-06-20 leg 6)**: M3 grouping vehicle を **markovFactor (有限 k-state) で確定**。leg 6 実装 agent が friction 回避のため condContextProb (full-context) route を「.toReal 摩擦ゼロ + genuine -log Pₙ 到達済みで短い」と推奨したが**却下**。refutation: condContextProb は full-history context ゆえ LZ parse の各 phrase が distinct context → (k-state,length) grouping で各 fiber size 1 → c_l(s)=1 → Jensen grouping `c·log c ≤ ∑ c_l(s)log c_l(s) + c·log D` が `c·log c ≤ 0 + c·log(≈c)` で vacuous (D8)。markovFactor は有限 k-state (|α|^k) で多数 phrase が同一 state 共有 → 非自明 fiber → genuine Ziv counting。.toReal friction は対価だが k(n)→∞ 対角化 (genuine optimality 証明) を買う唯一の道。leg 6 の 4 原子はこの正路の部品。

## 残る genuine core (次 leg、route LOCK = markovFactor)

残る genuine core = (i) **k-state threading** (markovFactor 位置不変性/stationarity: 同一 last-k context の phrase が同一 conditional に集約される補題、未配線、最大障害)、(ii) **(k-state,length) double-fiber grouping** (`card_mul_log_le_sum_group_mul_log_add_card_log` を `ι = state×length` で再利用)、(iii) **.toReal 橋** (markovFactor 積 ℝ≥0∞ → `group_card_mul_log_le_sum_neg_log` の ℝ + 正値性)、(iv) **telescoping → negLogQk** (qkSingleton 再帰 def そのもの、exact)、(v) **k(n)→∞ 対角化** (`negLogQk_div_tendsto_condEntropyTail` → `entropyRate_eq_lim_condEntropy`)。
