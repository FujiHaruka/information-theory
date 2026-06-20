# LZ78 確定事実台帳

> family `lz78` の確定事実の**単一の真実源**。フォーマット規約 → `CLAUDE.md`「Plan / docs hygiene」。
> プラン本文に同じ事実を再記述しない (散在防止)。プランからはこの台帳の行にリンクする。
> **確信度**: `machine` (機械検証可、コマンド併記) / `loogle-neg` (Found 0、query 併記) / `human-judgment` (解析的壁判断、**過大/過小評価しうる低信頼**)。

## 壁 (未解消、コード `@residual(wall:slug)` が SoT)

slug が code に存在する = 壁未解消。`plan_lint` はこれを照合し「plan が壁扱いだが slug 消失」を STALE 判定する。壁の真偽 (本当に Mathlib 壁か / 実は通れるか) は `human-judgment` なので独立 pivot で再確認する (→ CLAUDE.md「Verification」)。

| 壁 (slug) | 確信度 | 再検証コマンド (slug 存在 = 未解消) | last-verified | 場所 / 備考 |
|---|---|---|---|---|
| `wall:lz78-aseventual-ziv` | human-judgment | `rg '@residual\(wall:lz78-aseventual-ziv\)' InformationTheory/` | 7b0ecbb | **REAL 残 bare sorry = `ziv_aseventual_le_blockLogAvg₂`** (`GreedyParsingImpl.lean:556`、achievability)。threading foundation + tiling 材料化 (`lz78_block_tiling`) は **leg 9 で sorryAx-free + 監査 PASS** (下記達成テーブル)。残 mainline = composition → (W) empirical-profile → (V) diagonalization → (Z) W2 discharge。Q_k measure/AEP/sub-dist + per-context conditional 資産も **既存 sorry-free** → 「Q_k from scratch research-level」は過大評価だった (leg 5 是正)。**known W2 sub-task**: `Lmax = o(n)` a.s. (longest LZ78 phrase が sublinear に伸びる) は achievability wall 層に属し、tiling 層が供給するものではない (boundary conjuncts を実 W2 vanishing に変える役、planner は tiling 層に期待しないこと) |
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
| `markovFactor_eq_of_window_eq` = markovFactor 位置不変性 (n>k 分岐は last k+1 成分のみ依存・絶対位置非依存、kernel index k 固定) | machine | `#print axioms markovFactor_eq_of_window_eq` | ca78b10 | `Core.lean:465`、`[IsFiniteMeasure μ]`。route の土台 = position invariance (同一 last-k window の phrase が同一 conditional に集約される core 補題) |
| `condQkState μ p k (s:Fin k→α)` + `condQkState_sum_le_one` = per-k-state conditional sub-dist (`condQk μ p k k s`、`∑_w ≤ 1`) | machine | `#print axioms condQkState_sum_le_one` | ca78b10 | `Core.lean:490/498`、`[IsProbabilityMeasure μ]`。(k-state,length) grouping が instantiate する per-state sub-dist (`condQk` の k-state 専用 instance) |

### 条件付き context 資産 (`LZ78/ZivCondContext.lean`、leg 5 で建つ — node-context conditional の「第三の量」)

| 主張 | 確信度 | 再検証コマンド | last-verified | 場所 / 型・備考 |
|---|---|---|---|---|
| `condContextProb` = 固定 tuple の conditional `q(symbol\|context)` (cylinder 比) | machine | `rg -n 'def condContextProb' InformationTheory/Shannon/LZ78/ZivCondContext.lean` | cfe518b | `ZivCondContext.lean:151`、`(μ p) {m} (v : Fin m → α) (a : α) : ℝ`。marginal でも path-prefix でもない第三の量 |
| `condContext_sum_le_one` = node-context sub-distribution `∑_a q(v·a\|v) ≤ 1` | machine | `#print axioms condContext_sum_le_one` | cfe518b | `ZivCondContext.lean:174`、`[IsProbabilityMeasure μ]` `(hpos : 0 < P(blockRV m = v))`。**= plan が「次の genuine atom」と呼んでいた量、既に sorry-free 完成**。Kolmogorov consistency `sum_extend_marginal_real_eq` から |
| `condContext_card_mul_log_le_sum_neg_log` = per-context log-sum step | machine | `#print axioms condContext_card_mul_log_le_sum_neg_log` | cfe518b | `ZivCondContext.lean:193`、`(S : Finset α)` `(hPpos)` `(hPsum : ∑ ≤ 1)`。conditional 版 log-sum 不等式 (`group_card_mul_log_le_sum_neg_log` の conditional analogue) |
| `sum_neg_log_condContextProb_path_eq_blockLogAvg` = chain-rule backbone (`∑_{m<n} -log q_cond = n·blockLogAvg`) | machine | `#print axioms sum_neg_log_condContextProb_path_eq_blockLogAvg` | 6accdd2 | `ZivCondContext.lean:292`、`[IsProbabilityMeasure μ]` `(hn : 0<n)` `(hpos)`。**但し full-history context (全 distinct) ゆえ fiber size 1 で trivial → Ziv grouping vehicle にはならない。k=∞ reference として保持** |

### grouping bridge + overhead 制御 (leg 7、route の最難解析ピース2つ)

| 主張 | 確信度 | 再検証コマンド | last-verified | 場所 / 型・備考 |
|---|---|---|---|---|
| `condState_grouping_bound` = (k-state,length) double-fiber grouping bridge + .toReal 橋 (`c·log c ≤ ∑ -log condQkState.toReal + c·log D`) | machine | `#print axioms condState_grouping_bound` | 2b061f6 | `LZ78/ZivCondGrouping.lean:113` (+helper `condQkState_le_one`:63, `sum_condQkState_toReal_le_one`:78)。**.toReal 橋 (iii) 閉鎖**。⚠ overhead は `c·log D` = worst-case で**不十分** (下記 finding) — 単独では M3 を閉じない |
| `empirical_entropy_le_log_mean` = 経験分布エントロピーの平均長上界 (`∑ c_l log(C/c_l) ≤ C·log(N/C) + C`、κ=1、N=∑l·c_l=総長) | machine | `#print axioms empirical_entropy_le_log_mean` | 765a98d | `LZ78/EmpiricalEntropyMean.lean:141` (+helper `logSumInequality`:53, `sum_geom_shift_le_inv`:103)。**overhead 制御の核**。Gibbs (geometric reference θ=1−C/N) 経由。純 Finset/Real |

### threading 配線 (leg 8–9、Phase 2c-ii foundation、tiling 材料化 CLOSED)

threading 分解 `negLogQk(block) = boundary + ∑_phrases -log condQkState(state,phrase)` の **factor-level correspondence + tiling 材料化が両方 sorryAx-free で閉鎖**。残る唯一の open edge = **composition** (`negLogQk_phrase_threading` と `lz78_block_tiling` を `obtain` で繋ぎ tiling-hyp-free・a.s. の block 分解を産出) → その後 (W) empirical-profile → (V) diagonalization → (Z) W2 discharge。

| 主張 | 確信度 | 再検証コマンド | last-verified | 場所 / 型・備考 |
|---|---|---|---|---|
| `markovFactor_blockRV_eq_window` = **gateway atom**: 絶対位置 markovFactor (negLogQk 構成因子) = condQk の相対位置 factor (`markovFactor_eq_of_window_eq` 適用、m≥1 主分岐 + m=0 boundary kernel-branch 直接一致) | machine | `#print axioms markovFactor_blockRV_eq_window` | bf78de9 | `ZivThreading.lean:77`、`[IsFiniteMeasure μ]`。**threading の linchpin**。`k < N` (strict) 要求 |
| `windowState p k pos ω` = trailing k-state (position-coherent with blockRV) | machine | `rg -n 'def windowState' InformationTheory/Shannon/LZ78/ZivThreading.lean` | bf78de9 | `ZivThreading.lean:53` |
| `pmfLogCondMarkov_eq_neg_log_markovFactor` = 決定論橋 `pmfLogCondMarkov i = -log(markovFactor i).toReal` (i>k) | machine | `#print axioms pmfLogCondMarkov_eq_neg_log_markovFactor` | bf78de9 | `ZivThreading.lean:185`。Core の `markovFactor_blockRV_gt` が **private** ゆえ再導出 (気づき: 非 private 化で downstream 各 leg ~25 行節約) |
| `condQk_eq_prod_markovFactor` = `condQk = ∏ 絶対位置 markovFactor` (ℓ 帰納、各 peel で gateway atom 適用) | machine | `#print axioms condQk_eq_prod_markovFactor` | bf78de9 | `ZivThreading.lean:225` |
| `negLogQk_segment_eq_condQkState` = per-phrase segment 恒等式 `∑ pmfLogCondMarkov = -log(condQkState).toReal` (Real.log_prod + ENNReal.toReal_prod で telescope) | machine | `#print axioms negLogQk_segment_eq_condQkState` | bf78de9 | `ZivThreading.lean:273`。`hposfac` (per-position markovFactor>0) = regularity precondition (監査 PASS、bundling でない) |
| `negLogQk_phrase_threading` = block 分解 (tiling 入力下、**leg 8 body fill で sorryAx-free**): `negLogQk = boundary[0,b) + ∑_phrases -log condQkState + trailing[e,n)` | machine | `#print axioms negLogQk_phrase_threading` (stale olean 注意、要 `lake build ...ZivThreading`) | 29280cf | `ZivThreading.lean:335`、`@audit:ok` (`6c8d939`)。tiling (`N`/`hmono`/`hstart`:`k<` strict/`hNe`/`hen`) + `hposfac` (per-pos positivity) = **全 regularity (監査 PASS、非 bundling)**。trailing-boundary 一般化 (`N(last)=e≤n` + `∑Ico e n`) で unfinished tail の `≤`-vs-`=` を吸収 |
| `lz78_parse_tiling_positions` = **tiling 材料化の組合せ核 (leg 9 新、sorryAx-free)**: parse から決定論的 position tiling を産出 (`bAbsorbed = Nat.find` of first cumulative-length > k、`c = parseCount − bAbsorbed`、non-vacuity genuine) | machine | `#print axioms lz78_parse_tiling_positions` | 7b0ecbb | `GreedyLongestPrefix.lean`、`@audit:ok`。tiling の combinatorial core (cumulative-length だけで決まる、substring content 不要) |
| `markovFactor_blockRV_pos_ae` = a.s. positivity `∀ᵐ ω, ∀ pos, 0 < markovFactor (blockRV) pos ω` (leg 9 新、public、sorryAx-free) | machine | `#print axioms markovFactor_blockRV_pos_ae` | 7b0ecbb | `Core.lean`、`@audit:ok`、`cond_singleton_pos_ae` 由来。tiling 結論を a.s. shape にする positivity 供給 |
| `lz78_block_tiling` = **tiling 材料化 (leg 9 CLOSED、sorryAx-free、独立監査 PASS)**: parse から tiling existential を a.s. で産出 (5th existential `Lmax` + boundary conjuncts `n-e ≤ Lmax ∧ b ≤ k+Lmax` 付き) | machine | `#print axioms lz78_block_tiling` (期待 3 axioms、stale olean 注意 → 要 `lake build ...ZivThreading`) | 7b0ecbb | `ZivThreading.lean`、`@audit:ok` (`4e96667`/`5cad40b`/`7b0ecbb`)。**もはや sorry/residual ではない**。署名は **a.s. statement** `∀ᵐ ω ∂μ, ∃ …` (旧 per-ω positivity conjunct は全 ω で偽 = a.s. へ修正、auditor: strengthening-to-truth で downstream-needed conjunct は drop していない)。`bAbsorbed ≤ k+1` (旧 `≤ k` off-by-one 訂正)。substring CONTENT coherence は **不要** (`negLogQk_phrase_threading` が phrase content を `p.obs (N j.castSucc + m) ω` で直読、cumulative-LENGTH 位置のみが効く) |
| `lz78PhraseStringsAux_flatten_conserve` + `lz78PhraseStrings_flatten_prefix` = parse reconstruction invariant (`(parse).flatten ++ tail = input`) | machine | `#print axioms lz78PhraseStrings_flatten_prefix` | 6fed263 | `GreedyLongestPrefix.lean:209/239`。tiling 材料化の step 1 (flatten 保存、fuel 帰納) |
| helpers `lz78PhraseStringsAux_tail_mem` / `lz78PhraseStrings_flatten_tail_mem` / `length_le_foldr_max_of_mem` / `length_flatten_eq_foldr_length` (leg 9 新、sorryAx-free) | machine | `#print axioms lz78PhraseStrings_flatten_tail_mem` | 7b0ecbb | `GreedyLongestPrefix.lean`、tiling materialization 用 List 補助 (phrase 長 bound + flatten 長保存) |
| **composition (next open edge、未着手)**: `∀ᵐ ω, negLogQk = boundary[0,b) + ∑_phrases -log condQkState + trailing[e,n)` (args `μ,p,k,n` のみ、tiling-hyp-free・a.s.) | (未着手) | — | — | `lz78_block_tiling` から `obtain` → `negLogQk_phrase_threading` 適用で `negLogQk_phrase_threading` の tiling/positivity 仮説を a.s. に internalize。**両 atom は sorryAx-free だがまだ wire されていない** |

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
| max-entropy / geometric-distribution-entropy / Gibbs-mean 補題は Mathlib 不在 | loogle-neg | `Real.negMulLog, Finset.sum` Found 0、name "geometric"/"entropy" は binEntropy/qaryEntropy のみ | 765a98d | `empirical_entropy_le_log_mean` は in-project 自製 (log_sum_inequality + geometric reference)。**だが壁ではない、自製済** |

## 判断ログ (この台帳固有)

1. **seed 作成 (2026-06-20、leg 5 後)**: M3 achievability の route 是正を記録。`audit-tags.md` register の旧 prose「Q_k を一から構築する必要があり genuine research-level・数 leg」は**過大評価**。実際には Q_k measure/AEP/sub-dist (Core.lean 7 件) + node-context conditional 資産 (ZivCondContext.lean 4 件、leg 5 `cfe518b`/`6accdd2`) が**全て既存 sorry-free**。残る genuine core は Ziv (k-state,length)-grouping (Cover-Thomas Lemma 13.5.5) + k(n)→∞ diagonal の **grafting** に絞られた (~150–300 行、medium)。
2. **ブリーフ提供の decl 名 2 件を機械裏取りで訂正**: (a) ブリーフの `conditionalEntropyTail_tendsto_entropyRate` は実在せず、真の名は `entropyRate_eq_lim_condEntropy` (`EntropyRate.lean:484`、ファイルは `Shannon/EntropyRate.lean` で `SMB/AlgoetCover/` 配下ではない)。(b) `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` / `sum_qkSingleton_le_one` の process 型は **`StationaryProcess`** (`negLogQk_div_tendsto_condEntropyTail` のみ `ErgodicProcess` 要求)。
3. **route LOCK = markovFactor (condContextProb は不採用、2026-06-20 leg 6)**: M3 grouping vehicle を **markovFactor (有限 k-state) で確定**。leg 6 実装 agent が friction 回避のため condContextProb (full-context) route を「.toReal 摩擦ゼロ + genuine -log Pₙ 到達済みで短い」と推奨したが**却下**。refutation: condContextProb は full-history context ゆえ LZ parse の各 phrase が distinct context → (k-state,length) grouping で各 fiber size 1 → c_l(s)=1 → Jensen grouping `c·log c ≤ ∑ c_l(s)log c_l(s) + c·log D` が `c·log c ≤ 0 + c·log(≈c)` で vacuous (D8)。markovFactor は有限 k-state (|α|^k) で多数 phrase が同一 state 共有 → 非自明 fiber → genuine Ziv counting。.toReal friction は対価だが k(n)→∞ 対角化 (genuine optimality 証明) を買う唯一の道。leg 6 の 4 原子はこの正路の部品。
4. **leg 7 finding — overhead 評価是正 (2026-06-21)**: route lock (leg 6) は「(k-state,length) grouping の overhead `c·log D` は fixed k で `log D / n → 0` ゆえ vanish」としたが、これは検証量を誤っていた。実際の overhead は **`c·log D`** (generic grouping `card_mul_log_le_sum_group_mul_log_add_card_log` の `(∑k)·log(G.card)` 項) で、c = O(n/log n)・worst-case #lengths ~ √n ゆえ `c·log D ~ Θ(n)` で**消えない**。M3 wall docstring 自身が gap を「c·log c ≤ ∑ -log q + **o(n)** length-grouping AEP (D4 ∑qⱼ≈c trap)」と記しており整合 = この o(n) overhead 制御こそ documented wall の本体。**是正**: 正しい overhead は empirical 分布のエントロピー `c·H = c·log c − ∑_g c_g log c_g = ∑_g c_g log(c/c_g)` で、平均長制約 `∑_l l·c_l = n` (平均長 n/c ~ log n) の下 `empirical_entropy_le_log_mean` (765a98d) で `≤ C·log(n/c) + C = o(n)` に抑えられる (C·log(log n) ~ o(n))。**結論: route は壁でなく閉鎖可能 (overhead crux 765a98d sorryAx-free で de-risk 済)。ただし「medium grafting ~150-300行」は過小評価で、threading + empirical-profile 配線 + 対角化が残る multi-leg 作業。`condState_grouping_bound` (2b061f6) は真だが overhead が `c·log D` ゆえ単独では M3 を閉じない — 次 leg は empirical-profile を直接狙い、`c·log D` 形を再利用しない (気づき: ZivLengthGrouping の generic grouping は overhead 推定では empirical_entropy_le_log_mean に supersede される)。**

5. **leg 8 threading foundation (2026-06-21、`bf78de9`/`29280cf`/`6fed263`/`6c8d939`、要点圧縮)**: gateway atom `markovFactor_blockRV_eq_window` + factor-correspondence 5 補題 + `negLogQk_phrase_threading` body fill すべて **sorryAx-free**、tiling 材料化を `lz78_block_tiling` に隔離 (当時は新 1 sorry、honest_residual 監査 PASS)。詳細は達成テーブル「threading 配線」。leg 8 時点の sufficiency caveat (drop した `b`/`n-e` symbol-accounting は downstream-necessary、closure 時に boundary-length conjuncts を結論へ追加要) は **leg 9 で消化** (#6) — 当時の per-phrase substring-coherence 仮説も誤りと判明。

6. **leg 9 tiling 材料化 CLOSED + 3 findings (2026-06-21、`4e96667`/`5cad40b`/`7b0ecbb`)**: `lz78_block_tiling` が **fully CLOSED、sorryAx-free、独立 honesty 監査 PASS (`@audit:ok`)** — もはや sorry/residual ではない。新 sorryAx-free 資産 = `lz78_parse_tiling_positions` (combinatorial core、`GreedyLongestPrefix.lean`) + `markovFactor_blockRV_pos_ae` (a.s. positivity、`Core.lean` public) + List 補助 4 本。**3 findings (機械裏取り、leg 8 caveat を訂正)**: (a) leg 8 の per-ω positivity conjunct は **全 ω で偽** (`markovFactor` at `blockRV` の positivity は `cond_singleton_pos_ae` 由来で a.s. のみ) → 署名を **a.s. statement `∀ᵐ ω ∂μ, ∃ …`** に修正 (auditor: strengthening-to-truth、downstream-needed conjunct は drop なし)。(b) leg 8 の `bAbsorbed ≤ k` は **off-by-one** → `bAbsorbed ≤ k+1` に訂正。(c) **substring CONTENT coherence は不要** (`negLogQk_phrase_threading` が phrase content を `p.obs (N j.castSucc + m) ω` で直読、cumulative-LENGTH 位置のみ効く) → leg 8 の per-phrase substring-coherence atom は over-specified、実核は決定論的 cumulative-length tiling だった。最終署名は 5th existential `Lmax` + boundary conjuncts `n-e ≤ Lmax ∧ b ≤ k+Lmax`。**次 = composition** (両 atom を `obtain` で wire、tiling-hyp-free・a.s. の block 分解を産出)。

## 残る genuine core (次 leg、route LOCK = markovFactor、leg 9 後)

- **(i) k-state threading**: **gateway atom + factor correspondence 5 補題 + `negLogQk_phrase_threading` body fill + tiling 材料化 `lz78_block_tiling` すべて sorryAx-free (leg 8–9、`bf78de9`/`29280cf`/`7b0ecbb`、全監査 PASS)**。**次 atom = composition**: `lz78_block_tiling` から `obtain` → `negLogQk_phrase_threading` 適用で、tiling/positivity 仮説を a.s. に internalize した `∀ᵐ ω, negLogQk = boundary[0,b) + ∑_phrases -log condQkState + trailing[e,n)` (args `μ,p,k,n` のみ) を産出。両 atom は sorryAx-free だがまだ wire されていない。
- **(ii)+(iii) grouping + .toReal**: **`condState_grouping_bound` (2b061f6) 閉鎖**。ただし overhead は `c·log D` で**要 supersede** (上記 finding 4、empirical_entropy_le_log_mean に渡す)。
- **overhead crux**: **`empirical_entropy_le_log_mean` (765a98d) 閉鎖** (overhead 制御の核)。
- **残る本丸 (composition 後の本線)**:
  - **(W) empirical-profile 配線** = grouping を length 単独でなく (state,length) で行い、overhead を `empirical_entropy_le_log_mean` に渡す。平均長 = n/c を c = O(n/log n) から供給。`c·log D` 形 (`condState_grouping_bound`) は単独では閉じないので再利用しない。
    - **known sub-task**: `Lmax = o(n)` a.s. (longest LZ78 phrase が sublinear に伸びる) = `lz78_block_tiling` の boundary conjuncts (`n-e ≤ Lmax ∧ b ≤ k+Lmax`) を実 W2 vanishing に変える鍵。achievability wall 層に属し、tiling 層が供給するものではない (planner は tiling 層に期待しないこと、implementer + auditor 両者の flag)。
  - **(V) 対角化** = `negLogQk/n → H_k` (`negLogQk_div_tendsto_condEntropyTail`)、`H_k → H` (`entropyRate_eq_lim_condEntropy`)、k(n)→∞。
  - **(Z) W2 discharge** = `ziv_aseventual_le_blockLogAvg₂` (`GreedyParsingImpl.lean:556`、唯一の REAL 残 bare sorry `@residual(wall:lz78-aseventual-ziv)`) の sorry を埋める。
