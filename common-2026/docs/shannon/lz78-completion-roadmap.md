# LZ78 漸近最適性 完遂ロードマップ (incremental)

> 派生元: `docs/textbook-roadmap.md` 判断ログ #6 (詳細経緯は `git log -- docs/textbook-roadmap.md` の 2026-05-26 ロードマップ整理前 commit、特に旧 #17–#26 の Huffman/LZ78 grind 履歴)。
> 目的: **T4-A LZ78 (Cover–Thomas Thm 13.5.3) を標準B (無条件機械検証) で完遂**。
> 方針: `/goal` 一発完遂ループではなく、**各マイルストーンが genuine・committable・verifiable な単独 deliverable** となる少しずつ確実な進行。M1→M5 の順で、前段が次段の足場になる。

主定理: stationary ergodic source に対し圧縮率 `(1/n)·lz(X^n) → H` (base-2 entropy rate) a.s.

---

## 0. 現状 (2026-06-20、符号長 def-fix + units-mismatch fix 後)

**headline は type-check done であって proof done でない。** entry_point
`lz78_asymptotic_optimality_with_greedy_impl`
(`InformationTheory/Shannon/LZ78/GreedyParsingImpl.lean`) は genuine 命題で、
仮説引数は `μ`, `p` のみ。`#print axioms` の sorryAx 依存は genuine M3/M4 壁 2本
経由のみ (`h_bdd_above` は内製 discharge 済 = 引数から除去、commit `a1ae108`)。
**headline + 2壁の target は base-2 (bit) entropy rate `entropyRate₂` であって
nat 単位の `entropyRate` ではない** (units-mismatch defect 修正後、下記確定事実)。
SoT はコード側タグ (`@residual(wall:...)`)、本節は二次。

### 確定事実 (符号長 def-fix `5d08566` → units-mismatch fix `55e1cd9`)

1. **符号長 = genuine longest-prefix parse 化済**。`lz78GreedyImplEncodingLength n x`
   = genuine distinct phrase count `c = (lz78PhraseStrings (List.ofFn x)).length` を
   語数とする `c · bitLength c |α|`。以前のダミー1シンボル parse (count=n, rate 発散)
   は削除済。`c ≤ n`、genuine Ziv `c·log c ≤ K·n` (`lz78PhraseStrings_mul_log_le`、
   sorryAx-free) で rate は `O(1)`。符号長は **base-2 code** (`bitLength = Nat.log 2 …`)
   ゆえ per-symbol rate `lz78GreedyImplEncodingLength/n` は **bit 単位**。
2. **bit-vs-nat units defect を発見・`entropyRate₂` 化で修正** (commit `55e1cd9`、
   再監査 PASS)。符号長 def-fix 後、独立監査が **second defect = bit-vs-nat units
   mismatch** を発覚: `lz78GreedyImplEncodingLength/n` は bit-rate だが、headline +
   2壁の sandwich target が nat 単位の `entropyRate` のままで、正entropy源 A≥2 では
   `limsup = log₂A > logA` = **false-statement** (prior audit `9b09790` はこの units
   ずれを見落とし overturn された)。`99acb58` で `@audit:defect(false-statement)`
   確定 → `55e1cd9` で headline + 2壁の target を `entropyRate₂ = entropyRate/Real.log 2`
   (bit) に置換し TRUE-as-framed に修正、再監査 PASS。**sandwich target は `entropyRate₂`**
   で、`lz78GreedyImplEncodingLength/n` (bit) の真の極限 (`A=2` で `→ 1` 等) と整合する。
3. **2 headline sorry = genuine M3/M4 壁** (`GreedyParsingImpl.lean §3`、target =
   `entropyRate₂`):
   - `lz78GreedyImpl_converse_ae` (`entropyRate₂ ≤ liminf (lz/n)`)
     = `@residual(wall:lz78-converse-aseventual)` (M4 Barron a.s. lift)。
   - `lz78GreedyImpl_achievability_ae` (`limsup (lz/n) ≤ entropyRate₂`)
     = `@residual(wall:lz78-aseventual-ziv)` (M3 conditional-context Ziv 不等式)。
   - いずれも符号データ (`μ`, `p`) のみを取る genuine 命題 (load-bearing hyp なし)。
     `entropyRate₂` target で **TRUE-as-framed** (units fix で TRUE 化しただけで
     discharge ではない、a.s.-eventual Ziv/converse 内容は未証明)。ダミー parse 時代の
     defect は def-fix で、bit-vs-nat units defect は `entropyRate₂` 化で解消済。
4. **M3 壁の route 是正 = Q_k grafting (leg 5、2026-06-20、機械裏取り、本 leg 3 度目の修正)**:
   leg 4 後半は genuine core を「conditional-context AEP を一から構築 (Q_k from scratch、
   research-level・数 leg)」と characterize したが、これも **過大評価だった**。leg 5 で
   **kth-order Markov 測度 Q_k の measure/AEP/sub-distribution + node-context conditional 資産が
   既存 sorry-free** と機械裏取りされた ([lz78-facts.md](lz78-facts.md) 達成テーブルが SoT):
   - **Q_k 資産 (`SMB/AlgoetCover/Core.lean` 7 件、SMB 内部足場)**: `markovFactor` (per-step
     conditional kernel mass) / `qkSingleton` (joint mass `∏ markovFactor`) / `sum_qkSingleton_le_one`
     (per-path sub-distribution、内部に per-state `∑_a markovFactor=1` = `IsMarkovKernel`) /
     `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` (joint↔AEP 橋) / `negLogQk` /
     `negLogQk_div_tendsto_condEntropyTail` (H_k AEP `negLogQk/n → H_k`) /
     `entropyRate_eq_lim_condEntropy` (H_k→H、`EntropyRate.lean:484`、nat 単位)。
   - **node-context conditional 資産 (`LZ78/ZivCondContext.lean` 4 件、leg 5 `cfe518b`/`6accdd2`)**:
     `condContextProb` (conditional q(symbol|context) = 第三の量) / `condContext_sum_le_one`
     (**旧「次の genuine atom」= node-context sub-distribution `∑_a q(v·a|v)≤1`、既に sorry-free 完成**) /
     `condContext_card_mul_log_le_sum_neg_log` (per-context log-sum step) / chain-rule backbone
     `sum_neg_log_condContextProb_path_eq_blockLogAvg` (`∑ -log q_cond = n·blockLogAvg`、**但し
     full-history context = 全 distinct で fiber size 1 = trivial、grouping vehicle にはならず
     k=∞ reference のみ**)。
   - **残る genuine core = Ziv (k-state, length)-grouping (Cover-Thomas Lemma 13.5.5) + k(n)→∞
     diagonal の grafting** (~150–300 行、medium、唯一残る新規)。`(c·log₂c)/n ≤ negLogQk/n +
     overhead_k → H_k`、k→∞ で `H_k → H = entropyRate₂`。**vehicle は per-step markovFactor
     conditional** (joint qkSingleton を per-phrase marginal にするのは leg 4 marginal route と
     同じ方向逆 dead-end = D8 反復、禁止)。両単純 grouping (node-position D3 / marginal D8) は依然
     machine-ruled-out (再探索禁止、§2)。
   - gateway (単位整合) は plumbing で closed (`lz78_impl_bitrate_le_clogc_plus_overhead`、
     sorryAx-free)、convexity grouping (`ZivLengthGrouping.lean`) + marginal sub-distribution 橋
     (`ZivMeasureBridge.lean`) + node-context conditional (`ZivCondContext.lean`) も sorryAx-free
     (necessary scaffolding、§0 genuine 足場テーブル)。壁 `wall:lz78-aseventual-ziv` は honest に維持。
     treenode plan は **部分 un-park** (旧 T2 conditional sub-distribution = leg 5 で `condContext_sum_le_one`
     として建った、旧 T3 naive node-grouping assembly は D3 で dead、§4)。詳細 = §1 M3 / §3 / sub-plan
     [`lz78-m2-plan.md`](lz78-m2-plan.md) 判断ログ #4。
5. **`h_bdd_above` = 内製 discharge 済** (commit `a1ae108`、独立監査 all OK)。
   rate の `IsBoundedUnder (·≤·)` witness を proof body 内の `have` で構成し、
   **headline の仮説引数から除去した** (引数は `μ`, `p` のみ)。`O(1)` per-symbol
   rate 上界 `lz78_impl_rate_le_const` (sorryAx-free) を内製。当初 self-build 要と
   見ていた `Nat.log↔Real.log` bridge は Mathlib 既存 `Real.natLog_le_logb` で
   解決 (loogle Found 0 は誤判定、`docs/shannon/lz78-headline-bdd-discharge-plan.md`)。
6. **完遂条件 = headline sorryAx-free** (M3 + M4 discharge で達成)。

### genuine 済の足場 (sorryAx 非依存・commit 済)

| 層 | file | 内容 |
|---|---|---|
| 符号長 + parent bridge | `GreedyParsingImpl.lean` §1-§2 | genuine longest-prefix 符号長 + CT 13.5.2 bit-length 上界 (`c ≤ n` × `bitLength` 単調)、per-symbol rate 上界・非負 |
| Ziv 組合せ核 | `ZivCountingBody.lean` §4 | `lz78PhraseStrings_mul_log_le` (`c·log c ≤ K·n`)、`lz78PhraseStrings_count_isBigO` (`c = O(n/log n)`) |
| convexity grouping (leg 4) | `LZ78/ZivLengthGrouping.lean` | 抽象 Jensen grouping `card_mul_log_le_sum_group_mul_log_add_card_log` + LZ 長さ別 `lz78PhraseStrings_card_mul_log_le_sum_length_group` (両 sorryAx-free、commit `c472518`)。M2 Phase 2a、necessary scaffolding |
| marginal sub-dist 橋 (leg 4) | `LZ78/ZivMeasureBridge.lean` | per-length marginal sub-distribution `sum_marginal_real_le_one` + per-group log-sum `group_card_mul_log_le_sum_neg_log` + 集約 `lz78PhraseStrings_mul_log_le_sum_neg_log_marginal_add_overhead` (sorryAx-free、commit `d1d55db`)。M2 Phase 2b。**marginal なので方向不一致で `-log Pₙ` に届かない**が、sub-distribution + log-sum 機構は conditional 版に転用可 |
| base-2 単位 | `EntropyRate.lean` + `LZ78/ZivEntropyBridge.lean` | `entropyRate₂ = entropyRate / Real.log 2` を `EntropyRate.lean` に `@[entry_point]` def 化 (units fix `55e1cd9` で旧 prose のみ → 実 def 化、headline + 2壁の target)。`ZivEntropyBridge.lean` は `blockLogAvg₂ = blockLogAvg / log 2` 等の unit-conversion prose (lz=bit / entropy=nat 単位整合) |
| 無条件 SMB AEP (M3 限界供給) | `SMB/AlgoetCover/Liminf.lean` | `shannon_mcmillan_breiman` (`∀ᵐ ω, blockLogAvg μ p n ω → entropyRate μ p`、sorry-free entry_point)。M3 の **新たな限界対象** — `-log₂Pₙ/n → H₂` を free で供給 (旧 tree-node 基盤を obsolete 化、§3 校正参照) |
| converse UD-object (M1 済) | `LZ78/ConverseUDObject.lean` | 汎用 `uniquelyDecodable_of_constantLength` + 実 LZ78 token code UD → McMillan 期待値 converse `entropyD 2 P ≤ E[L]=K` (M4 入力) |
| **Q_k 資産 (kth-order Markov 測度、M3 grafting の足場)** | `SMB/AlgoetCover/Core.lean` + `EntropyRate.lean` | `markovFactor` (per-step conditional kernel mass) / `qkSingleton` (joint mass `∏ markovFactor`) / `sum_qkSingleton_le_one` (per-path sub-distribution、内部 per-state `∑_a markovFactor=1` = `IsMarkovKernel`) / `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` (joint↔AEP 橋) / `negLogQk_div_tendsto_condEntropyTail` (H_k AEP) / `entropyRate_eq_lim_condEntropy` (`EntropyRate.lean:484`、H_k→H、nat)。**全 sorry-free** ([lz78-facts.md](lz78-facts.md) 達成テーブル)。M3 の Q_k grafting が乗る既存資産 — 「Q_k from scratch」過大評価を是正 |
| **node-context conditional 資産 (leg 5、第三の量)** | `LZ78/ZivCondContext.lean` | `condContextProb` (conditional q(symbol\|context)) / `condContext_sum_le_one` (旧「次の genuine atom」node-context sub-distribution `∑_a q(v·a\|v)≤1`、既に sorry-free) / `condContext_card_mul_log_le_sum_neg_log` (per-context log-sum) / `sum_neg_log_condContextProb_path_eq_blockLogAvg` (**chain-rule backbone `∑ -log q_cond = n·blockLogAvg`、但し full-history context = fiber size 1 trivial、k=∞ reference のみ、grouping vehicle にはならない**)。全 sorry-free、commit `cfe518b`/`6accdd2` |

### 旧 Phase 履歴 (圧縮)
- 旧 `IsLZ78*` load-bearing 仮説路 (`IsLZ78ZivAsEventual` / `IsLZ78ConverseCodingLowerBound`
  / passthrough predicate 3本) は def-fix + dead scaffolding 削除 (commit `602b1ad`)
  で消滅、現在の SoT は `GreedyParsingImpl.lean` の wall sorry lemma 2本。
- 旧 FALSE per-block `IsLZ78ZivCombinatorialCore` (反例 `a^16`) は撤回済 (§2 D1/D2)。

---

## 1. 残る4部品 + 推奨着手順 (tractable 順)

### M1 — converse UD-object 【✅ 済 (2026-05-21)】
- **内容**: LZ78 符号化 (index, symbol) ストリームを定義し、**uniquely-decodable であることを証明** → Mathlib McMillan (`McMillanKraftBridge`) を**実 LZ78 code に適用** → 実コードの**期待値 converse `H_D ≤ E[lz]`** を genuine に。
- **注意**: `lz78PhraseStrings` 自体は **prefix-complete で UD でない**。真の UD object は encoded stream (別構造、新規構築要)。`_nodup` は UD の必要条件にすぎず不十分。
- **deliverable (実装済)**: `InformationTheory/Shannon/LZ78/ConverseUDObject.lean` (sorryAx 非依存、`lake env lean` silent)。
  - `uniquelyDecodable_of_constantLength` — 定長コード ⟹ UD (汎用、Mathlib 未収録、本 M1 の数学的核)。
  - `boolEncode`/`finBoolCode` — fixed-width binary code、`m < 2^K` で injective。
  - `lz78TokenCode c : Fin (c+1) × α → List Bool` (width `K = bitLength c |α|`) の injective + UD + `lz78TokenCode_kraftSum_le_one` + `lz78TokenCode_entropyD_le_expectedLength` (= `entropyD 2 P ≤ E[L] = K`)。
  - McMillanKraftBridge §3 Residual 1 (「UD object 未構築」) を解消。
- **残**: `IsLZ78ConverseCodingLowerBound` (block-rate, Cover–Thomas Eq. 13.130) は **未着手のまま** — token-level Kraft → block-rate a.s.-eventual `liminf` は **averaged⟶a.s. lift (= M4)** が必要。M1 は converse の**期待値層を実コードに接続**した段階。
- **規模 (実績)**: ~270 行。**リスク: 低〜中 (組合せ的)** — 想定通り、初回 skeleton がほぼそのまま通過。

### M2 — Ziv 組合せ核 (Q_k grafting) 【genuine medium、M3 achievability の本体攻略】
- **内容**: distinct-phrase log-sum を `c·log c ≤ -log Pₙ + o(n)` に乗せる。leg 4 後半で **2 つの単純 grouping が両方 machine-ruled-out**: (1) node-position-grouping = §2 D3 trap、(2) marginal-length-grouping = §2 D8 方向不一致。**leg 5 で route 是正**: 旧「conditional-context AEP を一から構築」過大評価は撤回 — Q_k measure/AEP/sub-distribution (`Core.lean` 7 件) + node-context conditional (`ZivCondContext.lean` 4 件、旧「次の genuine atom」`condContext_sum_le_one` 含む) が **全て既存 sorry-free** (§0 足場テーブル / [lz78-facts.md](lz78-facts.md))。残る genuine core = **Ziv (k-state, length)-grouping (Cover-Thomas Lemma 13.5.5) + k(n)→∞ diagonal の grafting**。**vehicle は per-step markovFactor conditional** (joint qkSingleton-per-phrase-marginal は D8 反復で禁止)。
- **deliverable**: `ziv_aseventual_le_blockLogAvg₂` (`@residual(wall:lz78-aseventual-ziv)`) の sorry を discharge → **achievability 完遂**。既証明 SMB (`shannon_mcmillan_breiman₂`) + Q_k AEP chain (`negLogQk_div_…` / `entropyRate_eq_lim_condEntropy`) に乗せる接続込み。
- **規模**: ~150–300 行。**リスク: medium (Ziv Lemma 13.5.5 grouping + k(n) diagonal grafting)**。Phase 1 gateway + Phase 2a convexity grouping + Phase 2b marginal 橋 + Phase 2c-i node-context conditional は **sorryAx-free 済** (足場)。残る Phase 2c-ii = Q_k grafting が支配。**旧「~300–600 行 research-level・数 leg、Q_k from scratch」過大評価は撤回**。sub-plan = [`lz78-m2-plan.md`](lz78-m2-plan.md)。

### M3 — a.s.-eventual Ziv 不等式を既証明 SMB + Q_k AEP に乗せる 【M2 Q_k grafting に統合】
> **2026-06-20 framing realign (r2)**: 旧 framing の **エルゴード対角線持ち上げ**
> (固定深さ k AEP `negLogQk_div_…` からの k↔n 連動 対角線/カットオフ) は **obsolete** —
> 無条件・sorry-free な Shannon–McMillan–Breiman AEP `shannon_mcmillan_breiman`
> (`SMB/AlgoetCover/Liminf.lean`、`∀ᵐ ω, blockLogAvg μ p n ω → entropyRate μ p`)
> が `-log₂Pₙ/n → H₂` を free で供給するため。SMB が蒸発させたのは **source entropy
> limit** (`-log₂Pₙ/n → H₂`、`blockLogAvg₂ → entropyRate₂`) **だけ** で、LZ 固有の
> combinatorial 不等式 `c·log₂c ≤ -log₂Pₙ + o(n)` は SMB と gateway の間に genuine に残る。
>
> **2026-06-20 leg 5 route 是正 (本 leg 3 度目の修正)**: leg 4 後半は genuine core を
> 「conditional-context AEP を一から構築 (Q_k from scratch、research-level・数 leg)」と
> characterize したが、これも **過大評価だった**。leg 5 で **Q_k measure/AEP/sub-distribution +
> node-context conditional 資産が既存 sorry-free** と機械裏取りされ ([lz78-facts.md](lz78-facts.md))、
> 残る genuine core は **Ziv (k-state, length)-grouping (Cover-Thomas Lemma 13.5.5) + k(n)→∞
> diagonal の grafting** に絞られた。M3 は M2 に統合され、独立した攻略 path を持たない。
- **両単純 grouping は machine-ruled-out (再探索禁止、§2)**:
  - **(1) node-position-grouping = D3 trap**: overhead `c·log(#nodes) ≈ c·log c` (LZ tree で
    #nodes≈c)、`lz78PhraseStrings_mul_log_le` (`c·log c ≤ K·n`、sorryAx-free) より `(c·log c)/n`
    は定数で vanish しない。
  - **(2) marginal-length-grouping = 方向不一致**: memory 源で `∑ -log P_marginal ≥ -log Pₙ`
    (chain rule `q_cond ≥ P_marginal`)。FKG/positive-association loogle **0-hit**。**joint
    qkSingleton を per-phrase marginal にするのも同じ D8 反復で禁止**。
- **既存 sorry-free 資産 (leg 5 機械裏取り、[lz78-facts.md](lz78-facts.md) が SoT)**:
  - **Q_k 資産 (`SMB/AlgoetCover/Core.lean` 7 件)**: `markovFactor` / `qkSingleton` /
    `sum_qkSingleton_le_one` (per-path sub-dist) / `qkSingleton_blockRV_eq_ofReal_exp_negLogQk`
    (joint↔AEP 橋) / `negLogQk` / `negLogQk_div_tendsto_condEntropyTail` (H_k AEP) /
    `entropyRate_eq_lim_condEntropy` (H_k→H、nat)。
  - **node-context conditional (`ZivCondContext.lean` 4 件、leg 5)**: `condContextProb` /
    `condContext_sum_le_one` (**旧「次の genuine atom」node-context sub-distribution
    `∑_a q(v·a|v)≤1`、既に sorry-free**) / `condContext_card_mul_log_le_sum_neg_log` /
    chain-rule backbone `sum_neg_log_condContextProb_path_eq_blockLogAvg` (**full-history context =
    fiber size 1 trivial、k=∞ reference のみ、grouping vehicle にはならない**)。
- **残る genuine core = Ziv (k-state, length)-grouping (Lemma 13.5.5) + k(n)→∞ diagonal grafting**:
  `(c·log₂c)/n ≤ negLogQk/n + overhead_k → H_k`、k→∞ で `H_k → H = entropyRate₂`。**vehicle は
  per-step markovFactor conditional** (`∑_a markovFactor(s,a)=1`、`Core.lean:327-361`)。AEP 接続は
  `qkSingleton_blockRV_eq_ofReal_exp_negLogQk` → `negLogQk_div_tendsto_condEntropyTail` →
  `entropyRate_eq_lim_condEntropy`。`-log₂Pₙ/n = blockLogAvg₂ → entropyRate₂`
  (`shannon_mcmillan_breiman`) で `limsup (c·log₂c)/n ≤ entropyRate₂` (= 壁補題
  `lz78GreedyImpl_achievability_ae` の RHS) に乗る。
- **plumbing で closed / sorryAx-free 済 (necessary scaffolding)**: gateway (単位整合)
  `lz78_impl_bitrate_le_clogc_plus_overhead` + convexity grouping `ZivLengthGrouping.lean`
  (M2 Phase 2a) + marginal sub-dist 橋 `ZivMeasureBridge.lean` (M2 Phase 2b) + node-context
  conditional `ZivCondContext.lean` (M2 Phase 2c-i)。いずれも単独では genuine core を閉じない。
- **D1/D2 (§2) との整合**: この Ziv 不等式は **a.s.-eventual / limsup + AEP 形でなければ
  ならない**。per-block universal な clean 形 (D1) も定数 overhead 形 (D2) も **machine-disproof
  で FALSE** (反例 `a^16`)。limsup 形で o(n) を吸収して初めて成立。
- **deliverable**: `lz78GreedyImpl_achievability_ae` (`@residual(wall:lz78-aseventual-ziv)`、
  `GreedyParsingImpl.lean`) の sorry を discharge → **achievability 完遂**。
- **規模/リスク**: gateway + convexity grouping + marginal 橋 + node-context conditional は
  **sorryAx-free 済 (足場)**。残る genuine 核 = Ziv (k-state,length)-grouping (Lemma 13.5.5) +
  k(n) diagonal grafting = **medium** (~150–300 行、既存 Q_k 資産への接合であって from scratch
  ではない、旧 research-level・数 leg 過大評価は撤回)。`wall:lz78-aseventual-ziv` は honest に維持
  (TRUE-as-framed、Lemma 13.5.5 + k(n) diagonal 未証明)。攻略 path = [`lz78-m2-plan.md`](lz78-m2-plan.md)。

### M4 — converse Barron a.s. lift 【要・腰据え】
- **内容**: M1 の期待値 converse `H_D ≤ E[lz]` を **a.s.-eventual pointwise `liminf lz/n ≥ entropyRate₂`** に持ち上げる (competitive-optimality / Barron 型エルゴード論法)。LZ78 は pointwise で Shannon code を破れるので **期待値↛pointwise**。
- **deliverable**: `lz78GreedyImpl_converse_ae` (`@residual(wall:lz78-converse-aseventual)`、`GreedyParsingImpl.lean`) の sorry を discharge → **converse 完遂**。
- **規模**: ~300–700 行。**リスク: 高** (a.s. エルゴード)。

### M5 — 最終合成 + 完遂判定 【capstone】
- **内容**: M3 + M4 で両 wall sorry lemma discharge → headline `lz78_asymptotic_optimality_with_greedy_impl` を無条件化、`#print axioms = [propext, Classical.choice, Quot.sound]` (sorryAx 非依存) 確認 = 標準B 完遂。`h_bdd_above` 内製化は済 (commit `a1ae108`、`lz78-headline-bdd-discharge-plan.md` ✅ CLOSED)、もう完遂条件ではない。
- **規模**: ~50–100 行 (配線のみ)。**リスク: 低** (M3/M4 が閉じれば)。

---

## 2. 既知の地雷 (machine-disproof / 確定済み — 再探索禁止)

- **D1**: per-block `c·log c ≤ -log Pₙ` (∀n∀ω, clean) は **FALSE**。反例 constant process `a^16` (c=5, `-log Pₙ=0`)。
- **D2**: overhead 版 `c·log c ≤ -log Pₙ + c·log(\|α\|+1)` も **FALSE** (`Pₙ→1` family)。当初 machine-disproof `not_isLZ78ZivCombinatorialCoreOverhead` で裏取り済 (反例 `n=16, Pₙ=1, c=5`)。**verdict は不変** だが、その refutation decl + 旧 FALSE predicate は def-fix cleanup (§0 旧 Phase 履歴、commit `602b1ad` 系) で in-tree 削除済 (現在 codebase 不在)。**per-block universal Ziv は誤った formulation** — genuine は a.s.-eventual のみ。**D1/D2 の per-block 偽性ゆえ M3 の Ziv 不等式は a.s.-eventual / limsup 形でなければならない** (§1 M3 realign 参照)。
- **D3 (machine-ruled-out)**: node-position-grouping overhead `(c·log #nodes)/n` は #nodes≈c で**定数収束 (vanish しない)** = treenode T1-T5 literal が死ぬ。**正しいのは finite-k grouping** (#states 有界 → convexity overhead vanish)。`log #nodes=log c` を `log log n` と取り違えない。
- **D4**: path-prefix `Q_c = ∏ condPhraseProb` の AEP は genuine (M0 で trivial と判明) **だが achievability に繋がらない** (`∑ⱼqⱼ≈c` の罠)。**裏付け**: path-prefix route の decl (`condPhraseProb` / `blockProb_neg_log_ge_sum`、`LZ78/ZivEntropyBridge.lean`) は `dep_consumers.sh` で **0 direct consumers** = orphan 確認済 → D4 dead-start (`∑ⱼqⱼ≈c` trap) が機械裏取りされた。genuine core はこの path-prefix を素通り — vehicle は per-step markovFactor conditional `∑_a markovFactor(s,a)≤1` / `condContext_sum_le_one` という第三の量 (path-prefix `∑qⱼ` でも marginal でもない、D8)。
- **D5**: McMillan は **Mathlib 既存** (`InformationTheory.kraft_mcmillan_inequality`)。再発明不要、wire 済 (M1 で使う)。
- **D6**: converse の pointwise `2^{-lz} ≤ Pₙ` 経路は**不健全** (Shannon-code 補題、`lz ≥ shannonLength` は pointwise 偽 = LZ78 universality の核心)。M4 は期待値→a.s. lift で。
- **D7**: Huffman 系の `mergedMeasure` 偽 core 等は別件 (本 roadmap 対象外、textbook-roadmap 判断ログ #6 + `huffman-fullB-structure-plan.md` 参照)。
- **D8 (machine-ruled-out)**: marginal-length-grouping (marginal route) は overhead vanish だが **方向不一致** — chain rule `-log Pₙ = ∑_j -log q_cond(j)` (conditional) に対し memory 源で `q_cond ≥ P_marginal` ゆえ `∑ -log P_marginal ≥ -log Pₙ` = 欲しい `≤` と逆 (iid 等号、memory 逆、Dirac 両 0 alive)。FKG/positive-association loogle **0-hit**。**marginal では `-log Pₙ` を上から押さえられない** → genuine core は **conditional** markovFactor / q(symbol|context) を使う (§1 M3 / §3)。**joint `qkSingleton(phrase)` を per-phrase marginal として `∑ -log qkSingleton(phrase)` するのも同じ D8 反復で禁止** (leg 4 marginal route と方向逆 dead-end)。

---

## 3. 校正・規模・リスク総括

- **校正 (2026-06-20 leg 5、Q_k 資産発見による route 是正)**: 既存 SMB (`SMB/AlgoetCover/` = `Core.lean` + `Liminf.lean` + `TwoSidedRatio.lean`、計 ~2800 行) は **完成済・sorry-free** で、headline `shannon_mcmillan_breiman` が `-log₂Pₙ/n → H₂` を free で供給する (source entropy limit のみ)。両単純 grouping (node-position = D3 trap / marginal = D8 方向不一致) は machine-ruled-out (§2、再探索禁止)。**leg 5 で route 是正**: leg 4 後半の「conditional-context AEP を一から構築 (Q_k from scratch、research-level・数 leg)」も **過大評価**。**Q_k measure/AEP/sub-distribution (`Core.lean` 7 件) + node-context conditional (`ZivCondContext.lean` 4 件、旧「次の genuine atom」`condContext_sum_le_one` 含む) が全て既存 sorry-free** ([lz78-facts.md](lz78-facts.md))。残る genuine 核 = **Ziv (k-state, length)-grouping (Cover-Thomas Lemma 13.5.5) + k(n)→∞ diagonal の grafting** = **medium** (既存 Q_k 資産への接合)。gateway + convexity grouping + marginal 橋 + node-context conditional は sorryAx-free 済 (足場)。**M4 (converse Barron a.s. lift) は別途** (SMB-lower + 期待値→a.s. lift、依然 high risk)。
- **総計**: おおよそ **~400–900 行** (M2/M3 = Ziv Lemma 13.5.5 grouping + k(n) diagonal grafting ~150–300 行 + M4 + 配線が主、旧 ~700–1500 行は Q_k 資産発見で是正)。
- **数学的位置づけ**: LZ78 最適性は**標準教科書定理 (深い/未解決ではない)**。**SMB が source entropy limit を、Q_k 資産が k-Markov measure/AEP/sub-distribution を握っている** ので残りの難しさは「Ziv 組合せ核 (Lemma 13.5.5 (k-state,length)-grouping) を既存 Q_k に grafting + k(n)→∞ diagonal」層に絞られる。「from scratch research-level」ではなく既存資産への接合。M4 は依然エルゴード a.s. lift が残る。
- **進め方の推奨**: **M1 → M2 = M3 (統合)** をまず閉じて足場を固める。**M2 gateway (Phase 1) + Phase 2a convexity grouping + Phase 2b marginal 橋 + Phase 2c-i node-context conditional は sorryAx-free 済 (足場)**、残る **M2 Phase 2c-ii = Ziv Lemma 13.5.5 grouping + k(n) diagonal grafting (genuine 核、medium)** が支配。gateway atom = per-step markovFactor conditional の (k-state,length)-grouping log-sum (gateway-atom-first で tier-2 維持の前に試す)。`lz78-ziv-treenode-plan.md` は **部分 un-park** (旧 T2 conditional sub-distribution = leg 5 で `condContext_sum_le_one` として建った、旧 T3 naive node-grouping assembly は D3 で dead)。**M4** (converse Barron a.s. lift) は独立した dedicated セッションで (依然 high risk)。

---

## 4. cross-link
- **sub-plan (M3 攻略 = mainline)**: [`lz78-m2-plan.md`](lz78-m2-plan.md) — M2/M3 Ziv 組合せ核 (Q_k grafting) = W2 `ziv_aseventual_le_blockLogAvg₂` (`@residual(wall:lz78-aseventual-ziv)`) discharge 計画。W1 SMB-in-bits は leg 3 で閉鎖済。**status: Phase 1 gateway + Phase 2a convexity grouping + Phase 2b marginal 橋 + Phase 2c-i node-context conditional = sorryAx-free 済 (足場)。Phase 2c-ii = Ziv (k-state,length)-grouping (Lemma 13.5.5) + k(n) diagonal grafting (genuine 核、medium)**。両単純 grouping (node-position D3 / marginal D8) machine-ruled-out。**leg 8: threading foundation = gateway GO + body fill + tiling 隔離、全監査 PASS** (`ZivThreading.lean`、factor correspondence 5 補題 + `negLogQk_phrase_threading` body fill sorryAx-free、残 1 sorry = `lz78_block_tiling` tiling 材料化 `:538`、監査 caveat = closure 時に boundary-length conjuncts 追加要、[lz78-facts.md](lz78-facts.md) 判断ログ #5/#6)。W2 は genuine core が閉じるまで `sorry` + `@residual` 維持。
- **settled-facts ledger**: [`lz78-facts.md`](lz78-facts.md) — Q_k 資産 7 件 + node-context conditional 4 件 + Ziv 核 + route 確定 (D3/D4/D8) の機械裏取り台帳 (family `lz78` の SoT、`#print axioms` で再導出)。
- **in-stock**: [`lz78-m3-treenode-inventory.md`](lz78-m3-treenode-inventory.md) — route 比較の機械裏取り在庫 (leg 4)。node-position-grouping = D3 trap で死ぬ、を確定。
- main: `docs/textbook-roadmap.md` 判断ログ #6 (現行サマリ、~35 エージェントの経緯・全 disproof・honest frontier の記録は `git log -- docs/textbook-roadmap.md` の 2026-05-26 整理前 commit に旧 #17–#26 として残置)
- **部分 un-park**: [`lz78-ziv-treenode-plan.md`](lz78-ziv-treenode-plan.md) — 旧 T2 per-node conditional sub-distribution `∑_a q(node·a|node) ≤ 1` は **leg 5 で `condContext_sum_le_one` として建った** (genuine 核、本線 M2 Phase 2c-i)。旧 T3 naive node-grouping assembly は **D3 trap で dead**、削除済 node-context 基盤資産 (`f67ec8a`/`602b1ad`) も dead。
- 既存 plan (本 roadmap が incremental master として統合): `lz78-completion-plan.md`, `lz78-treeinduced-aep-plan.md`, `lz78-aseventual-achievability-plan.md`, `lz78-blockrv-refactor-plan.md` + `-inventory.md`
- 完遂判定: `GreedyParsingImpl.lean` の wall sorry lemma 2本 (M3/M4) が discharge され、headline `lz78_asymptotic_optimality_with_greedy_impl` が `#print axioms` で sorryAx 非依存になった時点 = 標準B 完遂 (`h_bdd_above` 内製化は commit `a1ae108` で済、完遂条件から除外)。
