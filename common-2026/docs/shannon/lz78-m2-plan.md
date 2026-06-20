# LZ78: M2 length-grouping Ziv 組合せ不等式 サブ計画

> **Parent**: [`lz78-completion-roadmap.md`](lz78-completion-roadmap.md) §1 M2 / M3
> （achievability 壁 `lz78-aseventual-ziv` CLOSED leg 11、W2 = `ziv_aseventual_le_blockLogAvg₂`）

✅ **CLOSED (leg 11)**: W2 `ziv_aseventual_le_blockLogAvg₂` sorryAx-free + 独立 honesty 監査 PASS (`c22f2d5`、`@audit:ok`)。consumer `lz78GreedyImpl_achievability_ae` も sorryAx-free → **achievability 完遂**。achievability 壁 `lz78-aseventual-ziv` は CLOSED (leg 11、`c22f2d5`)。本サブ計画の目標は達成。headline 残壁は M4 converse のみ ([lz78-facts.md](lz78-facts.md) 達成テーブル「achievability W2 closure (leg 11)」が SoT)。

## 進捗

- [x] M0 在庫確認（leg 3 `lz78-m3-inventory.md` + leg 4 `lz78-m3-treenode-inventory.md` の route A/B 比較）✅
- [x] Phase 1 — gateway atom（Step A 符号長 bit-rate 展開）✅ **GO**（`lz78_impl_bitrate_le_clogc_plus_overhead`、`GreedyParsingImpl.lean:286`、sorryAx-free、commit `7171707`）→ 単位整合は壁でないと確定
- [x] Phase 2a — convexity grouping（length 別 Jensen）✅ **sorryAx-free**（`ZivLengthGrouping.lean`、commit `c472518`）— necessary scaffolding だが単独では不十分
- [x] Phase 2b — marginal sub-distribution + log-sum 橋 ✅ **sorryAx-free**（`ZivMeasureBridge.lean`、commit `d1d55db`）— **marginal なので方向不一致、`-log Pₙ` に届かない**（判断ログ #4）
- [x] Phase 2c-i — node-context conditional sub-distribution `∑_a q(v·a\|v) ≤ 1`（旧「次の genuine atom」）✅ **sorryAx-free**（`ZivCondContext.lean` `condContext_sum_le_one`/`condContext_card_mul_log_le_sum_neg_log`/chain-rule backbone、commit `cfe518b`/`6accdd2`、[lz78-facts.md](lz78-facts.md) 達成テーブル）— 第三の量は **既に建っている**
- [x] Phase 2c-ii — Ziv (k-state, length)-grouping + composition brick ✅ **CLOSED sorryAx-free + 全監査 PASS（leg 8–10）**。threading foundation + tiling 材料化（leg 8–9、`bf78de9`/`29280cf`/`7b0ecbb`）に続き、**leg 10 で `c·log c ≤ negLogQk + o(n)` composition brick 全体が CLOSED**（`ziv_achievability_composition`、新 file `ZivAchievabilityComposition.lean:194`、`@audit:ok`、`19314ee`/`65afc03`/`a25fd25`/`1ef7700`/`3867a29`）。(W) empirical-overhead brick `condState_grouping_bound_mean`（`ZivCondGrouping.lean:340`、worst-case `c·log D` を manifestly-o(n) mean-length に supersede、旧 `condState_grouping_bound` は consumer-less → retract-candidate）+ sub-step (A) `phraseSum_le_negLogQk`（+ unconditional `pmfLogCondMarkov_nonneg`）+ sub-step (B) reindex（`flatten_drop_take_getElem`/`condQkState_pos_of_markovFactor_pos`/`condQkState_congr_length`）。3 sig-strengthening は output-strengthening と再監査済。詳細 = [lz78-facts.md](lz78-facts.md)「threading 配線」「grouping bridge + overhead 制御」+ 判断ログ。
- [x] Phase 3 — (V) diagonalization ✅ **CLOSED (leg 11、`c22f2d5`)**: 各固定 k で `limsup(lz/n) ≤ conditionalEntropyTail k / log2` (Lemma 1 `ziv_aseventual_le_condEntropyTail_bits`、`:619`) + inf over k で `limsup(lz/n) ≤ entropyRate₂` (Lemma 2 `ziv_aseventual_le_entropyRate₂`、`:869`)、両 sorryAx-free。**「最大リスク = k-limit/n-limsup 交換 (k(n)→∞ 対角化)」は不要だった** — 最終 LHS `limsup(lz/n)` が k 非依存ゆえ k→∞ は RHS だけで `inf_k H_k = entropyRate` を取れば足り、対角化も `Lmax = o(n)` known sub-task も回避された (判断ログ参照)。overhead vanishing は全て `c/n → 0` + `x·log(1/x) → 0` boundary に帰着 (private helper `clog_div_le_two_mul_sqrt`/`cp_log_cp_le_reconcile`)。
- [x] Phase 4 — (Z) W2 discharge ✅ **CLOSED (leg 11、`c22f2d5`)**: `ziv_aseventual_le_blockLogAvg₂` (`:917`、`@audit:ok`) を Lemma 2 + `shannon_mcmillan_breiman₂` の `filter_upwards` 合成で sorryAx-free 化 → consumer `lz78GreedyImpl_achievability_ae` (`:1005`、`@audit:ok`) も sorryAx-free → achievability 完遂。signature 不変 (ripple ゼロ)。

## ゴール

W1（`shannon_mcmillan_breiman₂`、SMB-in-bits 橋）は leg 3 で **閉鎖済**（`@audit:ok`、sorryAx-free、`GreedyParsingImpl.lean:520`）。本サブ計画のゴール **W2 = `ziv_aseventual_le_blockLogAvg₂`**（`GreedyParsingImpl.lean:917`、`@audit:ok`）の discharge は **leg 11 で達成（`c22f2d5`、sorryAx-free + 独立監査 PASS）**。consumer `lz78GreedyImpl_achievability_ae`（`:1005`、`@audit:ok`）も sorryAx-free 化され **achievability 完遂**。headline 残壁は M4 converse（`lz78GreedyImpl_converse_ae`、`:484`）のみ。**本サブ計画の目標は達成。**

**status（leg 11 後、achievability 完遂）**: **残 active edge = none（本サブ計画の目標達成）**。Phase 1 gateway + Phase 2a/2b/2c-i 足場 + Phase 2c-ii（threading + tiling + composition brick）= sorryAx-free（leg 8–10）。Phase 3 (V) diagonalization + Phase 4 (Z) W2 discharge = leg 11 で CLOSED。Q_k 資産発見（leg 5）による route 是正と composition の「Ziv 組合せ核を既存 Q_k に grafting」が完遂された上で、(V) は**対角化不要**と判明し（最終 LHS が k 非依存）残りは各 k bound + inf over k で閉じた。背景（旧 plan の「conditional-context AEP を一から構築 = Q_k from scratch research-level」は過大評価で、**kth-order Markov 測度 Q_k とその AEP + sub-distribution 境界が既に sorry-free で存在**する、[lz78-facts.md](lz78-facts.md) 達成テーブル、機械裏取り済）:

- **Q_k 資産（`SMB/AlgoetCover/Core.lean`、SMB 内部足場として既存、全 sorry-free）**: `markovFactor`（per-step conditional kernel mass）/ `qkSingleton`（joint mass `∏ markovFactor`）/ `sum_qkSingleton_le_one`（per-path sub-distribution `∑_y qk ≤ 1`、内部に per-state `∑_a markovFactor=1` = `IsMarkovKernel`）/ `qkSingleton_blockRV_eq_ofReal_exp_negLogQk`（joint↔AEP 橋）/ `negLogQk_div_tendsto_condEntropyTail`（H_k AEP `negLogQk/n → H_k`）/ `entropyRate_eq_lim_condEntropy`（H_k → H、**nat 単位**、`EntropyRate.lean:484`）。
- **node-context conditional 資産（`ZivCondContext.lean`、leg 5 `cfe518b`/`6accdd2`、全 sorry-free）**: `condContextProb`（conditional `q(symbol|context)` = 第三の量）/ `condContext_sum_le_one`（**旧 plan が「次の genuine atom」と呼んでいた node-context sub-distribution `∑_a q(v·a|v)≤1`、既に建っている**）/ `condContext_card_mul_log_le_sum_neg_log`（per-context log-sum step）/ `sum_neg_log_condContextProb_path_eq_blockLogAvg`（chain-rule backbone `∑ -log q_cond = n·blockLogAvg`、**但し full-history context = 全 distinct で fiber size 1 = trivial、grouping vehicle にはならず k=∞ reference のみ**）。

**残る genuine core = Ziv (k-state, length)-grouping (Cover-Thomas Lemma 13.5.5) + k(n)→∞ diagonal の grafting**（唯一残る新規）:

1. **Ziv 組合せ核 (Lemma 13.5.5)**: LZ phrase を **(k-state, length)-grouping** し、**per-step `markovFactor` conditional** の sub-distribution（`∑_a markovFactor(s,a)=1`、`Core.lean:327-361` 抽出、または `condContext_sum_le_one`）で log-sum → `c·log c ≤ -log qkSingleton(whole) + overhead = negLogQk + overhead`。overhead `c·log(|α|^k·maxlen) = c(k·log|α| + log log n)` は fixed k で `/n → 0`。**vehicle は per-step markovFactor conditional**（joint `qkSingleton` を per-phrase marginal に使うのは leg 4 marginal route と同じ dead-end = D8 反復、**禁止**）。
2. **k=k(n)→∞ diagonal（genuine 新規 analytic step）**: k-limit（`entropyRate_eq_lim_condEntropy` で H_k→H）と n-limsup の交換、overhead `c·k(n)·log|α|/n → 0` を保ちつつ。SMB 自身も同じ closing move（`negLogQk_div_…` / `entropyRate_eq_lim_condEntropy`）を使うので intended route の強い signal。
3. **AEP 接続**: `qkSingleton_blockRV_eq_ofReal_exp_negLogQk`（joint→negLogQk）→ `negLogQk_div_tendsto_condEntropyTail`（→H_k）→ `entropyRate_eq_lim_condEntropy`（→H）。bit 化は `/Real.log 2` で機械整合（target は `entropyRate₂`）。

- **規模/リスク是正**: 旧「~300–600 行 research-level・数 leg、Q_k from scratch」→ 新「Q_k measure/AEP/sub-dist + node-context conditional は free、残るは Ziv Lemma 13.5.5 (k-state,length)-grouping + k(n) diagonal の grafting、~150–300 行、**medium risk**」。依然 genuine だが「from scratch research-level」ではない。
- **壁は維持 (leg 11 で達成済 = discharge)**: 当時の撤退ラインは「Ziv Lemma 13.5.5 gateway atom（per-step markovFactor (k-state,length)-grouping log-sum）が通らなければ tier-2 維持」（gateway-atom-first）。実際には composition brick + 各固定 k bound + inf over k で genuine discharge され、tier-2 維持は不要だった。

W2 の signature（`GreedyParsingImpl.lean:917`、`@audit:ok`、leg 11 で sorryAx-free 化、signature 不変）:

```lean
theorem ziv_aseventual_le_blockLogAvg₂
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup
        (fun n => (lz78GreedyImplEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop
      ≤ Filter.limsup
          (fun n => blockLogAvg₂ μ p.toStationaryProcess n ω) Filter.atTop := by
  sorry
```

**ripple（機械確認、`dep_consumers.sh`、本セッション）**: `ziv_aseventual_le_blockLogAvg₂` の direct consumer は **1 decl / 1 file のみ**（`lz78GreedyImpl_achievability_ae`、同 file）。consumer は W2 の **statement** にのみ依存し（body は sorry）、本サブ計画は W2 の body を埋めるだけで signature を変えない → **ripple ゼロ**。signature threading / 引数追加は不要・禁止（hypothesis bundling 防止）。

## Approach

### genuine target 不等式の Mathlib-shape-driven formulation

textbook の `c·log c ≤ -log Pₙ` を **そのまま def 化しない**。SMB が既に握っている結論形に target を合わせる。verbatim 確認済の握り 2 点:

- **SMB-in-bits の握り**（W1、`@audit:ok`）: `∀ᵐ ω, Tendsto (fun n => blockLogAvg₂ μ p n ω) atTop (𝓝 entropyRate₂)`。`blockLogAvg₂ μ p n ω = blockLogAvg μ p n ω / Real.log 2`（`GreedyParsingImpl.lean:502` def）。
- **`-log Pₙ` の握り**（`ZivEntropyBridge.lean:126`、`@entry_point`、verbatim）: `(n : ℝ) * blockLogAvg μ p n ω = - Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})`（`0 < n` 前提）。つまり `n · blockLogAvg = -log Pₙ`、`blockLogAvg = (-log Pₙ)/n`。

W2 の RHS は既に `limsup blockLogAvg₂`（W1 の握る量そのもの）になっており、これが **正しい Mathlib-shape**。よって M2 が建てるべきは、**per-n の比較不等式**

```
lz78GreedyImplEncodingLength n (blockRV n ω) / n  ≤  blockLogAvg₂ μ p n ω + err(n, ω)
```

を、各 ω で **a.s.-eventual に**（`∀ᶠ n`）成立させ、`err(n) → 0`（o(1)）を示す形。これを `Filter.limsup_le_limsup`（`Mathlib/Order/LiminfLimsup.lean:198`、verbatim 在庫済）に乗せれば W2 が閉じる。

**単位の選択（verbatim 確認して bit 単位で建てる）**: SMB-in-bits は既に `blockLogAvg₂`（bit）で握る。符号長 `lz78GreedyImplEncodingLength = c · bitLength c |α|`（`bitLength = Nat.log 2(c+1) + Nat.log 2|α| + 2`、`GreedyParsing.lean:112/115` verbatim）は **base-2 code length**。一方 Ziv 組合せ核 `lz78PhraseStrings_mul_log_le`（`ZivCountingBody.lean:357`、verbatim）は **nat 単位** `c·log c ≤ 8·log(|α|+1)·n`（`Real.log`）。`-log Pₙ`（`blockLogAvg_eq_neg_log_blockProb`）も **nat**。

→ **bit 単位の target に nat 量を持ち込む際は両辺を `Real.log 2` で割る**。`c·Nat.log 2(c+1)` → `c·log(c+1)/log 2`（`lz78_impl_natLog_mul_log_two_le`、`GreedyParsingImpl.lean:155` verbatim で `Nat.log 2 m · log 2 ≤ log m`）。`blockLogAvg₂ = blockLogAvg/log 2 = (-log Pₙ)/(n·log 2)`。**bit 版で `c·log₂c ≤ -log₂Pₙ + o(n)` を建て、両辺の `/log 2` は定数なので機械的に整合**（`div_le_div_of_nonneg_right`）。

### genuine core 戦略の骨子（Q_k grafting：既存 Q_k 資産に Ziv Lemma 13.5.5 + k(n) diagonal を接合）

genuine missing piece = `c·log c`（組合せ phrase count）を `-log Pₙ`（source 確率）に繋ぐ不等式 + overhead 制御。**leg 5 で Q_k 資産（kth-order Markov 測度の measure/AEP/sub-distribution + node-context conditional）が既存 sorry-free と機械裏取りされた**ので、骨子は「Q_k から一から構築」ではなく「既存 Q_k 資産への grafting」に絞られる:

1. **Step A（gateway、closed）**: 符号長 bit-rate を `c·log₂c/n` 型に展開（`lz78_impl_bitrate_le_clogc_plus_overhead`、sorryAx-free）。
2. **Step B-naive（両 ruled-out、再探索禁止）**: 単純な length-grouping で `c·log₂c ≤ -log₂Pₙ + overhead` を直接建てる路は **両方死ぬ** — (i) **node-position-grouping**（overhead `c·log(#nodes)≈c·log c`、D3 で非 vanish）、(ii) **marginal-length-grouping**（marginal sub-distribution `∑_a P(a)≤1` 経由の log-sum は `∑ -log P_marginal ≥ -log Pₙ` = **方向が逆**、D8）。
3. **Step B-genuine = Q_k grafting（composition brick CLOSED、leg 8–10）**: kth-order Markov 測度 `Q_k` に乗せた `c·log c ≤ negLogQk + o(n)` の **composition brick 全体が sorryAx-free + 全監査 PASS**（`ziv_achievability_composition`、`@audit:ok`）。Ziv 組合せ核 (Cover-Thomas Lemma 13.5.5) の (k-state,length)-grouping log-sum（vehicle = per-step `markovFactor` conditional）+ (W) empirical-overhead `condState_grouping_bound_mean`（manifestly-o(n) mean-length 形）+ (A) `phraseSum_le_negLogQk` + (B) reindex がすべて閉じた。
4. **Step C = (V) diagonalization（leg 11 CLOSED、対角化不要と判明）**: composition brick `c·log c ≤ negLogQk + o(n)` を `entropyRate₂` に持ち上げる。AEP 接続 `qkSingleton_blockRV_eq_ofReal_exp_negLogQk`（joint→negLogQk）→ `negLogQk_div_tendsto_condEntropyTail`（→H_k）→ `entropyRate_eq_lim_condEntropy`（→H）。**Phase 3 が「最大リスク」とした k-limit/n-limsup 交換（k(n)→∞ diagonal）は回避された** — 最終 LHS `limsup(lz/n)` が k に依存しないため、各固定 k で `limsup ≤ H_k/log2`（Lemma 1）を示し、k→∞ は **RHS だけ** で `inf_k H_k = entropyRate`（Lemma 2）を取れば足りる。k(n)→∞ の対角化も `Lmax = o(n)` a.s. も不要（overhead は全て `c/n → 0` + `x·log(1/x) → 0` boundary に帰着）。bit 化は `/Real.log 2` で機械整合。
5. **Step D（合成）**: per-n 比較不等式を `Filter.limsup_le_limsup` に乗せる。cobounded/bounded auto 引数は `lz78_impl_rate_le_const`（上界）+ `per_symbol_nonneg`（下界）で供給（headline `h_bdd_above` 既実証手法）。

**vehicle は per-step `markovFactor` conditional**。**joint `qkSingleton` を per-phrase marginal として `∑ -log qkSingleton(phrase)` するのは leg 4 marginal route と同じ方向逆 dead-end（D8 反復、禁止）**。**D4 path-prefix route（`condPhraseProb` / `blockProb_neg_log_ge_sum`、0 consumers）も `∑qⱼ≈c` trap で素通り**。leg 4 の `ZivMeasureBridge.lean` sub-distribution 機構（disjoint-cylinder 論法）は per-step conditional 版へ転用できる足場。

## Phase 詳細

### Phase 0 — M0 在庫確認（流用、~0 行）

leg 3 在庫 `lz78-m3-inventory.md`（§A SMB / §B 符号長 / §C Ziv 核 / §D blockLogAvg・entropyRate / §E Mathlib limsup API）が **本サブ計画の素材として既に完備**。W1 は閉じたので §E の self-build 要素 1（SMB-in-bits）は不要。新規在庫不要、§C/§D/§E を本計画 Phase に割り当てるだけ。**proof-log: no**。

### Phase 1 — gateway atom: Step A 符号長 bit-rate 展開（✅ GO、leg 3）

**結果（leg 3、commit `7171707`、sorryAx-free）**: `lz78_impl_bitrate_le_clogc_plus_overhead`（`GreedyParsingImpl.lean:286`、`[Nonempty α]` 追加）が **GO**。符号長 bit-rate を `c·log c/(log2·n) + overhead`（overhead = `(c·log 2 + c·(log₂|α|+2))/(log2·n)`）に分解、`lz78_impl_natLog_mul_log_two_le` + `bitLength_eq` で nat↔bit 単位整合を機械的に処理。**判定: nat↔bit 単位整合は壁でないと確定**（plumbing 級、想定外コスト無し）。proof-log 済。

**proof-log: yes**（gateway の go/no-go 記録、済）。

仮 signature（Mathlib-shape-driven、結論形を `blockLogAvg₂` 比較に噛ませる前段）:

```lean
-- a.s.-eventual ではなく決定論的・per-n の代数展開（ω は blockRV 経由で input に固定）
theorem lz78_impl_bitrate_le_clogc_plus_overhead
    (n : ℕ) (hn : 0 < n) (x : Fin n → α) :
    (lz78GreedyImplEncodingLength n x : ℝ) / (n : ℝ)
      ≤ ((c : ℝ) * Real.log (c : ℝ)) / (Real.log 2 * n)
          + ((Nat.log 2 (Fintype.card α) : ℝ) + 2 + (c : ℝ) / (n : ℝ)) / 1
    -- c := (lz78PhraseStrings (List.ofFn x)).length
```

- **供給資産**: `lz78_impl_rate_le_const` の証明内 `hlen`（`bitLength_eq` で `lz/n = c·(Nat.log 2(c+1)+log₂|α|+2)/n`）+ `lz78_impl_natLog_mul_log_two_le`（`Nat.log 2(c+1)·log 2 ≤ log(c+1)`）。`c·log(c+1) ≤ c·log c + c`（`log(c+1) ≤ log c + 1` を `c≥1` で、または `c·log(2c)=c·log2+c·log c`）。
- **novel か**: いいえ。`lz78_impl_rate_le_const`（`GreedyParsingImpl.lean:171`）の中身の切り出し + bit 化。
- **gateway 判定**: これが通れば nat↔bit 単位整合に想定外コストが無い = M2 tractable のシグナル。`+1` ずれ・`c=0` 退化に注意（`lz78_impl_rate_le_const` が既に処理済の手法を流用）。

### Phase 2 — genuine core（2a/2b/2c-i sorryAx-free 済、2c-ii = genuine wall）

leg 4–5 で分割。**2a/2b（convexity grouping + marginal 橋）+ 2c-i（node-context conditional sub-distribution + log-sum + chain-rule backbone）は sorryAx-free で建った**。残る genuine wall は **2c-ii = Ziv (k-state,length)-grouping (Lemma 13.5.5) + k(n) diagonal grafting**（既存 Q_k 資産への接合、medium）。

#### Phase 2a — convexity grouping（length 別 Jensen）✅ sorryAx-free（commit `c472518`）

抽象 Jensen grouping `c·log c ≤ ∑_ℓ c_ℓ·log c_ℓ + c·log(#groups)`（純 Finset/Real、`Real.convexOn_mul_log` + `ConvexOn.map_sum_le`）+ LZ 長さ別特化。**deliverable**: `card_mul_log_le_sum_group_mul_log_add_card_log`（`ZivLengthGrouping.lean:49`）+ `lz78PhraseStrings_card_mul_log_le_sum_length_group`（`:143`）、両 sorryAx-free。**判定**: convexity grouping それ自体は壁でない（D3 を回避する length-fiber 化は機械的に成立）。だが単独では `-log Pₙ` に届かない（per-group log-sum を source 確率に乗せる橋が別途必要）。

#### Phase 2b — marginal sub-distribution + log-sum 橋 ✅ sorryAx-free（commit `d1d55db`）— **方向不一致**

per-length **marginal** sub-distribution `∑_a P(a) ≤ 1` + per-group log-sum + 集約。**deliverable**: `sum_marginal_real_le_one`（`ZivMeasureBridge.lean:76`）+ `group_card_mul_log_le_sum_neg_log`（`:103`）+ `lz78PhraseStrings_mul_log_le_sum_neg_log_marginal_add_overhead`（`:184`、`c·log c ≤ ∑_phrases -log P_marginal + c·log D`）、全 sorryAx-free。**判定（machine-ruled-out）**: marginal 版は overhead が vanish するが、chain rule `-log Pₙ = ∑_j -log q_cond(j)` に対し memory 源では `q_cond ≥ P_marginal` ゆえ `∑ -log P_marginal ≥ -log Pₙ` = **欲しい `≤` と逆向き**（iid で等号、memory で逆、Dirac で両 0 alive）。FKG/positive-association の Mathlib 補題は loogle **0-hit**。**marginal では `-log Pₙ` を上から押さえられない** → 単独では genuine core を閉じない。ただし sub-distribution + log-sum の機構（disjoint-cylinder 論法）は conditional 版へ転用可能（necessary scaffolding）。

#### Phase 2c-i — node-context conditional sub-distribution + log-sum + chain-rule backbone ✅ sorryAx-free（commit `cfe518b`/`6accdd2`）

旧 plan が「次の genuine atom = node-context (conditional) sub-distribution `∑_a q(node·a|node) ≤ 1`」と呼んでいた **第三の量は既に建っている**（`ZivCondContext.lean`、全 sorry-free、[lz78-facts.md](lz78-facts.md) 達成テーブル）:

- `condContextProb`（`:151`、conditional `q(symbol|context)` = cylinder 比、marginal でも path-prefix でもない）
- `condContext_sum_le_one`（`:174`、`∑_a q(v·a|v) ≤ 1`、Kolmogorov consistency `sum_extend_marginal_real_eq` から）
- `condContext_card_mul_log_le_sum_neg_log`（`:193`、per-context log-sum step）
- `sum_neg_log_condContextProb_path_eq_blockLogAvg`（`:292`、chain-rule backbone `∑ -log q_cond = n·blockLogAvg`）。**但し full-history context（全 distinct）ゆえ fiber size 1 で trivial → Ziv grouping vehicle にはならない。k=∞ reference として保持**、grouping には使わない。

#### Phase 2c-ii — Ziv (k-state, length)-grouping + composition brick ✅ CLOSED sorryAx-free（leg 8–10）

**proof-log: yes**（leg 8–10 で記録済）。**`c·log c ≤ negLogQk + o(n)` composition brick 全体が CLOSED sorryAx-free + 独立監査 PASS**。Step B-naive（node-position D3 / marginal D8）が machine-ruled-out された後、生き残った構造 = **既存 kth-order Markov 測度 Q_k への grafting** が leg 10 で完遂された。

**leg 8–10 結果（達成テーブル [lz78-facts.md](lz78-facts.md)「threading 配線」「grouping bridge + overhead 制御」が SoT、`#print axioms` で再導出）**:

- **threading + tiling 材料化（leg 8–9）**: gateway atom `markovFactor_blockRV_eq_window` + factor correspondence 5 補題 + `negLogQk_phrase_threading` body fill + `lz78_block_tiling`（leg 9 CLOSED、`@audit:ok`）すべて sorryAx-free。
- **composition brick（leg 10、`ziv_achievability_composition`、新 file `ZivAchievabilityComposition.lean:194`、`@audit:ok`）**: a.s. `∃ c bAbsorbed Ntot, c+bAbsorbed = #phrases ∧ bAbsorbed ≤ k+1 ∧ Ntot ≤ n ∧ (c:ℝ)·log c ≤ negLogQk μ p k n ω + (c·log(Ntot/c)+c+c·log((card α)^k))`。
  - **(W) empirical-overhead brick** `condState_grouping_bound_mean`（`ZivCondGrouping.lean:340`、`@[entry_point]`）+ helper `state_marginalization_bound`（`:246`）= worst-case `c·log D` を manifestly-o(n) mean-length 形に supersede。旧 `condState_grouping_bound` は consumer-less → retract-candidate。
  - **sub-step (A)** `phraseSum_le_negLogQk`（`:111`）+ unconditional `pmfLogCondMarkov_nonneg`（`:84`）。
  - **sub-step (B)** position↔distinct-phrase reindex = 新 pure-List 補題 `flatten_drop_take_getElem`（`GreedyLongestPrefix.lean:320`）+ `condQkState_pos_of_markovFactor_pos`（`ZivThreading.lean:324`）+ `condQkState_congr_length`（`:141`）。
  - **3 sig-strengthening**（`lz78_parse_tiling_positions`/`lz78_block_tiling`/`negLogQk_parse_threading`）= 全て output-strengthening（`∃`-conjunct 追加、入力仮説の追加ではない）と再監査済 = honesty PASS。**vehicle は per-step markovFactor conditional**（joint qkSingleton-per-phrase-marginal は D8 反復で禁止、遵守済）。

### Phase 3 — (V) diagonalization ✅ CLOSED（leg 11、`c22f2d5`）

composition brick `c·log c ≤ negLogQk + o(n)`（CLOSED）を `entropyRate₂` に持ち上げる analytic 核を、**対角化なし**で閉じた。各固定 k で `limsup(lz/n) ≤ conditionalEntropyTail k / log2`（Lemma 1 `ziv_aseventual_le_condEntropyTail_bits`、`:619`）+ inf over k で `limsup(lz/n) ≤ entropyRate₂`（Lemma 2 `ziv_aseventual_le_entropyRate₂`、`:869`、`entropyRate_eq_lim_condEntropy` の RHS inf を取る）、両 sorryAx-free。**「最大リスク = k-limit/n-limsup 交換（k(n)→∞ 対角化）」は不要だった** — 最終 LHS `limsup(lz/n)` が k 非依存ゆえ LHS を k 固定の AEP に乗せる必要がなく、k→∞ は RHS だけで足りる。連動して **`Lmax = o(n)` known sub-task も不要**（overhead vanishing は全て `c/n → 0` = `lz78PhraseStrings_count_isBigO` + `x·log(1/x) → 0` boundary に帰着、private helper `clog_div_le_two_mul_sqrt`/`cp_log_cp_le_reconcile`）。

### Phase 4 — (Z) W2 discharge ✅ CLOSED（leg 11、`c22f2d5`）

`ziv_aseventual_le_blockLogAvg₂`（`GreedyParsingImpl.lean:917`、`@audit:ok`）を `filter_upwards [ziv_aseventual_le_entropyRate₂, shannon_mcmillan_breiman₂]` + `h_smb.limsup_eq`（RHS を `entropyRate₂` に書換え）で sorryAx-free 化。consumer `lz78GreedyImpl_achievability_ae`（`:1005`、`@audit:ok`）も sorryAx-free → **achievability 完遂**。signature 不変（ripple ゼロ）、docstring は achievability 壁 `lz78-aseventual-ziv` の `@residual` を除去 → `@audit:ok`、独立 honesty audit PASS。`#print axioms` = `[propext, Classical.choice, Quot.sound]`（再検証コマンドは [lz78-facts.md](lz78-facts.md) 達成テーブル）。

## 地雷の不変条件（再探索禁止、各 atom が抵触しないこと）

- **D1**: per-block `c·log c ≤ -log Pₙ`（∀n∀ω, clean）は **FALSE**（反例 `a^16`, c=5, -log Pₙ=0）。→ Phase 2c-ii は **a.s.-eventual + overhead 項込みの per-n 形 + AEP**、限界は limsup でのみ取る。
- **D2**: overhead 版 `c·log c ≤ -log Pₙ + c·log(|α|+1)`（∀n∀ω）も **FALSE**（`Pₙ→1` family）。→ overhead は finite-k truncation の vanish する項であって定数 `c·log(|α|+1)` ではない。
- **D3（machine-ruled-out）**: node-position-grouping overhead `(c·log #nodes)/n`（#nodes≈c）は **定数収束（vanish しない）** = treenode T1-T5 literal が死ぬ。→ finite-k で #states を有界にして overhead vanish。`log #nodes=log c` を `log log n` と取り違えない。
- **D4**: path-prefix `Q_c = ∏ condPhraseProb` の AEP（`blockProb_neg_log_ge_sum` / `condPhraseProb`、`ZivEntropyBridge.lean`）は **0 direct consumers**（機械裏取り、dead-start、`∑ⱼqⱼ≈c` trap）。→ Phase 2c-ii は **path-prefix を素通り**（vehicle は per-step markovFactor conditional `∑_a markovFactor(s,a)≤1` / `condContext_sum_le_one` という第三の量）。
- **D8（machine-ruled-out）**: marginal-length-grouping は overhead vanish だが **方向不一致** — memory 源で `∑ -log P_marginal ≥ -log Pₙ`（chain rule `-log Pₙ = ∑_j -log q_cond(j)` + `q_cond ≥ P_marginal`）= 欲しい `≤` と逆。FKG/positive-association loogle 0-hit。→ Phase 2c-ii は **conditional** markovFactor / q(symbol|context) を使う（marginal 不可）。**joint `qkSingleton(phrase)` を per-phrase marginal として `∑ -log qkSingleton(phrase)` するのも同じ D8 反復で禁止**（leg 4 marginal route と方向逆 dead-end）。

各 Phase の抵触チェック: Phase 1（決定論的代数展開、D1–D8 無関係）/ Phase 2a（convexity grouping、D3 を length-fiber で回避）/ Phase 2b（marginal sub-dist、D8 に該当して方向不一致＝単独で genuine core を閉じない）/ Phase 2c-i（node-context conditional sub-dist + log-sum + backbone、第三の量で D4・D8 回避、sorry-free 済）/ Phase 2c-ii（Q_k grafting：per-step markovFactor conditional の (k-state,length)-grouping、D1/D2 を AEP で / D3 を finite-k で / D4・D8 を conditional sub-dist で全て回避。**joint qkSingleton-per-phrase-marginal は D8 反復で禁止**）/ Phase 3（overhead vanish = D2/D3 準拠）/ Phase 4（limsup 合成、per-block 形を作らない = D1 準拠）。

## gateway atom 結果

**Phase 1（単位整合 gateway）= `lz78_impl_bitrate_le_clogc_plus_overhead` = GO**（commit `7171707`、sorryAx-free）。nat↔bit 単位整合は壁でないと確定（plumbing 級）。

**Phase 2a/2b（convexity grouping + marginal sub-dist 橋）= 両 sorryAx-free だが genuine core を閉じない**（commit `c472518`/`d1d55db`、necessary scaffolding）。

**Phase 2c-i の gateway atom = node-context conditional sub-distribution `∑_a q(node·a|node) ≤ 1` = `condContext_sum_le_one` = GO**（commit `cfe518b`、sorryAx-free）。旧「次の genuine atom」は **既に建っている**（[lz78-facts.md](lz78-facts.md) 達成テーブル）。chain-rule backbone `sum_neg_log_condContextProb_path_eq_blockLogAvg`（`6accdd2`）も sorry-free。

**Phase 2c-ii（threading + tiling + composition brick `c·log c ≤ negLogQk + o(n)`）= CLOSED sorryAx-free + 全監査 PASS**（leg 8–10、`ziv_achievability_composition` `@audit:ok`、`19314ee`/`65afc03`/`a25fd25`/`1ef7700`/`3867a29`）。Cover-Thomas Lemma 13.5.5 の (k-state,length)-grouping log-sum + (W) empirical-overhead + (A)(B) reindex がすべて閉じた。

**Phase 3 (V) diagonalization + Phase 4 (Z) W2 discharge = CLOSED**（leg 11、`c22f2d5`、sorryAx-free + 独立監査 PASS）。**(V) は対角化不要と判明**（最終 LHS が k 非依存 → 各 k bound + inf over k）、Phase 3/4 詳細セクション参照。**本サブ計画の目標は全て達成**。

## 撤退ライン（全 Phase CLOSED により invoke されず、履歴として保持）

- **route 履歴**: 旧 `lz78-ziv-treenode-plan.md`（node-position-grouping = route B）は D3 trap で reject 済（部分 un-park: conditional sub-distribution = 旧 T2 は genuine に必要な核と leg 4 で確認、leg 5 で `condContext_sum_le_one` として建った）。
- 退出口は **sorry + `@residual` のみ** という不変条件は遵守された（hypothesis bundling 無し、W2 signature `(μ, p)` + `[IsProbabilityMeasure μ]` regularity のみで不変）。

## 規模・リスク総括（達成後）

- **総計（実績）**: 全 Phase CLOSED。Phase 1/2a/2b/2c-i + Phase 2c-ii composition brick（sorryAx-free、leg 8–10）+ Phase 3 (V) + Phase 4 (Z)（leg 11）。旧「~300–600 行 research-level」は Q_k 資産発見 + composition closure + 対角化回避で大幅に是正。
- **最大リスクの帰結**: Phase 3 (V) を「highest risk = k-limit/n-limsup 交換」と評価していたが、**最終 LHS が k 非依存ゆえ対角化不要**と判明し回避（リスクは構造を見直すと存在しなかった、cause:single-route）。Phase 4 (Z) は plumbing（低、予想通り）。

## 判断ログ

1. **W1 は閉鎖済として扱う（在庫の W1 自前 closure 想定は obsolete）**: 在庫 `lz78-m3-inventory.md` は W1（SMB-in-bits 橋）を「自前 closure 対象（~30–60 行）」と書くが、leg 3 で `shannon_mcmillan_breiman₂`（`GreedyParsingImpl.lean:520`、`@audit:ok`、sorryAx-free）として **既に閉じた**。本サブ計画の対象は W2 のみ。
2. **bit 単位で建てる（verbatim 確認の帰結）**: SMB-in-bits が既に `blockLogAvg₂`（bit）で握り、W2 RHS も `limsup blockLogAvg₂`。target を bit 形 `c·log₂c ≤ -log₂Pₙ + o(n)` で建て、nat 量（`lz78PhraseStrings_mul_log_le`、`blockLogAvg_eq_neg_log_blockProb`）は `/Real.log 2` で機械整合。`c·log c ≤ -log Pₙ`（nat）を直接 def 化しない（W2 の Mathlib-shape は bit）。
3. **ripple ゼロ（機械確認）**: `ziv_aseventual_le_blockLogAvg₂` の direct consumer は 1 decl（`lz78GreedyImpl_achievability_ae`、同 file、statement 依存のみ）。W2 の body を埋めるだけで signature 不変 → 配線変更不要。`blockProb_neg_log_ge_sum`（D4）は 0 consumers（dead-start 裏取り）。
5. **achievability W2 CLOSED + 対角化回避（leg 11、`c22f2d5`、独立監査 PASS）**: W2 `ziv_aseventual_le_blockLogAvg₂` を sorryAx-free 化し（`@audit:ok`）、consumer `lz78GreedyImpl_achievability_ae` も sorryAx-free → achievability 完遂。**Phase 3 が「最大リスク」とした k-limit/n-limsup 交換（k(n)→∞ 対角化）は不要だった** — 最終 LHS `limsup(lz/n)` が k に依存しないため、LHS を k 固定の AEP に乗せる必要がなく、各固定 k で `limsup ≤ H_k/log2`（Lemma 1）を示し k→∞ は **RHS だけ** で `inf_k H_k = entropyRate`（Lemma 2）を取れば足りた。連動して known sub-task `Lmax = o(n)` a.s. も不要（overhead vanishing は `c/n → 0` + `x·log(1/x) → 0` boundary に帰着）。plan/facts/roadmap が固めていた「対角化必須・最大リスク」framing は単一ルート過大評価で、構造を見直すと回避できた（cause:single-route）。残 headline 壁 = M4 converse のみ。

4. **composition brick CLOSED → 残 active = (V)+(Z)（leg 10、`19314ee`/`65afc03`/`a25fd25`/`1ef7700`/`3867a29`）**: leg 5 の route 是正（Q_k grafting、Q_k 資産は既存 sorry-free）を踏まえ、leg 8–10 で **`c·log c ≤ negLogQk + o(n)` composition brick 全体が CLOSED sorryAx-free + 独立監査 PASS**（`ziv_achievability_composition` `@audit:ok`、[lz78-facts.md](lz78-facts.md) が SoT）。Cover-Thomas Lemma 13.5.5 の (k-state,length)-grouping log-sum + (W) empirical-overhead `condState_grouping_bound_mean`（worst-case `c·log D` を supersede、旧 `condState_grouping_bound` retract-candidate）+ (A) `phraseSum_le_negLogQk`（unconditional `pmfLogCondMarkov_nonneg`）+ (B) reindex（`flatten_drop_take_getElem` 等）がすべて閉じた。3 sig-strengthening は output-strengthening と再監査済。**vehicle は per-step markovFactor conditional**（joint qkSingleton-per-phrase-marginal は D8 反復で禁止、遵守済）。両単純 grouping（node-position D3 / marginal D8）は依然 machine-ruled-out（再探索禁止）。**残 active = Phase 3 (V) diagonalization（k-limit/n-limsup 交換 + `Lmax = o(n)` a.s.、highest risk）→ Phase 4 (Z) W2 discharge** のみ。achievability 壁 `lz78-aseventual-ziv` はこの時点では honest に維持されていた（TRUE-as-framed、(V) 未証明）が、leg 11 で CLOSED（`c22f2d5`）。
   - **記録のみ（コード触らない）**: `isLZ78PerPathParsingFactorization_of_pos` が `ZivEntropyBridge.lean`/`Stationary/Kernel.lean` の docstring で「genuinely constructed」と記載されているが実在 decl が無い（phantom 確認）。コード docstring fact error、別途修正候補（SoT はコード側、今回は記録のみ）。
