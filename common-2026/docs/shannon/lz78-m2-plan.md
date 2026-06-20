# LZ78: M2 length-grouping Ziv 組合せ不等式 サブ計画

> **Parent**: [`lz78-completion-roadmap.md`](lz78-completion-roadmap.md) §1 M2 / M3
> （壁 `@residual(wall:lz78-aseventual-ziv)`、W2 = `ziv_aseventual_le_blockLogAvg₂`）

## 進捗

- [x] M0 在庫確認（leg 3 `lz78-m3-inventory.md` + leg 4 `lz78-m3-treenode-inventory.md` の route A/B 比較）✅
- [x] Phase 1 — gateway atom（Step A 符号長 bit-rate 展開）✅ **GO**（`lz78_impl_bitrate_le_clogc_plus_overhead`、`GreedyParsingImpl.lean:286`、sorryAx-free、commit `7171707`）→ 単位整合は壁でないと確定
- [ ] Phase 2 — length-grouping log-sum 核（genuine novel）🔄 **leg 4: gateway atom（抽象 Jensen grouping）実装中**（`ZivLengthGrouping.lean`、leg 3 の STALL は route 取り違え artifact — 判断ログ #4）
- [ ] Phase 3 — overhead o(n) 制御 + limsup 合成 📋（Phase 2 gateway 通過後に着手）
- [ ] Phase 4 — W2 discharge（`ziv_aseventual_le_blockLogAvg₂` の sorry を埋める）📋（達成まで `sorry` + `@residual(wall:lz78-aseventual-ziv)` 維持）

## ゴール

W1（`shannon_mcmillan_breiman₂`、SMB-in-bits 橋）は leg 3 で **閉鎖済**（`@audit:ok`、sorryAx-free、`GreedyParsingImpl.lean:520`）。本サブ計画のゴールは残る **W2 = `ziv_aseventual_le_blockLogAvg₂`**（`GreedyParsingImpl.lean:557`、`@residual(wall:lz78-aseventual-ziv)`、唯一の active sorry）を **genuine に discharge** すること。W2 が閉じれば `lz78GreedyImpl_achievability_ae` が sorryAx-free 化され（合成本体は既に sorry-free）、**achievability 完遂**（headline に残るは M4 converse 壁のみ）。

**status（leg 4、route 是正後）**: Phase 1 gateway = **GO**（`lz78_impl_bitrate_le_clogc_plus_overhead` sorryAx-free、単位整合は壁でない）。**leg 3 の「STALL = single in-session で閉じない genuine research-level 壁、攻略は treenode T1-T5 路」は route 取り違えによる過大評価だった**（leg 4 の独立調査 = inventory `lz78-m3-treenode-inventory.md` + proof-pivot-advisor、両者機械裏取りで判明）:

- **route B (node-grouping = treenode T1-T5) は D3 trap で死ぬ**: overhead `c·log(#nodes) ≈ c·log c`、`lz78PhraseStrings_mul_log_le`（`c·log c ≤ K·n`、sorryAx-free）より `(c·log c)/n` は定数 = main term と同オーダーで vanish しない。数学的に細工不能。加えて treenode plan が「再利用、転記主体」と書く資産（`extendCylinder*`/`condNextSymbol_sum_eq_one`/`IsLZ78ZivCombinatorialCore`/ファイル `LZ78ZivCombinatorics.lean`/`LZ78ZivEntropyBridge.lean`）は commit `f67ec8a`/`602b1ad` で **削除済 (disk 不在)** = resurrection は転記でなく ~750-1100 行のゼロ再構築。`condPhraseProb` も固定 tuple `v` でなく観測 `ω` で parametrize された path-prefix 比なので node-context sub-distribution を既存資産から抽出できない。
- **唯一の genuine route = (A) length-grouping**（同じ長さ ℓ の distinct phrase ≤ |α|^ℓ、#groups = O(log n)、overhead `c·log log n` → vanish）= **本 m2-plan の Approach (Step A-D) そのもの**。leg 3 が「genuine research-level」と評価したのは node/path-prefix route を probe した artifact で、**route A の gateway atom（抽象 Jensen grouping 不等式）は leg 3 で一度も isolated に試されていない**。最難サブピース（packing `card_short_le`/`total_length_ge_count_mul_log`、envelope `count_isBigO`）は既に sorryAx-free in-tree → length-grouping を正しく取れば **1-2 leg で閉じる見込み**（earned research-level verdict ではない）。
- **decisive gateway atom（leg 4 で実装中）**: 抽象 Jensen grouping `c·log c ≤ ∑_ℓ c_ℓ·log c_ℓ + c·log(#groups)`（純 Finset/Real、`Real.convexOn_mul_log` + `ConvexOn.map_sum_le`）= treenode plan 判断 3 / feasibility リスク #1 そのもの。`InformationTheory/Shannon/LZ78/ZivLengthGrouping.lean` に実装。
- **壁は維持**: 結果が出るまで W2 = `sorry` + `@residual(wall:lz78-aseventual-ziv)` を honest に維持（discharge しない）。撤退ラインは「gateway atom が通らなければ tier-2 維持」。

W2 の verbatim signature（`GreedyParsingImpl.lean:557`、変更しない）:

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

### length-grouping 戦略の骨子（D3: node-grouping は偽）

genuine missing piece = `c·log c`（組合せ phrase count）を `-log Pₙ`（source 確率）に繋ぐ length-grouping 不等式 + overhead 制御。骨子:

1. **Step A（gateway）**: 符号長 bit-rate を `c·log₂c/n` 型に展開。`lz78_impl_rate_le_const` の証明内 `hlen`（`bitLength_eq` 展開）+ `hterm1`（`lz78_impl_natLog_mul_log_two_le`）を切り出して a.s.-eventual の比較対象を作る。**既存ピース流用、低リスク**。
2. **Step B（genuine novel = 最大の難所）**: `c·log₂c ≤ -log₂Pₙ + overhead` を a.s.-eventual で建てる。phrase を **長さ別にグルーピング**（同じ長さ `ℓ` の phrase は高々 `|α|^ℓ` 個）し、log-sum を `-log Pₙ`（= `n·blockLogAvg₂·log 2`）に対し下から押さえる。**node-grouping（`c·log D/n`、D≈c で定数収束、vanish しない）は D3 で偽 → 必ず length-grouping**。
3. **Step C（overhead o(n)）**: overhead = `c·H(length-dist) ≤ c·log(maxlen)`、`maxlen ≤ log_b n`（最長 phrase 長は対数オーダー）、`(c·log log n)/n → 0` を `c = O(n/log n)`（`lz78PhraseStrings_count_isBigO`、`ZivCountingBody.lean:410` verbatim、envelope `n/Real.log n`）と合成。`(c·log log n)/n = O((log log n)/log n) → 0`。
4. **Step D（合成）**: per-n 比較不等式を `Filter.limsup_le_limsup` に乗せる。cobounded/bounded auto 引数は `lz78_impl_rate_le_const`（上界、`GreedyParsingImpl.lean:171` verbatim）+ `per_symbol_nonneg`（下界）で供給（headline `h_bdd_above` 既実証手法）。

**D4 path-prefix route（`condPhraseProb` / `blockProb_neg_log_ge_sum`）は素通り**: `blockProb_neg_log_ge_sum` は **0 consumers**（本セッション `dep_consumers.sh` 機械裏取り、dead-start）で、握るのは `∑ⱼ -log qⱼ ≤ -log Pₙ` であって、missing piece の `c·log c ≤ ∑ⱼ -log qⱼ + o(n)`（`∑qⱼ≈c` trap、D4）ではない。length-grouping log-sum を **`-log Pₙ` に直接乗せる**（`∑qⱼ` を経由しない）。

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

### Phase 2 — length-grouping log-sum 核（🔄 leg 4: gateway atom 実装中）

**route 是正（leg 4）**: leg 3 の「stall = 2b の `c·log c ≤ -log Pₙ + o(n)` 接続 = 可変深さ tree-node AEP = single in-session plan で閉じない genuine research-level scope」は **node/path-prefix route を probe した artifact**。leg 4 の独立調査（inventory `lz78-m3-treenode-inventory.md` + proof-pivot-advisor、機械裏取り）で、その接続を **path-prefix `∑qⱼ`（D4 trap）/ node-grouping（D3 trap）でなく length-grouping で取れば壁ではない** と判明:

- **length-grouping log-sum の決定的 atom = 抽象 Jensen grouping** `c·log c ≤ ∑_ℓ c_ℓ·log c_ℓ + c·log(#groups)`（純 Finset/Real）を、phrase を `List.length` で fiber 化（`card_eq_sum_card_fiberwise` / `sum_fiberwise_of_maps_to`、Finset API 完備）した上で `Real.convexOn_mul_log` + `ConvexOn.map_sum_le` で建てる。`#groups = O(log n)`（maxlen lemma）なので overhead `c·log(#groups) = c·log log n` は `(c·log log n)/n = O((log log n)/log n) → 0` で vanish（D3 をクリア）。これが leg 3 で一度も isolated に試されていない gateway atom。
- leg 3 の refutation（sorryAx-free 単一 bound `c·log c ≤ 8·log(|α|+1)·n` は constant limsup しか出さず低エントロピー源で `entropyRate₂` 超過 = 不十分）は **「単一 bound では届かない」** ことを示すのみで、**length-grouping log-sum が届かないことを示していない**（length 別に entropy を割り当てると per-group bound の和が `-log Pₙ` に乗る）。

**proof-log: yes**（gateway atom の go/no-go 記録必須）。実装 = `InformationTheory/Shannon/LZ78/ZivLengthGrouping.lean`。

これが **genuine missing piece**（Mathlib にも codebase にもない核）。`c·log c` を `-log Pₙ` に繋ぐ length-grouping 不等式。**更に小分けに**:

- **2-gateway. 抽象 Jensen grouping atom**（leg 4、★最初に試す）。phrase 数を長さで fiber 化したときの `c·log c ≤ ∑_ℓ c_ℓ·log c_ℓ + c·log(#groups)`（純 Finset/Real、`Real.convexOn_mul_log` + `ConvexOn.map_sum_le`、in-project `log_sum_inequality` を group 集合に 1 回適用）。leg 3 で一度も isolated に試されていない decisive atom。これが通れば length-grouping が tractable のシグナル。`ZivLengthGrouping.lean` に実装。
- **2a. length-distribution の log-sum 下界**（novel、~60–120 行）。phrase strings を長さ別に分類し、`∑ phrases -log(per-phrase prob) ≥ c·log c - c·H(length-dist)` 型の組合せ不等式。供給テンプレート = `total_length_ge_count_mul_log`（`ZivCountingBody.lean:190` verbatim、`c·log c ≤ 8·log(|α|+1)·T`）の packing 論法（同じ長さの distinct phrase は高々 `|α|^ℓ` 個 → 長さ別 entropy bound）。`lz78PhraseStrings_nodup`（`GreedyLongestPrefix.lean:123`）が distinctness 前提を供給。
- **2b. per-path log-sum を `-log Pₙ` に接続**（novel + 既存橋、~40–80 行）。**D4 trap 回避が crux**: `∑ⱼ -log qⱼ`（path-prefix、`∑qⱼ≈c` trap）を経由せず、length-grouped log-sum を **直接** `-log Pₙ = n·blockLogAvg`（`blockLogAvg_eq_neg_log_blockProb`、`ZivEntropyBridge.lean:126` verbatim、`0 < n` + `0 < Pₙ` 前提）に乗せる。`0 < Pₙ` は a.s. regularity（observed cylinder 正質量）→ `∀ᵐ ω` の中で供給。
- **novel か**: **はい、2-gateway/2a/2b が核**。2-gateway は抽象 Jensen grouping、2a は length-grouped packing の組合せ核（`total_length_ge_count_mul_log` の packing を長さ別 entropy 形に拡張）、2b は length-sum を source 確率に乗せる接続。最難サブピース（packing `card_short_le`/`total_length_ge_count_mul_log`、envelope `count_isBigO`）は既に sorryAx-free in-tree。Mathlib に LZ78/Ziv 不等式は無い（loogle 0、在庫裏取り済）。

**地雷チェック**: per-block `∀n∀ω` 形にしない（D1/D2 FALSE、反例 `a^16`）。2a/2b は **per-n 不等式 + overhead 項込み**で、limsup 形で o(n) を吸収して初めて成立。clean `c·log c ≤ -log Pₙ`（D1）や overhead 付き ∀n∀ω（D2）を書いた瞬間に即撤退。

### Phase 3 — overhead o(n) 制御 + limsup 合成（~50–100 行、medium）

**proof-log: no**（plumbing 級だが o(n) 評価のみ注記）。

- **3a. overhead → 0**（~30–60 行）。`overhead(n) = c·log(maxlen)/n`。`maxlen ≤ log_b n`（最長 phrase 長 = 対数オーダー、`(|α|+1)^maxlen ≤ n` 型から）。`(c·log log n)/n` を `c = O(n/log n)`（`lz78PhraseStrings_count_isBigO`、`ZivCountingBody.lean:410` verbatim、envelope `n/Real.log n`）と合成 → `O((log log n)/log n) → 0`。`blockRV n ω` を `input n` として食わせる際は `lz78PhraseStrings_mul_log_le_of_length`（`:393`）/ `count_isBigO`（`hlen : (input n).length = n`）形に。`blockRV n ω` の length は `n`（`blockRV` の定義から、要 verbatim 確認）。
- **3b. limsup 合成**（~20–40 行）。Phase 1（Step A）+ Phase 2（c·log₂c ≤ -log₂Pₙ + overhead）+ Phase 3a（overhead→0）を `∀ᶠ n` の per-n 比較 `lz/n ≤ blockLogAvg₂ + err(n)`、`err→0` にまとめ、`Filter.limsup_le_limsup`（`LiminfLimsup.lean:198` verbatim、cobounded/bounded auto 引数）+ `Tendsto.add` 系（`err→0` を limsup に吸収）で `limsup(lz/n) ≤ limsup blockLogAvg₂`。cobounded/bounded witness = `lz78_impl_rate_le_const`（上界）+ `per_symbol_nonneg`（下界）、`Filter.isBoundedUnder_of`（headline `h_bdd_above` 実証手法）。

### Phase 4 — W2 discharge（~10–30 行、低リスク・配線のみ）

**proof-log: no**。

`ziv_aseventual_le_blockLogAvg₂`（`GreedyParsingImpl.lean:557`）の `sorry` を Phase 1–3 の合成で埋める。`∀ᵐ ω` の中で `0 < Pₙ`（a.s. regularity）+ `0 < n` を供給し、per-n 比較 → `limsup_le_limsup`。**signature は変えない**（statement は既に正しい Mathlib-shape）。完了後:

- consumer `lz78GreedyImpl_achievability_ae`（合成本体 sorry-free）が **sorryAx-free 化** → `#print axioms ziv_aseventual_le_blockLogAvg₂` / `lz78GreedyImpl_achievability_ae` = `[propext, Classical.choice, Quot.sound]` を機械確認（DoD proof done）。
- docstring の `@residual(wall:lz78-aseventual-ziv)` を除去し `@audit:ok` 化（**独立 honesty audit を要請** — 新 sorry 消滅 + signature honest 確認）。
- 親 roadmap §0/§1 の M3 行・achievability 状態を **child=SoT で同期更新**（W2 closed、headline 残壁 = M4 のみ）、`audit-tags.md` register の `lz78-aseventual-ziv` 行を CLOSED 注記。

## 地雷の不変条件（再探索禁止、各 atom が抵触しないこと）

- **D1**: per-block `c·log c ≤ -log Pₙ`（∀n∀ω, clean）は **FALSE**（反例 `a^16`, c=5, -log Pₙ=0）。→ Phase 2 は **a.s.-eventual + overhead 項込みの per-n 形**、限界は limsup でのみ取る。
- **D2**: overhead 版 `c·log c ≤ -log Pₙ + c·log(|α|+1)`（∀n∀ω）も **FALSE**（`Pₙ→1` family）。→ Phase 2/3 の overhead は **`c·log(maxlen)`（length-grouping、vanish する）**であって定数 `c·log(|α|+1)` ではない。
- **D3**: node-grouping overhead `(c·log D)/n`（D≈c）は **定数収束（vanish しない）**。→ Phase 2/3 は **必ず length-grouping**（overhead `c·log(maxlen)`、support 指数的に小 → vanish）。`log D=log c` を `log(n/c)≈log log n` と取り違えない。
- **D4**: path-prefix `Q_c = ∏ condPhraseProb` の AEP（`blockProb_neg_log_ge_sum` / `condPhraseProb`、`ZivEntropyBridge.lean`）は **0 direct consumers**（本セッション機械裏取り、dead-start、`∑ⱼqⱼ≈c` trap）。→ Phase 2b は **素通り**（`∑qⱼ` を経由せず length-grouped log-sum を直接 `-log Pₙ` に乗せる）。

各 Phase の抵触チェック: Phase 1（決定論的代数展開、limsup 対象を作るだけ、D1–D4 無関係）/ Phase 2a（length-grouped packing、D3 準拠）/ Phase 2b（`-log Pₙ` 直結、D4 素通り）/ Phase 3（overhead vanish = D2/D3 準拠）/ Phase 4（limsup 合成、per-block 形を作らない = D1 準拠）。

## gateway atom 結果

**Phase 1（単位整合 gateway）= `lz78_impl_bitrate_le_clogc_plus_overhead`（Step A 符号長 bit-rate 展開）= GO**（gateway-atom-first、commit `7171707`、sorryAx-free）。

- gateway 通過 → nat↔bit 単位整合（`Nat.log 2` ↔ `Real.log/log 2`、`+1` ずれ、`c=0` 退化）に想定外コスト無し = **単位整合は壁でない**と確定。Phase 1 の go/no-go gate は「単位整合の go」を意味し、「M2 全体 tractable」までは含意しない。

**Phase 2（length-grouping log-sum）の真の gateway atom = 抽象 Jensen grouping**（leg 4 で実装中、`ZivLengthGrouping.lean`）。

- leg 3 は Phase 1 通過後に Phase 2b を **path-prefix `∑qⱼ`（D4）/ node-grouping（D3）route で probe** し、「可変深さ tree-node AEP = genuine 壁」と評価したが、これは **route 取り違えによる artifact**（leg 4 の inventory + proof-pivot-advisor で機械裏取り）。length-grouping log-sum の decisive atom（抽象 Jensen grouping `c·log c ≤ ∑_ℓ c_ℓ·log c_ℓ + c·log(#groups)`）は **leg 3 で一度も isolated に dispatch されていない** = gateway-atom-first の atom 選定自体が誤っていた。
- length-grouping route なら #groups=O(log n) で overhead vanish（D3 クリア）、最難サブピースは既に sorryAx-free in-tree。gateway atom が通れば **1-2 leg で閉じる見込み**。

## 撤退ライン

- **gateway atom（抽象 Jensen grouping、leg 4）が通らない** → length-grouping log-sum 核が想定より重い → **`ziv_aseventual_le_blockLogAvg₂` を `sorry` + `@residual(wall:lz78-aseventual-ziv)` 維持**（tier-2 honest）。結果が出るまで W2 は discharge しない。
- **gateway（Phase 1、単位整合）が ~1 セッション以内に通らない** → 単位整合に想定外コストのシグナル（leg 3 で **不該当**、gateway は GO）。
- **Phase 2（length-grouping log-sum 核 2-gateway/2a/2b）が通らない** → genuine 組合せ核が想定より重い。同様に **`ziv_aseventual_le_blockLogAvg₂` を `sorry` + `@residual(wall:lz78-aseventual-ziv)` 維持**。
- 退出口は **sorry + `@residual` のみ**。hypothesis bundling（`*Hypothesis` / `*Reduction` predicate に core を抱えさせる）は **禁止**（CLAUDE.md「検証の誠実性」）。W2 の signature（`(μ, p)` + `[IsProbabilityMeasure μ]` regularity のみ）を変えない。Phase 2/3 で建てた個別 atom が sorry を持つなら、それぞれ `@residual(wall:lz78-aseventual-ziv)`（同壁）または新規 plan-slug を付与。
- **route 是正（leg 4）**: 旧 `lz78-ziv-treenode-plan.md`（node-grouping route B）は **D3 trap + 削除済資産で reject**（parked、判断ログ #4）。攻略は **本 m2-plan の length-grouping route A**（Step A-D + 抽象 Jensen gateway atom）。

## 規模・リスク総括

- **総計**: ~210–440 行（Phase 1: 30–60 / Phase 2: 120–250 / Phase 3: 50–100 / Phase 4: 10–30）。在庫 `lz78-m3-inventory.md` 自前要素 2（a.s.-eventual Ziv 比較、~150–400 行 medium）に整合。
- **支配項・最大リスク**: Phase 2（length-grouping log-sum 核、genuine novel、medium–high）。Phase 1/3/4 は plumbing〜既存資産流用（低〜medium）。leg 4 route 是正で「research-level、数 leg」評価は撤回 — gateway atom が通れば **1-2 leg 見込み**。
- **genuine novel 核の所在**: Phase 2-gateway（抽象 Jensen grouping）+ Phase 2a（length-grouped packing 組合せ核、`total_length_ge_count_mul_log` の packing を長さ別 entropy 形に拡張）+ Phase 2b（length-sum → `-log Pₙ` 直結、D4 trap 回避）。これ以外（Step A 展開・overhead vanish・limsup 合成）は既存資産。

## 判断ログ

1. **W1 は閉鎖済として扱う（在庫の W1 自前 closure 想定は obsolete）**: 在庫 `lz78-m3-inventory.md` は W1（SMB-in-bits 橋）を「自前 closure 対象（~30–60 行）」と書くが、leg 3 で `shannon_mcmillan_breiman₂`（`GreedyParsingImpl.lean:520`、`@audit:ok`、sorryAx-free）として **既に閉じた**。本サブ計画の対象は W2 のみ。
2. **bit 単位で建てる（verbatim 確認の帰結）**: SMB-in-bits が既に `blockLogAvg₂`（bit）で握り、W2 RHS も `limsup blockLogAvg₂`。target を bit 形 `c·log₂c ≤ -log₂Pₙ + o(n)` で建て、nat 量（`lz78PhraseStrings_mul_log_le`、`blockLogAvg_eq_neg_log_blockProb`）は `/Real.log 2` で機械整合。`c·log c ≤ -log Pₙ`（nat）を直接 def 化しない（W2 の Mathlib-shape は bit）。
3. **ripple ゼロ（機械確認）**: `ziv_aseventual_le_blockLogAvg₂` の direct consumer は 1 decl（`lz78GreedyImpl_achievability_ae`、同 file、statement 依存のみ）。W2 の body を埋めるだけで signature 不変 → 配線変更不要。`blockProb_neg_log_ge_sum`（D4）は 0 consumers（dead-start 裏取り）。
4. **route 確定 = length-grouping route A（leg 4 で route 取り違えを是正、inventory `lz78-m3-treenode-inventory.md` + proof-pivot-advisor、機械裏取り）**: leg 3 は Phase 2b を「可変深さ tree-node AEP = single in-session plan で閉じない genuine research-level 壁、攻略 = 旧 treenode T1-T5 路」と評価したが、これは **node/path-prefix route を probe した artifact**。
   - **route B（node-grouping = treenode T1-T5）は D3 trap で死ぬ**: overhead `c·log(#nodes) ≈ c·log c`、`lz78PhraseStrings_mul_log_le`（`c·log c ≤ K·n`、sorryAx-free）より `(c·log c)/n` は定数 = main term と同オーダーで vanish しない。数学的に細工不能。加えて treenode plan が「再利用、転記主体」と書く資産（`extendCylinder*`/`condNextSymbol_sum_eq_one`/`IsLZ78ZivCombinatorialCore`/`LZ78ZivCombinatorics.lean`/`LZ78ZivEntropyBridge.lean`）は commit `f67ec8a`/`602b1ad` で **削除済 (disk 不在、rg 確認)** = resurrection は ~750-1100 行のゼロ再構築。`condPhraseProb` も固定 tuple `v` でなく観測 `ω` で parametrize された path-prefix 比なので node-context sub-distribution を既存資産から抽出できない。
   - **唯一の genuine route = (A) length-grouping**（本 m2-plan の Approach Step A-D）。#groups = O(log n)、overhead `c·log log n` → vanish（D3 クリア）。最難サブピース（packing `card_short_le`/`total_length_ge_count_mul_log`、envelope `count_isBigO`）は既に sorryAx-free in-tree。**decisive gateway atom = 抽象 Jensen grouping** `c·log c ≤ ∑_ℓ c_ℓ·log c_ℓ + c·log(#groups)`（純 Finset/Real、`Real.convexOn_mul_log` + `ConvexOn.map_sum_le`）= treenode plan 判断 3 / feasibility リスク #1 そのもの。これは **leg 3 で一度も isolated に dispatch されていない**。`InformationTheory/Shannon/LZ78/ZivLengthGrouping.lean` に leg 4 で実装中、結果が出るまで W2 は `sorry` + `@residual(wall:lz78-aseventual-ziv)` 維持（discharge しない）。
   - **severity 再評価**: leg 3 の「research-level、数 leg」は earned verdict でなく route 取り違え由来 = **過大評価**。length-grouping を正しく取れば 1-2 leg 見込み。refutation の `c·log c ≤ K·n` 単一 bound 不十分は「単一 bound では届かない」を示すのみで length-grouping log-sum の不達を示さない。**壁 `wall:lz78-aseventual-ziv` 自体は honest に維持**（gateway atom 実装中、TRUE-as-framed、a.s.-eventual Ziv 内容は未証明）。treenode plan は parked/STALE 化（route B 死亡）。
   - **記録のみ（コード触らない）**: `isLZ78PerPathParsingFactorization_of_pos` が `ZivEntropyBridge.lean`/`Stationary/Kernel.lean` の docstring で「genuinely constructed」と記載されているが実在 decl が無い（inventory 発見、`rg` で phantom 確認）。コード docstring fact error、別途修正候補（SoT はコード側、今回は記録のみ）。
