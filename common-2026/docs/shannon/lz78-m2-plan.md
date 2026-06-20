# LZ78: M2 length-grouping Ziv 組合せ不等式 サブ計画

> **Parent**: [`lz78-completion-roadmap.md`](lz78-completion-roadmap.md) §1 M2 / M3
> （壁 `@residual(wall:lz78-aseventual-ziv)`、W2 = `ziv_aseventual_le_blockLogAvg₂`）

## 進捗

- [x] M0 在庫確認（leg 3 在庫 `lz78-m3-inventory.md` 流用 + 差分）✅
- [x] Phase 1 — gateway atom（Step A 符号長 bit-rate 展開）✅ **GO**（`lz78_impl_bitrate_le_clogc_plus_overhead`、`GreedyParsingImpl.lean:286`、sorryAx-free、commit `7171707`）→ 単位整合は壁でないと確定
- [ ] Phase 2 — length-grouping log-sum 核（genuine novel）🔄 **STALL at 2b**（可変深さ tree-node AEP、single in-session plan で閉じない genuine 壁 — 判断ログ #4）
- [ ] Phase 3 — overhead o(n) 制御 + limsup 合成 📋（Phase 2b 未着なので未到達）
- [ ] Phase 4 — W2 discharge（`ziv_aseventual_le_blockLogAvg₂` の sorry を埋める）📋（撤退ライン該当: `sorry` + `@residual(wall:lz78-aseventual-ziv)` 維持）

## ゴール

W1（`shannon_mcmillan_breiman₂`、SMB-in-bits 橋）は leg 3 で **閉鎖済**（`@audit:ok`、sorryAx-free、`GreedyParsingImpl.lean:520`）。本サブ計画のゴールは残る **W2 = `ziv_aseventual_le_blockLogAvg₂`**（`GreedyParsingImpl.lean:557`、`@residual(wall:lz78-aseventual-ziv)`、唯一の active sorry）を **genuine に discharge** すること。W2 が閉じれば `lz78GreedyImpl_achievability_ae` が sorryAx-free 化され（合成本体は既に sorry-free）、**achievability 完遂**（headline に残るは M4 converse 壁のみ）。

**leg 3 status（commit `7171707`）**: Phase 1 gateway = **GO**（`lz78_impl_bitrate_le_clogc_plus_overhead` sorryAx-free、単位整合は壁でない）。Phase 2 = **STALL at 2b**（`c·log c ≤ -log Pₙ + o(n)` 接続 = 可変深さ tree-node AEP、single in-session plan で閉じない genuine research-level 壁）→ W2 は `sorry` + `@residual` 維持（撤退ライン発動済、tier-2 honest、判断ログ #4）。M3 攻略は旧 `lz78-ziv-treenode-plan.md` T1-T5 路を resurrect する dedicated 複数 leg セッションへ。

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

### Phase 2 — length-grouping log-sum 核（🔄 STALL at 2b、leg 3）

**結果（leg 3、commit `7171707`）**: stall は 2a（length-grouped packing、既存 `total_length_ge_count_mul_log` あり）でも単位 plumbing でもなく、**2b の `c·log c ≤ -log Pₙ + o(n)` 接続そのもの**。これは **可変深さ tree-node AEP**（`c·log c ≤ ∑ⱼ -log qⱼ + o(n)`、D4 `∑qⱼ≈c` trap）を要し、codebase + Mathlib 不在。実装の決定的判定: 「Phase 2b の直接 `-log Pₙ` route は target としては real だが、`∑qⱼ` route と **同じ** genuine AEP で塞がれる。可変深さ tree-node AEP に shortcut は無い。**single in-session plan では閉じない genuine research-level scope**」。攻略 path = 旧 `lz78-ziv-treenode-plan.md` T1-T5（判断ログ #4）。**refutation（mandated）**: sorryAx-free 組合せ核 `c·log c ≤ 8·log(|α|+1)·n` は constant limsup `≤ 8·log(|α|+1)/log 2` しか出さず、低エントロピー源で `entropyRate₂` を超過 = genuine に不十分（壁確定、plumbing でない）。

**proof-log: yes**（最大の難所、攻略記録必須）。

これが **genuine missing piece**（Mathlib にも codebase にもない核）。`c·log c` を `-log Pₙ` に繋ぐ length-grouping 不等式。**更に小分けに**:

- **2a. length-distribution の log-sum 下界**（novel、~60–120 行）。phrase strings を長さ別に分類し、`∑ phrases -log(per-phrase prob) ≥ c·log c - c·H(length-dist)` 型の組合せ不等式。供給テンプレート = `total_length_ge_count_mul_log`（`ZivCountingBody.lean:190` verbatim、`c·log c ≤ 8·log(|α|+1)·T`）の packing 論法（同じ長さの distinct phrase は高々 `|α|^ℓ` 個 → 長さ別 entropy bound）。`lz78PhraseStrings_nodup`（`GreedyLongestPrefix.lean:123`）が distinctness 前提を供給。
- **2b. per-path log-sum を `-log Pₙ` に接続**（novel + 既存橋、~40–80 行）。**D4 trap 回避が crux**: `∑ⱼ -log qⱼ`（path-prefix、`∑qⱼ≈c` trap）を経由せず、length-grouped log-sum を **直接** `-log Pₙ = n·blockLogAvg`（`blockLogAvg_eq_neg_log_blockProb`、`ZivEntropyBridge.lean:126` verbatim、`0 < n` + `0 < Pₙ` 前提）に乗せる。`0 < Pₙ` は a.s. regularity（observed cylinder 正質量）→ `∀ᵐ ω` の中で供給。
- **novel か**: **はい、2a/2b 双方が核**。2a は length-grouped packing の組合せ核（`total_length_ge_count_mul_log` の packing を長さ別 entropy 形に拡張）、2b は length-sum を source 確率に乗せる接続。Mathlib に LZ78/Ziv 不等式は無い（loogle 0、在庫裏取り済）。

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

## gateway atom 結果（leg 3、済）

**Phase 1 = `lz78_impl_bitrate_le_clogc_plus_overhead`（Step A 符号長 bit-rate 展開）= GO**（gateway-atom-first、commit `7171707`、sorryAx-free）。

- gateway 通過 → nat↔bit 単位整合（`Nat.log 2` ↔ `Real.log/log 2`、`+1` ずれ、`c=0` 退化）に想定外コスト無し = **単位整合は壁でない**と確定。
- **しかし真の壁は単位整合の下流（Phase 2b）にあった**: gateway 通過後 Phase 2 に進むと、`c·log c ≤ -log Pₙ + o(n)` 接続（2b）が可変深さ tree-node AEP を要する genuine 壁で STALL（gateway-atom-first が「単位は OK だが combinatorial→conditional 橋が genuine 壁」を pinpoint した = atom-first の機能どおり）。Phase 1 の go/no-go gate は「単位整合の go」を意味し、「M2 全体 tractable」までは含意しなかった（leg 3 で combinatorial 核が真の壁と判明）。

## 撤退ライン（leg 3 で該当・発動済）

- **発動済（leg 3）**: Phase 2b（`c·log c ≤ -log Pₙ + o(n)` 接続 = 可変深さ tree-node AEP）が **single in-session plan で閉じない genuine 壁** と判明 → **`ziv_aseventual_le_blockLogAvg₂` を `sorry` のまま据え置き、`@residual(wall:lz78-aseventual-ziv)` 維持**（達成済、tier-2 honest）。gateway（Phase 1）は GO だったので「gateway 不通」撤退条件には該当せず、撤退は **Phase 2b genuine 壁** 条件で発動。
- **gateway（Phase 1）が ~1 セッション以内に通らない** → 単位整合に想定外コストのシグナル（leg 3 で **不該当**、gateway は GO）。
- **Phase 2（length-grouping log-sum 核 2a/2b）が通らない** → genuine 組合せ核が想定より重い（leg 3 で **2b が該当**）。同様に **`ziv_aseventual_le_blockLogAvg₂` を `sorry` + `@residual(wall:lz78-aseventual-ziv)` 維持**。
- 退出口は **sorry + `@residual` のみ**。hypothesis bundling（`*Hypothesis` / `*Reduction` predicate に core を抱えさせる）は **禁止**（CLAUDE.md「検証の誠実性」）。W2 の signature（`(μ, p)` + `[IsProbabilityMeasure μ]` regularity のみ）を変えない。Phase 2/3 で建てた個別 atom が sorry を持つなら、それぞれ `@residual(wall:lz78-aseventual-ziv)`（同壁）または新規 plan-slug を付与。
- **次の攻略**: 旧 `lz78-ziv-treenode-plan.md` T1-T5 路を resurrect する dedicated 複数 leg セッション（M3、判断ログ #4）。本サブ計画（M2）の単位整合 gateway は閉じた。

## 規模・リスク総括

- **総計**: ~210–440 行（Phase 1: 30–60 / Phase 2: 120–250 / Phase 3: 50–100 / Phase 4: 10–30）。在庫 `lz78-m3-inventory.md` 自前要素 2（a.s.-eventual Ziv 比較、~150–400 行 medium）に整合。
- **支配項・最大リスク**: Phase 2（length-grouping log-sum 核、genuine novel、medium–high）。Phase 1/3/4 は plumbing〜既存資産流用（低〜medium）。
- **genuine novel 核の所在**: Phase 2a（length-grouped packing 組合せ核、`total_length_ge_count_mul_log` の packing を長さ別 entropy 形に拡張）+ Phase 2b（length-sum → `-log Pₙ` 直結、D4 trap 回避）。これ以外（Step A 展開・overhead vanish・limsup 合成）は既存資産。

## 判断ログ

1. **W1 は閉鎖済として扱う（在庫の W1 自前 closure 想定は obsolete）**: 在庫 `lz78-m3-inventory.md` は W1（SMB-in-bits 橋）を「自前 closure 対象（~30–60 行）」と書くが、leg 3 で `shannon_mcmillan_breiman₂`（`GreedyParsingImpl.lean:520`、`@audit:ok`、sorryAx-free）として **既に閉じた**。本サブ計画の対象は W2 のみ。
2. **bit 単位で建てる（verbatim 確認の帰結）**: SMB-in-bits が既に `blockLogAvg₂`（bit）で握り、W2 RHS も `limsup blockLogAvg₂`。target を bit 形 `c·log₂c ≤ -log₂Pₙ + o(n)` で建て、nat 量（`lz78PhraseStrings_mul_log_le`、`blockLogAvg_eq_neg_log_blockProb`）は `/Real.log 2` で機械整合。`c·log c ≤ -log Pₙ`（nat）を直接 def 化しない（W2 の Mathlib-shape は bit）。
3. **ripple ゼロ（機械確認）**: `ziv_aseventual_le_blockLogAvg₂` の direct consumer は 1 decl（`lz78GreedyImpl_achievability_ae`、同 file、statement 依存のみ）。W2 の body を埋めるだけで signature 不変 → 配線変更不要。`blockProb_neg_log_ge_sum`（D4）は 0 consumers（dead-start 裏取り）。
4. **leg 3 stall pinpoint（gateway-atom-first、commit `7171707`、machine-verified）**: Phase 1 gateway = GO（`lz78_impl_bitrate_le_clogc_plus_overhead` sorryAx-free、単位整合は壁でないと確定）。stall は Phase 1（単位 plumbing）でも 2a（length-grouped packing、既存 `total_length_ge_count_mul_log`）でもなく、**Phase 2b の `c·log c ≤ -log Pₙ + o(n)` 接続そのもの = 可変深さ tree-node AEP**（`c·log c ≤ ∑ⱼ -log qⱼ + o(n)`、D4 `∑qⱼ≈c` trap）。直接 `-log Pₙ` route も `∑qⱼ` route と同じ genuine AEP で塞がれ、shortcut 無し → **single in-session plan で閉じない genuine research-level 壁**。撤退ライン Phase 2b 条件で発動、`@residual(wall:lz78-aseventual-ziv)` 維持（達成済）。**攻略 path**: 旧 `lz78-ziv-treenode-plan.md` T1-T5（tree-node sub-distribution → per-node 条件付き積 → `c log c ≤ ∑ -log q` log-sum → telescoping → `-log Pₙ` 接続）が obsolete でなく genuine な攻略 path（末尾の `-log Pₙ` 接続のみ r2 realign 後の SMB 接続形）。refutation（mandated）: `c·log c ≤ K·n` 単一組合せ核は constant limsup `≤ 8·log(|α|+1)/log 2` しか出さず低エントロピー源で `entropyRate₂` 超過 = 不十分（壁確定、plumbing でない）。`wall:lz78-aseventual-ziv` は不変（over-estimate でなく under-estimate 側 = roadmap r2 の「plumbing 級」誤認を是正、cause:false-statement 系の framing 訂正）。
