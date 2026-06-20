# LZ78: M2 length-grouping Ziv 組合せ不等式 サブ計画

> **Parent**: [`lz78-completion-roadmap.md`](lz78-completion-roadmap.md) §1 M2 / M3
> （壁 `@residual(wall:lz78-aseventual-ziv)`、W2 = `ziv_aseventual_le_blockLogAvg₂`）

## 進捗

- [x] M0 在庫確認（leg 3 `lz78-m3-inventory.md` + leg 4 `lz78-m3-treenode-inventory.md` の route A/B 比較）✅
- [x] Phase 1 — gateway atom（Step A 符号長 bit-rate 展開）✅ **GO**（`lz78_impl_bitrate_le_clogc_plus_overhead`、`GreedyParsingImpl.lean:286`、sorryAx-free、commit `7171707`）→ 単位整合は壁でないと確定
- [x] Phase 2a — convexity grouping（length 別 Jensen）✅ **sorryAx-free**（`ZivLengthGrouping.lean`、commit `c472518`）— necessary scaffolding だが単独では不十分
- [x] Phase 2b — marginal sub-distribution + log-sum 橋 ✅ **sorryAx-free**（`ZivMeasureBridge.lean`、commit `d1d55db`）— **marginal なので方向不一致、`-log Pₙ` に届かない**（判断ログ #4）
- [ ] Phase 2c — **genuine wall**: conditional-context (length, finite-context) AEP 🔄 **research-level**（marginal/node-position いずれも machine-ruled-out、判断ログ #4）→ 達成まで `sorry` + `@residual(wall:lz78-aseventual-ziv)` 維持
- [ ] Phase 3 — overhead o(n) 制御 + limsup 合成 📋（Phase 2c 通過後に着手）
- [ ] Phase 4 — W2 discharge（`ziv_aseventual_le_blockLogAvg₂` の sorry を埋める）📋（達成まで `sorry` + `@residual(wall:lz78-aseventual-ziv)` 維持）

## ゴール

W1（`shannon_mcmillan_breiman₂`、SMB-in-bits 橋）は leg 3 で **閉鎖済**（`@audit:ok`、sorryAx-free、`GreedyParsingImpl.lean:520`）。本サブ計画のゴールは残る **W2 = `ziv_aseventual_le_blockLogAvg₂`**（`GreedyParsingImpl.lean:557`、`@residual(wall:lz78-aseventual-ziv)`、唯一の active sorry）を **genuine に discharge** すること。W2 が閉じれば `lz78GreedyImpl_achievability_ae` が sorryAx-free 化され（合成本体は既に sorry-free）、**achievability 完遂**（headline に残るは M4 converse 壁のみ）。

**status（leg 4 後半、gateway-atom-first probe による壁の精密 characterization 後）**: Phase 1 gateway = GO（単位整合は壁でない）。Phase 2a convexity grouping + Phase 2b marginal sub-distribution 橋 = **両方 sorryAx-free で建った**（necessary scaffolding）が、**leg 4 前半の「length-grouping route A は 1-2 leg で閉じる、rest plumbing」という楽観は撤回する**。leg 4 後半の gateway-atom-first probe で、壁 `ziv_aseventual_le_blockLogAvg₂` は **genuine research-level** と精密に機械裏取りされた。**2 つの単純 grouping が両方 machine-ruled-out**:

- **(1) node-position-grouping（treenode T1-T5 literal）は D3 trap で死ぬ**: convexity overhead `c·log(#nodes)`、LZ tree で #nodes≈c なので `c·log(#nodes) ≈ c·log c` = main term と同オーダー、`lz78PhraseStrings_mul_log_le`（`c·log c ≤ K·n`、sorryAx-free）より `(c·log c)/n` は定数で vanish しない（D3 trap）。
- **(2) marginal-length-grouping（leg 4 前半に sorryAx-free で建てた marginal route）は overhead が vanish するが方向が逆**: chain rule で `-log Pₙ = ∑_j -log q_cond(j)`（conditional）、memory 源では `q_cond ≥ P_marginal` ゆえ `∑ -log P_marginal ≥ -log Pₙ` = 欲しい `≤` と逆向き（iid で等号、memory で逆、Dirac で両 0 alive）。FKG/positive-association の Mathlib 補題は loogle **0-hit**。**marginal では `-log Pₙ` を上から押さえられない**。
- **genuine core = conditional-context AEP**（唯一 `c·log c ≤ -log Pₙ + o(n)` を満たす構造）: **(length, finite-context)-grouping + conditional q(symbol|context) + AEP**。3 条件を同時に満たす必要 — (a) **conditional** で chain rule 経由 `-log Pₙ` に到達（marginal 不可）、(b) **per-context sub-distribution `∑_a q(context·a|context) ≤ 1`** で log-sum 適用可（path-prefix `condPhraseProb` は `∑qⱼ≈c` の D4 trap で不可）、(c) **finite-context で #contexts 有界** にして convexity overhead を vanish（naive node-grouping は #nodes≈c で D3 trap）。context 深さ→∞ の近似誤差を **AEP** で制御。= handoff 原典の「variable-depth tree-node AEP」framing は **正しかった**（leg 4 前半が一時 plumbing と誤読したのを再是正）。research-level・数 leg。
- **壁は維持**: 結果が出るまで W2 = `sorry` + `@residual(wall:lz78-aseventual-ziv)` を honest に維持（discharge しない）。撤退ラインは「conditional-context AEP が通らなければ tier-2 維持」。

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

### genuine core 戦略の骨子（両単純 grouping は machine-ruled-out → conditional-context AEP）

genuine missing piece = `c·log c`（組合せ phrase count）を `-log Pₙ`（source 確率）に繋ぐ不等式 + overhead 制御。**leg 4 後半で 2 つの単純 grouping が両方死ぬことが機械裏取りされた**ので、骨子は conditional-context AEP に絞られる:

1. **Step A（gateway、closed）**: 符号長 bit-rate を `c·log₂c/n` 型に展開（`lz78_impl_bitrate_le_clogc_plus_overhead`、sorryAx-free）。
2. **Step B-naive（両 ruled-out）**: 単純な length-grouping で `c·log₂c ≤ -log₂Pₙ + overhead` を直接建てる路は **両方死ぬ** — (i) **node-position-grouping**（overhead `c·log(#nodes)≈c·log c`、D3 で非 vanish）、(ii) **marginal-length-grouping**（overhead は vanish するが marginal sub-distribution `∑_a P(a)≤1` 経由で出る log-sum は `∑ -log P_marginal ≥ -log Pₙ` = **方向が逆**、memory 源で `-log Pₙ` を上から押さえられない）。
3. **Step B-genuine（research-level）**: 唯一生き残る構造 = **conditional-context AEP**。phrase を **(length, finite-context)** で grouping し、**conditional** q(symbol|context) で chain rule 経由 `-log Pₙ` に到達。per-context sub-distribution `∑_a q(context·a|context) ≤ 1` で log-sum を適用（marginal でも path-prefix `∑qⱼ` でもない第三の量）、finite-context で #contexts 有界にして convexity overhead を vanish、context 深さ→∞ の近似誤差は **AEP** で制御。= variable-depth tree-node AEP framing。
4. **Step C（overhead o(n)）**: finite-context truncation の overhead を `(c·log log n)/n → 0` で吸収（`c = O(n/log n)` envelope `lz78PhraseStrings_count_isBigO`、`ZivCountingBody.lean:410`）。
5. **Step D（合成）**: per-n 比較不等式を `Filter.limsup_le_limsup` に乗せる。cobounded/bounded auto 引数は `lz78_impl_rate_le_const`（上界）+ `per_symbol_nonneg`（下界）で供給（headline `h_bdd_above` 既実証手法）。

**marginal route（leg 4 前半 sorryAx-free 成果、necessary scaffolding）は方向不一致で `-log Pₙ` に届かない**。**D4 path-prefix route（`condPhraseProb` / `blockProb_neg_log_ge_sum`、0 consumers）も `∑qⱼ≈c` trap で素通り**。genuine core が要求する第三の量 = **node-context (conditional) sub-distribution** `∑_a q(node·a|node) ≤ 1`（marginal でも path-prefix でもない）= codebase + Mathlib 不在の missing measure-theoretic 核。leg 4 の `ZivMeasureBridge.lean` の sub-distribution 機構（`sum_marginal_real_le_one` の disjoint-cylinder 論法）を conditional cylinder 比へ拡張するのが入口。

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

### Phase 2 — genuine core（2a/2b sorryAx-free 済、2c = genuine wall）

leg 4 で 3 サブ Phase に分割。**2a/2b は sorryAx-free で建った（necessary scaffolding）が、2b が marginal で方向不一致 → genuine core は 2c = conditional-context AEP（research-level）**。

#### Phase 2a — convexity grouping（length 別 Jensen）✅ sorryAx-free（commit `c472518`）

抽象 Jensen grouping `c·log c ≤ ∑_ℓ c_ℓ·log c_ℓ + c·log(#groups)`（純 Finset/Real、`Real.convexOn_mul_log` + `ConvexOn.map_sum_le`）+ LZ 長さ別特化。**deliverable**: `card_mul_log_le_sum_group_mul_log_add_card_log`（`ZivLengthGrouping.lean:49`）+ `lz78PhraseStrings_card_mul_log_le_sum_length_group`（`:143`）、両 sorryAx-free。**判定**: convexity grouping それ自体は壁でない（D3 を回避する length-fiber 化は機械的に成立）。だが単独では `-log Pₙ` に届かない（per-group log-sum を source 確率に乗せる橋が別途必要）。

#### Phase 2b — marginal sub-distribution + log-sum 橋 ✅ sorryAx-free（commit `d1d55db`）— **方向不一致**

per-length **marginal** sub-distribution `∑_a P(a) ≤ 1` + per-group log-sum + 集約。**deliverable**: `sum_marginal_real_le_one`（`ZivMeasureBridge.lean:76`）+ `group_card_mul_log_le_sum_neg_log`（`:103`）+ `lz78PhraseStrings_mul_log_le_sum_neg_log_marginal_add_overhead`（`:184`、`c·log c ≤ ∑_phrases -log P_marginal + c·log D`）、全 sorryAx-free。**判定（machine-ruled-out）**: marginal 版は overhead が vanish するが、chain rule `-log Pₙ = ∑_j -log q_cond(j)` に対し memory 源では `q_cond ≥ P_marginal` ゆえ `∑ -log P_marginal ≥ -log Pₙ` = **欲しい `≤` と逆向き**（iid で等号、memory で逆、Dirac で両 0 alive）。FKG/positive-association の Mathlib 補題は loogle **0-hit**。**marginal では `-log Pₙ` を上から押さえられない** → 単独では genuine core を閉じない。ただし sub-distribution + log-sum の機構（disjoint-cylinder 論法）は conditional 版へ転用可能（necessary scaffolding）。

#### Phase 2c — genuine wall: conditional-context (length, finite-context) AEP 🔄 research-level

**proof-log: yes**（次 genuine atom の go/no-go 記録必須）。**これが genuine missing measure-theoretic 核**（codebase + Mathlib 不在）。両単純 grouping（node-position D3 / marginal 方向）が machine-ruled-out された後、唯一生き残る構造:

- **次の genuine atom = node-context (conditional) sub-distribution `∑_a q(node·a|node) ≤ 1`** — path-prefix `condPhraseProb`（D4 trap、0 consumers、`∑≈c`）でも marginal（方向逆）でもない **第三の量**。leg 4 の `ZivMeasureBridge.lean` の sub-distribution 機構（`sum_marginal_real_le_one` の disjoint-cylinder 論法）を **conditional cylinder 比** へ拡張する路。
- **正しい assembly = (length, finite-context)-grouping + conditional q(symbol|context) + AEP**。(a) conditional で chain rule 経由 `-log Pₙ` に到達、(b) per-context sub-distribution で log-sum 適用可、(c) finite-context で #contexts 有界 → convexity overhead vanish。context 深さ→∞ の近似誤差を AEP で制御。
- **handoff 原典の「variable-depth tree-node AEP」framing は正しかった**（leg 4 前半が一時 plumbing と誤読したのを再是正）。research-level・数 leg の genuine 壁。

**地雷チェック**: per-block `∀n∀ω` 形にしない（D1/D2 FALSE、反例 `a^16`）。conditional-context bound は **per-n 不等式 + overhead 項込み + AEP**で、limsup 形で o(n) を吸収して初めて成立。clean `c·log c ≤ -log Pₙ`（D1）や overhead 付き ∀n∀ω（D2）を書いた瞬間に即撤退。

### Phase 3 — overhead o(n) 制御 + limsup 合成（~50–100 行、medium、Phase 2c 通過後）

**proof-log: no**（plumbing 級だが o(n) 評価のみ注記）。

- **3a. overhead → 0**（~30–60 行）。finite-context truncation の overhead `(c·log log n)/n` を `c = O(n/log n)`（`lz78PhraseStrings_count_isBigO`、`ZivCountingBody.lean:410` verbatim、envelope `n/Real.log n`）と合成 → `O((log log n)/log n) → 0`。`blockRV n ω` を `input n` として食わせる際は `count_isBigO`（`hlen : (input n).length = n`）形に。
- **3b. limsup 合成**（~20–40 行）。Phase 1（Step A）+ Phase 2c（conditional-context AEP で `c·log₂c ≤ -log₂Pₙ + overhead`）+ Phase 3a（overhead→0）を `∀ᶠ n` の per-n 比較 `lz/n ≤ blockLogAvg₂ + err(n)`、`err→0` にまとめ、`Filter.limsup_le_limsup`（`LiminfLimsup.lean:198` verbatim、cobounded/bounded auto 引数）+ `Tendsto.add` 系で `limsup(lz/n) ≤ limsup blockLogAvg₂`。cobounded/bounded witness = `lz78_impl_rate_le_const`（上界）+ `per_symbol_nonneg`（下界）、`Filter.isBoundedUnder_of`（headline `h_bdd_above` 実証手法）。

### Phase 4 — W2 discharge（~10–30 行、低リスク・配線のみ）

**proof-log: no**。

`ziv_aseventual_le_blockLogAvg₂`（`GreedyParsingImpl.lean:557`）の `sorry` を Phase 1–3（Phase 2c = conditional-context AEP 通過後）の合成で埋める。`∀ᵐ ω` の中で `0 < Pₙ`（a.s. regularity）+ `0 < n` を供給し、per-n 比較 → `limsup_le_limsup`。**signature は変えない**（statement は既に正しい Mathlib-shape）。完了後:

- consumer `lz78GreedyImpl_achievability_ae`（合成本体 sorry-free）が **sorryAx-free 化** → `#print axioms ziv_aseventual_le_blockLogAvg₂` / `lz78GreedyImpl_achievability_ae` = `[propext, Classical.choice, Quot.sound]` を機械確認（DoD proof done）。
- docstring の `@residual(wall:lz78-aseventual-ziv)` を除去し `@audit:ok` 化（**独立 honesty audit を要請** — 新 sorry 消滅 + signature honest 確認）。
- 親 roadmap §0/§1 の M3 行・achievability 状態を **child=SoT で同期更新**（W2 closed、headline 残壁 = M4 のみ）、`audit-tags.md` register の `lz78-aseventual-ziv` 行を CLOSED 注記。

## 地雷の不変条件（再探索禁止、各 atom が抵触しないこと）

- **D1**: per-block `c·log c ≤ -log Pₙ`（∀n∀ω, clean）は **FALSE**（反例 `a^16`, c=5, -log Pₙ=0）。→ Phase 2c は **a.s.-eventual + overhead 項込みの per-n 形 + AEP**、限界は limsup でのみ取る。
- **D2**: overhead 版 `c·log c ≤ -log Pₙ + c·log(|α|+1)`（∀n∀ω）も **FALSE**（`Pₙ→1` family）。→ overhead は finite-context truncation の vanish する項であって定数 `c·log(|α|+1)` ではない。
- **D3（machine-ruled-out、leg 4 後半）**: node-position-grouping overhead `(c·log #nodes)/n`（#nodes≈c）は **定数収束（vanish しない）** = treenode T1-T5 literal が死ぬ。→ finite-context で #contexts を有界にして overhead vanish。`log #nodes=log c` を `log log n` と取り違えない。
- **D4**: path-prefix `Q_c = ∏ condPhraseProb` の AEP（`blockProb_neg_log_ge_sum` / `condPhraseProb`、`ZivEntropyBridge.lean`）は **0 direct consumers**（機械裏取り、dead-start、`∑ⱼqⱼ≈c` trap）。→ Phase 2c は **path-prefix を素通り**（必要なのは node-context conditional sub-distribution `∑_a q(node·a|node)≤1` という第三の量）。
- **D8（machine-ruled-out、leg 4 後半）**: marginal-length-grouping は overhead vanish だが **方向不一致** — memory 源で `∑ -log P_marginal ≥ -log Pₙ`（chain rule `-log Pₙ = ∑_j -log q_cond(j)` + `q_cond ≥ P_marginal`）= 欲しい `≤` と逆。FKG/positive-association loogle 0-hit。→ Phase 2c は **conditional** q(symbol|context) を使う（marginal 不可）。

各 Phase の抵触チェック: Phase 1（決定論的代数展開、D1–D8 無関係）/ Phase 2a（convexity grouping、D3 を length-fiber で回避）/ Phase 2b（marginal sub-dist、D8 に該当して方向不一致＝単独で genuine core を閉じない）/ Phase 2c（conditional-context AEP、D1/D2 を AEP で / D3 を finite-context で / D4・D8 を conditional sub-dist で全て回避）/ Phase 3（overhead vanish = D2/D3 準拠）/ Phase 4（limsup 合成、per-block 形を作らない = D1 準拠）。

## gateway atom 結果

**Phase 1（単位整合 gateway）= `lz78_impl_bitrate_le_clogc_plus_overhead` = GO**（commit `7171707`、sorryAx-free）。nat↔bit 単位整合は壁でないと確定（plumbing 級）。

**Phase 2a/2b（convexity grouping + marginal sub-dist 橋）= 両 sorryAx-free だが genuine core を閉じない**（commit `c472518`/`d1d55db`、necessary scaffolding）。

**Phase 2c の gateway atom = node-context (conditional) sub-distribution `∑_a q(node·a|node) ≤ 1`**（leg 5 以降）。

- leg 4 後半の gateway-atom-first probe で、**2 つの単純 grouping が両方 machine-ruled-out** されたのが決定的成果: (1) node-position-grouping = D3 trap（#nodes≈c で overhead 非 vanish）、(2) marginal-length-grouping = D8 方向不一致（`∑ -log P_marginal ≥ -log Pₙ`、memory で逆向き、FKG 補題 loogle 0-hit）。
- 残る genuine core = conditional-context AEP（marginal/path-prefix いずれでもない第三の量 `∑_a q(node·a|node) ≤ 1` を中心に、(length, finite-context)-grouping + AEP）。これが genuine missing measure-theoretic 核（codebase + Mathlib 不在）。**research-level・数 leg**（leg 4 前半の「1-2 leg で閉じる」楽観は撤回）。

## 撤退ライン

- **Phase 2c（conditional-context AEP）が通らない** → genuine core が想定通り research-level → **`ziv_aseventual_le_blockLogAvg₂` を `sorry` + `@residual(wall:lz78-aseventual-ziv)` 維持**（tier-2 honest）。結果が出るまで W2 は discharge しない。
- **node-context conditional sub-distribution atom が通らない** → genuine missing 核が想定より重い。同様に W2 = `sorry` + `@residual` 維持。
- 退出口は **sorry + `@residual` のみ**。hypothesis bundling（`*Hypothesis` / `*Reduction` predicate に core を抱えさせる）は **禁止**（CLAUDE.md「検証の誠実性」）。W2 の signature（`(μ, p)` + `[IsProbabilityMeasure μ]` regularity のみ）を変えない。Phase 2c/3 で建てた個別 atom が sorry を持つなら、それぞれ `@residual(wall:lz78-aseventual-ziv)`（同壁）または新規 plan-slug を付与。
- **route 履歴**: 旧 `lz78-ziv-treenode-plan.md`（node-position-grouping = route B）は D3 trap で reject 済（部分 un-park: conditional sub-distribution = 旧 T2 は genuine に必要な核と leg 4 で確認、判断ログ #4）。

## 規模・リスク総括

- **総計**: ~300–600 行（Phase 2c conditional-context AEP が支配 / Phase 3 + Phase 4 配線）。Phase 1/2a/2b は sorryAx-free 済（足場、~250 行 committed）。
- **支配項・最大リスク**: Phase 2c（conditional-context (length, finite-context) AEP、genuine missing measure-theoretic 核、research-level）。両単純 grouping が machine-ruled-out された後の唯一の生存構造。Phase 1/3/4 は plumbing〜既存資産流用（低〜medium）。
- **genuine missing 核の所在**: Phase 2c = node-context (conditional) sub-distribution `∑_a q(node·a|node) ≤ 1`（marginal/path-prefix いずれでもない第三の量）+ finite-context truncation + AEP。これ以外（Step A 展開・convexity grouping 2a・marginal 橋 2b・overhead vanish・limsup 合成）は既存資産 / sorryAx-free 済。

## 判断ログ

1. **W1 は閉鎖済として扱う（在庫の W1 自前 closure 想定は obsolete）**: 在庫 `lz78-m3-inventory.md` は W1（SMB-in-bits 橋）を「自前 closure 対象（~30–60 行）」と書くが、leg 3 で `shannon_mcmillan_breiman₂`（`GreedyParsingImpl.lean:520`、`@audit:ok`、sorryAx-free）として **既に閉じた**。本サブ計画の対象は W2 のみ。
2. **bit 単位で建てる（verbatim 確認の帰結）**: SMB-in-bits が既に `blockLogAvg₂`（bit）で握り、W2 RHS も `limsup blockLogAvg₂`。target を bit 形 `c·log₂c ≤ -log₂Pₙ + o(n)` で建て、nat 量（`lz78PhraseStrings_mul_log_le`、`blockLogAvg_eq_neg_log_blockProb`）は `/Real.log 2` で機械整合。`c·log c ≤ -log Pₙ`（nat）を直接 def 化しない（W2 の Mathlib-shape は bit）。
3. **ripple ゼロ（機械確認）**: `ziv_aseventual_le_blockLogAvg₂` の direct consumer は 1 decl（`lz78GreedyImpl_achievability_ae`、同 file、statement 依存のみ）。W2 の body を埋めるだけで signature 不変 → 配線変更不要。`blockProb_neg_log_ge_sum`（D4）は 0 consumers（dead-start 裏取り）。
4. **壁の精密 characterization = conditional-context AEP（leg 4 後半 gateway-atom-first probe、機械裏取り、本 leg 2 度目の修正）**: leg 4 前半の「length-grouping route A は 1-2 leg で閉じる、rest plumbing」という楽観は **撤回**。leg 4 後半の probe で壁 `ziv_aseventual_le_blockLogAvg₂` は **genuine research-level** と精密に裏取り。**2 つの単純 grouping が両方 machine-ruled-out**:
   - **(1) node-position-grouping（treenode T1-T5 literal）= D3 trap**: convexity overhead `c·log(#nodes)`、LZ tree で #nodes≈c なので `c·log(#nodes) ≈ c·log c` = main term と同オーダー、`lz78PhraseStrings_mul_log_le`（`c·log c ≤ K·n`、sorryAx-free）より `(c·log c)/n` は定数で vanish しない。
   - **(2) marginal-length-grouping（leg 4 前半 sorryAx-free 成果）= 方向不一致**: overhead は vanish するが、chain rule `-log Pₙ = ∑_j -log q_cond(j)`（conditional）に対し memory 源では `q_cond ≥ P_marginal` ゆえ `∑ -log P_marginal ≥ -log Pₙ` = 欲しい `≤` と逆（iid で等号、memory で逆、Dirac で両 0 alive）。FKG/positive-association の Mathlib 補題は loogle **0-hit**。marginal では `-log Pₙ` を上から押さえられない。
   - **leg 4 の genuine sorryAx-free 成果（necessary scaffolding、単独で不十分）**: `ZivLengthGrouping.lean`（commit `c472518`、抽象 Jensen grouping + LZ 長さ別、両 sorryAx-free）+ `ZivMeasureBridge.lean`（commit `d1d55db`、per-length marginal sub-distribution `sum_marginal_real_le_one` + per-group log-sum + 集約、sorryAx-free）。marginal 版なので方向不一致で `-log Pₙ` に届かないが、sub-distribution + log-sum 機構（disjoint-cylinder 論法）は conditional 版に転用可能。
   - **genuine core = conditional-context AEP**: 唯一 `c·log c ≤ -log Pₙ + o(n)` を満たす構造 = **(length, finite-context)-grouping + conditional q(symbol|context) + AEP**。3 条件同時 — (a) conditional で chain rule 経由 `-log Pₙ` 到達（marginal 不可）、(b) per-context sub-distribution `∑_a q(context·a|context) ≤ 1` で log-sum 適用可（path-prefix `condPhraseProb` は `∑qⱼ≈c` の D4 trap で不可）、(c) finite-context で #contexts 有界 → convexity overhead vanish（naive node-grouping は #nodes≈c で D3 trap）。context 深さ→∞ の近似誤差を AEP で制御。= handoff 原典の「variable-depth tree-node AEP」framing は **正しかった**（leg 4 前半が一時 plumbing と誤読したのを再是正）。
   - **次の genuine atom（leg 5 以降）= node-context (conditional) sub-distribution `∑_a q(node·a|node) ≤ 1`** — path-prefix `condPhraseProb`（D4 trap、0 consumers、`∑≈c`）でも marginal（方向逆）でもない第三の量 = genuine missing measure-theoretic 核（codebase + Mathlib 不在）。leg 4 の `ZivMeasureBridge.lean` sub-distribution 機構を conditional cylinder 比へ拡張 → finite-context truncation + AEP で convexity overhead vanish（research-level）。
   - **壁 `wall:lz78-aseventual-ziv` 自体は honest に維持**（TRUE-as-framed、conditional-context AEP 未証明）。treenode plan は **部分 un-park**（conditional sub-distribution = 旧 T2 は genuine 核、node-position-grouping = 旧 T3 assembly は D3 で dead）。
   - **記録のみ（コード触らない）**: `isLZ78PerPathParsingFactorization_of_pos` が `ZivEntropyBridge.lean`/`Stationary/Kernel.lean` の docstring で「genuinely constructed」と記載されているが実在 decl が無い（phantom 確認）。コード docstring fact error、別途修正候補（SoT はコード側、今回は記録のみ）。

## settled facts（machine-backed、confidence: machine）

leg 4 後半に機械裏取りされた壁の characterization。re-verification は `#print axioms` / loogle に任せ（prose cache しない）、ここは expensive-to-rederive な機械裏取り判定のみ簡潔に記録。

| claim | confidence | re-verification | notes |
|---|---|---|---|
| node-position-grouping = D3 trap（overhead `c·log #nodes ≈ c·log c` 非 vanish） | machine | `#print axioms lz78PhraseStrings_mul_log_le`（`c·log c ≤ K·n`、sorryAx-free） | #nodes≈c が D3 を実際に殺す |
| marginal-length-grouping = 方向不一致（`∑ -log P_marginal ≥ -log Pₙ`） | machine | FKG/positive-association loogle 0-hit + chain rule `q_cond ≥ P_marginal` | iid で等号、memory で逆、Dirac で両 0 alive |
| `ZivLengthGrouping.lean` + `ZivMeasureBridge.lean` 両 sorryAx-free | machine | `#print axioms` on `lz78PhraseStrings_card_mul_log_le_sum_length_group` / `lz78PhraseStrings_mul_log_le_sum_neg_log_marginal_add_overhead` | necessary scaffolding、commit `c472518`/`d1d55db` |
