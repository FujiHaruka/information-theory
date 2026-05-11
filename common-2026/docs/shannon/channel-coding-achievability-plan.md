# Channel coding achievability ムーンショット計画 (B-3) 🌙

> 起草 2026-05-12 / B-7 完了直後。Cover-Thomas Ch 7.7 (random coding argument) を AEP plumbing + B-7 i.i.d. corollary `mutualInfo_iid_eq_nsmul` を入口に Lean 化。**最難関シード** (見積 800-1500 行 / 4-6 週)。
>
> **2026-05-12 状態**: Phase A + Phase B-(a,b) 完了。Phase B-(c) (independent pair bound) 以降は deferred (新規 AEP point-wise upper bound + i.i.d. product measure plumbing が ~200-400 行追加で必要、後段 Phase C/D と合わせて 1000-1600 行を要する見積もり)。

## 進捗

- [x] Phase 0 — Inventory (Mathlib + 既存 Common2026 探索) ✅ → [channel-coding-achievability-inventory.md](channel-coding-achievability-inventory.md)
- [x] Phase A — Channel + Code 定義 ✅ (`Common2026/Shannon/ChannelCoding.lean`, 行 1-225, 約 200 行)
- [ ] Phase B — Jointly typical set + 3 joint AEP bounds 🚧 (a, b 完了 / c deferred)
  - [x] (a) `jointlyTypicalSet_prob_tendsto_one` ✅
  - [x] (b) `jointlyTypicalSet_card_le` ✅
  - [ ] (c) `jointlyTypicalSet_indep_prob_le` 📋 deferred
- [ ] Phase C — Random codebook + averaging argument 📋 deferred
- [ ] Phase D — 主定理 (`R < C ⟹ ∃ code, P_err → 0`) 📋 deferred

## ゴール / Approach

**最終定理 (Cover-Thomas Theorem 7.7.1 achievability 半分)**:
任意の DMC `W : α → Measure β` と入力分布 `p : Measure α` (alphabet 有限) について、
`R < I_p(X; Y)` ならば、各 `ε > 0` に対して十分大きな `n` で
ある `(2^{nR}, n)`-code が存在し、最大誤り確率 (またはエラー率) が `ε` 未満になる。

**全体戦略** (Cover-Thomas 7.7):

1. **Channel をどう表現するか** — `Kernel α β` (Mathlib `ProbabilityTheory.Kernel`) を採用。DMC は kernel + 入力分布 `p : Measure α` で「入力に joint 確率分布」を `p ⊗ₖ W` で構築できる。**Mathlib 既存 API 整合**: `klDiv_compProd_eq_add`, `Measure.compProd_const` 等が DMC analysis にそのまま流れ込む。
2. **Memoryless extension**: i.i.d. 入力 `p^n : Measure (Fin n → α)` + product channel `W^n : (Fin n → α) → Measure (Fin n → β)`。これは `Kernel.pi` で構築。
3. **Mutual info の reshape**: B-7 の `mutualInfo_iid_eq_nsmul` を使い `I(X^n; Y^n) = n · I(X; Y)`。これで rate を per-symbol に正規化。
4. **Jointly typical set `A_ε^n`** — 3 条件 (`-log p(x)/n ≈ H(X)`, `-log q(y)/n ≈ H(Y)`, `-log p(x,y)/n ≈ H(X,Y)`) を満たす `(x,y)` の集合。
5. **3 つの bound** (Cover-Thomas Theorem 7.6.1):
   - **(a)** `P((X^n, Y^n) ∈ A_ε^n) → 1` (joint AEP)
   - **(b)** `|A_ε^n| ≤ 2^{n(H(X,Y)+ε)}` (size bound)
   - **(c)** Independent pair: `(X̃^n, Y^n)` with `X̃^n ⊥ Y^n` and marginal laws,
     `P((X̃^n, Y^n) ∈ A_ε^n) ≤ 2^{-n(I(X;Y)-3ε)}`
6. **Random codebook**: `M = ⌈2^{nR}⌉` codewords i.i.d. from `p^n`. Averaging argument で
   平均誤り確率 ≤ `2ε`. Existence of deterministic code: probabilistic method.
7. **R < I_p に対する rate 制約**: `R + 3ε < I` で (c) の bound から **union bound** で誤り → 0.

**短縮形 (B-7 corollary 直接活用)**: chain rule (Phase B) 経由ではなく `klDiv_pi_eq_sum` 直接を使えるところは使う。e.g. `I(X^n; Y^n) = n·I` は B-7 で 1 行。

## Phase 0 — Inventory ✅

**結果**: [`channel-coding-achievability-inventory.md`](channel-coding-achievability-inventory.md) 参照。

要点:
- **Mathlib に "channel" "capacity" 既存 API 無し** (loogle 確認: `Kernel`/`Std.Channel` の hit のみ、IT 用なし)。DMC は自前定義 `Channel α β := Kernel α β` (alias) または直接 `Kernel α β` を使う。Capacity 定義 `C := ⨆ p, I_p` も自前。
- **再利用 (Common2026 内)**:
  - `Common2026/Shannon/MIChainRule.lean`: `mutualInfo_iid_eq_nsmul` ★中核★
  - `Common2026/Shannon/AEP.lean`: typical set / size bound / 確率 → 1 の単独版 (`X^n` のみ)。**Joint AEP は X 単独 AEP の構造をコピペ + 拡張** で書く (block ratio plumbing が 1 軸 → 3 軸に増える)。
  - `Common2026/Shannon/MutualInfo.lean`: `klDiv_map_measurableEquiv`, `klDiv_prod_const_left`
  - `Common2026/Shannon/Converse.lean`: encoder / decoder + `errorProb` の単一形は **`MeasureFano.errorProb`** で既に立っている。block 版 `errorProb` も同 namespace で追加可。
  - `Common2026/Shannon/Pi.lean`: `MeasurableEquiv` reshape

## Phase A — Channel + Code 定義 ✅

**スコープ** (新規ファイル `Common2026/Shannon/ChannelCoding.lean`、~150-300 行を見積もる):

定義:
- `Channel α β := Kernel α β` (DMC 1-symbol). `[IsMarkovKernel W]` で Markov 制約。
- `Channel.productChannel (W : Channel α β) (n : ℕ) : Channel (Fin n → α) (Fin n → β)` — `Kernel.pi` 構成。
- `Code (M : ℕ) (n : ℕ) (α β : Type*)`: structure with `encoder : Fin M → (Fin n → α)`, `decoder : (Fin n → β) → Fin M`.
- `Code.averageErrorProb (W : Channel α β) (c : Code M n α β) : ℝ≥0∞` — `(1/M) ∑ m, P(decoder(Y^n) ≠ m | X^n = encoder(m))`.
- `mutualInfo_of_inputDistribution (W : Channel α β) (p : Measure α) : ℝ≥0∞` — `I(X; Y)` where joint = `p ⊗ₘ W`.
- (オプション) `channelCapacity (W : Channel α β) : ℝ≥0∞ := ⨆ p, mutualInfo_of_inputDistribution W p`. **Phase D で必要なければ skip**.

ステップ:
- [ ] `Channel α β` 定義 + `IsMarkovKernel` の前提整理
- [ ] `Code` structure + `errorProb` の block 版定義
- [ ] `mutualInfo_of_inputDistribution` 定義 + basic API (well-typed, `ne_top`)
- [ ] Phase A skeleton 単体で `lake env lean` 通過

## Phase B — Jointly typical set + 3 joint AEP bounds 🚧

**スコープ** (`Common2026/Shannon/ChannelCoding.lean` Phase B 節、行 226-514、約 305 行):

定義 (✅):
- `jointSequence Xs Ys : ℕ → Ω → α × β` — 既存 AEP の `typicalSet` に joint 軸を渡すための reshape ヘルパー
- `jointlyTypicalSet μ Xs Ys n ε : Set ((Fin n → α) × (Fin n → β))` — 3 条件 (X-typical, Y-typical, (X,Y)-typical) の交叉

主補題 (Cover-Thomas Theorem 7.6.1):
- [x] `jointlyTypicalSet_prob_tendsto_one` ✅ — bound (a): `P((X^n, Y^n) ∈ A_ε^n) → 1`. 既存 `typicalSet_prob_tendsto_one` を 3 軸並列で実行 + union bound on complements + `ENNReal.continuous_sub_left` で `1 - 0 = 1` 結ぶ。Pairwise IndepFun + IdentDistrib を 3 軸 (X, Y, joint) で受ける。
- [x] `jointlyTypicalSet_card_le` ✅ — bound (b): `|A_ε^n| ≤ exp(n·(H(X,Y)+ε))`. `Finset.image` 単射 + `Finset.card_image_of_injective` で size を joint single-axis typical set に翻訳、既存 `typicalSet_card_le` 適用。`[DecidableEq α/β] [Nonempty α/β]` 要 (AEP 要件継承)。
- [ ] `jointlyTypicalSet_indep_prob_le` 📋 **deferred**: `X̃ ⊥ Y` ⇒ `P((X̃^n, Y^n) ∈ A_ε^n) ≤ exp(-n·(I-3ε))`.
  - **deferred 理由**: 必要な新規 plumbing が以下:
    - **`typicalSet_prob_le`** (新規 AEP 補題): `x ∈ typicalSet ε ⟹ (μ.map (jointRV Xs n)) {x} ≤ exp(-n(H - ε))` の点別上界。これは `(μ.map (jointRV Xs n)) {x} = ∏ P(x_i)` の i.i.d. factorization が必要 (現状 AEP は `iIndepFun` を前提とした block measure factorization を持たない)。
    - **Independent pair の joint measure**: `X̃^n ⊗ Y^n` (両者の marginal product) 上の measure を AEP の `Pairwise IndepFun` 形と整合させて立てる plumbing。
  - **見積行数**: AEP に新規 200-300 行 + 本シード Phase B-(c) 本体 ~100 行 = 約 300-400 行追加で完了。

撤退理由 (Phase B-(a, b) 完了時点で stop):
- 残り Phase B-(c) + Phase C + Phase D で合計 1000-1600 行追加。元の見積 800-1500 行を upper bound で超え、本シード 1 セッションで sorry ゼロ完了は不確実。
- Phase A + Phase B-(a, b) 単独で再利用価値あり: Slepian-Wolf strong typicality (B 節別シード) で `jointlyTypicalSet_card_le` がそのまま使え、AEP joint 形 publish の意味で independent value がある。

## Phase C — Random codebook + averaging argument 📋

**スコープ** (~300-500 行):

戦略候補:
- **(C1) Full probabilistic method**: random codebook を確率測度として構成し expectation で averaging。`Code` structure を index でランダム化、`∫ codebook P_err < ε ⟹ ∃ codebook, P_err < ε`。
- **(C2) Concrete pigeonhole**: P_err の合計 (over codebooks) ≤ ε · |codebooks| ⇒ 1 つ存在。**より軽量**。`Fintype` 上の sum で `Finset.exists_le_of_sum_le` 系。

判断: **(C2) を採用** (probabilistic method 用の measure-theoretic plumbing を避ける)。
- Codebooks 全体は `(Fin M → Fin n → α)` の有限集合 (alphabet 有限 + n 有限) で扱える。
- Sum 平均 ≤ M · ε ⇒ exists deterministic codebook。

ステップ:
- [ ] `Code` の集合上 `averageErrorProb` の sum / mean を立てる
- [ ] Joint typical decoding rule + その誤り確率の bound (上記 (a)-(c) bound から union bound)
- [ ] Averaging argument: average ≤ 2ε ⇒ ∃ code with P_err < 2ε
- [ ] Phase C 全体で `lake env lean` 通過

## Phase D — 主定理 📋

**スコープ** (~200-400 行):

主定理:
```lean
theorem channel_coding_achievability
    (W : Channel α β) [IsMarkovKernel W]
    (p : Measure α) [IsProbabilityMeasure p]
    (R : ℝ) (hR : R < (mutualInfo_of_inputDistribution W p).toReal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ (c : Code ⌈Real.exp (n * R · Real.log 2)⌉₊ n α β),
      (c.averageErrorProb W p).toReal < ε
```

ステップ:
- [ ] Phase C の codebook ↔ `2^{nR}` メッセージ数の対応
- [ ] `n → ∞` で各 bound が同時に成立する N の存在
- [ ] Phase D の `lake env lean` 通過 + `sorry` ゼロ

## 撤退ライン / 部分完了境界

本シードは **最難関**。以下の境界で部分完了をコミット可:

- **Phase A 完了で commit**: Channel / Code / errorProb / capacity 定義 publish。Phase B 以降を deferred plan へ。
- **Phase B 完了で commit**: Joint typical set + 3 bound publish。後段 (Phase C-D) deferred。Slepian-Wolf 等で部分再利用可能。
- **Phase C 完了で commit**: averaging argument publish。Phase D は existence of code を結合するだけだが、テクニカルな `n → ∞` 制御が残る。
- **Phase D 完了で commit**: 主定理 publish。完成。

**コミット粒度**: Phase 区切りで 1 commit 1 行。最終 commit は sorry ゼロで通る集合のみ。

## 判断ログ

1. **Channel を `Kernel α β` で表現** (Phase 0): Mathlib に既存 channel/IT API がない。`Kernel` は `klDiv_compProd_eq_add` 等の MI plumbing と整合。ad-hoc な `α → Measure β` で書くと積分の measurability 補題を再発明する羽目になるため避ける。

2. **(C2) Concrete pigeonhole を averaging で採用予定** (Phase 0): probabilistic method を `IsProbabilityMeasure (codebook空間)` で書くと kernel/product/Fubini plumbing を新規に増やすことになる。Codebooks が有限集合になる (有限 alphabet × 有限 n × 有限 M) ので `Finset` 上の sum 不等式 → `Finset.exists_le_of_sum_le` で十分。

3. **Phase B (jointly typical) のサイズ評価**: Cover-Thomas 7.6.1 の 3 つの bound はすべて 1 軸 typical set の組み合わせ。既存 `AEP.lean` の `typicalSet_card_le` を `(X, Y)` 軸で適用すれば (b) は 1 行 + reshape で出る。(a) も同じ。(c) のみが新規 → ここに最大のテクニカルリスク。

4. **Capacity 定義 `⨆ p, I_p` を Phase A で立てるか**: 主定理は **固定 input distribution `p` での `R < I_p`** で表現する方が短い (sup を回避)。Phase A で sup 形を立てるのは optional とし、まず固定 `p` 形で進める。

5. **(2026-05-12 Phase 0 終了時の見積もり再評価)**: Phase A-D 合計 1050-1900 行を見込む。これは元の見積 800-1500 行の上限相当。**3000 行を超える兆候はない** → Phase 単位で進行可。判断 = 続行 (stop しない)。

6. **(2026-05-12 Phase B-(a, b) 完了時 stop)**: 達成 514 行、残り Phase B-(c) + C + D で 1000-1600 行追加。Phase B-(c) は **i.i.d. product factorization** (現 AEP は pairwise indep のみ) の新規 plumbing が必要、見積 200-300 行 + 本体 100 行。本シード 1 セッションで sorry ゼロ完了は不確実なので **Phase A + Phase B-(a, b) で stop、deferred 区切り**。Phase A + B-(a, b) 単独で Slepian-Wolf strong typicality 等で再利用価値あり、AEP joint 形の publish として independent value がある。後続 B-1 / B-4 / B-8 シードは本シードに依存しないため進行可。
