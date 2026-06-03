# Channel coding achievability ムーンショット計画 (B-3) 🌙

> 起草 2026-05-12 / B-7 完了直後。Cover-Thomas Ch 7.7 (random coding argument) を AEP plumbing + B-7 i.i.d. corollary `mutualInfo_iid_eq_nsmul` を入口に Lean 化。**最難関シード** (見積 800-1500 行 / 4-6 週)。
>
> **2026-05-12 状態 (二度目の更新)**: Phase A + Phase B-(a,b,c) 完了。Phase C (random codebook + averaging) + Phase D (主定理) は依然 deferred。Phase B-(c) (independent pair bound) は AEP 拡張 (`typicalSet_prob_le`) + `iIndepFun_iff_map_fun_eq_pi_map` 経由の point-wise factorization で完成 (B-3' 区切り)。
>
> 実態整合 (2026-05-20): DONE-HONEST-HYPS — Phase C+D は子 plan B-3'' (`channel-coding-phase-cd-plan.md`) で完全閉鎖済。主定理 `channel_coding_achievability` (`InformationTheory/Shannon/ChannelCodingAchievability.lean:1607`、0 sorry) が `(W p hp_pos hW_pos R hR ε')` で `∃ N, ∀ n ≥ N, ∃ M c, (c.averageErrorProb W).toReal < ε'` を結論。本ファイル (`ChannelCoding.lean`) は Phase B 3 bound のみ (B-3') で、Phase C/D は別ファイル。下記 Phase C/D の「deferred」記述は B-3'' で解消済 (stale)。

## 進捗

- [x] Phase 0 — Inventory (Mathlib + 既存 InformationTheory 探索) ✅ → [channel-coding-achievability-inventory.md](channel-coding-achievability-inventory.md)
- [x] Phase A — Channel + Code 定義 ✅ (`InformationTheory/Shannon/ChannelCoding.lean`, 行 1-225, 約 200 行)
- [x] Phase B — Jointly typical set + 3 joint AEP bounds ✅
  - [x] (a) `jointlyTypicalSet_prob_tendsto_one` ✅
  - [x] (b) `jointlyTypicalSet_card_le` ✅
  - [x] (c) `jointlyTypicalSet_indep_prob_le` ✅ (2026-05-12 二度目)
- [ ] Phase C — Random codebook + averaging argument 📋 deferred (B-3'')
- [ ] Phase D — 主定理 (`R < C ⟹ ∃ code, P_err → 0`) 📋 deferred (B-3'')

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
- **再利用 (InformationTheory 内)**:
  - `InformationTheory/Shannon/MIChainRule.lean`: `mutualInfo_iid_eq_nsmul` ★中核★
  - `InformationTheory/Shannon/AEP.lean`: typical set / size bound / 確率 → 1 の単独版 (`X^n` のみ)。**Joint AEP は X 単独 AEP の構造をコピペ + 拡張** で書く (block ratio plumbing が 1 軸 → 3 軸に増える)。
  - `InformationTheory/Shannon/MutualInfo.lean`: `klDiv_map_measurableEquiv`, `klDiv_prod_const_left`
  - `InformationTheory/Shannon/Converse.lean`: encoder / decoder + `errorProb` の単一形は **`MeasureFano.errorProb`** で既に立っている。block 版 `errorProb` も同 namespace で追加可。
  - `InformationTheory/Shannon/Pi.lean`: `MeasurableEquiv` reshape

## Phase A — Channel + Code 定義 ✅

**スコープ** (新規ファイル `InformationTheory/Shannon/ChannelCoding.lean`、~150-300 行を見積もる):

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

**スコープ** (`InformationTheory/Shannon/ChannelCoding.lean` Phase B 節、行 226-514、約 305 行):

定義 (✅):
- `jointSequence Xs Ys : ℕ → Ω → α × β` — 既存 AEP の `typicalSet` に joint 軸を渡すための reshape ヘルパー
- `jointlyTypicalSet μ Xs Ys n ε : Set ((Fin n → α) × (Fin n → β))` — 3 条件 (X-typical, Y-typical, (X,Y)-typical) の交叉

主補題 (Cover-Thomas Theorem 7.6.1):
- [x] `jointlyTypicalSet_prob_tendsto_one` ✅ — bound (a): `P((X^n, Y^n) ∈ A_ε^n) → 1`. 既存 `typicalSet_prob_tendsto_one` を 3 軸並列で実行 + union bound on complements + `ENNReal.continuous_sub_left` で `1 - 0 = 1` 結ぶ。Pairwise IndepFun + IdentDistrib を 3 軸 (X, Y, joint) で受ける。
- [x] `jointlyTypicalSet_card_le` ✅ — bound (b): `|A_ε^n| ≤ exp(n·(H(X,Y)+ε))`. `Finset.image` 単射 + `Finset.card_image_of_injective` で size を joint single-axis typical set に翻訳、既存 `typicalSet_card_le` 適用。`[DecidableEq α/β] [Nonempty α/β]` 要 (AEP 要件継承)。
- [x] `jointlyTypicalSet_indep_prob_le` ✅ (2026-05-12 二度目): `X̃^n × Y^n` 独立 product measure 下で `((μX^n) × (μY^n)) A_ε^n ≤ exp(-n(I-3ε))`.

### Phase B-(c) Approach

**主補題シグネチャ** (`InformationTheory/Shannon/ChannelCoding.lean` 末尾):

```lean
theorem jointlyTypicalSet_indep_prob_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((μ.map (jointRV Xs n)).prod (μ.map (jointRV Ys n))).real
        (jointlyTypicalSet μ Xs Ys n ε))
      ≤ Real.exp ((n : ℝ) *
          ((InformationTheory.Shannon.entropy μ (jointSequence Xs Ys 0)
            - InformationTheory.Shannon.entropy μ (Xs 0)
            - InformationTheory.Shannon.entropy μ (Ys 0))
           + 3 * ε))
```

(LHS は `μ.real` (=`measureReal`) 形で実数値、RHS は `Real.exp` 形。`-I+3ε = HZ - HX - HY + 3ε` の符号順で書く。)

**Approach** (Phase B-(c) のみ):

1. **新規 AEP 補題** `typicalSet_prob_le` (`InformationTheory/Shannon/AEP.lean` Phase G 節として追加, ~80 行):
   - 仮定: `iIndepFun (fun i => Xs i) μ` + `∀ i, IdentDistrib (Xs i) (Xs 0) μ μ` + `∀ x, 0 < (μ.map (Xs 0)).real {x}`.
   - 結論: `x ∈ typicalSet μ Xs n ε ⟹ (μ.map (jointRV Xs n)).real {x} ≤ Real.exp (- (n : ℝ) * (entropy μ (Xs 0) - ε))`.
   - 証明 plumbing:
     - `iIndepFun.precomp (Fin.val_injective : Function.Injective (Fin.val : Fin n → ℕ))` で `iIndepFun (fun i : Fin n => Xs i.val) μ` を得る。
     - `iIndepFun_iff_map_fun_eq_pi_map` で `μ.map (fun ω i => Xs i.val ω) = Measure.pi (fun i : Fin n => μ.map (Xs i.val))`. LHS は `jointRV Xs n` と defeq.
     - `IdentDistrib.map_eq` で各 `i` に対し `μ.map (Xs i.val) = μ.map (Xs 0)`.
     - `Measure.pi_singleton`: `(Measure.pi μ) {x} = ∏ i, μ i {x i}`. これを `measureReal` 形に変換 (有限積).
     - `mem_typicalSet_iff` の片側 (`-ε < (∑/n) - H` ⇒ `n(H - ε) < ∑ pmfLog (x i)`) ⇒ `exp(-∑) < exp(-n(H-ε))` ⇒ `∏ P(x i) < exp(-n(H-ε))`.

2. **本体 `jointlyTypicalSet_indep_prob_le`** (~120-150 行):
   - 有限離散 product measure: `((μ.map (jointRV Xs n)).prod (μ.map (jointRV Ys n))).real S = ∑ (x, y) ∈ S.toFinset, μX.real {x} · μY.real {y}` (有限 alphabet).
     - 鍵: `Set.Finite.measureReal_eq` + `Measure.prod_apply_of_mem_singleton` 系。または `Finset.tsum` form。
   - 各 (x, y) ∈ A_ε^n は X-typical かつ Y-typical なので `μX.real {x} · μY.real {y} ≤ exp(-n(HX - ε)) · exp(-n(HY - ε)) = exp(-n(HX + HY - 2ε))` (新規 `typicalSet_prob_le` 2 回).
   - 個数 `≤ exp(n(HZ + ε))` (B-(b) `jointlyTypicalSet_card_le`, `HZ := entropy μ (jointSequence Xs Ys 0)`)。
   - 結合: `μ.real A ≤ exp(n(HZ + ε)) · exp(-n(HX + HY - 2ε)) = exp(n(HZ - HX - HY + 3ε)) = exp(-n(I - 3ε))`.

**`hidentZ` の不要性**: Phase B-(c) では joint 軸の identification は **使わない** (X 軸 / Y 軸の i.i.d.-ness で十分)。`hposZ` は `jointlyTypicalSet_card_le` (B-(b)) の signature が要求するため受け取る。

**実装場所**: AEP 拡張 (~80 行) は **`InformationTheory/Shannon/AEP.lean` 末尾の Phase G 節**として追加 (file 分割せず)。本体 (Phase B-(c) ~150 行) は **既存 `ChannelCoding.lean` 末尾**に追加 (file 分割せず)。両 file が `lake env lean` clean を維持する。

撤退理由 (Phase B 完了時点で再 stop):
- 残り Phase C + Phase D で 600-1000 行追加 (random codebook 上の確率空間構築 + main theorem の `n → ∞` 制御)。
- B-3' (Phase B-(c) 単独) で完了し、Phase C-D は B-3'' deferred として切り出す。
- Phase B 全体は **3 つの bound publish** で完成し、Slepian-Wolf 等で再利用価値あり。

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
