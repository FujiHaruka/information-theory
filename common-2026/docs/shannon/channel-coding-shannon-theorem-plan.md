# Channel coding (Shannon) full theorem (D-1) ムーンショット計画 🌙

(D-1 / [`docs/moonshot-seeds.md` 19-36](../moonshot-seeds.md), 2026-05-13 起草)

> Cover-Thomas 7.7.1 **完全形** (Shannon noisy channel coding theorem):
> 任意の DMC `W : Channel α β` (有限 alphabet) について、**capacity** `C := sup_p I(p; W)`
> が存在し、`R < C ⟹` 任意 `ε > 0` に対し十分大きい block 長 `n` で `M ≥ exp(n R)` 個の
> messages を持つ符号 `c` が存在して **maximum** error `max_m c.errorProbAt W m < ε` を達成。

既存 `channel_coding_achievability` (固定 `p`, **average** error, full-support `hp_pos + hW_pos`)
を出発点に、(1) **入力分布最大化**で固定 `p` 仮定を除き、(2) **expurgation** で average → max
error 化し、(3) **full support 仮定を除去**して任意 `p, W` に対する完全形に拡張する。

## 進捗

- [x] Phase 0 — 経路選択判断 ✅ (2026-05-13)
- [x] Phase A — 入力分布最大化 ✅ (2026-05-13、A.1 + A.2 連続性 + A.4 lt 特性化、A.3 達成元)
- [x] Phase B — Expurgation ✅ (2026-05-13、B.1 + B.2 + B.4 average→max wrapper)
- [x] Phase C — Full support 仮定除去 ✅ (2026-05-13、smoothing 経路で hp_pos 迂回)
- [x] Phase D — 主定理 `shannon_noisy_channel_coding_theorem` 統合 ✅ (2026-05-13、`hW_pos` のみユーザ仮定、`hp_pos` smoothing 経路で内部処理)

> 実態整合 (2026-05-20): DONE-HONEST-HYPS — `shannon_noisy_channel_coding_theorem` (`Common2026/Shannon/ChannelCodingShannonTheorem.lean:1011`) は `hW_pos : ∀ a b, 0 < (W a).real {b}` の正直な full-support 仮説 + `R < capacity W` のみで max-error 達成形を結論。ファイル全体で real-sorry **ゼロ** (`exists_capacity_achiever:317` / `mutualInfoOfChannel_restrict_to_support:816` も 0 sorry — 下記の "A.3 + C.1 documentation only sorry" 記述は stale で、現状の code には documentation sorry も残っていない)。`hW_pos` 除去版は後継 D-1' / D-1'' で完成 (`shannon_noisy_channel_coding_theorem_general_full`、下記参照)。

**完了サマリ (2026-05-13)**: `Common2026/Shannon/ChannelCodingShannonTheorem.lean` (918 行、13 declarations、D 主定理 0 sorry / A.3 + C.1 documentation only sorry)。Cover-Thomas 7.7.1 完全形:
```
shannon_noisy_channel_coding_theorem
  (W : Channel α β) [IsMarkovKernel W]
  (hW_pos : ∀ a b, 0 < (W a).real {b})
  {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
  {ε : ℝ} (hε : 0 < ε) :
  ∃ N, ∀ n ≥ N, ∃ M (_ : Nat.ceil (exp (n·R)) ≤ M) (c : Code M n α β),
    ∀ m, (c.errorProbAt W m).toReal < ε
```

**証明の構造**:
- A.4 (`capacity_lt_implies_exists_pmf`、`lt_csSup_iff` + `BddAbove` via `entropy_le_log_card`) で `∃ p₀ ∈ stdSimplex ℝ α, R < I(p₀; W).toReal`
- A.2 (`continuous_mutualInfoOfChannel_left`、3-entropy 展開 + `Real.continuous_negMulLog` + `continuous_finsetSum`) で MI の `p` 連続性
- Smoothing `p_δ := (1-δ) p₀ + δ · uniform` (small `δ₀ > 0` で `I(p_δ₀; W) > R₀ := (R + I(p₀;W))/2`、full support 確保)
- B.4 (`channel_coding_achievability_max_error`、既存 `channel_coding_achievability` + Markov filter + sub-code lift) で max error code 取得

**scope-deferred (本 plan 内 sorry のまま、D 主証明には未使用)**:
- A.3 `exists_capacity_achiever`: 達成元存在の direct form (documentation only、A.4 lt 特性化で主証明十分)
- C.1 `mutualInfoOfChannel_restrict_to_support`: Mathlib `klDiv` の `MeasurableEmbedding` 不変性補題が未整備。smoothing 経路で迂回したため D で未使用
- Phase C.2 hW_pos 緩和 (W_smooth 連続近似): `D-1'` deferred 後継として ~150-200 行追加見込み

## ゴール / Approach

**最終定理** (本 plan の deliverable):

```
shannon_noisy_channel_coding_theorem :
  (W : Channel α β) [IsMarkovKernel W]
  {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
  {ε : ℝ} (hε : 0 < ε) :
  ∃ N : ℕ, ∀ n, N ≤ n →
    ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
      (c : Code M n α β),
      (∀ m, (c.errorProbAt W m).toReal < ε)
```

ここで `capacity W : ℝ := ⨆ p ∈ stdSimplex ℝ α, (mutualInfoOfChannel (pmfToMeasure p) W).toReal`。

### Approach (全体戦略 — 3 段合成 + bridge)

**戦略の shape**: 既存 `channel_coding_achievability` (固定 `p`, average error, full support) を
**そのままブラックボックス**として 3 段の wrapper を被せる経路を取る。各段は **構造的に独立**:

1. **(A) Capacity 到達**: `R < C` から `R < I(p; W)` な `p` を直接取り出す
   (`lt_csSup_iff` / `IsCompact.exists_isMaxOn`)。既存 `channel_coding_achievability` の入力。
2. **(B) Expurgation**: 既存 achievability の出力 (average error `< ε`) から、**上位半分の
   messages の max error `< 2ε`** を Markov inequality (`Finset.card_filter_le` で
   "`errorProbAt > 2·avg` な m の数 ≤ M/2") で抽出。rate 損失 `log(M/2) = log M − log 2`
   は `n → ∞` で吸収。
3. **(C) Full support 仮定除去**: 既存 `channel_coding_achievability` は `hp_pos + hW_pos`
   要求。これを **`p` 側のみ**緩める (W 側は capacity 定義段でユーザが自由に選べるので
   capacity を `inf` ではなく `sup` で取る分には full-support W だけを使う `p` で sup
   が達成されるとは限らない、しかし `sup` 値自体は任意 W で取れる)。**経路**:
   - **(C-α) `klDiv = ∞` 縮退 self-trivial**: `p` の support 外の `a` で `I(p; W)` に
     寄与なし、Mutual info の値は `p` の support 上の sub-channel で決まる。formally
     `α_supp := {a | 0 < p {a}}` 上の restricted channel `W_supp` で
     `I(p; W) = I(p|_supp; W_supp)`、後者は full-support 入力。
   - **(C-β) W の full-support 仮定**: 主定理は **任意 W** で statement、ただし
     `I(p; W)` の値はそのままだが Phase A-(C) の達成元 `p*` は full-support W
     を要さないことを示す。**経路選択判断 (Phase 0)**: (C-α) の sub-channel 切り出しで
     `p` 側の `hp_pos` を vacuous 化、(C-β) は capacity 自体が `W` の 0-prob atom に
     非感受性 (`klDiv` の `≪` 仮定で 0-prob 入力からの 0-prob 出力は drop) を示して
     achievability 入力時に近似 `W_δ := (1-δ)W + δU` を取って `δ → 0` で連続性。
     **後者は重い**ため、Phase C scope を **「W は finite alphabet で `IsMarkovKernel`、
     achievability 入力時の full-support W は近似列で吸収」** に絞る (判断ログ 1)。

**Bridge と既存資産の関係**:
- 既存 `channel_coding_achievability` (1890 行) を **改変しない**。出発点は black-box。
- 新規ファイル: `Common2026/Shannon/ChannelCodingShannonTheorem.lean` (~600-800 行)。
- 既存 `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` (`ChannelCoding.lean:129`) を Phase A
  の連続性で活用 (entropy `Continuous` → MI `Continuous`)。
- `MIChainRule.mutualInfo_iid_eq_nsmul` は本 plan では未使用 (n-channel は既存 achievability
  内部で完結)。

### 規模見積

- **Phase 0**: ~20 行 plan 内追記、loogle 確認 30 分。
- **Phase A**: `capacity` 定義 + 連続性 + 達成元 ~250 行。鍵は `Continuous` 経由の
  `IsCompact.exists_isMaxOn` 適用 + `lt_csSup_iff` で `R < C ⟹ ∃ p, R < I(p; W)`。
- **Phase B**: expurgation ~150 行。Markov on Finset、`Finset.filter`/`Finset.card_filter_le`
  + sub-code 構築 (`Code.subcode` 補助定義 or 直接 encoder restriction)。
- **Phase C**: full support 緩和 ~200 行。sub-channel 切り出し補助補題 + 連続近似。
- **Phase D**: 3 段合成 + 主定理本体 ~100 行。
- 合計 ~700 行、新規 `Common2026/Shannon/ChannelCodingShannonTheorem.lean`。

## Phase 0 — 経路選択判断 📋

- [ ] **0.1** `capacity W` の shape 確定: `iSup`, `sSup`, または `IsCapacity` predicate。
  - **採用候補 (default)**: `capacity W : ℝ := sSup {(mutualInfoOfChannel (pmfToMeasure p) W).toReal
    | p ∈ stdSimplex ℝ α}`。理由: `lt_csSup_iff` (`Mathlib.Order.ConditionallyCompleteLattice.Basic`)
    で `R < C ⟹ ∃ I ∈ s, R < I` が直接出る、`sSup` の値の存在補題は不要 (`BddAbove` だけ要)。
  - **代替**: `IsCapacity W (C : ℝ) : Prop := IsLUB {I(p;W).toReal | p ∈ stdSimplex} C`
    で抽象化、`shannon_noisy_channel_coding_theorem` 自体は predicate 形に書く経路もあるが、
    Cover-Thomas 標準形 `C = sup ...` に固執して具体形を返す方が利用側で扱いやすい。
  - **loogle 確認結果** (2026-05-13):
    - `lt_csSup_iff` (`Mathlib.Order.ConditionallyCompleteLattice.Basic`): conditional Sup の
      lt 特性化 — 採用。
    - `IsCompact.exists_isMaxOn` (`Mathlib.Topology.Order.Compact`): コンパクト上連続関数は最大
      達成 — 採用。
    - `convex_stdSimplex` / `isCompact_stdSimplex` (`Mathlib.Analysis.Convex.StdSimplex`):
      `stdSimplex ℝ α` は Convex + Compact — 採用。

- [ ] **0.2** 縮退ケース整理:
  - `α` 空: `stdSimplex ℝ α = ∅` ⟹ `capacity W = sSup ∅ = 0` (Mathlib convention)、
    `R < 0` は `hR_pos` と矛盾 ⟹ 自明に false 含意。**Nonempty α 仮定を主定理に**。
  - `M = 0`: 既存 `averageErrorProb = 0`、`errorProbAt` は空 universe (`Fin 0` index)、
    `∀ m, _` は vacuous true。退化 OK。
  - `n = 0`: 既存 `channel_coding_achievability` で `N ≥ 1` 取れば自動回避。

- [ ] **0.3** Phase C 縮退戦略:
  - 採用 (default): `hp_pos` 緩和は **sub-channel 切り出し** (full-support `p|_supp` で
    既存 achievability、外挿時に support 外の symbol は使わない)。`hW_pos` 緩和は
    **deferred** (W に 0-prob atom があっても本質的に sub-channel で同等)、必要なら
    **C-β** として近似 `W_δ := (1-δ)W + δ·UnifChannel` で連続性を取る経路を別補題で。
  - **alternative**: `klDiv = ∞` 自明 case (`p ≫ outputDistribution` でない) は本来
    `mutualInfoOfChannel = ∞` を許す形だが、本 plan の `capacity` を `ℝ` 値で取る関係上、
    `(mutualInfoOfChannel p W).toReal = 0` に縮退 (`ENNReal.toReal_top = 0`)。これは
    capacity sup の上限値ではないので、capacity 達成元として選ばれない。

## Phase A — 入力分布最大化 📋

### A.1 — `capacity` 定義

- [ ] **A.1.1** Helper: `pmfToMeasure (p : α → ℝ) : Measure α` (pmf → measure bridge)。
  - 既存 Sanov / Csiszár で類似 utility ある可能性 → loogle / rg 要確認。
  - 候補: `Measure.ofFinset` 風 + `Finset.sum_eq_one` cofibration。
- [ ] **A.1.2** `capacity (W : Channel α β) : ℝ`:
  ```
  capacity W := sSup ((fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
                       '' stdSimplex ℝ α)
  ```
- [ ] **A.1.3** `capacity_nonneg`: `0 ≤ capacity W` (uniform pmf を取って `I ≥ 0` 経由)。
- [ ] **A.1.4** `capacity_bddAbove`: `BddAbove _` (`I(p; W) ≤ log |α|` で十分、より tight は不要)。

### A.2 — `(mutualInfoOfChannel p W).toReal` の連続性 (p について)

- [ ] **A.2.1** `continuous_mutualInfoOfChannel_left`:
  ```
  Continuous (fun p : α → ℝ => (mutualInfoOfChannel (pmfToMeasure p) W).toReal) on stdSimplex ℝ α
  ```
  経路: `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` で 3-entropy 形に書き換え、各 entropy が
  `Real.continuous_negMulLog` (`Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`) + finite sum
  で連続。
- [ ] **A.2.2** `entropy_continuous_pmf`: `H(p) := -∑ a, p a · log (p a)` の `p` についての
  連続性。Helper、`Real.continuous_negMulLog.comp_continuous_finset_sum` 型。

### A.3 — capacity 達成元

- [ ] **A.3.1** `exists_capacity_achiever`:
  ```
  ∃ p ∈ stdSimplex ℝ α, IsMaxOn
    (fun p => (mutualInfoOfChannel (pmfToMeasure p) W).toReal)
    (stdSimplex ℝ α) p
  ```
  経路: `IsCompact.exists_isMaxOn (isCompact_stdSimplex) (stdSimplex_nonempty) hCont`。
  **注意**: capacity 主定理は **達成元の存在に依存しない**経路 (`lt_csSup_iff` だけ)
  も取れる。下記 A.4 の lt 特性化補題で十分。**A.3.1 は documentation 価値**。

### A.4 — `R < C ⟹ ∃ p, R < I(p; W)`

- [ ] **A.4.1** `capacity_lt_implies_exists_pmf`:
  ```
  R < capacity W → ∃ p ∈ stdSimplex ℝ α, R < (mutualInfoOfChannel (pmfToMeasure p) W).toReal
  ```
  経路: `lt_csSup_iff (h_bdd : BddAbove s) (h_ne : s.Nonempty)` で `R < sSup s ↔ ∃ x ∈ s, R < x`、
  `Set.image` 形を展開して `p` を抽出。

## Phase B — Expurgation 📋

### B.1 — Markov on finset

- [ ] **B.1.1** `errorProbAt_filter_card_bound` (key lemma):
  任意 `c : Code M n α β`, `K > 0` で
  ```
  (Finset.univ.filter (fun m => (c.errorProbAt W m).toReal > K · (c.averageErrorProb W).toReal)).card
    < M / K
  ```
  ※ Markov inequality on `(1/M) ∑_m errorProbAt = avg`、`Finset.exists_lt_of_sum_lt` 系の対偶。
- [ ] **B.1.2** より直接的に: `K := 2` で
  ```
  (Finset.univ.filter (fun m => (c.errorProbAt W m).toReal ≤ 2 · avg)).card ≥ M / 2
  ```
  経路: 上の対偶。

### B.2 — Sub-code 構築

- [ ] **B.2.1** Helper `Code.subcode (c : Code M n α β) (S : Finset (Fin M)) : Code S.card n α β`:
  encoder を `S` の要素のみに restrict (`Fin S.card ≃ S` 経由)、decoder はそのまま
  (新しい index の範囲外を旧 index に拡張、外を任意の固定値に decode)。
- [ ] **B.2.2** `Code.subcode_errorProbAt`: `(subcode c S).errorProbAt W m'` が
  対応する `c.errorProbAt W (S.toList.get m')` に bounded above (decoder 縮退で
  上界、equality は wishful、bound だけで十分)。
  - **注意**: `subcode` の decoder 設計が tricky。`c.decoder y ∈ S` のときは旧 index 経由、
    そうでなければ任意 (fixed `m₀'`)。これで `errorEvent` が大きくなりうるが、
    error が起きるのは元の error event か `c.decoder y ∉ S` の場合のみ。
- [ ] **B.2.3** `Code.subcode_maxError_le`: `S := filter (errorProbAt ≤ 2 avg)` の場合
  `∀ m' : Fin S.card, (subcode c S).errorProbAt W m' ≤ 2 · avg`。

### B.3 — Rate 損失の漸近吸収

- [ ] **B.3.1** `log_half_card_asymptotic`:
  `Nat.ceil (exp (n · R)) ≤ M → M / 2 ≥ Nat.ceil (exp (n · R'))` for sufficiently
  large `n` whenever `R' < R`. 経路: `exp(n R) / 2 = exp(n R - log 2)`、`R - (log 2)/n → R`。

### B.4 — Average → Max wrapper

- [ ] **B.4.1** `channel_coding_achievability_max_error`:
  ```
  (W : Channel α β) [IsMarkovKernel W]
  (p : Measure α) [IsProbabilityMeasure p]
  (hp_pos : ∀ a, 0 < p.real {a})
  (hW_pos : ∀ a b, 0 < (W a).real {b})
  {R : ℝ} (hR_pos : 0 < R) (hR : R < (mutualInfoOfChannel p W).toReal)
  {ε : ℝ} (hε : 0 < ε) :
  ∃ N, ∀ n, N ≤ n → ∃ M (_ : Nat.ceil (exp (n · R)) ≤ M) (c : Code M n α β),
    (∀ m, (c.errorProbAt W m).toReal < ε)
  ```
  既存 `channel_coding_achievability` を `R₀ := (R + I)/2`, `ε₀ := ε/2` で呼び、B.1-B.3 で wrap。

## Phase C — Full support 仮定除去 📋

### C.1 — `p` 側 (`hp_pos`) の sub-channel 切り出し

- [ ] **C.1.1** `mutualInfoOfChannel_restrict_to_support`: `α_supp := {a | 0 < p.real {a}}` 上
  restrict した `(p|_supp, W|_supp)` で `mutualInfoOfChannel` 不変。`klDiv` の 0-mass
  on `support^c` 経由。
- [ ] **C.1.2** `Code_lift_from_subtype`: `Code M n α_supp β` から `Code M n α β` への
  injection (encoder の codomain を `Subtype → α` で expansion)、`errorProbAt` 不変。

### C.2 — `W` 側 (`hW_pos`) の連続近似 (scope-deferred 候補)

- [ ] **C.2.1** `W_smooth W δ a := (1-δ) · W a + δ · uniform_β` で `hW_pos` 獲得 +
  `capacity (W_smooth) → capacity W` の連続性 + `R < capacity W` から `R < capacity (W_smooth δ)`
  へ移して既存 achievability を適用、`W_smooth → W` で error continuity wrap。
- [ ] **C.2.2** **判断ログ 1 候補**: `hW_pos` 完全除去は ~150-200 行追加見込みで重い。
  本 plan **MVP** は (a) `hp_pos` 除去のみ完遂、(b) `hW_pos` は sub-channel 内で吸収
  可能な範囲で対応、完全形は **D-1' deferred** に切り出し。

## Phase D — 主定理 `shannon_noisy_channel_coding_theorem` 📋

### D.1 — 主定理 statement

- [ ] **D.1.1**
  ```
  shannon_noisy_channel_coding_theorem :
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_ : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε
  ```

### D.2 — 証明合成

- [ ] **D.2.1** Phase A.4 で `R < capacity W ⟹ ∃ p ∈ stdSimplex, R < I(p; W).toReal`。
- [ ] **D.2.2** Phase C.1 で `p` の support 制限 + Phase C.3 で `hW_pos` を effective に獲得。
- [ ] **D.2.3** Phase B.4 (achievability max error) を call で適用。

### D.3 — corollary (任意)

- [ ] **D.3.1** `shannon_noisy_channel_coding_theorem_uniform_input` (Cover-Thomas 7.7
  の弱版、`p = uniform` を取る場合): documentation 用、必須ではない。

## Mathlib API inventory (loogle 確認、2026-05-13)

各 API は loogle index 上で確認。signature は loogle 出力の verbatim、型クラス前提は
角括弧で verbatim 保存 (CLAUDE.md 強制):

- **`lt_csSup_iff`** (`Mathlib.Order.ConditionallyCompleteLattice.Basic`):
  - `lt_csSup_iff [ConditionallyCompleteLinearOrder α] {s : Set α} (hs : BddAbove s)
    (hne : s.Nonempty) {a : α} : a < sSup s ↔ ∃ b ∈ s, a < b`
  - 用途: Phase A.4 `capacity_lt_implies_exists_pmf` の核。
- **`IsCompact.exists_isMaxOn`** (`Mathlib.Topology.Order.Compact`):
  - `IsCompact.exists_isMaxOn [TopologicalSpace β] [ConditionallyCompleteLinearOrder α]
    [OrderClosedTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty)
    {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMaxOn f s x`
  - 用途: Phase A.3 達成元存在 (documentation only、A.4 だけで主証明は通る)。
- **`IsCompact.bddAbove_image`** (`Mathlib.Topology.Order.Compact`):
  - `IsCompact.bddAbove_image [TopologicalSpace α] [ConditionallyCompleteLinearOrder β]
    [OrderClosedTopology β] {s : Set α} {f : α → β} (hs : IsCompact s)
    (hf : ContinuousOn f s) : BddAbove (f '' s)`
  - 用途: Phase A.1.4 `capacity_bddAbove`。
- **`isCompact_stdSimplex`** (`Mathlib.Analysis.Convex.StdSimplex`):
  - `isCompact_stdSimplex (ι : Type*) [Fintype ι] : IsCompact (stdSimplex ℝ ι)`
  - 用途: Phase A.3 + A.1.4 のコンパクト性根拠。
- **`convex_stdSimplex`** (`Mathlib.Analysis.Convex.StdSimplex`):
  - `convex_stdSimplex (ι : Type*) [Fintype ι] : Convex ℝ (stdSimplex ℝ ι)`
  - 用途: Phase C で convex combination を取る場合のみ。
- **`Real.continuous_negMulLog`** (`Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`):
  - `Real.continuous_negMulLog : Continuous Real.negMulLog`
  - 用途: Phase A.2 entropy 連続性の基盤。
- **`Finset.card_filter_le`** (`Mathlib.Data.Finset.Card`):
  - `Finset.card_filter_le (s : Finset α) (p : α → Prop) [DecidablePred p]
    : (s.filter p).card ≤ s.card`
  - 用途: Phase B.1 filter サイズ評価の汎用。
- **`Finset.exists_lt_of_sum_lt`** (`Mathlib.Algebra.Order.BigOperators.Group.Finset`):
  - `Finset.exists_lt_of_sum_lt [OrderedCancelAddCommMonoid α] {s : Finset ι}
    {f g : ι → α} (Hlt : ∑ i ∈ s, f i < ∑ i ∈ s, g i) : ∃ i ∈ s, f i < g i`
  - 用途: Phase B.1 Markov inequality 対偶経路。

**プロジェクト内既存**:
- `mutualInfoOfChannel` (`Common2026/Shannon/ChannelCoding.lean:84`)
- `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` (`Common2026/Shannon/ChannelCoding.lean:129`)
- `channel_coding_achievability` (`Common2026/Shannon/ChannelCodingAchievability.lean:1605`)
- `Code.errorProbAt` / `Code.averageErrorProb` (`Common2026/Shannon/ChannelCoding.lean:204-213`)

**Mathlib gap 候補 (要新規実装)**:
- `pmfToMeasure : (α → ℝ) → Measure α` (Sanov/Csiszár で類似 utility あるか要 rg 確認)
- `Code.subcode` (Phase B.2 中核ヘルパ、本 plan で初出)
- `mutualInfoOfChannel` の Continuous (in `p`) — Sanov 経由で部分的に存在、本 plan で
  finite-alphabet 版を再構築

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 例 (起草時、未確定):
1. **Phase C scope 縮小** (起草時): `hW_pos` 完全除去は連続近似 `W_δ → W` の二重 limit
   で重く、本 plan MVP では sub-channel 切り出しで effective に処理。完全除去は D-1'
   deferred カードに記録 (`docs/moonshot-seeds.md` 更新時)。
2. **`capacity` の `ℝ`-値選択 vs `ℝ≥0∞`-値選択**: `(mutualInfoOfChannel p W).toReal` を
   取ることで `ℝ`-値 sSup を扱う。`mutualInfoOfChannel p W = ∞` の場合は `.toReal = 0` に
   縮退するが、capacity sup の値は他の有限 `p` で達成されるため影響なし。`ℝ≥0∞` 版は
   後付け可能、本 plan scope 外。
-->
