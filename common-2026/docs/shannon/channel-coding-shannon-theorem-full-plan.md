# D-1'' Phase D parent surgery — `h_passthrough` discharge

`Common2026/Shannon/ChannelCodingShannonTheoremFull.lean:52` の hypothesis pass-through 形 (`h_passthrough` 仮定で smoothing infrastructure を glue するだけ) を内部 discharge し、**`hW_pos` 完全除去**の Shannon noisy channel coding theorem general 形を publish。

親 plan: [D-1' Phase A-C plan](channel-coding-shannon-theorem-general-plan.md)、D-1 (full support 仮定下完全形): [D-1 plan](channel-coding-shannon-theorem-plan.md)。

---

## 進捗

- [ ] Phase D.0 — `exists_smooth_capacity_gt_uniform` (δ-uniform 化)
- [ ] Phase D.0' — `pSmooth` 統合 + (p, δ) joint continuity
- [ ] Phase D.1 — `pmfLogVariance` δ-asymptotic bound (per-axis)
- [ ] Phase D.2 — parent body inline copy with closed-form N export
- [ ] Phase D.3 — `δ_n := min(δ_B, ε/(8(n+1)))` choice + index assemble
- [ ] Phase D.4 — 主定理 + `ChannelCodingShannonTheoremFull.lean` の `h_passthrough` discharge

---

## ゴール

```lean
theorem shannon_noisy_channel_coding_theorem_general
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε
```

(`hW_pos` 完全除去版、D-1 の `hW_pos` 仮定を smoothing で消す)

`h_passthrough` の shape (現行 MVP):
```
∃ N : ℕ, ∀ n, N ≤ n →
  ∃ (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1),
    2 * (n : ℝ) * δ < ε / 2 ∧
    ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
      (c : Code M n α β),
      ∀ m, (c.errorProbAt (Channel.smooth W δ) m).toReal < ε / 2
```

---

## Approach

**Two-layer smoothing + n-vs-δ asymptotic comparison**.

1. **Two-layer smoothing**:
   - 入力側 `p_full := pSmooth p₀ δ_p` (`δ_p` 固定、n-独立) で `hp_pos`。
   - channel 側 `Channel.smooth W δ_n` (`δ_n → 0` as `n → ∞`) で `hW_pos`。
   - 入力 smoothing は parent D-1 `shannon_noisy_channel_coding_theorem` の手法を reuse、channel smoothing は D-1' Phase A の `Channel.smooth` を使用。

2. **`δ_n := min(δ_B, ε/(8(n+1)))`**:
   - `2 n δ_n ≤ ε/4 < ε/2` (TV bound condition、`errorProbAt_smooth_TV` で 2nδ_n だけ shift)。
   - `δ_n ≤ δ_B` (Phase D.0 で `R < I(p_full; W_smooth δ)` for δ ∈ (0, δ_B] を確保した uniform 領域)。

3. **N(δ_n) = O((log n)²) ≪ n**:
   - parent body refactor (2026-05-15 very late+1) で N₁/N₂ は既に closed-form (`jointlyTypicalSet_prob_ge_of_rate` + `channelCoding_E2_lt_of_rate`)。
   - N₂(δ) ≤ N₂_const (δ-uniform、`g(δ) := (I-R)/2 ≥ g_min`)。
   - N₁(δ) ≲ V_max(δ) / (η ε(δ)²) where V_max(δ) ≲ (log(|β|/δ))² (`p_full` で `q_δ(b) ≥ δ/|β|` etc.)。
   - `δ_n = ε/(8(n+1))` ⇒ `log(1/δ_n) ≤ log(8/ε) + log(n+1)`、よって `V_max(δ_n) ≲ (log(n+1))²`。
   - `(log n)²/n → 0` (Mathlib `Real.tendsto_log_div_pow_atTop` 派生) で `∃ N₀, ∀ n ≥ N₀, N₁(δ_n) ≤ n`。

4. **Parent achievability の inline copy** (Phase D.2):
   - parent body 160 行 (`ChannelCodingAchievability.lean:1607-1797`) を copy + closed-form N₁(δ), N₂(δ) を signature に expose。これにより `(p_full, W_smooth δ_n)` で δ ごとに parent body を再呼出しできる。
   - parent body は既に `jointlyTypicalSet_prob_ge_of_rate` + `channelCoding_E2_lt_of_rate` 直接呼出し形なので、追加 surgery 不要。

5. **Final assembly** (Phase D.4):
   - Phase D.3 で `δ_n`, `N₀` 取得。
   - Phase D.2 を call して codebook 取得 (average error < ε/2)。
   - `channel_coding_achievability_max_error` (D-1 既存) で average → max 変換 (rate 損失 → ε/4 etc.、δ_n に対しても n-uniform に動作)。
   - `errorProbAt_smooth_TV` で `errorProbAt W m < errorProbAt(W_smooth δ_n) m + 2nδ_n < ε/2 + ε/2 = ε`。

---

## Phase 分解

### Phase D.0 — `exists_smooth_capacity_gt_uniform`

既存 `exists_smooth_capacity_gt` (`ChannelCodingShannonTheoremGeneral.lean:305-349`) を δ-uniform 化:

```lean
private lemma exists_smooth_capacity_gt_uniform
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR : R < capacity W) :
    ∃ p₀ ∈ stdSimplex ℝ α, ∃ δ_B : ℝ, 0 < δ_B ∧ δ_B ≤ 1 ∧
      ∃ R₁ : ℝ, R < R₁ ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ_B,
        R₁ < (mutualInfoOfChannel (pmfToMeasure p₀) (Channel.smooth W δ)).toReal
```

**経路**: 既存 proof の `Metric.mem_nhdsWithin_iff` で抽出した `η` を用い、`δ_B := min(η/2, 1)` で全 δ ∈ (0, δ_B] に条件適用。

**行数**: ~40-60 行。

### Phase D.0' — `pSmooth` integration + joint continuity

```lean
private lemma pSmooth_pmf_smooth_capacity_gt
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR : R < capacity W) :
    ∃ p₀ ∈ stdSimplex ℝ α, ∃ δ_p δ_B : ℝ,
      0 < δ_p ∧ δ_p ≤ 1 ∧ 0 < δ_B ∧ δ_B ≤ 1 ∧
      ∃ I_lb : ℝ, R < I_lb ∧
      (∀ a, 0 < pSmooth p₀ δ_p a) ∧
      pSmooth p₀ δ_p ∈ stdSimplex ℝ α ∧
      ∀ δ ∈ Set.Ioc (0 : ℝ) δ_B,
        I_lb < (mutualInfoOfChannel (pmfToMeasure (pSmooth p₀ δ_p)) (Channel.smooth W δ)).toReal
```

**証明経路**: `mutualInfoOfChannel` の `(p, δ)`-joint continuity を構成 (3-entropy 展開、~50 行)。`(pSmooth p₀ 0, 0) = (p₀, W)` 近傍で `R + κ ≤ I` トラップを取り、`δ_p` 小 → `δ_B` 小の二段適用。

**新規補題**: `mutualInfoOfChannel_toReal_smooth_joint_continuous` (joint in p, δ on stdSimplex × Icc 0 1)、~50 行。

**Mathlib gap**: `Real.continuous_negMulLog` を `p, δ` 同時連続合成。既存補題 `continuous_mutualInfoOfChannel_right_smooth` (δ-連続) を `p` 軸にも展開。

**行数**: ~80-130 行 (joint continuity 込み)。

### Phase D.1 — Variance δ-asymptotic bound

```lean
-- D.1.1: pmfLog Y bound for smooth channel.
private lemma pmfLog_iidYs_bound_smooth
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (y : β) :
    |pmfLog (iidAmbientMeasure p (Channel.smooth W δ)) iidYs y|
      ≤ Real.log (Fintype.card β / δ)

-- D.1.5: variance bound.
private lemma pmfLogVariance_iidYs_le_smooth
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    pmfLogVariance (iidAmbientMeasure p (Channel.smooth W δ)) iidYs
      ≤ (Real.log (Fintype.card β / δ))^2

-- D.1.7: analysis.
private lemma exists_N_log_sq_le_n
    (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      C * (Real.log (8 * (n + 1) / ε))^2 + 1 ≤ n
```

**証明経路**: 
- D.1.1: `q_δ(b) := (outputDistribution p (W_smooth δ)).real {b} ≥ δ/|β|`、`|log q_δ(b)| ≤ log(|β|/δ)`.
- D.1.5: `variance_le_sq_of_bounded` (Mathlib `Probability/Moments/Variance.lean:499`) を `|X| ≤ B` で適用。
- D.1.7: `Real.tendsto_log_div_pow_atTop` を `log(n+1)/√n → 0` etc. で合成。

**行数**: ~150-250 行。

### Phase D.2 — Parent achievability inline copy + closed-form N

```lean
-- 新規 file `ChannelCodingShannonTheoremFullDischarge.lean` 内 (or extension).
-- Parent body コピー + closed-form N₁(δ), N₂(δ) signature 公開。
private theorem channel_coding_achievability_smooth_closed_form
    (W : Channel α β) [IsMarkovKernel W]
    (p₀ : α → ℝ) (hp₀_mem : p₀ ∈ stdSimplex ℝ α)
    (δ_p : ℝ) (hδ_p_pos : 0 < δ_p) (hδ_p_le : δ_p ≤ 1)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    {R : ℝ} (hR_pos : 0 < R) {I_lb : ℝ}
    (hR_lt_I_lb : R < I_lb)
    (hMI : I_lb < (mutualInfoOfChannel
      (pmfToMeasure (pSmooth p₀ δ_p)) (Channel.smooth W δ)).toReal)
    {ε' : ℝ} (hε' : 0 < ε') :
    -- closed-form N
    let N := ... -- ⌈max C₁·(log(|β|/δ))² C₂·(log(|α||β|/(δ_p·δ)))² C₃·(-log ε')⌉ + 1
    ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        (c.averageErrorProb (Channel.smooth W δ)).toReal < ε'
```

**経路**: `channel_coding_achievability` (`ChannelCodingAchievability.lean:1607-1797`) を copy + adapt:
- `p := pmfToMeasure (pSmooth p₀ δ_p)`, `W := Channel.smooth W δ` で instantiate。
- `hp_pos`: `pSmooth_pos` で構成 (`pSmooth p₀ δ_p a ≥ δ_p / |α| > 0`)。
- `hW_pos`: `Channel.smooth_real_singleton_pos` で `(W_smooth δ a).real {b} ≥ δ/|β| > 0`。
- `hR`: hypothesis から `R < I_lb < I(...)`.
- Step 4-5: AEPRate Step 3 Phase A を call、N₁ を closed-form 化。
- Step 6-7: AEPRate Step 2 を call、N₂ を closed-form 化。
- Step 8: codebook assembly (parent verbatim copy)。

**行数**: ~150-200 行 (parent body コピー + minor adapt)。

### Phase D.3 — `δ_n` choice + N assemble

```lean
private noncomputable def deltaN (δ_B ε : ℝ) (n : ℕ) : ℝ :=
  min δ_B (ε / (8 * ((n : ℝ) + 1)))

private lemma deltaN_pos {δ_B ε : ℝ} (hδ_B : 0 < δ_B) (hε : 0 < ε) (n : ℕ) :
    0 < deltaN δ_B ε n := ...

private lemma deltaN_TV_lt {δ_B ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    2 * (n : ℝ) * deltaN δ_B ε n < ε / 2 := ...

private lemma exists_N_for_smooth_achievability
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) {ε : ℝ} (hε : 0 < ε)
    (p₀ : α → ℝ) ... (δ_p δ_B I_lb : ℝ) ... :
    ∃ N : ℕ, ∀ n, N ≤ n →
      let δ_n := deltaN δ_B (ε / 2) n  -- ε/2 で TV bound, ε/4 total
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt (Channel.smooth W δ_n) m).toReal < ε / 2
```

**経路**: Phase D.1.7 (`(log n)²/n → 0`) で `∃ N₀, N(δ_n) ≤ n`、Phase D.2 と average→max wrapper で組み立て。

**行数**: ~80-120 行。

### Phase D.4 — 主定理 + `ChannelCodingShannonTheoremFull.lean` 更新

```lean
theorem shannon_noisy_channel_coding_theorem_general_discharge
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : Code M n α β),
        ∀ m, (c.errorProbAt W m).toReal < ε
```

**経路**: Phase D.4 で `h_passthrough_of_capacity_lt` を構成 → 既存 `shannon_noisy_channel_coding_theorem_general` (Full file の MVP) に渡して discharge。または `ChannelCodingShannonTheoremFull.lean` を直接更新して `h_passthrough` 削除。

**行数**: ~40-80 行 + Full file 更新 -5 行。

---

## 規模見積

| Phase | 内容 | 行数 |
|---|---|---|
| D.0 | uniform smooth capacity gt | 40-60 |
| D.0' | pSmooth + joint continuity | 80-130 |
| D.1 | variance δ-asymptotic bounds (4-7 補題) | 150-250 |
| D.2 | parent body inline copy + closed-form N | 150-200 |
| D.3 | δ_n + N assemble | 80-120 |
| D.4 | 主定理 + discharge | 40-80 |
| **合計** | | **~540-840 行** |

新規 file: `Common2026/Shannon/ChannelCodingShannonTheoremFullDischarge.lean` (~600 行想定)。

---

## Mathlib gap check

| API | 状態 | 用途 |
|---|---|---|
| `variance_le_sq_of_bounded` (`Probability/Moments/Variance.lean:499`) | ✓ Mathlib | Phase D.1 variance bound |
| `Real.tendsto_log_div_pow_atTop` (`(log n)/n → 0`) | ✓ Mathlib 派生 | Phase D.1.7 |
| `(p, δ)`-joint continuity of `mutualInfoOfChannel` | ✗ 新規 | Phase D.0' joint continuity |
| `pSmooth`, `Channel.smooth` infrastructure | ✓ Common2026 | parent D-1 + D-1' Phase A |
| `errorProbAt_smooth_TV` | ✓ Common2026 (D-1' Phase C) | Phase D.4 glue |
| `channel_coding_achievability_max_error` | ✓ Common2026 (D-1) | average → max |

**新規 Mathlib gap は 1 つだけ** (joint continuity)、~50 行で構成。

---

## 判断ログ

1. **parent body コピー必須**: 既存 `channel_coding_achievability` は `∃ N` 存在形を返すため、N が existential で外から見えない。`(p_full, W_smooth δ_n)` で δ ごとに再呼出しすると `N` も δ ごとに別個 existential、循環 (δ_n が n に依存する以上 N_n も n に依存して取れない)。よって closed-form N(δ) を signature に export する形に inline copy (Phase D.2)。

2. **入力側 smoothing (Phase D.0')**: `pSmooth p₀ δ_p` で `hp_pos` を vacuous 化。parent D-1 (`ChannelCodingShannonTheorem.lean:826-918`) と同じトリック、コードは public 化または再定義。

3. **δ_n = ε/(8(n+1))**: TV bound `2nδ_n < ε/4 < ε/2` を簡単に達成し、`log(1/δ_n) = log(8/ε) + log(n+1)` で V_max(δ_n) ≲ (log n)² となる polynomial decay の最弱形。exponential decay `δ_n = exp(-√n)` は V_max ~ n になり破綻。

4. **`(log n)² ≤ n` eventually**: `Real.log` の polynomial-vs-log growth gap で eventually 成立、Mathlib に直接 API は無いが `Real.tendsto_log_div_pow_atTop` から派生可。

5. **代替戦略 (撤退)**: parent `channel_coding_achievability` 自身を `hp_pos / hW_pos` 両方緩和に改造する案は `pmfLogVariance` の subset support 形 ~300 行 + Phase E `per_codeword_no_match` の formulation 影響と重く、本計画は採用しない。

6. **D-1'' Phase B との関係**: 当初 moonshot-seeds.md (`channel-coding-achievability-closed-form-plan.md`) で想定された「Phase B 独立 publish」は parent body refactor (2026-05-15 very late+1) で内部 closed-form 化が達成済み、独立 publish の必要性は薄い。Phase B は Phase D.2 (parent body inline copy) に統合。

---

## Critical Files for Implementation

- `Common2026/Shannon/ChannelCodingShannonTheoremFull.lean` (D-1'' MVP、Phase D.4 で discharge)
- `Common2026/Shannon/ChannelCodingShannonTheoremGeneral.lean` (Phase A-C + 拡張する Phase D.0)
- `Common2026/Shannon/ChannelCodingAchievability.lean:1607-1797` (parent body コピー source)
- `Common2026/Shannon/AEPRate.lean` (closed-form N₁/N₂ 部品)
- `Common2026/Shannon/ChannelCodingShannonTheorem.lean` (D-1 `_max_error` wrapper + `pSmooth`)
- 新規: `Common2026/Shannon/ChannelCodingShannonTheoremFullDischarge.lean`
