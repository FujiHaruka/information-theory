# Channel coding (Shannon) full theorem — `hW_pos` 緩和 (D-1') ムーンショット計画 🌙

(D-1' / 親 plan [`channel-coding-shannon-theorem-plan.md`](./channel-coding-shannon-theorem-plan.md) の "scope-deferred 後継"、2026-05-14 起草)

> 親 plan D-1 (`shannon_noisy_channel_coding_theorem`, `ChannelCodingShannonTheorem.lean` 918 行)
> は `hW_pos : ∀ a b, 0 < (W a).real {b}` を仮定。D-1' はこの仮定を取り除き、Cover-Thomas 7.7.1 を
> **任意の `IsMarkovKernel W` (0-prob atom を許容)** に拡張する。
>
> 経路: `W_smooth W δ a := (1-δ) • W a + δ • (uniformβ)` で full support 化、D-1 主定理を
> `W_smooth` に適用、`δ → 0⁺` 極限で error と capacity の連続性を経由して一般 W に持ち上げる。

## 進捗

- [ ] Phase 0 — Mathlib API inventory 📋
- [ ] Phase A — `Channel.smooth` 定義 + 基本性質 📋
- [ ] Phase B — `mutualInfoOfChannel` の `W` 連続性 (固定 p₀ 経由) 📋
- [ ] Phase C — 既存 D-1 を `W_smooth δ₀` に適用 + TV bound で error 差を抑制 📋
- [ ] Phase D — 主定理 `shannon_noisy_channel_coding_theorem_general` 組み立て 📋

## ゴール / Approach

### Goal (最終定理 signature)

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

親 D-1 主定理から `hW_pos` 仮定を **そのまま取り除く** 形。

### Context — D-1 主定理との関係

- 親 D-1 (`ChannelCodingShannonTheorem.lean:838`) は `hW_pos` 必須。
- `hW_pos` の用途は **唯一** 主定理本体で `channel_coding_achievability_max_error` → 既存
  `channel_coding_achievability` (`ChannelCodingAchievability.lean:1605`) に渡るのみ。
- 既存 1890 行は改変せず、`W_smooth` で full-support 化したものを既存に流す。

### Approach (4 段戦略 — smoothing + 連続性 + TV bound + 極限)

**戦略の shape**: 親 D-1 (full support W 版) を **ブラックボックス**として `W_smooth := (1-δ)W + δ·UnifChannel`
に適用、Phase B.2 で固定 `p₀` 経由で `R < capacity (W_smooth δ₀)` を確保、Phase C で
`Measure.pi` の TV 距離 tensorization (`‖pi(W_smooth δ) − pi(W)‖_TV ≤ n δ`) を構成し、
`δ → 0⁺` で error 差を線型 bound、最後に `δ_cap` を `n` 非依存に固定して二重 limit を回避。

1. **(A)** `W_smooth` の構成 + Markov 性 + 各 atom positivity (`> δ/|β|`)。
2. **(B)** MI の `W` 連続性 (3-entropy 展開 + `Real.continuous_negMulLog`、親 A.2 と同型を `W` 側に)。
   capacity の `W` 連続性は **回避**: 固定 `p₀` (`capacity_lt_implies_exists_pmf`) + MI 連続性で
   `R < capacity (W_smooth δ₀)` を直接示す。
3. **(C)** D-1 を `(W_smooth δ_cap, R, ε/2)` で call、`(N, M, c)` 取得。`δ_cap → 0` で
   `|errorProbAt(W, c, m) − errorProbAt(W_smooth δ_cap, c, m)| ≤ K · δ_cap` (TV bound 経由、
   `K` は `n` 依存だが `δ_cap` 非依存) を取り、`δ_cap` を最初から `min(δ_B, ε/(2K))` に
   調整して `ε/2 + ε/2 = ε` 未満を出す。
4. **(D)** 主定理組み立て。

**Bridge と既存資産の関係**:
- 親 D-1 主定理 `shannon_noisy_channel_coding_theorem` (`:838`) を **改変せず** 1 回 call。
- 新規ファイル: `Common2026/Shannon/ChannelCodingShannonTheoremGeneral.lean` (~200-280 行見込み)。
- 親 plan の `continuous_mutualInfoOfChannel_left` の **右 W 引数版** を新規追加。

### 規模見積

| Phase | 内容 | 行数 |
|---|---|---|
| 0 | Mathlib API inventory | 0 |
| A | `uniformMeasureβ` + `Channel.smooth W δ` + Markov 性 + `hW_pos` 派生 | 60-80 |
| B | `δ` 連続性 (MI、固定 `p₀` 経由) | 50-70 |
| C | D-1 適用 + TV bound + errorProbAt の `δ → 0` 連続性 | 60-90 |
| D | 主定理 | 30-40 |
| **合計** | | **~200-280 行** |

## Phase 0 — Mathlib API inventory

### 既存 Mathlib API (loogle 確認、2026-05-14)

- **`ProbabilityTheory.Kernel.instAddCommMonoid`**: `Kernel α β` は `AddCommMonoid`、加法は pointwise。
- **`ProbabilityTheory.Kernel.coe_add`**: `⇑(κ + η) = κ + η`。
- **`Real.continuous_negMulLog`**: 親 A.2 で使用済、Phase B でも再利用。
- **`Real.continuous_log`** + `continuous_pi`: 連続性合成の基本。

### 既存 Common2026 補題 (再利用)

- `pmfToMeasure` + `pmfToMeasure_real_singleton` + `pmfToMeasure_isProbabilityMeasure`
  (`ChannelCodingShannonTheorem.lean:54, 74, 93`).
- `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` (`ChannelCoding.lean:129`).
- `continuous_mutualInfoOfChannel_left` (`ChannelCodingShannonTheorem.lean:281`): 参考。
- `shannon_noisy_channel_coding_theorem` (`:838`): Phase C で黒箱 call。
- `capacity_bddAbove` (`:115`) + `capacity_lt_implies_exists_pmf` (`:327`).
- `Code.errorProbAt` (`ChannelCoding.lean:204`).

### D-1' で新規

- `uniformMeasureβ : Measure β` (`(Fintype.card β)⁻¹ • ∑ b, Measure.dirac b`)。
- `Channel.smooth W δ : Channel α β` + Markov 性 + `smooth_pos` + `smooth_zero`。
- `continuous_mutualInfoOfChannel_right_smooth_at_zero`: `δ ↦ MI(p, W_smooth δ).toReal` が 0 で連続。
- `errorProbAt_smooth_TV_bound`: `|errorProbAt(W_smooth δ, c, m) − errorProbAt(W, c, m)| ≤ n·δ` の type 不等式。

### Mathlib gap 候補

- `klDiv` の `W` 連続性 → Mathlib 不在、3-entropy 経由で迂回。
- `capacity W` の `W` 連続性 → Mathlib 不在、固定 `p₀` 経由で迂回。

## Phase A — `Channel.smooth` 定義 + 基本性質 📋

### A.1 — `uniformMeasureβ : Measure β`

- [ ] **A.1.1** Helper:
  ```lean
  noncomputable def uniformMeasureβ : Measure β :=
    (Fintype.card β : ℝ≥0∞)⁻¹ • ∑ b : β, Measure.dirac b
  ```
- [ ] **A.1.2** `uniformMeasureβ_isProbabilityMeasure`.
- [ ] **A.1.3** `uniformMeasureβ_real_singleton`: `= (Fintype.card β)⁻¹` (`> 0` since `[Nonempty β]`).

### A.2 — `Channel.smooth W δ`

- [ ] **A.2.1** 定義:
  ```lean
  noncomputable def Channel.smooth (W : Channel α β) (δ : ℝ) : Channel α β :=
    { toFun := fun a => ENNReal.ofReal (1 - δ) • W a + ENNReal.ofReal δ • uniformMeasureβ
      measurable' := ... }
  ```
  `Fintype β` + discrete `MeasurableSpace.discrete` で measurability 自動。
- [ ] **A.2.2** `Channel.smooth_apply` (`rfl` 形).
- [ ] **A.2.3** `Channel.smooth_zero`: `Channel.smooth W 0 = W`.

### A.3 — Markov 性 + 各 atom positivity

- [ ] **A.3.1** `Channel.smooth_isMarkovKernel` for `δ ∈ [0,1]`.
- [ ] **A.3.2** `Channel.smooth_real_singleton`:
  `(W_smooth δ a).real {b} = (1-δ) * (W a).real {b} + δ * (|β|)⁻¹` for `δ ∈ [0,1]`.
- [ ] **A.3.3** `Channel.smooth_pos`: `δ ∈ (0,1] → ∀ a b, 0 < (W_smooth δ a).real {b}`.

## Phase B — MI 連続性 (固定 `p₀` 経由) 📋

### B.1 — MI の `δ` 連続性

- [ ] **B.1.1** `mutualInfoOfChannel_toReal_smooth_eq`:
  3-entropy 展開 + A.3.2 で `(W_smooth δ a).real {b}` を `(1-δ)(W a).real{b} + δ/|β|` 代入形に。
- [ ] **B.1.2** `continuous_mutualInfoOfChannel_right_smooth`:
  ```lean
  Continuous (fun δ : ℝ => (mutualInfoOfChannel (pmfToMeasure p) (Channel.smooth W δ)).toReal)
  ```
  on `[0, 1]`. 各 `negMulLog` 項が連続、`continuous_finsetSum`.

### B.2 — `R < capacity W` から `R < capacity (W_smooth δ₀)`

- [ ] **B.2.1** `exists_smooth_capacity_gt`:
  ```lean
  R < capacity W → ∃ δ₀ ∈ Set.Ioc (0:ℝ) 1, R < capacity (Channel.smooth W δ₀)
  ```
  経路: `capacity_lt_implies_exists_pmf hR` で `p₀ ∈ stdSimplex` を取り
  `R < (mutualInfoOfChannel (pmfToMeasure p₀) W).toReal ≤ capacity W` を得る。
  `R₁ := (R + (mutualInfoOfChannel _ W).toReal) / 2` を mid-point に取り、B.1.2 から
  `eventually (R₁ < MI(p₀; W_smooth δ))` を `δ ∈ 𝓝[Ioc 0 1] 0` で取り出し、
  `MI(p₀; W_smooth δ₀) ≤ capacity (W_smooth δ₀)` で結論。

**(注)**: B.2 は `R < capacity W` から **存在形** で `δ₀ > 0` を取るだけ、capacity の `W` 連続性
(sup-of-cont) 全体は不要。

## Phase C — D-1 適用 + TV bound 📋

### C.1 — D-1 適用

- [ ] **C.1.1** Phase B.2.1 で `δ₀ ∈ (0, 1]` を取り `R < capacity (W_smooth δ₀)`.
- [ ] **C.1.2** `Channel.smooth_isMarkovKernel hδ₀` を instance として供給。
- [ ] **C.1.3** D-1 `shannon_noisy_channel_coding_theorem (W_smooth δ₀)` を call、
  `hW_pos := Channel.smooth_pos hδ₀_pos hδ₀_le_1`、`ε := ε/2` 目標で
  `(N, M, hM_lb, c, ∀m, (c.errorProbAt (W_smooth δ₀) m).toReal < ε/2)` 取得。

### C.2 — TV bound

- [ ] **C.2.1** `Channel.smooth_TV_bound`:
  `∀ a, (∑ b, |(W a).real {b} − (W_smooth δ a).real {b}|) ≤ 2 * δ` for `δ ∈ [0, 1]`.
  (A.3.2 から `|(W a).real {b} − (W_smooth δ a).real {b}| = δ · |(W a).real {b} − 1/|β||`、
  `∑_b ≤ 2δ` (TV 上界の有限和形).)
- [ ] **C.2.2** `Measure.pi_real_event_diff_le`:
  有限離散 `(α_i)_i : Fin n → β` で
  ```
  |(Measure.pi μ_i) E − (Measure.pi μ'_i) E|
    ≤ ∑ i, (∑ b, |(μ_i).real {b} − (μ'_i).real {b}|)
  ```
  (finite enumeration `E ⊆ Fin n → β` で各 `∏ i, μ_i.real {y i} − ∏ i, μ'_i.real {y i}` の
  telescoping、`|∏ a_i − ∏ b_i| ≤ ∑ |a_i − b_i|` (各因子 ∈ [0,1]) を `∑_{y ∈ E}` で合算 →
  独立 fibre 構造で各 `i` の TV に reduce)。
  **注**: 強い形 (`|β|^n` 因子なし) は `E ⊆ Fin n → β` 全体に対する telescope で出る。
- [ ] **C.2.3** `errorProbAt_smooth_TV`:
  `|((c.errorProbAt (W_smooth δ) m)).toReal − ((c.errorProbAt W m)).toReal| ≤ 2 * n * δ`
  for `δ ∈ [0, 1]`. (C.2.2 を `c.errorEvent m ⊆ Fin n → β` に適用、各 `i` で C.2.1.)

### C.3 — `δ₀` の取り直し

- [ ] **C.3.1** Phase D で `δ_cap := min(δ_B, ε / (4 * (n + 1)))` (各 `n` で取り直し可能だが、
  実際は D-1 の `N` を取った後に `δ_cap` を `n` ごとに **追加で** 小さく取る; D-1 の `N` 構成は
  `(I(p₀; W_smooth δ_cap) − R) / 6` 経路の rate slack のみに依存、`δ_cap → 0` で
  `I(p₀; W_smooth δ_cap) → I(p₀; W)` 一定値、よって `N(δ_cap)` は bounded、`δ_cap → 0` で発散しない)。

## Phase D — 主定理 📋

### D.1 — 主定理 statement

```lean
theorem shannon_noisy_channel_coding_theorem_general
    (W : Channel α β) [IsMarkovKernel W]
    {R : ℝ} (hR_pos : 0 < R) (hR : R < capacity W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∃ M (_h : Nat.ceil (Real.exp (n*R)) ≤ M) (c : Code M n α β),
      ∀ m, (c.errorProbAt W m).toReal < ε
```

### D.2 — 証明合成

- [ ] **D.2.1** Step 1: B.2.1 で `δ_B ∈ (0, 1]` を取り `R < capacity (W_smooth δ_B)`.
- [ ] **D.2.2** Step 2: D-1 を `W_smooth δ_B` に対し `ε/2` 目標で call、`N_B, M, c` の存在形を得る。
- [ ] **D.2.3** Step 3: 任意 `n ≥ N_B` で `c` を取り、C.2.3 から
  `(c.errorProbAt W m).toReal ≤ (c.errorProbAt (W_smooth δ_B) m).toReal + 2 n δ_B`.
- [ ] **D.2.4** Step 4: `δ_B` を `δ_B' := min(δ_B, ε/(4(n+1)))` で取り直すと、`R < capacity (W_smooth δ_B')`
  を維持しつつ `2 n δ_B' ≤ ε/2`、`(c'.errorProbAt W m).toReal < ε/2 + ε/2 = ε`.
  **しかし** `δ_B'` は `n` 依存、`c'` も `n` 依存。
  **解決**: `N` 自体は `δ_B` (≡ `R, I(p₀; W)`) のみに依存し `δ_B'` 取り直しで増えない
  ことを確認できれば、`n` ごとに別の `c_n` を作る → 主定理は `∃ N, ∀ n ≥ N, ∃ c_n, ...` 形なので
  `c_n` の `n` 依存は問題なし。**この経路で完走**。
- [ ] **D.2.5** 仕上げ: `N := N(δ_B)` を取り、各 `n ≥ N` で `δ_n := min(δ_B, ε/(4(n+1)))` を選び
  D-1 を `W_smooth δ_n` で再 call、`(M_n, c_n)` を得て主定理達成。
  **(注)**: 各 `n` で D-1 を再 call すると `N(δ_n)` が `n` ごとに異なる可能性。
  `δ_n ≤ δ_B` だが `N(δ_n) ≥ N(δ_B)` とは限らない (`I(p₀; W_smooth δ_n)` が `δ_n` で連続なので
  `δ_n → 0⁺` で → `I(p₀; W) > R` 一定値、`δ_n` 増加に対し monotonic な rate slack を持つ
  わけではないが、十分小 `δ_n` で slack はほぼ一定)。
  **安全な実装**: `N := sup_{δ ∈ (0, δ_B]} N(δ_n)` だが、bounded 性は連続性から。Phase 0
  で親 D-1 の `N` 構成を再読し、`N(δ)` の monotone 性または bound を確認 → なければ
  Phase C.3.1 の `δ_cap := min(δ_B, ε/(4 K_max))` で `K_max := 2 N_max` (= upper bound on n
  necessary, e.g., `N_max := N(δ_B/2)` を一度取って use both) で対応。
  **判断 (起草時)**: 親 D-1 の `N` 構成を確認した上で、最も単純な経路 (`δ_cap := min(δ_B, ε/(4 N_B))`
  で全 `n ≥ N_B` 共通の `δ_cap`) を採用予定。

## Risks / Unknowns

### R1 — 二重 limit 順序

`(δ, n)` 二重 limit は TV bound (C.2.3, `K = 2n`) で `K` を線型に落とし、`δ_cap` を `n` 共通に
固定する経路で **回避見込み**。親 D-1 の `N(δ)` の `δ` 依存性を確認すれば確定。

### R2 — `klDiv` の `W` 連続性 (Mathlib gap)

不在のため Phase B.1 で 3-entropy 展開経由 (親 A.2 と同型)。~50-70 行。

### R3 — `capacity W` の `W` 連続性 (Mathlib gap)

不在のため Phase B.2 で固定 `p₀` 経由に縮小、sup-of-cont 全体は構成しない。

### R4 — 親 D-1 の `N(δ)` 依存性

親 D-1 内部の `N` 構成を Phase 0 で再読、`δ` 経由の依存性を bound 化する必要。

### R5 — `Channel.smooth` の measurability

`Fintype β` + `MeasurableSpace β = ⊤` (discrete) で trivial、grep で `Kernel.add_measurable`
系の有無を確認。

## Mathlib inventory 必要箇所まとめ

| 必要性 | API | 状態 |
|---|---|---|
| MUST | `Kernel.instAddCommMonoid` (pointwise add) | ✓ Mathlib |
| MUST | `Real.continuous_negMulLog` | ✓ Mathlib |
| MUST | `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ` | ✓ Common2026 |
| MUST | `Measure.pi` 線型差展開 (TV bound) | 手で構成、~30-50 行 |
| SHOULD | `klDiv` の `W` 連続性 | ✗ 3-entropy 経由で迂回 |
| SHOULD | `capacity W` の `W` 連続性 (sup-of-cont) | ✗ 固定 `p₀` 経由で迂回 |

## 判断ログ

1. **Phase B 経路選択 (起草時)**: capacity の `W` 連続性 (sup-of-cont) は Mathlib 不在で
   本 plan に不要 (B.2.1 のみ必要)。固定 `p₀` 経由で迂回。

2. **TV bound 経路採用 (起草時)**: Phase C の `(δ, n)` 二重 limit は TV 距離 tensorization
   (`‖pi(W_smooth δ) − pi(W)‖_TV ≤ n δ`) で `K = n` 線型に落とすことで回避。
   `|β|^n` 因子を避けるための採用。

3. **D-1 黒箱化**: 親 1890 行 + 918 行に触らず、新規 ~200-280 行ファイルで完結。

4. **Phase C.2.2 TV bound 経路修正 (2026-05-14 実装時)**: `Measure.pi` 上の hybrid telescoping
   TV bound を `Finset.filter`-based partition で展開する初期方針は煩雑のため、`Fin.cons`-bijection
   + 直接 induction on `n` に切り替え。各 step で `Equiv.sum_comp` + `Finset.sum_product` +
   `Fintype.prod_sum` で sum-factorize する。新 lemma `sum_prod_diff_abs_le_aux` (≈80 行) +
   `Measure_pi_real_event_diff_le` (≈50 行) で **tight bound `2 n δ`** を達成。

5. **Phase D 残課題 (2026-05-14 実装時)**: 最終 step `2 n δ_B < ε/2` の synchronization が
   `δ_B` を `n` ごとに取り直す必要があり、`δ_n := min(δ_B, ε/(8(n+1)))` で各 `n` に対し
   親 D-1 を再 call する経路は parent D-1 の `N(δ_n)` の **δ-uniform 上界** を必要とする。
   この uniform 上界は MI の δ 連続性 (Phase B.1.2) + `(I(p₀; W) - R) > 0` slack で
   理論的には bounded だが、parent D-1 の `N` 構成は内部で rate slack と ε に依存するため、
   外から取り出すには parent の証明への踏み込みが必要。本 D-1' MVP は Phase D 主定理に **1 個の
   documented sorry** を残し、Phase A-C の rigorous 完成 (0 sorry) を確保する。

## 参考

- 親 plan: [`channel-coding-shannon-theorem-plan.md`](./channel-coding-shannon-theorem-plan.md)
- 親 D-1 実装: `Common2026/Shannon/ChannelCodingShannonTheorem.lean` (918 行)
- 既存 achievability: `Common2026/Shannon/ChannelCodingAchievability.lean:1605`
- moonshot 雛形: [`docs/moonshot-plan-template.md`](../moonshot-plan-template.md)
