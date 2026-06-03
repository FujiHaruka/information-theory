# Strong Stein — Mathlib + 既存 inventory

(B-4 / 2026-05-12)

## 経路選定の調査結果

### A. Information spectrum (Han-Verdú)

- `rg -rn "InformationSpectrum|HanVerdu" .lake/packages/mathlib/Mathlib/` — **0 件**。
- `loogle "InformationSpectrum"` — **unknown identifier**。
- 結論: Mathlib に存在せず、本シードでは構築しない (推定 4-6 週、別シード化)。

### B. Pinsker 経由 (B-5 で publish 済の `tvNorm_le_sqrt_klDiv`)

- `InformationTheory.Shannon.Pinsker.tvNorm_le_sqrt_klDiv` (Pinsker.lean:118) — 弱形
  `tvNorm P Q ≤ √(klDiv P Q).toReal` (定数 1)。
- 評価: TV/KL の翻訳でしかなく、現行 converse の `Pn(s) * (-log Qn s) ≥ (1-ε) * (-log Qn s)`
  の DPI 経由の `1/(1-ε)` factor を解消しない。**却下**。

### C. LLR typicality (採用)

- 既存 plumbing が完備:
  - `InformationTheory.Shannon.Stein.stein_inProbability` (Stein.lean:213) — WLLN on LLR。
  - `InformationTheory.Shannon.Stein.steinTypicalSet` (Stein.lean:257) — `{ x | |S/n - K| < δ }`。
  - `InformationTheory.Shannon.Stein.steinTypicalSet_P_prob_tendsto_one` (Stein.lean:275) —
    `P^n(T_n^δ) → 1`。
  - `InformationTheory.Shannon.Stein.steinTypicalSet_Q_prob_le` (Stein.lean:341) —
    `Q^n(T_n^δ) ≤ exp(-n(K-δ))` (achievability 側、point-wise LLR 下側を使用)。
- 新規構築:
  - **Q-side lower bound (symmetric)**: LLR 上側 `S/n < K + δ` を使い、
    `Q^n(x) ≥ exp(-n(K+δ)) · P^n(x)` per-point + 集約。
- 採用。

## Mathlib lemmas — 直接利用

### Tendsto / liminf / limsup の橋渡し

**`tendsto_of_le_liminf_of_limsup_le`**
- file:line: `Mathlib/Topology/Order/LiminfLimsup.lean:306`
- 型クラス前提: `[ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]`
  (`ℝ` で自動充足)
- シグネチャ:
  ```lean
  theorem tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β → α} {a : α}
      (hinf : a ≤ liminf u f) (hsup : limsup u f ≤ a)
      (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
      (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
      Tendsto u f (𝓝 a)
  ```
- 結論形: `Tendsto u f (𝓝 a)`。
- 用途: Phase C 主定理で `K ≤ liminf` (既存) と `limsup ≤ K` (新規) を結合。

### Real.log / Real.exp の単調性

- `Real.log_le_log_iff` / `Real.exp_lt_exp` 等は標準。既存 Stein で多用。

### 集合論 `s ∩ T = T \ (sᶜ ∩ T)` 系

- `Set.diff_eq` / `Set.inter_compl_self` / `measure_diff_eq` 等の標準 plumbing。

### `Filter.le_liminf_of_le` / `Filter.limsup_le_of_le`

- file:line: `Mathlib/Order/LiminfLimsup.lean`
- 既存 `stein_lemma` で使用済 (Stein.lean:1473)。

## 既存 Stein.lean からの参照リスト

すべて `InformationTheory.Shannon` namespace、`InformationTheory/Shannon/Stein.lean`:

| 補題 | 行 | 用途 |
|------|----|------|
| `llrPmf P Q : α → ℝ` | 53 | LLR pointwise |
| `steinTypicalSet P Q n δ` | 257 | `{x | |S/n - K| < δ}` |
| `mem_steinTypicalSet_iff` | 262 | unfold |
| `measurableSet_steinTypicalSet` | 268 | measurability |
| `steinTypicalSet_P_prob_tendsto_one` | 275 | P^n(T) → 1 |
| `steinTypicalSet_Q_prob_le` | 341 | Q-side upper bound (LLR 下側) **本シードの双対形を新規** |
| `stein_achievability` | 488 | 既存 achievability、Phase C で再利用 |
| `steinBetaSet` / `steinOptimalBeta` | 1139-1148 | 主定理 LHS |
| `steinOptimalBeta_pos` | 1275 | log 安全に取れる |
| `steinOptimalBeta_log_ge_of_achievability` | 1314 | liminf ≥ K の入力 |
| `stein_lemma` (sandwich) | 1390 | 既存 K ≤ liminf / limsup ≤ K/(1-ε) |

## 新規補題の必要性

1. **`steinTypicalSet_Q_prob_ge`** (Phase A): `Q^n(T_n^δ) ≥ exp(-n(K+δ)) · P^n(T_n^δ)`。
   - `steinTypicalSet_Q_prob_le` (Stein.lean:341) の **構造を symmetric にコピー**。
   - 違いは:
     - 既存: `K - δ < S/n` を使う → `exp(-(∑ llrPmf)) < exp(-n(K-δ))` (strict)。
     - 新規: `S/n < K + δ` を使う → `exp(-n(K+δ)) < exp(-(∑ llrPmf))`。
   - 集約方向: 既存は `Q^n(T) ≤ exp(-n(K-δ)) · P^n(T) ≤ exp(-n(K-δ)) · 1`。
   - 新規は `Q^n(T) ≥ exp(-n(K+δ)) · P^n(T)`。

2. **`steinAlphaTest_Q_prob_ge`** (Phase B): 任意 α-level test の Q-prob lower bound。
   - 入力: `s` measurable, `P^n(sᶜ) ≤ ε`.
   - 結論: `Q^n(s) ≥ exp(-n(K+δ)) · (P^n(T_n^δ) - ε)`.
   - 補助補題: `s ∩ T_n^δ` の P-測度 lower bound (`P^n(T) - ε`)、`s ∩ T ⊆ T` で
     per-point Q^n ≥ exp(-n(K+δ)) · P^n を流用、`Q^n(s) ≥ Q^n(s ∩ T)`。

3. **`stein_strong_lemma`** (Phase C): `Tendsto → K`。
   - 既存 `stein_lemma` の `liminf ≥ K` をそのまま流用 + 新 `limsup ≤ K`。
   - `tendsto_of_le_liminf_of_limsup_le` を最終形。

## 規模見積

| Phase | 推定行数 | 内訳 |
|-------|----------|------|
| A | 150 | `steinTypicalSet_Q_prob_ge` (per-point + sum) |
| B | 200 | `steinAlphaTest_Q_prob_ge` + `steinOptimalBeta_log_le_of_strong_converse` |
| C | 100 | `stein_strong_lemma` |
| **合計** | **~450** | 新規 `StrongStein.lean` |

既存 `Stein.lean` 改変なし、downstream 影響なし。
