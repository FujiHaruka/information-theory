# Shannon–McMillan–Breiman Phase D 完了計画 🌙

> Status (2026-05-16): Phase C.1+C.2 + Phase D Birkhoff-per-level 完了
> (`Common2026/Shannon/SMBChainRule.lean` 421 行、0 sorry / 0 warning)。
> 残: Algoet–Cover sandwich (~300-500 行) で 4 仮説 discharge → 仮定なし SMB。

## 完了済み (本 plan 着手前)

- **Phase A** — `StationaryProcess` / `ErgodicProcess` (`Stationary.lean` 119 行)
- **Phase B** — `blockEntropy` / `entropyRate` (`EntropyRate.lean` 498 行)
- **Phase C.5 / E-8''** — Birkhoff individual ergodic theorem
  (`BirkhoffErgodic.lean` 1107 行、`birkhoff_ergodic_ae` 0 sorry)
- **E-8' weakened** — `shannon_mcmillan_breiman_of_sandwich`
  (`ShannonMcMillanBreiman.lean` 179 行、4 仮説 pass-through 形)
- **Phase C.1+C.2** ✅ (2026-05-16、本 plan 着手で publish)
  → `Common2026/Shannon/SMBChainRule.lean` (421 行、0 sorry / 0 warning):
  - `pmfLogCond μ p i ω := -log (cd (block_i ω)).real {obs i ω}` + measurability
  - `block_measure_succ_singleton_eq` (ENNReal 乗法 chain rule)
  - `block_measure_succ_singleton_real_eq` (Real 版)
  - `block_singleton_pos_ae_at` / `_upTo` (a.s. positivity over prefix)
  - `cond_singleton_pos_ae` (条件付き positivity)
  - **`log_block_eq_sum_pmfLogCond`** (Phase C.1+C.2 主結果、
    a.s. log identity `-log P_n(block_n) = ∑_{i<n} pmfLogCond p i`)
- **Phase D partial** ✅ (2026-05-16、本 plan 着手で publish、同上 file 末尾):
  - `integral_pmfLogCond_eq_conditionalEntropyTail`
    (`∫ pmfLogCond p l dμ = H_l = conditionalEntropyTail μ p l`)
  - `integrable_pmfLogCond` (Fintype pushforward 経由)
  - **`birkhoffAverage_pmfLogCond_tendsto`** (per-level Birkhoff 適用、
    `(1/(n+1)) ∑_{i=0}^{n} pmfLogCond p l (T^[i] ω) → H_l` a.s.)

## 残: Algoet–Cover sandwich (~300-500 行見込み)

`shannon_mcmillan_breiman_of_sandwich` の 4 仮説:
- `h_liminf : ∀ᵐ ω, entropyRate ≤ liminf blockLogAvg n ω`
- `h_limsup : ∀ᵐ ω, limsup blockLogAvg n ω ≤ entropyRate`
- `h_bdd_above`, `h_bdd_below`: 有界性 (収束から自動)

を、Algoet–Cover (1988) 経路で discharge する。

### Approach (Algoet–Cover 1988)

#### limsup direction (`limsup ≤ entropyRate`)

固定 `k`, 各 `n ≥ k` で **k-Markov approximation**:
- `q_k^n(x^n) := ∏_{i=0}^{n-1} P(X_i | X_{max(0,i-k)}, …, X_{i-1})(x^n)`
- `-(1/n) log q_k^n(X^n) = (1/n) ∑_{i=0}^{n-1} pmfLogCond_{Markov-k}(i, ω)`
- ここで `pmfLogCond_{Markov-k}(i, ω) := pmfLogCond p (min k i) (T^[i - min k i] ω)` (時刻 `i` で最大 `k` 過去だけ条件付け)
- 定常性 + Birkhoff (本 plan 既証): `(1/n) ∑ pmfLogCond_{Markov-k}(i, ω) → H_k` a.s.

**Key inequality** (Algoet–Cover、likelihood ratio Markov):
- `P_n^X(x^n) / q_k^n(x^n) ≤ 1` (??? — 実は **直接 pointwise 不成立**、`Markov.likelihood_ratio_le` 形の確率 1 で成立する近似)
- ⟹ `-(1/n) log P_n^X(X^n) ≥ -(1/n) log q_k^n(X^n) - small`
- ⟹ `limsup blockLogAvg ≤ H_k + small` (with high probability eventually)
- Take `k → ∞`: `H_k → entropyRate`、small → 0。

#### liminf direction (`liminf ≥ entropyRate`)

対称形 + Fatou + DCT 経由。

### 必要な Mathlib 部品

| 部品 | Mathlib status |
|---|---|
| `birkhoff_ergodic_ae` | 本 plan で自前 (E-8'' 既証) |
| `Borel–Cantelli` (`MeasureTheory.measure_limsup_eq_zero`) | ✅ Mathlib 既存 |
| `Markov ineq` (`Pr[‖X‖ ≥ ε] ≤ ε⁻¹ 𝔼‖X‖`) | ✅ `meas_ge_le_mul_pow_enorm` |
| 多項 Markov sliding-window 期待値 | ⚠️ likelihood ratio 形は自前 |

### 工数感

- (D.1) k-Markov approximation 定義 + integrability + Birkhoff 適用: ~80-100 行
- (D.2) likelihood ratio + Markov ineq + Borel-Cantelli: ~150-200 行
- (D.3) limsup direction 主証明: ~80-100 行
- (D.4) liminf direction (対称形): ~80-100 行
- (D.5) sandwich → 主定理: ~30-50 行
- **合計**: **400-550 行**、~2-3 セッション

### 撤退ライン

- (D.2) likelihood ratio 形が Mathlib に gap 多すぎ → "Algoet-Cover 仮説形" SMB (Markov ineq + Borel-Cantelli を hypothesis にとり、本体は組み立てのみ) で hypothesis pass-through MVP (~100 行)、自前は別 plan へ。

## 11. 判断ログ

### 2026-05-16 — 起草 (Phase C.1+C.2 + D-partial 完了直後)

1. **Phase C.1+C.2 採用経路**: `condDistrib` + `compProd_map_condDistrib` + `piFinSuccAbove` equiv + `lintegral_singleton`。`Bridge.lean` / `Entropy.lean` の既存パターンに準拠。新規 Mathlib gap 0。
2. **Levy 経路撤退**: 当初 Phase C.3 で `MeasureTheory.Integrable.tendsto_ae_condExp` (Levy upward) を直接適用する経路を検討したが、SMB の "forward conditional log-likelihood `pmfLogCond p i` が `i → ∞` で収束する" は **stationarity と T-invertibility (or one-sided 構成) なしには成立しない**。SMB の証明は Levy ではなく **Algoet–Cover sandwich** (Markov ineq + Borel-Cantelli + Birkhoff-per-level) が必要と判明。
3. **Phase D Birkhoff-per-level 単独 publish**: `birkhoffAverage_pmfLogCond_tendsto` は Algoet–Cover sandwich の **入力部品** として独立に意義あり (`H_l` への各レベル収束)、本 plan の Phase D.1 そのもの。残: D.2-D.5 (sandwich 本体)。
4. **Algoet-Cover 経路選択理由**: Mathlib に likelihood ratio Markov ineq + Borel-Cantelli が揃っているため、Phase D.2 の自前構築は ~150-200 行で済む見込み。代替の "backward martingale" 経路は T-invertibility が必要で本 plan の生 `StationaryProcess` (片側 shift) に不適合。

## 参考

- 親 plan: [`shannon-mcmillan-breiman-plan.md`](shannon-mcmillan-breiman-plan.md)
- E-8' weak: [`shannon-mcmillan-breiman-phase-c-plan.md`](shannon-mcmillan-breiman-phase-c-plan.md)
- 実装: `Common2026/Shannon/SMBChainRule.lean`
- Algoet–Cover (1988): "A sandwich proof of the Shannon-McMillan-Breiman theorem"
  (Annals of Probability)
