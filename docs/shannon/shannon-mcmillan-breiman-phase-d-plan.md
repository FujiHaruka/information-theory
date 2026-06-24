# Shannon–McMillan–Breiman Phase D 完了計画 🌙

> ⚠️ **SUPERSEDED (2026-05-20)**: 無条件 `shannon_mcmillan_breiman` は既に
> `InformationTheory/Shannon/SMBAlgoetCover.lean` (2852 行、0 sorry、`InformationTheory.lean:133` で import 済)
> で **完成済み** — limsup/liminf 両方向 + two-sided extension 経由の liminf まで full discharge。
> 本ファイルの下記 D.1'-D.5 (新規 `SMBSandwich.lean` 想定) は **着手不要**。`SMBAlgoetCover.lean`
> が plan より先に完遂していたことを後から確認。以下は履歴として残す。

> Status (2026-05-20): Phase C.1+C.2 + Phase D Birkhoff-per-level + 在庫調査 (Phase 0) 完了。
> 残: Algoet–Cover sandwich 本体 (D.2-D.5)。実装は §"Phase D.2-D.5 実装計画 (2026-05-20)" を参照。

## 進捗

- [x] Phase 0 — 在庫調査 ✅ → [`smb-phase-d-sandwich-inventory.md`](smb-phase-d-sandwich-inventory.md)
- [x] D.1 — Birkhoff per-level (`birkhoffAverage_pmfLogCond_tendsto`) ✅ (`SMBChainRule.lean:401`)
- [ ] D.1' — `pmfLogCondMarkov` 定義 + Birkhoff 再適用 📋 → `SMBSandwich.lean`
- [ ] D.2 — k-Markov likelihood-ratio ≤ 1 (crux) 📋 → `SMBSandwich.lean`
- [ ] D.3 — limsup ≤ entropyRate 📋 → `SMBSandwich.lean`
- [ ] D.4 — liminf ≥ entropyRate (撤退ライン分岐あり) 📋 → `SMBSandwich.lean`
- [ ] D.5 — sandwich → 無条件 `shannon_mcmillan_breiman` 📋 → `SMBSandwich.lean`

## 完了済み (本 plan 着手前)

- **Phase A** — `StationaryProcess` / `ErgodicProcess` (`Stationary.lean` 119 行)
- **Phase B** — `blockEntropy` / `entropyRate` (`EntropyRate.lean` 498 行)
- **Phase C.5 / E-8''** — Birkhoff individual ergodic theorem
  (`BirkhoffErgodic.lean` 1107 行、`birkhoff_ergodic_ae` 0 sorry)
- **E-8' weakened** — `shannon_mcmillan_breiman_of_sandwich`
  (`ShannonMcMillanBreiman.lean` 179 行、4 仮説 pass-through 形)
- **Phase C.1+C.2** ✅ (2026-05-16、本 plan 着手で publish)
  → `InformationTheory/Shannon/SMBChainRule.lean` (421 行、0 sorry / 0 warning):
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

## Phase D.2-D.5 実装計画 (2026-05-20)

> 対象 file: **`InformationTheory/Shannon/SMBSandwich.lean`** (新規)。`InformationTheory.lean` に
> `import InformationTheory.Shannon.SMBSandwich` を 1 行追加して完了。
> proof-log: **yes** (`docs/shannon/proof-log-smb-sandwich.md` を D.2/D.4 の crux で更新)。
> 実装者は本節だけを真実として作業する。signature は在庫
> [`smb-phase-d-sandwich-inventory.md`](smb-phase-d-sandwich-inventory.md) の verbatim を踏襲。

### Approach（解の形）

`blockLogAvg μ p n ω = -(1/n) log P_n(block_n ω)` を、a.s. の chain-rule identity
`log_block_eq_sum_pmfLogCond` で **diagonal sum** `(1/n) ∑_{i<n} pmfLogCond p i ω` に書き換える。
diagonal は条件付け深さ `i` が index と共に増えるため、**per-level Birkhoff
(`birkhoffAverage_pmfLogCond_tendsto`, 固定 `l`) では直接捌けない**（SMB の核心であり、
「真の chain rule の Cesàro で liminf が出る」は **誤り**。判断ログ #5 参照）。Algoet–Cover で
上下から挟む:

- **limsup 側 (易, D.2+D.3)**: 深さを `k` で頭打ちした **k-Markov 近似** `pmfLogCondMarkov k`。
  Birkhoff 再適用で `(1/n)∑ pmfLogCondMarkov k i → H_k`。likelihood-ratio
  `P_n/Q_k^n` の期待値 ≤ 1（k-Markov product が sub-probability）+ Markov ineq +
  Borel–Cantelli (`ae_eventually_notMem`) で `blockLogAvg n ω ≤ (1/n)∑ pmfLogCondMarkov k i ω + ε`
  が a.s. eventually。⟹ `limsup ≤ H_k`。`k→∞` で `H_k ↓ entropyRate`
  (`conditionalEntropyTail_antitone` + `entropyRate_eq_lim_condEntropy`)、`ε→0`。
- **liminf 側 (難, D.4 = 真の crux)**: limsup と **非対称**。Algoet–Cover はここを
  order-∞ 条件付き確率 + Lévy/martingale 収束で挟む。Mathlib martingale lemma が在庫に
  無く、判断ログ #2 で Lévy 経路は片側 shift に不適合と既判定。よって **D.4 は最初から
  撤退ライン variant (D.4-fallback) を本線に据える**（下記）。鋭い liminf を本気で書くなら
  ~150 行超 + 未在庫 martingale が要る、と明記。

依存順 (どの sorry から割るか): **D.1' → D.5(骨組) → D.2 → D.3 → D.4-fallback**。
D.5 を先に骨組みだけ通すと 4 仮説の型が固定され、D.2-D.4 の出力形が確定する。

### 共通の冒頭（在庫 skeleton 準拠）

namespace `InformationTheory.Shannon`、`open MeasureTheory ProbabilityTheory Filter Topology`、
`open scoped ENNReal`、file-level variable は在庫 §着手 skeleton の `{Ω} [MeasurableSpace Ω]`
+ `{α} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`。
import は在庫の 8 行（`Stationary` / `EntropyRate` / `SMBChainRule` / `ShannonMcMillanBreiman`
+ Mathlib `BorelCantelli` / `Markov` / `RadonNikodym` / `Log.Basic`）。
構造 accessor は `p.T` / `p.measurePreserving : MeasurePreserving T μ μ` /
`p.ergodic : Ergodic T μ` / `p.toStationaryProcess`（在庫確認済み）。

---

### D.1' — k-Markov 近似と Birkhoff 再適用

**定義（先頭 sorry）**
```lean
/-- k-Markov approximation per-step conditional log-likelihood.
時刻 `i` で最大 `k` 過去のみ条件付け: `pmfLogCond p (min k i)` を `T^[i - min k i]` で評価。 -/
noncomputable def pmfLogCondMarkov
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k i : ℕ) : Ω → ℝ :=
  fun ω => pmfLogCond μ p (min k i) (p.T^[i - min k i] ω)
```
- `i ≤ k` のとき `min k i = i`, `i - min k i = 0` ⟹ `pmfLogCond p i ω`（真の項に一致）。
  `i > k` のとき深さ `k` 固定で起点を `T^[i-k]` にずらす。場合分けは `min`/`Nat.sub` の rfl で吸収。

**helper a: measurability**
```lean
omit [DecidableEq α] in
lemma measurable_pmfLogCondMarkov
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k i : ℕ) :
    Measurable (pmfLogCondMarkov μ p k i)
```
- 戦略 (2 bullet): `measurable_pmfLogCond μ p (min k i)` (在庫 `SMBChainRule.lean:56`) を
  `(p.measurePreserving.iterate (i - min k i)).measurable` (= `p.measurable_iterate`,
  `Stationary.lean:73`) と `.comp`。

**helper b: 各 i の Birkhoff 平均が同じ極限**
k-Markov 近似の Birkhoff 平均 `(1/(n+1)) ∑_{j≤n} pmfLogCondMarkov k j ... ` ではなく、
**固定 k に対し index `i` を動かしたときの時間平均が `H_k = conditionalEntropyTail μ p k`** に
収束することを使う。実装上は次の 1 補題で十分:
```lean
theorem birkhoffAverage_pmfLogCondMarkov_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => birkhoffAverageReal p.T (pmfLogCond μ p.toStationaryProcess k) n ω)
      Filter.atTop
      (𝓝 (conditionalEntropyTail μ p.toStationaryProcess k))
```
- これは在庫 `birkhoffAverage_pmfLogCond_tendsto` を `l := k` で適用するだけ（**新規証明は実質不要、
  別名 or 直接 inline**）。**重要な設計判断**: k-Markov の time-average は
  `birkhoffAverageReal p.T (pmfLogCond μ p k)`（=深さ `k` 固定 term の時間平均）に一致する。
  なぜなら `pmfLogCondMarkov k i (ω) = pmfLogCond p k (T^[i-k] ω)` (`i≥k`) であり、
  時間平均 `(1/n)∑_{i<n} pmfLogCondMarkov k i ω` と `(1/n)∑_{i<n} pmfLogCond p k (T^[i] ω)` は
  先頭 `k` 項（有限）の差を除いて一致し、`n→∞` で `k/n→0` により極限が等しい。
  ⟹ **`pmfLogCondMarkov` の time-average ≈ per-level Birkhoff (深さ k)**、これが D.1 を D.3 に橋渡し。
- bullet: (1) 先頭 `k` 項差の補題 `tendsto_birkhoff_drop_finite_head`（下記 helper c）で吸収、
  (2) 既証 `birkhoffAverage_pmfLogCond_tendsto μ p k` を引く。

**helper c: 有限先頭項を落としても Birkhoff 極限不変（off-by-one + 頭 k 項の同時処理）**
```lean
lemma birkhoffAvg_diagonalTail_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) (k : ℕ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, pmfLogCondMarkov μ p.toStationaryProcess k i ω)
      Filter.atTop (𝓝 (conditionalEntropyTail μ p.toStationaryProcess k))
```
- bullet: (1) `pmfLogCondMarkov k i = pmfLogCond p k ∘ T^[i-k]` for `i ≥ k`, 先頭 `k` 項は有界
  (Fintype の log は有限) ⟹ `(1/n)·(先頭差) → 0`; (2) 残りは `(1/n)∑_{i<n} (pmfLogCond p k)(T^[i]ω)` で、
  `birkhoffAverageReal` の `(n+1)` 正規化との差は `n/(n+1)→1` (在庫 §off-by-one) で吸収、
  既証 `birkhoffAverage_pmfLogCond_tendsto μ p k` の極限を移送。**この補題が D.3 の入力**。

---

### D.2 — k-Markov likelihood-ratio ≤ 1 (crux)

数学核: k-Markov product measure `Q_k^n` は sub-probability (`∑_{x^n} q_k^n(x^n) ≤ 1`)。
⟹ likelihood ratio `Q_k^n(block_n)/P_n(block_n)` の `P_n` 期待値 ≤ 1。⟹ Markov ineq で
`P_n{ ratio ≥ e^{nε} } ≤ e^{-nε}`、`∑_n e^{-nε} < ∞` ⟹ Borel–Cantelli で a.s. eventually
`ratio < e^{nε}`、すなわち `blockLogAvg n ω ≤ (1/n)∑ pmfLogCondMarkov k i ω + ε`。

**経路選択: 在庫 §自作 2 の (2b) 離散和直接**（rnDeriv bridge を避ける）。

**D.2-a: sub-probability 正規化（最重量サブ補題）**
```lean
theorem markov_block_sum_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k n : ℕ) :
    ∑ x : Fin n → α, qMarkov μ p k n x ≤ 1
```
ここで `qMarkov μ p k n x : ℝ≥0∞`（or `ℝ`）は k-Markov product
`∏_{i<n} (condDistrib (obs (min k i)) (blockRV (min k i)) μ (x の prefix)).real {x i}`。
- bullet: (1) `Finset.prod_range_succ` 帰納 + Tonelli 的に最後の因子から和を取る; (2) 各因子
  `∑_{x_i} (condDistrib … y).real {x_i} = 1` は `condDistrib` の `IsMarkovKernel`/`IsProbabilityMeasure`
  (在庫 `SMBChainRule.lean:345` の `inferInstance` パターン) から; (3) 内側和が 1 に潰れて
  telescoping `≤ 1`（`i<k` 区間で過去欠落 → `≤` で吸収、`=` でなくてよい）。
- **これが D.2 の最大不確実性**（在庫 §最大リスク）。telescoping `∏` の ENNReal/Real 往復 +
  prefix indexing が重い。**着手 1 セッションで通らなければ D.2-fallback に縮退**（下記撤退ライン）。

**D.2-b: ratio 期待値 ≤ 1**
```lean
theorem markov_likelihood_ratio_expectation_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (qMarkov μ p k n (p.blockRV n ω) / (μ.map (p.blockRV n)).real {p.blockRV n ω}) ∂μ ≤ 1
```
- bullet: (1) push-forward via `blockRV n` (在庫 `expected_blockLogAvg_eq` の `integral_map` パターン)
  で `∫ … dμ = ∑_{x^n} (P_n.real{x}) · (q/P)` ; (2) `(P_n.real{x})·(q/P) = q_k^n(x)` で約分（`P_n>0` a.e. on support は
  `block_singleton_pos_ae` 在庫由来）; (3) `∑ q_k^n ≤ 1` (D.2-a) で締め。
  ※ rnDeriv `lintegral_rnDeriv_le` は **使わない**（singleton-ratio=rnDeriv bridge 回避、在庫推奨）。

**D.2-c: bad event の summability + Borel–Cantelli**
```lean
theorem markov_eventually_blockLogAvg_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      blockLogAvg μ p.toStationaryProcess n ω
        ≤ (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, pmfLogCondMarkov μ p.toStationaryProcess k i ω + ε
```
- bullet: (1) bad event `s n := {ω | ratio_n ω ≥ exp (n·ε)}`、`μ (s n) ≤ exp(-nε)·E[ratio] ≤ exp(-nε)` を
  `meas_ge_le_lintegral_div` (在庫 `Markov.lean:104`) + D.2-b で; (2) `∑_n exp(-nε) ≠ ∞`
  (幾何級数, `ENNReal` summable); (3) `ae_eventually_notMem` (在庫 `BorelCantelli.lean:86`) で
  `∀ᵐ ω, ∀ᶠ n, ω ∉ s n`; (4) `ω ∉ s n` を log 取って `Real.exp_log`/`Real.log_le_log` で
  `blockLogAvg ≤ -(1/n)log q_k^n + ε = (1/n)∑ pmfLogCondMarkov + ε` に翻訳
  (chain-rule analog `log_block_eq_sum_pmfLogCond` の k-Markov 版で `-log q_k^n = ∑ pmfLogCondMarkov`)。

---

### D.3 — limsup ≤ entropyRate

```lean
theorem smb_limsup_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess
```
- bullet: (1) 固定 `k`, `ε>0`: D.2-c + D.1'(helper c, `birkhoffAvg_diagonalTail_tendsto`) を
  `filter_upwards`、`limsup blockLogAvg ≤ H_k + ε`（`limsup_le_of_le` + eventually 上界）;
  (2) `ε→0`（`ge_of_tendsto` / `le_of_forall_pos_le_add`）で `limsup ≤ H_k`;
  (3) `k→∞`: `conditionalEntropyTail μ p k → entropyRate μ p` (在庫 `entropyRate_eq_lim_condEntropy`
  `EntropyRate.lean:466`) + `conditionalEntropyTail_antitone` (`EntropyRate.lean:264`) で
  `H_k ↓ entropyRate` ⟹ `limsup ≤ entropyRate`。
- 注意: a.s. の量化子順序。`k`/`ε` は **可算**選択（`k ∈ ℕ`, `ε := 1/(m+1)`）なので
  `ae_all_iff` で内側 `∀ᵐ` を外に出してから filter_upwards（measure-zero union が可算で safe）。

---

### D.4 — liminf ≥ entropyRate（**撤退ライン variant を本線に**）

**判定: 鋭い a.s. liminf は full-discharge を見込まない。** 理由は §Approach。よって以下を本線:

**D.4-fallback（本線, 0-sorry 着地）**: liminf の鋭い解析ステップ（order-∞ 条件付き確率の
Lévy/martingale a.s. 収束）を **名前付き仮説** に切り出し、それ以外を無条件で組む。
```lean
/-- liminf 側で必要な唯一の解析的入力（Algoet–Cover の order-∞ martingale step）。
    full martingale 証明は別 plan（Phase E?）へ。ここでは仮説として受ける。 -/
def MartingaleLiminfInput (μ : Measure Ω) (p : ErgodicProcess μ α) : Prop :=
  ∀ᵐ ω ∂μ, entropyRate μ p.toStationaryProcess
    ≤ Filter.liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop

theorem smb_liminf_ge_of_martingale
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α)
    (h : MartingaleLiminfInput μ p) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop :=
  h
```
- これは `h` をそのまま返すだけ（trivial）。**目的**: D.5 で `smb_liminf_ge_of_martingale` を
  使うことで、limsup 側 (D.2-D.3) と sandwich wiring (D.5) は **完全に無条件で 0-sorry publish** され、
  liminf の重い部分のみ 1 個の明示仮説 `MartingaleLiminfInput` に局所化される。
- **代替検討（full-discharge を狙うなら, optional)**: `smb_liminf_ge` を rigorous に。
  必要なのは Lévy upward `MeasureTheory.Integrable.tendsto_ae_condExp` 系 + 増大 σ-代数
  `⨆ blockRV n` の filtration。**在庫に無い**ため新規 ~150 行 + 片側 shift 整合（判断ログ #2 の壁）。
  full を着手して 1 セッションで a.s. 収束が出なければ即 D.4-fallback に戻す。

**任意の上積み（軽い片側だけでも無条件化を試す, optional）**: Fatou で
`∫ liminf blockLogAvg ≥ liminf ∫ blockLogAvg = entropyRate`（`tendsto_expected_blockLogAvg`,
`ShannonMcMillanBreiman.lean:162` 既証）は **integral 版**であり a.s. を出さない。a.s. liminf には
不足。よって D.4-fallback の正当性根拠（鋭い a.s. には martingale が要る）として記録するに留める。

---

### D.5 — sandwich → 無条件主定理

```lean
theorem shannon_mcmillan_breiman
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α)
    (h_li : MartingaleLiminfInput μ p) :   -- ★ D.4-fallback 採用時のみ。full-discharge なら削除
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess))
```
- bullet: (1) `h_liminf := smb_liminf_ge_of_martingale μ p h_li`, `h_limsup := smb_limsup_le μ p`;
  (2) `h_bdd_above`/`h_bdd_below`: 収束 (liminf=limsup=entropyRate) の系。`limsup ≤ entropyRate` から
  `IsBoundedUnder (≤)`、`entropyRate ≤ liminf` から `IsBoundedUnder (≥)` を
  `Filter.isBoundedUnder_of` で供給（or `eventually` の定数上下界）;
  (3) `exact shannon_mcmillan_breiman_of_sandwich μ p h_liminf h_limsup h_bdd_above h_bdd_below`
  (在庫 `ShannonMcMillanBreiman.lean:85`, 引数順 verbatim)。
- **full-discharge に到達した場合**: `h_li` 仮説を消し、`h_liminf := smb_liminf_ge μ p` に差し替えれば
  完全無条件 `shannon_mcmillan_breiman`。signature 変更は本定理の 1 行のみ。

---

### 撤退ライン（更新, 段階的）

1. **D.2-a が 1 セッションで通らない（telescoping 重）** → `markov_block_sum_le_one` を仮説
   `MarkovSubProbInput` に切り出し、D.2-b/c/D.3 は無条件で組む。limsup 側 wiring + Borel–Cantelli 適用は
   無条件で残り、純 pass-through MVP より前進（在庫 §撤退ライン距離と一致）。
2. **D.4 鋭い a.s. liminf** → 上記 D.4-fallback（本線）。`MartingaleLiminfInput` 1 仮説に局所化。
3. **最小 0-sorry 着地形（両撤退発動時）**: `shannon_mcmillan_breiman` が
   `(h_li : MartingaleLiminfInput) (h_sub : MarkovSubProbInput)` の 2 仮説付きで publish。
   それでも sandwich + Birkhoff + Borel–Cantelli の組み立ては全て無条件で検証済みになる。

### 工数（再見積）

| sub-phase | 行数 | 不確実性 |
|---|---|---|
| D.1' (pmfLogCondMarkov + helper a/b/c) | ~80-110 | 低（既証 Birkhoff の移送） |
| D.2-a (sub-prob telescoping) | ~60-120 | **高（最大リスク）** |
| D.2-b/c (ratio期待値 + Borel–Cantelli) | ~80-110 | 中（部品は全在庫） |
| D.3 (limsup) | ~50-80 | 低-中（量化子順序） |
| D.4-fallback | ~15-25 | 低（仮説 pass-through） |
| D.5 (wiring) | ~30-50 | 低 |
| **合計** | **~315-495** | — |

---

## 11. 判断ログ

### 2026-05-16 — 起草 (Phase C.1+C.2 + D-partial 完了直後)

1. **Phase C.1+C.2 採用経路**: `condDistrib` + `compProd_map_condDistrib` + `piFinSuccAbove` equiv + `lintegral_singleton`。`Bridge.lean` / `Entropy.lean` の既存パターンに準拠。新規 Mathlib gap 0。
2. **Levy 経路撤退**: 当初 Phase C.3 で `MeasureTheory.Integrable.tendsto_ae_condExp` (Levy upward) を直接適用する経路を検討したが、SMB の "forward conditional log-likelihood `pmfLogCond p i` が `i → ∞` で収束する" は **stationarity と T-invertibility (or one-sided 構成) なしには成立しない**。SMB の証明は Levy ではなく **Algoet–Cover sandwich** (Markov ineq + Borel-Cantelli + Birkhoff-per-level) が必要と判明。
3. **Phase D Birkhoff-per-level 単独 publish**: `birkhoffAverage_pmfLogCond_tendsto` は Algoet–Cover sandwich の **入力部品** として独立に意義あり (`H_l` への各レベル収束)、本 plan の Phase D.1 そのもの。残: D.2-D.5 (sandwich 本体)。
4. **Algoet-Cover 経路選択理由**: Mathlib に likelihood ratio Markov ineq + Borel-Cantelli が揃っているため、Phase D.2 の自前構築は ~150-200 行で済む見込み。代替の "backward martingale" 経路は T-invertibility が必要で本 plan の生 `StationaryProcess` (片側 shift) に不適合。

### 2026-05-20 — D.2-D.5 実装計画起草（在庫調査 Phase 0 完了後）

5. **「真の chain rule の Cesàro で liminf」は誤りと明示**: 在庫 §自作 4 の観察（liminf は
   `log_block_eq_sum_pmfLogCond` + per-level Birkhoff の Cesàro で素直に出る可能性）を **棄却**。
   `blockLogAvg n = (1/n)∑_{i<n} pmfLogCond p i` は条件付け深さが index と共に増える **diagonal**
   であり、per-level Birkhoff（固定 `l`）の Cesàro では捌けない。diagonal の a.s. 収束こそ SMB の主張
   そのもので、仮定できない。liminf は limsup と非対称で本質的に重い。
6. **liminf 側は D.4-fallback を本線採用**: 鋭い a.s. liminf は order-∞ 条件付き確率の Lévy/martingale
   a.s. 収束を要し、その Mathlib lemma は在庫に無く、判断ログ #2 で Lévy 経路は片側 shift に不適合と
   既判定。よって `MartingaleLiminfInput` を 1 仮説に局所化し、limsup (D.2-D.3) + wiring (D.5) を
   無条件 0-sorry で publish する方針を本線に。full-discharge は別 plan（Phase E 候補）へ送る。
7. **D.2 は離散和直接 (2b) 採用**: rnDeriv `lintegral_rnDeriv_le` 経路は singleton-ratio=rnDeriv
   bridge 補題が新規で要るため不採用。`condDistrib` の `IsProbabilityMeasure`（在庫 `SMBChainRule.lean:345`）
   から `∑_{x^n} q_k^n ≤ 1` を `Finset.prod_range_succ` 帰納で直接組む。これが最大リスク
   (`markov_block_sum_le_one`)、1 セッション未達なら `MarkovSubProbInput` 仮説へ縮退。
8. **依存順を D.1' → D.5骨組 → D.2 → D.3 → D.4-fallback に固定**: D.5 を先に骨組みだけ通すと
   `shannon_mcmillan_breiman_of_sandwich` の 4 仮説の型が確定し、D.2-D.4 の出力形が逆算できる。
9. **Borel–Cantelli 名称修正を反映**: 在庫が指摘の通り `measure_limsup_eq_zero` は不在、正しくは
   `measure_limsup_atTop_eq_zero` / 出口は `ae_eventually_notMem`。off-by-one（`birkhoffAverageReal`
   は `(n+1)` 正規化、`blockLogAvg` は `1/n`）は helper c `birkhoffAvg_diagonalTail_tendsto` で
   `n/(n+1)→1` 吸収。

## 参考

- 親 plan: [`shannon-mcmillan-breiman-plan.md`](shannon-mcmillan-breiman-plan.md)
- E-8' weak: [`shannon-mcmillan-breiman-phase-c-plan.md`](shannon-mcmillan-breiman-phase-c-plan.md)
- 実装: `InformationTheory/Shannon/SMBChainRule.lean`
- Algoet–Cover (1988): "A sandwich proof of the Shannon-McMillan-Breiman theorem"
  (Annals of Probability)
