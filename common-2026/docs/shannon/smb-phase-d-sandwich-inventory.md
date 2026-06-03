# SMB Phase D — Algoet–Cover sandwich Mathlib/in-repo 在庫調査

> 親計画: [`shannon-mcmillan-breiman-phase-d-plan.md`](shannon-mcmillan-breiman-phase-d-plan.md)
> (esp. §"残: Algoet–Cover sandwich" / §工数感 D.1-D.5 / §撤退ライン).
> 本ファイルは Phase D の在庫調査 + D.2 (crux) feasibility 判定。**実装も計画起草もしない。**

## 一行サマリ

**Phase D で使う API のうち、組み立て部品（Borel–Cantelli・Markov ineq・rnDeriv 積分 ≤ 1・Birkhoff per-level・chain rule log identity）は ~85% が既存 (Mathlib 5 件 + 本 repo 5 件)。自作必要は 4 件 (k-Markov approx の定義 `pmfLogCondMarkov` / likelihood-ratio ≤ 1 in expectation の本体 / limsup-direction 主証明 / liminf-direction 対称形)。** **撤退ライン発動リスク = 中。** 最大の危険は D.2 の「k-Markov 近似 `q_k^n` の正規化 `∑ q_k^n ≤ 1`」を Mathlib の `rnDeriv` 機構に乗せられるかどうか — 乗せられなければ離散和を手で組む必要があり ~80-120 行膨らむ。**`[Invertible]`/両側 shift の leak は無し**（`Ergodic` は片側 `MeasurePreserving` のみ要求、確認済み）。

---

## 主定理の最終形（再掲）

discharge 対象は `shannon_mcmillan_breiman_of_sandwich` の 4 仮説
(`InformationTheory/Shannon/ShannonMcMillanBreiman.lean:85-105`)。最終目標は
**仮定なし `shannon_mcmillan_breiman`**:

```lean
theorem shannon_mcmillan_breiman
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess))
```

を、4 仮説を補題として証明し `shannon_mcmillan_breiman_of_sandwich` に渡すことで得る。

証明戦略 (Algoet–Cover 1988, pseudo-Lean):

```
-- limsup direction (limsup blockLogAvg ≤ entropyRate)
fix k. ∀ n ≥ k, define qkn ω := ∏_{i<n} P(X_i | X_{max(0,i-k)..i-1})(...)   -- k-Markov approx
have h_avg : (1/n) Σ pmfLogCondMarkov k i ω → H_k a.s.                     -- Birkhoff per-level (既)
have h_lr  : ∀ᵐ ω, ∀ᶠ n, blockLogAvg n ω ≤ -(1/n) log qkn ω + ε           -- D.2 crux
            -- = Markov ineq on P_n/qkn + Borel–Cantelli (Σ μ{ratio≥eⁿᵉ} < ∞)
calc limsup blockLogAvg ≤ H_k + ε                                          -- combine h_avg + h_lr
take k → ∞ via entropyRate_eq_lim_condEntropy: H_k → entropyRate, ε → 0
-- liminf direction: 対称形 (Fatou / DCT 経由)
-- bdd_above / bdd_below: 収束の系
```

---

## A. 在庫テーブル — 本 repo 既存部品 (Phase D の入力)

| 概念 | API (本 repo) | file:line | 状態 | Phase D での扱い |
|---|---|---|---|---|
| chain rule log identity | `log_block_eq_sum_pmfLogCond` | `InformationTheory/Shannon/SMBChainRule.lean:255` | ✅ 既存 (0 sorry) | `-log P_n(block_n ω) = ∑_{i<n} pmfLogCond p i ω` a.s. 真の log-likelihood 側 |
| per-step cond log-likelihood | `pmfLogCond` | `SMBChainRule.lean:50` | ✅ 既存 | k-Markov 版 `pmfLogCondMarkov` の雛形 |
| per-level integral 同定 | `integral_pmfLogCond_eq_conditionalEntropyTail` | `SMBChainRule.lean:304` | ✅ 既存 | `∫ pmfLogCond p l = H_l` |
| integrability | `integrable_pmfLogCond` | `SMBChainRule.lean:357` | ✅ 既存 | Birkhoff の前提 |
| **Birkhoff per-level** | `birkhoffAverage_pmfLogCond_tendsto` | `SMBChainRule.lean:401` | ✅ 既存 (0 sorry) | `(1/(n+1)) ∑_{i≤n} pmfLogCond p l (T^[i] ω) → H_l` a.s. — D.1 の心臓 |
| Birkhoff (抽象) | `birkhoff_ergodic_ae` | `InformationTheory/Shannon/BirkhoffErgodic.lean:1031` | ✅ 既存 (0 sorry) | k-Markov 近似にも再適用 |
| H_l → entropyRate | `entropyRate_eq_lim_condEntropy` | `InformationTheory/Shannon/EntropyRate.lean:466` | ✅ 既存 | k → ∞ の極限 |
| tail antitone | `conditionalEntropyTail_antitone` | `EntropyRate.lean:264` | ✅ 既存 | H_k の単調性 (sandwich の符号制御) |
| sandwich wrapper | `shannon_mcmillan_breiman_of_sandwich` | `ShannonMcMillanBreiman.lean:85` | ✅ 既存 | 4 仮説 → Tendsto |
| blockLogAvg 定義 | `blockLogAvg` | `ShannonMcMillanBreiman.lean:55` | ✅ 既存 | `-(1/n) log P_n(block_n ω)` (LHS) |

### 完全 signature (load-bearing, verbatim)

**`birkhoffAverage_pmfLogCond_tendsto`** (`SMBChainRule.lean:401-407`) — D.1 主入力:
```lean
theorem birkhoffAverage_pmfLogCond_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) (l : ℕ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => birkhoffAverageReal p.T (pmfLogCond μ p.toStationaryProcess l) n ω)
      Filter.atTop
      (𝓝 (conditionalEntropyTail μ p.toStationaryProcess l))
```
- 結論形 verbatim: `∀ᵐ ω ∂μ, Filter.Tendsto (fun n => birkhoffAverageReal p.T (pmfLogCond μ p.toStationaryProcess l) n ω) Filter.atTop (𝓝 (conditionalEntropyTail μ p.toStationaryProcess l))`
- 型クラス前提: `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]` (file-level variable) + `[IsProbabilityMeasure μ]`。
- **注意**: `birkhoffAverageReal` は `(n+1)` 項平均 `(∑_{i=0}^{n} f(T^[i]ω))/(n+1)` (`BirkhoffErgodic.lean:79`)。`blockLogAvg` は `-(1/n) log P_n` で **正規化が `n` vs `n+1` でズレる** → sandwich 結合時に off-by-one 整合が必要 (D.3/D.4 の plumbing)。

**`log_block_eq_sum_pmfLogCond`** (`SMBChainRule.lean:255-260`):
```lean
theorem log_block_eq_sum_pmfLogCond
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (n : ℕ) :
    ∀ᵐ ω ∂μ,
      -Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})
        = ∑ i ∈ Finset.range n, pmfLogCond μ p i ω
```
- 型クラス前提: file-level variable 同上、`omit [DecidableEq α]` 適用。

**`birkhoff_ergodic_ae`** (`BirkhoffErgodic.lean:1031-1035`):
```lean
theorem birkhoff_ergodic_ae {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverageReal T f n ω)
      atTop (𝓝 (∫ x, f x ∂μ))
```
- 引数順: `(hT : MeasurePreserving T μ μ)`, `(hT_erg : Ergodic T μ)`, `(hf : Integrable f μ)`。
- 型クラス前提: `{m₀ : MeasurableSpace Ω}` (file-level), `[IsProbabilityMeasure μ]`。**`StandardBorel` 不要 / 両側不要。**

**`pmfLogCond`** (`SMBChainRule.lean:50-53`) — k-Markov 雛形:
```lean
noncomputable def pmfLogCond
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (i : ℕ) : Ω → ℝ :=
  fun ω => -Real.log
    ((condDistrib (p.obs i) (p.blockRV i) μ (p.blockRV i ω)).real {p.obs i ω})
```
- k-Markov 版で必要なのは「最大 k 過去だけで条件付け」: 計画 (`...phase-d-plan.md:47`) は `pmfLogCond p (min k i) (T^[i - min k i] ω)`。定常性で `condDistrib (obs i) (blockRV_{i-k..i})` を `condDistrib (obs (min k i)) (blockRV (min k i)) ∘ T^[...]` に翻訳 → 既存 `pmfLogCond` を再利用できる見込み。

---

## B. 在庫テーブル — Mathlib 部品 (D.2 crux)

| 概念 | Mathlib API | file:line | 状態 | Phase D での扱い |
|---|---|---|---|---|
| Borel–Cantelli (limsup) | `MeasureTheory.measure_limsup_atTop_eq_zero` | `Mathlib/MeasureTheory/OuterMeasure/BorelCantelli.lean:62` | ✅ 既存 | `∑ μ(bad_n) < ∞ → μ(limsup bad_n) = 0` |
| Borel–Cantelli (eventually) | `MeasureTheory.ae_eventually_notMem` | `Mathlib/MeasureTheory/OuterMeasure/BorelCantelli.lean:86` | ✅ 既存 | **最有力**: `∀ᵐ x, ∀ᶠ n, x ∉ bad_n` — limsup blockLogAvg ≤ H_k + ε に直結 |
| Borel–Cantelli (frequently) | `MeasureTheory.measure_setOf_frequently_eq_zero` | `BorelCantelli.lean:79` | ✅ 既存 | predicate 版 (bad event を述語で持つとき) |
| Markov / Chebyshev | `MeasureTheory.meas_ge_le_lintegral_div` | `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:104` | ✅ 既存 | `μ{ε ≤ f} ≤ (∫⁻ f)/ε` — bad event 確率の上界 |
| Markov (乗法形) | `MeasureTheory.mul_meas_ge_le_lintegral₀` | `Markov.lean:50` | ✅ 既存 | `ε·μ{ε ≤ f} ≤ ∫⁻ f` — div 回避形 |
| **likelihood ratio ≤ μ s** | `MeasureTheory.meas_le_lintegral₀` | `Markov.lean:61` | ✅ 既存 | `(∀x∈s, 1≤f x) → μ s ≤ ∫⁻ f` — ratio ≥ 1 集合の測度を ratio 積分で抑える直接形 |
| rnDeriv 積分 ≤ univ | `MeasureTheory.Measure.lintegral_rnDeriv_le` | `Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean:325` | ✅ 既存 | **`∫⁻ dμ/dν dν ≤ μ univ ≤ 1`** — likelihood ratio 期待値 ≤ 1 の Mathlib 直系候補 |
| rnDeriv set 積分 ≤ μ s | `MeasureTheory.Measure.setLIntegral_rnDeriv_le` | `RadonNikodym.lean:321` | ✅ 既存 | 部分集合版 |
| **likelihood-ratio 期待値 ≤ 1 (k-Markov 形)** | — | — | ❌ **不在** | **自前**: `∑_{x^n} q_k^n(x^n) ≤ 1` (sub-probability normalization) を真の `P_n` 期待値に翻訳 |

### 完全 signature (load-bearing, verbatim)

**`ae_eventually_notMem`** (`BorelCantelli.lean:86-88`) — D.2 出口:
```lean
theorem ae_eventually_notMem {s : ℕ → Set α} (hs : (∑' i, μ (s i)) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n
```
- 引数順: `{s : ℕ → Set α}`, `(hs : (∑' i, μ (s i)) ≠ ∞)`。
- 型クラス前提 (file-level variable, `BorelCantelli.lean:36`): `{α ι F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] [Countable ι] {μ : F}`。**`IsProbabilityMeasure` も `StandardBorel` も `MeasurableSpace` すら不要** (`Measure Ω` は `OuterMeasureClass` instance を満たす)。
- 結論形 verbatim: `∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n`。

**`measure_limsup_atTop_eq_zero`** (`BorelCantelli.lean:62-64`):
```lean
theorem measure_limsup_atTop_eq_zero {s : ℕ → Set α} (hs : ∑' i, μ (s i) ≠ ∞) :
    μ (limsup s atTop) = 0
```
- 型クラス前提: 同上 file-level (但し `s : ℕ → Set α` なので `Countable ι` は不要)。
- **注意**: 計画書 (`...phase-d-plan.md:66`) の名前 `MeasureTheory.measure_limsup_eq_zero` は **存在しない** (loogle `Found 0`)。正しい名前は `measure_limsup_atTop_eq_zero`。

**`meas_ge_le_lintegral_div`** (`Markov.lean:104-105`):
```lean
theorem meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    (hε' : ε ≠ ∞) : μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε
```
- 引数順: `{f : α → ℝ≥0∞}`, `(hf : AEMeasurable f μ)`, `{ε : ℝ≥0∞}`, `(hε : ε ≠ 0)`, `(hε' : ε ≠ ∞)`。
- 型クラス前提 (file-level, `Markov.lean:28`): `{α : Type*} {mα : MeasurableSpace α} {μ : Measure α}`。**`IsProbabilityMeasure` 不要。**
- 結論形 verbatim: `μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε`。

**`meas_le_lintegral₀`** (`Markov.lean:61-62`) — ratio ≥ 1 集合の直接抑え:
```lean
lemma meas_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    {s : Set α} (hs : ∀ x ∈ s, 1 ≤ f x) : μ s ≤ ∫⁻ a, f a ∂μ
```
- 引数順: `{f : α → ℝ≥0∞}`, `(hf : AEMeasurable f μ)`, `{s : Set α}`, `(hs : ∀ x ∈ s, 1 ≤ f x)`。
- 結論形 verbatim: `μ s ≤ ∫⁻ a, f a ∂μ`。

**`Measure.lintegral_rnDeriv_le`** (`RadonNikodym.lean:325`) — 期待値 ≤ 1 の Mathlib 直系:
```lean
lemma lintegral_rnDeriv_le : ∫⁻ x, μ.rnDeriv ν x ∂ν ≤ μ Set.univ
```
- 型クラス前提 (file-level `RadonNikodym.lean:54,66`): `{α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}`。**absolute continuity 不要** (≤ 形なので任意の `μ, ν`)。
- 結論形 verbatim: `∫⁻ x, μ.rnDeriv ν x ∂ν ≤ μ Set.univ`。
- D.2 での使い方: `ν = P_n^X` (真の law), `μ = Q_k^n` (k-Markov law) と置けば `∫⁻ (dQ/dP) dP ≤ Q univ = 1`。**ただし `q_k^n / P_n` が rnDeriv で書けるか・離散だと rnDeriv が singleton 比に一致するかの bridge が必要** → 後述「自作」へ。

---

## 主要前提条件ボックス（前提事故が起きやすい lemma）

- **`ae_eventually_notMem` / `measure_limsup_atTop_eq_zero` (Borel–Cantelli)**:
  - 前提は `∑' i, μ(s i) ≠ ∞` **のみ**。`IsProbabilityMeasure` / `StandardBorel` / 可分性 一切不要。
  - `s : ℕ → Set α` を bad event `{ω | blockLogAvg n ω > H_k + ε}` で与え、`∑ μ(bad_n) < ∞` を Markov ineq で示せば終わり。**型クラス leak 無し。**
- **`meas_ge_le_lintegral_div` (Markov)**:
  - `f : α → ℝ≥0∞` (ENNReal 値) が要る。実数 `blockLogAvg` を ENNReal に持ち上げる cast 仕事が発生 (`Real.toNNReal`/`ENNReal.ofReal` 経由)。`ε ≠ 0 ∧ ε ≠ ∞` の側条件を毎回供給。
  - **対数を取った後の指数化**: bad event `{blockLogAvg > H_k+ε}` を ratio event `{P_n/q_k^n ≥ exp(nε)}` に翻訳する `Real.exp_log` (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`) と単調性が要る。`exp(nε)` を `ε` パラメタに渡すので `∑ μ(bad_n) ≤ ∑ exp(-nε) E[ratio] ≤ ∑ exp(-nε) < ∞` (幾何級数収束) が summability の根拠。
- **`lintegral_rnDeriv_le`**:
  - `μ.rnDeriv ν` は `μ` の `ν` に対する Radon–Nikodym 微分。離散有限アルファベットでは `(μ.rnDeriv ν) x = (μ.real {x})/(ν.real {x})` (ν-a.e.) になるはずだが、**この singleton-ratio = rnDeriv の同定補題が本 repo にない** (`Bridge.lean`/`Measure.lean` に類似なし)。これを書くか、rnDeriv を経由せず離散和 `∑_{x^n} q_k^n(x^n) ≤ 1` を直接組むかの分岐 = D.2 の最大の不確実性。
- **`birkhoffAverageReal` の `(n+1)` 正規化**:
  - per-level Birkhoff は `(n+1)` 項平均。`blockLogAvg` は `1/n` 正規化。sandwich 結合時に `n/(n+1) → 1` で吸収するか、両者を揃える補題が D.3/D.4 で必要 (off-by-one、~10-20 行)。

---

## 自作が必要な要素（優先度順）

1. **`pmfLogCondMarkov μ p k i : Ω → ℝ`** (k-Markov 近似の per-step term) — 工数 ~40-60 行
   - 推奨実装: `pmfLogCond μ p (min k i) (T^[i - min k i] ω)` を land させ、定常性 (`map_joint_eq_shifted` の一般化 / `identDistrib_obs_zero`) で `condDistrib` を時刻 0 起点に揃える。
   - 落とし穴: `i < k` のとき過去が k 未満 → `min k i` 場合分け。`T^[i - min k i]` の measurability/積分性は既存 `measurable_pmfLogCond` の comp で出る見込み。
   - これに対し Birkhoff per-level を再適用すれば `(1/n) ∑ pmfLogCondMarkov → H_k` (D.1)。`birkhoffAverage_pmfLogCond_tendsto` をほぼコピーで済む。

2. **likelihood-ratio ≤ 1 in expectation (D.2 crux)** — 工数 ~80-150 行 (**撤退ライン候補**)
   - 数学的核: `∑_{x^n} q_k^n(x^n) ≤ 1` (k-Markov product measure が sub-probability) ⟹ `E_{P_n}[P_n/q_k^n の逆数...]` を介して bad event 確率を Markov ineq で抑える。
   - **2 経路**:
     - (a) **rnDeriv 経路**: `Q_k^n := μ.map(k-Markov構成)`, `lintegral_rnDeriv_le` で `∫ (dQ/dP_n) dP_n ≤ 1`。要・離散 singleton-ratio = rnDeriv の同定補題 (新規 ~30-50 行) + `Q_k^n` を実際に Measure として構成 (~40 行)。
     - (b) **離散和直接経路**: `∑_{x^n ∈ (Fin n → α)} q_k^n(x^n) ≤ 1` を Fintype 上の有限和で示す (`condDistrib` の `IsMarkovKernel` から各因子和 = 1、Fubini-tonelli で積)。`meas_le_lintegral₀` に直接乗る形。bridge 補題不要だが telescoping 計算が重い。
   - 推奨: **(b) 離散和直接**。`condDistrib ... y` が `IsProbabilityMeasure` (本 repo `integral_pmfLogCond...` で既に `inferInstance` 利用、`SMBChainRule.lean:345`) なので各 factor の正規化が即出る。rnDeriv の bridge を避けられる。
   - 落とし穴: k-Markov product `q_k^n` の telescoping `∏` を Lean で扱う際の `Finset.prod_range_succ` 帰納 + ENNReal/Real 往復。ここで詰まると撤退ライン (下記)。

3. **limsup direction 主証明** — 工数 ~60-100 行
   - `ae_eventually_notMem` + (D.1) + (D.2) を combine。`H_k + ε` 上界を全 `n` 大で取り、`limsup ≤ H_k + ε`。k → ∞ で `entropyRate_eq_lim_condEntropy`、ε → 0。off-by-one 正規化吸収を含む。

4. **liminf direction 対称形** — 工数 ~60-100 行
   - 計画は Fatou/DCT 経由。limsup と非対称 (q_k^n は上界用、liminf は別構成 or 真の `pmfLogCond` の Birkhoff `∑ pmfLogCond p i → ` を直接使う)。
   - **観察**: liminf 側は実は `log_block_eq_sum_pmfLogCond` + Birkhoff per-level の Cesàro で `liminf ≥ entropyRate` がより素直に出る可能性 (真の chain rule をそのまま Cesàro)。limsup より軽いかもしれない。要検討。

5. **sandwich → 主定理 wiring** — 工数 ~30-50 行
   - 4 仮説を `shannon_mcmillan_breiman_of_sandwich` に渡すだけ。`h_bdd_above`/`h_bdd_below` は収束 (liminf/limsup 有界) から自動。

**合計見積**: 270-460 行 (計画書 400-550 行と整合)、~2-3 セッション。

---

## 撤退ラインへの距離

親計画 (`...phase-d-plan.md:80`) の撤退ライン:

> (D.2) likelihood ratio 形が Mathlib に gap 多すぎ → "Algoet-Cover 仮説形" SMB
> (Markov ineq + Borel-Cantelli を hypothesis にとり、本体は組み立てのみ) で
> hypothesis pass-through MVP (~100 行)、自前は別 plan へ。

**判定: 発動リスク = 中（条件付きで非発動を見込む）。**

- **非発動の根拠**: D.2 で必要な Mathlib 道具 (Borel–Cantelli `ae_eventually_notMem`, Markov `meas_ge_le_lintegral_div`/`meas_le_lintegral₀`, rnDeriv `lintegral_rnDeriv_le`) は **全て実在**し、型クラス leak も無い (確認済み)。likelihood-ratio ≤ 1 は離散和直接経路 (上記 2b) なら `condDistrib` の `IsProbabilityMeasure` から組める。
- **発動トリガー (新規撤退ライン提案)**: 上記「自作 2」(likelihood-ratio ≤ 1) の **離散和 telescoping `∑_{x^n} q_k^n ≤ 1` が着手 1 セッション内に通らない** 場合 → D.2 を「`∑ μ(bad_n) < ∞` を hypothesis に取る Algoet-Cover 半仮説形」に縮退し、limsup/liminf wiring (D.3-D.5) のみ無条件で publish (~120 行)。likelihood-ratio 本体は別 plan へ。
  - これでも sandwich wiring + Borel–Cantelli 適用部は無条件で残るので、計画書の純 pass-through MVP よりは前進。

---

## 着手 skeleton

`InformationTheory/Shannon/SMBSandwich.lean`（新規）の出だし:

```lean
import InformationTheory.Shannon.Stationary
import InformationTheory.Shannon.EntropyRate
import InformationTheory.Shannon.SMBChainRule
import InformationTheory.Shannon.ShannonMcMillanBreiman
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# SMB Algoet–Cover sandwich (Phase D.2-D.5): discharge the 4 hypotheses
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- k-Markov approximation per-step conditional log-likelihood (D.1). -/
noncomputable def pmfLogCondMarkov
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (k i : ℕ) : Ω → ℝ :=
  pmfLogCond μ p (min k i) ∘ p.T^[i - min k i]   -- 要 measurability/積分性確認

/-- D.2 crux: k-Markov likelihood ratio has expectation ≤ 1 (sub-probability). -/
theorem markov_likelihood_ratio_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (k n : ℕ) :
    True := by sorry   -- 実体: ∑_{x^n} q_k^n(x^n) ≤ 1 → bad event summability

/-- D.3: limsup ≤ entropyRate. -/
theorem smb_limsup_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess := by sorry

/-- D.4: liminf ≥ entropyRate. -/
theorem smb_liminf_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop := by sorry

/-- D.5: unconditional Shannon–McMillan–Breiman. -/
theorem shannon_mcmillan_breiman
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess)) := by sorry

end InformationTheory.Shannon
```

最初に割るべき `sorry` は `smb_liminf_ge` (上記 観察より limsup より軽い可能性) か、
crux `markov_likelihood_ratio_le_one` の離散和 (2b 経路)。

---

## まとめ

- 在庫: `docs/shannon/smb-phase-d-sandwich-inventory.md` (このファイル)
- 既存率: **~85% (本 repo 部品 10/10 + Mathlib 部品 7/8、likelihood-ratio 期待値 ≤ 1 のみ自作)**
- 自作必要: **4 件** (pmfLogCondMarkov / likelihood-ratio≤1 / limsup主証明 / liminf対称形) + wiring
- 撤退ライン発動: **条件付き no** (D.2 離散和が 1 セッションで通れば非発動)
- 最大リスク: **D.2 の `∑_{x^n} q_k^n ≤ 1` (k-Markov sub-probability normalization)** の Lean telescoping。Mathlib に likelihood-ratio 専用 lemma は無く (`likelihoodRatio` `Found 0`)、`condDistrib` の `IsProbabilityMeasure` から手で組む。rnDeriv 経由 (`lintegral_rnDeriv_le`) は singleton-ratio=rnDeriv の bridge 補題が新規で要るため離散和直接の方が安全。
- **型クラス leak: 無し。`Ergodic` は片側 `MeasurePreserving f μ μ` のみ要求 (`Mathlib/Dynamics/Ergodic/Ergodic.lean:50` 確認)、両側 shift/`[Invertible]`/`StandardBorel` は不要。** Algoet–Cover 経路が backward-martingale より優れる本質的理由。
</content>
</invoke>
