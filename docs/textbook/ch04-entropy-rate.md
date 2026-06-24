# 第4章 確率過程のエントロピーレート

> **このファイルについて**
>
> 本章は Cover & Thomas *Elements of Information Theory* (2nd ed.) Chapter 4
> (Entropy Rates of a Stochastic Process) を題材に、**検証済み Lean 定理を
> 骨格にした教科書原稿**である。本文の各主要結果には
> 「**Verified**: `定理名` (`InformationTheory/...`)」という形で、その命題に対応する
> Lean 4 + Mathlib の formal declaration を紐付けてある。
>
> **検証強度の注記** — 本章で `**Verified**` と記した定理はすべて、
> 本プロジェクトの完成判定 **proof done**（当該 declaration を含むファイルが
> `0 sorry` かつ `0 @residual`、すなわち無条件機械検証済み）を満たす。
> 紐付けた定理が属するファイル
> (`Stationary.lean` / `EntropyRate.lean` / `ShannonMcMillanBreiman.lean` /
> `BirkhoffErgodic.lean` / `SMBChainRule.lean` / `SMBAlgoetCover.lean` /
> `AEP.lean`) は本原稿作成時点で `sorry` / `@residual` を含まない。
>
> **形式化の枠組み** — 本ライブラリでは定常過程を、確率測度 `μ` を保つ
> 「シフト写像」 `T : Ω → Ω`（測度保存変換 `MeasurePreserving T μ μ`）と
> 単一の可測観測 `X : Ω → α` の組として表現する（構造体 `StationaryProcess`）。
> 時刻 `i` の観測は `X_i := X ∘ T^[i]` で、ブロック確率変数は
> `(X_0, …, X_{n-1}) : Ω → (Fin n → α)`。アルファベット `α` は有限型
> `[Fintype α]`、`μ` は確率測度 `[IsProbabilityMeasure μ]`。
> エルゴード性が必要な箇所では `T` のエルゴード性 (`Ergodic T μ`) を加えた
> `ErgodicProcess` を用いる。エントロピー類は第2章と同じく像測度
> `μ.map (·)` を通じた measure-theoretic 形式で定義される。
> 対応する Lean library は `InformationTheory/Shannon/`。

---

## 4.1 定常過程 (Stationary Processes)

確率過程 \(\{X_i\}\) が**定常 (stationary)** であるとは、任意の有限ブロックの結合分布が
時間シフトで不変であること、すなわち任意の \(n, \ell\) に対して
\[
\Pr[X_1 = x_1, \dots, X_n = x_n] = \Pr[X_{1+\ell} = x_1, \dots, X_{n+\ell} = x_n]
\]
が成り立つことをいう (Cover–Thomas 4.1)。

本ライブラリはこれを**測度保存力学系 (measure-preserving dynamical system)** として
形式化する。確率空間 \((\Omega, \mu)\) 上の測度を保つシフト \(T\) と観測 \(X\) を与えると、
時刻 \(i\) の観測は \(X_i := X \circ T^{i}\) で定まる。\(T\) が \(\mu\) を保つことが
定常性そのものに対応する（任意の \(i\) で \(X_i\) は \(X_0\) と同分布になる）。

**Verified (定義)**: `StationaryProcess` (`InformationTheory/Shannon/Stationary.lean`,
名前空間 `InformationTheory.Shannon`)

```lean
structure StationaryProcess (μ : Measure Ω) (α : Type*) [MeasurableSpace α] where
  /-- The shift / time-evolution map. -/
  T : Ω → Ω
  /-- The single observable; later samples are obtained by composing with `T^[i]`. -/
  X : Ω → α
  /-- `T` preserves `μ`. -/
  measurePreserving : MeasurePreserving T μ μ
  /-- The observable is measurable. -/
  measurable_X : Measurable X
```

時刻 \(i\) の観測とブロック確率変数は次のように導出される。

**Verified (定義)**: `StationaryProcess.obs` / `StationaryProcess.blockRV`
(`InformationTheory/Shannon/Stationary.lean`)

```lean
def obs (p : StationaryProcess μ α) (i : ℕ) : Ω → α :=
  p.X ∘ p.T^[i]

def blockRV (p : StationaryProcess μ α) (n : ℕ) : Ω → (Fin n → α) :=
  fun ω i => p.obs i ω
```

### エルゴード過程

定常過程のうちシフト \(T\) がさらに**エルゴード的 (ergodic)** であるものを
`ErgodicProcess` として分離する。エルゴード性は 4.4–4.5 の Shannon–McMillan–Breiman
定理で本質的に用いられる（時間平均と空間平均の一致を保証する）。

**Verified (定義)**: `ErgodicProcess` (`InformationTheory/Shannon/Stationary.lean`)

```lean
structure ErgodicProcess (μ : Measure Ω) (α : Type*) [MeasurableSpace α]
    extends StationaryProcess μ α where
  /-- `T` is ergodic for `μ`. -/
  ergodic : Ergodic T μ
```

> **注** — 教科書ではマルコフ連鎖を定常過程の代表例として扱う (4.1–4.3) が、
> 本ライブラリの中核はマルコフ連鎖固有の遷移行列ではなく、任意の定常（測度保存）
> 過程に対する一般論である。マルコフ連鎖のエントロピーレートの閉形式
> \(H = -\sum_{ij} \mu_i P_{ij} \log P_{ij}\)（Cover–Thomas 4.2.4）は
> 本章では独立定理として未紐付け（「未形式化の項目」参照）。

---

## 4.2 エントロピーレート (Entropy Rate)

定常過程のエントロピーレートには 2 つの定義がある (Cover–Thomas 4.2)。第一は
ブロックエントロピーの時間平均
\[
H(\mathcal{X}) = \lim_{n \to \infty} \frac{1}{n} H(X_1, X_2, \dots, X_n),
\]
第二は条件付きエントロピーの極限
\[
H'(\mathcal{X}) = \lim_{n \to \infty} H(X_n \mid X_{n-1}, \dots, X_1).
\]
定常過程では両者が存在し、しかも一致する（Cover–Thomas Theorem 4.2.1）。

### ブロックエントロピーと条件付きエントロピーテール（定義）

ブロックエントロピー \(H_n = H(X_0, \dots, X_{n-1})\) は、ブロック確率変数の
（第2章の）エントロピーとして定義する。

**Verified (定義)**: `blockEntropy` (`InformationTheory/Shannon/EntropyRate.lean`)

```lean
noncomputable def blockEntropy (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : ℝ :=
  entropy μ (p.blockRV n)
```

各ステップの条件付きエントロピー \(H(X_n \mid X_0, \dots, X_{n-1})\)
（**conditional entropy tail**）は、第2章の `condEntropy`（名前空間
`InformationTheory.MeasureFano`）を用いて定義する。

**Verified (定義)**: `conditionalEntropyTail` (`InformationTheory/Shannon/EntropyRate.lean`)

```lean
noncomputable def conditionalEntropyTail
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (n : ℕ) : ℝ :=
  InformationTheory.MeasureFano.condEntropy μ (p.obs n) (p.blockRV n)
```

エントロピーレートは \(H_n / n\) の極限として定義する。`Filter.limUnder` を用いるため、
極限が実際に存在することは別途 `entropyRate_exists_of_stationary` で保証する。

**Verified (定義)**: `entropyRate` (`InformationTheory/Shannon/EntropyRate.lean`)

```lean
noncomputable def entropyRate (μ : Measure Ω) (p : StationaryProcess μ α) : ℝ :=
  Filter.atTop.limUnder (fun n : ℕ => blockEntropy μ p n / n)
```

### チェイン則 \(H_{n+1} = H_n + H(X_n \mid X_{<n})\)

ブロックエントロピーは「これまでの履歴」と「次の 1 ステップの条件付きエントロピー」に
分解される。これがエントロピーレート存在証明のエンジンである。

**Verified**: `blockEntropy_succ_chain_rule` (`InformationTheory/Shannon/EntropyRate.lean`)

```lean
theorem blockEntropy_succ_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    blockEntropy μ p (n + 1)
      = blockEntropy μ p n + conditionalEntropyTail μ p n
```

反復適用すると、ブロックエントロピーは条件付きエントロピーテールの有限和になる
（\(H_n = \sum_{i<n} H(X_i \mid X_{<i})\)、Cover–Thomas 4.2.2 の鎖）。
基底ケース \(H_0 = 0\) も形式化済み (`blockEntropy_zero`)。

**Verified**: `blockEntropy_eq_sum_conditionalEntropyTail`
(`InformationTheory/Shannon/EntropyRate.lean`)

```lean
theorem blockEntropy_eq_sum_conditionalEntropyTail
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    blockEntropy μ p n = ∑ i ∈ Finset.range n, conditionalEntropyTail μ p i
```

### 条件付きエントロピーテールの単調減少 (Cover–Thomas Theorem 4.2.1, 第1段)

定常過程では \(H(X_n \mid X_{n-1}, \dots, X_0)\) が \(n\) について**単調非増加**である。
証明は、定常性（シフトによる結合分布の不変性）で \(H(X_n \mid X_{<n})\) を
\(H(X_{n+1} \mid X_1, \dots, X_n)\) に書き換え、第2章の「条件を増やすとエントロピーは
増えない」 (`condEntropy_le_condEntropy_of_pair`) を適用する。

**Verified**: `conditionalEntropyTail_antitone` (`InformationTheory/Shannon/EntropyRate.lean`)

```lean
theorem conditionalEntropyTail_antitone
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    Antitone (conditionalEntropyTail μ p)
```

各テールは非負でもある (`conditionalEntropyTail_nonneg`)。

### エントロピーレートの存在 (Cover–Thomas Theorem 4.2.1, 第2段)

条件付きエントロピーテールは単調非増加かつ下に有界（\(\ge 0\)）なので、ある極限
\(L\) に収束する。チェイン則の和分解と**チェザロ平均 (Cesàro mean)** により、
ブロックエントロピーの時間平均 \(H_n / n\) も同じ \(L\) に収束する。これが
\(\lim \frac{1}{n}H(X^n) = \lim H(X_n \mid X^{n-1})\) という 4.2 の同値性の核心である。

**Verified**: `entropyRate_exists_of_stationary` (`InformationTheory/Shannon/EntropyRate.lean`)

```lean
theorem entropyRate_exists_of_stationary
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    ∃ H : ℝ, Tendsto (fun n : ℕ => blockEntropy μ p n / n) atTop (𝓝 H)
```

### 2 つの定義の一致 \(\lim H(X_n \mid X^{n-1}) = H(\mathcal{X})\)

存在が分かれば、条件付きエントロピーテール列がまさに `entropyRate` に収束することが
言える。これが Cover–Thomas Theorem 4.2.1 の結論
\(H(\mathcal{X}) = H'(\mathcal{X})\)（2 つの定義の一致）の形式化である。

**Verified**: `entropyRate_eq_lim_condEntropy` (`InformationTheory/Shannon/EntropyRate.lean`)

```lean
theorem entropyRate_eq_lim_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    Tendsto (conditionalEntropyTail μ p) atTop (𝓝 (entropyRate μ p))
```

---

## 4.4 バーコフのエルゴード定理 (Birkhoff's Ergodic Theorem)

Shannon–McMillan–Breiman 定理の解析的な心臓部はバーコフの個別エルゴード定理である
（Cover–Thomas では 16.8 の証明で用いられる）。確率を保つエルゴード変換 \(T\) と
可積分な観測 \(f\) に対し、**時間平均が空間平均（期待値）に概収束**する:
\[
\frac{1}{n+1}\sum_{i=0}^{n} f(T^{i}\omega) \xrightarrow{\text{a.s.}} \int f \, d\mu.
\]

本ライブラリではバーコフ時間平均を次のように定義する（分母 \(n+1\) で \(n = 0\) の
ゼロ割を回避する）。

**Verified (定義)**: `birkhoffAverageReal` (`InformationTheory/Shannon/BirkhoffErgodic.lean`)

```lean
noncomputable def birkhoffAverageReal (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (∑ i ∈ Finset.range (n + 1), f (T^[i] ω)) / (n + 1 : ℝ)
```

### 極大エルゴード不等式 (Maximal Ergodic Inequality)

バーコフ定理の標準的証明は、Garsia による極大エルゴード不等式を経由する。
有限部分和の上限が正となる集合上で \(f\) の積分が非負になる:

**Verified**: `maximal_ergodic_inequality` (`InformationTheory/Shannon/BirkhoffErgodic.lean`)

```lean
theorem maximal_ergodic_inequality {μ : Measure Ω} [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Measurable f) (hf_int : Integrable f μ) (n : ℕ) :
    0 ≤ ∫ ω in {ω | 0 < maxPartialSum T f n ω}, f ω ∂μ
```

### バーコフの個別エルゴード定理（無条件版）

極大不等式から有理 \(\varepsilon\) サンドイッチ
(`birkhoff_eventually_lt_integral_add` / `birkhoff_eventually_gt_integral_sub`)
と Mathlib の `Ergodic.ae_eq_const_of_ae_eq_comp_ae` を組み合わせ、時間平均の概収束を
**仮説なし**で導く。

**Verified**: `birkhoff_ergodic_ae` (`InformationTheory/Shannon/BirkhoffErgodic.lean`)

```lean
theorem birkhoff_ergodic_ae {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverageReal T f n ω)
      atTop (𝓝 (∫ x, f x ∂μ))
```

---

## 4.5 Shannon–McMillan–Breiman 定理 (漸近等分割性, AEP)

定常エルゴード過程に対する **AEP (Asymptotic Equipartition Property)** は、
1 標本あたりの負の対数尤度がエントロピーレートに概収束する、というものである
（Cover–Thomas Theorem 16.8.1、第3章 AEP の定常過程への一般化）:
\[
-\frac{1}{n}\log p(X_0, X_1, \dots, X_{n-1}) \xrightarrow{\text{a.s.}} H(\mathcal{X}).
\]

本ライブラリの 1 ブロックあたり経験エントロピー推定量を `blockLogAvg` と呼ぶ。

**Verified (定義)**: `blockLogAvg` (`InformationTheory/Shannon/ShannonMcMillanBreiman.lean`)

```lean
noncomputable def blockLogAvg
    (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : Ω → ℝ :=
  fun ω => -(1 / (n : ℝ)) * Real.log ((μ.map (p.blockRV n)).real {p.blockRV n ω})
```

### 証明戦略 — サンドイッチ + 4 仮説の discharge

本ライブラリの SMB は次の構造で組み立てられている（Algoet–Cover の証明法）。
中核となるラッパーは、4 つの仮説（liminf 下界・limsup 上界・上下の概有界性）から
概収束を導く。

**Verified**: `shannon_mcmillan_breiman_of_sandwich`
(`InformationTheory/Shannon/ShannonMcMillanBreiman.lean`)

```lean
theorem shannon_mcmillan_breiman_of_sandwich
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α)
    (h_liminf : ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop)
    (h_limsup : ∀ᵐ ω ∂μ,
      Filter.limsup (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess)
    (h_bdd_above : ∀ᵐ ω ∂μ,
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
        (fun n => blockLogAvg μ p.toStationaryProcess n ω))
    (h_bdd_below : ∀ᵐ ω ∂μ,
      Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
        (fun n => blockLogAvg μ p.toStationaryProcess n ω)) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess))
```

> **注（仮説の性質）** — この 4 仮説は本ライブラリでは**すべて独立に無条件証明
> されている** discharge 定理（下記）の結論であって、結論の核心を抱えさせる
> load-bearing 仮説ではない。`shannon_mcmillan_breiman_of_sandwich` はそれらを
> `tendsto_of_le_liminf_of_limsup_le` で組み立てるだけの最終配線である。
> 本原稿作成時点ではこの 4 引数を実際に代入した「仮説なしの最終定理」declaration
> は未配線（「未形式化の項目」参照）だが、4 部品はすべて proof done である。

### 4 仮説の無条件 discharge

**(1) liminf 下界** — Algoet–Cover の両側拡張を経由して
\(H(\mathcal{X}) \le \liminf -\frac{1}{n}\log p(X^n)\) を概成立で示す。

**Verified**: `algoet_cover_liminf_bound` (`InformationTheory/Shannon/SMBAlgoetCover.lean`)

```lean
theorem algoet_cover_liminf_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      entropyRate μ p.toStationaryProcess
        ≤ Filter.liminf (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
```

**(2) limsup 上界** — \(k\)-マルコフ近似で各 \(k\) に対し
\(\limsup \le H_k = H(X_k \mid X_{<k})\) を示し、`entropyRate_eq_lim_condEntropy`
で \(k \to \infty\) として \(\limsup \le H(\mathcal{X})\) を得る。

**Verified**: `algoet_cover_limsup_bound` (`InformationTheory/Shannon/SMBAlgoetCover.lean`)

```lean
theorem algoet_cover_limsup_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.limsup (fun n => blockLogAvg μ p.toStationaryProcess n ω) Filter.atTop
        ≤ entropyRate μ p.toStationaryProcess
```

**(3)(4) 上下の概有界性** — `blockLogAvg` は各 \(n\) で非負（下に有界）、上は
\(k\)-Markov 誤差項とともに有界。

**Verified**: `blockLogAvg_bddAbove_ae` / `blockLogAvg_bddBelow_ae`
(`InformationTheory/Shannon/SMBAlgoetCover.lean`)

```lean
theorem blockLogAvg_bddAbove_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)

theorem blockLogAvg_bddBelow_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)
```

### 対数尤度のチェイン則とバーコフ的応用

サンドイッチ証明の代数的骨格は、ブロック負対数尤度を 1 ステップ条件付き負対数尤度
`pmfLogCond` の和に分解する**対数尤度のチェイン則**である。

**Verified (定義)**: `pmfLogCond` (`InformationTheory/Shannon/SMBChainRule.lean`)

```lean
noncomputable def pmfLogCond
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (i : ℕ) : Ω → ℝ :=
  fun ω => -Real.log
    ((condDistrib (p.obs i) (p.blockRV i) μ (p.blockRV i ω)).real {p.obs i ω})
```

この `pmfLogCond` の期待値が条件付きエントロピーテール \(H_l\) に一致する
（disintegration + Fubini）。

**Verified**: `integral_pmfLogCond_eq_conditionalEntropyTail`
(`InformationTheory/Shannon/SMBChainRule.lean`)

```lean
theorem integral_pmfLogCond_eq_conditionalEntropyTail
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : StationaryProcess μ α) (l : ℕ) :
    ∫ ω, pmfLogCond μ p l ω ∂μ = conditionalEntropyTail μ p l
```

ゆえに各レベル \(l\) でバーコフの定理を適用すると、`pmfLogCond p l` の時間平均が
\(H_l = H(X_l \mid X_{<l})\) に概収束する。これがサンドイッチ両辺を生む
「\(l\)-マルコフ近似」の出力である。

**Verified**: `birkhoffAverage_pmfLogCond_tendsto` (`InformationTheory/Shannon/SMBChainRule.lean`)

```lean
theorem birkhoffAverage_pmfLogCond_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) (l : ℕ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => birkhoffAverageReal p.T (pmfLogCond μ p.toStationaryProcess l) n ω)
      Filter.atTop
      (𝓝 (conditionalEntropyTail μ p.toStationaryProcess l))
```

### 期待値レベルの SMB（バーコフ不要）

a.s. 版に先立ち、期待値レベルでは `𝔼[blockLogAvg] = H_n / n` という等式が
バーコフなしで成立する。これは離散版 AEP の `integral_logLikelihood_zero` の
ブロック類似であり、期待値レベルで SMB が「正しい量」を捉えていることの確認になる。

**Verified**: `expected_blockLogAvg_eq` (`InformationTheory/Shannon/ShannonMcMillanBreiman.lean`)

```lean
theorem expected_blockLogAvg_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    {n : ℕ} (hn : 0 < n) :
    ∫ ω, blockLogAvg μ p n ω ∂μ = blockEntropy μ p n / n
```

---

## 4.補 i.i.d. 過程の AEP（第3章との接続）

i.i.d. 過程は定常エルゴード過程の最も単純な特例であり、そのエントロピーレートは
\(H(\mathcal{X}) = H(X_0)\) に退化する。第3章 AEP（独立同分布版）は大数の強法則から
直接得られ、SMB の特例として位置づけられる。参考として独立同分布版の概収束 AEP を
挙げておく。

**Verified**: `aep_ae` (`InformationTheory/Shannon/AEP.lean`)

```lean
theorem aep_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
      atTop
      (𝓝 (entropy μ (Xs 0)))
```

---

## 本章で未形式化の項目

Cover & Thomas Ch.4 のうち、本原稿のスコープ内で**独立した proof-done 定理を
確認できなかった**項目を正直に記す。

- **4.1–4.3 マルコフ連鎖固有の理論**: 遷移行列・定常分布
  \(\mu P = \mu\)、マルコフ連鎖のエントロピーレートの閉形式
  \(H = -\sum_{ij}\mu_i P_{ij}\log P_{ij}\)（Cover–Thomas 4.2.4）、
  ランダムウォークの例（4.3）は、本ライブラリの一般的測度保存過程の枠組みでは
  特例として包含されるが、マルコフ遷移行列を明示した独立 declaration は
  本章では未紐付け（未形式化）。
- **SMB の仮説なし最終定理（最終配線）**: 4 仮説の discharge 定理
  (`algoet_cover_liminf_bound` / `algoet_cover_limsup_bound` /
  `blockLogAvg_bddAbove_ae` / `blockLogAvg_bddBelow_ae`) と
  ラッパー `shannon_mcmillan_breiman_of_sandwich` はすべて proof done だが、
  これらを 1 つに結線した仮説フリーの `shannon_mcmillan_breiman` という名の
  単一 declaration は本原稿作成時点で `InformationTheory/Shannon/` に**存在しない**
  （`rg 'theorem shannon_mcmillan_breiman\b'` が 0 件）。4 部品 + ラッパーは
  揃っているので結線自体は機械的だが、未配線である点を未形式化として記す。
- **4.5 関数版 SMB / マルコフ近似定理の系**: ランダムウォークの定常分布等、
  教科書の個別例は未形式化。
- **エントロピーレートと熱力学第二法則・定常分布への収束 (4.4)**:
  本章では未紐付け（未形式化）。

---

## 所見（原稿生成で気づいた prose ↔ formal の乖離）

1. **「定常過程」が測度保存力学系として定義されている**: 教科書の
   「結合分布のシフト不変性」(`Pr[X_1..X_n] = Pr[X_{1+ℓ}..X_{n+ℓ}]`) は、本ライブラリでは
   単一観測 \(X\) と測度保存シフト \(T\) の組 (`StationaryProcess`) として与えられ、
   時刻 \(i\) の確率変数は \(X \circ T^i\) で導出される。読者の「\(\{X_i\}\) は別々の
   確率変数列」という直感とは表層が異なり、エルゴード理論との橋渡しを 1 行補足する
   必要がある。

2. **SMB が「サンドイッチ・ラッパー + 4 discharge 部品」に分解されており、
   仮説フリーの単一定理が未配線**: 教科書 Theorem 16.8.1 は 1 本の主張だが、
   本ライブラリでは `shannon_mcmillan_breiman_of_sandwich`（4 仮説を受け取る配線）と
   4 つの discharge 定理（各仮説を無条件証明）に分かれている。すべて proof done だが、
   両者を結線した「`theorem shannon_mcmillan_breiman`」という名の最終定理は実在しない。
   原稿側では「主張は完成済みだが最終 1 行の結線だけが未配線」という微妙な状態を
   正直に書き分ける必要があった。

3. **docstring が言及する `tendsto_expected_blockLogAvg` は実在しない**:
   `ShannonMcMillanBreiman.lean` の冒頭 docstring と `LempelZiv78.lean` のコメントが
   `tendsto_expected_blockLogAvg`（期待値版 SMB の収束）に言及するが、実 declaration を
   `rg` しても本体が存在しない（期待値「等式」 `expected_blockLogAvg_eq` までは実在）。
   roadmap・docstring の「代表名」が実コードと乖離する典型例で、本原稿では実在する
   `expected_blockLogAvg_eq` のみを引用した。

4. **`BirkhoffErgodic.lean` の `rg -c sorry` が「1」と出るが実 `sorry` はゼロ**:
   行 1007 の docstring に登場する語 "sorry-migration"（過去の移行フェーズ名）が
   素朴な `rg 'sorry'` にヒットする。実際の `sorry` タクティクや `@residual` は 0 で
   proof done。grep ベースの proof-done 判定は単語境界・コメント混入に注意が必要、
   という実例（本原稿では `\bsorry\b` で行を直接確認した）。

5. **バーコフ平均の分母が \(n+1\)**: `birkhoffAverageReal` は
   \(\frac{1}{n+1}\sum_{i=0}^{n}\) と定義され、教科書の \(\frac{1}{n}\sum_{i=0}^{n-1}\)
   とは index がずれる（\(n=0\) ゼロ割回避のため）。極限としては同値だが、
   有限 \(n\) の式を verbatim 対照する際にオフバイワンの注意が要る。
