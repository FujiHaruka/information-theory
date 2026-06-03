# 第3章 漸近等分配性 (Asymptotic Equipartition Property)

> **このファイルについて**
>
> 本章は Cover & Thomas *Elements of Information Theory* (2nd ed.) Chapter 3
> (Asymptotic Equipartition Property, AEP) を題材に、**検証済み Lean 定理を
> 骨格にした教科書原稿**である。本文の各主要結果には
> 「**Verified**: `定理名` (`InformationTheory/...`)」という形で、その命題に対応する
> Lean 4 + Mathlib の formal declaration を紐付けてある。
>
> **検証強度の注記** — 本章で `**Verified**` と記した定理はすべて、
> 本プロジェクトの完成判定 **proof done**（当該 declaration を含むファイルが
> `0 sorry` かつ `0 @residual`、すなわち無条件機械検証済み）を満たす。
> 紐付けた定理が属するファイル
> (`InformationTheory/Shannon/AEP.lean` /
> `InformationTheory/Shannon/StrongTypicality.lean`) は本章作成時点で
> `sorry` / `@residual` を一切含まない。
>
> **形式化の枠組み** — i.i.d. 情報源を、測度空間 `(Ω, μ)` 上の可測写像の列
> `Xs : ℕ → Ω → α` として表す（`Xs i : Ω → α` が第 `i` シンボル）。
> ブロック `X^n = (X_0, …, X_{n-1})` は結合確率変数
> `jointRV Xs n : Ω → (Fin n → α)` で与える。`μ` は確率測度
> `[IsProbabilityMeasure μ]`、アルファベット `α` は有限型
> `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]`。
> Mathlib に `IsIID` 述語は無いため、i.i.d. 仮定は
> **(独立)** + **(同分布)** の 2 本に分けて直接受ける:
> 独立性は「対独立」`Pairwise (fun i j => Xs i ⟂ᵢ[μ] Xs j)`
> または「相互独立」`iIndepFun (fun i => Xs i) μ`、
> 同分布性は `∀ i, IdentDistrib (Xs i) (Xs 0) μ μ`。
> 名前空間は `InformationTheory.Shannon`。エントロピー `entropy μ (Xs 0)` は
> 第2章 (`InformationTheory/Shannon/Bridge.lean`) と同じ measure-theoretic 定義
> （像測度 `μ.map (Xs 0)` の `negMulLog` 和）を用いる。

---

## 3.1 漸近等分配性 (AEP)

弱大数の法則 (WLLN) を経験エントロピー推定量に適用すると、i.i.d. 情報源に対して
\[
-\frac{1}{n}\log p(X_0, X_1, \dots, X_{n-1}) \longrightarrow H(X)
\]
が成り立つ。本ライブラリでは「シンボルごとの対数尤度」
`logLikelihood μ Xs i ω = -\log P(X_i(ω))` を導入し、その Cesàro 平均
`(1/n) ∑_{i<n} (-\log P(X_i))` の収束として AEP を述べる。
ここで `P = μ.map (Xs 0)` は情報源の周辺分布。

### 性質: 対数尤度の期待値はエントロピー

各補題の土台として、対数尤度の期待値がエントロピーに一致することを示す
（\(\mathbb{E}[-\log P(X_0)] = H(X)\)）。

**Verified**: `integral_logLikelihood_zero` (`InformationTheory/Shannon/AEP.lean`)

```lean
lemma integral_logLikelihood_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    ∫ ω, logLikelihood μ Xs 0 ω ∂μ = entropy μ (Xs 0)
```

### AEP — ほとんど確実な収束 (a.s. convergence)

経験エントロピー推定量はエントロピー `H(X)` にほとんど確実に収束する
（Cover & Thomas Theorem 3.1.1、強形）。Mathlib の強大数の法則
`strong_law_ae_real` を `Y_i := -\log P(X_i)` に適用して得る。

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

### AEP — 確率収束 (convergence in probability)

教科書本文 (Theorem 3.1.1) が述べる弱形。a.s. 収束から
`tendstoInMeasure_of_tendsto_ae` で導く。任意の `ε > 0` に対し、推定量が
`H(X)` から `ε` 以上離れる事象の確率が 0 に収束する。

**Verified**: `aep_inProbability` (`InformationTheory/Shannon/AEP.lean`)

```lean
theorem aep_inProbability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | ε ≤ |((∑ i ∈ Finset.range n, logLikelihood μ Xs i ω) / n)
                                  - entropy μ (Xs 0)|})
      atTop
      (𝓝 0)
```

---

## 3.2 典型集合 (Typical Set) — 弱典型性

**典型集合** \(T_\varepsilon^{(n)}\) は、経験エントロピーが真のエントロピー `H(X)` から
`ε` 未満しか離れていないブロック `x \in \mathcal{X}^n` の集合である:
\[
T_\varepsilon^{(n)} = \left\{ x : \left| -\tfrac1n \log p(x) - H(X) \right| < \varepsilon \right\}.
\]
本ライブラリでは `pmfLog μ Xs (x i) = -\log P(x_i)` を用い、ブロック
`x : Fin n → α` 上の集合として定義する。

**Verified (定義)**: `typicalSet` (`InformationTheory/Shannon/AEP.lean`)

```lean
noncomputable def typicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    Set (Fin n → α) :=
  { x | |(∑ i : Fin n, pmfLog μ Xs (x i)) / n - entropy μ (Xs 0)| < ε }
```

有限離散空間 `Fin n → α` の部分集合なので、可測性は自明に従う。

**Verified**: `measurableSet_typicalSet` (`InformationTheory/Shannon/AEP.lean`)

```lean
theorem measurableSet_typicalSet
    (μ : Measure Ω)
    (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    MeasurableSet (typicalSet μ Xs n ε)
```

### 性質 (1): 典型集合の確率は 1 に収束

Cover & Thomas Theorem 3.1.2(1)。ブロック `X^n` が典型集合に入る確率は
`n → ∞` で 1 に収束する。`aep_inProbability` の補事象として得る。

**Verified**: `typicalSet_prob_tendsto_one` (`InformationTheory/Shannon/AEP.lean`)

```lean
theorem typicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε})
      atTop
      (𝓝 1)
```

### 性質 (2): 各典型ブロックの確率 \(p(x) \approx 2^{-nH}\)

Cover & Thomas Theorem 3.1.2(2)。典型ブロック `x \in T_\varepsilon^{(n)}` の確率は
両側から指数的に挟まれる:
\[
2^{-n(H+\varepsilon)} \le p(x) \le 2^{-n(H-\varepsilon)}.
\]
本ライブラリでは `2^x` ではなく `Real.exp` で述べる（底変換で教科書形に戻る）。
上界・下界はそれぞれ独立の定理。積測度への分解
`μ.map (jointRV Xs n) = Measure.pi (μ.map (Xs ·))` が必要なため、対独立ではなく
**相互独立** `iIndepFun` を要求する。また周辺分布のフルサポート
`hpos : ∀ x, 0 < P(x)`（`Real.log 0 = 0` 規約のもとでサポート外点が下界を壊すため）
を仮定する。

**上界 (Verified)**: `typicalSet_prob_le` (`InformationTheory/Shannon/AEP.lean`)

```lean
theorem typicalSet_prob_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε : ℝ}
    (x : Fin n → α) (hx : x ∈ typicalSet μ Xs n ε) :
    (μ.map (jointRV Xs n)).real {x}
      ≤ Real.exp (- (n : ℝ) * (entropy μ (Xs 0) - ε))
```

**下界 (Verified)**: `typicalSet_prob_ge` (`InformationTheory/Shannon/AEP.lean`)

```lean
theorem typicalSet_prob_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε : ℝ}
    (x : Fin n → α) (hx : x ∈ typicalSet μ Xs n ε) :
    Real.exp (- (n : ℝ) * (entropy μ (Xs 0) + ε))
      ≤ (μ.map (jointRV Xs n)).real {x}
```

### 性質 (3): 典型集合の要素数 \(|T_\varepsilon^{(n)}| \approx 2^{nH}\)

Cover & Thomas Theorem 3.1.2(3)。典型集合の要素数も両側から指数的に挟まれる:
\[
(1-\eta)\,2^{n(H-\varepsilon)} \le |T_\varepsilon^{(n)}| \le 2^{n(H+\varepsilon)}.
\]

**上界 (Verified)**: `typicalSet_card_le` (`InformationTheory/Shannon/AEP.lean`)。
全ブロック確率の和 = 1 と性質(2)下界から。下界 `hpos` のみで足り、独立性は不要。

```lean
theorem typicalSet_card_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ) ≤
      Real.exp ((n : ℝ) * (entropy μ (Xs 0) + ε))
```

**下界 (Verified)**: `typicalSet_card_ge` (`InformationTheory/Shannon/AEP.lean`)。
典型集合の確率 `≥ 1-η` を仮定（性質(1)から `n` 大で成立）し、性質(2)上界と組む。

```lean
theorem typicalSet_card_ge
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (n : ℕ) {ε η : ℝ}
    (hμ : (1 - η) ≤ (μ.map (jointRV Xs n)).real (typicalSet μ Xs n ε)) :
    (1 - η) * Real.exp ((n : ℝ) * (entropy μ (Xs 0) - ε))
      ≤ ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
```

---

## 3.3 データ圧縮への帰結 (Data Compression / Source Coding)

Cover & Thomas Section 3.2。典型集合に約 `2^{nH}` 個の要素しか無いという事実から、
情報源を 1 シンボルあたり約 `H(X)` ビットで符号化できることが従う。本ライブラリは
ブロック符号 `(M_n, c_n, d_n)`（符号化 `c_n : \mathcal{X}^n → \{1,…,M_n\}`、
復号 `d_n`）を組み、レート `\log M_n / n` と誤り確率の両面で源符号化定理を完結させる。

### 達成可能性 (Achievability): \(R > H\) なら誤り確率 → 0

エントロピーより大きいレート `R > H` に対し、レートが `R` に収束し誤り確率が
0 に収束するブロック符号族が存在する（典型集合符号化）。

**Verified**: `source_coding_achievability` (`InformationTheory/Shannon/AEP.lean`)

```lean
theorem source_coding_achievability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {R : ℝ} (hR : entropy μ (Xs 0) < R) :
    ∃ M : ℕ → ℕ, ∃ _hM_pos : ∀ n, 0 < M n,
    ∃ c : ∀ n, (Fin n → α) → Fin (M n),
    ∃ d : ∀ n, Fin (M n) → (Fin n → α),
      Tendsto (fun n => Real.log (M n : ℝ) / n) atTop (𝓝 R) ∧
      Tendsto
        (fun n => InformationTheory.MeasureFano.errorProb μ
                    (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
        atTop (𝓝 0)
```

### 弱逆定理 (Weak Converse): 誤り確率 → 0 なら \(\liminf R_n \ge H\)

誤り確率が 0 に収束する符号は、漸近レートがエントロピーを下回れない。
ファノの不等式 (`InformationTheory.MeasureFano`、第2章 2.10) を用いて導く。
レートが一様に上に有界 (`hM_bdd`) なことを前提にする。

**Verified**: `source_coding_converse` (`InformationTheory/Shannon/AEP.lean`)

```lean
theorem source_coding_converse
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α)
    (M : ℕ → ℕ) [hM_pos : ∀ n, NeZero (M n)]
    (c : ∀ n, (Fin n → α) → Fin (M n))
    (d : ∀ n, Fin (M n) → (Fin n → α))
    (hPe_to_zero :
      Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
                          (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
              atTop (𝓝 0))
    (hM_bdd : ∃ R, ∀ n, Real.log (M n : ℝ) / n ≤ R) :
    entropy μ (Xs 0)
      ≤ Filter.liminf (fun n : ℕ => Real.log (M n : ℝ) / n) atTop
```

### 源符号化定理 (両側等号): \(\inf R = H\)

達成可能性と弱逆を統合し、達成可能なブロック源符号の漸近レートの下限が
情報源のエントロピーに一致することを述べる。「達成可能符号」は誤り確率が消え
レートが一様有界な符号族 `IsAchievableCode` として束ね、その達成レート集合
`achievableRates` の下限を取る。

**Verified (定義)**: `IsAchievableCode` (`InformationTheory/Shannon/AEP.lean`)

```lean
structure IsAchievableCode
    (μ : Measure Ω) (Xs : ℕ → Ω → α)
    (M : ℕ → ℕ)
    (c : ∀ n, (Fin n → α) → Fin (M n))
    (d : ∀ n, Fin (M n) → (Fin n → α)) : Prop where
  hM_pos : ∀ n, NeZero (M n)
  hPe_to_zero :
    Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
              (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
            atTop (𝓝 0)
  hM_bdd : ∃ R, ∀ n, Real.log (M n : ℝ) / n ≤ R
```

**Verified**: `source_coding_theorem` (`InformationTheory/Shannon/AEP.lean`)

```lean
theorem source_coding_theorem
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hcard : 2 ≤ Fintype.card α) :
    sInf (achievableRates μ Xs) = entropy μ (Xs 0)
```

（達成可能率の両側補題 `entropy_le_of_mem_achievableRates` (Phase D lift) と
`mem_achievableRates_of_gt_entropy` (Phase E lift) も形式化済み。）

---

## 3.4 強典型性 (Strong Typicality) — Cover & Thomas 11.2 先取り

C&T では強典型性は第11章で導入されるが、本ライブラリは AEP の自然な拡張として
形式化している。**強典型集合** は、各シンボル `a` の経験頻度 `N(a|x)/n`（型）が
真の確率 `P(a)` に各 `a` で一様に近いブロックの集合:
\[
A^{*(n)}_\varepsilon = \left\{ x : \forall a,\ \left| \tfrac{N(a|x)}{n} - P(a) \right| \le \varepsilon \right\}.
\]
`typeCount x a` は `x` に現れる `a` の個数。

**Verified (定義)**: `stronglyTypicalSet` (`InformationTheory/Shannon/StrongTypicality.lean`)

```lean
noncomputable def stronglyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    Set (Fin n → α) :=
  { x | ∀ a : α,
      |(typeCount x a : ℝ) / n - (μ.map (Xs 0)).real {a}| ≤ ε }
```

**Verified**: `measurableSet_stronglyTypicalSet`
(`InformationTheory/Shannon/StrongTypicality.lean`)

```lean
theorem measurableSet_stronglyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    MeasurableSet (stronglyTypicalSet μ Xs n ε)
```

### 性質 (1): 強典型集合の確率は 1 に収束

各シンボルの指標 `letterIndicator` に WLLN を適用し、有限アルファベット上で
union bound を取って「全シンボル同時に集中」を得る。

**Verified**: `stronglyTypicalSet_prob_tendsto_one`
(`InformationTheory/Shannon/StrongTypicality.lean`)

```lean
theorem stronglyTypicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε})
      atTop (𝓝 1)
```

### 強典型 ⟹ 弱典型 (橋渡し)

強典型ブロックは（`L := ∑_a |\log P(a)|` のスケール込みで）弱典型でもある:
`ε · L < ε'` なら `A^*_ε ⊆ T_{ε'}`。これにより弱典型集合の要素数上界
`typicalSet_card_le` がそのまま強典型集合の上界を与える。

**Verified**: `stronglyTypicalSet_subset_typicalSet`
(`InformationTheory/Shannon/StrongTypicality.lean`)

```lean
lemma stronglyTypicalSet_subset_typicalSet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {n : ℕ} (hn : 0 < n) {ε ε' : ℝ}
    (h_bound : ε * logSumAbs μ Xs < ε') :
    stronglyTypicalSet μ Xs n ε ⊆ typicalSet μ Xs n ε'
```

### 性質 (2): 要素数の下界 \(|A^*_\varepsilon| \gtrsim 2^{n(H - \varepsilon L)}\)

任意の `η, δ > 0` に対し、`n` が十分大きければ
`(1-η)·\exp(n·(H - εL - δ)) ≤ |A^*_ε^n|`。

**Verified**: `stronglyTypicalSet_card_ge_eventually`
(`InformationTheory/Shannon/StrongTypicality.lean`)

```lean
theorem stronglyTypicalSet_card_ge_eventually
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep_full : iIndepFun (fun i => Xs i) μ)
    (hindep_pair : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a})
    {ε δ η : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 - η) * Real.exp ((n : ℝ) * (entropy μ (Xs 0) - ε * logSumAbs μ Xs - δ))
        ≤ ((stronglyTypicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
```

---

## 本章で未形式化の項目

Cover & Thomas Ch.3 のうち、本章に対応する独立した proof-done 定理を
確認できなかった項目を正直に記す。

- **強典型集合の要素数上界の独立定理**: ロードマップが想起する
  `stronglyTypicalSet_card_le` という declaration は **実コードに存在しない**。
  上界は `stronglyTypicalSet_subset_typicalSet`（強 ⊆ 弱）と弱典型側の
  `typicalSet_card_le` の合成で得られる形になっており、独立した名前付き定理
  としては未形式化（本章では合成ルートのみ紐付け）。
- **連続情報源の AEP / 微分エントロピー版 (C&T 8.2 / 9.x)**: 本章スコープは
  離散・有限アルファベットに限る。連続版は future work（ロードマップ Ch.9 の
  continuous AEP は「量の壁」として scope-out 済み）。
- **一般定常エルゴード過程の AEP (Shannon–McMillan–Breiman, C&T 16.8)**:
  本章は i.i.d. ソースのみ。SMB 定理は別ファイル
  (`ShannonMcMillanBreiman.lean` 等) で扱われ、本章では未紐付け。

---

## 所見 (原稿生成で気づいた prose ↔ formal の乖離)

1. **ロードマップの代表名 `stronglyTypicalSet_card_le` が実在しない**:
   roadmap の Ch.3 行は代表として `typicalSet, stronglyTypicalSet` を挙げるが、
   強典型側の要素数上界は独立定理ではなく「強 ⊆ 弱 包含 + 弱側 card 上界」の
   合成で実装されている。教科書 prose の「3 主定理（確率→1・上界・下界）」を
   そのまま formal declaration に 1:1 対応づけられず、橋渡し補題
   `stronglyTypicalSet_subset_typicalSet` を経由する必要がある。

2. **i.i.d. 仮定が定理ごとに「対独立」と「相互独立」で分かれる**:
   WLLN ベースの結果（`aep_ae` / `aep_inProbability` /
   `typicalSet_prob_tendsto_one` / `stronglyTypicalSet_prob_tendsto_one`）は
   対独立 `Pairwise (Xs i ⟂ᵢ Xs j)` で足りるが、積測度分解を要する点ごとの
   確率評価（`typicalSet_prob_le/ge`、`typicalSet_card_ge`、源符号化系）は
   **相互独立** `iIndepFun` を要求する。教科書はどちらも素朴に「i.i.d.」と
   一括するため、原稿では定理ごとに必要な独立性の強さを明示する必要がある。

3. **指数の底が `Real.exp`（自然対数）で、教科書の `2^{nH}` と表層が異なる**:
   要素数・確率の評価はすべて `Real.exp (n·(H±ε))` 形で、教科書の \(2^{n(H\pm\varepsilon)}\)
   とは底が違う。底変換（`log` の基底）で一致するが、原稿では毎回「底変換で
   教科書形に戻る」旨の注釈が要る。

4. **フルサポート仮定 `hpos` が `Real.log 0 = 0` 規約に由来する技術的前提**:
   点ごとの確率下界・要素数評価は `∀ x, 0 < P(x)` を追加で要求する。これは
   教科書が暗黙に「support 全体」を仮定しているのを、Mathlib の `Real.log 0 = 0`
   規約のもとで明示化したもの（サポート外点が下界を壊す）。regularity 前提であり
   結論の核心を抱えるものではない。
