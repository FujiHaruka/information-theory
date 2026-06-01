# 第2章 エントロピー・相互情報量・データ処理不等式

> **このファイルについて (パイロット原稿)**
>
> 本章は Cover & Thomas *Elements of Information Theory* (2nd ed.) Chapter 2 を
> 題材に、**検証済み Lean 定理を骨格にした教科書原稿**が成立するかを検証する
> パイロットである。本文の各主要結果には
> 「**Verified**: `定理名` (`Common2026/...`)」という形で、その命題に対応する
> Lean 4 + Mathlib の formal declaration を紐付けてある。
>
> **検証強度の注記** — 本章で `**Verified**` と記した定理はすべて、
> 本プロジェクトの完成判定 **proof done**（当該 declaration を含むファイルが
> `0 sorry` かつ `0 @residual`、すなわち無条件機械検証済み）を満たす。
> 紐付けた定理が属するファイル
> (`Entropy.lean` / `MutualInfo.lean` / `MIChainRule.lean` /
> `CondMutualInfo.lean` / `DPI.lean` / `CondEntropyMemoryless.lean` /
> `Bridge.lean` / `MaxEntropy.lean` / `Fano/Measure.lean` / `Fano/Core.lean`)
> は本パイロット作成時点で `sorry` / `@residual` を含まない。
>
> **形式化の枠組み** — 本ライブラリでは確率変数を測度空間 `(Ω, μ)` 上の可測写像
> `Xs : Ω → X` として表現し、エントロピー等は像測度 `μ.map Xs` を通じて定義する
> （pmf を直接扱わず measure-theoretic 形式）。`μ` は確率測度
> `[IsProbabilityMeasure μ]`、アルファベット `X` は有限型 `[Fintype X]`
> （連続版の差分エントロピーは Ch.8、本章では離散のみ）。
> 対応する Lean library は `Common2026/Shannon/` および `Common2026/Fano/`。

---

## 2.1 エントロピー (Entropy)

離散確率変数 \(X\)（有限アルファベット \(\mathcal{X}\) に値をとる）のエントロピーは

\[
H(X) = -\sum_{x \in \mathcal{X}} p(x) \log p(x).
\]

本ライブラリでは `negMulLog p = -p \log p` を用いて、像測度 `μ.map Xs` の各 atom
質量の和として定義する。

**Verified (定義)**: `entropy` (`Common2026/Shannon/Bridge.lean`)

```lean
noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ :=
  ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})
```

### 性質: 非負性

\(0 \le p(x) \le 1\) より各項 `negMulLog p ≥ 0`、ゆえに \(H(X) \ge 0\)。

**Verified**: `entropy_nonneg` (`Common2026/Shannon/Bridge.lean`)

```lean
lemma entropy_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (hXs : Measurable Xs) : 0 ≤ entropy μ Xs
```

### 性質: 一様分布での上界 \(H(X) \le \log|\mathcal{X}|\)

エントロピーはアルファベットサイズの対数を超えない。これは
\(D(P \,\|\, U) \ge 0\)（一様分布 \(U\) への KL ダイバージェンスの非負性、Gibbs 不等式）
の帰結である。

**Verified**: `entropy_le_log_card` (`Common2026/Shannon/MaxEntropy.lean`)

```lean
theorem entropy_le_log_card
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    entropy μ X ≤ Real.log (Fintype.card α)
```

等号成立条件（像測度が一様分布であること）も形式化済み。

**Verified**: `entropy_eq_log_card_iff` (`Common2026/Shannon/MaxEntropy.lean`)

```lean
theorem entropy_eq_log_card_iff
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    entropy μ X = Real.log (Fintype.card α)
      ↔ μ.map X = uniformOn (Set.univ : Set α)
```

---

## 2.2 結合エントロピー・条件付きエントロピーとチェイン則

### 条件付きエントロピー (Conditional Entropy)

\[
H(X \mid Y) = \sum_y p(y) H(X \mid Y = y)
            = -\sum_{x,y} p(x,y) \log p(x \mid y).
\]

本ライブラリでは条件付き分布 `condDistrib Xs Yo μ y : Measure X` に対する各 \(y\) ごとの
離散エントロピーを、周辺 `μ.map Yo` で積分した形で定義する。

**Verified (定義)**: `condEntropy` (`Common2026/Fano/Measure.lean`,
名前空間 `InformationTheory.MeasureFano`)

```lean
def condEntropy (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) : ℝ :=
  ∫ y, ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x}) ∂(μ.map Yo)
```

### チェイン則 \(H(X, Y) = H(X) + H(Y \mid X)\)

結合エントロピー（ペア確率変数 `(Xs, Yo)` のエントロピー）が
周辺エントロピーと条件付きエントロピーの和に分解される。

**Verified**: `entropy_pair_eq_entropy_add_condEntropy`
(`Common2026/Shannon/Entropy.lean`)

```lean
theorem entropy_pair_eq_entropy_add_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    entropy μ (fun ω => (Xs ω, Yo ω))
      = entropy μ Xs + InformationTheory.MeasureFano.condEntropy μ Yo Xs
```

### 条件付けでエントロピーは増えない \(H(X \mid Y, Z) \le H(X \mid Y)\)

「条件 (conditioning) は平均エントロピーを減らす」(Cover & Thomas Thm 2.6.5
の系)。本ライブラリでは条件付き相互情報量の非負性から導く。

**Verified**: `condEntropy_le_condEntropy_of_pair`
(`Common2026/Shannon/Entropy.lean`)

```lean
theorem condEntropy_le_condEntropy_of_pair
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
    InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
      ≤ InformationTheory.MeasureFano.condEntropy μ Xs Yo
```

---

## 2.3 相互情報量 (Mutual Information)

\[
I(X; Y) = \sum_{x,y} p(x,y) \log \frac{p(x,y)}{p(x)p(y)}
        = D\!\left(p(x,y) \,\big\|\, p(x)p(y)\right).
\]

本ライブラリでは、結合分布の周辺積に対する KL ダイバージェンスとして
（Mathlib の `klDiv` を用いて）直接定義する。`ℝ≥0∞` 値である点に注意。

**Verified (定義)**: `mutualInfo` (`Common2026/Shannon/MutualInfo.lean`)

```lean
noncomputable def mutualInfo
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ :=
  klDiv (μ.map (fun ω => (Xs ω, Yo ω)))
        ((μ.map Xs).prod (μ.map Yo))
```

### 性質: 非負性・対称性・有限性

\(I(X; Y) \ge 0\)。`klDiv` が `ℝ≥0∞` 値であるため、定義から直ちに従う。

**Verified**: `mutualInfo_nonneg` (`Common2026/Shannon/MutualInfo.lean`)

```lean
theorem mutualInfo_nonneg (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) :
    0 ≤ mutualInfo μ Xs Yo
```

\(I(X; Y) = I(Y; X)\)（対称性）。

**Verified**: `mutualInfo_comm` (`Common2026/Shannon/MutualInfo.lean`)

```lean
theorem mutualInfo_comm
    (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = mutualInfo μ Yo Xs
```

有限アルファベット上では \(I(X; Y) < \infty\)（`≠ ∞`）。

**Verified**: `mutualInfo_ne_top` (`Common2026/Shannon/MutualInfo.lean`)

```lean
theorem mutualInfo_ne_top
    [Fintype X] [MeasurableSingletonClass X]
    [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo ≠ ∞
```

### \(I(X; Y) = 0 \iff X \perp Y\)

相互情報量がゼロであることと独立であることは同値。

**Verified**: `mutualInfo_eq_zero_iff_indep` (`Common2026/Shannon/MutualInfo.lean`)

```lean
theorem mutualInfo_eq_zero_iff_indep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = 0 ↔ IndepFun Xs Yo μ
```

### エントロピーと相互情報量の関係 \(I(X; Y) = H(X) - H(X \mid Y)\)

相互情報量を、KL 形式の定義から `H(X) - H(X|Y)` という entropy 表現に橋渡しする。
本ライブラリの主要な「橋 (bridge)」定理。`.toReal` をとって実数として等式を述べる
（`mutualInfo` が `ℝ≥0∞` 値、`entropy`/`condEntropy` が `ℝ` 値のため）。

**Verified**: `mutualInfo_eq_entropy_sub_condEntropy`
(`Common2026/Shannon/Bridge.lean`)

```lean
theorem mutualInfo_eq_entropy_sub_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    (mutualInfo μ Xs Yo).toReal
      = entropy μ Xs - InformationTheory.MeasureFano.condEntropy μ Xs Yo
```

これと 2.2 のチェイン則を組み合わせると、対称形
\(I(X; Y) = H(X) + H(Y) - H(X, Y)\) が得られる。

**Verified**: `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy`
(`Common2026/Shannon/MIChainRule.lean`)

```lean
theorem mutualInfo_eq_entropy_add_entropy_sub_jointEntropy
    (joint : Measure (α × β)) [IsProbabilityMeasure joint] :
    (mutualInfo joint Prod.fst Prod.snd).toReal
      = entropy joint Prod.fst + entropy joint Prod.snd - entropy joint id
```

---

## 2.4 エントロピー・相互情報量のチェイン則 (Chain Rules)

### 相互情報量のチェイン則 (2 変数 → 1 個追加)

\[
I(Z, X; Y) = I(Z; Y) + I(X; Y \mid Z).
\]

**Verified**: `mutualInfo_chain_rule` (`Common2026/Shannon/CondMutualInfo.lean`)

```lean
theorem mutualInfo_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo
      = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc
```

### 相互情報量のチェイン則 (\(n\) 変数版)

\[
I(X_0, \dots, X_{n-1}; Y) = \sum_{i} I(X_i; Y \mid X_0, \dots, X_{i-1}).
\]
`Fin n` 添字の確率変数列に対する完全形。

**Verified**: `mutualInfo_chain_rule_fin` (`Common2026/Shannon/MIChainRule.lean`)

```lean
theorem mutualInfo_chain_rule_fin
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (Yo : Ω → Y) (hYo : Measurable Yo) :
    mutualInfo μ (fun ω i => Xs i ω) Yo
      = ∑ i : Fin n, ...   -- 各 prefix 条件付き相互情報量の和
```

（右辺は各 \(i\) における prefix 条件付き相互情報量の有限和。完全な右辺式は
ソース `MIChainRule.lean:93` を参照。）

### 独立・同分布 (i.i.d.) ペアでの加法性

\(n\) 組の同分布な独立ペアでは \(I(X^n; Y^n) = n\, I(X_0; Y_0)\)。

**Verified**: `mutualInfo_iid_eq_nsmul` (`Common2026/Shannon/MIChainRule.lean`)

```lean
theorem mutualInfo_iid_eq_nsmul
    {n : ℕ} (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_iid_joint : ...) (h_iid_X : ...) (h_iid_Y : ...) :
    ...   -- I(X^n; Y^n) = n • I(X_0; Y_0)
```

（積測度分解 `h_iid_*` を仮定として要求。これらは i.i.d. 構造を表す regularity 仮定
であり、結論の核心を抱えさせるものではない。完全な式はソース
`MIChainRule.lean:370` を参照。）

積分布上の相互情報量が各成分の和になる一般形も形式化済み:
**Verified**: `mutualInfo_pi_eq_sum` (`Common2026/Shannon/MIChainRule.lean`)。

---

## 2.5 条件付き相互情報量 (Conditional Mutual Information)

\[
I(X; Y \mid Z) = \sum_z p(z)\, D\!\left(p(x,y \mid z) \,\big\|\, p(x \mid z) p(y \mid z)\right).
\]

本ライブラリでは条件付き分布カーネルの compProd 形 KL として定義する。

**Verified (定義)**: `condMutualInfo` (`Common2026/Shannon/CondMutualInfo.lean`)

```lean
noncomputable def condMutualInfo
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞ :=
  klDiv ((μ.map Zc) ⊗ₘ condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ)
        ((μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ)))
```

### 性質: 非負性・対称性

**Verified**: `condMutualInfo_nonneg` (`Common2026/Shannon/CondMutualInfo.lean`)

```lean
theorem condMutualInfo_nonneg
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) :
    0 ≤ condMutualInfo μ Xs Yo Zc
```

**Verified**: `condMutualInfo_comm` (`Common2026/Shannon/CondMutualInfo.lean`):
\(I(X; Y \mid Z) = I(Y; X \mid Z)\)。

### entropy 表現 \(I(X; Z \mid Y) = H(X \mid Y) - H(X \mid Y, Z)\)

**Verified**: `condMutualInfo_eq_condEntropy_sub_condEntropy`
(`Common2026/Shannon/Entropy.lean`)

```lean
theorem condMutualInfo_eq_condEntropy_sub_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
    (condMutualInfo μ Xs Zo Yo).toReal
      = InformationTheory.MeasureFano.condEntropy μ Xs Yo
        - InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
```

---

## 2.6 ジェンセン不等式と情報不等式 (Information Inequality)

KL ダイバージェンス（相対エントロピー）の非負性 \(D(p \,\|\, q) \ge 0\)
（Gibbs 不等式 / 情報不等式、Cover & Thomas Thm 2.6.3）。本ライブラリでは
pmf 形 `klDivPmf P Q = ∑ₐ Q(a) · klFun(P(a)/Q(a))` に対し独立に形式化している。

**Verified**: `klDivPmf_nonneg`
(`Common2026/Shannon/CsiszarProjection.lean`,
名前空間 `InformationTheory.Shannon.CsiszarProjection`)

```lean
lemma klDivPmf_nonneg (P Q : α → ℝ)
    (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) :
    0 ≤ klDivPmf P Q
```

等号成立条件 \(D(p \,\|\, q) = 0 \iff p = q\)（full support の参照 pmf `Q` に対して）も
形式化済み。

**Verified**: `klDivPmf_eq_zero_iff_pmf`
(`Common2026/Shannon/MaxEntropyConstrained.lean`)

```lean
lemma klDivPmf_eq_zero_iff_pmf
    {P Q : α → ℝ} (hP : P ∈ stdSimplex ℝ α) (_hQ : Q ∈ stdSimplex ℝ α)
    (hQ_pos : ∀ a, 0 < Q a) :
    klDivPmf P Q = 0 ↔ P = Q
```

測度論版の \(I(X; Y) \ge 0\)（KL の `ℝ≥0∞` 値としての非負性）は 2.3 の
`mutualInfo_nonneg` として既出。

---

## 2.7 対数和不等式 (Log-Sum Inequality)

非負 \(a_i\) と正 \(b_i\) に対し
\[
\left(\sum_i a_i\right) \log\frac{\sum_i a_i}{\sum_i b_i}
  \le \sum_i a_i \log\frac{a_i}{b_i}.
\]
\(x \mapsto x \log x\) の凸性（有限ジェンセン）から従う。情報不等式・DPI の基盤。

**Verified**: `log_sum_inequality`
(`Common2026/Shannon/LZ78ZivEntropyBridge.lean`, 名前空間 `InformationTheory.Shannon`)

```lean
theorem log_sum_inequality
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i))
      ≤ ∑ i ∈ s, a i * Real.log (a i / b i)
```

`negMulLog` 形（絶対連続条件 `b i = 0 → a i = 0` 付き）も
`log_sum_inequality_negMulLog` (`Common2026/Fano/DPI.lean`) として形式化済み。

---

## 2.8 データ処理不等式 (Data Processing Inequality)

### KL ダイバージェンスの単調性 (post-processing 不等式)

任意の可測写像 \(f\) による push-forward で KL ダイバージェンスは増えない:
\(D(\mu \circ f^{-1} \,\|\, \nu \circ f^{-1}) \le D(\mu \,\|\, \nu)\)。
DPI の基盤となる plumbing 定理。

**Verified**: `klDiv_map_le` (`Common2026/Shannon/DPI.lean`)

```lean
theorem klDiv_map_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν
```

### 相互情報量のデータ処理不等式 (post-processing)

\(Y\) を後処理 \(f\) に通すと相互情報量は増えない:
\(I(X; f(Y)) \le I(X; Y)\)。

**Verified**: `mutualInfo_le_of_postprocess` (`Common2026/Shannon/DPI.lean`)

```lean
theorem mutualInfo_le_of_postprocess
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo)
    {f : Y → Z} (hf : Measurable f) :
    mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo
```

### マルコフ連鎖版 DPI \(X \to Z \to Y \implies I(X; Y) \le I(Z; Y)\)

マルコフ連鎖 \(X \to Z \to Y\) のもとで、相互情報量は「中継変数」を超えない。
本ライブラリではマルコフ連鎖を結合分布の条件付き独立分解として定義する。

**Verified (定義)**: `IsMarkovChain` (`Common2026/Shannon/CondMutualInfo.lean`)

```lean
def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop :=
  μ.map (fun ω => (Zc ω, Xs ω, Yo ω))
    = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))
```

**Verified**: マルコフ連鎖下の条件付き相互情報量ゼロ
`condMutualInfo_eq_zero_of_markov` (`Common2026/Shannon/CondMutualInfo.lean`):
\(I(X; Y \mid Z) = 0\)。

**Verified**: `mutualInfo_le_of_markov` (`Common2026/Shannon/CondMutualInfo.lean`)

```lean
theorem mutualInfo_le_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo
```

### 記憶のない通信路における per-letter 分解

DPI の応用として、記憶のない (memoryless) 通信路では
\(I(X^n; Y^n) \le \sum_i I(X_i; Y_i)\) が成り立つ
（Cover & Thomas Thm 7.2.1 系、本章で先取り形式化済み）。

**Verified**: `mutualInfo_le_sum_per_letter_of_memoryless_strong`
(`Common2026/Shannon/CondEntropyMemoryless.lean`)

```lean
theorem mutualInfo_le_sum_per_letter_of_memoryless_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_per_letter_markov : ∀ i : Fin n,
      IsMarkovChain μ (fun ω j => Xs j ω) (Xs i) (Ys i))
    (h_outputs_cond_indep : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
        (fun ω j => Xs j ω)
        (Ys i)) :
    (mutualInfo μ (fun ω j => Xs j ω) (fun ω j => Ys j ω)).toReal
      ≤ ∑ i : Fin n, (mutualInfo μ (Xs i) (Ys i)).toReal
```

（2 つの `IsMarkovChain` 仮定は memoryless 通信路の構造そのものを表す
前提条件であり、呼び出し側が `IsMemorylessChannelStrong` 構造から取り出す。）

---

## 2.9 充足統計量 (Sufficient Statistics)

統計量 \(T(X)\) がパラメータ \(\theta\) に対し充足的 (sufficient) であるとは、
\(X \to T(X) \to \theta\) がマルコフ連鎖をなすこと（同値に \(\theta \to T(X) \to X\)、
すなわち \(X \perp \theta \mid T(X)\)）。このとき相互情報量は統計量を通しても保存される:
\(I(\theta; X) = I(\theta; T(X))\)（Cover & Thomas Thm 2.9.1、DPI の等号版）。

本ライブラリでは充足統計量をまず、`mutualInfo_le_of_markov` の結論形に直結する
**マルコフ連鎖形**で定義する（教科書の Neyman-Fisher 因子分解形を直接 def 化すると
`condDistrib` の \(\theta\)-非依存性経由で長い橋渡しを要するため）。因子分解形との同値は
別途、Mathlib の条件付き独立性補題を経由して形式化済み（後述 `isSufficient_iff_factorized`）。

**Verified (定義)**: `IsSufficientStatistic`
(`Common2026/Shannon/SufficientStatistic.lean`, 名前空間 `InformationTheory.Shannon`)

```lean
def IsSufficientStatistic
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) (f : X → T') : Prop :=
  IsMarkovChain μ Xs (fun ω => f (Xs ω)) θ
```

**Verified**: `mutualInfo_eq_of_sufficient`
(`Common2026/Shannon/SufficientStatistic.lean`)

```lean
theorem mutualInfo_eq_of_sufficient
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) {f : X → T'}
    (hθ : Measurable θ) (hXs : Measurable Xs) (hf : Measurable f)
    (hsuff : IsSufficientStatistic μ θ Xs f) :
    mutualInfo μ θ Xs = mutualInfo μ θ (fun ω => f (Xs ω))
```

証明は 2.8 のデータ処理不等式（後処理版 `mutualInfo_le_of_postprocess` で
\(I(\theta; T(X)) \le I(\theta; X)\)）と、マルコフ連鎖版 DPI
（`mutualInfo_le_of_markov` で逆向き \(I(\theta; X) \le I(\theta; T(X))\)）を
`le_antisymm` で合わせて得る。

### Neyman-Fisher 因子分解形との同値

教科書の充足性は因子分解 \(p(x \mid \theta) = g(T(x), \theta)\, h(x)\) で導入される。
これは測度論的には「\(T(X)\) を与えたとき \(X\) の条件付き分布が \(\theta\) に依存しない」、
すなわち \(\mathrm{condDistrib}(X \mid T(X), \theta) = \mathrm{condDistrib}(X \mid T(X))\)
（\(\theta\)-成分を足しても変わらない）とエンコードできる。本ライブラリではこの因子分解形を
`IsSufficientStatisticFactorized` として定義し、マルコフ連鎖形との**同値**を形式化した。
両形式とも条件付き独立性 \(X \perp \theta \mid T(X)\) の別表現であり、同値は Mathlib の
`condIndepFun_iff_*`（`Mathlib/Probability/Independence/Conditional.lean`）を経由して閉じる。

**Verified (定義)**: `IsSufficientStatisticFactorized`
(`Common2026/Shannon/SufficientStatistic.lean`)

```lean
def IsSufficientStatisticFactorized
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) (f : X → T') : Prop :=
  condDistrib Xs (fun ω => (f (Xs ω), θ ω)) μ
    =ᵐ[μ.map (fun ω => (f (Xs ω), θ ω))]
      (condDistrib Xs (fun ω => f (Xs ω)) μ).prodMkRight Θ
```

**Verified**: `isSufficient_iff_factorized`
(`Common2026/Shannon/SufficientStatistic.lean`)

```lean
theorem isSufficient_iff_factorized
    (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) {f : X → T'}
    (hθ : Measurable θ) (hXs : Measurable Xs) (hf : Measurable f) :
    IsSufficientStatistic μ θ Xs f ↔ IsSufficientStatisticFactorized μ θ Xs f
```

同値定理は条件付き独立性の標準 Borel 機構（`condExpKernel` 経由）を使うため、
マルコフ連鎖形単独の `mutualInfo_eq_of_sufficient` には不要だった
\([\,\text{StandardBorelSpace } \Omega\,]\) を標本空間に課す（正当な regularity 前提）。

---

## 2.10 ファノの不等式 (Fano's Inequality)

復号誤り確率 \(P_e\) を、条件付きエントロピー \(H(X \mid Y)\) によって下から評価する。
\[
H(X \mid Y) \le H_b(P_e) + P_e \log(|\mathcal{X}| - 1),
\]
ここで \(H_b\) は二値エントロピー。本ライブラリは pmf 形と measure-theoretic 形の
両方を形式化している。

### 測度論版（決定論的復号器）

**Verified**: `fano_inequality_measure_theoretic`
(`Common2026/Fano/Measure.lean`, 名前空間 `InformationTheory.MeasureFano`)

```lean
theorem fano_inequality_measure_theoretic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hdec : Measurable decoder)
    (hcard : 2 ≤ Fintype.card X) :
    condEntropy μ Xs Yo ≤
      Real.binEntropy (errorProb μ Xs Yo decoder)
        + errorProb μ Xs Yo decoder * Real.log ((Fintype.card X : ℝ) - 1)
```

ここで `errorProb μ Xs Yo decoder = μ.real {ω | Xs ω ≠ decoder (Yo ω)}` は
復号誤り確率 \(P_e\)、`Real.binEntropy` は二値エントロピー \(H_b\)。

### pmf 版（コア定理）と誤り確率の下界

有限結合 pmf `FiniteJointPMF X X` に対する基本形（`qaryEntropy` 形）:

**Verified**: `fano_core` / `fano_inequality` (`Common2026/Fano/Core.lean`)

```lean
theorem fano_core (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ Real.qaryEntropy (Fintype.card X) P.errorProb

theorem fano_inequality (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ fanoBoundRHSOfAlphabet X P.errorProb
```

ファノの不等式の逆向き（誤り確率の strict 下界）も形式化済み:

**Verified**: `error_lower_bound` (`Common2026/Fano/Core.lean`)

```lean
theorem error_lower_bound (hcard : 2 ≤ Fintype.card X) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 - 1 / (Fintype.card X : ℝ))
    (hPe1 : P.errorProb ≤ 1 - 1 / (Fintype.card X : ℝ))
    (haH : Real.qaryEntropy (Fintype.card X) a < P.condEntropy) :
    a < P.errorProb
```

---

## 本章で未形式化の項目

Cover & Thomas Ch.2 のうち、本パイロットのスコープ（離散・有限アルファベット）内で
**本章には対応する独立した定理を確認できなかった**項目を正直に記す。

- **2.10 ファノ不等式の系（誤り確率と \(H(X)\) の弱形 \(H(P_e) + P_e \log|\mathcal{X}| \ge H(X|Y)\)
  等の variant）**: コア形・測度論形・逆向き下界は形式化済みだが、
  すべての教科書系を網羅したわけではない。

（初版で「未形式化」と記した 2.6 情報不等式 \(D(p\|q)\ge 0\)・2.7 対数和不等式は、
その後の存在確認で既存定理 `klDivPmf_nonneg` / `klDivPmf_eq_zero_iff_pmf` /
`log_sum_inequality` が見つかり、2.6・2.7 節として紐付け済み。）

---

## パイロットとしての所見（原稿生成の課題）

本パイロットで顕在化した、prose ↔ formal statement の乖離と原稿化の課題を記録する。

1. **値の型の不一致（`ℝ≥0∞` vs `ℝ`）が prose を分断する**:
   `mutualInfo` / `condMutualInfo` は `klDiv` の `ℝ≥0∞` 値だが、`entropy` /
   `condEntropy` は `ℝ` 値。橋渡し定理（例 `mutualInfo_eq_entropy_sub_condEntropy`）は
   左辺に `.toReal` が付く。教科書 prose は両者を素朴に「\(=\)」で結ぶため、
   原稿側で「`.toReal` をとった等式」という注釈が毎回必要になる。

2. **マルコフ連鎖の定義が「条件付き独立分解」形で、教科書の \(X \to Z \to Y\)
   記法と表層が異なる**: `IsMarkovChain` は結合分布の compProd 等式
   (`μ.map (Z,X,Y) = (μ.map Z) ⊗ₘ (K_X ×ₖ K_Y)`) で定義される。
   教科書の「マルコフ連鎖」直感とのギャップは原稿で 1 行補足が要る。

3. **DPI の標準形 \(I(X;Y) \le I(X;Z)\)（\(X\to Z\to Y\)）と、本ライブラリの
   `mutualInfo_le_of_markov` の結論 \(I(X;Y) \le I(Z;Y)\) は引数配置が異なる**。
   どちらも DPI の正しい一形態だが、教科書の「どの版か」を原稿で明示しないと
   読者が取り違える。

4. **チェイン則 \(n\) 変数版・i.i.d. 加法性は右辺が長大で、原稿に verbatim 転記
   しづらい**: `mutualInfo_chain_rule_fin` / `mutualInfo_iid_eq_nsmul` は
   `Fin n` 和・積測度仮定 (`h_iid_*`) を含み、本文には骨子のみ転記して
   完全式はソース行番号参照に逃がした。原稿層では「式の核」と
   「regularity 仮定の束」を分離表示する仕組みが要りそう。

5. **`condEntropy` が `Common2026/Fano/` 名前空間に居る**: Ch.2 中核の
   条件付きエントロピー定義が `InformationTheory.MeasureFano.condEntropy` という
   一見 Ch.7/Fano 寄りの名前空間にある。章 ↔ ファイルの対応が 1:1 でないため、
   原稿生成の「章 → 紐付け定理」マッピングは roadmap だけでなく
   実コードの名前空間横断 grep が必須（本パイロットでも `n_measure_theoretic`
   という roadmap 想起名は実在せず、実体は `fano_inequality_measure_theoretic`
   だった）。
