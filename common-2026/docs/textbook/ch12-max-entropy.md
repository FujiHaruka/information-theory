# 第12章 最大エントロピー (Maximum Entropy)

> **このファイルについて**
>
> 本章は Cover & Thomas *Elements of Information Theory* (2nd ed.) Chapter 12
> (Maximum Entropy) を題材に、**検証済み Lean 定理を骨格にした教科書原稿**である。
> 本文の各主要結果には「**Verified**: `定理名` (`InformationTheory/...`)」という形で、
> その命題に対応する Lean 4 + Mathlib の formal declaration を紐付けてある。
>
> **検証強度の注記** — 本章で `**Verified**` と記した定理はすべて、
> 本プロジェクトの完成判定 **proof done**（当該 declaration を含むファイルが
> `0 sorry` かつ `0 @residual`、すなわち無条件機械検証済み）を満たす。
> 紐付けた定理が属するファイル
> (`MaxEntropy.lean` / `MaxEntropyConstrained.lean` /
> `MaxEntropyConstrainedKKT.lean`) は本章作成時点で `sorry` / `@residual` を
> 含まない。
>
> **形式化の枠組み** — 本章は二つの表現を併用する。
> 無制約の上界 \(H(X) \le \log|\mathcal{X}|\) は第2章と同じ measure-theoretic 形式
> （確率変数を測度空間 `(Ω, μ)` 上の可測写像 `X : Ω → α` として表現し、
> エントロピーは像測度 `μ.map X` を通じて定義）で述べる。
> 一方、モーメント制約付きの最大エントロピー（指数型族・Gibbs 分布）は
> **pmf 形式**で扱う：有限アルファベット `α` 上の pmf を
> `P : α → ℝ` (∈ `stdSimplex ℝ α`) として直接表し、エントロピーを
> `∑ x, Real.negMulLog (P x)`（= \(-\sum_x P(x)\log P(x)\)）で書く。
> KL ダイバージェンスは Csiszár の pmf 形 `klDivPmf` を用いる。
> アルファベット `α` は有限型 `[Fintype α] [DecidableEq α]`、空でない `[Nonempty α]`。
> 対応する Lean library は `InformationTheory/Shannon/MaxEntropy*.lean`。

---

## 12.1 最大エントロピー分布 (Maximum Entropy Distributions)

最大エントロピー問題とは、与えられた制約（典型的にはモーメント制約）を満たす分布の
うち Shannon エントロピーを最大にするものを求める問題である。Cover & Thomas
Theorem 12.1.1 は、その最大化分布が **Boltzmann–Gibbs 指数型族**

\[
p^*(x) = \frac{\exp\!\big(\sum_i \lambda_i f_i(x)\big)}{\sum_y \exp\!\big(\sum_i \lambda_i f_i(y)\big)}
\]

であることを主張する。ここで \(f_i\) は特徴写像（feature map）、\(\lambda_i\) は
モーメント制約 \(\mathbb{E}_P[f_i] = c_i\) に対応する Lagrange 乗数である。

> **形式化上の設計（ansatz pass-through）** — Lagrange 乗数 \(\lambda\) の*存在性*
> （\(\psi(\lambda)\) の凸性・Legendre 双対の解の存在）は Mathlib 未整備のため
> （`LagrangeMultipliers.lean` に KKT 不在の TODO がある）、本ライブラリは
> \(\lambda\) を**仮説として外から受け取る** pass-through 設計を採る。
> すなわち「与えられた \(\lambda\) が制約を満たすなら、その指数型族が最大化分布」
> という形で定理を述べ、\(\lambda\) の解の存在は別 plan のスコープとする。
> この \(\lambda\) は regularity（前提条件）であり、最大化主張の核心を
> 仮説に抱えさせるものではない。

### 無制約の場合: 一様分布が最大 \(H(X) \le \log|\mathcal{X}|\)

制約が無い場合、エントロピーを最大化するのは一様分布であり、その値は
アルファベットサイズの対数 \(\log|\mathcal{X}|\) である。これは
\(D(P \,\|\, U) \ge 0\)（一様分布 \(U\) への KL ダイバージェンスの非負性、Gibbs 不等式）
の帰結であり、第2章でも引用した結果である。本章では制約付き理論の特殊ケース
（空制約）として再掲する。

**Verified**: `entropy_le_log_card` (`InformationTheory/Shannon/MaxEntropy.lean`)

```lean
theorem entropy_le_log_card
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    entropy μ X ≤ Real.log (Fintype.card α)
```

等号成立条件（像測度が一様分布であること）も形式化済み。

**Verified**: `entropy_eq_log_card_iff` (`InformationTheory/Shannon/MaxEntropy.lean`)

```lean
theorem entropy_eq_log_card_iff
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    entropy μ X = Real.log (Fintype.card α)
      ↔ μ.map X = uniformOn (Set.univ : Set α)
```

### Gibbs 分布の定義 (Boltzmann–Gibbs pmf)

モーメント制約付きの最大化分布を表す Gibbs pmf を定義する。分母
\(Z(\lambda) = \sum_y \exp(\sum_i \lambda_i f_i(y))\) は分配関数 (partition function) である。

**Verified (定義)**: `gibbsZ` / `gibbsPmf`
(`InformationTheory/Shannon/MaxEntropyConstrained.lean`,
名前空間 `InformationTheory.Shannon.MaxEntropyConstrained`)

```lean
noncomputable def gibbsZ (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : ℝ :=
  ∑ y, Real.exp (∑ i, lam i * f i y)

noncomputable def gibbsPmf (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : α → ℝ :=
  fun x => Real.exp (∑ i, lam i * f i x) / gibbsZ f lam
```

`gibbsPmf f λ` は確かに pmf である（各成分が非負で総和が \(1\)）。

**Verified**: `gibbsPmf_mem_stdSimplex`
(`InformationTheory/Shannon/MaxEntropyConstrained.lean`)

```lean
lemma gibbsPmf_mem_stdSimplex [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    gibbsPmf f lam ∈ stdSimplex ℝ α
```

### Theorem 12.1.1（上界）: 制約下で Gibbs 分布がエントロピー最大

モーメント制約 \(\mathbb{E}_P[f_i] = c_i\) を満たす任意の pmf \(P\) について、
同じ制約を満たす Gibbs ansatz \(p^* = \text{gibbsPmf}\,f\,\lambda\) のエントロピーが
上界を与える：\(H(P) \le H(p^*)\)。

証明の重力中心は次の核 identity（任意の \(Q \in\) stdSimplex について）である：

\[
\mathrm{klDivPmf}(Q \,\|\, p^*) = -H(Q) - \langle \lambda, \mathbb{E}_Q[f]\rangle + \log Z(\lambda).
\]

\(Q = P\) と \(Q = p^*\) の二箇所でこれを評価し、KL の非負性
（`klDivPmf_nonneg`）と自己 KL がゼロであること（`klDivPmf_self_eq_zero`）を
組み合わせると \(H(P) \le H(p^*)\) が出る。Lagrange 乗数の凸性や存在性は一切不要。

**Verified**: `entropy_le_gibbs_of_constraints`
(`InformationTheory/Shannon/MaxEntropyConstrained.lean`)

```lean
theorem entropy_le_gibbs_of_constraints [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) ≤ ∑ x, Real.negMulLog (gibbsPmf f lam x)
```

### Theorem 12.1.1（一意性）: 等号成立は \(P = p^*\) のときに限る

最大化分布は本質的に一意である。エントロピー等号 \(H(P) = H(p^*)\) は
\(P = p^*\) と同値。これは KL ダイバージェンスがゼロになる条件
（\(\mathrm{klDivPmf}(P \,\|\, Q) = 0 \iff P = Q\)、`klDivPmf_eq_zero_iff_pmf`）から従う。

**Verified**: `entropy_eq_gibbs_iff_of_constraints`
(`InformationTheory/Shannon/MaxEntropyConstrained.lean`)

```lean
theorem entropy_eq_gibbs_iff_of_constraints [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_gibbs_constraints : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) = ∑ x, Real.negMulLog (gibbsPmf f lam x)
      ↔ P = gibbsPmf f lam
```

---

## 12.1（続）指数型族と KKT / Lagrange 双対の言葉

上の Gibbs 形と等価な、より KKT / Lagrangian に直接対応する表現も形式化されている。
指数型族 pmf と対数分配関数 \(\psi(\lambda)\) を次のように定義する：

\[
\psi(\lambda) = \log\!\Big(\sum_y \exp\langle\lambda, f(y)\rangle\Big), \qquad
p^*_\lambda(x) = \exp\!\big(\langle\lambda, f(x)\rangle - \psi(\lambda)\big).
\]

**Verified (定義)**: `logPartitionψ` / `expFamilyDist`
(`InformationTheory/Shannon/MaxEntropyConstrainedKKT.lean`,
名前空間 `InformationTheory.Shannon.MaxEntropyConstrainedKKT`)

```lean
noncomputable def logPartitionψ (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : ℝ :=
  Real.log (gibbsZ f lam)

noncomputable def expFamilyDist (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : α → ℝ :=
  fun x => Real.exp ((∑ i, lam i * f i x) - logPartitionψ f lam)
```

この `expFamilyDist` は `gibbsPmf` と各点で一致する（`Real.exp_sub` +
`Real.exp_log` の一段で橋渡しされる）ので、Gibbs 形のすべての性質が移植される。

**Verified**: `expFamilyDist_eq_gibbsPmf`
(`InformationTheory/Shannon/MaxEntropyConstrainedKKT.lean`)

```lean
lemma expFamilyDist_eq_gibbsPmf [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    expFamilyDist f lam = gibbsPmf f lam
```

### KKT 解のパッケージ化

Lagrangian \(L(p, \lambda) = H(p) + \sum_i \lambda_i (\mathbb{E}_p[f_i] - c_i)\) の鞍点条件
（\(p\) についての停留性が指数型族を選び出し、\(\lambda\) についての実行可能性が
モーメント整合 \(\nabla\psi(\lambda) = c\)）を、Lagrange 乗数とモーメント整合証拠の
組として構造体にまとめる。

**Verified (定義)**: `KKTSolution`
(`InformationTheory/Shannon/MaxEntropyConstrainedKKT.lean`)

```lean
structure KKTSolution (f : Fin k → α → ℝ) (c : Fin k → ℝ) where
  lam : Fin k → ℝ
  moment_match : ∀ i, ∑ x, expFamilyDist f lam x * f i x = c i
```

### Legendre 恒等式: 最大化分布の自己エントロピー

KKT 解に対し、指数型族最適分布のエントロピーは閉形式
\(H(p^*) = \psi(\lambda) - \langle\lambda, c\rangle\) を持つ。これは Lagrangian 鞍点での
原始値と双対値の一致（KKT 双対性）である。

**Verified**: `entropy_expFamilyDist_eq_legendre`
(`InformationTheory/Shannon/MaxEntropyConstrainedKKT.lean`)

```lean
theorem entropy_expFamilyDist_eq_legendre [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ) (S : KKTSolution f c) :
    ∑ x, Real.negMulLog (expFamilyDist f S.lam x)
      = logPartitionψ f S.lam - ∑ i, S.lam i * c i
```

### Theorem 12.1.1 — KKT / 指数型族版（主定理）

Cover & Thomas Theorem 12.1.1 を KKT 言語で再述する。制約実行可能な任意の \(P\) は、
KKT 証拠を伴う指数型族解のエントロピーを超えない。

**Verified**: `expFamily_maximizes_entropy`
(`InformationTheory/Shannon/MaxEntropyConstrainedKKT.lean`)

```lean
theorem expFamily_maximizes_entropy [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_KKT : ∀ i, ∑ x, expFamilyDist f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) ≤ ∑ x, Real.negMulLog (expFamilyDist f lam x)
```

`KKTSolution` 構造体で包んだ形（roadmap 代表名）も形式化済み。

**Verified**: `expFamily_maximizes_entropy_of_KKT`
(`InformationTheory/Shannon/MaxEntropyConstrainedKKT.lean`)

```lean
theorem expFamily_maximizes_entropy_of_KKT [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (S : KKTSolution f c) :
    ∑ x, Real.negMulLog (P x) ≤ ∑ x, Real.negMulLog (expFamilyDist f S.lam x)
```

### Theorem 12.1.1 — KKT / 指数型族版（一意性）

**Verified**: `expFamily_unique`
(`InformationTheory/Shannon/MaxEntropyConstrainedKKT.lean`)

```lean
theorem expFamily_unique [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_KKT : ∀ i, ∑ x, expFamilyDist f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) = ∑ x, Real.negMulLog (expFamilyDist f lam x)
      ↔ P = expFamilyDist f lam
```

`KKTSolution` 構造体で包んだ companion `expFamily_unique_of_KKT` も形式化済み。

### 変分形（自由エネルギー / Legendre 双対上界）

最大化主張は、各 \(\lambda\) に対する変分上界としても述べられる。制約実行可能な
任意の \(P\) は

\[
H(P) \le \psi(\lambda) - \langle\lambda, c\rangle
\]

を満たす。これは `logPartitionψ` を実行可能集合上の \(-H\) の Legendre 変換として
特徴づける変分形である（主不等式 + Legendre 恒等式の組み合わせ）。

**Verified**: `entropy_le_logPartition_sub_inner`
(`InformationTheory/Shannon/MaxEntropyConstrainedKKT.lean`)

```lean
theorem entropy_le_logPartition_sub_inner [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_KKT : ∀ i, ∑ x, expFamilyDist f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x)
      ≤ logPartitionψ f lam - ∑ i, lam i * c i
```

`KKTSolution` 包み版 `entropy_le_logPartition_sub_inner_of_KKT`、および KKT 一階条件
（モーメント整合 \(\nabla\psi(\lambda) = c\)）が Gibbs ansatz の制約整合と同値であることを
述べる `KKT_moment_match_iff_gibbs_moment_match` も形式化済み。

---

## 12.1（特例）教科書例題の閉形式

Cover & Thomas 12.1 / 章末問題に現れる代表的な最大エントロピー分布が、
上の一般理論の特殊ケースとして閉形式で形式化されている。

### 空制約 → 一様分布

特徴写像が零写像 \(f \equiv 0\)（例えば制約数 \(k = 0\)）のとき、Gibbs 分布は
\(\lambda\) に無依存に一様 pmf \(x \mapsto 1/|\mathcal{X}|\) となり、そのエントロピーは
\(\log|\mathcal{X}|\)。これは無制約版（`entropy_le_log_card`）の pmf 形と一致する。

**Verified**: `entropy_gibbsPmf_zero_eq_log_card`
(`InformationTheory/Shannon/MaxEntropyConstrained.lean`)

```lean
theorem entropy_gibbsPmf_zero_eq_log_card [Nonempty α] (lam : Fin k → ℝ) :
    ∑ x : α, Real.negMulLog (gibbsPmf (0 : Fin k → α → ℝ) lam x)
      = Real.log (Fintype.card α)
```

### 二点分布の指数型族 (Bernoulli, Ex. 12.1)

\(\alpha = \text{Bool}\)、特徴 \(f_0(b) = \mathbb{1}[b = \text{true}]\)、平均制約 \(\mu\) のとき、
Gibbs 分布は \(p^*(\text{true}) = \mu\), \(p^*(\text{false}) = 1-\mu\) で、エントロピーは
二値エントロピー \(H_b(\mu)\)（= \(-\mu\log\mu - (1-\mu)\log(1-\mu)\)）に一致する。

**Verified**: `entropy_gibbsPmf_bool_eq_binEntropy`
(`InformationTheory/Shannon/MaxEntropyConstrained.lean`)

```lean
theorem entropy_gibbsPmf_bool_eq_binEntropy
    (lam : Fin 1 → ℝ) (μ : ℝ)
    (h_mean : ∑ b : Bool, gibbsPmf boolFeature lam b * boolFeature 0 b = μ) :
    ∑ b : Bool, Real.negMulLog (gibbsPmf boolFeature lam b) = Real.binEntropy μ
```

### 離散指数分布 (geometric ratio 形, Ex. 12.2)

\(\alpha = \mathrm{Fin}(N+1)\)、線形特徴 \(f_0(x) = x\) のとき、\(q := \exp(\lambda_0)\) と
おくと Gibbs 分布は geometric ratio 形 \(x \mapsto q^x / \sum_y q^y\)（閉形式）となる。
Lagrange 乗数 \(\lambda\) の具体値（平均 \(\mu\) との対応）は ansatz pass-through のため
スコープ外で、分布の形のみを確定する。

**Verified**: `gibbsPmf_linearFeature_eq_geometric`
(`InformationTheory/Shannon/MaxEntropyConstrained.lean`)

```lean
theorem gibbsPmf_linearFeature_eq_geometric {N : ℕ} (lam : Fin 1 → ℝ) :
    gibbsPmf (linearFeature (N := N)) lam
      = fun x : Fin (N + 1) =>
          (Real.exp (lam 0)) ^ (x : ℕ)
            / ∑ y : Fin (N + 1), (Real.exp (lam 0)) ^ (y : ℕ)
```

---

## 本章で未形式化の項目

Cover & Thomas Ch.12 のうち、本章スコープ（離散・有限アルファベット）の枠で
**本章には対応する独立した proof-done 定理を確認できなかった**項目を正直に記す。

- **Lagrange 乗数 \(\lambda\) の存在性（解の存在定理）**: 本ライブラリの最大化定理は
  すべて \(\lambda\) を制約整合証拠つきで**外から受け取る** ansatz pass-through 形で
  あり、与えられたモーメント制約 \(c\) に対して整合する \(\lambda\) が必ず存在する
  ことは形式化していない。これは \(\psi(\lambda)\) の凸性と Legendre 双対の解の存在を
  要し、Mathlib は KKT / 凸双対の必要な定理を未整備（`LagrangeMultipliers.lean` に
  TODO）。コード中でも「別 plan (`max-entropy-constrained-existence-*`) のスコープ」
  と明記されており、本章では未形式化。
- **12.2 連続・微分エントロピー版の最大エントロピー（Gaussian が分散制約下で最大、
  指数分布が平均制約下で最大 等の連続分布版）**: 本章スコープは離散・有限
  アルファベットであり、連続版は未形式化（差分エントロピー側は別章 / 別ファイル
  `DifferentialEntropy.lean` の管轄で、本章には紐付けていない）。
- **12.3–12.6 スペクトル推定 (Burg の最大エントロピー定理、自己回帰過程、
  スペクトル推定の最大エントロピー法)**: 離散有限アルファベットの本章スコープ外で、
  本章では未形式化。
- **最大エントロピーレート過程（12.6, Burg）**: 本章では未形式化。

---

## 所見（原稿生成の課題）

本章で顕在化した、prose ↔ formal statement の乖離と原稿化の課題を記録する。

1. **無制約版（measure-theoretic）と制約付き版（pmf）で表現が分断される**:
   \(H(X) \le \log|\mathcal{X}|\) は像測度 `μ.map X` を用いた measure-theoretic 形
   (`entropy μ X`) だが、Gibbs / 指数型族の最大化定理は pmf 形
   (`∑ x, Real.negMulLog (P x)`, `P ∈ stdSimplex`) で述べられている。教科書は両者を
   同じ \(H(P)\) 記法で素朴に書くが、Lean 側では型が異なり、橋渡し（特に空制約 →
   一様 pmf の `entropy_gibbsPmf_zero_eq_log_card` が両者を `log |α|` の値で接続）が
   1 本必要になる。

2. **Lagrange 乗数 \(\lambda\) が「解」でなく「仮説」である点が教科書直感と乖離する**:
   教科書 Theorem 12.1.1 は「制約から \(\lambda\) が定まり、その指数型族が最大」と
   読めるが、本ライブラリは \(\lambda\) の存在性を回避するため \(\lambda\) を
   制約整合証拠つきで仮説として受け取る ansatz pass-through 形。これは
   regularity（前提条件）であって最大化の核心ではないが、原稿では「与えられた
   \(\lambda\) が制約を満たすなら」という条件節を毎回明示しないと、読者が
   「存在性まで証明済み」と誤読しうる。

3. **Gibbs 形と KKT / 指数型族形の二重表現**: `gibbsPmf` (`exp⟨λ,f⟩ / Z`) と
   `expFamilyDist` (`exp(⟨λ,f⟩ - ψ)`) は `expFamilyDist_eq_gibbsPmf` で各点一致する
   同一分布だが、ファイルが分かれ表記も異なる。教科書 prose では同一物として
   扱われるため、原稿では「両者は等しい」橋渡しを 1 行で示しつつ、KKT 版を
   roadmap 代表（`expFamily_maximizes_entropy_of_KKT`）として前面に出す構成にした。

4. **roadmap 代表名と実 declaration はおおむね一致**: 本章は roadmap の 4 代表名
   (`entropy_le_log_card`, `entropy_eq_log_card_iff`, `entropy_le_gibbs_of_constraints`,
   `expFamily_maximizes_entropy_of_KKT`) がすべて実在する proof-done declaration と
   verbatim 一致した（第2章パイロットで見られた roadmap 想起名と実名の乖離は
   本章では発生せず）。ただし `_of_KKT` 版と素の版（`KKTSolution` 包みの有無）の
   ペアが多数あり、どちらを「正典」とするかは原稿側の判断が要る。
