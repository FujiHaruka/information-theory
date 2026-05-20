# Fano の不等式・本丸の証明計画

> 実態整合 (2026-05-20): DONE-UNCOND — 本 plan のゴール (`hcore` 仮定を消す) は達成済。`fano_core (hcard : 2 ≤ Fintype.card X) : P.condEntropy ≤ Real.qaryEntropy (Fintype.card X) P.errorProb` が `Common2026/Fano/Core.lean:379` に存在し、外部 `hcore` なしで chain rule 2 通り + `H(E|X,Y)=0` から実証 (`fano_inequality` も `Core.lean:424` で `hcore` なし)。`lake env lean Common2026/Fano/Core.lean` silent、0 sorry。下記 Context 「hcore は仮説として外から渡されているだけ」は STALE。

## Context

`Common2026/Fano.lean` の現状：

- Mathlib の `Real.qaryEntropy` の上に **wrapper だけ**を作った状態。
- 教科書 RHS への rename (`fanoBoundRHS`)、単調性に基づく逆向きの形 (`fano_error_lower_bound_of_lt_qaryEntropy`)、`FiniteJointPMF` 構造体と `jointEntropy` / `condEntropy` / `errorProb` の **定義**は揃っている。
- ただし Fano の本体である

  ```lean
  P.condEntropy ≤ Real.qaryEntropy (Fintype.card X) (P.errorProb decode)
  ```

  は仮説 (`hcore`) として外から渡されているだけで、**証明されていない**。

ゴールは上の `hcore` を `FiniteJointPMF` から導出して定理に格上げし、`fano_inequality_of_core` の hypothesis を消すこと。

非ゴール：

- Mathlib への upstream / PR 化（旧 M7）。今回は local 完結で良い。
- `MeasureTheory.condEntropy` や `PMF` への置換。`FiniteJointPMF` 上で完結させる。

## Approach

教科書 Fano の証明を Lean に直訳する：

1. 誤り indicator `E : X × Y → Bool, E (x, y) := x ≠ decode y` を導入。
2. チェインルールを 2 通り展開：
   - `H(X, E | Y) = H(E | Y) + H(X | E, Y)`
   - `H(X, E | Y) = H(X | Y) + H(E | X, Y)`
3. `H(E | X, Y) = 0`（E は (X, Y) の決定的関数）から
   `H(X | Y) = H(E | Y) + H(X | E, Y)`。
4. 各項を抑える：
   - `H(E | Y) ≤ binEntropy Pe`（Jensen on `binEntropy` の凹性、binary 限定）
   - `H(X | E, Y) ≤ Pe · log(|X| - 1)`（E=0 で deterministic、E=1 で support サイズ |X|-1）
5. 合成して `fanoBoundRHS` の形に展開、既存の `qaryEntropy_eq_fanoBoundRHS` で締める。

戦略上のキーポイント：

- **Conditioning reduces entropy の一般版は使わない**。Fano に必要なのは binary な E に対する版だけなので、`Real.strictConcaveOn_binEntropy` + 有限 Jensen で軽量に済ませる。
- 一般 alphabet の `H(X) ≤ log(|support|)` は M1 で 1 度作れば、M5 の `E=1` 側で再利用できる。
- 順番通りに進めるよりも、**Jensen API の使い心地を M1 と M3 で先に検証**してから M2/M4/M5 の機械的部分に入る方が安全（API の壁にぶつかったら設計変更が必要なため）。

## ファイル構成

`Common2026/Fano.lean` を肥大化させない方針：

- `Common2026/Fano/Entropy.lean` — M1 の単項エントロピー基本性質
- `Common2026/Fano/CondEntropy.lean` — M2 の同時/条件付きエントロピー代数
- `Common2026/Fano/BinaryJensen.lean` — M3 の binary 限定 Jensen
- `Common2026/Fano/Core.lean` — M4〜M6 の Fano 本体証明
- `Common2026/Fano.lean` — 既存の wrapper 群はそのまま、`hcore` を `Core.lean` の定理で埋める

`Common2026.lean`（library root）に各ファイルの `import` を追記。

## マイルストーン

### M0. 基盤の最終確認（半日）

- 既存 `FiniteJointPMF` の API が以下に十分か確認：
  - `marginalY`, `jointEntropy`, `yEntropy`, `condEntropy`, `errorProb` の挙動
  - 不足があれば `marginalX`、`condMass (x | y)` 等を補う
- Mathlib 側の依存ライブラリ確認：
  - `Real.negMulLog` 系列（`Mathlib.Analysis.SpecialFunctions.NegMulLog`）
  - `Real.binEntropy` の凹性 (`Real.strictConcaveOn_binEntropy` 等)
  - `Finset` 版 Jensen (`ConcaveOn.le_inner_smul` / `inner_le_*`)
- 必要 import を `Common2026/Fano/Entropy.lean` のヘッダに固定。

**Done 条件**：上記 API が手元に揃っており、M1 の最初の lemma が書き始められる状態。

### M1. 単項エントロピーの基本性質（1〜2 日）

`Common2026/Fano/Entropy.lean` に：

```lean
def entropyOfFn (μ : α → ℝ) : ℝ := ∑ a, (μ a).negMulLog

lemma entropyOfFn_nonneg
    (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (h1 : ∀ a, μ a ≤ 1) :
    0 ≤ entropyOfFn μ

lemma entropyOfFn_le_log_card
    (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a) (hsum : ∑ a, μ a = 1) :
    entropyOfFn μ ≤ Real.log (Fintype.card α)

lemma entropyOfFn_le_log_supportCard
    (μ : α → ℝ) … :
    entropyOfFn μ ≤ Real.log (μ.support.card)

lemma entropyOfFn_eq_zero_of_isDirac
    (μ : α → ℝ) (a₀ : α) (h : ∀ a, μ a = if a = a₀ then 1 else 0) :
    entropyOfFn μ = 0
```

**難所**：`entropyOfFn_le_log_card` は Jensen on `negMulLog` の凹性。Mathlib の `ConcaveOn` API を使った Finset 重み付き Jensen の書き方を確立する。

**Done 条件**：4 本の lemma が `lake env lean` でクリーン通過。

### M2. 同時/条件付きエントロピーの代数（2〜3 日）

`Common2026/Fano/CondEntropy.lean` に：

```lean
lemma condEntropy_nonneg (P : FiniteJointPMF X Y) : 0 ≤ P.condEntropy

-- 3 変数版を扱うため、X × Z の joint 上で定義する補助
def jointEntropyOf (μ : α → ℝ) : ℝ := ∑ a, (μ a).negMulLog

-- チェインルール (両側展開して引き算で導出)
lemma chain_rule_of_three
    {X E Y : Type*} [Fintype X] [Fintype E] [Fintype Y]
    (μ : X → E → Y → ℝ) … :
    H(X, E | Y) = H(E | Y) + H(X | E, Y)

-- 決定的関数のエントロピー
lemma condEntropy_zero_of_deterministic
    (P : FiniteJointPMF X Y) (f : X → Y → E)
    (h : ∀ x y, μ_E (x, y) = δ_{f x y}) :
    H(E | X, Y) = 0
```

注意：3 変数を扱うために `FiniteJointPMF` を `X × E × Y` に拡張する小ユーティリティが必要。あるいは
`FiniteJointPMF X (E × Y)` 等の形で吸収する。

**難所**：Finset 二重和の入れ替え (`Finset.sum_comm`)、marginal 計算、3 変数の indexing。証明自体は地味だがバグりやすい。

**Done 条件**：チェインルールが `H(X|Y) = H(E|Y) + H(X|E,Y)` の形で取り出せる。

### M3. Binary 限定 Conditioning Reduces Entropy（2〜3 日）

`Common2026/Fano/BinaryJensen.lean` に：

```lean
lemma binEntropy_jensen_finset
    {ι : Type*} [Fintype ι] (w p : ι → ℝ)
    (hw_nn : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hp_mem : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i, w i * Real.binEntropy (p i) ≤ Real.binEntropy (∑ i, w i * p i)

lemma binary_condEntropy_le
    (P : FiniteJointPMF (Bool × Y)) … :
    H(E | Y) ≤ Real.binEntropy (P(E = 1))
```

**難所**：Mathlib の `ConcaveOn.le_inner_smul` / Finset Jensen の正確な型と引数順を掴む。
`Real.strictConcaveOn_binEntropy` の存在確認（無ければ凹性だけ別 lemma で確立）。

**ここが Fano の数学的な肝**。ここを越えれば残りは機械的。

**Done 条件**：`binary_condEntropy_le` がクリーン通過。

### M4. 誤り indicator のセットアップ（1 日）

`Common2026/Fano/Core.lean` の前半に：

```lean
def errIndicator (decode : Y → X) : X → Y → Bool := fun x y => decide (x ≠ decode y)

-- (X, Y) の同時分布から (E, Y) や (E, X, Y) の同時分布を導出
def withErr (P : FiniteJointPMF X Y) (decode : Y → X) :
    FiniteJointPMF (Bool × X) Y

lemma withErr_marginal_E_one
    (P : FiniteJointPMF X Y) (decode : Y → X) :
    P_E (true) = P.errorProb decode

lemma withErr_E_deterministic
    (P : FiniteJointPMF X Y) (decode : Y → X) :
    -- E は (X, Y) の決定的関数
    …
```

**Done 条件**：`P_E(true) = errorProb` と「E は (X, Y) の関数」が形式化されている。

### M5. Fano 分解の各項を抑える（2 日）

`Common2026/Fano/Core.lean` 中盤に：

```lean
-- (1) H(E | X, Y) = 0
lemma cond_entropy_E_given_XY_zero (P …) (decode …) : H(E | X, Y) = 0

-- (2) H(E | Y) ≤ binEntropy Pe
lemma cond_entropy_E_given_Y_le_binEntropy
    (P …) (decode …) :
    H(E | Y) ≤ Real.binEntropy (P.errorProb decode)

-- (3) H(X | E, Y) ≤ Pe · log(|X| - 1)
lemma cond_entropy_X_given_EY_le
    (P …) (decode …) :
    H(X | E, Y) ≤ P.errorProb decode * Real.log ((Fintype.card X : ℝ) - 1)
```

(3) は場合分け：

- `E = 0`：`X = decode(Y)` で deterministic ⇒ entropy 0。M2 の deterministic lemma。
- `E = 1`：`X ∈ X \ {decode y}`（cardinality `|X| - 1`）⇒ M1 の `entropyOfFn_le_log_supportCard`。
- 重み `(1 - Pe, Pe)` で平均 ⇒ `Pe · log(|X| - 1)`。

**Done 条件**：3 本の不等式 lemma が通る。

### M6. 組み立て（半日）

`Common2026/Fano/Core.lean` 末尾に：

```lean
theorem fano_core
    (P : FiniteJointPMF X Y) (decode : Y → X) (hcard : 2 ≤ Fintype.card X) :
    P.condEntropy ≤ Real.qaryEntropy (Fintype.card X) (P.errorProb decode) := by
  -- M2 のチェインルール:  H(X|Y) = H(E|Y) + H(X|E,Y)
  -- M5 (2) (3) で右辺を抑える
  -- 既存の qaryEntropy_eq_fanoBoundRHS で締める
```

そして `Common2026/Fano.lean` の `fano_inequality_of_core` / `error_lower_bound_of_core` の `hcore` 仮説を消し、`fano_core` を直接呼ぶ形にリファクタ。

**Done 条件**：

- `lake env lean Common2026/Fano.lean` がクリーン通過
- `lake env lean Common2026/Fano/Core.lean` がクリーン通過
- `Common2026.lean` に新ファイル群を `import` 追記
- `lake build` 全体グリーン

## クリティカルパスとリスク

**先に試すべき順序**：

1. M0 で API の存在確認
2. **M1 の `entropyOfFn_le_log_card`** を prototype（Jensen API の最初の壁）
3. **M3 の `binEntropy_jensen_finset`** を prototype（同じ壁の binary 版確認）

ここまでで「Mathlib の Jensen / Concavity API が当面の用途に耐える」ことを確認できれば、残り (M2, M4, M5, M6) は機械的な Finset 計算なので、量はあっても詰む確率は低い。

**主リスク**：

- `Real.strictConcaveOn_binEntropy` または `Real.concaveOn_negMulLog` 相当が Mathlib に無い／使いにくい場合、自前で凹性を確立する必要があり M1/M3 が +数日。
- 3 変数 joint の取り回しが `FiniteJointPMF X Y` の 2 変数前提と噛み合わず、M2 のチェインルールでデータ構造の小規模リファクタが必要になる可能性。

## 工数見積もり

| 段階 | 想定 |
|---|---|
| M0 | 半日 |
| M1 | 1〜2 日 |
| M2 | 2〜3 日 |
| M3 | 2〜3 日 |
| M4 | 1 日 |
| M5 | 2 日 |
| M6 | 半日 |
| **合計** | **2〜3 週間（Lean に慣れた 1 人作業）** |
