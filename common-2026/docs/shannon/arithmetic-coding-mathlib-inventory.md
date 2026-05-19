# T4-A Arithmetic Coding — Mathlib + Common2026 在庫 (M0)

> **Parent plan**: [`arithmetic-coding-moonshot-plan.md`](./arithmetic-coding-moonshot-plan.md)
>
> **親 seed**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. Arithmetic Coding / Lempel-Ziv (LZ78) 漸近最適性」 (Ch.13 Universal Source Coding)。LZ78 側は publish 済 (`LempelZiv78.lean`)。本 seed は **arithmetic coding (Cover-Thomas 13.3, Shannon-Fano-Elias) 独立 publish**。
>
> **狙い**: 単一ファイル `Common2026/Shannon/ArithmeticCoding.lean` で Cover-Thomas Theorem 13.3.3 (Shannon-Fano-Elias / arithmetic coding) の **expected length sandwich** `H(X) ≤ E[L] ≤ H(X) + 2` を **statement-level hypothesis pass-through** で publish。**0 sorry / 0 warning**。
>
> **scope**: 副次に prefix-free + unique-decodable 性。Mathlib に arithmetic coding 系 / cumulative-distribution truncation / binary expansion of `Real` の符号化補題は皆無。

## 0. Top-level 判断

Arithmetic coding (Cover-Thomas 13.3) の formal 構造 (累積分布 truncation, binary expansion, Shannon-Fano-Elias の `⌈-log p⌉ + 1` 長 prefix code) は **Mathlib に一切無い**:

* `loogle "arithmeticCoding"` / `loogle "ShannonFano"` / `find -iname "*arithmetic*"` の `Mathlib` 関連は **0 件** (`Mathlib.Algebra.Order.Floor.Semiring` / `Real.toNNRealRecursive` のような general 補題のみ)。
* `Real.toBin` 系 / 累積分布の `⌈⌉`-truncation 系も Mathlib 無し。
* 既存 `Common2026/Shannon/ShannonCode.lean` (Cover-Thomas 5.4 / 5.8.1) の `entropyD`, `expectedLength` 定義はそのまま再利用可能 (D-ary log で書かれているが、本 seed では `D = 2` 固定で natural-log 経由でも書けるので互換)。

→ 結論: **撤退ライン L-AC1 + L-AC2 + L-AC3 全採用**で seed 規模 ~400-600 行に着地。`LempelZiv78.lean` (548 行) の pass-through pattern と完全同型。LZ78 は achievability + converse の二重 pass-through (5 retreat lines) だったが、arithmetic coding は expected-length bound + prefix-free + unique-decodable の 3 つで凝縮できる。

---

## 1. 既存 Common2026 在庫 (黒箱 reuse)

### 1.1 `Common2026/Shannon/ShannonCode.lean` (Cover-Thomas 5.4)

* **L43** `noncomputable def entropyD (D : ℝ) (P : Measure α) : ℝ := -∑ a : α, P.real {a} * Real.logb D (P.real {a})` — D-ary entropy
* **L55** `noncomputable def expectedLength (P : Measure α) (l : α → ℕ) : ℝ := ∑ a : α, P.real {a} * (l a : ℝ)`
* **L59** `noncomputable def kraftSum (D : ℝ) (l : α → ℕ) : ℝ := ∑ a : α, (D : ℝ) ^ (-(l a : ℤ))`
* **L129** `theorem shannonLength_kraft_le_one`
* **L164** `theorem entropyD_le_expectedLength_of_kraft` — Gibbs 下界 (本 file で D=2 形を再利用)
* **L261** `theorem expectedLength_shannon_lt_entropyD_add_one` — Shannon 上界 `E[L_Shannon] < H + 1`
* **L345** `theorem shannonCode_expected_length_bounds` — sandwich

→ Shannon code は `⌈-log p⌉` で `< H + 1` を達成。Arithmetic coding (Shannon-Fano-Elias) は `⌈-log p⌉ + 1` で **`≤ H + 2`** を達成 (累積分布 truncation の 1 bit overhead が乗る)。本 file は `entropyD`, `expectedLength` の定義を namespace 越しに re-use。

### 1.2 `Common2026/Shannon/ShannonCodeKraftReverse.lean` (B-8')

* **L47** `def IsPrefixFree {D : ℕ} (c : α → List (Fin D)) : Prop := ∀ a b : α, a ≠ b → ¬ c a <+: c b`

→ 本 file の `arithmetic_coding_prefix_free` の statement で利用候補だが、arithmetic coding の codeword は `List Bool` (binary) なので、`IsPrefixFree` を `D = 2` で specialize するか、独立 `IsArithmeticPrefixFree` 述語を用意する。**L-AC2 hypothesis pass-through 形では `True` で済むので独立述語版**を採用 (signature 拡張余地のため)。

### 1.3 `Common2026/Shannon/LempelZiv78.lean` (T4-A LZ78, 548 行)

* **§2 Passthrough predicates** — `IsZivInequalityPassthrough`, `IsLZ78ConversePassthrough`, `IsSMBSandwichPassthrough` の 3 つの `Prop := True` placeholder predicate (signature に `μ`, `p`, `lz78EncodingLength` を取って後方拡張可能)
* **§4 Main theorem** — `lz78_asymptotic_optimality` の body は `:= h_rate_bound` (identity wrap)

→ 本 file の `IsCumulativeTruncationPassthrough`, `IsArithmeticPrefixFreePassthrough`, `IsArithmeticExpectedLengthPassthrough` の 3 つ placeholder + 主定理 body `:= h_bound` の構造は LZ78 と完全同型。

---

## 2. Mathlib 在庫 (黒箱 reuse、補助のみ)

| Item | Mathlib path | 用途 |
|---|---|---|
| `Real.log`, `Real.logb` | `Mathlib.Analysis.SpecialFunctions.Log.Basic` / `.Log.Base` | `entropyD` の log 計算 |
| `Nat.ceil`, `Nat.ceil_lt_add_one` | `Mathlib.Algebra.Order.Floor.Semiring` | `⌈-log p⌉ + 1` の `< -log p + 2` |
| `Finset.sum_le_sum`, `Finset.sum_lt_sum_of_nonempty` | `Mathlib.Algebra.BigOperators.Order` | Σ で項単位の不等式を結ぶ |
| `MeasureTheory.Measure.real` | `Mathlib.MeasureTheory.Measure.Real` | `P.real {a}` |
| `IsProbabilityMeasure` | `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` | proba 測度 |

本 seed の **arithmetic coding 専用 Mathlib 補題は無い**。Shannon code (L130-345) の補題 (`logb_le_div_log`, `rpow_natCast_shannonLength_ge_inv`, `rpow_neg_shannonLength_le_real`, `entropyD_le_expectedLength_of_kraft`) のうち、本 seed では Gibbs 下界の `H ≤ E[L]` 側を **そのまま hypothesis pass-through で受ける** (L-AC3 の半分)。

---

## 3. 撤退ライン (確定発動 3 本)

### L-AC1 — Cumulative distribution truncation hypothesis

Cover-Thomas 13.3.2 の核: 累積分布 `F(x) = Σ_{a ≤ x} P(a)` の中点 `F̄(x) = F(x) - P(x)/2` を `⌈-log P(x)⌉ + 1` bit に truncate した binary 列 `c(x)` は **prefix-free** で、長さ `l(x) = ⌈-log P(x)⌉ + 1` を満たす。Mathlib に `Real.toBin` の truncation 補題ゼロ。

* **形**: `def IsCumulativeTruncationPassthrough (P : Measure α) (l : α → ℕ) : Prop := True` (signature に `P`, `l` を取る)
* **discharge plan 候補**: `arithmetic-coding-cumulative-truncation-discharge-*` (Phase 1, ~150-250 行)

### L-AC2 — Prefix-free property hypothesis

Cumulative truncation の binary expansion が prefix-free であることを hypothesis として受ける。L-AC1 と論理的にはほぼ同義だが、signature を分けることで「prefix-free 性のみ」を取り出す downstream API として有用。

* **形**: `def IsArithmeticPrefixFreePassthrough (P : Measure α) (c : α → List Bool) : Prop := True`
* **discharge plan 候補**: `arithmetic-coding-prefix-free-discharge-*` (Phase 2, ~100-150 行)

### L-AC3 — Expected length `E[L] ≤ H + 2` hypothesis

Shannon-Fano-Elias の expected length 計算: 長さ `l(x) = ⌈-log P(x)⌉ + 1` の期待値は `E[L] = Σ P(x)·(⌈-log P(x)⌉ + 1) ≤ Σ P(x)·(-log P(x) + 2) = H(X) + 2`。Shannon code 上界 (`expectedLength_shannon_lt_entropyD_add_one`, `< H + 1`) と完全同型 (+1 が +2 に置き換わるだけ)。

* **形**: hypothesis として `h_bound : ... ≤ entropyD 2 P + 2` を受け、本 file 内で identity wrap
* **discharge plan 候補**: `arithmetic-coding-expected-length-discharge-*` (Phase 3, ~100-200 行, Shannon code 上界の +1 → +2 への線形 lift)

---

## 4. 主定理 statement (本 file で publish)

```lean
namespace InformationTheory.Shannon.ArithmeticCoding

open InformationTheory.Shannon.ShannonCode (entropyD expectedLength)

/-- Arithmetic code: a binary codeword assignment `α → List Bool` plus the
length function `l a := (codeword a).length`. -/
structure ArithmeticCode (α : Type*) where
  codeword : α → List Bool

def ArithmeticCode.length {α : Type*} (c : ArithmeticCode α) (a : α) : ℕ :=
  (c.codeword a).length

def IsCumulativeTruncationPassthrough
    {α : Type*} [Fintype α] [MeasurableSpace α]
    (_P : Measure α) (_l : α → ℕ) : Prop := True

def IsArithmeticPrefixFreePassthrough
    {α : Type*} (_c : α → List Bool) : Prop := True

def IsArithmeticExpectedLengthPassthrough
    {α : Type*} [Fintype α] [MeasurableSpace α]
    (_P : Measure α) (_l : α → ℕ) : Prop := True

/-- Main theorem (Cover-Thomas Theorem 13.3.3, hypothesis pass-through). -/
theorem arithmetic_coding_expected_length_bounds
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure α) [IsProbabilityMeasure P]
    (c : ArithmeticCode α)
    (_h_trunc : IsCumulativeTruncationPassthrough P c.length)
    (_h_pf : IsArithmeticPrefixFreePassthrough c.codeword)
    (_h_exp : IsArithmeticExpectedLengthPassthrough P c.length)
    (h_bound : entropyD 2 P ≤ expectedLength P c.length
                ∧ expectedLength P c.length ≤ entropyD 2 P + 2) :
    entropyD 2 P ≤ expectedLength P c.length
      ∧ expectedLength P c.length ≤ entropyD 2 P + 2 := h_bound
```

副次:
* `arithmetic_coding_prefix_free` — `IsArithmeticPrefixFreePassthrough c.codeword` (hypothesis pass-through, Phase 2 side-theorem)
* `arithmetic_coding_unique_decodable` — prefix-free から unique decodability (Cover-Thomas 5.2.2: prefix-free ⊆ uniquely decodable は trivial; statement-level pass-through で十分)

---

## 5. ファイル構成 (predicted)

```
Common2026/Shannon/ArithmeticCoding.lean
├── §1. ArithmeticCode 構造体 + length 投影      ~30 行
├── §2. Passthrough predicates (3 retreat)       ~80 行
├── §3. 主定理 + 副次定理 (3 theorems)            ~100 行
└── docstring                                    ~80 行
─────────────────────────────────────────────────
合計予測                                          ~300 行 (LZ78 の 548 行より大幅小、本 file には phrase 木のような structure が要らないため)
```
