# Shannon コード (B-8) Mathlib + Common2026 API インベントリ

> Phase 0 結果 (2026-05-12)。シードカード [B-8](../moonshot-seeds.md) の Mathlib API 探索結果。

## 結論

- **Mathlib にある**: `Real.logb`, `Nat.ceil` 基本 lemma 群, `Real.log_le_sub_one_of_pos`, `Real.rpow` 関連
- **Mathlib にある (符号系)**: `InformationTheory.UniquelyDecodable`, `InformationTheory.kraft_mcmillan_inequality` (順向きのみ)
- **Mathlib に無い**: prefix code 構造体, `kraft_mcmillan_converse` (Kraft 逆向き)
- **本シードの帰結**: 語長 (`α → ℕ`) 水準で完結する。文字列符号 (`Finset (List α)`) との bridge は不要。Kraft 逆向きは B-8' に切り出し。

## 1. 符号理論 (`Mathlib.InformationTheory.Coding`)

ファイル一覧:
- `Mathlib/InformationTheory/Coding/UniquelyDecodable.lean`
- `Mathlib/InformationTheory/Coding/KraftMcMillan.lean`

### 1.1 `UniquelyDecodable`

```
file: Mathlib/InformationTheory/Coding/UniquelyDecodable.lean:35
def UniquelyDecodable {α : Type*} (S : Set (List α)) : Prop :=
  ∀ (L₁ L₂ : List (List α)),
    (∀ w ∈ L₁, w ∈ S) → (∀ w ∈ L₂, w ∈ S) →
    L₁.flatten = L₂.flatten → L₁ = L₂
```

付随補題:
- `UniquelyDecodable.epsilon_not_mem` (Coding/UniquelyDecodable.lean:48): `UniquelyDecodable S → [] ∉ S`
- `UniquelyDecodable.flatten_injective` (Coding/UniquelyDecodable.lean:51)

### 1.2 `kraft_mcmillan_inequality` (順向きのみ)

```
file: Mathlib/InformationTheory/Coding/KraftMcMillan.lean:149
public theorem kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α]
    (h : UniquelyDecodable (S : Set (List α))) :
    ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1
```

**入力**: 文字列符号 `S : Finset (List α)` (D = `Fintype.card α`)。
**出力**: Kraft 和 `Σ D^{-|w|} ≤ 1`。

注: 本シードは語長水準で完結するため、この補題は **直接呼ばない** (Shannon 語長が Kraft を充足することを 1 から証明)。

### 1.3 prefix code 構造体 / Kraft 逆向き

**Mathlib に無し**。`rg "PrefixCode|prefix_code|IsPrefix" .lake/packages/mathlib/Mathlib/InformationTheory/` で 0 件。
Boolean cube / tree からの構成 (`Mathlib.SetTheory.Descriptive.Tree`) は prefix-related だが information-theoretic coding 構造ではない。

## 2. logb (D-ary log) — `Mathlib.Analysis.SpecialFunctions.Log.Base`

主要使用 API:

```
file: Mathlib/Analysis/SpecialFunctions/Log/Base.lean:46
theorem log_div_log : log x / log b = logb b x

file: Mathlib/Analysis/SpecialFunctions/Log/Base.lean:121
theorem logb_rpow_eq_mul_logb_of_pos (hx : 0 < x) : logb b (x ^ y) = y * logb b x

file: Mathlib/Analysis/SpecialFunctions/Log/Base.lean:146
theorem rpow_logb (hx : 0 < x) : b ^ logb b x = x        -- (b > 0, b ≠ 1)

file: Mathlib/Analysis/SpecialFunctions/Log/Base.lean:189
theorem logb_le_logb (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ x ≤ y    -- (b > 1)

file: Mathlib/Analysis/SpecialFunctions/Log/Base.lean:206
theorem logb_le_iff_le_rpow (hx : 0 < x) : logb b x ≤ y ↔ x ≤ b ^ y    -- (b > 1)

file: Mathlib/Analysis/SpecialFunctions/Log/Base.lean:212
theorem le_logb_iff_rpow_le (hy : 0 < y) : x ≤ logb b y ↔ b ^ x ≤ y    -- (b > 1)
```

## 3. Nat.ceil — `Mathlib.Algebra.Order.Floor.Semiring` / `Floor/Defs.lean`

主要使用 API:

```
file: Mathlib/Algebra/Order/Floor/Defs.lean:?
theorem Nat.ceil_le {α : Type*} [LinearOrderedSemifield α] [FloorSemiring α] {a : α} {n : ℕ} :
    ⌈a⌉₊ ≤ n ↔ a ≤ n

file: Mathlib/Algebra/Order/Floor/Semiring.lean:?
theorem Nat.le_ceil {α : Type*} [LinearOrderedSemifield α] [FloorSemiring α] (a : α) :
    a ≤ ⌈a⌉₊

file: Mathlib/Algebra/Order/Floor/Semiring.lean:?
theorem Nat.ceil_lt_add_one {α : Type*} [LinearOrderedSemifield α] [FloorSemiring α] {a : α}
    (ha : 0 ≤ a) : (⌈a⌉₊ : α) < a + 1
```

**鍵**: Shannon 語長 `⌈x⌉₊` で `x ≤ ⌈x⌉₊ < x + 1`。

## 4. Gibbs ingredient — `Mathlib.Analysis.SpecialFunctions.Log.Basic`

```
file: Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:306
theorem Real.log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x - 1
```

これで `Real.logb D x = Real.log x / Real.log D ≤ (x - 1) / Real.log D` (D > 1) で Gibbs 経路。

## 5. 既存 Common2026 API (関連)

- `Common2026/Shannon/Sanov.lean:73` `klDivSumForm P Q := ∑ a, P.real {a} * (log P {a} - log Q {a})` — finite-sum KL の textbook 形。Shannon code の lower bound 証明と同じ Gibbs パターンだが log 規約が違うため (`logb` vs `log`) 直接再利用はしない。
- `Common2026/Shannon/MaxEntropy.lean:229` `entropy_le_log_card`: `entropy μ X ≤ Real.log (Fintype.card α)`. これは base-`e` の `entropy` 形で、本シードの D-ary とは independent (将来 unify する場合は `log_div_log` 経由)。
- `Common2026/Shannon/AEP.lean` block source coding (`source_coding_theorem`): block-asymptotic 形、本シードは per-symbol 相補形。
