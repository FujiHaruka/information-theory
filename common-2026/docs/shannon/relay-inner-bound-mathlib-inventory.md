# T3-F Relay Inner Bound (DF/CF) Mathlib Inventory

> **Parent plan**: [`relay-inner-bound-moonshot-plan.md`](./relay-inner-bound-moonshot-plan.md)
>
> **Predecessor seed**: `Common2026/Shannon/RelayCutset.lean` (T3-F outer
> bound, 386 行, publish 2026-05-19).
>
> **Goal**: 既存 Common2026 + Mathlib 在庫を **relay inner bound (decode-and-
> forward / compress-and-forward)** の statement-level pass-through publish に
> 必要な範囲で棚卸し、撤退ライン L-RI1〜L-RI4 全発動下で `RelayInnerBound.lean`
> ~350-500 行 publish の足場を確定する。

## 1. 既存 Common2026 在庫 (黒箱 reuse)

### 1.1 Relay channel + relay code (T3-F outer bound 既存 publish からそのまま再利用)

- **`Common2026/Shannon/RelayCutset.lean:96`** — `abbrev RelayChannel`
  - 完全 signature:
    ```lean
    abbrev RelayChannel (α α₁ β β₁ : Type*)
        [MeasurableSpace α] [MeasurableSpace α₁]
        [MeasurableSpace β] [MeasurableSpace β₁] :=
      Kernel (α × α₁) (β × β₁)
    ```
  - 引数: `α α₁ β β₁ : Type*` + 4 つの `MeasurableSpace` インスタンス
  - 結論形: `Type` (型レベル kernel abbrev)
  - 役割: 本 plan の主定理 signature で受ける channel kernel 型。本 plan で
    再定義しない (`RelayCutset` を import して reuse)。

- **`Common2026/Shannon/RelayCutset.lean:115`** — `structure RelayCode`
  - 完全 signature:
    ```lean
    structure RelayCode (M n : ℕ) (α α₁ β β₁ : Type*)
        [MeasurableSpace α] [MeasurableSpace α₁]
        [MeasurableSpace β] [MeasurableSpace β₁] where
      encoder : Fin M → (Fin n → α)
      relay   : ∀ (i : Fin n), (Fin i.val → β₁) → α₁
      decoder : (Fin n → β) → Fin M
    ```
  - 引数: `M n : ℕ` + `α α₁ β β₁ : Type*` + 4 つの `MeasurableSpace`
  - 役割: 本 plan の存在形 inner bound (`∃ M n c, …`) の `c` の型として消費。
    relay field の dependent type の applying は本 plan 内でも発生しない
    (L-RI1 + L-RI2 全発動下で causality は全部 hypothesis pass-through 化)。

- **`Common2026/Shannon/RelayCutset.lean:188`** — `noncomputable def relayCutsetBound`
  - 完全 signature: `relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im`
  - 役割: 本 plan の inner bound では cutset bound 自体は使わない (DF/CF は
    Ib/Im とは別 4 数 / 5 数の min 構造)。ただし「outer bound と inner bound の
    関係」を docstring で参照する際に名前 `relayCutsetBound` を mention する。

### 1.2 Mutual / conditional mutual information primitives (L-RI1〜4 と直交)

- **`Common2026/Shannon/MutualInfo.lean:36`** — `mutualInfo (μ X Y : ...)`
- **`Common2026/Shannon/CondMutualInfo.lean:46`** — `condMutualInfo`

本 plan の主定理 signature では mutual information value 自体は **scalar `ℝ`**
で外から受ける形 (L-RI1/L-RI2/L-RI3/L-RI4 全発動下) なので、上記 primitive を
直接型レベルで触らない。docstring の参照のみ。

### 1.3 既存 inner bound publish pattern (本 plan 直接の雛形)

- **`Common2026/Shannon/MultipleAccessChannel.lean:531`** —
  `def MACInnerBoundExistence`
  - 完全 signature:
    ```lean
    def MACInnerBoundExistence
        {α₁ α₂ β : Type*}
        [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β]
        (R₁ R₂ : ℝ) : Prop :=
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M₁ M₂ : ℕ) (_c : MACCode M₁ M₂ n α₁ α₂ β),
          Real.exp ((n : ℝ) * R₁) ≤ (M₁ : ℝ)
          ∧ Real.exp ((n : ℝ) * R₂) ≤ (M₂ : ℝ)
    ```
  - 役割: **本 plan の `RelayDFInnerBoundExistence` /
    `RelayCFInnerBoundExistence` の signature 直接の雛形**。`R₁, R₂` を
    relay の単一 rate `R` に縮退 + `MACCode` を `RelayCode` に置換するだけ。

- **`Common2026/Shannon/MultipleAccessChannel.lean:567`** —
  `theorem mac_capacity_region_inner_bound`
  - 完全 signature:
    ```lean
    theorem mac_capacity_region_inner_bound
        (R₁ R₂ I₁ I₂ Iboth : ℝ)
        (_h_strict : R₁ < I₁ ∧ R₂ < I₂ ∧ R₁ + R₂ < Iboth)
        (_h_joint_typ : True)
        (h_existence : MACInnerBoundExistence (α₁ := α₁) (α₂ := α₂) (β := β) R₁ R₂) :
        MACInnerBoundExistence (α₁ := α₁) (α₂ := α₂) (β := β) R₁ R₂ :=
      h_existence
    ```
  - 役割: 本 plan の `relay_df_inner_bound` / `relay_cf_inner_bound` の
    body `:= h_existence` の完全雛形。`_h_strict` の不等式数と
    `_h_joint_typ : True` placeholder の数を DF/CF それぞれの achievability
    structure に合わせて拡張するのみ。

### 1.4 Outer bound (L-RC1〜5) との対称性

- **`Common2026/Shannon/RelayCutset.lean:343`** —
  `theorem relay_cutset_outer_bound`
  - signature の 7 引数 (`_hn`, `_c`, `R Ib Im`, `_h_csiszar`, `_h_chain`,
    `h_rate_bound`) は本 plan の inner bound 形と **数だけ揃える**:
    `_hn`, `_c`, `R I_DF_summands`, `_h_block_markov`, `_h_sliding_window`,
    `h_existence`。

## 2. Mathlib 在庫 (黒箱 reuse)

### 2.1 Existence / threshold form の足場

- **`Mathlib/Analysis/SpecialFunctions/Exp.lean`** — `Real.exp` (本 plan は
  存在形 `Real.exp ((n : ℝ) * R) ≤ (M : ℝ)` を MAC pattern と同形で書く)
- **`Mathlib/Order/MinMax.lean`** — `min_le_left`, `min_le_right`, `le_min`
  (DF rate / CF rate の `min` 構造の処理に必要)
- **`Mathlib/Data/Nat/Basic.lean`** — `Nat.le`, `∀ n ≥ N` の natural ordering

### 2.2 本 plan で必要な新 Mathlib API

**ゼロ** — 本 plan は statement-level hypothesis pass-through のみで、
proof tactic に新 Mathlib API は要らない。`exact h_existence` または
`⟨h.bound₁, h.bound₂, …⟩` のような 1 行 close のみ。

## 3. 設計確定事項

### 3.1 DF rate region (Cover-Thomas Theorem 15.10.2)

教科書本文 (Cover-Thomas Ch.15.10, eq. 15.236):

```
R ≤ min { I(X, X₁; Y),  I(X; Y, Y₁ | X₁) + I(X₁; Y) - I(X₁; Y, Y₁ | X) }
```

実用形式 (Cover-Thomas (15.232) original form):

```
R ≤ min { I(X; Y₁ | X₁) + I(X₁; Y),  I(X, X₁; Y) }
```

本 plan では **後者 (15.232) を採用** (signature が単純: 4 つの scalar
`I(X; Y₁ | X₁)`, `I(X₁; Y)`, `I(X, X₁; Y)` から `min { A + B, C }` を構成)。

- `InRelayDFRate R Imac Imrh Ibroad : Prop` — 2 つの DF 不等式を `structure`
  形で bundle (MAC 助力点 `Imac = I(X; Y₁ | X₁) + I(X₁; Y)` と broadcast 全
  `Ibroad = I(X, X₁; Y)` の min を `R` が下回るか):
  ```lean
  structure InRelayDFRate (R Imrh Iry Ibroad : ℝ) : Prop where
    boundMAC   : R ≤ Imrh + Iry      -- I(X; Y_1 | X_1) + I(X_1; Y)
    boundBroad : R ≤ Ibroad           -- I(X, X_1; Y)
  ```

  Cover-Thomas (15.232) 原形を **3 scalar `Imrh, Iry, Ibroad`** で受ける形
  (足し算 `Imrh + Iry` を本 file 内で完結)。

### 3.2 CF rate region (Cover-Thomas Theorem 15.10.3)

教科書本文 (Cover-Thomas Ch.15.10, eq. 15.243):

```
R ≤ I(X; Ŷ₁, Y | X₁)
```

subject to compression constraint (Wyner-Ziv side info):

```
I(X₁; Y) ≥ I(Y₁; Ŷ₁ | X₁, Y)
```

本 plan では **2 不等式の bundled form** を採用:

```lean
structure InRelayCFRate (R Idec Ix1y Iy1hy1 : ℝ) : Prop where
  rateBound       : R ≤ Idec                       -- I(X; Ŷ_1, Y | X_1)
  compressionFeas : Iy1hy1 ≤ Ix1y                  -- I(Y_1; Ŷ_1 | X_1, Y) ≤ I(X_1; Y)
```

CF の auxiliary `Ŷ_1` は本 plan 内では構造に embed しない (scalar `Idec`,
`Ix1y`, `Iy1hy1` で外から受ける)。

### 3.3 Existence form

DF / CF それぞれ:

```lean
def RelayDFInnerBoundExistence {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M : ℕ) (_c : RelayCode M n α α₁ β β₁),
      Real.exp ((n : ℝ) * R) ≤ (M : ℝ)

def RelayCFInnerBoundExistence {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M : ℕ) (_c : RelayCode M n α α₁ β β₁),
      Real.exp ((n : ℝ) * R) ≤ (M : ℝ)
```

MAC `MACInnerBoundExistence` と完全同形、`R₁, R₂` を単一 `R` に縮退。

## 4. 撤退ライン (L-RI シリーズ)

確定発動 4 本:

- **L-RI1**: block Markov encoding (DF achievability の構造的根幹) を
  `_h_block_markov : True` placeholder。Cover-Thomas 15.10.2 の B blocks
  random codebook + 段階的 cooperation の構成は ~600-1000 行。
- **L-RI2**: sliding-window joint typicality decoder (DF) を
  `_h_sliding_window : True` placeholder。各 block の段階的 decoding と
  error event collapse は ~400-600 行。
- **L-RI3**: Wyner-Ziv binning (CF) を `_h_wz_binning : True` placeholder。
  compression with side info の random binning ~500-700 行。
- **L-RI4**: side-information decoding (CF) を `_h_si_decode : True`
  placeholder。Ŷ_1 reconstruction + final decoding ~300-500 行。

主定理 body は `:= h_existence` の identity wrap、合計 ~1800-2800 行を別 seed に defer。

## 5. ファイル構成

```
Common2026/Shannon/
  RelayInnerBound.lean   ← 新規 (~350-500 行)
    ・InRelayDFRate (structure, 2 不等式)
    ・InRelayCFRate (structure, 2 不等式)
    ・RelayDFInnerBoundExistence (def, MAC inner bound pattern 流用)
    ・RelayCFInnerBoundExistence (def, 同上)
    ・relay_df_inner_bound (主定理 1, body := h_existence)
    ・relay_cf_inner_bound (主定理 2, body := h_existence)
    ・rate region helper lemmas (InRelayDFRate.mk', .iff_and, .mono_*)
    ・log-rate form wrappers
```

`Common2026.lean` は呼び出し側オーケストレータが import 追加 (本 plan 内では編集しない)。

## 6. 規模見積

| Phase | 中央 | 範囲 |
|---|---|---|
| Skeleton + structures + defs | 100 | 80-150 |
| DF inner bound + helpers | 100 | 80-150 |
| CF inner bound + helpers | 100 | 80-150 |
| Two-side wrappers + log-rate | 50 | 30-80 |
| docstring + cross-link | 50 | 40-80 |
| **合計** | **400** | **350-500** |

撤退 4 本全発動下、`lake env lean RelayInnerBound.lean` 単一 file 5-10 秒
inner loop。

## 7. Phase A skeleton (出だし)

```lean
import Common2026.Shannon.RelayCutset

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

section DFRate
structure InRelayDFRate (R Imrh Iry Ibroad : ℝ) : Prop where
  boundMAC   : R ≤ Imrh + Iry
  boundBroad : R ≤ Ibroad
end DFRate

section CFRate
structure InRelayCFRate (R Idec Ix1y Iy1hy1 : ℝ) : Prop where
  rateBound       : R ≤ Idec
  compressionFeas : Iy1hy1 ≤ Ix1y
end CFRate

section ExistenceForms
def RelayDFInnerBoundExistence {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M : ℕ) (_c : RelayCode M n α α₁ β β₁),
      Real.exp ((n : ℝ) * R) ≤ (M : ℝ)

def RelayCFInnerBoundExistence {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N,
    ∃ (M : ℕ) (_c : RelayCode M n α α₁ β β₁),
      Real.exp ((n : ℝ) * R) ≤ (M : ℝ)
end ExistenceForms

theorem relay_df_inner_bound
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R Imrh Iry Ibroad : ℝ)
    (_h_in_df_region : InRelayDFRate R Imrh Iry Ibroad)
    (_h_block_markov : True)
    (_h_sliding_window : True)
    (h_existence :
        RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayDFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  h_existence

theorem relay_cf_inner_bound
    {α α₁ β β₁ : Type*}
    [MeasurableSpace α] [MeasurableSpace α₁]
    [MeasurableSpace β] [MeasurableSpace β₁]
    (R Idec Ix1y Iy1hy1 : ℝ)
    (_h_in_cf_region : InRelayCFRate R Idec Ix1y Iy1hy1)
    (_h_wz_binning : True)
    (_h_si_decode : True)
    (h_existence :
        RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R) :
    RelayCFInnerBoundExistence (α := α) (α₁ := α₁) (β := β) (β₁ := β₁) R :=
  h_existence

end InformationTheory.Shannon
```
