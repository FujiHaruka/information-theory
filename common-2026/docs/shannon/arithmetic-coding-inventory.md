# Arithmetic Coding (Shannon-Fano-Elias) genuine 化 — Mathlib + InformationTheory API 在庫

> **Family**: Shannon / **Scope**: T4-A arithmetic coding (Cover-Thomas Ch.13.3) の genuine 構成置換調査
>
> **対象ファイル**: `InformationTheory/Shannon/ArithmeticCoding.lean` (現 288 行、完全 pass-through)
>
> **親計画**: [`arithmetic-coding-moonshot-plan.md`](./arithmetic-coding-moonshot-plan.md) / 先行 M0 在庫: [`arithmetic-coding-mathlib-inventory.md`](./arithmetic-coding-mathlib-inventory.md)
>
> 本ファイルは「pass-through を本物の構成に置換する」観点での再調査。先行 M0 在庫 (`arithmetic-coding-mathlib-inventory.md`) は「Mathlib 在庫 ZERO、撤退ライン 3 本全発動」と結論したが、**`ShannonCodeKraftReverse.lean` に既存の genuine prefix-code 構成があることを見落としている**。本調査の最大の発見はこの点。

---

## 一行サマリ

**期待長 sandwich (`H ≤ E[L] ≤ H+2`) は ShannonCode 機構の線形 lift で full discharge 可能 (既存率 ~90%)。prefix-free 構成も `ShannonCodeKraftReverse.shannonFanoCode` (既存の genuine MSB-first digit-expansion code) を `finTwoEquiv` で `List Bool` に lift すれば 8 割再利用可能。** 真の Mathlib gap は「実数 `F̄(a) ∈ [0,1)` の二進展開を `List Bool` で得る forward 関数」のみ (Mathlib に存在せず — `Real.fromBinary` は逆方向のみ)。ただし**この forward 二進展開は arithmetic coding には実は不要** — `ShannonCodeKraftReverse` は累積分布を整数 slot (`slotStart : ℕ`) で扱い実数二進展開を一切経由しない。**自作必要は 3〜4 件、撤退ライン発動 no (段階的着地で full discharge 圏内)**。

---

## 主定理の最終形 (現 signature と genuine 目標)

### 現状 (pass-through, `ArithmeticCoding.lean:249`)

```lean
theorem arithmetic_coding_expected_length_bounds
    (P : Measure α) [IsProbabilityMeasure P]
    (c : ArithmeticCode α)                                      -- opaque codeword field
    (_h_trunc : IsCumulativeTruncationPassthrough P c.length)   -- : Prop := True
    (_h_pf : IsArithmeticPrefixFreePassthrough c.codeword)      -- : Prop := True
    (_h_exp : IsArithmeticExpectedLengthPassthrough P c.length) -- : Prop := True
    (h_bound : entropyD 2 P ≤ expectedLength P c.length
                ∧ expectedLength P c.length ≤ entropyD 2 P + 2) :
    entropyD 2 P ≤ expectedLength P c.length ∧
      expectedLength P c.length ≤ entropyD 2 P + 2 := h_bound  -- 結論=仮説
```

問題: `c : ArithmeticCode α` が任意なので `c.length` は任意 → sandwich は仮説なしには成立しない。genuine 化には **「具体的構成 `arithmeticCode P` への bound」へ restate** が必須 (ブロック C 参照)。

### genuine 目標 (推奨 restate)

```lean
/-- Shannon-Fano-Elias の語長 l(a) = ⌈-log₂ P(a)⌉ + 1. -/
noncomputable def sfeLength (P : Measure α) (a : α) : ℕ := shannonLength 2 P a + 1

theorem arithmeticCode_expected_length_bounds
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a}) :
    entropyD 2 P ≤ expectedLength P (sfeLength P) ∧
      expectedLength P (sfeLength P) ≤ entropyD 2 P + 2 := by
  -- 下界: entropyD_le_expectedLength_of_kraft (既存)、sfeLength も Kraft 充足 (l↑ なら Kraft↓)
  -- 上界: expectedLength P (sfeLength P) = expectedLength P (shannonLength 2 P) + 1
  --        < (H + 1) + 1 = H + 2  via expectedLength_shannon_lt_entropyD_add_one (既存)
  sorry

theorem arithmeticCode_prefix_free (P : Measure α) (hP : ∀ a, 0 < P.real {a}) :
    ∃ c : α → List Bool, (∀ a, (c a).length = sfeLength P a) ∧
      Function.Injective c ∧ (∀ a b, a ≠ b → ¬ c a <+: c b) := by
  -- exists_prefix_code_of_kraft (既存, ShannonCodeKraftReverse) を D=2, l=sfeLength で適用
  -- → c : α → List (Fin 2)、finTwoEquiv で List Bool に map (prefix_map_iff_of_injective で性質保存)
  sorry
```

---

## ブロック A — 既存 common-2026 機構 (再利用元)

### A1. `InformationTheory/Shannon/ShannonCode.lean` (Cover-Thomas 5.4 / 5.8.1)

| 概念 | API | file:line | 状態 | genuine 化での扱い |
|---|---|---|---|---|
| D-ary entropy | `entropyD` | `ShannonCode.lean:45` | 既存 | `entropyD 2 P` を黒箱 reuse |
| 期待長 | `expectedLength` | `ShannonCode.lean:55` | 既存 | `expectedLength P (sfeLength P)` |
| Kraft 和 | `kraftSum` | `ShannonCode.lean:59` | 既存 | sfeLength の Kraft 充足証明に使う |
| Shannon 語長 | `shannonLength` | `ShannonCode.lean:51` | 既存 | `sfeLength P a := shannonLength 2 P a + 1` の土台 |
| 源符号化下界 | `entropyD_le_expectedLength_of_kraft` | `ShannonCode.lean:164` | **既存 (下界の核)** | sfeLength も Kraft 充足するので `H ≤ E[L]` 側を直接適用 |
| Shannon 上界 | `expectedLength_shannon_lt_entropyD_add_one` | `ShannonCode.lean:261` | **既存 (上界の核)** | `E[L_sfe] = E[L_shannon] + 1 < (H+1)+1 = H+2` の lift 元 |
| Shannon 語長の Kraft 充足 | `shannonLength_kraft_le_one` | `ShannonCode.lean:129` | 既存 | sfeLength の Kraft (より小さい) を sandwich する補助 |
| sandwich main | `shannonCode_expected_length_bounds` | `ShannonCode.lean:345` | 既存 | テンプレート |

**完全 signature (verbatim、`omit` 含む)**:

- `entropyD`:
  ```
  noncomputable def entropyD (D : ℝ) (P : Measure α) : ℝ :=
    -∑ a : α, P.real {a} * Real.logb D (P.real {a})
  ```
  section context: `variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`

- `expectedLength`:
  ```
  noncomputable def expectedLength (P : Measure α) (l : α → ℕ) : ℝ :=
    ∑ a : α, P.real {a} * (l a : ℝ)
  ```

- `entropyD_le_expectedLength_of_kraft` (源符号化下界 — **これが「H ≤ E[L] があるか」の答え: YES**):
  ```
  omit [DecidableEq α] [Nonempty α] in
  theorem entropyD_le_expectedLength_of_kraft
      {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P]
      (hP : ∀ a : α, 0 < P.real {a})
      (l : α → ℕ) (h_kraft : kraftSum D l ≤ 1) :
      entropyD D P ≤ expectedLength P l
  ```
  - 引数: `(hD : 1 < D)`, `(P : Measure α)`, instance `[IsProbabilityMeasure P]`, `(hP : ∀ a, 0 < P.real {a})`, `(l : α → ℕ)`, `(h_kraft : kraftSum D l ≤ 1)`
  - 結論形 (verbatim): `entropyD D P ≤ expectedLength P l`
  - 注意: **`hP : ∀ a, 0 < P.real {a}` (full support) が必須**。任意 `l` に対して成立 (Kraft 充足のみ前提) → sfeLength に直接適用可。

- `expectedLength_shannon_lt_entropyD_add_one` (上界の核):
  ```
  omit [DecidableEq α] in
  theorem expectedLength_shannon_lt_entropyD_add_one
      {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P]
      (hP : ∀ a : α, 0 < P.real {a}) :
      expectedLength P (shannonLength D P) < entropyD D P + 1
  ```
  - 結論形 (verbatim): `expectedLength P (shannonLength D P) < entropyD D P + 1`
  - 上界 lift: `expectedLength P (fun a => shannonLength D P a + 1) = expectedLength P (shannonLength D P) + (Σ P(a)·1) = expectedLength P (shannonLength D P) + 1 < (H+1)+1 = H+2`。`Σ_a P.real{a} = 1` の補題は ShannonCode 内に同型のものが複数回展開済 (`MeasureTheory.sum_measureReal_singleton`)。

### A2. `InformationTheory/Shannon/ShannonCodeKraftReverse.lean` (B-8' — **genuine prefix-code 構成、本調査の最重要発見**)

**この file が「ブロック B の hard part」を既に解決している。** 累積分布を実数二進展開ではなく **整数 slot (`slotStart : ℕ`)** で扱い、MSB-first base-`D` digit expansion でコードを生成、prefix-free を整数除算の代数で証明済。

| 概念 | API | file:line | 状態 | genuine 化での扱い |
|---|---|---|---|---|
| MSB-first 固定長 D-進展開 | `toBaseDLen` | `ShannonCodeKraftReverse.lean:41` | 既存 | 「整数 ⌊x·2^k⌋ の k-bit 表現」の役 (二進展開の代替) |
| prefix-free 述語 | `IsPrefixFree` | `ShannonCodeKraftReverse.lean:47` | 既存 | `List (Fin D)` 版。`List Bool` に lift 要 |
| take=prefix 橋 | `toBaseDLen_take` | `ShannonCodeKraftReverse.lean:60` | 既存 | 区間 disjoint→prefix の核 (整数版) |
| prefix→桁一致 | `toBaseDLen_eq_of_isPrefix` | `ShannonCodeKraftReverse.lean:82` | 既存 | 同上 |
| 桁単射 (有界域) | `toBaseDLen_injOn_lt` | `ShannonCodeKraftReverse.lean:95` | 既存 | 区間 disjoint の核 |
| slot 累積和 | `slotStart` | `ShannonCodeKraftReverse.lean:172` | 既存 | 累積分布 F の整数版 (実数 F̄ を回避) |
| slot 単調・gap | `slotStart_mono` / `slotStart_succ` / `slotStart_gap` | `:183`/`:194`/`:330` | 既存 | disjoint interval の代数 |
| Kraft→slot 上界 | `kraft_sum_nat_le_of_real` / `slotStart_le_pow` | `:237`/`:271` | 既存 | Kraft 充足から slot < D^L |
| **prefix-free 性 (本体)** | `shannonFanoCode_prefixFree` | `ShannonCodeKraftReverse.lean:422` | **既存 (genuine)** | prefix-free 構成の主役 |
| 単射性 | `shannonFanoCode_injective` | `ShannonCodeKraftReverse.lean:461` | 既存 | unique-decodable の素材 |
| **存在主定理** | `exists_prefix_code_of_kraft` | `ShannonCodeKraftReverse.lean:482` | **既存 (genuine)** | prefix-free 構成を一発で供給 |

**完全 signature (verbatim)**:

- `exists_prefix_code_of_kraft` (**prefix code 存在主定理 — Kraft 逆向き**):
  ```
  theorem exists_prefix_code_of_kraft
      {D : ℕ} (hD : 2 ≤ D)
      (l : α → ℕ) (hl : ∀ a, 0 < l a)
      (hk : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
      ∃ c : α → List (Fin D),
        Function.Injective c ∧
        (∀ a, (c a).length = l a) ∧
        IsPrefixFree c
  ```
  - section context: `variable {α : Type*} [Fintype α] [DecidableEq α]`
  - 引数: `{D : ℕ}`, `(hD : 2 ≤ D)`, `(l : α → ℕ)`, `(hl : ∀ a, 0 < l a)`, `(hk : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1)`
  - 結論形 (verbatim): `∃ c : α → List (Fin D), Function.Injective c ∧ (∀ a, (c a).length = l a) ∧ IsPrefixFree c`
  - **前提**: `hl : ∀ a, 0 < l a` — sfeLength は `shannonLength + 1 ≥ 1 > 0` で自動充足。`hk` の Kraft は `∑ D^(-l a) ≤ 1` 形 (= `kraftSum D l ≤ 1` を展開した形)。
  - **codeword 型は `List (Fin D)`、目標は `List Bool`** → `finTwoEquiv` で map 要 (ブロック B 参照)。

- `IsPrefixFree` (述語):
  ```
  def IsPrefixFree {D : ℕ} (c : α → List (Fin D)) : Prop :=
    ∀ a b : α, a ≠ b → ¬ c a <+: c b
  ```
  → 現 `ArithmeticCoding.lean` の `arithmetic_coding_prefix_free` の結論 `∀ a b, a ≠ b → ¬ c.codeword a <+: c.codeword b` と完全同型 (D=2)。

- `toBaseDLen` (整数 → 固定長 D-進列、二進展開の代替):
  ```
  def toBaseDLen (D : ℕ) [NeZero D] (L n : ℕ) : List (Fin D) :=
    List.ofFn (n := L) fun i =>
      ⟨(n / D ^ (L - 1 - (i : ℕ))) % D, Nat.mod_lt _ (Nat.pos_of_neZero D)⟩
  ```

### A3. Kraft の両向き (両方そろっている)

| 向き | API | file:line | 状態 |
|---|---|---|---|
| forward: prefix code ⟹ Kraft 充足 (McMillan) | Mathlib `kraft_mcmillan_inequality` | (下記 B 参照) | 既存 (Mathlib) |
| reverse: Kraft 充足 ⟹ prefix code 存在 | `exists_prefix_code_of_kraft` | `ShannonCodeKraftReverse.lean:482` | 既存 (自作済) |
| Shannon 語長は Kraft 充足 | `shannonLength_kraft_le_one` | `ShannonCode.lean:129` | 既存 |

→ **prefix code ⟺ Kraft の両向きとも完備**。

---

## ブロック B — Mathlib の二進展開 / List Bool / 実数切詰め

### B1. 実数 `x ∈ [0,1)` の二進展開を得る API — **forward は不在 (gap)、ただし不要**

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `(ℕ → Bool) → unitInterval` (逆方向) | `Real.fromBinary` | `Mathlib/Topology/MetricSpace/HausdorffAlexandroff.lean:43` | 既存だが**逆方向** | 使えない (bits→real、欲しいのは real→bits) |
| `(ℝ → (ℕ → Bool))` (forward 二進展開) | — | — | ❌ **該当 0 件** (`loogle "(ℝ → (ℕ → Bool))"` → `0 match`) | gap |
| Cantor 関数 | `Cardinal.cantorFunction` 系 | `Mathlib/Analysis/Real/Cardinality.lean` | 既存だが base-3 中心 | 使えない |
| `Int.fract` の二進切詰め | — | — | ❌ `loogle "Int.fract, Nat.digits"` → `0 件` | gap |

- `Real.fromBinary` の完全 signature (verbatim):
  ```
  noncomputable def fromBinary : (ℕ → Bool) → unitInterval :=
    let φ : (ℕ → Bool) ≃ₜ (ℕ → Fin 2) := Homeomorph.piCongrRight
      (fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
    Subtype.coind (ofDigits ∘ φ) (fun _ ↦ ⟨ofDigits_nonneg _, ofDigits_le_one _⟩)
  ```
  関連: `Real.fromBinary_surjective` / `Real.fromBinary_continuous` (同 file:51/48) — surjective だが injective でも逆関数でもない。

**結論 (重要)**: 実数 `F̄(a) = F(a) - P(a)/2` の forward 二進展開は Mathlib gap。**しかし `ShannonCodeKraftReverse` は実数二進展開を一切使わず、累積を整数 `slotStart : ℕ` で構成し `toBaseDLen` (整数→桁列) で符号化する。** よって教科書 (Cover-Thomas 13.3.2) の「実数中点の二進展開」を literal 形式化する必要はなく、整数 slot 構成で genuine prefix-free が既に取れている。教科書同値性 (中点二進展開 = slot 構成) を別補題で示すのは optional。

### B2. `List.IsPrefix` (`<+:`) 関連補題 — 完備 (Lean core `Init`)

| 概念 | API | file:line | 状態 | 完全 signature (verbatim) |
|---|---|---|---|---|
| prefix ⟹ 長さ ≤ | `List.IsPrefix.length_le` | `Init/Data/List/Sublist.lean:797` | 既存 | `theorem IsPrefix.length_le (h : l₁ <+: l₂) : l₁.length ≤ l₂.length` |
| 同長 prefix ⟹ 相等 | `List.IsPrefix.eq_of_length` | `Init/Data/List/Sublist.lean:882` | 既存 | `theorem IsPrefix.eq_of_length (h : l₁ <+: l₂) : l₁.length = l₂.length → l₁ = l₂` |
| 長さ逆 prefix ⟹ 相等 | `List.IsPrefix.eq_of_length_le` | `Init/Data/List/Sublist.lean:885` | 既存 | `theorem IsPrefix.eq_of_length_le (h : l₁ <+: l₂) : l₂.length ≤ l₁.length → l₁ = l₂` |
| prefix ⟺ take | `List.prefix_iff_eq_take` | `Init/Data/List/Sublist.lean:1328` | 既存 | `theorem prefix_iff_eq_take : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂` |
| map 下の prefix (単射 f) | `List.prefix_map_iff_of_injective` | `Init/Data/List/Nat/Sublist.lean:141` | **既存 (lift 橋)** | `theorem prefix_map_iff_of_injective {f : α → β} (hf : Function.Injective f) : l₁.map f <+: l₂.map f ↔ l₁ <+: l₂` |
| map 下の prefix | `List.IsPrefix.map` | `Init/Data/List/Sublist.lean` | 既存 | `(h : l₁ <+: l₂) → l₁.map f <+: l₂.map f` |

- `prefix_map_iff_of_injective` の引数: `{f : α → β}`, `(hf : Function.Injective f)`; 結論形 (verbatim): `l₁.map f <+: l₂.map f ↔ l₁ <+: l₂`
- これらは Lean core `Init` (Mathlib ではなく toolchain 同梱) なので import 不要 (List 基本が入れば自動)。`ShannonCodeKraftReverse` 内で既に `IsPrefix.length_le`, `prefix_iff_eq_take`, `IsPrefix.eq_of_length_le` を使用済 (= 動作確認済)。

### B3. 整数 `⌊x·2^k⌋` の k-bit 表現 — `toBaseDLen` (自作済) で充足、Mathlib `Nat.digits` は形が合わない

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| 整数→固定長 D-進列 (MSB-first) | `toBaseDLen` (自作) | `ShannonCodeKraftReverse.lean:41` | **既存 (推奨)** | これを使う |
| `Nat.digits 2` | Mathlib `Nat.digits` | `Mathlib/Data/Nat/Digits/*` | 既存だが LSB-first・可変長 | 固定長 prefix 論証に不向き |
| `Nat.digits 2 = Nat.bits` 同値 | `Nat.digits_two_eq_bits` | `Mathlib/Data/Nat/Digits/Lemmas.lean` | 既存 | 参考のみ |
| `Nat.testBit` × `Nat.div` | — | — | ❌ `loogle` → `0 件` (組合せ補題なし) | 使わない |

**結論**: 「整数の固定長二進表現 + その prefix 性」は Mathlib の `Nat.digits` (LSB-first, 可変長) では prefix 論証に不向き。`ShannonCodeKraftReverse.toBaseDLen` (MSB-first, 固定長) が **既に最適な形で自作済**で、prefix 補題 (`toBaseDLen_take`, `toBaseDLen_injOn_lt`) もそろっている。

### B4. 区間 disjoint → prefix-free の橋 — **整数 slot 形では `ShannonCodeKraftReverse` に既存、実数区間形は Mathlib 不在**

| 概念 | API | file:line | 状態 |
|---|---|---|---|
| `Set.Ico` disjoint ⟹ prefix-free (実数区間形) | — | — | ❌ `loogle "List.IsPrefix, Set.Ico"` → `0 件` |
| 整数 slot gap ⟹ ¬ prefix (整数形) | `not_isPrefix_of_sortedIndex_lt` | `ShannonCodeKraftReverse.lean:358` | **既存** |

→ 教科書の「実数区間 disjoint → prefix-free」は Mathlib 不在だが、その整数版 (slot gap → ¬prefix) は `ShannonCodeKraftReverse` に完備。

### B5. `Fin 2` ↔ `Bool` の lift

| 概念 | API | file:line | 完全 signature |
|---|---|---|---|
| `Fin 2 ≃ Bool` | `finTwoEquiv` | `Mathlib/Logic/Equiv/Defs.lean:902` | `def finTwoEquiv : Fin 2 ≃ Bool` |
| `⌈a⌉₊ < a + 1` | `Nat.ceil_lt_add_one` | `Mathlib/Algebra/Order/Floor/Semiring.lean:357` | `theorem ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : R) < a + 1` (context: `variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R}` + `[IsStrictOrderedRing R]`) |

→ `exists_prefix_code_of_kraft` が返す `c : α → List (Fin 2)` を `fun a => (c a).map finTwoEquiv : α → List Bool` に変換。prefix-free は `prefix_map_iff_of_injective finTwoEquiv.injective` で保存、length は `List.length_map` で保存。

### B6. Mathlib `kraft_mcmillan_inequality` (McMillan forward, unique-decodable → Kraft)

- file:line: `Mathlib/InformationTheory/Coding/KraftMcMillan.lean:149`
- 完全 signature (verbatim):
  ```
  public theorem kraft_mcmillan_inequality {S : Finset (List α)} [Fintype α] [Nonempty α]
      (h : UniquelyDecodable (S : Set (List α))) :
      ∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1
  ```
  - 引数: `{S : Finset (List α)}`, instance `[Fintype α] [Nonempty α]`, `(h : UniquelyDecodable (S : Set (List α)))`
  - 結論形 (verbatim): `∑ w ∈ S, (1 / Fintype.card α : ℝ) ^ w.length ≤ 1`
  - **前提注意**: `[Fintype α]` は**符号アルファベット** (`Bool` → `Fin 2`、card 2) に対する Fintype。`Finset (List α)` 表現 (文字列符号水準) なので、`α → List Bool` 関数水準とは形が違う (橋渡しに `Finset.image codeword univ` 等が要る)。
- `UniquelyDecodable` 定義: `Mathlib/InformationTheory/Coding/UniquelyDecodable.lean:35`
  ```
  def UniquelyDecodable (S : Set (List α)) : Prop :=
    ∀ (L₁ L₂ : List (List α)),
      (∀ w ∈ L₁, w ∈ S) → (∀ w ∈ L₂, w ∈ S) →
      L₁.flatten = L₂.flatten → L₁ = L₂
  ```
- 関連: `UniquelyDecodable.flatten_injective` (`UniquelyDecodable.lean:51`) / `UniquelyDecodable.epsilon_not_mem` (`:46`)

→ 現 `arithmetic_coding_unique_decodable` の結論 (`(s₁.map c).flatten = (s₂.map c).flatten → s₁ = s₂`) は Mathlib `UniquelyDecodable` を `α`-string list で書き換えた形。Mathlib 定義は `List (List α)` 形なので橋が要る。**prefix-free ⟹ unique-decodable の direct 補題は Mathlib に不在** (McMillan は逆向き) → 自作要 (下記)。

---

## 主要前提条件ボックス (前提事故注意)

- **`entropyD_le_expectedLength_of_kraft` (源符号化下界)**: `(hD : 1 < D)` / `[IsProbabilityMeasure P]` / `(hP : ∀ a, 0 < P.real {a})` (**full support 必須**) / `(h_kraft : kraftSum D l ≤ 1)`。sfeLength は `shannonLength+1` で Kraft 和が `shannonLength` より小さい → 充足は `shannonLength_kraft_le_one` を sandwich で示す (各項 `2^(-(l+1)) ≤ 2^(-l)` の Σ)。
- **`expectedLength_shannon_lt_entropyD_add_one` (上界)**: 同じく `(hP : ∀ a, 0 < P.real {a})` (full support) が本質。strict `<` は `Nat.ceil_lt_add_one` (`ha : 0 ≤ a` 前提、`a = -logb D P(a) ≥ 0` は `logb_nonpos` で確保、ShannonCode 内に既出パターン) + `Finset.sum_lt_sum` で導く。
- **`exists_prefix_code_of_kraft` (prefix-free 構成)**: `(hD : 2 ≤ D)` (D は **ℕ**、binary なら `D = 2`) / `(hl : ∀ a, 0 < l a)` (sfeLength で自動) / `(hk : ∑ a, (D:ℝ)^(-(l a:ℤ)) ≤ 1)` (= `kraftSum (D:ℝ) l ≤ 1` を展開した形、ℕ→ℝ cast 注意)。section に `[Fintype α] [DecidableEq α]` 要 (現 `ArithmeticCoding.lean` の variable と整合)。返り値は `List (Fin 2)` → `List Bool` lift 要。
- **`kraft_mcmillan_inequality` (McMillan)**: `[Fintype α] [Nonempty α]` は**符号文字**側 (`Fin 2`)。`Finset (List α)` 形なので `α → List Bool` 関数水準への橋が要る。**unique-decodability に使うなら、prefix-free→UD は別途自作** (Mathlib に prefix→UD direct なし)。
- **`Nat.ceil_lt_add_one`**: `[Semiring R] [LinearOrder R] [FloorSemiring R] [IsStrictOrderedRing R]` + `(ha : 0 ≤ a)`。`R = ℝ` で自動充足。

---

## 自作が必要な要素 (優先度順)

1. **`sfeLength` 定義 + Kraft 充足補題** (優先度: 高、~15-25 行)
   - `sfeLength P a := shannonLength 2 P a + 1`。`kraftSum 2 (sfeLength P) ≤ 1` を `shannonLength_kraft_le_one` から (各項 `2^(-(l+1)) = 2^(-l)/2 ≤ 2^(-l)`、Σ で `≤ Σ 2^(-l) ≤ 1`)。
   - 落とし穴: Kraft 和の項を半分にする計算 (`zpow` の `-(l+1) = -l - 1`)。ShannonCode の `zpow_neg_natCast_eq_rpow` (`:93`) 系を再利用。

2. **期待長 sandwich `arithmeticCode_expected_length_bounds`** (優先度: 高、~30-50 行) — **full discharge 圏内**
   - 下界: `entropyD_le_expectedLength_of_kraft hD P hP (sfeLength P) (kraft 充足)` 直適用。
   - 上界: `expectedLength P (sfeLength P) = expectedLength P (shannonLength 2 P) + 1` (Σ の線形性 + `Σ P(a) = 1`)、`expectedLength_shannon_lt_entropyD_add_one` の `< H+1` を `+1` して `< H+2` → `≤ H+2`。
   - 落とし穴: `expectedLength P (fun a => l a + 1)` の展開で `Nat.cast_add`、`Finset.sum_add_distrib`、`sum_measureReal_singleton` (ShannonCode 内に既出)。

3. **prefix-free 構成 `arithmeticCode_prefix_free`** (優先度: 中、~25-40 行) — **8 割再利用**
   - `exists_prefix_code_of_kraft (hD : 2 ≤ 2) (sfeLength P) (hl) (hk)` で `c : α → List (Fin 2)` を得る。
   - `finTwoEquiv` で `fun a => (c a).map finTwoEquiv : α → List Bool` に変換。
   - prefix-free 保存: `prefix_map_iff_of_injective finTwoEquiv.injective`。length 保存: `List.length_map`。injective 保存: `List.map_injective` + `finTwoEquiv.injective`。
   - 落とし穴: `hk` の形 — `exists_prefix_code_of_kraft` は `∑ (D:ℝ)^(-(l a:ℤ)) ≤ 1` を要求 (`kraftSum` の `unfold` 形)。`kraftSum 2 (sfeLength P)` から cast (`D : ℕ = 2` → `(2:ℝ)`) 注意。

4. **prefix-free ⟹ unique-decodable** (優先度: 低/optional、~40-80 行) — Mathlib に direct なし
   - Cover-Thomas 5.2.2: prefix code ⊆ uniquely decodable。Mathlib `UniquelyDecodable` (`List (List α)` 形) への橋が要る。greedy decode の単射性を `flatten` の長さ最小元一意性で示す (帰納)。
   - 代替: `arithmetic_coding_unique_decodable` を「prefix-free 仮定を取り結論を返す」honest brick として分離 (撤退ライン縮退、下記)。

5. **(optional) 教科書同値性: 中点二進展開 = slot 構成** (優先度: 最低)
   - Cover-Thomas literal の `F̄(a)` 中点二進展開と `slotStart` 構成の同値。実用上不要 (両者とも同じ prefix-free code を与えるが、本数式の genuine 性は slot 構成で完結)。書くなら `Real.fromBinary` gap に直面 (~100-200 行)。**書かないことを推奨**。

**推定総工数 (1〜3 まで、4 を honest brick 分離)**: ~70-115 行で期待長 full discharge + prefix-free 構成 genuine。4 を full 化するなら +40-80 行。

---

## ブロック C — 構成回避の代替設計の所見

- **主定理 restate は必須**。現 signature `(c : ArithmeticCode α)` は任意符号を取るため sandwich は仮説なしには偽。genuine 化は「具体構成 `sfeLength P` / `arithmeticCode P` に対する bound」へ restate する (上記「genuine 目標」)。これは pass-through 解消の不可避な構造変更。`ArithmeticCode` structure 自体は残してよい (`arithmeticCode P : ArithmeticCode α` を構成 def として与える)。

- **期待長 sandwich は length-only 仮定で二進展開を完全回避し full discharge 可能 (推奨)**。`sfeLength P a = shannonLength 2 P a + 1` という length 関数だけ定義すれば、`H ≤ E[L] ≤ H+2` は ShannonCode 機構 (`entropyD_le_expectedLength_of_kraft` + `expectedLength_shannon_lt_entropyD_add_one`) の線形 lift で閉じる。**二進展開・符号語の構成を一切経由しない**。これが最も確実な full discharge 経路 (推定 ~50-75 行)。

- **prefix-free 構成も二進展開 (実数) を回避して full discharge 可能**。当初の懸念「実数 F̄ の二進展開が Mathlib gap」は、`ShannonCodeKraftReverse.exists_prefix_code_of_kraft` (整数 slot 構成) が既にあるため回避される。`List (Fin 2) → List Bool` の lift (`finTwoEquiv` + `prefix_map_iff_of_injective`) だけが追加作業 (~25-40 行)。**「prefix-free は honest brick 分離」まで縮退する必要はない**。

- **段階的着地 (推奨設計、現実的)**:
  1. **Stage 1 (full discharge, ~70-115 行)**: 期待長 sandwich + prefix-free 構成を両方 genuine 化。length は ShannonCode lift、prefix-free は `exists_prefix_code_of_kraft` lift。**二進展開 gap は両方とも回避**。
  2. **Stage 2 (optional, +40-80 行)**: prefix-free ⟹ unique-decodable を Mathlib `UniquelyDecodable` 経由で genuine 化。これだけは Mathlib に direct 補題がないため自作。重ければ honest brick (prefix-free 仮定 pass-through) で残す。
  3. **Stage 3 (書かない推奨)**: 教科書 literal (実数中点二進展開) との同値。`Real.fromBinary` gap に直面、実用価値低。

- **推定 Lean 行数まとめ**:
  - 期待長 full discharge のみ: ~50-75 行 (最小着地)
  - + prefix-free 構成 genuine: +25-40 行
  - + unique-decodable genuine: +40-80 行
  - = full genuine (Stage 1+2): ~115-195 行 (現 288 行の pass-through 置換として妥当)

---

## 撤退ラインへの距離

親計画 ([`arithmetic-coding-moonshot-plan.md`](./arithmetic-coding-moonshot-plan.md)) の撤退ライン:
> [L-AC1] cumulative-distribution truncation を `Prop := True` で pass-through /
> [L-AC2] prefix-free 性を `Prop := True` で pass-through /
> [L-AC3] 平均長 `E[L] ≤ H+2` を hypothesis として受け body は `:= h_bound`。

**判定: 撤退ライン発動 = NO (genuine 化により 3 本とも解除可能)**。

- **L-AC3 (期待長)**: 解除。ShannonCode lift で full discharge (二進展開不要)。
- **L-AC1 + L-AC2 (truncation + prefix-free)**: 解除。`exists_prefix_code_of_kraft` (整数 slot 構成、既存 genuine) + `finTwoEquiv` lift で full discharge。**当初撤退理由「実数二進展開が Mathlib gap」は整数 slot 構成で回避される**ため発動不要。

**新規撤退ライン (縮退案、Stage 2 が重い場合のみ)**:
- **[L-AC4 (新)] unique-decodable**: prefix-free ⟹ unique-decodable は Mathlib に direct 補題なし (`kraft_mcmillan` は逆向き)。Stage 2 が ~80 行を超えるなら、`arithmetic_coding_unique_decodable` を「prefix-free 仮定を受け unique-decodable 結論を返す」honest brick (明示 signature pass-through) で残す。**期待長 + prefix-free 構成は full genuine、unique-decodable のみ honest pass-through** という段階的着地が現実的。

---

## 着手 skeleton

`InformationTheory/Shannon/ArithmeticCoding.lean` の genuine 版 出だし (現 file を置換):

```lean
import InformationTheory.Shannon.ShannonCode
import InformationTheory.Shannon.ShannonCodeKraftReverse
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Logic.Equiv.Defs

namespace InformationTheory.Shannon.ArithmeticCoding

open MeasureTheory
open InformationTheory.Shannon.ShannonCode (entropyD expectedLength shannonLength kraftSum)
open InformationTheory.Shannon.ShannonCodeKraftReverse (exists_prefix_code_of_kraft IsPrefixFree)

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Shannon-Fano-Elias codeword length: `l(a) = ⌈-log₂ P(a)⌉ + 1`. -/
noncomputable def sfeLength (P : Measure α) (a : α) : ℕ := shannonLength 2 P a + 1

/-- sfeLength も Kraft 不等式を充足 (各項 `2^(-(l+1)) ≤ 2^(-l)`). -/
lemma sfeLength_kraft_le_one
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a : α, 0 < P.real {a}) :
    kraftSum 2 (sfeLength P) ≤ 1 := by sorry

/-- 期待長 sandwich (full discharge): `H₂(P) ≤ E[L] ≤ H₂(P) + 2`. -/
theorem arithmeticCode_expected_length_bounds
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a : α, 0 < P.real {a}) :
    entropyD 2 P ≤ expectedLength P (sfeLength P) ∧
      expectedLength P (sfeLength P) ≤ entropyD 2 P + 2 := by sorry

/-- prefix-free 構成 (full discharge via exists_prefix_code_of_kraft + finTwoEquiv lift). -/
theorem arithmeticCode_prefix_free
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a : α, 0 < P.real {a}) :
    ∃ c : α → List Bool,
      (∀ a, (c a).length = sfeLength P a) ∧
      Function.Injective c ∧
      (∀ a b : α, a ≠ b → ¬ c a <+: c b) := by sorry

end InformationTheory.Shannon.ArithmeticCoding
```

注: `exists_prefix_code_of_kraft` の `hk` 引数は `∑ a, (D:ℝ)^(-(l a:ℤ)) ≤ 1` 形 (= `kraftSum (D:ℝ) l ≤ 1` の unfold)。`D = (2:ℕ)` で適用するため `(2:ℕ)` と `(2:ℝ)` の cast を `sfeLength_kraft_le_one` から橋渡しする。
