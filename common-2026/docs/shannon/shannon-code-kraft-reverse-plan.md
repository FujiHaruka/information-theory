# Shannon コード Kraft 逆向き (B-8') ムーンショット計画 🌙

> Status (2026-05-12): **完了 ✅**。`Common2026/Shannon/ShannonCodeKraftReverse.lean` (498 行、0 sorry / 0 error / 0 warning)。B-8 期待長 sandwich (`docs/shannon/shannon-code-moonshot-plan.md`) と並立 publish。

## 進捗

- [x] Phase 0 — Mathlib API インベントリ (List.IsPrefix / Nat.mod_pow_succ / List.mergeSort) ✅
- [x] Phase A — D-進数エンコーダ `toBaseDLen` と prefix-free 述語の定義 ✅
- [x] Phase B — 補助補題 `toBaseDLen_take` / `toBaseDLen_eq_of_isPrefix` / `toBaseDLen_injOn_lt` ✅
- [x] Phase C — Greedy 構成 (`List.mergeSort` + 累積和 `slotStart`) と Kraft 充足 → `slotStart` 上界 ✅
- [x] Phase D — Prefix-free 性 (`shannonFanoCode_prefixFree`) と Injectivity (`shannonFanoCode_injective`) ✅
- [x] Phase E — 主定理 `exists_prefix_code_of_kraft` ✅

## 実装結果サマリ

- **ファイル**: `Common2026/Shannon/ShannonCodeKraftReverse.lean` (498 行)
- **採用構成**: **D-進数 (Shannon-Fano) 構成** — sort-by-length → 累積和 `slotStart` → `toBaseDLen` で base-`D` 表現。Greedy with set-of-used-prefixes は不採用 (state 管理が重い)。
- **新規定義**:
  - `toBaseDLen (D : ℕ) [NeZero D] (L n : ℕ) : List (Fin D)` — MSB-first 固定長 base-`D` 表現 (`List.ofFn` ベース)
  - `IsPrefixFree {D : ℕ} (c : α → List (Fin D)) : Prop` — prefix-free 述語
  - `sortedByLen (l : α → ℕ) : List α` — `List.mergeSort` で `l` 昇順
  - `slotStart (D : ℕ) (l : α → ℕ) (L : ℕ) (k : ℕ) : ℕ` — `take k` 累積和
  - `sortedIndex (l : α → ℕ) (a : α) : ℕ` — `List.idxOf` 経由の位置
  - `shannonFanoCode {D} [NeZero D] (l : α → ℕ) (L : ℕ) (a : α) : List (Fin D)` — 主 code
  - `commonDepth (l : α → ℕ) : ℕ` — `Finset.univ.sup l`
- **主補題**:
  - `toBaseDLen_take`: `(toBaseDLen D L₂ n).take L₁ = toBaseDLen D L₁ (n / D^(L₂-L₁))` (`L₁ ≤ L₂`)
  - `toBaseDLen_eq_of_isPrefix`: `toBaseDLen D L₁ n₁ <+: toBaseDLen D L₂ n₂ ⟹ ... = toBaseDLen D L₁ (n₂ / D^(L₂-L₁))`
  - `toBaseDLen_injOn_lt`: `n₁, n₂ < D^L` + `toBaseDLen` 等しい ⟹ `n₁ = n₂` (digit-by-digit 帰納)
  - `slotStart_succ` / `slotStart_mono` / `slotStart_card_eq_sum`
  - `kraft_sum_nat_le_of_real`: Kraft 充足 (ℝ) ⟹ `Σ D^(L-l) ≤ D^L` (ℕ)
  - `slotStart_le_pow` / `slotStart_lt_pow_of_lt` (後者は strict、`l a ≤ L` 経由)
  - `slotStart_gap`: `j < k` ⟹ `slot j + D^(L-l(as[j])) ≤ slot k`
  - `not_isPrefix_of_sortedIndex_lt`: 補助 lemma で prefix-free 性の forward case を孤立
- **主定理**:
  ```
  theorem exists_prefix_code_of_kraft
      {D : ℕ} (hD : 2 ≤ D) (l : α → ℕ) (hl : ∀ a, 0 < l a)
      (hk : ∑ a : α, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
      ∃ c : α → List (Fin D),
        Function.Injective c ∧ (∀ a, (c a).length = l a) ∧ IsPrefixFree c
  ```
- **検証**: `lake env lean Common2026/Shannon/ShannonCodeKraftReverse.lean` clean — **0 sorry / 0 error / 0 warning**.
- **既存 B-8** (`Common2026/Shannon/ShannonCode.lean` 354 行) は **完全に並立** (touch せず)。
- **Mathlib に prefix code 構造体は無い** (`UniquelyDecodable` + `kraft_mcmillan_inequality` のみ)、B-8' は独立 implementation。
- **Mathlib 上流 PR 切り出し候補**: `toBaseDLen` と核補題 (`toBaseDLen_take` / `toBaseDLen_injOn_lt`) は coding/prefix code に閉じない一般 utility なので、`Mathlib.Data.Nat.Digits` 拡張または `Mathlib.InformationTheory.Coding.PrefixCode` (新規 file) として切り出し可能。

## 妥協 / 設計決定

1. **`hl : ∀ a, 0 < l a` は API 整合のために残す** が、proof 内では使わない (Kraft `≤ 1` 仮定から `|α| ≥ 2` のとき `l a = 0` は不可能、`|α| = 1` のときは prefix-free が trivial)。
2. **`D : ℕ` 形** (`(D : ℝ)` cast で Kraft を入力)、実数 `D` への一般化は不要。
3. **prefix code を構造体化せず述語形** (`Function.Injective` + `IsPrefixFree`) で完結。構造体化と Mathlib `UniquelyDecodable` への bridge は **B-8'' (deferred)** 候補。

## ゴール / Approach

**最終到達点**: 任意の正整数列 `l : α → ℕ` (有限アルファベット `α`, `[Fintype α]`) が
**Kraft 不等式** `Σ_a D^{-l(a)} ≤ 1` を充足するとき、長さ `l(a)` の **prefix code** が存在する:

```
theorem exists_prefix_code_of_kraft
    (l : α → ℕ) (hl : ∀ a, 0 < l a)
    (hD : 2 ≤ D)
    (hk : ∑ a, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    ∃ c : α → List (Fin D),
      Function.Injective c ∧
      (∀ a, (c a).length = l a) ∧
      (∀ a b, a ≠ b → ¬ c a <+: c b)
```

(Cover-Thomas 5.2.1 reverse direction; McMillan の逆形。)

### Approach の中核 (4 段)

1. **(エンコーダ) `toBaseDLen D L n`**: 自然数 `n` を base-`D` で表現した most-significant-first
   長さ `L` の `List (Fin D)`。`n < D^L` のとき意味のある digit 列、それ以外でも 0-padded
   ないし truncated だが本シードでは `n < D^L` のレジームのみ使う。
2. **(IsPrefix 特徴づけ)** `toBaseDLen D l₁ n₁ <+: toBaseDLen D l₂ n₂ ↔ n₁ = n₂ / D^(l₂ - l₁)`
   (`l₁ ≤ l₂` のとき) — これだけで prefix-free 性を arithmetic 条件に還元できる。
3. **(Greedy 構成)** `α` を「`l a` の昇順」(同点は任意 tiebreak) に sort し、累積和
   `slotStart k := Σ_{j < k} D^(L - l (as[j]))` を取り、`code (as[k]) := toBaseDLen D (l (as[k])) (slotStart k / D^(L - l (as[k])))`
   を定義。**Kraft 仮定で `slotStart |α| ≤ D^L`**、各 `slotStart k` も `< D^L` を保証。
4. **(Prefix-free 検証)** `j < k` で `slotStart k - slotStart j ≥ D^(L - l(as[j]))` から
   `(slotStart k) / D^(L - l(as[j])) ≠ (slotStart j) / D^(L - l(as[j]))` を導き、
   IsPrefix 特徴づけで prefix-free が出る。

### Mathlib-shape 駆動の定義設計

- **`List.IsPrefix`** (Init.Data.List.Sublist) の主要補題:
  - `List.prefix_or_prefix_of_prefix`: 共通の親への 2 prefix は片方が他方の prefix
  - `List.IsPrefix.length_le`: prefix ⇒ 長さ ≤
  - `List.IsPrefix.eq_of_length_le`: prefix + length ≤ ⇒ 等しい
  - `List.prefix_iff_eq_take`: `l₁ <+: l₂ ↔ l₁ = l₂.take l₁.length`
- **`Nat.digits` は LSB-first で長さ可変** なので **使わない**。独自実装 `toBaseDLen` を採用 (MSB-first、固定長、`(Fin D)` valued)。
- **`Finset.sort`** で sort-by-length。`Finset.sort_sorted` / `Finset.sort_nodup` で操作。
- **既存 `kraftSum`** (`Common2026/Shannon/ShannonCode.lean`) を入力形に採用:
  `kraftSum D l := Σ a, (D : ℝ) ^ (-(l a : ℤ))`。

### 撤退ライン / 妥協

- **`D : ℕ` 形に絞る** (`2 ≤ D`)。実数 `D ≥ 2` への一般化は不要 (alphabet は離散)。
- **`hl : ∀ a, 0 < l a` 強仮定**: 長さ 0 の code-word (空 list) は他のすべての prefix なので prefix-free 排除のため。
- **D-ary tree 構造体は導入しない**: 述語形 (`α → List (Fin D)`、injective、prefix-free) で完結。
  構造体への bridge は B-8'' (deferred) に切り出し、Mathlib 上流 PR との整合 (`InformationTheory.PrefixCode` proposal) も将来。

### ファイル構成

```
Common2026/Shannon/
  ShannonCodeKraftReverse.lean   ← 新規 (B-8' main)
  ShannonCode.lean               ← 既存 354 行、touch しない
```

`Common2026.lean` 末尾に `import Common2026.Shannon.ShannonCodeKraftReverse` 追加。

## Phase 0 — Mathlib API インベントリ 📋

### `List.IsPrefix` 系 (Init.Data.List.Sublist)

| Lemma | Signature | 用途 |
|---|---|---|
| `List.IsPrefix.length_le` | `l₁ <+: l₂ → l₁.length ≤ l₂.length` | prefix ⇒ 長さ比較 |
| `List.IsPrefix.eq_of_length_le` | `l₁ <+: l₂ → l₂.length ≤ l₁.length → l₁ = l₂` | 同長 prefix ⇒ 等しい |
| `List.prefix_or_prefix_of_prefix` | `l₁ <+: l₃ → l₂ <+: l₃ → l₁ <+: l₂ ∨ l₂ <+: l₁` | (使わない: 我々は直接構成) |
| `List.prefix_iff_eq_take` | `l₁ <+: l₂ ↔ l₁ = l₂.take l₁.length` | prefix の characterization |
| `List.prefix_append` | `l₁ <+: l₁ ++ l₂` | append form |
| `List.cons_prefix_iff` | `a :: l₁ <+: l₂ ↔ ∃ l₂', l₂ = a :: l₂' ∧ l₁ <+: l₂'` | inductive case |
| `List.prefix_append_right_inj` | `l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂` | 共通 prefix の cancel |

### `Nat` digit 系

- **`Nat.digits` (Mathlib.Data.Nat.Digits.Defs)** は LSB-first / 可変長で本シード不向き。独自 `toBaseDLen` を実装。
- **`Nat.div_lt_iff`** / **`Nat.lt_div_iff`** などの算術補題は標準。

### `Finset.sort` 系 (Mathlib.Data.Finset.Sort)

| Lemma | Signature | 用途 |
|---|---|---|
| `Finset.sort` | `(r : α → α → Prop) [DecidableRel r] [IsTrans r] [IsAntisymm r] [IsTotal r] : Finset α → List α` | sort by relation |
| `Finset.sort_perm_toList` | `Finset.sort r s ~ s.toList` | perm to underlying |
| `Finset.sort_nodup` | `(Finset.sort r s).Nodup` | nodup 保存 |
| `Finset.sort_sorted` | `(Finset.sort r s).Sorted r` | sorted 性 |
| `Finset.length_sort` | `(Finset.sort r s).length = s.card` | 長さ |

我々は `α` を全体 `Finset.univ` に sort して `List α` を得る。Order: `r a b := l a ≤ l b ∨ (l a = l b ∧ a < b)` のような lex order (or simpler: `l a ≤ l b` で sort, ties は任意)。`Fintype.toList` + `List.mergeSort` も同等。

### 既存 `kraftSum`

```
noncomputable def kraftSum (D : ℝ) (l : α → ℕ) : ℝ :=
  ∑ a : α, (D : ℝ) ^ (-(l a : ℤ))
```

→ 本シード入力形: `(hk : kraftSum D l ≤ 1)` と書ける。`D : ℕ` を `(D : ℝ)` に cast して仮定。

## Phase A — 定義 📋

### `toBaseDLen`

```lean
/-- MSB-first base-D digit expansion of length L of n.
    For n < D^L, this returns the canonical digit list. -/
def toBaseDLen (D L n : ℕ) : List (Fin (max D 1))
```

`D ≥ 1` (要 `2 ≤ D` から保証) は instance で扱う。実装は再帰:

```lean
def toBaseDLen (D : ℕ) : (L : ℕ) → (n : ℕ) → List (Fin (max D 1))
  | 0, _ => []
  | L+1, n => ⟨n / D^L % (max D 1), Nat.mod_lt _ (by ...)⟩ :: toBaseDLen D L n
```

(MSB-first: 最も意味のある桁から)

簡素化: 内部では `D ≥ 1` の前提があるので `Fin D` のままで書く。空ケースのみ別扱いなら可能。本実装では **`(2 ≤ D)` 仮定下で `Fin D` codomain** にする。

### `IsPrefixFree`

```lean
def IsPrefixFree {D : ℕ} (c : α → List (Fin D)) : Prop :=
  ∀ a b : α, a ≠ b → ¬ c a <+: c b
```

### 公開主定理形

```lean
theorem exists_prefix_code_of_kraft
    {D : ℕ} (hD : 2 ≤ D)
    (l : α → ℕ) (hl : ∀ a, 0 < l a)
    (hk : ∑ a, ((D : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    ∃ c : α → List (Fin D),
      Function.Injective c ∧
      (∀ a, (c a).length = l a) ∧
      (∀ a b : α, a ≠ b → ¬ c a <+: c b)
```

## Phase B — `toBaseDLen` 補助補題 📋

- `toBaseDLen_length`: `(toBaseDLen D L n).length = L`
- `toBaseDLen_take`: `(toBaseDLen D (L₁ + L₂) n).take L₁ = toBaseDLen D L₁ (n / D^L₂)` (MSB-first 規約から)
- `toBaseDLen_isPrefix_iff`: `toBaseDLen D l₁ n₁ <+: toBaseDLen D l₂ n₂ ↔ (l₁ ≤ l₂ ∧ n₁ = n₂ / D^(l₂ - l₁))` (`n_i < D^l_i` 前提下)
- `toBaseDLen_injective_lt_pow`: `n < D^L`, `n' < D^L`, `toBaseDLen D L n = toBaseDLen D L n' → n = n'`

## Phase C — Greedy 構成 (`slotStart` + Kraft 上界) 📋

```lean
-- as : List α, sorted by l, all of Finset.univ
-- L : 共通の depth (= Finset.univ.sup' l + 1, or just any sup)
-- slotStart k : ℕ = Σ_{j < k} D^(L - l (as[j]))
-- code a := let k := as.indexOf a; toBaseDLen D (l a) (slotStart k / D^(L - l a))
```

Kraft `Σ_a D^{-l(a)} ≤ 1` ⟹ `Σ_a D^(L - l(a)) ≤ D^L`、よって任意の `k` で `slotStart k ≤ D^L`。
さらに各 `k` で `slotStart k / D^(L - l (as[k])) < D^(l (as[k]))` (`slotStart k + D^(L - l(as[k])) ≤ D^L` から).

## Phase D — Prefix-free + Injective 検証 📋

- 異なる `a, b ∈ α` に対応する indices `j ≠ k` (WLOG `j < k`)。
- `slotStart k ≥ slotStart j + D^(L - l(as[j]))` (累積和の単調増加 + 該当項).
- 上の不等式と sort 順 `l(as[j]) ≤ l(as[k])` から `slotStart k / D^(L - l(as[j])) > slotStart j / D^(L - l(as[j]))`、
  特に **等しくない** → IsPrefix 特徴づけ (Phase B) で `c (as[j])` が `c (as[k])` の prefix でない。
- 対称形 (`c (as[k])` が `c (as[j])` の prefix でない) は長さ比較 (`l(as[j]) ≤ l(as[k])`、等号は別途)。
- Injectivity は prefix-free + (`c a = c b ↔ c a <+: c b ∧ c b <+: c a`) で。

## Phase E — 主定理組み立て 📋

`exists_prefix_code_of_kraft` を Phase A-D を組み合わせて `⟨code, injectivity, length, prefix_free⟩` で提示。

## 見積行数 / 検証

- 目標行数: **500-700 行** (`toBaseDLen` + 6-8 補題 + greedy 構成 + 主定理)。
- 検証: `lake env lean Common2026/Shannon/ShannonCodeKraftReverse.lean` clean、0 sorry。

## 判断ログ

1. **`Nat.digits` (Mathlib) は不採用**: LSB-first / 可変長で `IsPrefix` との接続が悪く、独自 `toBaseDLen` を MSB-first / 固定長で実装する方が補題数が少ない。
2. **D-進数構成 vs Greedy 構成**: D-進数 (累積和 `slotStart`) を採用。Greedy with set-of-used-prefixes は state 管理が重く、累積和の方が「Kraft 条件 → 上界保証」が直接に書ける。
3. **`hl : ∀ a, 0 < l a` 採用**: 長さ 0 の code-word (空 list) は trivially prefix of anything、prefix-free が壊れる。Cover-Thomas でも前提 (実用的には自然)。
4. **`D : ℕ` 形** (cast で `D : ℝ` の Kraft 条件と接続): 実数 `D` への一般化は不要。
