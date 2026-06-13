# Ch.5 Huffman cost-level 漸化式 — Mathlib API 在庫調査

> 🗄️ **ARCHIVED (Phase 完了)** — 完了済 Phase の在庫調査。in-project `file` 参照は 2026-06 split リファクタ前の旧モノリシックレイアウト (`Shannon/Huffman.lean` → 現 `Shannon/Huffman/*.lean`、`Shannon/HuffmanOptimality.lean` → `Shannon/Huffman/Optimality.lean` 等) を指す。陳腐化した旧行番号は除去済。歴史的記録として保存 (headline `huffmanLength_optimal` は sorryAx-free 完成)。

> 親計画: [`docs/shannon/huffman-strong-form-completion-plan.md`](huffman-strong-form-completion-plan.md)（判断ログ #4, 2026-05-30「cost-level merge identity への pivot」）。本ファイルは「multiset-level cost `huffmanCost s` の 1-step 漸化式を `s.card` strong induction で証明する」ために必要な Mathlib primitive の在庫。docs-only。
>
> **重要な事実 (verbatim 確認済)**: `huffmanCost` は **まだ存在しない** (`rg huffmanCost InformationTheory/ docs/` → 0 hit)。本調査は新規定義 `huffmanCost` + 漸化式補題のための在庫であり、既存コードの監査ではない。

## 一行サマリ

**cost-level 漸化式で使う Multiset 代数 API は 100% 既存 (`sum_cons` / `map_cons` / `sum_map_add` / `sum_map_erase` / `strongInductionOn` / `Finset.sum_eq_multiset_sum` 全て verbatim 確認済)。自作が必要なのは Mathlib lemma ではなく「定義そのもの」3 個 (`huffmanCost` の per-group length 関数 `len`、`huffmanCost`、漸化式補題) + 二重 erase の sum 分解 1 個 (既存 `sum_map_erase` の 2 連適用、bridge 不要)。撤退ラインは発動しない。最大の罠は category 2 の `Multiset.map_erase` が `Function.Injective f` を要求すること — ただし cost 分解は `sum_map_erase` (injective 不要) を使うので回避可能。**

---

## 主定理の最終形（再掲 + cost-level pivot の形）

cost-level pivot (親計画 判断ログ #4) の核は per-symbol depth identity を捨て、**tie-break 不変な multiset-level cost** に上げること。本調査が在庫する漸化式の想定形:

```lean
-- 想定: 各 group p = (A, pA) の「現時点での符号長」を測る関数 len : (Finset α × ℝ) → ℕ
-- (huffmanLengthAux の再帰構造を group 単位で測ったもの。定義は自作 §5)

noncomputable def huffmanCost (s : Multiset (Finset α × ℝ)) : ℝ :=
  (s.map (fun p => p.2 * (len p : ℝ))).sum     -- Σ_{group} (確率 × 符号長)

-- 1-step 漸化式 (x1 x2 = 最小 2 group, s'' = merged ::ₘ erase erase)
theorem huffmanCost_step (s) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    huffmanCost s = huffmanCost (huffmanStep s hs hg).val.2.2 + (x1.2 + x2.2) := by
  sorry
```

証明戦略 (pseudo-Lean):

```
-- s'' = (A∪B, pA+pB) ::ₘ ((s.erase x1).erase x2)
-- huffmanCost s'' = sum_cons で merged 項 + 残り項に分解
-- 残り項 ((s.erase x1).erase x2).map (·.2 * len ·) の sum を sum_map_erase 2 連で復元:
--   sum_map_erase x2 ∈ (s.erase x1)  : f x2 + (((s.erase x1).erase x2).map f).sum = ((s.erase x1).map f).sum
--   sum_map_erase x1 ∈ s             : f x1 + ((s.erase x1).map f).sum             = (s.map f).sum
-- len の漸化: x1, x2 は merged group の子なので len x1 = len x2 = len(merged) + 1
-- merged 項 (pA+pB)*(len merged) と x1,x2 項 pA*(len merged + 1), pB*(len merged + 1) の差 = pA + pB
-- → huffmanCost s = huffmanCost s'' + (x1.2 + x2.2)  ∎
```

注: `len` の漸化 (子の長さ = 親の長さ + 1) は `huffmanLengthAux_eq_step` (`InformationTheory/Shannon/Huffman.lean`) の `fun a => if a ∈ A ∨ a ∈ B then g a + 1 else g a` 構造に対応する。per-group 版 `len` を新規に定義する必要がある (§5)。

---

## API 在庫テーブル

### A. Multiset.sum / Multiset.map 代数 (漸化式の骨格)

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| cons 上の sum | `Multiset.sum_cons` | `Mathlib/Algebra/BigOperators/Group/Multiset/Defs.lean:73`（`to_additive` of `prod_cons`） | ✅ 既存 | merged 項を分離。下記 verbatim |
| cons 上の map | `Multiset.map_cons` | `Mathlib/Data/Multiset/MapFold.lean:73` | ✅ 既存 | `(merged ::ₘ rest).map f` を分解。下記 verbatim |
| map 合成 | `Multiset.map_map` | `Mathlib/Data/Multiset/MapFold.lean:155` | ✅ 既存 | `(s.map g).map f` 整理時の補助 |
| singleton の map | `Multiset.map_singleton` | `Mathlib/Data/Multiset/MapFold.lean:81` | ✅ 既存 | `initMultiset` (univ.val.map) 経由の base 計算補助 |
| zero の sum | `Multiset.sum_zero`（`to_additive` of `prod_zero`） | `Mathlib/Algebra/BigOperators/Group/Multiset/Defs.lean:69` | ✅ 既存 | base case (`s.card = 0`) |
| 加法分配 map sum | `Multiset.sum_map_add` | `Mathlib/Algebra/BigOperators/Group/Multiset/Basic.lean:113`（`to_additive` of `prod_map_mul`、使用例 228 行 `← sum_map_add`） | ✅ 既存 | cost を group ごとに加法分解する場合の補助 |

**verbatim signature (additive 源は乗法 + `@[to_additive]`)**:

- `Multiset.sum_cons` ← `prod_cons`:
  ```lean
  @[to_additive (attr := simp)]
  theorem prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
  ```
  加法形: `Multiset.sum_cons (a : M) (s) : (a ::ₘ s).sum = a + s.sum`。型クラス前提: `[AddCommMonoid M]`（源 `[CommMonoid M]` の to_additive）。我々の `M = ℝ`。

- `Multiset.map_cons`:
  ```lean
  theorem map_cons (f : α → β) (a s) : map f (a ::ₘ s) = f a ::ₘ map f s
  ```
  型クラス前提: **なし**（`{α β : Type*}` のみ）。

- `Multiset.map_map`:
  ```lean
  theorem map_map (g : β → γ) (f : α → β) (s : Multiset α) : map g (map f s) = map (g ∘ f) s
  ```
  型クラス前提: なし。

- `Multiset.sum_map_add` ← `prod_map_mul`:
  ```lean
  @[to_additive (attr := simp)]
  theorem prod_map_mul : (m.map fun i => f i * g i).prod = (m.map f).prod * (m.map g).prod
  ```
  加法形: `(m.map fun i => f i + g i).sum = (m.map f).sum + (m.map g).sum`。型クラス前提: `[AddCommMonoid M]`（源 `[CommMonoid M]`）。`m : Multiset ι`, `f g : ι → M`。

判定: **全項 ✅ 既存 / Found 0 なし / 自作要なし**。

### B. Multiset.erase 上の sum 分解 (二重 erase の核心)

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| **erase した map の sum 復元** | `Multiset.sum_map_erase` | `Mathlib/Algebra/BigOperators/Group/Multiset/Basic.lean:44`（`to_additive` of `prod_map_erase`） | ✅ 既存 | **本 Phase の主役**。二重 erase は 2 連適用 |
| erase そのものの sum 復元 | `Multiset.sum_erase`（`to_additive` of `prod_erase`） | `Mathlib/Algebra/BigOperators/Group/Multiset/Basic.lean:40` | ✅ 既存 | map なし版。`cost = s.sum` を直接持つ別 encode 時の補助 |
| cons_erase 同一視 | `Multiset.cons_erase` | `Mathlib/Data/Multiset/AddSub.lean:173` | ✅ 既存 | `a ::ₘ s.erase a = s`、再 cons 経由分解の代替ルート |
| map と erase の交換 | `Multiset.map_erase` | `Mathlib/Data/Multiset/MapFold.lean:195` | ⚠️ 既存だが **Injective 要求** | 罠。下記参照 |

**verbatim signature**:

- `Multiset.sum_map_erase` ← `prod_map_erase`:
  ```lean
  @[to_additive (attr := simp)]
  theorem prod_map_erase [DecidableEq ι] {a : ι} (h : a ∈ m) :
      f a * ((m.erase a).map f).prod = (m.map f).prod
  ```
  加法形: `Multiset.sum_map_erase [DecidableEq ι] {a : ι} (h : a ∈ m) : f a + ((m.erase a).map f).sum = (m.map f).sum`。
  型クラス前提: `[DecidableEq ι]`（要素型の DecidableEq）+ `[AddCommMonoid M]`（値型、源 `[CommMonoid M]`）。`m : Multiset ι`, `f : ι → M`, `a : ι`, `h : a ∈ m`。**`f` の injectivity は不要** — これが二重 erase 分解の正解ルート。我々の `ι = Finset α × ℝ`（`DecidableEq` あり）, `M = ℝ`。

- `Multiset.cons_erase`:
  ```lean
  theorem cons_erase {s : Multiset α} {a : α} : a ∈ s → a ::ₘ s.erase a = s
  ```
  型クラス前提: `[DecidableEq α]`（section 内）。

- `Multiset.map_erase`（**罠**）:
  ```lean
  theorem map_erase [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f) (x : α)
      (s : Multiset α) : (s.erase x).map f = (s.map f).erase (f x)
  ```
  型クラス前提: `[DecidableEq α] [DecidableEq β]` + 明示引数 `(hf : Function.Injective f)`。
  → **我々の cost 関数 `f = fun p => p.2 * (len p : ℝ)` は injective でない**（異なる group が同じ cost を持ちうる）。よって `map_erase` 経路は使えない。代わりに `sum_map_erase` (injective 不要、値レベルで直接 sum を復元) を使う。これが「sum_map_erase 2 連」戦略の根拠。

判定: **sum 分解は ✅ 既存 (`sum_map_erase`)。二重 erase 専用 lemma は不在だが `sum_map_erase` の 2 連適用で導出可能 (bridge 自作不要)。`map_erase` は injective 要求で本 Phase では使わない。**

### C. Multiset strong induction on card

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| multiset strong induction | `Multiset.strongInductionOn` | `Mathlib/Data/Multiset/Basic.lean:72` | ✅ 既存 | card 上の strong induction の標準形 |
| 展開等式 | `Multiset.strongInductionOn_eq` | `Mathlib/Data/Multiset/Basic.lean:79` | ✅ 既存 | IH の unfold |
| card 減少 | `huffmanStep_card_lt` (InformationTheory) | `InformationTheory/Shannon/Huffman.lean` | ✅ 既存 (自作済) | `s''.card < s.card`、IH 適用条件 |

**verbatim signature**:

```lean
/-- The strong induction principle for multisets. -/
@[elab_as_elim]
def strongInductionOn {p : Multiset α → Sort*} (s : Multiset α) (ih : ∀ s, (∀ t < s, p t) → p s) :
    p s
termination_by card s
decreasing_by exact card_lt_card _h
```

型クラス前提: **なし**（`{α : Type*}` のみ）。IH は `∀ t < s, p t`（multiset の `<` で減少）。

```lean
theorem strongInductionOn_eq {p : Multiset α → Sort*} (s : Multiset α) (H) :
    @strongInductionOn _ p s H = H s fun t _h => @strongInductionOn _ p t H
```

**注意 (戦略選択)**: `strongInductionOn` は multiset `<` 上の induction。`huffmanLengthAux` は既に `termination_by s.card`（`InformationTheory/Shannon/Huffman.lean`）で定義され、`huffmanLengthAux_eq_step` で展開済。よって `huffmanCost_step` の証明は **strong induction を新たに回す必要がなく、1-step 等式の直接計算で済む可能性が高い**（IH は不要、`huffmanLengthAux_eq_step` の per-group 版を len の漸化として使うだけ）。strong induction が要るのは「cost の閉形 `huffmanCost (initMultiset P) = Σ ...`」のような複数ステップ集約のときで、その場合 `s.card` を `Nat.strong_induction_on` で回すか `strongInductionOn` を使う。

判定: **✅ 既存。漸化式単発なら induction 自体不要。多ステップ集約には `strongInductionOn` / 既存 `huffmanStep_card_lt` で対応。**

### D. Finset.sum ↔ Multiset.sum bridge (`expectedLength` 接続)

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| **Finset.sum = (val.map f).sum** | `Finset.sum_eq_multiset_sum` | `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:331`（`to_additive` of `prod_eq_multiset_prod`、`rfl`） | ✅ 既存 | `expectedLength` → multiset.sum の橋。下記 verbatim |
| val.map.sum = Finset.sum | `Finset.sum_map_val` | `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:336`（`to_additive` of `prod_map_val`、`rfl`） | ✅ 既存 | 上記の逆向き |
| Multiset から Finset.sum へ | `Finset.sum_multiset_map_count` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | ✅ 既存 | count 経由（nodup 不要だが重い、不使用見込み） |

**verbatim signature**:

- `Finset.sum_eq_multiset_sum` ← `prod_eq_multiset_prod`:
  ```lean
  @[to_additive]
  theorem prod_eq_multiset_prod [CommMonoid M] (s : Finset ι) (f : ι → M) :
      ∏ x ∈ s, f x = (s.1.map f).prod := rfl
  ```
  加法形: `Finset.sum_eq_multiset_sum [AddCommMonoid M] (s : Finset ι) (f : ι → M) : ∑ x ∈ s, f x = (s.1.map f).sum`。型クラス前提: `[AddCommMonoid M]`（源 `[CommMonoid M]`）。**`rfl` なので defeq**。

- `Finset.sum_map_val` ← `prod_map_val`:
  ```lean
  @[to_additive (attr := simp)]
  lemma prod_map_val [CommMonoid M] (s : Finset ι) (f : ι → M) : (s.1.map f).prod = ∏ a ∈ s, f a := rfl
  ```
  加法形: `Finset.sum_map_val [AddCommMonoid M] (s : Finset ι) (f : ι → M) : (s.1.map f).sum = ∑ a ∈ s, f a`。`rfl`。

**接続の形 (verbatim 確認済の橋)**: `expectedLength P l = ∑ a : α, P.real {a} * (l a : ℝ)`（`InformationTheory/Shannon/ShannonCode.lean`）。`initMultiset P = (Finset.univ).val.map (fun a => ({a}, P.real {a}))`（`InformationTheory/Shannon/Huffman.lean`）。よって:

```
expectedLength P l
  = ∑ a : α, P.real {a} * (l a : ℝ)                        -- def
  = (univ.val.map (fun a => P.real {a} * (l a : ℝ))).sum   -- Finset.sum_eq_multiset_sum (rfl)
  = ((initMultiset P).map (fun p => p.2 * (len' p))).sum    -- map_map + len 整合 (len' on singleton = l)
  = huffmanCost (initMultiset P)                            -- def of huffmanCost
```

中間の「`univ.val.map g` → `(univ.val.map h).map k`」整理は `Multiset.map_map` (§A)。`len' ({a}, _)` が singleton group で `l a = huffmanLength P a` に一致することは `len` の定義整合で確保する（§5 自作）。

判定: **✅ 既存 (`sum_eq_multiset_sum` が `rfl` bridge)。`expectedLength = huffmanCost (initMultiset P)` の補題は §A,D の組合せで自作するが、Mathlib lemma は揃っている。**

### E. ℝ 上の有限和 (順序不要、可換群 sum で十分)

| 概念 | Mathlib API | 状態 | 扱い |
|---|---|---|---|
| ℝ は `AddCommMonoid` / `CommRing` | instance（Mathlib core） | ✅ 既存 | §A,B,D の全 `[AddCommMonoid M]` 前提を充足。順序 / `Nodup` 不要 |

判定: cost が ℝ 値なので、§A〜D の lemma は全て `[AddCommMonoid ℝ]` で発火。**順序・`Nodup`-aware な特殊 sum lemma は不要**。`HuffmanGrouping s` の `Nodup` は `erase` の振る舞い（`card_erase_of_mem` 等）に効くが、`sum_map_erase` 自体は nodup 非依存（`a ∈ m` だけ要求）。

---

## 主要前提条件ボックス（事故が起きやすい lemma）

- **`Multiset.sum_map_erase`** (category B 主役):
  - `[DecidableEq ι]` — 要素型 `Finset α × ℝ` の DecidableEq（`α` が `DecidableEq` を持てば自動、Huffman の variable に既存）。
  - `[AddCommMonoid M]` — 値型 `ℝ`、自動。
  - `(h : a ∈ m)` — **membership 仮説が必須**。二重 erase の 1 段目は `x2 ∈ s.erase x1`（`huffmanStep_spec` の `.val.2.1 ∈ s.erase .val.1` が供給、`InformationTheory/Shannon/Huffman.lean`）、2 段目は `x1 ∈ s`（同 spec `.val.1 ∈ s`, line 272）。membership は既存 spec から取れる。
  - `f` の injectivity は **不要**（`map_erase` と違い値レベル）。

- **`Multiset.map_erase`** (使わないが罠として明記):
  - `(hf : Function.Injective f)` を明示引数で要求。cost 関数は非 injective なので **この lemma は本 Phase で使用禁止**。

- **`Finset.sum_eq_multiset_sum`** (category D 橋):
  - `[AddCommMonoid M]` のみ。`rfl` なので `unfold` / `show` で透過。`initMultiset` の `univ.val.map` 形と直接 defeq でつながる。

- **`Multiset.strongInductionOn`** (category C):
  - 型クラス前提なし。IH は **multiset `<`**（`t < s`）であって `card` ではない。card で回したいなら `decreasing_by` 由来の `Multiset.card_lt_card` か既存 `huffmanStep_card_lt` で `s'' < s` を `s''.card < s.card` から導く（`Multiset.lt_iff_cons_le` / `card_lt_card` 経由）。**漸化式単発なら induction 不要**。

---

## 自作が必要な要素（優先度順）

Mathlib lemma の不足はゼロ。自作対象は全て **InformationTheory 側の定義 / 補題**。

1. **per-group length 関数 `len : (Finset α × ℝ) → ℕ`**（最優先、定義設計）
   - 推奨: `huffmanLengthAux` の per-symbol 構造を group 単位に持ち上げる。group `(A, pA)` の符号長は「A に属する任意 symbol の `huffmanLengthAux` 値」（HuffmanGrouping の disjoint + const-on-group 性で well-defined）。あるいは `huffmanStep` の再帰に沿って group 自身に length を焼き込む `huffmanCostAux` を新規再帰定義する（`termination_by s.card`、`huffmanLengthAux` と同型）。
   - **罠**: `len` を「A の代表 symbol の length」で定義すると、代表選択の well-defined 性（const-on-group）の補題が要る。`huffmanCostAux` として group に length を直接持たせる方が漸化式の `len x1 = len x2 = len(merged)+1` が定義的に取れて軽い。→ **Mathlib-shape-driven の原則**: 漸化式の結論形（`sum_cons` + `sum_map_erase` で割れる形）に合うよう、`huffmanCost` を最初から `(s.map (fun p => p.2 * len p)).sum` 形で定義し、`len` を再帰の中で `+1` する形にする。
   - 工数感: 定義 + well-defined 補題で 30〜60 行。

2. **`huffmanCost s := (s.map (fun p => p.2 * (len p : ℝ))).sum`**（定義、§1 に従属）
   - 工数感: 1 行。`len` 確定後に書く。

3. **`huffmanCost_step` 漸化式補題**（本 Phase の主結果）
   - 戦略: §冒頭 pseudo-Lean。`sum_cons` で merged 項分離 → `sum_map_erase` 2 連で `(s.erase x1).erase x2` の cost を復元 → `len` 漸化（`len x1 = len x2 = len merged + 1`）で算術整理。
   - 工数感: 40〜80 行（`len` 漸化補題込み）。最も重いのは `len x1 = len merged + 1` の証明で、`huffmanLengthAux_eq_step` の `if a ∈ A ∨ a ∈ B then g a + 1` 構造を group 版に翻訳する部分。
   - **罠**: 二重 erase の membership 順序（`x2 ∈ s.erase x1` を先に、`x1 ∈ s` を後に剥がす）。`sum_map_erase` を逆順適用すると `f x1` と `f x2` が混ざる。

4. **`expectedLength P l = huffmanCost (initMultiset P)` bridge 補題**（接続、§D）
   - 戦略: `Finset.sum_eq_multiset_sum`（rfl）+ `map_map` + `len` の singleton 整合。
   - 工数感: 15〜30 行。

判定: **Mathlib lemma 自作要 = 0 件。InformationTheory 定義/補題 自作要 = 4 件（うち定義 2、補題 2）**。二重 erase の sum 分解は専用 lemma を Mathlib に求めず `sum_map_erase` 2 連で導出（bridge 自作不要）。

---

## Mathlib 壁の列挙（真に不在のもの）

`@residual(wall:...)` 対象となる「Mathlib に存在しない primitive」は **ゼロ**。

- 二重 erase の sum 分解専用 lemma（例 `Multiset.sum_map_erase_erase`）: loogle `Multiset.sum_map_erase` は 1 件（単発版）のみ。二重版は不在だが、これは **wall ではなく単に「既存 lemma の 2 連適用で導出可能」**（hard でも blocked でもない、自明な合成）。共有 sorry 補題化は不要。
- per-group length / cost 概念: Mathlib に Huffman は無いので当然不在だが、これは family 固有の定義であって Mathlib 壁ではない。

→ **本 Phase に `@residual(wall:<name>)` 対象は無い。shared sorry 補題化候補も無い。** 全て type-check done → proof done まで genuine に到達可能な見込み（Mathlib 不在による sorry 残置は発生しない）。

---

## 撤退ラインへの距離

親計画 `huffman-strong-form-completion-plan.md` の撤退ライン（§撤退ライン, 312行〜）:

- 「H2-b 破綻（sort 順 cross-type 対応が取れない）→ C3 へ」「H1-a 破綻（shorten-to-Kraft=1）→ H2 先行 publish」: いずれも **per-symbol / swap-normalization 経路**の撤退ラインであり、本 cost-level pivot はこれら **の代替経路**（判断ログ #4 で per-symbol identity を dead と確定した後の新方針）。よって既存撤退ラインの「発動」とは無関係。

判定: **既存撤退ラインには触れない（発動 = no）**。cost-level pivot は撤退ライン #4 の結果として生まれた新経路で、その内部に新たな撤退リスクを持つ。

**新規撤退ライン候補**（cost-level pivot 固有、親計画への追記推奨）:

- **`len` の per-group well-defined / 漸化（`len x1 = len merged + 1`）が `huffmanLengthAux` 構造から取れない**場合
  → `huffmanCost` を per-symbol 経由（`Σ_{a∈A} P{a} * huffmanLengthAux a` を group cost とする）に再定義し、`huffmanStep` の symbol 集合不変性を経由して漸化を取る縮退案。
  → これでも cost は tie-break 不変（判断ログ #4 の pivot 動機）なので数学的中身は保たれる。
  → 撤退口は `huffmanCost_step` body の `sorry` + `@residual(plan:huffman-cost-recurrence)`（仮説束化は禁止）。

---

## 着手 skeleton

`InformationTheory/Shannon/HuffmanCost.lean`（新規）の出だし:

```lean
import InformationTheory.Shannon.Huffman          -- huffmanStep / huffmanLengthAux / initMultiset / HuffmanGrouping
import InformationTheory.Shannon.ShannonCode       -- expectedLength
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic   -- sum_map_erase / sum_map_add
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs     -- sum_cons / sum_zero
import Mathlib.Data.Multiset.MapFold                        -- map_cons / map_map
import Mathlib.Data.Multiset.Basic                          -- strongInductionOn

namespace InformationTheory.Shannon.Huffman

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- per-group 符号長 (huffmanLengthAux の group 版、再帰で +1)。要設計 (§5-1)。 -/
noncomputable def len (s : Multiset (Finset α × ℝ)) (p : Finset α × ℝ) : ℕ := sorry
  -- @residual(plan:huffman-cost-recurrence) — len は def なので分割設計、§5-1 参照

/-- multiset-level cost: Σ_{group} (確率 × 符号長)。 -/
noncomputable def huffmanCost (s : Multiset (Finset α × ℝ)) : ℝ :=
  (s.map (fun p => p.2 * (len s p : ℝ))).sum

/-- 1-step 漸化式 (cost-level merge identity, tie-break 不変)。 -/
theorem huffmanCost_step (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card)
    (hg : HuffmanGrouping s) :
    huffmanCost s =
      huffmanCost (huffmanStep s hs hg).val.2.2
        + ((huffmanStep s hs hg).val.1.2 + (huffmanStep s hs hg).val.2.1.2) := by
  sorry  -- @residual(plan:huffman-cost-recurrence)

/-- expectedLength との接続 (§D)。 -/
theorem expectedLength_eq_huffmanCost (P : MeasureTheory.Measure α) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      = huffmanCost (initMultiset P) := by
  sorry  -- @residual(plan:huffman-cost-recurrence)

end InformationTheory.Shannon.Huffman
```

> 注: `len` は `def` なので body に直接 `sorry` を書けない（CLAUDE.md「sorry を書けない箇所」）。実装時は §5-1 の通り `huffmanCostAux` 再帰定義（length を group に焼き込む）に書き換え、定義そのものは genuine に閉じる想定。上記 skeleton の `len := sorry` は設計確定までの暫定で、実装着手時に第一選択（定義書換）で解消する。

---

## まとめ

- インベントリ: **`docs/shannon/huffman-cost-recurrence-inventory.md`**（このファイル）
- **既存率 100%**（Multiset 代数 / strong induction / Finset↔Multiset bridge の Mathlib lemma は全て verbatim 確認済で存在）
- **自作必要 4 件**（Mathlib lemma ではなく InformationTheory 定義/補題: `len`/`huffmanCost`/`huffmanCost_step`/`expectedLength_eq_huffmanCost`）
- **Mathlib 壁 0 件**（`@residual(wall:...)` 対象なし、二重 erase 分解も `sum_map_erase` 2 連で導出）
- **撤退ライン発動 = no**（cost-level pivot は判断ログ #4 の新経路、既存撤退ラインに非接触）
- 最大の罠: `Multiset.map_erase` が `Function.Injective f` を要求するため cost 分解に使えない → `sum_map_erase`（injective 不要）に統一
