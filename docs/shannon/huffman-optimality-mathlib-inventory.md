# T1-A' Huffman 最適性 (sibling property + n→n-1 induction) — Mathlib 在庫追補調査

> 🗄️ **ARCHIVED (Phase 完了)** — 完了済 Phase の在庫調査。in-project `file` 参照は 2026-06 split リファクタ前の旧モノリシックレイアウト (`Shannon/Huffman.lean` → 現 `Shannon/Huffman/*.lean`、`Shannon/HuffmanOptimality.lean` → `Shannon/Huffman/Optimality.lean` 等) を指す。陳腐化した旧行番号は除去済。歴史的記録として保存 (headline `huffmanLength_optimal` は sorryAx-free 完成)。

> Parent roadmap: `docs/textbook-roadmap.md` §Tier 1 — **T1-A'. Huffman 最適性 (sibling property + 任意 `l` 比較)**
> 先行: `docs/shannon/huffman-mathlib-inventory.md` (T1-A 時点)、`docs/shannon/huffman-moonshot-plan.md` (T1-A 完了 plan)
> 既存実装: `InformationTheory/Shannon/Huffman.lean` (953 行 / 0 sorry / Phase 3 完遂 publish)
> 出力規約: T1-A inventory と同形。**T1-A inventory 既載 API は再掲しない** (§A 既存 ShannonCode + 既存 Mathlib `Finset.exists_min_image` / `Multiset.exists_min_image` / `Multiset.strongInductionOn` / `Multiset.sort` / `Finset.min'` / `Finset.induction` / `Finset.card_erase_of_mem` / `Finset.card_lt_card` / `Finset.sum_le_sum` / `Finset.sum_lt_sum` / `Finset.sum_insert` / `kraft_mcmillan_inequality` / `exists_prefix_code_of_kraft` 等)。本書はそれら**を所与とした上で、`exists_sibling_min_pair` + `huffmanLength_optimal` を実装する際の追加 API のみを網羅**する。

---

## 一行サマリ

**T1-A' で新規に必要な Mathlib API のうち 90% 以上が既存** (`Equiv.swap` + `Function.update` + `Finset.sum_erase_add` / `Finset.mul_prod_erase` / `Finset.sum_pair` + `Finset.image_erase` + `Nat.strong_induction_on` + `Finset.sum_sumElim` + `Finset.equivOfCardEq` の組み合わせで sibling 性質 + n→n-1 induction を回せる)。**真の不足は 2 件**:

1. **「Huffman 木の最深 leaf」を InformationTheory 既存 `huffmanLength : Measure α → α → ℕ` の Sup として表現する API** — Mathlib にも InformationTheory にも無し。自前構築 `Finset.exists_max_image (Finset.univ : Finset α) (huffmanLength P)` でカバー可、~15 行。
2. **「merged distribution `P'` on `α' := α / {a~b}`」の Lean 表現** — Mathlib に直接対応する quotient-based "merge measure" は無し (`Setoid` / `Quotient` / `Sum.elim` / `Function.update` の組み合わせで自前)。**ここが T1-A' の最大の設計判断ポイント** (§F-2 参照)。

**最大の発見 (危険度高)**: T1-A 既存 `huffmanLength : Measure α → α → ℕ` は **`Measure α` を直接受ける** signature で publish 済み。一方 Cover-Thomas の n→n-1 induction は「merged `P'` 上の Huffman」を IH で呼ぶ必要があるが、**`P'` を `Measure α'` として構成する**には `MeasurableSpace`/`MeasurableSingletonClass` 等の type-class が `α'` 上で必要になり、特に **merged type `α'` が quotient (`Quotient (s : Setoid α)`) の場合 `MeasurableSingletonClass` の継承が自明でない**。**T1-A inventory §F-3 の「`pmf : α → ℝ` 路線 vs `Measure α` 路線」が T1-A' で再燃**する。§F-3 (T1-A' 版) で詳述。

**撤退ライン**: T1-A' は roadmap 規模 ~400-500 行で見積もられているが、§F-2 の merged 型表現が「`α' := { x : α // x ≠ b }` (= `Finset.univ.erase b`-Subtype) + `b` を `a` に再map する `Function.update`」で取れれば `Quotient` を回避でき、Mathlib `MeasurableSingletonClass` の継承 (`Subtype.instMeasurableSpace` + `Subtype.measurableSingletonClass`) で type-class 地獄を回避可能 — **撤退ライン非発動見込み**。`Quotient` 路線を採ると `MeasurableSingletonClass` の自前付与 ~50 行追加で撤退ライン §G-2 発動リスク。

---

## 主定理の最終形 (T1-A' で publish 予定)

```lean
namespace InformationTheory.Shannon.Huffman

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Sibling property (Cover-Thomas Lemma 5.8.1)** — intermediate lemma. -/
theorem exists_sibling_min_pair
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    ∃ a b : α, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, huffmanLength P c ≤ huffmanLength P a) ∧
      (∀ c, P.real {a} ≤ P.real {c} ∨ P.real {b} ≤ P.real {c}) := sorry

/-- **主定理 (Cover-Thomas Theorem 5.8.1)** — 任意 Kraft-feasible `l` との比較形. -/
theorem huffmanLength_optimal
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l := sorry

end InformationTheory.Shannon.Huffman
```

証明戦略 (pseudo-Lean、`Fintype.card α = n` 上の strong induction、6-8 行):

```lean
-- induction on n := Fintype.card α
-- base n = 1: huffmanLength = 0 (定義より, `huffmanLengthAux_eq_zero` で `s.card = 1` ⇒ `fun _ => 0`).
--            ∑ a, P.real {a} * 0 = 0 ≤ RHS (hl_pos ⇒ ∀ a, P.real {a} * l a ≥ 0).
-- step n ≥ 2:
--   sibling step 1: exists_sibling_min_pair で (a, b) を取得 (a ≠ b, l_H a = l_H b, deepest, min 2).
--   sibling step 2: 任意の Kraft-feasible l も「最小 2 確率 element に等深兄弟を割り当てる形」に
--                   swap で正規化 (Cover-Thomas Lemma 5.8.1 (i)/(ii)) — `Equiv.swap` で l → l_swap.
--   merge:  α' := { x : α // x ≠ b } (Subtype, Fintype.card = n - 1)、
--           P' : Measure α'、l' : α' → ℕ ((l a) - 1 if x = ⟨a, ...⟩ else l x).
--   IH:     expectedLength P' (huffmanLength P') ≤ expectedLength P' l'.
--   bridge L: expectedLength P (huffmanLength P)
--              = expectedLength P' (huffmanLength P') + (P {a} + P {b})  -- Huffman side
--   bridge R: expectedLength P l_swap
--              ≥ expectedLength P' l' + (P {a} + P {b})                  -- 鍵 lemma (Phase 5.6)
--   合成 + swap で l に戻す:
--   expectedLength P (huffmanLength P)
--     = (IH 適用) + (P {a} + P {b})
--     ≤ expectedLength P' l' + (P {a} + P {b})
--     ≤ expectedLength P l_swap = expectedLength P l (swap 不変)
```

---

## API 在庫テーブル

### §A. T1-A 既存資産 (publish 済、本 T1-A' で直接 reuse)

**T1-A inventory `docs/shannon/huffman-mathlib-inventory.md` §A 既存 ShannonCode 資産 + 本セクションを併せて参照**。T1-A 完了時点で publish された T1-A' 専用基盤:

| name | file:line | signature (verbatim、`[...]` 含む) | 結論形 (verbatim) | T1-A' での扱い |
| --- | --- | --- | --- | --- |
| `huffmanLength` | `InformationTheory/Shannon/Huffman.lean` | `noncomputable def huffmanLength (P : Measure α) : α → ℕ` (variable `{α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`) | `:= huffmanLengthAux (initMultiset P)` | **reuse 確定** (主定理の LHS) |
| `huffmanLength_pos` | `InformationTheory/Shannon/Huffman.lean` | `theorem huffmanLength_pos (P : Measure α) [IsProbabilityMeasure P] (_hP : ∀ a, 0 < P.real {a}) (h_card : 2 ≤ Fintype.card α) (a : α) : 0 < huffmanLength P a` | `: 0 < huffmanLength P a` | reuse (sibling property の最深 leaf `huffmanLength P a ≥ 1` 用) |
| `huffmanLength_kraft_le_one` | `InformationTheory/Shannon/Huffman.lean` | `theorem huffmanLength_kraft_le_one (P : Measure α) [IsProbabilityMeasure P] (_hP : ∀ a, 0 < P.real {a}) : ∑ a : α, ((2 : ℝ)) ^ (-(huffmanLength P a : ℤ)) ≤ 1` | `: ∑ a : α, ((2 : ℝ)) ^ (-(huffmanLength P a : ℤ)) ≤ 1` | reuse (主定理 RHS の `l` 側に対応する LHS 側の Kraft 充足 — Gibbs 経由 chain で必要) |
| `huffmanLengthAux` | `InformationTheory/Shannon/Huffman.lean` | `noncomputable def huffmanLengthAux (s : Multiset (Finset α × ℝ)) : α → ℕ` (`termination_by s.card`) | `:= if hg : HuffmanGrouping s then if h : 2 ≤ s.card then ... else fun _ => 0 else fun _ => 0` | reuse (n→n-1 induction の内部呼び出し) |
| `huffmanLengthAux_eq_step` | `InformationTheory/Shannon/Huffman.lean` | `lemma huffmanLengthAux_eq_step (s : Multiset (Finset α × ℝ)) (h : 2 ≤ s.card) (hg : HuffmanGrouping s) : huffmanLengthAux s = let step := (huffmanStep s h hg).val; let A := step.1.1; let B := step.2.1.1; let s'' := step.2.2; let g := huffmanLengthAux s''; fun a => if a ∈ A ∨ a ∈ B then g a + 1 else g a` | (verbatim 上記) | reuse (step decomposition 用) |
| `huffmanLengthAux_step_merged` | `InformationTheory/Shannon/Huffman.lean` | `lemma huffmanLengthAux_step_merged (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) {a : α} (ha : a ∈ (huffmanStep s hs hg).val.1.1 ∨ a ∈ (huffmanStep s hs hg).val.2.1.1) : huffmanLengthAux s a = huffmanLengthAux (huffmanStep s hs hg).val.2.2 a + 1` | `: huffmanLengthAux s a = huffmanLengthAux (huffmanStep s hs hg).val.2.2 a + 1` | **reuse 確定** (bridge L: `huffmanLength` の +1 ペナルティを取り出す) |
| `huffmanLengthAux_step_other` | `InformationTheory/Shannon/Huffman.lean` | `lemma huffmanLengthAux_step_other (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) {a : α} (ha : ¬ (a ∈ (huffmanStep s hs hg).val.1.1 ∨ a ∈ (huffmanStep s hs hg).val.2.1.1)) : huffmanLengthAux s a = huffmanLengthAux (huffmanStep s hs hg).val.2.2 a` | `: huffmanLengthAux s a = huffmanLengthAux (huffmanStep s hs hg).val.2.2 a` | **reuse 確定** (bridge L: a ∉ AB の element は不変) |
| `huffmanLengthAux_const_on_group` | `InformationTheory/Shannon/Huffman.lean` | `lemma huffmanLengthAux_const_on_group (s : Multiset (Finset α × ℝ)) (hg : HuffmanGrouping s) (p : Finset α × ℝ) (hp : p ∈ s) (a b : α) (ha : a ∈ p.1) (hb : b ∈ p.1) : huffmanLengthAux s a = huffmanLengthAux s b` | `: huffmanLengthAux s a = huffmanLengthAux s b` | reuse (sibling property: 同じ group に属する element は語長一致 — 「等深兄弟」の核) |
| `huffmanStep` | `InformationTheory/Shannon/Huffman.lean` | `noncomputable def huffmanStep (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) : { p : (Finset α × ℝ) × (Finset α × ℝ) × Multiset (Finset α × ℝ) // p.1 ∈ s ∧ p.2.1 ∈ s.erase p.1 ∧ p.2.2 = (p.1.1 ∪ p.2.1.1, p.1.2 + p.2.1.2) ::ₘ ((s.erase p.1).erase p.2.1) ∧ HuffmanGrouping p.2.2 }` | (上記 verbatim) | reuse (内部 step、Subtype spec の `.property.1` 等で「最小 2 element」を取り出す) |
| `huffmanStep_spec` | `InformationTheory/Shannon/Huffman.lean` | `lemma huffmanStep_spec (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) : (huffmanStep s hs hg).val.1 ∈ s ∧ (huffmanStep s hs hg).val.2.1 ∈ s.erase (huffmanStep s hs hg).val.1 ∧ ... ∧ HuffmanGrouping (huffmanStep s hs hg).val.2.2` | (上記 4-tuple) | reuse (sibling pair の取得) |
| `initMultiset` | `InformationTheory/Shannon/Huffman.lean` | `noncomputable def initMultiset (P : Measure α) : Multiset (Finset α × ℝ) := (Finset.univ : Finset α).val.map (fun a => ({a}, P.real {a}))` | `:= ...` (上記) | reuse (`huffmanLength P = huffmanLengthAux (initMultiset P)`) |
| `HuffmanGrouping` | `InformationTheory/Shannon/Huffman.lean` | `def HuffmanGrouping (s : Multiset (Finset α × ℝ)) : Prop := s.Nodup ∧ (∀ p ∈ s, p.1.Nonempty) ∧ (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint p.1 q.1)` | `:= ...` | reuse (n→n-1 induction で `α'` 側の `initMultiset P'` も `HuffmanGrouping` を満たすことを示す) |

**重要: T1-A 既存実装 `huffmanLength` は `Multiset (Finset α × ℝ)` 上の `Nat.strongRec on s.card` で再帰**。T1-A' でも同じ抽象水準で induction を回すなら、「`P'` を作って `huffmanLength P'` を呼ぶ」のではなく**`huffmanLengthAux (initMultiset P').val` の structural lemma で直接処理**するのが既存 API と整合する経路 (§F-3 参照)。

### §B. T1-A' で新規必要 — min/argmin および「最深 leaf」抽出

sibling property の statement: 「最小 2 確率 element の Huffman 語長は等しく、`l` の最深 leaf である」。「最深 leaf」抽出のための API。

| name | file:line | signature (verbatim、`[...]` 含む) | 結論形 (verbatim) | T1-A' での扱い |
| --- | --- | --- | --- | --- |
| `Finset.exists_max_image` | `Mathlib/Data/Finset/Max.lean:525` | `theorem exists_max_image (s : Finset β) (f : β → α) (h : s.Nonempty) : ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x` (section variable `[LinearOrder α]`) | `: ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x` | **本命**: 「`Finset.univ : Finset α` 上で `huffmanLength P : α → ℕ` 最大の要素」(= 最深 leaf) を取り出す |
| `Finset.exists_min_image` | `Mathlib/Data/Finset/Max.lean:531` | (T1-A 既存、再掲) | (再掲) | reuse (最小確率 element の取り出し、`P.real {a}` の最小) |
| `Finset.min'` | `Mathlib/Data/Finset/Max.lean:180` | (T1-A 既存) | (再掲) | reuse (alt: 順序付き α 上の min') |
| `Finset.min'_lt_max'_of_card` | `Mathlib/Data/Finset/Max.lean` (search needed) | `theorem min'_lt_max'_of_card (h₂ : 1 < #s) : s.min' (card_pos.mp (lt_of_lt_of_le one_pos h₂.le)) < s.max' (card_pos.mp ...)` (section variable `[LinearOrder α]`) | `: s.min' ... < s.max' ...` | (informational) `n ≥ 2` のとき distinct な min, max が存在 |
| `Finset.exists_lt_of_lt_sup'` / `Finset.exists_le_max'` | (search needed) | — | — | (未必要) |

**確認した loogle 結果**:
- `loogle "Finset.exists_min_image, Finset.erase"` → `Found 0 declarations` (= 「`Finset.exists_min_image` を `erase` 後に呼ぶ」直接的なヘルパーは無し → 2 回目の min は `s.erase x1` に対し `Finset.exists_min_image` を再帰呼びする手作業で取る)
- `loogle "Finset.exists_second_min"` → `unknown identifier`
- `loogle "Finset.argmin"` → `unknown identifier` (`Finset.argmin` は存在しない、`List.argmin` は別物)

### §C. T1-A' で新規必要 — `Equiv.swap` + `Function.update` (任意 `l` 正規化)

sibling property の証明では「任意の Kraft-feasible `l` を、最小 2 element が等深兄弟になる形に swap で正規化」する。

| name | file:line | signature (verbatim、`[...]` 含む) | 結論形 (verbatim) | T1-A' での扱い |
| --- | --- | --- | --- | --- |
| `Equiv.swap` | `Mathlib/Logic/Equiv/Basic.lean:634` | `def swap (a b : α) : Perm α` (section variable `{α : Sort u} [DecidableEq α]`) | `:= ...` (実装は permutation) | **本命**: `l : α → ℕ` を `l ∘ Equiv.swap a b` に置き換えて argmin element の swap を実現 |
| `Equiv.swap_apply_left` | `Mathlib/Logic/Equiv/Basic.lean:650` | `theorem swap_apply_left (a b : α) : swap a b a = b` (section variable `{α : Sort u} [DecidableEq α]`) | `: swap a b a = b` | reuse (swap の値計算) |
| `Equiv.swap_apply_right` | `Mathlib/Logic/Equiv/Basic.lean:654` | `theorem swap_apply_right (a b : α) : swap a b b = a` (同 section) | `: swap a b b = a` | reuse |
| `Equiv.swap_apply_of_ne_of_ne` | `Mathlib/Logic/Equiv/Basic.lean:657` | `theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x` (同 section) | `: swap a b x = x` | reuse (a, b 以外は不変) |
| `Equiv.swap_self` | `Mathlib/Logic/Equiv/Basic.lean:639` | `theorem swap_self (a : α) : swap a a = Equiv.refl _` (同 section) | `: swap a a = Equiv.refl _` | (informational) |
| `Function.update` | `Mathlib/Logic/Function/Basic.lean:628` | `def update (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a` (section variable `{α : Sort u} {β : α → Sort v} [DecidableEq α]`) | `:= ...` | alt: `l` の 1 点書き換え (swap でなく直接書き換え) |
| `Function.update_self` | `Mathlib/Logic/Function/Basic.lean:632` | `theorem update_self (a : α) (v : β a) (f : ∀ a, β a) : update f a v a = v` (同 section) | `: update f a v a = v` | reuse |
| `Function.update_of_ne` | `Mathlib/Logic/Function/Basic.lean:636` | `theorem update_of_ne {a a' : α} (h : a ≠ a') (v : β a') (f : ∀ a, β a) : update f a' v a = f a` (同 section) | `: update f a' v a = f a` | reuse |

### §D. T1-A' で新規必要 — Finset.sum の swap/erase/pair bridge (expected length 比較)

`expectedLength P l = ∑ a : α, P.real {a} * l a` の **swap 不変性** と **{a, b} pair の項分け** + **merged 形 expected length への bridge**。

| name | file:line | signature (verbatim、`[...]` 含む) | 結論形 (verbatim) | T1-A' での扱い |
| --- | --- | --- | --- | --- |
| `Finset.sum_pair` (additive of `Finset.prod_pair`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:86` | `theorem prod_pair [DecidableEq ι] {a b : ι} (h : a ≠ b) : (∏ x ∈ ({a, b} : Finset ι), f x) = f a * f b` (section variable `{ι : Type*} {M : Type*} [CommMonoid M] {f : ι → M}`) | `: ∑ x ∈ ({a, b} : Finset ι), f x = f a + f b` | **本命**: bridge で `(P.real {a} + P.real {b}) * (depth + 1)` の項分け |
| `Finset.mul_prod_erase` (additive `Finset.add_sum_erase`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:741` | `theorem mul_prod_erase [DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι} (h : a ∈ s) : (f a * ∏ x ∈ s.erase a, f x) = ∏ x ∈ s, f x` (同 section) | `: (f a + ∑ x ∈ s.erase a, f x) = ∑ x ∈ s, f x` | **本命**: `expectedLength P l = P.real {a} * l a + (∑ x ∈ Finset.univ.erase a, P.real {x} * l x)` の取り出し |
| `Finset.prod_erase_mul` (additive `Finset.sum_erase_add`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:747` | `theorem prod_erase_mul [DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι} (h : a ∈ s) : (∏ x ∈ s.erase a, f x) * f a = ∏ x ∈ s, f x` (同 section) | `: (∑ x ∈ s.erase a, f x) + f a = ∑ x ∈ s, f x` | reuse (commutative variant) |
| `Finset.prod_attach` (additive `Finset.sum_attach`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:100` | `lemma prod_attach (s : Finset ι) (f : ι → M) : ∏ x ∈ s.attach, f x = ∏ x ∈ s, f x` (同 section) | `: ∑ x ∈ s.attach, f x = ∑ x ∈ s, f x` | **本命**: `s.attach` 上の sum を `s` 上の sum に bridge (`Subtype` を経由する merged `α'` 路線で必須) |
| `Finset.prod_image` (additive `Finset.sum_image`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:95` | `theorem prod_image [DecidableEq ι] {s : Finset κ} {g : κ → ι} : Set.InjOn g s → ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x)` (同 section) | `: ∑ x ∈ s.image g, f x = ∑ x ∈ s, f (g x)` | reuse (`α' → α` injection 経由で sum bridge) |
| `Finset.prod_sumElim` (additive `Finset.sum_sumElim`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:212` | `theorem prod_sumElim (s : Finset ι) (t : Finset κ) (f : ι → M) (g : κ → M) : ∏ x ∈ s.disjSum t, Sum.elim f g x = (∏ x ∈ s, f x) * ∏ x ∈ t, g x` (同 section) | `: ∑ x ∈ s.disjSum t, Sum.elim f g x = (∑ x ∈ s, f x) + ∑ x ∈ t, g x` | (alt) `α ⊕ Unit` 路線を採用するなら使用 (§F-2 参照) |
| `Finset.prod_subtype_of_mem` (additive `Finset.sum_subtype_of_mem`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:433` | `theorem prod_subtype_of_mem (f : ι → M) {p : ι → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) : ∏ x ∈ s, f x = ∏ x : { x // p x }, ...` (簡略表記) | (`Subtype` 経由の sum bridge) | reuse (`{x : α // x ≠ b}` 上の sum を `α` 上の sum に持ち上げ) |
| `Finset.sum_le_sum` / `Finset.sum_lt_sum` | (T1-A 既存) | (再掲) | (再掲) | reuse (LHS ≤ RHS の不等式の本体) |

### §E. T1-A' で新規必要 — merged 型 `α'` の表現とその cardinality / Fintype 構造

n→n-1 induction で「`b` を `a` に同一視した `α'`」を表現する API。**3 候補**を §F-2 で議論、ここではそれぞれに必要な Mathlib API を列挙。

#### (E-i) Subtype 経路 `α' := { x : α // x ≠ b }` — **推奨**

| name | file:line | signature (verbatim、`[...]` 含む) | 結論形 (verbatim) | T1-A' での扱い |
| --- | --- | --- | --- | --- |
| `Finset.image_erase` | `Mathlib/Data/Finset/Image.lean:444` | `theorem image_erase [DecidableEq α] {f : α → β} (hf : Injective f) (s : Finset α) (a : α) : (s.erase a).image f = (s.image f).erase (f a)` (section variable `{α β : Type*} [DecidableEq β]`) | `: (s.erase a).image f = (s.image f).erase (f a)` | reuse (`{x // x ≠ b}.attach.image (↑·)` = `(Finset.univ).erase b`) |
| `Subtype.instFintype` (auto) | `Mathlib/Data/Fintype/Basic.lean` | (auto-derive from `[Fintype α] [DecidablePred p]`) | (auto) | **必須**: `α'` への `[Fintype α']` 継承 |
| `Subtype.instMeasurableSpace` (auto) | `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean` | (auto-derive) | (auto) | **必須**: `α'` への `[MeasurableSpace α']` 継承 |
| `Subtype.measurableSingletonClass` | `Mathlib/MeasureTheory/MeasurableSpace/Basic.lean` (verify) | (auto-derive from `[MeasurableSingletonClass α]`) | (auto) | **必須**: `α'` への `[MeasurableSingletonClass α']` 継承 (Subtype 路線の利点) |
| `Fintype.card_subtype` | `Mathlib/Data/Fintype/Card.lean` (verify) | `theorem Fintype.subtype_card [Fintype α] (s : Finset α) (h : ∀ x, x ∈ s ↔ p x) : @Fintype.card {x // p x} _ = #s` | `: @Fintype.card {x // p x} _ = #s` | reuse (`Fintype.card α' = Fintype.card α - 1`) |
| `Finset.card_erase_of_mem` | (T1-A 既存) | (再掲) | (再掲) | reuse |

#### (E-ii) Quotient 経路 `α' := Quotient (s : Setoid α)` — **非推奨** (型クラス継承困難)

| name | file:line | signature (verbatim、`[...]` 含む) | 結論形 (verbatim) | T1-A' での扱い |
| --- | --- | --- | --- | --- |
| `Setoid` | `Init/Core.lean` (core Lean) | `class Setoid (α : Sort u) extends HasEquiv α where iseqv : Equivalence r` | (class) | (informational) |
| `Quotient.mk` | `Init/Core.lean` | `protected def Quotient.mk (s : Setoid α) (a : α) : Quotient s` | `: Quotient s` | (informational) |
| `Quotient.fintype` | `Mathlib/Data/Fintype/Basic.lean` (verify) | `instance Quotient.fintype [Fintype α] (s : Setoid α) [DecidableRel s.r] : Fintype (Quotient s)` | (instance) | (informational) |
| `Fintype.card_quotient_le` | `Mathlib/Data/Fintype/Card.lean` (verify) | `theorem Fintype.card_quotient_le [Fintype α] (s : Setoid α) [DecidableRel s.r] : Fintype.card (Quotient s) ≤ Fintype.card α` | `: ≤` (= 不可) | **欠陥**: 「`Fintype.card α' = Fintype.card α - 1`」は単なる `≤` でなく等号を要し、merge {a~b} に特化した `card_quotient_eq_card_sub_one` lemma が **Mathlib 不在** → 自前 ~20 行 |
| `Quotient.MeasurableSpace` (auto?) | (未調査、推測) | `MeasurableSpace (Quotient s)` の auto-derive は `[MeasurableSpace α]` から **必ずしも継承されない** | — | **欠陥**: `Quotient` 上の `MeasurableSpace` は **自前で `borel` か `comap` 経由で付与**する必要、`MeasurableSingletonClass` は更に困難 |

**確認した loogle**: `loogle "Setoid"` → 448 declarations、`Quotient.fintype` (`Mathlib/Data/Fintype/Basic.lean`) と `Fintype.card_quotient_le` (`Mathlib/Data/Fintype/Card.lean`) は存在するが、**等号版** `Fintype.card (Quotient s) = Fintype.card α - (# 同値類で merge された個数)` 系は **0 declarations**。

#### (E-iii) `Option α'` / `Sum α' Unit` 経路 — 中間案

| name | file:line | signature (verbatim、`[...]` 含む) | 結論形 (verbatim) | T1-A' での扱い |
| --- | --- | --- | --- | --- |
| `Sum.elim` | `Init/Data/Sum/Basic.lean` (core Lean) | `def Sum.elim {γ : Sort u} (f : α → γ) (g : β → γ) : α ⊕ β → γ` | `: α ⊕ β → γ` | alt (`l : α ⊕ Unit → ℕ` で表現) |
| `Finset.prod_disjSum` (additive `sum_disjSum`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:200` | `theorem prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι ⊕ κ → M) : ∏ x ∈ s.disjSum t, f x = (∏ x ∈ s, f (Sum.inl x)) * ∏ x ∈ t, f (Sum.inr x)` (同 §D section) | `: ∑ x ∈ s.disjSum t, f x = (∑ x ∈ s, f (Sum.inl x)) + ∑ x ∈ t, f (Sum.inr x)` | alt (sum decomposition) |
| `Equiv.sumCompl` / `Equiv.sumPSigmaDistrib` | (search needed) | — | — | (alt 経路の bridge) |

### §F. T1-A' で新規必要 — strong induction on `Fintype.card α`

T1-A 既存 `huffmanLengthAux_const_on_group` (`InformationTheory/Shannon/Huffman.lean`) や `huffmanLengthAux_pos_of_mem` (`InformationTheory/Shannon/Huffman.lean`) は `induction hn : s.card using Nat.strong_induction_on generalizing s` の pattern で書かれている。T1-A' でも同じ pattern を `Fintype.card α` の strong induction で使うのが既存実装と整合。

| name | file:line | signature (verbatim、`[...]` 含む) | 結論形 (verbatim) | T1-A' での扱い |
| --- | --- | --- | --- | --- |
| `Nat.strong_induction_on` | `Mathlib/Data/Nat/Init.lean:281` | `@[elab_as_elim] protected theorem strong_induction_on {p : ℕ → Prop} (n : ℕ) (h : ∀ n, (∀ m < n, p m) → p n) : p n` | `: p n` | **本命** (`induction hn : Fintype.card α using Nat.strong_induction_on generalizing α P l ...`) |
| `Nat.strongRecOn'` | `Mathlib/Data/Nat/Init.lean:256` | `def strongRecOn' {P : ℕ → Sort*} (n : ℕ) (h : ∀ n, (∀ m < n, P m) → P n) : P n` | `: P n` | alt (def-level strong recursion、`huffmanLengthAux` の termination で使用済) |
| `Fintype.card_subtype_lt` | (search needed, e.g., `Fintype.card_lt_of_injective_not_surjective` 系) | — | — | (informational, `Fintype.card {x // x ≠ b} = Fintype.card α - 1`) |
| `Fintype.equivOfCardEq` | `Mathlib/Data/Fintype/EquivFin.lean:143` | `noncomputable def equivOfCardEq (h : card α = card β) : α ≃ β` (section variable `{α β : Type*} [Fintype α] [Fintype β]`) | `: α ≃ β` | (alt) IH の statement を `Fintype.card α = n - 1` で書く際、`α` を具体的に `Fin (n-1)` に書き戻すなら使用 |
| `Finset.one_lt_card` | `Mathlib/Data/Finset/Card.lean:721` | `theorem one_lt_card : 1 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b` (section variable `{α : Type*} {s : Finset α}`) | `: 1 < #s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b` | reuse (`n ≥ 2` から「distinct な 2 element」を取り出す) |
| `Finset.one_lt_card_iff` | `Mathlib/Data/Finset/Card.lean:724` | `theorem one_lt_card_iff : 1 < #s ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b` (同 section) | `: 1 < #s ↔ ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b` | reuse (∃ unfolded form) |

### §G. T1-A' で新規必要 — Real 算術 (Kraft inequality の merge bridge)

merged `α'` 上の Kraft sum `∑ x : α', (2 : ℝ) ^ (-(l' x : ℤ))` と元の `∑ a : α, (2 : ℝ) ^ (-(l a : ℤ))` の関係。`+1` ペナルティ吸収: `2 ^ (-(d : ℤ)) = 2 ^ (-((d+1) : ℤ)) + 2 ^ (-((d+1) : ℤ))`.

| name | file:line | signature (verbatim、`[...]` 含む) | 結論形 (verbatim) | T1-A' での扱い |
| --- | --- | --- | --- | --- |
| `zpow_neg` / `Real.rpow_neg` 系 | `Mathlib/Algebra/GroupPower/Basic.lean` 等 | (T1-A 既存実装で繰り返し使用、`kraftPerGroup` 内部で `2 ^ (-(d+1 : ℤ)) + 2 ^ (-(d+1 : ℤ)) = 2 ^ (-(d : ℤ))` を展開済) | — | reuse (既存 `kraftPerGroup_step` の cast pattern を踏襲) |
| `Real.rpow_lt_one_iff` 等 | (T1-A 既存 ShannonCode で使用済) | — | — | reuse |

T1-A 既存 `huffmanLength_kraft_le_one` の proof で `2 ^ (-(d+1 : ℤ)) + 2 ^ (-(d+1 : ℤ)) = 2 ^ (-(d : ℤ))` の calculation chain が **既に書かれている** (`InformationTheory/Shannon/Huffman.lean` `kraftPerGroup_step` 内、行 682-865)。T1-A' でも **同じ identity を expectation の merge bridge で再利用**するため、補助 lemma `pow_two_neg_succ_add_self` (= 「`2 * 2^(-(d+1)) = 2^(-d)`」) を T1-A' 専用に抽出すべき (~5 行)。

---

## 主要前提条件ボックス

- `Equiv.swap`: `[DecidableEq α]` 必須 → T1-A 既存 variable で OK。
- `Function.update`: `[DecidableEq α]` 必須 → 同上 OK。
- `Finset.exists_max_image` / `Finset.exists_min_image`: image の codomain (`α` or `R`) に `[LinearOrder _]` 必須 → 最深 leaf は `huffmanLength P : α → ℕ` で `ℕ` linear order、最小確率は `P.real {a} : ℝ` で `ℝ` linear order、いずれも OK。
- `Finset.mul_prod_erase` / `Finset.sum_pair`: `[DecidableEq ι]` + `[CommMonoid M]` (additive 版は `[AddCommMonoid M]`) → `ℝ` で OK。
- `Subtype` 経路 (§E-i): `α' := { x : α // x ≠ b }` への type-class 継承
  - `[Fintype α']` ← `Subtype.fintype` (auto, requires `[Fintype α]` + `[DecidablePred (· ≠ b)]` ← `[DecidableEq α]`).
  - `[DecidableEq α']` ← `Subtype.decidableEq` (auto, requires `[DecidableEq α]`).
  - `[Nonempty α']` ← `n ≥ 2` から **手作業で示す** (`Fintype.card α ≥ 2` ⇒ `∃ a, a ≠ b`).
  - `[MeasurableSpace α']` ← `Subtype.instMeasurableSpace` (auto).
  - `[MeasurableSingletonClass α']` ← `Subtype.measurableSingletonClass` (要確認、`Mathlib/MeasureTheory/MeasurableSpace/Basic.lean` 検索)。**もし不在なら自前 ~10 行** (singleton in `α'` corresponds to singleton in `α`)。
- `Quotient` 経路 (§E-ii): **`MeasurableSpace (Quotient s)` の自動継承が不明**。`Mathlib/Data/Quot.lean` には `Quotient.fintype` 等が揃うが、`Quotient.instMeasurableSpace` は通常 `comap (Quotient.mk s)` で induce する手作業必要。**撤退ライン §G-2 発動の主要因**。

---

## 自作が必要な要素

| 優先度 | 名前 | 推奨実装 | 工数感 | 落とし穴 |
| --- | --- | --- | --- | --- |
| 1 | `exists_deepest_leaf` (T1-A' 内 helper) | `Finset.exists_max_image (Finset.univ : Finset α) (huffmanLength P)` を unfold した形 | ~15 行 | `n ≥ 1` (= `Finset.univ.Nonempty`) の前提を `[Nonempty α]` から取り出す bridge |
| 1 | `exists_sibling_min_pair` (Cover-Thomas Lemma 5.8.1) | (a) 最深 leaf 取り出し、(b) `huffmanLengthAux_const_on_group` で「最深 leaf を含む group `p ∈ initMultiset` の全 element は同じ深さ」、(c) min 2 確率と最深 leaf の swap 不変性 (swap argument は **`Equiv.swap` ベース**) | ~150-200 行 | swap argument は教科書通り、しかし「2 つの最深兄弟」を `huffmanLength P` の値だけから取り出すには **`initMultiset P` の最深 group `p ∈ initMultiset P` が `p.1.card ≥ 2` を満たすことを示す**必要。これは Huffman merge の構造的性質 (最深 group は必ず最後の merge step で生まれた `merged group`) なので、`huffmanLengthAux_eq_step` の逆向きの不変量 lemma が必要 (~50 行) |
| 1 | merged `Measure P' : Measure α'` の構成 + `IsProbabilityMeasure P'` | `α' := { x : α // x ≠ b }` 上で `P'.real {⟨a, ha⟩} := P.real {a} + P.real {b}` (a = 特定 element), 他は `P.real`. | ~80-100 行 | `Measure` の point-mass 構成は InformationTheory 既存 (e.g. `InformationTheory/Stein.lean` の `Measure.dirac` 等) でも繰り返し使われており pattern 確立済、しかし `Subtype` 上で書くと `MeasurableSet {⟨a, ha⟩}` 等の bridge が要る (~30 行) |
| 1 | merged `huffmanLength P' = ...` bridge | T1-A 既存 `huffmanLengthAux_step_merged` + `huffmanLengthAux_step_other` を `initMultiset P → initMultiset P'` の対応で結ぶ | ~80 行 | **本 inventory の最大の不確実性**: `initMultiset P` と `initMultiset P'` は `Multiset (Finset α × ℝ)` vs `Multiset (Finset α' × ℝ)` で **型が違う** → T1-A 既存 step lemma を直接適用できない。**§F-3 の design judgement が要**。代替: `initMultiset P'` を作らず、「`initMultiset P` の 1 step 進めた `huffmanStep` の結果」と直接対比する (`α' = α` 型を不変に保つ、`huffmanLengthAux_step_merged` を直接適用可) |
| 2 | bridge L `expectedLength P (huffmanLength P) = ... + (P {a} + P {b})` | `Finset.mul_prod_erase` 2 回適用で `a, b` の項を抜き出し、`huffmanLengthAux_step_merged` で `+1` ペナルティを取り出し、`{x : α // x ≠ a, x ≠ b}` 上の sum と merged 形を結ぶ | ~80 行 | `Finset.attach` + `Subtype` 経由の sum bridge は **Mathlib `Finset.sum_attach` 1 行で取れる**が、`P.real` を `α'` 上に lift する所で `MeasurableSet` が顔を出す。`Subtype` 路線なら auto-derive で済む |
| 2 | bridge R `expectedLength P l_swap ≥ expectedLength P' l' + (P {a} + P {b})` (鍵 lemma) | sibling property で `l_swap a = l_swap b = depth + 1` を保証、`l'` を `{x // x ≠ b}` 上で `l_swap x` ただし `x = a` のとき `l_swap a - 1 = depth` に書き換え | ~100-150 行 | **核心の非自明箇所**。`l_swap a = l_swap b` の **等号** + `l a, l b` が共に最大 (depth) であることを使う。任意 `l` 側では `l_swap a = l_swap b` は **swap で人工的に作る** (Cover-Thomas Lemma 5.8.1 (i)/(ii))、ここで `l a + l b` の和は不変だが個別の値は変わる |
| 3 | `huffmanLength_optimal` (主定理) | sibling property + bridge L + bridge R + IH (n-1 上の `huffmanLength_optimal`) を strong induction で合成 | ~100 行 | base case (`n = 1`) は trivial (`huffmanLength = 0`、`l ≥ 1`)、step case の合成は機械的 |

**規模見積もり**: 15 + 200 + 100 + 80 + 80 + 150 + 100 = **~725 行**。roadmap T1-A' 規模見積もり **~400-500 行を超過**。**§F-3 の design judgement で型変化を回避すれば ~500 行に収まる**見込み。

---

## §F. 想定 design judgement の材料 (T1-A' 専用)

### F-1. sibling property の statement form

T1-A inventory §F-4 の論点 (intermediate lemma 化 vs inline 化) は plan §C-4 で「intermediate lemma 化」を確定済。T1-A' でも踏襲。

**追加判断**: sibling property の statement で「最深 leaf」と「最小 2 確率」を **同一 lemma で結ぶ** か **2 件に分割** か。

```lean
-- 候補 (a): 統合 (plan §C-4 で採用済)
theorem exists_sibling_min_pair (P : Measure α) ... :
    ∃ a b, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, huffmanLength P c ≤ huffmanLength P a) ∧
      (∀ c, P.real {a} ≤ P.real {c} ∨ P.real {b} ≤ P.real {c})

-- 候補 (b): 分離
theorem exists_deepest_pair (P : Measure α) ... :
    ∃ a b, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, huffmanLength P c ≤ huffmanLength P a)
theorem deepest_pair_are_min_prob (P : Measure α) ... :
    let (a, b) := exists_deepest_pair P ...
    ∀ c, P.real {a} ≤ P.real {c} ∨ P.real {b} ≤ P.real {c}
```

**推奨**: 候補 (a) 統合 (plan §C-4 踏襲)。主定理 induction step で 1 件取り出せばよいので、分割するメリットが proof structure 上薄い。Cover-Thomas Lemma 5.8.1 (i)/(ii) はそれぞれ「最深 leaf を min 確率と swap 可」「最深 leaf の兄弟も最深」だが、これらは **`exists_sibling_min_pair` の内部 helper** として `private theorem` で抽出する。

### F-2. merged 型 `α'` の表現

| 候補 | 利点 | 欠点 | 推奨度 |
| --- | --- | --- | --- |
| (i) Subtype `α' := { x : α // x ≠ b }` | Mathlib type-class auto-derive (`Fintype`, `DecidableEq`, `MeasurableSpace`, `MeasurableSingletonClass` 全て継承)、`α' → α` の coercion が常に injective | `[Nonempty α']` は手作業 (`n ≥ 2` から構成)、`P'` の measure 構成で `MeasurableSet` を 1 度経由 | **★ 推奨** |
| (ii) Quotient `α' := Quotient (s : Setoid α)` (`a ~ b`) | textbook 流に「同値類で merge」、`Sum.elim` 不要 | `MeasurableSpace (Quotient s)` の自動継承が **不明** (要 `comap` 自前付与)、`MeasurableSingletonClass` は更に困難 → **撤退ライン §G-2 発動リスク** | × |
| (iii) `Option α'` (where `α'` is Subtype 経路) | `b` を `none` に flatten | `Option` の `MeasurableSpace` は `Option.instMeasurableSpace` で auto-derive されるが、`MeasurableSingletonClass` の継承は要確認 | △ (理論上可能、実装コスト不明) |
| (iv) `α' = α` 型不変 (merge を関数値で表現) | 型変化なし、IH を `huffmanLengthAux (huffmanStep s ...).val.2.2` 上で直接 | T1-A 既存 `huffmanLength` を呼ぶには `initMultiset P'` を作る必要があり、結局 `α'` 型問題に帰着 | ◯ (代案、§F-3 と組み合わせ) |

**推奨**: (i) Subtype 経路 (`α' := { x : α // x ≠ b }`)。Mathlib type-class 継承が全自動で、撤退ライン §G-2 を予防できる。

**注意点**: Subtype 経路を採ると、`Measure α'` の構成で `Subtype.instMeasurableSpace` を使うが、`P' = (P.restrict (Set.univ \ {b})).comap Subtype.val` 等の **measure pushforward / pullback** で組むと、`P'.real {⟨a, ha⟩} = P.real {a}` の bridge を 1 件 (~20 行) 書く必要。代替: `Measure.toReal` を介さず `P.real {a}` を直接 `α' → ℝ` の関数として持つ手作業 ~30 行。

### F-3. T1-A' を **`α'` 型変化を回避する設計** にできるか

**Key insight**: T1-A 既存 `huffmanLengthAux` は `Multiset (Finset α × ℝ)` 上の再帰で **`α` 型は不変**。merge step で `α` の subset を `Finset.union` で merge するが **`α` 自身は変えない**。T1-A' でも同じ抽象水準を保てば `α'` 型は要らない。

```lean
-- α' を作らない案 (推奨 § F-3 採用)
-- IH の statement を「huffmanLengthAux (huffmanStep (initMultiset P) ...).val.2.2 上の最適性」で書く
-- = 「α 型不変、しかし initMultiset から 1 step 進んだ Multiset 上の huffmanLength の最適性」
-- これなら α' / Subtype / Quotient のいずれも不要

theorem huffmanLengthAux_optimal
    (s : Multiset (Finset α × ℝ)) (hg : HuffmanGrouping s)
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_kraft : ... ≤ kraftPerGroup s) :  -- ここの仮定が要 cleanup
    -- 「s が initMultiset P から有限回 huffmanStep で到達可能 (= HuffmanReachable s P)」
    -- の前提下で expectedLength P (huffmanLengthAux s) ≤ expectedLength P l
    sorry
```

ただしこの設計は **「`l : α → ℕ` 側の Kraft 不等式を `s : Multiset (Finset α × ℝ)` の構造に整合させる仮定」が冗長になる** リスクあり (in particular, `kraftSum 2 l` を「`s` 上の Kraft」と読み替える bridge ~50 行)。

**判断**:
- 推奨 (i): **`α'` 型を作る Subtype 経路** + `huffmanLength P' : Measure α' → α' → ℕ` を呼ぶ古典的 induction。実装規模 ~725 行、§F-2 (i) で型問題を回避。
- 推奨 (ii): **`α'` 型を作らない `Multiset (Finset α × ℝ)` 不変経路** + `huffmanLengthAux s` を主役に IH を書く。実装規模 ~500 行に圧縮可能、ただし Kraft sum の bridge ~50 行が新規。

**最終推奨 (本 inventory 段階での暫定)**: **(ii) `α'` 型不変経路**。T1-A の既存実装が既に `Multiset (Finset α × ℝ)` 上で抽象化されており、`α'` 型を導入するとその抽象との二重管理になる。lean-planner 段階で再評価。

### F-4. `n → n-1` induction の Lean 表現

| 候補 | 利点 | 欠点 | 推奨度 |
| --- | --- | --- | --- |
| (a) `induction hn : Fintype.card α using Nat.strong_induction_on generalizing α P l ...` | textbook 流 | `generalizing α` が複雑 (`[Fintype α]` 等の type-class も generalize 必要) | △ |
| (b) `induction hn : s.card using Nat.strong_induction_on generalizing s P l ...` (`s : Multiset (Finset α × ℝ)` 上) | T1-A 既存 `huffmanLengthAux_pos_of_mem` / `huffmanLengthAux_const_on_group` と同 pattern | `α` 型は不変、`s.card` の strict decrease は `huffmanStep_card_lt` で取れる | **★ 推奨** (F-3 (ii) と整合) |
| (c) `Multiset.strongInductionOn` | termination が `card_lt_card` で自動 | T1-A 既存 plan §C-5 で却下済 (Lean 4 `Multiset.lt` の cons+erase での壊れ問題) | × |

**推奨**: (b) `s.card` 上の `Nat.strong_induction_on` (T1-A 既存 pattern と一致)。

---

## 撤退ライン

### §G-1. T1-A' の規模が ~500 行を大きく超える (~700+)

- **発動条件**: 実装 attempt で sibling property + bridge L + bridge R + 主定理合成が ~500 行に収まらず、~700 行を超える見込みになる。
- **対応**:
  - **(a) 弱形 publish**: 「任意 `l` の比較」を諦め、Shannon code との比較 `huffmanLength_le_shannonLength` のみ publish (T1-A 当初の弱形、判断ログ #2 と同じ retreat)。
  - **(b) D-ary 拡張を放棄**: 本 plan は binary 限定なので発動条件外。
- **判断**: 弱形 publish は本来 T1-A で済んでいる縮退案、ここで戻ると T1-A → T1-A' の分離意義が失われる → **発動 NG**。`α'` 型不変経路 (§F-3 (ii)) で 500 行収束を目指す。

### §G-2. merged 型 `α'` の `MeasurableSpace` / `MeasurableSingletonClass` の type-class 継承が困難

- **発動条件**: §F-2 (i) Subtype 路線で `Subtype.measurableSingletonClass` の auto-derive が確認できず、自前付与 ~50 行が必要になる。または §F-2 (ii) Quotient 路線を採って `MeasurableSpace (Quotient s)` の自前 `comap` 構成が必要になる。
- **対応**:
  - **(a) `α'` 型を作らない経路 (§F-3 (ii)) へ pivot**。`Multiset (Finset α × ℝ)` 上で induction、`α` 型不変。
  - **(b) `pmf : α → ℝ` 路線 (T1-A inventory §F-3 (ii) と同じ問題)** に pivot — `Measure α` を捨て、`expectedLengthOfPmf : (α → ℝ) → (α → ℕ) → ℝ` を新規 def。既存 `entropyD_le_expectedLength_of_kraft` との結合が無コストでなくなる (~30 行のbridge追加) が、`α'` 型変化への耐性が大幅に上がる。
- **判断**: **(a) を default**、(b) は (a) が動かない時の二次撤退。

### §G-3. sibling property の swap argument が 5 ターン進まない

- **発動条件**: `exists_sibling_min_pair` の proof (Cover-Thomas Lemma 5.8.1 の swap 部分) が 5 ターン以上 attempt しても 0 sorry に至らない。
- **対応**: **本 plan scope-out** — sibling property を別 seed `T1-A''` (更に分離) に切り出し、T1-A' は「sibling property を `axiom` として仮定する弱版」で wrap-up。
- **判断**: 教科書 swap argument は機械的だが Lean 4 で書くと `Equiv.swap` + `Function.update` の cast 地獄に hit する可能性、proof-pivot-advisor 相談ライン。

---

## 着手 skeleton (`InformationTheory/Shannon/HuffmanOptimal.lean`、~50 行)

```lean
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import InformationTheory.Shannon.Huffman

/-!
# Huffman 最適性 主定理 (T1-A' Cover-Thomas Theorem 5.8.1)

T1-A (`InformationTheory/Shannon/Huffman.lean`) で publish された `huffmanLength` の **最適性**
(任意 Kraft-feasible 語長関数 `l` との比較形) を、sibling property + n → n-1 induction で
証明する。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Sibling property (Cover-Thomas Lemma 5.8.1) -/

/-- **Sibling property (intermediate lemma)** — 最小 2 確率 element の Huffman 語長が
等しく、`huffmanLength` の最深 leaf である. -/
theorem exists_sibling_min_pair
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    ∃ a b : α, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, huffmanLength P c ≤ huffmanLength P a) ∧
      (∀ c, P.real {a} ≤ P.real {c} ∨ P.real {b} ≤ P.real {c}) := by
  sorry

/-! ### 主定理 (Cover-Thomas Theorem 5.8.1) -/

/-- **主定理**: Huffman 語長は任意の Kraft-feasible 語長関数より expected length が小さい. -/
theorem huffmanLength_optimal
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l := by
  sorry

end InformationTheory.Shannon.Huffman
```

`InformationTheory.lean` への追加:

```lean
import InformationTheory.Shannon.HuffmanOptimal
```

---

## §H. 既存率 / 自作見積もりサマリ

- **新規必要な Mathlib API**: 約 **25 件** (§B〜§F)。**全て既存** (`Finset.exists_max_image` / `Equiv.swap` / `Function.update` / `Finset.mul_prod_erase` / `Finset.sum_pair` / `Finset.sum_attach` / `Finset.sum_image` / `Nat.strong_induction_on` / `Finset.one_lt_card` / `Subtype.*` auto-derive 等)。**0 件の自前構築 Mathlib API**。
- **自作必要 (T1-A' 専用 lemma)**: **6 件** (`exists_deepest_leaf`, `exists_sibling_min_pair`, merged `P'` 構成, merged `huffmanLength` bridge, bridge L, bridge R) + 主定理 1 件。
- **既存 T1-A publish (`InformationTheory/Shannon/Huffman.lean`) を直接 reuse**: **10 件** (§A) — `huffmanLength`, `huffmanLength_pos`, `huffmanLength_kraft_le_one`, `huffmanLengthAux`, `huffmanLengthAux_eq_step`, `huffmanLengthAux_step_merged`, `huffmanLengthAux_step_other`, `huffmanLengthAux_const_on_group`, `huffmanStep`, `huffmanStep_spec`.
- **撤退ライン発動見込み**: **no** (§G-2 を §F-2 (i) Subtype 経路 + §F-3 (ii) `α'` 型不変経路で予防、§G-1 は §F-3 (ii) で 500 行収束を狙う、§G-3 は proof-pivot-advisor 相談ライン)。
- **最も危険な発見**: §F-3 の design judgement (型変化を回避するか否か) が **本 T1-A' の規模を 500 行〜725 行の間で大きく振らす**。lean-planner が plan 起草時に「Subtype 経路 (型変化あり、規模 ~725 行)」vs 「Multiset 上不変経路 (規模 ~500 行)」のどちらを採るかを **Phase 0 で確定** する必要あり。判断保留のまま実装に入ると mid-proof で型変化を回避する別経路に pivot する事態 (T1-A 判断ログ #3-4 と同種の問題) が再発するリスク高。

---

## 推奨設計 (1 行サマリ)

**§F-2 (i) Subtype `α' := { x : α // x ≠ b }` + §F-3 (ii) `α'` 型不変経路 (= `huffmanLengthAux s` 上の strong induction on `s.card`) + §F-4 (b) `Nat.strong_induction_on` の組み合わせで、T1-A 既存 API (`huffmanLengthAux_step_merged` / `huffmanLengthAux_step_other` / `huffmanLengthAux_const_on_group`) を再利用しつつ ~500 行で完成。**

---

## 参考

- T1-A inventory: [`huffman-mathlib-inventory.md`](./huffman-mathlib-inventory.md)
- T1-A plan (完了): [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md)
- T1-A 実装: `InformationTheory/Shannon/Huffman.lean` (953 行 / 0 sorry)
- Cover & Thomas *Elements of Information Theory* 2nd ed.,
  - **Lemma 5.8.1** (sibling property, swap argument)
  - **Theorem 5.8.1** (Huffman optimality, n → n-1 induction)
- `Multiset.exists_min_image`: `Mathlib/Data/Finset/Max.lean:567`
- `Finset.exists_min_image`: `Mathlib/Data/Finset/Max.lean:531`
- `Finset.exists_max_image`: `Mathlib/Data/Finset/Max.lean:525`
- `Equiv.swap`: `Mathlib/Logic/Equiv/Basic.lean:634`
- `Function.update`: `Mathlib/Logic/Function/Basic.lean:628`
- `Finset.mul_prod_erase`: `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:741`
- `Finset.sum_pair` (additive of `Finset.prod_pair`): `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:86`
- `Finset.sum_attach` (additive of `Finset.prod_attach`): `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:100`
- `Finset.sum_image` (additive of `Finset.prod_image`): `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:95`
- `Nat.strong_induction_on`: `Mathlib/Data/Nat/Init.lean:281`
- `Finset.image_erase`: `Mathlib/Data/Finset/Image.lean:444`
- `Finset.one_lt_card`: `Mathlib/Data/Finset/Card.lean:721`
- `Fintype.equivOfCardEq`: `Mathlib/Data/Fintype/EquivFin.lean:143`
- loogle index: `.lake/build/loogle.index` (build 済)
