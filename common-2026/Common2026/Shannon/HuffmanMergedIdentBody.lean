import Mathlib.Logic.Equiv.Basic
import Common2026.Shannon.HuffmanOptimality

/-!
# T1-A'' Huffman merged-length identification — vertical reduction (Wave 10, Seed S4)

`HuffmanMergedIdentificationHypothesis` (`HuffmanOptimality.lean`) の **下半分** を扱う.
内容: 任意 measure `Q` (3 ≤ card), sibling leaves `a ≠ b`, 任意 `x` で
`huffmanLength (mergedMeasure Q a b hab) x = (if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val)`.

## Approach

完全 discharge は `huffmanLengthAux` 再帰 (`huffmanStep` の `Classical.choose` を含む) を
2 carrier (`β` と `{x // x ≠ b}`) 間で関連付ける必要があり、judgement log #3 で
「~550 行 / 4-6 セッション / 不可能 scope」と判定済 (`huffman-optimality-t1apprime-moonshot-plan.md`).
`Classical.choose` の min 選択は relabeling と一般には可換でないため、naive な relabeling-invariance
は成立しない。

そこで本 file は seed の撤退ライン (vertical 分解) を採り、**measure-theory 層を完全に
discharge** して、残る genuine な再帰 content だけを **strictly more primitive** な predicate
`MergedHuffmanAuxIdentHypothesis` へ落とす:

1. `mergedMeasure` (= `Measure.sum` of diracs) を `initMultiset` 経由で **explicit な multiset**
   `mergedInitMultiset Q a b` に書き換える (`mergedMeasure_real` + `Multiset.map_congr` で
   完全証明、no-op でなく measure→multiset の genuine な簡約).
2. `huffmanLength = huffmanLengthAux ∘ initMultiset` (defeq) を使い、原 hypothesis を
   `huffmanLengthAux (mergedInitMultiset Q a b) x = ...` という pure-combinatorics の primitive
   predicate へ等価変形.
3. `MergedHuffmanAuxIdentHypothesis → HuffmanMergedIdentificationHypothesis` を **完全証明** で publish.

`mergedInitMultiset` は `Measure.real` を含まない explicit な `Finset {x // x≠b} × ℝ` の multiset
なので、原 predicate より厳密に primitive (measure 層が剥がれている). no-op でも defeq でも
ない (両者は `mergedMeasure_real` という非自明な等式で結ばれる).
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators

universe u

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Section A — `mergedMeasure` の explicit multiset 表現 -/

/-- **Explicit merged init multiset**: `initMultiset (mergedMeasure Q a b hab)` の
measure-free な明示形. 各 subtype 要素 `x : {y // y ≠ b}` に対し singleton group
`({x}, if x.val = a then Q.real{a} + Q.real{b} else Q.real{x.val})` を並べた multiset.

`Measure.sum` / `Measure.dirac` / `Measure.real` を一切含まないため、`mergedMeasure`
を経由する原 predicate より strictly primitive. -/
noncomputable def mergedInitMultiset
    (Q : Measure α) (a b : α) :
    Multiset (Finset {y : α // y ≠ b} × ℝ) :=
  (Finset.univ : Finset {y : α // y ≠ b}).val.map
    (fun x => (({x} : Finset {y : α // y ≠ b}),
      if x.val = a then Q.real {a} + Q.real {b} else Q.real {x.val}))

omit [LinearOrder α] [Nonempty α] in
/-- **measure→multiset 簡約 (genuine, 非 no-op)**: `initMultiset (mergedMeasure Q a b hab)`
は `mergedInitMultiset Q a b` に等しい. 証明は `mergedMeasure_real` (= `Measure.sum_smul_dirac_singleton`
経由の非自明な等式) を term-wise に適用. -/
lemma initMultiset_mergedMeasure_eq
    (Q : Measure α) [IsFiniteMeasure Q] (a b : α) (hab : a ≠ b) :
    initMultiset (mergedMeasure Q a b hab) = mergedInitMultiset Q a b := by
  unfold initMultiset mergedInitMultiset
  apply Multiset.map_congr rfl
  intro x _
  rw [mergedMeasure_real Q a b hab x]

omit [LinearOrder α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **grouping 不変量**: `mergedInitMultiset Q a b` は `HuffmanGrouping` を満たす
(各 singleton group が Nodup / Nonempty / 相互 disjoint). `huffmanLengthAux` を
本 multiset 上で展開する際に必須となる前提. -/
lemma mergedInitMultiset_huffmanGrouping
    (Q : Measure α) (a b : α) :
    HuffmanGrouping (mergedInitMultiset Q a b) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · unfold mergedInitMultiset
    have hinj : Function.Injective
        (fun x : {y : α // y ≠ b} =>
          (({x} : Finset {y : α // y ≠ b}),
            if x.val = a then Q.real {a} + Q.real {b} else Q.real {x.val})) := by
      intro p q hpq
      simp only [Prod.mk.injEq, Finset.singleton_inj] at hpq
      exact hpq.1
    exact (Finset.univ : Finset {y : α // y ≠ b}).nodup.map hinj
  · intro p hp
    unfold mergedInitMultiset at hp
    rw [Multiset.mem_map] at hp
    obtain ⟨x, _, hx⟩ := hp
    rw [← hx]
    exact Finset.singleton_nonempty x
  · intro p hp q hq hpq
    unfold mergedInitMultiset at hp hq
    rw [Multiset.mem_map] at hp hq
    obtain ⟨x, _, hx⟩ := hp
    obtain ⟨y, _, hy⟩ := hq
    rw [← hx, ← hy]
    have hxy : x ≠ y := by
      intro heq; apply hpq; rw [← hx, ← hy, heq]
    simp [hxy]

omit [LinearOrder α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **card**: `mergedInitMultiset Q a b` の cardinality は subtype `{y // y ≠ b}` の
要素数に等しい (= 各 leaf に 1 group). -/
lemma mergedInitMultiset_card
    (Q : Measure α) (a b : α) :
    (mergedInitMultiset Q a b).card = Fintype.card {y : α // y ≠ b} := by
  unfold mergedInitMultiset
  rw [Multiset.card_map]
  rfl

omit [LinearOrder α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **card (β-level)**: subtype の要素数を `Fintype.card α - 1` に書き換えた form.
`3 ≤ Fintype.card α` 前提下では `2 ≤ (mergedInitMultiset ...).card` が従い、
`huffmanLengthAux` の再帰 step が発火する (base case でない). -/
lemma mergedInitMultiset_card_eq_sub
    (Q : Measure α) (a b : α) :
    (mergedInitMultiset Q a b).card = Fintype.card α - 1 := by
  rw [mergedInitMultiset_card Q a b, Fintype.card_subtype_compl]
  simp

/-! ### Section B — primitive predicate -/

/-- **strictly-more-primitive genuine predicate**: `huffmanLengthAux` (= Huffman 再帰)
を **explicit な `mergedInitMultiset`** 上で評価した値の merge 恒等式.

原 `HuffmanMergedIdentificationHypothesis` から measure-theory 層 (`mergedMeasure` /
`Measure.real` / `initMultiset` の measure 計算) を完全に剥がした形. 残るのは pure な
Huffman 木の再帰 content のみ. これが本 seed が discharge を委ねる primitive.

@audit:retract-candidate(load-bearing-predicate) — `HuffmanWalls.merged_huffman_aux_ident_hypothesis_holds`
が wall lemma として未 discharge (`@residual(plan:huffman-strong-form-completion)`)。本
predicate を hypothesis に取る wrapper 群 (`huffmanLength_optimal_with_swap_and_aux` /
`huffmanLength_optimal_modulo_aux_ident`) は import cycle 回避のため signature 不変
(`huffman-sorry-migration-plan.md` 判断ログ #3)。後続 plan `huffman-strong-form-completion-plan`
完遂時に wall lemma を constructive に置換 + wrapper を signature 改変すれば本 predicate
は完全に削除可能。 -/
abbrev MergedHuffmanAuxIdentHypothesis : Prop :=
  ∀ {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q] (_hQ : ∀ a, 0 < Q.real {a})
    (_h_card : 3 ≤ Fintype.card β)
    (a b : β) (_hab : a ≠ b)
    (_h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (_h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (_h_sibling : huffmanLength Q a = huffmanLength Q b)
    (x : { y : β // y ≠ b }),
    huffmanLengthAux (mergedInitMultiset Q a b) x
      = (if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val)

/-! ### Section C — primitive ⟹ 原 hypothesis (完全証明) -/

/-- **vertical reduction の publish**: primitive predicate `MergedHuffmanAuxIdentHypothesis`
から原 `HuffmanMergedIdentificationHypothesis` を完全証明で導く. measure 層は
`initMultiset_mergedMeasure_eq` + `huffmanLength` の defeq 展開で完全に discharge.

注: `h_aux` は load-bearing hypothesis として消費されるが、body は constructive (`rw +
exact`)。本含意自体は genuine な reduction で sorry なし。consumer 側で
`HuffmanWalls.merged_huffman_aux_ident_hypothesis_holds` を渡せば
`HuffmanMergedIdentificationHypothesis` が transitive に得られる。closure 責任は
`HuffmanWalls.merged_huffman_aux_ident_hypothesis_holds` の
`@residual(plan:huffman-strong-form-completion)` が保有。 -/
theorem huffmanMergedIdentification_of_aux
    (h_aux : MergedHuffmanAuxIdentHypothesis.{u}) :
    HuffmanMergedIdentificationHypothesis.{u} := by
  intro β _ _ _ _ _ _ Q _ hQ h_card a b hab h_a_min h_b_min h_sibling x
  -- huffmanLength (mergedMeasure ...) x = huffmanLengthAux (initMultiset (mergedMeasure ...)) x  (defeq)
  -- = huffmanLengthAux (mergedInitMultiset Q a b) x  (by initMultiset_mergedMeasure_eq)
  show huffmanLengthAux (initMultiset (mergedMeasure Q a b hab)) x = _
  rw [initMultiset_mergedMeasure_eq Q a b hab]
  exact h_aux Q hQ h_card a b hab h_a_min h_b_min h_sibling x

/-! ### Section D — combined wrapper 再公開 (identification 半分を primitive で受ける) -/

/-- **`huffmanLength_optimal_with_hypotheses` の再公開**: identification hypothesis を
primitive `MergedHuffmanAuxIdentHypothesis` で受け取る form. swap normalization 半分
(`SwapNormalizationHypothesis`) はそのまま残る (本 seed の scope 外).

注: `h_swap` / `h_aux` は load-bearing hypothesis。本来は
`HuffmanWalls.swap_normalization_hypothesis_holds` /
`merged_huffman_aux_ident_hypothesis_holds` を呼ぶ形に書換べきだが、
`HuffmanWalls.lean → HuffmanStrongForm.lean → HuffmanMergedIdentBody.lean` の import chain
で循環するため signature 不変 (`huffman-sorry-migration-plan.md` 判断ログ #3 L-MIG-4 拡張)。
consumer 側で wall lemma を渡せば transitive に閉じる。

@residual(plan:huffman-strong-form-completion) -/
theorem huffmanLength_optimal_with_swap_and_aux
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (h_swap : SwapNormalizationHypothesis.{u})
    (h_aux : MergedHuffmanAuxIdentHypothesis.{u})
    (P : Measure β) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : β → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : β, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses h_swap
    (huffmanMergedIdentification_of_aux h_aux) P hP l hl_pos hl_kraft

end InformationTheory.Shannon.Huffman
