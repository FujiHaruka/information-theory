import Common2026.Shannon.HuffmanColexDeterminism

/-!
# T1-A'' Huffman — first-step identification PROBE (go/no-go for 案 A)

PROBE only. 目的: 決定的 `huffmanStep (initMultiset Q)` が、`MergedHuffmanAuxIdentHypothesis`
で外から与えられる `a` (`_h_a_min` = global-min) / `b` (`_h_b_min` = rest-min) /
`_h_sibling` の pair を **実際に first-merge する** ことを示せるか probe する。

## PROBE 結果 (確定)

**first-step identification は `∀ a b` 仮説では FALSE** (`chosen_le_given` で genuine 証明):
決定的 first 選択 `a*` は `(Q{·}, ·)` の lex-min (= prob-min かつ tie 時は `α`-最小;
`huffmanStep_initMultiset_fst_isLexMin` で genuine 証明)。与えられた `a` は `_h_a_min` で
prob-min と固定されるが、tie 時の `α`-order 位置は固定されないため `astar ≤ a` のみ従い、
`a = astar` は一般に偽。よって「決定的 step が given a,b を merge する」案 A の route は no-go。

**しかし merged-length identity 自体は TRUE** (手計算で確認、反例なし)。鍵は `_h_sibling`:
等語長 ⇒ `a, b` は同 depth の sibling であり、sibling pair を 1 leaf に collapse すると
**merge order に依らず** depth が 1 減る。よって正しい discharge route は first-step
identification ではなく **sibling-driven collapse** (確率 multiset で depth が決まる Huffman
性質、`HuffmanColexDeterminism.huffmanLengthAux_relabel_det` を部品に)。これは案 A(2) の
collapse 本体に相当し、moonshot 寄り (roadmap #19 追記4 の B 寄り)。

このファイルは probe 結果の genuine な記録 (lex-min 特性 + first-step 不可能性) のみを残す。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators Colex

universe u

variable {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### colex on singletons -/

/-- `initMultiset Q` の決定的 first 選択は `({a*}, Q{a*})` の形 (singleton)。 -/
lemma huffmanStep_initMultiset_fst_singleton
    (Q : Measure α) (h_card : 2 ≤ Fintype.card α) :
    ∃ a : α, (huffmanStep (initMultiset Q)
        (by rw [show (initMultiset Q).card = Fintype.card α by
              unfold initMultiset; rw [Multiset.card_map]; rfl]; exact h_card)
        (initMultiset_huffmanGrouping Q)).val.1 = ({a}, Q.real {a}) := by
  have hcard : 2 ≤ (initMultiset Q).card := by
    rw [show (initMultiset Q).card = Fintype.card α by
      unfold initMultiset; rw [Multiset.card_map]; rfl]; exact h_card
  have hmem := (huffmanStep_spec (initMultiset Q) hcard (initMultiset_huffmanGrouping Q)).1
  unfold initMultiset at hmem
  rw [Multiset.mem_map] at hmem
  obtain ⟨a, _, hae⟩ := hmem
  exact ⟨a, hae.symm⟩

/-- **PROBE 中核**: 決定的 first 選択 `a*` は、`(Q{·}, ·)` を lex-最小化する一意の元。
すなわち `∀ c, Q{a*} ≤ Q{c}` かつ「`Q{a*} = Q{c}` なら `a* ≤ c`」。 -/
lemma huffmanStep_initMultiset_fst_isLexMin
    (Q : Measure α) (h_card : 2 ≤ Fintype.card α) (a : α)
    (hfst : (huffmanStep (initMultiset Q)
        (by rw [show (initMultiset Q).card = Fintype.card α by
              unfold initMultiset; rw [Multiset.card_map]; rfl]; exact h_card)
        (initMultiset_huffmanGrouping Q)).val.1 = ({a}, Q.real {a})) :
    ∀ c, (Q.real {a} < Q.real {c}) ∨ (Q.real {a} = Q.real {c} ∧ a ≤ c) := by
  intro c
  have hg := initMultiset_huffmanGrouping Q
  have hcard : 2 ≤ (initMultiset Q).card := by
    rw [show (initMultiset Q).card = Fintype.card α by
      unfold initMultiset; rw [Multiset.card_map]; rfl]; exact h_card
  -- ({c}, Q{c}) ∈ initMultiset Q
  have hc_mem : ({c}, Q.real {c}) ∈ initMultiset Q := by
    unfold initMultiset; rw [Multiset.mem_map]; exact ⟨c, Finset.mem_univ _, rfl⟩
  -- groupKey of fst ≤ groupKey of ({c}, Q{c})
  have hkey := huffmanStep_key_min_fst (initMultiset Q) hcard hg ({c}, Q.real {c}) hc_mem
  rw [hfst] at hkey
  -- groupKey ({a}, Q{a}) = toLex (Q{a}, toColex {a}); same for c
  unfold groupKey at hkey
  rw [Prod.Lex.le_iff] at hkey
  simp only [ofLex_toLex] at hkey
  rcases hkey with hlt | ⟨h1, h2⟩
  · exact Or.inl hlt
  · refine Or.inr ⟨h1, ?_⟩
    rwa [Finset.Colex.singleton_le_singleton] at h2

/-- **PROBE verdict — 取れる最良の含意 (genuine)**: 与えられた prob-global-min `a`
(`∀ c, Q{a} ≤ Q{c}`) と決定的 first-merge 元 `astar` (lex-min) について、
**`astar ≤ a` のみ** が従う。`a = astar` は **従わない**:
`h_a_min` は `a` を prob で min と固定するだけで、確率 tie 時の `α`-order 上の位置は
固定しない。決定的 step は tie を colex (= singleton では `α`-order) で破り `α`-最小の
prob-min を選ぶため、`a` が `α`-最小でないなら `astar < a` (strict) が起こりうる。

これが案 A の first-step identification が **`∀ a b` 仮説では閉じない** 構造的理由。
docstring: NOT a discharge — `a = astar` は意図的に証明しない (一般には偽)。 -/
lemma chosen_le_given
    (Q : Measure α) (a astar : α)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (hstar_lexmin : ∀ c, (Q.real {astar} < Q.real {c}) ∨
        (Q.real {astar} = Q.real {c} ∧ astar ≤ c)) :
    astar ≤ a := by
  rcases hstar_lexmin a with hlt | ⟨_, hle⟩
  · exact absurd (h_a_min astar) (not_le.mpr hlt)
  · exact hle

end InformationTheory.Shannon.Huffman
