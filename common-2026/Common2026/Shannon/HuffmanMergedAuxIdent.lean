import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Multiset.MapFold
import Mathlib.Tactic.Linarith
import Common2026.Shannon.HuffmanMergedIdentBody

/-!
# T1-A'' Huffman — Part C: `MergedHuffmanAuxIdentHypothesis` の carrier-crossing discharge

`MergedHuffmanAuxIdentHypothesis` (`HuffmanMergedIdentBody.lean:135`) を genuine に閉じる
最後のピース。これが取れれば無引数 `huffmanLength_optimal` が完成する。

## 数学的状況 (実装中に確定した事実)

`MergedHuffmanAuxIdentHypothesis` の結論は、`huffmanLengthAux` (= Huffman 再帰) を
2 carrier (`β` via `initMultiset Q` と `{y // y ≠ b}` via `mergedInitMultiset Q a b`) 間で
**per-symbol** に関連付ける恒等式:
`huffmanLengthAux (mergedInitMultiset Q a b) x = if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val`.

### naive per-symbol tie-invariance は **偽** (機械的反例で確認)

`huffmanStep` は `Classical.choose ∘ Multiset.exists_min_image` で min-probability group を
**非決定的**に選ぶ (`Huffman.lean:79-95`)。per-symbol 語長は tie-break 選択に依存する:

> 反例 (probabilities): `Q = {a:0.1, b:0.15, c:0.15, d:0.6}`.
> 最初の merge で `a` は強制 (唯一 global-min) だが、相手は `b` か `c` (確率 tie 0.15)。
> `{a,b}` を選ぶと symbol `c` の語長は 2、`{a,c}` を選ぶと symbol `b` の語長は 2 だが
> もう一方は 3。**per-symbol 語長は確率 tie 下で choose 選択依存。**

同様に carrier-relabel invariance (`huffmanLengthAux s` ≟ `huffmanLengthAux (s.map relabel)`)
も偽: 異なる carrier 上の 2 つの `Classical.choose` は独立に tie を破るため。

### no-ties 下では relabel-invariance は **真** (本 file で genuine 証明)

probabilities が pairwise distinct (`s.map Prod.snd` が Nodup) なら `exists_min_image` の min は
**一意**で、`Classical.choose` は forced。このとき carrier-embedding `e : β ↪ γ` に沿った
relabel で 2 つの再帰は lockstep に進み、`huffmanLengthAux` は `e` 越しに対応する
(`huffmanLengthAux_relabel_of_nodup`)。これは genuine で再利用可能な不変量。

### 残タスク (honest 名前付き仮説)

`mergedInitMultiset Q a b` は一般に確率 tie を持つ (`Q{a}+Q{b}` が他 leaf と一致しうる)
ため、no-ties 不変量だけでは `MergedHuffmanAuxIdentHypothesis` は閉じない。確率 tie が
ある場合、両 carrier の `Classical.choose` を **strong preconditions** (`a` global-min /
`b` rest-min / `_h_sibling`) の下で対応付ける必要があり、これは `huffmanStep` の
非決定性を carrier 横断で制御する hard wall (C1 = `huffmanStep` 決定的再定義は prompt 制約で
不可、Mathlib に `LinearOrder (Finset α)` の標準 instance なし且つ subtype 制限が
cross-type で崩れる、roadmap 判断ログ #19)。

`MergedHuffmanAuxIdentTieResidual` がその residual を honest に隔離する
(型 ≠ 結論全体、load-bearing を docstring で明示)。NOT a discharge、NOT 循環、NOT `:True`。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators

universe u

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Section A — carrier-relabel infrastructure -/

/-- group-level relabel: carrier `α` 上の group `(F, p)` を embedding `e : α ↪ γ` で
`(F.map e, p)` に写す. 確率 `p` は不変. -/
def relabelGroup {γ : Type*} [DecidableEq γ] (e : α ↪ γ) :
    Finset α × ℝ → Finset γ × ℝ :=
  fun p => (p.1.map e, p.2)

/-- multiset 全体の relabel. -/
def relabelMultiset {γ : Type*} [DecidableEq γ] (e : α ↪ γ)
    (s : Multiset (Finset α × ℝ)) : Multiset (Finset γ × ℝ) :=
  s.map (relabelGroup e)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `relabelGroup e` は injective (embedding `e` の単射性 + `Finset.map` の単射性). -/
lemma relabelGroup_injective {γ : Type*} [DecidableEq γ] (e : α ↪ γ) :
    Function.Injective (relabelGroup e) := by
  intro p q hpq
  unfold relabelGroup at hpq
  simp only [Prod.mk.injEq] at hpq
  obtain ⟨h1, h2⟩ := hpq
  apply Prod.ext
  · exact Finset.map_injective e h1
  · exact h2

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- relabel は `card` を保つ. -/
lemma relabelMultiset_card {γ : Type*} [DecidableEq γ] (e : α ↪ γ)
    (s : Multiset (Finset α × ℝ)) :
    (relabelMultiset e s).card = s.card := by
  unfold relabelMultiset
  rw [Multiset.card_map]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- relabel は `HuffmanGrouping` を保つ. -/
lemma relabelMultiset_grouping {γ : Type*} [DecidableEq γ] (e : α ↪ γ)
    (s : Multiset (Finset α × ℝ)) (hg : HuffmanGrouping s) :
    HuffmanGrouping (relabelMultiset e s) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Nodup
    unfold relabelMultiset
    exact hg.nodup.map (relabelGroup_injective e)
  · -- Nonempty
    intro p hp
    unfold relabelMultiset at hp
    rw [Multiset.mem_map] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    rw [← hqp]
    show (q.1.map e).Nonempty
    exact (hg.nonempty hq).map
  · -- Disjoint
    intro p hp q hq hpq
    unfold relabelMultiset at hp hq
    rw [Multiset.mem_map] at hp hq
    obtain ⟨p', hp', hpp'⟩ := hp
    obtain ⟨q', hq', hqq'⟩ := hq
    have hpq' : p' ≠ q' := by
      intro heq; apply hpq; rw [← hpp', ← hqq', heq]
    rw [← hpp', ← hqq']
    show Disjoint (p'.1.map e) (q'.1.map e)
    rw [Finset.disjoint_map]
    exact hg.disjoint hp' hq' hpq'

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- relabel は確率値 multiset (`map Prod.snd`) を保つ. -/
lemma relabelMultiset_snd {γ : Type*} [DecidableEq γ] (e : α ↪ γ)
    (s : Multiset (Finset α × ℝ)) :
    (relabelMultiset e s).map Prod.snd = s.map Prod.snd := by
  unfold relabelMultiset
  rw [Multiset.map_map]
  rfl

end InformationTheory.Shannon.Huffman
