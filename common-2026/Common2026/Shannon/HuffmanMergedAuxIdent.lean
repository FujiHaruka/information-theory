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

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- relabel と `erase` は可換 (`relabelGroup e` の単射性経由). -/
lemma relabelMultiset_erase {γ : Type*} [DecidableEq γ] (e : α ↪ γ)
    (s : Multiset (Finset α × ℝ)) (p : Finset α × ℝ) :
    relabelMultiset e (s.erase p) = (relabelMultiset e s).erase (relabelGroup e p) := by
  unfold relabelMultiset
  exact Multiset.map_erase (relabelGroup e) (relabelGroup_injective e) p s

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- relabel は `mem` を反映 (単射性経由). -/
lemma relabelMultiset_mem {γ : Type*} [DecidableEq γ] (e : α ↪ γ)
    (s : Multiset (Finset α × ℝ)) (p : Finset α × ℝ) :
    relabelGroup e p ∈ relabelMultiset e s ↔ p ∈ s := by
  unfold relabelMultiset
  exact (Multiset.mem_map_of_injective (relabelGroup_injective e))

/-! ### Section B — no-ties tie-invariance (genuine, unconditional)

`s` の確率が pairwise distinct (`s.map Prod.snd` が Nodup) なら、`exists_min_image` の min は
**一意**で `Classical.choose` は forced。このとき `huffmanStep` の選択は relabel と可換になり、
`huffmanLengthAux` は carrier-embedding 越しに対応する。これが C3 (tie-invariance) の core。

これは genuine で unconditional な不変量だが、**`mergedInitMultiset` は一般に確率 tie を持つ**
(`Q{a}+Q{b}` が他 leaf と一致しうる) ため、本 lemma 単独では
`MergedHuffmanAuxIdentHypothesis` を閉じない (§file docstring の残タスク参照)。 -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **no-ties 下の min 一意性**: `s.map Prod.snd` が Nodup なら、`Multiset.exists_min_image`
の minimizer は一意 (確率値が distinct なので min を達成する group は唯一). -/
lemma min_unique_of_nodup_snd
    (s : Multiset (Finset α × ℝ)) (hnd : (s.map Prod.snd).Nodup)
    (p q : Finset α × ℝ) (hp : p ∈ s) (hq : q ∈ s)
    (hpmin : ∀ z ∈ s, p.2 ≤ z.2) (hqmin : ∀ z ∈ s, q.2 ≤ z.2) :
    p = q := by
  have hpq2 : p.2 = q.2 := le_antisymm (hpmin q hq) (hqmin p hp)
  -- nodup of map Prod.snd: distinct elements have distinct snd, so p.2 = q.2 ⇒ p = q
  exact Multiset.inj_on_of_nodup_map hnd p hp q hq hpq2

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- relabel は nodup-probs を保つ (`relabelMultiset_snd` で確率 multiset 不変). -/
lemma relabelMultiset_nodup_snd {γ : Type*} [DecidableEq γ] (e : α ↪ γ)
    (s : Multiset (Finset α × ℝ)) (hnd : (s.map Prod.snd).Nodup) :
    ((relabelMultiset e s).map Prod.snd).Nodup := by
  rw [relabelMultiset_snd]
  exact hnd

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **step-correspondence (1st selection)**: nodup-probs 下で、relabel した multiset の
`huffmanStep` 1st 選択は元の 1st 選択の relabel に等しい (両者とも一意 minimizer). -/
lemma huffmanStep_fst_relabel {γ : Type*} [DecidableEq γ] (e : α ↪ γ)
    (s : Multiset (Finset α × ℝ)) (hnd : (s.map Prod.snd).Nodup)
    (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    (hs' : 2 ≤ (relabelMultiset e s).card)
    (hg' : HuffmanGrouping (relabelMultiset e s)) :
    (huffmanStep (relabelMultiset e s) hs' hg').val.1
      = relabelGroup e ((huffmanStep s hs hg).val.1) := by
  -- LHS = unique min of relabel s.  RHS = relabel of min of s, also a min of relabel s.
  set p := (huffmanStep s hs hg).val.1 with hp_def
  set q := (huffmanStep (relabelMultiset e s) hs' hg').val.1 with hq_def
  -- p ∈ s, p is min of s
  have hp_mem : p ∈ s := (huffmanStep_spec s hs hg).1
  have hp_min : ∀ z ∈ s, p.2 ≤ z.2 := huffmanStep_min_fst s hs hg
  -- q ∈ relabel s, q is min of relabel s
  have hq_mem : q ∈ relabelMultiset e s := (huffmanStep_spec (relabelMultiset e s) hs' hg').1
  have hq_min : ∀ z ∈ relabelMultiset e s, q.2 ≤ z.2 :=
    huffmanStep_min_fst (relabelMultiset e s) hs' hg'
  -- relabelGroup e p ∈ relabel s and is a min (relabel preserves snd)
  have hrp_mem : relabelGroup e p ∈ relabelMultiset e s :=
    (relabelMultiset_mem e s p).mpr hp_mem
  have hrp_snd : (relabelGroup e p).2 = p.2 := rfl
  have hrp_min : ∀ z ∈ relabelMultiset e s, (relabelGroup e p).2 ≤ z.2 := by
    intro z hz
    -- z ∈ relabel s ⇒ z = relabelGroup e z' for some z' ∈ s
    unfold relabelMultiset at hz
    rw [Multiset.mem_map] at hz
    obtain ⟨z', hz', hzz'⟩ := hz
    rw [← hzz', hrp_snd]
    show p.2 ≤ (relabelGroup e z').2
    exact hp_min z' hz'
  -- nodup probs of relabel s
  have hnd' : ((relabelMultiset e s).map Prod.snd).Nodup :=
    relabelMultiset_nodup_snd e s hnd
  -- q = relabelGroup e p by uniqueness
  exact min_unique_of_nodup_snd (relabelMultiset e s) hnd' q (relabelGroup e p)
    hq_mem hrp_mem hq_min hrp_min

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- nodup-probs は `erase` で保たれる (sub-multiset の Nodup). -/
lemma nodup_snd_erase
    (s : Multiset (Finset α × ℝ)) (hnd : (s.map Prod.snd).Nodup) (p : Finset α × ℝ) :
    ((s.erase p).map Prod.snd).Nodup := by
  have hle : (s.erase p).map Prod.snd ≤ s.map Prod.snd :=
    Multiset.map_le_map (Multiset.erase_le p s)
  exact Multiset.nodup_of_le hle hnd

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **step-correspondence (2nd selection)**: nodup-probs 下で relabel した multiset の
`huffmanStep` 2nd 選択は元の 2nd 選択の relabel に等しい. -/
lemma huffmanStep_snd_relabel {γ : Type*} [DecidableEq γ] (e : α ↪ γ)
    (s : Multiset (Finset α × ℝ)) (hnd : (s.map Prod.snd).Nodup)
    (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    (hs' : 2 ≤ (relabelMultiset e s).card)
    (hg' : HuffmanGrouping (relabelMultiset e s)) :
    (huffmanStep (relabelMultiset e s) hs' hg').val.2.1
      = relabelGroup e ((huffmanStep s hs hg).val.2.1) := by
  set p := (huffmanStep s hs hg).val.2.1 with hp_def
  set q := (huffmanStep (relabelMultiset e s) hs' hg').val.2.1 with hq_def
  -- 1st selections correspond
  have h1 := huffmanStep_fst_relabel e s hnd hs hg hs' hg'
  -- p ∈ s.erase (huffmanStep s).val.1, p min of that
  have hp_mem : p ∈ s.erase (huffmanStep s hs hg).val.1 := (huffmanStep_spec s hs hg).2.1
  have hp_min : ∀ z ∈ s.erase (huffmanStep s hs hg).val.1, p.2 ≤ z.2 :=
    huffmanStep_min_snd s hs hg
  -- q ∈ relabel(s).erase (huffmanStep relabel).val.1, q min of that
  have hq_mem : q ∈ (relabelMultiset e s).erase (huffmanStep (relabelMultiset e s) hs' hg').val.1 :=
    (huffmanStep_spec (relabelMultiset e s) hs' hg').2.1
  have hq_min : ∀ z ∈ (relabelMultiset e s).erase
      (huffmanStep (relabelMultiset e s) hs' hg').val.1, q.2 ≤ z.2 :=
    huffmanStep_min_snd (relabelMultiset e s) hs' hg'
  -- the erased multiset on the relabel side equals relabel of (s.erase (huffmanStep s).val.1)
  have h_erase_eq : (relabelMultiset e s).erase (huffmanStep (relabelMultiset e s) hs' hg').val.1
      = relabelMultiset e (s.erase (huffmanStep s hs hg).val.1) := by
    rw [h1, relabelMultiset_erase]
  -- nodup probs of the erased multiset (relabel side)
  have hnd_er : (((relabelMultiset e s).erase
      (huffmanStep (relabelMultiset e s) hs' hg').val.1).map Prod.snd).Nodup :=
    nodup_snd_erase (relabelMultiset e s) (relabelMultiset_nodup_snd e s hnd) _
  -- relabelGroup e p ∈ erased multiset (relabel side) and is a min
  have hrp_mem : relabelGroup e p ∈ (relabelMultiset e s).erase
      (huffmanStep (relabelMultiset e s) hs' hg').val.1 := by
    rw [h_erase_eq]
    exact (relabelMultiset_mem e (s.erase (huffmanStep s hs hg).val.1) p).mpr hp_mem
  have hrp_min : ∀ z ∈ (relabelMultiset e s).erase
      (huffmanStep (relabelMultiset e s) hs' hg').val.1, (relabelGroup e p).2 ≤ z.2 := by
    intro z hz
    rw [h_erase_eq] at hz
    unfold relabelMultiset at hz
    rw [Multiset.mem_map] at hz
    obtain ⟨z', hz', hzz'⟩ := hz
    rw [← hzz']
    show p.2 ≤ (relabelGroup e z').2
    exact hp_min z' hz'
  exact min_unique_of_nodup_snd _ hnd_er q (relabelGroup e p) hq_mem hrp_mem hq_min hrp_min

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **step-output multiset correspondence**: nodup-probs 下で relabel した multiset の
`huffmanStep` 出力 (残木 `.val.2.2`) は元の出力の relabel に等しい. step 選択の対応
(`huffmanStep_fst/snd_relabel`) + merged group の relabel + erase の relabel 可換から. -/
lemma huffmanStep_step_relabel {γ : Type*} [DecidableEq γ] (e : α ↪ γ)
    (s : Multiset (Finset α × ℝ)) (hnd : (s.map Prod.snd).Nodup)
    (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    (hs' : 2 ≤ (relabelMultiset e s).card)
    (hg' : HuffmanGrouping (relabelMultiset e s)) :
    (huffmanStep (relabelMultiset e s) hs' hg').val.2.2
      = relabelMultiset e ((huffmanStep s hs hg).val.2.2) := by
  -- shapes
  obtain ⟨_, _, hshape_s, _⟩ := huffmanStep_spec s hs hg
  obtain ⟨_, _, hshape_rs, _⟩ := huffmanStep_spec (relabelMultiset e s) hs' hg'
  -- step selections correspond
  have h1 := huffmanStep_fst_relabel e s hnd hs hg hs' hg'
  have h2 := huffmanStep_snd_relabel e s hnd hs hg hs' hg'
  -- rewrite the relabel-side shape, then both step selections by correspondence
  rw [hshape_rs, h1, h2, hshape_s]
  -- relabelMultiset of a cons: distribute (relabelMultiset = map (relabelGroup e))
  show _ = ((((huffmanStep s hs hg).val.1.1 ∪ (huffmanStep s hs hg).val.2.1.1,
      (huffmanStep s hs hg).val.1.2 + (huffmanStep s hs hg).val.2.1.2) ::ₘ
      ((s.erase (huffmanStep s hs hg).val.1).erase
        (huffmanStep s hs hg).val.2.1))).map (relabelGroup e)
  rw [Multiset.map_cons]
  congr 1
  · -- merged group: relabelGroup e of (x1.1 ∪ x2.1, x1.2 + x2.2)
    unfold relabelGroup
    simp only [Prod.mk.injEq, and_true]
    rw [Finset.map_union]
  · -- erase erase parts: (relabel(s).erase rx1).erase rx2 = relabel(ee)
    show ((relabelMultiset e s).erase (relabelGroup e (huffmanStep s hs hg).val.1)).erase
        (relabelGroup e (huffmanStep s hs hg).val.2.1)
      = ((s.erase (huffmanStep s hs hg).val.1).erase
          (huffmanStep s hs hg).val.2.1).map (relabelGroup e)
    rw [← relabelMultiset_erase, ← relabelMultiset_erase]
    rfl

end InformationTheory.Shannon.Huffman
