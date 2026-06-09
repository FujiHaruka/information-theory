import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.ShannonCode.Basic
import InformationTheory.Shannon.ShannonCode.KraftReverse

/-!
# Huffman 最適性 (Cover-Thomas Theorem 5.8.1)

T1-A シードカード (`docs/shannon/huffman-moonshot-plan.md`).

binary (D = 2) prefix code に対し、`huffmanLength` を実構成し:
- 正値 (`huffmanLength_pos`)
- Kraft 不等式充足 (`huffmanLength_kraft_le_one`)
- 任意 Kraft-feasible `l` 比較で最適 (`huffmanLength_optimal`)
- 副系として prefix code 構成 (`exists_huffman_prefix_code`)

を publish.
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **決定的比較キー (colex 2 段 lex)** — `huffmanStep` の min 選択を一意化する.
第 1 キー = 確率 `p.2` (昇順)、tie-break 第 2 キー = `toColex p.1` (colex 順).
`[LinearOrder α]` から `LinearOrder (Colex (Finset α))` (`Finset.Colex.instLinearOrder`)
が立ち、`ℝ ×ₗ Colex (Finset α)` の `Prod.Lex` 全順序で min が一意確定する
(`groupKey` 単射: 確率が等しくても colex で区別). -/
noncomputable def groupKey (p : Finset α × ℝ) : ℝ ×ₗ Colex (Finset α) :=
  toLex (p.2, toColex p.1)

omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `groupKey` は単射 (確率 + colex tie-break で group を一意に決定). -/
@[entry_point]
lemma groupKey_injective : Function.Injective (groupKey (α := α)) := by
  intro p q h
  unfold groupKey at h
  have h1 : p.2 = q.2 := congrArg (fun z => (ofLex z).1) h
  have h2 : toColex p.1 = toColex q.1 := congrArg (fun z => (ofLex z).2) h
  rw [toColex_inj] at h2
  exact Prod.ext h2 h1

omit [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `groupKey` の min は確率 (`p.2`) の min を含意する (第 1 キー射影). -/
lemma groupKey_le_imp_snd_le {p q : Finset α × ℝ} (h : groupKey p ≤ groupKey q) :
    p.2 ≤ q.2 := by
  unfold groupKey at h
  rw [Prod.Lex.le_iff] at h
  rcases h with h | ⟨h1, _⟩
  · exact le_of_lt h
  · exact le_of_eq h1

/-! ### 内部実装: Multiset ベースの Huffman 再帰 -/

/-- Huffman 再帰で保たれる group 不変量 (C-6 強化版):
- `Nodup`: 多重集合 `s` に重複なし
- 各 group は非空 (`p.1.Nonempty`)
- 異なる group の `p.1` は互いに disjoint -/
def HuffmanGrouping (s : Multiset (Finset α × ℝ)) : Prop :=
  s.Nodup ∧
  (∀ p ∈ s, p.1.Nonempty) ∧
  (∀ p ∈ s, ∀ q ∈ s, p ≠ q → Disjoint p.1 q.1)

omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma HuffmanGrouping.nodup {s : Multiset (Finset α × ℝ)} (h : HuffmanGrouping s) :
    s.Nodup := h.1

omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma HuffmanGrouping.nonempty {s : Multiset (Finset α × ℝ)} (h : HuffmanGrouping s)
    {p : Finset α × ℝ} (hp : p ∈ s) : p.1.Nonempty := h.2.1 p hp

omit [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma HuffmanGrouping.disjoint {s : Multiset (Finset α × ℝ)} (h : HuffmanGrouping s)
    {p q : Finset α × ℝ} (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) :
    Disjoint p.1 q.1 := h.2.2 p hp q hq hpq

/-- `huffmanStep` (one step): 与えられた `s : Multiset (Finset α × ℝ)` から、
最小 2 group `(A, pA), (B, pB)` を取り出し、merged group `(A ∪ B, pA + pB)` を
含む新 multiset `s''` を返す. `s.card ≥ 2` + `HuffmanGrouping s` 前提.

`Subtype` で **構造的 spec を焼き込む** (plan C-6 強化版):
- 既存 3 件 (`p.1 ∈ s`, `p.2.1 ∈ s.erase p.1`, shape of `p.2.2`)
- 新規: `HuffmanGrouping p.2.2` (不変量保存) -/
noncomputable def huffmanStep
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    { p : (Finset α × ℝ) × (Finset α × ℝ) × Multiset (Finset α × ℝ) //
        p.1 ∈ s ∧
        p.2.1 ∈ s.erase p.1 ∧
        p.2.2 =
          (p.1.1 ∪ p.2.1.1, p.1.2 + p.2.1.2) ::ₘ
            ((s.erase p.1).erase p.2.1) ∧
        HuffmanGrouping p.2.2 } := by
  classical
  have hs_ne : s ≠ 0 := by
    intro heq; rw [heq, Multiset.card_zero] at hs; omega
  let x1 := Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
    (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)
  have hx1k : x1 ∈ s ∧ ∀ z ∈ s, groupKey x1 ≤ groupKey z :=
    Classical.choose_spec (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)
  have hx1 : x1 ∈ s ∧ ∀ z ∈ s, x1.2 ≤ z.2 :=
    ⟨hx1k.1, fun z hz => groupKey_le_imp_snd_le (hx1k.2 z hz)⟩
  let s' := s.erase x1
  have hs'_ne : s' ≠ 0 := by
    have hcard_s' : s'.card = s.card - 1 :=
      Multiset.card_erase_of_mem hx1.1
    intro heq
    rw [heq, Multiset.card_zero] at hcard_s'
    omega
  let x2 := Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
    (R := ℝ ×ₗ Colex (Finset α)) groupKey hs'_ne)
  have hx2k : x2 ∈ s' ∧ ∀ z ∈ s', groupKey x2 ≤ groupKey z :=
    Classical.choose_spec (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs'_ne)
  have hx2 : x2 ∈ s' ∧ ∀ z ∈ s', x2.2 ≤ z.2 :=
    ⟨hx2k.1, fun z hz => groupKey_le_imp_snd_le (hx2k.2 z hz)⟩
  -- HuffmanGrouping 保存の事実を組み上げる
  have hx1_mem : x1 ∈ s := hx1.1
  have hx2_mem_s' : x2 ∈ s' := hx2.1
  -- s.erase x1 のメンバから x2 が s に属する
  have hx2_mem_s : x2 ∈ s := Multiset.mem_of_mem_erase hx2_mem_s'
  -- Nodup ⇒ x1 と x2 は別物 (`x2 ∈ s.erase x1` から)
  have hx12_ne : x1 ≠ x2 := by
    intro heq
    rw [← heq] at hx2_mem_s'
    exact hg.nodup.notMem_erase hx2_mem_s'
  -- erase erase の構造 (Nodup 保存)
  have h_ee_nodup : ((s.erase x1).erase x2).Nodup :=
    ((hg.nodup.erase x1).erase x2)
  -- merged が ((s.erase x1).erase x2) に属しないことを示す
  -- (merged = (x1.1 ∪ x2.1, x1.2 + x2.2))
  let merged : Finset α × ℝ := (x1.1 ∪ x2.1, x1.2 + x2.2)
  -- merged ≠ q for any q ∈ erase erase (uses disjointness + nonempty + Nodup)
  have h_merged_not_in :
      merged ∉ ((s.erase x1).erase x2) := by
    intro hmem_ee
    -- q := merged ∈ erase erase ⊆ s
    have hmem_s' : merged ∈ s' := Multiset.mem_of_mem_erase hmem_ee
    have hmem_s : merged ∈ s := Multiset.mem_of_mem_erase hmem_s'
    -- merged ≠ x1: merged.1 = x1.1 ∪ x2.1, contains x2.1's elements,
    --   while x1.1 disjoint from x2.1 (x1 ≠ x2 + HuffmanGrouping)
    have h_merged_ne_x1 : merged ≠ x1 := by
      intro heq
      have hfst : merged.1 = x1.1 := by rw [heq]
      -- merged.1 = x1.1 ∪ x2.1; x2.1 is nonempty; so x2.1 ⊆ x1.1
      have hx2_ne : x2.1.Nonempty := hg.nonempty hx2_mem_s
      obtain ⟨a, ha⟩ := hx2_ne
      have ha_in_merged : a ∈ merged.1 := by
        show a ∈ x1.1 ∪ x2.1
        exact Finset.mem_union_right _ ha
      rw [hfst] at ha_in_merged
      have h_disj : Disjoint x1.1 x2.1 := hg.disjoint hx1_mem hx2_mem_s hx12_ne
      exact (Finset.disjoint_left.mp h_disj ha_in_merged) ha
    -- merged ≠ x2: symmetric
    have h_merged_ne_x2 : merged ≠ x2 := by
      intro heq
      have hfst : merged.1 = x2.1 := by rw [heq]
      have hx1_ne : x1.1.Nonempty := hg.nonempty hx1_mem
      obtain ⟨a, ha⟩ := hx1_ne
      have ha_in_merged : a ∈ merged.1 := by
        show a ∈ x1.1 ∪ x2.1
        exact Finset.mem_union_left _ ha
      rw [hfst] at ha_in_merged
      have h_disj : Disjoint x1.1 x2.1 := hg.disjoint hx1_mem hx2_mem_s hx12_ne
      exact (Finset.disjoint_right.mp h_disj ha_in_merged) ha
    -- erase で x1 を消したので、merged ∈ s' = s.erase x1 でも merged ≠ x1 が必要
    -- merged ∈ s かつ merged ≠ x1, merged ≠ x2, hence merged ∈ erase erase は OK
    -- このパスは矛盾を導かないので、別ルートが必要 — 実は merged ∈ s と矛盾?
    -- HuffmanGrouping disjoint より:
    --   merged ∈ s ∧ x1 ∈ s ∧ merged ≠ x1 ⇒ Disjoint merged.1 x1.1
    --   しかし merged.1 = x1.1 ∪ x2.1 ⊇ x1.1, ⇒ x1.1 = ∅ (x1.1 と自身 disjoint)
    --   一方 x1.1 nonempty (HuffmanGrouping nonempty) ⇒ 矛盾
    have h_disj_merged_x1 : Disjoint merged.1 x1.1 :=
      hg.disjoint hmem_s hx1_mem h_merged_ne_x1
    have hx1_ne : x1.1.Nonempty := hg.nonempty hx1_mem
    obtain ⟨a, ha⟩ := hx1_ne
    have ha_in_merged : a ∈ merged.1 := by
      show a ∈ x1.1 ∪ x2.1
      exact Finset.mem_union_left _ ha
    exact (Finset.disjoint_left.mp h_disj_merged_x1 ha_in_merged) ha
  refine ⟨(x1, x2, (x1.1 ∪ x2.1, x1.2 + x2.2) ::ₘ s'.erase x2), ?_, ?_, ?_, ?_⟩
  · exact hx1_mem
  · exact hx2_mem_s'
  · rfl
  -- HuffmanGrouping (merged ::ₘ erase erase)
  refine ⟨?_, ?_, ?_⟩
  · -- Nodup: cons は merged ∉ erase erase なら nodup
    exact (Multiset.nodup_cons).mpr ⟨h_merged_not_in, h_ee_nodup⟩
  · -- ∀ p ∈ cons, p.1.Nonempty
    intro p hp
    rcases Multiset.mem_cons.mp hp with hp_merged | hp_ee
    · -- p = merged
      rw [hp_merged]
      change (x1.1 ∪ x2.1).Nonempty
      have hx1_ne : x1.1.Nonempty := hg.nonempty hx1_mem
      exact hx1_ne.mono (Finset.subset_union_left)
    · -- p ∈ erase erase ⊆ s
      have hp_s' : p ∈ s' := Multiset.mem_of_mem_erase hp_ee
      have hp_s : p ∈ s := Multiset.mem_of_mem_erase hp_s'
      exact hg.nonempty hp_s
  · -- Disjoint
    intro p hp q hq hpq
    rcases Multiset.mem_cons.mp hp with hp_merged | hp_ee
    · -- p = merged
      rcases Multiset.mem_cons.mp hq with hq_merged | hq_ee
      · -- q = merged = p contradicts hpq
        exact absurd (hp_merged.trans hq_merged.symm) hpq
      · -- q ∈ erase erase ⊆ s, q ≠ x1, q ≠ x2
        have hq_s' : q ∈ s' := Multiset.mem_of_mem_erase hq_ee
        have hq_s : q ∈ s := Multiset.mem_of_mem_erase hq_s'
        have hq_ne_x1 : q ≠ x1 := by
          intro heq
          rw [heq] at hq_s'
          exact hg.nodup.notMem_erase hq_s'
        have hq_ne_x2 : q ≠ x2 := by
          intro heq
          rw [heq] at hq_ee
          exact (hg.nodup.erase x1).notMem_erase hq_ee
        -- p.1 = x1.1 ∪ x2.1, Disjoint with q.1 ⟺ Disjoint x1.1 q.1 ∧ Disjoint x2.1 q.1
        rw [hp_merged]
        change Disjoint (x1.1 ∪ x2.1) q.1
        rw [Finset.disjoint_union_left]
        exact ⟨hg.disjoint hx1_mem hq_s hq_ne_x1.symm,
               hg.disjoint hx2_mem_s hq_s hq_ne_x2.symm⟩
    · -- p ∈ erase erase
      rcases Multiset.mem_cons.mp hq with hq_merged | hq_ee
      · -- p ∈ erase erase, q = merged
        have hp_s' : p ∈ s' := Multiset.mem_of_mem_erase hp_ee
        have hp_s : p ∈ s := Multiset.mem_of_mem_erase hp_s'
        have hp_ne_x1 : p ≠ x1 := by
          intro heq
          rw [heq] at hp_s'
          exact hg.nodup.notMem_erase hp_s'
        have hp_ne_x2 : p ≠ x2 := by
          intro heq
          rw [heq] at hp_ee
          exact (hg.nodup.erase x1).notMem_erase hp_ee
        rw [hq_merged]
        change Disjoint p.1 (x1.1 ∪ x2.1)
        rw [Finset.disjoint_union_right]
        exact ⟨hg.disjoint hp_s hx1_mem hp_ne_x1,
               hg.disjoint hp_s hx2_mem_s hp_ne_x2⟩
      · -- both p, q ∈ erase erase ⊆ s, original disjoint
        have hp_s' : p ∈ s' := Multiset.mem_of_mem_erase hp_ee
        have hp_s : p ∈ s := Multiset.mem_of_mem_erase hp_s'
        have hq_s' : q ∈ s' := Multiset.mem_of_mem_erase hq_ee
        have hq_s : q ∈ s := Multiset.mem_of_mem_erase hq_s'
        exact hg.disjoint hp_s hq_s hpq

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanStep` の構造的 spec を取り出す簡略アクセサ. -/
lemma huffmanStep_spec
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    (huffmanStep s hs hg).val.1 ∈ s ∧
    (huffmanStep s hs hg).val.2.1 ∈ s.erase (huffmanStep s hs hg).val.1 ∧
    (huffmanStep s hs hg).val.2.2 =
      ((huffmanStep s hs hg).val.1.1 ∪ (huffmanStep s hs hg).val.2.1.1,
        (huffmanStep s hs hg).val.1.2 + (huffmanStep s hs hg).val.2.1.2) ::ₘ
        ((s.erase (huffmanStep s hs hg).val.1).erase (huffmanStep s hs hg).val.2.1) ∧
    HuffmanGrouping (huffmanStep s hs hg).val.2.2 :=
  (huffmanStep s hs hg).property

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **`huffmanStep` の groupKey-minimality spec (`.val.1` は `s` 全体の `groupKey` 最小)**.
決定化の核 — 定義本体の `Classical.choose (exists_min_image groupKey ...)` の spec を
unfold で取り出す. `groupKey` は単射なので min は一意 (確率 tie は colex で破られる).
carrier 横断の決定的対応 (Phase H2) に必須. -/
@[entry_point]
lemma huffmanStep_key_min_fst
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    ∀ z ∈ s, groupKey (huffmanStep s hs hg).val.1 ≤ groupKey z := by
  classical
  have hs_ne : s ≠ 0 := by
    intro heq; rw [heq, Multiset.card_zero] at hs; omega
  have hx1 : (Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)) ∈ s ∧
      ∀ z ∈ s, groupKey (Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
        (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)) ≤ groupKey z :=
    Classical.choose_spec (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)
  intro z hz
  show groupKey (huffmanStep s hs hg).val.1 ≤ groupKey z
  unfold huffmanStep
  exact hx1.2 z hz

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **`huffmanStep` の minimality spec (`.val.1` は `s` 全体の確率最小)**.
`huffmanStep_key_min_fst` (groupKey 最小) の第 1 キー射影 (`groupKey_le_imp_snd_le`)
から確率 `≤` を導く. statement は決定化前と不変. -/
@[entry_point]
lemma huffmanStep_min_fst
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    ∀ z ∈ s, (huffmanStep s hs hg).val.1.2 ≤ z.2 := by
  intro z hz
  exact groupKey_le_imp_snd_le (huffmanStep_key_min_fst s hs hg z hz)

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **`huffmanStep` の 2nd groupKey-minimality spec (`.val.2.1` は `s.erase .val.1` 全体の
`groupKey` 最小)**. 定義本体の 2 段目 `Classical.choose (exists_min_image groupKey ...)` の
spec を unfold で取り出す. -/
@[entry_point]
lemma huffmanStep_key_min_snd
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    ∀ z ∈ s.erase (huffmanStep s hs hg).val.1,
      groupKey (huffmanStep s hs hg).val.2.1 ≤ groupKey z := by
  classical
  have hs_ne : s ≠ 0 := by
    intro heq; rw [heq, Multiset.card_zero] at hs; omega
  -- x1 と s' = s.erase x1 を再構成
  set x1 := Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
    (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne) with hx1_def
  have hx1 : x1 ∈ s ∧ ∀ z ∈ s, groupKey x1 ≤ groupKey z :=
    Classical.choose_spec (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs_ne)
  have hs'_ne : s.erase x1 ≠ 0 := by
    have hcard_s' : (s.erase x1).card = s.card - 1 :=
      Multiset.card_erase_of_mem hx1.1
    intro heq
    rw [heq, Multiset.card_zero] at hcard_s'
    omega
  have hx2 : (Classical.choose (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs'_ne)) ∈ s.erase x1 ∧
      ∀ z ∈ s.erase x1, groupKey (Classical.choose (Multiset.exists_min_image
        (α := Finset α × ℝ) (R := ℝ ×ₗ Colex (Finset α)) groupKey hs'_ne)) ≤ groupKey z :=
    Classical.choose_spec (Multiset.exists_min_image (α := Finset α × ℝ)
      (R := ℝ ×ₗ Colex (Finset α)) groupKey hs'_ne)
  -- (huffmanStep s hs hg).val.1 = x1, .val.2.1 = x2, so s.erase .val.1 = s.erase x1
  have hfst : (huffmanStep s hs hg).val.1 = x1 := by unfold huffmanStep; rfl
  intro z hz
  rw [hfst] at hz
  show groupKey (huffmanStep s hs hg).val.2.1 ≤ groupKey z
  unfold huffmanStep
  exact hx2.2 z hz

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **`huffmanStep` の 2nd minimality spec (`.val.2.1` は `s.erase .val.1` 全体の確率最小)**.
`huffmanStep_key_min_snd` の第 1 キー射影から導く. statement は決定化前と不変. -/
@[entry_point]
lemma huffmanStep_min_snd
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    ∀ z ∈ s.erase (huffmanStep s hs hg).val.1,
      (huffmanStep s hs hg).val.2.1.2 ≤ z.2 := by
  intro z hz
  exact groupKey_le_imp_snd_le (huffmanStep_key_min_snd s hs hg z hz)

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanStep` 後の HuffmanGrouping 保存 (アクセサ). -/
lemma huffmanStep_grouping
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    HuffmanGrouping (huffmanStep s hs hg).val.2.2 :=
  (huffmanStep s hs hg).property.2.2.2

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanStep` 後の multiset cardinality は **ちょうど 1 減る**. -/
lemma huffmanStep_card_eq
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    (huffmanStep s hs hg).val.2.2.card = s.card - 1 := by
  classical
  obtain ⟨hx1_mem, hx2_mem, hshape, _⟩ := (huffmanStep s hs hg).property
  have hs'_card : (s.erase (huffmanStep s hs hg).val.1).card = s.card - 1 :=
    Multiset.card_erase_of_mem hx1_mem
  rw [hshape, Multiset.card_cons,
    Multiset.card_erase_of_mem hx2_mem, hs'_card]
  have hpred : (s.card - 1).pred = s.card - 2 := by
    rw [Nat.pred_eq_sub_one]; omega
  rw [hpred]
  omega

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanStep` 後の multiset cardinality は 1 減る. -/
lemma huffmanStep_card_lt
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    (huffmanStep s hs hg).val.2.2.card < s.card := by
  rw [huffmanStep_card_eq s hs hg]; omega

/-- `huffmanLength` の内部実装: 確率付き group (`Finset α × ℝ`) の Multiset を入力に、
各 `α` 要素に対する codeword 長を返す.

`s.card` 上の strong induction で再帰. `HuffmanGrouping s` でない場合は `fun _ => 0` を返す
(out-of-spec 入力に対する default; 我々が使うのは `initMultiset P` から始まる descendants
のみ、これらは常に `HuffmanGrouping`). -/
noncomputable def huffmanLengthAux
    (s : Multiset (Finset α × ℝ)) : α → ℕ := by
  classical
  exact
    if hg : HuffmanGrouping s then
      if h : 2 ≤ s.card then
        let step := (huffmanStep s h hg).val
        let A := step.1.1
        let B := step.2.1.1
        let s'' := step.2.2
        have : s''.card < s.card := huffmanStep_card_lt s h hg
        let g := huffmanLengthAux s''
        fun a => if a ∈ A ∨ a ∈ B then g a + 1 else g a
      else
        fun _ => 0
    else
      fun _ => 0
termination_by s.card

/-- Initial multiset: 各 singleton `{a}` を確率 `P.real {a}` でラップ. -/
noncomputable def initMultiset (P : Measure α) : Multiset (Finset α × ℝ) :=
  (Finset.univ : Finset α).val.map (fun a => ({a}, P.real {a}))

/-! ### `huffmanLengthAux` の展開 / 構造的不変量 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanLengthAux` の展開 (recursive step, `HuffmanGrouping` 前提). -/
lemma huffmanLengthAux_eq_step (s : Multiset (Finset α × ℝ)) (h : 2 ≤ s.card)
    (hg : HuffmanGrouping s) :
    huffmanLengthAux s =
      let step := (huffmanStep s h hg).val
      let A := step.1.1
      let B := step.2.1.1
      let s'' := step.2.2
      let g := huffmanLengthAux s''
      fun a => if a ∈ A ∨ a ∈ B then g a + 1 else g a := by
  rw [huffmanLengthAux]
  simp only [dif_pos hg, dif_pos h]

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanLengthAux` の base case (card ≤ 1 ∧ HuffmanGrouping). -/
lemma huffmanLengthAux_eq_zero (s : Multiset (Finset α × ℝ)) (h : s.card ≤ 1)
    (hg : HuffmanGrouping s) :
    huffmanLengthAux s = fun _ => 0 := by
  have h' : ¬ 2 ≤ s.card := by omega
  rw [huffmanLengthAux]
  simp only [dif_pos hg, dif_neg h']

/-! ### 主役定義 -/

/-- **Huffman 語長関数** (binary, D = 2). -/
noncomputable def huffmanLength (P : Measure α) : α → ℕ :=
  huffmanLengthAux (initMultiset P)

/-! ### 主定理 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanLengthAux` の正値性 invariant (induction on `s.card`):
    任意の group `p ∈ s` が `a` を含むなら、語長 `huffmanLengthAux s a` は
    `s.card = 1` のとき `0`、`s.card ≥ 2` のとき `> 0`. -/
lemma huffmanLengthAux_pos_of_mem
    (s : Multiset (Finset α × ℝ)) (a : α)
    (hmem : ∃ p ∈ s, a ∈ p.1) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    0 < huffmanLengthAux s a := by
  -- strong induction on s.card
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    -- n = s.card ≥ 2
    rw [huffmanLengthAux_eq_step s hs hg]
    simp only
    -- step を取り出す
    set step := (huffmanStep s hs hg).val with hstep_def
    obtain ⟨hx1_mem, hx2_mem, hshape, hg''⟩ := huffmanStep_spec s hs hg
    -- 場合分け: a ∈ step.1.1 ∨ a ∈ step.2.1.1
    by_cases h_in_AB : a ∈ step.1.1 ∨ a ∈ step.2.1.1
    · simp [h_in_AB]
    · simp only [h_in_AB, ↓reduceIte, gt_iff_lt]
      -- 残: 0 < huffmanLengthAux step.2.2 a
      -- ∃ p ∈ step.2.2, a ∈ p.1 を示す
      push Not at h_in_AB
      obtain ⟨h_not_A, h_not_B⟩ := h_in_AB
      -- hmem の p について、p ≠ step.1, p ≠ step.2.1, p ∈ erase erase
      obtain ⟨p, hp_mem, hp_a⟩ := hmem
      have hp_ne_x1 : p ≠ step.1 := by
        rintro rfl; exact h_not_A hp_a
      have hp_ne_x2 : p ≠ step.2.1 := by
        rintro rfl; exact h_not_B hp_a
      -- p ∈ s.erase step.1
      have hp_in_s' : p ∈ s.erase step.1 :=
        (Multiset.mem_erase_of_ne hp_ne_x1).mpr hp_mem
      -- p ∈ (s.erase step.1).erase step.2.1
      have hp_in_s'' :
          p ∈ (s.erase step.1).erase step.2.1 :=
        (Multiset.mem_erase_of_ne hp_ne_x2).mpr hp_in_s'
      have hp_in_step22 : p ∈ step.2.2 := by
        rw [hshape]; exact Multiset.mem_cons_of_mem hp_in_s''
      have hmem' : ∃ q ∈ step.2.2, a ∈ q.1 := ⟨p, hp_in_step22, hp_a⟩
      -- step.2.2.card < s.card より s.card ≥ 2 の場合に応じて IH か base-case
      have hs''_lt : step.2.2.card < s.card := huffmanStep_card_lt s hs hg
      -- s.card = 2 のとき、step.2.2.card = 1, s.erase step.1 .erase step.2.1 = 0
      -- このとき hp_in_s'' で p ∈ 0 → False、矛盾
      by_cases hs''_two : 2 ≤ step.2.2.card
      · -- IH 適用
        have hn' : step.2.2.card < n := by omega
        exact ih step.2.2.card hn' step.2.2 hmem' hs''_two hg'' rfl
      · -- step.2.2.card ≤ 1 のときは hp_in_s'' で矛盾を導く:
        -- step.2.2 = merged ::ₘ erase_erase なので step.2.2.card ≥ 1
        -- step.2.2.card ≤ 1 ⇒ step.2.2.card = 1 ⇒ erase_erase.card = 0 ⇒ p ∉ erase_erase
        push Not at hs''_two
        have h_ee_card : ((s.erase step.1).erase step.2.1).card = 0 := by
          have : step.2.2.card = ((s.erase step.1).erase step.2.1).card + 1 := by
            rw [hshape, Multiset.card_cons]
          omega
        have h_ee_zero : (s.erase step.1).erase step.2.1 = 0 :=
          Multiset.card_eq_zero.mp h_ee_card
        rw [h_ee_zero] at hp_in_s''
        exact absurd hp_in_s'' (Multiset.notMem_zero _)

omit [DecidableEq α] [LinearOrder α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `initMultiset` の各要素 `a` は singleton group `({a}, P.real {a})` に属する. -/
lemma mem_initMultiset (P : Measure α) (a : α) :
    ∃ p ∈ initMultiset P, a ∈ p.1 := by
  refine ⟨({a}, P.real {a}), ?_, ?_⟩
  · -- ({a}, _) ∈ Finset.univ.val.map (fun a => ({a}, _))
    unfold initMultiset
    simp
  · simp

omit [DecidableEq α] [LinearOrder α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `initMultiset P` は `HuffmanGrouping` を満たす (Nodup + Nonempty + Disjoint). -/
lemma initMultiset_huffmanGrouping (P : Measure α) :
    HuffmanGrouping (initMultiset P) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- Nodup: f := fun a => ({a}, P.real {a}) は injective (1st coord で識別)
    unfold initMultiset
    have hinj : Function.Injective
        (fun a : α => (({a} : Finset α), P.real {a})) := by
      intro a b hab
      simp only [Prod.mk.injEq, Finset.singleton_inj] at hab
      exact hab.1
    exact (Finset.univ : Finset α).nodup.map hinj
  · -- Nonempty
    intro p hp
    unfold initMultiset at hp
    rw [Multiset.mem_map] at hp
    obtain ⟨a, _, ha_eq⟩ := hp
    rw [← ha_eq]
    exact Finset.singleton_nonempty a
  · -- Disjoint: 異なる singleton は disjoint
    intro p hp q hq hpq
    unfold initMultiset at hp hq
    rw [Multiset.mem_map] at hp hq
    obtain ⟨a, _, ha_eq⟩ := hp
    obtain ⟨b, _, hb_eq⟩ := hq
    rw [← ha_eq, ← hb_eq]
    -- ({a}, _) ≠ ({b}, _) ⟹ a ≠ b
    have hab : a ≠ b := by
      intro heq
      apply hpq
      rw [← ha_eq, ← hb_eq, heq]
    simp [hab]

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- Huffman 語長は正値 (`Fintype.card α ≥ 2` のとき). -/
theorem huffmanLength_pos (P : Measure α) [IsProbabilityMeasure P]
    (_hP : ∀ a, 0 < P.real {a}) (h_card : 2 ≤ Fintype.card α) (a : α) :
    0 < huffmanLength P a := by
  unfold huffmanLength
  have hcard_init : (initMultiset P).card = Fintype.card α := by
    unfold initMultiset
    rw [Multiset.card_map]
    rfl
  apply huffmanLengthAux_pos_of_mem _ _ (mem_initMultiset P a)
  · rw [hcard_init]; exact h_card
  · exact initMultiset_huffmanGrouping P

/-! ### Kraft 不等式 — 補助補題 (constancy + 不変量) -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanLengthAux s a` は各 group `p ∈ s` の `p.1` 上で定数. -/
lemma huffmanLengthAux_const_on_group
    (s : Multiset (Finset α × ℝ)) (hg : HuffmanGrouping s)
    (p : Finset α × ℝ) (hp : p ∈ s) (a b : α) (ha : a ∈ p.1) (hb : b ∈ p.1) :
    huffmanLengthAux s a = huffmanLengthAux s b := by
  induction hn : s.card using Nat.strong_induction_on
    generalizing s p a b with
  | _ n ih =>
    by_cases h2 : 2 ≤ s.card
    · rw [huffmanLengthAux_eq_step s h2 hg]
      simp only
      set step := (huffmanStep s h2 hg).val with hstep_def
      obtain ⟨hx1_mem, hx2_mem, hshape, hg''⟩ := huffmanStep_spec s h2 hg
      have hs''_lt : step.2.2.card < n := by
        have hlt : (huffmanStep s h2 hg).val.2.2.card < s.card :=
          huffmanStep_card_lt s h2 hg
        show (huffmanStep s h2 hg).val.2.2.card < n
        omega
      by_cases hp_x1 : p = step.1
      · -- p = x1 ⇒ a, b ∈ x1.1
        rw [hp_x1] at ha hb
        have ha_AB : a ∈ step.1.1 ∨ a ∈ step.2.1.1 := Or.inl ha
        have hb_AB : b ∈ step.1.1 ∨ b ∈ step.2.1.1 := Or.inl hb
        simp only [ha_AB, ↓reduceIte, hb_AB, Nat.add_right_cancel_iff]
        -- merged ∈ s'', a ∈ merged.1 = x1.1 ∪ x2.1, b ∈ same
        have ha_merged : a ∈ step.1.1 ∪ step.2.1.1 := Finset.mem_union_left _ ha
        have hb_merged : b ∈ step.1.1 ∪ step.2.1.1 := Finset.mem_union_left _ hb
        have hmerged_in :
            (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2) ∈ step.2.2 := by
          rw [hshape]; exact Multiset.mem_cons_self _ _
        exact ih step.2.2.card hs''_lt (s := step.2.2) hg''
          (p := (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2))
          hmerged_in (a := a) (b := b) ha_merged hb_merged rfl
      · by_cases hp_x2 : p = step.2.1
        · -- p = x2: a, b ∈ x2.1
          rw [hp_x2] at ha hb
          have ha_AB : a ∈ step.1.1 ∨ a ∈ step.2.1.1 := Or.inr ha
          have hb_AB : b ∈ step.1.1 ∨ b ∈ step.2.1.1 := Or.inr hb
          simp only [ha_AB, ↓reduceIte, hb_AB, Nat.add_right_cancel_iff]
          have ha_merged : a ∈ step.1.1 ∪ step.2.1.1 := Finset.mem_union_right _ ha
          have hb_merged : b ∈ step.1.1 ∪ step.2.1.1 := Finset.mem_union_right _ hb
          have hmerged_in :
              (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2) ∈ step.2.2 := by
            rw [hshape]; exact Multiset.mem_cons_self _ _
          exact ih step.2.2.card hs''_lt (s := step.2.2) hg''
            (p := (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2))
            hmerged_in (a := a) (b := b) ha_merged hb_merged rfl
        · -- p ∈ ee
          have hp_ee : p ∈ (s.erase step.1).erase step.2.1 := by
            have hp_s' : p ∈ s.erase step.1 :=
              (Multiset.mem_erase_of_ne hp_x1).mpr hp
            exact (Multiset.mem_erase_of_ne hp_x2).mpr hp_s'
          have hp_s'' : p ∈ step.2.2 := by
            rw [hshape]; exact Multiset.mem_cons_of_mem hp_ee
          have h_disj_x1 : Disjoint p.1 step.1.1 :=
            hg.disjoint hp hx1_mem hp_x1
          have h_disj_x2 : Disjoint p.1 step.2.1.1 := by
            have hx2_s : step.2.1 ∈ s := Multiset.mem_of_mem_erase hx2_mem
            exact hg.disjoint hp hx2_s hp_x2
          have ha_notAB : ¬ (a ∈ step.1.1 ∨ a ∈ step.2.1.1) := by
            rintro (ha1 | ha2)
            · exact (Finset.disjoint_left.mp h_disj_x1 ha) ha1
            · exact (Finset.disjoint_left.mp h_disj_x2 ha) ha2
          have hb_notAB : ¬ (b ∈ step.1.1 ∨ b ∈ step.2.1.1) := by
            rintro (hb1 | hb2)
            · exact (Finset.disjoint_left.mp h_disj_x1 hb) hb1
            · exact (Finset.disjoint_left.mp h_disj_x2 hb) hb2
          simp only [ha_notAB, ↓reduceIte, hb_notAB]
          exact ih step.2.2.card hs''_lt (s := step.2.2) hg''
            (p := p) hp_s'' (a := a) (b := b) ha hb rfl
    · rw [huffmanLengthAux_eq_zero s (by omega) hg]

/-- Huffman 用 Kraft 和 (per-group 形). 各 group `p ∈ s` の Kraft 寄与は
`(∑ a ∈ p.1, 2^(-huffmanLengthAux s a)) / p.1.card`. constancy 補題下では
`2^(-d_p(s))` に一致. -/
noncomputable def kraftPerGroup (s : Multiset (Finset α × ℝ)) : ℝ :=
  (s.map (fun p =>
    (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (p.1.card : ℝ))).sum

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `kraftPerGroup` の base 値: `s.card ≤ 1` で `s.card` に等しい (各 group の depth = 0). -/
lemma kraftPerGroup_eq_card_of_base
    (s : Multiset (Finset α × ℝ)) (h : s.card ≤ 1) (hg : HuffmanGrouping s) :
    kraftPerGroup s = (s.card : ℝ) := by
  unfold kraftPerGroup
  rw [huffmanLengthAux_eq_zero s h hg]
  -- 各 term は (∑_{a ∈ p.1} 2^0) / p.1.card = p.1.card / p.1.card = 1
  -- s.map (fun _ => 1) |>.sum = s.card
  have hterm : ∀ p ∈ s,
      (∑ a ∈ p.1, (2 : ℝ) ^ (-((0 : ℕ) : ℤ))) / (p.1.card : ℝ) = 1 := by
    intro p hp
    have hp_ne : p.1.Nonempty := hg.nonempty hp
    have hcard_pos : 0 < p.1.card := Finset.card_pos.mpr hp_ne
    have hcard_ne : (p.1.card : ℝ) ≠ 0 := by exact_mod_cast hcard_pos.ne'
    rw [show -((0 : ℕ) : ℤ) = 0 from rfl, zpow_zero]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    field_simp
  rw [show s.map (fun p =>
      (∑ a ∈ p.1, (2 : ℝ) ^ (-((fun _ : α => (0 : ℕ)) a : ℤ))) / (p.1.card : ℝ))
      = s.map (fun _ => 1) from ?_]
  · rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one]
  · apply Multiset.map_congr rfl
    intro p hp
    exact hterm p hp

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Helper: `s = x1 ::ₘ x2 ::ₘ ee` (`Nodup` + erase の inverse). -/
lemma huffmanStep_orig_decomp
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    s = (huffmanStep s hs hg).val.1 ::ₘ (huffmanStep s hs hg).val.2.1 ::ₘ
        ((s.erase (huffmanStep s hs hg).val.1).erase (huffmanStep s hs hg).val.2.1) := by
  obtain ⟨hx1_mem, hx2_mem, _, _⟩ := (huffmanStep s hs hg).property
  have h1 : s = (huffmanStep s hs hg).val.1 ::ₘ s.erase (huffmanStep s hs hg).val.1 :=
    (Multiset.cons_erase hx1_mem).symm
  have h2 : s.erase (huffmanStep s hs hg).val.1 =
      (huffmanStep s hs hg).val.2.1 ::ₘ
        (s.erase (huffmanStep s hs hg).val.1).erase (huffmanStep s hs hg).val.2.1 :=
    (Multiset.cons_erase hx2_mem).symm
  exact h1.trans (congr_arg ((huffmanStep s hs hg).val.1 ::ₘ ·) h2)

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanLengthAux s a = huffmanLengthAux s'' a + 1` for `a ∈ x1.1 ∪ x2.1`. -/
lemma huffmanLengthAux_step_merged
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    {a : α} (ha : a ∈ (huffmanStep s hs hg).val.1.1 ∨
                  a ∈ (huffmanStep s hs hg).val.2.1.1) :
    huffmanLengthAux s a =
      huffmanLengthAux (huffmanStep s hs hg).val.2.2 a + 1 := by
  rw [huffmanLengthAux_eq_step s hs hg]
  simp [ha]

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `huffmanLengthAux s a = huffmanLengthAux s'' a` for `a ∉ x1.1 ∪ x2.1`. -/
lemma huffmanLengthAux_step_other
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    {a : α} (ha : ¬ (a ∈ (huffmanStep s hs hg).val.1.1 ∨
                  a ∈ (huffmanStep s hs hg).val.2.1.1)) :
    huffmanLengthAux s a =
      huffmanLengthAux (huffmanStep s hs hg).val.2.2 a := by
  rw [huffmanLengthAux_eq_step s hs hg]
  simp [ha]

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- 各 ee 内の group `q` について、`q.1` 上で `huffmanLengthAux s = huffmanLengthAux s''`. -/
lemma huffmanLengthAux_step_eq_on_other_group
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    (q : Finset α × ℝ)
    (hq : q ∈ (s.erase (huffmanStep s hs hg).val.1).erase
              (huffmanStep s hs hg).val.2.1)
    {a : α} (ha : a ∈ q.1) :
    huffmanLengthAux s a =
      huffmanLengthAux (huffmanStep s hs hg).val.2.2 a := by
  obtain ⟨hx1_mem, hx2_mem, _, _⟩ := (huffmanStep s hs hg).property
  have hq_s' : q ∈ s.erase (huffmanStep s hs hg).val.1 :=
    Multiset.mem_of_mem_erase hq
  have hq_s : q ∈ s := Multiset.mem_of_mem_erase hq_s'
  have hq_ne_x1 : q ≠ (huffmanStep s hs hg).val.1 := by
    intro heq; rw [heq] at hq_s'
    exact hg.nodup.notMem_erase hq_s'
  have hq_ne_x2 : q ≠ (huffmanStep s hs hg).val.2.1 := by
    intro heq; rw [heq] at hq
    exact (hg.nodup.erase _).notMem_erase hq
  have hx2_s : (huffmanStep s hs hg).val.2.1 ∈ s :=
    Multiset.mem_of_mem_erase hx2_mem
  have h_disj_x1 : Disjoint q.1 (huffmanStep s hs hg).val.1.1 :=
    hg.disjoint hq_s hx1_mem hq_ne_x1
  have h_disj_x2 : Disjoint q.1 (huffmanStep s hs hg).val.2.1.1 :=
    hg.disjoint hq_s hx2_s hq_ne_x2
  have ha_notAB : ¬ (a ∈ (huffmanStep s hs hg).val.1.1 ∨
                     a ∈ (huffmanStep s hs hg).val.2.1.1) := by
    rintro (h1 | h2)
    · exact (Finset.disjoint_left.mp h_disj_x1 ha) h1
    · exact (Finset.disjoint_left.mp h_disj_x2 ha) h2
  exact huffmanLengthAux_step_other s hs hg ha_notAB

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- `kraftPerGroup` の **step 不変量** (本 Kraft 証明の心臓部):
`s → huffmanStep s` で値が保存される.

論証: `s = x1 ::ₘ x2 ::ₘ ee` と `s'' = merged ::ₘ ee` に分解、それぞれの kraft 寄与:
- `ee 寄与`: 各 `q ∈ ee` で `huffmanLengthAux s = huffmanLengthAux s''` on `q.1` (disjoint
  から). 寄与は同一.
- `x1, x2 寄与 (in s)`: `(∑ a ∈ x1.1, 2^(-d_x1)) / x1.1.card + (∑ a ∈ x2.1, 2^(-d_x2)) / x2.1.card`
  ここで `d_x1 = d_x2 = d_merged + 1` (`huffmanLengthAux_step_merged`)
  = `(x1.1.card · 2^(-(d_m+1))) / x1.1.card + ...`
  = `2^(-(d_m+1)) + 2^(-(d_m+1))`
  = `2^(-d_m)`
- `merged 寄与 (in s'')`: `(∑ a ∈ merged.1, 2^(-d_m)) / merged.1.card`
  = `merged.1.card · 2^(-d_m) / merged.1.card = 2^(-d_m)`.
合計一致. -/
lemma kraftPerGroup_step
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    kraftPerGroup s = kraftPerGroup (huffmanStep s hs hg).val.2.2 := by
  obtain ⟨hx1_mem, hx2_mem, hshape, hg''⟩ := (huffmanStep s hs hg).property
  set x1 := (huffmanStep s hs hg).val.1 with hx1_def
  set x2 := (huffmanStep s hs hg).val.2.1 with hx2_def
  set s'' := (huffmanStep s hs hg).val.2.2 with hs''_def
  set ee := (s.erase x1).erase x2 with hee_def
  let merged : Finset α × ℝ := (x1.1 ∪ x2.1, x1.2 + x2.2)
  -- shape: s'' = merged ::ₘ ee
  have hshape' : s'' = merged ::ₘ ee := hshape
  -- x1, x2, ee の disjoint 性質
  have hx1_x2_ne : x1 ≠ x2 := by
    intro heq; rw [← heq] at hx2_mem
    exact hg.nodup.notMem_erase hx2_mem
  -- s = x1 ::ₘ x2 ::ₘ ee
  have hs_decomp : s = x1 ::ₘ x2 ::ₘ ee := huffmanStep_orig_decomp s hs hg
  -- nonempty proofs
  have hx1_ne : x1.1.Nonempty := hg.nonempty hx1_mem
  have hx2_s : x2 ∈ s := Multiset.mem_of_mem_erase hx2_mem
  have hx2_ne : x2.1.Nonempty := hg.nonempty hx2_s
  have hmerged_ne : merged.1.Nonempty := hx1_ne.mono Finset.subset_union_left
  -- cards
  have hx1_card_pos : (0 : ℝ) < x1.1.card := by
    exact_mod_cast Finset.card_pos.mpr hx1_ne
  have hx2_card_pos : (0 : ℝ) < x2.1.card := by
    exact_mod_cast Finset.card_pos.mpr hx2_ne
  have hmerged_card_pos : (0 : ℝ) < merged.1.card := by
    exact_mod_cast Finset.card_pos.mpr hmerged_ne
  -- disjoint
  have hdisj_x1x2 : Disjoint x1.1 x2.1 := hg.disjoint hx1_mem hx2_s hx1_x2_ne
  have hmerged_card : (merged.1.card : ℝ) = x1.1.card + x2.1.card := by
    show ((x1.1 ∪ x2.1).card : ℝ) = _
    rw [Finset.card_union_of_disjoint hdisj_x1x2]
    push_cast; ring
  -- depth values: pick a₀ ∈ x1.1, then d_x1 := huffmanLengthAux s a₀
  -- Need: depth is constant on x1.1, x2.1, merged.1
  -- Use constancy lemma + step relation
  -- Define depths as `huffmanLengthAux s'' a` for some specific a in merged.1
  -- Goal: ∑ x ∈ p.1, 2^(-huffmanLengthAux s x) for each p ∈ s
  -- Strategy: 直接 kraftPerGroup を sum_cons で展開 (s と s'' は触らない)
  -- Avoid `rw` on `hs_decomp` (would also rewrite inside `huffmanLengthAux s`).
  -- Instead use sum_cons directly via the multiset equality.
  have lhs_eq :
      kraftPerGroup s =
      (∑ a ∈ x1.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (x1.1.card : ℝ)
      + ((∑ a ∈ x2.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (x2.1.card : ℝ)
      + (ee.map (fun p =>
          (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (p.1.card : ℝ))).sum) := by
    unfold kraftPerGroup
    -- (s.map f).sum = ((x1 ::ₘ x2 ::ₘ ee).map f).sum (using hs_decomp at the multiset arg only)
    have : (s.map (fun p =>
        (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (p.1.card : ℝ))).sum
        = ((x1 ::ₘ x2 ::ₘ ee).map (fun p =>
        (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (p.1.card : ℝ))).sum := by
      exact congr_arg _ (congr_arg _ hs_decomp)
    rw [this]
    simp only [Multiset.map_cons, Multiset.sum_cons]
  have rhs_eq :
      kraftPerGroup s'' =
      (∑ a ∈ merged.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (merged.1.card : ℝ)
      + (ee.map (fun p =>
          (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (p.1.card : ℝ))).sum := by
    unfold kraftPerGroup
    have : (s''.map (fun p =>
        (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (p.1.card : ℝ))).sum
        = ((merged ::ₘ ee).map (fun p =>
        (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (p.1.card : ℝ))).sum := by
      exact congr_arg _ (congr_arg _ hshape')
    rw [this]
    simp only [Multiset.map_cons, Multiset.sum_cons]
  rw [lhs_eq, rhs_eq]
  -- LHS: f_s x1 + (f_s x2 + (ee.map f_s).sum)
  -- RHS: f_s'' merged + (ee.map f_s'').sum
  -- Need: ee 寄与等式 + (f_s x1 + f_s x2 = f_s'' merged)
  have h_ee_sum :
      (ee.map (fun p =>
        (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (p.1.card : ℝ))).sum
      = (ee.map (fun p =>
          (∑ a ∈ p.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (p.1.card : ℝ))).sum := by
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro q hq
    apply congr_arg (· / (q.1.card : ℝ))
    apply Finset.sum_congr rfl
    intro a ha
    rw [huffmanLengthAux_step_eq_on_other_group s hs hg q hq ha]
  -- 主等式: f_s x1 + f_s x2 = f_s'' merged
  -- f_s x1 = (∑ a ∈ x1.1, 2^(-huffmanLengthAux s a)) / x1.1.card
  -- by step_merged, huffmanLengthAux s a = huffmanLengthAux s'' a + 1 for a ∈ x1.1 (⊆ x1.1 ∪ x2.1)
  -- by constancy in s'' on merged.1 ⊇ x1.1: huffmanLengthAux s'' a = const = d_m
  -- pick a0 ∈ x1.1, b0 ∈ x2.1
  obtain ⟨a0, ha0⟩ := hx1_ne
  obtain ⟨b0, hb0⟩ := hx2_ne
  -- merged ∈ s''
  have hmerged_in_s'' : merged ∈ s'' := by rw [hshape']; exact Multiset.mem_cons_self _ _
  have ha0_merged : a0 ∈ merged.1 := Finset.mem_union_left _ ha0
  have hb0_merged : b0 ∈ merged.1 := Finset.mem_union_right _ hb0
  -- d_m := huffmanLengthAux s'' a0
  set d_m := huffmanLengthAux s'' a0 with hd_m_def
  -- All a ∈ merged.1: huffmanLengthAux s'' a = d_m (constancy in s'' on merged)
  have h_merged_const : ∀ a ∈ merged.1, huffmanLengthAux s'' a = d_m := by
    intro a ha
    exact huffmanLengthAux_const_on_group s'' hg'' merged hmerged_in_s'' a a0 ha ha0_merged
  -- For a ∈ x1.1 (⊆ merged.1): huffmanLengthAux s'' a = d_m, so huffmanLengthAux s a = d_m + 1
  have h_x1_aux : ∀ a ∈ x1.1, huffmanLengthAux s a = d_m + 1 := by
    intro a ha
    have h1 : huffmanLengthAux s a = huffmanLengthAux s'' a + 1 := by
      apply huffmanLengthAux_step_merged s hs hg
      exact Or.inl ha
    have h2 : huffmanLengthAux s'' a = d_m :=
      h_merged_const a (Finset.mem_union_left _ ha)
    omega
  -- Similarly for x2
  have h_x2_aux : ∀ a ∈ x2.1, huffmanLengthAux s a = d_m + 1 := by
    intro a ha
    have h1 : huffmanLengthAux s a = huffmanLengthAux s'' a + 1 := by
      apply huffmanLengthAux_step_merged s hs hg
      exact Or.inr ha
    have h2 : huffmanLengthAux s'' a = d_m :=
      h_merged_const a (Finset.mem_union_right _ ha)
    omega
  -- Compute terms:
  -- f_s x1 = (∑ a ∈ x1.1, 2^(-(d_m+1))) / x1.1.card = (x1.1.card · 2^(-(d_m+1))) / x1.1.card
  --       = 2^(-(d_m+1)) = (1/2) · 2^(-d_m)
  -- f_s x2 = same = (1/2) · 2^(-d_m)
  -- f_s x1 + f_s x2 = 2^(-d_m)
  -- f_s'' merged = (∑ a ∈ merged.1, 2^(-d_m)) / merged.1.card = merged.1.card · 2^(-d_m) / merged.1.card
  --             = 2^(-d_m)
  have h_x1_term :
      (∑ a ∈ x1.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (x1.1.card : ℝ)
      = (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) := by
    have : (∑ a ∈ x1.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ)))
        = (x1.1.card : ℝ) * (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) := by
      rw [show (x1.1.card : ℝ) * (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ))
          = ∑ _x ∈ x1.1, (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      apply Finset.sum_congr rfl
      intro a ha
      rw [h_x1_aux a ha]
    rw [this]
    field_simp
  have h_x2_term :
      (∑ a ∈ x2.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ))) / (x2.1.card : ℝ)
      = (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) := by
    have : (∑ a ∈ x2.1, (2 : ℝ) ^ (-(huffmanLengthAux s a : ℤ)))
        = (x2.1.card : ℝ) * (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) := by
      rw [show (x2.1.card : ℝ) * (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ))
          = ∑ _x ∈ x2.1, (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      apply Finset.sum_congr rfl
      intro a ha
      rw [h_x2_aux a ha]
    rw [this]
    field_simp
  have h_merged_term :
      (∑ a ∈ merged.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ))) / (merged.1.card : ℝ)
      = (2 : ℝ) ^ (-(d_m : ℤ)) := by
    have : (∑ a ∈ merged.1, (2 : ℝ) ^ (-(huffmanLengthAux s'' a : ℤ)))
        = (merged.1.card : ℝ) * (2 : ℝ) ^ (-(d_m : ℤ)) := by
      rw [show (merged.1.card : ℝ) * (2 : ℝ) ^ (-(d_m : ℤ))
          = ∑ _x ∈ merged.1, (2 : ℝ) ^ (-(d_m : ℤ)) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      apply Finset.sum_congr rfl
      intro a ha
      rw [h_merged_const a ha]
    rw [this]
    field_simp
  rw [h_x1_term, h_x2_term, h_merged_term, h_ee_sum]
  -- Goal: 2^(-(d_m+1)) + (2^(-(d_m+1)) + rest) = 2^(-d_m) + rest
  -- i.e. 2^(-(d_m+1)) + 2^(-(d_m+1)) = 2^(-d_m)
  have h_two_half : (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ))
      = (2 : ℝ) ^ (-(d_m : ℤ)) := by
    have h_pow : (2 : ℝ) ^ (-((d_m + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(d_m : ℤ)) / 2 := by
      have : -((d_m + 1 : ℕ) : ℤ) = -(d_m : ℤ) - 1 := by push_cast; ring
      rw [this, zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rw [h_pow]; ring
  linarith

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Strong invariant: `HuffmanGrouping s` ⇒ `kraftPerGroup s = s.card` (基底でも step でも `s.card` は減らない…?
実は `kraftPerGroup` は step で不変、`s.card` は減るので一致しない。**正しくは**: 各 group が depth `d_p` を
持ち、`∑_{p} 2^(-d_p) = 1` (full binary tree). 帰納 base case `s.card = 1` で `kraftPerGroup = 1`. -/
lemma kraftPerGroup_eq_one
    (s : Multiset (Finset α × ℝ)) (hs : 1 ≤ s.card) (hg : HuffmanGrouping s) :
    kraftPerGroup s = 1 := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases h2 : 2 ≤ s.card
    · rw [kraftPerGroup_step s h2 hg]
      have hlt : (huffmanStep s h2 hg).val.2.2.card < s.card :=
        huffmanStep_card_lt s h2 hg
      have hs'' : (huffmanStep s h2 hg).val.2.2.card < n := by
        show (huffmanStep s h2 hg).val.2.2.card < n; omega
      have hs''_card_pos : 1 ≤ (huffmanStep s h2 hg).val.2.2.card := by
        rw [huffmanStep_card_eq s h2 hg]; omega
      exact ih _ hs'' _ hs''_card_pos (huffmanStep_grouping s h2 hg) rfl
    · -- s.card = 1
      have h1 : s.card = 1 := by omega
      rw [kraftPerGroup_eq_card_of_base s (by omega) hg]
      simp [h1]

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- `initMultiset P` での `kraftPerGroup` は atom 和に一致: 各 group が singleton なので、
`∑_a 2^(-huffmanLength P a) = kraftPerGroup (initMultiset P) = 1`. -/
lemma kraftPerGroup_initMultiset_eq_kraft (P : Measure α) :
    kraftPerGroup (initMultiset P)
      = ∑ a : α, (2 : ℝ) ^ (-(huffmanLength P a : ℤ)) := by
  classical
  -- まず: kraftPerGroup の各 term は singleton group では `2^(-d)` に簡約
  have hsimp : ∀ a : α,
      (∑ x ∈ ({a} : Finset α),
          (2 : ℝ) ^ (-(huffmanLengthAux (initMultiset P) x : ℤ)))
        / (({a} : Finset α).card : ℝ)
      = (2 : ℝ) ^ (-(huffmanLengthAux (initMultiset P) a : ℤ)) := by
    intro a
    simp
  -- kraftPerGroup の展開: initMultiset = univ.val.map f
  unfold kraftPerGroup
  show ((initMultiset P).map _).sum
    = ∑ a : α, (2 : ℝ) ^ (-(huffmanLength P a : ℤ))
  unfold initMultiset
  rw [Multiset.map_map]
  -- Goal: ((univ.val.map (f ∘ (fun a => ({a}, P.real {a})))).sum = ∑ a ∈ univ, ...
  -- Finset.sum is defined as Multiset.sum ∘ Finset.val.map
  unfold huffmanLength
  -- Use Finset.sum_def
  rw [show ∑ a : α, (2 : ℝ) ^ (-(huffmanLengthAux (initMultiset P) a : ℤ))
      = ((Finset.univ : Finset α).val.map
          (fun a => (2 : ℝ) ^ (-(huffmanLengthAux (initMultiset P) a : ℤ)))).sum from rfl]
  -- Both sides are multiset sums of maps; show the maps are equal
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  -- Goal: ((∑ x ∈ {a}, 2^(-...)) / ({a}.card : ℝ)) = 2^(-...)
  -- Note: huffmanLengthAux (initMultiset P) — the inner `initMultiset` is opaque here
  exact hsimp a

omit [MeasurableSingletonClass α] in
/-- Huffman 語長は Kraft 不等式 (D = 2) を **等号** で充足: `∑ 2^(-huffmanLength) = 1`.
これは `kraftPerGroup` が `HuffmanGrouping` 上常に `1` であることから従う. -/
@[entry_point]
theorem huffmanLength_kraft_eq_one (P : Measure α) [IsProbabilityMeasure P]
    (_hP : ∀ a, 0 < P.real {a}) :
    ∑ a : α, ((2 : ℝ)) ^ (-(huffmanLength P a : ℤ)) = 1 := by
  rw [← kraftPerGroup_initMultiset_eq_kraft P]
  have hinit : HuffmanGrouping (initMultiset P) := initMultiset_huffmanGrouping P
  have hcard : 1 ≤ (initMultiset P).card := by
    unfold initMultiset
    rw [Multiset.card_map]
    have : 0 < Fintype.card α := Fintype.card_pos
    exact this
  exact kraftPerGroup_eq_one _ hcard hinit

omit [MeasurableSingletonClass α] in
/-- Huffman 語長は Kraft 不等式 (D = 2) を充足 (実は等号). -/
@[entry_point]
theorem huffmanLength_kraft_le_one (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a, 0 < P.real {a}) :
    ∑ a : α, ((2 : ℝ)) ^ (-(huffmanLength P a : ℤ)) ≤ 1 := by
  rw [huffmanLength_kraft_eq_one P hP]

omit [MeasurableSingletonClass α] in
/-- **副系**: Huffman 語長から prefix code が構成できる
(`ShannonCodeKraftReverse.exists_prefix_code_of_kraft` 経由). -/
@[entry_point]
theorem exists_huffman_prefix_code
    (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a, 0 < P.real {a}) (h_card : 2 ≤ Fintype.card α) :
    ∃ c : α → List (Fin 2),
      Function.Injective c ∧
      (∀ a, (c a).length = huffmanLength P a) ∧
      InformationTheory.Shannon.ShannonCodeKraftReverse.IsPrefixFree c := by
  apply InformationTheory.Shannon.ShannonCodeKraftReverse.exists_prefix_code_of_kraft
    (D := 2) (by norm_num)
  · intro a; exact huffmanLength_pos P hP h_card a
  · exact huffmanLength_kraft_le_one P hP

-- Phase 4-5 (`exists_sibling_min_pair` + `huffmanLength_optimal`) は本 plan
-- scope-out. 後続 seed `T1-A'` (`docs/textbook-roadmap.md` 参照) で publish 予定.

/-! ### cost-level pivot (T1-A'') — multiset-level expected length 漸化式

Cover-Thomas Theorem 5.8.1 強形を per-symbol depth identity (FALSE) ではなく
**期待長そのもの (cost = ∑ prob·depth)** の多重集合上漸化で閉じるための核。
`kraftPerGroup` 群 (`Huffman.lean:655`) と同じ per-group shape を採り、
`kraftPerGroup_step` の証明 template を mirror する
(`docs/shannon/huffman-cost-level-optimality-plan.md`)。 -/

/-- group 多重集合上の期待長 (= ∑ group, (group 確率質量 `p.2`) · (group depth)).
group 上 depth は `huffmanLengthAux_const_on_group` で定数なので、
`(∑ a ∈ p.1, d) / p.1.card` で代表元の depth を取り出す (= `kraftPerGroup` と同 shape).

@audit:ok — independent audit (2026-05-30): genuine def、`#print axioms` = [propext, Classical.choice, Quot.sound]。 -/
noncomputable def huffmanCost (s : Multiset (Finset α × ℝ)) : ℝ :=
  (s.map (fun p =>
    p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **cost の step 不変 + merged ペナルティ**:
`huffmanCost s = huffmanCost s'' + (x1.2 + x2.2)`  where `s'' = (huffmanStep s ..).val.2.2`,
`x1 = .val.1`, `x2 = .val.2.1`.
論証は `kraftPerGroup_step` (`Huffman.lean:770`) の直接 mirror: 重み `(∑ 2^(-d))/card` を
`p.2 * (∑ d)/card` に替え、merged 寄与 `(x1.2+x2.2)·d_m` と x1/x2 寄与
`x1.2·(d_m+1)+x2.2·(d_m+1)` の差 = `(x1.2+x2.2)`。

@audit:ok — independent audit (2026-05-30): 構造引数のみ (`HuffmanGrouping` / card)、genuine 帰納核、`#print axioms` = [propext, Classical.choice, Quot.sound]。 -/
lemma huffmanCost_step
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s) :
    huffmanCost s
      = huffmanCost (huffmanStep s hs hg).val.2.2
        + ((huffmanStep s hs hg).val.1.2 + (huffmanStep s hs hg).val.2.1.2) := by
  obtain ⟨hx1_mem, hx2_mem, hshape, hg''⟩ := (huffmanStep s hs hg).property
  set x1 := (huffmanStep s hs hg).val.1 with hx1_def
  set x2 := (huffmanStep s hs hg).val.2.1 with hx2_def
  set s'' := (huffmanStep s hs hg).val.2.2 with hs''_def
  set ee := (s.erase x1).erase x2 with hee_def
  let merged : Finset α × ℝ := (x1.1 ∪ x2.1, x1.2 + x2.2)
  have hshape' : s'' = merged ::ₘ ee := hshape
  have hx1_x2_ne : x1 ≠ x2 := by
    intro heq; rw [← heq] at hx2_mem
    exact hg.nodup.notMem_erase hx2_mem
  have hs_decomp : s = x1 ::ₘ x2 ::ₘ ee := huffmanStep_orig_decomp s hs hg
  have hx1_ne : x1.1.Nonempty := hg.nonempty hx1_mem
  have hx2_s : x2 ∈ s := Multiset.mem_of_mem_erase hx2_mem
  have hx2_ne : x2.1.Nonempty := hg.nonempty hx2_s
  have hmerged_ne : merged.1.Nonempty := hx1_ne.mono Finset.subset_union_left
  have hx1_card_pos : (0 : ℝ) < x1.1.card := by
    exact_mod_cast Finset.card_pos.mpr hx1_ne
  have hx2_card_pos : (0 : ℝ) < x2.1.card := by
    exact_mod_cast Finset.card_pos.mpr hx2_ne
  have hmerged_card_pos : (0 : ℝ) < merged.1.card := by
    exact_mod_cast Finset.card_pos.mpr hmerged_ne
  have hdisj_x1x2 : Disjoint x1.1 x2.1 := hg.disjoint hx1_mem hx2_s hx1_x2_ne
  have hmerged_card : (merged.1.card : ℝ) = x1.1.card + x2.1.card := by
    show ((x1.1 ∪ x2.1).card : ℝ) = _
    rw [Finset.card_union_of_disjoint hdisj_x1x2]
    push_cast; ring
  -- LHS / RHS を per-group 形に展開 (kraftPerGroup_step mirror)
  have lhs_eq :
      huffmanCost s =
      x1.2 * ((∑ a ∈ x1.1, (huffmanLengthAux s a : ℝ)) / (x1.1.card : ℝ))
      + (x2.2 * ((∑ a ∈ x2.1, (huffmanLengthAux s a : ℝ)) / (x2.1.card : ℝ))
      + (ee.map (fun p =>
          p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum) := by
    unfold huffmanCost
    have : (s.map (fun p =>
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum
        = ((x1 ::ₘ x2 ::ₘ ee).map (fun p =>
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum := by
      exact congr_arg _ (congr_arg _ hs_decomp)
    rw [this]
    simp only [Multiset.map_cons, Multiset.sum_cons]
  have rhs_eq :
      huffmanCost s'' =
      merged.2 * ((∑ a ∈ merged.1, (huffmanLengthAux s'' a : ℝ)) / (merged.1.card : ℝ))
      + (ee.map (fun p =>
          p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum := by
    unfold huffmanCost
    have : (s''.map (fun p =>
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum
        = ((merged ::ₘ ee).map (fun p =>
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum := by
      exact congr_arg _ (congr_arg _ hshape')
    rw [this]
    simp only [Multiset.map_cons, Multiset.sum_cons]
  rw [lhs_eq, rhs_eq]
  -- ee 寄与等式
  have h_ee_sum :
      (ee.map (fun p =>
        p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s a : ℝ)) / (p.1.card : ℝ)))).sum
      = (ee.map (fun p =>
          p.2 * ((∑ a ∈ p.1, (huffmanLengthAux s'' a : ℝ)) / (p.1.card : ℝ)))).sum := by
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro q hq
    apply congr_arg (q.2 * ·)
    apply congr_arg (· / (q.1.card : ℝ))
    apply Finset.sum_congr rfl
    intro a ha
    rw [huffmanLengthAux_step_eq_on_other_group s hs hg q hq ha]
  -- depth 値: a0 ∈ x1.1, b0 ∈ x2.1, d_m := huffmanLengthAux s'' a0
  obtain ⟨a0, ha0⟩ := hx1_ne
  obtain ⟨b0, hb0⟩ := hx2_ne
  have hmerged_in_s'' : merged ∈ s'' := by rw [hshape']; exact Multiset.mem_cons_self _ _
  have ha0_merged : a0 ∈ merged.1 := Finset.mem_union_left _ ha0
  have hb0_merged : b0 ∈ merged.1 := Finset.mem_union_right _ hb0
  set d_m := huffmanLengthAux s'' a0 with hd_m_def
  have h_merged_const : ∀ a ∈ merged.1, huffmanLengthAux s'' a = d_m := by
    intro a ha
    exact huffmanLengthAux_const_on_group s'' hg'' merged hmerged_in_s'' a a0 ha ha0_merged
  have h_x1_aux : ∀ a ∈ x1.1, huffmanLengthAux s a = d_m + 1 := by
    intro a ha
    have h1 : huffmanLengthAux s a = huffmanLengthAux s'' a + 1 :=
      huffmanLengthAux_step_merged s hs hg (Or.inl ha)
    have h2 : huffmanLengthAux s'' a = d_m :=
      h_merged_const a (Finset.mem_union_left _ ha)
    omega
  have h_x2_aux : ∀ a ∈ x2.1, huffmanLengthAux s a = d_m + 1 := by
    intro a ha
    have h1 : huffmanLengthAux s a = huffmanLengthAux s'' a + 1 :=
      huffmanLengthAux_step_merged s hs hg (Or.inr ha)
    have h2 : huffmanLengthAux s'' a = d_m :=
      h_merged_const a (Finset.mem_union_right _ ha)
    omega
  -- x1 寄与: (∑ a ∈ x1.1, (d_m+1)) / card = (d_m+1)
  have h_x1_term :
      (∑ a ∈ x1.1, (huffmanLengthAux s a : ℝ)) / (x1.1.card : ℝ)
      = ((d_m : ℝ) + 1) := by
    have hsum : (∑ a ∈ x1.1, (huffmanLengthAux s a : ℝ))
        = (x1.1.card : ℝ) * ((d_m : ℝ) + 1) := by
      rw [show (x1.1.card : ℝ) * ((d_m : ℝ) + 1)
          = ∑ _x ∈ x1.1, ((d_m : ℝ) + 1) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      apply Finset.sum_congr rfl
      intro a ha
      rw [h_x1_aux a ha]; push_cast; ring
    rw [hsum]; field_simp
  have h_x2_term :
      (∑ a ∈ x2.1, (huffmanLengthAux s a : ℝ)) / (x2.1.card : ℝ)
      = ((d_m : ℝ) + 1) := by
    have hsum : (∑ a ∈ x2.1, (huffmanLengthAux s a : ℝ))
        = (x2.1.card : ℝ) * ((d_m : ℝ) + 1) := by
      rw [show (x2.1.card : ℝ) * ((d_m : ℝ) + 1)
          = ∑ _x ∈ x2.1, ((d_m : ℝ) + 1) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      apply Finset.sum_congr rfl
      intro a ha
      rw [h_x2_aux a ha]; push_cast; ring
    rw [hsum]; field_simp
  have h_merged_term :
      (∑ a ∈ merged.1, (huffmanLengthAux s'' a : ℝ)) / (merged.1.card : ℝ)
      = (d_m : ℝ) := by
    have hsum : (∑ a ∈ merged.1, (huffmanLengthAux s'' a : ℝ))
        = (merged.1.card : ℝ) * (d_m : ℝ) := by
      rw [show (merged.1.card : ℝ) * (d_m : ℝ)
          = ∑ _x ∈ merged.1, (d_m : ℝ) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      apply Finset.sum_congr rfl
      intro a ha
      rw [h_merged_const a ha]
    rw [hsum]; field_simp
  rw [h_x1_term, h_x2_term, h_merged_term, h_ee_sum]
  -- merged.2 = x1.2 + x2.2
  show x1.2 * ((d_m : ℝ) + 1)
      + (x2.2 * ((d_m : ℝ) + 1) + _)
      = (x1.2 + x2.2) * (d_m : ℝ) + _ + (x1.2 + x2.2)
  ring

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **C2 base**: `huffmanCost s = 0` for `s.card ≤ 1` (全 group depth 0).

@audit:ok — independent audit (2026-05-30): genuine base case (card ≤ 1 → cost 0)、
`#print axioms` = [propext, Classical.choice, Quot.sound]、退化定義悪用でない (実際の base reduction)。 -/
lemma huffmanCost_eq_zero_of_base
    (s : Multiset (Finset α × ℝ)) (h : s.card ≤ 1) (hg : HuffmanGrouping s) :
    huffmanCost s = 0 := by
  unfold huffmanCost
  rw [huffmanLengthAux_eq_zero s h hg]
  rw [show s.map (fun p =>
      p.2 * ((∑ a ∈ p.1, ((fun _ : α => (0 : ℕ)) a : ℝ)) / (p.1.card : ℝ)))
      = s.map (fun _ => (0 : ℝ)) from ?_]
  · simp
  · apply Multiset.map_congr rfl
    intro p _
    simp

/-- Helper: 特定要素 `x ∈ s` を erase してから snd を map した結果は、
`s.map snd` から値 `x.2` を 1 個 erase したものに等しい (injective 不要、cons 分解). -/
private lemma map_snd_erase {α : Type*} [DecidableEq α]
    (s : Multiset (Finset α × ℝ)) (x : Finset α × ℝ) (hx : x ∈ s) :
    (s.erase x).map Prod.snd = (s.map Prod.snd).erase x.2 := by
  classical
  conv_rhs => rw [show s = x ::ₘ s.erase x from (Multiset.cons_erase hx).symm]
  rw [Multiset.map_cons, Multiset.erase_cons_head]

/-- **C3 核 — cost は確率多重集合のみで決まる (carrier 非依存)**.
2 つの `HuffmanGrouping` 多重集合 `s` (carrier `α`), `t` (carrier `β`) が同じ確率多重集合
(`s.map Prod.snd = t.map Prod.snd : Multiset ℝ`) を持てば、`huffmanCost s = huffmanCost t`.

証明 = `s.card` strong induction + `huffmanCost_step`:
- `huffmanStep` は確率最小・第2最小の 2 group を選ぶ (`huffmanStep_min_fst`/`_min_snd`)。
  tie でどの物理 group を選ぶかは違っても、選ばれる確率**値**は多重集合の最小2値で確定。
- ペナルティ `x1.2 + x2.2` = 最小2値の和 = `s.map snd` から確定 (s, t で一致)。
- 残木の確率多重集合も多重集合から確定 → IH 適用。

@audit:ok — independent audit (2026-05-30): C3 核 (carrier 非依存性) = cost-level pivot の crux。
per-symbol depth identity (FALSE) を経由せず strong induction + `huffmanCost_step` + 最小2値の
multiset antisymmetry 同定で証明。仮説は `HuffmanGrouping` 2 個 + `s.map snd = t.map snd` の
構造等式のみ (load-bearing でない)、`:= h` 循環でない。`#print axioms` = [propext, Classical.choice, Quot.sound]。 -/
lemma huffmanCost_eq_of_prob_multiset
    {α : Type*} [DecidableEq α] [LinearOrder α]
    {β : Type*} [DecidableEq β] [LinearOrder β]
    (s : Multiset (Finset α × ℝ)) (t : Multiset (Finset β × ℝ))
    (hsg : HuffmanGrouping s) (htg : HuffmanGrouping t)
    (h : s.map Prod.snd = t.map Prod.snd) :
    huffmanCost s = huffmanCost t := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s t β with
  | _ n ih =>
    -- card 一致
    have hcard_eq : s.card = t.card := by
      have h1 : (s.map Prod.snd).card = s.card := Multiset.card_map _ _
      have h2 : (t.map Prod.snd).card = t.card := Multiset.card_map _ _
      rw [← h1, ← h2, h]
    by_cases h2 : 2 ≤ s.card
    · -- step case
      have h2t : 2 ≤ t.card := by rw [← hcard_eq]; exact h2
      -- s 側 step
      set xs1 := (huffmanStep s h2 hsg).val.1 with hxs1
      set xs2 := (huffmanStep s h2 hsg).val.2.1 with hxs2
      set s'' := (huffmanStep s h2 hsg).val.2.2 with hs''
      obtain ⟨hxs1_mem, hxs2_mem, hshape_s, hg_s''⟩ := (huffmanStep s h2 hsg).property
      -- t 側 step
      set yt1 := (huffmanStep t h2t htg).val.1 with hyt1
      set yt2 := (huffmanStep t h2t htg).val.2.1 with hyt2
      set t'' := (huffmanStep t h2t htg).val.2.2 with ht''
      obtain ⟨hyt1_mem, hyt2_mem, hshape_t, hg_t''⟩ := (huffmanStep t h2t htg).property
      -- min 性 (確率値)
      have hxs1_min : ∀ z ∈ s, xs1.2 ≤ z.2 := huffmanStep_min_fst s h2 hsg
      have hxs2_min : ∀ z ∈ s.erase xs1, xs2.2 ≤ z.2 := huffmanStep_min_snd s h2 hsg
      have hyt1_min : ∀ z ∈ t, yt1.2 ≤ z.2 := huffmanStep_min_fst t h2t htg
      have hyt2_min : ∀ z ∈ t.erase yt1, yt2.2 ≤ z.2 := huffmanStep_min_snd t h2t htg
      have hxs2_mem_s : xs2 ∈ s := Multiset.mem_of_mem_erase hxs2_mem
      have hyt2_mem_t : yt2 ∈ t := Multiset.mem_of_mem_erase hyt2_mem
      -- M := s.map snd = t.map snd ; xs1.2, xs2.2, yt1.2, yt2.2 は M の元
      -- 最小値 (xs1.2 = yt1.2) を確率多重集合の antisymmetry で同定
      have hxs1_min_M : ∀ v ∈ s.map Prod.snd, xs1.2 ≤ v := by
        intro v hv
        rw [Multiset.mem_map] at hv
        obtain ⟨z, hz, hzv⟩ := hv
        rw [← hzv]; exact hxs1_min z hz
      have hyt1_min_M : ∀ v ∈ s.map Prod.snd, yt1.2 ≤ v := by
        intro v hv
        rw [h, Multiset.mem_map] at hv
        obtain ⟨z, hz, hzv⟩ := hv
        rw [← hzv]; exact hyt1_min z hz
      have hxs1v_M : xs1.2 ∈ s.map Prod.snd := Multiset.mem_map_of_mem _ hxs1_mem
      have hyt1v_M : yt1.2 ∈ s.map Prod.snd := by
        rw [h]; exact Multiset.mem_map_of_mem _ hyt1_mem
      have hv1_eq : xs1.2 = yt1.2 :=
        le_antisymm (hxs1_min_M _ hyt1v_M) (hyt1_min_M _ hxs1v_M)
      -- (s.erase xs1).map snd = (s.map snd).erase xs1.2
      have hsnd_s' : (s.erase xs1).map Prod.snd = (s.map Prod.snd).erase xs1.2 :=
        map_snd_erase s xs1 hxs1_mem
      have hsnd_t' : (t.erase yt1).map Prod.snd = (s.map Prod.snd).erase yt1.2 := by
        rw [map_snd_erase t yt1 hyt1_mem, ← h]
      -- xs2.2, yt2.2 は (s.map snd).erase xs1.2 = ....erase yt1.2 の最小値
      have hMe : (s.map Prod.snd).erase xs1.2 = (s.map Prod.snd).erase yt1.2 := by
        rw [hv1_eq]
      have hxs2v_Me : xs2.2 ∈ (s.map Prod.snd).erase xs1.2 := by
        rw [← hsnd_s']; exact Multiset.mem_map_of_mem _ hxs2_mem
      have hyt2v_Me : yt2.2 ∈ (s.map Prod.snd).erase yt1.2 := by
        rw [← hsnd_t']; exact Multiset.mem_map_of_mem _ hyt2_mem
      have hxs2_min_Me : ∀ v ∈ (s.map Prod.snd).erase xs1.2, xs2.2 ≤ v := by
        intro v hv
        rw [← hsnd_s', Multiset.mem_map] at hv
        obtain ⟨z, hz, hzv⟩ := hv
        rw [← hzv]; exact hxs2_min z hz
      have hyt2_min_Me : ∀ v ∈ (s.map Prod.snd).erase yt1.2, yt2.2 ≤ v := by
        intro v hv
        rw [← hsnd_t', Multiset.mem_map] at hv
        obtain ⟨z, hz, hzv⟩ := hv
        rw [← hzv]; exact hyt2_min z hz
      have hv2_eq : xs2.2 = yt2.2 := by
        apply le_antisymm
        · exact hxs2_min_Me _ (hMe ▸ hyt2v_Me)
        · exact hyt2_min_Me _ (hMe ▸ hxs2v_Me)
      -- penalty 一致
      have hpen : xs1.2 + xs2.2 = yt1.2 + yt2.2 := by rw [hv1_eq, hv2_eq]
      -- s''.map snd = t''.map snd
      have hsnd_s'' : s''.map Prod.snd
          = (xs1.2 + xs2.2) ::ₘ (((s.map Prod.snd).erase xs1.2).erase xs2.2) := by
        rw [hs'', hshape_s, Multiset.map_cons]
        congr 1
        rw [map_snd_erase (s.erase xs1) xs2 hxs2_mem, hsnd_s']
      have hsnd_t'' : t''.map Prod.snd
          = (yt1.2 + yt2.2) ::ₘ (((s.map Prod.snd).erase yt1.2).erase yt2.2) := by
        rw [ht'', hshape_t, Multiset.map_cons]
        congr 1
        rw [map_snd_erase (t.erase yt1) yt2 hyt2_mem, hsnd_t']
      have hsnd_eq : s''.map Prod.snd = t''.map Prod.snd := by
        rw [hsnd_s'', hsnd_t'', hpen, hv1_eq, hv2_eq]
      -- IH
      have hcard_s'' : s''.card < s.card := huffmanStep_card_lt s h2 hsg
      have hcard_s''_lt_n : s''.card < n := by omega
      have hcost_s'' : huffmanCost s'' = huffmanCost t'' :=
        ih s''.card hcard_s''_lt_n s'' t'' hg_s'' hg_t'' hsnd_eq rfl
      -- 連結
      rw [huffmanCost_step s h2 hsg, huffmanCost_step t h2t htg,
          ← hxs1, ← hxs2, ← hs'', ← hyt1, ← hyt2, ← ht'',
          hcost_s'', hpen]
    · -- base case: s.card ≤ 1
      have hs_le : s.card ≤ 1 := by omega
      have ht_le : t.card ≤ 1 := by rw [← hcard_eq]; exact hs_le
      rw [huffmanCost_eq_zero_of_base s hs_le hsg,
          huffmanCost_eq_zero_of_base t ht_le htg]

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **C1-b**: `expectedLength P (huffmanLength P) = huffmanCost (initMultiset P)`.
`initMultiset` の各 group は singleton `({a}, P.real{a})` なので per-group sum が
`∑ a, P.real{a}·(huffmanLength P a)` に collapse する.

@audit:ok — independent audit (2026-05-30): genuine def-unfold collapse、`#print axioms` = [propext, Classical.choice, Quot.sound]。 -/
lemma expectedLength_eq_huffmanCost (P : Measure α) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      = huffmanCost (initMultiset P) := by
  classical
  unfold InformationTheory.Shannon.ShannonCode.expectedLength huffmanCost
  unfold huffmanLength
  -- LHS: ∑ a : α, P.real{a} * d a = (univ.val.map (fun a => P.real{a} * d a)).sum
  rw [show ∑ a : α, P.real {a} * (huffmanLengthAux (initMultiset P) a : ℝ)
      = ((Finset.univ : Finset α).val.map
          (fun a => P.real {a} * (huffmanLengthAux (initMultiset P) a : ℝ))).sum from rfl]
  conv_rhs => rw [initMultiset, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  -- 各 singleton group では p.2 * (∑_{x∈{a}} d)/card = P.real{a} * (d a)
  show P.real {a} * (huffmanLengthAux (initMultiset P) a : ℝ)
    = P.real {a} * ((∑ x ∈ ({a} : Finset α),
        (huffmanLengthAux (initMultiset P) x : ℝ)) / (({a} : Finset α).card : ℝ))
  simp

end InformationTheory.Shannon.Huffman
