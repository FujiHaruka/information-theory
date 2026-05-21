import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Real
import Common2026.Shannon.Huffman

/-!
# Huffman 最適性 主定理 (T1-A' Cover-Thomas Theorem 5.8.1)

T1-A (`Common2026/Shannon/Huffman.lean`) で publish された `huffmanLength` の **最適性**
(任意 Kraft-feasible 語長関数 `l` との比較形) を、sibling property + n → n-1 induction で
証明する。

## Approach

設計判断は `docs/shannon/huffman-optimality-moonshot-plan.md` §設計判断 (C-1〜C-4) で確定済:

* **C-1**: ハイブリッド設計 — Subtype `α' := { x : α // x ≠ b }` + `α` 型不変 induction +
  `Nat.strong_induction_on` の組み合わせ。Quotient 経路は採用しない。
* **C-2**: sibling property は統合形 (`exists_sibling_min_pair`) で publish、内部分解は private.
* **C-3**: merged measure は point-mass 直接構成 (`Measure.map` / `restrict` 経由しない).
* **C-4**: 撤退ライン発動の事前枠を判断ログ #0 で予約済.

## Phase 0 結果 (skeleton 起動時)

`Subtype.instMeasurableSingletonClass`
(`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:196`) が auto-derive
で `α' := { x : α // x ≠ b }` に継承される。撤退ライン §G-2 (`MeasurableSingletonClass α'`
自前付与必要) は **発動しない**。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Phase 1 helpers — Phase 2 (sibling property) 用 -/

omit [MeasurableSingletonClass α] in
/-- **Helper (Phase 2.1)**: `huffmanLength P` の最深 leaf が取れる. `Fintype.card α ≥ 1` から
`Finset.univ.Nonempty` で `Finset.exists_max_image` を起動. -/
theorem exists_deepest_leaf (P : Measure α) (_h_card : 1 ≤ Fintype.card α) :
    ∃ a : α, ∀ c : α, huffmanLength P c ≤ huffmanLength P a := by
  classical
  have hne : (Finset.univ : Finset α).Nonempty := Finset.univ_nonempty
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset α)
    (fun c => huffmanLength P c) hne
  exact ⟨a, fun c => ha c (Finset.mem_univ _)⟩

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **Helper (Phase 2.2-2.4)**: `initMultiset P` の `huffmanStep` で取り出される
`(x1, x2)` ペアは singleton group `({a}, P.real {a})`, `({b}, P.real {b})` の形を持つ.
さらに以下を満たす:

* `a ≠ b`
* `huffmanLength P a = huffmanLength P b` (両者 merged group に属し const-on-group で同値)
* `P.real {a}, P.real {b}` は **`Multiset.exists_min_image` で取り出された最小 2 個**.

これにより plan §2.2-2.4 (Cover-Thomas Lemma 5.8.1 (ii)) を `huffmanStep` 構成から直接展開. -/
private theorem huffmanStep_initMultiset_sibling
    (P : Measure α) (h_card : 2 ≤ Fintype.card α) :
    ∃ a b : α, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, P.real {a} ≤ P.real {c}) ∧
      (∀ c, c ≠ a → P.real {b} ≤ P.real {c}) := by
  classical
  -- (initMultiset P).card = Fintype.card α ≥ 2
  have hcard_init : (initMultiset P).card = Fintype.card α := by
    unfold initMultiset; rw [Multiset.card_map]; rfl
  have h_init_card : 2 ≤ (initMultiset P).card := by rw [hcard_init]; exact h_card
  have h_init_grouping : HuffmanGrouping (initMultiset P) := initMultiset_huffmanGrouping P
  -- huffmanStep 適用
  set step := (huffmanStep (initMultiset P) h_init_card h_init_grouping).val with hstep_def
  obtain ⟨hx1_mem, hx2_mem, hshape, hg''⟩ :=
    huffmanStep_spec (initMultiset P) h_init_card h_init_grouping
  -- x1 ∈ initMultiset P ⇒ ∃ a, x1 = ({a}, P.real {a})
  have hx1_form : ∃ a : α, step.1 = ({a}, P.real {a}) := by
    unfold initMultiset at hx1_mem
    rw [Multiset.mem_map] at hx1_mem
    obtain ⟨a, _, hae⟩ := hx1_mem
    exact ⟨a, hae.symm⟩
  obtain ⟨a, hx1_eq⟩ := hx1_form
  -- x2 ∈ (initMultiset P).erase x1 ⊆ initMultiset P ⇒ ∃ b, x2 = ({b}, P.real {b})
  have hx2_mem_init : step.2.1 ∈ initMultiset P := Multiset.mem_of_mem_erase hx2_mem
  have hx2_form : ∃ b : α, step.2.1 = ({b}, P.real {b}) := by
    unfold initMultiset at hx2_mem_init
    rw [Multiset.mem_map] at hx2_mem_init
    obtain ⟨b, _, hbe⟩ := hx2_mem_init
    exact ⟨b, hbe.symm⟩
  obtain ⟨b, hx2_eq⟩ := hx2_form
  -- x1 ≠ x2: x2 ∈ s.erase x1 + Nodup ⇒ x1 ≠ x2 (otherwise x2 ∉ s.erase x2)
  have hx12_ne : step.1 ≠ step.2.1 := by
    intro heq
    rw [heq] at hx2_mem
    exact h_init_grouping.nodup.notMem_erase hx2_mem
  have hab : a ≠ b := by
    intro heq
    apply hx12_ne
    rw [hx1_eq, hx2_eq, heq]
  -- 最小性: 決定化後は publish 済 accessor (`huffmanStep_min_fst/_min_snd`、
  -- groupKey min の第 1 キー射影で確率 `≤` を返す) から取り出す. statement 不変.
  have hmin1 : ∀ z ∈ initMultiset P, step.1.2 ≤ z.2 :=
    huffmanStep_min_fst (initMultiset P) h_init_card h_init_grouping
  have hmin2 : ∀ z ∈ (initMultiset P).erase step.1, step.2.1.2 ≤ z.2 :=
    huffmanStep_min_snd (initMultiset P) h_init_card h_init_grouping
  refine ⟨a, b, hab, ?_, ?_, ?_⟩
  · -- huffmanLength P a = huffmanLength P b
    -- 両者 ∈ step.1.1 ∪ step.2.1.1 (a ∈ step.1.1 = {a}, b ∈ step.2.1.1 = {b})
    have ha_AB : a ∈ step.1.1 ∨ a ∈ step.2.1.1 := by
      left; rw [hx1_eq]; exact Finset.mem_singleton.mpr rfl
    have hb_AB : b ∈ step.1.1 ∨ b ∈ step.2.1.1 := by
      right; rw [hx2_eq]; exact Finset.mem_singleton.mpr rfl
    unfold huffmanLength
    rw [huffmanLengthAux_step_merged (initMultiset P) h_init_card h_init_grouping ha_AB,
        huffmanLengthAux_step_merged (initMultiset P) h_init_card h_init_grouping hb_AB]
    -- 残: huffmanLengthAux step.2.2 a = huffmanLengthAux step.2.2 b
    -- merged group ∈ step.2.2, a, b ∈ merged.1 = step.1.1 ∪ step.2.1.1
    have hmerged_in : (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2) ∈ step.2.2 := by
      rw [hshape]; exact Multiset.mem_cons_self _ _
    have ha_merged : a ∈ (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2).1 := by
      simp only
      apply Finset.mem_union_left
      rw [hx1_eq]; exact Finset.mem_singleton.mpr rfl
    have hb_merged : b ∈ (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2).1 := by
      simp only
      apply Finset.mem_union_right
      rw [hx2_eq]; exact Finset.mem_singleton.mpr rfl
    rw [huffmanLengthAux_const_on_group step.2.2 hg''
      (step.1.1 ∪ step.2.1.1, step.1.2 + step.2.1.2) hmerged_in a b ha_merged hb_merged]
  · -- ∀ c, P.real {a} ≤ P.real {c}
    intro c
    -- ({c}, P.real {c}) ∈ initMultiset P
    have hc_mem : ({c}, P.real {c}) ∈ initMultiset P := by
      unfold initMultiset
      rw [Multiset.mem_map]
      exact ⟨c, Finset.mem_univ _, rfl⟩
    have := hmin1 ({c}, P.real {c}) hc_mem
    -- step.1.2 = P.real {a} (from hx1_eq)
    rw [hx1_eq] at this
    exact this
  · -- ∀ c, c ≠ a → P.real {b} ≤ P.real {c}
    intro c hca
    have hc_mem_init : ({c}, P.real {c}) ∈ initMultiset P := by
      unfold initMultiset
      rw [Multiset.mem_map]
      exact ⟨c, Finset.mem_univ _, rfl⟩
    -- ({c}, P.real {c}) ≠ step.1 = ({a}, P.real {a})
    have hc_ne_step1 : ({c}, P.real {c}) ≠ step.1 := by
      rw [hx1_eq]
      intro heq
      apply hca
      simp only [Prod.mk.injEq, Finset.singleton_inj] at heq
      exact heq.1
    have hc_mem_erase : ({c}, P.real {c}) ∈ (initMultiset P).erase step.1 :=
      (Multiset.mem_erase_of_ne hc_ne_step1).mpr hc_mem_init
    have := hmin2 ({c}, P.real {c}) hc_mem_erase
    rw [hx2_eq] at this
    exact this

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **Helper (Phase 2.5)**: 最小 2 確率ペアが存在し、Huffman 語長が等しいことの bridge.
`exists_sibling_min_pair` 本体で使用.

**strong 形**: `a` が global-min (`∀ c, P{a} ≤ P{c}`) かつ `b` が残りの min
(`∀ c, c ≠ a → P{b} ≤ P{c}`). これは `huffmanStep_initMultiset_sibling` が返す情報を
そのまま伝播する (T1-A'' interface refactor で disjunctive 形から強化). -/
theorem huffmanLength_eq_of_min_prob_pair
    (P : Measure α) [IsProbabilityMeasure P] (_hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    ∃ a b : α, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, P.real {a} ≤ P.real {c}) ∧
      (∀ c, c ≠ a → P.real {b} ≤ P.real {c}) :=
  huffmanStep_initMultiset_sibling P h_card

/-! ### Sibling property (Cover-Thomas Lemma 5.8.1) -/

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **Sibling property (Cover-Thomas Lemma 5.8.1)** — intermediate lemma (案 B pivot).

最小 2 確率 element の Huffman 語長が等しい. 最深性条項 `(∀ c, huffmanLength P c ≤
huffmanLength P a)` は本 signature には含めず、Phase 4 主定理側で `exists_deepest_leaf`
を別途呼ぶ. Cover-Thomas Lemma 5.8.1 (i) の standard 証明 (`l` 側 swap normalization)
と整合する形.

**strong 形** (T1-A'' interface refactor): `a` = global-min, `b` = rest-min を返す.
旧 disjunctive 形 (`∀ c, P{a} ≤ P{c} ∨ P{b} ≤ P{c}`) は swap 論法を閉じられず
強形 `huffmanLength_optimal` に到達できないため、call site が実際に供給する情報
(`huffmanStep_initMultiset_sibling`) をそのまま publish する. -/
theorem exists_sibling_min_pair
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    ∃ a b : α, a ≠ b ∧ huffmanLength P a = huffmanLength P b ∧
      (∀ c, P.real {a} ≤ P.real {c}) ∧
      (∀ c, c ≠ a → P.real {b} ≤ P.real {c}) :=
  huffmanLength_eq_of_min_prob_pair P hP h_card

/-! ### Phase 3 helpers — Subtype `α'` lift bridges -/

/-- **Helper (Phase 3.2)**: merged measure `P'` on `α' := { x : α // x ≠ b }`.

C-3: point-mass 直接構成 (`Measure.map` / `Measure.restrict` 経由しない). 各 singleton
`{⟨x, hx⟩}` への measure 値は `if x = a then P.real {a} + P.real {b} else P.real {x}`.

設計 (Mathlib-shape-driven): `Measure.sum_smul_dirac_singleton`
(`Mathlib/MeasureTheory/Measure/Dirac.lean:140`) を結論形に取れるよう、
`Measure.sum (fun x => f x • Measure.dirac x)` の正準形で構成. -/
noncomputable def mergedMeasure (P : Measure α) (a b : α) (_hab : a ≠ b) :
    Measure { x : α // x ≠ b } :=
  Measure.sum (fun x : { x : α // x ≠ b } =>
    (if x.val = a then P {a} + P {b} else P {x.val}) • Measure.dirac x)

omit [Fintype α] [LinearOrder α] [Nonempty α] in
/-- **Helper (Phase 3.2.2)**: `mergedMeasure` の `Measure.real` 形式. -/
lemma mergedMeasure_real (P : Measure α) [IsFiniteMeasure P] (a b : α) (hab : a ≠ b)
    (x : { x : α // x ≠ b }) :
    (mergedMeasure P a b hab).real {x} =
      if x.val = a then P.real {a} + P.real {b} else P.real {x.val} := by
  -- 1: (mergedMeasure P a b hab) {x} = if x.val = a then P {a} + P {b} else P {x.val}
  have hmap : (mergedMeasure P a b hab) {x} =
      (if x.val = a then P {a} + P {b} else P {x.val}) := by
    unfold mergedMeasure
    exact Measure.sum_smul_dirac_singleton
  -- 2: real = toReal of (1)
  unfold Measure.real
  rw [hmap]
  by_cases hxa : x.val = a
  · simp only [hxa, if_true]
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  · simp only [hxa, if_false]

omit [Nonempty α] in
/-- **Helper (Phase 3.3) — Bridge L (proof-pivot-advisor (ii))**: Huffman 側 expected length
を sibling pair `(a, b)` の取り出し + 任意の `L' : α' → ℕ` の合成形に分解した等式.

proof-pivot-advisor 推奨 (ii) で signature を **sibling-driven 分解形** に再 shape.
`huffmanLength (mergedMeasure P a b hab)` を直接呼ばず、`L'` を `h_L'_link` の制約で
parametrize する。`huffmanLength (mergedMeasure P a b hab) = L'` の同一視は Phase 4 で別補題に切り出し. -/
lemma huffmanLength_bridge_L
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) (a b : α) (hab : a ≠ b)
    (h_sibling : huffmanLength P a = huffmanLength P b)
    (L' : { x : α // x ≠ b } → ℕ)
    (h_L'_link : ∀ x : { x : α // x ≠ b },
      L' x = if x.val = a then huffmanLength P a - 1 else huffmanLength P x.val) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      = InformationTheory.Shannon.ShannonCode.expectedLength
          (mergedMeasure P a b hab) L'
        + (P.real {a} + P.real {b}) := by
  classical
  set L := huffmanLength P with hL_def
  -- L a ≥ 1
  have hLa_pos : 0 < L a := huffmanLength_pos P hP h_card a
  have hLa_ge_one : 1 ≤ L a := hLa_pos
  -- ((L a - 1 : ℕ) : ℝ) = (L a : ℝ) - 1
  have hLa_cast : ((L a - 1 : ℕ) : ℝ) = (L a : ℝ) - 1 := by
    rw [Nat.cast_sub hLa_ge_one]; norm_num
  -- expectedLength の展開
  unfold InformationTheory.Shannon.ShannonCode.expectedLength
  -- LHS: ∑ x : α, P.real{x} * L x. b の項を分離.
  have hLHS_split :
      (∑ x : α, P.real {x} * (L x : ℝ))
        = (∑ x ∈ (Finset.univ : Finset α).erase b, P.real {x} * (L x : ℝ))
            + P.real {b} * (L b : ℝ) := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ b)]
  rw [hLHS_split]
  -- b を a に同一視 (h_sibling: L a = L b)
  have hLb_eq : (L b : ℝ) = (L a : ℝ) := by
    rw [h_sibling]
  rw [hLb_eq]
  -- Subtype α' へ移行: ∑ x ∈ univ.erase b, f x = ∑ x : { y // y ≠ b }, f x.val
  have h_erase_iff : ∀ x : α, x ∈ (Finset.univ : Finset α).erase b ↔ x ≠ b := by
    intro x
    simp [Finset.mem_erase]
  have h_sum_subtype :
      (∑ x ∈ (Finset.univ : Finset α).erase b, P.real {x} * (L x : ℝ))
        = ∑ x : { y : α // y ≠ b }, P.real {x.val} * (L x.val : ℝ) := by
    rw [Finset.sum_subtype (Finset.univ.erase b) h_erase_iff
      (fun x => P.real {x} * (L x : ℝ))]
  rw [h_sum_subtype]
  -- RHS: ∑ x : α', mergedReal{x} * L' x の展開
  -- a' := ⟨a, hab⟩ : α' で項分離
  set a' : { y : α // y ≠ b } := ⟨a, hab⟩ with ha'_def
  have ha'_mem : a' ∈ (Finset.univ : Finset { y : α // y ≠ b }) := Finset.mem_univ _
  -- L' a' = L a - 1, ∀ x : α', x ≠ a' → L' x = L x.val
  have hL'_a' : L' a' = L a - 1 := by
    rw [h_L'_link a']; simp [ha'_def]
  have hL'_other : ∀ x : { y : α // y ≠ b }, x ≠ a' → L' x = L x.val := by
    intro x hx
    rw [h_L'_link x]
    have hxv_ne_a : x.val ≠ a := by
      intro h
      apply hx
      apply Subtype.ext
      exact h
    simp [hxv_ne_a]
  -- merged measure の real 値
  have h_merged_a' : (mergedMeasure P a b hab).real {a'} = P.real {a} + P.real {b} := by
    rw [mergedMeasure_real P a b hab a']; simp [ha'_def]
  have h_merged_other : ∀ x : { y : α // y ≠ b }, x ≠ a' →
      (mergedMeasure P a b hab).real {x} = P.real {x.val} := by
    intro x hx
    rw [mergedMeasure_real P a b hab x]
    have hxv_ne_a : x.val ≠ a := by
      intro h; apply hx; apply Subtype.ext; exact h
    simp [hxv_ne_a]
  -- RHS の展開: a' の項を分離
  have hRHS_split :
      (∑ x : { y : α // y ≠ b }, (mergedMeasure P a b hab).real {x} * (L' x : ℝ))
        = (mergedMeasure P a b hab).real {a'} * (L' a' : ℝ)
          + ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
              (mergedMeasure P a b hab).real {x} * (L' x : ℝ) := by
    rw [← Finset.add_sum_erase _ _ ha'_mem]
  rw [hRHS_split, h_merged_a', hL'_a', hLa_cast]
  -- erase a' 上の sum を L' = L で書き換え
  have h_sum_erase :
      (∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
          (mergedMeasure P a b hab).real {x} * (L' x : ℝ))
        = ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
            P.real {x.val} * (L x.val : ℝ) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx_ne : x ≠ a' := Finset.ne_of_mem_erase hx
    rw [h_merged_other x hx_ne, hL'_other x hx_ne]
  rw [h_sum_erase]
  -- LHS の sum も a' で項分離
  have hLHS_subtype_split :
      (∑ x : { y : α // y ≠ b }, P.real {x.val} * (L x.val : ℝ))
        = P.real {a} * (L a : ℝ)
          + ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
              P.real {x.val} * (L x.val : ℝ) := by
    rw [← Finset.add_sum_erase _ _ ha'_mem]
  rw [hLHS_subtype_split]
  -- 残: P.real{a}*L a + ∑erase + P.real{b}*L a
  --   = (P.real{a}+P.real{b})*(L a - 1) + ∑erase + (P.real{a}+P.real{b})
  ring

omit [LinearOrder α] [Nonempty α] in
/-- **Helper (Phase 3.4) — Bridge R (鍵 lemma、proof-pivot-advisor (A))**: 任意 `l` 側の
expected length が merged 側 + `(P {a} + P {b})` の上から bound される不等式.

proof-pivot-advisor 推奨 (A) で `0 < l' x` clause を削除 (IH 適用に不要、Kraft + expectedLength
ineq のみで主定理 induction を回せる).

`liftL l a b : { x : α // x ≠ b } → ℕ` は `if x.val = a then l a - 1 else l x.val`
(+1 ペナルティ吸収) として helper 内で定義. sibling property で正規化済 `l a = l b` を使う. -/
lemma expectedLength_bridge_R
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (a b : α) (hab : a ≠ b)
    (h_lab : l a = l b)
    (h_la_ge_2 : 2 ≤ l a)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1) :
    ∃ l' : { x : α // x ≠ b } → ℕ,
      (∀ x, 0 < l' x) ∧
      (∑ x : { x : α // x ≠ b }, ((2 : ℝ)) ^ (-(l' x : ℤ)) ≤ 1) ∧
      InformationTheory.Shannon.ShannonCode.expectedLength P l
        = InformationTheory.Shannon.ShannonCode.expectedLength
            (mergedMeasure P a b hab) l'
          + (P.real {a} + P.real {b}) := by
  classical
  -- l' の定義
  refine ⟨fun x => if x.val = a then l a - 1 else l x.val, ?_, ?_, ?_⟩
  · -- positivity: x.val = a 側は l a - 1 ≥ 1; otherwise hl_pos.
    intro x
    by_cases hxa : x.val = a
    · simp only [hxa, if_true]; omega
    · simp only [hxa, if_false]; exact hl_pos x.val
  · -- Kraft inequality
    set l' : { x : α // x ≠ b } → ℕ :=
      fun x => if x.val = a then l a - 1 else l x.val with hl'_def
    set a' : { y : α // y ≠ b } := ⟨a, hab⟩ with ha'_def
    have ha'_mem : a' ∈ (Finset.univ : Finset { y : α // y ≠ b }) := Finset.mem_univ _
    have hla_ge_one : 1 ≤ l a := hl_pos a
    -- l' a' = l a - 1, ∀ x : α', x ≠ a' → l' x = l x.val
    have hl'_a' : l' a' = l a - 1 := by
      simp [hl'_def, ha'_def]
    have hl'_other : ∀ x : { y : α // y ≠ b }, x ≠ a' → l' x = l x.val := by
      intro x hx
      have hxv_ne_a : x.val ≠ a := by
        intro h; apply hx; apply Subtype.ext; exact h
      simp [hl'_def, hxv_ne_a]
    -- 2^(-(l a - 1 : ℤ)) = 2 * 2^(-(l a : ℤ))
    have hpow_succ : ((2 : ℝ)) ^ (-((l a - 1 : ℕ) : ℤ))
        = 2 * ((2 : ℝ)) ^ (-(l a : ℤ)) := by
      rw [Nat.cast_sub hla_ge_one]
      push_cast
      rw [show -((l a : ℤ) - 1) = 1 + -(l a : ℤ) by ring,
          zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      simp
    -- ∑_{x:α'} 2^{-l'(x)} の展開
    have h_sum_lhs :
        (∑ x : { x : α // x ≠ b }, ((2 : ℝ)) ^ (-(l' x : ℤ)))
          = ((2 : ℝ)) ^ (-((l a - 1 : ℕ) : ℤ))
            + ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
                ((2 : ℝ)) ^ (-(l x.val : ℤ)) := by
      rw [← Finset.add_sum_erase _ _ ha'_mem, hl'_a']
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hx_ne : x ≠ a' := Finset.ne_of_mem_erase hx
      rw [hl'_other x hx_ne]
    rw [h_sum_lhs, hpow_succ]
    -- ∑_{x:α} 2^{-l(x)} の方を展開: b の項を分離、ついで a の項を分離
    have h_erase_iff : ∀ x : α, x ∈ (Finset.univ : Finset α).erase b ↔ x ≠ b := by
      intro x; simp [Finset.mem_erase]
    have h_sum_α_split :
        (∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)))
          = ((2 : ℝ)) ^ (-(l b : ℤ))
            + ∑ x : { y : α // y ≠ b }, ((2 : ℝ)) ^ (-(l x.val : ℤ)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b),
          Finset.sum_subtype (Finset.univ.erase b) h_erase_iff
            (fun x => ((2 : ℝ)) ^ (-(l x : ℤ)))]
    -- ∑_{x:α'} 2^{-l(x.val)} の中で a' の項を更に分離
    have h_sum_α'_split :
        (∑ x : { y : α // y ≠ b }, ((2 : ℝ)) ^ (-(l x.val : ℤ)))
          = ((2 : ℝ)) ^ (-(l a : ℤ))
            + ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
                ((2 : ℝ)) ^ (-(l x.val : ℤ)) := by
      rw [← Finset.add_sum_erase _ _ ha'_mem]
    rw [h_sum_α'_split] at h_sum_α_split
    -- ∑_{x:α} = 2^{-l b} + 2^{-l a} + ∑_erase
    -- l a = l b なので: = 2 * 2^{-l a} + ∑_erase
    -- LHS: 2 * 2^{-l a} + ∑_erase ≤ 1 (= hl_kraft after rewrite)
    have h_lb_la : ((2 : ℝ)) ^ (-(l b : ℤ)) = ((2 : ℝ)) ^ (-(l a : ℤ)) := by
      rw [h_lab]
    rw [h_lb_la] at h_sum_α_split
    -- ∑_α = 2^{-l a} + (2^{-l a} + ∑_erase) = 2*2^{-l a} + ∑_erase
    have h_final : 2 * ((2 : ℝ)) ^ (-(l a : ℤ))
        + ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
            ((2 : ℝ)) ^ (-(l x.val : ℤ))
        = ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) := by
      rw [h_sum_α_split]; ring
    rw [h_final]
    exact hl_kraft
  · -- expectedLength equality
    set l' : { x : α // x ≠ b } → ℕ :=
      fun x => if x.val = a then l a - 1 else l x.val with hl'_def
    set a' : { y : α // y ≠ b } := ⟨a, hab⟩ with ha'_def
    have ha'_mem : a' ∈ (Finset.univ : Finset { y : α // y ≠ b }) := Finset.mem_univ _
    have hla_ge_one : 1 ≤ l a := hl_pos a
    have hla_cast : ((l a - 1 : ℕ) : ℝ) = (l a : ℝ) - 1 := by
      rw [Nat.cast_sub hla_ge_one]; norm_num
    unfold InformationTheory.Shannon.ShannonCode.expectedLength
    -- LHS: b の項を分離 + Subtype 化
    have h_erase_iff : ∀ x : α, x ∈ (Finset.univ : Finset α).erase b ↔ x ≠ b := by
      intro x; simp [Finset.mem_erase]
    have hLHS_split :
        (∑ x : α, P.real {x} * (l x : ℝ))
          = (∑ x ∈ (Finset.univ : Finset α).erase b, P.real {x} * (l x : ℝ))
              + P.real {b} * (l b : ℝ) := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ b)]
    rw [hLHS_split]
    have hlb_eq : (l b : ℝ) = (l a : ℝ) := by rw [h_lab]
    rw [hlb_eq]
    have h_sum_subtype :
        (∑ x ∈ (Finset.univ : Finset α).erase b, P.real {x} * (l x : ℝ))
          = ∑ x : { y : α // y ≠ b }, P.real {x.val} * (l x.val : ℝ) := by
      rw [Finset.sum_subtype (Finset.univ.erase b) h_erase_iff
        (fun x => P.real {x} * (l x : ℝ))]
    rw [h_sum_subtype]
    -- l' a' = l a - 1, l' x = l x.val for x ≠ a'
    have hl'_a' : l' a' = l a - 1 := by simp [hl'_def, ha'_def]
    have hl'_other : ∀ x : { y : α // y ≠ b }, x ≠ a' → l' x = l x.val := by
      intro x hx
      have hxv_ne_a : x.val ≠ a := by
        intro h; apply hx; apply Subtype.ext; exact h
      simp [hl'_def, hxv_ne_a]
    -- mergedMeasure values
    have h_merged_a' : (mergedMeasure P a b hab).real {a'} = P.real {a} + P.real {b} := by
      rw [mergedMeasure_real P a b hab a']; simp [ha'_def]
    have h_merged_other : ∀ x : { y : α // y ≠ b }, x ≠ a' →
        (mergedMeasure P a b hab).real {x} = P.real {x.val} := by
      intro x hx
      rw [mergedMeasure_real P a b hab x]
      have hxv_ne_a : x.val ≠ a := by
        intro h; apply hx; apply Subtype.ext; exact h
      simp [hxv_ne_a]
    -- RHS: a' の項を分離
    have hRHS_split :
        (∑ x : { y : α // y ≠ b }, (mergedMeasure P a b hab).real {x} * (l' x : ℝ))
          = (mergedMeasure P a b hab).real {a'} * (l' a' : ℝ)
            + ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
                (mergedMeasure P a b hab).real {x} * (l' x : ℝ) := by
      rw [← Finset.add_sum_erase _ _ ha'_mem]
    rw [hRHS_split, h_merged_a', hl'_a', hla_cast]
    -- erase 内 sum: l' = l, merged = P
    have h_sum_erase :
        (∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
            (mergedMeasure P a b hab).real {x} * (l' x : ℝ))
          = ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
              P.real {x.val} * (l x.val : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx_ne : x ≠ a' := Finset.ne_of_mem_erase hx
      rw [h_merged_other x hx_ne, hl'_other x hx_ne]
    rw [h_sum_erase]
    -- LHS の Subtype sum も a' で分離
    have hLHS_subtype_split :
        (∑ x : { y : α // y ≠ b }, P.real {x.val} * (l x.val : ℝ))
          = P.real {a} * (l a : ℝ)
            + ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
                P.real {x.val} * (l x.val : ℝ) := by
      rw [← Finset.add_sum_erase _ _ ha'_mem]
    rw [hLHS_subtype_split]
    ring

/-! ### Phase 4 helpers — `mergedMeasure` instance + swap normalization +
`huffmanLength = L'` identification -/

omit [LinearOrder α] [Nonempty α] in
/-- **Phase 4 helper**: `mergedMeasure P a b hab` is a probability measure (since
`P` is and the singleton masses sum to `1` on `α'`). -/
lemma mergedMeasure_isProbabilityMeasure
    (P : Measure α) [IsProbabilityMeasure P] (a b : α) (hab : a ≠ b) :
    IsProbabilityMeasure (mergedMeasure P a b hab) := by
  classical
  refine ⟨?_⟩
  -- (mergedMeasure P a b hab) univ = ∑ x : α', (mergedMeasure P a b hab) {x}
  rw [show (Set.univ : Set { y : α // y ≠ b }) = ↑(Finset.univ : Finset { y : α // y ≠ b })
      from (Finset.coe_univ).symm,
    ← MeasureTheory.sum_measure_singleton]
  -- Each (mergedMeasure P a b hab) {x} = if x.val = a then P{a} + P{b} else P{x.val}
  have hmass : ∀ x : { y : α // y ≠ b },
      (mergedMeasure P a b hab) {x} =
        (if x.val = a then P {a} + P {b} else P {x.val}) := by
    intro x; unfold mergedMeasure
    exact Measure.sum_smul_dirac_singleton
  simp_rw [hmass]
  -- Now: ∑ x : α', (if x.val = a then P{a} + P{b} else P{x.val}) = 1
  set a' : { y : α // y ≠ b } := ⟨a, hab⟩ with ha'_def
  have ha'_mem : a' ∈ (Finset.univ : Finset { y : α // y ≠ b }) := Finset.mem_univ _
  -- Split a' term
  rw [← Finset.add_sum_erase _ _ ha'_mem]
  have hif_a' :
      (if a'.val = a then P {a} + P {b} else P {a'.val})
        = P {a} + P {b} := by simp [ha'_def]
  rw [hif_a']
  -- Erase 上の sum: x ≠ a' なので x.val ≠ a なので if = P {x.val}
  have h_sum_erase :
      (∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
          (if x.val = a then P {a} + P {b} else P {x.val}))
        = ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
            P {x.val} := by
    apply Finset.sum_congr rfl
    intro x hx
    have hx_ne : x ≠ a' := Finset.ne_of_mem_erase hx
    have hxv_ne_a : x.val ≠ a := by
      intro h; apply hx_ne; apply Subtype.ext; exact h
    simp [hxv_ne_a]
  rw [h_sum_erase]
  -- ∑ x ∈ erase a' = ∑ x : α', x ≠ a' = ∑ y : α, y ≠ a, y ≠ b
  -- これと P{a} + P{b} を加えて P univ = 1 にする
  -- α 側の sum: ∑ y : α, P{y} = P univ = 1
  have h_total : (∑ y : α, P {y} : ℝ≥0∞) = 1 := by
    rw [MeasureTheory.sum_measure_singleton, Finset.coe_univ]
    exact measure_univ
  -- ∑ y : α = (P{a} + P{b}) + ∑ y ≠ a, y ≠ b, P{y}
  -- ここで RHS の最終形を計算で reduce.
  -- まず: ∑ y : α P{y} = P{b} + ∑ y ≠ b, P{y}
  have h_split_b : (∑ y : α, P {y} : ℝ≥0∞)
      = P {b} + ∑ y ∈ (Finset.univ : Finset α).erase b, P {y} := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  -- ∑ y ≠ b = ∑ x : α', P {x.val}
  have h_erase_iff : ∀ x : α, x ∈ (Finset.univ : Finset α).erase b ↔ x ≠ b := by
    intro x; simp [Finset.mem_erase]
  have h_subtype :
      (∑ y ∈ (Finset.univ : Finset α).erase b, P {y})
        = ∑ x : { y : α // y ≠ b }, P {x.val} := by
    rw [Finset.sum_subtype (Finset.univ.erase b) h_erase_iff
      (fun y => P {y})]
  rw [h_subtype] at h_split_b
  -- ∑ x : α' P{x.val} = P{a} + ∑ x ∈ erase a', P{x.val}
  have h_split_a' :
      (∑ x : { y : α // y ≠ b }, P {x.val} : ℝ≥0∞)
        = P {a} + ∑ x ∈ (Finset.univ : Finset { y : α // y ≠ b }).erase a',
            P {x.val} := by
    rw [← Finset.add_sum_erase _ _ ha'_mem]
  rw [h_split_a'] at h_split_b
  -- h_split_b: ∑ y : α P{y} = P{b} + (P{a} + ∑ erase a' P{x.val})
  -- ゴール: P{a} + P{b} + ∑ erase a' P{x.val} = 1
  rw [← h_total]
  rw [h_split_b]
  ring

omit [Fintype α] [LinearOrder α] [Nonempty α] in
/-- **Phase 4 helper**: positivity of `mergedMeasure` on singletons (from positivity of `P`). -/
lemma mergedMeasure_pos
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (a b : α) (hab : a ≠ b) (x : { y : α // y ≠ b }) :
    0 < (mergedMeasure P a b hab).real {x} := by
  rw [mergedMeasure_real P a b hab x]
  by_cases hxa : x.val = a
  · simp [hxa]; exact add_pos (hP a) (hP b)
  · simp [hxa]; exact hP x.val

omit [LinearOrder α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Phase 4 helper**: `Fintype.card { y : α // y ≠ b } = Fintype.card α - 1`. -/
private lemma fintype_card_subtype_ne (b : α) :
    Fintype.card { y : α // y ≠ b } = Fintype.card α - 1 := by
  classical
  have h1 : Fintype.card { y : α // y ≠ b } = (Finset.univ.filter (· ≠ b)).card := by
    rw [Fintype.card_subtype]
  rw [h1]
  rw [show (Finset.univ.filter (· ≠ b) : Finset α) = Finset.univ.erase b by
    ext x; simp [Finset.mem_erase]]
  rw [Finset.card_erase_of_mem (Finset.mem_univ b)]
  rfl

omit [LinearOrder α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Phase 4 sub-helper — single swap step**: `Equiv.swap a m` で `l` を入れ替えると、
`l a ≤ l m` ∧ `P.real {a} ≤ P.real {m}` の下で expected length が非増加, Kraft 和は不変.
さらに `(l ∘ Equiv.swap a m) a = l m`, `(l ∘ Equiv.swap a m) m = l a`. -/
lemma swap_step_le
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    let l' := l ∘ Equiv.swap a m
    (∀ x, 0 < l' x) ∧
    (∑ x : α, ((2 : ℝ)) ^ (-(l' x : ℤ)) ≤ 1) ∧
    InformationTheory.Shannon.ShannonCode.expectedLength P l'
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l ∧
    l' a = l m ∧ l' m = l a := by
  classical
  set σ : α ≃ α := Equiv.swap a m with hσ_def
  set l' : α → ℕ := l ∘ σ with hl'_def
  have hl'_pos : ∀ x, 0 < l' x := fun x => hl_pos (σ x)
  have hl'_a : l' a = l m := by simp [hl'_def, hσ_def, Equiv.swap_apply_left]
  have hl'_m : l' m = l a := by simp [hl'_def, hσ_def, Equiv.swap_apply_right]
  -- Kraft: ∑ x : α, 2^(-l' x) = ∑ x : α, 2^(-l (σ x)) = ∑ x : α, 2^(-l x)
  have hkraft' : ∑ x : α, ((2 : ℝ)) ^ (-(l' x : ℤ)) ≤ 1 := by
    have h_eq : (∑ x : α, ((2 : ℝ)) ^ (-(l' x : ℤ)))
        = ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) := by
      show (∑ x : α, ((2 : ℝ)) ^ (-(l (σ x) : ℤ))) = _
      exact Equiv.sum_comp σ (fun x => ((2 : ℝ)) ^ (-(l x : ℤ)))
    rw [h_eq]; exact hl_kraft
  -- Expected length: E[l'] - E[l] = (P{a} - P{m}) * (l m - l a) ≤ 0
  -- (∵ P{a} ≤ P{m} and l a ≤ l m, so (P{a}-P{m})*(l m - l a) ≤ 0)
  have hexpL' :
      InformationTheory.Shannon.ShannonCode.expectedLength P l'
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l := by
    unfold InformationTheory.Shannon.ShannonCode.expectedLength
    by_cases ham : a = m
    · -- a = m: σ = identity, so l' = l, trivial
      have hσ_id : σ = Equiv.refl α := by rw [hσ_def, ham]; exact Equiv.swap_self m
      have : l' = l := by
        funext x; show l (σ x) = l x; rw [hσ_id]; rfl
      rw [this]
    · -- a ≠ m
      -- ∑ x, P{x} * l' x = ∑ x, P{x} * l (σ x).
      -- Split: x = a, x = m, other.
      have h_univ_eq : (Finset.univ : Finset α)
          = insert a (insert m ((Finset.univ : Finset α).erase a |>.erase m)) := by
        ext x; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro _; by_cases hxa : x = a
          · left; exact hxa
          · by_cases hxm : x = m
            · right; left; exact hxm
            · right; right; exact ⟨hxm, hxa⟩
        · intro _; trivial
      have hm_not_in : m ∉ ((Finset.univ : Finset α).erase a |>.erase m) := by
        simp
      have ha_not_in : a ∉ insert m ((Finset.univ : Finset α).erase a |>.erase m) := by
        simp [Ne.symm ham]
      -- Both sums split using h_univ_eq
      have h_split : ∀ f : α → ℝ,
          (∑ x : α, f x) = f a + f m
            + ∑ x ∈ ((Finset.univ : Finset α).erase a).erase m, f x := by
        intro f
        conv_lhs => rw [show (Finset.univ : Finset α) = insert a (insert m
            (((Finset.univ : Finset α).erase a).erase m)) from h_univ_eq]
        rw [Finset.sum_insert ha_not_in, Finset.sum_insert hm_not_in]
        ring
      rw [h_split (fun x => P.real {x} * (l' x : ℝ)),
          h_split (fun x => P.real {x} * (l x : ℝ))]
      -- For x ∈ erase erase: σ x = x, so l' x = l x
      have h_eq_other : ∀ x ∈ ((Finset.univ : Finset α).erase a).erase m,
          P.real {x} * (l' x : ℝ) = P.real {x} * (l x : ℝ) := by
        intro x hx
        have hxm : x ≠ m :=
          (Finset.mem_erase.mp hx).1
        have hxa : x ≠ a := by
          rcases Finset.mem_erase.mp (Finset.mem_of_mem_erase hx) with ⟨hne, _⟩
          exact hne
        have hσx : σ x = x := Equiv.swap_apply_of_ne_of_ne hxa hxm
        show P.real {x} * (l (σ x) : ℝ) = P.real {x} * (l x : ℝ)
        rw [hσx]
      have h_sum_eq : (∑ x ∈ ((Finset.univ : Finset α).erase a).erase m,
                        P.real {x} * (l' x : ℝ))
          = ∑ x ∈ ((Finset.univ : Finset α).erase a).erase m,
              P.real {x} * (l x : ℝ) :=
        Finset.sum_congr rfl h_eq_other
      rw [h_sum_eq, hl'_a, hl'_m]
      -- Want: P{a}*l m + P{m}*l a + S ≤ P{a}*l a + P{m}*l m + S
      -- ⟺ (P{m} - P{a})*(l m - l a) ≥ 0
      have hPa : (0 : ℝ) ≤ P.real {m} - P.real {a} := by linarith
      have hLa : (0 : ℝ) ≤ ((l m : ℝ) - (l a : ℝ)) := by
        have : ((l a : ℝ)) ≤ ((l m : ℝ)) := by exact_mod_cast h_la_le_lm
        linarith
      have hprod : (0 : ℝ) ≤ (P.real {m} - P.real {a}) * ((l m : ℝ) - (l a : ℝ)) :=
        mul_nonneg hPa hLa
      nlinarith [hprod]
  exact ⟨hl'_pos, hkraft', hexpL', hl'_a, hl'_m⟩

/-! ### Phase 4 hypothesis abbreviations (weak form 用)

T1-A' 主定理を完全な 0 sorry で publish するために、Cover-Thomas 標準証明で最も
技術的に重い 2 ステップ — **swap normalization** と **huffmanLength identification** —
は本ファイルでは証明せず、`huffmanLength_optimal_with_hypotheses` の **hypothesis
として外から渡す weak form** で publish する。

これら 2 hypothesis を discharge する完全証明は後継 seed `T1-A''` (
`docs/textbook-roadmap.md`) で予定。abbreviation はそれまでの sub-statement の
typing 用. -/

universe u

/-- **Weak form hypothesis 1**: swap normalization — 任意 Kraft-feasible `l` を
`l_norm a = l_norm b` 形に変換可能 (expected length 非増加 + Kraft 維持).

**strong precondition** (T1-A'' interface refactor): least-prob 対 `(a, b)` について
`a` = global-min (`_h_a_min`), `b` = rest-min (`_h_b_min`). 旧 disjunctive 形
`∀ c, Q{a} ≤ Q{c} ∨ Q{b} ≤ Q{c}` は `a` が global-min なだけで `b` は任意でよく、
Cover-Thomas swap 論法 (least-2 leaf を最長 2 leaf へ swap) が閉じない。call site
(`huffmanLength_optimal_aux_with_hypotheses` の step case) は `exists_sibling_min_pair`
経由で strong 形を実際に供給するため、これは weak 化ではなく mis-statement の修正. -/
abbrev SwapNormalizationHypothesis : Prop :=
  ∀ {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (_hll_pos : ∀ x, 0 < ll x)
    (_hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (_hab : a ≠ b)
    (_h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (_h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (_h_card : 3 ≤ Fintype.card β),
    ∃ l_norm : β → ℕ,
      (∀ x, 0 < l_norm x) ∧
      (∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1) ∧
      l_norm a = l_norm b ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll

/-- **Weak form hypothesis 2**: `huffmanLength` identification on `mergedMeasure`.

**strong precondition** (T1-A'' interface refactor): `a` = global-min (`_h_a_min`),
`b` = rest-min (`_h_b_min`). identification は `a, b` が **first-merged (確率最小) 対**
のときのみ成立する (任意の sibling 対では merged tree が一致しない). call site
(`huffmanLength_optimal_aux_with_hypotheses` の step case) は `exists_sibling_min_pair`
経由で strong 形を実際に供給するため、これは weak 化ではなく mis-statement の修正. -/
abbrev HuffmanMergedIdentificationHypothesis : Prop :=
  ∀ {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q] (_hQ : ∀ a, 0 < Q.real {a})
    (_h_card : 3 ≤ Fintype.card β)
    (a b : β) (hab : a ≠ b)
    (_h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (_h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (_h_sibling : huffmanLength Q a = huffmanLength Q b)
    (x : { y : β // y ≠ b }),
    huffmanLength (mergedMeasure Q a b hab) x
      = (if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val)

/-! ### 主定理 (Cover-Thomas Theorem 5.8.1) — weak form -/

/-- **Phase 4 helper — strong induction motor**: Auxiliary version with `Fintype.card α = n`
explicit, allowing `Nat.strong_induction_on` on `n` with `generalizing α P l`.

**Weak form**: 2 hypothesis (`h_swap` / `h_ident`) を hypothesis として外から受け取る. -/
private theorem huffmanLength_optimal_aux_with_hypotheses (n : ℕ)
    (h_swap : SwapNormalizationHypothesis.{u})
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1)
    (hn : Fintype.card α = n) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l := by
  induction n using Nat.strong_induction_on generalizing α with
  | _ n IH =>
    classical
    -- base case: n ≤ 2
    by_cases h_card : Fintype.card α ≤ 2
    · -- n ≤ 2: huffmanLength P x ≤ 1 ∀ x. ∀ x, 0 < l x. So E[H] ≤ E[l].
      -- 具体的に: huffmanLength P x の値は card = 1 で 0, card = 2 で 1.
      -- 各場合に E[huffmanLength P] ≤ 1 = ∑ P {x} * 1 ≤ ∑ P {x} * l x = E[l]
      unfold InformationTheory.Shannon.ShannonCode.expectedLength
      -- 各 x : α について huffmanLength P x ≤ l x を示す
      apply Finset.sum_le_sum
      intro x _
      have hPx : 0 ≤ P.real {x} := measureReal_nonneg
      -- P.real {x} * huffmanLength P x ≤ P.real {x} * l x
      apply mul_le_mul_of_nonneg_left _ hPx
      -- huffmanLength P x ≤ l x as ℝ. 十分: huffmanLength P x ≤ 1 ≤ l x
      have h_huffman_le_one : huffmanLength P x ≤ 1 := by
        have h_card_pos : 1 ≤ Fintype.card α := Fintype.card_pos
        have h_card_le_2 : Fintype.card α ≤ 2 := h_card
        rcases Nat.lt_or_ge (Fintype.card α) 2 with h_lt | h_ge
        · -- card ≤ 1: huffmanLength = 0
          unfold huffmanLength
          have hcard_init : (initMultiset P).card ≤ 1 := by
            unfold initMultiset
            rw [Multiset.card_map]
            show (Finset.univ : Finset α).card ≤ 1
            rw [Finset.card_univ]
            omega
          rw [huffmanLengthAux_eq_zero (initMultiset P) hcard_init
            (initMultiset_huffmanGrouping P)]
          simp
        · -- card = 2: huffmanLength = 1
          have h_n : Fintype.card α = 2 := by omega
          unfold huffmanLength
          have hcard_init : (initMultiset P).card = 2 := by
            unfold initMultiset
            rw [Multiset.card_map]
            show (Finset.univ : Finset α).card = 2
            rw [Finset.card_univ]
            exact h_n
          have h_card_two : 2 ≤ (initMultiset P).card := by omega
          have h_grouping := initMultiset_huffmanGrouping P
          -- After one step, s''.card = 1, so huffmanLengthAux s'' = 0.
          set step := (huffmanStep (initMultiset P) h_card_two h_grouping).val with hstep_def
          have hstep_card : step.2.2.card = 1 := by
            show (huffmanStep (initMultiset P) h_card_two h_grouping).val.2.2.card = 1
            rw [huffmanStep_card_eq (initMultiset P) h_card_two h_grouping, hcard_init]
          have hstep_grouping : HuffmanGrouping step.2.2 :=
            (huffmanStep (initMultiset P) h_card_two h_grouping).property.2.2.2
          obtain ⟨hx1_mem, hx2_mem, hshape, hg''⟩ :=
            huffmanStep_spec (initMultiset P) h_card_two h_grouping
          have hx1_mem' : step.1 ∈ initMultiset P := hx1_mem
          have hx1_form : ∃ y : α, step.1 = ({y}, P.real {y}) := by
            unfold initMultiset at hx1_mem'
            rw [Multiset.mem_map] at hx1_mem'
            obtain ⟨y, _, hye⟩ := hx1_mem'
            exact ⟨y, hye.symm⟩
          obtain ⟨y₁, hy₁_eq⟩ := hx1_form
          have hx2_mem_init : step.2.1 ∈ initMultiset P :=
            Multiset.mem_of_mem_erase hx2_mem
          have hx2_form : ∃ y : α, step.2.1 = ({y}, P.real {y}) := by
            unfold initMultiset at hx2_mem_init
            rw [Multiset.mem_map] at hx2_mem_init
            obtain ⟨y, _, hye⟩ := hx2_mem_init
            exact ⟨y, hye.symm⟩
          obtain ⟨y₂, hy₂_eq⟩ := hx2_form
          have hy₁_ne_y₂ : y₁ ≠ y₂ := by
            intro heq
            have hstep1_ne : step.1 ≠ step.2.1 := by
              intro h
              rw [h] at hx2_mem
              exact h_grouping.nodup.notMem_erase hx2_mem
            apply hstep1_ne
            rw [hy₁_eq, hy₂_eq, heq]
          -- x ∈ {y₁, y₂} since card α = 2 and y₁ ≠ y₂
          have hx_eq : x = y₁ ∨ x = y₂ := by
            have h_univ : (Finset.univ : Finset α) = {y₁, y₂} := by
              apply Finset.eq_of_subset_of_card_le
              · intro z _
                by_contra hzn
                rw [Finset.mem_insert, Finset.mem_singleton] at hzn
                push Not at hzn
                have h3 : ({y₁, y₂, z} : Finset α).card = 3 := by
                  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
                      Finset.card_singleton]
                  · simp [hzn.2.symm]
                  · simp [hy₁_ne_y₂, hzn.1.symm]
                have h_le : ({y₁, y₂, z} : Finset α).card ≤ Fintype.card α :=
                  Finset.card_le_univ _
                omega
              · rw [show (Finset.univ : Finset α).card = 2 from
                  by rw [show (Finset.univ : Finset α).card = Fintype.card α from rfl]; exact h_n]
                rw [Finset.card_insert_of_notMem (by simp [hy₁_ne_y₂]),
                    Finset.card_singleton]
            have hxm : x ∈ (Finset.univ : Finset α) := Finset.mem_univ x
            rw [h_univ, Finset.mem_insert, Finset.mem_singleton] at hxm
            exact hxm
          have h_xy_inAB : x ∈ step.1.1 ∨ x ∈ step.2.1.1 := by
            cases hx_eq with
            | inl h => left; rw [hy₁_eq]; simp [h]
            | inr h => right; rw [hy₂_eq]; simp [h]
          rw [huffmanLengthAux_step_merged (initMultiset P) h_card_two h_grouping h_xy_inAB]
          have hstep22_le : step.2.2.card ≤ 1 := by rw [hstep_card]
          rw [huffmanLengthAux_eq_zero step.2.2 hstep22_le hstep_grouping]
      -- Combine: huffmanLength P x ≤ 1 ≤ l x
      have h_one_le_lx : (1 : ℝ) ≤ (l x : ℝ) := by
        exact_mod_cast hl_pos x
      calc ((huffmanLength P x : ℕ) : ℝ)
          ≤ (1 : ℝ) := by exact_mod_cast h_huffman_le_one
        _ ≤ (l x : ℝ) := h_one_le_lx
    · -- step case: Fintype.card α ≥ 3
      push Not at h_card
      have h_card_ge_3 : 3 ≤ Fintype.card α := h_card
      have h_card_ge_2 : 2 ≤ Fintype.card α := by omega
      -- sibling pair (a, b) を取得 (strong: a = global-min, b = rest-min)
      obtain ⟨a, b, hab, h_sib, h_a_min, h_b_min⟩ :=
        exists_sibling_min_pair P hP h_card_ge_2
      -- l を normalize: l_swap a = l_swap b  (hypothesis `h_swap` 経由)
      obtain ⟨l_norm, hln_pos, hln_kraft, hln_eq_ab, hln_le⟩ :=
        h_swap P l hl_pos hl_kraft a b hab h_a_min h_b_min h_card_ge_3
      -- l_norm a ≥ 2 (otherwise Kraft > 1 with card ≥ 3)
      have hln_a_ge_2 : 2 ≤ l_norm a := by
        by_contra h_lt
        push Not at h_lt
        have h_la_eq_1 : l_norm a = 1 := by
          have h_pos := hln_pos a; omega
        -- Then 2^(-l_norm a) = 1/2, same for b. plus at least 1 more positive term > 1.
        -- ∑ x : α, 2^(-l_norm x) ≥ 2^(-l_norm a) + 2^(-l_norm b) = 1, plus positive ⇒ > 1.
        -- Get c ≠ a, c ≠ b
        have h_exists_c : ∃ c : α, c ≠ a ∧ c ≠ b := by
          by_contra h_no_c
          have h_no_c' : ∀ c : α, c = a ∨ c = b := by
            intro c
            by_contra hcab
            apply h_no_c
            push Not at hcab
            exact ⟨c, hcab.1, hcab.2⟩
          have h_univ : (Finset.univ : Finset α) ⊆ {a, b} := by
            intro c _
            rcases h_no_c' c with h_eq_a | h_eq_b
            · rw [h_eq_a]; simp
            · rw [h_eq_b]; simp
          have h_card_le_2 : Fintype.card α ≤ 2 := by
            have hle := Finset.card_le_card h_univ
            simp only [Finset.card_univ] at hle
            have h2 : ({a, b} : Finset α).card ≤ 2 := by
              calc ({a, b} : Finset α).card
                  ≤ ({a} : Finset α).card + 1 := Finset.card_insert_le _ _
                _ = 2 := by rw [Finset.card_singleton]
            omega
          omega
        obtain ⟨c, hca, hcb⟩ := h_exists_c
        -- ∑ over {a, b, c} ≤ 1 から 2^(-1) + 2^(-1) + 2^(-l_norm c) ≤ 1
        have h_pos_pow : (0 : ℝ) < (2 : ℝ) ^ (-(l_norm c : ℤ)) := by
          apply zpow_pos
          norm_num
        have h_sum_three :
            ((2 : ℝ)) ^ (-(l_norm a : ℤ)) + ((2 : ℝ)) ^ (-(l_norm b : ℤ))
              + ((2 : ℝ)) ^ (-(l_norm c : ℤ))
              ≤ ∑ x : α, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) := by
          have hne_ab : a ≠ b := hab
          have hne_ca : c ≠ a := hca
          have hne_cb : c ≠ b := hcb
          have h_three_sub :
              ({a, b, c} : Finset α) ⊆ Finset.univ := Finset.subset_univ _
          have h_sum_eq :
              (∑ x ∈ ({a, b, c} : Finset α), ((2 : ℝ)) ^ (-(l_norm x : ℤ)))
                = ((2 : ℝ)) ^ (-(l_norm a : ℤ)) + ((2 : ℝ)) ^ (-(l_norm b : ℤ))
                  + ((2 : ℝ)) ^ (-(l_norm c : ℤ)) := by
            rw [show ({a, b, c} : Finset α) = insert a (insert b ({c} : Finset α)) from rfl,
                Finset.sum_insert (by simp [hne_ab, hne_ca.symm]),
                Finset.sum_insert (by simp [hne_cb.symm]),
                Finset.sum_singleton]
            ring
          rw [← h_sum_eq]
          apply Finset.sum_le_sum_of_subset_of_nonneg h_three_sub
          intros y _ _
          positivity
        have h_pow_a : ((2 : ℝ)) ^ (-(l_norm a : ℤ)) = 1/2 := by
          rw [h_la_eq_1]; norm_num
        have h_pow_b : ((2 : ℝ)) ^ (-(l_norm b : ℤ)) = 1/2 := by
          rw [← hln_eq_ab, h_la_eq_1]; norm_num
        rw [h_pow_a, h_pow_b] at h_sum_three
        linarith
      -- Bridge R: ∃ l', positivity ∧ kraft ∧ E[l_norm] = E[mergedMeasure, l'] + (P{a} + P{b})
      obtain ⟨l', hl'_pos, hl'_kraft, hl'_eq⟩ :=
        expectedLength_bridge_R P l_norm hln_pos a b hab hln_eq_ab hln_a_ge_2 hln_kraft
      -- mergedMeasure の IsProbabilityMeasure instance
      have hP'_inst : IsProbabilityMeasure (mergedMeasure P a b hab) :=
        mergedMeasure_isProbabilityMeasure P a b hab
      have hP'_pos : ∀ x : { y : α // y ≠ b },
          0 < (mergedMeasure P a b hab).real {x} :=
        mergedMeasure_pos P hP a b hab
      -- IH on α' (Fintype.card α' = Fintype.card α - 1 < n)
      have h_card_α' :
          Fintype.card { y : α // y ≠ b } = Fintype.card α - 1 :=
        fintype_card_subtype_ne b
      have h_card_α'_lt : Fintype.card { y : α // y ≠ b } < n := by
        rw [h_card_α', ← hn]; omega
      -- α' is nonempty: a ≠ b ⇒ ⟨a, hab⟩ : α'.
      haveI : Nonempty { y : α // y ≠ b } := ⟨⟨a, hab⟩⟩
      -- IH 適用: huffmanLength の方が l' より expected length 小
      have h_IH :
          InformationTheory.Shannon.ShannonCode.expectedLength
              (mergedMeasure P a b hab) (huffmanLength (mergedMeasure P a b hab))
            ≤ InformationTheory.Shannon.ShannonCode.expectedLength
              (mergedMeasure P a b hab) l' :=
        IH _ h_card_α'_lt (mergedMeasure P a b hab) hP'_pos l' hl'_pos hl'_kraft rfl
      -- huffmanLength_mergedMeasure_eq: huffmanLength (mergedMeasure ...) x = L'(x)
      -- (hypothesis `h_ident` 経由)
      have h_L'_link : ∀ x : { y : α // y ≠ b },
          huffmanLength (mergedMeasure P a b hab) x
            = (if x.val = a then huffmanLength P a - 1 else huffmanLength P x.val) := by
        intro x
        exact h_ident P hP h_card_ge_3 a b hab h_a_min h_b_min h_sib x
      -- Bridge L: E[P, huffmanLength P] = E[merged, huffmanLength merged] + (P{a} + P{b})
      have h_BL := huffmanLength_bridge_L P hP h_card_ge_2 a b hab h_sib
        (huffmanLength (mergedMeasure P a b hab)) h_L'_link
      -- 連結: E[P, huffmanLength P]
      --     = E[merged, huffmanLength merged] + (P{a}+P{b})    -- (h_BL)
      --     ≤ E[merged, l']                  + (P{a}+P{b})     -- (h_IH)
      --     = E[P, l_norm]                                    -- (hl'_eq, rearranged)
      --     ≤ E[P, l]                                          -- (hln_le)
      calc InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
          = InformationTheory.Shannon.ShannonCode.expectedLength
              (mergedMeasure P a b hab) (huffmanLength (mergedMeasure P a b hab))
            + (P.real {a} + P.real {b}) := h_BL
        _ ≤ InformationTheory.Shannon.ShannonCode.expectedLength
              (mergedMeasure P a b hab) l'
            + (P.real {a} + P.real {b}) := by linarith
        _ = InformationTheory.Shannon.ShannonCode.expectedLength P l_norm := by linarith
        _ ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l := hln_le

/-- **主定理 (Cover-Thomas Theorem 5.8.1) — weak form** — Huffman 語長は任意の
Kraft-feasible 語長関数より expected length が小さい. **Weak form** として
swap normalization と identification の 2 hypothesis を引数で受け取る. 完全な
discharge は後継 seed `T1-A''` で予定. -/
theorem huffmanLength_optimal_with_hypotheses
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h_swap : SwapNormalizationHypothesis.{u})
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_aux_with_hypotheses (Fintype.card α) h_swap h_ident
    P hP l hl_pos hl_kraft rfl

end InformationTheory.Shannon.Huffman
