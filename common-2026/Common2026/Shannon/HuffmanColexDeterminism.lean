import Common2026.Shannon.HuffmanMergedAuxIdent

/-!
# T1-A'' Huffman — colex 決定化による無条件 relabel 不変量

`huffmanStep` の colex 決定化 (`Huffman.lean`、`groupKey` 2 段 lex min) により、
`HuffmanMergedAuxIdent.lean` の no-ties 限定 (`NodupChain`) relabel 機構を
**無条件版** へ一般化する。`groupKey` は単射なので min は常に一意 (確率 tie は colex で
破られる)。よって relabel-invariance は `NodupChain` 不要で成立する。

## 設計上の重要制約 (Phase 0 probe で確定)

carrier 型に `[DecidableEq α]` と `[LinearOrder α]` の **2 つの DecidableEq instance** が
同時に在ると、`toColex_image_le_toColex_image` の colex 保存鎖が `whnf`/`isDefEq` で
タイムアウトする (ambient `[DecidableEq α]` vs `LinearOrder.toDecidableEq` の defeq 検査が
ℝ import 下で爆発)。よって本 file の carrier variable は **`[LinearOrder α]` のみ**を持ち、
`DecidableEq` はそこから導出する (separate `[DecidableEq α]` を置かない)。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators Colex

universe u

-- carrier `α` は [LinearOrder α] のみ (DecidableEq は導出、dual-instance timeout 回避)
variable {α : Type*} [Fintype α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### Section F — colex 保存 (strict-mono embedding) -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **colex 保存 (carrier 横断)**: strict-mono な underlying map を持つ embedding `e : α ↪ γ`
に沿って、`Finset.map e` は colex 順を保存する. これが cross-type 対応の核
(`Subtype.strictMono_coe` + `map_eq_image` + `toColex_image_le_toColex_image`). -/
lemma toColex_map_le_toColex_map {γ : Type*} [LinearOrder γ] (e : α ↪ γ)
    (he : StrictMono e) (s t : Finset α) :
    toColex (s.map e) ≤ toColex (t.map e) ↔ toColex s ≤ toColex t := by
  rw [Finset.map_eq_image, Finset.map_eq_image]
  exact Finset.Colex.toColex_image_le_toColex_image he

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **groupKey 保存 (carrier 横断)**: strict-mono embedding `e` に沿った `relabelGroup e` は
`groupKey` の順序を保存する (第 1 キー = 確率は不変、第 2 キー = colex は `e` strict-mono で
保存). 決定的 min が relabel と可換であることの核. -/
lemma groupKey_relabel_le {γ : Type*} [LinearOrder γ] (e : α ↪ γ)
    (he : StrictMono e) (p q : Finset α × ℝ) :
    groupKey (relabelGroup e p) ≤ groupKey (relabelGroup e q) ↔ groupKey p ≤ groupKey q := by
  have hcolex := toColex_map_le_toColex_map e he p.1 q.1
  unfold groupKey relabelGroup
  rw [Prod.Lex.le_iff, Prod.Lex.le_iff]
  simp only
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, hcolex.mp h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, hcolex.mpr h2⟩

/-! ### Section G — 無条件 (groupKey) min 一意性 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **無条件 min 一意性**: `groupKey` 最小を達成する group は唯一 (`groupKey` 単射). -/
lemma min_unique_of_key
    (s : Multiset (Finset α × ℝ)) (p q : Finset α × ℝ) (hp : p ∈ s) (hq : q ∈ s)
    (hpmin : ∀ z ∈ s, groupKey p ≤ groupKey z) (hqmin : ∀ z ∈ s, groupKey q ≤ groupKey z) :
    p = q := by
  have hkey : groupKey p = groupKey q := le_antisymm (hpmin q hq) (hqmin p hp)
  exact groupKey_injective hkey

/-! ### Section H — 無条件 (決定的) relabel correspondence

`huffmanStep` の colex 決定化により、relabel と min 選択は **無条件に可換** になる
(`NodupChain` 不要)。`huffmanStep_*_relabel` の決定版。 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **決定的 1st 選択 relabel 可換**: strict-mono embedding `e` で relabel した multiset の
`huffmanStep` 1st 選択は、元の 1st 選択の relabel に等しい (`groupKey` 一意性、無条件)。 -/
lemma huffmanStep_fst_relabel_det {γ : Type*} [LinearOrder γ] (e : α ↪ γ)
    (he : StrictMono e)
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    (hs' : 2 ≤ (relabelMultiset e s).card)
    (hg' : HuffmanGrouping (relabelMultiset e s)) :
    (huffmanStep (relabelMultiset e s) hs' hg').val.1
      = relabelGroup e ((huffmanStep s hs hg).val.1) := by
  set p := (huffmanStep s hs hg).val.1 with hp_def
  set q := (huffmanStep (relabelMultiset e s) hs' hg').val.1 with hq_def
  have hp_mem : p ∈ s := (huffmanStep_spec s hs hg).1
  have hp_min : ∀ z ∈ s, groupKey p ≤ groupKey z := huffmanStep_key_min_fst s hs hg
  have hq_mem : q ∈ relabelMultiset e s := (huffmanStep_spec (relabelMultiset e s) hs' hg').1
  have hq_min : ∀ z ∈ relabelMultiset e s, groupKey q ≤ groupKey z :=
    huffmanStep_key_min_fst (relabelMultiset e s) hs' hg'
  have hrp_mem : relabelGroup e p ∈ relabelMultiset e s :=
    (relabelMultiset_mem e s p).mpr hp_mem
  have hrp_min : ∀ z ∈ relabelMultiset e s, groupKey (relabelGroup e p) ≤ groupKey z := by
    intro z hz
    unfold relabelMultiset at hz
    rw [Multiset.mem_map] at hz
    obtain ⟨z', hz', hzz'⟩ := hz
    rw [← hzz']
    exact (groupKey_relabel_le e he p z').mpr (hp_min z' hz')
  exact min_unique_of_key (relabelMultiset e s) q (relabelGroup e p)
    hq_mem hrp_mem hq_min hrp_min

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **決定的 2nd 選択 relabel 可換** (無条件)。 -/
lemma huffmanStep_snd_relabel_det {γ : Type*} [LinearOrder γ] (e : α ↪ γ)
    (he : StrictMono e)
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    (hs' : 2 ≤ (relabelMultiset e s).card)
    (hg' : HuffmanGrouping (relabelMultiset e s)) :
    (huffmanStep (relabelMultiset e s) hs' hg').val.2.1
      = relabelGroup e ((huffmanStep s hs hg).val.2.1) := by
  set p := (huffmanStep s hs hg).val.2.1 with hp_def
  set q := (huffmanStep (relabelMultiset e s) hs' hg').val.2.1 with hq_def
  have h1 := huffmanStep_fst_relabel_det e he s hs hg hs' hg'
  have hp_mem : p ∈ s.erase (huffmanStep s hs hg).val.1 := (huffmanStep_spec s hs hg).2.1
  have hp_min : ∀ z ∈ s.erase (huffmanStep s hs hg).val.1, groupKey p ≤ groupKey z :=
    huffmanStep_key_min_snd s hs hg
  have hq_mem : q ∈ (relabelMultiset e s).erase
      (huffmanStep (relabelMultiset e s) hs' hg').val.1 :=
    (huffmanStep_spec (relabelMultiset e s) hs' hg').2.1
  have hq_min : ∀ z ∈ (relabelMultiset e s).erase
      (huffmanStep (relabelMultiset e s) hs' hg').val.1, groupKey q ≤ groupKey z :=
    huffmanStep_key_min_snd (relabelMultiset e s) hs' hg'
  have h_erase_eq : (relabelMultiset e s).erase (huffmanStep (relabelMultiset e s) hs' hg').val.1
      = relabelMultiset e (s.erase (huffmanStep s hs hg).val.1) := by
    rw [h1, relabelMultiset_erase]
  have hrp_mem : relabelGroup e p ∈ (relabelMultiset e s).erase
      (huffmanStep (relabelMultiset e s) hs' hg').val.1 := by
    rw [h_erase_eq]
    exact (relabelMultiset_mem e (s.erase (huffmanStep s hs hg).val.1) p).mpr hp_mem
  have hrp_min : ∀ z ∈ (relabelMultiset e s).erase
      (huffmanStep (relabelMultiset e s) hs' hg').val.1,
      groupKey (relabelGroup e p) ≤ groupKey z := by
    intro z hz
    rw [h_erase_eq] at hz
    unfold relabelMultiset at hz
    rw [Multiset.mem_map] at hz
    obtain ⟨z', hz', hzz'⟩ := hz
    rw [← hzz']
    exact (groupKey_relabel_le e he p z').mpr (hp_min z' hz')
  exact min_unique_of_key _ q (relabelGroup e p) hq_mem hrp_mem hq_min hrp_min

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **決定的 step-output multiset relabel 可換** (無条件)。1st/2nd 選択の対応 + merged group の
relabel + erase 可換から。 -/
lemma huffmanStep_step_relabel_det {γ : Type*} [LinearOrder γ] (e : α ↪ γ)
    (he : StrictMono e)
    (s : Multiset (Finset α × ℝ)) (hs : 2 ≤ s.card) (hg : HuffmanGrouping s)
    (hs' : 2 ≤ (relabelMultiset e s).card)
    (hg' : HuffmanGrouping (relabelMultiset e s)) :
    (huffmanStep (relabelMultiset e s) hs' hg').val.2.2
      = relabelMultiset e ((huffmanStep s hs hg).val.2.2) := by
  obtain ⟨_, _, hshape_s, _⟩ := huffmanStep_spec s hs hg
  obtain ⟨_, _, hshape_rs, _⟩ := huffmanStep_spec (relabelMultiset e s) hs' hg'
  have h1 := huffmanStep_fst_relabel_det e he s hs hg hs' hg'
  have h2 := huffmanStep_snd_relabel_det e he s hs hg hs' hg'
  rw [hshape_rs, h1, h2, hshape_s]
  show _ = ((((huffmanStep s hs hg).val.1.1 ∪ (huffmanStep s hs hg).val.2.1.1,
      (huffmanStep s hs hg).val.1.2 + (huffmanStep s hs hg).val.2.1.2) ::ₘ
      ((s.erase (huffmanStep s hs hg).val.1).erase
        (huffmanStep s hs hg).val.2.1))).map (relabelGroup e)
  rw [Multiset.map_cons]
  congr 1
  · unfold relabelGroup
    simp only [Prod.mk.injEq, and_true]
    rw [Finset.map_union]
  · show ((relabelMultiset e s).erase (relabelGroup e (huffmanStep s hs hg).val.1)).erase
        (relabelGroup e (huffmanStep s hs hg).val.2.1)
      = ((s.erase (huffmanStep s hs hg).val.1).erase
          (huffmanStep s hs hg).val.2.1).map (relabelGroup e)
    rw [← relabelMultiset_erase, ← relabelMultiset_erase]
    rfl

/-! ### Section I — 無条件 relabel-invariance of `huffmanLengthAux` (cornerstone)

step-correspondence (`huffmanStep_step_relabel_det`) を strong induction で持ち上げ、
`huffmanLengthAux` の carrier-embedding 越し不変量を **NodupChain 不要**で得る。
これが決定化が unlock する核心の不変量 (旧 `huffmanLengthAux_relabel` の無条件版)。 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **決定的 relabel-invariance cornerstone (無条件)**: strict-mono embedding `e : α ↪ γ` に
沿って `huffmanLengthAux` は不変:
`huffmanLengthAux (relabelMultiset e s) (e a) = huffmanLengthAux s a`.
`huffmanStep` の colex 決定化により `NodupChain` 前提が不要になった (`groupKey` min は常に一意)。 -/
lemma huffmanLengthAux_relabel_det {γ : Type*} [LinearOrder γ] (e : α ↪ γ)
    (he : StrictMono e)
    (s : Multiset (Finset α × ℝ)) (hg : HuffmanGrouping s) (a : α) :
    huffmanLengthAux (relabelMultiset e s) (e a) = huffmanLengthAux s a := by
  induction hn : s.card using Nat.strong_induction_on generalizing s a with
  | _ n ih =>
    have hg' : HuffmanGrouping (relabelMultiset e s) := relabelMultiset_grouping e s hg
    by_cases h2 : 2 ≤ s.card
    · have h2' : 2 ≤ (relabelMultiset e s).card := by
        rw [relabelMultiset_card]; exact h2
      have hstep := huffmanStep_step_relabel_det e he s h2 hg h2' hg'
      rw [huffmanLengthAux_eq_step (relabelMultiset e s) h2' hg',
        huffmanLengthAux_eq_step s h2 hg]
      simp only
      have h1 := huffmanStep_fst_relabel_det e he s h2 hg h2' hg'
      have h2sel := huffmanStep_snd_relabel_det e he s h2 hg h2' hg'
      have hA : (huffmanStep (relabelMultiset e s) h2' hg').val.1.1
          = (huffmanStep s h2 hg).val.1.1.map e := by
        rw [h1]; rfl
      have hB : (huffmanStep (relabelMultiset e s) h2' hg').val.2.1.1
          = (huffmanStep s h2 hg).val.2.1.1.map e := by
        rw [h2sel]; rfl
      have hmem : (e a ∈ (huffmanStep (relabelMultiset e s) h2' hg').val.1.1 ∨
            e a ∈ (huffmanStep (relabelMultiset e s) h2' hg').val.2.1.1)
          ↔ (a ∈ (huffmanStep s h2 hg).val.1.1 ∨
            a ∈ (huffmanStep s h2 hg).val.2.1.1) := by
        rw [hA, hB, Finset.mem_map', Finset.mem_map']
      have hcard'' : (huffmanStep s h2 hg).val.2.2.card < n := by
        have := huffmanStep_card_lt s h2 hg; omega
      have hIH : huffmanLengthAux (relabelMultiset e ((huffmanStep s h2 hg).val.2.2)) (e a)
          = huffmanLengthAux ((huffmanStep s h2 hg).val.2.2) a :=
        ih _ hcard'' ((huffmanStep s h2 hg).val.2.2)
          (huffmanStep_grouping s h2 hg) a rfl
      rw [hstep, hIH]
      by_cases hd : a ∈ (huffmanStep s h2 hg).val.1.1 ∨
          a ∈ (huffmanStep s h2 hg).val.2.1.1
      · rw [if_pos (hmem.mpr hd), if_pos hd]
      · rw [if_neg (fun h => hd (hmem.mp h)), if_neg hd]
    · have hc1 : s.card ≤ 1 := by omega
      have hc1' : (relabelMultiset e s).card ≤ 1 := by rw [relabelMultiset_card]; exact hc1
      rw [huffmanLengthAux_eq_zero (relabelMultiset e s) hc1' hg',
        huffmanLengthAux_eq_zero s hc1 hg]

/-! ### Section J — 残タスク (honest, load-bearing): collapse correspondence

`huffmanLengthAux_relabel_det` (Section I) は決定化が unlock した **無条件 genuine** な
relabel 不変量で、`HuffmanMergedAuxIdent.lean` の旧 no-ties (`NodupChain`) 機構を
完全に置き換える。これにより Section E の障害 (ii) (NodupChain 不成立) と
(iii) (per-symbol invariance 偽) は **解消** された (両 carrier の決定的 min は colex で
常に一意、relabel と無条件可換)。

**しかし `MergedHuffmanAuxIdentHypothesis` の完全 discharge には、なお 1 つの genuine な
構造補題 (collapse correspondence) が残る。** これは determinization では自動的に閉じない
(`huffmanStep` の within-tree 非決定性を断つことと、cross-tree の Finset-label 構造変更を
橋渡しすることは別問題)。具体的に:

`relabelMultiset (subtypeNeEmbedding b) (mergedInitMultiset Q a b)` (β carrier 上) は
`initMultiset Q` の最初の決定的 merge 後の残木 `s''_β` と **1 group だけ** 異なる:
mergedInit 側は absorbing leaf が singleton `({a}, Q{a}+Q{b})`、`s''_β` 側は card-2 group
`({a,b}, Q{a}+Q{b})`。確率は同一だが colex が異なる
(`toColex {a} < toColex {a,b}`、`{a} ⊂ {a,b}` より strict)。

**collapse 補題**: `huffmanLengthAux` は、ある group の Finset-label `{a}` を `{a,b}`
(同確率、`b` は他に現れない fresh element) に拡張しても、`b` 以外の leaf の値を保つ:
`huffmanLengthAux (({a},p) ::ₘ rest) z = huffmanLengthAux (({a,b},p) ::ₘ rest) z`  (`z ≠ b`).

これは **genuine な Huffman の事実** で、数値検証 (例 `Q={a:.1,c:.25,b:.15,d:.5}`、
`a<c<b` で colex tie-break が両木で食い違うケース) で **per-leaf identity は成立** を確認済
だが、merge **order** は equal-probability tie 下で両木間で食い違いうるため、naive な
lockstep 帰納では閉じない。tie-break order に依存しない invariant (確率 multiset で
depth が決まる Huffman 性質の機械化) が必要で、規模は ~150-250 行 + tie 場合分け、
本 session で genuine に閉じるには proof-pivot-advisor のエスカレーションが妥当。

**honesty 線 (重要)**: 本 session は collapse 補題を fake な residual hypothesis
(型 ≡ `MergedHuffmanAuxIdentHypothesis`) で抜くことを **しない** (Section E / plan 撤退ライン
の禁止事項)。よって無引数 `huffmanLength_optimal` は **publish しない**。honest な最前線は
引き続き headline `huffmanLength_optimal_modulo_aux_ident` (`HuffmanStrongForm.lean`、
Hyp2 = `MergedHuffmanAuxIdentHypothesis` を明示引数で取る、sorryAx 非依存) のまま。
本 session の genuine な前進は: (1) `huffmanStep` colex 決定化 (`Huffman.lean`、無条件)、
(2) `huffmanLengthAux_relabel_det` (NodupChain 不要の無条件 relabel cornerstone)。 -/

end InformationTheory.Shannon.Huffman
