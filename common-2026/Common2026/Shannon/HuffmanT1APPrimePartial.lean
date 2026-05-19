import Mathlib.Logic.Equiv.Basic
import Common2026.Shannon.HuffmanOptimality

/-!
# T1-A'' Huffman 最適性 partial / plumbing 補題群

`Common2026/Shannon/HuffmanOptimality.lean` (T1-A' weak form publish, 1054 行 / 0 sorry) の
`swap_step_le` (`:650`) 周辺の **extractor / trivial-case 補題群** を独立 publish.

完全な hypothesis discharge (T1-A'' full scope) は
[`docs/shannon/huffman-optimality-t1apprime-moonshot-plan.md`](../../docs/shannon/huffman-optimality-t1apprime-moonshot-plan.md)
で judgement log #3 で「~550 行 / 4-6 セッション」と判定済の不可能 scope.
本 file は同 plan の縮小版
[`docs/shannon/huffman-t1apprime-partial-moonshot-plan.md`](../../docs/shannon/huffman-t1apprime-partial-moonshot-plan.md)
の publish 物.

## Approach

`swap_step_le` (`HuffmanOptimality.lean:650`) は 5-tuple
`(0 < l', kraft ≤ 1, expectedLength ≤, l' a = l m, l' m = l a)` を返す多目的 helper.
client が個別パートを使う場合の起動コストを下げるため、各成分を **個別命名 extractor**
として publish する. 加えて `a = m` (恒等 swap) trivial 系
(`swap_step_le_self`)、2 段同元 swap の involution (`swap_compose_self`),
`SwapNormalizationHypothesis` の自明 `ll a = ll b` case の discharge
(`SwapNormalizationHypothesis_trivial_when_eq`) を加える.

本 file は T1-A''' (後続 seed) で full hypothesis discharge を着手するときの skeleton
起動コスト低下を狙った plumbing 集. 主定理の強形 publish は本 file の scope-out.
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ### `swap_step_le` の 4 分解 extractor

`swap_step_le` (`HuffmanOptimality.lean:650`) の返す 5-tuple のうち、client が個別に
よく使う 4 成分を独立 lemma として publish.
-/

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **`swap_step_le` extractor (positivity)**: swap 後の `l'` も全点 positive. -/
theorem swap_step_le_pos
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    ∀ x, 0 < (l ∘ Equiv.swap a m) x := by
  exact (swap_step_le P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm).1

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **`swap_step_le` extractor (Kraft)**: swap 後 Kraft 和も `≤ 1` を維持. -/
theorem swap_step_le_kraft
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    ∑ x : α, ((2 : ℝ)) ^ (-((l ∘ Equiv.swap a m) x : ℤ)) ≤ 1 := by
  exact (swap_step_le P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm).2.1

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **`swap_step_le` extractor (expected length)**: swap 後 expected length は非増加. -/
theorem swap_step_le_expectedLength_le
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (l ∘ Equiv.swap a m)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l := by
  exact (swap_step_le P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm).2.2.1

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **`swap_step_le` extractor (値 swap)**: swap 後の `l'` は `(a, m)` 位置で値が入れ替わる. -/
theorem swap_step_le_values
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    (l ∘ Equiv.swap a m) a = l m ∧ (l ∘ Equiv.swap a m) m = l a := by
  exact ⟨(swap_step_le P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm).2.2.2.1,
         (swap_step_le P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm).2.2.2.2⟩

/-! ### 恒等 swap (`a = m`) trivial 系 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **恒等 swap**: `Equiv.swap m m` は `Equiv.refl α` と等しい (Mathlib 既存
`Equiv.swap_self` を `Equiv.refl` 形に整理). `l ∘ Equiv.swap m m = l`. -/
theorem swap_step_le_self_comp (l : α → ℕ) (m : α) :
    l ∘ Equiv.swap m m = l := by
  funext x
  show l ((Equiv.swap m m) x) = l x
  rw [Equiv.swap_self]
  rfl

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **恒等 swap の `swap_step_le` 適用**: `a = m` のとき `swap_step_le` の結論は trivial
(swap = identity ⇒ `l' = l`, Kraft / expected length / 値 swap が即時等号). -/
theorem swap_step_le_self
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (_hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (m : α) :
    (l ∘ Equiv.swap m m) = l ∧
    (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ Equiv.swap m m) x : ℤ)) ≤ 1) ∧
    InformationTheory.Shannon.ShannonCode.expectedLength P (l ∘ Equiv.swap m m)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l ∧
    (l ∘ Equiv.swap m m) m = l m := by
  have h_id : l ∘ Equiv.swap m m = l := swap_step_le_self_comp l m
  refine ⟨h_id, ?_, ?_, ?_⟩
  · rw [h_id]; exact hl_kraft
  · rw [h_id]
  · rw [h_id]

/-! ### 2 段同元 swap の involution 性質 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **同元 swap の involution**: `Equiv.swap a m ∘ Equiv.swap a m = Equiv.refl α`.
従って `l ∘ Equiv.swap a m ∘ Equiv.swap a m = l`. Mathlib `Equiv.swap_apply_left/right`
+ `Equiv.swap_apply_of_ne_of_ne` の case-split で確認. -/
theorem swap_compose_self_comp (l : α → ℕ) (a m : α) :
    l ∘ Equiv.swap a m ∘ Equiv.swap a m = l := by
  funext x
  show l ((Equiv.swap a m) ((Equiv.swap a m) x)) = l x
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · by_cases hxm : x = m
    · subst hxm
      rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxm,
          Equiv.swap_apply_of_ne_of_ne hxa hxm]

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **同元 2 段 swap の `swap_step_le` 適用**: `swap_step_le` を `(a, m)` で適用後、
さらに `(a, m)` で `l'` に対し swap_step_le を適用すると `l'' = l` に戻る. ただし
中間状態 `l'` で `l' a ≤ l' m ∧ P.real {a} ≤ P.real {m}` が成立する保証は **ない**
ため、本 lemma は直接 `swap_step_le` を 2 段適用する形ではなく、`Equiv.swap` 合成の
involution 性質を `l` 視点から述べる形で publish. -/
theorem swap_compose_self_eq (l : α → ℕ) (a m : α) :
    (l ∘ Equiv.swap a m) ∘ Equiv.swap a m = l := by
  exact swap_compose_self_comp l a m

/-! ### `SwapNormalizationHypothesis` の自明 case discharge

`ll a = ll b` が input で既成立している場合、hypothesis 結論の `l_norm` として `ll` 自身を
選べば全条件が pass-through で成立する. これは hypothesis 全体の **本格 discharge ではない**
(任意 `ll` で `l_norm a = l_norm b` を作る discharge は scope-out)、`ll a = ll b` の場合の
特殊形 trivial 補題.
-/

universe u

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **`SwapNormalizationHypothesis` 自明 case**: `ll a = ll b` が既成立なら、hypothesis 結論の
`l_norm` を `ll` 自身に取ることで全条件 (positivity / Kraft / `l_norm a = l_norm b` /
expected length 非増加) が pass-through で成立. これは `SwapNormalizationHypothesis` 全体
の hypothesis discharge **ではない** が、後続 T1-A''' で「`ll a = ll b` を作るところまで
誘導する swap argument」の終端で使える partial 補題.

注: 本 lemma は `SwapNormalizationHypothesis` の universe-polymorphic abbrev (= `∀ β ...`)
を **point-wise** に展開した形で記述. `SwapNormalizationHypothesis.{u}` 全体が成立する
ことを意味するものではない. -/
theorem SwapNormalizationHypothesis_trivial_when_eq
    {β : Type*} [Fintype β] [DecidableEq β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (h_eq : ll a = ll b) :
    ∃ l_norm : β → ℕ,
      (∀ x, 0 < l_norm x) ∧
      (∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1) ∧
      l_norm a = l_norm b ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := by
  exact ⟨ll, hll_pos, hll_kraft, h_eq, le_refl _⟩

end InformationTheory.Shannon.Huffman
