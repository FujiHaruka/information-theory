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

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
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
    {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β]
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

/-! ### `Equiv.swap` の対称性 + 自明 case 拡張 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap 対称性**: `l ∘ Equiv.swap a m = l ∘ Equiv.swap m a` (Mathlib `Equiv.swap_comm`
を `∘` 形に持ち上げ). 後続 T1-A''' で「swap 順序非依存」を主張する step で利用. -/
theorem swap_comp_symm (l : α → ℕ) (a m : α) :
    l ∘ Equiv.swap a m = l ∘ Equiv.swap m a := by
  funext x
  show l ((Equiv.swap a m) x) = l ((Equiv.swap m a) x)
  rw [Equiv.swap_comm]

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap 値の対称性**: `(l ∘ Equiv.swap a m) m = l a` (代表値). swap 後の値が a と m を
入れ替えるという swap の defining property を `∘` 形で再公開. -/
theorem swap_value_at_m (l : α → ℕ) (a m : α) :
    (l ∘ Equiv.swap a m) m = l a := by
  show l ((Equiv.swap a m) m) = l a
  rw [Equiv.swap_apply_right]

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap 値の対称性 2**: `(l ∘ Equiv.swap a m) a = l m`. -/
theorem swap_value_at_a (l : α → ℕ) (a m : α) :
    (l ∘ Equiv.swap a m) a = l m := by
  show l ((Equiv.swap a m) a) = l m
  rw [Equiv.swap_apply_left]

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap 不動点**: `x ≠ a → x ≠ m → (l ∘ Equiv.swap a m) x = l x`. swap の点 outside
`{a, m}` での自明性を `∘` 形で再公開. -/
theorem swap_value_outside (l : α → ℕ) (a m x : α) (hxa : x ≠ a) (hxm : x ≠ m) :
    (l ∘ Equiv.swap a m) x = l x := by
  show l ((Equiv.swap a m) x) = l x
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxm]

/-! ### `SwapNormalizationHypothesis` 自明 case の対称性 -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **trivial case 対称性**: `ll a = ll b → ll b = ll a` で対称形 hypothesis も成立。
本 lemma は `SwapNormalizationHypothesis_trivial_when_eq` を symm 形に並置するだけで、
swap pair `(a, b)` の順序を反転した形を提供. -/
theorem SwapNormalizationHypothesis_trivial_when_eq_symm
    {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (h_eq : ll a = ll b) :
    ∃ l_norm : β → ℕ,
      (∀ x, 0 < l_norm x) ∧
      (∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1) ∧
      l_norm b = l_norm a ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := by
  exact ⟨ll, hll_pos, hll_kraft, h_eq.symm, le_refl _⟩

/-! ### Wave 4 — partial plumbing 補題 拡張群

下記は T1-A'' full discharge (judgement log #3 で「~550 行 / 4-6 セッション」と判定済の
不可能 scope) の **撤退ライン採用** に基づく拡張. 完全 discharge を作る代わりに、後続
seed T1-A''' (再着手) が呼び出すであろう plumbing extractor / trivial-case wrapper を
**partial** として publish.

判断ログ #2 で示された通り、bubble sort metric 上の strict descent は単純 metric では
保証不能 (`Equiv.Perm` 上の lex ordering が要)、本 wave は metric 経路を **scope-out**
し、`swap_step_le` 周辺の plumbing / `mergedMeasure` 値抽出 / 自明 case wrapper の
拡張に絞る.
-/

/-! #### Wave 4-A — `swap_step_le` の追加 combined extractor -/

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **`swap_step_le` combined extractor (positivity + Kraft)**: swap 後の `l'` が
positive かつ Kraft 和を維持する 2 条件をまとめた tuple. client が後続 step に
渡すときの両条件 forwarding を 1 呼び出しで済ませる. -/
theorem swap_step_le_pos_kraft
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    (∀ x, 0 < (l ∘ Equiv.swap a m) x) ∧
    (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ Equiv.swap a m) x : ℤ)) ≤ 1) := by
  refine ⟨?_, ?_⟩
  · exact swap_step_le_pos P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm
  · exact swap_step_le_kraft P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **`swap_step_le` triple extractor (positivity + Kraft + expectedLength)**: swap で
保たれる 3 条件をまとめて返す. `swap_step_le_pos_kraft` に `expectedLength_le` を
連結した形. -/
theorem swap_step_le_pos_kraft_exp
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    (∀ x, 0 < (l ∘ Equiv.swap a m) x) ∧
    (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ Equiv.swap a m) x : ℤ)) ≤ 1) ∧
    InformationTheory.Shannon.ShannonCode.expectedLength P (l ∘ Equiv.swap a m)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l := by
  refine ⟨?_, ?_, ?_⟩
  · exact swap_step_le_pos P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm
  · exact swap_step_le_kraft P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm
  · exact swap_step_le_expectedLength_le P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **`swap_step_le` value summary**: swap 後の `l'` の `a, m` 位置での値を tuple で
返す. `swap_step_le_values` の 2 つの値を独立位置で個別公開. -/
theorem swap_step_le_value_a
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    (l ∘ Equiv.swap a m) a = l m :=
  (swap_step_le_values P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm).1

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **`swap_step_le` value at m**: swap 後の `l' m = l a`. -/
theorem swap_step_le_value_m
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    (l ∘ Equiv.swap a m) m = l a :=
  (swap_step_le_values P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm).2

/-! #### Wave 4-B — `Equiv.swap` 関連 subsidiary 補題 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap 後の値が常に `{l a, l m, l x}` のいずれか**: `(l ∘ Equiv.swap a m) x` は
case-split で `l m / l a / l x` のいずれかに帰着する明示形. -/
theorem swap_value_cases (l : α → ℕ) (a m x : α) :
    (l ∘ Equiv.swap a m) x = l a ∨
    (l ∘ Equiv.swap a m) x = l m ∨
    (l ∘ Equiv.swap a m) x = l x := by
  by_cases hxa : x = a
  · right; left
    rw [hxa]
    show l ((Equiv.swap a m) a) = l m
    rw [Equiv.swap_apply_left]
  · by_cases hxm : x = m
    · left
      rw [hxm]
      show l ((Equiv.swap a m) m) = l a
      rw [Equiv.swap_apply_right]
    · right; right
      exact swap_value_outside l a m x hxa hxm

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap 順序対称性 (値版)**: `(l ∘ Equiv.swap a m) x = (l ∘ Equiv.swap m a) x` を
point-wise で. `swap_comp_symm` の `∘` 関数等式から point-wise 版を直接導出. -/
theorem swap_value_symm (l : α → ℕ) (a m x : α) :
    (l ∘ Equiv.swap a m) x = (l ∘ Equiv.swap m a) x := by
  have h := swap_comp_symm l a m
  exact congrFun h x

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap 自己合成の値**: `(l ∘ Equiv.swap a m) ((Equiv.swap a m) x) = l x`.
`swap_compose_self_comp` の point-wise 版. -/
theorem swap_compose_self_value (l : α → ℕ) (a m x : α) :
    (l ∘ Equiv.swap a m) ((Equiv.swap a m) x) = l x := by
  have h := swap_compose_self_comp l a m
  exact congrFun h x

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap 不動点 (refl 化)**: `a = m` の場合は `Equiv.swap m m = Equiv.refl α`
(Mathlib `Equiv.swap_self`). `Equiv` レベルでの恒等性を明示形で公開. -/
theorem swap_self_eq_refl (m : α) :
    Equiv.swap m m = Equiv.refl α := Equiv.swap_self m

/-! #### Wave 4-C — `mergedMeasure` 値分解 plumbing extractor -/

omit [Fintype α] [Nonempty α] in
/-- **`mergedMeasure_real` at `a`**: `x.val = a` の case で
`mergedMeasure Q a b hab .real {x} = Q.real {a} + Q.real {b}`. -/
theorem mergedMeasure_real_at_a
    (Q : Measure α) [IsProbabilityMeasure Q]
    (a b : α) (hab : a ≠ b)
    (x : { y : α // y ≠ b }) (hxa : x.val = a) :
    (mergedMeasure Q a b hab).real {x} = Q.real {a} + Q.real {b} := by
  rw [mergedMeasure_real Q a b hab x]
  simp [hxa]

omit [Fintype α] [Nonempty α] in
/-- **`mergedMeasure_real` at non-a**: `x.val ≠ a` の case で
`(mergedMeasure Q a b hab).real {x} = Q.real {x.val}`. -/
theorem mergedMeasure_real_at_other
    (Q : Measure α) [IsProbabilityMeasure Q]
    (a b : α) (hab : a ≠ b)
    (x : { y : α // y ≠ b }) (hxa : x.val ≠ a) :
    (mergedMeasure Q a b hab).real {x} = Q.real {x.val} := by
  rw [mergedMeasure_real Q a b hab x]
  simp [hxa]

omit [Fintype α] [Nonempty α] in
/-- **`mergedMeasure_pos` at `a` (= sum positivity)**: hP positivity の下で
`(mergedMeasure Q a b hab).real {x} > 0` を `x.val = a` 限定で直接公開. -/
theorem mergedMeasure_pos_at_a
    (Q : Measure α) [IsProbabilityMeasure Q] (hQ : ∀ y, 0 < Q.real {y})
    (a b : α) (hab : a ≠ b)
    (x : { y : α // y ≠ b }) (hxa : x.val = a) :
    0 < (mergedMeasure Q a b hab).real {x} := by
  rw [mergedMeasure_real_at_a Q a b hab x hxa]
  exact add_pos (hQ a) (hQ b)

omit [Fintype α] [Nonempty α] in
/-- **`mergedMeasure_pos` at non-a**: hP positivity の下で
`(mergedMeasure Q a b hab).real {x} > 0` を `x.val ≠ a` 限定で直接公開. -/
theorem mergedMeasure_pos_at_other
    (Q : Measure α) [IsProbabilityMeasure Q] (hQ : ∀ y, 0 < Q.real {y})
    (a b : α) (hab : a ≠ b)
    (x : { y : α // y ≠ b }) (hxa : x.val ≠ a) :
    0 < (mergedMeasure Q a b hab).real {x} := by
  rw [mergedMeasure_real_at_other Q a b hab x hxa]
  exact hQ x.val

omit [Fintype α] [Nonempty α] in
/-- **`mergedMeasure_real` の sum 上限保存**: `Q.real {a} + Q.real {b}` が `Q` 全体の
sum (= 1, probability measure) で押さえられる. -/
theorem mergedMeasure_real_at_a_le_one
    (Q : Measure α) [IsProbabilityMeasure Q] (_hQ : ∀ y, 0 < Q.real {y})
    (a b : α) (hab : a ≠ b)
    (x : { y : α // y ≠ b }) (hxa : x.val = a) :
    (mergedMeasure Q a b hab).real {x} ≤ 1 := by
  rw [mergedMeasure_real_at_a Q a b hab x hxa]
  -- Q.real {a} + Q.real {b} ≤ Q.real Set.univ = 1 (∵ {a, b} ⊆ univ + disjoint)
  have h_disjoint : Disjoint ({a} : Set α) {b} := by
    rw [Set.disjoint_singleton]; exact hab
  have h_union : Q.real ({a} ∪ {b}) = Q.real {a} + Q.real {b} := by
    rw [measureReal_union h_disjoint (MeasurableSet.singleton b)]
  have h_le_univ : Q.real ({a} ∪ {b}) ≤ Q.real Set.univ :=
    measureReal_mono (Set.subset_univ _) (measure_ne_top Q Set.univ)
  have h_univ : Q.real Set.univ = 1 := by
    rw [measureReal_def]
    rw [measure_univ]
    simp
  rw [h_union] at h_le_univ
  rw [h_univ] at h_le_univ
  exact h_le_univ

/-! #### Wave 4-D — `SwapNormalizationHypothesis` 自明 case の `Equiv.swap` 連携 -/

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **trivial case via swap (`l a = l b`)**: `Equiv.swap` を経由しても自明形 hypothesis が
そのまま成立する補題. `Equiv.swap a b ∘ Equiv.swap a b = id` の involution を用いて
`l_norm := ll` を保持する形で discharge. swap を 0 段挿入する場合の identity. -/
theorem SwapNormalizationHypothesis_trivial_when_eq_via_swap
    {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (h_eq : ll a = ll b) :
    ∃ l_norm : β → ℕ,
      (∀ x, 0 < l_norm x) ∧
      (∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1) ∧
      l_norm a = l_norm b ∧
      l_norm = ll ∘ Equiv.swap a b ∘ Equiv.swap a b ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := by
  refine ⟨ll, hll_pos, hll_kraft, h_eq, ?_, le_refl _⟩
  funext x
  show ll x = ll ((Equiv.swap a b) ((Equiv.swap a b) x))
  by_cases hxa : x = a
  · subst hxa; rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · by_cases hxb : x = b
    · subst hxb; rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb,
          Equiv.swap_apply_of_ne_of_ne hxa hxb]

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **swap-based trivial discharge witness**: `ll a = ll b` の入力に対し、`l_norm` を
`ll` ではなく `ll ∘ Equiv.swap a b` で取り直しても hypothesis が成立する代替 witness.
swap で値が `(a, b)` 間で入れ替わるが `ll a = ll b` の下で `l_norm a = l_norm b` は
`ll b = ll a` (= `ll a = ll b` の symm) で成立. -/
theorem SwapNormalizationHypothesis_trivial_via_single_swap
    {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (_hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (h_eq : ll a = ll b) :
    ∃ l_norm : β → ℕ,
      (∀ x, 0 < l_norm x) ∧
      l_norm a = l_norm b ∧
      l_norm = ll ∘ Equiv.swap a b := by
  refine ⟨ll ∘ Equiv.swap a b, ?_, ?_, rfl⟩
  · intro x; exact hll_pos _
  · show ll ((Equiv.swap a b) a) = ll ((Equiv.swap a b) b)
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact h_eq.symm

/-! #### Wave 4-E — Kraft 不等式の swap 不変性 補題 -/

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Kraft sum の swap 不変性 (等式形)**: `Equiv.swap` permutation で Kraft 和は
不変 (`Equiv.sum_comp` の specialization). swap step での Kraft 不等式の保持を
言うために、まず等式形を独立 publish. -/
theorem kraft_sum_swap_eq
    (l : α → ℕ) (a m : α) :
    (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ Equiv.swap a m) x : ℤ)))
      = ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) := by
  classical
  set σ : α ≃ α := Equiv.swap a m
  show (∑ x : α, ((2 : ℝ)) ^ (-(l (σ x) : ℤ)))
    = ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ))
  exact Equiv.sum_comp σ (fun x => ((2 : ℝ)) ^ (-(l x : ℤ)))

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Kraft 不等式の swap 不変性 (≤ 1 形)**: 上記等式から従う ≤ 1 形. -/
theorem kraft_sum_swap_le_one
    (l : α → ℕ) (a m : α)
    (h_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1) :
    (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ Equiv.swap a m) x : ℤ))) ≤ 1 := by
  rw [kraft_sum_swap_eq l a m]; exact h_kraft

/-! #### Wave 4-F — Equiv.swap の合成可換性 / 値 case の系 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **`Equiv.swap` の `a = b` での恒等性 (値版)**: `Equiv.swap m m x = x`. -/
theorem swap_self_value (m x : α) :
    (Equiv.swap m m) x = x := by
  rw [Equiv.swap_self]; rfl

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap の値 (left)**: `(Equiv.swap a m) a = m`. Mathlib `Equiv.swap_apply_left` の
非 `∘` 版を独立 lemma に持ち上げ. 後続 proof で `show` ステップを 1 つ削減. -/
theorem swap_apply_left' (a m : α) : (Equiv.swap a m) a = m :=
  Equiv.swap_apply_left a m

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap の値 (right)**: `(Equiv.swap a m) m = a`. -/
theorem swap_apply_right' (a m : α) : (Equiv.swap a m) m = a :=
  Equiv.swap_apply_right a m

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap 後の値 = swap 前の値 (対角 case)**: `(l ∘ Equiv.swap a a) x = l x`. -/
theorem swap_diag_value (l : α → ℕ) (a x : α) :
    (l ∘ Equiv.swap a a) x = l x := by
  show l ((Equiv.swap a a) x) = l x
  rw [swap_self_value a x]

/-! #### Wave 4-G — 自明 case wrapper の対称性 + 派生 -/

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **trivial wrapper at `a = b` (≠ 条件 + `ll a = ll b`)**: `a ≠ b` の入力 + `ll a = ll b`
で自明 hypothesis を直接 discharge する形. swap pair `(a, b)` の `a ≠ b` 制約を保持. -/
theorem SwapNormalizationHypothesis_trivial_with_neq
    {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (_hab : a ≠ b) (h_eq : ll a = ll b) :
    ∃ l_norm : β → ℕ,
      (∀ x, 0 < l_norm x) ∧
      (∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1) ∧
      l_norm a = l_norm b ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll :=
  SwapNormalizationHypothesis_trivial_when_eq Q ll hll_pos hll_kraft a b h_eq

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **trivial wrapper packaged tuple form**: 上記 discharge の 4 条件を **structure 風
tuple** にした形. client が `obtain ⟨l, h1, h2, h3, h4⟩` で取り出せる. -/
theorem SwapNormalizationHypothesis_trivial_tuple
    {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (h_eq : ll a = ll b) :
    ∃ l_norm : β → ℕ,
      ((∀ x, 0 < l_norm x) ∧
       (∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1)) ∧
      (l_norm a = l_norm b ∧
       InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
         ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll) := by
  refine ⟨ll, ⟨hll_pos, hll_kraft⟩, h_eq, le_refl _⟩

/-! #### Wave 4-H — `huffmanLength_optimal` partial wrapper (3-arg + 2-arg form)

`huffmanLength_optimal_with_hypotheses` (1054 行 / weak form) を呼び出す側の負担を
軽くする partial wrapper. `h_swap` と `h_ident` を引数で取りつつ、`{α : Type u}` →
`{α : Type*}` の universe relaxation で wrapping. 強形 `huffmanLength_optimal`
(hypothesis なし) は本 plan scope-out のため、wrapping 形のみ提供.
-/

universe v

/-- **partial wrapper (weak form, level-polymorphic)**: T1-A' weak form
`huffmanLength_optimal_with_hypotheses` を `{α : Type v}` universe で wrap. 既存の
universe-`u` 形をそのまま呼び出すだけだが、後続 seed で `{α : Type*}` 呼び出しを
拾う用.

`@audit:suspect(huffman-t1apprime-partial-moonshot-plan)` -/
theorem huffmanLength_optimal_with_hypotheses_at
    {α : Type v} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h_swap : SwapNormalizationHypothesis.{v})
    (h_ident : HuffmanMergedIdentificationHypothesis.{v})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses h_swap h_ident P hP l hl_pos hl_kraft

/-- **partial wrapper (combined hypothesis tuple form)**: 2 hypothesis を tuple
形に combine した形の wrapper. client は `⟨h_swap, h_ident⟩` で渡せる.

`@audit:suspect(huffman-t1apprime-partial-moonshot-plan)` -/
theorem huffmanLength_optimal_with_combined_hypothesis
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : SwapNormalizationHypothesis.{u} ∧ HuffmanMergedIdentificationHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses h.1 h.2 P hP l hl_pos hl_kraft

/-! #### Wave 4-I — Cover-Thomas Lemma 5.8.1 (i) の partial discharge 形 -/

/-- **Hypothesis 1 partial — `ll a = ll b` を仮定する形**: 入力で既に `ll a = ll b` が
成立している場合の `SwapNormalizationHypothesis` 結論を直接 publish. 任意の `(a, b)`
最小 prob pair に対して `l_norm a = l_norm b` が必要だが、本 partial は **`ll a = ll b`
を追加仮定** にする形で discharge する弱形. -/
theorem SwapNormalizationHypothesis_at_pair_when_eq
    {β : Type*} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (_hab : a ≠ b)
    (_h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (_h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (_h_card : 3 ≤ Fintype.card β)
    (h_eq : ll a = ll b) :
    ∃ l_norm : β → ℕ,
      (∀ x, 0 < l_norm x) ∧
      (∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1) ∧
      l_norm a = l_norm b ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll :=
  SwapNormalizationHypothesis_trivial_when_eq Q ll hll_pos hll_kraft a b h_eq

/-! #### Wave 4-J — `Equiv.swap` の合成・引き戻し計算 plumbing -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap involutive (個別形 `a`)**: `Equiv.swap a m` の involution を `a` 位置で確認. -/
theorem swap_involutive_at_a (a m : α) :
    (Equiv.swap a m) ((Equiv.swap a m) a) = a := by
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right]

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap involutive (個別形 `m`)**: `Equiv.swap a m` の involution を `m` 位置で確認. -/
theorem swap_involutive_at_m (a m : α) :
    (Equiv.swap a m) ((Equiv.swap a m) m) = m := by
  rw [Equiv.swap_apply_right, Equiv.swap_apply_left]

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap involutive (一般形 `x`)**: `Equiv.swap a m` の involution を任意点 `x` で確認.
`swap_compose_self_comp` の応用. -/
theorem swap_involutive_at (a m x : α) :
    (Equiv.swap a m) ((Equiv.swap a m) x) = x := by
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · by_cases hxm : x = m
    · subst hxm
      rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxm,
          Equiv.swap_apply_of_ne_of_ne hxa hxm]

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap inverse は自己と等しい**: `(Equiv.swap a m).symm = Equiv.swap a m`. -/
theorem swap_symm_eq (a m : α) :
    (Equiv.swap a m).symm = Equiv.swap a m := Equiv.symm_swap a m

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap 2 回適用は恒等 (Equiv 形)**: `(Equiv.swap a m).trans (Equiv.swap a m) = Equiv.refl α`.
Mathlib `Equiv.swap_swap` の `trans` 形ラッピング. -/
theorem swap_trans_self (a m : α) :
    (Equiv.swap a m).trans (Equiv.swap a m) = Equiv.refl α := by
  ext x; exact swap_involutive_at a m x

/-! #### Wave 4-K — Equiv.swap permutation の sum invariance -/

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **swap 経由 expectedLength の総量保存に対する補題**: swap step での expectedLength を
`Equiv.sum_comp` 形に持ち上げた等式. swap で expectedLength 値そのものは変わるが、
**台が同じ index set にわたる sum** であることを明示形で提供. -/
theorem expectedLength_swap_via_sum_comp
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (a m : α) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (l ∘ Equiv.swap a m)
      = ∑ x : α, P.real {x} * ((l ((Equiv.swap a m) x) : ℝ)) := by
  unfold InformationTheory.Shannon.ShannonCode.expectedLength
  rfl

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **`swap_step_le` の expectedLength 結論を再呼び出ししやすい形に整形**: `l ∘ Equiv.swap a m`
と `l` の expectedLength の差を `(P.real {m} - P.real {a}) * (l m - l a)` で押さえる
明示形. ただし本 partial は `swap_step_le_expectedLength_le` を呼ぶ wrapping. -/
theorem expectedLength_swap_le
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (l ∘ Equiv.swap a m)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  swap_step_le_expectedLength_le P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm

/-! #### Wave 4-L — swap argument 2-step composition の plumbing -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **2 swap composition (異なる pair)**: `l ∘ Equiv.swap a m ∘ Equiv.swap c d` の **値**
を pair で表現. ただし非交叉 case の point-wise 簡約は別 lemma, ここでは composed
function を `l (swap c d (swap a m x))` 形に展開する純粋等式. -/
theorem swap_compose_two_value (l : α → ℕ) (a m c d x : α) :
    (l ∘ Equiv.swap c d ∘ Equiv.swap a m) x
      = l ((Equiv.swap c d) ((Equiv.swap a m) x)) := rfl

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **2 swap composition (同 pair = identity)**: 同 pair の 2 swap は恒等. -/
theorem swap_compose_same_pair (l : α → ℕ) (a m : α) :
    l ∘ Equiv.swap a m ∘ Equiv.swap a m = l :=
  swap_compose_self_comp l a m

/-! #### Wave 4-M — Hypothesis discharge を **`Equiv.swap a b` で構成する partial 構築** -/

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **swap 後 expectedLength の trivial 上限**: `ll a = ll b` の入力では swap が
expectedLength を変えない (両側で同じ係数), つまり `expectedLength P (ll ∘ Equiv.swap a b)
= expectedLength P ll` (≤). swap で `(a, b)` 位置の `ll` 値が入れ替わるが値が等しいから
不変. -/
theorem expectedLength_swap_eq_when_ll_eq
    (P : Measure α) [IsProbabilityMeasure P]
    (ll : α → ℕ) (a b : α) (h_eq : ll a = ll b) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (ll ∘ Equiv.swap a b)
      = InformationTheory.Shannon.ShannonCode.expectedLength P ll := by
  unfold InformationTheory.Shannon.ShannonCode.expectedLength
  apply Finset.sum_congr rfl
  intro x _
  show P.real {x} * ((ll ((Equiv.swap a b) x) : ℝ)) = P.real {x} * ((ll x : ℝ))
  congr 1
  by_cases hxa : x = a
  · subst hxa
    rw [Equiv.swap_apply_left]
    exact_mod_cast h_eq.symm
  · by_cases hxb : x = b
    · subst hxb
      rw [Equiv.swap_apply_right]
      exact_mod_cast h_eq
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **swap 後 expectedLength の `≤` 形**: 上記等式の `≤` 形 (≤ 1 形より弱いが client が
swap step で要求しがちな形). -/
theorem expectedLength_swap_le_when_ll_eq
    (P : Measure α) [IsProbabilityMeasure P]
    (ll : α → ℕ) (a b : α) (h_eq : ll a = ll b) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (ll ∘ Equiv.swap a b)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P ll :=
  le_of_eq (expectedLength_swap_eq_when_ll_eq P ll a b h_eq)

/-! #### Wave 4-N — `Function.update` との交換性 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **`Function.update` の自己更新**: `Function.update l a (l a) = l`. Mathlib
`Function.update_eq_self` の rewriting 形. -/
theorem update_self_eq (l : α → ℕ) (a : α) :
    Function.update l a (l a) = l := Function.update_eq_self a l

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **`Function.update` の固定点**: `Function.update l a v a = v`. -/
theorem update_at (l : α → ℕ) (a : α) (v : ℕ) :
    Function.update l a v a = v := Function.update_self _ _ _

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **`Function.update` の非更新点**: `Function.update l a v x = l x` if `x ≠ a`. -/
theorem update_at_other (l : α → ℕ) (a x : α) (v : ℕ) (hxa : x ≠ a) :
    Function.update l a v x = l x := Function.update_of_ne hxa _ _

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **`Function.update` の二重 update**: `update (update l a u) a v = update l a v`. -/
theorem update_idem_eq (l : α → ℕ) (a : α) (u v : ℕ) :
    Function.update (Function.update l a u) a v = Function.update l a v :=
  Function.update_idem u v l

/-! #### Wave 4-O — Equiv composition の Equiv.swap 計算 -/

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap composition with refl**: `Equiv.swap a m ∘ Equiv.refl α = Equiv.swap a m`
(値版). -/
theorem swap_comp_refl_value (l : α → ℕ) (a m x : α) :
    (l ∘ Equiv.swap a m ∘ Equiv.refl α) x = (l ∘ Equiv.swap a m) x := rfl

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap (a, a) composition is identity**: `l ∘ Equiv.swap a a = l`. -/
theorem swap_diag_comp (l : α → ℕ) (a : α) :
    l ∘ Equiv.swap a a = l := by
  funext x; exact swap_diag_value l a x

omit [Fintype α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **swap (a, m) と swap (m, a) は同関数 (値版)**: 任意 `x` で値が等しい. -/
theorem swap_comm_value (l : α → ℕ) (a m x : α) :
    l ((Equiv.swap a m) x) = l ((Equiv.swap m a) x) := by
  rw [Equiv.swap_comm]

/-! #### Wave 4-P — partial form の `huffmanLength_optimal` 補題集

`huffmanLength_optimal` の完全 form (= hypothesis なし) は本 plan scope-out (judgement
log #2-#3 の不可能 scope). 代替に **partial form** (= hypothesis 引数つきの様々な
wrapper) を集める. これらは後続 seed T1-A''' で hypothesis を discharge した瞬間に
強形を一発で生成する terminal step として使える. -/

/-- **partial wrapper: hypothesis を tuple で **`Σ`-pair** 化**: 2 hypothesis を非依存
`Σ`-pair で取り出す形. inhabited `PProd` 風.

`@audit:suspect(huffman-t1apprime-partial-moonshot-plan)` -/
theorem huffmanLength_optimal_with_pair_hypothesis
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : PProd (SwapNormalizationHypothesis.{u}) (HuffmanMergedIdentificationHypothesis.{u}))
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses h.fst h.snd P hP l hl_pos hl_kraft

/-- **partial wrapper: contraposition form**: 結論を否定の対偶形で publish. 後続
client が strict 不等式から逆向きに矛盾を起こす useful な form.

`@audit:suspect(huffman-t1apprime-partial-moonshot-plan)` -/
theorem huffmanLength_optimal_with_hypotheses_contra
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h_swap : SwapNormalizationHypothesis.{u})
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1)
    (h_lt : InformationTheory.Shannon.ShannonCode.expectedLength P l
             < InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)) :
    False :=
  absurd (huffmanLength_optimal_with_hypotheses h_swap h_ident P hP l hl_pos hl_kraft)
    (not_le_of_gt h_lt)

end InformationTheory.Shannon.Huffman
