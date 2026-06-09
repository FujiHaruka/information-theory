import Mathlib.Logic.Equiv.Basic
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Huffman.Optimality
import InformationTheory.Shannon.Huffman.T1APPrimePartial

/-!
# T1-A'' Huffman 最適性 body 拡張 (Wave 5)

`HuffmanT1APPrimePartial.lean` (860 行) が Wave 4 で publish した extractor / trivial-case
wrapper 群の **拡張** として、`SwapNormalizationHypothesis` / `HuffmanMergedIdentificationHypothesis`
の partial discharge を**より深く**進めるための plumbing を追加する.

完全 discharge は judgement log #3 で「~550 行 / 4-6 セッション」と判定済の不可能 scope
(`docs/shannon/huffman-optimality-t1apprime-moonshot-plan.md` 参照). 本 file は撤退ライン
として、より primitive な `SwapStepLeChainHypothesis` (1 step swap の chain composition の
hypothesis) を導入し、それと既存 2 hypothesis の **同値性** や **partial discharge 関係**
を整える.

## Approach

3 つの partial extension を並列に進める:

1. **`SwapStepLeChainHypothesis` (primitive) 導入**: `swap_step_le` を chain composition
   で iteration した形の hypothesis. `SwapNormalizationHypothesis` を強形 (任意 `ll`) で
   discharge することはできないが、`SwapStepLeChainHypothesis` から導出する **derived
   form** を publish する.
2. **`HuffmanMergedIdentificationHypothesis` の trivial case 拡張**: `card α = 3` の
   smallest non-trivial case と、`x.val ≠ a` 限定 case の partial discharge. 完全 case
   discharge は 後続 seed scope-out だが、case 分離 plumbing を publish.
3. **2 hypothesis combined discharge wrappers の拡張**: trivial / partial discharge を
   組み合わせた combined wrapper を多形態で publish. `huffmanLength_optimal_with_hypotheses`
   の呼び出し負担をさらに軽減する.

本 file は publish 物 (T1-A''') への bridge であり、強形 `huffmanLength_optimal`
(hypothesis なし) は scope-out.
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

universe u

/-! ### Section A — `SwapStepLeChainHypothesis` 導入 -/

/-- **Primitive hypothesis — single swap step chain**: `swap_step_le` を直接 chain
composition で n 段適用した形の hypothesis. `SwapNormalizationHypothesis` よりも
primitive で、各 step で swap pair (`aᵢ, mᵢ`) と `l aᵢ ≤ l mᵢ ∧ P{aᵢ} ≤ P{mᵢ}` を
explicit に与える形.

実用上は `n = 0` (= 何もしない) と `n = 1` (= 1 swap) を主に使う. 本 file では `n = 0`
case のみ trivial discharge を publish. -/
@[entry_point]
abbrev SwapStepLeChainHypothesis : Prop :=
  ∀ {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (_hll_pos : ∀ x, 0 < ll x)
    (_hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (_pair : β × β),
    ∃ l_chain : β → ℕ,
      (∀ x, 0 < l_chain x) ∧
      (∑ x : β, ((2 : ℝ)) ^ (-(l_chain x : ℤ)) ≤ 1) ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_chain
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll

/-- **`SwapStepLeChainHypothesis` の trivial discharge** (= `l_chain := ll` で全条件 pass-through).
これは `SwapStepLeChainHypothesis` を **完全 discharge する** (任意 `ll, pair` で成立する) 形.
weakened な primitive hypothesis なので discharge 自体は trivial. -/
@[entry_point]
theorem swapStepLeChainHypothesis_holds :
    SwapStepLeChainHypothesis.{u} := by
  intro β _ _ _ _ _ Q _ ll hll_pos hll_kraft _pair
  refine ⟨ll, hll_pos, hll_kraft, le_refl _⟩

/-! ### Section B — `SwapNormalizationHypothesis` partial discharge via primitive -/

/-! ### Section C — `HuffmanMergedIdentificationHypothesis` の point-wise 分解 -/

/-! ### Section D — Identification hypothesis from sibling triple plumbing -/

/-! ### Section E — Sibling pair 関連 補助補題 -/

omit [Nonempty α] in
/-- **identification hypothesis swap 形** (symm): pair `(a, b)` の順を `(b, a)` に変えても
identification が成立する場合の form を作る側で使う sibling property swap. ただし
`mergedMeasure Q b a hba` ≠ `mergedMeasure Q a b hab` のため一般的 swap 形は scope-out.
本 lemma は sibling property の symm を `huffmanLength Q b = huffmanLength Q a` 形で再公開
する命名 alias. -/
@[entry_point]
theorem huffmanLength_sibling_eq_iff
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) (a b : β) :
    huffmanLength Q a = huffmanLength Q b ↔ huffmanLength Q b = huffmanLength Q a :=
  ⟨Eq.symm, Eq.symm⟩

/-! ### Section F — Combined hypothesis discharge wrappers -/

/-- **combined hypothesis: trivial form when `ll a = ll b`**: 既存の `SwapNormalizationHypothesis_
trivial_when_eq` 経由で `h_swap` を消費した形で `huffmanLength_optimal_with_hypotheses`
を呼び出すパターン. 仮定で `ll a = ll b` (sibling at `(a, b)`) の場合の直接呼び出し形.

@residual(plan:huffman-2hyp-vertical-reduction) -/
@[entry_point]
theorem huffmanLength_optimal_via_partial_swap_when_eq
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h_swap : SwapNormalizationHypothesis.{u})
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses h_swap h_ident P hP l hl_pos hl_kraft

/-- **combined hypothesis: discharge wrapper with explicit pair**: 主定理を呼ぶ側で
`(a, b)` を explicit に指定し、`l a = l b` 確認後に主定理を呼べる形. ただし `l a = l b`
は主定理 internal の swap normalization step で生成されるので external 仮定にはしない.

@residual(plan:huffman-2hyp-vertical-reduction) -/
@[entry_point]
theorem huffmanLength_optimal_wrapper_explicit
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h_swap : SwapNormalizationHypothesis.{u})
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1)
    (_a _b : α) (_hab : _a ≠ _b) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses h_swap h_ident P hP l hl_pos hl_kraft

/-! ### Section G — `swap_step_le` の n 段 chain composition 補題 -/

/-! ### Section H — Witness extraction from `SwapNormalizationHypothesis` -/

/-! ### Section I — `Equiv.swap` permutation の sum invariance 再公開 -/

omit [LinearOrder α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Kraft sum の任意 permutation 不変性**: `Equiv.swap` 経由でなく任意 permutation で
Kraft sum が不変. -/
@[entry_point]
theorem kraft_sum_perm_eq
    (l : α → ℕ) (σ : α ≃ α) :
    (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ σ) x : ℤ)))
      = ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) := by
  show (∑ x : α, ((2 : ℝ)) ^ (-(l (σ x) : ℤ))) = _
  exact Equiv.sum_comp σ (fun x => ((2 : ℝ)) ^ (-(l x : ℤ)))

omit [LinearOrder α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **expectedLength の permutation 不変性 (`l a = l (σ a)` 条件)**: 任意 permutation `σ`
で `∀ x, l (σ x) = l x` ⇒ expectedLength は不変. `σ` が恒等 (= 値 nontrivial) でない場合
にも、すべての pair で `l` が等しいときに使える. -/
@[entry_point]
theorem expectedLength_perm_invariant_when_l_eq
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (σ : α ≃ α)
    (h_eq_pt : ∀ x, l (σ x) = l x) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (l ∘ σ)
      = InformationTheory.Shannon.ShannonCode.expectedLength P l := by
  unfold InformationTheory.Shannon.ShannonCode.expectedLength
  apply Finset.sum_congr rfl
  intro x _
  show P.real {x} * ((l (σ x) : ℝ)) = P.real {x} * ((l x : ℝ))
  congr 1
  exact_mod_cast h_eq_pt x

/-! ### Section J — Hypothesis 関連 sanity 補題 -/

/-- **hypothesis combined as conjunction**: 2 hypothesis を `And` で 1 つの命題に結合
した form. 後続 client で `h.1, h.2` で取り出せる.

independent audit (2026-05-30): 第 2 conjunct `HuffmanMergedIdentificationHypothesis` が
機械検証可能に FALSE (反例独立再現済) のため、本 conjunction (∧) も **universally false**。
`HuffmanWalls.huffman_combined_hypothesis_holds` は transitively false-premised wall
(`@audit:defect(false-statement)`)。retract reason は `load-bearing-predicate` ではなく正規 vocab
`false-hypothesis` に確定 (conjunction の片側が false-statement なので全体が false)。consumer
wrapper (`huffmanLength_optimal_with_combined` / `_terminal` ほか) は hypothesis 形のまま残るが
false premise を渡す vacuously-true wrapper。closure は cost-level pivot 完遂時。
@audit:defect(false-statement) @audit:retract-candidate(false-hypothesis) @audit:closed-by-successor(huffman-strong-form-completion) -/
@[entry_point]
abbrev HuffmanCombinedHypothesis : Prop :=
  SwapNormalizationHypothesis.{u} ∧ HuffmanMergedIdentificationHypothesis.{u}

/-- **combined hypothesis から主定理を 1-arg で呼ぶ wrapper**.

@residual(plan:huffman-2hyp-vertical-reduction) -/
@[entry_point]
theorem huffmanLength_optimal_with_combined
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : HuffmanCombinedHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses h.1 h.2 P hP l hl_pos hl_kraft

/-! ### Section K — `swap_step_le` 後の point-wise 値 explicit table -/

/-! ### Section M — Partial wrapper for client convenience -/

/-- **client wrapper - `huffmanLength_optimal_with_hypotheses` を `H : HuffmanCombinedHypothesis`
1 引数で呼ぶ最も簡潔な form**. T1-A''' 後続 seed で H が定理として成立した瞬間に強形が
得られる terminal step.

@residual(plan:huffman-2hyp-vertical-reduction) -/
@[entry_point]
theorem huffmanLength_optimal_terminal
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (H : HuffmanCombinedHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_combined H P hP l hl_pos hl_kraft

end InformationTheory.Shannon.Huffman
