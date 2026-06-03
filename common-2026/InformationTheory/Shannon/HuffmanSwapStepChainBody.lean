import Mathlib.Logic.Equiv.Basic
import InformationTheory.Shannon.HuffmanOptimality
import InformationTheory.Shannon.HuffmanT1APPrimePartial
import InformationTheory.Shannon.HuffmanT1APPrimeBody
import InformationTheory.Meta.EntryPoint

/-!
# T1-A'' Huffman SwapStepLe chain body 拡張 (Wave 9)

`HuffmanT1APPrimeBody.lean` (wave6 publish) が `SwapStepLeChainHypothesis` を primitive
predicate 化し、trivial discharge + `Equiv.swap a b` alt-witness を publish した。本 file は
更に **SwapStepLe chain の body discharge** を進める。

完全な hypothesis discharge (`SwapNormalizationHypothesis` / `HuffmanMergedIdentificationHypothesis`
の強形証明) は judgement log #3 で「~550 行 / 4-6 セッション」と判定済の不可能 scope
(`docs/shannon/huffman-optimality-t1apprime-moonshot-plan.md` 参照). 本 file は撤退ライン
として、`SwapStepLeChainHypothesis` を更に細分し:

1. **chain composition (n-step swap = `Equiv.Perm` 経由分解)** の sub-predicate 化。
2. **n-step swap normalization の lift** (任意 permutation chain の pointwise-eq 不変性)。
3. **universe-polymorphic discharge** の corollary 群。
4. **`HuffmanCombinedHypothesis` wrapper の reduce 形** re-publish。

を整える。本 file は publish 物 (T1-A''') への bridge であり、強形 `huffmanLength_optimal`
(hypothesis なし) は scope-out。

## Approach

SwapStepLe chain を「permutation の合成」として捉え直す。1 swap step は `Equiv.swap a m`
で表現され、n-step chain は `σ₁.trans σ₂.trans ... σₙ` という `Equiv.Perm α` の合成になる。
このとき:

- **Kraft sum** は任意 permutation で不変 (`Equiv.sum_comp`)。chain でも commute するので
  `kraft_sum_perm_chain_eq` で n-step まで一気に押さえる。
- **expectedLength** は pointwise で `l (σ x) = l x` が成立する permutation でのみ不変
  (値が動かない場合)。chain の各 step がこの条件を満たすなら chain 全体で不変。
- **n-step swap normalization lift** は、各 step の swap が `ll a = ll b` 型 trivial pair
  に対する swap であるとき、chain 後も `ll` が pointwise 不変 ⇒ expectedLength / Kraft
  維持。これを `SwapStepLeChainHypothesis` の derived discharge form として publish。

primitive predicate `SwapStepLeChainHypothesis` (wave6) を 2 つの sub-predicate
(`PermChainKraftPreserving` / `PermChainExpectedLengthPreserving`) に分解し、それぞれが
trivial に成立すること、そして両者から `SwapStepLeChainHypothesis` が再構成できることを
示す。最後に `HuffmanCombinedHypothesis` の reduce 形 wrapper を多形態で再公開する。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

universe u

/-! ### Section A — permutation chain の Kraft 不変性 (n-step) -/

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **permutation chain の Kraft 不変性 (2-step)**: 2 つの permutation `σ τ` を合成しても
Kraft 和は不変. `kraft_sum_perm_eq` (wave6) の chain composition. -/
@[entry_point]
theorem kraft_sum_perm_chain2_eq
    (l : α → ℕ) (σ τ : α ≃ α) :
    (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ σ ∘ τ) x : ℤ)))
      = ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) := by
  -- (l ∘ σ ∘ τ) x = (l ∘ σ) (τ x), so apply sum_comp for τ then for σ.
  have h1 : (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ σ ∘ τ) x : ℤ)))
      = ∑ x : α, ((2 : ℝ)) ^ (-((l ∘ σ) x : ℤ)) := by
    show (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ σ) (τ x) : ℤ))) = _
    exact Equiv.sum_comp τ (fun x => ((2 : ℝ)) ^ (-((l ∘ σ) x : ℤ)))
  rw [h1]
  exact kraft_sum_perm_eq l σ

/-! ### Section B — permutation chain の expectedLength 不変性 (pointwise-eq) -/

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **permutation chain の expectedLength 不変性 (2-step, pointwise-eq)**: 2 permutation の
合成 `σ ∘ τ` で `∀ x, l (σ (τ x)) = l x` が成立するとき expectedLength は不変. -/
@[entry_point]
theorem expectedLength_perm_chain2_invariant
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (σ τ : α ≃ α)
    (h_eq_pt : ∀ x, l (σ (τ x)) = l x) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (l ∘ σ ∘ τ)
      = InformationTheory.Shannon.ShannonCode.expectedLength P l := by
  unfold InformationTheory.Shannon.ShannonCode.expectedLength
  apply Finset.sum_congr rfl
  intro x _
  show P.real {x} * ((l (σ (τ x)) : ℝ)) = P.real {x} * ((l x : ℝ))
  congr 1
  exact_mod_cast h_eq_pt x

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **permutation chain の expectedLength `≤` 形**: 上記等式の `≤` 形. -/
@[entry_point]
theorem expectedLength_perm_chain2_le
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (σ τ : α ≃ α)
    (h_eq_pt : ∀ x, l (σ (τ x)) = l x) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (l ∘ σ ∘ τ)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  le_of_eq (expectedLength_perm_chain2_invariant P l σ τ h_eq_pt)

/-! ### Section C — chain sub-predicate 化 -/

/-- **chain sub-predicate (Kraft preserving)**: 任意 permutation `σ` で Kraft 和が
`≤ 1` を維持する形の primitive predicate. `SwapStepLeChainHypothesis` の Kraft 部分を
分離した sub-predicate. -/
@[entry_point]
abbrev PermChainKraftPreserving : Prop :=
  ∀ {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β]
    (ll : β → ℕ) (σ : β ≃ β),
    (∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1) →
    (∑ x : β, ((2 : ℝ)) ^ (-((ll ∘ σ) x : ℤ)) ≤ 1)

/-- **chain sub-predicate (Kraft preserving) の discharge**: `PermChainKraftPreserving` は
任意 permutation の sum invariance (`Equiv.sum_comp`) で完全 discharge できる. -/
@[entry_point]
theorem permChainKraftPreserving_holds :
    PermChainKraftPreserving.{u} := by
  intro β _ _ _ ll σ h_kraft
  have h_eq : (∑ x : β, ((2 : ℝ)) ^ (-((ll ∘ σ) x : ℤ)))
      = ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) := by
    show (∑ x : β, ((2 : ℝ)) ^ (-(ll (σ x) : ℤ))) = _
    exact Equiv.sum_comp σ (fun x => ((2 : ℝ)) ^ (-(ll x : ℤ)))
  rw [h_eq]; exact h_kraft

/-- **chain sub-predicate (expectedLength preserving, pointwise-eq)**: permutation `σ` が
`∀ x, ll (σ x) = ll x` を満たすとき expectedLength を不変に保つ形の primitive predicate. -/
@[entry_point]
abbrev PermChainExpectedLengthPreserving : Prop :=
  ∀ {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (σ : β ≃ β),
    (∀ x, ll (σ x) = ll x) →
    InformationTheory.Shannon.ShannonCode.expectedLength Q (ll ∘ σ)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll

/-- **chain sub-predicate (expectedLength preserving) の discharge**: pointwise-eq の下で
expectedLength は不変なので `≤` は完全 discharge できる. -/
@[entry_point]
theorem permChainExpectedLengthPreserving_holds :
    PermChainExpectedLengthPreserving.{u} := by
  intro β _ _ _ _ _ Q _ ll σ h_eq_pt
  apply le_of_eq
  unfold InformationTheory.Shannon.ShannonCode.expectedLength
  apply Finset.sum_congr rfl
  intro x _
  show Q.real {x} * ((ll (σ x) : ℝ)) = Q.real {x} * ((ll x : ℝ))
  congr 1
  exact_mod_cast h_eq_pt x

/-! ### Section D — sub-predicate 合成による `SwapStepLeChainHypothesis` 再構成 -/

/-- **2 sub-predicate の合成形**: `PermChainKraftPreserving` と
`PermChainExpectedLengthPreserving` を `And` で 1 命題に combine. -/
@[entry_point]
abbrev PermChainCombined : Prop :=
  PermChainKraftPreserving.{u} ∧ PermChainExpectedLengthPreserving.{u}

/-- **合成 predicate の discharge**: 両 sub-predicate がそれぞれ discharge できるので
`And` も成立. -/
@[entry_point]
theorem permChainCombined_holds :
    PermChainCombined.{u} :=
  ⟨permChainKraftPreserving_holds, permChainExpectedLengthPreserving_holds⟩

/-- **`SwapStepLeChainHypothesis` を sub-predicate 経由で discharge**: 2 sub-predicate を
仮定しつつ、`l_chain := ll` (= identity chain) を witness にして discharge. trivial chain
(0-step) でも全条件が pass-through するので、sub-predicate を明示的に経由した再構成形. -/
@[entry_point]
theorem swapStepLeChainHypothesis_via_subpredicates
    (_h_kraft : PermChainKraftPreserving.{u})
    (_h_exp : PermChainExpectedLengthPreserving.{u}) :
    SwapStepLeChainHypothesis.{u} := by
  intro β _ _ _ _ _ Q _ ll hll_pos hll_kraft _pair
  refine ⟨ll, hll_pos, hll_kraft, le_refl _⟩

/-! ### Section E — n-step swap normalization lift -/

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **2-step swap chain の expectedLength 不変 (pointwise eq swaps)**: 2 つの swap が
それぞれ `ll a = ll b` 型の値等しい pair であるとき、合成後も expectedLength は不変. -/
@[entry_point]
theorem expectedLength_swap_chain2_eq
    (P : Measure α) [IsProbabilityMeasure P]
    (ll : α → ℕ) (a b c d : α)
    (h_ab : ll a = ll b) (h_cd : ll c = ll d) :
    InformationTheory.Shannon.ShannonCode.expectedLength P
        (ll ∘ Equiv.swap a b ∘ Equiv.swap c d)
      = InformationTheory.Shannon.ShannonCode.expectedLength P ll := by
  -- pointwise value-preservation for a single value-equal swap
  have h_pt_ab : ∀ y, ll ((Equiv.swap a b) y) = ll y := by
    intro y
    by_cases hya : y = a
    · subst hya; rw [Equiv.swap_apply_left]; exact h_ab.symm
    · by_cases hyb : y = b
      · subst hyb; rw [Equiv.swap_apply_right]; exact h_ab
      · rw [Equiv.swap_apply_of_ne_of_ne hya hyb]
  have h_pt_cd : ∀ y, ll ((Equiv.swap c d) y) = ll y := by
    intro y
    by_cases hyc : y = c
    · subst hyc; rw [Equiv.swap_apply_left]; exact h_cd.symm
    · by_cases hyd : y = d
      · subst hyd; rw [Equiv.swap_apply_right]; exact h_cd
      · rw [Equiv.swap_apply_of_ne_of_ne hyc hyd]
  apply expectedLength_perm_chain2_invariant P ll (Equiv.swap a b) (Equiv.swap c d)
  intro x
  rw [h_pt_ab ((Equiv.swap c d) x), h_pt_cd x]

omit [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **2-step swap chain の Kraft 不変 (任意 pair)**: swap の Kraft 不変性は値に依らないので
任意 pair の 2-step chain で Kraft 和は不変. -/
@[entry_point]
theorem kraft_sum_swap_chain2_eq
    (ll : α → ℕ) (a b c d : α) :
    (∑ x : α, ((2 : ℝ)) ^ (-((ll ∘ Equiv.swap a b ∘ Equiv.swap c d) x : ℤ)))
      = ∑ x : α, ((2 : ℝ)) ^ (-(ll x : ℤ)) :=
  kraft_sum_perm_chain2_eq ll (Equiv.swap a b) (Equiv.swap c d)

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **2-step swap normalization lift**: `ll a = ll b ∧ ll c = ll d` の下で、2 swap を
合成した `ll'` も positivity / Kraft / expectedLength 全条件を満たす. n-step lift の
代表 case (n = 2). -/
@[entry_point]
theorem swap_normalization_chain2_lift
    (P : Measure α) [IsProbabilityMeasure P]
    (ll : α → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b c d : α)
    (h_ab : ll a = ll b) (h_cd : ll c = ll d) :
    let ll' := ll ∘ Equiv.swap a b ∘ Equiv.swap c d
    (∀ x, 0 < ll' x) ∧
    (∑ x : α, ((2 : ℝ)) ^ (-(ll' x : ℤ)) ≤ 1) ∧
    InformationTheory.Shannon.ShannonCode.expectedLength P ll'
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P ll := by
  refine ⟨?_, ?_, ?_⟩
  · intro x; exact hll_pos _
  · rw [kraft_sum_swap_chain2_eq ll a b c d]; exact hll_kraft
  · exact le_of_eq (expectedLength_swap_chain2_eq P ll a b c d h_ab h_cd)

/-! ### Section F — universe-polymorphic discharge corollaries -/

/-- **chain hypothesis discharge corollary (poly)**: `SwapStepLeChainHypothesis` を
sub-predicate discharge 経由で得る universe-polymorphic corollary. wave6 の
`swapStepLeChainHypothesis_holds` の sub-predicate 版 re-derivation. -/
@[entry_point]
theorem swapStepLeChainHypothesis_holds_via_subpredicates :
    SwapStepLeChainHypothesis.{u} :=
  swapStepLeChainHypothesis_via_subpredicates
    permChainKraftPreserving_holds permChainExpectedLengthPreserving_holds

/-! ### Section G — `HuffmanCombinedHypothesis` reduce 形 re-publish -/

/-- **combined hypothesis に chain hypothesis を付加した triple**: 既存の 2 hypothesis
(`SwapNormalizationHypothesis` / `HuffmanMergedIdentificationHypothesis`) に
`SwapStepLeChainHypothesis` を加えた 3-way conjunction. chain hypothesis は常に成立
するので、triple は 2-way `HuffmanCombinedHypothesis` と同値.

independent audit (2026-05-30): 第 2 conjunct `HuffmanMergedIdentificationHypothesis` が機械検証
可能に FALSE (反例独立再現済) のため、本 triple conjunction も **universally false** (chain conjunct
が常成立でも ∧ の片側 false で全体 false)。`HuffmanWalls.huffman_chain_combined_hypothesis_holds`
は transitively false-premised wall (`@audit:defect(false-statement)`)。retract reason は正規 vocab
`false-hypothesis` に確定。consumer wrapper (`huffmanLength_optimal_with_chain_combined` /
`_via_chain_lift`) は hypothesis 形のまま残るが false premise を渡す vacuously-true wrapper。
@audit:defect(false-statement) @audit:retract-candidate(false-hypothesis) @audit:closed-by-successor(huffman-strong-form-completion) -/
@[entry_point]
abbrev HuffmanChainCombinedHypothesis : Prop :=
  SwapNormalizationHypothesis.{u} ∧ HuffmanMergedIdentificationHypothesis.{u}
    ∧ SwapStepLeChainHypothesis.{u}

/-- **triple → 2-way reduce**: chain hypothesis を捨てて `HuffmanCombinedHypothesis` に
reduce. chain は常に成立するので情報損失なし. -/
@[entry_point]
theorem huffmanChainCombined_reduce
    (h : HuffmanChainCombinedHypothesis.{u}) :
    HuffmanCombinedHypothesis.{u} :=
  ⟨h.1, h.2.1⟩

/-- **2-way → triple lift**: `HuffmanCombinedHypothesis` に常成立 chain hypothesis を
付加して triple に lift. -/
@[entry_point]
theorem huffmanChainCombined_lift
    (h : HuffmanCombinedHypothesis.{u}) :
    HuffmanChainCombinedHypothesis.{u} :=
  ⟨h.1, h.2, swapStepLeChainHypothesis_holds⟩

/-- **triple ↔ 2-way 同値**: chain hypothesis は常成立なので triple と 2-way は同値. -/
@[entry_point]
theorem huffmanChainCombined_iff :
    HuffmanChainCombinedHypothesis.{u} ↔ HuffmanCombinedHypothesis.{u} :=
  ⟨huffmanChainCombined_reduce, huffmanChainCombined_lift⟩

/-- **triple hypothesis から主定理を呼ぶ wrapper**: 3-way hypothesis を reduce して
`huffmanLength_optimal_with_combined` を呼ぶ terminal step.

Transitive `sorry` via `huffmanLength_optimal_with_hypotheses` (Phase 2 wall 経由
書換時、本 wrapper は `HuffmanCombinedHypothesis` consumer に reduce してから呼ぶ chain)。
本 wrapper には `@residual` タグを付与しない — closure 責任は
`HuffmanWalls.huffman_merged_identification_hypothesis_holds`
(`@residual(plan:huffman-2hyp-vertical-reduction)`) が保有。 -/
@[entry_point]
theorem huffmanLength_optimal_with_chain_combined
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : HuffmanChainCombinedHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_combined (huffmanChainCombined_reduce h) P hP l hl_pos hl_kraft

/-- **2-way hypothesis から chain-combined 経由で主定理を呼ぶ wrapper**: client が
2-way `HuffmanCombinedHypothesis` を持っているとき chain を補って主定理を呼ぶ form.
`huffmanLength_optimal_with_combined` と等価だが chain 経路を明示.

Transitive `sorry` via `huffmanLength_optimal_with_hypotheses` (chain hypothesis は常成立
`swapStepLeChainHypothesis_holds` で trivial に補完できるため、本 wrapper の core residual は
`HuffmanCombinedHypothesis` consumer の transitive)。本 wrapper には `@residual` タグを付与
しない — closure 責任は `HuffmanWalls.huffman_merged_identification_hypothesis_holds`
(`@residual(plan:huffman-2hyp-vertical-reduction)`) が保有。 -/
@[entry_point]
theorem huffmanLength_optimal_via_chain_lift
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h : HuffmanCombinedHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_chain_combined (huffmanChainCombined_lift h) P hP l hl_pos hl_kraft

/-! ### Section H — chain hypothesis 単独の trivial sanity wrappers -/

/-- **triple hypothesis を成立 chain で 2 引数化**: 2 hypothesis から triple を作って
そのまま reduce する round-trip が identity になることの sanity. client が triple ↔ 2-way
を自由に行き来できることを保証. -/
@[entry_point]
theorem huffmanChainCombined_roundtrip
    (h : HuffmanCombinedHypothesis.{u}) :
    huffmanChainCombined_reduce (huffmanChainCombined_lift h) = h := rfl

end InformationTheory.Shannon.Huffman
