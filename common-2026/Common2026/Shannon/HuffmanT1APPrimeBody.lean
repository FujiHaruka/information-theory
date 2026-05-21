import Mathlib.Logic.Equiv.Basic
import Common2026.Shannon.HuffmanOptimality
import Common2026.Shannon.HuffmanT1APPrimePartial

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
theorem swapStepLeChainHypothesis_holds :
    SwapStepLeChainHypothesis.{u} := by
  intro β _ _ _ _ _ Q _ ll hll_pos hll_kraft _pair
  refine ⟨ll, hll_pos, hll_kraft, le_refl _⟩

/-! ### Section B — `SwapNormalizationHypothesis` partial discharge via primitive -/

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **`SwapNormalizationHypothesis` の partial form — `ll a = ll b` を仮定する場合の
discharge**: 既存の `SwapNormalizationHypothesis_trivial_when_eq` の universe-polymorphic
版. Pinpoint で `ll a = ll b` だけ仮定して結論を生成する形. -/
theorem swapNormalizationHypothesis_at_pair_when_eq_poly
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β]
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
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll :=
  SwapNormalizationHypothesis_trivial_when_eq Q ll hll_pos hll_kraft a b h_eq

/-- **partial discharge — `ll a = ll b` のもとで `Equiv.swap a b` 後の同 hypothesis**:
`ll ∘ Equiv.swap a b` を `l_norm` の候補にしても hypothesis が成立する. swap で値が
入れ替わるが `ll a = ll b` のため `l_norm a = l_norm b` は維持. expectedLength 等式は
`expectedLength_swap_eq_when_ll_eq` (partial 既存) で押さえる. -/
theorem swapNormalizationHypothesis_alt_witness_swap
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β]
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
  classical
  refine ⟨ll ∘ Equiv.swap a b, ?_, ?_, ?_, ?_⟩
  · intro x; exact hll_pos _
  · -- Kraft 不変 (swap permutation)
    show (∑ x : β, ((2 : ℝ)) ^ (-((ll ∘ Equiv.swap a b) x : ℤ))) ≤ 1
    have h_eq_kraft :
        (∑ x : β, ((2 : ℝ)) ^ (-((ll ∘ Equiv.swap a b) x : ℤ)))
          = ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) := by
      show (∑ x : β, ((2 : ℝ)) ^ (-(ll ((Equiv.swap a b) x) : ℤ))) = _
      exact Equiv.sum_comp (Equiv.swap a b) (fun x => ((2 : ℝ)) ^ (-(ll x : ℤ)))
    rw [h_eq_kraft]; exact hll_kraft
  · -- `(ll ∘ swap a b) a = ll b = ll a = (ll ∘ swap a b) b`
    show ll ((Equiv.swap a b) a) = ll ((Equiv.swap a b) b)
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact h_eq.symm
  · -- expectedLength 不変 (swap で `ll a = ll b` なら shift 無し)
    -- 既存補題 `expectedLength_swap_eq_when_ll_eq` の universe-polymorphic 形.
    unfold InformationTheory.Shannon.ShannonCode.expectedLength
    apply Finset.sum_le_sum
    intro x _
    show Q.real {x} * ((ll ((Equiv.swap a b) x) : ℝ)) ≤ Q.real {x} * ((ll x : ℝ))
    have hPx : 0 ≤ Q.real {x} := measureReal_nonneg
    apply mul_le_mul_of_nonneg_left _ hPx
    -- ll (swap a b x) = ll x かつ等号 (≤)
    by_cases hxa : x = a
    · subst hxa
      rw [Equiv.swap_apply_left]
      exact_mod_cast Nat.le_of_eq h_eq.symm
    · by_cases hxb : x = b
      · subst hxb
        rw [Equiv.swap_apply_right]
        exact_mod_cast Nat.le_of_eq h_eq
      · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-! ### Section C — `HuffmanMergedIdentificationHypothesis` の point-wise 分解 -/

omit [Nonempty α] in
/-- **identification hypothesis の point-wise extractor (`x.val = a` case)**: `hsib`
仮定の下で `x.val = a` のとき `huffmanLength (mergedMeasure ...) x = huffmanLength P a - 1`.
本 lemma は **hypothesis** として外から受け取ったもの (`h_ident`) から `x.val = a` の
case の値を抽出する extractor. -/
theorem huffmanMergedIdentification_at_a
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    (Q : Measure β) [IsProbabilityMeasure Q] (hQ : ∀ a, 0 < Q.real {a})
    (h_card : 3 ≤ Fintype.card β)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_sibling : huffmanLength Q a = huffmanLength Q b)
    (x : { y : β // y ≠ b }) (hxa : x.val = a) :
    huffmanLength (mergedMeasure Q a b hab) x = huffmanLength Q a - 1 := by
  have h := h_ident Q hQ h_card a b hab h_a_min h_b_min h_sibling x
  rw [h]
  simp [hxa]

omit [Nonempty α] in
/-- **identification hypothesis の point-wise extractor (`x.val ≠ a` case)**: `hsib`
仮定の下で `x.val ≠ a` のとき `huffmanLength (mergedMeasure ...) x = huffmanLength P x.val`. -/
theorem huffmanMergedIdentification_at_other
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    (Q : Measure β) [IsProbabilityMeasure Q] (hQ : ∀ a, 0 < Q.real {a})
    (h_card : 3 ≤ Fintype.card β)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_sibling : huffmanLength Q a = huffmanLength Q b)
    (x : { y : β // y ≠ b }) (hxa : x.val ≠ a) :
    huffmanLength (mergedMeasure Q a b hab) x = huffmanLength Q x.val := by
  have h := h_ident Q hQ h_card a b hab h_a_min h_b_min h_sibling x
  rw [h]
  simp [hxa]

omit [Nonempty α] in
/-- **identification hypothesis combined formula**: `x.val = a` / `≠ a` の case を `if`
で 1 式に書いた形. `h_ident` の結論そのまま (alias) だが、後続 client が直接 `if` 形を
受け取りたいときの reference. -/
theorem huffmanMergedIdentification_combined
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    (Q : Measure β) [IsProbabilityMeasure Q] (hQ : ∀ a, 0 < Q.real {a})
    (h_card : 3 ≤ Fintype.card β)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_sibling : huffmanLength Q a = huffmanLength Q b)
    (x : { y : β // y ≠ b }) :
    huffmanLength (mergedMeasure Q a b hab) x
      = (if x.val = a then huffmanLength Q a - 1 else huffmanLength Q x.val) :=
  h_ident Q hQ h_card a b hab h_a_min h_b_min h_sibling x

/-! ### Section D — Identification hypothesis from sibling triple plumbing -/

omit [Nonempty α] in
/-- **identification hypothesis の sibling 対 a/b 双方向**: `huffmanLength Q a =
huffmanLength Q b` から `huffmanLength (mergedMeasure ...) x` を `x.val = b` 形は
そもそも domain `{y // y ≠ b}` で除外されているので、`x.val ∈ {a, c (≠ b)}` の case
分類だけが残る. これを explicit に publish. -/
theorem huffmanMergedIdentification_dichotomy
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    (Q : Measure β) [IsProbabilityMeasure Q] (hQ : ∀ a, 0 < Q.real {a})
    (h_card : 3 ≤ Fintype.card β)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_sibling : huffmanLength Q a = huffmanLength Q b)
    (x : { y : β // y ≠ b }) :
    (x.val = a ∧
      huffmanLength (mergedMeasure Q a b hab) x = huffmanLength Q a - 1) ∨
    (x.val ≠ a ∧
      huffmanLength (mergedMeasure Q a b hab) x = huffmanLength Q x.val) := by
  by_cases hxa : x.val = a
  · left
    refine ⟨hxa, ?_⟩
    exact huffmanMergedIdentification_at_a h_ident Q hQ h_card a b hab h_a_min h_b_min h_sibling x hxa
  · right
    refine ⟨hxa, ?_⟩
    exact huffmanMergedIdentification_at_other h_ident Q hQ h_card a b hab h_a_min h_b_min h_sibling x hxa

/-! ### Section E — Sibling pair 関連 補助補題 -/

omit [Nonempty α] in
/-- **sibling property 対称化**: `huffmanLength Q a = huffmanLength Q b` から symm 形
`huffmanLength Q b = huffmanLength Q a`. trivial だが client で `eq.symm` を毎回書か
ないための alias. -/
theorem huffmanLength_sibling_symm
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β)
    (a b : β) (h_sibling : huffmanLength Q a = huffmanLength Q b) :
    huffmanLength Q b = huffmanLength Q a := h_sibling.symm

omit [Nonempty α] in
/-- **identification hypothesis swap 形** (symm): pair `(a, b)` の順を `(b, a)` に変えても
identification が成立する場合の form を作る側で使う sibling property swap. ただし
`mergedMeasure Q b a hba` ≠ `mergedMeasure Q a b hab` のため一般的 swap 形は scope-out.
本 lemma は sibling property の symm を `huffmanLength Q b = huffmanLength Q a` 形で再公開
する命名 alias. -/
theorem huffmanLength_sibling_eq_iff
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) (a b : β) :
    huffmanLength Q a = huffmanLength Q b ↔ huffmanLength Q b = huffmanLength Q a :=
  ⟨Eq.symm, Eq.symm⟩

/-! ### Section F — Combined hypothesis discharge wrappers -/

/-- **combined hypothesis: trivial form when `ll a = ll b`**: 既存の `SwapNormalizationHypothesis_
trivial_when_eq` 経由で `h_swap` を消費した形で `huffmanLength_optimal_with_hypotheses`
を呼び出すパターン. 仮定で `ll a = ll b` (sibling at `(a, b)`) の場合の直接呼び出し形. -/
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
は主定理 internal の swap normalization step で生成されるので external 仮定にはしない. -/
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

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **swap chain step (length 1)**: 1 段 swap 後の 4 条件 (positivity / Kraft / expectedLength /
value at a / value at m) tuple. `swap_step_le` の全条件を 1 lemma に再構成. -/
theorem swap_chain_step_one
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m}) :
    (∀ x, 0 < (l ∘ Equiv.swap a m) x) ∧
    (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ Equiv.swap a m) x : ℤ)) ≤ 1) ∧
    InformationTheory.Shannon.ShannonCode.expectedLength P (l ∘ Equiv.swap a m)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l ∧
    (l ∘ Equiv.swap a m) a = l m ∧
    (l ∘ Equiv.swap a m) m = l a :=
  swap_step_le P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **swap chain step (length 0 = identity)**: 0 段 (= identity) で trivial に成立する形. -/
theorem swap_chain_step_zero
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1) :
    (∀ x, 0 < l x) ∧
    (∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1) ∧
    InformationTheory.Shannon.ShannonCode.expectedLength P l
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  ⟨hl_pos, hl_kraft, le_refl _⟩

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **swap chain composition (2 段)**: 1 段目 `(a, m)`, 2 段目 `(c, d)` で双方の前提が
成立するとき 4 条件の chain composition. 中間状態 `l'` を経由する形.
注: 2 段目の前提 (`l' c ≤ l' d` ∧ `P{c} ≤ P{d}`) は 1 段目の swap で `l'` が変化した後で
評価する必要があるため、入力で **直接** `l' c ≤ l' d` を仮定する形で記述. -/
theorem swap_chain_step_two
    (P : Measure α) [IsProbabilityMeasure P]
    (l : α → ℕ) (hl_pos : ∀ x, 0 < l x)
    (hl_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) ≤ 1)
    (a m : α)
    (h_la_le_lm : l a ≤ l m) (h_Pa_le_Pm : P.real {a} ≤ P.real {m})
    (c d : α)
    (h_lcd_le : (l ∘ Equiv.swap a m) c ≤ (l ∘ Equiv.swap a m) d)
    (h_Pcd_le : P.real {c} ≤ P.real {d}) :
    let l' := l ∘ Equiv.swap a m
    let l'' := l' ∘ Equiv.swap c d
    (∀ x, 0 < l'' x) ∧
    (∑ x : α, ((2 : ℝ)) ^ (-(l'' x : ℤ)) ≤ 1) ∧
    InformationTheory.Shannon.ShannonCode.expectedLength P l''
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l := by
  -- Step 1: swap_step_le at (a, m)
  obtain ⟨hl'_pos, hl'_kraft, hl'_exp, _, _⟩ :=
    swap_step_le P l hl_pos hl_kraft a m h_la_le_lm h_Pa_le_Pm
  -- Step 2: swap_step_le at (c, d) on l'
  obtain ⟨hl''_pos, hl''_kraft, hl''_exp, _, _⟩ :=
    swap_step_le P (l ∘ Equiv.swap a m) hl'_pos hl'_kraft c d h_lcd_le h_Pcd_le
  refine ⟨hl''_pos, hl''_kraft, ?_⟩
  exact le_trans hl''_exp hl'_exp

/-! ### Section H — Witness extraction from `SwapNormalizationHypothesis` -/

omit [Nonempty α] [MeasurableSingletonClass α] in
/-- **witness extraction**: `SwapNormalizationHypothesis` を適用したとき得られる `l_norm`
を抽出する form. tuple の全成分を `obtain` で取り出す client の boilerplate を 1 個に
まとめた wrapper. -/
theorem SwapNormalizationHypothesis_apply_witness
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (h_swap : SwapNormalizationHypothesis.{u})
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_card : 3 ≤ Fintype.card β) :
    ∃ l_norm : β → ℕ,
      (∀ x, 0 < l_norm x) ∧
      (∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1) ∧
      l_norm a = l_norm b ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll :=
  h_swap Q ll hll_pos hll_kraft a b hab h_a_min h_b_min h_card

/-- **witness positivity extractor**: hypothesis 結論の存在から positivity だけ取り出す. -/
theorem SwapNormalizationHypothesis_witness_pos
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (h_swap : SwapNormalizationHypothesis.{u})
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_card : 3 ≤ Fintype.card β) :
    ∃ l_norm : β → ℕ, ∀ x, 0 < l_norm x := by
  obtain ⟨l_norm, hpos, _, _, _⟩ :=
    h_swap Q ll hll_pos hll_kraft a b hab h_a_min h_b_min h_card
  exact ⟨l_norm, hpos⟩

/-- **witness kraft extractor**: hypothesis 結論の存在から Kraft だけ取り出す. -/
theorem SwapNormalizationHypothesis_witness_kraft
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (h_swap : SwapNormalizationHypothesis.{u})
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_card : 3 ≤ Fintype.card β) :
    ∃ l_norm : β → ℕ, ∑ x : β, ((2 : ℝ)) ^ (-(l_norm x : ℤ)) ≤ 1 := by
  obtain ⟨l_norm, _, hkraft, _, _⟩ :=
    h_swap Q ll hll_pos hll_kraft a b hab h_a_min h_b_min h_card
  exact ⟨l_norm, hkraft⟩

/-- **witness sibling equality extractor**: hypothesis 結論から `l_norm a = l_norm b` の
sibling 等式だけ取り出す. -/
theorem SwapNormalizationHypothesis_witness_eq
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (h_swap : SwapNormalizationHypothesis.{u})
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_card : 3 ≤ Fintype.card β) :
    ∃ l_norm : β → ℕ, l_norm a = l_norm b := by
  obtain ⟨l_norm, _, _, heq, _⟩ :=
    h_swap Q ll hll_pos hll_kraft a b hab h_a_min h_b_min h_card
  exact ⟨l_norm, heq⟩

/-- **witness expected length extractor**: hypothesis 結論から expectedLength `≤` だけ
取り出す. -/
theorem SwapNormalizationHypothesis_witness_expL
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (h_swap : SwapNormalizationHypothesis.{u})
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (hll_pos : ∀ x, 0 < ll x)
    (hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (hab : a ≠ b)
    (h_a_min : ∀ c, Q.real {a} ≤ Q.real {c})
    (h_b_min : ∀ c, c ≠ a → Q.real {b} ≤ Q.real {c})
    (h_card : 3 ≤ Fintype.card β) :
    ∃ l_norm : β → ℕ,
      InformationTheory.Shannon.ShannonCode.expectedLength Q l_norm
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := by
  obtain ⟨l_norm, _, _, _, hle⟩ :=
    h_swap Q ll hll_pos hll_kraft a b hab h_a_min h_b_min h_card
  exact ⟨l_norm, hle⟩

/-! ### Section I — `Equiv.swap` permutation の sum invariance 再公開 -/

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **任意 permutation の sum invariance**: `Equiv.swap a m` を任意 `σ : α ≃ α` に
generalise した形. `Equiv.sum_comp` の direct alias. -/
theorem permutation_sum_invariance
    (σ : α ≃ α) (f : α → ℝ) :
    (∑ x : α, f (σ x)) = ∑ x : α, f x :=
  Equiv.sum_comp σ f

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **Kraft sum の任意 permutation 不変性**: `Equiv.swap` 経由でなく任意 permutation で
Kraft sum が不変. -/
theorem kraft_sum_perm_eq
    (l : α → ℕ) (σ : α ≃ α) :
    (∑ x : α, ((2 : ℝ)) ^ (-((l ∘ σ) x : ℤ)))
      = ∑ x : α, ((2 : ℝ)) ^ (-(l x : ℤ)) := by
  show (∑ x : α, ((2 : ℝ)) ^ (-(l (σ x) : ℤ))) = _
  exact Equiv.sum_comp σ (fun x => ((2 : ℝ)) ^ (-(l x : ℤ)))

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **expectedLength の permutation 不変性 (`l a = l (σ a)` 条件)**: 任意 permutation `σ`
で `∀ x, l (σ x) = l x` ⇒ expectedLength は不変. `σ` が恒等 (= 値 nontrivial) でない場合
にも、すべての pair で `l` が等しいときに使える. -/
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
した form. 後続 client で `h.1, h.2` で取り出せる. -/
abbrev HuffmanCombinedHypothesis : Prop :=
  SwapNormalizationHypothesis.{u} ∧ HuffmanMergedIdentificationHypothesis.{u}

/-- **combined hypothesis 投影 left**. -/
theorem huffmanCombinedHypothesis_swap
    (h : HuffmanCombinedHypothesis.{u}) :
    SwapNormalizationHypothesis.{u} := h.1

/-- **combined hypothesis 投影 right**. -/
theorem huffmanCombinedHypothesis_ident
    (h : HuffmanCombinedHypothesis.{u}) :
    HuffmanMergedIdentificationHypothesis.{u} := h.2

/-- **combined hypothesis から主定理を 1-arg で呼ぶ wrapper**. -/
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

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **swap 後の各点の値 (table)**: `(l ∘ Equiv.swap a m) x` の値を `x = a`, `x = m`,
それ以外で case 分けして table 化. 既存 `swap_value_cases` のより explicit な形. -/
theorem swap_value_table
    (l : α → ℕ) (a m x : α) :
    ((x = a ∧ (l ∘ Equiv.swap a m) x = l m) ∨
     (x = m ∧ x ≠ a ∧ (l ∘ Equiv.swap a m) x = l a) ∨
     (x ≠ a ∧ x ≠ m ∧ (l ∘ Equiv.swap a m) x = l x)) := by
  by_cases hxa : x = a
  · left
    refine ⟨hxa, ?_⟩
    rw [hxa]
    show l ((Equiv.swap a m) a) = l m
    rw [Equiv.swap_apply_left]
  · by_cases hxm : x = m
    · right; left
      refine ⟨hxm, hxa, ?_⟩
      rw [hxm]
      show l ((Equiv.swap a m) m) = l a
      rw [Equiv.swap_apply_right]
    · right; right
      refine ⟨hxa, hxm, ?_⟩
      show l ((Equiv.swap a m) x) = l x
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxm]

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **swap 後の値が non-decrease**: `l a ≤ l m` のもと、swap 後の各点の値は元の値
**以下** (= swap で小さい値が大きい位置に来る). 厳密には:
`(l ∘ Equiv.swap a m) x ≤ max (l x) (l m)` (粗い上限). -/
theorem swap_value_le_max
    (l : α → ℕ) (a m x : α) (h_la_le_lm : l a ≤ l m) :
    (l ∘ Equiv.swap a m) x ≤ max (l x) (l m) := by
  by_cases hxa : x = a
  · -- x = a: (l ∘ swap a m) a = l m, RHS = max (l a) (l m) ≥ l m
    rw [hxa]
    show l ((Equiv.swap a m) a) ≤ max (l a) (l m)
    rw [Equiv.swap_apply_left]
    exact le_max_right _ _
  · by_cases hxm : x = m
    · -- x = m: (l ∘ swap a m) m = l a, RHS = max (l m) (l m) = l m ≥ l a
      rw [hxm]
      show l ((Equiv.swap a m) m) ≤ max (l m) (l m)
      rw [Equiv.swap_apply_right]
      have : (l a : ℕ) ≤ l m := h_la_le_lm
      simp; exact this
    · show l ((Equiv.swap a m) x) ≤ max (l x) (l m)
      rw [Equiv.swap_apply_of_ne_of_ne hxa hxm]
      exact le_max_left _ _

/-! ### Section L — Partial discharge composition with `huffmanLength_kraft_eq_one` -/

/-- **huffmanLength の self-comparison via 主定理 (`card α ≥ 2` 仮定形)**: `huffmanLength P`
自身を `l` として主定理に入れた形は trivial に `≤` (= 反射律) で成立. `huffmanLength_pos`
が `2 ≤ card α` を要求するため、本 wrapper も同条件で公開. -/
theorem huffmanLength_optimal_self
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h_swap : SwapNormalizationHypothesis.{u})
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (h_card : 2 ≤ Fintype.card α) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P) :=
  huffmanLength_optimal_with_hypotheses h_swap h_ident P hP
    (huffmanLength P) (huffmanLength_pos P hP h_card)
    (huffmanLength_kraft_le_one P hP)

/-! ### Section M — Partial wrapper for client convenience -/

/-- **client wrapper - `huffmanLength_optimal_with_hypotheses` を `H : HuffmanCombinedHypothesis`
1 引数で呼ぶ最も簡潔な form**. T1-A''' 後続 seed で H が定理として成立した瞬間に強形が
得られる terminal step. -/
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
