import Mathlib.Logic.Equiv.Basic
import Common2026.Shannon.HuffmanOptimality
import Common2026.Shannon.HuffmanT1APPrimePartial
import Common2026.Shannon.HuffmanT1APPrimeBody
import Common2026.Shannon.HuffmanSwapStepChainBody

/-!
# T1-A'' Huffman swap-normalization body (Wave 10, seed S13)

`SwapNormalizationHypothesis` (`HuffmanOptimality.lean`) は

> 任意 Kraft-feasible `ll` と least-probable sibling `a, b` に対し,
> `l_norm a = l_norm b` ∧ Kraft 維持 ∧ expected length 非増加 な `l_norm` が存在する

という genuine な存在 + 不等式 statement。完全 discharge は moonshot judgement log #3 で
「~550 行 / 4-6 セッション」と判定済の不可能 scope。本 file は **genuine vertical
reduction** として、4 conjunct のうち **2 つ (positivity / Kraft) を generic に discharge** し、
残る 2 つ (equalization `l_norm a = l_norm b` / expected length 非増加) を **strictly more
primitive な predicate `EqualizingPermHypothesis` に縦分解**する。

## Approach

Cover-Thomas の swap argument の本質は「語長を **permutation で並べ替えて** `a, b` を
等長にする」ことにある。語長関数 `ll` を permutation `σ : β ≃ β` で並べ替えた `ll ∘ σ` は:

- **positivity**: `(ll ∘ σ) x = ll (σ x) > 0` — `ll` の positivity から自動 (`hll_pos`)。
- **Kraft**: `∑ 2^{-(ll∘σ) x} = ∑ 2^{-ll x}` — permutation 不変 (`kraft_sum_perm_eq`, wave6)。

ので 4 conjunct のうち positivity / Kraft は **permutation という構造から無料で出る**。
残る genuine な核は:

1. **equalization** `(ll ∘ σ) a = (ll ∘ σ) b` — σ が `a, b` の語長を揃えること,
2. **expected length 非増加** `expectedLength Q (ll ∘ σ) ≤ expectedLength Q ll` —
   σ が least-probable 順序を尊重すること (`swap_step_le` の核),

の 2 点だけ。これを `EqualizingPermHypothesis` (= 「上記 σ が存在する」) として切り出し,
`EqualizingPermHypothesis → SwapNormalizationHypothesis` を **完全証明** (positivity / Kraft
を generic discharge して縦に縮約) する。

これは no-op でも defeq でもない: `EqualizingPermHypothesis` は元 hypothesis の 4 conjunct
存在を **2 conjunct (それも permutation 形に固定)** に縮約しており, σ の non-trivial な
構成 (語長並べ替え + 順序尊重) が genuine な残余として残る。

最後に `huffmanLength_optimal_with_hypotheses` を `EqualizingPermHypothesis` 経由で再公開
(`huffmanLength_optimal_via_equalizing_perm`)。identification hypothesis は本 seed scope-out
のため据え置き。
-/

namespace InformationTheory.Shannon.Huffman

open MeasureTheory
open scoped BigOperators ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

universe u

/-! ### Section A — generic discharge: permutation で positivity / Kraft は無料 -/

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **permutation 後 positivity の generic discharge**: `ll` が positive なら任意
permutation `σ` で `ll ∘ σ` も positive. -/
theorem perm_length_pos
    (ll : α → ℕ) (hll_pos : ∀ x, 0 < ll x) (σ : α ≃ α) :
    ∀ x, 0 < (ll ∘ σ) x :=
  fun x => hll_pos (σ x)

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- **permutation 後 Kraft の generic discharge**: Kraft 和は permutation 不変
(`kraft_sum_perm_eq`) なので `ll ∘ σ` も `≤ 1`. -/
theorem perm_length_kraft
    (ll : α → ℕ)
    (hll_kraft : ∑ x : α, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1) (σ : α ≃ α) :
    (∑ x : α, ((2 : ℝ)) ^ (-((ll ∘ σ) x : ℤ))) ≤ 1 := by
  rw [kraft_sum_perm_eq ll σ]; exact hll_kraft

/-! ### Section B — strictly-more-primitive predicate -/

/-- **縮約 predicate `EqualizingPermHypothesis`**: 任意 Kraft-feasible `ll` と
least-probable sibling `a, b` に対し, 語長を並べ替える permutation `σ : β ≃ β` で
`a, b` を等長にし (`(ll ∘ σ) a = (ll ∘ σ) b`), かつ expected length を増やさない
ものが存在する。

`SwapNormalizationHypothesis` の 4 conjunct (positivity / Kraft / equalization /
expected length 非増加) のうち, **positivity と Kraft は permutation 構造から無料**
なので, これらを落とした 2 conjunct (それも permutation 形に固定) のみを要求する。

**⚠ HONESTY ALERT — この述語は FALSE であり discharge 不能 (dead end)。**
permutation `σ` は語長 multiset `{ll x}` を保存する。したがって `(ll∘σ) a = (ll∘σ) b`
を達成するには `ll` の値の中に同じ長さが少なくとも 2 つ必要。しかし feasible (positive,
Kraft ≤ 1) な `ll` は全語長が相異なってよい。
**反例** (機械検証済): `β = Fin 3`, `ll = ![1,2,3]` (positive, Kraft = 7/8 ≤ 1),
`Q{0}=Q{1}=1/10, Q{2}=8/10` (`a=0, b=1` が least-probable, `_h_min`/`_h_card` 充足)。
語長 multiset `{1,2,3}` は相異なるので, どの `σ` でも位置 0,1 を等長化できない。
ゆえに `EqualizingPermHypothesis` は **偽**。これを `_holds` として証明することは
不可能であり, 試みれば honesty defect になる。

正しい swap normalization は **permutation ではなく語長 multiset を変える** 操作を要する
(上の反例では `l_norm = ![2,2,2]` が equalize かつ `E=2.0 ≤ 2.7=E[ll]` で `Hyp1` 自体は
真; しかし `![2,2,2]` は `![1,2,3]` の permutation ではない)。よって本縮約鎖
(`Swap ← EqualizingPerm ← EqualizingSwapTarget`) は `Hyp1` discharge の道としては
**閉じている**。`Hyp1` の genuine discharge は本 file 冒頭が言う ~550 行 moonshot に戻る。

以下の `swapNormalizationHypothesis_of_equalizingPerm` 等は「(偽の述語) → 結論」という
vacuously-true な含意であり (循環でも `:True` でもない genuine な定理), 偽前提を外す道は
ない点に注意。

`@audit:defect(false-hypothesis)` -/
abbrev EqualizingPermHypothesis : Prop :=
  ∀ {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (_hll_pos : ∀ x, 0 < ll x)
    (_hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (_hab : a ≠ b)
    (_h_min : ∀ c, Q.real {a} ≤ Q.real {c} ∨ Q.real {b} ≤ Q.real {c})
    (_h_card : 3 ≤ Fintype.card β),
    ∃ σ : β ≃ β,
      (ll ∘ σ) a = (ll ∘ σ) b ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q (ll ∘ σ)
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll

/-! ### Section C — 縦分解: `EqualizingPermHypothesis → SwapNormalizationHypothesis` -/

/-- **vertical reduction (本 seed の主結果)**: `EqualizingPermHypothesis` が成立すれば
`SwapNormalizationHypothesis` も成立する。permutation `σ` を hypothesis から取り出し,
`l_norm := ll ∘ σ` を witness にすると positivity / Kraft は generic discharge
(`perm_length_pos` / `perm_length_kraft`), equalization と expected length は σ の性質
からそのまま得られる。

注: 前提 `h_eq : EqualizingPermHypothesis` は **false predicate** (`@audit:defect(false-hypothesis)`)
であるが、本含意は vacuously-true な genuine 定理であり構造的に閉じる (= 偽前提 → 結論 の
正しい含意、`:= h` 循環でも `:True` でもない)。`Hyp1` の genuine discharge は
`HuffmanStrongForm.lean:144` `swap_normalization_proof` が独立に閉じている。

`@audit:retract-candidate(false-hypothesis) @audit:closed-by-successor(huffman-2hyp-vertical-reduction)` -/
theorem swapNormalizationHypothesis_of_equalizingPerm
    (h_eq : EqualizingPermHypothesis.{u}) :
    SwapNormalizationHypothesis.{u} := by
  intro β _ _ _ _ _ _ Q _ ll hll_pos hll_kraft a b hab h_a_min _h_b_min h_card
  -- strong precondition `h_a_min` (a = global-min) supplies the disjunctive `_h_min`
  -- required by the (FALSE-chain) EqualizingPermHypothesis predicate.
  have h_min : ∀ c, Q.real {a} ≤ Q.real {c} ∨ Q.real {b} ≤ Q.real {c} :=
    fun c => Or.inl (h_a_min c)
  obtain ⟨σ, hσ_eq, hσ_expL⟩ :=
    h_eq Q ll hll_pos hll_kraft a b hab h_min h_card
  refine ⟨ll ∘ σ, ?_, ?_, hσ_eq, hσ_expL⟩
  · exact perm_length_pos ll hll_pos σ
  · exact perm_length_kraft ll hll_kraft σ

/-! ### Section D — `EqualizingPermHypothesis` の非空性 / 更なる縦分解

縮約 predicate が vacuous でない (= genuine に inhabit 可能) ことを示す constructive
補題群。`ll a = ll b` の trivial case では `σ = Equiv.refl`, 一般 case では「等長化
swap target が存在する」strictly-more-primitive な `EqualizingSwapTargetHypothesis` から
`swap_step_le` 経由で σ を構成する。後者は expected length 非増加の核 (`swap_step_le`)
を **完全 discharge** し, 残余を「swap target の存在」のみに縮約する。 -/

omit [Nonempty α] in
/-- **trivial case の equalizing perm witness**: `ll a = ll b` が既成立なら `σ = Equiv.refl`
で `(ll ∘ refl) a = (ll ∘ refl) b` かつ expected length 不変。`EqualizingPermHypothesis`
の結論を `ll a = ll b` のもとで pointwise に discharge する (非空性 anchor)。 -/
theorem equalizingPerm_witness_when_eq
    {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (a b : β) (h_eq : ll a = ll b) :
    ∃ σ : β ≃ β,
      (ll ∘ σ) a = (ll ∘ σ) b ∧
      InformationTheory.Shannon.ShannonCode.expectedLength Q (ll ∘ σ)
        ≤ InformationTheory.Shannon.ShannonCode.expectedLength Q ll := by
  refine ⟨Equiv.refl β, ?_, ?_⟩
  · show ll ((Equiv.refl β) a) = ll ((Equiv.refl β) b); simpa using h_eq
  · have : (ll ∘ (Equiv.refl β)) = ll := by funext x; rfl
    rw [this]

/-- **predicate `EqualizingSwapTargetHypothesis`**: 等長化を
**1 swap** で達成できる場合の swap target の存在。任意 Kraft-feasible `ll` と
least-probable sibling `a, b` に対し, ある symbol `m` で
`ll a = ll m` (swap `b ↔ m` 後に `b` が `a` と等長になる),
`ll b ≤ ll m` ∧ `Q{b} ≤ Q{m}` (swap_step_le の order 条件),
`m ≠ a` (swap が `a` の語長を動かさない)
を満たすものが存在する。

**⚠ HONESTY ALERT — この述語も FALSE であり discharge 不能 (dead end)。**
disjunction の語長部分 `ll a = ll b ∨ ∃ m ≠ a, ll a = ll m ∧ ll b ≤ ll m` だけで既に
破綻する: 上の `EqualizingPermHypothesis` と同じ反例 `ll = ![1,2,3]`, `a=0, b=1` で,
左枝 `ll 0 = ll 1` は `1 = 2` で偽; 右枝は `ll 0 = ll m` (= `ll m = 1`) かつ `m ≠ 0` を
要求するが長さ 1 の symbol は `0` のみで `m ≠ 0` と両立しない (機械検証済
`eqSwapTarget_length_part_false`)。設計が非対称 (`b ↔ m` swap で `a` を不動に固定し
`ll a = ll m` 厳密等長を強いる) なため, `ll a < ll b` のとき必ず破綻する。
`EqualizingPermHypothesis` を含意する (`equalizingPerm_of_swapTarget`) が, 含意元が偽
なので discharge には使えない。`Hyp1` を割る道としては閉じている。

`@audit:defect(false-hypothesis)` -/
abbrev EqualizingSwapTargetHypothesis : Prop :=
  ∀ {β : Type u} [Fintype β] [DecidableEq β] [LinearOrder β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (Q : Measure β) [IsProbabilityMeasure Q]
    (ll : β → ℕ) (_hll_pos : ∀ x, 0 < ll x)
    (_hll_kraft : ∑ x : β, ((2 : ℝ)) ^ (-(ll x : ℤ)) ≤ 1)
    (a b : β) (_hab : a ≠ b)
    (_h_min : ∀ c, Q.real {a} ≤ Q.real {c} ∨ Q.real {b} ≤ Q.real {c})
    (_h_card : 3 ≤ Fintype.card β),
    ll a = ll b ∨
    ∃ m : β, m ≠ a ∧ ll a = ll m ∧ ll b ≤ ll m ∧ Q.real {b} ≤ Q.real {m}

/-- **`EqualizingSwapTargetHypothesis → EqualizingPermHypothesis` (更なる縦分解)**:
swap target `m` から `σ := Equiv.swap b m` を構成する。`swap_step_le` (= `swap_step_le`
の `(b, m)` 適用) が expected length 非増加 + 全 safety を保証, `m ≠ a` から
`(ll ∘ σ) a = ll a = ll m = (ll ∘ σ) b` の等長化が従う。expected length 非増加の核を
完全 discharge し, 残余を swap target の存在のみに縮約する。

注: 含意元 `h_tgt : EqualizingSwapTargetHypothesis` は **false predicate**
(`@audit:defect(false-hypothesis)`) であるが、本含意は vacuously-true な genuine 定理であり
構造的に閉じる。

`@audit:retract-candidate(false-hypothesis) @audit:closed-by-successor(huffman-2hyp-vertical-reduction)` -/
theorem equalizingPerm_of_swapTarget
    (h_tgt : EqualizingSwapTargetHypothesis.{u}) :
    EqualizingPermHypothesis.{u} := by
  intro β _ _ _ _ _ _ Q _ ll hll_pos hll_kraft a b hab h_min h_card
  rcases h_tgt Q ll hll_pos hll_kraft a b hab h_min h_card with h_eq | ⟨m, hma, h_am, h_blem, h_Pblem⟩
  · -- 既に等長: σ = refl
    exact equalizingPerm_witness_when_eq Q ll a b h_eq
  · -- 1 swap `b ↔ m` で等長化
    classical
    -- swap_step_le を pair `(b, m)` に適用
    have h_step := swap_step_le Q ll hll_pos hll_kraft b m h_blem h_Pblem
    -- h_step : (∀ x, 0 < (ll ∘ swap b m) x) ∧ ... ∧ expectedLength ... ∧
    --          (ll ∘ swap b m) b = ll m ∧ (ll ∘ swap b m) m = ll b
    obtain ⟨_, _, h_expL, h_swap_b, _h_swap_m⟩ := h_step
    refine ⟨Equiv.swap b m, ?_, h_expL⟩
    -- 等長化: (ll ∘ swap b m) a = ll a (a ≠ b, a ≠ m) ; (ll ∘ swap b m) b = ll m = ll a
    have ha_ne_b : a ≠ b := hab
    have ha_ne_m : a ≠ m := fun h => hma h.symm
    have h_lhs : (ll ∘ Equiv.swap b m) a = ll a := by
      show ll ((Equiv.swap b m) a) = ll a
      rw [Equiv.swap_apply_of_ne_of_ne ha_ne_b ha_ne_m]
    have h_rhs : (ll ∘ Equiv.swap b m) b = ll m := by
      show ll ((Equiv.swap b m) b) = ll m
      rw [Equiv.swap_apply_left]
    rw [h_lhs, h_rhs, h_am]

/-- **swap target 経由 vertical reduction (alias)**: `EqualizingSwapTargetHypothesis` から
直接 `SwapNormalizationHypothesis` を得る合成 form。

注: 含意元 `h_tgt : EqualizingSwapTargetHypothesis` は **false predicate**
(`@audit:defect(false-hypothesis)`) — 上 2 補題と同様 vacuously-true な含意。

`@audit:retract-candidate(false-hypothesis) @audit:closed-by-successor(huffman-2hyp-vertical-reduction)` -/
theorem swapNormalizationHypothesis_of_swapTarget
    (h_tgt : EqualizingSwapTargetHypothesis.{u}) :
    SwapNormalizationHypothesis.{u} :=
  swapNormalizationHypothesis_of_equalizingPerm
    (equalizingPerm_of_swapTarget h_tgt)

/-! ### Section E — 主定理の `EqualizingPermHypothesis` 経由再公開 -/

/-- **`huffmanLength_optimal` の `EqualizingPermHypothesis` 経由 weak form**: swap
normalization hypothesis を strictly-more-primitive な `EqualizingPermHypothesis` に
置き換えて再公開。identification hypothesis は本 seed scope-out のため据え置き。

Transitive `sorry` via `huffmanLength_optimal_with_hypotheses` (本 plan
`huffman-sorry-migration-plan.md` 判断ログ #2 L-MIG-4 発動により signature 不変、
load-bearing hypothesis 引数を残す top-most weak-form API)。本 wrapper には `@residual`
タグを付与しない — closure 責任は `HuffmanWalls.huffman_merged_identification_hypothesis_holds`
が保有 (`@residual(plan:huffman-2hyp-vertical-reduction)`)。`h_eqperm` は
**false predicate** (`@audit:defect(false-hypothesis)`)、本含意自体は vacuously-true。

`@audit:retract-candidate(false-hypothesis) @audit:closed-by-successor(huffman-2hyp-vertical-reduction)` -/
theorem huffmanLength_optimal_via_equalizing_perm
    {α : Type u} [Fintype α] [DecidableEq α] [LinearOrder α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (h_eqperm : EqualizingPermHypothesis.{u})
    (h_ident : HuffmanMergedIdentificationHypothesis.{u})
    (P : Measure α) [IsProbabilityMeasure P] (hP : ∀ a, 0 < P.real {a})
    (l : α → ℕ) (hl_pos : ∀ a, 0 < l a)
    (hl_kraft : ∑ a : α, ((2 : ℝ)) ^ (-(l a : ℤ)) ≤ 1) :
    InformationTheory.Shannon.ShannonCode.expectedLength P (huffmanLength P)
      ≤ InformationTheory.Shannon.ShannonCode.expectedLength P l :=
  huffmanLength_optimal_with_hypotheses
    (swapNormalizationHypothesis_of_equalizingPerm h_eqperm) h_ident
    P hP l hl_pos hl_kraft

end InformationTheory.Shannon.Huffman
