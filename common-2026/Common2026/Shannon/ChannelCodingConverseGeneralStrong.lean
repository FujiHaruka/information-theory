import Common2026.Shannon.ChannelCodingConverseGeneralComplete
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Channel coding converse (general input) — strong memoryless variant (D-2'')

[D-2'' ムーンショット plan](../../../docs/shannon/channel-coding-converse-general-d2-double-prime-plan.md)
の Phase B Session 1。`ChannelCodingConverseGeneralComplete.lean` (D-2') が hypothesis-form
で残した 3 仮説 (`h_yother_zero`, `h_split`, `h_markov_xprefix`) を、より強い memoryless 述語
**`IsMemorylessChannelStrong`** から直接導出することを目標とする。

## Scope

* `IsMemorylessChannelStrong` (Option C, structure 形): 2 つの Markov axiom
  - per-letter:  `X^n → X_i → Y_i`
  - outputs cond. indep.: `Y^{≠i} → X^n → Y_i`
* `MeasurableEquiv` plumbing: `Fin n → β ≃ᵐ β × ({j // j ≠ i} → β)`
  (`piEquivPiSubtypeProd` + `funUnique` の合成)
* `h_markov_xprefix_of_strong`: per-letter Markov を `isMarkovChain_map_left` で post-process。
* `h_split_of_strong`: Y-axis chain rule split を `condMutualInfo_chain_rule_Y_2var`
  + `condMutualInfo_map_middle_measurableEquiv` で discharge。
* `h_yother_zero_of_strong` (**Session 2 sorry**): outputs cond. indep. + per-letter から
  conditioning RV を `(Xprefix, Y_i)` に置換する追加変形が必要。
* `channel_coding_converse_general_memoryless_strong` (主定理): 上記 3 つを合成し、
  既存 `channel_coding_converse_general_memoryless` を呼び出す。

`h_yother_zero` のみ未討究 (Markov 構造の置換が複雑) で sorry を残す。残り 2 つは clean
discharge。 -/

namespace InformationTheory.Shannon.ChannelCodingConverseGeneral

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Strong memoryless 述語 -/

section StrongMemoryless

variable {n : ℕ}
variable {α : Type*} [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
variable {β : Type*} [MeasurableSpace β] [Nonempty β] [StandardBorelSpace β]

/-- **Strong memoryless DMC predicate** (Option C, structure 形, 2 Markov axioms).

`IsMemorylessChannel` (D-2') が `(X^{≠i}, Y^{≠i}) → X_i → Y_i` を 1 つの Markov 公理にまとめて
いたのに対し、本述語は 2 つに分解する:

* `per_letter_markov`: 各 `i` で `(X^n) → X_i → Y_i`、すなわち `Y_i` は他の入力 `X^{≠i}` に
  依存しない (per-letter チャネル性)。
* `outputs_cond_indep`: 各 `i` で `Y^{≠i} → X^n → Y_i`、すなわち入力全体を condition すれば
  `Y_i` は他の出力 `Y^{≠i}` と独立 (出力の条件付き独立性)。

これら 2 つから、対応する 3 仮説 (`h_yother_zero`, `h_split`, `h_markov_xprefix`) を
合成して `channel_coding_converse_general_memoryless` を呼び出すのが本 file の目標。 -/
structure IsMemorylessChannelStrong (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) : Prop where
  /-- Per-letter Markov: `Y_i` depends on `X^n` only through `X_i`. -/
  per_letter_markov : ∀ i : Fin n,
    Shannon.IsMarkovChain μ (fun ω j => Xs j ω) (Xs i) (Ys i)
  /-- Outputs are conditionally independent across `i` given the full input `X^n`. -/
  outputs_cond_indep : ∀ i : Fin n,
    Shannon.IsMarkovChain μ
      (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
      (fun ω j => Xs j ω)
      (Ys i)

end StrongMemoryless

/-! ## MeasurableEquiv plumbing -/

section MeasurableEquivPlumbing

variable {n : ℕ}
variable {β : Type*} [MeasurableSpace β]

/-- `Fin n → β ≃ᵐ β × ({j : Fin n // j ≠ i} → β)`: 第 `i` 成分を取り出して残りと積に分解。

戦略: `MeasurableEquiv.piEquivPiSubtypeProd` で `(∀ j, β) ≃ᵐ ({j // j = i} → β)
× ({j // j ≠ i} → β)` を作り、第 1 因子の `{j // j = i} → β` を `MeasurableEquiv.funUnique`
で `β` に潰す (Mathlib `Unique.subtypeEq` インスタンス由来)。-/
noncomputable def measurableEquivExtract (i : Fin n) :
    (Fin n → β) ≃ᵐ β × ({j : Fin n // j ≠ i} → β) :=
  -- (∀ j, β) ≃ᵐ ({j // j = i} → β) × ({j // j ≠ i} → β)
  (MeasurableEquiv.piEquivPiSubtypeProd (π := fun _ : Fin n => β) (fun j => j = i)).trans
    -- collapse {j // j = i} → β to β
    ((MeasurableEquiv.funUnique {j : Fin n // j = i} β).prodCongr (.refl _))

end MeasurableEquivPlumbing

/-! ## Discharge lemmas -/

section Discharge

variable {n : ℕ}
variable {α : Type*} [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
variable {β : Type*} [MeasurableSpace β] [Nonempty β] [StandardBorelSpace β]

/-- **`h_markov_xprefix` discharge from `IsMemorylessChannelStrong`**.

The augmented Markov chain `(X^{<i}, X_i) → X_i → Y_i` is obtained from `per_letter_markov i`
(`(fun ω j => Xs j ω) → Xs i → Ys i`) by left post-processing with
`f := fun (x : Fin n → α) => ((fun j : Fin i.val => x ⟨j.val, j.isLt.trans i.isLt⟩), x i)`,
applying `isMarkovChain_map_left`. -/
lemma h_markov_xprefix_of_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_strong : IsMemorylessChannelStrong μ Xs Ys) :
    ∀ i : Fin n,
      Shannon.IsMarkovChain μ
        (fun ω => (
          (fun (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω),
          Xs i ω))
        (Xs i) (Ys i) := by
  intro i
  -- Post-process the full input X^n: extract (Xprefix, X_i).
  have h_full_meas : Measurable (fun ω j => Xs j ω) := measurable_pi_iff.mpr hXs
  have hf : Measurable
      (fun (x : Fin n → α) =>
        ((fun (j : Fin i.val) => x ⟨j.val, j.isLt.trans i.isLt⟩), x i)) := by
    refine Measurable.prodMk ?_ (measurable_pi_apply _)
    exact measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
  exact Shannon.isMarkovChain_map_left
    μ (fun ω j => Xs j ω) (Xs i) (Ys i)
    h_full_meas (hXs i) (hYs i) hf (h_strong.per_letter_markov i)

/-- **`h_split` discharge from `IsMemorylessChannelStrong`** (independent of memoryless;
purely a `condMutualInfo` reshape + 2-var chain rule).

```
condMI X_i Y^n Xprefix
  = condMI X_i Y_i Xprefix + condMI X_i Y^{≠i} (Xprefix, Y_i)
```

戦略:
1. `condMutualInfo_map_middle_measurableEquiv` で `Y^n` を `(Y_i, Y^{≠i})` に reshape。
2. `condMutualInfo_chain_rule_Y_2var` で `(Y_i, Y^{≠i})` を分解。

`I(Xprefix; X_i) ≠ ∞` の有限性は finite-alphabet 仮定から `mutualInfo_ne_top` で得る。 -/
lemma h_split_of_strong
    [Fintype α] [MeasurableSingletonClass α] [DecidableEq α]
    [Fintype β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i)) :
    ∀ i : Fin n,
      Shannon.condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
          (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        = Shannon.condMutualInfo μ (Xs i) (Ys i)
            (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
          + Shannon.condMutualInfo μ (Xs i)
              (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
              (fun ω => (
                (fun (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω),
                Ys i ω)) := by
  intro i
  -- Set up the prefix RV.
  set Xprefix : Ω → (Fin i.val → α) :=
    fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω with hXprefix_def
  have hXprefix : Measurable Xprefix :=
    measurable_pi_iff.mpr (fun j => hXs ⟨j.val, j.isLt.trans i.isLt⟩)
  have hYall : Measurable (fun ω (j : Fin n) => Ys j ω) :=
    measurable_pi_iff.mpr hYs
  have hYother : Measurable
      (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω) :=
    measurable_pi_iff.mpr (fun j => hYs j.val)
  -- Reshape Y^n via the measurable equiv (Y^n ≃ᵐ Y_i × Y^{≠i}).
  -- Define the equiv's symm so post-composing on (Y_i, Y^{≠i}) gives Y^n.
  let e : (Fin n → β) ≃ᵐ β × ({j : Fin n // j ≠ i} → β) :=
    measurableEquivExtract (β := β) i
  -- LHS of split: rewrite Y^n as e.symm (Y_i, Y^{≠i}).
  have h_pointwise : ∀ ω,
      e.symm (Ys i ω, fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
        = (fun j => Ys j ω) := by
    intro ω
    -- e is piEquivPiSubtypeProd ∘ funUnique on first factor.
    -- e.symm collapses (β × ({j // j ≠ i} → β)) back to (Fin n → β):
    --   if j = i, returns Ys i ω; else returns Ys j ω.
    -- We verify by `funext`.
    funext j
    by_cases hj : j = i
    · -- j = i case
      subst hj
      simp [e, measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.trans, MeasurableEquiv.prodCongr]
    · -- j ≠ i case
      simp [e, measurableEquivExtract,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.funUnique,
        MeasurableEquiv.trans, MeasurableEquiv.prodCongr, hj]
  -- Pair RV: Measurable.
  have hYpair : Measurable
      (fun ω => (Ys i ω, fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω)) :=
    (hYs i).prodMk hYother
  -- Step A: rewrite Y^n via e.symm.
  have hLHS_eq :
      Shannon.condMutualInfo μ (Xs i) (fun ω j => Ys j ω) Xprefix
        = Shannon.condMutualInfo μ (Xs i)
            (fun ω => e.symm
              (Ys i ω, fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω))
            Xprefix := by
    congr 1
    funext ω
    exact (h_pointwise ω).symm
  rw [hLHS_eq]
  -- Step B: peel off e.symm via condMutualInfo_map_middle_measurableEquiv.
  -- Note: signature is condMutualInfo_map_middle_measurableEquiv μ Xs Yo Zc hXs hYo hZc e.
  rw [Shannon.condMutualInfo_map_middle_measurableEquiv μ
      (Xs i)
      (fun ω => (Ys i ω, fun (j : {j : Fin n // j ≠ i}) => Ys j.val ω))
      Xprefix (hXs i) hYpair hXprefix e.symm]
  -- Step C: 2-var Y-axis chain rule.
  -- Need finiteness side condition: I(Xprefix; X_i) ≠ ∞ (finite alphabet).
  have h_fin : Shannon.mutualInfo μ Xprefix (Xs i) ≠ ∞ :=
    Shannon.mutualInfo_ne_top μ Xprefix (Xs i) hXprefix (hXs i)
  exact condMutualInfo_chain_rule_Y_2var μ (Xs i) (Ys i)
    (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω) Xprefix
    (hXs i) (hYs i) hYother hXprefix h_fin

/-- **`h_yother_zero` discharge from `IsMemorylessChannelStrong`** (Session 2 — sorry).

The Yother term `condMI X_i Y^{≠i} (Xprefix, Y_i)` should vanish from
`outputs_cond_indep i` (`Y^{≠i} → X^n → Y_i`) combined with `per_letter_markov`. The
challenge: the conditioning RV is `(Xprefix, Y_i)`, not `X^n` alone, so direct application
of `condMutualInfo_eq_zero_of_markov` is not possible. Need an additional Markov-chain
rearrangement (push `X^{>i}` from the conditioning side, absorb via per-letter chain).

撤退ライン: 本 lemma は **Session 2** で discharge する。Session 1 では skeleton statement
のみ確定し isolated `sorry` で残す。 -/
lemma h_yother_zero_of_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (_hXs : ∀ i, Measurable (Xs i)) (_hYs : ∀ i, Measurable (Ys i))
    (_h_strong : IsMemorylessChannelStrong μ Xs Ys) :
    ∀ i : Fin n,
      Shannon.condMutualInfo μ (Xs i)
          (fun ω (j : {j : Fin n // j ≠ i}) => Ys j.val ω)
          (fun ω => (
            (fun (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω),
            Ys i ω)) = 0 := by
  sorry

end Discharge

/-! ## 主定理: 強 memoryless 版 channel coding converse -/

section MainConverseStrong

variable {n : ℕ}
variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M] [StandardBorelSpace M]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
variable {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]

omit [DecidableEq β] in
/-- **Channel coding converse, strong memoryless DMC version (D-2'')**.

`channel_coding_converse_general_memoryless` (D-2', hypothesis-form) を
`IsMemorylessChannelStrong` から純粋に導出する。3 仮説のうち `h_split`, `h_markov_xprefix`
は本 file で discharge 済み、`h_yother_zero` は Session 2 まで sorry (本定理は
`h_yother_zero_of_strong` 経由でその sorry を吸収する)。

D-2' の主定理 hypothesis 形と同じ結論 — finite-alphabet memoryless DMC で
Cover-Thomas Thm 7.9 の per-letter `I(X_i; Y_i)` バウンドが Fano 不等式と組み合わさる形。 -/
theorem channel_coding_converse_general_memoryless_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : Shannon.IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (h_memo : IsMemorylessChannel μ (fun i ω => encoder (Msg ω) i) Ys)
    (h_strong : IsMemorylessChannelStrong μ
      (fun i ω => encoder (Msg ω) i) Ys)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : Shannon.mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (∑ i : Fin n,
        (Shannon.mutualInfo μ
          (fun ω => encoder (Msg ω) i) (Ys i)).toReal) +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1) := by
  -- Set up the per-letter X RV from encoder.
  set Xs : Fin n → Ω → α := fun i ω => encoder (Msg ω) i with hXs_def
  have h_encoder : Measurable encoder := measurable_of_countable _
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i =>
    (measurable_pi_apply i).comp (h_encoder.comp hMsg)
  -- Discharge h_markov_xprefix and h_split from h_strong.
  have h_markov_xprefix := h_markov_xprefix_of_strong μ Xs Ys hXs_meas hYs h_strong
  have h_split := h_split_of_strong μ Xs Ys hXs_meas hYs
  have h_yother_zero := h_yother_zero_of_strong μ Xs Ys hXs_meas hYs h_strong
  -- Apply D-2' main theorem.
  exact channel_coding_converse_general_memoryless
    μ Msg encoder Ys decoder hMsg hYs hdecoder hmarkov h_memo
    h_yother_zero h_split h_markov_xprefix
    hMsg_uniform hcard hMI_finite

end MainConverseStrong

end InformationTheory.Shannon.ChannelCodingConverseGeneral
