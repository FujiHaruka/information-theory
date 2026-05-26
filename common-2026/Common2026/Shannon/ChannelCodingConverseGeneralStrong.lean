import Common2026.Draft.Shannon.ChannelCodingConverseGeneralComplete
import Common2026.Meta.EntryPoint
import Common2026.Shannon.CondEntropyMemoryless
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Channel coding converse (general input) — strong memoryless variant (D-2'')

[D-2'' ムーンショット plan](../../../docs/shannon/channel-coding-converse-general-d2-double-prime-plan.md)
の Phase B。`channel_coding_converse_general_memoryless_strong` は **Cover-Thomas Thm 7.9
のエントロピー劣加法経路** (`Common2026/Shannon/CondEntropyMemoryless.lean`) を通じて
`IsMemorylessChannelStrong` から直接導出する。D-2' hypothesis-form (3 仮説経由) は
`h_yother_zero` が encoder 任意では偽 (反例: `X_1 := X_0`) のため、Cover-Thomas の
劣加法 (`H(Y^n) ≤ ∑ H(Y_i)`) ＋ 強 memoryless `H(Y^n|X^n) = ∑ H(Y_i|X_i)` 経路に切り替えた。

## Scope

* `IsMemorylessChannelStrong` (Option C, structure 形): 2 つの Markov axiom
  - per-letter:  `X^n → X_i → Y_i`
  - outputs cond. indep.: `Y^{≠i} → X^n → Y_i`
* `MeasurableEquiv` plumbing: `Fin n → β ≃ᵐ β × ({j // j ≠ i} → β)`
  (`piEquivPiSubtypeProd` + `funUnique` の合成)
* `h_markov_xprefix_of_strong`, `h_split_of_strong`: D-2' hypothesis-form 用の
  helper だが、新しい主定理経路 (Cover-Thomas) では呼ばれない **dead code**。歴史的記録
  および将来 D-2' hypothesis-form を再利用する場合のため残置。
* `channel_coding_converse_general_memoryless_strong` (主定理): single-shot Markov-encoder
  converse + `mutualInfo_le_sum_per_letter_of_memoryless_strong` (Cover-Thomas Thm 7.9
  encoder-agnostic chain) で証明。

**Architectural note**: An earlier session attempted to derive the D-2' hypothesis
`h_yother_zero` from `IsMemorylessChannelStrong`, but a counterexample (n = 2, i = 0,
X_1 := X_0 degenerate encoder + iid Bernoulli(1/4) noise) showed the claim is
*mathematically false* under arbitrary encoders. The fix is the entropy-subadditivity
route of Cover-Thomas Thm 7.9, which bypasses `h_yother_zero` entirely. See
`CondEntropyMemoryless.lean` for the supporting infrastructure (entropy subadditivity,
n-var conditional chain rule, Markov-drop-irrelevant, conditional factorization). -/

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
@[entry_point]
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
@[entry_point]
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

/- **Architectural note**: an earlier session attempted to derive the D-2'
hypothesis `h_yother_zero : condMI X_i Y^{≠i} (Xprefix, Y_i) = 0` from
`IsMemorylessChannelStrong`. A counterexample (n = 2, i = 0, X_1 := X_0
degenerate encoder + iid Bernoulli(1/4) noise) showed the claim is **false**
under arbitrary encoders — the joint distribution of `(X_i, X^{≠i})` is
unconstrained, so `Y^{≠i} ⊥/ X_i | Y_i` in general.

The fix is the entropy-subadditivity route of Cover-Thomas Thm 7.9
(see `mutualInfo_le_sum_per_letter_of_memoryless_strong` in the next section,
backed by `Common2026/Shannon/CondEntropyMemoryless.lean`), which bypasses
`h_yother_zero` entirely and works for any encoder. -/

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

/-- **Channel coding converse, strong memoryless DMC version (D-2'')**.

`IsMemorylessChannelStrong` 仮定下で per-letter mutual information の和に減衰する形。
Cover-Thomas Thm 7.9 のエントロピー劣加法経路を辿る:

```
log |M| ≤ I(X^n; Y^n).toReal + Fano                              -- single-shot Markov encoder
        ≤ ∑ I(X_i; Y_i).toReal + Fano                            -- mutualInfo_le_sum_per_letter_of_memoryless_strong
```

D-2' hypothesis-form (`channel_coding_converse_general_memoryless`) は 3 仮説の中に
`h_yother_zero` を含むが、これは encoder 任意では数学的に偽である (反例: `X_1 := X_0`)
ため、本定理はこれを **経由しない**。代わりに `mutualInfo_le_sum_per_letter_of_memoryless_strong`
は subadditivity (encoder-agnostic) + 強 memoryless `H(Y^n|X^n) = ∑ H(Y_i|X_i)` のみを使う。

引数 `h_memo : IsMemorylessChannel` は historical reasons (D-2' 互換) で残しているが、
新しい証明経路では使われない。 -/
@[entry_point]
theorem channel_coding_converse_general_memoryless_strong
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : Shannon.IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (_h_memo : IsMemorylessChannel μ (fun i ω => encoder (Msg ω) i) Ys)
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
  -- Set up per-letter and joint X RVs.
  set Xs : Fin n → Ω → α := fun i ω => encoder (Msg ω) i with hXs_def
  have h_encoder : Measurable encoder := measurable_of_countable _
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i =>
    (measurable_pi_apply i).comp (h_encoder.comp hMsg)
  have hY_pi : Measurable (fun ω (i : Fin n) => Ys i ω) :=
    measurable_pi_iff.mpr hYs
  -- Step 1: single-shot Markov-encoder converse on (X = Fin n → α, Y = Fin n → β).
  have h_single :=
    Shannon.shannon_converse_single_shot_markov_encoder (X := Fin n → α)
      μ Msg encoder (fun ω i => Ys i ω) decoder
      hMsg hY_pi h_encoder hdecoder hmarkov hMsg_uniform hcard hMI_finite
  -- Normalize `(encoder ∘ Msg)` to `fun ω => encoder (Msg ω)`.
  rw [show (encoder ∘ Msg) = fun ω => encoder (Msg ω) from rfl] at h_single
  -- Step 2: Cover-Thomas Thm 7.9 — per-letter MI bound.
  -- `fun ω => encoder (Msg ω) = fun ω j => Xs j ω` (definitional).
  have h_pi_eq : (fun ω => encoder (Msg ω)) = (fun ω j => Xs j ω) := by
    funext ω j; rfl
  rw [h_pi_eq] at h_single
  have h_per_letter :=
    Shannon.mutualInfo_le_sum_per_letter_of_memoryless_strong μ Xs Ys hXs_meas hYs
      h_strong.per_letter_markov h_strong.outputs_cond_indep
  -- Combine: log |M| ≤ I(X^n; Y^n).toReal + Fano ≤ ∑ I(X_i; Y_i).toReal + Fano.
  linarith

end MainConverseStrong

end InformationTheory.Shannon.ChannelCodingConverseGeneral
