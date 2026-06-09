import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.MIChainRule

/-!
# Channel coding converse — general input form, chain-rule decomposition (D-2)

[D-2 ムーンショット plan](../../../docs/shannon/channel-coding-converse-general-plan.md) の
第一歩。既存 `channel_coding_converse_iid` (`ChannelCodingConverse.lean`) は **i.i.d. 入力**
仮定下で `I(X^n; Y^n)` を `n · I(X_0; Y_0)` に圧縮する形だが、本ファイルでは **iid 仮定を完全に
外し**、代わりに `mutualInfo_chain_rule_fin` で `I(X^n; Y^n)` を per-i conditional MI の和に
分解した形を publish する。

### 主張

`Msg : Ω → M` を一様分布、`encoder : M → (Fin n → α)`、`Ys : Fin n → Ω → β` を通信路出力、
`decoder : (Fin n → β) → M` とする。Markov chain `Msg → encoder ∘ Msg → Y^n` 仮定下で:

```
log |M| ≤ ∑ i, I(X_i; Y^n | X^{<i}).toReal + h(Pe) + Pe · log(|M| − 1)
```

ここで `X_i ω := encoder (Msg ω) i`、`Y^n ω := fun i => Ys i ω`、`Pe := errorProb`、
`X^{<i}` は先頭 `i` 個の入力記号 (prefix RV)。

### 構成 (3 step、bridge ゼロ)

1. `shannon_converse_single_shot_markov_encoder` で `log|M| ≤ I(X^n; Y^n).toReal + Fano`。
2. `mutualInfo_chain_rule_fin` で `I(X^n; Y^n) = ∑ I(X_i; Y^n | X^{<i})` (ENNReal 等式)。
3. `ENNReal.toReal_sum` で和の `.toReal` 分配 (per-i `condMutualInfo_ne_top` で summand 有限)。

### iid 版との関係

iid 仮定下では `mutualInfo_iid_eq_nsmul` で chain rule を経由せず `n · I(X_0; Y_0)` に直接
圧縮できる (既存 `channel_coding_converse_iid` 採用経路)。本形は **iid を外した代わりに** 和を
そのまま残したもの。次の段で memoryless channel property を加えれば per-summand
`I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i)` が出て Cover-Thomas 7.9 完全形に到達するが、本セッションの
scope 外 (deferred)。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M]
variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

omit [DecidableEq M] [DecidableEq α] [DecidableEq β] in
/-- Channel coding converse, **general input** form (Markov encoder, chain-rule decomposition).

`Msg : Ω → M` 一様、`encoder : M → (Fin n → α)`、`Ys : Fin n → Ω → β`、
`decoder : (Fin n → β) → M`。Markov chain `Msg → encoder ∘ Msg → Y^n` 仮定下で:

```
log |M| ≤ ∑ i, I(X_i; Y^n | X^{<i}).toReal + h(Pe) + Pe · log(|M| − 1)
```

ここで:
* `X_i ω := encoder (Msg ω) i`
* `Y^n ω := fun i => Ys i ω`
* `X^{<i} ω := fun (j : Fin i.val) => encoder (Msg ω) ⟨j.val, ...⟩` (prefix RV)
* `Pe := errorProb μ Msg Y^n decoder`

iid 仮定を要しない (既存 `channel_coding_converse_iid` との違い)。memoryless channel property に
基づく per-summand bound `I(X_i; Y^n | X^{<i}) ≤ I(X_i; Y_i)` は deferred、本定理 RHS は
chain rule で分解した形を残す。 -/
@[entry_point]
theorem channel_coding_converse_general_chainRule
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (∑ i : Fin n,
        (condMutualInfo μ
          (fun ω => encoder (Msg ω) i)
          (fun ω j => Ys j ω)
          (fun ω (j : Fin i.val) =>
            encoder (Msg ω) ⟨j.val, j.isLt.trans i.isLt⟩)).toReal) +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1) := by
  classical
  -- Auto-derived measurability.
  have h_encoder : Measurable encoder := measurable_of_countable _
  have h_X_full : Measurable (fun ω => encoder (Msg ω)) := h_encoder.comp hMsg
  have h_Yo : Measurable (fun ω (i : Fin n) => Ys i ω) :=
    measurable_pi_iff.mpr hYs
  -- Step 1: Markov-encoder single-shot converse on (X = Fin n → α, Y = Fin n → β).
  have h_step1 :=
    shannon_converse_single_shot_markov_encoder (X := Fin n → α)
      μ Msg encoder (fun ω i => Ys i ω) decoder
      hMsg h_Yo h_encoder hdecoder hmarkov hMsg_uniform hcard hMI_finite
  -- Step 2: n-variable chain rule for mutual information.
  set Xs : Fin n → Ω → α := fun i ω => encoder (Msg ω) i with hXs_def
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i =>
    (measurable_pi_apply i).comp h_X_full
  have h_chain :=
    mutualInfo_chain_rule_fin (Y := Fin n → β)
      μ Xs hXs_meas (fun ω i => Ys i ω) h_Yo
  -- `fun ω i => Xs i ω = fun ω => encoder (Msg ω)` definitionally.
  have h_pi_eq_encoder :
      (fun ω (i : Fin n) => Xs i ω) = fun ω => encoder (Msg ω) := rfl
  rw [h_pi_eq_encoder] at h_chain
  -- `(encoder ∘ Msg) = fun ω => encoder (Msg ω)` definitionally; normalize.
  rw [show (encoder ∘ Msg) = fun ω => encoder (Msg ω) from rfl, h_chain] at h_step1
  -- Step 3: distribute `.toReal` over the finite sum.
  -- Each per-i conditional MI is finite (finite alphabets).
  have h_each_ne_top : ∀ i : Fin n,
      condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
        (fun ω (j : Fin i.val) =>
          Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) ≠ ∞ := by
    intro i
    -- Prefix RV is measurable.
    have h_prefix_meas :
        Measurable (fun ω (j : Fin i.val) =>
          Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) :=
      measurable_pi_iff.mpr fun j => hXs_meas ⟨j.val, j.isLt.trans i.isLt⟩
    exact condMutualInfo_ne_top (X := α) (Y := Fin n → β) (Z := Fin i.val → α)
      μ (Xs i) (fun ω j => Ys j ω)
      (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      (hXs_meas i) h_Yo h_prefix_meas
  have h_each_ne_top' : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      condMutualInfo μ (Xs i) (fun ω j => Ys j ω)
        (fun ω (j : Fin i.val) =>
          Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) ≠ ∞ :=
    fun i _ => h_each_ne_top i
  rw [ENNReal.toReal_sum h_each_ne_top'] at h_step1
  -- `Xs i = fun ω => encoder (Msg ω) i` definitionally; goal matches h_step1.
  exact h_step1

end InformationTheory.Shannon
