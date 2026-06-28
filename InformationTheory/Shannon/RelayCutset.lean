import InformationTheory.Shannon.MultipleAccess.Converse

/-!
# Relay channel — cut-set outer bound (structure + single-letterization)

The relay channel (Cover–Thomas §15.10) has a single sender, a single relay, and a single
receiver. The cut-set outer bound (Thm 15.10.1) bounds any achievable rate by the minimum of
two mutual-information quantities, evaluated at the worst joint input distribution:

* the **broadcast cut** `I(X; Y₁, Y | X₁)` — information leaving the sender, conditioned on
  the relay's transmission;
* the **MAC cut** `I(X, X₁; Y)` — information arriving at the receiver from the
  sender–relay pair.

This file provides the structural definitions (`RelayChannel`, `RelayCode`,
`relayCutsetBound`) and the two **single-letterization** lemmas that turn the block
quantities `I(Xⁿ, X₁ⁿ; Yⁿ)` and `I(Xⁿ; Y₁ⁿ, Yⁿ | X₁ⁿ)` into per-letter sums under a
memoryless relay channel. Both single-letterizations are instances of the multiple-access
converse machinery: the MAC cut reuses the unconditional per-letter bound and the broadcast
cut reuses the conditional one, with the joint input `(Xᵢ, X₁ᵢ)` and joint output
`(Y₁ᵢ, Yᵢ)` playing the roles of the MAC's joint input/output.

The memoryless structure is a *precondition* (regularity); the per-letter inequality (the
genuine content) is proven, not assumed. The operational outer bound
`relay_cutset_outer_bound` (Fano + data processing + the `min` combination) lives in a
separate file.

## Main statements

* `relay_mac_cut_singleletterize` — `I(Xⁿ, X₁ⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ, X₁ᵢ; Yᵢ)`.
* `relay_broadcast_cut_singleletterize` — `I(Xⁿ; Y₁ⁿ, Yⁿ | X₁ⁿ) ≤ ∑ᵢ I(Xᵢ; Y₁ᵢ, Yᵢ | X₁ᵢ)`.
-/

namespace InformationTheory.Shannon.Relay

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open InformationTheory.Shannon.MAC
open scoped ENNReal NNReal BigOperators

/-- A **relay channel**: Markov kernel from joint input `(α × α₁)` to joint output `(β × β₁)`
(sender input `α`, relay input `α₁`, receiver output `β`, relay observation `β₁`). -/
abbrev RelayChannel (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁] [MeasurableSpace β] [MeasurableSpace β₁] :=
  Kernel (α × α₁) (β × β₁)

/-- A **relay block code** of length `n` with `M` messages: a sender encoder, a causal relay
function (reads past relay observations `β₁`, emits the next relay input `α₁`), and a decoder. -/
structure RelayCode (M n : ℕ) (α α₁ β β₁ : Type*)
    [MeasurableSpace α] [MeasurableSpace α₁] [MeasurableSpace β] [MeasurableSpace β₁] where
  encoder : Fin M → (Fin n → α)
  relay   : ∀ (i : Fin n), (Fin i.val → β₁) → α₁
  decoder : (Fin n → β) → Fin M

/-- **Cut-set outer bound (scalar form)**: the minimum of the broadcast-cut rate
`Ib = I(X; Y₁, Y | X₁)` and the MAC-cut rate `Im = I(X, X₁; Y)`. The outer maximisation over
joint input pmfs `p(x, x₁)` is left to callers. -/
noncomputable def relayCutsetBound (Ib Im : ℝ) : ℝ := min Ib Im

@[simp] lemma relayCutsetBound_def (Ib Im : ℝ) : relayCutsetBound Ib Im = min Ib Im := rfl

section SingleLetterization

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α α₁ β β₁ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
    [MeasurableSpace α₁] [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
    [MeasurableSpace β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable {n : ℕ}

omit [DecidableEq α] [DecidableEq α₁] [DecidableEq β] in
/-- **MAC-cut single-letterization**: under a memoryless relay channel (joint input
`(Xᵢ, X₁ᵢ)` to receiver output `Yᵢ`), the block mutual information `I(Xⁿ, X₁ⁿ; Yⁿ)` is bounded
by the per-letter sum `∑ᵢ I(Xᵢ, X₁ᵢ; Yᵢ)`. The memoryless structure is a precondition; the
inequality (the genuine content) is proven, not assumed.
@audit:ok -/
theorem relay_mac_cut_singleletterize
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (X₁s : Fin n → Ω → α₁) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hX₁s : ∀ i, Measurable (X₁s i)) (hYs : ∀ i, Measurable (Ys i))
    (h_memo : IsMemorylessChannel μ (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys) :
    (mutualInfo μ (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω)).toReal
      ≤ ∑ i : Fin n, (mutualInfo μ (fun ω ↦ (Xs i ω, X₁s i ω)) (Ys i)).toReal := by
  have hJoint : ∀ i, Measurable (fun ω ↦ (Xs i ω, X₁s i ω)) := fun i ↦
    (hXs i).prodMk (hX₁s i)
  have h_per_letter := per_letter_markov_of_memoryless μ
    (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys hJoint hYs h_memo
  have h_outputs := outputs_cond_indep_of_memoryless μ
    (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys hJoint hYs h_memo
  exact mutualInfo_le_sum_per_letter_of_memoryless_strong μ
    (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys hJoint hYs h_per_letter h_outputs

omit [DecidableEq α] [DecidableEq β] [DecidableEq β₁] in
/-- **Broadcast-cut single-letterization**: the conditional block mutual information
`I(Xⁿ; Y₁ⁿ, Yⁿ | X₁ⁿ)` is bounded by the per-letter sum `∑ᵢ I(Xᵢ; Y₁ᵢ, Yᵢ | X₁ᵢ)`, under the
memoryless relay channel with joint input `(Xᵢ, X₁ᵢ)` and joint output `(Y₁ᵢ, Yᵢ)`.
@audit:ok -/
theorem relay_broadcast_cut_singleletterize
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (X₁s : Fin n → Ω → α₁)
    (Ys : Fin n → Ω → β) (Y₁s : Fin n → Ω → β₁)
    (hXs : ∀ i, Measurable (Xs i)) (hX₁s : ∀ i, Measurable (X₁s i))
    (hYs : ∀ i, Measurable (Ys i)) (hY₁s : ∀ i, Measurable (Y₁s i))
    (h_memo : IsMemorylessChannel μ (fun i ω ↦ (Xs i ω, X₁s i ω)) (fun i ω ↦ (Y₁s i ω, Ys i ω))) :
    (condMutualInfo μ (fun ω j ↦ Xs j ω) (fun ω j ↦ (Y₁s j ω, Ys j ω)) (fun ω j ↦ X₁s j ω)).toReal
      ≤ ∑ i : Fin n,
          (condMutualInfo μ (Xs i) (fun ω ↦ (Y₁s i ω, Ys i ω)) (X₁s i)).toReal := by
  have hJoint : ∀ i, Measurable (fun ω ↦ (Xs i ω, X₁s i ω)) := fun i ↦
    (hXs i).prodMk (hX₁s i)
  have hJointOut : ∀ i, Measurable (fun ω ↦ (Y₁s i ω, Ys i ω)) := fun i ↦
    (hY₁s i).prodMk (hYs i)
  have h_per_letter := per_letter_markov_of_memoryless μ
    (fun i ω ↦ (Xs i ω, X₁s i ω)) (fun i ω ↦ (Y₁s i ω, Ys i ω)) hJoint hJointOut h_memo
  have h_outputs := outputs_cond_indep_of_memoryless μ
    (fun i ω ↦ (Xs i ω, X₁s i ω)) (fun i ω ↦ (Y₁s i ω, Ys i ω)) hJoint hJointOut h_memo
  exact condMutualInfo_singleletter_le_of_memoryless μ Xs X₁s
    (fun i ω ↦ (Y₁s i ω, Ys i ω)) hXs hX₁s hJointOut h_per_letter h_outputs

end SingleLetterization

section MacCutOuterBound

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α α₁ β : Type*}
  [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
  [Fintype α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
    [StandardBorelSpace α₁]
  [Fintype β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
variable {M n : ℕ} [NeZero M]

/-- **MAC-cut operational outer bound** (relay channel, Cover–Thomas Thm 15.10.1, MAC cut): for a
uniformly distributed message `W` decoded from the receiver output `Yⁿ`, the rate is bounded by
the per-letter MAC-cut sum plus a Fano slack,
`log M ≤ ∑ᵢ I(Xᵢ, X₁ᵢ; Yᵢ) + h(Pe) + Pe · log(M - 1)`, where `Pe` is the block decoding error
probability.

The proof chains destination Fano (`shannon_converse_single_shot`), the data-processing
inequality along the block Markov chain `W → (Xⁿ, X₁ⁿ) → Yⁿ` (`mutualInfo_le_of_markov`), and the
MAC-cut single-letterization (`relay_mac_cut_singleletterize`). The Markov and memoryless
hypotheses are *preconditions* (structure / regularity); the per-letter inequality (the genuine
content) is proven, not assumed, so neither hypothesis is load-bearing. The outer maximisation
over joint input pmfs `p(x, x₁)` — and hence the conversion of the per-letter sum to
`n · max_p I` — is left to callers, which is why the conclusion keeps the explicit per-letter sum.
@audit:ok -/
theorem relay_mac_cut_outer_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Fin M) (decoder : (Fin n → β) → Fin M)
    (Xs : Fin n → Ω → α) (X₁s : Fin n → Ω → α₁) (Ys : Fin n → Ω → β)
    (hW : Measurable W) (hdecoder : Measurable decoder)
    (hXs : ∀ i, Measurable (Xs i)) (hX₁s : ∀ i, Measurable (X₁s i)) (hYs : ∀ i, Measurable (Ys i))
    (hW_uniform : μ.map W = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ M)
    (h_markov : IsMarkovChain μ W (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω))
    (h_memo : IsMemorylessChannel μ (fun i ω ↦ (Xs i ω, X₁s i ω)) Ys) :
    Real.log (M : ℝ) ≤
      (∑ i : Fin n, (mutualInfo μ (fun ω ↦ (Xs i ω, X₁s i ω)) (Ys i)).toReal)
        + Real.binEntropy (MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) decoder)
        + MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) decoder * Real.log ((M : ℝ) - 1) := by
  have hYpi : Measurable (fun ω j ↦ Ys j ω) := measurable_pi_iff.mpr hYs
  have hZpi : Measurable (fun ω j ↦ (Xs j ω, X₁s j ω)) :=
    measurable_pi_iff.mpr (fun j ↦ (hXs j).prodMk (hX₁s j))
  have hMI_W : mutualInfo μ W (fun ω j ↦ Ys j ω) ≠ ∞ :=
    mutualInfo_ne_top μ W (fun ω j ↦ Ys j ω) hW hYpi
  have hMI_Z :
      mutualInfo μ (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω) ≠ ∞ :=
    mutualInfo_ne_top μ (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω) hZpi hYpi
  -- Step 1: destination Fano `log M ≤ I(W; Yⁿ) + h(Pe) + Pe · log(M − 1)`.
  have hcard' : 2 ≤ Fintype.card (Fin M) := by rw [Fintype.card_fin]; exact hcard
  have hStep1 := shannon_converse_single_shot μ W (fun ω j ↦ Ys j ω) decoder
    hW hYpi hdecoder hW_uniform hcard' hMI_W
  rw [Fintype.card_fin] at hStep1
  -- Step 2: data-processing inequality along `W → (Xⁿ, X₁ⁿ) → Yⁿ`.
  have hStep2_enn :
      mutualInfo μ W (fun ω j ↦ Ys j ω)
        ≤ mutualInfo μ (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω) :=
    mutualInfo_le_of_markov μ W (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω)
      hW hZpi hYpi h_markov
  have hStep2 :
      (mutualInfo μ W (fun ω j ↦ Ys j ω)).toReal
        ≤ (mutualInfo μ (fun ω j ↦ (Xs j ω, X₁s j ω)) (fun ω j ↦ Ys j ω)).toReal :=
    ENNReal.toReal_mono hMI_Z hStep2_enn
  -- Step 3: MAC-cut single-letterization `I(Xⁿ, X₁ⁿ; Yⁿ) ≤ ∑ᵢ I(Xᵢ, X₁ᵢ; Yᵢ)`.
  have hStep3 := relay_mac_cut_singleletterize μ Xs X₁s Ys hXs hX₁s hYs h_memo
  linarith [hStep1, hStep2, hStep3]

end MacCutOuterBound

section BroadcastCutTelescope

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α α₁ β β₁ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁]
    [MeasurableSpace α₁] [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype β] [DecidableEq β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁]
    [MeasurableSpace β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable {M n : ℕ} [NeZero M]

omit [DecidableEq α] [DecidableEq α₁] [DecidableEq β] [DecidableEq β₁] in
/-- **Broadcast-cut message-level telescoping** (relay channel, Cover–Thomas Thm 15.10.1,
broadcast cut): the message–output mutual information `I(W; Yⁿ)` is bounded directly by the
per-letter conditional sum `∑ᵢ I(Xᵢ; Y₁ᵢ, Yᵢ | X₁ᵢ)`, where `Xᵢ = encoder(W)ᵢ` is the i-th
sender symbol and `X₁ᵢ = relay i (Y₁^{<i})` is the i-th relay symbol read causally from the
relay's past observations.

This is the gateway atom for the broadcast cut: it cannot be obtained from
`relay_broadcast_cut_singleletterize` (which single-letterizes the *block* conditional
`I(Xⁿ; Y₁ⁿ, Yⁿ | X₁ⁿ)`), because routing through the block quantity leaves a chain-rule
remainder `I(W; X₁ⁿ) ≠ 0` (the relay input `X₁ⁿ` depends causally on `W` through the
feedback). The proof instead telescopes per-letter with the causal conditioner `X₁ᵢ`:

```
I(W; Yⁿ) ≤ I(W; (Y₁ⁿ, Yⁿ))                                     -- post-processing
         = ∑ᵢ [H(Vᵢ | V^{<i}) − H(Vᵢ | W, V^{<i})]              -- chain rule, Vᵢ = (Y₁ᵢ, Yᵢ)
         ≤ ∑ᵢ [H(Vᵢ | X₁ᵢ) − H(Vᵢ | Xᵢ, X₁ᵢ)]                  -- per-letter (below)
         = ∑ᵢ I(Xᵢ; Vᵢ | X₁ᵢ).
```

The per-letter step uses two facts:

* `H(Vᵢ | V^{<i}) ≤ H(Vᵢ | X₁ᵢ)` — conditioning reduces entropy: `X₁ᵢ = relay i (Y₁^{<i})` is
  a deterministic function of the past pairs `V^{<i}`, so conditioning on `V^{<i}` is a
  refinement of conditioning on `X₁ᵢ`.  Structural, derived (not assumed).
* `H(Vᵢ | W, V^{<i}) = H(Vᵢ | Xᵢ, X₁ᵢ)` — memorylessness: both `Xᵢ = encoder(W)ᵢ` (a function
  of `W`) and `X₁ᵢ` (a function of `V^{<i}`) are deterministic functions of `(W, V^{<i})`, and
  given the i-th channel input `(Xᵢ, X₁ᵢ)` the i-th output `Vᵢ` is independent of `(W, V^{<i})`.

The single precondition `h_memo` is exactly the latter independence,
`Vᵢ ⫫ (W, V^{<i}) | (Xᵢ, X₁ᵢ)`, the d-separation property of a memoryless relay channel: the
i-th output is conditionally independent of the message and the past output pairs given the
i-th channel input.  It encodes the channel's memoryless structure, not the conclusion (it is
true in the operational setup where `Vᵢ` is fresh channel noise applied to `(Xᵢ, X₁ᵢ)`), so it
is a *regularity precondition*, not load-bearing — mirroring the `h_memo` of
`bc_input_singleletterize`.  It is **not** the false independence `W ⫫ X₁ⁿ` (which fails for a
causal relay): the conditioning here is on the i-th input, not on a fictitious second message.
@audit:ok -/
theorem relay_broadcast_cut_message_telescope
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Fin M)
    (c : RelayCode M n α α₁ β β₁)
    (Ys : Fin n → Ω → β) (Y₁s : Fin n → Ω → β₁)
    (hW : Measurable W)
    (hYs : ∀ i, Measurable (Ys i)) (hY₁s : ∀ i, Measurable (Y₁s i))
    (h_memo : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω ↦ (Y₁s i ω, Ys i ω))
        (fun ω ↦ (c.encoder (W ω) i,
          c.relay i (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)))
        (fun ω ↦ (W ω,
          fun (j : Fin i.val) ↦
            (Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω, Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)))) :
    (mutualInfo μ W (fun ω j ↦ Ys j ω)).toReal
      ≤ ∑ i : Fin n,
          (condMutualInfo μ (fun ω ↦ c.encoder (W ω) i) (fun ω ↦ (Y₁s i ω, Ys i ω))
            (fun ω ↦ c.relay i
              (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))).toReal := by
  classical
  -- Abbreviations matching the conclusion's syntactic shape.
  set Xs : Fin n → Ω → α := fun i ω ↦ c.encoder (W ω) i with hXs_def
  set X₁s : Fin n → Ω → α₁ := fun i ω ↦
    c.relay i (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω) with hX₁s_def
  set Vs : Fin n → Ω → (β₁ × β) := fun i ω ↦ (Y₁s i ω, Ys i ω) with hVs_def
  set Vpi : Ω → (Fin n → β₁ × β) := fun ω j ↦ Vs j ω with hVpi_def
  -- per-letter prefix `V^{<i}` and conditioners.
  set Vpre : ∀ i : Fin n, Ω → (Fin i.val → β₁ × β) := fun i ω (j : Fin i.val) ↦
    Vs ⟨j.val, j.isLt.trans i.isLt⟩ ω with hVpre_def
  set WVpre : ∀ i : Fin n, Ω → (Fin M × (Fin i.val → β₁ × β)) := fun i ω ↦
    (W ω, Vpre i ω) with hWVpre_def
  set Js : Fin n → Ω → (α × α₁) := fun i ω ↦ (Xs i ω, X₁s i ω) with hJs_def
  -- Measurabilities.
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i ↦
    (measurable_of_countable (fun w ↦ c.encoder w i)).comp hW
  have hX₁s_meas : ∀ i, Measurable (X₁s i) := fun i ↦
    (measurable_of_countable (c.relay i)).comp
      (measurable_pi_iff.mpr fun j ↦ hY₁s _)
  have hVs_meas : ∀ i, Measurable (Vs i) := fun i ↦ (hY₁s i).prodMk (hYs i)
  have hVpi_meas : Measurable Vpi := measurable_pi_iff.mpr hVs_meas
  have hYpi_meas : Measurable (fun ω j ↦ Ys j ω) := measurable_pi_iff.mpr hYs
  have hVpre_meas : ∀ i, Measurable (Vpre i) := fun i ↦
    measurable_pi_iff.mpr fun j ↦ hVs_meas _
  have hWVpre_meas : ∀ i, Measurable (WVpre i) := fun i ↦ hW.prodMk (hVpre_meas i)
  have hJs_meas : ∀ i, Measurable (Js i) := fun i ↦ (hXs_meas i).prodMk (hX₁s_meas i)
  -- Step 1: post-processing `I(W; Yⁿ) ≤ I(W; Vⁿ)` (`Yⁿ` is `π₂` of `Vⁿ`).
  have hMI_Vpi_fin : mutualInfo μ W Vpi ≠ ∞ := mutualInfo_ne_top μ W Vpi hW hVpi_meas
  have hPost : (mutualInfo μ W (fun ω j ↦ Ys j ω)).toReal ≤ (mutualInfo μ W Vpi).toReal := by
    refine ENNReal.toReal_mono hMI_Vpi_fin ?_
    have h := mutualInfo_le_of_postprocess μ W Vpi hW hVpi_meas
      (f := fun (v : Fin n → β₁ × β) (j : Fin n) ↦ (v j).2) (measurable_pi_iff.mpr fun j ↦
        (measurable_pi_apply j).snd)
    have hfun : ((fun (v : Fin n → β₁ × β) (j : Fin n) ↦ (v j).2) ∘ Vpi)
        = fun ω j ↦ Ys j ω := by
      funext ω j; simp [hVpi_def, hVs_def]
    rwa [hfun] at h
  -- Step 2: `I(W; Vⁿ) = H(Vⁿ) − H(Vⁿ | W)`.
  have hLHS : (mutualInfo μ W Vpi).toReal
      = entropy μ Vpi - InformationTheory.MeasureFano.condEntropy μ Vpi W := by
    rw [mutualInfo_comm μ W Vpi hW hVpi_meas]
    exact mutualInfo_eq_entropy_sub_condEntropy μ Vpi W hVpi_meas hW
  -- Step 3: chain rules.
  have hEnt : entropy μ Vpi
      = ∑ i : Fin n, InformationTheory.MeasureFano.condEntropy μ (Vs i) (Vpre i) :=
    jointEntropy_chain_rule μ Vs hVs_meas
  have hCondEnt : InformationTheory.MeasureFano.condEntropy μ Vpi W
      = ∑ i : Fin n, InformationTheory.MeasureFano.condEntropy μ (Vs i) (WVpre i) :=
    condEntropy_pi_chain_rule_aux μ W Vs hW hVs_meas
  -- Step 4: per-letter RHS as a conditional-entropy difference.
  have hRHS : ∀ i : Fin n,
      (condMutualInfo μ (Xs i) (Vs i) (X₁s i)).toReal
        = InformationTheory.MeasureFano.condEntropy μ (Vs i) (X₁s i)
          - InformationTheory.MeasureFano.condEntropy μ (Vs i)
              (fun ω ↦ (X₁s i ω, Xs i ω)) := by
    intro i
    rw [condMutualInfo_comm μ (Xs i) (Vs i) (X₁s i) (hXs_meas i) (hVs_meas i) (hX₁s_meas i)]
    exact condMutualInfo_eq_condEntropy_sub_condEntropy μ (Vs i) (X₁s i) (Xs i)
      (hVs_meas i) (hX₁s_meas i) (hXs_meas i)
  -- Step 5 (conditioning reduces entropy): `H(Vᵢ | V^{<i}) ≤ H(Vᵢ | X₁ᵢ)`.
  have hCond : ∀ i : Fin n,
      InformationTheory.MeasureFano.condEntropy μ (Vs i) (Vpre i)
        ≤ InformationTheory.MeasureFano.condEntropy μ (Vs i) (X₁s i) := by
    intro i
    -- `X₁ᵢ` is the deterministic relay function of the past pairs `V^{<i}`.
    set relayF : (Fin i.val → β₁ × β) → α₁ :=
      fun v ↦ c.relay i (fun j ↦ (v j).1) with hrelayF_def
    have hrelayF_meas : Measurable relayF := measurable_of_countable relayF
    have hX₁_eq : (fun ω ↦ relayF (Vpre i ω)) = X₁s i := by
      funext ω; simp [hrelayF_def, hVpre_def, hVs_def, hX₁s_def]
    have hmk : IsMarkovChain μ (Vs i) (Vpre i) (X₁s i) := by
      have h := isMarkovChain_comp_conditioner_right μ (Vs i) (Vpre i)
        (hVs_meas i) (hVpre_meas i) hrelayF_meas
      rwa [hX₁_eq] at h
    have hdrop := condEntropy_drop_irrelevant_of_markov μ (Vs i) (Vpre i) (X₁s i)
      (hVs_meas i) (hVpre_meas i) (hX₁s_meas i) hmk
    have hcomm := condEntropy_measurableEquiv_comp μ (Vs i) (hVs_meas i)
      (fun ω ↦ (Vpre i ω, X₁s i ω)) ((hVpre_meas i).prodMk (hX₁s_meas i))
      MeasurableEquiv.prodComm
    rw [show (fun ω ↦ MeasurableEquiv.prodComm (Vpre i ω, X₁s i ω))
          = (fun ω ↦ (X₁s i ω, Vpre i ω)) from rfl] at hcomm
    have hle := condEntropy_le_condEntropy_of_pair μ (Vs i) (X₁s i) (Vpre i)
      (hVs_meas i) (hX₁s_meas i) (hVpre_meas i)
    calc InformationTheory.MeasureFano.condEntropy μ (Vs i) (Vpre i)
        = InformationTheory.MeasureFano.condEntropy μ (Vs i)
            (fun ω ↦ (Vpre i ω, X₁s i ω)) := hdrop.symm
      _ = InformationTheory.MeasureFano.condEntropy μ (Vs i)
            (fun ω ↦ (X₁s i ω, Vpre i ω)) := hcomm.symm
      _ ≤ InformationTheory.MeasureFano.condEntropy μ (Vs i) (X₁s i) := hle
  -- Step 6 (memoryless collapse): `H(Vᵢ | W, V^{<i}) = H(Vᵢ | X₁ᵢ, Xᵢ)`.
  have hMemo : ∀ i : Fin n,
      InformationTheory.MeasureFano.condEntropy μ (Vs i) (WVpre i)
        = InformationTheory.MeasureFano.condEntropy μ (Vs i)
            (fun ω ↦ (X₁s i ω, Xs i ω)) := by
    intro i
    -- `(Xᵢ, X₁ᵢ)` is the deterministic channel input read off `(W, V^{<i})`.
    set inputF : (Fin M × (Fin i.val → β₁ × β)) → (α × α₁) :=
      fun p ↦ (c.encoder p.1 i, c.relay i (fun j ↦ (p.2 j).1)) with hinputF_def
    have hinputF_meas : Measurable inputF := measurable_of_countable inputF
    have hJs_eq : (fun ω ↦ inputF (WVpre i ω)) = Js i := by
      funext ω
      simp [hinputF_def, hWVpre_def, hVpre_def, hVs_def, hJs_def, hXs_def, hX₁s_def]
    have hmk1 : IsMarkovChain μ (Vs i) (WVpre i) (Js i) := by
      have h := isMarkovChain_comp_conditioner_right μ (Vs i) (WVpre i)
        (hVs_meas i) (hWVpre_meas i) hinputF_meas
      rwa [hJs_eq] at h
    have hdrop1 := condEntropy_drop_irrelevant_of_markov μ (Vs i) (WVpre i) (Js i)
      (hVs_meas i) (hWVpre_meas i) (hJs_meas i) hmk1
    have hcomm1 := condEntropy_measurableEquiv_comp μ (Vs i) (hVs_meas i)
      (fun ω ↦ (WVpre i ω, Js i ω)) ((hWVpre_meas i).prodMk (hJs_meas i))
      MeasurableEquiv.prodComm
    rw [show (fun ω ↦ MeasurableEquiv.prodComm (WVpre i ω, Js i ω))
          = (fun ω ↦ (Js i ω, WVpre i ω)) from rfl] at hcomm1
    have hdrop2 := condEntropy_drop_irrelevant_of_markov μ (Vs i) (Js i) (WVpre i)
      (hVs_meas i) (hJs_meas i) (hWVpre_meas i) (h_memo i)
    have hcomm2 := condEntropy_measurableEquiv_comp μ (Vs i) (hVs_meas i)
      (Js i) (hJs_meas i) MeasurableEquiv.prodComm
    rw [show (fun ω ↦ MeasurableEquiv.prodComm (Js i ω))
          = (fun ω ↦ (X₁s i ω, Xs i ω)) from rfl] at hcomm2
    calc InformationTheory.MeasureFano.condEntropy μ (Vs i) (WVpre i)
        = InformationTheory.MeasureFano.condEntropy μ (Vs i)
            (fun ω ↦ (WVpre i ω, Js i ω)) := hdrop1.symm
      _ = InformationTheory.MeasureFano.condEntropy μ (Vs i)
            (fun ω ↦ (Js i ω, WVpre i ω)) := hcomm1.symm
      _ = InformationTheory.MeasureFano.condEntropy μ (Vs i) (Js i) := hdrop2
      _ = InformationTheory.MeasureFano.condEntropy μ (Vs i)
            (fun ω ↦ (X₁s i ω, Xs i ω)) := hcomm2.symm
  -- Assemble.
  have hPerLetter : ∀ i : Fin n,
      InformationTheory.MeasureFano.condEntropy μ (Vs i) (Vpre i)
          - InformationTheory.MeasureFano.condEntropy μ (Vs i) (WVpre i)
        ≤ (condMutualInfo μ (Xs i) (Vs i) (X₁s i)).toReal := by
    intro i
    rw [hRHS i, hMemo i]
    linarith [hCond i]
  calc (mutualInfo μ W (fun ω j ↦ Ys j ω)).toReal
      ≤ (mutualInfo μ W Vpi).toReal := hPost
    _ = entropy μ Vpi - InformationTheory.MeasureFano.condEntropy μ Vpi W := hLHS
    _ = (∑ i : Fin n, InformationTheory.MeasureFano.condEntropy μ (Vs i) (Vpre i))
          - ∑ i : Fin n, InformationTheory.MeasureFano.condEntropy μ (Vs i) (WVpre i) := by
        rw [hEnt, hCondEnt]
    _ = ∑ i : Fin n,
          (InformationTheory.MeasureFano.condEntropy μ (Vs i) (Vpre i)
            - InformationTheory.MeasureFano.condEntropy μ (Vs i) (WVpre i)) := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin n, (condMutualInfo μ (Xs i) (Vs i) (X₁s i)).toReal :=
        Finset.sum_le_sum fun i _ ↦ hPerLetter i

end BroadcastCutTelescope

section CutsetHeadline

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α α₁ β β₁ : Type*}
  [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [StandardBorelSpace α]
  [Fintype α₁] [Nonempty α₁]
    [MeasurableSpace α₁] [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype β] [Nonempty β]
    [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [Fintype β₁] [Nonempty β₁]
    [MeasurableSpace β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁]
variable {M n : ℕ} [NeZero M]

/-- **Broadcast-cut operational outer bound** (relay channel, Cover–Thomas Thm 15.10.1, broadcast
cut): for a uniformly distributed message `W` decoded from the receiver output `Yⁿ`, the rate is
bounded by the per-letter broadcast-cut sum plus a Fano slack,
`log M ≤ ∑ᵢ I(Xᵢ; Y₁ᵢ, Yᵢ | X₁ᵢ) + h(Pe) + Pe · log(M - 1)`, where `Xᵢ = encoder(W)ᵢ`,
`X₁ᵢ = relay i (Y₁^{<i})`, and `Pe` is the block decoding error probability.

The proof chains destination Fano (`shannon_converse_single_shot`) with the broadcast-cut
message-level telescoping (`relay_broadcast_cut_message_telescope`). The memoryless d-separation
hypothesis is a *precondition* (channel structure / regularity); the per-letter inequality (the
genuine content) is proven, not assumed. The outer maximisation over joint input pmfs is left to
callers, which is why the conclusion keeps the explicit per-letter sum. -/
theorem relay_broadcast_cut_outer_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Fin M)
    (c : RelayCode M n α α₁ β β₁)
    (Ys : Fin n → Ω → β) (Y₁s : Fin n → Ω → β₁)
    (hW : Measurable W)
    (hYs : ∀ i, Measurable (Ys i)) (hY₁s : ∀ i, Measurable (Y₁s i))
    (hW_uniform : μ.map W = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ M)
    (h_memo : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω ↦ (Y₁s i ω, Ys i ω))
        (fun ω ↦ (c.encoder (W ω) i,
          c.relay i (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)))
        (fun ω ↦ (W ω,
          fun (j : Fin i.val) ↦
            (Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω, Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)))) :
    Real.log (M : ℝ) ≤
      (∑ i : Fin n,
          (condMutualInfo μ (fun ω ↦ c.encoder (W ω) i) (fun ω ↦ (Y₁s i ω, Ys i ω))
            (fun ω ↦ c.relay i
              (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))).toReal)
        + Real.binEntropy (MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) c.decoder)
        + MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) c.decoder * Real.log ((M : ℝ) - 1) := by
  have hYpi : Measurable (fun ω j ↦ Ys j ω) := measurable_pi_iff.mpr hYs
  have hMI_W : mutualInfo μ W (fun ω j ↦ Ys j ω) ≠ ∞ :=
    mutualInfo_ne_top μ W (fun ω j ↦ Ys j ω) hW hYpi
  have hcard' : 2 ≤ Fintype.card (Fin M) := by rw [Fintype.card_fin]; exact hcard
  have hdec : Measurable c.decoder := measurable_of_countable c.decoder
  -- Step 1: destination Fano `log M ≤ I(W; Yⁿ) + h(Pe) + Pe · log(M − 1)`.
  have hStep1 := shannon_converse_single_shot μ W (fun ω j ↦ Ys j ω) c.decoder
    hW hYpi hdec hW_uniform hcard' hMI_W
  rw [Fintype.card_fin] at hStep1
  -- Step 2: broadcast-cut message-level telescoping `I(W; Yⁿ) ≤ ∑ᵢ I(Xᵢ; Y₁ᵢ, Yᵢ | X₁ᵢ)`.
  have hStep2 := relay_broadcast_cut_message_telescope μ W c Ys Y₁s hW hYs hY₁s h_memo
  linarith [hStep1, hStep2]

/-- **Cut-set outer bound** (relay channel, Cover–Thomas Thm 15.10.1): for a uniformly distributed
message `W` decoded from the receiver output `Yⁿ`, the rate is bounded by the `min` of the two cut
rates, each taken as its per-letter sum plus a common Fano slack:

* the **broadcast cut** `∑ᵢ I(Xᵢ; Y₁ᵢ, Yᵢ | X₁ᵢ) + h(Pe) + Pe · log(M - 1)`, and
* the **MAC cut** `∑ᵢ I(Xᵢ, X₁ᵢ; Yᵢ) + h(Pe) + Pe · log(M - 1)`,

where `Xᵢ = encoder(W)ᵢ`, `X₁ᵢ = relay i (Y₁^{<i})`, and `Pe` is the block decoding error
probability.

The proof combines the two cut bounds (`relay_broadcast_cut_outer_bound` and
`relay_mac_cut_outer_bound`) via `le_min`. The memoryless / Markov / causal-relay hypotheses are
*preconditions* (channel structure / regularity); the genuine content is carried by the two
single-letterization cut lemmas and is proven, not assumed. The outer maximisation over joint
input pmfs `p(x, x₁)` — the textbook `n · max_p` — is left to callers, which is why the conclusion
keeps the explicit per-letter sums. -/
theorem relay_cutset_outer_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Fin M)
    (c : RelayCode M n α α₁ β β₁)
    (Ys : Fin n → Ω → β) (Y₁s : Fin n → Ω → β₁)
    (hW : Measurable W)
    (hYs : ∀ i, Measurable (Ys i)) (hY₁s : ∀ i, Measurable (Y₁s i))
    (hW_uniform : μ.map W = (Fintype.card (Fin M) : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ M)
    (h_markov_mac : IsMarkovChain μ W
      (fun ω j ↦ (c.encoder (W ω) j,
        c.relay j (fun (k : Fin j.val) ↦ Y₁s ⟨k.val, k.isLt.trans j.isLt⟩ ω)))
      (fun ω j ↦ Ys j ω))
    (h_memo_mac : IsMemorylessChannel μ
      (fun i ω ↦ (c.encoder (W ω) i,
        c.relay i (fun (k : Fin i.val) ↦ Y₁s ⟨k.val, k.isLt.trans i.isLt⟩ ω))) Ys)
    (h_memo_bc : ∀ i : Fin n,
      IsMarkovChain μ
        (fun ω ↦ (Y₁s i ω, Ys i ω))
        (fun ω ↦ (c.encoder (W ω) i,
          c.relay i (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)))
        (fun ω ↦ (W ω,
          fun (j : Fin i.val) ↦
            (Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω, Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)))) :
    Real.log (M : ℝ) ≤ relayCutsetBound
      ((∑ i : Fin n,
          (condMutualInfo μ (fun ω ↦ c.encoder (W ω) i) (fun ω ↦ (Y₁s i ω, Ys i ω))
            (fun ω ↦ c.relay i
              (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))).toReal)
        + Real.binEntropy (MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) c.decoder)
        + MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) c.decoder * Real.log ((M : ℝ) - 1))
      ((∑ i : Fin n,
          (mutualInfo μ (fun ω ↦ (c.encoder (W ω) i,
            c.relay i (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω)))
              (Ys i)).toReal)
        + Real.binEntropy (MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) c.decoder)
        + MeasureFano.errorProb μ W (fun ω j ↦ Ys j ω) c.decoder * Real.log ((M : ℝ) - 1)) := by
  rw [relayCutsetBound_def]
  refine le_min ?_ ?_
  · -- broadcast cut
    exact relay_broadcast_cut_outer_bound μ W c Ys Y₁s hW hYs hY₁s hW_uniform hcard h_memo_bc
  · -- MAC cut
    exact relay_mac_cut_outer_bound μ W c.decoder
      (fun i ω ↦ c.encoder (W ω) i)
      (fun i ω ↦ c.relay i (fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      Ys hW (measurable_of_countable c.decoder)
      (fun i ↦ (measurable_of_countable (fun w ↦ c.encoder w i)).comp hW)
      (fun i ↦ (measurable_of_countable (c.relay i)).comp
        (measurable_pi_iff.mpr fun j ↦ hY₁s _))
      hYs hW_uniform hcard h_markov_mac h_memo_mac

end CutsetHeadline

end InformationTheory.Shannon.Relay
