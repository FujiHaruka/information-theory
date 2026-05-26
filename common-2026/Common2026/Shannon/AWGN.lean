import Common2026.Meta.EntryPoint
import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.DifferentialEntropy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# T2-A: AWGN channel capacity `C = (1/2) log(1 + P/N)`

Cover-Thomas Ch.9. The continuous specialization of the Shannon noisy-channel
coding theorem to the additive white Gaussian noise channel.

## Roadmap (per `docs/shannon/awgn-moonshot-plan.md`)

* Phase A (this file) — `awgnChannel` kernel + `AwgnCode` bundle + MI closed-form
  bridge + `awgnCapacity` definition + closed form `= (1/2) log(1+P/N)`.
* Phase B (`AWGNAchievability.lean`) — Achievability under hypothesis F-1
  (continuous joint-typicality pass-through).
* Phase C (`AWGNConverse.lean`) — Converse under hypothesis F-3 (per-letter
  integrability pass-through).
* Phase D (this file, end) — Main theorem `awgn_channel_coding_theorem`
  (achievability + converse + closed-form sandwich).

## 撤退ライン (本 file で発動)

* **F-2 (MI bridge)**: `mutualInfoOfChannel (gaussianReal 0 P) (awgnChannel N)
  = h(Y) - h(Z)` の bridge は hypothesis として外出し
  (`mutualInfoOfChannel_gaussianInput_closed_form` の `h_bridge` 引数)。
* **F-1 / F-3**: 主定理 `awgn_channel_coding_theorem` の signature で
  `IsAwgnTypicalityHypothesis` / `IsAwgnConverseIntegrableHyp` を pass-through。
* **F-4 (kernel measurability)**: `awgnChannel` の `measurable'` field —
  `Measurable (fun x : ℝ => gaussianReal x N)` — は本 plan のスコープ外として
  外部 hypothesis `h_awgn_measurable` 経由で構成 (`mkAwgnChannel`)。直接構成
  (~50-100 行、`measurable_gaussianPDF` + Fubini) は後続 plan
  `awgn-kernel-measurability-plan.md` に defer。判断ログ #1 で確定。

## Mathlib-shape-driven Definitions

* `awgnChannel N : Channel ℝ ℝ` は `toFun x := gaussianReal x N` で直接定義
  (`gaussianReal_conv_gaussianReal` (`m₁+m₂, v₁+v₂`) の結論形に直結)。
* `awgnCapacity P N : ℝ` は `sSup` 直書き
  (`Common2026/Shannon/ChannelCodingShannonTheorem.lean` の `stdSimplex` 形は
  `Fintype α` 想定で AWGN 不適用)。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## D.1 — `awgnChannel : Channel ℝ ℝ`

撤退ライン F-4 採用: `Measurable (fun x : ℝ => gaussianReal x N)` を hypothesis
引数として外出し。直接構成 (`measurable_gaussianPDF` + Fubini, ~50-100 行) は
別 plan に defer。 -/

/-- The AWGN measurability hypothesis: `(fun x : ℝ => gaussianReal x N)` is
measurable as a map `ℝ → Measure ℝ`. Discharging this is deferred to a follow-up
plan `awgn-kernel-measurability-plan.md` (see `docs/shannon/awgn-moonshot-plan.md`
撤退ライン F-4 / 判断ログ #1). -/
def IsAwgnChannelMeasurable (N : ℝ≥0) : Prop :=
  Measurable (fun x : ℝ => gaussianReal x N)

/-- AWGN channel kernel: on input `x : ℝ`, output `Y = x + Z` where `Z ∼ 𝒩(0, N)`.
The kernel returns the law of `Y` directly as `gaussianReal x N` (mean shifted to `x`,
variance = noise power `N`).

撤退ライン F-4 hypothesis pass-through: requires `IsAwgnChannelMeasurable N`
to construct the kernel (Mathlib API for `m`-measurability of `gaussianReal m v`
is not yet in the inventory; see plan §危険 4). -/
noncomputable def awgnChannel (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) :
    InformationTheory.Shannon.ChannelCoding.Channel ℝ ℝ where
  toFun x := gaussianReal x N
  measurable' := h_meas

@[simp] lemma awgnChannel_apply (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) (x : ℝ) :
    (awgnChannel N h_meas) x = gaussianReal x N := rfl

/-- `awgnChannel N` is a Markov kernel (each fibre is a probability measure). -/
instance awgnChannel.instIsMarkovKernel (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) :
    IsMarkovKernel (awgnChannel N h_meas) where
  isProbabilityMeasure x := by
    show IsProbabilityMeasure (gaussianReal x N)
    infer_instance

/-! ## D.6 — `AwgnCode` (Code + power constraint + decoder measurability) -/

/-- Block code with a power constraint and a measurable decoder, specialized to
input/output alphabet `ℝ`. Adds the two fields missing from `Code M n ℝ ℝ`:

* `decoder_meas` — required because `MeasurableSingletonClass (Fin n → ℝ)` fails
  for continuous output alphabet (every singleton has Lebesgue measure 0).
* `power_constraint` — the output-power constraint
  `(1/n) ∑ (encoder m i)² ≤ P` for every message `m`. -/
structure AwgnCode (M n : ℕ) (P : ℝ) where
  encoder : Fin M → (Fin n → ℝ)
  decoder : (Fin n → ℝ) → Fin M
  decoder_meas : Measurable decoder
  power_constraint : ∀ m : Fin M,
    (∑ i : Fin n, (encoder m i)^2) ≤ (n : ℝ) * P

/-- Forget the power constraint and decoder measurability to get a bare `Code`. -/
noncomputable def AwgnCode.toCode {M n : ℕ} {P : ℝ} (c : AwgnCode M n P) :
    InformationTheory.Shannon.ChannelCoding.Code M n ℝ ℝ where
  encoder := c.encoder
  decoder := c.decoder

/-! ## D.3 — `mutualInfo` closed form for Gaussian-input AWGN (F-2 hypothesis form) -/

/-- (撤退ライン F-2 hypothesis form) Closed form of the channel mutual information
for the AWGN channel with Gaussian input. We require the textbook identity
`I = h(Y) - h(Z)` as a hypothesis `h_bridge` (here `Y ∼ 𝒩(0, P+N)`,
`Z ∼ 𝒩(0, N)`); from there the right-hand side reduces to `(1/2) log(1+P/N)` by
pure `differentialEntropy_gaussianReal` algebra.

Discharging `h_bridge` (= "`mutualInfoOfChannel` (KL form) = `h(Y) - h(Y|X)`"
for AWGN) is deferred to the follow-up plan
`docs/shannon/awgn-mi-bridge-plan.md`.

`@audit:closed-by-successor(awgn-mi-bridge-plan)` -/
@[entry_point]
theorem mutualInfoOfChannel_gaussianInput_closed_form
    (P N : ℝ≥0) (hP : (P : ℝ) ≠ 0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_bridge :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P) (awgnChannel N h_meas)).toReal
          = Common2026.Shannon.differentialEntropy (gaussianReal 0 (P + N))
              - Common2026.Shannon.differentialEntropy (gaussianReal 0 N)) :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
        (gaussianReal 0 P) (awgnChannel N h_meas)).toReal
      = (1/2) * Real.log (1 + (P : ℝ) / (N : ℝ)) := by
  -- Step 1: rewrite MI as h(P+N) - h(N) via the bridge hypothesis.
  rw [h_bridge]
  -- Step 2: discharge both entropies via `differentialEntropy_gaussianReal`.
  have hPN_NN : P + N ≠ 0 := by
    intro h
    have hP0 : (P : ℝ) = 0 := by
      have hPnn : (0 : ℝ) ≤ P := P.coe_nonneg
      have hNnn : (0 : ℝ) ≤ N := N.coe_nonneg
      have hsum : (P : ℝ) + N = 0 := by exact_mod_cast (congrArg (fun x : ℝ≥0 => (x : ℝ)) h)
      linarith
    exact hP hP0
  have hN_NN : N ≠ 0 := fun h => hN (by exact_mod_cast (congrArg (fun x : ℝ≥0 => (x : ℝ)) h))
  rw [Common2026.Shannon.differentialEntropy_gaussianReal 0 hPN_NN,
      Common2026.Shannon.differentialEntropy_gaussianReal 0 hN_NN]
  -- Step 3: pure log algebra: (1/2)[log(2πe(P+N)) - log(2πeN)] = (1/2) log((P+N)/N)
  --                          = (1/2) log(1 + P/N).
  have hN_pos : (0 : ℝ) < N := by
    have : (N : ℝ) ≥ 0 := N.coe_nonneg
    exact lt_of_le_of_ne this (Ne.symm hN)
  have hP_pos : (0 : ℝ) < P := by
    have : (P : ℝ) ≥ 0 := P.coe_nonneg
    exact lt_of_le_of_ne this (Ne.symm hP)
  have hPN_pos : (0 : ℝ) < (P : ℝ) + (N : ℝ) := by linarith
  have hPN_coe : ((P + N : ℝ≥0) : ℝ) = (P : ℝ) + (N : ℝ) := by push_cast; ring
  have h2πe : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  -- (1/2) log(2πe(P+N)) - (1/2) log(2πeN) = (1/2) log((2πe(P+N))/(2πeN)) = (1/2) log((P+N)/N)
  have h_log_diff :
      (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((P + N : ℝ≥0) : ℝ))
        - (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ))
      = (1/2) * Real.log (((P : ℝ) + N) / (N : ℝ)) := by
    rw [hPN_coe]
    have h_num : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * ((P : ℝ) + N) := by positivity
    have h_den : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (N : ℝ) := by positivity
    rw [← mul_sub]
    congr 1
    rw [← Real.log_div h_num.ne' h_den.ne']
    congr 1
    field_simp
  rw [h_log_diff]
  -- ((P + N)/N) = 1 + P/N
  congr 1
  rw [show ((P : ℝ) + N) / (N : ℝ) = 1 + (P : ℝ) / (N : ℝ) by field_simp; ring]

/-! ## D.2 — `awgnCapacity P N` -/

/-- Power-constrained channel capacity. Supremum of `I(p; W)` over probability
measures `p` with second moment ≤ `P`. -/
noncomputable def awgnCapacity (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : ℝ :=
  sSup ((fun p : Measure ℝ =>
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N h_meas)).toReal) ''
        { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P })

/-- The Gaussian input `𝒩(0, P)` lies in the AWGN constraint set
`{p | IsProbabilityMeasure p ∧ ∫ x², ≤ P}`. -/
theorem gaussianInput_mem_constraintSet (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) :
    (gaussianReal 0 P.toNNReal) ∈
      { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P } := by
  refine ⟨inferInstance, ?_⟩
  -- ∫ x² ∂(gaussianReal 0 P.toNNReal) = Var = P
  have h_var : (Var[fun x : ℝ => x; gaussianReal 0 P.toNNReal] : ℝ) = (P.toNNReal : ℝ) :=
    by rw [variance_fun_id_gaussianReal]
  have h_var_eq :
      (∫ x, (x - (0 : ℝ))^2 ∂(gaussianReal 0 P.toNNReal))
        = (Var[fun x : ℝ => x; gaussianReal 0 P.toNNReal] : ℝ) := by
    rw [variance_eq_integral measurable_id'.aemeasurable]
    congr 1
    rw [integral_id_gaussianReal]
  have h_int : ∫ x, x^2 ∂(gaussianReal 0 P.toNNReal) = (P.toNNReal : ℝ) := by
    have h1 : ∫ x, x^2 ∂(gaussianReal 0 P.toNNReal)
        = ∫ x, (x - (0 : ℝ))^2 ∂(gaussianReal 0 P.toNNReal) := by
      simp
    rw [h1, h_var_eq, h_var]
  rw [h_int, Real.coe_toNNReal P hP]

/-- The AWGN capacity is bounded below by `(1/2) log(1 + P/N)` — achieved by the
Gaussian input, using the F-2 hypothesis form of the closed-form MI.

`@audit:closed-by-successor(awgn-moonshot-plan)` -/
@[entry_point]
theorem awgnCapacity_ge_gaussian
    (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_bridge_gauss :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
          = (1/2) * Real.log (1 + P / (N : ℝ)))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ =>
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N h_meas)).toReal) ''
          { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P })) :
    (1/2) * Real.log (1 + P / (N : ℝ)) ≤ awgnCapacity P N h_meas := by
  -- The Gaussian input is feasible (mem_constraintSet) and achieves the bound.
  have h_mem := gaussianInput_mem_constraintSet P hP N
  unfold awgnCapacity
  refine h_bridge_gauss ▸ le_csSup h_bdd ?_
  exact ⟨gaussianReal 0 P.toNNReal, h_mem, rfl⟩

/-- The AWGN capacity is bounded above by `(1/2) log(1 + P/N)` — every input
satisfying the second-moment constraint gives MI ≤ `(1/2) log(1+P/N)` via the
Gaussian max-entropy bound. Pass-through via hypothesis `h_max_ent`.

`@audit:closed-by-successor(awgn-moonshot-plan)` -/
@[entry_point]
theorem awgnCapacity_le_gaussian
    (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_max_ent :
        ∀ p ∈ { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P },
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N h_meas)).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N h_meas ≤ (1/2) * Real.log (1 + P / (N : ℝ)) := by
  unfold awgnCapacity
  -- Standard sSup-upper-bound argument: every image element is ≤ the target.
  refine csSup_le ?_ ?_
  · -- Image is nonempty: the Gaussian input is in the constraint set.
    refine ⟨_, gaussianReal 0 P.toNNReal, gaussianInput_mem_constraintSet P hP N, rfl⟩
  · rintro y ⟨p, hp_mem, rfl⟩
    exact h_max_ent p hp_mem

/-- **AWGN capacity closed form** (Cover-Thomas 9.1). Sandwich: the supremum over
power-constrained inputs equals `(1/2) log(1 + P/N)`.

`h_bridge_gauss`, `h_max_ent`, `h_bdd` are the F-2 撤退ライン hypotheses; their
discharge is deferred to follow-up plans.

`@audit:closed-by-successor(awgn-moonshot-plan)` -/
@[entry_point]
theorem awgnCapacity_eq
    (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_bridge_gauss :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
          = (1/2) * Real.log (1 + P / (N : ℝ)))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ =>
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N h_meas)).toReal) ''
          { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P }))
    (h_max_ent :
        ∀ p ∈ { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P },
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N h_meas)).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N h_meas = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  apply le_antisymm
  · exact awgnCapacity_le_gaussian P hP N hN h_meas h_max_ent
  · exact awgnCapacity_ge_gaussian P hP N hN h_meas h_bridge_gauss h_bdd

end InformationTheory.Shannon.AWGN
