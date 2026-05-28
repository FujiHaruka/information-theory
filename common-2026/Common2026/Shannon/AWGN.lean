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

The hypothesis-free successor `mutualInfoOfChannel_gaussianInput_closed_form'`
lives in `AWGNMIClosedForm.lean` (takes no `h_bridge`). This `h_bridge`-form is
retained transitionally because its capacity consumer's genuine successor
(`awgn_capacity_closed_form_of_out`, `ContChannelMIDecomp.lean`) is still a `sorry`.

NOTE (honesty audit 2026-05-28): `h_bridge` here remains a **load-bearing
hypothesis** — it asserts the textbook identity `I.toReal = h(P+N) − h(N)` that
the theorem claims to derive, and the body merely `rw [h_bridge]` + Gaussian
log-algebra (axiom profile has no `sorryAx`: the substance lives entirely in the
hypothesis). `@audit:superseded-by` records the successor; the retract-candidate
marker records that this wrapper is itself not honest-complete (load-bearing hyp,
new-policy sorry-based migration pending) and is kept only for its active consumer
`awgn_mi_gaussian_closed_form_of_primitives` (`AWGNMIBridge.lean:281`).

`@audit:superseded-by(mutualInfoOfChannel_gaussianInput_closed_form')` @audit:retract-candidate(load-bearing-predicate) -/
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

/-! ## D.2 — `awgnPowerConstraintSet` + `awgnCapacity P N` -/

/-- Power constraint set: probability measures with a (genuine, lintegral) second
moment `≤ P`. Using the lower integral `∫⁻ x, ofReal (x²) ∂p ≤ ofReal P` instead of the
Bochner `∫ x, x² ∂p ≤ P` matters: Bochner `∫` returns `0` on a non-`p`-integrable
integrand (`MeasureTheory.integral_undef`), so the naive Bochner constraint would admit
heavy-tailed inputs (e.g. wide Cauchy laws) with infinite second moment via the spurious
`∫ x² ∂p = 0 ≤ P`, making the converse bound `(1/2)log(1+P/N)` false. The lintegral form
forces `∫⁻ ofReal(x²) < ∞`, hence genuine integrability of `x²`, ruling out those inputs.
`awgnPowerConstraintSet_mem_iff_integrable` bridges back to the Bochner moment + the
integrability regularity used by the converse phases. -/
def awgnPowerConstraintSet (P : ℝ) : Set (Measure ℝ) :=
  { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂p ≤ ENNReal.ofReal P }

/-- Membership in `awgnPowerConstraintSet P` (lintegral form) yields both the genuine
integrability of `x²` and the Bochner second-moment bound `∫ x² ∂p ≤ P`. This is the
bridge the converse phases (`AwgnCapacityConverseMaxent.lean`) consume: the lintegral
constraint carries the regularity (`Integrable (fun x => x²) p`) the Bochner form alone
cannot supply.

Independent honesty audit (2026-05-29): genuine (0 sorry). The four Mathlib lemmas
(`hasFiniteIntegral_iff_ofReal`, `ENNReal.ofReal_lt_top`, `ofReal_integral_eq_lintegral_ofReal`,
`ENNReal.ofReal_le_ofReal_iff`) are applied in the correct direction with their nonneg / 0≤P /
integrability side-conditions discharged genuinely (`sq_nonneg`, `hP`, `h_int`). The name says
`_iff` but the statement is the one-directional `mem → (integrable ∧ bound)`; not a honesty
defect, only mildly misleading (callers use it as `_of_mem`). @audit:ok -/
theorem awgnPowerConstraintSet_mem_iff_integrable
    (P : ℝ) (hP : 0 ≤ P) (p : Measure ℝ)
    (hp : p ∈ awgnPowerConstraintSet P) :
    Integrable (fun x => x ^ 2) p ∧ ∫ x, x ^ 2 ∂p ≤ P := by
  obtain ⟨hp_prob, hp_lint⟩ := hp
  have h_nonneg : 0 ≤ᵐ[p] fun x => x ^ 2 := Filter.Eventually.of_forall (fun x => sq_nonneg x)
  have h_meas_sq : AEStronglyMeasurable (fun x : ℝ => x ^ 2) p := by fun_prop
  -- finite lintegral ⇒ HasFiniteIntegral ⇒ Integrable
  have h_lt_top : (∫⁻ x, ENNReal.ofReal (x ^ 2) ∂p) < ∞ :=
    lt_of_le_of_lt hp_lint ENNReal.ofReal_lt_top
  have h_hfi : HasFiniteIntegral (fun x => x ^ 2) p :=
    (hasFiniteIntegral_iff_ofReal h_nonneg).mpr h_lt_top
  have h_int : Integrable (fun x => x ^ 2) p := ⟨h_meas_sq, h_hfi⟩
  refine ⟨h_int, ?_⟩
  -- Bochner bound: ofReal (∫ x²) = ∫⁻ ofReal (x²) ≤ ofReal P, then strip ofReal.
  have h_ofReal : ENNReal.ofReal (∫ x, x ^ 2 ∂p) = ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂p :=
    ofReal_integral_eq_lintegral_ofReal h_int h_nonneg
  have h_le : ENNReal.ofReal (∫ x, x ^ 2 ∂p) ≤ ENNReal.ofReal P := h_ofReal ▸ hp_lint
  exact (ENNReal.ofReal_le_ofReal_iff hP).mp h_le

/-- Power-constrained channel capacity. Supremum of `I(p; W)` over probability
measures `p` in `awgnPowerConstraintSet P` (second moment ≤ `P`, lintegral form). -/
noncomputable def awgnCapacity (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : ℝ :=
  sSup ((fun p : Measure ℝ =>
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N h_meas)).toReal) ''
        awgnPowerConstraintSet P)

/-- The Gaussian input `𝒩(0, P)` lies in the AWGN constraint set
`awgnPowerConstraintSet P`.

Independent honesty audit (2026-05-29): genuine (0 sorry) re-proof against the lintegral
constraint. `∫⁻ ofReal(x²) = ofReal(Var) = ofReal P ≤ ofReal P` via genuine `Integrable x²`
(`memLp_id_gaussianReal … .integrable_sq`) + variance identity; achievability side (`_ge_gaussian`)
is preserved — the Gaussian still feasible under the stricter set. @audit:ok -/
theorem gaussianInput_mem_constraintSet (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) :
    (gaussianReal 0 P.toNNReal) ∈ awgnPowerConstraintSet P := by
  refine ⟨inferInstance, ?_⟩
  -- ∫ x² ∂(gaussianReal 0 P.toNNReal) = Var = P, so ∫⁻ ofReal(x²) = ofReal P ≤ ofReal P.
  have h_var : (Var[fun x : ℝ => x; gaussianReal 0 P.toNNReal] : ℝ) = (P.toNNReal : ℝ) :=
    by rw [variance_fun_id_gaussianReal]
  have h_var_eq :
      (∫ x, (x - (0 : ℝ))^2 ∂(gaussianReal 0 P.toNNReal))
        = (Var[fun x : ℝ => x; gaussianReal 0 P.toNNReal] : ℝ) := by
    rw [variance_eq_integral measurable_id'.aemeasurable]
    congr 1
    rw [integral_id_gaussianReal]
  have h_int_val : ∫ x, x^2 ∂(gaussianReal 0 P.toNNReal) = (P.toNNReal : ℝ) := by
    have h1 : ∫ x, x^2 ∂(gaussianReal 0 P.toNNReal)
        = ∫ x, (x - (0 : ℝ))^2 ∂(gaussianReal 0 P.toNNReal) := by
      simp
    rw [h1, h_var_eq, h_var]
  -- x² is integrable against the Gaussian (MemLp 2).
  have h_int : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 P.toNNReal) :=
    (memLp_id_gaussianReal (μ := 0) (v := P.toNNReal) 2).integrable_sq
  have h_nonneg : 0 ≤ᵐ[gaussianReal 0 P.toNNReal] fun x => x ^ 2 :=
    Filter.Eventually.of_forall (fun x => sq_nonneg x)
  have h_lint :
      ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(gaussianReal 0 P.toNNReal)
        = ENNReal.ofReal (P.toNNReal : ℝ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal h_int h_nonneg, h_int_val]
  rw [h_lint]
  exact ENNReal.ofReal_le_ofReal (by rw [Real.coe_toNNReal P hP])

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
          awgnPowerConstraintSet P)) :
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
        ∀ p ∈ awgnPowerConstraintSet P,
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
          awgnPowerConstraintSet P))
    (h_max_ent :
        ∀ p ∈ awgnPowerConstraintSet P,
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N h_meas)).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N h_meas = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  apply le_antisymm
  · exact awgnCapacity_le_gaussian P hP N hN h_meas h_max_ent
  · exact awgnCapacity_ge_gaussian P hP N hN h_meas h_bridge_gauss h_bdd

end InformationTheory.Shannon.AWGN
