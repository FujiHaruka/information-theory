import Common2026.Meta.EntryPoint
import Common2026.Shannon.AWGNMIBridgeDischarge

/-!
# W9-G1 T2-A AWGN MI bridge: body discharge of `IsAwgnMIDecomp`

Wave6 `Common2026/Shannon/AWGNMIBridge.lean` reduced the AWGN MI bridge
(Cover-Thomas 9.2.1, `I(X;Y) = h(Y) − h(Y|X)`) to three primitive predicates.
Wave7 `AWGNMIBridgeDischarge.lean` body-discharged `IsAwgnOutputGaussian`
(via the bind/conv bridge) and `IsAwgnCondEntropyEqNoise` is already fully
discharged inside `AWGNMIBridge.lean`. The remaining opaque predicate is

```
IsAwgnMIDecomp P N h_meas
  := (mutualInfoOfChannel (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
       = differentialEntropy (outputDistribution …)
         − ∫ x, differentialEntropy ((awgnChannel N h_meas) x) ∂(gaussianReal 0 P.toNNReal)
```

i.e. the **continuous-channel mutual-information chain rule**
`I(X;Y) = h(Y) − h(Y|X)`, with `h(Y|X)` realized as the integral of fibrewise
differential entropies.

## Approach

The MI chain identity `I = h(Y) − h(Y|X)` is **not AWGN-specific**: it holds for
any Markov channel `W : ℝ → Measure ℝ` and input law `p` whose joint, output and
fibre laws are absolutely continuous w.r.t. Lebesgue volume (so all differential
entropies are densities-based). Concretely it is a density-level identity:

```
I = ∫∫ W(y|x) log(W(y|x)/q(y)) dy dp(x)
  = ∫∫ W(y|x) log W(y|x) dy dp(x) − ∫ q(y) log q(y) dy
  = −h(Y|X) + h(Y).
```

The KL→density expansion (`klDiv` ⇒ `∫ llr`) plus the Bayes split
`rnDeriv (p⊗ₘW) (p.prod q) = (W(y|x)/q(y))` is exactly the Mathlib
`klDiv_compProd_eq_add` chain-rule machinery applied at the *density* level,
together with the differential-entropy definition. That continuous chain rule is
**not in Mathlib** (the discrete analogue
`mutualInfo_eq_entropy_add_entropy_sub_jointEntropy` exists; the continuous
density version does not). Discharging it inside this file would require
~200-300 lines of rnDeriv / Fubini / integrability bookkeeping with no reusable
Mathlib lemma to lean on.

This file therefore performs an **honest vertical sub-decomposition**:

1. **Phase A — AWGN absolute-continuity facts (fully discharged).** Each AWGN
   fibre `W x = gaussianReal x N` and (given the output-Gaussian fact) the
   output marginal are `≪ volume`. These are exactly the side conditions any
   future discharge of the abstract chain rule will consume; we discharge them
   here directly from Mathlib `gaussianReal_absolutelyContinuous`.
2. **Phase B — Abstract continuous MI chain predicate (deferred).**
   `IsContChannelMIDecompHyp p W` is the *AWGN-independent* continuous-channel MI
   chain rule. It is strictly more primitive and more reusable than the opaque
   `IsAwgnMIDecomp`: it makes no reference to Gaussians.
3. **Phase C — Combinator (fully discharged).** At the AWGN instance
   `p := gaussianReal 0 P.toNNReal`, `W := awgnChannel N h_meas`, the abstract
   predicate is definitionally the AWGN predicate, so
   `awgn_midecomp_of_cont_chain` discharges `IsAwgnMIDecomp` from
   `IsContChannelMIDecompHyp` by an `exact`.
4. **Phase D — Re-publish.** `awgn_theorem_of_typicality_converse_midecomp_discharged`
   and the capacity form re-expose the wave7 theorems with the `IsAwgnMIDecomp`
   hypothesis replaced by the smaller, AWGN-independent `IsContChannelMIDecompHyp`
   (⚠️ still OPEN; typicality/converse also remain OPEN hypotheses).

## 撤退ライン

撤退ライン T2-A `IsAwgnMIDecomp` を **AWGN 非依存の連続版 MI chain rule
predicate `IsContChannelMIDecompHyp`** に縮減する形で discharge。AWGN 固有の
absolute-continuity 側条件 (各 fibre / output が `≪ volume`) は Phase A で
Mathlib `gaussianReal_absolutelyContinuous` 直結で完全 discharge 済み。残る
abstract chain rule のみ named hypothesis として後続 plan
(`awgn-mi-decomp-plan.md`) に defer。これは density-level の klDiv 展開を要し、
Mathlib 不在 (連続版 chain rule)。`Prop := True` placeholder で水増しせず、
honest pass-through で止める。

## Mathlib gap (PR 候補)

* `mutualInfoOfChannel_eq_diffEntropy_sub_condDiffEntropy`: continuous-channel
  analogue of `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy`. Requires
  `klDiv_compProd_eq_add` at density level + `differentialEntropy` unfold +
  Bayes rnDeriv split. Not in Mathlib; this is the body of
  `IsContChannelMIDecompHyp`.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — AWGN absolute-continuity facts -/

/-- **Each AWGN fibre is absolutely continuous w.r.t. Lebesgue volume.**
`W x = gaussianReal x N ≪ volume` for `N ≠ 0`. Direct from Mathlib
`gaussianReal_absolutelyContinuous`. This is one of the side conditions the
continuous MI chain rule consumes (every fibre must have a density). -/
@[entry_point]
theorem awgnChannel_apply_absolutelyContinuous
    (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (x : ℝ) :
    (awgnChannel N h_meas) x ≪ volume := by
  rw [awgnChannel_apply]
  exact gaussianReal_absolutelyContinuous x hN

/-- **Output marginal is absolutely continuous w.r.t. Lebesgue volume**, given
the output-Gaussian fact `IsAwgnOutputGaussian` (discharged by
`AWGNMIBridgeDischarge.awgn_output_gaussian_of_bind_eq_conv`). The output is then
`gaussianReal 0 (P.toNNReal + N) ≪ volume`. -/
@[entry_point]
theorem awgn_output_absolutelyContinuous_of_outputGaussian
    (P : ℝ) (N : ℝ≥0) (hPN : P.toNNReal + N ≠ 0) (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas) :
    (InformationTheory.Shannon.ChannelCoding.outputDistribution
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)) ≪ volume := by
  rw [h_out]
  exact gaussianReal_absolutelyContinuous 0 hPN

/-! ## Phase B — Abstract continuous-channel MI chain rule predicate -/

/-- **Continuous-channel mutual-information chain rule** (named hypothesis,
AWGN-independent).

For an input law `p` on `ℝ` and a Markov channel `W : Channel ℝ ℝ`, the channel
mutual information splits as the difference of differential entropies

```
(mutualInfoOfChannel p W).toReal
  = differentialEntropy (outputDistribution p W)
    − ∫ x, differentialEntropy (W x) ∂p
```

i.e. `I(X;Y) = h(Y) − h(Y|X)`. This is the continuous (density-based) analogue of
the discrete `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy`. It is a generic
measure-theoretic fact requiring the joint / output / fibre laws to be `≪ volume`
(so the differential entropies are density integrals) plus the relevant
integrability; it makes **no reference to the AWGN / Gaussian structure**.

Discharging the body requires the density-level klDiv expansion
(`klDiv_compProd_eq_add` + Bayes rnDeriv split + `differentialEntropy` unfold),
which is not in Mathlib. We expose it as a single named hypothesis (strictly more
primitive and reusable than the AWGN-specific `IsAwgnMIDecomp`), to be discharged
in the follow-up `awgn-mi-decomp-plan.md`. -/
def IsContChannelMIDecompHyp
    (p : Measure ℝ) (W : InformationTheory.Shannon.ChannelCoding.Channel ℝ ℝ) : Prop :=
  (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel p W).toReal
    = Common2026.Shannon.differentialEntropy
        (InformationTheory.Shannon.ChannelCoding.outputDistribution p W)
      - (∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p)

/-! ## Phase C — Combinator: abstract chain rule → `IsAwgnMIDecomp` -/

/-- **`IsAwgnMIDecomp` from the abstract continuous MI chain rule.**

At the AWGN instance `p := gaussianReal 0 P.toNNReal`, `W := awgnChannel N h_meas`,
the abstract predicate `IsContChannelMIDecompHyp` is *definitionally* the AWGN
predicate `IsAwgnMIDecomp` (both unfold to the same `mutualInfoOfChannel … =
differentialEntropy (outputDistribution …) − ∫ …`). The discharge is therefore an
`exact`.

`@audit:closed-by-successor(awgn-mi-decomp-plan)`
(The successor predicate `IsContChannelMIDecompHyp` above is discharged
hypothesis-free in `ContChannelMIDecomp.lean` (`isContChannelMIDecompHyp_awgn`),
whose generic body `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` now delegates the
sole density-level wall to the shared sorry lemma
`AwgnWalls.contChannelMIDecomp_holds` (`@residual(wall:awgn-mi-decomp)`). This
wrapper is a pure `unfold + exact` shim and not itself a load-bearing claim.) -/
@[entry_point]
theorem awgn_midecomp_of_cont_chain
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (h_chain : IsContChannelMIDecompHyp
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)) :
    IsAwgnMIDecomp P N h_meas := by
  unfold IsAwgnMIDecomp
  unfold IsContChannelMIDecompHyp at h_chain
  exact h_chain

/-- The reverse direction also holds definitionally — the AWGN predicate is just
the abstract chain rule at the AWGN instance. Confirms the two predicates carry
identical content (no information lost in the abstraction). -/
@[entry_point]
theorem cont_chain_of_awgn_midecomp
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (h_decomp : IsAwgnMIDecomp P N h_meas) :
    IsContChannelMIDecompHyp
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas) := by
  unfold IsContChannelMIDecompHyp
  unfold IsAwgnMIDecomp at h_decomp
  exact h_decomp

end InformationTheory.Shannon.AWGN
