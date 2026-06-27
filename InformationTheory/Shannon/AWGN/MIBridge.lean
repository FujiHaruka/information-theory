import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.ChannelMeasurability

/-!
# AWGN channel mutual information closed form

For the AWGN channel `Y = X + Z` with Gaussian input `X ∼ 𝒩(0, P)` and independent
noise `Z ∼ 𝒩(0, N)`, the channel mutual information has the closed form

```
I(X ; Y) = h(Y) − h(Y | X) = h(𝒩(0, P + N)) − h(𝒩(0, N)).
```

This identity is reduced to three explicit primitive predicates, each capturing one
fundamental fact about the AWGN structure:

1. `IsAwgnOutputGaussian` — the channel output marginal
   `(gaussianReal 0 P ⊗ₘ awgnChannel N).snd = gaussianReal 0 (P+N)`
   (Gaussian + Gaussian convolution).
2. `IsAwgnMIDecomp` — the channel MI splits as
   `I(X;Y).toReal = h(Y) − h(Y|X)` (`mutualInfoOfChannel` ↔ entropy bridge),
   where `h(Y|X) := ∫ h(awgnChannel N x) ∂(gaussianReal 0 P)` is the
   integral of fibrewise differential entropies.
3. `IsAwgnCondEntropyEqNoise` — the conditional entropy equals the noise
   entropy: `∫ h(awgnChannel N x) ∂(gaussianReal 0 P) = h(𝒩(0, N))` (translation
   invariance of `differentialEntropy`, integrated against the input).

The combinator `awgn_mi_bridge_of_primitives` chains these three into the closed-form
mutual-information identity.

## Main definitions

* `IsAwgnOutputGaussian`, `IsAwgnMIDecomp`, `IsAwgnCondEntropyEqNoise` — the three
  primitive predicates described above.

## Main statements

* `differentialEntropy_gaussianReal_mean_invariant` — `h(𝒩(m, v)) = h(𝒩(0, v))`.
* `awgn_cond_entropy_eq_noise_entropy_of_const` — discharge of
  `IsAwgnCondEntropyEqNoise`.
* `awgn_mi_bridge_of_primitives` — the closed-form mutual information from the three
  primitives.
* `awgn_mi_gaussian_closed_form_of_primitives` — the `(1/2) log(1 + P/N)` value of the
  Gaussian-input mutual information.
* `awgn_capacity_closed_form_F2_discharged` — the AWGN capacity closed form with the
  Gaussian MI fact reduced to two primitives.

## Approach

```
                                     ┌── IsAwgnOutputGaussian P N h_meas
                                     │   = (jointDistribution ...).snd
                                     │     = gaussianReal 0 (P+N)
mutual-information identity:         │
  I(X;Y).toReal                      ├── IsAwgnMIDecomp P N h_meas
  = h(N(0,P+N)) − h(N(0,N))   ◀────  │   = I(X;Y).toReal
                                     │     = h(output) − h(Y|X)
                                     │
                                     └── IsAwgnCondEntropyEqNoise P N h_meas
                                         = h(Y|X) = h(N(0,N))
```

Pipeline (proof body of `awgn_mi_bridge_of_primitives`):
```
I.toReal = h(out) − h(Y|X)                 -- IsAwgnMIDecomp
         = h(gaussianReal 0 (P+N)) − h(Y|X) -- IsAwgnOutputGaussian (rewrites out)
         = h(gaussianReal 0 (P+N)) − h(N)   -- IsAwgnCondEntropyEqNoise
```

## Implementation notes

The mean-translation invariance of Gaussian differential entropy,
`differentialEntropy (gaussianReal m v) = differentialEntropy (gaussianReal 0 v)`,
follows from `differentialEntropy_map_add_const` and `gaussianReal_map_const_add`; it
is published here as `differentialEntropy_gaussianReal_mean_invariant` and brings every
channel fibre to the noise-only form.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-- Mean translation invariance of Gaussian differential entropy:
`h(𝒩(m, v)) = h(𝒩(0, v))`. -/
theorem differentialEntropy_gaussianReal_mean_invariant
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    InformationTheory.Shannon.differentialEntropy (gaussianReal m v)
      = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 v) := by
  have h1 : InformationTheory.Shannon.differentialEntropy (gaussianReal m v)
      = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * v) :=
    InformationTheory.Shannon.differentialEntropy_gaussianReal m hv
  have h2 : InformationTheory.Shannon.differentialEntropy (gaussianReal 0 v)
      = (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * v) :=
    InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hv
  rw [h1, h2]

/-- Each AWGN channel fibre has the same differential entropy as the noise alone:
`h(awgnChannel N x) = h(𝒩(0, N))`. -/
theorem differentialEntropy_awgnChannel_apply_eq_noise
    (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (x : ℝ) :
    InformationTheory.Shannon.differentialEntropy ((awgnChannel N h_meas) x)
      = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  rw [awgnChannel_apply]
  exact differentialEntropy_gaussianReal_mean_invariant x hN

/-! ## Three primitive predicates -/

/-- The channel output marginal under Gaussian input `gaussianReal 0 P` equals the
convolution `gaussianReal 0 (P + N)`. -/
def IsAwgnOutputGaussian (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  (InformationTheory.Shannon.ChannelCoding.outputDistribution
      (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas))
    = gaussianReal 0 (P.toNNReal + N)

/-- The channel mutual information splits as `I(X;Y) = h(Y) − h(Y|X)`, where `h(Y|X)`
is the integral of fibrewise differential entropies against the input law. This is the
continuous analogue of `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ`. -/
def IsAwgnMIDecomp (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
      (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
    = InformationTheory.Shannon.differentialEntropy
        (InformationTheory.Shannon.ChannelCoding.outputDistribution
          (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas))
      - (∫ x, InformationTheory.Shannon.differentialEntropy ((awgnChannel N h_meas) x)
            ∂(gaussianReal 0 P.toNNReal))

/-- The integral of fibrewise differential entropies against the Gaussian input
collapses to the noise-only entropy `h(𝒩(0, N))`.

By `differentialEntropy_awgnChannel_apply_eq_noise` the integrand is identically the
constant `h(𝒩(0, N))`, so this predicate holds for any probability-measure input; it
is kept as a named primitive for symmetry with the other two. -/
def IsAwgnCondEntropyEqNoise (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  (∫ x, InformationTheory.Shannon.differentialEntropy ((awgnChannel N h_meas) x)
        ∂(gaussianReal 0 P.toNNReal))
    = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N)

/-- The integral of fibrewise differential entropies under Gaussian input collapses to
`h(𝒩(0, N))`, discharging `IsAwgnCondEntropyEqNoise`. -/
@[entry_point]
theorem awgn_cond_entropy_eq_noise_entropy_of_const
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) :
    IsAwgnCondEntropyEqNoise P N h_meas := by
  unfold IsAwgnCondEntropyEqNoise
  -- The integrand is the constant `h(𝒩(0, N))`.
  have h_const : ∀ x,
      InformationTheory.Shannon.differentialEntropy ((awgnChannel N h_meas) x)
        = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) :=
    fun x ↦ differentialEntropy_awgnChannel_apply_eq_noise N hN h_meas x
  -- ∫ const ∂(gaussianReal 0 P) = const · (gaussianReal 0 P).real univ = const · 1.
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ h_const x))]
  -- ∫ c ∂μ = c (probability measure).
  simp

/-- The closed-form AWGN channel mutual information
`I(X;Y).toReal = h(𝒩(0, P+N)) − h(𝒩(0, N))`, obtained by chaining the three
primitive predicates:
```
I.toReal = h(out) − h(Y|X)                    [IsAwgnMIDecomp]
         = h(𝒩(0, P+N)) − h(Y|X)               [IsAwgnOutputGaussian]
         = h(𝒩(0, P+N)) − h(𝒩(0, N))           [IsAwgnCondEntropyEqNoise]
```
-/
@[entry_point]
theorem awgn_mi_bridge_of_primitives
    (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas)
    (h_decomp : IsAwgnMIDecomp P N h_meas)
    (h_cond : IsAwgnCondEntropyEqNoise P N h_meas) :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
      = InformationTheory.Shannon.differentialEntropy
            (gaussianReal 0 (P.toNNReal + N))
        - InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  -- Step 1: MI decomposition.
  rw [h_decomp]
  -- Step 2: rewrite output marginal via primitive 1.
  rw [h_out]
  -- Step 3: collapse conditional entropy via primitive 3.
  rw [h_cond]

/-- The Gaussian-input AWGN channel mutual information equals `(1/2) log(1 + P/N)`,
obtained by combining the three primitives into `awgn_mi_bridge_of_primitives` and
running the Gaussian closed-form `differentialEntropy_gaussianReal` log algebra inline. -/
@[entry_point]
theorem awgn_mi_gaussian_closed_form_of_primitives
    (P : ℝ) (hP_pos : (0 : ℝ) < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas)
    (h_decomp : IsAwgnMIDecomp P N h_meas) :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  have hN_NN : N ≠ 0 :=
    fun h ↦ hN (by exact_mod_cast (congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) h))
  have h_cond : IsAwgnCondEntropyEqNoise P N h_meas :=
    awgn_cond_entropy_eq_noise_entropy_of_const P N hN_NN h_meas
  have h_mi_bridge :=
    awgn_mi_bridge_of_primitives P N h_meas h_out h_decomp h_cond
  -- The remaining steps are pure `differentialEntropy_gaussianReal` log algebra.
  -- `(P.toNNReal : ℝ) = P` from positivity.
  have hP_toNN : ((P.toNNReal : ℝ≥0) : ℝ) = P := Real.coe_toNNReal P hP_pos.le
  -- Step 1: rewrite MI as h(P+N) - h(N) via the bridge identity.
  rw [h_mi_bridge]
  -- Step 2: discharge both entropies via `differentialEntropy_gaussianReal`.
  have hPN_NN : P.toNNReal + N ≠ 0 := by
    intro h
    have hP0 : (P.toNNReal : ℝ) = 0 := by
      have hPnn : (0 : ℝ) ≤ (P.toNNReal : ℝ≥0) := (P.toNNReal).coe_nonneg
      have hNnn : (0 : ℝ) ≤ N := N.coe_nonneg
      have hsum : ((P.toNNReal : ℝ≥0) : ℝ) + N = 0 := by
        exact_mod_cast (congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) h)
      linarith
    rw [hP_toNN] at hP0
    exact hP_pos.ne' hP0
  rw [InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hPN_NN,
      InformationTheory.Shannon.differentialEntropy_gaussianReal 0 hN_NN]
  -- Step 3: pure log algebra: (1/2)[log(2πe(P+N)) - log(2πeN)] = (1/2) log((P+N)/N)
  --                          = (1/2) log(1 + P/N).
  have hN_pos : (0 : ℝ) < N := by
    have : (N : ℝ) ≥ 0 := N.coe_nonneg
    exact lt_of_le_of_ne this (Ne.symm hN)
  have hPN_pos : (0 : ℝ) < P + (N : ℝ) := by linarith [N.coe_nonneg]
  have hPN_coe : ((P.toNNReal + N : ℝ≥0) : ℝ) = P + (N : ℝ) := by
    push_cast [hP_toNN]; ring
  have h_2pe : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by positivity
  have h_log_diff :
      (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * ((P.toNNReal + N : ℝ≥0) : ℝ))
        - (1/2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (N : ℝ))
      = (1/2) * Real.log ((P + N) / (N : ℝ)) := by
    rw [hPN_coe]
    have h_num : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (P + N) := mul_pos h_2pe hPN_pos
    have h_den : (0 : ℝ) < 2 * Real.pi * Real.exp 1 * (N : ℝ) := mul_pos h_2pe hN_pos
    rw [← mul_sub]
    congr 1
    rw [← Real.log_div h_num.ne' h_den.ne']
    congr 1
    field_simp
  rw [h_log_diff]
  -- ((P + N)/N) = 1 + P/N
  congr 1
  rw [show (P + N) / (N : ℝ) = 1 + P / (N : ℝ) by field_simp; ring]

/-- The AWGN capacity closed form, re-published with the Gaussian mutual-information
fact reduced to the two primitives `IsAwgnOutputGaussian` and `IsAwgnMIDecomp`. The
remaining hypotheses (`h_bdd`, `h_max_ent`) are unchanged.

`@audit:superseded-by(awgn_capacity_closed_form_genuine)` -/
@[entry_point]
theorem awgn_capacity_closed_form_F2_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_out : IsAwgnOutputGaussian P N (isAwgnChannelMeasurable N))
    (h_decomp : IsAwgnMIDecomp P N (isAwgnChannelMeasurable N))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ ↦
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N (isAwgnChannelMeasurable N))).toReal) ''
          awgnPowerConstraintSet P))
    (h_max_ent :
        ∀ p ∈ awgnPowerConstraintSet P,
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N (isAwgnChannelMeasurable N))).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N (isAwgnChannelMeasurable N)
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  have h_bridge_gauss :=
    awgn_mi_gaussian_closed_form_of_primitives P hP N hN
      (isAwgnChannelMeasurable N) h_out h_decomp
  exact awgn_capacity_closed_form_F1_discharged P hP.le N hN
    h_bridge_gauss h_bdd h_max_ent

end InformationTheory.Shannon.AWGN
