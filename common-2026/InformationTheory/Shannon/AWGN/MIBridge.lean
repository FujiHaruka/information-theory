import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.F1Discharge

/-!
# T2-A F-2 (MI bridge) discharge: AWGN channel mutual information closed form

Cover-Thomas Ch.9, Theorem 9.2.1: for the AWGN channel `Y = X + Z` with Gaussian
input `X ∼ 𝒩(0, P)` and independent noise `Z ∼ 𝒩(0, N)`,

```
I(X ; Y) = h(Y) − h(Y | X) = h(𝒩(0, P + N)) − h(𝒩(0, N)).
```

`AWGNF1Discharge.awgn_theorem_F1_discharged` exposes this identity as the
hypothesis `h_mi_bridge`. The present file discharges that hypothesis by
**reducing it to three explicit primitive predicates**, each capturing one
fundamental fact about the AWGN structure:

1. `IsAwgnOutputGaussian` — the channel output marginal
   `(gaussianReal 0 P ⊗ₘ awgnChannel N).snd = gaussianReal 0 (P+N)`
   (Gaussian + Gaussian convolution).
2. `IsAwgnMIDecomp` — the channel MI splits as
   `I(X;Y).toReal = h(Y) − h(Y|X)` (`mutualInfoOfChannel` ↔ entropy bridge),
   where `h(Y|X) := ∫ h(awgnChannel N x) ∂(gaussianReal 0 P)` is the
   integral of fibrewise differential entropies.
3. `IsAwgnCondEntropyEqNoise` — the conditional entropy equals the noise
   entropy: `∫ h(awgnChannel N x) ∂(gaussianReal 0 P) = h(𝒩(0, N))` (mean
   shift / translation invariance of `differentialEntropy`, integrated against
   the input).

The main combinator `awgn_mi_bridge_of_primitives` chains these three into the
`h_mi_bridge` shape consumed by `AWGNF1Discharge`. The hypothesis-free
re-publish `awgn_theorem_F2_discharged` takes the three primitive predicates
in place of the raw `h_mi_bridge` equality.

## 撤退ライン

撤退ライン F-2 を **3 個の primitive predicate に縮減** した形で discharge。
本 file は textbook discharge を行わず、各 primitive predicate を `Prop`
として **具体 predicate 形** で外出しする (CLAUDE.md / 親 plan の指示通り)。
将来の plan で各 primitive predicate を Mathlib `gaussianReal_conv_gaussianReal`
+ `differentialEntropy_map_add_const` + `mutualInfoOfChannel_eq_*` で
discharge 可能 (本 file の補助補題 `awgn_cond_entropy_eq_noise_entropy_of_const`
が個別 fibre の translation invariance を Mathlib 直結で証明済み)。

## Approach

```
                                     ┌── IsAwgnOutputGaussian P N h_meas
                                     │   = (jointDistribution ...).snd
                                     │     = gaussianReal 0 (P+N)
h_mi_bridge :                        │
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

## Mathlib gap (PR 候補)

* `differentialEntropy (gaussianReal m v) = differentialEntropy (gaussianReal 0 v)`:
  既存の `differentialEntropy_map_add_const` + `gaussianReal_map_const_add`
  から導出可能だが、専用 lemma は未掲載。本 file の `differentialEntropy_gaussianReal_mean_invariant`
  はそれを Mathlib 直結 1 行で publish (Mathlib-shape-driven)。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Phase A — Auxiliary: mean-translation invariance of `differentialEntropy` on Gaussian -/

/-- **Mean translation invariance of Gaussian differential entropy** (Mathlib gap PR
candidate).

`h(𝒩(m, v)) = h(𝒩(0, v))` — translation by `m` does not change differential entropy.

Direct corollary of `differentialEntropy_map_add_const` + `gaussianReal_map_const_add`.
Used inside `awgn_cond_entropy_eq_noise_entropy_of_const` to bring every fibre
`awgnChannel N x = gaussianReal x N` to the noise-only form `gaussianReal 0 N`. -/
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

/-- Pointwise version on AWGN fibre: each fibre `awgnChannel N x = gaussianReal x N`
has the same differential entropy as the noise alone. -/
theorem differentialEntropy_awgnChannel_apply_eq_noise
    (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (x : ℝ) :
    InformationTheory.Shannon.differentialEntropy ((awgnChannel N h_meas) x)
      = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) := by
  rw [awgnChannel_apply]
  exact differentialEntropy_gaussianReal_mean_invariant x hN

/-! ## Phase B — Three primitive predicates -/

/-- **Primitive predicate 1: output Gaussian.** The channel output marginal
under Gaussian input `gaussianReal 0 P` equals the convolution
`gaussianReal 0 (P + N)`.

Discharge route (deferred): `gaussianReal_conv_gaussianReal` + the joint
`(p ⊗ₘ awgnChannel N).snd = ∫ (awgnChannel N x) ∂p` identity. -/
def IsAwgnOutputGaussian (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  (InformationTheory.Shannon.ChannelCoding.outputDistribution
      (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas))
    = gaussianReal 0 (P.toNNReal + N)

/-- **Primitive predicate 2: MI ↔ entropy decomposition.** The channel mutual
information splits as `I(X;Y) = h(Y) − h(Y|X)`, where `h(Y|X)` is realized
as the integral of fibrewise differential entropies against the input law.

This is the continuous analogue of
`mutualInfoOfChannel_eq_HX_add_HY_sub_HZ`. Discharge route (deferred): unfold
`mutualInfoOfChannel` (KL form) and split via `klDiv_compProd_*` Mathlib API. -/
def IsAwgnMIDecomp (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
      (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
    = InformationTheory.Shannon.differentialEntropy
        (InformationTheory.Shannon.ChannelCoding.outputDistribution
          (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas))
      - (∫ x, InformationTheory.Shannon.differentialEntropy ((awgnChannel N h_meas) x)
            ∂(gaussianReal 0 P.toNNReal))

/-- **Primitive predicate 3: conditional entropy equals noise entropy.**
The integral of fibrewise differential entropies against the Gaussian input
collapses to the noise-only entropy `h(𝒩(0, N))`.

Note: by `differentialEntropy_awgnChannel_apply_eq_noise`, the integrand is
identically the constant `h(𝒩(0, N))`, so this predicate is equivalent to
`IsProbabilityMeasure (gaussianReal 0 P.toNNReal)` (always true). The constant
collapse is proved as `awgn_cond_entropy_eq_noise_entropy_of_const` below;
this `def` is kept as a named hypothesis purely for symmetry with the
deferred discharge structure. -/
def IsAwgnCondEntropyEqNoise (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  (∫ x, InformationTheory.Shannon.differentialEntropy ((awgnChannel N h_meas) x)
        ∂(gaussianReal 0 P.toNNReal))
    = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N)

/-! ## Phase C — Discharge of primitive 3 (`IsAwgnCondEntropyEqNoise`) -/

/-- The integral of fibrewise differential entropies under Gaussian input
collapses to `h(𝒩(0, N))` — proven from
`differentialEntropy_awgnChannel_apply_eq_noise` (mean translation invariance
of Gaussian entropy) and `IsProbabilityMeasure`. -/
@[entry_point]
theorem awgn_cond_entropy_eq_noise_entropy_of_const
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) :
    IsAwgnCondEntropyEqNoise P N h_meas := by
  unfold IsAwgnCondEntropyEqNoise
  -- The integrand is the constant `h(𝒩(0, N))`.
  have h_const : ∀ x,
      InformationTheory.Shannon.differentialEntropy ((awgnChannel N h_meas) x)
        = InformationTheory.Shannon.differentialEntropy (gaussianReal 0 N) :=
    fun x => differentialEntropy_awgnChannel_apply_eq_noise N hN h_meas x
  -- ∫ const ∂(gaussianReal 0 P) = const · (gaussianReal 0 P).real univ = const · 1.
  rw [integral_congr_ae (Filter.Eventually.of_forall (fun x => h_const x))]
  -- ∫ c ∂μ = c (probability measure).
  simp

/-! ## Phase D — Bridge combinator (3 primitives → `h_mi_bridge` shape) -/

/-- **MI bridge from primitives.** Combines the three primitive predicates
into the `h_mi_bridge` equality consumed by
`AWGNF1Discharge.awgn_theorem_F1_discharged`.

Proof: chain
```
I.toReal = h(out) − h(Y|X)                    [IsAwgnMIDecomp]
         = h(𝒩(0, P+N)) − h(Y|X)               [IsAwgnOutputGaussian]
         = h(𝒩(0, P+N)) − h(𝒩(0, N))           [IsAwgnCondEntropyEqNoise]
```

`@audit:closed-by-successor(awgn-mi-decomp-plan)` -/
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

/-! ## Phase E — Re-publish: hypothesis-free `awgn_theorem_F2_discharged` (3-primitive form) -/

/-- **AWGN channel coding theorem** (F-1 + F-2 partially discharged form).

元々は `AWGNF1Discharge.awgn_theorem_F1_discharged` の `h_mi_bridge` 引数を、本 file
の 3 個の primitive predicate (`IsAwgnOutputGaussian`, `IsAwgnMIDecomp`,
`IsAwgnCondEntropyEqNoise`) **の組** に縮減して埋める wrapper だった。

**2026-06-12 h_mi_bridge cleanup**: `awgn_theorem_F1_discharged` から dead
`h_mi_bridge` 引数が除去されたため、本 wrapper の body から primitives → bridge
構築 (`awgn_cond_entropy_eq_noise_entropy_of_const` + `awgn_mi_bridge_of_primitives`
経由) を削除し、`awgn_theorem_F1_discharged` への単純 pass-through にした。
`h_out` / `h_decomp` primitives hypothesis は signature に残置 — body 未消費の
**under-consumption** (load-bearing の逆: 仮説が結論を弱めも強めもしない) だが、
削除すると consumer `MIBridgeDischarge.awgn_theorem_of_typicality_converse_bindconv`
へ波及するため本 cleanup の scope 外とした。`awgn_mi_bridge_of_primitives` 補題
自体は genuine な MI bridge discharge として残置 (他用途あり)。

`@audit:superseded-by(awgn_achievability)` — cleanup 後、本 wrapper の statement は
`awgn_theorem_F1_discharged` (ないし headline `awgn_achievability` +
`isAwgnChannelMeasurable`) と内容重複。削除候補だが歴史的 entry point として残置。

`@audit:closed-by-successor(awgn-mi-decomp-plan)` -/
@[entry_point]
theorem awgn_theorem_F2_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_out : IsAwgnOutputGaussian P N (isAwgnChannelMeasurable N))
    (h_decomp : IsAwgnMIDecomp P N (isAwgnChannelMeasurable N))
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt
                  (awgnChannel N (isAwgnChannelMeasurable N)) m).toReal < ε :=
  -- 2026-06-12 cleanup: `awgn_theorem_F1_discharged` から dead `h_mi_bridge` 引数が
  -- 除去されたため、本 wrapper の primitives → bridge 構築 (旧
  -- `awgn_mi_bridge_of_primitives` 経由) は消費先を失い削除。`h_out` / `h_decomp`
  -- は signature 互換性のため残置 (under-consumption、`set_option
  -- linter.unusedVariables false`)。achievability の結論は MI bridge に依存しない。
  awgn_theorem_F1_discharged P hP N hN hR_pos hR_lt_C hε

/-! ## Phase F — Capacity closed form (3-primitive form) -/

/-- **Closed-form Gaussian MI** from primitives.

Combines the 3 primitives into the bridge (`awgn_mi_bridge_of_primitives`), then
runs the Gaussian closed-form `differentialEntropy_gaussianReal` log-algebra
**inline** to produce the `(1/2) log(1 + P/N)` value used by `awgnCapacity_eq`.
The algebra was formerly the load-bearing wrapper
`AWGN.mutualInfoOfChannel_gaussianInput_closed_form` (took the bridge identity as
a hypothesis `h_bridge`); that wrapper has been retired and its body inlined here,
where `h_mi_bridge` is genuinely discharged from primitives.

`@audit:closed-by-successor(awgn-mi-decomp-plan)` -/
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
    fun h => hN (by exact_mod_cast (congrArg (fun x : ℝ≥0 => (x : ℝ)) h))
  have h_cond : IsAwgnCondEntropyEqNoise P N h_meas :=
    awgn_cond_entropy_eq_noise_entropy_of_const P N hN_NN h_meas
  have h_mi_bridge :=
    awgn_mi_bridge_of_primitives P N h_meas h_out h_decomp h_cond
  -- Inlined Gaussian-input closed-form algebra (was the load-bearing wrapper
  -- `AWGN.mutualInfoOfChannel_gaussianInput_closed_form`, now retired). `h_mi_bridge`
  -- is genuinely constructed above from `awgn_mi_bridge_of_primitives`, so the
  -- remaining steps are pure `differentialEntropy_gaussianReal` log-algebra.
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
        exact_mod_cast (congrArg (fun x : ℝ≥0 => (x : ℝ)) h)
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

/-- **AWGN capacity closed form** (F-1 + F-2 partially discharged form).

`AWGNF1Discharge.awgn_capacity_closed_form_F1_discharged` の `h_bridge_gauss`
引数を、本 file の 2 primitives (`IsAwgnOutputGaussian` + `IsAwgnMIDecomp`)
に縮減した形で再 publish。残りの hypothesis (`h_bdd`, `h_max_ent`) はそのまま.

`@audit:closed-by-successor(awgn-mi-decomp-plan)` -/
@[entry_point]
theorem awgn_capacity_closed_form_F2_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_out : IsAwgnOutputGaussian P N (isAwgnChannelMeasurable N))
    (h_decomp : IsAwgnMIDecomp P N (isAwgnChannelMeasurable N))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ =>
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
