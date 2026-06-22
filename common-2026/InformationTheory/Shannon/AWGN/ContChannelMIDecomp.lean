import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.ChannelCoding.MIDecomp
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.AWGN.MutualInfoDecomposition
import InformationTheory.Shannon.AWGN.BindConvolution
import InformationTheory.Shannon.AWGN.KLCapacityAndAEP
import InformationTheory.Shannon.AWGN.PerCodewordPowerConstraint
import InformationTheory.Shannon.AWGN.ConverseMIChainRule
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Continuous-channel mutual-information chain rule

This file applies the **continuous-channel MI chain rule**
`I(X;Y) = h(Y) − h(Y|X)` (`IsContChannelMIDecompHyp`) at the AWGN
channel, with `h(Y|X)` realized as the integral of fibrewise differential entropies.

The AWGN-independent generic core (the `InformationTheory.Shannon.ChannelCoding.*`
section: `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` and its helpers) lives
**upstream** in `InformationTheory/Shannon/ChannelCoding/MIDecomp.lean` (imported above),
so the AWGN converse chain (`AWGN.Converse`) can reuse it without an import cycle.

## Approach

The MI chain identity is **not AWGN-specific**: it holds for any Markov channel
`W : Channel ℝ ℝ` and input law `p`. Concretely it is a density-level identity
opened from the `klDiv` definition of `mutualInfoOfChannel`:

```
I = ∫_z llr (p⊗ₘW) (p.prod q) z ∂(p⊗ₘW)          -- toReal_klDiv_of_measure_eq
  = ∫_z [log f_{Wx}(z.2) − log f_q(z.2)] ∂(p⊗ₘW)  -- Bayes density split  (★)
  = ∫_x ∫_y log f_{Wx}(y) ∂(W x) ∂p               -- integral_compProd
      − ∫_y log f_q(y) ∂q                          -- snd marginal of (p⊗ₘW)
  = −∫_x h(W x) ∂p + h(Y).
```

The KL→integral expansion, the Fubini split (`integral_compProd`), the output
marginal identification (`outputDistribution = (p⊗ₘW).snd`) and the
differential-entropy density form (`differentialEntropy_eq_integral_density`) are
all proved here.

The single step **(★)** — the Bayes density split of the joint log-likelihood
ratio into fibre/output log densities — is the conditional-rnDeriv-to-fibre
identification `(p⊗ₘW).rnDeriv (p.prod q) (x,y) =ᵐ (W x).rnDeriv vol y / q.rnDeriv vol y`.
Mathlib's `rnDeriv_compProd` machinery stops at the *conditional* rnDeriv
`(μ⊗ₘκ).rnDeriv (μ⊗ₘη)` and provides **no** fibre identification
`= (κ a).rnDeriv (η a)`. This is supplied here by the linchpin
`rnDeriv_compProd_fibre` (withDensity route), assembled into the per-fibre split by
`llr_compProd_prod_split`. The body `mutualInfoOfChannel_toReal_eq_diffEntropy_sub`
discharges the entire klDiv→integral structure (`toReal_klDiv_of_measure_eq`), the Bayes
split, the Fubini decomposition (`integral_compProd` + `integral_sub`) and both
differential-entropy identifications (fibre + output, via
`integral_log_rnDeriv_eq_neg_diffEntropy`) explicitly.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-- **Each AWGN fibre is absolutely continuous w.r.t. the (Gaussian) output law.**
`gaussianReal x N ≪ volume ≪ gaussianReal 0 (P.toNNReal+N) = q`, both full-support
Gaussians. Used to discharge the joint absolute continuity `p⊗ₘW ≪ p.prod q` and the
Bayes density split. -/
theorem awgnChannel_apply_absolutelyContinuous_output
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (hPN : P.toNNReal + N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas) (x : ℝ) :
    (awgnChannel N h_meas) x
      ≪ InformationTheory.Shannon.ChannelCoding.outputDistribution
          (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas) := by
  rw [h_out, awgnChannel_apply]
  exact (gaussianReal_absolutelyContinuous x hN).trans
    (gaussianReal_absolutelyContinuous' 0 hPN)

/-- **2-variable (joint) measurability of the ℝ≥0∞ Gaussian pdf.**
The closed-form Gaussian pdf is everywhere jointly measurable in `(mean, point)`,
whereas the measure-form rnDeriv `fun z => (gaussianReal z.1 N).rnDeriv volume z.2`
is **not** (it is only a.e.-determined). This brick supplies the everywhere
joint measurability that the eq-set construction in `llr_compProd_prod_split`
requires. -/
theorem measurable_gaussianPDF_uncurry (N : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ ↦ gaussianPDF z.1 N z.2) := by
  simp only [gaussianPDF, gaussianPDFReal]
  fun_prop

/-- **2-variable (joint) measurability of the ℝ-valued Gaussian pdf.** Companion of
`measurable_gaussianPDF_uncurry`; used to supply the joint `AEStronglyMeasurable`
prerequisite when lifting the proxy log-density integrability to the compProd. -/
theorem measurable_gaussianPDFReal_uncurry (N : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ ↦ gaussianPDFReal z.1 N z.2) := by
  simp only [gaussianPDFReal]
  fun_prop

/-- **Second moment of a real Gaussian is integrable.** `(y − m)²` is integrable
against `gaussianReal m' v'` (any mean / variance), since `id ∈ L²(gaussianReal)`
(`memLp_id_gaussianReal`). Needed to discharge the Gaussian log-density
integrabilities (the log pdf is a constant plus a `(y − m)²` term). -/
theorem integrable_sq_sub_gaussianReal (m m' : ℝ) (v' : ℝ≥0) :
    Integrable (fun y ↦ (y - m) ^ 2) (gaussianReal m' v') := by
  -- `id ∈ L²` and `id ∈ L¹`, so `y², y, 1` are all integrable; expand `(y-m)²`.
  have h_sq : Integrable (fun y : ℝ ↦ y ^ 2) (gaussianReal m' v') :=
    (memLp_id_gaussianReal (μ := m') (v := v') 2).integrable_sq
  have h_id : Integrable (fun y : ℝ ↦ y) (gaussianReal m' v') := by
    have := (memLp_id_gaussianReal (μ := m') (v := v') 1).integrable (by norm_num)
    simpa using this
  have h_eq : (fun y : ℝ ↦ (y - m) ^ 2)
      = fun y ↦ y ^ 2 - 2 * m * y + m ^ 2 := by
    funext y; ring
  rw [h_eq]
  exact ((h_sq.sub (h_id.const_mul (2 * m))).add (integrable_const (m ^ 2)))

/-- **Log Gaussian density is integrable against a Gaussian law.** For `v ≠ 0`,
`fun y => Real.log (gaussianPDFReal m v y)` is integrable against `gaussianReal m' v'`.
The log pdf splits as `c₀ + c₁·(y − m)²`, a constant plus a finite-second-moment term. -/
theorem integrable_log_gaussianPDFReal_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (m' : ℝ) (v' : ℝ≥0) :
    Integrable (fun y ↦ Real.log (gaussianPDFReal m v y)) (gaussianReal m' v') := by
  -- `log (gaussianPDFReal m v y) = c₀ + c₁·(y − m)²`.
  have h_eq : (fun y ↦ Real.log (gaussianPDFReal m v y))
      = fun y ↦ (-(1/2) * Real.log (2 * Real.pi * v))
          + (-(1 / (2 * (v : ℝ)))) * (y - m) ^ 2 := by
    funext y
    rw [InformationTheory.Shannon.log_gaussianPDFReal_eq m hv y]
    ring
  rw [h_eq]
  exact (integrable_const _).add
    ((integrable_sq_sub_gaussianReal m m' v').const_mul (-(1 / (2 * (v : ℝ)))))

/-- **Log of the Gaussian rnDeriv (toReal) is integrable against the Gaussian law.**
For `v ≠ 0`, `fun y => Real.log ((gaussianReal m v).rnDeriv volume y).toReal` is
integrable against `gaussianReal m v`. Bridges the literal `Measure.rnDeriv` form
appearing in the honest hypotheses to `gaussianPDFReal` via the a.e. identity
`rnDeriv_gaussianReal`, then `integrable_log_gaussianPDFReal_gaussianReal`. -/
theorem integrable_log_rnDeriv_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun y ↦ Real.log ((gaussianReal m v).rnDeriv volume y).toReal)
      (gaussianReal m v) := by
  -- `rnDeriv =ᵐ[gaussianReal] gaussianPDF`, transported from vol via absolute continuity.
  have h_rn : (gaussianReal m v).rnDeriv volume =ᵐ[gaussianReal m v] gaussianPDF m v :=
    (gaussianReal_absolutelyContinuous m hv).ae_le (rnDeriv_gaussianReal m v)
  -- the log-density observables agree a.e. on `gaussianReal m v`
  have h_log :
      (fun y ↦ Real.log (gaussianPDFReal m v y))
        =ᵐ[gaussianReal m v]
      (fun y ↦ Real.log ((gaussianReal m v).rnDeriv volume y).toReal) := by
    filter_upwards [h_rn] with y hy
    rw [hy, toReal_gaussianPDF]
  exact (integrable_log_gaussianPDFReal_gaussianReal m hv m v).congr h_log

/-- **Second moment about the mean of a real Gaussian** (variance form). The mean of
`gaussianReal m N` is `m`, so `∫ y, (y − m)² ∂(gaussianReal m N) = N` by
`variance_fun_id_gaussianReal`. Used to make the per-fibre L¹-norm integral of the
joint log-density a *constant* in the input `x`, which discharges the third condition
of `Measure.integrable_compProd_iff`. -/
theorem integral_sq_sub_self_gaussianReal (m : ℝ) (N : ℝ≥0) :
    ∫ y, (y - m) ^ 2 ∂(gaussianReal m N) = (N : ℝ) := by
  have hvar := variance_fun_id_gaussianReal (μ := m) (v := N)
  rw [variance_eq_integral (by fun_prop)] at hvar
  simpa only [id_eq, integral_id_gaussianReal] using hvar

open InformationTheory.Shannon.ChannelCoding in
/-- **Proxy-form joint integrability of the AWGN fibre log-density.**
The fibre log-density, in measurable-proxy form
`fun z => Real.log (gaussianPDF z.1 N z.2).toReal`, is integrable against the joint
`p ⊗ₘ awgnChannel N`. Built via `Measure.integrable_compProd_iff`: joint
`AEStronglyMeasurable` from the brick `measurable_gaussianPDFReal_uncurry`, per-fibre
integrability from `integrable_log_gaussianPDFReal_gaussianReal`, and per-fibre L¹-norm
integrability via the constant-second-moment fact `integral_sq_sub_self_gaussianReal`
(the log pdf is `c₀ + c₁·(y−x)²`, whose norm-integral is bounded by `|c₀| + |c₁|·N`,
constant in `x`). -/
theorem integrable_log_proxy_fibre_compProd
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (h_meas : IsAwgnChannelMeasurable N) :
    Integrable
      (fun z : ℝ × ℝ ↦ Real.log (gaussianPDF z.1 N z.2).toReal)
      ((gaussianReal 0 P.toNNReal) ⊗ₘ (awgnChannel N h_meas)) := by
  set p := gaussianReal 0 P.toNNReal with hp_def
  set W := awgnChannel N h_meas with hW_def
  -- the joint integrand decomposes everywhere as `c₀ + c₁·(z.2 − z.1)²`
  set c₀ : ℝ := -(1 / 2) * Real.log (2 * Real.pi * N) with hc₀
  set c₁ : ℝ := -(1 / (2 * (N : ℝ))) with hc₁
  have h_eq : (fun z : ℝ × ℝ ↦ Real.log (gaussianPDF z.1 N z.2).toReal)
      = fun z ↦ c₀ + c₁ * (z.2 - z.1) ^ 2 := by
    funext z
    rw [toReal_gaussianPDF, InformationTheory.Shannon.log_gaussianPDFReal_eq z.1 hN z.2, hc₀, hc₁]
    ring
  rw [h_eq]
  -- the `(z.2 − z.1)²` term is integrable against the joint via compProd-iff
  have h_sq : Integrable (fun z : ℝ × ℝ ↦ (z.2 - z.1) ^ 2) (p ⊗ₘ W) := by
    have h_aesm : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ (z.2 - z.1) ^ 2) (p ⊗ₘ W) :=
      ((measurable_snd.sub measurable_fst).pow_const 2).aestronglyMeasurable
    rw [Measure.integrable_compProd_iff h_aesm]
    refine ⟨Filter.Eventually.of_forall (fun x ↦ ?_), ?_⟩
    · -- per-fibre `Integrable (fun y => (y − x)²) (W x = gaussianReal x N)`
      simpa only [hW_def, awgnChannel_apply] using integrable_sq_sub_gaussianReal x x N
    · -- per-fibre L¹-norm integral is the constant `N` (nonneg integrand, second moment)
      have h_norm : (fun x ↦ ∫ y, ‖(y - x) ^ 2‖ ∂(W x)) = fun _ ↦ (N : ℝ) := by
        funext x
        have : (fun y ↦ ‖(y - x) ^ 2‖) = fun y ↦ (y - x) ^ 2 := by
          funext y; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        rw [this, hW_def, awgnChannel_apply]
        exact integral_sq_sub_self_gaussianReal x N
      rw [h_norm]
      exact integrable_const _
  exact (integrable_const c₀).add (h_sq.const_mul c₁)

open InformationTheory.Shannon.ChannelCoding in
/-- **AWGN instance of `IsContChannelMIDecompHyp`.**

Applies the general body `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` at the AWGN
instance `p := gaussianReal 0 P.toNNReal`, `W := awgnChannel N h_meas`. From the inputs
`P, N, hN, hPN, h_meas, h_out` alone, all of the following are supplied:

* the fibre / output absolute continuities `hW_ac`, `hq_ac` (Gaussian facts);
* the **joint absolute continuity** `p⊗ₘW ≪ p.prod q`
  (`absolutelyContinuous_compProd_right_iff` + fibre-vs-output ac);
* the **Bayes density split** `h_llr_split` — from the general
  `llr_compProd_prod_split`, which rests on the **linchpin**
  `rnDeriv_compProd_fibre` (the fibre form of the compProd rnDeriv);
* the **fibre log-density integrability** and the **fibre joint measurability** — via the
  **measurable PDF proxy** `g := fun z => gaussianPDF z.1 N z.2`.

**Why the measurable PDF proxy.** The *measure-form* parameterized rnDeriv
`fun z => (gaussianReal z.1 N).rnDeriv volume z.2` has **no** everywhere joint
measurability (rnDeriv is a.e.-determined; `rnDeriv_gaussianReal` is `=ᵐ[volume]`, not
everywhere). Instead, the fibre density term is carried by the closed-form proxy `g`,
which **is** everywhere jointly measurable (`measurable_gaussianPDF_uncurry`). The
proxy↔rnDeriv bridge is the per-fibre a.e. agreement
`hg_ae x : (W x).rnDeriv vol =ᵐ[W x] g(x,·)` (from `rnDeriv_gaussianReal` lifted via
`gaussianReal_absolutelyContinuous`), consumed only *inside integrals* by
`llr_compProd_prod_split` and `integral_log_proxy_fibre` — never via a joint a.e.
`MeasurableSet`, which would be circular. The proxy-form joint integrability is
`integrable_log_proxy_fibre_compProd`. The two **output**-side log-density
integrabilities follow from the Gaussian density facts: `h_int_out_joint` (the integrand
depends only on `z.2`, so it is `g ∘ snd` with `(p ⊗ₘ W).snd = outputDistribution = q`)
reduces to `h_int_out_marg`, which is `integrable_log_rnDeriv_gaussianReal` at
`q = gaussianReal 0 (P + N)`. -/
theorem isContChannelMIDecompHyp_awgn
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (hPN : P.toNNReal + N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas) :
    IsContChannelMIDecompHyp
      (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas) := by
  classical
  set p := gaussianReal 0 P.toNNReal with hp_def
  set W := awgnChannel N h_meas with hW_def
  set q := outputDistribution p W with hq_def
  -- measurable PDF proxy `g := gaussianPDF` for the fibre volume-density
  set g : ℝ × ℝ → ℝ≥0∞ := fun z ↦ gaussianPDF z.1 N z.2 with hg_def
  have hg_meas : Measurable g := measurable_gaussianPDF_uncurry N
  -- per-fibre rnDeriv↔proxy bridge: `(W x).rnDeriv vol =ᵐ[W x] g(x, ·)`
  have hg_ae : ∀ x, (fun y ↦ (W x).rnDeriv volume y) =ᵐ[W x] fun y ↦ g (x, y) := by
    intro x
    rw [hW_def, awgnChannel_apply]
    exact (gaussianReal_absolutelyContinuous x hN).ae_le (rnDeriv_gaussianReal x N)
  -- output law is a probability measure (it is the Gaussian `gaussianReal 0 (P+N)`)
  have hq_prob : IsProbabilityMeasure q := by
    rw [hq_def, h_out]; infer_instance
  -- fibre-vs-output absolute continuity
  have hWx_q : ∀ x, W x ≪ q :=
    awgnChannel_apply_absolutelyContinuous_output P N hN hPN h_meas h_out
  -- output ≪ volume
  have hq_vol : q ≪ volume :=
    awgn_output_absolutelyContinuous_of_outputGaussian P N hPN h_meas h_out
  -- joint absolute continuity `p⊗ₘW ≪ p.prod q`
  have h_joint_ac : (p ⊗ₘ W) ≪ p.prod q := by
    rw [show p.prod q = p ⊗ₘ (Kernel.const ℝ q) from (Measure.compProd_const).symm]
    exact Measure.absolutelyContinuous_compProd_right_iff.mpr
      (Filter.Eventually.of_forall (fun x ↦ by simpa only [Kernel.const_apply] using hWx_q x))
  -- Bayes density split via the general linchpin-backed lemma (proxy form)
  have h_llr_split := llr_compProd_prod_split (p := p) (W := W) q hWx_q hq_vol
    h_joint_ac g hg_meas hg_ae
  -- fibre log-density integrability against the joint, in proxy form
  have h_int_fibre_joint :
      Integrable (fun z ↦ Real.log (g z).toReal) (p ⊗ₘ W) :=
    integrable_log_proxy_fibre_compProd P N hN h_meas
  -- output marginal log-density integrability (Gaussian fact, q = 𝒩(0, P+N))
  have h_int_out_marg :
      Integrable (fun y ↦ Real.log (q.rnDeriv volume y).toReal) q := by
    rw [hq_def, h_out]
    exact integrable_log_rnDeriv_gaussianReal 0 hPN
  -- joint output log-density integrability: integrand = (log-density ∘ snd),
  --    and `(p ⊗ₘ W).snd = outputDistribution p W = q`, so reduce to `h_int_out_marg`.
  have h_int_out_joint :
      Integrable (fun z ↦ Real.log (q.rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    have h_eq : q = (p ⊗ₘ W).map Prod.snd := rfl
    have hg_aesm :
        AEStronglyMeasurable (fun y ↦ Real.log (q.rnDeriv volume y).toReal) q :=
      h_int_out_marg.aestronglyMeasurable
    rw [show (fun z : ℝ × ℝ ↦ Real.log (q.rnDeriv volume z.2).toReal)
          = (fun y ↦ Real.log (q.rnDeriv volume y).toReal) ∘ Prod.snd from rfl]
    refine (integrable_map_measure ?_ measurable_snd.aemeasurable).mp ?_
    · rw [← h_eq]; exact hg_aesm
    · rw [← h_eq]; exact h_int_out_marg
  unfold IsContChannelMIDecompHyp
  -- All arguments of the generic body
  -- `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` come from the Gaussian facts built
  -- above: the three absolute continuities, the fibre-vs-output ac `hWx_q`, the
  -- measurable proxy `g` + its per-fibre a.e. bridge `hg_ae`, and the two log-density
  -- integrabilities (proxy fibre `h_int_fibre_joint`, output `h_int_out_joint`). The
  -- body itself supplies the KL→llr step, Bayes split, Fubini, and both fibre/output
  -- entropy identifications.
  exact mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    (W := W) (awgnChannel_apply_absolutelyContinuous N hN h_meas)
    hWx_q hq_vol h_joint_ac g hg_meas hg_ae h_int_fibre_joint h_int_out_joint

open InformationTheory.Shannon.ChannelCoding in
/-- **`IsAwgnMIDecomp` wrapper.**

Composes `isContChannelMIDecompHyp_awgn` with the combinator
`awgn_midecomp_of_cont_chain`. The MI-decomp predicate `IsAwgnMIDecomp` follows from the
inputs `P, N, hN, hPN, h_meas, h_out` alone — via the **linchpin**
`rnDeriv_compProd_fibre`, the general `llr_compProd_prod_split`, and the **measurable PDF
proxy** `g := gaussianPDF` (see `isContChannelMIDecompHyp_awgn`). The Bayes density
split, the joint absolute continuity, both fibre/output absolute continuities, the fibre
log-density integrability and the two output-side log-density integrabilities are all
supplied. Everything else in the MI chain rule (KL→integral, Fubini split, both
differential-entropy identifications, output marginal) comes from the general body. -/
theorem isAwgnMIDecomp_of_densitySplit
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (hPN : P.toNNReal + N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas) :
    IsAwgnMIDecomp P N h_meas :=
  awgn_midecomp_of_cont_chain P N h_meas
    (isContChannelMIDecompHyp_awgn P N hN hPN h_meas h_out)

/-- **Closed-form Gaussian MI from `h_out`.**

Same as `awgn_mi_gaussian_closed_form_of_primitives` but with the `h_decomp`
argument supplied internally: `IsAwgnMIDecomp` comes from
`isAwgnMIDecomp_of_densitySplit`, leaving `h_out` as the only standing hypothesis. -/
theorem awgn_mi_gaussian_closed_form_of_out
    (P : ℝ) (hP_pos : (0 : ℝ) < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas) :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  have hN_NN : N ≠ 0 :=
    fun h ↦ hN (by exact_mod_cast (congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) h))
  have hP_toNN_pos : (0 : ℝ≥0) < P.toNNReal := Real.toNNReal_pos.mpr hP_pos
  have hPN : P.toNNReal + N ≠ 0 :=
    (add_pos_of_pos_of_nonneg hP_toNN_pos (zero_le' (a := N))).ne'
  have h_decomp : IsAwgnMIDecomp P N h_meas :=
    isAwgnMIDecomp_of_densitySplit P N hN_NN hPN h_meas h_out
  exact awgn_mi_gaussian_closed_form_of_primitives P hP_pos N hN h_meas h_out h_decomp

/-! **AWGN capacity closed form** — hosted downstream.

This file cannot host the closed form `awgnCapacity P N = (1/2) log(1 + P/N)`, since the
converse depends on `AwgnCapacityConverseMaxent`, which imports this file; wiring it here
would create an import cycle. The closed form is therefore stated in its successor
`AwgnCapacityConverseMaxent.awgn_capacity_closed_form_genuine`. -/

end InformationTheory.Shannon.AWGN
