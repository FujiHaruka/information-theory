import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Continuous-channel mutual-information chain rule (generic body)

[awgn-mi-decomp-plan.md](../../../docs/shannon/awgn-mi-decomp-plan.md).

This file genuinely discharges the **continuous-channel MI chain rule**
`I(X;Y) = h(Y) − h(Y|X)`, with `h(Y|X)` realized as the integral of fibrewise
differential entropies. The identity is **not AWGN-specific**: it holds for any
Markov channel `W : Channel ℝ ℝ` and input law `p`.

This is the AWGN-independent generic core, relocated here (2026-06-11) from
`InformationTheory/Draft/Shannon/ContChannelMIDecomp.lean` so that it lives
**upstream** of the AWGN converse chain (`AWGN.Converse`), breaking the import cycle
that previously prevented the per-letter MI bridge
(`awgn_per_letter_mi_bridge_genuine`) from reusing it. The original file imports this
one and re-exports these declarations under their unchanged fully-qualified names
(`InformationTheory.Shannon.ChannelCoding.*`), so downstream consumers (ParallelGaussian,
AwgnCapacityConverseMaxent) are unaffected.

## Approach

The MI chain identity is a density-level identity opened from the `klDiv` definition
of `mutualInfoOfChannel`:

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
all genuinely discharged here. The single step **(★)** — the Bayes density split of
the joint log-likelihood ratio into fibre/output log densities — is the
conditional-rnDeriv-to-fibre identification supplied **genuinely** by the linchpin
`rnDeriv_compProd_fibre` (withDensity route), assembled by `llr_compProd_prod_split`.
The body `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` is **fully genuine (0 sorry,
no shared wall)**.
-/

namespace InformationTheory.Shannon.ChannelCoding

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

variable {p : Measure ℝ} [IsProbabilityMeasure p]
variable {W : Channel ℝ ℝ} [IsMarkovKernel W]

/-- **Marginal identification (genuine).** For a bounded-density observable
`g : ℝ → ℝ`, the joint integral of `g ∘ snd` against `p ⊗ₘ W` equals the integral
of `g` against the output marginal `outputDistribution p W = (p ⊗ₘ W).snd`. -/
theorem integral_snd_outputDistribution
    (g : ℝ → ℝ) (hg : Integrable g (outputDistribution p W)) :
    ∫ z, g z.2 ∂(p ⊗ₘ W) = ∫ y, g y ∂(outputDistribution p W) := by
  have h_eq : outputDistribution p W = (p ⊗ₘ W).map Prod.snd := rfl
  have hg' : AEStronglyMeasurable g ((p ⊗ₘ W).map Prod.snd) := by
    rw [← h_eq]; exact hg.aestronglyMeasurable
  rw [h_eq, MeasureTheory.integral_map measurable_snd.aemeasurable hg']

/-- **General log-density entropy identification (genuine).** For any `μ : Measure ℝ`
with `μ ≪ volume` and measurable density `f := μ.rnDeriv volume`, the integral of
`log f` against `μ` is `−differentialEntropy μ`. This is the generalization of
`integral_log_density_fibre` to an arbitrary `≪ volume` measure (the proof never used
that `μ` was a channel fibre); it is reused for both the fibre term (`μ := W x`) and
the output term (`μ := outputDistribution p W`) in the assembly below.
@audit:ok -/
theorem integral_log_rnDeriv_eq_neg_diffEntropy
    (μ : Measure ℝ) [SigmaFinite μ] (hμ : μ ≪ volume) :
    ∫ y, Real.log (μ.rnDeriv volume y).toReal ∂μ
      = -InformationTheory.Shannon.differentialEntropy μ := by
  set f : ℝ → ℝ≥0∞ := μ.rnDeriv volume with hf_def
  have hf_meas : Measurable f := Measure.measurable_rnDeriv _ _
  have hf_lt_top : ∀ᵐ y ∂(volume : Measure ℝ), f y < ∞ := Measure.rnDeriv_lt_top _ _
  have h_wd : μ = volume.withDensity f := (Measure.withDensity_rnDeriv_eq _ _ hμ).symm
  -- rewrite the LHS integral against `μ` as an integral against `volume`
  calc ∫ y, Real.log (f y).toReal ∂μ
      = ∫ y, Real.log (f y).toReal ∂(volume.withDensity f) := by rw [h_wd]
    _ = ∫ y, (f y).toReal • Real.log (f y).toReal ∂volume :=
        integral_withDensity_eq_integral_toReal_smul hf_meas hf_lt_top _
    _ = ∫ y, (f y).toReal * Real.log (f y).toReal ∂volume := by
        simp only [smul_eq_mul]
    _ = -InformationTheory.Shannon.differentialEntropy μ := by
        unfold InformationTheory.Shannon.differentialEntropy
        rw [← integral_neg]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        rw [Real.negMulLog_def]
        ring

/-- **Fibre differential-entropy identification (genuine).** For an `≪ volume`
fibre `W x` with measurable density `f := (W x).rnDeriv volume`, the inner integral
of `log f` against `W x` is `−differentialEntropy (W x)`. Thin wrapper around the
general `integral_log_rnDeriv_eq_neg_diffEntropy`. -/
theorem integral_log_density_fibre
    (x : ℝ) (hWx : W x ≪ volume) :
    ∫ y, Real.log ((W x).rnDeriv volume y).toReal ∂(W x)
      = -InformationTheory.Shannon.differentialEntropy (W x) :=
  integral_log_rnDeriv_eq_neg_diffEntropy (W x) hWx

/-- **Proxy form of the fibre differential-entropy identification** (Route B).
Same conclusion as `integral_log_density_fibre`, but stated with a measurable
PDF proxy `g` in place of the (non-jointly-measurable) measure-form rnDeriv.
The proxy↔rnDeriv bridge is absorbed *inside the integral* via `integral_congr_ae`
fed by the per-fibre a.e. agreement `hg_ae`, so no joint measurability is ever
needed. This is the step that lets the body keep its fibre term in proxy form. -/
theorem integral_log_proxy_fibre
    (x : ℝ) (hWx : W x ≪ volume) {g : ℝ × ℝ → ℝ≥0∞}
    (hg_ae : (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y)) :
    ∫ y, Real.log (g (x, y)).toReal ∂(W x)
      = -InformationTheory.Shannon.differentialEntropy (W x) := by
  rw [← integral_log_density_fibre x hWx]
  refine integral_congr_ae ?_
  filter_upwards [hg_ae] with y hy
  rw [hy]

/-- **Linchpin: fibre form of the compProd Radon-Nikodym derivative** (Mathlib TODO,
`Composition/RadonNikodym.lean:28-29`). For finite `μ, κ, η` with `μ ⊗ₘ κ ≪ μ ⊗ₘ η`,
the conditional rnDeriv `∂(μ⊗ₘκ)/∂(μ⊗ₘη)` is `(μ⊗ₘη)`-a.e. the fibrewise kernel
rnDeriv `Kernel.rnDeriv κ η p.1 p.2`.

Proof (withDensity route): `μ⊗ₘκ ≪ μ⊗ₘη` gives `κ a ≪ η a` a.e. (`kernel_of_compProd`),
so `κ =ᵐ[μ] η.withDensity (κ.rnDeriv η)` (`withDensity_rnDeriv_eq`); hence
`μ⊗ₘκ = μ⊗ₘ(η.withDensity (κ.rnDeriv η)) = (μ⊗ₘη).withDensity (fun p ↦ κ.rnDeriv η p.1 p.2)`
(`compProd_congr` + `compProd_withDensity`); finish with `Measure.rnDeriv_withDensity`. -/
theorem rnDeriv_compProd_fibre
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {μ : Measure α} {κ η : Kernel α β}
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)
      =ᵐ[μ ⊗ₘ η] fun p => Kernel.rnDeriv κ η p.1 p.2 := by
  -- fibrewise absolute continuity from the joint one
  have h_ac_fibre : ∀ᵐ a ∂μ, κ a ≪ η a := h_ac.kernel_of_compProd
  -- the measurable density `g p := Kernel.rnDeriv κ η p.1 p.2`
  have hg_meas : Measurable (Function.uncurry (Kernel.rnDeriv κ η)) :=
    Kernel.measurable_rnDeriv κ η
  -- `κ =ᵐ[μ] η.withDensity (κ.rnDeriv η)`
  have hκ_eq : κ =ᵐ[μ] η.withDensity (Kernel.rnDeriv κ η) := by
    filter_upwards [h_ac_fibre] with a ha using (Kernel.withDensity_rnDeriv_eq ha).symm
  -- transport to compProd, then to a withDensity of the joint measure
  have h_cp : μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity (fun p => Kernel.rnDeriv κ η p.1 p.2) := by
    rw [Measure.compProd_congr hκ_eq, Measure.compProd_withDensity hg_meas]
  -- finish: rnDeriv of a withDensity is the density
  rw [h_cp]
  exact Measure.rnDeriv_withDensity (μ ⊗ₘ η) (by fun_prop)

/-- **Per-measure log-density split** (Bayes step, genuine). For `ν ≪ q ≪ volume`
all `σ`-finite, the log of the relative density `dν/dq` splits as the difference of
the two `volume`-log-densities:
`log (dν/dq y) = log (dν/dvol y) − log (dq/dvol y)`, `ν`-a.e. Built from the rnDeriv
chain rule `dν/dq · dq/dvol =ᵐ dν/dvol` plus positivity (`q ≪ vol` ⇒ `dq/dvol > 0`
on `ν` since `ν ≪ q`). -/
theorem log_rnDeriv_split
    {ν q : Measure ℝ} [SigmaFinite ν] [SigmaFinite q]
    (hνq : ν ≪ q) (hq_vol : q ≪ volume) :
    (fun y => Real.log ((ν.rnDeriv q y).toReal))
      =ᵐ[ν]
    (fun y => Real.log ((ν.rnDeriv volume y).toReal)
                - Real.log ((q.rnDeriv volume y).toReal)) := by
  -- chain rule  dν/dq · dq/dvol =ᵐ[q] dν/dvol, transported to ν
  have h_chain : (fun y => ν.rnDeriv q y * q.rnDeriv volume y)
      =ᵐ[ν] ν.rnDeriv volume :=
    hνq.ae_le (Measure.rnDeriv_mul_rnDeriv' (μ := ν) (ν := q) (κ := volume) hq_vol)
  -- positivity / finiteness of both factors, ν-a.e.
  have h_pos_νq : ∀ᵐ y ∂ν, 0 < ν.rnDeriv q y := Measure.rnDeriv_pos hνq
  have h_lt_νq : ∀ᵐ y ∂ν, ν.rnDeriv q y < ∞ := hνq.ae_le (Measure.rnDeriv_lt_top ν q)
  have h_pos_q : ∀ᵐ y ∂ν, 0 < q.rnDeriv volume y := hνq.ae_le (Measure.rnDeriv_pos hq_vol)
  have h_lt_q : ∀ᵐ y ∂ν, q.rnDeriv volume y < ∞ :=
    hνq.ae_le (hq_vol.ae_le (Measure.rnDeriv_lt_top q volume))
  filter_upwards [h_chain, h_pos_νq, h_lt_νq, h_pos_q, h_lt_q]
    with y hy hpos1 hlt1 hpos2 hlt2
  -- both toReal factors are strictly positive, hence nonzero
  have hne1 : ((ν.rnDeriv q y).toReal) ≠ 0 :=
    (ENNReal.toReal_pos hpos1.ne' hlt1.ne).ne'
  have hne2 : ((q.rnDeriv volume y).toReal) ≠ 0 :=
    (ENNReal.toReal_pos hpos2.ne' hlt2.ne).ne'
  -- rewrite log(dν/dvol) = log((dν/dq)·(dq/dvol)) and split
  rw [← hy, ENNReal.toReal_mul, Real.log_mul hne1 hne2]
  ring

/-- **★ General Bayes density split of the joint llr** (genuine, modulo named ac
hyps). For input law `p`, Markov channel `W`, output `q := outputDistribution p W`,
with each fibre `≪ q ≪ volume` and joint `≪ p.prod q`, the log-likelihood ratio of
the joint against the product factorizes into fibre/output log-densities. This is
the body of the residual hypothesis `h_llr_split`. Combines the linchpin
`rnDeriv_compProd_fibre` (at `η := Kernel.const ℝ q`) with `rnDeriv_eq_rnDeriv_measure`
and the per-fibre `log_rnDeriv_split`. -/
theorem llr_compProd_prod_split
    (q : Measure ℝ) [IsProbabilityMeasure q]
    (hWx_q : ∀ x, W x ≪ q) (hq_vol : q ≪ volume)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod q)
    -- measurable PDF proxy `g` for the fibre volume-density (Route B: AWGN supplies
    -- `g := fun z => gaussianPDF z.1 N z.2`, everywhere jointly measurable). The
    -- per-fibre a.e. agreement `hg_ae` carries the rnDeriv↔proxy bridge.
    (g : ℝ × ℝ → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y)) :
    (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
    (fun z => Real.log (g z).toReal
                - Real.log (q.rnDeriv volume z.2).toReal) := by
  -- present `p.prod q` as a compProd with the constant kernel `Kernel.const ℝ q`
  have h_prod : p.prod q = p ⊗ₘ (Kernel.const ℝ q) := (Measure.compProd_const).symm
  -- joint ≪ compProd-const  (rewrite of `h_joint_ac`)
  have h_ac' : (p ⊗ₘ W) ≪ p ⊗ₘ (Kernel.const ℝ q) := by rwa [h_prod] at h_joint_ac
  -- (1) linchpin: joint rnDeriv =ᵐ[p⊗ₘ const q] fibrewise kernel rnDeriv;
  --     transport to a.e. on the joint via `h_ac'`
  have h1 : (p ⊗ₘ W).rnDeriv (p.prod q)
      =ᵐ[p ⊗ₘ W] fun z => Kernel.rnDeriv W (Kernel.const ℝ q) z.1 z.2 := by
    rw [h_prod]
    exact h_ac'.ae_le (rnDeriv_compProd_fibre h_ac')
  -- (2+3) per-fibre: log of the fibrewise kernel rnDeriv splits into the proxy fibre
  -- term `log (g z).toReal` minus the output term, lifted to the joint. The eq-set is
  -- built directly with the everywhere-measurable proxy `g`, never the rnDeriv form.
  have h_split : (fun z => Real.log ((Kernel.rnDeriv W (Kernel.const ℝ q) z.1 z.2)).toReal)
      =ᵐ[p ⊗ₘ W] fun z => Real.log (g z).toReal
                  - Real.log (q.rnDeriv volume z.2).toReal := by
    refine Measure.ae_compProd_of_ae_ae ?_ ?_
    · refine measurableSet_eq_fun ?_ ?_
      · exact (Kernel.measurable_rnDeriv W (Kernel.const ℝ q)).ennreal_toReal.log
      · exact (hg_meas.ennreal_toReal.log).sub
          (((Measure.measurable_rnDeriv q volume).comp measurable_snd).ennreal_toReal.log)
    · -- a.e. `a ∂p`, a.e. `b ∂(W a)`
      filter_upwards with a
      -- fibre kernel rnDeriv = fibre measure rnDeriv `(W a).rnDeriv q`, a.e. on `W a`
      have hker : (fun b => Kernel.rnDeriv W (Kernel.const ℝ q) a b)
          =ᵐ[W a] fun b => (W a).rnDeriv q b := by
        have := (hWx_q a).ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := W) (η := Kernel.const ℝ q) (a := a))
        simpa only [Kernel.const_apply] using this
      -- per-fibre rnDeriv↔proxy bridge `(W a).rnDeriv vol =ᵐ[W a] g(a,·)`
      filter_upwards [hker, log_rnDeriv_split (hWx_q a) hq_vol, hg_ae a]
        with b hb hb_split hg_b
      rw [hb, hb_split, hg_b]
  -- assemble:  llr = log(joint rnDeriv).toReal = log(fibre kernel rnDeriv).toReal = split
  have h_llr_eq : (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
      fun z => Real.log ((Kernel.rnDeriv W (Kernel.const ℝ q) z.1 z.2)).toReal := by
    simp only [llr_def]
    filter_upwards [h1] with z hz1
    rw [hz1]
  exact h_llr_eq.trans h_split

/-- **★ Continuous-channel MI chain rule body** (AWGN-independent, genuine).

`(mutualInfoOfChannel p W).toReal = h(Y) − ∫ h(Y|X=x) dp(x)`, the density-level
analogue of the discrete `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy`.

This is assembled **genuinely (0 sorry)** from the local helpers — no external
density-level wall. The proof opens `mutualInfoOfChannel = klDiv (p⊗ₘW) (p.prod q)`
(`q := outputDistribution p W`) via `toReal_klDiv_of_measure_eq` (both factors are
probability measures, so the univ-mass condition is automatic), rewrites the joint
log-likelihood ratio by the Bayes density split `llr_compProd_prod_split`, splits the
resulting integral with `integral_sub`, identifies the fibre term with
`integral_compProd` + `integral_log_proxy_fibre` (each fibre `↦ −h(W x)`), and
identifies the output term with `integral_snd_outputDistribution` +
`integral_log_rnDeriv_eq_neg_diffEntropy` (`↦ −h(q)`).
@audit:ok -/
theorem mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    (hW_ac : ∀ x, W x ≪ volume)
    (hWx_q : ∀ x, W x ≪ outputDistribution p W)
    (hq_ac : outputDistribution p W ≪ volume)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W))
    (g : ℝ × ℝ → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y))
    (h_int_fibre : Integrable (fun z : ℝ × ℝ => Real.log (g z).toReal) (p ⊗ₘ W))
    (h_int_out : Integrable
        (fun z : ℝ × ℝ => Real.log
            ((outputDistribution p W).rnDeriv volume z.2).toReal) (p ⊗ₘ W)) :
    (mutualInfoOfChannel p W).toReal
      = InformationTheory.Shannon.differentialEntropy (outputDistribution p W)
        - (∫ x, InformationTheory.Shannon.differentialEntropy (W x) ∂p) := by
  set q := outputDistribution p W with hq_def
  -- `p.prod q` is a probability measure (product of two probability measures)
  have hq_vol : q ≪ volume := hq_ac
  -- Phase 1: open `mutualInfoOfChannel` to an llr integral against the joint.
  have h_kl :
      (mutualInfoOfChannel p W).toReal
        = ∫ z, llr (p ⊗ₘ W) (p.prod q) z ∂(p ⊗ₘ W) := by
    rw [mutualInfoOfChannel_def, jointDistribution_def]
    refine toReal_klDiv_of_measure_eq h_joint_ac ?_
    rw [measure_univ, measure_univ]
  rw [h_kl]
  -- Phase 3: rewrite the integrand by the Bayes density split (a.e. on the joint).
  rw [integral_congr_ae
        (llr_compProd_prod_split (p := p) (W := W) q hWx_q hq_vol h_joint_ac g hg_meas hg_ae)]
  -- split the integral of the difference into two integrals
  rw [integral_sub h_int_fibre h_int_out]
  -- Phase 4: fibre term `∫ z, log (g z).toReal ∂(p⊗ₘW) = -∫ x, h(W x) ∂p`.
  have h_fibre :
      (∫ z, Real.log (g z).toReal ∂(p ⊗ₘ W))
        = -(∫ x, InformationTheory.Shannon.differentialEntropy (W x) ∂p) := by
    rw [Measure.integral_compProd h_int_fibre]
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact integral_log_proxy_fibre x (hW_ac x) (hg_ae x)
  -- Phase 5: output term `∫ z, log f_q(z.2) ∂(p⊗ₘW) = -h(q)`.
  have h_out :
      (∫ z, Real.log (q.rnDeriv volume z.2).toReal ∂(p ⊗ₘ W))
        = -InformationTheory.Shannon.differentialEntropy q := by
    -- reduce the joint integral to the output marginal `q = (p⊗ₘW).map snd`
    have h_eq : q = (p ⊗ₘ W).map Prod.snd := rfl
    have h_int_joint :
        Integrable
          ((fun y => Real.log (q.rnDeriv volume y).toReal) ∘ Prod.snd) (p ⊗ₘ W) := h_int_out
    have h_marg_meas :
        AEStronglyMeasurable (fun y => Real.log (q.rnDeriv volume y).toReal) q :=
      ((Measure.measurable_rnDeriv q volume).ennreal_toReal.log).aestronglyMeasurable
    have h_int_out_marg :
        Integrable (fun y => Real.log (q.rnDeriv volume y).toReal) q := by
      rw [h_eq]
      refine (integrable_map_measure ?_ measurable_snd.aemeasurable).mpr h_int_joint
      rw [← h_eq]; exact h_marg_meas
    rw [integral_snd_outputDistribution
          (fun y => Real.log (q.rnDeriv volume y).toReal) (by rw [← hq_def]; exact h_int_out_marg)]
    rw [← hq_def]
    exact integral_log_rnDeriv_eq_neg_diffEntropy q hq_vol
  -- Phase 6: combine.
  rw [h_fibre, h_out]
  ring

/-! ## Generic (output type `β` + reference measure `ref`) MI chain rule

The 1-D body `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` above is specialized to
`Channel ℝ ℝ` with the Lebesgue reference `volume : Measure ℝ`. The block AWGN converse
needs the **n-dimensional output** form (`β := Fin n → ℝ`, `ref := volume`), so we
re-derive the same chain identity for an arbitrary input type `α`, output type `β`, and
reference measure `ref : Measure β`, stated in **log-density-integral form**
(`∫ log (rnDeriv · ref)`) rather than `differentialEntropy`, so the consumer is free to
identify each integral with whatever entropy notion it uses (`jointDifferentialEntropyPi`
for the AWGN block). The proof mirrors the 1-D one step for step; only the helper lemmas
are re-stated generically. -/

section Generic

variable {α : Type*} {mα : MeasurableSpace α} {β : Type*} {mβ : MeasurableSpace β}

/-- **Generic marginal identification.** For a `ref`-integrable observable `g : β → ℝ`,
the joint integral of `g ∘ snd` against `p ⊗ₘ W` equals the integral of `g` against the
output marginal `outputDistribution p W = (p ⊗ₘ W).snd`. Generic in `α, β`. -/
theorem integral_snd_outputDistribution_gen
    {p : Measure α} {W : Channel α β}
    (g : β → ℝ) (hg : Integrable g (outputDistribution p W)) :
    ∫ z, g z.2 ∂(p ⊗ₘ W) = ∫ y, g y ∂(outputDistribution p W) := by
  have h_eq : outputDistribution p W = (p ⊗ₘ W).map Prod.snd := rfl
  have hg' : AEStronglyMeasurable g ((p ⊗ₘ W).map Prod.snd) := by
    rw [← h_eq]; exact hg.aestronglyMeasurable
  rw [h_eq, MeasureTheory.integral_map measurable_snd.aemeasurable hg']

/-- **Generic per-measure log-density split** (Bayes step). For `ν ≪ q ≪ ref` all
`σ`-finite (with `ν.HaveLebesgueDecomposition q`, `q.HaveLebesgueDecomposition ref`),
`log (dν/dq y) = log (dν/dref y) − log (dq/dref y)`, `ν`-a.e. Generic reference `ref`. -/
theorem log_rnDeriv_split_gen
    {ν q ref : Measure β} [SigmaFinite ν] [SigmaFinite q] [SigmaFinite ref]
    [ν.HaveLebesgueDecomposition q] [q.HaveLebesgueDecomposition ref]
    [ν.HaveLebesgueDecomposition ref]
    (hνq : ν ≪ q) (hq_ref : q ≪ ref) :
    (fun y => Real.log ((ν.rnDeriv q y).toReal))
      =ᵐ[ν]
    (fun y => Real.log ((ν.rnDeriv ref y).toReal)
                - Real.log ((q.rnDeriv ref y).toReal)) := by
  have h_chain : (fun y => ν.rnDeriv q y * q.rnDeriv ref y)
      =ᵐ[ν] ν.rnDeriv ref :=
    hνq.ae_le (Measure.rnDeriv_mul_rnDeriv' (μ := ν) (ν := q) (κ := ref) hq_ref)
  have h_pos_νq : ∀ᵐ y ∂ν, 0 < ν.rnDeriv q y := Measure.rnDeriv_pos hνq
  have h_lt_νq : ∀ᵐ y ∂ν, ν.rnDeriv q y < ∞ := hνq.ae_le (Measure.rnDeriv_lt_top ν q)
  have h_pos_q : ∀ᵐ y ∂ν, 0 < q.rnDeriv ref y := hνq.ae_le (Measure.rnDeriv_pos hq_ref)
  have h_lt_q : ∀ᵐ y ∂ν, q.rnDeriv ref y < ∞ :=
    hνq.ae_le (hq_ref.ae_le (Measure.rnDeriv_lt_top q ref))
  filter_upwards [h_chain, h_pos_νq, h_lt_νq, h_pos_q, h_lt_q]
    with y hy hpos1 hlt1 hpos2 hlt2
  have hne1 : ((ν.rnDeriv q y).toReal) ≠ 0 :=
    (ENNReal.toReal_pos hpos1.ne' hlt1.ne).ne'
  have hne2 : ((q.rnDeriv ref y).toReal) ≠ 0 :=
    (ENNReal.toReal_pos hpos2.ne' hlt2.ne).ne'
  rw [← hy, ENNReal.toReal_mul, Real.log_mul hne1 hne2]
  ring

/-- **★ Generic Bayes density split of the joint llr.** For input law `p`, Markov
channel `W : Channel α β`, output `q := outputDistribution p W`, with each fibre
`≪ q ≪ ref` and joint `≪ p.prod q`, the log-likelihood ratio of the joint against the
product factorizes into fibre/output log-densities. Generic in `α, β, ref`. -/
theorem llr_compProd_prod_split_gen
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {p : Measure α} [IsProbabilityMeasure p]
    {W : Channel α β} [IsMarkovKernel W]
    (q ref : Measure β) [IsProbabilityMeasure q] [SigmaFinite ref]
    [q.HaveLebesgueDecomposition ref]
    (hWx_q : ∀ x, W x ≪ q) (hq_ref : q ≪ ref)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod q)
    (g : α × β → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => (W x).rnDeriv ref y) =ᵐ[W x] fun y => g (x, y)) :
    (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
    (fun z => Real.log (g z).toReal
                - Real.log (q.rnDeriv ref z.2).toReal) := by
  have h_prod : p.prod q = p ⊗ₘ (Kernel.const α q) := (Measure.compProd_const).symm
  have h_ac' : (p ⊗ₘ W) ≪ p ⊗ₘ (Kernel.const α q) := by rwa [h_prod] at h_joint_ac
  have h1 : (p ⊗ₘ W).rnDeriv (p.prod q)
      =ᵐ[p ⊗ₘ W] fun z => Kernel.rnDeriv W (Kernel.const α q) z.1 z.2 := by
    rw [h_prod]
    exact h_ac'.ae_le (rnDeriv_compProd_fibre h_ac')
  have h_split : (fun z => Real.log ((Kernel.rnDeriv W (Kernel.const α q) z.1 z.2)).toReal)
      =ᵐ[p ⊗ₘ W] fun z => Real.log (g z).toReal
                  - Real.log (q.rnDeriv ref z.2).toReal := by
    refine Measure.ae_compProd_of_ae_ae ?_ ?_
    · refine measurableSet_eq_fun ?_ ?_
      · exact (Kernel.measurable_rnDeriv W (Kernel.const α q)).ennreal_toReal.log
      · exact (hg_meas.ennreal_toReal.log).sub
          (((Measure.measurable_rnDeriv q ref).comp measurable_snd).ennreal_toReal.log)
    · filter_upwards with a
      have hker : (fun b => Kernel.rnDeriv W (Kernel.const α q) a b)
          =ᵐ[W a] fun b => (W a).rnDeriv q b := by
        have := (hWx_q a).ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := W) (η := Kernel.const α q) (a := a))
        simpa only [Kernel.const_apply] using this
      filter_upwards [hker, log_rnDeriv_split_gen (hWx_q a) hq_ref, hg_ae a]
        with b hb hb_split hg_b
      rw [hb, hb_split, hg_b]
  have h_llr_eq : (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
      fun z => Real.log ((Kernel.rnDeriv W (Kernel.const α q) z.1 z.2)).toReal := by
    simp only [llr_def]
    filter_upwards [h1] with z hz1
    rw [hz1]
  exact h_llr_eq.trans h_split

/-- **★ Generic continuous-channel MI chain rule body** (output type `β`, reference
`ref`), in **log-density-integral form**:

`I.toReal = (∫ x, ∫ y, log(d(W x)/d ref y) ∂(W x) ∂p) − (∫ y, log(dq/d ref y) ∂q)`,

i.e. `I = (−h(Y|X)) − (−h(Y)) = h(Y) − h(Y|X)` once each integral is identified with the
relevant neg-entropy by `integral_log_rnDeriv_self_eq_neg`. Genuine, mirrors the 1-D body
`mutualInfoOfChannel_toReal_eq_diffEntropy_sub`.
@audit:ok -/
theorem mutualInfoOfChannel_toReal_eq_log_density_sub
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {p : Measure α} [IsProbabilityMeasure p]
    {W : Channel α β} [IsMarkovKernel W]
    (ref : Measure β) [SigmaFinite ref]
    [(outputDistribution p W).HaveLebesgueDecomposition ref]
    (hWx_q : ∀ x, W x ≪ outputDistribution p W)
    (hq_ref : outputDistribution p W ≪ ref)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W))
    (g : α × β → ℝ≥0∞) (hg_meas : Measurable g)
    (hg_ae : ∀ x, (fun y => (W x).rnDeriv ref y) =ᵐ[W x] fun y => g (x, y))
    (h_int_fibre : Integrable (fun z : α × β => Real.log (g z).toReal) (p ⊗ₘ W))
    (h_int_out : Integrable
        (fun z : α × β => Real.log
            ((outputDistribution p W).rnDeriv ref z.2).toReal) (p ⊗ₘ W))
    (h_fibre_self : ∀ x, ∫ y, Real.log (g (x, y)).toReal ∂(W x)
        = ∫ y, Real.log ((W x).rnDeriv ref y).toReal ∂(W x))
    (h_out_self : Integrable
        (fun y => Real.log ((outputDistribution p W).rnDeriv ref y).toReal)
        (outputDistribution p W)) :
    (mutualInfoOfChannel p W).toReal
      = (∫ x, (∫ y, Real.log ((W x).rnDeriv ref y).toReal ∂(W x)) ∂p)
        - (∫ y, Real.log ((outputDistribution p W).rnDeriv ref y).toReal
              ∂(outputDistribution p W)) := by
  set q := outputDistribution p W with hq_def
  have h_kl :
      (mutualInfoOfChannel p W).toReal
        = ∫ z, llr (p ⊗ₘ W) (p.prod q) z ∂(p ⊗ₘ W) := by
    rw [mutualInfoOfChannel_def, jointDistribution_def]
    refine toReal_klDiv_of_measure_eq h_joint_ac ?_
    rw [measure_univ, measure_univ]
  rw [h_kl]
  rw [integral_congr_ae
        (llr_compProd_prod_split_gen (p := p) (W := W) q ref hWx_q hq_ref h_joint_ac
          g hg_meas hg_ae)]
  rw [integral_sub h_int_fibre h_int_out]
  -- fibre term
  have h_fibre :
      (∫ z, Real.log (g z).toReal ∂(p ⊗ₘ W))
        = ∫ x, (∫ y, Real.log ((W x).rnDeriv ref y).toReal ∂(W x)) ∂p := by
    rw [Measure.integral_compProd h_int_fibre]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact h_fibre_self x
  -- output term
  have h_out :
      (∫ z, Real.log (q.rnDeriv ref z.2).toReal ∂(p ⊗ₘ W))
        = ∫ y, Real.log (q.rnDeriv ref y).toReal ∂q := by
    rw [integral_snd_outputDistribution_gen
          (fun y => Real.log (q.rnDeriv ref y).toReal) (by rw [← hq_def]; exact h_out_self)]
  rw [h_fibre, h_out]

end Generic

end InformationTheory.Shannon.ChannelCoding
