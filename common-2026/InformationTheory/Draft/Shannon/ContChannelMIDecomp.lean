import InformationTheory.Shannon.ChannelCoding
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.AWGNMIDecompBody
import InformationTheory.Shannon.AWGNBindConvBody
import InformationTheory.Shannon.AwgnWalls
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Continuous-channel mutual-information chain rule (body discharge)

[awgn-mi-decomp-plan.md](../../../docs/shannon/awgn-mi-decomp-plan.md).

This file genuinely discharges the **continuous-channel MI chain rule**
`I(X;Y) = h(Y) − h(Y|X)` (`AWGNMIDecompBody.IsContChannelMIDecompHyp`), with `h(Y|X)`
realized as the integral of fibrewise differential entropies.

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
all genuinely discharged here.

The single step **(★)** — the Bayes density split of the joint log-likelihood
ratio into fibre/output log densities — is the conditional-rnDeriv-to-fibre
identification `(p⊗ₘW).rnDeriv (p.prod q) (x,y) =ᵐ (W x).rnDeriv vol y / q.rnDeriv vol y`.
Mathlib's `rnDeriv_compProd` machinery stops at the *conditional* rnDeriv
`(μ⊗ₘκ).rnDeriv (μ⊗ₘη)` and provides **no** fibre identification
`= (κ a).rnDeriv (η a)`. This is supplied **genuinely** here by the linchpin
`rnDeriv_compProd_fibre` (withDensity route), assembled into the per-fibre split by
`llr_compProd_prod_split`. As of 2026-05-28 the body
`mutualInfoOfChannel_toReal_eq_diffEntropy_sub` is therefore **fully genuine (0 sorry,
no shared wall)**: the entire klDiv→integral structure (`toReal_klDiv_of_measure_eq`),
the Bayes split, the Fubini decomposition (`integral_compProd` + `integral_sub`) and
both differential-entropy identifications (fibre + output, via
`integral_log_rnDeriv_eq_neg_diffEntropy`) are proved explicitly. The former shared
sorry lemma `AwgnWalls.contChannelMIDecomp_holds` has been retired.
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
      = -Common2026.Shannon.differentialEntropy μ := by
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
    _ = -Common2026.Shannon.differentialEntropy μ := by
        unfold Common2026.Shannon.differentialEntropy
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
      = -Common2026.Shannon.differentialEntropy (W x) :=
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
      = -Common2026.Shannon.differentialEntropy (W x) := by
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

This is now assembled **genuinely (0 sorry)** from the local helpers — no external
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
      = Common2026.Shannon.differentialEntropy (outputDistribution p W)
        - (∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p) := by
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
        = -(∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p) := by
    rw [Measure.integral_compProd h_int_fibre]
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact integral_log_proxy_fibre x (hW_ac x) (hg_ae x)
  -- Phase 5: output term `∫ z, log f_q(z.2) ∂(p⊗ₘW) = -h(q)`.
  have h_out :
      (∫ z, Real.log (q.rnDeriv volume z.2).toReal ∂(p ⊗ₘ W))
        = -Common2026.Shannon.differentialEntropy q := by
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

end InformationTheory.Shannon.ChannelCoding

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

/-- **2-variable (joint) measurability of the ℝ≥0∞ Gaussian pdf** (Route B linchpin).
The closed-form Gaussian pdf is everywhere jointly measurable in `(mean, point)`,
whereas the measure-form rnDeriv `fun z => (gaussianReal z.1 N).rnDeriv volume z.2`
is **not** (it is only a.e.-determined). This brick supplies the everywhere
joint measurability that the eq-set construction in `llr_compProd_prod_split`
requires. -/
theorem measurable_gaussianPDF_uncurry (N : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ => gaussianPDF z.1 N z.2) := by
  simp only [gaussianPDF, gaussianPDFReal]
  fun_prop

/-- **2-variable (joint) measurability of the ℝ-valued Gaussian pdf.** Companion of
`measurable_gaussianPDF_uncurry`; used to supply the joint `AEStronglyMeasurable`
prerequisite when lifting the proxy log-density integrability to the compProd. -/
theorem measurable_gaussianPDFReal_uncurry (N : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ => gaussianPDFReal z.1 N z.2) := by
  simp only [gaussianPDFReal]
  fun_prop

/-- **Second moment of a real Gaussian is integrable.** `(y − m)²` is integrable
against `gaussianReal m' v'` (any mean / variance), since `id ∈ L²(gaussianReal)`
(`memLp_id_gaussianReal`). Needed to discharge the Gaussian log-density
integrabilities (the log pdf is a constant plus a `(y − m)²` term). -/
theorem integrable_sq_sub_gaussianReal (m m' : ℝ) (v' : ℝ≥0) :
    Integrable (fun y => (y - m) ^ 2) (gaussianReal m' v') := by
  -- `id ∈ L²` and `id ∈ L¹`, so `y², y, 1` are all integrable; expand `(y-m)²`.
  have h_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal m' v') :=
    (memLp_id_gaussianReal (μ := m') (v := v') 2).integrable_sq
  have h_id : Integrable (fun y : ℝ => y) (gaussianReal m' v') := by
    have := (memLp_id_gaussianReal (μ := m') (v := v') 1).integrable (by norm_num)
    simpa using this
  have h_eq : (fun y : ℝ => (y - m) ^ 2)
      = fun y => y ^ 2 - 2 * m * y + m ^ 2 := by
    funext y; ring
  rw [h_eq]
  exact ((h_sq.sub (h_id.const_mul (2 * m))).add (integrable_const (m ^ 2)))

/-- **Log Gaussian density is integrable against a Gaussian law.** For `v ≠ 0`,
`fun y => Real.log (gaussianPDFReal m v y)` is integrable against `gaussianReal m' v'`.
The log pdf splits as `c₀ + c₁·(y − m)²`, a constant plus a finite-second-moment term. -/
theorem integrable_log_gaussianPDFReal_gaussianReal
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (m' : ℝ) (v' : ℝ≥0) :
    Integrable (fun y => Real.log (gaussianPDFReal m v y)) (gaussianReal m' v') := by
  -- `log (gaussianPDFReal m v y) = c₀ + c₁·(y − m)²` (Phase C-2 split).
  have h_eq : (fun y => Real.log (gaussianPDFReal m v y))
      = fun y => (-(1/2) * Real.log (2 * Real.pi * v))
          + (-(1 / (2 * (v : ℝ)))) * (y - m) ^ 2 := by
    funext y
    rw [Common2026.Shannon.log_gaussianPDFReal_eq m hv y]
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
    Integrable (fun y => Real.log ((gaussianReal m v).rnDeriv volume y).toReal)
      (gaussianReal m v) := by
  -- `rnDeriv =ᵐ[gaussianReal] gaussianPDF`, transported from vol via absolute continuity.
  have h_rn : (gaussianReal m v).rnDeriv volume =ᵐ[gaussianReal m v] gaussianPDF m v :=
    (gaussianReal_absolutelyContinuous m hv).ae_le (rnDeriv_gaussianReal m v)
  -- the log-density observables agree a.e. on `gaussianReal m v`
  have h_log :
      (fun y => Real.log (gaussianPDFReal m v y))
        =ᵐ[gaussianReal m v]
      (fun y => Real.log ((gaussianReal m v).rnDeriv volume y).toReal) := by
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
/-- **Proxy-form joint integrability of the AWGN fibre log-density** (Route B, discharges
residual #2). The fibre log-density, in measurable-proxy form
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
      (fun z : ℝ × ℝ => Real.log (gaussianPDF z.1 N z.2).toReal)
      ((gaussianReal 0 P.toNNReal) ⊗ₘ (awgnChannel N h_meas)) := by
  set p := gaussianReal 0 P.toNNReal with hp_def
  set W := awgnChannel N h_meas with hW_def
  -- the joint integrand decomposes everywhere as `c₀ + c₁·(z.2 − z.1)²`
  set c₀ : ℝ := -(1 / 2) * Real.log (2 * Real.pi * N) with hc₀
  set c₁ : ℝ := -(1 / (2 * (N : ℝ))) with hc₁
  have h_eq : (fun z : ℝ × ℝ => Real.log (gaussianPDF z.1 N z.2).toReal)
      = fun z => c₀ + c₁ * (z.2 - z.1) ^ 2 := by
    funext z
    rw [toReal_gaussianPDF, Common2026.Shannon.log_gaussianPDFReal_eq z.1 hN z.2, hc₀, hc₁]
    ring
  rw [h_eq]
  -- the `(z.2 − z.1)²` term is integrable against the joint via compProd-iff
  have h_sq : Integrable (fun z : ℝ × ℝ => (z.2 - z.1) ^ 2) (p ⊗ₘ W) := by
    have h_aesm : AEStronglyMeasurable (fun z : ℝ × ℝ => (z.2 - z.1) ^ 2) (p ⊗ₘ W) :=
      ((measurable_snd.sub measurable_fst).pow_const 2).aestronglyMeasurable
    rw [Measure.integrable_compProd_iff h_aesm]
    refine ⟨Filter.Eventually.of_forall (fun x => ?_), ?_⟩
    · -- per-fibre `Integrable (fun y => (y − x)²) (W x = gaussianReal x N)`
      simpa only [hW_def, awgnChannel_apply] using integrable_sq_sub_gaussianReal x x N
    · -- per-fibre L¹-norm integral is the constant `N` (nonneg integrand, second moment)
      have h_norm : (fun x => ∫ y, ‖(y - x) ^ 2‖ ∂(W x)) = fun _ => (N : ℝ) := by
        funext x
        have : (fun y => ‖(y - x) ^ 2‖) = fun y => (y - x) ^ 2 := by
          funext y; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        rw [this, hW_def, awgnChannel_apply]
        exact integral_sq_sub_self_gaussianReal x N
      rw [h_norm]
      exact integrable_const _
  exact (integrable_const c₀).add (h_sq.const_mul c₁)

open InformationTheory.Shannon.ChannelCoding in
/-- **★ AWGN instance discharge of `IsContChannelMIDecompHyp` (F-2′).**

Applies the general body `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` at the AWGN
instance `p := gaussianReal 0 P.toNNReal`, `W := awgnChannel N h_meas`. This theorem is
now **hypothesis-free** (only `P, N, hN, hPN, h_meas, h_out`): all of the following are
discharged genuinely:

* the fibre / output absolute continuities `hW_ac`, `hq_ac` (Gaussian facts);
* the **joint absolute continuity** `p⊗ₘW ≪ p.prod q`
  (`absolutelyContinuous_compProd_right_iff` + fibre-vs-output ac);
* the **Bayes density split** `h_llr_split` — discharged by the general
  `llr_compProd_prod_split`, which rests on the now-proved **linchpin**
  `rnDeriv_compProd_fibre` (the Mathlib TODO fibre form of the compProd rnDeriv);
* the **fibre log-density integrability** and the **fibre joint measurability** —
  formerly the two residual honest hypotheses `h_meas_fibre`/`h_int_fibre_joint`, now
  discharged via the **Route B measurable PDF proxy** `g := fun z => gaussianPDF z.1 N z.2`.

**Route B (why the two residuals are gone).** The *measure-form* parameterized rnDeriv
`fun z => (gaussianReal z.1 N).rnDeriv volume z.2` has **no** everywhere joint
measurability (rnDeriv is a.e.-determined; `rnDeriv_gaussianReal` is `=ᵐ[volume]`, not
everywhere). Instead of trying to build that, the fibre density term is moved to the
closed-form proxy `g`, which **is** everywhere jointly measurable
(`measurable_gaussianPDF_uncurry`). The proxy↔rnDeriv bridge is the per-fibre a.e.
agreement `hg_ae x : (W x).rnDeriv vol =ᵐ[W x] g(x,·)` (from `rnDeriv_gaussianReal`
lifted via `gaussianReal_absolutelyContinuous`), consumed only *inside integrals* by
`llr_compProd_prod_split` and `integral_log_proxy_fibre` — never via a joint a.e.
`MeasurableSet`, which would be circular. The proxy-form joint integrability is
`integrable_log_proxy_fibre_compProd`. The two **output**-side log-density
integrabilities are discharged here genuinely from the Gaussian density facts:
`h_int_out_joint` (the integrand depends only on `z.2`, so it is `g ∘ snd` with
`(p ⊗ₘ W).snd = outputDistribution = q`) reduces to `h_int_out_marg`, which is
`integrable_log_rnDeriv_gaussianReal` at `q = gaussianReal 0 (P + N)`. -/
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
  -- measurable PDF proxy `g := gaussianPDF` for the fibre volume-density (Route B)
  set g : ℝ × ℝ → ℝ≥0∞ := fun z => gaussianPDF z.1 N z.2 with hg_def
  have hg_meas : Measurable g := measurable_gaussianPDF_uncurry N
  -- per-fibre rnDeriv↔proxy bridge: `(W x).rnDeriv vol =ᵐ[W x] g(x, ·)`
  have hg_ae : ∀ x, (fun y => (W x).rnDeriv volume y) =ᵐ[W x] fun y => g (x, y) := by
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
      (Filter.Eventually.of_forall (fun x => by simpa only [Kernel.const_apply] using hWx_q x))
  -- Bayes density split via the general linchpin-backed lemma (proxy form)
  have h_llr_split := llr_compProd_prod_split (p := p) (W := W) q hWx_q hq_vol
    h_joint_ac g hg_meas hg_ae
  -- ★ fibre log-density integrability against the joint, in proxy form (Route B)
  have h_int_fibre_joint :
      Integrable (fun z => Real.log (g z).toReal) (p ⊗ₘ W) :=
    integrable_log_proxy_fibre_compProd P N hN h_meas
  -- ★ output marginal log-density integrability (Gaussian fact, q = 𝒩(0, P+N))
  have h_int_out_marg :
      Integrable (fun y => Real.log (q.rnDeriv volume y).toReal) q := by
    rw [hq_def, h_out]
    exact integrable_log_rnDeriv_gaussianReal 0 hPN
  -- ★ joint output log-density integrability: integrand = (log-density ∘ snd),
  --    and `(p ⊗ₘ W).snd = outputDistribution p W = q`, so reduce to `h_int_out_marg`.
  have h_int_out_joint :
      Integrable (fun z => Real.log (q.rnDeriv volume z.2).toReal) (p ⊗ₘ W) := by
    have h_eq : q = (p ⊗ₘ W).map Prod.snd := rfl
    have hg_aesm :
        AEStronglyMeasurable (fun y => Real.log (q.rnDeriv volume y).toReal) q :=
      h_int_out_marg.aestronglyMeasurable
    rw [show (fun z : ℝ × ℝ => Real.log (q.rnDeriv volume z.2).toReal)
          = (fun y => Real.log (q.rnDeriv volume y).toReal) ∘ Prod.snd from rfl]
    refine (integrable_map_measure ?_ measurable_snd.aemeasurable).mp ?_
    · rw [← h_eq]; exact hg_aesm
    · rw [← h_eq]; exact h_int_out_marg
  unfold IsContChannelMIDecompHyp
  -- All arguments of the now-genuine generic body
  -- `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` are discharged genuinely from the
  -- Gaussian facts built above: the three absolute continuities, the fibre-vs-output
  -- ac `hWx_q`, the measurable proxy `g` + its per-fibre a.e. bridge `hg_ae`, and the
  -- two log-density integrabilities (proxy fibre `h_int_fibre_joint`, output
  -- `h_int_out_joint`). The body itself (KL→llr, Bayes split, Fubini, both fibre/output
  -- entropy identifications) is fully genuine (0 sorry) — no shared MI-decomp wall.
  exact mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    (W := W) (awgnChannel_apply_absolutelyContinuous N hN h_meas)
    hWx_q hq_vol h_joint_ac g hg_meas hg_ae h_int_fibre_joint h_int_out_joint

open InformationTheory.Shannon.ChannelCoding in
/-- **F-2′ wrapper: `IsAwgnMIDecomp`, hypothesis-free.**

Composes `isContChannelMIDecompHyp_awgn` with the existing combinator
`awgn_midecomp_of_cont_chain`. The opaque MI-decomp predicate `IsAwgnMIDecomp` is now
discharged **with no residual honest hypotheses** (only `P, N, hN, hPN, h_meas, h_out`)
— via the genuinely-proved **linchpin** `rnDeriv_compProd_fibre`, the general
`llr_compProd_prod_split`, and the **Route B measurable PDF proxy** `g := gaussianPDF`
that retires the former residuals `h_meas_fibre`/`h_int_fibre_joint` (see
`isContChannelMIDecompHyp_awgn`). The Bayes density split, the joint absolute
continuity, both fibre/output absolute continuities, the fibre log-density
integrability and the two output-side log-density integrabilities are all discharged.
Everything else in the MI chain rule (KL→integral, Fubini split, both
differential-entropy identifications, output marginal) is genuinely discharged by the
general body. -/
theorem isAwgnMIDecomp_of_densitySplit
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (hPN : P.toNNReal + N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas) :
    IsAwgnMIDecomp P N h_meas :=
  awgn_midecomp_of_cont_chain P N h_meas
    (isContChannelMIDecompHyp_awgn P N hN hPN h_meas h_out)

/-- **Closed-form Gaussian MI from `h_out` alone.**

Same as `awgn_mi_gaussian_closed_form_of_primitives` but with the `h_decomp`
argument removed: `IsAwgnMIDecomp` is now discharged genuinely via Route B
(`isAwgnMIDecomp_of_densitySplit`), leaving only `h_out` honest. -/
theorem awgn_mi_gaussian_closed_form_of_out
    (P : ℝ) (hP_pos : (0 : ℝ) < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas) :
    (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
        (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)).toReal
      = (1/2) * Real.log (1 + P / (N : ℝ)) := by
  have hN_NN : N ≠ 0 :=
    fun h => hN (by exact_mod_cast (congrArg (fun x : ℝ≥0 => (x : ℝ)) h))
  have hP_toNN_pos : (0 : ℝ≥0) < P.toNNReal := Real.toNNReal_pos.mpr hP_pos
  have hPN : P.toNNReal + N ≠ 0 :=
    (add_pos_of_pos_of_nonneg hP_toNN_pos (zero_le' (a := N))).ne'
  have h_decomp : IsAwgnMIDecomp P N h_meas :=
    isAwgnMIDecomp_of_densitySplit P N hN_NN hPN h_meas h_out
  exact awgn_mi_gaussian_closed_form_of_primitives P hP_pos N hN h_meas h_out h_decomp

/-! **AWGN capacity closed form** — genuinely discharged downstream.

This file can only host the closed form with the converse `h_max_ent` as a `sorry`
(the genuine converse lives in `AwgnCapacityConverseMaxent`, which imports this file, so
wiring it here would create an import cycle). The former in-file `sorry` wrapper
`awgn_capacity_closed_form_of_out` has therefore been removed in favour of the genuine
successor `AwgnCapacityConverseMaxent.awgn_capacity_closed_form_genuine`
(`awgnCapacity P N = (1/2) log(1 + P/N)`, 0 sorry / 0 residual, `@audit:ok`). The wall
`awgn-capacity-converse-maxent` is CLOSED (2026-05-29). -/

end InformationTheory.Shannon.AWGN
