import Common2026.Shannon.ChannelCoding
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.AWGNMIDecompBody
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
`= (κ a).rnDeriv (η a)`; deriving it genuinely needs the full `Kernel.rnDeriv`
theory (a >100-line rabbit hole, plan 撤退ライン D-2 = F-2′). We therefore expose
**only this split** as a single named honest hypothesis `h_llr_split`, keeping the
body 🟢ʰ genuine: the entire klDiv→integral structure, the Fubini decomposition and
both differential-entropy identifications are proved explicitly. At the AWGN
instance the split is dischargeable from the Gaussian density facts.
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

/-- **Fibre differential-entropy identification (genuine).** For an `≪ volume`
fibre `W x` with measurable density `f := (W x).rnDeriv volume`, the inner integral
of `log f` against `W x` is `−differentialEntropy (W x)`. -/
theorem integral_log_density_fibre
    (x : ℝ) (hWx : W x ≪ volume) :
    ∫ y, Real.log ((W x).rnDeriv volume y).toReal ∂(W x)
      = -Common2026.Shannon.differentialEntropy (W x) := by
  set f : ℝ → ℝ≥0∞ := (W x).rnDeriv volume with hf_def
  have hf_meas : Measurable f := Measure.measurable_rnDeriv _ _
  have hf_lt_top : ∀ᵐ y ∂(volume : Measure ℝ), f y < ∞ := Measure.rnDeriv_lt_top _ _
  have h_wd : W x = volume.withDensity f := (Measure.withDensity_rnDeriv_eq _ _ hWx).symm
  -- rewrite the LHS integral against `W x` as an integral against `volume`
  calc ∫ y, Real.log (f y).toReal ∂(W x)
      = ∫ y, Real.log (f y).toReal ∂(volume.withDensity f) := by rw [h_wd]
    _ = ∫ y, (f y).toReal • Real.log (f y).toReal ∂volume :=
        integral_withDensity_eq_integral_toReal_smul hf_meas hf_lt_top _
    _ = ∫ y, (f y).toReal * Real.log (f y).toReal ∂volume := by
        simp only [smul_eq_mul]
    _ = -Common2026.Shannon.differentialEntropy (W x) := by
        unfold Common2026.Shannon.differentialEntropy
        rw [← integral_neg]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        rw [Real.negMulLog_def]
        ring

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
    -- joint measurability of the fibre volume-density (AWGN: Gaussian pdf in `(x,y)`)
    (h_meas_fibre : Measurable (fun z : ℝ × ℝ => (W z.1).rnDeriv volume z.2)) :
    (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
    (fun z => Real.log ((W z.1).rnDeriv volume z.2).toReal
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
  -- (2+3) per-fibre: log of the fibrewise kernel rnDeriv splits, lifted to the joint
  have h_split : (fun z => Real.log ((Kernel.rnDeriv W (Kernel.const ℝ q) z.1 z.2)).toReal)
      =ᵐ[p ⊗ₘ W] fun z => Real.log ((W z.1).rnDeriv volume z.2).toReal
                  - Real.log (q.rnDeriv volume z.2).toReal := by
    refine Measure.ae_compProd_of_ae_ae ?_ ?_
    · refine measurableSet_eq_fun ?_ ?_
      · exact (Kernel.measurable_rnDeriv W (Kernel.const ℝ q)).ennreal_toReal.log
      · exact (h_meas_fibre.ennreal_toReal.log).sub
          (((Measure.measurable_rnDeriv q volume).comp measurable_snd).ennreal_toReal.log)
    · -- a.e. `a ∂p`, a.e. `b ∂(W a)`
      filter_upwards with a
      -- fibre kernel rnDeriv = fibre measure rnDeriv `(W a).rnDeriv q`, a.e. on `W a`
      have hker : (fun b => Kernel.rnDeriv W (Kernel.const ℝ q) a b)
          =ᵐ[W a] fun b => (W a).rnDeriv q b := by
        have := (hWx_q a).ae_le
          (Kernel.rnDeriv_eq_rnDeriv_measure (κ := W) (η := Kernel.const ℝ q) (a := a))
        simpa only [Kernel.const_apply] using this
      filter_upwards [hker, log_rnDeriv_split (hWx_q a) hq_vol] with b hb hb_split
      rw [hb, hb_split]
  -- assemble:  llr = log(joint rnDeriv).toReal = log(fibre kernel rnDeriv).toReal = split
  have h_llr_eq : (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
      fun z => Real.log ((Kernel.rnDeriv W (Kernel.const ℝ q) z.1 z.2)).toReal := by
    simp only [llr_def]
    filter_upwards [h1] with z hz1
    rw [hz1]
  exact h_llr_eq.trans h_split

/-- **★ Continuous-channel MI chain rule body** (AWGN-independent, 🟢ʰ honest).

`(mutualInfoOfChannel p W).toReal = h(Y) − ∫ h(Y|X=x) dp(x)`, the density-level
analogue of the discrete `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy`. -/
theorem mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    (hW_ac : ∀ x, W x ≪ volume)
    (hq_ac : outputDistribution p W ≪ volume)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod (outputDistribution p W))
    -- ★ Bayes density split (honest; conditional-rnDeriv→fibre identification, plan D-2)
    (h_llr_split :
      (fun z => llr (p ⊗ₘ W) (p.prod (outputDistribution p W)) z)
        =ᵐ[p ⊗ₘ W]
      (fun z => Real.log ((W z.1).rnDeriv volume z.2).toReal
                  - Real.log ((outputDistribution p W).rnDeriv volume z.2).toReal))
    -- integrability of the two log-density pieces against the joint
    (h_int_fibre_joint :
      Integrable (fun z => Real.log ((W z.1).rnDeriv volume z.2).toReal) (p ⊗ₘ W))
    (h_int_out_joint :
      Integrable (fun z =>
        Real.log ((outputDistribution p W).rnDeriv volume z.2).toReal) (p ⊗ₘ W))
    -- output observable integrability against the marginal
    (h_int_out_marg : Integrable (fun y =>
        Real.log ((outputDistribution p W).rnDeriv volume y).toReal)
        (outputDistribution p W)) :
    (mutualInfoOfChannel p W).toReal
      = Common2026.Shannon.differentialEntropy (outputDistribution p W)
        - (∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p) := by
  classical
  set q := outputDistribution p W with hq_def
  -- abbreviations for the two log-density observables
  set Lfib : ℝ × ℝ → ℝ := fun z => Real.log ((W z.1).rnDeriv volume z.2).toReal with hLfib
  set Lout : ℝ × ℝ → ℝ := fun z => Real.log (q.rnDeriv volume z.2).toReal with hLout
  -- step 1+2 : KL → llr integral (toReal_klDiv_of_measure_eq, univ = 1 on both sides)
  have h_univ : (p ⊗ₘ W) Set.univ = (p.prod q) Set.univ := by
    rw [measure_univ, measure_univ]
  have h_kl : (mutualInfoOfChannel p W).toReal
      = ∫ z, llr (p ⊗ₘ W) (p.prod q) z ∂(p ⊗ₘ W) := by
    rw [mutualInfoOfChannel_def, jointDistribution_def, ← hq_def]
    exact toReal_klDiv_of_measure_eq h_joint_ac h_univ
  -- step (★) : Bayes density split
  have h_split : ∫ z, llr (p ⊗ₘ W) (p.prod q) z ∂(p ⊗ₘ W)
      = ∫ z, (Lfib z - Lout z) ∂(p ⊗ₘ W) := by
    refine integral_congr_ae ?_
    filter_upwards [h_llr_split] with z hz using hz
  -- step 3 : split into two joint integrals
  have h_sub : ∫ z, (Lfib z - Lout z) ∂(p ⊗ₘ W)
      = (∫ z, Lfib z ∂(p ⊗ₘ W)) - (∫ z, Lout z ∂(p ⊗ₘ W)) :=
    integral_sub h_int_fibre_joint h_int_out_joint
  -- step 4 : fibre term = − ∫ h(W x) ∂p (Fubini + integral_log_density_fibre)
  have h_fib : ∫ z, Lfib z ∂(p ⊗ₘ W)
      = -(∫ x, Common2026.Shannon.differentialEntropy (W x) ∂p) := by
    rw [Measure.integral_compProd h_int_fibre_joint]
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    -- inner integral over the fibre `W x`
    show ∫ y, Lfib (x, y) ∂(W x) = -Common2026.Shannon.differentialEntropy (W x)
    have h_inner : ∫ y, Lfib (x, y) ∂(W x)
        = ∫ y, Real.log ((W x).rnDeriv volume y).toReal ∂(W x) := rfl
    rw [h_inner, integral_log_density_fibre x (hW_ac x)]
  -- step 5 : output term = − h(q) (snd marginal + density entropy)
  have h_out : ∫ z, Lout z ∂(p ⊗ₘ W)
      = -Common2026.Shannon.differentialEntropy q := by
    have h_marg : ∫ z, Lout z ∂(p ⊗ₘ W)
        = ∫ y, Real.log (q.rnDeriv volume y).toReal ∂q := by
      have := integral_snd_outputDistribution
        (fun y => Real.log (q.rnDeriv volume y).toReal) h_int_out_marg
      rw [← hq_def] at this
      exact this
    rw [h_marg]
    -- ∫ y, log f_q ∂q = -h(q) via the same withDensity argument
    have hqd : q ≪ volume := hq_ac
    rw [show (fun y => Real.log (q.rnDeriv volume y).toReal)
          = (fun y => Real.log (q.rnDeriv volume y).toReal) from rfl]
    -- reuse the fibre-style identity manually for q
    set fq : ℝ → ℝ≥0∞ := q.rnDeriv volume with hfq
    have hfq_meas : Measurable fq := Measure.measurable_rnDeriv _ _
    have hfq_lt_top : ∀ᵐ y ∂(volume : Measure ℝ), fq y < ∞ := Measure.rnDeriv_lt_top _ _
    have h_wd : q = volume.withDensity fq := (Measure.withDensity_rnDeriv_eq _ _ hqd).symm
    calc ∫ y, Real.log (fq y).toReal ∂q
        = ∫ y, Real.log (fq y).toReal ∂(volume.withDensity fq) := by rw [h_wd]
      _ = ∫ y, (fq y).toReal • Real.log (fq y).toReal ∂volume :=
          integral_withDensity_eq_integral_toReal_smul hfq_meas hfq_lt_top _
      _ = ∫ y, (fq y).toReal * Real.log (fq y).toReal ∂volume := by simp only [smul_eq_mul]
      _ = -Common2026.Shannon.differentialEntropy q := by
          unfold Common2026.Shannon.differentialEntropy
          rw [← integral_neg]
          refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
          rw [Real.negMulLog_def]
          ring
  -- combine
  rw [h_kl, h_split, h_sub, h_fib, h_out]
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

open InformationTheory.Shannon.ChannelCoding in
/-- **★ AWGN instance discharge of `IsContChannelMIDecompHyp` (F-2′).**

Applies the general body `mutualInfoOfChannel_toReal_eq_diffEntropy_sub` at the AWGN
instance `p := gaussianReal 0 P.toNNReal`, `W := awgnChannel N h_meas`. Discharged
genuinely (no longer hypotheses):

* the fibre / output absolute continuities `hW_ac`, `hq_ac` (Gaussian facts);
* the **joint absolute continuity** `p⊗ₘW ≪ p.prod q`
  (`absolutelyContinuous_compProd_right_iff` + fibre-vs-output ac);
* the **Bayes density split** `h_llr_split` — discharged by the general
  `llr_compProd_prod_split`, which rests on the now-proved **linchpin**
  `rnDeriv_compProd_fibre` (the Mathlib TODO fibre form of the compProd rnDeriv).

The residual hypotheses are now just (a) the joint measurability of the fibre
Gaussian density `h_meas_fibre` and (b) the fibre log-density integrability
`h_int_fibre_joint`. **Both depend on the same genuine Mathlib gap**: the joint
(in `(x, y)`) measurability of the *measure-form* parameterized rnDeriv
`fun z => (gaussianReal z.1 N).rnDeriv volume z.2`. Mathlib only provides this for
the *kernel-form* rnDeriv (`Kernel.measurable_rnDeriv`), which is merely `=ᵐ` to
the measure form (`Kernel.rnDeriv_eq_rnDeriv_measure`); the a.e.-to-measurable
bridge needs a measurable equality set, which is exactly the missing fact (circular).
The two **output**-side log-density integrabilities are discharged here genuinely
from the Gaussian density facts: `h_int_out_joint` (the integrand depends only on
`z.2`, so it is `g ∘ snd` with `(p ⊗ₘ W).snd = outputDistribution = q`) reduces to
`h_int_out_marg`, which is `integrable_log_rnDeriv_gaussianReal` at
`q = gaussianReal 0 (P + N)`. This shrinks the residual from four honest
hypotheses to two (both pinned to the single rnDeriv joint-measurability gap). -/
theorem isContChannelMIDecompHyp_awgn
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (hPN : P.toNNReal + N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas)
    (h_meas_fibre :
      Measurable (fun z : ℝ × ℝ => ((awgnChannel N h_meas) z.1).rnDeriv volume z.2))
    (h_int_fibre_joint :
      Integrable (fun z =>
          Real.log (((awgnChannel N h_meas) z.1).rnDeriv volume z.2).toReal)
        ((gaussianReal 0 P.toNNReal) ⊗ₘ (awgnChannel N h_meas))) :
    IsContChannelMIDecompHyp
      (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas) := by
  classical
  set p := gaussianReal 0 P.toNNReal with hp_def
  set W := awgnChannel N h_meas with hW_def
  set q := outputDistribution p W with hq_def
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
  -- Bayes density split via the general linchpin-backed lemma
  have h_llr_split := llr_compProd_prod_split (p := p) (W := W) q hWx_q hq_vol
    h_joint_ac h_meas_fibre
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
  refine mutualInfoOfChannel_toReal_eq_diffEntropy_sub
    (W := W) ?_ ?_ h_joint_ac h_llr_split
    h_int_fibre_joint h_int_out_joint h_int_out_marg
  · -- hW_ac : each fibre ≪ volume
    exact awgnChannel_apply_absolutelyContinuous N hN h_meas
  · -- hq_ac : output ≪ volume
    exact hq_vol

open InformationTheory.Shannon.ChannelCoding in
/-- **F-2′ wrapper: `IsAwgnMIDecomp` from the shrunk AWGN residuals.**

Composes `isContChannelMIDecompHyp_awgn` with the existing combinator
`awgn_midecomp_of_cont_chain`. The opaque MI-decomp predicate `IsAwgnMIDecomp` is now
reduced — via the genuinely-proved **linchpin** `rnDeriv_compProd_fibre` and the
general `llr_compProd_prod_split` — from "the whole AWGN MI chain-rule formula" to
just the fibre Gaussian-density joint measurability `h_meas_fibre` plus the fibre
log-density integrability `h_int_fibre_joint`. The Bayes density split, the joint
absolute continuity, both fibre/output absolute continuities and the two
**output-side** log-density integrabilities are all discharged. Everything else in
the MI chain rule (KL→integral, Fubini split, both differential-entropy
identifications, output marginal) is genuinely discharged by the general body. The
two residuals are both pinned to the single Mathlib gap (joint measurability of the
measure-form parameterized rnDeriv). -/
theorem isAwgnMIDecomp_of_densitySplit
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (hPN : P.toNNReal + N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas)
    (h_meas_fibre :
      Measurable (fun z : ℝ × ℝ => ((awgnChannel N h_meas) z.1).rnDeriv volume z.2))
    (h_int_fibre_joint :
      Integrable (fun z =>
          Real.log (((awgnChannel N h_meas) z.1).rnDeriv volume z.2).toReal)
        ((gaussianReal 0 P.toNNReal) ⊗ₘ (awgnChannel N h_meas))) :
    IsAwgnMIDecomp P N h_meas :=
  awgn_midecomp_of_cont_chain P N h_meas
    (isContChannelMIDecompHyp_awgn P N hN hPN h_meas h_out h_meas_fibre
      h_int_fibre_joint)

end InformationTheory.Shannon.AWGN
