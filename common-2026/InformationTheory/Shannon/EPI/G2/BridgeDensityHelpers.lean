import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# EPI G2 bridge — density-expansion + Fubini-marginal helpers (sub-gaps (b), (c))

Two standalone identities feeding the assembly of the EPI G2 bridge lemma
`differentialEntropy (μ.map X) − condDifferentialEntropy X Z μ = (klDiv joint product).toReal`
(`EPIG2ConvEntropyMonotone.lean`). Both are independent of sub-gap (a) (the conditional
KL integral form, the genuine `wall:cond-diff-entropy`).

## sub-gap (b) — per-fibre density expansion

`klDiv_toReal_eq_neg_differentialEntropy_sub_cross` :
`(klDiv P Q).toReal = − differentialEntropy P − ∫ x, (P-density x) · log (Q-density x) ∂volume`,
where `P-density x := (P.rnDeriv volume x).toReal`, under `P ≪ volume`, `Q ≪ volume`,
equal mass, and cross-term integrability. This is the density-level reading of
`∫ llr P Q ∂P = ∫ p log p − ∫ p log q = −h(P) − ∫ p log q`.

## sub-gap (c) — Fubini + marginal identification

`integral_condDistrib_marginal_eq` :
`∫ z, (∫ x, g x ∂(condDistrib X Z μ z)) ∂(μ.map Z) = ∫ x, g x ∂(μ.map X)`,
i.e. averaging the `X`-fibre integral over `μ.map Z` returns the `μ.map X` integral.
The genuine core is the measure-level identity; a density-form wrapper
`integral_condDistrib_density_marginal_eq` packages the assembly's
`∫ x, (κ z -density x) · log (qX x) ∂volume` shape.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

set_option linter.unusedSectionVars false

/-! ## sub-gap (b) — per-fibre density expansion -/

/-- **Density split of `llr`**: when `P ≪ volume` and `Q ≪ volume`, the
log-likelihood ratio `llr P Q` splits, `P`-a.e., into the difference of the
two volume-densities' logarithms:
`llr P Q x = log (P-density x) − log (Q-density x)` for `P`-a.e. `x`,
where `P-density x := (P.rnDeriv volume x).toReal`.

This is `rnDeriv P Q = rnDeriv P volume / rnDeriv Q volume` (a.e.) under the chain rule,
pushed through `Real.log`.
@audit:ok -/
theorem llr_eq_log_density_sub_log_density
    (P Q : Measure ℝ) [SigmaFinite P] [SigmaFinite Q]
    (hPv : P ≪ volume) (hQv : Q ≪ volume) (hPQ : P ≪ Q) :
    llr P Q
      =ᵐ[P] fun x => Real.log ((P.rnDeriv volume x).toReal)
        - Real.log ((Q.rnDeriv volume x).toReal) := by
  -- `P.rnDeriv Q * Q.rnDeriv volume =ᵐ[volume] P.rnDeriv volume`, transferred to `P`-a.e.
  have hchain : P.rnDeriv Q * Q.rnDeriv volume =ᵐ[P] P.rnDeriv volume :=
    hPv.ae_le (Measure.rnDeriv_mul_rnDeriv hPQ)
  -- positivity / finiteness of the two derivatives, `P`-a.e.
  have hPQpos : ∀ᵐ x ∂P, 0 < P.rnDeriv Q x := Measure.rnDeriv_pos hPQ
  have hPQtop : ∀ᵐ x ∂P, P.rnDeriv Q x ≠ ∞ := hPQ.ae_le (Measure.rnDeriv_ne_top P Q)
  have hQpos : ∀ᵐ x ∂P, 0 < Q.rnDeriv volume x := hPQ.ae_le (Measure.rnDeriv_pos hQv)
  have hQtop : ∀ᵐ x ∂P, Q.rnDeriv volume x ≠ ∞ := hPv.ae_le (Measure.rnDeriv_ne_top Q volume)
  filter_upwards [hchain, hPQpos, hPQtop, hQpos, hQtop]
    with x hx hPQx hPQtopx hQx hQtopx
  -- `(P.rnDeriv volume x).toReal = (P.rnDeriv Q x).toReal * (Q.rnDeriv volume x).toReal`
  have hxR : (P.rnDeriv volume x).toReal
      = (P.rnDeriv Q x).toReal * (Q.rnDeriv volume x).toReal := by
    rw [← hx, Pi.mul_apply, ENNReal.toReal_mul]
  simp only [llr_def]
  rw [hxR, Real.log_mul (ne_of_gt (ENNReal.toReal_pos hPQx.ne' hPQtopx))
    (ne_of_gt (ENNReal.toReal_pos hQx.ne' hQtopx)), add_sub_cancel_right]

/-- **Per-fibre density expansion** (sub-gap (b)). For `P Q : Measure ℝ` with
`P ≪ volume`, `Q ≪ volume`, equal total mass `P univ = Q univ`, the real-valued
Kullback-Leibler divergence expands into minus the differential entropy of `P`
and a cross-entropy term:

`(klDiv P Q).toReal = − differentialEntropy P`
` − ∫ x, (P.rnDeriv volume x).toReal · log ((Q.rnDeriv volume x).toReal) ∂volume`.

`differentialEntropy P = − ∫ p log p` and the cross-term is `∫ p log q`, so this is
`∫ p log p − ∫ p log q = ∫ p log (p/q) = ∫ llr P Q ∂P`.

The cross-term integrability
`Integrable (fun x => (P.rnDeriv volume x).toReal · log ((Q.rnDeriv volume x).toReal)) volume`
is a regularity precondition (the term may otherwise be non-integrable).
@audit:ok -/
theorem klDiv_toReal_eq_neg_differentialEntropy_sub_cross
    (P Q : Measure ℝ) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPv : P ≪ volume) (hQv : Q ≪ volume) (hPQ : P ≪ Q)
    (hmass : P Set.univ = Q Set.univ)
    (h_logp_int : Integrable
      (fun x => (P.rnDeriv volume x).toReal * Real.log ((P.rnDeriv volume x).toReal)) volume)
    (h_cross_int : Integrable
      (fun x => (P.rnDeriv volume x).toReal * Real.log ((Q.rnDeriv volume x).toReal)) volume) :
    (klDiv P Q).toReal
      = - differentialEntropy P
        - ∫ x, (P.rnDeriv volume x).toReal * Real.log ((Q.rnDeriv volume x).toReal) ∂volume := by
  set p := fun x => (P.rnDeriv volume x).toReal with hp
  set q := fun x => (Q.rnDeriv volume x).toReal with hq
  -- Step 1: `(klDiv P Q).toReal = ∫ llr P Q ∂P` (equal mass, no integrability side-condition).
  rw [toReal_klDiv_of_measure_eq hPQ hmass]
  -- Step 2: rewrite `llr P Q` as `log p − log q`, `P`-a.e.
  rw [integral_congr_ae (llr_eq_log_density_sub_log_density P Q hPv hQv hPQ)]
  -- Step 3: push `∫ · ∂P` to `∫ p · · ∂volume`.
  rw [← integral_toReal_rnDeriv_mul (μ := P) (ν := volume) hPv]
  -- Step 4: distribute the product over the difference, then split the integral.
  have hdist : (fun x => p x * (Real.log (p x) - Real.log (q x)))
      = (fun x => p x * Real.log (p x) - p x * Real.log (q x)) := by
    funext x; ring
  rw [hdist, integral_sub h_logp_int h_cross_int]
  -- Step 5: `∫ p log p = − differentialEntropy P`.
  have hent : differentialEntropy P = -∫ x, p x * Real.log (p x) ∂volume := by
    unfold differentialEntropy
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.negMulLog_def, hp]
    ring
  rw [hent]
  ring

/-- Per-fibre balance in `ℝ≥0∞`: the sum of the differential entropy positive part `A`,
KL divergence, and cross-entropy positive part `Cpos` equals the sum of the negative parts
`B` and `Cneg`.
A subtraction-free identity used by the assembler via `lintegral_add`.
@audit:ok -/
theorem klDiv_negMulLog_cross_balance_ennreal
    (P ν : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    (hPv : P ≪ volume) (hνv : ν ≪ volume) (hPν : P ≪ ν)
    (h_logp_int : Integrable
      (fun x => (P.rnDeriv volume x).toReal * Real.log ((P.rnDeriv volume x).toReal)) volume)
    (h_cross_int : Integrable
      (fun x => (P.rnDeriv volume x).toReal * Real.log ((ν.rnDeriv volume x).toReal)) volume)
    (hKL : klDiv P ν ≠ ∞) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((P.rnDeriv volume x).toReal)) ∂volume)
      + klDiv P ν
      + (∫⁻ x, ENNReal.ofReal ((P.rnDeriv volume x).toReal
            * Real.log ((ν.rnDeriv volume x).toReal)) ∂volume)
    = (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog ((P.rnDeriv volume x).toReal))) ∂volume)
      + (∫⁻ x, ENNReal.ofReal (-((P.rnDeriv volume x).toReal
            * Real.log ((ν.rnDeriv volume x).toReal))) ∂volume) := by
  set p := fun x => (P.rnDeriv volume x).toReal with hp
  set q := fun x => (ν.rnDeriv volume x).toReal with hq
  -- A := ∫⁻ ofReal(negMulLog p), B := ∫⁻ ofReal(-(negMulLog p)),
  -- Cpos := ∫⁻ ofReal(p·log q), Cneg := ∫⁻ ofReal(-(p·log q)).
  set A := ∫⁻ x, ENNReal.ofReal (Real.negMulLog (p x)) ∂volume with hA
  set B := ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (p x))) ∂volume with hB
  set Cpos := ∫⁻ x, ENNReal.ofReal (p x * Real.log (q x)) ∂volume with hCpos
  set Cneg := ∫⁻ x, ENNReal.ofReal (-(p x * Real.log (q x))) ∂volume with hCneg
  -- Step 1: finiteness of the four lintegrals
  -- (template from `differentialEntropyExt_of_ac_integrable`).
  have hbound : ∀ (f : ℝ → ℝ), Integrable f volume →
      (∫⁻ x, ENNReal.ofReal (f x) ∂volume) ≠ ⊤ := by
    intro f hf
    refine ne_top_of_le_ne_top hf.hasFiniteIntegral.ne (lintegral_mono fun x => ?_)
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  -- `negMulLog p = -(p·log p)`, so `negMulLog ∘ p` is integrable (from `h_logp_int.neg`).
  have h_negMulLog_int : Integrable (fun x => Real.negMulLog (p x)) volume := by
    refine (h_logp_int.neg).congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Real.negMulLog_eq_neg, Pi.neg_apply, hp]
  have hAfin : A ≠ ⊤ := hbound _ h_negMulLog_int
  have hBfin : B ≠ ⊤ := hbound _ h_negMulLog_int.neg
  have hCposfin : Cpos ≠ ⊤ := hbound _ h_cross_int
  have hCnegfin : Cneg ≠ ⊤ := hbound _ h_cross_int.neg
  -- Step 2: both sides ≠ ∞.
  have hLHS_ne : A + klDiv P ν + Cpos ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hAfin, hKL⟩, hCposfin⟩
  have hRHS_ne : B + Cneg ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hBfin, hCnegfin⟩
  -- Step 3: reduce the ℝ≥0∞ equality to a `.toReal` equality.
  rw [← ENNReal.toReal_eq_toReal_iff' hLHS_ne hRHS_ne]
  -- Step 4: distribute `.toReal` over the sums.
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hAfin, hKL⟩) hCposfin,
    ENNReal.toReal_add hAfin hKL, ENNReal.toReal_add hBfin hCnegfin]
  -- Step 5: pos/neg part decomposition of the two real integrals.
  -- `∫ negMulLog p = A.toReal - B.toReal` (this also gives `differentialEntropy P`).
  have hdecomp_logp : differentialEntropy P = A.toReal - B.toReal := by
    rw [differentialEntropy]
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part h_negMulLog_int
  -- `∫ p·log q = Cpos.toReal - Cneg.toReal`.
  have hdecomp_cross : (∫ x, p x * Real.log (q x) ∂volume) = Cpos.toReal - Cneg.toReal :=
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part h_cross_int
  -- Step 6: Real sibling — `klDiv.toReal = -differentialEntropy P - ∫ p·log q`.
  have hmass : P Set.univ = ν Set.univ := by rw [measure_univ, measure_univ]
  have hKLreal : (klDiv P ν).toReal
      = - differentialEntropy P - ∫ x, p x * Real.log (q x) ∂volume :=
    klDiv_toReal_eq_neg_differentialEntropy_sub_cross P ν hPv hνv hPν hmass h_logp_int h_cross_int
  -- Step 7: close by linear arithmetic.
  rw [hKLreal, hdecomp_logp, hdecomp_cross]
  ring

/-! ## sub-gap (c) — Fubini + marginal identification -/

/-- **Fubini + `condDistrib` marginal identification** (sub-gap (c), measure-level core).
For `X : Ω → ℝ`, `Z : Ω → α` measurable and `g : ℝ → ℝ` integrable against `μ.map X`,
averaging the `X`-fibre integral of `g` over the law `μ.map Z` of `Z` returns the
`μ.map X` integral:

`∫ z, (∫ x, g x ∂(condDistrib X Z μ z)) ∂(μ.map Z) = ∫ x, g x ∂(μ.map X)`.

Proof route: `compProd_map_condDistrib` identifies `(μ.map Z) ⊗ₘ condDistrib X Z μ`
with `μ.map (fun ω => (Z ω, X ω))`; `Measure.integral_compProd` (Fubini, on
`fun p => g p.2`) opens the joint integral into the iterated fibre integral; and
`integral_map` reduces the joint integral to `∫ x, g x ∂(μ.map X)` via the second
projection.
@audit:ok -/
theorem integral_condDistrib_marginal_eq
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) {g : ℝ → ℝ}
    (hg_int : Integrable g (μ.map X)) :
    ∫ z, (∫ x, g x ∂(condDistrib X Z μ z)) ∂(μ.map Z) = ∫ x, g x ∂(μ.map X) := by
  -- The joint law `(μ.map Z) ⊗ₘ condDistrib X Z μ = μ.map (Z, X)`.
  have hjoint : (μ.map Z) ⊗ₘ condDistrib X Z μ = μ.map (fun ω => (Z ω, X ω)) :=
    compProd_map_condDistrib hX.aemeasurable
  -- The second marginal of the joint is `μ.map X`.
  have hsnd : (μ.map (fun ω => (Z ω, X ω))).map Prod.snd = μ.map X := by
    rw [Measure.map_map measurable_snd (hZ.prodMk hX)]; rfl
  -- `snd` is quasi-measure-preserving from the joint to `μ.map X`.
  have hqmp : Measure.QuasiMeasurePreserving Prod.snd
      (μ.map (fun ω => (Z ω, X ω))) (μ.map X) :=
    ⟨measurable_snd, hsnd.le.absolutelyContinuous⟩
  -- `g ∘ snd` is a.e.-strongly measurable against the joint.
  have hgsnd_meas : AEStronglyMeasurable (fun p : α × ℝ => g p.2)
      (μ.map (fun ω => (Z ω, X ω))) :=
    hg_int.aestronglyMeasurable.comp_quasiMeasurePreserving hqmp
  -- `g ∘ snd` is integrable against the joint.
  have hgsnd_int : Integrable (fun p : α × ℝ => g p.2) ((μ.map Z) ⊗ₘ condDistrib X Z μ) := by
    rw [hjoint, integrable_map_measure hgsnd_meas (hZ.prodMk hX).aemeasurable]
    exact hg_int.comp_measurable hX
  -- Fubini: open the joint integral into the iterated fibre integral.
  rw [← Measure.integral_compProd hgsnd_int]
  -- Identify the joint with `μ.map (Z, X)` and reduce via `integral_map` twice.
  rw [hjoint, integral_map (hZ.prodMk hX).aemeasurable hgsnd_meas]
  rw [← integral_map hX.aemeasurable hg_int.aestronglyMeasurable]

/-- **Density-form wrapper of sub-gap (c)**, packaging the cross-entropy shape the
assembly consumes. With `g := fun x => Real.log ((μ.map X).rnDeriv volume x).toReal`
and the per-fibre density rewrite `∫ x, g x ∂(κ z) = ∫ x, (κ z -density x) · g x ∂volume`
(needs `κ z ≪ volume` a.e. `z`), the `μ.map Z`-average of the fibre cross-integral
equals the marginal cross-integral against `μ.map X`'s own density:

`∫ z, (∫ x, (κ z -density x) · log (qX x) ∂volume) ∂(μ.map Z)`
`= ∫ x, (qX x) · log (qX x) ∂volume`,
where `qX x := ((μ.map X).rnDeriv volume x).toReal`.

`hX_ac` (`μ.map X ≪ volume`), `hκ_ac` (each fibre `condDistrib X Z μ z ≪ volume`, a.e. `z`)
and `h_logq_int` (integrability of `log qX` against `μ.map X`) are regularity
preconditions inherited from the disintegration / sub-gap (a) finiteness.
@audit:ok -/
theorem integral_condDistrib_density_marginal_eq
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z)
    (hX_ac : (μ.map X) ≪ volume)
    (hκ_ac : ∀ᵐ z ∂(μ.map Z), condDistrib X Z μ z ≪ volume)
    (h_logq_int : Integrable
      (fun x => Real.log (((μ.map X).rnDeriv volume x).toReal)) (μ.map X)) :
    ∫ z, (∫ x, ((condDistrib X Z μ z).rnDeriv volume x).toReal
            * Real.log (((μ.map X).rnDeriv volume x).toReal) ∂volume) ∂(μ.map Z)
      = ∫ x, ((μ.map X).rnDeriv volume x).toReal
            * Real.log (((μ.map X).rnDeriv volume x).toReal) ∂volume := by
  set g := fun x => Real.log (((μ.map X).rnDeriv volume x).toReal) with hg
  -- Per-fibre density rewrite: for a.e. `z`, the inner volume-integral against the
  -- fibre density equals the fibre integral of `g`.
  have hinner : ∫ z, (∫ x, ((condDistrib X Z μ z).rnDeriv volume x).toReal * g x ∂volume) ∂(μ.map Z)
      = ∫ z, (∫ x, g x ∂(condDistrib X Z μ z)) ∂(μ.map Z) := by
    refine integral_congr_ae ?_
    filter_upwards [hκ_ac] with z hz
    exact integral_toReal_rnDeriv_mul hz
  rw [hinner]
  -- Sub-gap (c) core: average of the fibre integral over `μ.map Z` is the `μ.map X` integral.
  rw [integral_condDistrib_marginal_eq X Z μ hX hZ h_logq_int]
  -- Rewrite the marginal `∫ g ∂(μ.map X)` back into the density form against `volume`.
  rw [← integral_toReal_rnDeriv_mul (μ := μ.map X) (ν := volume) hX_ac]

/-! ## sub-gap (c) — ℝ≥0∞ (finiteness-free) marginal collapse for crux ② -/

/-- **ℝ≥0∞ Fubini + `condDistrib` marginal identification** (crux ② core).
ℝ≥0∞ mirror of `integral_condDistrib_marginal_eq`: for `X : Ω → ℝ`, `Z : Ω → α`
measurable and `g : ℝ → ℝ≥0∞` measurable, averaging the `X`-fibre lintegral of `g`
over `μ.map Z` returns the `μ.map X` lintegral:

`∫⁻ z, (∫⁻ x, g x ∂(condDistrib X Z μ z)) ∂(μ.map Z) = ∫⁻ x, g x ∂(μ.map X)`.

ℝ≥0∞ Tonelli (`Measure.lintegral_compProd`) is unconditional, so unlike the `∫`/Bochner
sibling no integrability hypothesis is needed — just measurability `hg`.

Proof route: `compProd_map_condDistrib` identifies `(μ.map Z) ⊗ₘ condDistrib X Z μ`
with `μ.map (fun ω => (Z ω, X ω))`; `Measure.lintegral_compProd` (Tonelli on
`fun p => g p.2`) opens the joint lintegral into the iterated fibre lintegral; and
`lintegral_map` reduces the joint lintegral to `∫⁻ x, g x ∂(μ.map X)` via the second
projection.
@audit:ok -/
theorem lintegral_condDistrib_marginal_eq
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, (∫⁻ x, g x ∂(condDistrib X Z μ z)) ∂(μ.map Z) = ∫⁻ x, g x ∂(μ.map X) := by
  -- The joint law `(μ.map Z) ⊗ₘ condDistrib X Z μ = μ.map (Z, X)`.
  have hjoint : (μ.map Z) ⊗ₘ condDistrib X Z μ = μ.map (fun ω => (Z ω, X ω)) :=
    compProd_map_condDistrib hX.aemeasurable
  -- The second marginal of the joint is `μ.map X`.
  have hsnd : (μ.map (fun ω => (Z ω, X ω))).map Prod.snd = μ.map X := by
    rw [Measure.map_map measurable_snd (hZ.prodMk hX)]; rfl
  have hgsnd : Measurable (fun p : α × ℝ => g p.2) := hg.comp measurable_snd
  calc ∫⁻ z, (∫⁻ x, g x ∂(condDistrib X Z μ z)) ∂(μ.map Z)
      = ∫⁻ p, g p.2 ∂((μ.map Z) ⊗ₘ condDistrib X Z μ) :=
        (Measure.lintegral_compProd hgsnd).symm
    _ = ∫⁻ p, g p.2 ∂(μ.map (fun ω => (Z ω, X ω))) := by rw [hjoint]
    _ = ∫⁻ y, g y ∂((μ.map (fun ω => (Z ω, X ω))).map Prod.snd) :=
        (lintegral_map hg measurable_snd).symm
    _ = ∫⁻ x, g x ∂(μ.map X) := by rw [hsnd]

/-- **ℝ≥0∞ cross-term marginal collapse** (crux ② core, sign-parametrized).
ℝ≥0∞ mirror of `integral_condDistrib_density_marginal_eq`: the `μ.map Z`-average of the
fibre cross-lintegral `∫⁻ x, ofReal (sign (pz_x · log qX_x)) ∂volume` (where
`pz_x := (condDistrib X Z μ z -density x)`, `qX_x := (μ.map X -density x)`,
`log qX_x := Real.log qX_x`) collapses to the marginal cross-lintegral against the
`μ.map X` density.

`hsign_hom` (`sign (a * b) = a * sign b`) lets the `pz`-factor commute out of `sign`,
so `ofReal (pz · sign (log qX)) = ofReal pz · ofReal (sign (log qX))` (`ofReal_mul`,
`pz ≥ 0`) and the `pz = (κz)-density` factor is absorbed via `lintegral_rnDeriv_mul`.
The assembly instantiates `sign := id` (positive part) and `sign := Neg.neg` (negative
part). `ofReal` clips negatives to 0, so the two instantiations split the signed
cross-term into its `ℝ≥0∞` positive/negative parts.

All hypotheses are regularity preconditions (measurability, absolute continuity,
homogeneity of `sign`); the marginal collapse is the conclusion.
@audit:ok -/
theorem lintegral_condDistrib_cross_eq
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z)
    (hX_ac : (μ.map X) ≪ volume)
    (hκ_ac : ∀ᵐ z ∂(μ.map Z), condDistrib X Z μ z ≪ volume)
    (sign : ℝ → ℝ) (hsign_meas : Measurable sign)
    (hsign_hom : ∀ a b : ℝ, sign (a * b) = a * sign b) :
    ∫⁻ z, (∫⁻ x, ENNReal.ofReal (sign (((condDistrib X Z μ z).rnDeriv volume x).toReal
            * Real.log (((μ.map X).rnDeriv volume x).toReal))) ∂volume) ∂(μ.map Z)
      = ∫⁻ x, ENNReal.ofReal (sign (((μ.map X).rnDeriv volume x).toReal
            * Real.log (((μ.map X).rnDeriv volume x).toReal))) ∂volume := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  -- The `z`-free `ℝ≥0∞` factor `g x := ofReal (sign (log qX_x))`.
  set g : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (sign (Real.log (((μ.map X).rnDeriv volume x).toReal))) with hg
  have hg_meas : Measurable g := by
    refine ENNReal.measurable_ofReal.comp (hsign_meas.comp (Real.measurable_log.comp ?_))
    exact (Measure.measurable_rnDeriv (μ.map X) volume).ennreal_toReal
  -- Step 1: per-fibre density rewrite. For a.e. `z` (with `κz ≪ volume`), the inner
  -- volume-lintegral of the signed cross-term equals the fibre lintegral of `g`.
  have hfib : ∀ᵐ z ∂(μ.map Z),
      (∫⁻ x, ENNReal.ofReal (sign (((condDistrib X Z μ z).rnDeriv volume x).toReal
          * Real.log (((μ.map X).rnDeriv volume x).toReal))) ∂volume)
        = ∫⁻ x, g x ∂(condDistrib X Z μ z) := by
    filter_upwards [hκ_ac] with z hz
    -- a.e.[volume] rewrite of the integrand into `(κz).rnDeriv volume x * g x`.
    have hrw : ∀ᵐ x ∂volume,
        ENNReal.ofReal (sign (((condDistrib X Z μ z).rnDeriv volume x).toReal
            * Real.log (((μ.map X).rnDeriv volume x).toReal)))
          = (condDistrib X Z μ z).rnDeriv volume x * g x := by
      filter_upwards [Measure.rnDeriv_lt_top (condDistrib X Z μ z) volume] with x hx
      rw [hsign_hom, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hx.ne, hg]
    rw [lintegral_congr_ae hrw,
      lintegral_rnDeriv_mul hz hg_meas.aemeasurable]
  rw [lintegral_congr_ae hfib]
  -- Step 2: marginal core — average the fibre lintegral over `μ.map Z`.
  rw [lintegral_condDistrib_marginal_eq X Z μ hX hZ hg_meas]
  -- Step 3: reverse density rewrite — fold `∫⁻ g ∂(μ.map X)` back into the density form.
  rw [← lintegral_rnDeriv_mul hX_ac hg_meas.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top (μ.map X) volume] with x hx
  -- Goal: `(μ.map X).rnDeriv volume x * g x = ofReal (sign (qX · log qX))`.
  rw [hg, show (μ.map X).rnDeriv volume x = ENNReal.ofReal (((μ.map X).rnDeriv volume x).toReal)
        from (ENNReal.ofReal_toReal hx.ne).symm,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← hsign_hom,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

end InformationTheory.Shannon
