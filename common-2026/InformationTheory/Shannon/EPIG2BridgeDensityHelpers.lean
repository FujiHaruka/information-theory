import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

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

Independent honesty audit 2026-06-05: genuine (sorryAx-free). `hPv`/`hQv`/`hPQ` are
absolute-continuity preconditions (regularity); the a.e. identity is the conclusion.
`@audit:ok` -/
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

`(klDiv P Q).toReal = − differentialEntropy P − ∫ x, (P.rnDeriv volume x).toReal · log ((Q.rnDeriv volume x).toReal) ∂volume`.

`differentialEntropy P = − ∫ p log p` and the cross-term is `∫ p log q`, so this is
`∫ p log p − ∫ p log q = ∫ p log (p/q) = ∫ llr P Q ∂P`.

The cross-term integrability `Integrable (fun x => (P.rnDeriv volume x).toReal · log ((Q.rnDeriv volume x).toReal)) volume`
is a regularity precondition (the term may otherwise be non-integrable).

Independent honesty audit 2026-06-05: genuine (sorryAx-free). All hypotheses are
regularity: `hPv`/`hQv`/`hPQ` (absolute continuity), `hmass` (equal mass — discharged at
the consumer for probability measures), `h_logp_int`/`h_cross_int` (integrability). The
density expansion is proved in-body (`toReal_klDiv_of_measure_eq` + `llr` split +
`integral_toReal_rnDeriv_mul`), not bundled. Sufficiency holds: this is a verified
equality, not an asserted bound. `@audit:ok` -/
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

Independent honesty audit 2026-06-05: genuine (sorryAx-free). `hX`/`hZ` (measurability)
and `hg_int` (integrability against `μ.map X`) are regularity preconditions; the marginal
identity is proved in-body via `compProd_map_condDistrib` + Fubini + `integral_map`.
`@audit:ok` -/
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

Independent honesty audit 2026-06-05: genuine (sorryAx-free). `hX_ac`/`hκ_ac`
(absolute continuity) and `h_logq_int` (integrability) are regularity; the density-form
identity is proved in-body (per-fibre `integral_toReal_rnDeriv_mul` +
`integral_condDistrib_marginal_eq`). `@audit:ok` -/
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

end InformationTheory.Shannon
