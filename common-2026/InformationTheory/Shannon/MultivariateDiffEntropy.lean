import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.InformationTheory.KullbackLeibler.Basic
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.MIChainRule

/-!
# Multivariate differential entropy and subadditivity

Common foundation for AWGN / Parallel-Gaussian output-entropy upper bounds.

## Main definitions

* `jointDifferentialEntropy` — 2-variable joint differential entropy on `Measure (ℝ × ℝ)`,
  defined as `-∫ negMulLog (dμ/dvol)` (same shape as the 1-D `differentialEntropy`).
* `jointDifferentialEntropyPi` — `n`-variable form on `Measure (Fin n → ℝ)`.

## Main statements

* `integral_log_rnDeriv_self_eq_neg` — `∫ log(dμ/dν) ∂μ = -h(μ)`.
* `jointDifferentialEntropy_le_sum_v2` — `h(X,Y) ≤ h(X) + h(Y)`.
* `jointDifferentialEntropyPi_le_sum` — `h(Yⁿ) ≤ ∑ᵢ h(Yᵢ)`.

## Implementation notes

Subadditivity follows from `KL ≥ 0` + the bridge
`(klDiv(joint ‖ ∏ marginals)).toReal = ∑ h(marginalᵢ) − h(joint)`.
The Bayes density split is established via Mathlib's `prod_withDensity₀` +
`rnDeriv_mul_rnDeriv`. The 2-variable original versions tagged
`@audit:superseded-by(...)` are kept for backward compatibility.

`pi_withDensity` (joint density = ∏ marginal densities on `Fin n → ℝ`) is absent
from Mathlib, so it is built in-tree as `pi_withDensity_fin` by
`measurePreserving_piFinSuccAbove` induction. The generic `withDensity_map_equiv`
(change-of-variables under a measurable equivalence) is also absent in Mathlib's
non-rnDeriv form and is supplied here.
-/

namespace InformationTheory.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal Real

/-! ## Definitions (Mathlib-shape-driven, mirror the 1-D `differentialEntropy`) -/

/-- **2-variable joint differential entropy.** Defined `-∫ negMulLog (dμ/dvol)` on
`Measure (ℝ × ℝ)`, identical in shape to the 1-D `differentialEntropy`, so the
existing 1-D density lemmas apply through `volume_eq_prod` (which holds by `rfl`). -/
noncomputable def jointDifferentialEntropy (μ : Measure (ℝ × ℝ)) : ℝ :=
  ∫ z, Real.negMulLog ((μ.rnDeriv volume z).toReal) ∂volume

/-- **`n`-variable joint differential entropy** on `Measure (Fin n → ℝ)` (the
parallel-Gaussian consumer form). `Fin n → ℝ` is chosen over `EuclideanSpace`
so that the product-Lebesgue API (`volume_pi`, `Measure.pi`) applies directly. -/
noncomputable def jointDifferentialEntropyPi {n : ℕ} (μ : Measure (Fin n → ℝ)) : ℝ :=
  ∫ z, Real.negMulLog ((μ.rnDeriv volume z).toReal) ∂volume

/-! ## Reusable core: `∫ log(dμ/dν) ∂μ = -∫ negMulLog(dμ/dν) ∂ν` -/

/-- For `μ ≪ ν`, `∫ x, log((μ.rnDeriv ν x).toReal) ∂μ = -∫ x, negMulLog((μ.rnDeriv ν x).toReal) ∂ν`.

The RHS is the (joint/1-D) differential entropy when `ν` is the relevant Lebesgue measure. -/
theorem integral_log_rnDeriv_self_eq_neg
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) :
    ∫ x, Real.log ((μ.rnDeriv ν x).toReal) ∂μ
      = -∫ x, Real.negMulLog ((μ.rnDeriv ν x).toReal) ∂ν := by
  -- pull the integral against `μ` back to `ν` via the Radon-Nikodym change of variables
  have h_pull : ∫ x, Real.log ((μ.rnDeriv ν x).toReal) ∂μ
      = ∫ x, (μ.rnDeriv ν x).toReal • Real.log ((μ.rnDeriv ν x).toReal) ∂ν :=
    (integral_rnDeriv_smul (μ := μ) (ν := ν) hμν
      (f := fun x ↦ Real.log ((μ.rnDeriv ν x).toReal))).symm
  rw [h_pull, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x ↦ ?_))
  simp only [smul_eq_mul, Real.negMulLog_def]
  ring

/-! ## Generic `withDensity` change-of-variables under a measurable equivalence -/

/-- **Generic `withDensity_map` (Mathlib absent, rnDeriv-version de-specialized).**
Pushforward of a `withDensity` measure along a measurable equivalence `e`:
`(μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm)`. Mathlib only ships
the rnDeriv-specialized `MeasurableEmbedding.map_withDensity_rnDeriv`; the generic
form below de-specializes its 5-line proof, replacing the final `rnDeriv_map`
congruence by the trivial `e.symm_apply_apply` cancellation.
@audit:ok -/
theorem withDensity_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} (e : α ≃ᵐ β) {g : α → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity g).map e = (μ.map e).withDensity (g ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    setLIntegral_map hs (hg.comp e.symm.measurable) e.measurable]
  refine setLIntegral_congr_fun (e.measurable hs) (fun x _ ↦ ?_)
  simp [Function.comp, e.symm_apply_apply]

/-! ## 2-variable bridge + subadditivity -/

/-- 2-variable subadditivity bridge:
`(klDiv(joint ‖ μ_X ⊗ μ_Y)).toReal = h(μ_X) + h(μ_Y) − h(joint)`.

Hypotheses: absolute continuity + Bayes llr split `h_llr_split` + integrability.
Superseded by `klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2`, which internalizes the split.

`@audit:superseded-by(klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2)` -/
theorem klDiv_prod_marginals_toReal_eq_sum_sub_joint
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume)
    (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd))
    -- honest Bayes density split: `llr(joint ‖ ∏ marg) =
    -- log(joint) − log(margX) − log(margY)`, i.e. `log(d joint / d∏marg)`.
    (h_llr_split :
      (fun z ↦ llr μ ((μ.map Prod.fst).prod (μ.map Prod.snd)) z)
        =ᵐ[μ]
      (fun z ↦ Real.log ((μ.rnDeriv volume z).toReal)
                  - Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)
                  - Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)))
    -- integrability of the three log-density pieces against the joint
    (h_int_fst :
      Integrable (fun z ↦ Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)) μ)
    (h_int_snd :
      Integrable (fun z ↦ Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)) μ)
    (h_int_joint :
      Integrable (fun z ↦ Real.log ((μ.rnDeriv volume z).toReal)) μ)
    -- marginal-side integrability for the Fubini reductions
    (h_int_fst_marg :
      Integrable (fun x ↦ Real.log (((μ.map Prod.fst).rnDeriv volume x).toReal))
        (μ.map Prod.fst))
    (h_int_snd_marg :
      Integrable (fun y ↦ Real.log (((μ.map Prod.snd).rnDeriv volume y).toReal))
        (μ.map Prod.snd)) :
    (klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))).toReal
      = differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd)
        - jointDifferentialEntropy μ := by
  classical
  set μX := μ.map Prod.fst with hμX
  set μY := μ.map Prod.snd with hμY
  haveI : IsProbabilityMeasure μX := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure μY := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  -- abbreviations for the three log-density observables
  set Lfst : ℝ × ℝ → ℝ := fun z ↦ Real.log ((μX.rnDeriv volume z.1).toReal) with hLfst
  set Lsnd : ℝ × ℝ → ℝ := fun z ↦ Real.log ((μY.rnDeriv volume z.2).toReal) with hLsnd
  set Ljoint : ℝ × ℝ → ℝ := fun z ↦ Real.log ((μ.rnDeriv volume z).toReal) with hLjoint
  -- step 1 : KL → llr integral (toReal_klDiv_of_measure_eq, univ = 1 both sides)
  have h_univ : μ Set.univ = (μX.prod μY) Set.univ := by rw [measure_univ, measure_univ]
  have h_kl : (klDiv μ (μX.prod μY)).toReal = ∫ z, llr μ (μX.prod μY) z ∂μ :=
    toReal_klDiv_of_measure_eq h_joint_ac h_univ
  -- step 2 : Bayes density split
  have h_split : ∫ z, llr μ (μX.prod μY) z ∂μ
      = ∫ z, (Ljoint z - Lfst z - Lsnd z) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [h_llr_split] with z hz using hz
  -- step 3 : split into three joint integrals
  have h_add : ∫ z, (Ljoint z - Lfst z - Lsnd z) ∂μ
      = (∫ z, Ljoint z ∂μ) - (∫ z, Lfst z ∂μ) - (∫ z, Lsnd z ∂μ) := by
    have h1 : ∫ z, (Ljoint z - Lfst z - Lsnd z) ∂μ
        = (∫ z, (Ljoint z - Lfst z) ∂μ) - (∫ z, Lsnd z ∂μ) :=
      integral_sub (h_int_joint.sub h_int_fst) h_int_snd
    have h2 : ∫ z, (Ljoint z - Lfst z) ∂μ = (∫ z, Ljoint z ∂μ) - (∫ z, Lfst z ∂μ) :=
      integral_sub h_int_joint h_int_fst
    rw [h1, h2]
  -- step 4 : fst term = − h(μX)  (marginal id via integral_map, then generic helper)
  have h_fst : ∫ z, Lfst z ∂μ = -differentialEntropy μX := by
    have h_marg : ∫ z, Lfst z ∂μ
        = ∫ x, Real.log ((μX.rnDeriv volume x).toReal) ∂μX := by
      rw [hμX, integral_map measurable_fst.aemeasurable h_int_fst_marg.aestronglyMeasurable]
    rw [h_marg, integral_log_rnDeriv_self_eq_neg h_fst_ac, differentialEntropy]
  -- step 5 : snd term = − h(μY)
  have h_snd : ∫ z, Lsnd z ∂μ = -differentialEntropy μY := by
    have h_marg : ∫ z, Lsnd z ∂μ
        = ∫ y, Real.log ((μY.rnDeriv volume y).toReal) ∂μY := by
      rw [hμY, integral_map measurable_snd.aemeasurable h_int_snd_marg.aestronglyMeasurable]
    rw [h_marg, integral_log_rnDeriv_self_eq_neg h_snd_ac, differentialEntropy]
  -- step 6 : joint term = − h(joint)
  have hμ_ac : μ ≪ (volume : Measure (ℝ × ℝ)) := by
    -- μ ≪ μX.prod μY ≪ volume.prod volume = volume
    refine h_joint_ac.trans ?_
    rw [Measure.volume_eq_prod]
    exact h_fst_ac.prod h_snd_ac
  have h_jt : ∫ z, Ljoint z ∂μ = -jointDifferentialEntropy μ := by
    rw [jointDifferentialEntropy, integral_log_rnDeriv_self_eq_neg
      (μ := μ) (ν := (volume : Measure (ℝ × ℝ))) hμ_ac]
  -- combine
  rw [h_kl, h_split, h_add, h_fst, h_snd, h_jt]
  ring

/-- **★ 2-variable differential-entropy subadditivity** `h(X,Y) ≤ h(X) + h(Y)`.

Requires an explicit `h_llr_split` hypothesis for the Bayes density split.
Superseded by `jointDifferentialEntropy_le_sum_v2`, which internalizes the split.

`@audit:superseded-by(jointDifferentialEntropy_le_sum_v2)` -/
theorem jointDifferentialEntropy_le_sum
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume)
    (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd))
    (h_llr_split :
      (fun z ↦ llr μ ((μ.map Prod.fst).prod (μ.map Prod.snd)) z)
        =ᵐ[μ]
      (fun z ↦ Real.log ((μ.rnDeriv volume z).toReal)
                  - Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)
                  - Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)))
    (h_int_fst :
      Integrable (fun z ↦ Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)) μ)
    (h_int_snd :
      Integrable (fun z ↦ Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)) μ)
    (h_int_joint :
      Integrable (fun z ↦ Real.log ((μ.rnDeriv volume z).toReal)) μ)
    (h_int_fst_marg :
      Integrable (fun x ↦ Real.log (((μ.map Prod.fst).rnDeriv volume x).toReal))
        (μ.map Prod.fst))
    (h_int_snd_marg :
      Integrable (fun y ↦ Real.log (((μ.map Prod.snd).rnDeriv volume y).toReal))
        (μ.map Prod.snd)) :
    jointDifferentialEntropy μ
      ≤ differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd) := by
  have h_nn : (0 : ℝ) ≤ (klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))).toReal :=
    ENNReal.toReal_nonneg
  have h_bridge := klDiv_prod_marginals_toReal_eq_sum_sub_joint
    h_fst_ac h_snd_ac h_joint_ac h_llr_split h_int_fst h_int_snd h_int_joint
    h_int_fst_marg h_int_snd_marg
  linarith [h_nn, h_bridge]

/-! ## `n`-variable bridge + subadditivity -/

/-- **`pi_withDensity` (Mathlib absent, built by `piFinSuccAbove` induction).**
The product measure of `withDensity` factors is the `withDensity` of the product
measure with the product density `z ↦ ∏ᵢ fᵢ (z i)`. Specialized to `Fin n → ℝ`
(all factors on `ℝ`), the form the `n`-variable density split requires.
@audit:ok -/
theorem pi_withDensity_fin {n : ℕ} (ν : Fin n → Measure ℝ) [∀ i, SigmaFinite (ν i)]
    {f : Fin n → ℝ → ℝ≥0∞} (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((ν i).withDensity (f i))] :
    Measure.pi (fun i ↦ (ν i).withDensity (f i))
      = (Measure.pi ν).withDensity (fun z ↦ ∏ i, f i (z i)) := by
  induction n with
  | zero =>
    -- both sides are the unique measure on `Fin 0 → ℝ`; the density is `1`
    have h_emp : (fun z : Fin 0 → ℝ ↦ ∏ i, f i (z i)) = (1 : (Fin 0 → ℝ) → ℝ≥0∞) := by
      funext z; simp
    rw [h_emp, withDensity_one]
    congr 1
    funext i
    exact i.elim0
  | succ m ih =>
    classical
    -- reshape `Fin (m+1) → ℝ` as `ℝ × (Fin m → ℝ)` via `piFinSuccAbove 0`
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0 with he
    -- `ν` restricted to the `succAbove 0` tail
    set νr : Fin m → Measure ℝ := fun j ↦ ν (Fin.succAbove 0 j) with hνr
    haveI : ∀ j, SigmaFinite (νr j) := fun j ↦ inferInstanceAs (SigmaFinite (ν _))
    set fr : Fin m → ℝ → ℝ≥0∞ := fun j ↦ f (Fin.succAbove 0 j) with hfr
    have hfr_meas : ∀ j, Measurable (fr j) := fun j ↦ hf _
    haveI : ∀ j, SigmaFinite ((νr j).withDensity (fr j)) :=
      fun j ↦ inferInstanceAs (SigmaFinite ((ν _).withDensity (f _)))
    -- the product density is measurable
    have hprod_meas : Measurable (fun z : Fin (m + 1) → ℝ ↦ ∏ i, f i (z i)) :=
      Finset.measurable_prod _ (fun i _ ↦ (hf i).comp (measurable_pi_apply i))
    -- it suffices to prove equality after pushing forward along the equiv `e`
    refine MeasurableEquiv.map_measurableEquiv_injective e ?_
    -- LHS pushed forward: measurePreserving + IH + prod_withDensity
    have h_mp : (Measure.pi (fun i ↦ (ν i).withDensity (f i))).map e
        = ((ν 0).withDensity (f 0)).prod (Measure.pi (fun j ↦ (νr j).withDensity (fr j))) :=
      (measurePreserving_piFinSuccAbove (fun i ↦ (ν i).withDensity (f i)) 0).map_eq
    have h_lhs : (Measure.pi (fun i ↦ (ν i).withDensity (f i))).map e
        = ((ν 0).withDensity (f 0)).prod
            ((Measure.pi νr).withDensity (fun z ↦ ∏ j, fr j (z j))) := by
      rw [h_mp, ih νr hfr_meas]
    rw [h_lhs]
    -- RHS pushed forward: withDensity_map_equiv + measurePreserving
    have h_pi_mp : (Measure.pi ν).map e = (ν 0).prod (Measure.pi νr) :=
      (measurePreserving_piFinSuccAbove ν 0).map_eq
    have h_rhs : ((Measure.pi ν).withDensity (fun z ↦ ∏ i, f i (z i))).map e
        = ((ν 0).prod (Measure.pi νr)).withDensity
            ((fun z ↦ ∏ i, f i (z i)) ∘ e.symm) := by
      rw [withDensity_map_equiv e hprod_meas, h_pi_mp]
    rw [h_rhs]
    -- fuse the two `withDensity`s on the LHS via `prod_withDensity`
    have hf0 : Measurable (f 0) := hf 0
    have hprodr : Measurable (fun z : Fin m → ℝ ↦ ∏ j, fr j (z j)) :=
      Finset.measurable_prod _ (fun j _ ↦ (hfr_meas j).comp (measurable_pi_apply j))
    rw [prod_withDensity hf0 hprodr]
    -- match the two densities
    congr 1
    funext p
    -- `e.symm p = Fin.insertNth 0 p.1 p.2`; split the product at the `0` coordinate
    show f 0 p.1 * (∏ j, fr j (p.2 j)) = ∏ i, f i (e.symm p i)
    rw [Fin.prod_univ_succAbove _ 0]
    have h_symm : ⇑(e.symm) = fun q : ℝ × (Fin m → ℝ) ↦ Fin.insertNth 0 q.1 q.2 := by
      rfl
    rw [h_symm]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, hfr]

/-- `n`-variable product-marginals factorization: `Measure.pi (μ.map (· i))`
expressed as a `withDensity` on Lebesgue measure with product density
`z ↦ ∏ᵢ (μ.map (· i)).rnDeriv volume (z i)`.
@audit:ok -/
theorem pi_marginals_eq_volume_withDensity
    {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μ.map (fun z ↦ z i))]
    (h_marg_ac : ∀ i, (μ.map (fun z ↦ z i)) ≪ volume) :
    Measure.pi (fun i ↦ μ.map (fun z ↦ z i))
      = (volume : Measure (Fin n → ℝ)).withDensity
          (fun z ↦ ∏ i, (μ.map (fun z ↦ z i)).rnDeriv volume (z i)) := by
  -- rewrite each marginal as `volume.withDensity (rnDeriv ·)`
  have h_each : (fun i ↦ μ.map (fun z ↦ z i))
      = fun i ↦ (volume : Measure ℝ).withDensity ((μ.map (fun z ↦ z i)).rnDeriv volume) := by
    funext i
    exact (Measure.withDensity_rnDeriv_eq _ _ (h_marg_ac i)).symm
  rw [h_each]
  rw [pi_withDensity_fin (fun _ ↦ (volume : Measure ℝ))
        (f := fun i ↦ (μ.map (fun z ↦ z i)).rnDeriv volume)
        (fun i ↦ Measure.measurable_rnDeriv _ _)]
  rw [← volume_pi]

/-- `n`-variable LLR split (a.e.[μ]): the log-likelihood ratio of `μ` against
the product of its marginals equals `log(joint density) − ∑ᵢ log(marginalᵢ density)`
almost-everywhere wrt `μ`. The `n`-variable analogue of `llr_split_from_density_factorize`.
@audit:ok -/
theorem llr_split_from_density_factorize_pi
    {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μ.map (fun z ↦ z i))]
    (h_marg_ac : ∀ i, (μ.map (fun z ↦ z i)) ≪ volume)
    (hμ_ac : μ ≪ (volume : Measure (Fin n → ℝ)))
    (h_joint_ac : μ ≪ Measure.pi (fun i ↦ μ.map (fun z ↦ z i))) :
    (fun z ↦ llr μ (Measure.pi (fun i ↦ μ.map (fun z ↦ z i))) z)
      =ᵐ[μ]
    (fun z ↦ Real.log ((μ.rnDeriv volume z).toReal)
                - ∑ i, Real.log (((μ.map (fun z ↦ z i)).rnDeriv volume (z i)).toReal)) := by
  classical
  set μi : Fin n → Measure ℝ := fun i ↦ μ.map (fun z ↦ z i) with hμi
  set ρ := Measure.pi (fun i ↦ μ.map (fun z ↦ z i)) with hρ
  haveI : IsProbabilityMeasure ρ := by rw [hρ]; infer_instance
  -- factorize ρ as `volume.withDensity g`
  set g : (Fin n → ℝ) → ℝ≥0∞ :=
    fun z ↦ ∏ i, (μ.map (fun z ↦ z i)).rnDeriv volume (z i) with hg
  have h_ρ_eq : ρ = (volume : Measure (Fin n → ℝ)).withDensity g := by
    rw [hρ, hg]; exact pi_marginals_eq_volume_withDensity h_marg_ac
  -- Step A: chain rule `μ.rnDeriv ρ · ρ.rnDeriv vol =ᵐ[vol] μ.rnDeriv vol`
  have h_chain_vol : (fun z ↦ μ.rnDeriv ρ z * ρ.rnDeriv volume z)
      =ᵐ[(volume : Measure (Fin n → ℝ))] (fun z ↦ μ.rnDeriv volume z) :=
    Measure.rnDeriv_mul_rnDeriv (μ := μ) (ν := ρ)
      (κ := (volume : Measure (Fin n → ℝ))) h_joint_ac
  -- Step B: ρ.rnDeriv vol =ᵐ[vol] g
  have h_g_meas : Measurable g :=
    Finset.measurable_prod _
      (fun i _ ↦ (Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply i))
  have h_ρ_rnDeriv : ρ.rnDeriv volume =ᵐ[(volume : Measure (Fin n → ℝ))] g := by
    rw [h_ρ_eq]
    exact Measure.rnDeriv_withDensity (volume : Measure (Fin n → ℝ)) h_g_meas
  -- Step C: `μ.rnDeriv ρ · g =ᵐ[vol] μ.rnDeriv vol`
  have h_prod_vol : (fun z ↦ μ.rnDeriv ρ z * g z)
      =ᵐ[(volume : Measure (Fin n → ℝ))] (fun z ↦ μ.rnDeriv volume z) := by
    filter_upwards [h_chain_vol, h_ρ_rnDeriv] with z h1 h2
    rw [← h1, h2]
  -- Step D: pull `=ᵐ[vol]` to `=ᵐ[μ]`
  have h_prod_μ : (fun z ↦ μ.rnDeriv ρ z * g z)
      =ᵐ[μ] (fun z ↦ μ.rnDeriv volume z) := hμ_ac.ae_le h_prod_vol
  -- a.e.[μ] positivity / finiteness
  have h_rnD_ρ_pos : ∀ᵐ z ∂μ, μ.rnDeriv ρ z ≠ 0 := by
    filter_upwards [Measure.rnDeriv_pos h_joint_ac] with z hz using hz.ne'
  have h_rnD_ρ_ne_top : ∀ᵐ z ∂μ, μ.rnDeriv ρ z ≠ ∞ :=
    h_joint_ac.ae_le (Measure.rnDeriv_ne_top μ ρ)
  have h_rnD_vol_pos : ∀ᵐ z ∂μ, μ.rnDeriv volume z ≠ 0 := by
    filter_upwards [Measure.rnDeriv_pos hμ_ac] with z hz using hz.ne'
  have h_rnD_vol_ne_top : ∀ᵐ z ∂μ, μ.rnDeriv volume z ≠ ∞ :=
    hμ_ac.ae_le (Measure.rnDeriv_ne_top μ volume)
  -- marginal-side positivity / finiteness a.e.[μ], pushed forward per coordinate
  have h_marg_pos : ∀ i, ∀ᵐ z ∂μ, (μ.map (fun z ↦ z i)).rnDeriv volume (z i) ≠ 0 := by
    intro i
    set mi : (Fin n → ℝ) → ℝ := fun z ↦ z i with hmi
    set q : ℝ → Prop := fun x ↦ (μ.map mi).rnDeriv volume x ≠ 0 with hq
    have hmeas_q : MeasurableSet {x | q x} :=
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl
    have h_marg : ∀ᵐ x ∂(μ.map mi), q x := by
      filter_upwards [Measure.rnDeriv_pos (h_marg_ac i)] with x hx using hx.ne'
    exact (ae_map_iff (f := mi) (measurable_pi_apply i).aemeasurable hmeas_q).mp h_marg
  have h_marg_ne_top : ∀ i, ∀ᵐ z ∂μ, (μ.map (fun z ↦ z i)).rnDeriv volume (z i) ≠ ∞ := by
    intro i
    set mi : (Fin n → ℝ) → ℝ := fun z ↦ z i with hmi
    set q : ℝ → Prop := fun x ↦ (μ.map mi).rnDeriv volume x ≠ ∞ with hq
    have hmeas_q : MeasurableSet {x | q x} :=
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl
    have h_marg : ∀ᵐ x ∂(μ.map mi), q x :=
      (h_marg_ac i).ae_le (Measure.rnDeriv_ne_top _ volume)
    exact (ae_map_iff (f := mi) (measurable_pi_apply i).aemeasurable hmeas_q).mp h_marg
  -- collect the per-coordinate facts into universally-quantified ae statements
  have h_all_pos : ∀ᵐ z ∂μ, ∀ i, (μ.map (fun z ↦ z i)).rnDeriv volume (z i) ≠ 0 :=
    ae_all_iff.mpr h_marg_pos
  have h_all_ne_top : ∀ᵐ z ∂μ, ∀ i, (μ.map (fun z ↦ z i)).rnDeriv volume (z i) ≠ ∞ :=
    ae_all_iff.mpr h_marg_ne_top
  -- combine pointwise
  filter_upwards [h_prod_μ, h_rnD_ρ_pos, h_rnD_ρ_ne_top, h_rnD_vol_pos,
    h_rnD_vol_ne_top, h_all_pos, h_all_ne_top]
    with z h_eq h_ρ_ne0 h_ρ_neT h_vol_ne0 h_vol_neT h_X_ne0 h_X_neT
  -- `g z = ∏ i, μi.rnDeriv vol (z i)` is finite and nonzero
  have h_g_ne_top : g z ≠ ∞ := by
    rw [hg]; exact ENNReal.prod_ne_top (fun i _ ↦ h_X_neT i)
  have h_g_ne_zero : g z ≠ 0 := by
    rw [hg]; exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h_X_ne0 i)
  -- take toReal of `h_eq`
  have h_eq_real : (μ.rnDeriv ρ z).toReal * (g z).toReal = (μ.rnDeriv volume z).toReal := by
    have := congrArg ENNReal.toReal h_eq
    simpa [ENNReal.toReal_mul] using this
  have h_ρ_pos_real : 0 < (μ.rnDeriv ρ z).toReal := ENNReal.toReal_pos h_ρ_ne0 h_ρ_neT
  have h_g_pos_real : 0 < (g z).toReal := ENNReal.toReal_pos h_g_ne_zero h_g_ne_top
  -- take log
  have h_log : Real.log ((μ.rnDeriv ρ z).toReal) + Real.log ((g z).toReal)
      = Real.log ((μ.rnDeriv volume z).toReal) := by
    rw [← Real.log_mul h_ρ_pos_real.ne' h_g_pos_real.ne', h_eq_real]
  -- expand `log (g z).toReal = ∑ i, log (μi.rnDeriv vol (z i)).toReal`
  have h_log_g : Real.log ((g z).toReal)
      = ∑ i, Real.log (((μ.map (fun z ↦ z i)).rnDeriv volume (z i)).toReal) := by
    rw [hg, ENNReal.toReal_prod, Real.log_prod]
    intro i _
    exact (ENNReal.toReal_pos (h_X_ne0 i) (h_X_neT i)).ne'
  -- conclude: `llr μ ρ z = log (μ.rnDeriv ρ z).toReal`
  show Real.log ((μ.rnDeriv ρ z).toReal) = _
  linarith [h_log, h_log_g]

/-- `n`-variable subadditivity bridge:
`(klDiv(joint ‖ ∏ᵢ μᵢ)).toReal = ∑ᵢ h(μᵢ) − h(joint)`, where `μᵢ := μ.map (· i)`.

Regularity hypotheses: absolute continuity + Bochner integrability of log-density observables.
@audit:ok -/
theorem klDiv_pi_marginals_toReal_eq_sum_sub_joint
    {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μ.map (fun z ↦ z i))]
    (h_marg_ac : ∀ i, (μ.map (fun z ↦ z i)) ≪ volume)
    (hμ_ac : μ ≪ (volume : Measure (Fin n → ℝ)))
    (h_joint_ac : μ ≪ Measure.pi (fun i ↦ μ.map (fun z ↦ z i)))
    -- integrability of the joint log-density piece against the joint
    (h_int_joint :
      Integrable (fun z ↦ Real.log ((μ.rnDeriv volume z).toReal)) μ)
    -- integrability of each marginal log-density piece against the joint
    (h_int_marg : ∀ i,
      Integrable (fun z ↦ Real.log (((μ.map (fun z ↦ z i)).rnDeriv volume (z i)).toReal)) μ) :
    (klDiv μ (Measure.pi (fun i ↦ μ.map (fun z ↦ z i)))).toReal
      = (∑ i, differentialEntropy (μ.map (fun z ↦ z i))) - jointDifferentialEntropyPi μ := by
  classical
  set ρ := Measure.pi (fun i ↦ μ.map (fun z ↦ z i)) with hρ
  haveI : IsProbabilityMeasure ρ := by rw [hρ]; infer_instance
  -- marginal-side integrability derived from the joint-side hypothesis via
  -- `integrable_map_measure` (the joint-side piece is `g ∘ (· i)`, the marginal
  -- being `μ.map (· i)`), so it is *not* an extra honest assumption.
  have h_int_marg_self : ∀ i,
      Integrable (fun x ↦ Real.log (((μ.map (fun z ↦ z i)).rnDeriv volume x).toReal))
        (μ.map (fun z ↦ z i)) := by
    intro i
    have h_aesm : AEStronglyMeasurable
        (fun x ↦ Real.log (((μ.map (fun z ↦ z i)).rnDeriv volume x).toReal))
        (μ.map (fun z ↦ z i)) :=
      ((Real.measurable_log.comp
        (Measure.measurable_rnDeriv _ _).ennreal_toReal).aestronglyMeasurable)
    exact (integrable_map_measure h_aesm (measurable_pi_apply i).aemeasurable).mpr (h_int_marg i)
  -- abbreviations for the log-density observables
  set Lmarg : Fin n → (Fin n → ℝ) → ℝ :=
    fun i z ↦ Real.log (((μ.map (fun z ↦ z i)).rnDeriv volume (z i)).toReal) with hLmarg
  set Ljoint : (Fin n → ℝ) → ℝ := fun z ↦ Real.log ((μ.rnDeriv volume z).toReal) with hLjoint
  -- step 1 : KL → llr integral
  have h_univ : μ Set.univ = ρ Set.univ := by rw [measure_univ, measure_univ]
  have h_kl : (klDiv μ ρ).toReal = ∫ z, llr μ ρ z ∂μ :=
    toReal_klDiv_of_measure_eq h_joint_ac h_univ
  -- step 2 : Bayes density split (delegated to the independent split lemma)
  have h_split : ∫ z, llr μ ρ z ∂μ
      = ∫ z, (Ljoint z - ∑ i, Lmarg i z) ∂μ := by
    refine integral_congr_ae ?_
    have := llr_split_from_density_factorize_pi h_marg_ac hμ_ac h_joint_ac
    filter_upwards [this] with z hz using hz
  -- step 3 : split into joint integral minus sum of marginal integrals
  have h_add : ∫ z, (Ljoint z - ∑ i, Lmarg i z) ∂μ
      = (∫ z, Ljoint z ∂μ) - ∑ i, (∫ z, Lmarg i z ∂μ) := by
    rw [integral_sub h_int_joint (integrable_finsetSum _ (fun i _ ↦ h_int_marg i))]
    rw [integral_finsetSum _ (fun i _ ↦ h_int_marg i)]
  -- step 4 : each marginal term = − h(μᵢ)  (marginal id via integral_map + generic core)
  have h_marg_term : ∀ i, ∫ z, Lmarg i z ∂μ = -differentialEntropy (μ.map (fun z ↦ z i)) := by
    intro i
    have h_marg : ∫ z, Lmarg i z ∂μ
        = ∫ x, Real.log (((μ.map (fun z ↦ z i)).rnDeriv volume x).toReal)
            ∂(μ.map (fun z ↦ z i)) := by
      rw [hLmarg]
      simp only
      rw [integral_map (measurable_pi_apply i).aemeasurable
        (h_int_marg_self i).aestronglyMeasurable]
    rw [h_marg, integral_log_rnDeriv_self_eq_neg (h_marg_ac i), differentialEntropy]
  -- step 5 : joint term = − h(joint)
  have h_jt : ∫ z, Ljoint z ∂μ = -jointDifferentialEntropyPi μ := by
    rw [jointDifferentialEntropyPi, hLjoint]
    simp only
    rw [integral_log_rnDeriv_self_eq_neg (μ := μ) (ν := (volume : Measure (Fin n → ℝ))) hμ_ac]
  -- combine
  rw [h_kl, h_split, h_add, h_jt]
  simp only [h_marg_term]
  rw [Finset.sum_neg_distrib]
  ring

/-- **★ `n`-variable differential-entropy subadditivity** `h(Yⁿ) ≤ ∑ᵢ h(Yᵢ)`
(the parallel-Gaussian consumer form). `KL ≥ 0` + the bridge, by `linarith`.
@audit:ok -/
@[entry_point]
theorem jointDifferentialEntropyPi_le_sum
    {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μ.map (fun z ↦ z i))]
    (h_marg_ac : ∀ i, (μ.map (fun z ↦ z i)) ≪ volume)
    (hμ_ac : μ ≪ (volume : Measure (Fin n → ℝ)))
    (h_joint_ac : μ ≪ Measure.pi (fun i ↦ μ.map (fun z ↦ z i)))
    (h_int_joint :
      Integrable (fun z ↦ Real.log ((μ.rnDeriv volume z).toReal)) μ)
    (h_int_marg : ∀ i,
      Integrable (fun z ↦ Real.log (((μ.map (fun z ↦ z i)).rnDeriv volume (z i)).toReal)) μ) :
    jointDifferentialEntropyPi μ
      ≤ ∑ i, differentialEntropy (μ.map (fun z ↦ z i)) := by
  have h_nn : (0 : ℝ) ≤ (klDiv μ (Measure.pi (fun i ↦ μ.map (fun z ↦ z i)))).toReal :=
    ENNReal.toReal_nonneg
  have h_bridge := klDiv_pi_marginals_toReal_eq_sum_sub_joint
    h_marg_ac hμ_ac h_joint_ac h_int_joint h_int_marg
  linarith [h_nn, h_bridge]

/-! ## 2-variable Bayes density split

The `_v2` family below discharges the `h_llr_split` hypothesis of the
original `klDiv_prod_marginals_toReal_eq_sum_sub_joint` and
`jointDifferentialEntropy_le_sum` via Mathlib's `prod_withDensity` +
`rnDeriv_mul_rnDeriv`. -/

/-- Product of marginals expressed as a `withDensity` on Lebesgue measure.

For a joint probability measure `μ` on `ℝ × ℝ` with marginals `μX, μY` both absolutely
continuous wrt the Lebesgue measure, the product `μX × μY` factors through the
Lebesgue measure on `ℝ × ℝ` as
`(μX).prod (μY) = volume.withDensity (z ↦ μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2)`. -/
theorem prod_marginals_eq_volume_withDensity
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume) :
    (μ.map Prod.fst).prod (μ.map Prod.snd)
      = (volume : Measure (ℝ × ℝ)).withDensity
          (fun z ↦ (μ.map Prod.fst).rnDeriv volume z.1
                      * (μ.map Prod.snd).rnDeriv volume z.2) := by
  haveI : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  -- rewrite each marginal as `volume.withDensity (rnDeriv ·)`
  conv_lhs =>
    rw [← Measure.withDensity_rnDeriv_eq _ _ h_fst_ac,
        ← Measure.withDensity_rnDeriv_eq _ _ h_snd_ac]
  -- fuse the two `withDensity`s via `prod_withDensity₀`
  rw [prod_withDensity₀ (Measure.measurable_rnDeriv _ _).aemeasurable
        (Measure.measurable_rnDeriv _ _).aemeasurable]
  -- `volume.prod volume = (volume : Measure (ℝ × ℝ))` (definitional)
  rw [← Measure.volume_eq_prod]

/-- Log-likelihood ratio split for the 2-variable joint (a.e.[μ]).

The LLR of `μ` against the product of its marginals equals
`log(joint density) − log(marginal_X density on z.1) − log(marginal_Y density on z.2)`
almost-everywhere wrt `μ`. -/
theorem llr_split_from_density_factorize
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume)
    (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd)) :
    (fun z ↦ llr μ ((μ.map Prod.fst).prod (μ.map Prod.snd)) z)
      =ᵐ[μ]
    (fun z ↦ Real.log ((μ.rnDeriv volume z).toReal)
                - Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)
                - Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)) := by
  classical
  set μX := μ.map Prod.fst with hμX
  set μY := μ.map Prod.snd with hμY
  haveI : IsProbabilityMeasure μX :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure μY :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  set ρ := μX.prod μY with hρ
  -- factorize ρ as `volume.withDensity g`
  set g : ℝ × ℝ → ℝ≥0∞ :=
    fun z ↦ μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2 with hg
  have h_ρ_eq : ρ = (volume : Measure (ℝ × ℝ)).withDensity g := by
    rw [hρ, hg]; exact prod_marginals_eq_volume_withDensity h_fst_ac h_snd_ac
  -- μ ≪ volume (via μ ≪ ρ ≪ vol.prod vol = vol)
  have hμ_vol : μ ≪ (volume : Measure (ℝ × ℝ)) := by
    refine h_joint_ac.trans ?_
    rw [Measure.volume_eq_prod]
    exact h_fst_ac.prod h_snd_ac
  -- Step A: chain rule `μ.rnDeriv ρ · ρ.rnDeriv vol =ᵐ[vol] μ.rnDeriv vol`
  have h_chain_vol : (fun z ↦ μ.rnDeriv ρ z * ρ.rnDeriv volume z)
      =ᵐ[(volume : Measure (ℝ × ℝ))] (fun z ↦ μ.rnDeriv volume z) := by
    have := Measure.rnDeriv_mul_rnDeriv (μ := μ) (ν := ρ)
      (κ := (volume : Measure (ℝ × ℝ))) h_joint_ac
    exact this
  -- Step B: ρ.rnDeriv vol =ᵐ[vol] g (from h_ρ_eq + rnDeriv_withDensity₀)
  have h_g_meas : AEMeasurable g (volume : Measure (ℝ × ℝ)) := by
    refine AEMeasurable.mul ?_ ?_
    · exact ((Measure.measurable_rnDeriv μX volume).comp measurable_fst).aemeasurable
    · exact ((Measure.measurable_rnDeriv μY volume).comp measurable_snd).aemeasurable
  have h_ρ_rnDeriv : ρ.rnDeriv volume =ᵐ[(volume : Measure (ℝ × ℝ))] g := by
    have := Measure.rnDeriv_withDensity₀ (ν := (volume : Measure (ℝ × ℝ))) h_g_meas
    rw [h_ρ_eq]
    exact this
  -- Step C: combine to get `μ.rnDeriv ρ · g =ᵐ[vol] μ.rnDeriv vol`
  have h_prod_vol : (fun z ↦ μ.rnDeriv ρ z * g z)
      =ᵐ[(volume : Measure (ℝ × ℝ))] (fun z ↦ μ.rnDeriv volume z) := by
    filter_upwards [h_chain_vol, h_ρ_rnDeriv] with z h1 h2
    rw [← h1, h2]
  -- Step D: pull `=ᵐ[vol]` to `=ᵐ[μ]` via μ ≪ vol
  have h_prod_μ : (fun z ↦ μ.rnDeriv ρ z * g z)
      =ᵐ[μ] (fun z ↦ μ.rnDeriv volume z) := hμ_vol.ae_le h_prod_vol
  -- a.e. positivity / finiteness conditions a.e.[μ]
  have h_rnD_ρ_pos : ∀ᵐ z ∂μ, μ.rnDeriv ρ z ≠ 0 := by
    filter_upwards [Measure.rnDeriv_pos h_joint_ac] with z hz using hz.ne'
  have h_rnD_ρ_ne_top : ∀ᵐ z ∂μ, μ.rnDeriv ρ z ≠ ∞ :=
    h_joint_ac.ae_le (Measure.rnDeriv_ne_top μ ρ)
  have h_rnD_vol_pos : ∀ᵐ z ∂μ, μ.rnDeriv volume z ≠ 0 := by
    filter_upwards [Measure.rnDeriv_pos hμ_vol] with z hz using hz.ne'
  have h_rnD_vol_ne_top : ∀ᵐ z ∂μ, μ.rnDeriv volume z ≠ ∞ :=
    hμ_vol.ae_le (Measure.rnDeriv_ne_top μ volume)
  -- marginal-side positivity a.e.[μ] via push-forward
  have h_μX_pos : ∀ᵐ z ∂μ, μX.rnDeriv volume z.1 ≠ 0 := by
    have h_μX : ∀ᵐ x ∂μX, μX.rnDeriv volume x ≠ 0 := by
      filter_upwards [Measure.rnDeriv_pos h_fst_ac] with x hx using hx.ne'
    have := (ae_map_iff measurable_fst.aemeasurable
      (p := fun x ↦ μX.rnDeriv volume x ≠ 0)
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl).mp h_μX
    exact this
  have h_μY_pos : ∀ᵐ z ∂μ, μY.rnDeriv volume z.2 ≠ 0 := by
    have h_μY : ∀ᵐ y ∂μY, μY.rnDeriv volume y ≠ 0 := by
      filter_upwards [Measure.rnDeriv_pos h_snd_ac] with y hy using hy.ne'
    have := (ae_map_iff measurable_snd.aemeasurable
      (p := fun y ↦ μY.rnDeriv volume y ≠ 0)
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl).mp h_μY
    exact this
  have h_μX_ne_top : ∀ᵐ z ∂μ, μX.rnDeriv volume z.1 ≠ ∞ := by
    have h_μX : ∀ᵐ x ∂μX, μX.rnDeriv volume x ≠ ∞ :=
      h_fst_ac.ae_le (Measure.rnDeriv_ne_top μX volume)
    have := (ae_map_iff measurable_fst.aemeasurable
      (p := fun x ↦ μX.rnDeriv volume x ≠ ∞)
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl).mp h_μX
    exact this
  have h_μY_ne_top : ∀ᵐ z ∂μ, μY.rnDeriv volume z.2 ≠ ∞ := by
    have h_μY : ∀ᵐ y ∂μY, μY.rnDeriv volume y ≠ ∞ :=
      h_snd_ac.ae_le (Measure.rnDeriv_ne_top μY volume)
    have := (ae_map_iff measurable_snd.aemeasurable
      (p := fun y ↦ μY.rnDeriv volume y ≠ ∞)
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl).mp h_μY
    exact this
  -- Combine: at z satisfying all the conditions, take toReal + log of `h_prod_μ`.
  filter_upwards [h_prod_μ, h_rnD_ρ_pos, h_rnD_ρ_ne_top, h_rnD_vol_pos,
    h_rnD_vol_ne_top, h_μX_pos, h_μY_pos, h_μX_ne_top, h_μY_ne_top]
    with z h_eq h_ρ_ne0 h_ρ_neT h_vol_ne0 h_vol_neT h_X_ne0 h_Y_ne0 h_X_neT h_Y_neT
  -- now `μ.rnDeriv ρ z * (μX.rnDeriv vol z.1 * μY.rnDeriv vol z.2) = μ.rnDeriv vol z` in ℝ≥0∞
  -- take toReal:
  have h_g_ne_top : μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2 ≠ ∞ :=
    ENNReal.mul_ne_top h_X_neT h_Y_neT
  have h_g_ne_zero : μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2 ≠ 0 :=
    mul_ne_zero h_X_ne0 h_Y_ne0
  -- toReal on both sides of h_eq
  have h_eq_real :
      (μ.rnDeriv ρ z).toReal
        * (μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2).toReal
        = (μ.rnDeriv volume z).toReal := by
    have := congrArg ENNReal.toReal h_eq
    simp only at this
    rw [ENNReal.toReal_mul] at this
    exact this
  -- the two factors on the LHS are strictly positive as reals
  have h_ρ_pos_real : 0 < (μ.rnDeriv ρ z).toReal :=
    ENNReal.toReal_pos h_ρ_ne0 h_ρ_neT
  have h_g_pos_real : 0 < (μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2).toReal :=
    ENNReal.toReal_pos h_g_ne_zero h_g_ne_top
  have h_X_pos_real : 0 < (μX.rnDeriv volume z.1).toReal :=
    ENNReal.toReal_pos h_X_ne0 h_X_neT
  have h_Y_pos_real : 0 < (μY.rnDeriv volume z.2).toReal :=
    ENNReal.toReal_pos h_Y_ne0 h_Y_neT
  -- take log of `h_eq_real`
  have h_log : Real.log ((μ.rnDeriv ρ z).toReal)
        + Real.log ((μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2).toReal)
        = Real.log ((μ.rnDeriv volume z).toReal) := by
    rw [← Real.log_mul h_ρ_pos_real.ne' h_g_pos_real.ne', h_eq_real]
  -- split the second log via toReal_mul + log_mul
  have h_g_toReal : (μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2).toReal
      = (μX.rnDeriv volume z.1).toReal * (μY.rnDeriv volume z.2).toReal :=
    ENNReal.toReal_mul
  have h_log_g : Real.log ((μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2).toReal)
      = Real.log ((μX.rnDeriv volume z.1).toReal)
        + Real.log ((μY.rnDeriv volume z.2).toReal) := by
    rw [h_g_toReal, Real.log_mul h_X_pos_real.ne' h_Y_pos_real.ne']
  -- conclude: llr μ ρ z = log(μ.rnDeriv ρ z).toReal = log(μ.rnDeriv vol z).toReal
  --                       − log(μX.rnDeriv vol z.1).toReal − log(μY.rnDeriv vol z.2).toReal
  show Real.log ((μ.rnDeriv ρ z).toReal) = _
  linarith [h_log, h_log_g]

/-- 2-variable subadditivity bridge without explicit `h_llr_split`:
`(klDiv(joint ‖ μ_X ⊗ μ_Y)).toReal = h(μ_X) + h(μ_Y) − h(joint)`.

The Bayes density split is produced internally by `llr_split_from_density_factorize`. -/
@[entry_point]
theorem klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume)
    (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd))
    (h_int_fst :
      Integrable (fun z ↦ Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)) μ)
    (h_int_snd :
      Integrable (fun z ↦ Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)) μ)
    (h_int_joint :
      Integrable (fun z ↦ Real.log ((μ.rnDeriv volume z).toReal)) μ)
    (h_int_fst_marg :
      Integrable (fun x ↦ Real.log (((μ.map Prod.fst).rnDeriv volume x).toReal))
        (μ.map Prod.fst))
    (h_int_snd_marg :
      Integrable (fun y ↦ Real.log (((μ.map Prod.snd).rnDeriv volume y).toReal))
        (μ.map Prod.snd)) :
    (klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))).toReal
      = differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd)
        - jointDifferentialEntropy μ :=
  klDiv_prod_marginals_toReal_eq_sum_sub_joint
    h_fst_ac h_snd_ac h_joint_ac
    (llr_split_from_density_factorize h_fst_ac h_snd_ac h_joint_ac)
    h_int_fst h_int_snd h_int_joint h_int_fst_marg h_int_snd_marg

/-- **★ 2-variable differential-entropy subadditivity** `h(X,Y) ≤ h(X) + h(Y)`.

The Bayes density split is internalized via `llr_split_from_density_factorize`;
no explicit `h_llr_split` argument required. -/
@[entry_point]
theorem jointDifferentialEntropy_le_sum_v2
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume)
    (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd))
    (h_int_fst :
      Integrable (fun z ↦ Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)) μ)
    (h_int_snd :
      Integrable (fun z ↦ Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)) μ)
    (h_int_joint :
      Integrable (fun z ↦ Real.log ((μ.rnDeriv volume z).toReal)) μ)
    (h_int_fst_marg :
      Integrable (fun x ↦ Real.log (((μ.map Prod.fst).rnDeriv volume x).toReal))
        (μ.map Prod.fst))
    (h_int_snd_marg :
      Integrable (fun y ↦ Real.log (((μ.map Prod.snd).rnDeriv volume y).toReal))
        (μ.map Prod.snd)) :
    jointDifferentialEntropy μ
      ≤ differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd) :=
  jointDifferentialEntropy_le_sum
    h_fst_ac h_snd_ac h_joint_ac
    (llr_split_from_density_factorize h_fst_ac h_snd_ac h_joint_ac)
    h_int_fst h_int_snd h_int_joint h_int_fst_marg h_int_snd_marg


end InformationTheory.Shannon
