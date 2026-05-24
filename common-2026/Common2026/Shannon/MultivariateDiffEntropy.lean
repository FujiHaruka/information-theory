import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Common2026.Shannon.DifferentialEntropy
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.MIChainRule

/-!
# Multivariate differential entropy + subadditivity

Genuine common foundation for the AWGN / Parallel-Gaussian output-entropy upper
bounds (`docs/shannon/multivariate-diffentropy-inventory.md`). Provides:

* `jointDifferentialEntropy` — 2-variable joint differential entropy
  (`Measure (ℝ × ℝ)`), defined `-∫ negMulLog (dμ/dvol)` exactly as the 1-D
  `differentialEntropy`, so `volume_eq_prod` (`rfl`) makes the 1-D lemmas apply.
* `jointDifferentialEntropyPi` — the `n`-variable form (`Measure (Fin n → ℝ)`)
  the parallel-Gaussian consumer requires.
* `integral_log_rnDeriv_self_eq_neg` — the reusable `∫ log(dμ/dν) ∂μ = -h(μ)`
  core (works for joint *and* each marginal).
* `jointDifferentialEntropy_le_sum` / `jointDifferentialEntropyPi_le_sum` —
  subadditivity `h(Yⁿ) ≤ ∑ᵢ h(Yᵢ)`, via `klDiv(joint ‖ ∏ marginals) ≥ 0`.

## Honesty status

The subadditivity *structure* (`KL ≥ 0` from `ENNReal.toReal_nonneg` + bridge) is
genuine. The bridge from `KL` to entropies needs the Bayes density split
(`llr(joint ‖ ∏ marginals) = ∑ log(marginalᵢ) − log(joint)`) plus integrability,
carried as named honest hypotheses exactly mirroring the existing channel手本
`ContChannelMIDecomp.mutualInfoOfChannel_toReal_eq_diffEntropy_sub`. The
`n`-variable bridge is honest in the same way; `pi_withDensity` (the joint
density = ∏ marginal density bridge) is **absent from Mathlib**, so it is folded
into the honest llr-split hypothesis rather than self-built (inventory §D-1a).
-/

namespace Common2026.Shannon

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

/-- **Generic log-density / entropy identity (genuine).** For `μ ≪ ν` on any
measurable space, `∫ x, log((μ.rnDeriv ν x).toReal) ∂μ = -∫ x, negMulLog((μ.rnDeriv
ν x).toReal) ∂ν`. The RHS is precisely the (joint/1-D) differential entropy when
`ν` is the relevant Lebesgue measure. Built from `integral_rnDeriv_smul`. -/
theorem integral_log_rnDeriv_self_eq_neg
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) :
    ∫ x, Real.log ((μ.rnDeriv ν x).toReal) ∂μ
      = -∫ x, Real.negMulLog ((μ.rnDeriv ν x).toReal) ∂ν := by
  -- pull the integral against `μ` back to `ν` via the Radon-Nikodym change of variables
  have h_pull : ∫ x, Real.log ((μ.rnDeriv ν x).toReal) ∂μ
      = ∫ x, (μ.rnDeriv ν x).toReal • Real.log ((μ.rnDeriv ν x).toReal) ∂ν :=
    (integral_rnDeriv_smul (μ := μ) (ν := ν) hμν
      (f := fun x => Real.log ((μ.rnDeriv ν x).toReal))).symm
  rw [h_pull, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [smul_eq_mul, Real.negMulLog_def]
  ring

/-! ## 2-variable bridge + subadditivity -/

/-- **2-variable subadditivity bridge (genuine structure, honest density split).**
`(klDiv(joint ‖ μ_X ⊗ μ_Y)).toReal = h(μ_X) + h(μ_Y) − h(joint)`. The honest
hypotheses (absolute continuity + Bayes llr split + integrability) mirror the
channel手本 `mutualInfoOfChannel_toReal_eq_diffEntropy_sub`.

`@audit:suspect(differential-entropy-plan)` -/
theorem klDiv_prod_marginals_toReal_eq_sum_sub_joint
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume)
    (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd))
    -- honest Bayes density split (mirrors 手本 `h_llr_split`): `llr(joint ‖ ∏ marg) =
    -- log(joint) − log(margX) − log(margY)`, i.e. `log(d joint / d∏marg)`.
    (h_llr_split :
      (fun z => llr μ ((μ.map Prod.fst).prod (μ.map Prod.snd)) z)
        =ᵐ[μ]
      (fun z => Real.log ((μ.rnDeriv volume z).toReal)
                  - Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)
                  - Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)))
    -- integrability of the three log-density pieces against the joint
    (h_int_fst :
      Integrable (fun z => Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)) μ)
    (h_int_snd :
      Integrable (fun z => Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)) μ)
    (h_int_joint :
      Integrable (fun z => Real.log ((μ.rnDeriv volume z).toReal)) μ)
    -- marginal-side integrability for the Fubini reductions
    (h_int_fst_marg :
      Integrable (fun x => Real.log (((μ.map Prod.fst).rnDeriv volume x).toReal))
        (μ.map Prod.fst))
    (h_int_snd_marg :
      Integrable (fun y => Real.log (((μ.map Prod.snd).rnDeriv volume y).toReal))
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
  set Lfst : ℝ × ℝ → ℝ := fun z => Real.log ((μX.rnDeriv volume z.1).toReal) with hLfst
  set Lsnd : ℝ × ℝ → ℝ := fun z => Real.log ((μY.rnDeriv volume z.2).toReal) with hLsnd
  set Ljoint : ℝ × ℝ → ℝ := fun z => Real.log ((μ.rnDeriv volume z).toReal) with hLjoint
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
`KL ≥ 0` (`ENNReal.toReal_nonneg`) + the bridge, closed by `linarith`.

`@audit:suspect(differential-entropy-plan)` -/
theorem jointDifferentialEntropy_le_sum
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume)
    (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd))
    (h_llr_split :
      (fun z => llr μ ((μ.map Prod.fst).prod (μ.map Prod.snd)) z)
        =ᵐ[μ]
      (fun z => Real.log ((μ.rnDeriv volume z).toReal)
                  - Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)
                  - Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)))
    (h_int_fst :
      Integrable (fun z => Real.log (((μ.map Prod.fst).rnDeriv volume z.1).toReal)) μ)
    (h_int_snd :
      Integrable (fun z => Real.log (((μ.map Prod.snd).rnDeriv volume z.2).toReal)) μ)
    (h_int_joint :
      Integrable (fun z => Real.log ((μ.rnDeriv volume z).toReal)) μ)
    (h_int_fst_marg :
      Integrable (fun x => Real.log (((μ.map Prod.fst).rnDeriv volume x).toReal))
        (μ.map Prod.fst))
    (h_int_snd_marg :
      Integrable (fun y => Real.log (((μ.map Prod.snd).rnDeriv volume y).toReal))
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

/-- **`n`-variable subadditivity bridge (genuine structure, honest density split).**
`(klDiv(joint ‖ ∏ᵢ μᵢ)).toReal = ∑ᵢ h(μᵢ) − h(joint)`, where `μᵢ := μ.map (· i)`.
The honest llr split absorbs the absent `pi_withDensity` (inventory §D-1a).

`@audit:suspect(differential-entropy-plan)` -/
theorem klDiv_pi_marginals_toReal_eq_sum_sub_joint
    {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μ.map (fun z => z i))]
    (h_marg_ac : ∀ i, (μ.map (fun z => z i)) ≪ volume)
    (hμ_ac : μ ≪ (volume : Measure (Fin n → ℝ)))
    (h_joint_ac : μ ≪ Measure.pi (fun i => μ.map (fun z => z i)))
    -- honest Bayes density split: `llr(joint ‖ ∏ marg) = log(joint) − ∑ log(margᵢ)`.
    (h_llr_split :
      (fun z => llr μ (Measure.pi (fun i => μ.map (fun z => z i))) z)
        =ᵐ[μ]
      (fun z => Real.log ((μ.rnDeriv volume z).toReal)
                  - (∑ i, Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal))))
    (h_int_marg : ∀ i,
      Integrable (fun z => Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal)) μ)
    (h_int_joint :
      Integrable (fun z => Real.log ((μ.rnDeriv volume z).toReal)) μ)
    -- marginal identification: ∫ (g ∘ eval i) ∂μ = ∫ g ∂(μ.map eval i)
    (h_marg_id : ∀ i,
      (∫ z, Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal) ∂μ)
        = ∫ x, Real.log (((μ.map (fun z => z i)).rnDeriv volume x).toReal)
            ∂(μ.map (fun z => z i))) :
    (klDiv μ (Measure.pi (fun i => μ.map (fun z => z i)))).toReal
      = (∑ i, differentialEntropy (μ.map (fun z => z i))) - jointDifferentialEntropyPi μ := by
  classical
  set ν := Measure.pi (fun i => μ.map (fun z => z i)) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  -- abbreviations
  set Ljoint : (Fin n → ℝ) → ℝ := fun z => Real.log ((μ.rnDeriv volume z).toReal) with hLjoint
  set Lmarg : Fin n → (Fin n → ℝ) → ℝ :=
    fun i z => Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal) with hLmarg
  -- step 1 : KL → llr integral (univ = 1 both sides)
  have h_univ : μ Set.univ = ν Set.univ := by rw [measure_univ, measure_univ]
  have h_kl : (klDiv μ ν).toReal = ∫ z, llr μ ν z ∂μ :=
    toReal_klDiv_of_measure_eq h_joint_ac h_univ
  -- step 2 : Bayes density split
  have h_split : ∫ z, llr μ ν z ∂μ
      = ∫ z, (Ljoint z - (∑ i, Lmarg i z)) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [h_llr_split] with z hz using hz
  -- step 3 : split into joint integral minus sum of marginal integrals
  have h_sub : ∫ z, (Ljoint z - (∑ i, Lmarg i z)) ∂μ
      = (∫ z, Ljoint z ∂μ) - ∑ i, (∫ z, Lmarg i z ∂μ) := by
    have h_int_sum : Integrable (fun z => ∑ i, Lmarg i z) μ :=
      integrable_finsetSum _ (fun i _ => h_int_marg i)
    rw [integral_sub h_int_joint h_int_sum,
      integral_finsetSum Finset.univ (fun i _ => h_int_marg i)]
  -- step 4 : joint term = − h(joint)
  have h_jt : ∫ z, Ljoint z ∂μ = -jointDifferentialEntropyPi μ := by
    rw [jointDifferentialEntropyPi, integral_log_rnDeriv_self_eq_neg
      (μ := μ) (ν := (volume : Measure (Fin n → ℝ))) hμ_ac]
  -- step 5 : each marginal term = − h(margᵢ)  (marginal id + generic helper)
  have h_mg : ∀ i, ∫ z, Lmarg i z ∂μ = -differentialEntropy (μ.map (fun z => z i)) := by
    intro i
    rw [hLmarg]
    rw [h_marg_id i, integral_log_rnDeriv_self_eq_neg (h_marg_ac i), differentialEntropy]
  -- combine
  rw [h_kl, h_split, h_sub, h_jt]
  rw [Finset.sum_congr rfl (fun i _ => h_mg i)]
  rw [Finset.sum_neg_distrib]
  ring

/-- **★ `n`-variable differential-entropy subadditivity** `h(Yⁿ) ≤ ∑ᵢ h(Yᵢ)`
(the parallel-Gaussian consumer form). `KL ≥ 0` + the bridge, by `linarith`.

`@audit:suspect(differential-entropy-plan)` -/
theorem jointDifferentialEntropyPi_le_sum
    {n : ℕ} {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (μ.map (fun z => z i))]
    (h_marg_ac : ∀ i, (μ.map (fun z => z i)) ≪ volume)
    (hμ_ac : μ ≪ (volume : Measure (Fin n → ℝ)))
    (h_joint_ac : μ ≪ Measure.pi (fun i => μ.map (fun z => z i)))
    (h_llr_split :
      (fun z => llr μ (Measure.pi (fun i => μ.map (fun z => z i))) z)
        =ᵐ[μ]
      (fun z => Real.log ((μ.rnDeriv volume z).toReal)
                  - (∑ i, Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal))))
    (h_int_marg : ∀ i,
      Integrable (fun z => Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal)) μ)
    (h_int_joint :
      Integrable (fun z => Real.log ((μ.rnDeriv volume z).toReal)) μ)
    (h_marg_id : ∀ i,
      (∫ z, Real.log (((μ.map (fun z => z i)).rnDeriv volume (z i)).toReal) ∂μ)
        = ∫ x, Real.log (((μ.map (fun z => z i)).rnDeriv volume x).toReal)
            ∂(μ.map (fun z => z i))) :
    jointDifferentialEntropyPi μ
      ≤ ∑ i, differentialEntropy (μ.map (fun z => z i)) := by
  have h_nn : (0 : ℝ) ≤ (klDiv μ (Measure.pi (fun i => μ.map (fun z => z i)))).toReal :=
    ENNReal.toReal_nonneg
  have h_bridge := klDiv_pi_marginals_toReal_eq_sum_sub_joint
    h_marg_ac hμ_ac h_joint_ac h_llr_split h_int_marg h_int_joint h_marg_id
  linarith [h_nn, h_bridge]

end Common2026.Shannon
