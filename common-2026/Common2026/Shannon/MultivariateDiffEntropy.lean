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
(`llr(joint ‖ ∏ marginals) = ∑ log(marginalᵢ) − log(joint)`) plus integrability.

* **2-variable case (Phase 1 plan, discharged 2026-05-25):** the `h_llr_split`
  honest hypothesis is fully discharged via Mathlib's `prod_withDensity₀` +
  `rnDeriv_withDensity₀` + `rnDeriv_mul_rnDeriv` chain — see
  `llr_split_from_density_factorize` and the `_v2` successors
  (`klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2`,
  `jointDifferentialEntropy_le_sum_v2`). The pre-discharge versions are kept
  for backward compatibility, tagged
  `@audit:superseded-by(<v2-name>)`.

* **`n`-variable case:** still load-bearing on `h_llr_split` plus integrability,
  carried as named honest hypotheses mirroring the channel手本
  `ContChannelMIDecomp.mutualInfoOfChannel_toReal_eq_diffEntropy_sub`.
  `pi_withDensity` (joint density = ∏ marginal density bridge) is **absent from
  Mathlib** (inventory §D-1a); the natural discharge is induction of the
  2-variable bridge via `measurePreserving_piFinSuccAbove`, which requires a
  change-of-variables for `withDensity` under measurable equivalences (also
  absent in Mathlib in the generic non-rnDeriv form). Tagged
  `@audit:suspect(multivariate-diffentropy-subadditivity-plan)` as the
  residual discharge target.
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

The `h_llr_split` honest hypothesis is **discharged** by the successor
`klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2`; this version is retained
for backward compatibility with prior callers.

`@audit:superseded-by(klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2)` -/
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

The `h_llr_split` honest hypothesis is **discharged** by the successor
`jointDifferentialEntropy_le_sum_v2`; this version is retained for backward
compatibility with prior callers.

`@audit:superseded-by(jointDifferentialEntropy_le_sum_v2)` -/
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

`@audit:suspect(multivariate-diffentropy-subadditivity-plan)` -/
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

`@audit:suspect(multivariate-diffentropy-subadditivity-plan)` -/
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

/-! ## Phase 1 — genuine 2-variable Bayes density split (no honest `h_llr_split`)

The `_v2` family below discharges the `h_llr_split` honest hypothesis of the
original `klDiv_prod_marginals_toReal_eq_sum_sub_joint` and
`jointDifferentialEntropy_le_sum` via Mathlib's `prod_withDensity` +
`rnDeriv_mul_rnDeriv`. The original (suspect) statements are kept for
backward compatibility; the `_v2` versions are the genuine successors. -/

/-- **Density factorization of product marginals (genuine).** For a joint
probability measure `μ` on `ℝ × ℝ` with marginals `μX, μY` both absolutely
continuous wrt the Lebesgue measure, the product `μX × μY` factors through the
Lebesgue measure on `ℝ × ℝ` as

  `(μX).prod (μY) = volume.withDensity (z ↦ μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2)`.

Discharge route: `Measure.withDensity_rnDeriv_eq` rewrites each marginal as
`volume.withDensity (.rnDeriv volume)`, then `prod_withDensity₀` fuses them, and
`Measure.volume_eq_prod` (`rfl`) identifies the result. -/
theorem prod_marginals_eq_volume_withDensity
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume) :
    (μ.map Prod.fst).prod (μ.map Prod.snd)
      = (volume : Measure (ℝ × ℝ)).withDensity
          (fun z => (μ.map Prod.fst).rnDeriv volume z.1
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

/-- **Genuine Bayes density split for the 2-variable joint (a.e.[μ]).** The
log-likelihood ratio of `μ` against the product of its marginals equals
`log(joint density) − log(marginal_X density on z.1) − log(marginal_Y density on z.2)`
almost-everywhere wrt `μ`, *without* an honest hypothesis. Discharge route:
`prod_marginals_eq_volume_withDensity` + `rnDeriv_mul_rnDeriv` + `Real.log_mul`
on the multiplicative chain `μ.rnDeriv ρ · ρ.rnDeriv vol = μ.rnDeriv vol`. -/
theorem llr_split_from_density_factorize
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume)
    (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd)) :
    (fun z => llr μ ((μ.map Prod.fst).prod (μ.map Prod.snd)) z)
      =ᵐ[μ]
    (fun z => Real.log ((μ.rnDeriv volume z).toReal)
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
    fun z => μX.rnDeriv volume z.1 * μY.rnDeriv volume z.2 with hg
  have h_ρ_eq : ρ = (volume : Measure (ℝ × ℝ)).withDensity g := by
    rw [hρ, hg]; exact prod_marginals_eq_volume_withDensity h_fst_ac h_snd_ac
  -- μ ≪ volume (via μ ≪ ρ ≪ vol.prod vol = vol)
  have hμ_vol : μ ≪ (volume : Measure (ℝ × ℝ)) := by
    refine h_joint_ac.trans ?_
    rw [Measure.volume_eq_prod]
    exact h_fst_ac.prod h_snd_ac
  -- Step A: chain rule `μ.rnDeriv ρ · ρ.rnDeriv vol =ᵐ[vol] μ.rnDeriv vol`
  have h_chain_vol : (fun z => μ.rnDeriv ρ z * ρ.rnDeriv volume z)
      =ᵐ[(volume : Measure (ℝ × ℝ))] (fun z => μ.rnDeriv volume z) := by
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
  have h_prod_vol : (fun z => μ.rnDeriv ρ z * g z)
      =ᵐ[(volume : Measure (ℝ × ℝ))] (fun z => μ.rnDeriv volume z) := by
    filter_upwards [h_chain_vol, h_ρ_rnDeriv] with z h1 h2
    rw [← h1, h2]
  -- Step D: pull `=ᵐ[vol]` to `=ᵐ[μ]` via μ ≪ vol
  have h_prod_μ : (fun z => μ.rnDeriv ρ z * g z)
      =ᵐ[μ] (fun z => μ.rnDeriv volume z) := hμ_vol.ae_le h_prod_vol
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
      (p := fun x => μX.rnDeriv volume x ≠ 0)
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl).mp h_μX
    exact this
  have h_μY_pos : ∀ᵐ z ∂μ, μY.rnDeriv volume z.2 ≠ 0 := by
    have h_μY : ∀ᵐ y ∂μY, μY.rnDeriv volume y ≠ 0 := by
      filter_upwards [Measure.rnDeriv_pos h_snd_ac] with y hy using hy.ne'
    have := (ae_map_iff measurable_snd.aemeasurable
      (p := fun y => μY.rnDeriv volume y ≠ 0)
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl).mp h_μY
    exact this
  have h_μX_ne_top : ∀ᵐ z ∂μ, μX.rnDeriv volume z.1 ≠ ∞ := by
    have h_μX : ∀ᵐ x ∂μX, μX.rnDeriv volume x ≠ ∞ :=
      h_fst_ac.ae_le (Measure.rnDeriv_ne_top μX volume)
    have := (ae_map_iff measurable_fst.aemeasurable
      (p := fun x => μX.rnDeriv volume x ≠ ∞)
      (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl).mp h_μX
    exact this
  have h_μY_ne_top : ∀ᵐ z ∂μ, μY.rnDeriv volume z.2 ≠ ∞ := by
    have h_μY : ∀ᵐ y ∂μY, μY.rnDeriv volume y ≠ ∞ :=
      h_snd_ac.ae_le (Measure.rnDeriv_ne_top μY volume)
    have := (ae_map_iff measurable_snd.aemeasurable
      (p := fun y => μY.rnDeriv volume y ≠ ∞)
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

/-- **2-variable subadditivity bridge (genuine, no `h_llr_split`).** Discharged
version of `klDiv_prod_marginals_toReal_eq_sum_sub_joint`: the Bayes density
split is produced internally by `llr_split_from_density_factorize`, so the
honest `h_llr_split` argument is no longer required. The remaining hypotheses
are regularity (absolute continuity + Bochner integrability of three
log-density observables). -/
theorem klDiv_prod_marginals_toReal_eq_sum_sub_joint_v2
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume)
    (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd))
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
    (klDiv μ ((μ.map Prod.fst).prod (μ.map Prod.snd))).toReal
      = differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd)
        - jointDifferentialEntropy μ :=
  klDiv_prod_marginals_toReal_eq_sum_sub_joint
    h_fst_ac h_snd_ac h_joint_ac
    (llr_split_from_density_factorize h_fst_ac h_snd_ac h_joint_ac)
    h_int_fst h_int_snd h_int_joint h_int_fst_marg h_int_snd_marg

/-- **★ 2-variable differential-entropy subadditivity (genuine, no `h_llr_split`).**
Discharged version of `jointDifferentialEntropy_le_sum`: `h(X,Y) ≤ h(X) + h(Y)`
with the Bayes density split internalized via `llr_split_from_density_factorize`. -/
theorem jointDifferentialEntropy_le_sum_v2
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (h_fst_ac : (μ.map Prod.fst) ≪ volume)
    (h_snd_ac : (μ.map Prod.snd) ≪ volume)
    (h_joint_ac : μ ≪ (μ.map Prod.fst).prod (μ.map Prod.snd))
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
      ≤ differentialEntropy (μ.map Prod.fst) + differentialEntropy (μ.map Prod.snd) :=
  jointDifferentialEntropy_le_sum
    h_fst_ac h_snd_ac h_joint_ac
    (llr_split_from_density_factorize h_fst_ac h_snd_ac h_joint_ac)
    h_int_fst h_int_snd h_int_joint h_int_fst_marg h_int_snd_marg

/-! ## Phase 2 — withdrawal note on `n`-variable subadditivity

The `n`-variable subadditivity bridge (`klDiv_pi_marginals_toReal_eq_sum_sub_joint`
+ `jointDifferentialEntropyPi_le_sum` above) keeps the honest `h_llr_split`
hypothesis. The natural discharge route is by inducting the Phase 1 2-variable
density factorization (`prod_marginals_eq_volume_withDensity`) through
`measurePreserving_piFinSuccAbove`, building a `pi_marginals_eq_volume_withDensity`
counterpart. This induction is non-trivial — it requires a change-of-variables
for `withDensity` under measurable equivalences (which is not a direct Mathlib
lemma — only the rnDeriv-specialized `MeasurableEmbedding.map_withDensity_rnDeriv`
exists), plus reshape of the density between the iterated-prod and `Measure.pi`
forms. An initial attempt (~250 lines including the `pi_eq` shortcut) ran into
several reshape frictions (definitional `volume_pi` vs `Measure.pi (fun _ => volume)`,
`piFinSuccAbove 0` vs `piFinSuccAbove (Fin.last n)` orientation, etc.).

Per plan §"撤退条件 — 案 A / 案 B 双方で行き詰まる → n 変数のみ honest hyp 温存",
the `n`-variable case is **kept as the existing honest-hyp form**. The
`@audit:suspect(multivariate-diffentropy-subadditivity-plan)` slug remains valid
as the SoT for the residual discharge, and the proof-log records the genuine
direction tried so a future session can continue. -/

end Common2026.Shannon
