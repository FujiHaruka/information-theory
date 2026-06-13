import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Bases
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPI.Stam.Discharge
import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.FisherInfo.V2DeBruijnPerTime
import InformationTheory.Shannon.FisherInfo.V2DeBruijnAssembly
import InformationTheory.Shannon.EPI.Vitali.UI
import InformationTheory.Shannon.EPI.G2.KLFatouLSC
import InformationTheory.Shannon.EPI.G2.ConvEntropyDensity
import InformationTheory.Meta.EntryPoint

/-!
# Heat-flow entropy-power continuity at the endpoint `t = 0⁺`

This file isolates the single analytic atom used by the EPI continuity consumer in
`EPIStamToBridge.lean`: the continuity of
`t ↦ entropyPower (P.map (fun ω => X ω + √t · Z ω))` at the endpoint `t = 0⁺` along
the heat-flow ray. The interior `t > 0` continuity is supplied separately and
genuinely by `csiszarLogRatioGap_differentiableOn_interior`.

The endpoint atom is `heatFlowEntropyPower_continuousWithinAt_zero`, claiming only
`ContinuousWithinAt (Set.Ioi 0) 0` (the single endpoint limit `t → 0⁺`). The endpoint
is re-attached to the interior with the OrderDual mirror
`AntitoneOn.insert_of_continuousWithinAt` (added in this file).

## Main statements

* `heatFlowEntropyPower_continuousWithinAt_zero` — endpoint entropy-power continuity.
* `heatFlowDifferentialEntropy_continuousWithinAt_zero` — the inner
  differential-entropy continuity it lifts.
* `differentialEntropy_convDensity_integral_tendsto` — the density-level
  entropy-integral convergence underlying both.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Topology

/-! ## Entropy finiteness of the limit density (a precondition)

`Integrable (negMulLog pX)` (= `h(X) < ∞`, differential entropy of the limit
density `pX` finite) is required as the limit-side `Integrable` input by the
entropy-integral machinery. It does **not** follow from the L¹ +
finite-second-moment regularity of `pX` (a concentrated density can have
`∫ negMulLog pX = −∞`). It is therefore carried as an explicit `hpX_ent`
precondition: the input `X` has finite differential entropy. This is a regularity
precondition on the input distribution, not a load-bearing conclusion. -/

/-- **Per-time entropy-integrand integrability.**
For each `t > 0`, `negMulLog (convDensityAdd pX g_t)` is `volume`-integrable.

Delegates verbatim to the in-tree asset
`FisherInfoV2.convDensityAdd_negMulLog_integrable` (same conclusion type); pure
plumbing, no new analytic content.
@audit:ok -/
theorem convDensityAdd_negMulLog_integrable_pub
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume :=
  InformationTheory.Shannon.FisherInfoV2.convDensityAdd_negMulLog_integrable
    pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht

/-! ## Two-sided sandwich for the entropy-integral limit

The lift from per-time entropy integrals to the endpoint entropy integral is a
two-sided sandwich:

* **(α) limsup upper bound** — `InformationTheory.EPIG2KLFatou.negMulLog_convDensity_limsup_le`
  (Fatou / KL lower-semicontinuity): `limsup (∫ negMulLog f_n) ≤ ∫ negMulLog pX`.
* **(β) per-`n` lower bound** — `negMulLog_convDensity_entropy_ge_density`
  (conditioning reduces entropy): `∫ negMulLog pX ≤ ∫ negMulLog f_n`.
* **uniform upper bound** — `negMulLog_convDensityAdd_gaussian_entropy_upper`
  (Gaussian maximum-entropy): a per-`n` bound with a uniform variance majorant
  (the `v n` are bounded since `v n → 0`), supplying the `IsBoundedUnder (· ≤ ·)`
  witness for the squeeze.

The squeeze `tendsto_of_le_liminf_of_limsup_le` then gives `∫ negMulLog f_n → ∫
negMulLog pX` along sequences, lifted to `𝓝[Ioi 0] 0` via
`Filter.tendsto_iff_seq_tendsto`. -/

/-- **Entropy-integral convergence.** Given the regularity of `pX` and the
entropy-finiteness precondition `hpX_ent` (= `h(X) < ∞`, a regularity precondition
on the input), the differential-entropy integrals of the heat-smoothed densities
converge to the entropy integral of `pX` as `t → 0⁺`:

`∫ negMulLog (convDensityAdd pX g_t) ∂volume → ∫ negMulLog pX ∂volume`.
@audit:ok -/
@[entry_point]
theorem differentialEntropy_convDensity_integral_tendsto
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume) :
    Tendsto
      (fun t : ℝ =>
        ∫ x, Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) x)
          ∂volume)
      (𝓝[Set.Ioi 0] 0)
      (𝓝 (∫ x, Real.negMulLog (pX x) ∂volume)) := by
  -- Reduce the continuous filter `𝓝[Ioi 0] 0` to sequences (it is countably generated).
  rw [tendsto_iff_seq_tendsto]
  intro u hu_lim
  -- A sequence tending to `0` within `Ioi 0` is eventually positive; here we extract
  -- positivity for *every* `n` by reindexing onto the eventually-positive tail.
  have hu_evpos : ∀ᶠ n in atTop, (0 : ℝ) < u n := by
    have hmem : ∀ᶠ n in atTop, u n ∈ Set.Ioi (0 : ℝ) :=
      hu_lim.eventually (eventually_mem_nhdsWithin)
    simpa using hmem
  -- Build a strictly-positive surrogate sequence `v` agreeing with `u` eventually,
  -- then transfer the limit by congruence.
  classical
  set v : ℕ → ℝ := fun n => if 0 < u n then u n else 1 with hv_def
  have hv_pos : ∀ n, 0 < v n := by
    intro n; simp only [hv_def]; split
    · assumption
    · exact one_pos
  have hv_eq : ∀ᶠ n in atTop, v n = u n := by
    filter_upwards [hu_evpos] with n hn
    simp only [hv_def, if_pos hn]
  -- Abbreviations.
  set F : ℕ → ℝ → ℝ :=
    fun n x => Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨v n, (hv_pos n).le⟩) x)
    with hF_def
  set g : ℝ → ℝ := fun x => Real.negMulLog (pX x) with hg_def
  -- Per-time integrability of the entropy integrands (also yields measurability).
  have hFint : ∀ n, Integrable (F n) volume := by
    intro n
    rw [hF_def]
    exact convDensityAdd_negMulLog_integrable_pub hpX_nn hpX_meas hpX_int hpX_mass hpX_mom
      (hv_pos n)
  -- `v → 0⁺`: agrees with `u` eventually, and `u → 0⁺`.
  have hv_lim : Tendsto v atTop (𝓝[Set.Ioi 0] 0) :=
    hu_lim.congr' (hv_eq.mono fun n hn => hn.symm)
  -- `v` converges, hence its range is bounded above.
  have hv_bdd : BddAbove (Set.range v) :=
    (hv_lim.mono_right nhdsWithin_le_nhds).bddAbove_range
  -- Abbreviation for the target value `a := ∫ g = ∫ negMulLog pX`.
  set a : ℝ := ∫ x, g x ∂volume with ha_def
  -- **(β) lower bound** (`negMulLog_convDensity_entropy_ge_density`):
  -- for every `n`, `∫ negMulLog pX ≤ ∫ F n`, i.e. `a ≤ ∫ F n`.
  have hβ : ∀ n, a ≤ ∫ x, F n x ∂volume := by
    intro n
    rw [ha_def, hg_def, hF_def]
    exact negMulLog_convDensity_entropy_ge_density hpX_nn hpX_meas hpX_int hpX_mass hpX_mom
      hpX_ent (v_Z := 1) one_pos v hv_pos n
  -- **(α) limsup upper bound** (`negMulLog_convDensity_limsup_le`):
  -- `limsup (∫ F ·) ≤ ∫ negMulLog pX = a`.
  have hα : Filter.limsup (fun n => ∫ x, F n x ∂volume) atTop ≤ a := by
    rw [ha_def, hg_def]
    have hlim := InformationTheory.EPIG2KLFatou.negMulLog_convDensity_limsup_le
      hpX_nn hpX_meas hpX_int hpX_mass hpX_mom hpX_ent (σ2 := 1) one_ne_zero v hv_pos hv_lim
    -- The lever's summand `∫ negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨v n,_⟩))`
    -- is `F n` by definition.
    simpa only [hF_def] using hlim
  -- **Uniform upper bound on `∫ F n`**: the Gaussian
  -- maximum-entropy bound `negMulLog_convDensityAdd_gaussian_entropy_upper` gives a per-`n`
  -- bound with a uniform variance majorant `V` (since the `v n` are bounded above).
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ n, (∫ x, F n x ∂volume) ≤ C := by
    -- Pick a real bound `B` on the range of `v`, and the majorant `V := ∫ x²pX + B + 1`.
    obtain ⟨B, hB⟩ := hv_bdd
    have hBnn : (0 : ℝ) ≤ B := le_trans (hv_pos 0).le (hB (Set.mem_range_self 0))
    set Vr : ℝ := (∫ x, x ^ 2 * pX x ∂volume) + B + 1 with hVr_def
    have hVr_pos : (0 : ℝ) < Vr := by
      have hmom_nn : (0 : ℝ) ≤ ∫ x, x ^ 2 * pX x ∂volume :=
        integral_nonneg fun x => mul_nonneg (sq_nonneg x) (hpX_nn x)
      have : (0 : ℝ) < (∫ x, x ^ 2 * pX x ∂volume) + B + 1 := by positivity
      rwa [hVr_def]
    refine ⟨(1/2) * Real.log (2 * Real.pi * Real.exp 1 * Vr), fun n => ?_⟩
    have hVnn : (0 : ℝ≥0) ≠ Vr.toNNReal := by
      intro h; exact hVr_pos.ne' (by rw [← Real.coe_toNNReal Vr hVr_pos.le, ← h]; rfl)
    have hVle : (∫ x, x ^ 2 * pX x ∂volume) + v n ≤ (Vr.toNNReal : ℝ) := by
      rw [Real.coe_toNNReal Vr hVr_pos.le, hVr_def]
      have : v n ≤ B := hB (Set.mem_range_self n)
      linarith
    have hub := negMulLog_convDensityAdd_gaussian_entropy_upper
      hpX_nn hpX_meas hpX_int hpX_mass hpX_mom (t := v n) (hv_pos n)
      (V := Vr.toNNReal) hVle (Ne.symm hVnn)
    -- The bound's variance witness `⟨v n,_⟩` matches `F n`, and `V.toNNReal` coerces back.
    rw [hF_def]
    calc (∫ x, Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨v n, (hv_pos n).le⟩) x) ∂volume)
        ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * (Vr.toNNReal : ℝ)) := hub
      _ = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * Vr) := by
            rw [Real.coe_toNNReal Vr hVr_pos.le]
  -- Boundedness witnesses for the squeeze.
  have hbdd_le : Filter.IsBoundedUnder (· ≤ ·) atTop (fun n => ∫ x, F n x ∂volume) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall hC)
  have hbdd_ge : Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => ∫ x, F n x ∂volume) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hβ)
  -- `a ≤ liminf (∫ F ·)` from the (β) lower bound.
  have hliminf : a ≤ Filter.liminf (fun n => ∫ x, F n x ∂volume) atTop :=
    le_liminf_of_le (Filter.isCoboundedUnder_ge_of_le atTop hC) (Eventually.of_forall hβ)
  -- Squeeze: `∫ F n → a`.
  have hL1 :
      Tendsto (fun n => ∫ x, F n x ∂volume) atTop (𝓝 a) :=
    tendsto_of_le_liminf_of_limsup_le hliminf hα hbdd_le hbdd_ge
  -- The goal's target `𝓝 (∫ negMulLog pX)` is already `𝓝 a` (folded via `g`/`a`).
  -- Transfer back from `v` to `u` (they agree eventually). The goal's per-`n`
  -- variance witness is `(u n).toNNReal`; on the eventual set where `v n = u n`
  -- (and `u n > 0`) this equals `⟨v n, (hv_pos n).le⟩`.
  refine hL1.congr' ?_
  filter_upwards [hv_eq, hu_evpos] with n hn hupos
  have hwit : (u n).toNNReal = (⟨v n, (hv_pos n).le⟩ : ℝ≥0) := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ hupos.le]
    exact hn.symm
  simp only [hF_def, Function.comp_apply, hwit]

/-- **Heat-flow differential-entropy endpoint continuity.** With explicit regularity
preconditions on `X, Z` (measurability, independence, Gaussian noise law
`P.map Z = 𝒩(0, v_Z)`) and a Real density witness `pX` for `P.map X`, the inner
differential entropy of the heat-flow path is `ContinuousWithinAt (Set.Ioi 0) 0`:

`t ↦ differentialEntropy (P.map (X + √t·Z))` is continuous at `t = 0⁺`.

The density identification `pPath_eq_convDensityAdd` turns the pushforward density
into `convDensityAdd pX (gaussianPDFReal 0 ⟨t·v_Z,_⟩)` for each `t > 0`, the
differential entropy becomes `∫ negMulLog (convDensityAdd …)`, the
entropy-integral convergence `differentialEntropy_convDensity_integral_tendsto`
(reparameterised `t' := t·v_Z`) supplies the limit, and `ContinuousWithinAt`
is recovered with the endpoint value `differentialEntropy (P.map X) = ∫ negMulLog pX`.
All fields are preconditions (regularity / input-distribution data); no continuity
conclusion is bundled.
@audit:ok -/
theorem heatFlowDifferentialEntropy_continuousWithinAt_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (X Z : Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (hX_meas : Measurable X) (hZ_meas : Measurable Z) (hXZ_indep : IndepFun X Z P)
    (v_Z : ℝ≥0) (hv_Z_pos : 0 < v_Z) (hZ_law : P.map Z = gaussianReal 0 v_Z)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume) :
    ContinuousWithinAt
      (fun t : ℝ => differentialEntropy (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      (Set.Ioi 0) 0 := by
  have hv_Z_pos' : (0 : ℝ) < v_Z := hv_Z_pos
  -- Endpoint value: `f 0 = differentialEntropy (P.map X) = ∫ negMulLog pX`.
  have h_path0 : (fun ω => X ω + Real.sqrt (0 : ℝ) * Z ω) = X := by
    funext ω; simp [Real.sqrt_zero]
  have h_end_val :
      differentialEntropy (P.map (fun ω => X ω + Real.sqrt (0 : ℝ) * Z ω))
        = ∫ x, Real.negMulLog (pX x) ∂volume := by
    rw [h_path0, hpX_law,
      differentialEntropy_eq_integral_withDensity hpX_meas.ennreal_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hpX_nn x)]
  -- Per-`t > 0`, the inner differential entropy equals the `convDensityAdd`
  -- entropy integral with variance `t·v_Z`.
  have h_perT : ∀ t : ℝ, 0 < t →
      differentialEntropy (P.map (fun ω => X ω + Real.sqrt t * Z ω))
        = ∫ x, Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 (t * v_Z).toNNReal) x) ∂volume := by
    intro t ht
    have htv : (0 : ℝ) < t * v_Z := mul_pos ht hv_Z_pos'
    -- `(t·v_Z).toNNReal = ⟨t·v_Z, _⟩` (variance witness produced by `pPath_eq_convDensityAdd`).
    have hwit : (t * (v_Z : ℝ)).toNNReal = (⟨t * v_Z, htv.le⟩ : ℝ≥0) := by
      apply NNReal.coe_injective; rw [Real.coe_toNNReal _ htv.le]; rfl
    rw [hwit]
    -- `P.map (X + √t·Z) = P.map (gaussianConvolution X Z t)` (defeq).
    have hpath_eq :
        (fun ω => X ω + Real.sqrt t * Z ω)
          = InformationTheory.Shannon.FisherInfoV2.gaussianConvolution X Z t := rfl
    rw [hpath_eq]
    -- density identification
    have hrn := InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
      X Z hX_meas hZ_meas hXZ_indep v_Z hv_Z_pos hZ_law pX hpX_nn hpX_meas hpX_law ht
    unfold differentialEntropy
    -- push the a.e. density identity into the integrand.
    refine integral_congr_ae ?_
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal]
    unfold convDensityAdd
    exact integral_nonneg fun y =>
      mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- Reparameterise the entropy-integral limit `t' := t·v_Z`. First the inner reparam.
  have h_reparam : Tendsto (fun t : ℝ => t * (v_Z : ℝ)) (𝓝[Set.Ioi 0] 0) (𝓝[Set.Ioi 0] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun t : ℝ => t * (v_Z : ℝ)) (𝓝 0) (𝓝 (0 * (v_Z : ℝ))) :=
        (continuous_mul_const (v_Z : ℝ)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos ht hv_Z_pos'
  have h_layer2 := differentialEntropy_convDensity_integral_tendsto
    hpX_nn hpX_meas hpX_int hpX_mass hpX_mom hpX_ent
  have h_tendsto :
      Tendsto (fun t : ℝ => ∫ x, Real.negMulLog
        (convDensityAdd pX (gaussianPDFReal 0 (t * v_Z).toNNReal) x) ∂volume)
        (𝓝[Set.Ioi 0] 0) (𝓝 (∫ x, Real.negMulLog (pX x) ∂volume)) :=
    h_layer2.comp h_reparam
  -- Assemble `ContinuousWithinAt`.
  rw [ContinuousWithinAt, h_end_val]
  refine h_tendsto.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (h_perT t ht).symm

/-- **AntitoneOn endpoint-insert** — the OrderDual mirror of
`MonotoneOn.insert_of_continuousWithinAt`. If `f` is `AntitoneOn s` and
left-continuous-within-`s` at a cluster point `x`, then `f` is `AntitoneOn` the
augmented set `insert x s`. Used to re-attach the endpoint `t = 0` to the genuine
interior `AntitoneOn (Set.Ioi 0)`.

Mathlib has the monotone version only; this is its dual via `OrderDual.toDual`
(an order-reversing homeomorphism on `β`), which sends `AntitoneOn f s` to
`MonotoneOn (toDual ∘ f) s` and preserves `ContinuousWithinAt`.
@audit:ok -/
theorem _root_.AntitoneOn.insert_of_continuousWithinAt
    {α β : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    [TopologicalSpace β] [LinearOrder β] [OrderClosedTopology β]
    {f : α → β} {s : Set α} {x : α}
    (hf : AntitoneOn f s) (hx : ClusterPt x (Filter.principal s))
    (h'x : ContinuousWithinAt f s x) :
    AntitoneOn f (insert x s) := by
  -- `AntitoneOn f s` is `MonotoneOn (toDual ∘ f) s`; apply the monotone insert.
  have hmono : MonotoneOn (fun a => OrderDual.toDual (f a)) s := hf.dual_right
  have hcont : ContinuousWithinAt (fun a => OrderDual.toDual (f a)) s x :=
    continuous_toDual.continuousWithinAt.comp h'x (Set.mapsTo_univ _ _)
  exact (hmono.insert_of_continuousWithinAt hx hcont).dual_right

/-- **Heat-flow endpoint regularity bundle** (precondition for the G2 wall lemma).

Carries exactly the regularity / input-distribution data the density-identification
bridge (`pPath_eq_convDensityAdd`) and the entropy-integral machinery
(`differentialEntropy_convDensity_integral_tendsto`) require, at the endpoint
`t = 0⁺`:

* `hX_meas` / `hZ_meas` / `hXZ_indep` — measurability + independence of the de
  Bruijn pair `X ⊥ Z` (Cover–Thomas 17.7.2 standing assumptions).
* `v_Z` / `hv_Z_pos` / `hZ_law` — the Gaussian noise law `P.map Z = 𝒩(0, v_Z)`
  (general variance, so the sum instance `Z_X+Z_Y ∼ 𝒩(0,2)` fits).
* `pX` / `hpX_nn` / `hpX_meas` / `hpX_law` — a Real density witness for `P.map X`.
* `hpX_int` / `hpX_mass` / `hpX_mom` — `pX` is a probability density with finite
  second moment.
* `hpX_ent` — `negMulLog pX` is `volume`-integrable, i.e. the input differential
  entropy `h(X)` is finite (a regularity precondition on the input distribution,
  not derivable from L¹ + second moment).

Every field is a precondition (regularity / input-distribution data); none is a
continuity / L¹-convergence / density-identification conclusion. This is not a
load-bearing hypothesis bundle — the analytic content is discharged genuinely by
`heatFlowDifferentialEntropy_continuousWithinAt_zero`, which only consumes these
fields as inputs. -/
structure IsHeatFlowEndpointRegular {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] where
  hX_meas : Measurable X
  hZ_meas : Measurable Z
  hXZ_indep : IndepFun X Z P
  v_Z : ℝ≥0
  hv_Z_pos : 0 < v_Z
  hZ_law : P.map Z = gaussianReal 0 v_Z
  pX : ℝ → ℝ
  hpX_nn : ∀ x, 0 ≤ pX x
  hpX_meas : Measurable pX
  hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x))
  hpX_int : Integrable pX volume
  hpX_mass : (∫ y, pX y ∂volume) = 1
  hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume
  hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume

/-- **Heat-flow entropy-power endpoint continuity.**

`t ↦ entropyPower (P.map (fun ω => X ω + √t · Z ω))` is `ContinuousWithinAt
(Set.Ioi 0) 0` (the limit `t → 0⁺`). The consumer
(`csiszarLogRatioGap_continuousWithinAt_zero`) reduces to three instances of this
single endpoint term; the interior `t > 0` continuity is supplied separately and
genuinely from `csiszarLogRatioGap_differentiableOn_interior` (`.continuousOn`).

The endpoint is discharged via the inner differential-entropy continuity
`heatFlowDifferentialEntropy_continuousWithinAt_zero` (density identification
`pPath_eq_convDensityAdd` + reparameterised entropy-integral convergence
`differentialEntropy_convDensity_integral_tendsto`), with `entropyPower =
exp ∘ (2·differentialEntropy)` lifting it via `Real.continuous_exp`.

The signature takes `IsHeatFlowEndpointRegular X Z P`, whose fields are all
preconditions (regularity / input-distribution data); no continuity /
density-identification conclusion is bundled.
@audit:ok -/
@[entry_point]
theorem heatFlowEntropyPower_continuousWithinAt_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_endpt : IsHeatFlowEndpointRegular X Z P) :
    ContinuousWithinAt
      (fun t : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      (Set.Ioi (0 : ℝ)) 0 := by
  -- Genuine reduction: `entropyPower = exp ∘ (2 · differentialEntropy)`, so the
  -- endpoint continuity follows from the endpoint continuity of the inner
  -- differential entropy via `Real.continuous_exp`.
  have key :
      ContinuousWithinAt
        (fun t : ℝ => differentialEntropy (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
        (Set.Ioi (0 : ℝ)) 0 :=
    heatFlowDifferentialEntropy_continuousWithinAt_zero X Z P
      h_endpt.hX_meas h_endpt.hZ_meas h_endpt.hXZ_indep
      h_endpt.v_Z h_endpt.hv_Z_pos h_endpt.hZ_law
      h_endpt.pX h_endpt.hpX_nn h_endpt.hpX_meas h_endpt.hpX_law
      h_endpt.hpX_int h_endpt.hpX_mass h_endpt.hpX_mom h_endpt.hpX_ent
  have hcomp :
      ContinuousWithinAt
        (fun t : ℝ => Real.exp (2 *
          differentialEntropy (P.map (fun ω => X ω + Real.sqrt t * Z ω))))
        (Set.Ioi (0 : ℝ)) 0 :=
    ((key.const_smul (2 : ℝ)).rexp)
  -- `entropyPower μ = exp (2 * differentialEntropy μ)` definitionally.
  simpa only [entropyPower, smul_eq_mul] using hcomp

end InformationTheory.Shannon
