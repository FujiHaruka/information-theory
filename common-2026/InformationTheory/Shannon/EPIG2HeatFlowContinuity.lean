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
import InformationTheory.Shannon.EntropyPowerInequality
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPIStamDischarge
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.FisherInfoV2DeBruijnPerTime
import InformationTheory.Shannon.FisherInfoV2DeBruijnAssembly
import InformationTheory.Shannon.EPIVitaliAE
import InformationTheory.Shannon.EPIVitaliUnifTight
import InformationTheory.Shannon.EPIVitaliUI

/-!
# G2: heat-flow entropy-power continuity at the endpoint `t = 0⁺`

This file isolates the single analytic atom shared by the two EPI continuity
consumers in `EPIStamToBridge.lean`:

* `csiszarLogRatioGap_continuousOn` (R-5-b, live: feeds `antitoneOn_of_deriv_nonpos`
  in R-5-c), and
* `csiszarGap1Source_continuousOn` (A-4-1, dead difference version).

Both reduce, at the endpoint `t = 0`, to the continuity of a single term
`t ↦ entropyPower (P.map (fun ω => X ω + √t · Z ω))` as `t → 0⁺` along the
heat-flow ray. The interior `t > 0` is genuine (already supplied by
`csiszarGap1Source_differentiableOn_interior` / `csiszarLogRatioGap_differentiableOn_interior`).

## Surface shrink (2026-06-04): full ray → endpoint `t = 0⁺` only

The shared wall is now `heatFlowEntropyPower_continuousWithinAt_zero`, claiming
only `ContinuousWithinAt (Set.Ioi 0) 0` (the single endpoint limit `t → 0⁺`),
not the full-ray `ContinuousOn (Set.Ici 0)`. The interior `t > 0` continuity is
recovered *genuinely* on the consumer side (`EPIStamToBridge.lean`) from
`csiszarLogRatioGap_differentiableOn_interior` (`.continuousOn`, no wall), and the
endpoint is re-attached with the OrderDual mirror
`AntitoneOn.insert_of_continuousWithinAt` (added in this file). Net honesty gain:
the residual shrinks from "continuity along every ray point" to "continuity at the
single endpoint `t = 0⁺`"; the interior is now honest-genuine.

## GATE verdict (2026-06-03): NO-GO — `wall:heatflow-continuity`

The endpoint continuity hinges on a `t = 0⁺`-uniform integrable pointwise
majorant `g` with `‖negMulLog (f_t x)‖ ≤ g x` for all small `t`, required by
`MeasureTheory.continuousWithinAt_of_dominated`. Such a `g` cannot be built from
the fields available in `IsDeBruijnRegularityHyp`:

* The only smoothed-density envelopes (`convDensityAdd_logFactor_poly_majorant`,
  `_chain_domination`, `gaussGradMaj`, all in `FisherInfoV2DeBruijnAssembly.lean`,
  all `private`) are **fixed-`t`** with constants that **diverge as `t → 0⁺`**
  (`A_up ⊃ (1/2)·log(4πt) + 2R²/t`, slope `B = 2/t`) and are restricted to
  `s ∈ Ioo (t/2, 2t)` — explicitly bounded away from `0`.
* The regularity fields supply only `pX_nn`, `pX_meas`, `pX_law` (an L¹ density)
  and `pX_mom` (finite second moment) — no L^∞ / continuity control on `pX`. For a
  general L¹ + finite-second-moment density `pX`, `negMulLog (pX ∗ g_t)` admits no
  single `t`-uniform integrable pointwise envelope as `t → 0⁺` (e.g. `pX` with an
  integrable singularity).

`entropyPower` / `differentialEntropy` continuity is absent in both Mathlib and
InformationTheory (loogle: 0 declarations). The endpoint atom is therefore parked
as a shared sorry lemma `heatFlowEntropyPower_continuousWithinAt_zero` under the
(now SUPERSEDED) wall name `heatflow-continuity` — see the wall register; the live
residual is `wall:approx-identity-L1`. The DCT machinery
(`continuousWithinAt_of_dominated`) itself is fully present in Mathlib; the wall
is the uniform majorant only.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Topology

/-! ## Layer 1 — approximate-identity L¹ convergence (moved)

The density-level approximate-identity L¹ convergence `convDensityAdd pX g_t → pX`
in `L¹(volume)` as `t → 0⁺` now lives in `EPIApproxIdentityL1.lean` as
`convDensityAdd_tendsto_L1_zero` (with its genuine translation-continuity /
continuous-Minkowski / difference-representation helpers). It is not consumed by
the layer-2 machinery below (which goes through the Vitali UI/UT/ae witnesses), so
this file no longer carries a (formerly orphan, duplicate) copy. -/

/-! ## Layer 1' — entropy finiteness of the limit density (now a precondition)

`Integrable (negMulLog pX)` (= `h(X) < ∞`, differential entropy of the limit
density `pX` finite) is required as the limit-side `MemLp` / `Integrable` input by
the Vitali (`tendsto_Lp_of_tendsto_ae`) and the L¹→integral
(`tendsto_integral_of_L1'`) machinery. It does **not** follow from the L¹ +
finite-second-moment regularity of `pX` (a concentrated density can have
`∫ negMulLog pX = −∞`, an under-hypothesised / insufficient signature in the sense
of CLAUDE.md「検証の誠実性」). Rather than claim a false implication, it is now
carried as an explicit **`hpX_ent` precondition** (plan Phase 5-F, 落とし穴2 option
a): the input `X` has finite differential entropy. This is a regularity
precondition on the input distribution, not a load-bearing conclusion. The former
`negMulLog_integrable_of_density` lemma (which falsely claimed derivability from L¹
+ second moment) is deleted. -/

/-! ## Layer 1'' — per-time entropy-integrand integrability (parked wall)

The L¹→integral machinery (`tendsto_integral_of_L1'`) requires
`Integrable (negMulLog (convDensityAdd pX g_t))` for each `t > 0`. Mathlib-internal
asset `convDensityAdd_negMulLog_integrable` (FisherInfoV2DeBruijnAssembly.lean:2529)
proves exactly this but is `private` (file-scoped). Re-exposed here as a public
shared sorry lemma; a follow-up may make the Assembly version public and discharge
this by delegation (genuine, no new analytic content). -/

/-- **Layer 1'' (per-time entropy-integrand integrability).**
For each `t > 0`, `negMulLog (convDensityAdd pX g_t)` is `volume`-integrable.

Closed (2026-06-04, plan Phase 5-E) by importing the genuine in-tree asset
`FisherInfoV2.convDensityAdd_negMulLog_integrable`
(`FisherInfoV2DeBruijnAssembly.lean:2529`, `@audit:ok`, sorryAx-free). The asset
was formerly `private` (file-scoped); it is now public, and this lemma delegates to
it verbatim (same conclusion type). Pure plumbing, no new analytic content — the
former `private` file-scope obstacle is removed.
@audit:ok -/
theorem convDensityAdd_negMulLog_integrable_pub
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume :=
  InformationTheory.Shannon.FisherInfoV2.convDensityAdd_negMulLog_integrable
    pX hpX_nn hpX_meas hpX_int hpX_mass hpX_mom ht

/-! ## Layer 2 — UnifIntegrable / UnifTight witnesses (parked) + genuine lifting

Given the parked layer-1 inputs and the regularity of `pX`, the lift from L¹
density convergence to entropy-integral convergence is genuine Mathlib machinery
(`tendsto_Lp_of_tendsto_ae` + `tendsto_integral_of_L1'`, both `[IsFiniteMeasure]`-
free), modulo the `UnifIntegrable` / `UnifTight` witnesses (parked). -/

/-! The UI witness `negMulLog_convDensity_unifIntegrable` now lives in
`EPIVitaliUI.lean` (genuine `withDensity` probability framing + Gaussian
maximum-entropy upper bound; only the de la Vallée-Poussin indicator-tail core
parked under `wall:approx-identity-L1`). It carries the extra regularity
precondition `hpX_mass : (∫ y, pX y) = 1` (needed for the probability framing,
supplied by the layer-2 consumer). Consumed below by the layer-2 machinery. -/

/-- **Layer 2 (genuine lifting machinery).** Density-level entropy-integral
convergence: given the parked layer-1 input (approximate-identity L¹ convergence),
the regularity of `pX`, and the entropy-finiteness precondition `hpX_ent`
(= `h(X) < ∞`, a regularity precondition on the input — see Layer 1' note), the
differential-entropy integrals of the heat-smoothed densities converge to the
entropy integral of `pX` as `t → 0⁺`:

`∫ negMulLog (convDensityAdd pX g_t) ∂volume → ∫ negMulLog pX ∂volume`.

This is the genuine Phase-3 machinery: sequentialisation of `𝓝[Ioi 0] 0`
(`Filter.tendsto_iff_seq_tendsto`, `nhdsWithin` countably generated) → Vitali
(`tendsto_Lp_of_tendsto_ae`, `[IsFiniteMeasure]`-free via `UnifTight`) →
L¹→integral (`tendsto_integral_of_L1'`, measure/filter-free). No own `sorry`; the
only residual is the parked layer-1 / UI / UT approximate-identity machinery it
consumes (`wall:approx-identity-L1`). The former limit-density entropy-finiteness
residual is now the `hpX_ent` precondition (plan Phase 5-F, not a residual).

Independent honesty audit 2026-06-04 (fresh subagent, commit 36fc577): PASS (no own
residual; transitive only). Machine-checked: own body is `sorry`-free (`#print
axioms` = `[propext, sorryAx, Classical.choice, Quot.sound]` where `sorryAx` is
purely transitive through the consumed UI/UT witnesses; the sole own-file `sorry` is
the UI witness `:153`, NOT this body). The 2026-06-04 subsequence-route rewrite is
genuine: a.e. convergence is reconstructed from the genuine
`negMulLog_convDensity_tendsto_ae_subseq` (`@audit:ok`, sorryAx-free) via
`tendsto_of_subseq_tendsto` + `tendsto_Lp_of_tendsto_ae`, with UI/UT restricted to
the reindexed family `fun i => F (ns (ms i))` (trivial `∀ i` reindex, no leak). The
a.e. core is NOT hidden in a hypothesis — it is rebuilt from the genuine subsequence
witness, so the removed full-sequence ae witness's substance is not laundered
elsewhere. All hypotheses are regularity/normalisation (hpX_nn/meas/int/mass/mom/
ent). NOT circular / load-bearing / degenerate; sufficiency holds. Not `@audit:ok`
only because of the transitive layer-1 sorries (UI/UT). -/
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
  -- Vitali (infinite-measure version, via UnifTight): `eLpNorm (F n - g) 1 → 0`.
  have haef : ∀ n, AEStronglyMeasurable (F n) volume := fun n => (hFint n).aestronglyMeasurable
  have hg' : MemLp g 1 volume := by
    rw [hg_def]
    exact memLp_one_iff_integrable.mpr hpX_ent
  -- `v → 0⁺`: agrees with `u` eventually, and `u → 0⁺`.
  have hv_lim : Tendsto v atTop (𝓝[Set.Ioi 0] 0) :=
    hu_lim.congr' (hv_eq.mono fun n hn => hn.symm)
  -- `v` converges, hence its range is bounded above (supplies `hu_bdd` to the
  -- UI/UT witnesses, whose tail estimates require boundedness of the variances).
  have hv_bdd : BddAbove (Set.range v) :=
    (hv_lim.mono_right nhdsWithin_le_nhds).bddAbove_range
  have hui : UnifIntegrable F 1 volume :=
    negMulLog_convDensity_unifIntegrable hpX_nn hpX_meas hpX_int hpX_mass hpX_mom v hv_pos hv_bdd
  have hut : UnifTight F 1 volume :=
    negMulLog_convDensity_unifTight hpX_nn hpX_meas hpX_int hpX_mom v hv_pos hv_bdd
  -- Vitali via the subsequence route: `tendsto_Lp_of_tendsto_ae` needs full-sequence
  -- a.e. convergence, which we only have along subsequences (the genuine ae witness
  -- `negMulLog_convDensity_tendsto_ae_subseq`). Use `tendsto_of_subseq_tendsto`: it
  -- suffices that every subsequence has a further subsequence converging in L¹.
  have hVitali :
      Tendsto (fun n => eLpNorm (F n - g) 1 volume) atTop (𝓝 0) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    -- `v ∘ ns → 0⁺` too.
    have hvns_pos : ∀ k, 0 < v (ns k) := fun k => hv_pos (ns k)
    have hvns_lim : Tendsto (fun k => v (ns k)) atTop (𝓝[Set.Ioi 0] 0) :=
      hv_lim.comp hns
    obtain ⟨ms, _hms_mono, hms_ae⟩ :=
      negMulLog_convDensity_tendsto_ae_subseq hpX_nn hpX_meas hpX_int hpX_mom
        (fun k => v (ns k)) hvns_pos hvns_lim
    refine ⟨ms, ?_⟩
    -- a.e. convergence of the reindexed family `F (ns (ms i))`.
    have hae : ∀ᵐ x ∂volume,
        Tendsto (fun i => F (ns (ms i)) x) atTop (𝓝 (g x)) := by
      filter_upwards [hms_ae] with x hx
      simpa only [hF_def, hg_def] using hx
    -- Restrict UI / UT to the subsequence `i ↦ F (ns (ms i))` (reindexing is trivial
    -- since both quantifiers are `∀ i`).
    refine tendsto_Lp_of_tendsto_ae (le_refl 1) (by simp)
      (fun i => haef (ns (ms i))) hg' ?_ ?_ hae
    · intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := hui hε
      exact ⟨δ, hδ, fun i s hs hμs => hδ' (ns (ms i)) s hs hμs⟩
    · intro ε hε
      obtain ⟨s, hμs, hsε⟩ := hut hε
      exact ⟨s, hμs, fun i => hsε (ns (ms i))⟩
  -- L¹→integral: `∫ F n → ∫ g`.
  have hfi : Integrable g volume := by
    rw [hg_def]
    exact hpX_ent
  have hFi : ∀ᶠ n in atTop, Integrable (F n) volume :=
    Eventually.of_forall hFint
  have hL1 :
      Tendsto (fun n => ∫ x, F n x ∂volume) atTop (𝓝 (∫ x, g x ∂volume)) :=
    tendsto_integral_of_L1' g hfi hFi hVitali
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

/-- **Step 1 (genuine standalone helper): heat-flow differential-entropy endpoint
continuity.** With explicit regularity preconditions on `X, Z` (measurability,
independence, Gaussian noise law `P.map Z = 𝒩(0, v_Z)`) and a Real density witness
`pX` for `P.map X`, the inner differential entropy of the heat-flow path is
`ContinuousWithinAt (Set.Ioi 0) 0`:

`t ↦ differentialEntropy (P.map (X + √t·Z))` is continuous at `t = 0⁺`.

This is the genuine bridge (plan Phase 5-B, Approach B-1..B-4): the density
identification `pPath_eq_convDensityAdd` (`@audit:ok`, general `v_Z`) turns the
pushforward density into `convDensityAdd pX (gaussianPDFReal 0 ⟨t·v_Z,_⟩)` for each
`t > 0`, the differential entropy becomes `∫ negMulLog (convDensityAdd …)` (B-2),
the layer-2 machinery `differentialEntropy_convDensity_integral_tendsto`
(reparameterised `t' := t·v_Z`) supplies the limit (B-3), and `ContinuousWithinAt`
is recovered with the endpoint value `differentialEntropy (P.map X) = ∫ negMulLog pX`
(B-4). All fields are preconditions (regularity / input-distribution data); no
continuity conclusion is bundled. The only residuals are transitive (layer-2
`wall:approx-identity-L1`); this helper itself adds no `@residual`.

Independent honesty audit 2026-06-04 (fresh subagent, commit fa0fe3f): PASS.
Own body is `sorry`-free. After the 2026-06-04 layer-2 subsequence-route rewrite,
the file's only `sorry` warning is the single parked layer-2 UI witness
`negMulLog_convDensity_unifIntegrable` (`wall:approx-identity-L1`); the UT and
a.e.-convergence witnesses are now consumed from `EPIVitaliUnifTight.lean`
(UT, parked) and the genuine `EPIVitaliAE.negMulLog_convDensity_tendsto_ae_subseq`
(0 sorry). `#print axioms` shows `sorryAx` purely transitive through the remaining
UI witness (NOT in the helper's own derivation). The
density bridge call (`pPath_eq_convDensityAdd`, `@audit:ok`) matches signatures
verbatim; `differentialEntropy_convDensity_integral_tendsto.comp h_reparam` is a
genuine `t' := t·v_Z` reparam. Sufficiency holds: conclusion follows from the
regularity hypotheses (no free-variable counterexample — singular `P.map X` is
excluded by the `hpX_law` density witness). NOT circular / load-bearing /
degenerate. Not `@audit:ok` only because of the transitive layer-1 sorries. -/
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
  -- (B-1 + B-2) Per-`t > 0`, the inner differential entropy equals the
  -- `convDensityAdd` entropy integral with variance `t·v_Z`.
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
    -- density identification (B-1)
    have hrn := InformationTheory.Shannon.FisherInfoV2.pPath_eq_convDensityAdd
      X Z hX_meas hZ_meas hXZ_indep v_Z hv_Z_pos hZ_law pX hpX_nn hpX_meas hpX_law ht
    unfold differentialEntropy
    -- (B-2) push the a.e. density identity into the integrand.
    refine integral_congr_ae ?_
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal]
    unfold convDensityAdd
    exact integral_nonneg fun y =>
      mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)
  -- (B-3) Reparameterise the layer-2 limit `t' := t·v_Z`. First the inner reparam.
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
  -- (B-4) Assemble `ContinuousWithinAt`.
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

Independent honesty audit 2026-06-04 (fresh subagent): genuine 0 sorry, sorryAx-free
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`)、循環なし (body は
Mathlib `MonotoneOn.insert_of_continuousWithinAt` の OrderDual mirror、`:= h` でない)、
型クラス制約 (`OrderClosedTopology β` 等) は monotone 版と整合。
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
bridge (`pPath_eq_convDensityAdd`) and the layer-2 machinery
(`differentialEntropy_convDensity_integral_tendsto`) require, at the endpoint
`t = 0⁺`:

* `hX_meas` / `hZ_meas` / `hXZ_indep` — measurability + independence of the de
  Bruijn pair `X ⊥ Z` (Cover-Thomas 17.7.2 standing assumptions).
* `v_Z` / `hv_Z_pos` / `hZ_law` — the Gaussian noise law `P.map Z = 𝒩(0, v_Z)`
  (general variance, so the sum instance `Z_X+Z_Y ∼ 𝒩(0,2)` fits).
* `pX` / `hpX_nn` / `hpX_meas` / `hpX_law` — a Real density witness for `P.map X`.
* `hpX_int` / `hpX_mass` / `hpX_mom` — `pX` is a probability density with finite
  second moment (layer-2 regularity inputs).
* `hpX_ent` — `negMulLog pX` is `volume`-integrable, i.e. the input differential
  entropy `h(X)` is finite (plan Phase 5-F precondition; a regularity precondition
  on the input distribution, not derivable from L¹ + second moment — see Layer 1').

**Every field is a precondition** (regularity / input-distribution data); none is a
continuity / L¹-convergence / density-identification conclusion. This is NOT a
load-bearing hypothesis bundle — the analytic content is discharged genuinely by
`heatFlowDifferentialEntropy_continuousWithinAt_zero`, which only *consumes* these
fields as inputs (cf. `audit-tags.md` "non-bundle check").

Independent honesty audit 2026-06-04 (fresh subagent, commit fa0fe3f): PASS. All
13 fields checked individually — measurability / independence / Gaussian noise law
/ Real density witness data — every one is a precondition. No field has type
`ContinuousWithinAt …` / a limit / an L¹-convergence / a density-identification
equality; the structure carries no conclusion atom. Not load-bearing (tier 5),
not degenerate. The wall lemma consumes the bundle as inputs to the genuine helper.

Plan Phase 5-F (2026-06-04): a 14th field `hpX_ent` (`Integrable (negMulLog pX)`,
input entropy finiteness) was added. It is a regularity precondition on the input
distribution `X` (the input has finite differential entropy), NOT a continuity /
density-identification conclusion — distinct from the heat-flow continuity that is
the wall lemma's conclusion. It replaces the former false-as-stated
`negMulLog_integrable_of_density` lemma (which claimed entropy finiteness followed
from L¹ + second moment; a concentrated density refutes that). -/
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

/-- **G2 shared wall lemma (endpoint version)** — heat-flow entropy-power
continuity at the single endpoint `t = 0⁺`.

`t ↦ entropyPower (P.map (fun ω => X ω + √t · Z ω))` is `ContinuousWithinAt
(Set.Ioi 0) 0` (the limit `t → 0⁺`). The live consumer
(`csiszarLogRatioGap_continuousWithinAt_zero`) reduces to three instances of this
single endpoint term; the interior `t > 0` continuity is supplied separately and
genuinely from `csiszarLogRatioGap_differentiableOn_interior` (`.continuousOn`),
so the wall is confined to the one endpoint atom.

The endpoint `t = 0⁺` is genuinely discharged (2026-06-04, plan Phase 5-B): the
inner differential-entropy continuity is the standalone helper
`heatFlowDifferentialEntropy_continuousWithinAt_zero` (density identification
`pPath_eq_convDensityAdd` + reparameterised layer-2 machinery
`differentialEntropy_convDensity_integral_tendsto`), and `entropyPower =
exp ∘ (2·differentialEntropy)` lifts it via `Real.continuous_exp`. The direct
`sorry` is gone; the only residual is transitive, through the layer-2 machinery's
`wall:approx-identity-L1` (approximate-identity L¹ convergence).

The bridge requires `Measurable X`, `Measurable Z`, `IndepFun X Z P` and a Real
density witness for `P.map X` — not carried by the old `IsDeBruijnRegularityHyp`.
This signature now takes `IsHeatFlowEndpointRegular X Z P` instead, whose fields
are **all preconditions** (regularity / input-distribution data); no continuity /
density-identification conclusion is bundled (not load-bearing). The structure was
threaded down the consumer chain in the same plan (Phase 5-D).

Surface shrink (2026-06-04): the predecessor `heatFlowEntropyPower_continuousOn`
claimed the full ray `ContinuousOn (Set.Ici 0)`; this version shrinks the residual
to the single endpoint, with the interior recovered genuinely on the consumer side.

Residual status (plan Phase 5-B/5-E/5-F closure): this lemma's **own** body is
genuine — it delegates to `heatFlowDifferentialEntropy_continuousWithinAt_zero`
(itself `sorry`-free). The `plan:epi-g2-layer2-moonshot-plan` part of the old
compound is now **closed**:

* Phase 5-E (plumbing): `convDensityAdd_negMulLog_integrable_pub` is now genuine —
  it delegates to the (now public) `@audit:ok` Assembly asset
  `FisherInfoV2.convDensityAdd_negMulLog_integrable`. No longer a residual.
* Phase 5-F (precondition): the limit-density entropy finiteness (former
  `negMulLog_integrable_of_density`, which falsely claimed derivability from L¹ +
  second moment) is now the `hpX_ent` field of `IsHeatFlowEndpointRegular` — a
  regularity precondition, not a residual.

The remaining `sorryAx` in `#print axioms` is therefore purely transitive through
the layer-2 machinery's `wall:approx-identity-L1` only (approximate-identity L¹
convergence: `convDensityAdd_tendsto_L1_zero` + the 3 Vitali UI/UT/ae witnesses).

Independent honesty audit 2026-06-04 (fresh subagent, commit fa0fe3f): PASS as
`honest_residual`. (a) Own body is genuine delegation: `key` from
`heatFlowDifferentialEntropy_continuousWithinAt_zero` (own sorry 0) +
`entropyPower = exp ∘ (2·differentialEntropy)` lift via `.const_smul.rexp`. (b)
`wall:approx-identity-L1` confirmed transitive via the 4 parked Vitali witnesses;
loogle (`MeasureTheory.convolution, MeasureTheory.eLpNorm`) = 0 declarations, so
the general-L¹ approximate-identity convergence is a genuine Mathlib gap (in
register). Signature `IsHeatFlowEndpointRegular X Z P` — all preconditions
(including the new `hpX_ent`, audited above). NOT load-bearing / circular /
wall-misuse.

@residual(wall:approx-identity-L1) -/
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
