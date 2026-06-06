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
import InformationTheory.Shannon.EPIVitaliUI
import InformationTheory.Shannon.EPIG2KLFatouLSC
import InformationTheory.Shannon.EPIG2ConvEntropyDensity
import InformationTheory.Meta.EntryPoint

/-!
# G2: heat-flow entropy-power continuity at the endpoint `t = 0⁺`

This file isolates the single analytic atom used by the live EPI continuity
consumer in `EPIStamToBridge.lean`:

* `csiszarLogRatioGap_continuousOn` (R-5-b, live: feeds `antitoneOn_of_deriv_nonpos`
  in R-5-c).

(The dead difference-version continuity consumer was deleted with the dead
de Bruijn difference subgraph.)

It reduces, at the endpoint `t = 0`, to the continuity of a single term
`t ↦ entropyPower (P.map (fun ω => X ω + √t · Z ω))` as `t → 0⁺` along the
heat-flow ray. The interior `t > 0` is genuine (already supplied by
`csiszarLogRatioGap_differentiableOn_interior`).

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
continuous-Minkowski / difference-representation helpers). The layer-2 machinery
below no longer consumes it: the 2026-06-05 sandwich swap derives the
entropy-integral limit directly from the (α)/(β) bounds (both `@audit:ok`), so the
Vitali UI/UT/ae route and its `wall:approx-identity-L1` witnesses are gone. -/

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

/-! ## Layer 2 — genuine two-sided sandwich (2026-06-05)

The lift from per-time entropy integrals to the endpoint entropy integral is now a
genuine two-sided sandwich, replacing the former Vitali (UnifIntegrable / UnifTight)
route. The previous route consumed parked `wall:approx-identity-L1` witnesses; those
are deleted. The sandwich uses two `@audit:ok` levers plus a genuine maxent bound:

* **(α) limsup upper bound** — `InformationTheory.EPIG2KLFatou.negMulLog_convDensity_limsup_le`
  (Fatou / KL lower-semicontinuity): `limsup (∫ negMulLog f_n) ≤ ∫ negMulLog pX`.
* **(β) per-`n` lower bound** — `negMulLog_convDensity_entropy_ge_density`
  (conditioning reduces entropy): `∫ negMulLog pX ≤ ∫ negMulLog f_n`.
* **uniform upper bound** — `negMulLog_convDensityAdd_gaussian_entropy_upper`
  (Gaussian maximum-entropy, `@audit:ok`): a per-`n` bound with a uniform variance
  majorant (the `v n` are bounded since `v n → 0`), supplying the
  `IsBoundedUnder (· ≤ ·)` witness for the squeeze.

The squeeze `tendsto_of_le_liminf_of_limsup_le` then gives `∫ negMulLog f_n → ∫
negMulLog pX` along sequences, lifted to `𝓝[Ioi 0] 0` via
`Filter.tendsto_iff_seq_tendsto`. -/

/-- **Layer 2 (genuine entropy-integral convergence).** Density-level
entropy-integral convergence: given the regularity of `pX` and the entropy-finiteness
precondition `hpX_ent` (= `h(X) < ∞`, a regularity precondition on the input — see
Layer 1' note), the differential-entropy integrals of the heat-smoothed densities
converge to the entropy integral of `pX` as `t → 0⁺`:

`∫ negMulLog (convDensityAdd pX g_t) ∂volume → ∫ negMulLog pX ∂volume`.

**Genuine, sorryAx-free (2026-06-05).** Sequentialisation of `𝓝[Ioi 0] 0`
(`Filter.tendsto_iff_seq_tendsto`, `nhdsWithin` countably generated), then the
two-sided sandwich described in the section header: (α) limsup upper bound +
(β) per-`n` lower bound (both `@audit:ok`), squeezed by
`tendsto_of_le_liminf_of_limsup_le` with the uniform upper-boundedness witness from
the genuine Gaussian maxent bound `negMulLog_convDensityAdd_gaussian_entropy_upper`
(`@audit:ok`). No `sorry`, no residual.

`#print axioms differentialEntropy_convDensity_integral_tendsto` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-checked 2026-06-05).
All hypotheses are regularity / normalisation (hpX_nn/meas/int/mass/mom/ent); NOT
circular / load-bearing / degenerate; sufficiency holds.

Independent honesty audit 2026-06-05 (fresh subagent): PASS. (a) signature unchanged
across the sandwich swap (git: theorem header is a diff context line in `b8ee036`,
only the body's `have`-steps changed). (b) The sandwich wires (α)
`negMulLog_convDensity_limsup_le` + (β) `negMulLog_convDensity_entropy_ge_density`
(both `@audit:ok`, sorryAx-free) without bundling the conclusion; `σ2:=1` / `v_Z:=1`
are honest auxiliary-scale instances, independent of the kernel variance `u n`.
(c) boundedness supplied by the genuine maxent bound
`negMulLog_convDensityAdd_gaussian_entropy_upper` (`@audit:ok`, body uses
`differentialEntropy_le_gaussian_of_variance_le`, NOT the Vitali route / `wall:approx-identity-L1`,
not vacuous). (d) `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(sorryAx-free, machine-checked 2026-06-05 after `lake build` olean refresh).
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
  -- **(β) lower bound** (`negMulLog_convDensity_entropy_ge_density`, genuine, `@audit:ok`):
  -- for every `n`, `∫ negMulLog pX ≤ ∫ F n`, i.e. `a ≤ ∫ F n`.
  have hβ : ∀ n, a ≤ ∫ x, F n x ∂volume := by
    intro n
    rw [ha_def, hg_def, hF_def]
    exact negMulLog_convDensity_entropy_ge_density hpX_nn hpX_meas hpX_int hpX_mass hpX_mom
      hpX_ent (v_Z := 1) one_pos v hv_pos n
  -- **(α) limsup upper bound** (`negMulLog_convDensity_limsup_le`, genuine, `@audit:ok`):
  -- `limsup (∫ F ·) ≤ ∫ negMulLog pX = a`.
  have hα : Filter.limsup (fun n => ∫ x, F n x ∂volume) atTop ≤ a := by
    rw [ha_def, hg_def]
    have hlim := InformationTheory.EPIG2KLFatou.negMulLog_convDensity_limsup_le
      hpX_nn hpX_meas hpX_int hpX_mass hpX_mom hpX_ent (σ2 := 1) one_ne_zero v hv_pos hv_lim
    -- The lever's summand `∫ negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨v n,_⟩))`
    -- is `F n` by definition.
    simpa only [hF_def] using hlim
  -- **Uniform upper bound on `∫ F n`** (genuine, `@audit:ok`, no wall): the Gaussian
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
continuity conclusion is bundled.

**Genuine, sorryAx-free (2026-06-05).** After the layer-2 sandwich swap, the
consumed `differentialEntropy_convDensity_integral_tendsto` is itself sorryAx-free,
so this helper has no residual. `#print axioms
heatFlowDifferentialEntropy_continuousWithinAt_zero` =
`[propext, Classical.choice, Quot.sound]` (machine-checked 2026-06-05). The density
bridge call (`pPath_eq_convDensityAdd`, `@audit:ok`) matches signatures verbatim;
`differentialEntropy_convDensity_integral_tendsto.comp h_reparam` is a genuine
`t' := t·v_Z` reparam. Sufficiency holds: conclusion follows from the regularity
hypotheses (no free-variable counterexample — singular `P.map X` is excluded by the
`hpX_law` density witness). NOT circular / load-bearing / degenerate.

Independent honesty audit 2026-06-05 (fresh subagent): PASS. After the layer-2
sandwich swap the consumed `differentialEntropy_convDensity_integral_tendsto` is
sorryAx-free, so this helper has no residual; `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (machine-checked). All 14 fields are
preconditions; the density bridge `pPath_eq_convDensityAdd` (`@audit:ok`) is consumed
as input, no conclusion bundled.
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
`sorry` is gone.

**Wall CLOSED (2026-06-05, sandwich swap).** The layer-2 machinery
`differentialEntropy_convDensity_integral_tendsto` was re-derived genuinely via a
two-sided sandwich — the Fatou-LSC limsup upper bound
`InformationTheory.EPIG2KLFatou.negMulLog_convDensity_limsup_le` (α, `@audit:ok`)
plus the conditioning per-`n` lower bound
`negMulLog_convDensity_entropy_ge_density` (β, `@audit:ok`), squeezed by
`tendsto_of_le_liminf_of_limsup_le` with the uniform upper-boundedness witness from
the genuine Gaussian maxent bound `negMulLog_convDensityAdd_gaussian_entropy_upper`
(`@audit:ok`). The Vitali UI/UT route (and the parked
`wall:approx-identity-L1` witnesses) is no longer consumed; the witnesses were
deleted. `#print axioms` is now `[propext, Classical.choice, Quot.sound]`
(sorryAx-free, machine-checked 2026-06-05). This lemma carries no residual.

The bridge requires `Measurable X`, `Measurable Z`, `IndepFun X Z P` and a Real
density witness for `P.map X` — not carried by the old `IsDeBruijnRegularityHyp`.
This signature now takes `IsHeatFlowEndpointRegular X Z P` instead, whose fields
are **all preconditions** (regularity / input-distribution data); no continuity /
density-identification conclusion is bundled (not load-bearing). The structure was
threaded down the consumer chain in the same plan (Phase 5-D).

Surface shrink (2026-06-04): the predecessor `heatFlowEntropyPower_continuousOn`
claimed the full ray `ContinuousOn (Set.Ici 0)`; this version shrinks the residual
to the single endpoint, with the interior recovered genuinely on the consumer side.

Residual status (plan Phase 5-B/5-E/5-F + 2026-06-05 sandwich closure): this
lemma's **own** body is genuine — it delegates to
`heatFlowDifferentialEntropy_continuousWithinAt_zero` (itself `sorry`-free), which
in turn consumes the now-genuine layer-2 machinery. All former residuals are closed:

* Phase 5-E (plumbing): `convDensityAdd_negMulLog_integrable_pub` is genuine —
  it delegates to the (now public) `@audit:ok` Assembly asset
  `FisherInfoV2.convDensityAdd_negMulLog_integrable`.
* Phase 5-F (precondition): the limit-density entropy finiteness is the `hpX_ent`
  field of `IsHeatFlowEndpointRegular` — a regularity precondition, not a residual.
* 2026-06-05 (layer-2 sandwich): the last transitive residual
  (`wall:approx-identity-L1`, via the Vitali UI/UT witnesses) is removed — the
  layer-2 limit is now derived by the (α)/(β) sandwich, both `@audit:ok`. The
  Vitali witnesses were deleted.

`#print axioms heatFlowEntropyPower_continuousWithinAt_zero` is therefore
`[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-checked
2026-06-05). The signature `IsHeatFlowEndpointRegular X Z P` carries only
preconditions (regularity / input-distribution data); no continuity /
density-identification conclusion is bundled (not load-bearing / circular /
wall-misuse). 0 own sorry, 0 residual.

Independent honesty audit 2026-06-05 (fresh subagent): PASS — EPI G2 endpoint
continuity is genuine in general form and `wall:approx-identity-L1` is CLOSED.
Verified: (1) body delegates to `heatFlowDifferentialEntropy_continuousWithinAt_zero`
(`@audit:ok`) + `Real.continuous_exp` lift, no conclusion bundled; (2) the Vitali
UI/UT/ae witnesses are deleted and no active `@residual(wall:approx-identity-L1)`
sorry remains in `InformationTheory/` (all mentions are docstring prose); (3) the
deletion is the legitimate removal of orphaned scaffolding (replaced by the genuine
(α)/(β) sandwich), not concealment — `convDensityAdd_second_moment` etc. are retained
and the module rebuilds clean; (4) `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free, machine-checked).
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
