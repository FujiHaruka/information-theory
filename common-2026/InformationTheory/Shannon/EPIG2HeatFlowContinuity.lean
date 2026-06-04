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
as a shared sorry lemma `heatFlowEntropyPower_continuousWithinAt_zero` with
`@residual(wall:heatflow-continuity)`. The DCT machinery
(`continuousWithinAt_of_dominated`) itself is fully present in Mathlib; the wall
is the uniform majorant only.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIConvDensity
open scoped ENNReal NNReal Topology

/-! ## Layer 1 — approximate-identity L¹ convergence (parked wall)

The single genuine-Mathlib-gap that the layer-2 machinery rests on. Parked as a
shared sorry lemma so the layer-2 lifting (`differentialEntropy` integral
convergence) closes genuinely on top of it. -/

/-- **Layer 1 (approximate-identity L¹ convergence, moonshot core).**
The heat-kernel smoothing `convDensityAdd pX g_t` of an L¹ + finite-second-moment
density `pX` converges to `pX` in `L¹(volume)` as the variance `t → 0⁺`. This is
the standard approximate-identity L¹ convergence; Mathlib's
`convolution_tendsto_right` is pointwise/bump-only (no general L¹ `pX`), and
`tendsto_convDensityAdd_gaussian_zero` is the spatial tail `z → ±∞` (a different
limit). A true Mathlib gap.

@residual(wall:approx-identity-L1) -/
theorem convDensityAdd_tendsto_L1_zero
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) :
    Tendsto (fun t : ℝ =>
      eLpNorm (convDensityAdd pX (gaussianPDFReal 0 t.toNNReal) - pX) 1 volume)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  sorry

/-! ## Layer 1' — entropy finiteness of the limit density (parked wall)

`MemLp (negMulLog pX) 1 volume` (= `h(X) < ∞`) is required as the limit-side
`MemLp`/`Integrable` input by the Vitali (`tendsto_Lp_of_tendsto_ae`) and the
L¹→integral (`tendsto_integral_of_L1'`) machinery. It does **not** follow from the
L¹ + finite-second-moment regularity of `pX` (a concentrated density can have
`∫ negMulLog pX = −∞`). This is the *limit-density* (`t = 0`, `pX` itself) entropy
finiteness — distinct both from the approximate-identity L¹ wall above and from
the register's `wall:entropy-finiteness` (which is the **smoothed** density
`pX ∗ g_t` at `t > 0`, already CLOSED 2026-06-01). The plan (落とし穴2) owns its
closure: add an `Integrable (negMulLog pX)` regularity precondition (option a) or
derive it (option b). Classified as `plan:` not `wall:`: closure path is a
plan-level precondition/derivation decision, not a Mathlib gap.

Audit 2026-06-04 (fresh subagent): reclassified `wall:entropy-finiteness` →
`plan:epi-g2-layer2-moonshot-plan`. The register's `entropy-finiteness` is the
smoothed-density (`t > 0`) form (CLOSED); this limit-density (`t = 0`) finiteness
is plan-owned (落とし穴2, options a/b/c, closure path unsettled). -/

/-- **Layer 1' (entropy finiteness of the limit density).**
`negMulLog pX` is `volume`-integrable (i.e. the differential entropy `h(X)` of the
limit density `pX` is finite). Required as the `hg'` / `hfi` input of the layer-2
machinery. Not derivable from L¹ + finite second moment alone (loogle:
`MeasureTheory.Integrable, Real.negMulLog` → 0 declarations;
`convDensityAdd_negMulLog_integrable` is the `t > 0` smoothed-density form only,
not `pX` itself at `t = 0`).

Audit 2026-06-04 (fresh subagent): reclassified `wall:entropy-finiteness` →
`plan:epi-g2-layer2-moonshot-plan`. This limit-density (`t = 0`, `pX` itself)
entropy finiteness is distinct from the register's `wall:entropy-finiteness`
(smoothed `t > 0` density, CLOSED). It is plan-owned (落とし穴2: add an
`Integrable (negMulLog pX)` regularity precondition or derive it), not a Mathlib
wall — closure is a plan-level precondition decision.
@residual(plan:epi-g2-layer2-moonshot-plan) -/
theorem negMulLog_integrable_of_density
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) :
    Integrable (fun x => Real.negMulLog (pX x)) volume := by
  sorry

/-! ## Layer 1'' — per-time entropy-integrand integrability (parked wall)

The L¹→integral machinery (`tendsto_integral_of_L1'`) requires
`Integrable (negMulLog (convDensityAdd pX g_t))` for each `t > 0`. Mathlib-internal
asset `convDensityAdd_negMulLog_integrable` (FisherInfoV2DeBruijnAssembly.lean:2529)
proves exactly this but is `private` (file-scoped). Re-exposed here as a public
shared sorry lemma; a follow-up may make the Assembly version public and discharge
this by delegation (genuine, no new analytic content). -/

/-- **Layer 1'' (per-time entropy-integrand integrability).**
For each `t > 0`, `negMulLog (convDensityAdd pX g_t)` is `volume`-integrable. This
is a `private` genuine asset in `FisherInfoV2DeBruijnAssembly.lean:2529`
(`convDensityAdd_negMulLog_integrable`, `@audit:ok`, sorryAx-free). Parked here only
because the asset is file-scoped; closing it is pure plumbing (make the Assembly
version public, or relocate), no new analytic content.

Audit 2026-06-04 (fresh subagent): reclassified `wall:entropy-finiteness` →
`plan:epi-g2-layer2-moonshot-plan`. NOT a Mathlib wall — the analytic content is a
genuine in-tree `@audit:ok` asset (smoothed-density entropy finiteness, register's
`entropy-finiteness` is CLOSED). The only obstacle is `private` file-scope; closure
is plan-managed plumbing (plan Phase 3 / inventory §plumbing, "5〜15 行 純 plumbing").
A `wall:` tag would falsely claim a Mathlib gap.
@residual(plan:epi-g2-layer2-moonshot-plan) -/
theorem convDensityAdd_negMulLog_integrable_pub
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume := by
  sorry

/-! ## Layer 2 — UnifIntegrable / UnifTight witnesses (parked) + genuine lifting

Given the parked layer-1 inputs and the regularity of `pX`, the lift from L¹
density convergence to entropy-integral convergence is genuine Mathlib machinery
(`tendsto_Lp_of_tendsto_ae` + `tendsto_integral_of_L1'`, both `[IsFiniteMeasure]`-
free), modulo the `UnifIntegrable` / `UnifTight` witnesses (parked). -/

/-- **Layer 2 UI witness (parked).** Uniform integrability of the entropy
integrands along any sequence `u : ℕ → ℝ` with `u n > 0`. Vitali input `hui`.

@residual(wall:approx-identity-L1) -/
theorem negMulLog_convDensity_unifIntegrable
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) :
    UnifIntegrable
      (fun n => fun x =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
      1 volume := by
  sorry

/-- **Layer 2 UT witness (parked).** Uniform tightness of the entropy integrands
along any sequence `u : ℕ → ℝ` with `u n > 0`. Vitali input `hut` (the additional
hypothesis that makes Vitali work on the infinite-measure space `volume`). The
finite second moment `pX_mom` is expected to drive the tail estimate.

@residual(wall:approx-identity-L1) -/
theorem negMulLog_convDensity_unifTight
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) :
    UnifTight
      (fun n => fun x =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
      1 volume := by
  sorry

/-- **Layer 2 a.e. pointwise convergence (parked).** Along any sequence
`u → 0⁺`, the entropy integrands converge `negMulLog (convDensityAdd pX g_{u n}) →
negMulLog pX` a.e. Follows from the layer-1 L¹ convergence via an a.e.-convergent
subsequence; parked together with layer 1 as the same approximate-identity content
threaded through `Real.continuous_negMulLog`.

@residual(wall:approx-identity-L1) -/
theorem negMulLog_convDensity_tendsto_ae
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    ∀ᵐ x ∂volume,
      Tendsto (fun n =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x))
        atTop (𝓝 (Real.negMulLog (pX x))) := by
  sorry

/-- **Layer 2 (genuine lifting machinery).** Density-level entropy-integral
convergence: given the parked layer-1 inputs (approximate-identity L¹ convergence
+ entropy finiteness) and the regularity of `pX`, the differential-entropy
integrals of the heat-smoothed densities converge to the entropy integral of `pX`
as `t → 0⁺`:

`∫ negMulLog (convDensityAdd pX g_t) ∂volume → ∫ negMulLog pX ∂volume`.

This is the genuine Phase-3 machinery: sequentialisation of `𝓝[Ioi 0] 0`
(`Filter.tendsto_iff_seq_tendsto`, `nhdsWithin` countably generated) → Vitali
(`tendsto_Lp_of_tendsto_ae`, `[IsFiniteMeasure]`-free via `UnifTight`) →
L¹→integral (`tendsto_integral_of_L1'`, measure/filter-free). No own `sorry`; the
only residuals are the parked layer-1 / UI / UT lemmas it consumes. -/
theorem differentialEntropy_convDensity_integral_tendsto
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) :
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
    exact (memLp_one_iff_integrable.mpr
      (negMulLog_integrable_of_density hpX_nn hpX_meas hpX_int hpX_mom))
  have hui : UnifIntegrable F 1 volume :=
    negMulLog_convDensity_unifIntegrable hpX_nn hpX_meas hpX_int hpX_mom v hv_pos
  have hut : UnifTight F 1 volume :=
    negMulLog_convDensity_unifTight hpX_nn hpX_meas hpX_int hpX_mom v hv_pos
  have hfg : ∀ᵐ x ∂volume, Tendsto (fun n => F n x) atTop (𝓝 (g x)) := by
    -- `v → 0⁺`: agrees with `u` eventually, and `u → 0⁺`.
    have hv_lim : Tendsto v atTop (𝓝[Set.Ioi 0] 0) :=
      hu_lim.congr' (hv_eq.mono fun n hn => hn.symm)
    exact negMulLog_convDensity_tendsto_ae hpX_nn hpX_meas hpX_int hpX_mom v hv_pos hv_lim
  have hVitali :
      Tendsto (fun n => eLpNorm (F n - g) 1 volume) atTop (𝓝 0) :=
    tendsto_Lp_of_tendsto_ae (le_refl 1) (by simp) haef hg' hui hut hfg
  -- L¹→integral: `∫ F n → ∫ g`.
  have hfi : Integrable g volume := by
    rw [hg_def]
    exact negMulLog_integrable_of_density hpX_nn hpX_meas hpX_int hpX_mom
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

/-- **G2 shared wall lemma (endpoint version)** — heat-flow entropy-power
continuity at the single endpoint `t = 0⁺`.

`t ↦ entropyPower (P.map (fun ω => X ω + √t · Z ω))` is `ContinuousWithinAt
(Set.Ioi 0) 0` (the limit `t → 0⁺`). The live consumer
(`csiszarLogRatioGap_continuousWithinAt_zero`) reduces to three instances of this
single endpoint term; the interior `t > 0` continuity is supplied separately and
genuinely from `csiszarLogRatioGap_differentiableOn_interior` (`.continuousOn`),
so the wall is confined to the one endpoint atom.

The endpoint `t = 0⁺` is the analytic content. Its proof would go through
`MeasureTheory.continuousWithinAt_of_dominated` on the density integrand
`negMulLog (f_t x)`, whose only missing premise is a `t = 0⁺`-uniform integrable
pointwise majorant. That majorant is not derivable from `IsDeBruijnRegularityHyp`
(see file header GATE verdict, 2026-06-03 NO-GO) and `entropyPower` /
`differentialEntropy` continuity is absent from both Mathlib and InformationTheory
(loogle: 0 declarations). This is a true continuity claim with body `sorry`; no
continuity conclusion is taken as a hypothesis. `IsDeBruijnRegularityHyp` fields
are regularity-only (density witness / per-`t` V2 regularity /
interval-integrability), none a continuity claim.

Surface shrink (2026-06-04): the predecessor `heatFlowEntropyPower_continuousOn`
claimed the full ray `ContinuousOn (Set.Ici 0)`; this version shrinks the residual
to the single endpoint, with the interior recovered genuinely on the consumer side.

Audit 2026-06-04 (fresh subagent): the compound `@residual` dropped
`wall:entropy-finiteness` (misclassified — that register wall is the smoothed
`t > 0` density form, already CLOSED; the limit-density `t = 0` finiteness it
actually relies on is plan-owned 落とし穴2). The remaining direct `sorry` is the
density-identification bridge (a `plan:` signature change), consuming
`differentialEntropy_convDensity_integral_tendsto` whose only un-CLOSED wall is
`wall:approx-identity-L1`. Compound (AND) = those two.

Layer-2 genuine machinery (2026-06-04): the density-level entropy-integral
convergence `differentialEntropy_convDensity_integral_tendsto` is now **genuine**
(Vitali `tendsto_Lp_of_tendsto_ae` + L¹→integral `tendsto_integral_of_L1'`, both
`[IsFiniteMeasure]`-free), resting only on parked layer-1 lemmas
(`convDensityAdd_tendsto_L1_zero` etc., `wall:approx-identity-L1`) and entropy
finiteness (`negMulLog_integrable_of_density`, `wall:entropy-finiteness`). The
remaining direct `sorry` here is the **density-identification bridge**: turning
`entropyPower (P.map (X+√t·Z))` into the density-level integral requires the
measurability/independence of `X, Z` (`pPath_eq_convDensityAdd` needs
`Measurable X`, `Measurable Z`, `IndepFun X Z P`), which are **not** carried by
`IsDeBruijnRegularityHyp` and **not** supplied by the live consumer
`csiszarLogRatioGap_continuousWithinAt_zero` (it passes only `h_reg`). Adding them
to this signature would break that consumer, so the bridge is parked pending a
signature change in a follow-up plan. Once threaded, the wall lemma closes
genuinely against `differentialEntropy_convDensity_integral_tendsto`.

@residual(wall:approx-identity-L1,plan:epi-g2-layer2-moonshot-plan) -/
theorem heatFlowEntropyPower_continuousWithinAt_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_reg : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z P) :
    ContinuousWithinAt
      (fun t : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      (Set.Ioi (0 : ℝ)) 0 := by
  -- Genuine reduction: `entropyPower = exp ∘ (2 · differentialEntropy)`, so the
  -- endpoint continuity follows from the endpoint continuity of the inner
  -- differential entropy via `Real.continuous_exp`.
  have key :
      ContinuousWithinAt
        (fun t : ℝ => differentialEntropy (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
        (Set.Ioi (0 : ℝ)) 0 := by
    -- The genuine layer-2 machinery
    -- (`differentialEntropy_convDensity_integral_tendsto`) supplies the density-level
    -- integral convergence `∫ negMulLog (convDensityAdd pX g_t) → ∫ negMulLog pX`.
    -- Bridging it to `differentialEntropy (P.map (X+√t·Z))` requires identifying the
    -- pushforward density with `convDensityAdd pX g_t` (`pPath_eq_convDensityAdd`),
    -- which needs `Measurable X`, `Measurable Z`, `IndepFun X Z P` — not carried by
    -- `IsDeBruijnRegularityHyp` and not supplied by the live consumer. Parked.
    -- @residual(wall:approx-identity-L1,plan:epi-g2-layer2-moonshot-plan)
    sorry
  have hcomp :
      ContinuousWithinAt
        (fun t : ℝ => Real.exp (2 *
          differentialEntropy (P.map (fun ω => X ω + Real.sqrt t * Z ω))))
        (Set.Ioi (0 : ℝ)) 0 :=
    ((key.const_smul (2 : ℝ)).rexp)
  -- `entropyPower μ = exp (2 * differentialEntropy μ)` definitionally.
  simpa only [entropyPower, smul_eq_mul] using hcomp

end InformationTheory.Shannon
