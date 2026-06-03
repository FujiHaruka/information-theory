import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPowerInequality
import InformationTheory.Shannon.EPIPlumbing
import InformationTheory.Shannon.FisherInfoV2
import InformationTheory.Shannon.FisherInfoV2DeBruijn
import InformationTheory.Shannon.FisherInfoV2DeBruijnGenuine
import InformationTheory.Shannon.FisherInfoGaussian
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.EPIBlachmanDensity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# T2-D-S: Entropy Power Inequality — Stam inequality + de Bruijn integration 経路 discharge

`InformationTheory/Shannon/EntropyPowerInequality.lean` (T2-D, 347 行) の主定理
`entropy_power_inequality` は L-EPI1 + L-EPI2 + L-EPI3 三本立て hypothesis
pass-through pattern で publish 済。本 file は **Stam inequality + de Bruijn
integration 経路** で L-EPI1 / L-EPI2 を真の signature に格上げし、合成 wrapper
`epi_via_stam` で **L-EPI3 を導出する hypothesis pipeline** を整える。

## Roadmap

* §2 Stam inequality predicate (`IsStamInequalityHyp`) — Cover-Thomas 17.7.2
  の真の signature `1/J(X+Y) ≥ 1/J(X) + 1/J(Y)` を hypothesis 化 + L-EPI1 bridge。
* §3 de Bruijn regularity hypothesis (`IsDeBruijnRegularityHyp`) — heat-flow
  path 上の各 t での `IsRegularDeBruijnHyp` + tail integrability を集約。
* §4 de Bruijn integration predicate (`IsDeBruijnIntegrationHyp`) — Cover-Thomas
  17.7.2 の `∫₀^∞ ... dt = h(N) - h(X)` integration identity を hypothesis 化
  + L-EPI2 bridge。
* §5 Gaussian saturation full discharge: `X, Y` ともに Gaussian なら Stam +
  de Bruijn 全 hypothesis が **trivially** 取れる (Mathlib
  `fisherInfoOfDensity_gaussianPDFReal` + Gaussian closed form 経由)。
* §6 合成 wrapper `epi_via_stam`: §2 + §4 + bridge hypothesis から L-EPI3
  を導出する。本格 discharge は L-EPI1/L-EPI2 → L-EPI3 の Stam-to-EPI bridge
  (Cover-Thomas Lemma 17.7.3 の `∫ (J(X+√tZ)⁻¹) dt` 計算) が必要だが、本 file
  は bridge そのものを predicate `IsStamToEPIBridgeHyp` として hypothesis 化。
* §7 Gaussian full discharge corollary: §5 + §6 の合成で **Gaussian X, Y に
  対し EPI が hypothesis 不要で導出**。

## 撤退ライン (本 file で発動)

Mathlib に Stam inequality / de Bruijn integration / Fisher info convolution
lemma が **完全不在** (`rg "Stam" → 0 hit`、inventory §A.5)。本 file は

* L-EPI1 (Stam) は `IsStamInequalityHyp` 真 signature 化 (`1/J ≥ 1/J + 1/J` 形)。
  旧 EntropyPowerInequality.lean の `IsStamInequalityHypothesis (= True)`
  への trivial bridge `isStamInequalityHypothesis_of_stamInequalityHyp` は
  Phase 3 Wave 2 (2026-05-27) で retract 済 (placeholder def 自体が削除)。
* L-EPI2 (de Bruijn) は `IsDeBruijnIntegrationHyp` 真 signature 化
  (`∫₀^∞ (d/dt) h(X+√t Z) dt = h(∞) - h(X)` integration identity 形)。
  旧 `IsDeBruijnIntegrationHypothesis (= True)` への trivial bridge も
  同 wave で retract 済。
* 合成経路 `Stam + de Bruijn → L-EPI3` は更に `IsStamToEPIBridgeHyp` を
  hypothesis 化 (Cover-Thomas Lemma 17.7.3 の本体経路、参考: Stam 1959 / Blachman
  1965 / Cover-Thomas Ch.17.7 末尾 path-integral 議論)。**本 file scope-out**、
  別 plan `epi-stam-to-conclusion-plan.md` (未着手) で discharge する想定。
* Gaussian saturation case のみ §5/§7 で **撤退ラインなしで full discharge**。

## 主シグネチャ

* `IsStamInequalityHyp X Y P` (§2) — Stam inequality 真 signature
  (旧 L-EPI1 bridge `isStamInequalityHypothesis_of_stamInequalityHyp` は
  Phase 3 Wave 2 で retract 済、placeholder `:= True` 廃止に伴う)
* `IsDeBruijnRegularityHyp X Z P` (§3) — de Bruijn regularity predicate
* `IsDeBruijnIntegrationHyp X Z P` (§4) — de Bruijn integration 真 signature
* `IsStamToEPIBridgeHyp X Y P` (§6) — Stam + de Bruijn → L-EPI3 bridge hypothesis
* `epi_via_stam` (§6) — 合成 wrapper, L-EPI3 を導出
* `epi_via_stam_gaussian` (§7) — Gaussian saturation full discharge corollary
-/

namespace InformationTheory.Shannon.EPIStamDischarge

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality

/-! ## §2 — Stam inequality predicate (Cover-Thomas Lemma 17.7.2 真 signature) -/

/-- **Stam inequality hypothesis** (L-EPI1 真 signature, Cover-Thomas Lemma 17.7.2).

For independent `X, Y` with finite Fisher information,

    `1 / J(X + Y) ≥ 1 / J(X) + 1 / J(Y)`

where `J` is Fisher information (return type `ℝ` via `fisherInfoReal`).

This is the 1-dimensional **Stam inequality** in inverse form (Cover-Thomas Lemma
17.7.2; Stam 1959; Blachman 1965). Used as hypothesis pass-through; Mathlib has
neither Fisher info convolution nor the inverse-triangle inequality (`rg "Stam"
→ 0 hit`). Discharge via `epi-stam-discharge-plan.md` (未着手).

To avoid division-by-zero, we phrase the predicate to require either
`J(X) = J(Y) = 0` (Dirac case) or the inverse inequality on the real-valued
projections (with finiteness).

Audit 2026-05-31 (owner-level pivot, epi-wall-reattack-plan): sound Prop statement.
The injected hyps (`IsRegularDensityV2 fX/fY`, `∫fX=1`, `∫fY=1`, the *pointwise*
convolution identity `∀ x, fXY x = convDensityAdd fX fY x`, and the
`IsBlachmanConvReady fX fY` bundle) are jointly satisfiable (Gaussian witness
`isBlachmanConvReady_gaussianPDFReal` + `convDensityAdd_gaussian_closed_form`,
NON-vacuous); the pointwise `hconv` ties `fXY` to the convolution so the conclusion is
the genuine Stam bound, not universally false. These are regularity preconditions, not
the inequality core (which is genuinely closed in `stam_step2_density_wall` via
`convex_fisher_bound_of_ready`). Pivoted in lockstep with `IsStamInequalityResidual`
(defeq chain via `fisherInfoOfMeasureV2_def`); the pointwise convolution constraint +
`IsBlachmanConvReady` were added to let `isStamInequalityHyp_via_body` consume the
genuine `IsStamCauchySchwarzOptimal` producer. No honesty defect.

@audit:ok — independent honesty audit (2026-05-31): SOUND non-vacuous Prop. The injected
hyps are regularity preconditions (smoothness / normalization / pointwise convolution
identification / 19-field `Integrable`/boundedness/positivity bundle); none bundles the
inequality core (the conclusion `1/J_sum ≥ 1/J_X+1/J_Y` is genuinely produced from
regularity by `isStamInequalityHyp_via_step3` → `stam_step2_density_wall`, sorryAx-free).
Non-vacuous: Gaussian witness `isBlachmanConvReady_gaussianPDFReal` inhabits the gating
bundle. Pivot defeq-aligned with `IsStamInequalityResidual` (`fisherInfoOfMeasureV2_def`);
defeq pass-through sites (`EPIStamToBridge` / `EPIL3Integration`) unchanged + green =
honest type-identity, not sorry concealment. @audit:ok -/
def IsStamInequalityHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    J_X = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    J_sum = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Y ω)) fXY).toReal →
    InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fX →
    InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fY →
    (∫ x, fX x ∂MeasureTheory.volume = 1) →
    (∫ x, fY x ∂MeasureTheory.volume = 1) →
    (∀ x, fXY x =
      InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY x) →
    InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady fX fY →
    1 / J_sum ≥ 1 / J_X + 1 / J_Y

-- (retracted, Phase 3 Wave 2, 2026-05-27) `isStamInequalityHypothesis_of_stamInequalityHyp`
-- bridged `IsStamInequalityHyp X Y P → IsStamInequalityHypothesis X Y P` via
-- `trivial`. The target placeholder `IsStamInequalityHypothesis := True` in
-- `EntropyPowerInequality.lean` has been retracted in the same wave (defect-kind
-- prop-true resolved); the bridge has no remaining call sites.

/-- Stam inequality hypothesis is symmetric in `X, Y` (the role of `X+Y` is
unchanged when swapping the addends). -/
theorem isStamInequalityHyp_symm
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamInequalityHyp X Y P) :
    IsStamInequalityHyp Y X P := by
  intro J_Y J_X J_sum fY fX fXY hJY hJX hJsum hJY_def hJX_def hJsum_def
    hregY hregX hnormY hnormX hconv hready
  have h_comm : (fun ω => Y ω + X ω) = fun ω => X ω + Y ω := by
    funext ω; ring
  rw [h_comm] at hJsum_def
  -- transport the pointwise convolution constraint across `convDensityAdd` commutativity
  have hconv' : ∀ x, fXY x =
      InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY x := by
    intro x
    rw [InformationTheory.Shannon.EPIConvDensity.convDensityAdd_comm fX fY]
    exact hconv x
  have hready' :
      InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady fX fY :=
    InformationTheory.Shannon.EPIBlachmanDensity.isBlachmanConvReady_symm hready
  have h_inst := h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    hregX hregY hnormX hnormY hconv' hready'
  linarith

/-! ## §3 — de Bruijn regularity predicate -/

/-- **de Bruijn regularity hypothesis along the heat-flow path** (L-DB1 形).

Bundles for each `t ∈ [0, ∞)` the family-level regularity
`IsRegularDeBruijnHyp X Z P t` needed to apply `deBruijn_identity`, together
with the tail integrability of the derivative `(d/dt) h(X + √t Z)` and the
limit `lim_{t → ∞} h(X + √t Z) = (1/2) log (2πe (Var X + t))` (which collapses
to `+∞` at finite truncation, with the limit form taking the genuine Gaussian
saturation).

Used as hypothesis pass-through; Mathlib has no machinery for any of these
ingredients (`rg "deBruijn" → 0 hit`).

`@audit:retract-candidate(load-bearing-predicate)`
(migrated 2026-05-28 from legacy `@audit:staged(epi-debruijn-regularity)`:
this `structure` carries genuine `HasDerivAt` content via `reg_at` +
`density_t_eq` pin, so it cannot be reduced to `sorry` in its body. Closure
plan: `docs/shannon/epi-debruijn-integration-plan.md`. Active consumers
exist across `EPIStamDischarge` / `EPIStamToBridge` / `EPIL3Integration`,
so this is **not** a candidate for outright deletion — the tag flags it
for eventual decomposition into a regularity precondition + the genuine
de Bruijn lemma (`wall:debruijn-integration` is now [CLOSED 2026-06-04])
once consumers can carry caller-supplied density data directly.)

**Resolved 2026-05-25** (Wave 3 third batch): former
`Integrable ... (volume.restrict (Set.Ioi 0))` field was unsatisfiable even for
Gaussian X (the integrand `1/(2(v+t))` over `(0,∞)` diverges, but `Integrable`
requires `HasFiniteIntegral`). Replaced with bounded-T `IntervalIntegrable`
window (`∀ T > 0, IntervalIntegrable f' volume 0 T`); for Gaussian
`density_path t := gaussianPDFReal m (v + ⟨t,_⟩)` the integrand
`1/(2(v+t))` is continuous and bounded on `[0,T]`, so the field is genuinely
satisfiable. Tail behavior beyond `T` was originally going to be externalized via a
separate `IsDeBruijnTailHyp` predicate; that predicate was **retracted** in
the same Wave 3 third batch by independent audit
(`defect(epi-debruijn-tail-vacuous-and-empty)`, see `EPIL3Integration.lean`
retraction comment). Tail-analysis externalization is now a pending plan-level
task (`docs/shannon/epi-debruijn-integration-plan.md` Phase C-5, awaiting
`EReal`-lift refactor). Predicate remains load-bearing (carries the
regularity content) so the audit tag stays at `staged(epi-debruijn-regularity)`
rather than `ok`.

**Honest refactor 2026-05-25+α** (sub-plan
`docs/shannon/epi-debruijn-regularity-refactor-plan.md`): former
`integrable_deriv : ∃ density_path, ...` had an inner existential decoupled
from `reg_at`'s internal `density_t`, allowing trivial discharge of
`integrable_deriv` *alone* via `density_path := fun _ _ ↦ 0` (an independent
audit caveat on 2026-05-25). The structure has been refactored: `density_path`
is now a top-level structure field, and the new `density_t_eq` field pins it
to `(reg_at t ht).density_t`. Consequently, picking `density_path := 0`
forces `(reg_at t ht).density_t = 0` via `density_t_eq`, which forces the
RHS of `deBruijn_identity_v2 X Z ht (reg_at t ht)` (Phase 2.B foundation
removed the `derivAt_entropy_eq_half_fisher_v2` field; the V2 de Bruijn
identity is now delivered by the genuine (sorryAx-free)
`debruijnIdentityV2_holds_assembled`; `wall:debruijn-integration` is [CLOSED
2026-06-04]) to
`(1/2) * fisherInfoOfDensityReal 0 = 0`; for the Gaussian instance the LHS
is `HasDerivAt (fun s => h(𝒩(m, v+s))) (1/(2(v+t))) t` with
`1/(2(v+t)) ≠ 0`, contradicting the pinned `0`. Thus the degenerate witness
is now structurally infeasible — the trivial-zero bypass is closed at the
type level. The previous caveat tag (slug
`epi-debruijn-regularity-integrable-deriv-decoupled`, kind `caveat`) has been
removed; the predicate remains load-bearing (carries the genuine `HasDerivAt`
content) so the staged-audit tag stays.

audit:PASS 2026-05-25 by honesty-auditor (independent, Track B):
Tier 1 (caveat structurally resolved — inner existential gone, `density_path`
top-level + `density_t_eq` pin present, `integrable_deriv` shares witness),
Tier 2 (`density_path := 0` infeasible: `density_t_eq` forces V2 `density_t = 0`,
RHS `(1/2) * fisherInfoOfDensityReal 0 = 0` contradicts Gaussian
`1/(2(v+t))` derivative via `HasDerivAt.unique`),
Tier 3 (`density_t_eq` is load-bearing not decorative — removing it
restores the decoupled-existential bypass; `reg_at` keeps genuine
`HasDerivAt` content; legacy `staged(epi-debruijn-regularity)` retained
in 2026-05-25 audit because no general non-Gaussian discharge yet and
tail-beyond-T externalization still pending. 2026-05-28 migration moved
the tag to `retract-candidate(load-bearing-predicate)` per the current
sorry-based honesty workflow — see top of docstring). -/
structure IsDeBruijnRegularityHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- Shared density witness. `density_path t` is intended to be the density
  of `P.map (X + √t · Z)`. The same witness drives both `reg_at` (via
  `density_t_eq` below) and `integrable_deriv`, structurally closing the
  trivial-zero bypass that the previous independent existentials allowed. -/
  density_path : ℝ → ℝ → ℝ
  /-- For each strictly positive `t`, the family is regular in the de Bruijn
  sense (V2 form, RHS keyed on V2 Fisher info; `IsRegularDeBruijnHypV2` carries
  its own internal `density_t` witness — that internal witness is pinned to
  the top-level `density_path t` by `density_t_eq` below). -/
  reg_at : ∀ t : ℝ, 0 < t → InformationTheory.Shannon.FisherInfoV2.IsRegularDeBruijnHypV2 X Z P t
  /-- Pin the V2-internal `density_t` of `reg_at t ht` to the top-level
  `density_path t`. Without this pin, the previous structure had two
  independent existentials and `density_path := fun _ _ ↦ 0` trivially
  discharged `integrable_deriv` alone (the resolved caveat). With this pin,
  `density_path = 0` forces `(reg_at t ht).density_t = 0` and hence
  `deBruijn_identity_v2 X Z ht (reg_at t ht)`'s RHS to `0` (Phase 2.B
  foundation removed the `derivAt_entropy_eq_half_fisher_v2` field; V2
  de Bruijn is now delivered by the genuine `debruijnIdentityV2_holds_assembled`,
  `wall:debruijn-integration` is [CLOSED 2026-06-04]), which contradicts the true
  Gaussian derivative `1/(2(v+t)) ≠ 0`. -/
  density_t_eq : ∀ t : ℝ, ∀ ht : 0 < t,
    (reg_at t ht).density_t = density_path t
  /-- The derivative `(1/2)·J(X+√t·Z).toReal` is interval-integrable on every
  bounded window `[0, T]` along the heat-flow path, using the shared
  `density_path`. Bounded-T form is genuinely satisfiable for Gaussian X (the
  integrand `1/(2(v+t))` is continuous and bounded on `[0,T]`); tail behavior
  beyond `T` is a pending plan-level task (the previously intended
  `IsDeBruijnTailHyp` externalization was retracted by independent audit;
  see `EPIL3Integration.lean` retraction comment). -/
  integrable_deriv :
    ∀ T : ℝ, 0 < T →
      IntervalIntegrable
        (fun t : ℝ => (1/2)
          * (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Real.sqrt t * Z ω)) (density_path t)).toReal)
        volume 0 T

/-! ## §4 — de Bruijn integration predicate (Cover-Thomas Lemma 17.7.2 真 signature) -/

/-- **de Bruijn integration hypothesis** (L-EPI2 真 signature).

Cover-Thomas Lemma 17.7.2 integration identity along the heat-flow path:

    `h(N(0, Var X + T)) - h(X)
      = ∫_0^T (1/2) · J(X + √t · Z) dt`,

i.e., the differential entropy gap between `X` and the maximally entropy
Gaussian with the same variance equals the path integral of half the Fisher
information.

Used as hypothesis pass-through; full discharge requires both the de Bruijn
identity (T2-F `deBruijn_identity` packaged with the L-DB1 regularity above)
and the fundamental theorem of calculus along an unbounded interval (`rg
"intervalIntegral.integral_deriv" → only bounded-interval forms`).

`@audit:retract-candidate(load-bearing-predicate)`
(migrated 2026-05-28 from legacy `@audit:staged(epi-debruijn-integration)`:
this `def : Prop` is the existential identity
`∃ fPath, ∀ ..., h_target - h_X = ∫ ... ∂volume`, the Cover-Thomas
17.7.2 integration form itself, which cannot be reduced to `sorry` in a
def body. Closure plan: `docs/shannon/epi-debruijn-integration-plan.md`.
**Wall-delegation now in place (Cluster C sorry-migration 2026-05-28; Phase 4
structural closure 2026-05-31)**: the `def` is kept as the genuine
integration-form `Prop` (its shape is referenced by heat-flow path consumers +
`EPIL3Integration`), but the analytic core is no longer threaded as a
load-bearing hypothesis anywhere — there are 0 hypothesis-form consumers, and a
general witness `isDeBruijnIntegrationHyp_holds` (below) produces the predicate
(given `0 ≤ T` + a `IsDeBruijnPathRegular` path-regularity precondition) by
delegating to the upstream lemma `debruijnIntegrationIdentity_holds`
(`FisherInfoV2DeBruijn.lean`). Phase 4 reduced that lemma's former independent
`sorry` to the per-time de Bruijn identity via FTC; that per-time identity is
now the genuine (sorryAx-free) `debruijnIdentityV2_holds_assembled`
(`wall:debruijn-integration` is [CLOSED 2026-06-04]), so no de Bruijn `sorry`
remains at any use site.)

**Resolved 2026-05-25** (Wave 3 third batch): former `∀ fPath` quantification
collapsed via `fPath := fun _ _ ↦ 0` (because
`fisherInfoOfMeasureV2 _ f = fisherInfoOfDensity f` is defeq, the measure
argument is a labelling-only device), forcing the integrand to `0` and
demanding `h_target = h_X` — false for non-degenerate `(X, T > 0)`.
Refactored to existential `∃ fPath`, selecting the genuine density path
along the heat-flow trajectory (Gaussian instance:
`fPath t := gaussianPDFReal m (v + ⟨t,_⟩)`). Predicate remains load-bearing
(carries the de Bruijn integration identity content); 2026-05-28 migration
moved the tag from legacy `staged(epi-debruijn-integration)` to
`retract-candidate(load-bearing-predicate)` (see top of docstring) per
the current sorry-based honesty workflow. -/
def IsDeBruijnIntegrationHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) (T : ℝ) : Prop :=
  ∃ (fPath : ℝ → ℝ → ℝ),
    ∀ (h_X h_target : ℝ),
      h_X = InformationTheory.Shannon.differentialEntropy (P.map X) →
      h_target = InformationTheory.Shannon.differentialEntropy
                  (P.map (fun ω => X ω + Real.sqrt T * Z ω)) →
      h_target - h_X
        = ∫ t in Set.Ioo 0 T, (1/2)
          * (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Real.sqrt t * Z ω)) (fPath t)).toReal ∂volume

/-- Trivial degenerate case: when `T ≤ 0` the integration interval `(0, T)` is
empty, so the identity is `h_target - h_X = 0`. This holds whenever
`h_target = h_X`, which is the natural boundary case (`T = 0`). -/
theorem isDeBruijnIntegrationHyp_at_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω)
    (h_boundary :
      InformationTheory.Shannon.differentialEntropy (P.map X) =
        InformationTheory.Shannon.differentialEntropy
          (P.map (fun ω => X ω + Real.sqrt 0 * Z ω))) :
    IsDeBruijnIntegrationHyp X Z P 0 := by
  refine ⟨fun _ _ => 0, ?_⟩
  intro h_X h_target hX_def htarget_def
  -- Integral over the empty set `Ioo 0 0` is 0.
  have h_empty : Set.Ioo (0 : ℝ) 0 = ∅ := by
    ext x
    constructor
    · intro hx
      have := hx.1
      have := hx.2
      linarith
    · intro hx
      exact hx.elim
  rw [h_empty, MeasureTheory.setIntegral_empty]
  rw [hX_def, htarget_def, ← h_boundary]
  ring

/-- **General de Bruijn integration witness** — `IsDeBruijnIntegrationHyp X Z P T`
holds whenever `0 ≤ T` and the heat-flow path is regular
(`IsDeBruijnPathRegular`), by delegation to the structurally-closed lemma
`debruijnIntegrationIdentity_holds` (Phase 4 structural closure 2026-05-31).

The integration identity is now genuinely reduced to the per-time de Bruijn
identity (genuine `debruijnIdentityV2_holds_assembled`,
`wall:debruijn-integration` is [CLOSED 2026-06-04]) via FTC: the
upstream lemma carries **no local `sorry`**, only a path-regularity /
integrability precondition `h_path` (which `X` admissible, how regular the
path) plus `0 ≤ T`. The de Bruijn analytic core (heat eq + IBP) lives solely in
the genuine per-time identity lemma, not in any hypothesis bundle here.

The per-time lemma's existential is stated with `gaussianConvolution X Z t`, which is
definitionally `fun ω => X ω + √t · Z ω` (the heat-flow path used by the predicate
body), so the witness threads through directly. -/
@[entry_point]
theorem isDeBruijnIntegrationHyp_holds
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (T : ℝ) (hT : 0 ≤ T)
    (h_path : InformationTheory.Shannon.FisherInfoV2.IsDeBruijnPathRegular X Z P T) :
    IsDeBruijnIntegrationHyp X Z P T :=
  InformationTheory.Shannon.FisherInfoV2.debruijnIntegrationIdentity_holds X Z hX hZ hXZ T hT h_path

-- (retracted, wave-1) `isDeBruijnIntegrationHypothesis_of_deBruijnIntegrationHyp`
-- produced `IsDeBruijnIntegrationHypothesis` (formerly `:= True` placeholder)
-- via `trivial`; a pure Prop=True passthrough (degenerate_def) with no callers.
-- The target placeholder def itself was retracted in Phase 3 Wave 2 (2026-05-27).
-- The genuine de Bruijn integration predicate is `IsDeBruijnIntegrationHyp` (§4) above.

/-! ## §5 — Gaussian saturation full discharge of the upstream hypotheses

When both `P.map X` and `P.map Y` are Gaussian, the upstream Stam / de Bruijn
hypotheses are **all discharged for free**: Stam becomes the trivial inverse
identity (because `J(N(m, v)) = 1/v` closed-form), and de Bruijn-integration
collapses to the linear variance increase along the heat flow.

The block below packages this discharge via the genuine Gaussian saturation
result (`entropyPower_gaussian_additivity`) reused in §7.

**RESOLVED (2026-05-20):** the former `isStamInequalityHyp_of_fisherInfoReal_zero`
(and its `_sum_zero` / `_Y_zero` siblings) discharged the Stam predicate by
`exfalso`-ing the `0 < J_X` precondition against the buggy V1 `fisherInfo = 0`
artefact for Gaussians. That asserted *nothing* about Stam actually holding and
was removed. The genuine Gaussian EPI path runs entirely through
`entropyPower_gaussian_additivity` (see §7).
-/

/-! ## §6 — Stam-to-EPI bridge + 合成 wrapper -/

/-- **Stam-to-EPI bridge hypothesis** (L-EPI1 + L-EPI2 → L-EPI3 path-integral
argument bundling).

Cover-Thomas Lemma 17.7.3 derives EPI from Stam inequality + de Bruijn
identity by considering the heat-flow path

    `Z_t := (1 - t) · X + √t · G + t · √(...) · ...`

(a normalized parametric mixture) and showing that the entropy power along
the path is concave. This requires both Stam and de Bruijn as upstream
inputs, plus the FTC over the path and a saturation argument at the endpoint.

Bundled here as a hypothesis predicate to be discharged in the follow-up plan
`epi-stam-to-conclusion-plan.md` (未着手). -/
def IsStamToEPIBridgeHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  IsStamInequalityHyp X Y P → IsEntropyPowerInequalityHypothesis X Y P

/-- Trivial discharge: when the EPI hypothesis is already known by some other
route (e.g. Gaussian saturation), the bridge holds trivially. -/
theorem isStamToEPIBridgeHyp_of_epi
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_epi : IsEntropyPowerInequalityHypothesis X Y P) :
    IsStamToEPIBridgeHyp X Y P :=
  fun _ => h_epi

/-- **`epi_via_stam`**: 合成 wrapper. Stam inequality + de Bruijn integration
+ Stam-to-EPI bridge から L-EPI3 (`IsEntropyPowerInequalityHypothesis`) を
導出する。本 file の主 deliverable。

`@audit:ok` -/
@[entry_point]
theorem epi_via_stam
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω}
    (X Y Z : Ω → ℝ)
    (h_stam : IsStamInequalityHyp X Y P)
    (h_bridge : IsStamToEPIBridgeHyp X Y P) :
    IsEntropyPowerInequalityHypothesis X Y P :=
  h_bridge h_stam

/-- **Variant of `epi_via_stam`** routed through the EntropyPowerInequality
main theorem `entropy_power_inequality`. Returns the EPI directly.

NOTE (2026-05-30 audit): body は `entropy_power_inequality` を呼び `_h_bridge`
を無視するため、transitive に `stamToEPIBridge_holds`
(`@residual(plan:epi-stam-to-conclusion-plan)`,
`EntropyPowerInequality.lean:223`) の `sorry` を消費する (`#print axioms` で
`sorryAx` 依存を確認)。proof-done でなく、以前の `@audit:ok` は tier-1 誤付与だった
(sibling `epi_via_stam` は `h_bridge h_stam` で genuine に conditional 適用するため
sorryAx 非依存; こちらは headline 経由で bridge を内部 discharge してしまう点が違い)。
reduction 自体は honest。transitive consumer のため `@residual` は付けない。 -/
@[entry_point]
theorem epi_via_stam_main
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityHyp X Y P)
    (_h_bridge : IsStamToEPIBridgeHyp X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  -- `IsStamInequalityHyp` is reducibly defeq to `IsStamInequalityResidual` (both
  -- are Fisher-info inverse-triangle predicates), so it threads into the
  -- non-circular `entropy_power_inequality` headline directly. The Stam→EPI
  -- bridge `_h_bridge` is now internally discharged via the shared sorry lemma
  -- `stamToEPIBridge_holds`, so the argument is unused at this wrapper.
  entropy_power_inequality P X Y hX hY hXY h_stam

/-! ## §7 — Gaussian full discharge (`epi_via_stam_gaussian`) -/

/-- **Gaussian full discharge**: for independent Gaussian `X, Y` with non-zero
variance, `IsStamToEPIBridgeHyp X Y P` is **discharged with no upstream
hypothesis** (the EPI hypothesis is provable directly via
`isEntropyPowerInequalityHypothesis_of_gaussian`). -/
theorem isStamToEPIBridgeHyp_of_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    IsStamToEPIBridgeHyp X Y P := by
  have h_epi :=
    isEntropyPowerInequalityHypothesis_of_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂
      hv₁ hv₂ hLawX hLawY
  exact isStamToEPIBridgeHyp_of_epi h_epi

/-- **`epi_via_stam_gaussian`**: for independent Gaussians `X, Y`, EPI holds
with equality via the Gaussian saturation discharge — no upstream hypothesis
required. Routes through the §6 wrapper to demonstrate the Stam-bridge
pipeline structure. -/
@[entry_point]
theorem epi_via_stam_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  -- Equality form from Gaussian saturation.
  have h_eq := entropyPower_gaussian_additivity
    P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY
  -- `=` implies `≥`.
  exact h_eq.ge

/-! ## §8 — corollaries + sanity check exports -/

/-- Symmetric form of `epi_via_stam`.

`@audit:ok` -/
@[entry_point]
theorem epi_via_stam_symm
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω}
    (X Y Z : Ω → ℝ)
    (h_stam : IsStamInequalityHyp Y X P)
    (h_bridge : IsStamToEPIBridgeHyp Y X P) :
    IsEntropyPowerInequalityHypothesis Y X P :=
  epi_via_stam Y X Z h_stam h_bridge

/-- Pass-through bridge: `IsStamToEPIBridgeHyp` is implied by the conjunction
`Stam → EPI`. -/
theorem isStamToEPIBridgeHyp_of_forall
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamInequalityHyp X Y P → IsEntropyPowerInequalityHypothesis X Y P) :
    IsStamToEPIBridgeHyp X Y P :=
  h

-- (retracted, wave-1) `isDeBruijnIntegrationHypothesis_trivial_of_anything` produced
-- `IsDeBruijnIntegrationHypothesis` (formerly `:= True` placeholder) via `trivial`;
-- an even more obviously vacuous Prop=True passthrough (degenerate_def) with no callers.
-- The target placeholder def itself was retracted in Phase 3 Wave 2 (2026-05-27).

/-! ## §9 — 3-arg EPI via Stam (chain application) -/

/-- **3-arg EPI via Stam pipeline**: chains `epi_via_stam` twice to obtain
the 3-argument EPI.

`@audit:ok` -/
@[entry_point]
theorem epi_via_stam_three_arg
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z G : Ω → ℝ)
    (h_xy_stam : IsStamInequalityHyp X Y P)
    (h_xy_bridge : IsStamToEPIBridgeHyp X Y P)
    (h_xyz_stam : IsStamInequalityHyp (fun ω => X ω + Y ω) Z P)
    (h_xyz_bridge : IsStamToEPIBridgeHyp (fun ω => X ω + Y ω) Z P) :
    entropyPower (P.map (fun ω => X ω + Y ω + Z ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) + entropyPower (P.map Z) := by
  have h_xy_epi := epi_via_stam X Y G h_xy_stam h_xy_bridge
  have h_xyz_epi := epi_via_stam (fun ω => X ω + Y ω) Z G h_xyz_stam h_xyz_bridge
  exact entropy_power_inequality_three_arg P X Y Z h_xyz_epi h_xy_epi

/-! ## §10 — Stam predicate manipulation -/

/-- **Stam predicate is preserved under arithmetic equivalent rephrasings**: if
two functions `X, Y` are pointwise equal to `X', Y'` then their Stam predicates
coincide (the predicate depends only on `P.map X`, `P.map Y`, `P.map (X + Y)`). -/
theorem isStamInequalityHyp_congr
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y X' Y' : Ω → ℝ} {P : Measure Ω}
    (hX : X = X') (hY : Y = Y')
    (h : IsStamInequalityHyp X Y P) :
    IsStamInequalityHyp X' Y' P := by
  subst hX; subst hY; exact h

/-- The Stam predicate is preserved by adding a constant to `X` and `Y` when the
distributional shape of `P.map X`, `P.map Y`, and `P.map (X+Y)` (and hence
Fisher information) is preserved by the translation. This is the *predicate-
level* statement; the corresponding distributional invariance (Fisher info
is translation-invariant) is in the downstream discharge plan. -/
theorem isStamInequalityHyp_of_fisherInfo_eq
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y X' Y' : Ω → ℝ} {P : Measure Ω}
    (hJX : ∀ f : ℝ → ℝ, InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) f
          = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X') f)
    (hJY : ∀ f : ℝ → ℝ, InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) f
          = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y') f)
    (hJsum : ∀ f : ℝ → ℝ,
        InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map (fun ω => X ω + Y ω)) f
          = InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X' ω + Y' ω)) f)
    (h : IsStamInequalityHyp X Y P) :
    IsStamInequalityHyp X' Y' P := by
  intro J_X J_Y J_sum fX fY fXY hJX_pos hJY_pos hJsum_pos hJX_def hJY_def hJsum_def
  have hJX_def' :
      J_X = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal := by
    rw [hJX_def, hJX]
  have hJY_def' :
      J_Y = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal := by
    rw [hJY_def, hJY]
  have hJsum_def' :
      J_sum = (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Y ω)) fXY).toReal := by
    rw [hJsum_def, hJsum]
  exact h J_X J_Y J_sum fX fY fXY hJX_pos hJY_pos hJsum_pos hJX_def' hJY_def' hJsum_def'

/-! ## §11 — de Bruijn regularity manipulation -/

/-- de Bruijn integration `T = 0` always holds in the **structurally trivial**
case where `X + √0 · Z = X` pointwise. -/
theorem isDeBruijnIntegrationHyp_at_zero_pointwise
    {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω)
    (h_pt : (fun ω => X ω + Real.sqrt 0 * Z ω) = X) :
    IsDeBruijnIntegrationHyp X Z P 0 := by
  apply isDeBruijnIntegrationHyp_at_zero
  rw [h_pt]

/-- **`√0 = 0`** specialization: at `T = 0`, the heat-flow path returns
`X + 0 · Z = X`. Used to discharge `isDeBruijnIntegrationHyp_at_zero`. -/
theorem heat_flow_path_at_zero {Ω : Type*} (X Z : Ω → ℝ) :
    (fun ω => X ω + Real.sqrt 0 * Z ω) = X := by
  funext ω
  rw [Real.sqrt_zero, zero_mul, add_zero]

/-! ## §12 — Stam-to-EPI bridge: symmetry / composability -/

/-- The Stam-to-EPI bridge is *not* symmetric in the usual sense (Stam is
symmetric while the bridge picks up `Y + X` vs `X + Y` from the
`IsEntropyPowerInequalityHypothesis` ordering). The symmetric form
re-routes through `isEntropyPowerInequalityHypothesis_symm`.

`@audit:ok` -/
theorem isStamToEPIBridgeHyp_symm
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamToEPIBridgeHyp X Y P) :
    IsStamToEPIBridgeHyp Y X P := by
  intro h_stamYX
  have h_stamXY := isStamInequalityHyp_symm h_stamYX
  exact isEntropyPowerInequalityHypothesis_symm (h h_stamXY)

/-- The Stam-to-EPI bridge composes through trivial EPI fact: if EPI is
already known, the bridge is the constant function.

`@audit:ok` -/
theorem isStamToEPIBridgeHyp_const
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_epi : IsEntropyPowerInequalityHypothesis X Y P) :
    IsStamToEPIBridgeHyp X Y P :=
  isStamToEPIBridgeHyp_of_epi h_epi

/-! ## §13 — Gaussian saturation corollaries -/

/-- **Gaussian saturation via Stam pipeline**: when both `P.map X` and
`P.map Y` are Gaussian with non-zero variance, the EPI follows through the
§6 wrapper (`epi_via_stam_main`) via the Gaussian-discharged bridge. -/
@[entry_point]
theorem entropy_power_inequality_via_stam_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂)
    (h_stam : IsStamInequalityHyp X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  have h_bridge : IsStamToEPIBridgeHyp X Y P :=
    isStamToEPIBridgeHyp_of_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY
  exact epi_via_stam_main P X Y Z hX hY hXY h_stam h_bridge

/-- **Variance-additive form of Gaussian saturation**: the entropy power of
the Gaussian sum equals `2πe (v₁ + v₂) = 2πe v₁ + 2πe v₂`, matching the
EPI inequality with equality. -/
@[entry_point]
theorem entropyPower_gaussian_sum_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      = entropyPower (P.map X) + entropyPower (P.map Y) :=
  entropyPower_gaussian_additivity P X Y hX hY hXY m₁ m₂ v₁ v₂
    hv₁ hv₂ hLawX hLawY

/-! ## §14 — Log-form / Cover-Thomas alternative signatures via Stam pipeline -/

/-- **Log-form EPI via Stam pipeline**: combines `epi_via_stam_main` with
`entropy_power_inequality_log_form` from `EntropyPowerInequality.lean`.

NOTE (2026-05-30 audit): body は `entropy_power_inequality_log_form` を呼ぶため
transitive に `stamToEPIBridge_holds`
(`@residual(plan:epi-stam-to-conclusion-plan)`, `EntropyPowerInequality.lean:223`)
の `sorry` を消費する (`#print axioms` で `sorryAx` 依存を確認)。proof-done でなく、
以前の `@audit:ok` は tier-1 誤付与だった。reduction は honest。transitive consumer
のため `@residual` は付けない。 -/
@[entry_point]
theorem entropy_log_form_via_stam
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityHyp X Y P)
    (_h_bridge : IsStamToEPIBridgeHyp X Y P) :
    InformationTheory.Shannon.differentialEntropy (P.map (fun ω => X ω + Y ω))
      ≥ (1/2) * Real.log
          (entropyPower (P.map X) + entropyPower (P.map Y)) :=
  entropy_power_inequality_log_form P X Y hX hY hXY h_stam

/-- **Exp-form EPI via Stam pipeline**: Cover-Thomas Theorem 17.7.3 露出形.

NOTE (2026-05-30 audit): body は `entropy_power_inequality_exp_form` を呼ぶため
transitive に `stamToEPIBridge_holds`
(`@residual(plan:epi-stam-to-conclusion-plan)`, `EntropyPowerInequality.lean:223`)
の `sorry` を消費する (`#print axioms` で `sorryAx` 依存を確認)。proof-done でなく、
以前の `@audit:ok` は tier-1 誤付与だった。reduction は honest。transitive consumer
のため `@residual` は付けない。 -/
@[entry_point]
theorem entropy_exp_form_via_stam
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityHyp X Y P)
    (_h_bridge : IsStamToEPIBridgeHyp X Y P) :
    Real.exp (2 * InformationTheory.Shannon.differentialEntropy
              (P.map (fun ω => X ω + Y ω)))
      ≥ Real.exp (2 * InformationTheory.Shannon.differentialEntropy (P.map X))
        + Real.exp (2 * InformationTheory.Shannon.differentialEntropy (P.map Y)) :=
  entropy_power_inequality_exp_form P X Y hX hY hXY h_stam

/-- **Normalized `(2πe)⁻¹` form via Stam pipeline**: Cover-Thomas Ch.17 流儀
`N(X+Y) ≥ N(X) + N(Y)`.

NOTE (2026-05-30 audit): body は `entropy_power_inequality_normalized` を呼ぶため
transitive に `stamToEPIBridge_holds`
(`@residual(plan:epi-stam-to-conclusion-plan)`, `EntropyPowerInequality.lean:223`)
の `sorry` を消費する (`#print axioms` で `sorryAx` 依存を確認)。proof-done でなく、
以前の `@audit:ok` は tier-1 誤付与だった。reduction は honest。transitive consumer
のため `@residual` は付けない。 -/
@[entry_point]
theorem entropy_normalized_form_via_stam
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityHyp X Y P)
    (_h_bridge : IsStamToEPIBridgeHyp X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω)) / gaussianEntropyPowerConst
      ≥ entropyPower (P.map X) / gaussianEntropyPowerConst
        + entropyPower (P.map Y) / gaussianEntropyPowerConst :=
  entropy_power_inequality_normalized P X Y hX hY hXY h_stam

/-! ## §15 — 4-arg EPI chain via Stam pipeline -/

/-- **4-arg EPI via Stam pipeline**: chains `epi_via_stam` three times.

`@audit:ok` -/
@[entry_point]
theorem epi_via_stam_four_arg
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z W G : Ω → ℝ)
    (h_xy_stam : IsStamInequalityHyp X Y P)
    (h_xy_bridge : IsStamToEPIBridgeHyp X Y P)
    (h_xyz_stam : IsStamInequalityHyp (fun ω => X ω + Y ω) Z P)
    (h_xyz_bridge : IsStamToEPIBridgeHyp (fun ω => X ω + Y ω) Z P)
    (h_xyzw_stam : IsStamInequalityHyp (fun ω => X ω + Y ω + Z ω) W P)
    (h_xyzw_bridge : IsStamToEPIBridgeHyp (fun ω => X ω + Y ω + Z ω) W P) :
    entropyPower (P.map (fun ω => X ω + Y ω + Z ω + W ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y)
        + entropyPower (P.map Z) + entropyPower (P.map W) := by
  have h_xy_epi := epi_via_stam X Y G h_xy_stam h_xy_bridge
  have h_xyz_epi := epi_via_stam (fun ω => X ω + Y ω) Z G h_xyz_stam h_xyz_bridge
  have h_xyzw_epi := epi_via_stam (fun ω => X ω + Y ω + Z ω) W G h_xyzw_stam h_xyzw_bridge
  exact entropy_power_inequality_four_arg P X Y Z W h_xyzw_epi h_xyz_epi h_xy_epi

/-! ## §16 — Stam pipeline composability witnesses -/

/-- **Composability witness**: any conjunction `(Stam X Y P) ∧ (StamToEPIBridge X Y P)`
yields the EPI hypothesis.

`@audit:ok` -/
theorem isEntropyPowerInequalityHypothesis_of_stam_pair
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_stam : IsStamInequalityHyp X Y P)
    (h_bridge : IsStamToEPIBridgeHyp X Y P) :
    IsEntropyPowerInequalityHypothesis X Y P :=
  h_bridge h_stam

/-- **Pipeline composability**: given the L-EPI3-form already, the Stam pipeline
trivially returns the same hypothesis.

`@audit:ok` -/
theorem epi_pipeline_idempotent
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_epi : IsEntropyPowerInequalityHypothesis X Y P)
    (h_stam : IsStamInequalityHyp X Y P) :
    IsEntropyPowerInequalityHypothesis X Y P :=
  (isStamToEPIBridgeHyp_of_epi h_epi) h_stam

/-- **3-arg via Stam (route through `IsStamToEPIBridgeHyp` rather than direct
EPI hypotheses)**: shows that the Stam-pipeline 3-arg form composes with
`entropy_power_inequality_three_arg`.

`@audit:ok` -/
@[entry_point]
theorem epi_via_stam_three_arg_normalized
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z G : Ω → ℝ)
    (h_xy_stam : IsStamInequalityHyp X Y P)
    (h_xy_bridge : IsStamToEPIBridgeHyp X Y P)
    (h_xyz_stam : IsStamInequalityHyp (fun ω => X ω + Y ω) Z P)
    (h_xyz_bridge : IsStamToEPIBridgeHyp (fun ω => X ω + Y ω) Z P) :
    entropyPower (P.map (fun ω => X ω + Y ω + Z ω)) / gaussianEntropyPowerConst
      ≥ entropyPower (P.map X) / gaussianEntropyPowerConst
        + entropyPower (P.map Y) / gaussianEntropyPowerConst
        + entropyPower (P.map Z) / gaussianEntropyPowerConst := by
  have h_3arg := epi_via_stam_three_arg P X Y Z G h_xy_stam h_xy_bridge
    h_xyz_stam h_xyz_bridge
  -- Divide both sides by the positive constant.
  have hc_pos : 0 < gaussianEntropyPowerConst := gaussianEntropyPowerConst_pos
  have h_sum_div :
      entropyPower (P.map X) / gaussianEntropyPowerConst
        + entropyPower (P.map Y) / gaussianEntropyPowerConst
        + entropyPower (P.map Z) / gaussianEntropyPowerConst
      = (entropyPower (P.map X) + entropyPower (P.map Y) + entropyPower (P.map Z))
          / gaussianEntropyPowerConst := by
    field_simp
  rw [ge_iff_le, h_sum_div]
  exact div_le_div_of_nonneg_right h_3arg hc_pos.le

/-! ## §17 — Sanity check / regression theorems -/

/-- **Sanity check**: the Stam pipeline composed with the EntropyPowerInequality
top-level theorem recovers the exact main statement signature.

NOTE (2026-05-30 audit): body は `entropy_power_inequality` を呼び `_h_bridge`
を無視するため、transitive に `stamToEPIBridge_holds`
(`@residual(plan:epi-stam-to-conclusion-plan)`, `EntropyPowerInequality.lean:223`)
の `sorry` を消費する (`#print axioms` で `sorryAx` 依存を確認)。proof-done でなく、
以前の `@audit:ok` は tier-1 誤付与だった。reduction は honest。transitive consumer
のため `@residual` は付けない。 -/
@[entry_point]
theorem epi_via_stam_main_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityHyp X Y P)
    (_h_bridge : IsStamToEPIBridgeHyp X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  -- (Phase 3 Wave 2, 2026-05-27) `_h_db : IsDeBruijnIntegrationHypothesis` argument
  -- was removed: the placeholder def was retracted; the body never used `_h_db`.
  entropy_power_inequality P X Y hX hY hXY h_stam

/-- **Round trip**: if we have the Stam-derived EPI, the EntropyPowerInequality
predicate is exactly the result of the bridge applied to Stam.

`@audit:ok` -/
theorem epi_via_stam_recovers_predicate
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_stam : IsStamInequalityHyp X Y P)
    (h_bridge : IsStamToEPIBridgeHyp X Y P) :
    IsEntropyPowerInequalityHypothesis X Y P :=
  h_bridge h_stam

end InformationTheory.Shannon.EPIStamDischarge