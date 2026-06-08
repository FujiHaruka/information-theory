import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EntropyPower.Inequality
import InformationTheory.Shannon.EPI.Stam.Discharge
import InformationTheory.Shannon.FisherInfo.V2DeBruijnGenuine
import InformationTheory.Shannon.EPI.L3Integration
import InformationTheory.Shannon.EPI.Stam.ToBridge
import InformationTheory.Shannon.EPI.Case1.RatioLimit
import InformationTheory.Shannon.EPI.G2.HeatFlowContinuity
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Order.Monotone.Basic
import InformationTheory.Shannon.EPI.Case1.TwoTime.Core

/-!
# EPI case-1 two-time object — matched-time path existence (§1)

The inverse-function subproject: construct `s(t) = N_A⁻¹(N_A(0)·eᵗ)`. Five private
sub-lemmas (i)–(v) + `matchedTimePath_exists`. Verbatim split of `TwoTime.lean`
§1; proofs unchanged. Builds on `TwoTimeCore.lean` (§0). Umbrella: `TwoTime.lean`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

namespace InformationTheory.Shannon.EPICase1TwoTime

open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge
open InformationTheory.Shannon.EPIL3Integration (csiszarLogRatioGap)
open InformationTheory.Shannon.EPIStamToBridge (entropyPower_hasDerivAt_of_diffEnt_hasDerivAt)
open InformationTheory.Shannon.EPICase1RatioLimit
  (entropyPower_rescaled_path_tendsto entropyPower_path_scaling IsRescaledPathRegular)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## §1 — Matched-time path existence (inverse-function subproject)

The largest block (Phase 2 ~200-300 lines): construct `s(t) = N_A⁻¹(N_A(0)·eᵗ)`
via strict monotonicity (`J_A > 0`), continuity on `Ici 0`, surjectivity
(`N_A → ∞`), continuous inverse (`StrictMonoOn.orderIso`), and inverse-function
derivative (`HasDerivAt.of_local_left_inverse` + `comp`). The hypotheses are
**only** regularity preconditions; the conclusion (existence of a matched path)
is the genuine output, not bundled.

The five pieces (i)-(v) are isolated as private sub-lemmas below.
-/

/-- **(ii) Continuity of `N_A` on `Ici 0`.** Interior `s > 0` continuity from the
supplied interior derivative `hJ_deriv` (`HasDerivAt → ContinuousAt`); the endpoint
`s = 0` from the heat-flow endpoint continuity
(`heatFlowEntropyPower_continuousWithinAt_zero`, CLOSED 2026-06-05). -/
private theorem matchedTimePath_N_continuousOn
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_endpt : IsHeatFlowEndpointRegular A B P)
    (hN_diff_int : ∀ s : ℝ, 0 < s → DifferentiableAt ℝ (fun u => heatFlowEP A B P u) s) :
    ContinuousOn (fun s => heatFlowEP A B P s) (Set.Ici (0 : ℝ)) := by
  -- Endpoint `s = 0⁺`: heat-flow endpoint continuity (CLOSED 2026-06-05).
  have h0 : ContinuousWithinAt (fun s => heatFlowEP A B P s) (Set.Ici (0 : ℝ)) 0 := by
    have hendpt :
        ContinuousWithinAt
          (fun t : ℝ => entropyPower (P.map (fun ω => A ω + Real.sqrt t * B ω)))
          (Set.Ioi (0 : ℝ)) 0 :=
      heatFlowEntropyPower_continuousWithinAt_zero A B P h_endpt
    -- `heatFlowEP A B P t = entropyPower (P.map (A + √t·B))` definitionally.
    have hendpt' : ContinuousWithinAt (fun s => heatFlowEP A B P s) (Set.Ioi (0 : ℝ)) 0 := by
      simpa only [heatFlowEP] using hendpt
    exact (continuousWithinAt_Ioi_iff_Ici).mp hendpt'
  intro x hx
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with hx0 | hx0
  · -- `x = 0`: use the endpoint continuity.
    subst hx0
    exact h0
  · -- `x > 0`: interior, `DifferentiableAt → ContinuousAt → ContinuousWithinAt`.
    exact ((hN_diff_int x hx0).continuousAt).continuousWithinAt

/-- **(i) Strict monotonicity of `N_A` on `Ici 0`.** From `strictMonoOn_of_deriv_pos`
on the convex `Ici 0`: continuity (ii) + interior derivative
`N_A(s)·J_A(s) > 0` (`entropyPower_pos` × `hJ_pos`). -/
private theorem matchedTimePath_N_strictMonoOn
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (J_A : ℝ → ℝ)
    (hJ_pos : ∀ s : ℝ, 0 < s → 0 < J_A s)
    (hJ_deriv : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun u => heatFlowEP A B P u) (heatFlowEP A B P s * J_A s) s)
    (hN_cont : ContinuousOn (fun s => heatFlowEP A B P s) (Set.Ici (0 : ℝ))) :
    StrictMonoOn (fun s => heatFlowEP A B P s) (Set.Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hN_cont
  intro x hx
  rw [interior_Ici] at hx
  have hx_pos : 0 < x := hx
  -- `deriv N x = N x * J_A x` from the supplied interior `HasDerivAt`.
  have hderiv : deriv (fun u => heatFlowEP A B P u) x = heatFlowEP A B P x * J_A x :=
    (hJ_deriv x hx_pos).deriv
  rw [hderiv]
  exact mul_pos (by simpa [heatFlowEP] using entropyPower_pos _) (hJ_pos x hx_pos)

/-- **(iii)+(iv) Continuous inverse `g = N_A⁻¹`.** From strict monotonicity (i),
continuity (ii), and surjectivity (`N_A → ∞`, IVT `intermediate_value_Ici`):
the inverse `g` maps `Ici C` into `Ici 0`, is a right inverse of `N_A` on `Ici C`,
is continuous, and sends `C` to `0`. -/
private theorem matchedTimePath_inverse
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hN_cont : ContinuousOn (fun s => heatFlowEP A B P s) (Set.Ici (0 : ℝ)))
    (hN_mono : StrictMonoOn (fun s => heatFlowEP A B P s) (Set.Ici (0 : ℝ)))
    (hC_pos : 0 < heatFlowEP A B P 0)
    (hN_tendsto : Filter.Tendsto (fun s => heatFlowEP A B P s) Filter.atTop Filter.atTop) :
    ∃ g : ℝ → ℝ,
      (∀ y, heatFlowEP A B P 0 ≤ y → 0 ≤ g y)
      ∧ (∀ y, heatFlowEP A B P 0 ≤ y → heatFlowEP A B P (g y) = y)
      ∧ ContinuousOn g (Set.Ici (heatFlowEP A B P 0))
      ∧ g (heatFlowEP A B P 0) = 0 := by
  classical
  set N : ℝ → ℝ := fun s => heatFlowEP A B P s with hN
  set C : ℝ := N 0 with hC
  -- **Surjectivity onto `Ici C`** via IVT.
  have h_surjOn : Set.SurjOn N (Set.Ici (0 : ℝ)) (Set.Ici C) := by
    have hsub : Set.Ici (N (0 : ℝ)) ⊆ N '' Set.Ici (0 : ℝ) :=
      isPreconnected_Ici.intermediate_value_Ici
        (Set.self_mem_Ici)
        (Filter.le_principal_iff.mpr (Filter.Ici_mem_atTop 0))
        hN_cont hN_tendsto
    intro y hy
    exact hsub (by simpa [hC] using hy)
  -- The inverse function and its core properties.
  set g : ℝ → ℝ := Function.invFunOn N (Set.Ici (0 : ℝ)) with hg
  have h_maps : Set.MapsTo g (Set.Ici C) (Set.Ici (0 : ℝ)) := h_surjOn.mapsTo_invFunOn
  have h_rinv : Set.RightInvOn g N (Set.Ici C) := h_surjOn.rightInvOn_invFunOn
  have h_injOn : Set.InjOn N (Set.Ici (0 : ℝ)) := hN_mono.injOn
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · -- `0 ≤ g y` from `g y ∈ Ici 0`.
    intro y hy
    exact h_maps (by simpa [hC] using hy)
  · -- `N (g y) = y`.
    intro y hy
    exact h_rinv (by simpa [hC] using hy)
  · -- **Continuity of `g` on `Ici C`** (the inverse-continuity piece).
    -- `g` is strictly monotone on `Ici C` (inverse of the strict-mono `N`).
    have h_leftInv : Set.LeftInvOn g N (Set.Ici (0 : ℝ)) := h_injOn.leftInvOn_invFunOn
    -- `N` maps `Ici 0` into `Ici C` (monotone, `N 0 = C`).
    have hN_maps : Set.MapsTo N (Set.Ici (0 : ℝ)) (Set.Ici C) := by
      intro s hs
      simp only [Set.mem_Ici] at hs ⊢
      have : N 0 ≤ N s := hN_mono.monotoneOn (Set.self_mem_Ici) hs hs
      simpa [hC] using this
    have hg_mono : StrictMonoOn g (Set.Ici C) := by
      intro y₁ hy₁ y₂ hy₂ hlt
      have hg₁ : g y₁ ∈ Set.Ici (0 : ℝ) := h_maps hy₁
      have hg₂ : g y₂ ∈ Set.Ici (0 : ℝ) := h_maps hy₂
      by_contra hge
      push_neg at hge
      have : N (g y₂) ≤ N (g y₁) := hN_mono.monotoneOn hg₂ hg₁ hge
      rw [h_rinv hy₁, h_rinv hy₂] at this
      linarith
    -- `g '' (Ici C) = Ici 0`.
    have hg_image : g '' Set.Ici C = Set.Ici (0 : ℝ) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨y, hy, rfl⟩; exact h_maps hy
      · intro s hs
        exact ⟨N s, hN_maps hs, h_leftInv hs⟩
    -- Continuity at each point of `Ici C`, split into interior and endpoint.
    intro y hy
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hy) with hyC | hyC
    · -- Endpoint `y = C`: right continuity via right-surjectivity.
      -- `hyC : C = y`.
      have hgy : g y = 0 := by
        have hgy_mem : g y ∈ Set.Ici (0 : ℝ) := h_maps hy
        have hN_gy : N (g y) = N 0 := by rw [h_rinv hy, ← hyC]
        exact h_injOn hgy_mem (Set.self_mem_Ici) hN_gy
      -- `hyC : heatFlowEP A B P 0 = y`, i.e. `C = y`.
      -- Keep `s = Ici C` for the mono / surj / nbhd; the conclusion is `Ici y`.
      have hs_nhds : Set.Ici C ∈ 𝓝[≥] y := by
        rw [show C = y from hyC]; exact self_mem_nhdsWithin
      have h_surj_r : Set.SurjOn g (Set.Ici C) (Set.Ioi (g y)) := by
        rw [hgy]
        intro z hz
        have hz0 : (0:ℝ) ≤ z := le_of_lt hz
        exact ⟨N z, hN_maps hz0, h_leftInv hz0⟩
      -- conclusion `ContinuousWithinAt g (Ici y) y`; goal `ContinuousWithinAt g (Ici C) y`.
      have hcont := hg_mono.continuousWithinAt_right_of_surjOn hs_nhds h_surj_r
      rw [hyC]
      exact hcont
    · -- Interior `y > C`: full `ContinuousAt`, then `.continuousWithinAt`.
      have hs_nhds : Set.Ici C ∈ 𝓝 y := Ici_mem_nhds hyC
      have hgy_pos : 0 < g y := by
        have hgy_mem : g y ∈ Set.Ici (0:ℝ) := h_maps hy
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hgy_mem) with h0 | h0
        · exfalso
          have hval : N (g y) = N 0 := by rw [← h0]
          rw [h_rinv hy] at hval
          -- `hval : y = N 0 = C`, contradicting `hyC : C < y`.
          have : y = C := hval
          rw [this] at hyC; exact lt_irrefl _ hyC
        · exact h0
      have h_img_nhds : g '' Set.Ici C ∈ 𝓝 (g y) := by
        rw [hg_image]; exact Ici_mem_nhds hgy_pos
      exact (hg_mono.continuousAt_of_image_mem_nhds hs_nhds h_img_nhds).continuousWithinAt
  · -- `g C = 0`: `N (g C) = C = N 0`, `N` injective on `Ici 0`, both in `Ici 0`.
    have hgC_mem : g C ∈ Set.Ici (0 : ℝ) := h_maps (Set.self_mem_Ici)
    have hN_gC : N (g C) = N 0 := by
      have := h_rinv (Set.self_mem_Ici (a := C)); rw [this]
    exact h_injOn hgC_mem (Set.self_mem_Ici) hN_gC

/-- **Continuity of the matched path** `t ↦ g (C·eᵗ)` on `Ici 0`, from
`ContinuousAt g (C·eᵗ)` (interior, `t > 0`) and the endpoint. -/
private theorem matchedTimePath_path_continuousOn
    (g : ℝ → ℝ) (C : ℝ) (hC_pos : 0 < C)
    (hg_cont : ContinuousOn g (Set.Ici C)) :
    ContinuousOn (fun t => g (C * Real.exp t)) (Set.Ici (0 : ℝ)) := by
  -- `t ↦ C·eᵗ` is continuous and maps `Ici 0` into `Ici C` (since `eᵗ ≥ 1`).
  have hinner : ContinuousOn (fun t : ℝ => C * Real.exp t) (Set.Ici (0 : ℝ)) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  have hmaps : Set.MapsTo (fun t : ℝ => C * Real.exp t) (Set.Ici (0 : ℝ)) (Set.Ici C) := by
    intro t ht
    simp only [Set.mem_Ici] at ht ⊢
    nlinarith [Real.one_le_exp ht, hC_pos]
  exact hg_cont.comp hinner hmaps

/-- **(v) Inverse-function chain rule glue** (proof-log §Two-time formulation gate,
mechanically verified in `ProbeF1.lean`): the matched path `s(t) = g (C·eᵗ)` has
derivative `1/J_A(s(t))` at `t > 0`, via `HasDerivAt.of_local_left_inverse` (giving
`g' (C·eᵗ) = (N·J)⁻¹`) composed with `d/dt (C·eᵗ) = C·eᵗ`, cancelling to `1/J`. -/
private theorem matchedTimePath_path_hasDerivAt
    (N J_A g : ℝ → ℝ) (C t : ℝ) (ht : 0 < t) (hC_pos : 0 < C)
    (hN_mono : StrictMonoOn N (Set.Ici (0 : ℝ)))
    (hg_maps : ∀ y, C ≤ y → 0 ≤ g y)
    (hg_cont : ContinuousOn g (Set.Ici C))
    (hg_rinv : ∀ y, C ≤ y → N (g y) = y)
    (hC_eq : N 0 = C)
    (hJ_pos : ∀ s : ℝ, 0 < s → 0 < J_A s)
    (hJ_deriv : ∀ s : ℝ, 0 < s → HasDerivAt N (N s * J_A s) s) :
    HasDerivAt (fun t => g (C * Real.exp t)) (1 / J_A (g (C * Real.exp t))) t := by
  -- `C·eᵗ > C` since `eᵗ > 1` for `t > 0`.
  have hCe_gt : C < C * Real.exp t := by
    nlinarith [Real.add_one_lt_exp (ne_of_gt ht), hC_pos]
  have hCe_pos : 0 < C * Real.exp t := lt_trans hC_pos hCe_gt
  set sa := g (C * Real.exp t) with hsa
  -- `Ici C` is a neighborhood of `C·eᵗ` (an interior point).
  have hIci_nhds : Set.Ici C ∈ nhds (C * Real.exp t) :=
    Ici_mem_nhds hCe_gt
  -- `ContinuousAt g (C·eᵗ)` from `ContinuousOn g (Ici C)` at the interior point.
  have hg_contAt : ContinuousAt g (C * Real.exp t) :=
    (hg_cont (C * Real.exp t) (le_of_lt hCe_gt)).continuousAt hIci_nhds
  -- `N (g (C·eᵗ)) = C·eᵗ` (matched value), so `sa ∈ Ici 0` and `sa > 0`.
  have hmatch : N sa = C * Real.exp t := hg_rinv (C * Real.exp t) (le_of_lt hCe_gt)
  -- `sa > 0`: otherwise `sa = 0` (since `sa ∈ Ici 0`... but we don't have `sa ∈ Ici 0`
  -- directly; derive `N sa = C·eᵗ > C = N 0` and strict mono ⟹ `sa > 0`).
  -- We need `sa ∈ Ici 0` to use strict mono. The right inverse maps into `Ici 0`,
  -- which we get from `hg_rinv` consistency: `N sa = C·eᵗ`. Use that `N` is strictly
  -- mono on `Ici 0` with `N 0 = C < C·eᵗ = N sa`. But strict mono needs `sa ∈ Ici 0`.
  -- This is supplied by the inverse construction; thread it via positivity of `N sa`.
  -- Instead, obtain `sa > 0` from the maps-to property implicitly: we only need it for
  -- `hJ_deriv` and `hJ_pos`. We get `0 < sa` from `N`-strict-mono once `sa ≥ 0`.
  have hsa_nn : 0 ≤ sa := hg_maps (C * Real.exp t) (le_of_lt hCe_gt)
  have hsa_pos : 0 < sa := by
    rcases eq_or_lt_of_le hsa_nn with h0 | h0
    · -- `sa = 0` ⟹ `N sa = N 0 = C`, contradicting `N sa = C·eᵗ > C`.
      exfalso
      have : N sa = C := by rw [← h0, hC_eq]
      rw [hmatch] at this
      linarith [hCe_gt, this]
    · exact h0
  -- Now assemble via the proof-log glue.
  have hNpos : 0 < N sa := by rw [hmatch]; exact hCe_pos
  have hJpos : 0 < J_A sa := hJ_pos sa hsa_pos
  have hf'_ne : N sa * J_A sa ≠ 0 := ne_of_gt (mul_pos hNpos hJpos)
  -- `N`'s interior derivative at `sa`: `HasDerivAt N (N sa * J_A sa) sa`.
  have hN_deriv : HasDerivAt N (N sa * J_A sa) sa := hJ_deriv sa hsa_pos
  -- eventually-right-inverse near `C·eᵗ`: holds on the neighborhood `Ioi C ⊇`.
  have hrinv : ∀ᶠ y in nhds (C * Real.exp t), N (g y) = y := by
    filter_upwards [Ici_mem_nhds hCe_gt] with y hy
    exact hg_rinv y hy
  -- `g'(C·eᵗ) = (N sa · J_A sa)⁻¹`.
  have hg_deriv : HasDerivAt g (N sa * J_A sa)⁻¹ (C * Real.exp t) := by
    have hN_deriv' : HasDerivAt N (N sa * J_A sa) (g (C * Real.exp t)) := by
      rw [← hsa]; exact hN_deriv
    exact hN_deriv'.of_local_left_inverse hg_contAt hf'_ne hrinv
  have hinner : HasDerivAt (fun u : ℝ => C * Real.exp u) (C * Real.exp t) t := by
    have := (Real.hasDerivAt_exp t).const_mul C; simpa using this
  have hcomp : HasDerivAt (fun u : ℝ => g (C * Real.exp u))
      ((N sa * J_A sa)⁻¹ * (C * Real.exp t)) t := HasDerivAt.comp t hg_deriv hinner
  have hval : (N sa * J_A sa)⁻¹ * (C * Real.exp t) = 1 / J_A sa := by
    rw [← hmatch]; field_simp
  rw [hsa] at hcomp ⊢
  rwa [hval] at hcomp

/-- **TT-path existence** — the matched-time path `s : ℝ → ℝ` exists.

Hypotheses are regularity preconditions only: positivity of the Fisher info
`J_A` along the path (`hJ_pos`, a genuine `0 < fisherInfo` precondition that has
no in-tree theorem, threaded as in `csiszarLogRatioGap_deriv_le_zero`'s
`hJX_pos`), measurability, and independence. The conclusion is `∃ s,
IsMatchedTimePath ...` — the existence of the matched path with its `e^t`
property and FII-matched derivative.

**Proof done (2026-06-06): genuinely closed, sorryAx-free.** The inverse-function
subproject is assembled from five private sub-lemmas (`#print axioms
matchedTimePath_exists = [propext, Classical.choice, Quot.sound]`):

* (i) `matchedTimePath_N_strictMonoOn` — strict monotonicity from `J_A > 0`
(`strictMonoOn_of_deriv_pos`, derivative `N_A(s)·J_A(s) > 0` via
`entropyPower_pos` × `hJ_pos`);
* (ii) `matchedTimePath_N_continuousOn` — continuity on `Ici 0` (interior from the
supplied derivative `DifferentiableAt → ContinuousAt`; endpoint `s = 0⁺` from
`heatFlowEntropyPower_continuousWithinAt_zero`, CLOSED 2026-06-05, via
`continuousWithinAt_Ioi_iff_Ici`);
* (iii)+(iv) `matchedTimePath_inverse` — surjectivity onto `[N_A 0, ∞)`
(`isPreconnected_Ici.intermediate_value_Ici`, IVT) + continuous inverse
`g = Function.invFunOn N_A (Ici 0)` (`StrictMonoOn.continuousAt_of_image_mem_nhds`
/ `...continuousWithinAt_right_of_surjOn`);
* (v) `matchedTimePath_path_hasDerivAt` — inverse-function chain rule glue
(`HasDerivAt.of_local_left_inverse` giving `g'(C·eᵗ) = (N·J)⁻¹`, composed via
`HasDerivAt.comp` with `d/dt (C·eᵗ) = C·eᵗ`, cancelling to `1/J_A`; mirrors the
mechanically-verified `ProbeF1.lean` glue).

**Surjectivity precondition** (`hN_tendsto`): the single-source heat-flow entropy
power `N_A(s) = entropyPower (P.map (A + √s·B))` diverges to `∞` as `s → ∞`. This
is a genuine regularity datum (no in-tree theorem gives it for an arbitrary `A`),
assembled from `entropyPower_path_scaling` (`N_A(s) = s · entropyPower(P.map(A/√s + B))`)
times `entropyPower_rescaled_path_tendsto` (the rescaled path entropy power tends to
the positive `entropyPower (P.map B)`). It is **not** load-bearing on the EPI
conclusion: it is the order-completeness datum used to invert `N_A` (surjectivity onto
`[N_A 0, ∞)`).

**Endpoint precondition** (`h_endpt : IsHeatFlowEndpointRegular A B P`): a regularity
bundle (measurability / independence / Real density witness of `P.map A` / input
entropy finiteness) consumed by the heat-flow endpoint continuity lemma; all fields
are preconditions, none bundles the EPI conclusion.

Independent honesty audit 2026-06-06 (fresh subagent): PASS — `@audit:ok` affirmed.
(1) `#print axioms matchedTimePath_exists = [propext, Classical.choice, Quot.sound]`
(sorryAx-free, machine-checked; the file is now fully proof-done, 0 in-file
`sorry`). (2) `hN_tendsto` is a GENUINE regularity /
order-completeness precondition, NOT load-bearing: it is the divergence of the
single-source entropy power `N_A(s) → ∞` (assembled from `entropyPower_path_scaling`
× `entropyPower_rescaled_path_tendsto`, both in-tree, the latter `@audit:ok` and
landing on the positive finite limit `entropyPower (P.map B)`); it carries neither the
EPI inequality nor any matched-path construction core, serving only to invert `N_A`
(surjectivity onto `[N_A 0, ∞)`). (3) `h_endpt : IsHeatFlowEndpointRegular` is the
same all-precondition bundle already `@audit:ok` at the consuming
`heatFlowEntropyPower_continuousWithinAt_zero`; no conclusion bundled. (4) All five
private sub-lemmas (i)-(v) are genuine: no circular `:= h`, no `:True` slot, no
degenerate exploitation; (v)'s inverse-function glue discharges sign/cancellation
honestly (`hf'_ne` from `mul_pos`, `hval` cancels `(N·J)⁻¹·(C·eᵗ)` to `1/J` via the
matched value `N sa = C·eᵗ`). (5) The four `IsMatchedTimePath` fields are constructed
from the real inverse `g`, not trivially satisfied at a degenerate `s` — the existence
is non-vacuous.

Re-audit 2026-06-06 (commit `4074dea`, conclusion strengthened with `∀ t, 0<t→0<s t`
and `Tendsto s atTop atTop`): PASS — `@audit:ok` re-affirmed. Both new conjuncts are
GENUINELY proven (no sorry, non-vacuous): positivity from `g (C·eᵗ) > 0` via strict-mono
inverse (`hg_rinv'` + `hN_mono`, exfalso on the `g=0` branch using `N(g y)=C` vs
`C<C·eᵗ`); divergence from inner `C·eᵗ→∞` (`const_mul_atTop`) composed with `g→∞`
(strict-mono `N` + right-inverse, explicit `tendsto_atTop_atTop` witness). `#print axioms
matchedTimePath_exists = [propext, Classical.choice, Quot.sound]` (sorryAx-free,
machine-verified this audit, with the strengthened signature).
@audit:ok -/
theorem matchedTimePath_exists
    (A B : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (J_A : ℝ → ℝ)
    (hA : Measurable A) (hB : Measurable B) (hAB : IndepFun A B P)
    (hJ_pos : ∀ s : ℝ, 0 < s → 0 < J_A s)
    (hJ_deriv : ∀ s : ℝ, 0 < s →
      HasDerivAt (fun u => heatFlowEP A B P u) (heatFlowEP A B P s * J_A s) s)
    (h_endpt : IsHeatFlowEndpointRegular A B P)
    (hN_tendsto : Filter.Tendsto (fun s => heatFlowEP A B P s) Filter.atTop Filter.atTop) :
    ∃ s : ℝ → ℝ, IsMatchedTimePath A B P J_A s
      ∧ (∀ t : ℝ, 0 < t → 0 < s t)
      ∧ Filter.Tendsto s Filter.atTop Filter.atTop := by
  classical
  set N : ℝ → ℝ := fun s => heatFlowEP A B P s with hN
  set C : ℝ := N 0 with hC
  -- `C = N 0 > 0`.
  have hC_pos : 0 < C := by
    simp only [hC, hN, heatFlowEP]; exact entropyPower_pos _
  -- (ii) `N` is continuous on `Ici 0`.
  have hN_cont : ContinuousOn N (Set.Ici (0 : ℝ)) :=
    matchedTimePath_N_continuousOn A B P h_endpt
      (fun s hs => (hJ_deriv s hs).differentiableAt)
  -- (i) `N` is strictly monotone on `Ici 0`.
  have hN_mono : StrictMonoOn N (Set.Ici (0 : ℝ)) :=
    matchedTimePath_N_strictMonoOn A B P J_A hJ_pos hJ_deriv hN_cont
  -- (iv) the continuous inverse `g` with `N ∘ g = id` near `C·eᵗ` (t>0) and `g 0' = 0`.
  obtain ⟨g, hg_maps, hg_rinv, hg_cont, hg_zero⟩ :=
    matchedTimePath_inverse A B P hN_cont hN_mono hC_pos hN_tendsto
  -- Repackage the inverse properties in the `C`-indexed form (`C = N 0`).
  have hg_maps' : ∀ y, C ≤ y → 0 ≤ g y := by
    intro y hy; exact hg_maps y (by simpa [hC, hN] using hy)
  have hg_rinv' : ∀ y, C ≤ y → N (g y) = y := by
    intro y hy; exact hg_rinv y (by simpa [hC, hN] using hy)
  -- Define the matched path `s(t) := g (C · eᵗ)`.
  refine ⟨fun t => g (C * Real.exp t), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- start_zero: `s 0 = g (C·e⁰) = g C = 0`.
    simp only [Real.exp_zero, mul_one]
    exact hg_zero
  · -- matched_growth: `N (s t) = C · eᵗ` for `t ≥ 0`.
    intro t ht
    have hCe : C ≤ C * Real.exp t := by
      nlinarith [Real.one_le_exp ht, hC_pos]
    have : N (g (C * Real.exp t)) = C * Real.exp t :=
      hg_rinv (C * Real.exp t) hCe
    simpa only [hN, heatFlowEP, hC] using this
  · -- cont: continuity of `t ↦ g (C·eᵗ)` on `Ici 0`.
    exact matchedTimePath_path_continuousOn g C hC_pos hg_cont
  · -- deriv_at: inverse-function chain rule glue (proof-log §formulation gate).
    intro t ht
    exact matchedTimePath_path_hasDerivAt N J_A g C t ht hC_pos
      hN_mono hg_maps hg_cont hg_rinv rfl hJ_pos hJ_deriv
  · -- positivity: `s t = g (C·eᵗ) > 0` for `t > 0` (strict-mono inverse, `g C = 0`).
    intro t ht
    have hCe_gt : C < C * Real.exp t := by
      nlinarith [Real.add_one_lt_exp (ne_of_gt ht), hC_pos]
    have hsa_nn : 0 ≤ g (C * Real.exp t) := hg_maps' _ (le_of_lt hCe_gt)
    rcases eq_or_lt_of_le hsa_nn with h0 | h0
    · exfalso
      have : N (g (C * Real.exp t)) = C := by rw [← h0, hC]
      rw [hg_rinv' _ (le_of_lt hCe_gt)] at this
      linarith
    · exact h0
  · -- divergence: `s t = g (C·eᵗ) → ∞` (inner `C·eᵗ → ∞`, `g → ∞` via strict-mono `N`).
    have hinner : Filter.Tendsto (fun t : ℝ => C * Real.exp t) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hC_pos Real.tendsto_exp_atTop
    have hg_atTop : Filter.Tendsto g Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro M
      refine ⟨max C (N (max M 0 + 1)), ?_⟩
      intro y hy
      have hyC : C ≤ y := le_trans (le_max_left _ _) hy
      have hM1_nn : (0 : ℝ) ≤ max M 0 + 1 := by positivity
      have hgy_nn : 0 ≤ g y := hg_maps' y hyC
      have hN_gy : N (g y) = y := hg_rinv' y hyC
      have hge : N (max M 0 + 1) ≤ N (g y) := by
        rw [hN_gy]; exact le_trans (le_max_right _ _) hy
      have hbig : max M 0 + 1 ≤ g y := by
        by_contra hlt
        push_neg at hlt
        have := hN_mono (Set.mem_Ici.mpr hgy_nn) (Set.mem_Ici.mpr hM1_nn) hlt
        linarith
      calc M ≤ max M 0 := le_max_left _ _
        _ ≤ max M 0 + 1 := by linarith
        _ ≤ g y := hbig
    exact hg_atTop.comp hinner

end InformationTheory.Shannon.EPICase1TwoTime
