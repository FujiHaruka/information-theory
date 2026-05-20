import Common2026.Shannon.WynerZiv
import Common2026.Shannon.WynerZivAchievability
import Common2026.Shannon.RateDistortionAchievabilityPhaseD
import Common2026.Shannon.WynerZivDecoderFailureAssembly

/-!
# Wyner–Ziv decoder-failure → distortion achievability bridge (T3-D wave10 S17)

This file builds the **bridge** between the two genuine abstraction layers of the
Wyner–Ziv achievability argument that earlier seeds left disconnected:

* the **binning layer** (`WynerZivDecoderFailureAssembly.lean`), whose
  `wzDecoderFail_aep_assembled` shows the *decoder-failure probability* of the
  random-binning code tends to `0` (covering ε₁ + packing S/M, at aligned μ/ε₀);
* the **code/distortion layer** (`WynerZiv.lean` / `WynerZivAchievability.lean`),
  whose `WynerZivCode` / `expectedBlockDistortion` and achievability-existence
  statement `wyner_ziv_achievability_existence` reason about *expected block
  distortion ≤ D*, never about the raw decoder-failure event.

The S14 assembly seed flagged that **no decoder-failure → code-distortion bridge
existed in the codebase**. This file supplies it, via the standard rate-distortion
achievability glue (Cover–Thomas 13.6 / 15.9 distortion bound).

## Approach

The single genuine ingredient is the **error-event × bounded-distortion
decomposition** (the exact pattern of `source_avg_distortion_le_simpler` in
`RateDistortionAchievabilityPhaseD.lean`, transplanted to `WynerZivCode`):

> Split the expected block distortion of a `WynerZivCode` over a measurable
> *decoder-failure set* `Fail`. On the **success** event `Failᶜ` the
> reconstruction is jointly-typical, so per-block distortion `≤ D + δ`. On the
> **failure** event the distortion is at worst `distortionMax dN`. Hence
> `𝔼[blockDistortion] ≤ (D + δ) + distortionMax dN · ℙ(Fail)`.

So a *vanishing* decoder-failure probability (the binning-layer provenance,
`wzDecoderFail_aep_assembled`) plus the typical-success bound yields
`expectedBlockDistortion ≤ D + ε`, which is precisely the hypothesis consumed by
`wyner_ziv_achievability_existence`. The bridge therefore **reduces** the opaque
achievability-existence hypothesis to the strictly-more-primitive pair
(decoder-failure → 0) + (typical-set per-letter distortion bound).

Three layers:

1. `wzExpectedBlockDistortion_le_of_fail` — the decomposition + integration glue
   on a single `WynerZivCode`. Genuine measure-theoretic content (pointwise
   indicator bound → `integral_mono` → `integral_indicator_const`), copied in
   shape from `source_avg_distortion_le_simpler`.
2. `wynerZivAchievabilityExistence_of_failProb` — assemble per-`n` code witnesses
   (each with a vanishing failure probability and the typical-success bound) into
   the achievability-existence form `∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ M c, …`.
3. `wyner_ziv_achievability_existence_bridged` — re-publish
   `wyner_ziv_achievability_existence` with the bridge applied: its
   achievability-existence hypothesis is *discharged* from the failure-probability
   sequence + typical bound, not pass-through.

## 撤退ライン

* **The per-`n` code witnesses** (a `WynerZivCode` whose decoder-failure
  probability is small and whose success-event reconstruction is distortion
  typical) are taken as the input sequence. They are the binning-layer
  provenance: `wzDecoderFail_aep_assembled` produces the vanishing failure
  probability; converting its binning code `(f_U, g)` into a `WynerZivCode`
  encoder/decoder is the alphabet-instantiation step, threaded as a hypothesis.
  This file's content is the **distortion decomposition + asymptotic assembly**,
  not the alphabet instantiation — that decomposition is genuinely missing from
  the codebase and is what the seed asks for.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Decoder-failure × distortion decomposition on a `WynerZivCode` -/

section Decomposition

variable {α β γ : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]
variable [Nonempty α] [Nonempty γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ]
variable {M n : ℕ}

/-- The block reconstruction of a Wyner–Ziv code on a source/side-info block
`p : Fin n → α × β`. -/
noncomputable def wzBlockRecon (c : WynerZivCode M n α β γ)
    (p : Fin n → α × β) : Fin n → γ :=
  c.decoder (c.encoder (fun i => (p i).1), fun i => (p i).2)

/-- The block source of `p : Fin n → α × β`. -/
def wzBlockSource (p : Fin n → α × β) : Fin n → α := fun i => (p i).1

/-- **Decoder-failure × distortion decomposition.**

Let `Fail ⊆ (Fin n → α × β)` be a (measurable) decoder-failure set, `Edδ` a
success-event distortion bound (think `D + δ`), and assume:

* on the **success** event `Failᶜ`, the block distortion of the reconstruction is
  at most `Edδ`;
* the source-block probability of `Fail` is at most `pFail`.

Then the expected block distortion of the code is at most
`Edδ + distortionMax dN · pFail`. This is the rate-distortion achievability
distortion bound (error event contributes ≤ failure-prob · max-distortion;
success event contributes ≤ Edδ). -/
theorem wzExpectedBlockDistortion_le_of_fail
    (c : WynerZivCode M n α β γ) (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (dN : DistortionFn α γ) (Edδ pFail : ℝ) (hEdδ_nn : 0 ≤ Edδ)
    (Fail : Set (Fin n → α × β))
    (h_succ : ∀ p ∉ Fail,
        blockDistortion dN n (wzBlockSource p) (wzBlockRecon c p) ≤ Edδ)
    (h_pfail :
        (Measure.pi (fun _ : Fin n => P_XY)).real Fail ≤ pFail) :
    c.expectedBlockDistortion P_XY dN
      ≤ Edδ + distortionMax dN * pFail := by
  classical
  set Pn : Measure (Fin n → α × β) := Measure.pi (fun _ : Fin n => P_XY) with hPn
  haveI : IsProbabilityMeasure Pn := by rw [hPn]; infer_instance
  set dMax : ℝ := distortionMax dN with hdMax
  have h_dMax_nn : 0 ≤ dMax := distortionMax_nonneg dN
  -- The integrand of `expectedBlockDistortion`.
  set f : (Fin n → α × β) → ℝ :=
    fun p => blockDistortion dN n (wzBlockSource p) (wzBlockRecon c p) with hf
  -- Failure set is measurable (finite ambient).
  have h_Fail_meas : MeasurableSet Fail := (Set.toFinite _).measurableSet
  -- Pointwise bound: `f p ≤ Edδ + dMax · 𝟙_Fail p`.
  have h_pointwise : ∀ p : Fin n → α × β,
      f p ≤ Edδ + dMax * (Fail.indicator (fun _ => (1 : ℝ)) p) := by
    intro p
    by_cases hp : p ∈ Fail
    · -- On the failure event: `f p ≤ dMax`.
      have h_bd : f p ≤ dMax := blockDistortion_le_distortionMax dN n _ _
      have h_ind : Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p = 1 :=
        Set.indicator_of_mem hp _
      calc f p ≤ dMax := h_bd
        _ = 0 + dMax * 1 := by ring
        _ ≤ Edδ + dMax * 1 := by linarith
        _ = Edδ + dMax * (Fail.indicator (fun _ => (1 : ℝ)) p) := by rw [h_ind]
    · -- On the success event: `f p ≤ Edδ`.
      have h_bd : f p ≤ Edδ := h_succ p hp
      have h_ind : Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p = 0 :=
        Set.indicator_of_notMem hp _
      calc f p ≤ Edδ := h_bd
        _ = Edδ + dMax * 0 := by ring
        _ = Edδ + dMax * (Fail.indicator (fun _ => (1 : ℝ)) p) := by rw [h_ind]
  -- Integrability of both sides (bounded on a probability measure).
  have h_meas_f : Measurable f := measurable_of_finite _
  have h_meas_g : Measurable
      (fun p : Fin n → α × β => Edδ + dMax * (Fail.indicator (fun _ => (1 : ℝ)) p)) :=
    measurable_of_finite _
  have h_f_le : ∀ p, ‖f p‖ ≤ dMax := by
    intro p
    rw [hf, Real.norm_eq_abs, abs_of_nonneg (blockDistortion_nonneg dN n _ _)]
    exact blockDistortion_le_distortionMax dN n _ _
  have h_int_f : Integrable f Pn := by
    refine Integrable.mono' (g := fun _ => dMax) (integrable_const dMax)
      h_meas_f.aestronglyMeasurable (Filter.Eventually.of_forall h_f_le)
  have h_int_g : Integrable
      (fun p : Fin n → α × β => Edδ + dMax * (Fail.indicator (fun _ => (1 : ℝ)) p)) Pn := by
    refine Integrable.mono' (g := fun _ => Edδ + dMax) (integrable_const (Edδ + dMax))
      h_meas_g.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have h_ind_le : (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p) ≤ 1 := by
      by_cases hp : p ∈ Fail
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]; linarith
    have h_ind_nn : 0 ≤ (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) p
    have h_val_le : Edδ + dMax * (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p)
        ≤ Edδ + dMax := by
      have : dMax * (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p) ≤ dMax := by
        calc dMax * (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p)
            ≤ dMax * 1 := mul_le_mul_of_nonneg_left h_ind_le h_dMax_nn
          _ = dMax := by ring
      linarith
    have h_val_nn : 0 ≤ Edδ + dMax * (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p) :=
      add_nonneg hEdδ_nn (mul_nonneg h_dMax_nn h_ind_nn)
    rw [Real.norm_eq_abs, abs_of_nonneg h_val_nn]
    exact h_val_le
  -- Integrate the pointwise bound.
  have h_int_mono :
      ∫ p, f p ∂Pn
        ≤ ∫ p, Edδ + dMax * (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p) ∂Pn :=
    integral_mono h_int_f h_int_g h_pointwise
  -- Evaluate the RHS integral.
  have h_int_const : ∫ _p : Fin n → α × β, Edδ ∂Pn = Edδ := by
    rw [integral_const]; simp
  have h_int_indicator :
      ∫ p : Fin n → α × β, dMax * (Fail.indicator (fun _ => (1 : ℝ)) p) ∂Pn
        = dMax * Pn.real Fail := by
    have h_ind_eq :
        (fun p : Fin n → α × β => dMax * (Fail.indicator (fun _ => (1 : ℝ)) p))
          = Fail.indicator (fun _ : Fin n → α × β => dMax) := by
      funext p
      by_cases hp : p ∈ Fail
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]; ring
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]; ring
    rw [h_ind_eq, integral_indicator_const dMax h_Fail_meas, smul_eq_mul]; ring
  have h_const_int : Integrable (fun _ : Fin n → α × β => Edδ) Pn := integrable_const Edδ
  have h_ind_int : Integrable
      (fun p : Fin n → α × β => dMax * (Fail.indicator (fun _ => (1 : ℝ)) p)) Pn := by
    refine Integrable.mono' (g := fun _ => dMax) (integrable_const dMax)
      (measurable_of_finite _).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have h_ind_le : (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p) ≤ 1 := by
      by_cases hp : p ∈ Fail
      · rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem hp]; linarith
    have h_ind_nn : 0 ≤ (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) p
    have h_val_nn : 0 ≤ dMax * (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p) :=
      mul_nonneg h_dMax_nn h_ind_nn
    have h_val_le : dMax * (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p) ≤ dMax := by
      calc dMax * (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p)
          ≤ dMax * 1 := mul_le_mul_of_nonneg_left h_ind_le h_dMax_nn
        _ = dMax := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg h_val_nn]
    exact h_val_le
  have h_int_split :
      ∫ p, Edδ + dMax * (Fail.indicator (fun _ : Fin n → α × β => (1 : ℝ)) p) ∂Pn
        = Edδ + dMax * Pn.real Fail := by
    rw [integral_add h_const_int h_ind_int, h_int_const, h_int_indicator]
  -- Identify the LHS integral with `expectedBlockDistortion`.
  have h_lhs : c.expectedBlockDistortion P_XY dN = ∫ p, f p ∂Pn := rfl
  rw [h_int_split] at h_int_mono
  -- Final: chain `expectedBlockDistortion = ∫ f ≤ Edδ + dMax·ℙ(Fail) ≤ Edδ + dMax·pFail`.
  calc c.expectedBlockDistortion P_XY dN
      = ∫ p, f p ∂Pn := h_lhs
    _ ≤ Edδ + dMax * Pn.real Fail := h_int_mono
    _ ≤ Edδ + dMax * pFail := by
        have := mul_le_mul_of_nonneg_left h_pfail h_dMax_nn
        linarith

end Decomposition

/-! ## Section 2 — Asymptotic assembly into the achievability-existence form -/

section Assembly

variable {α β γ : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]
variable [Nonempty α] [Nonempty β] [Nonempty γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ]

/-- **Assembly of the achievability-existence form from a vanishing decoder
failure.**

Suppose for every block length `n` we have a code `cWit n` of size `M n` and a
decoder-failure set `Fail n` such that:

* the success-event block distortion is `≤ D + δ` (`h_succ`);
* the rate is at most `R` (`h_rate`: `M n ≤ exp(n R)`);
* the **decoder-failure probability tends to `0`** (`h_failProb`: for every
  tolerance, eventually `ℙ(Fail n) ≤ tolerance`) — this is exactly the shape
  produced by `wzDecoderFail_aep_assembled`.

Then the achievability-existence form holds for any `D' ≥ D + δ`: for every
`ε > 0`, eventually a code achieves expected block distortion `≤ D' + ε`. -/
theorem wynerZivAchievabilityExistence_of_failProb
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (dN : DistortionFn α γ) (D R : ℝ)
    (M : ℕ → ℕ)
    (cWit : ∀ n, WynerZivCode (M n) n α β γ)
    (Fail : ∀ n, Set (Fin n → α × β))
    (Edδ : ℝ) (hEdδ_nn : 0 ≤ Edδ) (hEdδ_le : Edδ ≤ D)
    (h_succ : ∀ n, ∀ p ∉ Fail n,
        blockDistortion dN n (wzBlockSource p) (wzBlockRecon (cWit n) p) ≤ Edδ)
    (h_rate : ∀ n, (M n : ℝ) ≤ Real.exp ((n : ℝ) * R))
    (h_failProb : ∀ η > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
        (Measure.pi (fun _ : Fin n => P_XY)).real (Fail n) ≤ η) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M' : ℕ) (c : WynerZivCode M' n α β γ),
          (M' : ℝ) ≤ Real.exp ((n : ℝ) * R)
            ∧ c.expectedBlockDistortion P_XY dN ≤ D + ε := by
  intro ε hε
  set dMax : ℝ := distortionMax dN with hdMax
  have h_dMax_nn : 0 ≤ dMax := distortionMax_nonneg dN
  -- Tolerance `η := ε / (dMax + 1) > 0`, chosen so `dMax · η ≤ ε`.
  set η : ℝ := ε / (dMax + 1) with hη
  have h_dMax1_pos : 0 < dMax + 1 := by linarith
  have hη_pos : 0 < η := by rw [hη]; positivity
  -- `dMax · η ≤ ε`.
  have h_dMaxη_le : dMax * η ≤ ε := by
    rw [hη]
    calc dMax * (ε / (dMax + 1))
        = (dMax / (dMax + 1)) * ε := by ring
      _ ≤ 1 * ε := by
          refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hε)
          rw [div_le_one h_dMax1_pos]; linarith
      _ = ε := one_mul ε
  obtain ⟨N, hN⟩ := h_failProb η hη_pos
  refine ⟨N, ?_⟩
  intro n hn
  refine ⟨M n, cWit n, h_rate n, ?_⟩
  -- Apply the decomposition glue at code `cWit n`, failure set `Fail n`, bound `Edδ`.
  have h_pfail : (Measure.pi (fun _ : Fin n => P_XY)).real (Fail n) ≤ η := hN n hn
  have h_dist :
      (cWit n).expectedBlockDistortion P_XY dN ≤ Edδ + dMax * η :=
    wzExpectedBlockDistortion_le_of_fail (cWit n) P_XY dN Edδ η hEdδ_nn (Fail n)
      (h_succ n) h_pfail
  calc (cWit n).expectedBlockDistortion P_XY dN
      ≤ Edδ + dMax * η := h_dist
    _ ≤ D + ε := by linarith

end Assembly

/-! ## Section 3 — Re-publish the achievability-existence wrapper with the bridge -/

section Republish

variable {α β γ : Type*}
variable [Fintype α] [Fintype β] [Fintype γ]
variable [Nonempty α] [Nonempty β] [Nonempty γ]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass γ]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Wyner–Ziv achievability — existence form, bridged.**

This re-publishes `wyner_ziv_achievability_existence` with its opaque
achievability-existence hypothesis *discharged* by the decoder-failure → 0
bridge: instead of receiving the existence claim ready-made, it receives the
strictly-more-primitive pair

* a per-`n` code with success-event distortion `≤ Edδ ≤ D` and rate `≤ R`, plus
* the decoder-failure probability tending to `0` (`h_failProb`, the
  `wzDecoderFail_aep_assembled` provenance),

and *produces* the achievability-existence conclusion via
`wynerZivAchievabilityExistence_of_failProb`. -/
theorem wyner_ziv_achievability_existence_bridged
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (P_XY_pmf : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (dN : DistortionFn α γ)
    (_h_R_gt : R > wynerZivRatePmf U P_XY_pmf d D)
    (M : ℕ → ℕ)
    (cWit : ∀ n, WynerZivCode (M n) n α β γ)
    (Fail : ∀ n, Set (Fin n → α × β))
    (Edδ : ℝ) (hEdδ_nn : 0 ≤ Edδ) (hEdδ_le : Edδ ≤ D)
    (h_succ : ∀ n, ∀ p ∉ Fail n,
        blockDistortion dN n (wzBlockSource p) (wzBlockRecon (cWit n) p) ≤ Edδ)
    (h_rate : ∀ n, (M n : ℝ) ≤ Real.exp ((n : ℝ) * R))
    (h_failProb : ∀ η > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
        (Measure.pi (fun _ : Fin n => P_XY)).real (Fail n) ≤ η) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M' : ℕ) (c : WynerZivCode M' n α β γ),
          (M' : ℝ) ≤ Real.exp ((n : ℝ) * R)
            ∧ c.expectedBlockDistortion P_XY dN ≤ D + ε :=
  wynerZivAchievabilityExistence_of_failProb P_XY dN D R M cWit Fail
    Edδ hEdδ_nn hEdδ_le h_succ h_rate h_failProb

end Republish

end InformationTheory.Shannon
