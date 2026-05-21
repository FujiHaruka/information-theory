import Common2026.Shannon.ChernoffSanovDischarge
import Common2026.Shannon.ChernoffPerTiltSanov
import Common2026.Shannon.ChernoffPerTiltDischarge
import Common2026.Shannon.ChernoffConverse
import Common2026.Shannon.Chernoff
import Common2026.Shannon.CramerLC2Discharge
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.LocalExtr

/-!
# Chernoff converse — genuine discharge of `IsChernoffBandMassToOne`

This file **genuinely discharges** the honest load-bearing hypothesis
`ChernoffSanovDischarge.IsChernoffBandMassToOne` (band mass → 1) under
regularity hypotheses only (`P₁, P₂` full-support pmfs, `P₁ ≠ P₂`), turning the
Chernoff converse `limsup rate ≤ chernoffInfo` into an **unconditional**
(regularity-only) theorem `chernoff_converse_holds`.

## Strategy (two stages + boundary handling)

* **(a) First-order optimality.** `λ ↦ chernoffZSum P₁ P₂ λ` is differentiable;
  at an interior minimiser `λ*` Fermat gives `Z'(λ*) = 0`, equivalently the
  `Q`-mean of `log(P₁) − log(P₂)` vanishes, where `Q = chernoffMediator`.
  (`hasDerivAt_chernoffZSum`, `chernoffMediator_mean_logRatio_eq_zero`.)
* **(b) `Q`-LLN.** Under the vanishing-mean condition the empirical log-ratio
  concentrates at `0` (`strong_law_ae_real` on the infinite product
  `infinitePi Q`, then `tendstoInMeasure_of_tendsto_ae`), so the typical band has
  `Q^n`-mass → 1. (`isChernoffBandMassToOne_of_interior_optimal`.)
* **Boundary exclusion.** `Z(0) = Z(1) = 1`, `Z'(0) = -KL(P₁‖P₂) < 0` and
  `Z'(1) = KL(P₂‖P₁) > 0` (strict Gibbs, `Real.log_lt_sub_one_of_pos`), so under
  `P₁ ≠ P₂` the minimiser is interior. (`exists_interior_minimiser`.)

No new load-bearing hypothesis is introduced; the only assumptions are
regularity. The reindex plumbing (`infinitePi` `ℕ`-coordinates ↔ `Fin n` band)
is handled by `infinitePi_map_take` / `chernoffMediatorMeasure_pi_real_band`.
-/

namespace InformationTheory.Shannon.ChernoffBandMassDischarge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Real MeasureTheory ProbabilityTheory Filter Finset
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.ChernoffConverse
open InformationTheory.Shannon.ChernoffPerTiltDischarge
open InformationTheory.Shannon.ChernoffSanovDischarge
open scoped Topology ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-! ## (a) First-order optimality -/

/-- **Derivative of `λ ↦ Z(λ)`.** Each term `(P₁ a)^{1-λ}·(P₂ a)^λ` differentiates
to `(P₁ a)^{1-λ}·(P₂ a)^λ·(log (P₂ a) − log (P₁ a))`, and the finite sum gives the
stated derivative. -/
lemma hasDerivAt_chernoffZSum
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (lam : ℝ) :
    HasDerivAt (fun l => chernoffZSum P₁ P₂ l)
      (∑ a, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam *
        (Real.log (P₂ a) - Real.log (P₁ a))) lam := by
  unfold chernoffZSum
  apply HasDerivAt.fun_sum
  intro a _
  -- term a: `(P₁ a)^(1-l) · (P₂ a)^l`
  have h₁ : HasDerivAt (fun l : ℝ => (P₁ a) ^ (1 - l))
      (Real.log (P₁ a) * (-1) * (P₁ a) ^ (1 - lam)) lam := by
    have hf : HasDerivAt (fun l : ℝ => 1 - l) (-1) lam := by
      simpa using (hasDerivAt_const lam (1 : ℝ)).sub (hasDerivAt_id lam)
    exact hf.const_rpow (hP₁_pos a)
  have h₂ : HasDerivAt (fun l : ℝ => (P₂ a) ^ l)
      ((P₂ a) ^ lam * Real.log (P₂ a)) lam :=
    (hasStrictDerivAt_const_rpow (hP₂_pos a) lam).hasDerivAt
  have hmul := h₁.mul h₂
  convert hmul using 1
  ring

/-- **First-order optimality at an interior minimiser.** If `λ* ∈ (0,1)` is a
minimiser of `Z` on `[0,1]`, then the `Q`-mean of `log(P₁) − log(P₂)` is `0`,
where `Q = chernoffMediator P₁ P₂ λ*`. -/
lemma chernoffMediator_mean_logRatio_eq_zero
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (hlam_int : lam ∈ Set.Ioo (0:ℝ) 1)
    (hlam_min : IsMinOn (fun l => chernoffZSum P₁ P₂ l) (Set.Icc 0 1) lam) :
    (∑ a, ChernoffConverse.chernoffMediator P₁ P₂ lam a
        * (Real.log (P₁ a) - Real.log (P₂ a))) = 0 := by
  have hZ_pos : 0 < chernoffZSum P₁ P₂ lam :=
    chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam
  -- Fermat: `Z'(lam) = 0` at the interior minimiser.
  have hZ' := hasDerivAt_chernoffZSum P₁ P₂ hP₁_pos hP₂_pos lam
  have h_nhds : Set.Icc (0:ℝ) 1 ∈ 𝓝 lam := by
    have : lam ∈ interior (Set.Icc (0:ℝ) 1) := by
      rw [interior_Icc]; exact hlam_int
    exact mem_interior_iff_mem_nhds.mp this
  have h_localmin : IsLocalMin (fun l => chernoffZSum P₁ P₂ l) lam :=
    hlam_min.isLocalMin h_nhds
  have h_fermat : (∑ a, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam *
      (Real.log (P₂ a) - Real.log (P₁ a))) = 0 :=
    h_localmin.hasDerivAt_eq_zero hZ'
  -- The Z'-numerator with the flipped sign is also zero.
  have h_fermat' : (∑ a, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam *
      (Real.log (P₁ a) - Real.log (P₂ a))) = 0 := by
    have : (∑ a, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam *
        (Real.log (P₁ a) - Real.log (P₂ a)))
        = -(∑ a, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam *
          (Real.log (P₂ a) - Real.log (P₁ a))) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      ring
    rw [this, h_fermat, neg_zero]
  -- Rewrite the mediator-mean sum as `(1/Z) · (flipped Z'-numerator)`.
  have h_rw : (∑ a, ChernoffConverse.chernoffMediator P₁ P₂ lam a
        * (Real.log (P₁ a) - Real.log (P₂ a)))
      = (∑ a, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam *
          (Real.log (P₁ a) - Real.log (P₂ a))) / chernoffZSum P₁ P₂ lam := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold ChernoffConverse.chernoffMediator
    ring
  rw [h_rw, h_fermat', zero_div]

/-! ## Boundary exclusion (strict Gibbs ⇒ interior minimiser) -/

/-- **Strict Gibbs**: for distinct full-support pmfs `Q ≠ R` the cross sum
`∑ a, Q a · (log (R a) − log (Q a)) < 0` (i.e. `KL(Q‖R) > 0`). -/
private lemma gibbs_cross_sum_neg
    (Q R : α → ℝ) [Nonempty α]
    (hQ_pos : ∀ a, 0 < Q a) (hR_pos : ∀ a, 0 < R a)
    (hQ_sum : ∑ a, Q a = 1) (hR_sum : ∑ a, R a = 1)
    (hne : Q ≠ R) :
    (∑ a, Q a * (Real.log (R a) - Real.log (Q a))) < 0 := by
  -- Each term `Q a · log(R a / Q a) ≤ R a − Q a`, strict at a point where `R a ≠ Q a`.
  have h_term_le : ∀ a, Q a * (Real.log (R a) - Real.log (Q a)) ≤ R a - Q a := by
    intro a
    have hlog : Real.log (R a) - Real.log (Q a) = Real.log (R a / Q a) := by
      rw [Real.log_div (hR_pos a).ne' (hQ_pos a).ne']
    rw [hlog]
    have hbound : Real.log (R a / Q a) ≤ R a / Q a - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hR_pos a) (hQ_pos a))
    have := mul_le_mul_of_nonneg_left hbound (hQ_pos a).le
    calc Q a * Real.log (R a / Q a) ≤ Q a * (R a / Q a - 1) := this
      _ = R a - Q a := by
          have hQne : Q a ≠ 0 := (hQ_pos a).ne'
          field_simp
  -- A point where `R ≠ Q` gives a strict term.
  obtain ⟨a₀, ha₀⟩ : ∃ a, R a ≠ Q a := by
    by_contra h
    push Not at h
    exact hne (funext (fun a => (h a).symm))
  have h_term_lt : Q a₀ * (Real.log (R a₀) - Real.log (Q a₀)) < R a₀ - Q a₀ := by
    have hlog : Real.log (R a₀) - Real.log (Q a₀) = Real.log (R a₀ / Q a₀) := by
      rw [Real.log_div (hR_pos a₀).ne' (hQ_pos a₀).ne']
    rw [hlog]
    have hQne₀ : Q a₀ ≠ 0 := (hQ_pos a₀).ne'
    have hne_div : R a₀ / Q a₀ ≠ 1 := by
      intro h
      exact ha₀ ((div_eq_one_iff_eq hQne₀).mp h)
    have hbound : Real.log (R a₀ / Q a₀) < R a₀ / Q a₀ - 1 :=
      Real.log_lt_sub_one_of_pos (div_pos (hR_pos a₀) (hQ_pos a₀)) hne_div
    have := mul_lt_mul_of_pos_left hbound (hQ_pos a₀)
    calc Q a₀ * Real.log (R a₀ / Q a₀) < Q a₀ * (R a₀ / Q a₀ - 1) := this
      _ = R a₀ - Q a₀ := by field_simp
  -- Sum the (strict) bound: `∑ Q·log(R/Q) < ∑ (R − Q) = 0`.
  have h_sum_lt :
      (∑ a, Q a * (Real.log (R a) - Real.log (Q a))) < ∑ a, (R a - Q a) :=
    Finset.sum_lt_sum (fun a _ => h_term_le a) ⟨a₀, Finset.mem_univ _, h_term_lt⟩
  have h_rhs : (∑ a, (R a - Q a)) = 0 := by
    rw [Finset.sum_sub_distrib, hR_sum, hQ_sum, sub_self]
  rw [h_rhs] at h_sum_lt
  exact h_sum_lt

/-- **`Z'(0) = -KL(P₁‖P₂) < 0` under `P₁ ≠ P₂`** (full-support pmfs). -/
lemma deriv_chernoffZSum_lam_zero_neg
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (hne : P₁ ≠ P₂) :
    (∑ a, (P₁ a) ^ (1 - (0:ℝ)) * (P₂ a) ^ (0:ℝ) *
      (Real.log (P₂ a) - Real.log (P₁ a))) < 0 := by
  have h_eq : (∑ a, (P₁ a) ^ (1 - (0:ℝ)) * (P₂ a) ^ (0:ℝ) *
        (Real.log (P₂ a) - Real.log (P₁ a)))
      = ∑ a, P₁ a * (Real.log (P₂ a) - Real.log (P₁ a)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
  rw [h_eq]
  exact gibbs_cross_sum_neg P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum hne

/-- **`Z'(1) = KL(P₂‖P₁) > 0` under `P₁ ≠ P₂`** (full-support pmfs). -/
lemma deriv_chernoffZSum_lam_one_pos
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (hne : P₁ ≠ P₂) :
    0 < (∑ a, (P₁ a) ^ (1 - (1:ℝ)) * (P₂ a) ^ (1:ℝ) *
      (Real.log (P₂ a) - Real.log (P₁ a))) := by
  have h_eq : (∑ a, (P₁ a) ^ (1 - (1:ℝ)) * (P₂ a) ^ (1:ℝ) *
        (Real.log (P₂ a) - Real.log (P₁ a)))
      = -(∑ a, P₂ a * (Real.log (P₁ a) - Real.log (P₂ a))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [sub_self, Real.rpow_one, Real.rpow_zero, one_mul]
    ring
  rw [h_eq]
  have h_gibbs := gibbs_cross_sum_neg P₂ P₁ hP₂_pos hP₁_pos hP₂_sum hP₁_sum
    (fun h => hne h.symm)
  linarith

/-- **The left endpoint `0` is not a minimiser** when `Z'(0) < 0`. -/
private lemma not_isMinOn_zero_of_deriv_neg
    {Z : ℝ → ℝ} {Z' : ℝ} (hZ' : HasDerivAt Z Z' 0) (hneg : Z' < 0) :
    ¬ IsMinOn Z (Set.Icc (0:ℝ) 1) 0 := by
  intro hmin
  -- slope `(Z x − Z 0)/x → Z' < 0` along `𝓝[>] 0`, so eventually slope < 0.
  have h_slope := (hasDerivAt_iff_tendsto_slope_left_right.mp hZ').2
  have h_ev : ∀ᶠ x in 𝓝[>] (0:ℝ), slope Z 0 x < 0 :=
    h_slope.eventually_lt_const hneg
  have h_mem : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Set.Ioo (0:ℝ) 1 :=
    Filter.eventually_iff.mpr (Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num))
  obtain ⟨x, hx_slope, hx_pos, hx_lt1⟩ := (h_ev.and h_mem).exists
  rw [slope_def_field, sub_zero] at hx_slope
  have hZx_lt : Z x < Z 0 := by
    rcases div_neg_iff.mp hx_slope with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have hx_mem' : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx_pos.le, hx_lt1.le⟩
  exact absurd (hmin hx_mem') (not_le.mpr hZx_lt)

/-- **The right endpoint `1` is not a minimiser** when `Z'(1) > 0`. -/
private lemma not_isMinOn_one_of_deriv_pos
    {Z : ℝ → ℝ} {Z' : ℝ} (hZ' : HasDerivAt Z Z' 1) (hpos : 0 < Z') :
    ¬ IsMinOn Z (Set.Icc (0:ℝ) 1) 1 := by
  intro hmin
  have h_slope := (hasDerivAt_iff_tendsto_slope_left_right.mp hZ').1
  have h_ev : ∀ᶠ x in 𝓝[<] (1:ℝ), 0 < slope Z 1 x :=
    h_slope.eventually_const_lt hpos
  have h_mem : ∀ᶠ x in 𝓝[<] (1:ℝ), x ∈ Set.Ioo (0:ℝ) 1 :=
    Filter.eventually_iff.mpr (Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num))
  obtain ⟨x, hx_slope, hx_pos, hx_lt1⟩ := (h_ev.and h_mem).exists
  rw [slope_def_field] at hx_slope
  have hZx_lt : Z x < Z 1 := by
    have hxsub : x - 1 < 0 := by linarith
    rcases div_pos_iff.mp hx_slope with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have hx_mem' : x ∈ Set.Icc (0:ℝ) 1 := ⟨hx_pos.le, hx_lt1.le⟩
  exact absurd (hmin hx_mem') (not_le.mpr hZx_lt)

/-- **An interior minimiser exists** under `P₁ ≠ P₂` (full-support pmfs):
`∃ λ* ∈ (0,1)`, `IsMinOn Z [0,1] λ*` and `chernoffInfo = -log Z(λ*)`. -/
lemma exists_interior_minimiser
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (hne : P₁ ≠ P₂) :
    ∃ lam ∈ Set.Ioo (0:ℝ) 1,
      IsMinOn (fun l => chernoffZSum P₁ P₂ l) (Set.Icc 0 1) lam ∧
      chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) := by
  -- A minimiser of `Z` on the compact interval `[0,1]` exists.
  have hZ_cont : ContinuousOn (fun l => chernoffZSum P₁ P₂ l) (Set.Icc 0 1) :=
    (chernoffZSum_continuous P₁ P₂ hP₁_pos hP₂_pos).continuousOn
  obtain ⟨lam, hlam_mem, hlam_min⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_isMinOn
      (Set.nonempty_Icc.mpr (by norm_num)) hZ_cont
  -- The minimiser is interior: the endpoints are excluded by the derivative signs.
  have h_int : lam ∈ Set.Ioo (0:ℝ) 1 := by
    rcases (Set.mem_Icc.mp hlam_mem) with ⟨h0, h1⟩
    refine ⟨lt_of_le_of_ne h0 ?_, lt_of_le_of_ne h1 ?_⟩
    · intro h_eq
      -- lam = 0 contradicts `Z'(0) < 0`.
      have hZ'0 := hasDerivAt_chernoffZSum P₁ P₂ hP₁_pos hP₂_pos 0
      exact not_isMinOn_zero_of_deriv_neg hZ'0
        (deriv_chernoffZSum_lam_zero_neg P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum hne)
        (h_eq ▸ hlam_min)
    · intro h_eq
      -- lam = 1 contradicts `Z'(1) > 0`.
      have hZ'1 := hasDerivAt_chernoffZSum P₁ P₂ hP₁_pos hP₂_pos 1
      exact not_isMinOn_one_of_deriv_pos hZ'1
        (deriv_chernoffZSum_lam_one_pos P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum hne)
        (h_eq.symm ▸ hlam_min)
  -- `chernoffInfo = -log Z(λ*)`: the minimiser of `Z` minimises `log ∘ Z` too.
  have h_chern : chernoffInfo P₁ P₂ = -Real.log (chernoffZSum P₁ P₂ lam) := by
    unfold chernoffInfo
    congr 1
    -- `sInf (log Z '' Icc) = log Z(λ*)`.
    have h_lb : Real.log (chernoffZSum P₁ P₂ lam) ∈
        lowerBounds ((fun l : ℝ => Real.log (chernoffZSum P₁ P₂ l)) '' Set.Icc (0:ℝ) 1) := by
      rintro _ ⟨l, hl, rfl⟩
      exact Real.log_le_log (chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam) (hlam_min hl)
    have h_mem_img : Real.log (chernoffZSum P₁ P₂ lam) ∈
        (fun l : ℝ => Real.log (chernoffZSum P₁ P₂ l)) '' Set.Icc (0:ℝ) 1 :=
      ⟨lam, hlam_mem, rfl⟩
    apply le_antisymm
    · exact csInf_le ⟨_, h_lb⟩ h_mem_img
    · exact le_csInf ⟨_, h_mem_img⟩ h_lb
  exact ⟨lam, h_int, hlam_min, h_chern⟩

/-! ## (b) `Q`-LLN reindex plumbing -/

/-- **`Take`-map**: `T ω = fun i : Fin n => ω i.val` pushes `infinitePi Q`
forward to the finite product `Measure.pi (Fin n) Q`. -/
lemma infinitePi_map_take
    (Q : Measure α) [IsProbabilityMeasure Q] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => Q)).map (fun ω : ℕ → α => fun i : Fin n => ω i)
      = Measure.pi (fun _ : Fin n => Q) := by
  classical
  have hT_meas : Measurable (fun ω : ℕ → α => fun i : Fin n => ω i) := by
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply _
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  -- Compute the pushforward on a box.
  rw [Measure.map_apply hT_meas (MeasurableSet.univ_pi hs)]
  -- The preimage of the `Fin n`-box is the `range n`-box with `t j = s ⟨j,_⟩`.
  set t : ℕ → Set α := fun j => if h : j < n then s ⟨j, h⟩ else Set.univ with ht
  have h_preimage : (fun ω : ℕ → α => fun i : Fin n => ω i) ⁻¹' (Set.univ.pi s)
      = Set.pi (↑(Finset.range n)) t := by
    ext ω
    constructor
    · intro h j hj
      rw [Finset.coe_range, Set.mem_Iio] at hj
      simp only [ht, dif_pos hj]
      have := (Set.mem_univ_pi.mp h) ⟨j, hj⟩
      simpa using this
    · intro h i _
      have hi := h i.val (by rw [Finset.coe_range, Set.mem_Iio]; exact i.isLt)
      simpa only [ht, dif_pos i.isLt, Fin.eta] using hi
  have h_mt : ∀ j ∈ Finset.range n, MeasurableSet (t j) := by
    intro j hj
    simp only [ht]
    split_ifs with h
    · exact hs _
    · exact MeasurableSet.univ
  rw [h_preimage]
  rw [show ((↑(Finset.range n) : Set ℕ).pi t) = Set.pi (↑(Finset.range n)) t from rfl,
    Measure.infinitePi_pi (μ := fun _ : ℕ => Q) (s := Finset.range n) (t := t) h_mt]
  -- Reindex `∏ j ∈ range n, Q (t j) = ∏ i : Fin n, Q (s i)`.
  rw [← Fin.prod_univ_eq_prod_range (fun j => Q (t j)) n]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [ht, dif_pos i.isLt, Fin.eta]

/-- **Band-mass = `Q^n`-real-measure of the band**: the pmf-form band mass
`∑_{x ∈ band} ∏ mediator` equals the real measure of the band under
`Measure.pi (Fin n) Q`, `Q = chernoffMediatorMeasure`. -/
lemma chernoffMediatorMeasure_pi_real_band
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (n : ℕ) (ε : ℝ) :
    (∑ x ∈ (chernoffLogRatioBand P₁ P₂ n ε).toFinite.toFinset,
        ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i))
      = (Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam)).real
          (chernoffLogRatioBand P₁ P₂ n ε) := by
  haveI : IsProbabilityMeasure (chernoffMediatorMeasure P₁ P₂ lam) :=
    chernoffMediatorMeasure_isProbabilityMeasure P₁ P₂ hP₁_pos hP₂_pos lam
  -- Each term `∏ mediator = (Q^n).real {x}`.
  have h_term : ∀ x : Fin n → α,
      (∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i))
        = (Measure.pi (fun _ : Fin n => chernoffMediatorMeasure P₁ P₂ lam)).real {x} := by
    intro x
    rw [Measure.real, ChernoffPerTiltSanov.chernoffMediatorMeasure_pi_singleton_toReal
      P₁ P₂ hP₁_pos hP₂_pos lam x]
  simp_rw [h_term]
  -- Sum of singleton real-measures over the band finset = real measure of the finset.
  rw [MeasureTheory.sum_measureReal_singleton]
  -- The band finset coerces back to the band set.
  rw [Measure.real, Measure.real, Set.Finite.coe_toFinset]

/-- **The `Q`-mean of `Y = log P₁ − log P₂` equals the mediator-mean sum**. -/
lemma chernoffMediator_integral_eq
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (lam : ℝ) :
    ∫ a, (Real.log (P₁ a) - Real.log (P₂ a)) ∂(chernoffMediatorMeasure P₁ P₂ lam)
      = ∑ a, ChernoffConverse.chernoffMediator P₁ P₂ lam a *
          (Real.log (P₁ a) - Real.log (P₂ a)) := by
  haveI : IsProbabilityMeasure (chernoffMediatorMeasure P₁ P₂ lam) :=
    chernoffMediatorMeasure_isProbabilityMeasure P₁ P₂ hP₁_pos hP₂_pos lam
  rw [MeasureTheory.integral_fintype (hf := MeasureTheory.Integrable.of_finite)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [chernoffMediatorMeasure_real_singleton P₁ P₂ hP₁_pos hP₂_pos lam a, smul_eq_mul]

/-! ## (b) `Q`-LLN core: band mass → 1 from interior optimality -/

/-- **Genuine core**: at an interior minimiser `λ*` (with the vanishing-mean
condition from `(a)`), the band has `Q^n`-mass eventually `≥ 1/2`. This is the
genuine discharge of `IsChernoffBandMassToOne` modulo first-order optimality. -/
theorem isChernoffBandMassToOne_of_interior_optimal
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (lam : ℝ) (hlam_int : lam ∈ Set.Ioo (0:ℝ) 1)
    (hlam_min : IsMinOn (fun l => chernoffZSum P₁ P₂ l) (Set.Icc 0 1) lam) :
    IsChernoffBandMassToOne P₁ P₂ lam := by
  classical
  -- Abbreviations.
  set Q : Measure α := chernoffMediatorMeasure P₁ P₂ lam with hQ
  haveI hQ_prob : IsProbabilityMeasure Q :=
    chernoffMediatorMeasure_isProbabilityMeasure P₁ P₂ hP₁_pos hP₂_pos lam
  set Y : α → ℝ := fun a => Real.log (P₁ a) - Real.log (P₂ a) with hY
  have hY_meas : Measurable Y := measurable_of_finite Y
  set μ : Measure (ℕ → α) := Measure.infinitePi (fun _ : ℕ => Q) with hμ
  set X : ℕ → (ℕ → α) → ℝ := fun i ω => Y (ω i) with hX
  -- The `Q`-mean of `Y` is `0` (first-order optimality).
  have h_mean0 : μ[X 0] = 0 := by
    have h_push : μ[X 0] = ∫ a, Y a ∂Q := by
      have hmap : μ.map (fun ω : ℕ → α => ω 0) = Q := Measure.infinitePi_map_eval _ 0
      calc μ[X 0] = ∫ a, Y a ∂(μ.map (fun ω : ℕ → α => ω 0)) := by
            rw [integral_map (measurable_pi_apply 0).aemeasurable
              hY_meas.aestronglyMeasurable]
        _ = ∫ a, Y a ∂Q := by rw [hmap]
    rw [h_push, hY, chernoffMediator_integral_eq P₁ P₂ hP₁_pos hP₂_pos lam,
      chernoffMediator_mean_logRatio_eq_zero P₁ P₂ hP₁_pos hP₂_pos lam hlam_int hlam_min]
  -- IID structure: pairwise independence + identical distribution.
  have h_int : Integrable (X 0) μ := by
    have hYQ : Integrable Y Q := MeasureTheory.Integrable.of_finite
    have hmap : μ.map (fun ω : ℕ → α => ω 0) = Q := Measure.infinitePi_map_eval _ 0
    rw [← hmap] at hYQ
    exact (integrable_map_measure hY_meas.aestronglyMeasurable
      (measurable_pi_apply 0).aemeasurable).mp hYQ
  have h_indep : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) X) := by
    intro i j hij
    exact (InformationTheory.Shannon.Cramer.Discharge.iIndepFun_eval_under_infinitePi
      (μ₀ := Q) hY_meas).indepFun hij
  have h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ := fun i =>
    InformationTheory.Shannon.Cramer.Discharge.identDistrib_eval_under_infinitePi
      (μ₀ := Q) hY_meas i
  -- SLLN: empirical mean → `μ[X 0] = 0` almost surely.
  have h_slln : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / n) atTop (𝓝 (0:ℝ)) := by
    have := strong_law_ae_real X h_int h_indep h_ident
    rw [h_mean0] at this
    exact this
  -- Convergence in measure of the empirical mean to `0`.
  set Sn : ℕ → (ℕ → α) → ℝ := fun n ω => (∑ i ∈ Finset.range n, X i ω) / n with hSn
  have h_inm : MeasureTheory.TendstoInMeasure μ Sn atTop (fun _ => (0:ℝ)) := by
    apply MeasureTheory.tendstoInMeasure_of_tendsto_ae
    · intro n
      apply Measurable.aestronglyMeasurable
      apply Measurable.div_const
      exact Finset.measurable_sum _ (fun i _ => hY_meas.comp (measurable_pi_apply i))
    · exact h_slln
  -- Now the discharge proper.
  intro ε hε
  -- The complement of the band has `μ`-mass → 0 (convergence in measure at `ε`).
  have h_tail : Tendsto
      (fun n : ℕ => μ {ω | ε ≤ |Sn n ω|}) atTop (𝓝 0) := by
    have hinm := h_inm (ENNReal.ofReal ε) (by positivity)
    refine hinm.congr (fun n => ?_)
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [edist_dist, Real.dist_eq, sub_zero, ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  -- Band mass (pmf form) equals the `μ`-real measure of the cylinder `{|Sn| ≤ ε}`.
  have h_band_eq : ∀ n : ℕ, 0 < n →
      (∑ x ∈ (chernoffLogRatioBand P₁ P₂ n ε).toFinite.toFinset,
          ∏ i, ChernoffConverse.chernoffMediator P₁ P₂ lam (x i))
        = μ.real {ω | |Sn n ω| ≤ ε} := by
    intro n hn
    rw [chernoffMediatorMeasure_pi_real_band P₁ P₂ hP₁_pos hP₂_pos lam n ε]
    -- `Q^n = μ.map T`, so `(Q^n).real band = μ.real (T ⁻¹' band)`.
    have hmap := infinitePi_map_take Q n
    have hT_meas : Measurable (fun ω : ℕ → α => fun i : Fin n => ω i) := by
      apply measurable_pi_lambda; intro i; exact measurable_pi_apply _
    have h_band_meas : MeasurableSet (chernoffLogRatioBand P₁ P₂ n ε) :=
      (chernoffLogRatioBand P₁ P₂ n ε).toFinite.measurableSet
    rw [Measure.real, Measure.real, ← hmap, Measure.map_apply hT_meas h_band_meas]
    -- `T ⁻¹' band = {ω | |Sn n ω| ≤ ε}`.
    congr 2
    ext ω
    simp only [Set.mem_preimage, ChernoffSanovDischarge.mem_chernoffLogRatioBand_iff,
      Set.mem_setOf_eq, hSn, hX, hY]
    rw [Fin.sum_univ_eq_sum_range (fun i => Real.log (P₁ (ω i)) - Real.log (P₂ (ω i))) n]
    rw [abs_div, abs_of_pos (by exact_mod_cast hn : (0:ℝ) < n),
      div_le_iff₀ (by exact_mod_cast hn : (0:ℝ) < n)]
    rw [mul_comm]
  -- Band mass → 1: it is `μ.real univ − μ.real {ε < |Sn|}` and the tail → 0.
  -- We use the tail `{ε ≤ |Sn|} ⊇ {ε < |Sn|}` to bound the complement.
  have h_band_tendsto : Tendsto
      (fun n : ℕ => μ.real {ω | |Sn n ω| ≤ ε}) atTop (𝓝 1) := by
    -- complement: `{|Sn| ≤ ε}ᶜ = {ε < |Sn|}`; its real mass → 0.
    have h_compl_meas : ∀ n, MeasurableSet {ω | |Sn n ω| ≤ ε} := by
      intro n
      apply measurableSet_le _ measurable_const
      apply Measurable.abs
      apply Measurable.div_const
      exact Finset.measurable_sum _ (fun i _ => hY_meas.comp (measurable_pi_apply i))
    -- real-tail → 0 from the ENNReal tail.
    have h_tail_real : Tendsto
        (fun n : ℕ => μ.real {ω | ε ≤ |Sn n ω|}) atTop (𝓝 0) := by
      have : (fun n : ℕ => μ.real {ω | ε ≤ |Sn n ω|})
          = fun n : ℕ => (μ {ω | ε ≤ |Sn n ω|}).toReal := by
        funext n; rw [Measure.real]
      rw [this]
      rw [show (0:ℝ) = (0 : ℝ≥0∞).toReal by simp]
      exact (ENNReal.continuousAt_toReal (by simp)).tendsto.comp h_tail
    -- `μ.real {|Sn| ≤ ε} = 1 − μ.real {ε < |Sn|}`, bounded between `1 − tail` and `1`.
    have h_eq : ∀ n, μ.real {ω | |Sn n ω| ≤ ε}
        = 1 - μ.real {ω | ε < |Sn n ω|} := by
      intro n
      have h_set : {ω | |Sn n ω| ≤ ε} = {ω | ε < |Sn n ω|}ᶜ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
      rw [h_set, measureReal_compl (by
        apply measurableSet_lt measurable_const
        apply Measurable.abs
        apply Measurable.div_const
        exact Finset.measurable_sum _ (fun i _ => hY_meas.comp (measurable_pi_apply i)))]
      simp [probReal_univ]
    -- `{ε < |Sn|} ⊆ {ε ≤ |Sn|}`, so its real mass is squeezed to 0.
    have h_lt_tendsto : Tendsto
        (fun n : ℕ => μ.real {ω | ε < |Sn n ω|}) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => measureReal_nonneg) (g := fun n => μ.real {ω | ε ≤ |Sn n ω|})
      · intro n
        exact measureReal_mono (fun ω (hω : ε < |Sn n ω|) => le_of_lt hω)
      · exact h_tail_real
    rw [show (1:ℝ) = 1 - 0 by ring]
    simp_rw [h_eq]
    exact tendsto_const_nhds.sub h_lt_tendsto
  -- Eventually band mass ≥ 1/2.
  have h_ev_half : ∀ᶠ n : ℕ in atTop, (1/2 : ℝ) ≤ μ.real {ω | |Sn n ω| ≤ ε} :=
    h_band_tendsto.eventually_const_le (by norm_num)
  filter_upwards [h_ev_half, eventually_gt_atTop 0] with n hn_half hn_pos
  rw [h_band_eq n hn_pos]
  exact hn_half

/-! ## Headline: regularity-only Chernoff converse -/

/-- **Chernoff converse, unconditional (regularity only)**: for full-support
pmfs `P₁ ≠ P₂`, `limsup rate ≤ chernoffInfo`. -/
theorem chernoff_converse_holds
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (hne : P₁ ≠ P₂) :
    Filter.limsup
      (fun n : ℕ => -((1 : ℝ) / n) * Real.log (bayesErrorMinPmf P₁ P₂ n)) atTop
        ≤ chernoffInfo P₁ P₂ := by
  obtain ⟨lam, hlam_int, hlam_min, h_chern⟩ :=
    exists_interior_minimiser P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum hne
  refine ChernoffSanovDischarge.chernoff_converse_of_bandMass P₁ P₂ hP₁_pos hP₂_pos ?_
  refine ⟨lam, Set.Ioo_subset_Icc_self hlam_int, h_chern, ?_⟩
  exact isChernoffBandMassToOne_of_interior_optimal P₁ P₂ hP₁_pos hP₂_pos lam hlam_int hlam_min

end InformationTheory.Shannon.ChernoffBandMassDischarge
