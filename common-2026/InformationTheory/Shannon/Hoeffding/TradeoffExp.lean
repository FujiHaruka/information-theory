import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Sanov.LDP
import InformationTheory.Shannon.Sanov.LDPEquality
import InformationTheory.Shannon.KLDivContinuous
import InformationTheory.Shannon.CsiszarProjection
import InformationTheory.Shannon.Chernoff.Basic
import InformationTheory.Shannon.Hoeffding.Tradeoff
import InformationTheory.Shannon.Hoeffding.SandwichDischarge

/-!
# Hoeffding tradeoff — exponential-level redefinition (full genuine closure)

This file fixes the **DEF-FLAW** of the constant-α `steinTypeII_at_level_pmf`
headline (sandwich plan judgement log #4): the operational quantity is
redefined at the **exponential level** — the acceptance region is the
KL-sublevel set of empirical types `E_r n = {c | klDivIndex c n P₁ ≤ r}` — and
the resulting Type-II error converges to `hoeffdingE2 P₁ P₂ r`. The two
directions are proved separately: the converse (limsup) via
`sanov_ldp_upper_bound` on the non-perturbed minimizer `Qstar`, and the
achievability (liminf) via `sanov_ldp_lower_bound_pointwise` on a perturbation
`Qstar_ε = (1-ε)·Qstar + ε·P₁` (strict KL-interior, so the rounded types are
eventually in `E_r`) followed by `ε → 0`. The headline `hoeffding_tradeoff_exp`
is **hypothesis-free** on the interior `0 < r < klDivPmf P₂ P₁` (no `h_in_E`).

See `docs/shannon/hoeffding-exponent-level-redef-plan.md`.
-/

namespace InformationTheory.Shannon.HoeffdingTradeoffExp

open MeasureTheory ProbabilityTheory Real Filter
open InformationTheory.Shannon
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon.HoeffdingTradeoff
open InformationTheory.Shannon.HoeffdingSandwichDischarge
open scoped BigOperators Topology ENNReal

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Phase 1 — `E_r` acceptance region + `steinTypeII_exp` definition -/

/-- **Exponential-level acceptance region**: *valid* empirical types
(`∑ c = n`) whose KL divergence from `P₁` is within `r` (a closed KL-sublevel
set, indexed by `TypeCountIndex`). The `∑ c = n` clause restricts to genuine
empirical pmfs `c/n`; types with `∑ c ≠ n` have an empty type class
(`typeClassByCount_empty_of_sum_ne`) so the acceptance region is unchanged. -/
noncomputable def E_r (P₁ : α → ℝ) (hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₁_sum : ∑ a, P₁ a = 1)
    (n : ℕ) (r : ℝ) : Finset (TypeCountIndex α n) :=
  letI := Classical.decPred
    (fun c : TypeCountIndex α n =>
      0 < n ∧ (∑ a, (c a : ℕ)) = n ∧
      klDivIndex (fun a => (c a : ℕ)) n (pmfToMeasure P₁ hP₁_nn hP₁_sum) ≤ r)
  Finset.univ.filter
    (fun c : TypeCountIndex α n =>
      0 < n ∧ (∑ a, (c a : ℕ)) = n ∧
      klDivIndex (fun a => (c a : ℕ)) n (pmfToMeasure P₁ hP₁_nn hP₁_sum) ≤ r)

/-- **Type-II error of the exponential-level test**: the `P₂ⁿ` mass of the
acceptance region `⋃_{c ∈ E_r} T_c`. -/
noncomputable def steinTypeII_exp (P₁ P₂ : α → ℝ)
    (hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₁_sum : ∑ a, P₁ a = 1)
    (hP₂_nn : ∀ a, 0 ≤ P₂ a) (hP₂_sum : ∑ a, P₂ a = 1)
    (n : ℕ) (r : ℝ) : ℝ :=
  ((Measure.pi (fun _ : Fin n => pmfToMeasure P₂ hP₂_nn hP₂_sum))
    (⋃ c ∈ E_r P₁ hP₁_nn hP₁_sum n r,
      typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal

lemma mem_E_r_iff (P₁ : α → ℝ) (hP₁_nn : ∀ a, 0 ≤ P₁ a) (hP₁_sum : ∑ a, P₁ a = 1)
    (n : ℕ) (r : ℝ) (c : TypeCountIndex α n) :
    c ∈ E_r P₁ hP₁_nn hP₁_sum n r ↔
      0 < n ∧ (∑ a, (c a : ℕ)) = n ∧
      klDivIndex (fun a => (c a : ℕ)) n (pmfToMeasure P₁ hP₁_nn hP₁_sum) ≤ r := by
  unfold E_r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## Phase 2 — KL bridges (count-0-tolerant) -/

omit [DecidableEq α] in
/-- **`klDivPmf` log-diff form tolerant of count-0 atoms in `P`**: requires only
`Q` full support (and both sum to 1), not `P` full support. The `P a = 0` term
matches on both sides (`Q a` vs `0 + Q a - 0`). -/
lemma klDivPmf_eq_log_diff_sum_of_Q_pos
    {P Q : α → ℝ}
    (hP_nn : ∀ a, 0 ≤ P a)
    (hP_sum : ∑ a, P a = 1)
    (hQ_sum : ∑ a, Q a = 1)
    (hQ_pos : ∀ a, 0 < Q a) :
    klDivPmf P Q = ∑ a : α, P a * (Real.log (P a) - Real.log (Q a)) := by
  unfold klDivPmf
  have h_term : ∀ a : α,
      Q a * klFun (P a / Q a) = P a * (Real.log (P a) - Real.log (Q a)) + (Q a - P a) := by
    intro a
    have hQne : Q a ≠ 0 := (hQ_pos a).ne'
    rcases eq_or_lt_of_le (hP_nn a) with hP0 | hPpos
    · -- P a = 0: both sides reduce to Q a.
      rw [← hP0]
      simp [InformationTheory.klFun_zero]
    · have h_log_div : Real.log (P a / Q a) = Real.log (P a) - Real.log (Q a) :=
        Real.log_div hPpos.ne' hQne
      unfold klFun
      rw [h_log_div]
      field_simp
      ring
  simp_rw [h_term]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hQ_sum, hP_sum]
  ring

omit [DecidableEq α] in
/-- **`klDivIndex` as `klDivPmf` of the empirical pmf** (count-0 tolerant):
for `∑ c = n`, `n > 0`, `Q` full support,
`klDivIndex c n Q = klDivPmf (c · / n) (Q.real ∘ singleton)`. -/
lemma klDivIndex_eq_klDivPmf_empirical
    (Q : Measure α) (hQ_pos : ∀ a, 0 < Q.real {a}) (hQ_sum : ∑ a, Q.real {a} = 1)
    {n : ℕ} (hn : 0 < n) {c : α → ℕ} (hc_sum : (∑ a, c a) = n) :
    klDivIndex c n Q
      = klDivPmf (fun a => (c a : ℝ) / n) (fun a => Q.real {a}) := by
  classical
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have h_emp_nn : ∀ a, 0 ≤ (c a : ℝ) / n := fun a => by positivity
  have h_emp_sum : ∑ a, (c a : ℝ) / n = 1 := by
    rw [← Finset.sum_div]
    rw [show (∑ a, (c a : ℝ)) = ((∑ a, c a : ℕ) : ℝ) by push_cast; rfl]
    rw [hc_sum]
    field_simp
  rw [klDivIndex_eq_ofVec, klDivSumForm_ofVec]
  rw [klDivPmf_eq_log_diff_sum_of_Q_pos h_emp_nn h_emp_sum hQ_sum hQ_pos]

/-! ## Phase 5 — Qstar from the constructive minimizer -/

-- (consumed inline in the headline; no standalone lemma needed)

/-! ## Phase 2 (continued) — `h_in_E` from rounded-type KL convergence -/

/-- **Eventually accepted**: the rounded type of a strict-interior `Qstar`
(`klDivPmf Qstar P₁ < r`) lands in `E_r n` for all large `n`. -/
lemma roundedTypeIndex_mem_E_r_eventually
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₁_sum : ∑ a, P₁ a = 1)
    {Qstar : α → ℝ} (hQs_sum : ∑ a, Qstar a = 1) (hQs_nn : ∀ a, 0 ≤ Qstar a)
    {r : ℝ} (h_strict : klDivPmf Qstar P₁ < r) :
    ∀ᶠ n : ℕ in atTop,
      roundedTypeIndex Qstar n
        ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r := by
  set μ₁ := pmfToMeasure P₁ (fun a => (hP₁_pos a).le) hP₁_sum with hμ₁
  have hμ₁_pos : ∀ a, 0 < μ₁.real {a} := fun a => by
    rw [hμ₁, pmfToMeasure_real_singleton]; exact hP₁_pos a
  -- KL of the rounded type of Qstar converges to klDivSumForm_ofVec Qstar (μ₁.real ∘ singleton).
  have h_tendsto :
      Tendsto (fun n : ℕ =>
          klDivIndex (fun a => (roundedTypeIndex Qstar n a : ℕ)) n μ₁)
        atTop (𝓝 (klDivSumForm_ofVec Qstar (fun a => μ₁.real {a}))) :=
    klDivIndex_rounded_tendsto μ₁ hμ₁_pos Qstar hQs_sum hQs_nn
  -- The limit equals klDivPmf Qstar P₁.
  have h_lim_eq : klDivSumForm_ofVec Qstar (fun a => μ₁.real {a}) = klDivPmf Qstar P₁ := by
    rw [klDivSumForm_ofVec]
    rw [klDivPmf_eq_log_diff_sum_of_Q_pos hQs_nn hQs_sum hP₁_sum hP₁_pos]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hμ₁, pmfToMeasure_real_singleton]
  rw [h_lim_eq] at h_tendsto
  -- Eventually klDivIndex < r ⇒ ≤ r ⇒ membership.
  have h_event : ∀ᶠ n : ℕ in atTop,
      klDivIndex (fun a => (roundedTypeIndex Qstar n a : ℕ)) n μ₁ < r :=
    h_tendsto.eventually (eventually_lt_nhds h_strict)
  have h_n_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
  filter_upwards [h_event, h_n_pos] with n hn hn_pos
  rw [mem_E_r_iff]
  exact ⟨hn_pos, roundedTypeIndex_sum Qstar hQs_sum hQs_nn n hn_pos, hn.le⟩

/-! ## Phase 2 (continued) — perturbation toward `P₁` (discharges L-EXP-IN) -/

/-- **Perturbed minimizer** `Qstar_ε := (1-ε)·Qstar + ε·P₁`. -/
noncomputable def Qstar_perturb (Qstar P₁ : α → ℝ) (ε : ℝ) : α → ℝ :=
  fun a => (1 - ε) * Qstar a + ε * P₁ a

omit [DecidableEq α] in
lemma Qstar_perturb_nonneg {Qstar P₁ : α → ℝ}
    (hQs_nn : ∀ a, 0 ≤ Qstar a) (hP₁_nn : ∀ a, 0 ≤ P₁ a)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ a, 0 ≤ Qstar_perturb Qstar P₁ ε a := by
  intro a; unfold Qstar_perturb
  have h1 : 0 ≤ 1 - ε := by linarith
  have hQa := hQs_nn a
  have hPa := hP₁_nn a
  have t1 : 0 ≤ (1 - ε) * Qstar a := mul_nonneg h1 hQa
  have t2 : 0 ≤ ε * P₁ a := mul_nonneg hε0 hPa
  linarith

omit [DecidableEq α] in
lemma Qstar_perturb_sum {Qstar P₁ : α → ℝ}
    (hQs_sum : ∑ a, Qstar a = 1) (hP₁_sum : ∑ a, P₁ a = 1) (ε : ℝ) :
    ∑ a, Qstar_perturb Qstar P₁ ε a = 1 := by
  unfold Qstar_perturb
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hQs_sum, hP₁_sum]
  ring

omit [DecidableEq α] in
/-- **Strict interior of the perturbation**: by convexity of `klDivPmf · P₁`
(`klDivPmf_strictConvexOn_left`) plus `klDivPmf P₁ P₁ = 0`, a tiny push toward
`P₁` strictly lowers the constraint value below the active value
`klDivPmf Qstar P₁ ≤ r`. -/
lemma klDivPmf_perturb_lt
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₁_sum : ∑ a, P₁ a = 1)
    {Qstar : α → ℝ} (hQs_sum : ∑ a, Qstar a = 1) (hQs_nn : ∀ a, 0 ≤ Qstar a)
    {r : ℝ} (hr_pos : 0 < r) (h_le : klDivPmf Qstar P₁ ≤ r)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    klDivPmf (Qstar_perturb Qstar P₁ ε) P₁ < r := by
  classical
  have hP₁_nn : ∀ a, 0 ≤ P₁ a := fun a => (hP₁_pos a).le
  have hQs_mem : Qstar ∈ stdSimplex ℝ α := ⟨hQs_nn, hQs_sum⟩
  have hP₁_mem : P₁ ∈ stdSimplex ℝ α := ⟨hP₁_nn, hP₁_sum⟩
  -- Convexity of `klDivPmf · P₁` on the simplex.
  have h_conv := (klDivPmf_strictConvexOn_left P₁ hP₁_pos).convexOn.2
    hQs_mem hP₁_mem (by linarith : (0 : ℝ) ≤ 1 - ε) hε0.le (by ring)
  -- The convex-combination point equals `Qstar_perturb`.
  have h_pt : (1 - ε) • Qstar + ε • P₁ = Qstar_perturb Qstar P₁ ε := by
    funext a; simp [Qstar_perturb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h_pt] at h_conv
  -- klDivPmf P₁ P₁ = 0.
  have h_self : klDivPmf P₁ P₁ = 0 := klDivPmf_self_eq_zero P₁ hP₁_pos
  -- klDivPmf Qstar P₁ ≥ 0.
  have h_nn : 0 ≤ klDivPmf Qstar P₁ := klDivPmf_nonneg Qstar P₁ hQs_nn hP₁_nn
  simp only [smul_eq_mul, h_self, mul_zero, add_zero] at h_conv
  -- h_conv : klDivPmf Qstar_ε P₁ ≤ (1 - ε) * klDivPmf Qstar P₁
  rcases eq_or_lt_of_le h_nn with h_zero | h_pos
  · -- klDivPmf Qstar P₁ = 0 ⇒ Qstar_ε's KL ≤ 0 < r.
    rw [← h_zero, mul_zero] at h_conv
    linarith
  · -- klDivPmf Qstar P₁ > 0 ⇒ strict shrink (1-ε) factor < klDivPmf Qstar P₁ ≤ r.
    calc klDivPmf (Qstar_perturb Qstar P₁ ε) P₁
        ≤ (1 - ε) * klDivPmf Qstar P₁ := h_conv
      _ < klDivPmf Qstar P₁ := by nlinarith
      _ ≤ r := h_le

omit [DecidableEq α] in
/-- **ε-continuity of `klDivPmf Qstar_ε P₂`**: as `ε → 0`, the perturbed KL
divergence converges to `klDivPmf Qstar P₂` (continuity of `klDivPmf · P₂`). -/
lemma klDivPmf_perturb_tendsto
    (P₁ P₂ : α → ℝ) (hP₂_pos : ∀ a, 0 < P₂ a)
    {Qstar : α → ℝ} :
    Tendsto (fun ε : ℝ => klDivPmf (Qstar_perturb Qstar P₁ ε) P₂)
      (𝓝[>] 0) (𝓝 (klDivPmf Qstar P₂)) := by
  classical
  -- ε ↦ Qstar_perturb is continuous (each coordinate is) and equals Qstar at 0.
  have h_pt_cont : Continuous (fun ε : ℝ => Qstar_perturb Qstar P₁ ε) := by
    apply continuous_pi
    intro a
    unfold Qstar_perturb
    fun_prop
  have h_pt0 : Qstar_perturb Qstar P₁ 0 = Qstar := by
    funext a; simp [Qstar_perturb]
  -- klDivPmf · P₂ is continuous.
  have h_kl_cont : Continuous (fun P : α → ℝ => klDivPmf P P₂) :=
    continuous_klDivPmf_left P₂ hP₂_pos
  have h_comp : Continuous (fun ε : ℝ => klDivPmf (Qstar_perturb Qstar P₁ ε) P₂) :=
    h_kl_cont.comp h_pt_cont
  have h_tendsto : Tendsto (fun ε : ℝ => klDivPmf (Qstar_perturb Qstar P₁ ε) P₂)
      (𝓝 0) (𝓝 (klDivPmf (Qstar_perturb Qstar P₁ 0) P₂)) := h_comp.tendsto 0
  rw [h_pt0] at h_tendsto
  exact h_tendsto.mono_left nhdsWithin_le_nhds

/-! ## Phase 4 — `h_minimizer` premise -/

/-- **Minimizer premise**: for every `c ∈ E_r n`, the minimizer value
`klDivSumForm_ofVec Qstar (P₂.real ∘ singleton)` lower-bounds `klDivIndex c n P₂`.
Holds for the strict-interior Qstar. -/
lemma hoeffding_exp_minimizer
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {r : ℝ} (_h_r_pos : 0 < r)
    {Qstar : α → ℝ}
    (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ r)
    (hQs_pos : ∀ a, 0 < Qstar a)
    (hQs_min : hoeffdingE2 P₁ P₂ r = klDivPmf Qstar P₂) :
    ∀ n, ∀ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
      klDivSumForm_ofVec Qstar (fun a => (pmfToMeasure P₂ (fun a => (hP₂_pos a).le) hP₂_sum).real {a})
        ≤ klDivIndex (fun a => (c a : ℕ)) n (pmfToMeasure P₂ (fun a => (hP₂_pos a).le) hP₂_sum) := by
  set μ₁ := pmfToMeasure P₁ (fun a => (hP₁_pos a).le) hP₁_sum with hμ₁
  set μ₂ := pmfToMeasure P₂ (fun a => (hP₂_pos a).le) hP₂_sum with hμ₂
  have hμ₁_real : ∀ a, μ₁.real {a} = P₁ a := fun a => by rw [hμ₁, pmfToMeasure_real_singleton]
  have hμ₂_real : ∀ a, μ₂.real {a} = P₂ a := fun a => by rw [hμ₂, pmfToMeasure_real_singleton]
  have hμ₁_pos : ∀ a, 0 < μ₁.real {a} := fun a => by rw [hμ₁_real]; exact hP₁_pos a
  have hμ₂_pos : ∀ a, 0 < μ₂.real {a} := fun a => by rw [hμ₂_real]; exact hP₂_pos a
  have hμ₁_sum : ∑ a, μ₁.real {a} = 1 := by simp only [hμ₁_real]; exact hP₁_sum
  have hμ₂_sum : ∑ a, μ₂.real {a} = 1 := by simp only [hμ₂_real]; exact hP₂_sum
  -- LHS = klDivPmf Qstar P₂.
  have hQs_sum : ∑ a, Qstar a = 1 := hQs_mem.1.2
  have hQs_nn : ∀ a, 0 ≤ Qstar a := fun a => (hQs_pos a).le
  have h_lhs : klDivSumForm_ofVec Qstar (fun a => μ₂.real {a}) = klDivPmf Qstar P₂ := by
    rw [klDivSumForm_ofVec, klDivPmf_eq_log_diff_sum_of_Q_pos hQs_nn hQs_sum hP₂_sum hP₂_pos]
    exact Finset.sum_congr rfl fun a _ => by simp only [hμ₂_real]
  rw [h_lhs]
  intro n c hc
  rw [mem_E_r_iff] at hc
  obtain ⟨hn_pos, hc_sum, hc_kl⟩ := hc
  -- empirical pmf p := c/n is in the constraint set K.
  set p : α → ℝ := fun a => (c a : ℝ) / n with hp_def
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hp_nn : ∀ a, 0 ≤ p a := fun a => by rw [hp_def]; positivity
  have hp_sum : ∑ a, p a = 1 := by
    rw [hp_def, ← Finset.sum_div,
      show (∑ a, (c a : ℝ)) = ((∑ a, c a : ℕ) : ℝ) by push_cast; rfl, hc_sum]
    field_simp
  have hp_simplex : p ∈ stdSimplex ℝ α := ⟨hp_nn, hp_sum⟩
  -- klDivIndex c n μ₂ = klDivPmf p μ₂.real = klDivPmf p P₂.
  have h_index₂ : klDivIndex (fun a => (c a : ℕ)) n μ₂ = klDivPmf p P₂ := by
    rw [klDivIndex_eq_klDivPmf_empirical μ₂ hμ₂_pos hμ₂_sum hn_pos hc_sum]
    show klDivPmf p (fun a => μ₂.real {a}) = klDivPmf p P₂
    unfold klDivPmf
    exact Finset.sum_congr rfl fun a _ => by simp only [hμ₂_real]
  have h_index₁ : klDivIndex (fun a => (c a : ℕ)) n μ₁ = klDivPmf p P₁ := by
    rw [klDivIndex_eq_klDivPmf_empirical μ₁ hμ₁_pos hμ₁_sum hn_pos hc_sum]
    show klDivPmf p (fun a => μ₁.real {a}) = klDivPmf p P₁
    unfold klDivPmf
    exact Finset.sum_congr rfl fun a _ => by simp only [hμ₁_real]
  rw [h_index₂]
  -- p ∈ K since klDivPmf p P₁ ≤ r.
  have hp_mem : p ∈ hoeffdingConstraintSet P₁ r := ⟨hp_simplex, h_index₁ ▸ hc_kl⟩
  -- klDivPmf Qstar P₂ = hoeffdingE2 ≤ klDivPmf p P₂ via csInf_le.
  rw [← hQs_min]
  unfold hoeffdingE2
  have h_bdd : BddBelow ((fun Q : α → ℝ => klDivPmf Q P₂) ''
      {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ r}) := by
    refine ⟨0, ?_⟩
    rintro y ⟨Q', hQ', rfl⟩
    exact klDivPmf_nonneg Q' P₂ hQ'.1.1 (fun a => (hP₂_pos a).le)
  exact csInf_le h_bdd ⟨p, hp_mem, rfl⟩

/-! ## Phase 2 (continued) — achievability via perturbation (L-EXP-IN discharge) -/

/-- **Achievability rate bound at perturbation level `ε`**: for the strictly
interior perturbed minimizer `Qstar_ε`, the genuine strict-interior
`roundedTypeIndex_mem_E_r_eventually` feeds `sanov_ldp_lower_bound_pointwise`,
yielding `-klDivPmf Qstar_ε P₂ ≤ liminf (rate)`. **No `h_in_E` is used.** -/
lemma hoeffding_exp_liminf_perturb
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {r : ℝ} (h_r_pos : 0 < r)
    {Qstar : α → ℝ} (hQs_sum : ∑ a, Qstar a = 1) (hQs_nn : ∀ a, 0 ≤ Qstar a)
    (h_le : klDivPmf Qstar P₁ ≤ r)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    -klDivPmf (Qstar_perturb Qstar P₁ ε) P₂
      ≤ Filter.liminf (fun n : ℕ => (1 / (n : ℝ)) * Real.log
          (((Measure.pi (fun _ : Fin n =>
              pmfToMeasure P₂ (fun a => (hP₂_pos a).le) hP₂_sum))
            (⋃ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
              typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal)) atTop := by
  set μ₂ := pmfToMeasure P₂ (fun a => (hP₂_pos a).le) hP₂_sum with hμ₂
  have hμ₂_pos : ∀ a : α, 0 < μ₂.real {a} := fun a => by
    rw [hμ₂, pmfToMeasure_real_singleton]; exact hP₂_pos a
  set Pε := Qstar_perturb Qstar P₁ ε with hPε
  -- Pε is a full-support pmf.
  have hPε_sum : ∑ a, Pε a = 1 := Qstar_perturb_sum hQs_sum hP₁_sum ε
  have hPε_full : ∀ a, 0 < Pε a := by
    intro a
    rw [hPε]; unfold Qstar_perturb
    have h1 : 0 ≤ (1 - ε) * Qstar a := mul_nonneg (by linarith) (hQs_nn a)
    have h2 : 0 < ε * P₁ a := mul_pos hε0 (hP₁_pos a)
    linarith
  have hPε_nn : ∀ a, 0 ≤ Pε a := fun a => (hPε_full a).le
  -- Strict interior.
  have h_strict : klDivPmf Pε P₁ < r :=
    klDivPmf_perturb_lt P₁ hP₁_pos hP₁_sum hQs_sum hQs_nn h_r_pos h_le hε0 hε1
  -- Eventual membership of the rounded type of Pε (genuine, strict).
  have h_inE : ∀ᶠ n : ℕ in atTop,
      roundedTypeIndex Pε n ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r :=
    roundedTypeIndex_mem_E_r_eventually P₁ hP₁_pos hP₁_sum hPε_sum hPε_nn h_strict
  -- Sanov pointwise lower bound for Pε.
  have h_lb := sanov_ldp_lower_bound_pointwise μ₂ hμ₂_pos Pε hPε_sum hPε_full
    (fun n => E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r) h_inE
  -- Bridge klDivSumForm_ofVec Pε (μ₂.real ∘ ·) = klDivPmf Pε P₂.
  have h_bridge : klDivSumForm_ofVec Pε (fun a => μ₂.real {a}) = klDivPmf Pε P₂ := by
    rw [klDivSumForm_ofVec, klDivPmf_eq_log_diff_sum_of_Q_pos hPε_nn hPε_sum hP₂_sum hP₂_pos]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hμ₂, pmfToMeasure_real_singleton]
  rw [h_bridge] at h_lb
  exact h_lb

/-! ## Phase 6 — headline

The Sanov two-sided collapse (`sanov_ldp_equality`), the minimizer premise
(`hoeffding_exp_minimizer`), the KL bridges, the `Qstar` extraction
(`exists_hoeffding_minimizer_full_support`) and the sign flip are all genuine and
discharged below. The single residual gap is **L-EXP-IN** (plan judgement log #1,
Phase 2 §撤退条件): the interior minimizer `Qstar` lies on the *active* boundary
`klDivPmf Qstar P₁ = r` (the tilt's constraint is an equality, see
`HoeffdingLagrangeIVTBody.lean:161`), so the rounded type
`roundedTypeIndex Qstar n` converges to the closed-sublevel *boundary* and is not
provably eventually inside `E_r n = {klDivIndex ≤ r}`. Enlarging `E_r` with a
rounding margin restores achievability but breaks `hoeffding_exp_minimizer`
(a margin point may beat `Qstar`), so the two requirements genuinely conflict at
the active constraint. This is the one honest LDP-plumbing hypothesis
`h_in_E`. -/

/-- **Hoeffding tradeoff at the exponential level** (interior), **full genuine
closure — hypothesis-free**.

The single remaining honest hypothesis `h_in_E` of the prior version (the
**L-EXP-IN** gap: the realizing minimizer `Qstar` sits on the *active* boundary
`klDivPmf Qstar P₁ = r`, so its rounded type straddles the closed sublevel set
`E_r n = {klDivIndex ≤ r}`) is now discharged by a **perturbation argument**.
Pushing `Qstar` slightly toward `P₁` (`Qstar_perturb`) lands strictly inside the
constraint (`klDivPmf_perturb_lt`, by convexity of `klDivPmf · P₁` and
`klDivPmf P₁ P₁ = 0`), restoring the genuine strict-interior eventual membership
(`roundedTypeIndex_mem_E_r_eventually`). The achievability (`liminf`) bound is
proven per-perturbation (`hoeffding_exp_liminf_perturb`) and the perturbation is
removed by ε→0 continuity (`klDivPmf_perturb_tendsto`). The converse (`limsup`)
bound uses `sanov_ldp_upper_bound`, which needs only the minimizer premise (no
`h_in_E`); its positivity witness is supplied by the same perturbed sequence. -/
@[entry_point]
theorem hoeffding_tradeoff_exp
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {r : ℝ} (h_r_pos : 0 < r) (_h_r_lt : r < klDivPmf P₂ P₁) :
    Tendsto (fun n : ℕ => -((1 : ℝ) / n) * Real.log
        (steinTypeII_exp P₁ P₂ (fun a => (hP₁_pos a).le) hP₁_sum
          (fun a => (hP₂_pos a).le) hP₂_sum n r))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ r)) := by
  classical
  set μ₂ := pmfToMeasure P₂ (fun a => (hP₂_pos a).le) hP₂_sum with hμ₂
  -- Phase 5: extract the constructive full-support minimizer Qstar.
  obtain ⟨Qstar, hQs_mem, hQs_min, hQs_pos⟩ :=
    exists_hoeffding_minimizer_full_support P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
      h_r_pos.le
  have hQs_sum : ∑ a, Qstar a = 1 := hQs_mem.1.2
  have hQs_nn : ∀ a, 0 ≤ Qstar a := fun a => (hQs_pos a).le
  have hQs_le : klDivPmf Qstar P₁ ≤ r := hQs_mem.2
  have hμ₂_pos : ∀ a : α, 0 < μ₂.real {a} := fun a => by
    rw [hμ₂, pmfToMeasure_real_singleton]; exact hP₂_pos a
  -- Abbreviations: D (the exponent) and f (the rate, before sign flip).
  set D : ℝ := klDivPmf Qstar P₂ with hD
  set f : ℕ → ℝ := fun n => (1 / (n : ℝ)) * Real.log
    (((Measure.pi (fun _ : Fin n => μ₂))
      (⋃ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
        typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) with hf
  -- The minimizer premise (no h_in_E), bridged to the value D.
  have h_minim := hoeffding_exp_minimizer P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
    h_r_pos hQs_mem hQs_pos hQs_min
  have h_lhs_bridge :
      klDivSumForm_ofVec Qstar (fun a => μ₂.real {a}) = D := by
    rw [hD, klDivSumForm_ofVec,
      klDivPmf_eq_log_diff_sum_of_Q_pos hQs_nn hQs_sum hP₂_sum hP₂_pos]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hμ₂, pmfToMeasure_real_singleton]
  rw [h_lhs_bridge] at h_minim
  -- h_minim : ∀ n, ∀ c ∈ E_r n, D ≤ klDivIndex c n μ₂
  -- ===== Achievability: -D ≤ liminf f (perturbation + ε→0) =====
  have h_liminf : -D ≤ liminf f atTop := by
    -- For all ε ∈ (0,1): -klDivPmf Qstar_ε P₂ ≤ liminf f.
    have h_event : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        -klDivPmf (Qstar_perturb Qstar P₁ ε) P₂ ≤ liminf f atTop := by
      have h_lt1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by norm_num))
      have h_pos : ∀ᶠ ε : ℝ in 𝓝[>] 0, (0 : ℝ) < ε := eventually_mem_nhdsWithin.mono
        (fun ε hε => hε)
      filter_upwards [h_lt1, h_pos] with ε hε1 hε0
      exact hoeffding_exp_liminf_perturb P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
        h_r_pos hQs_sum hQs_nn hQs_le hε0 hε1
    -- ε→0 continuity: -klDivPmf Qstar_ε P₂ → -D.
    have h_tendsto :
        Tendsto (fun ε : ℝ => -klDivPmf (Qstar_perturb Qstar P₁ ε) P₂)
          (𝓝[>] 0) (𝓝 (-D)) :=
      (klDivPmf_perturb_tendsto P₁ P₂ hP₂_pos).neg
    exact le_of_tendsto h_tendsto h_event
  -- ===== Converse: limsup f ≤ -D (sanov upper bound, h_in_E-free) =====
  -- positivity witness: the perturbed sequence's rounded type is eventually in E_r.
  have h_inE_perturb : ∀ᶠ n : ℕ in atTop,
      roundedTypeIndex (Qstar_perturb Qstar P₁ (1/2)) n
        ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r := by
    have hP_sum : ∑ a, Qstar_perturb Qstar P₁ (1/2) a = 1 :=
      Qstar_perturb_sum hQs_sum hP₁_sum (1/2)
    have hP_nn : ∀ a, 0 ≤ Qstar_perturb Qstar P₁ (1/2) a :=
      Qstar_perturb_nonneg hQs_nn (fun a => (hP₁_pos a).le) (by norm_num) (by norm_num)
    have hP_strict : klDivPmf (Qstar_perturb Qstar P₁ (1/2)) P₁ < r :=
      klDivPmf_perturb_lt P₁ hP₁_pos hP₁_sum hQs_sum hQs_nn h_r_pos hQs_le
        (by norm_num) (by norm_num)
    exact roundedTypeIndex_mem_E_r_eventually P₁ hP₁_pos hP₁_sum hP_sum hP_nn hP_strict
  have h_meas_pos : ∀ᶠ n : ℕ in atTop, 0 < n ∧
      0 < ((Measure.pi (fun _ : Fin n => μ₂))
        (⋃ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
          typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal := by
    have h_n_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    have hP_sum : ∑ a, Qstar_perturb Qstar P₁ (1/2) a = 1 :=
      Qstar_perturb_sum hQs_sum hP₁_sum (1/2)
    have hP_nn : ∀ a, 0 ≤ Qstar_perturb Qstar P₁ (1/2) a :=
      Qstar_perturb_nonneg hQs_nn (fun a => (hP₁_pos a).le) (by norm_num) (by norm_num)
    filter_upwards [h_n_pos, h_inE_perturb] with n hn_pos h_inE
    refine ⟨hn_pos, ?_⟩
    -- some accepted type T_c is nonempty ⇒ its singleton has positive μ₂^n mass.
    obtain ⟨x, hx⟩ := typeClassByCount_nonempty_of_sum
      (fun a => (roundedTypeIndex (Qstar_perturb Qstar P₁ (1/2)) n a : ℕ))
      (roundedTypeIndex_sum (Qstar_perturb Qstar P₁ (1/2)) hP_sum hP_nn n hn_pos)
    have hx_in : x ∈ ⋃ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
        typeClassByCount (α := α) (fun a => (c a : ℕ)) := by
      simp only [Set.mem_iUnion]
      exact ⟨roundedTypeIndex (Qstar_perturb Qstar P₁ (1/2)) n, h_inE, hx⟩
    have h_sing_pos : (0 : ℝ) < ((Measure.pi (fun _ : Fin n => μ₂)) {x}).toReal := by
      rw [Measure.pi_singleton, ENNReal.toReal_prod]
      exact Finset.prod_pos (fun i _ => hμ₂_pos (x i))
    have h_sing_le : ((Measure.pi (fun _ : Fin n => μ₂)) {x}).toReal
        ≤ ((Measure.pi (fun _ : Fin n => μ₂))
          (⋃ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
            typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal := by
      apply ENNReal.toReal_mono
      · exact measure_ne_top _ _
      · exact measure_mono (Set.singleton_subset_iff.mpr hx_in)
    linarith
  -- upper-bound event: ∀ ε > 0, eventually f n ≤ -D + ε (sanov upper bound, h_in_E-free).
  have h_upper_event : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, f n ≤ -D + ε := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := sanov_ldp_upper_bound μ₂ hμ₂_pos
      (fun n => E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r) D h_minim hε
    have h_n_ge : ∀ᶠ n : ℕ in atTop, N₀ ≤ n :=
      Filter.eventually_atTop.mpr ⟨N₀, fun n hn => hn⟩
    filter_upwards [h_n_ge, h_meas_pos] with n hn_ge h_npos_meas
    obtain ⟨hn_pos, h_union_pos⟩ := h_npos_meas
    exact hN₀ n hn_ge hn_pos h_union_pos
  -- ===== Boundedness for the sandwich =====
  have h_bdd_above : Filter.IsBoundedUnder (· ≤ ·) atTop f := by
    refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    have h_n_pos : ∀ᶠ n : ℕ in atTop, 0 < n :=
      Filter.eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    filter_upwards [h_n_pos] with n hn_pos
    show f n ≤ 0
    rw [hf]
    have h_le_one : ((Measure.pi (fun _ : Fin n => μ₂))
        (⋃ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
          typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal ≤ 1 := by
      have := MeasureTheory.measureReal_le_one (μ := Measure.pi (fun _ : Fin n => μ₂))
        (s := ⋃ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
          typeClassByCount (α := α) (fun a => (c a : ℕ)))
      simpa [MeasureTheory.measureReal_def] using this
    have h_log_le : Real.log _ ≤ 0 := Real.log_nonpos ENNReal.toReal_nonneg h_le_one
    have h_one_div_nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos h_one_div_nn h_log_le
  have h_bdd_below : Filter.IsBoundedUnder (· ≥ ·) atTop f := by
    -- m := min_a μ₂.real {a} > 0; μ₂^n(⋃) ≥ μ₂^n({x}) ≥ m^n ⇒ f n ≥ log m.
    obtain ⟨a₀, _, ha₀⟩ := Finset.exists_min_image (s := (Finset.univ : Finset α))
      (f := fun a => μ₂.real {a}) ⟨Classical.choice inferInstance, Finset.mem_univ _⟩
    set m : ℝ := μ₂.real {a₀} with hm
    have hm_pos : 0 < m := hμ₂_pos a₀
    refine ⟨Real.log m, ?_⟩
    rw [Filter.eventually_map]
    have hP_sum : ∑ a, Qstar_perturb Qstar P₁ (1/2) a = 1 :=
      Qstar_perturb_sum hQs_sum hP₁_sum (1/2)
    have hP_nn : ∀ a, 0 ≤ Qstar_perturb Qstar P₁ (1/2) a :=
      Qstar_perturb_nonneg hQs_nn (fun a => (hP₁_pos a).le) (by norm_num) (by norm_num)
    filter_upwards [h_meas_pos, h_inE_perturb] with n h_npos_meas h_inE
    obtain ⟨hn_pos, h_union_pos⟩ := h_npos_meas
    show Real.log m ≤ f n
    rw [hf]
    -- a witness type for nonemptiness, giving μ₂^n({x}) ≥ m^n.
    obtain ⟨x, hx⟩ := typeClassByCount_nonempty_of_sum
      (fun a => (roundedTypeIndex (Qstar_perturb Qstar P₁ (1/2)) n a : ℕ))
      (roundedTypeIndex_sum (Qstar_perturb Qstar P₁ (1/2)) hP_sum hP_nn n hn_pos)
    have hx_in : x ∈ ⋃ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
        typeClassByCount (α := α) (fun a => (c a : ℕ)) := by
      simp only [Set.mem_iUnion]
      exact ⟨roundedTypeIndex (Qstar_perturb Qstar P₁ (1/2)) n, h_inE, hx⟩
    have h_sing_ge : m ^ n ≤ ((Measure.pi (fun _ : Fin n => μ₂)) {x}).toReal := by
      rw [Measure.pi_singleton, ENNReal.toReal_prod]
      calc m ^ n = ∏ _i : Fin n, m := by rw [Finset.prod_const]; simp
        _ ≤ ∏ i : Fin n, μ₂.real {x i} :=
          Finset.prod_le_prod (fun i _ => hm_pos.le)
            (fun i _ => ha₀ (x i) (Finset.mem_univ _))
    have h_sing_le : ((Measure.pi (fun _ : Fin n => μ₂)) {x}).toReal
        ≤ ((Measure.pi (fun _ : Fin n => μ₂))
          (⋃ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
            typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal := by
      apply ENNReal.toReal_mono
      · exact measure_ne_top _ _
      · exact measure_mono (Set.singleton_subset_iff.mpr hx_in)
    have h_union_ge : m ^ n ≤ ((Measure.pi (fun _ : Fin n => μ₂))
        (⋃ c ∈ E_r P₁ (fun a => (hP₁_pos a).le) hP₁_sum n r,
          typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal :=
      le_trans h_sing_ge h_sing_le
    have h_pow_pos : (0 : ℝ) < m ^ n := pow_pos hm_pos _
    have h_log_pow_le := Real.log_le_log h_pow_pos h_union_ge
    rw [Real.log_pow] at h_log_pow_le
    have h_n_inv_pos : 0 < 1 / (n : ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left h_log_pow_le h_n_inv_pos.le
    rwa [show (1 / (n : ℝ)) * ((n : ℝ) * Real.log m) = Real.log m by field_simp] at h
  -- ===== Converse limsup: from h_upper_event (∀ ε, eventually ≤ -D+ε) + cobounded. =====
  have h_limsup : limsup f atTop ≤ -D := by
    have h_cobdd : Filter.IsCoboundedUnder (· ≤ ·) atTop f :=
      h_bdd_below.isCoboundedUnder_flip
    by_contra h_lt
    push Not at h_lt
    set ε := (limsup f atTop - (-D)) / 2 with hε_def
    have hε_pos : 0 < ε := by rw [hε_def]; linarith
    have h_ub : limsup f atTop ≤ -D + ε :=
      Filter.limsup_le_of_le h_cobdd (h_upper_event ε hε_pos)
    rw [hε_def] at h_ub
    linarith
  -- ===== Assemble: Tendsto f → -D, then sign flip to hoeffdingE2 =====
  have h_tendsto_f : Tendsto f atTop (𝓝 (-D)) :=
    tendsto_of_le_liminf_of_limsup_le h_liminf h_limsup h_bdd_above h_bdd_below
  -- f = (1/n) log (steinTypeII_exp) definitionally; the headline is -f → hoeffdingE2.
  have h_neg := h_tendsto_f.neg
  rw [neg_neg] at h_neg
  rw [show hoeffdingE2 P₁ P₂ r = D from hQs_min]
  refine h_neg.congr (fun n => ?_)
  simp only [hf, steinTypeII_exp]
  ring

end InformationTheory.Shannon.HoeffdingTradeoffExp
