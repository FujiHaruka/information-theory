import InformationTheory.Meta.EntryPoint
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact

/-!
# Csiszár I-projection and the Pythagorean inequality

For a finite alphabet `α`, a full-support reference pmf `Q : α → ℝ`, and a closed convex
set `K ⊆ stdSimplex ℝ α`:

- **Existence**: there is `Q* ∈ K` minimizing `klDivPmf · Q` over `K`.
- **Uniqueness**: the minimizer is unique.
- **Pythagorean inequality** (Cover-Thomas 11.6.1): for all `P ∈ K`,
  `klDivPmf P Q ≥ klDivPmf P Q* + klDivPmf Q* Q`.

## Main definitions

* `klDivPmf P Q := ∑ a, Q a * klFun (P a / Q a)` — real-valued finite-alphabet KL divergence.

## Main statements

* `csiszar_projection_exists` — existence via extreme value theorem.
* `csiszar_projection_unique` — uniqueness via strict convexity.
* `csiszar_pythagoras_inequality` — Pythagorean inequality via the first-order condition.

## Implementation notes

Proof strategy for the Pythagorean inequality: the first-order condition
`∑ (P - Q*)(log Q* - log Q) ≥ 0` is derived from the right derivative of
`t ↦ klDivPmf ((1-t)Q* + tP) Q` at `t = 0` being non-negative (minimality of `Q*`).
Combined with the algebraic identity
`klDivPmf P Q = klDivPmf P Q* + ∑ P·(log Q* - log Q)` and the expansion of
`klDivPmf Q* Q`, this gives the inequality.
-/

namespace InformationTheory.Shannon.CsiszarProjection

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter
open scoped BigOperators Topology

variable {α : Type*} [Fintype α]

/-! ## `klDivPmf`: definition, non-negativity, continuity, and strict convexity -/

/-- **Real-valued finite-alphabet KL divergence** as a pmf functional:
`klDivPmf P Q := ∑ a, Q a * klFun (P a / Q a)` where
`klFun x = x * log x + 1 - x` (Mathlib `InformationTheory.klFun`).

Equivalent to `(klDiv P Q).toReal` under support hypotheses (bridge in `Sanov.lean`),
but we work Real-only here to leverage `strictConvexOn_klFun` + finite-sum API directly. -/
noncomputable def klDivPmf (P Q : α → ℝ) : ℝ :=
  ∑ a : α, Q a * klFun (P a / Q a)

/-- `klDivPmf` is non-negative on the simplex when Q is a pmf (full support not required:
each summand is `Q a * klFun (P a / Q a) ≥ 0` whenever `Q a ≥ 0`, since `klFun` ≥ 0 on `[0, ∞)`
and `P a / Q a ≥ 0` follows from `P a ≥ 0` and `Q a ≥ 0`). -/
lemma klDivPmf_nonneg (P Q : α → ℝ)
    (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) :
    0 ≤ klDivPmf P Q := by
  unfold klDivPmf
  refine Finset.sum_nonneg fun a _ => ?_
  have h_ratio_nn : 0 ≤ P a / Q a := div_nonneg (hP a) (hQ a)
  exact mul_nonneg (hQ a) (klFun_nonneg h_ratio_nn)

/-- `klFun` is continuous on `[0, ∞)` (Mathlib `continuous_klFun`). The composition
`fun P => klFun (P a / Q a)` is continuous in P when `Q a > 0`. -/
lemma continuous_klDivPmf_left (Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) :
    Continuous (fun P : α → ℝ => klDivPmf P Q) := by
  unfold klDivPmf
  refine continuous_finsetSum _ fun a _ => ?_
  -- (Q a) * klFun ((P a) / (Q a)) : continuous in P.
  have hQne : Q a ≠ 0 := (hQ_pos a).ne'
  have h_apply : Continuous (fun P : α → ℝ => P a) := continuous_apply a
  have h_div : Continuous (fun P : α → ℝ => P a / Q a) :=
    h_apply.div_const (Q a)
  have h_kl : Continuous (fun P : α → ℝ => klFun (P a / Q a)) :=
    continuous_klFun.comp h_div
  exact h_kl.const_mul (Q a)

/-- `klDivPmf · Q` is strictly convex on `stdSimplex ℝ α` (full support Q + Π ⊆ simplex).

Per-coordinate: `klFun` is strictly convex on `[0, ∞)` (`strictConvexOn_klFun`).
The map `P ↦ P a / Q a` is affine (when `Q a > 0` is fixed), and `Q a * (·)` preserves
strict convexity. Sum of strictly convex (in at least one coordinate where `P ≠ P'`)
gives strict convexity of the sum.

(But care: if `P = P'` they agree in every coordinate; if `P ≠ P'` then there is at least
one coordinate `a` where `P a ≠ P' a`, and at that coordinate `klFun` strict convexity fires.) -/
lemma klDivPmf_strictConvexOn_left (Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) :
    StrictConvexOn ℝ (stdSimplex ℝ α) (fun P : α → ℝ => klDivPmf P Q) := by
  refine ⟨convex_stdSimplex ℝ α, ?_⟩
  intro P hP P' hP' hne s t hs ht hst
  -- We need: klDivPmf (s • P + t • P') Q < s * klDivPmf P Q + t * klDivPmf P' Q
  -- Strategy: ∃ a₀, P a₀ ≠ P' a₀ (since P ≠ P'). At that a₀, klFun strict convexity fires.
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, P a₀ ≠ P' a₀ := by
    by_contra h_all_eq
    apply hne
    funext a
    exact not_not.mp (fun hne_a => h_all_eq ⟨a, hne_a⟩)
  -- Per-coordinate ratios: P a / Q a ∈ Ici 0 (since hP.1, hQ_pos).
  have h_ratio_nn : ∀ a, 0 ≤ P a / Q a := fun a => div_nonneg (hP.1 a) (hQ_pos a).le
  have h_ratio_nn' : ∀ a, 0 ≤ P' a / Q a := fun a => div_nonneg (hP'.1 a) (hQ_pos a).le
  -- per-coordinate convexity of klFun on [0,∞)
  have h_ratio_combo : ∀ a : α,
      (s • P + t • P') a / Q a = s * (P a / Q a) + t * (P' a / Q a) := by
    intro a
    have hQne : Q a ≠ 0 := (hQ_pos a).ne'
    have h_apply : (s • P + t • P') a = s * P a + t * P' a := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h_apply]
    field_simp
  have h_per : ∀ a : α,
      klFun ((s • P + t • P') a / Q a)
        ≤ s * klFun (P a / Q a) + t * klFun (P' a / Q a) := by
    intro a
    rw [h_ratio_combo a]
    have h_conv := convexOn_klFun.2 (h_ratio_nn a) (h_ratio_nn' a) hs.le ht.le hst
    simpa [smul_eq_mul] using h_conv
  have h_ratio_ne : P a₀ / Q a₀ ≠ P' a₀ / Q a₀ := by
    intro h_eq_ratio
    have hQne : Q a₀ ≠ 0 := (hQ_pos a₀).ne'
    apply ha₀
    have := congrArg (· * Q a₀) h_eq_ratio
    simp only at this
    field_simp at this
    exact this
  have h_strict_a₀ :
      klFun ((s • P + t • P') a₀ / Q a₀)
        < s * klFun (P a₀ / Q a₀) + t * klFun (P' a₀ / Q a₀) := by
    rw [h_ratio_combo a₀]
    have h_strict := strictConvexOn_klFun.2 (h_ratio_nn a₀) (h_ratio_nn' a₀)
      h_ratio_ne hs ht hst
    simpa [smul_eq_mul] using h_strict
  -- Multiply by Q a (positive) and sum.
  -- klDivPmf (s • P + t • P') Q = ∑ a, Q a * klFun ((s • P + t • P') a / Q a)
  -- ≤ ∑ a, Q a * (s * klFun(P a / Q a) + t * klFun(P' a / Q a))
  -- with strict at a₀.
  unfold klDivPmf
  show ∑ a, Q a * klFun ((s • P + t • P') a / Q a)
    < s • ∑ a, Q a * klFun (P a / Q a) + t • ∑ a, Q a * klFun (P' a / Q a)
  have h_total :
      ∑ a, Q a * klFun ((s • P + t • P') a / Q a)
        < ∑ a, Q a * (s * klFun (P a / Q a) + t * klFun (P' a / Q a)) := by
    refine Finset.sum_lt_sum (fun a _ => ?_) ⟨a₀, Finset.mem_univ _, ?_⟩
    · exact mul_le_mul_of_nonneg_left (h_per a) (hQ_pos a).le
    · exact mul_lt_mul_of_pos_left h_strict_a₀ (hQ_pos a₀)
  have h_split : ∑ a, Q a * (s * klFun (P a / Q a) + t * klFun (P' a / Q a))
      = s * ∑ a, Q a * klFun (P a / Q a) + t * ∑ a, Q a * klFun (P' a / Q a) := by
    have : ∑ a, Q a * (s * klFun (P a / Q a) + t * klFun (P' a / Q a))
        = ∑ a, (s * (Q a * klFun (P a / Q a)) + t * (Q a * klFun (P' a / Q a))) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [smul_eq_mul, smul_eq_mul]
  linarith

/-! ## Existence via extreme value theorem -/

lemma isCompact_of_subset_stdSimplex {K : Set (α → ℝ)}
    (hK_closed : IsClosed K) (hK_sub : K ⊆ stdSimplex ℝ α) :
    IsCompact K :=
  IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ α) hK_closed hK_sub

/-- **Existence** (Cover-Thomas 11.6.1 a): for a nonempty closed set `K ⊆ stdSimplex ℝ α` and
full-support `Q`, there exists `Q* ∈ K` minimizing `klDivPmf · Q` over `K`. -/
@[entry_point]
theorem csiszar_projection_exists {K : Set (α → ℝ)} {Q : α → ℝ}
    (hK_closed : IsClosed K)
    (hK_sub : K ⊆ stdSimplex ℝ α)
    (hK_ne : K.Nonempty)
    (hQ_pos : ∀ a, 0 < Q a) :
    ∃ Qstar ∈ K, IsMinOn (fun P => klDivPmf P Q) K Qstar := by
  have hK_compact : IsCompact K := isCompact_of_subset_stdSimplex hK_closed hK_sub
  have h_cont : Continuous (fun P : α → ℝ => klDivPmf P Q) :=
    continuous_klDivPmf_left Q hQ_pos
  exact hK_compact.exists_isMinOn hK_ne h_cont.continuousOn

/-! ## Uniqueness via strict convexity -/

/-- **Uniqueness** (Cover-Thomas 11.6.1 b): the minimizer of `klDivPmf · Q` on a convex
`K ⊆ stdSimplex ℝ α` is unique. -/
@[entry_point]
theorem csiszar_projection_unique {K : Set (α → ℝ)} {Q : α → ℝ}
    (hK_conv : Convex ℝ K)
    (hK_sub : K ⊆ stdSimplex ℝ α)
    (hQ_pos : ∀ a, 0 < Q a)
    {Qstar Qstar' : α → ℝ}
    (hQs : Qstar ∈ K) (hQs' : Qstar' ∈ K)
    (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar)
    (hmin' : IsMinOn (fun P => klDivPmf P Q) K Qstar') :
    Qstar = Qstar' := by
  by_contra hne
  -- The two minimizers have the same value (each is ≤ the other).
  have hval_eq : klDivPmf Qstar Q = klDivPmf Qstar' Q := by
    have h1 : klDivPmf Qstar Q ≤ klDivPmf Qstar' Q := hmin hQs'
    have h2 : klDivPmf Qstar' Q ≤ klDivPmf Qstar Q := hmin' hQs
    linarith
  -- Midpoint Pm := (1/2) • Qstar + (1/2) • Qstar' is in K (convex).
  set Pm : α → ℝ := (1/2 : ℝ) • Qstar + (1/2 : ℝ) • Qstar' with hPm_def
  have hPm_mem : Pm ∈ K := by
    have h_half_nn : (0 : ℝ) ≤ 1/2 := by norm_num
    have h_sum : (1/2 : ℝ) + 1/2 = 1 := by norm_num
    exact hK_conv hQs hQs' h_half_nn h_half_nn h_sum
  -- By strict convexity of klDivPmf, klDivPmf Pm Q < (1/2)*klDivPmf Qstar Q + (1/2)*klDivPmf Qstar' Q
  -- = klDivPmf Qstar Q.
  have hsc := klDivPmf_strictConvexOn_left Q hQ_pos
  have h_half_pos : (0 : ℝ) < 1/2 := by norm_num
  have h_sum : (1/2 : ℝ) + 1/2 = 1 := by norm_num
  have h_strict := hsc.2 (hK_sub hQs) (hK_sub hQs') hne h_half_pos h_half_pos h_sum
  -- h_strict : klDivPmf Pm Q < (1/2) • klDivPmf Qstar Q + (1/2) • klDivPmf Qstar' Q
  simp only [smul_eq_mul] at h_strict
  -- Minimality: klDivPmf Qstar Q ≤ klDivPmf Pm Q.
  have h_min : klDivPmf Qstar Q ≤ klDivPmf Pm Q := hmin hPm_mem
  show False
  have h_avg : (1/2 : ℝ) * klDivPmf Qstar Q + (1/2 : ℝ) * klDivPmf Qstar' Q
      = klDivPmf Qstar Q := by rw [← hval_eq]; ring
  -- h_strict (beta-reduced) gives klDivPmf Pm Q < klDivPmf Qstar Q, contradicting h_min.
  have h_strict' : klDivPmf Pm Q
      < (1/2 : ℝ) * klDivPmf Qstar Q + (1/2 : ℝ) * klDivPmf Qstar' Q := h_strict
  linarith

/-! ## Pythagorean inequality -/

/-- **Standard sum form** for `klDivPmf` under probability measure hypotheses:
`klDivPmf P Q = ∑ a, P a * (log (P a) - log (Q a))` when `∑ P = ∑ Q = 1` and both
positive. (`klFun(t) = t log t + 1 - t` ⟹ `Q * klFun(P/Q) = P log(P/Q) + Q - P`,
sum collapses 1 - 1 = 0.) -/
lemma klDivPmf_eq_log_diff_sum
    {P Q : α → ℝ}
    (hP_sum : ∑ a, P a = 1)
    (hQ_sum : ∑ a, Q a = 1)
    (hP_pos : ∀ a, 0 < P a)
    (hQ_pos : ∀ a, 0 < Q a) :
    klDivPmf P Q = ∑ a : α, P a * (Real.log (P a) - Real.log (Q a)) := by
  unfold klDivPmf
  -- per term: Q a * klFun (P a / Q a) = P a * log (P a / Q a) + Q a - P a
  --         = P a * (log (P a) - log (Q a)) + Q a - P a
  have h_term : ∀ a : α,
      Q a * klFun (P a / Q a) = P a * (Real.log (P a) - Real.log (Q a)) + (Q a - P a) := by
    intro a
    have hQne : Q a ≠ 0 := (hQ_pos a).ne'
    have h_ratio_pos : 0 < P a / Q a := div_pos (hP_pos a) (hQ_pos a)
    have h_log_div : Real.log (P a / Q a) = Real.log (P a) - Real.log (Q a) :=
      Real.log_div (hP_pos a).ne' hQne
    unfold klFun
    -- Q a * ((P a / Q a) * log (P a / Q a) + 1 - P a / Q a)
    -- = (P a) * log (P a / Q a) + Q a - P a
    rw [h_log_div]
    field_simp
    ring
  simp_rw [h_term]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hQ_sum, hP_sum]
  ring

/-- Algebraic identity: for full-support `P, Q*, Q`,
`klDivPmf P Q = klDivPmf P Q* + ∑ a, P a * (log (Q* a) - log (Q a))`. -/
lemma klDivPmf_decomp_via_intermediate
    {P Qstar Q : α → ℝ}
    (hP_sum : ∑ a, P a = 1)
    (hQs_sum : ∑ a, Qstar a = 1)
    (hQ_sum : ∑ a, Q a = 1)
    (hP_pos : ∀ a, 0 < P a)
    (hQs_pos : ∀ a, 0 < Qstar a)
    (hQ_pos : ∀ a, 0 < Q a) :
    klDivPmf P Q
      = klDivPmf P Qstar + ∑ a : α, P a * (Real.log (Qstar a) - Real.log (Q a)) := by
  rw [klDivPmf_eq_log_diff_sum hP_sum hQ_sum hP_pos hQ_pos,
      klDivPmf_eq_log_diff_sum hP_sum hQs_sum hP_pos hQs_pos]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Expansion of `klDivPmf Q* Q` in log-ratio form:
`klDivPmf Q* Q = ∑ a, Q* a * (log (Q* a) - log (Q a))`. -/
lemma klDivPmf_self_expand
    {Qstar Q : α → ℝ}
    (hQs_sum : ∑ a, Qstar a = 1)
    (hQ_sum : ∑ a, Q a = 1)
    (hQs_pos : ∀ a, 0 < Qstar a)
    (hQ_pos : ∀ a, 0 < Q a) :
    klDivPmf Qstar Q
      = ∑ a : α, Qstar a * (Real.log (Qstar a) - Real.log (Q a)) :=
  klDivPmf_eq_log_diff_sum hQs_sum hQ_sum hQs_pos hQ_pos

/-- Derivative of the segment functional `t ↦ klDivPmf ((1-t) • Qstar + t • P) Q` at `t = 0`,
equal to `∑ a, (P a - Qstar a) * (log (Qstar a) - log (Q a))`. -/
lemma csiszar_segment_hasDerivAt
    {Q Qstar P : α → ℝ} (hQ_pos : ∀ a, 0 < Q a) (hQs_pos : ∀ a, 0 < Qstar a) :
    HasDerivAt (fun t : ℝ => klDivPmf ((1 - t) • Qstar + t • P) Q)
      (∑ a : α, (P a - Qstar a) * (Real.log (Qstar a) - Real.log (Q a))) 0 := by
  classical
  set Pt : ℝ → α → ℝ := fun t => (1 - t) • Qstar + t • P with hPt_def
  -- per-coordinate derivative
  have h_per : ∀ a : α,
      HasDerivAt (fun t : ℝ => Q a * klFun (Pt t a / Q a))
        ((P a - Qstar a) * (Real.log (Qstar a) - Real.log (Q a))) 0 := by
    intro a
    have hQne : Q a ≠ 0 := (hQ_pos a).ne'
    -- g_a t := Pt t a / Q a = Qstar a / Q a + t * ((P a - Qstar a) / Q a).
    have h_g_eq : (fun t : ℝ => Pt t a / Q a)
        = fun t => Qstar a / Q a + t * ((P a - Qstar a) / Q a) := by
      funext t
      have h_apply : Pt t a = (1 - t) * Qstar a + t * P a := by
        simp [hPt_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h_apply]
      field_simp
      ring
    -- HasDerivAt g_a ((P a - Qstar a) / Q a) 0
    have h_g_deriv : HasDerivAt (fun t : ℝ => Pt t a / Q a) ((P a - Qstar a) / Q a) 0 := by
      rw [h_g_eq]
      have h1 : HasDerivAt (fun t : ℝ => t * ((P a - Qstar a) / Q a))
          ((P a - Qstar a) / Q a) 0 := by
        have := (hasDerivAt_id (0 : ℝ)).mul_const ((P a - Qstar a) / Q a)
        simpa using this
      have h2 : HasDerivAt (fun t : ℝ => Qstar a / Q a + t * ((P a - Qstar a) / Q a))
          ((P a - Qstar a) / Q a) 0 := by
        have := h1.const_add (Qstar a / Q a)
        simpa using this
      exact h2
    -- g_a 0 = Qstar a / Q a (positive).
    have h_g0 : Pt 0 a / Q a = Qstar a / Q a := by
      have h_apply : Pt 0 a = Qstar a := by
        simp [hPt_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h_apply]
    have h_g0_pos : 0 < Qstar a / Q a := div_pos (hQs_pos a) (hQ_pos a)
    -- klFun has derivative log at Qstar a / Q a.
    have h_klfun_deriv : HasDerivAt klFun (Real.log (Qstar a / Q a)) (Qstar a / Q a) :=
      hasDerivAt_klFun h_g0_pos.ne'
    -- Need klFun at (Pt 0 a / Q a) which equals Qstar a / Q a.
    have h_klfun_deriv' : HasDerivAt klFun (Real.log (Qstar a / Q a))
        ((fun t : ℝ => Pt t a / Q a) 0) := by
      show HasDerivAt klFun (Real.log (Qstar a / Q a)) (Pt 0 a / Q a)
      rw [h_g0]
      exact h_klfun_deriv
    -- Chain rule (klFun ∘ g_a) has derivative log(g 0) * g'(0).
    have h_kl_deriv : HasDerivAt (fun t : ℝ => klFun (Pt t a / Q a))
        (Real.log (Qstar a / Q a) * ((P a - Qstar a) / Q a)) 0 := by
      have := h_klfun_deriv'.comp (0 : ℝ) h_g_deriv
      simpa [Function.comp_def] using this
    -- × Q a (const_mul)
    have h_scaled : HasDerivAt (fun t : ℝ => Q a * klFun (Pt t a / Q a))
        (Q a * (Real.log (Qstar a / Q a) * ((P a - Qstar a) / Q a))) 0 :=
      h_kl_deriv.const_mul (Q a)
    -- Massage the RHS:
    have h_rhs_eq :
        Q a * (Real.log (Qstar a / Q a) * ((P a - Qstar a) / Q a))
          = (P a - Qstar a) * (Real.log (Qstar a) - Real.log (Q a)) := by
      rw [Real.log_div (hQs_pos a).ne' hQne]
      field_simp
    rw [h_rhs_eq] at h_scaled
    exact h_scaled
  -- Sum: HasDerivAt of φ = ∑ … = D
  have h_sum : HasDerivAt (fun t : ℝ => ∑ a : α, Q a * klFun (Pt t a / Q a))
      (∑ a : α, (P a - Qstar a) * (Real.log (Qstar a) - Real.log (Q a))) 0 := by
    have h_sum_fn := HasDerivAt.sum (u := Finset.univ) (𝕜 := ℝ)
      (fun a _ => h_per a)
    have h_fun_eq :
        (fun t : ℝ => ∑ a : α, Q a * klFun (Pt t a / Q a))
          = ∑ a ∈ (Finset.univ : Finset α), fun t : ℝ => Q a * klFun (Pt t a / Q a) := by
      funext t
      simp [Finset.sum_apply]
    rw [h_fun_eq]
    exact h_sum_fn
  -- klDivPmf (Pt t) Q matches the sum (defeq).
  show HasDerivAt (fun t : ℝ => klDivPmf (Pt t) Q)
    (∑ a : α, (P a - Qstar a) * (Real.log (Qstar a) - Real.log (Q a))) 0
  have h_eq : ∀ t : ℝ, klDivPmf (Pt t) Q = ∑ a : α, Q a * klFun (Pt t a / Q a) := by
    intro t; rfl
  simp_rw [h_eq]
  exact h_sum

/-- **First-order condition**: if `Q*` minimizes `klDivPmf · Q` over `K`, then for all `P ∈ K`,
`∑ a, (P a - Q* a) * (log (Q* a) - log (Q a)) ≥ 0`.

Proof: the right derivative of `t ↦ klDivPmf ((1-t)Q* + tP) Q` at `t = 0` equals the sum,
and non-negativity follows from minimality (`φ(0) ≤ φ(t)` for small `t > 0`). -/
lemma csiszar_first_order_condition
    {K : Set (α → ℝ)} {Q : α → ℝ}
    (hK_conv : Convex ℝ K)
    (hQ_pos : ∀ a, 0 < Q a)
    {Qstar : α → ℝ} (hQs : Qstar ∈ K) (hQs_pos : ∀ a, 0 < Qstar a)
    (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar)
    {P : α → ℝ} (hP : P ∈ K) :
    0 ≤ ∑ a : α, (P a - Qstar a) * (Real.log (Qstar a) - Real.log (Q a)) := by
  classical
  -- Segment: Pt t := (1 - t) • Qstar + t • P, with Pt 0 = Qstar.
  set Pt : ℝ → α → ℝ := fun t => (1 - t) • Qstar + t • P with hPt_def
  -- φ t := klDivPmf (Pt t) Q
  set φ : ℝ → ℝ := fun t => klDivPmf (Pt t) Q with hφ_def
  set D : ℝ := ∑ a : α, (P a - Qstar a) * (Real.log (Qstar a) - Real.log (Q a)) with hD_def
  -- Step 1: HasDerivAt φ D 0.
  -- For each a, per-coordinate inner function: g_a (t) := Pt t a / Q a
  --   = ((1 - t) * Qstar a + t * P a) / Q a
  --   = Qstar a / Q a + t * (P a - Qstar a) / Q a.
  -- g_a is affine in t with slope (P a - Qstar a) / Q a and g_a 0 = Qstar a / Q a > 0.
  -- d/dt klFun(g_a t) = log(g_a t) * (P a - Qstar a)/Q a (by `hasDerivAt_klFun` + chain rule).
  -- At t = 0: log(Qstar a / Q a) * (P a - Qstar a)/Q a.
  -- × Q a: log(Qstar a / Q a) * (P a - Qstar a).
  -- Summing: ∑ a, log(Qstar a/Q a)·(P a − Qstar a) = D (by `log_div`).
  have hφ_deriv : HasDerivAt φ D 0 := csiszar_segment_hasDerivAt hQ_pos hQs_pos
  -- Step 2: For t ∈ [0, 1], Pt t ∈ K (by convexity).
  have h_Pt_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, Pt t ∈ K := by
    intro t ht
    have h0 : 0 ≤ 1 - t := by linarith [ht.2]
    have h1 : 0 ≤ t := ht.1
    have hsum : (1 - t) + t = 1 := by ring
    exact hK_conv hQs hP h0 h1 hsum
  -- Step 3: For t ∈ [0, 1], φ t ≥ φ 0 = klDivPmf Qstar Q.
  have h_Pt0 : Pt 0 = Qstar := by
    simp [hPt_def]
  have hφ0 : φ 0 = klDivPmf Qstar Q := by
    show klDivPmf (Pt 0) Q = klDivPmf Qstar Q
    rw [h_Pt0]
  have h_φ_ge : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ 0 ≤ φ t := by
    intro t ht
    rw [hφ0]
    exact hmin (h_Pt_mem t ht)
  -- Step 4: HasDerivAt φ D 0 ⟹ Tendsto (slope φ 0) (𝓝[>] 0) (𝓝 D).
  -- For t ∈ (0, 1], slope φ 0 t = (φ t - φ 0)/t ≥ 0.
  -- So D ≥ 0 by le_of_tendsto.
  have h_slope_tendsto : Tendsto (slope φ 0) (𝓝[>] (0 : ℝ)) (𝓝 D) := by
    have h_lr := (hasDerivAt_iff_tendsto_slope_left_right (𝕜 := ℝ)).mp hφ_deriv
    exact h_lr.2
  have h_slope_nn : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ slope φ 0 t := by
    -- Eventually for t > 0 small, t ≤ 1.
    have h_event : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
      apply mem_nhdsWithin.mpr
      refine ⟨Set.Iio 1, isOpen_Iio, by norm_num, ?_⟩
      intro x hx
      exact ⟨hx.2, le_of_lt hx.1⟩
    filter_upwards [h_event] with t ht
    have ht_pos : 0 < t := ht.1
    have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, ht.2⟩
    rw [slope_def_field]
    have h_num : 0 ≤ φ t - φ 0 := sub_nonneg.mpr (h_φ_ge t ht_mem)
    have h_denom : 0 < t - 0 := by linarith
    exact div_nonneg h_num h_denom.le
  -- Conclude: D ≥ 0.
  have : (0 : ℝ) ≤ D := by
    refine ge_of_tendsto h_slope_tendsto ?_
    exact h_slope_nn
  exact this

/-- **Pythagorean inequality** (Cover-Thomas 11.6.1 c): for the minimizer `Q*` and any `P ∈ K`,
`klDivPmf P Q ≥ klDivPmf P Q* + klDivPmf Q* Q`.

Proof: combine the algebraic identity `klDivPmf P Q = klDivPmf P Q* + ∑ P·(log Q* - log Q)`,
the expansion `klDivPmf Q* Q = ∑ Q*·(log Q* - log Q)`, and the first-order condition
`∑ (P - Q*)·(log Q* - log Q) ≥ 0`. -/
@[entry_point]
theorem csiszar_pythagoras_inequality
    {K : Set (α → ℝ)} {Q : α → ℝ}
    (hK_conv : Convex ℝ K)
    (hK_sub : K ⊆ stdSimplex ℝ α)
    (hQ_sum : ∑ a, Q a = 1)
    (hQ_pos : ∀ a, 0 < Q a)
    {Qstar : α → ℝ} (hQs : Qstar ∈ K) (hQs_pos : ∀ a, 0 < Qstar a)
    (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar)
    {P : α → ℝ} (hP : P ∈ K) (hP_pos : ∀ a, 0 < P a) :
    klDivPmf P Q ≥ klDivPmf P Qstar + klDivPmf Qstar Q := by
  -- Extract simplex membership for P, Qstar.
  have hP_simplex := hK_sub hP
  have hQs_simplex := hK_sub hQs
  have hP_sum : ∑ a, P a = 1 := hP_simplex.2
  have hQs_sum : ∑ a, Qstar a = 1 := hQs_simplex.2
  -- Identity 1: klDivPmf P Q = klDivPmf P Qstar + ∑ P (log Qstar - log Q)
  have h_id1 := klDivPmf_decomp_via_intermediate hP_sum hQs_sum hQ_sum
    hP_pos hQs_pos hQ_pos
  -- Identity 2: klDivPmf Qstar Q = ∑ Qstar (log Qstar - log Q)
  have h_id2 := klDivPmf_self_expand hQs_sum hQ_sum hQs_pos hQ_pos
  -- First-order: ∑ (P - Qstar) (log Qstar - log Q) ≥ 0
  have h_first := csiszar_first_order_condition hK_conv hQ_pos hQs hQs_pos hmin hP
  -- Distribute: ∑ (P - Qstar) (log Qstar - log Q)
  --           = ∑ P (log Qstar - log Q) - ∑ Qstar (log Qstar - log Q)
  --           = ∑ P (log Qstar - log Q) - klDivPmf Qstar Q
  have h_split : ∑ a : α, (P a - Qstar a) * (Real.log (Qstar a) - Real.log (Q a))
      = (∑ a : α, P a * (Real.log (Qstar a) - Real.log (Q a)))
        - (∑ a : α, Qstar a * (Real.log (Qstar a) - Real.log (Q a))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h_split] at h_first
  -- Combine: klDivPmf P Q = klDivPmf P Qstar + (∑ Qstar (log Qstar - log Q) + nonneg)
  --                       = klDivPmf P Qstar + klDivPmf Qstar Q + (nonneg).
  show klDivPmf P Qstar + klDivPmf Qstar Q ≤ klDivPmf P Q
  rw [h_id1, h_id2]
  linarith

end InformationTheory.Shannon.CsiszarProjection
