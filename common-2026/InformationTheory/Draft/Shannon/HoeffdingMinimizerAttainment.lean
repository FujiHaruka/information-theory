import InformationTheory.Draft.Shannon.HoeffdingLagrangeIVTBody
import InformationTheory.Meta.EntryPoint

/-!
# S18 Hoeffding I-projection minimizer attainment — `IsHoeffdingTiltMinimal` discharge

`HoeffdingLagrangeIVTBody.lean` (wave10 S1) discharged the `mem` half of
`IsHoeffdingLagrangeHyp` from the IVT and reduced the `realises` half to the
strictly-primitive predicate

      `IsHoeffdingTiltMinimal P₁ P₂ α λ`
        := `IsMinOn (klDivPmf · P₂) (hoeffdingConstraintSet P₁ α) (hoeffdingTilt P₁ P₂ λ)`,

the Csiszár I-projection minimality of the exponential tilt. This file
**discharges** that minimality fully (no `sorry`, no boundary pass-through),
for the genuine interior regime `0 < λ ≤ 1` with the IVT constraint-match
`klDivPmf (tilt) P₁ = α`.

## Approach

The discharge is the exponential-family Pythagorean identity, derived from the
**log-linearity** of the tilt and a per-coordinate algebraic identity that holds
*even at zero atoms* (so the minimality extends to the whole constraint set `K`,
boundary included — no `IsHoeffdingInteriorGradient` retreat is needed).

The key per-coordinate fact, valid for `R > 0` and all `Q ≥ 0` (including `Q = 0`,
where `0 · log 0 = 0`):

      `R · klFun (Q / R) = Q · log Q - Q · log R + (R - Q)`.

Summing this against the three references `P₂`, `P₁`, `T = hoeffdingTilt P₁ P₂ λ`
with weights `λ`, `1 - λ`, `-1` makes the `Q log Q` terms cancel (coefficients
`λ + (1-λ) - 1 = 0`) and the `Q log R` terms collapse via the tilt's
constant-log-ratio identity `log T - (1-λ) log P₁ - λ log P₂ = -log Z`
(`hoeffdingTilt_log_ratio_const`) into the *flat* term `Q · (-log Z)`. Summing
over the simplex (`∑ Q = 1`) gives the **master identity**

      `λ · D(Q‖P₂) + (1-λ) · D(Q‖P₁) - D(Q‖T) = -log Z`        (∀ Q ∈ stdSimplex).

Specialising to `Q = T` (`D(T‖T)=0`) and subtracting yields the **Pythagorean
difference**

      `λ (D(Q‖P₂) - D(T‖P₂)) + (1-λ)(D(Q‖P₁) - D(T‖P₁)) = D(Q‖T) ≥ 0`.

For `Q ∈ K` the constraint gives `D(Q‖P₁) ≤ α = D(T‖P₁)`, so the `(1-λ)·(…)`
term is `≤ 0` (using `1-λ ≥ 0`); hence `λ (D(Q‖P₂) - D(T‖P₂)) ≥ 0`, and with
`λ > 0` we get `D(T‖P₂) ≤ D(Q‖P₂)` — exactly `IsMinOn`.

## What this file publishes

* `klFun_ref_mul` — per-coordinate `R·klFun(Q/R) = Q logQ - Q logR + (R-Q)`,
  valid at `Q = 0`.
* `klDivPmf_eq_entropyCross_sum` — `D(Q‖R) = ∑ (Q logQ - Q logR + R - Q)`.
* `hoeffdingTilt_kl_master` — the master identity (∀ `Q ∈ stdSimplex`).
* `hoeffdingTilt_kl_pythagoras_diff` — the Pythagorean difference identity.
* `isHoeffdingTiltMinimal_of_constraint_eq` — **the `IsHoeffdingTiltMinimal`
  discharge** from `0 < λ`, `λ ≤ 1`, and the constraint-match equality.
* `isHoeffdingLagrangeHyp_of_constraint_eq` — full `IsHoeffdingLagrangeHyp` with
  *both* halves now constructive (no minimality hypothesis carried).
* `exists_isHoeffdingLagrangeHyp_interior` — interior existence: IVT supplies the
  `λ ∈ (0,1]`, minimality is discharged in-file.
-/

namespace InformationTheory.Shannon.HoeffdingMinimizerAttainment

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon InformationTheory.Shannon.HoeffdingTradeoff
open InformationTheory.Shannon.HoeffdingInteriorBody
open InformationTheory.Shannon.HoeffdingInteriorGradientBody
open InformationTheory.Shannon.HoeffdingLagrangeIVTBody
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Phase 1 — Per-coordinate `klFun` identity (valid at zero atoms) -/

/-- **Per-coordinate `klFun` identity**: for a positive reference `R` and any
`Q ≥ 0` (including `Q = 0`, where `0 · log 0 = 0`),
`R · klFun (Q / R) = Q · log Q - Q · log R + (R - Q)`. -/
lemma klFun_ref_mul {R Q : ℝ} (hR : 0 < R) (hQ : 0 ≤ Q) :
    R * klFun (Q / R) = Q * Real.log Q - Q * Real.log R + (R - Q) := by
  rcases eq_or_lt_of_le hQ with hQ0 | hQpos
  · -- Q = 0 : LHS = R * klFun 0 = R * 1 = R ; RHS = 0 - 0 + (R - 0) = R.
    subst hQ0
    simp [InformationTheory.klFun_zero]
  · -- Q > 0 : R * ((Q/R) log(Q/R) + 1 - Q/R) = Q (log Q - log R) + R - Q.
    have hRne : R ≠ 0 := hR.ne'
    have h_log_div : Real.log (Q / R) = Real.log Q - Real.log R :=
      Real.log_div hQpos.ne' hRne
    unfold klFun
    rw [h_log_div]
    field_simp
    ring

/-! ## Phase 2 — `klDivPmf` cross-entropy sum form (no full support) -/

omit [DecidableEq α] in
/-- **Cross-entropy sum form** of `klDivPmf`, valid for any `Q ∈ stdSimplex`
(full support *not* required) and full-support reference `R`:
`klDivPmf Q R = ∑ a, (Q a · log (Q a) - Q a · log (R a) + (R a - Q a))`. -/
lemma klDivPmf_eq_entropyCross_sum
    {Q R : α → ℝ} (hR_pos : ∀ a, 0 < R a) (hQ_nn : ∀ a, 0 ≤ Q a) :
    klDivPmf Q R
      = ∑ a, (Q a * Real.log (Q a) - Q a * Real.log (R a) + (R a - Q a)) := by
  unfold klDivPmf
  refine Finset.sum_congr rfl fun a _ => ?_
  exact klFun_ref_mul (hR_pos a) (hQ_nn a)

/-! ## Phase 3 — Master exponential-family identity -/

omit [DecidableEq α] in
/-- **Master identity**: for every `Q ∈ stdSimplex` the log-linear weighting of
the three KL divergences against `P₂`, `P₁`, and the tilt collapses to the flat
`-log Z`:

    `λ · klDivPmf Q P₂ + (1-λ) · klDivPmf Q P₁ - klDivPmf Q (tilt) = -log Z(λ)`.

This holds with no full-support hypothesis on `Q`. -/
lemma hoeffdingTilt_kl_master
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (lam : ℝ) {Q : α → ℝ} (hQ : Q ∈ stdSimplex ℝ α) :
    lam * klDivPmf Q P₂ + (1 - lam) * klDivPmf Q P₁
        - klDivPmf Q (hoeffdingTilt P₁ P₂ lam)
      = -Real.log (chernoffZSum P₁ P₂ lam) := by
  classical
  set T : α → ℝ := hoeffdingTilt P₁ P₂ lam with hT_def
  have hT_pos : ∀ a, 0 < T a := hoeffdingTilt_pos P₁ P₂ hP₁_pos hP₂_pos lam
  have hQ_nn : ∀ a, 0 ≤ Q a := hQ.1
  -- Cross-entropy sum forms for the three references.
  rw [klDivPmf_eq_entropyCross_sum (fun a => hP₂_pos a) hQ_nn,
      klDivPmf_eq_entropyCross_sum (fun a => hP₁_pos a) hQ_nn,
      klDivPmf_eq_entropyCross_sum (fun a => hT_pos a) hQ_nn]
  -- Pull scalars into the sums, then collapse per coordinate.
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  -- Per-coordinate: combine to Q a * (-log Z) + (lam P₂ a + (1-lam) P₁ a - T a).
  have h_per : ∀ a : α,
      lam * (Q a * Real.log (Q a) - Q a * Real.log (P₂ a) + (P₂ a - Q a))
        + (1 - lam) * (Q a * Real.log (Q a) - Q a * Real.log (P₁ a) + (P₁ a - Q a))
        - (Q a * Real.log (Q a) - Q a * Real.log (T a) + (T a - Q a))
        = Q a * (-Real.log (chernoffZSum P₁ P₂ lam))
          + (lam * P₂ a + (1 - lam) * P₁ a - T a) := by
    intro a
    -- log T a = (1-lam) log P₁ a + lam log P₂ a - log Z, from the log-ratio identity.
    have h_log_ratio := hoeffdingTilt_log_ratio_const P₁ P₂ hP₁_pos hP₂_pos lam a
    -- h_log_ratio : log (T a) - (1-lam) log (P₁ a) - lam log (P₂ a) = -log Z
    have h_logT : Real.log (T a)
        = (1 - lam) * Real.log (P₁ a) + lam * Real.log (P₂ a)
          - Real.log (chernoffZSum P₁ P₂ lam) := by
      have : Real.log (hoeffdingTilt P₁ P₂ lam a)
          - (1 - lam) * Real.log (P₁ a) - lam * Real.log (P₂ a)
          = -Real.log (chernoffZSum P₁ P₂ lam) := h_log_ratio
      simp only [hT_def]
      linarith [this]
    rw [h_logT]
    ring
  rw [Finset.sum_congr rfl fun a _ => h_per a]
  -- Split: ∑ Q a · (-log Z) + ∑ (lam P₂ + (1-lam) P₁ - T) = -log Z · 1 + 0.
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  have hQ_sum : ∑ a, Q a = 1 := hQ.2
  have hT_sum : ∑ a, T a = 1 := hoeffdingTilt_sum_eq_one P₁ P₂ hP₁_pos hP₂_pos lam
  -- ∑ (lam P₂ a + (1-lam) P₁ a - T a) = lam·1 + (1-lam)·1 - 1 = 0.
  have h_const_sum : ∑ a, (lam * P₂ a + (1 - lam) * P₁ a - T a) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hP₁_sum, hP₂_sum, hT_sum]
    ring
  rw [hQ_sum, h_const_sum]
  ring

/-! ## Phase 4 — Pythagorean difference identity -/

omit [DecidableEq α] in
/-- **Pythagorean difference identity** (Csiszár): subtracting the master
identity at `Q` and at the tilt `T` (where `klDivPmf T T = 0`):

    `λ (klDivPmf Q P₂ - klDivPmf T P₂) + (1-λ)(klDivPmf Q P₁ - klDivPmf T P₁)
       = klDivPmf Q T`. -/
lemma hoeffdingTilt_kl_pythagoras_diff
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (lam : ℝ) {Q : α → ℝ} (hQ : Q ∈ stdSimplex ℝ α) :
    lam * (klDivPmf Q P₂ - klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂)
        + (1 - lam) * (klDivPmf Q P₁ - klDivPmf (hoeffdingTilt P₁ P₂ lam) P₁)
      = klDivPmf Q (hoeffdingTilt P₁ P₂ lam) := by
  classical
  set T : α → ℝ := hoeffdingTilt P₁ P₂ lam with hT_def
  have hT_pos : ∀ a, 0 < T a := hoeffdingTilt_pos P₁ P₂ hP₁_pos hP₂_pos lam
  have hT_mem : T ∈ stdSimplex ℝ α :=
    hoeffdingTilt_mem_stdSimplex P₁ P₂ hP₁_pos hP₂_pos lam
  -- Master at Q and at T.
  have h_master_Q := hoeffdingTilt_kl_master P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum lam hQ
  have h_master_T := hoeffdingTilt_kl_master P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum lam hT_mem
  -- klDivPmf T T = 0.
  have h_TT : klDivPmf T T = 0 := klDivPmf_self_eq_zero T hT_pos
  -- Subtract; the -log Z cancels.
  simp only [hT_def] at h_master_Q h_master_T h_TT ⊢
  rw [h_TT] at h_master_T
  linarith [h_master_Q, h_master_T]

/-! ## Phase 5 — `IsHoeffdingTiltMinimal` discharge -/

omit [DecidableEq α] in
/-- **I-projection minimality discharge**: for `0 < λ ≤ 1` and the IVT
constraint-match `klDivPmf (tilt) P₁ = α`, the tilt minimises `klDivPmf · P₂`
over the constraint set `K(α)`. This *fully discharges* the primitive
`IsHoeffdingTiltMinimal` (whole constraint set, boundary included). -/
theorem isHoeffdingTiltMinimal_of_constraint_eq
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha lam : ℝ} (h_lam_pos : 0 < lam) (h_lam_le : lam ≤ 1)
    (h_kl : klDivPmf (hoeffdingTilt P₁ P₂ lam) P₁ = alpha) :
    IsHoeffdingTiltMinimal P₁ P₂ alpha lam := by
  classical
  intro Q hQ
  -- Goal: klDivPmf (tilt) P₂ ≤ klDivPmf Q P₂  (IsMinOn applied at Q ∈ K).
  show klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂ ≤ klDivPmf Q P₂
  -- Unpack constraint-set membership.
  obtain ⟨hQ_simplex, hQ_kl⟩ : Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha := hQ
  set T : α → ℝ := hoeffdingTilt P₁ P₂ lam with hT_def
  -- Pythagorean difference identity.
  have h_pyth := hoeffdingTilt_kl_pythagoras_diff P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
    lam hQ_simplex
  -- klDivPmf Q T ≥ 0.
  have h_QT_nn : 0 ≤ klDivPmf Q T :=
    klDivPmf_nonneg Q T (fun a => hQ_simplex.1 a)
      (fun a => (hoeffdingTilt_pos P₁ P₂ hP₁_pos hP₂_pos lam a).le)
  -- Constraint: klDivPmf Q P₁ - klDivPmf T P₁ ≤ 0  (since klDivPmf T P₁ = alpha).
  have h_constraint : klDivPmf Q P₁ - klDivPmf T P₁ ≤ 0 := by
    rw [show klDivPmf T P₁ = alpha from h_kl]
    linarith [hQ_kl]
  -- 1 - lam ≥ 0.
  have h_one_sub : 0 ≤ 1 - lam := by linarith
  -- (1-lam)·(constraint) ≤ 0.
  have h_term2 : (1 - lam) * (klDivPmf Q P₁ - klDivPmf T P₁) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos h_one_sub h_constraint
  -- From h_pyth: lam·(D(Q‖P₂) - D(T‖P₂)) = D(Q‖T) - (1-lam)·(constraint) ≥ 0.
  simp only [hT_def] at h_pyth ⊢
  have h_lam_diff_nn : 0 ≤ lam * (klDivPmf Q P₂ - klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂) := by
    have := h_pyth
    nlinarith [h_QT_nn, h_term2, this]
  -- lam > 0 ⟹ D(T‖P₂) ≤ D(Q‖P₂).
  have h_diff_nn : 0 ≤ klDivPmf Q P₂ - klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂ := by
    have h_mul' : 0 ≤ (klDivPmf Q P₂ - klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂) * lam := by
      rw [mul_comm]; exact h_lam_diff_nn
    exact nonneg_of_mul_nonneg_left h_mul' h_lam_pos
  linarith

/-! ## Phase 6 — Constructive `IsHoeffdingLagrangeHyp` (both halves) -/

omit [DecidableEq α] in
/-- **Fully constructive Lagrange hypothesis**: from `0 < λ ≤ 1` and the IVT
constraint-match, build `IsHoeffdingLagrangeHyp` with both `mem` *and*
`realises` constructive — no minimality hypothesis carried. -/
theorem isHoeffdingLagrangeHyp_of_constraint_eq
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha lam : ℝ} (h_lam_pos : 0 < lam) (h_lam_le : lam ≤ 1)
    (h_kl : klDivPmf (hoeffdingTilt P₁ P₂ lam) P₁ = alpha) :
    IsHoeffdingLagrangeHyp P₁ P₂ alpha lam := by
  classical
  exact isHoeffdingLagrangeHyp_of_minimal P₁ P₂ hP₁_pos hP₂_pos h_kl
    (isHoeffdingTiltMinimal_of_constraint_eq P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
      h_lam_pos h_lam_le h_kl)

/-! ## Phase 7 — Interior existence (IVT + discharged minimality) -/

omit [DecidableEq α] in
/-- **Interior existence**: for interior `0 < α ≤ klDivPmf P₂ P₁`, the IVT
supplies a `λ ∈ (0,1]` whose tilt matches the constraint, and the in-file
minimality discharge upgrades it to a *fully constructive*
`IsHoeffdingLagrangeHyp` — no external minimality hypothesis. -/
theorem exists_isHoeffdingLagrangeHyp_interior
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_pos : 0 < alpha)
    (h_alpha_le : alpha ≤ klDivPmf P₂ P₁) :
    ∃ lam ∈ Set.Ioc (0 : ℝ) 1, IsHoeffdingLagrangeHyp P₁ P₂ alpha lam := by
  classical
  -- IVT supplies lam ∈ [0,1] with klDivPmf (tilt) P₁ = alpha.
  obtain ⟨lam, hlam_mem, hlam_kl⟩ :=
    exists_lam_hoeffdingTilt_kl_eq P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
      h_alpha_pos.le h_alpha_le
  -- lam ≠ 0: at lam = 0 the constraint functional is 0, contradicting alpha > 0.
  have h_lam_pos : 0 < lam := by
    rcases lt_or_eq_of_le hlam_mem.1 with h | h
    · exact h
    · exfalso
      -- h : 0 = lam, so lam = 0.
      have h_lam0 : lam = 0 := h.symm
      rw [h_lam0] at hlam_kl
      rw [hoeffdingTilt_kl_P₁_lam_zero P₁ P₂ hP₁_pos hP₂_pos hP₁_sum] at hlam_kl
      -- hlam_kl : 0 = alpha, contradicting 0 < alpha.
      linarith [hlam_kl]
  refine ⟨lam, ⟨h_lam_pos, hlam_mem.2⟩, ?_⟩
  exact isHoeffdingLagrangeHyp_of_constraint_eq P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
    h_lam_pos hlam_mem.2 hlam_kl

end InformationTheory.Shannon.HoeffdingMinimizerAttainment
