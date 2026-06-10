import InformationTheory.Draft.Shannon.HoeffdingInteriorGradientBody
import InformationTheory.Meta.EntryPoint
import Mathlib.Topology.Order.IntermediateValue

/-!
# T1-D Hoeffding tradeoff — Lagrange constraint-match via IVT (wave10 S1)

`HoeffdingInteriorGradientBody.lean` (wave9) reduced the interior Csiszár
characterization to a single named hypothesis `IsHoeffdingLagrangeHyp`, a
`structure` with two fields:

* `mem` — the tilt at `lam` lies in the constraint set `K(α)`
  (`klDivPmf (tilt) P₁ ≤ alpha`);
* `realises` — the tilt at `lam` realises the infimum
  (`hoeffdingE2 = klDivPmf (tilt) P₂`).

The companion gradient sub-predicate `IsKLGradientHyp` is *already discharged*
in-file (`isKLGradientHyp_tilt`). This file discharges the **`mem`** half — the
*constraint-match* — from the **Intermediate Value Theorem**, and reduces the
remaining **`realises`** half to a strictly-more-primitive *minimality*
predicate `IsHoeffdingTiltMinimal` (the Csiszár I-projection minimality), with
the bridge `IsHoeffdingTiltMinimal → realises` fully discharged.

## Approach

The constraint functional along the tilt family is

      `g(λ) := klDivPmf (hoeffdingTilt P₁ P₂ λ) P₁`.

At the endpoints the tilt collapses to the data distributions
(`chernoffMediator_lam_zero/one`):

      `g(0) = klDivPmf P₁ P₁ = 0`,   `g(1) = klDivPmf P₂ P₁`.

`g` is continuous on `[0,1]` (the mediator is a continuous `rpow`/`Z`-quotient,
`klFun` is continuous, finite-sum). By `intermediate_value_Icc`, for every
`alpha ∈ [0, klDivPmf P₂ P₁]` there is a `λ ∈ [0,1]` with `g(λ) = alpha`. That
`λ` makes the tilt land *exactly* on the constraint boundary, discharging the
`mem` field (with equality, hence `≤ alpha`). This is the genuine implicit-
function / monotonicity content the wave9 design flagged.

The `realises` field is the Csiszár-projection infimum-attainment. It is
*not* derivable from IVT; it requires that the tilt minimises `klDivPmf · P₂`
over `K(α)`. We expose this as the primitive `IsHoeffdingTiltMinimal` (an
`IsMinOn` flag, real content — not defeq to `realises`) and discharge the
bridge `IsHoeffdingTiltMinimal → (hoeffdingE2 = klDivPmf tilt P₂)` via the
`sInf` characterisation (`le_csInf` + `csInf_le`). Supplying the minimality
flag + IVT then assembles a full `IsHoeffdingLagrangeHyp`.

## What this file publishes

* `hoeffdingTilt_continuous_kl_P₁` — continuity of `g` on `ℝ`.
* `hoeffdingTilt_kl_P₁_lam_zero` / `_lam_one` — endpoint values of `g`.
* `exists_lam_hoeffdingTilt_kl_eq` — **IVT constraint-match**, fully discharged.
* `hoeffdingTilt_mem_constraintSet_of_kl_eq` — `mem` from a constraint-match.
* `IsHoeffdingTiltMinimal` — primitive minimality predicate (`IsMinOn`).
* `isHoeffdingTiltMinimal_realises` — bridge `minimal → realises`.
* `isHoeffdingLagrangeHyp_of_minimal` — assemble `IsHoeffdingLagrangeHyp` from
  IVT `mem` + minimality.
* `exists_isHoeffdingLagrangeHyp_of_minimal` — existence form (IVT supplies the
  `lam`; minimality is supplied per witness).

## Retreat line

The standalone discharge of `IsHoeffdingTiltMinimal` (the I-projection
minimality of the explicit tilt, i.e. the first-order/gradient KKT argument)
is the single remaining analytic content; it is kept as the primitive carried
through `isHoeffdingLagrangeHyp_of_minimal`. The `mem` half is now fully
constructive.
-/

namespace InformationTheory.Shannon.HoeffdingLagrangeIVTBody

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter
open InformationTheory.Shannon.Chernoff
open InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon InformationTheory.Shannon.HoeffdingTradeoff
open InformationTheory.Shannon.HoeffdingInteriorBody
open InformationTheory.Shannon.HoeffdingInteriorGradientBody
open scoped BigOperators Topology

variable {α : Type*} [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Phase 1 — Continuity of the constraint functional `g(λ) = klDivPmf T_λ P₁` -/

/-- The Chernoff mediator coordinate `λ ↦ T_λ(a)` is continuous in `λ` (a
continuous `rpow` numerator divided by the strictly-positive continuous `Z`). -/
lemma chernoffMediator_continuous_lam
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (a : α) :
    Continuous (fun lam : ℝ => chernoffMediator P₁ P₂ lam a) := by
  unfold chernoffMediator
  -- (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam / Z(lam), Z > 0 continuous.
  have h_num1 : Continuous (fun lam : ℝ => (P₁ a) ^ (1 - lam)) := by
    have h_base : Continuous (fun lam : ℝ => (1 - lam)) := continuous_const.sub continuous_id
    exact (Real.continuous_const_rpow (hP₁_pos a).ne').comp h_base
  have h_num2 : Continuous (fun lam : ℝ => (P₂ a) ^ lam) :=
    Real.continuous_const_rpow (hP₂_pos a).ne'
  have h_num : Continuous (fun lam : ℝ => (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam) :=
    h_num1.mul h_num2
  have h_Z : Continuous (fun lam : ℝ => chernoffZSum P₁ P₂ lam) :=
    chernoffZSum_continuous P₁ P₂ hP₁_pos hP₂_pos
  exact h_num.div h_Z (fun lam => (chernoffZSum_pos P₁ P₂ hP₁_pos hP₂_pos lam).ne')

/-- The constraint functional `g(λ) := klDivPmf (hoeffdingTilt P₁ P₂ λ) P₁` is
continuous in `λ` on all of `ℝ`. -/
lemma hoeffdingTilt_continuous_kl_P₁
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) :
    Continuous (fun lam : ℝ => klDivPmf (hoeffdingTilt P₁ P₂ lam) P₁) := by
  -- klDivPmf T_λ P₁ = ∑ a, P₁ a * klFun (T_λ a / P₁ a); each term continuous in λ.
  unfold klDivPmf
  refine continuous_finsetSum _ fun a _ => ?_
  have hP₁ne : P₁ a ≠ 0 := (hP₁_pos a).ne'
  have h_med : Continuous (fun lam : ℝ => hoeffdingTilt P₁ P₂ lam a) :=
    chernoffMediator_continuous_lam P₁ P₂ hP₁_pos hP₂_pos a
  have h_div : Continuous (fun lam : ℝ => hoeffdingTilt P₁ P₂ lam a / P₁ a) :=
    h_med.div_const (P₁ a)
  have h_kl : Continuous (fun lam : ℝ => klFun (hoeffdingTilt P₁ P₂ lam a / P₁ a)) :=
    continuous_klFun.comp h_div
  exact h_kl.const_mul (P₁ a)

/-! ## Phase 2 — Endpoint values of `g` -/

/-- `g(0) = klDivPmf P₁ P₁ = 0`. -/
lemma hoeffdingTilt_kl_P₁_lam_zero
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) :
    klDivPmf (hoeffdingTilt P₁ P₂ 0) P₁ = 0 := by
  classical
  have h_eq : hoeffdingTilt P₁ P₂ 0 = P₁ := by
    funext a
    rw [hoeffdingTilt_eq_chernoffMediator]
    exact chernoffMediator_lam_zero P₁ P₂ hP₁_pos hP₂_pos hP₁_sum a
  rw [h_eq]
  exact klDivPmf_self_eq_zero P₁ hP₁_pos

/-- `g(1) = klDivPmf P₂ P₁`. -/
lemma hoeffdingTilt_kl_P₁_lam_one
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₂_sum : ∑ a, P₂ a = 1) :
    klDivPmf (hoeffdingTilt P₁ P₂ 1) P₁ = klDivPmf P₂ P₁ := by
  classical
  have h_eq : hoeffdingTilt P₁ P₂ 1 = P₂ := by
    funext a
    rw [hoeffdingTilt_eq_chernoffMediator]
    exact chernoffMediator_lam_one P₁ P₂ hP₁_pos hP₂_pos hP₂_sum a
  rw [h_eq]

/-! ## Phase 3 — IVT constraint-match -/

/-- **IVT constraint-match**: for any `alpha ∈ [0, klDivPmf P₂ P₁]` there is a
tilt parameter `lam ∈ [0,1]` whose tilt hits the Type-I constraint *exactly*:
`klDivPmf (hoeffdingTilt P₁ P₂ lam) P₁ = alpha`. Discharged from
`intermediate_value_Icc`. -/
theorem exists_lam_hoeffdingTilt_kl_eq
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha)
    (h_alpha_le : alpha ≤ klDivPmf P₂ P₁) :
    ∃ lam ∈ Set.Icc (0 : ℝ) 1,
      klDivPmf (hoeffdingTilt P₁ P₂ lam) P₁ = alpha := by
  set g : ℝ → ℝ := fun lam => klDivPmf (hoeffdingTilt P₁ P₂ lam) P₁ with hg_def
  have hg_cont : Continuous g := hoeffdingTilt_continuous_kl_P₁ P₁ P₂ hP₁_pos hP₂_pos
  have hg0 : g 0 = 0 := hoeffdingTilt_kl_P₁_lam_zero P₁ P₂ hP₁_pos hP₂_pos hP₁_sum
  have hg1 : g 1 = klDivPmf P₂ P₁ :=
    hoeffdingTilt_kl_P₁_lam_one P₁ P₂ hP₁_pos hP₂_pos hP₂_sum
  -- alpha ∈ [g 0, g 1].
  have h_mem_Icc : alpha ∈ Set.Icc (g 0) (g 1) := by
    rw [hg0, hg1]
    exact ⟨h_alpha_nn, h_alpha_le⟩
  -- IVT: [g 0, g 1] ⊆ g '' [0,1].
  have h_ivt := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hg_cont.continuousOn
  obtain ⟨lam, hlam_mem, hlam_eq⟩ := h_ivt h_mem_Icc
  exact ⟨lam, hlam_mem, hlam_eq⟩

/-! ## Phase 4 — `mem` from a constraint-match -/

/-- A tilt parameter hitting the constraint with equality lands in the
constraint set `K(α)` (membership = simplex + `KL = alpha ≤ alpha`). -/
theorem hoeffdingTilt_mem_constraintSet_of_kl_eq
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {alpha lam : ℝ}
    (h_kl : klDivPmf (hoeffdingTilt P₁ P₂ lam) P₁ = alpha) :
    hoeffdingTilt P₁ P₂ lam ∈ hoeffdingConstraintSet P₁ alpha := by
  classical
  refine ⟨hoeffdingTilt_mem_stdSimplex P₁ P₂ hP₁_pos hP₂_pos lam, ?_⟩
  exact le_of_eq h_kl

/-! ## Phase 5 — Primitive minimality predicate + bridge to `realises` -/

/-- **Primitive tilt-minimality** (Csiszár I-projection): the tilt at `lam`
minimises `klDivPmf · P₂` over the constraint set `K(α)`. This carries genuine
content (an `IsMinOn` over all of `K`), distinct from the `sInf`-form
`hoeffdingE2 = klDivPmf tilt P₂` of `IsHoeffdingLagrangeHyp.realises`. -/
def IsHoeffdingTiltMinimal (P₁ P₂ : α → ℝ) (alpha lam : ℝ) : Prop :=
  IsMinOn (fun Q : α → ℝ => klDivPmf Q P₂)
    (hoeffdingConstraintSet P₁ alpha) (hoeffdingTilt P₁ P₂ lam)

/-- **Bridge (minimal ⇒ realises)**: when the tilt at `lam` lies in `K(α)` and
minimises `klDivPmf · P₂` on `K(α)`, it realises the infimum
`hoeffdingE2 P₁ P₂ alpha`. Discharged via the `sInf` characterisation. -/
theorem isHoeffdingTiltMinimal_realises
    (P₁ P₂ : α → ℝ) (hP₂_pos : ∀ a, 0 < P₂ a)
    {alpha lam : ℝ}
    (h_mem : hoeffdingTilt P₁ P₂ lam ∈ hoeffdingConstraintSet P₁ alpha)
    (h_min : IsHoeffdingTiltMinimal P₁ P₂ alpha lam) :
    hoeffdingE2 P₁ P₂ alpha = klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂ := by
  classical
  set S : Set (α → ℝ) := {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha} with hS_def
  -- The constraint set is exactly S (defeq).
  have h_mem_S : hoeffdingTilt P₁ P₂ lam ∈ S := h_mem
  set img : Set ℝ := (fun Q : α → ℝ => klDivPmf Q P₂) '' S with himg_def
  have h_bdd : BddBelow img := by
    refine ⟨0, ?_⟩
    rintro y ⟨Q', hQ', rfl⟩
    exact klDivPmf_nonneg Q' P₂ hQ'.1.1 (fun a => (hP₂_pos a).le)
  have h_tilt_img : klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂ ∈ img :=
    ⟨hoeffdingTilt P₁ P₂ lam, h_mem_S, rfl⟩
  -- Lower-bound direction: hoeffdingE2 = sInf img ≤ klDivPmf tilt P₂.
  have h_le : hoeffdingE2 P₁ P₂ alpha ≤ klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂ := by
    show sInf img ≤ klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂
    exact csInf_le h_bdd h_tilt_img
  -- Minimality direction: klDivPmf tilt P₂ ≤ sInf img.
  have h_ge : klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂ ≤ hoeffdingE2 P₁ P₂ alpha := by
    show klDivPmf (hoeffdingTilt P₁ P₂ lam) P₂ ≤ sInf img
    refine le_csInf ⟨_, h_tilt_img⟩ ?_
    rintro y ⟨Q', hQ', rfl⟩
    -- Q' ∈ S = hoeffdingConstraintSet, minimality applies.
    exact h_min hQ'
  linarith

/-! ## Phase 6 — Assemble `IsHoeffdingLagrangeHyp` -/

/-- **Assemble Lagrange hypothesis**: from an IVT constraint-match (`mem`,
`klDivPmf tilt P₁ = alpha`) and the minimality primitive, build a full
`IsHoeffdingLagrangeHyp`. The `mem` half is constructive; only minimality is
carried. -/
theorem isHoeffdingLagrangeHyp_of_minimal
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {alpha lam : ℝ}
    (h_kl : klDivPmf (hoeffdingTilt P₁ P₂ lam) P₁ = alpha)
    (h_min : IsHoeffdingTiltMinimal P₁ P₂ alpha lam) :
    IsHoeffdingLagrangeHyp P₁ P₂ alpha lam := by
  have h_mem : hoeffdingTilt P₁ P₂ lam ∈ hoeffdingConstraintSet P₁ alpha :=
    hoeffdingTilt_mem_constraintSet_of_kl_eq P₁ P₂ hP₁_pos hP₂_pos h_kl
  exact
    { mem := h_mem
      realises := isHoeffdingTiltMinimal_realises P₁ P₂ hP₂_pos h_mem h_min }

/-- **Existence form**: IVT supplies a `lam ∈ [0,1]` matching the constraint;
together with the minimality primitive at that `lam`, a full
`IsHoeffdingLagrangeHyp` exists. The minimality hypothesis is quantified over
the (otherwise unknown) IVT witness. -/
@[entry_point]
theorem exists_isHoeffdingLagrangeHyp_of_minimal
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha)
    (h_alpha_le : alpha ≤ klDivPmf P₂ P₁)
    (h_min : ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      klDivPmf (hoeffdingTilt P₁ P₂ lam) P₁ = alpha →
      IsHoeffdingTiltMinimal P₁ P₂ alpha lam) :
    ∃ lam ∈ Set.Icc (0 : ℝ) 1, IsHoeffdingLagrangeHyp P₁ P₂ alpha lam := by
  obtain ⟨lam, hlam_mem, hlam_kl⟩ :=
    exists_lam_hoeffdingTilt_kl_eq P₁ P₂ hP₁_pos hP₂_pos hP₁_sum hP₂_sum
      h_alpha_nn h_alpha_le
  refine ⟨lam, hlam_mem, ?_⟩
  exact isHoeffdingLagrangeHyp_of_minimal P₁ P₂ hP₁_pos hP₂_pos hlam_kl
    (h_min lam hlam_mem hlam_kl)

end InformationTheory.Shannon.HoeffdingLagrangeIVTBody
