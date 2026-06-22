import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.AWGN.Main

/-!
# AWGN kernel measurability

The AWGN channel kernel `fun x : ℝ ↦ gaussianReal x N` is measurable on the Giry
monad. This discharges the `IsAwgnChannelMeasurable N` predicate, which lets the
AWGN channel coding theorem and the capacity closed form be re-published without
the kernel-measurability side hypothesis.

## Main statements

* `isAwgnChannelMeasurable` — the AWGN kernel `fun x ↦ gaussianReal x N` is
  measurable.
* `awgn_theorem_F1_discharged` — the AWGN channel coding theorem, with the kernel
  measurability hypothesis discharged by `isAwgnChannelMeasurable`.
* `awgn_capacity_closed_form_F1_discharged` — the AWGN capacity closed form, with
  the kernel measurability hypothesis discharged.

## Implementation notes

The kernel is reshaped as a mean shift of a fixed measure,
`gaussianReal x N = (gaussianReal 0 N).map (x + ·)` (via `gaussianReal_map_const_add`
specialized to mean `0`). Measurability of the resulting map then follows
structurally from the Giry monad API (`Measure.measurable_of_measurable_coe`
together with `Measure.measurable_measure_prodMk_left`), rather than from any
analytic estimate.
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

lemma gaussianReal_eq_zero_map (x : ℝ) (N : ℝ≥0) :
    gaussianReal x N = (gaussianReal 0 N).map (x + ·) := by
  rw [gaussianReal_map_const_add x, zero_add]

/-- The AWGN channel kernel `fun x : ℝ ↦ gaussianReal x N` is measurable on the Giry
monad, discharging the `IsAwgnChannelMeasurable N` predicate. -/
@[entry_point]
theorem isAwgnChannelMeasurable (N : ℝ≥0) : IsAwgnChannelMeasurable N := by
  unfold IsAwgnChannelMeasurable
  -- Function equality `fun x => gaussianReal x N = fun x => (gaussianReal 0 N).map (x + ·)`.
  have h_fun_eq :
      (fun x : ℝ ↦ gaussianReal x N)
        = (fun x : ℝ ↦ (gaussianReal 0 N).map (x + ·)) := by
    funext x
    exact gaussianReal_eq_zero_map x N
  rw [h_fun_eq]
  -- Giry-monad measurability criterion: ∀ s, ms s → Measurable (fun x ↦ μ.map (x+·) s).
  refine Measure.measurable_of_measurable_coe _ ?_
  intro s hs
  -- `MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ s}` (Borel preimage of continuous addition).
  have h_meas_add : MeasurableSet {p : ℝ × ℝ | p.1 + p.2 ∈ s} :=
    (measurable_fst.add measurable_snd) hs
  -- Function equality: ∀ x, (gaussianReal 0 N).map (x + ·) s
  --              = (gaussianReal 0 N) (Prod.mk x ⁻¹' {p | p.1 + p.2 ∈ s}).
  have h_apply_eq :
      (fun x : ℝ ↦ ((gaussianReal 0 N).map (x + ·)) s)
        = (fun x : ℝ ↦ (gaussianReal 0 N)
            (Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 + p.2 ∈ s})) := by
    funext x
    have h_meas_x : Measurable (x + · : ℝ → ℝ) :=
      measurable_const.add measurable_id
    rw [Measure.map_apply h_meas_x hs]
    -- (x + ·) ⁻¹' s = Prod.mk x ⁻¹' {p | p.1 + p.2 ∈ s}
    rfl
  rw [h_apply_eq]
  exact measurable_measure_prodMk_left h_meas_add

/-- The AWGN channel coding theorem, re-published with the kernel-measurability
hypothesis discharged by `isAwgnChannelMeasurable N`, so it no longer appears in
the signature.

`@audit:closed-by-successor(awgn-moonshot-plan)`

@audit:ok (independent honesty audit 2026-06-12, commit e728ebf: `h_mi_bridge`
removed from signature. Pure strengthening — the parent `awgn_channel_coding_theorem`
never consumed `h_mi_bridge` in its body, so this wrapper's old `h_mi_bridge`
pass-through was dead. Post-removal body delegates to `awgn_channel_coding_theorem`
(itself a sorryAx-free pass-through of `awgn_achievability`); conclusion follows
verbatim. `#print axioms awgn_theorem_F1_discharged` = `[propext, Classical.choice,
Quot.sound]` re-confirmed by this audit.) -/
@[entry_point]
theorem awgn_theorem_F1_discharged
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    {R : ℝ} (hR_pos : 0 < R) (hR_lt_C : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M)
        (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt
                  (awgnChannel N (isAwgnChannelMeasurable N)) m).toReal < ε :=
  awgn_channel_coding_theorem P hP N hN (isAwgnChannelMeasurable N)
    hR_pos hR_lt_C hε

/-- The AWGN capacity closed form, re-published with the kernel-measurability
hypothesis discharged by `isAwgnChannelMeasurable N`. The remaining hypotheses
(`h_bridge_gauss`, `h_bdd`, `h_max_ent`) are unchanged.

`@audit:closed-by-successor(awgn-mi-bridge-plan)` -/
@[entry_point]
theorem awgn_capacity_closed_form_F1_discharged
    (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_bridge_gauss :
        (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
            (gaussianReal 0 P.toNNReal)
            (awgnChannel N (isAwgnChannelMeasurable N))).toReal
          = (1/2) * Real.log (1 + P / (N : ℝ)))
    (h_bdd :
        BddAbove ((fun p : Measure ℝ ↦
            (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
                p (awgnChannel N (isAwgnChannelMeasurable N))).toReal) ''
          awgnPowerConstraintSet P))
    (h_max_ent :
        ∀ p ∈ awgnPowerConstraintSet P,
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (awgnChannel N (isAwgnChannelMeasurable N))).toReal
            ≤ (1/2) * Real.log (1 + P / (N : ℝ))) :
    awgnCapacity P N (isAwgnChannelMeasurable N)
      = (1/2) * Real.log (1 + P / (N : ℝ)) :=
  awgn_capacity_closed_form P hP N hN (isAwgnChannelMeasurable N)
    h_bridge_gauss h_bdd h_max_ent

end InformationTheory.Shannon.AWGN
