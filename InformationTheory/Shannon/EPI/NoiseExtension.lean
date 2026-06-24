import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import InformationTheory.Shannon.EntropyPower.Inequality

/-!
# EPI lift-and-transport: 3-noise lift machinery

The 3-noise lift space `Ω × ℝ × ℝ × ℝ` (three independent standard Gaussian factors)
and the transport lemma that reduces a lift-space EPI conclusion to a base-space one.

## Main definitions

- `liftMeasure3`: the product measure on `Ω × ℝ × ℝ × ℝ`.

## Main statements

- `entropyPower_map_comp_fst_eq3`: `entropyPower` is preserved by the first-factor projection.
- `entropy_power_inequality_via_lift3`: reduces a lift-space EPI to the base-space EPI.
-/

namespace InformationTheory.Shannon.EPINoiseExtension

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon.EntropyPowerInequality

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable (X Y : Ω → ℝ)

/-! ## 3-noise lift (two-time route)

The two-time assembler `entropyPower_add_ge_case1_of_regular_twotime` perturbs the
sum with a SEPARATE single unit noise `Z`, independent of `(Z_X, Z_Y)`. That requires a
3-noise lift `Ω × ℝ × ℝ × ℝ` (three independent standard normals), since reusing one
of the 2-noise factors for `Z` would break `Z ⊥ (Z_X, Z_Y)`. In the transport lemma below
only the first factor (`Prod.fst`) carries `X`/`Y`, so all three `entropyPower` terms
transport via `measurePreserving_fst`. -/

/-- Product measure on the 3-noise lift space `Ω × ℝ × ℝ × ℝ` (three standard Gaussian factors). -/
noncomputable abbrev liftMeasure3 : Measure (Ω × ℝ × ℝ × ℝ) :=
  P.prod ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))

omit [IsProbabilityMeasure P] in
theorem entropyPower_map_comp_fst_eq3 (hX : Measurable X) :
    entropyPower ((liftMeasure3 P).map (fun p ↦ X p.1)) = entropyPower (P.map X) := by
  have hmap : (liftMeasure3 P).map (fun p : Ω × ℝ × ℝ × ℝ ↦ X p.1) = P.map X := by
    rw [show (fun p : Ω × ℝ × ℝ × ℝ ↦ X p.1) = X ∘ Prod.fst from rfl,
      ← Measure.map_map hX measurable_fst, measurePreserving_fst.map_eq]
  rw [hmap]

omit [IsProbabilityMeasure P] in
/-- Reduce a lift-space EPI conclusion to the base-space EPI via measure transport along
`Prod.fst`. -/
theorem entropy_power_inequality_via_lift3 (hX : Measurable X) (hY : Measurable Y)
    (h_lift_epi : entropyPower ((liftMeasure3 P).map (fun p ↦ X p.1 + Y p.1))
      ≥ entropyPower ((liftMeasure3 P).map (fun p ↦ X p.1))
        + entropyPower ((liftMeasure3 P).map (fun p ↦ Y p.1))) :
    entropyPower (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  rw [entropyPower_map_comp_fst_eq3 P X hX,
      entropyPower_map_comp_fst_eq3 P Y hY] at h_lift_epi
  rwa [entropyPower_map_comp_fst_eq3 P (fun ω ↦ X ω + Y ω) (hX.add hY)] at h_lift_epi

end InformationTheory.Shannon.EPINoiseExtension
