/-
# EPI lift-and-transport: 3-noise lift 機材

本 file は **3-noise lift** 空間 `Ω × ℝ × ℝ × ℝ` (3 因子はすべて `gaussianReal 0 1`) 上の
machinery を集約する。two-time case-1 assembler は和を `(Z_X, Z_Y)` とは独立な単一 unit noise `Z`
で摂動するため独立な標準正規が 3 つ要る。lift 上では第1因子 `Prod.fst` だけが `X`/`Y` を運ぶので、
3 つの `entropyPower` 項はすべて `measurePreserving_fst` で base へ transport できる。

`entropy_power_inequality_via_lift3` が live な transport lemma で、密度版 EPI 結論が消費する:
`EPIDensityForm.entropy_power_inequality_of_density`,
`EPICase1SmoothingLimit.entropy_power_inequality_of_density_explicit` /
`entropy_power_add_ge_of_finite_variance`。

## History

元の **2-noise** lift route (`liftMeasure` on `Ω × ℝ × ℝ` / `stamScalingNoise_exists_on_lift` /
`entropy_power_inequality_via_lift`) と、それが住んでいた richness 述語 `IsStamScalingNoiseHyp`
(ToBridge.lean) は、削除された in-place 偽 W2 `stamScalingNoise_exists` (commit `192410c`) の honest
置換だった。genuine・sorryAx-free だったが、3-noise route が密度版結論に結線された時点で superseded な
dead code になり、consumer ripple 0 で削除した (2026-06-09, `epi-richness-route-b-plan` closure)。
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import InformationTheory.Shannon.EntropyPower.Inequality

namespace InformationTheory.Shannon.EPINoiseExtension

open MeasureTheory ProbabilityTheory
open InformationTheory.Shannon.EntropyPowerInequality

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable (X Y : Ω → ℝ)

/-! ## 3-noise lift (two-time route)

The two-time assembler `entropyPower_add_ge_case1_of_regular_twotime` perturbs the
sum with a SEPARATE single unit noise `Z`, independent of `(Z_X, Z_Y)`. That requires a
**3-noise** lift `Ω × ℝ × ℝ × ℝ` (three independent standard normals), since reusing one
of the 2-noise factors for `Z` would break `Z ⊥ (Z_X, Z_Y)`. In the transport lemma below
only the first factor (`Prod.fst`) carries `X`/`Y`, so all three `entropyPower` terms
transport via `measurePreserving_fst`. -/

/-- 3-noise lift 空間 `Ω × ℝ × ℝ × ℝ` の測度 (3 因子はすべて標準正規)。 -/
noncomputable abbrev liftMeasure3 : Measure (Ω × ℝ × ℝ × ℝ) :=
  P.prod ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))

omit [IsProbabilityMeasure P] in
/-- lift3 上で `X` law が保存される (transport の linchpin)。 -/
theorem entropyPower_map_comp_fst_eq3 (hX : Measurable X) :
    entropyPower ((liftMeasure3 P).map (fun p => X p.1)) = entropyPower (P.map X) := by
  have hmap : (liftMeasure3 P).map (fun p : Ω × ℝ × ℝ × ℝ => X p.1) = P.map X := by
    rw [show (fun p : Ω × ℝ × ℝ × ℝ => X p.1) = X ∘ Prod.fst from rfl,
      ← Measure.map_map hX measurable_fst, measurePreserving_fst.map_eq]
  rw [hmap]

omit [IsProbabilityMeasure P] in
/-- route B 本体 (3-noise lift、conditional transport 形)。仮説 `h_lift_epi` は別測度
`liftMeasure3 P` 上の EPI 結論で、base `(Ω,P)` の EPI と別 Prop。これは honest な
measure-transport reduction (Stam の核を抱えず lift 空間 EPI を base へ張替えるだけ) で、
非循環・非バンドル。 -/
theorem entropy_power_inequality_via_lift3 (hX : Measurable X) (hY : Measurable Y)
    (h_lift_epi : entropyPower ((liftMeasure3 P).map (fun p => X p.1 + Y p.1))
      ≥ entropyPower ((liftMeasure3 P).map (fun p => X p.1))
        + entropyPower ((liftMeasure3 P).map (fun p => Y p.1))) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  rw [entropyPower_map_comp_fst_eq3 P X hX,
      entropyPower_map_comp_fst_eq3 P Y hY] at h_lift_epi
  rwa [entropyPower_map_comp_fst_eq3 P (fun ω => X ω + Y ω) (hX.add hY)] at h_lift_epi

end InformationTheory.Shannon.EPINoiseExtension
