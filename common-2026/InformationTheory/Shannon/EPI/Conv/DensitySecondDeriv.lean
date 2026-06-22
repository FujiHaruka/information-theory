import InformationTheory.Shannon.EPI.Conv.Density
import InformationTheory.Shannon.FisherInfo.DeBruijnPerTime
import InformationTheory.Shannon.FisherInfo.Gaussian

/-!
# Convolution density — spatial 2nd derivative identification (STEP D bridge)

The genuine spatial-second-derivative closed form of the heat-flow convolution
density `p_s(z) = ∫ y, pX y · g_s(z - y) ∂volume` (`g_s = gaussianPDFReal 0 ⟨s,_⟩`,
variance `s`):

```
deriv (deriv (convDensityAdd pX g_s)) z
  = ∫ y, pX y · (g_s(z - y) · ((z - y)²/s² - 1/s)) ∂volume.
```

This is the upstream block of GAP② (`convDensityAdd_deriv2_poly_moment_majorant`):
once the second derivative is identified as this integral, GAP② majorizes it by
`∫ pX y · g_s(z-y) · |(z-y)²/s² - 1/s| dy` via a triangle bound.

## Mathlib-shape-driven

The conclusion is an **equality** (not a `HasDerivAt`) so that the triangle bound
in GAP② can `rw` it directly. We reach it by applying the parametric-integral
gateway `hasDerivAt_integral_of_dominated_loc_of_deriv_le` twice (1st then 2nd
spatial derivative), mirroring the genuine STEP D code in
`FisherInfoDeBruijnPerTime.heatFlow_density_heat_equation`. The Gaussian-tail
domination of the polynomial×Gaussian integrand is supplied as **honest
regularity preconditions** in the exact shape the gateway consumes — NOT a
load-bearing bundling of the second-derivative conclusion, which is *derived*.

The per-`y` kernel derivative closed forms are the `@audit:ok` atoms
`heatFlow_density_heat_equation_kernel_x_deriv1` / `_x_deriv2`
(`FisherInfoDeBruijnPerTime.lean`), and `heatFlow_density_heat_equation_kernel_eq`
bridges them to `gaussianPDFReal`.
-/

namespace InformationTheory.Shannon.EPIConvDensitySecondDeriv

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EPIConvDensity
open InformationTheory.Shannon.FisherInfo

/-- **Spatial first-derivative identification (as a function).** Under
Gaussian-tail domination preconditions, the spatial first derivative of the
convolution density is the integral of `pX y · ∂_z g_s(z-y) = pX y · g_s(z-y)·(-(z-y)/s)`:

```
deriv (convDensityAdd pX g_s) = fun ζ => ∫ y, pX y · (g_s(ζ-y) · (-(ζ-y)/s)) ∂volume.
```

All hyps are integrand-level regularity (per-`y` integrability / ae-measurability /
Gaussian-tail norm bound), 1:1 with the gateway lemma's argument group. NOT
load-bearing: the derivative is *derived* via the gateway, not assumed.

Genuine, sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`),
0 sorry / 0 residual. -/
theorem convDensityAdd_deriv1_gaussian_eq
    (pX : ℝ → ℝ) {s : ℝ} (hs : 0 < s)
    (bound1 : ℝ → ℝ) (hbound1_int : Integrable bound1 volume)
    (hF1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume)
    (hF1_int : ∀ ξ : ℝ,
      Integrable (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume)
    (hF1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))) volume)
    (hb1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))‖ ≤ bound1 y) :
    deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      = fun ζ : ℝ => ∫ y, pX y * (gaussianPDFReal 0 ⟨s, hs.le⟩ (ζ - y)
          * (-((ζ - y) / s))) ∂volume := by
  -- `convDensityAdd pX g_s = fun ζ => ∫ y, pX y · kernel s (ζ-y)` (s>0, all ζ).
  have hconv_eq : (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      = (fun ζ : ℝ => ∫ y, pX y * heatFlow_density_heat_equation_kernel s (ζ - y) ∂volume) := by
    funext ζ
    unfold convDensityAdd
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [heatFlow_density_heat_equation_kernel_eq hs (ζ - y)]
  funext ζ
  -- per-y spatial 1st-derivative HasDerivAt (kernel `_x_deriv1` chained through `ξ ↦ ξ - y`).
  have hdiff : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun ξ => pX y * heatFlow_density_heat_equation_kernel s (ξ - y))
        (pX y * (heatFlow_density_heat_equation_kernel s (ξ - y) * (-((ξ - y) / s)))) ξ := by
    filter_upwards with y
    intro ξ _
    have hk := heatFlow_density_heat_equation_kernel_x_deriv1 hs (ξ - y)
    have hshift : HasDerivAt (fun ξ : ℝ => ξ - y) 1 ξ := by
      simpa using (hasDerivAt_id ξ).sub_const y
    have hcomp := hk.comp ξ hshift
    simp only [mul_one] at hcomp
    exact hcomp.const_mul (pX y)
  have hgate :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun ζ y => pX y * heatFlow_density_heat_equation_kernel s (ζ - y))
      (F' := fun ζ y => pX y * (heatFlow_density_heat_equation_kernel s (ζ - y)
        * (-((ζ - y) / s))))
      (bound := bound1) (Filter.univ_mem)
      (Filter.Eventually.of_forall hF1_meas) (hF1_int ζ) (hF1'_meas ζ)
      hb1 hbound1_int hdiff
  -- `hgate.2 : HasDerivAt (fun ζ => ∫ y, pX y · kernel s (ζ-y)) (∫ y, pX y · kernel·(-(ζ-y)/s)) ζ`
  have hderiv : HasDerivAt (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      (∫ y, pX y *
        (heatFlow_density_heat_equation_kernel s (ζ - y) * (-((ζ - y) / s))) ∂volume) ζ := by
    rw [hconv_eq]; exact hgate.2
  rw [hderiv.deriv]
  -- rewrite the kernel back to `gaussianPDFReal` inside the integral.
  refine integral_congr_ae ?_
  filter_upwards with y
  rw [heatFlow_density_heat_equation_kernel_eq hs (ζ - y)]

/-- **Spatial second-derivative closed form (STEP D bridge).** Under Gaussian-tail
domination preconditions, the spatial second derivative of the heat-flow
convolution density is the integral of `pX y · ∂²_z g_s(z-y)`:

```
deriv (deriv (convDensityAdd pX g_s)) z
  = ∫ y, pX y · (g_s(z-y) · ((z-y)²/s² - 1/s)) ∂volume.
```

`hpX_nn` / `hpX_int` are regularity preconditions on `pX` (carried for downstream
GAP② consumers; not used by this pure differentiation identity). The `bound1` /
`bound2` groups are Gaussian-tail domination preconditions in the exact gateway
shape (integrand-level, NOT load-bearing). The closed form is *derived* via two
gateway applications + the `@audit:ok` kernel derivative atoms `_x_deriv1` /
`_x_deriv2`.
@audit:ok -/
theorem convDensityAdd_deriv2_eq_gaussian
    (pX : ℝ → ℝ) (_hpX_nn : ∀ x, 0 ≤ pX x) (_hpX_int : Integrable pX volume)
    {s : ℝ} (hs : 0 < s) (z : ℝ)
    (bound1 : ℝ → ℝ) (hbound1_int : Integrable bound1 volume)
    (hF1_meas : ∀ ξ : ℝ,
      AEStronglyMeasurable
        (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume)
    (hF1_int : ∀ ξ : ℝ,
      Integrable (fun y => pX y * heatFlow_density_heat_equation_kernel s (ξ - y)) volume)
    (hF1'_meas : ∀ ξ : ℝ, AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))) volume)
    (hb1 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s)))‖ ≤ bound1 y)
    (bound2 : ℝ → ℝ) (hbound2_int : Integrable bound2 volume)
    (hF2_int : Integrable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (z - y)
        * (-((z - y) / s)))) volume)
    (hF2'_meas : AEStronglyMeasurable
      (fun y => pX y * (heatFlow_density_heat_equation_kernel s (z - y)
        * ((z - y) ^ 2 / s ^ 2 - 1 / s))) volume)
    (hb2 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      ‖pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * ((ξ - y) ^ 2 / s ^ 2 - 1 / s))‖ ≤ bound2 y) :
    deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))) z
      = ∫ y, pX y * (gaussianPDFReal 0 ⟨s, hs.le⟩ (z - y)
          * ((z - y) ^ 2 / s ^ 2 - 1 / s)) ∂volume := by
  -- STEP 1: identify `deriv (convDensityAdd pX g_s)` as the 1st-derivative integral function.
  have hd1 := convDensityAdd_deriv1_gaussian_eq pX hs bound1 hbound1_int hF1_meas hF1_int
    hF1'_meas hb1
  rw [hd1]
  -- The 1st-derivative function, in kernel form (s>0, all ζ).
  have hd1_kernel : (fun ζ : ℝ => ∫ y, pX y * (gaussianPDFReal 0 ⟨s, hs.le⟩ (ζ - y)
        * (-((ζ - y) / s))) ∂volume)
      = (fun ζ : ℝ => ∫ y, pX y * (heatFlow_density_heat_equation_kernel s (ζ - y)
          * (-((ζ - y) / s))) ∂volume) := by
    funext ζ
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [heatFlow_density_heat_equation_kernel_eq hs (ζ - y)]
  rw [hd1_kernel]
  -- STEP 2: differentiate the kernel-form 1st-derivative integral at `z` via the gateway.
  -- per-y spatial 2nd-derivative HasDerivAt (kernel `_x_deriv2` chained through `ξ ↦ ξ - y`).
  have hdiff2 : ∀ᵐ y ∂volume, ∀ ξ ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun ξ => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
          * (-((ξ - y) / s))))
        (pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
          * ((ξ - y) ^ 2 / s ^ 2 - 1 / s))) ξ := by
    filter_upwards with y
    intro ξ _
    have hk := heatFlow_density_heat_equation_kernel_x_deriv2 hs (ξ - y)
    have hshift : HasDerivAt (fun ξ : ℝ => ξ - y) 1 ξ := by
      simpa using (hasDerivAt_id ξ).sub_const y
    have hcomp := hk.comp ξ hshift
    simp only [mul_one] at hcomp
    exact hcomp.const_mul (pX y)
  have hgate2 :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun ξ y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * (-((ξ - y) / s))))
      (F' := fun ξ y => pX y * (heatFlow_density_heat_equation_kernel s (ξ - y)
        * ((ξ - y) ^ 2 / s ^ 2 - 1 / s)))
      (bound := bound2) (Filter.univ_mem)
      (Filter.Eventually.of_forall hF1'_meas) hF2_int hF2'_meas
      hb2 hbound2_int hdiff2
  -- `hgate2.2 : HasDerivAt (1st-deriv kernel function) (∫ y, pX y · kernel·((z-y)²/s²-1/s)) z`
  rw [hgate2.2.deriv]
  -- rewrite the kernel back to `gaussianPDFReal` inside the integral.
  refine integral_congr_ae ?_
  filter_upwards with y
  rw [heatFlow_density_heat_equation_kernel_eq hs (z - y)]

end InformationTheory.Shannon.EPIConvDensitySecondDeriv
