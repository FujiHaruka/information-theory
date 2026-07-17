import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Pre-equalizer: bounded-below endomorphisms are invertible with norm control

The geometric core of the Shannon–Hartley achievability route ("route (ii)", the operator lower
bound). A linear endomorphism `A` of a finite-dimensional inner-product space that is bounded below,
`c ‖v‖² ≤ ‖A v‖²` with `c > 0`, is surjective, and every target `t` has a preimage `a` whose energy
is controlled: `‖a‖² ≤ (1/c) ‖t‖²`. This replaces the matrix-inverse `G⁻¹` step of the informal
sketch with a self-contained finite-dimensional fact.
-/

namespace InformationTheory.Shannon.ShannonHartleyPreequalizer

open scoped InnerProductSpace

/-- **Pre-equalizer.** A bounded-below (`c ‖v‖² ≤ ‖A v‖²`, `c > 0`) linear endomorphism of a
finite-dimensional inner-product space is surjective with a norm-controlled preimage: every target
`t` has an `a` with `A a = t` and `‖a‖² ≤ (1/c) ‖t‖²`.

Injectivity: `A v = 0` forces `c ‖v‖² ≤ 0`, so `v = 0`. On a finite-dimensional space an injective
endomorphism is surjective, giving the preimage `a`; feeding it back through the lower bound and
dividing by `c > 0` yields the energy control. -/
theorem exists_preequalizer {n : ℕ} {c : ℝ} (hc : 0 < c)
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hbdd : ∀ v, c * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2) (t : EuclideanSpace ℝ (Fin n)) :
    ∃ a, A a = t ∧ ‖a‖ ^ 2 ≤ (1 / c) * ‖t‖ ^ 2 := by
  -- `A` is injective: `A v = 0 ⟹ c ‖v‖² ≤ 0 ⟹ v = 0`.
  have hinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).mpr fun v hv => ?_
    have h := hbdd v
    rw [hv, norm_zero] at h
    have hv2 : ‖v‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖v‖]
    have : ‖v‖ = 0 := by nlinarith [norm_nonneg v, sq_nonneg ‖v‖]
    exact norm_eq_zero.mp this
  -- Injective endomorphism of a finite-dimensional space is surjective.
  obtain ⟨a, ha⟩ := (LinearMap.injective_iff_surjective.mp hinj) t
  refine ⟨a, ha, ?_⟩
  -- Feed `a` through the lower bound and divide by `c > 0`.
  have h := hbdd a
  rw [ha] at h
  have hcinv : (0 : ℝ) < 1 / c := by positivity
  calc ‖a‖ ^ 2 = (1 / c) * (c * ‖a‖ ^ 2) := by field_simp
    _ ≤ (1 / c) * ‖t‖ ^ 2 := mul_le_mul_of_nonneg_left h hcinv.le

end InformationTheory.Shannon.ShannonHartleyPreequalizer
