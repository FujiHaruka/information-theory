import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Lifting an `L²` class to a genuine pointwise representative

The matched-filter receiver of a continuous-time AWGN code (`ContAwgnCode`) needs its test
functions to be honest `ℝ → ℝ` functions: `testFn_support` asks for the support to lie in `[0, T]`
*everywhere* (not just a.e.), and `testFn_orthonormal` states orthonormality as a *pointwise*
Lebesgue integral `∫ t, gᵢ t · gⱼ t`, not an `L²` inner product. The spectral assets that produce
the family, however, live in `Lp` as a.e.-equivalence classes.

This file bridges that gap for the real space `Lp ℝ 2 volume`. Given an `f : Lp ℝ 2 volume`
whose a.e. representative already vanishes a.e. off a measurable set `s`, its `s`-indicator
`ptRepr s f := s.indicator (⇑f)` is a genuine function that

* is supported in `s` *everywhere* (`support_ptRepr_subset`), because it is an indicator on `s`;
* still lies in `L²` (`memLp_ptRepr`);
* agrees with `⇑f` a.e. (`ptRepr_ae_eq`), so no `L²` content is lost.

The a.e. agreement turns the pointwise product integral into the `L²` inner product
(`integral_ptRepr_mul`), which upgrades an orthonormal family in `Lp ℝ 2 volume` (supported a.e.
in `[0, T]`) to a pointwise-orthonormal family of `[0, T]`-supported functions
(`exists_pointwise_orthonormal_of_orthonormal`) — exactly the three `ContAwgnCode.testFn`
regularity fields.
-/

namespace InformationTheory.Shannon.LpPointwise

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

/-- The pointwise representative of an `L²` class `f`, cut down to the set `s`: the genuine
function `s.indicator (⇑f)`. When `⇑f` already vanishes a.e. off `s`, this loses no `L²` content
(`ptRepr_ae_eq`) but gains an *everywhere* support bound (`support_ptRepr_subset`). -/
noncomputable def ptRepr (s : Set ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) : ℝ → ℝ :=
  s.indicator (⇑f)

/-- `ptRepr s f` is supported in `s` everywhere (it is an `s`-indicator). -/
theorem support_ptRepr_subset (s : Set ℝ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    Function.support (ptRepr s f) ⊆ s :=
  Set.support_indicator_subset

/-- `ptRepr s f` still lies in `L²`. -/
theorem memLp_ptRepr {s : Set ℝ} (hs : MeasurableSet s) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    MemLp (ptRepr s f) 2 volume :=
  (Lp.memLp f).indicator hs

/-- If `⇑f` vanishes a.e. off `s`, then `ptRepr s f` agrees with `⇑f` a.e. -/
theorem ptRepr_ae_eq {s : Set ℝ} (hs : MeasurableSet s) (f : Lp ℝ 2 (volume : Measure ℝ))
    (hf : (⇑f : ℝ → ℝ) =ᵐ[volume.restrict sᶜ] 0) :
    ptRepr s f =ᵐ[volume] (⇑f) :=
  indicator_ae_eq_of_restrict_compl_ae_eq_zero hs hf

/-- The pointwise product integral of two representatives equals the `L²` inner product of the
underlying classes, provided both vanish a.e. off `s`. -/
theorem integral_ptRepr_mul {s : Set ℝ} (hs : MeasurableSet s) (f g : Lp ℝ 2 (volume : Measure ℝ))
    (hf : (⇑f : ℝ → ℝ) =ᵐ[volume.restrict sᶜ] 0)
    (hg : (⇑g : ℝ → ℝ) =ᵐ[volume.restrict sᶜ] 0) :
    (∫ t, ptRepr s f t * ptRepr s g t) = ⟪f, g⟫ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ptRepr_ae_eq hs f hf, ptRepr_ae_eq hs g hg] with t htf htg
  rw [htf, htg, RCLike.inner_apply, conj_trivial]
  ring

/-- **Keystone.** An orthonormal family in `Lp ℝ 2 volume`, each member supported a.e. in
`[0, T]`, lifts to a family of genuine `ℝ → ℝ` functions that satisfy the three
`ContAwgnCode.testFn` regularity fields: everywhere-support in `[0, T]`, `MemLp`, and pointwise
orthonormality `∫ t, gᵢ t · gⱼ t = δᵢⱼ`. -/
theorem exists_pointwise_orthonormal_of_orthonormal {k : ℕ} {T : ℝ}
    (e : Fin k → Lp ℝ 2 (volume : Measure ℝ)) (he : Orthonormal ℝ e)
    (hsupp : ∀ i, (⇑(e i) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)ᶜ] 0) :
    ∃ g : Fin k → (ℝ → ℝ),
      (∀ i, Function.support (g i) ⊆ Set.Icc (0 : ℝ) T) ∧
      (∀ i, MemLp (g i) 2 volume) ∧
      (∀ i j, (∫ t, g i t * g j t) = if i = j then (1 : ℝ) else 0) := by
  refine ⟨fun i => ptRepr (Set.Icc (0 : ℝ) T) (e i), ?_, ?_, ?_⟩
  · intro i; exact support_ptRepr_subset _ _
  · intro i; exact memLp_ptRepr measurableSet_Icc _
  · intro i j
    rw [integral_ptRepr_mul measurableSet_Icc (e i) (e j) (hsupp i) (hsupp j)]
    exact orthonormal_iff_ite.mp he i j

end InformationTheory.Shannon.LpPointwise
