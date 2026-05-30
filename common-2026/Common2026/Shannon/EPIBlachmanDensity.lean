import Common2026.Shannon.EPIConvDensity
import Common2026.Shannon.FisherInfoV2
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
# EPI Blachman — explicit density route (S2 + S3, condExp 不使用)

Phase 3b of `docs/shannon/epi-wall-reattack-plan.md` (density-route, condExp-free).
Consumes the Phase 3a gateway `convDensityAdd_hasDerivAt_of_regular`
(`EPIConvDensity.lean:187`, `@audit:ok`) and builds, *without any
`condExp`/`condDistrib`/disintegration*:

* `condDensityX fX fY z x := fX x * fY (z - x) / convDensityAdd fX fY z`
  — the conditional density `p_{X|Z}(x|z)` written as an explicit ratio of
  Bochner integrands.
* `condDensityX_integral_eq_one` — normalization `∫ x, p_{X|Z}(x|z) dx = 1`.
* `symm_deriv_integral_eq` (**S2**) — symmetric derivative identity
  `∫ x, deriv fX x · fY (z - x) = ∫ x, fX x · deriv fY (z - x)` (both `= p_Z'(z)`),
  obtained from the genuine gateway applied in both factor orders +
  `convDensityAdd_comm` + the reflection substitution.
* `score_conv_eq_weighted_integral` (**S3**, the Blachman core) — for any `λ`,
  with `W_λ(x,z) := λ · logDeriv fX x + (1-λ) · logDeriv fY (z-x)`,
  `logDeriv (convDensityAdd fX fY) z = ∫ x, W_λ x z · p_{X|Z}(x|z) dx`.
  This is the score-of-convolution representation written as an explicit
  probability-weighted integral, the substitute for the disintegration bridge.

All bundled hypotheses are **regularity preconditions** (`IsRegularDensityV2`,
boundedness of the smooth factor and its derivative, integrability of the score
products, positivity of `p_Z`). None is a load-bearing bundling of the score
identity itself — see CLAUDE.md「検証の誠実性」.
-/

namespace InformationTheory.Shannon.EPIBlachmanDensity

open MeasureTheory Real
open scoped ENNReal NNReal
open Common2026.Shannon.FisherInfoV2
open InformationTheory.Shannon.EPIConvDensity

/-- **Conditional density** `p_{X|Z}(x|z) := fX(x) · fY(z - x) / p_Z(z)`, where
`p_Z = convDensityAdd fX fY`. Explicit ratio form (no `condDistrib`). -/
noncomputable def condDensityX (fX fY : ℝ → ℝ) (z x : ℝ) : ℝ :=
  fX x * fY (z - x) / convDensityAdd fX fY z

/-- **Score weight** `W_λ(x,z) := λ · logDeriv fX x + (1-λ) · logDeriv fY (z - x)`. -/
noncomputable def scoreWeight (fX fY : ℝ → ℝ) (lam z x : ℝ) : ℝ :=
  lam * logDeriv fX x + (1 - lam) * logDeriv fY (z - x)

/-- **Normalization** of the conditional density: `∫ x, p_{X|Z}(x|z) dx = 1`.

Numerator `∫ x, fX x · fY (z - x) = convDensityAdd fX fY z = p_Z(z)` (by
definition), divided by `p_Z(z) > 0`.

`hpZ` is a regularity precondition (positivity of the convolution density at `z`,
satisfied whenever `fX, fY > 0` are integrable).

@audit:ok — genuine: numerator `∫ fX·fY(z-·) = convDensityAdd` is `rfl`, divided
by genuine positivity `hpZ` (`div_self`); not a degenerate/vacuous use of `0 < p_Z`.
sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). -/
theorem condDensityX_integral_eq_one (fX fY : ℝ → ℝ) (z : ℝ)
    (hpZ : 0 < convDensityAdd fX fY z) :
    ∫ x, condDensityX fX fY z x ∂volume = 1 := by
  unfold condDensityX
  -- `∫ x, fX x * fY (z - x) / p_Z(z) = (∫ x, fX x * fY (z - x)) / p_Z(z)`.
  rw [integral_div]
  -- numerator `∫ x, fX x * fY (z - x) = convDensityAdd fX fY z` by definition.
  have hnum : (∫ x, fX x * fY (z - x) ∂volume) = convDensityAdd fX fY z := rfl
  rw [hnum]
  exact div_self hpZ.ne'

/-- **S2 — symmetric derivative identity** of the convolution density:
`∫ x, deriv fX x · fY (z - x) = ∫ x, fX x · deriv fY (z - x)` (both `= p_Z'(z)`).

Genuine: apply the Phase 3a gateway `convDensityAdd_hasDerivAt_of_regular` in both
factor orders, use `convDensityAdd_comm` + derivative uniqueness, then the
volume-preserving reflection substitution `x ↦ z - x`.

@audit:ok — all hyps are regularity preconditions (`IsRegularDensityV2` =
diff/pos/tail/∫deriv=0, `Integrable`, `∃M` boundedness); none bundles the
conclusion. Conclusion derived from the `@audit:ok` gateway in both factor orders
+ `HasDerivAt.unique` + reflection. sorryAx-free. -/
theorem symm_deriv_integral_eq (fX fY : ℝ → ℝ) (z : ℝ)
    (hregX : IsRegularDensityV2 fX) (hregY : IsRegularDensityV2 fY)
    (hX_int : Integrable fX volume) (hY_int : Integrable fY volume)
    (hX_bdd : ∃ M : ℝ, ∀ w, |fX w| ≤ M) (hX'_bdd : ∃ M : ℝ, ∀ w, |deriv fX w| ≤ M)
    (hY_bdd : ∃ M : ℝ, ∀ w, |fY w| ≤ M) (hY'_bdd : ∃ M : ℝ, ∀ w, |deriv fY w| ≤ M) :
    ∫ x, deriv fX x * fY (z - x) ∂volume = ∫ x, fX x * deriv fY (z - x) ∂volume := by
  -- Gateway in order (fX, fY): derivative of `convDensityAdd fX fY` at z is
  -- `∫ x, fX x * deriv fY (z - x)`.
  have hderiv_XY :
      HasDerivAt (convDensityAdd fX fY)
        (∫ x, convDensityAddDeriv fX fY z x ∂volume) z :=
    convDensityAdd_hasDerivAt_of_regular fX fY z hregX hregY hX_int hY_bdd hY'_bdd
  -- Gateway in order (fY, fX): derivative of `convDensityAdd fY fX` at z is
  -- `∫ x, fY x * deriv fX (z - x)`.
  have hderiv_YX :
      HasDerivAt (convDensityAdd fY fX)
        (∫ x, convDensityAddDeriv fY fX z x ∂volume) z :=
    convDensityAdd_hasDerivAt_of_regular fY fX z hregY hregX hY_int hX_bdd hX'_bdd
  -- `convDensityAdd fY fX = convDensityAdd fX fY`, so both are `HasDerivAt` of the
  -- same function at z; derivatives are unique.
  rw [convDensityAdd_comm fY fX] at hderiv_YX
  have huniq :
      (∫ x, convDensityAddDeriv fX fY z x ∂volume)
        = ∫ x, convDensityAddDeriv fY fX z x ∂volume :=
    hderiv_XY.unique hderiv_YX
  -- Unfold the derivative integrands.
  simp only [convDensityAddDeriv] at huniq
  -- huniq : ∫ x, fX x * deriv fY (z - x) = ∫ x, fY x * deriv fX (z - x)
  -- Reflection substitution `x ↦ z - x` on `g x := fY (z - x) * deriv fX x`.
  have hrefl := MeasureTheory.integral_sub_left_eq_self
      (fun x => fY (z - x) * deriv fX x) (μ := volume) z
  simp only [sub_sub_cancel] at hrefl
  -- hrefl : ∫ x, fY x * deriv fX (z - x) = ∫ x, fY (z - x) * deriv fX x
  rw [huniq, hrefl]
  -- goal : ∫ x, deriv fX x * fY (z - x) = ∫ x, fY (z - x) * deriv fX x
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))

/-- **S3 — score representation (Blachman core, condExp 不使用).**

For any `λ`, with `W_λ(x,z) := λ · logDeriv fX x + (1-λ) · logDeriv fY (z - x)`,
`logDeriv (convDensityAdd fX fY) z = ∫ x, W_λ x z · p_{X|Z}(x|z) dx`.

Proof skeleton (explicit Bochner integrals + cancellation, NO disintegration):

* `logDeriv p_Z z = p_Z'(z) / p_Z(z)` (gateway `HasDerivAt` + `logDeriv_apply`).
* `∫ W_λ · p_{X|Z} = (1/p_Z) ∫ W_λ · fX(x) fY(z-x)`.
* `W_λ · fX(x) fY(z-x) = λ (logDeriv fX x · fX x) fY(z-x) + (1-λ) fX x (logDeriv fY(z-x) · fY(z-x))`,
  and `logDeriv f · f = deriv f` pointwise (positivity).
* `∫ deriv fX(x) fY(z-x) = p_Z'(z)` (S2) and `∫ fX(x) deriv fY(z-x) = p_Z'(z)`
  (gateway derivative).  Numerator `= λ p_Z' + (1-λ) p_Z' = p_Z'`.  Divide by `p_Z`.

`h_int_W` is the regularity precondition that the weighted integrand is integrable.

@audit:ok — NOT load-bearing: no hyp contains `logDeriv (convDensityAdd …)` nor
the score equality; all hyps are regularity (`IsRegularDensityV2`, `∃M`,
`Integrable`, `0 < p_Z`). Core-reconstruction test passes — conclusion is genuinely
assembled (LHS via gateway `HasDerivAt`+`logDeriv_apply`; RHS via pointwise
`logDeriv f·f = deriv f` cancellation + S2 `symm_deriv_integral_eq`), not handed by
a hypothesis. condExp/condDistrib/disintegration absent from body + imports
(density route honest). sorryAx-free (`#print axioms` = standard 3). -/
theorem score_conv_eq_weighted_integral (fX fY : ℝ → ℝ) (lam z : ℝ)
    (hregX : IsRegularDensityV2 fX) (hregY : IsRegularDensityV2 fY)
    (hX_int : Integrable fX volume) (hY_int : Integrable fY volume)
    (hX_bdd : ∃ M : ℝ, ∀ w, |fX w| ≤ M) (hX'_bdd : ∃ M : ℝ, ∀ w, |deriv fX w| ≤ M)
    (hY_bdd : ∃ M : ℝ, ∀ w, |fY w| ≤ M) (hY'_bdd : ∃ M : ℝ, ∀ w, |deriv fY w| ≤ M)
    (hpZ : 0 < convDensityAdd fX fY z)
    (hint_X : Integrable (fun x => deriv fX x * fY (z - x)) volume)
    (hint_Y : Integrable (fun x => fX x * deriv fY (z - x)) volume) :
    logDeriv (convDensityAdd fX fY) z
      = ∫ x, scoreWeight fX fY lam z x * condDensityX fX fY z x ∂volume := by
  -- abbreviation `P := p_Z'(z) = ∫ x, fX x * deriv fY (z - x)`.
  set P : ℝ := ∫ x, fX x * deriv fY (z - x) ∂volume with hP_def
  -- (1) LHS: `logDeriv p_Z z = P / p_Z(z)`.
  have hderiv :
      HasDerivAt (convDensityAdd fX fY)
        (∫ x, convDensityAddDeriv fX fY z x ∂volume) z :=
    convDensityAdd_hasDerivAt_of_regular fX fY z hregX hregY hX_int hY_bdd hY'_bdd
  have hderiv_val : (∫ x, convDensityAddDeriv fX fY z x ∂volume) = P := by
    simp only [convDensityAddDeriv, hP_def]
  rw [hderiv_val] at hderiv
  have hLHS : logDeriv (convDensityAdd fX fY) z = P / convDensityAdd fX fY z := by
    rw [logDeriv_apply, hderiv.deriv]
  rw [hLHS]
  -- (2) RHS: pull out `1 / p_Z(z)`.
  have hRHS :
      (∫ x, scoreWeight fX fY lam z x * condDensityX fX fY z x ∂volume)
        = (∫ x, scoreWeight fX fY lam z x * (fX x * fY (z - x)) ∂volume)
            / convDensityAdd fX fY z := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    unfold condDensityX
    field_simp
  rw [hRHS]
  -- (3) numerator `∫ scoreWeight · fX(x) fY(z-x) = P`.
  congr 1
  -- pointwise rewrite: `scoreWeight · fX(x) fY(z-x)`
  --   `= lam · (deriv fX x · fY (z - x)) + (1 - lam) · (fX x · deriv fY (z - x))`.
  have hpt : ∀ x,
      scoreWeight fX fY lam z x * (fX x * fY (z - x))
        = lam * (deriv fX x * fY (z - x))
            + (1 - lam) * (fX x * deriv fY (z - x)) := by
    intro x
    unfold scoreWeight
    have hsx : logDeriv fX x * fX x = deriv fX x := by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregX.pos x).ne']
    have hsy : logDeriv fY (z - x) * fY (z - x) = deriv fY (z - x) := by
      rw [logDeriv_apply, div_mul_cancel₀ _ (hregY.pos (z - x)).ne']
    -- expand and substitute the two score-times-density cancellations.
    calc
      (lam * logDeriv fX x + (1 - lam) * logDeriv fY (z - x)) * (fX x * fY (z - x))
          = lam * (logDeriv fX x * fX x) * fY (z - x)
              + (1 - lam) * (logDeriv fY (z - x) * fY (z - x)) * fX x := by ring
      _ = lam * (deriv fX x * fY (z - x))
              + (1 - lam) * (fX x * deriv fY (z - x)) := by
            rw [hsx, hsy]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  -- split the integral and use S2 to identify both terms with `P`.
  rw [integral_add (by exact hint_X.const_mul lam) (by exact hint_Y.const_mul (1 - lam)),
    integral_const_mul, integral_const_mul]
  -- `∫ deriv fX · fY(z-x) = ∫ fX · deriv fY(z-x) = P` by S2.
  have hS2 := symm_deriv_integral_eq fX fY z hregX hregY hX_int hY_int
    hX_bdd hX'_bdd hY_bdd hY'_bdd
  rw [hS2]
  -- both integrals now equal `P`.
  rw [← hP_def]
  ring

/-! ## Phase 3c — convex Fisher bound (density route step 4-5)

This section consumes S2/S3 (above) and assembles the **convex Fisher bound**

`(fisherInfoOfDensity (convDensityAdd fX fY)).toReal ≤
   lam² · (fisherInfoOfDensity fX).toReal + (1-lam)² · (fisherInfoOfDensity fY).toReal`

for `0 ≤ lam ≤ 1`, via:

* **atom A** (`fisherInfoOfDensity_toReal_eq_integral`) — the lintegral↔Bochner
  bridge `(fisherInfoOfDensity f).toReal = ∫ x, (logDeriv f x)² · f x ∂volume`
  (genuine, `integral_eq_lintegral_of_nonneg_ae` + `ENNReal.ofReal_mul`).
* **S4 pointwise Cauchy-Schwarz** (`score_sq_le_weighted_integral`) — probability
  weighted CS: `(logDeriv p_Z z)² ≤ ∫ x, (W_λ x z)² · p_{X|Z}(x|z) dx`.
* the Tonelli swap + 3-term evaluation (`λ²·J_X + (1-λ)²·J_Y`, cross-term `= 0`).
-/

/-- **atom A — lintegral↔Bochner bridge** for the Fisher information of a density.

`(fisherInfoOfDensity f).toReal = ∫ x, (logDeriv f x)² · f x ∂volume`.

`fisherInfoOfDensity f = ∫⁻ x, ofReal((logDeriv f x)²) · ofReal(f x)` by definition;
`ofReal((logDeriv f x)² · f x) = ofReal((logDeriv f x)²) · ofReal(f x)` by
`ENNReal.ofReal_mul` (both factors nonneg), and the integrand
`(logDeriv f x)² · f x` is nonnegative (`hpos`), so
`integral_eq_lintegral_of_nonneg_ae` applies.

`hpos` (`f ≥ 0`) and `hint` (Bochner-integrability of the squared-score density)
are regularity preconditions, satisfied by any genuine probability density with
finite Fisher information; neither bundles the Fisher-info value.

Genuine (0 sorry): pure lintegral↔Bochner bridge, no Blachman content.

@audit:ok — independent audit: hyps `hpos`/`hint` are regularity preconditions
(nonneg + integrability of the squared-score density), neither bundles the
Fisher-info value. Conclusion genuinely assembled
(`integral_eq_lintegral_of_nonneg_ae` + `ENNReal.ofReal_mul`). `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (sorryAx-free, verified transiently). -/
theorem fisherInfoOfDensity_toReal_eq_integral (f : ℝ → ℝ)
    (hpos : ∀ x, 0 ≤ f x)
    (hint : Integrable (fun x => (logDeriv f x) ^ 2 * f x) volume) :
    (fisherInfoOfDensity f).toReal = ∫ x, (logDeriv f x) ^ 2 * f x ∂volume := by
  -- Bochner ↔ lintegral on the nonneg integrand `g x := (logDeriv f x)² · f x`.
  have hg_nonneg : 0 ≤ᵐ[volume] fun x => (logDeriv f x) ^ 2 * f x :=
    Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hpos x))
  rw [integral_eq_lintegral_of_nonneg_ae hg_nonneg hint.1]
  -- `fisherInfoOfDensity f = ∫⁻ ofReal((logDeriv f x)²) · ofReal(f x)`; combine via `ofReal_mul`.
  congr 1
  unfold fisherInfoOfDensity
  refine lintegral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [ENNReal.ofReal_mul (sq_nonneg (logDeriv f x))]

/-- **S4 — probability-weighted pointwise Cauchy-Schwarz** of the score.

With `W_λ(x,z) := scoreWeight fX fY lam z x` and `p_{X|Z}(x|z) := condDensityX fX fY z x`
(a probability weight: `≥ 0`, `∫ = 1`), and the S3 representation
`logDeriv p_Z z = ∫ x, W_λ · p_{X|Z}`, Jensen / Cauchy-Schwarz gives

`(logDeriv (convDensityAdd fX fY) z)² ≤ ∫ x, (W_λ x z)² · p_{X|Z}(x|z) dx`.

`hpZ` (positivity of `p_Z(z)`) is a regularity precondition; the squared-weight
integrability `hint_Wsq` is a regularity precondition on admissible densities.
None of the hyps bundles the conclusion inequality.

Genuine (0 sorry): with the probability measure
`μ := volume.withDensity (fun x => ENNReal.ofReal (condDensityX fX fY z x))`
(`IsProbabilityMeasure` from 3b `condDensityX_integral_eq_one` via
`ofReal_integral_eq_lintegral_ofReal`), S4 is exactly Jensen for the convex `(·)²`:
`Even.convexOn_pow` + `ConvexOn.map_integral_le`
(`Mathlib/Analysis/Convex/Integral.lean:199`, `[IsProbabilityMeasure μ]`,
`g (∫ f ∂μ) ≤ ∫ g∘f ∂μ`) composed with the change-of-variables
`integral_withDensity_eq_integral_toReal_smul₀`
(`Bochner/ContinuousLinearMap.lean:310`) to rewrite `∫ · ∂μ = ∫ condDensityX·· ∂volume`,
and S3 `score_conv_eq_weighted_integral` to identify `∫ scoreWeight ∂μ` with
`logDeriv p_Z z`. condExp/condDistrib/disintegration absent (density route honest).

`hcond_int` (integrability of the conditional density), `hint_W` (integrability of
the score weight against `condDensityX`) and `hint_Wsq` are regularity preconditions
on admissible densities; none bundles the conclusion inequality.

@audit:ok — independent audit (2026-05-30): no hyp contains the score-square
inequality. `hpZ` (positivity), `hcond_int`/`hint_W`/`hint_Wsq` (Integrable
side-conditions) and the boundedness hyps are all regularity preconditions; none
bundles the conclusion. `IsProbabilityMeasure μ` is genuinely derived from 3b
`condDensityX_integral_eq_one` (mass = 1, not faked). Conclusion assembled via
`ConvexOn.map_integral_le` (Jensen for `(·)²`) + `integral_withDensity_…` CoV + S3.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx-free, verified
transiently — S4 body is genuine 0-sorry, no transitive sorry). -/
theorem score_sq_le_weighted_integral (fX fY : ℝ → ℝ) (lam z : ℝ)
    (hregX : IsRegularDensityV2 fX) (hregY : IsRegularDensityV2 fY)
    (hX_int : Integrable fX volume) (hY_int : Integrable fY volume)
    (hX_bdd : ∃ M : ℝ, ∀ w, |fX w| ≤ M) (hX'_bdd : ∃ M : ℝ, ∀ w, |deriv fX w| ≤ M)
    (hY_bdd : ∃ M : ℝ, ∀ w, |fY w| ≤ M) (hY'_bdd : ∃ M : ℝ, ∀ w, |deriv fY w| ≤ M)
    (hpZ : 0 < convDensityAdd fX fY z)
    (hint_X : Integrable (fun x => deriv fX x * fY (z - x)) volume)
    (hint_Y : Integrable (fun x => fX x * deriv fY (z - x)) volume)
    (hcond_int : Integrable (condDensityX fX fY z) volume)
    (hint_W :
        Integrable (fun x => scoreWeight fX fY lam z x * condDensityX fX fY z x) volume)
    (hint_Wsq :
        Integrable (fun x => (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x) volume) :
    (logDeriv (convDensityAdd fX fY) z) ^ 2
      ≤ ∫ x, (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x ∂volume := by
  -- Conditional density is nonneg (ratio of nonneg `fX·fY(z-·)` by positive `p_Z`).
  have hcond_nonneg : ∀ x, 0 ≤ condDensityX fX fY z x := by
    intro x
    unfold condDensityX
    exact div_nonneg (mul_nonneg (hregX.pos x).le (hregY.pos (z - x)).le) hpZ.le
  -- Density `d x := ENNReal.ofReal (condDensityX fX fY z x)`, ae-measurable + finite.
  set d : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (condDensityX fX fY z x) with hd_def
  have hd_meas : AEMeasurable d volume :=
    (hcond_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hd_lt_top : ∀ᵐ x ∂volume, d x < ∞ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  -- Probability measure `μ := volume.withDensity d`; mass = ∫⁻ d = ofReal(∫ condDensityX) = 1.
  set μ : Measure ℝ := volume.withDensity d with hμ_def
  have hμ_mass : μ Set.univ = 1 := by
    rw [hμ_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [hd_def, ← ofReal_integral_eq_lintegral_ofReal hcond_int
        (Filter.Eventually.of_forall hcond_nonneg),
      condDensityX_integral_eq_one fX fY z hpZ, ENNReal.ofReal_one]
  have : IsProbabilityMeasure μ := ⟨hμ_mass⟩
  -- Change of variables: `∫ g ∂μ = ∫ condDensityX·g ∂volume` for `g : ℝ → ℝ`.
  have hCoV : ∀ g : ℝ → ℝ,
      ∫ x, g x ∂μ = ∫ x, condDensityX fX fY z x * g x ∂volume := by
    intro g
    rw [hμ_def, integral_withDensity_eq_integral_toReal_smul₀ hd_meas hd_lt_top]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hd_def, smul_eq_mul, ENNReal.toReal_ofReal (hcond_nonneg x)]
  -- (1) `∫ scoreWeight ∂μ = logDeriv p_Z z` (S3 + CoV + mul_comm).
  have hmean : ∫ x, scoreWeight fX fY lam z x ∂μ = logDeriv (convDensityAdd fX fY) z := by
    rw [hCoV]
    rw [score_conv_eq_weighted_integral fX fY lam z hregX hregY hX_int hY_int
      hX_bdd hX'_bdd hY_bdd hY'_bdd hpZ hint_X hint_Y]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [mul_comm]
  -- (2) Jensen for the convex `(·)²` on `μ`.
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow (by norm_num)
  have hjensen :
      (∫ x, scoreWeight fX fY lam z x ∂μ) ^ 2
        ≤ ∫ x, (scoreWeight fX fY lam z x) ^ 2 ∂μ := by
    have hfi : Integrable (scoreWeight fX fY lam z) μ := by
      rw [hμ_def, integrable_withDensity_iff_integrable_smul₀' hd_meas hd_lt_top]
      refine (hint_W.congr (Filter.Eventually.of_forall (fun x => ?_)))
      simp only [hd_def, smul_eq_mul, ENNReal.toReal_ofReal (hcond_nonneg x), mul_comm]
    have hgi : Integrable ((fun x : ℝ => x ^ 2) ∘ scoreWeight fX fY lam z) μ := by
      rw [hμ_def, integrable_withDensity_iff_integrable_smul₀' hd_meas hd_lt_top]
      refine (hint_Wsq.congr (Filter.Eventually.of_forall (fun x => ?_)))
      simp only [hd_def, Function.comp_apply, smul_eq_mul,
        ENNReal.toReal_ofReal (hcond_nonneg x), mul_comm]
    have hcont : ContinuousOn (fun x : ℝ => x ^ 2) Set.univ :=
      (continuous_pow 2).continuousOn
    have := hconv.map_integral_le hcont isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hfi hgi
    simpa only [Function.comp_apply] using this
  -- Assemble: rewrite the mean via S3, then push the RHS through CoV.
  rw [← hmean]
  refine hjensen.trans (le_of_eq ?_)
  rw [hCoV]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only [mul_comm]

/-- **Convex Fisher bound (density route, Phase 3c main result).**

For `0 ≤ lam ≤ 1`,
`(fisherInfoOfDensity (convDensityAdd fX fY)).toReal
   ≤ lam² · (fisherInfoOfDensity fX).toReal + (1-lam)² · (fisherInfoOfDensity fY).toReal`.

Proof shape (explicit density route, condExp-free):

* `J_sum = ∫ z, (logDeriv p_Z z)² · p_Z(z) dz` (atom A on `p_Z = convDensityAdd fX fY`).
* `(logDeriv p_Z z)² ≤ ∫ x, W_λ² · p_{X|Z}` pointwise (S4 `score_sq_le_weighted_integral`).
* integrate against `p_Z`, cancel `p_{X|Z}·p_Z = fX(x)·fY(z-x)`, swap order (Tonelli),
  expand `W_λ² = λ²s_X² + (1-λ)²s_Y² + 2λ(1-λ)s_X s_Y`:
  * `λ²` term `= λ²·J_X` (`∫_z fY(z-x) dz = 1` by translation invariance + normalization),
  * `(1-λ)²` term `= (1-λ)²·J_Y`,
  * cross term `= 0` (`∫ logDeriv fX · fX = 0` and `∫ logDeriv fY · fY = 0`,
    `integral_logDeriv_density_eq_zero`).

All bundled hypotheses are regularity preconditions (`IsRegularDensityV2`,
boundedness, integrability side-conditions, normalization `∫ = 1`, positivity of
`p_Z`); none bundles the inequality core, which lives in the `sorry` below and in
the S4 lemma.

Independent audit (2026-05-30): reclassified `wall:stam-blachman` →
`plan:epi-wall-reattack-plan`. Closability is transitive on S4
(`score_sq_le_weighted_integral`, now genuinely closed via `ConvexOn.map_integral_le`
on a withDensity probability measure) plus parts all present: Tonelli
`integral_integral_swap` (`Mathlib/MeasureTheory/Integral/Prod.lean`), cross-term
`= 0` via `integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:158`, repo), and
atom A `fisherInfoOfDensity_toReal_eq_integral` (genuine, `@audit:ok`). No separate
genuine Mathlib gap; not a wall.

Phase 3c-cont status (2026-05-30): the atom-A reduction (LHS/RHS → Bochner) and the
S4 pointwise→integrated monotone step are genuinely assembled below; the residual
`sorry` is the Tonelli order-swap + 3-term evaluation of the post-swap integral
(`λ²·J_X + (1-λ)²·J_Y` via translation invariance + `integral_logDeriv_density_eq_zero`
cross-term-zero). That step requires `∀z`-quantified product / fibre integrability
preconditions (`hint_W_z`, `hint_Wsq_z`, `hcond_int_z`, the product-measure
`Integrable (uncurry ...)`), threaded below as honest regularity preconditions.
The remaining `sorry` is purely the analytic 3-term Tonelli evaluation, not a wall.

Independent audit (2026-05-30): honest residual, classification confirmed. All
preconditions are regularity — the `∀z` Integrable hyps (`hint_X/Y/cond_int/W/Wsq`)
feed S4 per-z; `hint_inner` is the Integrable side-condition of the RHS integrand
required by `integral_mono_ae` (asserts integrability, NOT the cross-term=0 nor the
3-term value); `hint_fisherX/Y/Z` are atom-A integrability preconditions. None
bundles the inequality core, which lives in the `sorry`. Steps (a) S4-monotone via
`integral_mono_ae` and (b) `condDensityX·p_Z` cancellation are genuine. The `sorry`
(Tonelli swap + 3-term eval) is plan-closable: `integral_logDeriv_density_eq_zero`
(FisherInfoV2.lean:158, repo), Tonelli, atom A, S4 (`@audit:ok`) all present → not a
Mathlib wall. Plan `docs/shannon/epi-wall-reattack-plan.md` exists.
@residual(plan:epi-wall-reattack-plan) -/
theorem convex_fisher_bound (fX fY : ℝ → ℝ) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hregX : IsRegularDensityV2 fX) (hregY : IsRegularDensityV2 fY)
    (hX_int : Integrable fX volume) (hY_int : Integrable fY volume)
    (hX_bdd : ∃ M : ℝ, ∀ w, |fX w| ≤ M) (hX'_bdd : ∃ M : ℝ, ∀ w, |deriv fX w| ≤ M)
    (hY_bdd : ∃ M : ℝ, ∀ w, |fY w| ≤ M) (hY'_bdd : ∃ M : ℝ, ∀ w, |deriv fY w| ≤ M)
    (hnormX : ∫ x, fX x ∂volume = 1) (hnormY : ∫ x, fY x ∂volume = 1)
    (hpZ : ∀ z, 0 < convDensityAdd fX fY z)
    (hint_X : ∀ z, Integrable (fun x => deriv fX x * fY (z - x)) volume)
    (hint_Y : ∀ z, Integrable (fun x => fX x * deriv fY (z - x)) volume)
    (hcond_int : ∀ z, Integrable (condDensityX fX fY z) volume)
    (hint_W : ∀ z,
        Integrable (fun x => scoreWeight fX fY lam z x * condDensityX fX fY z x) volume)
    (hint_Wsq : ∀ z,
        Integrable (fun x => (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x) volume)
    (hint_inner :
        Integrable (fun z =>
          (∫ x, (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x ∂volume)
            * convDensityAdd fX fY z) volume)
    (hint_fisherX : Integrable (fun x => (logDeriv fX x) ^ 2 * fX x) volume)
    (hint_fisherY : Integrable (fun x => (logDeriv fY x) ^ 2 * fY x) volume)
    (hint_fisherZ :
        Integrable (fun z => (logDeriv (convDensityAdd fX fY) z) ^ 2 * convDensityAdd fX fY z)
          volume) :
    (fisherInfoOfDensity (convDensityAdd fX fY)).toReal
      ≤ lam ^ 2 * (fisherInfoOfDensity fX).toReal
          + (1 - lam) ^ 2 * (fisherInfoOfDensity fY).toReal := by
  -- atom A converts all three Fisher informations to Bochner integrals.
  rw [fisherInfoOfDensity_toReal_eq_integral (convDensityAdd fX fY)
        (fun z => (hpZ z).le) hint_fisherZ,
      fisherInfoOfDensity_toReal_eq_integral fX (fun x => (hregX.pos x).le) hint_fisherX,
      fisherInfoOfDensity_toReal_eq_integral fY (fun x => (hregY.pos x).le) hint_fisherY]
  -- Reduced goal: `∫ z, (logDeriv p_Z z)²·p_Z z ≤ λ²·∫ s_X²·fX + (1-λ)²·∫ s_Y²·fY`.
  -- (a) S4 pointwise → integrate against `p_Z ≥ 0` (monotone).
  have hmono :
      (∫ z, (logDeriv (convDensityAdd fX fY) z) ^ 2 * convDensityAdd fX fY z ∂volume)
        ≤ ∫ z, (∫ x, (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x ∂volume)
            * convDensityAdd fX fY z ∂volume := by
    refine integral_mono_ae hint_fisherZ hint_inner
      (Filter.Eventually.of_forall (fun z => ?_))
    have hS4 := score_sq_le_weighted_integral fX fY lam z hregX hregY hX_int hY_int
      hX_bdd hX'_bdd hY_bdd hY'_bdd (hpZ z) (hint_X z) (hint_Y z) (hcond_int z)
      (hint_W z) (hint_Wsq z)
    exact mul_le_mul_of_nonneg_right hS4 (hpZ z).le
  refine hmono.trans (le_of_eq ?_)
  -- (b) cancel `condDensityX z x · p_Z z = fX x · fY (z - x)`, pull `p_Z z` into the inner ∫.
  have hb : ∀ z,
      (∫ x, (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x ∂volume)
          * convDensityAdd fX fY z
        = ∫ x, (scoreWeight fX fY lam z x) ^ 2 * (fX x * fY (z - x)) ∂volume := by
    intro z
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    show (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x * convDensityAdd fX fY z
      = (scoreWeight fX fY lam z x) ^ 2 * (fX x * fY (z - x))
    unfold condDensityX
    rw [mul_assoc, div_mul_cancel₀ _ (hpZ z).ne']
  simp only [hb]
  -- Remaining: (c) Tonelli order-swap `∫_z ∫_x W²·fX(x)·fY(z-x) = ∫_x ∫_z (...)`
  -- (needs product-measure `Integrable (uncurry ...)`), then (d) the 3-term evaluation
  -- expanding `W² = λ²s_X(x)² + (1-λ)²s_Y(z-x)² + 2λ(1-λ)s_X(x)s_Y(z-x)`:
  --   λ² term  → λ²·∫ s_X²·fX  (∫_z fY(z-x) dz = 1 by `integral_sub_left_eq_self` + `hnormY`)
  --   (1-λ)² term → (1-λ)²·∫ s_Y²·fY  (translation + `hnormX`)
  --   cross term → 0  (`integral_logDeriv_density_eq_zero` on each factor).
  -- Steps (a) S4-monotone + (b) condDensityX·p_Z cancellation above are genuine; this
  -- residual is purely the analytic Tonelli evaluation (not a Mathlib wall).
  -- @residual(plan:epi-wall-reattack-plan)
  sorry

end InformationTheory.Shannon.EPIBlachmanDensity
