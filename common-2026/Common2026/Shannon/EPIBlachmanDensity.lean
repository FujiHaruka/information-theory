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

/-! ### Phase 3c-fin — Tonelli 3-term evaluation helpers

These three private lemmas evaluate each of the three terms obtained by expanding
`W_λ² = λ²·s_X(x)² + (1-λ)²·s_Y(z-x)² + 2λ(1-λ)·s_X(x)·s_Y(z-x)` inside the double
integral `∫_z ∫_x W_λ²·fX(x)·fY(z-x)`. Each uses `integral_integral_swap` (Tonelli,
Bochner) to put `z` innermost, then translation invariance `integral_sub_right_eq_self`
+ the normalizations / `integral_logDeriv_density_eq_zero` to collapse the inner `z`
integral. The product-measure integrability hypotheses (`Integrable (uncurry …)`) are
honest regularity preconditions (Gaussian-satisfied, load-bearing-free). -/

/-- **Term 1** (the `λ²` term): translation invariance pulls the inner `z` integral of
`fY (z - x)` to `1`, leaving `J_X`.

@audit:ok — independent audit (2026-05-30): `hnormY` (∫fY=1) is a normalization
regularity precondition; `hint1 : Integrable (uncurry …) (volume.prod volume)` is a
pure product-measure integrability precondition on the already-expanded `λ²` term
integrand (asserts integrability, not the integral's value — no core bundling).
Conclusion genuinely reconstructed: `integral_integral_swap` (Tonelli) +
`integral_sub_right_eq_self` (translation) + `hnormY`. Not handed by any hyp.
sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). -/
private theorem convex_fisher_term1 (fX fY : ℝ → ℝ)
    (hnormY : ∫ x, fY x ∂volume = 1)
    (hint1 :
        Integrable
          (Function.uncurry fun z x => (logDeriv fX x) ^ 2 * fX x * fY (z - x))
          (volume.prod volume)) :
    (∫ z, ∫ x, (logDeriv fX x) ^ 2 * fX x * fY (z - x) ∂volume ∂volume)
      = ∫ x, (logDeriv fX x) ^ 2 * fX x ∂volume := by
  -- Tonelli: put `z` innermost.
  rw [integral_integral_swap hint1]
  -- inner `z` integral of `fY (z - x)` is `∫ fY = 1`; pull constant out.
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  rw [show (fun z => (logDeriv fX x) ^ 2 * fX x * fY (z - x))
        = (fun z => ((logDeriv fX x) ^ 2 * fX x) * fY (z - x)) from rfl,
    integral_const_mul]
  have htr := MeasureTheory.integral_sub_right_eq_self fY (μ := volume) x
  rw [htr, hnormY, mul_one]

/-- **Term 2** (the `(1-λ)²` term): substitute `y = z - x` (translation), the inner `z`
integral becomes `J_Y`, and `∫_x fX = 1`.

@audit:ok — independent audit (2026-05-30): `hnormX` (∫fX=1) is a normalization
regularity precondition; `hint2 : Integrable (uncurry …) (volume.prod volume)` is a
pure product-measure integrability precondition on the already-expanded `(1-λ)²` term
integrand (no core bundling). Conclusion genuinely reconstructed:
`integral_integral_swap` (Tonelli) + `integral_sub_right_eq_self` (translation) +
`hnormX`. Not handed by any hyp.
sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). -/
private theorem convex_fisher_term2 (fX fY : ℝ → ℝ)
    (hnormX : ∫ x, fX x ∂volume = 1)
    (hint2 :
        Integrable
          (Function.uncurry fun z x => (logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x))
          (volume.prod volume)) :
    (∫ z, ∫ x, (logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x) ∂volume ∂volume)
      = ∫ y, (logDeriv fY y) ^ 2 * fY y ∂volume := by
  -- Tonelli: put `z` innermost.
  rw [integral_integral_swap hint2]
  -- inner `z` integral of `(logDeriv fY (z-x))²·fY (z-x)` is `J_Y` (translation), `fX x` is constant.
  have hinner : ∀ x : ℝ,
      (∫ z, (logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x) ∂volume)
        = fX x * ∫ y, (logDeriv fY y) ^ 2 * fY y ∂volume := by
    intro x
    rw [show (fun z => (logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x))
          = (fun z => fX x * ((logDeriv fY (z - x)) ^ 2 * fY (z - x))) from
        funext (fun z => by ring),
      integral_const_mul]
    have htr := MeasureTheory.integral_sub_right_eq_self
        (fun y => (logDeriv fY y) ^ 2 * fY y) (μ := volume) x
    rw [htr]
  simp only [hinner]
  rw [integral_mul_const, hnormX, one_mul]

/-- **Term 3** (the cross term): the inner `z` integral of `logDeriv fY (z-x)·fY (z-x)`
is `∫ logDeriv fY · fY = 0`, so the whole term vanishes.

@audit:ok — independent audit (2026-05-30): `hregY : IsRegularDensityV2 fY` is a
regularity precondition (diff/pos/tail/∫deriv=0), consumed only to invoke the
`@audit:ok` lemma `integral_logDeriv_density_eq_zero`; `hint3 : Integrable (uncurry
…) (volume.prod volume)` is a pure product-measure integrability precondition on the
already-expanded cross-term integrand (no core bundling). Conclusion (= 0) genuinely
reconstructed: `integral_integral_swap` (Tonelli) + `integral_sub_right_eq_self`
(translation) + `integral_logDeriv_density_eq_zero` (score-mean-zero). Not handed by
any hyp. sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`). -/
private theorem convex_fisher_cross (fX fY : ℝ → ℝ)
    (hregY : IsRegularDensityV2 fY)
    (hint3 :
        Integrable
          (Function.uncurry fun z x =>
            logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x)))
          (volume.prod volume)) :
    (∫ z, ∫ x, logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x))
        ∂volume ∂volume) = 0 := by
  -- Tonelli: put `z` innermost.
  rw [integral_integral_swap hint3]
  -- inner `z` integral of `logDeriv fY (z-x)·fY (z-x)` is `J_Y`-score = 0; pull constant out.
  have hinner : ∀ x : ℝ,
      (∫ z, logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x)) ∂volume) = 0 := by
    intro x
    rw [integral_const_mul]
    -- `∫ z, logDeriv fY (z - x) · fY (z - x) = ∫ y, logDeriv fY y · fY y = 0`.
    have htr := MeasureTheory.integral_sub_right_eq_self
        (fun y => logDeriv fY y * fY y) (μ := volume) x
    rw [htr, integral_logDeriv_density_eq_zero hregY, mul_zero]
  simp only [hinner, integral_zero]

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
`p_Z`, and the three product-measure `Integrable (uncurry …)` Tonelli
preconditions); none bundles the inequality core.

Assembly (all genuine, no `sorry`):
* atom A `fisherInfoOfDensity_toReal_eq_integral` rewrites all three Fisher
  informations to Bochner integrals;
* S4 `score_sq_le_weighted_integral` (`@audit:ok`, Jensen on a `withDensity`
  probability measure) gives `(logDeriv p_Z z)² ≤ ∫ x, W_λ²·p_{X|Z}` pointwise,
  integrated against `p_Z ≥ 0` via `integral_mono_ae`;
* `condDensityX·p_Z = fX(x)·fY(z-x)` cancellation;
* the 3-term Tonelli evaluation `convex_fisher_term1/2/cross` (`integral_integral_swap`
  + translation invariance `integral_sub_right_eq_self` + normalization /
  `integral_logDeriv_density_eq_zero` for the cross term) yields
  `λ²·J_X + (1-λ)²·J_Y` (cross term `= 0`).

2026-05-30 Phase 3c-fin genuine closure (0 sorry, `sorryAx`-free: `#print axioms` =
`[propext, Classical.choice, Quot.sound]`).

@audit:ok — independent honesty audit (2026-05-30): core-reconstruction test PASS.
The newly-added `hint_prod1/2/3 : Integrable (uncurry fun z x => <concrete expanded
term>) (volume.prod volume)` assert only product-measure integrability of the three
fully-spelled-out expanded integrands — they carry the integrand verbatim but assert
integrability, NOT the integral's value; granting all 3 does not hand over `J_sum ≤
λ²J_X + (1-λ)²J_Y` (consumed only as Tonelli `integral_integral_swap` /
`integral_integral` preconditions + helper-lemma args). Likewise `hint_inner`,
per-z `hint_X/Y`, `hcond_int`, `hint_W/Wsq`, `hint_fisherX/Y/Z` are Integrable
side-conditions; `hregX/hregY` (IsRegularDensityV2), `hX_bdd`/…, `hnormX/Y`, `hpZ`
(0 < p_Z), `0 ≤ lam ≤ 1` are regularity preconditions. None bundles the inequality
core. The bound is genuinely assembled from atom A (`@audit:ok`) + S4
`score_sq_le_weighted_integral` (`@audit:ok`, Jensen pointwise) + `integral_mono_ae`
+ condDensityX·p_Z cancellation + the 3 Tonelli helpers (each `@audit:ok` above).
sorryAx-free verified transiently (`#print axioms` = `[propext, Classical.choice,
Quot.sound]`, no transitive sorry). -/
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
          volume)
    -- Product-measure integrability of the 3 expanded terms (Tonelli preconditions,
    -- Gaussian-satisfied regularity; none bundles the inequality core).
    (hint_prod1 :
        Integrable
          (Function.uncurry fun z x => (logDeriv fX x) ^ 2 * fX x * fY (z - x))
          (volume.prod volume))
    (hint_prod2 :
        Integrable
          (Function.uncurry fun z x => (logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x))
          (volume.prod volume))
    (hint_prod3 :
        Integrable
          (Function.uncurry fun z x =>
            logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x)))
          (volume.prod volume)) :
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
  -- (c)-(d) Expand `W²·fX(x)·fY(z-x)` into 3 terms, split the double integral, evaluate
  -- each term with the Tonelli helpers `convex_fisher_term1/2/cross`.
  -- Abbreviations for the three (uncurried) term integrands.
  set T1 : ℝ → ℝ → ℝ := fun z x => (logDeriv fX x) ^ 2 * fX x * fY (z - x) with hT1_def
  set T2 : ℝ → ℝ → ℝ := fun z x => (logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x) with hT2_def
  set T3 : ℝ → ℝ → ℝ :=
    fun z x => logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x)) with hT3_def
  -- Pointwise expansion `W²·(fX·fY(z-x)) = λ²·T1 + (1-λ)²·T2 + 2λ(1-λ)·T3`.
  have hexpand : ∀ z x,
      (scoreWeight fX fY lam z x) ^ 2 * (fX x * fY (z - x))
        = lam ^ 2 * T1 z x + (1 - lam) ^ 2 * T2 z x + 2 * lam * (1 - lam) * T3 z x := by
    intro z x
    simp only [scoreWeight, hT1_def, hT2_def, hT3_def]
    ring
  -- Rewrite the inner integrand pointwise (no integrability needed for the rewrite).
  have hstep1 :
      (∫ z, ∫ x, (scoreWeight fX fY lam z x) ^ 2 * (fX x * fY (z - x)) ∂volume ∂volume)
        = ∫ z, ∫ x,
            (lam ^ 2 * T1 z x + (1 - lam) ^ 2 * T2 z x + 2 * lam * (1 - lam) * T3 z x)
            ∂volume ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => hexpand z x))
  rw [hstep1]
  -- Convert the nested double integrals to product-measure integrals.
  rw [integral_integral
        (f := fun z x =>
          lam ^ 2 * T1 z x + (1 - lam) ^ 2 * T2 z x + 2 * lam * (1 - lam) * T3 z x)
        (by
          -- prod-integrability of the sum from the 3 scaled prod hyps.
          have h1 := (hint_prod1.const_mul (lam ^ 2))
          have h2 := (hint_prod2.const_mul ((1 - lam) ^ 2))
          have h3 := (hint_prod3.const_mul (2 * lam * (1 - lam)))
          simpa only [Function.uncurry, hT1_def, hT2_def, hT3_def] using
            (h1.add h2).add h3)]
  -- Split the product integral into the 3 scaled pieces.
  have hi1 : Integrable (fun p : ℝ × ℝ => lam ^ 2 * T1 p.1 p.2) (volume.prod volume) :=
    hint_prod1.const_mul (lam ^ 2)
  have hi2 : Integrable (fun p : ℝ × ℝ => (1 - lam) ^ 2 * T2 p.1 p.2) (volume.prod volume) :=
    hint_prod2.const_mul ((1 - lam) ^ 2)
  have hi3 : Integrable (fun p : ℝ × ℝ => 2 * lam * (1 - lam) * T3 p.1 p.2) (volume.prod volume) :=
    hint_prod3.const_mul (2 * lam * (1 - lam))
  have hsplit :
      (∫ p : ℝ × ℝ, (lam ^ 2 * T1 p.1 p.2 + (1 - lam) ^ 2 * T2 p.1 p.2
            + 2 * lam * (1 - lam) * T3 p.1 p.2) ∂volume.prod volume)
        = (lam ^ 2 * ∫ p : ℝ × ℝ, T1 p.1 p.2 ∂volume.prod volume)
            + (1 - lam) ^ 2 * (∫ p : ℝ × ℝ, T2 p.1 p.2 ∂volume.prod volume)
            + 2 * lam * (1 - lam) * ∫ p : ℝ × ℝ, T3 p.1 p.2 ∂volume.prod volume := by
    have h12 :
        (∫ p : ℝ × ℝ, (lam ^ 2 * T1 p.1 p.2 + (1 - lam) ^ 2 * T2 p.1 p.2)
            + 2 * lam * (1 - lam) * T3 p.1 p.2 ∂volume.prod volume)
          = (∫ p : ℝ × ℝ, lam ^ 2 * T1 p.1 p.2 + (1 - lam) ^ 2 * T2 p.1 p.2 ∂volume.prod volume)
              + ∫ p : ℝ × ℝ, 2 * lam * (1 - lam) * T3 p.1 p.2 ∂volume.prod volume :=
      integral_add (hi1.add hi2) hi3
    rw [h12, integral_add hi1 hi2,
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hsplit]
  -- Convert each product integral back to nested and apply the helper lemmas.
  rw [← integral_integral (f := T1) hint_prod1, ← integral_integral (f := T2) hint_prod2,
    ← integral_integral (f := T3) hint_prod3]
  rw [hT1_def, hT2_def, hT3_def]
  rw [convex_fisher_term1 fX fY hnormY hint_prod1,
    convex_fisher_term2 fX fY hnormX hint_prod2,
    convex_fisher_cross fX fY hregY hint_prod3]
  ring

/-! ## Phase 3d bundle — `IsBlachmanConvReady` regularity precondition bundle

`convex_fisher_bound` requires, beyond `IsRegularDensityV2 fX/fY` + `∫=1`, a set of
**regularity preconditions** that `IsRegularDensityV2` does *not* imply: boundedness
of `f` and `deriv f`, several integrability side-conditions, positivity of the
convolution density `p_Z`, and the three product-measure (Tonelli) integrabilities.
These are needed for the convolution-Fisher analysis but are **not** derivable from
"regular density" alone (e.g. `Differentiable` does not bound `deriv f`).

We bundle them into a single structure `IsBlachmanConvReady fX fY` so the Stam
predicates (`IsStamCondExpCSHyp` / `IsStamCauchySchwarz` / `IsStamCauchySchwarzOptimal`)
can carry exactly **one** extra hypothesis rather than 14. Every field is a
regularity / integrability / boundedness / positivity precondition — **none** bundles
the convex Fisher inequality core (which lives genuinely inside `convex_fisher_bound`'s
body). The `lam`-dependent integrabilities (`int_W`, `int_Wsq`, `int_inner`) are
quantified over `lam ∈ [0,1]` because the consuming predicates conclude an `∀ lam`
bound. -/
/-- Regularity precondition bundle for the convolution-Fisher analysis.

@audit:ok — independent honesty audit (2026-05-31): all 19 fields are pure
regularity / integrability / boundedness / positivity preconditions; the bundle is
field-for-field the SAME hypotheses `convex_fisher_bound` (`@audit:ok`) already takes
individually (1:1 mapping verified — see `convex_fisher_bound_of_ready`). The
`logDeriv (convDensityAdd fX fY)`-containing fields (`int_fisherZ` / `int_prod1/2/3`)
assert only **`Integrable (…)`** of the verbatim integrands, NOT the value of any
integral nor any inequality — identical honesty state to `convex_fisher_bound`'s
already-`@audit:ok` argument group. No `:True` slot, no circular field, no
inequality/equality core bundled. NON-VACUOUSNESS: a proven Gaussian inhabitant
`isBlachmanConvReady_gaussianPDFReal` (`EPIBlachmanGaussianWitness.lean`) is now wired
in-tree with all 19 fields genuine (0 sorry, `#print axioms` → sorryAx-free), so the
predicates carrying this bundle have a machine-confirmed proven inhabitant. (Witness
`isBlachmanConvReady_gaussianPDFReal` independent honesty audit COMPLETE 2026-05-31,
commit `6e65535`, `@audit:ok` confirmed — sorryAx-free machine-verified. Scope note:
this confirms non-vacuousness of `IsBlachmanConvReady` itself; a Gaussian inhabitant
lemma for the upstream `IsStamCauchySchwarz*` predicates is the remaining
`epi-wall-reattack-plan` wiring step.) -/
structure IsBlachmanConvReady (fX fY : ℝ → ℝ) : Prop where
  /-- `fX` is Lebesgue-integrable. -/
  int_fX : Integrable fX volume
  /-- `fY` is Lebesgue-integrable. -/
  int_fY : Integrable fY volume
  /-- `fX` is bounded. -/
  bdd_fX : ∃ M : ℝ, ∀ w, |fX w| ≤ M
  /-- `deriv fX` is bounded (NOT implied by `IsRegularDensityV2`). -/
  bdd_fX' : ∃ M : ℝ, ∀ w, |deriv fX w| ≤ M
  /-- `fY` is bounded. -/
  bdd_fY : ∃ M : ℝ, ∀ w, |fY w| ≤ M
  /-- `deriv fY` is bounded (NOT implied by `IsRegularDensityV2`). -/
  bdd_fY' : ∃ M : ℝ, ∀ w, |deriv fY w| ≤ M
  /-- The convolution density `p_Z = convDensityAdd fX fY` is strictly positive. -/
  pos_pZ : ∀ z, 0 < convDensityAdd fX fY z
  /-- Per-`z` integrability of `deriv fX · fY(z - ·)`. -/
  int_X : ∀ z, Integrable (fun x => deriv fX x * fY (z - x)) volume
  /-- Per-`z` integrability of `fX · deriv fY(z - ·)`. -/
  int_Y : ∀ z, Integrable (fun x => fX x * deriv fY (z - x)) volume
  /-- Per-`z` integrability of the conditional density. -/
  cond_int : ∀ z, Integrable (condDensityX fX fY z) volume
  /-- Per-`(lam, z)` integrability of `scoreWeight · condDensityX`. -/
  int_W : ∀ lam, 0 ≤ lam → lam ≤ 1 → ∀ z,
      Integrable (fun x => scoreWeight fX fY lam z x * condDensityX fX fY z x) volume
  /-- Per-`(lam, z)` integrability of `scoreWeight² · condDensityX`. -/
  int_Wsq : ∀ lam, 0 ≤ lam → lam ≤ 1 → ∀ z,
      Integrable (fun x => (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x) volume
  /-- Per-`lam` integrability of the inner-weighted convolution density. -/
  int_inner : ∀ lam, 0 ≤ lam → lam ≤ 1 →
      Integrable (fun z =>
        (∫ x, (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x ∂volume)
          * convDensityAdd fX fY z) volume
  /-- Integrability of the `fX`-Fisher integrand. -/
  int_fisherX : Integrable (fun x => (logDeriv fX x) ^ 2 * fX x) volume
  /-- Integrability of the `fY`-Fisher integrand. -/
  int_fisherY : Integrable (fun x => (logDeriv fY x) ^ 2 * fY x) volume
  /-- Integrability of the `p_Z`-Fisher integrand. -/
  int_fisherZ : Integrable
      (fun z => (logDeriv (convDensityAdd fX fY) z) ^ 2 * convDensityAdd fX fY z) volume
  /-- Product-measure integrability of the first expanded Tonelli term. -/
  int_prod1 : Integrable
      (Function.uncurry fun z x => (logDeriv fX x) ^ 2 * fX x * fY (z - x)) (volume.prod volume)
  /-- Product-measure integrability of the second expanded Tonelli term. -/
  int_prod2 : Integrable
      (Function.uncurry fun z x => (logDeriv fY (z - x)) ^ 2 * fX x * fY (z - x))
      (volume.prod volume)
  /-- Product-measure integrability of the cross Tonelli term. -/
  int_prod3 : Integrable
      (Function.uncurry fun z x =>
        logDeriv fX x * fX x * (logDeriv fY (z - x) * fY (z - x))) (volume.prod volume)

/-- **Symmetry of the regularity bundle** under `X ↔ Y` swap.

`IsBlachmanConvReady` is genuinely symmetric: `convDensityAdd` is commutative
(`convDensityAdd_comm`) and each integrability / boundedness field transports across
the reflection substitution `x ↦ z - x` (volume-preserving) together with the marginal
swap on the product-measure fields. The full field-by-field transport is a ~50-line
reflection-invariance exercise orthogonal to the Phase 3d analytic core; it is deferred
as a regularity-bundle lemma. Consumed only by the (unused) API-completeness lemmas
`isStamCauchySchwarz_symm` / `isStamCondExpCSHyp_symm`.

@residual(plan:epi-wall-reattack-plan) -/
theorem isBlachmanConvReady_symm {fX fY : ℝ → ℝ}
    (h : IsBlachmanConvReady fX fY) : IsBlachmanConvReady fY fX := by
  sorry

/-- **Convex Fisher bound from the regularity bundle**. Applies `convex_fisher_bound`
by projecting all 14+ integrability / boundedness / positivity preconditions out of
the `IsBlachmanConvReady` bundle. Pure plumbing — no analytic content beyond
`convex_fisher_bound`.

@audit:ok — independent honesty audit (2026-05-31): 0-sorry projection wrapper; body
forwards the 20 `IsBlachmanConvReady` fields (+ `hreg`/`hnorm` regularity) into the
`@audit:ok` core `convex_fisher_bound` at the consumer-chosen `lam`. No hypothesis
carries the inequality core; conclusion ≠ any hypothesis type. -/
theorem convex_fisher_bound_of_ready (fX fY : ℝ → ℝ) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hregX : IsRegularDensityV2 fX) (hregY : IsRegularDensityV2 fY)
    (hnormX : ∫ x, fX x ∂volume = 1) (hnormY : ∫ x, fY x ∂volume = 1)
    (hready : IsBlachmanConvReady fX fY) :
    (fisherInfoOfDensity (convDensityAdd fX fY)).toReal
      ≤ lam ^ 2 * (fisherInfoOfDensity fX).toReal
          + (1 - lam) ^ 2 * (fisherInfoOfDensity fY).toReal :=
  convex_fisher_bound fX fY lam hlam0 hlam1 hregX hregY
    hready.int_fX hready.int_fY hready.bdd_fX hready.bdd_fX' hready.bdd_fY hready.bdd_fY'
    hnormX hnormY hready.pos_pZ hready.int_X hready.int_Y hready.cond_int
    (hready.int_W lam hlam0 hlam1) (hready.int_Wsq lam hlam0 hlam1)
    (hready.int_inner lam hlam0 hlam1)
    hready.int_fisherX hready.int_fisherY hready.int_fisherZ
    hready.int_prod1 hready.int_prod2 hready.int_prod3

end InformationTheory.Shannon.EPIBlachmanDensity
