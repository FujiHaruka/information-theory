import Common2026.Shannon.EPIConvDensity
import Common2026.Shannon.FisherInfoV2
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities

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

Genuine (0 sorry): pure lintegral↔Bochner bridge, no Blachman content. Pending
independent honesty audit (then `@audit:ok`). -/
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
The inequality core (conditional CS on the explicit probability weight) is the
Blachman/Stam analytic content.

@residual(wall:stam-blachman) -/
theorem score_sq_le_weighted_integral (fX fY : ℝ → ℝ) (lam z : ℝ)
    (hregX : IsRegularDensityV2 fX) (hregY : IsRegularDensityV2 fY)
    (hX_int : Integrable fX volume) (hY_int : Integrable fY volume)
    (hX_bdd : ∃ M : ℝ, ∀ w, |fX w| ≤ M) (hX'_bdd : ∃ M : ℝ, ∀ w, |deriv fX w| ≤ M)
    (hY_bdd : ∃ M : ℝ, ∀ w, |fY w| ≤ M) (hY'_bdd : ∃ M : ℝ, ∀ w, |deriv fY w| ≤ M)
    (hpZ : 0 < convDensityAdd fX fY z)
    (hint_X : Integrable (fun x => deriv fX x * fY (z - x)) volume)
    (hint_Y : Integrable (fun x => fX x * deriv fY (z - x)) volume)
    (hint_Wsq :
        Integrable (fun x => (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x) volume) :
    (logDeriv (convDensityAdd fX fY) z) ^ 2
      ≤ ∫ x, (scoreWeight fX fY lam z x) ^ 2 * condDensityX fX fY z x ∂volume := by
  sorry

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
the S4 lemma. The score-of-convolution Cauchy-Schwarz + Tonelli evaluation is the
Blachman/Stam analytic wall.

@residual(wall:stam-blachman) -/
theorem convex_fisher_bound (fX fY : ℝ → ℝ) (lam : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hregX : IsRegularDensityV2 fX) (hregY : IsRegularDensityV2 fY)
    (hX_int : Integrable fX volume) (hY_int : Integrable fY volume)
    (hX_bdd : ∃ M : ℝ, ∀ w, |fX w| ≤ M) (hX'_bdd : ∃ M : ℝ, ∀ w, |deriv fX w| ≤ M)
    (hY_bdd : ∃ M : ℝ, ∀ w, |fY w| ≤ M) (hY'_bdd : ∃ M : ℝ, ∀ w, |deriv fY w| ≤ M)
    (hnormX : ∫ x, fX x ∂volume = 1) (hnormY : ∫ x, fY x ∂volume = 1)
    (hpZ : ∀ z, 0 < convDensityAdd fX fY z)
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
  -- Remaining content = score-of-convolution Cauchy-Schwarz (S4) integrated against `p_Z`
  -- + Tonelli order-swap + 3-term evaluation (cross term = 0). This is the Blachman/Stam
  -- analytic wall; the S4 pointwise bound is `score_sq_le_weighted_integral`.
  -- @residual(wall:stam-blachman)
  sorry

end InformationTheory.Shannon.EPIBlachmanDensity
