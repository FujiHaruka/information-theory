import Common2026.Meta.EntryPoint
import Common2026.Shannon.EntropyPowerInequality
import Common2026.Shannon.EPIPlumbing
import Common2026.Shannon.EPIStamDischarge
import Common2026.Shannon.EPIL3Integration
import Common2026.Shannon.FisherInfoV2
import Common2026.Shannon.FisherInfoV2DeBruijn
import Common2026.Shannon.FisherInfoGaussian
import Common2026.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# T2-D-B: Stam inequality body discharge (Cauchy-Schwarz / convolution-score path)

`Common2026/Shannon/EPIStamDischarge.lean` (Wave 5, 755 行) で Stam inequality
`1 / J(X+Y) ≥ 1 / J(X) + 1 / J(Y)` を `IsStamInequalityHyp` 真 signature で
publish 済。本 file (Wave 6 T2-D-B) はその **body discharge** を Cauchy-Schwarz
+ convolution-score 経路で組み上げる。

## Approach

Cover-Thomas Lemma 17.7.2 の標準的な 1 次元 Stam inequality 証明は次の path:

1. **Score representation of convolution** (Lemma 17.7.1 / Blachman 1965): for
   independent `X, Y` with densities, the score of `Z := X + Y` satisfies
   `s_Z(z) = E[s_X(X) | X + Y = z] = E[s_Y(Y) | X + Y = z]`.
2. **Cauchy-Schwarz** on `E[s_X(X) | X + Y = z]` and any linear combination
   `λ s_X(X) + (1 - λ) s_Y(Y)`:
       `s_Z(z)² ≤ E[(λ s_X(X) + (1 - λ) s_Y(Y))² | X + Y = z]`.
3. **Take total expectation**: `J(Z) ≤ λ² J(X) + (1 - λ)² J(Y)`.
4. **Optimize over λ**: with `λ = J(Y) / (J(X) + J(Y))`,
       `J(Z) ≤ J(X) J(Y) / (J(X) + J(Y)) ⇔ 1/J(Z) ≥ 1/J(X) + 1/J(Y)`.

Mathlib に
* `condExp`-based score conditional expectation manipulation,
* Stam inequality / Blachman score-conv identity,
* Cauchy-Schwarz on conditional expectations

の三つともは標準形では存在しない (`rg "Stam|Blachman|score_conv" → 0 hit`).
本 file は本体の **body** を Cauchy-Schwarz predicate 形に分解し、各 step を
predicate pass-through で publish した上で、**predicate chain で Stam 真
signature `IsStamInequalityHyp` を導出する** wrapper を提供する。

### 撤退ライン (本 file で発動)

* **L-Stam-CS** (本 file core): `IsStamCauchySchwarz X Y P` predicate 形で Step 2-3
  (Cauchy-Schwarz + total expectation) を pass-through。
* **L-Stam-Conv** (本 file core): `IsStamScoreConvolution X Y P` で Step 1
  (convolution score representation) を pass-through。
* **L-Stam-Opt** (本 file core): `IsStamLambdaOptimal X Y P` で Step 4 (λ 最適化)
  を pass-through。実体は `1 / a + 1 / b ≤ (a + b) / (a * b)` 形の純算術なので、
  **predicate-free** で direct discharge する補題も併設。

### 主シグネチャ

* `IsStamScoreConvolution X Y P` (§1) — Step 1 predicate
* `IsStamCauchySchwarz X Y P` (§2) — Step 2-3 predicate
* `IsStamLambdaOptimal` (§3) — Step 4 純算術 closed form
* `stam_inequality_via_predicate` (§4) — chain combinator (deliverable)
* `isStamInequalityHyp_via_body` (§4) — `IsStamInequalityHyp` への bridge
* `isStamCauchySchwarz_of_gaussian` (§5) — Gaussian discharge
* `isStamScoreConvolution_of_gaussian` (§5) — Gaussian discharge
* `stam_inequality_gaussian_body` (§5) — Gaussian full discharge corollary
* `epi_via_stam_body_gaussian` (§6) — pipeline integration with §5
-/

namespace InformationTheory.Shannon.EPIStamInequalityBody

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPIStamDischarge

/-! ## §1 — Convolution score representation predicate (Step 1) -/

/-- **Convolution score representation hypothesis** (Blachman 1965 / Cover-Thomas
Lemma 17.7.1 body form).

For independent `X, Y` with smooth densities `p_X, p_Y` (so that the score
`s_X := (log p_X)' = p_X' / p_X` is well-defined), the score of the sum
`Z := X + Y` admits the conditional expectation representation

    `s_Z(z) = E[s_X(X) | X + Y = z] = E[s_Y(Y) | X + Y = z]`.

In particular, for any `λ ∈ [0, 1]`,

    `s_Z(z) = E[λ · s_X(X) + (1 - λ) · s_Y(Y) | X + Y = z]`.

This identity (Blachman's score-of-convolution lemma) is the foundation of the
1-dimensional Stam inequality proof. Mathlib has neither the score function
abstraction tied to `pdf` nor `condExp` integration over the sum-level
σ-algebra. We reify here the **optimal λ-witness** that the score-convolution
identity *produces* (the value `λ* = J_Y / (J_X + J_Y)` is the one that
minimizes the Cauchy-Schwarz upper bound in Step 4). This honest typed form
replaces the Wave 7 `:= True` placeholder.

The genuine `condExp`-of-score derivation (the Blachman identity producing this
λ-witness from a `lconvolution` density argument) is the irreducible
measure-theoretic core — a Mathlib wall (b) (`rg "Blachman|score_conv" → 0 hit`,
no `lconvolution` differentiability API). We reify its *output* (the existence
of the λ-witness in `[0, 1]`) rather than its derivation; the witness is
unconditionally constructible by `isStamScoreConvolution_intro` below, so this
predicate is *honestly discharged* (Tier 1) — it is **not load-bearing** for the
λ-optimization downstream (Step 4 only consumes the λ-witness, which always
exists as a real number in `[0,1]` for positive Fisher infos).

`@audit:ok` -/
def IsStamScoreConvolution {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y : ℝ) (fX fY : ℝ → ℝ), 0 < J_X → 0 < J_Y →
    J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧ lam = J_Y / (J_X + J_Y)

/-- **Unconditional discharge of the score-convolution typed predicate**.

The optimal λ-witness `λ* = J_Y / (J_X + J_Y)` always lies in `[0, 1]` for
positive Fisher infos — this is pure arithmetic (`positivity` + `div_le_one`).
This replaces the Wave 7 `trivial` discharge of the `Prop := True` placeholder
with a real construction; the witness it produces is exactly the one the
λ-optimization (Step 4 `stam_lambda_min`) consumes.

`@audit:ok` -/
@[entry_point]
theorem isStamScoreConvolution_intro {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : IsStamScoreConvolution X Y P := by
  intro J_X J_Y fX fY hJX hJY _hJX_def _hJY_def
  refine ⟨J_Y / (J_X + J_Y), ?_, ?_, rfl⟩
  · positivity
  · have hsum : 0 < J_X + J_Y := by linarith
    rw [div_le_one hsum]; linarith


/-! ## §2 — Cauchy-Schwarz + total expectation predicate (Step 2-3) -/

/-- **Cauchy-Schwarz + total expectation hypothesis** (Stam body).

The genuine Stam-proof body step: given the score-convolution identity, apply
Cauchy-Schwarz pointwise to `s_Z(z)² = E[λ s_X + (1 - λ) s_Y | sum = z]²`,
then take total expectation against `p_Z` to obtain

    `J(Z) ≤ λ² J(X) + (1 - λ)² J(Y)`.

Phrased here as: there exists `λ ∈ [0, 1]` with the inequality between
real-valued Fisher info projections. The predicate enforces only the
**existence of the bounding λ-witness**; the optimum is selected separately in
§3. -/
def IsStamCauchySchwarz {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Y ω)) fXY).toReal →
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 ∧
      J_sum ≤ lam ^ 2 * J_X + (1 - lam) ^ 2 * J_Y

/-- The Cauchy-Schwarz predicate is symmetric in `X, Y` (swap `λ ↦ 1 - λ`). -/
theorem isStamCauchySchwarz_symm {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamCauchySchwarz X Y P) :
    IsStamCauchySchwarz Y X P := by
  intro J_Y J_X J_sum fY fX fXY hJY hJX hJsum hJY_def hJX_def hJsum_def
  have h_comm : (fun ω => Y ω + X ω) = fun ω => X ω + Y ω := by
    funext ω; ring
  rw [h_comm] at hJsum_def
  obtain ⟨lam, hlam_lo, hlam_hi, hbd⟩ :=
    h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  refine ⟨1 - lam, by linarith, by linarith, ?_⟩
  -- `J_sum ≤ lam² J_X + (1 - lam)² J_Y = (1 - (1 - lam))² J_X + (1 - lam)² J_Y`.
  have : (1 - (1 - lam)) ^ 2 = lam ^ 2 := by ring
  linarith [this]

/-! ## §3 — λ-optimization closed form (Step 4): pure arithmetic, no predicate -/

/-- **λ-optimization closed form** (Stam Step 4).

For positive `a, b > 0`, the function `λ ↦ λ² a + (1 - λ)² b` is minimized at
`λ* = b / (a + b)` with minimum value `a b / (a + b)`. Combined with Step 3,
this gives `J(Z) ≤ J(X) J(Y) / (J(X) + J(Y))`, equivalently
`1 / J(Z) ≥ 1 / J(X) + 1 / J(Y)`. -/
@[entry_point]
theorem stam_lambda_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let lam := b / (a + b)
    lam ^ 2 * a + (1 - lam) ^ 2 * b = a * b / (a + b) := by
  have hab : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := hab.ne'
  show (b / (a + b)) ^ 2 * a + (1 - b / (a + b)) ^ 2 * b = a * b / (a + b)
  field_simp
  ring

/-- **λ optimum upper bound**: for any `λ ∈ ℝ`, `λ² a + (1-λ)² b ≥ ab / (a+b)`.
Cauchy-Schwarz / AM-GM direct consequence. -/
@[entry_point]
theorem stam_lambda_lower_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (lam : ℝ) :
    a * b / (a + b) ≤ lam ^ 2 * a + (1 - lam) ^ 2 * b := by
  have hab : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := hab.ne'
  -- The minimum value `ab/(a+b)` is achieved at `λ = b/(a+b)`. The deviation
  -- `(λ - b/(a+b))² · (a+b)` measures the slack. We show
  -- `λ² a + (1 - λ)² b - ab/(a+b) = (λ - b/(a+b))² · (a+b) ≥ 0`.
  have h_expand : lam ^ 2 * a + (1 - lam) ^ 2 * b - a * b / (a + b)
      = (lam - b / (a + b)) ^ 2 * (a + b) := by
    field_simp
    ring
  have h_sq_nn : 0 ≤ (lam - b / (a + b)) ^ 2 := sq_nonneg _
  have h_prod_nn : 0 ≤ (lam - b / (a + b)) ^ 2 * (a + b) :=
    mul_nonneg h_sq_nn hab.le
  linarith [h_expand, h_prod_nn]

/-- **Inverse-form Stam algebraic identity**: for `a, b, c > 0` with
`c ≤ ab/(a+b)`, the inverse relation `1/c ≥ 1/a + 1/b` holds. -/
@[entry_point]
theorem stam_inverse_form_of_harmonic_mean
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_le : c ≤ a * b / (a + b)) :
    1 / c ≥ 1 / a + 1 / b := by
  have hab : 0 < a + b := by linarith
  have h_target_pos : 0 < a * b / (a + b) := by positivity
  -- `c ≤ ab/(a+b) → 1/c ≥ (a+b)/(ab) = 1/a + 1/b`.
  have h_inv_le : 1 / (a * b / (a + b)) ≤ 1 / c :=
    one_div_le_one_div_of_le hc h_le
  have h_rhs : 1 / (a * b / (a + b)) = 1 / a + 1 / b := by
    have hab_ne : a + b ≠ 0 := hab.ne'
    have ha_ne : a ≠ 0 := ha.ne'
    have hb_ne : b ≠ 0 := hb.ne'
    field_simp
    ring
  rw [h_rhs] at h_inv_le
  exact h_inv_le

/-! ## §4 — Predicate chain combinator (the deliverable) -/

/-- **Optimal Cauchy-Schwarz predicate** (the actually pipeline-usable form).

Strengthens `IsStamCauchySchwarz` to require the witness `λ = J_Y / (J_X + J_Y)`,
which is the optimal λ minimizing `λ² J_X + (1-λ)² J_Y`.

⚠ **DEFECT — universally FALSE predicate** (independent honesty audit 2026-05-30).
The body universally quantifies over **arbitrary unconstrained** `fX fY fXY : ℝ→ℝ`
with NO constraint tying `fXY` to the convolution of `fX, fY`, and
`fisherInfoOfMeasureV2 _μ f = fisherInfoOfDensity f` **ignores its measure
argument** (`fisherInfoOfMeasureV2_def`, `:86`, `rfl`), so the densities are also
untied to `P.map X / P.map Y / P.map (X+Y)`. Refuting instance (all hypotheses
genuinely satisfiable, NON-vacuous): `fX = fY = gaussianPDFReal 0 1`
⇒ `J_X = J_Y = (fisherInfoOfDensity (gaussianPDFReal 0 1)).toReal = (ofReal (1/1)).toReal = 1`
(`fisherInfoOfDensity_gaussianPDFReal`, `FisherInfoV2.lean:273`), RHS `= 1/2`;
`fXY = gaussianPDFReal 0 (1/100)` ⇒ `J_sum = (ofReal (1/(1/100))).toReal = 100`
(positive finite, `0 < J_sum` holds); conclusion `100 ≤ 1/2` is FALSE. The genuine
Stam content `J(p_X ⋆ p_Y) ≤ λ²J(p_X)+(1-λ)²J(p_Y)` cannot be plugged in: the body
has no handle identifying `fXY` with `convDensityAdd fX fY`. This is NOT a Mathlib
wall — it is a signature pivot bug. **Owner-task** (out of scope for the
audit; flagged to orchestrator): add the convolution constraint (e.g.
`fXY =ᵐ[volume] EPIConvDensity.convDensityAdd fX fY` + density regularity tying
`fX, fY, fXY` to `pdf (P.map X/Y/(X+Y))`), rippling to
`entropy_power_inequality_via_body` / `stam_inequality_via_predicate_optimal` /
`stam_convex_fisher_bound_gaussian`. Note the sibling predicates
`IsStamCondExpCSHyp` (`EPIStamStep12Body.lean:200`) and `IsStamInequalityResidual`
(`EntropyPowerInequality.lean:190`) share the identical missing-convolution-constraint
defect (same refuting instance).
@audit:defect(false-statement) @audit:closed-by-successor(epi-wall-reattack-plan) -/
def IsStamCauchySchwarzOptimal {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
    J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
    J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
    J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
              (P.map (fun ω => X ω + Y ω)) fXY).toReal →
    J_sum ≤ J_X * J_Y / (J_X + J_Y)

/-- **Stam Step 2 density wall — shared sorry 補題**.

The genuine analytic core of the Stam inequality's Step 2-3 (Cover-Thomas Lemma
17.7.2 / Blachman 1965): for independent `X, Y` with smooth densities, the
conditional Cauchy-Schwarz `s_Z(z)² ≤ E[(λ s_X + (1-λ) s_Y)² | X+Y=z]` integrated
against `p_Z` gives the convex Fisher bound `J(Z) ≤ λ² J(X) + (1-λ)² J(Y)`,
whose λ-optimum is the **optimal Cauchy-Schwarz** form
`J(Z) ≤ J(X) J(Y) / (J(X) + J(Y))`.

This is the genuine measure-theoretic wall: Mathlib has **neither** the
score-of-convolution conditional-expectation representation (`condExp` of
`logDeriv` of a convolution density) **nor** Fisher-information convolution
lemmas (`rg "Stam|Blachman|score_conv" → 0 hit`). Building the apparatus
(joint law on `ℝ × ℝ` + sum-level sub-σ-algebra + Fubini + heat-kernel score
identity) is a multi-file ~300-line effort, scoped out as a single shared wall.

Before this lemma, the genuine Step 2 core was carried as a **load-bearing
hypothesis** `(h_cs_opt : IsStamCauchySchwarzOptimal X Y P)` on the public
end-to-end theorem `entropy_power_inequality_via_body` (a tier-5 honesty
defect: Step 2 was *assumed*, not proved). This lemma localizes that core to a
single honest `sorry`, so downstream wrappers consume it as a normal lemma call
and carry no load-bearing Step-2 hypothesis. The Gaussian special case is
genuinely discharged separately
(`Common2026.Shannon.FisherInfoV2.stam_convex_fisher_bound_gaussian`).

Regularity preconditions (measurability, independence, probability measure) are
kept as honest arguments; the irreducible analytic content is the `sorry`.

## ⚠ Structural blocker discovered 2026-05-30 (epi-wall-reattack Phase 3, NO-GO)

Phase 3 attempted to discharge this `sorry` via the genuine Blachman route
(gateway `convDensity_add_differentiable` → conditional score `s_Z = E[s_X | X+Y=z]`
→ `ConvexOn.map_condExp_le` → `integral_condExp` + cross-term → λ-optimization).
The attempt is **NO-GO for a deeper reason than the anticipated L-EPIW-3-α
(Blachman disintegration self-build)**: the *target predicate*
`IsStamCauchySchwarzOptimal X Y P` is **not provable at its current signature**,
independent of any Blachman apparatus.

`IsStamCauchySchwarzOptimal` (`:245`) universally quantifies over **arbitrary,
unconstrained** densities `fX fY fXY : ℝ → ℝ`, with the only hypotheses being the
three Fisher-info `.toReal` definitions and positivity, and concludes
`J_sum ≤ J_X * J_Y / (J_X + J_Y)`. Crucially, **there is no constraint linking
`fXY` to the convolution of `fX, fY`** (and `fisherInfoOfMeasureV2 _μ f`
**ignores its measure argument** — it is `fisherInfoOfDensity f`, so the
densities are also not tied to `P.map X / P.map Y / P.map (X+Y)`). The statement
is therefore mathematically **false**: take `fX = fY = gaussianPDFReal 0 1`
(`J_X = J_Y = 1`, RHS `= 1/2`) and `fXY = gaussianPDFReal 0 (1/100)`
(`J_sum = 100`, a finite positive Fisher info via the closed form `1/v`); then
`100 ≤ 1/2` fails. The genuine Stam content `J(p_X ⋆ p_Y) ≤ λ²J(p_X)+(1-λ)²J(p_Y)`
cannot be plugged in because the body has **no handle** identifying `fXY` with
`convDensityAdd fX fY`.

Honest verdict: the wall here is **not** (only) the Blachman score-of-convolution
self-build. The predicate signature itself strips the convolution relationship
that makes Stam true, so no Mathlib-complete Blachman apparatus discharges it.
The correct next step is an **owner-level signature pivot** of
`IsStamCauchySchwarzOptimal` to add the convolution constraint (e.g.
`fXY =ᵐ[volume] EPIConvDensity.convDensityAdd fX fY` + density regularity tying
`fX, fY, fXY` to `pdf (P.map X/Y/(X+Y))`) — a multi-declaration change rippling to
`entropy_power_inequality_via_body` and the Gaussian discharge
`stam_convex_fisher_bound_gaussian`. That pivot is out of scope for filling this
`sorry` and is flagged to the orchestrator rather than built upon. Until then the
honest residual stays here.

## ⚠ Audit verdict 2026-05-30 — `wall:stam-step2-density` is a DEFECT, not a wall

Independent honesty audit confirmed (counterexample re-derived from verbatim
closed forms) that the target predicate `IsStamCauchySchwarzOptimal X Y P` is
**universally FALSE at its current signature** (see the def docstring at `:245`).
This `sorry` therefore does **not** mark a genuine "Mathlib-absent wall" closeable
by Blachman apparatus — it proves a FALSE statement, so **no** honest discharge
exists at this signature. The prior `@residual(wall:stam-step2-density)` was a
**misclassification** (a defect masquerading as a Mathlib wall). Reclassified to
`@audit:defect(false-statement)`. The genuine next step is the **owner-level
signature pivot** of `IsStamCauchySchwarzOptimal` (add the convolution constraint;
ripple to `entropy_power_inequality_via_body` / `stam_inequality_via_predicate_optimal`
/ `stam_convex_fisher_bound_gaussian`); the `sorry` body becomes honestly
dischargeable only after that pivot. Out of scope for the audit — flagged to
orchestrator as an owner task under `epi-wall-reattack-plan`.

@audit:defect(false-statement) @audit:closed-by-successor(epi-wall-reattack-plan) -/
theorem stam_step2_density_wall
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) :
    IsStamCauchySchwarzOptimal X Y P := by
  sorry

/-- **Stam inequality via predicate chain (optimal form)** — actual deliverable.

Given the optimal Cauchy-Schwarz predicate, chain through Step 4 closed form to
obtain the inverse-form Stam inequality. (The former cosmetic
`IsStamScoreConvolution` slot was dropped in the wall-consolidation pass: its
body never used it — it is unconditionally constructible by
`isStamScoreConvolution_intro` and carried no information.)

Audit note (2026-05-30): this is a genuine **implication** wrapper — body is the
algebraic reshaping `J_sum ≤ J_X·J_Y/(J_X+J_Y) ⊢ 1/J_sum ≥ 1/J_X+1/J_Y` (conclusion
type ≠ hypothesis type), `sorryAx`-free (`#print axioms` → `[propext, Classical.choice,
Quot.sound]`), so `@audit:ok` for the implication is correct. **Caveat**: the
antecedent `IsStamCauchySchwarzOptimal X Y P` is a universally-FALSE predicate at its
current signature (`:245` audit), satisfiable only via the false-statement `sorry`
wall `stam_step2_density_wall` (`@audit:defect(false-statement)`). This wrapper does
NOT launder that defect into genuine completeness — it asserts only the implication,
not the antecedent. After the owner-level signature pivot of `IsStamCauchySchwarzOptimal`
(`epi-wall-reattack-plan`) the wrapper stays valid (the algebra is signature-agnostic).

`@audit:ok` -/
@[entry_point]
theorem stam_inequality_via_predicate_optimal
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_cs_opt : IsStamCauchySchwarzOptimal X Y P) :
    ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
      J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
      J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
      J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
                (P.map (fun ω => X ω + Y ω)) fXY).toReal →
      1 / J_sum ≥ 1 / J_X + 1 / J_Y := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  have h_le := h_cs_opt J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  exact stam_inverse_form_of_harmonic_mean hJX hJY hJsum h_le

/-- **`IsStamInequalityHyp` from body predicate**. The genuine Stam-inequality
predicate (Cover-Thomas Lemma 17.7.2 真 signature) follows from the optimal-CS
predicate alone. This is the **bridge from body to plumbing**. (The former
cosmetic `IsStamScoreConvolution` argument was dropped in the wall-consolidation
pass — it was unused, unconditionally constructible by
`isStamScoreConvolution_intro`.)

`@audit:ok` -/
@[entry_point]
theorem isStamInequalityHyp_via_body
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_cs_opt : IsStamCauchySchwarzOptimal X Y P) :
    IsStamInequalityHyp X Y P := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  exact stam_inequality_via_predicate_optimal h_cs_opt
    J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def

/-! ## §5 — Gaussian saturation discharge -/


/- **RESOLVED (2026-05-20):** the former `isStamCauchySchwarzOptimal_of_gaussian_fisherInfo_zero`
and its chain lemmas `isStamInequalityHyp_of_gaussian_via_body` /
`isStamInequalityHyp_of_gaussian_via_body_Y` discharged the optimal-CS predicate
vacuously by `exfalso`-ing the `0 < J_X` (resp. `0 < J_Y`) precondition against
the buggy V1 `fisherInfo = 0` artefact for Gaussians. They asserted nothing about
Stam actually holding and were removed. The genuine Gaussian EPI runs via
`entropyPower_gaussian_additivity` (see `epi_via_stam_body_gaussian`
in §6 below). -/

/-! ## §6 — EPI pipeline integration with body discharge -/

/-- **Stam-to-EPI bridge via body discharge** (Gaussian case): combine
the body-derived Stam inequality with the Stam-to-EPI bridge from
`EPIStamDischarge.isStamToEPIBridgeHyp_of_gaussian`. -/
theorem isStamToEPIBridgeHyp_via_body_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    IsStamToEPIBridgeHyp X Y P :=
  isStamToEPIBridgeHyp_of_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY

/-- **EPI via Stam body discharge (Gaussian case)**: full deliverable end-to-end.
For Gaussian `X, Y` with non-zero variance, EPI follows through the body
discharge + Gaussian saturation bridge — no upstream hypothesis required. -/
@[entry_point]
theorem epi_via_stam_body_gaussian
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
  epi_via_stam_gaussian P X Y hX hY hXY m₁ m₂ v₁ v₂ hv₁ hv₂ hLawX hLawY

/-! ## §7 — Predicate manipulation lemmas -/

/-- The optimal CS predicate is *strictly stronger* than the existential CS
predicate `IsStamCauchySchwarz`. -/
theorem isStamCauchySchwarz_of_optimal
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : IsStamCauchySchwarzOptimal X Y P) :
    IsStamCauchySchwarz X Y P := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  -- Optimal λ = J_Y / (J_X + J_Y) gives the inequality
  -- `J_sum ≤ λ² J_X + (1-λ)² J_Y = J_X J_Y / (J_X + J_Y)`.
  refine ⟨J_Y / (J_X + J_Y), ?_, ?_, ?_⟩
  · positivity
  · have hsum : 0 < J_X + J_Y := by linarith
    rw [div_le_one hsum]
    linarith
  · have h_le := h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    have h_min := stam_lambda_min hJX hJY
    -- `lam² J_X + (1-lam)² J_Y = J_X J_Y / (J_X + J_Y)` at `lam = J_Y/(J_X+J_Y)`.
    show J_sum ≤ (J_Y / (J_X + J_Y)) ^ 2 * J_X
                  + (1 - J_Y / (J_X + J_Y)) ^ 2 * J_Y
    linarith [h_min]

/-- The score-convolution predicate is symmetric in `X, Y` — *unconditionally*
provable since the W9 typed body is a pure existence Prop on the optimal λ
witness (which is constructed from `J_X, J_Y` only, no asymmetry in the
predicate body). Provided primarily to absorb `IsStamScoreConvolution Y X P`
slots in upstream pipelines that swap `(X, Y)` order. -/
theorem isStamScoreConvolution_symm
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (_h : IsStamScoreConvolution X Y P) :
    IsStamScoreConvolution Y X P :=
  isStamScoreConvolution_intro Y X P

/-! ## §8 — λ-optimization: independent algebraic corollaries -/

/-! ## §9 — Direct optimal-CS construction from λ-witness -/

/-- **Optimal CS from a λ-witness at the optimum**: given a Cauchy-Schwarz
witness with `λ = J_Y / (J_X + J_Y)`, the optimal-form predicate is recovered.

`@audit:ok` -/
theorem isStamCauchySchwarzOptimal_of_lambda_optimal
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h : ∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum →
      J_X = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map X) fX).toReal →
      J_Y = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2 (P.map Y) fY).toReal →
      J_sum = (Common2026.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
                (P.map (fun ω => X ω + Y ω)) fXY).toReal →
      J_sum ≤ (J_Y / (J_X + J_Y)) ^ 2 * J_X
              + (1 - J_Y / (J_X + J_Y)) ^ 2 * J_Y) :
    IsStamCauchySchwarzOptimal X Y P := by
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  have h_bd := h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
  have h_min := stam_lambda_min hJX hJY
  linarith [h_min]

/-! ## §10 — Stam inequality body discharge pipeline integration -/

/-- **Body-discharged Stam inequality via Integrated Pipeline**: composes the
body discharge predicates with the Wave 6 `EPIL3Integration` integrated
pipeline.

The former `h_bridge : IsStamToEPIBridgeHyp` argument was removed in the Cluster C
Tier-2 migration (`epi-stam-cluster-c-sorry-migration-plan`, route L-EPISC-3-α):
`IsEPIL3IntegratedPipeline` no longer carries a load-bearing `bridge` field, so
the pipeline is built from the genuine Stam residual alone (the Stam→EPI bridge is
discharged internally by consumers via `stamToEPIBridge_holds`).

`@audit:ok` -/
theorem isStamInequalityHyp_via_body_to_pipeline
    {Ω : Type*} [MeasurableSpace Ω]
    {X Y : Ω → ℝ} {P : Measure Ω}
    (h_cs_opt : IsStamCauchySchwarzOptimal X Y P) :
    InformationTheory.Shannon.EPIL3Integration.IsEPIL3IntegratedPipeline X Y P :=
  { stam := isStamInequalityHyp_via_body h_cs_opt }

/-- **End-to-end EPI via body discharge** (composes §4 + §6 + EPIL3 pipeline).

The former load-bearing Step-2 hypothesis `(h_cs_opt : IsStamCauchySchwarzOptimal
X Y P)` (a tier-5 honesty defect — Step 2 was *assumed*) has been removed: the
optimal Cauchy-Schwarz / convex Fisher bound is now supplied internally by the
shared sorry lemma `stam_step2_density_wall`.
The Step-1 score-convolution predicate is constructed unconditionally via
`isStamScoreConvolution_intro` (cosmetic slot). The public signature therefore
carries **no** load-bearing Step-2 analytic hypothesis — only regularity
(measurability / independence / probability measure) — with the Step-2 obligation
localized to the shared sorry lemma `stam_step2_density_wall`.

⚠ Audit 2026-05-30: `stam_step2_density_wall` is NOT a genuine Mathlib wall — its
target predicate `IsStamCauchySchwarzOptimal` is universally FALSE at its current
signature (reclassified to `@audit:defect(false-statement)`; see `:245` / `:359`).
This wrapper therefore consumes a false-statement `sorry` (and a second wall
`stamToEPIBridge_holds`), so it is NOT proof-done. Honest closure requires the
owner-level signature pivot under `epi-wall-reattack-plan`, not a Blachman discharge.

The remaining `h_bridge : IsStamToEPIBridgeHyp` argument is **not** load-bearing
at this wrapper: `epi_via_stam_main` ignores it (`_h_bridge`), discharging the
Stam→EPI bridge internally via the separate shared sorry lemma
`stamToEPIBridge_holds`. It is retained only as a cosmetic interface slot.

Independent honesty audit (2026-05-30, commit `f3affec`): the signature is now
honest — the former load-bearing `h_cs_opt : IsStamCauchySchwarzOptimal` (tier-5
defect: Step 2 *assumed*) is genuinely removed and `h_bridge` is verified unused
(`epi_via_stam_main` binds it as `_h_bridge`). However this wrapper is **not**
proof done: it consumes two shared sorry walls (`stam_step2_density_wall` in this
file, `EntropyPowerInequality.stamToEPIBridge_holds`) and so depends transitively
on `sorryAx` (verified via `#print axioms` →
`[propext, sorryAx, Classical.choice, Quot.sound]`). The prior `@audit:ok`
(tier 1) was therefore incorrect for the post-rewrite state and has been removed;
the genuine residual lives in the two walls, each carrying its own `@residual`. -/
@[entry_point]
theorem entropy_power_inequality_via_body
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (h_bridge : IsStamToEPIBridgeHyp X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  have h_cs_opt := stam_step2_density_wall P X Y hX hY hXY
  have h_stam := isStamInequalityHyp_via_body h_cs_opt
  exact epi_via_stam_main P X Y X hX hY hXY h_stam h_bridge

/-! ## §11 — Sanity check / regression theorems -/

/-- **Sanity check**: `stam_inverse_form_of_harmonic_mean` recovers the standard
form `1/c ≥ 1/a + 1/b` when `c = ab/(a+b)` exactly. -/
theorem stam_inverse_form_at_equality {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 / (a * b / (a + b)) = 1 / a + 1 / b := by
  have hab : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := hab.ne'
  have ha_ne : a ≠ 0 := ha.ne'
  have hb_ne : b ≠ 0 := hb.ne'
  field_simp
  ring

/-- **Sanity check**: at `λ = 0`, the upper bound is `J_Y`. -/
theorem stam_lambda_at_zero (a b : ℝ) :
    (0 : ℝ) ^ 2 * a + (1 - 0) ^ 2 * b = b := by ring

/-- **Sanity check**: at `λ = 1`, the upper bound is `J_X`. -/
theorem stam_lambda_at_one (a b : ℝ) :
    (1 : ℝ) ^ 2 * a + (1 - 1) ^ 2 * b = a := by ring

end InformationTheory.Shannon.EPIStamInequalityBody
