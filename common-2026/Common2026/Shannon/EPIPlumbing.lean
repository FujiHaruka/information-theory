import Common2026.Meta.EntryPoint
import Common2026.Shannon.EntropyPowerInequality
import Common2026.Shannon.DifferentialEntropy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# T2-D-P: Entropy Power Inequality — Plumbing補題群 (partial publish)

`Common2026/Shannon/EntropyPowerInequality.lean` (T2-D, 347 行) で publish 済の
`entropyPower μ := Real.exp (2 · h(μ))` 周りの **plumbing 補題群** を本 file で
独立 publish する。Stam inequality / de Bruijn integration 本体 (L-EPI1 / L-EPI2
discharge) は **scope-out** — 本 file は

* `entropyPower` の基本性質 (positivity / non-zero / log-form / 2πe-normalized form)
* `differentialEntropy` の Phase B (translation / scaling / affine) を `entropyPower`
  に持ち上げた変形系
* `entropy_power_inequality` を 2πe-normalized form (Cover-Thomas Ch.17 流儀の
  `N(μ) := (2πe)⁻¹ · entropyPower μ` 形) に reshape したもの
* L-EPI3 hypothesis pass-through に乗る 4-arg chain

を扱う。撤退ラインは積極的に許容 (~200-400 行で 0 sorry 着地)。

## 主シグネチャ

* `entropyPower_pos_iff` / `entropyPower_ne_zero` — Tier 0 positivity 系
* `entropyPower_eq_of_differentialEntropy_eq` / `entropyPower_le_of_differentialEntropy_le`
   / `entropyPower_lt_of_differentialEntropy_lt` — 単調性
* `log_entropyPower` — log-form unfold
* `gaussianEntropyPowerConst` / `entropyPower_div_two_pi_e_gaussianReal` —
   Cover-Thomas `(2πe)⁻¹` normalization
* `entropyPower_map_add_const_eq_self` / `entropyPower_map_mul_const`
   / `entropyPower_map_affine` — Phase B-1/B-2/B-3 lift
* `entropy_power_inequality_normalized` — `N(X+Y) ≥ N(X) + N(Y)` form
* `entropy_power_inequality_four_arg` — 4-arg chain

## Mathlib-shape-driven

`entropyPower μ := Real.exp (2 · h(μ))` は `Real.exp_pos` / `Real.exp_log` /
`Real.log_exp` / `Real.exp_le_exp` の結論形に直結 (T2-D 本文 design)。

## 撤退ライン

Stam inequality + de Bruijn integration discharge は本 file scope 外。
`entropy_power_inequality_normalized` 等は既存 `entropy_power_inequality` を
hypothesis pass-through 形で reshape したものに留まる。
-/

namespace InformationTheory.Shannon.EntropyPowerInequality

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Topology

/-! ## §1 — Positivity / non-zero / log-form 系 -/


/-- `entropyPower μ ≠ 0` (corollary of strict positivity). -/
@[entry_point]
theorem entropyPower_ne_zero (μ : Measure ℝ) : entropyPower μ ≠ 0 :=
  (entropyPower_pos μ).ne'

/-- `Real.log (entropyPower μ) = 2 · h(μ)`. -/
@[entry_point]
theorem log_entropyPower (μ : Measure ℝ) :
    Real.log (entropyPower μ) = 2 * Common2026.Shannon.differentialEntropy μ := by
  unfold entropyPower
  exact Real.log_exp _

/-! ## §2 — Monotonicity in `differentialEntropy` -/

/-- If two measures share the same differential entropy, their entropy powers
coincide. -/
@[entry_point]
theorem entropyPower_eq_of_differentialEntropy_eq {μ ν : Measure ℝ}
    (h : Common2026.Shannon.differentialEntropy μ
          = Common2026.Shannon.differentialEntropy ν) :
    entropyPower μ = entropyPower ν := by
  unfold entropyPower
  rw [h]

/-- Monotonicity (≤): `h(μ) ≤ h(ν) ⟹ entropyPower μ ≤ entropyPower ν`. -/
@[entry_point]
theorem entropyPower_le_of_differentialEntropy_le {μ ν : Measure ℝ}
    (h : Common2026.Shannon.differentialEntropy μ
          ≤ Common2026.Shannon.differentialEntropy ν) :
    entropyPower μ ≤ entropyPower ν := by
  unfold entropyPower
  refine Real.exp_le_exp.mpr ?_
  linarith

/-- Strict monotonicity (<): `h(μ) < h(ν) ⟹ entropyPower μ < entropyPower ν`. -/
@[entry_point]
theorem entropyPower_lt_of_differentialEntropy_lt {μ ν : Measure ℝ}
    (h : Common2026.Shannon.differentialEntropy μ
          < Common2026.Shannon.differentialEntropy ν) :
    entropyPower μ < entropyPower ν := by
  unfold entropyPower
  refine Real.exp_lt_exp.mpr ?_
  linarith

/-! ## §3 — Cover-Thomas `(2πe)⁻¹` normalized form -/

/-- The Cover-Thomas normalization constant `2πe`. -/
noncomputable def gaussianEntropyPowerConst : ℝ := 2 * Real.pi * Real.exp 1

/-- `gaussianEntropyPowerConst > 0`. -/
@[entry_point]
theorem gaussianEntropyPowerConst_pos : 0 < gaussianEntropyPowerConst := by
  unfold gaussianEntropyPowerConst; positivity

/-- **`(2πe)⁻¹`-normalized form for Gaussian**: under the Cover-Thomas
`N(μ) := (2πe)⁻¹ · entropyPower μ` normalization, the Gaussian saturating
case takes the closed form `N(gaussianReal m v) = v`. -/
@[entry_point]
theorem entropyPower_div_two_pi_e_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    entropyPower (gaussianReal m v) / gaussianEntropyPowerConst = (v : ℝ) := by
  rw [entropyPower_gaussianReal m hv]
  unfold gaussianEntropyPowerConst
  field_simp

/-! ## §4 — Phase B (translation / scaling / affine) lift to `entropyPower` -/

/-- Phase B-1 lift: `entropyPower (μ.map (· + a)) = entropyPower μ`. This is the
`entropyPower` companion to `Common2026.Shannon.differentialEntropy_map_add_const`. -/
@[entry_point]
theorem entropyPower_map_add_const_eq_self
    {μ : Measure ℝ} (hμ : μ ≪ volume) [SigmaFinite μ] (a : ℝ) :
    entropyPower (μ.map (· + a)) = entropyPower μ :=
  entropyPower_map_add_const hμ a

/-- Phase B-2 lift: `entropyPower (μ.map (· * c)) = |c|² · entropyPower μ`. -/
@[entry_point]
theorem entropyPower_map_mul_const
    {μ : Measure ℝ} (hμ : μ ≪ volume) [IsProbabilityMeasure μ] {c : ℝ} (hc : c ≠ 0)
    (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    entropyPower (μ.map (· * c)) = c^2 * entropyPower μ := by
  unfold entropyPower
  rw [Common2026.Shannon.differentialEntropy_map_mul_const hμ hc h_ent_int]
  -- exp(2 (h(μ) + log|c|)) = exp(2 h(μ)) * exp(2 log|c|) = exp(2 h(μ)) * |c|^2 = c² * exp(2 h(μ))
  rw [show (2 : ℝ) * (Common2026.Shannon.differentialEntropy μ + Real.log |c|)
        = 2 * Common2026.Shannon.differentialEntropy μ + 2 * Real.log |c| from by ring]
  rw [Real.exp_add]
  have h_abs_pos : (0 : ℝ) < |c| := abs_pos.mpr hc
  have h_log : Real.exp (2 * Real.log |c|) = c^2 := by
    rw [show (2 : ℝ) * Real.log |c| = Real.log (|c| ^ 2) from by
      rw [Real.log_pow]; ring]
    rw [Real.exp_log (by positivity : (0 : ℝ) < |c|^2)]
    rw [sq_abs]
  rw [h_log]
  ring

/-- Phase B-3 lift: `entropyPower (μ.map (fun x => a * x + b)) = a² · entropyPower μ`.

The translation term `+ b` is absorbed (entropy power is translation-invariant),
leaving only the scaling factor `a²`. -/
@[entry_point]
theorem entropyPower_map_affine
    {μ : Measure ℝ} (hμ : μ ≪ volume) [IsProbabilityMeasure μ] {a : ℝ} (ha : a ≠ 0) (b : ℝ)
    (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    entropyPower (μ.map (fun x => a * x + b)) = a^2 * entropyPower μ := by
  unfold entropyPower
  rw [Common2026.Shannon.differentialEntropy_map_affine hμ ha b h_ent_int]
  rw [show (2 : ℝ) * (Common2026.Shannon.differentialEntropy μ + Real.log |a|)
        = 2 * Common2026.Shannon.differentialEntropy μ + 2 * Real.log |a| from by ring]
  rw [Real.exp_add]
  have h_log : Real.exp (2 * Real.log |a|) = a^2 := by
    rw [show (2 : ℝ) * Real.log |a| = Real.log (|a| ^ 2) from by
      rw [Real.log_pow]; ring]
    rw [Real.exp_log (by positivity : (0 : ℝ) < |a|^2)]
    rw [sq_abs]
  rw [h_log]
  ring

/-! ## §5 — `(2πe)⁻¹`-normalized EPI form (Cover-Thomas Ch.17 流儀) -/

/-- **EPI in `(2πe)⁻¹`-normalized form** (Cover-Thomas Theorem 17.7.3 alt signature).

Defining `N(μ) := entropyPower μ / (2πe)`, the EPI

    `N(X + Y) ≥ N(X) + N(Y)`

is equivalent to the un-normalized form. L-EPI3 hypothesis pass-through. -/
@[entry_point]
theorem entropy_power_inequality_normalized
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityResidual X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω)) / gaussianEntropyPowerConst
      ≥ entropyPower (P.map X) / gaussianEntropyPowerConst
        + entropyPower (P.map Y) / gaussianEntropyPowerConst := by
  have h := entropy_power_inequality P X Y hX hY hXY h_stam
  -- Divide both sides by the positive constant `2πe`.
  have hc_pos : 0 < gaussianEntropyPowerConst := gaussianEntropyPowerConst_pos
  have h_sum_div :
      entropyPower (P.map X) / gaussianEntropyPowerConst
        + entropyPower (P.map Y) / gaussianEntropyPowerConst
      = (entropyPower (P.map X) + entropyPower (P.map Y))
          / gaussianEntropyPowerConst := by
    field_simp
  rw [ge_iff_le, h_sum_div]
  exact div_le_div_of_nonneg_right h hc_pos.le

/-! ## §6 — 4-arg EPI chain (L-EPI3 pass-through を 3 回適用) -/

/-- **4-arg EPI pass-through**: for independent `X, Y, Z, W` with the appropriate
L-EPI3 hypotheses, `entropyPower (X+Y+Z+W) ≥ Σ entropyPower (·)`.

Chains three applications of L-EPI3 (the 2-arg `IsEntropyPowerInequalityHypothesis`
predicate): once on `((X+Y)+Z) vs W`, once on `(X+Y) vs Z`, once on `X vs Y`.

`@audit:staged(epi-stam-to-conclusion-plan)` -/
theorem entropy_power_inequality_four_arg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Z W : Ω → ℝ)
    (h_xyz_w_epi :
      IsEntropyPowerInequalityHypothesis (fun ω => X ω + Y ω + Z ω) W P)
    (h_xy_z_epi : IsEntropyPowerInequalityHypothesis (fun ω => X ω + Y ω) Z P)
    (h_x_y_epi : IsEntropyPowerInequalityHypothesis X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω + Z ω + W ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) + entropyPower (P.map Z)
          + entropyPower (P.map W) := by
  -- Step 1: from `h_xyz_w_epi`:
  -- entropyPower ((X+Y+Z) + W) ≥ entropyPower (X+Y+Z) + entropyPower W
  have h1 : entropyPower (P.map (fun ω => X ω + Y ω + Z ω + W ω))
      ≥ entropyPower (P.map (fun ω => X ω + Y ω + Z ω)) + entropyPower (P.map W) := by
    have h_assoc : (fun ω : Ω => (X ω + Y ω + Z ω) + W ω)
        = (fun ω : Ω => X ω + Y ω + Z ω + W ω) := by
      funext ω; ring
    have h := h_xyz_w_epi
    unfold IsEntropyPowerInequalityHypothesis at h
    rw [h_assoc] at h
    exact h
  -- Step 2: from `entropy_power_inequality_three_arg`:
  -- entropyPower (X+Y+Z) ≥ entropyPower X + entropyPower Y + entropyPower Z
  have h2 : entropyPower (P.map (fun ω => X ω + Y ω + Z ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) + entropyPower (P.map Z) :=
    entropy_power_inequality_three_arg P X Y Z h_xy_z_epi h_x_y_epi
  -- Combine via transitivity.
  linarith

/-! ## §7 — Misc. corollaries -/

/-- Log-form of EPI: `2 h(X+Y) ≥ log (entropyPower X + entropyPower Y)`.

Derived from `entropy_power_inequality` by applying `Real.log` (the inequality
direction is preserved since `Real.log` is monotone on `(0, ∞)`). -/
@[entry_point]
theorem two_differentialEntropy_ge_log_sum
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityResidual X Y P) :
    2 * Common2026.Shannon.differentialEntropy (P.map (fun ω => X ω + Y ω))
      ≥ Real.log (entropyPower (P.map X) + entropyPower (P.map Y)) := by
  have h_epi' : entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) :=
    entropy_power_inequality P X Y hX hY hXY h_stam
  have h_rhs_pos : 0 < entropyPower (P.map X) + entropyPower (P.map Y) :=
    add_pos (entropyPower_pos _) (entropyPower_pos _)
  have h_log : Real.log (entropyPower (P.map (fun ω => X ω + Y ω)))
      ≥ Real.log (entropyPower (P.map X) + entropyPower (P.map Y)) :=
    Real.log_le_log h_rhs_pos h_epi'
  rw [log_entropyPower] at h_log
  exact h_log

/-- L-EPI3 hypothesis is symmetric in `X` and `Y` (when the sum is reordered). -/
theorem isEntropyPowerInequalityHypothesis_symm
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X Y : Ω → ℝ}
    (h : IsEntropyPowerInequalityHypothesis X Y P) :
    IsEntropyPowerInequalityHypothesis Y X P := by
  unfold IsEntropyPowerInequalityHypothesis at *
  have h_comm : (fun ω => Y ω + X ω) = fun ω => X ω + Y ω := by
    funext ω; ring
  rw [h_comm, add_comm (entropyPower (P.map Y))]
  exact h

end InformationTheory.Shannon.EntropyPowerInequality
