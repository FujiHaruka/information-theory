import Common2026.Shannon.RateDistortionConverseMonotone

/-!
# Rate-distortion convexity (E-4'' Phase A + B core)

[`docs/shannon/rate-distortion-convexity-plan.md`](../../../docs/shannon/rate-distortion-convexity-plan.md)
の Phase A + Phase B core 実装。Cover-Thomas 10.4 の **rate-distortion 関数の凸性**:

```
∀ D₁ D₂ : ℝ, ∀ λ ∈ [0, 1],
  R(λ D₁ + (1-λ) D₂) ≤ λ R(D₁) + (1-λ) R(D₂)
```

## 主補題

* `mixtureMeasure` — 2 つの結合分布の convex combination (measure-level)
* `mixtureMeasure_map_fst` / `mixtureMeasure_map_snd` — pushforward の線形性
* `mixtureMeasure_map_fst_eq` — 同じ X-marginal `P` をもつ 2 結合分布の混合は再び `P`
* `expectedDistortion_mixtureMeasure` — distortion 線形性
* `mixtureMeasure_feasible` — feasibility が convex combination で保存
* `rateDistortionFunction_convexOn` — **Phase B 主補題**

## 設計判断 (plan 判断ログ参照)

* **pmf 形 scope retreat**: `klDiv` の joint convexity が Mathlib 不在で
  ~500 行 gap。Phase B 主補題は **`klDiv` joint convexity を hypothesis**
  として取り回す subnormal 形で publish (specializations が各設定で discharge する
  pattern)。
* **iInf plumbing**: 任意 feasible `ν₁`, `ν₂` をとって convex combination を構成し、
  feasibility + 値 evaluation を経由して `iInf_le_of_le` で直接 press する。
* **Phase C (n-letter form)** は deferred。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## Phase A — Mixture measure 構成 + feasibility 保存 -/

/-- Convex combination of two joint measures on `α × β` with weight `λ ∈ [0, 1]`. -/
noncomputable def mixtureMeasure
    (lam : ℝ) (ν₁ ν₂ : Measure (α × β)) : Measure (α × β) :=
  ENNReal.ofReal lam • ν₁ + ENNReal.ofReal (1 - lam) • ν₂

/-- `Prod.fst` pushforward of a convex combination is the convex combination of pushforwards. -/
theorem mixtureMeasure_map_fst
    (lam : ℝ) (ν₁ ν₂ : Measure (α × β)) :
    (mixtureMeasure lam ν₁ ν₂).map Prod.fst
      = ENNReal.ofReal lam • ν₁.map Prod.fst
        + ENNReal.ofReal (1 - lam) • ν₂.map Prod.fst := by
  unfold mixtureMeasure
  rw [Measure.map_add _ _ measurable_fst,
      Measure.map_smul, Measure.map_smul]

/-- `Prod.snd` pushforward of a convex combination is the convex combination of pushforwards. -/
theorem mixtureMeasure_map_snd
    (lam : ℝ) (ν₁ ν₂ : Measure (α × β)) :
    (mixtureMeasure lam ν₁ ν₂).map Prod.snd
      = ENNReal.ofReal lam • ν₁.map Prod.snd
        + ENNReal.ofReal (1 - lam) • ν₂.map Prod.snd := by
  unfold mixtureMeasure
  rw [Measure.map_add _ _ measurable_snd,
      Measure.map_smul, Measure.map_smul]

/-- If two joint distributions share the same `Prod.fst` marginal `P`, then so does
their convex combination (with `λ ∈ [0, 1]`). -/
theorem mixtureMeasure_map_fst_eq
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (P : Measure α) (ν₁ ν₂ : Measure (α × β))
    (h₁ : ν₁.map Prod.fst = P) (h₂ : ν₂.map Prod.fst = P) :
    (mixtureMeasure lam ν₁ ν₂).map Prod.fst = P := by
  rw [mixtureMeasure_map_fst, h₁, h₂, ← add_smul,
      ← ENNReal.ofReal_add hlam₀ (by linarith)]
  have h_one : lam + (1 - lam) = 1 := by ring
  rw [h_one, ENNReal.ofReal_one, one_smul]

/-- Expected distortion is linear in the joint measure: distortion of the convex
combination equals the convex combination of distortions, provided distortion is
integrable under each joint. -/
theorem expectedDistortion_mixtureMeasure
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (d : α → β → ℝ) (ν₁ ν₂ : Measure (α × β))
    (h_int₁ : Integrable (fun p => d p.1 p.2) ν₁)
    (h_int₂ : Integrable (fun p => d p.1 p.2) ν₂) :
    expectedDistortion d (mixtureMeasure lam ν₁ ν₂)
      = lam * expectedDistortion d ν₁ + (1 - lam) * expectedDistortion d ν₂ := by
  unfold expectedDistortion mixtureMeasure
  have h_int₁' : Integrable (fun p : α × β => d p.1 p.2) (ENNReal.ofReal lam • ν₁) :=
    h_int₁.smul_measure ENNReal.ofReal_ne_top
  have h_int₂' : Integrable (fun p : α × β => d p.1 p.2) (ENNReal.ofReal (1 - lam) • ν₂) :=
    h_int₂.smul_measure ENNReal.ofReal_ne_top
  rw [integral_add_measure h_int₁' h_int₂',
      integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal hlam₀, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - lam)]
  simp [smul_eq_mul]

/-- Feasibility is preserved under convex combinations: if `ν₁` is feasible at `D₁`
and `ν₂` is feasible at `D₂`, then `mixtureMeasure λ ν₁ ν₂` is feasible at
`λ D₁ + (1-λ) D₂`. -/
theorem mixtureMeasure_feasible
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (P : Measure α) (d : α → β → ℝ)
    (ν₁ ν₂ : Measure (α × β))
    (h_marg₁ : ν₁.map Prod.fst = P) (h_marg₂ : ν₂.map Prod.fst = P)
    {D₁ D₂ : ℝ}
    (h_dist₁ : expectedDistortion d ν₁ ≤ D₁) (h_dist₂ : expectedDistortion d ν₂ ≤ D₂)
    (h_int₁ : Integrable (fun p => d p.1 p.2) ν₁)
    (h_int₂ : Integrable (fun p => d p.1 p.2) ν₂) :
    (mixtureMeasure lam ν₁ ν₂).map Prod.fst = P
    ∧ expectedDistortion d (mixtureMeasure lam ν₁ ν₂) ≤ lam * D₁ + (1 - lam) * D₂ := by
  refine ⟨mixtureMeasure_map_fst_eq hlam₀ hlam₁ P ν₁ ν₂ h_marg₁ h_marg₂, ?_⟩
  rw [expectedDistortion_mixtureMeasure hlam₀ hlam₁ d ν₁ ν₂ h_int₁ h_int₂]
  have h1lam : 0 ≤ 1 - lam := by linarith
  exact add_le_add (mul_le_mul_of_nonneg_left h_dist₁ hlam₀)
    (mul_le_mul_of_nonneg_left h_dist₂ h1lam)

/-! ## Phase B core — R(D) convexity 主補題

`klDiv` の joint convexity を直接示すのは Mathlib 不在の gap。
**`klDiv` joint convexity を hypothesis として取り回す subnormal 形** で publish。
Specializations (e.g. finite-alphabet pmf 形) は別ファイルで discharge する pattern。 -/

/-- **R(D) is convex** (joint-`klDiv`-convexity hypothesis form).

The rate-distortion function is convex in the distortion threshold provided the
joint mutual-information convexity inequality holds at the witness measures —
which is **Cover-Thomas 2.7.2** (joint convexity of relative entropy in
`(numerator, denominator)`) specialized to mutual information.

We package the convexity-of-`klDiv` step as an explicit hypothesis (`h_klDiv_conv`)
to keep this lemma standalone; specializations (e.g. finite-alphabet pmf form) can
discharge that hypothesis via log-sum inequality at the per-atom level. -/
theorem rateDistortionFunction_convexOn
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P]
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (D₁ D₂ : ℝ)
    (h_klDiv_conv :
      ∀ (ν₁ ν₂ : Measure (α × β)),
        ν₁.map Prod.fst = P → ν₂.map Prod.fst = P →
        Integrable (fun p => d p.1 p.2) ν₁ →
        Integrable (fun p => d p.1 p.2) ν₂ →
        expectedDistortion d ν₁ ≤ D₁ → expectedDistortion d ν₂ ≤ D₂ →
        klDiv (mixtureMeasure lam ν₁ ν₂)
            (((mixtureMeasure lam ν₁ ν₂).map Prod.fst).prod
              ((mixtureMeasure lam ν₁ ν₂).map Prod.snd))
          ≤ ENNReal.ofReal lam
              * klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd))
            + ENNReal.ofReal (1 - lam)
              * klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)))
    (h_int_witness :
      ∀ (ν : Measure (α × β)), ν.map Prod.fst = P →
        Integrable (fun p => d p.1 p.2) ν) :
    rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂)
      ≤ ENNReal.ofReal lam * rateDistortionFunction d P D₁
        + ENNReal.ofReal (1 - lam) * rateDistortionFunction d P D₂ := by
  -- ## Per-pair bound: for any feasible (ν₁, ν₂), R(λD₁+(1-λ)D₂) is bounded by
  -- the convex combination of joint klDiv at the witnesses.
  have h_per_pair : ∀ (ν₁ ν₂ : Measure (α × β)),
      ν₁.map Prod.fst = P → ν₂.map Prod.fst = P →
      expectedDistortion d ν₁ ≤ D₁ → expectedDistortion d ν₂ ≤ D₂ →
      rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂)
        ≤ ENNReal.ofReal lam * klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd))
          + ENNReal.ofReal (1 - lam)
            * klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)) := by
    intro ν₁ ν₂ h_marg₁ h_marg₂ h_dist₁ h_dist₂
    have h_int₁ : Integrable (fun p : α × β => d p.1 p.2) ν₁ := h_int_witness ν₁ h_marg₁
    have h_int₂ : Integrable (fun p : α × β => d p.1 p.2) ν₂ := h_int_witness ν₂ h_marg₂
    obtain ⟨h_mix_marg, h_mix_dist⟩ :=
      mixtureMeasure_feasible hlam₀ hlam₁ P d ν₁ ν₂ h_marg₁ h_marg₂
        h_dist₁ h_dist₂ h_int₁ h_int₂
    have h_feas :
        rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂)
          ≤ klDiv (mixtureMeasure lam ν₁ ν₂)
              (((mixtureMeasure lam ν₁ ν₂).map Prod.fst).prod
                ((mixtureMeasure lam ν₁ ν₂).map Prod.snd)) :=
      rateDistortionFunction_le_of_feasible d P (lam * D₁ + (1 - lam) * D₂)
        (mixtureMeasure lam ν₁ ν₂) h_mix_marg h_mix_dist
    exact le_trans h_feas
      (h_klDiv_conv ν₁ ν₂ h_marg₁ h_marg₂ h_int₁ h_int₂ h_dist₁ h_dist₂)
  -- ## RHS factorization: rewrite λ R(D₁) + (1-λ) R(D₂)
  -- as ⨅ ν₁ feas, ⨅ ν₂ feas, [λ klDiv ν₁ + (1-λ) klDiv ν₂] using mul_iInf + iInf_add + add_iInf.
  -- We handle boundary cases (lam = 0 or lam = 1) separately to avoid the mul_iInf side conditions.
  set a : ℝ≥0∞ := ENNReal.ofReal lam with ha_def
  set b : ℝ≥0∞ := ENNReal.ofReal (1 - lam) with hb_def
  have h1lam : 0 ≤ 1 - lam := by linarith
  -- Case split on lam = 0 / lam = 1 / 0 < lam < 1.
  by_cases hlam_eq0 : lam = 0
  · -- lam = 0: a = 0, b = 1, λD₁+(1-λ)D₂ = D₂.
    subst hlam_eq0
    have ha0 : a = 0 := by simp [ha_def]
    have hb1 : b = 1 := by simp [hb_def]
    have h_arg : (0 : ℝ) * D₁ + (1 - 0) * D₂ = D₂ := by ring
    rw [h_arg, ha0, hb1, zero_mul, zero_add, one_mul]
  by_cases hlam_eq1 : lam = 1
  · -- lam = 1: a = 1, b = 0, λD₁+(1-λ)D₂ = D₁.
    subst hlam_eq1
    have ha1 : a = 1 := by simp [ha_def]
    have hb0 : b = 0 := by simp [hb_def]
    have h_arg : (1 : ℝ) * D₁ + (1 - 1) * D₂ = D₁ := by ring
    rw [h_arg, ha1, hb0, zero_mul, add_zero, one_mul]
  -- Strict interior: 0 < lam < 1.
  have hlam_pos : 0 < lam := lt_of_le_of_ne hlam₀ (Ne.symm hlam_eq0)
  have hlam_lt1 : lam < 1 := lt_of_le_of_ne hlam₁ hlam_eq1
  have h1lam_pos : 0 < 1 - lam := by linarith
  have ha_pos : 0 < a := by simp [ha_def, ENNReal.ofReal_pos, hlam_pos]
  have hb_pos : 0 < b := by simp [hb_def, ENNReal.ofReal_pos, h1lam_pos]
  have ha_ne_zero : a ≠ 0 := ha_pos.ne'
  have hb_ne_zero : b ≠ 0 := hb_pos.ne'
  have ha_ne_top : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hb_ne_top : b ≠ ∞ := ENNReal.ofReal_ne_top
  -- Push a/b inside the nested iInfs for R(D₁) and R(D₂).
  -- R(D₁) = ⨅ ν₁, ⨅ (_ : marg), ⨅ (_ : dist), klDiv ν₁ ...
  -- a * R(D₁) = ⨅ ν₁, ⨅ (_ : marg), ⨅ (_ : dist), a * klDiv ν₁ ...
  have h_aR1 :
      a * rateDistortionFunction d P D₁
        = ⨅ (ν₁ : Measure (α × β)) (_ : ν₁.map Prod.fst = P)
            (_ : expectedDistortion d ν₁ ≤ D₁),
            a * klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd)) := by
    unfold rateDistortionFunction
    rw [ENNReal.mul_iInf_of_ne ha_ne_zero ha_ne_top]
    refine iInf_congr fun ν₁ => ?_
    rw [ENNReal.mul_iInf_of_ne ha_ne_zero ha_ne_top]
    refine iInf_congr fun _ => ?_
    rw [ENNReal.mul_iInf_of_ne ha_ne_zero ha_ne_top]
  have h_bR2 :
      b * rateDistortionFunction d P D₂
        = ⨅ (ν₂ : Measure (α × β)) (_ : ν₂.map Prod.fst = P)
            (_ : expectedDistortion d ν₂ ≤ D₂),
            b * klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)) := by
    unfold rateDistortionFunction
    rw [ENNReal.mul_iInf_of_ne hb_ne_zero hb_ne_top]
    refine iInf_congr fun ν₂ => ?_
    rw [ENNReal.mul_iInf_of_ne hb_ne_zero hb_ne_top]
    refine iInf_congr fun _ => ?_
    rw [ENNReal.mul_iInf_of_ne hb_ne_zero hb_ne_top]
  rw [h_aR1, h_bR2]
  -- Now use iInf_add then add_iInf to factor in the sum.
  -- (⨅ ν₁, f ν₁) + (⨅ ν₂, g ν₂) = ⨅ ν₁, [f ν₁ + ⨅ ν₂, g ν₂] = ⨅ ν₁, ⨅ ν₂, [f ν₁ + g ν₂]
  rw [ENNReal.iInf_add]
  refine le_iInf fun ν₁ => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun h_marg₁ => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun h_dist₁ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun ν₂ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun h_marg₂ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun h_dist₂ => ?_
  -- Goal: rateDistortionFunction d P (lam*D₁+(1-lam)*D₂) ≤ a * klDiv ν₁ ... + b * klDiv ν₂ ...
  exact h_per_pair ν₁ ν₂ h_marg₁ h_marg₂ h_dist₁ h_dist₂

end InformationTheory.Shannon
