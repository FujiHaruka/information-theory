import InformationTheory.Shannon.RateDistortion.ConverseMonotone
import InformationTheory.Meta.EntryPoint

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

* **`klDiv` joint convexity は DPI 経路で genuine に閉じた** (Cover-Thomas 2.7.2)。
  Mathlib 直接不在だが、selector-extension (`Bool × Ω`) + プロジェクト資産
  `klDiv_map_le` (一般 pushforward DPI) + 二点 selector の per-slice KL 加法性
  (`klDiv_add_of_mutuallySingular`、互いに特異な成分の rnDeriv 分解) で自作。
  3 層: `klDiv_joint_convex` (gateway) → `klDiv_mixture_le` → 主補題。
  旧 subnormal (joint convexity を hypothesis 化) 形は撤回済。
* **iInf plumbing**: 任意 feasible `ν₁`, `ν₂` をとって convex combination を構成し、
  feasibility + per-pair bound を経由して `ENNReal.mul_iInf_of_ne` / `iInf_add` /
  `add_iInf` で press する。境界 `lam = 0, 1` は別 branch。
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
@[entry_point]
theorem mixtureMeasure_map_fst
    (lam : ℝ) (ν₁ ν₂ : Measure (α × β)) :
    (mixtureMeasure lam ν₁ ν₂).map Prod.fst
      = ENNReal.ofReal lam • ν₁.map Prod.fst
        + ENNReal.ofReal (1 - lam) • ν₂.map Prod.fst := by
  unfold mixtureMeasure
  rw [Measure.map_add _ _ measurable_fst,
      Measure.map_smul, Measure.map_smul]

/-- `Prod.snd` pushforward of a convex combination is the convex combination of pushforwards. -/
@[entry_point]
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
@[entry_point]
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

`klDiv` の joint convexity (Cover-Thomas 2.7.2) は Mathlib 直接不在の gap だが、
プロジェクト資産 `klDiv_map_le` (一般 pushforward DPI) を核に DPI 経路で genuine に
閉じる。

3 層構造:
* 層1 (gateway) `klDiv_joint_convex` — RD 固有構造から切り離した純 joint convexity。
* 層2 `klDiv_mixture_le` — 層1 の RD 固有形への plumbing 適用。
* 層3 `rateDistortionFunction_convexOn` — 層2 の iInf press。 -/

/-! ### 層1 (gateway) — `klDiv` の純 joint convexity -/

/-- `klDiv` は `Prod.mk b`-埋め込みで不変: `klDiv ((dirac b).prod μ)((dirac b).prod σ) = klDiv μ σ`。
両 DPI (`klDiv_map_le` を `Prod.mk b` と `Prod.snd` の両方向で適用) で示す。
@audit:ok -/
private lemma klDiv_dirac_prod {Ω : Type*} [MeasurableSpace Ω]
    (b : Bool) (μ σ : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure σ] :
    klDiv ((Measure.dirac b).prod μ) ((Measure.dirac b).prod σ) = klDiv μ σ := by
  have hmk : Measurable (Prod.mk b : Ω → Bool × Ω) := measurable_prodMk_left
  rw [Measure.dirac_prod, Measure.dirac_prod]
  have _ : IsFiniteMeasure (μ.map (Prod.mk b)) := Measure.isFiniteMeasure_map μ _
  have _ : IsFiniteMeasure (σ.map (Prod.mk b)) := Measure.isFiniteMeasure_map σ _
  refine le_antisymm (klDiv_map_le hmk μ σ) ?_
  -- 逆向き: Prod.snd で射影して戻す
  have hsnd : Measurable (Prod.snd : Bool × Ω → Ω) := measurable_snd
  have h := klDiv_map_le hsnd (μ.map (Prod.mk b)) (σ.map (Prod.mk b))
  rwa [Measure.map_map hsnd hmk, Measure.map_map hsnd hmk,
    show (Prod.snd ∘ Prod.mk b) = (id : Ω → Ω) from rfl, Measure.map_id, Measure.map_id] at h

/-- 二つのスライス `(dirac true).prod μ` と `(dirac false).prod σ` は互いに特異。
@audit:ok -/
private lemma mutuallySingular_dirac_prod {Ω : Type*} [MeasurableSpace Ω]
    (μ σ : Measure Ω) [SFinite μ] [SFinite σ] :
    (Measure.dirac true).prod μ ⟂ₘ (Measure.dirac false).prod σ := by
  have hmkt : Measurable (Prod.mk true : Ω → Bool × Ω) := measurable_prodMk_left
  have hmkf : Measurable (Prod.mk false : Ω → Bool × Ω) := measurable_prodMk_left
  have hmeas : MeasurableSet ({p : Bool × Ω | p.1 = false}) :=
    measurable_fst (measurableSet_singleton false)
  refine ⟨{p : Bool × Ω | p.1 = false}, hmeas, ?_, ?_⟩
  · rw [Measure.dirac_prod, Measure.map_apply hmkt hmeas]
    convert measure_empty (μ := μ)
    ext ω; simp
  · rw [Measure.dirac_prod, Measure.map_apply hmkf hmeas.compl]
    convert measure_empty (μ := σ)
    ext ω; simp

/-- 互いに特異な成分の和に対する `klDiv` の加法性。
`A₁, B₁` と `A₂, B₂` がそれぞれ分離した台に乗っているとき (各 cross-特異)、
`klDiv (A₁+A₂)(B₁+B₂) = klDiv A₁ B₁ + klDiv A₂ B₂`。
3 つの特異性仮説 (`hB`/`hA₂B₁`/`hA₁B₂`) は全て rnDeriv 消失 (`rnDeriv_eq_zero_of_mutuallySingular`)
+ 加法分解 (`rnDeriv_add_right_of_mutuallySingular`) に genuine に消費される precondition で、
いずれかを落とすと加法性が偽になる (load-bearing core ではなく幾何的分離条件)。
@audit:ok -/
private lemma klDiv_add_of_mutuallySingular {Ω : Type*} [MeasurableSpace Ω]
    (A₁ A₂ B₁ B₂ : Measure Ω)
    [IsFiniteMeasure A₁] [IsFiniteMeasure A₂] [IsFiniteMeasure B₁] [IsFiniteMeasure B₂]
    (hB : B₁ ⟂ₘ B₂) (hA₂B₁ : A₂ ⟂ₘ B₁) (hA₁B₂ : A₁ ⟂ₘ B₂) :
    klDiv (A₁ + A₂) (B₁ + B₂) = klDiv A₁ B₁ + klDiv A₂ B₂ := by
  have hac_B₁ : B₁ ≪ B₁ + B₂ := Measure.AbsolutelyContinuous.rfl.add_right B₂
  have hac_B₂ : B₂ ≪ B₁ + B₂ := Measure.AbsolutelyContinuous.rfl.add_right' B₁
  -- 絶対連続性で場合分け
  by_cases hac₁ : A₁ ≪ B₁
  swap
  · -- A₁ ⋘̸ B₁ ⟹ 右辺 = ∞、左辺も ∞
    rw [klDiv_of_not_ac hac₁, top_add, klDiv_of_not_ac]
    intro hac
    exact hac₁ (Measure.absolutelyContinuous_of_add_of_mutuallySingular
      (Measure.AbsolutelyContinuous.add_left_iff.mp hac).1 hA₁B₂)
  by_cases hac₂ : A₂ ≪ B₂
  swap
  · rw [klDiv_of_not_ac hac₂, add_top, klDiv_of_not_ac]
    intro hac
    refine hac₂ (Measure.absolutelyContinuous_of_add_of_mutuallySingular
      (ν₁ := B₂) (ν₂ := B₁) ?_ hA₂B₁)
    rw [add_comm B₂ B₁]
    exact (Measure.AbsolutelyContinuous.add_left_iff.mp hac).2
  -- 主ケース: A₁ ≪ B₁ かつ A₂ ≪ B₂
  have hac : (A₁ + A₂) ≪ (B₁ + B₂) :=
    Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨hac₁.trans hac_B₁, hac₂.trans hac_B₂⟩
  rw [klDiv_eq_lintegral_klFun_of_ac hac₁, klDiv_eq_lintegral_klFun_of_ac hac₂,
    klDiv_eq_lintegral_klFun_of_ac hac, lintegral_add_measure]
  -- rnDeriv の和分解 (a.e.[B₁+B₂])
  have hsum : (A₁ + A₂).rnDeriv (B₁ + B₂)
      =ᵐ[B₁ + B₂] A₁.rnDeriv (B₁ + B₂) + A₂.rnDeriv (B₁ + B₂) :=
    Measure.rnDeriv_add A₁ A₂ (B₁ + B₂)
  congr 1
  · -- B₁ 上: (A₁+A₂).rnDeriv(B₁+B₂) =ᵐ[B₁] A₁.rnDeriv B₁
    refine lintegral_congr_ae ?_
    have hzero : A₂.rnDeriv (B₁ + B₂) =ᵐ[B₁] 0 :=
      Measure.rnDeriv_eq_zero_of_mutuallySingular hA₂B₁ hac_B₁
    have h2 : A₁.rnDeriv (B₁ + B₂) =ᵐ[B₁] A₁.rnDeriv B₁ :=
      Measure.rnDeriv_add_right_of_mutuallySingular hB
    filter_upwards [hac_B₁.ae_le hsum, hzero, h2] with x hx1 hx0 hx2
    rw [hx1, Pi.add_apply, hx0, Pi.zero_apply, add_zero, hx2]
  · -- B₂ 上: (A₁+A₂).rnDeriv(B₁+B₂) =ᵐ[B₂] A₂.rnDeriv B₂
    refine lintegral_congr_ae ?_
    have hzero : A₁.rnDeriv (B₁ + B₂) =ᵐ[B₂] 0 :=
      Measure.rnDeriv_eq_zero_of_mutuallySingular hA₁B₂ hac_B₂
    have h2 : A₂.rnDeriv (B₁ + B₂) =ᵐ[B₂] A₂.rnDeriv B₂ := by
      rw [add_comm B₁ B₂]
      exact Measure.rnDeriv_add_right_of_mutuallySingular hB.symm
    filter_upwards [hac_B₂.ae_le hsum, hzero, h2] with x hx1 hx0 hx2
    rw [hx1, Pi.add_apply, hx0, Pi.zero_apply, zero_add, hx2]

/-- 二点スライス上の `klDiv` 加法性 + 同一スカラー両側の引き出し:
互いに特異なスライスの和に対し klDiv は分配し、各スライスのスカラーが引き出せる。
@audit:ok -/
private lemma klDiv_two_slice {Ω : Type*} [MeasurableSpace Ω]
    (μ₁ μ₂ σ₁ σ₂ : Measure Ω)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂]
    (a b : ℝ≥0) :
    klDiv ((a : ℝ≥0∞) • (Measure.dirac true).prod μ₁
            + (b : ℝ≥0∞) • (Measure.dirac false).prod μ₂)
          ((a : ℝ≥0∞) • (Measure.dirac true).prod σ₁
            + (b : ℝ≥0∞) • (Measure.dirac false).prod σ₂)
      = (a : ℝ≥0∞) * klDiv ((Measure.dirac true).prod μ₁) ((Measure.dirac true).prod σ₁)
        + (b : ℝ≥0∞) * klDiv ((Measure.dirac false).prod μ₂) ((Measure.dirac false).prod σ₂) := by
  set St₁ := (Measure.dirac true).prod μ₁ with hSt₁
  set Sf₂ := (Measure.dirac false).prod μ₂ with hSf₂
  set Tt₁ := (Measure.dirac true).prod σ₁ with hTt₁
  set Tf₂ := (Measure.dirac false).prod σ₂ with hTf₂
  have _ : IsFiniteMeasure St₁ := by rw [hSt₁]; infer_instance
  have _ : IsFiniteMeasure Sf₂ := by rw [hSf₂]; infer_instance
  have _ : IsFiniteMeasure Tt₁ := by rw [hTt₁]; infer_instance
  have _ : IsFiniteMeasure Tf₂ := by rw [hTf₂]; infer_instance
  have _ : IsFiniteMeasure ((a : ℝ≥0∞) • St₁) := Measure.smul_finite St₁ ENNReal.coe_ne_top
  have _ : IsFiniteMeasure ((b : ℝ≥0∞) • Sf₂) := Measure.smul_finite Sf₂ ENNReal.coe_ne_top
  have _ : IsFiniteMeasure ((a : ℝ≥0∞) • Tt₁) := Measure.smul_finite Tt₁ ENNReal.coe_ne_top
  have _ : IsFiniteMeasure ((b : ℝ≥0∞) • Tf₂) := Measure.smul_finite Tf₂ ENNReal.coe_ne_top
  have hTtf : Tt₁ ⟂ₘ Tf₂ := mutuallySingular_dirac_prod σ₁ σ₂
  have hStTf : St₁ ⟂ₘ Tf₂ := mutuallySingular_dirac_prod μ₁ σ₂
  have hSfTt : Sf₂ ⟂ₘ Tt₁ := (mutuallySingular_dirac_prod σ₁ μ₂).symm
  -- 両側 smul で特異性を保存する局所補題
  have smul_both : ∀ {U V : Measure (Bool × Ω)} (r s : ℝ≥0),
      U ⟂ₘ V → ((r : ℝ≥0∞) • U) ⟂ₘ ((s : ℝ≥0∞) • V) :=
    fun r s h => ((h.smul (r : ℝ≥0∞)).symm.smul (s : ℝ≥0∞)).symm
  rw [klDiv_add_of_mutuallySingular ((a : ℝ≥0∞) • St₁) ((b : ℝ≥0∞) • Sf₂)
        ((a : ℝ≥0∞) • Tt₁) ((b : ℝ≥0∞) • Tf₂)
        (smul_both a b hTtf) (smul_both b a hSfTt) (smul_both a b hStTf)]
  -- 各スライスでスカラーを引き出す (klDiv_smul_same: 同一スカラー両側)
  rw [show ((a : ℝ≥0∞) • St₁) = a • St₁ from rfl,
      show ((a : ℝ≥0∞) • Tt₁) = a • Tt₁ from rfl,
      show ((b : ℝ≥0∞) • Sf₂) = b • Sf₂ from rfl,
      show ((b : ℝ≥0∞) • Tf₂) = b • Tf₂ from rfl,
      klDiv_smul_same (μ := St₁) (ν := Tt₁) a,
      klDiv_smul_same (μ := Sf₂) (ν := Tf₂) b]

/-- **層1 (gateway): joint convexity of `klDiv`.**

純 joint convexity を RD 固有の marginal 構造から切り離した一般形。
selector-extension (`Bool × Ω`) + DPI (`klDiv_map_le` で selector を `Prod.snd` 射影で
忘れる) + 二点 selector の per-slice KL 計算 (`klDiv_two_slice`) で genuine に構築する。
`_hlam₀`/`_hlam₁` (lam ∈ [0,1]) は body 未使用: `ENNReal.ofReal` の負値クランプにより任意 lam で
真 (statement を不当に弱めも強めもしない無害な framing 残置、load-bearing でない)。
@audit:ok -/
theorem klDiv_joint_convex
    {Ω : Type*} [MeasurableSpace Ω]
    {lam : ℝ} (_hlam₀ : 0 ≤ lam) (_hlam₁ : lam ≤ 1)
    (μ₁ μ₂ σ₁ σ₂ : Measure Ω)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure σ₁] [IsFiniteMeasure σ₂] :
    klDiv (ENNReal.ofReal lam • μ₁ + ENNReal.ofReal (1 - lam) • μ₂)
          (ENNReal.ofReal lam • σ₁ + ENNReal.ofReal (1 - lam) • σ₂)
      ≤ ENNReal.ofReal lam * klDiv μ₁ σ₁ + ENNReal.ofReal (1 - lam) * klDiv μ₂ σ₂ := by
  set a : ℝ≥0 := lam.toNNReal with ha
  set b : ℝ≥0 := (1 - lam).toNNReal with hb
  have hae : ENNReal.ofReal lam = (a : ℝ≥0∞) := rfl
  have hbe : ENNReal.ofReal (1 - lam) = (b : ℝ≥0∞) := rfl
  -- selector-extension on Bool × Ω
  set M : Measure (Bool × Ω) :=
    (a : ℝ≥0∞) • (Measure.dirac true).prod μ₁ + (b : ℝ≥0∞) • (Measure.dirac false).prod μ₂
    with hM
  set N : Measure (Bool × Ω) :=
    (a : ℝ≥0∞) • (Measure.dirac true).prod σ₁ + (b : ℝ≥0∞) • (Measure.dirac false).prod σ₂
    with hN
  have _ : IsFiniteMeasure ((a : ℝ≥0∞) • (Measure.dirac true).prod μ₁) :=
    Measure.smul_finite _ ENNReal.coe_ne_top
  have _ : IsFiniteMeasure ((b : ℝ≥0∞) • (Measure.dirac false).prod μ₂) :=
    Measure.smul_finite _ ENNReal.coe_ne_top
  have _ : IsFiniteMeasure ((a : ℝ≥0∞) • (Measure.dirac true).prod σ₁) :=
    Measure.smul_finite _ ENNReal.coe_ne_top
  have _ : IsFiniteMeasure ((b : ℝ≥0∞) • (Measure.dirac false).prod σ₂) :=
    Measure.smul_finite _ ENNReal.coe_ne_top
  have _ : IsFiniteMeasure M := by rw [hM]; infer_instance
  have _ : IsFiniteMeasure N := by rw [hN]; infer_instance
  -- M.map snd = numerator,  N.map snd = denominator
  have hMsnd : M.map Prod.snd = (a : ℝ≥0∞) • μ₁ + (b : ℝ≥0∞) • μ₂ := by
    rw [hM, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul]
    congr 1 <;> congr 1 <;>
      exact (Measure.snd_prod (μ := Measure.dirac _) (ν := _))
  have hNsnd : N.map Prod.snd = (a : ℝ≥0∞) • σ₁ + (b : ℝ≥0∞) • σ₂ := by
    rw [hN, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul]
    congr 1 <;> congr 1 <;>
      exact (Measure.snd_prod (μ := Measure.dirac _) (ν := _))
  -- DPI: klDiv (M.map snd)(N.map snd) ≤ klDiv M N
  have hDPI := klDiv_map_le (measurable_snd) M N
  rw [hMsnd, hNsnd] at hDPI
  -- klDiv M N = a * klDiv μ₁ σ₁ + b * klDiv μ₂ σ₂
  have hMN : klDiv M N = (a : ℝ≥0∞) * klDiv μ₁ σ₁ + (b : ℝ≥0∞) * klDiv μ₂ σ₂ := by
    rw [hM, hN, klDiv_two_slice μ₁ μ₂ σ₁ σ₂ a b,
      klDiv_dirac_prod true μ₁ σ₁, klDiv_dirac_prod false μ₂ σ₂]
  rw [hae, hbe]
  rw [hMN] at hDPI
  exact hDPI

/-! ### 層2 — RD 固有形への plumbing 適用 -/

/-- **層2: `klDiv` の joint convexity (混合測度形)**。
分母 `P` (X-marginal) は両 witness で固定、`ν.map snd` のみ線形。
層1 (`klDiv_joint_convex`) の genuine な plumbing 適用。
@audit:ok -/
theorem klDiv_mixture_le
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1)
    (P : Measure α) [IsProbabilityMeasure P]
    (ν₁ ν₂ : Measure (α × β)) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : ν₁.map Prod.fst = P) (h₂ : ν₂.map Prod.fst = P) :
    klDiv (mixtureMeasure lam ν₁ ν₂)
        (((mixtureMeasure lam ν₁ ν₂).map Prod.fst).prod
          ((mixtureMeasure lam ν₁ ν₂).map Prod.snd))
      ≤ ENNReal.ofReal lam * klDiv ν₁ ((ν₁.map Prod.fst).prod (ν₁.map Prod.snd))
        + ENNReal.ofReal (1 - lam) * klDiv ν₂ ((ν₂.map Prod.fst).prod (ν₂.map Prod.snd)) := by
  set m₁ := ν₁.map Prod.snd with hm₁
  set m₂ := ν₂.map Prod.snd with hm₂
  have _ : IsFiniteMeasure m₁ := by rw [hm₁]; exact Measure.isFiniteMeasure_map ν₁ _
  have _ : IsFiniteMeasure m₂ := by rw [hm₂]; exact Measure.isFiniteMeasure_map ν₂ _
  -- 分母 fst marginal = P, snd marginal = w•m₁ + w'•m₂
  have hfst : (mixtureMeasure lam ν₁ ν₂).map Prod.fst = P :=
    mixtureMeasure_map_fst_eq hlam₀ hlam₁ P ν₁ ν₂ h₁ h₂
  have hsnd : (mixtureMeasure lam ν₁ ν₂).map Prod.snd
      = ENNReal.ofReal lam • m₁ + ENNReal.ofReal (1 - lam) • m₂ :=
    mixtureMeasure_map_snd lam ν₁ ν₂
  -- 分母 = w•(P.prod m₁) + w'•(P.prod m₂)
  have hden : (((mixtureMeasure lam ν₁ ν₂).map Prod.fst).prod
        ((mixtureMeasure lam ν₁ ν₂).map Prod.snd))
      = ENNReal.ofReal lam • (P.prod m₁) + ENNReal.ofReal (1 - lam) • (P.prod m₂) := by
    rw [hfst, hsnd, Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right]
  -- RHS の klDiv 分母を P.prod mᵢ に揃える
  have hrhs₁ : (ν₁.map Prod.fst).prod m₁ = P.prod m₁ := by rw [h₁]
  have hrhs₂ : (ν₂.map Prod.fst).prod m₂ = P.prod m₂ := by rw [h₂]
  rw [hden, hrhs₁, hrhs₂]
  exact klDiv_joint_convex hlam₀ hlam₁ ν₁ ν₂ (P.prod m₁) (P.prod m₂)

/-! ### 層3 — R(D) convexity 主補題 (iInf press) -/

/-- **R(D) is convex**: the rate-distortion function is convex in the distortion
threshold (Cover-Thomas 10.4).

`R(λ D₁ + (1-λ) D₂) ≤ λ R(D₁) + (1-λ) R(D₂)`.

Proof: take any feasible witnesses `ν₁` (at `D₁`), `ν₂` (at `D₂`); their convex
combination `mixtureMeasure λ ν₁ ν₂` is feasible at `λ D₁ + (1-λ) D₂`
(`mixtureMeasure_feasible`), and the joint convexity of `klDiv`
(`klDiv_mixture_le`, layer 2, itself genuine via the DPI gateway
`klDiv_joint_convex`) gives the per-pair bound; pressing the `iInf` over feasible
witnesses yields convexity.

The regularity hypothesis `h_int_witness` (integrability of `d` on every joint
with `Prod.fst`-marginal `P`) is a passive regularity precondition, needed so that
the mixture witness has well-defined feasibility (`expectedDistortion` linearity).
It supplies no convexity content — the convexity flows entirely from the genuine
DPI gateway (`klDiv_map_le`), so it is not load-bearing.
@audit:ok -/
@[entry_point]
theorem rateDistortionFunction_convexOn
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P]
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₁ : lam ≤ 1) (D₁ D₂ : ℝ)
    (h_int_witness :
      ∀ (ν : Measure (α × β)), ν.map Prod.fst = P →
        Integrable (fun p => d p.1 p.2) ν) :
    rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂)
      ≤ ENNReal.ofReal lam * rateDistortionFunction d P D₁
        + ENNReal.ofReal (1 - lam) * rateDistortionFunction d P D₂ := by
  set w := ENNReal.ofReal lam with hw
  set w' := ENNReal.ofReal (1 - lam) with hw'
  -- g ν = 被 iInf 量
  set g : Measure (α × β) → ℝ≥0∞ :=
    fun ν => klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd)) with hg
  -- per-pair bound: 任意 feasible ν₁ (at D₁), ν₂ (at D₂) で
  --   R(target) ≤ w * g ν₁ + w' * g ν₂
  have h_per_pair : ∀ (ν₁ ν₂ : Measure (α × β)),
      ν₁.map Prod.fst = P → expectedDistortion d ν₁ ≤ D₁ →
      ν₂.map Prod.fst = P → expectedDistortion d ν₂ ≤ D₂ →
      rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂) ≤ w * g ν₁ + w' * g ν₂ := by
    intro ν₁ ν₂ hm₁ hd₁ hm₂ hd₂
    have hfin₁ : IsFiniteMeasure ν₁ := by
      refine ⟨?_⟩
      have : ν₁ Set.univ = P Set.univ := by
        rw [← hm₁, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
      rw [this]; exact measure_lt_top P _
    have hfin₂ : IsFiniteMeasure ν₂ := by
      refine ⟨?_⟩
      have : ν₂ Set.univ = P Set.univ := by
        rw [← hm₂, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
      rw [this]; exact measure_lt_top P _
    have hint₁ : Integrable (fun p => d p.1 p.2) ν₁ := h_int_witness ν₁ hm₁
    have hint₂ : Integrable (fun p => d p.1 p.2) ν₂ := h_int_witness ν₂ hm₂
    obtain ⟨hfeas_marg, hfeas_dist⟩ :=
      mixtureMeasure_feasible hlam₀ hlam₁ P d ν₁ ν₂ hm₁ hm₂ hd₁ hd₂ hint₁ hint₂
    calc rateDistortionFunction d P (lam * D₁ + (1 - lam) * D₂)
        ≤ klDiv (mixtureMeasure lam ν₁ ν₂)
            (((mixtureMeasure lam ν₁ ν₂).map Prod.fst).prod
              ((mixtureMeasure lam ν₁ ν₂).map Prod.snd)) :=
          rateDistortionFunction_le_of_feasible d P _ _ hfeas_marg hfeas_dist
      _ ≤ w * g ν₁ + w' * g ν₂ := klDiv_mixture_le hlam₀ hlam₁ P ν₁ ν₂ hm₁ hm₂
  -- `w * R(D)` を nested iInf に展開する補助 (w ≠ 0, ≠ ∞ のとき)
  have h_mul_iInf : ∀ (c : ℝ≥0∞) (D : ℝ), c ≠ 0 → c ≠ ⊤ →
      c * rateDistortionFunction d P D
        = ⨅ (ν : Measure (α × β)) (_ : ν.map Prod.fst = P)
            (_ : expectedDistortion d ν ≤ D), c * g ν := by
    intro c D hc0 hctop
    unfold rateDistortionFunction
    rw [ENNReal.mul_iInf_of_ne hc0 hctop]
    refine iInf_congr fun ν => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 hctop]
    refine iInf_congr fun _ => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 hctop]
  -- iInf press、境界 lam = 0, 1 で場合分け
  rcases eq_or_lt_of_le hlam₀ with hlam0 | hlam0
  · -- lam = 0: w = 0, w' = 1, target = D₂
    rw [hw, hw', ← hlam0]
    have heq : (0 : ℝ) * D₁ + (1 - 0) * D₂ = D₂ := by ring
    rw [heq]
    simp only [sub_zero, ENNReal.ofReal_zero, ENNReal.ofReal_one, zero_mul, zero_add, one_mul,
      le_refl]
  rcases eq_or_lt_of_le hlam₁ with hlam1 | hlam1
  · -- lam = 1: w = 1, w' = 0, target = D₁
    rw [hw, hw', hlam1]
    have heq : (1 : ℝ) * D₁ + (1 - 1) * D₂ = D₁ := by ring
    rw [heq]
    simp only [sub_self, ENNReal.ofReal_one, ENNReal.ofReal_zero, one_mul, zero_mul, add_zero,
      le_refl]
  -- 0 < lam < 1: 内部、w, w' ≠ 0, ≠ ∞
  have hw0 : w ≠ 0 := by rw [hw]; simp [ENNReal.ofReal_eq_zero, not_le, hlam0]
  have hwtop : w ≠ ⊤ := by rw [hw]; exact ENNReal.ofReal_ne_top
  have hw'0 : w' ≠ 0 := by
    rw [hw']; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
  have hw'top : w' ≠ ⊤ := by rw [hw']; exact ENNReal.ofReal_ne_top
  rw [h_mul_iInf w D₁ hw0 hwtop, h_mul_iInf w' D₂ hw'0 hw'top]
  -- 左の iInf (ν₁ / marg / dist) を順に剥がす
  rw [ENNReal.iInf_add]
  refine le_iInf fun ν₁ => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hm₁ => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hd₁ => ?_
  -- 右の iInf (ν₂ / marg / dist) を順に剥がす
  rw [ENNReal.add_iInf]
  refine le_iInf fun ν₂ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hm₂ => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun hd₂ => ?_
  exact h_per_pair ν₁ ν₂ hm₁ hd₁ hm₂ hd₂

end InformationTheory.Shannon
