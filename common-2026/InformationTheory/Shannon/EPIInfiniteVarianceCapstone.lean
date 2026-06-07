/-
# 無限分散 a.c. 古典 EPI — capstone (route T → 無条件 EPI dispatch genuine 接続)

route T headline `entropyPowerExt_add_ge_infinite_variance_truncation`
(`EPIInfiniteVarianceTruncation.lean` 末尾、sorryAx-free) を用いて、named wall
`entropyPowerExt_add_ge_infinite_variance`
(旧 `EPICase1SmoothingLimit.lean:1407`、`@residual(wall:epi-infinite-variance-classical)`、`sorry`)
を **genuine closure** する capstone。

## import 制約 (循環回避)

IVT (`EPIInfiniteVarianceTruncation`) は `EPICase1SmoothingLimit` を import している
(一方向)。よって wall を EPICase1SmoothingLimit 内で headline を使って証明すると循環。
本 capstone を **IVT の下流** に置き、IVT 系のみ import (`EPICase1SmoothingLimit` は IVT 経由で
推移的に利用可能)。dispatch の consumer (`EPIUncondDispatch`) は IVT を import しないが、IVT は
EPIUncondDispatch を import しないので循環なし。

## Approach

旧 wall signature と同一 (explicit X Y, `h_infvar`) の theorem を立て、
**和の有限微分エントロピー `hent_sum` の有無で case split**:

* **Case 1** (`hent_sum` 有り): route T headline
  `entropyPowerExt_add_ge_infinite_variance_truncation` を適用 (`h_infvar` 不使用)。
* **Case 2** (`¬ hent_sum`): 和の密度 `r := (P.map(X+Y)).rnDeriv vol |>.toReal` の `negMulLog`
  が非可積分。負部 `B := ∫⁻ ofReal(-(negMulLog r))` は P 版負部補題 (`integrable_negPart...`) で
  有限。`Integrable g vol ⟺ A<⊤ ∧ B<⊤` (`A := ∫⁻ ofReal(negMulLog r)`) の対偶で
  `¬integrable ∧ B<⊤ → A=⊤` → `differentialEntropyExt ν = (A:EReal) - (B:EReal) = ⊤ - (finite) = ⊤`
  → `entropyPowerExt ν = ⊤` → `le_top` で結論。

`h_infvar` は signature 互換のため保持するが load-bearing でない (Case 1 で未使用、結論を弱める
仮説)。`hX_ent`/`hY_ent` は各成分有限微分エントロピー regularity precondition。
-/
import InformationTheory.Shannon.EPIInfiniteVarianceTruncation

namespace InformationTheory.Shannon.EPIInfiniteVarianceTruncation

open MeasureTheory Filter Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1SmoothingLimit
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAdd_comm)
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **P 版 負部可積分性** — 和の密度 `r := (P.map(X+Y)).rnDeriv vol |>.toReal` (= `pX ∗ pY`,
convolution) の `negMulLog` の負部 `(negMulLog r)⁻ = max (-(negMulLog r)) 0 = (r log r)⁺` の
`volume`-可積分性。

condTrunc 版 `integrable_negPart_negMulLog_map_condTrunc_sum` (`:600`, genuine `@audit:ok`) の P 版。
condTrunc を `P` 自身に読み替え、密度同定 `rnDeriv_map_sum_ae` (`:1085`、P 版 conv density 同定) と、
`Cq = (φ pY)⁺` 可積分性を `hY_ent` から直接 (`hY_ent.neg.pos_part`) 取る (condTrunc 版が
`integrable_negMulLog_map_condTrunc` 経由だった部分の簡素化)。

機構 (route ② Jensen + Tonelli、無限分散でも moment 不要): `pX·vol = P.map X` は確率測度
(`∫ pX = 1`)。`t ↦ t log t` は凸 (`Real.convexOn_mul_log`) ゆえ Jensen 積分版
(`ConvexOn.map_integral_le`) で `(r(z) log r(z))⁺ ≤ ∫ x, pX(x)·(pY(z-x) log pY(z-x))⁺ dx`。
Tonelli + Lebesgue 平行移動不変で `∫⁻ z (r log r)⁺ ≤ 1·C < ∞`、`C = ∫ (pY log pY)⁺ < ∞` (from
`hY_ent`)。

honest: 結論は可積分性 (regularity)。仮説は a.c. + measurability + indep + 各成分有限微分
エントロピー `hX_ent`/`hY_ent`。和エントロピー可積分性 (= Case 2 で否定する量) を仮説で受けて
いない (非循環・非バンドル)。本 body は `hY_ent` のみ使用 (`hX_ent` 未使用 = より弱い仮説で成立)。

独立 honesty audit 2026-06-07 (commit c9103c6 系): 4-check 全 PASS。(1) 非循環 — body は
genuine Jensen+Tonelli 組立 (`:= h` でない)、結論を仮説に encode せず。(2) 非バンドル — `hY_ent`
は Y 単独密度 (別測度 `P.map Y`) の有限微分エントロピー precondition で `Cq=(φ pY)⁺` 可積分性供給
に使うのみ、和の密度負部 (= 結論) を bundle しない。(3) 非退化 — 具体的可積分性命題。(4) sufficiency
— `pX·vol=P.map X` が確率測度 (`∫ pX=1`) ゆえ Jensen 積分版 (`φ(∫f)≤∫φ(f)`、凸 φ=t log t) が確率
測度上で genuine 適用可能、`∫⁻(r log r)⁺ ≤ 1·C<∞`。`#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free、本監査機械確認) ゆえ proof done。
@audit:ok -/
theorem integrable_negPart_negMulLog_map_sum (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume) :
    Integrable (fun x => max (-(Real.negMulLog
      ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) 0) volume := by
  classical
  -- marginal densities and the sum density `r`.
  set pX : ℝ → ℝ := fun y => (P.map X).rnDeriv volume y |>.toReal with hpX_def
  set pY : ℝ → ℝ := fun y => (P.map Y).rnDeriv volume y |>.toReal with hpY_def
  set ν := P.map (fun ω => X ω + Y ω) with hν_def
  set r : ℝ → ℝ := fun x => (ν.rnDeriv volume x).toReal with hr_def
  -- `φ t = t log t = -(negMulLog t)`.
  set φ : ℝ → ℝ := fun t => t * Real.log t with hφ_def
  have hφ_eq : ∀ t, -(Real.negMulLog t) = φ t := by
    intro t; show -(-t * Real.log t) = t * Real.log t; ring
  -- basic measurability / nonnegativity.
  have hr_meas : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpX_meas : Measurable pX := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpY_meas : Measurable pY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpX_nn : ∀ x, 0 ≤ pX x := fun _ => ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun _ => ENNReal.toReal_nonneg
  have hφ_meas : Measurable φ := measurable_id.mul (Real.measurable_log.comp measurable_id)
  -- target integrand `G z := max (φ (r z)) 0`.
  set G : ℝ → ℝ := fun z => max (φ (r z)) 0 with hG_def
  have hG_nn : ∀ z, 0 ≤ G z := fun _ => le_max_right _ _
  have hG_meas : Measurable G := (hφ_meas.comp hr_meas).max measurable_const
  have hgoal_eq : (fun x => max (-(Real.negMulLog
      ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) 0) = G := by
    funext z; rw [hG_def]; simp only [hφ_eq, hr_def, hν_def]
  rw [hgoal_eq]
  -- `r =ᵐ convDensityAdd pX pY` (sum density identity, P-version).
  have hr_conv : r =ᵐ[volume] EPIConvDensity.convDensityAdd pX pY := by
    have h := rnDeriv_map_sum_ae P hX hY hX_ac hY_ac hXY
    filter_upwards [h] with x hx
    show (ν.rnDeriv volume x).toReal = EPIConvDensity.convDensityAdd pX pY x
    rw [hν_def, hx, ENNReal.toReal_ofReal]
    exact integral_nonneg (fun t => mul_nonneg (hpX_nn t) (hpY_nn _))
  -- `pX · vol = P.map X` is a probability measure (since `∫ pX = 1`).
  haveI hpXP : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI hpYP : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)) := by
    have hcongr : (fun x => ENNReal.ofReal (pX x)) =ᵐ[volume] (P.map X).rnDeriv volume := by
      filter_upwards [(P.map X).rnDeriv_lt_top volume] with x hx
      rw [hpX_def]; exact ENNReal.ofReal_toReal hx.ne
    rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hX_ac]
  set μX : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (pX x)) with hμX_def
  haveI hμXP : IsProbabilityMeasure μX := hpX_law ▸ hpXP
  -- `pX`'s lintegral is `1`.
  have hpX_lint : ∫⁻ x, ENNReal.ofReal (pX x) ∂volume = 1 := by
    have hu : μX Set.univ = 1 := measure_univ
    rwa [hμX_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hu
  -- `pY`'s lintegral is `1` too (needed for the `qn`-section finiteness).
  have hpY_law : P.map Y = volume.withDensity (fun x => ENNReal.ofReal (pY x)) := by
    have hcongr : (fun x => ENNReal.ofReal (pY x)) =ᵐ[volume] (P.map Y).rnDeriv volume := by
      filter_upwards [(P.map Y).rnDeriv_lt_top volume] with x hx
      rw [hpY_def]; exact ENNReal.ofReal_toReal hx.ne
    rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hY_ac]
  have hpY_lint : ∫⁻ x, ENNReal.ofReal (pY x) ∂volume = 1 := by
    have hv : (volume.withDensity (fun x => ENNReal.ofReal (pY x))) Set.univ = 1 := by
      rw [← hpY_law]; exact measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hv
  -- `pY`'s entropy integrand is integrable (the genuine use of `hY_ent`).
  have hpY_ent_int : Integrable (fun x => Real.negMulLog (pY x)) volume := hY_ent
  -- the two halves of `φ ∘ pY`:  `Cq = (φ pY)⁺`,  `Cm = (φ pY)⁻`, both integrable.
  set Cq : ℝ → ℝ := fun w => max (φ (pY w)) 0 with hCq_def
  set Cm : ℝ → ℝ := fun w => max (-(φ (pY w))) 0 with hCm_def
  have hCq_nn : ∀ w, 0 ≤ Cq w := fun _ => le_max_right _ _
  have hCm_nn : ∀ w, 0 ≤ Cm w := fun _ => le_max_right _ _
  have hCq_meas : Measurable Cq := (hφ_meas.comp hpY_meas).max measurable_const
  have hCm_meas : Measurable Cm := ((hφ_meas.comp hpY_meas).neg).max measurable_const
  have hCq_int : Integrable Cq volume := by
    have heq : Cq = fun w => max ((-(fun x => Real.negMulLog (pY x))) w) 0 := by
      funext w; show max (φ (pY w)) 0 = max (-(Real.negMulLog (pY w))) 0
      rw [hφ_eq]
    rw [heq]; exact hpY_ent_int.neg.pos_part
  have hCm_int : Integrable Cm volume := by
    have heq : Cm = fun w => max ((fun x => Real.negMulLog (pY x)) w) 0 := by
      funext w; show max (-(φ (pY w))) 0 = max (Real.negMulLog (pY w)) 0
      rw [← hφ_eq, neg_neg]
    rw [heq]; exact hpY_ent_int.pos_part
  -- finiteness of `C = ∫⁻ ofReal (Cq) = ∫⁻ ofReal ((φ pY)⁺)`.
  set C : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (Cq w) ∂volume with hC_def
  have hC_lt_top : C < ∞ := by
    have hfin := hCq_int.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hCq_nn)] at hfin
    rw [hC_def]; exact hfin
  -- ============================================================================
  -- global product-measure integrability of the three convolution kernels.
  -- `K g (z, x) = pX x * g (z - x)`.  Below `g ∈ {pY, Cq, Cm}`.
  -- ============================================================================
  have hjoint_meas : ∀ g : ℝ → ℝ, Measurable g →
      AEStronglyMeasurable (fun p : ℝ × ℝ => pX p.2 * g (p.1 - p.2)) (volume.prod volume) := by
    intro g hg
    exact ((hpX_meas.comp measurable_snd).mul
      (hg.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  -- Tonelli identity for nonneg `g`, via translation invariance.
  have hkernel_lint : ∀ g : ℝ → ℝ, Measurable g → (∀ w, 0 ≤ g w) →
      ∫⁻ z, ∫⁻ x, ENNReal.ofReal (pX x * g (z - x)) ∂volume ∂volume
        = (∫⁻ x, ENNReal.ofReal (pX x) ∂volume) * (∫⁻ w, ENNReal.ofReal (g w) ∂volume) := by
    intro g hg hg_nn
    have hswap : ∫⁻ z, ∫⁻ x, ENNReal.ofReal (pX x * g (z - x)) ∂volume ∂volume
        = ∫⁻ x, ∫⁻ z, ENNReal.ofReal (pX x * g (z - x)) ∂volume ∂volume := by
      rw [lintegral_lintegral_swap]
      exact ((hpX_meas.comp measurable_snd).mul
        (hg.comp (measurable_fst.sub measurable_snd))).ennreal_ofReal.aemeasurable
    rw [hswap]
    have hgz_meas : ∀ x : ℝ, Measurable (fun z => ENNReal.ofReal (g (z - x))) := fun x =>
      (hg.comp (measurable_id.sub_const x)).ennreal_ofReal
    have hinner : ∀ x, ∫⁻ z, ENNReal.ofReal (pX x * g (z - x)) ∂volume
        = ENNReal.ofReal (pX x) * ∫⁻ w, ENNReal.ofReal (g w) ∂volume := by
      intro x
      calc ∫⁻ z, ENNReal.ofReal (pX x * g (z - x)) ∂volume
          = ∫⁻ z, ENNReal.ofReal (pX x) * ENNReal.ofReal (g (z - x)) ∂volume := by
            apply lintegral_congr; intro z; rw [ENNReal.ofReal_mul (hpX_nn x)]
        _ = ENNReal.ofReal (pX x) * ∫⁻ z, ENNReal.ofReal (g (z - x)) ∂volume :=
            lintegral_const_mul _ (hgz_meas x)
        _ = ENNReal.ofReal (pX x) * ∫⁻ w, ENNReal.ofReal (g w) ∂volume := by
            rw [lintegral_sub_right_eq_self (fun w => ENNReal.ofReal (g w)) x]
    simp_rw [hinner]
    rw [lintegral_mul_const _ hpX_meas.ennreal_ofReal]
  -- a.e.-`z` section integrabilities.
  have hkernel_int : ∀ g : ℝ → ℝ, Measurable g → (∀ w, 0 ≤ g w) →
      (∫⁻ w, ENNReal.ofReal (g w) ∂volume) ≠ ∞ →
      Integrable (fun p : ℝ × ℝ => pX p.2 * g (p.1 - p.2)) (volume.prod volume) := by
    intro g hg hg_nn hg_fin
    refine ⟨hjoint_meas g hg, ?_⟩
    have hnn : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), 0 ≤ pX p.2 * g (p.1 - p.2) :=
      Filter.Eventually.of_forall (fun p => mul_nonneg (hpX_nn _) (hg_nn _))
    rw [hasFiniteIntegral_iff_ofReal hnn,
      lintegral_prod _ (hjoint_meas g hg).aemeasurable.ennreal_ofReal,
      hkernel_lint g hg hg_nn, hpX_lint, one_mul]
    exact lt_of_le_of_ne le_top hg_fin
  have hsec_pY : ∀ᵐ z ∂volume, Integrable (fun x => pX x * pY (z - x)) volume := by
    exact (hkernel_int pY hpY_meas hpY_nn (by rw [hpY_lint]; exact ENNReal.one_ne_top)).prod_right_ae
  have hsec_Cq : ∀ᵐ z ∂volume, Integrable (fun x => pX x * Cq (z - x)) volume := by
    exact (hkernel_int Cq hCq_meas hCq_nn (by rw [← hC_def]; exact hC_lt_top.ne)).prod_right_ae
  have hsec_Cm : ∀ᵐ z ∂volume, Integrable (fun x => pX x * Cm (z - x)) volume := by
    have hCm_fin : (∫⁻ w, ENNReal.ofReal (Cm w) ∂volume) ≠ ∞ := by
      have hfin := hCm_int.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hCm_nn)] at hfin
      exact hfin.ne
    exact (hkernel_int Cm hCm_meas hCm_nn hCm_fin).prod_right_ae
  -- ============================================================================
  -- per-`z` Jensen bound:  `G z ≤ ∫ x, pX x * Cq (z - x) ∂volume`  (a.e. `z`).
  -- ============================================================================
  have hjensen : ∀ᵐ z ∂volume, G z ≤ ∫ x, pX x * Cq (z - x) ∂volume := by
    filter_upwards [hr_conv, hsec_pY, hsec_Cq, hsec_Cm] with z hz hzpY hzCq hzCm
    set f : ℝ → ℝ := fun x => pY (z - x) with hf_def
    have hf_nn : ∀ x, 0 ≤ f x := fun _ => hpY_nn _
    have hpXofReal_meas : Measurable (fun x => ENNReal.ofReal (pX x)) := hpX_meas.ennreal_ofReal
    have hpXofReal_lt : ∀ᵐ x ∂volume, ENNReal.ofReal (pX x) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    have hμX_smul : ∀ (h : ℝ → ℝ),
        ∫ x, h x ∂μX = ∫ x, pX x * h x ∂volume := by
      intro h
      rw [hμX_def, integral_withDensity_eq_integral_toReal_smul hpXofReal_meas hpXofReal_lt]
      apply integral_congr_ae; filter_upwards with x
      rw [ENNReal.toReal_ofReal (hpX_nn x), smul_eq_mul]
    have hf_int : Integrable f μX := by
      rw [hμX_def, integrable_withDensity_iff_integrable_smul' hpXofReal_meas hpXofReal_lt]
      refine hzpY.congr ?_
      filter_upwards with x; rw [ENNReal.toReal_ofReal (hpX_nn x), smul_eq_mul]
    have hCqf_int : Integrable (fun x => max (φ (f x)) 0) μX := by
      rw [hμX_def, integrable_withDensity_iff_integrable_smul' hpXofReal_meas hpXofReal_lt]
      refine hzCq.congr ?_
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (hpX_nn x), smul_eq_mul]
    have hCmf_int : Integrable (fun x => max (-(φ (f x))) 0) μX := by
      rw [hμX_def, integrable_withDensity_iff_integrable_smul' hpXofReal_meas hpXofReal_lt]
      refine hzCm.congr ?_
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (hpX_nn x), smul_eq_mul]
    have hφf_eq : (fun x => φ (f x)) = fun x => max (φ (f x)) 0 - max (-(φ (f x))) 0 := by
      funext x
      rcases le_or_gt 0 (φ (f x)) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith : -(φ (f x)) ≤ 0)]; ring
      · rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(φ (f x)))]; ring
    have hφf_int : Integrable (fun x => φ (f x)) μX := by
      rw [hφf_eq]; exact hCqf_int.sub hCmf_int
    have hjz : φ (∫ x, f x ∂μX) ≤ ∫ x, φ (f x) ∂μX := by
      have := Real.convexOn_mul_log.map_integral_le
        (μ := μX) (f := f) (g := φ)
        Real.continuous_mul_log.continuousOn
        isClosed_Ici
        (Filter.Eventually.of_forall (fun x => hf_nn x))
        hf_int hφf_int
      simpa only [hφ_def] using this
    have hrz_eq : r z = ∫ x, f x ∂μX := by
      rw [hz]; show EPIConvDensity.convDensityAdd pX pY z = _
      rw [hμX_smul f]; rfl
    have hstep1 : φ (r z) ≤ ∫ x, φ (f x) ∂μX := by rw [hrz_eq]; exact hjz
    have hstep2 : (∫ x, φ (f x) ∂μX) ≤ ∫ x, max (φ (f x)) 0 ∂μX :=
      integral_mono hφf_int hCqf_int (fun x => le_max_left _ _)
    have hstep3 : (∫ x, max (φ (f x)) 0 ∂μX) = ∫ x, pX x * Cq (z - x) ∂volume := by
      rw [hμX_smul (fun x => max (φ (f x)) 0)]
    have hCq_int_z : (0 : ℝ) ≤ ∫ x, pX x * Cq (z - x) ∂volume :=
      integral_nonneg (fun x => mul_nonneg (hpX_nn x) (hCq_nn _))
    rw [hG_def]
    exact max_le (by rw [← hstep3]; exact le_trans hstep1 hstep2) hCq_int_z
  -- ============================================================================
  -- assemble:  `∫⁻ ofReal G ≤ ∫⁻ z ∫⁻ x ofReal (pX x * Cq (z-x)) = 1·C < ∞`.
  -- ============================================================================
  refine ⟨hG_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG_nn)]
  calc ∫⁻ z, ENNReal.ofReal (G z) ∂volume
      ≤ ∫⁻ z, ENNReal.ofReal (∫ x, pX x * Cq (z - x) ∂volume) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [hjensen] with z hz
        exact ENNReal.ofReal_le_ofReal hz
    _ ≤ ∫⁻ z, ∫⁻ x, ENNReal.ofReal (pX x * Cq (z - x)) ∂volume ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [hsec_Cq] with z hz
        calc ENNReal.ofReal (∫ x, pX x * Cq (z - x) ∂volume)
            = ∫⁻ x, ENNReal.ofReal (pX x * Cq (z - x)) ∂volume := by
              rw [ofReal_integral_eq_lintegral_ofReal hz
                (Filter.Eventually.of_forall (fun x => mul_nonneg (hpX_nn x) (hCq_nn _)))]
          _ ≤ _ := le_refl _
    _ = (∫⁻ x, ENNReal.ofReal (pX x) ∂volume) * (∫⁻ w, ENNReal.ofReal (Cq w) ∂volume) :=
        hkernel_lint Cq hCq_meas hCq_nn
    _ = C := by rw [hpX_lint, one_mul, hC_def]
    _ < ∞ := hC_lt_top

/-- **genuine wall** — 無限分散 a.c. 古典 EPI `Nₑ(X+Y) ≥ Nₑ(X) + Nₑ(Y)`。
旧 `EPICase1SmoothingLimit.entropyPowerExt_add_ge_infinite_variance` (`:1407`,
`@residual(wall:epi-infinite-variance-classical)`、`sorry`) と同一 signature の genuine 版。

機構 = `hent_sum` の case split (`h_infvar` は signature 互換のため保持、Case 1 で未使用 =
load-bearing でない、honest):
* Case 1 (`hent_sum` 有り): route T headline 適用 (genuine, sorryAx-free)。
* Case 2 (`¬ hent_sum`): 和エントロピー非可積分 → 負部有限 (P 版負部補題) → 正部 `A=⊤` →
  `differentialEntropyExt ν = ⊤` → `entropyPowerExt ν = ⊤` → `le_top`。

honest: `h_infvar` は結論を弱める仮説で load-bearing でない (Case 1 で未使用)。
`hX_ent`/`hY_ent` は各成分有限微分エントロピー regularity precondition。route T で genuine
closure 済 (旧 Lieb-Young / Brascamp-Lieb 壁主張は FALSE WALL — conditioning truncation で
moment 非依存に閉じる)。

独立 honesty audit 2026-06-07 (commit c9103c6 系): 4-check 全 PASS。(1) 非循環 — body は genuine
case split (`:= h` でない)。(2) 非バンドル — `h_infvar` は **unused** (Case 1/2 とも未使用) =
theorem を弱める仮説で load-bearing でなく honest (signature 互換のため保持、無くても成立 = より強い)。
`hX_ent`/`hY_ent` は regularity precondition。(3) **非退化 (核心チェック)** — Case 2 (`¬hent_sum`) は
`differentialEntropyExt ν = A − B` (A=正部 lintegral、B=負部 lintegral) で **B<⊤ を P 版負部補題で
genuine に供給**してから `¬hent_sum ∧ B<⊤ → A=⊤` を導出、`A−B = ⊤−finite = ⊤` (`EReal.top_sub`) →
`entropyPowerExt=⊤` → `le_top`。危険枝 `B=⊤` (h=−∞ → `entropyPowerExt=0` → EPI 偽) を B<⊤ で確実に
回避 = 退化境界 (h=−∞) を突いた vacuous closure ではない。(4) sufficiency — Case 1 は headline 引数
完全一致 thread、Case 2 は le_top、両枝で結論 follow。`#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free、本監査機械確認) ゆえ proof done。
@audit:ok -/
theorem entropyPowerExt_add_ge_infinite_variance
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (h_infvar : ¬ (Integrable (fun ω => (X ω) ^ 2) P ∧ Integrable (fun ω => (Y ω) ^ 2) P)) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- the sum law `ν := P.map (X+Y)` and its absolute continuity.
  set ν : Measure ℝ := P.map (fun ω => X ω + Y ω) with hν_def
  have hν_ac : ν ≪ volume := by
    rw [hν_def]
    have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
      rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
    rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac
  by_cases hent_sum : Integrable
      (fun x => Real.negMulLog (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume
  · -- Case 1: route T headline applies (`h_infvar` unused).
    exact entropyPowerExt_add_ge_infinite_variance_truncation P hX hY hXY hX_ac hY_ac
      hX_ent hY_ent hent_sum
  · -- Case 2: sum entropy non-integrable ⇒ `differentialEntropyExt ν = ⊤` ⇒ `Nₑ ν = ⊤`.
    -- the sum density `r` and its `negMulLog`.
    set g : ℝ → ℝ := fun x => Real.negMulLog ((ν.rnDeriv volume x).toReal) with hg_def
    have hg_meas : Measurable g :=
      (Real.continuous_negMulLog.measurable.comp
        (Measure.measurable_rnDeriv _ _).ennreal_toReal)
    -- B := ∫⁻ ofReal(-(g x))  is finite (P-version negative-part lemma).
    set B : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (-(g x)) ∂volume with hB_def
    have hB_lt_top : B < ⊤ := by
      have hint := integrable_negPart_negMulLog_map_sum P hX hY hX_ac hY_ac hXY hY_ent
      have hnn : ∀ x, (0 : ℝ) ≤ max (-(g x)) 0 := fun _ => le_max_right _ _
      have hfin := hint.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)] at hfin
      -- `∫⁻ ofReal (max (-(g x)) 0) = ∫⁻ ofReal (-(g x))`  (negative part = max with 0,
      -- and `ofReal` ignores the difference on the region where `-(g x) ≤ 0`).
      have heq : (∫⁻ x, ENNReal.ofReal (max (-(g x)) 0) ∂volume)
          = ∫⁻ x, ENNReal.ofReal (-(g x)) ∂volume := by
        apply lintegral_congr; intro x
        rcases le_or_gt 0 (-(g x)) with h | h
        · rw [max_eq_left h]
        · rw [max_eq_right h.le, ENNReal.ofReal_of_nonpos h.le, ENNReal.ofReal_of_nonpos (by linarith)]
      rw [heq] at hfin; rw [hB_def]; exact hfin
    -- A := ∫⁻ ofReal(g x).  From `¬ hent_sum` and `B < ⊤` we get `A = ⊤`.
    set A : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (g x) ∂volume with hA_def
    have hA_top : A = ⊤ := by
      -- `¬ Integrable g` ⇒ `¬ HasFiniteIntegral g` ⇒ `∫⁻ ‖g‖ₑ = ⊤` ⇒ `A + B = ⊤`.
      have hnotfin : ¬ HasFiniteIntegral g volume := by
        intro hfin
        exact hent_sum ⟨hg_meas.aestronglyMeasurable, hfin⟩
      have henorm_top : (∫⁻ x, ‖g x‖ₑ ∂volume) = ⊤ := by
        by_contra h
        exact hnotfin (hasFiniteIntegral_iff_enorm.mpr (lt_of_le_of_ne le_top h))
      -- `∫⁻ ‖g‖ₑ = A + B`.
      have hsplit : (∫⁻ x, ‖g x‖ₑ ∂volume) = A + B := by
        rw [hA_def, hB_def, ← lintegral_add_left
          (Measurable.ennreal_ofReal hg_meas) (fun x => ENNReal.ofReal (-(g x)))]
        apply lintegral_congr; intro x
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
        rcases le_or_gt 0 (g x) with h | h
        · have hneg : ENNReal.ofReal (-(g x)) = 0 :=
            ENNReal.ofReal_of_nonpos (by linarith)
          rw [abs_of_nonneg h, hneg, add_zero]
        · have hpos : ENNReal.ofReal (g x) = 0 :=
            ENNReal.ofReal_of_nonpos h.le
          rw [abs_of_neg h, hpos, zero_add]
      rw [hsplit] at henorm_top
      -- `A + B = ⊤` with `B < ⊤` ⇒ `A = ⊤`.
      by_contra hA
      exact (ENNReal.add_lt_top.mpr ⟨lt_of_le_of_ne le_top hA, hB_lt_top⟩).ne henorm_top
    -- `differentialEntropyExt ν = (A : EReal) - (B : EReal) = ⊤ - finite = ⊤`.
    have hdiff_top : differentialEntropyExt ν = ⊤ := by
      rw [differentialEntropyExt_of_ac hν_ac]
      show ((A : EReal) - (B : EReal)) = ⊤
      rw [hA_top, EReal.coe_ennreal_top]
      exact EReal.top_sub (by
        rw [Ne, EReal.coe_ennreal_eq_top_iff]; exact hB_lt_top.ne)
    -- `Nₑ ν = ⊤`, conclude.
    have hN_top : entropyPowerExt ν = ⊤ := entropyPowerExt_eq_top_of_diffEntExt_top hdiff_top
    rw [ge_iff_le, hN_top]
    exact le_top

end InformationTheory.Shannon.EPIInfiniteVarianceTruncation
