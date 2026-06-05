import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.EPICase1RatioLimit

/-!
# EPI case-1 sum-instance de Bruijn producer (L-Sum-struct closure)

This file supplies the sum-instance regularity hypothesis
`IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` consumed by the case-1 final wrapper
`entropyPower_add_ge_case1_of_methodX` (`EPICase1RatioLimit.lean:1517-1518`).

The core obstacle is that the sum noise `Z_X+Z_Y ∼ 𝒩(0,2)` (variance `2`) is type-incompatible
with the unit-variance hardcode in `IsRegularDeBruijnHypV2.Z_law` (`gaussianReal 0 1`,
`FisherInfoV2DeBruijn.lean:210`). See `docs/shannon/epi-case1-sum-producer-plan.md`.

## Route 決定 (M1, 2026-06-05, 実機械確認済)

blast radius 実測:
* `IsRegularDeBruijnHypV2` consumer = **13 file / 50+ 件** (`rg -c IsRegularDeBruijnHypV2`)。
  (b-2) で既存 structure の `Z_law` (および `density_t_eq` の variance carrier) を
  general-variance 化すると、全 consumer の breakage が深刻。
* (b-1) 新規 sum-専用 general-variance structure は blast radius ゼロだが、wrapper signature
  `h_reg_sum : IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` (`:1517-1518`) が
  `IsDeBruijnRegularityHyp` を**固定で要求**するため、producer の返り値型を新 structure に
  差し替えられない (wrapper 全面改変 = (c) ルートになり影響大)。

M1 probe (本 file 旧 skeleton) で `reg_at .Z_law` の obligation が verbatim
`P.map (fun ω => Z_X ω + Z_Y ω) = gaussianReal 0 1` であることを `show` で実機械確認した。
sum noise の真の law は `gaussianReal 0 2` (`hZXZY_law` で導出可能、下記 body) なので、この field
を genuine に閉じることは **数学的に不可能** (FALSE statement、`gaussianReal 0 1 ≠ gaussianReal 0 2`)。

→ 採用ルート: **既存 `IsDeBruijnRegularityHyp` を返す形を保ち、genuine に埋まる field
(`density_t` / `pX_sum` series / `density_t_eq` / `integrable_deriv` の bound 部) は埋め、
唯一 FALSE-as-stated な `Z_law` field を defect マーカーで明示**。`integrable_deriv` の
`t`-可測性は残1 (X/Y producer) と同型障害なので honest tier-2 residual で compound park。

**独立監査 (2026-06-06)**: `Z_law` field は producer の真の仮説下で uninhabitable
(`P.map (Z_X+Z_Y) = gaussianReal 0 1` vs 真の law `gaussianReal 0 2`、機械確認済)。これは
plan-residual ではなく **false-statement defect** (`@audit:defect(false-statement)`)。
真の closure は `IsRegularDeBruijnHypV2` の `Z_law` general-variance 化 (structure 改変、
successor plan `epi-case1-debruijn-genvar-struct-plan` 要起草)。詳細は producer docstring 参照。
他 field (density 系 + `integrable_deriv` bound) は genuine、保持価値あり。
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace InformationTheory.Shannon.EPICase1SumProducer

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **PS-1/2/3 sum producer**: case-1 方針X (unit-noise) の前提から sum-instance
`IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` を供給する。

`pX_sum := (P.map (X+Y)).rnDeriv volume |>.toReal` を sum input `S := X+Y` の Lebesgue 密度
witness とし、X/Y producer (`isDeBruijnRegularityHyp_of_methodX_unitnoise`,
`EPICase1RatioLimit.lean:1936`) の pX-series plumbing を `S=X+Y` で再利用する。

**追加 precondition は全て regularity** (load-bearing でない):
* `hXY_ac : (P.map (X+Y)) ≪ volume` — sum input が Lebesgue 密度を持つ (rnDeriv witness 用)
* `h_mom_S : Integrable (fun ω => (X ω+Y ω)^2) P` — sum の有限2次モーメント (pX_mom 用)
* `h_fisher_S` / `hreg_pXS` / `hnorm_pXS` / `hready_pXS` — 残1 と同型の finite-Fisher +
  regular-density + normalization + `IsBlachmanConvReady` bundle (integrable_deriv の bound 部、
  PB-2b `fisherInfoOfDensity_convDensityAdd_le` 適用用)。`IsBlachmanConvReady` の全 field は
  `Integrable (…)` / `∃ M, |·| ≤ M` / `0 < …` で不等式核を encode しない。

これらは X/Y producer の同名 precondition と同種 (sum input への regularity 要求)。
de Bruijn / Fisher 単調性の不等式核は一切 bundle しない。

**唯一の honesty 上の制約 (DEFECT, false-statement)**: `reg_at .Z_law` field は unit-hardcode
`P.map (Z_X+Z_Y) = gaussianReal 0 1` を要求するが、sum noise の真の law は `gaussianReal 0 2`
(独立 Gaussian の和、本 body で `hZXZY_law` として導出)。`gaussianReal 0 1 ≠ gaussianReal 0 2`
(`gaussianReal_ext_iff` で variance `1≠2`、独立監査 2026-06-06 機械確認) なので `Z_law` field
obligation は producer の真の仮説下で **FALSE-as-stated = 充足不能型**。producer の仮説集合は
矛盾せず充足可能 (独立標準正規 2 つで全 regularity + law/indep が成立、`hZXZY_law` 自身が
`gaussianReal 0 2` を導出する = 仮説に隠れ矛盾なし) なので vacuous-truth の抜け道もない。

これは `@residual(plan:...)` の誤分類だった: 当該 plan (`epi-case1-sum-producer-plan`、撤退ライン
L-Sum-struct-park) は producer 単独で `Z_law` を closure **しない**ことを自認しており、slug が
closure を約束できない。真の closure は `IsRegularDeBruijnHypV2` の `Z_law` field を
general-variance 化 (`gaussianReal 0 v_Z` + v_Z field、prior art `IsHeatFlowEndpointRegular`
`EPIG2HeatFlowContinuity.lean:352`) する **structure 改変** (別 plan・別 wave、blast radius 13
file / 50+ consumer または sum 専用新 structure + wrapper signature 改変)。第一選択 (定義書換で
sorry を proof body の honest residual に逃がす) が当該 session scope 外 (structure 改変は本 file
外への影響) なため、第二選択の暫定 defect マーカーを付与する。

@audit:defect(false-statement)
@audit:closed-by-successor(epi-case1-debruijn-genvar-struct-plan) -/
noncomputable def isDeBruijnRegularityHyp_sum_of_methodX_unitnoise
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hZX : Measurable Z_X) (hZY : Measurable Z_Y)
    (hZXZY_indep : IndepFun Z_X Z_Y P)
    (hZX_law : P.map Z_X = gaussianReal 0 1) (hZY_law : P.map Z_Y = gaussianReal 0 1)
    -- sum-input regularity (all preconditions, NOT load-bearing):
    (hXY_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume)
    (h_mom_S : Integrable (fun ω => (X ω + Y ω) ^ 2) P)
    (h_fisher_S : InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
        (fun x => ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) ≠ ∞)
    (hreg_pXS : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        (fun x => ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal))
    (hnorm_pXS : ∫ x, ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal ∂volume = 1)
    (hready_pXS : ∀ v : ℝ≥0, v ≠ 0 →
        InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
          (fun x => ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)
          (gaussianPDFReal 0 v)) :
    InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp
      (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P := by
  classical
  -- Real density witness for `S := X+Y` from a.c. (pX-series plumbing reused from the X/Y
  -- producer `EPICase1RatioLimit.lean:1957-1980` with `S = X+Y`).
  set S : Ω → ℝ := fun ω => X ω + Y ω with hS_def
  have hS_meas : Measurable S := hX.add hY
  set pXS : ℝ → ℝ := fun x => ((P.map S).rnDeriv volume x).toReal with hpXS_def
  have hpXS_nn : ∀ x, 0 ≤ pXS x := fun x => ENNReal.toReal_nonneg
  have hpXS_meas : Measurable pXS :=
    ((P.map S).measurable_rnDeriv volume).ennreal_toReal
  have hpXS_law : P.map S = volume.withDensity (fun x => ENNReal.ofReal (pXS x)) := by
    have hfin : ∀ᵐ x ∂volume, (P.map S).rnDeriv volume x < ∞ :=
      Measure.rnDeriv_lt_top (P.map S) volume
    have hcongr : (fun x => ENNReal.ofReal (pXS x)) =ᵐ[volume]
        (P.map S).rnDeriv volume := by
      filter_upwards [hfin] with x hx
      simp only [hpXS_def, ENNReal.ofReal_toReal hx.ne]
    rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hXY_ac]
  have hpXS_mom : Integrable (fun y => y ^ 2 * pXS y) volume := by
    have hsq_law : Integrable (fun y => y ^ 2) (P.map S) := by
      rw [integrable_map_measure
        ((by fun_prop : Measurable (fun y : ℝ => y ^ 2)).aestronglyMeasurable)
        hS_meas.aemeasurable]
      simpa [Function.comp] using h_mom_S
    rw [hpXS_law] at hsq_law
    rw [integrable_withDensity_iff_integrable_smul₀'
      hpXS_meas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at hsq_law
    refine hsq_law.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hpXS_nn x)]; ring
  refine
    { density_path := fun t => InformationTheory.Shannon.EPIConvDensity.convDensityAdd pXS
        (gaussianPDFReal 0 t.toNNReal),
      reg_at := fun t ht =>
        { Z_law := ?_zlaw
          density_t := InformationTheory.Shannon.EPIConvDensity.convDensityAdd pXS
            (gaussianPDFReal 0 ⟨t, ht.le⟩)
          density_t_eq := fun _ _ => rfl
          pX := pXS
          pX_nn := hpXS_nn
          pX_meas := hpXS_meas
          pX_law := hpXS_law
          pX_mom := hpXS_mom }
      density_t_eq := ?_topdteq
      integrable_deriv := ?_intderiv }
  · -- Z_law: PARK. The unit-hardcode requires `P.map (Z_X+Z_Y) = gaussianReal 0 1`, but the
    -- genuine sum-noise law is `gaussianReal 0 2` (FALSE-as-stated). The honest derivation of
    -- the *true* law is recorded here for the auditor; the field obligation itself cannot be
    -- discharged without general-variance structure surgery (out of session scope, see header).
    have hZXZY_law : P.map (fun ω => Z_X ω + Z_Y ω) = gaussianReal 0 2 := by
      have h := gaussianReal_add_gaussianReal_of_indepFun hZXZY_indep hZX_law hZY_law
      have h_eq : (Z_X + Z_Y) = fun ω => Z_X ω + Z_Y ω := by funext ω; rfl
      rw [h_eq] at h
      have h2 : (1 : ℝ≥0) + 1 = 2 := by norm_num
      rw [h2] at h
      simpa using h
    -- `gaussianReal 0 1 ≠ gaussianReal 0 2`: the obligation `P.map (Z_X+Z_Y) = gaussianReal 0 1`
    -- contradicts `hZXZY_law` (machine-verified FALSE under the producer's true, satisfiable
    -- hypotheses; independent audit 2026-06-06). This is NOT a closeable plan-residual: the
    -- field obligation is uninhabitable without general-variance structure surgery.
    -- @audit:defect(false-statement)
    -- @audit:closed-by-successor(epi-case1-debruijn-genvar-struct-plan)
    sorry
  · -- top-level density_t_eq: the V2-internal density_t is pinned to density_path t (both =
    -- conv-pin), identical to the X/Y producer (`EPICase1RatioLimit.lean:1996-2000`).
    intro t ht
    have : t.toNNReal = (⟨t, ht.le⟩ : ℝ≥0) := by
      apply NNReal.eq; exact Real.coe_toNNReal t ht.le
    rw [this]
  · -- integrable_deriv: design (b) bound is genuine (PB-2b fires on pXS/g_t via the threaded
    -- sum-input regularity), identical to the X/Y producer; only the `t`-measurability is parked
    -- (same isomorphic obstacle as 残1 X/Y producer `EPICase1RatioLimit.lean:2041`).
    intro T hT
    simp only [InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2_def]
    set C : ℝ := (1 / 2) *
      (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity pXS).toReal with hC_def
    have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) T,
        (1 / 2) * (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pXS
              (gaussianPDFReal 0 t.toNNReal))).toReal ≤ C := by
      intro t ht
      have htpos : 0 < t := ht.1
      have hv_ne : t.toNNReal ≠ 0 := by
        simp only [ne_eq, Real.toNNReal_eq_zero, not_le]; exact htpos
      have hregY : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
          (gaussianPDFReal 0 t.toNNReal) :=
        InformationTheory.Shannon.EPIBlachmanGaussianWitness.isRegularDensityV2_gaussianPDFReal hv_ne
      have hnormY : ∫ x, gaussianPDFReal 0 t.toNNReal x ∂volume = 1 :=
        ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 hv_ne
      have hmono := InformationTheory.Shannon.EPICase1RatioLimit.fisherInfoOfDensity_convDensityAdd_le
        pXS (gaussianPDFReal 0 t.toNNReal)
        hreg_pXS hregY hnorm_pXS hnormY (hready_pXS _ hv_ne)
      simp only [hC_def]
      exact mul_le_mul_of_nonneg_left hmono (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    refine MeasureTheory.Measure.integrableOn_of_bounded
      (by
        simp only [ne_eq]
        exact (measure_Ioc_lt_top).ne)
      ?_meas (M := C) ?_bdd
    · -- `t`-measurability: same obstacle as 残1 X/Y producer (no Mathlib parameter-measurability
      -- lemma for `logDeriv (convDensityAdd …)` lintegral). The bound is genuine; only this is
      -- parked, and it is transitive on the 残1 closure.
      -- @residual(plan:epi-case1-sum-producer-plan,plan:epi-case1-debruijn-producer-plan)
      sorry
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
      intro t ht
      have hnn : (0 : ℝ) ≤ (1 / 2) *
          (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
            (InformationTheory.Shannon.EPIConvDensity.convDensityAdd pXS
              (gaussianPDFReal 0 t.toNNReal))).toReal :=
        mul_nonneg (by norm_num) ENNReal.toReal_nonneg
      rw [Real.norm_of_nonneg hnn]
      exact hbound t ht

end InformationTheory.Shannon.EPICase1SumProducer
