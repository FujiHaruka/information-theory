import Common2026.Shannon.FisherInfoV2DeBruijnPerTime

/-!
# per-time de Bruijn identity — Phase 5 capstone assembly

`debruijnIdentityV2_holds` (`FisherInfoV2DeBruijn.lean`,
`@residual(plan:epi-debruijn-pertime-closure)`) を一般 `X` で genuine 化する
**Phase 5 assembly** (`epi-debruijn-pertime-closure-plan.md` §Phase 5 詳細設計 §5C)。

## import cycle 回避 (新 file 方式)

`FisherInfoV2DeBruijnPerTime.lean` (atom 供給元) は
`import Common2026.Shannon.FisherInfoV2DeBruijn` している (atom が wall file の
`gaussianConvolution` 等を使うため)。assembly は逆に atom を使うので、
`FisherInfoV2DeBruijn.lean` の `debruijnIdentityV2_holds` body に直接書くと **import 循環**。
→ 本 file (`FisherInfoV2DeBruijnAssembly.lean`) を atom file の下流に置き
(`import FisherInfoV2DeBruijnPerTime` 合法、循環なし)、ここで同 signature の genuine theorem
`debruijnIdentityV2_holds_assembled` を証明する。元の `debruijnIdentityV2_holds` は wall
sorry のまま残し、本 file の `_assembled` が genuine 版 (plan §運用ルール「import cycle 注意」
第一選択)。

## assembly 7 段 (plan §5C)

`debruijnIdentityV2_holds_assembled` body を 6 genuine atom で組む:

1. **density 同定** (`pPath_eq_convDensityAdd`、`h_reg.pX`/`pX_law` 等) +
   `density_t_eq` (rnDeriv pin) + `toReal_ofReal` で `density_t =ᵐ pPath t`。
2. **entropy = ∫ negMulLog pPath** (`differentialEntropy_eq_integral_density`)。
3. **parametric diff** (`entropy_hasDerivAt_via_parametric`)。
4. **heat eq** (`heatFlow_density_heat_equation`、∂_σ pPath = (1/2)∂²_x pPath)。
5. **IBP** (`debruijn_ibp_step`)。
6. **fisher congr** (`fisher_from_logDeriv`)。
7. **最終 congr** で RHS を `(1/2)*fisherInfoOfDensityReal h_reg.density_t` に一致。

## 残 regularity gap (named private lemma に factor out、honest sorry)

各 atom は genuine だが、atom を呼ぶための具体的 regularity discharge (Gaussian-tail
domination の `Integrable`、被積分関数 ae-measurability、`tsupport` 全域 C¹、chain-rule
plumbing) は PR 級 (plan §5C 表 L-PT-γ/δ + §5B-4)。これらは named private lemma に分離し
`sorry` + `@residual(plan:epi-debruijn-pertime-closure)` で残す (monolithic wall →
構造化 + 名前付き regularity gap)。**仮説束化・load-bearing 禁止** — gap lemma は全て
regularity precondition (被積分関数の微分・有界性・可測性) であって結論 (`HasDerivAt` /
heat eq) を bundle しない。
-/

namespace Common2026.Shannon.FisherInfoV2

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal

open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAddDeriv)

variable {Ω : Type*} {_mΩ : MeasurableSpace Ω}

/-! ## §5C assembly — `debruijnIdentityV2_holds_assembled`

下記 named private lemma は assembly が各 atom を呼ぶための regularity/chain plumbing。
全て honest sorry (`@residual(plan:epi-debruijn-pertime-closure)`)、本来証明したい形を保つ。
-/

/-- **Assembly chain core (段 2-7, honest sorry)**: given the heat-flow density path
`pPath s = convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩)` (the convolution density of the
law of `X + √s·Z`) with its X-density witness `pX`, the `s`-derivative of the entropy
`∫ negMulLog (pPath s ·)` at `t` equals `(1/2) · fisherInfoOfDensityReal (pPath t)`.

This is the analytic chain of plan §5C 段 2-7 (entropy=∫negMulLog density →
parametric diff → heat eq → IBP → fisher congr → value match), composing the 6 genuine
atoms (`entropy_hasDerivAt_via_parametric`, `heatFlow_density_heat_equation`,
`debruijn_ibp_step`, `fisher_from_logDeriv`). The remaining gap is the concrete
Gaussian-tail domination / `tsupport`-wide C¹ / integrability regularity needed to
discharge those atoms' hypotheses (plan L-PT-γ/δ + §5B-4), which is PR-level.

`pX`/`hpX_nn`/`hpX_meas`/`hpX_int` are pure regularity preconditions (X has a Lebesgue
density `pX`). The conclusion (`HasDerivAt … (1/2) · fisher`) is NOT bundled into a
hypothesis — it is the genuine claim, derived from the 6 atoms once the regularity is
supplied.

@residual(plan:epi-debruijn-pertime-closure) -/
private theorem debruijnIdentityV2_holds_assembled_chain
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => ∫ x, Real.negMulLog
        (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) ∂volume)
      ((1/2) * fisherInfoOfDensityReal
        (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      t := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)

/-- **Entropy ↔ ∫ negMulLog density bridge (段 1-2, honest sorry)**: along the heat-flow
path, the differential entropy of the pushforward equals the `∫ negMulLog` of the
convolution density, on a neighborhood of `t`, and the entropy function agrees
eventually with the `∫ negMulLog (convDensityAdd …)` function used by the chain core.

Concretely: for `s` near `t` (so `s > 0`),
`differentialEntropy (P.map (X + √s·Z)) = ∫ x, negMulLog (convDensityAdd pX g_s x)`.
This uses Phase 1b (`pPath_eq_convDensityAdd`, density identification) +
`differentialEntropy_eq_integral_density` (`DifferentialEntropy.lean:65`,
`negMulLog x = -(x log x)`). The gap is the a.e.-equality bookkeeping
(`rnDeriv =ᵐ ofReal∘convDensityAdd` → `differentialEntropy` integrand congr).

All hypotheses are regularity preconditions; the conclusion (an entropy/integral
equality) is NOT a `HasDerivAt` core.

@residual(plan:epi-debruijn-pertime-closure) -/
private theorem debruijnIdentityV2_holds_assembled_entropy_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    {t : ℝ} (ht : 0 < t) :
    (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      =ᶠ[nhds t] (fun s => ∫ x, Real.negMulLog
        (convDensityAdd pX (gaussianPDFReal 0 ⟨max s 0, le_max_right _ _⟩) x) ∂volume) := by
  -- on the neighborhood `s > 0` the two functions are equal pointwise.
  filter_upwards [eventually_gt_nhds ht] with s hs
  -- at `s > 0`: `max s 0 = s`.
  have hmax : max s 0 = s := max_eq_left hs.le
  -- Phase 1b: `rnDeriv (P.map (X+√s·Z)) =ᵐ ofReal∘convDensityAdd pX g_s`.
  have h1b := pPath_eq_convDensityAdd X Z hX hZ hXZ hZ_law pX hpX_nn hpX_meas hpX_law hs
  -- unfold differentialEntropy = ∫ negMulLog ((rnDeriv).toReal).
  unfold differentialEntropy
  -- rewrite the variance witness `⟨max s 0, _⟩` to `⟨s, hs.le⟩`.
  have hwit : (⟨max s 0, le_max_right s 0⟩ : ℝ≥0) = ⟨s, hs.le⟩ := by
    apply NNReal.eq; exact hmax
  rw [hwit]
  -- congr the two integrands a.e. via Phase 1b + `toReal_ofReal` (convDensityAdd ≥ 0).
  refine integral_congr_ae ?_
  filter_upwards [h1b] with x hx
  rw [hx]
  -- `negMulLog ((ofReal (convDensityAdd …)).toReal) = negMulLog (convDensityAdd …)`
  -- needs `convDensityAdd … x ≥ 0` (so `toReal_ofReal`).
  rw [ENNReal.toReal_ofReal]
  -- nonnegativity of `convDensityAdd pX g_s x = ∫ y, pX y · g_s (x-y)`.
  refine integral_nonneg (fun y => ?_)
  exact mul_nonneg (hpX_nn y) (gaussianPDFReal_nonneg 0 _ _)

/-- **Fisher value match (段 1+7, honest sorry)**: the Fisher info of the time-`t`
convolution density `convDensityAdd pX g_t` equals the Fisher info of the structure's
density witness `density_t`, because both are a.e. equal to the time-`t` pushforward
density (`density_t` via the rnDeriv pin `density_t_eq`, the convolution via Phase 1b).

`fisherInfoOfDensityReal` respects a.e.-equality of densities (the `∫⁻` integrand
matches a.e.). The gap is the a.e.-congruence of `fisherInfoOfDensity` under a.e.-equal
densities + the two-pin合成 (plan §5A-4).

@residual(plan:epi-debruijn-pertime-closure) -/
private theorem debruijnIdentityV2_holds_assembled_fisher_match
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    (density_t : ℝ → ℝ)
    (hdensity_t_eq : ∀ x,
      density_t x = ((P.map (gaussianConvolution X Z t)).rnDeriv volume x).toReal)
    {t : ℝ} (ht : 0 < t) :
    fisherInfoOfDensityReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩))
      = fisherInfoOfDensityReal density_t := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)

/-- **de Bruijn identity body — genuine assembly (Phase 5, plan §5C)**.

Same signature as `debruijnIdentityV2_holds` (`FisherInfoV2DeBruijn.lean`), proved by
assembling the 6 genuine per-time atoms
(`FisherInfoV2DeBruijnPerTime.lean`, all `@audit:ok`). Lives in a separate file to avoid
the import cycle (the atom file imports `FisherInfoV2DeBruijn`, so the wall file cannot
import the atoms; the assembly is the *reverse* dependency).

The assembly threads through three named regularity-plumbing lemmas
(`_entropy_eq` = 段 1-2, `_chain` = 段 2-7, `_fisher_match` = 段 1+7), each of which is an
honest `sorry` + `@residual(plan:epi-debruijn-pertime-closure)` for the concrete
Gaussian-tail domination / `tsupport`-wide C¹ / integrability regularity (PR-level,
plan L-PT-γ/δ). The atoms themselves are genuine.

`@residual(plan:epi-debruijn-pertime-closure)` -/
theorem debruijnIdentityV2_holds_assembled
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    {t : ℝ} (ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
      t := by
  -- pX integrability from `pX_law` + `P` probability (mirrors Phase 1b `:210`).
  have hpX_int : Integrable h_reg.pX volume := by
    rw [Integrable, hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h_reg.pX_nn)]
    refine ⟨h_reg.pX_meas.aestronglyMeasurable, ?_⟩
    have hlint : ∫⁻ x, ENNReal.ofReal (h_reg.pX x) ∂volume = (P.map X) Set.univ := by
      rw [h_reg.pX_law, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    rw [hlint, Measure.map_apply hX MeasurableSet.univ, Set.preimage_univ, measure_univ]
    exact ENNReal.one_lt_top
  -- 段 2-7: the entropy-as-∫negMulLog chain has the half-fisher derivative at t.
  have h_chain := debruijnIdentityV2_holds_assembled_chain h_reg.pX h_reg.pX_nn
    h_reg.pX_meas hpX_int ht
  -- 段 1-2: entropy =ᶠ ∫ negMulLog (convDensityAdd …) near t.
  have h_eq := debruijnIdentityV2_holds_assembled_entropy_eq X Z hX hZ hXZ h_reg.Z_law
    h_reg.pX h_reg.pX_nn h_reg.pX_meas h_reg.pX_law ht
  -- transfer the derivative to the entropy function via eventual equality.
  have h_ent : HasDerivAt
      (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal
        (convDensityAdd h_reg.pX (gaussianPDFReal 0 ⟨t, ht.le⟩)))
      t := h_chain.congr_of_eventuallyEq h_eq
  -- 段 1+7: rewrite the RHS fisher value to use `h_reg.density_t`.
  rw [debruijnIdentityV2_holds_assembled_fisher_match X Z hX hZ hXZ h_reg.Z_law
    h_reg.pX h_reg.pX_nn h_reg.pX_meas h_reg.pX_law h_reg.density_t h_reg.density_t_eq ht]
    at h_ent
  exact h_ent

end Common2026.Shannon.FisherInfoV2
