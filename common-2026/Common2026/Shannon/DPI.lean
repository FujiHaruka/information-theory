import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.MeasureTheory.Measure.Prod
import Common2026.Shannon.MutualInfo

/-!
# Data processing inequality for mutual information (Phase 4-α DPI)

Shannon ムーンショット ([`docs/shannon-moonshot-plan.md`](../../../docs/shannon-moonshot-plan.md))
の Phase 4-α DPI: `I(X; f(Y)) ≤ I(X; Y)` (deterministic post-processing on Y).

戦略 (計画書 `:223`, 在庫調査 `docs/shannon-mathlib-inventory.md` B 節):
1. **核補題** `klDiv_map_le`: 一般 pushforward DPI `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν`。
   Mathlib に直接補題は **不在**。`ConvexOn.apply_rnDeriv_ae_le_integral` (`MeasureTheory/
   Measure/Decomposition/IntegralRNDeriv.lean:137`) の Jensen 不等式と `Measure.rnDeriv_map`
   (一般 Measurable 形, `ConditionalExpectation/RadonNikodym.lean:83`) で構築する。
2. **mutualInfo の DPI 系**: 核補題を `Prod.map id f` に適用し、`map_prod_map` と
   `compProd_map_condDistrib` の plumbing で `mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo`
   を導く。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]
variable {Z : Type*} [MeasurableSpace Z]

/-- 一般 pushforward DPI (核補題): `Measurable f` の pushforward で KL divergence は減る。
Mathlib に直接補題は **完全不在** (Phase 4-M0 在庫調査 B 節で確認済) のため自作。

戦略 (Jensen + Measure.rnDeriv_map):
- `Measure.rnDeriv_map` (`ConditionalExpectation/RadonNikodym.lean:83`) で
  `(μ.map f).rnDeriv (ν.map f) ∘ f =ᵐ[ν] ν⁻[μ.rnDeriv ν | comap f]`
- `klFun` の凸性 (`KullbackLeibler/KLFun.lean: convexOn_klFun`) + 条件付き Jensen で
  `klFun((dμ.map f / dν.map f) ∘ f) ≤ᵐ ν⁻[klFun(dμ/dν) | comap f]`
- 両辺を `ν` 積分し、`(ν.map f)` 上の積分に変換すれば
  `klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν`

予算: 50〜100 行。条件付き期待値の積分・絶対連続性の `f`-pushforward への伝播・klFun
の連続性 / 強可測性が plumbing の主体。-/
private theorem klDiv_map_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν := by
  -- 非絶対連続側: klDiv μ ν = ∞ なので自明
  by_cases hμν : μ ≪ ν
  swap
  · rw [klDiv_of_not_ac hμν]; exact le_top
  -- μ ≪ ν の主ケース: Jensen 経由
  have h_ac_map : μ.map f ≪ ν.map f := hμν.map hf
  have hMμmap : IsFiniteMeasure (μ.map f) := Measure.isFiniteMeasure_map μ f
  have hMνmap : IsFiniteMeasure (ν.map f) := Measure.isFiniteMeasure_map ν f
  -- 両 KL を lintegral klFun 形に
  rw [klDiv_eq_lintegral_klFun_of_ac h_ac_map, klDiv_eq_lintegral_klFun_of_ac hμν]
  -- ν.map f 上の積分を ν 上の積分に翻訳: ∫⁻ y, g y ∂(ν.map f) = ∫⁻ x, g (f x) ∂ν
  rw [show (∫⁻ y, ENNReal.ofReal
              (klFun ((μ.map f).rnDeriv (ν.map f) y).toReal) ∂(ν.map f))
        = ∫⁻ x, ENNReal.ofReal
              (klFun ((μ.map f).rnDeriv (ν.map f) (f x)).toReal) ∂ν from
      lintegral_map (by fun_prop) hf]
  -- 残る不等式:
  --   ∫⁻ x, ofReal (klFun ((μ.map f).rnDeriv (ν.map f) (f x)).toReal) ∂ν
  --     ≤ ∫⁻ x, ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν
  -- 戦略: pointwise ae 不等式 (Jensen) を作って lintegral monotonicity で持ち上げ
  refine lintegral_mono_ae ?_
  -- ae 不等式の構築:
  --   ofReal (klFun ((μ.map f).rnDeriv (ν.map f) (f x)).toReal)
  --     ≤ ofReal (klFun (μ.rnDeriv ν x).toReal)  ae[ν]
  --
  -- これは "pushforward の klFun(rnDeriv) は元の klFun(rnDeriv) の comap-σ 上 condExp ≤ 元"
  -- という DPI 核. 構成要素:
  -- 1) `toReal_rnDeriv_map`:
  --      `((μ.map f).rnDeriv (ν.map f) (f ·)).toReal =ᵐ[ν] ν[(μ.rnDeriv ν).toReal | comap f]`
  -- 2) `convexOn_klFun` + `ConvexOn.map_condExp_le` (Jensen):
  --      `klFun ∘ ν[(μ.rnDeriv ν).toReal | comap f] ≤ᵐ ν[klFun ∘ (μ.rnDeriv ν).toReal | comap f]`
  -- 3) `integral_condExp` (lintegral 版が必要、ENNReal.ofReal で持ち上げ):
  --      `∫⁻ x, ofReal (ν[g | F] x) ∂ν = ∫⁻ x, ofReal (g x) ∂ν` (g ≥ 0 のとき)
  -- ※ 3) を pointwise ae 不等式に組み込むには、(2) の Jensen を ae で適用したあと
  -- 全体を `lintegral_condExp_eq` 系の補題で書き換える必要があり、かなりの plumbing 量。
  -- Phase 4-α DPI 核の **残作業**: TODO. 詳細は handoff.md に集約。
  sorry

/-- Data processing inequality: deterministic post-processing decreases mutual information.
`Z = f(Y)` で `I(X; f(Y)) ≤ I(X; Y)`.

戦略: `klDiv_map_le` を `g := Prod.map id f : X × Y → X × Z` に適用し、
- `μ.map (Xs, f∘Yo) = (μ.map (Xs, Yo)).map (Prod.map id f)` (Map composition)
- `(μ.map Xs).prod (μ.map (f∘Yo)) = ((μ.map Xs).prod (μ.map Yo)).map (Prod.map id f)`
  (`Measure.map_prod_map`)

の 2 つの書き換えで `mutualInfo μ Xs (f∘Yo) = klDiv ((μ.map (Xs,Yo)).map g) (((μ.map Xs).prod (μ.map Yo)).map g)`
にし、`klDiv_map_le` を直接適用。 -/
theorem mutualInfo_le_of_postprocess
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo)
    {f : Y → Z} (hf : Measurable f) :
    mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo := by
  unfold mutualInfo
  have hpair : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  have hg : Measurable (Prod.map id f : X × Y → X × Z) := measurable_id.prodMap hf
  have _ : IsFiniteMeasure (μ.map Xs) := Measure.isFiniteMeasure_map μ Xs
  have _ : IsFiniteMeasure (μ.map Yo) := Measure.isFiniteMeasure_map μ Yo
  have _ : IsFiniteMeasure (μ.map (fun ω => (Xs ω, Yo ω))) :=
    Measure.isFiniteMeasure_map μ _
  -- joint distribution は Prod.map id f の pushforward
  have h_joint : μ.map (fun ω => (Xs ω, f (Yo ω)))
      = (μ.map (fun ω => (Xs ω, Yo ω))).map (Prod.map id f) := by
    rw [Measure.map_map hg hpair]
    rfl
  -- product distribution も Prod.map id f の pushforward
  have h_prod : (μ.map Xs).prod (μ.map (f ∘ Yo))
      = ((μ.map Xs).prod (μ.map Yo)).map (Prod.map id f) := by
    rw [show μ.map (f ∘ Yo) = (μ.map Yo).map f from (Measure.map_map hf hYo).symm,
        ← Measure.map_prod_map (μ.map Xs) (μ.map Yo) measurable_id hf,
        Measure.map_id]
  show klDiv (μ.map (fun ω => (Xs ω, f (Yo ω))))
      ((μ.map Xs).prod (μ.map (f ∘ Yo)))
    ≤ klDiv (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))
  rw [h_joint, h_prod]
  exact klDiv_map_le hg _ _

end InformationTheory.Shannon
