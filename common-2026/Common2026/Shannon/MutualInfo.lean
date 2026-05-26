import Common2026.Meta.EntryPoint
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Mutual information via KL divergence (Phase 4-α skeleton)

Shannon ムーンショット ([`docs/shannon/shannon-moonshot-plan.md`](../../../docs/shannon/shannon-moonshot-plan.md))
の Phase 4-α: Mathlib の `klDiv` を主軸に、相互情報量 `mutualInfo`、その基本性質
(`mutualInfo_nonneg`, `mutualInfo_comm`, `mutualInfo_eq_zero_iff_indep`) を整備する。

Phase 4-M0 の在庫調査結果 ([`docs/shannon/shannon-mathlib-inventory.md`](../../../docs/shannon/shannon-mathlib-inventory.md))
に基づく skeleton。実証は sorry-driven で順次充填する。

主要素材:
* `klDiv (μ ν : Measure α) : ℝ≥0∞` — `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57`
* `klDiv_compProd_left` — `KullbackLeibler/ChainRule.lean:182` (`@[simp]`)
* `klDiv_compProd_eq_add` — `KullbackLeibler/ChainRule.lean:204`
* `klDiv_eq_zero_iff` — `KullbackLeibler/Basic.lean:377`
* `indepFun_iff_map_prod_eq_prod_map_map` — `Probability/Independence/Basic.lean:701`
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]

/-- Mutual information via KL divergence:
`I(X; Y) := KL(P_{X,Y} ‖ P_X ⊗ P_Y)`. -/
noncomputable def mutualInfo
    (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ :=
  klDiv (μ.map (fun ω => (Xs ω, Yo ω)))
        ((μ.map Xs).prod (μ.map Yo))

/-- 相互情報量は非負。`klDiv` が `ℝ≥0∞` 値なので signature 上自明。 -/
@[entry_point]
theorem mutualInfo_nonneg (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) :
    0 ≤ mutualInfo μ Xs Yo := bot_le

/-- KL の MeasurableEquiv 不変性: 測度同型での pushforward は KL 値を保つ。
Mathlib 不在 (Phase 4-M0 在庫調査確認済) のため自作。

戦略: `MeasurableEmbedding.rnDeriv_map` (`Decomposition/RadonNikodym.lean:516`) で
`(μ.map e).rnDeriv (ν.map e) ∘ e =ᵐ[ν] μ.rnDeriv ν` を得て、`lintegral_map_equiv` で
`∫⁻ ∂(ν.map e)` を `∫⁻ ∂ν` に翻訳、`klDiv_eq_lintegral_klFun_of_ac` で結ぶ。
非 `≪` 側は `e.symm` で逆変換して矛盾。 -/
theorem klDiv_map_measurableEquiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  have he : MeasurableEmbedding e := e.measurableEmbedding
  have he_sym : MeasurableEmbedding e.symm := e.symm.measurableEmbedding
  by_cases hμν : μ ≪ ν
  · have hμν_map : μ.map e ≪ ν.map e := he.absolutelyContinuous_map hμν
    rw [klDiv_eq_lintegral_klFun_of_ac hμν_map, klDiv_eq_lintegral_klFun_of_ac hμν,
        lintegral_map_equiv]
    refine lintegral_congr_ae ?_
    filter_upwards [he.rnDeriv_map μ ν] with x hx
    rw [hx]
  · have hμν_map : ¬ μ.map e ≪ ν.map e := by
      intro h
      apply hμν
      have h₁ : (μ.map e).map e.symm ≪ (ν.map e).map e.symm :=
        he_sym.absolutelyContinuous_map h
      simpa using h₁
    rw [klDiv_of_not_ac hμν, klDiv_of_not_ac hμν_map]

/-- KL の積測度補題 (probability measure 版): `klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂`。
DPI plumbing の起点。

戦略: `prod_swap` + `klDiv_map_measurableEquiv` で `klDiv (ν₁.prod μ) (ν₂.prod μ)` に
変形し、`compProd_const` で `klDiv (ν₁ ⊗ₘ Kernel.const _ μ) (ν₂ ⊗ₘ Kernel.const _ μ)` に
翻訳、`klDiv_compProd_left` を適用。`Kernel.const _ μ` が Markov である必要があるため
`[IsProbabilityMeasure μ]` を要求。一般 `IsFiniteMeasure` 形は将来課題。 -/
theorem klDiv_prod_const_left
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (ν₁ ν₂ : Measure β) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    klDiv (μ.prod ν₁) (μ.prod ν₂) = klDiv ν₁ ν₂ := by
  let e : β × α ≃ᵐ α × β := MeasurableEquiv.prodComm
  have h₁ : (ν₁.prod μ).map e = μ.prod ν₁ := Measure.prod_swap
  have h₂ : (ν₂.prod μ).map e = μ.prod ν₂ := Measure.prod_swap
  rw [← h₁, ← h₂, klDiv_map_measurableEquiv e,
      ← Measure.compProd_const, ← Measure.compProd_const, klDiv_compProd_left]

/-- 相互情報量の対称性: `I(X; Y) = I(Y; X)`。
`MeasurableEquiv.prodComm` 経由で `klDiv_map_measurableEquiv` を適用。 -/
@[entry_point]
theorem mutualInfo_comm
    (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = mutualInfo μ Yo Xs := by
  unfold mutualInfo
  let e : Y × X ≃ᵐ X × Y := MeasurableEquiv.prodComm
  have h₁ : (μ.map (fun ω => (Yo ω, Xs ω))).map e = μ.map (fun ω => (Xs ω, Yo ω)) := by
    rw [Measure.map_map e.measurable (hYo.prodMk hXs)]
    rfl
  have h₂ : ((μ.map Yo).prod (μ.map Xs)).map e = (μ.map Xs).prod (μ.map Yo) :=
    Measure.prod_swap
  rw [← h₁, ← h₂, klDiv_map_measurableEquiv e]

/-- 相互情報量がゼロ ↔ 独立。
`indepFun_iff_map_prod_eq_prod_map_map` (`Independence/Basic.lean:701`) と
`klDiv_eq_zero_iff` (`KullbackLeibler/Basic.lean:377`) の合成で示す。 -/
@[entry_point]
theorem mutualInfo_eq_zero_iff_indep
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo = 0 ↔ IndepFun Xs Yo μ := by
  have hpair : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  have : IsProbabilityMeasure (μ.map (fun ω => (Xs ω, Yo ω))) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  have : IsProbabilityMeasure (μ.map Xs) := Measure.isProbabilityMeasure_map hXs.aemeasurable
  have : IsProbabilityMeasure (μ.map Yo) := Measure.isProbabilityMeasure_map hYo.aemeasurable
  rw [mutualInfo, klDiv_eq_zero_iff,
      ← indepFun_iff_map_prod_eq_prod_map_map hXs.aemeasurable hYo.aemeasurable]

/-- 有限アルファベット上で結合分布が周辺積に絶対連続。Fintype の任意の集合は
singleton の有限和に分解でき、product 測度の atom が 0 ⇒ 周辺の atom が 0 ⇒
joint の atom も 0 (周辺射影での monotonicity)。 -/
private lemma map_pair_absolutelyContinuous_prod_marginals
    [Fintype X] [MeasurableSingletonClass X]
    [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    μ.map (fun ω => (Xs ω, Yo ω)) ≪ (μ.map Xs).prod (μ.map Yo) := by
  classical
  refine Measure.AbsolutelyContinuous.mk fun s _ hs_zero => ?_
  set sf : Finset (X × Y) := Finset.univ.filter (· ∈ s)
  have hs_decomp : s = ⋃ p ∈ sf, ({p} : Set (X × Y)) := by
    ext p; simp [sf]
  have h_pwd : Set.PairwiseDisjoint (↑sf) (fun p : X × Y => ({p} : Set (X × Y))) :=
    fun a _ b _ hne => Set.disjoint_singleton.mpr hne
  have h_meas : ∀ p ∈ sf, MeasurableSet ({p} : Set (X × Y)) :=
    fun p _ => measurableSet_singleton p
  have h_prod_sum : ∑ p ∈ sf, ((μ.map Xs).prod (μ.map Yo)) {p} = 0 := by
    rw [← measure_biUnion_finset h_pwd h_meas, ← hs_decomp]; exact hs_zero
  have h_prod_each : ∀ p ∈ sf, ((μ.map Xs).prod (μ.map Yo)) {p} = 0 := fun p hp =>
    le_antisymm (h_prod_sum ▸ Finset.single_le_sum
      (f := fun q => ((μ.map Xs).prod (μ.map Yo)) {q})
      (fun _ _ => bot_le) hp) bot_le
  rw [hs_decomp, measure_biUnion_finset h_pwd h_meas]
  refine Finset.sum_eq_zero fun ⟨x, y⟩ hp => ?_
  have h_pt := h_prod_each (x, y) hp
  rw [show ({(x, y)} : Set (X × Y)) = {x} ×ˢ {y} from
    Set.singleton_prod_singleton.symm, Measure.prod_prod] at h_pt
  rw [Measure.map_apply (hXs.prodMk hYo) (measurableSet_singleton _)]
  rcases mul_eq_zero.mp h_pt with hX | hY
  · refine le_antisymm ?_ bot_le
    calc μ ((fun ω => (Xs ω, Yo ω)) ⁻¹' {(x, y)})
        ≤ μ (Xs ⁻¹' {x}) := by
          refine measure_mono fun ω hω => ?_
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hω
          exact hω.1
      _ = (μ.map Xs) {x} := (Measure.map_apply hXs (measurableSet_singleton _)).symm
      _ = 0 := hX
  · refine le_antisymm ?_ bot_le
    calc μ ((fun ω => (Xs ω, Yo ω)) ⁻¹' {(x, y)})
        ≤ μ (Yo ⁻¹' {y}) := by
          refine measure_mono fun ω hω => ?_
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hω
          exact hω.2
      _ = (μ.map Yo) {y} := (Measure.map_apply hYo (measurableSet_singleton _)).symm
      _ = 0 := hY

/-- 有限アルファベットの結合分布上で `llr` は可積分。Fintype 上の確率測度では
`lintegral_fintype` で有限和に分解され、各項が `≤ ENNReal.coe * (probability)` で有限。 -/
private lemma integrable_llr_map_pair_prod_marginals
    [Fintype X] [MeasurableSingletonClass X]
    [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    Integrable
      (llr (μ.map (fun ω => (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo)))
      (μ.map (fun ω => (Xs ω, Yo ω))) := by
  haveI : IsProbabilityMeasure (μ.map (fun ω => (Xs ω, Yo ω))) :=
    Measure.isProbabilityMeasure_map (hXs.prodMk hYo).aemeasurable
  refine ⟨(measurable_llr _ _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
  exact ENNReal.sum_lt_top.mpr fun _ _ =>
    ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)

/-- 有限アルファベットでは相互情報量は有限。AC + integrable から `klDiv_ne_top`。
Phase A の `condMutualInfo_eq_condEntropy_sub_condEntropy` で chain rule の
`ENNReal.toReal_add` を有効化するために必要。 -/
@[entry_point]
theorem mutualInfo_ne_top
    [Fintype X] [MeasurableSingletonClass X]
    [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo ≠ ∞ :=
  klDiv_ne_top
    (map_pair_absolutelyContinuous_prod_marginals μ Xs Yo hXs hYo)
    (integrable_llr_map_pair_prod_marginals μ Xs Yo hXs hYo)

end InformationTheory.Shannon
