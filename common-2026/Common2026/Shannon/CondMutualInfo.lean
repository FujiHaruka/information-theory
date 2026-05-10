import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.DPI

/-!
# Conditional mutual information & Markov chains (Phase 4-δ-(b) skeleton)

Shannon ムーンショット ([`docs/shannon-moonshot-plan.md`](../../../docs/shannon-moonshot-plan.md))
の Phase 4-δ-(b): 条件付き相互情報量 `condMutualInfo` と Markov chain 述語
`IsMarkovChain` を定義し、chain rule と Markov ⇒ condMI = 0、その合成として
`mutualInfo_le_of_markov` (`I(X; Y) ≤ I(Z; Y)` under `X → Z → Y`) を整備する。

設計判断 / Mathlib 在庫は [`docs/shannon-condmi-inventory.md`](../../../docs/shannon-condmi-inventory.md)
を参照。Markov 定式化は **β 形式** (condDistrib 等式形) を採用、Mathlib
`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` (`Conditional.lean:867`) と直結する。

主応用: `Common2026/Shannon/Converse.lean` 末尾の `shannon_converse_single_shot_markov_encoder`
(Markov chain `Msg → encoder ∘ Msg → Yo` ⇒ `I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)` で encoder を
含む single-shot converse を導く)。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]
variable {Z : Type*} [MeasurableSpace Z]

/-- Conditional mutual information via KL divergence:
`I(X; Y | Z) := ∫ KL(P_{(X,Y) | Z=z} ‖ P_{X | Z=z} ⊗ P_{Y | Z=z}) dP_Z(z)`. -/
noncomputable def condMutualInfo
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞ :=
  ∫⁻ z, klDiv (condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ z)
              ((condDistrib Xs Zc μ z).prod (condDistrib Yo Zc μ z))
        ∂(μ.map Zc)

/-- Conditional mutual information is non-negative (signature 上自明、`klDiv` が `ℝ≥0∞` 値)。 -/
theorem condMutualInfo_nonneg
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) :
    0 ≤ condMutualInfo μ Xs Yo Zc := bot_le

/-- Markov chain `Xs → Zc → Yo` (β-form, condDistrib 等式形): `Yo` の (Zc, Xs) 条件付き分布が
`Zc` のみに依存する。Mathlib `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`
(`Conditional.lean:867`) の RHS をそのまま定義として採用。 -/
def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop :=
  condDistrib Yo (fun ω => (Zc ω, Xs ω)) μ
    =ᵐ[μ.map (fun ω => (Zc ω, Xs ω))]
    (condDistrib Yo Zc μ).prodMkRight X

/-- Chain rule: `I((Z, X); Y) = I(Z; Y) + I(X; Y | Z)`.

戦略 (`docs/shannon-condmi-inventory.md` §chain rule plumbing):
1. `μ.map ((Zc, Xs), Yo)` を 3 重 compProd `μ.map Zc ⊗ₘ condDistrib Xs Zc μ ⊗ₘ
   condDistrib Yo (Zc, Xs) μ` に分解 (`compProd_map_condDistrib` を 2 回 + `compProd_assoc`)
2. RHS の積測度 `(μ.map (Zc, Xs)).prod (μ.map Yo)` も同様に compProd 形へ
3. `klDiv_compProd_eq_add` を 1 段適用し `I(Z;Y)` と condMI 部分に分離
4. condMI 部分を `klDiv` の積分形 (`condMutualInfo` の定義) に書き換え

最大の plumbing 障壁は `Kernel.compProd_assoc` (`map prodAssoc.symm` 形) を Measure 側に
下ろす書き換え。推定 40〜60 行。 -/
theorem mutualInfo_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
    mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo
      = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc := by
  sorry

/-- Markov chain `Xs → Zc → Yo` ⇒ `I(X; Y | Z) = 0`.

戦略: β 形式の Markov 等式で `condDistrib Yo (Zc, Xs) μ z =ᵐ condDistrib Yo Zc μ z` を取り出し、
`condMutualInfo` の被積分関数 `klDiv ((condDistrib (Xs, Yo) Zc μ) z) ((condDistrib Xs Zc μ z).prod
(condDistrib Yo Zc μ z))` が ae-zero になることを示す (kernel 共有 ⇒ klDiv = 0、または
`klDiv_compProd_left` 経由)。推定 20〜30 行。 -/
theorem condMutualInfo_eq_zero_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    condMutualInfo μ Xs Yo Zc = 0 := by
  sorry

/-- Markov chain `Xs → Zc → Yo` ⇒ `I(Xs; Yo) ≤ I(Zc; Yo)`.

戦略 (chain rule + condMI = 0 + DPI for `Prod.snd : Z × X → X` の合成):
1. DPI for `Prod.snd`: `I(Yo; Xs) ≤ I(Yo; (Zc, Xs))`、`mutualInfo_comm` で両端の対称化により
   `I(Xs; Yo) ≤ I((Zc, Xs); Yo)`
2. `mutualInfo_chain_rule` で `I((Zc, Xs); Yo) = I(Zc; Yo) + I(Xs; Yo | Zc)`
3. `condMutualInfo_eq_zero_of_markov` で `I(Xs; Yo | Zc) = 0`
4. 1+2+3 を合成

主応用: `shannon_converse_single_shot_markov_encoder` (Converse.lean 末尾)。 -/
theorem mutualInfo_le_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo := by
  have h_pair_meas : Measurable (fun ω => (Zc ω, Xs ω)) := hZc.prodMk hXs
  -- Step 1: DPI on second arg with f := Prod.snd, applied to Yo as first arg
  have h_snd_eq : (Prod.snd : Z × X → X) ∘ (fun ω => (Zc ω, Xs ω)) = Xs := rfl
  have h_dpi_yo :
      mutualInfo μ Yo (Prod.snd ∘ (fun ω => (Zc ω, Xs ω))) ≤
        mutualInfo μ Yo (fun ω => (Zc ω, Xs ω)) :=
    mutualInfo_le_of_postprocess μ Yo (fun ω => (Zc ω, Xs ω)) hYo h_pair_meas measurable_snd
  rw [h_snd_eq] at h_dpi_yo
  -- DPI: I(Yo; Xs) ≤ I(Yo; (Zc, Xs))
  -- Symmetrize via mutualInfo_comm: I(Xs; Yo) ≤ I((Zc, Xs); Yo)
  have h_dpi :
      mutualInfo μ Xs Yo ≤ mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo := by
    rw [mutualInfo_comm μ Xs Yo hXs hYo,
        mutualInfo_comm μ (fun ω => (Zc ω, Xs ω)) Yo h_pair_meas hYo]
    exact h_dpi_yo
  -- Step 2: chain rule I((Zc, Xs); Yo) = I(Zc; Yo) + condMutualInfo Xs Yo Zc
  have h_chain :
      mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo
        = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc :=
    mutualInfo_chain_rule μ Xs Yo Zc hXs hYo hZc
  -- Step 3: Markov ⇒ condMI = 0
  have h_zero : condMutualInfo μ Xs Yo Zc = 0 :=
    condMutualInfo_eq_zero_of_markov μ Xs Zc Yo hXs hZc hYo hmarkov
  -- Compose
  rw [h_chain, h_zero, add_zero] at h_dpi
  exact h_dpi

end InformationTheory.Shannon
