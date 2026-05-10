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

/-- Conditional mutual information via KL divergence (compProd form):
`I(X; Y | Z) := KL(P_Z ⊗ P_{(X,Y)|Z} ‖ P_Z ⊗ (P_{X|Z} × P_{Y|Z}))`.

第 1 引数は `compProd_map_condDistrib` で `μ.map (Zc, Xs, Yo)` と等しい。compProd 形を直接の
定義として採用する理由: Mathlib の chain rule (`klDiv_compProd_eq_add`) と直結し、γ-form Markov
仮定下で `condMutualInfo = 0` が `klDiv_self` で trivial に従う。

教科書的な積分形 `∫⁻ z, klDiv (κ_joint z) (κ_factored z) ∂(μ.map Z)` との同値性 (条件付き KL の
公式) は補題として将来追加可能 (Mathlib に直接対応する補題は不在 — 必要になったら自作)。 -/
noncomputable def condMutualInfo
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞ :=
  klDiv ((μ.map Zc) ⊗ₘ condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ)
        ((μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ)))

/-- Conditional mutual information is non-negative (signature 上自明、`klDiv` が `ℝ≥0∞` 値)。 -/
theorem condMutualInfo_nonneg
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) :
    0 ≤ condMutualInfo μ Xs Yo Zc := bot_le

/-- Markov chain `Xs → Zc → Yo` (γ-form, joint factorization): 結合分布が `Zc` を介して
`Xs` と `Yo` の条件付き分布の積に分解される。Mathlib `condIndepFun_iff_map_prod_eq_prod_
condDistrib_prod_condDistrib` (`Conditional.lean:817`) の RHS と同型。

β-form (condDistrib 等式形 + `prodMkRight`) は `[StandardBorelSpace Ω]` を経由する Mathlib
lemma を要するため (`Conditional.lean:867` の `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`
は `[StandardBorelSpace Ω]` 必須)、ここでは Ω への追加制約を避けて γ-form を採用。

両形式は標準 Borel 仮定下で同値 (Mathlib lemma 経由)。 -/
def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop :=
  μ.map (fun ω => (Zc ω, Xs ω, Yo ω))
    = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))

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

/-- Markov chain `Xs → Zc → Yo` (γ-form) ⇒ `I(X; Y | Z) = 0`.

γ-form 採用により直接的な証明: condMutualInfo の第1引数 `(μ.map Zc) ⊗ₘ condDistrib (Xs, Yo) Zc μ`
は `compProd_map_condDistrib` で `μ.map (Zc, Xs, Yo)` と一致し、γ-form Markov の RHS が第2引数
そのものなので、両者が等しく `klDiv_self` で 0。 -/
theorem condMutualInfo_eq_zero_of_markov
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    condMutualInfo μ Xs Yo Zc = 0 := by
  unfold condMutualInfo
  have h_pair : Measurable (fun ω => (Xs ω, Yo ω)) := hXs.prodMk hYo
  have h_num_eq : (μ.map Zc) ⊗ₘ condDistrib (fun ω => (Xs ω, Yo ω)) Zc μ
      = μ.map (fun ω => (Zc ω, Xs ω, Yo ω)) := compProd_map_condDistrib h_pair.aemeasurable
  rw [h_num_eq, hmarkov]
  exact klDiv_self _

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
