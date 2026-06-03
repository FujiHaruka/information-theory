import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Conditional
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.CondMutualInfo

/-!
# Sufficient statistics and mutual information (Cover-Thomas 2.9)

`T` が `θ` に対し sufficient (= chain `X → T(X) → θ` が Markov) ⟹ `I(θ; X) = I(θ; T(X))`。

`IsSufficientStatistic` を教科書の Neyman-Fisher 因子分解形で直接 def 化せず、
`mutualInfo_le_of_markov` の結論形に直結する **markov-form** (`IsMarkovChain μ Xs (f∘Xs) θ`)
で定義する。これにより主定理は `mutualInfo_le_of_postprocess` (≥ 方向) と
`mutualInfo_le_of_markov` + `mutualInfo_comm` (≤ 方向) の `le_antisymm` で閉じる。

在庫: [`docs/shannon/ch2-gaps-inventory.md`](../../../docs/shannon/ch2-gaps-inventory.md) ブロック A。
計画: [`docs/shannon/ch2-gaps-plan.md`](../../../docs/shannon/ch2-gaps-plan.md) WI-1。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {Θ : Type*} [MeasurableSpace Θ]
variable {X : Type*} [MeasurableSpace X]
variable {T' : Type*} [MeasurableSpace T']

/-- 充足統計量 (markov-form): chain `Xs → f∘Xs → θ` が Markov chain。
すなわち statistic `T(X) = f(X)` が `Xs` と `θ` を分離する (`Xs ⊥ θ | T(X)`)。

教科書の Neyman-Fisher 因子分解形 (条件付き分布が `θ` に非依存) との同値は
将来の別補題 (Mathlib 壁、在庫 A-1 で sufficiency 定義 0 件確認)。
@audit:ok -/
def IsSufficientStatistic
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) (f : X → T') : Prop :=
  IsMarkovChain μ Xs (fun ω => f (Xs ω)) θ

/-- Cover-Thomas 2.9: `T` が `θ` に対し sufficient ⟹ `I(θ; X) = I(θ; T(X))`.

`IsSufficientStatistic` は markov-form の **構造前提** (precondition) であって、
結論 `I(θ;X) = I(θ;T(X))` そのものではない (markov 等式 ≠ 相互情報量等式)。
@audit:ok -/
@[entry_point]
theorem mutualInfo_eq_of_sufficient
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) {f : X → T'}
    (hθ : Measurable θ) (hXs : Measurable Xs) (hf : Measurable f)
    (hsuff : IsSufficientStatistic μ θ Xs f) :
    mutualInfo μ θ Xs = mutualInfo μ θ (fun ω => f (Xs ω)) := by
  have hfXs : Measurable (fun ω => f (Xs ω)) := hf.comp hXs
  -- (≥ 方向) T(X) = f∘Xs は θ の相手 X の決定論的後処理。
  have h_ge : mutualInfo μ θ (fun ω => f (Xs ω)) ≤ mutualInfo μ θ Xs :=
    mutualInfo_le_of_postprocess μ θ Xs hθ hXs hf
  -- (≤ 方向) sufficiency の markov chain `Xs → f∘Xs → θ` から DPI、
  -- `mutualInfo_comm` で両辺の引数を入れ替えて (θ, ·) 形に揃える。
  have h_markov : mutualInfo μ Xs θ ≤ mutualInfo μ (fun ω => f (Xs ω)) θ :=
    mutualInfo_le_of_markov μ Xs (fun ω => f (Xs ω)) θ hXs hfXs hθ hsuff
  have h_le : mutualInfo μ θ Xs ≤ mutualInfo μ θ (fun ω => f (Xs ω)) := by
    rw [mutualInfo_comm μ θ Xs hθ hXs, mutualInfo_comm μ θ (fun ω => f (Xs ω)) hθ hfXs]
    exact h_markov
  exact le_antisymm h_le h_ge

/-! ## Neyman-Fisher 因子分解形との同値 (WI-1.2)

教科書 Cover-Thomas 2.9 の充足統計量は **因子分解形** で導入される:
`p(x ∣ θ) = g(T(x), θ) · h(x)`、すなわち「`T(X)` を与えたとき `X` の条件付き分布が
`θ` に依存しない」。測度論的には `condDistrib Xs (T, θ) = (condDistrib Xs T).prodMkRight`
(`θ`-成分を足しても `X` の条件付き分布が変わらない) と書ける。

markov-form (`IsSufficientStatistic`) との同値は Mathlib の条件付き独立性 ⟺ 各分解形の
補題 (`condIndepFun_iff_*`, `Conditional.lean`) を経由して閉じる。直感的には両者とも
「`X ⊥ θ ∣ T(X)`」という同一の条件付き独立性の別表現。 -/

/-- 充足統計量 (因子分解形 / Neyman-Fisher): `T(X)` を与えたとき `X` の条件付き分布が
`θ` に依存しない。`condDistrib Xs (T(X), θ) =ᵃᵉ (condDistrib Xs T(X)).prodMkRight Θ`。

これは教科書の `p(x ∣ θ) = g(T(x), θ) h(x)` の測度論的エンコード
(条件付き分布の `θ`-非依存性、在庫 §A-1)。
@audit:ok -/
def IsSufficientStatisticFactorized
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) (f : X → T') : Prop :=
  condDistrib Xs (fun ω => (f (Xs ω), θ ω)) μ
    =ᵐ[μ.map (fun ω => (f (Xs ω), θ ω))]
      (condDistrib Xs (fun ω => f (Xs ω)) μ).prodMkRight Θ

/-- markov-form ⟺ 因子分解形 (Neyman-Fisher) の同値。両者とも `X ⊥ θ ∣ T(X)` を表す。

戦略 (Mathlib 条件付き独立性経由):
- (A) `IsSufficientStatistic` (γ-form joint factorization) ⟺ `Xs ⟂ᵢ[f∘Xs] θ`
  via `condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib` + `compProd_eq_comp_prod`。
- (B) `Xs ⟂ᵢ[f∘Xs] θ` ⟺ `θ ⟂ᵢ[f∘Xs] Xs` via `CondIndepFun.symm`。
- (C) `θ ⟂ᵢ[f∘Xs] Xs` ⟺ 因子分解形 via `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`。
@audit:ok -/
theorem isSufficient_iff_factorized
    (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Θ] [Nonempty Θ]
    (θ : Ω → Θ) (Xs : Ω → X) {f : X → T'}
    (hθ : Measurable θ) (hXs : Measurable Xs) (hf : Measurable f) :
    IsSufficientStatistic μ θ Xs f ↔ IsSufficientStatisticFactorized μ θ Xs f := by
  have hfXs : Measurable (fun ω => f (Xs ω)) := hf.comp hXs
  -- (A) markov γ-form ⟺ condIndepFun `Xs ⟂ᵢ[f∘Xs] θ`
  have hA : IsSufficientStatistic μ θ Xs f
      ↔ Xs ⟂ᵢ[fun ω => f (Xs ω), hfXs; μ] θ := by
    unfold IsSufficientStatistic IsMarkovChain
    rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hXs hθ hfXs,
        Measure.compProd_eq_comp_prod]
  -- (B) condIndepFun の対称性
  have hB : (Xs ⟂ᵢ[fun ω => f (Xs ω), hfXs; μ] θ)
      ↔ (θ ⟂ᵢ[fun ω => f (Xs ω), hfXs; μ] Xs) :=
    ⟨CondIndepFun.symm, CondIndepFun.symm⟩
  -- (C) condIndepFun `θ ⟂ᵢ[f∘Xs] Xs` ⟺ 因子分解形 (β-form)
  have hC : (θ ⟂ᵢ[fun ω => f (Xs ω), hfXs; μ] Xs)
      ↔ IsSufficientStatisticFactorized μ θ Xs f := by
    unfold IsSufficientStatisticFactorized
    rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hXs hθ hfXs]
  exact hA.trans (hB.trans hC)

end InformationTheory.Shannon
