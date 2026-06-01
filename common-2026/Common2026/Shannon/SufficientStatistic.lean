import Mathlib.Probability.Kernel.CondDistrib
import Common2026.Meta.EntryPoint
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.DPI
import Common2026.Shannon.CondMutualInfo

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

end InformationTheory.Shannon
