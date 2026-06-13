import InformationTheory.Shannon.Han.D

/-!
# Han's inequality — subset average chain

The normalized average subset entropy `Hₖ := (k · C(n,k))⁻¹ · ∑_{|S|=k} H(X_S)` is
nonincreasing in `k`.

## Main statements

* `averageSubsetEntropy μ Xs k` — the normalized average `Hₖ`.
* `subset_sum_step` — `k · S_{k+1} ≤ (n − k) · S_k`, obtained by summing
  `han_inequality_subset` over `|S| = k + 1` and reindexing the double sum.
* `subset_average_anti` — `H_{k+1} ≤ Hₖ`.
* `subset_average_chain` — `H_{k₂} ≤ H_{k₁}` for `1 ≤ k₁ ≤ k₂ ≤ n`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

end InformationTheory.Shannon
