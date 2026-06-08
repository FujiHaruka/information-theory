import InformationTheory.Shannon.Han.D

/-!
# Han Phase D-1: subset average chain (skeleton)

Han Phase D ロードマップ ([`docs/han/han-phase-d-plan.md`](../../../docs/han/han-phase-d-plan.md))
の Phase B (D-1)。$H_k := (k \binom{n}{k})^{-1} \sum_{|S|=k} H(X_S)$ が
$k$ について非増加であることを示す。

## 主要定義・主定理

* `averageSubsetEntropy μ Xs k` ─ $H_k$。
* `subset_sum_step` ─ $k \cdot S_{k+1} \le (n-k) \cdot S_k$。`han_inequality_subset` を
  `|S| = k+1` で和を取って二重和 reindex する形。
* `subset_average_anti` ─ $H_{k+1} \le H_k$。`subset_sum_step` から正規化定数の代数操作で。
* `subset_average_chain` ─ $H_{k_2} \le H_{k_1}$ for $1 \le k_1 \le k_2 \le n$。
  `Nat.le_induction` で `subset_average_anti` を反復。

## 戦略 (plan より)

* 二重和 reindex: $\sum_{|S|=k+1} \sum_{i\in S} f(S \setminus \{i\}) = (n-k) \sum_{|T|=k} f(T)$
  は `sum_bij'` で `(S, i) ↦ (S.erase i, i)` ↔ `(T, i) ↦ (insert i T, i)` の双方向写像、
  + `sum_finset_product'` で二重和に展開、`mul_sum` + `card_sdiff` で `(n-k)` 倍に潰す。
  写経テンプレ: `Mathlib/Algebra/Polynomial/Derivative.lean:710-728`。
* 正規化定数: `(k+1) · binomial(n,k+1) = (n-k) · binomial(n,k)` (`Nat.choose_succ_right_eq` 等)。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

end InformationTheory.Shannon
