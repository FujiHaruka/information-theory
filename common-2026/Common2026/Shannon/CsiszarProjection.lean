import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact

/-!
# Csiszár I-projection / Pythagorean inequality

Common2026 E-6 ムーンショット ([`docs/shannon/csiszar-projection-plan.md`])。

有限アルファベット `α` 上の確率 pmf `Q : α → ℝ` (full support) と凸閉集合
`K ⊆ stdSimplex ℝ α` について

- **存在**: `∃ Q* ∈ K, ∀ P ∈ K, klDivPmf Q* Q ≤ klDivPmf P Q`
- **一意性**: 最小化元は一意
- **Pythagorean inequality** (Cover-Thomas 11.6.1):
  `klDivPmf P Q ≥ klDivPmf P Q* + klDivPmf Q* Q` for `P ∈ K`

## 主定理

* `klDivPmf P Q := ∑ a, Q a * klFun (P a / Q a)` (Real-valued, finite-alphabet pmf 形)
* `csiszar_projection_exists` — 存在 (extreme value theorem + 連続性)
* `csiszar_projection_unique` — 一意性 (strict convexity)
* `csiszar_pythagoras_inequality` — Pythagorean inequality (1 次条件)

## 戦略 (Approach)

1. **Phase A**: `klDivPmf` 定義 + 連続性 (`klFun` 連続 + Q full support) +
   strict convexity (per-coordinate `strictConvexOn_klFun`)
2. **Phase B**: `IsCompact.exists_isMinOn` 経由で存在
3. **Phase C**: strict convexity + mid-point の対偶論法で一意性
4. **Phase D**: 代数恒等式 `klDivPmf P Q = klDivPmf P Q* + ∑ P(a) log(Q*/Q)` +
   1 次条件 `∑ (P - Q*) log(Q*/Q) ≥ 0` を `t ↦ klDivPmf ((1-t)Q* + tP) Q` の
   右微分 `≥ 0` で導出
-/

namespace InformationTheory.Shannon.CsiszarProjection

open Set Real InformationTheory
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Phase A — `klDivPmf` 定義 + 連続性 + 厳密凸性 -/

/-- **Real-valued finite-alphabet KL divergence** as a pmf functional:
`klDivPmf P Q := ∑ a, Q a * klFun (P a / Q a)` where
`klFun x = x * log x + 1 - x` (Mathlib `InformationTheory.klFun`).

Equivalent to `(klDiv P Q).toReal` under support hypotheses (bridge in `Sanov.lean`),
but we work Real-only here to leverage `strictConvexOn_klFun` + finite-sum API directly. -/
noncomputable def klDivPmf (P Q : α → ℝ) : ℝ :=
  ∑ a : α, Q a * klFun (P a / Q a)

/-- `klDivPmf` is non-negative on the simplex when Q is a pmf (full support not required:
each summand is `Q a * klFun (P a / Q a) ≥ 0` whenever `Q a ≥ 0`, since `klFun` ≥ 0 on `[0, ∞)`
and `P a / Q a ≥ 0` follows from `P a ≥ 0` and `Q a ≥ 0`). -/
lemma klDivPmf_nonneg (P Q : α → ℝ)
    (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) :
    0 ≤ klDivPmf P Q := by
  sorry

/-- `klFun` is continuous on `[0, ∞)` (Mathlib `continuous_klFun`). The composition
`fun P => klFun (P a / Q a)` is continuous in P when `Q a > 0`. -/
lemma continuous_klDivPmf_left (Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) :
    Continuous (fun P : α → ℝ => klDivPmf P Q) := by
  sorry

/-- `klDivPmf · Q` is strictly convex on `stdSimplex ℝ α` (full support Q + Π ⊆ simplex).

Per-coordinate: `klFun` is strictly convex on `[0, ∞)` (`strictConvexOn_klFun`).
The map `P ↦ P a / Q a` is affine (when `Q a > 0` is fixed), and `Q a * (·)` preserves
strict convexity. Sum of strictly convex (in at least one coordinate where `P ≠ P'`)
gives strict convexity of the sum.

(But care: if `P = P'` they agree in every coordinate; if `P ≠ P'` then there is at least
one coordinate `a` where `P a ≠ P' a`, and at that coordinate `klFun` strict convexity fires.) -/
lemma klDivPmf_strictConvexOn_left (Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) :
    StrictConvexOn ℝ (stdSimplex ℝ α) (fun P : α → ℝ => klDivPmf P Q) := by
  sorry

/-! ## Phase B — 存在 (extreme value theorem) -/

/-- 任意の閉集合 `K ⊆ stdSimplex ℝ α` はコンパクト
(`isCompact_stdSimplex` + `IsCompact.of_isClosed_subset`)。 -/
lemma isCompact_of_subset_stdSimplex {K : Set (α → ℝ)}
    (hK_closed : IsClosed K) (hK_sub : K ⊆ stdSimplex ℝ α) :
    IsCompact K := by
  sorry

/-- **存在** (Cover-Thomas 11.6.1 a): 閉凸非空 `K ⊆ stdSimplex ℝ α` と full-support
reference Q について `klDivPmf · Q` を最小化する `Q* ∈ K` が存在する。 -/
theorem csiszar_projection_exists {K : Set (α → ℝ)} {Q : α → ℝ}
    (hK_closed : IsClosed K)
    (hK_sub : K ⊆ stdSimplex ℝ α)
    (hK_ne : K.Nonempty)
    (hQ_pos : ∀ a, 0 < Q a) :
    ∃ Qstar ∈ K, IsMinOn (fun P => klDivPmf P Q) K Qstar := by
  sorry

/-! ## Phase C — 一意性 (strict convexity) -/

/-- **一意性** (Cover-Thomas 11.6.1 b): 凸閉非空 `K ⊆ stdSimplex ℝ α` 上の最小化元は一意。 -/
theorem csiszar_projection_unique {K : Set (α → ℝ)} {Q : α → ℝ}
    (hK_conv : Convex ℝ K)
    (hK_sub : K ⊆ stdSimplex ℝ α)
    (hQ_pos : ∀ a, 0 < Q a)
    {Qstar Qstar' : α → ℝ}
    (hQs : Qstar ∈ K) (hQs' : Qstar' ∈ K)
    (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar)
    (hmin' : IsMinOn (fun P => klDivPmf P Q) K Qstar') :
    Qstar = Qstar' := by
  sorry

/-! ## Phase D — Pythagorean inequality -/

/-- **代数恒等式**: full support `P, Q*, Q` (簡単のため: 全 atom で `P a > 0`,
`Q* a > 0`, `Q a > 0`) のもとで
`klDivPmf P Q = klDivPmf P Q* + ∑ a, P a * (log (Q* a) - log (Q a))`。 -/
lemma klDivPmf_decomp_via_intermediate
    {P Qstar Q : α → ℝ}
    (hP_sum : ∑ a, P a = 1)
    (hQs_sum : ∑ a, Qstar a = 1)
    (hQ_sum : ∑ a, Q a = 1)
    (hP_pos : ∀ a, 0 < P a)
    (hQs_pos : ∀ a, 0 < Qstar a)
    (hQ_pos : ∀ a, 0 < Q a) :
    klDivPmf P Q
      = klDivPmf P Qstar + ∑ a : α, P a * (Real.log (Qstar a) - Real.log (Q a)) := by
  sorry

/-- **`klDivPmf Q* Q` の展開** (Q*, Q full support):
`klDivPmf Q* Q = ∑ a, Q* a * (log (Q* a) - log (Q a))` (= 標準形 `∑ Q* log(Q*/Q)`)。 -/
lemma klDivPmf_self_expand
    {Qstar Q : α → ℝ}
    (hQs_sum : ∑ a, Qstar a = 1)
    (hQ_sum : ∑ a, Q a = 1)
    (hQs_pos : ∀ a, 0 < Qstar a)
    (hQ_pos : ∀ a, 0 < Q a) :
    klDivPmf Qstar Q
      = ∑ a : α, Qstar a * (Real.log (Qstar a) - Real.log (Q a)) := by
  sorry

/-- **1 次条件**: `Q*` が最小化元なら、任意 `P ∈ K` で
`∑ a, (P a - Q* a) * (log (Q* a) - log (Q a)) ≥ 0`。

戦略: `φ(t) := klDivPmf ((1-t)Q* + tP) Q` は `t = 0` で右微分が
`∑ a, (P a - Q* a) * (log (Q* a) - log (Q a))` であり、最小化条件 `φ(0) ≤ φ(t)`
(for `t ∈ [0,1]`) から右微分 ≥ 0。 -/
lemma csiszar_first_order_condition
    {K : Set (α → ℝ)} {Q : α → ℝ}
    (hK_conv : Convex ℝ K)
    (hK_sub : K ⊆ stdSimplex ℝ α)
    (hQ_pos : ∀ a, 0 < Q a)
    {Qstar : α → ℝ} (hQs : Qstar ∈ K) (hQs_pos : ∀ a, 0 < Qstar a)
    (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar)
    {P : α → ℝ} (hP : P ∈ K) :
    0 ≤ ∑ a : α, (P a - Qstar a) * (Real.log (Qstar a) - Real.log (Q a)) := by
  sorry

/-- **Pythagorean inequality** (Cover-Thomas 11.6.1 c):
最小化元 `Q*` と `P ∈ K` について
`klDivPmf P Q ≥ klDivPmf P Q* + klDivPmf Q* Q`。

戦略: 代数恒等式 `klDivPmf P Q = klDivPmf P Q* + ∑ P a · log(Q*/Q)` +
`klDivPmf Q* Q = ∑ Q* a · log(Q*/Q)` + 1 次条件
`∑ (P - Q*) log(Q*/Q) ≥ 0` の 3 つを合成。 -/
theorem csiszar_pythagoras_inequality
    {K : Set (α → ℝ)} {Q : α → ℝ}
    (hK_conv : Convex ℝ K)
    (hK_sub : K ⊆ stdSimplex ℝ α)
    (hQ_pos : ∀ a, 0 < Q a)
    {Qstar : α → ℝ} (hQs : Qstar ∈ K) (hQs_pos : ∀ a, 0 < Qstar a)
    (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar)
    {P : α → ℝ} (hP : P ∈ K) (hP_pos : ∀ a, 0 < P a) :
    klDivPmf P Q ≥ klDivPmf P Qstar + klDivPmf Qstar Q := by
  sorry

end InformationTheory.Shannon.CsiszarProjection
