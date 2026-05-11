import Common2026.Shannon.LoomisWhitney

/-!
# Brascamp–Lieb 不等式 (組合せ形) + Hypercube product projection bound

Han Phase D の `shearer_inequality` を engine として、任意の cover ファミリ
`S : ι → Finset (Fin n)` (各 `j : Fin n` を `k` 回以上覆う) に対する一般化
Loomis–Whitney 形:
$$|A|^k \le \prod_{i : \iota} |\pi_{S_i}(A)|.$$

`Common2026/Shannon/LoomisWhitney.lean` の Shearer 応用パターンを **cover 非依存** に
拡張し、Loomis–Whitney (cover `S i = univ.erase i`) と Hypercube product projection
bound (singleton cover `S i = {i}`) の両方を corollary に持つ統一形を与える。

## 主定義・主定理

* `projectionSubset S A` — `S` 制限射影像。`(↥S → α)` 値の Finset。
* `jointEntropySubset_le_log_projectionSubset_card` — 任意 `S` 上の subset-entropy ≤ projection log 濃度。
* `brascamp_lieb_finset` — Brascamp–Lieb 不等式 (組合せ形)。
* `hypercube_product_projection_bound` — singleton cover で `|A| ≤ ∏ i, |π_{{i}}(A)|`。

## 既存 `LoomisWhitney.lean` との関係

LW (`loomis_whitney`) は `S i := univ.filter (· ≠ i)` の特殊形として理論的に
`brascamp_lieb_finset` の corollary だが、**既存ファイルの shape を維持** (定義
`projectionExcept` / 主定理 `loomis_whitney` 両方そのまま) する判断。新規
`BrascampLieb.lean` は独立に書き、`LoomisWhitney.lean` の `entropy_le_log_image_card`
+ `entropy_uniformOn_eq_log_card` を再利用するだけ。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-! ## Phase A — 任意 `S` 上の射影 plumbing -/

/-- 任意の `S : Finset (Fin n)` 上の射影像。
`A : Finset (Fin n → α)` を `(↥S → α)` 値の Finset に落とす。 -/
def projectionSubset {n : ℕ} {α : Type*} [DecidableEq α]
    (S : Finset (Fin n)) (A : Finset (Fin n → α)) :
    Finset (↥S → α) :=
  A.image (fun (x : Fin n → α) (j : ↥S) => x j.val)

/-- 任意 `S` 上の subset-entropy は射影像の log 濃度を超えない。

`μ = uniformOn (A : Set (Fin n → α))` のもとで、`Xs i ω := ω i` に対して
`jointEntropySubset μ Xs S = entropy μ (fun ω (j : ↥S) => ω j.val)`、これは
そのまま `entropy_le_log_image_card` の形なので、`f := (fun x j => x j.val)`
で適用する。LW の `jointEntropySubset_le_log_projectionExcept_card` の
**任意 cover 版** (索引型を `↥S` のまま使う simpler 版)。 -/
theorem jointEntropySubset_le_log_projectionSubset_card
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty) (S : Finset (Fin n)) :
    jointEntropySubset (uniformOn (A : Set (Fin n → α)))
        (fun (i : Fin n) (ω : Fin n → α) => ω i) S
      ≤ Real.log (projectionSubset S A).card := by
  classical
  haveI hprob : IsProbabilityMeasure (uniformOn (A : Set (Fin n → α))) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  -- jointEntropySubset μ (fun i ω => ω i) S = entropy μ (fun ω j => ω j.val)
  unfold jointEntropySubset
  -- The function f : (Fin n → α) → (↥S → α), ω ↦ (j ↦ ω j.val).
  set fproj : (Fin n → α) → (↥S → α) := fun (x : Fin n → α) (j : ↥S) => x j.val
    with hfproj_def
  have hfproj_meas : Measurable fproj :=
    measurable_pi_iff.mpr (fun (j : ↥S) => measurable_pi_apply j.val)
  -- Goal after `unfold jointEntropySubset`:
  --   entropy μ (fun ω (i : ↥S) => (fun i ω => ω i) i.val ω) ≤ log (projectionSubset S A).card
  -- which simplifies to entropy μ fproj ≤ log (A.image fproj).card.
  have h_le := entropy_le_log_image_card (β := Fin n → α) (γ := ↥S → α)
    hA fproj hfproj_meas
  -- (A.image fproj) = projectionSubset S A by def.
  show entropy (uniformOn (A : Set (Fin n → α))) fproj
      ≤ Real.log (projectionSubset S A).card
  exact h_le

/-! ## Phase B — Brascamp–Lieb 主定理 -/

/-- Brascamp–Lieb 不等式 (組合せ形)。

`S : ι → Finset (Fin n)` が各 `j : Fin n` を少なくとも `k` 回被覆するとき、
任意の有限部分集合 `A : Finset (Fin n → α)` (`A.Nonempty`) で:
$$|A|^k \le \prod_{i : \iota} |\pi_{S_i}(A)|.$$

ここで `\pi_{S_i}(A) = projectionSubset (S i) A`。
Loomis–Whitney は `S i := univ.filter (· ≠ i)` (各 `j` を `n-1` 回 cover) の特殊形。
Hypercube product projection bound は `S i := {i}` (各 `j` を 1 回 cover) の特殊形。 -/
theorem brascamp_lieb_finset
    {n k : ℕ} {ι : Type*} [Fintype ι]
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty)
    (S : ι → Finset (Fin n))
    (hk : ∀ j : Fin n,
      k ≤ (Finset.univ.filter (fun i : ι => j ∈ S i)).card) :
    A.card ^ k ≤ ∏ i : ι, (projectionSubset (S i) A).card := by
  classical
  haveI hprob : IsProbabilityMeasure (uniformOn (A : Set (Fin n → α))) :=
    isProbabilityMeasure_uniformOn A.finite_toSet hA
  set μ : Measure (Fin n → α) := uniformOn (A : Set (Fin n → α)) with hμ_def
  set Xs : Fin n → (Fin n → α) → α := fun i ω => ω i with hXs_def
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i => measurable_pi_apply i
  -- Apply Shearer engine
  have h_shearer := shearer_inequality μ Xs hXs_meas S hk
  -- LHS bridge: jointEntropy μ Xs = log #A
  have h_joint_log : jointEntropy μ Xs = Real.log A.card := by
    unfold jointEntropy
    have h_eq : (fun (ω : Fin n → α) (i : Fin n) => Xs i ω) = id := by
      funext ω; funext i; rfl
    rw [h_eq]
    exact entropy_uniformOn_eq_log_card hA
  rw [h_joint_log] at h_shearer
  -- RHS bridge: each summand ≤ log #(projectionSubset (S i) A)
  have h_marginal : ∀ i : ι,
      jointEntropySubset μ Xs (S i)
        ≤ Real.log (projectionSubset (S i) A).card := by
    intro i
    exact jointEntropySubset_le_log_projectionSubset_card hA (S i)
  have h_RHS_le : ∑ i : ι, jointEntropySubset μ Xs (S i)
      ≤ ∑ i : ι, Real.log (projectionSubset (S i) A).card :=
    Finset.sum_le_sum (fun i _ => h_marginal i)
  -- Combine: (k : ℝ) * log #A ≤ ∑ i, log #(projectionSubset (S i) A)
  have h_log :
      (k : ℝ) * Real.log A.card
        ≤ ∑ i : ι, Real.log (projectionSubset (S i) A).card :=
    h_shearer.trans h_RHS_le
  -- Positivity of projection cardinalities
  have h_proj_pos : ∀ i : ι, 0 < (projectionSubset (S i) A).card := by
    intro i
    have : (projectionSubset (S i) A).Nonempty :=
      hA.image (fun (x : Fin n → α) (j : ↥(S i)) => x j.val)
    exact this.card_pos
  have h_proj_ne : ∀ i : ι,
      ((projectionSubset (S i) A).card : ℝ) ≠ 0 := fun i => by
    exact_mod_cast (h_proj_pos i).ne'
  -- Convert ∑ log to log ∏
  have h_sum_log_eq :
      (∑ i : ι, Real.log (projectionSubset (S i) A).card)
        = Real.log (∏ i : ι, ((projectionSubset (S i) A).card : ℝ)) := by
    rw [Real.log_prod (fun i _ => h_proj_ne i)]
  rw [h_sum_log_eq] at h_log
  -- LHS: (k : ℝ) * log #A = log (#A ^ k)
  have h_lhs_eq :
      (k : ℝ) * Real.log A.card = Real.log ((A.card : ℝ) ^ k) := by
    rw [Real.log_pow]
  rw [h_lhs_eq] at h_log
  -- Peel off log via monotonicity
  have h_card_pos : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have h_lhs_pos : (0 : ℝ) < (A.card : ℝ) ^ k := pow_pos h_card_pos _
  have h_rhs_pos : (0 : ℝ) < ∏ i : ι, ((projectionSubset (S i) A).card : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast h_proj_pos i)
  have h_pow_le :
      (A.card : ℝ) ^ k
        ≤ ∏ i : ι, ((projectionSubset (S i) A).card : ℝ) :=
    (Real.log_le_log_iff h_lhs_pos h_rhs_pos).mp h_log
  -- Cast to ℕ
  have h_cast :
      ((A.card ^ k : ℕ) : ℝ)
        ≤ (((∏ i : ι, (projectionSubset (S i) A).card) : ℕ) : ℝ) := by
    push_cast
    exact h_pow_le
  exact_mod_cast h_cast

/-! ## Phase C — Hypercube product projection bound (singleton cover corollary) -/

/-- Singleton-cover 系の corollary: 各 `i : Fin n` を cover が単独 `{i}` で 1 回ずつ覆うと、
任意の `A : Finset (Fin n → α)` (`A.Nonempty`) で
$$|A| \le \prod_{i : \text{Fin}\,n} |\pi_{\{i\}}(A)|.$$

これは Brascamp–Lieb で `S i := {i}`, `k := 1` を取った特殊形。
`α = Bool` を渡せば Boolean cube 上で `|π_{{i}}(A)| ≤ 2` から `|A| ≤ 2^n` を回復。
Han-Bregman 流の hypercube isoperimetric inequality の基本形。 -/
theorem hypercube_product_projection_bound
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {A : Finset (Fin n → α)} (hA : A.Nonempty) :
    A.card ≤ ∏ i : Fin n, (projectionSubset ({i} : Finset (Fin n)) A).card := by
  classical
  -- Apply BL with S i := {i}, k := 1
  set S : Fin n → Finset (Fin n) := fun i => ({i} : Finset (Fin n)) with hS_def
  have h_cover : ∀ j : Fin n,
      1 ≤ (Finset.univ.filter (fun i : Fin n => j ∈ S i)).card := by
    intro j
    -- {i | j ∈ {i}} = {i | i = j} = {j}, card = 1
    have h_filter_eq : Finset.univ.filter (fun i : Fin n => j ∈ S i)
        = ({j} : Finset (Fin n)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, S]
      exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [h_filter_eq, Finset.card_singleton]
  have h_BL := brascamp_lieb_finset (k := 1) hA S h_cover
  -- A.card ^ 1 = A.card
  simpa using h_BL

end InformationTheory.Shannon
