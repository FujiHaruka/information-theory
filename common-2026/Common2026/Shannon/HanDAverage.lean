import Common2026.Shannon.HanD

/-!
# Han Phase D-1: subset average chain (skeleton)

Han Phase D ロードマップ ([`docs/han-phase-d-plan.md`](../../../docs/han-phase-d-plan.md))
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

/-- $H_k = (k \binom{n}{k})^{-1} \sum_{|S|=k} H(X_S)$。
$k = 0$ では分母 $0$ となるので $H_0 = 0$ ((`Real` の $a/0 = 0$ 規約)。 -/
noncomputable def averageSubsetEntropy
    (μ : Measure Ω) (Xs : Fin n → Ω → α) (k : ℕ) : ℝ :=
  (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      jointEntropySubset μ Xs S) / (k * n.choose k)

/-- 二重和 reindex: $|S|=k+1$ にわたる $\sum_{i \in S} f(S \setminus \{i\})$ の和は
$|T|=k$ にわたる $f(T)$ の和を $(n-k)$ 倍したもの。各 $T$ は ちょうど $(n-k)$ 個の
$S = T \cup \{i\}$ ($i \in [n] \setminus T$) から到達される。

写経テンプレ: `Mathlib/Algebra/Polynomial/Derivative.lean:710-728`
(`iterate_derivative_prod_X_sub_C` 内)。`sum_finset_product'` で product 化 →
`sum_bij'` で `(S, i) ↦ (S.erase i, i)` ↔ `(T, j) ↦ (insert j T, j)` の双方向写像 →
`sum_finset_product'` 逆向きで再び二重和 → `mul_sum` + `sum_const` + `card_sdiff` で整理。 -/
private lemma sum_powersetCard_succ_erase
    (f : Finset (Fin n) → ℝ) {k : ℕ} (hk : k + 1 ≤ n) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k+1),
        ∑ i ∈ S, f (S.erase i)
      = ((n - k) : ℝ)
        * ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, f T := by
  classical
  calc
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k+1),
        ∑ i ∈ S, f (S.erase i)
      = ∑ (S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k+1))
            (i ∈ (Finset.univ : Finset (Fin n))) with i ∈ S, f (S.erase i) := by
        rw [← Finset.sum_finset_product']
        grind
    _ = ∑ (T ∈ (Finset.univ : Finset (Fin n)).powersetCard k)
            (i ∈ (Finset.univ : Finset (Fin n))) with i ∉ T, f T := by
        apply Finset.sum_bij' (fun ⟨S, i⟩ _ => ⟨S.erase i, i⟩)
            (fun ⟨T, i⟩ _ => ⟨insert i T, i⟩)
        · intro r hr; dsimp at hr ⊢; congr 1; grind
        · intro r hr; dsimp at hr ⊢; congr 1; grind
        all_goals grind
    _ = ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
          ∑ _i ∈ (Finset.univ : Finset (Fin n)) \ T, f T := by
        rw [← Finset.sum_finset_product']
        grind
    _ = ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ((n - k) : ℝ) * f T := by
        have hk' : k ≤ n := by omega
        refine Finset.sum_congr rfl (fun T hT => ?_)
        rw [Finset.sum_const]
        have hT' : T.card = k := (Finset.mem_powersetCard.mp hT).2
        have h_sdiff_card : ((Finset.univ : Finset (Fin n)) \ T).card = n - k := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ T), Finset.card_univ,
              Fintype.card_fin, hT']
        rw [h_sdiff_card, nsmul_eq_mul, Nat.cast_sub hk']
    _ = ((n - k) : ℝ) * ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k, f T := by
        rw [Finset.mul_sum]

/-- Han 1978 単発: $k \cdot S_{k+1} \le (n-k) \cdot S_k$ where
$S_k = \sum_{|T|=k} H(X_T)$。`han_inequality_subset` を $|S| = k+1$ の各 $S$ で
適用して和を取り、$(S, i) \mapsto (S \setminus \{i\}, i)$ の reindex で右辺を整理する。 -/
theorem subset_sum_step
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {k : ℕ} (hk : k + 1 ≤ n) :
    (k : ℝ) * (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k+1),
                  jointEntropySubset μ Xs S)
      ≤ ((n - k) : ℝ) * (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
                            jointEntropySubset μ Xs T) := by
  classical
  -- 各 |S|=k+1 の S で han_inequality_subset を適用 (S.card = k+1 ⟹ 係数 (S.card - 1) = k)
  have h_pointwise : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k+1),
      (k : ℝ) * jointEntropySubset μ Xs S
        ≤ ∑ i ∈ S, jointEntropySubset μ Xs (S.erase i) := by
    intro S hS
    have hcard : S.card = k + 1 := (Finset.mem_powersetCard.mp hS).2
    have h := han_inequality_subset μ Xs hXs S
    rw [hcard] at h
    have heq : ((k + 1 : ℕ) : ℝ) - 1 = (k : ℝ) := by push_cast; ring
    rwa [heq] at h
  -- 集計し、LHS で k を sum 外に出す
  have h_sum :
      (k : ℝ) * (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k+1),
                    jointEntropySubset μ Xs S)
        ≤ ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k+1),
            ∑ i ∈ S, jointEntropySubset μ Xs (S.erase i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum h_pointwise
  -- 補助補題で RHS を reindex
  rw [sum_powersetCard_succ_erase (fun T => jointEntropySubset μ Xs T) hk] at h_sum
  exact h_sum

/-- Han 1978 主定理: $H_k$ は $k$ について非増加。`subset_sum_step` と
$(k+1) \binom{n}{k+1} = (n-k) \binom{n}{k}$ を組み合わせる。 -/
theorem subset_average_anti
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    averageSubsetEntropy μ Xs (k+1) ≤ averageSubsetEntropy μ Xs k := by
  have h_step := subset_sum_step μ Xs hXs hkn
  -- 分母の正値性
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkp1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hk_le : k ≤ n := by omega
  have hC_k_pos : (0 : ℝ) < (n.choose k : ℝ) := by
    have : 0 < n.choose k := Nat.choose_pos hk_le
    exact_mod_cast this
  have hC_kp1_pos : (0 : ℝ) < (n.choose (k + 1) : ℝ) := by
    have : 0 < n.choose (k + 1) := Nat.choose_pos hkn
    exact_mod_cast this
  -- choose recurrence: (k+1) * C(n,k+1) = C(n,k) * (n-k)
  have h_choose_nat : (k + 1) * n.choose (k + 1) = n.choose k * (n - k) := by
    rw [mul_comm (k + 1) _, Nat.choose_succ_right_eq]
  have h_choose_ℝ :
      ((k + 1 : ℕ) : ℝ) * (n.choose (k + 1) : ℝ)
        = (n.choose k : ℝ) * ((n : ℝ) - (k : ℝ)) := by
    have := congrArg ((↑) : ℕ → ℝ) h_choose_nat
    push_cast at this
    rw [Nat.cast_sub hk_le] at this
    push_cast
    linarith
  -- h_step の両辺に C(n,k) ≥ 0 を掛ける (約分の向きを揃える)
  have h_step_C := mul_le_mul_of_nonneg_right h_step hC_k_pos.le
  -- 不等式変形
  unfold averageSubsetEntropy
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- 目標: S_{k+1} * (↑k * ↑C(n,k)) ≤ S_k * (↑(k+1) * ↑C(n,k+1))
  set A := ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k+1),
              jointEntropySubset μ Xs S with hA_def
  set B := ∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
              jointEntropySubset μ Xs T with hB_def
  calc A * (((k : ℕ) : ℝ) * (n.choose k : ℝ))
      = ((k : ℝ) * A) * (n.choose k : ℝ) := by ring
    _ ≤ (((n : ℝ) - (k : ℝ)) * B) * (n.choose k : ℝ) := h_step_C
    _ = B * ((n.choose k : ℝ) * ((n : ℝ) - (k : ℝ))) := by ring
    _ = B * (((k + 1 : ℕ) : ℝ) * (n.choose (k + 1) : ℝ)) := by rw [h_choose_ℝ]

/-- 連鎖系: $H_{k_2} \le H_{k_1}$ for $1 \le k_1 \le k_2 \le n$。
`subset_average_anti` を `Nat.le_induction` で反復。 -/
theorem subset_average_chain
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {k₁ k₂ : ℕ} (h1 : 1 ≤ k₁) (h12 : k₁ ≤ k₂) (h2 : k₂ ≤ n) :
    averageSubsetEntropy μ Xs k₂ ≤ averageSubsetEntropy μ Xs k₁ := by
  -- h2 を motive に含めるために revert してから k₂, h12 で induction
  revert h2
  induction k₂, h12 using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ k₂' h ih =>
    intro h2
    have h2' : k₂' ≤ n := by omega
    have hk1' : 1 ≤ k₂' := by omega
    exact (subset_average_anti μ Xs hXs hk1' h2).trans (ih h2')

end InformationTheory.Shannon
