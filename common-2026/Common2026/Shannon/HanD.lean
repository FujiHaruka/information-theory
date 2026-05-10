import Common2026.Shannon.Han

/-!
# Han Phase D: subset 版 joint entropy infrastructure (skeleton)

Han Phase D ロードマップ ([`docs/han-phase-d-plan.md`](../../../docs/han-phase-d-plan.md))
の Phase A skeleton。`Fin n` の任意部分集合 `S : Finset (Fin n)` に対する
joint entropy `H(X_S)` を定義し、Phase B (D-1 subset average chain) /
Phase C (D-2 Shearer) の入口となる 4 主定理を sorry-driven で並べる。

## 主要定義・主定理

* `jointEntropySubset μ Xs S` ─ `(i : ↑S) → α` 値の joint entropy。
* `jointEntropySubset_univ` ─ `S = univ` で `jointEntropy μ Xs` に一致。
* `jointEntropySubset_chain_rule` ─ subset 版 chain rule。
* `condEntropy_subset_anti` ─ subset 版 conditioning monotonicity (`T₁ ⊆ T₂ ⟹` 条件側を増やすと減る)。
* `han_inequality_subset` ─ Han の不等式の subset 版。`han_inequality` を `Finset.orderEmbOfFin S` で
  restrict し reshape する見込み。

## 戦略 (inventory より)

* Pi 値 instance (`Fintype`, `MeasurableSpace`, `MeasurableSingletonClass`,
  `Nonempty`, `DecidableEq`) は `Han.lean` の `{j // j ≠ i}` 前例から自動発火見込み
  (inventory 軸 (c))。
* `jointEntropySubset_chain_rule` / `condEntropy_subset_anti` は
  `Finset.induction_on` で `S` を 1 元ずつ拡張、Phase A/B の写経再利用。
* `han_inequality_subset` は `Finset.orderEmbOfFin S rfl : Fin S.card ↪o Fin n`
  経由で既存 `han_inequality` を適用、両辺を `entropy_measurableEquiv_comp` +
  `MeasurableEquiv.piCongrLeft` で reshape (inventory 軸 (d), 50〜70 行見積もり)。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- 部分集合 `S : Finset (Fin n)` 上の joint entropy。
`(i : ↑S) → α` 値の random variable のエントロピー。 -/
noncomputable def jointEntropySubset
    (μ : Measure Ω) (Xs : Fin n → Ω → α) (S : Finset (Fin n)) : ℝ :=
  entropy μ (fun ω (i : S) => Xs i.val ω)

/-- `S = Finset.univ` のとき subset 版は通常の `jointEntropy` に一致。 -/
theorem jointEntropySubset_univ
    (μ : Measure Ω) (Xs : Fin n → Ω → α) :
    jointEntropySubset μ Xs Finset.univ = jointEntropy μ Xs := by
  sorry

/-- subset 版 chain rule:
`H(X_S) = ∑ i ∈ S, H(X_i | X_{S ∩ {j : j < i}})`。

Phase A の `entropy_pair_eq_entropy_add_condEntropy` を `Finset.induction_on` で
`S` の各要素について反復適用する。 -/
theorem jointEntropySubset_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : Finset (Fin n)) :
    jointEntropySubset μ Xs S
      = ∑ i ∈ S,
          InformationTheory.MeasureFano.condEntropy μ (Xs i)
            (fun ω (j : (S.filter (· < i))) => Xs j.val ω) := by
  sorry

/-- subset 版 conditioning monotonicity:
`T₁ ⊆ T₂ ⟹ H(X_i | X_{T₂}) ≤ H(X_i | X_{T₁})`。

Phase A の `condEntropy_le_condEntropy_of_pair` を `T₂ \ T₁` の要素を
1 つずつ `T₁` に加える induction で繰り返す。 -/
theorem condEntropy_subset_anti
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (i : Fin n) {T₁ T₂ : Finset (Fin n)} (hT : T₁ ⊆ T₂) :
    InformationTheory.MeasureFano.condEntropy μ (Xs i)
        (fun ω (j : T₂) => Xs j.val ω)
      ≤ InformationTheory.MeasureFano.condEntropy μ (Xs i)
          (fun ω (j : T₁) => Xs j.val ω) := by
  sorry

/-- Han の不等式の subset 版:
`(|S| - 1) · H(X_S) ≤ ∑ i ∈ S, H(X_{S \ {i}})`。

`Finset.orderEmbOfFin S rfl : Fin S.card ↪o Fin n` で `S` を `Fin S.card` から
の埋め込みとみなし、`Xs' k ω := Xs (S.orderEmbOfFin rfl k) ω` に対して既存
`han_inequality` を適用、両辺を `jointEntropySubset` 形に reshape する。 -/
theorem han_inequality_subset
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : Finset (Fin n)) :
    ((S.card : ℝ) - 1) * jointEntropySubset μ Xs S
      ≤ ∑ i ∈ S, jointEntropySubset μ Xs (S.erase i) := by
  sorry

end InformationTheory.Shannon
