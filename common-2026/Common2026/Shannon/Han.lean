import Common2026.Shannon.Entropy

/-!
# Joint entropy on `Fin n` and the n-variable chain rule (Phase B skeleton)

Han 不等式ムーンショット ([`docs/han-moonshot-plan.md`](../../../docs/han-moonshot-plan.md))
の Phase B skeleton。Phase A の 2 変数 chain rule
`entropy_pair_eq_entropy_add_condEntropy` を `Fin n` の prefix に対して反復適用して
n 変数 chain rule を得る。Phase C (Han の不等式本体) の入口。

## 主要定義・主定理

* `jointEntropy μ Xs` ─ `Fin n → Ω → α` の joint entropy。`entropy` の薄いラッパー。
* `jointEntropyExcept μ Xs i` ─ index `i` を除いた `{j // j ≠ i}`-値の joint entropy。
* `jointEntropy_chain_rule` ─ `H(X_0, …, X_{n-1}) = ∑ i, H(X_i | X_0, …, X_{i-1})`。

## 戦略

`n` に関する induction:

* base (`n = 0`): joint は単一点 `Fin 0 → α` 上、`entropy = 0`、和も空。
* step (`n + 1`): `Fin (n+1) → α` を「`Fin n` への restriction」と「`Xs ⟨n, _⟩`」の
  pair に分解 → Phase A `entropy_pair_eq_entropy_add_condEntropy` を 1 段適用 →
  IH で n-prefix を展開 → `Fin.sum_univ_castSucc` 系で和に整形。

Pi-値 RV の instance (`Pi.fintype`, `MeasurableSpace.pi`,
`Pi.instMeasurableSingletonClass`) は Phase 0 で `Fin n → α` まで自動発火確認済。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Joint entropy of a finite family of random variables. -/
noncomputable def jointEntropy
    (μ : Measure Ω) (Xs : Fin n → Ω → α) : ℝ :=
  entropy μ (fun ω i => Xs i ω)

/-- Joint entropy with the `i`-th coordinate removed. -/
noncomputable def jointEntropyExcept
    (μ : Measure Ω) (Xs : Fin n → Ω → α) (i : Fin n) : ℝ :=
  entropy μ (fun ω (j : {j // j ≠ i}) => Xs j ω)

/-- n 変数 chain rule for Shannon joint entropy:
`H(X_0, …, X_{n-1}) = ∑ i, H(X_i | X_0, …, X_{i-1})`.

Phase A の `entropy_pair_eq_entropy_add_condEntropy` を `n` についての帰納で
反復適用して証明する。 -/
theorem jointEntropy_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    jointEntropy μ Xs
      = ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy μ (Xs i)
            (fun ω (j : Fin i.val) =>
              Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  sorry

end InformationTheory.Shannon
