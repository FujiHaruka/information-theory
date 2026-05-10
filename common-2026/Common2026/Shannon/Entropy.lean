import Common2026.Shannon.Bridge
import Common2026.Shannon.CondMutualInfo

/-!
# Entropy chain rule, conditional entropy tower, and conditioning monotonicity (Phase A skeleton)

Han 不等式ムーンショット ([`docs/han-moonshot-plan.md`](../../../docs/han-moonshot-plan.md)) の Phase A:
2 変数版の Shannon 不等式群を整備する。Phase B (n 変数 Han 本体) はここで揃った
chain rule と「条件付けで減る」を `Fin n` の prefix に対して反復適用して証明する。

## 主定理

* `entropy_pair_eq_entropy_add_condEntropy` ─ `H(X, Y) = H(X) + H(Y | X)` (chain rule)
* `condEntropy_tower` ─ `H(X | Y, Z) = ∫ y, ∫ z, ... d(condDistrib Z Y μ y) d P_Y` (補助補題)
* `condMutualInfo_eq_condEntropy_sub_condEntropy` ─ `I(X; Z | Y) = H(X | Y) - H(X | Y, Z)` (中間補題)
* `condEntropy_le_condEntropy_of_pair` ─ `H(X | Y, Z) ≤ H(X | Y)` (条件付けで減る)

## 戦略 (Phase 0 結果より)

中間補題は `condMutualInfo` の compProd 形定義を `klDiv_compProd_const_eq_lintegral_of_ac`
(Bridge.lean Helper 1) で fiber 上に展開し、各 fiber で Bridge 主定理
`mutualInfo_eq_entropy_sub_condEntropy` を呼ぶ。Bridge 全体の写経は不要。tower 補題は
`μ.map (Yo, Zo) = (μ.map Yo) ⊗ₘ condDistrib Zo Yo μ` で disintegration し Tonelli を効かせる。
詳細は [`docs/han-mathlib-inventory.md`](../../../docs/han-mathlib-inventory.md) §3。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- Chain rule for Shannon entropy: `H(X, Y) = H(X) + H(Y | X)`. -/
theorem entropy_pair_eq_entropy_add_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hYo : Measurable Yo) :
    entropy μ (fun ω => (Xs ω, Yo ω))
      = entropy μ Xs + InformationTheory.MeasureFano.condEntropy μ Yo Xs := by
  sorry

/-- Tower of conditional entropy: disintegrating the joint conditioner `(Y, Z)` into
`Z` given `Y` followed by `Y`,
`H(X | Y, Z) = ∫ y, ∫ z, Σ x, negMulLog (condDistrib X (Y,Z) μ (y,z) {x})
                d(condDistrib Z Y μ y) d P_Y`.

The inner expression `Σ x, negMulLog (condDistrib X (Y,Z) μ (y,z) {x})` is the slice-wise
Shannon entropy of `X` conditioned on the simultaneous value of `Y` and `Z`. The two
outer integrals build back up to `H(X | Y, Z)`. Required as a lemma for the middle
result `condMutualInfo_eq_condEntropy_sub_condEntropy`. -/
theorem condEntropy_tower
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
    InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
      = ∫ y, ∫ z, ∑ x : X, Real.negMulLog
            ((condDistrib Xs (fun ω => (Yo ω, Zo ω)) μ (y, z)).real {x})
            ∂(condDistrib Zo Yo μ y) ∂(μ.map Yo) := by
  sorry

/-- The chain rule for conditional mutual information in Shannon (additive) form:
`I(X; Z | Y) = H(X | Y) - H(X | Y, Z)`.

Strategy (per Phase 0 inventory): expand `condMutualInfo μ Xs Zo Yo` into its compProd
form, apply Bridge Helper 1 (`klDiv_compProd_const_eq_lintegral_of_ac`) to convert the
joint KL into a fiber-wise integral, then invoke Bridge's main theorem
`mutualInfo_eq_entropy_sub_condEntropy` on each fiber. The resulting fiber-wise
expression integrates against `μ.map Yo` to produce `H(X|Y) - H(X|Y,Z)`, where the
second term requires `condEntropy_tower` to absorb the inner conditional entropy. -/
theorem condMutualInfo_eq_condEntropy_sub_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
    (condMutualInfo μ Xs Zo Yo).toReal
      = InformationTheory.MeasureFano.condEntropy μ Xs Yo
        - InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω)) := by
  sorry

/-- Conditioning never increases entropy: `H(X | Y, Z) ≤ H(X | Y)`. Direct corollary of
the middle lemma `condMutualInfo_eq_condEntropy_sub_condEntropy` and
`condMutualInfo_nonneg`. Phase B (n-variable Han) reduces to iterating this on
prefixes of `Fin n`. -/
theorem condEntropy_le_condEntropy_of_pair
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
    InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
      ≤ InformationTheory.MeasureFano.condEntropy μ Xs Yo := by
  sorry

end InformationTheory.Shannon
