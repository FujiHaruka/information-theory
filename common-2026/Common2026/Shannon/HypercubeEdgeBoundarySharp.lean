import Common2026.Shannon.HypercubeEdgeBoundary
import Common2026.Shannon.HanD
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Hypercube edge-boundary entropy-sharp inequality (B-2'')

Boolean cube `Fin n → Bool` 上の edge-boundary に関する **entropy-sharp** 形
isoperimetric 不等式:

  `|A| · (n - log₂ |A|) ≤ |∂_e A|`

(Harper / Han / Cover-Thomas 流。AM-GM 形 B-2' `edgeBoundary_ge_AMGM` よりも sharp。)

戦略は `condEntropy_coord_eq` (核補題, Phase B) で `μ_A := uniformOn A` 上の
方向 `i` の条件付きエントロピーを fibre size 1/2 の point-wise 計算で
`(2 (|A| - |π_{≠i}(A)|) / |A|) · log 2` と評価し、chain rule (`jointEntropy_chain_rule`) +
conditioning monotonicity (`condEntropy_subset_anti`) で Σ を log|A| で押さえ、
B-2' counting identity (`edgeBoundary_count_eq`) と組み合わせる。

詳細は `docs/shannon/hypercube-edge-boundary-sharp-plan.md` を参照。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-! ## Phase A — `μ_A := uniformOn (A : Set (Fin n → Bool))` setup -/

/-- `μ_A := uniformOn (A : Set (Fin n → Bool))` は `A.Nonempty` で確率測度。 -/
private lemma uniformOn_A_isProb
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    IsProbabilityMeasure (uniformOn (A : Set (Fin n → Bool))) := by
  sorry

/-- 座標射影 `ω ↦ ω i` の可測性。`measurable_pi_apply` の薄いラッパー。 -/
private lemma xsCoord_measurable {n : ℕ} (i : Fin n) :
    Measurable (fun ω : Fin n → Bool => ω i) := by
  sorry

/-- `{j // j ≠ i}` 上への投影 `ω ↦ fun j => ω j.val` の可測性。 -/
private lemma xExceptCoord_measurable {n : ℕ} (i : Fin n) :
    Measurable (fun ω : Fin n → Bool => fun (j : {j : Fin n // j ≠ i}) => ω j.val) := by
  sorry

/-- `μ_A` 上の coord-family `Xs i ω := ω i` の joint entropy は `log |A|`。
B-2' AM-GM 形と同じ `h_joint_log` reshape パターン。 -/
private lemma jointEntropy_xs_eq_log_card
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    jointEntropy (uniformOn (A : Set (Fin n → Bool)))
        (fun (i : Fin n) (ω : Fin n → Bool) => ω i)
      = Real.log A.card := by
  sorry

/-! ## Phase B — 核補題 `condEntropy_coord_eq` -/

/-- direction `i` の doubly-covered fibre 数。`|A| - |π_{≠i}(A)|`。
plan の `D_i` (B-2' Phase A 判断ログ #3) と同一。 -/
private noncomputable def doublyCoveredCount
    {n : ℕ} (i : Fin n) (A : Finset (Fin n → Bool)) : ℕ :=
  A.card - (projectionExcept i A).card

/-- 各 `y ∈ projectionExcept i A` で fibre size `c_i(y) ∈ {1, 2}`、
size 2 の fibre 数は `doublyCoveredCount i A`。 -/
private lemma fibre_size_classification
    {n : ℕ} (i : Fin n) {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    ((projectionExcept i A).filter
        (fun y => (A.filter (fun x => projMap i x = y)).card = 2)).card
      = doublyCoveredCount i A := by
  sorry

/-- 各 `y ∈ projectionExcept i A` 上の point-wise エントロピー値:
size-2 fibre → `Bern(1/2)` で和 `log 2`、size-1 fibre → Dirac で和 `0`。 -/
private lemma pointwise_condEntropy_value
    {n : ℕ} (i : Fin n) {A : Finset (Fin n → Bool)} (hA : A.Nonempty)
    (y : {j : Fin n // j ≠ i} → Bool)
    (hy : y ∈ projectionExcept i A) :
    ∑ b : Bool, Real.negMulLog
        ((condDistrib (fun ω : Fin n → Bool => ω i)
            (fun ω j => ω j.val)
            (uniformOn (A : Set (Fin n → Bool))) y).real {b})
      = if (A.filter (fun x => projMap i x = y)).card = 2 then Real.log 2 else 0 := by
  sorry

/-- 核補題: 方向 `i` の条件付きエントロピー。
`condEntropy μ_A (Xs i) X_{≠i} = (2 (|A| - |π_{≠i}(A)|) / |A|) · log 2`。 -/
theorem condEntropy_coord_eq
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) (i : Fin n) :
    InformationTheory.MeasureFano.condEntropy
        (uniformOn (A : Set (Fin n → Bool)))
        (fun ω : Fin n → Bool => ω i)
        (fun ω (j : {j : Fin n // j ≠ i}) => ω j.val)
      = (2 * ((A.card : ℝ) - ((projectionExcept i A).card : ℝ)) / A.card)
          * Real.log 2 := by
  sorry

/-! ## Phase C — chain rule + conditioning monotonicity -/

/-- Σ_i の条件付きエントロピーを `log|A|` で押さえる。

chain rule (`jointEntropy_chain_rule`) で
`log|A| = Σ_i condEntropy μ_A (Xs i) X_{<i}` を取り、
各 `i` で `condEntropy_subset_anti` を
`T₁ := univ.filter (· < i) ⊆ T₂ := univ.erase i` に適用し、
`Fin i.val ≃ ↥(univ.filter (· < i))` と `{j // j ≠ i} ≃ ↥(univ.erase i)` の reshape で結ぶ。 -/
theorem sum_condEntropy_le_log_card
    {n : ℕ} {A : Finset (Fin n → Bool)} (hA : A.Nonempty) :
    ∑ i : Fin n,
        InformationTheory.MeasureFano.condEntropy
          (uniformOn (A : Set (Fin n → Bool)))
          (fun ω : Fin n → Bool => ω i)
          (fun ω (j : {j : Fin n // j ≠ i}) => ω j.val)
      ≤ Real.log A.card := by
  sorry

/-! ## Phase D — 主定理 -/

/-- B-2'' 主結果 (Harper / Han entropy-sharp edge-isoperimetric):
nonempty `A ⊆ Fin n → Bool` で `|A| · (n - log₂ |A|) ≤ |∂_e A|`。

`condEntropy_coord_eq` (Phase B) と `sum_condEntropy_le_log_card` (Phase C) で
Σ を `log|A|` で押さえ、B-2' の counting identity `edgeBoundary_count_eq`
(`2 Σ_i |π_{≠i}(A)| = n|A| + |∂_e A|`) を ℝ にキャストして代入、
`Real.logb 2 |A| = log |A| / log 2` の bridge で `log₂` 形に整える。 -/
theorem edgeBoundary_entropy_sharp {n : ℕ} {A : Finset (Fin n → Bool)}
    (hA : A.Nonempty) :
    (A.card : ℝ) * ((n : ℝ) - Real.logb 2 A.card) ≤ (edgeBoundaryCount A : ℝ) := by
  sorry

end InformationTheory.Shannon
