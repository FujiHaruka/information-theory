import Common2026.Shannon.SanovLDP
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.Monoid

/-!
# KL divergence vector form continuity (B-1'' Phase A)

`klDivSumForm_ofVec p q := ∑ a, p a · (log (p a) - log (q a))` の
`p : α → ℝ` (point-wise / Pi topology) 上での連続性。

`SanovLDP.lean` の `klDivIndex c n Q` は `klDivSumForm_ofVec (c · / n) (Q.real ∘ singleton)`
に書き直せる (`klDivIndex_eq_ofVec`)、これにより Phase B / D の rounded type sequence の
KL 値の `Tendsto` を `klDivSumForm_ofVec` の連続性 + `(c/n → P°)` で取れる。

詳細: `docs/shannon/sanov-ldp-equality-plan.md` Phase A.
-/

namespace InformationTheory.Shannon

open MeasureTheory Real

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- KL divergence in finite-alphabet **vector** form (`α → ℝ` 入力):
`klDivSumForm_ofVec p q := ∑ a, p a · (log (p a) - log (q a))`.

`Measure α` 経由ではなく `α → ℝ` の Pi-topology で連続性を取るための変種。
B-1' の `klDivIndex c n Q` とは `c · / n` を `p`、`Q.real ∘ singleton` を `q` として一致
(`klDivIndex_eq_ofVec`). -/
noncomputable def klDivSumForm_ofVec (p q : α → ℝ) : ℝ :=
  ∑ a : α, p a * (Real.log (p a) - Real.log (q a))

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- **KL の `p` 上での連続性** (Phase A 主補題):
`q a > 0` for all `a` ⟹ `p ↦ klDivSumForm_ofVec p q` is continuous on `α → ℝ`.

境界処理:
* `p a = 0`: `negMulLog 0 = 0` ⇒ `p a · log p a = 0` で連続。
* `q a = 0`: 除外 (`hq_pos`)。`log q a` は定数として登場。

証明 sketch: 各 `a` で `p a · log p a = -negMulLog (p a)` を `Real.negMulLog_def` で取り
`Real.continuous_negMulLog.comp (continuous_apply a)`。`p ↦ -p a · log q a` は定数倍で連続。
合計 `p a · (log p a - log q a)` の連続性、`continuous_finset_sum` で plumbing。 -/
theorem klDivSumForm_ofVec_continuous
    (q : α → ℝ) (_hq_pos : ∀ a, 0 < q a) :
    Continuous (fun p : α → ℝ => klDivSumForm_ofVec p q) := by
  -- Rewrite each summand `p a * (log (p a) - log (q a))` as
  --   `-(Real.negMulLog (p a)) - Real.log (q a) * p a`
  -- and use `Real.continuous_negMulLog` (extends `x * log x` continuously through 0).
  show Continuous fun p : α → ℝ => ∑ a : α, p a * (Real.log (p a) - Real.log (q a))
  have hrewrite : ∀ (p : α → ℝ) (a : α),
      p a * (Real.log (p a) - Real.log (q a))
        = -(Real.negMulLog (p a)) - Real.log (q a) * p a := by
    intro p a
    rw [Real.negMulLog_eq_neg]
    ring
  simp_rw [hrewrite]
  refine continuous_finsetSum (Finset.univ : Finset α) (fun a _ => ?_)
  have h_eval : Continuous (fun p : α → ℝ => p a) := continuous_apply a
  have h_negMulLog : Continuous (fun p : α → ℝ => Real.negMulLog (p a)) :=
    Real.continuous_negMulLog.comp h_eval
  exact h_negMulLog.neg.sub (h_eval.const_mul (Real.log (q a)))

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **`klDivIndex` (B-1') と `klDivSumForm_ofVec` の連絡**:
`klDivIndex c n Q = klDivSumForm_ofVec (c/n) (Q.real ∘ singleton)`. -/
lemma klDivIndex_eq_ofVec (c : α → ℕ) (n : ℕ) (Q : Measure α) :
    klDivIndex c n Q
      = klDivSumForm_ofVec (fun a => (c a : ℝ) / n) (fun a => Q.real {a}) := rfl

end InformationTheory.Shannon
