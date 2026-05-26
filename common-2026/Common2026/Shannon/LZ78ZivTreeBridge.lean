import Common2026.Draft.Shannon.LZ78ZivTreeNode
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

/-!
# LZ78 Ziv combinatorics — CT 13.5.5 bridge feasibility probe (HONEST DEFECT REPORT)

This file is the result of a skeleton-first feasibility probe of the proposed
final crux of LZ78 achievability: discharging `IsLZ78ZivCombinatorialCoreOverhead`
(`LZ78ZivTreeNode.lean`) by combining the genuine per-node log-sum step
`node_logsum_step` with a grouping-overhead step and a tree-measure-vs-path-measure
bridge step (CT 13.5.5).

## Finding: `IsLZ78ZivCombinatorialCoreOverhead` is mathematically FALSE

The probe discovered that the target hypothesis itself is **false** as a
per-block, per-path `∀ n ∀ ω` statement — so it cannot be discharged (a false
`Prop` is unsatisfiable; any "discharge" would prove a falsehood). The
`(a,a,b)` single check recorded in `LZ78ZivTreeNode.lean`'s docstring as
evidence that the overhead form is "mathematically TRUE" is *not* enough to
establish the universal statement, and it misses an entire family of
counterexamples.

**Counterexample (genuine, machine-checked below).** Take the *constant
process* (`T = id`, `X ≡ a`) on `Ω = Unit` with the Dirac measure. Every block
is `a^n`, so `Pₙ = (μ.map (blockRV n)).real {a^n} = 1` and `-log Pₙ = 0`. The
genuine longest-prefix LZ parse of `a^n` emits `c ≈ √n` *distinct* phrases
(`a, aa, aaa, …`; `lz78PhraseStrings_count_le`). The overhead core then claims

```
c · log c ≤ -log Pₙ + c · log(|α|+1) = 0 + c · log(|α|+1),
```

i.e. `log c ≤ log(|α|+1)`, i.e. `c ≤ |α|+1`. But `c` grows like `√n` without
bound, so for `n = 16`, `α = Bool` (`|α| = 2`) the parse has `c = 5` phrases
and `5·log 5 ≈ 8.05 > 5·log 3 ≈ 5.49`. The inequality fails. ∎

This is **not** merely the lower-order-overhead subtlety (`overhead/n → 0`):
it is a genuine failure of the *finite-`n`, every-`ω`* form. The same failure
appears for non-degenerate i.i.d. processes with `P(a)` close to `1` (block
`a^n`, a rare but positive-probability event), where `-log Pₙ = n·(-log p)`
is small while `c log c ∼ √n·log√n` is large. The constant process is the
cleanest witness and is the one formalized here.

## Why the per-block form cannot be repaired with an `O(c)` overhead

Numerically (`/tmp` probe during this session) even the textbook CT-style
overhead `c·log(n/c)` is insufficient as `p → 1`. The genuine Cover–Thomas
LZ optimality `c log c ∼ -log Pₙ` is an **a.s.-eventual** (ergodic / AEP)
statement, *not* a per-block `∀ n ∀ ω` inequality. The correct repaired
honest input is an a.s.-eventual rate bound (the structure
`IsLZ78AchievabilityZivUpperBound` already used downstream), not the per-block
`IsLZ78ZivCombinatorialCoreOverhead`. The latter should be retired as a defect.

## What this file publishes

A *genuine, unconditional* refutation `not_isLZ78ZivCombinatorialCoreOverhead`
exhibiting the constant process as a witness that the overhead core is false.
No `sorry`, no load-bearing hypothesis.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

/-! ## §1. The constant process witness -/

/-- **Constant process on `Unit`**: shift `T = id`, observable `X ≡ a`. Every
observation is `a`, so every block is the constant tuple `a^n`. With the Dirac
measure on `Unit`, the block law is `δ_{a^n}` and `Pₙ = 1`. This is the
witness that `IsLZ78ZivCombinatorialCoreOverhead` is false. -/
noncomputable def constProcess {α : Type*} [MeasurableSpace α] (a : α) :
    StationaryProcess (Measure.dirac (() : Unit)) α where
  T := id
  X := fun _ => a
  measurePreserving := MeasurePreserving.id _
  measurable_X := measurable_const

@[simp] lemma constProcess_blockRV {α : Type*} [MeasurableSpace α] (a : α)
    (n : ℕ) (ω : Unit) :
    (constProcess a).blockRV n ω = fun _ : Fin n => a := by
  funext i
  simp [StationaryProcess.blockRV, StationaryProcess.obs, constProcess]

/-- The block law of the constant process is the Dirac measure at the constant
tuple `a^n`, so its real mass at `{a^n}` is `1`. -/
lemma constProcess_blockProb_eq_one {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : α) (n : ℕ) :
    ((Measure.dirac (() : Unit)).map ((constProcess a).blockRV n)).real
        {(constProcess a).blockRV n ()}
      = 1 := by
  rw [Measure.map_dirac (() : Unit)]
  rw [measureReal_def, Measure.dirac_apply' _ (measurableSet_singleton _)]
  simp

/-! ## §2. The refutation -/

/-- **Phrase count of the constant-`true` length-16 block is `5`** (genuine,
by computation): `blockRV 16 ()` is `true^16`, whose longest-prefix LZ parse
emits the `5` distinct phrases `[t], [t,t], [t,t,t], [t,t,t,t]` (lengths
`1+2+3+4 = 10 ≤ 16`, plus the partial fifth). -/
lemma constProcess_blockRV16_count :
    (lz78PhraseStrings
        (List.ofFn ((constProcess (true : Bool)).blockRV 16 ()))).length = 5 := by
  rw [constProcess_blockRV, List.ofFn_const]
  decide

/-- **`IsLZ78ZivCombinatorialCoreOverhead` is mathematically FALSE** (genuine,
unconditional refutation).

The constant process on `Unit` with observable `≡ true` over `Bool` is a
witness: at `n = 16`, `ω = ()` the block is `true^16` with `Pₙ = 1`
(`-log Pₙ = 0`), and the LZ parse emits `c = 5` distinct phrases
(`constProcess_blockRV16_count`). The overhead core then asserts
`5·log 5 ≤ 0 + 5·log 3`, i.e. `log 5 ≤ log 3`, which is false.

**Consequence.** The per-block `∀ n ∀ ω` form `IsLZ78ZivCombinatorialCoreOverhead`
(`LZ78ZivTreeNode.lean`) cannot be discharged — it is unsatisfiable, so every
downstream headline assuming it (`isLZ78AchievabilityZivUpperBound_distinctOverhead`,
`lz78_two_sided_optimality_distinct_ziv_overhead_core_wired`) is vacuously
conditioned for *some* processes (it does hold for many, but not all). The
docstring's claim that the overhead form is "mathematically TRUE" (justified by
the single `(a,a,b)` check) is incorrect: it misses the `√n`-growth-of-`c` vs
`O(c)`-overhead family witnessed here. The genuine Cover–Thomas LZ optimality
`c log c ∼ -log Pₙ` is an a.s.-eventual (ergodic/AEP) statement, not a per-block
universal inequality; the honest input should be an a.s.-eventual rate bound. -/
theorem not_isLZ78ZivCombinatorialCoreOverhead :
    ¬ IsLZ78ZivCombinatorialCoreOverhead
        (Measure.dirac (() : Unit)) (constProcess (true : Bool)) := by
  intro hcore
  -- instantiate at n = 16, ω = ().
  have h := hcore 16 ()
  -- rewrite the count to 5 and the overhead block.
  rw [constProcess_blockRV16_count] at h
  -- `Pₙ = 1`, so `-log Pₙ = 0`.
  have hPn : ((Measure.dirac (() : Unit)).map
      ((constProcess (true : Bool)).blockRV 16)).real
        {(constProcess (true : Bool)).blockRV 16 ()} = 1 :=
    constProcess_blockProb_eq_one (true : Bool) 16
  rw [hPn, Real.log_one, neg_zero, zero_add] at h
  -- `lz78ZivOverhead = c · log(|Bool|+1) = 5 · log 3`.
  have hov : lz78ZivOverhead (Measure.dirac (() : Unit))
      (constProcess (true : Bool)) 16 ()
      = ((5 : ℕ) : ℝ) * Real.log 3 := by
    rw [lz78ZivOverhead, constProcess_blockRV16_count,
        show (Fintype.card Bool : ℝ) + 1 = 3 by rw [Fintype.card_bool]; norm_num]
  rw [hov] at h
  -- now `h : (5:ℝ) * log 5 ≤ (5:ℝ) * log 3`; but `log 5 > log 3`, contradiction.
  have hlog : Real.log 3 < Real.log 5 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have h5 : ((5 : ℕ) : ℝ) = 5 := by norm_num
  rw [h5] at h
  nlinarith [hlog]

end InformationTheory.Shannon
