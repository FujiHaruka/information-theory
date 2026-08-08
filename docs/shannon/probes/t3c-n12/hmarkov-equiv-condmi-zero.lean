-- Probe: machine-checks that from the unconditional chain rule alone, the conclusion of
-- `plainDirectionalBound_eq_condFree` is equivalent (for `t ≠ 0`) to `I(C; Z | X) = 0`, the
-- information-theoretic form of that theorem's `hmarkov` hypothesis.
-- Audit line: A4-c of `bc-t3c-n12-audit.md` §4.2.
-- Re-run: lake env lean docs/shannon/probes/t3c-n12/hmarkov-equiv-condmi-zero.lean

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

-- A4-c: 無条件の連鎖律だけから、`plainDirectionalBound_eq_condFree` の結論 (`t ≠ 0`) は
--       `I(C; Z | X) = 0` = `hmarkov` の情報量版と同値である
example (IXCZ ICZ IXZgC IXZ ICZgX t : ℝ) (ht : t ≠ 0)
    (chain1 : IXCZ = ICZ + IXZgC) (chain2 : IXCZ = IXZ + ICZgX) :
    (t * IXZgC = t * (IXZ - ICZ)) ↔ ICZgX = 0 := by
  constructor
  · intro h
    have h' : IXZgC = IXZ - ICZ := by
      have := mul_left_cancel₀ ht h
      linarith
    linarith
  · intro h
    have hEq : IXZgC = IXZ - ICZ := by linarith
    rw [hEq]
