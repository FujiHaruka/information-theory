-- Probe: machine-checks that the hypothesis `he : e * log 2 ≤ binEntropy p` of
-- `binEntropy_binConv_sub_binEntropy_le` is the `x = 1/2` pointwise instance of that theorem's
-- own conclusion, and that dropping `he` makes the statement false (`p = 1/4`, `e = 1`, `x = 1/2`).
-- Audit lines: A4-a (first example) + A4-b (second example) of `bc-t3c-n12-audit.md` §4.2.
-- Re-run: lake env lean docs/shannon/probes/t3c-n12/he-is-conclusion-pointwise.lean

import InformationTheory.Shannon.BroadcastChannel.MoreCapableBinary

-- A4-a: `he` は結論の `x = 1/2` 各点版そのものである
example (p e : ℝ)
    (hconcl : Real.binEntropy ((1 / 2) * (1 - p) + (1 - 1 / 2) * p) - Real.binEntropy p
      ≤ (1 - e) * Real.binEntropy (1 / 2 : ℝ)) :
    e * Real.log 2 ≤ Real.binEntropy p := by
  have hx : ((1 : ℝ) / 2) * (1 - p) + (1 - 1 / 2) * p = 2⁻¹ := by ring
  have hhalf : Real.binEntropy ((1 : ℝ) / 2) = Real.log 2 := by
    rw [show ((1 : ℝ) / 2) = 2⁻¹ by norm_num]; exact Real.binEntropy_two_inv
  rw [hx, hhalf, Real.binEntropy_two_inv] at hconcl
  nlinarith [hconcl]

-- A4-b: `he` を落とすと命題は偽になる (`p = 1/4`, `e = 1`, `x = 1/2`)
example : ¬ (∀ p e x : ℝ, 0 < p → p < 1 / 2 → 0 ≤ x → x ≤ 1 →
    Real.binEntropy (x * (1 - p) + (1 - x) * p) - Real.binEntropy p
      ≤ (1 - e) * Real.binEntropy x) := by
  intro h
  have hinst := h (1 / 4) 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hx : ((1 : ℝ) / 2) * (1 - 1 / 4) + (1 - 1 / 2) * (1 / 4) = 2⁻¹ := by norm_num
  have hhalf : Real.binEntropy ((1 : ℝ) / 2) = Real.log 2 := by
    rw [show ((1 : ℝ) / 2) = 2⁻¹ by norm_num]; exact Real.binEntropy_two_inv
  rw [hx, hhalf, Real.binEntropy_two_inv] at hinst
  have hlt : Real.binEntropy ((1 : ℝ) / 4) < Real.log 2 :=
    Real.binEntropy_lt_log_two.2 (by norm_num)
  nlinarith [hinst, hlt]
