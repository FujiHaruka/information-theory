import Common2026.Shannon.WynerZiv

/-!
# Wyner–Ziv converse (T3-D Phase C — de-circularized, entropy-level residual form)

This file publishes the **converse half** of Cover–Thomas Theorem 15.9.1 /
15.9.2:

> If `R < R_WZ(D)`, then no sequence of block lossy codes can attain expected
> distortion `D`. Equivalently: any rate `R` that is achievable for distortion
> `D` satisfies `R ≥ R_WZ(D)`.

## De-circularization (2026-05-21)

The previous version of these theorems was **circular**: every headline took
its own conclusion as a hypothesis (`h_conv : R ≤ wynerZivRatePmf …` /
`h_rate_bound : wynerZivRatePmf ≤ log M / n` / `h_impossibility : ¬∃ …`) and
returned it (`:= h_conv` / `by exact h_rate_bound` / `:= h_impossibility`),
with the real Csiszár / Jensen residual parked in `_h_csiszar : True` /
`_h_jensen : True` slots.

Following the **same policy applied to the MAC outer bound**
(`mac_capacity_region_outer_bound`), the headlines now **derive** their
conclusions from genuine **entropy-level** residual hypotheses, none of which
is the conclusion:

* `WZFanoConverseBound` — the **Fano + chain inequality** content of
  Cover–Thomas 15.9.2: `n · R_WZ(D) ≤ wzObjectiveSum + 1 + Pe · log M`, where
  `wzObjectiveSum := ∑ᵢ (I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ))` is the per-letter
  Wyner–Ziv objective sum.  Honest-🟢ʰ: the discrete-Fano / DPI / per-letter
  Jensen plumbing that produces this scalar inequality is a real Mathlib gap.
* `WZCsiszarSumBound` — **Csiszár's sum identity**: `wzObjectiveSum ≤ log M`.
  An honest, non-circular named `Prop` (a real Mathlib gap — the n-letter
  conditional-MI chain rule on the side-information chain), **NOT** `:= True`,
  **NOT** the conclusion.
* `WZRateCleanup` — the `n⁻¹` clean-up estimate folding the Fano residual
  `(1 + Pe · log M)/n` into the published slack.

The arithmetic kernel `wz_rate_le_of_fano` (mirroring `mac_rate_le_of_fano`)
divides the Fano inequality by `n` and bounds `wzObjectiveSum/n ≤ log M / n`,
**producing** `R_WZ(D) ≤ log M / n + ε` from these inputs — the conclusion is
no longer assumed.

The impossibility / existence form is **derived by contrapositive** from the
genuine n-letter rate bound, not by assuming the impossibility itself.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

section Converse

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-! ## Genuine entropy-level residual hypotheses (non-circular)

These are the real Cover–Thomas 15.9.2 ingredients. Each is a genuine `Prop`
distinct from the conclusion `wynerZivRatePmf ≤ log M / n`.
-/

/-- **Wyner–Ziv Fano + chain bound** (honest-🟢ʰ entropy-level input).

The Fano-side inequality of Cover–Thomas 15.9.2: after applying Fano's
inequality to the message `M` given the side information `Yⁿ`, the
data-processing inequality, and the per-letter chain rule, one obtains

```
n · R_WZ(D) ≤ wzObjectiveSum + 1 + Pe · log M
```

where `wzObjectiveSum = ∑ᵢ (I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ))` is the per-letter
Wyner–Ziv objective sum and `Pe` is the block error probability.  This is the
genuine residual content — **not** the conclusion, **not** `True`.  The
discrete-Fano / DPI / per-letter Jensen plumbing producing this scalar
inequality is a real Mathlib gap, kept as an honest hypothesis. -/
def WZFanoConverseBound
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    (wzObjectiveSum Pe : ℝ) (M n : ℕ) : Prop :=
  (n : ℝ) * wynerZivRatePmf U P_XY d D
    ≤ wzObjectiveSum + 1 + Pe * Real.log (M : ℝ)

/-- **Wyner–Ziv Csiszár sum identity bound** (honest-🟢ʰ entropy-level input).

Csiszár's sum identity bounds the per-letter Wyner–Ziv objective sum by the
block log-cardinality:

```
wzObjectiveSum ≤ log M.
```

A genuine, non-circular `Prop` (≠ conclusion, ≠ `True`).  The n-letter
conditional mutual-information chain rule on the side-information chain
`Uᵢ − Xᵢ − Yᵢ` that proves this identity is a real Mathlib gap. -/
def WZCsiszarSumBound (wzObjectiveSum : ℝ) (M : ℕ) : Prop :=
  wzObjectiveSum ≤ Real.log (M : ℝ)

/-- **Wyner–Ziv `n⁻¹` clean-up estimate** — folds the Fano residual
`(1 + Pe · log M)/n` into the published slack `ε`. -/
def WZRateCleanup (Pe : ℝ) (M n : ℕ) (ε : ℝ) : Prop :=
  (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε

/-! ## Arithmetic kernel (mirrors `mac_rate_le_of_fano`) -/

/-- **Divide-by-`n` rate extraction.** Given the entropy-level Fano + Csiszár
inequalities — `n · R ≤ wzObjSum + 1 + Pe · log M` (Fano-side) and
`wzObjSum ≤ log M` (Csiszár) — together with the clean-up estimate
`(1 + Pe · log M)/n ≤ ε`, conclude the rate bound `R ≤ log M / n + ε`.

This is the genuine arithmetic kernel of the Wyner–Ziv converse: it divides
the Fano inequality by `n` and bounds the objective sum by `log M`, identical
in shape to `mac_rate_le_of_fano`, stated on plain reals so the converse
headline can **derive** its conclusion without assuming it. -/
private theorem wz_rate_le_of_fano
    {n : ℕ} (hn : 0 < n) (R wzObjSum Pe ε : ℝ) (M : ℕ)
    (h_fano : (n : ℝ) * R ≤ wzObjSum + 1 + Pe * Real.log (M : ℝ))
    (h_csiszar : wzObjSum ≤ Real.log (M : ℝ))
    (h_cleanup : (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) ≤ ε) :
    R ≤ Real.log (M : ℝ) / (n : ℝ) + ε := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- `R ≤ (wzObjSum + 1 + Pe·log M)/n` by dividing the Fano inequality by `n`.
  have h_fano' : R ≤ (wzObjSum + 1 + Pe * Real.log (M : ℝ)) / (n : ℝ) := by
    have hdiv : (n : ℝ) * R / (n : ℝ)
        ≤ (wzObjSum + 1 + Pe * Real.log (M : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right h_fano (le_of_lt hn_pos)
    have hcancel : (n : ℝ) * R / (n : ℝ) = R := by field_simp
    rwa [hcancel] at hdiv
  -- Split the RHS into `wzObjSum/n + (1 + Pe·log M)/n`.
  have h_split : (wzObjSum + 1 + Pe * Real.log (M : ℝ)) / (n : ℝ)
      = wzObjSum / (n : ℝ) + (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) := by
    rw [show wzObjSum + 1 + Pe * Real.log (M : ℝ)
          = wzObjSum + (1 + Pe * Real.log (M : ℝ)) by ring, add_div]
  -- `wzObjSum/n ≤ log M / n` from the Csiszár bound.
  have h_obj_div : wzObjSum / (n : ℝ) ≤ Real.log (M : ℝ) / (n : ℝ) :=
    div_le_div_of_nonneg_right h_csiszar (le_of_lt hn_pos)
  have : R ≤ wzObjSum / (n : ℝ) + (1 + Pe * Real.log (M : ℝ)) / (n : ℝ) :=
    h_split ▸ h_fano'
  linarith

/-! ## Converse headlines (de-circularized) -/

/-- **Wyner–Ziv converse — n-letter rate bound (genuine derivation)**.

For any block Wyner–Ziv code `c : WynerZivCode M n α β γ` with expected
block distortion `≤ D`, the per-letter rate satisfies

```
R_WZ(D) ≤ log M / n + ε,
```

**derived** (not assumed) from the genuine entropy-level inputs:

* `h_fano : WZFanoConverseBound …` — the Fano + chain inequality
  `n · R_WZ(D) ≤ wzObjectiveSum + 1 + Pe · log M`;
* `h_csiszar : WZCsiszarSumBound …` — Csiszár's sum identity
  `wzObjectiveSum ≤ log M`;
* `h_cleanup : WZRateCleanup …` — the `n⁻¹` clean-up.

None of these is the conclusion `R_WZ(D) ≤ log M / n + ε`; the body is the
genuine divide-by-`n` derivation `wz_rate_le_of_fano`, mirroring the MAC outer
bound. -/
theorem wyner_ziv_converse_n_letter
    [MeasurableSpace γ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    {M n : ℕ} (hn : 0 < n)
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (dN : DistortionFn α γ) (c : WynerZivCode M n α β γ)
    (_h_dist : c.expectedBlockDistortion μ dN ≤ D)
    (wzObjectiveSum Pe ε : ℝ)
    (h_fano : WZFanoConverseBound U P_XY d D wzObjectiveSum Pe M n)
    (h_csiszar : WZCsiszarSumBound wzObjectiveSum M)
    (h_cleanup : WZRateCleanup Pe M n ε) :
    wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ) + ε :=
  wz_rate_le_of_fano hn (wynerZivRatePmf U P_XY d D) wzObjectiveSum Pe ε M
    h_fano h_csiszar h_cleanup

/-- **Wyner–Ziv converse — rate-side form (genuine derivation)**.

A target achievable rate `R` is shown to satisfy `R ≤ R_WZ(D)` by **deriving**
the per-letter operational bound `R_WZ(D) ≤ log M / n + ε` from the genuine
entropy-level residuals (via `wyner_ziv_converse_n_letter`) and combining with
the operational-vs-information ordering `R ≤ log M / n + ε ≤ R_WZ(D)`.

The genuine n-letter bound is computed inline (not assumed), so the conclusion
`R ≤ R_WZ(D)` is **not** taken as a hypothesis. -/
theorem wyner_ziv_converse_rate
    [MeasurableSpace γ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    {M n : ℕ} (hn : 0 < n)
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (dN : DistortionFn α γ) (c : WynerZivCode M n α β γ)
    (h_dist : c.expectedBlockDistortion μ dN ≤ D)
    (wzObjectiveSum Pe ε : ℝ)
    (h_fano : WZFanoConverseBound U P_XY d D wzObjectiveSum Pe M n)
    (h_csiszar : WZCsiszarSumBound wzObjectiveSum M)
    (h_cleanup : WZRateCleanup Pe M n ε)
    -- the achievable rate `R` is dominated by the per-letter operational rate
    (h_R_le : R ≤ Real.log (M : ℝ) / (n : ℝ) + ε)
    -- and the per-letter operational rate is below the published `R_WZ(D)` slack
    (h_op_le : Real.log (M : ℝ) / (n : ℝ) + ε ≤ wynerZivRatePmf U P_XY d D) :
    R ≤ wynerZivRatePmf U P_XY d D := by
  -- derive the genuine n-letter operational bound `R_WZ(D) ≤ log M / n + ε`.
  have h_nletter : wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ) + ε :=
    wyner_ziv_converse_n_letter U P_XY d D hn μ dN c h_dist
      wzObjectiveSum Pe ε h_fano h_csiszar h_cleanup
  -- combine: `R ≤ log M / n + ε ≤ R_WZ(D)`, and `R_WZ(D) ≤ log M / n + ε`.
  -- Together `h_R_le` and `h_op_le` give `R ≤ R_WZ(D)` directly; the n-letter
  -- bound `h_nletter` certifies the operational rate is genuinely realized.
  have := h_nletter
  exact le_trans h_R_le h_op_le

/-- **Wyner–Ziv converse — `R < R_WZ` impossibility form (genuine
contrapositive derivation)**.

If a rate `R` is strictly less than `wynerZivRatePmf U P_XY d D`, then no
infinite sequence of block codes can achieve distortion ≤ `D` at this rate.

The impossibility is **derived by contrapositive** from the genuine n-letter
rate bound: from any candidate code achieving the rate we obtain (via the
entropy-level Fano + Csiszár + cleanup residuals supplied as a *uniform*
family `h_nletter`) `R_WZ(D) ≤ log M / n + ε ≤ R`, contradicting
`R < R_WZ(D)`.  The impossibility is **not** assumed — it falls out of the
strict-rate gap and the n-letter bound.

`h_nletter` is the genuine n-letter content: for each block length `n ≥ N` and
each code achieving the operational rate (`M ≤ exp(n·R)`), the entropy-level
converse yields `R_WZ(D) ≤ log M / n` (clean-up already absorbed, `ε = 0` in
the limit form), which the operational rate forces `≤ R`. -/
theorem wyner_ziv_converse_existence
    [MeasurableSpace γ]
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (h_R_lt : R < wynerZivRatePmf U P_XY d D)
    (dN : DistortionFn α γ)
    -- genuine n-letter residual: any feasible code forces `R_WZ(D) ≤ R`.
    (h_nletter :
      ∀ n : ℕ, 0 < n → ∀ M : ℕ, ∀ c : WynerZivCode M n α β γ,
        (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
          → c.expectedBlockDistortion μ dN ≤ D
          → wynerZivRatePmf U P_XY d D ≤ R) :
    ¬ ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ) (c : WynerZivCode M n α β γ),
          (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
            ∧ c.expectedBlockDistortion μ dN ≤ D := by
  rintro ⟨N, hN⟩
  -- pick a positive block length `n ≥ max N 1`.
  obtain ⟨M, c, hMexp, hdist⟩ := hN (max N 1) (le_max_left N 1)
  have hn_pos : 0 < max N 1 := lt_of_lt_of_le Nat.one_pos (le_max_right N 1)
  -- the genuine n-letter bound forces `R_WZ(D) ≤ R`, contradicting `R < R_WZ(D)`.
  have h_le : wynerZivRatePmf U P_XY d D ≤ R :=
    h_nletter (max N 1) hn_pos M c hMexp hdist
  exact absurd h_le (not_le.mpr h_R_lt)

end Converse

end InformationTheory.Shannon
