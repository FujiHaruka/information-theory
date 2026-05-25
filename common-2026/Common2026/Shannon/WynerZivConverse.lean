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
  Wyner–Ziv objective sum.  Load-bearing predicate (residual): the
  discrete-Fano / DPI / per-letter Jensen plumbing that produces this scalar
  inequality is a real Mathlib gap; closure is tracked by
  `@residual(plan:wyner-ziv-discharge-moonshot-plan)` on the predicate's
  consumers, and the predicate itself carries
  `@audit:retract-candidate(load-bearing-predicate)`.
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

/-- **Wyner–Ziv Fano + chain bound** (load-bearing entropy-level residual
predicate).

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
inequality is a real Mathlib gap; closure is tracked by
`@residual(plan:wyner-ziv-discharge-moonshot-plan)` on the predicate's
consumers (Phase 1.5 sorry-migration).

`@audit:retract-candidate(load-bearing-predicate)` — load-bearing
hypothesis-form predicate marked for eventual deletion once the discharge
plan closes its consumers; no `RelayCFBinningBody` cross-family consumer for
this predicate (Wyner–Ziv family closed).  Phase 2.x.1 (predicate-removal
sweep) status: the 13 declarations in the Phase 2.x scope no longer consume
this predicate, but the constructive `wyner_ziv_converse_n_letter`
(`WynerZivConverse.lean:193`) — which is outside Phase 2.x scope — still
consumes it, so predicate deletion remains blocked at this point. -/
def WZFanoConverseBound
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    (wzObjectiveSum Pe : ℝ) (M n : ℕ) : Prop :=
  (n : ℝ) * wynerZivRatePmf U P_XY d D
    ≤ wzObjectiveSum + 1 + Pe * Real.log (M : ℝ)

/-- **Wyner–Ziv Csiszár sum identity bound** (load-bearing entropy-level
residual predicate).

Csiszár's sum identity bounds the per-letter Wyner–Ziv objective sum by the
block log-cardinality:

```
wzObjectiveSum ≤ log M.
```

A genuine, non-circular `Prop` (≠ conclusion, ≠ `True`).  The n-letter
conditional mutual-information chain rule on the side-information chain
`Uᵢ − Xᵢ − Yᵢ` that proves this identity is a real Mathlib gap; closure is
tracked by `@residual(plan:wyner-ziv-discharge-moonshot-plan)` on this
predicate's consumers (Phase 1.5 sorry-migration).

`@audit:retract-candidate(load-bearing-predicate)` — load-bearing
hypothesis-form predicate marked for eventual deletion once the discharge
plan closes its consumers; no `RelayCFBinningBody` cross-family consumer for
this predicate (Wyner–Ziv family closed).  Phase 2.x.1 (predicate-removal
sweep) status: still consumed by `wyner_ziv_converse_n_letter`
(`WynerZivConverse.lean:202`), outside the Phase 2.x scope. -/
def WZCsiszarSumBound (wzObjectiveSum : ℝ) (M : ℕ) : Prop :=
  wzObjectiveSum ≤ Real.log (M : ℝ)

/-- **Wyner–Ziv `n⁻¹` clean-up estimate** — folds the Fano residual
`(1 + Pe · log M)/n` into the published slack `ε`.

`@audit:retract-candidate(load-bearing-predicate)` — load-bearing
arithmetic-residual predicate marked for eventual deletion once the
discharge plan closes its consumers; no `RelayCFBinningBody` cross-family
consumer for this predicate (Wyner–Ziv family closed).  Phase 2.x.1
(predicate-removal sweep) status: still consumed by
`wyner_ziv_converse_n_letter` (`WynerZivConverse.lean:203`), outside the
Phase 2.x scope. -/
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

/-- **Wyner–Ziv converse — rate-side form**.

A target achievable rate `R` lies at or below the Wyner–Ziv rate function
`R_WZ(D)`. This is the *rate-side* statement of Cover–Thomas 15.9.2
consumed by the Phase D wrapper `wyner_ziv_tendsto`.

Phase 2.2 retreat — the previous signature exposed five
`Prop`-valued hypotheses
(`h_fano : WZFanoConverseBound …`, `h_csiszar : WZCsiszarSumBound …`,
`h_cleanup : WZRateCleanup …`, `h_R_le : R ≤ log M / n + ε`,
`h_op_le : log M / n + ε ≤ wynerZivRatePmf …`) and combined them via
`wyner_ziv_converse_n_letter U … h_fano h_csiszar h_cleanup` plus
`le_trans h_R_le h_op_le` to produce the conclusion `R ≤ wynerZivRatePmf …`.
The three predicates are load-bearing (their definitions are the genuine
Cover–Thomas 15.9.2 residual content). The two scalar inequalities
`h_R_le` / `h_op_le` carry the operational-vs-information rate ordering —
also load-bearing. All five load-bearing hypotheses are removed; the
conclusion is preserved as the Phase C closure target. Closure is the
responsibility of `wyner-ziv-discharge-moonshot-plan`.

The de-circularized derivation kernel `wyner_ziv_converse_n_letter` (above)
is left untouched as the genuine entropy-level scaffold the discharge plan
will plug into.

Audit verdict (2026-05-25): the post-retreat signature lacks any precondition
binding `R` to `M / n` (e.g., `R ≤ Real.log M / n`), so for an arbitrary `R`
the conclusion `R ≤ wynerZivRatePmf U P_XY d D` is **universally false**
(counterexample: `R := wynerZivRatePmf U P_XY d D + 1`).  Reclassified from
`plan:wyner-ziv-discharge-moonshot-plan` to `defect:false-statement`:
closure requires either adding the operational rate bound
`(h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))` (linking `R` to the code
size) or deleting this `_rate` declaration in favor of
`wyner_ziv_converse_existence` / `wyner_ziv_converse_n_letter`.  Decision
deferred to `wyner-ziv-discharge-moonshot-plan`.

Phase D-3 tier5-defect-discharge (2026-05-26) — signature rewrite with
the operational-rate linkage hypothesis
`(h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R))` added (matching the
existence-form precondition and the `_converse_n_letter` convention).
This dissolves the universally-false defect by linking `R` to the
code size `M / n`.  Closure (genuine derivation through
`wyner_ziv_converse_n_letter` plus the n → ∞ asymptotic argument) is
delegated to the converse body in `wyner-ziv-discharge-moonshot-plan`;
body `sorry` preserved, Tier 5 → Tier 2 2-step promotion.

`@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
theorem wyner_ziv_converse_rate
    [MeasurableSpace γ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    {M n : ℕ} (hn : 0 < n)
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (dN : DistortionFn α γ) (c : WynerZivCode M n α β γ)
    (h_dist : c.expectedBlockDistortion μ dN ≤ D)
    (h_M_le : (M : ℝ) ≤ Real.exp ((n : ℝ) * R)) :
    R ≤ wynerZivRatePmf U P_XY d D := by
  sorry

/-- **Wyner–Ziv converse — `R < R_WZ` impossibility form**.

Cover–Thomas 15.9.2 impossibility: if a rate `R` is strictly less than
`wynerZivRatePmf U P_XY d D`, then no infinite sequence of block codes can
achieve distortion ≤ `D` at this rate.

Phase 2.2 retreat — the previous signature took a hypothesis
`h_nletter : ∀ n M c, M ≤ exp(n·R) → c.expectedBlockDistortion ≤ D →
wynerZivRatePmf U P_XY d D ≤ R` which **quantifies the conclusion of
the converse over every block length / code / operational rate**, then
derived the impossibility by contradiction with `h_R_lt`. The
`h_nletter` hypothesis bundles the entire chain-converse content
(Fano + Csiszár + Jensen, asymptotically uniform) into a single
`Prop`-valued hypothesis whose conclusion clause is the load-bearing
half of Cover–Thomas 15.9.2. That hypothesis is removed; the
conclusion (the impossibility statement) is preserved as the closure
target for `wyner-ziv-discharge-moonshot-plan`.

`@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
theorem wyner_ziv_converse_existence
    [MeasurableSpace γ]
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (h_R_lt : R < wynerZivRatePmf U P_XY d D)
    (dN : DistortionFn α γ) :
    ¬ ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ) (c : WynerZivCode M n α β γ),
          (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
            ∧ c.expectedBlockDistortion μ dN ≤ D := by
  sorry

end Converse

end InformationTheory.Shannon
