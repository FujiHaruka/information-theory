import InformationTheory.Shannon.WynerZiv.Operational
import InformationTheory.Shannon.WynerZiv.FactorizableRate
import InformationTheory.Shannon.WynerZiv.ConverseGateway

/-!
# Wyner–Ziv converse (operational lower bound on the rate)

This file provides the converse leg of the Wyner–Ziv operational main theorem
(Cover–Thomas Thm 15.9.1): every achievable rate `R` at distortion `D` for the
i.i.d. source `P_XY` with decoder side information satisfies
`R_WZ(D) ≤ R`, where `R_WZ` is the factorisable Wyner–Ziv rate function
`wynerZivRateFactorizable`.

## Proof outline (steps 6–10 of the plan)

For a block Wyner–Ziv code with deterministic encoder `J : (Fin n → α) → Fin M`
and side-information decoder on an i.i.d. source `(Xⁿ, Yⁿ)`:

6. `n·R ≥ H(J) ≥ I(J; Xⁿ) − I(J; Yⁿ)` (deterministic encoder + data processing).
7. Chain rule identifies the single-letter auxiliary `Uᵢ := (J, Y^{i-1})`, giving
   `I(J; Xⁿ) − I(J; Yⁿ) = ∑ᵢ [I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ)]` after cross-term cancellation.
8. Cross terms cancel via the heterogeneous Csiszár sum identity
   (`csiszar_sum_identity_hetero`, proved sorry-free).
9. Per-letter feasibility + convexity of `R_WZ` (`wynerZivRateFactorizable_convex_in_D`)
   give `∑ᵢ [I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ)] ≥ ∑ᵢ R_WZ(Dᵢ) ≥ n · R_WZ((1/n) ∑ Dᵢ)`.
10. Antitonicity (`wynerZivRateFactorizable_antitone`) reaches `n · R_WZ(D)`.

The per-letter measure-form mutual informations are landed onto the pmf-form
`wzMutualInfoXU` / `wzMutualInfoYU` via the proved bridges
`wzMutualInfoXU_eq_mutualInfo` / `wzMutualInfoYU_eq_mutualInfo`.

## Auxiliary-alphabet quantification (honesty note)

The single-letterized auxiliary `Uᵢ := (J, Y^{i-1})` constructed in the proof has a
type that varies with `i` and `n`. The headline `wynerZivRateFactorizable U` is stated
for a *fixed* caller-supplied auxiliary type `U`. The two are reconciled by the
Carathéodory cardinality bound `|U| ≤ |α| + 1`: the rate-optimal Wyner–Ziv auxiliary
can be taken with at most `|α| + 1` symbols, so it embeds into any `U` with
`|α| + 1 ≤ |U|`, yielding a `U`-valued feasible point whose objective bounds the
`sInf`. Hence the converse is stated with the sizing precondition
`Fintype.card α + 1 ≤ Fintype.card U`.

This precondition is **necessary**: the statement is *false* for a fixed `U` that is
too small. Concretely, for a source whose optimal auxiliary genuinely needs `|α| + 1`
symbols, choosing `U = Fin |α|` restricts the `sInf` to a strictly larger value than
the achievable `R = R_WZ(D)`, so `wynerZivRateFactorizable (Fin |α|) ≤ R` fails while
`R` is achievable. The unconditional `∀ U` form of the converse is therefore *not*
true-as-framed; the sizing precondition is a genuine (non-load-bearing) regularity
condition on the auxiliary alphabet, not a bundling of the proof core.

The proof core (single-letterization + Carathéodory reduction) is left as
`sorry + @residual(plan:wyner-ziv-main-plan)`; the cardinality reduction proper is
deferred to the separate plan `wz-auxiliary-cardinality-bound`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {α β γ U : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Fintype U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]

/-! ## `n`-letter single-letterized converse -/

/-- **Wyner–Ziv converse, `n`-letter single-letterized form.**

For a block Wyner–Ziv code `c` with a measurable deterministic encoder / decoder on
an i.i.d. source of `(X, Y)` pairs (mutual independence `hindep` + identical marginals
`hlaw = P_XY`), whose expected block distortion is at most `D`, the factorisable
Wyner–Ziv rate is bounded by the block log-cardinality rate:
```
R_WZ(D) ≤ (1/n) · log M.
```

The independence / i.i.d. preconditions (`hindep` + `hlaw`) are genuine regularity
preconditions (the conclusion is false without them, mirroring
`rate_distortion_converse_n_letter_singleLetter`). The sizing precondition
`hU_card : |α| + 1 ≤ |U|` is the Carathéodory largeness constraint that makes the
statement true for the fixed auxiliary type `U` (see the module docstring); it is a
non-load-bearing precondition on the auxiliary alphabet.

The proof (single-letterization via `bc_input_singleletterize` + cross-term
cancellation via `csiszar_sum_identity_hetero` + convexity/antitone of `R_WZ` +
the pmf↔measure bridges + Carathéodory reduction) is the converse core.

@residual(plan:wyner-ziv-main-plan) -/
theorem wyner_ziv_converse_n_letter_singleLetter
    {Ω : Type*} [MeasurableSpace Ω]
    {M n : ℕ} [NeZero M] (hn : 0 < n)
    (c : WynerZivCode M n α β γ)
    (hencoder : Measurable c.encoder) (hdecoder : Measurable c.decoder)
    (d : DistortionFn α γ)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindep : iIndepFun (fun i ω ↦ (Xs i ω, Ys i ω)) μ)
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (hlaw : ∀ i, μ.map (fun ω ↦ (Xs i ω, Ys i ω)) = P_XY)
    (hU_card : Fintype.card α + 1 ≤ Fintype.card U)
    {D : ℝ}
    (hD : c.expectedBlockDistortion P_XY d ≤ D) :
    wynerZivRateFactorizable U (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D
      ≤ (1 / (n : ℝ)) * Real.log (M : ℝ) := by
  sorry

/-! ## Operational converse headline -/

/-- **Wyner–Ziv converse** (Cover–Thomas Thm 15.9.1, operational lower bound).

If rate `R` is achievable at distortion `D` for the i.i.d. source `P_XY` with decoder
side information, then the factorisable Wyner–Ziv rate satisfies `R_WZ(D) ≤ R`.

The auxiliary alphabet `U` is a fixed caller-supplied type; the sizing precondition
`hU_card : |α| + 1 ≤ |U|` is the Carathéodory largeness constraint (see the module
docstring — the unconditional `∀ U` form is false-as-framed, so this precondition is
necessary and honest, not load-bearing).

The proof reduces `WynerZivAchievable` to a sequence of block codes, applies the
`n`-letter single-letterized converse `wyner_ziv_converse_n_letter_singleLetter` to
each, and passes to the limit `(1/n) log (M n) → R` (with the distortion slack
`D + ε → D` absorbed by antitonicity of `R_WZ`).

@residual(plan:wyner-ziv-main-plan) -/
@[entry_point]
theorem wyner_ziv_converse
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (hU_card : Fintype.card α + 1 ≤ Fintype.card U)
    (h_ach : WynerZivAchievable P_XY d R D) :
    wynerZivRateFactorizable U (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D ≤ R := by
  sorry

end InformationTheory.Shannon
