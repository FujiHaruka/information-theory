import InformationTheory.Shannon.WynerZiv.Converse.Prelim
import InformationTheory.Shannon.WynerZiv.Converse.SingleLetter
import InformationTheory.Shannon.WynerZiv.Converse.Headline

/-!
# Wyner–Ziv converse (operational lower bound on the rate)

This file provides the converse leg of the Wyner–Ziv operational main theorem
(Cover–Thomas): every achievable rate `R` at distortion `D` for the
i.i.d. source `P_XY` with decoder side information satisfies
`R_WZ(D) ≤ R`, where `R_WZ` is the reshaped Wyner–Ziv rate function
`wynerZivRate` — the infimum of the objective over feasible factorizable points
at *every* finite auxiliary alphabet (`FactorizableRate.lean` §10).

## Proof outline (steps 6–10 of the plan)

For a block Wyner–Ziv code with deterministic encoder `J : (Fin n → α) → Fin M`
and side-information decoder on an i.i.d. source `(Xⁿ, Yⁿ)`:

6. `n·R ≥ H(J) ≥ I(J; Xⁿ) − I(J; Yⁿ)` (deterministic encoder + data processing).
7. The single-letter auxiliary is `Uᵢ := (J, Y_{\i})` — the encoder output `J`
   together with *all the other* side-information symbols `Y_{\i} = (Yⱼ)_{j≠i}`.
   The full block `Yⁿ = (Y_{\i}, Yᵢ)` is forced onto `Uᵢ` because the per-letter
   reconstruction `X̂ᵢ = (decoder (J, Yⁿ))ᵢ` depends on the *entire* `Yⁿ`; a
   one-sided `Y^{i-1}` auxiliary is therefore ruled out (distortion-hostile).
8. Memorylessness gives the per-letter Markov chain `Uᵢ − Xᵢ − Yᵢ`
   (`wz_perletter_markov`, proved sorry-free from `iIndepFun`). Together with the
   *conditional* mutual-information chain — **not** the heterogeneous Csiszár sum
   identity, which is orphaned on this route —
   `∑ᵢ [I(Xᵢ; Uᵢ) − I(Yᵢ; Uᵢ)] = ∑ᵢ I(Xᵢ; Uᵢ | Yᵢ)` (Markov ⟹ `I(Yᵢ; Uᵢ | Xᵢ) = 0`)
   `= ∑ᵢ I(Xᵢ; J | Yⁿ)` (`(Y_{\i}, Yᵢ) = Yⁿ` + memoryless collapse)
   `≤ I(Xⁿ; J | Yⁿ) = I(J; Xⁿ) − I(J; Yⁿ)` (conditional chain rule + `J − Xⁿ − Yⁿ`).
9. Per-letter feasibility (each empirical `(Xᵢ, Yᵢ, Uᵢ)` is `IsWynerZivFactorizable`
   via the Markov chain) lands each objective as a value of `wzRateValueSet` at its
   own budget `Dᵢ`; time-sharing (`wzRateValueSet_avg_mem`) averages them.
10. The average distortion budget `(1/n) ∑ᵢ Dᵢ ≤ D` (from `hD`) with
    `wzRateValueSet_mono_in_D` and the reshaped landing `wynerZivRate_le_of_feasible`
    reaches `R_WZ(D) ≤ (1/n)(I(J; Xⁿ) − I(J; Yⁿ)) ≤ (1/n) log M`.

The per-letter measure-form mutual informations are landed onto the pmf-form
`wzMutualInfoXU` / `wzMutualInfoYU` via the proved bridges
`wzMutualInfoXU_eq_mutualInfo` / `wzMutualInfoYU_eq_mutualInfo`.

## Auxiliary-alphabet quantification (reshape rationale)

The single-letterized auxiliary `Uᵢ := (J, Y_{\i})` constructed in the proof has a
type that varies with `i` and `n` and a cardinality that grows with the block length.
The fixed-`U` rate `wynerZivRateFactorizable U` cannot receive such an auxiliary
without a Carathéodory cardinality reduction (embedding the rate-optimal auxiliary into
a `U` with `|α| + 1 ≤ |U|`) — a hard support lemma plus a shared-decoder `n`-ary
Jensen on the converse's critical path.

The **reshape** (proposal A) removes both: the converse concludes against
`wynerZivRate`, the infimum of the objective over feasible factorizable points at
*every* finite auxiliary alphabet `Fin k` at once (`FactorizableRate.lean` §10). A
large single-letterization auxiliary of any finite type (here `Uᵢ` of type
`Fin M × ({j // j ≠ i} → β)`) then lands *directly* as a feasible point of the
reshaped infimum via `wynerZivRate_le_of_feasible`, with no cardinality bound and no
support lemma. The reshaped statement is `∀`-clean: it carries no auxiliary sizing
precondition.

Non-degeneracy (junk-`sInf` guard): `wynerZivRate = sInf (wzRateValueSet …)` and, in
`ℝ`, `sInf ∅ = 0`. The union-of-images form of `wzRateValueSet` injects no junk (empty
constraints contribute the empty image), and the objective's data-processing
non-negativity `I(X;U) − I(Y;U) ≥ 0` (Markov chain `U − X − Y`) bounds the value set
below by `0` uniformly in the auxiliary size (`wzRateValueSet_bddBelow_of_pmf`), so the
`sInf` is a genuine non-negative rate, not a vacuous `≤ 0`.

The single-letterization sub-lemmas — per-letter factorizability
`wz_perletter_factorizable` (with its empirical-factorizable crux
`wz_perletter_empirical_factorizable`), the conditional-MI collapse / rate atoms, and
the distortion average `wz_perletter_distortion_avg` — are now closed sorryAx-free; the
data-processing non-negativity `wzObjective_nonneg_of_factorizable` is likewise
discharged genuinely (sorryAx-free) via the measure-form DPI + the pmf↔measure bridges +
a discrete Markov-chain realization (`wzFactorizable_isMarkovChain`), so
`wzRateValueSet_bddBelow_of_pmf` (the reshaped rate's non-degeneracy `BddBelow` guard) is
likewise unconditional. The single-letterization witness `wz_converse_feasible_point` is
itself closed sorryAx-free (machine-checked `#print axioms`). The L1 Carathéodory fixed-`K`
identification `wynerZivRate_eq_factorizable_finK` and its core `wz_support_reduce` (the
support-cardinality reduction to `Fin (|α|+3)`) are now closed sorry-free, so the entire
converse headline `wyner_ziv_converse` is sorryAx-free.

## Module structure

Umbrella of the `Shannon/WynerZiv/Converse/` family, re-exporting:

* `Converse.Prelim` — the `n`-letter converse, the reshaped-rate non-degeneracy, the local
  pmf → measure realization, and the append form of `IsMarkovChain`.
* `Converse.SingleLetter` — the per-letter Markov gateway atom, the single-letterization
  sub-lemmas, and the single-letter rate bound `wynerZivRate_le_of_code`.
* `Converse.Headline` — the endpoint right-continuity infrastructure and the operational
  converse headline `wyner_ziv_converse`.
-/
