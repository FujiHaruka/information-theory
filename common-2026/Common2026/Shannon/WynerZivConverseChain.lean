import Common2026.Shannon.WynerZiv
import Common2026.Shannon.WynerZivConverse
import Common2026.Shannon.RateDistortionConverseNLetter

/-!
# Wyner–Ziv converse n-letter chain rule body (T3-D wave7, L-WZ2 chain discharge)

This file refines `wyner_ziv_converse_n_letter` from `WynerZivConverse.lean` by
discharging its monolithic `h_rate_bound` hypothesis into a **chain** of smaller
ingredients, in the same style as `rate_distortion_converse_n_letter_singleLetter`
(`RateDistortionConverseNLetter.lean:260`):

1. **Per-letter Wyner–Ziv feasibility** (`wzRate_le_perLetter_objective`) — for
   each coordinate `i`, the per-letter rate function `R_WZ(D_i)` is bounded by
   the per-letter Wyner–Ziv objective `I(X_i; U_i) − I(Y_i; U_i)` of a feasible
   joint. **Hypothesis pass-through**: per-letter feasibility (Markov + marginal
   + distortion at `D_i`) is bundled into the input.
2. **Csiszár's sum identity** (`csiszar_sum_identity_statement`) — the rate
   inequality `∑ (I(X_i; U_i) − I(Y_i; U_i)) ≤ log M` on `toReal`. **Hypothesis
   pass-through**: the proof of the identity itself (n-letter chain rule on
   conditional mutual information + Fano + side-info chain) is deferred to a
   separate seed.
3. **n-way Jensen + antitonicity** (`wzRate_jensen_antitone`) — `R_WZ(D) ≤ (1/n)
   ∑ R_WZ(D_i)`. **Hypothesis pass-through**: combined Jensen on `R_WZ` convexity
   in `D` plus antitonicity. Inherits the `h_jensen_antitone` shape from
   `RateDistortionConverseNLetter` and re-exports it on the Wyner–Ziv side.

Composing these three ingredients gives the n-letter Wyner–Ziv converse on
`toReal`:
```
wynerZivRatePmf U P_XY d D ≤ Real.log M / n.
```

The proof is purely the chain assembly (pass-through + `mul_le_mul_of_nonneg_left`
+ `Finset.sum_le_sum`). All deep information-theoretic content is factored out
as the three hypotheses above.

## Scope

* New theorems live in `InformationTheory.Shannon` namespace, suffixed with
  `_chain` to distinguish from the monolithic `wyner_ziv_converse_n_letter`.
* Existing `WynerZivConverse.lean` is **not** edited — this is a parallel
  publish, so the existing pass-through theorem remains the public API for
  downstream Phase D wrappers.
* The bundling shape `h_jensen_antitone` reuses the exact contract of
  `RateDistortionConverseNLetter`, allowing future cross-discharge.

## 撤退ライン

* **L-WZ2-A**: Per-letter feasibility is supplied as `h_perLetter` (an n-tuple
  of per-letter objective bounds). Discharge requires constructing the per-letter
  auxiliary `U_i := (M, Y^{<i}, Y^{>i})` and verifying Markov / marginal /
  distortion — ~150-250 lines, deferred.
* **L-WZ2-B**: Csiszár sum identity is supplied as `h_csiszar`. Discharge
  requires n-letter conditional MI chain rule + Fano-style block MI bound —
  ~200-300 lines, deferred.
* **L-WZ3**: Jensen + antitonicity is supplied as `h_jensen_antitone` (same
  shape as RD-converse-n-letter). Discharge needs `R_WZ(D)` convexity in `D`
  — ~100-150 lines, deferred (separate seed).
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

section ConverseChain

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-! ## Per-letter feasibility hypothesis bundle -/

/-- Per-letter Wyner–Ziv feasibility statement. For each `i : Fin n`, the
per-letter rate function `R_WZ(D_i)` (at threshold `D_i := ∫ d(X_i, X̂_i) ∂μ`)
is bounded above by the per-letter Wyner–Ziv objective `I(X_i; U_i) − I(Y_i; U_i)`
on `ℝ` (i.e., already `toReal`-converted). This is the conclusion shape of the
per-letter feasibility argument; the actual construction of `U_i` and the
verification of Markov / marginal / distortion are deferred to a separate seed.

The `Real` value `wzPerLetterObjective i` is the realized per-letter objective,
serving as the per-letter upper bound on `R_WZ(D_i)`. -/
structure WZPerLetterBound
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {n : ℕ}
    (D_arr : Fin n → ℝ) (wzPerLetterObjective : Fin n → ℝ) : Prop where
  perLetter :
    ∀ i : Fin n, wynerZivRatePmf U P_XY d (D_arr i) ≤ wzPerLetterObjective i

/-- Csiszár sum identity statement: the sum of per-letter Wyner–Ziv objectives
is bounded above by `Real.log M`. This bundles together:

* the n-letter conditional MI chain rule, and
* the Fano-side block MI bound `(I(X^n; M | Y^n)).toReal ≤ Real.log M`.

The realized per-letter objectives `wzPerLetterObjective i` are the LHS of the
identity; the RHS is `Real.log M`. The actual identity proof (chain rule
manipulation + Fano) is deferred. -/
def CsiszarSumIdentity
    {n : ℕ} (wzPerLetterObjective : Fin n → ℝ) (M : ℕ) : Prop :=
  ∑ i : Fin n, wzPerLetterObjective i ≤ Real.log (M : ℝ)

/-- n-way Jensen + antitonicity statement for the Wyner–Ziv rate function on
`toReal`. Mirrors the bundling shape of `h_jensen_antitone` from
`RateDistortionConverseNLetter`. -/
def WZJensenAntitone
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {n : ℕ}
    (D : ℝ) (D_arr : Fin n → ℝ) : Prop :=
  wynerZivRatePmf U P_XY d D
    ≤ (1 / (n : ℝ)) * ∑ i : Fin n, wynerZivRatePmf U P_XY d (D_arr i)

/-! ## Main chain assembly -/

/-- **Wyner–Ziv converse — n-letter chain assembly** (L-WZ2 chain discharge).

Composes per-letter feasibility + Csiszár sum identity + Jensen-antitonicity
into the final rate bound `R_WZ(D) ≤ Real.log M / n`. This is the explicit
chain assembly form of `wyner_ziv_converse_n_letter` (whose `h_rate_bound`
hypothesis can now be discharged by exhibiting `wzPerLetterObjective` and
proving the three component hypotheses separately). -/
theorem wyner_ziv_converse_chain
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) {n : ℕ} (hn : 0 < n)
    (M : ℕ)
    (D : ℝ) (D_arr : Fin n → ℝ)
    (wzPerLetterObjective : Fin n → ℝ)
    (h_perLetter : WZPerLetterBound U P_XY d D_arr wzPerLetterObjective)
    (h_csiszar : CsiszarSumIdentity wzPerLetterObjective M)
    (h_jensen_antitone : WZJensenAntitone U P_XY d D D_arr) :
    wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ) := by
  -- Step 0: 1/n ≥ 0.
  have hn_pos_R : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_one_div_n_nn : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  -- Step 1: per-letter pointwise bound R_WZ(D_i) ≤ wzPerLetterObjective i.
  have h_sum_le :
      ∑ i : Fin n, wynerZivRatePmf U P_XY d (D_arr i)
        ≤ ∑ i : Fin n, wzPerLetterObjective i :=
    Finset.sum_le_sum (fun i _ => h_perLetter.perLetter i)
  -- Step 2: chain on Real side.
  calc wynerZivRatePmf U P_XY d D
      ≤ (1 / (n : ℝ)) * ∑ i : Fin n, wynerZivRatePmf U P_XY d (D_arr i) :=
        h_jensen_antitone
    _ ≤ (1 / (n : ℝ)) * ∑ i : Fin n, wzPerLetterObjective i :=
        mul_le_mul_of_nonneg_left h_sum_le h_one_div_n_nn
    _ ≤ (1 / (n : ℝ)) * Real.log (M : ℝ) :=
        mul_le_mul_of_nonneg_left h_csiszar h_one_div_n_nn
    _ = Real.log (M : ℝ) / (n : ℝ) := by ring

/-- **Wyner–Ziv converse — n-letter chain form on a block code**. Specializes
`wyner_ziv_converse_chain` to a `WynerZivCode M n α β γ` with expected block
distortion `≤ D`, exposing the same `wyner_ziv_converse_n_letter` signature but
with the monolithic `h_rate_bound` replaced by the three component hypotheses. -/
theorem wyner_ziv_converse_chain_block
    [MeasurableSpace γ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    {M n : ℕ} (hn : 0 < n)
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (dN : DistortionFn α γ) (c : WynerZivCode M n α β γ)
    (_h_dist : c.expectedBlockDistortion μ dN ≤ D)
    (D_arr : Fin n → ℝ)
    (wzPerLetterObjective : Fin n → ℝ)
    (h_perLetter : WZPerLetterBound U P_XY d D_arr wzPerLetterObjective)
    (h_csiszar : CsiszarSumIdentity wzPerLetterObjective M)
    (h_jensen_antitone : WZJensenAntitone U P_XY d D D_arr) :
    wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ) :=
  wyner_ziv_converse_chain U P_XY d hn M D D_arr wzPerLetterObjective
    h_perLetter h_csiszar h_jensen_antitone

/-! ## Auxiliary objective definitions and sum manipulations -/

section ObjectiveSupport

variable {α' β' γ' : Type*}

/-- **Per-letter Wyner–Ziv objective on `Real`** — pointwise difference
`I(X_i; U_i) − I(Y_i; U_i)` (the per-letter form of the WZ objective). The
realized per-letter objective is the difference of the two per-letter mutual
informations (already `toReal`-converted by the caller). -/
def wzObjectiveReal {n : ℕ} (Ixu Iyu : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Ixu i - Iyu i

/-- The per-letter objective decomposes as `Ixu i − Iyu i` by definition. -/
@[simp] lemma wzObjectiveReal_apply {n : ℕ} (Ixu Iyu : Fin n → ℝ) (i : Fin n) :
    wzObjectiveReal Ixu Iyu i = Ixu i - Iyu i := rfl

/-- Sum of per-letter Wyner–Ziv objectives equals `∑ I(X_i; U_i) − ∑ I(Y_i; U_i)`. -/
lemma sum_wzObjectiveReal {n : ℕ} (Ixu Iyu : Fin n → ℝ) :
    ∑ i : Fin n, wzObjectiveReal Ixu Iyu i
      = (∑ i : Fin n, Ixu i) - (∑ i : Fin n, Iyu i) := by
  simp only [wzObjectiveReal_apply, Finset.sum_sub_distrib]

/-- Per-letter Wyner–Ziv objective is bounded above by `Ixu i` (when `Iyu i ≥ 0`,
which holds for any mutual information on the simplex side). -/
lemma wzObjectiveReal_le_Ixu {n : ℕ} (Ixu Iyu : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ Iyu i) (i : Fin n) :
    wzObjectiveReal Ixu Iyu i ≤ Ixu i := by
  simp only [wzObjectiveReal_apply, sub_le_iff_le_add]
  linarith [h_nonneg i]

/-- Sum of per-letter Wyner–Ziv objectives is bounded above by `∑ Ixu i` when
`Iyu i ≥ 0` for all `i`. -/
lemma sum_wzObjectiveReal_le_sum_Ixu {n : ℕ} (Ixu Iyu : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ Iyu i) :
    ∑ i : Fin n, wzObjectiveReal Ixu Iyu i ≤ ∑ i : Fin n, Ixu i :=
  Finset.sum_le_sum (fun i _ => wzObjectiveReal_le_Ixu Ixu Iyu h_nonneg i)

end ObjectiveSupport

/-! ## Csiszár sum identity — statement-level conversions

These lemmas convert between equivalent statement forms of Csiszár's sum
identity (sum-of-differences ≤ block MI ≤ log M), bridging the chain
assembly's `CsiszarSumIdentity` predicate and the more granular forms used in
discharge plans.
-/

section CsiszarStatementBridge

variable {α' β' γ' : Type*}

/-- **Csiszár statement form A → main predicate**. If the sum of per-letter
objectives is bounded by the block MI and the block MI is bounded by `log M`,
the bundled `CsiszarSumIdentity` predicate holds. -/
lemma csiszarSumIdentity_of_blockMI_chain
    {n : ℕ} (wzObj : Fin n → ℝ) (M : ℕ) (blockMI : ℝ)
    (h_sum_le_block : ∑ i : Fin n, wzObj i ≤ blockMI)
    (h_block_le_log : blockMI ≤ Real.log (M : ℝ)) :
    CsiszarSumIdentity wzObj M :=
  le_trans h_sum_le_block h_block_le_log

/-- **Csiszár statement form B → main predicate**. Equivalent statement using
the `wzObjectiveReal` decomposition: if `∑ I(X_i; U_i) − ∑ I(Y_i; U_i)`
is bounded by `log M` directly, the bundled predicate holds. -/
lemma csiszarSumIdentity_of_diff_sum
    {n : ℕ} (Ixu Iyu : Fin n → ℝ) (M : ℕ)
    (h : (∑ i : Fin n, Ixu i) - (∑ i : Fin n, Iyu i) ≤ Real.log (M : ℝ)) :
    CsiszarSumIdentity (wzObjectiveReal Ixu Iyu) M := by
  show ∑ i : Fin n, wzObjectiveReal Ixu Iyu i ≤ Real.log (M : ℝ)
  rw [sum_wzObjectiveReal]; exact h

/-- **Csiszár sum identity from pointwise per-letter MI bounds + Iyu nonneg**.
If `∑ Ixu i ≤ Real.log M` (block MI bound + chain rule give this directly)
and `Iyu i ≥ 0` for all `i`, then the sum of per-letter objectives is bounded
by `log M` via the slack `−∑ Iyu i ≤ 0`. Useful for discharging the predicate
without explicitly computing the block MI of the side-info-conditioned chain. -/
lemma csiszarSumIdentity_of_Ixu_block_bound
    {n : ℕ} (Ixu Iyu : Fin n → ℝ) (M : ℕ)
    (h_Iyu_nn : ∀ i, 0 ≤ Iyu i)
    (h_Ixu_block : ∑ i : Fin n, Ixu i ≤ Real.log (M : ℝ)) :
    CsiszarSumIdentity (wzObjectiveReal Ixu Iyu) M := by
  show ∑ i : Fin n, wzObjectiveReal Ixu Iyu i ≤ Real.log (M : ℝ)
  refine le_trans ?_ h_Ixu_block
  exact sum_wzObjectiveReal_le_sum_Ixu Ixu Iyu h_Iyu_nn

end CsiszarStatementBridge

/-! ## Jensen-antitone statement support -/

section JensenAntitoneBridge

variable {α' β' γ' : Type*}

/-- **`WZJensenAntitone` from RD-style bundle**. Given the canonical
`(R(D)).toReal ≤ (1/n) ∑ (R(D_i)).toReal` shape on `wynerZivRatePmf`, the
bundled `WZJensenAntitone` predicate holds. This is a re-export forwarder
that allows seeds discharging the convexity to plug into the chain assembly
using the same shape as `RateDistortionConverseNLetter`. -/
lemma wzJensenAntitone_of_pointwise
    (P_XY : α' × β' → ℝ) (d : α' → γ' → ℝ) {n : ℕ}
    (D : ℝ) (D_arr : Fin n → ℝ)
    (U : Type*) [Fintype U] [MeasurableSpace U]
    [Fintype α'] [Fintype β']
    [MeasurableSpace α'] [MeasurableSpace β']
    (h : wynerZivRatePmf U P_XY d D
          ≤ (1 / (n : ℝ)) * ∑ i : Fin n, wynerZivRatePmf U P_XY d (D_arr i)) :
    WZJensenAntitone U P_XY d D D_arr := h

/-- **`WZJensenAntitone` is monotone in the LHS rate**: if a smaller value
already satisfies the bound, so does any value below it. (Trivial bridge,
exposes the monotonic-LHS shape often needed when chaining with antitonicity.) -/
lemma wzJensenAntitone_of_le
    (P_XY : α' × β' → ℝ) (d : α' → γ' → ℝ) {n : ℕ}
    (D : ℝ) (D_arr : Fin n → ℝ)
    (U : Type*) [Fintype U] [MeasurableSpace U]
    [Fintype α'] [Fintype β']
    [MeasurableSpace α'] [MeasurableSpace β']
    {bound : ℝ}
    (h_lhs_le : wynerZivRatePmf U P_XY d D ≤ bound)
    (h_bound_le : bound
        ≤ (1 / (n : ℝ)) * ∑ i : Fin n, wynerZivRatePmf U P_XY d (D_arr i)) :
    WZJensenAntitone U P_XY d D D_arr :=
  le_trans h_lhs_le h_bound_le

end JensenAntitoneBridge

/-! ## Per-letter feasibility — statement support -/

section PerLetterSupport

variable {α' β' γ' : Type*}

/-- **`WZPerLetterBound` from a pointwise list of inequalities**. The
`structure`-wrapped predicate is created from an `∀ i, R_WZ(D_i) ≤ obj_i`
hypothesis. -/
def wzPerLetterBound_of_forall
    (U : Type*) [Fintype U] [MeasurableSpace U]
    [Fintype α'] [Fintype β']
    [MeasurableSpace α'] [MeasurableSpace β']
    (P_XY : α' × β' → ℝ) (d : α' → γ' → ℝ) {n : ℕ}
    (D_arr : Fin n → ℝ) (wzPerLetterObjective : Fin n → ℝ)
    (h : ∀ i : Fin n,
          wynerZivRatePmf U P_XY d (D_arr i) ≤ wzPerLetterObjective i) :
    WZPerLetterBound U P_XY d D_arr wzPerLetterObjective :=
  ⟨h⟩

/-- **`WZPerLetterBound` weakened via larger objective**. If the per-letter
objective is replaced by a larger sequence pointwise, the predicate still
holds. (Useful when the chain assembly's chained objective bounds need to
be slackened to fit the bundled `CsiszarSumIdentity`.) -/
lemma wzPerLetterBound_mono
    (U : Type*) [Fintype U] [MeasurableSpace U]
    [Fintype α'] [Fintype β']
    [MeasurableSpace α'] [MeasurableSpace β']
    (P_XY : α' × β' → ℝ) (d : α' → γ' → ℝ) {n : ℕ}
    (D_arr : Fin n → ℝ) (obj₁ obj₂ : Fin n → ℝ)
    (h_le : ∀ i, obj₁ i ≤ obj₂ i)
    (h₁ : WZPerLetterBound U P_XY d D_arr obj₁) :
    WZPerLetterBound U P_XY d D_arr obj₂ :=
  ⟨fun i => le_trans (h₁.perLetter i) (h_le i)⟩

/-- **`WZPerLetterBound` from constant pointwise bound**. If a single value
`C` upper-bounds every per-letter rate, the predicate with the constant
objective `fun _ => C` holds. -/
lemma wzPerLetterBound_const
    (U : Type*) [Fintype U] [MeasurableSpace U]
    [Fintype α'] [Fintype β']
    [MeasurableSpace α'] [MeasurableSpace β']
    (P_XY : α' × β' → ℝ) (d : α' → γ' → ℝ) {n : ℕ}
    (D_arr : Fin n → ℝ) (C : ℝ)
    (h : ∀ i : Fin n, wynerZivRatePmf U P_XY d (D_arr i) ≤ C) :
    WZPerLetterBound U P_XY d D_arr (fun _ => C) :=
  ⟨h⟩

end PerLetterSupport

/-! ## Chain-rule conditional MI statement-level identities

These lemmas package Csiszár-style telescoping identities and chain-rule
rearrangements as `Real`-side statement-pass forms. They keep the chain
assembly's `CsiszarSumIdentity` predicate compatible with both `mutualInfo`-
and `condMutualInfo`-based discharges. Discharging via the actual conditional
MI chain rule (`MIChainRule.mutualInfo_chain_rule_fin`) is left to a separate
seed; these statement-level bridges allow plug-in either way.
-/

section ChainRuleStatementBridge

variable {α' β' γ' : Type*}

/-- **Telescope identity → block MI bound**. If a sequence
`condMI : Fin n → ℝ` decomposes via a chain rule into `block ≤ ∑ condMI`
(`h_chain`), and the block is bounded by `Real.log M` (`h_block_le_log`),
then `∑ condMI` is bounded by `Real.log M` too. Used to flatten the
Csiszár-style chain rule into the bundled `CsiszarSumIdentity` shape. -/
lemma sum_condMI_le_log_of_chain
    {n : ℕ} (condMI : Fin n → ℝ) (M : ℕ) (block : ℝ)
    (h_chain : ∑ i : Fin n, condMI i ≤ block)
    (h_block_le_log : block ≤ Real.log (M : ℝ)) :
    ∑ i : Fin n, condMI i ≤ Real.log (M : ℝ) :=
  le_trans h_chain h_block_le_log

/-- **Per-letter pointwise → per-letter sum**. The conditional MI chain rule
hypothesis `(MIChainRule)` produces a per-letter form
`∑ condMI ≤ block`. From per-letter inequalities `wzObj i ≤ condMI i`, the
sum form follows. -/
lemma sum_wzObj_le_block_of_perLetter_condMI
    {n : ℕ} (wzObj condMI : Fin n → ℝ) (block : ℝ)
    (h_perLetter : ∀ i, wzObj i ≤ condMI i)
    (h_chain : ∑ i : Fin n, condMI i ≤ block) :
    ∑ i : Fin n, wzObj i ≤ block :=
  le_trans (Finset.sum_le_sum (fun i _ => h_perLetter i)) h_chain

/-- **Chain rule + Fano → CsiszarSumIdentity (composed)**. The end-to-end
chain rule discharge: per-letter `wzObj` is bounded pointwise by per-letter
`condMI`, the conditional MI chain rule yields `∑ condMI ≤ block`, and the
block is bounded by `Real.log M`. The bundled `CsiszarSumIdentity`
predicate then holds. -/
lemma csiszarSumIdentity_of_perLetter_chain_fano
    {n : ℕ} (wzObj condMI : Fin n → ℝ) (M : ℕ) (block : ℝ)
    (h_perLetter : ∀ i, wzObj i ≤ condMI i)
    (h_chain : ∑ i : Fin n, condMI i ≤ block)
    (h_fano : block ≤ Real.log (M : ℝ)) :
    CsiszarSumIdentity wzObj M :=
  csiszarSumIdentity_of_blockMI_chain wzObj M block
    (sum_wzObj_le_block_of_perLetter_condMI wzObj condMI block h_perLetter h_chain)
    h_fano

/-- **Symmetric difference re-arrangement**. The Wyner–Ziv per-letter objective
`I(X_i; U_i) − I(Y_i; U_i)` can be rewritten as `condMI` over `U_i` given
`Y_i` (when the auxiliary `U_i := (M, Y^{<i}, Y^{>i})` is chosen). This
statement-level re-arrangement allows the chain assembly to interchangeably
use the difference form `wzObjectiveReal Ixu Iyu` and the conditional form
`condMI`. -/
lemma wzObjectiveReal_eq_condMI_of_decomposition
    {n : ℕ} (Ixu Iyu condMI : Fin n → ℝ)
    (h_decomp : ∀ i, Ixu i - Iyu i = condMI i) :
    wzObjectiveReal Ixu Iyu = condMI := by
  funext i
  simp only [wzObjectiveReal_apply]
  exact h_decomp i

/-- **Symmetric per-letter equality reformulation**. If `Ixu i − Iyu i = condMI i`
for all `i`, then the sum-of-objectives equals the sum-of-condMIs. -/
lemma sum_wzObjectiveReal_eq_sum_condMI
    {n : ℕ} (Ixu Iyu condMI : Fin n → ℝ)
    (h_decomp : ∀ i, Ixu i - Iyu i = condMI i) :
    ∑ i : Fin n, wzObjectiveReal Ixu Iyu i
      = ∑ i : Fin n, condMI i := by
  rw [wzObjectiveReal_eq_condMI_of_decomposition Ixu Iyu condMI h_decomp]

end ChainRuleStatementBridge

/-! ## Composite discharge — single-shot composition

A single composite lemma that bundles per-letter feasibility + chain rule +
Fano + Jensen into the final `wynerZivRatePmf ≤ log M / n` form, exposing
all five component hypotheses (per-letter ≤ condMI, chain ≤ block, Fano,
Jensen, antitonicity) as separate inputs.
-/

section CompositeDischarge

variable {α' β' γ' : Type*}
variable [Fintype α'] [Fintype β']
  [MeasurableSpace α'] [MeasurableSpace β']

/-- **Composite chain discharge** — the most decomposed form of the chain
assembly. Replaces the bundled `CsiszarSumIdentity` with its three underlying
ingredients (per-letter ≤ condMI, chain telescope, Fano-side block bound) and
plugs into `wyner_ziv_converse_chain`. -/
theorem wyner_ziv_converse_chain_composite
    (U : Type*) [Fintype U] [MeasurableSpace U]
    (P_XY : α' × β' → ℝ) (d : α' → γ' → ℝ) {n : ℕ} (hn : 0 < n)
    (M : ℕ)
    (D : ℝ) (D_arr : Fin n → ℝ)
    (wzPerLetterObjective : Fin n → ℝ)
    (h_perLetter : WZPerLetterBound U P_XY d D_arr wzPerLetterObjective)
    (condMI : Fin n → ℝ) (block : ℝ)
    (h_perLetter_le_condMI :
      ∀ i, wzPerLetterObjective i ≤ condMI i)
    (h_chain : ∑ i : Fin n, condMI i ≤ block)
    (h_fano : block ≤ Real.log (M : ℝ))
    (h_jensen_antitone : WZJensenAntitone U P_XY d D D_arr) :
    wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ) := by
  have h_csiszar : CsiszarSumIdentity wzPerLetterObjective M :=
    csiszarSumIdentity_of_perLetter_chain_fano wzPerLetterObjective condMI M block
      h_perLetter_le_condMI h_chain h_fano
  exact wyner_ziv_converse_chain U P_XY d hn M D D_arr wzPerLetterObjective
    h_perLetter h_csiszar h_jensen_antitone

end CompositeDischarge

/-! ## Bridge to existing `wyner_ziv_converse_n_letter` -/

/-- The chain assembly `wyner_ziv_converse_chain` discharges the
`h_rate_bound` hypothesis of `wyner_ziv_converse_n_letter`. Given the three
component hypotheses, the existing monolithic publish is recovered. -/
theorem wyner_ziv_converse_n_letter_chain
    [MeasurableSpace γ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    {M n : ℕ} (hn : 0 < n)
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (dN : DistortionFn α γ) (c : WynerZivCode M n α β γ)
    (h_dist : c.expectedBlockDistortion μ dN ≤ D)
    (D_arr : Fin n → ℝ)
    (wzPerLetterObjective : Fin n → ℝ)
    (h_perLetter : WZPerLetterBound U P_XY d D_arr wzPerLetterObjective)
    (h_csiszar : CsiszarSumIdentity wzPerLetterObjective M)
    (h_jensen_antitone : WZJensenAntitone U P_XY d D D_arr) :
    wynerZivRatePmf U P_XY d D ≤ Real.log (M : ℝ) / (n : ℝ) :=
  wyner_ziv_converse_n_letter U P_XY d D hn μ dN c h_dist trivial trivial
    (wyner_ziv_converse_chain_block U P_XY d D hn μ dN c h_dist D_arr
      wzPerLetterObjective h_perLetter h_csiszar h_jensen_antitone)

end ConverseChain

/-! ## Existence form — chain assembly contrapositive

The chain assembly induces the `R < R_WZ(D)` impossibility form. If the
per-letter / Csiszár / Jensen ingredients all hold, then no infinite sequence
of block codes can achieve rate below `R_WZ(D)` at distortion `D`. This is
the existence-form companion of `wyner_ziv_converse_existence` in
`WynerZivConverse.lean`, lifted to the chain assembly setting.
-/

section ExistenceForm

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Chain assembly → existence-form converse**. The contrapositive packaging
of `wyner_ziv_converse_chain`: if `R < R_WZ(D)`, then for any `N` there exists
some `n ≥ N` such that no `WynerZivCode M n α β γ` with `M ≤ exp(n · R)` can
satisfy the chain assembly's three component hypotheses simultaneously with
distortion `≤ D`. The negation statement is supplied as `h_impossibility`,
matching the shape of `wyner_ziv_converse_existence`. -/
theorem wyner_ziv_converse_chain_existence
    [MeasurableSpace γ]
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (_h_R_lt : R < wynerZivRatePmf U P_XY d D)
    (dN : DistortionFn α γ)
    (h_impossibility :
      ¬ ∃ N : ℕ, ∀ n ≥ N,
          ∃ (M : ℕ) (c : WynerZivCode M n α β γ),
            (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
              ∧ c.expectedBlockDistortion μ dN ≤ D) :
    ¬ ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ) (c : WynerZivCode M n α β γ),
          (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
            ∧ c.expectedBlockDistortion μ dN ≤ D := h_impossibility

end ExistenceForm

/-! ## Tendsto wrapper using chain assembly

Reuses the existing `wyner_ziv_tendsto` wrapper but discharges the converse
side via the chain assembly. This is the public entry-point downstream code
should call when both ach and chain-based converse are available.
-/

section TendstoWrapper

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Wyner–Ziv rate-equality wrapper (chain-discharge form)**. Given:

* `h_ach`: achievability `wynerZivRatePmf(D) ≤ R` (from achievability seed);
* `h_chain_conv`: converse rate inequality `R ≤ wynerZivRatePmf(D)` produced
  by the chain assembly (cf. `wyner_ziv_converse_chain`),

the rate `R` equals `wynerZivRatePmf(D)`. Pure forwarder to
`wyner_ziv_tendsto`. -/
theorem wyner_ziv_tendsto_chain
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (h_ach : wynerZivRatePmf U P_XY d D ≤ R)
    (h_chain_conv : R ≤ wynerZivRatePmf U P_XY d D) :
    R = wynerZivRatePmf U P_XY d D :=
  wyner_ziv_tendsto U P_XY d D R h_ach h_chain_conv

end TendstoWrapper

end InformationTheory.Shannon
