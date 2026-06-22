import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.RateDistortion.Converse
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Order.Compact

/-!
# Rate-distortion achievability — structure and pmf-direct `R(D)`

The structural layer for the achievability half of Cover–Thomas 10.5: block
lossy codes and the pmf-direct rate-distortion function with its compactness /
continuity / minimizer-existence apparatus.

## Main definitions

* `DistortionFn α β` — a single-symbol distortion `α → β → ℝ≥0`.
* `blockDistortion d n x y` — the block distortion `(1/n) ∑ d(xᵢ, yᵢ)`.
* `LossyCode M n α β` — a block lossy code (deterministic encoder + decoder).
* `LossyCode.expectedBlockDistortion` — its expected block distortion.
* `expectedDistortionPmf d q` — pmf-form expected distortion `∑ q(a,b) · d(a,b)`.
* `marginalFst` / `marginalSnd` — the marginals of a joint pmf.
* `RDConstraint P_X d D` — the feasible joint-pmf set.
* `mutualInfoPmf q` — mutual information in entropy form `H(fst) + H(snd) − H(q)`.
* `rateDistortionFunctionPmf P_X d D` — the pmf-direct rate-distortion function.

## Main statements

* `RDConstraint_isClosed` / `RDConstraint_isCompact` — closedness and compactness
  of the feasible set.
* `rateDistortionFunctionPmf_attained` — the infimum is attained on a non-empty
  feasible set.

## Implementation notes

* Mutual information is defined in the `negMulLog` entropy form
  `H(X) + H(Y) − H(X, Y)`: it is a finite sum of `Real.negMulLog`, hence
  continuous on all of `α × β → ℝ` (`Real.continuous_negMulLog`). The KL / log-ratio
  form is avoided because its continuity breaks at zero marginals.
* `RDConstraint` is a subset of `Set (α × β → ℝ)`: an affine constraint on the
  standard simplex of `α × β`, closed and convex, so `IsCompact.exists_isMinOn`
  applies directly.
-/

namespace InformationTheory.Shannon

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## Distortion function -/

/-- A single-symbol distortion function `d : α → β → ℝ≥0`. -/
abbrev DistortionFn (α β : Type*) := α → β → NNReal

/-- The block distortion `dⁿ((xᵢ), (yᵢ)) := (1/n) ∑ d(xᵢ, yᵢ)`, valued in `ℝ`. -/
noncomputable def blockDistortion {α β : Type*} (d : DistortionFn α β) (n : ℕ)
    (x : Fin n → α) (y : Fin n → β) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ((d (x i) (y i) : NNReal) : ℝ)

theorem blockDistortion_nonneg
    {α β : Type*} (d : DistortionFn α β) (n : ℕ)
    (x : Fin n → α) (y : Fin n → β) :
    0 ≤ blockDistortion d n x y := by
  unfold blockDistortion
  refine mul_nonneg ?_ ?_
  · by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · exact div_nonneg zero_le_one (le_of_lt (lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn)))
  · exact Finset.sum_nonneg (fun i _ ↦ NNReal.coe_nonneg _)

/-! ## Block lossy code -/

/-- A **block lossy code** of length `n` with `M` codewords over source alphabet `α`
and reconstruction alphabet `β`: a deterministic encoder `(Fin n → α) → Fin M` and
decoder `Fin M → (Fin n → β)`. -/
structure LossyCode (M n : ℕ) (α β : Type*)
    [MeasurableSpace α] [MeasurableSpace β] where
  encoder : (Fin n → α) → Fin M
  decoder : Fin M → (Fin n → β)

namespace LossyCode

variable {M n : ℕ}

/-- Expected block distortion of a lossy code under an i.i.d. source `P_X` on `α`. -/
noncomputable def expectedBlockDistortion
    (c : LossyCode M n α β) (P_X : Measure α) (d : DistortionFn α β) : ℝ :=
  ∫ x : Fin n → α,
      blockDistortion d n x (c.decoder (c.encoder x))
    ∂(Measure.pi (fun _ : Fin n ↦ P_X))

/-- Expected block distortion is non-negative. -/
@[entry_point]
theorem expectedBlockDistortion_nonneg
    (c : LossyCode M n α β) (P_X : Measure α) (d : DistortionFn α β) :
    0 ≤ c.expectedBlockDistortion P_X d := by
  unfold expectedBlockDistortion
  exact integral_nonneg (fun x ↦ blockDistortion_nonneg d n x _)

end LossyCode

/-! ## pmf-form expected distortion, marginals, and feasible set -/

section PmfForm

variable [Fintype α] [Fintype β]

/-- pmf-form expected distortion `∑ a, b, q(a,b) · d(a,b)` for a joint pmf
`q : α × β → ℝ` and `NNReal`-valued distortion `d`. -/
noncomputable def expectedDistortionPmf
    (d : DistortionFn α β) (q : α × β → ℝ) : ℝ :=
  ∑ a, ∑ b, q (a, b) * ((d a b : NNReal) : ℝ)

/-- First (source-side) marginal of a joint pmf `q : α × β → ℝ`. -/
noncomputable def marginalFst (q : α × β → ℝ) : α → ℝ :=
  fun a ↦ ∑ b, q (a, b)

/-- Second (reconstruction-side) marginal of a joint pmf `q : α × β → ℝ`. -/
noncomputable def marginalSnd (q : α × β → ℝ) : β → ℝ :=
  fun b ↦ ∑ a, q (a, b)


/-- Continuity of `expectedDistortionPmf` in `q` (linear in finite sum). -/
lemma continuous_expectedDistortionPmf (d : DistortionFn α β) :
    Continuous (fun q : α × β → ℝ ↦ expectedDistortionPmf d q) := by
  unfold expectedDistortionPmf
  refine continuous_finsetSum _ fun a _ ↦ ?_
  refine continuous_finsetSum _ fun b _ ↦ ?_
  exact (continuous_apply (a, b)).mul continuous_const

/-- Continuity of `marginalFst` in `q`. -/
lemma continuous_marginalFst :
    Continuous (fun q : α × β → ℝ ↦ marginalFst q) := by
  unfold marginalFst
  refine continuous_pi fun a ↦ ?_
  refine continuous_finsetSum _ fun b _ ↦ ?_
  exact continuous_apply (a, b)

/-- Continuity of `marginalSnd` in `q`. -/
lemma continuous_marginalSnd :
    Continuous (fun q : α × β → ℝ ↦ marginalSnd q) := by
  unfold marginalSnd
  refine continuous_pi fun b ↦ ?_
  refine continuous_finsetSum _ fun a _ ↦ ?_
  exact continuous_apply (a, b)


/-- The feasible joint-pmf set `{q ∈ stdSimplex | marginalFst q = P_X ∧
expectedDistortionPmf d q ≤ D}`. -/
def RDConstraint
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) : Set (α × β → ℝ) :=
  {q | q ∈ stdSimplex ℝ (α × β) ∧ marginalFst q = P_X ∧ expectedDistortionPmf d q ≤ D}


/-- `RDConstraint ⊆ stdSimplex ℝ (α × β)`. -/
lemma RDConstraint_subset_stdSimplex (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    RDConstraint P_X d D ⊆ stdSimplex ℝ (α × β) :=
  fun _ hq ↦ hq.1

/-- `RDConstraint` is closed: intersection of closed sets (stdSimplex closed,
linear constraints closed). -/
lemma RDConstraint_isClosed (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    IsClosed (RDConstraint P_X d D) := by
  -- {q | q ∈ stdSimplex} ∩ {q | marginalFst q = P_X} ∩ {q | expectedDistortionPmf d q ≤ D}.
  have h1 : IsClosed (stdSimplex ℝ (α × β)) := isClosed_stdSimplex ℝ (α × β)
  have h2 : IsClosed {q : α × β → ℝ | marginalFst q = P_X} :=
    isClosed_eq continuous_marginalFst continuous_const
  have h3 : IsClosed {q : α × β → ℝ | expectedDistortionPmf d q ≤ D} :=
    isClosed_le (continuous_expectedDistortionPmf d) continuous_const
  have heq : RDConstraint P_X d D
      = stdSimplex ℝ (α × β) ∩ {q | marginalFst q = P_X} ∩
          {q | expectedDistortionPmf d q ≤ D} := by
    ext q; constructor
    · rintro ⟨h1', h2', h3'⟩; exact ⟨⟨h1', h2'⟩, h3'⟩
    · rintro ⟨⟨h1', h2'⟩, h3'⟩; exact ⟨h1', h2', h3'⟩
  rw [heq]
  exact (h1.inter h2).inter h3

/-- `RDConstraint` is compact (closed subset of compact stdSimplex). -/
lemma RDConstraint_isCompact (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) :
    IsCompact (RDConstraint P_X d D) :=
  IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ (α × β))
    (RDConstraint_isClosed P_X d D)
    (RDConstraint_subset_stdSimplex P_X d D)


/-! ## pmf-form mutual information (entropy form, continuous via `negMulLog`) -/

/-- `mutualInfoPmf q := H(fst) + H(snd) − H(joint)` written via `negMulLog`:
`I(X;Y) = ∑_a negMulLog(q.fst a) + ∑_b negMulLog(q.snd b) − ∑_{a,b} negMulLog(q(a,b))`.
This formulation is **continuous on all of `α × β → ℝ`** because `Real.negMulLog`
is continuous everywhere (with `negMulLog 0 = 0`). -/
noncomputable def mutualInfoPmf (q : α × β → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (marginalFst q a))
    + (∑ b, Real.negMulLog (marginalSnd q b))
    - (∑ p, Real.negMulLog (q p))

/-- `mutualInfoPmf` is continuous on `α × β → ℝ`. -/
lemma continuous_mutualInfoPmf :
    Continuous (fun q : α × β → ℝ ↦ mutualInfoPmf q) := by
  unfold mutualInfoPmf
  refine Continuous.sub (Continuous.add ?_ ?_) ?_
  · refine continuous_finsetSum _ fun a _ ↦ ?_
    have h_marg : Continuous (fun q : α × β → ℝ ↦ marginalFst q a) :=
      (continuous_apply a).comp continuous_marginalFst
    exact Real.continuous_negMulLog.comp h_marg
  · refine continuous_finsetSum _ fun b _ ↦ ?_
    have h_marg : Continuous (fun q : α × β → ℝ ↦ marginalSnd q b) :=
      (continuous_apply b).comp continuous_marginalSnd
    exact Real.continuous_negMulLog.comp h_marg
  · refine continuous_finsetSum _ fun p _ ↦ ?_
    exact Real.continuous_negMulLog.comp (continuous_apply p)

/-! ## pmf-form rate-distortion function `R(D)` -/

/-- The pmf-direct rate-distortion function
`R(D) := sInf {mutualInfoPmf q | q ∈ RDConstraint P_X d D}`. When the constraint
set is non-empty the infimum is attained (`rateDistortionFunctionPmf_attained`),
since `RDConstraint` is compact and `mutualInfoPmf` is continuous.

The `sInf` of the image is used (rather than the predicate `⨅`) to avoid the
`ConditionallyCompleteLattice` `BddBelow` side conditions of `⨅ q ∈ S, f q` over
`ℝ`. -/
@[entry_point]
noncomputable def rateDistortionFunctionPmf
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ) : ℝ :=
  sInf (mutualInfoPmf '' RDConstraint P_X d D)

/-! ## Existence of a minimizer -/

/-- When the constraint set `RDConstraint P_X d D` is non-empty, the infimum
defining `rateDistortionFunctionPmf` is attained by some `q* ∈ RDConstraint`. -/
@[entry_point]
theorem rateDistortionFunctionPmf_attained
    (P_X : α → ℝ) (d : DistortionFn α β) (D : ℝ)
    (h_ne : (RDConstraint P_X d D).Nonempty) :
    ∃ qStar ∈ RDConstraint P_X d D,
      IsMinOn (fun q ↦ mutualInfoPmf q) (RDConstraint P_X d D) qStar := by
  have h_compact : IsCompact (RDConstraint P_X d D) := RDConstraint_isCompact P_X d D
  have h_cont : Continuous (fun q : α × β → ℝ ↦ mutualInfoPmf q) := continuous_mutualInfoPmf
  exact h_compact.exists_isMinOn h_ne h_cont.continuousOn


end PmfForm

end InformationTheory.Shannon
