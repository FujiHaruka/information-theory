import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.RateDistortion.Achievability
import InformationTheory.Shannon.RateDistortion.ConverseNLetter

/-!
# Wyner–Ziv lossy distributed coding

The rate-distortion function for Wyner–Ziv lossy compression with side
information `Y` available at the decoder only (Cover–Thomas, Theorem 15.9.1):

```
R_WZ(D) = min_{p(u|x), f : U × Y → X̂} [ I(X ; U) − I(Y ; U) ]
```

with the minimization subject to the Markov chain `U − X − Y` and the distortion
constraint `𝔼 d(X, f(U, Y)) ≤ D`.

This file defines the `WynerZivCode` structure, the joint pmf marginals, the
`WynerZivConstraint` feasible set, the `wynerZivRatePmf` rate function, the
slice-attainment lemma, and the rate-equality wrapper `wyner_ziv_tendsto`. The
achievability and converse legs are developed in `WynerZivAchievability.lean` and
`WynerZivConverse.lean`.

## Main definitions

* `WynerZivCode` — a Wyner–Ziv block code (X-side encoder, side-information
  decoder).
* `wzMarginalXY`, `wzMarginalXU`, `wzMarginalYU` — the marginals of a joint pmf.
* `WynerZivConstraint` — the feasible `(q, f)` pairs.
* `wynerZivRatePmf` — the rate function `R_WZ(D)`.

## Main statements

* `continuous_wzObjective` — continuity of the objective `I(X;U) − I(Y;U)`.
* `wynerZivRatePmf_attained_slice` — the objective attains its minimum on a
  decoder slice.
* `wyner_ziv_tendsto` — the rate-equality form from two-sided bounds.

## Implementation notes

The decoder `f : U × β → γ` is carried as an external second component, so the
constraint set lives on `(α × β × U → ℝ) × (U × β → γ)`. The auxiliary alphabet
`U` is taken as an argument rather than constructed from a cardinality bound.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Wyner–Ziv block code -/

/-- A **Wyner–Ziv block code** of length `n` with `M` codewords. Encoder is
X-side only; decoder takes `(codeword, side info Y^n)` and reproduces an
estimate of `X^n` over the reconstruction alphabet `γ`. -/
structure WynerZivCode (M n : ℕ) (α β γ : Type*)
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] where
  encoder : (Fin n → α) → Fin M
  decoder : Fin M × (Fin n → β) → (Fin n → γ)

namespace WynerZivCode

variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {M n : ℕ}

/-- Expected block distortion of a Wyner–Ziv code under a joint source measure
`P_XY` on `α × β`. The source is i.i.d., so `(X^n, Y^n)` is distributed
according to `Measure.pi (fun _ => P_XY)` on `(α × β)^n`. -/
noncomputable def expectedBlockDistortion
    (c : WynerZivCode M n α β γ) (P_XY : Measure (α × β))
    (d : DistortionFn α γ) : ℝ :=
  ∫ p : Fin n → α × β,
      blockDistortion d n (fun i ↦ (p i).1)
        (c.decoder (c.encoder (fun i ↦ (p i).1), fun i ↦ (p i).2))
    ∂(Measure.pi (fun _ : Fin n ↦ P_XY))

/-- Expected block distortion is non-negative (the integrand is a non-negative
real-valued function). -/
@[entry_point]
theorem expectedBlockDistortion_nonneg
    (c : WynerZivCode M n α β γ) (P_XY : Measure (α × β))
    (d : DistortionFn α γ) :
    0 ≤ c.expectedBlockDistortion P_XY d := by
  unfold expectedBlockDistortion
  exact integral_nonneg fun _ ↦ blockDistortion_nonneg d n _ _

end WynerZivCode

/-! ## pmf form: 3-variable marginals and mutual informations -/

section PmfForm

variable {α β : Type*} [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- `(α, β)`-marginal of a joint pmf `q : α × β × U → ℝ`. -/
noncomputable def wzMarginalXY (q : α × β × U → ℝ) : α × β → ℝ :=
  fun p ↦ ∑ u, q (p.1, p.2, u)

/-- `(α, U)`-marginal of a joint pmf `q : α × β × U → ℝ`. -/
noncomputable def wzMarginalXU (q : α × β × U → ℝ) : α × U → ℝ :=
  fun p ↦ ∑ y, q (p.1, y, p.2)

/-- `(β, U)`-marginal of a joint pmf `q : α × β × U → ℝ`. -/
noncomputable def wzMarginalYU (q : α × β × U → ℝ) : β × U → ℝ :=
  fun p ↦ ∑ x, q (x, p.1, p.2)

/-- 3-variable mutual information `I(X ; U)` for a joint pmf `q : α × β × U → ℝ`,
defined as `mutualInfoPmf (wzMarginalXU q)`. -/
noncomputable def wzMutualInfoXU (q : α × β × U → ℝ) : ℝ :=
  mutualInfoPmf (wzMarginalXU U q)

/-- 3-variable mutual information `I(Y ; U)` for a joint pmf `q : α × β × U → ℝ`,
defined as `mutualInfoPmf (wzMarginalYU q)`. -/
noncomputable def wzMutualInfoYU (q : α × β × U → ℝ) : ℝ :=
  mutualInfoPmf (wzMarginalYU U q)

/-- `wzMarginalXY` is continuous in `q` (finite sum of evaluations). -/
lemma continuous_wzMarginalXY :
    Continuous (fun q : α × β × U → ℝ ↦ wzMarginalXY U q) := by
  unfold wzMarginalXY
  refine continuous_pi fun p ↦ ?_
  refine continuous_finsetSum _ fun u _ ↦ ?_
  exact continuous_apply (p.1, p.2, u)

/-- `wzMarginalXU` is continuous in `q`. -/
lemma continuous_wzMarginalXU :
    Continuous (fun q : α × β × U → ℝ ↦ wzMarginalXU U q) := by
  unfold wzMarginalXU
  refine continuous_pi fun p ↦ ?_
  refine continuous_finsetSum _ fun y _ ↦ ?_
  exact continuous_apply (p.1, y, p.2)

/-- `wzMarginalYU` is continuous in `q`. -/
lemma continuous_wzMarginalYU :
    Continuous (fun q : α × β × U → ℝ ↦ wzMarginalYU U q) := by
  unfold wzMarginalYU
  refine continuous_pi fun p ↦ ?_
  refine continuous_finsetSum _ fun x _ ↦ ?_
  exact continuous_apply (x, p.1, p.2)

/-- `wzMutualInfoXU` is continuous in `q`. -/
lemma continuous_wzMutualInfoXU :
    Continuous (fun q : α × β × U → ℝ ↦ wzMutualInfoXU U q) :=
  continuous_mutualInfoPmf.comp (continuous_wzMarginalXU U)

/-- `wzMutualInfoYU` is continuous in `q`. -/
lemma continuous_wzMutualInfoYU :
    Continuous (fun q : α × β × U → ℝ ↦ wzMutualInfoYU U q) :=
  continuous_mutualInfoPmf.comp (continuous_wzMarginalYU U)

/-- The Wyner–Ziv objective `I(X ; U) − I(Y ; U)` is continuous in the joint pmf. -/
@[entry_point]
lemma continuous_wzObjective :
    Continuous (fun q : α × β × U → ℝ ↦ wzMutualInfoXU U q - wzMutualInfoYU U q) :=
  (continuous_wzMutualInfoXU U).sub (continuous_wzMutualInfoYU U)

end PmfForm

/-! ## Wyner–Ziv constraint set

The decoder `f : U × β → γ` is carried as an *external* second component, so
the constraint set lives on the product `(α × β × U → ℝ) × (U × β → γ)`. The
Markov constraint `U − X − Y` is encoded in cross-product form, well-defined
even where marginals vanish (inventory §6.5).
-/

section Constraint

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Distortion functional in pmf form for Wyner–Ziv:
`∑_{x,y,u} q(x,y,u) · d(x, f(u,y))`. -/
noncomputable def wzExpectedDistortion
    (d : α → γ → ℝ) (q : α × β × U → ℝ) (f : U × β → γ) : ℝ :=
  ∑ p : α × β × U, q p * d p.1 (f (p.2.2, p.2.1))

/-- Markov-chain cross-product form
`q(x,y,u) · q_X(x,u') = q(x,y,u') · q_X(x,u)` where `q_X(x,u) := ∑_y q(x,y,u)`.
Encoded as a real-valued affine condition (well-defined where `q_X` vanishes —
both sides become `0`). -/
def wzMarkovCrossEq (q : α × β × U → ℝ) : Prop :=
  ∀ x : α, ∀ y : β, ∀ u u' : U,
    q (x, y, u) * (∑ y', q (x, y', u'))
      = q (x, y, u') * (∑ y', q (x, y', u))

/-- **Wyner–Ziv constraint set** — feasible `(q, f)` pairs satisfying:
1. `q ∈ stdSimplex ℝ (α × β × U)` — non-negative pmf with total mass 1.
2. `wzMarginalXY q = P_XY` — `(X, Y)` marginal matches the source.
3. `wzMarkovCrossEq q` — Markov chain `U − X − Y`.
4. `wzExpectedDistortion d q f ≤ D` — expected distortion within budget. -/
def WynerZivConstraint
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) :
    Set ((α × β × U → ℝ) × (U × β → γ)) :=
  {qf | qf.1 ∈ stdSimplex ℝ (α × β × U)
        ∧ wzMarginalXY U qf.1 = P_XY
        ∧ wzMarkovCrossEq U qf.1
        ∧ wzExpectedDistortion U d qf.1 qf.2 ≤ D}

/-- Membership unfold for `WynerZivConstraint`. -/
@[entry_point]
lemma mem_WynerZivConstraint_iff
    {P_XY : α × β → ℝ} {d : α → γ → ℝ} {D : ℝ}
    {qf : (α × β × U → ℝ) × (U × β → γ)} :
    qf ∈ WynerZivConstraint U P_XY d D ↔
      qf.1 ∈ stdSimplex ℝ (α × β × U)
        ∧ wzMarginalXY U qf.1 = P_XY
        ∧ wzMarkovCrossEq U qf.1
        ∧ wzExpectedDistortion U d qf.1 qf.2 ≤ D := Iff.rfl

end Constraint

/-! ## Wyner–Ziv rate function -/

section Rate

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- The **Wyner–Ziv rate function** (pmf form),
`R_WZ(D) := sInf { I(X;U) − I(Y;U) | (q, f) ∈ WynerZivConstraint U P_XY d D }`,
with the auxiliary alphabet `U` taken as an argument. -/
noncomputable def wynerZivRatePmf
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ) : ℝ :=
  sInf ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
            wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
    '' WynerZivConstraint U P_XY d D)

/-- Upper bound from any feasible point: if `(q, f) ∈ WynerZivConstraint`
and the image is bounded below (which it always is on the simplex), then
`wynerZivRatePmf ≤ I(X;U)(q) − I(Y;U)(q)`. -/
@[entry_point]
theorem wynerZivRatePmf_le_of_feasible
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    (qf : (α × β × U → ℝ) × (U × β → γ))
    (hqf : qf ∈ WynerZivConstraint U P_XY d D)
    (h_bdd : BddBelow ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
            '' WynerZivConstraint U P_XY d D)) :
    wynerZivRatePmf U P_XY d D ≤
      wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1 := by
  unfold wynerZivRatePmf
  exact csInf_le h_bdd ⟨qf, hqf, rfl⟩

/-- **Attainment (slice form)** — fix a decoder `f₀ : U × β → γ` and assume
the slice `K f₀ := {q | (q, f₀) ∈ WynerZivConstraint U P_XY d D}` is
non-empty. Then there exists a `qStar ∈ K f₀` minimizing the Wyner–Ziv
objective `I(X;U) − I(Y;U)` over `K f₀`. This is the structural ingredient
that the achievability/converse proofs rely on; the full *joint* attainment
over `(q, f)` requires further hypotheses on `(γ, U, β)` and is deferred. -/
@[entry_point]
theorem wynerZivRatePmf_attained_slice
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    (f₀ : U × β → γ)
    (h_ne : ({q : α × β × U → ℝ | (q, f₀) ∈ WynerZivConstraint U P_XY d D}).Nonempty) :
    ∃ qStar ∈ ({q : α × β × U → ℝ | (q, f₀) ∈ WynerZivConstraint U P_XY d D}),
      IsMinOn (fun q ↦ wzMutualInfoXU U q - wzMutualInfoYU U q)
        ({q : α × β × U → ℝ | (q, f₀) ∈ WynerZivConstraint U P_XY d D}) qStar := by
  classical
  set K : Set (α × β × U → ℝ) :=
    {q | (q, f₀) ∈ WynerZivConstraint U P_XY d D}
  have hK_subset : K ⊆ stdSimplex ℝ (α × β × U) :=
    fun q hq ↦ hq.1
  -- The Markov cross-product equation set is closed (intersection over
  -- (x, y, u, u') of equality sets between products of continuous evaluations).
  have hMarkov_closed :
      IsClosed {q : α × β × U → ℝ | wzMarkovCrossEq U q} := by
    have h_eq :
        {q : α × β × U → ℝ | wzMarkovCrossEq U q}
          = ⋂ (x : α), ⋂ (y : β), ⋂ (u : U), ⋂ (u' : U),
              {q : α × β × U → ℝ |
                q (x, y, u) * (∑ y', q (x, y', u'))
                  = q (x, y, u') * (∑ y', q (x, y', u))} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iInter, wzMarkovCrossEq]
    rw [h_eq]
    refine isClosed_iInter fun x ↦ ?_
    refine isClosed_iInter fun y ↦ ?_
    refine isClosed_iInter fun u ↦ ?_
    refine isClosed_iInter fun u' ↦ ?_
    refine isClosed_eq ?_ ?_
    · refine Continuous.mul (continuous_apply (x, y, u)) ?_
      refine continuous_finsetSum _ fun y' _ ↦ ?_
      exact continuous_apply (x, y', u')
    · refine Continuous.mul (continuous_apply (x, y, u')) ?_
      refine continuous_finsetSum _ fun y' _ ↦ ?_
      exact continuous_apply (x, y', u)
  have hMarg_closed :
      IsClosed {q : α × β × U → ℝ | wzMarginalXY U q = P_XY} :=
    isClosed_eq (continuous_wzMarginalXY U) continuous_const
  have hDist_cont :
      Continuous (fun q : α × β × U → ℝ ↦ wzExpectedDistortion U d q f₀) := by
    unfold wzExpectedDistortion
    refine continuous_finsetSum _ fun p _ ↦ ?_
    exact (continuous_apply p).mul continuous_const
  have hDist_closed :
      IsClosed {q : α × β × U → ℝ | wzExpectedDistortion U d q f₀ ≤ D} :=
    isClosed_le hDist_cont continuous_const
  have hSimp_closed : IsClosed (stdSimplex ℝ (α × β × U)) :=
    isClosed_stdSimplex ℝ (α × β × U)
  have hK_eq : K = stdSimplex ℝ (α × β × U)
      ∩ {q | wzMarginalXY U q = P_XY}
      ∩ {q | wzMarkovCrossEq U q}
      ∩ {q | wzExpectedDistortion U d q f₀ ≤ D} := by
    ext q
    refine ⟨?_, ?_⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
  have hK_closed : IsClosed K := by
    rw [hK_eq]
    exact ((hSimp_closed.inter hMarg_closed).inter hMarkov_closed).inter hDist_closed
  have hK_compact : IsCompact K :=
    IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ (α × β × U)) hK_closed hK_subset
  have hCont_obj :
      Continuous (fun q : α × β × U → ℝ ↦ wzMutualInfoXU U q - wzMutualInfoYU U q) :=
    continuous_wzObjective U
  exact hK_compact.exists_isMinOn h_ne hCont_obj.continuousOn

/-- The image of the Wyner–Ziv constraint set under the objective is bounded
below by any caller-supplied lower bound `B` (the canonical bound is
`-Real.log (Fintype.card U)`, since `I(X;U) ≥ 0` and
`I(Y;U) ≤ Real.log (Fintype.card U)` on a finite alphabet). -/
@[entry_point]
theorem wynerZivRatePmf_image_bddBelow_of_objective
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D : ℝ)
    (B : ℝ)
    (h_lb : ∀ qf ∈ WynerZivConstraint U P_XY d D,
              B ≤ wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1) :
    BddBelow ((fun qf : (α × β × U → ℝ) × (U × β → γ) ↦
                wzMutualInfoXU U qf.1 - wzMutualInfoYU U qf.1)
            '' WynerZivConstraint U P_XY d D) := by
  refine ⟨B, ?_⟩
  rintro v ⟨qf, hqf, rfl⟩
  exact h_lb qf hqf

end Rate

/-! ## Rate-equality wrapper -/

section Wrapper

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- The Wyner–Ziv rate-equality form: from achievability
`R ≥ wynerZivRatePmf(D)` and converse `R ≤ wynerZivRatePmf(D)`,
`R = wynerZivRatePmf(D)`. The two-sided hypotheses are discharged in
`WynerZivAchievability.lean` and `WynerZivConverse.lean`. -/
@[entry_point]
theorem wyner_ziv_tendsto
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (h_ach : wynerZivRatePmf U P_XY d D ≤ R)
    (h_conv : R ≤ wynerZivRatePmf U P_XY d D) :
    R = wynerZivRatePmf U P_XY d D :=
  le_antisymm h_conv h_ach

end Wrapper

end InformationTheory.Shannon
