import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.WynerZiv.FactorizableRate

/-!
# Wyner–Ziv objective convexity (Cover–Thomas Lemma 15.9)

This file discharges the `h_obj_convex` hypothesis carried by
`WynerZiv/FactorizableRate.lean` (`wynerZivRateFactorizable_convex`,
`wynerZivRateFactorizable_convex_in_D`): the convexity of the Wyner–Ziv
objective `I(X;U) − I(Y;U)` in the joint pmf `q`, along convex combinations
of *factorisable* joints `q = κ(u|x)·P_XY(x,y)`.

## Approach

The objective `wzMutualInfoXU U q − wzMutualInfoYU U q` is expanded through
the entropy form `mutualInfoPmf m = H(fst m) + H(snd m) − H(m)`.  Two exact
algebraic cancellations make the deep content explicit and isolate it from
the trivial parts:

* **`H(U)` cancellation (any `q`).** The `U`-marginal of `wzMarginalXU U q`
  and of `wzMarginalYU U q` coincide — both equal `P_U(u) = ∑_{x,y} q(x,y,u)`
  — by Fubini.  Hence the `∑_u negMulLog(P_U u)` terms (the `H(U)` blocks)
  cancel between `I(X;U)` and `I(Y;U)`.  This needs **no** factorisation.

* **`H(X) − H(Y)` constancy (factorisable `q`).** The `X`-marginal of
  `wzMarginalXU U q` equals `∑_y q(x,y,·)` summed over `u`, i.e. the
  `(X)`-marginal of `wzMarginalXY U q`.  For factorisable `q` the latter is
  `P_XY`, so this block is the constant `H(P_X)` — independent of the kernel
  `κ`.  Likewise the `Y`-block is the constant `H(P_Y)`.  Along a convex
  combination of two factorisable joints these constants are *identical*, so
  they cancel out of the convexity inequality.

After both cancellations the objective reads
`objective(q) = (H(P_X) − H(P_Y)) + (H(m_YU) − H(m_XU))`,
where `m_XU = wzMarginalXU U q`, `m_YU = wzMarginalYU U q`, and
`H(m) = ∑ negMulLog(m ·)` is the joint Shannon block.  The whole
non-trivial content of Lemma 15.9 is therefore exactly the **convexity of
the conditional-entropy difference** `κ ↦ H(m_YU) − H(m_XU)` (this is the
conditional mutual information `I(X;U|Y)`).

That residual is published as the primitive predicate
`WynerZivCondEntDiffConvex` — a genuine `ConvexOn`-shaped convexity-of-MI
statement, the irreducible Lemma-15.9 core.  `h_obj_convex` is then derived
in full from this single predicate (`wzObjective_convex_of_condEntDiff`),
and the rate-level wrapper `wynerZivRateFactorizable_convex_in_D` is
re-published with `h_obj_convex` replaced by the strictly more primitive
`WynerZivCondEntDiffConvex`.

## Implementation notes

The bare convexity of the conditional-entropy difference
`WynerZivCondEntDiffConvex` is the irreducible analytic core of Cover–Thomas
Lemma 15.9 (convexity of `I(X;U|Y)` in `κ`, a joint-convexity-of-KL argument);
it is carried as a predicate rather than proved here. Everything around it — the
`H(U)` cancellation, the `H(X)−H(Y)` constancy, and the assembly into
`h_obj_convex` — is discharged.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## §1 Joint Shannon block of the `(·,U)` marginals -/

section JointBlock

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Joint Shannon block `H(m_XU) = ∑_{x,u} negMulLog(m_XU(x,u))` of the
`(X,U)`-marginal of a joint pmf `q`. -/
noncomputable def wzJointEntXU (q : α × β × U → ℝ) : ℝ :=
  ∑ p : α × U, Real.negMulLog (wzMarginalXU U q p)

/-- Joint Shannon block `H(m_YU) = ∑_{y,u} negMulLog(m_YU(y,u))` of the
`(Y,U)`-marginal of a joint pmf `q`. -/
noncomputable def wzJointEntYU (q : α × β × U → ℝ) : ℝ :=
  ∑ p : β × U, Real.negMulLog (wzMarginalYU U q p)

end JointBlock

/-! ## §2 The `U`-marginals of `wzMarginalXU` and `wzMarginalYU` agree -/

section UMarginal

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- The `U`-marginal of `wzMarginalXU U q` equals the `U`-marginal of
`wzMarginalYU U q`: both are `P_U(u) = ∑_{x,y} q(x,y,u)`.  Holds for any `q`
(Fubini swap of the `x`/`y` sums). -/
lemma marginalSnd_wzMarginalXU_eq_marginalSnd_wzMarginalYU
    (q : α × β × U → ℝ) :
    marginalSnd (wzMarginalXU U q) = marginalSnd (wzMarginalYU U q) := by
  funext u
  unfold marginalSnd wzMarginalXU wzMarginalYU
  -- LHS: ∑ x, ∑ y, q (x, y, u); RHS: ∑ y, ∑ x, q (x, y, u).
  exact Finset.sum_comm

end UMarginal

/-! ## §3 The `X`/`Y`-marginals of the `(·,U)` marginals -/

section XYMarginal

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- The `X`-marginal of `wzMarginalXU U q` equals the `X`-marginal of
`wzMarginalXY U q` (sum over `(y,u)`). -/
lemma marginalFst_wzMarginalXU_eq_marginalFst_wzMarginalXY
    (q : α × β × U → ℝ) :
    marginalFst (wzMarginalXU U q) = marginalFst (wzMarginalXY U q) := by
  funext x
  unfold marginalFst wzMarginalXU wzMarginalXY
  -- LHS: ∑ u, ∑ y, q (x, y, u); RHS: ∑ y, ∑ u, q (x, y, u).
  exact Finset.sum_comm

/-- The `X`-marginal of `wzMarginalYU U q` equals the `Y`-marginal of
`wzMarginalXY U q` (sum over `(x,u)`). -/
lemma marginalFst_wzMarginalYU_eq_marginalSnd_wzMarginalXY
    (q : α × β × U → ℝ) :
    marginalFst (wzMarginalYU U q) = marginalSnd (wzMarginalXY U q) := by
  funext y
  unfold marginalFst marginalSnd wzMarginalYU wzMarginalXY
  -- LHS: ∑ u, ∑ x, q (x, y, u); RHS: ∑ x, ∑ u, q (x, y, u).
  exact Finset.sum_comm

end XYMarginal

/-! ## §4 Objective decomposition: `H(U)` cancellation -/

section Decomposition

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Objective decomposition (any `q`).**  After cancelling the shared
`H(U)` block,
`I(X;U) − I(Y;U)
  = [H(marginalFst m_XU) − H(marginalFst m_YU)] + [H(m_YU) − H(m_XU)]`,
where `H(g) = ∑ negMulLog(g ·)` over the relevant alphabet. -/
lemma wzObjective_decomp (q : α × β × U → ℝ) :
    wzMutualInfoXU U q - wzMutualInfoYU U q
      = ((∑ x, Real.negMulLog (marginalFst (wzMarginalXU U q) x))
          - (∑ y, Real.negMulLog (marginalFst (wzMarginalYU U q) y)))
        + (wzJointEntYU U q - wzJointEntXU U q) := by
  unfold wzMutualInfoXU wzMutualInfoYU mutualInfoPmf wzJointEntXU wzJointEntYU
  -- The two `U`-marginal Shannon blocks coincide (Fubini).
  have hU : (∑ u, Real.negMulLog (marginalSnd (wzMarginalXU U q) u))
              = (∑ u, Real.negMulLog (marginalSnd (wzMarginalYU U q) u)) := by
    rw [marginalSnd_wzMarginalXU_eq_marginalSnd_wzMarginalYU U q]
  rw [hU]; ring

end Decomposition

/-! ## §5 The marginal-block constant on factorisable joints -/

section MarginalConstant

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- On a factorisable joint the `X`/`Y`-marginal blocks reduce to the
source-only constant `H(P_X) − H(P_Y)`. -/
lemma wzObjective_marginalBlock_factorisable
    (P_XY : α × β → ℝ) {q : α × β × U → ℝ}
    (hq : IsWynerZivFactorizable U P_XY q) :
    ((∑ x, Real.negMulLog (marginalFst (wzMarginalXU U q) x))
        - (∑ y, Real.negMulLog (marginalFst (wzMarginalYU U q) y)))
      = ((∑ x, Real.negMulLog (marginalFst P_XY x))
          - (∑ y, Real.negMulLog (marginalSnd P_XY y))) := by
  have hXY : wzMarginalXY U q = P_XY :=
    IsWynerZivFactorizable_marginalXY U P_XY hq
  have hX : marginalFst (wzMarginalXU U q) = marginalFst P_XY := by
    rw [marginalFst_wzMarginalXU_eq_marginalFst_wzMarginalXY U q, hXY]
  have hY : marginalFst (wzMarginalYU U q) = marginalSnd P_XY := by
    rw [marginalFst_wzMarginalYU_eq_marginalSnd_wzMarginalXY U q, hXY]
  rw [hX, hY]

end MarginalConstant

/-! ## §6 The primitive convexity predicate (Lemma-15.9 core) -/

section Predicate

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **The irreducible Lemma-15.9 core.**  Convexity of the conditional
entropy difference `H(m_YU) − H(m_XU) = I(X;U|Y)` along convex combinations
of factorisable joints.  This is the genuine analytic content of
Cover–Thomas Lemma 15.9 (a joint-convexity-of-KL argument); it is *strictly
more primitive* than `h_obj_convex` because both the `H(U)` cancellation and
the `H(X)−H(Y)` constancy have been factored out. -/
def WynerZivCondEntDiffConvex (P_XY : α × β → ℝ) : Prop :=
  ∀ q₁ q₂ : α × β × U → ℝ,
    IsWynerZivFactorizable U P_XY q₁ →
    IsWynerZivFactorizable U P_XY q₂ →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (wzJointEntYU U (a • q₁ + b • q₂) - wzJointEntXU U (a • q₁ + b • q₂))
        ≤ a * (wzJointEntYU U q₁ - wzJointEntXU U q₁)
          + b * (wzJointEntYU U q₂ - wzJointEntXU U q₂)

end Predicate

/-! ## §7 `h_obj_convex` from the primitive predicate -/

section Assembly

variable {α β : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Objective convexity from the conditional-entropy-difference core.**
Given `WynerZivCondEntDiffConvex` (the Lemma-15.9 core), the Wyner–Ziv
objective `I(X;U) − I(Y;U)` is convex along factorisable convex
combinations — i.e. exactly the `h_obj_convex` hypothesis consumed by
`WynerZiv/FactorizableRate.lean`.

`@audit:superseded-by(wynerZivCondEntDiffConvex_holds)` -/
@[entry_point]
theorem wzObjective_convex_of_condEntDiff
    (P_XY : α × β → ℝ)
    (h_core : WynerZivCondEntDiffConvex U P_XY)
    (q₁ q₂ : α × β × U → ℝ)
    (hq₁ : IsWynerZivFactorizable U P_XY q₁)
    (hq₂ : IsWynerZivFactorizable U P_XY q₂)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    wzMutualInfoXU U (a • q₁ + b • q₂) - wzMutualInfoYU U (a • q₁ + b • q₂)
      ≤ a * (wzMutualInfoXU U q₁ - wzMutualInfoYU U q₁)
        + b * (wzMutualInfoXU U q₂ - wzMutualInfoYU U q₂) := by
  -- The mixed joint is itself factorisable.
  have hmix : IsWynerZivFactorizable U P_XY (a • q₁ + b • q₂) :=
    IsWynerZivFactorizable_convex_combination U P_XY hq₁ hq₂ ha hb hab
  -- Abbreviation: the common source-only marginal-block constant.
  set C : ℝ := (∑ x, Real.negMulLog (marginalFst P_XY x))
                - (∑ y, Real.negMulLog (marginalSnd P_XY y)) with hC
  -- Decompose each objective into (marginal block) + (cond.-entropy diff).
  have hd₁ := wzObjective_decomp U q₁
  have hd₂ := wzObjective_decomp U q₂
  have hdm := wzObjective_decomp U (a • q₁ + b • q₂)
  -- Each marginal block collapses to the constant `C`.
  have hb₁ := wzObjective_marginalBlock_factorisable U P_XY hq₁
  have hb₂ := wzObjective_marginalBlock_factorisable U P_XY hq₂
  have hbm := wzObjective_marginalBlock_factorisable U P_XY hmix
  rw [← hC] at hb₁ hb₂ hbm
  rw [hb₁] at hd₁
  rw [hb₂] at hd₂
  rw [hbm] at hdm
  -- The core inequality on the conditional-entropy differences.
  have hcore := h_core q₁ q₂ hq₁ hq₂ a b ha hb hab
  -- Assemble.
  rw [hd₁, hd₂, hdm]
  have hab' : (a + b) * C = C := by rw [hab, one_mul]
  nlinarith [hcore, hab']

end Assembly

/-! ## §8 Re-published rate-level convexity wrapper -/

section RateWrapper

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- Convexity of the factorizable rate function in `D`, with `h_obj_convex`
replaced by the more primitive conditional-entropy-difference convexity predicate
`WynerZivCondEntDiffConvex` (discharged into `h_obj_convex` by
`wzObjective_convex_of_condEntDiff`).

`@audit:superseded-by(wynerZivRateFactorizable_convex_in_D_unconditional)` -/
@[entry_point]
theorem wynerZivRateFactorizable_convex_in_D_of_condEntDiff
    {P_XY : α × β → ℝ} (h_pmf : P_XY ∈ stdSimplex ℝ (α × β))
    (d : α → γ → ℝ) (f : U × β → γ)
    {D₁ D₂ : ℝ}
    (h_core : WynerZivCondEntDiffConvex U P_XY)
    {q₁ q₂ : α × β × U → ℝ}
    (h_feasible₁ : (q₁, f) ∈ WynerZivFactorizableConstraint U P_XY d D₁)
    (h_feasible₂ : (q₂, f) ∈ WynerZivFactorizableConstraint U P_XY d D₂)
    (h_attain₁ : wynerZivRateFactorizable U P_XY d D₁
                  = wzMutualInfoXU U q₁ - wzMutualInfoYU U q₁)
    (h_attain₂ : wynerZivRateFactorizable U P_XY d D₂
                  = wzMutualInfoXU U q₂ - wzMutualInfoYU U q₂)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    wynerZivRateFactorizable U P_XY d (a * D₁ + b * D₂)
      ≤ a * wynerZivRateFactorizable U P_XY d D₁
        + b * wynerZivRateFactorizable U P_XY d D₂ := by
  classical
  exact wynerZivRateFactorizable_convex_in_D U h_pmf d f
    (fun q₁' q₂' hq₁' hq₂' a' b' ha' hb' hab' ↦
      wzObjective_convex_of_condEntDiff U P_XY h_core q₁' q₂' hq₁' hq₂' a' b' ha' hb' hab')
    h_feasible₁ h_feasible₂ h_attain₁ h_attain₂ ha hb hab

end RateWrapper

end InformationTheory.Shannon
