import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MaxEntropyConstrained

/-!
# Constrained Maximum Entropy — Lagrange / KKT perspective (T3-A')

The companion file `MaxEntropyConstrained.lean` publishes the **Boltzmann–Gibbs**
main theorems (`entropy_le_gibbs_of_constraints`, `entropy_eq_gibbs_iff_of_constraints`)
in the `gibbsPmf f λ` notation, derived by the algebraic-identity route
(`klDivPmf_gibbsPmf_eq`). The present file re-packages those results in the
**KKT / exponential-family language**:

  expFamilyDist λ f x := exp (⟨λ, f x⟩ - ψ(λ))
  logPartitionψ λ f   := log (∑ y, exp ⟨λ, f y⟩)

with `ψ(λ) = logPartitionψ` the log-partition function. The two presentations
are equal pointwise (`expFamilyDist_eq_gibbsPmf`), so every property of `gibbsPmf`
transports to `expFamilyDist`. The KKT first-order condition (∇ψ(λ) = 𝔼[f] in
the unconstrained Lagrangian) appears as the **moment-matching hypothesis**
which we pass through (Mathlib lacks the convex-duality theorems needed to
*solve* for `λ`; it does have everything we need to *use* a given solution).

## Main results

* `logPartitionψ`                         — log-partition function `ψ(λ)`
* `expFamilyDist`                         — exponential-family pmf
                                            `x ↦ exp (⟨λ, f x⟩ - ψ(λ))`
* `expFamilyDist_eq_gibbsPmf`             — bridge `expFamilyDist = gibbsPmf`
* `expFamilyDist_mem_stdSimplex`          — `expFamilyDist λ f ∈ stdSimplex`
* `expFamilyDist_pos`                     — pointwise strict positivity
* `KKTSolution`                           — packaged Lagrange multiplier + moment witness
* `entropy_expFamilyDist_eq_legendre`     — Legendre identity
                                            `H(p*) = ψ(λ) - ⟨λ, c⟩`
* `expFamily_maximizes_entropy`           — **main theorem (Tier 1)** —
                                            constraint-respecting `P` satisfies
                                            `H(P) ≤ H(expFamilyDist λ f)`
* `expFamily_unique`                      — **main theorem (Tier 2)** —
                                            equality ⟺ `P = expFamilyDist λ f`
* `expFamily_maximizes_entropy_of_KKT`    — Cover–Thomas Theorem 12.1.1 in the
                                            `KKTSolution` packaging
* `entropy_le_logPartition_sub_inner`     — variational form
                                            `H(P) ≤ ψ(λ) - ⟨λ, c⟩`

## Approach

We define `logPartitionψ` and `expFamilyDist` via the existing `gibbsZ` and
`gibbsPmf` (a single `Real.exp_sub` step bridges the two presentations). All
theorems are then proved by direct reduction to their `gibbsPmf` analogues in
`MaxEntropyConstrained.lean`. The KKT first-order condition is encoded as the
constraint-witness hypothesis `∀ i, ∑ x, expFamilyDist λ f x · f i x = c i`
(equivalent to `∇ψ(λ) = 𝔼_{p*}[f]` at the saddle point, but stated in the
ansatz-pass-through form to avoid the convex-duality theorems Mathlib does
not provide).
-/

namespace InformationTheory.Shannon.MaxEntropyConstrainedKKT

set_option linter.unusedSectionVars false

open Real InformationTheory
open InformationTheory.Shannon.MaxEntropyConstrained
  (gibbsZ gibbsPmf gibbsZ_pos gibbsPmf_pos gibbsPmf_nonneg gibbsPmf_sum_eq_one
   gibbsPmf_mem_stdSimplex log_gibbsPmf klDivPmf_gibbsPmf_eq
   entropy_le_gibbs_of_constraints entropy_eq_gibbs_iff_of_constraints)
open InformationTheory.Shannon.CsiszarProjection (klDivPmf klDivPmf_nonneg)
open InformationTheory.Shannon.Chernoff (klDivPmf_self_eq_zero)
open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {k : ℕ}

/-! ## Section 1 — Log-partition function and exponential-family pmf -/

/-- **Log-partition function** `ψ(λ) := log (∑ y, exp ⟨λ, f y⟩)`.

In the Lagrangian for constrained maximum entropy, `ψ(λ)` is the Legendre dual
of `H` and its gradient `∇ψ(λ) = 𝔼_{p_λ^*}[f]` encodes the KKT first-order
condition (moment matching). -/
noncomputable def logPartitionψ (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : ℝ :=
  Real.log (gibbsZ f lam)

/-- **Exponential family pmf**, Lagrangian / KKT-canonical form:

  expFamilyDist λ f x := exp (⟨λ, f x⟩ - ψ(λ))

where `⟨λ, f x⟩ = ∑ i, λ i · f i x`. This is the saddle-point optimizer of the
Lagrangian `L(p, λ) = H(p) + ∑ i, λ i (𝔼_p[f i] - c i)`. By
`expFamilyDist_eq_gibbsPmf` it agrees pointwise with `gibbsPmf f λ`, so all
positivity / pmf properties transfer. -/
noncomputable def expFamilyDist (f : Fin k → α → ℝ) (lam : Fin k → ℝ) : α → ℝ :=
  fun x => Real.exp ((∑ i, lam i * f i x) - logPartitionψ f lam)

/-- **Bridge**: the KKT-canonical form `expFamilyDist` agrees pointwise with the
Boltzmann–Gibbs form `gibbsPmf`:

  exp (⟨λ, f x⟩ - ψ(λ)) = exp ⟨λ, f x⟩ / Z(λ).

Proof: `Real.exp_sub` + `Real.exp_log` on `Z(λ) > 0`. -/
lemma expFamilyDist_eq_gibbsPmf [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    expFamilyDist f lam = gibbsPmf f lam := by
  funext x
  unfold expFamilyDist logPartitionψ gibbsPmf
  rw [Real.exp_sub, Real.exp_log (gibbsZ_pos f lam)]

/-! ## Section 2 — Basic positivity / pmf properties transported from `gibbsPmf` -/

/-- `expFamilyDist` is pointwise strictly positive. -/
@[entry_point]
lemma expFamilyDist_pos [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) (x : α) :
    0 < expFamilyDist f lam x := by
  rw [show expFamilyDist f lam = gibbsPmf f lam from expFamilyDist_eq_gibbsPmf f lam]
  exact gibbsPmf_pos f lam x

/-- `expFamilyDist λ f ∈ stdSimplex ℝ α`. -/
@[entry_point]
lemma expFamilyDist_mem_stdSimplex [Nonempty α]
    (f : Fin k → α → ℝ) (lam : Fin k → ℝ) :
    expFamilyDist f lam ∈ stdSimplex ℝ α := by
  rw [show expFamilyDist f lam = gibbsPmf f lam from expFamilyDist_eq_gibbsPmf f lam]
  exact gibbsPmf_mem_stdSimplex f lam

/-! ## Section 3 — KKT solution packaging -/

/-- **KKT solution** for the constrained maximum-entropy problem with feature
maps `f : Fin k → α → ℝ` and moment targets `c : Fin k → ℝ`.

A `KKTSolution f c` packages a Lagrange multiplier vector `lam : Fin k → ℝ`
with a proof that the exponential-family ansatz `expFamilyDist f lam` satisfies
the moment-matching first-order condition `𝔼_{p*}[f i] = c i` for all `i`.

This is precisely the KKT condition for the Lagrangian
`L(p, λ) = H(p) + ∑ i, λ i (𝔼_p[f i] - c i)`: stationarity in `p` picks out
the exponential family, and feasibility in `λ` is the moment match. -/
structure KKTSolution (f : Fin k → α → ℝ) (c : Fin k → ℝ) where
  /-- Lagrange multiplier (one per feature / constraint). -/
  lam : Fin k → ℝ
  /-- **KKT moment-matching condition** — `∇ψ(λ) = c`, equivalently
      `𝔼_{p*}[f i] = c i` for all `i`. -/
  moment_match : ∀ i, ∑ x, expFamilyDist f lam x * f i x = c i

/-- KKT-solution moment matching restated in the `gibbsPmf` language. -/
lemma KKTSolution.gibbs_moment_match [Nonempty α]
    {f : Fin k → α → ℝ} {c : Fin k → ℝ} (S : KKTSolution f c) :
    ∀ i, ∑ x, gibbsPmf f S.lam x * f i x = c i := by
  intro i
  have h := S.moment_match i
  rw [show expFamilyDist f S.lam = gibbsPmf f S.lam
        from expFamilyDist_eq_gibbsPmf f S.lam] at h
  exact h

/-! ## Section 4 — Legendre identity: self-entropy of the exponential family -/

/-- **Legendre / saddle-point identity** for the exponential family. With KKT
solution `(λ, moment_match)` for constraints `c`, the entropy of the
exponential-family optimum has the closed form

  H(p*) = ψ(λ) - ⟨λ, c⟩.

This is the KKT duality: at the saddle point of the Lagrangian, the primal value
equals the dual value `ψ(λ) - ⟨λ, c⟩`. -/
@[entry_point]
theorem entropy_expFamilyDist_eq_legendre [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ) (S : KKTSolution f c) :
    ∑ x, Real.negMulLog (expFamilyDist f S.lam x)
      = logPartitionψ f S.lam - ∑ i, S.lam i * c i := by
  -- Reduce to gibbsPmf and apply the core identity at Q = gibbsPmf.
  rw [show expFamilyDist f S.lam = gibbsPmf f S.lam
        from expFamilyDist_eq_gibbsPmf f S.lam]
  -- Core identity at Q := gibbsPmf yields:
  --   klDivPmf gibbs gibbs = -H(gibbs) - ⟨λ, 𝔼_gibbs[f]⟩ + log Z.
  -- LHS = 0 by `klDivPmf_self_eq_zero`; RHS uses moment_match.
  have h_eq_G := klDivPmf_gibbsPmf_eq f S.lam (gibbsPmf f S.lam)
                  (gibbsPmf_mem_stdSimplex f S.lam)
  have h_self : klDivPmf (gibbsPmf f S.lam) (gibbsPmf f S.lam) = 0 :=
    klDivPmf_self_eq_zero (gibbsPmf f S.lam) (gibbsPmf_pos f S.lam)
  -- Apply moment match in h_eq_G.
  have h_match := S.gibbs_moment_match
  have h_inner_G : (∑ i, S.lam i * (∑ x, gibbsPmf f S.lam x * f i x))
                    = ∑ i, S.lam i * c i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_match i]
  rw [h_inner_G] at h_eq_G
  unfold logPartitionψ
  linarith

/-! ## Section 5 — Main theorem: exponential family maximizes constrained entropy -/

/-- **Cover–Thomas Theorem 12.1.1 (Tier 1) — KKT / exponential-family form**.

Under moment constraints `𝔼_P[f i] = c i` for all `i`, the entropy of `P` is
bounded above by the entropy of the exponential-family solution
`expFamilyDist f λ`, provided the latter also satisfies the same moments
(KKT first-order condition).

This is `entropy_le_gibbs_of_constraints` repackaged in the KKT language. -/
@[entry_point]
theorem expFamily_maximizes_entropy [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_KKT : ∀ i, ∑ x, expFamilyDist f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) ≤ ∑ x, Real.negMulLog (expFamilyDist f lam x) := by
  -- Transport the KKT moment-match to the gibbs form, invoke the existing
  -- `entropy_le_gibbs_of_constraints`, then transport the conclusion back.
  have h_gibbs_KKT : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i := by
    intro i
    have := h_KKT i
    rw [show expFamilyDist f lam = gibbsPmf f lam
          from expFamilyDist_eq_gibbsPmf f lam] at this
    exact this
  have h := entropy_le_gibbs_of_constraints f c P hP hP_constraints lam h_gibbs_KKT
  rw [show expFamilyDist f lam = gibbsPmf f lam
        from expFamilyDist_eq_gibbsPmf f lam]
  exact h

/-- **KKT-packaged Cover–Thomas Theorem 12.1.1**: a constraint-feasible `P` cannot
exceed the entropy of the exponential-family solution attached to a KKT witness. -/
@[entry_point]
theorem expFamily_maximizes_entropy_of_KKT [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (S : KKTSolution f c) :
    ∑ x, Real.negMulLog (P x) ≤ ∑ x, Real.negMulLog (expFamilyDist f S.lam x) :=
  expFamily_maximizes_entropy f c P hP hP_constraints S.lam S.moment_match

/-! ## Section 6 — Uniqueness of the exponential-family maximizer -/

/-- **Cover–Thomas Theorem 12.1.1 uniqueness (Tier 2) — KKT / exponential-family form**.

For constraint-feasible `P` and a KKT-witnessed exponential-family solution,
entropy equality `H(P) = H(expFamilyDist f λ)` holds *if and only if*
`P = expFamilyDist f λ` pointwise.

This is `entropy_eq_gibbs_iff_of_constraints` repackaged. -/
@[entry_point]
theorem expFamily_unique [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_KKT : ∀ i, ∑ x, expFamilyDist f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x) = ∑ x, Real.negMulLog (expFamilyDist f lam x)
      ↔ P = expFamilyDist f lam := by
  have h_bridge : expFamilyDist f lam = gibbsPmf f lam :=
    expFamilyDist_eq_gibbsPmf f lam
  have h_gibbs_KKT : ∀ i, ∑ x, gibbsPmf f lam x * f i x = c i := by
    intro i
    have := h_KKT i
    rw [h_bridge] at this
    exact this
  rw [h_bridge]
  exact entropy_eq_gibbs_iff_of_constraints f c P hP hP_constraints lam h_gibbs_KKT

/-- KKT-packaged uniqueness companion of `expFamily_maximizes_entropy_of_KKT`. -/
@[entry_point]
theorem expFamily_unique_of_KKT [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (S : KKTSolution f c) :
    ∑ x, Real.negMulLog (P x) = ∑ x, Real.negMulLog (expFamilyDist f S.lam x)
      ↔ P = expFamilyDist f S.lam :=
  expFamily_unique f c P hP hP_constraints S.lam S.moment_match

/-! ## Section 7 — Variational form (free-energy / Legendre dual upper bound) -/

/-- **Variational upper bound (Legendre / free-energy form)** — any constraint-feasible
`P` satisfies the dual bound

  H(P) ≤ ψ(λ) - ⟨λ, c⟩

for *every* `λ` whose exponential-family solution satisfies the same moments.
This is the variational characterization of `logPartitionψ` as the Legendre
transform of `-H` restricted to the feasibility set. -/
@[entry_point]
theorem entropy_le_logPartition_sub_inner [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (lam : Fin k → ℝ)
    (h_KKT : ∀ i, ∑ x, expFamilyDist f lam x * f i x = c i) :
    ∑ x, Real.negMulLog (P x)
      ≤ logPartitionψ f lam - ∑ i, lam i * c i := by
  -- Combine main inequality + Legendre identity on the gibbs side.
  have h_main := expFamily_maximizes_entropy f c P hP hP_constraints lam h_KKT
  -- Set up KKT solution S = ⟨lam, h_KKT⟩ to use the Legendre lemma.
  let S : KKTSolution f c := { lam := lam, moment_match := h_KKT }
  have h_leg : ∑ x, Real.negMulLog (expFamilyDist f lam x)
                = logPartitionψ f lam - ∑ i, lam i * c i :=
    entropy_expFamilyDist_eq_legendre (S := S) f c
  linarith

/-- KKT-packaged variational form. -/
@[entry_point]
theorem entropy_le_logPartition_sub_inner_of_KKT [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (P : α → ℝ) (hP : P ∈ stdSimplex ℝ α)
    (hP_constraints : ∀ i, ∑ x, P x * f i x = c i)
    (S : KKTSolution f c) :
    ∑ x, Real.negMulLog (P x)
      ≤ logPartitionψ f S.lam - ∑ i, S.lam i * c i :=
  entropy_le_logPartition_sub_inner f c P hP hP_constraints S.lam S.moment_match

/-! ## Section 8 — KKT first-order moment-matching reformulation -/

/-- **KKT first-order condition equivalence** — the moment-matching hypothesis
`𝔼_{p*}[f] = c` (the gradient-of-ψ condition `∇ψ(λ) = c`) is *equivalent* to
the gibbs ansatz satisfying the same constraint as `P`. This is the formal
content of "KKT stationarity in `λ`". -/
@[entry_point]
lemma KKT_moment_match_iff_gibbs_moment_match [Nonempty α]
    (f : Fin k → α → ℝ) (c : Fin k → ℝ) (lam : Fin k → ℝ) :
    (∀ i, ∑ x, expFamilyDist f lam x * f i x = c i)
      ↔ (∀ i, ∑ x, gibbsPmf f lam x * f i x = c i) := by
  rw [show expFamilyDist f lam = gibbsPmf f lam
        from expFamilyDist_eq_gibbsPmf f lam]


/-! ## Section 9 — Stationarity expansion: log-pmf is affine in features -/

/-! ## Section 10 — Tier 3 stretch: zero-multiplier reduction = uniform -/

/-- **KKT zero-multiplier reduction**: `expFamilyDist f 0 = expFamilyDist g 0`
for any features `f`, `g` (both equal to the uniform pmf). This is the
unconstrained-Lagrangian degenerate case `λ = 0`. -/
@[entry_point]
lemma expFamilyDist_lam_zero_eq [Nonempty α]
    (f : Fin k → α → ℝ) :
    expFamilyDist f (fun _ => (0 : ℝ)) = fun _ => (1 : ℝ) / Fintype.card α := by
  funext x
  unfold expFamilyDist logPartitionψ gibbsZ
  have h_num_zero : (∑ i, (fun _ : Fin k => (0 : ℝ)) i * f i x) = 0 := by simp
  have h_den : (∑ y, Real.exp (∑ i, (fun _ : Fin k => (0 : ℝ)) i * f i y))
                = (Fintype.card α : ℝ) := by
    have h_each : ∀ y : α,
        Real.exp (∑ i, (fun _ : Fin k => (0 : ℝ)) i * f i y) = 1 := by
      intro y
      have h_sum : (∑ i, (fun _ : Fin k => (0 : ℝ)) i * f i y) = 0 := by simp
      rw [h_sum, Real.exp_zero]
    rw [Finset.sum_congr rfl (fun y _ => h_each y)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [h_num_zero, h_den]
  -- Goal: exp (0 - log (Fintype.card α : ℝ)) = 1 / Fintype.card α
  have hN_pos : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [zero_sub, Real.exp_neg, Real.exp_log hN_pos, one_div]

end InformationTheory.Shannon.MaxEntropyConstrainedKKT
