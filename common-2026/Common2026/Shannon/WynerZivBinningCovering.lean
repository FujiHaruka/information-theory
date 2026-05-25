import Common2026.Shannon.WynerZivBinningBody

/-!
# Wyner–Ziv L-WZ1 binning body — covering / packing decomposition
# (T3-D wave7 gap-close)

This file refines the `WynerZivBinningBody.lean` (wave5, 613 行) random-binning
body by **decomposing the two-rate condition into two independent
sub-predicates** following the standard information-theoretic pattern:

* **Covering bound** (rate-`R₁` side): the random codebook of size
  `2^{n R₁}` covers the source typical set with high probability. This
  controls `μ(E_typ)` — the probability that the chosen codeword
  `u^n` *fails* to be jointly typical with the source `(x^n, y^n)`.
* **Packing bound** (rate-`R₂` side): the binning of `2^{n R₁}` codewords
  into `2^{n R₂}` bins has *low* alias collision probability within each
  bin. This controls `μ(E_bin)` — the probability that some non-true
  codeword in the same bin happens to be jointly typical with the
  side-info.

The Wyner–Ziv binning rate then *equals* `R₁ − R₂` (the codebook rate minus
the bin rate). Cover–Thomas §15.9 uses exactly this decomposition (also
shared by lossy source coding with side information, Gel'fand–Pinsker, etc.)

## Scope

* **`IsWynerZivBinningCovering R₁ ε₁ μ ...`** — predicate form of the
  covering bound: under the random codebook (parameterised externally), the
  probability that the true `(u^n, y^n)` is not jointly typical is at most
  `ε₁`. This is exactly `μ.real (wzError_E_typ ...) ≤ ε₁` in the present
  abstraction; the *rate parameter* `R₁` enters when the actual codebook
  construction discharges this predicate via AEP.
* **`IsWynerZivBinningPacking R₂ ε₂ μ ...`** — predicate form of the
  packing bound: under the random binning, the probability that some
  alias `u' ≠ u^n` in the same bin is jointly typical with `y^n` is at
  most `ε₂`. This is `μ.real (wzError_E_bin ...) ≤ ε₂`. The packing
  rate enters via the slice cardinality / `M = 2^{n R₂}` relationship,
  discharged by a separate seed.
* **`wyner_ziv_binning_via_covering_packing`** — the main composition
  theorem: given both predicates, the decoder failure probability is at
  most `ε₁ + ε₂`. This is the standard "covering + packing ⇒ achievability"
  pattern, and reduces in two lines to `wzAchievability_random_binning_body`.
* **`wynerZivBinningBody_of_covering_packing`** — the bridge re-export:
  the same statement repackaged in the exact shape consumed by downstream
  achievability theorems, including the existence-of-codes form.

## 撤退ライン

* **Actual covering / packing discharge** — `IsWynerZivBinningCovering` and
  `IsWynerZivBinningPacking` are predicate pass-throughs. Their genuine
  discharge requires:
  - covering: AEP on the random codebook (Markov inequality + Chebyshev on
    the expected number of typical codewords),
  - packing: union bound + binning collision probability `1/M` + slice
    cardinality bound `|T^n_{U|Y}| ≤ exp(n(H(U|Y)+2ε))`.
  Both are deferred to separate seeds in the wave6/wave7 discharge plan.
* **Rate parameters `R₁, R₂` as bookkeeping** — the predicates carry `R₁`
  and `R₂` purely as documentation; the underlying inequalities are on
  the *error probabilities* `ε₁, ε₂`. Down-stream code can instantiate
  with concrete `ε_i := f(R_i)` functions when the AEP / cardinality
  bounds are filled in.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

/-! ## Section 1 — Covering predicate -/

section Covering

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]

/-- **Wyner–Ziv random-codebook covering predicate.**

Given a probability measure `μ` on the sample space `Ω`, random sequences
`Us : Ω → Fin n → U` (the auxiliary codeword) and `Ys : Ω → Fin n → β`
(the side info), a jointly-typicality predicate `JT`, a (rate-`R₁`)
**bookkeeping rate parameter `R₁`**, and an error tolerance `ε₁ ≥ 0`,
the codebook is said to **cover** at rate `R₁` if the probability that
the chosen codeword fails to be jointly typical with the side info is
at most `ε₁`:

```
μ.real { ω | ¬ JT (Us ω, Ys ω) } ≤ ε₁.
```

This is `μ.real (wzError_E_typ Us Ys JT) ≤ ε₁`. The rate `R₁` is carried
as documentation; the actual covering discharge (via AEP + Markov on the
random codebook size `M_C = ⌈exp(n R₁)⌉`) is deferred to a separate seed.

`@audit:retract-candidate(load-bearing-predicate)` — load-bearing
hypothesis-form predicate marked for eventual deletion once the in-family
discharge plan (`wyner-ziv-discharge-moonshot-plan`) closes its in-family
consumers.  **Cross-family consumer present**:
`RelayCFBinningBody.lean:127` re-namespaces this predicate for the Relay
CF (compress-and-forward) family. Predicate deletion is therefore blocked
until the Relay family runs its own sorry-migration sweep; the candidate
marker stays as bookkeeping. -/
def IsWynerZivBinningCovering
    (_R₁ : ℝ) (ε₁ : ℝ)
    (μ : Measure Ω) {n : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop) : Prop :=
  μ.real (wzError_E_typ (n := n) Us Ys JT) ≤ ε₁

/-- Unfolding lemma for `IsWynerZivBinningCovering`. -/
lemma IsWynerZivBinningCovering_def
    {R₁ ε₁ : ℝ}
    {μ : Measure Ω} {n : ℕ}
    {Us : Ω → Fin n → U} {Ys : Ω → Fin n → β}
    {JT : (Fin n → U) × (Fin n → β) → Prop} :
    IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT ↔
      μ.real (wzError_E_typ (n := n) Us Ys JT) ≤ ε₁ := Iff.rfl

/-- The covering predicate is monotone in the error tolerance: a tighter bound
implies any looser bound. -/
lemma IsWynerZivBinningCovering.mono
    {R₁ ε₁ ε₁' : ℝ}
    {μ : Measure Ω} {n : ℕ}
    {Us : Ω → Fin n → U} {Ys : Ω → Fin n → β}
    {JT : (Fin n → U) × (Fin n → β) → Prop}
    (h : IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT)
    (h_le : ε₁ ≤ ε₁') :
    IsWynerZivBinningCovering R₁ ε₁' μ Us Ys JT :=
  le_trans h h_le

/-- The covering predicate is independent of the rate-bookkeeping `R₁`:
substituting `R₁ ↦ R₁'` leaves the underlying probability bound unchanged. -/
lemma IsWynerZivBinningCovering.rate_irrelevant
    {R₁ R₁' ε₁ : ℝ}
    {μ : Measure Ω} {n : ℕ}
    {Us : Ω → Fin n → U} {Ys : Ω → Fin n → β}
    {JT : (Fin n → U) × (Fin n → β) → Prop}
    (h : IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT) :
    IsWynerZivBinningCovering R₁' ε₁ μ Us Ys JT := h

end Covering

/-! ## Section 2 — Packing predicate -/

section Packing

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]

/-- **Wyner–Ziv random-binning packing predicate.**

Given a probability measure `μ` on `Ω`, random sequences `Us`, `Ys`, a joint
typicality predicate `JT`, a (deterministic) binning function `f_U`, a
bookkeeping rate parameter `R₂` (the binning rate, with `M = 2^{n R₂}`),
and an error tolerance `ε₂ ≥ 0`, the binning is said to **pack** at rate
`R₂` if the probability that some alias `u' ≠ Us ω` in the same bin is
jointly typical with `Ys ω` is at most `ε₂`:

```
μ.real { ω | ∃ u' ≠ Us ω, f_U u' = f_U (Us ω) ∧ JT (u', Ys ω) } ≤ ε₂.
```

This is `μ.real (wzError_E_bin Us Ys JT f_U) ≤ ε₂`. The rate `R₂` is carried
as bookkeeping; the actual packing discharge (union bound + `1/M` collision
+ slice cardinality bound) is deferred to a separate seed.

`@audit:retract-candidate(load-bearing-predicate)` — load-bearing
hypothesis-form predicate marked for eventual deletion once the in-family
discharge plan (`wyner-ziv-discharge-moonshot-plan`) closes its in-family
consumers.  **Cross-family consumer present**:
`RelayCFBinningBody.lean:195` re-namespaces this predicate for the Relay
CF (compress-and-forward) family. Predicate deletion is therefore blocked
until the Relay family runs its own sorry-migration sweep; the candidate
marker stays as bookkeeping. -/
def IsWynerZivBinningPacking
    (_R₂ : ℝ) (ε₂ : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (f_U : (Fin n → U) → Fin M) : Prop :=
  μ.real (wzError_E_bin (n := n) Us Ys JT f_U) ≤ ε₂

/-- Unfolding lemma for `IsWynerZivBinningPacking`. -/
lemma IsWynerZivBinningPacking_def
    {R₂ ε₂ : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Us : Ω → Fin n → U} {Ys : Ω → Fin n → β}
    {JT : (Fin n → U) × (Fin n → β) → Prop}
    {f_U : (Fin n → U) → Fin M} :
    IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U ↔
      μ.real (wzError_E_bin (n := n) Us Ys JT f_U) ≤ ε₂ := Iff.rfl

/-- The packing predicate is monotone in the error tolerance. -/
lemma IsWynerZivBinningPacking.mono
    {R₂ ε₂ ε₂' : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Us : Ω → Fin n → U} {Ys : Ω → Fin n → β}
    {JT : (Fin n → U) × (Fin n → β) → Prop}
    {f_U : (Fin n → U) → Fin M}
    (h : IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U)
    (h_le : ε₂ ≤ ε₂') :
    IsWynerZivBinningPacking R₂ ε₂' μ Us Ys JT f_U :=
  le_trans h h_le

/-- The packing predicate is independent of the rate-bookkeeping `R₂`. -/
lemma IsWynerZivBinningPacking.rate_irrelevant
    {R₂ R₂' ε₂ : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Us : Ω → Fin n → U} {Ys : Ω → Fin n → β}
    {JT : (Fin n → U) × (Fin n → β) → Prop}
    {f_U : (Fin n → U) → Fin M}
    (h : IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U) :
    IsWynerZivBinningPacking R₂' ε₂ μ Us Ys JT f_U := h

end Packing

/-! ## Section 3 — Decoder failure decomposition via covering / packing

This section is the main bridge: the two predicates above, taken together,
imply the WynerZivBinningBody decoder-failure bound `ε₁ + ε₂`. The proof
is a direct application of `wzAchievability_random_binning_body` —
covering ⇒ ε_typ bound, packing ⇒ ε_bin bound.
-/

section Bridge

variable {Ω U β γ : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]
variable [MeasurableSpace γ]

/-- **Wyner–Ziv binning via covering + packing — main composition.**

Given:
* `h_cov` — `IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT` (codebook covers
  source typical set with failure prob `≤ ε₁`),
* `h_pack` — `IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U` (random binning
  has alias collision prob `≤ ε₂`),
* measurability of `E_typ`, `E_bin`, and the decoder-failure set,

the decoder-failure probability is at most `ε₁ + ε₂`. The Wyner–Ziv binning
rate is `R = R₁ − R₂`; the rate parameters themselves are encoded only as
bookkeeping in the predicates (the underlying probability bounds are what
matter for this lemma).

The proof: covering ⇒ `μ.real(E_typ) ≤ ε₁`, packing ⇒ `μ.real(E_bin) ≤ ε₂`,
then apply `wzAchievability_random_binning_body` for the union bound.
This is precisely the standard "covering + packing" pattern.

Phase 1.5 (sorry-migration): body retreated to `sorry`. The previous body
reduced (via `IsWynerZivBinningCovering_def` / `..._Packing_def` defequal
unfolds) to a call into `wzAchievability_random_binning_body` (itself
load-bearing on `h_typ_prob` / `h_bin_prob`, sorry-migrated below in the
same Phase). Closure responsibility is parked on the discharge plan.

Cross-family consumer note: `RelayCFBinningBody.lean:348` calls this
declaration directly, so it now picks up a transitive `sorry`. The Relay
file is **out of scope** for this Wyner–Ziv sweep — the Relay family's
own sorry-migration sweep will handle the docstring annotation.

`@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
theorem wyner_ziv_binning_via_covering_packing
    [Nonempty β] [Nonempty γ]
    {R₁ R₂ ε₁ ε₂ : ℝ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {n M : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (f_U : (Fin n → U) → Fin M)
    (f : U × β → γ)
    (h_meas_typ : MeasurableSet (wzError_E_typ (n := n) Us Ys JT))
    (h_meas_bin : MeasurableSet (wzError_E_bin (n := n) Us Ys JT f_U))
    (h_meas_fail :
      MeasurableSet { ω : Ω |
        wzJointlyTypicalDecoderBody f_U JT f (f_U (Us ω), Ys ω)
          ≠ fun i => f (Us ω i, Ys ω i) })
    (h_cov : IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT)
    (h_pack : IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U) :
    μ.real { ω : Ω |
        wzJointlyTypicalDecoderBody f_U JT f (f_U (Us ω), Ys ω)
          ≠ fun i => f (Us ω i, Ys ω i) }
      ≤ ε₁ + ε₂ := by
  sorry

/-- **Bridge to `WynerZivBinningBody`** — same statement re-exported with the
implicit bookkeeping that `R = R₁ − R₂` is the Wyner–Ziv binning rate. This
is the form consumed by downstream achievability composition.

Phase 1.5 (sorry-migration): pure re-export forwarder to
`wyner_ziv_binning_via_covering_packing` (now `sorry`). Body retreated to
`sorry`; closure responsibility lives on the same plan slug.

`@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
theorem wynerZivBinningBody_of_covering_packing
    [Nonempty β] [Nonempty γ]
    {R₁ R₂ ε₁ ε₂ : ℝ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {n M : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (f_U : (Fin n → U) → Fin M)
    (f : U × β → γ)
    (h_meas_typ : MeasurableSet (wzError_E_typ (n := n) Us Ys JT))
    (h_meas_bin : MeasurableSet (wzError_E_bin (n := n) Us Ys JT f_U))
    (h_meas_fail :
      MeasurableSet { ω : Ω |
        wzJointlyTypicalDecoderBody f_U JT f (f_U (Us ω), Ys ω)
          ≠ fun i => f (Us ω i, Ys ω i) })
    (h_cov : IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT)
    (h_pack : IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U) :
    μ.real { ω : Ω |
        wzJointlyTypicalDecoderBody f_U JT f (f_U (Us ω), Ys ω)
          ≠ fun i => f (Us ω i, Ys ω i) }
      ≤ ε₁ + ε₂ := by
  sorry

end Bridge

/-! ## Section 4 — Existence form: covering + packing ⇒ vanishing error rate

A common downstream consumption: rather than a single bound `ε₁ + ε₂`, we
package an *asymptotic* form — "for every ε > 0 there is N such that for
n ≥ N the covering + packing both hold with ε_i ≤ ε/2 and the binning rate
is `R₁ − R₂`". This is the existence pattern that the public achievability
theorem `wyner_ziv_achievability_existence` consumes.
-/

section ExistenceForm

variable {Ω U β γ : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]
variable [MeasurableSpace γ]

/-- **Asymptotic covering + packing ⇒ asymptotic decoder failure → 0.**

Given an existence-form covering and packing hypothesis (a sequence `n ↦
(Us_n, Ys_n, f_U_n, ε_n)` together with measurability and predicate
guarantees), produce the existence-form decoder failure bound. This is
exactly the shape consumed by `wyner_ziv_achievability_existence`.

Phase 1.5 (sorry-migration): body retreated to `sorry`. `h_asymp` is an
existence-form bundling of the covering + packing predicates at every
block length — load-bearing. The previous body wrapped
`wyner_ziv_binning_via_covering_packing` (now also `sorry`) inside the
existence quantifier; closure responsibility is parked on the discharge
plan.

`@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
theorem wyner_ziv_binning_existence_of_covering_packing
    [Nonempty β] [Nonempty γ]
    {R₁ R₂ : ℝ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (JT : ∀ n : ℕ, (Fin n → U) × (Fin n → β) → Prop)
    (h_asymp :
      ∀ ε > (0 : ℝ),
        ∃ N : ℕ, ∀ n ≥ N,
          ∃ (M : ℕ)
            (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
            (f_U : (Fin n → U) → Fin M) (f : U × β → γ)
            (ε₁ ε₂ : ℝ),
            ε₁ + ε₂ ≤ ε
              ∧ MeasurableSet (wzError_E_typ (n := n) Us Ys (JT n))
              ∧ MeasurableSet (wzError_E_bin (n := n) Us Ys (JT n) f_U)
              ∧ MeasurableSet { ω : Ω |
                  wzJointlyTypicalDecoderBody f_U (JT n) f (f_U (Us ω), Ys ω)
                    ≠ fun i => f (Us ω i, Ys ω i) }
              ∧ IsWynerZivBinningCovering R₁ ε₁ μ Us Ys (JT n)
              ∧ IsWynerZivBinningPacking R₂ ε₂ μ Us Ys (JT n) f_U) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ)
          (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
          (f_U : (Fin n → U) → Fin M) (f : U × β → γ),
          μ.real { ω : Ω |
              wzJointlyTypicalDecoderBody f_U (JT n) f (f_U (Us ω), Ys ω)
                ≠ fun i => f (Us ω i, Ys ω i) }
            ≤ ε := by
  sorry

end ExistenceForm

/-! ## Section 5 — Predicate combinators

Small helper lemmas that combine the covering and packing predicates into
a single "joint achievability" predicate, useful when downstream code
wants to thread a single hypothesis through. Pure repackaging — no new
information-theoretic content.
-/

section Combinators

variable {Ω U β : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]

/-- **Joint covering + packing predicate.** A single conjunction of the two
sub-predicates, useful as a packaged hypothesis.

`@audit:retract-candidate(load-bearing-predicate)` — load-bearing
hypothesis-form (joint) predicate marked for eventual deletion once the
in-family discharge plan (`wyner-ziv-discharge-moonshot-plan`) closes its
in-family consumers.  **Cross-family consumer present**:
`RelayCFBinningBody.lean:262` re-namespaces this predicate for the Relay
CF (compress-and-forward) family. Predicate deletion is therefore blocked
until the Relay family runs its own sorry-migration sweep; the candidate
marker stays as bookkeeping. -/
def IsWynerZivBinningAchievable
    (R₁ R₂ ε₁ ε₂ : ℝ)
    (μ : Measure Ω) {n M : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (f_U : (Fin n → U) → Fin M) : Prop :=
  IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT
    ∧ IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U

/-- Unfolding lemma. -/
lemma IsWynerZivBinningAchievable_def
    {R₁ R₂ ε₁ ε₂ : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Us : Ω → Fin n → U} {Ys : Ω → Fin n → β}
    {JT : (Fin n → U) × (Fin n → β) → Prop}
    {f_U : (Fin n → U) → Fin M} :
    IsWynerZivBinningAchievable R₁ R₂ ε₁ ε₂ μ Us Ys JT f_U ↔
      IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT
        ∧ IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U := Iff.rfl

/-- Build the joint predicate from the two pieces. -/
lemma IsWynerZivBinningAchievable.mk
    {R₁ R₂ ε₁ ε₂ : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Us : Ω → Fin n → U} {Ys : Ω → Fin n → β}
    {JT : (Fin n → U) × (Fin n → β) → Prop}
    {f_U : (Fin n → U) → Fin M}
    (h_cov : IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT)
    (h_pack : IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U) :
    IsWynerZivBinningAchievable R₁ R₂ ε₁ ε₂ μ Us Ys JT f_U :=
  ⟨h_cov, h_pack⟩

/-- Extract the covering side from the joint predicate. -/
lemma IsWynerZivBinningAchievable.covering
    {R₁ R₂ ε₁ ε₂ : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Us : Ω → Fin n → U} {Ys : Ω → Fin n → β}
    {JT : (Fin n → U) × (Fin n → β) → Prop}
    {f_U : (Fin n → U) → Fin M}
    (h : IsWynerZivBinningAchievable R₁ R₂ ε₁ ε₂ μ Us Ys JT f_U) :
    IsWynerZivBinningCovering R₁ ε₁ μ Us Ys JT := h.1

/-- Extract the packing side from the joint predicate. -/
lemma IsWynerZivBinningAchievable.packing
    {R₁ R₂ ε₁ ε₂ : ℝ}
    {μ : Measure Ω} {n M : ℕ}
    {Us : Ω → Fin n → U} {Ys : Ω → Fin n → β}
    {JT : (Fin n → U) × (Fin n → β) → Prop}
    {f_U : (Fin n → U) → Fin M}
    (h : IsWynerZivBinningAchievable R₁ R₂ ε₁ ε₂ μ Us Ys JT f_U) :
    IsWynerZivBinningPacking R₂ ε₂ μ Us Ys JT f_U := h.2

end Combinators

/-! ## Section 6 — Joint predicate → decoder failure bound

The joint predicate `IsWynerZivBinningAchievable` lets us re-state the
main composition theorem in a one-hypothesis shape, useful for downstream
existence theorems that already package both sub-bounds together.
-/

section JointBridge

variable {Ω U β γ : Type*} [MeasurableSpace Ω]
variable [Fintype U] [Nonempty U]
  [MeasurableSpace U] [MeasurableSingletonClass U]
variable [Fintype β] [MeasurableSpace β]
variable [MeasurableSpace γ]

/-- **Joint covering + packing predicate ⇒ decoder failure bound.** Same
content as `wyner_ziv_binning_via_covering_packing` but consuming the
single joint predicate `IsWynerZivBinningAchievable`.

Phase 1.5 (sorry-migration): body retreated to `sorry`. Pure re-export of
`wyner_ziv_binning_via_covering_packing` (now `sorry`) through the joint
predicate destructure (`h_ach.covering` / `h_ach.packing`); closure
responsibility lives on the same plan slug.

Cross-family consumer note: `IsWynerZivBinningAchievable` is re-namespaced
by `RelayCFBinningBody.lean:262`, but this particular wrapper theorem is
in-family only. Predicate retract-candidate marker on the predicate
itself remains blocked by Relay (see the predicate definition's
docstring).

`@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
theorem wyner_ziv_binning_decoder_fail_of_achievable
    [Nonempty β] [Nonempty γ]
    {R₁ R₂ ε₁ ε₂ : ℝ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {n M : ℕ}
    (Us : Ω → Fin n → U) (Ys : Ω → Fin n → β)
    (JT : (Fin n → U) × (Fin n → β) → Prop)
    (f_U : (Fin n → U) → Fin M)
    (f : U × β → γ)
    (h_meas_typ : MeasurableSet (wzError_E_typ (n := n) Us Ys JT))
    (h_meas_bin : MeasurableSet (wzError_E_bin (n := n) Us Ys JT f_U))
    (h_meas_fail :
      MeasurableSet { ω : Ω |
        wzJointlyTypicalDecoderBody f_U JT f (f_U (Us ω), Ys ω)
          ≠ fun i => f (Us ω i, Ys ω i) })
    (h_ach : IsWynerZivBinningAchievable R₁ R₂ ε₁ ε₂ μ Us Ys JT f_U) :
    μ.real { ω : Ω |
        wzJointlyTypicalDecoderBody f_U JT f (f_U (Us ω), Ys ω)
          ≠ fun i => f (Us ω i, Ys ω i) }
      ≤ ε₁ + ε₂ := by
  sorry

end JointBridge

end InformationTheory.Shannon
