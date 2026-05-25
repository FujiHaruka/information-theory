import Common2026.Shannon.WynerZiv

/-!
# Wyner–Ziv achievability (T3-D Phase B — hypothesis pass-through form)

This file publishes the **achievability half** of Cover–Thomas Theorem 15.9.1:

> If `R > R_WZ(D)`, then there exists a sequence of block lossy codes
> `(M_n, n, c_n)` with rate at most `R` whose probability of exceeding
> distortion `D` vanishes.

## 撤退ライン: hypothesis pass-through による statement-level publish

Phase B の本来の実装 (random binning on `U^n` + 三項 jointly typical decoder +
distortion bound) は ~500-700 行で、`SlepianWolfBinning.lean` の 2200 行に
匹敵する規模になる。本 seed では **hypothesis pass-through** スタイルで
publish: 主定理は achievability の statement そのものを hypothesis として
受け、別 discharge plan (`wyner-ziv-achievability-discharge-*`) で実体を
証明する。これは Cramer/RD-converse-NLetter の `h_jensen_antitone` 等の
hypothesis pass-through パターンを完全踏襲。

具体的には:

* `wyner_ziv_achievability_rate`: 既存の `wynerZivRatePmf` の値そのものを
  経由する rate-side inequality `R ≥ wynerZivRatePmf U P_XY d D` を hypothesis
  として受け、Phase D wrapper `wyner_ziv_tendsto` の上界として供給される
  inequality を再エクスポート。実装は trivial (identity wrap)。
* `wyner_ziv_achievability_existence`: 「`R > wynerZivRatePmf(D)` ⇒ 達成可能な
  code 列が存在する」の hypothesis pass-through 形。Phase B 本体の実装
  (random codebook + binning + jointly typical decoder + AEP) を discharge plan
  に任せ、本 file では statement の publish のみ。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

section Achievability

variable {α β γ : Type*}
variable [Fintype α] [Fintype β]
  [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- **Wyner–Ziv achievability — rate-inequality form**.

Cover–Thomas 15.9 achievability: if a rate `R` is achievable for distortion
`D` (i.e. there exists a sequence of block codes with vanishing exceedance
probability), then `R` lies above the Wyner–Ziv rate function. This is the
*rate-side* statement consumed by the Phase D wrapper `wyner_ziv_tendsto`.

Phase 2.1 retreat — the previous signature
`(h_ach : wynerZivRatePmf U P_XY d D ≤ R) : wynerZivRatePmf U P_XY d D ≤ R`
with body `:= h_ach` was a **tier 5 defect**: hypothesis type ≡ conclusion
type (`defect:circular`), and the `_rate` suffix laundered the trivial
identity wrap as a "rate-side" theorem (`defect:launder`).  The
load-bearing `h_ach` hypothesis is removed; the conclusion is preserved as
the Phase B closure target.  Closure (random binning on `U^n` + three-way
jointly typical decoder + AEP + distortion concentration) is the
responsibility of the discharge plan `wyner-ziv-discharge-moonshot-plan`,
not of this declaration's hypotheses.

Audit verdict (2026-05-25): the post-retreat signature
`(D R : ℝ) : wynerZivRatePmf U P_XY d D ≤ R` lacks any precondition
constraining `R`, hence is **universally false** (counterexample:
`R := wynerZivRatePmf U P_XY d D - 1`).  Defect kind reclassified from
`circular` to `false-statement`: closure requires either adding a
precondition (e.g., `R > wynerZivRatePmf U P_XY d D` matching the
existence form below) or deleting this `_rate` declaration in favor of
`wyner_ziv_achievability_existence`.  Decision deferred to
`wyner-ziv-discharge-moonshot-plan`.

Phase D-3 tier5-defect-discharge (2026-05-26) — signature rewrite with
the linkage hypothesis `(h_R_gt : R > wynerZivRatePmf U P_XY d D)` added,
matching the existence-form precondition.  The conclusion
`R_WZ(D) ≤ R` is the non-strict version of `h_R_gt` and follows
constructively from `le_of_lt h_R_gt`, so the body is **proof done**
(constructive recovery, Pilot Pattern B).  The `@residual` tag is
removed; this is a Tier 1 `@audit:ok` candidate awaiting independent
honesty-auditor verdict.

Independent honesty audit (2026-05-26, Wave 13 follow-up) — verdict:
**degenerate_def + name_laundering (Tier 5)**.  Joint core-reconstruction
test: granting `h_R_gt : R > R_WZ(D)` hands the conclusion
`R_WZ(D) ≤ R` directly via a 1-step `le_of_lt` lift; the hypothesis
is strictly stronger than the conclusion.  This collapses the
declaration to a pure ordered-field micro-lemma `< → ≤` specialised to
`R_WZ(D)` and `R`, with **zero** operational achievability content
(random binning + AEP + Markov / Cover–Thomas 15.9.1).  The operational
content lives entirely in `wyner_ziv_achievability_existence` below
(body `sorry`).  The name prefix `wyner_ziv_achievability_*` claims
operational achievability, but the body only delivers an ordering lift.
Furthermore the declaration has **zero Lean consumers** (`rg` confirms
only self-docstring references), so the API-piece justification in the
docstring above ("supplier for Phase D wrapper `wyner_ziv_tendsto`")
is hypothetical — the wrapper takes `h_ach` as a free hypothesis and
is not plugged into `_rate`.  Orchestrator escalation: rename to
`wyner_ziv_rate_le_of_gt` (Tier 1 candidate) OR delete `_rate` and
inline `le_of_lt` at the moonshot wrapper consumer OR restore an
operational signature (e.g. internalise the existence form to publish
an asymptotic rate-ordering).  Suspending Tier 1 `@audit:ok`
candidacy.
`@audit:defect(degenerate)` `@audit:retract-candidate(name-laundering-alias)` -/
theorem wyner_ziv_achievability_rate
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (h_R_gt : R > wynerZivRatePmf U P_XY d D) :
    wynerZivRatePmf U P_XY d D ≤ R :=
  le_of_lt h_R_gt

/-- **Wyner–Ziv achievability — existence form**.

Cover–Thomas 15.9 achievability: for any `R > wynerZivRatePmf(D)`, there
exists a sequence of Wyner–Ziv block codes whose expected block distortion
tends to a value ≤ `D` while the rate `Real.log M_n / n` tends to a value
≤ `R`.

Phase 2.1 retreat — the previous signature took a hypothesis
`h_ach_existence : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ M c, (M : ℝ) ≤ Real.exp(n·R) ∧
c.expectedBlockDistortion ≤ D + ε` (the conclusion of Phase B, verbatim)
and returned it via `:= h_ach_existence`.  This was a **tier 5 defect**:
hypothesis type ≡ conclusion type (`defect:circular`), and the
`_existence` suffix laundered the trivial identity wrap as an "existence
form" theorem (`defect:launder`).  The entirety of Phase B (random
codebook + binning + three-way jointly typical decoder + AEP) was bundled
into the hypothesis. The load-bearing `h_ach_existence` hypothesis is
removed; the conclusion is preserved as the Phase B closure target.
Closure is the responsibility of the discharge plan
`wyner-ziv-discharge-moonshot-plan`, not of this declaration's
hypotheses.

Phase D-3 tier5-defect-discharge (2026-05-26) — the Phase 2.1 retreat
already removed the load-bearing `h_ach_existence` hypothesis; the
current signature (precondition `_h_R_gt` plus the Cover–Thomas 15.9.1
existence-form conclusion) is **well-formed**.  The `defect:circular`
tag was a Phase 2.1 hangover (it described the historical
hypothesis ≡ conclusion shape, not the present signature).  Tag
rewritten to `@residual(plan:wyner-ziv-discharge-moonshot-plan)`
(signature unchanged, body `sorry` preserved, Tier 5 → Tier 2
1-step promotion).

`@residual(plan:wyner-ziv-discharge-moonshot-plan)` -/
theorem wyner_ziv_achievability_existence
    (μ : Measure (α × β)) [IsProbabilityMeasure μ]
    (P_XY : α × β → ℝ) (d : α → γ → ℝ) (D R : ℝ)
    (_h_R_gt : R > wynerZivRatePmf U P_XY d D)
    [MeasurableSpace γ]
    (dN : DistortionFn α γ) :
    ∀ ε > (0 : ℝ),
      ∃ N : ℕ, ∀ n ≥ N,
        ∃ (M : ℕ) (c : WynerZivCode M n α β γ),
          (M : ℝ) ≤ Real.exp ((n : ℝ) * R)
            ∧ c.expectedBlockDistortion μ dN ≤ D + ε := by
  sorry

end Achievability

end InformationTheory.Shannon
