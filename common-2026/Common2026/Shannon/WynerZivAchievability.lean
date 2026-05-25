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

* `wyner_ziv_rate_le_of_gt` (旧 `wyner_ziv_achievability_rate`): `R > wynerZivRatePmf`
  から `wynerZivRatePmf ≤ R` への ordered-field lift micro-lemma。Wave 14 rename
  で operational achievability content の name laundering を解消。Tier 1 candidate。
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

/-- **`<` → `≤` ordered-field lift specialised to `wynerZivRatePmf`**.

Micro-lemma: strict inequality `R > wynerZivRatePmf U P_XY d D` lifts to
non-strict `wynerZivRatePmf U P_XY d D ≤ R` via `le_of_lt`.  Plain
ordered-field content, **no operational achievability claim**.  The
operational random-binning + AEP + Markov / Cover–Thomas 15.9.1 content
lives entirely in `wyner_ziv_achievability_existence` below.

History: this declaration was previously named `wyner_ziv_achievability_rate`
with a long tier-5 migration history (`defect:circular` → `defect:false-statement`
→ Phase D-3 (Wave 13) constructive recovery `:= le_of_lt h_R_gt`).  Wave 13
independent honesty audit (2026-05-26) verdict: the `_achievability_*` name
prefix laundered a pure `< → ≤` lift as operational content
(`defect:degenerate` + `name-laundering-alias`).  Wave 14 orchestrator
escalation resolution: **rename to `wyner_ziv_rate_le_of_gt`** preserving
the constructive recovery body (Tier 1 candidate), zero Lean consumers
unaffected.

Wave 14 independent honesty audit (2026-05-26, fresh subagent verdict)
— **pass (Tier 1)**.  Doctrine check:
* Signature: hypothesis `R > wynerZivRatePmf …` is strictly stronger than
  conclusion `wynerZivRatePmf … ≤ R`, consumed via `le_of_lt` (not
  circular identity `:= h`).
* Body: 1-step `le_of_lt h_R_gt` is a genuine ordered-field lift, no
  hidden sorry / residual / `@audit:*`.
* Name + docstring: new prefix `_rate_le_of_gt` literally describes the
  `< → ≤` form; docstring verbatim renounces operational content
  ("no operational achievability claim").  Wave 13 root causes
  (`_achievability_*` prefix + operational name laundering) are
  eliminated.
* Joint core-reconstruction test: granting `h_R_gt` hands exactly the
  micro-lemma the theorem claims (and no more); load-bearing in the
  trivial sense that any 1-step lift is, but the lemma's name +
  docstring acknowledge this scope, so honest by design.
`@audit:ok` -/
theorem wyner_ziv_rate_le_of_gt
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
