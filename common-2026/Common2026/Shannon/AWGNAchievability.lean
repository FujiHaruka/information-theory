import Common2026.Shannon.AWGN

/-!
# T2-A Phase B: AWGN channel coding theorem — achievability (F-1 hypothesis form)

Cover-Thomas Ch.9.2 (sphere packing / continuous joint typicality / Gaussian
random codebook) を **撤退ライン F-1 hypothesis pass-through 形** で publish。

実体 (continuous joint typical set on `ℝⁿ × ℝⁿ`, Gaussian random codebook,
continuous AEP の 3 つの bounds, sphere volume formula) は別 plan
`docs/shannon/awgn-achievability-typicality-plan.md` (Tier 3) に defer。

本 file は `IsAwgnTypicalityHypothesis` predicate の定義 + `awgn_achievability`
の薄い wrapper のみで、Tier 1 publish が成立する範囲を表す。
T1-B Chernoff `L-S2` / T1-C Cramer `L-C2` / T2-F de Bruijn `L-F1+L-F2` と
同型 pattern。
-/

namespace InformationTheory.Shannon.AWGN

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## F-1 hypothesis predicate -/

/-- **AWGN continuous joint-typicality hypothesis** (Cover-Thomas 9.2 schema).

実体 = sphere packing on `ℝⁿ` + Gaussian random codebook + 3 つの continuous AEP
bounds (球殻 volume / Gaussian tail decay / union bound on M codewords)。

For any `R < (1/2) log(1+P/N)` and `ε > 0`, there exists `N₀` such that for
every `n ≥ N₀`, there is an `AwgnCode` with `M ≥ ⌈exp(nR)⌉` messages and per-
message error probability < ε.

**HONESTY NOTE.** This predicate is the universal-`R, ε` quantified form
of the achievability conclusion itself. The "hypothesis" is therefore
load-bearing in the strongest sense: providing it amounts to proving
the achievability theorem for all valid `R, ε` at once. The genuine
analytic content (sphere packing + random coding + AEP) is what makes
this predicate non-vacuous; that derivation is deferred to
`awgn-achievability-typicality-plan.md` (plan drafted; analytic body
pending).

`@audit:defect(circular)` `@audit:closed-by-successor(awgn-achievability-typicality-plan)` `@audit:staged(n-dim-gaussian-aep)` -/
def IsAwgnTypicalityHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∀ {ε : ℝ}, 0 < ε →
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε

/-! ## Achievability — `awgn_achievability` (F-1 hypothesis pass-through) -/

/-- **load-bearing hypothesis — NOT a discharge.**

**AWGN achievability theorem (Cover-Thomas 9.1.1)**.

For any rate `R < C = (1/2) log(1+P/N)` and target error probability `ε > 0`,
there exists `N₀` such that for every block length `n ≥ N₀`, there is an
`AwgnCode` (output power ≤ `P`, measurable decoder) with `M ≥ ⌈exp(nR)⌉`
messages whose per-message error probability is below `ε`.

**HONESTY NOTE (rebrand-B, cluster GaussianCh_circular_passthru).** The
hypothesis `h_typicality : IsAwgnTypicalityHypothesis P N h_meas` is the
universal-`R, ε` quantified form of this very conclusion — see its
definition above (`∀ {R} (hR_pos) (hR) {ε} (hε), ∃ N₀ ...`). The body
is `h_typicality hR_pos hR hε`, i.e. a single instantiation. This is
**not** a discharge of the achievability theorem; it is a re-statement
that hides the genuine analytic content (sphere packing on `ℝⁿ`,
Gaussian random codebook, three continuous-AEP bounds, union bound on
`M` codewords) inside the hypothesis. The hypothesis predicate
**carries the proof's CORE** and is the actual residual.

Discharging `IsAwgnTypicalityHypothesis` (i.e. constructing the
hypothesis from first principles rather than assuming it) is the work
of `awgn-achievability-typicality-plan.md` (plan drafted; analytic body
pending). Until that body lands, this theorem is a **load-bearing
hypothesis wrapper**, not a proven achievability result.

L-S2 / L-C2 / L-F1+L-F2 と同型の薄い wrapper (同じ honesty 状態)。

`@audit:closed-by-successor(awgn-achievability-typicality-plan)` `@residual(plan:awgn-achievability-typicality-plan)` -/
theorem awgn_achievability
    (P : ℝ) (hP : 0 < P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_typicality : IsAwgnTypicalityHypothesis P N h_meas)
    {R : ℝ} (hR_pos : 0 < R) (hR : R < (1/2) * Real.log (1 + P / (N : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
        ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε :=
  h_typicality hR_pos hR hε

end InformationTheory.Shannon.AWGN
