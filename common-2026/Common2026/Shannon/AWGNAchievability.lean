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

本 hypothesis を discharge するのは別 plan
(`awgn-achievability-typicality-plan.md`)。本 plan では definitionally exposed。-/
def IsAwgnTypicalityHypothesis (P : ℝ) (N : ℝ≥0)
    (h_meas : IsAwgnChannelMeasurable N) : Prop :=
  ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) →
    ∀ {ε : ℝ}, 0 < ε →
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P),
          ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε

/-! ## Achievability — `awgn_achievability` (F-1 hypothesis pass-through) -/

/-- **AWGN achievability theorem (Cover-Thomas 9.1.1)**.

For any rate `R < C = (1/2) log(1+P/N)` and target error probability `ε > 0`,
there exists `N₀` such that for every block length `n ≥ N₀`, there is an
`AwgnCode` (output power ≤ `P`, measurable decoder) with `M ≥ ⌈exp(nR)⌉`
messages whose per-message error probability is below `ε`.

**F-1 hypothesis pass-through form** (sphere packing / continuous joint
typicality は `IsAwgnTypicalityHypothesis P N h_meas` predicate に集約)。
discharging it は `awgn-achievability-typicality-plan.md` へ。

L-S2 / L-C2 / L-F1+L-F2 と同型の薄い wrapper。-/
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
