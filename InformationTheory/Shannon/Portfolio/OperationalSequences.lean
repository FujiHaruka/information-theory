import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Portfolio.Basic
import InformationTheory.Shannon.Gambling.OperationalSequences
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic

/-!
# Operational log-optimal portfolios over i.i.d. markets (Cover–Thomas §16.3)

For an i.i.d. sequence of market outcomes `As : ℕ → Ω → α` on a finite alphabet `α`, an
investor reinvesting all wealth with a fixed rebalanced portfolio `b : Fin m → ℝ` and
price relatives `X : α → (Fin m → ℝ)` accumulates wealth whose log grows like
`∑ i, log (S_b (As i))`. The **operational** (sequence-level) result is that the
time-averaged log-wealth growth converges almost surely to the growth rate
`W(b) = growthRate p X b`, where `p` is the law of a single outcome `As 0`. This is the
non-diagonal generalization of the horse-race operational theorem
`InformationTheory.Shannon.Gambling.seqLogWealth_div_tendsto_doublingRate` (recovered by
the diagonal choice `X a i = o i · [a = i]`), and the strong-law counterpart of the
single-shot log-optimality theorem `logOptimal_of_kuhnTucker`.

## Main definitions

* `portfolioLogReturn` — the alphabet-side per-period log return `g a = log (S_b a)`.
* `seqLogWealth` — the log-wealth after `n` periods, `log S_n = ∑ i, portfolioLogReturn X b (As i)`.

## Main statements

* `seqLogWealth_div_tendsto_growthRate` — §16.3: for a fixed portfolio `b`, `(1/n)·log S_n`
  converges almost surely to `growthRate (lawPmf μ (As 0)) X b`.
* `seqLogWealth_asymptotically_optimal` — a log-optimal (Kuhn–Tucker) portfolio `bs` is
  asymptotically optimal: almost surely both growth rates exist and the arbitrary portfolio
  `b` does not beat `bs`.

## Implementation notes

The proof reuses the strong law `ProbabilityTheory.strong_law_ae_real` applied to the
sequence `fun i ω ↦ portfolioLogReturn X b (As i ω)`, exactly as the gambling mirror
applies it to the horse-race log return. The only non-mechanical step is identifying the
strong-law limit `μ[portfolioLogReturn X b ∘ As 0]` with `growthRate (lawPmf μ (As 0)) X b`,
via the bet-independent discrete-expectation bridge
`InformationTheory.Shannon.Gambling.integral_comp_law`. The deterministic dominance
`W(b) ≤ W(bs)` is the `IsMaxOn` conclusion of the static `logOptimal_of_kuhnTucker`
applied to `b`. The non-diagonal difficulty (log-optimal portfolios are not proportional)
is fully absorbed by that static theorem; the strong-law skeleton is bet-independent.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Section 16.3.
-/

namespace InformationTheory.Shannon.Portfolio

open MeasureTheory ProbabilityTheory Filter Real
open scoped BigOperators Topology
open InformationTheory.Shannon.Gambling (lawPmf integral_comp_law lawPmf_mem_stdSimplex)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
variable {m : ℕ}

/-- The alphabet-side per-period log return `g a = log (S_b a)`: the log growth factor of
wealth when the outcome is `a`, the portfolio is `b`, and the price relatives are `X`. -/
noncomputable def portfolioLogReturn (X : α → Fin m → ℝ) (b : Fin m → ℝ) : α → ℝ :=
  fun a ↦ Real.log (wealthRelative X b a)

/-- The log-wealth after `n` periods starting from unit wealth,
`log S_n = ∑ i < n, portfolioLogReturn X b (As i ω)`. -/
noncomputable def seqLogWealth (X : α → Fin m → ℝ) (b : Fin m → ℝ) (As : ℕ → Ω → α) (n : ℕ) :
    Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range n, portfolioLogReturn X b (As i ω)

lemma measurable_portfolioLogReturn (X : α → Fin m → ℝ) (b : Fin m → ℝ) :
    Measurable (portfolioLogReturn X b) :=
  measurable_of_finite _

lemma integrable_portfolioLogReturn_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : α → Fin m → ℝ) (b : Fin m → ℝ) (As : ℕ → Ω → α) (hAs : ∀ i, Measurable (As i)) :
    Integrable (fun ω ↦ portfolioLogReturn X b (As 0 ω)) μ := by
  have : IsProbabilityMeasure (μ.map (As 0)) :=
    Measure.isProbabilityMeasure_map (hAs 0).aemeasurable
  have h_int : Integrable (portfolioLogReturn X b) (μ.map (As 0)) := Integrable.of_finite
  exact h_int.comp_measurable (hAs 0)

lemma identDistrib_portfolioLogReturn (μ : Measure Ω) (X : α → Fin m → ℝ) (b : Fin m → ℝ)
    (As : ℕ → Ω → α) (hident : ∀ i, IdentDistrib (As i) (As 0) μ μ) (i : ℕ) :
    IdentDistrib (fun ω ↦ portfolioLogReturn X b (As i ω))
      (fun ω ↦ portfolioLogReturn X b (As 0 ω)) μ μ :=
  (hident i).comp (measurable_portfolioLogReturn X b)

lemma indepFun_portfolioLogReturn (μ : Measure Ω) (X : α → Fin m → ℝ) (b : Fin m → ℝ)
    (As : ℕ → Ω → α) (hindep : Pairwise fun i j ↦ As i ⟂ᵢ[μ] As j) :
    Pairwise fun i j ↦ (fun ω ↦ portfolioLogReturn X b (As i ω))
      ⟂ᵢ[μ] (fun ω ↦ portfolioLogReturn X b (As j ω)) := by
  intro i j hij
  exact (hindep hij).comp (measurable_portfolioLogReturn X b) (measurable_portfolioLogReturn X b)

/-- **Operational log-optimal portfolio theorem** (Cover–Thomas §16.3): for an i.i.d.
market sequence `As`, a fixed rebalanced portfolio `b` under price relatives `X`, the
time-averaged log-wealth growth `(1/n)·log S_n` converges almost surely to the growth rate
`growthRate (lawPmf μ (As 0)) X b`, where `lawPmf μ (As 0)` is the law of a single
outcome.
@audit:ok — sorryAx-free (`[propext, Classical.choice,
Quot.sound]`). `lawPmf μ (As 0)` is a genuine definitional binding (pushforward law of
`As 0`), not a bundled `(h : μ[…] = growthRate …)` slot. `hAs`/`hindep`/`hident` and
`[IsProbabilityMeasure μ]` are the SLLN regularity preconditions. Routes through
`strong_law_ae_real` + the expectation→pmf bridge `integral_comp_law`; non-circular. -/
@[entry_point]
theorem seqLogWealth_div_tendsto_growthRate
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : α → Fin m → ℝ) (b : Fin m → ℝ)
    (As : ℕ → Ω → α) (hAs : ∀ i, Measurable (As i))
    (hindep : Pairwise fun i j ↦ As i ⟂ᵢ[μ] As j)
    (hident : ∀ i, IdentDistrib (As i) (As 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ seqLogWealth X b As n ω / n) atTop
      (𝓝 (growthRate (lawPmf μ (As 0)) X b)) := by
  -- Apply the strong law to `X i := portfolioLogReturn X b ∘ As i`, then identify the limit.
  have hint : Integrable (fun ω ↦ portfolioLogReturn X b (As 0 ω)) μ :=
    integrable_portfolioLogReturn_zero μ X b As hAs
  have hindBL := indepFun_portfolioLogReturn μ X b As hindep
  have hidBL := identDistrib_portfolioLogReturn μ X b As hident
  have h_lln := strong_law_ae_real (fun i ω ↦ portfolioLogReturn X b (As i ω)) hint hindBL hidBL
  -- Identify the strong-law limit `μ[portfolioLogReturn X b ∘ As 0]` with the growth rate.
  have h_lim : ∫ ω, portfolioLogReturn X b (As 0 ω) ∂μ = growthRate (lawPmf μ (As 0)) X b := by
    rw [integral_comp_law μ (As 0) (hAs 0) (portfolioLogReturn X b)]
    rfl
  filter_upwards [h_lln] with ω hω
  simpa only [seqLogWealth, h_lim] using hω

/-- **Operational asymptotic optimality** (Cover–Thomas §16.3): a log-optimal
(Kuhn–Tucker) portfolio `bs` is asymptotically optimal. Almost surely both the arbitrary
portfolio `b` and `bs` have a growth rate, and the arbitrary portfolio does not beat `bs`.
@audit:ok — sorryAx-free (`[propext, Classical.choice,
Quot.sound]`). `hKT` is the first-order Kuhn–Tucker condition on `bs` alone (gradient
inequalities `∀ i, ∑ a, p a · X a i / S_bs(a) ≤ 1`), NOT the conclusion `W(b) ≤ W(bs)`:
it is bridged to global optimality by the concavity/Jensen content proved sorry-free in
`logOptimal_of_kuhnTucker` (Cover–Thomas Thm 16.2.1). Non-vacuous — a non-log-optimal `bs`
fails `hKT` (by `kuhnTucker_of_logOptimal`), so the hypothesis genuinely pins the optimum
rather than smuggling the comparison. `hb`/`hbs` are simplex membership, `hpos` is the
log-domain positivity precondition; the two a.s. conjuncts come from H1 (×2) and the third
deterministic inequality from the static theorem — no conjunct is passed as a hypothesis. -/
@[entry_point]
theorem seqLogWealth_asymptotically_optimal
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : α → Fin m → ℝ) (b bs : Fin m → ℝ)
    (hb : b ∈ stdSimplex ℝ (Fin m)) (hbs : bs ∈ stdSimplex ℝ (Fin m))
    (hpos : ∀ a, ∀ c ∈ stdSimplex ℝ (Fin m), 0 < wealthRelative X c a)
    (As : ℕ → Ω → α) (hAs : ∀ i, Measurable (As i))
    (hindep : Pairwise fun i j ↦ As i ⟂ᵢ[μ] As j)
    (hident : ∀ i, IdentDistrib (As i) (As 0) μ μ)
    (hKT : ∀ i, (∑ a, lawPmf μ (As 0) a * X a i / wealthRelative X bs a) ≤ 1) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ seqLogWealth X b As n ω / n) atTop
        (𝓝 (growthRate (lawPmf μ (As 0)) X b)) ∧
      Tendsto (fun n ↦ seqLogWealth X bs As n ω / n) atTop
        (𝓝 (growthRate (lawPmf μ (As 0)) X bs)) ∧
      growthRate (lawPmf μ (As 0)) X b ≤ growthRate (lawPmf μ (As 0)) X bs := by
  have hp := lawPmf_mem_stdSimplex μ (As 0) (hAs 0)
  have h_b := seqLogWealth_div_tendsto_growthRate μ X b As hAs hindep hident
  have h_bs := seqLogWealth_div_tendsto_growthRate μ X bs As hAs hindep hident
  -- The deterministic dominance `W(b) ≤ W(bs)` is the `IsMaxOn` conclusion of the static
  -- log-optimality theorem for the Kuhn–Tucker portfolio `bs`, applied to `b`.
  have h_opt := logOptimal_of_kuhnTucker (lawPmf μ (As 0)) X bs hp hbs hpos hKT
  filter_upwards [h_b, h_bs] with ω hωb hωbs
  exact ⟨hωb, hωbs, h_opt hb⟩

end InformationTheory.Shannon.Portfolio
