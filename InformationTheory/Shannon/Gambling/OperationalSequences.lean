import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Gambling.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Operational gambling over horse-race sequences (Cover–Thomas §6.3)

For an i.i.d. sequence of horse races `Xs : ℕ → Ω → α` on a finite alphabet `α`, a
gambler reinvesting all wealth with a fixed bet `b : α → ℝ` and odds `o : α → ℝ`
accumulates wealth whose log grows like `∑ i, log (b (Xs i) · o (Xs i))`. The
**operational** (sequence-level) result is that the time-averaged log-wealth growth
converges almost surely to the doubling rate `W(b, o, p)`, where `p` is the law of a
single race `Xs 0`. This is the strong-law counterpart of the single-shot expectation
theorem `doublingRate_le_proportional`, and a near-clone of the asymptotic
equipartition property `aep_ae`.

## Main definitions

* `betLogReturn` — the alphabet-side per-race log return `g x = log (b x · o x)`.
* `seqLogWealth` — the log-wealth after `n` races, `log S_n = ∑ i, betLogReturn b o (Xs i)`.
* `lawPmf` — the pmf (law) `p x = (μ.map X).real {x}` of a finite random variable `X`.

## Main statements

* `seqLogWealth_div_tendsto_doublingRate` — §6.3: for a general bet, `(1/n)·log S_n`
  converges almost surely to `doublingRate b o (lawPmf μ (Xs 0))`.
* `seqLogWealth_proportional_asymptotically_optimal` — the proportional (Kelly) bet
  `b = p` is asymptotically optimal: almost surely both growth rates exist and the
  arbitrary bet does not beat the Kelly bet.

## Implementation notes

The proof reuses the strong law `ProbabilityTheory.strong_law_ae_real` applied to the
sequence `fun i ω ↦ betLogReturn b o (Xs i ω)`, exactly as `aep_ae` applies it to the
log-likelihood sequence. The only non-mechanical step is identifying the strong-law
limit `μ[betLogReturn b o ∘ Xs 0]` with `doublingRate b o (lawPmf μ (Xs 0))`, via the
discrete-expectation bridge `integral_comp_law` (push-forward `integral_map` followed by
the finite-sum collapse `integral_fintype`).

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Section 6.3.
-/

namespace InformationTheory.Shannon.Gambling

open MeasureTheory ProbabilityTheory Filter Real
open scoped BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The alphabet-side per-race log return `g x = log (b x · o x)`: the log growth
factor of wealth when the race outcome is `x`, the bet is `b`, and the odds are `o`. -/
noncomputable def betLogReturn (b o : α → ℝ) : α → ℝ :=
  fun x ↦ Real.log (b x * o x)

/-- The log-wealth after `n` races starting from unit wealth,
`log S_n = ∑ i < n, betLogReturn b o (Xs i ω)`. -/
noncomputable def seqLogWealth (b o : α → ℝ) (Xs : ℕ → Ω → α) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ ∑ i ∈ Finset.range n, betLogReturn b o (Xs i ω)

/-- The pmf (law) of a finite random variable `X`, `p x = (μ.map X).real {x}`. -/
noncomputable def lawPmf (μ : Measure Ω) (X : Ω → α) : α → ℝ :=
  fun x ↦ (μ.map X).real {x}

lemma measurable_betLogReturn (b o : α → ℝ) : Measurable (betLogReturn b o) :=
  measurable_of_finite _

/-- Discrete-expectation bridge: the expectation of `g ∘ X` collapses to the finite sum
against the law of `X`, `∫ ω, g (X ω) ∂μ = ∑ x, (μ.map X).real {x} · g x`. -/
lemma integral_comp_law (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α)
    (hX : Measurable X) (g : α → ℝ) :
    ∫ ω, g (X ω) ∂μ = ∑ x, (μ.map X).real {x} * g x := by
  have hM : IsProbabilityMeasure (μ.map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  -- Step 1: push forward through `X`.
  have h_push : ∫ ω, g (X ω) ∂μ = ∫ x, g x ∂(μ.map X) :=
    (integral_map hX.aemeasurable (measurable_of_finite g).aestronglyMeasurable).symm
  -- Step 2: collapse to a finite sum, and convert `•` to `*`.
  rw [h_push, integral_fintype (μ := μ.map X) Integrable.of_finite]
  simp only [smul_eq_mul]

lemma integrable_betLogReturn_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (b o : α → ℝ) (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    Integrable (fun ω ↦ betLogReturn b o (Xs 0 ω)) μ := by
  have : IsProbabilityMeasure (μ.map (Xs 0)) :=
    Measure.isProbabilityMeasure_map (hXs 0).aemeasurable
  have h_int : Integrable (betLogReturn b o) (μ.map (Xs 0)) := Integrable.of_finite
  exact h_int.comp_measurable (hXs 0)

lemma identDistrib_betLogReturn (μ : Measure Ω) (b o : α → ℝ) (Xs : ℕ → Ω → α)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (i : ℕ) :
    IdentDistrib (fun ω ↦ betLogReturn b o (Xs i ω))
      (fun ω ↦ betLogReturn b o (Xs 0 ω)) μ μ :=
  (hident i).comp (measurable_betLogReturn b o)

lemma indepFun_betLogReturn (μ : Measure Ω) (b o : α → ℝ) (Xs : ℕ → Ω → α)
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j) :
    Pairwise fun i j ↦ (fun ω ↦ betLogReturn b o (Xs i ω))
      ⟂ᵢ[μ] (fun ω ↦ betLogReturn b o (Xs j ω)) := by
  intro i j hij
  exact (hindep hij).comp (measurable_betLogReturn b o) (measurable_betLogReturn b o)

lemma lawPmf_mem_stdSimplex (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α)
    (hX : Measurable X) : lawPmf μ X ∈ stdSimplex ℝ α := by
  have hM : IsProbabilityMeasure (μ.map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  refine ⟨fun x ↦ ?_, ?_⟩
  · exact measureReal_nonneg
  · show (∑ x : α, (μ.map X).real {x}) = 1
    have h1 : (∑ x : α, (μ.map X).real {x}) = (μ.map X).real (Finset.univ : Finset α) := by
      simp [sum_measureReal_singleton]
    rw [h1, Finset.coe_univ]
    exact probReal_univ

/-- **Operational gambling theorem** (Cover–Thomas §6.3): for an i.i.d. horse-race
sequence `Xs`, a fixed bet `b` under odds `o`, the time-averaged log-wealth growth
`(1/n)·log S_n` converges almost surely to the doubling rate
`doublingRate b o (lawPmf μ (Xs 0))`, where `lawPmf μ (Xs 0)` is the law of a single
race. -/
@[entry_point]
theorem seqLogWealth_div_tendsto_doublingRate
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b o : α → ℝ)
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ seqLogWealth b o Xs n ω / n) atTop
      (𝓝 (doublingRate b o (lawPmf μ (Xs 0)))) := by
  -- Apply the strong law to `X i := betLogReturn b o ∘ Xs i`, then identify the limit.
  have hint : Integrable (fun ω ↦ betLogReturn b o (Xs 0 ω)) μ :=
    integrable_betLogReturn_zero μ b o Xs hXs
  have hindBL := indepFun_betLogReturn μ b o Xs hindep
  have hidBL := identDistrib_betLogReturn μ b o Xs hident
  have h_lln := strong_law_ae_real (fun i ω ↦ betLogReturn b o (Xs i ω)) hint hindBL hidBL
  -- Identify the strong-law limit `μ[betLogReturn b o ∘ Xs 0]` with the doubling rate.
  have h_lim : ∫ ω, betLogReturn b o (Xs 0 ω) ∂μ = doublingRate b o (lawPmf μ (Xs 0)) := by
    rw [integral_comp_law μ (Xs 0) (hXs 0) (betLogReturn b o)]
    rfl
  filter_upwards [h_lln] with ω hω
  simpa only [seqLogWealth, h_lim] using hω

/-- The sequence-level growth rate of the proportional (Kelly) bet `b = p` in closed
form, `W(p, o, p) = ∑ x, p x · log (o x) − H(p)`. -/
theorem seqLogWealth_proportional_div_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ] (o : α → ℝ) (ho : ∀ x, 0 < o x)
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ seqLogWealth (lawPmf μ (Xs 0)) o Xs n ω / n) atTop
      (𝓝 ((∑ x, lawPmf μ (Xs 0) x * Real.log (o x))
        - ∑ x, Real.negMulLog (lawPmf μ (Xs 0) x))) := by
  have hp := lawPmf_mem_stdSimplex μ (Xs 0) (hXs 0)
  have h_closed := doublingRate_proportional_eq (lawPmf μ (Xs 0)) o hp ho
  have h_main :=
    seqLogWealth_div_tendsto_doublingRate μ (lawPmf μ (Xs 0)) o Xs hXs hindep hident
  filter_upwards [h_main] with ω hω
  rwa [h_closed] at hω

/-- **Operational Kelly optimality** (Cover–Thomas §6.3): the proportional (Kelly) bet
`b = p` is asymptotically optimal. Almost surely both the arbitrary full-support bet `b`
and the Kelly bet `p` have a growth rate, and the arbitrary bet does not beat the Kelly
bet. -/
@[entry_point]
theorem seqLogWealth_proportional_asymptotically_optimal
    (μ : Measure Ω) [IsProbabilityMeasure μ] (b o : α → ℝ)
    (hb : b ∈ stdSimplex ℝ α) (hb_pos : ∀ x, 0 < b x) (ho : ∀ x, 0 < o x)
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j ↦ Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ ↦ seqLogWealth b o Xs n ω / n) atTop
        (𝓝 (doublingRate b o (lawPmf μ (Xs 0)))) ∧
      Tendsto (fun n : ℕ ↦ seqLogWealth (lawPmf μ (Xs 0)) o Xs n ω / n) atTop
        (𝓝 (doublingRate (lawPmf μ (Xs 0)) o (lawPmf μ (Xs 0)))) ∧
      doublingRate b o (lawPmf μ (Xs 0))
        ≤ doublingRate (lawPmf μ (Xs 0)) o (lawPmf μ (Xs 0)) := by
  have hp := lawPmf_mem_stdSimplex μ (Xs 0) (hXs 0)
  have h_b := seqLogWealth_div_tendsto_doublingRate μ b o Xs hXs hindep hident
  have h_kelly :=
    seqLogWealth_div_tendsto_doublingRate μ (lawPmf μ (Xs 0)) o Xs hXs hindep hident
  have h_opt := doublingRate_le_proportional (lawPmf μ (Xs 0)) b o hp hb hb_pos ho
  filter_upwards [h_b, h_kelly] with ω hωb hωk
  exact ⟨hωb, hωk, h_opt⟩

end InformationTheory.Shannon.Gambling
