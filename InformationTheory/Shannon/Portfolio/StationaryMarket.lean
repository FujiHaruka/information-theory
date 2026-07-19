import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BirkhoffErgodic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Log-optimal portfolios over stationary ergodic markets (Cover–Thomas §16.5)

For a stationary ergodic market driven by a measure-preserving ergodic shift `T : Ω → Ω`,
with the price-relative vector at the first epoch given by an observation
`X : Ω → (Fin m → ℝ)`, an investor reinvesting all wealth with a fixed rebalanced
portfolio `b : Fin m → ℝ` accumulates wealth whose log grows like
`∑ i, log (b · X (T^[i] ω))`. The time-averaged log-wealth growth converges almost surely
to the expected log return `∫ ω, log (b · X ω) ∂μ`. This is the stationary-ergodic
counterpart of the i.i.d. operational theorem
`InformationTheory.Shannon.Portfolio.seqLogWealth_div_tendsto_growthRate`, obtained by
replacing the strong law of large numbers with the Birkhoff individual ergodic theorem.

## Main definitions

* `stationaryLogReturn` — the per-epoch log return `log (b · X ω) = log (∑ j, b j · X ω j)`.

## Main statements

* `seqLogWealth_div_tendsto_stationary` — §16.5 (fixed portfolio): the Birkhoff time
  average of the log return converges almost surely to `∫ ω, log (b · X ω) ∂μ`.

## Implementation notes

The proof is a direct application of the Birkhoff individual ergodic theorem
`InformationTheory.Shannon.birkhoff_ergodic_ae` to the integrable observable
`stationaryLogReturn X b`, mirroring the template
`InformationTheory.Shannon.birkhoffAverage_pmfLogCond_tendsto`. The normalization matches
the in-project `birkhoffAverageReal`, whose time average uses `n + 1` terms
(`∑_{i=0}^{n}`) over the denominator `n + 1`.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Section 16.5.
-/

namespace InformationTheory.Shannon.Portfolio

open MeasureTheory Filter
open scoped BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {m : ℕ}

/-- The per-epoch log return `log (b · X ω) = log (∑ j, b j · X ω j)`: the log growth factor
of wealth when the price-relative vector is `X ω` and the portfolio is `b`. -/
noncomputable def stationaryLogReturn (X : Ω → Fin m → ℝ) (b : Fin m → ℝ) : Ω → ℝ :=
  fun ω ↦ Real.log (∑ j, b j * X ω j)

/-- Stationary ergodic log-optimal portfolio theorem (Cover–Thomas §16.5): for a
measure-preserving ergodic shift `T` on a probability space, a fixed rebalanced portfolio
`b`, and an integrable per-epoch log return, the Birkhoff time average of the log-wealth
growth converges almost surely to the expected log return `∫ ω, log (b · X ω) ∂μ`.
@audit:ok — sorryAx-free (`[propext, Classical.choice, Quot.sound]`). Direct application of
`birkhoff_ergodic_ae`; `hT`/`hT_erg`/`hint` are its ergodic-system and integrability
preconditions, `∫ ω, stationaryLogReturn X b ω` is a genuine definitional binding (the
spatial mean), and the spelled-out `range (n+1) / (n+1)` average matches `birkhoffAverageReal`.
Non-circular, no load-bearing hypothesis. -/
@[entry_point]
theorem seqLogWealth_div_tendsto_stationary
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    (X : Ω → (Fin m → ℝ)) (b : Fin m → ℝ)
    (hint : Integrable (stationaryLogReturn X b) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ (∑ i ∈ Finset.range (n + 1), stationaryLogReturn X b (T^[i] ω)) / (n + 1 : ℝ))
        atTop
      (𝓝 (∫ ω, stationaryLogReturn X b ω ∂μ)) := by
  filter_upwards [birkhoff_ergodic_ae hT hT_erg hint] with ω hω
  exact hω

/-- Stationary asymptotic optimality (Cover–Thomas §16.5): a log-optimal portfolio `bs`
satisfying the integral Kuhn–Tucker condition `∀ i, ∫ X_i / (bs · X) ∂μ ≤ 1` maximizes the
expected log return: every simplex portfolio `b` has `∫ log (b · X) ≤ ∫ log (bs · X)`.

Together with `seqLogWealth_div_tendsto_stationary` this gives the asymptotic dominance of
`bs` over any fixed `b`: the almost-sure limits of the time-averaged log-wealth satisfy the
same inequality.
@audit:ok — sorryAx-free (`[propext, Classical.choice, Quot.sound]`). `hKT` constrains only
`bs` (per-coordinate integral stationarity, `b`-free), so it is the honest hypothesis of the
Kuhn–Tucker sufficiency theorem, not the conclusion in disguise: the dominance is proved
genuinely via the tangent bound `log t ≤ t − 1` integrated against the wealth ratio, then
`∫ R = ∑ i, b i · ∫ X_i/(bs·X) ≤ 1`. Simplex/positivity/integrability hypotheses are
regularity preconditions; non-circular, no load-bearing hypothesis. -/
@[entry_point]
theorem stationaryLogReturn_integral_le_of_kuhnTucker
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → (Fin m → ℝ)) (b bs : Fin m → ℝ)
    (hb : b ∈ stdSimplex ℝ (Fin m))
    (hpos_b : ∀ ω, 0 < ∑ j, b j * X ω j)
    (hpos_bs : ∀ ω, 0 < ∑ j, bs j * X ω j)
    (hint_b : Integrable (stationaryLogReturn X b) μ)
    (hint_bs : Integrable (stationaryLogReturn X bs) μ)
    (hint_coord : ∀ i, Integrable (fun ω ↦ X ω i / (∑ j, bs j * X ω j)) μ)
    (hKT : ∀ i, (∫ ω, X ω i / (∑ j, bs j * X ω j) ∂μ) ≤ 1) :
    ∫ ω, stationaryLogReturn X b ω ∂μ ≤ ∫ ω, stationaryLogReturn X bs ω ∂μ := by
  -- The wealth ratio `R ω = (b · X ω) / (bs · X ω) = ∑ i, b i · (X ω i / (bs · X ω))`.
  have hratio_eq : (fun ω ↦ (∑ j, b j * X ω j) / (∑ j, bs j * X ω j))
      = fun ω ↦ ∑ i, b i * (X ω i / (∑ j, bs j * X ω j)) := by
    funext ω
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ ↦ by rw [mul_div_assoc])
  have hR_int : Integrable (fun ω ↦ (∑ j, b j * X ω j) / (∑ j, bs j * X ω j)) μ := by
    rw [hratio_eq]
    exact integrable_finsetSum _ (fun i _ ↦ (hint_coord i).const_mul (b i))
  -- Pointwise `log (b · X) − log (bs · X) = log R ≤ R − 1`.
  have hbound : ∀ ω, stationaryLogReturn X b ω - stationaryLogReturn X bs ω
      ≤ (∑ j, b j * X ω j) / (∑ j, bs j * X ω j) - 1 := by
    intro ω
    have h1 : stationaryLogReturn X b ω - stationaryLogReturn X bs ω
        = Real.log ((∑ j, b j * X ω j) / (∑ j, bs j * X ω j)) := by
      simp only [stationaryLogReturn]
      rw [Real.log_div (ne_of_gt (hpos_b ω)) (ne_of_gt (hpos_bs ω))]
    rw [h1]
    exact Real.log_le_sub_one_of_pos (div_pos (hpos_b ω) (hpos_bs ω))
  -- Integrate the pointwise bound.
  have hstep : (∫ ω, stationaryLogReturn X b ω ∂μ) - (∫ ω, stationaryLogReturn X bs ω ∂μ)
      ≤ (∫ ω, (∑ j, b j * X ω j) / (∑ j, bs j * X ω j) ∂μ) - 1 := by
    have hright : (∫ ω, ((∑ j, b j * X ω j) / (∑ j, bs j * X ω j) - 1) ∂μ)
        = (∫ ω, (∑ j, b j * X ω j) / (∑ j, bs j * X ω j) ∂μ) - 1 := by
      rw [integral_sub hR_int (integrable_const 1)]; simp
    calc (∫ ω, stationaryLogReturn X b ω ∂μ) - (∫ ω, stationaryLogReturn X bs ω ∂μ)
        = ∫ ω, (stationaryLogReturn X b ω - stationaryLogReturn X bs ω) ∂μ :=
          (integral_sub hint_b hint_bs).symm
      _ ≤ ∫ ω, ((∑ j, b j * X ω j) / (∑ j, bs j * X ω j) - 1) ∂μ :=
          integral_mono_ae (hint_b.sub hint_bs) (hR_int.sub (integrable_const 1))
            (ae_of_all _ hbound)
      _ = (∫ ω, (∑ j, b j * X ω j) / (∑ j, bs j * X ω j) ∂μ) - 1 := hright
  -- `∫ R = ∑ i, b i · ∫ X_i/(bs·X) ≤ ∑ i, b i · 1 = 1`.
  have hR_le : (∫ ω, (∑ j, b j * X ω j) / (∑ j, bs j * X ω j) ∂μ) ≤ 1 := by
    rw [hratio_eq, integral_finsetSum _ (fun i _ ↦ (hint_coord i).const_mul (b i))]
    have hterm : ∀ i, (∫ ω, b i * (X ω i / (∑ j, bs j * X ω j)) ∂μ)
        = b i * ∫ ω, X ω i / (∑ j, bs j * X ω j) ∂μ := fun i ↦ integral_const_mul (b i) _
    simp_rw [hterm]
    calc ∑ i, b i * ∫ ω, X ω i / (∑ j, bs j * X ω j) ∂μ
        ≤ ∑ i, b i * 1 :=
          Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hKT i) (hb.1 i))
      _ = 1 := by simp [hb.2]
  linarith

end InformationTheory.Shannon.Portfolio
