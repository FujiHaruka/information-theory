import InformationTheory.Shannon.EPI.Case1.SmoothingLimit
import InformationTheory.Shannon.EPI.Stam.SupplyTwoTime
import InformationTheory.Shannon.EPI.G2.ConvEntropyMonotone
import InformationTheory.Shannon.EPI.InfiniteVariance.Truncation.Construction
import InformationTheory.Shannon.EPI.InfiniteVariance.Truncation.Density
import InformationTheory.Shannon.EPI.InfiniteVariance.Truncation.Convergence

/-!
# Classical entropy power inequality for absolutely continuous, infinite-variance sums

The classical entropy power inequality `Nₑ(X + Y) ≥ Nₑ(X) + Nₑ(Y)` for an independent sum of
two absolutely continuous random variables with finite differential entropy, without assuming
finite variance. It is obtained from the finite-variance entropy power inequality
`entropyPowerExt_add_ge_of_finite_variance` by applying it to the conditioning truncation
`X_n := X | {|X| ≤ n ∧ |Y| ≤ n}` and passing to the limit `n → ∞`.

## Main statements

* `entropyPowerExt_add_ge_infinite_variance_truncation` — the law-level inequality
  `Nₑ(P.map (X + Y)) ≥ Nₑ(P.map X) + Nₑ(P.map Y)` for the conditioning-truncation route.

## Implementation notes

For each `n` the conditioned measure `P_n := P[· | {|X| ≤ n ∧ |Y| ≤ n}]` (joint conditioning on
both components) has compact support, hence finite second moments and finite differential
entropy; it preserves absolute continuity (`cond_absolutelyContinuous` plus monotonicity of
`Measure.map` under absolute continuity) and independence (conditioning on the rectangular event
`X⁻¹[-n, n] ∩ Y⁻¹[-n, n]` preserves `IndepFun X Y`). So the finite-variance inequality applies at
each `n`, giving `Nₑ(P_n.map (X + Y)) ≥ Nₑ(P_n.map X) + Nₑ(P_n.map Y)`.

The final assembly is a `limsup` chain that does not depend on moments: the per-`n` inequality,
the upper semicontinuity bound `Nₑ(P.map (X + Y)) ≥ limsupₙ Nₑ(P_n.map (X + Y))` (Gibbs plus a
cross-entropy dominated convergence argument), and the right-hand convergences
`Nₑ(P_n.map X) → Nₑ(P.map X)`, `Nₑ(P_n.map Y) → Nₑ(P.map Y)` compose into
`Nₑ(P.map (X + Y)) ≥ limsupₙ Nₑ(P_n.map (X + Y)) ≥ limₙ (Nₑ(P_n.map X) + Nₑ(P_n.map Y))`.

Design choices:
* the truncation index is `n : ℕ` with truncation set `{|X| ≤ n ∧ |Y| ≤ n}`, monotone in `n`, so
  monotone / dominated convergence along the `atTop` filter is direct;
* the conditioning API is `ProbabilityTheory.cond P s = (P s)⁻¹ • P.restrict s`, whose absolute
  continuity is `cond_absolutelyContinuous`. A naive indicator truncation `1_{|X| ≤ n} · X` would
  create an atom in the law and break absolute continuity, so conditioning is used instead;
* the black box works with the random-variable form `P.map (fun ω => X ω + Y ω)`; convolution is
  implicit in `P_n.map (X + Y)` and `Measure.conv` is never expanded explicitly;
* independence is preserved because joint conditioning is on a rectangular event.
-/

namespace InformationTheory.Shannon.EPIInfiniteVarianceTruncation

open MeasureTheory Filter Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1SmoothingLimit
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAdd_comm)
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The law-level entropy power inequality `Nₑ(P.map (X + Y)) ≥ Nₑ(P.map X) + Nₑ(P.map Y)` for an
independent, absolutely continuous, finite-differential-entropy sum, via the conditioning
truncation route: the per-`n` black-box inequality, the upper semicontinuity bound, and the
right-hand convergences compose into `Nₑ(X) + Nₑ(Y) = lim RHSₙ ≤ limsup LHSₙ ≤ Nₑ(X + Y)`.

The finiteness `hent_sum` of the differential entropy of the sum is a regularity precondition fed
to the upper semicontinuity bound; it does not encode the inequality (if the sum entropy were
`+∞` then `Nₑ(P.map (X + Y)) = ⊤` and the inequality is immediate). -/
theorem entropyPowerExt_add_ge_infinite_variance_truncation
    (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x ↦ Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x ↦ Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hent_sum : Integrable
      (fun x ↦ Real.negMulLog ((P.map (fun ω ↦ X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω ↦ X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- Goal: `Nₑ(P.map X) + Nₑ(P.map Y) ≤ Nₑ(P.map(X+Y))`.
  rw [ge_iff_le]
  -- (1) RHS convergence: `Nₑ(P_n.map X) + Nₑ(P_n.map Y) → Nₑ(P.map X) + Nₑ(P.map Y)`.
  have hX_tendsto :
      Tendsto (fun n ↦ entropyPowerExt ((condTrunc P X Y n).map X)) atTop
        (𝓝 (entropyPowerExt (P.map X))) :=
    entropyPowerExt_map_condTrunc_tendsto P hX hY hXY (Or.inl rfl) hX_ac hX_ent
  have hY_tendsto :
      Tendsto (fun n ↦ entropyPowerExt ((condTrunc P X Y n).map Y)) atTop
        (𝓝 (entropyPowerExt (P.map Y))) :=
    entropyPowerExt_map_condTrunc_tendsto P hX hY hXY (Or.inr rfl) hY_ac hY_ent
  have hRHS_tendsto :
      Tendsto (fun n ↦ entropyPowerExt ((condTrunc P X Y n).map X)
          + entropyPowerExt ((condTrunc P X Y n).map Y)) atTop
        (𝓝 (entropyPowerExt (P.map X) + entropyPowerExt (P.map Y))) :=
    hX_tendsto.add hY_tendsto
  -- (2) per-n inequality (eventually): `Nₑ(P_n.map X) + Nₑ(P_n.map Y) ≤ Nₑ(P_n.map(X+Y))`.
  have hper_n :
      ∀ᶠ n in atTop,
        entropyPowerExt ((condTrunc P X Y n).map X)
            + entropyPowerExt ((condTrunc P X Y n).map Y)
          ≤ entropyPowerExt ((condTrunc P X Y n).map (fun ω ↦ X ω + Y ω)) := by
    filter_upwards [eventually_measure_truncSet_pos P hX hY] with n hpos
    exact entropyPowerExt_condTrunc_add_ge P hX hY hXY hX_ac hY_ac hX_ent hY_ent hpos
  -- (3) limsup chain.
  calc
    entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)
        = Filter.limsup (fun n ↦ entropyPowerExt ((condTrunc P X Y n).map X)
            + entropyPowerExt ((condTrunc P X Y n).map Y)) atTop :=
          hRHS_tendsto.limsup_eq.symm
    _ ≤ Filter.limsup
          (fun n ↦ entropyPowerExt ((condTrunc P X Y n).map (fun ω ↦ X ω + Y ω))) atTop :=
          Filter.limsup_le_limsup hper_n
    _ ≤ entropyPowerExt (P.map (fun ω ↦ X ω + Y ω)) :=
          entropyPowerExt_condTrunc_sum_limsup_le
            P hX hY hXY hX_ac hY_ac hX_ent hY_ent hent_sum

end InformationTheory.Shannon.EPIInfiniteVarianceTruncation
