import InformationTheory.Fano.Core
import InformationTheory.Meta.EntryPoint
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Fano's inequality: measure-theoretic form

The measure-theoretic form of Fano's inequality (Cover–Thomas, Polyanskiy), proved with
Mathlib's `condDistrib` (the regular conditional distribution) as the central object, for a
deterministic decoder `Y → X`.

Setting:
* `X : Fintype` (discrete, finite) — the channel alphabet
* `Y : MeasurableSpace` (arbitrary; `ℝ`, `ℝⁿ`, Polish spaces, etc. are admissible)
* random variables `Xs : Ω → X` (source) and `Yo : Ω → Y` (observation) on `(Ω, μ)`
* `decoder : Y → X` — a deterministic measurable decoder

## Main definitions

* `condEntropy μ Xs Yo` — the conditional entropy `H(Xs | Yo)` as an integral over `μ.map Yo`.
* `errorProb μ Xs Yo decoder` — the decoding error probability `P(Xs ≠ decoder ∘ Yo)`.

## Main statements

* `fano_inequality_measure_theoretic` — `H(Xs | Yo) ≤ binEntropy Pe + Pe · log(|X| − 1)`.

## Implementation notes

The discrete Fano inequality of `Fano.Core` is applied pointwise for each `y : Y`, then
aggregated into integral form on `P_Yo = μ.map Yo` via Bochner–Jensen. The proof chains four
steps:

```
H(Xs | Yo)
  = ∫ y, [∑ x, negMulLog (Q_y {x})] dP_Yo                    -- def of condEntropy
  ≤ ∫ y, qaryEntropy |X| (Pe_y) dP_Yo                        -- Step 1: pointwise_fano
  ≤ qaryEntropy |X| (∫ y, Pe_y dP_Yo)                        -- Step 2: Bochner Jensen
  = qaryEntropy |X| (errorProb μ Xs Yo decoder)              -- Step 3: disintegration
  = h(Pe) + Pe · log(|X| - 1)                                -- Step 4: qaryEntropy split
```

Here `Q_y = (condDistrib Xs Yo μ y).real` is the conditional distribution of `Xs` given `y`
and `Pe_y = Q_y {x | x ≠ decoder y}` is the error rate given `y`. The `StandardBorelSpace`
requirement of `condDistrib` is imposed on the output type, which here is `X`; from
`Fintype + MeasurableSingletonClass + Countable` the instance
`DiscreteMeasurableSpace → StandardBorelSpace` is derived automatically, so `Y` carries no
extra constraint.
-/

namespace InformationTheory.MeasureFano

open MeasureTheory ProbabilityTheory

open scoped ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [MeasurableSpace Y]

/-! ## Definitions -/

/-- Conditional Shannon entropy, measure-theoretic form:
`H(Xs | Yo) = ∫ H(Xs | Yo = y) dP_Yo(y)`.

For each `y : Y` the measure `condDistrib Xs Yo μ y : Measure X` is discrete, so the
conditional entropy at `y` is the pointwise `negMulLog` sum, integrated against
`P_Yo = μ.map Yo`. -/
def condEntropy (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) : ℝ :=
  ∫ y, ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x}) ∂(μ.map Yo)

/-- Decoding error probability `Pe = P(Xs ≠ decoder ∘ Yo)`. -/
def errorProb (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X) : ℝ :=
  μ.real {ω | Xs ω ≠ decoder (Yo ω)}

/-- Error rate given `y`: `Pe(y) = (condDistrib Xs Yo μ y).real {x | x ≠ decoder y}`. -/
def pointwiseErrorProb (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X) (y : Y) : ℝ :=
  (condDistrib Xs Yo μ y).real {x : X | x ≠ decoder y}

/-! ## Pointwise Fano (bridge to the discrete form)

A glue lemma for invoking the discrete Fano inequality at each `y : Y`, in a form with the
`y`-dependence abstracted away: for any probability measure `Q : Measure X` and guess
`xh : X`, the Shannon entropy is bounded by `qaryEntropy |X| Pe`. The proof applies
`FiniteJointPMF.fano_inequality` to the `FiniteJointPMF X X` whose second coordinate is a
Dirac mass at `xh`.
-/

omit [DecidableEq X] [Nonempty X] in
private lemma sum_real_singleton_eq_one (Q : Measure X) [IsProbabilityMeasure Q] :
    ∑ x : X, Q.real {x} = 1 := by
  rw [show (∑ x : X, Q.real {x}) = ∑ x ∈ (Finset.univ : Finset X), Q.real {x} from rfl,
      sum_measureReal_singleton]
  rw [show ((Finset.univ : Finset X) : Set X) = Set.univ from Finset.coe_univ]
  simp [measureReal_def, measure_univ]

/-- The `FiniteJointPMF X X` built from a probability measure `Q : Measure X` and a guess
`xh : X`, with a Dirac mass at `xh` in the second coordinate, i.e.
`mass x x' = Q.real {x} · 𝟙[x' = xh]`. -/
def diracPMF (Q : Measure X) [IsProbabilityMeasure Q] (xh : X) :
    FiniteJointPMF X X where
  mass := fun x x' => if x' = xh then Q.real {x} else 0
  mass_nonneg := fun x x' => by
    split_ifs
    · exact measureReal_nonneg
    · exact le_refl 0
  sum_mass := by
    -- ∑ x, ∑ x', (if x' = xh then Q.real {x} else 0) = ∑ x, Q.real {x} = 1
    have hInner : ∀ x : X,
        (∑ x' : X, if x' = xh then Q.real {x} else 0) = Q.real {x} := by
      intro x
      rw [Finset.sum_eq_single xh (fun b _ hb => by simp [hb]) (fun h => (h (Finset.mem_univ _)).elim)]
      simp
    rw [Finset.sum_congr rfl (fun x _ => hInner x)]
    exact sum_real_singleton_eq_one Q

/-! ### Computations for `diracPMF` -/

omit [Nonempty X] in
private lemma diracPMF_mass (Q : Measure X) [IsProbabilityMeasure Q] (xh x x' : X) :
    (diracPMF Q xh).mass x x' = if x' = xh then Q.real {x} else 0 := rfl

omit [Nonempty X] in
/-- The joint entropy of `diracPMF Q xh` equals `∑ x, negMulLog (Q.real {x})`. -/
private lemma diracPMF_jointEntropy (Q : Measure X) [IsProbabilityMeasure Q] (xh : X) :
    (diracPMF Q xh).jointEntropy = ∑ x : X, Real.negMulLog (Q.real {x}) := by
  unfold FiniteJointPMF.jointEntropy
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single xh
    (fun b _ hb => by rw [diracPMF_mass, if_neg hb]; simp)
    (fun h => (h (Finset.mem_univ _)).elim)]
  rw [diracPMF_mass, if_pos rfl]

omit [Nonempty X] in
/-- The `Y`-marginal of `diracPMF Q xh` is the Dirac mass at `xh`. -/
private lemma diracPMF_marginalY (Q : Measure X) [IsProbabilityMeasure Q] (xh x' : X) :
    (diracPMF Q xh).marginalY x' = if x' = xh then 1 else 0 := by
  unfold FiniteJointPMF.marginalY
  by_cases hx' : x' = xh
  · rw [hx', if_pos rfl]
    have : (∑ x : X, (diracPMF Q xh).mass x xh) = ∑ x : X, Q.real {x} :=
      Finset.sum_congr rfl (fun x _ => by rw [diracPMF_mass, if_pos rfl])
    rw [this, sum_real_singleton_eq_one]
  · rw [if_neg hx']
    apply Finset.sum_eq_zero
    intro x _
    rw [diracPMF_mass, if_neg hx']

omit [Nonempty X] in
/-- The `Y`-entropy of `diracPMF Q xh` is `0` (the Dirac mass is pure). -/
private lemma diracPMF_yEntropy (Q : Measure X) [IsProbabilityMeasure Q] (xh : X) :
    (diracPMF Q xh).yEntropy = 0 := by
  unfold FiniteJointPMF.yEntropy
  apply Finset.sum_eq_zero
  intro x' _
  rw [diracPMF_marginalY]
  by_cases hx' : x' = xh
  · rw [if_pos hx']; simp
  · rw [if_neg hx']; simp

omit [Nonempty X] in
/-- The conditional entropy of `diracPMF Q xh` equals `∑ x, negMulLog (Q.real {x})`. -/
private lemma diracPMF_condEntropy (Q : Measure X) [IsProbabilityMeasure Q] (xh : X) :
    (diracPMF Q xh).condEntropy = ∑ x : X, Real.negMulLog (Q.real {x}) := by
  unfold FiniteJointPMF.condEntropy
  rw [diracPMF_jointEntropy, diracPMF_yEntropy, sub_zero]

omit [Nonempty X] in
/-- The error probability of `diracPMF Q xh` is the `Q`-mass of the complement of `{xh}`. -/
private lemma diracPMF_errorProb (Q : Measure X) [IsProbabilityMeasure Q] (xh : X) :
    (diracPMF Q xh).errorProb = Q.real {x : X | x ≠ xh} := by
  unfold FiniteJointPMF.errorProb
  -- Inner sum collapses to the xh column, contributing iff x ≠ xh.
  have hInner : ∀ x : X,
      (∑ x' : X, if x = x' then 0 else (diracPMF Q xh).mass x x')
        = if x = xh then 0 else Q.real {x} := by
    intro x
    rw [Finset.sum_eq_single xh
      (fun b _ hb => by rw [diracPMF_mass, if_neg hb]; simp)
      (fun h => (h (Finset.mem_univ _)).elim)]
    rw [diracPMF_mass, if_pos rfl]
  rw [Finset.sum_congr rfl (fun x _ => hInner x)]
  -- Split the xh term out (it is 0), leaving ∑ x ∈ univ \ {xh}, Q.real {x}.
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ xh)
      (fun x => (if x = xh then (0:ℝ) else Q.real {x}))]
  rw [if_pos rfl, add_zero]
  have hDiff : ∀ x ∈ ((Finset.univ : Finset X) \ ({xh} : Finset X)),
      (if x = xh then (0:ℝ) else Q.real {x}) = Q.real {x} := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
    rw [if_neg hx.2]
  rw [Finset.sum_congr rfl hDiff, sum_measureReal_singleton]
  -- Now: Q.real ↑(univ \ {xh}) = Q.real {x | x ≠ xh}.
  have hSet : (↑((Finset.univ : Finset X) \ ({xh} : Finset X)) : Set X)
              = {x : X | x ≠ xh} := by
    ext x
    simp
  rw [hSet]

omit [DecidableEq X] [Nonempty X] in
/-- Pointwise Fano: for a probability measure `Q : Measure X` and guess `xh : X`,
`∑ x, negMulLog (Q.real {x}) ≤ qaryEntropy |X| (Q.real {x | x ≠ xh})`. The conclusion comes
directly from `fano_core` applied to `diracPMF Q xh` (Dirac at `xh` in the second
coordinate). -/
lemma pointwise_fano (Q : Measure X) [IsProbabilityMeasure Q] (xh : X)
    (hcard : 2 ≤ Fintype.card X) :
    (∑ x : X, Real.negMulLog (Q.real {x}))
      ≤ Real.qaryEntropy (Fintype.card X) (Q.real {x : X | x ≠ xh}) := by
  classical
  have hFano := (diracPMF Q xh).fano_core hcard
  rw [diracPMF_condEntropy, diracPMF_errorProb] at hFano
  exact hFano

/-! ## Main theorem: Fano's inequality, measure-theoretic form

Steps 1–4 are chained with `calc`. Each step is built locally as a `have` inside the
theorem rather than as a separate lemma.
-/

omit [DecidableEq X] in
/-- Fano's inequality, measure-theoretic form (deterministic decoder). -/
@[entry_point]
theorem fano_inequality_measure_theoretic
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hdec : Measurable decoder)
    (hcard : 2 ≤ Fintype.card X) :
    condEntropy μ Xs Yo ≤
      Real.binEntropy (errorProb μ Xs Yo decoder)
        + errorProb μ Xs Yo decoder * Real.log ((Fintype.card X : ℝ) - 1) := by
  -- ## Shared infrastructure (used in Steps 1 / 2 / 3)
  haveI : IsProbabilityMeasure (μ.map Yo) :=
    Measure.isProbabilityMeasure_map hYo.aemeasurable
  -- Lift the `y`-dependent error event `{x | x ≠ decoder y}` to a fixed measurable set on
  -- `Y × X`, so that `Kernel.measurable_kernel_prodMk_left` applies.
  have hMS : MeasurableSet {p : Y × X | p.2 ≠ decoder p.1} := by
    have hMS_eq : MeasurableSet {p : Y × X | p.2 = decoder p.1} :=
      measurableSet_eq_fun measurable_snd (hdec.comp measurable_fst)
    have hMS_swap : {p : Y × X | p.2 ≠ decoder p.1}
                    = ({p : Y × X | p.2 = decoder p.1})ᶜ := by
      ext p; simp [Set.mem_compl_iff]
    rw [hMS_swap]; exact hMS_eq.compl
  have hPreimage : ∀ y : Y, {x : X | x ≠ decoder y}
                   = Prod.mk y ⁻¹' {p : Y × X | p.2 ≠ decoder p.1} := by
    intro y; ext x; simp
  have hPeENN : Measurable
      (fun y => (condDistrib Xs Yo μ y) {x : X | x ≠ decoder y}) := by
    simp only [hPreimage]
    exact Kernel.measurable_kernel_prodMk_left hMS
  have hPeMeas : Measurable (pointwiseErrorProb μ Xs Yo decoder) := by
    change Measurable
      (fun y => ((condDistrib Xs Yo μ y) {x : X | x ≠ decoder y}).toReal)
    exact ENNReal.measurable_toReal.comp hPeENN
  have hPe_mem :
      ∀ᵐ y ∂(μ.map Yo), pointwiseErrorProb μ Xs Yo decoder y ∈ Set.Icc (0:ℝ) 1 :=
    Filter.Eventually.of_forall
      (fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
  have hPe_integrable :
      Integrable (pointwiseErrorProb μ Xs Yo decoder) (μ.map Yo) :=
    Integrable.of_mem_Icc 0 1 hPeMeas.aemeasurable hPe_mem
  have hLog_nonneg : 0 ≤ Real.log ((Fintype.card X : ℝ) - 1) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hcard
    linarith
  -- ## Step 1: apply the discrete Fano (`pointwise_fano`) per `y`, bounding the integrand
  -- above by `qaryEntropy (Pe(y))`.
  have hPointwise : ∀ y : Y,
      (∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x}))
        ≤ Real.qaryEntropy (Fintype.card X)
            (pointwiseErrorProb μ Xs Yo decoder y) := fun y =>
    pointwise_fano (condDistrib Xs Yo μ y) (decoder y) hcard
  have step1 :
      condEntropy μ Xs Yo ≤
        ∫ y, Real.qaryEntropy (Fintype.card X)
              (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo) := by
    unfold condEntropy
    apply MeasureTheory.integral_mono_ae
    · -- Integrable LHS: `∑ x, negMulLog ((cond y).real {x})` is bounded and measurable on a
      -- probability measure.
      have hMeasOne : ∀ x : X,
          Measurable (fun y => (condDistrib Xs Yo μ y).real {x}) := fun x =>
        ENNReal.measurable_toReal.comp
          (Kernel.measurable_coe _ (measurableSet_singleton x))
      have hLHS : Measurable
          (fun y => ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x})) :=
        Finset.measurable_sum _ (fun x _ =>
          Real.continuous_negMulLog.measurable.comp (hMeasOne x))
      apply Integrable.of_mem_Icc 0 (Fintype.card X) hLHS.aemeasurable
      refine Filter.Eventually.of_forall (fun y => ⟨?_, ?_⟩)
      · exact Finset.sum_nonneg (fun x _ =>
          Real.negMulLog_nonneg measureReal_nonneg measureReal_le_one)
      · -- Each term satisfies `negMulLog t ≤ 1 - t ≤ 1` for `t ≥ 0`.
        calc ∑ x : X, Real.negMulLog ((condDistrib Xs Yo μ y).real {x})
            ≤ ∑ _x : X, (1 : ℝ) := by
              refine Finset.sum_le_sum (fun x _ => ?_)
              have hUB := Real.negMulLog_le_one_sub_self
                (measureReal_nonneg (μ := condDistrib Xs Yo μ y)
                  (s := ({x} : Set X)))
              linarith [measureReal_nonneg (μ := condDistrib Xs Yo μ y)
                (s := ({x} : Set X))]
          _ = (Fintype.card X : ℝ) := by simp
    · -- Integrable RHS: `y ↦ qaryEntropy |X| (Pe(y))`, with `Pe ∈ [0,1]` and `qaryEntropy`
      -- continuous.
      have hRHS : Measurable
          (fun y => Real.qaryEntropy (Fintype.card X)
                      (pointwiseErrorProb μ Xs Yo decoder y)) :=
        Real.qaryEntropy_continuous.measurable.comp hPeMeas
      apply Integrable.of_mem_Icc 0
        (Real.log ((Fintype.card X : ℝ) - 1) + Real.log 2) hRHS.aemeasurable
      refine Filter.Eventually.of_forall (fun y => ?_)
      have hPe_nn : 0 ≤ pointwiseErrorProb μ Xs Yo decoder y := measureReal_nonneg
      have hPe_le_one : pointwiseErrorProb μ Xs Yo decoder y ≤ 1 := measureReal_le_one
      refine ⟨Real.qaryEntropy_nonneg hPe_nn hPe_le_one, ?_⟩
      unfold Real.qaryEntropy
      rw [show Real.log ((Fintype.card X - 1 : ℤ) : ℝ)
            = Real.log ((Fintype.card X : ℝ) - 1) by push_cast; rfl]
      have h1 : pointwiseErrorProb μ Xs Yo decoder y * Real.log ((Fintype.card X : ℝ) - 1)
                ≤ Real.log ((Fintype.card X : ℝ) - 1) := by
        nlinarith [hPe_nn, hPe_le_one, hLog_nonneg]
      linarith [Real.binEntropy_le_log_two
        (p := pointwiseErrorProb μ Xs Yo decoder y)]
    · exact Filter.Eventually.of_forall hPointwise
  -- ## Step 2: Bochner–Jensen bounds the integral above by `qaryEntropy (∫ Pe(y) dP_Yo)`.
  -- Split `qaryEntropy = Pe·log(|X|-1) + binEntropy(Pe)`: the linear term commutes with the
  -- integral, and concave Jensen (`ConcaveOn.le_map_integral`) applies to the `binEntropy` term.
  have step2 :
      (∫ y, Real.qaryEntropy (Fintype.card X)
              (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo))
        ≤ Real.qaryEntropy (Fintype.card X)
            (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo)) := by
    have hbinEntropy_integrable :
        Integrable (fun y => Real.binEntropy (pointwiseErrorProb μ Xs Yo decoder y))
          (μ.map Yo) := by
      apply Integrable.of_mem_Icc 0 (Real.log 2)
        (Real.binEntropy_continuous.measurable.comp hPeMeas).aemeasurable
      exact Filter.Eventually.of_forall (fun _ =>
        ⟨Real.binEntropy_nonneg measureReal_nonneg measureReal_le_one,
         Real.binEntropy_le_log_two⟩)
    have hqDecomp : ∀ p : ℝ,
        Real.qaryEntropy (Fintype.card X) p
          = p * Real.log ((Fintype.card X : ℝ) - 1) + Real.binEntropy p := fun p => by
      rw [InformationTheory.qaryEntropy_eq_binEntropy_add_log]; ring
    have hLHS_eq :
        (∫ y, Real.qaryEntropy (Fintype.card X)
                (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo))
          = (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo)) *
              Real.log ((Fintype.card X : ℝ) - 1) +
            (∫ y, Real.binEntropy (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo)) := by
      simp only [hqDecomp]
      rw [integral_add (hPe_integrable.mul_const _) hbinEntropy_integrable,
          integral_mul_const]
    have hJensen :
        (∫ y, Real.binEntropy (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo))
          ≤ Real.binEntropy
              (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo)) :=
      Real.strictConcave_binEntropy.concaveOn.le_map_integral
        Real.binEntropy_continuous.continuousOn isClosed_Icc
        hPe_mem hPe_integrable hbinEntropy_integrable
    rw [hLHS_eq, hqDecomp (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo))]
    linarith
  -- ## Step 3: disintegration gives `∫ Pe(y) dP_Yo = errorProb μ Xs Yo decoder`.
  -- Chain: `integral_toReal` lifts the real integral to a lintegral, then
  -- `compProd_apply (←) → compProd_map_condDistrib → map_apply` descend to an event on `μ`.
  have step3 :
      (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo))
        = errorProb μ Xs Yo decoder := by
    have hPe_lt_top : ∀ᵐ y ∂(μ.map Yo),
        (condDistrib Xs Yo μ y) {x : X | x ≠ decoder y} < ∞ :=
      Filter.Eventually.of_forall (fun _ => measure_lt_top _ _)
    unfold pointwiseErrorProb errorProb
    show (∫ y, ((condDistrib Xs Yo μ y) {x : X | x ≠ decoder y}).toReal ∂(μ.map Yo))
          = (μ {ω | Xs ω ≠ decoder (Yo ω)}).toReal
    rw [integral_toReal hPeENN.aemeasurable hPe_lt_top]
    congr 1
    simp_rw [hPreimage]
    rw [← Measure.compProd_apply hMS,
        compProd_map_condDistrib hXs.aemeasurable,
        Measure.map_apply (hYo.prodMk hXs) hMS]
    rfl
  -- Step 4: `qaryEntropy = binEntropy + Pe * log(|X|-1)` (a known rewrite).
  have step4 :
      Real.qaryEntropy (Fintype.card X) (errorProb μ Xs Yo decoder)
        = Real.binEntropy (errorProb μ Xs Yo decoder)
          + errorProb μ Xs Yo decoder * Real.log ((Fintype.card X : ℝ) - 1) :=
    InformationTheory.qaryEntropy_eq_binEntropy_add_log _ _
  -- Chain: step1 → step2 → step3 → step4
  calc condEntropy μ Xs Yo
      ≤ ∫ y, Real.qaryEntropy (Fintype.card X)
              (pointwiseErrorProb μ Xs Yo decoder y) ∂(μ.map Yo) := step1
    _ ≤ Real.qaryEntropy (Fintype.card X)
          (∫ y, pointwiseErrorProb μ Xs Yo decoder y ∂(μ.map Yo)) := step2
    _ = Real.qaryEntropy (Fintype.card X) (errorProb μ Xs Yo decoder) := by rw [step3]
    _ = _ := step4

end

end InformationTheory.MeasureFano
