import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Bridge
import InformationTheory.Shannon.CondMutualInfo

/-!
# Entropy chain rule and conditioning monotonicity

Two-variable Shannon inequalities: chain rule, conditional mutual information formula,
and the fact that conditioning never increases entropy.

## Main statements

* `entropy_pair_eq_entropy_add_condEntropy` — `H(X, Y) = H(X) + H(Y | X)`.
* `condEntropy_tower` — disintegration form of `H(X | Y, Z)`.
* `condMutualInfo_eq_condEntropy_sub_condEntropy` — `I(X; Z | Y) = H(X | Y) - H(X | Y, Z)`.
* `condEntropy_le_condEntropy_of_pair` — `H(X | Y, Z) ≤ H(X | Y)`.

## Implementation notes

`condMutualInfo_eq_condEntropy_sub_condEntropy` uses the Mathlib mutual-information
chain rule `mutualInfo_chain_rule` plus `mutualInfo_comm`/`condMutualInfo_comm` to
put `Xs` on the left, then lifts to `.toReal` using finiteness from `mutualInfo_ne_top`
and `condMutualInfo_ne_top`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]
variable {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z]

omit [DecidableEq X] [Nonempty X] [DecidableEq Y] in
/-- Chain rule for Shannon entropy: `H(X, Y) = H(X) + H(Y | X)`. -/
@[entry_point]
theorem entropy_pair_eq_entropy_add_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y)
    (_hXs : Measurable Xs) (hYo : Measurable Yo) :
    entropy μ (fun ω => (Xs ω, Yo ω))
      = entropy μ Xs + InformationTheory.MeasureFano.condEntropy μ Yo Xs := by
  haveI : IsProbabilityMeasure (μ.map Xs) :=
    Measure.isProbabilityMeasure_map _hXs.aemeasurable
  -- Disintegrate the joint: μ.map (Xs, Yo) = (μ.map Xs) ⊗ₘ condDistrib Yo Xs μ.
  have h_joint : μ.map (fun ω => (Xs ω, Yo ω))
      = (μ.map Xs) ⊗ₘ (condDistrib Yo Xs μ) :=
    (compProd_map_condDistrib hYo.aemeasurable).symm
  -- Joint singleton mass = marginal × conditional (real form).
  have h_pair_real : ∀ (x : X) (y : Y),
      (μ.map (fun ω => (Xs ω, Yo ω))).real {(x, y)}
        = (μ.map Xs).real {x} * (condDistrib Yo Xs μ x).real {y} := by
    intro x y
    rw [Measure.real, Measure.real, Measure.real, h_joint,
      show ({(x, y)} : Set (X × Y)) = {x} ×ˢ {y} from
        (Set.singleton_prod_singleton).symm,
      Measure.compProd_apply_prod (measurableSet_singleton x) (measurableSet_singleton y),
      lintegral_singleton, ENNReal.toReal_mul]
    ring
  -- Each fiber `condDistrib Yo Xs μ x` is a probability measure (Markov kernel).
  have h_cond_sum_one : ∀ x : X, ∑ y : Y, (condDistrib Yo Xs μ x).real {y} = 1 := by
    intro x
    have _ : IsProbabilityMeasure (condDistrib Yo Xs μ x) := inferInstance
    rw [show (∑ y : Y, (condDistrib Yo Xs μ x).real {y})
          = ∑ y ∈ (Finset.univ : Finset Y), (condDistrib Yo Xs μ x).real {y} from rfl,
      sum_measureReal_singleton]
    rw [show ((Finset.univ : Finset Y) : Set Y) = Set.univ from Finset.coe_univ]
    simp [measureReal_def, measure_univ]
  -- Inner conditional-entropy slice as a function of `x`.
  set h : X → ℝ := fun x =>
    ∑ y : Y, Real.negMulLog ((condDistrib Yo Xs μ x).real {y}) with h_def
  -- `h` is measurable and bounded in `[0, |Y|]`, hence integrable on the probability
  -- measure `μ.map Xs`.
  have h_meas_one : ∀ y : Y,
      Measurable (fun x => (condDistrib Yo Xs μ x).real {y}) := fun y =>
    ENNReal.measurable_toReal.comp
      (Kernel.measurable_coe _ (measurableSet_singleton y))
  have h_meas : Measurable h :=
    Finset.measurable_sum _ (fun y _ =>
      Real.continuous_negMulLog.measurable.comp (h_meas_one y))
  have h_le_one : ∀ x y, (condDistrib Yo Xs μ x).real {y} ≤ 1 := fun x y => by
    have _ : IsProbabilityMeasure (condDistrib Yo Xs μ x) := inferInstance
    exact measureReal_le_one
  have h_integrable : Integrable h (μ.map Xs) := by
    apply Integrable.of_mem_Icc 0 (Fintype.card Y) h_meas.aemeasurable
    refine Filter.Eventually.of_forall (fun x => ⟨?_, ?_⟩)
    · exact Finset.sum_nonneg (fun y _ =>
        Real.negMulLog_nonneg measureReal_nonneg (h_le_one x y))
    · calc h x ≤ ∑ _y : Y, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun y _ => ?_)
            have := Real.negMulLog_le_one_sub_self
              (measureReal_nonneg (μ := condDistrib Yo Xs μ x) (s := ({y} : Set Y)))
            linarith [measureReal_nonneg (μ := condDistrib Yo Xs μ x) (s := ({y} : Set Y))]
        _ = (Fintype.card Y : ℝ) := by simp
  -- LHS expansion. Sum over `X × Y` factored as iterated sum.
  unfold entropy
  rw [show (Finset.univ : Finset (X × Y))
        = (Finset.univ : Finset X) ×ˢ (Finset.univ : Finset Y) from rfl,
    Finset.sum_product]
  -- Rewrite the integrand of the inner sum using the joint singleton formula and
  -- the `negMulLog` product rule `negMulLog (a * b) = b * negMulLog a + a * negMulLog b`.
  have h_each : ∀ (x : X) (y : Y),
      Real.negMulLog ((μ.map (fun ω => (Xs ω, Yo ω))).real {(x, y)})
        = (condDistrib Yo Xs μ x).real {y} * Real.negMulLog ((μ.map Xs).real {x})
          + (μ.map Xs).real {x}
              * Real.negMulLog ((condDistrib Yo Xs μ x).real {y}) := fun x y => by
    rw [h_pair_real x y, Real.negMulLog_mul]
  simp_rw [h_each, Finset.sum_add_distrib]
  -- First part: ∑ y, Q(x){y} * negMulLog (P(x)) = (∑ y Q(x){y}) * negMulLog P(x) = negMulLog P(x).
  have h_first : ∀ x : X,
      (∑ y : Y, (condDistrib Yo Xs μ x).real {y} * Real.negMulLog ((μ.map Xs).real {x}))
        = Real.negMulLog ((μ.map Xs).real {x}) := fun x => by
    rw [← Finset.sum_mul, h_cond_sum_one, one_mul]
  -- Second part: ∑ y, P(x) * negMulLog(Q(x){y}) = P(x) * h(x).
  have h_second : ∀ x : X,
      (∑ y : Y, (μ.map Xs).real {x}
            * Real.negMulLog ((condDistrib Yo Xs μ x).real {y}))
        = (μ.map Xs).real {x} * h x := fun x => by
    rw [h_def]
    exact (Finset.mul_sum _ _ _).symm
  simp_rw [h_first, h_second]
  -- RHS condEntropy is ∫ x, h x ∂(μ.map Xs); convert via integral_fintype.
  show (∑ x : X, Real.negMulLog ((μ.map Xs).real {x}))
        + ∑ x : X, (μ.map Xs).real {x} * h x
      = entropy μ Xs + InformationTheory.MeasureFano.condEntropy μ Yo Xs
  rw [show InformationTheory.MeasureFano.condEntropy μ Yo Xs = ∫ x, h x ∂(μ.map Xs) from rfl,
    integral_fintype h_integrable]
  -- entropy μ Xs = ∑ x, negMulLog ((μ.map Xs).real {x}) by definition.
  rfl

omit [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSingletonClass Y]
    [DecidableEq Z] in
/-- Tower of conditional entropy: disintegrating the joint conditioner `(Y, Z)` into
`Z` given `Y` followed by `Y`,
`H(X | Y, Z) = ∫ y, ∫ z, Σ x, negMulLog (condDistrib X (Y,Z) μ (y,z) {x})
                d(condDistrib Z Y μ y) d P_Y`.

The inner expression `Σ x, negMulLog (condDistrib X (Y,Z) μ (y,z) {x})` is the slice-wise
Shannon entropy of `X` conditioned on the simultaneous value of `Y` and `Z`. The two
outer integrals build back up to `H(X | Y, Z)`. Required as a lemma for the middle
result `condMutualInfo_eq_condEntropy_sub_condEntropy`. -/
@[entry_point]
theorem condEntropy_tower
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (_hXs : Measurable Xs) (_hYo : Measurable Yo) (hZo : Measurable Zo) :
    InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
      = ∫ y, ∫ z, ∑ x : X, Real.negMulLog
            ((condDistrib Xs (fun ω => (Yo ω, Zo ω)) μ (y, z)).real {x})
            ∂(condDistrib Zo Yo μ y) ∂(μ.map Yo) := by
  haveI : IsProbabilityMeasure (μ.map (fun ω => (Yo ω, Zo ω))) :=
    Measure.isProbabilityMeasure_map (_hYo.prodMk hZo).aemeasurable
  -- Integrand: f p = ∑ x, negMulLog ((cond Xs (Yo, Zo) μ p).real {x}). Bounded in [0, |X|].
  set f : Y × Z → ℝ := fun p =>
    ∑ x : X, Real.negMulLog
      ((condDistrib Xs (fun ω => (Yo ω, Zo ω)) μ p).real {x}) with hf_def
  have h_meas_one : ∀ x : X,
      Measurable (fun p : Y × Z =>
        (condDistrib Xs (fun ω => (Yo ω, Zo ω)) μ p).real {x}) := fun x =>
    ENNReal.measurable_toReal.comp
      (Kernel.measurable_coe _ (measurableSet_singleton x))
  have h_meas : Measurable f :=
    Finset.measurable_sum _ (fun x _ =>
      Real.continuous_negMulLog.measurable.comp (h_meas_one x))
  have h_le_one : ∀ p x,
      (condDistrib Xs (fun ω => (Yo ω, Zo ω)) μ p).real {x} ≤ 1 := fun p _ => by
    have _ : IsProbabilityMeasure
        (condDistrib Xs (fun ω => (Yo ω, Zo ω)) μ p) := inferInstance
    exact measureReal_le_one
  have h_integrable : Integrable f (μ.map (fun ω => (Yo ω, Zo ω))) := by
    apply Integrable.of_mem_Icc 0 (Fintype.card X) h_meas.aemeasurable
    refine Filter.Eventually.of_forall (fun p => ⟨?_, ?_⟩)
    · exact Finset.sum_nonneg (fun x _ =>
        Real.negMulLog_nonneg measureReal_nonneg (h_le_one p x))
    · calc f p ≤ ∑ _x : X, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun x _ => ?_)
            have := Real.negMulLog_le_one_sub_self
              (measureReal_nonneg
                (μ := condDistrib Xs (fun ω => (Yo ω, Zo ω)) μ p) (s := ({x} : Set X)))
            linarith [measureReal_nonneg
              (μ := condDistrib Xs (fun ω => (Yo ω, Zo ω)) μ p) (s := ({x} : Set X))]
        _ = (Fintype.card X : ℝ) := by simp
  -- Unfold condEntropy, disintegrate μ.map (Yo, Zo), apply integral_compProd.
  unfold InformationTheory.MeasureFano.condEntropy
  have h_yz : μ.map (fun ω => (Yo ω, Zo ω))
      = (μ.map Yo) ⊗ₘ (condDistrib Zo Yo μ) :=
    (compProd_map_condDistrib hZo.aemeasurable).symm
  rw [show (fun y => ∑ x : X, Real.negMulLog
            ((condDistrib Xs (fun ω => (Yo ω, Zo ω)) μ y).real {x})) = f from rfl,
    h_yz, Measure.integral_compProd (h_yz ▸ h_integrable)]

omit [DecidableEq X] [DecidableEq Y] [Nonempty Y] [DecidableEq Z] in
/-- Conditional mutual information formula: `I(X; Z | Y) = H(X | Y) - H(X | Y, Z)`. -/
@[entry_point]
theorem condMutualInfo_eq_condEntropy_sub_condEntropy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
    (condMutualInfo μ Xs Zo Yo).toReal
      = InformationTheory.MeasureFano.condEntropy μ Xs Yo
        - InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω)) := by
  classical
  have hYZ : Measurable (fun ω => (Yo ω, Zo ω)) := hYo.prodMk hZo
  -- Step 1: chain rule with renamed args
  have h_chain := mutualInfo_chain_rule μ Zo Xs Yo hZo hXs hYo
  -- Step 2: commute every term to put Xs on the LHS of the mI/cMI
  rw [mutualInfo_comm μ (fun ω => (Yo ω, Zo ω)) Xs hYZ hXs,
      mutualInfo_comm μ Yo Xs hYo hXs,
      condMutualInfo_comm μ Zo Xs Yo hZo hXs hYo] at h_chain
  -- h_chain: mI(Xs; (Yo,Zo)) = mI(Xs; Yo) + cMI(Xs; Zo | Yo)
  -- Step 3: finiteness for ENNReal.toReal_add
  have h_mI_finite : mutualInfo μ Xs Yo ≠ ∞ :=
    mutualInfo_ne_top μ Xs Yo hXs hYo
  have h_cMI_finite : condMutualInfo μ Xs Zo Yo ≠ ∞ :=
    condMutualInfo_ne_top μ Xs Zo Yo hXs hZo hYo
  -- Step 4: take .toReal and substitute Bridge results
  have h_chain_toReal : (mutualInfo μ Xs (fun ω => (Yo ω, Zo ω))).toReal
      = (mutualInfo μ Xs Yo).toReal + (condMutualInfo μ Xs Zo Yo).toReal := by
    rw [h_chain, ENNReal.toReal_add h_mI_finite h_cMI_finite]
  rw [mutualInfo_eq_entropy_sub_condEntropy μ Xs (fun ω => (Yo ω, Zo ω)) hXs hYZ,
      mutualInfo_eq_entropy_sub_condEntropy μ Xs Yo hXs hYo] at h_chain_toReal
  linarith

omit [DecidableEq X] [DecidableEq Y] [Nonempty Y] [DecidableEq Z] in
/-- Conditioning never increases entropy: `H(X | Y, Z) ≤ H(X | Y)`. Direct corollary of
the middle lemma `condMutualInfo_eq_condEntropy_sub_condEntropy` and
`condMutualInfo_nonneg`. Phase B (n-variable Han) reduces to iterating this on
prefixes of `Fin n`. -/
@[entry_point]
theorem condEntropy_le_condEntropy_of_pair
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
    InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
      ≤ InformationTheory.MeasureFano.condEntropy μ Xs Yo := by
  have h_mid := condMutualInfo_eq_condEntropy_sub_condEntropy μ Xs Yo Zo hXs hYo hZo
  have h_nn : 0 ≤ (condMutualInfo μ Xs Zo Yo).toReal := ENNReal.toReal_nonneg
  linarith

end InformationTheory.Shannon
