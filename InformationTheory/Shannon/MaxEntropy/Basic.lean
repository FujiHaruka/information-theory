import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Bridge
import Mathlib.Probability.UniformOn
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Maximum entropy (Gibbs inequality)

For a finite-alphabet random variable `X : Ω → α`,
`entropy μ X ≤ Real.log (Fintype.card α)`,
with equality if and only if `μ.map X = uniformOn Set.univ`.

## Main definitions

## Main statements

* `klDiv_uniformOn_univ_toReal_eq` — KL-divergence identity:
  `(klDiv (μ.map X) (uniformOn univ)).toReal = log |α| − entropy μ X`.
* `entropy_le_log_card` — Shannon entropy is at most `log |α|`.
* `entropy_eq_log_card_iff` — equality holds if and only if `μ.map X = uniformOn univ`.

## Implementation notes

The main results follow directly from concavity of `negMulLog` on `Set.Ici 0` via the
finite-sum Jensen inequality (`ConcaveOn.le_map_sum` and
`StrictConcaveOn.map_sum_eq_iff`), with uniform weights `1/N` (`N = |α|`).
No KL-divergence machinery is needed; `klDiv_uniformOn_univ_toReal_eq` is a secondary
identity derived from the same computation. This is the general-measure analogue of
`LoomisWhitney.entropy_le_log_image_card`.
-/

namespace InformationTheory.Shannon.MaxEntropy

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

omit [DecidableEq α] [Nonempty α] in
/-- The ENNReal singleton mass of `uniformOn (univ : Set α)` is `1 / |α|`. -/
private lemma uniformOn_univ_apply_singleton (x : α) :
    (uniformOn (Set.univ : Set α)) ({x} : Set α) = 1 / (Fintype.card α : ℝ≥0∞) := by
  classical
  have h_set : ({x} : Set α) = (({x} : Finset α) : Set α) := by simp
  rw [h_set]
  rw [show (Set.univ : Set α) = ((Finset.univ : Finset α) : Set α) from
        (Finset.coe_univ).symm,
      uniformOn_apply_finset, Finset.univ_inter, Finset.card_singleton,
      Finset.card_univ, Nat.cast_one]

omit [DecidableEq α] [Nonempty α] in
/-- The `measureReal` singleton mass of `uniformOn (univ : Set α)` is `1 / |α|`. -/
private lemma uniformOn_univ_real_singleton (x : α) :
    (uniformOn (Set.univ : Set α)).real ({x} : Set α) = (1 : ℝ) / Fintype.card α := by
  rw [Measure.real, uniformOn_univ_apply_singleton x,
    ENNReal.toReal_div, ENNReal.toReal_one]
  rfl

omit [DecidableEq α] [Nonempty α] in
/-- Any pushforward `μ.map X` is absolutely continuous with respect to `uniformOn univ`. -/
private lemma map_absolutelyContinuous_uniformOn_univ
    (μ : Measure Ω) (X : Ω → α) :
    (μ.map X) ≪ uniformOn (Set.univ : Set α) := by
  classical
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 ↦ ?_
  -- decompose A = ⋃ x ∈ univ.filter (· ∈ A), {x}
  set s : Finset α := Finset.univ.filter (fun x ↦ x ∈ A)
  have hA_decomp : A = ⋃ x ∈ s, ({x} : Set α) := by
    ext z
    simp [s]
  have h_meas : ∀ x ∈ s, MeasurableSet ({x} : Set α) :=
    fun x _ ↦ measurableSet_singleton x
  have h_pwd : Set.PairwiseDisjoint (↑s) (fun x : α ↦ ({x} : Set α)) :=
    fun a _ b _ hne ↦ Set.disjoint_singleton.mpr hne
  -- U A = 0 ⟹ s = ∅ (each singleton has positive mass)
  have hU_each_pos : ∀ x : α,
      (uniformOn (Set.univ : Set α)) ({x} : Set α) ≠ 0 := by
    intro x
    rw [uniformOn_univ_apply_singleton x]
    intro h
    rw [ENNReal.div_eq_zero_iff] at h
    rcases h with h1 | h2
    · exact one_ne_zero h1
    · exact (ENNReal.natCast_ne_top _) h2
  have h_s_empty : s = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hxs
    have hxA : ({x} : Set α) ⊆ A := by
      have : x ∈ A := (Finset.mem_filter.mp hxs).2
      intro z hz; rw [Set.mem_singleton_iff] at hz; exact hz ▸ this
    have hle : (uniformOn (Set.univ : Set α)) ({x} : Set α) ≤ 0 := by
      rw [← hA0]
      exact measure_mono hxA
    exact hU_each_pos x (le_antisymm hle bot_le)
  -- μ.map X (A) = sum over s = 0
  rw [hA_decomp, measure_biUnion_finset h_pwd h_meas, h_s_empty]
  simp

omit [DecidableEq α] [Nonempty α] in
/-- Absolute continuity and integrability of `llr` imply `klDiv` is finite. -/
private lemma klDiv_map_uniformOn_univ_ne_top
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) :
    klDiv (μ.map X) (uniformOn (Set.univ : Set α)) ≠ ∞ := by
  classical
  have _hP : IsProbabilityMeasure (μ.map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  have hac := map_absolutelyContinuous_uniformOn_univ μ X
  -- llr is integrable on a Fintype (finite measure, log is bounded by log |α|)
  have h_int : Integrable (llr (μ.map X) (uniformOn (Set.univ : Set α))) (μ.map X) := by
    refine ⟨(measurable_llr _ _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ ↦
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  exact klDiv_ne_top hac h_int

/-! ## KL-divergence identity -/

omit [DecidableEq α] in
/-- `(klDiv (μ.map X) (uniformOn univ)).toReal = log |α| - entropy μ X`. -/
@[entry_point]
theorem klDiv_uniformOn_univ_toReal_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    (klDiv (μ.map X) (uniformOn (Set.univ : Set α))).toReal
      = Real.log (Fintype.card α) - entropy μ X := by
  classical
  set N : ℕ := Fintype.card α with hN_def
  have hN_pos : 0 < N := Fintype.card_pos
  have hN_pos_R : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have hN_ne_R : (N : ℝ) ≠ 0 := hN_pos_R.ne'
  set P : Measure α := μ.map X with hP_def
  set U : Measure α := uniformOn (Set.univ : Set α) with hU_def
  haveI hP : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI hU : IsProbabilityMeasure U := by rw [hU_def]; infer_instance
  have hPU : P ≪ U := map_absolutelyContinuous_uniformOn_univ μ X
  -- toReal_klDiv_of_measure_eq
  have h_univ : P Set.univ = U Set.univ := by
    rw [measure_univ, measure_univ]
  rw [toReal_klDiv_of_measure_eq hPU h_univ]
  -- ∫ a, llr P U a ∂P  with  llr P U x = log (P.rnDeriv U x).toReal
  -- (P.rnDeriv U x).toReal * U.real{x} = P.real{x}
  -- U.real{x} = 1/N ⟹ (P.rnDeriv U x).toReal = N * P.real{x}
  have h_U_singleton : ∀ x : α, U.real {x} = (1 : ℝ) / N := by
    intro x
    rw [hU_def]
    exact uniformOn_univ_real_singleton x
  -- llr identity ae P: when P{x} > 0 we have P.rnDeriv U x = N * P{x}.
  -- For x with P{x} = 0, llr is irrelevant (vanishes in the Bochner integral).
  -- Goal: ∫ a, llr P U a ∂P = log N - entropy μ X.
  -- Step: rewrite ∫ as a Fintype sum (integral_fintype after integrability).
  have h_int : Integrable (llr P U) P := by
    refine ⟨(measurable_llr _ _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_fintype]
    exact ENNReal.sum_lt_top.mpr fun _ _ ↦
      ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _)
  rw [integral_fintype h_int]
  -- ∑ x, P.real {x} • llr P U x
  -- For each x, P.real{x} * llr P U x.
  -- Case P{x} = 0: term is 0.
  -- Case P{x} > 0: (P.rnDeriv U x).toReal = P.real{x} / U.real{x} = N * P.real{x},
  --                so llr = log N + log P.real{x}.
  -- Sum = ∑ P.real{x} * (log N + log P.real{x}) = log N * 1 + ∑ P{x} log P{x}
  --     = log N - entropy μ X.
  have h_term : ∀ x : α,
      P.real {x} • llr P U x
        = P.real {x} * Real.log N - Real.negMulLog (P.real {x}) := by
    intro x
    by_cases hPx : P.real {x} = 0
    · simp [hPx, Real.negMulLog_zero]
    have hPx_pos : 0 < P.real {x} :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hPx)
    have hP_ne : P {x} ≠ 0 := by
      intro h
      apply hPx
      rw [Measure.real, h]; rfl
    -- rnDeriv identification: (P.rnDeriv U x) * U {x} = P {x}.
    have h_rnD_enn : (P.rnDeriv U x) * U {x} = P {x} := by
      have h_wd : U.withDensity (P.rnDeriv U) = P :=
        Measure.withDensity_rnDeriv_eq P U hPU
      have h1 : (U.withDensity (P.rnDeriv U)) {x} = P {x} := by rw [h_wd]
      rw [withDensity_apply _ (measurableSet_singleton x),
        lintegral_singleton] at h1
      exact h1
    have h_rnD_real : (P.rnDeriv U x).toReal * U.real {x} = P.real {x} := by
      rw [Measure.real, Measure.real, ← ENNReal.toReal_mul, h_rnD_enn]
    have hU_pos : 0 < U.real {x} := by
      rw [h_U_singleton x]
      positivity
    have h_rnD_eq : (P.rnDeriv U x).toReal = (N : ℝ) * P.real {x} := by
      have h_U_val : U.real {x} = 1 / N := h_U_singleton x
      have h_NPx : (N : ℝ) * P.real {x} * (1 / N) = P.real {x} := by
        field_simp
      have h_eq2 : (P.rnDeriv U x).toReal * (1 / N) = P.real {x} := by
        rw [← h_U_val]; exact h_rnD_real
      have hUne : ((1 : ℝ) / N) ≠ 0 := by positivity
      have := h_eq2.trans h_NPx.symm
      exact mul_right_cancel₀ hUne this
    -- llr = log ((N : ℝ) * P.real {x}) = log N + log P.real {x}
    have h_NPx_pos : 0 < (N : ℝ) * P.real {x} := mul_pos hN_pos_R hPx_pos
    have h_llr : llr P U x = Real.log N + Real.log (P.real {x}) := by
      unfold llr
      rw [h_rnD_eq, Real.log_mul hN_ne_R hPx_pos.ne']
    rw [h_llr, smul_eq_mul, Real.negMulLog]
    ring
  simp_rw [h_term]
  rw [Finset.sum_sub_distrib]
  -- ∑ x, P.real {x} * log N = log N * 1 = log N (since ∑ P.real{x} = 1).
  rw [show (∑ x : α, P.real {x} * Real.log N)
        = (∑ x : α, P.real {x}) * Real.log N from
        (Finset.sum_mul _ _ _).symm]
  have h_sum_one : ∑ x : α, P.real {x} = 1 := by
    rw [show (∑ x : α, P.real {x})
          = ∑ x ∈ (Finset.univ : Finset α), P.real {x} from rfl,
        sum_measureReal_singleton]
    rw [show ((Finset.univ : Finset α) : Set α) = Set.univ from Finset.coe_univ]
    simp [measureReal_def, measure_univ]
  rw [h_sum_one, one_mul]
  -- ∑ x, negMulLog (P.real {x}) = entropy μ X (by definition of entropy).
  show Real.log N - ∑ x : α, Real.negMulLog (P.real {x})
    = Real.log N - entropy μ X
  rfl

/-! ## Main theorem via Jensen's inequality -/

omit [DecidableEq α] in
/-- **Gibbs' inequality** (uniform bound): the Shannon entropy of a finite-alphabet
random variable is at most `log |α|`. -/
@[entry_point]
theorem entropy_le_log_card
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    entropy μ X ≤ Real.log (Fintype.card α) := by
  classical
  set N : ℕ := Fintype.card α with hN_def
  have hN_pos : 0 < N := Fintype.card_pos
  have hN_pos_R : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have hN_ne_R : (N : ℝ) ≠ 0 := hN_pos_R.ne'
  set P : Measure α := μ.map X with hP_def
  haveI hP : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hent : entropy μ X = ∑ x : α, Real.negMulLog (P.real {x}) := rfl
  have h_sum_one : ∑ x : α, P.real {x} = 1 := by
    rw [show (∑ x : α, P.real {x}) = ∑ x ∈ (Finset.univ : Finset α), P.real {x} from rfl,
        sum_measureReal_singleton]
    rw [show ((Finset.univ : Finset α) : Set α) = Set.univ from Finset.coe_univ]
    simp [measureReal_def, measure_univ]
  -- finite-sum Jensen: uniform weights 1/N, each point P.real {x} ∈ Ici 0
  have hw0 : ∀ i ∈ (Finset.univ : Finset α), (0 : ℝ) ≤ 1 / N := fun _ _ ↦ by positivity
  have hw1 : ∑ _i ∈ (Finset.univ : Finset α), (1 : ℝ) / N = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div, div_self hN_ne_R]
  have hmem : ∀ i ∈ (Finset.univ : Finset α), P.real {i} ∈ Set.Ici (0 : ℝ) :=
    fun _ _ ↦ Set.mem_Ici.mpr measureReal_nonneg
  have hJ := Real.concaveOn_negMulLog.le_map_sum
      (t := (Finset.univ : Finset α)) (w := fun _ ↦ (1 : ℝ) / N)
      (p := fun i ↦ P.real {i}) hw0 hw1 hmem
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum, h_sum_one, mul_one, ← hent] at hJ
  -- hJ : (1 / N) * entropy μ X ≤ negMulLog (1 / N)
  have hneg : Real.negMulLog (1 / (N : ℝ)) = (1 / N) * Real.log N := by
    rw [Real.negMulLog, one_div, Real.log_inv]; ring
  rw [hneg] at hJ
  exact le_of_mul_le_mul_left hJ (by positivity)

/-! ## Equality condition -/

omit [DecidableEq α] in
/-- **Gibbs' inequality** (equality condition): equality `entropy μ X = log |α|`
holds if and only if `μ.map X = uniformOn univ`. -/
@[entry_point]
theorem entropy_eq_log_card_iff
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) :
    entropy μ X = Real.log (Fintype.card α)
      ↔ μ.map X = uniformOn (Set.univ : Set α) := by
  classical
  set N : ℕ := Fintype.card α with hN_def
  have hN_pos : 0 < N := Fintype.card_pos
  have hN_pos_R : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have hN_ne_R : (N : ℝ) ≠ 0 := hN_pos_R.ne'
  set P : Measure α := μ.map X with hP_def
  haveI hP : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hent : entropy μ X = ∑ x : α, Real.negMulLog (P.real {x}) := rfl
  have h_sum_one : ∑ x : α, P.real {x} = 1 := by
    rw [show (∑ x : α, P.real {x}) = ∑ x ∈ (Finset.univ : Finset α), P.real {x} from rfl,
        sum_measureReal_singleton]
    rw [show ((Finset.univ : Finset α) : Set α) = Set.univ from Finset.coe_univ]
    simp [measureReal_def, measure_univ]
  have hw0 : ∀ i ∈ (Finset.univ : Finset α), (0 : ℝ) < 1 / N := fun _ _ ↦ by positivity
  have hw1 : ∑ _i ∈ (Finset.univ : Finset α), (1 : ℝ) / N = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div, div_self hN_ne_R]
  have hmem : ∀ i ∈ (Finset.univ : Finset α), P.real {i} ∈ Set.Ici (0 : ℝ) :=
    fun _ _ ↦ Set.mem_Ici.mpr measureReal_nonneg
  -- strict-concave Jensen equality case (positive weights 1/N)
  have hJiff := Real.strictConcaveOn_negMulLog.map_sum_eq_iff
      (t := (Finset.univ : Finset α)) (w := fun _ ↦ (1 : ℝ) / N)
      (p := fun i ↦ P.real {i}) hw0 hw1 hmem
  simp only [smul_eq_mul] at hJiff
  rw [← Finset.mul_sum, ← Finset.mul_sum, h_sum_one, mul_one, ← hent] at hJiff
  have hneg : Real.negMulLog (1 / (N : ℝ)) = (1 / N) * Real.log N := by
    rw [Real.negMulLog, one_div, Real.log_inv]; ring
  rw [hneg] at hJiff
  -- hJiff : (1/N) * log N = (1/N) * entropy μ X ↔ ∀ j ∈ univ, P.real {j} = 1/N
  -- bridge1: cancel 1/N to get entropy = log N
  have hbridge1 : (entropy μ X = Real.log N)
      ↔ ((1 : ℝ) / N * Real.log N = 1 / N * entropy μ X) := by
    constructor
    · intro h; rw [h]
    · intro h
      exact (mul_left_cancel₀ (by positivity : (1 : ℝ) / N ≠ 0) h).symm
  -- bridge2: all singleton masses equal 1/N ↔ P = uniformOn univ (by singleton ext)
  have hbridge2 : (∀ j ∈ (Finset.univ : Finset α), P.real {j} = 1 / N)
      ↔ P = uniformOn (Set.univ : Set α) := by
    constructor
    · intro h
      apply Measure.ext_of_singleton
      intro a
      have hreal : P.real {a} = (uniformOn (Set.univ : Set α)).real {a} := by
        rw [h a (Finset.mem_univ a), uniformOn_univ_real_singleton a]
      exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal
    · intro h j _
      rw [h]; exact uniformOn_univ_real_singleton j
  rw [hbridge1, hJiff]
  exact hbridge2

end InformationTheory.Shannon.MaxEntropy
