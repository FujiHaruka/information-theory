import InformationTheory.Shannon.Sanov.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Moments.Variance

/-!
# Conditional asymptotic equipartition for independent non-identical products

A block `zb : Fin n → T` of symbols selects a per-coordinate observation law `ν (zb i)` on a finite
alphabet `β`, and a per-coordinate statistic `ψ (zb i)`.  The empirical mean of the statistic
concentrates around the ambient mean `∑ p, q p · (ν p)[ψ p]` as soon as the empirical type of the
block is close to `q` in total variation: Chebyshev on the product measure pins the empirical mean
to its own conditional mean, and the type closeness pins that conditional mean to the ambient one.

The two halves are stated separately because their content is different: the Chebyshev half holds
for every block, while the pin half is exactly what strong (rather than entropy-only) typicality
of the block buys.  The pin half amplifies the type radius by `∑ p, |(ν p)[ψ p]|`, so a caller
that needs the ambient deviation below `ε` must supply a block whose type radius is smaller than
`ε` by that factor.

## Main statements

* `pi_nonuniform_mean_concentration` — finite-`n` Chebyshev for a non-identically distributed
  independent product.
* `pi_nonuniform_concentration_tendsto` — its uniform-in-`(ν, ψ)` form under a common sup-bound.
* `sum_eq_typeCount_mul` — method-of-types regrouping of a per-coordinate sum.
* `abs_sum_mul_sub_sum_mul_le` — the linear functional of a type is Lipschitz in the type.
* `pi_empiricalMean_deviation_le_of_type_close` — the two halves combined.

## Implementation notes

The Chebyshev half takes the per-coordinate laws as a bare family `ν : Fin n → Measure β`, whereas
the combined statement takes them as a kernel `ν : T → Measure β` read along a block; a caller that
holds only a family, with no block to read it along, uses the former directly.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false

variable {T β : Type*} [Fintype T] [DecidableEq T]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ### Chebyshev on a non-identically distributed product -/

/-- Chebyshev's inequality for an independent, not identically distributed product: the mass the
product `Measure.pi ν` puts on the blocks whose empirical mean of `ψ` deviates from the mean of the
per-coordinate means by `δ` or more is at most `(∑ i, variance (ψ i) (ν i)) / (n ^ 2 * δ ^ 2)`. -/
lemma pi_nonuniform_mean_concentration
    {n : ℕ} (hn : 0 < n)
    (ν : Fin n → Measure β) [∀ i, IsProbabilityMeasure (ν i)]
    (ψ : Fin n → β → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi ν).real
        { yb : Fin n → β | δ ≤ |(∑ i, ψ i (yb i)) / (n : ℝ)
            - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)| }
      ≤ (∑ i, variance (ψ i) (ν i)) / ((n : ℝ) ^ 2 * δ ^ 2) := by
  classical
  set μpi : Measure (Fin n → β) := Measure.pi ν with hμpi
  haveI : IsProbabilityMeasure μpi := by rw [hμpi]; infer_instance
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmemν : ∀ i, MemLp (ψ i) 2 (ν i) := fun i ↦ MemLp.of_discrete
  have hmemcoord : ∀ i : Fin n, MemLp (fun yb : Fin n → β ↦ ψ i (yb i)) 2 μpi :=
    fun i ↦ (hmemν i).comp_measurePreserving (measurePreserving_eval ν i)
  set S : (Fin n → β) → ℝ := fun yb ↦ ∑ i, ψ i (yb i) with hS
  have hSmem : MemLp S 2 μpi := by
    have hsum := memLp_finsetSum (μ := μpi) (p := (2 : ℝ≥0∞)) Finset.univ
      (f := fun (i : Fin n) (yb : Fin n → β) ↦ ψ i (yb i)) (fun i _ ↦ hmemcoord i)
    exact hsum
  have hVarS : variance S μpi = ∑ i, variance (ψ i) (ν i) := by
    have hpi := variance_sum_pi (ι := Fin n) (Ω := fun _ : Fin n ↦ β)
      (μ := ν) (X := ψ) hmemν
    rw [hS, show (fun yb : Fin n → β ↦ ∑ i, ψ i (yb i))
        = (∑ i, fun ω : Fin n → β ↦ ψ i (ω i)) by
      funext yb; simp [Finset.sum_apply]]
    rw [hpi]
  have hmeanS : μpi[S] = ∑ i, ∫ y, ψ i y ∂(ν i) := by
    have hint : ∀ i : Fin n, μpi[fun yb : Fin n → β ↦ ψ i (yb i)] = ∫ y, ψ i y ∂(ν i) := by
      intro i
      have hmp : MeasurePreserving (Function.eval i) μpi (ν i) := measurePreserving_eval ν i
      calc μpi[fun yb : Fin n → β ↦ ψ i (yb i)]
          = ∫ yb, ψ i (Function.eval i yb) ∂μpi := rfl
        _ = ∫ y, ψ i y ∂(Measure.map (Function.eval i) μpi) := by
              rw [integral_map hmp.measurable.aemeasurable]
              exact (hmemν i).aestronglyMeasurable.aemeasurable.aestronglyMeasurable.mono_ac
                (by rw [hmp.map_eq])
        _ = ∫ y, ψ i y ∂(ν i) := by rw [hmp.map_eq]
    rw [hS, integral_finsetSum]
    · exact Finset.sum_congr rfl (fun i _ ↦ hint i)
    · exact fun i _ ↦ (hmemcoord i).integrable (by norm_num)
  have habs : ∀ yb : Fin n → β,
      |S yb - μpi[S]| = (n : ℝ) * |(∑ i, ψ i (yb i)) / (n : ℝ)
          - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)| := by
    intro yb
    rw [hmeanS]
    rw [show (n : ℝ) * |(∑ i, ψ i (yb i)) / (n : ℝ) - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)|
          = |(n : ℝ) * ((∑ i, ψ i (yb i)) / (n : ℝ)
              - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ))| by
        rw [abs_mul, abs_of_pos hnR]]
    congr 1
    simp only [hS]
    field_simp
  have hset : { yb : Fin n → β | δ ≤ |(∑ i, ψ i (yb i)) / (n : ℝ)
          - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)| }
      = { yb : Fin n → β | (n : ℝ) * δ ≤ |S yb - μpi[S]| } := by
    ext yb
    simp only [Set.mem_setOf_eq, habs yb]
    constructor
    · intro h; exact mul_le_mul_of_nonneg_left h hnR.le
    · intro h; exact le_of_mul_le_mul_left h hnR
  rw [measureReal_def, hset]
  have hcheb := meas_ge_le_variance_div_sq (μ := μpi) hSmem (c := (n : ℝ) * δ) (by positivity)
  calc (μpi { yb : Fin n → β | (n : ℝ) * δ ≤ |S yb - μpi[S]| }).toReal
      ≤ (ENNReal.ofReal (variance S μpi / ((n : ℝ) * δ) ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ = variance S μpi / ((n : ℝ) * δ) ^ 2 :=
        ENNReal.toReal_ofReal (div_nonneg (variance_nonneg S μpi) (by positivity))
    _ = (∑ i, variance (ψ i) (ν i)) / ((n : ℝ) ^ 2 * δ ^ 2) := by rw [hVarS, mul_pow]

/-- The uniform form of the Chebyshev bound: past a threshold determined by the sup-bound `B`, the
deviation `δ` and the tolerance `tol` alone, every independent non-identically distributed product
of statistics bounded by `B` puts mass at most `tol` on the `δ`-deviation set of the empirical mean.

@audit:ok -/
lemma pi_nonuniform_concentration_tendsto
    {B δ tol : ℝ} (hδ : 0 < δ) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (ν : Fin n → Measure β),
        (∀ i, IsProbabilityMeasure (ν i)) → ∀ (ψ : Fin n → β → ℝ),
        (∀ i y, |ψ i y| ≤ B) →
        (Measure.pi ν).real
            { yb : Fin n → β | δ ≤ |(∑ i, ψ i (yb i)) / (n : ℝ)
                - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)| }
          ≤ tol := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (B ^ 2 / (tol * δ ^ 2))
  refine ⟨N₀ + 1, fun n hn ν hν ψ hψ ↦ ?_⟩
  have hn_pos : 0 < n := lt_of_lt_of_le (Nat.succ_pos N₀) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn_pos
  haveI : ∀ i, IsProbabilityMeasure (ν i) := hν
  have hcheb := pi_nonuniform_mean_concentration hn_pos ν ψ (δ := δ) hδ
  have hvar_le : ∀ i, variance (ψ i) (ν i) ≤ B ^ 2 := by
    intro i
    have hIcc : ∀ᵐ y ∂(ν i), ψ i y ∈ Set.Icc (-B) B :=
      Filter.Eventually.of_forall (fun y ↦ abs_le.mp (hψ i y))
    have hbdd := variance_le_sq_of_bounded hIcc (measurable_of_finite (ψ i)).aemeasurable
    calc variance (ψ i) (ν i) ≤ ((B - (-B)) / 2) ^ 2 := hbdd
      _ = B ^ 2 := by ring
  have hsum_var : (∑ i, variance (ψ i) (ν i)) ≤ (n : ℝ) * B ^ 2 := by
    calc (∑ i, variance (ψ i) (ν i)) ≤ ∑ _i : Fin n, B ^ 2 :=
          Finset.sum_le_sum (fun i _ ↦ hvar_le i)
      _ = (n : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 * δ ^ 2 := by positivity
  have hstep1 : (∑ i, variance (ψ i) (ν i)) / ((n : ℝ) ^ 2 * δ ^ 2)
      ≤ ((n : ℝ) * B ^ 2) / ((n : ℝ) ^ 2 * δ ^ 2) := by
    gcongr
  have hstep2 : ((n : ℝ) * B ^ 2) / ((n : ℝ) ^ 2 * δ ^ 2) = B ^ 2 / ((n : ℝ) * δ ^ 2) := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    field_simp
  have hstep3 : B ^ 2 / ((n : ℝ) * δ ^ 2) ≤ tol := by
    have hnδ : (0 : ℝ) < (n : ℝ) * δ ^ 2 := by positivity
    rw [div_le_iff₀ hnδ]
    have htolδ : (0 : ℝ) < tol * δ ^ 2 := by positivity
    have hn_gt : B ^ 2 / (tol * δ ^ 2) < (n : ℝ) := by
      have : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.trans' (Nat.le_succ N₀)
      linarith [hN₀]
    have hlt : B ^ 2 < (n : ℝ) * (tol * δ ^ 2) := by
      rw [div_lt_iff₀ htolδ] at hn_gt; linarith [hn_gt]
    nlinarith [hlt]
  calc (Measure.pi ν).real
          { yb : Fin n → β | δ ≤ |(∑ i, ψ i (yb i)) / (n : ℝ)
              - (∑ i, ∫ y, ψ i y ∂(ν i)) / (n : ℝ)| }
        ≤ (∑ i, variance (ψ i) (ν i)) / ((n : ℝ) ^ 2 * δ ^ 2) := hcheb
      _ ≤ ((n : ℝ) * B ^ 2) / ((n : ℝ) ^ 2 * δ ^ 2) := hstep1
      _ = B ^ 2 / ((n : ℝ) * δ ^ 2) := hstep2
      _ ≤ tol := hstep3

/-! ### Linear functionals of an empirical type -/

/-- Method-of-types regrouping: summing a statistic over the coordinates of a block equals summing
it over the alphabet, each letter weighted by the number of coordinates carrying it. -/
lemma sum_eq_typeCount_mul {n : ℕ} (z : Fin n → T) (f : T → ℝ) :
    ∑ i, f (z i) = ∑ p : T, (typeCount z p : ℝ) * f p := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset T)) (g := z) (fun i _ ↦ Finset.mem_univ _) f]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The linear functional `t ↦ ∑ p, t p * g p` is Lipschitz in the coordinatewise distance of its
argument, with constant `∑ p, |g p|`. -/
lemma abs_sum_mul_sub_sum_mul_le (t q g : T → ℝ) {r : ℝ}
    (hclose : ∀ p, |t p - q p| ≤ r) :
    |(∑ p, t p * g p) - ∑ p, q p * g p| ≤ (∑ p, |g p|) * r := by
  classical
  have hdiff : (∑ p, t p * g p) - ∑ p, q p * g p = ∑ p, (t p - q p) * g p := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ by ring
  rw [hdiff]
  calc |∑ p, (t p - q p) * g p|
      ≤ ∑ p, |(t p - q p) * g p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, r * |g p| := by
        refine Finset.sum_le_sum fun p _ ↦ ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hclose p) (abs_nonneg _)
    _ = (∑ p, |g p|) * r := by rw [← Finset.mul_sum, mul_comm]

/-! ### The conditional AEP -/

/-- For a block `zb` whose empirical type is within `r` of `q`, the product measure
`Measure.pi (fun i ↦ ν (zb i))` puts mass at most `tol` on the blocks whose empirical statistic
deviates from the ambient mean `∑ p, q p · (ν p)[ψ p]` by `ε` or more, once `n ≥ N`.  The
threshold `N` depends only on the sup-bound `B`, the deviation `ε` and the tolerance `tol`; the
block, the type radius, the statistic and the kernel are quantified afterwards, so a caller may
apply it uniformly over a code ensemble.

The hypothesis `hpin` is the radius separation: the type radius `r` must beat `ε/2` after
amplification by `∑ p, |(ν p)[ψ p]|`.  At `r = ε` the conclusion is false in general — the
amplification constant is unrelated to `ε` — so a caller must shrink the type radius by that
factor before invoking this.  The reference vector `q` is arbitrary: the conclusion measures the
deviation from `q`'s own mean, so no consistency or full-support precondition on `q` arises here;
a caller that wants the deviation read against an entropy supplies that identification itself.

@audit:ok -/
theorem pi_empiricalMean_deviation_le_of_type_close
    {B ε tol : ℝ} (hε : 0 < ε) (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (ν : T → Measure β),
        (∀ p, IsProbabilityMeasure (ν p)) → ∀ (ψ : T → β → ℝ),
        (∀ p y, |ψ p y| ≤ B) → ∀ (q : T → ℝ) (r : ℝ) (zb : Fin n → T),
        (∀ p, |(typeCount zb p : ℝ) / (n : ℝ) - q p| ≤ r) →
        (∑ p, |∫ y, ψ p y ∂(ν p)|) * r < ε / 2 →
        (Measure.pi (fun i ↦ ν (zb i))).real
            { yb : Fin n → β | ε ≤ |(∑ i, ψ (zb i) (yb i)) / (n : ℝ)
                - ∑ p, q p * ∫ y, ψ p y ∂(ν p)| }
          ≤ tol := by
  classical
  obtain ⟨N, hN⟩ := pi_nonuniform_concentration_tendsto (β := β)
    (B := B) (δ := ε / 2) (tol := tol) (by linarith) htol
  refine ⟨N, fun n hn ν hν ψ hψ q r zb hclose hpin ↦ ?_⟩
  haveI : ∀ i : Fin n, IsProbabilityMeasure (ν (zb i)) := fun i ↦ hν (zb i)
  set g : T → ℝ := fun p ↦ ∫ y, ψ p y ∂(ν p) with hg
  -- The conditional mean of the block is the type-weighted mean of `g`.
  have hmean_eq : (∑ i, ∫ y, ψ (zb i) y ∂(ν (zb i))) / (n : ℝ)
      = ∑ p, ((typeCount zb p : ℝ) / (n : ℝ)) * g p := by
    rw [show (∑ i, ∫ y, ψ (zb i) y ∂(ν (zb i))) = ∑ i, g (zb i) from rfl,
      sum_eq_typeCount_mul zb g, Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ ↦ by ring
  -- Type closeness pins that conditional mean to the ambient mean, strictly inside `ε/2`.
  have hpin' : |(∑ i, ∫ y, ψ (zb i) y ∂(ν (zb i))) / (n : ℝ) - ∑ p, q p * g p| < ε / 2 := by
    rw [hmean_eq]
    exact lt_of_le_of_lt
      (abs_sum_mul_sub_sum_mul_le (fun p ↦ (typeCount zb p : ℝ) / (n : ℝ)) q g hclose) hpin
  -- Chebyshev around the conditional mean, then the triangle inequality.
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (hN n hn (fun i ↦ ν (zb i)) (fun i ↦ hν (zb i)) (fun i ↦ ψ (zb i)) (fun i y ↦ hψ (zb i) y))
  intro yb hyb
  simp only [Set.mem_setOf_eq] at hyb ⊢
  have htri := abs_sub_le
    ((∑ i, ψ (zb i) (yb i)) / (n : ℝ))
    ((∑ i, ∫ y, ψ (zb i) y ∂(ν (zb i))) / (n : ℝ))
    (∑ p, q p * g p)
  linarith [hyb, htri, hpin']

end InformationTheory.Shannon
