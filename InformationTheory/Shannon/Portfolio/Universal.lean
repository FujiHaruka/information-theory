import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.Compact
import InformationTheory.Meta.EntryPoint

/-!
# Cover's universal portfolio (Cover–Thomas Section 16.7)

For a market on `Fin (d + 1)` stocks with a fixed data stream of price relatives
`xs : ℕ → Fin (d + 1) → ℝ`, the wealth of a constant-rebalanced portfolio `b` on the
simplex after `n` periods is `constWealth xs b n = ∏ i < n, (b · xs i)`. Cover's
*universal portfolio* averages the constant-rebalanced wealth uniformly over the
simplex, giving `universalWealth xs n = (∫ b, constWealth xs b n) / vol`. The main
result (Theorem 16.7.1) is that this achieves the same exponential growth rate as the
best constant-rebalanced portfolio chosen in hindsight: the per-period regret
`(1 / n) · (log S*_n − log Ŝ_n)` tends to `0`.

The simplex is parametrized by its `d` free coordinates: the corner simplex
`cornerSimplex d = {y | 0 ≤ y ∧ ∑ y ≤ 1}` carries the ambient Lebesgue measure of
`Fin d → ℝ`, and `simplexLift` sends `y` to the full portfolio with last coordinate
`1 − ∑ y`. This makes the uniform measure on the simplex an honest, computable object
(the intrinsic `(d)`-dimensional measure on the affine hyperplane `∑ b = 1` has no
Mathlib API, whereas the corner parametrization only needs `volume` on `Fin d → ℝ`).

## Main definitions

* `cornerSimplex` — the `d`-dimensional corner simplex in `Fin d → ℝ`.
* `simplexLift` — lifts free coordinates `y` to a portfolio on `Fin (d + 1)`.
* `constWealth` — wealth `∏ i < n, (b · xs i)` of a constant-rebalanced portfolio.
* `universalWealth` — Cover's universal wealth, the uniform average over the simplex.
* `bestConstantWealth` — the best constant-rebalanced wealth in hindsight, `S*_n`.
* `universalRegret` — the per-period regret `(log S*_n − log Ŝ_n) / n`.

## Main statements

* `universal_portfolio_regret_tendsto_zero` — Theorem 16.7.1: the per-period regret of
  the universal portfolio tends to `0`.

## Implementation notes

The regret theorem is derived from three analytic facts about the universal wealth —
positivity, the average bound `Ŝ_n ≤ S*_n`, and Cover's shrink bound
`S*_n ≤ e · (n + 1) ^ d · Ŝ_n`. The shrink bound
uses `MeasureTheory.Measure.addHaar_image_homothety`: the homothety
`b ↦ (1 − λ) b* + λ b` scales simplex volume by `λ ^ d`, and on its image the wealth
stays within a factor `(1 − λ) ^ n ≥ e⁻¹` of the optimum.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  Section 16.7.
-/

namespace InformationTheory.Shannon.Portfolio

open MeasureTheory Filter Real
open scoped BigOperators Topology

variable {d : ℕ}

/-- The corner simplex `{y : Fin d → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}`, the domain
of the `d` free coordinates of a portfolio on `Fin (d + 1)` stocks. It carries the
ambient Lebesgue measure of `Fin d → ℝ`. -/
def cornerSimplex (d : ℕ) : Set (Fin d → ℝ) := {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1}

/-- Lift the free coordinates `y : Fin d → ℝ` to a full portfolio on `Fin (d + 1)`
stocks by appending the last coordinate `1 − ∑ i, y i`. -/
noncomputable def simplexLift (y : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc y (1 - ∑ i, y i)

/-- Wealth `∏ i < n, (b · xs i)` of the constant-rebalanced portfolio `b` after `n`
periods with price relatives `xs`. -/
noncomputable def constWealth
    (xs : ℕ → Fin (d + 1) → ℝ) (b : Fin (d + 1) → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∑ j, b j * xs i j

/-- Cover's universal wealth `Ŝ_n`: the uniform average of the constant-rebalanced
wealth over the simplex, computed via the corner parametrization. -/
noncomputable def universalWealth (xs : ℕ → Fin (d + 1) → ℝ) (n : ℕ) : ℝ :=
  (∫ y in cornerSimplex d, constWealth xs (simplexLift y) n) / (volume (cornerSimplex d)).toReal

/-- The best constant-rebalanced wealth in hindsight `S*_n = ⨆ b, constWealth xs b n`,
the supremum over the simplex. -/
noncomputable def bestConstantWealth (xs : ℕ → Fin (d + 1) → ℝ) (n : ℕ) : ℝ :=
  ⨆ b : stdSimplex ℝ (Fin (d + 1)), constWealth xs (b : Fin (d + 1) → ℝ) n

/-- The per-period regret `(log S*_n − log Ŝ_n) / n` of the universal portfolio. -/
noncomputable def universalRegret (xs : ℕ → Fin (d + 1) → ℝ) (n : ℕ) : ℝ :=
  (Real.log (bestConstantWealth xs n) - Real.log (universalWealth xs n)) / (n : ℝ)

theorem simplexLift_mem_stdSimplex {y : Fin d → ℝ} (hy : y ∈ cornerSimplex d) :
    simplexLift y ∈ stdSimplex ℝ (Fin (d + 1)) := by
  refine ⟨fun j ↦ ?_, ?_⟩
  · refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp only [simplexLift, Fin.snoc_last]
      have := hy.2
      linarith
    · simp only [simplexLift, Fin.snoc_castSucc]
      exact hy.1 i
  · rw [Fin.sum_univ_castSucc]
    simp only [simplexLift, Fin.snoc_castSucc, Fin.snoc_last]
    ring

theorem wealthFactor_pos {xs : ℕ → Fin (d + 1) → ℝ} (hpos : ∀ i j, 0 < xs i j)
    {b : Fin (d + 1) → ℝ} (hb : b ∈ stdSimplex ℝ (Fin (d + 1))) (i : ℕ) :
    0 < ∑ j, b j * xs i j := by
  refine Finset.sum_pos' (fun j _ ↦ mul_nonneg (hb.1 j) (hpos i j).le) ?_
  obtain ⟨j, hj⟩ : ∃ j, 0 < b j := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have hle : ∑ j, b j ≤ 0 := Finset.sum_nonpos (fun j _ ↦ h j)
    rw [hb.2] at hle
    linarith
  exact ⟨j, Finset.mem_univ j, mul_pos hj (hpos i j)⟩

theorem constWealth_pos {xs : ℕ → Fin (d + 1) → ℝ} (hpos : ∀ i j, 0 < xs i j)
    {b : Fin (d + 1) → ℝ} (hb : b ∈ stdSimplex ℝ (Fin (d + 1))) (n : ℕ) :
    0 < constWealth xs b n :=
  Finset.prod_pos (fun i _ ↦ wealthFactor_pos hpos hb i)

theorem isCompact_cornerSimplex : IsCompact (cornerSimplex d) := by
  have hclosed : IsClosed (cornerSimplex d) := by
    rw [cornerSimplex, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun i ↦ ?_) ?_
    · exact isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_le (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const
  have hbdd : Bornology.IsBounded (cornerSimplex d) := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin d → ℝ)) (r := 1)).subset ?_
    intro y hy
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hy.1 i)]
    exact (Finset.single_le_sum (fun j _ ↦ hy.1 j) (Finset.mem_univ i)).trans hy.2
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

theorem cornerSimplex_nonempty : (cornerSimplex d).Nonempty :=
  ⟨0, fun _ ↦ le_refl _, by simp⟩

theorem measurableSet_cornerSimplex : MeasurableSet (cornerSimplex d) :=
  isCompact_cornerSimplex.measurableSet

theorem volume_cornerSimplex_pos : 0 < volume (cornerSimplex d) := by
  set U : Set (Fin d → ℝ) := {y | (∀ i, 0 < y i) ∧ ∑ i, y i < 1} with hU
  have hUsub : U ⊆ cornerSimplex d := fun y hy ↦ ⟨fun i ↦ (hy.1 i).le, hy.2.le⟩
  have hUopen : IsOpen U := by
    rw [hU, Set.setOf_and, Set.setOf_forall]
    exact IsOpen.inter
      (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i))
      (isOpen_lt (continuous_finsetSum _ fun i _ ↦ continuous_apply i) continuous_const)
  have hUne : U.Nonempty := by
    refine ⟨fun _ ↦ 1 / (2 * ((d : ℝ) + 1)), fun i ↦ by positivity, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  exact lt_of_lt_of_le (hUopen.measure_pos volume hUne) (measure_mono hUsub)

theorem volume_cornerSimplex_ne_top : volume (cornerSimplex d) ≠ ⊤ :=
  isCompact_cornerSimplex.measure_ne_top

theorem volume_cornerSimplex_toReal_pos : 0 < (volume (cornerSimplex d)).toReal :=
  ENNReal.toReal_pos volume_cornerSimplex_pos.ne' volume_cornerSimplex_ne_top

theorem continuous_liftWealth (xs : ℕ → Fin (d + 1) → ℝ) (n : ℕ) :
    Continuous (fun y : Fin d → ℝ ↦ constWealth xs (simplexLift y) n) := by
  have hlift : Continuous (fun y : Fin d → ℝ ↦ simplexLift y) := by
    refine continuous_pi (fun j ↦ ?_)
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simp only [simplexLift, Fin.snoc_last]
      exact continuous_const.sub (continuous_finsetSum _ fun i _ ↦ continuous_apply i)
    · simp only [simplexLift, Fin.snoc_castSucc]
      exact continuous_apply i
  unfold constWealth
  refine continuous_finsetProd _ (fun i _ ↦ ?_)
  refine continuous_finsetSum _ (fun j _ ↦ ?_)
  exact ((continuous_apply j).comp hlift).mul continuous_const

theorem integrableOn_liftWealth (xs : ℕ → Fin (d + 1) → ℝ) (n : ℕ) :
    IntegrableOn (fun y : Fin d → ℝ ↦ constWealth xs (simplexLift y) n) (cornerSimplex d) :=
  (continuous_liftWealth xs n).continuousOn.integrableOn_compact isCompact_cornerSimplex

theorem simplexLift_init {b : Fin (d + 1) → ℝ} (hb : b ∈ stdSimplex ℝ (Fin (d + 1))) :
    simplexLift (Fin.init b) = b := by
  have hsum : (1 : ℝ) - ∑ i, Fin.init b i = b (Fin.last d) := by
    have hb2 := hb.2
    rw [Fin.sum_univ_castSucc] at hb2
    have hinit : (∑ i, Fin.init b i) = ∑ i : Fin d, b (Fin.castSucc i) := rfl
    rw [hinit]; linarith
  unfold simplexLift
  rw [hsum]
  exact Fin.snoc_init_self b

theorem init_mem_cornerSimplex {b : Fin (d + 1) → ℝ} (hb : b ∈ stdSimplex ℝ (Fin (d + 1))) :
    Fin.init b ∈ cornerSimplex d := by
  refine ⟨fun i ↦ hb.1 i.castSucc, ?_⟩
  have hb2 := hb.2
  rw [Fin.sum_univ_castSucc] at hb2
  have hlast : 0 ≤ b (Fin.last d) := hb.1 _
  have hinit : (∑ i, Fin.init b i) = ∑ i : Fin d, b (Fin.castSucc i) := rfl
  rw [hinit]; linarith

/-- The best constant-rebalanced wealth is attained at a maximizer over the corner simplex,
and dominates the lifted wealth of every corner point. -/
theorem bestConstantWealth_attained (xs : ℕ → Fin (d + 1) → ℝ) (n : ℕ) :
    ∃ y ∈ cornerSimplex d, bestConstantWealth xs n = constWealth xs (simplexLift y) n ∧
      ∀ z ∈ cornerSimplex d, constWealth xs (simplexLift z) n ≤ bestConstantWealth xs n := by
  obtain ⟨ystar, hystar_mem, hystar_max⟩ :=
    isCompact_cornerSimplex.exists_isMaxOn cornerSimplex_nonempty
      (continuous_liftWealth xs n).continuousOn
  have hUB : ∀ b : stdSimplex ℝ (Fin (d + 1)),
      constWealth xs (b : Fin (d + 1) → ℝ) n ≤ constWealth xs (simplexLift ystar) n := by
    intro b
    have hb_eq : (b : Fin (d + 1) → ℝ) = simplexLift (Fin.init (b : Fin (d + 1) → ℝ)) :=
      (simplexLift_init b.2).symm
    rw [hb_eq]
    exact hystar_max (init_mem_cornerSimplex b.2)
  have hbdd : BddAbove (Set.range
      (fun b : stdSimplex ℝ (Fin (d + 1)) ↦ constWealth xs (b : Fin (d + 1) → ℝ) n)) :=
    ⟨_, by rintro _ ⟨b, rfl⟩; exact hUB b⟩
  haveI : Nonempty (stdSimplex ℝ (Fin (d + 1))) :=
    ⟨⟨simplexLift ystar, simplexLift_mem_stdSimplex hystar_mem⟩⟩
  have hBCW : bestConstantWealth xs n = constWealth xs (simplexLift ystar) n :=
    le_antisymm (ciSup_le hUB)
      (le_ciSup hbdd ⟨simplexLift ystar, simplexLift_mem_stdSimplex hystar_mem⟩)
  refine ⟨ystar, hystar_mem, hBCW, fun z hz ↦ ?_⟩
  rw [hBCW]
  exact hystar_max hz

theorem simplexLift_smul_add (lam : ℝ) (y z : Fin d → ℝ) :
    simplexLift ((1 - lam) • y + lam • z)
      = (1 - lam) • simplexLift y + lam • simplexLift z := by
  funext j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp only [simplexLift, Fin.snoc_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  · simp only [simplexLift, Fin.snoc_castSucc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Real inequality behind the shrink constant: `(1 - 1/(n+1)) ^ n ≥ e⁻¹`. -/
theorem exp_neg_one_le_shrink (n : ℕ) :
    Real.exp (-1) ≤ (1 - 1 / ((n : ℝ) + 1)) ^ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, pow_zero]
    calc Real.exp (-1) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := Real.exp_zero
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    -- `(1 + 1/n) ^ n ≤ e`, so its reciprocal `(1 - 1/(n+1)) ^ n ≥ e⁻¹`.
    have hkey : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      have h1 : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / (n : ℝ)) := by
        have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
      calc (1 + 1 / (n : ℝ)) ^ n
          ≤ (Real.exp (1 / (n : ℝ))) ^ n := by
            exact pow_le_pow_left₀ (by positivity) h1 n
        _ = Real.exp ((n : ℝ) * (1 / (n : ℝ))) := (Real.exp_nat_mul _ n).symm
        _ = Real.exp 1 := by rw [mul_one_div, div_self (ne_of_gt hn')]
    have hn1 : (n : ℝ) ≠ 0 := ne_of_gt hn'
    have hbase : (1 - 1 / ((n : ℝ) + 1)) = (1 + 1 / (n : ℝ))⁻¹ := by
      rw [inv_eq_one_div]
      field_simp
      ring
    rw [hbase, inv_pow, Real.exp_neg]
    exact inv_anti₀ (by positivity) hkey

/-- Positivity of the universal wealth: with strictly positive price relatives every
constant-rebalanced wealth is positive, and the uniform average over the
positive-measure corner simplex stays positive.

@audit:ok — sorryAx-free (`[propext, Classical.choice, Quot.sound]`). `hpos` regularity. -/
theorem universalWealth_pos
    (xs : ℕ → Fin (d + 1) → ℝ) (hpos : ∀ i j, 0 < xs i j) (n : ℕ) :
    0 < universalWealth xs n := by
  have hnn : 0 ≤ᵐ[volume.restrict (cornerSimplex d)]
      fun y ↦ constWealth xs (simplexLift y) n :=
    (ae_restrict_iff' measurableSet_cornerSimplex).mpr
      (Eventually.of_forall fun y hy ↦
        (constWealth_pos hpos (simplexLift_mem_stdSimplex hy) n).le)
  have hsupp : Function.support (fun y ↦ constWealth xs (simplexLift y) n) ∩ cornerSimplex d
      = cornerSimplex d :=
    Set.inter_eq_right.mpr fun y hy ↦
      ne_of_gt (constWealth_pos hpos (simplexLift_mem_stdSimplex hy) n)
  unfold universalWealth
  refine div_pos ?_ volume_cornerSimplex_toReal_pos
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn (integrableOn_liftWealth xs n), hsupp]
  exact volume_cornerSimplex_pos

/-- The universal wealth never exceeds the best constant-rebalanced wealth: `Ŝ_n` is a
uniform average of values `constWealth xs (simplexLift y) n ≤ S*_n`.

@audit:ok — sorryAx-free (`[propext, Classical.choice, Quot.sound]`). `_hpos` is unused
(dominance holds without positivity); underscored to keep the uniform core interface. -/
theorem universalWealth_le_bestConstantWealth
    (xs : ℕ → Fin (d + 1) → ℝ) (_hpos : ∀ i j, 0 < xs i j) (n : ℕ) :
    universalWealth xs n ≤ bestConstantWealth xs n := by
  obtain ⟨ystar, hystar_mem, hBCW, hmax⟩ := bestConstantWealth_attained xs n
  have hconst : IntegrableOn (fun _ : Fin d → ℝ ↦ bestConstantWealth xs n) (cornerSimplex d) :=
    integrableOn_const volume_cornerSimplex_ne_top
  unfold universalWealth
  rw [div_le_iff₀ volume_cornerSimplex_toReal_pos]
  calc ∫ y in cornerSimplex d, constWealth xs (simplexLift y) n
      ≤ ∫ _ in cornerSimplex d, bestConstantWealth xs n :=
        setIntegral_mono_on (integrableOn_liftWealth xs n) hconst measurableSet_cornerSimplex
          fun y hy ↦ hmax y hy
    _ = bestConstantWealth xs n * (volume (cornerSimplex d)).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl

/-- Cover's shrink bound: the best constant-rebalanced wealth exceeds the universal
wealth by at most a factor `e · (n + 1) ^ d`. The homothety
`b ↦ (1 − 1/(n+1)) b* + (1/(n+1)) b` scales simplex volume by `(n + 1)⁻ᵈ`
(`MeasureTheory.Measure.addHaar_image_homothety`) and keeps the wealth within
`(1 − 1/(n+1)) ^ n ≥ e⁻¹` of the optimum.

@audit:ok — sorryAx-free (`[propext, Classical.choice, Quot.sound]`). `hpos` regularity;
the shrink bound is genuine (homothety volume scaling + setIntegral monotonicity). -/
theorem bestConstantWealth_le_mul_universalWealth
    (xs : ℕ → Fin (d + 1) → ℝ) (hpos : ∀ i j, 0 < xs i j) (n : ℕ) :
    bestConstantWealth xs n ≤ Real.exp 1 * ((n : ℝ) + 1) ^ d * universalWealth xs n := by
  set lam : ℝ := 1 / ((n : ℝ) + 1) with hlam
  have hlam_pos : 0 < lam := by rw [hlam]; positivity
  have hlam_le : lam ≤ 1 := by
    rw [hlam, div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨ystar, hystar_mem, hBCW, hmax⟩ := bestConstantWealth_attained xs n
  -- The homothety centered at `ystar` with ratio `lam`, as an affine combination.
  have hhom : ∀ y : Fin d → ℝ,
      AffineMap.homothety ystar lam y = (1 - lam) • ystar + lam • y := by
    intro y
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
    abel
  set img := AffineMap.homothety ystar lam '' cornerSimplex d with himg
  -- The image stays inside the corner simplex (convexity).
  have himg_sub : img ⊆ cornerSimplex d := by
    rw [himg]
    rintro _ ⟨y, hy, rfl⟩
    rw [hhom y]
    refine ⟨fun i ↦ ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg (by linarith) (hystar_mem.1 i))
        (mul_nonneg hlam_pos.le (hy.1 i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - lam by linarith) (sub_nonneg.mpr hystar_mem.2),
        mul_nonneg hlam_pos.le (sub_nonneg.mpr hy.2)]
  -- The image is compact, hence measurable and of finite measure.
  have hcpt_img : IsCompact img :=
    isCompact_cornerSimplex.image
      (AffineMap.homothety ystar lam).continuous_of_finiteDimensional
  -- Its Lebesgue measure scales by `lam ^ d`.
  have hvol_eq : volume img = ENNReal.ofReal (lam ^ d) * volume (cornerSimplex d) := by
    rw [himg, Measure.addHaar_image_homothety, Module.finrank_fin_fun,
      abs_of_nonneg (pow_nonneg hlam_pos.le d)]
  have hvol : (volume img).toReal = lam ^ d * (volume (cornerSimplex d)).toReal := by
    rw [hvol_eq, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hlam_pos.le d)]
  -- On the image, each lifted wealth stays within `(1 - lam) ^ n` of the optimum `S*_n`.
  have hfac : ∀ y' ∈ img, (1 - lam) ^ n * bestConstantWealth xs n
      ≤ constWealth xs (simplexLift y') n := by
    intro y' hy'
    rw [himg] at hy'
    obtain ⟨y, hy, rfl⟩ := hy'
    rw [hhom y, simplexLift_smul_add, hBCW]
    have hbstar_mem := simplexLift_mem_stdSimplex hystar_mem
    have hbby_mem := simplexLift_mem_stdSimplex hy
    have hfactor : ∀ i, (1 - lam) * (∑ j, simplexLift ystar j * xs i j)
        ≤ ∑ j, ((1 - lam) • simplexLift ystar + lam • simplexLift y) j * xs i j := by
      intro i
      have hsplit : ∑ j, ((1 - lam) • simplexLift ystar + lam • simplexLift y) j * xs i j
          = (1 - lam) * (∑ j, simplexLift ystar j * xs i j)
            + lam * (∑ j, simplexLift y j * xs i j) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hsplit]
      have hnn : 0 ≤ lam * (∑ j, simplexLift y j * xs i j) :=
        mul_nonneg hlam_pos.le
          (Finset.sum_nonneg fun j _ ↦ mul_nonneg (hbby_mem.1 j) (hpos i j).le)
      linarith
    calc (1 - lam) ^ n * constWealth xs (simplexLift ystar) n
        = ∏ i ∈ Finset.range n, (1 - lam) * (∑ j, simplexLift ystar j * xs i j) := by
          unfold constWealth
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range n,
            (∑ j, ((1 - lam) • simplexLift ystar + lam • simplexLift y) j * xs i j) := by
          refine Finset.prod_le_prod (fun i _ ↦ ?_) (fun i _ ↦ hfactor i)
          exact mul_nonneg (by linarith) (wealthFactor_pos hpos hbstar_mem i).le
      _ = constWealth xs ((1 - lam) • simplexLift ystar + lam • simplexLift y) n := rfl
  -- Integrating the pointwise bound over the image, then enlarging to the corner simplex.
  have hg_nonneg : 0 ≤ᵐ[volume.restrict (cornerSimplex d)]
      fun y ↦ constWealth xs (simplexLift y) n :=
    (ae_restrict_iff' measurableSet_cornerSimplex).mpr
      (Eventually.of_forall fun y hy ↦
        (constWealth_pos hpos (simplexLift_mem_stdSimplex hy) n).le)
  have hint_img : IntegrableOn (fun y ↦ constWealth xs (simplexLift y) n) img :=
    (integrableOn_liftWealth xs n).mono_set himg_sub
  have hconst_img : IntegrableOn
      (fun _ : Fin d → ℝ ↦ (1 - lam) ^ n * bestConstantWealth xs n) img :=
    integrableOn_const hcpt_img.measure_ne_top
  have hlow : (volume img).toReal * ((1 - lam) ^ n * bestConstantWealth xs n)
      ≤ ∫ y in cornerSimplex d, constWealth xs (simplexLift y) n := by
    calc (volume img).toReal * ((1 - lam) ^ n * bestConstantWealth xs n)
        = ∫ _ in img, (1 - lam) ^ n * bestConstantWealth xs n := by
          rw [setIntegral_const, smul_eq_mul]; rfl
      _ ≤ ∫ y in img, constWealth xs (simplexLift y) n :=
          setIntegral_mono_on hconst_img hint_img hcpt_img.measurableSet hfac
      _ ≤ ∫ y in cornerSimplex d, constWealth xs (simplexLift y) n :=
          setIntegral_mono_set (integrableOn_liftWealth xs n) hg_nonneg
            (Eventually.of_forall fun x hx ↦ himg_sub hx)
  -- Rewrite the corner integral through the definition of the universal wealth.
  have hInt_eq : ∫ y in cornerSimplex d, constWealth xs (simplexLift y) n
      = universalWealth xs n * (volume (cornerSimplex d)).toReal := by
    unfold universalWealth
    rw [div_mul_cancel₀ _ (ne_of_gt volume_cornerSimplex_toReal_pos)]
  -- Cancel the (positive) simplex volume to isolate the wealth inequality.
  have hkey : lam ^ d * (1 - lam) ^ n * bestConstantWealth xs n ≤ universalWealth xs n := by
    have h' : (lam ^ d * (1 - lam) ^ n * bestConstantWealth xs n)
        * (volume (cornerSimplex d)).toReal
        ≤ universalWealth xs n * (volume (cornerSimplex d)).toReal := by
      have hcombine : lam ^ d * (volume (cornerSimplex d)).toReal
          * ((1 - lam) ^ n * bestConstantWealth xs n)
          ≤ universalWealth xs n * (volume (cornerSimplex d)).toReal := by
        rw [← hvol, ← hInt_eq]; exact hlow
      calc (lam ^ d * (1 - lam) ^ n * bestConstantWealth xs n)
            * (volume (cornerSimplex d)).toReal
          = lam ^ d * (volume (cornerSimplex d)).toReal
            * ((1 - lam) ^ n * bestConstantWealth xs n) := by ring
        _ ≤ universalWealth xs n * (volume (cornerSimplex d)).toReal := hcombine
    exact le_of_mul_le_mul_right h' volume_cornerSimplex_toReal_pos
  -- Fold in the shrink constant `e · (n + 1) ^ d`.
  have hbcw_nonneg : 0 ≤ bestConstantWealth xs n := by
    rw [hBCW]; exact (constWealth_pos hpos (simplexLift_mem_stdSimplex hystar_mem) n).le
  have hexp1 : (1 : ℝ) ≤ Real.exp 1 * (1 - lam) ^ n := by
    have h1 : Real.exp (-1) ≤ (1 - lam) ^ n := by rw [hlam]; exact exp_neg_one_le_shrink n
    have h2 : Real.exp 1 * Real.exp (-1) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos 1, h1, h2]
  have hlamd : lam ^ d * ((n : ℝ) + 1) ^ d = 1 := by
    rw [hlam, div_pow, one_pow, one_div, inv_mul_cancel₀ (by positivity)]
  have hLHS : Real.exp 1 * ((n : ℝ) + 1) ^ d
        * (lam ^ d * (1 - lam) ^ n * bestConstantWealth xs n)
      = Real.exp 1 * (1 - lam) ^ n * bestConstantWealth xs n := by
    linear_combination (Real.exp 1 * (1 - lam) ^ n * bestConstantWealth xs n) * hlamd
  calc bestConstantWealth xs n
      ≤ Real.exp 1 * (1 - lam) ^ n * bestConstantWealth xs n := by
        nlinarith [hexp1, hbcw_nonneg]
    _ = Real.exp 1 * ((n : ℝ) + 1) ^ d
          * (lam ^ d * (1 - lam) ^ n * bestConstantWealth xs n) := hLHS.symm
    _ ≤ Real.exp 1 * ((n : ℝ) + 1) ^ d * universalWealth xs n :=
        mul_le_mul_of_nonneg_left hkey (by positivity)

/-- Theorem 16.7.1 (Cover–Thomas): the per-period regret of the universal portfolio
relative to the best constant-rebalanced portfolio chosen in hindsight tends to `0`.

@audit:ok — sorryAx-free (`[propext, Classical.choice, Quot.sound]`). `hpos` (positive
price relatives) is a regularity precondition; the squeeze is proven from the three
analytic cores, none bundled into a hypothesis. -/
@[entry_point]
theorem universal_portfolio_regret_tendsto_zero
    (xs : ℕ → Fin (d + 1) → ℝ) (hpos : ∀ i j, 0 < xs i j) :
    Tendsto (fun n ↦ universalRegret xs n) atTop (𝓝 0) := by
  -- The three analytic facts about the universal wealth.
  have hU_pos : ∀ n, 0 < universalWealth xs n := fun n ↦ universalWealth_pos xs hpos n
  have hUS : ∀ n, universalWealth xs n ≤ bestConstantWealth xs n :=
    fun n ↦ universalWealth_le_bestConstantWealth xs hpos n
  have hshrink : ∀ n, bestConstantWealth xs n
      ≤ Real.exp 1 * ((n : ℝ) + 1) ^ d * universalWealth xs n :=
    fun n ↦ bestConstantWealth_le_mul_universalWealth xs hpos n
  have hS_pos : ∀ n, 0 < bestConstantWealth xs n := fun n ↦ lt_of_lt_of_le (hU_pos n) (hUS n)
  -- Lower bound: the regret is nonnegative because `Ŝ_n ≤ S*_n`.
  have hlow : ∀ n, 0 ≤ universalRegret xs n := by
    intro n
    refine div_nonneg ?_ (Nat.cast_nonneg n)
    have := Real.log_le_log (hU_pos n) (hUS n)
    linarith
  -- Upper bound: the regret is at most `(1 + d · log (n + 1)) / n` (for `n ≥ 1`).
  have hup : ∀ n, 1 ≤ n →
      universalRegret xs n ≤ (1 + (d : ℝ) * Real.log ((n : ℝ) + 1)) / (n : ℝ) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpospow : (0 : ℝ) < ((n : ℝ) + 1) ^ d := by positivity
    have hlogS : Real.log (bestConstantWealth xs n)
        ≤ 1 + (d : ℝ) * Real.log ((n : ℝ) + 1) + Real.log (universalWealth xs n) := by
      have h1 := Real.log_le_log (hS_pos n) (hshrink n)
      rw [Real.log_mul (by positivity) (hU_pos n).ne',
          Real.log_mul (Real.exp_pos 1).ne' hpospow.ne',
          Real.log_exp, Real.log_pow] at h1
      linarith
    have hnum : Real.log (bestConstantWealth xs n) - Real.log (universalWealth xs n)
        ≤ 1 + (d : ℝ) * Real.log ((n : ℝ) + 1) := by linarith
    exact (div_le_div_iff_of_pos_right hnpos).mpr hnum
  -- The upper bounding sequence tends to `0`.
  have hg_lim : Tendsto (fun n : ℕ ↦ (1 + (d : ℝ) * Real.log ((n : ℝ) + 1)) / (n : ℝ))
      atTop (𝓝 0) := by
    have h1n : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hlogx : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hn1 : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hlog2 : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1))
        atTop (𝓝 0) := hlogx.comp hn1
    have hratio : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).add h1n
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have hlogn : Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) := by
      have hprod := hlog2.mul hratio
      rw [zero_mul] at hprod
      refine hprod.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hne1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have hsum := h1n.add (hlogn.const_mul (d : ℝ))
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  -- Squeeze the regret between `0` and the vanishing upper bound.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg_lim
    (Eventually.of_forall hlow) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn using hup n hn

end InformationTheory.Shannon.Portfolio
