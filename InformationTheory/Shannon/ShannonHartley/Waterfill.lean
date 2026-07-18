import InformationTheory.Shannon.ShannonHartley.Main

/-!
# Water-filling arithmetic for the Shannon-Hartley converse

Pure real-analysis lemmas supporting the continuous-time Shannon-Hartley converse. They are
independent of any Gaussian / measure-theoretic / rotation machinery: everything here is
elementary calculus on `ℝ` plus finite-sum concavity (Jensen).

* `mul_log_one_add_div_monotone` — the map `x ↦ x · log(1 + a/x)` is monotone on `(0, ∞)` for
  `a ≥ 0` (the per-slot capacity is increasing in the number of degrees of freedom).
* `waterfill_head_tail_bound` — the fixed-`T` water-filling split: the total per-slot log-capacity
  is bounded by a tail contribution `c₀·TP/N₀` plus a head contribution
  `B · ½ log(1 + TP/(B·N₀/2))`, where `B` dominates the count of "loud" slots.
* `waterfill_head_div_tendsto` — dividing the head contribution by `T` and letting `T → ∞`
  converges to the Shannon-Hartley capacity `bandlimitedAwgnCapacity W N₀ P`.
-/

namespace InformationTheory.Shannon.ShannonHartley

open Filter
open scoped Topology
open InformationTheory.Shannon.TimeBandLimiting

set_option linter.unusedVariables false

/-- Elementary lower bound `u/(1+u) ≤ log(1+u)` for `u ≥ 0`. -/
private lemma div_one_add_le_log_one_add {u : ℝ} (hu : 0 ≤ u) :
    u / (1 + u) ≤ Real.log (1 + u) := by
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have hy : (0 : ℝ) < (1 + u)⁻¹ := by positivity
  have hlog := Real.log_le_sub_one_of_pos hy
  rw [Real.log_inv] at hlog
  have key : u / (1 + u) = 1 - (1 + u)⁻¹ := by field_simp; ring
  rw [key]
  linarith [hlog]

/-- The per-slot capacity `x ↦ x · log(1 + a/x)` is monotone in the number of degrees of freedom
`x` on `(0, ∞)` for `a ≥ 0`. -/
lemma mul_log_one_add_div_monotone {a : ℝ} (ha : 0 ≤ a) :
    MonotoneOn (fun x : ℝ => x * Real.log (1 + a / x)) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun x : ℝ => x * Real.log (1 + a / x)) (Set.Ioi 0) := by
    apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.log
    · exact continuousOn_const.add
        (continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt hx))
    · intro x hx
      have hx0 : 0 < x := hx
      have hu : 0 ≤ a / x := div_nonneg ha hx0.le
      exact ne_of_gt (by linarith)
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun x => Real.log (1 + a / x) - a / x / (1 + a / x)) (convex_Ioi 0) hcont
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hu0 : 0 ≤ a / x := div_nonneg ha hx0.le
    have hpos : (0 : ℝ) < 1 + a / x := by linarith
    have hposne : (1 + a / x) ≠ 0 := ne_of_gt hpos
    have hax : HasDerivAt (fun y : ℝ => a / y) ((0 * x - a * 1) / x ^ 2) x :=
      (hasDerivAt_const x a).div (hasDerivAt_id x) hxne
    have hinner : HasDerivAt (fun y : ℝ => 1 + a / y) ((0 * x - a * 1) / x ^ 2) x :=
      hax.const_add 1
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + a / y))
        ((0 * x - a * 1) / x ^ 2 / (1 + a / x)) x :=
      hinner.log hposne
    have hprod : HasDerivAt (fun y : ℝ => y * Real.log (1 + a / y))
        (1 * Real.log (1 + a / x) + x * ((0 * x - a * 1) / x ^ 2 / (1 + a / x))) x :=
      (hasDerivAt_id x).mul hlog
    have hval : 1 * Real.log (1 + a / x) + x * ((0 * x - a * 1) / x ^ 2 / (1 + a / x))
        = Real.log (1 + a / x) - a / x / (1 + a / x) := by
      field_simp
      ring
    rw [hval] at hprod
    exact hprod.hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 : 0 < x := hx
    have hu : 0 ≤ a / x := div_nonneg ha hx0.le
    have := div_one_add_le_log_one_add hu
    linarith

/-- Concavity of `x ↦ ½ log(1 + x/(N₀/2))` on `[0, ∞)`. -/
private lemma concaveOn_half_log_one_add_div {N₀ : ℝ} (hN₀ : 0 < N₀) :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => (1 / 2) * Real.log (1 + x / (N₀ / 2))) := by
  have hN2 : (0 : ℝ) < N₀ / 2 := by linarith
  set A : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ 1 + ((N₀ / 2)⁻¹ • LinearMap.id).toAffineMap with hA
  have hAeq : ∀ x : ℝ, A x = 1 + x / (N₀ / 2) := by
    intro x
    simp only [hA, AffineMap.coe_add, Pi.add_apply, AffineMap.const_apply,
      LinearMap.coe_toAffineMap, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring
  have hlogconc : ConcaveOn ℝ (Set.Ioi 0) Real.log := strictConcaveOn_log_Ioi.concaveOn
  have hcomp : ConcaveOn ℝ (A ⁻¹' Set.Ioi 0) (Real.log ∘ A) := hlogconc.comp_affineMap A
  have hsub : Set.Ici 0 ⊆ A ⁻¹' Set.Ioi 0 := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_Ioi, hAeq]
    have : 0 ≤ x / (N₀ / 2) := div_nonneg hx hN2.le
    linarith
  have hconc2 : ConcaveOn ℝ (Set.Ici 0) (Real.log ∘ A) := hcomp.subset hsub (convex_Ici 0)
  have hfun : (Real.log ∘ A) = fun x => Real.log (1 + x / (N₀ / 2)) := by
    funext x; simp only [Function.comp_apply, hAeq]
  rw [hfun] at hconc2
  have hscaled := hconc2.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  simpa only [smul_eq_mul] using hscaled

/-- The fixed-`T` water-filling head/tail split. Splitting the slots into "loud" ones
(`c₀ < νᵢ`, at most `B` of them by the count hypothesis) and "quiet" ones, the total per-slot
log-capacity is bounded by a tail term `c₀·TP/N₀` (linearization `log(1+x) ≤ x` on the quiet slots)
plus a head term `B · ½ log(1 + TP/(B·N₀/2))` (Jensen + monotonicity on the loud slots). -/
lemma waterfill_head_tail_bound {k : ℕ} (N₀ TP c₀ : ℝ) (hN₀ : 0 < N₀) (hTP : 0 ≤ TP)
    (hc₀ : 0 < c₀) (ν Q P' : Fin k → ℝ)
    (hP'0 : ∀ i, 0 ≤ P' i) (hP'ν : ∀ i, P' i ≤ ν i * Q i)
    (hQ0 : ∀ i, 0 ≤ Q i) (hQsum : ∑ i, Q i ≤ TP)
    (hν0 : ∀ i, 0 ≤ ν i) (hν1 : ∀ i, ν i ≤ 1)
    {B : ℕ} (hcount : (Finset.univ.filter (fun i => c₀ < ν i)).card ≤ B) :
    ∑ i, (1 / 2) * Real.log (1 + P' i / (N₀ / 2))
      ≤ c₀ * TP / N₀
        + (B : ℝ) * ((1 / 2) * Real.log (1 + TP / ((B : ℝ) * (N₀ / 2)))) := by
  classical
  have hN2 : (0 : ℝ) < N₀ / 2 := by linarith
  have hN0ne : N₀ ≠ 0 := hN₀.ne'
  -- the per-slot capacity is monotone on `[0, ∞)`
  have hg_mono : ∀ z w : ℝ, 0 ≤ z → z ≤ w →
      (1 / 2) * Real.log (1 + z / (N₀ / 2)) ≤ (1 / 2) * Real.log (1 + w / (N₀ / 2)) := by
    intro z w hz hzw
    have h1 : (0 : ℝ) < 1 + z / (N₀ / 2) := by have := div_nonneg hz hN2.le; linarith
    have h2 : 1 + z / (N₀ / 2) ≤ 1 + w / (N₀ / 2) := by
      have : z / (N₀ / 2) ≤ w / (N₀ / 2) := by gcongr
      linarith
    have h3 := Real.log_le_log h1 h2
    linarith [mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  -- the per-slot capacity is nonnegative on `[0, ∞)`
  have hg_nonneg : ∀ z : ℝ, 0 ≤ z → 0 ≤ (1 / 2) * Real.log (1 + z / (N₀ / 2)) := by
    intro z hz
    have hzz : (0 : ℝ) ≤ z / (N₀ / 2) := div_nonneg hz hN2.le
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + z / (N₀ / 2) by linarith)
    linarith
  set headS := Finset.univ.filter (fun i => c₀ < ν i) with hheadS
  -- split the total sum into "loud" (head) and "quiet" (tail) slots
  have hsplit :
      ∑ i, (1 / 2) * Real.log (1 + P' i / (N₀ / 2))
        = (∑ i ∈ headS, (1 / 2) * Real.log (1 + P' i / (N₀ / 2)))
          + ∑ i ∈ Finset.univ.filter (fun i => ¬ c₀ < ν i),
              (1 / 2) * Real.log (1 + P' i / (N₀ / 2)) := by
    rw [hheadS, Finset.sum_filter_add_sum_filter_not]
  -- TAIL: linearize `log(1+x) ≤ x` and use `νᵢ ≤ c₀`
  have htail :
      ∑ i ∈ Finset.univ.filter (fun i => ¬ c₀ < ν i),
          (1 / 2) * Real.log (1 + P' i / (N₀ / 2))
        ≤ c₀ * TP / N₀ := by
    have hbound : ∀ i ∈ Finset.univ.filter (fun i => ¬ c₀ < ν i),
        (1 / 2) * Real.log (1 + P' i / (N₀ / 2)) ≤ c₀ * Q i / N₀ := by
      intro i hi
      have hνc : ν i ≤ c₀ := not_lt.mp (Finset.mem_filter.mp hi).2
      have hpos : (0 : ℝ) < 1 + P' i / (N₀ / 2) := by
        have := div_nonneg (hP'0 i) hN2.le; linarith
      have hlog := Real.log_le_sub_one_of_pos hpos
      have hP'c : P' i ≤ c₀ * Q i := (hP'ν i).trans (mul_le_mul_of_nonneg_right hνc (hQ0 i))
      have h1a : (1 / 2) * Real.log (1 + P' i / (N₀ / 2)) ≤ (1 / 2) * (P' i / (N₀ / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith [hlog]) (by norm_num)
      have h1b : (1 / 2) * (P' i / (N₀ / 2)) = P' i / N₀ := by field_simp
      rw [h1b] at h1a
      have h3 : P' i / N₀ ≤ c₀ * Q i / N₀ := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hP'c (by positivity)
      linarith
    calc ∑ i ∈ Finset.univ.filter (fun i => ¬ c₀ < ν i),
            (1 / 2) * Real.log (1 + P' i / (N₀ / 2))
          ≤ ∑ i ∈ Finset.univ.filter (fun i => ¬ c₀ < ν i), c₀ * Q i / N₀ :=
            Finset.sum_le_sum hbound
      _ = (c₀ / N₀) * ∑ i ∈ Finset.univ.filter (fun i => ¬ c₀ < ν i), Q i := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ (c₀ / N₀) * TP := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun i _ _ => hQ0 i)) hQsum
      _ = c₀ * TP / N₀ := by ring
  -- HEAD: Jensen + monotonicity in the number of loud slots
  have hhead :
      ∑ i ∈ headS, (1 / 2) * Real.log (1 + P' i / (N₀ / 2))
        ≤ (B : ℝ) * ((1 / 2) * Real.log (1 + TP / ((B : ℝ) * (N₀ / 2)))) := by
    rw [show TP / ((B : ℝ) * (N₀ / 2)) = (B : ℝ)⁻¹ * TP / (N₀ / 2) from by ring]
    have hbridge : ∀ x : ℝ,
        x * ((1 / 2) * Real.log (1 + x⁻¹ * TP / (N₀ / 2)))
          = (1 / 2) * (x * Real.log (1 + TP / (N₀ / 2) / x)) := by
      intro x
      rw [show x⁻¹ * TP / (N₀ / 2) = TP / (N₀ / 2) / x from by ring]
      ring
    rcases Nat.eq_zero_or_pos headS.card with hK0 | hKpos
    · -- empty head: LHS is `0`, RHS is nonnegative
      have hempty : headS = ∅ := Finset.card_eq_zero.mp hK0
      rw [hempty, Finset.sum_empty]
      exact mul_nonneg (Nat.cast_nonneg B)
        (hg_nonneg ((B : ℝ)⁻¹ * TP) (mul_nonneg (by positivity) hTP))
    · have hcardR : (0 : ℝ) < (headS.card : ℝ) := Nat.cast_pos.mpr hKpos
      have hcard_ne : (headS.card : ℝ) ≠ 0 := ne_of_gt hcardR
      have hcardB : (headS.card : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hcount
      have hBpos : (0 : ℝ) < (B : ℝ) := lt_of_lt_of_le hcardR hcardB
      have hSqTP : ∑ i ∈ headS, Q i ≤ TP :=
        le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => hQ0 i)) hQsum
      have hSqnn : (0 : ℝ) ≤ ∑ i ∈ headS, Q i := Finset.sum_nonneg (fun i _ => hQ0 i)
      -- Step 1: `P'ᵢ ≤ Qᵢ`, so the head log-sum grows
      have hstep1 :
          ∑ i ∈ headS, (1 / 2) * Real.log (1 + P' i / (N₀ / 2))
            ≤ ∑ i ∈ headS, (1 / 2) * Real.log (1 + Q i / (N₀ / 2)) := by
        apply Finset.sum_le_sum
        intro i _
        exact hg_mono (P' i) (Q i) (hP'0 i)
          ((hP'ν i).trans (by nlinarith [hν1 i, hQ0 i]))
      -- Jensen with uniform weights `1/card`
      have hconc := concaveOn_half_log_one_add_div (N₀ := N₀) hN₀
      have hsum_w : ∑ _i ∈ headS, ((headS.card : ℝ)⁻¹) = 1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcard_ne]
      have hjen := hconc.le_map_sum (t := headS) (w := fun _ => (headS.card : ℝ)⁻¹) (p := Q)
        (fun i _ => by positivity) hsum_w (fun i _ => Set.mem_Ici.mpr (hQ0 i))
      rw [← Finset.smul_sum, ← Finset.smul_sum] at hjen
      simp only [smul_eq_mul] at hjen
      have hSf :
          ∑ i ∈ headS, (1 / 2) * Real.log (1 + Q i / (N₀ / 2))
            ≤ (headS.card : ℝ)
                * ((1 / 2)
                  * Real.log (1 + (headS.card : ℝ)⁻¹ * (∑ i ∈ headS, Q i) / (N₀ / 2))) := by
        have hmul := mul_le_mul_of_nonneg_left hjen hcardR.le
        rwa [← mul_assoc, mul_inv_cancel₀ hcard_ne, one_mul] at hmul
      -- Step 5: `∑ headS Q ≤ TP`
      have hstep5 :
          (headS.card : ℝ)
              * ((1 / 2) * Real.log (1 + (headS.card : ℝ)⁻¹ * (∑ i ∈ headS, Q i) / (N₀ / 2)))
            ≤ (headS.card : ℝ)
                * ((1 / 2) * Real.log (1 + (headS.card : ℝ)⁻¹ * TP / (N₀ / 2))) := by
        apply mul_le_mul_of_nonneg_left _ hcardR.le
        apply hg_mono
        · exact mul_nonneg (by positivity) hSqnn
        · exact mul_le_mul_of_nonneg_left hSqTP (by positivity)
      -- Step 6: monotonicity in the count (`card ≤ B`) via Lemma 1
      have hmono := mul_log_one_add_div_monotone (a := TP / (N₀ / 2)) (div_nonneg hTP hN2.le)
      have hL : (headS.card : ℝ) * Real.log (1 + TP / (N₀ / 2) / (headS.card : ℝ))
            ≤ (B : ℝ) * Real.log (1 + TP / (N₀ / 2) / (B : ℝ)) :=
        hmono (Set.mem_Ioi.mpr hcardR) (Set.mem_Ioi.mpr hBpos) hcardB
      calc ∑ i ∈ headS, (1 / 2) * Real.log (1 + P' i / (N₀ / 2))
            ≤ ∑ i ∈ headS, (1 / 2) * Real.log (1 + Q i / (N₀ / 2)) := hstep1
        _ ≤ (headS.card : ℝ)
              * ((1 / 2) * Real.log (1 + (headS.card : ℝ)⁻¹ * (∑ i ∈ headS, Q i) / (N₀ / 2))) := hSf
        _ ≤ (headS.card : ℝ)
              * ((1 / 2) * Real.log (1 + (headS.card : ℝ)⁻¹ * TP / (N₀ / 2))) := hstep5
        _ = (1 / 2) * ((headS.card : ℝ) * Real.log (1 + TP / (N₀ / 2) / (headS.card : ℝ))) :=
              hbridge (headS.card : ℝ)
        _ ≤ (1 / 2) * ((B : ℝ) * Real.log (1 + TP / (N₀ / 2) / (B : ℝ))) :=
              mul_le_mul_of_nonneg_left hL (by norm_num)
        _ = (B : ℝ) * ((1 / 2) * Real.log (1 + (B : ℝ)⁻¹ * TP / (N₀ / 2))) := (hbridge (B : ℝ)).symm
  rw [hsplit]
  linarith [hhead, htail]

/-- The head water-filling contribution, divided by `T`, converges to the Shannon-Hartley
capacity as `T → ∞`: `prolateCount T W c₀ / T → 2W`, and the continuous scaling function
`y ↦ y · ½ log(1 + P/(y·N₀/2))` evaluated at `2W` equals `bandlimitedAwgnCapacity W N₀ P`. -/
lemma waterfill_head_div_tendsto (W N₀ P c₀ : ℝ) (hW : 0 < W) (hN₀ : 0 < N₀)
    (hP : 0 ≤ P) (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1) :
    Filter.Tendsto (fun T : ℝ => ((prolateCount T W c₀ : ℝ)
        * ((1 / 2) * Real.log (1 + T * P / ((prolateCount T W c₀ : ℝ) * (N₀ / 2))))) / T)
      Filter.atTop (nhds (bandlimitedAwgnCapacity W N₀ P)) := by
  have hr : Tendsto (fun T : ℝ => (prolateCount T W c₀ : ℝ) / T) atTop (𝓝 (2 * W)) :=
    prolateCount_div_tendsto W hW hc₀0 hc₀1
  have h2W : (0 : ℝ) < 2 * W := by linarith
  have hN2 : (0 : ℝ) < N₀ / 2 := by linarith
  have hd : (0 : ℝ) < 2 * W * (N₀ / 2) := mul_pos h2W hN2
  -- continuity of the scaling function `y ↦ y · ½ log(1 + P/(y·N₀/2))` at `2W`
  have hgcont : ContinuousAt
      (fun y : ℝ => y * ((1 / 2) * Real.log (1 + P / (y * (N₀ / 2))))) (2 * W) := by
    apply ContinuousAt.mul continuousAt_id
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.log
    · exact continuousAt_const.add
        (continuousAt_const.div (continuousAt_id.mul continuousAt_const) (ne_of_gt hd))
    · have : (0 : ℝ) ≤ P / (2 * W * (N₀ / 2)) := div_nonneg hP hd.le
      exact ne_of_gt (by linarith)
  -- value at `2W` equals the Shannon-Hartley capacity
  have hgval : 2 * W * (1 / 2 * Real.log (1 + P / (2 * W * (N₀ / 2))))
      = bandlimitedAwgnCapacity W N₀ P := by
    have he : 2 * W * (N₀ / 2) = N₀ * W := by ring
    rw [bandlimitedAwgnCapacity, he]
    ring
  have htend := (hgcont.tendsto).comp hr
  rw [hgval] at htend
  refine htend.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hTne : T ≠ 0 := ne_of_gt hT
  have hN2ne : (N₀ / 2) ≠ 0 := ne_of_gt hN2
  have harg : 1 + P / ((prolateCount T W c₀ : ℝ) / T * (N₀ / 2))
      = 1 + T * P / ((prolateCount T W c₀ : ℝ) * (N₀ / 2)) := by
    rcases eq_or_ne (prolateCount T W c₀ : ℝ) 0 with hc | hc
    · rw [hc]; simp
    · field_simp
  simp only [Function.comp_apply]
  rw [harg]
  ring

end InformationTheory.Shannon.ShannonHartley
