import InformationTheory.Shannon.MultipleAccess.TimeSharing
import Mathlib.Analysis.Convex.Combination

/-!
# Multiple access channel — time-sharing converse (convex-geometry gateway)

The pure convex-geometry core of the two-user MAC time-sharing converse.  An achievable rate
pair `(R₁, R₂)` bounded, coordinate-wise, by the time averages of a family of per-letter
pentagons lies in the convex hull of the union of those pentagons.

This file currently provides only the geometric gateway lemma
`mac_avgPentagon_mem_convexHull`; the measure-theoretic gaps (code→ambient bridge, weak-converse
limit extraction, per-letter identification) are handled elsewhere.

## Note on hypotheses

The gateway lemma requires **both** `a i ≤ c i` and `b i ≤ c i`.  These are the two single-user
mutual-information bounds `I(X₁;Y|X₂) ≤ I(X₁,X₂;Y)` and `I(X₂;Y|X₁) ≤ I(X₁,X₂;Y)` in the MAC
application.  Without `b i ≤ c i` the statement is false: with `n = 2`, `a = (0,4)`, `b = (4,0)`,
`c = (0,4)`, the point `(0,2)` satisfies every remaining hypothesis yet the union of pentagons
collapses onto the `x`-axis, so `(0,2)` is not in the hull.
-/

namespace InformationTheory.Shannon.MAC

open scoped BigOperators

/-- If the `positive-quadrant` set `s` is down-closed (any point coordinate-wise below a point of
`s` is again in `s`) then its convex hull is down-closed as well: a nonnegative point dominated by
a hull point is itself a hull point.  Proved constructively by globally scaling each vertex of a
representing convex combination by the coordinate ratios `p.1 / q.1`, `p.2 / q.2`. -/
private lemma convexHull_mem_of_le {s : Set (ℝ × ℝ)}
    (hpos : ∀ pt ∈ s, 0 ≤ pt.1 ∧ 0 ≤ pt.2)
    (hdown : ∀ pt ∈ s, ∀ x y : ℝ, 0 ≤ x → x ≤ pt.1 → 0 ≤ y → y ≤ pt.2 → (x, y) ∈ s)
    {q p : ℝ × ℝ} (hq : q ∈ convexHull ℝ s)
    (hp1 : 0 ≤ p.1) (hp2 : 0 ≤ p.2) (hle1 : p.1 ≤ q.1) (hle2 : p.2 ≤ q.2) :
    p ∈ convexHull ℝ s := by
  classical
  rw [mem_convexHull_iff_exists_fintype] at hq
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ := hq
  set r1 : ℝ := if q.1 = 0 then 0 else p.1 / q.1 with hr1def
  set r2 : ℝ := if q.2 = 0 then 0 else p.2 / q.2 with hr2def
  -- the componentwise sums of the representing combination equal q
  have hq1 : ∑ i, w i * (z i).1 = q.1 := by
    have := congrArg Prod.fst hsum
    simpa [Prod.fst_sum, Prod.smul_fst, smul_eq_mul] using this
  have hq2 : ∑ i, w i * (z i).2 = q.2 := by
    have := congrArg Prod.snd hsum
    simpa [Prod.snd_sum, Prod.smul_snd, smul_eq_mul] using this
  -- ratios lie in [0,1]
  have hr1_nonneg : 0 ≤ r1 := by
    rw [hr1def]; split_ifs with h
    · exact le_refl 0
    · exact div_nonneg hp1 (le_of_lt (lt_of_le_of_ne (hp1.trans hle1) (Ne.symm h)))
  have hr1_le : r1 ≤ 1 := by
    rw [hr1def]; split_ifs with h
    · exact zero_le_one
    · rw [div_le_one (lt_of_le_of_ne (hp1.trans hle1) (Ne.symm h))]; exact hle1
  have hr2_nonneg : 0 ≤ r2 := by
    rw [hr2def]; split_ifs with h
    · exact le_refl 0
    · exact div_nonneg hp2 (le_of_lt (lt_of_le_of_ne (hp2.trans hle2) (Ne.symm h)))
  have hr2_le : r2 ≤ 1 := by
    rw [hr2def]; split_ifs with h
    · exact zero_le_one
    · rw [div_le_one (lt_of_le_of_ne (hp2.trans hle2) (Ne.symm h))]; exact hle2
  -- key scaling identities
  have hkey1 : q.1 * r1 = p.1 := by
    rw [hr1def]; split_ifs with h
    · rw [mul_zero]; linarith [hp1, hle1, h]
    · rw [mul_div_cancel₀ _ h]
  have hkey2 : q.2 * r2 = p.2 := by
    rw [hr2def]; split_ifs with h
    · rw [mul_zero]; linarith [hp2, hle2, h]
    · rw [mul_div_cancel₀ _ h]
  refine mem_convexHull_of_exists_fintype w (fun i => ((z i).1 * r1, (z i).2 * r2)) hw0 hw1 ?_ ?_
  · intro i
    obtain ⟨hzi1, hzi2⟩ := hpos _ (hz i)
    refine hdown _ (hz i) _ _ (mul_nonneg hzi1 hr1_nonneg) ?_ (mul_nonneg hzi2 hr2_nonneg) ?_
    · calc (z i).1 * r1 ≤ (z i).1 * 1 := mul_le_mul_of_nonneg_left hr1_le hzi1
        _ = (z i).1 := mul_one _
    · calc (z i).2 * r2 ≤ (z i).2 * 1 := mul_le_mul_of_nonneg_left hr2_le hzi2
        _ = (z i).2 := mul_one _
  · apply Prod.ext
    · simp only [Prod.fst_sum, Prod.smul_fst, smul_eq_mul]
      calc ∑ i, w i * ((z i).1 * r1) = (∑ i, w i * (z i).1) * r1 := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => by ring)
        _ = q.1 * r1 := by rw [hq1]
        _ = p.1 := hkey1
    · simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
      calc ∑ i, w i * ((z i).2 * r2) = (∑ i, w i * (z i).2) * r2 := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => by ring)
        _ = q.2 * r2 := by rw [hq2]
        _ = p.2 := hkey2

/-- Convex-geometry gateway for the MAC time-sharing converse.  If a rate pair `(R₁, R₂)` is
bounded coordinate-wise by the time averages `(∑ a)/n`, `(∑ b)/n` and, jointly, `(∑ c)/n` of a
family of per-letter pentagons `Pᵢ = {(x,y) | 0 ≤ x ≤ aᵢ, 0 ≤ y ≤ bᵢ, x + y ≤ cᵢ}`, then
`(R₁, R₂)` lies in the convex hull of `⋃ i, Pᵢ`.  Requires both single-user bounds `a i ≤ c i`
and `b i ≤ c i` (see the module note). -/
theorem mac_avgPentagon_mem_convexHull {n : ℕ} (hn : 0 < n)
    (a b c : Fin n → ℝ) (h0a : ∀ i, 0 ≤ a i) (h0b : ∀ i, 0 ≤ b i)
    (hac : ∀ i, a i ≤ c i) (hbc : ∀ i, b i ≤ c i) (hsub : ∀ i, c i ≤ a i + b i)
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (h1 : R₁ ≤ (∑ i, a i) / n) (h2 : R₂ ≤ (∑ i, b i) / n) (hs : R₁ + R₂ ≤ (∑ i, c i) / n) :
    (R₁, R₂) ∈ convexHull ℝ
      (⋃ i, ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ a i ∧ p.2 ≤ b i ∧ p.1 + p.2 ≤ c i}
             : Set (ℝ × ℝ))) := by
  classical
  set S : Set (ℝ × ℝ) :=
    ⋃ i, {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ a i ∧ p.2 ≤ b i ∧ p.1 + p.2 ≤ c i} with hS
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hw1 : ∑ _i : Fin n, (n : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hn']
  -- down-closedness data for `S`
  have hpos : ∀ pt ∈ S, 0 ≤ pt.1 ∧ 0 ≤ pt.2 := by
    intro pt hpt
    rw [hS, Set.mem_iUnion] at hpt
    obtain ⟨i, hi⟩ := hpt
    exact ⟨hi.1, hi.2.1⟩
  have hdown : ∀ pt ∈ S, ∀ x y : ℝ, 0 ≤ x → x ≤ pt.1 → 0 ≤ y → y ≤ pt.2 → (x, y) ∈ S := by
    intro pt hpt x y hx0 hxle hy0 hyle
    rw [hS, Set.mem_iUnion] at hpt ⊢
    obtain ⟨i, hi⟩ := hpt
    refine ⟨i, hx0, hy0, hxle.trans hi.2.2.1, hyle.trans hi.2.2.2.1, ?_⟩
    calc x + y ≤ pt.1 + pt.2 := add_le_add hxle hyle
      _ ≤ c i := hi.2.2.2.2
  -- the two corner families lie in `S`
  have hcA_mem : ∀ i, ((a i, c i - a i) : ℝ × ℝ) ∈ S := by
    intro i
    rw [hS, Set.mem_iUnion]
    refine ⟨i, h0a i, ?_, le_refl _, ?_, ?_⟩
    · show 0 ≤ c i - a i; linarith [hac i]
    · show c i - a i ≤ b i; linarith [hsub i]
    · show a i + (c i - a i) ≤ c i; linarith
  have hcB_mem : ∀ i, ((c i - b i, b i) : ℝ × ℝ) ∈ S := by
    intro i
    rw [hS, Set.mem_iUnion]
    refine ⟨i, ?_, h0b i, ?_, le_refl _, ?_⟩
    · show 0 ≤ c i - b i; linarith [hbc i]
    · show c i - b i ≤ a i; linarith [hsub i]
    · show (c i - b i) + b i ≤ c i; linarith
  -- the two corner averages lie in the convex hull
  set A : ℝ × ℝ := ∑ i, (n : ℝ)⁻¹ • ((a i, c i - a i) : ℝ × ℝ) with hAdef
  set B : ℝ × ℝ := ∑ i, (n : ℝ)⁻¹ • ((c i - b i, b i) : ℝ × ℝ) with hBdef
  have hA_mem : A ∈ convexHull ℝ S := by
    rw [hAdef]
    exact mem_convexHull_of_exists_fintype _ _ (fun _ => by positivity) hw1 hcA_mem rfl
  have hB_mem : B ∈ convexHull ℝ S := by
    rw [hBdef]
    exact mem_convexHull_of_exists_fintype _ _ (fun _ => by positivity) hw1 hcB_mem rfl
  -- component computations
  have hA1 : A.1 = (∑ i, a i) / n := by
    rw [hAdef]
    simp only [Prod.fst_sum, Prod.smul_fst, smul_eq_mul]
    rw [← Finset.mul_sum, inv_mul_eq_div]
  have hAsum : A.1 + A.2 = (∑ i, c i) / n := by
    rw [hAdef]
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [← Finset.sum_add_distrib,
      show (∑ i, ((n : ℝ)⁻¹ * a i + (n : ℝ)⁻¹ * (c i - a i))) = ∑ i, (n : ℝ)⁻¹ * c i from
        Finset.sum_congr rfl (fun i _ => by ring),
      ← Finset.mul_sum, inv_mul_eq_div]
  have hB2 : B.2 = (∑ i, b i) / n := by
    rw [hBdef]
    simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
    rw [← Finset.mul_sum, inv_mul_eq_div]
  have hBsum : B.1 + B.2 = (∑ i, c i) / n := by
    rw [hBdef]
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [← Finset.sum_add_distrib,
      show (∑ i, ((n : ℝ)⁻¹ * (c i - b i) + (n : ℝ)⁻¹ * b i)) = ∑ i, (n : ℝ)⁻¹ * c i from
        Finset.sum_congr rfl (fun i _ => by ring),
      ← Finset.mul_sum, inv_mul_eq_div]
  have hR1A : R₁ ≤ A.1 := by rw [hA1]; exact h1
  have hR2B : R₂ ≤ B.2 := by rw [hB2]; exact h2
  -- produce a hull point dominating `(R₁, R₂)`
  obtain ⟨q, hqmem, hq1, hq2⟩ :
      ∃ q : ℝ × ℝ, q ∈ convexHull ℝ S ∧ R₁ ≤ q.1 ∧ R₂ ≤ q.2 := by
    by_cases hc1 : R₂ ≤ A.2
    · exact ⟨A, hA_mem, hR1A, hc1⟩
    · rw [not_le] at hc1
      by_cases hc2 : R₁ ≤ B.1
      · exact ⟨B, hB_mem, hc2, hR2B⟩
      · rw [not_le] at hc2
        have hden : 0 < A.1 - B.1 := by linarith [hR1A]
        have hne : A.1 - B.1 ≠ 0 := ne_of_gt hden
        set θ : ℝ := (R₁ - B.1) / (A.1 - B.1) with hθdef
        have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (le_of_lt hden)
        have hθ1 : θ ≤ 1 := by rw [hθdef, div_le_one hden]; linarith [hR1A]
        have hfst : (θ • A + (1 - θ) • B).1 = θ * A.1 + (1 - θ) * B.1 := by
          simp [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        have hsnd : (θ • A + (1 - θ) • B).2 = θ * A.2 + (1 - θ) * B.2 := by
          simp [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        have hval1 : (θ • A + (1 - θ) • B).1 = R₁ := by
          rw [hfst, hθdef]; field_simp; ring
        have hsumq : (θ • A + (1 - θ) • B).1 + (θ • A + (1 - θ) • B).2 = (∑ i, c i) / n := by
          rw [hfst, hsnd,
            show θ * A.1 + (1 - θ) * B.1 + (θ * A.2 + (1 - θ) * B.2)
              = θ * (A.1 + A.2) + (1 - θ) * (B.1 + B.2) from by ring,
            hAsum, hBsum]
          ring
        refine ⟨θ • A + (1 - θ) • B, ?_, ?_, ?_⟩
        · exact (convex_convexHull ℝ S) hA_mem hB_mem hθ0 (by linarith) (by ring)
        · rw [hval1]
        · have hq2eq : (θ • A + (1 - θ) • B).2 = (∑ i, c i) / n - R₁ := by
            have := hsumq; rw [hval1] at this; linarith
          rw [hq2eq]; linarith [hs]
  exact convexHull_mem_of_le hpos hdown hqmem hR₁ hR₂ hq1 hq2

end InformationTheory.Shannon.MAC
