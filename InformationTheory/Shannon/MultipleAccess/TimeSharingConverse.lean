import InformationTheory.Shannon.MultipleAccess.TimeSharing
import InformationTheory.Shannon.MultipleAccess.Reconciliation
import InformationTheory.Shannon.MultipleAccess.Converse
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Integral.Marginal

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

/-! ### Pentagon well-formedness for the product input

The convex-geometry gateway `mac_avgPentagon_mem_convexHull` needs the two single-user bounds
`a i ≤ c i` and `b i ≤ c i`.  In the MAC application these are the two information inequalities
`macInfo₁ ≤ macInfoBoth` and `macInfo₂ ≤ macInfoBoth`, i.e. `I(X₁; (X₂, Y)) ≤ I((X₁, X₂); Y)` and
`I(X₂; (X₁, Y)) ≤ I((X₁, X₂); Y)`.  Both follow from the chain rule
`I((X₁, X₂); Y) = I(X_j; Y) + I(X_{3-j}; Y | X_j)` and nonnegativity of mutual information (finite
alphabets, so no independence hypothesis is needed here). -/

section PentagonWellFormedness

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁]
    [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂]
    [MeasurableSingletonClass α₂] [StandardBorelSpace α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
    [MeasurableSingletonClass β] [StandardBorelSpace β]

omit [StandardBorelSpace α₂] in
/-- Pentagon well-formedness (user 1): `macInfo₁ ≤ macInfoBoth`, i.e.
`I(X₁; (X₂, Y)) ≤ I((X₁, X₂); Y)`.  Supplies the `a i ≤ c i` hypothesis of
`mac_avgPentagon_mem_convexHull`.  Proved by the chain rule
`I((X₂, X₁); Y) = I(X₂; Y) + I(X₁; Y | X₂)` (after `prodComm`) and `condMutualInfo_nonneg`. -/
theorem mac_macInfo₁_le_macInfoBoth
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁] (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    macInfo₁ p₁ p₂ W ≤ macInfoBoth p₁ p₂ W := by
  have hX1 : Measurable (Prod.fst : α₁ × α₂ × β → α₁) := measurable_fst
  have hX2 : Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hY : Measurable (fun q : α₁ × α₂ × β ↦ q.2.2) := measurable_snd.comp measurable_snd
  rw [macInfo₁_eq_condMutualInfo_toReal p₁ p₂ W, macInfoBoth_eq_mutualInfo_toReal p₁ p₂ W]
  set J := macJointDistribution p₁ p₂ W with hJ
  refine ENNReal.toReal_mono ?_ ?_
  · exact mutualInfo_ne_top J _ _ (hX1.prodMk hX2) hY
  · -- `I((X₁, X₂); Y) = I((X₂, X₁); Y)` (prodComm), then chain rule
    -- `I((X₂, X₁); Y) = I(X₂; Y) + I(X₁; Y | X₂)`, then drop the nonneg `I(X₂; Y)`.
    have heq : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) (fun q ↦ q.2.2)
        = mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.1, q.1)) (fun q ↦ q.2.2) :=
      mutualInfo_map_left_measurableEquiv J (fun q : α₁ × α₂ × β ↦ (q.2.1, q.1))
        (fun q ↦ q.2.2) (hX2.prodMk hX1) hY MeasurableEquiv.prodComm
    have hchain : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.1, q.1)) (fun q ↦ q.2.2)
        = mutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2)
          + condMutualInfo J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1) :=
      mutualInfo_chain_rule J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1) hX1 hY hX2
    rw [heq, hchain]
    exact self_le_add_left _ _

omit [StandardBorelSpace α₁] in
/-- Pentagon well-formedness (user 2): `macInfo₂ ≤ macInfoBoth`, i.e.
`I(X₂; (X₁, Y)) ≤ I((X₁, X₂); Y)`.  Supplies the `b i ≤ c i` hypothesis of
`mac_avgPentagon_mem_convexHull`.  Proved by the chain rule
`I((X₁, X₂); Y) = I(X₁; Y) + I(X₂; Y | X₁)` and `condMutualInfo_nonneg`. -/
theorem mac_macInfo₂_le_macInfoBoth
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁] (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    macInfo₂ p₁ p₂ W ≤ macInfoBoth p₁ p₂ W := by
  have hX1 : Measurable (Prod.fst : α₁ × α₂ × β → α₁) := measurable_fst
  have hX2 : Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hY : Measurable (fun q : α₁ × α₂ × β ↦ q.2.2) := measurable_snd.comp measurable_snd
  rw [macInfo₂_eq_condMutualInfo_toReal p₁ p₂ W, macInfoBoth_eq_mutualInfo_toReal p₁ p₂ W]
  set J := macJointDistribution p₁ p₂ W with hJ
  refine ENNReal.toReal_mono ?_ ?_
  · exact mutualInfo_ne_top J _ _ (hX1.prodMk hX2) hY
  · -- chain rule `I((X₁, X₂); Y) = I(X₁; Y) + I(X₂; Y | X₁)`, then drop the nonneg `I(X₁; Y)`.
    have hchain : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) (fun q ↦ q.2.2)
        = mutualInfo J Prod.fst (fun q ↦ q.2.2)
          + condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst :=
      mutualInfo_chain_rule J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst hX2 hY hX1
    rw [hchain]
    exact self_le_add_left _ _

end PentagonWellFormedness

/-! ### Code → ambient bridge (Gap 0)

`mac_converse` is a *floating* message-level statement: it takes the ambient probability space
`μ`, the message/output projections, and all the memoryless / Markov / independence / uniformity
hypotheses as preconditions.  This section constructs, from a bare `MACCode c` and a Markov
channel `W`, the canonical ambient measure

`macConverseAmbient c W := (uniform on Fin M₁ × Fin M₂) ⊗ₘ (per-letter product channel)`

on `Ω := (Fin M₁ × Fin M₂) × (Fin n → β)`, reads the messages and outputs off as coordinate
projections, and discharges the `mac_converse` hypotheses.  The resulting bridge
`mac_converse_from_code` is the true operational starting point of the converse. -/

section CodeToAmbient

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open scoped ENNReal

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁]
    [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂]
    [MeasurableSingletonClass α₂] [StandardBorelSpace α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
    [MeasurableSingletonClass β] [StandardBorelSpace β]
variable {M₁ M₂ n : ℕ}

/-- The uniform probability law `(card X)⁻¹ • count` on a nonempty finite type. -/
instance uniformCount_isProbabilityMeasure {X : Type*}
    [Fintype X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X] :
    IsProbabilityMeasure ((Fintype.card X : ℝ≥0∞)⁻¹ • Measure.count : Measure X) := by
  constructor
  have hcard : (Measure.count (Set.univ : Set X)) = (Fintype.card X : ℝ≥0∞) := by
    rw [Measure.count_apply_finite Set.univ Set.finite_univ]
    simp
  rw [Measure.smul_apply, smul_eq_mul, hcard,
    ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)]

/-- Uniform input law on the message pair: the product of the two uniform message laws. -/
noncomputable def macConverseInput (M₁ M₂ : ℕ) : Measure (Fin M₁ × Fin M₂) :=
  ((Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count).prod
    ((Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)

instance macConverseInput_isProbabilityMeasure [NeZero M₁] [NeZero M₂] :
    IsProbabilityMeasure (macConverseInput M₁ M₂) := by
  unfold macConverseInput; infer_instance

/-- Per-letter product-channel kernel: given the message pair `m`, the output law is the product
over the `n` letters of the channel `W` applied to the encoded pair `(encoder₁ m₁ i, encoder₂ m₂ i)`.
The channel input is deterministic in the messages (through the encoders). -/
noncomputable def macConverseKernel
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) :
    Kernel (Fin M₁ × Fin M₂) (Fin n → β) :=
  Kernel.ofFunOfCountable
    (fun m ↦ Measure.pi (fun i ↦ W (c.encoder₁ m.1 i, c.encoder₂ m.2 i)))

instance macConverseKernel_isMarkovKernel
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    IsMarkovKernel (macConverseKernel c W) := by
  refine ⟨fun m ↦ ?_⟩
  show IsProbabilityMeasure (Measure.pi (fun i ↦ W (c.encoder₁ m.1 i, c.encoder₂ m.2 i)))
  infer_instance

/-- Canonical ambient measure for the MAC converse: a uniform message pair passed through the
per-letter product channel. -/
noncomputable def macConverseAmbient
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) :
    Measure ((Fin M₁ × Fin M₂) × (Fin n → β)) :=
  (macConverseInput M₁ M₂) ⊗ₘ (macConverseKernel c W)

instance macConverseAmbient_isProbabilityMeasure
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    IsProbabilityMeasure (macConverseAmbient c W) := by
  unfold macConverseAmbient; infer_instance

/-- Message-1 projection `ω ↦ ω.1.1`. -/
def macConverseMsg₁ : ((Fin M₁ × Fin M₂) × (Fin n → β)) → Fin M₁ := fun ω ↦ ω.1.1

/-- Message-2 projection `ω ↦ ω.1.2`. -/
def macConverseMsg₂ : ((Fin M₁ × Fin M₂) × (Fin n → β)) → Fin M₂ := fun ω ↦ ω.1.2

/-- Output projection `i ↦ ω ↦ ω.2 i`. -/
def macConverseYs : Fin n → ((Fin M₁ × Fin M₂) × (Fin n → β)) → β := fun i ω ↦ ω.2 i

omit [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] in
lemma measurable_macConverseMsg₁ :
    Measurable (macConverseMsg₁ (M₁ := M₁) (M₂ := M₂) (n := n) (β := β)) :=
  measurable_fst.fst

omit [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] in
lemma measurable_macConverseMsg₂ :
    Measurable (macConverseMsg₂ (M₁ := M₁) (M₂ := M₂) (n := n) (β := β)) :=
  measurable_fst.snd

omit [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] in
lemma measurable_macConverseYs (i : Fin n) :
    Measurable (macConverseYs (M₁ := M₁) (M₂ := M₂) (n := n) (β := β) i) :=
  (measurable_pi_apply i).comp measurable_snd

lemma macConverseInput_map_fst [NeZero M₁] [NeZero M₂] :
    (macConverseInput M₁ M₂).map Prod.fst
      = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count := by
  unfold macConverseInput
  rw [Measure.map_fst_prod, measure_univ, one_smul]

lemma macConverseInput_map_snd [NeZero M₁] [NeZero M₂] :
    (macConverseInput M₁ M₂).map Prod.snd
      = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count := by
  unfold macConverseInput
  rw [Measure.map_snd_prod, measure_univ, one_smul]

lemma macConverseInput_eq :
    macConverseInput M₁ M₂ = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count := by
  refine Measure.ext_of_singleton (fun q ↦ ?_)
  obtain ⟨a, b⟩ := q
  have hsgl : ({(a, b)} : Set (Fin M₁ × Fin M₂)) = {a} ×ˢ {b} := by
    ext ⟨x, y⟩; simp [Prod.ext_iff]
  have hR : ((Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count) {(a, b)}
      = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ := by
    rw [Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]
  have hL : (macConverseInput M₁ M₂) {(a, b)}
      = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ * (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ := by
    unfold macConverseInput
    rw [hsgl, Measure.prod_prod, Measure.smul_apply, Measure.smul_apply, smul_eq_mul,
      smul_eq_mul, Measure.count_singleton, Measure.count_singleton, mul_one, mul_one]
  rw [hL, hR, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]

/-- The map `ω ↦ (Msg₁ ω, Msg₂ ω)` is the outer first projection `Prod.fst` on the ambient. -/
lemma macConverse_msgPair_eq_fst :
    (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β) ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω))
      = Prod.fst := by
  funext ω; exact Prod.mk.eta

lemma macConverseMsg₁_uniform
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    (macConverseAmbient c W).map macConverseMsg₁
      = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count := by
  have hcomp : (macConverseMsg₁ (M₁ := M₁) (M₂ := M₂) (n := n) (β := β))
      = Prod.fst ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map measurable_fst measurable_fst]
  have hfst : (macConverseAmbient c W).map Prod.fst = macConverseInput M₁ M₂ := by
    rw [macConverseAmbient]; exact Measure.fst_compProd _ _
  rw [hfst, macConverseInput_map_fst]

lemma macConverseMsg₂_uniform
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    (macConverseAmbient c W).map macConverseMsg₂
      = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count := by
  have hcomp : (macConverseMsg₂ (M₁ := M₁) (M₂ := M₂) (n := n) (β := β))
      = Prod.snd ∘ Prod.fst := rfl
  rw [hcomp, ← Measure.map_map measurable_snd measurable_fst]
  have hfst : (macConverseAmbient c W).map Prod.fst = macConverseInput M₁ M₂ := by
    rw [macConverseAmbient]; exact Measure.fst_compProd _ _
  rw [hfst, macConverseInput_map_snd]

lemma macConverseMsg₁₂_uniform
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    (macConverseAmbient c W).map (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω))
      = (Fintype.card (Fin M₁ × Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count := by
  rw [macConverse_msgPair_eq_fst]
  have hfst : (macConverseAmbient c W).map Prod.fst = macConverseInput M₁ M₂ := by
    rw [macConverseAmbient]; exact Measure.fst_compProd _ _
  rw [hfst, macConverseInput_eq]

/-- Codeword → output block kernel: given an encoded input-pair codeword `x = (x₁, x₂)`, the
output law is the per-letter product `∏ᵢ W (x₁ i, x₂ i)` of the MAC channel. -/
noncomputable def macConverseCodeKernel (W : MACChannel α₁ α₂ β) :
    Kernel ((Fin n → α₁) × (Fin n → α₂)) (Fin n → β) :=
  Kernel.ofFunOfCountable (fun x ↦ Measure.pi (fun i ↦ W (x.1 i, x.2 i)))

instance macConverseCodeKernel_isMarkovKernel (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    IsMarkovKernel (macConverseCodeKernel (n := n) (α₁ := α₁) (α₂ := α₂) (β := β) W) := by
  refine ⟨fun x ↦ ?_⟩
  show IsProbabilityMeasure (Measure.pi (fun i ↦ W (x.1 i, x.2 i)))
  infer_instance

/-- Abstract Markov-chain factorization `M → g M → Y` for an ambient `ν ⊗ₘ κ` in which the
message-to-output kernel `κ` factors through a deterministic encoder `g : M → Z` and a
codeword kernel `Wcode : Z → Y` (i.e. `κ m = Wcode (g m)`).  This is the general shape behind
the concrete MAC-converse Markov chain; it needs no product/pi structure, only the
factorization `hκ`.
@audit:ok -/
private lemma isMarkovChain_of_compProd_encoder
    {M Z Y : Type*}
    [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace Z]
    [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (ν : Measure M) [IsProbabilityMeasure ν]
    (g : M → Z) (hg : Measurable g)
    (κ : Kernel M Y) [IsMarkovKernel κ]
    (Wcode : Kernel Z Y) [IsMarkovKernel Wcode]
    (hκ : ∀ m : M, κ m = Wcode (g m)) :
    IsMarkovChain (ν ⊗ₘ κ)
      (Prod.fst : M × Y → M)
      (fun ω : M × Y ↦ g ω.1)
      (Prod.snd : M × Y → Y) := by
  set μ : Measure (M × Y) := ν ⊗ₘ κ with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  set Xs : M × Y → M := Prod.fst with hXs_def
  set Zc : M × Y → Z := fun ω ↦ g ω.1 with hZc_def
  set Yo : M × Y → Y := Prod.snd with hYo_def
  have hXs_meas : Measurable Xs := measurable_fst
  have hZc_meas : Measurable Zc := hg.comp measurable_fst
  have hYo_meas : Measurable Yo := measurable_snd
  -- Message marginal `μ.map Xs = ν`, hence codeword law `μ.map Zc = ν.map g`.
  have h_map_Xs : μ.map Xs = ν := by rw [hμ_def, hXs_def]; exact Measure.fst_compProd _ _
  have h_map_Zc : μ.map Zc = ν.map g := by
    have hcomp : Zc = g ∘ Xs := rfl
    rw [hcomp, ← Measure.map_map hg hXs_meas, h_map_Xs]
  -- Linchpin: `μ.map (Zc, Yo) = (μ.map Zc) ⊗ₘ Wcode`.
  have h_pair_eq : μ.map (fun ω ↦ (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ Wcode := by
    rw [h_map_Zc]
    refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
    have hFmeas : Measurable (fun ω : M × Y ↦ f (Zc ω, Yo ω)) :=
      hf.comp (hZc_meas.prodMk hYo_meas)
    have hF_meas : Measurable (fun z : Z ↦ ∫⁻ y : Y, f (z, y) ∂(Wcode z)) :=
      Measurable.lintegral_kernel_prod_right' (κ := Wcode) hf
    rw [lintegral_map hf (hZc_meas.prodMk hYo_meas), hμ_def,
      Measure.lintegral_compProd hFmeas, Measure.lintegral_compProd hf,
      lintegral_map hF_meas hg]
    refine lintegral_congr fun m ↦ ?_
    rw [hκ]
  -- Identify `condDistrib Yo Zc μ =ᵐ Wcode`.
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc_meas.aemeasurable
  have hK_Y_eq : condDistrib Yo Zc μ =ᵐ[μ.map Zc] Wcode :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hYo_meas.aemeasurable h_pair_eq
  unfold IsMarkovChain
  set K_X : Kernel Z M := condDistrib Xs Zc μ with hK_X_def
  have h_compProd_eq :
      (μ.map Zc) ⊗ₘ (K_X ×ₖ condDistrib Yo Zc μ) = (μ.map Zc) ⊗ₘ (K_X ×ₖ Wcode) := by
    refine Measure.compProd_congr ?_
    filter_upwards [hK_Y_eq] with a ha
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, ha]
  rw [h_compProd_eq]
  -- Triple-joint factorization via `ext_of_lintegral`.
  have h_LHS_meas : Measurable (fun ω ↦ (Zc ω, Xs ω, Yo ω)) :=
    hZc_meas.prodMk (hXs_meas.prodMk hYo_meas)
  have hKX_fold : (μ.map Zc) ⊗ₘ K_X = μ.map (fun ω ↦ (Zc ω, Xs ω)) :=
    compProd_map_condDistrib (μ := μ) (X := Zc) (Y := Xs) hXs_meas.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf h_LHS_meas, Measure.lintegral_compProd hf]
  have h_inner_split : ∀ z : Z,
      ∫⁻ p : M × Y, f (z, p.1, p.2) ∂((K_X ×ₖ Wcode) z)
        = ∫⁻ x : M, ∫⁻ y : Y, f (z, x, y) ∂(Wcode z) ∂(K_X z) := by
    intro z
    rw [Kernel.prod_apply,
      lintegral_prod (fun p : M × Y ↦ f (z, p.1, p.2))
        (hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).aemeasurable]
  simp_rw [h_inner_split]
  set G : Z × M → ℝ≥0∞ := fun p ↦ ∫⁻ y : Y, f (p.1, p.2, y) ∂(Wcode p.1) with hG_def
  have hG_meas : Measurable G := by
    let K' : Kernel (Z × M) Y := Wcode.comap (Prod.fst : Z × M → Z) measurable_fst
    have h_eq_K' : G = fun p : Z × M ↦ ∫⁻ y : Y, f (p.1, p.2, y) ∂(K' p) := by
      funext p; simp [G, K', Kernel.comap_apply]
    rw [h_eq_K']
    exact Measurable.lintegral_kernel_prod_right' (κ := K')
      (f := fun pp : (Z × M) × Y ↦ f (pp.1.1, pp.1.2, pp.2))
      (hf.comp (((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  have h_RHS_is_G : ∀ z : Z, ∀ x : M,
      ∫⁻ y : Y, f (z, x, y) ∂(Wcode z) = G (z, x) := fun _ _ ↦ rfl
  simp_rw [h_RHS_is_G]
  have hFmeas2 : Measurable (fun ω : M × Y ↦ f (Zc ω, Xs ω, Yo ω)) := hf.comp h_LHS_meas
  have hGmeas2 : Measurable (fun ω : M × Y ↦ G (Zc ω, Xs ω)) :=
    hG_meas.comp (hZc_meas.prodMk hXs_meas)
  rw [← Measure.lintegral_compProd hG_meas, hKX_fold,
    lintegral_map hG_meas (hZc_meas.prodMk hXs_meas), hμ_def,
    Measure.lintegral_compProd hFmeas2, Measure.lintegral_compProd hGmeas2]
  refine lintegral_congr fun m ↦ ?_
  rw [hκ]
  have hRHSconst : (fun y : Y ↦ G (Zc (m, y), Xs (m, y)))
      = (fun _ : Y ↦ ∫⁻ y' : Y, f (g m, m, y') ∂(Wcode (g m))) := by
    funext y; show G (g m, m) = _; rw [hG_def]
  rw [hRHSconst, lintegral_const, measure_univ, mul_one]

/-- Re-randomizing a single coordinate of a product of probability measures leaves the
`Measure.pi`-integral unchanged.  Used to peel the `i`-th output letter off the block channel
`∏ⱼ W (xⱼ)` in the memoryless-channel derivation.
@audit:ok -/
private lemma lintegral_pi_reRandomize {γ : Type*} [MeasurableSpace γ]
    {k : ℕ} (ζ : Fin k → Measure γ) [∀ j, IsProbabilityMeasure (ζ j)]
    (i : Fin k) (F : (Fin k → γ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y ∂(Measure.pi ζ)
      = ∫⁻ y, (∫⁻ b, F (Function.update y i b) ∂(ζ i)) ∂(Measure.pi ζ) := by
  classical
  haveI : ∀ j, SigmaFinite (ζ j) := fun j ↦ inferInstance
  have hGmeas : Measurable (fun y ↦ ∫⁻ b, F (Function.update y i b) ∂(ζ i)) := by
    rw [show (fun y ↦ ∫⁻ b, F (Function.update y i b) ∂(ζ i))
          = MeasureTheory.lmarginal ζ ({i} : Finset (Fin k)) F from
        (MeasureTheory.lmarginal_singleton F i).symm]
    exact hF.lmarginal (μ := ζ)
  refine MeasureTheory.lintegral_eq_of_lmarginal_eq ({i} : Finset (Fin k)) hF hGmeas ?_
  rw [← MeasureTheory.lmarginal_singleton F i,
    MeasureTheory.lmarginal_singleton (MeasureTheory.lmarginal ζ ({i} : Finset (Fin k)) F) i]
  funext x
  simp_rw [MeasureTheory.lmarginal_update_of_mem ζ (Finset.mem_singleton_self i) F]
  rw [lintegral_const, measure_univ, mul_one]

/-- Marginalization of a product of probability measures at a single coordinate.
@audit:ok -/
private lemma lintegral_pi_eval {γ : Type*} [MeasurableSpace γ]
    {k : ℕ} (ζ : Fin k → Measure γ) [∀ j, IsProbabilityMeasure (ζ j)]
    (i : Fin k) (g : γ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g (y i) ∂(Measure.pi ζ) = ∫⁻ b, g b ∂(ζ i) := by
  rw [lintegral_pi_reRandomize ζ i (fun y ↦ g (y i)) (hg.comp (measurable_pi_apply i))]
  simp only [Function.update_self]
  rw [lintegral_const, measure_univ, mul_one]

/-- **Memoryless-channel property from a product-channel ambient.**  If the message-to-output
kernel factors as the per-letter product `κ m = ∏ⱼ W (x m j)` of a channel `W` applied to a
deterministic codeword `x m`, the ambient `ν ⊗ₘ κ` is a memoryless channel with per-letter
inputs `x ω.1 i` and per-letter outputs `ω.2 i`.
@audit:ok -/
private lemma isMemorylessChannel_of_compProd_pi
    {M A B : Type*}
    [MeasurableSpace M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {k : ℕ}
    (ν : Measure M) [IsProbabilityMeasure ν]
    (x : M → Fin k → A) (hx : Measurable x)
    (W : Kernel A B) [IsMarkovKernel W]
    (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ]
    (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))) :
    IsMemorylessChannel (ν ⊗ₘ κ) (fun i ω ↦ x ω.1 i) (fun i ω ↦ ω.2 i) := by
  intro i
  set μ : Measure (M × (Fin k → B)) := ν ⊗ₘ κ with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  -- The three RVs of the per-letter Markov chain.
  set Zc : M × (Fin k → B) → A := fun ω ↦ x ω.1 i with hZc_def
  set Yo : M × (Fin k → B) → B := fun ω ↦ ω.2 i with hYo_def
  set Full : M × (Fin k → B) → (({j : Fin k // j ≠ i} → A) × ({j : Fin k // j ≠ i} → B)) :=
    fun ω ↦ ((fun j ↦ x ω.1 j.val), (fun j ↦ ω.2 j.val)) with hFull_def
  have hxi_meas : Measurable (fun m ↦ x m i) := (measurable_pi_apply i).comp hx
  have hZc_meas : Measurable Zc := hxi_meas.comp measurable_fst
  have hYo_meas : Measurable Yo := (measurable_pi_apply i).comp measurable_snd
  have hFull_meas : Measurable Full := by
    rw [hFull_def]
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_iff.mpr
        (fun j ↦ (measurable_pi_apply j.val).comp (hx.comp measurable_fst))
    · exact measurable_pi_iff.mpr (fun j ↦ (measurable_pi_apply j.val).comp measurable_snd)
  -- Codeword law `μ.map Zc = ν.map (· i ∘ x)`.
  have h_map_Zc : μ.map Zc = ν.map (fun m ↦ x m i) := by
    have hcomp : Zc = (fun m ↦ x m i) ∘ Prod.fst := rfl
    rw [hcomp, ← Measure.map_map hxi_meas measurable_fst]
    congr 1
    rw [hμ_def]; exact Measure.fst_compProd _ _
  -- Step 1: `μ.map (Zc, Yo) = (μ.map Zc) ⊗ₘ W`.
  have h_pair_eq : μ.map (fun ω ↦ (Zc ω, Yo ω)) = (μ.map Zc) ⊗ₘ W := by
    rw [h_map_Zc]
    refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
    have hFmeas : Measurable (fun ω : M × (Fin k → B) ↦ f (Zc ω, Yo ω)) :=
      hf.comp (hZc_meas.prodMk hYo_meas)
    have hFm2 : Measurable (fun z : A ↦ ∫⁻ b : B, f (z, b) ∂(W z)) :=
      Measurable.lintegral_kernel_prod_right' (κ := W) hf
    rw [lintegral_map hf (hZc_meas.prodMk hYo_meas), hμ_def,
      Measure.lintegral_compProd hFmeas, Measure.lintegral_compProd hf,
      lintegral_map hFm2 hxi_meas]
    refine lintegral_congr fun m ↦ ?_
    rw [hκ]
    exact lintegral_pi_eval (fun j ↦ W (x m j)) i (fun b ↦ f (x m i, b))
      (hf.comp (measurable_const.prodMk measurable_id))
  -- Step 2: identify `condDistrib Yo Zc μ =ᵐ W` and substitute.
  haveI : IsProbabilityMeasure (μ.map Zc) :=
    Measure.isProbabilityMeasure_map hZc_meas.aemeasurable
  have hK_Y_eq : condDistrib Yo Zc μ =ᵐ[μ.map Zc] W :=
    condDistrib_ae_eq_of_measure_eq_compProd Zc hYo_meas.aemeasurable h_pair_eq
  unfold IsMarkovChain
  set K_Full := condDistrib Full Zc μ with hK_Full_def
  have h_compProd_eq :
      (μ.map Zc) ⊗ₘ (K_Full ×ₖ condDistrib Yo Zc μ) = (μ.map Zc) ⊗ₘ (K_Full ×ₖ W) := by
    refine Measure.compProd_congr ?_
    filter_upwards [hK_Y_eq] with a ha
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, ha]
  rw [h_compProd_eq]
  -- Step 3: triple-joint factorization via `ext_of_lintegral` + the re-randomize identity.
  have h_LHS_meas : Measurable (fun ω ↦ (Zc ω, Full ω, Yo ω)) :=
    hZc_meas.prodMk (hFull_meas.prodMk hYo_meas)
  have hKX_fold : (μ.map Zc) ⊗ₘ K_Full = μ.map (fun ω ↦ (Zc ω, Full ω)) :=
    compProd_map_condDistrib (μ := μ) (X := Zc) (Y := Full) hFull_meas.aemeasurable
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf h_LHS_meas, Measure.lintegral_compProd hf]
  have h_inner_split : ∀ z : A,
      ∫⁻ p : (({j : Fin k // j ≠ i} → A) × ({j : Fin k // j ≠ i} → B)) × B,
          f (z, p.1, p.2) ∂((K_Full ×ₖ W) z)
        = ∫⁻ full, ∫⁻ b, f (z, full, b) ∂(W z) ∂(K_Full z) := by
    intro z
    rw [Kernel.prod_apply,
      lintegral_prod
        (fun p : (({j : Fin k // j ≠ i} → A) × ({j : Fin k // j ≠ i} → B)) × B ↦ f (z, p.1, p.2))
        (hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).aemeasurable]
  simp_rw [h_inner_split]
  set G : A × (({j : Fin k // j ≠ i} → A) × ({j : Fin k // j ≠ i} → B)) → ℝ≥0∞ :=
    fun p ↦ ∫⁻ b, f (p.1, p.2, b) ∂(W p.1) with hG_def
  have hG_meas : Measurable G := by
    let K' : Kernel (A × (({j : Fin k // j ≠ i} → A) × ({j : Fin k // j ≠ i} → B))) B :=
      W.comap Prod.fst measurable_fst
    have h_eq_K' : G = fun p ↦ ∫⁻ b, f (p.1, p.2, b) ∂(K' p) := by
      funext p; simp [G, K', Kernel.comap_apply]
    rw [h_eq_K']
    exact Measurable.lintegral_kernel_prod_right' (κ := K')
      (f := fun pp ↦ f (pp.1.1, pp.1.2, pp.2))
      (hf.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have h_RHS_is_G : ∀ z full, ∫⁻ b, f (z, full, b) ∂(W z) = G (z, full) := fun _ _ ↦ rfl
  simp_rw [h_RHS_is_G]
  have hFmeas2 : Measurable (fun ω ↦ f (Zc ω, Full ω, Yo ω)) := hf.comp h_LHS_meas
  have hGmeas2 : Measurable (fun ω ↦ G (Zc ω, Full ω)) := hG_meas.comp (hZc_meas.prodMk hFull_meas)
  rw [← Measure.lintegral_compProd hG_meas, hKX_fold,
    lintegral_map hG_meas (hZc_meas.prodMk hFull_meas), hμ_def,
    Measure.lintegral_compProd hFmeas2, Measure.lintegral_compProd hGmeas2]
  refine lintegral_congr fun m ↦ ?_
  rw [hκ]
  have hpair_m : Measurable (fun y : Fin k → B ↦ ((m, y) : M × (Fin k → B))) :=
    measurable_const.prodMk measurable_id
  have hFm3 : Measurable (fun y ↦ f (Zc (m, y), Full (m, y), Yo (m, y))) :=
    hf.comp ((hZc_meas.comp hpair_m).prodMk
      ((hFull_meas.comp hpair_m).prodMk (hYo_meas.comp hpair_m)))
  rw [lintegral_pi_reRandomize (fun j ↦ W (x m j)) i
    (fun y ↦ f (Zc (m, y), Full (m, y), Yo (m, y))) hFm3]
  refine lintegral_congr fun y ↦ ?_
  rw [hG_def]
  show ∫⁻ b, f (Zc (m, Function.update y i b), Full (m, Function.update y i b),
      Yo (m, Function.update y i b)) ∂(W (x m i))
    = ∫⁻ b, f (Zc (m, y), Full (m, y), b) ∂(W (x m i))
  refine lintegral_congr fun b ↦ ?_
  refine congrArg f (Prod.ext rfl (Prod.ext (Prod.ext rfl ?_) ?_))
  · funext j; exact Function.update_of_ne j.2 b y
  · exact Function.update_self i b y

/-- Memoryless-channel property of the constructed ambient: the per-letter output is conditionally
independent of the other letters given the current input pair.
@audit:ok -/
lemma macConverse_memorylessChannel
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    IsMemorylessChannel (macConverseAmbient c W)
      (fun i ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i))
      macConverseYs :=
  isMemorylessChannel_of_compProd_pi (macConverseInput M₁ M₂)
    (fun m j ↦ (c.encoder₁ m.1 j, c.encoder₂ m.2 j)) (measurable_of_countable _)
    W (macConverseKernel c W) (fun m ↦ rfl)

/-- The two messages are independent under the constructed ambient (uniform product input law),
hence their mutual information vanishes.
@audit:ok -/
lemma macConverse_mutualInfo_eq_zero
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    mutualInfo (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂ = 0 := by
  rw [mutualInfo_eq_zero_iff_indep (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂
      measurable_macConverseMsg₁ measurable_macConverseMsg₂,
    indepFun_iff_map_prod_eq_prod_map_map measurable_macConverseMsg₁.aemeasurable
      measurable_macConverseMsg₂.aemeasurable,
    macConverseMsg₁_uniform c W, macConverseMsg₂_uniform c W, macConverse_msgPair_eq_fst]
  have hfst : (macConverseAmbient c W).map Prod.fst = macConverseInput M₁ M₂ := by
    rw [macConverseAmbient]; exact Measure.fst_compProd _ _
  rw [hfst, macConverseInput]

/-- Markov chain `(messages) → (encoded inputs) → (outputs)` for the constructed ambient.
@audit:ok -/
lemma macConverse_isMarkovChain
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    IsMarkovChain (macConverseAmbient c W)
      (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω))
      (fun ω ↦ ((fun j ↦ c.encoder₁ (macConverseMsg₁ ω) j),
        (fun j ↦ c.encoder₂ (macConverseMsg₂ ω) j)))
      (fun ω j ↦ macConverseYs j ω) := by
  have h := isMarkovChain_of_compProd_encoder (M := Fin M₁ × Fin M₂)
    (Z := (Fin n → α₁) × (Fin n → α₂)) (Y := Fin n → β)
    (macConverseInput M₁ M₂)
    (fun m ↦ (c.encoder₁ m.1, c.encoder₂ m.2)) (measurable_of_countable _)
    (macConverseKernel c W) (macConverseCodeKernel W) (fun m ↦ rfl)
  exact h

/-- **MAC converse, from a bare code** (Gap 0 bridge).  For any two-user MAC block code `c` and
Markov channel `W`, the canonical ambient measure `macConverseAmbient c W` discharges every
hypothesis of the floating message-level converse `mac_converse`, so the rate pair
`(log M₁, log M₂)` lies in the corner-point region determined by the per-letter conditional and
joint mutual informations (still carrying the Fano slack, removed later in Gap A).
@audit:ok -/
theorem mac_converse_from_code
    [NeZero M₁] [NeZero M₂]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InMACCapacityRegion (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((∑ i : Fin n,
          condMutualInfo (macConverseAmbient c W)
              (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
              (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
              (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).1))
        + MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
              (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).1) * Real.log ((M₁ : ℝ) - 1))
      ((∑ i : Fin n,
          condMutualInfo (macConverseAmbient c W)
              (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
              (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
              (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).2))
        + MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
              (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).2) * Real.log ((M₂ : ℝ) - 1))
      ((∑ i : Fin n,
          mutualInfo (macConverseAmbient c W)
              (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i))
              (macConverseYs i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb (macConverseAmbient c W)
              (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω)
              c.decoder)
        + MeasureFano.errorProb (macConverseAmbient c W)
              (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω)
              c.decoder * Real.log (((M₁ * M₂ : ℕ) : ℝ) - 1)) := by
  exact mac_converse (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂ macConverseYs c
    measurable_macConverseMsg₁ measurable_macConverseMsg₂ measurable_macConverseYs
    (macConverseMsg₁_uniform c W) (macConverseMsg₂_uniform c W) (macConverseMsg₁₂_uniform c W)
    (macConverse_memorylessChannel c W) (macConverse_mutualInfo_eq_zero c W)
    (macConverse_isMarkovChain c W) hcard₁ hcard₂

end CodeToAmbient

section RateExtract

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open scoped ENNReal

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁]
    [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂]
    [MeasurableSingletonClass α₂] [StandardBorelSpace α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
    [MeasurableSingletonClass β] [StandardBorelSpace β]
variable {M₁ M₂ n : ℕ}

/-- If `⌈exp x⌉₊ ≤ M` then `x ≤ log M`: the block-length-to-rate atom.  `exp x ≤ ⌈exp x⌉₊ ≤ M`,
so taking logs (both sides positive) gives `x = log (exp x) ≤ log M`. -/
lemma le_log_of_ceil_exp_le {x : ℝ} {M : ℕ}
    (hM : Nat.ceil (Real.exp x) ≤ M) : x ≤ Real.log (M : ℝ) := by
  have h1 : Real.exp x ≤ (Nat.ceil (Real.exp x) : ℝ) := Nat.le_ceil _
  have h2 : ((Nat.ceil (Real.exp x) : ℕ) : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hM
  have h3 : Real.exp x ≤ (M : ℝ) := h1.trans h2
  calc x = Real.log (Real.exp x) := (Real.log_exp x).symm
    _ ≤ Real.log (M : ℝ) := Real.log_le_log (Real.exp_pos x) h3

/-- **Weak-converse finite-`n` rate extraction** (Gap A core).  For a fixed two-user block code
whose message counts satisfy `⌈exp (n R₁)⌉ ≤ M₁`, `⌈exp (n R₂)⌉ ≤ M₂`, chaining the code→ambient
converse `mac_converse_from_code` with `n Rⱼ ≤ log Mⱼ` moves the rate scaled by `n` inside the
corner-point region determined by the per-letter conditional/joint mutual informations plus the
Fano slack (still symbolic; the Fano→0 limit is the later CV step). -/
lemma mac_converse_rate_extract [NeZero M₁] [NeZero M₂]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) {R₁ R₂ : ℝ}
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂) :
    InMACCapacityRegion ((n : ℝ) * R₁) ((n : ℝ) * R₂)
      ((∑ i : Fin n,
          condMutualInfo (macConverseAmbient c W)
              (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
              (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
              (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).1))
        + MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
              (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).1) * Real.log ((M₁ : ℝ) - 1))
      ((∑ i : Fin n,
          condMutualInfo (macConverseAmbient c W)
              (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
              (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
              (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).2))
        + MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
              (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).2) * Real.log ((M₂ : ℝ) - 1))
      ((∑ i : Fin n,
          mutualInfo (macConverseAmbient c W)
              (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i))
              (macConverseYs i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb (macConverseAmbient c W)
              (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω)
              c.decoder)
        + MeasureFano.errorProb (macConverseAmbient c W)
              (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω)
              c.decoder * Real.log (((M₁ * M₂ : ℕ) : ℝ) - 1)) := by
  have h := mac_converse_from_code c W hcard₁ hcard₂
  have hlog₁ : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hlog₂ : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  exact ⟨hlog₁.trans h.bound₁, hlog₂.trans h.bound₂,
    (add_le_add hlog₁ hlog₂).trans h.boundSum⟩

/-- **Joint error-probability reconciliation** (Gap A error bridge).  The ambient *joint* decode
error under `macConverseAmbient c W` equals the code's average error probability: the ambient was
built as `uniform(messages) ⊗ per-letter product channel` precisely to model uniform-message
transmission, so its joint error event has probability `averageErrorProb`. -/
lemma mac_converse_ambient_errorProb_joint_eq
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    MeasureFano.errorProb (macConverseAmbient c W)
        (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω)
        c.decoder
      = (c.averageErrorProb W).toReal := by
  have hM : M₁ * M₂ ≠ 0 := Nat.mul_ne_zero (NeZero.ne M₁) (NeZero.ne M₂)
  set S : Set ((Fin M₁ × Fin M₂) × (Fin n → β)) := {ω | ω.1 ≠ c.decoder ω.2} with hS_def
  have hS_meas : MeasurableSet S := (Set.toFinite S).measurableSet
  -- the joint error event is the ambient set `{ω | ω.1 ≠ c.decoder ω.2}`
  have h_err : MeasureFano.errorProb (macConverseAmbient c W)
      (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω) c.decoder
      = (macConverseAmbient c W).real S := rfl
  -- each kernel fibre measures exactly the pointwise error probability
  have h_ker : ∀ m : Fin M₁ × Fin M₂,
      (macConverseKernel c W) m (Prod.mk m ⁻¹' S) = c.errorProbAt W m := by
    intro m
    have h_sec : Prod.mk m ⁻¹' S = c.errorEvent m := by
      ext y
      simp only [Set.mem_preimage, hS_def, Set.mem_setOf_eq, MACCode.mem_errorEvent]
      exact ne_comm
    rw [h_sec]
    rfl
  have h_measure : (macConverseAmbient c W) S = c.averageErrorProb W := by
    rw [macConverseAmbient, Measure.compProd_apply hS_meas]
    simp_rw [h_ker]
    rw [macConverseInput_eq, lintegral_smul_measure, lintegral_count, tsum_fintype,
      MACCode.averageErrorProb, if_neg hM, smul_eq_mul]
    congr 1
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
  rw [h_err, measureReal_def, h_measure]

/-- The ambient user-1 marginal decode error is at most the joint decode error: the event
`{msg₁ mis-decoded}` is contained in `{message pair mis-decoded}`. -/
lemma mac_converse_ambient_errorProb_user1_le
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
        (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω))
        (fun p ↦ (c.decoder p.2).1)
      ≤ MeasureFano.errorProb (macConverseAmbient c W)
        (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω)
        c.decoder := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hcontra
  exact hω (congrArg Prod.fst hcontra)

/-- The ambient user-2 marginal decode error is at most the joint decode error. -/
lemma mac_converse_ambient_errorProb_user2_le
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] :
    MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
        (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω))
        (fun p ↦ (c.decoder p.2).2)
      ≤ MeasureFano.errorProb (macConverseAmbient c W)
        (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω)
        c.decoder := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro hcontra
  exact hω (congrArg Prod.snd hcontra)

end RateExtract

section PerLetterInfo

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open scoped ENNReal

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁]
    [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂]
    [MeasurableSingletonClass α₂] [StandardBorelSpace α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
    [MeasurableSingletonClass β] [StandardBorelSpace β]
variable {M₁ M₂ n : ℕ}

/-- **Per-letter joint pushforward of a product-channel compProd.**  For an ambient
`ν ⊗ₘ κ` whose message-to-output kernel factors as the per-letter product
`κ m = ∏ⱼ W (x m j)`, the joint law of the `i`-th input-output pair `(x ω.1 i, ω.2 i)` is the
channel joint `(ν.map (· i ∘ x)) ⊗ₘ W`.  This is the `h_pair_eq` core of
`isMemorylessChannel_of_compProd_pi`, isolated as the single genuinely-new measure identity
behind Gap B′. -/
private lemma compProd_pi_map_pair_eq
    {M A B : Type*} [MeasurableSpace M] [MeasurableSpace A] [MeasurableSpace B]
    {k : ℕ} (ν : Measure M) [IsProbabilityMeasure ν]
    (x : M → Fin k → A) (hx : Measurable x)
    (W : Kernel A B) [IsMarkovKernel W]
    (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ]
    (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))) (i : Fin k) :
    (ν ⊗ₘ κ).map (fun ω ↦ (x ω.1 i, ω.2 i)) = (ν.map (fun m ↦ x m i)) ⊗ₘ W := by
  set μ : Measure (M × (Fin k → B)) := ν ⊗ₘ κ with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  set Zc : M × (Fin k → B) → A := fun ω ↦ x ω.1 i with hZc_def
  set Yo : M × (Fin k → B) → B := fun ω ↦ ω.2 i with hYo_def
  have hxi_meas : Measurable (fun m ↦ x m i) := (measurable_pi_apply i).comp hx
  have hZc_meas : Measurable Zc := hxi_meas.comp measurable_fst
  have hYo_meas : Measurable Yo := (measurable_pi_apply i).comp measurable_snd
  show μ.map (fun ω ↦ (Zc ω, Yo ω)) = (ν.map (fun m ↦ x m i)) ⊗ₘ W
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hFmeas : Measurable (fun ω : M × (Fin k → B) ↦ f (Zc ω, Yo ω)) :=
    hf.comp (hZc_meas.prodMk hYo_meas)
  have hFm2 : Measurable (fun z : A ↦ ∫⁻ b : B, f (z, b) ∂(W z)) :=
    Measurable.lintegral_kernel_prod_right' (κ := W) hf
  rw [lintegral_map hf (hZc_meas.prodMk hYo_meas), hμ_def,
    Measure.lintegral_compProd hFmeas, Measure.lintegral_compProd hf,
    lintegral_map hFm2 hxi_meas]
  refine lintegral_congr fun m ↦ ?_
  rw [hκ]
  exact lintegral_pi_eval (fun j ↦ W (x m j)) i (fun b ↦ f (x m i, b))
    (hf.comp (measurable_const.prodMk measurable_id))

/-- Mutual information is invariant under a shared pushforward of both random variables:
`I(f; g) = I(f ∘ T; g ∘ T)` when the pair law on `μ.map T` matches the pair law of the composed
variables on `μ`. -/
private lemma mutualInfo_map_comp
    {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure Ω) (T : Ω → Ω') (hT : Measurable T)
    (f : Ω' → A) (hf : Measurable f) (g : Ω' → B) (hg : Measurable g) :
    mutualInfo (μ.map T) f g = mutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω)) := by
  unfold mutualInfo
  rw [Measure.map_map (hf.prodMk hg) hT, Measure.map_map hf hT, Measure.map_map hg hT]
  rfl

/-- `condDistrib` is stable under a shared pushforward of the conditioning and conditioned
variables: `condDistrib f h (μ.map T) =ᵃ condDistrib (f ∘ T) (h ∘ T) μ` on the conditioning
marginal. -/
private lemma condDistrib_map_comp
    {Ω Ω' A C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace C]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω') (hT : Measurable T)
    (f : Ω' → A) (hf : Measurable f) (h : Ω' → C) (hh : Measurable h) :
    condDistrib f h (μ.map T)
      =ᵐ[(μ.map T).map h] condDistrib (fun ω ↦ f (T ω)) (fun ω ↦ h (T ω)) μ := by
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  refine condDistrib_ae_eq_of_measure_eq_compProd h hf.aemeasurable ?_
  rw [Measure.map_map (hh.prodMk hf) hT, Measure.map_map hh hT]
  exact (compProd_map_condDistrib (X := fun ω ↦ h (T ω)) (Y := fun ω ↦ f (T ω))
    (hf.comp hT).aemeasurable).symm

/-- Conditional mutual information is invariant under a shared pushforward of all three random
variables: `I(f; g | h) = I(f ∘ T; g ∘ T | h ∘ T)`. -/
private lemma condMutualInfo_map_comp
    {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω') (hT : Measurable T)
    (f : Ω' → A) (hf : Measurable f) (g : Ω' → B) (hg : Measurable g)
    (h : Ω' → C) (hh : Measurable h) :
    condMutualInfo (μ.map T) f g h
      = condMutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω)) (fun ω ↦ h (T ω)) := by
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hbase : (μ.map T).map h = μ.map (fun ω ↦ h (T ω)) := Measure.map_map hh hT
  have hpair := condDistrib_map_comp μ T hT (fun q ↦ (f q, g q)) (hf.prodMk hg) h hh
  have hf' := condDistrib_map_comp μ T hT f hf h hh
  have hg' := condDistrib_map_comp μ T hT g hg h hh
  have hprodk :
      (condDistrib f h (μ.map T)) ×ₖ (condDistrib g h (μ.map T))
        =ᵐ[(μ.map T).map h]
      (condDistrib (fun ω ↦ f (T ω)) (fun ω ↦ h (T ω)) μ)
        ×ₖ (condDistrib (fun ω ↦ g (T ω)) (fun ω ↦ h (T ω)) μ) := by
    filter_upwards [hf', hg'] with a haf hag
    ext s hs
    rw [Kernel.prod_apply, Kernel.prod_apply, haf, hag]
  rw [hbase] at hpair hprodk
  unfold condMutualInfo
  rw [hbase]
  congr 1
  · exact Measure.compProd_congr hpair
  · exact Measure.compProd_congr hprodk

/-- `condMutualInfo_map_comp` phrased against any measure `ρ` propositionally equal to `μ.map T`.
The equation hypothesis is substituted (transporting its `IsFiniteMeasure` instance), which sidesteps
the ill-typed motive of rewriting the measure argument of `condMutualInfo` directly. -/
private lemma condMutualInfo_map_comp'
    {Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω') (hT : Measurable T)
    (ρ : Measure Ω') [IsFiniteMeasure ρ] (hρ : ρ = μ.map T)
    (f : Ω' → A) (hf : Measurable f) (g : Ω' → B) (hg : Measurable g)
    (h : Ω' → C) (hh : Measurable h) :
    condMutualInfo ρ f g h
      = condMutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω)) (fun ω ↦ h (T ω)) := by
  subst hρ
  exact condMutualInfo_map_comp μ T hT f hf g hg h hh

/-- **Step 1 (Gap B′): per-letter joint law identification.**  Under the converse ambient
`macConverseAmbient c W`, the joint law of the `i`-th per-letter triple
`(X₁ᵢ, X₂ᵢ, Yᵢ)` equals the achievability per-coordinate joint `macJointDistribution p₁ᵢ p₂ᵢ W`
of the product of the per-letter input marginals `p₁ᵢ = μ.map X₁ᵢ`, `p₂ᵢ = μ.map X₂ᵢ`.  The two
inputs are independent (functions of the independent uniform messages), and the output is
conditionally `W`-distributed by the per-letter product-channel structure. -/
lemma macConverse_map_triple_eq
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    (macConverseAmbient c W).map
        (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i,
                  macConverseYs i ω))
      = macJointDistribution
          ((macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i))
          ((macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) W := by
  have hx : Measurable (fun (m : Fin M₁ × Fin M₂) (j : Fin n) ↦
      (c.encoder₁ m.1 j, c.encoder₂ m.2 j)) := measurable_of_countable _
  have hpairmeas : Measurable
      (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β) ↦
        ((c.encoder₁ ω.1.1 i, c.encoder₂ ω.1.2 i), ω.2 i)) := measurable_of_countable _
  -- per-letter input-output pair law
  have hpair : (macConverseAmbient c W).map
        (fun ω ↦ ((c.encoder₁ ω.1.1 i, c.encoder₂ ω.1.2 i), ω.2 i))
      = (macConverseInput M₁ M₂).map (fun m ↦ (c.encoder₁ m.1 i, c.encoder₂ m.2 i)) ⊗ₘ W := by
    rw [macConverseAmbient]
    exact compProd_pi_map_pair_eq (macConverseInput M₁ M₂)
      (fun m j ↦ (c.encoder₁ m.1 j, c.encoder₂ m.2 j)) hx W (macConverseKernel c W)
      (fun m ↦ rfl) i
  -- the per-letter input marginals are the product of the two message-encoder marginals
  have hmarg : (macConverseInput M₁ M₂).map (fun m ↦ (c.encoder₁ m.1 i, c.encoder₂ m.2 i))
      = ((macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)).prod
        ((macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) := by
    have hu1 : (macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)
        = ((Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count).map (fun m₁ ↦ c.encoder₁ m₁ i) := by
      rw [show (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β) ↦ c.encoder₁ (macConverseMsg₁ ω) i)
            = (fun m₁ ↦ c.encoder₁ m₁ i) ∘ macConverseMsg₁ from rfl,
          ← Measure.map_map (measurable_of_countable _) measurable_macConverseMsg₁,
          macConverseMsg₁_uniform c W]
    have hu2 : (macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)
        = ((Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count).map (fun m₂ ↦ c.encoder₂ m₂ i) := by
      rw [show (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β) ↦ c.encoder₂ (macConverseMsg₂ ω) i)
            = (fun m₂ ↦ c.encoder₂ m₂ i) ∘ macConverseMsg₂ from rfl,
          ← Measure.map_map (measurable_of_countable _) measurable_macConverseMsg₂,
          macConverseMsg₂_uniform c W]
    rw [hu1, hu2, macConverseInput,
        show (fun m : Fin M₁ × Fin M₂ ↦ (c.encoder₁ m.1 i, c.encoder₂ m.2 i))
          = Prod.map (fun m₁ ↦ c.encoder₁ m₁ i) (fun m₂ ↦ c.encoder₂ m₂ i) from rfl]
    exact (Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)).symm
  rw [show (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β) ↦
        (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i, macConverseYs i ω))
      = ⇑MeasurableEquiv.prodAssoc ∘
        (fun ω ↦ ((c.encoder₁ ω.1.1 i, c.encoder₂ ω.1.2 i), ω.2 i)) from rfl,
    ← Measure.map_map MeasurableEquiv.prodAssoc.measurable hpairmeas, hpair, hmarg]
  rfl

/-- **Per-letter identification, user 1** (Gap B′ deliverable).  The ambient per-letter
conditional mutual information `I(X₁ᵢ; Yᵢ | X₂ᵢ)` equals the achievability corner information
`macInfo₁` of the per-letter product input.  This rewrites the user-1 sum term of
`mac_converse_rate_extract` into `∑ᵢ macInfo₁ p₁ᵢ p₂ᵢ W`. -/
lemma mac_condMI_eq_macInfo₁_at
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    (condMutualInfo (macConverseAmbient c W)
        (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
        (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)).toReal
      = macInfo₁ ((macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i))
          ((macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) W := by
  haveI : IsProbabilityMeasure ((macConverseAmbient c W).map
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  haveI : IsProbabilityMeasure ((macConverseAmbient c W).map
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  rw [macInfo₁_eq_condMutualInfo_toReal]
  congr 1
  exact (condMutualInfo_map_comp' (macConverseAmbient c W)
    (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i,
              macConverseYs i ω)) (measurable_of_countable _)
    _ (macConverse_map_triple_eq c W i).symm
    Prod.fst measurable_fst (fun q ↦ q.2.2) measurable_snd.snd
    (fun q ↦ q.2.1) measurable_snd.fst).symm

/-- **Per-letter identification, user 2** (Gap B′ deliverable).  The ambient per-letter
conditional mutual information `I(X₂ᵢ; Yᵢ | X₁ᵢ)` equals `macInfo₂` of the per-letter product
input. -/
lemma mac_condMI_eq_macInfo₂_at
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    (condMutualInfo (macConverseAmbient c W)
        (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
        (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)).toReal
      = macInfo₂ ((macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i))
          ((macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) W := by
  haveI : IsProbabilityMeasure ((macConverseAmbient c W).map
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  haveI : IsProbabilityMeasure ((macConverseAmbient c W).map
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  rw [macInfo₂_eq_condMutualInfo_toReal]
  congr 1
  exact (condMutualInfo_map_comp' (macConverseAmbient c W)
    (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i,
              macConverseYs i ω)) (measurable_of_countable _)
    _ (macConverse_map_triple_eq c W i).symm
    (fun q ↦ q.2.1) measurable_snd.fst (fun q ↦ q.2.2) measurable_snd.snd
    Prod.fst measurable_fst).symm

/-- **Per-letter identification, sum corner** (Gap B′ deliverable).  The ambient per-letter
joint mutual information `I((X₁ᵢ, X₂ᵢ); Yᵢ)` equals `macInfoBoth` of the per-letter product
input. -/
lemma mac_mutualInfo_eq_macInfoBoth_at
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    (mutualInfo (macConverseAmbient c W)
        (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i))
        (macConverseYs i)).toReal
      = macInfoBoth ((macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i))
          ((macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) W := by
  haveI : IsProbabilityMeasure ((macConverseAmbient c W).map
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  haveI : IsProbabilityMeasure ((macConverseAmbient c W).map
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  rw [macInfoBoth_eq_mutualInfo_toReal]
  congr 1
  rw [← macConverse_map_triple_eq c W i,
    mutualInfo_map_comp (macConverseAmbient c W)
      (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i,
                macConverseYs i ω)) (measurable_of_countable _)
      (fun q ↦ (q.1, q.2.1)) (measurable_fst.prodMk measurable_snd.fst)
      (fun q ↦ q.2.2) measurable_snd.snd]

end PerLetterInfo

/-! ### CV assembly (Dispatch B): Fano→0 limit + point construction + axis casework

The converse-half headline `mac_timesharing_converse`.  An achievable rate pair `(R₁, R₂)` in the
first quadrant lies in the closed convex hull of the union of all per-input pentagons.  The core is
the interior case `0 < R₁`, `0 < R₂`: for a sequence of block codes with error `→ 0` and length
`→ ∞`, the uniformly-shrunk rate point `(R₁(1−Pe) − log2/n, R₂(1−Pe) − log2/n)` lies in the hull
(per-code, via the geometric gateway `mac_avgPentagon_mem_convexHull`), and converges to `(R₁, R₂)`,
which is therefore in the *closed* hull. -/

section CVAssembly

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open Filter
open scoped ENNReal Topology

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁]
    [MeasurableSingletonClass α₁] [StandardBorelSpace α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂]
    [MeasurableSingletonClass α₂] [StandardBorelSpace α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β]
    [MeasurableSingletonClass β] [StandardBorelSpace β]
variable {M₁ M₂ n : ℕ}

/-- Per-letter mutual-information superadditivity under input independence (Dispatch A deliverable).
`I((X₁, X₂); Y) ≤ I(X₁; Y | X₂) + I(X₂; Y | X₁)`.  This is the `hsub` well-formedness hypothesis of
`mac_avgPentagon_mem_convexHull`; it is a universal geometric fact about the product input, threaded
here exactly like the existing `hac`/`hbc` corners `mac_macInfo₁/₂_le_macInfoBoth`.
Proved by the two chain-rule decompositions `I((X₁, X₂); Y) = I(X₂; Y) + I(X₁; Y | X₂)` and the
identity `I(X₂; Y | X₁) = I(X₂; Y) + I(X₁; X₂ | Y)` (the `I(X₁; X₂) = 0` term drops under the
independent product input), so `I(X₂; Y) ≤ I(X₂; Y | X₁)` and the claim follows. -/
lemma mac_perletter_superadd (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂] (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    macInfoBoth p₁ p₂ W ≤ macInfo₁ p₁ p₂ W + macInfo₂ p₁ p₂ W := by
  have hX1 : Measurable (Prod.fst : α₁ × α₂ × β → α₁) := measurable_fst
  have hX2 : Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) := measurable_fst.comp measurable_snd
  have hY : Measurable (fun q : α₁ × α₂ × β ↦ q.2.2) := measurable_snd.comp measurable_snd
  rw [macInfoBoth_eq_mutualInfo_toReal p₁ p₂ W, macInfo₁_eq_condMutualInfo_toReal p₁ p₂ W,
      macInfo₂_eq_condMutualInfo_toReal p₁ p₂ W]
  set J := macJointDistribution p₁ p₂ W with hJ
  -- Finiteness of the two corner informations.
  have hC1_ne : condMutualInfo J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1) ≠ ∞ :=
    condMutualInfo_ne_top J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1) hX1 hY hX2
  have hC2_ne : condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst ≠ ∞ :=
    condMutualInfo_ne_top J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst hX2 hY hX1
  -- Independence of the two inputs under the product law `p₁ ⊗ p₂`.
  have indep0 : mutualInfo J Prod.fst (fun q : α₁ × α₂ × β ↦ q.2.1) = 0 :=
    macJoint_mutualInfo_X1_X2_eq_zero p₁ p₂ W
  -- Chain-rule decomposition A: `I((X₁, X₂); Y) = I(X₂; Y) + I(X₁; Y | X₂)`.
  have heqA1 : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) (fun q ↦ q.2.2)
      = mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.1, q.1)) (fun q ↦ q.2.2) :=
    mutualInfo_map_left_measurableEquiv J (fun q : α₁ × α₂ × β ↦ (q.2.1, q.1))
      (fun q ↦ q.2.2) (hX2.prodMk hX1) hY MeasurableEquiv.prodComm
  have hchainA : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.1, q.1)) (fun q ↦ q.2.2)
      = mutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2)
        + condMutualInfo J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1) :=
    mutualInfo_chain_rule J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1) hX1 hY hX2
  have decompA := heqA1.trans hchainA
  -- Reshaping and chain rules feeding `I(X₂; Y) ≤ I(X₂; Y | X₁)`.
  have reshapeE : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.1, q.2.2)) (fun q ↦ q.2.1)
      = mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.2, q.1)) (fun q ↦ q.2.1) :=
    mutualInfo_map_left_measurableEquiv J (fun q : α₁ × α₂ × β ↦ (q.2.2, q.1))
      (fun q ↦ q.2.1) (hY.prodMk hX1) hX2 MeasurableEquiv.prodComm
  -- `I((X₁, Y); X₂) = I(X₁; X₂) + I(Y; X₂ | X₁)`.
  have chainB : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.1, q.2.2)) (fun q ↦ q.2.1)
      = mutualInfo J Prod.fst (fun q ↦ q.2.1)
        + condMutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst :=
    mutualInfo_chain_rule J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst hY hX2 hX1
  -- `I((Y, X₁); X₂) = I(Y; X₂) + I(X₁; X₂ | Y)`.
  have chainD : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.2, q.1)) (fun q ↦ q.2.1)
      = mutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1)
        + condMutualInfo J Prod.fst (fun q ↦ q.2.1) (fun q ↦ q.2.2) :=
    mutualInfo_chain_rule J Prod.fst (fun q ↦ q.2.1) (fun q ↦ q.2.2) hX1 hX2 hY
  -- `I((Y, X₁); X₂) = I(Y; X₂ | X₁)` (the `I(X₁; X₂) = 0` term drops out).
  have e2 : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.2.2, q.1)) (fun q ↦ q.2.1)
      = condMutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst := by
    rw [← reshapeE, chainB, indep0, zero_add]
  -- `I(Y; X₂ | X₁) = I(Y; X₂) + I(X₁; X₂ | Y)`.
  have hCMI : condMutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst
      = mutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1)
        + condMutualInfo J Prod.fst (fun q ↦ q.2.1) (fun q ↦ q.2.2) := by
    rw [← e2, chainD]
  -- Commute to `I(X₂; Y | X₁)` (the `macInfo₂` corner form).
  have commC2 : condMutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst
      = condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst :=
    condMutualInfo_comm J (fun q ↦ q.2.2) (fun q ↦ q.2.1) Prod.fst hY hX2 hX1
  have hC2 : condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst
      = mutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1)
        + condMutualInfo J Prod.fst (fun q ↦ q.2.1) (fun q ↦ q.2.2) := by
    rw [← commC2, hCMI]
  -- Conditioning increases mutual information under independence: `I(X₂; Y) ≤ I(X₂; Y | X₁)`.
  have comm2 : mutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2)
      = mutualInfo J (fun q ↦ q.2.2) (fun q ↦ q.2.1) :=
    mutualInfo_comm J (fun q ↦ q.2.1) (fun q ↦ q.2.2) hX2 hY
  have hSub : mutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2)
      ≤ condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst := by
    rw [hC2, comm2]
    exact self_le_add_right _ _
  -- Assemble: `I((X₁, X₂); Y) = I(X₂; Y) + I(X₁; Y | X₂) ≤ I(X₁; Y | X₂) + I(X₂; Y | X₁)`.
  have hMBle : mutualInfo J (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) (fun q ↦ q.2.2)
      ≤ condMutualInfo J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1)
        + condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst := by
    rw [decompA, add_comm (condMutualInfo J Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1))
        (condMutualInfo J (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst)]
    gcongr
  rw [← ENNReal.toReal_add hC1_ne hC2_ne]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hC1_ne, hC2_ne⟩) hMBle

/-- Nonnegativity of the corner information `macInfo₁` for probability inputs. -/
lemma macInfo₁_nonneg (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂] (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    0 ≤ macInfo₁ p₁ p₂ W := by
  rw [macInfo₁_eq_condMutualInfo_toReal]; exact ENNReal.toReal_nonneg

/-- Nonnegativity of the corner information `macInfo₂` for probability inputs. -/
lemma macInfo₂_nonneg (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂] (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    0 ≤ macInfo₂ p₁ p₂ W := by
  rw [macInfo₂_eq_condMutualInfo_toReal]; exact ENNReal.toReal_nonneg

/-- Nonnegativity of the corner information `macInfoBoth` for probability inputs. -/
lemma macInfoBoth_nonneg (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂] (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    0 ≤ macInfoBoth p₁ p₂ W := by
  rw [macInfoBoth_eq_mutualInfo_toReal]; exact ENNReal.toReal_nonneg

/-- **Per-code shrunk-point membership** (Dispatch B analytic core).  For a length-`n` two-user code
with `2 ≤ M₁`, `2 ≤ M₂` and `⌈exp (n Rⱼ)⌉ ≤ Mⱼ`, if the uniformly-shrunk rate point
`(R₁(1−Pe) − log2/n, R₂(1−Pe) − log2/n)` (with `Pe` the average error probability) is in the first
quadrant, then it lies in the closed convex hull of all per-input pentagons.  Combines the finite-`n`
Fano bounds with the geometric gateway `mac_avgPentagon_mem_convexHull` and the per-letter
identification of Gap B′. -/
lemma mac_converse_shrunk_point_mem
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂)
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
    (hx1 : 0 ≤ R₁ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ))
    (hx2 : 0 ≤ R₂ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ)) :
    (R₁ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ),
     R₂ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  haveI : NeZero M₁ := ⟨by omega⟩
  haveI : NeZero M₂ := ⟨by omega⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hM₁R : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hcard₁
  have hM₂R : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hcard₂
  have hM₁ne : (M₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hM₂ne : (M₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- the finite-`n` converse from the code
  have h := mac_converse_from_code c W hcard₁ hcard₂
  -- per-letter product-input marginals
  set p₁ : Fin n → Measure α₁ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) with hp₁def
  set p₂ : Fin n → Measure α₂ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) with hp₂def
  have hp₁prob : ∀ i, IsProbabilityMeasure (p₁ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hp₂prob : ∀ i, IsProbabilityMeasure (p₂ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  -- abbreviate the average error and the three symbolic per-letter information sums
  set Pe := (c.averageErrorProb W).toReal with hPeDef
  set Pe₁ := MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
    (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω)) (fun p ↦ (c.decoder p.2).1) with hPe₁def
  set Pe₂ := MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
    (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω)) (fun p ↦ (c.decoder p.2).2) with hPe₂def
  set S₁ := (∑ i : Fin n, condMutualInfo (macConverseAmbient c W)
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)).toReal with hS₁def
  set S₂ := (∑ i : Fin n, condMutualInfo (macConverseAmbient c W)
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)).toReal with hS₂def
  set Sb := (∑ i : Fin n, mutualInfo (macConverseAmbient c W)
      (fun ω ↦ (c.encoder₁ (macConverseMsg₁ ω) i, c.encoder₂ (macConverseMsg₂ ω) i))
      (macConverseYs i)).toReal with hSbdef
  -- the joint decode error equals the code's average error probability `Pe`
  have hjoint : MeasureFano.errorProb (macConverseAmbient c W)
      (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω) c.decoder = Pe :=
    mac_converse_ambient_errorProb_joint_eq c W
  -- error-probability bounds
  have hPe_0 : 0 ≤ Pe := ENNReal.toReal_nonneg
  have hPe_1 : Pe ≤ 1 := by rw [← hjoint]; exact measureReal_le_one
  have hPe1_0 : 0 ≤ Pe₁ := measureReal_nonneg
  have hPe1_1 : Pe₁ ≤ 1 := measureReal_le_one
  have hPe1_le : Pe₁ ≤ Pe := (mac_converse_ambient_errorProb_user1_le c W).trans (le_of_eq hjoint)
  have hPe2_0 : 0 ≤ Pe₂ := measureReal_nonneg
  have hPe2_1 : Pe₂ ≤ 1 := measureReal_le_one
  have hPe2_le : Pe₂ ≤ Pe := (mac_converse_ambient_errorProb_user2_le c W).trans (le_of_eq hjoint)
  -- log-slack pieces
  have hnR1 : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hnR2 : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  have hlogm1 : Real.log ((M₁ : ℝ) - 1) ≤ Real.log (M₁ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogm2 : Real.log ((M₂ : ℝ) - 1) ≤ Real.log (M₂ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2n_nonneg : 0 ≤ Real.log 2 / (n : ℝ) :=
    div_nonneg (le_of_lt (Real.log_pos (by norm_num))) (le_of_lt hn')
  -- user-1 clean Fano bound: `R₁(1-Pe) - log2/n ≤ S₁/n`
  have hbound1 : R₁ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ S₁ / (n : ℝ) := by
    have hb1 := h.bound₁
    have hbe1 : Real.binEntropy Pe₁ ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hprod1 : Pe₁ * Real.log ((M₁ : ℝ) - 1) ≤ Pe₁ * Real.log (M₁ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogm1 hPe1_0
    have hstep1 : Real.log (M₁ : ℝ) * (1 - Pe₁) ≤ S₁ + Real.log 2 := by
      have e : Real.log (M₁ : ℝ) * (1 - Pe₁) = Real.log (M₁ : ℝ) - Pe₁ * Real.log (M₁ : ℝ) := by ring
      rw [e]; linarith [hb1, hbe1, hprod1]
    have hstep2 : (n : ℝ) * R₁ * (1 - Pe₁) ≤ Real.log (M₁ : ℝ) * (1 - Pe₁) :=
      mul_le_mul_of_nonneg_right hnR1 (by linarith)
    have hstep3 : (n : ℝ) * R₁ * (1 - Pe) ≤ (n : ℝ) * R₁ * (1 - Pe₁) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg n) hR₁)
    have key1 : (n : ℝ) * R₁ * (1 - Pe) ≤ S₁ + Real.log 2 := hstep3.trans (hstep2.trans hstep1)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn',
      show R₁ * (1 - Pe) * (n : ℝ) = (n : ℝ) * R₁ * (1 - Pe) from by ring]
    exact key1
  -- user-2 clean Fano bound: `R₂(1-Pe) - log2/n ≤ S₂/n`
  have hbound2 : R₂ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ S₂ / (n : ℝ) := by
    have hb2 := h.bound₂
    have hbe2 : Real.binEntropy Pe₂ ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hprod2 : Pe₂ * Real.log ((M₂ : ℝ) - 1) ≤ Pe₂ * Real.log (M₂ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogm2 hPe2_0
    have hstep1 : Real.log (M₂ : ℝ) * (1 - Pe₂) ≤ S₂ + Real.log 2 := by
      have e : Real.log (M₂ : ℝ) * (1 - Pe₂) = Real.log (M₂ : ℝ) - Pe₂ * Real.log (M₂ : ℝ) := by ring
      rw [e]; linarith [hb2, hbe2, hprod2]
    have hstep2 : (n : ℝ) * R₂ * (1 - Pe₂) ≤ Real.log (M₂ : ℝ) * (1 - Pe₂) :=
      mul_le_mul_of_nonneg_right hnR2 (by linarith)
    have hstep3 : (n : ℝ) * R₂ * (1 - Pe) ≤ (n : ℝ) * R₂ * (1 - Pe₂) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg n) hR₂)
    have key2 : (n : ℝ) * R₂ * (1 - Pe) ≤ S₂ + Real.log 2 := hstep3.trans (hstep2.trans hstep1)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn',
      show R₂ * (1 - Pe) * (n : ℝ) = (n : ℝ) * R₂ * (1 - Pe) from by ring]
    exact key2
  -- sum clean Fano bound: `(R₁+R₂)(1-Pe) - log2/n ≤ Sb/n`
  have hboundS : (R₁ + R₂) * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ Sb / (n : ℝ) := by
    have hbs := h.boundSum
    rw [hjoint] at hbs
    have hbeJ : Real.binEntropy Pe ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hge4 : (4 : ℝ) ≤ ((M₁ * M₂ : ℕ) : ℝ) := by exact_mod_cast Nat.mul_le_mul hcard₁ hcard₂
    have hlogJ : Real.log (((M₁ * M₂ : ℕ) : ℝ) - 1) ≤ Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ) := by
      rw [← Real.log_mul hM₁ne hM₂ne, ← Nat.cast_mul]
      exact Real.log_le_log (by linarith) (by linarith)
    have hprodJ : Pe * Real.log (((M₁ * M₂ : ℕ) : ℝ) - 1) ≤ Pe * (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogJ hPe_0
    have hnR12 : (n : ℝ) * (R₁ + R₂) ≤ Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ) := by
      have e : (n : ℝ) * (R₁ + R₂) = (n : ℝ) * R₁ + (n : ℝ) * R₂ := by ring
      rw [e]; linarith [hnR1, hnR2]
    have hstepS1 : (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) * (1 - Pe) ≤ Sb + Real.log 2 := by
      have e : (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) * (1 - Pe)
          = (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) - Pe * (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) := by
        ring
      rw [e]; linarith [hbs, hbeJ, hprodJ]
    have hstepS2 : (n : ℝ) * (R₁ + R₂) * (1 - Pe) ≤ (Real.log (M₁ : ℝ) + Real.log (M₂ : ℝ)) * (1 - Pe) :=
      mul_le_mul_of_nonneg_right hnR12 (by linarith)
    have keyS : (n : ℝ) * (R₁ + R₂) * (1 - Pe) ≤ Sb + Real.log 2 := hstepS2.trans hstepS1
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn',
      show (R₁ + R₂) * (1 - Pe) * (n : ℝ) = (n : ℝ) * (R₁ + R₂) * (1 - Pe) from by ring]
    exact keyS
  -- identify the symbolic sums with the per-letter `macInfo` sums (Gap B′): distribute `.toReal`
  -- over the finite sum (each term finite on the finite alphabets) and apply the per-letter values
  have hSm1 : S₁ = ∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W := by
    rw [hS₁def, ENNReal.toReal_sum (fun i _ => condMutualInfo_ne_top _ _ _ _
      (measurable_of_countable _) (measurable_of_countable _) (measurable_of_countable _))]
    exact Finset.sum_congr rfl (fun i _ => mac_condMI_eq_macInfo₁_at c W i)
  have hSm2 : S₂ = ∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W := by
    rw [hS₂def, ENNReal.toReal_sum (fun i _ => condMutualInfo_ne_top _ _ _ _
      (measurable_of_countable _) (measurable_of_countable _) (measurable_of_countable _))]
    exact Finset.sum_congr rfl (fun i _ => mac_condMI_eq_macInfo₂_at c W i)
  have hSmb : Sb = ∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W := by
    rw [hSbdef, ENNReal.toReal_sum (fun i _ => mutualInfo_ne_top _ _ _
      (measurable_of_countable _) (measurable_of_countable _))]
    exact Finset.sum_congr rfl (fun i _ => mac_mutualInfo_eq_macInfoBoth_at c W i)
  -- the gateway hypotheses in `macInfo` form
  have h1 : R₁ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ (∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W) / (n : ℝ) :=
    hSm1 ▸ hbound1
  have h2 : R₂ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ (∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W) / (n : ℝ) :=
    hSm2 ▸ hbound2
  have hs : (R₁ * (1 - Pe) - Real.log 2 / (n : ℝ)) + (R₂ * (1 - Pe) - Real.log 2 / (n : ℝ))
      ≤ (∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W) / (n : ℝ) := by
    have hboundS' : (R₁ + R₂) * (1 - Pe) - Real.log 2 / (n : ℝ)
        ≤ (∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W) / (n : ℝ) := hSmb ▸ hboundS
    calc (R₁ * (1 - Pe) - Real.log 2 / (n : ℝ)) + (R₂ * (1 - Pe) - Real.log 2 / (n : ℝ))
        = (R₁ + R₂) * (1 - Pe) - 2 * (Real.log 2 / (n : ℝ)) := by ring
      _ ≤ (R₁ + R₂) * (1 - Pe) - Real.log 2 / (n : ℝ) := by linarith
      _ ≤ (∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W) / (n : ℝ) := hboundS'
  -- geometric gateway
  have hmem : (R₁ * (1 - Pe) - Real.log 2 / (n : ℝ), R₂ * (1 - Pe) - Real.log 2 / (n : ℝ))
      ∈ convexHull ℝ (⋃ i : Fin n,
          ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
            ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
           : Set (ℝ × ℝ))) :=
    mac_avgPentagon_mem_convexHull hn
      (fun i => macInfo₁ (p₁ i) (p₂ i) W) (fun i => macInfo₂ (p₁ i) (p₂ i) W)
      (fun i => macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₁_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₂_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₁_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₂_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_perletter_superadd (p₁ i) (p₂ i) W)
      hx1 hx2 h1 h2 hs
  -- reindex the raw per-letter union into the master probability-input union
  have hsubset : (⋃ i : Fin n,
        ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
          ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
         : Set (ℝ × ℝ)))
      ⊆ (⋃ (q₁ : Measure α₁) (q₂ : Measure α₂)
          (_ : IsProbabilityMeasure q₁) (_ : IsProbabilityMeasure q₂), macPentagon q₁ q₂ W) := by
    intro pt hpt
    rw [Set.mem_iUnion] at hpt
    obtain ⟨i, hi⟩ := hpt
    haveI := hp₁prob i; haveI := hp₂prob i
    simp only [Set.mem_iUnion]
    exact ⟨p₁ i, p₂ i, hp₁prob i, hp₂prob i, hi⟩
  exact convexHull_subset_closedConvexHull (convexHull_mono hsubset hmem)

/-- **Interior case** of the converse: for strictly positive rates, an achievable pair lies in the
closed convex hull of the per-input pentagons. -/
lemma mac_timesharing_converse_interior (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hach : MACAchievable W R₁ R₂) :
    (R₁, R₂) ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
        (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  -- for each `k`, extract a length-`nₖ ≥ k+1` code with `2 ≤ M₁, M₂` and error `< 1/(k+1)`
  have hex : ∀ k : ℕ, ∃ (nn m₁ m₂ : ℕ) (c : MACCode m₁ m₂ nn α₁ α₂ β),
      0 < nn ∧ 2 ≤ m₁ ∧ 2 ≤ m₂ ∧ (k : ℝ) + 1 ≤ (nn : ℝ)
        ∧ Nat.ceil (Real.exp ((nn : ℝ) * R₁)) ≤ m₁ ∧ Nat.ceil (Real.exp ((nn : ℝ) * R₂)) ≤ m₂
        ∧ (c.averageErrorProb W).toReal < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨N, hN⟩ := hach (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨m₁, m₂, hm₁, hm₂, c, hPe⟩ := hN (max N (k + 1)) (le_max_left _ _)
    have hnnpos : 0 < max N (k + 1) := lt_of_lt_of_le (Nat.succ_pos k) (le_max_right _ _)
    have hnge : (k : ℝ) + 1 ≤ ((max N (k + 1) : ℕ) : ℝ) := by
      have hle : k + 1 ≤ max N (k + 1) := le_max_right _ _
      calc (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((max N (k + 1) : ℕ) : ℝ) := by exact_mod_cast hle
    have hcard : ∀ R : ℝ, 0 < R → ∀ M : ℕ, Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R)) ≤ M
        → 2 ≤ M := by
      intro R hR M hM
      have hpos : (0 : ℝ) < ((max N (k + 1) : ℕ) : ℝ) * R := mul_pos (by exact_mod_cast hnnpos) hR
      have h1lt : (1 : ℝ) < Real.exp (((max N (k + 1) : ℕ) : ℝ) * R) := by
        rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]; exact Real.exp_lt_exp.mpr hpos
      have h1c : (1 : ℝ) < (Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R)) : ℝ) :=
        lt_of_lt_of_le h1lt (Nat.le_ceil _)
      have : 1 < Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R)) := by exact_mod_cast h1c
      omega
    exact ⟨max N (k + 1), m₁, m₂, c, hnnpos, hcard R₁ hR₁ m₁ hm₁, hcard R₂ hR₂ m₂ hm₂, hnge,
      hm₁, hm₂, hPe⟩
  choose nn m₁ m₂ c hnpos hcard₁ hcard₂ hnge hM₁ hM₂ hPe using hex
  -- the average error probabilities converge to `0`, hence so does `log2/nₖ`
  have hPe0 : Tendsto (fun k => ((c k).averageErrorProb W).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun k => (hPe k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hnn_top : Tendsto (fun k => (nn k : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => le_trans (by linarith) (hnge k)) tendsto_natCast_atTop_atTop
  have hlog0 : Tendsto (fun k => Real.log 2 / (nn k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hnn_top
  -- each coordinate of the shrunk-rate sequence converges to `Rⱼ`
  have hf1 : Tendsto (fun k => R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      atTop (𝓝 R₁) := by
    have hlim : Tendsto (fun k => R₁ * (1 - ((c k).averageErrorProb W).toReal)
        - Real.log 2 / (nn k : ℝ)) atTop (𝓝 (R₁ * (1 - 0) - 0)) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hPe0)).sub hlog0
    simpa using hlim
  have hf2 : Tendsto (fun k => R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      atTop (𝓝 R₂) := by
    have hlim : Tendsto (fun k => R₂ * (1 - ((c k).averageErrorProb W).toReal)
        - Real.log 2 / (nn k : ℝ)) atTop (𝓝 (R₂ * (1 - 0) - 0)) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hPe0)).sub hlog0
    simpa using hlim
  have htend : Tendsto (fun k => (R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ),
      R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))) atTop (𝓝 (R₁, R₂)) :=
    hf1.prodMk_nhds hf2
  -- eventually the shrunk point is in the first quadrant
  have hpos1 : ∀ᶠ k in atTop, 0 ≤ R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ) := by
    filter_upwards [hf1.eventually (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hR₁))] with k hk
    exact le_of_lt hk
  have hpos2 : ∀ᶠ k in atTop, 0 ≤ R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ) := by
    filter_upwards [hf2.eventually (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hR₂))] with k hk
    exact le_of_lt hk
  -- eventually the shrunk point lies in the closed convex hull (via the per-code lemma)
  have hev : ∀ᶠ k in atTop, (R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ),
      R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
    filter_upwards [hpos1, hpos2] with k hk1 hk2
    exact mac_converse_shrunk_point_mem (c k) W (hnpos k) (hcard₁ k) (hcard₂ k) hR₁.le hR₂.le
      (hM₁ k) (hM₂ k) hk1 hk2
  exact isClosed_closedConvexHull.mem_of_tendsto htend hev

/-- **User-1 finite-`n` Fano corner bound** (axis extract).  Extracts the single user-1 corner
inequality `log |M₁| ≤ ∑ᵢ I(X₁ᵢ; Yᵢ | X₂ᵢ) + h(Pe₁) + Pe₁ log(|M₁| − 1)` directly from
`mac_converse_bound₁` and `mac_singleletterize_bound₁` on the canonical ambient measure, *without*
routing through the two-user `mac_converse_from_code`.  Requires only `2 ≤ M₁`; user 2 enters only
through `NeZero M₂`, so this survives the `M₂ = 1` axis degeneracy that blocks the joint converse. -/
lemma mac_converse_from_code_bound₁
    [NeZero M₁] [NeZero M₂]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) :
    Real.log (M₁ : ℝ) ≤
      (∑ i : Fin n,
          condMutualInfo (macConverseAmbient c W)
              (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
              (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
              (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).1))
        + MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
              (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).1) * Real.log ((M₁ : ℝ) - 1) := by
  have hbound := mac_converse_bound₁ (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂
    macConverseYs c measurable_macConverseMsg₁ measurable_macConverseMsg₂ measurable_macConverseYs
    (macConverseMsg₁_uniform c W) hcard₁
  have hsingle := mac_singleletterize_bound₁ (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂
    macConverseYs c measurable_macConverseMsg₁ measurable_macConverseMsg₂ measurable_macConverseYs
    (macConverse_memorylessChannel c W) (macConverse_mutualInfo_eq_zero c W)
    (macConverse_isMarkovChain c W)
  have hfin : (∑ i : Fin n,
      condMutualInfo (macConverseAmbient c W)
        (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
        (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)) ≠ ∞ :=
    (ENNReal.sum_lt_top.mpr fun i _ =>
      (condMutualInfo_ne_top _ _ _ _ (measurable_of_countable _) (measurable_of_countable _)
        (measurable_of_countable _)).lt_top).ne
  have hle := ENNReal.toReal_mono hfin hsingle
  linarith [hbound, hle]

/-- **User-2 finite-`n` Fano corner bound** (axis extract).  Symmetric to
`mac_converse_from_code_bound₁`: requires only `2 ≤ M₂`, surviving the `M₁ = 1` axis degeneracy. -/
lemma mac_converse_from_code_bound₂
    [NeZero M₁] [NeZero M₂]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hcard₂ : 2 ≤ M₂) :
    Real.log (M₂ : ℝ) ≤
      (∑ i : Fin n,
          condMutualInfo (macConverseAmbient c W)
              (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
              (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)).toReal
        + Real.binEntropy
            (MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
              (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).2))
        + MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
              (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω))
              (fun p ↦ (c.decoder p.2).2) * Real.log ((M₂ : ℝ) - 1) := by
  have hbound := mac_converse_bound₂ (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂
    macConverseYs c measurable_macConverseMsg₁ measurable_macConverseMsg₂ measurable_macConverseYs
    (macConverseMsg₂_uniform c W) hcard₂
  have hsingle := mac_singleletterize_bound₂ (macConverseAmbient c W) macConverseMsg₁ macConverseMsg₂
    macConverseYs c measurable_macConverseMsg₁ measurable_macConverseMsg₂ measurable_macConverseYs
    (macConverse_memorylessChannel c W) (macConverse_mutualInfo_eq_zero c W)
    (macConverse_isMarkovChain c W)
  have hfin : (∑ i : Fin n,
      condMutualInfo (macConverseAmbient c W)
        (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
        (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)) ≠ ∞ :=
    (ENNReal.sum_lt_top.mpr fun i _ =>
      (condMutualInfo_ne_top _ _ _ _ (measurable_of_countable _) (measurable_of_countable _)
        (measurable_of_countable _)).lt_top).ne
  have hle := ENNReal.toReal_mono hfin hsingle
  linarith [hbound, hle]

/-- **Per-code shrunk-point membership, axis user 1** (`R₂ = 0`).  Trimmed copy of
`mac_converse_shrunk_point_mem` for the axis point `(R₁(1−Pe) − log2/n, 0)`: uses only the user-1
Fano bound (`mac_converse_from_code_bound₁`, needing just `2 ≤ M₁`) plus per-letter nonnegativity, so
it survives the `M₂ = 1` degeneracy. -/
lemma mac_converse_shrunk_point_mem_axis1 [NeZero M₂]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁)
    {R₁ : ℝ} (hR₁ : 0 ≤ R₁)
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hx1 : 0 ≤ R₁ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ)) :
    (R₁ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ), (0 : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  haveI : NeZero M₁ := ⟨by omega⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hM₁R : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hcard₁
  -- per-letter product-input marginals
  set p₁ : Fin n → Measure α₁ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) with hp₁def
  set p₂ : Fin n → Measure α₂ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) with hp₂def
  have hp₁prob : ∀ i, IsProbabilityMeasure (p₁ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hp₂prob : ∀ i, IsProbabilityMeasure (p₂ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  -- abbreviate the average error, the user-1 marginal error, and the user-1 information sum
  set Pe := (c.averageErrorProb W).toReal with hPeDef
  set Pe₁ := MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₁
    (fun ω ↦ (macConverseMsg₂ ω, fun i ↦ macConverseYs i ω)) (fun p ↦ (c.decoder p.2).1) with hPe₁def
  set S₁ := (∑ i : Fin n, condMutualInfo (macConverseAmbient c W)
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) (macConverseYs i)
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i)).toReal with hS₁def
  -- the joint decode error equals the code's average error probability `Pe`
  have hjoint : MeasureFano.errorProb (macConverseAmbient c W)
      (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω) c.decoder = Pe :=
    mac_converse_ambient_errorProb_joint_eq c W
  have hPe_0 : 0 ≤ Pe := ENNReal.toReal_nonneg
  have hPe_1 : Pe ≤ 1 := by rw [← hjoint]; exact measureReal_le_one
  have hPe1_0 : 0 ≤ Pe₁ := measureReal_nonneg
  have hPe1_1 : Pe₁ ≤ 1 := measureReal_le_one
  have hPe1_le : Pe₁ ≤ Pe := (mac_converse_ambient_errorProb_user1_le c W).trans (le_of_eq hjoint)
  have hnR1 : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hlogm1 : Real.log ((M₁ : ℝ) - 1) ≤ Real.log (M₁ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2n_nonneg : 0 ≤ Real.log 2 / (n : ℝ) :=
    div_nonneg (le_of_lt (Real.log_pos (by norm_num))) (le_of_lt hn')
  -- user-1 clean Fano bound: `R₁(1-Pe) - log2/n ≤ S₁/n`
  have hbound1 : R₁ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ S₁ / (n : ℝ) := by
    have hb1 := mac_converse_from_code_bound₁ c W hcard₁
    have hbe1 : Real.binEntropy Pe₁ ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hprod1 : Pe₁ * Real.log ((M₁ : ℝ) - 1) ≤ Pe₁ * Real.log (M₁ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogm1 hPe1_0
    have hstep1 : Real.log (M₁ : ℝ) * (1 - Pe₁) ≤ S₁ + Real.log 2 := by
      have e : Real.log (M₁ : ℝ) * (1 - Pe₁) = Real.log (M₁ : ℝ) - Pe₁ * Real.log (M₁ : ℝ) := by ring
      rw [e]; linarith [hb1, hbe1, hprod1]
    have hstep2 : (n : ℝ) * R₁ * (1 - Pe₁) ≤ Real.log (M₁ : ℝ) * (1 - Pe₁) :=
      mul_le_mul_of_nonneg_right hnR1 (by linarith)
    have hstep3 : (n : ℝ) * R₁ * (1 - Pe) ≤ (n : ℝ) * R₁ * (1 - Pe₁) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg n) hR₁)
    have key1 : (n : ℝ) * R₁ * (1 - Pe) ≤ S₁ + Real.log 2 := hstep3.trans (hstep2.trans hstep1)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn',
      show R₁ * (1 - Pe) * (n : ℝ) = (n : ℝ) * R₁ * (1 - Pe) from by ring]
    exact key1
  -- identify the user-1 sum with the per-letter `macInfo₁` sum (Gap B′)
  have hSm1 : S₁ = ∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W := by
    rw [hS₁def, ENNReal.toReal_sum (fun i _ => condMutualInfo_ne_top _ _ _ _
      (measurable_of_countable _) (measurable_of_countable _) (measurable_of_countable _))]
    exact Finset.sum_congr rfl (fun i _ => mac_condMI_eq_macInfo₁_at c W i)
  have h1 : R₁ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ (∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W) / (n : ℝ) :=
    hSm1 ▸ hbound1
  -- second coordinate is `0`, so the user-2 and sum gateway bounds are nonnegativity / user-1 chained
  have h2 : (0 : ℝ) ≤ (∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W) / (n : ℝ) := by
    refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) (le_of_lt hn')
    haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₂_nonneg (p₁ i) (p₂ i) W
  have hsumle : (∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W)
      ≤ ∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W := by
    refine Finset.sum_le_sum fun i _ => ?_
    haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₁_le_macInfoBoth (p₁ i) (p₂ i) W
  have hs : (R₁ * (1 - Pe) - Real.log 2 / (n : ℝ)) + 0
      ≤ (∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W) / (n : ℝ) := by
    rw [add_zero]
    exact h1.trans (div_le_div_of_nonneg_right hsumle (le_of_lt hn'))
  -- geometric gateway with the second rate `= 0`
  have hmem : (R₁ * (1 - Pe) - Real.log 2 / (n : ℝ), (0 : ℝ))
      ∈ convexHull ℝ (⋃ i : Fin n,
          ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
            ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
           : Set (ℝ × ℝ))) :=
    mac_avgPentagon_mem_convexHull hn
      (fun i => macInfo₁ (p₁ i) (p₂ i) W) (fun i => macInfo₂ (p₁ i) (p₂ i) W)
      (fun i => macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₁_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₂_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₁_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₂_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_perletter_superadd (p₁ i) (p₂ i) W)
      hx1 (le_refl 0) h1 h2 hs
  -- reindex the raw per-letter union into the master probability-input union
  have hsubset : (⋃ i : Fin n,
        ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
          ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
         : Set (ℝ × ℝ)))
      ⊆ (⋃ (q₁ : Measure α₁) (q₂ : Measure α₂)
          (_ : IsProbabilityMeasure q₁) (_ : IsProbabilityMeasure q₂), macPentagon q₁ q₂ W) := by
    intro pt hpt
    rw [Set.mem_iUnion] at hpt
    obtain ⟨i, hi⟩ := hpt
    haveI := hp₁prob i; haveI := hp₂prob i
    simp only [Set.mem_iUnion]
    exact ⟨p₁ i, p₂ i, hp₁prob i, hp₂prob i, hi⟩
  exact convexHull_subset_closedConvexHull (convexHull_mono hsubset hmem)

/-- **Per-code shrunk-point membership, axis user 2** (`R₁ = 0`).  Symmetric to
`mac_converse_shrunk_point_mem_axis1`. -/
lemma mac_converse_shrunk_point_mem_axis2 [NeZero M₁]
    (c : MACCode M₁ M₂ n α₁ α₂ β) (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₂ : 2 ≤ M₂)
    {R₂ : ℝ} (hR₂ : 0 ≤ R₂)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
    (hx2 : 0 ≤ R₂ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ)) :
    ((0 : ℝ), R₂ * (1 - (c.averageErrorProb W).toReal) - Real.log 2 / (n : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  haveI : NeZero M₂ := ⟨by omega⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hM₂R : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hcard₂
  set p₁ : Fin n → Measure α₁ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i) with hp₁def
  set p₂ : Fin n → Measure α₂ :=
    fun i => (macConverseAmbient c W).map (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) with hp₂def
  have hp₁prob : ∀ i, IsProbabilityMeasure (p₁ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hp₂prob : ∀ i, IsProbabilityMeasure (p₂ i) := fun i =>
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  set Pe := (c.averageErrorProb W).toReal with hPeDef
  set Pe₂ := MeasureFano.errorProb (macConverseAmbient c W) macConverseMsg₂
    (fun ω ↦ (macConverseMsg₁ ω, fun i ↦ macConverseYs i ω)) (fun p ↦ (c.decoder p.2).2) with hPe₂def
  set S₂ := (∑ i : Fin n, condMutualInfo (macConverseAmbient c W)
      (fun ω ↦ c.encoder₂ (macConverseMsg₂ ω) i) (macConverseYs i)
      (fun ω ↦ c.encoder₁ (macConverseMsg₁ ω) i)).toReal with hS₂def
  have hjoint : MeasureFano.errorProb (macConverseAmbient c W)
      (fun ω ↦ (macConverseMsg₁ ω, macConverseMsg₂ ω)) (fun ω i ↦ macConverseYs i ω) c.decoder = Pe :=
    mac_converse_ambient_errorProb_joint_eq c W
  have hPe_0 : 0 ≤ Pe := ENNReal.toReal_nonneg
  have hPe_1 : Pe ≤ 1 := by rw [← hjoint]; exact measureReal_le_one
  have hPe2_0 : 0 ≤ Pe₂ := measureReal_nonneg
  have hPe2_1 : Pe₂ ≤ 1 := measureReal_le_one
  have hPe2_le : Pe₂ ≤ Pe := (mac_converse_ambient_errorProb_user2_le c W).trans (le_of_eq hjoint)
  have hnR2 : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  have hlogm2 : Real.log ((M₂ : ℝ) - 1) ≤ Real.log (M₂ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2n_nonneg : 0 ≤ Real.log 2 / (n : ℝ) :=
    div_nonneg (le_of_lt (Real.log_pos (by norm_num))) (le_of_lt hn')
  have hbound2 : R₂ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ S₂ / (n : ℝ) := by
    have hb2 := mac_converse_from_code_bound₂ c W hcard₂
    have hbe2 : Real.binEntropy Pe₂ ≤ Real.log 2 := Real.binEntropy_le_log_two
    have hprod2 : Pe₂ * Real.log ((M₂ : ℝ) - 1) ≤ Pe₂ * Real.log (M₂ : ℝ) :=
      mul_le_mul_of_nonneg_left hlogm2 hPe2_0
    have hstep1 : Real.log (M₂ : ℝ) * (1 - Pe₂) ≤ S₂ + Real.log 2 := by
      have e : Real.log (M₂ : ℝ) * (1 - Pe₂) = Real.log (M₂ : ℝ) - Pe₂ * Real.log (M₂ : ℝ) := by ring
      rw [e]; linarith [hb2, hbe2, hprod2]
    have hstep2 : (n : ℝ) * R₂ * (1 - Pe₂) ≤ Real.log (M₂ : ℝ) * (1 - Pe₂) :=
      mul_le_mul_of_nonneg_right hnR2 (by linarith)
    have hstep3 : (n : ℝ) * R₂ * (1 - Pe) ≤ (n : ℝ) * R₂ * (1 - Pe₂) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (Nat.cast_nonneg n) hR₂)
    have key2 : (n : ℝ) * R₂ * (1 - Pe) ≤ S₂ + Real.log 2 := hstep3.trans (hstep2.trans hstep1)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn',
      show R₂ * (1 - Pe) * (n : ℝ) = (n : ℝ) * R₂ * (1 - Pe) from by ring]
    exact key2
  have hSm2 : S₂ = ∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W := by
    rw [hS₂def, ENNReal.toReal_sum (fun i _ => condMutualInfo_ne_top _ _ _ _
      (measurable_of_countable _) (measurable_of_countable _) (measurable_of_countable _))]
    exact Finset.sum_congr rfl (fun i _ => mac_condMI_eq_macInfo₂_at c W i)
  have h2 : R₂ * (1 - Pe) - Real.log 2 / (n : ℝ) ≤ (∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W) / (n : ℝ) :=
    hSm2 ▸ hbound2
  have h1 : (0 : ℝ) ≤ (∑ i : Fin n, macInfo₁ (p₁ i) (p₂ i) W) / (n : ℝ) := by
    refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) (le_of_lt hn')
    haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₁_nonneg (p₁ i) (p₂ i) W
  have hsumle : (∑ i : Fin n, macInfo₂ (p₁ i) (p₂ i) W)
      ≤ ∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W := by
    refine Finset.sum_le_sum fun i _ => ?_
    haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₂_le_macInfoBoth (p₁ i) (p₂ i) W
  have hs : (0 : ℝ) + (R₂ * (1 - Pe) - Real.log 2 / (n : ℝ))
      ≤ (∑ i : Fin n, macInfoBoth (p₁ i) (p₂ i) W) / (n : ℝ) := by
    rw [zero_add]
    exact h2.trans (div_le_div_of_nonneg_right hsumle (le_of_lt hn'))
  have hmem : ((0 : ℝ), R₂ * (1 - Pe) - Real.log 2 / (n : ℝ))
      ∈ convexHull ℝ (⋃ i : Fin n,
          ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
            ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
           : Set (ℝ × ℝ))) :=
    mac_avgPentagon_mem_convexHull hn
      (fun i => macInfo₁ (p₁ i) (p₂ i) W) (fun i => macInfo₂ (p₁ i) (p₂ i) W)
      (fun i => macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₁_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact macInfo₂_nonneg (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₁_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_macInfo₂_le_macInfoBoth (p₁ i) (p₂ i) W)
      (fun i => by haveI := hp₁prob i; haveI := hp₂prob i; exact mac_perletter_superadd (p₁ i) (p₂ i) W)
      (le_refl 0) hx2 h1 h2 hs
  have hsubset : (⋃ i : Fin n,
        ({p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ≤ macInfo₁ (p₁ i) (p₂ i) W
          ∧ p.2 ≤ macInfo₂ (p₁ i) (p₂ i) W ∧ p.1 + p.2 ≤ macInfoBoth (p₁ i) (p₂ i) W}
         : Set (ℝ × ℝ)))
      ⊆ (⋃ (q₁ : Measure α₁) (q₂ : Measure α₂)
          (_ : IsProbabilityMeasure q₁) (_ : IsProbabilityMeasure q₂), macPentagon q₁ q₂ W) := by
    intro pt hpt
    rw [Set.mem_iUnion] at hpt
    obtain ⟨i, hi⟩ := hpt
    haveI := hp₁prob i; haveI := hp₂prob i
    simp only [Set.mem_iUnion]
    exact ⟨p₁ i, p₂ i, hp₁prob i, hp₂prob i, hi⟩
  exact convexHull_subset_closedConvexHull (convexHull_mono hsubset hmem)

/-- **Axis case, user 1** (`R₂ = 0`).  For a strictly positive rate `R₁` achievable with `R₂ = 0`,
the pair `(R₁, 0)` lies in the closed convex hull of the per-input pentagons.  Uses the user-1-only
finite-`n` Fano bound `mac_converse_from_code_bound₁` (which needs only `2 ≤ M₁`, and thus survives
the `M₂ = 1` degeneracy of the axis), then takes the Fano→0 limit as in the interior case. -/
lemma mac_timesharing_converse_axis1 (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {R₁ : ℝ} (hR₁ : 0 < R₁) (hach : MACAchievable W R₁ 0) :
    (R₁, (0 : ℝ)) ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
        (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  -- for each `k`, extract a length-`nₖ ≥ k+1` code with `2 ≤ m₁`, `1 ≤ m₂` and error `< 1/(k+1)`
  have hex : ∀ k : ℕ, ∃ (nn m₁ m₂ : ℕ) (c : MACCode m₁ m₂ nn α₁ α₂ β),
      0 < nn ∧ 2 ≤ m₁ ∧ 1 ≤ m₂ ∧ (k : ℝ) + 1 ≤ (nn : ℝ)
        ∧ Nat.ceil (Real.exp ((nn : ℝ) * R₁)) ≤ m₁
        ∧ (c.averageErrorProb W).toReal < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨N, hN⟩ := hach (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨m₁, m₂, hm₁, hm₂, c, hPe⟩ := hN (max N (k + 1)) (le_max_left _ _)
    have hnnpos : 0 < max N (k + 1) := lt_of_lt_of_le (Nat.succ_pos k) (le_max_right _ _)
    have hnge : (k : ℝ) + 1 ≤ ((max N (k + 1) : ℕ) : ℝ) := by
      have hle : k + 1 ≤ max N (k + 1) := le_max_right _ _
      calc (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((max N (k + 1) : ℕ) : ℝ) := by exact_mod_cast hle
    have hcardm₁ : 2 ≤ m₁ := by
      have hpos : (0 : ℝ) < ((max N (k + 1) : ℕ) : ℝ) * R₁ := mul_pos (by exact_mod_cast hnnpos) hR₁
      have h1lt : (1 : ℝ) < Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₁) := by
        rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]; exact Real.exp_lt_exp.mpr hpos
      have h1c : (1 : ℝ) < (Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₁)) : ℝ) :=
        lt_of_lt_of_le h1lt (Nat.le_ceil _)
      have : 1 < Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₁)) := by exact_mod_cast h1c
      omega
    have hcardm₂ : 1 ≤ m₂ := by
      have h := hm₂
      simp only [mul_zero, Real.exp_zero, Nat.ceil_one] at h
      exact h
    exact ⟨max N (k + 1), m₁, m₂, c, hnnpos, hcardm₁, hcardm₂, hnge, hm₁, hPe⟩
  choose nn m₁ m₂ c hnpos hcard₁ hcard₂ hnge hM₁ hPe using hex
  -- the average error probabilities converge to `0`, hence so does `log2/nₖ`
  have hPe0 : Tendsto (fun k => ((c k).averageErrorProb W).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun k => (hPe k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hnn_top : Tendsto (fun k => (nn k : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => le_trans (by linarith) (hnge k)) tendsto_natCast_atTop_atTop
  have hlog0 : Tendsto (fun k => Real.log 2 / (nn k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hnn_top
  -- the first coordinate of the shrunk-rate sequence converges to `R₁`; the second is constant `0`
  have hf1 : Tendsto (fun k => R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      atTop (𝓝 R₁) := by
    have hlim : Tendsto (fun k => R₁ * (1 - ((c k).averageErrorProb W).toReal)
        - Real.log 2 / (nn k : ℝ)) atTop (𝓝 (R₁ * (1 - 0) - 0)) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hPe0)).sub hlog0
    simpa using hlim
  have htend : Tendsto (fun k => (R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ),
      (0 : ℝ))) atTop (𝓝 (R₁, (0 : ℝ))) :=
    hf1.prodMk_nhds tendsto_const_nhds
  -- eventually the shrunk point is in the first quadrant
  have hpos1 : ∀ᶠ k in atTop, 0 ≤ R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ) := by
    filter_upwards [hf1.eventually (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hR₁))] with k hk
    exact le_of_lt hk
  -- eventually the shrunk point lies in the closed convex hull (via the axis per-code lemma)
  have hev : ∀ᶠ k in atTop, (R₁ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ),
      (0 : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
    filter_upwards [hpos1] with k hk1
    haveI : NeZero (m₂ k) := ⟨by have := hcard₂ k; omega⟩
    exact mac_converse_shrunk_point_mem_axis1 (c k) W (hnpos k) (hcard₁ k) hR₁.le (hM₁ k) hk1
  exact isClosed_closedConvexHull.mem_of_tendsto htend hev

/-- **Axis case, user 2** (`R₁ = 0`).  Symmetric to `mac_timesharing_converse_axis1`: uses the
user-2-only finite-`n` Fano bound `mac_converse_from_code_bound₂` (needing only `2 ≤ M₂`, surviving
the `M₁ = 1` degeneracy), then takes the Fano→0 limit. -/
lemma mac_timesharing_converse_axis2 (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {R₂ : ℝ} (hR₂ : 0 < R₂) (hach : MACAchievable W 0 R₂) :
    ((0 : ℝ), R₂) ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
        (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  -- for each `k`, extract a length-`nₖ ≥ k+1` code with `1 ≤ m₁`, `2 ≤ m₂` and error `< 1/(k+1)`
  have hex : ∀ k : ℕ, ∃ (nn m₁ m₂ : ℕ) (c : MACCode m₁ m₂ nn α₁ α₂ β),
      0 < nn ∧ 1 ≤ m₁ ∧ 2 ≤ m₂ ∧ (k : ℝ) + 1 ≤ (nn : ℝ)
        ∧ Nat.ceil (Real.exp ((nn : ℝ) * R₂)) ≤ m₂
        ∧ (c.averageErrorProb W).toReal < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨N, hN⟩ := hach (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨m₁, m₂, hm₁, hm₂, c, hPe⟩ := hN (max N (k + 1)) (le_max_left _ _)
    have hnnpos : 0 < max N (k + 1) := lt_of_lt_of_le (Nat.succ_pos k) (le_max_right _ _)
    have hnge : (k : ℝ) + 1 ≤ ((max N (k + 1) : ℕ) : ℝ) := by
      have hle : k + 1 ≤ max N (k + 1) := le_max_right _ _
      calc (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((max N (k + 1) : ℕ) : ℝ) := by exact_mod_cast hle
    have hcardm₂ : 2 ≤ m₂ := by
      have hpos : (0 : ℝ) < ((max N (k + 1) : ℕ) : ℝ) * R₂ := mul_pos (by exact_mod_cast hnnpos) hR₂
      have h1lt : (1 : ℝ) < Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₂) := by
        rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]; exact Real.exp_lt_exp.mpr hpos
      have h1c : (1 : ℝ) < (Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₂)) : ℝ) :=
        lt_of_lt_of_le h1lt (Nat.le_ceil _)
      have : 1 < Nat.ceil (Real.exp (((max N (k + 1) : ℕ) : ℝ) * R₂)) := by exact_mod_cast h1c
      omega
    have hcardm₁ : 1 ≤ m₁ := by
      have h := hm₁
      simp only [mul_zero, Real.exp_zero, Nat.ceil_one] at h
      exact h
    exact ⟨max N (k + 1), m₁, m₂, c, hnnpos, hcardm₁, hcardm₂, hnge, hm₂, hPe⟩
  choose nn m₁ m₂ c hnpos hcard₁ hcard₂ hnge hM₂ hPe using hex
  have hPe0 : Tendsto (fun k => ((c k).averageErrorProb W).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun k => (hPe k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hnn_top : Tendsto (fun k => (nn k : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun k => le_trans (by linarith) (hnge k)) tendsto_natCast_atTop_atTop
  have hlog0 : Tendsto (fun k => Real.log 2 / (nn k : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hnn_top
  have hf2 : Tendsto (fun k => R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      atTop (𝓝 R₂) := by
    have hlim : Tendsto (fun k => R₂ * (1 - ((c k).averageErrorProb W).toReal)
        - Real.log 2 / (nn k : ℝ)) atTop (𝓝 (R₂ * (1 - 0) - 0)) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hPe0)).sub hlog0
    simpa using hlim
  have htend : Tendsto (fun k => ((0 : ℝ),
      R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ)))
      atTop (𝓝 ((0 : ℝ), R₂)) :=
    tendsto_const_nhds.prodMk_nhds hf2
  have hpos2 : ∀ᶠ k in atTop, 0 ≤ R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ) := by
    filter_upwards [hf2.eventually (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hR₂))] with k hk
    exact le_of_lt hk
  have hev : ∀ᶠ k in atTop, ((0 : ℝ),
      R₂ * (1 - ((c k).averageErrorProb W).toReal) - Real.log 2 / (nn k : ℝ))
      ∈ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
    filter_upwards [hpos2] with k hk2
    haveI : NeZero (m₁ k) := ⟨by have := hcard₁ k; omega⟩
    exact mac_converse_shrunk_point_mem_axis2 (c k) W (hnpos k) (hcard₂ k) hR₂.le (hM₂ k) hk2
  exact isClosed_closedConvexHull.mem_of_tendsto htend hev

/-- **MAC time-sharing converse (CV headline).**  Every achievable first-quadrant rate pair lies in
the closed convex hull of the union of all per-input pentagons `macPentagon p₁ p₂ W` over
probability inputs `p₁`, `p₂`.  Assembled by casework on whether each rate is zero or positive:
the interior case uses the Fano→0 limit `mac_timesharing_converse_interior`, the origin `(0,0)` lies
in any pentagon, and the two axis cases are honest gaps (see `mac_timesharing_converse_axis1/2`). -/
theorem mac_timesharing_converse (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    {p | MACAchievable W p.1 p.2 ∧ 0 ≤ p.1 ∧ 0 ≤ p.2}
      ⊆ closedConvexHull ℝ (⋃ (p₁ : Measure α₁) (p₂ : Measure α₂)
          (_ : IsProbabilityMeasure p₁) (_ : IsProbabilityMeasure p₂), macPentagon p₁ p₂ W) := by
  rintro ⟨R₁, R₂⟩ ⟨hach, hR₁0, hR₂0⟩
  rcases hR₁0.lt_or_eq with hR₁ | hR₁
  · rcases hR₂0.lt_or_eq with hR₂ | hR₂
    · exact mac_timesharing_converse_interior W hR₁ hR₂ hach
    · subst hR₂
      exact mac_timesharing_converse_axis1 W hR₁ hach
  · subst hR₁
    rcases hR₂0.lt_or_eq with hR₂ | hR₂
    · exact mac_timesharing_converse_axis2 W hR₂ hach
    · subst hR₂
      -- origin: `(0, 0)` lies in every pentagon (all five inequalities are `0 ≤ nonneg`)
      apply subset_closedConvexHull
      haveI hd1 : IsProbabilityMeasure (Measure.dirac (Classical.arbitrary α₁) : Measure α₁) :=
        inferInstance
      haveI hd2 : IsProbabilityMeasure (Measure.dirac (Classical.arbitrary α₂) : Measure α₂) :=
        inferInstance
      simp only [Set.mem_iUnion]
      refine ⟨Measure.dirac (Classical.arbitrary α₁), Measure.dirac (Classical.arbitrary α₂),
        hd1, hd2, le_refl _, le_refl _, ?_, ?_, ?_⟩
      · exact macInfo₁_nonneg _ _ W
      · exact macInfo₂_nonneg _ _ W
      · simpa using macInfoBoth_nonneg (Measure.dirac (Classical.arbitrary α₁))
          (Measure.dirac (Classical.arbitrary α₂)) W

end CVAssembly

end InformationTheory.Shannon.MAC
