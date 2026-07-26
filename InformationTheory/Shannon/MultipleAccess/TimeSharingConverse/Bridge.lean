import InformationTheory.Shannon.MultipleAccess.TimeSharing
import InformationTheory.Shannon.MultipleAccess.Reconciliation
import InformationTheory.Shannon.MultipleAccess.Converse
import InformationTheory.Shannon.ChannelCoding.CodeToAmbient
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Integral.Marginal

/-!
# Multiple access channel — time-sharing converse, geometric gateway and measure bridge

The convex-geometry gateway `mac_avgPentagon_mem_convexHull` (an achievable pair bounded
coordinate-wise by time averages of per-letter pentagons lies in the convex hull of their union),
together with the measure-theoretic bridge feeding it: pentagon well-formedness for the product
input, the code → ambient reduction, rate extraction, and the per-letter information
transport under coordinate maps.
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
  refine mem_convexHull_of_exists_fintype w (fun i ↦ ((z i).1 * r1, (z i).2 * r2)) hw0 hw1 ?_ ?_
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
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ ↦ by ring)
        _ = q.1 * r1 := by rw [hq1]
        _ = p.1 := hkey1
    · simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
      calc ∑ i, w i * ((z i).2 * r2) = (∑ i, w i * (z i).2) * r2 := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ ↦ by ring)
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
    exact mem_convexHull_of_exists_fintype _ _ (fun _ ↦ by positivity) hw1 hcA_mem rfl
  have hB_mem : B ∈ convexHull ℝ S := by
    rw [hBdef]
    exact mem_convexHull_of_exists_fintype _ _ (fun _ ↦ by positivity) hw1 hcB_mem rfl
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
        Finset.sum_congr rfl (fun i _ ↦ by ring),
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
        Finset.sum_congr rfl (fun i _ ↦ by ring),
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

/-! ### Code → ambient bridge

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

/-- The MAC converse instantiated at a bare code: for any two-user MAC block code `c` and
Markov channel `W`, the canonical ambient measure `macConverseAmbient c W` discharges every
hypothesis of the floating converse `mac_converse`, so the rate pair `(log M₁, log M₂)` lies
in the corner-point region determined by the per-letter conditional and joint mutual
informations.  The Fano slack is still carried here; it vanishes only in the `n → ∞` limit.
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

/-- Finite-`n` rate extraction for the weak converse: for a fixed two-user block code whose
message counts satisfy `⌈exp (n R₁)⌉ ≤ M₁`, `⌈exp (n R₂)⌉ ≤ M₂`, chaining the code→ambient
converse `mac_converse_from_code` with `n Rⱼ ≤ log Mⱼ` moves the rate scaled by `n` inside the
corner-point region determined by the per-letter conditional/joint mutual informations plus the
Fano slack.  The slack is still symbolic here; the Fano → 0 limit is taken in
`mac_timesharing_converse`. -/
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

/-- The ambient *joint* decode error under `macConverseAmbient c W` equals the code's average
error probability: the ambient was built as `uniform(messages) ⊗ per-letter product channel`
precisely to model uniform-message transmission, so its joint error event has probability
`averageErrorProb`. -/
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
  -- each kernel fiber measures exactly the pointwise error probability
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

/-- Per-letter joint law identification: under the converse ambient
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

/-- Per-letter identification of the user-1 corner information: the ambient per-letter
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

/-- Per-letter identification of the user-2 corner information: the ambient per-letter
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

/-- Per-letter identification of the sum-corner information: the ambient per-letter joint
mutual information `I((X₁ᵢ, X₂ᵢ); Yᵢ)` equals `macInfoBoth` of the per-letter product
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
end InformationTheory.Shannon.MAC
