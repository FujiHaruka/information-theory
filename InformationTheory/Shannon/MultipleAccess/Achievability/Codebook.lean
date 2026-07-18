import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.AchievabilityCore
import InformationTheory.Shannon.MultipleAccess.IIDAmbient
import InformationTheory.Shannon.ChannelCoding.Achievability.Main

/-!
# Multiple access channel — codebook, decoder, and Bonferroni decomposition

The two-user codebook plumbing for MAC achievability (Cover–Thomas §15.3.1): the codebook
type, the joint-typical pair decoder, the `MACCode` bundle, the four-event Bonferroni
decomposition of the per-pair error probability, the corner-point information quantities,
and the block-law / channel-fold helpers feeding the two-codebook random-coding average.
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-! ### Codebook + joint-typical pair decoder -/

/-- A length-`n` codebook for one MAC user: a function from message indices to
length-`n` words.  Two codebooks (one per user) make up a `MACCode`. -/
abbrev MACCodebook (M n : ℕ) (α : Type*) := Fin M → (Fin n → α)

/-- Joint-typical pair decoder.  Given a received word `y`, returns the unique message
pair `(m₁, m₂)` such that `(c₁ m₁, c₂ m₂, y) ∈ macJointlyTypicalSet …`, falling back to
`(⟨0, hM₁⟩, ⟨0, hM₂⟩)` if either no such pair exists or it is not unique. -/
noncomputable def macJointTypicalDecoder
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (c₁ : MACCodebook M₁ n α₁) (c₂ : MACCodebook M₂ n α₂) :
    (Fin n → β) → Fin M₁ × Fin M₂ := fun y ↦
  haveI : Decidable (∃! p : Fin M₁ × Fin M₂,
      (c₁ p.1, c₂ p.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε) :=
    Classical.propDecidable _
  if h : ∃! p : Fin M₁ × Fin M₂,
      (c₁ p.1, c₂ p.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε
    then Classical.choose h.exists
    else (⟨0, hM₁⟩, ⟨0, hM₂⟩)

/-- Bundle two codebooks + the joint-typical pair decoder into a `MACCode`. -/
noncomputable def macCodebookToCode
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ε : ℝ)
    (c₁ : MACCodebook M₁ n α₁) (c₂ : MACCodebook M₂ n α₂) :
    MACCode M₁ M₂ n α₁ α₂ β where
  encoder₁ := c₁
  encoder₂ := c₂
  decoder := macJointTypicalDecoder μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂

/-! ### Four-event Bonferroni decomposition -/

omit [DecidableEq α₁] [Nonempty α₁] [MeasurableSingletonClass α₁]
  [DecidableEq α₂] [Nonempty α₂] [MeasurableSingletonClass α₂]
  [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β] in
/-- **Four-event Bonferroni bound.**  When the pair `(m₁, m₂)` is sent, the per-pair error
probability of the joint-typical pair decoder is bounded by the four error events:

* `E0` — the correct codeword triple `(c₁ m₁, c₂ m₂, y)` is not jointly typical;
* `E1` — some user-1 alias `m₁' ≠ m₁` (with user 2 correct) is jointly typical;
* `E2` — some user-2 alias `m₂' ≠ m₂` (with user 1 correct) is jointly typical;
* `E3` — some pair `(m₁', m₂')` with both indices wrong is jointly typical.

The block output law is `ν = Measure.pi (i ↦ W (c₁ m₁ i, c₂ m₂ i))`.  This is the
two-codebook / four-event generalisation of the single-user
`errorProbAt_le_E1_plus_E2`; the two-codebook averaging consumes the four terms term by
term. -/
theorem mac_errorProbAt_le_bonferroni4
    (μ : Measure Ω) (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    {M₁ M₂ n : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) {ε : ℝ}
    (c₁ : MACCodebook M₁ n α₁) (c₂ : MACCodebook M₂ n α₂)
    (m₁ : Fin M₁) (m₂ : Fin M₂) :
    ((macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂).errorProbAt W (m₁, m₂)).toReal
      ≤ (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
          {y | (c₁ m₁, c₂ m₂, y) ∉ macJointlyTypicalSet μ X1s X2s Ys n ε}
        + ∑ m₁' ∈ (Finset.univ : Finset (Fin M₁)).erase m₁,
            (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
              {y | (c₁ m₁', c₂ m₂, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε}
        + ∑ m₂' ∈ (Finset.univ : Finset (Fin M₂)).erase m₂,
            (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
              {y | (c₁ m₁, c₂ m₂', y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε}
        + ∑ p ∈ ((Finset.univ : Finset (Fin M₁)).erase m₁) ×ˢ
                  ((Finset.univ : Finset (Fin M₂)).erase m₂),
            (Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i))).real
              {y | (c₁ p.1, c₂ p.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε} := by
  classical
  -- Treat the (7-fold) jointly typical set as atomic to keep unification cheap.
  set J : Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
    macJointlyTypicalSet μ X1s X2s Ys n ε with hJ_def
  -- Index sets for the three alias sums.
  set S1 : Finset (Fin M₁) := (Finset.univ : Finset (Fin M₁)).erase m₁ with hS1_def
  set S2 : Finset (Fin M₂) := (Finset.univ : Finset (Fin M₂)).erase m₂ with hS2_def
  set S3 : Finset (Fin M₁ × Fin M₂) := S1 ×ˢ S2 with hS3_def
  -- The code and the block output law.
  set c : MACCode M₁ M₂ n α₁ α₂ β := macCodebookToCode μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂ with hc_def
  set ν : Measure (Fin n → β) := Measure.pi (fun i ↦ W (c₁ m₁ i, c₂ m₂ i)) with hν_def
  haveI : IsProbabilityMeasure ν := by rw [hν_def]; infer_instance
  -- The four error events: E0 (correct pair atypical), and the three alias families.
  set E0 : Set (Fin n → β) := {y | (c₁ m₁, c₂ m₂, y) ∉ J} with hE0_def
  set E1indiv : Fin M₁ → Set (Fin n → β) :=
    fun a ↦ {y | (c₁ a, c₂ m₂, y) ∈ J} with hE1_def
  set E2indiv : Fin M₂ → Set (Fin n → β) :=
    fun b ↦ {y | (c₁ m₁, c₂ b, y) ∈ J} with hE2_def
  set E3indiv : Fin M₁ × Fin M₂ → Set (Fin n → β) :=
    fun p ↦ {y | (c₁ p.1, c₂ p.2, y) ∈ J} with hE3_def
  -- Step 1: the error event is contained in the union of the four error events.
  have h_sub : c.errorEvent (m₁, m₂) ⊆
      ((E0 ∪ ⋃ a ∈ S1, E1indiv a) ∪ ⋃ b ∈ S2, E2indiv b) ∪ ⋃ p ∈ S3, E3indiv p := by
    intro y hy
    rw [MACCode.mem_errorEvent] at hy
    -- A typical alias pair `p ≠ (m₁, m₂)` lands in one of the three alias unions.
    have place : ∀ p : Fin M₁ × Fin M₂,
        (c₁ p.1, c₂ p.2, y) ∈ J → p ≠ (m₁, m₂) →
        y ∈ ((E0 ∪ ⋃ a ∈ S1, E1indiv a) ∪ ⋃ b ∈ S2, E2indiv b) ∪ ⋃ p ∈ S3, E3indiv p := by
      intro p hp_mem hp_ne
      by_cases ha : p.1 = m₁
      · -- user 1 correct, so user 2 must be wrong (E2).
        have hb : p.2 ≠ m₂ := fun hb ↦ hp_ne (Prod.ext_iff.mpr ⟨ha, hb⟩)
        refine Or.inl (Or.inr ?_)
        refine Set.mem_iUnion.mpr ⟨p.2, ?_⟩
        refine Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩, ?_⟩
        change (c₁ m₁, c₂ p.2, y) ∈ J
        rw [← ha]; exact hp_mem
      · by_cases hb : p.2 = m₂
        · -- user 1 wrong, user 2 correct (E1).
          refine Or.inl (Or.inl (Or.inr ?_))
          refine Set.mem_iUnion.mpr ⟨p.1, ?_⟩
          refine Set.mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩, ?_⟩
          change (c₁ p.1, c₂ m₂, y) ∈ J
          rw [← hb]; exact hp_mem
        · -- both wrong (E3).
          refine Or.inr ?_
          refine Set.mem_iUnion.mpr ⟨p, ?_⟩
          refine Set.mem_iUnion.mpr
            ⟨Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩,
              Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩⟩, ?_⟩
          exact hp_mem
    -- Case analyse on whether the correct pair is typical.
    by_cases hc_typ : (c₁ m₁, c₂ m₂, y) ∈ J
    · -- Correct pair typical: either some alias is also typical (E1/E2/E3), or the correct
      -- pair is the unique typical pair, so the decoder outputs `(m₁, m₂)`, contradicting `hy`.
      by_cases h_alias : ∃ p : Fin M₁ × Fin M₂, (c₁ p.1, c₂ p.2, y) ∈ J ∧ p ≠ (m₁, m₂)
      · obtain ⟨p, hp_mem, hp_ne⟩ := h_alias
        exact place p hp_mem hp_ne
      · exfalso
        apply hy
        -- No alias ⇒ `(m₁, m₂)` is the unique typical pair.
        have huniq : ∃! p : Fin M₁ × Fin M₂,
            (c₁ p.1, c₂ p.2, y) ∈ macJointlyTypicalSet μ X1s X2s Ys n ε := by
          refine ⟨(m₁, m₂), hc_typ, ?_⟩
          intro p hp
          by_contra hne
          exact h_alias ⟨p, hp, hne⟩
        change macJointTypicalDecoder μ X1s X2s Ys hM₁ hM₂ ε c₁ c₂ y = (m₁, m₂)
        unfold macJointTypicalDecoder
        rw [dif_pos huniq]
        exact huniq.unique (Classical.choose_spec huniq.exists) hc_typ
    · -- Correct pair atypical: y ∈ E0.
      exact Or.inl (Or.inl (Or.inl hc_typ))
  -- Step 2: bound the error measure by the union bound over the four events.
  have h_eq_meas : c.errorProbAt W (m₁, m₂) = ν (c.errorEvent (m₁, m₂)) := by
    change (Measure.pi (fun i ↦ W (c.encoder₁ (m₁, m₂).1 i, c.encoder₂ (m₁, m₂).2 i)))
        (c.errorEvent (m₁, m₂)) = _
    rfl
  have h_real_eq : (c.errorProbAt W (m₁, m₂)).toReal = ν.real (c.errorEvent (m₁, m₂)) := by
    rw [h_eq_meas]; rfl
  rw [h_real_eq]
  calc ν.real (c.errorEvent (m₁, m₂))
      ≤ ν.real (((E0 ∪ ⋃ a ∈ S1, E1indiv a) ∪ ⋃ b ∈ S2, E2indiv b) ∪ ⋃ p ∈ S3, E3indiv p) :=
        measureReal_mono h_sub (measure_ne_top _ _)
    _ ≤ ν.real ((E0 ∪ ⋃ a ∈ S1, E1indiv a) ∪ ⋃ b ∈ S2, E2indiv b)
          + ν.real (⋃ p ∈ S3, E3indiv p) := measureReal_union_le _ _
    _ ≤ (ν.real (E0 ∪ ⋃ a ∈ S1, E1indiv a) + ν.real (⋃ b ∈ S2, E2indiv b))
          + ν.real (⋃ p ∈ S3, E3indiv p) := add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ ((ν.real E0 + ν.real (⋃ a ∈ S1, E1indiv a)) + ν.real (⋃ b ∈ S2, E2indiv b))
          + ν.real (⋃ p ∈ S3, E3indiv p) :=
        add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl
    _ ≤ ((ν.real E0 + ∑ a ∈ S1, ν.real (E1indiv a)) + ∑ b ∈ S2, ν.real (E2indiv b))
          + ∑ p ∈ S3, ν.real (E3indiv p) :=
        add_le_add (add_le_add (add_le_add le_rfl (measureReal_biUnion_finset_le _ _))
          (measureReal_biUnion_finset_le _ _)) (measureReal_biUnion_finset_le _ _)

/-! ### Corner-point information quantities

The three rate corners returned in the entropy-exponent form handed back by the
gateway atoms `macJTS_indep_prob_le_X1`/`_X2`/`_both`: `macInfo₁ = I(X₁; (X₂, Y))`,
`macInfo₂ = I(X₂; (X₁, Y))`, `macInfoBoth = I((X₁, X₂); Y)`, each expressed as a
difference of entropies of marginals of the per-coordinate joint law
`macJointDistribution p₁ p₂ W`.  Under the independent product input `p₁ ⊗ p₂` these
equal the textbook conditional informations `I(X₁; Y | X₂)` / `I(X₂; Y | X₁)` /
`I(X₁, X₂; Y)`. -/

/-- `I(X₁; (X₂, Y)) = H(X₁) + H(X₂, Y) − H(X₁, X₂, Y)` for the per-coordinate joint. -/
noncomputable def macInfo₁
    (p₁ : Measure α₁) (p₂ : Measure α₂) (W : MACChannel α₁ α₂ β) : ℝ :=
  entropy (macJointDistribution p₁ p₂ W) Prod.fst
    + entropy (macJointDistribution p₁ p₂ W) Prod.snd
    - entropy (macJointDistribution p₁ p₂ W) id

/-- `I(X₂; (X₁, Y)) = H(X₂) + H(X₁, Y) − H(X₁, X₂, Y)`. -/
noncomputable def macInfo₂
    (p₁ : Measure α₁) (p₂ : Measure α₂) (W : MACChannel α₁ α₂ β) : ℝ :=
  entropy (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.1)
    + entropy (macJointDistribution p₁ p₂ W) (fun q ↦ (q.1, q.2.2))
    - entropy (macJointDistribution p₁ p₂ W) id

/-- `I((X₁, X₂); Y) = H(X₁, X₂) + H(Y) − H(X₁, X₂, Y)`. -/
noncomputable def macInfoBoth
    (p₁ : Measure α₁) (p₂ : Measure α₂) (W : MACChannel α₁ α₂ β) : ℝ :=
  entropy (macJointDistribution p₁ p₂ W) (fun q ↦ (q.1, q.2.1))
    + entropy (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.2)
    - entropy (macJointDistribution p₁ p₂ W) id

/-! ### Two-codebook averaging: block-law / channel-fold helpers -/

/-- Product-measure slice expansion over the first factor (finite alphabets). -/
lemma mac_prodReal_eq_slice_sum
    {A B : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (P : Measure A) [IsProbabilityMeasure P] (ν : Measure B) [IsProbabilityMeasure ν]
    (J : Set (A × B)) :
    (P.prod ν).real J = ∑ a : A, P.real {a} * ν.real {b | (a, b) ∈ J} := by
  classical
  have h_J_fin : J.Finite := Set.toFinite _
  set Jfin : Finset _ := h_J_fin.toFinset with hJfin_def
  have h_J_coe : (Jfin : Set _) = J := h_J_fin.coe_toFinset
  have h_prod_sum : (P.prod ν).real J = ∑ pq ∈ Jfin, P.real {pq.1} * ν.real {pq.2} := by
    have h_real_eq : (P.prod ν).real J = ∑ p ∈ Jfin, (P.prod ν).real {p} := by
      rw [← h_J_coe, ← sum_measureReal_singleton (μ := P.prod ν) Jfin]
    rw [h_real_eq]
    refine Finset.sum_congr rfl (fun pq _ ↦ ?_)
    have h_sgl : ({pq} : Set (A × B)) = ({pq.1} : Set A) ×ˢ ({pq.2} : Set B) := by
      ext ⟨a, b⟩; simp [Prod.ext_iff]
    rw [h_sgl]; exact measureReal_prod_prod _ _
  rw [h_prod_sum]
  have h_ind : (∑ pq ∈ Jfin, P.real {pq.1} * ν.real {pq.2})
      = ∑ a : A, ∑ b : B, (if (a, b) ∈ J then P.real {a} * ν.real {b} else 0) := by
    rw [show Jfin = ((Finset.univ : Finset _) ×ˢ Finset.univ : Finset _).filter (· ∈ J) from ?_]
    · rw [Finset.sum_filter, ← Finset.sum_product']
    · ext pq
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      constructor
      · intro h; exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩
      · intro h; exact h.2
  rw [h_ind]
  refine Finset.sum_congr rfl (fun a _ ↦ ?_)
  set S : Set B := {b | (a, b) ∈ J}
  have h_S_fin : S.Finite := Set.toFinite _
  have h_ν_slice : ν.real {b | (a, b) ∈ J} = ∑ b ∈ h_S_fin.toFinset, ν.real {b} := by
    have h_eq : ({b | (a, b) ∈ J} : Set _) = ↑h_S_fin.toFinset := by rw [h_S_fin.coe_toFinset]
    rw [h_eq, sum_measureReal_singleton]
  rw [h_ν_slice, Finset.mul_sum]
  rw [show (∑ b : B, (if (a, b) ∈ J then P.real {a} * ν.real {b} else 0))
          = ∑ b ∈ (Finset.univ : Finset B).filter (fun b ↦ (a, b) ∈ J),
              P.real {a} * ν.real {b} from by rw [Finset.sum_filter]]
  apply Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext b; simp

open Classical in
/-- A finite-alphabet measure of a set equals the indicator sum over singletons. -/
lemma measureReal_eq_sum_ite {γ : Type*} [Fintype γ] [MeasurableSpace γ]
    [MeasurableSingletonClass γ] (μ : Measure γ) [IsProbabilityMeasure μ] (S : Set γ) :
    μ.real S = ∑ z : γ, (if z ∈ S then μ.real {z} else 0) := by
  have hS : S = ↑((Finset.univ : Finset γ).filter (· ∈ S)) := by ext z; simp
  rw [← Finset.sum_filter, sum_measureReal_singleton, ← hS]

/-- The first-input marginal of the per-coordinate MAC joint law is `p₁`. -/
lemma macJointDistribution_map_fst
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    (macJointDistribution p₁ p₂ W).map Prod.fst = p₁ := by
  unfold macJointDistribution
  rw [Measure.map_map measurable_fst MeasurableEquiv.prodAssoc.measurable]
  have h_comp : (Prod.fst : α₁ × α₂ × β → α₁) ∘ (MeasurableEquiv.prodAssoc :
      (α₁ × α₂) × β ≃ᵐ α₁ × α₂ × β)
      = (Prod.fst : α₁ × α₂ → α₁) ∘ (Prod.fst : (α₁ × α₂) × β → α₁ × α₂) := by
    funext r; rfl
  rw [h_comp, ← Measure.map_map measurable_fst measurable_fst]
  have h1 : (jointDistribution (p₁.prod p₂) W).map Prod.fst = p₁.prod p₂ := by
    show (jointDistribution (p₁.prod p₂) W).fst = p₁.prod p₂
    rw [jointDistribution_def]
    exact Measure.fst_compProd _ _
  rw [h1]
  show (p₁.prod p₂).fst = p₁
  exact Measure.fst_prod

/-- The per-coordinate MAC joint law singleton mass:
`ν{(a₁, a₂, b)} = p₁{a₁} · p₂{a₂} · W(a₁, a₂){b}`. -/
lemma macJointDistribution_triple_singleton
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (a₁ : α₁) (a₂ : α₂) (b : β) :
    (macJointDistribution p₁ p₂ W).real {(a₁, a₂, b)}
      = p₁.real {a₁} * p₂.real {a₂} * (W (a₁, a₂)).real {b} := by
  unfold macJointDistribution
  rw [Measure.real,
    Measure.map_apply MeasurableEquiv.prodAssoc.measurable (measurableSet_singleton _)]
  have h_pre : (MeasurableEquiv.prodAssoc ⁻¹' ({(a₁, a₂, b)} : Set (α₁ × α₂ × β)))
      = ({((a₁, a₂), b)} : Set ((α₁ × α₂) × β)) := by
    ext ⟨⟨x, y⟩, z⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply, Prod.mk.injEq]
    tauto
  rw [h_pre, jointDistribution_singleton]
  rw [show ((p₁.prod p₂) {(a₁, a₂)}) = p₁ {a₁} * p₂ {a₂} from by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod]]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  rfl

/-- The per-coordinate `(X₂, Y)` marginal singleton mass:
`ν_{X₂Y}{(a₂, b)} = p₂{a₂} · ∑_{a₁} p₁{a₁} W(a₁, a₂){b}`. -/
lemma macJointDistribution_X2Y_singleton
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (a₂ : α₂) (b : β) :
    ((macJointDistribution p₁ p₂ W).map (fun q : α₁ × α₂ × β ↦ (q.2.1, q.2.2))).real {(a₂, b)}
      = p₂.real {a₂} * ∑ a₁ : α₁, p₁.real {a₁} * (W (a₁, a₂)).real {b} := by
  classical
  have hmeas : Measurable (fun q : α₁ × α₂ × β ↦ (q.2.1, q.2.2)) :=
    (measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)
  rw [map_measureReal_apply hmeas (measurableSet_singleton _)]
  -- The preimage is the finite set {(a₁, a₂, b) | a₁ : α₁}.
  set T : Set (α₁ × α₂ × β) :=
    (fun q : α₁ × α₂ × β ↦ (q.2.1, q.2.2)) ⁻¹' {(a₂, b)} with hT_def
  set F : Finset (α₁ × α₂ × β) :=
    (Finset.univ : Finset α₁).image (fun a₁ ↦ (a₁, a₂, b)) with hF_def
  have hF_coe : (F : Set (α₁ × α₂ × β)) = T := by
    ext q
    simp only [hF_def, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
      hT_def, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a₁, rfl⟩; rfl
    · intro h; exact ⟨q.1, by rw [← h]⟩
  -- Sum over the finite set T, reindexed by a₁.
  have h_sum : (macJointDistribution p₁ p₂ W).real T
      = ∑ a₁ : α₁, (macJointDistribution p₁ p₂ W).real {(a₁, a₂, b)} := by
    rw [← hF_coe, ← sum_measureReal_singleton (μ := macJointDistribution p₁ p₂ W) F, hF_def,
      Finset.sum_image (by intro a _ a' _ h; exact (Prod.mk.injEq _ _ _ _).mp h |>.1)]
  rw [h_sum]
  rw [Finset.sum_congr rfl (fun a₁ _ ↦ macJointDistribution_triple_singleton p₁ p₂ W a₁ a₂ b)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a₁ _ ↦ ?_)
  ring

/-- The `X₁`-block law under the MAC ambient measure equals `Measure.pi p₁`. -/
lemma mac_block_law_X1
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] (n : ℕ) :
    (macAmbientMeasure p₁ p₂ W).map (jointRV macX1s n)
      = Measure.pi (fun _ : Fin n ↦ p₁) := by
  refine block_law_X_eq_pi_p (macAmbientMeasure p₁ p₂ W) macX1s measurable_macX1s ?_ ?_ p₁ ?_ n
  · exact macAmbient_iIndepFun_coord p₁ p₂ W Prod.fst measurable_fst
  · exact fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W Prod.fst measurable_fst i
  · rw [show (macX1s 0 : (ℕ → α₁ × α₂ × β) → α₁) = fun ω ↦ Prod.fst (ω 0) from rfl,
      macAmbient_map_coord p₁ p₂ W Prod.fst measurable_fst 0, macJointDistribution_map_fst]

/-- The `(X₂, Y)`-joint-block law singleton mass factorizes over coordinates as a
product of the per-coordinate `(X₂, Y)` marginal masses. -/
lemma mac_block_law_X2Y_singleton
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (n : ℕ) (x₂ : Fin n → α₂) (y : Fin n → β) :
    ((macAmbientMeasure p₁ p₂ W).map
        (fun ω ↦ (jointRV macX2s n ω, jointRV macYs n ω))).real {(x₂, y)}
      = ∏ i, ((macJointDistribution p₁ p₂ W).map
          (fun q : α₁ × α₂ × β ↦ (q.2.1, q.2.2))).real {(x₂ i, y i)} := by
  classical
  set μ : Measure (ℕ → α₁ × α₂ × β) := macAmbientMeasure p₁ p₂ W with hμ_def
  set νXY : Measure (α₂ × β) :=
    (macJointDistribution p₁ p₂ W).map (fun q : α₁ × α₂ × β ↦ (q.2.1, q.2.2)) with hνXY_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  haveI : IsProbabilityMeasure νXY := by
    rw [hνXY_def]
    exact Measure.isProbabilityMeasure_map
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_snd.comp measurable_snd)).aemeasurable
  set g₀ : (ℕ → α₁ × α₂ × β) → (Fin n → α₂) × (Fin n → β) :=
    fun ω ↦ (jointRV macX2s n ω, jointRV macYs n ω) with hg₀_def
  set ê : (Fin n → α₂) × (Fin n → β) → (Fin n → α₂ × β) :=
    fun q i ↦ (q.1 i, q.2 i) with hê_def
  have hg₀_meas : Measurable g₀ :=
    (measurable_jointRV macX2s measurable_macX2s n).prodMk
      (measurable_jointRV macYs measurable_macYs n)
  have hê_meas : Measurable ê :=
    measurable_pi_lambda _ fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
  -- The reshaped block law is the pi power of the per-coordinate (X₂,Y) marginal.
  set ρ : Measure (Fin n → α₂ × β) :=
    μ.map (jointRV (jointSequence macX2s macYs) n) with hρ_def
  have hρ_eq : ρ = Measure.pi (fun _ : Fin n ↦ νXY) := by
    refine block_law_X_eq_pi_p μ (jointSequence macX2s macYs)
      (fun i ↦ measurable_jointSequence macX2s macYs measurable_macX2s measurable_macYs i)
      ?_ ?_ νXY ?_ n
    · exact macAmbient_iIndepFun_coord p₁ p₂ W (fun q ↦ (q.2.1, q.2.2))
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
    · exact fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.2.1, q.2.2))
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)) i
    · rw [show (jointSequence macX2s macYs 0 : (ℕ → α₁ × α₂ × β) → α₂ × β)
            = fun ω ↦ (fun q : α₁ × α₂ × β ↦ (q.2.1, q.2.2)) (ω 0) from rfl,
        macAmbient_map_coord p₁ p₂ W (fun q ↦ (q.2.1, q.2.2))
          ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)) 0,
        hνXY_def]
  -- νA2.map ê = ρ.
  have hν_eq_ρ : (μ.map g₀).map ê = ρ := by
    rw [Measure.map_map hê_meas hg₀_meas, hρ_def]
    congr 1
  -- The reshape preimage of a singleton is a singleton.
  have h_pre : ê ⁻¹' {ê (x₂, y)} = {((x₂, y) : (Fin n → α₂) × (Fin n → β))} := by
    ext ⟨u, v⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have hu : u = x₂ := by funext i; exact (Prod.mk.injEq _ _ _ _).mp (congrFun h i) |>.1
      have hv : v = y := by funext i; exact (Prod.mk.injEq _ _ _ _).mp (congrFun h i) |>.2
      rw [hu, hv]
    · intro h; rw [h]
  calc (μ.map g₀).real {(x₂, y)}
      = (μ.map g₀).real (ê ⁻¹' {ê (x₂, y)}) := by rw [h_pre]
    _ = ((μ.map g₀).map ê).real {ê (x₂, y)} :=
        (map_measureReal_apply hê_meas (measurableSet_singleton _)).symm
    _ = ρ.real {ê (x₂, y)} := by rw [hν_eq_ρ]
    _ = (Measure.pi (fun _ : Fin n ↦ νXY)).real {fun i ↦ (x₂ i, y i)} := by rw [hρ_eq]
    _ = ∏ i, νXY.real {(x₂ i, y i)} := measureReal_pi_singleton_eq_prod _ _

/-- **Pair-channel conditional-output fold-in (singleton form).**  The `(X₂, Y)`-joint
block-law mass at `(x₂, y)` equals the average over the true user-1 codeword `x₁ ~ p₁ⁿ`
of the paired-channel output mass at `y`, weighted by the user-2 codeword mass.  This is
the genuine novelty of the two-codebook averaging: the true user-1 input is marginalized
out of the pair channel `W(·, x₂ i)` to recover the conditional `(X₂, Y)` output law. -/
lemma mac_chan_fold_one
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (n : ℕ) (x₂ : Fin n → α₂) (y : Fin n → β) :
    ((macAmbientMeasure p₁ p₂ W).map
        (fun ω ↦ (jointRV macX2s n ω, jointRV macYs n ω))).real {(x₂, y)}
      = ∑ x₁ : Fin n → α₁, (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
          * (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
          * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y} := by
  classical
  have hP₁ : ∀ x₁ : Fin n → α₁,
      (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁} = ∏ i, p₁.real {x₁ i} :=
    fun x₁ ↦ measureReal_pi_singleton_eq_prod _ _
  have hP₂ : (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂} = ∏ i, p₂.real {x₂ i} :=
    measureReal_pi_singleton_eq_prod _ _
  have hPW : ∀ x₁ : Fin n → α₁,
      (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y} = ∏ i, (W (x₁ i, x₂ i)).real {y i} :=
    fun x₁ ↦ measureReal_pi_singleton_eq_prod _ _
  -- LHS: block law singleton, then per-coordinate (X₂,Y) marginal expansion.
  rw [mac_block_law_X2Y_singleton p₁ p₂ W n x₂ y,
    Finset.prod_congr rfl (fun i _ ↦ macJointDistribution_X2Y_singleton p₁ p₂ W (x₂ i) (y i)),
    Finset.prod_mul_distrib]
  -- RHS: fold the true user-1 codeword into the per-coordinate sum.
  symm
  have h_pi_sum : (∏ i, ∑ a₁ : α₁, p₁.real {a₁} * (W (a₁, x₂ i)).real {y i})
      = ∑ x₁ : Fin n → α₁, ∏ i, (p₁.real {x₁ i} * (W (x₁ i, x₂ i)).real {y i}) := by
    have h := (Finset.prod_univ_sum
      (κ := fun _ : Fin n ↦ α₁)
      (t := fun _ : Fin n ↦ (Finset.univ : Finset α₁))
      (R := ℝ)
      (f := fun (i : Fin n) (a₁ : α₁) ↦ p₁.real {a₁} * (W (a₁, x₂ i)).real {y i}))
    have h_pi : Fintype.piFinset (fun _ : Fin n ↦ (Finset.univ : Finset α₁))
        = (Finset.univ : Finset (Fin n → α₁)) := by ext c; simp
    rw [h_pi] at h
    exact h
  calc ∑ x₁ : Fin n → α₁, (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
          * (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
          * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y}
      = ∑ x₁ : Fin n → α₁, (∏ i, p₂.real {x₂ i})
          * ∏ i, (p₁.real {x₁ i} * (W (x₁ i, x₂ i)).real {y i}) := by
        refine Finset.sum_congr rfl (fun x₁ _ ↦ ?_)
        rw [hP₁ x₁, hP₂, hPW x₁, Finset.prod_mul_distrib]
        ring
    _ = (∏ i, p₂.real {x₂ i})
          * ∑ x₁ : Fin n → α₁, ∏ i, (p₁.real {x₁ i} * (W (x₁ i, x₂ i)).real {y i}) := by
        rw [Finset.mul_sum]
    _ = (∏ i, p₂.real {x₂ i})
          * ∏ i, ∑ a₁ : α₁, p₁.real {a₁} * (W (a₁, x₂ i)).real {y i} := by
        rw [h_pi_sum]

/-- Set-level version of the conditional-output fold-in: the `(X₂, Y)`-joint block law of
a finite set `T` equals the user-2-weighted average over the true user-1 codeword of the
paired-channel mass of the `x₂`-slice of `T`. -/
lemma mac_chan_fold_set
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (n : ℕ) (T : Set ((Fin n → α₂) × (Fin n → β))) :
    ((macAmbientMeasure p₁ p₂ W).map
        (fun ω ↦ (jointRV macX2s n ω, jointRV macYs n ω))).real T
      = ∑ x₂ : Fin n → α₂, ∑ x₁ : Fin n → α₁,
          (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
            * (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
            * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₂, y) ∈ T} := by
  classical
  set νA2 : Measure ((Fin n → α₂) × (Fin n → β)) :=
    (macAmbientMeasure p₁ p₂ W).map (fun ω ↦ (jointRV macX2s n ω, jointRV macYs n ω))
    with hνA2_def
  haveI : IsProbabilityMeasure νA2 := by
    rw [hνA2_def]
    exact Measure.isProbabilityMeasure_map
      ((measurable_jointRV macX2s measurable_macX2s n).prodMk
        (measurable_jointRV macYs measurable_macYs n)).aemeasurable
  classical
  -- Enumerate the LHS as an indicator double sum.
  have h_enum : νA2.real T
      = ∑ x₂ : Fin n → α₂, ∑ y : Fin n → β,
          (if (x₂, y) ∈ T then νA2.real {(x₂, y)} else 0) := by
    rw [measureReal_eq_sum_ite νA2 T, Fintype.sum_prod_type]
  rw [h_enum]
  refine Finset.sum_congr rfl (fun x₂ _ ↦ ?_)
  -- LHS per `x₂`: apply the singleton fold-in inside the indicator.
  have hL : (∑ y : Fin n → β, (if (x₂, y) ∈ T then νA2.real {(x₂, y)} else 0))
      = ∑ y : Fin n → β, (if (x₂, y) ∈ T then
          (∑ x₁ : Fin n → α₁, (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
            * (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
            * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y}) else 0) := by
    refine Finset.sum_congr rfl (fun y _ ↦ ?_)
    rw [hνA2_def, mac_chan_fold_one p₁ p₂ W n x₂ y]
  rw [hL]
  symm
  -- RHS per `x₂`: slice the paired-channel mass and reorder the sums.
  calc ∑ x₁ : Fin n → α₁, (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
          * (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
          * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₂, y) ∈ T}
      = ∑ x₁ : Fin n → α₁, ∑ y : Fin n → β,
          (if (x₂, y) ∈ T then (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
            * (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
            * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y} else 0) := by
        refine Finset.sum_congr rfl (fun x₁ _ ↦ ?_)
        rw [measureReal_eq_sum_ite (Measure.pi (fun i ↦ W (x₁ i, x₂ i))) {y | (x₂, y) ∈ T},
          Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ ↦ ?_)
        simp only [Set.mem_setOf_eq, mul_ite, mul_zero]
    _ = ∑ y : Fin n → β, ∑ x₁ : Fin n → α₁,
          (if (x₂, y) ∈ T then (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
            * (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
            * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y} else 0) := Finset.sum_comm
    _ = ∑ y : Fin n → β, (if (x₂, y) ∈ T then
          (∑ x₁ : Fin n → α₁, (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
            * (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
            * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y}) else 0) := by
        refine Finset.sum_congr rfl (fun y _ ↦ ?_)
        rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
        by_cases h : (x₂, y) ∈ T
        · rw [if_pos h, if_pos h]
          refine Finset.sum_congr rfl (fun x₁ _ ↦ ?_); ring
        · rw [if_neg h, if_neg h]

/-- The second-input marginal of the per-coordinate MAC joint law is `p₂`. -/
lemma macJointDistribution_map_X2
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] :
    (macJointDistribution p₁ p₂ W).map (fun q : α₁ × α₂ × β ↦ q.2.1) = p₂ := by
  unfold macJointDistribution
  rw [Measure.map_map (show Measurable (fun q : α₁ × α₂ × β ↦ q.2.1) from
        measurable_fst.comp measurable_snd) MeasurableEquiv.prodAssoc.measurable]
  have h_comp : ((fun q : α₁ × α₂ × β ↦ q.2.1) ∘ (MeasurableEquiv.prodAssoc :
      (α₁ × α₂) × β ≃ᵐ α₁ × α₂ × β))
      = (Prod.snd : α₁ × α₂ → α₂) ∘ (Prod.fst : (α₁ × α₂) × β → α₁ × α₂) := by
    funext r; rfl
  rw [h_comp, ← Measure.map_map measurable_snd measurable_fst]
  have h1 : (jointDistribution (p₁.prod p₂) W).map Prod.fst = p₁.prod p₂ := by
    show (jointDistribution (p₁.prod p₂) W).fst = p₁.prod p₂
    rw [jointDistribution_def]
    exact Measure.fst_compProd _ _
  rw [h1]
  show (p₁.prod p₂).snd = p₂
  exact Measure.snd_prod

/-- The `X₂`-block law under the MAC ambient measure equals `Measure.pi p₂`. -/
lemma mac_block_law_X2
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W] (n : ℕ) :
    (macAmbientMeasure p₁ p₂ W).map (jointRV macX2s n)
      = Measure.pi (fun _ : Fin n ↦ p₂) := by
  refine block_law_X_eq_pi_p (macAmbientMeasure p₁ p₂ W) macX2s measurable_macX2s ?_ ?_ p₂ ?_ n
  · exact macAmbient_iIndepFun_coord p₁ p₂ W (fun q ↦ q.2.1) (measurable_fst.comp measurable_snd)
  · exact fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ q.2.1)
      (measurable_fst.comp measurable_snd) i
  · rw [show (macX2s 0 : (ℕ → α₁ × α₂ × β) → α₂) = fun ω ↦ (fun q : α₁ × α₂ × β ↦ q.2.1) (ω 0)
        from rfl,
      macAmbient_map_coord p₁ p₂ W (fun q ↦ q.2.1) (measurable_fst.comp measurable_snd) 0,
      macJointDistribution_map_X2]

/-- Full-triple split block-law singleton mass factorizes over coordinates as a product of
the per-coordinate MAC joint masses. -/
lemma mac_block_law_triple_singleton
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (n : ℕ) (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) (y : Fin n → β) :
    ((macAmbientMeasure p₁ p₂ W).map
        (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω))).real {(x₁, x₂, y)}
      = ∏ i, (macJointDistribution p₁ p₂ W).real {(x₁ i, x₂ i, y i)} := by
  classical
  set μ : Measure (ℕ → α₁ × α₂ × β) := macAmbientMeasure p₁ p₂ W with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  set g₀ : (ℕ → α₁ × α₂ × β) → (Fin n → α₁) × (Fin n → α₂) × (Fin n → β) :=
    fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω) with hg₀_def
  set ê : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β) → (Fin n → α₁ × α₂ × β) :=
    fun q i ↦ (q.1 i, q.2.1 i, q.2.2 i) with hê_def
  have hg₀_meas : Measurable g₀ :=
    (measurable_jointRV macX1s measurable_macX1s n).prodMk
      ((measurable_jointRV macX2s measurable_macX2s n).prodMk
        (measurable_jointRV macYs measurable_macYs n))
  have hê_meas : Measurable ê :=
    measurable_pi_lambda _ fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).prodMk
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))
  set ρ : Measure (Fin n → α₁ × α₂ × β) :=
    μ.map (jointRV (macJointSequence macX1s macX2s macYs) n) with hρ_def
  have hρ_eq : ρ = Measure.pi (fun _ : Fin n ↦ macJointDistribution p₁ p₂ W) := by
    refine block_law_X_eq_pi_p μ (macJointSequence macX1s macX2s macYs)
      (fun i ↦ measurable_macJointSequence macX1s macX2s macYs
        measurable_macX1s measurable_macX2s measurable_macYs i)
      ?_ ?_ (macJointDistribution p₁ p₂ W) ?_ n
    · exact macAmbient_iIndepFun_coord p₁ p₂ W id measurable_id
    · exact fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W id measurable_id i
    · rw [show (macJointSequence macX1s macX2s macYs 0 : (ℕ → α₁ × α₂ × β) → α₁ × α₂ × β)
            = fun ω ↦ id (ω 0) from rfl,
        macAmbient_map_coord p₁ p₂ W id measurable_id 0, Measure.map_id]
  have hν_eq_ρ : (μ.map g₀).map ê = ρ := by
    rw [Measure.map_map hê_meas hg₀_meas, hρ_def]
    congr 1
  have h_pre : ê ⁻¹' {ê (x₁, x₂, y)}
      = {((x₁, x₂, y) : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β))} := by
    ext ⟨u, v, w⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have hu : u = x₁ := by funext i; exact congrArg (·.1) (congrFun h i)
      have hv : v = x₂ := by funext i; exact congrArg (fun p ↦ p.2.1) (congrFun h i)
      have hw : w = y := by funext i; exact congrArg (fun p ↦ p.2.2) (congrFun h i)
      rw [hu, hv, hw]
    · intro h; rw [h]
  calc (μ.map g₀).real {(x₁, x₂, y)}
      = (μ.map g₀).real (ê ⁻¹' {ê (x₁, x₂, y)}) := by rw [h_pre]
    _ = ((μ.map g₀).map ê).real {ê (x₁, x₂, y)} :=
        (map_measureReal_apply hê_meas (measurableSet_singleton _)).symm
    _ = ρ.real {ê (x₁, x₂, y)} := by rw [hν_eq_ρ]
    _ = (Measure.pi (fun _ : Fin n ↦ macJointDistribution p₁ p₂ W)).real
          {fun i ↦ (x₁ i, x₂ i, y i)} := by rw [hρ_eq]
    _ = ∏ i, (macJointDistribution p₁ p₂ W).real {(x₁ i, x₂ i, y i)} :=
        measureReal_pi_singleton_eq_prod _ _

/-- **Master pair-channel fold (full triple).**  The full-triple split block law of a finite
set `T` equals the average over the true codeword pair `(x₁, x₂) ~ p₁ⁿ ⊗ p₂ⁿ` of the
paired-channel mass of the corresponding slice of `T`. -/
lemma mac_chan_fold_triple_set
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (n : ℕ) (T : Set ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β))) :
    ((macAmbientMeasure p₁ p₂ W).map
        (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω))).real T
      = ∑ x₁ : Fin n → α₁, ∑ x₂ : Fin n → α₂,
          (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
            * (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
            * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₁, x₂, y) ∈ T} := by
  classical
  set νt : Measure ((Fin n → α₁) × (Fin n → α₂) × (Fin n → β)) :=
    (macAmbientMeasure p₁ p₂ W).map
      (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω)) with hνt_def
  haveI : IsProbabilityMeasure νt := by
    rw [hνt_def]
    exact Measure.isProbabilityMeasure_map
      ((measurable_jointRV macX1s measurable_macX1s n).prodMk
        ((measurable_jointRV macX2s measurable_macX2s n).prodMk
          (measurable_jointRV macYs measurable_macYs n))).aemeasurable
  -- Per-coordinate factorization of the full-triple singleton mass.
  have h_single : ∀ (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) (y : Fin n → β),
      νt.real {(x₁, x₂, y)}
        = (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
          * (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
          * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y} := by
    intro x₁ x₂ y
    rw [hνt_def, mac_block_law_triple_singleton p₁ p₂ W n x₁ x₂ y,
      Finset.prod_congr rfl (fun i _ ↦
        macJointDistribution_triple_singleton p₁ p₂ W (x₁ i) (x₂ i) (y i)),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      ← measureReal_pi_singleton_eq_prod (fun _ : Fin n ↦ p₁) x₁,
      ← measureReal_pi_singleton_eq_prod (fun _ : Fin n ↦ p₂) x₂,
      ← measureReal_pi_singleton_eq_prod (fun i ↦ W (x₁ i, x₂ i)) y]
  -- Enumerate the LHS as an indicator triple sum, then collapse the output sum.
  rw [hνt_def] at *
  rw [measureReal_eq_sum_ite νt T, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x₁ _ ↦ ?_)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x₂ _ ↦ ?_)
  rw [measureReal_eq_sum_ite (Measure.pi (fun i ↦ W (x₁ i, x₂ i))) {y | (x₁, x₂, y) ∈ T},
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ ↦ ?_)
  simp only [Set.mem_setOf_eq]
  rw [h_single x₁ x₂ y]
  by_cases h : (x₁, x₂, y) ∈ T
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- The `(X₁, Y)`-split joint block-law fold, derived from the master triple fold by
projecting out `X₂`. -/
lemma mac_chan_fold_X1Y_set
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (n : ℕ) (T : Set ((Fin n → α₁) × (Fin n → β))) :
    ((macAmbientMeasure p₁ p₂ W).map
        (fun ω ↦ (jointRV macX1s n ω, jointRV macYs n ω))).real T
      = ∑ x₁ : Fin n → α₁, ∑ x₂ : Fin n → α₂,
          (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
            * (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
            * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | (x₁, y) ∈ T} := by
  classical
  have hmeas_triple : Measurable (fun ω : ℕ → α₁ × α₂ × β ↦
      (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω)) :=
    (measurable_jointRV macX1s measurable_macX1s n).prodMk
      ((measurable_jointRV macX2s measurable_macX2s n).prodMk
        (measurable_jointRV macYs measurable_macYs n))
  have hproj_meas : Measurable
      (fun t : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β) ↦ (t.1, t.2.2)) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hmap : (macAmbientMeasure p₁ p₂ W).map (fun ω ↦ (jointRV macX1s n ω, jointRV macYs n ω))
      = ((macAmbientMeasure p₁ p₂ W).map
          (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω))).map
        (fun t ↦ (t.1, t.2.2)) := by
    rw [Measure.map_map hproj_meas hmeas_triple]; rfl
  rw [hmap, map_measureReal_apply hproj_meas (Set.toFinite T).measurableSet,
    mac_chan_fold_triple_set p₁ p₂ W n ((fun t ↦ (t.1, t.2.2)) ⁻¹' T)]
  simp only [Set.mem_preimage]

/-- The `Y`-block-law fold, derived from the master triple fold by projecting out both
inputs. -/
lemma mac_chan_fold_Y_set
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (n : ℕ) (T : Set (Fin n → β)) :
    ((macAmbientMeasure p₁ p₂ W).map (jointRV macYs n)).real T
      = ∑ x₁ : Fin n → α₁, ∑ x₂ : Fin n → α₂,
          (Measure.pi (fun _ : Fin n ↦ p₁)).real {x₁}
            * (Measure.pi (fun _ : Fin n ↦ p₂)).real {x₂}
            * (Measure.pi (fun i ↦ W (x₁ i, x₂ i))).real {y | y ∈ T} := by
  classical
  have hmeas_triple : Measurable (fun ω : ℕ → α₁ × α₂ × β ↦
      (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω)) :=
    (measurable_jointRV macX1s measurable_macX1s n).prodMk
      ((measurable_jointRV macX2s measurable_macX2s n).prodMk
        (measurable_jointRV macYs measurable_macYs n))
  have hproj_meas : Measurable
      (fun t : (Fin n → α₁) × (Fin n → α₂) × (Fin n → β) ↦ t.2.2) :=
    measurable_snd.comp measurable_snd
  have hmap : (macAmbientMeasure p₁ p₂ W).map (jointRV macYs n)
      = ((macAmbientMeasure p₁ p₂ W).map
          (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω, jointRV macYs n ω))).map
        (fun t ↦ t.2.2) := by
    rw [Measure.map_map hproj_meas hmeas_triple]; rfl
  rw [hmap, map_measureReal_apply hproj_meas (Set.toFinite T).measurableSet,
    mac_chan_fold_triple_set p₁ p₂ W n ((fun t ↦ t.2.2) ⁻¹' T)]
  simp only [Set.mem_preimage]

/-- The `(X₁, X₂)`-split joint block-law singleton mass equals `p₁ⁿ{x₁} · p₂ⁿ{x₂}`, derived
from the master triple fold by projecting out the output. -/
lemma mac_block_law_X1X2_singleton
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (n : ℕ) (xa : Fin n → α₁) (xb : Fin n → α₂) :
    ((macAmbientMeasure p₁ p₂ W).map
        (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω))).real {(xa, xb)}
      = (Measure.pi (fun _ : Fin n ↦ p₁)).real {xa}
          * (Measure.pi (fun _ : Fin n ↦ p₂)).real {xb} := by
  classical
  set μ : Measure (ℕ → α₁ × α₂ × β) := macAmbientMeasure p₁ p₂ W with hμ_def
  haveI : IsProbabilityMeasure μ := by rw [hμ_def]; infer_instance
  set g₀ : (ℕ → α₁ × α₂ × β) → (Fin n → α₁) × (Fin n → α₂) :=
    fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω) with hg₀_def
  set ê : (Fin n → α₁) × (Fin n → α₂) → (Fin n → α₁ × α₂) :=
    fun q i ↦ (q.1 i, q.2 i) with hê_def
  have hg₀_meas : Measurable g₀ :=
    (measurable_jointRV macX1s measurable_macX1s n).prodMk
      (measurable_jointRV macX2s measurable_macX2s n)
  have hê_meas : Measurable ê :=
    measurable_pi_lambda _ fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
  have hmap12 : (macJointDistribution p₁ p₂ W).map (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1))
      = p₁.prod p₂ := by
    unfold macJointDistribution
    rw [Measure.map_map (show Measurable (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) from
          measurable_fst.prodMk (measurable_fst.comp measurable_snd))
        MeasurableEquiv.prodAssoc.measurable]
    have h_comp : ((fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) ∘ (MeasurableEquiv.prodAssoc :
        (α₁ × α₂) × β ≃ᵐ α₁ × α₂ × β)) = (Prod.fst : (α₁ × α₂) × β → α₁ × α₂) := by
      funext r; rfl
    rw [h_comp]
    show (jointDistribution (p₁.prod p₂) W).fst = p₁.prod p₂
    rw [jointDistribution_def]
    exact Measure.fst_compProd _ _
  set ρ : Measure (Fin n → α₁ × α₂) :=
    μ.map (jointRV (jointSequence macX1s macX2s) n) with hρ_def
  have hρ_eq : ρ = Measure.pi (fun _ : Fin n ↦ p₁.prod p₂) := by
    refine block_law_X_eq_pi_p μ (jointSequence macX1s macX2s)
      (fun i ↦ measurable_jointSequence macX1s macX2s measurable_macX1s measurable_macX2s i)
      ?_ ?_ (p₁.prod p₂) ?_ n
    · exact macAmbient_iIndepFun_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1))
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    · exact fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1))
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) i
    · rw [show (jointSequence macX1s macX2s 0 : (ℕ → α₁ × α₂ × β) → α₁ × α₂)
            = fun ω ↦ (fun q : α₁ × α₂ × β ↦ (q.1, q.2.1)) (ω 0) from rfl,
        macAmbient_map_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1))
          (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) 0,
        hmap12]
  have hν_eq_ρ : (μ.map g₀).map ê = ρ := by
    rw [Measure.map_map hê_meas hg₀_meas, hρ_def]
    congr 1
  have h_pre : ê ⁻¹' {ê (xa, xb)} = {((xa, xb) : (Fin n → α₁) × (Fin n → α₂))} := by
    ext ⟨u, v⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      have hu : u = xa := by funext i; exact (Prod.mk.injEq _ _ _ _).mp (congrFun h i) |>.1
      have hv : v = xb := by funext i; exact (Prod.mk.injEq _ _ _ _).mp (congrFun h i) |>.2
      rw [hu, hv]
    · intro h; rw [h]
  calc (μ.map g₀).real {(xa, xb)}
      = (μ.map g₀).real (ê ⁻¹' {ê (xa, xb)}) := by rw [h_pre]
    _ = ((μ.map g₀).map ê).real {ê (xa, xb)} :=
        (map_measureReal_apply hê_meas (measurableSet_singleton _)).symm
    _ = ρ.real {ê (xa, xb)} := by rw [hν_eq_ρ]
    _ = (Measure.pi (fun _ : Fin n ↦ p₁.prod p₂)).real {fun i ↦ (xa i, xb i)} := by rw [hρ_eq]
    _ = ∏ i, (p₁.prod p₂).real {(xa i, xb i)} := measureReal_pi_singleton_eq_prod _ _
    _ = ∏ i, (p₁.real {xa i} * p₂.real {xb i}) := by
        refine Finset.prod_congr rfl (fun i _ ↦ ?_)
        rw [← Set.singleton_prod_singleton, measureReal_prod_prod]
    _ = (∏ i, p₁.real {xa i}) * (∏ i, p₂.real {xb i}) := Finset.prod_mul_distrib
    _ = (Measure.pi (fun _ : Fin n ↦ p₁)).real {xa}
          * (Measure.pi (fun _ : Fin n ↦ p₂)).real {xb} := by
        rw [measureReal_pi_singleton_eq_prod (fun _ : Fin n ↦ p₁) xa,
          measureReal_pi_singleton_eq_prod (fun _ : Fin n ↦ p₂) xb]

/-- **Split-form restatement of the user-2 gateway atom.**  The reshaped-product /
preimage-set conclusion of `macJTS_indep_prob_le_X2` recast over the split product
`X₂-block ⊗ (X₁, Y)-joint-block`. -/
lemma macJTS_indep_prob_le_X2_split
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((macAmbientMeasure p₁ p₂ W).map (jointRV macX2s n)).prod
        ((macAmbientMeasure p₁ p₂ W).map
          (fun ω ↦ (jointRV macX1s n ω, jointRV macYs n ω)))).real
        {q : (Fin n → α₂) × ((Fin n → α₁) × (Fin n → β)) |
          (q.2.1, q.1, q.2.2) ∈
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε}
      ≤ Real.exp ((n : ℝ) *
          ((entropy (macAmbientMeasure p₁ p₂ W) (macJointSequence macX1s macX2s macYs 0)
            - entropy (macAmbientMeasure p₁ p₂ W) (macX2s 0)
            - entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX1s macYs 0)) + 3 * ε)) := by
  classical
  set ê : (Fin n → α₁) × (Fin n → β) → (Fin n → α₁ × β) :=
    fun q i ↦ (q.1 i, q.2 i) with hê_def
  have hê_meas : Measurable ê :=
    measurable_pi_lambda _ fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
  set μX2 : Measure (Fin n → α₂) := (macAmbientMeasure p₁ p₂ W).map (jointRV macX2s n)
    with hμX2_def
  set νsplit : Measure ((Fin n → α₁) × (Fin n → β)) :=
    (macAmbientMeasure p₁ p₂ W).map (fun ω ↦ (jointRV macX1s n ω, jointRV macYs n ω))
    with hνsplit_def
  haveI : IsProbabilityMeasure μX2 :=
    Measure.isProbabilityMeasure_map (measurable_jointRV macX2s measurable_macX2s n).aemeasurable
  haveI : IsProbabilityMeasure νsplit :=
    Measure.isProbabilityMeasure_map ((measurable_jointRV macX1s measurable_macX1s n).prodMk
      (measurable_jointRV macYs measurable_macYs n)).aemeasurable
  -- The gateway atom (reshaped form).
  have h_gw := macJTS_indep_prob_le_X2 (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs
    measurable_macX1s measurable_macX2s measurable_macYs
    (macAmbient_iIndepFun_coord p₁ p₂ W (fun q ↦ q.2.1) (measurable_fst.comp measurable_snd))
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ q.2.1)
      (measurable_fst.comp measurable_snd) i)
    (macAmbient_iIndepFun_coord p₁ p₂ W (fun q ↦ (q.1, q.2.2))
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.1, q.2.2))
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) i)
    (fun x ↦ macAmbient_map_coord_real_singleton_pos p₁ p₂ W hp₁ hp₂ hW (fun q ↦ q.2.1)
      (measurable_fst.comp measurable_snd) 0 x (Classical.arbitrary α₁, x, Classical.arbitrary β) rfl)
    (fun q ↦ macAmbient_map_coord_real_singleton_pos p₁ p₂ W hp₁ hp₂ hW (fun r ↦ (r.1, r.2.2))
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) 0 q
      (q.1, Classical.arbitrary α₂, q.2) rfl)
    (fun q ↦ macAmbient_map_coord_real_singleton_pos p₁ p₂ W hp₁ hp₂ hW
      (fun r ↦ (r.2.1, r.1, r.2.2))
      ((measurable_fst.comp measurable_snd).prodMk
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))) 0 q
      (q.2.1, q.1, q.2.2) rfl)
    n hε
  -- Pushforward of the split `(X₁, Y)` block law through the reshape.
  have h_push : νsplit.map ê
      = (macAmbientMeasure p₁ p₂ W).map (jointRV (jointSequence macX1s macYs) n) := by
    rw [hνsplit_def, Measure.map_map hê_meas ((measurable_jointRV macX1s measurable_macX1s n).prodMk
      (measurable_jointRV macYs measurable_macYs n))]
    rfl
  have h_prodpush : (μX2.prod νsplit).map (Prod.map (@id (Fin n → α₂)) ê)
      = μX2.prod ((macAmbientMeasure p₁ p₂ W).map (jointRV (jointSequence macX1s macYs) n)) := by
    have hmp := Measure.map_prod_map μX2 νsplit (measurable_id) hê_meas
    rw [Measure.map_id, h_push] at hmp
    exact hmp.symm
  have hE_meas : Measurable (Prod.map (@id (Fin n → α₂)) ê) := measurable_id.prodMap hê_meas
  calc (μX2.prod νsplit).real
          {q : (Fin n → α₂) × ((Fin n → α₁) × (Fin n → β)) |
            (q.2.1, q.1, q.2.2) ∈
              macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε}
      = (μX2.prod νsplit).real ((Prod.map (@id (Fin n → α₂)) ê) ⁻¹'
          ((fun q : (Fin n → α₂) × (Fin n → α₁ × β) ↦
              (((fun i ↦ (q.2 i).1) : Fin n → α₁),
                (q.1, ((fun i ↦ (q.2 i).2) : Fin n → β)))) ⁻¹'
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε)) := rfl
    _ = ((μX2.prod νsplit).map (Prod.map (@id (Fin n → α₂)) ê)).real
          ((fun q : (Fin n → α₂) × (Fin n → α₁ × β) ↦
              (((fun i ↦ (q.2 i).1) : Fin n → α₁),
                (q.1, ((fun i ↦ (q.2 i).2) : Fin n → β)))) ⁻¹'
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε) :=
        (map_measureReal_apply hE_meas (Set.toFinite _).measurableSet).symm
    _ = (μX2.prod ((macAmbientMeasure p₁ p₂ W).map
          (jointRV (jointSequence macX1s macYs) n))).real
          ((fun q : (Fin n → α₂) × (Fin n → α₁ × β) ↦
              (((fun i ↦ (q.2 i).1) : Fin n → α₁),
                (q.1, ((fun i ↦ (q.2 i).2) : Fin n → β)))) ⁻¹'
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε) := by
        rw [h_prodpush]
    _ ≤ _ := h_gw

/-- **Split-form restatement of the both-users gateway atom.**  The reshaped-product /
preimage-set conclusion of `macJTS_indep_prob_le_both` recast over the split product
`(X₁, X₂)-joint-block ⊗ Y-block`. -/
lemma macJTS_indep_prob_le_both_split
    (p₁ : Measure α₁) [IsProbabilityMeasure p₁]
    (p₂ : Measure α₂) [IsProbabilityMeasure p₂]
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (hp₁ : ∀ a : α₁, 0 < p₁.real {a}) (hp₂ : ∀ a : α₂, 0 < p₂.real {a})
    (hW : ∀ a : α₁ × α₂, ∀ b : β, 0 < (W a).real {b})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((macAmbientMeasure p₁ p₂ W).map
          (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω))).prod
        ((macAmbientMeasure p₁ p₂ W).map (jointRV macYs n))).real
        {q : ((Fin n → α₁) × (Fin n → α₂)) × (Fin n → β) |
          (q.1.1, q.1.2, q.2) ∈
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε}
      ≤ Real.exp ((n : ℝ) *
          ((entropy (macAmbientMeasure p₁ p₂ W) (macJointSequence macX1s macX2s macYs 0)
            - entropy (macAmbientMeasure p₁ p₂ W) (jointSequence macX1s macX2s 0)
            - entropy (macAmbientMeasure p₁ p₂ W) (macYs 0)) + 3 * ε)) := by
  classical
  set ê : (Fin n → α₁) × (Fin n → α₂) → (Fin n → α₁ × α₂) :=
    fun q i ↦ (q.1 i, q.2 i) with hê_def
  have hê_meas : Measurable ê :=
    measurable_pi_lambda _ fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
  set νsplit12 : Measure ((Fin n → α₁) × (Fin n → α₂)) :=
    (macAmbientMeasure p₁ p₂ W).map (fun ω ↦ (jointRV macX1s n ω, jointRV macX2s n ω))
    with hνsplit12_def
  set μY : Measure (Fin n → β) := (macAmbientMeasure p₁ p₂ W).map (jointRV macYs n)
    with hμY_def
  haveI : IsProbabilityMeasure νsplit12 :=
    Measure.isProbabilityMeasure_map ((measurable_jointRV macX1s measurable_macX1s n).prodMk
      (measurable_jointRV macX2s measurable_macX2s n)).aemeasurable
  haveI : IsProbabilityMeasure μY :=
    Measure.isProbabilityMeasure_map (measurable_jointRV macYs measurable_macYs n).aemeasurable
  -- The gateway atom (reshaped form).
  have h_gw := macJTS_indep_prob_le_both (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs
    measurable_macX1s measurable_macX2s measurable_macYs
    (macAmbient_iIndepFun_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ (q.1, q.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) i)
    (macAmbient_iIndepFun_coord p₁ p₂ W (fun q ↦ q.2.2) (measurable_snd.comp measurable_snd))
    (fun i ↦ macAmbient_identDistrib_coord p₁ p₂ W (fun q ↦ q.2.2)
      (measurable_snd.comp measurable_snd) i)
    (fun q ↦ macAmbient_map_coord_real_singleton_pos p₁ p₂ W hp₁ hp₂ hW (fun r ↦ (r.1, r.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) 0 q
      (q.1, q.2, Classical.arbitrary β) rfl)
    (fun y ↦ macAmbient_map_coord_real_singleton_pos p₁ p₂ W hp₁ hp₂ hW (fun r ↦ r.2.2)
      (measurable_snd.comp measurable_snd) 0 y (Classical.arbitrary α₁, Classical.arbitrary α₂, y) rfl)
    (fun q ↦ macAmbient_map_coord_real_singleton_pos p₁ p₂ W hp₁ hp₂ hW
      (fun r ↦ ((r.1, r.2.1), r.2.2))
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)) 0 q
      (q.1.1, q.1.2, q.2) rfl)
    n hε
  -- Pushforward of the split `(X₁, X₂)` block law through the reshape.
  have h_push : νsplit12.map ê
      = (macAmbientMeasure p₁ p₂ W).map (jointRV (jointSequence macX1s macX2s) n) := by
    rw [hνsplit12_def, Measure.map_map hê_meas ((measurable_jointRV macX1s measurable_macX1s n).prodMk
      (measurable_jointRV macX2s measurable_macX2s n))]
    rfl
  have h_prodpush : (νsplit12.prod μY).map (Prod.map ê (@id (Fin n → β)))
      = ((macAmbientMeasure p₁ p₂ W).map (jointRV (jointSequence macX1s macX2s) n)).prod μY := by
    have hmp := Measure.map_prod_map νsplit12 μY hê_meas (measurable_id)
    rw [Measure.map_id, h_push] at hmp
    exact hmp.symm
  have hE_meas : Measurable (Prod.map ê (@id (Fin n → β))) := hê_meas.prodMap measurable_id
  calc (νsplit12.prod μY).real
          {q : ((Fin n → α₁) × (Fin n → α₂)) × (Fin n → β) |
            (q.1.1, q.1.2, q.2) ∈
              macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε}
      = (νsplit12.prod μY).real ((Prod.map ê (@id (Fin n → β))) ⁻¹'
          ((fun q : (Fin n → α₁ × α₂) × (Fin n → β) ↦
              (((fun i ↦ (q.1 i).1) : Fin n → α₁),
                (((fun i ↦ (q.1 i).2) : Fin n → α₂), q.2))) ⁻¹'
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε)) := rfl
    _ = ((νsplit12.prod μY).map (Prod.map ê (@id (Fin n → β)))).real
          ((fun q : (Fin n → α₁ × α₂) × (Fin n → β) ↦
              (((fun i ↦ (q.1 i).1) : Fin n → α₁),
                (((fun i ↦ (q.1 i).2) : Fin n → α₂), q.2))) ⁻¹'
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε) :=
        (map_measureReal_apply hE_meas (Set.toFinite _).measurableSet).symm
    _ = (((macAmbientMeasure p₁ p₂ W).map (jointRV (jointSequence macX1s macX2s) n)).prod μY).real
          ((fun q : (Fin n → α₁ × α₂) × (Fin n → β) ↦
              (((fun i ↦ (q.1 i).1) : Fin n → α₁),
                (((fun i ↦ (q.1 i).2) : Fin n → α₂), q.2))) ⁻¹'
            macJointlyTypicalSet (macAmbientMeasure p₁ p₂ W) macX1s macX2s macYs n ε) := by
        rw [h_prodpush]
    _ ≤ _ := h_gw

end InformationTheory.Shannon.MAC
