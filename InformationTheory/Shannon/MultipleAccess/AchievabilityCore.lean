import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MultipleAccess.JointTypicality

/-!
# Multiple access channel — achievability analytic core

The conditional independent-pair probability bounds `E1` / `E2` / `E3` for the two-user
MAC random-coding argument (Cover–Thomas §15.3.1).  These are the genuinely analytic
ingredient of MAC achievability; the rest of the achievability proof (Bonferroni union
bound + two-codebook averaging) is plumbing over these bounds.

## Approach

Each `Eⱼ` is a regrouping instance of the single-user independent-pair bound
`InformationTheory.Shannon.ChannelCoding.jointlyTypicalSet_indep_prob_le`.  For `E1`
(user 1 uses a wrong codeword `X̃₁ ⟂ (X₂, Y)`), the three-way jointly typical set
`macJointlyTypicalSet` is contained, under the reshape
`(x₁, x₂, y) ↦ (x₁, fun i ↦ (x₂ i, y i))`, in the single-user jointly typical set
`jointlyTypicalSet μ X₁s (jointSequence X₂s Ys)` (treating the pair `(X₂, Y)` as the
single "output" axis).  Measure monotonicity plus the product-measure pushforward
identity `Measure.map_prod_map` then reduce the bound to the single-user lemma, whose
exit form is exactly the desired `H`-form exponent
`H(X₁, X₂, Y) − H(X₁) − H(X₂, Y) + 3ε`.
-/

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **E1 — user-1 conditional independent-pair bound.**  When user 1's codeword `X̃₁` is
drawn independently of the jointly distributed pair `(X₂, Y)`, the probability that the
triple lands in the three-way jointly typical set is at most
`exp(n·(H(X₁,X₂,Y) − H(X₁) − H(X₂,Y) + 3ε))`.

The measure is the product of user 1's block law and the joint block law of `(X₂, Y)`.
The exponent is the single-user exit form; combined with input independence (downstream)
it equals `exp(-n·(I(X₁;Y|X₂) − 3ε))`. -/
@[entry_point]
theorem macJTS_indep_prob_le_X1
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i))
    (hindepX1 : iIndepFun (fun i ↦ X1s i) μ)
    (hidentX1 : ∀ i, IdentDistrib (X1s i) (X1s 0) μ μ)
    (hindepX2Y : iIndepFun (fun i ↦ jointSequence X2s Ys i) μ)
    (hidentX2Y : ∀ i, IdentDistrib (jointSequence X2s Ys i) (jointSequence X2s Ys 0) μ μ)
    (hposX1 : ∀ x : α₁, 0 < (μ.map (X1s 0)).real {x})
    (hposX2Y : ∀ p : α₂ × β, 0 < (μ.map (jointSequence X2s Ys 0)).real {p})
    (hposZ : ∀ p : α₁ × α₂ × β,
      0 < (μ.map (macJointSequence X1s X2s Ys 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((μ.map (jointRV X1s n)).prod
        (μ.map (fun ω ↦ (jointRV X2s n ω, jointRV Ys n ω)))).real
        (macJointlyTypicalSet μ X1s X2s Ys n ε)
      ≤ Real.exp ((n : ℝ) *
          ((entropy μ (macJointSequence X1s X2s Ys 0)
            - entropy μ (X1s 0)
            - entropy μ (jointSequence X2s Ys 0)) + 3 * ε)) := by
  classical
  -- Block laws.
  set μX1 : Measure (Fin n → α₁) := μ.map (jointRV X1s n) with hμX1_def
  set g : Ω → (Fin n → α₂) × (Fin n → β) :=
    fun ω ↦ (jointRV X2s n ω, jointRV Ys n ω) with hg_def
  have hg_meas : Measurable g :=
    (measurable_jointRV X2s hX2s n).prodMk (measurable_jointRV Ys hYs n)
  set νA2 : Measure ((Fin n → α₂) × (Fin n → β)) := μ.map g with hνA2_def
  -- Measurability of the regrouped "output" sequence `(X₂, Y)`.
  have hX2Ys : ∀ i, Measurable ((jointSequence X2s Ys) i) := fun i ↦
    measurable_jointSequence X2s Ys hX2s hYs i
  -- The reshape `(x₂, y) ↦ (fun i ↦ (x₂ i, y i))`.
  set ê : (Fin n → α₂) × (Fin n → β) → (Fin n → α₂ × β) :=
    fun q i ↦ (q.1 i, q.2 i) with hê_def
  have hê_meas : Measurable ê :=
    measurable_pi_lambda _ fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
  -- The single-user independent-pair bound on the regrouped jointly typical set.
  have key := jointlyTypicalSet_indep_prob_le μ X1s (jointSequence X2s Ys) hX1s hX2Ys
    hindepX1 hidentX1 hindepX2Y hidentX2Y hposX1 hposX2Y hposZ n hε
  -- Probability-measure instances (for product σ-finiteness / finiteness).
  haveI hμX1prob : IsProbabilityMeasure μX1 :=
    Measure.isProbabilityMeasure_map (measurable_jointRV X1s hX1s n).aemeasurable
  haveI hνA2prob : IsProbabilityMeasure νA2 :=
    Measure.isProbabilityMeasure_map hg_meas.aemeasurable
  haveI : IsProbabilityMeasure (μX1.prod νA2) := by infer_instance
  -- Inclusion `macJTS ⊆ (Prod.map id ê) ⁻¹' (single-user JTS)`.
  have h_incl : macJointlyTypicalSet μ X1s X2s Ys n ε ⊆
      (Prod.map (@id (Fin n → α₁)) ê) ⁻¹' (jointlyTypicalSet μ X1s (jointSequence X2s Ys) n ε) := by
    intro p hp
    obtain ⟨h1, _h2, _h3, _h4, _h5, h6, h7⟩ := hp
    exact ⟨h1, h6, h7⟩
  -- Pushforward of the `(X₂, Y)` block law through the reshape.
  have h_push : νA2.map ê = μ.map (jointRV (jointSequence X2s Ys) n) := by
    rw [hνA2_def, Measure.map_map hê_meas hg_meas]
    rfl
  -- Product pushforward identity `(μX1 × νA2).map (id × ê) = μX1 × (X₂,Y)-block-law`.
  have h_prodpush : (μX1.prod νA2).map (Prod.map (@id (Fin n → α₁)) ê)
      = μX1.prod (μ.map (jointRV (jointSequence X2s Ys) n)) := by
    have hmp := Measure.map_prod_map μX1 νA2 (measurable_id) hê_meas
    rw [Measure.map_id, h_push] at hmp
    exact hmp.symm
  have hE_meas : Measurable (Prod.map (@id (Fin n → α₁)) ê) :=
    measurable_id.prodMap hê_meas
  have hJTSB_meas : MeasurableSet (jointlyTypicalSet μ X1s (jointSequence X2s Ys) n ε) :=
    measurableSet_jointlyTypicalSet μ X1s (jointSequence X2s Ys) n ε
  -- Reduce to the single-user bound; rewrite the three-way entropy to the regrouped form.
  rw [macJointSequence_eq]
  calc (μX1.prod νA2).real (macJointlyTypicalSet μ X1s X2s Ys n ε)
      ≤ (μX1.prod νA2).real ((Prod.map (@id (Fin n → α₁)) ê) ⁻¹'
          (jointlyTypicalSet μ X1s (jointSequence X2s Ys) n ε)) := measureReal_mono h_incl
    _ = ((μX1.prod νA2).map (Prod.map (@id (Fin n → α₁)) ê)).real
          (jointlyTypicalSet μ X1s (jointSequence X2s Ys) n ε) :=
        (map_measureReal_apply hE_meas hJTSB_meas).symm
    _ = (μX1.prod (μ.map (jointRV (jointSequence X2s Ys) n))).real
          (jointlyTypicalSet μ X1s (jointSequence X2s Ys) n ε) := by rw [h_prodpush]
    _ ≤ _ := key

/-- Relabeling invariance of the typical set: along a measurable equivalence `e` of finite
alphabets, a block is typical iff its `e`-image is typical for the `e`-relabeled sequence.
Both the empirical `pmfLog` sum and the true entropy are invariant under `e`. -/
private lemma typicalSet_relabel
    {γ δ : Type*}
    [Fintype γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    [Fintype δ] [Nonempty δ] [MeasurableSpace δ] [MeasurableSingletonClass δ]
    (μ : Measure Ω) (Zs : ℕ → Ω → γ) (hZs : ∀ i, Measurable (Zs i)) (e : γ ≃ᵐ δ)
    (n : ℕ) (ε : ℝ) (z : Fin n → γ)
    (hz : z ∈ InformationTheory.Shannon.typicalSet μ Zs n ε) :
    (fun i ↦ e (z i)) ∈
      InformationTheory.Shannon.typicalSet μ (fun i ω ↦ e (Zs i ω)) n ε := by
  rw [InformationTheory.Shannon.mem_typicalSet_iff] at hz ⊢
  -- The relabeled marginal singleton mass at `e x` equals the original at `x`.
  have hsingle : ∀ x : γ,
      (μ.map (fun ω ↦ e ((Zs 0) ω))).real {e x} = (μ.map (Zs 0)).real {x} := by
    intro x
    rw [show (fun ω ↦ e ((Zs 0) ω)) = (e : γ → δ) ∘ (Zs 0) from rfl,
      ← Measure.map_map e.measurable (hZs 0),
      map_measureReal_apply e.measurable (measurableSet_singleton _)]
    congr 1
    ext w
    simp [e.injective.eq_iff]
  -- `pmfLog` of the relabeled sequence at `e x` equals `pmfLog` of `Zs` at `x`.
  have hpmf : ∀ x : γ,
      InformationTheory.Shannon.pmfLog μ (fun i ω ↦ e (Zs i ω)) (e x)
        = InformationTheory.Shannon.pmfLog μ Zs x := by
    intro x
    change -Real.log ((μ.map (fun ω ↦ e ((Zs 0) ω))).real {e x})
        = -Real.log ((μ.map (Zs 0)).real {x})
    rw [hsingle x]
  -- The entropy term is invariant under `e`.
  have hent : InformationTheory.Shannon.entropy μ ((fun i ω ↦ e (Zs i ω)) 0)
      = InformationTheory.Shannon.entropy μ (Zs 0) :=
    entropy_measurableEquiv_comp μ (Zs 0) (hZs 0) e
  -- Rewrite both terms in the goal and conclude from `hz`.
  rw [hent]
  simp only [hpmf]
  exact hz

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **E3 — both-users conditional independent-pair bound.**  When the pair of codewords
`(X̃₁, X̃₂)` is drawn independently of the output block `Y`, the probability that the
(reshuffled) triple lands in the three-way jointly typical set is at most
`exp(n·(H(X₁,X₂,Y) − H(X₁,X₂) − H(Y) + 3ε))`.

This is the direct three-axis analogue of the single-user independent-pair bound, with the
`(X₁,X₂)` axes grouped as the "input" and `Y` as the "output".  Combined with input
independence (downstream) the exponent equals `exp(-n·(I(X₁,X₂;Y) − 3ε))`. -/
@[entry_point]
theorem macJTS_indep_prob_le_both
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i))
    (hindepX1X2 : iIndepFun (fun i ↦ jointSequence X1s X2s i) μ)
    (hidentX1X2 : ∀ i, IdentDistrib (jointSequence X1s X2s i) (jointSequence X1s X2s 0) μ μ)
    (hindepY : iIndepFun (fun i ↦ Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hposX1X2 : ∀ p : α₁ × α₂, 0 < (μ.map (jointSequence X1s X2s 0)).real {p})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : (α₁ × α₂) × β,
      0 < (μ.map (jointSequence (jointSequence X1s X2s) Ys 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((μ.map (jointRV (jointSequence X1s X2s) n)).prod (μ.map (jointRV Ys n))).real
        ((fun q : (Fin n → α₁ × α₂) × (Fin n → β) ↦
            (((fun i ↦ (q.1 i).1) : Fin n → α₁),
              (((fun i ↦ (q.1 i).2) : Fin n → α₂), q.2))) ⁻¹'
          macJointlyTypicalSet μ X1s X2s Ys n ε)
      ≤ Real.exp ((n : ℝ) *
          ((entropy μ (macJointSequence X1s X2s Ys 0)
            - entropy μ (jointSequence X1s X2s 0)
            - entropy μ (Ys 0)) + 3 * ε)) := by
  classical
  -- Cheap associator equiv `(a, b, c) ↦ ((a, b), c)` (direct projections keep `whnf` fast).
  let e₃ : (α₁ × α₂ × β) ≃ᵐ (α₁ × α₂) × β :=
    { toFun := fun p ↦ ((p.1, p.2.1), p.2.2)
      invFun := fun p ↦ (p.1.1, p.1.2, p.2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun :=
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd)
      measurable_invFun :=
        (measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd) }
  -- Convert `e₃`-relabeled sequences to the left-associated form by *cheap per-point* `rfl`
  -- (so `entropy` / `typicalSet` never get unfolded during unification).
  have hseq0 : (fun ω ↦ e₃ (macJointSequence X1s X2s Ys 0 ω))
      = jointSequence (jointSequence X1s X2s) Ys 0 := by funext ω; rfl
  have hseq : (fun (i : ℕ) (ω : Ω) ↦ e₃ (macJointSequence X1s X2s Ys i ω))
      = jointSequence (jointSequence X1s X2s) Ys := by funext i ω; rfl
  -- The canonical three-joint entropy equals the left-associated one.
  have h_ent3 : entropy μ (macJointSequence X1s X2s Ys 0)
      = entropy μ (jointSequence (jointSequence X1s X2s) Ys 0) := by
    rw [← hseq0]
    exact (entropy_measurableEquiv_comp μ (macJointSequence X1s X2s Ys 0)
      (measurable_macJointSequence X1s X2s Ys hX1s hX2s hYs 0) e₃).symm
  -- Single-user independent-pair bound for the regrouped axes `(X₁,X₂) ⟂ Y`.
  have key := jointlyTypicalSet_indep_prob_le μ (jointSequence X1s X2s) Ys
    (fun i ↦ measurable_jointSequence X1s X2s hX1s hX2s i) hYs
    hindepX1X2 hidentX1X2 hindepY hidentY hposX1X2 hposY hposZ n hε
  haveI : IsProbabilityMeasure (μ.map (jointRV (jointSequence X1s X2s) n)) :=
    Measure.isProbabilityMeasure_map
      (measurable_jointRV (jointSequence X1s X2s)
        (fun i ↦ measurable_jointSequence X1s X2s hX1s hX2s i) n).aemeasurable
  haveI : IsProbabilityMeasure (μ.map (jointRV Ys n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV Ys hYs n).aemeasurable
  -- Inclusion of the reshaped macJTS into the single-user jointly typical set.
  have h_incl : (fun q : (Fin n → α₁ × α₂) × (Fin n → β) ↦
        (((fun i ↦ (q.1 i).1) : Fin n → α₁),
          (((fun i ↦ (q.1 i).2) : Fin n → α₂), q.2))) ⁻¹'
        macJointlyTypicalSet μ X1s X2s Ys n ε ⊆
      jointlyTypicalSet μ (jointSequence X1s X2s) Ys n ε := by
    intro q hq
    obtain ⟨_h1, _h2, h3, h4, _h5, _h6, h7⟩ := hq
    refine ⟨h4, h3, ?_⟩
    have hbridge := typicalSet_relabel μ (macJointSequence X1s X2s Ys)
      (measurable_macJointSequence X1s X2s Ys hX1s hX2s hYs) e₃ n ε
      (fun i ↦ ((q.1 i).1, ((q.1 i).2, q.2 i))) h7
    have helem : (fun i ↦ e₃ ((q.1 i).1, ((q.1 i).2, q.2 i)))
        = (fun i ↦ (q.1 i, q.2 i)) := by funext i; rfl
    rw [hseq, helem] at hbridge
    exact hbridge
  rw [h_ent3]
  exact le_trans (measureReal_mono h_incl) key

omit [DecidableEq α₁] [DecidableEq α₂] [DecidableEq β] in
/-- **E2 — user-2 conditional independent-pair bound.**  When user 2's codeword `X̃₂` is
drawn independently of the jointly distributed pair `(X₁, Y)`, the probability that the
(reshuffled) triple lands in the three-way jointly typical set is at most
`exp(n·(H(X₁,X₂,Y) − H(X₂) − H(X₁,Y) + 3ε))`.

This is the user-1/user-2 mirror image of `macJTS_indep_prob_le_X1`, with `(X₁, Y)` as the
jointly distributed "output" axis.  Combined with input independence (downstream) the
exponent equals `exp(-n·(I(X₂;Y|X₁) − 3ε))`. -/
@[entry_point]
theorem macJTS_indep_prob_le_X2
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X1s : ℕ → Ω → α₁) (X2s : ℕ → Ω → α₂) (Ys : ℕ → Ω → β)
    (hX1s : ∀ i, Measurable (X1s i)) (hX2s : ∀ i, Measurable (X2s i))
    (hYs : ∀ i, Measurable (Ys i))
    (hindepX2 : iIndepFun (fun i ↦ X2s i) μ)
    (hidentX2 : ∀ i, IdentDistrib (X2s i) (X2s 0) μ μ)
    (hindepX1Y : iIndepFun (fun i ↦ jointSequence X1s Ys i) μ)
    (hidentX1Y : ∀ i, IdentDistrib (jointSequence X1s Ys i) (jointSequence X1s Ys 0) μ μ)
    (hposX2 : ∀ x : α₂, 0 < (μ.map (X2s 0)).real {x})
    (hposX1Y : ∀ p : α₁ × β, 0 < (μ.map (jointSequence X1s Ys 0)).real {p})
    (hposZ : ∀ p : α₂ × α₁ × β,
      0 < (μ.map (jointSequence X2s (jointSequence X1s Ys) 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((μ.map (jointRV X2s n)).prod (μ.map (jointRV (jointSequence X1s Ys) n))).real
        ((fun q : (Fin n → α₂) × (Fin n → α₁ × β) ↦
            (((fun i ↦ (q.2 i).1) : Fin n → α₁),
              (q.1, ((fun i ↦ (q.2 i).2) : Fin n → β)))) ⁻¹'
          macJointlyTypicalSet μ X1s X2s Ys n ε)
      ≤ Real.exp ((n : ℝ) *
          ((entropy μ (macJointSequence X1s X2s Ys 0)
            - entropy μ (X2s 0)
            - entropy μ (jointSequence X1s Ys 0)) + 3 * ε)) := by
  classical
  -- Cheap permutation equiv `(a, b, c) ↦ (b, a, c)` (direct projections keep `whnf` fast).
  let e₂ : (α₁ × α₂ × β) ≃ᵐ α₂ × α₁ × β :=
    { toFun := fun p ↦ (p.2.1, (p.1, p.2.2))
      invFun := fun p ↦ (p.2.1, (p.1, p.2.2))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      measurable_toFun :=
        (measurable_fst.comp measurable_snd).prodMk
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
      measurable_invFun :=
        (measurable_fst.comp measurable_snd).prodMk
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd)) }
  have hseq0 : (fun ω ↦ e₂ (macJointSequence X1s X2s Ys 0 ω))
      = jointSequence X2s (jointSequence X1s Ys) 0 := by funext ω; rfl
  have hseq : (fun (i : ℕ) (ω : Ω) ↦ e₂ (macJointSequence X1s X2s Ys i ω))
      = jointSequence X2s (jointSequence X1s Ys) := by funext i ω; rfl
  have h_ent2 : entropy μ (macJointSequence X1s X2s Ys 0)
      = entropy μ (jointSequence X2s (jointSequence X1s Ys) 0) := by
    rw [← hseq0]
    exact (entropy_measurableEquiv_comp μ (macJointSequence X1s X2s Ys 0)
      (measurable_macJointSequence X1s X2s Ys hX1s hX2s hYs 0) e₂).symm
  have key := jointlyTypicalSet_indep_prob_le μ X2s (jointSequence X1s Ys)
    hX2s (fun i ↦ measurable_jointSequence X1s Ys hX1s hYs i)
    hindepX2 hidentX2 hindepX1Y hidentX1Y hposX2 hposX1Y hposZ n hε
  haveI : IsProbabilityMeasure (μ.map (jointRV X2s n)) :=
    Measure.isProbabilityMeasure_map (measurable_jointRV X2s hX2s n).aemeasurable
  haveI : IsProbabilityMeasure (μ.map (jointRV (jointSequence X1s Ys) n)) :=
    Measure.isProbabilityMeasure_map
      (measurable_jointRV (jointSequence X1s Ys)
        (fun i ↦ measurable_jointSequence X1s Ys hX1s hYs i) n).aemeasurable
  have h_incl : (fun q : (Fin n → α₂) × (Fin n → α₁ × β) ↦
        (((fun i ↦ (q.2 i).1) : Fin n → α₁),
          (q.1, ((fun i ↦ (q.2 i).2) : Fin n → β)))) ⁻¹'
        macJointlyTypicalSet μ X1s X2s Ys n ε ⊆
      jointlyTypicalSet μ X2s (jointSequence X1s Ys) n ε := by
    intro q hq
    obtain ⟨_h1, h2, _h3, _h4, h5, _h6, h7⟩ := hq
    refine ⟨h2, h5, ?_⟩
    have hbridge := typicalSet_relabel μ (macJointSequence X1s X2s Ys)
      (measurable_macJointSequence X1s X2s Ys hX1s hX2s hYs) e₂ n ε
      (fun i ↦ ((q.2 i).1, (q.1 i, (q.2 i).2))) h7
    have helem : (fun i ↦ e₂ ((q.2 i).1, (q.1 i, (q.2 i).2)))
        = (fun i ↦ (q.1 i, q.2 i)) := by funext i; rfl
    rw [hseq, helem] at hbridge
    exact hbridge
  rw [h_ent2]
  exact le_trans (measureReal_mono h_incl) key

end InformationTheory.Shannon.MAC
