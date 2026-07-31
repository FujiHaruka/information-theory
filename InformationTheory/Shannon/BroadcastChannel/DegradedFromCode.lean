import InformationTheory.Shannon.BroadcastChannel.Converse
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Bridge
import InformationTheory.Shannon.BroadcastChannel.Achievability.Setup

/-!
# Broadcast channel — the degraded converse at the ambient of a code

Physical degradedness of a broadcast channel says every letter of receiver 2's output is a
stochastic function of the corresponding letter of receiver 1's output.  On the ambient measure
of a block code this upgrades to a statement about whole blocks: receiver 2's output block is
appended to receiver 1's by the blockwise product of the degrading kernel, so at every letter
the receiver-2 prefix is conditionally independent of the current receiver-1 letter given
message 2 and the receiver-1 prefix.  That conditional independence is exactly the structural
hypothesis of the degraded converse, which therefore lands at a bare broadcast code.

## Main statements

* `bcConverse_degradedBlock` — under physical degradedness the letter-`i` output of receiver 1
  is conditionally independent of the receiver-2 prefix given message 2 and the receiver-1
  prefix, on the ambient measure of a broadcast code.  This is the hypothesis `h_deg_block` of
  `bc_degraded_converse` at `bcConverseAmbient`.
* `bc_degraded_converse_from_code` — the degraded outer bound (Cover–Thomas Thm 15.6.2) at a
  bare broadcast code, with the auxiliary `Uᵢ = (W₂, Y₂^{i-1})` read off the ambient.

## Implementation notes

Degradedness enters only through the degrading kernel it provides, and that kernel is applied
to the whole output block before the block identity is cut down to a prefix:
`bcConverse_block_append` appends the entire receiver-2 block to `(messages, Y₁ⁿ)` by the
blockwise product `piBlockKernel` of that kernel, and `bcConverse_prefix_append` reindexes the
resulting identity along the injection of `Fin i` into `Fin n`.  The block form is the one the
product structure of the ambient gives directly, so keeping the two steps apart separates the
product-measure recombination from the reindexing.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators

variable {α : Type*} [MeasurableSpace α]
variable {β₁ : Type*} [Fintype β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
variable {β₂ : Type*} [Fintype β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]
variable {M₁ M₂ n : ℕ}

/-! ## Appending the degraded output block -/

lemma bcConverse_block_append
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (Q : Kernel β₁ β₂) [IsMarkovKernel Q]
    (hQ : ∀ a : α, W a = ((W a).map Prod.fst).bind fun y₁ ↦ (Q y₁).map fun y₂ ↦ (y₁, y₂)) :
    (bcConverseAmbient c W).map
        (fun ω ↦ ((ω.1, fun j ↦ bcConverseY₁s j ω), fun j ↦ bcConverseY₂s j ω))
      = ((bcConverseAmbient c W).map (fun ω ↦ (ω.1, fun j ↦ bcConverseY₁s j ω)))
          ⊗ₘ Kernel.prodMkLeft (Fin M₁ × Fin M₂) (piBlockKernel Q) := by
  classical
  have hunzip : Measurable
      (fun (y : Fin n → β₁ × β₂) ↦ ((fun j ↦ (y j).1), (fun j ↦ (y j).2))) := by fun_prop
  have hy₁ : Measurable (fun (y : Fin n → β₁ × β₂) (j : Fin n) ↦ (y j).1) := by fun_prop
  have hprob : ∀ (m : Fin M₁ × Fin M₂) (j : Fin n),
      IsProbabilityMeasure ((W (c.encoder m j)).map Prod.fst) :=
    fun _ _ ↦ Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hproj : ∀ m : Fin M₁ × Fin M₂,
      (Measure.pi fun j ↦ W (c.encoder m j)).map (fun y j ↦ (y j).1)
        = Measure.pi fun j ↦ (W (c.encoder m j)).map Prod.fst := by
    intro m
    haveI := hprob m
    have h := congrArg (fun ρ ↦ ρ.map Prod.fst)
      (pi_map_unzip_eq_compProd Q (fun j ↦ W (c.encoder m j)) fun j ↦ hQ _)
    rw [Measure.map_map measurable_fst hunzip] at h
    exact h.trans (Measure.fst_compProd _ _)
  have hker : (bcConverseKernel c W).map
        (fun (y : Fin n → β₁ × β₂) ↦ ((fun j ↦ (y j).1), (fun j ↦ (y j).2)))
      = ((bcConverseKernel c W).map fun (y : Fin n → β₁ × β₂) (j : Fin n) ↦ (y j).1)
          ⊗ₖ Kernel.prodMkLeft (Fin M₁ × Fin M₂) (piBlockKernel Q) := by
    ext m : 1
    haveI := hprob m
    rw [Kernel.map_apply _ hunzip, Kernel.compProd_apply_eq_compProd_sectR,
      Kernel.map_apply _ hy₁]
    have hsect : Kernel.sectR (Kernel.prodMkLeft (Fin M₁ × Fin M₂) (piBlockKernel Q)) m
        = piBlockKernel (k := n) Q := rfl
    rw [hsect, show bcConverseKernel c W m = Measure.pi fun j ↦ W (c.encoder m j) from rfl,
      hproj m]
    exact pi_map_unzip_eq_compProd Q (fun j ↦ W (c.encoder m j)) fun j ↦ hQ _
  have hΦ : (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦
        ((ω.1, fun j ↦ bcConverseY₁s j ω), fun j ↦ bcConverseY₂s j ω))
      = ⇑MeasurableEquiv.prodAssoc.symm ∘
        Prod.map id (fun (y : Fin n → β₁ × β₂) ↦ ((fun j ↦ (y j).1), (fun j ↦ (y j).2))) := rfl
  rw [hΦ, ← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable (by fun_prop),
    bcConverseAmbient, ← Measure.compProd_map hunzip, hker, Measure.compProd_assoc,
    Measure.compProd_map hy₁]
  rfl

lemma bcConverse_prefix_append
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (Q : Kernel β₁ β₂) [IsMarkovKernel Q]
    (hQ : ∀ a : α, W a = ((W a).map Prod.fst).bind fun y₁ ↦ (Q y₁).map fun y₂ ↦ (y₁, y₂))
    (i : Fin n) :
    (bcConverseAmbient c W).map
        (fun ω ↦ (((bcConverseMsg₂ ω,
            fun (j : Fin i.val) ↦ bcConverseY₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω),
          bcConverseY₁s i ω),
          fun (j : Fin i.val) ↦ bcConverseY₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      = ((bcConverseAmbient c W).map
          (fun ω ↦ ((bcConverseMsg₂ ω,
              fun (j : Fin i.val) ↦ bcConverseY₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω),
            bcConverseY₁s i ω)))
          ⊗ₘ Kernel.prodMkRight β₁ (Kernel.prodMkLeft (Fin M₂) (piBlockKernel Q)) := by
  classical
  have he : Function.Injective
      (fun (j : Fin i.val) ↦ (⟨j.val, j.isLt.trans i.isLt⟩ : Fin n)) := by
    intro j k hjk
    simp only [Fin.mk.injEq] at hjk
    exact Fin.val_injective hjk
  have hg₁ : Measurable (fun (p : (Fin M₁ × Fin M₂) × (Fin n → β₁)) ↦
      ((p.1.2, fun (j : Fin i.val) ↦ p.2 ⟨j.val, j.isLt.trans i.isLt⟩), p.2 i)) := by fun_prop
  have hg₂ : Measurable
      (fun (v : Fin n → β₂) (j : Fin i.val) ↦ v ⟨j.val, j.isLt.trans i.isLt⟩) := by fun_prop
  have hκ : (Kernel.prodMkLeft (Fin M₁ × Fin M₂) (piBlockKernel (k := n) Q)).map
        (fun (v : Fin n → β₂) (j : Fin i.val) ↦ v ⟨j.val, j.isLt.trans i.isLt⟩)
      = (Kernel.prodMkRight β₁
          (Kernel.prodMkLeft (Fin M₂) (piBlockKernel (k := i.val) Q))).comap _ hg₁ := by
    ext p : 1
    rw [Kernel.map_apply _ hg₂, Kernel.comap_apply]
    exact pi_map_comp_of_injective (fun j ↦ Q (p.2 j)) _ he
  have hΦ : (fun ω : (Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂) ↦
        (((bcConverseMsg₂ ω,
            fun (j : Fin i.val) ↦ bcConverseY₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω),
          bcConverseY₁s i ω),
          fun (j : Fin i.val) ↦ bcConverseY₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      = Prod.map
          (fun (p : (Fin M₁ × Fin M₂) × (Fin n → β₁)) ↦
            ((p.1.2, fun (j : Fin i.val) ↦ p.2 ⟨j.val, j.isLt.trans i.isLt⟩), p.2 i))
          (fun (v : Fin n → β₂) (j : Fin i.val) ↦ v ⟨j.val, j.isLt.trans i.isLt⟩) ∘
        fun ω ↦ ((ω.1, fun j ↦ bcConverseY₁s j ω), fun j ↦ bcConverseY₂s j ω) := rfl
  rw [hΦ, ← Measure.map_map (hg₁.prodMap hg₂) (by fun_prop),
    bcConverse_block_append c W Q hQ, compProd_map_prodMap _ _ hg₁ hg₂ _ hκ,
    Measure.map_map hg₁ (by fun_prop)]
  rfl

/-! ## The degraded converse at a code -/

section Degraded

variable [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace β₁] [Nonempty β₁]
variable [StandardBorelSpace β₂] [Nonempty β₂]

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α] in
lemma bcConverse_degradedBlock
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (hdeg : IsBCDegraded W) (i : Fin n) :
    IsMarkovChain (bcConverseAmbient c W) (bcConverseY₁s i)
      (fun ω ↦ (bcConverseMsg₂ ω,
        fun (j : Fin i.val) ↦ bcConverseY₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      (fun ω (j : Fin i.val) ↦ bcConverseY₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω) := by
  obtain ⟨Q, hQmarkov, hQ⟩ := hdeg
  haveI := hQmarkov
  exact isMarkovChain_of_append (bcConverseAmbient c W) (bcConverseY₁s i)
    (fun ω ↦ (bcConverseMsg₂ ω,
      fun (j : Fin i.val) ↦ bcConverseY₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
    (fun ω (j : Fin i.val) ↦ bcConverseY₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω)
    (measurable_bcConverseY₁s i)
    (measurable_bcConverseMsg₂.prodMk
      (measurable_pi_iff.mpr fun j ↦ measurable_bcConverseY₁s _))
    (measurable_pi_iff.mpr fun j ↦ measurable_bcConverseY₂s _)
    (Kernel.prodMkLeft (Fin M₂) (piBlockKernel Q))
    (bcConverse_prefix_append c W Q hQ i)

/-- The degraded outer bound instantiated at a bare broadcast code (Cover–Thomas Thm 15.6.2):
for a physically degraded Markov channel `W` and any two-receiver block code `c`, the canonical
ambient measure `bcConverseAmbient c W` discharges every hypothesis of the message-level
converse `bc_degraded_converse`, so the rate pair `(log M₁, log M₂)` lies in the auxiliary-variable
capacity region whose information bounds are the per-letter sums `∑ᵢ I(Xᵢ; Y_{1,i} | Uᵢ)` and
`∑ᵢ I(Uᵢ; Y_{2,i})` with `Uᵢ = (W₂, Y₂^{i-1})`.  Degradedness is consumed only through
`bcConverse_degradedBlock`, so beyond it the hypotheses are the two message counts.  The Fano
slack is still carried here; it vanishes only in the `n → ∞` limit. -/
@[entry_point]
theorem bc_degraded_converse_from_code
    [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hdeg : IsBCDegraded W) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InBCCapacityRegion (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((∑ i : Fin n,
          condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i) (bcConverseY₁s i)
            (fun ω ↦ (bcConverseMsg₂ ω,
              fun (j : Fin i.val) ↦ bcConverseY₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))).toReal
        + bcConverseFanoSlack₁ c W)
      ((∑ i : Fin n,
          mutualInfo (bcConverseAmbient c W)
            (fun ω ↦ (bcConverseMsg₂ ω,
              fun (j : Fin i.val) ↦ bcConverseY₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
            (bcConverseY₂s i)).toReal
        + bcConverseFanoSlack₂ c W) := by
  have h := bc_degraded_converse (bcConverseAmbient c W) bcConverseMsg₁ bcConverseMsg₂
    bcConverseY₁s bcConverseY₂s c
    measurable_bcConverseMsg₁ measurable_bcConverseMsg₂
    measurable_bcConverseY₁s measurable_bcConverseY₂s
    (bcConverseMsg₁_uniform c W) (bcConverseMsg₂_uniform c W)
    (bcConverse_mutualInfo_eq_zero c W)
    (bcConverse_memoryless₁ c W) (bcConverse_degradedBlock c W hdeg)
    (bcConverse_isMarkovChain₁ c W) hcard₁ hcard₂
  refine ⟨?_, ?_⟩
  · have h₁ := h.bound₁
    rw [add_assoc] at h₁
    exact h₁
  · have h₂ := h.bound₂
    rw [add_assoc] at h₂
    exact h₂

end Degraded

end InformationTheory.Shannon.BroadcastChannel
