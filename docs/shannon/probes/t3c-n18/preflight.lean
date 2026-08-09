/-
PROBE — not an in-project asset (nothing under `InformationTheory/` imports this file).

Preflight for the N18 leg: is `thm7Region W` inhabited?  The closedness statements the leg is
trying to discharge are vacuously true if the region is empty, so a membership witness has to be
built before the closedness verdict can be read.

Run:  lake env lean docs/shannon/probes/t3c-n18/preflight.lean
-/
import InformationTheory.Shannon.BroadcastChannel.Thm7Region

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel
open InformationTheory.Shannon.BroadcastChannel.Marton

namespace ProbeThm7N18

universe u

section Helpers

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : Type*} [MeasurableSpace X]
variable {Y : Type*} [MeasurableSpace Y]
variable {Z : Type*} [MeasurableSpace Z]

lemma ae_eq_const_of_map_eq_dirac [MeasurableSingletonClass X] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → X) (hf : Measurable f) (c : X)
    (h : μ.map f = Measure.dirac c) : f =ᵐ[μ] fun _ ↦ c := by
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨f ⁻¹' {c}, ?_, fun ω hω ↦ hω⟩
  rw [mem_ae_iff, ← Set.preimage_compl, ← Measure.map_apply hf (measurableSet_singleton c).compl,
    h, Measure.dirac_apply' _ (measurableSet_singleton c).compl]
  simp

lemma mutualInfo_eq_zero_of_ae_const (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo)
    (c : X) (hc : Xs =ᵐ[μ] fun _ ↦ c) : mutualInfo μ Xs Yo = 0 := by
  rw [mutualInfo_eq_zero_iff_indep μ Xs Yo hXs hYo]
  exact (indepFun_const_left c Yo).congr hc.symm (Filter.EventuallyEq.refl _ _)

lemma condMutualInfo_eq_zero_of_ae_const (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc)
    (c : X) (hc : Xs =ᵐ[μ] fun _ ↦ c) : condMutualInfo μ Xs Yo Zc = 0 := by
  have h_chain := mutualInfo_chain_rule μ Yo Xs Zc hYo hXs hZc
  have h0 : mutualInfo μ (fun ω ↦ (Zc ω, Yo ω)) Xs = 0 := by
    rw [mutualInfo_comm μ _ Xs (hZc.prodMk hYo) hXs]
    exact mutualInfo_eq_zero_of_ae_const μ Xs _ hXs (hZc.prodMk hYo) c hc
  have h1 : mutualInfo μ Zc Xs = 0 := by
    rw [mutualInfo_comm μ Zc Xs hZc hXs]
    exact mutualInfo_eq_zero_of_ae_const μ Xs Zc hXs hZc c hc
  rw [h0, h1, zero_add] at h_chain
  rw [condMutualInfo_comm μ Xs Yo Zc hXs hYo hZc]
  exact h_chain.symm

end Helpers

section CondIndep

lemma iCondIndepFun_of_subsingleton_codomain {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    {β : ι → Type*} [m : ∀ i, MeasurableSpace (β i)] [∀ i, Subsingleton (β i)]
    [∀ i, Nonempty (β i)] (f : ∀ i, Ω → β i) (hf : ∀ i, Measurable (f i))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m' : MeasurableSpace Ω} (hm' : m' ≤ mΩ) :
    iCondIndepFun m' hm' f μ := by
  classical
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul (μ := μ) m f hf]
  intro S sets _hsets
  by_cases hall : ∀ i ∈ S, (Classical.arbitrary (β i)) ∈ sets i
  · have huniv : ∀ i ∈ S, f i ⁻¹' sets i = Set.univ := fun i hi ↦
      Set.eq_univ_of_forall fun ω ↦ by
        simpa only [Set.mem_preimage, Subsingleton.elim (f i ω) (Classical.arbitrary (β i))]
          using hall i hi
    have hInter : (⋂ i ∈ S, f i ⁻¹' sets i) = Set.univ :=
      Set.eq_univ_of_forall fun ω ↦ Set.mem_iInter₂.2 fun i hi ↦ (huniv i hi) ▸ Set.mem_univ ω
    have hunivExp : μ⟦(Set.univ : Set Ω) | m'⟧ = (1 : Ω → ℝ) := by
      rw [Set.indicator_univ]; exact condExp_const hm' 1
    rw [hInter, Finset.prod_congr rfl fun i hi ↦ by rw [huniv i hi], Finset.prod_const,
      hunivExp, one_pow]
  · push Not at hall
    obtain ⟨i₀, hi₀S, hi₀⟩ := hall
    have hempty : f i₀ ⁻¹' sets i₀ = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω ↦ hi₀ (by
        rw [Subsingleton.elim (Classical.arbitrary (β i₀)) (f i₀ ω)]; exact hω)
    have hInter : (⋂ i ∈ S, f i ⁻¹' sets i) = ∅ :=
      Set.eq_empty_of_subset_empty (hempty ▸ Set.biInter_subset_of_mem hi₀S)
    have hzeroExp : μ⟦(∅ : Set Ω) | m'⟧ = (0 : Ω → ℝ) := by
      rw [Set.indicator_empty]; exact condExp_zero
    rw [hInter, hzeroExp, Finset.prod_eq_zero hi₀S (by rw [hempty, hzeroExp])]

end CondIndep

variable {α β₁ β₂ : Type u} [Fintype α] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [Fintype β₁] [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [Fintype β₂] [MeasurableSpace β₂] [StandardBorelSpace β₂] [Nonempty β₂]

instance instSubsingletonBcAuxZero : Subsingleton (bcAuxAlphabet.{u} 0) :=
  ⟨fun a b ↦ ULift.down_injective (Subsingleton.elim (α := Fin 1) a.down b.down)⟩

/-- The degenerate ambient law: a point mass on the input, the channel and the auxiliary
receiver kernel applied to it, and one-point auxiliary alphabets. -/
noncomputable def degLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    Measure (Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂) :=
  ((Measure.dirac x₀ ⊗ₘ W) ⊗ₘ TJ).map
    (fun q ↦ ((fun _ ↦ default), q.1.1, q.1.2.1, q.1.2.2, q.2))

instance (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    IsProbabilityMeasure (degLaw W TJ x₀) := by
  unfold degLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma degLaw_map_input (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    (degLaw W TJ x₀).map (fun q ↦ q.2.1) = Measure.dirac x₀ := by
  rw [degLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  have : ((fun q : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ ↦ q.2.1) ∘
      fun q : (α × β₁ × β₂) × bcAuxAlphabet.{u} kJ ↦
        (((fun _ ↦ default) : (i : Thm7AuxIdx) → bcAuxAlphabet.{u} 0), q.1.1, q.1.2.1,
          q.1.2.2, q.2)) = fun q ↦ q.1.1 := rfl
  rw [this]
  have h1 : (fun q : (α × β₁ × β₂) × bcAuxAlphabet.{u} kJ ↦ q.1.1)
      = (fun r : α × β₁ × β₂ ↦ r.1) ∘ (fun q : (α × β₁ × β₂) × bcAuxAlphabet.{u} kJ ↦ q.1) := rfl
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop)]
  have h2 : ((Measure.dirac x₀ ⊗ₘ W) ⊗ₘ TJ).map (fun q ↦ q.1) = Measure.dirac x₀ ⊗ₘ W :=
    Measure.fst_compProd _ _
  rw [h2]
  exact Measure.fst_compProd _ _

lemma degLaw_map_outputs (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    (degLaw W TJ x₀).map (fun q ↦ (q.2.1, q.2.2.1, q.2.2.2.1)) = Measure.dirac x₀ ⊗ₘ W := by
  rw [degLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  have : ((fun q : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ ↦ (q.2.1, q.2.2.1, q.2.2.2.1)) ∘
      fun q : (α × β₁ × β₂) × bcAuxAlphabet.{u} kJ ↦
        (((fun _ ↦ default) : (i : Thm7AuxIdx) → bcAuxAlphabet.{u} 0), q.1.1, q.1.2.1,
          q.1.2.2, q.2)) = fun q ↦ q.1 := rfl
  rw [this]
  exact Measure.fst_compProd _ _

lemma degLaw_map_full (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    (degLaw W TJ x₀).map (fun q ↦ ((q.2.1, q.2.2.1, q.2.2.2.1), q.2.2.2.2))
      = (Measure.dirac x₀ ⊗ₘ W) ⊗ₘ TJ := by
  rw [degLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  have : ((fun q : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ ↦
        ((q.2.1, q.2.2.1, q.2.2.2.1), q.2.2.2.2)) ∘
      fun q : (α × β₁ × β₂) × bcAuxAlphabet.{u} kJ ↦
        (((fun _ ↦ default) : (i : Thm7AuxIdx) → bcAuxAlphabet.{u} 0), q.1.1, q.1.2.1,
          q.1.2.2, q.2)) = id := rfl
  rw [this, Measure.map_id]

lemma degLaw_isThm7Law (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    IsThm7Law W TJ (Measure.dirac x₀) (degLaw W TJ x₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact iCondIndepFun_of_subsingleton_codomain _ (fun j ↦ by fun_prop) _ _
  · rw [degLaw_map_outputs, degLaw_map_input]
  · rw [degLaw_map_full, degLaw_map_outputs]
  · exact degLaw_map_input W TJ x₀

lemma degLaw_slots (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    thm7Slots (degLaw W TJ x₀) = 0 := by
  haveI : MeasurableSingletonClass α := measurableSingleton_of_standardBorel
  have haux : ∀ i : Thm7AuxIdx, (fun q : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ ↦ q.1 i)
      =ᵐ[degLaw W TJ x₀] fun _ ↦ (default : bcAuxAlphabet.{u} 0) :=
    fun _ ↦ Filter.Eventually.of_forall fun _ ↦ Subsingleton.elim _ _
  have hX : (fun q : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ ↦ q.2.1)
      =ᵐ[degLaw W TJ x₀] fun _ ↦ x₀ :=
    ae_eq_const_of_map_eq_dirac _ _ (by fun_prop) x₀ (degLaw_map_input W TJ x₀)
  have hauxMI : ∀ {T : Type u} [MeasurableSpace T] (i : Thm7AuxIdx)
      (g : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → T), Measurable g →
      mutualInfoReal (degLaw W TJ x₀) (fun q ↦ q.1 i) g = 0 := by
    intro T _ i g hg
    rw [mutualInfoReal,
      mutualInfo_eq_zero_of_ae_const _ _ g (by fun_prop) hg default (haux i), ENNReal.toReal_zero]
  have hXMI : ∀ {T : Type u} [MeasurableSpace T]
      (g : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → T), Measurable g →
      mutualInfoReal (degLaw W TJ x₀) (fun q ↦ q.2.1) g = 0 := by
    intro T _ g hg
    rw [mutualInfoReal,
      mutualInfo_eq_zero_of_ae_const _ _ g (by fun_prop) hg x₀ hX, ENNReal.toReal_zero]
  have hauxCMI : ∀ {T R : Type u} [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T]
      [MeasurableSpace R] (i : Thm7AuxIdx) (g : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → T)
      (h : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → R), Measurable g → Measurable h →
      condMutualInfoReal (degLaw W TJ x₀) (fun q ↦ q.1 i) g h = 0 := by
    intro T R _ _ _ _ i g h hg hh
    rw [condMutualInfoReal,
      condMutualInfo_eq_zero_of_ae_const _ _ g h (by fun_prop) hg hh default (haux i),
      ENNReal.toReal_zero]
  have hXCMI : ∀ {T R : Type u} [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T]
      [MeasurableSpace R] (g : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → T)
      (h : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → R), Measurable g → Measurable h →
      condMutualInfoReal (degLaw W TJ x₀) (fun q ↦ q.2.1) g h = 0 := by
    intro T R _ _ _ _ g h hg hh
    rw [condMutualInfoReal,
      condMutualInfo_eq_zero_of_ae_const _ _ g h (by fun_prop) hg hh x₀ hX, ENNReal.toReal_zero]
  funext i
  fin_cases i <;>
    simp only [thm7Slots, Pi.zero_apply] <;>
    first
      | exact hauxMI _ _ (by fun_prop)
      | exact hXMI _ (by fun_prop)
      | exact hauxCMI _ _ _ (by fun_prop) (by fun_prop)
      | exact hXCMI _ _ (by fun_prop) (by fun_prop)

theorem origin_mem_thm7Region (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (x₀ : α) :
    ((0, 0, 0) : ℝ × ℝ × ℝ) ∈ thm7Region W := by
  simp only [thm7Region, Set.mem_iUnion]
  refine ⟨⟨Measure.dirac x₀, inferInstance⟩, ?_⟩
  simp only [thm7RegionOfInput, Set.mem_iInter]
  intro kJ TJ hTJ
  haveI := hTJ
  simp only [thm7RegionOfAuxReceiver, Set.mem_iUnion]
  refine ⟨fun _ ↦ 0, fun i ↦ ?_, ⟨degLaw W TJ x₀, inferInstance⟩, ?_, ?_⟩
  · simp only [thm7Cap]; split <;> omega
  · simpa only [ProbabilityMeasure.coe_mk] using degLaw_isThm7Law W TJ x₀
  · simp only [ProbabilityMeasure.coe_mk, thm7RegionOfLaw, Set.mem_setOf_eq,
      degLaw_slots W TJ x₀]
    norm_num [InThm7, IsThm7Eligible]

theorem thm7Region_nonempty (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (thm7Region W).Nonempty :=
  ⟨(0, 0, 0), origin_mem_thm7Region W (Classical.arbitrary α)⟩

#print axioms thm7Region_nonempty
#print axioms origin_mem_thm7Region
#print axioms degLaw_slots
#print axioms degLaw_isThm7Law
#print axioms iCondIndepFun_of_subsingleton_codomain

end ProbeThm7N18
