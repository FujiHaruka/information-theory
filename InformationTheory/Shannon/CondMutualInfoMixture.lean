import InformationTheory.Shannon.CondKLIntegral
import InformationTheory.Shannon.CondMutualInfo

/-!
# Averaging an information slot over a countable mixture

A mixture of laws indexed by a countable tag is a composition product of the tag law with the
kernel of the components, so the tag-conditioned mutual information of the mixture is the tag
average of the mutual informations of the components.  Adding back the tag term of the chain rule
turns that into an identity for the mutual information of the mixture itself, whenever the
variable in question recovers the tag; dropping the tag term leaves the averaging inequality.

None of the statements mentions a channel or a code: they are properties of `mutualInfo` and
`condMutualInfo` under a composition product of a countably supported measure with a Markov
kernel, together with the invariance of an information slot under an injective re-encoding of one
of its variables.

## Main statements

* `mutualInfo_eq_of_leftInverse` — re-encoding a variable by a map that has a left inverse leaves
  the mutual information it carries about another variable unchanged, since the data processing
  inequality applies in both directions.
* `condMutualInfo_eq_of_leftInverse_cond` — the same re-encoding applied to the conditioning
  variable of a conditional mutual information, obtained from the chain rule by cancelling the
  tag term on both sides.
* `condMutualInfo_compProd_fst_eq_lintegral` and `condMutualInfo_compProd_snd_eq_lintegral` — the
  tag-conditioned mutual information of a mixture is the tag average of the components, in the
  unconditional and in the conditional form.
* `mutualInfo_compProd_eq_add_lintegral` — for a variable that recovers the tag, the mutual
  information of the mixture itself splits into the information the tag carries and the tag
  average of the components.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

lemma mutualInfo_eq_of_leftInverse {Ω γ A B : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → A) (Yo : Ω → γ)
    (hU : Measurable U) (hYo : Measurable Yo)
    {f : A → B} {g : B → A} (hf : Measurable f) (hg : Measurable g)
    (hgf : ∀ a, g (f a) = a) :
    mutualInfo μ (fun ω ↦ f (U ω)) Yo = mutualInfo μ U Yo := by
  have hfU : Measurable (fun ω ↦ f (U ω)) := hf.comp hU
  refine le_antisymm ?_ ?_
  · rw [mutualInfo_comm μ _ Yo hfU hYo, mutualInfo_comm μ U Yo hU hYo]
    exact mutualInfo_le_of_postprocess μ Yo U hYo hU hf
  · have hUg : U = fun ω ↦ g (f (U ω)) := funext fun ω ↦ (hgf (U ω)).symm
    rw [mutualInfo_comm μ U Yo hU hYo, mutualInfo_comm μ _ Yo hfU hYo]
    calc mutualInfo μ Yo U = mutualInfo μ Yo (fun ω ↦ g (f (U ω))) := by rw [← hUg]
      _ ≤ mutualInfo μ Yo (fun ω ↦ f (U ω)) :=
          mutualInfo_le_of_postprocess μ Yo _ hYo hfU hg

lemma mutualInfo_congr_ae {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Ω) {Xs Xs' : Ω → A} (Yo : Ω → B) (h : Xs =ᵐ[μ] Xs') :
    mutualInfo μ Xs Yo = mutualInfo μ Xs' Yo := by
  have hpair : μ.map (fun ω ↦ (Xs ω, Yo ω)) = μ.map (fun ω ↦ (Xs' ω, Yo ω)) := by
    refine Measure.map_congr ?_
    filter_upwards [h] with ω hω
    rw [hω]
  rw [mutualInfo, mutualInfo, hpair, Measure.map_congr h]

lemma condMutualInfo_eq_of_leftInverse_cond {Ω A B C C' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C] [MeasurableSpace C']
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → A) (Yo : Ω → B) (Zc : Ω → C)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc)
    {f : C → C'} {g : C' → C} (hf : Measurable f) (hg : Measurable g) (hgf : ∀ c, g (f c) = c)
    (hfin : mutualInfo μ Zc Yo ≠ ∞) :
    condMutualInfo μ Xs Yo (fun ω ↦ f (Zc ω)) = condMutualInfo μ Xs Yo Zc := by
  have hpair : mutualInfo μ (fun ω ↦ (f (Zc ω), Xs ω)) Yo
      = mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo :=
    mutualInfo_eq_of_leftInverse μ (fun ω ↦ (Zc ω, Xs ω)) Yo (hZc.prodMk hXs) hYo
      (f := fun p ↦ (f p.1, p.2)) (g := fun p ↦ (g p.1, p.2))
      ((hf.comp measurable_fst).prodMk measurable_snd)
      ((hg.comp measurable_fst).prodMk measurable_snd) (fun p ↦ by rw [hgf p.1])
  have hz : mutualInfo μ (fun ω ↦ f (Zc ω)) Yo = mutualInfo μ Zc Yo :=
    mutualInfo_eq_of_leftInverse μ Zc Yo hZc hYo hf hg hgf
  rw [mutualInfo_chain_rule μ Xs Yo (fun ω ↦ f (Zc ω)) hXs hYo (hf.comp hZc),
    mutualInfo_chain_rule μ Xs Yo Zc hXs hYo hZc, hz] at hpair
  exact (ENNReal.add_right_inj hfin).mp hpair

variable {T S A B : Type*} [MeasurableSpace T] [MeasurableSpace S]
variable [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
variable [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]

private lemma condDistrib_compProd_fst_ae_eq {C : Type*} [MeasurableSpace C]
    [StandardBorelSpace C] [Nonempty C] (μ : Measure T) [IsProbabilityMeasure μ]
    (κ : Kernel T S) [IsMarkovKernel κ] {h : S → C} (hh : Measurable h) :
    condDistrib (fun p : T × S ↦ h p.2) Prod.fst (μ ⊗ₘ κ) =ᵐ[μ] κ.map h := by
  haveI : IsMarkovKernel (κ.map h) := Kernel.IsMarkovKernel.map _ hh
  have hbase : (μ ⊗ₘ κ).map Prod.fst = μ := Measure.fst_compProd μ κ
  have hkey := condDistrib_ae_eq_of_measure_eq_compProd (μ := μ ⊗ₘ κ) Prod.fst
    (hh.comp measurable_snd).aemeasurable (κ := κ.map h)
    (by rw [hbase, Measure.compProd_map hh]; rfl)
  rwa [hbase] at hkey

lemma condMutualInfo_compProd_fst_eq_lintegral [Countable T] [MeasurableSingletonClass T]
    (μ : Measure T) [IsProbabilityMeasure μ] (κ : Kernel T S) [IsMarkovKernel κ]
    {f : S → A} {g : S → B} (hf : Measurable f) (hg : Measurable g) :
    condMutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) Prod.fst
      = ∫⁻ t, mutualInfo (κ t) f g ∂μ := by
  have hbase : (μ ⊗ₘ κ).map Prod.fst = μ := Measure.fst_compProd μ κ
  haveI : IsMarkovKernel (κ.map fun s ↦ (f s, g s)) := Kernel.IsMarkovKernel.map _ (hf.prodMk hg)
  haveI : IsMarkovKernel (κ.map f) := Kernel.IsMarkovKernel.map _ hf
  haveI : IsMarkovKernel (κ.map g) := Kernel.IsMarkovKernel.map _ hg
  have hslice : ∀ t, mutualInfo (κ t) f g
      = klDiv ((κ.map fun s ↦ (f s, g s)) t) (((κ.map f) ×ₖ (κ.map g)) t) := by
    intro t
    rw [Kernel.map_apply _ (hf.prodMk hg), Kernel.prod_apply, Kernel.map_apply _ hf,
      Kernel.map_apply _ hg]
    rfl
  have hJ := condDistrib_compProd_fst_ae_eq μ κ (hf.prodMk hg)
  have hF := condDistrib_compProd_fst_ae_eq μ κ hf
  have hG := condDistrib_compProd_fst_ae_eq μ κ hg
  have hP : (condDistrib (fun p : T × S ↦ f p.2) Prod.fst (μ ⊗ₘ κ) ×ₖ
      condDistrib (fun p : T × S ↦ g p.2) Prod.fst (μ ⊗ₘ κ)) =ᵐ[μ] (κ.map f) ×ₖ (κ.map g) := by
    filter_upwards [hF, hG] with t htF htG
    rw [Kernel.prod_apply, Kernel.prod_apply, htF, htG]
  rw [condMutualInfo, hbase, Measure.compProd_congr hJ, Measure.compProd_congr hP]
  by_cases hac : μ ⊗ₘ (κ.map fun s ↦ (f s, g s)) ≪ μ ⊗ₘ ((κ.map f) ×ₖ (κ.map g))
  · rw [klDiv_compProd_lintegral hac]
    exact lintegral_congr fun t ↦ (hslice t).symm
  · rw [klDiv_of_not_ac hac]
    simp_rw [hslice]
    refine (lintegral_eq_top_of_measure_eq_top_ne_zero
      (measurable_of_countable _).aemeasurable ?_).symm
    intro hzero
    refine hac (Measure.absolutelyContinuous_compProd_right_iff.mpr ?_)
    have hne : ∀ᵐ t ∂μ, klDiv ((κ.map fun s ↦ (f s, g s)) t)
        (((κ.map f) ×ₖ (κ.map g)) t) ≠ ∞ := by
      rw [MeasureTheory.ae_iff]
      simpa using hzero
    filter_upwards [hne] with t ht
    by_contra hnot
    exact ht (klDiv_of_not_ac hnot)

lemma mutualInfo_compProd_eq_add_lintegral [Countable T] [MeasurableSingletonClass T]
    (μ : Measure T) [IsProbabilityMeasure μ] (κ : Kernel T S) [IsMarkovKernel κ]
    {f : S → A} {g : S → B} (hf : Measurable f) (hg : Measurable g)
    {tag : A → T} (htag : Measurable tag) (hrec : ∀ᵐ p ∂(μ ⊗ₘ κ), tag (f p.2) = p.1) :
    mutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2)
      = mutualInfo (μ ⊗ₘ κ) Prod.fst (fun p ↦ g p.2)
        + ∫⁻ t, mutualInfo (κ t) f g ∂μ := by
  have hfsnd : Measurable (fun p : T × S ↦ f p.2) := hf.comp measurable_snd
  have hgsnd : Measurable (fun p : T × S ↦ g p.2) := hg.comp measurable_snd
  have hpad : mutualInfo (μ ⊗ₘ κ) (fun p : T × S ↦ (tag (f p.2), f p.2)) (fun p ↦ g p.2)
      = mutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) :=
    mutualInfo_eq_of_leftInverse (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) hfsnd hgsnd
      (f := fun a ↦ (tag a, a)) (g := Prod.snd) (htag.prodMk measurable_id) measurable_snd
      (fun _ ↦ rfl)
  have hae : (fun p : T × S ↦ (tag (f p.2), f p.2)) =ᵐ[μ ⊗ₘ κ] fun p ↦ (p.1, f p.2) := by
    filter_upwards [hrec] with p hp
    rw [hp]
  rw [← hpad, mutualInfo_congr_ae (μ ⊗ₘ κ) (fun p ↦ g p.2) hae,
    mutualInfo_chain_rule (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) Prod.fst hfsnd hgsnd
      measurable_fst,
    condMutualInfo_compProd_fst_eq_lintegral μ κ hf hg]

lemma condMutualInfo_compProd_snd_eq_lintegral [Countable T] [MeasurableSingletonClass T]
    {C : Type*} [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
    (μ : Measure T) [IsProbabilityMeasure μ] (κ : Kernel T S) [IsMarkovKernel κ]
    {f : S → A} {g : S → B} {h : S → C} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) {tag : C → T} (htag : Measurable tag)
    (hrec : ∀ᵐ p ∂(μ ⊗ₘ κ), tag (h p.2) = p.1)
    (htagfin : mutualInfo (μ ⊗ₘ κ) Prod.fst (fun p ↦ g p.2) ≠ ∞)
    (hmargfin : (∫⁻ t, mutualInfo (κ t) h g ∂μ) ≠ ∞) :
    condMutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) (fun p ↦ h p.2)
      = ∫⁻ t, condMutualInfo (κ t) f g h ∂μ := by
  have hb := mutualInfo_chain_rule (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) (fun p ↦ h p.2)
    (hf.comp measurable_snd) (hg.comp measurable_snd) (hh.comp measurable_snd)
  have hc := mutualInfo_compProd_eq_add_lintegral μ κ (hh.prodMk hf) hg
    (tag := fun w ↦ tag w.1) (htag.comp measurable_fst)
    (by filter_upwards [hrec] with p hp using hp)
  have hd := mutualInfo_compProd_eq_add_lintegral μ κ hh hg htag hrec
  have hsplit : ∫⁻ t, mutualInfo (κ t) (fun q ↦ (h q, f q)) g ∂μ
      = (∫⁻ t, mutualInfo (κ t) h g ∂μ) + ∫⁻ t, condMutualInfo (κ t) f g h ∂μ := by
    have he : ∀ t, mutualInfo (κ t) (fun q ↦ (h q, f q)) g
        = mutualInfo (κ t) h g + condMutualInfo (κ t) f g h :=
      fun t ↦ mutualInfo_chain_rule (κ t) f g h hf hg hh
    simp_rw [he]
    exact lintegral_add_left (measurable_of_countable _) _
  have hfin : mutualInfo (μ ⊗ₘ κ) Prod.fst (fun p ↦ g p.2) + ∫⁻ t, mutualInfo (κ t) h g ∂μ ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨htagfin, hmargfin⟩
  refine (((ENNReal.add_right_inj hfin).mp ?_).symm)
  conv_lhs => rw [add_assoc, ← hsplit, ← hc]
  rw [hb, hd]

end InformationTheory.Shannon
