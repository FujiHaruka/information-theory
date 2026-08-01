import InformationTheory.Shannon.CondMutualInfo

/-!
# Invariance of an information slot under a re-encoding of one of its variables

An information slot depends on the variable filling it only through the information that variable
carries, so replacing the variable by its image under a map that has a left inverse leaves the slot
unchanged: the data processing inequality bounds the slot in one direction along the map and in the
other along the left inverse.  The same holds for a variable replaced by one equal to it almost
everywhere, since the two induce the same joint law.  For a re-encoding of the conditioning
variable the chain rule turns the statement about a pair back into one about the conditional
mutual information.

None of the statements mentions a channel or a code: they are properties of `mutualInfo` and
`condMutualInfo` under a substitution of one of their variables.

## Main statements

* `mutualInfo_eq_of_leftInverse` — re-encoding a variable by a map that has a left inverse leaves
  the mutual information it carries about another variable unchanged.
* `mutualInfo_congr_ae` — two variables that agree almost everywhere carry the same mutual
  information about a third.
* `condMutualInfo_eq_of_leftInverse_cond` — the same re-encoding applied to the conditioning
  variable of a conditional mutual information, obtained from the chain rule by cancelling the
  tag term on both sides.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory
open scoped ENNReal

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

end InformationTheory.Shannon
