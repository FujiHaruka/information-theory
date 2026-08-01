import InformationTheory.Shannon.CondEntropyMemoryless
import InformationTheory.Shannon.CondMutualInfoMixture
import InformationTheory.Shannon.MaxEntropy.Basic

/-!
# Mutual information against a variable of finite range

Mutual information is a divergence, so nothing bounds it in general.  As soon as one of the two
variables ranges over a finite alphabet, though, the information the pair shares is capped by the
entropy of that variable alone, hence by the log of its alphabet size, and the bound does not see
the other side at all: it may range over an arbitrary standard Borel space.  Finiteness of the
information is the same statement read qualitatively, and it is what lets the estimates be moved
into the reals.

The degenerate end of the scale is a variable whose range is a single point up to a null set.
Such a variable is independent of everything, so it shares no information with any other one, and
conditioning on it is the same as not conditioning at all.

## Main statements

* `mutualInfo_ne_top_of_fintype_right` — a finite alphabet on one side alone makes the mutual
  information finite.
* `mutualInfo_le_ofReal_log_card` — that mutual information is at most the log of the finite
  alphabet size.
* `mutualInfo_eq_zero_of_ae_const` — an almost everywhere constant variable shares no information.
* `condMutualInfo_eq_mutualInfo_of_ae_const` — conditioning on an almost everywhere constant
  variable leaves the mutual information unchanged.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory
open scoped ENNReal

section FiniteRange

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
variable {B : Type*} [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

theorem mutualInfo_ne_top_of_fintype_right (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → A) (Yo : Ω → B) (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo ≠ ∞ :=
  ne_top_of_le_ne_top (mutualInfo_ne_top μ Yo Yo hYo hYo)
    (mutualInfo_le_of_markov μ Xs Yo Yo hXs hYo hYo
      (isMarkovChain_comp_conditioner_right μ Xs Yo hXs hYo measurable_id))

theorem mutualInfo_le_ofReal_log_card (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → A) (Yo : Ω → B) (hXs : Measurable Xs) (hYo : Measurable Yo) :
    mutualInfo μ Xs Yo ≤ ENNReal.ofReal (Real.log (Fintype.card B)) := by
  have htoReal : (mutualInfo μ Xs Yo).toReal ≤ Real.log (Fintype.card B) := by
    rw [mutualInfo_comm μ Xs Yo hXs hYo, mutualInfo_eq_entropy_sub_condEntropy μ Yo Xs hYo hXs]
    have hnn : 0 ≤ InformationTheory.MeasureFano.condEntropy μ Yo Xs := condEntropy_nonneg μ Yo Xs
    have hcard : entropy μ Yo ≤ Real.log (Fintype.card B) :=
      InformationTheory.Shannon.MaxEntropy.entropy_le_log_card μ Yo hYo
    linarith
  calc mutualInfo μ Xs Yo = ENNReal.ofReal (mutualInfo μ Xs Yo).toReal :=
        (ENNReal.ofReal_toReal (mutualInfo_ne_top_of_fintype_right μ Xs Yo hXs hYo)).symm
    _ ≤ ENNReal.ofReal (Real.log (Fintype.card B)) := ENNReal.ofReal_le_ofReal htoReal

omit [StandardBorelSpace A] [Nonempty A] [Fintype B] [Nonempty B]
  [MeasurableSingletonClass B] in
theorem mutualInfo_eq_zero_of_ae_const (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → A) (Yo : Ω → B) (hYo : Measurable Yo) (c : A) (hc : Xs =ᵐ[μ] fun _ ↦ c) :
    mutualInfo μ Xs Yo = 0 := by
  rw [mutualInfo_congr_ae μ Yo hc]
  exact (mutualInfo_eq_zero_iff_indep μ (fun _ ↦ c) Yo measurable_const hYo).2
    (indepFun_const_left c Yo)

end FiniteRange

section Constant

variable {Ω A B C : Type*} [MeasurableSpace Ω]
variable [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
variable [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [MeasurableSpace C]

lemma condMutualInfo_eq_mutualInfo_of_ae_const (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → A) (Yo : Ω → B) (Zc : Ω → C) (hXs : Measurable Xs) (hYo : Measurable Yo)
    (hZc : Measurable Zc) (c : C) (hc : Zc =ᵐ[μ] fun _ ↦ c) :
    condMutualInfo μ Xs Yo Zc = mutualInfo μ Xs Yo := by
  have hchain := mutualInfo_chain_rule μ Xs Yo Zc hXs hYo hZc
  have hzero : mutualInfo μ Zc Yo = 0 := mutualInfo_eq_zero_of_ae_const μ Zc Yo hYo c hc
  have hae : (fun ω ↦ (Zc ω, Xs ω)) =ᵐ[μ] fun ω ↦ (c, Xs ω) := by
    filter_upwards [hc] with ω hω
    rw [hω]
  have hpair : mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo = mutualInfo μ Xs Yo := by
    rw [mutualInfo_congr_ae μ Yo hae]
    exact mutualInfo_eq_of_leftInverse μ Xs Yo hXs hYo (f := fun a ↦ (c, a)) (g := Prod.snd)
      (measurable_const.prodMk measurable_id) measurable_snd (fun _ ↦ rfl)
  rw [hpair, hzero, zero_add] at hchain
  exact hchain.symm

end Constant

end InformationTheory.Shannon
