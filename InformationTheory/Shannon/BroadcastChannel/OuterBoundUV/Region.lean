import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Bridge
import InformationTheory.Shannon.ChannelCoding.CodeToAmbient
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Algebra.Order.UpperLower

/-!
# Broadcast channel — the UV outer region as a subset of the plane

The four information slots of the UV outer bound are functionals of a five-tuple law
`(U, V, X, Y₁, Y₂)` and do not mention the channel.  A region defined as the union of the
resulting quadrilaterals over *all* five-tuple laws would therefore be the whole plane: a law
that copies the input into the outputs makes every slot as large as the input alphabet allows,
whatever the channel is.  The union is therefore indexed by the laws whose output pair is
generated from the input letter by the channel and by nothing else, which is one composition
product identity, `IsUVChannelLaw`.

## Main definitions

* `IsUVChannelLaw W ν` — the conditional law of the output pair `(Y₁, Y₂)` given the two
  auxiliaries and the input letter `(U, V, X)` is `W X`.  This says at once that the output law
  is the channel and that the auxiliaries reach the outputs only through the input letter.
* `uvRegion ν` — the quadrilateral cut out by the four information slots of a five-tuple law.
* `bcOuterRegionUV W` — the UV outer region: the closure of the union of `uvRegion ν` over the
  channel laws `ν` on a fixed pair of countable auxiliary alphabets.
* `uvConstLaw W x₀` — the channel law with constant auxiliaries and constant input letter `x₀`,
  which witnesses that the union is indexed by a nonempty family.
* `uvOutputCopiesInputLaw`, `uvAuxCopiesOutputLaw` — two five-tuple laws that the channel
  constraint rejects, over the channels `uvBlindChannel` and `uvFairBitChannel`.

## Main statements

* `bcOuterRegionUV_isClosed` — the region is closed.
* `bcOuterRegionUV_isLowerSet` — the region is a lower set, so a rate pair below one of its
  points belongs to it as well.
* `bcOuterRegionUV_nonempty` — the region is nonempty, witnessed by `uvConstLaw`, so the union
  is indexed by a nonempty family of channel laws.
* `isUVChannelLaw_iff` — a law is a channel law exactly when it is a law of the auxiliaries and
  the input letter pushed through the channel, which describes the index of the union directly.
* `IsUVChannelLaw.map_input_output` — a channel law has the channel joint `(ν.map X) ⊗ₘ W` as
  its input-output pair law, which is the constraint a law copying the input letter into the
  outputs violates.
* `not_isUVChannelLaw_uvOutputCopiesInputLaw` and `not_isUVChannelLaw_uvAuxCopiesOutputLaw` — the
  constraint rejects two structurally different degenerate laws, one whose outputs copy the input
  letter and one whose auxiliary copies an output over a one-letter input alphabet.
* `IsUVChannelLaw.smul`, `IsUVChannelLaw.add` — mixtures of channel laws are channel laws, so
  averaging the letter laws of a code stays inside the index of the union.
* `IsUVChannelLaw.map_auxiliaries` — re-encoding the two auxiliary alphabets keeps a channel
  law a channel law, which is how a law on the auxiliaries of a code reaches the fixed ones.
* `IsUVChannelLaw.swap_auxiliaries` — exchanging the two auxiliary alphabets keeps a channel law
  a channel law, so a law indexing its auxiliaries in the opposite order indexes the union too.

## Implementation notes

`IsUVChannelLaw` is one composition-product identity between two pushforwards of `ν`, rather
than a conjunction of "the output pair is distributed by the channel" and "the auxiliaries are
conditionally independent of the output pair given the input letter".  A single identity is the
shape the `Measure.map` and `Measure.compProd` lemmas consume, so the mixture, re-encoding and
marginalization lemmas are each a rewrite chain; the first conjunct is recovered from it as
`IsUVChannelLaw.map_input_output`, and the second is the statement that the conditional law is
read at the input coordinate only.

Both auxiliary alphabets of `bcOuterRegionUV` are fixed to `ℕ` instead of being quantified over
countable types, so the union ranges over measures rather than over types.  The closure is taken
because a union of intersections of closed half-planes need not be closed, and because the
operational region is itself a closure.

`uvRegion` imposes no sign constraint on the rate pair, matching the operational region, which
contains nonpositive pairs; imposing one would exclude pairs the operational region contains.
Both regions being lower sets is what carries the inclusion off the first quadrant, so no
intersection with it is needed.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {α : Type*} [MeasurableSpace α]
variable {β₁ : Type*} [MeasurableSpace β₁]
variable {β₂ : Type*} [MeasurableSpace β₂]

/-! ## Channel laws of a five-tuple -/

section ChannelLaw

variable {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]

/-! ### The constraint and its characterization -/

/-- A five-tuple law `(U, V, X, Y₁, Y₂)` is a channel law for `W` when the conditional law of the
output pair given the two auxiliaries and the input letter is `W X`: pushing the law forward to
the pair `((U, V, X), (Y₁, Y₂))` gives the composition product of the `(U, V, X)` marginal with
`W` read at the input coordinate.

The identity carries both constraints that keep the region proper.  Taking the `(U, V)` component
of the first factor away leaves the input-output pair law `(ν.map X) ⊗ₘ W`, so the outputs are
distributed by the channel; keeping it says that the conditional law does not depend on the
auxiliaries, so they act on the outputs only through the input letter.

The identity pins the law exactly: it holds if and only if `ν` is the composition product of its
own `(U, V, X)` marginal with the channel read at the input letter, so the union is indexed by
the laws obtained from an arbitrary law of `(U, V, X)` through the channel and by nothing else.
@audit:ok -/
def IsUVChannelLaw (W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂)) : Prop :=
  ν.map (fun q ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2))
    = (ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) ⊗ₘ
        W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)

private lemma measurable_uvFirstThree :
    Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
    (measurable_fst.comp (measurable_snd.comp measurable_snd)))

private lemma measurable_uvSplit :
    Measurable (fun q : U × V × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) :=
  measurable_uvFirstThree.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))

private lemma measurable_uvUnsplit :
    Measurable (fun z : (U × V × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2)) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))))

lemma isUVChannelLaw_iff (W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂)) :
    IsUVChannelLaw W ν ↔
      ν = ((ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) ⊗ₘ
            W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)).map
          (fun z : (U × V × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2)) := by
  have hid₁ : (fun z : (U × V × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2)) ∘
      (fun q : U × V × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) = id := rfl
  have hid₂ : (fun q : U × V × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) ∘
      (fun z : (U × V × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2)) = id := rfl
  constructor
  · intro h
    have h2 := congrArg (Measure.map (fun z : (U × V × α) × (β₁ × β₂) ↦
      (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2))) h
    rwa [Measure.map_map measurable_uvUnsplit measurable_uvSplit, hid₁, Measure.map_id] at h2
  · intro h
    unfold IsUVChannelLaw
    conv_lhs => rw [h]
    rw [Measure.map_map measurable_uvSplit measurable_uvUnsplit, hid₂, Measure.map_id]

/-! ### Mixtures, re-encodings and marginals -/

/-- @audit:ok -/
lemma IsUVChannelLaw.smul {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)}
    [SFinite ν] (h : IsUVChannelLaw W ν) (a : ℝ≥0∞) : IsUVChannelLaw W (a • ν) := by
  unfold IsUVChannelLaw at h ⊢
  rw [Measure.map_smul, Measure.map_smul, h, Measure.compProd_smul_left]

/-- @audit:ok -/
lemma IsUVChannelLaw.add {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν₁ ν₂ : Measure (U × V × α × β₁ × β₂)}
    [SFinite ν₁] [SFinite ν₂] (h₁ : IsUVChannelLaw W ν₁) (h₂ : IsUVChannelLaw W ν₂) :
    IsUVChannelLaw W (ν₁ + ν₂) := by
  unfold IsUVChannelLaw at h₁ h₂ ⊢
  rw [Measure.map_add _ _ measurable_uvSplit, Measure.map_add _ _ measurable_uvFirstThree,
    h₁, h₂, Measure.compProd_add_left]

lemma IsUVChannelLaw.finsetSum {ι : Type*} {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν : ι → Measure (U × V × α × β₁ × β₂)} [∀ i, IsFiniteMeasure (ν i)]
    (h : ∀ i, IsUVChannelLaw W (ν i)) (s : Finset ι) :
    IsUVChannelLaw W (∑ i ∈ s, ν i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    unfold IsUVChannelLaw
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a).add ih

/-- @audit:ok -/
lemma IsUVChannelLaw.map_auxiliaries {U' V' : Type*} [MeasurableSpace U'] [MeasurableSpace V']
    {W : BCChannel α β₁ β₂} [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν]
    (h : IsUVChannelLaw W ν) {f : U → U'} {g : V → V'} (hf : Measurable f) (hg : Measurable g) :
    IsUVChannelLaw W (ν.map fun q ↦ (f q.1, g q.2.1, q.2.2)) := by
  have hφ : Measurable (fun r : U × V × α ↦ (f r.1, g r.2.1, r.2.2)) :=
    (hf.comp measurable_fst).prodMk
      ((hg.comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have hψ : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (f q.1, g q.2.1, q.2.2)) :=
    (hf.comp measurable_fst).prodMk
      ((hg.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
  have hprod : Measurable (fun z : (U × V × α) × (β₁ × β₂) ↦
      ((f z.1.1, g z.1.2.1, z.1.2.2), z.2)) := (hφ.comp measurable_fst).prodMk measurable_snd
  have hkernel : W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)
      = (W.comap (fun r : U' × V' × α ↦ r.2.2) (measurable_snd.comp measurable_snd)).comap
        (fun r : U × V × α ↦ (f r.1, g r.2.1, r.2.2)) hφ := Kernel.ext fun _ ↦ rfl
  unfold IsUVChannelLaw at h ⊢
  rw [Measure.map_map measurable_uvSplit hψ, Measure.map_map measurable_uvFirstThree hψ]
  have hcong := congrArg (Measure.map (fun z : (U × V × α) × (β₁ × β₂) ↦
    ((f z.1.1, g z.1.2.1, z.1.2.2), z.2))) h
  rw [Measure.map_map hprod measurable_uvSplit, hkernel,
    compProd_comap_map_prodMap (ν.map fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1))
      (W.comap (fun r : U' × V' × α ↦ r.2.2) (measurable_snd.comp measurable_snd)) hφ,
    Measure.map_map hφ measurable_uvFirstThree] at hcong
  exact hcong

lemma IsUVChannelLaw.swap_auxiliaries {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) :
    IsUVChannelLaw W (ν.map fun q ↦ (q.2.1, q.1, q.2.2)) := by
  have hσ : Measurable (fun r : U × V × α ↦ (r.2.1, r.1, r.2.2)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hψ : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.2.1, q.1, q.2.2)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hprod : Measurable (fun z : (U × V × α) × (β₁ × β₂) ↦
      ((z.1.2.1, z.1.1, z.1.2.2), z.2)) := (hσ.comp measurable_fst).prodMk measurable_snd
  have hkernel : W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)
      = (W.comap (fun r : V × U × α ↦ r.2.2) (measurable_snd.comp measurable_snd)).comap
        (fun r : U × V × α ↦ (r.2.1, r.1, r.2.2)) hσ := Kernel.ext fun _ ↦ rfl
  unfold IsUVChannelLaw at h ⊢
  rw [Measure.map_map measurable_uvSplit hψ, Measure.map_map measurable_uvFirstThree hψ]
  have hcong := congrArg (Measure.map (fun z : (U × V × α) × (β₁ × β₂) ↦
    ((z.1.2.1, z.1.1, z.1.2.2), z.2))) h
  rw [Measure.map_map hprod measurable_uvSplit, hkernel,
    compProd_comap_map_prodMap (ν.map fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1))
      (W.comap (fun r : V × U × α ↦ r.2.2) (measurable_snd.comp measurable_snd)) hσ,
    Measure.map_map hσ measurable_uvFirstThree] at hcong
  exact hcong

/-- @audit:ok -/
lemma IsUVChannelLaw.map_input_output {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) :
    ν.map (fun q ↦ (q.2.2.1, q.2.2.2)) = (ν.map fun q ↦ q.2.2.1) ⊗ₘ W := by
  have hg : Measurable (fun r : U × V × α ↦ r.2.2) := measurable_snd.comp measurable_snd
  have hπ : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hP : Measurable (fun q : U × V × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) :=
    hπ.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hmap : Measurable (fun z : (U × V × α) × (β₁ × β₂) ↦ (z.1.2.2, z.2)) :=
    (hg.comp measurable_fst).prodMk measurable_snd
  have hcong := congrArg (Measure.map (fun z : (U × V × α) × (β₁ × β₂) ↦ (z.1.2.2, z.2))) h
  rw [Measure.map_map hmap hP,
    compProd_comap_map_prodMap (ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) W hg,
    Measure.map_map hg hπ] at hcong
  exact hcong

end ChannelLaw

/-! ## The UV outer region -/

section Region

variable [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace β₁] [Nonempty β₁]
variable [StandardBorelSpace β₂] [Nonempty β₂]

/-- The quadrilateral of a five-tuple law: the rate pairs satisfying the two corner bounds and
the two sum-rate bounds of `InBCOuterRegionUV` at the four information slots of the law.  No sign
constraint is imposed, matching the operational region, which contains nonpositive rate pairs.
@audit:ok -/
def uvRegion {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : Set (ℝ × ℝ) :=
  {p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal
    (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}

/-- The UV (Nair–El Gamal) outer region of a broadcast channel: the closure of the union of the
quadrilaterals `uvRegion ν` over the channel laws `ν` of `W`.

Both auxiliary alphabets are fixed to `ℕ`, which quantifies over every countable auxiliary
without quantifying over types.  The closure is taken because a union of closed half-plane
intersections need not be closed, and because the operational region is itself a closure.
@audit:ok -/
def bcOuterRegionUV (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂))
    (_ : IsUVChannelLaw W (ν : Measure (ℕ × ℕ × α × β₁ × β₂))),
      uvRegion (ν : Measure (ℕ × ℕ × α × β₁ × β₂)))

/-- @audit:ok -/
theorem bcOuterRegionUV_isClosed (W : BCChannel α β₁ β₂) : IsClosed (bcOuterRegionUV W) :=
  isClosed_closure

/-- @audit:ok -/
lemma uvRegion_isLowerSet {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : IsLowerSet (uvRegion ν) := by
  rintro p q hqp ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨hqp.1.trans h₁, hqp.2.trans h₂, (add_le_add hqp.1 hqp.2).trans h₃,
    (add_le_add hqp.1 hqp.2).trans h₄⟩

/-- The UV outer region is a lower set: a rate pair below a point of the region is again in the
region.  Each quadrilateral bounds the two rates and their sum from above, and both the union and
the closure preserve that.
@audit:ok -/
theorem bcOuterRegionUV_isLowerSet (W : BCChannel α β₁ β₂) :
    IsLowerSet (bcOuterRegionUV W) :=
  IsLowerSet.closure
    (isLowerSet_iUnion fun _ ↦ isLowerSet_iUnion fun _ ↦ uvRegion_isLowerSet _)

/-- The five-tuple law with constant auxiliaries and a constant input letter `x₀`, whose output
pair is drawn from `W x₀`.
@audit:ok -/
noncomputable def uvConstLaw (W : BCChannel α β₁ β₂) (x₀ : α) :
    Measure (ℕ × ℕ × α × β₁ × β₂) :=
  ((Measure.dirac ((0 : ℕ), (0 : ℕ), x₀)) ⊗ₘ
      W.comap (fun r : ℕ × ℕ × α ↦ r.2.2) (measurable_snd.comp measurable_snd)).map
    (fun z ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2))

omit [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [Nonempty β₁]
  [StandardBorelSpace β₂] [Nonempty β₂] in
private lemma measurable_uvUnassoc :
    Measurable (fun z : (ℕ × ℕ × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2)) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))))

instance uvConstLaw_isProbabilityMeasure (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (x₀ : α) :
    IsProbabilityMeasure (uvConstLaw W x₀) := by
  unfold uvConstLaw
  exact Measure.isProbabilityMeasure_map measurable_uvUnassoc.aemeasurable

omit [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [Nonempty β₁]
  [StandardBorelSpace β₂] [Nonempty β₂] in
/-- @audit:ok -/
lemma uvConstLaw_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (x₀ : α) :
    IsUVChannelLaw W (uvConstLaw W x₀) := by
  have hg : Measurable (fun r : ℕ × ℕ × α ↦ r.2.2) := measurable_snd.comp measurable_snd
  have hπ : Measurable (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hP : Measurable (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) :=
    hπ.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hcomp₁ : (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) ∘
      (fun z : (ℕ × ℕ × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2)) = id := rfl
  have hcomp₂ : (fun q : ℕ × ℕ × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) ∘
      (fun z : (ℕ × ℕ × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2))
      = Prod.fst := rfl
  unfold IsUVChannelLaw uvConstLaw
  rw [Measure.map_map hP measurable_uvUnassoc, Measure.map_map hπ measurable_uvUnassoc,
    hcomp₁, hcomp₂, Measure.map_id,
    show (Measure.dirac ((0 : ℕ), (0 : ℕ), x₀) ⊗ₘ
        W.comap (fun r : ℕ × ℕ × α ↦ r.2.2) hg).map Prod.fst
      = Measure.dirac ((0 : ℕ), (0 : ℕ), x₀) from Measure.fst_compProd _ _]

/-- @audit:ok -/
theorem bcOuterRegionUV_nonempty (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (bcOuterRegionUV W).Nonempty := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty α)
  refine ⟨(0, 0), subset_closure (Set.mem_iUnion.mpr ⟨⟨uvConstLaw W x₀, inferInstance⟩,
    Set.mem_iUnion.mpr ⟨uvConstLaw_isUVChannelLaw W x₀, ?_, ?_, ?_, ?_⟩⟩)⟩ <;>
    simp

end Region

/-! ## The channel constraint is not vacuous

The information slots do not mention the channel, so the constraint is what stops the union from
exhausting the plane, and it has to reject two structurally different families of laws.

A law that copies the input letter into both outputs carries a full input alphabet of information
in every slot no matter which channel indexes the region, and such laws exist over every alphabet,
so the output law has to be pinned to the channel.  `uvOutputCopiesInputLaw` copies a fair bit
into both outputs and is rejected over the channel that always outputs `(false, false)`.

Pinning the output law alone would still leave the auxiliaries free to read the outputs directly,
which manufactures information about a receiver that the input letter does not carry.
`uvAuxCopiesOutputLaw` lives over a one-letter input alphabet and has the channel joint as its
input-output pair law, so it meets the first constraint, yet its first auxiliary is the output
bit, and it is rejected as well. -/

section NotVacuous

/-- The broadcast channel over a binary input alphabet whose two receivers always read `false`,
so that no input letter is visible at either output. -/
noncomputable def uvBlindChannel : BCChannel Bool Bool Bool :=
  Kernel.const Bool (Measure.dirac (false, false))

instance uvBlindChannel_isMarkovKernel : IsMarkovKernel uvBlindChannel := by
  unfold uvBlindChannel
  infer_instance

/-- The five-tuple law that draws a fair bit and copies it into the input letter, into both
outputs and into both auxiliaries. -/
noncomputable def uvOutputCopiesInputLaw : Measure (Bool × Bool × Bool × Bool × Bool) :=
  ((Fintype.card Bool : ℝ≥0∞)⁻¹ • Measure.count : Measure Bool).map fun b ↦ (b, b, b, b, b)

instance uvOutputCopiesInputLaw_isProbabilityMeasure :
    IsProbabilityMeasure uvOutputCopiesInputLaw := by
  unfold uvOutputCopiesInputLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem not_isUVChannelLaw_uvOutputCopiesInputLaw :
    ¬ IsUVChannelLaw uvBlindChannel uvOutputCopiesInputLaw := by
  intro h
  have hcopy : Measurable fun b : Bool ↦ ((b, b, b, b, b) : Bool × Bool × Bool × Bool × Bool) :=
    measurable_of_countable _
  have hout := h.map_input_output
  unfold uvOutputCopiesInputLaw uvBlindChannel at hout
  set μ : Measure Bool := (Fintype.card Bool : ℝ≥0∞)⁻¹ • Measure.count with hμ_def
  rw [Measure.map_map (measurable_of_countable _) hcopy,
    Measure.map_map (measurable_of_countable _) hcopy] at hout
  have hS : MeasurableSet {p : Bool × Bool × Bool | p.2 = (true, true)} :=
    measurable_snd (measurableSet_singleton (true, true))
  have hval := congrArg (fun ρ : Measure (Bool × Bool × Bool) ↦
    ρ {p : Bool × Bool × Bool | p.2 = (true, true)}) hout
  rw [Measure.map_apply (measurable_of_countable _) hS, Measure.compProd_apply hS] at hval
  simp only [Function.comp_def] at hval
  have hleft : μ ((fun b : Bool ↦ (b, b, b)) ⁻¹' {p : Bool × Bool × Bool | p.2 = (true, true)})
      = (2 : ℝ≥0∞)⁻¹ := by
    have hset : (fun b : Bool ↦ (b, b, b)) ⁻¹' {p : Bool × Bool × Bool | p.2 = (true, true)}
        = {true} := by
      ext b; cases b <;> simp
    rw [hset, hμ_def]
    simp
  have hright : ∫⁻ a : Bool, (Kernel.const Bool (Measure.dirac ((false, false) : Bool × Bool))) a
      (Prod.mk a ⁻¹' {p : Bool × Bool × Bool | p.2 = (true, true)})
      ∂(μ.map fun b : Bool ↦ b) = 0 := by
    simp [Kernel.const_apply, Measure.dirac_apply']
  rw [hleft, hright] at hval
  exact (ENNReal.inv_ne_zero.mpr (by norm_num)) hval

/-- The law of two copies of a fair bit. -/
noncomputable def uvFairBitPair : Measure (Bool × Bool) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (false, false) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (true, true)

instance uvFairBitPair_isProbabilityMeasure : IsProbabilityMeasure uvFairBitPair := by
  constructor
  simp [uvFairBitPair, ENNReal.inv_two_add_inv_two]

/-- The broadcast channel over a one-letter input alphabet that sends the same fair bit to both
receivers, so that its input carries no information at all. -/
noncomputable def uvFairBitChannel : BCChannel Unit Bool Bool := Kernel.const Unit uvFairBitPair

instance uvFairBitChannel_isMarkovKernel : IsMarkovKernel uvFairBitChannel := by
  unfold uvFairBitChannel
  infer_instance

/-- The five-tuple law over `uvFairBitChannel` whose first auxiliary is the common output bit and
whose second auxiliary is constant. -/
noncomputable def uvAuxCopiesOutputLaw : Measure (ℕ × ℕ × Unit × Bool × Bool) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (0, 0, (), false, false) +
    (2 : ℝ≥0∞)⁻¹ • Measure.dirac (1, 0, (), true, true)

instance uvAuxCopiesOutputLaw_isProbabilityMeasure :
    IsProbabilityMeasure uvAuxCopiesOutputLaw := by
  constructor
  simp [uvAuxCopiesOutputLaw, ENNReal.inv_two_add_inv_two]

theorem uvAuxCopiesOutputLaw_map_input_output :
    uvAuxCopiesOutputLaw.map (fun q ↦ (q.2.2.1, q.2.2.2))
      = (uvAuxCopiesOutputLaw.map fun q ↦ q.2.2.1) ⊗ₘ uvFairBitChannel := by
  have hX : Measurable (fun q : ℕ × ℕ × Unit × Bool × Bool ↦ q.2.2.1) := measurable_of_countable _
  have hXY : Measurable (fun q : ℕ × ℕ × Unit × Bool × Bool ↦ (q.2.2.1, q.2.2.2)) :=
    measurable_of_countable _
  have hmk : Measurable (Prod.mk (α := Unit) (β := Bool × Bool) ()) :=
    measurable_const.prodMk measurable_id
  have hmarg : (uvAuxCopiesOutputLaw.map fun q ↦ q.2.2.1) = Measure.dirac () := by
    rw [uvAuxCopiesOutputLaw, Measure.map_add _ _ hX, Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' hX, Measure.map_dirac' hX, ← add_smul, ENNReal.inv_two_add_inv_two,
      one_smul]
  rw [hmarg, uvFairBitChannel, Measure.compProd_const, Measure.dirac_prod, uvAuxCopiesOutputLaw,
    uvFairBitPair, Measure.map_add _ _ hXY, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' hXY, Measure.map_dirac' hXY,
    Measure.map_add _ _ hmk, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' hmk, Measure.map_dirac' hmk]

theorem not_isUVChannelLaw_uvAuxCopiesOutputLaw :
    ¬ IsUVChannelLaw uvFairBitChannel uvAuxCopiesOutputLaw := by
  intro h
  unfold IsUVChannelLaw at h
  set S : Set ((ℕ × ℕ × Unit) × (Bool × Bool)) := {z | z.1.1 = 0 ∧ z.2 = (true, true)} with hS_def
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  have hsplit : Measurable (fun q : ℕ × ℕ × Unit × Bool × Bool ↦
      ((q.1, q.2.1, q.2.2.1), q.2.2.2)) := measurable_of_countable _
  have hπ : Measurable (fun q : ℕ × ℕ × Unit × Bool × Bool ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_of_countable _
  have hmargπ : (uvAuxCopiesOutputLaw.map fun q ↦ (q.1, q.2.1, q.2.2.1))
      = (2 : ℝ≥0∞)⁻¹ • Measure.dirac ((0 : ℕ), (0 : ℕ), ()) +
        (2 : ℝ≥0∞)⁻¹ • Measure.dirac ((1 : ℕ), (0 : ℕ), ()) := by
    rw [uvAuxCopiesOutputLaw, Measure.map_add _ _ hπ, Measure.map_smul, Measure.map_smul,
      Measure.map_dirac' hπ, Measure.map_dirac' hπ]
  have hval := (Measure.ext_iff.mp h) S hS
  rw [Measure.map_apply hsplit hS, Measure.compProd_apply hS, hmargπ,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac, lintegral_dirac] at hval
  have hlhs : uvAuxCopiesOutputLaw ((fun q : ℕ × ℕ × Unit × Bool × Bool ↦
      ((q.1, q.2.1, q.2.2.1), q.2.2.2)) ⁻¹' S) = 0 := by
    have hset : (fun q : ℕ × ℕ × Unit × Bool × Bool ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) ⁻¹' S
        = {q | q.1 = 0 ∧ q.2.2.2 = (true, true)} := by
      ext q; simp [hS_def]
    rw [hset, uvAuxCopiesOutputLaw]
    simp [Measure.dirac_apply]
  have hset₁ : Prod.mk ((0 : ℕ), (0 : ℕ), ()) ⁻¹' S = {((true, true) : Bool × Bool)} := by
    ext y; simp [hS_def]
  have hset₂ : Prod.mk ((1 : ℕ), (0 : ℕ), ()) ⁻¹' S = (∅ : Set (Bool × Bool)) := by
    ext y; simp [hS_def]
  rw [hlhs, Kernel.comap_apply, Kernel.comap_apply, uvFairBitChannel, Kernel.const_apply] at hval
  rw [hset₁, hset₂, uvFairBitPair] at hval
  simp at hval

end NotVacuous

end InformationTheory.Shannon.BroadcastChannel
