import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.Operational
import InformationTheory.Shannon.BroadcastChannel.OuterBound
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Bridge
import InformationTheory.Shannon.CondKLIntegral
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

The main result is `bc_capacity_subset_uv`: the operational capacity region of the channel lies
in this region.  The rate pair of a code, each coordinate discounted by the error probability of
its receiver and by two bits per letter, is a point of the quadrilateral of the time-shared letter
law; the discount vanishes as the error tolerance shrinks and the block length grows, and the
region is a closed lower set, so the limit and the rate pairs below it are in the region too.

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
* `uvRelabel` — re-encoding of the two auxiliary alphabets of a five-tuple.
* `bcUVLetterKernel`, `bcUVLetterIndexLaw`, `bcUVTimeShare` — the letter laws of a code read as a
  Markov kernel from the letter index, the uniform law of that index, and the resulting mixture.
* `BroadcastCode.padFirst`, `BroadcastCode.padSecond` — a second message attached to a receiver
  that carries only one, which is what brings a code of a zero rate into the scope of a converse
  asking for at least two messages per receiver.

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
* `bcUVJointDistribution_isUVChannelLaw` — the letter-`i` law of a broadcast code is a channel
  law, so the letter laws of a code index the union.
* `condMutualInfo_compProd_fst_eq_lintegral` and `condMutualInfo_compProd_snd_eq_lintegral` — the
  tag-conditioned mutual information of a mixture is the tag average of the components, in the
  unconditional and in the conditional form.
* `bcUVTimeShare_uvInfo₁_ge` and its three companions — each information slot of the time-shared
  law dominates the average of the letter slots.
* `bc_uv_shrunk_point_mem` — the rate pair of a code, shrunk by the Fano slack per letter, lies
  in the region.
* `bc_uv_code_point_mem` — the same in the form the asymptotic argument consumes: each rate is
  discounted by the error probability of its receiver and by two bits per letter, which no
  longer refers to the message count of the other receiver.
* `bc_achievable_clamp_iff` — clamping a rate pair into the first quadrant leaves achievability
  unchanged, since both ceilings equal one at a nonpositive rate.
* `bc_uv_quadrant_mem_of_achievable` — an achievable rate pair with nonnegative coordinates lies
  in the region, obtained from the code points by letting the error tolerance and the per-letter
  residue vanish.
* `bc_capacity_subset_uv` — the operational capacity region lies in the UV outer region.

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

The asymptotic argument runs on `bc_uv_code_point_mem` rather than on `bc_uv_shrunk_point_mem`:
the latter subtracts the sum of both Fano slacks from each coordinate, and a slack of the other
receiver is not controlled by the rate of this one, since the message counts of an achievable
pair are bounded from below only.  Discounting each rate by its own error probability removes
that coupling, and the residue is two bits per block whatever the message counts are.

`compProd_comap_map_prodMap` and `compProd_pi_map_pair_eq_of_update_invariant` speak about a
composition product of an arbitrary measure with an arbitrary Markov kernel and mention no
broadcast-specific data.  The second generalizes `compProd_pi_map_pair_eq`: in place of the
input letter `x · i`, the first component may be any map that is invariant under updating the
`i`-th output coordinate and that retracts onto the input letter, which is what lets a padded
auxiliary variable sit there.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α : Type*} [MeasurableSpace α]
variable {β₁ : Type*} [MeasurableSpace β₁]
variable {β₂ : Type*} [MeasurableSpace β₂]
variable {M₁ M₂ n : ℕ}

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

/-- @audit:ok -/
lemma compProd_comap_map_prodMap {A A' B : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] (μ : Measure A) [SFinite μ] (κ : Kernel A' B) [IsMarkovKernel κ]
    {g : A → A'} (hg : Measurable g) :
    (μ ⊗ₘ κ.comap g hg).map (fun z ↦ (g z.1, z.2)) = (μ.map g) ⊗ₘ κ := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hmap : Measurable (fun z : A × B ↦ (g z.1, z.2)) :=
    (hg.comp measurable_fst).prodMk measurable_snd
  have hin : Measurable (fun a : A' ↦ ∫⁻ b, f (a, b) ∂(κ a)) :=
    Measurable.lintegral_kernel_prod_right' (κ := κ) hf
  have hcomp : Measurable (fun z : A × B ↦ f (g z.1, z.2)) := hf.comp hmap
  rw [lintegral_map hf hmap, Measure.lintegral_compProd hcomp,
    Measure.lintegral_compProd hf, lintegral_map hin hg]
  rfl

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

/-! ## The letter laws of a code are channel laws -/

section CodeLaw

/-- @audit:ok -/
lemma compProd_pi_map_pair_eq_of_update_invariant
    {M A B C : Type*} [MeasurableSpace M] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] {k : ℕ}
    (ν : Measure M) [IsProbabilityMeasure ν]
    (x : M → Fin k → A)
    (W : Kernel A B) [IsMarkovKernel W]
    (κ : Kernel M (Fin k → B)) [IsMarkovKernel κ]
    (hκ : ∀ m, κ m = Measure.pi (fun j ↦ W (x m j))) (i : Fin k)
    (G : M × (Fin k → B) → C) (hG : Measurable G)
    (hGupd : ∀ (m : M) (y : Fin k → B) (b : B), G (m, Function.update y i b) = G (m, y))
    (g : C → A) (hg : Measurable g) (hgG : ∀ ω, g (G ω) = x ω.1 i) :
    (ν ⊗ₘ κ).map (fun ω ↦ (G ω, ω.2 i)) = ((ν ⊗ₘ κ).map G) ⊗ₘ (W.comap g hg) := by
  have hYo : Measurable (fun ω : M × (Fin k → B) ↦ ω.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  have hpair : Measurable (fun ω : M × (Fin k → B) ↦ (G ω, ω.2 i)) := hG.prodMk hYo
  have hlhs : Measurable (fun ω : M × (Fin k → B) ↦ f (G ω, ω.2 i)) := hf.comp hpair
  have hin : Measurable (fun c : C ↦ ∫⁻ b, f (c, b) ∂((W.comap g hg) c)) :=
    Measurable.lintegral_kernel_prod_right' (κ := W.comap g hg) hf
  have hrhs : Measurable
      (fun ω : M × (Fin k → B) ↦ ∫⁻ b, f (G ω, b) ∂((W.comap g hg) (G ω))) := hin.comp hG
  rw [lintegral_map hf hpair, Measure.lintegral_compProd hf, lintegral_map hin hG,
    Measure.lintegral_compProd hlhs, Measure.lintegral_compProd hrhs]
  refine lintegral_congr fun m ↦ ?_
  rw [hκ]
  have hFm : Measurable (fun y : Fin k → B ↦ f (G (m, y), y i)) :=
    hf.comp ((hG.comp (measurable_const.prodMk measurable_id)).prodMk (measurable_pi_apply i))
  rw [lintegral_pi_reRandomize (fun j ↦ W (x m j)) i (fun y ↦ f (G (m, y), y i)) hFm]
  refine lintegral_congr fun y ↦ ?_
  have hker : (W.comap g hg) (G (m, y)) = W (x m i) := by
    rw [Kernel.comap_apply, hgG (m, y)]
  rw [hker]
  exact lintegral_congr fun b ↦ by rw [hGupd m y b, Function.update_self i b y]

variable [Nonempty β₁] [Nonempty β₂]

/-- @audit:ok -/
theorem bcUVJointDistribution_isUVChannelLaw
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    [NeZero M₁] [NeZero M₂] (i : Fin n) :
    IsUVChannelLaw W (bcUVJointDistribution c W i) := by
  set U := Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂) with hU_def
  set V := Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂) with hV_def
  set G : ((Fin M₁ × Fin M₂) × (Fin n → β₁ × β₂)) → U × V × α :=
    fun ω ↦ (uvAuxPad bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i ω,
      uvAuxPad bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i ω, c.encoder ω.1 i) with hG_def
  have hg : Measurable (fun r : U × V × α ↦ r.2.2) := measurable_snd.comp measurable_snd
  have hGm : Measurable G :=
    (measurable_uvAuxPad bcConverseMsg₂ bcConverseY₁s bcConverseY₂s measurable_bcConverseMsg₂
        measurable_bcConverseY₁s measurable_bcConverseY₂s i).prodMk
      ((measurable_uvAuxPad bcConverseMsg₁ bcConverseY₁s bcConverseY₂s measurable_bcConverseMsg₁
          measurable_bcConverseY₁s measurable_bcConverseY₂s i).prodMk
        ((measurable_pi_apply i).comp ((measurable_of_countable c.encoder).comp measurable_fst)))
  have hGupd : ∀ (m : Fin M₁ × Fin M₂) (y : Fin n → β₁ × β₂) (b : β₁ × β₂),
      G (m, Function.update y i b) = G (m, y) := by
    intro m y b
    have hpre : ∀ j : Fin i.val,
        bcConverseY₁s (M₁ := M₁) (M₂ := M₂) ⟨j.val, j.isLt.trans i.isLt⟩
            (m, Function.update y i b)
          = bcConverseY₁s ⟨j.val, j.isLt.trans i.isLt⟩ (m, y) := fun j ↦
      congrArg Prod.fst
        (Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt j.isLt)) b y)
    have hsuf : ∀ j : {j : Fin n // i.val < j.val},
        bcConverseY₂s (M₁ := M₁) (M₂ := M₂) j.val (m, Function.update y i b)
          = bcConverseY₂s j.val (m, y) := fun j ↦
      congrArg Prod.snd
        (Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt j.2).symm) b y)
    have haux₂ : uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i (m, Function.update y i b)
        = uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i (m, y) :=
      Prod.ext rfl (Prod.ext (funext hpre) (funext hsuf))
    have haux₁ : uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i (m, Function.update y i b)
        = uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i (m, y) :=
      Prod.ext rfl (Prod.ext (funext hpre) (funext hsuf))
    exact Prod.ext (congrArg (uvPadMap i) haux₂)
      (Prod.ext (congrArg (uvPadMap i) haux₁) rfl)
  have hπ : Measurable (fun q : U × V × α × β₁ × β₂ ↦ (q.1, q.2.1, q.2.2.1)) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hP : Measurable (fun q : U × V × α × β₁ × β₂ ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) :=
    hπ.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have key := compProd_pi_map_pair_eq_of_update_invariant (bcConverseInput M₁ M₂) c.encoder W
    (bcConverseKernel c W) (fun m ↦ rfl) i G hGm hGupd (fun r : U × V × α ↦ r.2.2) hg
    (fun _ ↦ rfl)
  unfold IsUVChannelLaw bcUVJointDistribution
  rw [Measure.map_map hP (measurable_bcUVTuple c i),
    Measure.map_map hπ (measurable_bcUVTuple c i)]
  exact key

end CodeLaw

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

/-! ## Averaging an information slot over a countable mixture

A mixture of laws indexed by a countable tag is a composition product of the tag law with the
kernel of the components, so the tag-conditioned mutual information of the mixture is the tag
average of the mutual informations of the components.  Adding back the tag term of the chain rule
turns that into an identity for the mutual information of the mixture itself, whenever the
variable in question recovers the tag; dropping the tag term leaves the averaging inequality. -/

section Averaging

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

end Averaging

/-! ## Re-encoding the auxiliary alphabets -/

section AuxRelabel

variable {U V U' V' : Type*}
variable [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace U'] [MeasurableSpace V']

/-- Re-encoding of the two auxiliary alphabets of a five-tuple, leaving the input letter and the
two output letters alone. -/
def uvRelabel (e₁ : U → U') (e₂ : V → V') :
    U × V × α × β₁ × β₂ → U' × V' × α × β₁ × β₂ :=
  fun q ↦ (e₁ q.1, e₂ q.2.1, q.2.2)

lemma measurable_uvRelabel {e₁ : U → U'} {e₂ : V → V'} (he₁ : Measurable e₁)
    (he₂ : Measurable e₂) : Measurable (uvRelabel (α := α) (β₁ := β₁) (β₂ := β₂) e₁ e₂) :=
  (he₁.comp measurable_fst).prodMk
    ((he₂.comp (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))

lemma uvInfo₁_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    {e₁ : U → U'} {e₂ : V → V'} {d₂ : V' → V} (he₁ : Measurable e₁) (he₂ : Measurable e₂)
    (hd₂ : Measurable d₂) (h₂ : ∀ v, d₂ (e₂ v) = v) :
    uvInfo₁ (ν.map (uvRelabel e₁ e₂)) = uvInfo₁ ν := by
  rw [uvInfo₁, uvInfo₁, mutualInfo_map_comp ν (uvRelabel e₁ e₂) (measurable_uvRelabel he₁ he₂)
    (fun q ↦ q.2.1) (measurable_fst.comp measurable_snd) (fun q ↦ q.2.2.2.1)
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))]
  exact mutualInfo_eq_of_leftInverse ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)
    (measurable_fst.comp measurable_snd)
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    he₂ hd₂ h₂

lemma uvInfo₂_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    {e₁ : U → U'} {e₂ : V → V'} {d₁ : U' → U} (he₁ : Measurable e₁) (he₂ : Measurable e₂)
    (hd₁ : Measurable d₁) (h₁ : ∀ u, d₁ (e₁ u) = u) :
    uvInfo₂ (ν.map (uvRelabel e₁ e₂)) = uvInfo₂ ν := by
  rw [uvInfo₂, uvInfo₂, mutualInfo_map_comp ν (uvRelabel e₁ e₂) (measurable_uvRelabel he₁ he₂)
    (fun q ↦ q.1) measurable_fst (fun q ↦ q.2.2.2.2)
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))]
  exact mutualInfo_eq_of_leftInverse ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2) measurable_fst
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    he₁ hd₁ h₁

section Sum

variable [StandardBorelSpace α] [Nonempty α]
variable [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
variable [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂]
variable [Fintype U] [MeasurableSingletonClass U] [Fintype V] [MeasurableSingletonClass V]

omit [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂]
  [Fintype V] [MeasurableSingletonClass V] in
lemma uvInfoSum₂_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    {e₁ : U → U'} {e₂ : V → V'} {d₁ : U' → U} (he₁ : Measurable e₁) (he₂ : Measurable e₂)
    (hd₁ : Measurable d₁) (h₁ : ∀ u, d₁ (e₁ u) = u) :
    uvInfoSum₂ (ν.map (uvRelabel e₁ e₂)) = uvInfoSum₂ ν := by
  rw [uvInfoSum₂, uvInfoSum₂, uvInfo₂_map_uvRelabel ν he₁ he₂ hd₁ h₁]
  congr 1
  rw [condMutualInfo_map_comp ν (uvRelabel e₁ e₂) (measurable_uvRelabel he₁ he₂)
    (fun q ↦ q.2.2.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (fun q ↦ q.2.2.2.1)
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (fun q ↦ q.1) measurable_fst]
  exact condMutualInfo_eq_of_leftInverse_cond ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1)
    (fun q ↦ q.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    measurable_fst he₁ hd₁ h₁
    (mutualInfo_ne_top ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.1) measurable_fst
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

omit [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [Fintype U] [MeasurableSingletonClass U] in
lemma uvInfoSum₁_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    {e₁ : U → U'} {e₂ : V → V'} {d₂ : V' → V} (he₁ : Measurable e₁) (he₂ : Measurable e₂)
    (hd₂ : Measurable d₂) (h₂ : ∀ v, d₂ (e₂ v) = v) :
    uvInfoSum₁ (ν.map (uvRelabel e₁ e₂)) = uvInfoSum₁ ν := by
  rw [uvInfoSum₁, uvInfoSum₁, uvInfo₁_map_uvRelabel ν he₁ he₂ hd₂ h₂]
  congr 1
  rw [condMutualInfo_map_comp ν (uvRelabel e₁ e₂) (measurable_uvRelabel he₁ he₂)
    (fun q ↦ q.2.2.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (fun q ↦ q.2.2.2.2)
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (fun q ↦ q.2.1) (measurable_fst.comp measurable_snd)]
  exact condMutualInfo_eq_of_leftInverse_cond ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2)
    (fun q ↦ q.2.1) (measurable_fst.comp (measurable_snd.comp measurable_snd))
    (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
    (measurable_fst.comp measurable_snd) he₂ hd₂ h₂
    (mutualInfo_ne_top ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.2) (measurable_fst.comp measurable_snd)
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

end Sum

end AuxRelabel

/-! ## Time sharing -/

section TimeSharing

variable [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
variable [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
variable [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂]

/-! ### The time-shared five-tuple law -/

/-- The letter laws of a broadcast code, read as a Markov kernel from the letter index. -/
noncomputable def bcUVLetterKernel (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    Kernel (Fin n) ((Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂) :=
  Kernel.ofFunOfCountable (bcUVJointDistribution c W)

/-- The uniform law of the letter index of a length-`n` block code. -/
noncomputable def bcUVLetterIndexLaw (n : ℕ) : Measure (Fin n) :=
  (Fintype.card (Fin n) : ℝ≥0∞)⁻¹ • Measure.count

instance bcUVLetterIndexLaw_isProbabilityMeasure [NeZero n] :
    IsProbabilityMeasure (bcUVLetterIndexLaw n) := by
  unfold bcUVLetterIndexLaw; infer_instance

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α] [Fintype β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Fintype β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] in
lemma bcUVLetterKernel_apply (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    (i : Fin n) : bcUVLetterKernel c W i = bcUVJointDistribution c W i := rfl

instance bcUVLetterKernel_isMarkovKernel (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] :
    IsMarkovKernel (bcUVLetterKernel c W) := by
  refine ⟨fun i ↦ ?_⟩
  change IsProbabilityMeasure (bcUVJointDistribution c W i)
  infer_instance

/-- The time-shared five-tuple law of a broadcast code: the letter index is drawn uniformly and
the letter-`i` five-tuple is read off the ambient measure.  The letter index survives inside both
auxiliaries, which already carry it as their first component.
@audit:ok -/
noncomputable def bcUVTimeShare (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    Measure ((Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂) :=
  ((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W).map Prod.snd

instance bcUVTimeShare_isProbabilityMeasure (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    IsProbabilityMeasure (bcUVTimeShare c W) := by
  unfold bcUVTimeShare
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α] [Fintype β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Fintype β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] in
lemma bcUVTimeShare_eq_sum (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    bcUVTimeShare c W = ∑ i : Fin n, (n : ℝ≥0∞)⁻¹ • bcUVJointDistribution c W i := by
  ext s hs
  rw [bcUVTimeShare, ← Measure.snd, Measure.snd_compProd,
    Measure.bind_apply hs (Kernel.aemeasurable _), bcUVLetterIndexLaw, lintegral_smul_measure,
    lintegral_count, tsum_fintype, smul_eq_mul, Fintype.card_fin, Measure.finsetSum_apply]
  simp [bcUVLetterKernel_apply, Finset.mul_sum]

omit [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [MeasurableSingletonClass β₂]
  [StandardBorelSpace β₂] in
lemma bcUVTimeShare_isUVChannelLaw (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    IsUVChannelLaw W (bcUVTimeShare c W) := by
  have hne : ((n : ℝ≥0∞))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  haveI : ∀ i : Fin n, IsFiniteMeasure ((n : ℝ≥0∞)⁻¹ • bcUVJointDistribution c W i) := fun i ↦
    Measure.smul_finite _ hne
  rw [bcUVTimeShare_eq_sum]
  exact IsUVChannelLaw.finsetSum
    (fun i ↦ (bcUVJointDistribution_isUVChannelLaw c W i).smul _) Finset.univ

omit [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [StandardBorelSpace β₂] in
lemma bcUVLetterKernel_ae_tag (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    ∀ᵐ p ∂((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W),
      p.2.1.1 = p.1 ∧ p.2.2.1.1 = p.1 := by
  rw [Measure.ae_compProd_iff (Set.toFinite _).measurableSet]
  filter_upwards with i
  rw [bcUVLetterKernel_apply, bcUVJointDistribution,
    ae_map_iff (measurable_bcUVTuple c i).aemeasurable (Set.toFinite _).measurableSet]
  filter_upwards with ω
  exact ⟨rfl, rfl⟩

/-! ### The four slots of the time-shared law dominate the letter averages -/

lemma lintegral_bcUVLetterIndexLaw [NeZero n] (F : Fin n → ℝ≥0∞) :
    ∫⁻ i, F i ∂(bcUVLetterIndexLaw n) = (n : ℝ≥0∞)⁻¹ * ∑ i, F i := by
  rw [bcUVLetterIndexLaw, lintegral_smul_measure, lintegral_count, tsum_fintype, smul_eq_mul,
    Fintype.card_fin]

omit [StandardBorelSpace α] [Nonempty α] in
lemma bcUVTimeShare_uvInfo₁_ge (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, uvInfo₁ (bcUVJointDistribution c W i)
      ≤ uvInfo₁ (bcUVTimeShare c W) := by
  have hV : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.1) :=
    measurable_fst.comp measurable_snd
  have hY₁ : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  rw [uvInfo₁, bcUVTimeShare, mutualInfo_map_comp _ Prod.snd measurable_snd _ hV _ hY₁,
    mutualInfo_compProd_eq_add_lintegral _ _ hV hY₁ (tag := fun a ↦ a.1) measurable_fst
      (by filter_upwards [bcUVLetterKernel_ae_tag c W] with p hp using hp.2),
    lintegral_bcUVLetterIndexLaw]
  simp only [uvInfo₁, bcUVLetterKernel_apply]
  exact le_add_self

omit [StandardBorelSpace α] [Nonempty α] in
lemma bcUVTimeShare_uvInfo₂_ge (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, uvInfo₂ (bcUVJointDistribution c W i)
      ≤ uvInfo₂ (bcUVTimeShare c W) := by
  have hU : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.1) := measurable_fst
  have hY₂ : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  rw [uvInfo₂, bcUVTimeShare, mutualInfo_map_comp _ Prod.snd measurable_snd _ hU _ hY₂,
    mutualInfo_compProd_eq_add_lintegral _ _ hU hY₂ (tag := fun a ↦ a.1) measurable_fst
      (by filter_upwards [bcUVLetterKernel_ae_tag c W] with p hp using hp.1),
    lintegral_bcUVLetterIndexLaw]
  simp only [uvInfo₂, bcUVLetterKernel_apply]
  exact le_add_self

lemma bcUVTimeShare_condMutualInfo₁_eq (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    condMutualInfo (bcUVTimeShare c W) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)
      = (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, condMutualInfo (bcUVJointDistribution c W i)
          (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1) := by
  have hne : ((n : ℝ≥0∞))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hX : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hY₁ : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hU : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.1) := measurable_fst
  have hmarg : (∫⁻ t, mutualInfo (bcUVLetterKernel c W t) (fun q ↦ q.1) (fun q ↦ q.2.2.2.1)
      ∂(bcUVLetterIndexLaw n)) ≠ ∞ := by
    rw [lintegral_bcUVLetterIndexLaw]
    exact ENNReal.mul_ne_top hne (ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ ↦
      lt_top_iff_ne_top.mpr (mutualInfo_ne_top _ _ _ hU hY₁)))
  have h1 := condMutualInfo_map_comp' ((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W) Prod.snd
    measurable_snd (bcUVTimeShare c W) rfl (fun q ↦ q.2.2.1) hX (fun q ↦ q.2.2.2.1) hY₁
    (fun q ↦ q.1) hU
  have h2 := condMutualInfo_compProd_snd_eq_lintegral (bcUVLetterIndexLaw n)
    (bcUVLetterKernel c W) hX hY₁ hU (tag := fun a ↦ a.1) measurable_fst
    (by filter_upwards [bcUVLetterKernel_ae_tag c W] with p hp using hp.1)
    (mutualInfo_ne_top _ _ _ measurable_fst (hY₁.comp measurable_snd)) hmarg
  rw [h1, h2, lintegral_bcUVLetterIndexLaw]
  simp only [bcUVLetterKernel_apply]

lemma bcUVTimeShare_condMutualInfo₂_eq (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    condMutualInfo (bcUVTimeShare c W) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1)
      = (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, condMutualInfo (bcUVJointDistribution c W i)
          (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1) := by
  have hne : ((n : ℝ≥0∞))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hX : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hY₂ : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hV : Measurable (fun q : (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)) ×
      (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂)) × α × β₁ × β₂ ↦ q.2.1) :=
    measurable_fst.comp measurable_snd
  have hmarg : (∫⁻ t, mutualInfo (bcUVLetterKernel c W t) (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.2)
      ∂(bcUVLetterIndexLaw n)) ≠ ∞ := by
    rw [lintegral_bcUVLetterIndexLaw]
    exact ENNReal.mul_ne_top hne (ne_of_lt (ENNReal.sum_lt_top.mpr fun i _ ↦
      lt_top_iff_ne_top.mpr (mutualInfo_ne_top _ _ _ hV hY₂)))
  have h1 := condMutualInfo_map_comp' ((bcUVLetterIndexLaw n) ⊗ₘ bcUVLetterKernel c W) Prod.snd
    measurable_snd (bcUVTimeShare c W) rfl (fun q ↦ q.2.2.1) hX (fun q ↦ q.2.2.2.2) hY₂
    (fun q ↦ q.2.1) hV
  have h2 := condMutualInfo_compProd_snd_eq_lintegral (bcUVLetterIndexLaw n)
    (bcUVLetterKernel c W) hX hY₂ hV (tag := fun a ↦ a.1) measurable_fst
    (by filter_upwards [bcUVLetterKernel_ae_tag c W] with p hp using hp.2)
    (mutualInfo_ne_top _ _ _ measurable_fst (hY₂.comp measurable_snd)) hmarg
  rw [h1, h2, lintegral_bcUVLetterIndexLaw]
  simp only [bcUVLetterKernel_apply]

lemma bcUVTimeShare_uvInfoSum₂_ge (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, uvInfoSum₂ (bcUVJointDistribution c W i)
      ≤ uvInfoSum₂ (bcUVTimeShare c W) := by
  simp only [uvInfoSum₂]
  rw [Finset.sum_add_distrib, mul_add, bcUVTimeShare_condMutualInfo₁_eq]
  exact add_le_add (bcUVTimeShare_uvInfo₂_ge c W) le_rfl

lemma bcUVTimeShare_uvInfoSum₁_ge (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂)
    [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] [NeZero n] :
    (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, uvInfoSum₁ (bcUVJointDistribution c W i)
      ≤ uvInfoSum₁ (bcUVTimeShare c W) := by
  simp only [uvInfoSum₁]
  rw [Finset.sum_add_distrib, mul_add, bcUVTimeShare_condMutualInfo₂_eq]
  exact add_le_add (bcUVTimeShare_uvInfo₁_ge c W) le_rfl

/-! ### The shrunk rate point -/

lemma le_toReal_of_inv_mul_le {S J : ℝ≥0∞} {m : ℕ} (hm : 0 < m)
    (hSJ : (m : ℝ≥0∞)⁻¹ * S ≤ J) (hJ : J ≠ ∞) {r : ℝ} (hr : (m : ℝ) * r ≤ S.toReal) :
    r ≤ J.toReal := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hminv : ((m : ℝ≥0∞))⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top m)
  have hmono := ENNReal.toReal_mono hJ hSJ
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, inv_mul_eq_div] at hmono
  have hkey : r ≤ S.toReal / (m : ℝ) := (le_div_iff₀ hm0).mpr (by linarith)
  linarith

/-- @audit:ok -/
lemma bc_uv_mixture_point_mem
    [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hn : 0 < n) {r₁ r₂ : ℝ}
    (hb₁ : (n : ℝ) * r₁ ≤ (∑ i : Fin n, uvInfo₁ (bcUVJointDistribution c W i)).toReal)
    (hb₂ : (n : ℝ) * r₂ ≤ (∑ i : Fin n, uvInfo₂ (bcUVJointDistribution c W i)).toReal)
    (hb₃ : (n : ℝ) * (r₁ + r₂)
      ≤ (∑ i : Fin n, uvInfoSum₂ (bcUVJointDistribution c W i)).toReal)
    (hb₄ : (n : ℝ) * (r₁ + r₂)
      ≤ (∑ i : Fin n, uvInfoSum₁ (bcUVJointDistribution c W i)).toReal) :
    (r₁, r₂) ∈ bcOuterRegionUV W := by
  haveI : NeZero n := ⟨hn.ne'⟩
  -- re-encode the two auxiliary alphabets of the time-shared law into `ℕ`
  obtain ⟨e₁, hinj₁⟩ := exists_injective_nat (Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂))
  obtain ⟨e₂, hinj₂⟩ := exists_injective_nat (Fin n × Fin M₁ × (Fin n → β₁) × (Fin n → β₂))
  have hme₁ : Measurable e₁ := measurable_of_countable e₁
  have hme₂ : Measurable e₂ := measurable_of_countable e₂
  have hd₁ : ∀ u, Function.invFun e₁ (e₁ u) = u := Function.leftInverse_invFun hinj₁
  have hd₂ : ∀ v, Function.invFun e₂ (e₂ v) = v := Function.leftInverse_invFun hinj₂
  haveI : IsProbabilityMeasure ((bcUVTimeShare c W).map (uvRelabel e₁ e₂)) :=
    Measure.isProbabilityMeasure_map (measurable_uvRelabel hme₁ hme₂).aemeasurable
  have hchan : IsUVChannelLaw W ((bcUVTimeShare c W).map (uvRelabel e₁ e₂)) :=
    (bcUVTimeShare_isUVChannelLaw c W).map_auxiliaries hme₁ hme₂
  -- the four slots are unchanged by the re-encoding
  have hs₁ : uvInfo₁ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂)) = uvInfo₁ (bcUVTimeShare c W) :=
    uvInfo₁_map_uvRelabel _ hme₁ hme₂ (measurable_of_countable _) hd₂
  have hs₂ : uvInfo₂ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂)) = uvInfo₂ (bcUVTimeShare c W) :=
    uvInfo₂_map_uvRelabel _ hme₁ hme₂ (measurable_of_countable _) hd₁
  have hs₃ : uvInfoSum₂ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))
      = uvInfoSum₂ (bcUVTimeShare c W) :=
    uvInfoSum₂_map_uvRelabel _ hme₁ hme₂ (measurable_of_countable _) hd₁
  have hs₄ : uvInfoSum₁ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))
      = uvInfoSum₁ (bcUVTimeShare c W) :=
    uvInfoSum₁_map_uvRelabel _ hme₁ hme₂ (measurable_of_countable _) hd₂
  -- finiteness of the four slots of the time-shared law
  have hfin₁ : uvInfo₁ (bcUVTimeShare c W) ≠ ∞ :=
    mutualInfo_ne_top _ _ _ (measurable_fst.comp measurable_snd)
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hfin₂ : uvInfo₂ (bcUVTimeShare c W) ≠ ∞ :=
    mutualInfo_ne_top _ _ _ measurable_fst
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hfin₃ : uvInfoSum₂ (bcUVTimeShare c W) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hfin₂, condMutualInfo_ne_top _ _ _ _
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      measurable_fst⟩
  have hfin₄ : uvInfoSum₁ (bcUVTimeShare c W) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hfin₁, condMutualInfo_ne_top _ _ _ _
      (measurable_fst.comp (measurable_snd.comp measurable_snd))
      (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
      (measurable_fst.comp measurable_snd)⟩
  -- the four bounds at the re-encoded time-shared law
  have g₁ : r₁ ≤ (uvInfo₁ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))).toReal :=
    le_toReal_of_inv_mul_le hn (by rw [hs₁]; exact bcUVTimeShare_uvInfo₁_ge c W)
      (by rw [hs₁]; exact hfin₁) hb₁
  have g₂ : r₂ ≤ (uvInfo₂ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))).toReal :=
    le_toReal_of_inv_mul_le hn (by rw [hs₂]; exact bcUVTimeShare_uvInfo₂_ge c W)
      (by rw [hs₂]; exact hfin₂) hb₂
  have g₃ : r₁ + r₂ ≤ (uvInfoSum₂ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))).toReal :=
    le_toReal_of_inv_mul_le hn (by rw [hs₃]; exact bcUVTimeShare_uvInfoSum₂_ge c W)
      (by rw [hs₃]; exact hfin₃) hb₃
  have g₄ : r₁ + r₂ ≤ (uvInfoSum₁ ((bcUVTimeShare c W).map (uvRelabel e₁ e₂))).toReal :=
    le_toReal_of_inv_mul_le hn (by rw [hs₄]; exact bcUVTimeShare_uvInfoSum₁_ge c W)
      (by rw [hs₄]; exact hfin₄) hb₄
  exact subset_closure (Set.mem_iUnion.mpr
    ⟨⟨(bcUVTimeShare c W).map (uvRelabel e₁ e₂), inferInstance⟩,
      Set.mem_iUnion.mpr ⟨hchan, g₁, g₂, g₃, g₄⟩⟩)

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace β₁] [Nonempty β₁] [StandardBorelSpace β₂] [Nonempty β₂] in
/-- @audit:ok -/
lemma bcConverseFanoSlack₁_le [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) :
    bcConverseFanoSlack₁ c W
      ≤ Real.log 2 + (c.averageErrorProb₁ W).toReal * Real.log (M₁ : ℝ) := by
  have hM : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hcard₁
  have hlog : Real.log ((M₁ : ℝ) - 1) ≤ Real.log (M₁ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [bcConverseFanoSlack₁, bcConverse_errorProb₁_eq]
  exact add_le_add Real.binEntropy_le_log_two
    (mul_le_mul_of_nonneg_left hlog ENNReal.toReal_nonneg)

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace β₁] [Nonempty β₁] [StandardBorelSpace β₂] [Nonempty β₂] in
/-- @audit:ok -/
lemma bcConverseFanoSlack₂_le [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard₂ : 2 ≤ M₂) :
    bcConverseFanoSlack₂ c W
      ≤ Real.log 2 + (c.averageErrorProb₂ W).toReal * Real.log (M₂ : ℝ) := by
  have hM : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hcard₂
  have hlog : Real.log ((M₂ : ℝ) - 1) ≤ Real.log (M₂ : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [bcConverseFanoSlack₂, bcConverse_errorProb₂_eq]
  exact add_le_add Real.binEntropy_le_log_two
    (mul_le_mul_of_nonneg_left hlog ENNReal.toReal_nonneg)

/-- @audit:ok -/
lemma bc_uv_converse_slots [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    InBCOuterRegionUV (Real.log (M₁ : ℝ)) (Real.log (M₂ : ℝ))
      ((∑ i : Fin n, uvInfo₁ (bcUVJointDistribution c W i)).toReal + bcConverseFanoSlack₁ c W)
      ((∑ i : Fin n, uvInfo₂ (bcUVJointDistribution c W i)).toReal + bcConverseFanoSlack₂ c W)
      ((∑ i : Fin n, uvInfoSum₂ (bcUVJointDistribution c W i)).toReal
        + bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W)
      ((∑ i : Fin n, uvInfoSum₁ (bcUVJointDistribution c W i)).toReal
        + bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) := by
  have hext := bc_uv_converse_from_code c W hcard₁ hcard₂
  rwa [show (∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
        (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i))
      = ∑ i : Fin n, uvInfo₁ (bcUVJointDistribution c W i) from
      Finset.sum_congr rfl fun i _ ↦ bc_uv_mutualInfo_eq_uvInfo₁_at c W i,
    show (∑ i : Fin n, mutualInfo (bcConverseAmbient c W)
        (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i))
      = ∑ i : Fin n, uvInfo₂ (bcUVJointDistribution c W i) from
      Finset.sum_congr rfl fun i _ ↦ bc_uv_mutualInfo_eq_uvInfo₂_at c W i,
    show (∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
          (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i) (bcConverseY₂s i)
        + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
          (bcConverseY₁s i) (uvAux bcConverseMsg₂ bcConverseY₁s bcConverseY₂s i)))
      = ∑ i : Fin n, uvInfoSum₂ (bcUVJointDistribution c W i) from
      Finset.sum_congr rfl fun i _ ↦ bc_uv_sum_eq_uvInfoSum₂_at c W i,
    show (∑ i : Fin n, (mutualInfo (bcConverseAmbient c W)
          (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i) (bcConverseY₁s i)
        + condMutualInfo (bcConverseAmbient c W) (fun ω ↦ c.encoder ω.1 i)
          (bcConverseY₂s i) (uvAux bcConverseMsg₁ bcConverseY₁s bcConverseY₂s i)))
      = ∑ i : Fin n, uvInfoSum₁ (bcUVJointDistribution c W i) from
      Finset.sum_congr rfl fun i _ ↦ bc_uv_sum_eq_uvInfoSum₁_at c W i] at hext

/-- The rate pair of a broadcast code, shrunk by the per-letter Fano slack, lies in the UV outer
region.  The letter index is absorbed into the auxiliaries, which already carry it, so the
average of the letter laws is again a channel law and dominates the per-letter averages of all
four information slots.
@audit:ok -/
theorem bc_uv_shrunk_point_mem
    [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) {R₁ R₂ : ℝ}
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂) :
    (R₁ - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) / (n : ℝ),
      R₂ - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) / (n : ℝ))
      ∈ bcOuterRegionUV W := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hM₁R : (2 : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hcard₁
  have hM₂R : (2 : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast hcard₂
  -- both Fano slacks are nonnegative, so shrinking by their sum only weakens the bounds
  have hF₁ : 0 ≤ bcConverseFanoSlack₁ c W := by
    unfold bcConverseFanoSlack₁
    exact add_nonneg (Real.binEntropy_nonneg measureReal_nonneg measureReal_le_one)
      (mul_nonneg measureReal_nonneg (Real.log_nonneg (by linarith)))
  have hF₂ : 0 ≤ bcConverseFanoSlack₂ c W := by
    unfold bcConverseFanoSlack₂
    exact add_nonneg (Real.binEntropy_nonneg measureReal_nonneg measureReal_le_one)
      (mul_nonneg measureReal_nonneg (Real.log_nonneg (by linarith)))
  -- the code-level converse, with the four per-letter sums identified as slot sums
  have hslot := bc_uv_converse_slots c W hcard₁ hcard₂
  have hr₁ : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hr₂ : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  have hcorner : ∀ r : ℝ, (n : ℝ) * (r - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W)
      / (n : ℝ)) = (n : ℝ) * r - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) := by
    intro r
    field_simp
  have hsumr : (n : ℝ) * ((R₁ - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) / (n : ℝ))
        + (R₂ - (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) / (n : ℝ)))
      = (n : ℝ) * R₁ + (n : ℝ) * R₂
        - 2 * (bcConverseFanoSlack₁ c W + bcConverseFanoSlack₂ c W) := by
    field_simp
    ring
  refine bc_uv_mixture_point_mem c W hn ?_ ?_ ?_ ?_
  · rw [hcorner]; linarith [hslot.bound₁, hF₂]
  · rw [hcorner]; linarith [hslot.bound₂, hF₁]
  · rw [hsumr]; linarith [hslot.sumBound₂, hF₁, hF₂]
  · rw [hsumr]; linarith [hslot.sumBound₁, hF₁, hF₂]

/-- @audit:ok -/
lemma bc_uv_code_point_mem [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) :
    ((Real.log (M₁ : ℝ) * (1 - (c.averageErrorProb₁ W).toReal) - 2 * Real.log 2) / (n : ℝ),
      (Real.log (M₂ : ℝ) * (1 - (c.averageErrorProb₂ W).toReal) - 2 * Real.log 2) / (n : ℝ))
      ∈ bcOuterRegionUV W := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hslot := bc_uv_converse_slots c W hcard₁ hcard₂
  have hF₁ := bcConverseFanoSlack₁_le c W hcard₁
  have hF₂ := bcConverseFanoSlack₂_le c W hcard₂
  have hcancel : ∀ x : ℝ, (n : ℝ) * (x / (n : ℝ)) = x := fun x ↦ by field_simp
  have hcancel₂ : ∀ x y : ℝ, (n : ℝ) * (x / (n : ℝ) + y / (n : ℝ)) = x + y := by
    intro x y; field_simp
  have he₁ : Real.log (M₁ : ℝ) * (1 - (c.averageErrorProb₁ W).toReal)
      = Real.log (M₁ : ℝ) - (c.averageErrorProb₁ W).toReal * Real.log (M₁ : ℝ) := by ring
  have he₂ : Real.log (M₂ : ℝ) * (1 - (c.averageErrorProb₂ W).toReal)
      = Real.log (M₂ : ℝ) - (c.averageErrorProb₂ W).toReal * Real.log (M₂ : ℝ) := by ring
  refine bc_uv_mixture_point_mem c W hn ?_ ?_ ?_ ?_
  · rw [hcancel, he₁]; linarith [hslot.bound₁]
  · rw [hcancel, he₂]; linarith [hslot.bound₂]
  · rw [hcancel₂, he₁, he₂]; linarith [hslot.sumBound₂]
  · rw [hcancel₂, he₁, he₂]; linarith [hslot.sumBound₁]

/-- @audit:ok -/
lemma bc_uv_rate_point_mem [NeZero M₁] [NeZero M₂]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (hn : 0 < n) (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) {r₁ r₂ : ℝ}
    (h₁ : (n : ℝ) * r₁ ≤ Real.log (M₁ : ℝ) * (1 - (c.averageErrorProb₁ W).toReal))
    (h₂ : (n : ℝ) * r₂ ≤ Real.log (M₂ : ℝ) * (1 - (c.averageErrorProb₂ W).toReal)) :
    (r₁ - 2 * Real.log 2 / (n : ℝ), r₂ - 2 * Real.log 2 / (n : ℝ)) ∈ bcOuterRegionUV W := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine bcOuterRegionUV_isLowerSet W (Prod.mk_le_mk.mpr ⟨?_, ?_⟩)
    (bc_uv_code_point_mem c W hn hcard₁ hcard₂)
  · have hd : r₁ ≤ Real.log (M₁ : ℝ) * (1 - (c.averageErrorProb₁ W).toReal) / (n : ℝ) := by
      rw [le_div_iff₀ hn']; linarith [h₁]
    rw [sub_div]
    linarith
  · have hd : r₂ ≤ Real.log (M₂ : ℝ) * (1 - (c.averageErrorProb₂ W).toReal) / (n : ℝ) := by
      rw [le_div_iff₀ hn']; linarith [h₂]
    rw [sub_div]
    linarith

end TimeSharing

/-! ## Padding a code that carries a single message -/

section Padding

namespace BroadcastCode

/-- A second receiver-1 message attached to a code that carries only one.  Both messages are sent
with the single codeword of the original code, so receiver 1 cannot separate them, while receiver
2 sees exactly the original code.  This is what puts a code of a nonpositive rate pair inside the
scope of the converse, which asks for at least two messages per receiver.
@audit:ok -/
def padFirst (c : BroadcastCode 1 M₂ n α β₁ β₂) : BroadcastCode 2 M₂ n α β₁ β₂ where
  encoder m := c.encoder (0, m.2)
  decoder₁ _ := 0
  decoder₂ := c.decoder₂

/-- The mirror of `padFirst` at the second receiver.
@audit:ok -/
def padSecond (c : BroadcastCode M₁ 1 n α β₁ β₂) : BroadcastCode M₁ 2 n α β₁ β₂ where
  encoder m := c.encoder (m.1, 0)
  decoder₁ := c.decoder₁
  decoder₂ _ := 0

/-- @audit:ok -/
lemma averageErrorProb₂_padFirst (c : BroadcastCode 1 M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    (c.padFirst).averageErrorProb₂ W = c.averageErrorProb₂ W := by
  rcases Nat.eq_zero_or_pos M₂ with hM | hM
  · subst hM; simp [averageErrorProb₂]
  have hpt : ∀ m : Fin 2 × Fin M₂,
      (c.padFirst).errorProbAt₂ W m = c.errorProbAt₂ W (0, m.2) := fun _ ↦ rfl
  have hsum2 : (∑ m : Fin 2 × Fin M₂, (c.padFirst).errorProbAt₂ W m)
      = 2 * ∑ b : Fin M₂, c.errorProbAt₂ W (0, b) := by
    simp only [hpt, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hsum1 : (∑ m : Fin 1 × Fin M₂, c.errorProbAt₂ W m)
      = ∑ b : Fin M₂, c.errorProbAt₂ W (0, b) := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  have hcast : ((2 * M₂ : ℕ) : ℝ≥0∞) = 2 * (M₂ : ℝ≥0∞) := by push_cast; ring
  unfold averageErrorProb₂
  rw [if_neg (by simpa using hM.ne'), if_neg (by simpa using hM.ne'), hsum2, hsum1, hcast,
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), one_mul,
    show (2 : ℝ≥0∞)⁻¹ * (M₂ : ℝ≥0∞)⁻¹ * (2 * ∑ b : Fin M₂, c.errorProbAt₂ W (0, b))
      = ((2 : ℝ≥0∞)⁻¹ * 2) * ((M₂ : ℝ≥0∞)⁻¹ * ∑ b : Fin M₂, c.errorProbAt₂ W (0, b)) by ring,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- @audit:ok -/
lemma averageErrorProb₁_padSecond (c : BroadcastCode M₁ 1 n α β₁ β₂) (W : BCChannel α β₁ β₂) :
    (c.padSecond).averageErrorProb₁ W = c.averageErrorProb₁ W := by
  rcases Nat.eq_zero_or_pos M₁ with hM | hM
  · subst hM; simp [averageErrorProb₁]
  have hpt : ∀ m : Fin M₁ × Fin 2,
      (c.padSecond).errorProbAt₁ W m = c.errorProbAt₁ W (m.1, 0) := fun _ ↦ rfl
  have hsum2 : (∑ m : Fin M₁ × Fin 2, (c.padSecond).errorProbAt₁ W m)
      = 2 * ∑ a : Fin M₁, c.errorProbAt₁ W (a, 0) := by
    simp only [hpt, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
  have hsum1 : (∑ m : Fin M₁ × Fin 1, c.errorProbAt₁ W m)
      = ∑ a : Fin M₁, c.errorProbAt₁ W (a, 0) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ ↦ Fin.sum_univ_one fun b ↦ c.errorProbAt₁ W (a, b)
  have hcast : ((M₁ * 2 : ℕ) : ℝ≥0∞) = (M₁ : ℝ≥0∞) * 2 := by push_cast; ring
  unfold averageErrorProb₁
  rw [if_neg (by simpa using hM.ne'), if_neg (by simpa using hM.ne'), hsum2, hsum1, hcast,
    ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num)), mul_one,
    show (M₁ : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹ * (2 * ∑ a : Fin M₁, c.errorProbAt₁ W (a, 0))
      = ((2 : ℝ≥0∞)⁻¹ * 2) * ((M₁ : ℝ≥0∞)⁻¹ * ∑ a : Fin M₁, c.errorProbAt₁ W (a, 0)) by ring,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

end BroadcastCode

end Padding

/-! ## The operational region lies in the UV outer region -/

section Operational

variable [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]
variable [Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]
variable [Fintype β₂] [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂]

omit [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α] [Fintype β₁]
  [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁] [Fintype β₂]
  [MeasurableSingletonClass β₂] [StandardBorelSpace β₂] [Nonempty β₂] in
/-- Clamping a rate pair into the first quadrant leaves achievability unchanged: at a nonpositive
rate the message count `⌈exp (n * R)⌉` a code is asked to carry is one, the same value it takes at
rate zero.
@audit:ok -/
lemma bc_achievable_clamp_iff (W : BCChannel α β₁ β₂) (R₁ R₂ : ℝ) :
    BCAchievable W R₁ R₂ ↔ BCAchievable W (max R₁ 0) (max R₂ 0) := by
  have key : ∀ (R : ℝ) (n : ℕ),
      Nat.ceil (Real.exp ((n : ℝ) * max R 0)) = Nat.ceil (Real.exp ((n : ℝ) * R)) := by
    intro R n
    by_cases hR : 0 ≤ R
    · rw [max_eq_left hR]
    · replace hR : R < 0 := not_le.mp hR
      rw [max_eq_right hR.le, mul_zero, Real.exp_zero, Nat.ceil_one]
      symm
      refine le_antisymm (Nat.ceil_le.mpr ?_) (Nat.ceil_pos.mpr (Real.exp_pos _))
      rw [Nat.cast_one, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hR.le)
  constructor
  · intro h ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨M₁, M₂, hM₁, hM₂, c, hc⟩ := hN n hn
    exact ⟨M₁, M₂, by rw [key R₁ n]; exact hM₁, by rw [key R₂ n]; exact hM₂, c, hc⟩
  · intro h ε' hε'
    obtain ⟨N, hN⟩ := h ε' hε'
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨M₁, M₂, hM₁, hM₂, c, hc⟩ := hN n hn
    exact ⟨M₁, M₂, by rw [← key R₁ n]; exact hM₁, by rw [← key R₂ n]; exact hM₂, c, hc⟩

/-- @audit:ok -/
lemma bc_uv_shifted_point_mem (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    (c : BroadcastCode M₁ M₂ n α β₁ β₂) (hn : 0 < n) {R₁ R₂ ε : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (hε1 : ε ≤ 1)
    (hM₁ : Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M₁)
    (hM₂ : Nat.ceil (Real.exp ((n : ℝ) * R₂)) ≤ M₂)
    (he₁ : (c.averageErrorProb₁ W).toReal ≤ ε) (he₂ : (c.averageErrorProb₂ W).toReal ≤ ε) :
    (R₁ * (1 - ε) - 2 * Real.log 2 / (n : ℝ), R₂ * (1 - ε) - 2 * Real.log 2 / (n : ℝ))
      ∈ bcOuterRegionUV W := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogM₁ : (n : ℝ) * R₁ ≤ Real.log (M₁ : ℝ) := le_log_of_ceil_exp_le hM₁
  have hlogM₂ : (n : ℝ) * R₂ ≤ Real.log (M₂ : ℝ) := le_log_of_ceil_exp_le hM₂
  have h1M₁ : 1 ≤ M₁ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hM₁
  have h1M₂ : 1 ≤ M₂ := lt_of_lt_of_le (Nat.ceil_pos.mpr (Real.exp_pos _)) hM₂
  have hnR₁ : (0 : ℝ) ≤ (n : ℝ) * R₁ := mul_nonneg hn'.le hR₁
  have hnR₂ : (0 : ℝ) ≤ (n : ℝ) * R₂ := mul_nonneg hn'.le hR₂
  have hprod₁ : (n : ℝ) * (R₁ * (1 - ε))
      ≤ Real.log (M₁ : ℝ) * (1 - (c.averageErrorProb₁ W).toReal) := by
    rw [← mul_assoc]
    exact mul_le_mul hlogM₁ (by linarith) (by linarith) (hnR₁.trans hlogM₁)
  have hprod₂ : (n : ℝ) * (R₂ * (1 - ε))
      ≤ Real.log (M₂ : ℝ) * (1 - (c.averageErrorProb₂ W).toReal) := by
    rw [← mul_assoc]
    exact mul_le_mul hlogM₂ (by linarith) (by linarith) (hnR₂.trans hlogM₂)
  -- a padded receiver contributes nothing: its rate is zero and its Fano slack is one bit
  have hpad : ∀ {K₁ K₂ : ℕ} (d : BroadcastCode K₁ K₂ n α β₁ β₂), (2 : ℕ) ≤ K₁ →
      (0 : ℝ) ≤ Real.log ((2 : ℕ) : ℝ) * (1 - (d.averageErrorProb₁ W).toReal) := by
    intro K₁ K₂ d _
    have hle : (d.averageErrorProb₁ W).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (d.averageErrorProb₁_le_one W)
    rw [hcast2]
    exact mul_nonneg (Real.log_nonneg (by norm_num)) (by linarith)
  have hpad' : ∀ {K₁ K₂ : ℕ} (d : BroadcastCode K₁ K₂ n α β₁ β₂), (2 : ℕ) ≤ K₂ →
      (0 : ℝ) ≤ Real.log ((2 : ℕ) : ℝ) * (1 - (d.averageErrorProb₂ W).toReal) := by
    intro K₁ K₂ d _
    have hle : (d.averageErrorProb₂ W).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (d.averageErrorProb₂_le_one W)
    rw [hcast2]
    exact mul_nonneg (Real.log_nonneg (by norm_num)) (by linarith)
  rcases eq_or_lt_of_le h1M₁ with h1 | h1
  · -- receiver 1 carries a single message, so its rate is zero and the code needs padding
    subst h1
    have hR₁z : R₁ = 0 := by
      rw [Nat.cast_one, Real.log_one] at hlogM₁
      have : R₁ ≤ 0 := by nlinarith
      linarith
    rcases eq_or_lt_of_le h1M₂ with h2 | h2
    · subst h2
      have hR₂z : R₂ = 0 := by
        rw [Nat.cast_one, Real.log_one] at hlogM₂
        have : R₂ ≤ 0 := by nlinarith
        linarith
      haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
      refine bc_uv_rate_point_mem (c.padFirst.padSecond) W hn le_rfl le_rfl ?_ ?_
      · rw [hR₁z, zero_mul, mul_zero]
        exact hpad _ le_rfl
      · rw [hR₂z, zero_mul, mul_zero]
        exact hpad' _ le_rfl
    · haveI : NeZero M₂ := ⟨by omega⟩
      haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
      refine bc_uv_rate_point_mem c.padFirst W hn le_rfl (by omega) ?_ ?_
      · rw [hR₁z, zero_mul, mul_zero]
        exact hpad _ le_rfl
      · rw [BroadcastCode.averageErrorProb₂_padFirst]
        exact hprod₂
  · rcases eq_or_lt_of_le h1M₂ with h2 | h2
    · subst h2
      have hR₂z : R₂ = 0 := by
        rw [Nat.cast_one, Real.log_one] at hlogM₂
        have : R₂ ≤ 0 := by nlinarith
        linarith
      haveI : NeZero M₁ := ⟨by omega⟩
      haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
      refine bc_uv_rate_point_mem c.padSecond W hn (by omega) le_rfl ?_ ?_
      · rw [BroadcastCode.averageErrorProb₁_padSecond]
        exact hprod₁
      · rw [hR₂z, zero_mul, mul_zero]
        exact hpad' _ le_rfl
    · haveI : NeZero M₁ := ⟨by omega⟩
      haveI : NeZero M₂ := ⟨by omega⟩
      exact bc_uv_rate_point_mem c W hn (by omega) (by omega) hprod₁ hprod₂

/-- An achievable rate pair with nonnegative coordinates lies in the UV outer region.  For every
error tolerance and every block length the pair, discounted by the error probability of each
receiver and by two bits per letter, is a point of the region; those points converge to the pair
itself as the tolerance shrinks and the block length grows, and the region is closed.
@audit:ok -/
lemma bc_uv_quadrant_mem_of_achievable (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {R₁ R₂ : ℝ}
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (hach : BCAchievable W R₁ R₂) :
    (R₁, R₂) ∈ bcOuterRegionUV W := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ η : ℝ, 0 < η → (R₁ - η, R₂ - η) ∈ bcOuterRegionUV W := by
    intro η hη
    have hden : (0 : ℝ) < 2 * (R₁ + R₂ + 1) := by linarith
    set ε := min (1 / 2) (η / (2 * (R₁ + R₂ + 1))) with hεdef
    have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hεle : ε ≤ η / (2 * (R₁ + R₂ + 1)) := min_le_right _ _
    obtain ⟨N, hN⟩ := hach ε hε0
    obtain ⟨n, hnge⟩ := exists_nat_ge (max (max (N : ℝ) 1) (4 * Real.log 2 / η))
    have hnN : N ≤ n := by
      exact_mod_cast ((le_max_left (N : ℝ) 1).trans (le_max_left _ _)).trans hnge
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := ((le_max_right (N : ℝ) 1).trans (le_max_left _ _)).trans hnge
    have hn : 0 < n := by exact_mod_cast lt_of_lt_of_le zero_lt_one hn1
    have hn' : (0 : ℝ) < (n : ℝ) := by linarith
    obtain ⟨M₁, M₂, hM₁, hM₂, c, hc₁, hc₂⟩ := hN n hnN
    -- the error term and the two-bit term are each at most half the target slack
    have hA : R₁ * ε ≤ η / 2 := by
      have hεD : ε * (2 * (R₁ + R₂ + 1)) ≤ η := (le_div_iff₀ hden).mp hεle
      nlinarith [mul_nonneg hε0.le hR₂, hε0.le]
    have hA' : R₂ * ε ≤ η / 2 := by
      have hεD : ε * (2 * (R₁ + R₂ + 1)) ≤ η := (le_div_iff₀ hden).mp hεle
      nlinarith [mul_nonneg hε0.le hR₁, hε0.le]
    have hB : 2 * Real.log 2 / (n : ℝ) ≤ η / 2 := by
      have h4 : 4 * Real.log 2 / η ≤ (n : ℝ) := (le_max_right _ _).trans hnge
      rw [div_le_iff₀ hη] at h4
      rw [div_le_div_iff₀ hn' (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hmem := bc_uv_shifted_point_mem W c hn hR₁ hR₂ hε1 hM₁ hM₂ hc₁.le hc₂.le
    refine bcOuterRegionUV_isLowerSet W (Prod.mk_le_mk.mpr ⟨?_, ?_⟩) hmem
    · have : R₁ * (1 - ε) = R₁ - R₁ * ε := by ring
      rw [this]; linarith
    · have : R₂ * (1 - ε) = R₂ - R₂ * ε := by ring
      rw [this]; linarith
  have ht : Filter.Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Filter.Tendsto (fun k : ℕ ↦ R₁ - 1 / ((k : ℝ) + 1)) Filter.atTop (nhds R₁) := by
    simpa using tendsto_const_nhds.sub ht
  have h2 : Filter.Tendsto (fun k : ℕ ↦ R₂ - 1 / ((k : ℝ) + 1)) Filter.atTop (nhds R₂) := by
    simpa using tendsto_const_nhds.sub ht
  exact (bcOuterRegionUV_isClosed W).mem_of_tendsto (h1.prodMk_nhds h2)
    (Filter.Eventually.of_forall fun k ↦ key _ (by positivity))

/-- The operational capacity region of a broadcast channel is contained in the UV (Nair–El Gamal)
outer region.  Together with `marton_region_subset_capacity` this places the capacity region
between Marton's inner bound and the UV outer bound as subsets of the plane.

Nonpositive rates are covered without a sign hypothesis: clamping a rate pair into the first
quadrant leaves achievability unchanged, and the outer region is a lower set, so the clamped pair
carries the original one.
@audit:ok -/
@[entry_point]
theorem bc_capacity_subset_uv (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    bcCapacityRegion W ⊆ bcOuterRegionUV W := by
  rw [bcCapacityRegion]
  refine (bcOuterRegionUV_isClosed W).closure_subset_iff.mpr fun p hp ↦ ?_
  have hmem : (max p.1 0, max p.2 0) ∈ bcOuterRegionUV W :=
    bc_uv_quadrant_mem_of_achievable W (le_max_right _ _) (le_max_right _ _)
      ((bc_achievable_clamp_iff W p.1 p.2).mp hp)
  exact bcOuterRegionUV_isLowerSet W ⟨le_max_left _ _, le_max_left _ _⟩ hmem

end Operational

end InformationTheory.Shannon.BroadcastChannel

