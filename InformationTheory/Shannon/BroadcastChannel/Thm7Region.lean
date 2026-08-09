import InformationTheory.Shannon.BroadcastChannel.Marton.RegionCardinality
import InformationTheory.Shannon.BroadcastChannel.OuterBoundTransport
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Conditional
import Mathlib.Data.Fin.VecNotation

/-!
# Broadcast channel — the three-rate region of the auxiliary-receiver outer bound

The auxiliary-receiver outer bound constrains a rate triple `(R₀, R₁, R₂)` through three systems
of auxiliary variables — a plain one `(U, V, W)`, a first enhanced one `(Ũ, Ṽ, W̃)` and a second
enhanced one `(Û, V̂, Ŵ)` — together with the output `J` of an auxiliary receiver. The region is
a union over input laws of an intersection over auxiliary receivers of a union over the joint
laws of the nine auxiliary variables, the input, the two outputs and the auxiliary output.

## Main definitions

* `Thm7AuxIdx` — the index `(j, i)` of the `i`-th member of the `j`-th auxiliary triple.
* `Thm7Ambient` — the thirteen-factor ambient space of one joint law.
* `thm7Slots` — the twenty-five informations a joint law provides.
* `InThm7` — the constraint bundle on a rate triple, read off the slots.
* `IsThm7Eligible` — the compatibility conditions a joint law's slots have to satisfy.
* `IsThm7Law` — the factorization a joint law has to satisfy.
* `thm7Cap` — the cardinality caps on the auxiliary alphabets.
* `thm7RegionOfLaw`, `thm7RegionOfAuxReceiver`, `thm7RegionOfInput` — the three inner levels of
  the region, one per binder of the nest.
* `thm7Region` — the region itself, as a subset of `ℝ³`.
* `zeroRateSlice` and `thm7RegionSlice` — the `R₀ = 0` slice, as a subset of the plane.
* `thm7DegenerateLaw` — the joint law a point mass on the input induces, with one-point auxiliary
  alphabets.

## Main statements

* `isClosed_thm7Region` — the region is closed, without passing to the closure.
* `thm7Region_nonempty` — the region is inhabited when the channel is a Markov kernel.

## Implementation notes

The ambient space of one joint law is a product of thirteen factors, and the constraints read
twenty-five informations off it. Both the constraint bundle and the eligibility conditions that
select which joint laws take part are stated against those slots rather than against the law, so
that a slot is named once and used by several constraints.

The joint laws are bound as probability measures rather than as finite measures: a joint law is a
distribution, and the compactness of the space of probability measures on a finite ambient space
is what a closedness argument for the union has to reach for.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel.Marton

universe u

/-- The index of an auxiliary variable: `(j, i)` is the `i`-th member of the `j`-th auxiliary
triple, so that `(0, ·) = (U, V, W)`, `(1, ·) = (Ũ, Ṽ, W̃)` and `(2, ·) = (Û, V̂, Ŵ)`. Slot
`i = 2` is the `W`-type member of its triple. -/
abbrev Thm7AuxIdx := Fin 3 × Fin 3

/-- The ambient space of one joint law: nine auxiliary variables as a `Thm7AuxIdx`-indexed
family, together with the input, the two outputs and the auxiliary receiver output. -/
abbrev Thm7Ambient (kv : Thm7AuxIdx → ℕ) (kJ : ℕ) (α β₁ β₂ : Type u) : Type u :=
  ((i : Thm7AuxIdx) → bcAuxAlphabet.{u} (kv i)) × α × β₁ × β₂ × bcAuxAlphabet.{u} kJ

variable {α β₁ β₂ : Type u} [Fintype α] [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [Fintype β₁] [MeasurableSpace β₁] [StandardBorelSpace β₁] [Nonempty β₁]
  [Fintype β₂] [MeasurableSpace β₂] [StandardBorelSpace β₂] [Nonempty β₂]

section Slots

variable {kv : Thm7AuxIdx → ℕ} {kJ : ℕ}

/-- The twenty-five informations of a joint law, as reals. Slots `0-16` are the ones the
constraint bundle mentions; slots `17-24` are the further ones only the eligibility conditions
mention. The informations are differenced by the constraints, so they are taken in `ℝ` rather
than in `ℝ≥0∞`. -/
noncomputable def thm7Slots (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) [IsFiniteMeasure ν] :
    Fin 25 → ℝ :=
  let A : (i : Thm7AuxIdx) → Thm7Ambient kv kJ α β₁ β₂ → bcAuxAlphabet.{u} (kv i) := fun i q ↦ q.1 i
  let X : Thm7Ambient kv kJ α β₁ β₂ → α := fun q ↦ q.2.1
  let Y : Thm7Ambient kv kJ α β₁ β₂ → β₁ := fun q ↦ q.2.2.1
  let Z : Thm7Ambient kv kJ α β₁ β₂ → β₂ := fun q ↦ q.2.2.2.1
  let J : Thm7Ambient kv kJ α β₁ β₂ → bcAuxAlphabet.{u} kJ := fun q ↦ q.2.2.2.2
  ![ mutualInfoReal ν (A (0, 2)) Y,                                  -- 0  I(W ; Y)
     mutualInfoReal ν (A (2, 2)) Y,                                  -- 1  I(Ŵ ; Y)
     mutualInfoReal ν (A (0, 2)) Z,                                  -- 2  I(W ; Z)
     mutualInfoReal ν (A (1, 2)) Z,                                  -- 3  I(W̃ ; Z)
     condMutualInfoReal ν (A (0, 0)) Y (A (0, 2)),                   -- 4  I(U ; Y | W)
     mutualInfoReal ν (A (1, 2)) J,                                  -- 5  I(W̃ ; J)
     mutualInfoReal ν (A (2, 2)) J,                                  -- 6  I(Ŵ ; J)
     condMutualInfoReal ν (A (1, 0)) J (A (1, 2)),                   -- 7  I(Ũ ; J | W̃)
     condMutualInfoReal ν (A (2, 0)) Y (A (2, 2)),                   -- 8  I(Û ; Y | Ŵ)
     condMutualInfoReal ν (A (2, 0)) J (A (2, 2)),                   -- 9  I(Û ; J | Ŵ)
     condMutualInfoReal ν (A (0, 1)) Z (A (0, 2)),                   -- 10 I(V ; Z | W)
     condMutualInfoReal ν (A (2, 1)) J (A (2, 2)),                   -- 11 I(V̂ ; J | Ŵ)
     condMutualInfoReal ν (A (1, 1)) Z (A (1, 2)),                   -- 12 I(Ṽ ; Z | W̃)
     condMutualInfoReal ν (A (1, 1)) J (A (1, 2)),                   -- 13 I(Ṽ ; J | W̃)
     mutualInfoReal ν X J,                                           -- 14 I(X ; J)
     condMutualInfoReal ν X Y (fun q ↦ (A (0, 1) q, A (0, 2) q)),    -- 15 I(X ; Y | V, W)
     condMutualInfoReal ν X Z (fun q ↦ (A (0, 0) q, A (0, 2) q)),    -- 16 I(X ; Z | U, W)
     condMutualInfoReal ν (A (1, 0)) Z (A (1, 2)),                   -- 17 I(Ũ ; Z | W̃)
     condMutualInfoReal ν (A (0, 0)) Z (A (0, 2)),                   -- 18 I(U ; Z | W)
     condMutualInfoReal ν (A (2, 1)) Y (A (2, 2)),                   -- 19 I(V̂ ; Y | Ŵ)
     condMutualInfoReal ν (A (0, 1)) Y (A (0, 2)),                   -- 20 I(V ; Y | W)
     condMutualInfoReal ν X Z (fun q ↦ (A (1, 0) q, A (1, 2) q)),    -- 21 I(X ; Z | Ũ, W̃)
     condMutualInfoReal ν X J (fun q ↦ (A (1, 0) q, A (1, 2) q)),    -- 22 I(X ; J | Ũ, W̃)
     condMutualInfoReal ν X Y (fun q ↦ (A (2, 1) q, A (2, 2) q)),    -- 23 I(X ; Y | V̂, Ŵ)
     condMutualInfoReal ν X J (fun q ↦ (A (2, 1) q, A (2, 2) q)) ]   -- 24 I(X ; J | V̂, Ŵ)

end Slots

/-- The constraint bundle on a rate triple `(R₀, R₁, R₂)`, read off the twenty-five slots. -/
def InThm7 (s : Fin 25 → ℝ) (R : ℝ × ℝ × ℝ) : Prop :=
  R.1 ≤ min (min (s 0) (s 1)) (min (s 2) (s 3))
  ∧ R.1 + R.2.1 ≤ min (s 0) (s 2) + s 4
  ∧ R.1 + R.2.1 ≤
      min (s 3 + min 0 (s 0 - s 2)) (s 5 + s 1 - s 6) + s 7 + s 8 - s 9
  ∧ R.1 + R.2.1 ≤ min (s 1 + min 0 (s 2 - s 0)) (s 6 + s 3 - s 5) + s 8
  ∧ R.1 + R.2.2 ≤ min (s 0) (s 2) + s 10
  ∧ R.1 + R.2.2 ≤
      min (s 1 + min 0 (s 2 - s 0)) (s 6 + s 3 - s 5) + s 11 + s 12 - s 13
  ∧ R.1 + R.2.2 ≤ min (s 3 + min 0 (s 0 - s 2)) (s 5 + s 1 - s 6) + s 12
  ∧ R.1 + R.2.1 + R.2.2 ≤
      min (s 1 - s 6) (s 3 - s 5) + s 14 + s 8 - s 9 + s 12 - s 13
  ∧ R.1 + R.2.1 + R.2.2 ≤ min (s 0) (s 2) + min (s 10 + s 15) (s 4 + s 16)

/-- The compatibility conditions a joint law's slots have to satisfy for the law to take part in
the region. -/
def IsThm7Eligible (s : Fin 25 → ℝ) : Prop :=
  (s 3 - s 5) + (s 6 - s 1) = s 2 - s 0
  ∧ (s 17 - s 7) + (s 9 - s 8) = s 18 - s 4
  ∧ (s 12 - s 13) + (s 11 - s 19) = s 10 - s 20
  ∧ 0 ≤ s 21 - s 22 ∧ s 21 - s 22 ≤ s 12 - s 13
  ∧ 0 ≤ s 23 - s 24 ∧ s 23 - s 24 ≤ s 8 - s 9
  ∧ s 10 + s 15 = s 4 + s 16

section Law

variable {kv : Thm7AuxIdx → ℕ} {kJ : ℕ}

/-- The factorization a joint law has to satisfy, as four clauses: the three auxiliary triples
are conditionally independent given the input; the pair of outputs is the channel applied to the
input; the auxiliary receiver output is its kernel applied to the input and the two outputs; and
the input has the prescribed law.

The last three clauses constrain marginals only. They pin the law of `(X, Y, Z)` and the law of
`((X, Y, Z), J)`, so they say which kernels produce the outputs, but they do not by themselves
make the outputs conditionally independent of the auxiliary variables given the input. A joint
law satisfying the four clauses is therefore not forced to be a product of the conditional laws
of the three triples with the two channels, and this predicate admits more laws than that
product form does. Every set built from it below is accordingly at least as large as the
corresponding set built from the product form. -/
def IsThm7Law (W : BCChannel α β₁ β₂) (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ))
    (p : Measure α) (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) [IsFiniteMeasure ν] : Prop :=
  @iCondIndepFun (Thm7Ambient kv kJ α β₁ β₂) (Fin 3) _ _ inferInstance
      ((measurable_fst.comp measurable_snd :
        Measurable (fun q : Thm7Ambient kv kJ α β₁ β₂ ↦ q.2.1)).comap_le)
      (fun j ↦ (i : Fin 3) → bcAuxAlphabet.{u} (kv (j, i))) _
      (fun j q i ↦ q.1 (j, i)) ν inferInstance
  ∧ ν.map (fun q ↦ (q.2.1, q.2.2.1, q.2.2.2.1)) = (ν.map (fun q ↦ q.2.1)) ⊗ₘ W
  ∧ ν.map (fun q ↦ ((q.2.1, q.2.2.1, q.2.2.2.1), q.2.2.2.2)) =
      (ν.map (fun q ↦ (q.2.1, q.2.2.1, q.2.2.2.1))) ⊗ₘ TJ
  ∧ ν.map (fun q ↦ q.2.1) = p

end Law

/-- The cardinality caps on the auxiliary alphabets: the `W`-type member of each triple is capped
at `|X| + 6` and every other member at `|X| + 1`. -/
def thm7Cap (α : Type u) [Fintype α] (i : Thm7AuxIdx) : ℕ :=
  if i.2 = 2 then Fintype.card α + 6 else Fintype.card α + 1

/-- One joint law's worth of the region: the rate triples the law admits, or nothing at all when
the law fails the compatibility conditions. -/
noncomputable def thm7RegionOfLaw {kv : Thm7AuxIdx → ℕ} {kJ : ℕ}
    (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) [IsFiniteMeasure ν] : Set (ℝ × ℝ × ℝ) :=
  {R | InThm7 (thm7Slots ν) R ∧ IsThm7Eligible (thm7Slots ν)}

/-- The rate triples one auxiliary receiver admits for a fixed input law: the union over the
joint laws obeying the cardinality caps. -/
noncomputable def thm7RegionOfAuxReceiver (W : BCChannel α β₁ β₂) (p : Measure α) {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) : Set (ℝ × ℝ × ℝ) :=
  ⋃ (kv : Thm7AuxIdx → ℕ) (_ : ∀ i, kv i < thm7Cap α i)
    (ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂))
    (_ : IsThm7Law W TJ p (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))),
    thm7RegionOfLaw (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))

/-- The rate triples a fixed input law admits: the intersection over the auxiliary receivers,
which the genie is free to choose. -/
noncomputable def thm7RegionOfInput (W : BCChannel α β₁ β₂) (p : Measure α) :
    Set (ℝ × ℝ × ℝ) :=
  ⋂ (kJ : ℕ) (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) (_ : IsMarkovKernel TJ),
    thm7RegionOfAuxReceiver W p TJ

/-- The region of the auxiliary-receiver outer bound, as a subset of `ℝ³`: a union over input
laws of an intersection over auxiliary receivers of a union over joint laws obeying the
cardinality caps. -/
noncomputable def thm7Region (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ × ℝ) :=
  ⋃ (p : ProbabilityMeasure α), thm7RegionOfInput W (p : Measure α)

/-- The `R₀ = 0` slice of a set of rate triples, as a subset of the plane. -/
def zeroRateSlice (S : Set (ℝ × ℝ × ℝ)) : Set (ℝ × ℝ) := {q | (0, q.1, q.2) ∈ S}

/-- The `R₀ = 0` slice of the region of the auxiliary-receiver outer bound. -/
noncomputable def thm7RegionSlice (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ) :=
  zeroRateSlice (thm7Region W)

lemma zeroRateSlice_iUnion {ι : Type*} (S : ι → Set (ℝ × ℝ × ℝ)) :
    zeroRateSlice (⋃ i, S i) = ⋃ i, zeroRateSlice (S i) := by
  ext q; simp [zeroRateSlice]

lemma zeroRateSlice_iInter {ι : Type*} (S : ι → Set (ℝ × ℝ × ℝ)) :
    zeroRateSlice (⋂ i, S i) = ⋂ i, zeroRateSlice (S i) := by
  ext q; simp [zeroRateSlice]

section Closedness

lemma isClosed_setOf_inThm7 (s : Fin 25 → ℝ) : IsClosed {R : ℝ × ℝ × ℝ | InThm7 s R} := by
  simp only [InThm7, Set.setOf_and]
  repeat' apply IsClosed.inter
  all_goals exact isClosed_le (by fun_prop) continuous_const

omit [Fintype α] [Fintype β₁] [Fintype β₂] in
lemma isClosed_thm7RegionOfLaw {kv : Thm7AuxIdx → ℕ} {kJ : ℕ}
    (ν : Measure (Thm7Ambient kv kJ α β₁ β₂)) [IsFiniteMeasure ν] :
    IsClosed (thm7RegionOfLaw ν) := by
  by_cases h : IsThm7Eligible (thm7Slots ν)
  · have hset : thm7RegionOfLaw ν = {R : ℝ × ℝ × ℝ | InThm7 (thm7Slots ν) R} := by
      ext R; simp [thm7RegionOfLaw, h]
    rw [hset]
    exact isClosed_setOf_inThm7 _
  · have hset : thm7RegionOfLaw ν = (∅ : Set (ℝ × ℝ × ℝ)) := by
      ext R; simp [thm7RegionOfLaw, h]
    rw [hset]
    exact isClosed_empty

lemma finite_setOf_lt_thm7Cap (α : Type u) [Fintype α] :
    {kv : Thm7AuxIdx → ℕ | ∀ i, kv i < thm7Cap α i}.Finite := by
  have hpi : {kv : Thm7AuxIdx → ℕ | ∀ i, kv i < thm7Cap α i}
      = Set.pi Set.univ fun i ↦ Set.Iio (thm7Cap α i) := by
    ext kv; simp [Set.mem_pi]
  rw [hpi]
  exact Set.Finite.pi fun i ↦ Set.finite_Iio _

/-- The union over the joint laws of one fixed pair of auxiliary alphabets is closed.

The index is a space of probability measures on a finite ambient space, so it is compact once it
carries the weak topology, and the union of a compact family of closed sets is closed as soon as
the family has a closed graph. The graph is closed exactly when the twenty-five informations
depend continuously on the joint law and the factorization cuts out a closed set of joint laws.
Each information is a combination of entropies, whose continuity in the joint law is
`continuous_entropy_of_discrete`; the missing piece is that the four clauses of the
factorization cut out a closed set.

@residual(plan:bc-computable-region-formalization) -/
lemma isClosed_iUnion_thm7RegionOfLaw (W : BCChannel α β₁ β₂) (p : Measure α) {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) (kv : Thm7AuxIdx → ℕ) :
    IsClosed (⋃ (ν : ProbabilityMeasure (Thm7Ambient kv kJ α β₁ β₂))
      (_ : IsThm7Law W TJ p (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))),
      thm7RegionOfLaw (ν : Measure (Thm7Ambient kv kJ α β₁ β₂))) := by
  sorry

lemma isClosed_thm7RegionOfAuxReceiver (W : BCChannel α β₁ β₂) (p : Measure α) {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) :
    IsClosed (thm7RegionOfAuxReceiver W p TJ) := by
  rw [thm7RegionOfAuxReceiver]
  exact (finite_setOf_lt_thm7Cap α).isClosed_biUnion fun kv _ ↦
    isClosed_iUnion_thm7RegionOfLaw W p TJ kv

lemma isClosed_thm7RegionOfInput (W : BCChannel α β₁ β₂) (p : Measure α) :
    IsClosed (thm7RegionOfInput W p) := by
  rw [thm7RegionOfInput]
  exact isClosed_iInter fun _ ↦ isClosed_iInter fun TJ ↦ isClosed_iInter fun _ ↦
    isClosed_thm7RegionOfAuxReceiver W p TJ

/-- The region of the auxiliary-receiver outer bound is closed, without passing to the closure.

What one fixed input law contributes is closed, so what is left is the union over the input laws.
That union is over a space of probability measures on a finite alphabet, and a union of closed
sets over an index that is merely compact is not closed unless the family also varies
continuously with the index.

The channel is an arbitrary kernel here, and for the zero kernel the region is empty, so what the
statement asks for beyond the closedness of the empty set is confined to the channels for which
the region is inhabited.

@residual(plan:bc-computable-region-formalization) -/
theorem isClosed_thm7Region (W : BCChannel α β₁ β₂) : IsClosed (thm7Region W) := by
  sorry

end Closedness

section WeakContinuity

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [DiscreteTopology Ω]
  [CompactSpace Ω] [OpensMeasurableSpace Ω]

lemma continuous_measureReal_of_discrete (S : Set Ω) :
    Continuous fun ν : ProbabilityMeasure Ω ↦ (ν : Measure Ω).real S := by
  have hcont : Continuous fun ν : ProbabilityMeasure Ω ↦
      ∫ ω, (BoundedContinuousFunction.mkOfCompact
        (⟨S.indicator fun _ ↦ (1 : ℝ), continuous_of_discreteTopology⟩ : C(Ω, ℝ))) ω
          ∂(ν : Measure Ω) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction _
  refine hcont.congr fun ν ↦ ?_
  change ∫ ω, S.indicator (fun _ ↦ (1 : ℝ)) ω ∂(ν : Measure Ω) = _
  exact MeasureTheory.integral_indicator_one (isOpen_discrete S).measurableSet

lemma continuous_entropy_of_discrete {T : Type*} [Fintype T] [MeasurableSpace T]
    [MeasurableSingletonClass T] (f : Ω → T) (hf : Measurable f) :
    Continuous fun ν : ProbabilityMeasure Ω ↦ entropy (ν : Measure Ω) f := by
  have hpt : ∀ (ν : ProbabilityMeasure Ω) (x : T),
      ((ν : Measure Ω).map f).real {x} = (ν : Measure Ω).real (f ⁻¹' {x}) := fun ν x ↦ by
    rw [measureReal_def, measureReal_def, Measure.map_apply hf (measurableSet_singleton x)]
  refine continuous_finsetSum Finset.univ fun x _ ↦ ?_
  exact (Real.continuous_negMulLog.comp (continuous_measureReal_of_discrete (f ⁻¹' {x}))).congr
    fun ν ↦ by rw [hpt ν x]; rfl

end WeakContinuity

section Nonemptiness

section Vanishing

variable {Ω : Type*} [MeasurableSpace Ω] {X : Type*} [MeasurableSpace X]
  {Y : Type*} [MeasurableSpace Y] {Z : Type*} [MeasurableSpace Z]

lemma ae_eq_const_of_map_eq_dirac [MeasurableSingletonClass X] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → X) (hf : Measurable f) (c : X)
    (h : μ.map f = Measure.dirac c) : f =ᵐ[μ] fun _ ↦ c := by
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨f ⁻¹' {c}, ?_, fun ω hω ↦ hω⟩
  rw [mem_ae_iff, ← Set.preimage_compl, ← Measure.map_apply hf (measurableSet_singleton c).compl,
    h, Measure.dirac_apply' _ (measurableSet_singleton c).compl]
  simp

lemma condMutualInfo_eq_zero_of_ae_const (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc)
    (c : X) (hc : Xs =ᵐ[μ] fun _ ↦ c) : condMutualInfo μ Xs Yo Zc = 0 := by
  have h_chain := mutualInfo_chain_rule μ Yo Xs Zc hYo hXs hZc
  have h0 : mutualInfo μ (fun ω ↦ (Zc ω, Yo ω)) Xs = 0 := by
    rw [mutualInfo_comm μ _ Xs (hZc.prodMk hYo) hXs]
    exact mutualInfo_eq_zero_of_ae_const μ Xs _ (hZc.prodMk hYo) c hc
  have h1 : mutualInfo μ Zc Xs = 0 := by
    rw [mutualInfo_comm μ Zc Xs hZc hXs]
    exact mutualInfo_eq_zero_of_ae_const μ Xs Zc hZc c hc
  rw [h0, h1, zero_add] at h_chain
  rw [condMutualInfo_comm μ Xs Yo Zc hXs hYo hZc]
  exact h_chain.symm

end Vanishing

lemma iCondIndepFun_of_subsingleton_codomain {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {β : ι → Type*} [m : ∀ i, MeasurableSpace (β i)]
    [∀ i, Subsingleton (β i)] [∀ i, Nonempty (β i)] (f : ∀ i, Ω → β i)
    (hf : ∀ i, Measurable (f i)) (μ : Measure Ω) [IsProbabilityMeasure μ]
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

instance instSubsingletonBcAuxAlphabetZero : Subsingleton (bcAuxAlphabet.{u} 0) :=
  ⟨fun a b ↦ ULift.down_injective (Subsingleton.elim (α := Fin 1) a.down b.down)⟩

/-- The joint law a point mass on the input induces: the channel and the auxiliary receiver
kernel applied to that point mass, with one-point auxiliary alphabets. -/
noncomputable def thm7DegenerateLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    Measure (Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂) :=
  ((Measure.dirac x₀ ⊗ₘ W) ⊗ₘ TJ).map
    (fun q ↦ ((fun _ ↦ default), q.1.1, q.1.2.1, q.1.2.2, q.2))

instance (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    IsProbabilityMeasure (thm7DegenerateLaw W TJ x₀) := by
  unfold thm7DegenerateLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

omit [Fintype α] [StandardBorelSpace α] [Nonempty α] [Fintype β₁] [StandardBorelSpace β₁]
  [Nonempty β₁] [Fintype β₂] [StandardBorelSpace β₂] [Nonempty β₂] in
lemma thm7DegenerateLaw_map_input (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    (thm7DegenerateLaw W TJ x₀).map (fun q ↦ q.2.1) = Measure.dirac x₀ := by
  rw [thm7DegenerateLaw, Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : ((fun q : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ ↦ q.2.1) ∘
      fun q : (α × β₁ × β₂) × bcAuxAlphabet.{u} kJ ↦
        (((fun _ ↦ default) : (i : Thm7AuxIdx) → bcAuxAlphabet.{u} 0), q.1.1, q.1.2.1,
          q.1.2.2, q.2)) = fun q ↦ q.1.1 := rfl
  have hsplit : (fun q : (α × β₁ × β₂) × bcAuxAlphabet.{u} kJ ↦ q.1.1)
      = (fun r : α × β₁ × β₂ ↦ r.1) ∘ (fun q : (α × β₁ × β₂) × bcAuxAlphabet.{u} kJ ↦ q.1) := rfl
  rw [hcomp, hsplit, ← Measure.map_map (by fun_prop) (by fun_prop),
    show ((Measure.dirac x₀ ⊗ₘ W) ⊗ₘ TJ).map (fun q ↦ q.1) = Measure.dirac x₀ ⊗ₘ W from
      Measure.fst_compProd _ _]
  exact Measure.fst_compProd _ _

omit [Fintype α] [StandardBorelSpace α] [Nonempty α] [Fintype β₁] [StandardBorelSpace β₁]
  [Nonempty β₁] [Fintype β₂] [StandardBorelSpace β₂] [Nonempty β₂] in
lemma thm7DegenerateLaw_map_outputs (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    (thm7DegenerateLaw W TJ x₀).map (fun q ↦ (q.2.1, q.2.2.1, q.2.2.2.1))
      = Measure.dirac x₀ ⊗ₘ W := by
  rw [thm7DegenerateLaw, Measure.map_map (by fun_prop) (by fun_prop),
    show ((fun q : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ ↦ (q.2.1, q.2.2.1, q.2.2.2.1)) ∘
      fun q : (α × β₁ × β₂) × bcAuxAlphabet.{u} kJ ↦
        (((fun _ ↦ default) : (i : Thm7AuxIdx) → bcAuxAlphabet.{u} 0), q.1.1, q.1.2.1,
          q.1.2.2, q.2)) = fun q ↦ q.1 from rfl]
  exact Measure.fst_compProd _ _

omit [Fintype α] [StandardBorelSpace α] [Nonempty α] [Fintype β₁] [StandardBorelSpace β₁]
  [Nonempty β₁] [Fintype β₂] [StandardBorelSpace β₂] [Nonempty β₂] in
lemma thm7DegenerateLaw_map_full (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    (thm7DegenerateLaw W TJ x₀).map (fun q ↦ ((q.2.1, q.2.2.1, q.2.2.2.1), q.2.2.2.2))
      = (Measure.dirac x₀ ⊗ₘ W) ⊗ₘ TJ := by
  rw [thm7DegenerateLaw, Measure.map_map (by fun_prop) (by fun_prop),
    show ((fun q : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ ↦
        ((q.2.1, q.2.2.1, q.2.2.2.1), q.2.2.2.2)) ∘
      fun q : (α × β₁ × β₂) × bcAuxAlphabet.{u} kJ ↦
        (((fun _ ↦ default) : (i : Thm7AuxIdx) → bcAuxAlphabet.{u} 0), q.1.1, q.1.2.1,
          q.1.2.2, q.2)) = id from rfl, Measure.map_id]

omit [Fintype α] [Nonempty α] [Fintype β₁] [Nonempty β₁] [Fintype β₂] [Nonempty β₂] in
lemma thm7DegenerateLaw_isThm7Law (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    IsThm7Law W TJ (Measure.dirac x₀) (thm7DegenerateLaw W TJ x₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact iCondIndepFun_of_subsingleton_codomain _ (fun _ ↦ by fun_prop) _ _
  · rw [thm7DegenerateLaw_map_outputs, thm7DegenerateLaw_map_input]
  · rw [thm7DegenerateLaw_map_full, thm7DegenerateLaw_map_outputs]
  · exact thm7DegenerateLaw_map_input W TJ x₀

omit [Fintype α] [Fintype β₁] [Fintype β₂] in
lemma thm7Slots_thm7DegenerateLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W] {kJ : ℕ}
    (TJ : Kernel (α × β₁ × β₂) (bcAuxAlphabet.{u} kJ)) [IsMarkovKernel TJ] (x₀ : α) :
    thm7Slots (thm7DegenerateLaw W TJ x₀) = 0 := by
  haveI : MeasurableSingletonClass α := measurableSingleton_of_standardBorel
  have haux : ∀ i : Thm7AuxIdx, (fun q : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ ↦ q.1 i)
      =ᵐ[thm7DegenerateLaw W TJ x₀] fun _ ↦ (default : bcAuxAlphabet.{u} 0) :=
    fun _ ↦ Filter.Eventually.of_forall fun _ ↦ Subsingleton.elim _ _
  have hX : (fun q : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ ↦ q.2.1)
      =ᵐ[thm7DegenerateLaw W TJ x₀] fun _ ↦ x₀ :=
    ae_eq_const_of_map_eq_dirac _ _ (by fun_prop) x₀ (thm7DegenerateLaw_map_input W TJ x₀)
  have hauxMI : ∀ {T : Type u} [MeasurableSpace T] (i : Thm7AuxIdx)
      (g : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → T), Measurable g →
      mutualInfoReal (thm7DegenerateLaw W TJ x₀) (fun q ↦ q.1 i) g = 0 := by
    intro T _ i g hg
    rw [mutualInfoReal,
      mutualInfo_eq_zero_of_ae_const _ _ g hg default (haux i), ENNReal.toReal_zero]
  have hXMI : ∀ {T : Type u} [MeasurableSpace T]
      (g : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → T), Measurable g →
      mutualInfoReal (thm7DegenerateLaw W TJ x₀) (fun q ↦ q.2.1) g = 0 := by
    intro T _ g hg
    rw [mutualInfoReal,
      mutualInfo_eq_zero_of_ae_const _ _ g hg x₀ hX, ENNReal.toReal_zero]
  have hauxCMI : ∀ {T R : Type u} [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T]
      [MeasurableSpace R] (i : Thm7AuxIdx) (g : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → T)
      (h : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → R), Measurable g → Measurable h →
      condMutualInfoReal (thm7DegenerateLaw W TJ x₀) (fun q ↦ q.1 i) g h = 0 := by
    intro T R _ _ _ _ i g h hg hh
    rw [condMutualInfoReal,
      condMutualInfo_eq_zero_of_ae_const _ _ g h (by fun_prop) hg hh default (haux i),
      ENNReal.toReal_zero]
  have hXCMI : ∀ {T R : Type u} [MeasurableSpace T] [StandardBorelSpace T] [Nonempty T]
      [MeasurableSpace R] (g : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → T)
      (h : Thm7Ambient (fun _ ↦ 0) kJ α β₁ β₂ → R), Measurable g → Measurable h →
      condMutualInfoReal (thm7DegenerateLaw W TJ x₀) (fun q ↦ q.2.1) g h = 0 := by
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

omit [Fintype β₁] [Fintype β₂] in
lemma origin_mem_thm7Region (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (x₀ : α) :
    ((0, 0, 0) : ℝ × ℝ × ℝ) ∈ thm7Region W := by
  simp only [thm7Region, Set.mem_iUnion]
  refine ⟨⟨Measure.dirac x₀, inferInstance⟩, ?_⟩
  simp only [thm7RegionOfInput, Set.mem_iInter]
  intro kJ TJ hTJ
  haveI := hTJ
  simp only [thm7RegionOfAuxReceiver, Set.mem_iUnion]
  refine ⟨fun _ ↦ 0, fun i ↦ ?_, ⟨thm7DegenerateLaw W TJ x₀, inferInstance⟩, ?_, ?_⟩
  · simp only [thm7Cap]; split <;> omega
  · simpa only [ProbabilityMeasure.coe_mk] using thm7DegenerateLaw_isThm7Law W TJ x₀
  · simp only [ProbabilityMeasure.coe_mk, thm7RegionOfLaw, Set.mem_setOf_eq,
      thm7Slots_thm7DegenerateLaw W TJ x₀]
    norm_num [InThm7, IsThm7Eligible]

omit [Fintype β₁] [Fintype β₂] in
/-- The region of the auxiliary-receiver outer bound is inhabited: it contains the origin.

The hypothesis that the channel is a Markov kernel is not removable. For the zero kernel the
clause pinning the law of the outputs has no solution among the probability measures, so no joint
law takes part and the region is empty.

@audit:ok -/
@[entry_point]
theorem thm7Region_nonempty (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    (thm7Region W).Nonempty :=
  ⟨(0, 0, 0), origin_mem_thm7Region W (Classical.arbitrary α)⟩

end Nonemptiness

end InformationTheory.Shannon.BroadcastChannel
