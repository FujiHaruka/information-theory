import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.MIChainRule
import InformationTheory.Shannon.AEP.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Channel coding theorem — primitive definitions

## Main definitions

* `Channel α β := Kernel α β` (DMC, one-symbol).
* `Code M n α β`: encoder–decoder bundle for a block code of length `n` with `M` codewords.
* `Code.errorProbAt`: point-wise error probability for message `m`.
* `Code.averageErrorProb`: average error probability under a uniform message distribution.
* `mutualInfoOfChannel`: mutual information `I(X; Y)` under input distribution `p` and channel `W`.
* Jointly typical set definitions and associated probability bounds.

## Implementation notes

* `Channel = Kernel α β` (`ProbabilityTheory.Kernel`) allows direct use of Mathlib's
  `klDiv_compProd_*` API.
* Joint distribution is `p ⊗ₘ W` (`MeasureTheory.Measure.compProd`), so `(X, Y) ∼ p ⊗ₘ W`.
* The block channel `W^n` is not constructed explicitly; the i.i.d. product is expressed as
  `Measure.pi (fun _ => jointDistribution p W)` reshaped to `(Fin n → α) × (Fin n → β)`.
-/

namespace InformationTheory.Shannon.ChannelCoding

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## Channel (DMC) -/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- A **discrete memoryless channel** (DMC) is just a (Markov) kernel `α → Measure β`.
Markov-ness is requested as a separate type-class hypothesis on the user side, so the
definition itself stays the bare `Kernel`. -/
abbrev Channel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :=
  Kernel α β

/-- Channel joint distribution under input law `p`: `p ⊗ₘ W` is the joint distribution
of `(X, Y)` when `X ∼ p` and `Y | X ∼ W X`. Lives in `Measure (α × β)`. -/
noncomputable def jointDistribution (p : Measure α) (W : Channel α β) : Measure (α × β) :=
  p ⊗ₘ W

@[simp] lemma jointDistribution_def (p : Measure α) (W : Channel α β) :
    jointDistribution p W = p ⊗ₘ W := rfl

/-- For a Markov kernel `W` and probability input `p`, the joint `p ⊗ₘ W` is a
probability measure. -/
instance jointDistribution.instIsProbabilityMeasure
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    IsProbabilityMeasure (jointDistribution p W) := by
  unfold jointDistribution
  infer_instance

/-- The output distribution of the channel under input `p`: `q := p ⊗ₘ W` projected to
`β`, i.e. the second marginal. Used for the channel-output marginal `q(y) = ∑ₓ p(x) W(y|x)`. -/
noncomputable def outputDistribution (p : Measure α) (W : Channel α β) : Measure β :=
  (jointDistribution p W).snd

instance outputDistribution.instIsProbabilityMeasure
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    IsProbabilityMeasure (outputDistribution p W) := by
  unfold outputDistribution
  infer_instance

/-- The mutual information of `(X, Y) ∼ p ⊗ₘ W`. Defined as
`klDiv (p ⊗ₘ W) (p ⊗ q)` where `q := outputDistribution p W`. Equivalent to the
standard `mutualInfo` of any random variable pair drawn from `p ⊗ₘ W`. -/
noncomputable def mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞ :=
  klDiv (jointDistribution p W) (p.prod (outputDistribution p W))

@[simp] lemma mutualInfoOfChannel_def (p : Measure α) (W : Channel α β) :
    mutualInfoOfChannel p W
      = klDiv (jointDistribution p W) (p.prod (outputDistribution p W)) := rfl

/-- **`mutualInfoOfChannel` equals MI of the joint coordinates.** Unfolds the
`klDiv`-defined `mutualInfoOfChannel p W` into the canonical
`mutualInfo (jointDistribution p W) Prod.fst Prod.snd`. Used as the bridge from
the channel-side formulation to the joint-distribution-side three-term identity. -/
theorem mutualInfoOfChannel_eq_mutualInfo_prod
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    mutualInfoOfChannel p W
      = InformationTheory.Shannon.mutualInfo (jointDistribution p W)
          Prod.fst Prod.snd := by
  unfold mutualInfoOfChannel InformationTheory.Shannon.mutualInfo
  -- Three rewrites: joint.map id = joint, joint.fst = p, joint.snd = outputDistribution.
  have h_id : (jointDistribution p W).map (fun z : α × β => (z.1, z.2))
      = jointDistribution p W := by
    have : (fun z : α × β => (z.1, z.2)) = id := by funext z; rfl
    rw [this, Measure.map_id]
  have h_fst : (jointDistribution p W).map Prod.fst = p := by
    show ((p ⊗ₘ W).map Prod.fst) = p
    rw [show ((p ⊗ₘ W).map Prod.fst) = (p ⊗ₘ W).fst from rfl]
    exact Measure.fst_compProd p W
  have h_snd : (jointDistribution p W).map Prod.snd = outputDistribution p W := rfl
  rw [h_id, h_fst, h_snd]

/-- **Entropy ↔ mutual-information bridge for the channel.**
The channel mutual information equals the three-term form
`H(X) + H(Y) − H(X, Y)` on the joint distribution `p ⊗ₘ W`, where `H` is the
discrete Shannon entropy and `H(X, Y) := entropy (p ⊗ₘ W) id` is the joint entropy
on `α × β`.

Composing this with `entropy_eq_of_identDistrib` lets the achievability consumer
rewrite the joint-AEP exponent
`H(jointSeq Xs Ys 0) − H(Xs 0) − H(Ys 0) = −(mutualInfoOfChannel p W).toReal`
once the i.i.d. ambient `μ := Measure.infinitePi (jointDistribution p W)` is plumbed
in (so that `μ.map (Xs 0) = p`, etc.). -/
theorem mutualInfoOfChannel_eq_HX_add_HY_sub_HZ
    [Fintype α] [Nonempty α] [MeasurableSingletonClass α]
    [Fintype β] [Nonempty β] [MeasurableSingletonClass β]
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    (mutualInfoOfChannel p W).toReal
      = InformationTheory.Shannon.entropy (jointDistribution p W) Prod.fst
        + InformationTheory.Shannon.entropy (jointDistribution p W) Prod.snd
        - InformationTheory.Shannon.entropy (jointDistribution p W) id := by
  classical
  rw [mutualInfoOfChannel_eq_mutualInfo_prod p W]
  exact InformationTheory.Shannon.mutualInfo_eq_entropy_add_entropy_sub_jointEntropy
    (jointDistribution p W)

/-! ## Block code -/

/-- A **block code** of length `n` with `M` messages over input alphabet `α` and
output alphabet `β`: a deterministic encoder `Fin M → (Fin n → α)` and decoder
`(Fin n → β) → Fin M`.

We bundle no measurability fields: on finite (or `MeasurableSingletonClass`) alphabets
all functions are automatically measurable, so requiring fields would only force the
caller to discharge `measurable_of_finite` redundantly. -/
structure Code (M n : ℕ) (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  encoder : Fin M → (Fin n → α)
  decoder : (Fin n → β) → Fin M

namespace Code

variable {M n : ℕ}

/-- The decoding region for message `m`: `{y : Fin n → β | decoder y = m}`. -/
def decodingRegion (c : Code M n α β) (m : Fin M) : Set (Fin n → β) :=
  { y | c.decoder y = m }

@[simp] lemma mem_decodingRegion (c : Code M n α β) (m : Fin M) (y : Fin n → β) :
    y ∈ c.decodingRegion m ↔ c.decoder y = m := Iff.rfl

/-- Decoding regions are measurable on a `MeasurableSingletonClass` output alphabet
(every set is then measurable). -/
lemma measurableSet_decodingRegion
    [Fintype β] [MeasurableSingletonClass β]
    (c : Code M n α β) (m : Fin M) :
    MeasurableSet (c.decodingRegion m) :=
  (Set.toFinite _).measurableSet

/-- The complement of the decoding region for `m` ("error event" for `m` given the
output `y`): `{y | decoder y ≠ m}`. -/
def errorEvent (c : Code M n α β) (m : Fin M) : Set (Fin n → β) :=
  (c.decodingRegion m)ᶜ

@[simp] lemma mem_errorEvent (c : Code M n α β) (m : Fin M) (y : Fin n → β) :
    y ∈ c.errorEvent m ↔ c.decoder y ≠ m := by
  simp [errorEvent, decodingRegion]

end Code

/-! ## Block-code error probability -/

variable [Fintype α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSingletonClass β]

namespace Code

variable {M n : ℕ}

/-- Pointwise error probability when message `m` is sent through the channel `W`
applied symbol-wise to `encoder m`. We model the channel output distribution given
`x : Fin n → α` as `Measure.pi (i ↦ W (x i))` — the canonical "memoryless extension"
of `W` to length `n` blocks. -/
noncomputable def errorProbAt
    (c : Code M n α β) (W : Channel α β) (m : Fin M) : ℝ≥0∞ :=
  (Measure.pi (fun i => W (c.encoder m i))) (c.errorEvent m)

/-- Average error probability under a uniform message: `(1/M) ∑ m, errorProbAt c W m`.
For `M = 0` we set this to `0` (the sum is empty). -/
noncomputable def averageErrorProb
    (c : Code M n α β) (W : Channel α β) : ℝ≥0∞ :=
  if M = 0 then 0
  else (M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, c.errorProbAt W m

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] in
/-- The average error probability is bounded above by `1` (each `errorProbAt ≤ 1` for a
Markov kernel; summing over `M` terms and dividing by `M` keeps the bound). -/
@[entry_point]
theorem averageErrorProb_le_one
    [Nonempty β]
    (c : Code M n α β) (W : Channel α β) [IsMarkovKernel W] :
    c.averageErrorProb W ≤ 1 := by
  unfold averageErrorProb
  by_cases hM : M = 0
  · simp [hM]
  · simp only [hM, if_false]
    -- Each summand ≤ 1
    have h_each : ∀ m : Fin M, c.errorProbAt W m ≤ 1 := by
      intro m
      have : IsProbabilityMeasure
          (Measure.pi (fun i => W (c.encoder m i))) := by infer_instance
      exact prob_le_one
    -- Sum ≤ M
    have h_sum_le : (∑ m : Fin M, c.errorProbAt W m) ≤ (M : ℝ≥0∞) := by
      calc (∑ m : Fin M, c.errorProbAt W m)
          ≤ ∑ _m : Fin M, (1 : ℝ≥0∞) := Finset.sum_le_sum fun m _ => h_each m
        _ = (M : ℝ≥0∞) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                                  nsmul_eq_mul, mul_one]
    -- Multiply both sides by (M : ℝ≥0∞)⁻¹
    have hM_pos : (0 : ℝ≥0∞) < M := by
      rw [show (0 : ℝ≥0∞) = ((0 : ℕ) : ℝ≥0∞) from by simp,
        Nat.cast_lt (α := ℝ≥0∞)]
      exact Nat.pos_of_ne_zero hM
    have hM_ne_top : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
    calc ((M : ℝ≥0∞)⁻¹ * ∑ m : Fin M, c.errorProbAt W m)
        ≤ (M : ℝ≥0∞)⁻¹ * (M : ℝ≥0∞) := mul_le_mul_of_nonneg_left h_sum_le bot_le
      _ = 1 := ENNReal.inv_mul_cancel hM_pos.ne' hM_ne_top

end Code

/-! ## Jointly typical set (definitions + bounds (a), (b), (c))

Cover-Thomas Theorem 7.6.1. The jointly typical set is the intersection of three
single-axis typical conditions (X, Y, and (X, Y) jointly). Bounds (a) and (b) follow
directly from the AEP single-axis theorems (`typicalSet_prob_tendsto_one` and
`typicalSet_card_le`) applied to the joint sequence `i ↦ (Xs i, Ys i)`. The
"independent-pair" bound (c) is the genuinely new ingredient.

The "marginal sequence" formulation `Xs : ℕ → Ω → α`, `Ys : ℕ → Ω → β` matches the
AEP plumbing in `AEP.lean`. The joint sequence is `Zs i ω := (Xs i ω, Ys i ω)`. -/

section JointlyTypical

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Joint sequence over the product alphabet `α × β`. -/
noncomputable def jointSequence
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) : ℕ → Ω → α × β :=
  fun i ω => (Xs i ω, Ys i ω)

omit [MeasurableSpace α] [MeasurableSpace β] [Fintype α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSingletonClass β] [MeasurableSpace Ω] in
@[simp] lemma jointSequence_apply
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (i : ℕ) (ω : Ω) :
    jointSequence Xs Ys i ω = (Xs i ω, Ys i ω) := rfl

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] in
lemma measurable_jointSequence
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i)) (i : ℕ) :
    Measurable (jointSequence Xs Ys i) :=
  (hXs i).prodMk (hYs i)

/-- The **jointly typical set** `A_ε^n ⊆ (Fin n → α) × (Fin n → β)`: pairs `(x, y)`
whose empirical entropies of `X`, `Y`, and `(X, Y)` are all within `ε` of the true
entropies.

Implementation: the X-typical condition uses the marginal sequence `Xs` (via
`InformationTheory.Shannon.typicalSet μ Xs n ε`), the Y-typical condition uses `Ys`,
and the joint-typical condition uses the joint sequence `Zs := jointSequence Xs Ys`
over the product alphabet `α × β`. We package this as the preimage of the three
single-axis typical sets under the natural reshape `(Fin n → α × β) ≃ (Fin n → α) × (Fin n → β)`. -/
noncomputable def jointlyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n : ℕ) (ε : ℝ) :
    Set ((Fin n → α) × (Fin n → β)) :=
  { p |
    (p.1 ∈ InformationTheory.Shannon.typicalSet μ Xs n ε)
    ∧ (p.2 ∈ InformationTheory.Shannon.typicalSet μ Ys n ε)
    ∧ (fun i => (p.1 i, p.2 i)) ∈
        InformationTheory.Shannon.typicalSet μ (jointSequence Xs Ys) n ε }

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
@[entry_point]
lemma mem_jointlyTypicalSet_iff
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (n : ℕ) (ε : ℝ) (x : Fin n → α) (y : Fin n → β) :
    (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε ↔
      x ∈ InformationTheory.Shannon.typicalSet μ Xs n ε
      ∧ y ∈ InformationTheory.Shannon.typicalSet μ Ys n ε
      ∧ (fun i => (x i, y i)) ∈
          InformationTheory.Shannon.typicalSet μ (jointSequence Xs Ys) n ε := Iff.rfl

/-- The jointly typical set is measurable (finite product alphabet). -/
theorem measurableSet_jointlyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n : ℕ) (ε : ℝ) :
    MeasurableSet (jointlyTypicalSet μ Xs Ys n ε) :=
  (Set.toFinite _).measurableSet

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- The jointly typical set is finite (it lives in a finite ambient space). -/
lemma jointlyTypicalSet_finite
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n : ℕ) (ε : ℝ) :
    (jointlyTypicalSet μ Xs Ys n ε).Finite := Set.toFinite _

/-- **Bound (b): size of the jointly typical set**. The size is bounded by the size of
the joint single-axis typical set, which (by `typicalSet_card_le` applied to the joint
sequence over `α × β`) is at most `exp(n · (H(X, Y) + ε))`.

We bound `|A_ε^n|` by the cardinality of the joint typical set, which is a strictly
weaker (larger) bound than `2^{n(H(X,Y)+ε)}` but suffices for the channel coding
argument. The textbook bound `|A_ε^n| ≤ 2^{n(H(X,Y)+ε)}` (in `Real.exp` base) follows
by intersecting with the joint condition. -/
@[entry_point]
theorem jointlyTypicalSet_card_le
    [Nonempty α] [Nonempty β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hpos : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((jointlyTypicalSet μ Xs Ys n ε).toFinite.toFinset.card : ℝ) ≤
      Real.exp ((n : ℝ) *
        (InformationTheory.Shannon.entropy μ (jointSequence Xs Ys 0) + ε)) := by
  -- Strategy: embed jointlyTypicalSet into the single-axis joint typical set via
  -- the reshape (x, y) ↦ (fun i => (x i, y i)) : (Fin n → α) × (Fin n → β) → Fin n → α × β.
  -- Then apply typicalSet_card_le to the joint sequence.
  set Zs : ℕ → Ω → α × β := jointSequence Xs Ys with hZs_def
  have hZs : ∀ i, Measurable (Zs i) := fun i =>
    measurable_jointSequence Xs Ys hXs hYs i
  -- The reshape map.
  classical
  let φ : (Fin n → α) × (Fin n → β) → (Fin n → α × β) :=
    fun p i => (p.1 i, p.2 i)
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    apply Prod.ext
    · funext i
      have := congr_fun hpq i
      exact (Prod.mk.injEq _ _ _ _).mp this |>.1
    · funext i
      have := congr_fun hpq i
      exact (Prod.mk.injEq _ _ _ _).mp this |>.2
  -- Work directly at the finset level: build a Finset.image of jointlyTypicalSet
  -- under φ that injects into the joint single-axis typical set's finset.
  -- Step 1: jointlyTypicalSet's finset is in bijection (via φ) with its image
  -- under φ at the Finset level.
  let JT := (jointlyTypicalSet μ Xs Ys n ε).toFinite.toFinset
  let ZT := (InformationTheory.Shannon.typicalSet μ Zs n ε).toFinite.toFinset
  -- The image JT.image φ is a subset of ZT.
  have h_image_sub : JT.image φ ⊆ ZT := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨⟨x, y⟩, hxy_mem, rfl⟩ := hz
    have hxy : (x, y) ∈ jointlyTypicalSet μ Xs Ys n ε :=
      (Set.Finite.mem_toFinset _).mp hxy_mem
    -- The joint condition is the third conjunct
    rw [Set.Finite.mem_toFinset]
    exact hxy.2.2
  have h_card_image : JT.card = (JT.image φ).card :=
    (Finset.card_image_of_injective _ hφ_inj).symm
  have h_card_le_finset : JT.card ≤ ZT.card := by
    rw [h_card_image]; exact Finset.card_le_card h_image_sub
  have h_card_le_R : (JT.card : ℝ) ≤ (ZT.card : ℝ) := by exact_mod_cast h_card_le_finset
  -- Apply typicalSet_card_le for the joint sequence Zs.
  have h_joint :=
    InformationTheory.Shannon.typicalSet_card_le μ Zs hZs hpos n hε
  exact h_card_le_R.trans h_joint

-- Helper: if three events each have measure tending to 1, so does their triple intersection.
-- (Complement-union bound: P(Aᶜ ∪ Bᶜ ∪ Cᶜ) ≤ P(Aᶜ) + P(Bᶜ) + P(Cᶜ) → 0.)
private theorem measure_inter3_tendsto_one {Ω' : Type*} [MeasurableSpace Ω']
    (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (A B C : ℕ → Set Ω')
    (hA : ∀ n, MeasurableSet (A n)) (hB : ∀ n, MeasurableSet (B n)) (hC : ∀ n, MeasurableSet (C n))
    (hA1 : Filter.Tendsto (fun n => μ' (A n)) Filter.atTop (𝓝 1))
    (hB1 : Filter.Tendsto (fun n => μ' (B n)) Filter.atTop (𝓝 1))
    (hC1 : Filter.Tendsto (fun n => μ' (C n)) Filter.atTop (𝓝 1)) :
    Filter.Tendsto (fun n => μ' (A n ∩ B n ∩ C n)) Filter.atTop (𝓝 1) := by
  -- Step 1: for any measurable E with μ'(E) → 1, we have μ'(Eᶜ) → 0.
  have h_bad_tendsto : ∀ (E : ℕ → Set Ω') (hE : ∀ n, MeasurableSet (E n))
      (h : Filter.Tendsto (fun n => μ' (E n)) Filter.atTop (𝓝 1)),
      Filter.Tendsto (fun n => μ' ((E n)ᶜ)) Filter.atTop (𝓝 0) := by
    intro E hE h
    have h_id : ∀ n, μ' ((E n)ᶜ) = 1 - μ' (E n) := fun n => by
      rw [measure_compl (hE n) (measure_ne_top μ' _), measure_univ]
    refine Filter.Tendsto.congr (fun n => (h_id n).symm) ?_
    have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
      ENNReal.continuous_sub_left (by simp)
    have h_step : Filter.Tendsto (fun n => (1 : ℝ≥0∞) - μ' (E n)) Filter.atTop
        (𝓝 ((1 : ℝ≥0∞) - 1)) := h_cont.tendsto _ |>.comp h
    simpa using h_step
  -- Step 2: derive complement → 0 for each axis.
  have h_badA_to_zero := h_bad_tendsto A hA hA1
  have h_badB_to_zero := h_bad_tendsto B hB hB1
  have h_badC_to_zero := h_bad_tendsto C hC hC1
  -- Step 3: complement of A ∩ B ∩ C ⊆ Aᶜ ∪ Bᶜ ∪ Cᶜ.
  have h_compl_sub : ∀ n, (A n ∩ B n ∩ C n)ᶜ ⊆ (A n)ᶜ ∪ (B n)ᶜ ∪ (C n)ᶜ := by
    intro n ω hω
    rw [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_inter_iff,
        not_and_or, not_and_or] at hω
    rcases hω with (h_or | hC_bad)
    · rcases h_or with hA_bad | hB_bad
      · exact Set.mem_union_left _ (Set.mem_union_left _ hA_bad)
      · exact Set.mem_union_left _ (Set.mem_union_right _ hB_bad)
    · exact Set.mem_union_right _ hC_bad
  -- Step 4: bound μ'((A∩B∩C)ᶜ) by the sum of the three complement measures.
  have h_bound_compl : ∀ n,
      μ' ((A n ∩ B n ∩ C n)ᶜ) ≤ μ' ((A n)ᶜ) + μ' ((B n)ᶜ) + μ' ((C n)ᶜ) := by
    intro n
    calc μ' ((A n ∩ B n ∩ C n)ᶜ)
        ≤ μ' ((A n)ᶜ ∪ (B n)ᶜ ∪ (C n)ᶜ) := measure_mono (h_compl_sub n)
      _ ≤ μ' ((A n)ᶜ ∪ (B n)ᶜ) + μ' ((C n)ᶜ) := measure_union_le _ _
      _ ≤ (μ' ((A n)ᶜ) + μ' ((B n)ᶜ)) + μ' ((C n)ᶜ) := by
          gcongr; exact measure_union_le _ _
      _ = μ' ((A n)ᶜ) + μ' ((B n)ᶜ) + μ' ((C n)ᶜ) := by ring
  -- Step 5: the sum of complements → 0 + 0 + 0 = 0.
  have h_sum_tendsto : Filter.Tendsto
      (fun n => μ' ((A n)ᶜ) + μ' ((B n)ᶜ) + μ' ((C n)ᶜ)) Filter.atTop (𝓝 0) := by
    have h12 := h_badA_to_zero.add h_badB_to_zero
    have h_all := h12.add h_badC_to_zero
    simpa using h_all
  -- Step 6: squeeze to conclude μ'((A∩B∩C)ᶜ) → 0.
  have h_compl_tendsto : Filter.Tendsto (fun n => μ' ((A n ∩ B n ∩ C n)ᶜ))
      Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_sum_tendsto (fun n => bot_le) h_bound_compl
  -- Step 7: μ'(A∩B∩C) = 1 − μ'((A∩B∩C)ᶜ) → 1 − 0 = 1.
  have h_meas_int : ∀ n, MeasurableSet (A n ∩ B n ∩ C n) :=
    fun n => ((hA n).inter (hB n)).inter (hC n)
  have h_id : ∀ n, μ' (A n ∩ B n ∩ C n) = 1 - μ' ((A n ∩ B n ∩ C n)ᶜ) := fun n => by
    rw [measure_compl (h_meas_int n) (measure_ne_top μ' _), measure_univ]
    exact (ENNReal.sub_sub_cancel (by simp) prob_le_one).symm
  refine Filter.Tendsto.congr (fun n => (h_id n).symm) ?_
  have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
    ENNReal.continuous_sub_left (by simp)
  have h_step : Filter.Tendsto (fun n => (1 : ℝ≥0∞) - μ' ((A n ∩ B n ∩ C n)ᶜ))
      Filter.atTop (𝓝 ((1 : ℝ≥0∞) - 0)) := h_cont.tendsto _ |>.comp h_compl_tendsto
  simpa using h_step

/-- **Bound (a): joint AEP probability**. The probability that the block-joint pair
`(X^n, Y^n)` lies in the jointly typical set tends to `1`.

Strategy: the event "(X^n, Y^n) jointly typical" is the intersection of three single-axis
typical events; its complement is contained in the union of three single-axis complements,
each of which has measure tending to `0` by the single-axis `typicalSet_prob_tendsto_one`. -/
@[entry_point]
theorem jointlyTypicalSet_prob_tendsto_one
    [Nonempty α] [Nonempty β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY : Pairwise fun i j => Ys i ⟂ᵢ[μ] Ys j)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hindepZ : Pairwise fun i j =>
      jointSequence Xs Ys i ⟂ᵢ[μ] jointSequence Xs Ys j)
    (hidentZ : ∀ i,
      IdentDistrib (jointSequence Xs Ys i) (jointSequence Xs Ys 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ =>
        μ {ω | (InformationTheory.Shannon.jointRV Xs n ω,
                InformationTheory.Shannon.jointRV Ys n ω) ∈
                jointlyTypicalSet μ Xs Ys n ε})
      Filter.atTop
      (𝓝 1) := by
  -- Convergence of each single-axis "good" event.
  have hX :=
    InformationTheory.Shannon.typicalSet_prob_tendsto_one μ Xs hXs hindepX hidentX hε
  have hY :=
    InformationTheory.Shannon.typicalSet_prob_tendsto_one μ Ys hYs hindepY hidentY hε
  set Zs : ℕ → Ω → α × β := jointSequence Xs Ys with hZs_def
  have hZs : ∀ i, Measurable (Zs i) := fun i =>
    measurable_jointSequence Xs Ys hXs hYs i
  have hZ :=
    InformationTheory.Shannon.typicalSet_prob_tendsto_one μ Zs hZs hindepZ hidentZ hε
  -- Naming events.
  set goodX : ℕ → Set Ω := fun n =>
    {ω | InformationTheory.Shannon.jointRV Xs n ω ∈
          InformationTheory.Shannon.typicalSet μ Xs n ε}
  set goodY : ℕ → Set Ω := fun n =>
    {ω | InformationTheory.Shannon.jointRV Ys n ω ∈
          InformationTheory.Shannon.typicalSet μ Ys n ε}
  set goodZ : ℕ → Set Ω := fun n =>
    {ω | InformationTheory.Shannon.jointRV Zs n ω ∈
          InformationTheory.Shannon.typicalSet μ Zs n ε}
  -- The joint event is the intersection of the three.
  set jointEvt : ℕ → Set Ω := fun n =>
    {ω | (InformationTheory.Shannon.jointRV Xs n ω,
          InformationTheory.Shannon.jointRV Ys n ω) ∈
          jointlyTypicalSet μ Xs Ys n ε}
  -- Key fact: jointEvt n = goodX n ∩ goodY n ∩ goodZ n.
  -- (The joint condition on (fun i => (X_i ω, Y_i ω)) is exactly jointRV Zs n ω.)
  have h_joint_decomp : ∀ n, jointEvt n = goodX n ∩ goodY n ∩ goodZ n := by
    intro n
    ext ω
    constructor
    · intro hω
      obtain ⟨hX', hY', hZ'⟩ := hω
      refine ⟨⟨hX', hY'⟩, ?_⟩
      -- hZ' : (fun i => (jointRV Xs n ω i, jointRV Ys n ω i)) ∈ typicalSet μ Zs n ε
      -- The function (fun i => (Xs i ω, Ys i ω)) = jointRV Zs n ω by defeq.
      exact hZ'
    · rintro ⟨⟨hX', hY'⟩, hZ'⟩
      refine ⟨hX', hY', ?_⟩
      exact hZ'
  -- Each good event is measurable (finite product alphabet).
  have h_meas_goodX : ∀ n, MeasurableSet (goodX n) := fun n =>
    (InformationTheory.Shannon.measurable_jointRV Xs hXs n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ Xs n ε)
  have h_meas_goodY : ∀ n, MeasurableSet (goodY n) := fun n =>
    (InformationTheory.Shannon.measurable_jointRV Ys hYs n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ Ys n ε)
  have h_meas_goodZ : ∀ n, MeasurableSet (goodZ n) := fun n =>
    (InformationTheory.Shannon.measurable_jointRV Zs hZs n)
      (InformationTheory.Shannon.measurableSet_typicalSet μ Zs n ε)
  -- Apply the abstract complement-union-bound helper to goodX/goodY/goodZ.
  -- Rewrite goal: μ (jointEvt n) = μ (goodX n ∩ goodY n ∩ goodZ n) via h_joint_decomp.
  have h_eq : ∀ n, μ (jointEvt n) = μ (goodX n ∩ goodY n ∩ goodZ n) :=
    fun n => congr_arg μ (h_joint_decomp n)
  rw [show (fun n => μ (jointEvt n)) = fun n => μ (goodX n ∩ goodY n ∩ goodZ n) from
    funext h_eq]
  exact measure_inter3_tendsto_one μ goodX goodY goodZ
    h_meas_goodX h_meas_goodY h_meas_goodZ hX hY hZ

/-- **Bound (c): independent-pair probability**. The probability under the **product**
measure `μX^n × μY^n` (where `μX^n := μ.map (jointRV Xs n)` and similarly for `Y`) that
`(X̃, Y)` lies in the jointly typical set is bounded by `exp(-n(I - 3ε))` (in the
log form: `exp(n · (H(X,Y) - H(X) - H(Y) + 3ε))`).

This is Cover-Thomas Theorem 7.6.1 (7.71). The key inputs are
`typicalSet_prob_le` (new AEP lemma, point-wise upper bound on the probability of
each typical block) applied to the `X` and `Y` axes, and `jointlyTypicalSet_card_le`
for the cardinality of the joint typical set.

Mutual independence (`iIndepFun`) along **each** of the `X` and `Y` axes is required
to factorise the block laws `μ.map (jointRV Xs n) = Measure.pi (μ.map (Xs ·))`. The
joint axis identification (`hidentZ`) is **not** required for this bound (it is
required only by the random-codebook average downstream of this lemma). -/
@[entry_point]
theorem jointlyTypicalSet_indep_prob_le
    [Nonempty α] [Nonempty β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hindepX_full : iIndepFun (fun i => Xs i) μ)
    (hidentX : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hindepY_full : iIndepFun (fun i => Ys i) μ)
    (hidentY : ∀ i, IdentDistrib (Ys i) (Ys 0) μ μ)
    (hposX : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
    (hposY : ∀ y : β, 0 < (μ.map (Ys 0)).real {y})
    (hposZ : ∀ p : α × β,
      0 < (μ.map (jointSequence Xs Ys 0)).real {p})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (((μ.map (InformationTheory.Shannon.jointRV Xs n)).prod
        (μ.map (InformationTheory.Shannon.jointRV Ys n))).real
        (jointlyTypicalSet μ Xs Ys n ε))
      ≤ Real.exp ((n : ℝ) *
          ((InformationTheory.Shannon.entropy μ (jointSequence Xs Ys 0)
            - InformationTheory.Shannon.entropy μ (Xs 0)
            - InformationTheory.Shannon.entropy μ (Ys 0))
           + 3 * ε)) := by
  classical
  -- Notation.
  set μX : Measure (Fin n → α) := μ.map (InformationTheory.Shannon.jointRV Xs n)
    with hμX_def
  set μY : Measure (Fin n → β) := μ.map (InformationTheory.Shannon.jointRV Ys n)
    with hμY_def
  set HX : ℝ := InformationTheory.Shannon.entropy μ (Xs 0) with hHX_def
  set HY : ℝ := InformationTheory.Shannon.entropy μ (Ys 0) with hHY_def
  set HZ : ℝ := InformationTheory.Shannon.entropy μ (jointSequence Xs Ys 0)
    with hHZ_def
  -- The jointly typical set as a Finset.
  set A : Set ((Fin n → α) × (Fin n → β)) := jointlyTypicalSet μ Xs Ys n ε with hA_def
  set Afin : Finset ((Fin n → α) × (Fin n → β)) :=
    (jointlyTypicalSet_finite μ Xs Ys n ε).toFinset with hAfin_def
  -- The X- and Y-block laws are probability measures (hence σ-finite).
  have hXmeas : Measurable (InformationTheory.Shannon.jointRV Xs n) :=
    InformationTheory.Shannon.measurable_jointRV Xs hXs n
  have hYmeas : Measurable (InformationTheory.Shannon.jointRV Ys n) :=
    InformationTheory.Shannon.measurable_jointRV Ys hYs n
  haveI : IsProbabilityMeasure μX :=
    Measure.isProbabilityMeasure_map hXmeas.aemeasurable
  haveI : IsProbabilityMeasure μY :=
    Measure.isProbabilityMeasure_map hYmeas.aemeasurable
  haveI : IsProbabilityMeasure (μX.prod μY) := by
    have : IsFiniteMeasure μX := inferInstance
    have : IsFiniteMeasure μY := inferInstance
    infer_instance
  -- Step 1: rewrite `(μX.prod μY).real A` as a Finset sum over `Afin`.
  have h_sum_decomp :
      (μX.prod μY).real A
        = ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2} := by
    -- `A.real = ∑ p ∈ Afin, μ.real {p}` by `sum_measureReal_singleton` applied to `μX.prod μY`.
    have h_real_eq : (μX.prod μY).real A = ∑ p ∈ Afin, (μX.prod μY).real {p} := by
      -- `A = ⋃ p ∈ Afin, {p}` (or use `measure_biUnion_finset`).
      have h_coe : (Afin : Set _) = A :=
        (jointlyTypicalSet_finite μ Xs Ys n ε).coe_toFinset
      rw [← h_coe, ← sum_measureReal_singleton (μ := μX.prod μY) Afin]
    rw [h_real_eq]
    refine Finset.sum_congr rfl ?_
    intro p _
    -- `{p} = {p.1} ×ˢ {p.2}`.
    have h_singleton_prod : ({p} : Set ((Fin n → α) × (Fin n → β)))
        = ({p.1} : Set (Fin n → α)) ×ˢ ({p.2} : Set (Fin n → β)) := by
      ext q
      simp [Prod.ext_iff]
    rw [h_singleton_prod]
    exact measureReal_prod_prod _ _
  -- Step 2: each summand bounded by `exp(-n(HX - ε)) · exp(-n(HY - ε))`.
  have h_each_le : ∀ p ∈ Afin,
      μX.real {p.1} * μY.real {p.2}
        ≤ Real.exp (- (n : ℝ) * (HX - ε)) * Real.exp (- (n : ℝ) * (HY - ε)) := by
    intro p hp
    have hp_set : p ∈ A := (Set.Finite.mem_toFinset _).mp hp
    rcases hp_set with ⟨hxX, hyY, _hxyZ⟩
    -- `μX.real {p.1} ≤ exp(-n(HX - ε))`.
    have hbdX : μX.real {p.1} ≤ Real.exp (- (n : ℝ) * (HX - ε)) :=
      InformationTheory.Shannon.typicalSet_prob_le μ Xs hXs hindepX_full hidentX
        hposX n p.1 hxX
    have hbdY : μY.real {p.2} ≤ Real.exp (- (n : ℝ) * (HY - ε)) :=
      InformationTheory.Shannon.typicalSet_prob_le μ Ys hYs hindepY_full hidentY
        hposY n p.2 hyY
    -- Both `≥ 0`, so multiplication preserves order.
    have hX_nn : 0 ≤ μX.real {p.1} := measureReal_nonneg
    have hY_nn : 0 ≤ μY.real {p.2} := measureReal_nonneg
    have hY_exp_nn : 0 ≤ Real.exp (- (n : ℝ) * (HY - ε)) := (Real.exp_pos _).le
    calc μX.real {p.1} * μY.real {p.2}
        ≤ Real.exp (- (n : ℝ) * (HX - ε)) * μY.real {p.2} := by
          exact mul_le_mul_of_nonneg_right hbdX hY_nn
      _ ≤ Real.exp (- (n : ℝ) * (HX - ε)) * Real.exp (- (n : ℝ) * (HY - ε)) := by
          exact mul_le_mul_of_nonneg_left hbdY (Real.exp_pos _).le
  -- Step 3: bound the sum by `card(Afin) · exp(...)` and then bound the cardinality.
  set C : ℝ := Real.exp (- (n : ℝ) * (HX - ε)) * Real.exp (- (n : ℝ) * (HY - ε))
    with hC_def
  have hC_nn : 0 ≤ C := by
    simp only [hC_def]
    exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have h_sum_le : ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2}
      ≤ (Afin.card : ℝ) * C := by
    calc ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2}
        ≤ ∑ _p ∈ Afin, C := Finset.sum_le_sum h_each_le
      _ = (Afin.card : ℝ) * C := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step 4: bound the cardinality by `jointlyTypicalSet_card_le`.
  have h_card_le : (Afin.card : ℝ) ≤ Real.exp ((n : ℝ) * (HZ + ε)) :=
    jointlyTypicalSet_card_le μ Xs Ys hXs hYs hposZ n hε
  -- Step 5: combine.
  have h_final_calc :
      (Afin.card : ℝ) * C
        ≤ Real.exp ((n : ℝ) * (HZ + ε)) * C :=
    mul_le_mul_of_nonneg_right h_card_le hC_nn
  have h_combine : (μX.prod μY).real A ≤ Real.exp ((n : ℝ) * (HZ + ε)) * C := by
    calc (μX.prod μY).real A
        = ∑ p ∈ Afin, μX.real {p.1} * μY.real {p.2} := h_sum_decomp
      _ ≤ (Afin.card : ℝ) * C := h_sum_le
      _ ≤ Real.exp ((n : ℝ) * (HZ + ε)) * C := h_final_calc
  -- Step 6: collapse the RHS into a single `exp` with the desired exponent.
  have h_rhs_eq :
      Real.exp ((n : ℝ) * (HZ + ε)) * C
        = Real.exp ((n : ℝ) * ((HZ - HX - HY) + 3 * ε)) := by
    -- exp(a) * exp(b) * exp(c) = exp(a + b + c).
    have h_expand : C
        = Real.exp (- (n : ℝ) * (HX - ε) + - (n : ℝ) * (HY - ε)) := by
      rw [hC_def, ← Real.exp_add]
    rw [h_expand, ← Real.exp_add]
    congr 1
    ring
  rw [h_rhs_eq] at h_combine
  exact h_combine

end JointlyTypical

end InformationTheory.Shannon.ChannelCoding

