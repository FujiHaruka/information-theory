import Common2026.Shannon.MutualInfo
import Common2026.Shannon.MIChainRule
import Common2026.Shannon.AEP
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Channel coding theorem — achievability (B-3 Phase A)

[B-3 ムーンショット plan](../../../docs/shannon/channel-coding-achievability-plan.md) の
Phase A: 通信路符号化定理 (achievability 半分) のためのプリミティブ定義。

## Phase A スコープ

* `Channel α β := Kernel α β` (DMC 1-symbol). `[IsMarkovKernel W]` で probability kernel 性。
* `Code (M n : ℕ) (α β : Type*)`: encoder + decoder の bundle (有限 alphabet 上、measurability は自動)
* `Code.errorProbAt`: メッセージ `m : Fin M` を送ったときの誤り確率 (point-wise)
* `Code.averageErrorProb`: 一様な入力メッセージに対する平均誤り確率
* `mutualInfoOfChannel`: 入力分布 + channel から `I(X; Y)` を計算

主定理 (`channel_coding_achievability`) は本ファイルの Phase D で扱う。Phase B (jointly
typical set + 3 joint AEP bounds) と Phase C (random codebook averaging) は本シードの
後続コミット (もしくは別 deferred plan) で順次追加。

## 設計判断

* **Channel = `Kernel α β`** (`ProbabilityTheory.Kernel`) を採用 (plan #1)。Mathlib の
  `klDiv_compProd_*` API がそのまま channel coding analysis に流れ込み、ad-hoc な
  `α → Measure β` 形は避ける。
* **Joint distribution = `p ⊗ₘ W`**: 入力分布 `p` と channel `W` から
  `MeasureTheory.Measure.compProd` で joint を構成。`(X, Y) ∼ p ⊗ₘ W`.
* **errorProb は `μ.real {…}` 形** (`MeasureFano.errorProb` と統一)。
* **Block channel `W^n` は明示構築せず**、joint product 形 `Measure.pi (i ↦ p ⊗ₘ W)` を
  reshape で `(Fin n → α) × (Fin n → β)` 上の分布として書く方針。`Kernel.pi` は Mathlib 不在。
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

/-- `mutualInfoOfChannel` is non-negative (vacuous since `klDiv : ℝ≥0∞`). -/
theorem mutualInfoOfChannel_nonneg (p : Measure α) (W : Channel α β) :
    0 ≤ mutualInfoOfChannel p W := bot_le

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

/-- **Entropy ↔ mutual-information bridge for the channel (B-3'' Phase D-(b) bridge).**
The channel mutual information equals the three-term form
`H(X) + H(Y) − H(X, Y)` on the joint distribution `p ⊗ₘ W`, where `H` is the
discrete Shannon entropy and `H(X, Y) := entropy (p ⊗ₘ W) id` is the joint entropy
on `α × β`.

Composing this with `entropy_eq_of_identDistrib` lets the Phase D-(b) consumer
rewrite the joint-AEP exponent
`H(jointSeq Xs Ys 0) − H(Xs 0) − H(Ys 0) = −(mutualInfoOfChannel p W).toReal`
once the i.i.d. ambient `μ := Measure.infinitePi (jointDistribution p W)` is plumbed
in (so that `μ.map (Xs 0) = p`, etc.). -/
theorem mutualInfoOfChannel_eq_HX_add_HY_sub_HZ
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
    [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSingletonClass β]
    (p : Measure α) [IsProbabilityMeasure p]
    (W : Channel α β) [IsMarkovKernel W] :
    (mutualInfoOfChannel p W).toReal
      = InformationTheory.Shannon.entropy (jointDistribution p W) Prod.fst
        + InformationTheory.Shannon.entropy (jointDistribution p W) Prod.snd
        - InformationTheory.Shannon.entropy (jointDistribution p W) id := by
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

lemma measurableSet_errorEvent
    [Fintype β] [MeasurableSingletonClass β]
    (c : Code M n α β) (m : Fin M) :
    MeasurableSet (c.errorEvent m) :=
  (c.measurableSet_decodingRegion m).compl

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

omit [Fintype α] [MeasurableSingletonClass α] [Fintype β] [MeasurableSingletonClass β] in
/-- The average error probability is finite (≤ 1 < ∞). -/
theorem averageErrorProb_ne_top
    [Nonempty β]
    (c : Code M n α β) (W : Channel α β) [IsMarkovKernel W] :
    c.averageErrorProb W ≠ ∞ :=
  (c.averageErrorProb_le_one W).trans_lt ENNReal.one_lt_top |>.ne

end Code

/-! ## Phase B — Jointly typical set (definitions + bounds (a), (b))

Cover-Thomas Theorem 7.6.1. The jointly typical set is the intersection of three
single-axis typical conditions (X, Y, and (X, Y) jointly). Bounds (a) and (b) follow
directly from the existing AEP single-axis theorems (`typicalSet_prob_tendsto_one` and
`typicalSet_card_le`) applied to the joint sequence `i ↦ (Xs i, Ys i)`. The
"independent-pair" bound (c) is the genuinely new ingredient and is deferred to a
subsequent commit.

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
theorem jointlyTypicalSet_card_le
    [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
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

/-- **Bound (a): joint AEP probability**. The probability that the block-joint pair
`(X^n, Y^n)` lies in the jointly typical set tends to `1`.

Strategy: the event "(X^n, Y^n) jointly typical" is the intersection of three single-axis
typical events; its complement is contained in the union of three single-axis complements,
each of which has measure tending to `0` by the single-axis `typicalSet_prob_tendsto_one`. -/
theorem jointlyTypicalSet_prob_tendsto_one
    [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
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
  -- Bound `μ (jointEvt n)` from below: P(A ∩ B ∩ C) ≥ P(A) + P(B) + P(C) - 2.
  -- We use the complement approach: P(complement of A∩B∩C) ≤ ∑ P(complement of each).
  -- That gives μ(jointEvt n)ᶜ → 0, hence μ(jointEvt n) → 1.
  set badX : ℕ → Set Ω := fun n => (goodX n)ᶜ
  set badY : ℕ → Set Ω := fun n => (goodY n)ᶜ
  set badZ : ℕ → Set Ω := fun n => (goodZ n)ᶜ
  -- Each event is measurable (finite product alphabet).
  have h_meas_goodX : ∀ n, MeasurableSet (goodX n) := by
    intro n
    have : MeasurableSet (InformationTheory.Shannon.typicalSet μ Xs n ε) :=
      InformationTheory.Shannon.measurableSet_typicalSet μ Xs n ε
    exact (InformationTheory.Shannon.measurable_jointRV Xs hXs n) this
  have h_meas_goodY : ∀ n, MeasurableSet (goodY n) := by
    intro n
    have : MeasurableSet (InformationTheory.Shannon.typicalSet μ Ys n ε) :=
      InformationTheory.Shannon.measurableSet_typicalSet μ Ys n ε
    exact (InformationTheory.Shannon.measurable_jointRV Ys hYs n) this
  have h_meas_goodZ : ∀ n, MeasurableSet (goodZ n) := by
    intro n
    have : MeasurableSet (InformationTheory.Shannon.typicalSet μ Zs n ε) :=
      InformationTheory.Shannon.measurableSet_typicalSet μ Zs n ε
    exact (InformationTheory.Shannon.measurable_jointRV Zs hZs n) this
  -- μ(goodX n) → 1 ⇒ μ(badX n) → 0; similarly Y, Z.
  have h_bad_tendsto : ∀ (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n))
      (h : Filter.Tendsto (fun n => μ (E n)) Filter.atTop (𝓝 1)),
      Filter.Tendsto (fun n => μ ((E n)ᶜ)) Filter.atTop (𝓝 0) := by
    intro E hE h
    have h_id : ∀ n, μ ((E n)ᶜ) = 1 - μ (E n) := fun n => by
      rw [measure_compl (hE n) (measure_ne_top μ _), measure_univ]
    refine Filter.Tendsto.congr (fun n => (h_id n).symm) ?_
    have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
      ENNReal.continuous_sub_left (by simp)
    have h_step : Filter.Tendsto (fun n => (1 : ℝ≥0∞) - μ (E n)) Filter.atTop
        (𝓝 ((1 : ℝ≥0∞) - 1)) := h_cont.tendsto _ |>.comp h
    simpa using h_step
  have h_badX_to_zero : Filter.Tendsto (fun n => μ (badX n)) Filter.atTop (𝓝 0) :=
    h_bad_tendsto goodX h_meas_goodX hX
  have h_badY_to_zero : Filter.Tendsto (fun n => μ (badY n)) Filter.atTop (𝓝 0) :=
    h_bad_tendsto goodY h_meas_goodY hY
  have h_badZ_to_zero : Filter.Tendsto (fun n => μ (badZ n)) Filter.atTop (𝓝 0) :=
    h_bad_tendsto goodZ h_meas_goodZ hZ
  -- μ(jointEvt n)ᶜ ≤ μ(badX n) + μ(badY n) + μ(badZ n) → 0.
  have h_compl_sub : ∀ n, (jointEvt n)ᶜ ⊆ badX n ∪ badY n ∪ badZ n := by
    intro n
    rw [h_joint_decomp n]
    intro ω hω
    -- hω : ω ∉ goodX n ∩ goodY n ∩ goodZ n
    rw [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_inter_iff,
        not_and_or, not_and_or] at hω
    rcases hω with (h_or | hZ_bad)
    · rcases h_or with hX_bad | hY_bad
      · exact Set.mem_union_left _ (Set.mem_union_left _ hX_bad)
      · exact Set.mem_union_left _ (Set.mem_union_right _ hY_bad)
    · exact Set.mem_union_right _ hZ_bad
  have h_bound_compl : ∀ n,
      μ ((jointEvt n)ᶜ) ≤ μ (badX n) + μ (badY n) + μ (badZ n) := by
    intro n
    calc μ ((jointEvt n)ᶜ)
        ≤ μ (badX n ∪ badY n ∪ badZ n) := measure_mono (h_compl_sub n)
      _ ≤ μ (badX n ∪ badY n) + μ (badZ n) := measure_union_le _ _
      _ ≤ (μ (badX n) + μ (badY n)) + μ (badZ n) := by
          gcongr
          exact measure_union_le (badX n) (badY n)
      _ = μ (badX n) + μ (badY n) + μ (badZ n) := by ring
  -- Tendsto: μ(badX n) + μ(badY n) + μ(badZ n) → 0 + 0 + 0 = 0.
  have h_sum_tendsto : Filter.Tendsto
      (fun n => μ (badX n) + μ (badY n) + μ (badZ n)) Filter.atTop (𝓝 0) := by
    have h12 : Filter.Tendsto (fun n => μ (badX n) + μ (badY n))
        Filter.atTop (𝓝 (0 + 0)) := h_badX_to_zero.add h_badY_to_zero
    have h_all : Filter.Tendsto (fun n => (μ (badX n) + μ (badY n)) + μ (badZ n))
        Filter.atTop (𝓝 ((0 + 0) + 0)) := h12.add h_badZ_to_zero
    simpa using h_all
  -- μ((jointEvt n)ᶜ) → 0 by squeeze with `0 ≤ · ≤ (sum)`.
  have h_compl_tendsto : Filter.Tendsto (fun n => μ ((jointEvt n)ᶜ))
      Filter.atTop (𝓝 0) := by
    -- bot_le for 0 ≤ μ; h_bound_compl for the upper bound; sandwich.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_sum_tendsto (fun n => bot_le) h_bound_compl
  -- μ(jointEvt n) = 1 - μ((jointEvt n)ᶜ) → 1 - 0 = 1.
  -- jointEvt n is measurable.
  have h_meas_joint : ∀ n, MeasurableSet (jointEvt n) := by
    intro n
    rw [h_joint_decomp n]
    exact ((h_meas_goodX n).inter (h_meas_goodY n)).inter (h_meas_goodZ n)
  have h_id : ∀ n, μ (jointEvt n) = 1 - μ ((jointEvt n)ᶜ) := fun n => by
    rw [measure_compl (h_meas_joint n) (measure_ne_top μ _), measure_univ]
    -- 1 - (1 - x) = x for x ≤ 1 in ℝ≥0∞ (which holds: x = μ ≤ 1)
    have h_le : μ (jointEvt n) ≤ 1 := prob_le_one
    exact (ENNReal.sub_sub_cancel (by simp) h_le).symm
  refine Filter.Tendsto.congr (fun n => (h_id n).symm) ?_
  have h_cont : Continuous (fun x : ℝ≥0∞ => (1 : ℝ≥0∞) - x) :=
    ENNReal.continuous_sub_left (by simp)
  have h_step : Filter.Tendsto (fun n => (1 : ℝ≥0∞) - μ ((jointEvt n)ᶜ))
      Filter.atTop (𝓝 ((1 : ℝ≥0∞) - 0)) := h_cont.tendsto _ |>.comp h_compl_tendsto
  simpa using h_step

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
joint axis identification (`hidentZ`) is **not** required for this bound (it would
be required only for Phase C / D, downstream of this lemma). -/
theorem jointlyTypicalSet_indep_prob_le
    [DecidableEq α] [Nonempty α] [DecidableEq β] [Nonempty β]
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
