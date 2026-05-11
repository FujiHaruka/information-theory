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
open scoped ENNReal NNReal BigOperators

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

end InformationTheory.Shannon.ChannelCoding
