import InformationTheory.Shannon.MutualInfo
import InformationTheory.Shannon.DPI
import InformationTheory.Shannon.Bridge
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Fano.Measure
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Single-shot Shannon channel coding converse

The converse to the channel coding theorem (single-shot version): for a uniformly
distributed message `Msg` and channel output `Yo`,
`log |M| ≤ I(Msg; Yo) + h(Pe) + Pe · log(|M| - 1)`.

## Main statements

* `shannon_converse_single_shot` — converse bound for a uniform message.
* `shannon_converse_single_shot_markov_encoder` — converse with a Markov encoder.

## Implementation notes

The proof chains `entropy μ Msg = log |M|` (uniform), the Bridge identity
`mutualInfo_eq_entropy_sub_condEntropy`, the DPI `mutualInfo_le_of_postprocess`
(applied to `decoder : Y → M`), and the Fano inequality. The encoder-free formulation
is adopted because `I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)` does not hold without a Markov
assumption; the Markov-encoder corollary is proved separately.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M]
variable {Y : Type*} [MeasurableSpace Y]

omit [DecidableEq M] in
/-- For a uniformly distributed message `Msg : Ω → M` over a finite alphabet
(i.e. `μ.map Msg = |M|⁻¹ • Measure.count`), the Shannon entropy equals `log |M|`. -/
private lemma entropy_of_uniform_msg
    (μ : Measure Ω)
    (Msg : Ω → M)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count) :
    entropy μ Msg = Real.log (Fintype.card M) := by
  unfold entropy
  have hcard_ne : (Fintype.card M : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have h_measure : ∀ x : M, (μ.map Msg).real {x} = (Fintype.card M : ℝ)⁻¹ := by
    intro x
    rw [Measure.real, hMsg_uniform, Measure.smul_apply, smul_eq_mul,
        Measure.count_singleton, mul_one, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
  simp_rw [h_measure]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog,
      Real.log_inv]
  field_simp

omit [DecidableEq M] in
/-- Single-shot Shannon converse: for a uniformly distributed message `Msg`
transmitted via channel output `Yo` and decoded by `decoder`,
`log |M| ≤ I(Msg; Yo) + h(Pe) + Pe · log(|M| - 1)`,
where `Pe = errorProb μ Msg Yo decoder = μ {Msg ≠ decoder ∘ Yo}`.

Requires `mutualInfo μ Msg Yo ≠ ∞` so that `.toReal` is monotone across DPI. -/
theorem shannon_converse_single_shot
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Yo : Ω → Y) (decoder : Y → M)
    (hMsg : Measurable Msg) (hYo : Measurable Yo) (hdecoder : Measurable decoder)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ Msg Yo ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (mutualInfo μ Msg Yo).toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg Yo decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg Yo decoder *
          Real.log ((Fintype.card M : ℝ) - 1) := by
  classical
  -- Local abbrev
  set Pe := InformationTheory.MeasureFano.errorProb μ Msg Yo decoder
  have hM_hat_meas : Measurable (decoder ∘ Yo) := hdecoder.comp hYo
  -- Step 1: entropy μ Msg = log |M|
  have h_entropy_log : entropy μ Msg = Real.log (Fintype.card M) :=
    entropy_of_uniform_msg μ Msg hMsg_uniform
  -- Step 2: Phase 4-β bridge — KL form ↔ entropy − condEntropy
  have h_bridge :
      (mutualInfo μ Msg (decoder ∘ Yo)).toReal
        = entropy μ Msg
          - InformationTheory.MeasureFano.condEntropy μ Msg (decoder ∘ Yo) :=
    mutualInfo_eq_entropy_sub_condEntropy μ Msg (decoder ∘ Yo) hMsg hM_hat_meas
  -- Step 3: Phase 4-α DPI on Y → decoder ∘ Y, lifted to toReal under finiteness
  have h_dpi_ennreal :
      mutualInfo μ Msg (decoder ∘ Yo) ≤ mutualInfo μ Msg Yo :=
    mutualInfo_le_of_postprocess μ Msg Yo hMsg hYo hdecoder
  have h_dpi :
      (mutualInfo μ Msg (decoder ∘ Yo)).toReal ≤ (mutualInfo μ Msg Yo).toReal :=
    ENNReal.toReal_mono hMI_finite h_dpi_ennreal
  -- Step 4: Phase 3 Fano applied with `decoder = id : M → M`,
  -- which yields the same Pe by definitional reduction.
  have h_Pe_eq :
      InformationTheory.MeasureFano.errorProb μ Msg (decoder ∘ Yo) (id : M → M)
        = Pe := rfl
  have h_fano := InformationTheory.MeasureFano.fano_inequality_measure_theoretic
    μ Msg (decoder ∘ Yo) (id : M → M) hMsg hM_hat_meas measurable_id hcard
  rw [h_Pe_eq] at h_fano
  -- Chain: `log|M| = H(Msg) = I(Msg;M_hat).toReal + condEntropy ≤ I(Msg;Yo).toReal + Fano`
  linarith

/-! ## Corollary: injective encoder

For an injective `encoder : M → X`, one additional application of the DPI with
`decoder' := Function.invFun encoder` gives `I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)`,
which combines with `shannon_converse_single_shot` to give the encoder-included bound.
-/

/-! ## Corollary: Markov encoder -/

omit [DecidableEq M] in
/-- Single-shot Shannon converse with a Markov encoder:
under the Markov chain `Msg → encoder ∘ Msg → Yo`,
`log |M| ≤ I(encoder ∘ Msg; Yo) + h(Pe) + Pe · log(|M| - 1)`. -/
theorem shannon_converse_single_shot_markov_encoder
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → X) (Yo : Ω → Y) (decoder : Y → M)
    (hMsg : Measurable Msg) (hYo : Measurable Yo)
    (hencoder : Measurable encoder) (hdecoder : Measurable decoder)
    (hmarkov : IsMarkovChain μ Msg (encoder ∘ Msg) Yo)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ (encoder ∘ Msg) Yo ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (mutualInfo μ (encoder ∘ Msg) Yo).toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg Yo decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg Yo decoder *
          Real.log ((Fintype.card M : ℝ) - 1) := by
  -- Markov chain ⇒ I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)
  have h_enc_Msg : Measurable (encoder ∘ Msg) := hencoder.comp hMsg
  have h_le_ennreal :
      mutualInfo μ Msg Yo ≤ mutualInfo μ (encoder ∘ Msg) Yo :=
    mutualInfo_le_of_markov μ Msg (encoder ∘ Msg) Yo hMsg h_enc_Msg hYo hmarkov
  have hMI_Msg_finite : mutualInfo μ Msg Yo ≠ ∞ :=
    ne_top_of_le_ne_top hMI_finite h_le_ennreal
  have h_le_real :
      (mutualInfo μ Msg Yo).toReal ≤ (mutualInfo μ (encoder ∘ Msg) Yo).toReal :=
    ENNReal.toReal_mono hMI_finite h_le_ennreal
  -- apply the base single-shot converse
  have h_base := shannon_converse_single_shot
    μ Msg Yo decoder hMsg hYo hdecoder hMsg_uniform hcard hMI_Msg_finite
  linarith

end InformationTheory.Shannon
