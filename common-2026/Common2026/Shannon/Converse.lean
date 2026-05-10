import Common2026.Shannon.MutualInfo
import Common2026.Shannon.DPI
import Common2026.Shannon.Bridge
import Common2026.Shannon.CondMutualInfo
import Common2026.Fano.Measure
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Single-shot Shannon converse (Phase 4-γ skeleton)

Shannon ムーンショット ([`docs/shannon/shannon-moonshot-plan.md`](../../../docs/shannon/shannon-moonshot-plan.md))
の Phase 4-γ: 通信路符号化定理の逆 (single-shot 版) を、Phase 4-β bridge と
Phase 4-α DPI、Phase 3 Fano (Measure 版) の組み合わせで導く。

## 主定理

`Msg : Ω → M` (uniform on `M`, `|M| ≥ 2`)、`Yo : Ω → Y` (channel output)、
`decoder : Y → M`、`Pe = μ {Msg ≠ decoder ∘ Yo}` のとき:

```
log |M| ≤ I(Msg; Yo) + h(Pe) + Pe · log(|M| - 1)
```

`mutualInfo μ Msg Yo` が `∞` のとき `.toReal = 0` で bound が壊れるため、有限性を仮定する。

## 証明骨格

```
log|M| = H(Msg)                                           -- helper: uniform → log|M|
       = I(Msg; decoder∘Yo).toReal + H(Msg | decoder∘Yo)  -- Phase 4-β bridge (rearranged)
       ≤ I(Msg; Yo).toReal        + H(Msg | decoder∘Yo)   -- Phase 4-α DPI (postprocess Y → M_hat)
       ≤ I(Msg; Yo).toReal        + h(Pe) + Pe·log(|M|-1) -- Phase 3 Fano (decoder = id : M→M)
```

なお計画書 (`docs/shannon/shannon-moonshot-plan.md` Phase 4-γ) では `I(encoder∘Msg; Yo)` を含む版が
書かれているが、Markov 仮定なしには `I(Msg; Yo) ≤ I(encoder∘Msg; Yo)` は一般に成り立たない
ため、ここでは encoder を含まない素直な定式化を採用する。encoder 版は injective encoder の
仮定下でこの結果から系として従う。
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

/-! ## Phase 4-δ-(a): injective encoder の系

`encoder : M → X` が injective なら、Phase 4-α DPI を `decoder' := Function.invFun encoder`
で 1 回追加で適用するだけで `I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)` が出る。これを
`shannon_converse_single_shot` と組み合わせて encoder を含む形の bound を導く。

```
I(Msg; Yo) = I(Yo; Msg)                              -- mutualInfo_comm
           = I(Yo; decoder' ∘ (encoder ∘ Msg))       -- decoder' ∘ encoder = id
           ≤ I(Yo; encoder ∘ Msg)                    -- Phase 4-α DPI
           = I(encoder ∘ Msg; Yo)                    -- mutualInfo_comm
```
-/

/-- Single-shot Shannon converse, encoder 付き版 (injective encoder の系):
`encoder : M → X` が injective なら、`log |M| ≤ I(encoder ∘ Msg; Yo) + h(Pe) + Pe · log(|M| - 1)`. -/
theorem shannon_converse_single_shot_injective_encoder
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → X) (Yo : Ω → Y) (decoder : Y → M)
    (hMsg : Measurable Msg) (hYo : Measurable Yo)
    (hencoder : Measurable encoder) (hdecoder : Measurable decoder)
    (hencoder_inj : Function.Injective encoder)
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
  -- 左逆 decoder' : X → M を Function.invFun で構成
  let decoder' : X → M := Function.invFun encoder
  have hdecoder'_left : Function.LeftInverse decoder' encoder :=
    Function.leftInverse_invFun hencoder_inj
  have hMsg_eq : decoder' ∘ (encoder ∘ Msg) = Msg := by
    funext ω; exact hdecoder'_left (Msg ω)
  -- decoder' は X が Fintype + MeasurableSingletonClass なので自動 measurable
  have hdecoder' : Measurable decoder' := measurable_of_countable _
  have h_enc_Msg : Measurable (encoder ∘ Msg) := hencoder.comp hMsg
  -- DPI: I(Yo; decoder' ∘ (encoder ∘ Msg)) ≤ I(Yo; encoder ∘ Msg)
  have h_dpi_yo :
      mutualInfo μ Yo (decoder' ∘ (encoder ∘ Msg))
        ≤ mutualInfo μ Yo (encoder ∘ Msg) :=
    mutualInfo_le_of_postprocess μ Yo (encoder ∘ Msg) hYo h_enc_Msg hdecoder'
  rw [hMsg_eq] at h_dpi_yo
  -- 対称化: I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)
  have h_le_ennreal :
      mutualInfo μ Msg Yo ≤ mutualInfo μ (encoder ∘ Msg) Yo := by
    rw [mutualInfo_comm μ Msg Yo hMsg hYo,
        ← mutualInfo_comm μ (encoder ∘ Msg) Yo h_enc_Msg hYo] at *
    exact h_dpi_yo
  -- I(Msg; Yo) も有限
  have hMI_Msg_finite : mutualInfo μ Msg Yo ≠ ∞ :=
    ne_top_of_le_ne_top hMI_finite h_le_ennreal
  -- toReal レベルでの単調性
  have h_le_real :
      (mutualInfo μ Msg Yo).toReal ≤ (mutualInfo μ (encoder ∘ Msg) Yo).toReal :=
    ENNReal.toReal_mono hMI_finite h_le_ennreal
  -- 既存 single-shot に bridge
  have h_base := shannon_converse_single_shot
    μ Msg Yo decoder hMsg hYo hdecoder hMsg_uniform hcard hMI_Msg_finite
  linarith

/-! ## Phase 4-δ-(b): Markov encoder の系

Markov chain `Msg → encoder ∘ Msg → Yo` (β-form: `Yo` の (encoder∘Msg, Msg) 条件付き分布が
encoder∘Msg のみに依存) の仮定下では、`mutualInfo_le_of_markov` で `I(Msg; Yo) ≤
I(encoder ∘ Msg; Yo)` が出る。injective encoder の系 (Phase 4-δ-(a)) と異なり encoder の
injectivity を仮定しない代わりに、通信路の Markov 性を要請する形。

```
I(Msg; Yo) ≤ I(encoder ∘ Msg; Yo)         -- mutualInfo_le_of_markov (Markov chain hypothesis)
log |M| ≤ I(Msg; Yo) + h(Pe) + Pe·log(|M|-1)  -- shannon_converse_single_shot
```
-/

/-- Single-shot Shannon converse, Markov encoder 版:
Markov chain `Msg → encoder ∘ Msg → Yo` (β-form) のもとで、
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
  -- 既存 single-shot に bridge
  have h_base := shannon_converse_single_shot
    μ Msg Yo decoder hMsg hYo hdecoder hMsg_uniform hcard hMI_Msg_finite
  linarith

end InformationTheory.Shannon
