import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Converse
import InformationTheory.Shannon.MIChainRule

/-!
# Channel coding converse — n-variable i.i.d. form

## Main statements

* `channel_coding_converse_iid`: Under a Markov chain `Msg → encoder ∘ Msg → Y^n`
  and an i.i.d. joint distribution assumption, the log-cardinality of the message
  set is bounded by `n · I(X_0; Y_0) + h(Pe) + Pe · log(|M| - 1)`.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [MeasurableSpace M] [MeasurableSingletonClass M]
variable {α β : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β]
  [MeasurableSpace β] [MeasurableSingletonClass β]

omit [DecidableEq M] [DecidableEq α] [DecidableEq β] in
/-- Channel coding converse, n-variable i.i.d. form (Markov encoder).

Under a Markov chain `Msg → encoder ∘ Msg → Y^n` and an i.i.d. joint
distribution assumption:

```
log |M| ≤ n · I(X_0; Y_0).toReal + h(Pe) + Pe · log(|M| - 1)
```

where `X_0 ω := encoder (Msg ω) 0`, `Y_0 := Ys 0`, and
`Pe := errorProb μ Msg Y^n decoder`. -/
@[entry_point]
theorem channel_coding_converse_iid
    {n : ℕ} (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (h_iid_joint : μ.map (fun ω (i : Fin n) => (encoder (Msg ω) i, Ys i ω))
        = Measure.pi (fun i =>
            μ.map (fun ω => (encoder (Msg ω) i, Ys i ω))))
    (h_iid_X : μ.map (fun ω (i : Fin n) => encoder (Msg ω) i)
        = Measure.pi (fun i => μ.map (fun ω => encoder (Msg ω) i)))
    (h_iid_Y : μ.map (fun ω (i : Fin n) => Ys i ω)
        = Measure.pi (fun i => μ.map (Ys i)))
    (h_copy : ∀ i,
        μ.map (fun ω => (encoder (Msg ω) i, Ys i ω))
          = μ.map (fun ω => (encoder (Msg ω) ⟨0, hn⟩, Ys ⟨0, hn⟩ ω)))
    (h_copy_X : ∀ i,
        μ.map (fun ω => encoder (Msg ω) i)
          = μ.map (fun ω => encoder (Msg ω) ⟨0, hn⟩))
    (h_copy_Y : ∀ i, μ.map (Ys i) = μ.map (Ys ⟨0, hn⟩))
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (n : ℝ) * (mutualInfo μ
        (fun ω => encoder (Msg ω) ⟨0, hn⟩) (Ys ⟨0, hn⟩)).toReal +
        Real.binEntropy
          (InformationTheory.MeasureFano.errorProb μ Msg
            (fun ω i => Ys i ω) decoder) +
        InformationTheory.MeasureFano.errorProb μ Msg
          (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1) := by
  classical
  -- Auto-derived: encoder/Yo measurability + StandardBorel/Nonempty for `Fin n → α`,
  -- `Fin n → β`.
  have h_encoder : Measurable encoder := measurable_of_countable _
  have h_X_full : Measurable (fun ω => encoder (Msg ω)) := h_encoder.comp hMsg
  have h_Yo : Measurable (fun ω (i : Fin n) => Ys i ω) :=
    measurable_pi_iff.mpr hYs
  -- Step 1: Markov-encoder single-shot converse on (X = Fin n → α, Y = Fin n → β).
  have h_step1 :=
    shannon_converse_single_shot_markov_encoder (X := Fin n → α)
      μ Msg encoder (fun ω i => Ys i ω) decoder
      hMsg h_Yo h_encoder hdecoder hmarkov hMsg_uniform hcard hMI_finite
  -- Step 2: i.i.d. corollary collapses `I(X^n; Y^n) = n • I(X_0; Y_0)`.
  set Xs : Fin n → Ω → α := fun i ω => encoder (Msg ω) i with hXs_def
  have hXs_meas : ∀ i, Measurable (Xs i) := fun i =>
    (measurable_pi_apply i).comp h_X_full
  have h_step2 :=
    mutualInfo_iid_eq_nsmul hn μ Xs Ys hXs_meas hYs
      h_iid_joint h_iid_X h_iid_Y h_copy h_copy_X h_copy_Y
  -- `fun ω i => Xs i ω = fun ω => encoder (Msg ω)` definitionally.
  have h_pi_eq_encoder :
      (fun ω (i : Fin n) => Xs i ω) = fun ω => encoder (Msg ω) := rfl
  rw [h_pi_eq_encoder] at h_step2
  -- Step 3: `(n • _).toReal = n * _.toReal`. h_step1 uses `encoder ∘ Msg` (defeq to
  -- η-expanded form in h_step2); normalize with `Function.comp_def`.
  rw [show (encoder ∘ Msg) = fun ω => encoder (Msg ω) from rfl,
      h_step2, ENNReal.toReal_nsmul, nsmul_eq_mul] at h_step1
  -- `Xs ⟨0, hn⟩ = fun ω => encoder (Msg ω) ⟨0, hn⟩` definitionally.
  exact h_step1

end InformationTheory.Shannon
