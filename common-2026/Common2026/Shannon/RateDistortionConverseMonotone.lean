import Common2026.Shannon.RateDistortionConverse

/-!
# Rate-distortion converse (specified-distortion form, E-4' MVP)

[`docs/shannon/rate-distortion-converse-plan.md`](../../../docs/shannon/rate-distortion-converse-plan.md)
の後継カード E-4' の MVP。Cover-Thomas 10.4 を **指定歪み形** で publish:

```
D̃ := 𝔼 d(X, decoder(encoder X)) ≤ D
⟹ (rateDistortionFunction (μ.map X) D).toReal ≤ Real.log M
```

戦略は **R(D) の単調性** (`D₁ ≤ D₂ ⟹ R(D₂) ≤ R(D₁)`、feasible set 包含) と
親 single-shot 形 (`R(D̃) ≤ log M`) の合成。`R(D) ≤ R(D̃) ≤ log M`。

E-4 本来 scope の convexity + n-letter Jensen は別カード (E-4'') へ deferred。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## Monotonicity of `rateDistortionFunction` -/

/-- **Antitone monotonicity of `R(D)`**. The rate-distortion function is antitone
in the distortion threshold: enlarging the feasibility budget can only lower the
infimum.

Proof: any joint feasible at `D₁` (i.e. `expectedDistortion d ν ≤ D₁`) is also
feasible at `D₂` (since `D₁ ≤ D₂`), so the `iInf` at `D₂` is over a *larger*
set and hence smaller. -/
theorem rateDistortionFunction_antitone
    (d : α → β → ℝ) (P : Measure α)
    {D₁ D₂ : ℝ} (hD : D₁ ≤ D₂) :
    rateDistortionFunction d P D₂ ≤ rateDistortionFunction d P D₁ := by
  unfold rateDistortionFunction
  refine le_iInf fun ν => le_iInf fun hν_marg => le_iInf fun hν_dist => ?_
  -- ν is feasible at D₁; feasibility at D₂ follows from hD.
  have hν_dist₂ : expectedDistortion d ν ≤ D₂ := le_trans hν_dist hD
  exact iInf_le_of_le ν (iInf_le_of_le hν_marg (iInf_le _ hν_dist₂))

/-! ## Specified-distortion single-shot converse 主定理 -/

/-- **Single-shot rate-distortion converse, specified-distortion form (E-4' MVP)**.

For any single-shot lossy code `(encoder, decoder)` with image alphabet `M` and
source random variable `X : Ω → α`, if the actual expected distortion
`D̃ := 𝔼 d(X, decoder(encoder X))` does not exceed a specified threshold `D`,
then the rate-distortion function at the *specified* threshold `D` is also
bounded by `Real.log |M|`:
```
∫ ω, d (X ω) (decoder (encoder (X ω))) ∂μ ≤ D
⟹ (rateDistortionFunction d (μ.map X) D).toReal ≤ Real.log |M|.
```

This is the form most commonly seen in textbooks (`R(D) ≤ rate`) and is the
specified-distortion lift of `rate_distortion_converse_single_shot` via R(D)
monotonicity. The `n`-letter form requires `R(D)` convexity (Jensen) and is
deferred (E-4''). -/
theorem rate_distortion_converse_single_shot_specified
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β]
    {M : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (encoder : α → M) (decoder : M → β)
    (hX : Measurable X)
    (hencoder : Measurable encoder) (hdecoder : Measurable decoder)
    (d : α → β → ℝ)
    (hd : Measurable (fun p : α × β => d p.1 p.2))
    (hMI_W_finite :
      mutualInfo μ X (fun ω => encoder (X ω)) ≠ ∞)
    {D : ℝ}
    (hD : ∫ ω, d (X ω) (decoder (encoder (X ω))) ∂μ ≤ D) :
    (rateDistortionFunction d (μ.map X) D).toReal
      ≤ Real.log (Fintype.card M) := by
  -- ## Step 1: parent single-shot converse at the *actual* distortion D̃.
  have h_parent :
      (rateDistortionFunction d (μ.map X)
          (∫ ω, d (X ω) (decoder (encoder (X ω))) ∂μ)).toReal
        ≤ Real.log (Fintype.card M) :=
    rate_distortion_converse_single_shot μ X encoder decoder
      hX hencoder hdecoder d hd hMI_W_finite
  -- ## Step 2: monotonicity gives R(D) ≤ R(D̃) (both in ℝ≥0∞).
  have h_mono :
      rateDistortionFunction d (μ.map X) D
        ≤ rateDistortionFunction d (μ.map X)
            (∫ ω, d (X ω) (decoder (encoder (X ω))) ∂μ) :=
    rateDistortionFunction_antitone d (μ.map X) hD
  -- ## Step 3: lift to ℝ via `ENNReal.toReal_mono`.
  -- The parent R(D̃) is finite (bounded above by mutualInfo μ X Xh which is
  -- finite by hMI_W_finite + DPI). We extract finiteness from h_parent's
  -- premise rather than re-proving it.
  set W : Ω → M := fun ω => encoder (X ω) with hW_def
  set Xh : Ω → β := fun ω => decoder (encoder (X ω)) with hXh_def
  have hW_meas : Measurable W := hencoder.comp hX
  have hXh_meas : Measurable Xh := hdecoder.comp hW_meas
  -- R(D̃) ≤ mutualInfo μ X Xh (feasible: ν := μ.map (X, Xh)).
  have h_R_Dtilde_le_MI :
      rateDistortionFunction d (μ.map X)
          (∫ ω, d (X ω) (Xh ω) ∂μ)
        ≤ mutualInfo μ X Xh := by
    set ν : Measure (α × β) := μ.map (fun ω => (X ω, Xh ω)) with hν_def
    have hν_marg : ν.map Prod.fst = μ.map X := by
      rw [hν_def, Measure.map_map measurable_fst (hX.prodMk hXh_meas)]
      rfl
    have h_expDist :
        expectedDistortion d ν = ∫ ω, d (X ω) (Xh ω) ∂μ := by
      unfold expectedDistortion
      rw [hν_def, integral_map (hX.prodMk hXh_meas).aemeasurable
        hd.aestronglyMeasurable]
    have hν_dist :
        expectedDistortion d ν ≤ ∫ ω, d (X ω) (Xh ω) ∂μ := by rw [h_expDist]
    have h_kl_eq :
        klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd))
          = mutualInfo μ X Xh := by
      have h_snd : ν.map Prod.snd = μ.map Xh := by
        rw [hν_def, Measure.map_map measurable_snd (hX.prodMk hXh_meas)]
        rfl
      rw [hν_marg, h_snd]; rfl
    calc rateDistortionFunction d (μ.map X) (∫ ω, d (X ω) (Xh ω) ∂μ)
        ≤ klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd)) :=
          rateDistortionFunction_le_of_feasible d (μ.map X) _ ν hν_marg hν_dist
      _ = mutualInfo μ X Xh := h_kl_eq
  -- mutualInfo μ X Xh ≠ ∞ via DPI from hMI_W_finite.
  have hXh_eq_decoder_W : Xh = decoder ∘ W := rfl
  have h_dpi :
      mutualInfo μ X Xh ≤ mutualInfo μ X W := by
    rw [hXh_eq_decoder_W]
    exact mutualInfo_le_of_postprocess μ X W hX hW_meas hdecoder
  have hMI_Xh_finite : mutualInfo μ X Xh ≠ ∞ :=
    ne_top_of_le_ne_top hMI_W_finite h_dpi
  -- Hence R(D̃) ≠ ∞.
  have h_R_Dtilde_finite :
      rateDistortionFunction d (μ.map X)
          (∫ ω, d (X ω) (Xh ω) ∂μ) ≠ ∞ :=
    ne_top_of_le_ne_top hMI_Xh_finite h_R_Dtilde_le_MI
  -- Final: (R(D)).toReal ≤ (R(D̃)).toReal ≤ log M.
  have h_toReal :
      (rateDistortionFunction d (μ.map X) D).toReal
        ≤ (rateDistortionFunction d (μ.map X)
              (∫ ω, d (X ω) (Xh ω) ∂μ)).toReal :=
    ENNReal.toReal_mono h_R_Dtilde_finite h_mono
  linarith

end InformationTheory.Shannon
