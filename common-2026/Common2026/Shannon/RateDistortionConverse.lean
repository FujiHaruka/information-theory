import Common2026.Fano.Measure
import Common2026.Meta.EntryPoint
import Common2026.Shannon.Bridge
import Common2026.Shannon.DPI
import Common2026.Shannon.MaxEntropy
import Common2026.Shannon.MutualInfo
import Common2026.Shannon.Pi

/-!
# Rate-distortion converse (single-shot, E-4)

[`docs/shannon/rate-distortion-converse-plan.md`](../../../docs/shannon/rate-distortion-converse-plan.md)
の本体。Cover-Thomas 10.4 の **single-shot 形** rate-distortion converse:

```
Real.log M ≥ entropy μ W                    -- entropy_le_log_card
          ≥ (mutualInfo μ X W).toReal       -- I = H - H|... ≤ H (condEntropy nonneg)
          ≥ (mutualInfo μ X X̂).toReal       -- DPI: X̂ = decoder ∘ W
          ≥ (rateDistortionFunction P_X D̃).toReal
                                            -- iInf ≤ value at the joint ν := μ.map (X, X̂)
```

## 主定理

- `rate_distortion_converse_single_shot`:
    `R(D̃) ≤ log M` for `D̃ := 𝔼 d(X, decoder(encoder X))`.

## 設計判断 (plan 判断ログより)

- **single-shot scope**. n-letter form は R(D) の convexity を要し deferred。
- **`R(D̃)`** (実測歪み) で publish。R(D) 単調性は deferred。
- **MI 有限性は仮定**。
- distortion measure `d : α → β → ℝ` (non-negativity 不要)。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## Phase A — definitions -/

/-- Expected distortion of a joint distribution `ν : Measure (α × β)` under a
distortion measure `d : α → β → ℝ`. -/
noncomputable def expectedDistortion
    (d : α → β → ℝ) (ν : Measure (α × β)) : ℝ :=
  ∫ p, d p.1 p.2 ∂ν

/-- Rate-distortion function. For a source distribution `P : Measure α` and
distortion threshold `D : ℝ`, R(D) is the infimum (in `ℝ≥0∞`) of the joint
KL-form mutual information `klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd))`
over feasible joint distributions `ν` satisfying:
- `ν.map Prod.fst = P` (X-marginal matches source)
- `expectedDistortion d ν ≤ D` (average distortion within threshold)

When no feasible `ν` exists the iInf is `∞`. The value lives in `ℝ≥0∞` so the
`iInf` is total. -/
noncomputable def rateDistortionFunction
    (d : α → β → ℝ) (P : Measure α) (D : ℝ) : ℝ≥0∞ :=
  ⨅ (ν : Measure (α × β)) (_ : ν.map Prod.fst = P)
    (_ : expectedDistortion d ν ≤ D),
      klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd))

/-! ## Phase B — basic properties -/

/-- Feasible point ⇒ `R(D)` ≤ value: exhibiting a feasible joint `ν` gives an
upper bound on the rate-distortion function. -/
theorem rateDistortionFunction_le_of_feasible
    (d : α → β → ℝ) (P : Measure α) (D : ℝ)
    (ν : Measure (α × β))
    (hν_marg : ν.map Prod.fst = P)
    (hν_dist : expectedDistortion d ν ≤ D) :
    rateDistortionFunction d P D
      ≤ klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd)) := by
  unfold rateDistortionFunction
  exact iInf_le_of_le ν (iInf_le_of_le hν_marg (iInf_le _ hν_dist))

/-! ## Phase C — single-shot converse 主定理 -/

/-- Marginal of the joint `μ.map (X, Xh)` is `μ.map X` (left projection). -/
private lemma map_fst_joint
    (μ : Measure Ω) (X : Ω → α) (Xh : Ω → β)
    (hX : Measurable X) (hXh : Measurable Xh) :
    (μ.map (fun ω => (X ω, Xh ω))).map Prod.fst = μ.map X := by
  rw [Measure.map_map measurable_fst (hX.prodMk hXh)]
  rfl

/-- Marginal of the joint `μ.map (X, Xh)` is `μ.map Xh` (right projection). -/
private lemma map_snd_joint
    (μ : Measure Ω) (X : Ω → α) (Xh : Ω → β)
    (hX : Measurable X) (hXh : Measurable Xh) :
    (μ.map (fun ω => (X ω, Xh ω))).map Prod.snd = μ.map Xh := by
  rw [Measure.map_map measurable_snd (hX.prodMk hXh)]
  rfl

/-- The joint-`klDiv` form of mutual information at `ν := μ.map (X, Xh)` equals
`mutualInfo μ X Xh`. Both sides unfold to the same KL divergence after pushing
the `Prod.fst`/`Prod.snd` projections through `μ.map`. -/
private lemma klDiv_joint_eq_mutualInfo
    (μ : Measure Ω) (X : Ω → α) (Xh : Ω → β)
    (hX : Measurable X) (hXh : Measurable Xh) :
    klDiv (μ.map (fun ω => (X ω, Xh ω)))
        (((μ.map (fun ω => (X ω, Xh ω))).map Prod.fst).prod
          ((μ.map (fun ω => (X ω, Xh ω))).map Prod.snd))
      = mutualInfo μ X Xh := by
  rw [map_fst_joint μ X Xh hX hXh, map_snd_joint μ X Xh hX hXh]
  rfl

/-- Pushforward of `d (X ω) (Xh ω)` under `μ.map (X, Xh)` recovers the original
integral over `μ`: `∫ p, d p.1 p.2 ∂(μ.map (X, Xh)) = ∫ ω, d (X ω) (Xh ω) ∂μ`. -/
private lemma expectedDistortion_map
    (μ : Measure Ω) (X : Ω → α) (Xh : Ω → β)
    (hX : Measurable X) (hXh : Measurable Xh)
    (d : α → β → ℝ) (hd : Measurable (fun p : α × β => d p.1 p.2)) :
    expectedDistortion d (μ.map (fun ω => (X ω, Xh ω)))
      = ∫ ω, d (X ω) (Xh ω) ∂μ := by
  unfold expectedDistortion
  rw [integral_map (hX.prodMk hXh).aemeasurable hd.aestronglyMeasurable]

/-- **Single-shot rate-distortion converse (E-4 主定理)**.

For any single-shot lossy code `(encoder, decoder)` with image alphabet `M` and
source random variable `X : Ω → α`, the rate-distortion function evaluated at
the achieved distortion `D̃ := 𝔼 d(X, decoder(encoder X))` is bounded above by
`Real.log |M|`:
```
(rateDistortionFunction d P_X D̃).toReal ≤ Real.log |M|.
```
This is the single-shot form of Cover-Thomas 10.4. The `n`-letter form
`rate ≥ R(D)` requires `R(D)` convexity (Jensen) and is deferred. -/
@[entry_point]
theorem rate_distortion_converse_single_shot
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
      mutualInfo μ X (fun ω => encoder (X ω)) ≠ ∞) :
    (rateDistortionFunction d (μ.map X)
        (∫ ω, d (X ω) (decoder (encoder (X ω))) ∂μ)).toReal
      ≤ Real.log (Fintype.card M) := by
  -- Set up the auxiliary random variables.
  set W : Ω → M := fun ω => encoder (X ω) with hW_def
  set Xh : Ω → β := fun ω => decoder (encoder (X ω)) with hXh_def
  have hW_meas : Measurable W := hencoder.comp hX
  have hXh_meas : Measurable Xh := hdecoder.comp hW_meas
  -- ## Step 1: entropy μ W ≤ Real.log |M|.
  have h_step1 : entropy μ W ≤ Real.log (Fintype.card M) :=
    InformationTheory.Shannon.MaxEntropy.entropy_le_log_card μ W hW_meas
  -- ## Step 2: (mutualInfo μ X W).toReal ≤ entropy μ W.
  -- Use Bridge: I(W; X) = H(W) - H(W|X) ≤ H(W). Then mutualInfo_comm.
  have h_bridge :
      (mutualInfo μ W X).toReal
        = entropy μ W - InformationTheory.MeasureFano.condEntropy μ W X :=
    mutualInfo_eq_entropy_sub_condEntropy μ W X hW_meas hX
  have h_condEntropy_nn :
      0 ≤ InformationTheory.MeasureFano.condEntropy μ W X :=
    condEntropy_nonneg μ W X
  have h_comm : mutualInfo μ X W = mutualInfo μ W X :=
    mutualInfo_comm μ X W hX hW_meas
  have h_step2 : (mutualInfo μ X W).toReal ≤ entropy μ W := by
    rw [h_comm, h_bridge]; linarith
  -- ## Step 3: mutualInfo μ X Xh ≤ mutualInfo μ X W via DPI.
  -- Xh = decoder ∘ W definitionally.
  have hXh_eq : Xh = decoder ∘ W := rfl
  have h_dpi_ennreal :
      mutualInfo μ X Xh ≤ mutualInfo μ X W := by
    rw [hXh_eq]
    exact mutualInfo_le_of_postprocess μ X W hX hW_meas hdecoder
  have hMI_Xh_finite : mutualInfo μ X Xh ≠ ∞ :=
    ne_top_of_le_ne_top hMI_W_finite h_dpi_ennreal
  have h_step3 :
      (mutualInfo μ X Xh).toReal ≤ (mutualInfo μ X W).toReal :=
    ENNReal.toReal_mono hMI_W_finite h_dpi_ennreal
  -- ## Step 4: (rateDistortionFunction (μ.map X) D̃).toReal ≤ (mutualInfo μ X Xh).toReal.
  -- Apply rateDistortionFunction_le_of_feasible to ν := μ.map (X, Xh).
  set ν : Measure (α × β) := μ.map (fun ω => (X ω, Xh ω)) with hν_def
  have hν_marg : ν.map Prod.fst = μ.map X := map_fst_joint μ X Xh hX hXh_meas
  have h_expDist :
      expectedDistortion d ν = ∫ ω, d (X ω) (Xh ω) ∂μ :=
    expectedDistortion_map μ X Xh hX hXh_meas d hd
  have hν_dist :
      expectedDistortion d ν ≤ ∫ ω, d (X ω) (Xh ω) ∂μ := by
    rw [h_expDist]
  have h_R_le_kl :
      rateDistortionFunction d (μ.map X) (∫ ω, d (X ω) (Xh ω) ∂μ)
        ≤ klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd)) :=
    rateDistortionFunction_le_of_feasible d (μ.map X)
      (∫ ω, d (X ω) (Xh ω) ∂μ) ν hν_marg hν_dist
  have h_kl_eq_MI :
      klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd))
        = mutualInfo μ X Xh :=
    klDiv_joint_eq_mutualInfo μ X Xh hX hXh_meas
  have h_R_le_MI :
      rateDistortionFunction d (μ.map X) (∫ ω, d (X ω) (Xh ω) ∂μ)
        ≤ mutualInfo μ X Xh := by
    rw [← h_kl_eq_MI]; exact h_R_le_kl
  have h_step4 :
      (rateDistortionFunction d (μ.map X)
          (∫ ω, d (X ω) (Xh ω) ∂μ)).toReal
        ≤ (mutualInfo μ X Xh).toReal :=
    ENNReal.toReal_mono hMI_Xh_finite h_R_le_MI
  -- Chain.
  linarith

end InformationTheory.Shannon
