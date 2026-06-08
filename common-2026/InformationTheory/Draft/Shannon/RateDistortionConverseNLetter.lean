import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.RateDistortion.ConverseMonotone
import InformationTheory.Shannon.RateDistortion.Achievability
import InformationTheory.Shannon.RateDistortion.ConvexityDischarge

/-!
# Rate-distortion converse (n-letter form, E-4''C MVP)

[`docs/moonshot-seeds.md`](../../../docs/moonshot-seeds.md) の **E-4''C** カード:
n-letter ブロック lossy code に対する converse:

```
∀ block lossy code (encoder, decoder),  i.i.d. source P_X^n,
  c.expectedBlockDistortion P_X d ≤ D ⟹
    (1/n) · (rateDistortionFunction d P_X D).toReal ≤ (1/n) · Real.log M.
```

## Stage 構成

* **Stage 1 — block-level n-letter converse**: 既存 `rate_distortion_converse_single_shot_specified`
  を `(α := Fin n → α, β := Fin n → β, M := Fin M)` で **直接 instantiate**。
  block distortion `blockDistortion d n` を distortion measure として渡し、
  `c.expectedBlockDistortion P_X d ≤ D` を hypothesis に取る。
  結論: `(rateDistortionFunction (blockDistortion d n) (P_X^n) D).toReal ≤ Real.log M`。
* **Stage 2 — single-letterized form**: per-letter `R(Dt) ≤ I(X_i; X̂_i)` を集めて
  `h_super: ∑ I(X_i; X̂_i) ≤ I(X^n; X̂^n)` (hypothesis) + Stage 1 + n-way Jensen
  (hypothesis pass-through) + block-distortion identity (hypothesis pass-through) で
  `(R(D) over per-letter P_X).toReal ≤ (1/n) · log M` を導く。

## 設計判断

* **Hypothesis pass-through を許容**: n-way Jensen (`n · R(D̃) ≤ ∑ R(Dt)`)、
  block-distortion Fubini identity (`expectedBlockDistortion = (1/n) ∑ Dt`)、
  MI tensorization `∑ I(X_i; X̂_i) ≤ I(X^n; X̂^n)` の三本は **仮定として受け取る**。
  これらは各々 ~50-200 行で discharge 可能だが本 MVP の scope 外。
* **既存ファイル不変**: 新規ファイルのみ。`RateDistortionConverse.lean` 等の
  既存 file は編集しない (downstream 影響回避)。

## 主定理

* `rate_distortion_converse_n_letter_block`: Stage 1。block-level distortion form。
* `rate_distortion_converse_n_letter_singleLetter`: Stage 2。single-letterized form。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-! ## Stage 1 — block-level n-letter converse -/

/-- **Stage 1 — block-level n-letter rate-distortion converse**.

For any block lossy code `c : LossyCode M n α β` (with `encoder : (Fin n → α) → Fin M`,
`decoder : Fin M → (Fin n → β)`) and i.i.d. source `P_X` on `α`, if
`c.expectedBlockDistortion P_X d ≤ D` then the block-level rate-distortion
function satisfies
```
(rateDistortionFunction (fun x y => blockDistortion d n x y)
  (Measure.pi (fun _ => P_X)) D).toReal ≤ Real.log M.
```

This is a direct `(α := Fin n → α, β := Fin n → β, M := Fin M)` instantiation of
`rate_distortion_converse_single_shot_specified` with the block distortion as the
distortion measure. The proof packages the lossy code into the
`(encoder, decoder)` shape required by the parent theorem and routes the
i.i.d. source through `Measure.pi`. -/
@[entry_point]
theorem rate_distortion_converse_n_letter_block
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSingletonClass β]
    {M n : ℕ} [NeZero M]
    (c : LossyCode M n α β)
    (hencoder : Measurable c.encoder) (hdecoder : Measurable c.decoder)
    (d : DistortionFn α β)
    (P_X : Measure α) [IsProbabilityMeasure P_X]
    {D : ℝ}
    (hD : c.expectedBlockDistortion P_X d ≤ D)
    (hMI_W_finite :
      mutualInfo (Measure.pi (fun _ : Fin n => P_X)) id
        (fun x => c.encoder x) ≠ ∞) :
    (rateDistortionFunction (fun x y => blockDistortion d n x y)
        (Measure.pi (fun _ : Fin n => P_X)) D).toReal
      ≤ Real.log (Fintype.card (Fin M)) := by
  -- Substitution: α' := Fin n → α, β' := Fin n → β, M' := Fin M,
  -- Ω' := Fin n → α, μ' := Measure.pi (fun _ => P_X), X' := id,
  -- d' := fun x y => blockDistortion d n x y.
  set Pi_X : Measure (Fin n → α) := Measure.pi (fun _ : Fin n => P_X) with hPi_def
  haveI : IsProbabilityMeasure Pi_X := by
    rw [hPi_def]; infer_instance
  -- d as ℝ-valued bivariate function.
  set d_block : (Fin n → α) → (Fin n → β) → ℝ :=
    fun x y => blockDistortion d n x y with hd_block_def
  -- Measurability of (x, y) ↦ d_block x y on the product space.
  -- d_block is real-valued, but α × β is Fintype + MeasurableSingletonClass, so all
  -- functions out of it are measurable. We prove measurability of the projection
  -- bundle and use the fact that any function from a discrete measurable space is
  -- measurable.
  have hd_block_meas : Measurable
      (fun p : (Fin n → α) × (Fin n → β) => d_block p.1 p.2) := by
    show Measurable (fun p : (Fin n → α) × (Fin n → β) =>
      (1 / (n : ℝ)) * ∑ i, ((d (p.1 i) (p.2 i) : NNReal) : ℝ))
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ fun i _ => ?_
    refine measurable_coe_nnreal_real.comp ?_
    -- d (p.1 i) (p.2 i) : NNReal. α × β is Fintype + MeasurableSingletonClass,
    -- so any function out is measurable; pre-composing with the measurable pair
    -- (p.1 i, p.2 i) preserves measurability.
    have h_pair :
        Measurable (fun p : (Fin n → α) × (Fin n → β) => (p.1 i, p.2 i)) :=
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
    have h_d : Measurable (fun ab : α × β => d ab.1 ab.2) :=
      measurable_from_prod_countable_left (fun _ => measurable_of_countable _)
    exact h_d.comp h_pair
  -- expectedBlockDistortion identity: P_X^n integral of d_block id (decoder ∘ encoder).
  have h_expBlock_eq :
      ∫ x : Fin n → α, d_block x (c.decoder (c.encoder x)) ∂Pi_X
        = c.expectedBlockDistortion P_X d := by
    unfold LossyCode.expectedBlockDistortion
    rfl
  have hD' :
      ∫ x : Fin n → α, d_block (id x) (c.decoder (c.encoder (id x))) ∂Pi_X ≤ D := by
    simp only [id_eq]
    rw [h_expBlock_eq]
    exact hD
  -- mutualInfo with X = id reduces to mutualInfo at the source RVs.
  have hMI' :
      mutualInfo Pi_X id (fun x => c.encoder (id x)) ≠ ∞ := by
    simpa [id_eq] using hMI_W_finite
  -- Apply parent theorem. `Measure.map id Pi_X = Pi_X` since `id` is a measurable
  -- equiv (identity); use `Measure.map_id` to align signatures.
  have h_main :=
    rate_distortion_converse_single_shot_specified
      (α := Fin n → α) (β := Fin n → β) (M := Fin M)
      Pi_X (X := id) (encoder := c.encoder) (decoder := c.decoder)
      measurable_id hencoder hdecoder d_block hd_block_meas hMI' hD'
  simpa using h_main

/-! ## Block-level MI ≤ log M (Stage 2 補助) -/

/-- **Block-level MI ≤ log M**. For any block lossy code `c : LossyCode M n α β`
and i.i.d. source `μ` on `Ω` with X^n-projection `Xs_block : Ω → (Fin n → α)`,
the mutual information between `X^n` and the reconstruction
`X̂^n := decoder ∘ encoder ∘ X^n` satisfies
```
(mutualInfo μ X^n X̂^n).toReal ≤ Real.log (Fintype.card (Fin M)).
```

Same DPI + max-entropy chain as `rate_distortion_converse_single_shot`'s steps 1-3,
extracted as a standalone lemma. -/
@[entry_point]
lemma mutualInfo_block_le_log_card
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSingletonClass β]
    {M n : ℕ} [NeZero M]
    (c : LossyCode M n α β)
    (hencoder : Measurable c.encoder) (hdecoder : Measurable c.decoder)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs_block : Ω → (Fin n → α)) (hXs_block : Measurable Xs_block)
    (hMI_W_finite :
      mutualInfo μ Xs_block (fun ω => c.encoder (Xs_block ω)) ≠ ∞) :
    (mutualInfo μ Xs_block
        (fun ω => c.decoder (c.encoder (Xs_block ω)))).toReal
      ≤ Real.log (Fintype.card (Fin M)) := by
  -- Same as `rate_distortion_converse_single_shot` steps 1-3.
  set W : Ω → Fin M := fun ω => c.encoder (Xs_block ω) with hW_def
  set Xh : Ω → (Fin n → β) := fun ω => c.decoder (c.encoder (Xs_block ω)) with hXh_def
  have hW_meas : Measurable W := hencoder.comp hXs_block
  have hXh_meas : Measurable Xh := hdecoder.comp hW_meas
  -- Step 1: entropy μ W ≤ log M.
  have h_step1 : entropy μ W ≤ Real.log (Fintype.card (Fin M)) :=
    InformationTheory.Shannon.MaxEntropy.entropy_le_log_card μ W hW_meas
  -- Step 2: (mutualInfo μ Xs_block W).toReal ≤ entropy μ W via Bridge.
  have h_bridge :
      (mutualInfo μ W Xs_block).toReal
        = entropy μ W - InformationTheory.MeasureFano.condEntropy μ W Xs_block :=
    mutualInfo_eq_entropy_sub_condEntropy μ W Xs_block hW_meas hXs_block
  have h_condEntropy_nn :
      0 ≤ InformationTheory.MeasureFano.condEntropy μ W Xs_block :=
    condEntropy_nonneg μ W Xs_block
  have h_comm : mutualInfo μ Xs_block W = mutualInfo μ W Xs_block :=
    mutualInfo_comm μ Xs_block W hXs_block hW_meas
  have h_step2 : (mutualInfo μ Xs_block W).toReal ≤ entropy μ W := by
    rw [h_comm, h_bridge]; linarith
  -- Step 3: DPI gives mutualInfo μ Xs_block Xh ≤ mutualInfo μ Xs_block W.
  have hXh_eq : Xh = c.decoder ∘ W := rfl
  have h_dpi :
      mutualInfo μ Xs_block Xh ≤ mutualInfo μ Xs_block W := by
    rw [hXh_eq]
    exact mutualInfo_le_of_postprocess μ Xs_block W hXs_block hW_meas hdecoder
  have hMI_Xh_finite : mutualInfo μ Xs_block Xh ≠ ∞ :=
    ne_top_of_le_ne_top hMI_W_finite h_dpi
  have h_step3 :
      (mutualInfo μ Xs_block Xh).toReal ≤ (mutualInfo μ Xs_block W).toReal :=
    ENNReal.toReal_mono hMI_W_finite h_dpi
  linarith

/-! ## Stage 2 — single-letterized form (hypothesis pass-through) -/

/-- **Per-letter feasible feed**: for fixed `i`, the joint `ν_i := μ.map (Xs i, X̂s i)`
is feasible for the per-letter `R(Dt)` at threshold
`Dt := ∫ d(Xs i ω) (X̂s i ω) ∂μ`. Hence
`R(Dt) ≤ klDiv ν_i ((ν_i.map fst).prod (ν_i.map snd)) = mutualInfo μ (Xs i) (X̂s i)`.

This is the per-letter analogue of the chain used in `rate_distortion_converse_single_shot`. -/
@[entry_point]
lemma rateDistortionFunction_le_mutualInfo_perLetter
    {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β']
    (μ : Measure Ω) (X : Ω → α') (Xh : Ω → β')
    (hX : Measurable X) (hXh : Measurable Xh)
    (d : α' → β' → ℝ)
    (hd : Measurable (fun p : α' × β' => d p.1 p.2)) :
    rateDistortionFunction d (μ.map X) (∫ ω, d (X ω) (Xh ω) ∂μ)
      ≤ mutualInfo μ X Xh := by
  -- Joint ν := μ.map (X, Xh) is feasible at D̃ := ∫ d(X, Xh) ∂μ.
  set ν : Measure (α' × β') := μ.map (fun ω => (X ω, Xh ω)) with hν_def
  -- Marginal: ν.map fst = μ.map X.
  have hν_marg : ν.map Prod.fst = μ.map X := by
    rw [hν_def, Measure.map_map measurable_fst (hX.prodMk hXh)]
    rfl
  -- Expected distortion of ν equals ∫ d(X, Xh) ∂μ (pushforward integral).
  have h_expDist : expectedDistortion d ν = ∫ ω, d (X ω) (Xh ω) ∂μ := by
    unfold expectedDistortion
    rw [hν_def, integral_map (hX.prodMk hXh).aemeasurable hd.aestronglyMeasurable]
  have hν_dist : expectedDistortion d ν ≤ ∫ ω, d (X ω) (Xh ω) ∂μ := by
    rw [h_expDist]
  -- klDiv-form of MI: klDiv ν ((ν.map fst).prod (ν.map snd)) = mutualInfo μ X Xh.
  have h_snd : ν.map Prod.snd = μ.map Xh := by
    rw [hν_def, Measure.map_map measurable_snd (hX.prodMk hXh)]
    rfl
  have h_kl_eq :
      klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd)) = mutualInfo μ X Xh := by
    rw [hν_marg, h_snd]; rfl
  calc rateDistortionFunction d (μ.map X) (∫ ω, d (X ω) (Xh ω) ∂μ)
      ≤ klDiv ν ((ν.map Prod.fst).prod (ν.map Prod.snd)) :=
        rateDistortionFunction_le_of_feasible d (μ.map X) _ ν hν_marg hν_dist
    _ = mutualInfo μ X Xh := h_kl_eq

/-- **Stage 2 — single-letterized n-letter rate-distortion converse**.

Hypothesis pass-through form. Given a block lossy code, an i.i.d. source `P_X`,
and a probability space `(Ω, μ)` where `Xs i : Ω → α` are i.i.d. copies of `P_X`
and `X̂s i := (decoder ∘ encoder ∘ X^n)_i : Ω → β`, the per-letter
rate-distortion function evaluates as:
```
(rateDistortionFunction (d as ℝ-valued) P_X D).toReal ≤ (1/n) · Real.log M.
```

The proof composes:
1. **Per-letter feasibility**: `R(Dt) ≤ I(X_i; X̂_i)` via
   `rateDistortionFunction_le_mutualInfo_perLetter`.
2. **`h_super` hypothesis**: `∑ I(X_i; X̂_i) ≤ I(X^n; X̂^n)` (MI tensorization,
   hypothesis pass-through).
3. **Block-level MI bound**: `I(X^n; X̂^n).toReal ≤ log M`
   (`mutualInfo_block_le_log_card`).
4. **`h_jensen_antitone` hypothesis**: combined Jensen + antitonicity on toReal:
   `(R(P_X, D)).toReal ≤ (1/n) ∑ (R(P_X, Dt)).toReal`. Bundles n-way Jensen
   (via R(D) convexity) with antitonicity (via `c.expectedBlockDistortion ≤ D`).
   Hypothesis pass-through.

Migration note (Phase 2.RD.1 of `ratedistortion-pgpc-sorry-migration-plan`):
The two load-bearing hypotheses `h_super` (MI tensorization for the block) and
`h_jensen_antitone` (combined n-way Jensen + antitonicity + block-distortion
identity, on toReal) have been removed; both are mathematically substantial
Mathlib-gap content that must be closed by the converse plan, not absorbed
into a precondition. Body retreated to `sorry`.

`@residual(plan:rate-distortion-converse-plan)`

-/
@[entry_point]
theorem rate_distortion_converse_n_letter_singleLetter
    [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSingletonClass β]
    {M n : ℕ} [NeZero M] (hn : 0 < n)
    (c : LossyCode M n α β)
    (hencoder : Measurable c.encoder) (hdecoder : Measurable c.decoder)
    (d : DistortionFn α β)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (P_X : Measure α) [IsProbabilityMeasure P_X]
    (hXs_law : ∀ i, μ.map (Xs i) = P_X)
    -- ω ↦ X^n(ω) := (Xs 0 ω, …, Xs (n-1) ω); Xh i ω := (decoder (encoder X^n(ω))) i.
    (h_MI_block_finite :
      mutualInfo μ (fun ω i => Xs i ω)
        (fun ω => c.encoder (fun j => Xs j ω)) ≠ ∞)
    (h_MI_perletter_finite :
      ∀ i, mutualInfo μ (Xs i)
        (fun ω => c.decoder (c.encoder (fun j => Xs j ω)) i) ≠ ∞)
    {D : ℝ} :
    (rateDistortionFunction (fun a b => ((d a b : NNReal) : ℝ)) P_X D).toReal
      ≤ (1 / (n : ℝ)) * Real.log (Fintype.card (Fin M)) := by
  sorry

end InformationTheory.Shannon
