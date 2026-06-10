import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.RateDistortion.ConverseMonotone
import InformationTheory.Shannon.RateDistortion.Achievability
import InformationTheory.Shannon.RateDistortion.ConvexityDischarge
import InformationTheory.Shannon.CondEntropyMemoryless
import InformationTheory.Shannon.AEP.Basic.Converse
import InformationTheory.Shannon.Bridge
import InformationTheory.Shannon.Entropy

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
* **Stage 2 — single-letterized form (genuine, no hypothesis pass-through)**:
  per-letter feasibility `R(Dt) ≤ I(X_i; X̂_i)` + MI superadditivity
  `∑ I(X_i; X̂_i) ≤ I(X^n; X̂^n)` (self-built, **not** a Mathlib wall) + n-way
  Jensen (built by induction from binary `rateDistortionFunction_convexOn`) +
  block-distortion identity (`expectedBlockDistortion = (1/n) ∑ Dt`, via the i.i.d.
  product law) + antitonicity で
  `(R(D) over per-letter P_X).toReal ≤ (1/n) · log M` を導く。proof done (0 sorry
  / 0 residual、`#print axioms` で sorryAx-free)。

## 設計判断

* **i.i.d. source の precondition 化**: 旧 MVP では「n-way Jensen / block-distortion
  Fubini identity / MI tensorization」を仮説 pass-through で受けていたが、これらは
  全て genuine に閉じた。MI superadditivity は独立 source 前提
  (`hindep : iIndepFun` + `hXs_law`) の下で in-project entropy 資産
  (`entropy_pi_eq_sum_of_indep` + gateway `condEntropy_pi_le_sum_condEntropy_per_letter`
  + bridge `mutualInfo_eq_entropy_sub_condEntropy`) を配線して self-build。`hindep`
  / `hXs_law` / `hD` は core を載せ替える load-bearing predicate ではなく、結論が
  成立するための genuine な precondition (独立性が無いと反例: `n=2, X₁=X₂`)。
* **既存ファイル不変**: 新規 import (`CondEntropyMemoryless` / `AEP.Basic.Converse`
  / `Bridge` / `Entropy`) のみ追加、`RateDistortionConverse.lean` 等の既存 file は
  編集しない (downstream 影響回避)。

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
    [Fintype α] [Nonempty α] [MeasurableSingletonClass α]
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
  classical
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
    [Fintype α] [Nonempty α] [MeasurableSingletonClass α]
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

/-! ## Stage 2 core — n-way Jensen for `R(D)` from binary convexity -/

/-- **Finite-alphabet integrability witness**: on finite alphabets any
`d : α → β → ℝ` is integrable against any finite measure on `α × β`. Discharges the
regularity precondition of `rateDistortionFunction_convexOn`. -/
private lemma integrable_d_of_finite
    {α β : Type*} [Fintype α] [Fintype β]
      [MeasurableSpace α] [MeasurableSingletonClass α]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (d : α → β → ℝ) (ν : Measure (α × β)) [IsFiniteMeasure ν] :
    Integrable (fun p : α × β => d p.1 p.2) ν :=
  Integrable.of_finite

/-- **ENNReal n-way Jensen for `R(D)` (uniform weights)**: for finite alphabets,
```
R(d, P, (1/n) ∑ i, Dvals i) ≤ ∑ i, ENNReal.ofReal (1/n) * R(d, P, Dvals i).
```
Built from the binary convexity `rateDistortionFunction_convexOn` by induction on
`n` via the running-average decomposition
`avg(n+1) = (n/(n+1)) · avg(n) + (1/(n+1)) · D_n`. -/
private lemma rateDistortionFunction_jensen_uniform
    {α β : Type*} [Fintype α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (d : α → β → ℝ) (P : Measure α) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (Dvals : Fin n → ℝ) :
    rateDistortionFunction d P ((1 / (n : ℝ)) * ∑ i, Dvals i)
      ≤ ∑ i, ENNReal.ofReal (1 / (n : ℝ)) * rateDistortionFunction d P (Dvals i) := by
  classical
  -- Integrability witness, fixed for all of `P`'s feasible joints (finite alphabet).
  have h_int_witness : ∀ (ν : Measure (α × β)), ν.map Prod.fst = P →
      Integrable (fun p => d p.1 p.2) ν := by
    intro ν hν
    have : IsFiniteMeasure ν := by
      refine ⟨?_⟩
      have hh : ν Set.univ = P Set.univ := by
        rw [← hν, Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
      rw [hh]; exact measure_lt_top P _
    exact integrable_d_of_finite d ν
  -- Induction on `m` for the running average over the first `m+1` points.
  -- Generalize over `Dvals : Fin (m+1) → ℝ`.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction m with
  | zero =>
    -- n = 1: R((1/1) * (Dvals 0)) ≤ ofReal 1 * R(Dvals 0).
    simp only [zero_add, Nat.cast_one, one_div, inv_one, one_mul,
      ENNReal.ofReal_one]
    rw [Fin.sum_univ_one, Fin.sum_univ_one]
  | succ m IH =>
    -- avg over Fin (m+2) = ((m+1)/(m+2)) * avg(prefix) + (1/(m+2)) * Dlast.
    set N : ℝ := ((m : ℝ) + 1) + 1 with hN_def
    have hN_pos : 0 < N := by positivity
    -- Prefix points (Fin (m+1)) and last point.
    set Dpre : Fin (m + 1) → ℝ := fun i => Dvals i.castSucc with hDpre_def
    set Dlast : ℝ := Dvals (Fin.last (m + 1)) with hDlast_def
    -- λ = (m+1)/N, 1 - λ = 1/N.
    set lam : ℝ := ((m : ℝ) + 1) / N with hlam_def
    have hlam0 : 0 ≤ lam := by rw [hlam_def]; positivity
    have hlam1 : lam ≤ 1 := by
      rw [hlam_def, div_le_one hN_pos, hN_def]; linarith
    have hN0 : N ≠ 0 := ne_of_gt hN_pos
    have h1mlam : 1 - lam = 1 / N := by
      rw [hlam_def, eq_div_iff hN0, sub_mul, one_mul, div_mul_cancel₀ _ hN0, hN_def]
      ring
    -- avg(prefix) = (1/(m+1)) ∑ Dpre.
    set avgPre : ℝ := (1 / ((m : ℝ) + 1)) * ∑ i, Dpre i with havgPre_def
    -- Key arithmetic: (1/N) ∑_{Fin (m+2)} Dvals = lam * avgPre + (1-lam) * Dlast.
    have h_avg_eq :
        (1 / N) * ∑ i, Dvals i = lam * avgPre + (1 - lam) * Dlast := by
      rw [Fin.sum_univ_castSucc, h1mlam, havgPre_def, hlam_def, hDpre_def, hDlast_def]
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    -- Cast `(↑(m+1)+1)` and `↑(m+2)` agree.
    have hNcast : ((↑(m + 1 + 1) : ℝ)) = N := by rw [hN_def]; push_cast; ring
    -- Rewrite the goal's argument and ofReal weight using N.
    rw [show ((1 : ℝ) / (↑(m + 1 + 1))) = 1 / N from by rw [hNcast], h_avg_eq]
    -- Binary convexity at the running-average split.
    have h_binary :=
      rateDistortionFunction_convexOn d P hlam0 hlam1 avgPre Dlast h_int_witness
    -- IH on the prefix: R(avgPre) ≤ ∑ ofReal (1/(m+1)) * R(Dpre i).
    have h_IH := IH Dpre
    rw [show ((1 : ℝ) / (↑(m + 1))) = 1 / ((m : ℝ) + 1) from by push_cast; ring] at h_IH
    -- Chain: R(avg) ≤ ofReal lam * R(avgPre) + ofReal (1-lam) * R(Dlast)
    --             ≤ ofReal lam * (∑ ofReal(1/(m+1)) R(Dpre)) + ofReal(1-lam) R(Dlast)
    --             = ∑_{Fin (m+2)} ofReal (1/N) * R(Dvals).
    calc rateDistortionFunction d P (lam * avgPre + (1 - lam) * Dlast)
        ≤ ENNReal.ofReal lam * rateDistortionFunction d P avgPre
            + ENNReal.ofReal (1 - lam) * rateDistortionFunction d P Dlast := h_binary
      _ ≤ ENNReal.ofReal lam
            * (∑ i, ENNReal.ofReal (1 / ((m : ℝ) + 1))
                * rateDistortionFunction d P (Dpre i))
            + ENNReal.ofReal (1 - lam) * rateDistortionFunction d P Dlast := by
            gcongr
      _ = ∑ i, ENNReal.ofReal (1 / N) * rateDistortionFunction d P (Dvals i) := by
            -- Split the RHS sum over Fin (m+2) into prefix + last.
            rw [Fin.sum_univ_castSucc
                  (f := fun i => ENNReal.ofReal (1 / N) * rateDistortionFunction d P (Dvals i)),
                Finset.mul_sum]
            congr 1
            · -- prefix: ofReal lam * (ofReal (1/(m+1)) * R(Dpre i))
              --        = ofReal (1/N) * R(Dvals i.castSucc).
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [← mul_assoc, ← ENNReal.ofReal_mul hlam0, hlam_def, hDpre_def]
              congr 2
              have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
              field_simp
            · -- last term: ofReal (1-lam) * R(Dlast) = ofReal (1/N) * R(Dvals (last)).
              rw [h1mlam, hDlast_def]

/-! ## Stage 2 core — MI superadditivity for an independent source -/

/-- **Prefix independence on `Fin n` from `iIndepFun`**: for a mutually independent
family `Xs : Fin n → Ω → α`, each `Xs i` is independent of its prefix
`(Xs 0, …, Xs (i-1))`. `Fin n`-indexed analogue of
`indepFun_Xs_prefix_of_iIndepFun` (which is `ℕ`-indexed and private). -/
private lemma indepFun_prefix_of_iIndepFun_fin
    {n : ℕ}
    {α : Type*} [MeasurableSpace α]
    (μ : Measure Ω)
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : iIndepFun (fun i => Xs i) μ) (i : Fin n) :
    IndepFun (Xs i) (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω) μ := by
  classical
  set S : Finset (Fin n) := {i} with hS_def
  set T : Finset (Fin n) := Finset.univ.filter (fun j => j.val < i.val) with hT_def
  have hST_disj : Disjoint S T := by
    rw [Finset.disjoint_singleton_left, hT_def, Finset.mem_filter]
    rintro ⟨-, hlt⟩
    exact lt_irrefl _ hlt
  have h_pair_indep := hindep.indepFun_finset S T hST_disj hXs
  -- LHS projection: (S → α) → α, evaluate at i.
  let projS : (S → α) → α := fun f => f ⟨i, Finset.mem_singleton.mpr rfl⟩
  have hprojS_meas : Measurable projS := measurable_pi_apply _
  -- RHS projection: (T → α) → (Fin i.val → α) by reindexing j ↦ ⟨j.val, _⟩.
  let projT : (T → α) → (Fin i.val → α) :=
    fun f (j : Fin i.val) =>
      f ⟨⟨j.val, j.isLt.trans i.isLt⟩, by
        rw [hT_def, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, j.isLt⟩⟩
  have hprojT_meas : Measurable projT :=
    measurable_pi_iff.mpr (fun j => measurable_pi_apply _)
  have h_lifted := h_pair_indep.comp hprojS_meas hprojT_meas
  exact h_lifted

/-- **Independent-source block entropy additivity**: for a mutually independent
family `Xs : Fin n → Ω → α`, `H(X^n) = ∑ i, H(X_i)`.

Chain rule (`jointEntropy_chain_rule`) collapses each `H(X_i | X^{<i})` to `H(X_i)`
via `condEntropy_eq_entropy_of_indepFun` and prefix independence. Unlike
`entropy_jointRV_eq_n_smul`, no identical-distribution assumption is used (each
marginal may differ); we stop before the `IdentDistrib` collapse. -/
private lemma entropy_pi_eq_sum_of_indep
    {n : ℕ}
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : iIndepFun (fun i => Xs i) μ) :
    entropy μ (fun ω j => Xs j ω) = ∑ i : Fin n, entropy μ (Xs i) := by
  classical
  -- jointEntropy μ Xs = entropy μ (fun ω j => Xs j ω) by defeq.
  have h_je : jointEntropy μ Xs = entropy μ (fun ω j => Xs j ω) := rfl
  rw [← h_je, jointEntropy_chain_rule μ Xs hXs]
  apply Finset.sum_congr rfl
  intro i _
  set prefix_i : Ω → (Fin i.val → α) :=
    fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω with hprefix_def
  have hprefix_meas : Measurable prefix_i :=
    measurable_pi_iff.mpr (fun j => hXs ⟨j.val, j.isLt.trans i.isLt⟩)
  have h_indep : IndepFun (Xs i) prefix_i μ :=
    indepFun_prefix_of_iIndepFun_fin μ Xs hXs hindep i
  exact condEntropy_eq_entropy_of_indepFun μ (Xs i) prefix_i (hXs i) hprefix_meas h_indep

/-- **Gateway piece (b): conditional-entropy subadditivity on the block**.
For any `Xs : Fin n → Ω → α` and any reconstruction family `Xhs : Fin n → Ω → β`,
```
H(X^n | X̂^n) ≤ ∑ i, H(X_i | X̂_i).
```
Encoder/decoder-agnostic; no independence needed. This is the conditional-entropy
analogue of subadditivity, obtained from the conditional chain rule
`condEntropy_pi_chain_rule` (`H(X^n | X̂^n) = ∑ H(X_i | X̂^n, X^{<i})`) followed by
dropping the extra conditioners `(X̂^n, X^{<i})` down to `X̂_i` via
`condEntropy_le_condEntropy_of_pair` (conditioning on a superset can only lower
conditional entropy). -/
-- @audit:ok — independent honesty audit 2026-06-10. Encoder/decoder- and
-- independence-agnostic; the conditioner reshape (MeasurableEquiv) + chain rule +
-- `condEntropy_le_condEntropy_of_pair` are genuine, no load-bearing hyp.
-- sorryAx-free (machine-confirmed).
lemma condEntropy_pi_le_sum_condEntropy_per_letter
    {n : ℕ}
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Xhs : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hXhs : ∀ i, Measurable (Xhs i)) :
    InformationTheory.MeasureFano.condEntropy μ
        (fun ω j => Xs j ω) (fun ω j => Xhs j ω)
      ≤ ∑ i : Fin n,
          InformationTheory.MeasureFano.condEntropy μ (Xs i) (Xhs i) := by
  classical
  have hXhs_pi : Measurable (fun ω j => Xhs j ω) := measurable_pi_iff.mpr hXhs
  -- Step 1: conditional chain rule on the block.
  -- H(X^n | X̂^n) = ∑ i, H(X_i | (X̂^n, X^{<i})).
  rw [condEntropy_pi_chain_rule μ (fun ω j => Xhs j ω) Xs hXhs_pi hXs]
  -- Step 2: per-summand drop.
  apply Finset.sum_le_sum
  intro i _
  -- Goal: H(X_i | (X̂^n, X^{<i})) ≤ H(X_i | X̂_i).
  -- Conditioner W := (fun ω => (X̂^n ω, X^{<i} ω)).
  set Xprefix : Ω → (Fin i.val → α) :=
    fun ω j => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω with hXprefix_def
  have hXprefix_meas : Measurable Xprefix :=
    measurable_pi_iff.mpr (fun j => hXs ⟨j.val, j.isLt.trans i.isLt⟩)
  -- Reshape the X̂^n part of the conditioner to extract the i-th coordinate X̂_i,
  -- using `MeasurableEquiv.piEquivPiSubtypeProd` (specialized to `j = i`).
  -- e₀ : (Fin n → β) ≃ᵐ ({j // j = i} → β) × ({j // j ≠ i} → β).
  let e₀ : (Fin n → β) ≃ᵐ ({j : Fin n // j = i} → β) × ({j : Fin n // j ≠ i} → β) :=
    MeasurableEquiv.piEquivPiSubtypeProd (π := fun _ : Fin n => β) (fun j => j = i)
  -- e₁ : ({j // j = i} → β) ≃ᵐ β (the singleton index set).
  let e₁ : ({j : Fin n // j = i} → β) ≃ᵐ β :=
    MeasurableEquiv.funUnique {j : Fin n // j = i} β
  -- e : (Fin n → β) ≃ᵐ β × ({j // j ≠ i} → β).
  let e : (Fin n → β) ≃ᵐ β × ({j : Fin n // j ≠ i} → β) :=
    e₀.trans (e₁.prodCongr (.refl _))
  -- e (X̂^n ω) = (X̂_i ω, X̂^{≠i} ω).
  set XhnoI : Ω → ({j : Fin n // j ≠ i} → β) :=
    fun ω (j : {j : Fin n // j ≠ i}) => Xhs j.val ω with hXhnoI_def
  have hXhnoI_meas : Measurable XhnoI :=
    measurable_pi_iff.mpr (fun j => hXhs j.val)
  have h_e_eq : ∀ ω, e (fun j => Xhs j ω) = (Xhs i ω, XhnoI ω) := by
    intro ω
    apply Prod.ext
    · have hdef : ((default : {j : Fin n // j = i}) : Fin n) = i := by
        show ((⟨i, rfl⟩ : {j : Fin n // j = i}) : Fin n) = i
        rfl
      simp [e, e₀, e₁, MeasurableEquiv.piEquivPiSubtypeProd,
        MeasurableEquiv.funUnique, MeasurableEquiv.prodCongr, hdef]
    · funext j
      simp [e, e₀, e₁, MeasurableEquiv.piEquivPiSubtypeProd,
        MeasurableEquiv.funUnique, MeasurableEquiv.prodCongr, XhnoI]
  -- Now reshape the full conditioner via the equiv on the first factor.
  -- E : (Fin n → β) × (Fin i → α) ≃ᵐ (β × ({j // j ≠ i} → β)) × (Fin i → α).
  let E : ((Fin n → β) × (Fin i.val → α)) ≃ᵐ
      (β × ({j : Fin n // j ≠ i} → β)) × (Fin i.val → α) :=
    e.prodCongr (.refl _)
  -- Associativity reshape to expose X̂_i as the kept conditioner:
  -- (β × R) × P ≃ᵐ β × (R × P).
  let E' : ((β × ({j : Fin n // j ≠ i} → β)) × (Fin i.val → α)) ≃ᵐ
      β × (({j : Fin n // j ≠ i} → β) × (Fin i.val → α)) :=
    MeasurableEquiv.prodAssoc
  let Etot : ((Fin n → β) × (Fin i.val → α)) ≃ᵐ
      β × (({j : Fin n // j ≠ i} → β) × (Fin i.val → α)) :=
    E.trans E'
  -- Etot (X̂^n ω, X^{<i} ω) = (X̂_i ω, (X̂^{≠i} ω, X^{<i} ω)).
  have hEtot_eq : ∀ ω,
      Etot (fun j => Xhs j ω, Xprefix ω)
        = (Xhs i ω, (XhnoI ω, Xprefix ω)) := by
    intro ω
    show E' (E (fun j => Xhs j ω, Xprefix ω))
      = (Xhs i ω, (XhnoI ω, Xprefix ω))
    have hE : E (fun j => Xhs j ω, Xprefix ω)
        = ((Xhs i ω, XhnoI ω), Xprefix ω) := by
      show (e (fun j => Xhs j ω), Xprefix ω) = ((Xhs i ω, XhnoI ω), Xprefix ω)
      rw [h_e_eq ω]
    rw [hE]
    rfl
  -- condEntropy is invariant under the equiv reshape of the conditioner.
  have hcond_meas : Measurable (fun ω => (fun j => Xhs j ω, Xprefix ω)) :=
    hXhs_pi.prodMk hXprefix_meas
  have h_reshape :
      InformationTheory.MeasureFano.condEntropy μ (Xs i)
          (fun ω => (fun j => Xhs j ω, Xprefix ω))
        = InformationTheory.MeasureFano.condEntropy μ (Xs i)
            (fun ω => (Xhs i ω, (XhnoI ω, Xprefix ω))) := by
    have h := condEntropy_measurableEquiv_comp μ (Xs i) (hXs i)
      (fun ω => (fun j => Xhs j ω, Xprefix ω)) hcond_meas Etot
    rw [show (fun ω => Etot (fun j => Xhs j ω, Xprefix ω))
            = (fun ω => (Xhs i ω, (XhnoI ω, Xprefix ω))) from funext hEtot_eq] at h
    exact h.symm
  rw [h_reshape]
  -- Drop the (X̂^{≠i}, X^{<i}) part via condEntropy_le_condEntropy_of_pair.
  exact condEntropy_le_condEntropy_of_pair μ (Xs i) (Xhs i)
    (fun ω => (XhnoI ω, Xprefix ω)) (hXs i) (hXhs i)
    (hXhnoI_meas.prodMk hXprefix_meas)

/-- **Stage 2 core: mutual-information superadditivity for an independent source**.
For `Xs : Fin n → Ω → α` *mutually independent* and any reconstruction family
`Xhs : Fin n → Ω → β`,
```
∑ i, (I(X_i; X̂_i)).toReal ≤ (I(X^n; X̂^n)).toReal.
```
Standard chain:
```
I(X^n; X̂^n) = H(X^n) - H(X^n | X̂^n)
            = ∑ H(X_i) - H(X^n | X̂^n)            -- independence (Block, equality)
            ≥ ∑ H(X_i) - ∑ H(X_i | X̂_i)           -- gateway (b)
            = ∑ (H(X_i) - H(X_i | X̂_i)) = ∑ I(X_i; X̂_i).
```
This is the same family as the "D-1 wall" in `ParallelGaussianPerCoord.lean`, but
it is **not** a Mathlib wall: it wires the existing in-project entropy assets
(independent-source entropy additivity + the conditional-entropy chain rule).

@audit:ok — independent honesty audit 2026-06-10. `hindep` is genuinely
load-bearing in the *mathematical* sense (a true precondition, NOT bundled core):
it is consumed only inside `entropy_pi_eq_sum_of_indep` to collapse `H(X^n)` to
`∑ H(Xᵢ)`. Dropping it makes the claim FALSE (X₁=X₂ ⇒ `∑I > I_joint`), so the
hypothesis is necessary and the inequality follows semantically. The hard step
(superadditivity) is built in the body from genuine bridge/chain-rule lemmas, not
asserted by a hypothesis. sorryAx-free (machine-confirmed). -/
lemma mutualInfo_superadditive_of_indep
    {n : ℕ}
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
      [MeasurableSpace α] [MeasurableSingletonClass α]
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Xhs : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hXhs : ∀ i, Measurable (Xhs i))
    (hindep : iIndepFun (fun i => Xs i) μ) :
    (∑ i : Fin n, (mutualInfo μ (Xs i) (Xhs i)).toReal)
      ≤ (mutualInfo μ (fun ω j => Xs j ω) (fun ω j => Xhs j ω)).toReal := by
  classical
  have hX_pi : Measurable (fun ω j => Xs j ω) := measurable_pi_iff.mpr hXs
  have hXh_pi : Measurable (fun ω j => Xhs j ω) := measurable_pi_iff.mpr hXhs
  -- Bridge: I(X^n; X̂^n).toReal = H(X^n) - H(X^n | X̂^n).
  have h_bridge_joint :
      (mutualInfo μ (fun ω j => Xs j ω) (fun ω j => Xhs j ω)).toReal
        = entropy μ (fun ω j => Xs j ω)
          - InformationTheory.MeasureFano.condEntropy μ
              (fun ω j => Xs j ω) (fun ω j => Xhs j ω) :=
    mutualInfo_eq_entropy_sub_condEntropy μ
      (fun ω j => Xs j ω) (fun ω j => Xhs j ω) hX_pi hXh_pi
  rw [h_bridge_joint]
  -- Independence: H(X^n) = ∑ H(X_i). (equality)
  have h_add : entropy μ (fun ω j => Xs j ω) = ∑ i : Fin n, entropy μ (Xs i) :=
    entropy_pi_eq_sum_of_indep μ Xs hXs hindep
  rw [h_add]
  -- Gateway (b): H(X^n | X̂^n) ≤ ∑ H(X_i | X̂_i).
  have h_cond_le :
      InformationTheory.MeasureFano.condEntropy μ
          (fun ω j => Xs j ω) (fun ω j => Xhs j ω)
        ≤ ∑ i : Fin n,
            InformationTheory.MeasureFano.condEntropy μ (Xs i) (Xhs i) :=
    condEntropy_pi_le_sum_condEntropy_per_letter μ Xs Xhs hXs hXhs
  -- Per-letter bridge: I(X_i; X̂_i).toReal = H(X_i) - H(X_i | X̂_i).
  have h_each_bridge : ∀ i : Fin n,
      (mutualInfo μ (Xs i) (Xhs i)).toReal
        = entropy μ (Xs i)
          - InformationTheory.MeasureFano.condEntropy μ (Xs i) (Xhs i) := by
    intro i
    exact mutualInfo_eq_entropy_sub_condEntropy μ (Xs i) (Xhs i) (hXs i) (hXhs i)
  -- Rewrite LHS sum via per-letter bridge and ∑ distributivity.
  have h_lhs_eq :
      (∑ i : Fin n, (mutualInfo μ (Xs i) (Xhs i)).toReal)
        = (∑ i : Fin n, entropy μ (Xs i))
          - (∑ i : Fin n,
              InformationTheory.MeasureFano.condEntropy μ (Xs i) (Xhs i)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => h_each_bridge i)
  rw [h_lhs_eq]
  linarith

/-- **Stage 2 — single-letterized n-letter rate-distortion converse** (genuine).

Given a block lossy code, an i.i.d. source `P_X`, and a probability space
`(Ω, μ)` where `Xs i : Ω → α` are i.i.d. copies of `P_X` (mutual independence
`hindep` + identical marginals `hXs_law`) and `X̂ᵢ := (decoder ∘ encoder ∘ X^n)ᵢ`,
the single-letter rate-distortion function satisfies
```
(rateDistortionFunction (d as ℝ-valued) P_X D).toReal ≤ (1/n) · Real.log M.
```

The proof composes, all with in-project genuine assets (no `sorry`, no residual):
1. **Block-distortion identity**: `(1/n) ∑ᵢ Dᵢ = c.expectedBlockDistortion P_X d`
   via the product law `μ.map X^n = Measure.pi (fun _ => P_X)`
   (`iIndepFun_iff_map_fun_eq_pi_map` + `hXs_law`), `integral_map`, and Fubini
   linearity over the finite sum.
2. **Antitonicity**: `R(P_X, D) ≤ R(P_X, (1/n)∑Dᵢ)` since `(1/n)∑Dᵢ ≤ D` (`hD`).
3. **n-way Jensen**: `R(P_X, (1/n)∑Dᵢ) ≤ ∑ ofReal(1/n) · R(P_X, Dᵢ)` built by
   induction on `n` from the binary convexity `rateDistortionFunction_convexOn`
   (`rateDistortionFunction_jensen_uniform`, this file).
4. **Per-letter feasibility**: `R(P_X, Dᵢ) ≤ I(Xᵢ; X̂ᵢ)` via
   `rateDistortionFunction_le_mutualInfo_perLetter` (`μ.map (Xs i) = P_X`).
5. **MI superadditivity** (independent source): `∑ I(Xᵢ; X̂ᵢ) ≤ I(X^n; X̂^n)` via
   `mutualInfo_superadditive_of_indep` (this file). This was previously believed
   to be a Mathlib wall (the "D-1 wall" family of `ParallelGaussianPerCoord.lean`);
   it is **not** — it wires the existing in-project entropy assets
   (`entropy_pi_eq_sum_of_indep` = independent-source `H(X^n) = ∑ H(Xᵢ)`, the
   gateway `condEntropy_pi_le_sum_condEntropy_per_letter` = `H(X^n|X̂^n) ≤
   ∑ H(Xᵢ|X̂ᵢ)`, and the MI↔entropy bridge `mutualInfo_eq_entropy_sub_condEntropy`).
6. **Block MI bound**: `I(X^n; X̂^n).toReal ≤ log M` (`mutualInfo_block_le_log_card`).

Under-hypothesized history (2026-06-10): a previous signature took `{D : ℝ}` as a
free variable and assumed nothing about the joint law of `Xs`, making the claimed
conclusion **false** as framed (degenerate-boundary counterexamples: `n=1, M=2,
|α|=4` uniform Hamming `D=0` gives `R = log 4 > log 2`; or `n=2, X₁=X₂` fully
dependent gives `R = log 2 > (1/2)log 2`). The repair adds, as genuine
*preconditions* (not load-bearing predicate bundling):
* `hD : c.expectedBlockDistortion P_X d ≤ D` — the operating point.
* `hindep : iIndepFun (fun i => Xs i) μ` + `hXs_law` — the i.i.d. memoryless
  source assumption (this is what makes MI superadditivity hold).
The finiteness preconditions `h_MI_block_finite` / `h_MI_perletter_finite` are
regularity (needed for the `ENNReal.toReal` monotonicity steps).

@audit:ok — independent honesty audit 2026-06-10 (commit `e73513c`): all
preconditions (`hD`/`hindep`/`hXs_law`/`[Nonempty β]`/MI-finiteness) are genuine
regularity, not load-bearing core bundling; the superadditivity + n-way Jensen
core is self-built in the body. Sufficiency confirmed: both cited
degenerate-boundary counterexamples (D-free, X₁=X₂ dependent) are closed by `hD`
and `hindep` respectively. `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free, machine-reconfirmed). -/
@[entry_point]
theorem rate_distortion_converse_n_letter_singleLetter
    [Fintype α] [Nonempty α] [MeasurableSingletonClass α]
    [Fintype β] [Nonempty β] [MeasurableSingletonClass β]
    {M n : ℕ} [NeZero M] (hn : 0 < n)
    (c : LossyCode M n α β)
    (hencoder : Measurable c.encoder) (hdecoder : Measurable c.decoder)
    (d : DistortionFn α β)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : iIndepFun (fun i => Xs i) μ)
    (P_X : Measure α) [IsProbabilityMeasure P_X]
    (hXs_law : ∀ i, μ.map (Xs i) = P_X)
    -- ω ↦ X^n(ω) := (Xs 0 ω, …, Xs (n-1) ω); Xh i ω := (decoder (encoder X^n(ω))) i.
    (h_MI_block_finite :
      mutualInfo μ (fun ω i => Xs i ω)
        (fun ω => c.encoder (fun j => Xs j ω)) ≠ ∞)
    (h_MI_perletter_finite :
      ∀ i, mutualInfo μ (Xs i)
        (fun ω => c.decoder (c.encoder (fun j => Xs j ω)) i) ≠ ∞)
    {D : ℝ}
    (hD : c.expectedBlockDistortion P_X d ≤ D) :
    (rateDistortionFunction (fun a b => ((d a b : NNReal) : ℝ)) P_X D).toReal
      ≤ (1 / (n : ℝ)) * Real.log (Fintype.card (Fin M)) := by
  classical
  -- Real-valued distortion and reconstruction RVs.
  set d' : α → β → ℝ := fun a b => ((d a b : NNReal) : ℝ) with hd'_def
  set Xn : Ω → (Fin n → α) := fun ω j => Xs j ω with hXn_def
  set Xhn : Ω → (Fin n → β) :=
    fun ω => c.decoder (c.encoder (fun j => Xs j ω)) with hXhn_def
  set Xh : Fin n → Ω → β :=
    fun i ω => c.decoder (c.encoder (fun j => Xs j ω)) i with hXh_def
  have hXn_meas : Measurable Xn := measurable_pi_iff.mpr hXs
  have hXhn_meas : Measurable Xhn := hdecoder.comp (hencoder.comp hXn_meas)
  have hXh_meas : ∀ i, Measurable (Xh i) := fun i => (measurable_pi_apply i).comp hXhn_meas
  have hd'_meas : Measurable (fun p : α × β => d' p.1 p.2) :=
    measurable_from_prod_countable_left (fun _ => measurable_of_countable _)
  -- Per-letter distortion thresholds.
  set Dvals : Fin n → ℝ := fun i => ∫ ω, d' (Xs i ω) (Xh i ω) ∂μ with hDvals_def
  -- Product law: μ.map Xn = Measure.pi (fun _ => P_X).
  have h_pi_law : μ.map Xn = Measure.pi (fun _ : Fin n => P_X) := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map (μ := μ) (f := fun i => Xs i)
      (fun i => (hXs i).aemeasurable)).mp hindep
    rw [hXn_def, h]
    congr 1
    funext i
    exact hXs_law i
  -- Block-distortion identity: (1/n) ∑ Dvals = expectedBlockDistortion P_X d.
  have h_block_id :
      (1 / (n : ℝ)) * ∑ i, Dvals i = c.expectedBlockDistortion P_X d := by
    -- Each Dvals i = ∫ x, d' (x i) (decoder (encoder x) i) ∂(pi P_X) via change of vars.
    have h_each : ∀ i, Dvals i
        = ∫ x : Fin n → α, d' (x i) (c.decoder (c.encoder x) i)
            ∂(Measure.pi (fun _ : Fin n => P_X)) := by
      intro i
      rw [hDvals_def]
      have hg_meas : Measurable
          (fun x : Fin n → α => d' (x i) (c.decoder (c.encoder x) i)) := by
        apply measurable_of_countable
      rw [← h_pi_law, integral_map hXn_meas.aemeasurable hg_meas.aestronglyMeasurable]
    -- Sum and pull through the integral.
    calc (1 / (n : ℝ)) * ∑ i, Dvals i
        = (1 / (n : ℝ)) * ∑ i, ∫ x : Fin n → α,
            d' (x i) (c.decoder (c.encoder x) i)
              ∂(Measure.pi (fun _ : Fin n => P_X)) := by
            rw [Finset.sum_congr rfl (fun i _ => h_each i)]
      _ = (1 / (n : ℝ)) * ∫ x : Fin n → α,
            ∑ i, d' (x i) (c.decoder (c.encoder x) i)
              ∂(Measure.pi (fun _ : Fin n => P_X)) := by
            rw [integral_finsetSum]
            exact fun i _ => Integrable.of_finite
      _ = ∫ x : Fin n → α,
            (1 / (n : ℝ)) * ∑ i, d' (x i) (c.decoder (c.encoder x) i)
              ∂(Measure.pi (fun _ : Fin n => P_X)) := by
            rw [integral_const_mul]
      _ = c.expectedBlockDistortion P_X d := by
            rw [LossyCode.expectedBlockDistortion]
            rfl
  -- Finiteness of each per-letter MI and the block MI.
  have hMI_per_finite : ∀ i, mutualInfo μ (Xs i) (Xh i) ≠ ∞ := by
    intro i
    exact h_MI_perletter_finite i
  have hMI_block_finite :
      mutualInfo μ Xn Xhn ≠ ∞ := by
    -- I(X^n; X̂^n) ≤ I(X^n; encoder) (DPI) which is finite by h_MI_block_finite.
    have hpost : mutualInfo μ Xn Xhn
        ≤ mutualInfo μ Xn (fun ω => c.encoder (fun j => Xs j ω)) := by
      have : Xhn = c.decoder ∘ (fun ω => c.encoder (fun j => Xs j ω)) := rfl
      rw [this]
      exact mutualInfo_le_of_postprocess μ Xn
        (fun ω => c.encoder (fun j => Xs j ω)) hXn_meas
        (hencoder.comp hXn_meas) hdecoder
    exact ne_top_of_le_ne_top h_MI_block_finite hpost
  -- Per-letter R(Dvals i) ≤ I(Xᵢ; X̂ᵢ), so R(Dvals i) is finite.
  have h_per_feasible : ∀ i,
      rateDistortionFunction d' P_X (Dvals i) ≤ mutualInfo μ (Xs i) (Xh i) := by
    intro i
    have h := rateDistortionFunction_le_mutualInfo_perLetter μ (Xs i) (Xh i)
      (hXs i) (hXh_meas i) d' hd'_meas
    rw [hXs_law i] at h
    exact h
  have hR_per_finite : ∀ i, rateDistortionFunction d' P_X (Dvals i) ≠ ∞ := fun i =>
    ne_top_of_le_ne_top (hMI_per_finite i) (h_per_feasible i)
  -- ===== Main chain =====
  -- Step A: antitonicity. R(D) ≤ R((1/n)∑Dvals) since (1/n)∑Dvals ≤ D.
  have h_avg_le_D : (1 / (n : ℝ)) * ∑ i, Dvals i ≤ D := by rw [h_block_id]; exact hD
  have h_antitone :
      rateDistortionFunction d' P_X D
        ≤ rateDistortionFunction d' P_X ((1 / (n : ℝ)) * ∑ i, Dvals i) :=
    rateDistortionFunction_antitone d' P_X h_avg_le_D
  -- Step B: Jensen. R((1/n)∑Dvals) ≤ ∑ ofReal(1/n) * R(Dvals i).
  have h_jensen :
      rateDistortionFunction d' P_X ((1 / (n : ℝ)) * ∑ i, Dvals i)
        ≤ ∑ i, ENNReal.ofReal (1 / (n : ℝ)) * rateDistortionFunction d' P_X (Dvals i) :=
    rateDistortionFunction_jensen_uniform d' P_X hn Dvals
  -- Now work in `.toReal`. RHS of jensen is finite (each summand finite).
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum_finite :
      (∑ i, ENNReal.ofReal (1 / (n : ℝ)) * rateDistortionFunction d' P_X (Dvals i)) ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hR_per_finite i)
  -- toReal of the Jensen RHS = (1/n) ∑ (R(Dvals i)).toReal.
  have h_jensen_toReal_rhs :
      (∑ i, ENNReal.ofReal (1 / (n : ℝ)) * rateDistortionFunction d' P_X (Dvals i)).toReal
        = (1 / (n : ℝ)) * ∑ i, (rateDistortionFunction d' P_X (Dvals i)).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hR_per_finite i))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  -- Chain Steps A + B in toReal.
  have h_AB :
      (rateDistortionFunction d' P_X D).toReal
        ≤ (1 / (n : ℝ)) * ∑ i, (rateDistortionFunction d' P_X (Dvals i)).toReal := by
    have hle :
        rateDistortionFunction d' P_X D
          ≤ ∑ i, ENNReal.ofReal (1 / (n : ℝ)) * rateDistortionFunction d' P_X (Dvals i) :=
      le_trans h_antitone h_jensen
    have := ENNReal.toReal_mono hsum_finite hle
    rwa [h_jensen_toReal_rhs] at this
  -- Step C: per-letter feasibility, R(Dvals i).toReal ≤ I(Xᵢ; X̂ᵢ).toReal.
  have h_per_toReal : ∀ i,
      (rateDistortionFunction d' P_X (Dvals i)).toReal
        ≤ (mutualInfo μ (Xs i) (Xh i)).toReal := fun i =>
    ENNReal.toReal_mono (hMI_per_finite i) (h_per_feasible i)
  -- Step D: MI superadditivity, ∑ I(Xᵢ; X̂ᵢ).toReal ≤ I(X^n; X̂^n).toReal.
  have h_super :
      (∑ i, (mutualInfo μ (Xs i) (Xh i)).toReal)
        ≤ (mutualInfo μ Xn Xhn).toReal :=
    mutualInfo_superadditive_of_indep μ Xs Xh hXs hXh_meas hindep
  -- Step E: block bound, I(X^n; X̂^n).toReal ≤ log M.
  have h_block_bound :
      (mutualInfo μ Xn Xhn).toReal ≤ Real.log (Fintype.card (Fin M)) := by
    have hfin' : mutualInfo μ Xn (fun ω => c.encoder (Xn ω)) ≠ ∞ := h_MI_block_finite
    have h := mutualInfo_block_le_log_card c hencoder hdecoder μ Xn hXn_meas hfin'
    exact h
  -- Assemble: combine Steps A-E.
  -- (R(D)).toReal ≤ (1/n) ∑ R(Dvals i).toReal ≤ (1/n) ∑ I(Xᵢ;X̂ᵢ).toReal
  --            ≤ (1/n) I(X^n;X̂^n).toReal ≤ (1/n) log M.
  have h_sum_per_le :
      (∑ i, (rateDistortionFunction d' P_X (Dvals i)).toReal)
        ≤ ∑ i, (mutualInfo μ (Xs i) (Xh i)).toReal :=
    Finset.sum_le_sum (fun i _ => h_per_toReal i)
  have hn_inv_nonneg : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  calc (rateDistortionFunction d' P_X D).toReal
      ≤ (1 / (n : ℝ)) * ∑ i, (rateDistortionFunction d' P_X (Dvals i)).toReal := h_AB
    _ ≤ (1 / (n : ℝ)) * ∑ i, (mutualInfo μ (Xs i) (Xh i)).toReal := by
        exact mul_le_mul_of_nonneg_left h_sum_per_le hn_inv_nonneg
    _ ≤ (1 / (n : ℝ)) * (mutualInfo μ Xn Xhn).toReal := by
        exact mul_le_mul_of_nonneg_left h_super hn_inv_nonneg
    _ ≤ (1 / (n : ℝ)) * Real.log (Fintype.card (Fin M)) := by
        exact mul_le_mul_of_nonneg_left h_block_bound hn_inv_nonneg

end InformationTheory.Shannon
