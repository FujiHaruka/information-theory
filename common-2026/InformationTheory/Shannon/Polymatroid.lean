import InformationTheory.Meta.EntryPoint
import InformationTheory.Polymatroid.Basic
import InformationTheory.Shannon.Han.D

/-!
# Polymatroid axioms for joint entropy (Phase A〜C skeleton)

Polymatroid moonshot ([`docs/han/polymatroid-moonshot-plan.md`](../../../docs/han/polymatroid-moonshot-plan.md))
の Phase A skeleton。Han Phase D の `jointEntropySubset` (`HanD.lean:114`) が
**polymatroid rank function の 3 性質** を満たすことを示す:

* Phase A — `jointEntropySubset_empty`     : `H(X_∅) = 0`
* Phase B — `jointEntropySubset_mono`      : `S ⊆ T ⟹ H(X_S) ≤ H(X_T)`
* Phase C — `jointEntropySubset_submodular`:
  `H(X_{S∪T}) + H(X_{S∩T}) ≤ H(X_S) + H(X_T)`

## 戦略 (inventory より)

* Phase A — `Pi.uniqueOfIsEmpty` で `(↥(∅ : Finset (Fin n)) → α)` が `Unique`、
  HanD chain rule base case (`Han.lean:64-85`) と同じパターン。
* Phase B — `MeasurableEquiv.piFinsetUnion`
  (`Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:612`) で
  `T = S ⊔ (T\S)` を pair `((↥S → α) × (↥(T\S) → α))` に reshape、
  Phase A `entropy_pair_eq_entropy_add_condEntropy` + `condEntropy ≥ 0` で結ぶ。
* Phase C — 3 ピース disjoint 分解 `S ∪ T = I ⊔ A ⊔ B`
  (`I := S ∩ T`, `A := S \ T`, `B := T \ S`)。各 entropy を chain rule で展開し、
  `condEntropy_le_condEntropy_of_pair` で `H(X_B | X_I, X_A) ≤ H(X_B | X_I)` を効かせる。
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Phase A — empty subset entropy -/

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Polymatroid axiom (i): empty subset entropy is zero.

`(↥(∅ : Finset (Fin n)) → α)` is `Unique` via `Pi.uniqueOfIsEmpty`, so the
push-forward measure is concentrated on `default` and `Real.negMulLog 1 = 0`. -/
@[entry_point]
theorem jointEntropySubset_empty
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) :
    jointEntropySubset μ Xs ∅ = 0 := by
  unfold jointEntropySubset entropy
  have hmeas : Measurable (fun ω (i : (∅ : Finset (Fin n))) => Xs i.val ω) :=
    measurable_pi_iff.mpr (fun i => (Finset.notMem_empty i.val i.property).elim)
  haveI : IsProbabilityMeasure
      (μ.map (fun ω (i : (∅ : Finset (Fin n))) => Xs i.val ω)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  haveI : IsEmpty (↥(∅ : Finset (Fin n))) :=
    ⟨fun i => (Finset.notMem_empty i.val i.property)⟩
  haveI : Unique (↥(∅ : Finset (Fin n)) → α) := Pi.uniqueOfIsEmpty _
  rw [Fintype.sum_unique]
  have hsingle : ((μ.map (fun ω (i : (∅ : Finset (Fin n))) => Xs i.val ω)).real
        {default} : ℝ) = 1 := by
    have huniv : ({default} : Set (↥(∅ : Finset (Fin n)) → α)) = Set.univ := by
      ext f; simp [Subsingleton.elim f default]
    rw [huniv, measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [hsingle, Real.negMulLog_one]

/-! ## Phase B — monotonicity -/

/-- Polymatroid axiom (ii): monotonicity in `S`.

`T = S ⊔ (T \ S)` reshape via `MeasurableEquiv.piFinsetUnion` followed by the
pair chain rule and `condEntropy ≥ 0`. -/
@[entry_point]
theorem jointEntropySubset_mono
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {S T : Finset (Fin n)} (h : S ⊆ T) :
    jointEntropySubset μ Xs S ≤ jointEntropySubset μ Xs T := by
  -- Setup: split T into S and T \ S via subsetSplitMEquivAux.
  set XS : Ω → (↥S → α) := fun ω j => Xs j.val ω with hXS_def
  set XR : Ω → (↥(T \ S) → α) := fun ω j => Xs j.val ω with hXR_def
  have hXS_meas : Measurable XS :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  have hXR_meas : Measurable XR :=
    measurable_pi_iff.mpr (fun _ => hXs _)
  let e := subsetSplitMEquivAux (β := fun _ : Fin n => α)
    Finset.disjoint_sdiff (Finset.union_sdiff_of_subset h)
  -- Bridge: (e ∘ (XS, XR)) ω = X_T ω
  have hbridge : (fun ω => e (XS ω, XR ω))
      = fun ω (j : ↥T) => Xs j.val ω := by
    funext ω
    exact subsetSplitMEquivAux_apply Finset.disjoint_sdiff
      (Finset.union_sdiff_of_subset h) (fun k => Xs k ω)
  -- Reshape entropy of X_T to entropy of the pair (XS, XR).
  have h_reshape :
      entropy μ (fun ω (j : ↥T) => Xs j.val ω)
        = entropy μ (fun ω => (XS ω, XR ω)) := by
    rw [← hbridge]
    exact entropy_measurableEquiv_comp μ
      (fun ω => (XS ω, XR ω)) (hXS_meas.prodMk hXR_meas) e
  -- Pair chain rule: H(XS, XR) = H(XS) + H(XR | XS).
  have h_chain :
      entropy μ (fun ω => (XS ω, XR ω))
        = entropy μ XS
          + InformationTheory.MeasureFano.condEntropy μ XR XS :=
    entropy_pair_eq_entropy_add_condEntropy μ XS XR hXS_meas hXR_meas
  -- condEntropy is non-negative: 0 ≤ H(XR | XS).
  have h_cond_nn :
      0 ≤ InformationTheory.MeasureFano.condEntropy μ XR XS :=
    condEntropy_nonneg μ XR XS
  -- Combine.
  unfold jointEntropySubset
  rw [h_reshape, h_chain]
  linarith

/-! ## Subset chain rule helper (used by Phase C)

A "disjoint union" version of the pair chain rule that lets the caller specify
the target `U` directly (avoiding `T₂ \ T₁` casts). -/

/-- Disjoint-union pair chain rule. If `s ∪ t = U` and `Disjoint s t`, then
`H(X_U) = H(X_s) + H(X_t | X_s)`.

Proof: build `e : ((↥s → α) × (↥t → α)) ≃ᵐ (↥U → α)` directly from
`subsetSplitMEquivAux` (Mathlib `MeasurableEquiv.piFinsetUnion` + cast), then apply
the pair chain rule. -/
theorem jointEntropySubset_disjoint_union
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {s t U : Finset (Fin n)} (hd : Disjoint s t) (hU : s ∪ t = U) :
    jointEntropySubset μ Xs U
      = jointEntropySubset μ Xs s
        + InformationTheory.MeasureFano.condEntropy μ
            (fun ω (j : ↥t) => Xs j.val ω)
            (fun ω (j : ↥s) => Xs j.val ω) := by
  set XS : Ω → (↥s → α) := fun ω j => Xs j.val ω
  set XT : Ω → (↥t → α) := fun ω j => Xs j.val ω
  have hXS_meas : Measurable XS := measurable_pi_iff.mpr (fun _ => hXs _)
  have hXT_meas : Measurable XT := measurable_pi_iff.mpr (fun _ => hXs _)
  let e := subsetSplitMEquivAux (β := fun _ : Fin n => α) hd hU
  have hbridge : (fun ω => e (XS ω, XT ω))
      = fun ω (j : ↥U) => Xs j.val ω := by
    funext ω
    exact subsetSplitMEquivAux_apply hd hU (fun k => Xs k ω)
  have h_reshape :
      entropy μ (fun ω (j : ↥U) => Xs j.val ω)
        = entropy μ (fun ω => (XS ω, XT ω)) := by
    rw [← hbridge]
    exact entropy_measurableEquiv_comp μ
      (fun ω => (XS ω, XT ω)) (hXS_meas.prodMk hXT_meas) e
  have h_chain :
      entropy μ (fun ω => (XS ω, XT ω))
        = entropy μ XS
          + InformationTheory.MeasureFano.condEntropy μ XT XS :=
    entropy_pair_eq_entropy_add_condEntropy μ XS XT hXS_meas hXT_meas
  unfold jointEntropySubset
  rw [h_reshape, h_chain]

/-- condEntropy reshape under disjoint union: when `Disjoint s t` and `s ∪ t = U`,
the condEntropy with conditioner `X_U` equals the condEntropy with conditioner the
pair `(X_s, X_t)`. -/
theorem condEntropy_reshape_disjoint_union
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
      [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (Xc : Ω → β) (hXc : Measurable Xc)
    {s t U : Finset (Fin n)} (hd : Disjoint s t) (hU : s ∪ t = U) :
    InformationTheory.MeasureFano.condEntropy μ Xc
        (fun ω (j : ↥U) => Xs j.val ω)
      = InformationTheory.MeasureFano.condEntropy μ Xc
          (fun ω => ((fun (j : ↥s) => Xs j.val ω), (fun (j : ↥t) => Xs j.val ω))) := by
  set XS : Ω → (↥s → α) := fun ω j => Xs j.val ω
  set XT : Ω → (↥t → α) := fun ω j => Xs j.val ω
  have hXS_meas : Measurable XS := measurable_pi_iff.mpr (fun _ => hXs _)
  have hXT_meas : Measurable XT := measurable_pi_iff.mpr (fun _ => hXs _)
  let e := subsetSplitMEquivAux (β := fun _ : Fin n => α) hd hU
  have hbridge : (fun ω => e (XS ω, XT ω))
      = fun ω (j : ↥U) => Xs j.val ω := by
    funext ω
    exact subsetSplitMEquivAux_apply hd hU (fun k => Xs k ω)
  rw [show (fun ω (j : ↥U) => Xs j.val ω) = fun ω => e (XS ω, XT ω) from hbridge.symm]
  exact condEntropy_measurableEquiv_comp μ Xc hXc
    (fun ω => (XS ω, XT ω)) (hXS_meas.prodMk hXT_meas) e

/-! ## Phase C — submodularity -/

/-- Polymatroid axiom (iii): submodularity.

3-piece disjoint decomposition `S ∪ T = I ⊔ A ⊔ B` with `I := S ∩ T`,
`A := S \ T`, `B := T \ S`. Expand each side via chain rule and apply
`condEntropy_le_condEntropy_of_pair` once. -/
@[entry_point]
theorem jointEntropySubset_submodular
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S T : Finset (Fin n)) :
    jointEntropySubset μ Xs (S ∪ T) + jointEntropySubset μ Xs (S ∩ T)
      ≤ jointEntropySubset μ Xs S + jointEntropySubset μ Xs T := by
  -- Three disjoint decompositions:
  --   (a) S       = (S∩T) ⊔ (S\T)
  --   (b) T       = (S∩T) ⊔ (T\S)
  --   (c) S ∪ T   = S     ⊔ (T\S)
  have hda : Disjoint (S ∩ T) (S \ T) :=
    (Finset.disjoint_sdiff_inter S T).symm
  have hUa : (S ∩ T) ∪ (S \ T) = S := by
    rw [Finset.union_comm]; exact Finset.sdiff_union_inter S T
  have hdb : Disjoint (S ∩ T) (T \ S) := by
    have : Disjoint (T ∩ S) (T \ S) := (Finset.disjoint_sdiff_inter T S).symm
    rwa [Finset.inter_comm] at this
  have hUb : (S ∩ T) ∪ (T \ S) = T := by
    rw [Finset.inter_comm, Finset.union_comm]; exact Finset.sdiff_union_inter T S
  have hdc : Disjoint S (T \ S) := Finset.disjoint_sdiff
  have hUc : S ∪ (T \ S) = S ∪ T := Finset.union_sdiff_self_eq_union
  -- Apply jointEntropySubset_disjoint_union three times.
  have h_S_eq  := jointEntropySubset_disjoint_union μ Xs hXs hda hUa
  have h_T_eq  := jointEntropySubset_disjoint_union μ Xs hXs hdb hUb
  have h_ST_eq := jointEntropySubset_disjoint_union μ Xs hXs hdc hUc
  -- Set up name shortcuts.
  set XI : Ω → (↥(S ∩ T) → α) := fun ω j => Xs j.val ω with hXI_def
  set XA : Ω → (↥(S \ T) → α) := fun ω j => Xs j.val ω with hXA_def
  set XB : Ω → (↥(T \ S) → α) := fun ω j => Xs j.val ω with hXB_def
  have hXI_meas : Measurable XI := measurable_pi_iff.mpr (fun _ => hXs _)
  have hXA_meas : Measurable XA := measurable_pi_iff.mpr (fun _ => hXs _)
  have hXB_meas : Measurable XB := measurable_pi_iff.mpr (fun _ => hXs _)
  -- (c) gives: H(X_{S∪T}) = H(X_S) + H(X_B | X_S).
  -- Reshape H(X_B | X_S) = H(X_B | (X_{S∩T}, X_{S\T})) via condEntropy_reshape_disjoint_union.
  have h_cond_S_pair :
      InformationTheory.MeasureFano.condEntropy μ XB
          (fun ω (j : ↥S) => Xs j.val ω)
        = InformationTheory.MeasureFano.condEntropy μ XB
            (fun ω => (XI ω, XA ω)) :=
    condEntropy_reshape_disjoint_union μ Xs hXs XB hXB_meas hda hUa
  -- condEntropy_le_condEntropy_of_pair: H(X_B | (X_{S∩T}, X_{S\T})) ≤ H(X_B | X_{S∩T}).
  have h_cond_le :
      InformationTheory.MeasureFano.condEntropy μ XB
          (fun ω => (XI ω, XA ω))
        ≤ InformationTheory.MeasureFano.condEntropy μ XB XI :=
    condEntropy_le_condEntropy_of_pair μ XB XI XA hXB_meas hXI_meas hXA_meas
  -- Compute. Let H_I := jointEntropySubset μ Xs (S ∩ T), H_S := ..., etc.
  -- From h_S_eq:  H_S  = H_I + H(X_A | X_I)
  -- From h_T_eq:  H_T  = H_I + H(X_B | X_I)
  -- From h_ST_eq: H_ST = H_S + H(X_B | X_S)   (and X_S = (fun ω j => ...))
  -- We want:     H_ST + H_I ≤ H_S + H_T.
  -- Equivalently:H_S + H(X_B | X_S) + H_I ≤ H_S + H_T = H_S + H_I + H(X_B | X_I).
  -- Which reduces to: H(X_B | X_S) ≤ H(X_B | X_I).
  -- And h_cond_S_pair + h_cond_le gives exactly that.
  have h_BS_le_BI :
      InformationTheory.MeasureFano.condEntropy μ XB
          (fun ω (j : ↥S) => Xs j.val ω)
        ≤ InformationTheory.MeasureFano.condEntropy μ XB XI := by
    rw [h_cond_S_pair]; exact h_cond_le
  -- Combine: from h_S_eq, h_T_eq, h_ST_eq, h_BS_le_BI, do linarith.
  -- jointEntropySubset μ Xs (S ∩ T) = entropy μ XI is by definition.
  -- The condEntropy slot in h_T_eq/h_S_eq matches XB/XA (with conditioner XI).
  -- Note: The condEntropy slot in h_T_eq is condEntropy μ (fun ω j : ↥(T\S) => ...) (fun ω j : ↥(S∩T) => ...)
  -- which equals condEntropy μ XB XI by `set` definitions.
  -- Same for h_S_eq.
  linarith [h_S_eq, h_T_eq, h_ST_eq, h_BS_le_BI]

/-! ## Polymatroid wrapper

Joint entropy as a `Combinatorics.Polymatroid` term: the four polymatroid
axioms are exactly the three theorems above (`jointEntropySubset_empty` /
`jointEntropySubset_mono` / `jointEntropySubset_submodular`), repackaged
into the `Polymatroid` structure introduced in
`InformationTheory/Polymatroid/Basic.lean`. -/

/-- Joint entropy as a polymatroid rank function. -/
@[entry_point]
noncomputable def entropyPolymatroid
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    Combinatorics.Polymatroid (Fin n) where
  rank S := jointEntropySubset μ Xs S
  rank_empty := jointEntropySubset_empty μ Xs
  rank_mono := fun _ _ h => jointEntropySubset_mono μ Xs hXs h
  rank_submodular := jointEntropySubset_submodular μ Xs hXs

end InformationTheory.Shannon
