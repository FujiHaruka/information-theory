import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.Stationary.Basic
import InformationTheory.Shannon.EntropyRate
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Dynamics.Ergodic.Ergodic

namespace InformationTheory.Shannon.TwoSided

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology symmDiff

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Shifted finite-dimensional marginals -/

section ShiftedMarginal

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)

/-- The minimal non-negative integer `N` that makes every element of `J` non-negative
after shifting by `N`. For empty `J` we return `0`. -/
noncomputable def shiftAmount (J : Finset ℤ) : ℕ :=
  if h : J.Nonempty then (-(J.min' h)).toNat else 0

/-- For any sufficient shift `N`, every `j ∈ J` satisfies `0 ≤ j + N`. -/
lemma zero_le_shiftAmount_add (J : Finset ℤ) {j : ℤ} (hj : j ∈ J) :
    (0 : ℤ) ≤ j + shiftAmount J := by
  classical
  have hJ : J.Nonempty := ⟨j, hj⟩
  unfold shiftAmount
  rw [dif_pos hJ]
  have hmin : J.min' hJ ≤ j := J.min'_le _ hj
  by_cases hpos : 0 ≤ -(J.min' hJ)
  · have hcoe : ((-(J.min' hJ)).toNat : ℤ) = -(J.min' hJ) := Int.toNat_of_nonneg hpos
    rw [hcoe]; linarith
  · -- `-J.min' hJ < 0`, i.e. `J.min' hJ > 0`; then `j ≥ 0` and toNat ≥ 0.
    have hcoe : (0 : ℤ) ≤ ((-(J.min' hJ)).toNat : ℤ) := Int.natCast_nonneg _
    have h0 : 0 ≤ j := le_trans (by linarith) hmin
    linarith

/-- The joint observation at `ℤ`-indexed times, parametrized by a shift `N`:
`obsZ μ p N J ω j := X (T^[(j + N).toNat] ω)`. When `N ≥ shiftAmount J`, this
records the genuine block `(X_{j₀+N}, X_{j₁+N}, …)` evaluated at the points of `J`. -/
noncomputable def obsZ (N : ℕ) (J : Finset ℤ) : Ω → (∀ _ : J, α) :=
  fun ω j => p.obs (j.1 + N).toNat ω

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The joint observation `obsZ μ p N J` is measurable. -/
lemma measurable_obsZ (N : ℕ) (J : Finset ℤ) : Measurable (obsZ μ p N J) := by
  refine measurable_pi_iff.mpr (fun j => ?_)
  exact p.measurable_obs _

/-- The finite-dimensional marginal of the (yet-to-be-built) two-sided extension at
the index set `J : Finset ℤ`. Defined as the law of `obsZ` at the canonical shift
`shiftAmount J`; the value is independent of the chosen shift by stationarity
(`shiftedMarginal_eq_of_shift`). -/
noncomputable def shiftedMarginal (J : Finset ℤ) : Measure (∀ _ : J, α) :=
  μ.map (obsZ μ p (shiftAmount J) J)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- For two non-negative shifts `N₁ ≤ N₂` both valid for `J`, the joint observation
under `N₂` is the same as under `N₁` precomposed with `T^[N₂ - N₁]`. -/
lemma obsZ_succ_shift {J : Finset ℤ} (N k : ℕ)
    (hN : ∀ j ∈ J, (0 : ℤ) ≤ j + N) :
    obsZ μ p (N + k) J = (obsZ μ p N J) ∘ p.T^[k] := by
  funext ω j
  simp only [obsZ, Function.comp_apply, StationaryProcess.obs]
  -- Goal: X (T^[(j.1 + (N + k)).toNat] ω) = X (T^[(j.1 + N).toNat] (T^[k] ω))
  have hjN : (0 : ℤ) ≤ j.1 + N := hN _ j.2
  have hjNk : (0 : ℤ) ≤ j.1 + ((N + k : ℕ) : ℤ) := by
    have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
    have : ((N + k : ℕ) : ℤ) = (N : ℤ) + k := by push_cast; ring
    rw [this]; linarith
  -- `(j.1 + (N+k)).toNat = (j.1 + N).toNat + k`
  have htoNat : ((j.1 + ((N + k : ℕ) : ℤ)).toNat) = (j.1 + N).toNat + k := by
    have h1 : ((j.1 + N).toNat : ℤ) = j.1 + N := Int.toNat_of_nonneg hjN
    have h2 : ((j.1 + ((N + k : ℕ) : ℤ)).toNat : ℤ) = j.1 + ((N + k : ℕ) : ℤ) :=
      Int.toNat_of_nonneg hjNk
    -- Lift through ℤ
    have : ((((j.1 + N).toNat + k : ℕ)) : ℤ) = j.1 + ((N + k : ℕ) : ℤ) := by
      push_cast; linarith [h1]
    have h3 : ((j.1 + ((N + k : ℕ) : ℤ)).toNat : ℤ)
        = (((j.1 + N).toNat + k : ℕ) : ℤ) := by rw [h2, ← this]
    exact_mod_cast h3
  -- T^[(j.1 + N + k).toNat] ω = T^[(j.1 + N).toNat + k] ω
  -- We want T^[a + k] ω = T^[a] (T^[k] ω), which is `Function.iterate_add_apply T a k ω`.
  rw [htoNat, Function.iterate_add_apply p.T]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- **N-invariance of `obsZ` under push-forward** (stationarity, single-shift step).
For any valid shift `N`, pushing forward by `obsZ μ p (N + k) J` agrees with pushing
forward by `obsZ μ p N J`. -/
lemma map_obsZ_succ {J : Finset ℤ} (N k : ℕ) (hN : ∀ j ∈ J, (0 : ℤ) ≤ j + N) :
    μ.map (obsZ μ p (N + k) J) = μ.map (obsZ μ p N J) := by
  rw [obsZ_succ_shift μ p N k hN,
      ← Measure.map_map (measurable_obsZ μ p N J) (p.measurable_iterate k),
      (p.measurePreserving.iterate k).map_eq]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- **N-invariance of the pushforward law** (general form): any two valid shifts
yield the same pushforward measure. -/
theorem map_obsZ_eq_of_shift {J : Finset ℤ} (N₁ N₂ : ℕ)
    (h₁ : ∀ j ∈ J, (0 : ℤ) ≤ j + N₁)
    (h₂ : ∀ j ∈ J, (0 : ℤ) ≤ j + N₂) :
    μ.map (obsZ μ p N₁ J) = μ.map (obsZ μ p N₂ J) := by
  -- WLOG via the symmetric chain
  rcases le_total N₁ N₂ with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (map_obsZ_succ μ p N₁ k h₁).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact map_obsZ_succ μ p N₂ k h₂

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The shifted marginal coincides with the pushforward of `obsZ` for any valid shift,
not just the canonical `shiftAmount J`. -/
@[entry_point]
theorem shiftedMarginal_eq_of_shift (J : Finset ℤ) (N : ℕ)
    (hN : ∀ j ∈ J, (0 : ℤ) ≤ j + N) :
    shiftedMarginal μ p J = μ.map (obsZ μ p N J) := by
  unfold shiftedMarginal
  exact map_obsZ_eq_of_shift μ p _ _ (fun j hj => zero_le_shiftAmount_add J hj) hN

/-- Each shifted marginal is a probability measure (pushforward of a probability
measure under a measurable map). -/
instance instIsProbabilityMeasure_shiftedMarginal (J : Finset ℤ) :
    IsProbabilityMeasure (shiftedMarginal μ p J) := by
  unfold shiftedMarginal
  exact Measure.isProbabilityMeasure_map (measurable_obsZ μ p _ J).aemeasurable

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- **Projective consistency**: for `J ⊆ I`, restricting `shiftedMarginal μ p I` along
the inclusion gives `shiftedMarginal μ p J`. -/
@[entry_point]
theorem isProjectiveMeasureFamily_shiftedMarginal :
    IsProjectiveMeasureFamily
      (α := fun _ : ℤ => α) (shiftedMarginal μ p) := by
  intro I J hJI
  classical
  -- Pick a shift `N` that works for `I` (and hence for `J ⊆ I`).
  -- Use the larger of `shiftAmount I` and `shiftAmount J` to be safe; in fact
  -- `shiftAmount I` alone works since `J ⊆ I` means `J.min' ≥ I.min'`.
  by_cases hI : I.Nonempty
  · set N := shiftAmount I with hN_def
    have hN_I : ∀ i ∈ I, (0 : ℤ) ≤ i + N :=
      fun i hi => zero_le_shiftAmount_add I hi
    have hN_J : ∀ j ∈ J, (0 : ℤ) ≤ j + N :=
      fun j hj => hN_I j (hJI hj)
    -- Rewrite both sides via the explicit shift `N`.
    rw [shiftedMarginal_eq_of_shift μ p I N hN_I,
        shiftedMarginal_eq_of_shift μ p J N hN_J]
    -- Now: `μ.map (obsZ N J) = (μ.map (obsZ N I)).map (Finset.restrict₂ hJI)`.
    -- The key observation: `obsZ N J = Finset.restrict₂ hJI ∘ obsZ N I`.
    have h_comp :
        obsZ μ p N J
          = (Finset.restrict₂ (π := fun _ : ℤ => α) hJI) ∘ (obsZ μ p N I) := by
      funext ω j; rfl
    rw [h_comp,
        Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : ℤ => α) hJI)
          (measurable_obsZ μ p N I)]
  · -- I is empty, so J = ∅ too.
    have hJ_empty : J = ∅ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hI
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      have := hJI hj
      rw [hI] at this
      exact Finset.notMem_empty _ this
    subst hJ_empty
    -- I = ∅, J = ∅. The empty inclusion is the identity (uniquely typed).
    have hI_empty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    subst hI_empty
    -- Now `Finset.restrict₂ hJI : (∀ i : (∅ : Finset ℤ), α) → (∀ j : (∅ : Finset ℤ), α)`.
    -- Both shiftedMarginal `∅` are probability measures on a subsingleton type.
    -- It suffices to show they're both probability measures on the unique singleton.
    have : Finset.restrict₂ (π := fun _ : ℤ => α) hJI = id := by
      funext f j
      exact (Finset.notMem_empty _ j.2).elim
    rw [this, Measure.map_id]

end ShiftedMarginal

/-! ## Projective consistency + σ-additivity -/

section StationaryContent

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)

/-- The `AddContent` on measurable cylinders of `ℤ → α` induced by the shifted
finite-dimensional marginals. -/
noncomputable def stationaryContent :
    AddContent ℝ≥0∞ (measurableCylinders (fun _ : ℤ => α)) :=
  projectiveFamilyContent (isProjectiveMeasureFamily_shiftedMarginal μ p)

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- σ-additivity input: for any antitone sequence of measurable cylinders with empty
intersection, the content tends to 0.

The proof uses the **finite-type Cantor argument**: equipping `α` with the discrete
topology turns `ℤ → α` into a compact Hausdorff space (`Pi.compactSpace` from finite
discrete factors), every cylinder `cylinder I S` is closed (preimage of a finite, hence
closed, set), and every closed subset of a compact space is compact. Cantor's
intersection theorem for sequences (`IsCompact.nonempty_iInter_of_sequence_…`) then
gives `∃ N, A N = ∅`, after which `stationaryContent (A n) = 0` for `n ≥ N`. -/
theorem stationaryContent_tendsto_zero
    {A : ℕ → Set (∀ _ : ℤ, α)}
    (A_mem : ∀ n, A n ∈ measurableCylinders (fun _ : ℤ => α))
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n => stationaryContent μ p (A n)) atTop (𝓝 0) := by
  classical
  -- Equip `α` with the discrete topology; `ℤ → α` becomes compact Hausdorff.
  letI : TopologicalSpace α := ⊥
  haveI : DiscreteTopology α := ⟨rfl⟩
  -- (Pi instances ensure ℤ → α is a topological space; finite + discrete ⇒ compact.)
  -- Extract a cylinder representation for each `A n`.
  have A_cyl : ∀ n, ∃ (s : Finset ℤ) (S : Set (∀ _ : s, α)),
      MeasurableSet S ∧ A n = cylinder s S := by
    intro n; exact (mem_measurableCylinders (A n)).1 (A_mem n)
  choose s S _hS A_eq using A_cyl
  -- The base set `S n` is a finite subset of the finite type `∀ i : s n, α`.
  have hS_finite : ∀ n, (S n).Finite := fun n => Set.toFinite (S n)
  -- Finite subsets of a (discrete, hence T1) space are closed.
  have hS_closed : ∀ n, IsClosed (S n) := fun n => (hS_finite n).isClosed
  -- The cylinder is the preimage of `S n` under the continuous restriction map.
  have hAn_closed : ∀ n, IsClosed (A n) := by
    intro n
    rw [A_eq n]
    exact (hS_closed n).preimage (s n).continuous_restrict
  -- ℤ → α is a compact space (product of compact discrete finite α).
  have hAn_compact : ∀ n, IsCompact (A n) := fun n => (hAn_closed n).isCompact
  -- Cantor: ⋂ A n = ∅ + each A n is compact + closed + antitone ⇒ some A N = ∅.
  -- Apply the contrapositive of `IsCompact.nonempty_iInter_of_sequence_…`.
  have hN : ∃ N, A N = ∅ := by
    by_contra h
    push Not at h
    have hA_ne : ∀ n, (A n).Nonempty := h
    have hA_dec : ∀ n, A (n + 1) ⊆ A n := fun n => A_anti (Nat.le_succ n)
    have hnon : (⋂ n, A n).Nonempty :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        A hA_dec hA_ne (hAn_compact 0) hAn_closed
    rw [A_inter] at hnon
    exact hnon.ne_empty rfl
  obtain ⟨N, hAN⟩ := hN
  -- For n ≥ N, A n ⊆ A N = ∅, hence A n = ∅, hence content is 0.
  apply Tendsto.congr' (f₁ := fun _ => (0 : ℝ≥0∞)) _ tendsto_const_nhds
  rw [EventuallyEq, eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hAn_empty : A n = ∅ := Set.subset_empty_iff.mp (hAN ▸ A_anti hn)
  rw [hAn_empty]
  exact (addContent_empty (m := stationaryContent μ p)).symm

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `stationaryContent` is σ-subadditive (from `tendsto_zero`). -/
theorem stationaryContent_isSigmaSubadditive :
    (stationaryContent μ p).IsSigmaSubadditive := by
  -- Mirrors `Mathlib/Probability/ProductMeasure.lean : isSigmaSubadditive_piContent`.
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' => ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (stationaryContent μ p)
    (fun _ _ => projectiveFamilyContent_ne_top _)
    (fun _ hs_mem hs_anti hs_inter =>
      stationaryContent_tendsto_zero μ p hs_mem hs_anti hs_inter)
    hf hf_Union hf'

end StationaryContent

/-! ## Carathéodory extension `μZ` -/

section MuZ

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)

/-- The two-sided extension `μ_ℤ : Measure (ℤ → α)` obtained from the stationary
process `(Ω, T, μ, X)` by Carathéodory extension of the `stationaryContent`. -/
@[entry_point]
noncomputable def μZ : Measure (∀ _ : ℤ, α) :=
  (stationaryContent μ p).measure
    isSetSemiring_measurableCylinders
    (by rw [generateFrom_measurableCylinders])
    (stationaryContent_isSigmaSubadditive μ p)

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- On measurable cylinders, `μZ` agrees with `shiftedMarginal`. -/
@[entry_point]
theorem μZ_cylinder {I : Finset ℤ} {S : Set (∀ _ : I, α)} (hS : MeasurableSet S) :
    μZ μ p (cylinder I S) = shiftedMarginal μ p I S := by
  -- μZ on a cylinder = stationaryContent on that cylinder
  --                  = projectiveFamilyFun applied to the cylinder
  --                  = shiftedMarginal μ p I S.
  rw [μZ, AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
    (cylinder_mem_measurableCylinders _ _ hS)]
  exact projectiveFamilyContent_cylinder
    (isProjectiveMeasureFamily_shiftedMarginal μ p) hS

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `μZ` is the projective limit of the shifted marginals. -/
@[entry_point]
theorem isProjectiveLimit_μZ :
    IsProjectiveLimit (μZ μ p) (shiftedMarginal μ p) := by
  intro I
  ext s hs
  -- `(μZ).map (I.restrict) s = μZ ((I.restrict)⁻¹' s) = μZ (cylinder I s) = shiftedMarginal s`.
  rw [Measure.map_apply (Finset.measurable_restrict I) hs, ← cylinder, μZ_cylinder μ p hs]

/-- `μZ` is a probability measure. -/
instance instIsProbabilityMeasure_μZ : IsProbabilityMeasure (μZ μ p) := by
  -- μZ univ = μZ (cylinder ∅ univ) = shiftedMarginal μ p ∅ univ = 1.
  constructor
  rw [show (Set.univ : Set (∀ _ : ℤ, α)) = cylinder (∅ : Finset ℤ) Set.univ from
        (cylinder_univ ∅).symm,
      μZ_cylinder μ p MeasurableSet.univ]
  exact measure_univ

end MuZ

/-! ## Shift `MeasurePreserving` + `Ergodic` -/

section Shift

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)

/-- The two-sided shift `σ : (ℤ → α) → (ℤ → α)`, `σ x i := x (i + 1)`. -/
@[entry_point]
def shiftZ : (∀ _ : ℤ, α) → (∀ _ : ℤ, α) := fun x i => x (i + 1)

/-- The inverse shift, `σ⁻¹ x i := x (i - 1)`. -/
def shiftZSymm : (∀ _ : ℤ, α) → (∀ _ : ℤ, α) := fun x i => x (i - 1)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The shift is measurable. -/
theorem measurable_shiftZ : Measurable (shiftZ : (∀ _ : ℤ, α) → _) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply (i + 1))

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The inverse shift is measurable. -/
@[entry_point]
theorem measurable_shiftZSymm : Measurable (shiftZSymm : (∀ _ : ℤ, α) → _) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply (i - 1))

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The two-sided shift preserves `μZ`.

Proof outline: both `μZ μ p` and `(μZ μ p).map shiftZ` are projective limits of
the family `shiftedMarginal μ p` of finite-dimensional marginals. By
`IsProjectiveLimit.unique` they are equal. The projective property of the
pushforward reduces to the *shift-invariance of the marginals*: for any
`I : Finset ℤ`, the marginal at `I + 1` (relabeled through the bijection `· + 1`)
equals the marginal at `I`, which is exactly `shiftedMarginal_eq_of_shift`. -/
@[entry_point]
theorem measurePreserving_shiftZ :
    MeasurePreserving (shiftZ : (∀ _ : ℤ, α) → _) (μZ μ p) (μZ μ p) := by
  classical
  refine ⟨measurable_shiftZ, ?_⟩
  -- The pushforward by `shiftZ` is also a projective limit of `shiftedMarginal`.
  have hlimit : IsProjectiveLimit ((μZ μ p).map shiftZ) (shiftedMarginal μ p) := by
    intro I
    -- Define `I_shift := I.map ⟨(· + 1), …⟩` and the natural bijection
    -- `e : (∀ _ : I_shift, α) → (∀ _ : I, α)`, `e f j := f ⟨j.1 + 1, _⟩`.
    set I_shift : Finset ℤ :=
      I.map ⟨fun i => i + 1, fun a b h => by linarith⟩ with hI_shift
    have hmem_shift : ∀ j : I, j.1 + 1 ∈ I_shift := by
      intro j; rw [hI_shift, Finset.mem_map]
      exact ⟨j.1, j.2, rfl⟩
    set e : (∀ _ : I_shift, α) → (∀ _ : I, α) :=
      fun f j => f ⟨j.1 + 1, hmem_shift j⟩ with he_def
    have hmeas_e : Measurable e :=
      measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
    -- Rewrite the composition: `I.restrict ∘ shiftZ = e ∘ I_shift.restrict`.
    have hcomp : I.restrict ∘ (shiftZ : (∀ _ : ℤ, α) → _) = e ∘ I_shift.restrict := by
      funext x j
      show shiftZ x j.1 = (I_shift.restrict x) ⟨j.1 + 1, hmem_shift j⟩
      rfl
    -- Push everything through.
    calc ((μZ μ p).map shiftZ).map I.restrict
        = (μZ μ p).map (I.restrict ∘ shiftZ) := by
            rw [← Measure.map_map (Finset.measurable_restrict I) measurable_shiftZ]
      _ = (μZ μ p).map (e ∘ I_shift.restrict) := by rw [hcomp]
      _ = ((μZ μ p).map I_shift.restrict).map e := by
            rw [Measure.map_map hmeas_e (Finset.measurable_restrict I_shift)]
      _ = (shiftedMarginal μ p I_shift).map e := by
            rw [isProjectiveLimit_μZ μ p I_shift]
      _ = shiftedMarginal μ p I := ?_
    -- Final step: shifted marginal at `I_shift` pushed through `e` recovers
    -- the marginal at `I`. Pick a common shift `N := shiftAmount I` and use the
    -- N-independence of the pushforward to compute both sides via `obsZ`.
    -- Show `shiftedMarginal μ p I_shift = μ.map (obsZ μ p (shiftAmount I) I_shift)`
    have hN_shift : ∀ k ∈ I_shift, (0 : ℤ) ≤ k + shiftAmount I := by
      intro k hk
      rw [hI_shift, Finset.mem_map] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      have : (0 : ℤ) ≤ j + shiftAmount I := zero_le_shiftAmount_add I hj
      show (0 : ℤ) ≤ (j + 1) + shiftAmount I
      linarith
    have hN_I_succ : ∀ j ∈ I, (0 : ℤ) ≤ j + (shiftAmount I + 1) := by
      intro j hj
      have : (0 : ℤ) ≤ j + shiftAmount I := zero_le_shiftAmount_add I hj
      linarith
    rw [shiftedMarginal_eq_of_shift μ p I_shift (shiftAmount I) hN_shift,
        shiftedMarginal_eq_of_shift μ p I (shiftAmount I + 1) hN_I_succ]
    -- Now: `(μ.map (obsZ μ p (shiftAmount I) I_shift)).map e = μ.map (obsZ μ p (shiftAmount I + 1) I)`.
    rw [Measure.map_map hmeas_e (measurable_obsZ μ p _ I_shift)]
    congr 1
    funext ω
    funext j
    -- LHS at `j : I`: `e (obsZ N I_shift ω) j = obsZ N I_shift ω ⟨j.1+1, _⟩
    --                = p.obs (j.1 + 1 + N).toNat ω`
    -- RHS at `j : I`: `obsZ (N+1) I ω j = p.obs (j.1 + (N+1)).toNat ω`
    show p.obs ((j.1 + 1) + (shiftAmount I : ℤ)).toNat ω
        = p.obs (j.1 + ((shiftAmount I + 1 : ℕ) : ℤ)).toNat ω
    congr 2
    push_cast; ring
  -- Conclude via `IsProjectiveLimit.unique`.
  exact IsProjectiveLimit.unique hlimit (isProjectiveLimit_μZ μ p)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- `shiftZSymm` is the left-inverse of `shiftZ`. -/
@[entry_point]
theorem leftInverse_shiftZSymm :
    Function.LeftInverse (shiftZSymm (α := α)) shiftZ := by
  intro x; funext i; simp [shiftZ, shiftZSymm]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- `shiftZSymm` is the right-inverse of `shiftZ`. -/
@[entry_point]
theorem rightInverse_shiftZSymm :
    Function.RightInverse (shiftZSymm (α := α)) shiftZ := by
  intro x; funext i; simp [shiftZ, shiftZSymm]

end Shift

/-! ## Coupling with the one-sided side -/

section Coupling

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)

/-- The forward (one-sided) embedding `Ω → (ℕ → α)`, `ω ↦ (X (T^[i] ω))_i`. -/
@[entry_point]
def forwardEmbed : Ω → (∀ _ : ℕ, α) := fun ω i => p.obs i ω

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The forward embedding is measurable. -/
theorem measurable_forwardEmbed : Measurable (forwardEmbed (μ := μ) p) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  exact p.measurable_obs i

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The ℕ-projection of `μZ` agrees with the law of `forwardEmbed`.

Both sides are probability measures on `ℕ → α`. We verify equality on the
π-system of measurable cylinders using `MeasureTheory.ext_of_generate_finite`,
then compute each cylinder's measure: on the LHS via `μZ_cylinder` after
rewriting the preimage as a ℤ-cylinder, and on the RHS via the definition
of `forwardEmbed` together with `shiftedMarginal_eq_of_shift` at shift `0`. -/
@[entry_point]
theorem μZ_nat_proj_eq :
    Measure.map (fun x : (∀ _ : ℤ, α) => fun i : ℕ => x (i : ℤ)) (μZ μ p)
      = Measure.map (forwardEmbed (μ := μ) p) μ := by
  classical
  -- Abbreviate the ℕ-projection map.
  set natProj : (∀ _ : ℤ, α) → (∀ _ : ℕ, α) :=
    fun x i => x (i : ℤ) with hnatProj
  have hmeas_natProj : Measurable natProj :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (i : ℤ))
  -- Cast `ℕ → ℤ` is injective; use it to map `Finset ℕ → Finset ℤ`.
  have hcast_inj : Function.Injective (Nat.cast : ℕ → ℤ) := Nat.cast_injective
  -- Both LHS, RHS are probability measures; in particular finite.
  have hLHS_prob : IsProbabilityMeasure
      (Measure.map natProj (μZ μ p)) :=
    Measure.isProbabilityMeasure_map hmeas_natProj.aemeasurable
  -- Apply `ext_of_generate_finite` on `measurableCylinders (fun _ : ℕ => α)`.
  refine MeasureTheory.ext_of_generate_finite (measurableCylinders (fun _ : ℕ => α))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (fun s hs => ?_) ?_
  · -- Cylinder case.
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).mp hs
    -- Map `I` into ℤ.
    set I_ℤ : Finset ℤ := I.map ⟨Nat.cast, hcast_inj⟩ with hI_ℤ
    -- Bijection helper: each `j : I` corresponds to `⟨(j.1 : ℤ), _⟩ : I_ℤ`.
    have hmem : ∀ j : I, ((j.1 : ℕ) : ℤ) ∈ I_ℤ := by
      intro j; rw [hI_ℤ, Finset.mem_map]
      exact ⟨j.1, j.2, rfl⟩
    -- The bijection `bij : (∀ i : I_ℤ, α) → (∀ j : I, α)`.
    set bij : (∀ _ : I_ℤ, α) → (∀ _ : I, α) :=
      fun f j => f ⟨((j.1 : ℕ) : ℤ), hmem j⟩ with hbij_def
    have hmeas_bij : Measurable bij :=
      measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
    -- Preimage rewrite: `natProj⁻¹ (cylinder I S) = cylinder I_ℤ (bij⁻¹ S)`.
    have hpre : natProj ⁻¹' cylinder I S = cylinder I_ℤ (bij ⁻¹' S) := by
      ext x
      change (I.restrict (natProj x)) ∈ S ↔ (I_ℤ.restrict x) ∈ bij ⁻¹' S
      rfl
    -- LHS evaluation.
    rw [Measure.map_apply hmeas_natProj (MeasurableSet.cylinder I hS),
        hpre,
        μZ_cylinder μ p (hmeas_bij hS)]
    -- Now: `shiftedMarginal μ p I_ℤ (bij⁻¹ S) = (Measure.map forwardEmbed μ) (cylinder I S)`.
    -- All elements of `I_ℤ` are non-negative, so we can take shift `N=0`.
    have hI_ℤ_nonneg : ∀ i ∈ I_ℤ, (0 : ℤ) ≤ i + (0 : ℕ) := by
      intro i hi
      rw [hI_ℤ, Finset.mem_map] at hi
      obtain ⟨n, _, rfl⟩ := hi
      simp [Function.Embedding.coeFn_mk]
    rw [shiftedMarginal_eq_of_shift μ p I_ℤ 0 hI_ℤ_nonneg,
        Measure.map_apply (measurable_obsZ μ p 0 I_ℤ) (hmeas_bij hS)]
    rw [Measure.map_apply (measurable_forwardEmbed (μ := μ) p)
          (MeasurableSet.cylinder I hS)]
    -- Identify the two preimages on `Ω`: both compute to the same set.
    apply congrArg
    ext ω
    -- Goal: ω ∈ (bij ∘ obsZ ...)⁻¹ S ↔ ω ∈ (forwardEmbed)⁻¹ (cylinder I S)
    have hcoerce : ∀ j : I, ((((j.1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)).toNat) = j.1 := by
      intro j; simp
    have hfun : bij (obsZ μ p 0 I_ℤ ω) = I.restrict (forwardEmbed (μ := μ) p ω) := by
      funext j
      simp only [hbij_def, obsZ, forwardEmbed, Finset.restrict]
      rw [show ((((j.1 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)).toNat) = j.1 from hcoerce j]
    simp only [Set.mem_preimage, hfun, mem_cylinder]
  · -- Equality on univ.
    rw [Measure.map_apply hmeas_natProj MeasurableSet.univ,
        Measure.map_apply (measurable_forwardEmbed (μ := μ) p) MeasurableSet.univ]
    simp

omit [DecidableEq α] [Nonempty α] in
/-- Block cylinder under `μZ` equals the block-law on the one-sided side. -/
@[entry_point]
theorem μZ_block_cylinder_eq (n : ℕ) (s : Fin n → α) :
    μZ μ p { x | ∀ i : Fin n, x ((i : ℕ) : ℤ) = s i }
      = (μ.map (p.blockRV n)) {s} := by
  classical
  -- The set `{x | ∀ i : Fin n, x ((i : ℕ) : ℤ) = s i}` is a measurable cylinder on
  -- the finite index set `I_ℤ := (Finset.range n).map (Nat.cast embedding)`.
  -- We express it as a cylinder on `I_ℤ` with base equal to a singleton in
  -- the relabeled function space, then apply `μZ_cylinder` + `shiftedMarginal`.
  set I_ℤ : Finset ℤ :=
    (Finset.range n).map ⟨Nat.cast, Nat.cast_injective⟩ with hI_ℤ
  -- Bijection: each `j : I_ℤ` corresponds to some `i : Fin n` with `i.1 = j.1.toNat`.
  -- Define `S_ℤ : Set (∀ _ : I_ℤ, α)` = `{f | ∀ i : Fin n, f ⟨(i : ℤ), _⟩ = s i}`.
  have hmem : ∀ i : Fin n, ((i : ℕ) : ℤ) ∈ I_ℤ := by
    intro i; rw [hI_ℤ, Finset.mem_map]
    exact ⟨i, by simp [Finset.mem_range, i.2], rfl⟩
  set S_ℤ : Set (∀ _ : I_ℤ, α) :=
    {f | ∀ i : Fin n, f ⟨((i : ℕ) : ℤ), hmem i⟩ = s i} with hS_ℤ
  -- Measurability of S_ℤ: intersection of fiber-equality sets (`α` has
  -- `MeasurableSingletonClass`).
  have hS_ℤ_meas : MeasurableSet S_ℤ := by
    rw [hS_ℤ]
    have : {f : ∀ _ : I_ℤ, α | ∀ i : Fin n, f ⟨((i : ℕ) : ℤ), hmem i⟩ = s i}
        = ⋂ i : Fin n, {f | f ⟨((i : ℕ) : ℤ), hmem i⟩ = s i} := by
      ext f; simp
    rw [this]
    refine MeasurableSet.iInter (fun i => ?_)
    have hmeas : Measurable (fun f : ∀ _ : I_ℤ, α => f ⟨((i : ℕ) : ℤ), hmem i⟩) :=
      measurable_pi_apply _
    have hpre : {f : ∀ _ : I_ℤ, α | f ⟨((i : ℕ) : ℤ), hmem i⟩ = s i}
        = (fun f : ∀ _ : I_ℤ, α => f ⟨((i : ℕ) : ℤ), hmem i⟩) ⁻¹' {s i} := rfl
    rw [hpre]
    exact hmeas (measurableSet_singleton (s i))
  -- The set equality.
  have hset : {x : (∀ _ : ℤ, α) | ∀ i : Fin n, x ((i : ℕ) : ℤ) = s i}
      = cylinder I_ℤ S_ℤ := by
    ext x
    simp only [Set.mem_setOf_eq, cylinder, Set.mem_preimage, Finset.restrict, hS_ℤ]
  rw [hset, μZ_cylinder μ p hS_ℤ_meas]
  -- All elements of `I_ℤ` are non-negative; use shift `N = 0`.
  have hI_ℤ_nonneg : ∀ i ∈ I_ℤ, (0 : ℤ) ≤ i + (0 : ℕ) := by
    intro i hi
    rw [hI_ℤ, Finset.mem_map] at hi
    obtain ⟨k, _, rfl⟩ := hi
    simp [Function.Embedding.coeFn_mk]
  rw [shiftedMarginal_eq_of_shift μ p I_ℤ 0 hI_ℤ_nonneg]
  rw [Measure.map_apply (measurable_obsZ μ p 0 I_ℤ) hS_ℤ_meas]
  rw [Measure.map_apply (p.measurable_blockRV n) (measurableSet_singleton s)]
  -- Identify preimages on Ω.
  congr 1
  ext ω
  simp only [Set.mem_preimage, hS_ℤ, Set.mem_setOf_eq, obsZ,
    Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    have := h i
    -- `p.obs ((((i:ℕ):ℤ) + 0).toNat) ω = s i`
    have hcast : ((((i : ℕ) : ℤ) + ((0 : ℕ) : ℤ)).toNat) = i.1 := by simp
    rw [hcast] at this
    exact this
  · intro h i
    have hcast : ((((i : ℕ) : ℤ) + ((0 : ℕ) : ℤ)).toNat) = i.1 := by simp
    rw [hcast]
    exact congrFun h i

end Coupling

/-! ## `ergodic_shiftZ`

Two-sided shift ergodicity via **cylinder approximation + ℕ-factor transfer**.

For a `shiftZ`-invariant measurable set `A ⊆ (ℤ → α)`:

1. Approximate `A` by a finite cylinder `t` (over some `F ⊆ ℤ`) up to ε in symmetric
   difference — via `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing`
   on `measurableCylinders` (a set ring generating the product σ-algebra).
2. For `k` large enough that `F + k ⊆ ℕ`, the shifted cylinder
   `shiftZ^[k]⁻¹' t` is a cylinder over a nonnegative index set,
   hence lies in `cylinderEvents {i : ℤ | 0 ≤ i}`.
3. By measure-preservation of `shiftZ^[k]` and shift-invariance of `A`,
   `μZ(A Δ shiftZ^[k]⁻¹' t) = μZ(A Δ t) < ε`, so `A` is approximable to within
   any ε by sets in `cylinderEvents {i : ℤ | 0 ≤ i}`.
4. Hence `A` is `μZ`-a.e. equal to some `A' = natProj⁻¹' B` for measurable `B`,
   and `B` is `shiftN`-invariant mod-null on `μ.map forwardEmbed`.
5. `(ℕ → α, shiftN, μ.map forwardEmbed)` is ergodic (forward
   `ergodic_of_ergodic_semiconj` from `(Ω, T, μ)` via `forwardEmbed`).
6. Conclude `μZ(A) = μN(B) ∈ {0, 1}`.
-/

section Ergodicity

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)

/-- The one-sided (`ℕ`-indexed) shift `σ_ℕ : (ℕ → α) → (ℕ → α)`, `σ_ℕ y i := y (i+1)`. -/
def shiftN : (∀ _ : ℕ, α) → (∀ _ : ℕ, α) := fun y i => y (i + 1)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The forward shift on `ℕ → α` is measurable. -/
theorem measurable_shiftN : Measurable (shiftN : (∀ _ : ℕ, α) → _) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply (i + 1))

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The forward embedding semiconjugates `T` and `shiftN`. -/
theorem forwardEmbed_semiconj :
    Function.Semiconj (forwardEmbed (μ := μ) p) p.T shiftN := by
  intro ω
  funext i
  show p.obs i (p.T ω) = p.obs (i + 1) ω
  simp only [StationaryProcess.obs, Function.comp_apply, ← Function.iterate_succ_apply]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The ℕ-projection `natProj : (ℤ → α) → (ℕ → α)`, `natProj x i := x (i : ℤ)`. -/
def natProj : (∀ _ : ℤ, α) → (∀ _ : ℕ, α) := fun x i => x (i : ℤ)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `natProj` is measurable. -/
theorem measurable_natProj : Measurable (natProj (α := α)) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply (i : ℤ))

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- `natProj` semiconjugates `shiftZ` and `shiftN`. -/
theorem natProj_semiconj :
    Function.Semiconj (natProj (α := α)) shiftZ shiftN := by
  intro x
  funext i
  show shiftZ x (i : ℤ) = natProj x (i + 1)
  show x ((i : ℤ) + 1) = x (((i + 1 : ℕ) : ℤ))
  push_cast
  rfl

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- `natProj` is measure-preserving from `μZ` to `μ.map forwardEmbed`. -/
theorem measurePreserving_natProj :
    MeasurePreserving (natProj (α := α)) (μZ μ p) (μ.map (forwardEmbed (μ := μ) p)) := by
  refine ⟨measurable_natProj, ?_⟩
  exact μZ_nat_proj_eq μ p

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- `forwardEmbed` is measure-preserving from `μ` to its pushforward. -/
@[entry_point]
theorem measurePreserving_forwardEmbed :
    MeasurePreserving (forwardEmbed (μ := μ) p) μ (μ.map (forwardEmbed (μ := μ) p)) :=
  ⟨measurable_forwardEmbed (μ := μ) p, rfl⟩

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The forward shift on `(ℕ → α, μ.map forwardEmbed)` is ergodic when the underlying
process is ergodic. Direct application of `ergodic_of_ergodic_semiconj` with
`forwardEmbed` as the measure-preserving semiconjugacy from `(Ω, T, μ)`. -/
@[entry_point]
theorem ergodic_shiftN (p : ErgodicProcess μ α) :
    Ergodic (shiftN : (∀ _ : ℕ, α) → _) (μ.map (forwardEmbed (μ := μ) p.toStationaryProcess)) :=
  (measurePreserving_forwardEmbed μ p.toStationaryProcess).ergodic_of_ergodic_semiconj
    p.ergodic measurable_shiftN (forwardEmbed_semiconj μ p.toStationaryProcess)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [IsProbabilityMeasure μ] in
/-- `shiftZ` iterated `k` times: `shiftZ^[k] x i = x (i + k)`. -/
lemma shiftZ_iterate_apply (k : ℕ) (x : ∀ _ : ℤ, α) (i : ℤ) :
    (shiftZ^[k] x) i = x (i + k) := by
  induction k generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show (shiftZ^[n] x) (i + 1) = x (i + ((n + 1 : ℕ) : ℤ))
    rw [ih]
    congr 1
    push_cast
    ring

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- Preimage of a measurable cylinder over `F` under `shiftZ^[k]` is a measurable
cylinder over `F + k = F.image (· + k)`. -/
lemma shiftZ_iterate_preimage_cylinder (k : ℕ) (F : Finset ℤ)
    {S : Set (∀ _ : F, α)} (hS : MeasurableSet S) :
    ∃ S' : Set (∀ _ : F.image (fun j : ℤ => j + (k : ℤ)), α),
      MeasurableSet S' ∧
      shiftZ^[k] ⁻¹' (cylinder F S)
        = cylinder (F.image (fun j : ℤ => j + (k : ℤ))) S' := by
  classical
  set F' : Finset ℤ := F.image (fun j : ℤ => j + (k : ℤ)) with hF'
  have hbij_mem : ∀ j : F, j.1 + (k : ℤ) ∈ F' := by
    intro j
    rw [hF', Finset.mem_image]
    exact ⟨j.1, j.2, rfl⟩
  set ξ : (∀ _ : F', α) → (∀ _ : F, α) :=
    fun f j => f ⟨j.1 + (k : ℤ), hbij_mem j⟩ with hξ_def
  have hmeas_ξ : Measurable ξ :=
    measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
  refine ⟨ξ ⁻¹' S, hmeas_ξ hS, ?_⟩
  ext x
  show (F.restrict (shiftZ^[k] x)) ∈ S ↔ (F'.restrict x) ∈ ξ ⁻¹' S
  simp only [Set.mem_preimage]
  have h_eq : F.restrict (shiftZ^[k] x) = ξ (F'.restrict x) := by
    funext j
    show (shiftZ^[k] x) j.1 = (F'.restrict x) ⟨j.1 + (k : ℤ), hbij_mem j⟩
    rw [shiftZ_iterate_apply]
    rfl
  rw [h_eq]

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- Preimage under `shiftZ^[k]` preserves measurable cylinders: the preimage of
a `measurableCylinders` element is again in `measurableCylinders`. -/
@[entry_point]
lemma shiftZ_iterate_preimage_mem_measurableCylinders (k : ℕ)
    {t : Set (∀ _ : ℤ, α)} (ht : t ∈ measurableCylinders (fun _ : ℤ => α)) :
    shiftZ^[k] ⁻¹' t ∈ measurableCylinders (fun _ : ℤ => α) := by
  obtain ⟨F, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht
  obtain ⟨S', hS', heq⟩ := shiftZ_iterate_preimage_cylinder (α := α) k F hS
  rw [heq]
  exact cylinder_mem_measurableCylinders _ _ hS'

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- After shifting by `k ≥ -F.min` (when `F` is nonempty), the cylinder lies
in `cylinderEvents {i : ℤ | 0 ≤ i}` (the positive-index σ-algebra). The witness
index set is `F.image (· + k)`, all of whose elements are ≥ 0. -/
lemma shiftZ_iterate_preimage_cylinder_in_pos
    {F : Finset ℤ} {S : Set (∀ _ : F, α)} (hS : MeasurableSet S)
    {k : ℕ} (hk : ∀ j ∈ F, (0 : ℤ) ≤ j + k) :
    MeasurableSet[cylinderEvents (X := fun _ : ℤ => α) {i : ℤ | 0 ≤ i}]
      (shiftZ^[k] ⁻¹' (cylinder F S)) := by
  classical
  obtain ⟨S', hS', heq⟩ := shiftZ_iterate_preimage_cylinder (α := α) k F hS
  rw [heq]
  -- The cylinder `cylinder (F.image (· + k)) S'` is measurable in
  -- `cylinderEvents {≥ 0}` because all indices in `F.image (· + k)` are ≥ 0.
  set F' : Finset ℤ := F.image (fun j : ℤ => j + (k : ℤ)) with hF'
  -- Show `(cylinder F' S')` is measurable in `cylinderEvents {≥ 0}`.
  -- A cylinder is `restrict F' ⁻¹' S'`. The map `restrict F'` is measurable in
  -- `cylinderEvents {≥ 0}` iff each coordinate `(· i)` for `i ∈ F'` is.
  have hF'_pos : ∀ i ∈ F', (0 : ℤ) ≤ i := by
    intro i hi
    rw [hF', Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    exact hk j hj
  -- The restriction `F'.restrict : (ℤ → α) → (∀ _ : F', α)` is measurable
  -- in cylinderEvents {≥ 0} via measurable_pi_iff (per coord).
  have hres :
      Measurable[cylinderEvents (X := fun _ : ℤ => α) {i : ℤ | 0 ≤ i}]
        (F'.restrict : (∀ _ : ℤ, α) → (∀ _ : F', α)) := by
    rw [@measurable_pi_iff]
    intro i
    -- The map `x ↦ x i.1` for `i.1 ∈ F'` (so `i.1 ≥ 0`) is `cylinderEvents {≥0}`-measurable.
    exact measurable_cylinderEvent_apply (Δ := {i : ℤ | 0 ≤ i}) (X := fun _ : ℤ => α)
      (hF'_pos i.1 i.2)
  exact hres hS'

end Ergodicity

section ErgodicityMain

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)

/-- The positive-index σ-algebra on `ℤ → α`, i.e., the σ-algebra of events
depending only on coordinates `i ≥ 0`. -/
@[reducible] def posSigma : MeasurableSpace (∀ _ : ℤ, α) :=
  cylinderEvents (X := fun _ : ℤ => α) {i : ℤ | 0 ≤ i}

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- `posSigma ≤ pi`. -/
@[entry_point]
lemma posSigma_le_pi : posSigma (α := α) ≤ MeasurableSpace.pi :=
  cylinderEvents_le_pi

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- `natProj` is measurable from `posSigma` to `pi` on `ℕ → α`. -/
@[entry_point]
lemma measurable_natProj_posSigma :
    Measurable[posSigma (α := α)] (natProj (α := α)) := by
  rw [@measurable_pi_iff]
  intro i
  -- `(natProj x) i = x (i : ℤ)`, with `(i : ℤ) ≥ 0`.
  show Measurable[posSigma (α := α)] (fun x : (∀ _ : ℤ, α) => x (i : ℤ))
  exact measurable_cylinderEvent_apply (Δ := {i : ℤ | 0 ≤ i}) (X := fun _ : ℤ => α)
    (Int.natCast_nonneg i)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- A `posSigma`-measurable set is the `natProj`-preimage of a measurable set
in `ℕ → α`. This is the **factoring lemma**: positive-index events factor through `natProj`. -/
lemma exists_preimage_natProj_of_posSigma
    {A : Set (∀ _ : ℤ, α)} (hA : MeasurableSet[posSigma (α := α)] A) :
    ∃ B : Set (∀ _ : ℕ, α), MeasurableSet B ∧ A = natProj ⁻¹' B := by
  -- The σ-algebra `posSigma` is generated by `(· i)⁻¹' (measurable in α)` for `i ≥ 0`.
  -- The map `natProj` is measurable from `posSigma` to `pi` (just shown).
  -- We need: `posSigma = MeasurableSpace.comap natProj MeasurableSpace.pi`.
  -- ⇒ direction: posSigma ≤ comap natProj pi, since natProj is posSigma → pi measurable.
  -- ⇐ direction: comap natProj pi ≤ posSigma. Each generator of comap is
  --   `natProj⁻¹ (measurable set in ℕ→α)` and we need it in posSigma.
  --   Suffices to check on a π-system generating pi on ℕ→α: take cylinders or coord generators.
  --   `natProj⁻¹ ((· i)⁻¹ S) = ((· i) ∘ natProj)⁻¹ S = (· (i : ℤ))⁻¹ S` for `S ⊆ α` measurable.
  --   Since `(i : ℤ) ≥ 0`, `(· (i : ℤ))⁻¹ S ∈ posSigma`. ✓
  -- Show: posSigma = comap natProj pi
  have h_comap : (MeasurableSpace.pi : MeasurableSpace (∀ _ : ℕ, α)).comap (natProj (α := α))
      = posSigma (α := α) := by
    -- Two-side antisymm.
    apply le_antisymm
    · -- comap pi ≤ posSigma
      -- pi on ℕ→α = ⨆ i, (m_α).comap (· i)
      -- So comap natProj pi = ⨆ i, comap natProj ((m_α).comap (· i))
      --                     = ⨆ i, (m_α).comap ((· i) ∘ natProj)
      --                     = ⨆ i, (m_α).comap (· (i:ℤ))
      -- And (m_α).comap (· (i:ℤ)) ≤ posSigma because (i:ℤ) ≥ 0.
      rw [show (MeasurableSpace.pi : MeasurableSpace (∀ _ : ℕ, α))
            = ⨆ i : ℕ, (inferInstance : MeasurableSpace α).comap (fun x : (∀ _ : ℕ, α) => x i) from rfl]
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le (fun i => ?_)
      rw [MeasurableSpace.comap_comp]
      -- Goal: (m_α).comap ((·i) ∘ natProj) ≤ posSigma
      -- (·i) ∘ natProj = fun x => natProj x i = fun x => x (i:ℤ)
      show ((inferInstance : MeasurableSpace α).comap
        (fun x : (∀ _ : ℤ, α) => natProj x i)) ≤ posSigma (α := α)
      show ((inferInstance : MeasurableSpace α).comap
        (fun x : (∀ _ : ℤ, α) => x (i : ℤ))) ≤ posSigma (α := α)
      -- This generator is in cylinderEvents {≥ 0} because (i:ℤ) ≥ 0.
      refine le_iSup₂ (f := fun (j : ℤ) (_ : j ∈ {i : ℤ | 0 ≤ i}) =>
        ((inferInstance : MeasurableSpace α).comap
          (fun x : (∀ _ : ℤ, α) => x j))) (i : ℤ) ?_
      exact Int.natCast_nonneg i
    · -- posSigma ≤ comap natProj pi
      -- posSigma = ⨆ i ∈ {≥ 0}, (m_α).comap (·i)
      -- We need each generator in comap natProj pi.
      refine iSup₂_le (fun i hi => ?_)
      -- Generator: (m_α).comap (· i) for i ≥ 0.
      -- (· i : ℤ → α → α). Since i ≥ 0, set j := i.toNat, then i = j.
      -- (·i) = (·(j:ℤ)) = (·j) ∘ natProj. So (m_α).comap (·i) = comap natProj ((m_α).comap (·j)).
      set j : ℕ := i.toNat with hj_def
      have hij : (j : ℤ) = i := Int.toNat_of_nonneg hi
      have h_eq : (fun x : (∀ _ : ℤ, α) => x i)
          = (fun y : (∀ _ : ℕ, α) => y j) ∘ natProj := by
        funext x
        show x i = natProj x j
        show x i = x (j : ℤ)
        rw [hij]
      rw [h_eq, ← MeasurableSpace.comap_comp]
      -- (m_α).comap ((·j) ∘ natProj) ≤ comap natProj pi
      refine MeasurableSpace.comap_mono ?_
      -- (m_α).comap (·j : ℕ→α → α) ≤ pi
      exact le_iSup (fun i : ℕ => ((inferInstance : MeasurableSpace α).comap
        (fun y : (∀ _ : ℕ, α) => y i))) j
  -- Now A ∈ posSigma = comap natProj pi means A = natProj⁻¹ B for some pi-measurable B.
  rw [← h_comap] at hA
  obtain ⟨B, hB, hB_eq⟩ := MeasurableSpace.measurableSet_comap.mp hA
  exact ⟨B, hB, hB_eq.symm⟩

end ErgodicityMain

section ErgodicityProof

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α)

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The two-sided shift is ergodic when the underlying process is ergodic.

By cylinder approximation + ℕ-factor transfer. For any
`shiftZ`-invariant measurable set `A`, approximate `A` to within ε by a
measurable cylinder, then shift to move the index set into the nonnegative
half-line. This yields a `posSigma`-measurable approximation, so `A` is μZ-a.e.
equal to a `posSigma`-measurable set `A' = natProj⁻¹ B`. By ergodicity of
`shiftN` on `μ.map forwardEmbed`, `B` is either null or co-null, hence so is `A`. -/
@[entry_point]
theorem ergodic_shiftZ :
    Ergodic (shiftZ : (∀ _ : ℤ, α) → _) (μZ μ p.toStationaryProcess) := by
  classical
  set q : StationaryProcess μ α := p.toStationaryProcess with hq_def
  set ν : Measure (∀ _ : ℕ, α) := μ.map (forwardEmbed (μ := μ) q) with hν_def
  have hν_prob : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_forwardEmbed (μ := μ) q).aemeasurable
  -- Ergodicity of shiftN on ν.
  have hN : Ergodic (shiftN : (∀ _ : ℕ, α) → _) ν := ergodic_shiftN μ p
  refine ⟨measurePreserving_shiftZ μ q, ?_⟩
  refine ⟨fun A hA hA_inv => ?_⟩
  -- Step 1: reduce `EventuallyConst A` to `μZ A = 0 ∨ μZ (A^c) = 0`.
  rw [eventuallyConst_set']
  -- Step 2: extract `A` to `posSigma`-measurable form modulo null.
  -- Cylinder approximation: for each ε > 0, find a cylinder t with μZ(A Δ t) < ε.
  -- Shift t to be in posSigma. Conclude A ∈ (posSigma) modulo null.
  -- Then use ergodicity of shiftN.
  -- We extract `A =ᵐ A'` for some `posSigma`-measurable `A'`.
  have h_approx_pos : ∃ A' : Set (∀ _ : ℤ, α),
      MeasurableSet[posSigma (α := α)] A' ∧ A =ᵐ[μZ μ q] A' := by
    -- Step (a): For each n, find a cylinder t_n with μZ(A Δ t_n) < 2^{-(n+1)}.
    have hC : ∃ D : Set (Set (∀ _ : ℤ, α)),
        D.Countable ∧ D ⊆ measurableCylinders (fun _ : ℤ => α) ∧
          μZ μ q (⋃₀ D)ᶜ = 0 := by
      refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
      · intro s hs
        rw [Set.mem_singleton_iff] at hs
        subst hs
        rw [← cylinder_univ (∅ : Finset ℤ)]
        exact cylinder_mem_measurableCylinders _ _ MeasurableSet.univ
      · simp
    -- For each n, use the symmDiff approximation lemma.
    have h_approx : ∀ n : ℕ, ∃ t ∈ measurableCylinders (fun _ : ℤ => α),
        μZ μ q (t ∆ A) < (1 / 2 : ℝ≥0∞) ^ (n + 1) := by
      intro n
      exact exists_measure_symmDiff_lt_of_generateFrom_isSetRing
        isSetRing_measurableCylinders hC generateFrom_measurableCylinders.symm hA
        (ENNReal.pow_pos (by norm_num) (n + 1))
    choose t ht_mem ht_lt using h_approx
    -- For each n, t n is a cylinder over some F_n.
    have ht_cyl : ∀ n, ∃ (F : Finset ℤ) (S : Set (∀ _ : F, α)),
        MeasurableSet S ∧ t n = cylinder F S := fun n =>
      (mem_measurableCylinders (t n)).mp (ht_mem n)
    choose F S hS_meas hF_eq using ht_cyl
    -- For each n, pick k_n large enough so F_n + k_n ⊆ ℕ.
    -- Set k_n := max(0, -min(F_n)).toNat if F_n nonempty, else 0.
    set k : ℕ → ℕ := fun n =>
      if h : (F n).Nonempty then (-(F n).min' h).toNat else 0 with hk_def
    -- For each n, all elements of F_n shifted by k_n are nonneg.
    have hk_nonneg : ∀ n, ∀ j ∈ F n, (0 : ℤ) ≤ j + (k n : ℤ) := by
      intro n j hj
      by_cases hF : (F n).Nonempty
      · simp only [hk_def, dif_pos hF]
        have hmin_le : (F n).min' hF ≤ j := (F n).min'_le _ hj
        by_cases hpos : 0 ≤ -(F n).min' hF
        · have hcoe : ((-((F n).min' hF)).toNat : ℤ) = -((F n).min' hF) :=
            Int.toNat_of_nonneg hpos
          rw [hcoe]; linarith
        · push Not at hpos
          have h0 : 0 ≤ j := le_trans (by linarith) hmin_le
          have : (0 : ℤ) ≤ ((-((F n).min' hF)).toNat : ℤ) := Int.natCast_nonneg _
          linarith
      · exact absurd ⟨j, hj⟩ hF
    -- Define s_n := shiftZ^[k_n]⁻¹' t_n. Cylinder + in posSigma.
    set s : ℕ → Set (∀ _ : ℤ, α) := fun n => shiftZ^[k n] ⁻¹' t n with hs_def
    have hs_pos : ∀ n, MeasurableSet[posSigma (α := α)] (s n) := by
      intro n
      rw [hs_def]
      simp only
      rw [hF_eq n]
      exact shiftZ_iterate_preimage_cylinder_in_pos (α := α) (hS_meas n) (hk_nonneg n)
    have hs_meas : ∀ n, MeasurableSet (s n) := fun n =>
      cylinderEvents_le_pi (s n) (hs_pos n)
    -- μZ(s_n Δ A) = μZ(t_n Δ A) (via measure preservation + shift invariance).
    have hs_diff : ∀ n, μZ μ q (s n ∆ A) < (1 / 2 : ℝ≥0∞) ^ (n + 1) := by
      intro n
      -- s_n Δ A = shiftZ^[k]⁻¹ t_n Δ shiftZ^[k]⁻¹ A (since A = shiftZ^[k]⁻¹ A by invariance).
      have hA_iter : ∀ k', shiftZ^[k'] ⁻¹' A = A := by
        intro k'
        induction k' with
        | zero => simp
        | succ m ih =>
          show (shiftZ^[m + 1]) ⁻¹' A = A
          rw [Function.iterate_succ, Set.preimage_comp]
          -- shiftZ^[m+1] = shiftZ^[m] ∘ shiftZ. So preimage is (shiftZ^[m] ∘ shiftZ)⁻¹ A = shiftZ⁻¹ (shiftZ^[m]⁻¹ A) = shiftZ⁻¹ A = A.
          rw [ih, hA_inv]
      have h_diff_eq : s n ∆ A = shiftZ^[k n] ⁻¹' (t n ∆ A) := by
        -- shiftZ^[k]⁻¹ (t Δ A) = (shiftZ^[k]⁻¹ t) Δ (shiftZ^[k]⁻¹ A) = s_n Δ A.
        rw [Set.preimage_symmDiff, hA_iter (k n)]
      rw [h_diff_eq]
      have hmp : MeasurePreserving (shiftZ^[k n] : (∀ _ : ℤ, α) → _) (μZ μ q) (μZ μ q) :=
        (measurePreserving_shiftZ μ q).iterate (k n)
      have h_meas_diff : NullMeasurableSet (t n ∆ A) (μZ μ q) :=
        (((MeasurableSet.of_mem_measurableCylinders (ht_mem n)).symmDiff hA)).nullMeasurableSet
      rw [hmp.measure_preimage h_meas_diff]
      exact ht_lt n
    -- Borel-Cantelli: ∑ μZ(s_n Δ A) ≤ ∑ (1/2)^{n+1} ≤ ∑ (1/2)^n, so limsup (s_n Δ A) is null.
    have h_sum_fin : ∑' n : ℕ, μZ μ q (s n ∆ A) ≠ ∞ := by
      have h_geom_fin : ∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ n ≠ ∞ := by
        rw [ENNReal.tsum_geometric]
        simp
      have h_le : ∀ n : ℕ, μZ μ q (s n ∆ A) ≤ (1 / 2 : ℝ≥0∞) ^ n := by
        intro n
        refine le_trans (le_of_lt (hs_diff n)) ?_
        -- (1/2)^(n+1) = (1/2)^n * (1/2) ≤ (1/2)^n.
        rw [pow_succ]
        refine mul_le_of_le_one_right' ?_
        norm_num
      exact ne_top_of_le_ne_top h_geom_fin (ENNReal.tsum_le_tsum h_le)
    have h_limsup_null : μZ μ q (Filter.limsup (fun n => s n ∆ A) Filter.atTop) = 0 :=
      MeasureTheory.measure_limsup_atTop_eq_zero h_sum_fin
    -- Define A' := Filter.liminf s atTop. Show A' ∈ posSigma and A =ᵐ A'.
    refine ⟨Filter.liminf s Filter.atTop, ?_, ?_⟩
    · -- liminf s = ⨆ n, ⨅ m ≥ n, s m. Each s m ∈ posSigma; closed under ⨅, ⨆.
      rw [Filter.liminf_eq_iSup_iInf_of_nat]
      -- Goal: MeasurableSet[posSigma] (⨆ n, ⨅ i ≥ n, s i)
      -- ⨆ on sets is ⋃, ⨅ is ⋂. Apply MeasurableSet.iUnion + MeasurableSet.iInter.
      refine MeasurableSet.iUnion (fun n => ?_)
      refine MeasurableSet.iInter (fun m => ?_)
      refine MeasurableSet.iInter (fun _ => hs_pos m)
    · -- A =ᵐ liminf s.
      -- The set `limsup (s n Δ A)` has μZ measure 0. For x outside this null set,
      -- x ∈ s n Δ A only finitely often, i.e., eventually x ∈ A ↔ x ∈ s n.
      -- So x ∈ A ↔ (x ∈ s n for all sufficiently large n) ↔ x ∈ liminf s.
      have h_ae_notin : ∀ᵐ x ∂(μZ μ q), x ∉ Filter.limsup (fun n => s n ∆ A) Filter.atTop :=
        measure_eq_zero_iff_ae_notMem.mp h_limsup_null
      filter_upwards [h_ae_notin] with x hx
      -- hx : x ∉ limsup (fun n => s n ∆ A) atTop
      -- Goal: A x = liminf s atTop x  (Set membership as `Prop` equality)
      rw [mem_limsup_iff_frequently_mem, Filter.not_frequently] at hx
      -- hx : ∀ᶠ n in atTop, x ∉ s n ∆ A
      apply propext
      show x ∈ A ↔ x ∈ Filter.liminf s Filter.atTop
      rw [mem_liminf_iff_eventually_mem]
      -- Goal: x ∈ A ↔ ∀ᶠ n in atTop, x ∈ s n.
      constructor
      · intro hxA
        filter_upwards [hx] with n hxn
        by_contra hxs
        exact hxn (Or.inr ⟨hxA, hxs⟩)
      · intro hxs
        rcases (hxs.and hx).exists with ⟨n, hxsn, hxn_diff⟩
        by_contra hxA
        exact hxn_diff (Or.inl ⟨hxsn, hxA⟩)
  obtain ⟨A', hA'_pos, hAA'⟩ := h_approx_pos
  -- A' = natProj⁻¹ B for some measurable B.
  obtain ⟨B, hB, hA'_eq⟩ := exists_preimage_natProj_of_posSigma (α := α) hA'_pos
  -- B is shiftN-invariant mod null on ν.
  have h_natProj_mp : MeasurePreserving (natProj (α := α)) (μZ μ q) ν :=
    measurePreserving_natProj μ q
  -- shiftZ⁻¹ A = A. Apply natProj.
  -- shiftZ⁻¹ A =ᵐ shiftZ⁻¹ A' (since A =ᵐ A')
  -- shiftZ⁻¹ A' = shiftZ⁻¹ (natProj⁻¹ B) = (natProj ∘ shiftZ)⁻¹ B = (shiftN ∘ natProj)⁻¹ B
  --             = natProj⁻¹ (shiftN⁻¹ B)
  -- So A =ᵐ natProj⁻¹ B and A = shiftZ⁻¹ A =ᵐ natProj⁻¹ (shiftN⁻¹ B). Hence
  -- natProj⁻¹ B =ᵐ natProj⁻¹ (shiftN⁻¹ B), so ν(B Δ shiftN⁻¹ B) = 0.
  have h_inv_mod : shiftN ⁻¹' B =ᵐ[ν] B := by
    -- Derive via measure-preserving + the shift invariance of A.
    -- natProj⁻¹ (shiftN⁻¹ B Δ B) has μZ measure 0.
    have h1 : natProj ⁻¹' (shiftN ⁻¹' B) = shiftZ ⁻¹' A' := by
      rw [hA'_eq]
      ext x
      -- LHS: shiftN (natProj x) ∈ B. RHS: natProj (shiftZ x) ∈ B.
      -- natProj_semiconj: natProj ∘ shiftZ = shiftN ∘ natProj.
      simp only [Set.mem_preimage]
      rw [show natProj (shiftZ x) = shiftN (natProj x) from
        natProj_semiconj (α := α) x]
    have h2 : shiftZ ⁻¹' A' =ᵐ[μZ μ q] A' := by
      -- shiftZ⁻¹ A =ᵐ shiftZ⁻¹ A' (since A =ᵐ A'), and shiftZ⁻¹ A = A by hA_inv, so
      -- shiftZ⁻¹ A' =ᵐ A =ᵐ A'.
      have hA_inv' : shiftZ ⁻¹' A' =ᵐ[μZ μ q] shiftZ ⁻¹' A :=
        (measurePreserving_shiftZ μ q).quasiMeasurePreserving.ae_eq_comp hAA'.symm
      have step1 : shiftZ ⁻¹' A' =ᵐ[μZ μ q] A := hA_inv ▸ hA_inv'
      exact step1.trans hAA'
    -- natProj⁻¹ (shiftN⁻¹ B) =ᵐ natProj⁻¹ B (via h1 + hA'_eq + h2)
    have h3 : natProj ⁻¹' (shiftN ⁻¹' B) =ᵐ[μZ μ q] natProj ⁻¹' B := by
      rw [h1, ← hA'_eq]; exact h2
    -- Push through measure-preserving natProj to get shiftN⁻¹ B =ᵐ[ν] B.
    have h4 : (μZ μ q) (natProj ⁻¹' ((shiftN ⁻¹' B) ∆ B)) = 0 := by
      have : natProj ⁻¹' ((shiftN ⁻¹' B) ∆ B)
          = (natProj ⁻¹' (shiftN ⁻¹' B)) ∆ (natProj ⁻¹' B) := by
        ext x; simp [Set.mem_symmDiff, Set.mem_preimage]
      rw [this]
      exact measure_symmDiff_eq_zero_iff.mpr h3
    have h5 : ν ((shiftN ⁻¹' B) ∆ B) = 0 := by
      have := h_natProj_mp.measure_preimage (s := (shiftN ⁻¹' B) ∆ B)
        ((measurable_shiftN hB).symmDiff hB).nullMeasurableSet
      rw [this] at h4
      exact h4
    -- ν((shiftN⁻¹B) Δ B) = 0 ⇒ shiftN⁻¹ B =ᵐ B.
    exact measure_symmDiff_eq_zero_iff.mp h5
  -- By shiftN ergodicity: B =ᵐ ∅ ∨ B =ᵐ univ.
  have h_or : B =ᵐ[ν] (∅ : Set _) ∨ B =ᵐ[ν] (Set.univ : Set _) := by
    refine hN.quasiErgodic.ae_empty_or_univ₀ hB.nullMeasurableSet ?_
    exact h_inv_mod
  rcases h_or with h_zero | h_one
  · left
    -- B =ᵐ ∅ implies natProj⁻¹ B =ᵐ ∅ implies A' =ᵐ ∅ implies A =ᵐ ∅.
    have hB_zero : ν B = 0 := ae_eq_empty.mp h_zero
    have hA'_zero : μZ μ q A' = 0 := by
      rw [hA'_eq, h_natProj_mp.measure_preimage hB.nullMeasurableSet]
      exact hB_zero
    have hA_zero : μZ μ q A = 0 := by
      have h := measure_mono_ae hAA'.le
      exact le_antisymm (h.trans hA'_zero.le) bot_le
    exact ae_eq_empty.mpr hA_zero
  · right
    -- B =ᵐ univ implies B^c =ᵐ ∅ implies ν B^c = 0 ⇒ ν B = 1 ⇒ μZ A' = 1 ⇒ μZ A = 1.
    have hB_univ : ν (Bᶜ) = 0 := ae_eq_univ.mp h_one
    have hA'_compl : μZ μ q (A'ᶜ) = 0 := by
      have : A'ᶜ = natProj ⁻¹' (Bᶜ) := by rw [hA'_eq]; rfl
      rw [this, h_natProj_mp.measure_preimage hB.compl.nullMeasurableSet]
      exact hB_univ
    have hA_compl : μZ μ q (Aᶜ) = 0 := by
      have hA_compl_ae : Aᶜ =ᵐ[μZ μ q] A'ᶜ := hAA'.compl
      have := ae_eq_empty.mp ((hA_compl_ae.trans (ae_eq_empty.mpr hA'_compl)) :
        Aᶜ =ᵐ[μZ μ q] (∅ : Set _))
      exact this
    exact ae_eq_univ.mpr hA_compl

end ErgodicityProof

end InformationTheory.Shannon.TwoSided
