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
import InformationTheory.Probability.TwoSidedExtension.Core
import InformationTheory.Probability.TwoSidedExtension.Backward

namespace InformationTheory.Shannon.TwoSided

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology symmDiff

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

section Backward

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
/-! ### Bridge to `conditionalEntropyTail`

The remaining piece of the integral identity is matching the `μZ`-side condExp
formulation of `condProbPast` with the `μ`-side `condDistrib` formulation of
`conditionalEntropyTail`. We bridge through:
* `pastBlock k : (∀ _ : ℤ, α) → (Fin k → α)`, the projection
  `x ↦ (x(-k), x(-k+1), …, x(-1))`; viewing the finite past as a finite-dimensional
  RV;
* `condDistrib_ae_eq_condExp` to identify `condProbPast a k` with
  `(condDistrib coord0 (pastBlock k) (μZ) (pastBlock k x)).real {a}`;
* a stationarity-driven joint-law equality between the `μZ`-pushforward of
  `(coord0, pastBlock k)` and the `μ`-pushforward of `(obs k, blockRV k)`,
  which transports `condEntropy` between the two sides via
  `condEntropy_eq_pushforward`. -/

/-- The "past block" projection: `pastBlock k x i := x (i.val - k)`.
Maps `x : ℤ → α` to its restriction at indices `{-k, -k+1, …, -1}`, viewed
as a function `Fin k → α`. -/
def pastBlock (k : ℕ) : (∀ _ : ℤ, α) → (Fin k → α) :=
  fun x i => x ((i.val : ℤ) - k)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The past block projection is measurable. -/
lemma measurable_pastBlock (k : ℕ) :
    Measurable (pastBlock k : (∀ _ : ℤ, α) → (Fin k → α)) := by
  refine measurable_pi_iff.mpr (fun i => ?_)
  exact measurable_pi_apply _

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α]
  [IsProbabilityMeasure μ] in
/-- The comap of `MeasurableSpace.pi` along `pastBlock k` equals `pastSigma k`.
This is the algebraic identification of the "past block" σ-algebra with the
generator-form `pastSigma k`. -/
lemma comap_pastBlock_eq_pastSigma (k : ℕ) :
    (MeasurableSpace.pi : MeasurableSpace (Fin k → α)).comap (pastBlock k)
      = pastSigma (α := α) k := by
  -- `MeasurableSpace.pi (Fin k → α) = ⨆ i : Fin k, m_α.comap (·i)`.
  -- comap pulls back: `(⨆ M).comap f = ⨆ M.comap f`.
  -- So LHS = `⨆ i : Fin k, m_α.comap (fun x => x ((i.val : ℤ) - k))`.
  -- RHS = `cylinderEvents {j : ℤ | -k ≤ j ∧ j ≤ -1} = ⨆ j ∈ {-k,…,-1}, m_α.comap (·j)`.
  -- A `Fin k`-indexed iSup over `i.val - k` and a `ℤ`-indexed (restricted) iSup over
  -- `j ∈ {-k,…,-1}` are the same family.
  -- Use `measurable_iff_comap_le`/`measurable_pi_iff` style: a σ-algebra ≤ another
  -- iff the identity map is measurable. Equivalent direct comap rewriting:
  apply le_antisymm
  · -- LHS ≤ RHS: rewrite `MeasurableSpace.pi` as iSup of coordinate comaps,
    -- pull comap through iSup, identify each `Fin k → α` coord with a ℤ index.
    change MeasurableSpace.comap (pastBlock k) MeasurableSpace.pi ≤ _
    rw [show (MeasurableSpace.pi : MeasurableSpace (Fin k → α))
        = ⨆ i : Fin k, MeasurableSpace.comap (fun x : Fin k → α => x i) inferInstance from rfl,
      MeasurableSpace.comap_iSup]
    refine iSup_le (fun i => ?_)
    rw [MeasurableSpace.comap_comp]
    -- Goal: `m_α.comap (fun x => x ((i.val : ℤ) - k)) ≤ pastSigma k`.
    have hi_mem : ((i.val : ℤ) - k) ∈ ({j : ℤ | -(k : ℤ) ≤ j ∧ j ≤ -1} : Set ℤ) := by
      refine ⟨?_, ?_⟩
      · have h1 : (0 : ℤ) ≤ (i.val : ℤ) := Int.natCast_nonneg _
        linarith
      · have h2 : (i.val : ℤ) ≤ k - 1 := by
          have hh : i.val < k := i.2
          have : (i.val : ℤ) < (k : ℤ) := by exact_mod_cast hh
          linarith
        linarith
    -- `pastSigma k` reduces to the cylinderEvents iSup.
    change MeasurableSpace.comap (fun x : (∀ _ : ℤ, α) => x ((i.val : ℤ) - k))
        inferInstance ≤ cylinderEvents (X := fun _ : ℤ => α) _
    show _ ≤ ⨆ j ∈ ({j : ℤ | -(k : ℤ) ≤ j ∧ j ≤ -1} : Set ℤ),
            MeasurableSpace.comap (fun x : (∀ _ : ℤ, α) => x j) inferInstance
    exact le_iSup₂ (f := fun j _ =>
      MeasurableSpace.comap (fun x : (∀ _ : ℤ, α) => x j) inferInstance)
      ((i.val : ℤ) - k) hi_mem
  · -- RHS ≤ LHS.
    change cylinderEvents (X := fun _ : ℤ => α) _
          ≤ MeasurableSpace.comap (pastBlock k) MeasurableSpace.pi
    show ⨆ j ∈ ({j : ℤ | -(k : ℤ) ≤ j ∧ j ≤ -1} : Set ℤ),
            MeasurableSpace.comap (fun x : (∀ _ : ℤ, α) => x j) inferInstance
          ≤ MeasurableSpace.comap (pastBlock k) MeasurableSpace.pi
    refine iSup₂_le (fun j hj => ?_)
    obtain ⟨h_lo, h_hi⟩ := hj
    -- j ∈ [-k, -1], so j + k ∈ [0, k-1], cast to Fin k.
    have hj_plus_k_nn : (0 : ℤ) ≤ j + k := by linarith
    set i : ℕ := (j + k).toNat with hi_def
    have hi_eq_int : (i : ℤ) = j + k := Int.toNat_of_nonneg hj_plus_k_nn
    have hi_lt : i < k := by
      have : (i : ℤ) < (k : ℤ) := by rw [hi_eq_int]; linarith
      exact_mod_cast this
    let i' : Fin k := ⟨i, hi_lt⟩
    have hj_eq : j = (i'.val : ℤ) - k := by
      show j = ((i : ℤ)) - k
      rw [hi_eq_int]; ring
    rw [hj_eq]
    -- Goal: `m_α.comap (fun x => x ((i'.val : ℤ) - k)) ≤ (m_pi).comap (pastBlock k)`.
    rw [show (MeasurableSpace.pi : MeasurableSpace (Fin k → α))
        = ⨆ ii : Fin k, MeasurableSpace.comap (fun x : Fin k → α => x ii) inferInstance from rfl,
      MeasurableSpace.comap_iSup]
    refine le_trans ?_ (le_iSup _ i')
    rw [MeasurableSpace.comap_comp]
    -- (m_α.comap (fun x : Fin k → α => x i')).comap (pastBlock k)
    --   = m_α.comap (fun x => pastBlock k x i')
    --   = m_α.comap (fun x => x ((i'.val : ℤ) - k))
    -- which matches LHS.
    rfl

/-! ### Joint-law identification via stationarity -/

omit [DecidableEq α] [Nonempty α] in
lemma mapZ_coord0_pastBlock_apply_singleton (k : ℕ) (a : α) (s : Fin k → α) :
    (μZ μ p).map (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x)) {(a, s)}
      = (μ.map (p.blockRV (k + 1))) {Fin.snoc s a} := by
  classical
  have hpair_meas_Z : Measurable (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x)) :=
    (measurable_coord0).prodMk (measurable_pastBlock k)
  set s_full : Fin (k + 1) → α := Fin.snoc s a with hs_full_def
  -- Step LHS-1: rewrite the LHS as μZ of a set, then split into shifted-marginal.
  rw [Measure.map_apply hpair_meas_Z (measurableSet_singleton _)]
  -- Preimage rewrite: { x | (x 0 = a) ∧ pastBlock k x = s }
  --   = { x | ∀ i : Fin (k+1), x ((i.val:ℤ) - k) = s_full i }
  have hpre : (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x)) ⁻¹' {(a, s)}
      = { x : (∀ _ : ℤ, α) | ∀ i : Fin (k + 1), x ((i.val : ℤ) - k) = s_full i } := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hcoord, hpast⟩
      intro i
      -- Cases on i: either i = Fin.last k or i = j.castSucc for j : Fin k.
      refine Fin.lastCases ?_ ?_ i
      · -- i = Fin.last k: x ((k:ℤ) - k) = x 0 = a = s_full (Fin.last k).
        have h_int_last : ((Fin.last k).val : ℤ) - k = 0 := by
          show ((k : ℤ)) - k = 0; ring
        rw [h_int_last, hs_full_def, Fin.snoc_last]
        exact hcoord
      · intro j
        -- i = j.castSucc: x (j.val - k) = (pastBlock k x) j = s j = s_full j.castSucc.
        have hj_cast_val : (j.castSucc : Fin (k+1)).val = j.val := rfl
        rw [hs_full_def, Fin.snoc_castSucc]
        show x ((j.val : ℤ) - k) = s j
        have : pastBlock k x j = s j := congr_fun hpast _
        exact this
    · intro hall
      refine ⟨?_, ?_⟩
      · -- coord0 x = a: extract `i = Fin.last k`.
        have h_int_last : ((Fin.last k).val : ℤ) - k = 0 := by
          show ((k : ℤ)) - k = 0; ring
        have hlast := hall (Fin.last k)
        rw [h_int_last, hs_full_def, Fin.snoc_last] at hlast
        exact hlast
      · funext j
        have h := hall j.castSucc
        rw [hs_full_def, Fin.snoc_castSucc] at h
        show x ((j.val : ℤ) - k) = s j
        have hcast_val : (j.castSucc : Fin (k+1)).val = j.val := rfl
        rw [hcast_val] at h
        exact h
  rw [hpre]
  -- A cylinder on the index set `J := { (i.val:ℤ) - k | i : Fin (k+1) }`.
  set J : Finset ℤ :=
    (Finset.univ.image (fun i : Fin (k + 1) => (i.val : ℤ) - k))
    with hJ_def
  have hi_mem : ∀ i : Fin (k + 1), ((i.val : ℤ) - k) ∈ J := by
    intro i
    rw [hJ_def, Finset.mem_image]
    exact ⟨i, Finset.mem_univ _, rfl⟩
  set S_J : Set (∀ _ : J, α) :=
    { f | ∀ i : Fin (k + 1), f ⟨((i.val : ℤ) - k), hi_mem i⟩ = s_full i } with hS_J
  have hS_J_meas : MeasurableSet S_J := by
    have h_inter : S_J = ⋂ i : Fin (k + 1),
        { f : ∀ _ : J, α | f ⟨((i.val : ℤ) - k), hi_mem i⟩ = s_full i } := by
      ext f; simp [hS_J]
    rw [h_inter]
    refine MeasurableSet.iInter (fun i => ?_)
    have hpre' : { f : ∀ _ : J, α | f ⟨((i.val : ℤ) - k), hi_mem i⟩ = s_full i }
        = (fun f : ∀ _ : J, α => f ⟨((i.val : ℤ) - k), hi_mem i⟩) ⁻¹' {s_full i} := rfl
    rw [hpre']
    exact (measurable_pi_apply _) (measurableSet_singleton _)
  have h_set_eq :
      { x : (∀ _ : ℤ, α) | ∀ i : Fin (k + 1), x ((i.val : ℤ) - k) = s_full i }
        = cylinder J S_J := by
    ext x
    simp only [Set.mem_setOf_eq, cylinder, Set.mem_preimage, Finset.restrict, hS_J]
  rw [h_set_eq, μZ_cylinder μ p hS_J_meas]
  have hJ_shift : ∀ j ∈ J, (0 : ℤ) ≤ j + k := by
    intro j hj
    rw [hJ_def, Finset.mem_image] at hj
    obtain ⟨i, _, rfl⟩ := hj
    have h1 : (0 : ℤ) ≤ (i.val : ℤ) := Int.natCast_nonneg _
    linarith
  rw [shiftedMarginal_eq_of_shift μ p J k hJ_shift,
      Measure.map_apply (measurable_obsZ μ p k J) hS_J_meas]
  rw [Measure.map_apply (p.measurable_blockRV (k+1)) (measurableSet_singleton _)]
  apply congrArg
  ext ω
  simp only [Set.mem_preimage, hS_J, Set.mem_setOf_eq, obsZ, Set.mem_singleton_iff]
  constructor
  · intro hf
    funext i
    have := hf i
    have hcast : ((((i.val : ℤ) - k) + ((k : ℕ) : ℤ)).toNat) = i.val := by
      have : ((i.val : ℤ) - k) + ((k : ℕ) : ℤ) = (i.val : ℤ) := by ring
      rw [this]
      exact_mod_cast Int.toNat_natCast _
    show p.blockRV (k+1) ω i = s_full i
    rw [hcast] at this
    exact this
  · intro hf i
    have hcast : ((((i.val : ℤ) - k) + ((k : ℕ) : ℤ)).toNat) = i.val := by
      have : ((i.val : ℤ) - k) + ((k : ℕ) : ℤ) = (i.val : ℤ) := by ring
      rw [this]
      exact_mod_cast Int.toNat_natCast _
    rw [hcast]
    exact congr_fun hf i

omit [Fintype α] [DecidableEq α] [Nonempty α] [IsProbabilityMeasure μ] in
lemma map_obs_blockRV_apply_singleton (k : ℕ) (a : α) (s : Fin k → α) :
    μ.map (fun ω : Ω => (p.obs k ω, p.blockRV k ω)) {(a, s)}
      = (μ.map (p.blockRV (k + 1))) {Fin.snoc s a} := by
  classical
  have hpair_meas_Ω : Measurable (fun ω : Ω => (p.obs k ω, p.blockRV k ω)) :=
    (p.measurable_obs k).prodMk (p.measurable_blockRV k)
  set s_full : Fin (k + 1) → α := Fin.snoc s a with hs_full_def
  rw [Measure.map_apply hpair_meas_Ω (measurableSet_singleton _),
      Measure.map_apply (p.measurable_blockRV (k+1)) (measurableSet_singleton _)]
  apply congrArg
  ext ω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hobs, hblock⟩
    funext i
    refine Fin.lastCases ?_ ?_ i
    · -- i = Fin.last k.
      rw [hs_full_def, Fin.snoc_last]
      show p.obs (Fin.last k) ω = a
      show p.obs k ω = a
      exact hobs
    · intro j
      -- i = j.castSucc.
      rw [hs_full_def, Fin.snoc_castSucc]
      show p.obs j.castSucc.val ω = s j
      have h1 : (j.castSucc : Fin (k+1)).val = j.val := rfl
      rw [h1]
      show p.obs j.val ω = s j
      have h2 : p.blockRV k ω j = p.obs j.val ω := rfl
      rw [← h2, hblock]
  · intro hblock_full
    refine ⟨?_, ?_⟩
    · -- p.obs k ω = a (extract Fin.last k).
      have hlast := congr_fun hblock_full (Fin.last k)
      rw [hs_full_def, Fin.snoc_last] at hlast
      show p.obs k ω = a
      show p.obs (Fin.last k) ω = a
      exact hlast
    · funext j
      have hj := congr_fun hblock_full j.castSucc
      rw [hs_full_def, Fin.snoc_castSucc] at hj
      show p.obs j.val ω = s j
      have h1 : (j.castSucc : Fin (k+1)).val = j.val := rfl
      have h2 : p.blockRV (k + 1) ω j.castSucc = p.obs j.castSucc.val ω := rfl
      rw [h2] at hj
      rw [h1] at hj
      exact hj

omit [DecidableEq α] [Nonempty α] in
/-- **Joint-law equality** (the key bridge for the integral identity).

The pushforward of `μZ` under the joint map `x ↦ (coord0 x, pastBlock k x)`
equals the pushforward of `μ` under `ω ↦ (p.obs k ω, p.blockRV k ω)`.

Proof: both sides are probability measures on `α × (Fin k → α)`. We show they
agree on rectangles `{a} ×ˢ {s}`, which is enough since the spaces are finite.
The LHS rectangle reduces, via stationarity (shift by `k`), to the marginal at
the index set `{0, 1, …, k}`, which equals the ℕ-side block.
The RHS rectangle is exactly the singleton mass of `μ.map (p.blockRV (k+1))`
at the corresponding `Fin (k+1) → α`. -/
@[entry_point]
theorem joint_pastBlock_coord0_eq (k : ℕ) :
    (μZ μ p).map (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x))
      = μ.map (fun ω : Ω => (p.obs k ω, p.blockRV k ω)) := by
  classical
  -- Both are probability measures on `α × (Fin k → α)` (finite × finite).
  have hpair_meas_Z : Measurable (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x)) :=
    (measurable_coord0).prodMk (measurable_pastBlock k)
  have hpair_meas_Ω : Measurable (fun ω : Ω => (p.obs k ω, p.blockRV k ω)) :=
    (p.measurable_obs k).prodMk (p.measurable_blockRV k)
  -- Both are probability measures (in particular, finite).
  haveI : IsProbabilityMeasure
      ((μZ μ p).map (fun x : (∀ _ : ℤ, α) => (coord0 x, pastBlock k x))) :=
    Measure.isProbabilityMeasure_map hpair_meas_Z.aemeasurable
  haveI : IsProbabilityMeasure
      (μ.map (fun ω : Ω => (p.obs k ω, p.blockRV k ω))) :=
    Measure.isProbabilityMeasure_map hpair_meas_Ω.aemeasurable
  -- It suffices to show equality on singletons (finite types).
  refine Measure.ext_of_singleton ?_
  rintro ⟨a, s⟩
  -- Both LHS and RHS singletons reduce to `μ.map (blockRV (k+1)) {Fin.snoc s a}`.
  rw [mapZ_coord0_pastBlock_apply_singleton μ p k a s,
    map_obs_blockRV_apply_singleton μ p k a s]

omit [DecidableEq α] in
/-- **Conditional expectation identification**: `condProbPast a k` agrees a.s.
with the `condDistrib`-form regular conditional probability built from
`(coord0, pastBlock k)`. -/
lemma condProbPast_ae_eq_condDistrib (a : α) (k : ℕ) :
    condProbPast μ p a k =ᵐ[μZ μ p]
      fun x => (ProbabilityTheory.condDistrib coord0 (pastBlock k) (μZ μ p)
        (pastBlock k x)).real {a} := by
  -- Apply `condDistrib_ae_eq_condExp` with Y := coord0, X := pastBlock k, s := {a}.
  -- This gives:
  --   `(condDistrib coord0 pastBlock μZ (pastBlock k x)).real {a}
  --      =ᵐ[μZ] μZ⟦coord0 ⁻¹' {a} | (m_α^Fin k).comap (pastBlock k)⟧`
  -- and we identify the σ-algebra via `comap_pastBlock_eq_pastSigma`.
  -- `condProbPast a k x` is defined as `μZ[indicator(coord0=a) | pastFiltration k]
  --   = μZ[indicator | pastSigma k]`, so we need to relate to `μZ⟦coord0⁻¹{a} | pastSigma k⟧`.
  -- Recall: `μZ⟦S | m⟧ = μZ[indicator(S) | m]` by definition. So both formulas agree.
  have h_ae := ProbabilityTheory.condDistrib_ae_eq_condExp (μ := μZ μ p)
    (X := pastBlock k) (Y := coord0)
    (measurable_pastBlock k) measurable_coord0 (measurableSet_singleton a)
  -- h_ae : (fun x => (condDistrib coord0 (pastBlock k) μZ (pastBlock k x)).real {a})
  --   =ᵐ[μZ] μZ⟦coord0 ⁻¹' {a} | (m_α).comap (pastBlock k)⟧
  --   = μZ⟦coord0 ⁻¹' {a} | pastSigma k⟧  (after rewriting the comap)
  -- Note: `μ⟦s | m⟧ := μ[s.indicator (fun _ => (1 : ℝ)) | m]`.
  -- So `μZ⟦coord0 ⁻¹' {a} | pastSigma k⟧ = μZ[indicator | pastSigma k] = condProbPast a k`.
  symm
  have h_sigma_eq : (inferInstance : MeasurableSpace (Fin k → α)).comap (pastBlock k)
      = (pastFiltration (α := α)) k := comap_pastBlock_eq_pastSigma k
  -- Rewrite the conditional expectation σ-algebra.
  refine h_ae.trans ?_
  -- Goal: μZ⟦coord0 ⁻¹' {a} | _.comap (pastBlock k)⟧ =ᵐ condProbPast a k.
  unfold condProbPast
  show (μZ μ p)⟦coord0 ⁻¹' {a} | (inferInstance : MeasurableSpace (Fin k → α)).comap (pastBlock k)⟧
      =ᵐ[μZ μ p] (μZ μ p)[(coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ))
          | (pastFiltration (α := α)) k]
  rw [h_sigma_eq]


end Backward

end InformationTheory.Shannon.TwoSided
