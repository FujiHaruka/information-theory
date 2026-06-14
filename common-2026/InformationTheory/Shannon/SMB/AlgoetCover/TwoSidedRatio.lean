import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.SMB.ChainRule
import InformationTheory.Shannon.SMB.McMillanBreiman
import InformationTheory.Probability.TwoSidedExtension
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## D.5 — liminf direction (2-sided infinite-past detour)

The liminf direction `liminf blockLogAvg ≥ entropyRate` cannot be obtained from
the one-sided k-Markov approximation alone: the ratio `P_n/q_k` has unbounded
chi-squared expectation. The fix (Algoet–Cover 1988) is to use the **infinite
past** conditional `q_∞(X_0^{n-1}|past_∞) = ∏ μZ(X_i|X_{-∞}^{i-1})`, defined on
the 2-sided extension `(ℤ → α, μZ, shiftZ)` (see `TwoSidedExtension.lean`).

By the tower property, `E_μZ[P_n/q_∞] = 1`, so Markov + Borel–Cantelli give
`P_n/q_∞ ≤ n²` eventually μZ-a.s. Logarithmically, this is
`blockLogAvgZ ≥ (1/n) Σ pmfLogCondInfty - 2 log n / n`. Birkhoff applied to
`pmfLogCondInfty` on the 2-sided ergodic system gives
`(1/n) Σ pmfLogCondInfty(shiftZ^[i] x) → ∫ pmfLogCondInfty dμZ = entropyRate`,
so `liminf blockLogAvgZ ≥ entropyRate` μZ-a.s. We transfer to the Ω-side via
`forwardEmbed` and the measure-preservation `μ.map forwardEmbed = μZ.map natProj`.
-/

open InformationTheory.Shannon.TwoSided

/-- **First-`n` block projection on the 2-sided side**: pulls out `x_0, …, x_{n-1}`. -/
noncomputable def firstBlockZ (n : ℕ) : (∀ _ : ℤ, α) → (Fin n → α) :=
  fun x i => x (i.val : ℤ)

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
lemma measurable_firstBlockZ (n : ℕ) :
    Measurable (firstBlockZ (α := α) n) :=
  measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

omit [DecidableEq α] [Nonempty α] in
/-- The first-`n` block on the 2-sided side has the same law as `blockRV n` on Ω. -/
lemma map_firstBlockZ_eq_map_blockRV
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    (μZ μ p).map (firstBlockZ (α := α) n) = μ.map (p.blockRV n) := by
  classical
  -- Both sides are probability measures on `Fin n → α` (finite codomain).
  haveI hLHS_prob : IsProbabilityMeasure
      ((μZ μ p).map (firstBlockZ (α := α) n)) :=
    Measure.isProbabilityMeasure_map (measurable_firstBlockZ n).aemeasurable
  haveI hRHS_prob : IsProbabilityMeasure (μ.map (p.blockRV n)) :=
    Measure.isProbabilityMeasure_map (p.measurable_blockRV n).aemeasurable
  -- Suffices to show equality on singletons (finite type).
  refine Measure.ext_of_singleton ?_
  intro s
  rw [Measure.map_apply (measurable_firstBlockZ n) (measurableSet_singleton _),
      Measure.map_apply (p.measurable_blockRV n) (measurableSet_singleton _)]
  -- Now: μZ {x | firstBlockZ n x = s} = μ {ω | p.blockRV n ω = s}.
  -- The LHS preimage is `{x | ∀ i : Fin n, x (i.val : ℤ) = s i}`, a 2-sided
  -- cylinder. The RHS is `μ.map (p.blockRV n) {s}`. Apply `μZ_block_cylinder_eq`.
  have h_LHS_eq : (firstBlockZ (α := α) n) ⁻¹' {s}
      = { x : (∀ _ : ℤ, α) | ∀ i : Fin n, x ((i : ℕ) : ℤ) = s i } := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro hx i
      show x ((i : ℕ) : ℤ) = s i
      rw [show ((i : ℕ) : ℤ) = (i.val : ℤ) from rfl]
      exact congr_fun hx i
    · intro h
      funext i
      show x (i.val : ℤ) = s i
      have := h i
      simpa using this
  rw [h_LHS_eq]
  -- Now: μZ {x | ∀ i, x ((i : ℕ) : ℤ) = s i} = μ.map (p.blockRV n) {s} (by μZ_block_cylinder_eq).
  -- Then unfold μ.map ... = μ (preimage ...).
  rw [μZ_block_cylinder_eq μ p n s]
  rw [Measure.map_apply (p.measurable_blockRV n) (measurableSet_singleton _)]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Z-side blockLogAvg**: the per-symbol negative log-likelihood on the 2-sided side. -/
noncomputable def blockLogAvgZ
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    (∀ _ : ℤ, α) → ℝ :=
  fun x => -(1 / (n : ℝ)) *
    Real.log (((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x})

omit [DecidableEq α] [Nonempty α] in
/-- Bridge: `blockLogAvgZ n (natural extension of ω) = blockLogAvg n ω`. The
"natural extension" `fun i : ℤ => p.obs i.toNat ω` ignores negative coords
(maps them to `p.obs 0 ω = X ω`), but `blockLogAvgZ n` only looks at coords
`{0, …, n-1}`, where it agrees with `forwardEmbed`. -/
lemma blockLogAvgZ_natExt_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) (ω : Ω) :
    blockLogAvgZ μ p n
        (fun i : ℤ => p.obs i.toNat ω) = blockLogAvg μ p n ω := by
  classical
  -- The 2-sided extension at integer coord `i ≥ 0` is `p.obs i ω`.
  unfold blockLogAvgZ blockLogAvg
  -- The argument: `firstBlockZ n (extension ω) = blockRV n ω`.
  have h_args : (firstBlockZ (α := α) n) (fun i : ℤ => p.obs i.toNat ω)
      = p.blockRV n ω := by
    funext i
    show p.obs ((i.val : ℤ).toNat) ω = p.obs i.val ω
    simp
  rw [h_args]
  -- The two measures (μZ.map firstBlockZ n) and (μ.map blockRV n) coincide.
  rw [map_firstBlockZ_eq_map_blockRV μ p n]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Z-side negLogQ∞**: Birkhoff sum of `pmfLogCondInfty` along the orbit. -/
noncomputable def negLogQInftyZ
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    (∀ _ : ℤ, α) → ℝ :=
  fun x => ∑ i ∈ Finset.range n, pmfLogCondInfty μ p (shiftZ^[i] x)

/-- **The Z-side lower-bound likelihood ratio**: `exp(negLogQ∞ - n · blockLogAvgZ)`,
which represents `P_n/q_∞` lifted to `ℝ≥0∞`. -/
noncomputable def MRatioLowerZ
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    (∀ _ : ℤ, α) → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x - (n : ℝ) * blockLogAvgZ μ p n x))

/-! ### Inductive-step infrastructure for `integral_MRatioLowerZ_le_one` -/

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Probability ratio at the `(n+1)`-block over the `n`-block**: when `P_n(s) > 0`,
this is `P_{n+1}(snoc(s, a)) / P_n(s)`; defaulted to `0` when `P_n(s) = 0`. -/
private noncomputable def blockCondRatio
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (s : Fin n → α) (a : α) : ℝ :=
  let P_n : ℝ := ((μZ μ p).map (firstBlockZ (α := α) n)).real {s}
  let P_succ : ℝ :=
    ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {Fin.snoc s a}
  if P_n = 0 then 0 else P_succ / P_n

omit [DecidableEq α] [Nonempty α] in
/-- `blockCondRatio` is measurable (as a discrete map `Fin n → α → α → ℝ`). -/
private lemma measurable_blockCondRatio_apply
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (a : α) :
    Measurable (fun s : Fin n → α => blockCondRatio μ p n s a) :=
  measurable_of_finite _

omit [DecidableEq α] [Nonempty α] in
/-- Sum of `blockCondRatio` over `a : α` equals `1` whenever `P_n(s) > 0`. -/
private lemma sum_blockCondRatio
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α)
    (n : ℕ) (s : Fin n → α)
    (hs_pos : 0 < ((μZ μ p).map (firstBlockZ (α := α) n)).real {s}) :
    ∑ a, blockCondRatio μ p n s a = 1 := by
  classical
  -- Use that `∑_a (μZ.map firstBlockZ (n+1)) {snoc s a} = (μZ.map firstBlockZ n) {s}`.
  -- Then divide both sides by P_n > 0.
  set P_n : ℝ := ((μZ μ p).map (firstBlockZ (α := α) n)).real {s} with hP_n_def
  have hP_n_ne : P_n ≠ 0 := hs_pos.ne'
  -- Each summand equals `(μZ.map firstBlockZ (n+1)) {snoc s a} / P_n`.
  have h_each : ∀ a, blockCondRatio μ p n s a
      = ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {Fin.snoc s a} / P_n := by
    intro a
    show (if ((μZ μ p).map (firstBlockZ (α := α) n)).real {s} = 0 then 0
        else ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {Fin.snoc s a} /
              ((μZ μ p).map (firstBlockZ (α := α) n)).real {s})
        = ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {Fin.snoc s a} / P_n
    rw [← hP_n_def, if_neg hP_n_ne]
  simp_rw [h_each, ← Finset.sum_div]
  -- Now show `∑_a (μZ.map firstBlockZ (n+1)) {snoc s a} = P_n`.
  have h_sum :
      ∑ a, ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {Fin.snoc s a} = P_n := by
    -- Use that `Fin.init (firstBlockZ (n+1) x) = firstBlockZ n x`, so the union of
    -- `{Fin.snoc s a}` over a is the preimage of `{s}` under `Fin.init`.
    have h_init : ∀ (x : ∀ _ : ℤ, α),
        Fin.init (firstBlockZ (α := α) (n + 1) x) = firstBlockZ (α := α) n x := by
      intro x
      funext i
      show firstBlockZ (n + 1) x i.castSucc = firstBlockZ n x i
      show x (i.castSucc.val : ℤ) = x (i.val : ℤ)
      have h_eq : (i.castSucc : Fin (n+1)).val = i.val := rfl
      rw [h_eq]
    -- Express `P_n = ∑_a (μZ.map firstBlockZ (n+1)) {snoc s a}` via
    -- pushforward of `Fin.init`.
    have h_eq : ((μZ μ p).map (firstBlockZ (α := α) n)).real {s}
        = ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real
            (Fin.init ⁻¹' {s} : Set (Fin (n + 1) → α)) := by
      have h_factor : firstBlockZ (α := α) n
          = Fin.init ∘ firstBlockZ (α := α) (n + 1) := by
        funext x i
        exact (h_init x).symm.symm ▸ rfl
      have h_init_meas : Measurable (Fin.init : (Fin (n + 1) → α) → (Fin n → α)) :=
        measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)
      rw [h_factor, ← Measure.map_map h_init_meas (measurable_firstBlockZ (n + 1))]
      rw [Measure.real, Measure.map_apply h_init_meas (measurableSet_singleton _),
        ← Measure.real]
    -- And the preimage `Fin.init ⁻¹' {s}` is `⋃_a {Fin.snoc s a}` (disjoint).
    have h_preim : (Fin.init ⁻¹' {s} : Set (Fin (n + 1) → α))
        = ⋃ a : α, {Fin.snoc s a} := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
      constructor
      · intro h_init_t
        refine ⟨t (Fin.last n), ?_⟩
        -- t = Fin.snoc (Fin.init t) (t (Fin.last n)) = Fin.snoc s (t (Fin.last n)).
        rw [← h_init_t]
        exact (Fin.snoc_init_self t).symm
      · rintro ⟨a, h_t_eq⟩
        rw [h_t_eq, Fin.init_snoc]
    rw [hP_n_def, h_eq, h_preim]
    -- Now `(μZ.map firstBlockZ (n+1)) (⋃_a {snoc s a}) = ∑_a (μZ.map firstBlockZ (n+1)) {snoc s a}`.
    -- `Fin.snoc s` is injective in `a` (since `(snoc s a) (Fin.last n) = a`).
    have h_inj : Function.Injective (fun a : α => (Fin.snoc s a : Fin (n + 1) → α)) := by
      intro a₁ a₂ h_eq_snoc
      have := congr_fun h_eq_snoc (Fin.last n)
      simp only [Fin.snoc_last] at this
      exact this
    -- Singletons are pairwise disjoint.
    have h_disj :
        Pairwise (Function.onFun Disjoint
          (fun a : α => ({Fin.snoc s a} : Set (Fin (n + 1) → α)))) := by
      intro a₁ a₂ hab
      simp only [Function.onFun, Set.disjoint_singleton]
      intro h
      exact hab (h_inj h)
    -- iUnion = biUnion (over Finset.univ).
    have h_iUnion_to_biUnion :
        (⋃ a : α, ({Fin.snoc s a} : Set (Fin (n + 1) → α)))
          = ⋃ a ∈ (Finset.univ : Finset α), ({Fin.snoc s a} : Set _) := by
      ext t; simp
    rw [h_iUnion_to_biUnion]
    rw [measureReal_biUnion_finset (fun a _ b _ hab => h_disj hab)
      (fun a _ => measurableSet_singleton _)]
  rw [h_sum, div_self hP_n_ne]

omit [DecidableEq α] [Nonempty α] in
/-- **A.s. positivity of `P_n^Z`**: the singleton mass at the realized
`firstBlockZ n x` is a.s. positive under `μZ`.

Transferred from the Ω-side `block_singleton_pos_ae_at` via `map_firstBlockZ_eq_map_blockRV`. -/
private lemma firstBlockZ_singleton_pos_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    ∀ᵐ x ∂(μZ μ p), 0 < ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x} := by
  classical
  -- The "bad" set is a finite (hence measurable) set in `Fin n → α` of zero measure,
  -- and its preimage under `firstBlockZ n` has μZ-measure 0.
  set S : Set (Fin n → α) :=
    {s | ((μZ μ p).map (firstBlockZ (α := α) n)).real {s} = 0} with hS_def
  have h_S_finite : S.Finite := Set.toFinite S
  have h_S_meas : MeasurableSet S := h_S_finite.measurableSet
  -- (μZ.map firstBlockZ n) S = 0 (sum over finite S of singleton masses = 0).
  have h_S_zero : ((μZ μ p).map (firstBlockZ (α := α) n)) S = 0 := by
    have hS_eq : S = (h_S_finite.toFinset : Set (Fin n → α)) :=
      (Set.Finite.coe_toFinset h_S_finite).symm
    rw [hS_eq, ← sum_measure_singleton]
    refine Finset.sum_eq_zero ?_
    intro s hs
    have hs_mem : s ∈ S := by rwa [Set.Finite.mem_toFinset] at hs
    have hs_real : ((μZ μ p).map (firstBlockZ (α := α) n)).real {s} = 0 := hs_mem
    have h_lt : ((μZ μ p).map (firstBlockZ (α := α) n)) {s} < ∞ := measure_lt_top _ _
    rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hs_real
    exact hs_real.resolve_right h_lt.ne
  -- Pull back to μZ via `firstBlockZ ⁻¹`.
  have h_preim : (μZ μ p) ((firstBlockZ (α := α) n) ⁻¹' S) = 0 := by
    rw [← Measure.map_apply (measurable_firstBlockZ n) h_S_meas]
    exact h_S_zero
  refine ae_iff.mpr ?_
  refine measure_mono_null ?_ h_preim
  intro x hx
  simp only [Set.mem_setOf_eq, not_lt] at hx
  show x ∈ (firstBlockZ (α := α) n) ⁻¹' S
  simp only [Set.mem_preimage, Set.mem_setOf_eq, S]
  exact le_antisymm hx measureReal_nonneg

omit [DecidableEq α] [Nonempty α] in
/-- **Pointwise factorization of `MRatioLowerZ (n+1)` on the a.s. positive set**.

On the set where both `P_n(firstBlockZ n x) > 0` and `P_{n+1}(firstBlockZ (n+1) x) > 0`,
we have the decomposition
`MRatioLowerZ (n+1) x = MRatioLowerZ n x · ofReal(blockCondRatio · exp(pmfLogCondInfty(shift^n x)))`,
where `blockCondRatio` is the chain-rule ratio. -/
private lemma MRatioLowerZ_succ_eq_mul
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ)
    (x : ∀ _ : ℤ, α)
    (hPn_pos : 0 < ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x})
    (hPsucc_pos :
      0 < ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {firstBlockZ (n + 1) x}) :
    MRatioLowerZ μ p (n + 1) x
      = MRatioLowerZ μ p n x
        * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) (x (n : ℤ)))
        * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x))) := by
  classical
  unfold MRatioLowerZ
  -- Rewrite both sides as `ofReal` of real expressions, then handle in ℝ.
  set Pn : ℝ := ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x} with hPn_def
  set Psucc : ℝ := ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real {firstBlockZ (n + 1) x}
    with hPsucc_def
  -- `blockLogAvgZ n x = -(1/n) * log Pn`, so `n * blockLogAvgZ = -log Pn`.
  -- For n = 0, blockLogAvgZ 0 x = -(1/0) * 0 = 0 in Lean (since `1/0 = 0` in ℝ).
  -- For n ≥ 1 with Pn > 0, `exp(-n * blockLogAvgZ n x) = Pn`.
  have h_n_succ_avg : Real.exp (-((n : ℝ) + 1) * blockLogAvgZ μ p (n + 1) x) = Psucc := by
    unfold blockLogAvgZ
    rw [show -((n : ℝ) + 1) * (-(1 / ((n + 1 : ℕ) : ℝ))
            * Real.log Psucc)
          = Real.log Psucc by
          have h_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
          push_cast
          field_simp,
        Real.exp_log hPsucc_pos]
  have h_n_avg : Real.exp (-(n : ℝ) * blockLogAvgZ μ p n x) = Pn := by
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero]
      -- Pn for n = 0 is `((μZ.map firstBlockZ 0).real {firstBlockZ 0 x})` which is the unique map.
      -- firstBlockZ 0 maps everyone to the empty function; mass = total = 1.
      show 1 = Pn
      rw [hPn_def]
      have h_meas : Measurable (firstBlockZ (α := α) 0) := measurable_firstBlockZ 0
      rw [Measure.real, Measure.map_apply h_meas (measurableSet_singleton _)]
      have h_univ : (firstBlockZ (α := α) 0) ⁻¹' {firstBlockZ 0 x} = Set.univ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        funext i; exact i.elim0
      rw [h_univ, measure_univ]; rfl
    · unfold blockLogAvgZ
      have h_n_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
      rw [show -(n : ℝ) * (-(1 / (n : ℝ)) * Real.log Pn) = Real.log Pn by field_simp,
        Real.exp_log hPn_pos]
  -- LHS: `ofReal(exp(negLogQ_{n+1}) * exp(-(n+1) blockLogAvgZ_{n+1}))`
  --    = `ofReal(exp(negLogQ_n) * exp(pmfLogCondInfty(shift^n x)) * Psucc)`.
  have hLHS_arg : negLogQInftyZ μ p (n + 1) x - ((n + 1 : ℕ) : ℝ) * blockLogAvgZ μ p (n + 1) x
      = (negLogQInftyZ μ p n x + pmfLogCondInfty μ p (shiftZ^[n] x))
        + (-((n : ℝ) + 1) * blockLogAvgZ μ p (n + 1) x) := by
    unfold negLogQInftyZ
    rw [Finset.sum_range_succ]; push_cast; ring
  rw [hLHS_arg, Real.exp_add, Real.exp_add, h_n_succ_avg]
  -- RHS: `MRatioLowerZ n x * ofReal(blockCondRatio) * ofReal(exp(pmfLogCondInfty))`.
  -- `MRatioLowerZ n x = ofReal(exp(negLogQ_n) * Pn) on positive set`.
  have hMR_n : ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x
        - (n : ℝ) * blockLogAvgZ μ p n x))
      = ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x) * Pn) := by
    congr 1
    rw [show negLogQInftyZ μ p n x - (n : ℝ) * blockLogAvgZ μ p n x
        = negLogQInftyZ μ p n x + (-(n : ℝ) * blockLogAvgZ μ p n x) by ring]
    rw [Real.exp_add, h_n_avg]
  rw [hMR_n]
  -- `blockCondRatio μ p n (firstBlockZ n x) (x n) = Psucc / Pn` (since `firstBlockZ (n+1) x =
  -- snoc(firstBlockZ n x, x n)`).
  have h_snoc : firstBlockZ (α := α) (n + 1) x
      = (Fin.snoc (firstBlockZ n x) (x (n : ℤ)) : Fin (n + 1) → α) := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · -- i = Fin.last n
      show x (((Fin.last n).val : ℕ) : ℤ)
        = (Fin.snoc (firstBlockZ (α := α) n x) (x (n : ℤ)) : Fin (n + 1) → α) (Fin.last n)
      rw [Fin.snoc_last]
      show x (((Fin.last n).val : ℕ) : ℤ) = x (n : ℤ)
      congr 1
    · intro j
      show firstBlockZ (n + 1) x j.castSucc
        = (Fin.snoc (firstBlockZ (α := α) n x) (x (n : ℤ)) : Fin (n + 1) → α) j.castSucc
      rw [Fin.snoc_castSucc]
      show x ((j.castSucc.val : ℤ)) = x ((j.val : ℤ))
      have h_eq : (j.castSucc : Fin (n+1)).val = j.val := rfl
      rw [h_eq]
  have h_ratio : blockCondRatio μ p n (firstBlockZ n x) (x (n : ℤ)) = Psucc / Pn := by
    show (if ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x} = 0 then 0
        else ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real
            {Fin.snoc (firstBlockZ n x) (x (n : ℤ))} /
            ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x})
        = Psucc / Pn
    rw [if_neg (by rw [← hPn_def]; exact hPn_pos.ne'),
        show Fin.snoc (firstBlockZ (α := α) n x) (x (n : ℤ)) = firstBlockZ (n + 1) x from h_snoc.symm,
        ← hPn_def, ← hPsucc_def]
  rw [h_ratio]
  -- Combine via `ENNReal.ofReal_mul`.
  have h_exp_nn : 0 ≤ Real.exp (negLogQInftyZ μ p n x) := (Real.exp_pos _).le
  have h_exp_pos : 0 < Real.exp (negLogQInftyZ μ p n x) := Real.exp_pos _
  have h_pn_pos : 0 < Pn := hPn_pos
  have h_psucc_pos : 0 < Psucc := hPsucc_pos
  have h_pcondInfty_pos : 0 < Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)) := Real.exp_pos _
  -- LHS: ofReal( (exp Q_n) * (exp pmf) * Psucc )
  -- RHS: ofReal( (exp Q_n) * Pn ) * ofReal( Psucc/Pn ) * ofReal( exp pmf )
  --    = ofReal( exp Q_n * Pn * Psucc/Pn * exp pmf )
  --    = ofReal( exp Q_n * exp pmf * Psucc )
  rw [show Real.exp (negLogQInftyZ μ p n x) * Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)) * Psucc
        = Real.exp (negLogQInftyZ μ p n x) * Psucc * Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x))
        by ring]
  rw [ENNReal.ofReal_mul (by positivity)]
  rw [ENNReal.ofReal_mul h_exp_nn]
  -- Goal: ofReal(exp Qn) * ofReal Psucc * ofReal(exp pmf)
  --     = ofReal(exp Qn * Pn) * ofReal(Psucc/Pn) * ofReal(exp pmf).
  congr 1
  -- Goal: ofReal(exp Qn) * ofReal Psucc = ofReal(exp Qn * Pn) * ofReal(Psucc/Pn).
  rw [ENNReal.ofReal_mul h_exp_nn]
  rw [show Psucc / Pn = Psucc * (1 / Pn) by ring]
  rw [ENNReal.ofReal_mul h_psucc_pos.le]
  -- Goal: ofReal(exp Qn) * ofReal Psucc = ofReal(exp Qn) * ofReal Pn * (ofReal Psucc * ofReal (1/Pn))
  rw [show ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x)) * ENNReal.ofReal Pn
        * (ENNReal.ofReal Psucc * ENNReal.ofReal (1 / Pn))
      = ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n x)) * ENNReal.ofReal Psucc
        * (ENNReal.ofReal Pn * ENNReal.ofReal (1 / Pn)) by ring]
  rw [← ENNReal.ofReal_mul h_pn_pos.le, mul_one_div, div_self h_pn_pos.ne']
  simp

/-- **ENNReal pull-out for indicator factor** (special case of the pull-out property
for the conditional Lebesgue expectation). If `m ≤ m₀`, `μ.trim` σ-finite, `B ∈ m`,
and `f : Ω → ℝ≥0∞`, then `∫⁻ x, B.indicator(1) · f dμ = ∫⁻ x, B.indicator(1) · μ⁻[f|m] dμ`.

Direct consequence of `setLIntegral_condLExp` since `B ∈ m`. -/
private lemma lintegral_indicator_mul_eq
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : @Measure Ω m₀)
    [SigmaFinite (μ.trim hm)]
    {B : Set Ω} (hB : MeasurableSet[m] B) (f : Ω → ℝ≥0∞) :
    ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x * f x ∂μ
      = ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x * μ⁻[f|m] x ∂μ := by
  -- LHS = ∫⁻ x in B, f dμ via indicator/restrict, then setLIntegral_condLExp.
  have h_rw : ∀ (h : Ω → ℝ≥0∞),
      ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x * h x ∂μ = ∫⁻ x in B, h x ∂μ := by
    intro h
    rw [show (fun x => B.indicator (fun _ => (1 : ℝ≥0∞)) x * h x)
          = B.indicator (fun x => 1 * h x) from ?_]
    · rw [MeasureTheory.lintegral_indicator (hm _ hB)]
      simp
    · funext x
      by_cases hx : x ∈ B
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
  rw [h_rw, h_rw, MeasureTheory.setLIntegral_condLExp hm μ f hB]

/-- **ENNReal pull-out (general)**: for `g : Ω → ℝ≥0∞` `m`-measurable and `f : Ω → ℝ≥0∞`
measurable, `∫⁻ x, g · f dμ = ∫⁻ x, g · μ⁻[f|m] dμ`. -/
private lemma lintegral_mul_eq_lintegral_mul_condLExp
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : @Measure Ω m₀)
    [SigmaFinite (μ.trim hm)]
    {g : Ω → ℝ≥0∞} (hg : Measurable[m] g)
    {f : Ω → ℝ≥0∞} (hf : @Measurable Ω ℝ≥0∞ m₀ _ f) :
    ∫⁻ x, g x * f x ∂μ = ∫⁻ x, g x * μ⁻[f|m] x ∂μ := by
  classical
  -- Approximate g by m-simple functions sn ↑ g.
  set sn : ℕ → @SimpleFunc Ω m ℝ≥0∞ := SimpleFunc.eapprox g with hsn_def
  have h_sn_mono : ∀ x, Monotone (fun n => (sn n : Ω → ℝ≥0∞) x) :=
    fun x i j hij => SimpleFunc.monotone_eapprox _ hij x
  have h_g_iSup : ∀ x, g x = ⨆ n, (sn n : Ω → ℝ≥0∞) x :=
    fun x => (SimpleFunc.iSup_eapprox_apply hg x).symm
  have h_sn_meas_m₀ : ∀ n, @Measurable Ω ℝ≥0∞ m₀ _ (sn n : Ω → ℝ≥0∞) :=
    fun n => ((sn n).measurable).mono hm le_rfl
  have h_cL_meas : Measurable[m] (μ⁻[f|m]) := MeasureTheory.measurable_condLExp m μ f
  have h_cL_meas_m₀ : @Measurable Ω ℝ≥0∞ m₀ _ (μ⁻[f|m]) := h_cL_meas.mono hm le_rfl
  -- Pointwise: g x * h x = ⨆ n, (sn n x) * h x (since ⨆ commutes with mul).
  have h_g_mul_iSup : ∀ (h : Ω → ℝ≥0∞), (fun x => g x * h x)
      = fun x => ⨆ n, (sn n : Ω → ℝ≥0∞) x * h x := by
    intro h
    funext x
    rw [h_g_iSup, ENNReal.iSup_mul]
  have h_mono_mul : ∀ (h : Ω → ℝ≥0∞) x, Monotone (fun n => (sn n : Ω → ℝ≥0∞) x * h x) := by
    intro h x i j hij
    have h_nn : (0 : ℝ≥0∞) ≤ h x := bot_le
    exact mul_le_mul_of_nonneg_right (h_sn_mono x hij) h_nn
  have h_meas_mul : ∀ (h : Ω → ℝ≥0∞), @Measurable Ω ℝ≥0∞ m₀ _ h →
      ∀ n, @Measurable Ω ℝ≥0∞ m₀ _ (fun x => (sn n : Ω → ℝ≥0∞) x * h x) :=
    fun h hh n => Measurable.mul (h_sn_meas_m₀ n) hh
  -- Step A: each simple function step holds, using linearity + lintegral_indicator_mul_eq.
  have h_step : ∀ n, ∫⁻ x, (sn n : Ω → ℝ≥0∞) x * f x ∂μ
      = ∫⁻ x, (sn n : Ω → ℝ≥0∞) x * μ⁻[f|m] x ∂μ := by
    intro n
    -- Decompose sn n via its range.
    have h_sn_decomp : ∀ x, (sn n : Ω → ℝ≥0∞) x
        = ∑ c ∈ (sn n).range, c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x := by
      intro x
      rw [Finset.sum_eq_single (sn n x)]
      · simp
      · intro c _ hc
        have h_notmem : x ∉ (sn n) ⁻¹' {c} := fun hx => hc hx.symm
        simp [Set.indicator_of_notMem h_notmem]
      · intro hcontra
        exact absurd (SimpleFunc.mem_range_self _ x) hcontra
    have h_decomp : ∀ x (h : Ω → ℝ≥0∞), (sn n : Ω → ℝ≥0∞) x * h x
        = ∑ c ∈ (sn n).range, (c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x) * h x := by
      intro x h
      rw [h_sn_decomp x, Finset.sum_mul]
    have h_preim_meas : ∀ c, MeasurableSet[m] ((sn n) ⁻¹' {c}) :=
      fun c => (sn n).measurableSet_fiber c
    have h_preim_lt_top : ∀ c ∈ (sn n).range, c ≠ ∞ := by
      intro c hc
      rcases SimpleFunc.mem_range.mp hc with ⟨x, rfl⟩
      exact (SimpleFunc.eapprox_lt_top g n x).ne
    have h_per_c_LHS : ∀ c (h : Ω → ℝ≥0∞), c ≠ ∞ →
        ∫⁻ x, (c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x) * h x ∂μ
          = c * ∫⁻ x, ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x * h x ∂μ := by
      intro c h hc_ne_top
      rw [show (fun x => c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x * h x)
          = fun x => c * (((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x * h x) from
            funext (fun _ => by ring)]
      rw [MeasureTheory.lintegral_const_mul' _ _ hc_ne_top]
    -- Apply per-c rewriting on both sides.
    rw [show (fun x => (sn n : Ω → ℝ≥0∞) x * f x)
        = fun x => ∑ c ∈ (sn n).range,
          (c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x) * f x from
            funext (fun x => h_decomp x f)]
    rw [show (fun x => (sn n : Ω → ℝ≥0∞) x * μ⁻[f|m] x)
        = fun x => ∑ c ∈ (sn n).range,
          (c * ((sn n) ⁻¹' {c}).indicator (fun _ => (1 : ℝ≥0∞)) x) * μ⁻[f|m] x from
            funext (fun x => h_decomp x _)]
    rw [MeasureTheory.lintegral_finsetSum _ (fun c _ =>
      ((Measurable.indicator measurable_const (hm _ (h_preim_meas c))).const_mul c).mul hf)]
    rw [MeasureTheory.lintegral_finsetSum _ (fun c _ =>
      ((Measurable.indicator measurable_const (hm _ (h_preim_meas c))).const_mul c).mul
        h_cL_meas_m₀)]
    refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [h_per_c_LHS c f (h_preim_lt_top c hc),
        h_per_c_LHS c (μ⁻[f|m]) (h_preim_lt_top c hc),
        lintegral_indicator_mul_eq hm μ (h_preim_meas c) f]
  -- Step B: pass to MCT via lintegral_iSup.
  rw [h_g_mul_iSup f, h_g_mul_iSup (μ⁻[f|m])]
  rw [MeasureTheory.lintegral_iSup (fun n => h_meas_mul f hf n) (fun i j hij x => h_mono_mul f x hij)]
  rw [MeasureTheory.lintegral_iSup (fun n => h_meas_mul (μ⁻[f|m]) h_cL_meas_m₀ n)
    (fun i j hij x => h_mono_mul _ x hij)]
  exact iSup_congr h_step

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **σ-algebra of the shifted past**: events depending only on `{x_i : i ≤ n - 1}`. -/
@[reducible] private def shiftedPastSigma (n : ℕ) : MeasurableSpace (∀ _ : ℤ, α) :=
  (negPastSigma (α := α)).comap (shiftZ^[n])

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
private lemma shiftedPastSigma_le (n : ℕ) :
    (shiftedPastSigma (α := α) n) ≤ MeasurableSpace.pi := by
  intro s ⟨t, ht_neg, hts⟩
  rw [← hts]
  exact (measurable_shiftZ.iterate n) (cylinderEvents_le_pi _ ht_neg)

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- The map `condProbInfty(a) ∘ shift^[n]` is measurable w.r.t. `shiftedPastSigma n`. -/
private lemma measurable_condProbInfty_comp_shift_shiftedPastSigma
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) (a : α) :
    @Measurable _ _ (shiftedPastSigma (α := α) n) _
      (fun x => condProbInfty μ p a (shiftZ^[n] x)) := by
  have h_sm_negPast : StronglyMeasurable[negPastSigma (α := α)] (condProbInfty μ p a) := by
    have h := stronglyMeasurable_condProbInfty μ p a
    rw [show (⨆ n : ℕ, (pastFiltration (α := α)) n)
        = (⨆ n : ℕ, pastSigma (α := α) n) from rfl, iSup_pastSigma_eq_negPastSigma] at h
    exact h
  have h_meas_negPast : @Measurable _ _ (negPastSigma (α := α)) _ (condProbInfty μ p a) :=
    h_sm_negPast.measurable
  intro s hs
  show MeasurableSet[shiftedPastSigma n] ((fun x => condProbInfty μ p a (shiftZ^[n] x)) ⁻¹' s)
  refine ⟨condProbInfty μ p a ⁻¹' s, h_meas_negPast hs, ?_⟩
  rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Generic comap-through-shift lemma**: if `f : (∀_:ℤ,α) → β` satisfies
`f = g ∘ shiftZ^[n]` for some `negPastSigma`-measurable `g`, then `f` is
`shiftedPastSigma n`-measurable. -/
private lemma measurable_shiftedPastSigma_of_eq_comp
    {β : Type*} [MeasurableSpace β] (n : ℕ) (f : (∀ _ : ℤ, α) → β)
    {g : (∀ _ : ℤ, α) → β}
    (hg : @Measurable _ _ (negPastSigma (α := α)) _ g)
    (hf : f = g ∘ (shiftZ^[n])) :
    @Measurable _ _ (shiftedPastSigma (α := α) n) _ f := by
  intro s hs
  show MeasurableSet[shiftedPastSigma n] (f ⁻¹' s)
  refine ⟨g ⁻¹' s, hg hs, ?_⟩
  rw [hf]; rfl

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- `shiftZSymm` is a left inverse of `shiftZ`. -/
private lemma shiftZSymm_shiftZ (x : ∀ _ : ℤ, α) : shiftZSymm (shiftZ x) = x := by
  funext i
  show (shiftZ x) (i - 1) = x i
  show x ((i - 1) + 1) = x i
  congr 1; ring

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- Iterated version: `shiftZSymm^n ∘ shiftZ^n = id`. -/
private lemma shiftZSymm_iterate_shiftZ_iterate (n : ℕ) (x : ∀ _ : ℤ, α) :
    (shiftZSymm^[n]) (shiftZ^[n] x) = x := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- (shiftZSymm^[n+1]) ((shiftZ^[n+1]) x)
    -- = (shiftZSymm^[n]) (shiftZSymm (shiftZ (shiftZ^[n] x)))
    -- = (shiftZSymm^[n]) (shiftZ^[n] x)        by shiftZSymm_shiftZ
    -- = x                                       by ih
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply']
    rw [shiftZSymm_shiftZ]
    exact ih

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α] in
/-- `shiftZSymm^n y i = y (i - n)`. -/
private lemma shiftZSymm_iterate_apply (n : ℕ) (y : ∀ _ : ℤ, α) (i : ℤ) :
    (shiftZSymm^[n]) y i = y (i - n) := by
  induction n generalizing i with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    show (shiftZSymm^[k] y) (i - 1) = y (i - (k + 1 : ℕ))
    rw [ih]
    congr 1
    push_cast; ring

omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- Coordinate projection `(· k)` is `negPastSigma`-measurable when `k ≤ -1`. -/
private lemma measurable_coord_negPastSigma {k : ℤ} (hk : k ≤ -1) :
    @Measurable _ _ (negPastSigma (α := α)) _ (fun y : (∀ _ : ℤ, α) => y k) := by
  -- `negPastSigma = cylinderEvents {i ≤ -1}`, so coord-k for k ≤ -1 is a generator.
  exact measurable_cylinderEvent_apply (X := fun _ : ℤ => α) (Δ := {i : ℤ | i ≤ -1})
    (i := k) hk

omit [DecidableEq α] [Nonempty α] in
/-- `MRatioLowerZ μ p n` is `shiftedPastSigma n`-measurable. Depends only on `x_0, …, x_{n-1}`,
which after `shift^n` lives at indices `-n, …, -1`. -/
private lemma measurable_MRatioLowerZ_shiftedPastSigma
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    @Measurable _ _ (shiftedPastSigma (α := α) n) _ (MRatioLowerZ μ p n) := by
  classical
  -- Factor MRatio(n) through shift^n: MRatio(n) x = G (shift^n x) where
  -- G y := MRatio(n) (shiftZSymm^[n] y). Show G is negPastSigma-measurable.
  set G : (∀ _ : ℤ, α) → ℝ≥0∞ := fun y => MRatioLowerZ μ p n (shiftZSymm^[n] y)
    with hG_def
  have h_factor : MRatioLowerZ μ p n = G ∘ shiftZ^[n] := by
    funext x
    show MRatioLowerZ μ p n x = MRatioLowerZ μ p n (shiftZSymm^[n] (shiftZ^[n] x))
    rw [shiftZSymm_iterate_shiftZ_iterate]
  refine measurable_shiftedPastSigma_of_eq_comp n _ ?_ h_factor
  -- Show G is negPastSigma-measurable: unfold and prove piece by piece.
  show @Measurable _ _ (negPastSigma (α := α)) _
    (fun y => MRatioLowerZ μ p n (shiftZSymm^[n] y))
  show @Measurable _ _ (negPastSigma (α := α)) _
    (fun y => ENNReal.ofReal (Real.exp (negLogQInftyZ μ p n (shiftZSymm^[n] y) -
      (n : ℝ) * blockLogAvgZ μ p n (shiftZSymm^[n] y))))
  refine ENNReal.measurable_ofReal.comp ?_
  refine Real.measurable_exp.comp ?_
  -- negLogQInftyZ - n · blockLogAvgZ at shiftZSymm^[n] y.
  refine Measurable.sub ?_ ?_
  · -- negLogQInftyZ n (shiftZSymm^[n] y) = ∑_{i<n} pmfLogCondInfty(shift^i(shiftZSymm^[n] y)).
    unfold negLogQInftyZ
    refine Finset.measurable_sum _ (fun i hi => ?_)
    have hi_lt : i < n := Finset.mem_range.mp hi
    -- pmfLogCondInfty(shift^i ∘ shiftZSymm^[n] y): depends on y at coords ≤ -1.
    -- Build by hand.
    show @Measurable _ _ (negPastSigma (α := α)) _
      (fun y => pmfLogCondInfty μ p (shiftZ^[i] (shiftZSymm^[n] y)))
    unfold pmfLogCondInfty
    refine (Real.measurable_log.comp ?_).neg
    refine Finset.measurable_sum _ (fun a _ => ?_)
    refine Measurable.mul ?_ ?_
    · -- indicator (coord0 ⁻¹' {a}) (1 : ℝ) at shift^i (shiftZSymm^[n] y)
      -- = if (shift^i (shiftZSymm^[n] y)) 0 = a then 1 else 0
      -- = if y (i - n) = a then 1 else 0.
      have h_coord_eq : ∀ y : ∀ _ : ℤ, α,
          coord0 (shiftZ^[i] (shiftZSymm^[n] y)) = y (((i : ℤ)) - (n : ℤ)) := by
        intro y
        show (shiftZ^[i] (shiftZSymm^[n] y)) 0 = y (((i : ℤ)) - (n : ℤ))
        rw [shiftZ_iterate_apply]
        show (shiftZSymm^[n] y) (0 + (i : ℤ)) = y (((i : ℤ)) - (n : ℤ))
        rw [shiftZSymm_iterate_apply]
        congr 1; ring
      have h_indicator_eq : ∀ y : ∀ _ : ℤ, α,
          Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ)) (shiftZ^[i] (shiftZSymm^[n] y))
            = Set.indicator (((fun y : (∀ _ : ℤ, α) => y (((i : ℤ)) - (n : ℤ))) ⁻¹' {a}))
                (fun _ => (1 : ℝ)) y := by
        intro y
        have h_cy := h_coord_eq y
        by_cases hy : (shiftZ^[i] (shiftZSymm^[n] y)) 0 = a
        · have hy' : y (((i : ℤ)) - (n : ℤ)) = a := by rw [← h_cy]; exact hy
          have h1 : shiftZ^[i] (shiftZSymm^[n] y) ∈ coord0 ⁻¹' {a} := hy
          have h2 : y ∈ ((fun y : (∀ _ : ℤ, α) => y (((i : ℤ)) - (n : ℤ))) ⁻¹' {a}) := hy'
          rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
        · have hy' : ¬ y (((i : ℤ)) - (n : ℤ)) = a := by rw [← h_cy]; exact hy
          have h1 : shiftZ^[i] (shiftZSymm^[n] y) ∉ coord0 ⁻¹' {a} := hy
          have h2 : y ∉ ((fun y : (∀ _ : ℤ, α) => y (((i : ℤ)) - (n : ℤ))) ⁻¹' {a}) := hy'
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      rw [show (fun y => Set.indicator (coord0 ⁻¹' {a}) (fun _ => (1 : ℝ))
              (shiftZ^[i] (shiftZSymm^[n] y)))
          = fun y => Set.indicator (((fun y : (∀ _ : ℤ, α) => y (((i : ℤ)) - (n : ℤ))) ⁻¹' {a}))
                (fun _ => (1 : ℝ)) y from funext h_indicator_eq]
      refine Measurable.indicator measurable_const ?_
      -- coord (i - n) for i < n is at index ≤ -1.
      have h_le : ((i : ℤ)) - (n : ℤ) ≤ -1 := by
        have : (i : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hi_lt
        linarith
      exact (measurable_coord_negPastSigma h_le) (measurableSet_singleton a)
    · -- condProbInfty μ p a (shift^i (shiftZSymm^[n] y)): rewrite as composition.
      -- For i < n: shift^i (shiftZSymm^[n] y) depends on y at indices ≤ -1.
      -- Strategy: use measurable_shiftedPastSigma_of_eq_comp style argument.
      -- Or: condProbInfty is negPastSigma-measurable on its arg, and shift^i ∘ shiftZSymm^[n]
      -- as a function (∀_:ℤ,α) → (∀_:ℤ,α) maps negPastSigma to negPastSigma when i < n.
      have h_cP_meas_negPast : @Measurable _ _ (negPastSigma (α := α)) _
          (condProbInfty μ p a) := by
        have h := (stronglyMeasurable_condProbInfty μ p a).measurable
        rw [show (⨆ k : ℕ, (pastFiltration (α := α)) k) = negPastSigma from
          iSup_pastSigma_eq_negPastSigma] at h
        exact h
      -- shift^i ∘ shiftZSymm^[n] is measurable as (negPastSigma) → (negPastSigma) for i < n.
      -- Use measurable_cylinderEvents_iff: it suffices that each coord-k for k ≤ -1
      -- composed gives a coord at index k + i - n ≤ -1, which is negPastSigma-measurable.
      have h_shift_comp_meas : @Measurable _ _ (negPastSigma (α := α)) (negPastSigma (α := α))
          (fun y : (∀ _ : ℤ, α) => shiftZ^[i] (shiftZSymm^[n] y)) := by
        refine measurable_cylinderEvents_iff.mpr ?_
        intro k hk
        -- Need: y ↦ (shiftZ^[i] (shiftZSymm^[n] y)) k is `negPastSigma`-measurable.
        have h_apply_eq : ∀ y : (∀ _ : ℤ, α),
            (shiftZ^[i] (shiftZSymm^[n] y)) k = y (k + (i : ℤ) - (n : ℤ)) := by
          intro y
          rw [shiftZ_iterate_apply, shiftZSymm_iterate_apply]
        rw [show (fun y : (∀ _ : ℤ, α) => (shiftZ^[i] (shiftZSymm^[n] y)) k)
            = fun y : (∀ _ : ℤ, α) => y (k + (i : ℤ) - (n : ℤ)) from funext h_apply_eq]
        have h_idx_le : k + (i : ℤ) - (n : ℤ) ≤ -1 := by
          have hi_lt' : (i : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hi_lt
          have hk_le : k ≤ -1 := hk
          linarith
        exact measurable_coord_negPastSigma h_idx_le
      exact h_cP_meas_negPast.comp h_shift_comp_meas
  · -- n · blockLogAvgZ n (shiftZSymm^[n] y) measurable.
    refine measurable_const.mul ?_
    unfold blockLogAvgZ
    refine measurable_const.mul ?_
    refine Real.measurable_log.comp ?_
    -- Goal: y ↦ ((μZ.map firstBlockZ n).real {firstBlockZ n (shiftZSymm^[n] y)}) is
    -- negPastSigma-measurable.
    -- The composition: y ↦ shiftZSymm^[n] y ↦ firstBlockZ n (shiftZSymm^[n] y) ↦ ...
    -- firstBlockZ n (shiftZSymm^[n] y) j = y (j.val - n : ℤ) for j ∈ Fin n.
    have h_disc : Measurable (fun s : Fin n → α =>
        (((μZ μ p).map (firstBlockZ (α := α) n)).real {s})) := measurable_of_finite _
    refine h_disc.comp ?_
    -- Now: y ↦ firstBlockZ n (shiftZSymm^[n] y) is negPastSigma → pi-measurable.
    show @Measurable _ _ (negPastSigma (α := α)) MeasurableSpace.pi
      (fun y => firstBlockZ (α := α) n (shiftZSymm^[n] y))
    refine (@measurable_pi_iff (∀ _ : ℤ, α) (Fin n) (fun _ => α) (negPastSigma (α := α))
      _ _).mpr ?_
    intro j
    -- (firstBlockZ n (shiftZSymm^[n] y)) j = (shiftZSymm^[n] y) (j.val : ℤ) = y ((j.val : ℤ) - n).
    show @Measurable _ _ (negPastSigma (α := α)) _ (fun y => firstBlockZ (α := α) n
      (shiftZSymm^[n] y) j)
    have h_eq : ∀ y : (∀ _ : ℤ, α),
        firstBlockZ (α := α) n (shiftZSymm^[n] y) j = y (((j.val : ℕ) : ℤ) - (n : ℤ)) := by
      intro y
      show (shiftZSymm^[n] y) ((j.val : ℕ) : ℤ) = y (((j.val : ℕ) : ℤ) - (n : ℤ))
      rw [shiftZSymm_iterate_apply]
    rw [show (fun y => firstBlockZ (α := α) n (shiftZSymm^[n] y) j)
        = fun y : (∀ _ : ℤ, α) => y (((j.val : ℕ) : ℤ) - (n : ℤ)) from funext h_eq]
    have h_idx_le : ((j.val : ℕ) : ℤ) - (n : ℤ) ≤ -1 := by
      have hj : j.val < n := j.isLt
      have hj' : (j.val : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hj
      linarith
    exact measurable_coord_negPastSigma h_idx_le

omit [DecidableEq α] [Nonempty α] in
/-- **Substep A — Tower identification**: the conditional Lebesgue expectation of
the ENNReal indicator `1_{x_n = a}` w.r.t. `shiftedPastSigma n` equals
`ofReal(condProbInfty(a)(shift^n x))` a.s.

Proof: by uniqueness of conditional Lebesgue expectation (`ae_eq_condLExp`).
The candidate is `shiftedPastSigma n`-measurable, and its integral on each
`s = (shift^n)⁻¹' t` matches the indicator's integral. The latter reduces (via
`MeasurePreserving.setLIntegral_comp_preimage`) to a real-valued condExp
identity `setIntegral_condExp` for `condProbInfty(a)`, converted to ENNReal via
`integral_eq_lintegral_of_nonneg_ae` + finiteness. -/
private lemma condLExp_indicator_coord_n_eq_ofReal_condProbInfty_shift
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) (a : α) :
    (fun x => ENNReal.ofReal (condProbInfty μ p a (shiftZ^[n] x)))
      =ᵐ[μZ μ p]
      (μZ μ p)⁻[((shiftZ^[n])⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))
        | shiftedPastSigma (α := α) n] := by
  classical
  have hm : (shiftedPastSigma (α := α) n) ≤ MeasurableSpace.pi := shiftedPastSigma_le n
  haveI : SigmaFinite ((μZ μ p).trim hm) := by
    haveI : IsFiniteMeasure ((μZ μ p).trim hm) := isFiniteMeasure_trim hm
    infer_instance
  -- Indicators in ℝ and ℝ≥0∞.
  set indR : (∀ _ : ℤ, α) → ℝ :=
    (coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ)) with hindR_def
  set indENN₀ : (∀ _ : ℤ, α) → ℝ≥0∞ :=
    (coord0 ⁻¹' {a}).indicator (fun _ => (1 : ℝ≥0∞)) with hindENN₀_def
  -- Candidate Y.
  set Y : (∀ _ : ℤ, α) → ℝ≥0∞ :=
    (fun x => ENNReal.ofReal (condProbInfty μ p a (shiftZ^[n] x))) with hY_def
  -- (i) Y is shiftedPastSigma n-measurable.
  have hY_meas : Measurable[shiftedPastSigma (α := α) n] Y :=
    ENNReal.measurable_ofReal.comp
      (measurable_condProbInfty_comp_shift_shiftedPastSigma μ p n a)
  -- Shift is measure-preserving.
  have h_mp_shift : MeasurePreserving (shiftZ^[n]) (μZ μ p) (μZ μ p) :=
    (measurePreserving_shiftZ μ p).iterate n
  -- Pointwise: indicator at shift = indicator at coord0, after shift.
  have h_indENN_factor : ∀ x : (∀ _ : ℤ, α),
      ((shiftZ^[n])⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞)) x
        = indENN₀ (shiftZ^[n] x) := by
    intro x
    by_cases hx : shiftZ^[n] x ∈ coord0 ⁻¹' {a}
    · have hx' : x ∈ (shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a}) := hx
      simp [indENN₀, Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    · have hx' : x ∉ (shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a}) := hx
      simp [indENN₀, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  -- Measurable maps for the lintegral_comp.
  have h_meas_condProbInfty : Measurable (condProbInfty μ p a) :=
    (stronglyMeasurable_condProbInfty μ p a).measurable.mono
      (iSup_le (fun k => (pastFiltration (α := α)).le k)) le_rfl
  have h_meas_ofReal_cP : Measurable (fun y => ENNReal.ofReal (condProbInfty μ p a y)) :=
    ENNReal.measurable_ofReal.comp h_meas_condProbInfty
  have h_indENN₀_meas : Measurable indENN₀ :=
    Measurable.indicator measurable_const (measurableSet_coord0_eq a)
  -- (ii) Set-integral equality on each s ∈ shiftedPastSigma n.
  refine ae_eq_condLExp hm (μZ μ p)
    (((shiftZ^[n])⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) hY_meas ?_
  intro s hs
  obtain ⟨t, ht_neg, hts⟩ := hs
  subst hts
  have h_meas_t_pi : MeasurableSet t :=
    cylinderEvents_le_pi (X := fun _ : ℤ => α) _ ht_neg
  -- LHS: ∫⁻ x in (shift^n)⁻¹' t, Y x ∂μZ = ∫⁻ y in t, ofReal(condProbInfty a y) ∂μZ.
  have h_LHS : ∫⁻ x in (shiftZ^[n]) ⁻¹' t, Y x ∂(μZ μ p)
      = ∫⁻ y in t, ENNReal.ofReal (condProbInfty μ p a y) ∂(μZ μ p) :=
    h_mp_shift.setLIntegral_comp_preimage h_meas_t_pi h_meas_ofReal_cP
  -- RHS: ∫⁻ x in (shift^n)⁻¹' t, indENN x ∂μZ = ∫⁻ y in t, indENN₀ y ∂μZ.
  have h_RHS :
      ∫⁻ x in (shiftZ^[n]) ⁻¹' t, ((shiftZ^[n])⁻¹' (coord0 ⁻¹' {a})).indicator
        (fun _ => (1 : ℝ≥0∞)) x ∂(μZ μ p)
        = ∫⁻ y in t, indENN₀ y ∂(μZ μ p) := by
    rw [show (fun x => ((shiftZ^[n])⁻¹' (coord0 ⁻¹' {a})).indicator
            (fun _ => (1 : ℝ≥0∞)) x)
        = fun x => indENN₀ (shiftZ^[n] x) from funext h_indENN_factor]
    exact h_mp_shift.setLIntegral_comp_preimage h_meas_t_pi h_indENN₀_meas
  rw [h_LHS, h_RHS]
  -- Reduce to real condExp identity for condProbInfty(a).
  have h_int_real : ∫ y in t, condProbInfty μ p a y ∂(μZ μ p)
      = ∫ y in t, indR y ∂(μZ μ p) := by
    have h_int_indR : Integrable indR (μZ μ p) := integrable_indicator_coord0_eq μ p a
    have h_condExp_eq :
        condProbInfty μ p a =ᵐ[μZ μ p] (μZ μ p)[indR | ⨆ k : ℕ, (pastFiltration (α := α)) k] :=
      condProbInfty_eq_condExp_tail μ p a
    have h_neg_le : (⨆ k : ℕ, (pastFiltration (α := α)) k) ≤ MeasurableSpace.pi := by
      rw [show (⨆ k : ℕ, (pastFiltration (α := α)) k) = negPastSigma from
        iSup_pastSigma_eq_negPastSigma]
      exact cylinderEvents_le_pi
    haveI : SigmaFinite ((μZ μ p).trim h_neg_le) := by
      haveI : IsFiniteMeasure ((μZ μ p).trim h_neg_le) := isFiniteMeasure_trim h_neg_le
      infer_instance
    have h_t_meas_iSup : MeasurableSet[⨆ k : ℕ, (pastFiltration (α := α)) k] t := by
      rw [show (⨆ k : ℕ, (pastFiltration (α := α)) k) = negPastSigma from
        iSup_pastSigma_eq_negPastSigma]
      exact ht_neg
    have h_setInt_condExp :
        ∫ y in t, ((μZ μ p)[indR | ⨆ k : ℕ, (pastFiltration (α := α)) k]) y ∂(μZ μ p)
          = ∫ y in t, indR y ∂(μZ μ p) :=
      setIntegral_condExp h_neg_le h_int_indR h_t_meas_iSup
    have h_setInt_cong :
        ∫ y in t, condProbInfty μ p a y ∂(μZ μ p)
          = ∫ y in t, ((μZ μ p)[indR | ⨆ k : ℕ, (pastFiltration (α := α)) k]) y ∂(μZ μ p) := by
      refine setIntegral_congr_ae h_meas_t_pi ?_
      filter_upwards [h_condExp_eq] with y hy _
      exact hy
    rw [h_setInt_cong, h_setInt_condExp]
  -- Convert real integral equality to lintegral equality.
  have h_cP_nn : 0 ≤ᵐ[μZ μ p] condProbInfty μ p a := ae_zero_le_condProbInfty μ p a
  have h_indR_nn : 0 ≤ᵐ[μZ μ p] indR :=
    Filter.Eventually.of_forall (fun x => indicator_coord0_eq_nonneg a x)
  have h_indR_int : Integrable indR (μZ μ p) := integrable_indicator_coord0_eq μ p a
  have h_cP_int : Integrable (condProbInfty μ p a) (μZ μ p) := by
    refine ⟨h_meas_condProbInfty.aestronglyMeasurable, ?_⟩
    have h_le : ∀ᵐ x ∂(μZ μ p), ‖condProbInfty μ p a x‖ ≤ 1 := by
      filter_upwards [h_cP_nn, ae_condProbInfty_le_one μ p a] with x hnn hle
      rw [Real.norm_of_nonneg hnn]; exact hle
    exact HasFiniteIntegral.of_bounded h_le
  have h_cP_nn_rest : 0 ≤ᵐ[(μZ μ p).restrict t] condProbInfty μ p a :=
    ae_restrict_of_ae h_cP_nn
  have h_indR_nn_rest : 0 ≤ᵐ[(μZ μ p).restrict t] indR := ae_restrict_of_ae h_indR_nn
  have h_int_cP_rest : Integrable (condProbInfty μ p a) ((μZ μ p).restrict t) :=
    h_cP_int.restrict
  have h_int_indR_rest : Integrable indR ((μZ μ p).restrict t) :=
    h_indR_int.restrict
  have h_eq_cP :
      ∫ y in t, condProbInfty μ p a y ∂(μZ μ p)
        = ENNReal.toReal (∫⁻ y in t, ENNReal.ofReal (condProbInfty μ p a y) ∂(μZ μ p)) := by
    rw [show (∫ y in t, condProbInfty μ p a y ∂(μZ μ p))
        = ∫ y, condProbInfty μ p a y ∂((μZ μ p).restrict t) from rfl]
    rw [integral_eq_lintegral_of_nonneg_ae h_cP_nn_rest
      h_int_cP_rest.aestronglyMeasurable]
  have h_eq_indR :
      ∫ y in t, indR y ∂(μZ μ p)
        = ENNReal.toReal (∫⁻ y in t, ENNReal.ofReal (indR y) ∂(μZ μ p)) := by
    rw [show (∫ y in t, indR y ∂(μZ μ p))
        = ∫ y, indR y ∂((μZ μ p).restrict t) from rfl]
    rw [integral_eq_lintegral_of_nonneg_ae h_indR_nn_rest
      h_int_indR_rest.aestronglyMeasurable]
  -- Finiteness of both lintegrals.
  have h_lint_cP_ne :
      ∫⁻ y in t, ENNReal.ofReal (condProbInfty μ p a y) ∂(μZ μ p) ≠ ∞ := by
    have h_le : ∀ᵐ y ∂((μZ μ p).restrict t),
        ENNReal.ofReal (condProbInfty μ p a y) ≤ 1 := by
      have h_le_one_rest : ∀ᵐ y ∂((μZ μ p).restrict t),
          condProbInfty μ p a y ≤ 1 := ae_restrict_of_ae (ae_condProbInfty_le_one μ p a)
      filter_upwards [h_le_one_rest] with y hy
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal hy
    have h_bound :
        ∫⁻ y in t, ENNReal.ofReal (condProbInfty μ p a y) ∂(μZ μ p) ≤ ∫⁻ _ in t, 1 ∂(μZ μ p) :=
      lintegral_mono_ae h_le
    have h_finite : ∫⁻ _ in t, (1 : ℝ≥0∞) ∂(μZ μ p) < ∞ := by
      simp only [MeasureTheory.lintegral_const, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, one_mul]
      exact measure_lt_top _ _
    exact (h_bound.trans_lt h_finite).ne
  have h_lint_indR_ne :
      ∫⁻ y in t, ENNReal.ofReal (indR y) ∂(μZ μ p) ≠ ∞ := by
    have h_le : ∀ᵐ y ∂((μZ μ p).restrict t),
        ENNReal.ofReal (indR y) ≤ 1 := by
      filter_upwards with y
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
      exact ENNReal.ofReal_le_ofReal (indicator_coord0_eq_le_one a y)
    have h_bound :
        ∫⁻ y in t, ENNReal.ofReal (indR y) ∂(μZ μ p) ≤ ∫⁻ _ in t, 1 ∂(μZ μ p) :=
      lintegral_mono_ae h_le
    have h_finite : ∫⁻ _ in t, (1 : ℝ≥0∞) ∂(μZ μ p) < ∞ := by
      simp only [MeasureTheory.lintegral_const, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, one_mul]
      exact measure_lt_top _ _
    exact (h_bound.trans_lt h_finite).ne
  have h_lintegral_eq :
      ∫⁻ y in t, ENNReal.ofReal (condProbInfty μ p a y) ∂(μZ μ p)
        = ∫⁻ y in t, ENNReal.ofReal (indR y) ∂(μZ μ p) := by
    have h_eq_toReal :
        ENNReal.toReal (∫⁻ y in t, ENNReal.ofReal (condProbInfty μ p a y) ∂(μZ μ p))
          = ENNReal.toReal (∫⁻ y in t, ENNReal.ofReal (indR y) ∂(μZ μ p)) := by
      rw [← h_eq_cP, ← h_eq_indR, h_int_real]
    exact (ENNReal.toReal_eq_toReal_iff' h_lint_cP_ne h_lint_indR_ne).mp h_eq_toReal
  rw [h_lintegral_eq]
  refine lintegral_congr_ae ?_
  filter_upwards with y
  by_cases hy : y ∈ coord0 ⁻¹' {a}
  · simp [indR, indENN₀, Set.indicator_of_mem hy]
  · simp [indR, indENN₀, Set.indicator_of_notMem hy]

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Indicator-support collapse**: on the set `{x_n = a}`, the factor
`exp(pmfLogCondInfty(shift^n x))` equals `1/condProbInfty(a)(shift^n x)`
(in ℝ; with `1/0 = 0`). Formulated as an indicator-times-factor pointwise identity. -/
private lemma indicator_mul_ofReal_exp_pmf_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) (a : α)
    (x : ∀ _ : ℤ, α) :
    (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
        * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)))
      = (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
        * ENNReal.ofReal (Real.exp (-Real.log (condProbInfty μ p a (shiftZ^[n] x)))) := by
  by_cases hx : x ∈ (shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})
  · -- coord0(shift^n x) = a; pmfLogCondInfty(shift^n x) = -log(condProbInfty(a)(shift^n x)).
    have h_coord : coord0 (shiftZ^[n] x) = a := hx
    have h_pmf_eq : pmfLogCondInfty μ p (shiftZ^[n] x)
        = -Real.log (condProbInfty μ p a (shiftZ^[n] x)) := by
      unfold pmfLogCondInfty
      rw [pmfLogCondPast_inner_eq_self
        (fun a' => condProbInfty μ p a' (shiftZ^[n] x)) (shiftZ^[n] x)]
      rw [h_coord]
    rw [h_pmf_eq]
  · -- Off support: indicator = 0, both sides 0.
    rw [Set.indicator_of_notMem hx]
    simp

omit [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] in
/-- **Reciprocal product bound**: `ofReal(exp(-log c)) · ofReal(c) ≤ 1` for any real `c`.
- When `c > 0`: `exp(-log c) · c = 1`, so product = 1.
- When `c ≤ 0`: `ofReal(c) = 0`, so product = 0.
-/
private lemma ofReal_exp_neg_log_mul_ofReal_le_one (c : ℝ) :
    ENNReal.ofReal (Real.exp (-Real.log c)) * ENNReal.ofReal c ≤ 1 := by
  by_cases hc_pos : 0 < c
  · have h_eq : Real.exp (-Real.log c) * c = 1 := by
      rw [Real.exp_neg, Real.exp_log hc_pos]
      exact inv_mul_cancel₀ hc_pos.ne'
    have h_exp_nn : 0 ≤ Real.exp (-Real.log c) := (Real.exp_pos _).le
    rw [← ENNReal.ofReal_mul h_exp_nn, h_eq, ENNReal.ofReal_one]
  · have hc_le : c ≤ 0 := not_lt.mp hc_pos
    rw [show ENNReal.ofReal c = 0 from ENNReal.ofReal_of_nonpos hc_le, mul_zero]
    exact zero_le_one

omit [DecidableEq α] [Nonempty α] in
lemma measurable_pmfLogCondInfty
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) :
    Measurable (pmfLogCondInfty μ p) := by
  classical
  unfold pmfLogCondInfty
  refine (Real.measurable_log.comp ?_).neg
  refine Finset.measurable_sum _ (fun a _ => ?_)
  refine Measurable.mul ?_ ?_
  · refine Measurable.indicator measurable_const ?_
    exact measurableSet_coord0_eq a
  · exact ((stronglyMeasurable_condProbInfty μ p a).mono
      (iSup_le (fun n => (pastFiltration (α := α)).le n))).measurable

omit [DecidableEq α] [Nonempty α] in
lemma measurable_MRatioLowerZ
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    Measurable (MRatioLowerZ μ p n) := by
  classical
  unfold MRatioLowerZ
  refine ENNReal.measurable_ofReal.comp ?_
  refine Real.measurable_exp.comp ?_
  refine Measurable.sub ?_ ?_
  · unfold negLogQInftyZ
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (measurable_pmfLogCondInfty μ p).comp ((measurable_shiftZ).iterate i)
  · refine measurable_const.mul ?_
    unfold blockLogAvgZ
    refine measurable_const.mul ?_
    refine Real.measurable_log.comp ?_
    have h_disc : Measurable (fun y : Fin n → α =>
        (((μZ μ p).map (firstBlockZ (α := α) n)).real {y})) := measurable_of_finite _
    exact h_disc.comp (measurable_firstBlockZ n)

omit [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma eq_sum_indicator_preimage_mul {β : Type*} (φ : β → α) (x : β)
    (f : α → ℝ≥0∞) :
    f (φ x) = ∑ a, ((φ ⁻¹' {a}).indicator (fun _ => (1 : ℝ≥0∞))) x * f a := by
  classical
  rw [Finset.sum_eq_single (φ x)]
  · rw [Set.indicator_of_mem (by rfl : x ∈ φ ⁻¹' {φ x}), one_mul]
  · intro b _ hb
    rw [Set.indicator_of_notMem (by intro hx; exact hb hx.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [DecidableEq α] [Nonempty α] in
/-- **CORE LEMMA (tower property)**: `∫ MRatioLowerZ n dμZ ≤ 1`. -/
theorem integral_MRatioLowerZ_le_one
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (n : ℕ) :
    ∫⁻ x, MRatioLowerZ μ p n x ∂(μZ μ p) ≤ 1 := by
  induction n with
  | zero =>
    have h_const : ∀ x, MRatioLowerZ μ p 0 x = 1 := by
      intro x
      unfold MRatioLowerZ negLogQInftyZ blockLogAvgZ
      simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, sub_zero,
        Real.exp_zero, ENNReal.ofReal_one]
    have h_int_eq : ∫⁻ x, MRatioLowerZ μ p 0 x ∂(μZ μ p) = 1 := by
      calc ∫⁻ x, MRatioLowerZ μ p 0 x ∂(μZ μ p)
          = ∫⁻ _, (1 : ℝ≥0∞) ∂(μZ μ p) := by
            refine lintegral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun x => by rw [h_const x])
        _ = (μZ μ p) Set.univ := by rw [lintegral_one]
        _ = 1 := measure_univ
    rw [h_int_eq]
  | succ n ih =>
    -- **Inductive step** (Algoet–Cover tower argument).
    --
    -- All infrastructure helpers are in this file:
    --   * `MRatioLowerZ_succ_eq_mul`: pointwise factorization
    --       `MRatioLowerZ (n+1) x = MRatioLowerZ n x · ofReal(blockCondRatio) · ofReal(exp pmf)`
    --       (a.e. on the positive set).
    --   * `sum_blockCondRatio`: `∑_a blockCondRatio = 1` on the positive set.
    --   * `firstBlockZ_singleton_pos_ae`: `P_n^Z > 0` a.s.
    --   * `lintegral_mul_eq_lintegral_mul_condLExp`: general ENNReal pull-out
    --       `∫⁻ g · f dμ = ∫⁻ g · μ⁻[f|m] dμ` for `m`-measurable `g`.
    --   * `shiftedPastSigma n := negPastSigma.comap shift^n`: the relevant sub-σ-algebra.
    --
    -- **Remaining glue work (~150 LOC, deferred to next pass)**:
    --
    --   (a) Tower identification: combine `condExp_comp_measurePreserving` (from
    --       `TwoSidedExtension.lean`) with `condProbInfty_eq_condExp_tail` to get
    --       `μZ⁻[(coord_n=a).indicator (1 : ℝ≥0∞) | shiftedPastSigma n] x
    --          =ᵐ ENNReal.ofReal (condProbInfty(a)(shift^n x))`. Goes through
    --       `toReal_condLExp` bridge between real `condExp` and ENNReal `condLExp`.
    --
    --   (b) On positive set: `ofReal(exp(pmfLogCondInfty y)) · ofReal(condProbInfty (coord0 y) y) = 1`,
    --       i.e., `pmf inverse = condProb`. Direct from the definition of `pmfLogCondInfty`
    --       (using `pmfLogCondPast_inner_eq_self`).
    --
    --   (c) Combine via:
    --       ```
    --       ∫⁻ MRatioLowerZ (n+1) dμZ
    --         = ∫⁻ ∑_a [coord_n=a] · MRatioLowerZ n · ofReal(ratio_a/condProbInfty) dμZ  -- by (a),(b),decomp
    --         = ∑_a ∫⁻ [coord_n=a] · (factor_a) dμZ                                       -- finset sum/integral commute
    --         = ∑_a ∫⁻ μZ⁻[[coord_n=a]|F_n] · (factor_a) dμZ                              -- pull-out
    --         = ∑_a ∫⁻ ofReal(condProbInfty(a)(shift^n)) · (factor_a) dμZ                 -- tower id (a)
    --         = ∑_a ∫⁻ MRatioLowerZ n · ofReal(ratio_a) dμZ                               -- cancellation
    --         = ∫⁻ MRatioLowerZ n · ofReal(∑_a ratio_a) dμZ                               -- finset sum
    --         ≤ ∫⁻ MRatioLowerZ n dμZ                                                     -- ∑ ratio_a = 1
    --         ≤ 1                                                                          -- by ih
    --       ```
    --
    -- Reference: Algoet–Cover (1988), Sandwich Theorem proof.
    classical
    -- Shorthand for the per-a integrand.
    set F : α → (∀ _ : ℤ, α) → ℝ≥0∞ := fun a x =>
      (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
        * MRatioLowerZ μ p n x
        * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
        * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x))) with hF_def
    -- Step 1: pointwise (a.s.) decomposition `MRatio(n+1) =ᵐ ∑_a F a`.
    have h_pmf_meas : Measurable
        (fun x : (∀ _ : ℤ, α) => Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x))) :=
      Real.measurable_exp.comp ((measurable_pmfLogCondInfty μ p).comp
        (measurable_shiftZ.iterate n))
    have h_MR_meas : ∀ k, Measurable (MRatioLowerZ μ p k) :=
      fun k => measurable_MRatioLowerZ μ p k
    -- All a.s. statements collected up front.
    have h_decomp : ∀ᵐ x ∂(μZ μ p),
        MRatioLowerZ μ p (n + 1) x = ∑ a, F a x := by
      have h_pos_n := firstBlockZ_singleton_pos_ae μ p n
      have h_pos_succ := firstBlockZ_singleton_pos_ae μ p (n + 1)
      filter_upwards [h_pos_n, h_pos_succ] with x hpn hpsucc
      have h_succ := MRatioLowerZ_succ_eq_mul μ p n x hpn hpsucc
      -- Rewrite the RHS of h_succ using `x (n : ℤ) = coord0(shift^n x)`.
      have h_coord_n : x (n : ℤ) = coord0 (shiftZ^[n] x) := by
        show x (n : ℤ) = (shiftZ^[n] x) 0
        rw [shiftZ_iterate_apply]
        congr 1; simp
      -- Decompose: f(coord0(shift^n x)) = ∑_a 1[coord0(shift^n x) = a] · f(a).
      -- Pull this through: MRatio · ofReal(ratio_{coord0 shift^n x}) · ofReal(exp pmf)
      --    = ∑_a 1[coord0(shift^n x) = a] · MRatio · ofReal(ratio_a) · ofReal(exp pmf).
      rw [h_succ, h_coord_n]
      -- Goal: MRatio n x · ofReal(blockCondRatio n (firstBlockZ n x) (coord0(shift^n x)))
      --       · ofReal(exp pmf shift^n x)
      --     = ∑ a, F a x
      have h_sum_indicator :
          ∀ (f : α → ℝ≥0∞),
            f (coord0 (shiftZ^[n] x))
              = ∑ a, (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
                  * f a :=
        fun f => eq_sum_indicator_preimage_mul (fun y => coord0 (shiftZ^[n] y)) x f
      -- Apply h_sum_indicator with f a := ofReal(blockCondRatio ... a) · ofReal(exp pmf shift^n x).
      -- Then re-associate the multiplication.
      have h_combined :
          ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) (coord0 (shiftZ^[n] x)))
            * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)))
            = ∑ a, (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
                * (ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
                  * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)))) := by
        have := h_sum_indicator (fun a =>
          ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
            * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x))))
        exact this
      rw [show MRatioLowerZ μ p n x
            * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) (coord0 (shiftZ^[n] x)))
            * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)))
          = MRatioLowerZ μ p n x
            * (ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) (coord0 (shiftZ^[n] x)))
              * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)))) by ring]
      rw [h_combined]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      show MRatioLowerZ μ p n x
            * ((((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
              * (ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
                * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)))))
          = (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
            * MRatioLowerZ μ p n x
            * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
            * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)))
      ring
    -- Step 2: bound each summand.
    have h_per_a : ∀ a : α,
        ∫⁻ x, F a x ∂(μZ μ p)
          ≤ ∫⁻ x, MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a) ∂(μZ μ p) := by
      intro a
      -- Rewrite F a x using indicator-support collapse: replace exp(pmf shift^n)
      -- with exp(-log condProbInfty(a) shift^n) on the support.
      have h_F_rewrite : ∀ x, F a x =
          (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
            * MRatioLowerZ μ p n x
            * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
            * ENNReal.ofReal (Real.exp
                (-Real.log (condProbInfty μ p a (shiftZ^[n] x)))) := by
        intro x
        show (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
              * MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
              * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x))) = _
        have h := indicator_mul_ofReal_exp_pmf_eq μ p n a x
        rw [show (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
              * MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
              * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)))
            = MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
              * ((((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
                * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x)))) by ring]
        rw [h]
        ring
      rw [lintegral_congr_ae (Filter.Eventually.of_forall h_F_rewrite)]
      -- Now express integrand as g(x) · 1[x n = a](x), with g := MRatio(n) · ratio_a · exp(-log c_a shift^n).
      set g : (∀ _ : ℤ, α) → ℝ≥0∞ := fun x =>
        MRatioLowerZ μ p n x
          * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
          * ENNReal.ofReal (Real.exp
              (-Real.log (condProbInfty μ p a (shiftZ^[n] x)))) with hg_def
      have h_g_meas_m : Measurable[shiftedPastSigma (α := α) n] g := by
        show @Measurable _ _ (shiftedPastSigma (α := α) n) _
          (fun x => MRatioLowerZ μ p n x
            * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
            * ENNReal.ofReal (Real.exp
                (-Real.log (condProbInfty μ p a (shiftZ^[n] x)))))
        refine Measurable.mul ?_ ?_
        · refine Measurable.mul ?_ ?_
          · exact measurable_MRatioLowerZ_shiftedPastSigma μ p n
          · -- ofReal(blockCondRatio n (firstBlockZ n x) a): m-measurable.
            refine ENNReal.measurable_ofReal.comp ?_
            -- blockCondRatio(·, a) ∘ firstBlockZ n: m-measurable.
            refine (measurable_blockCondRatio_apply μ p n a).comp ?_
            -- firstBlockZ n is m-measurable.
            -- (Factor through shift^n: firstBlockZ n x = (j ↦ x j) for j < n, and
            -- on shifted side coords are -n..-1.)
            show @Measurable _ _ (shiftedPastSigma (α := α) n) _ (firstBlockZ (α := α) n)
            refine (@measurable_pi_iff (∀ _ : ℤ, α) (Fin n) (fun _ => α)
              (shiftedPastSigma (α := α) n) _ _).mpr ?_
            intro j
            -- firstBlockZ n x j = x (j.val : ℤ). After shift^n: shift^n x (j.val - n).
            show @Measurable _ _ (shiftedPastSigma (α := α) n) _
              (fun x : (∀ _ : ℤ, α) => firstBlockZ (α := α) n x j)
            show @Measurable _ _ (shiftedPastSigma (α := α) n) _
              (fun x : (∀ _ : ℤ, α) => x ((j.val : ℕ) : ℤ))
            refine measurable_shiftedPastSigma_of_eq_comp n _
              (g := fun y : (∀ _ : ℤ, α) => y (((j.val : ℕ) : ℤ) - (n : ℤ))) ?_ ?_
            · -- coord (j.val - n) for j < n: index ≤ -1, so negPastSigma-measurable.
              have h_idx_le : ((j.val : ℕ) : ℤ) - (n : ℤ) ≤ -1 := by
                have hj : j.val < n := j.isLt
                have hj' : (j.val : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hj
                linarith
              exact measurable_coord_negPastSigma h_idx_le
            · funext x
              show x ((j.val : ℕ) : ℤ) = (shiftZ^[n] x) (((j.val : ℕ) : ℤ) - (n : ℤ))
              rw [shiftZ_iterate_apply]
              congr 1; ring
        · -- ofReal(exp(-log condProbInfty(a)(shift^n x))): m-measurable.
          refine ENNReal.measurable_ofReal.comp ?_
          refine Real.measurable_exp.comp ?_
          refine Measurable.neg ?_
          refine Real.measurable_log.comp ?_
          exact measurable_condProbInfty_comp_shift_shiftedPastSigma μ p n a
      have h_indicator_meas : @Measurable _ _ MeasurableSpace.pi _
          (fun x : (∀ _ : ℤ, α) =>
            (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x) := by
        refine Measurable.indicator measurable_const ?_
        exact ((measurable_shiftZ).iterate n) (measurableSet_coord0_eq a)
      -- Pull out via lintegral_mul_eq_lintegral_mul_condLExp.
      have h_pull_out :
          ∫⁻ x, g x * (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator
              (fun _ => (1 : ℝ≥0∞))) x ∂(μZ μ p)
            = ∫⁻ x, g x * ((μZ μ p)⁻[
                (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞)))
                  | shiftedPastSigma (α := α) n] x) ∂(μZ μ p) := by
        haveI : SigmaFinite ((μZ μ p).trim (shiftedPastSigma_le n)) := by
          haveI : IsFiniteMeasure ((μZ μ p).trim (shiftedPastSigma_le n)) :=
            isFiniteMeasure_trim _
          infer_instance
        exact lintegral_mul_eq_lintegral_mul_condLExp (shiftedPastSigma_le n)
          (μZ μ p) h_g_meas_m h_indicator_meas
      -- The integrand: g x · indicator x. Compare to F a x: F a x = indicator x · MRatio · ratio · exp(...)
      -- After rewrite, it's indicator · g.
      rw [show (fun x => (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
            * MRatioLowerZ μ p n x
            * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
            * ENNReal.ofReal (Real.exp (-Real.log (condProbInfty μ p a (shiftZ^[n] x)))))
        = fun x => g x
          * (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x from
        funext (fun x => by
          show (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
                * MRatioLowerZ μ p n x
                * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
                * ENNReal.ofReal (Real.exp
                    (-Real.log (condProbInfty μ p a (shiftZ^[n] x))))
              = (MRatioLowerZ μ p n x
                  * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
                  * ENNReal.ofReal (Real.exp
                      (-Real.log (condProbInfty μ p a (shiftZ^[n] x)))))
                * (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
          ring)]
      rw [h_pull_out]
      -- Substitute the condLExp via substep A.
      have h_subA := condLExp_indicator_coord_n_eq_ofReal_condProbInfty_shift μ p n a
      have h_lint_eq :
          ∫⁻ x, g x * ((μZ μ p)⁻[
              (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞)))
                | shiftedPastSigma (α := α) n] x) ∂(μZ μ p)
            = ∫⁻ x, g x
                * ENNReal.ofReal (condProbInfty μ p a (shiftZ^[n] x)) ∂(μZ μ p) := by
        refine lintegral_congr_ae ?_
        filter_upwards [h_subA] with x hx
        rw [hx]
      rw [h_lint_eq]
      -- Now bound: g x · ofReal(c_a(shift^n x)) ≤ MRatio(n) · ofReal(ratio_a).
      -- This is by the reciprocal product bound on the exp(-log c) · c factor.
      refine lintegral_mono_ae ?_
      filter_upwards with x
      -- Goal: g x · ofReal(c_a) ≤ MRatio(n) x · ofReal(ratio_a).
      -- Recall g x = MRatio(n) x · ofReal(ratio_a) · ofReal(exp(-log c_a(shift^n))).
      show (MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
              * ENNReal.ofReal (Real.exp
                  (-Real.log (condProbInfty μ p a (shiftZ^[n] x)))))
            * ENNReal.ofReal (condProbInfty μ p a (shiftZ^[n] x))
          ≤ MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
      rw [show MRatioLowerZ μ p n x
            * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
            * ENNReal.ofReal (Real.exp (-Real.log (condProbInfty μ p a (shiftZ^[n] x))))
            * ENNReal.ofReal (condProbInfty μ p a (shiftZ^[n] x))
          = MRatioLowerZ μ p n x
            * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
            * (ENNReal.ofReal (Real.exp (-Real.log (condProbInfty μ p a (shiftZ^[n] x))))
              * ENNReal.ofReal (condProbInfty μ p a (shiftZ^[n] x))) by ring]
      calc MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
              * (ENNReal.ofReal (Real.exp (-Real.log
                  (condProbInfty μ p a (shiftZ^[n] x))))
                * ENNReal.ofReal (condProbInfty μ p a (shiftZ^[n] x)))
          ≤ MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by simp)
            exact ofReal_exp_neg_log_mul_ofReal_le_one _
        _ = MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a) := by rw [mul_one]
    -- Step 3: assemble.
    -- ∫⁻ MRatio(n+1) = ∫⁻ ∑_a F a = ∑_a ∫⁻ F a ≤ ∑_a ∫⁻ MRatio(n) · ratio_a
    --                = ∫⁻ MRatio(n) · (∑_a ratio_a) = ∫⁻ MRatio(n) ≤ 1.
    calc ∫⁻ x, MRatioLowerZ μ p (n + 1) x ∂(μZ μ p)
        = ∫⁻ x, ∑ a, F a x ∂(μZ μ p) := lintegral_congr_ae h_decomp
      _ = ∑ a, ∫⁻ x, F a x ∂(μZ μ p) := by
          rw [MeasureTheory.lintegral_finsetSum]
          intro a _
          -- Measurability of F a x as m₀-measurable. F a x is a product of 4 factors.
          show Measurable (fun x =>
            (((shiftZ^[n]) ⁻¹' (coord0 ⁻¹' {a})).indicator (fun _ => (1 : ℝ≥0∞))) x
              * MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a)
              * ENNReal.ofReal (Real.exp (pmfLogCondInfty μ p (shiftZ^[n] x))))
          refine Measurable.mul ?_ ?_
          · refine Measurable.mul ?_ ?_
            · refine Measurable.mul ?_ ?_
              · refine Measurable.indicator measurable_const ?_
                exact ((measurable_shiftZ).iterate n) (measurableSet_coord0_eq a)
              · exact h_MR_meas n
            · refine ENNReal.measurable_ofReal.comp ?_
              refine (measurable_blockCondRatio_apply μ p n a).comp ?_
              exact measurable_firstBlockZ n
          · exact ENNReal.measurable_ofReal.comp h_pmf_meas
      _ ≤ ∑ a, ∫⁻ x, MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a) ∂(μZ μ p) :=
            Finset.sum_le_sum (fun a _ => h_per_a a)
      _ = ∫⁻ x, ∑ a, MRatioLowerZ μ p n x
              * ENNReal.ofReal (blockCondRatio μ p n (firstBlockZ n x) a) ∂(μZ μ p) := by
          rw [MeasureTheory.lintegral_finsetSum]
          intro a _
          refine Measurable.mul (h_MR_meas n) ?_
          refine ENNReal.measurable_ofReal.comp ?_
          refine (measurable_blockCondRatio_apply μ p n a).comp ?_
          exact measurable_firstBlockZ n
      _ = ∫⁻ x, MRatioLowerZ μ p n x *
              ENNReal.ofReal (∑ a, blockCondRatio μ p n (firstBlockZ n x) a) ∂(μZ μ p) := by
          refine lintegral_congr_ae ?_
          filter_upwards with x
          rw [← Finset.mul_sum]
          congr 1
          -- ofReal commutes with finite non-negative sum.
          rw [← ENNReal.ofReal_sum_of_nonneg]
          intro a _
          -- blockCondRatio is ≥ 0: either 0 (when Pn = 0) or Psucc/Pn ≥ 0.
          show 0 ≤ if ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x} = 0 then 0
              else ((μZ μ p).map (firstBlockZ (α := α) (n + 1))).real
                {Fin.snoc (firstBlockZ n x) a} /
                  ((μZ μ p).map (firstBlockZ (α := α) n)).real {firstBlockZ n x}
          split_ifs with hpn
          · rfl
          · exact div_nonneg measureReal_nonneg measureReal_nonneg
      _ ≤ ∫⁻ x, MRatioLowerZ μ p n x ∂(μZ μ p) := by
          refine lintegral_mono_ae ?_
          filter_upwards [firstBlockZ_singleton_pos_ae μ p n] with x hpn
          rw [sum_blockCondRatio μ p n (firstBlockZ n x) hpn]
          rw [ENNReal.ofReal_one, mul_one]
      _ ≤ 1 := ih

end InformationTheory.Shannon
