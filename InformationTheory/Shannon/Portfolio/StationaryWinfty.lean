import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bases
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Topology.Order.MonotoneConvergence
import InformationTheory.Shannon.Portfolio.StationaryMarket

/-!
# Measurable selection of a log-optimal portfolio (Cover–Thomas §16.5)

Gateway lemma for the stationary-market `W_∞` AEP (Theorem 16.5.1): a concave Carathéodory
objective (measurable in the sample point, continuous and concave in the portfolio) admits a
measurable selection of an argmax over the standard simplex. This is a measurable-maximum
theorem. Mathlib has no ready measurable-selection lemma (see
`Mathlib/Probability/Decision/BayesEstimator.lean`, which notes selection theorems are not yet
in Mathlib), so the selector is self-built by strictly-concave (Tikhonov) regularization: for
each `ε > 0` the perturbed objective `F ω · − ε ‖·‖²` has a unique maximizer `bEps ε ω`, which
is measurable as a limit of finite near-maximizers; letting `ε → 0` gives a measurable genuine
maximizer of `F ω` (the point of the argmax set nearest the origin).

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed.), Wiley, 2006.
  §16.5.
-/

namespace InformationTheory.Shannon.Portfolio

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal

section MeasurableArgmax

variable {Ω : Type*} [MeasurableSpace Ω]
variable {m : ℕ}

/-- Strictly-convex Tikhonov regularizer `‖b‖²` (squared Euclidean norm on `Fin m → ℝ`). -/
private def qReg (b : Fin m → ℝ) : ℝ := ∑ i, b i ^ 2

private theorem qReg_continuous : Continuous (qReg (m := m)) := by
  unfold qReg
  exact continuous_finsetSum _ fun i _ ↦ (continuous_apply i).pow 2

-- The regularizer is strictly convex on the (convex) simplex.
private theorem qReg_strictConvexOn :
    StrictConvexOn ℝ (stdSimplex ℝ (Fin m)) (qReg (m := m)) := by
  refine ⟨convex_stdSimplex ℝ (Fin m), ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hb1 : b = 1 - a := by linarith
  subst hb1
  simp only [qReg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro i _
    nlinarith [mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (x i - y i))]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    exact ⟨i, Finset.mem_univ i,
      by nlinarith [mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr hi))]⟩

-- The Tikhonov-regularized objective is strictly concave on the simplex.
omit [MeasurableSpace Ω] in
private theorem gEps_strictConcaveOn (F : Ω → (Fin m → ℝ) → ℝ)
    (hF_conc : ∀ ω, ConcaveOn ℝ (stdSimplex ℝ (Fin m)) (F ω)) {ε : ℝ} (hε : 0 < ε) (ω : Ω) :
    StrictConcaveOn ℝ (stdSimplex ℝ (Fin m)) (fun b ↦ F ω b - ε * qReg b) := by
  have hqc : StrictConvexOn ℝ (stdSimplex ℝ (Fin m)) (fun b ↦ ε * qReg b) := by
    refine ⟨qReg_strictConvexOn.1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have h := qReg_strictConvexOn.2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at h ⊢
    nlinarith [mul_lt_mul_of_pos_left h hε]
  have hcc : StrictConcaveOn ℝ (stdSimplex ℝ (Fin m)) (fun b ↦ -(ε * qReg b)) := hqc.neg
  have hadd := (hF_conc ω).add_strictConcaveOn hcc
  have heq : (fun b ↦ F ω b - ε * qReg b) = (F ω) + fun b ↦ -(ε * qReg b) := by
    funext b; simp [sub_eq_add_neg]
  rw [heq]; exact hadd

-- For fixed `ε > 0`: a measurable selection of the (unique) maximizer of the regularized
-- objective `F ω · − ε ‖·‖²` over the simplex (measurable as a limit of finite near-maximizers).
private theorem exists_measurable_argmax_gEps
    (F : Ω → (Fin m → ℝ) → ℝ) [Nonempty (Fin m)]
    (hF_meas : ∀ b : Fin m → ℝ, Measurable (fun ω ↦ F ω b))
    (hF_cont : ∀ ω, ContinuousOn (F ω) (stdSimplex ℝ (Fin m)))
    (hF_conc : ∀ ω, ConcaveOn ℝ (stdSimplex ℝ (Fin m)) (F ω))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ bEps : Ω → (Fin m → ℝ), Measurable bEps ∧
      (∀ ω, bEps ω ∈ stdSimplex ℝ (Fin m)) ∧
      (∀ ω, IsMaxOn (fun b ↦ F ω b - ε * qReg b) (stdSimplex ℝ (Fin m)) (bEps ω)) := by
  classical
  set S := stdSimplex ℝ (Fin m) with hS
  have hS_compact : IsCompact S := isCompact_stdSimplex ℝ (Fin m)
  have hS_ne : S.Nonempty := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary (Fin m))⟩
  -- the regularized objective `g ω`, continuous and strictly concave on `S`
  have hg_cont : ∀ ω, ContinuousOn (fun b ↦ F ω b - ε * qReg b) S := fun ω ↦
    (hF_cont ω).sub ((continuous_const.mul qReg_continuous).continuousOn)
  have hg_sconc : ∀ ω, StrictConcaveOn ℝ S (fun b ↦ F ω b - ε * qReg b) :=
    fun ω ↦ gEps_strictConcaveOn F hF_conc hε ω
  -- unique maximizer of `g ω` on `S`
  have hmax : ∀ ω, ∃ z ∈ S, IsMaxOn (fun b ↦ F ω b - ε * qReg b) S z := fun ω ↦
    hS_compact.exists_isMaxOn hS_ne (hg_cont ω)
  set bEps : Ω → (Fin m → ℝ) := fun ω ↦ (hmax ω).choose with hbEps_def
  have hbEps_mem : ∀ ω, bEps ω ∈ S := fun ω ↦ (hmax ω).choose_spec.1
  have hbEps_max : ∀ ω, IsMaxOn (fun b ↦ F ω b - ε * qReg b) S (bEps ω) := fun ω ↦
    (hmax ω).choose_spec.2
  -- countable dense sequence in `S`
  haveI : Nonempty S := hS_ne.to_subtype
  set d : ℕ → (Fin m → ℝ) := fun k ↦ (TopologicalSpace.denseSeq S k : Fin m → ℝ) with hd_def
  have hd_mem : ∀ k, d k ∈ S := fun k ↦ (TopologicalSpace.denseSeq S k).2
  have hd_dense : ∀ x ∈ S, x ∈ closure (Set.range d) := by
    intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ closure (Set.range (TopologicalSpace.denseSeq S)) :=
      TopologicalSpace.denseRange_denseSeq S _
    have h2 := image_closure_subset_closure_image (continuous_subtype_val)
      (Set.mem_image_of_mem _ h1)
    rw [← Set.range_comp] at h2
    exact h2
  -- value function `V ω := ⨆ k, g ω (d k)`, measurable
  set V : Ω → ℝ := fun ω ↦ ⨆ k, (F ω (d k) - ε * qReg (d k)) with hV_def
  have hV_meas : Measurable V :=
    Measurable.iSup fun k ↦ (hF_meas (d k)).sub measurable_const
  have hbdd : ∀ ω, BddAbove (Set.range fun k ↦ F ω (d k) - ε * qReg (d k)) := by
    intro ω
    refine ⟨F ω (bEps ω) - ε * qReg (bEps ω), ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hbEps_max ω (hd_mem k)
  have hV_le : ∀ ω, V ω ≤ F ω (bEps ω) - ε * qReg (bEps ω) := fun ω ↦
    ciSup_le fun k ↦ hbEps_max ω (hd_mem k)
  have hV_ge : ∀ ω, F ω (bEps ω) - ε * qReg (bEps ω) ≤ V ω := by
    intro ω
    obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp (hd_dense (bEps ω) (hbEps_mem ω))
    have hu_in_S : ∀ j, u j ∈ S := fun j ↦ by
      obtain ⟨k, hk⟩ := hu_mem j; rw [← hk]; exact hd_mem k
    have hcont : ContinuousWithinAt (fun b ↦ F ω b - ε * qReg b) S (bEps ω) :=
      (hg_cont ω) _ (hbEps_mem ω)
    have htend2 : Tendsto u atTop (𝓝[S] (bEps ω)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_lim
        (Filter.Eventually.of_forall hu_in_S)
    have htend : Tendsto (fun j ↦ F ω (u j) - ε * qReg (u j)) atTop
        (𝓝 (F ω (bEps ω) - ε * qReg (bEps ω))) := Filter.Tendsto.comp hcont htend2
    refine le_of_tendsto htend (Filter.Eventually.of_forall fun j ↦ ?_)
    obtain ⟨k, hk⟩ := hu_mem j
    rw [← hk]
    exact le_ciSup (hbdd ω) k
  have hV_eq : ∀ ω, V ω = F ω (bEps ω) - ε * qReg (bEps ω) := fun ω ↦
    le_antisymm (hV_le ω) (hV_ge ω)
  -- near-maximizer selection sequence, measurable
  have hnear : ∀ (n : ℕ) ω, ∃ k, V ω - 1 / (n + 1) < F ω (d k) - ε * qReg (d k) := by
    intro n ω
    apply exists_lt_of_lt_ciSup
    exact sub_lt_self (V ω) (one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n))
  set cSeq : ℕ → Ω → (Fin m → ℝ) := fun n ω ↦ d (Nat.find (hnear n ω)) with hcSeq_def
  have hcSeq_meas : ∀ n, Measurable (cSeq n) := by
    intro n
    exact Measurable.find (fun _ ↦ measurable_const) (fun k ↦
      measurableSet_lt (hV_meas.sub measurable_const) ((hF_meas (d k)).sub measurable_const))
      (hnear n)
  have hcSeq_mem : ∀ n ω, cSeq n ω ∈ S := fun n ω ↦ hd_mem _
  have hcSeq_lb : ∀ n ω, V ω - 1 / (n + 1) < F ω (cSeq n ω) - ε * qReg (cSeq n ω) := fun n ω ↦
    Nat.find_spec (hnear n ω)
  -- convergence of the near-maximizers to the unique maximizer
  have hconv : ∀ ω, Tendsto (fun n ↦ cSeq n ω) atTop (𝓝 (bEps ω)) := by
    intro ω
    -- the objective values along the selection tend to the maximum value `V ω`
    have hlow : Tendsto (fun n : ℕ ↦ V ω - 1 / ((n : ℝ) + 1)) atTop (𝓝 (V ω)) := by
      simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hsq : Tendsto (fun n ↦ F ω (cSeq n ω) - ε * qReg (cSeq n ω)) atTop (𝓝 (V ω)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
        (fun n ↦ (hcSeq_lb n ω).le)
        (fun n ↦ (hbEps_max ω (hcSeq_mem n ω)).trans (hV_eq ω).ge)
    apply hS_compact.tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall fun n ↦ hcSeq_mem n ω)
    intro y hy_mem hy_cluster
    obtain ⟨ψ, hψ_lim, hψ_top⟩ := hy_cluster.exists_seq_tendsto
    have hy_cont : ContinuousWithinAt (fun b ↦ F ω b - ε * qReg b) S y := (hg_cont ω) _ hy_mem
    have hψ_in : Tendsto (fun j ↦ cSeq (ψ j) ω) atTop (𝓝[S] y) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hψ_lim
        (Filter.Eventually.of_forall fun j ↦ hcSeq_mem _ ω)
    have hgy : Tendsto (fun j ↦ F ω (cSeq (ψ j) ω) - ε * qReg (cSeq (ψ j) ω)) atTop
        (𝓝 (F ω y - ε * qReg y)) := Filter.Tendsto.comp hy_cont hψ_in
    have hgy_eq : F ω y - ε * qReg y = V ω := tendsto_nhds_unique hgy (hsq.comp hψ_top)
    have hfby : F ω (bEps ω) - ε * qReg (bEps ω) = F ω y - ε * qReg y :=
      (hV_eq ω).symm.trans hgy_eq.symm
    have hy_max : IsMaxOn (fun b ↦ F ω b - ε * qReg b) S y := fun z hz ↦
      (hbEps_max ω hz).trans (le_of_eq hfby)
    exact (hg_sconc ω).eq_of_isMaxOn hy_max (hbEps_max ω) hy_mem (hbEps_mem ω)
  refine ⟨bEps, ?_, hbEps_mem, hbEps_max⟩
  exact measurable_of_tendsto_metrizable hcSeq_meas (tendsto_pi_nhds.mpr hconv)

/-- Measurable selection of an argmax of a concave Carathéodory function over the standard simplex.
For `F` measurable in `ω` (for each fixed portfolio `b`), continuous and concave in `b` on the
simplex, there is a measurable `bstar : Ω → (Fin m → ℝ)` picking, for each `ω`, a point of the
simplex that maximizes `F ω` over the simplex.

The domain-nonemptiness hypothesis `[Nonempty (Fin m)]` (i.e. `m ≥ 1`) is a regularity
precondition: for `m = 0` the simplex is empty and no selection into it exists.

@audit:ok -/
theorem exists_measurable_argmax_on_stdSimplex [Nonempty (Fin m)]
    (F : Ω → (Fin m → ℝ) → ℝ)
    (hF_meas : ∀ b : Fin m → ℝ, Measurable (fun ω ↦ F ω b))
    (hF_cont : ∀ ω, ContinuousOn (F ω) (stdSimplex ℝ (Fin m)))
    (hF_conc : ∀ ω, ConcaveOn ℝ (stdSimplex ℝ (Fin m)) (F ω)) :
    ∃ bstar : Ω → (Fin m → ℝ), Measurable bstar ∧
      (∀ ω, bstar ω ∈ stdSimplex ℝ (Fin m)) ∧
      (∀ ω, IsMaxOn (F ω) (stdSimplex ℝ (Fin m)) (bstar ω)) := by
  classical
  set S := stdSimplex ℝ (Fin m) with hS
  have hS_compact : IsCompact S := isCompact_stdSimplex ℝ (Fin m)
  have hS_ne : S.Nonempty := ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary (Fin m))⟩
  have hS_closed : IsClosed S := hS_compact.isClosed
  have hqReg_nonneg : ∀ b : Fin m → ℝ, 0 ≤ qReg b := fun b ↦
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  -- the argmax set `A ω` of `F ω`: convex, compact, nonempty
  have hFmax : ∀ ω, ∃ z ∈ S, IsMaxOn (F ω) S z := fun ω ↦
    hS_compact.exists_isMaxOn hS_ne (hF_cont ω)
  set xstar : Ω → (Fin m → ℝ) := fun ω ↦ (hFmax ω).choose with hxstar_def
  have hxstar_mem : ∀ ω, xstar ω ∈ S := fun ω ↦ (hFmax ω).choose_spec.1
  have hxstar_max : ∀ ω, IsMaxOn (F ω) S (xstar ω) := fun ω ↦ (hFmax ω).choose_spec.2
  set A : Ω → Set (Fin m → ℝ) := fun ω ↦ {x ∈ S | F ω (xstar ω) ≤ F ω x} with hA_def
  have hA_sub_S : ∀ ω, A ω ⊆ S := fun ω x hx ↦ hx.1
  have hA_ne : ∀ ω, (A ω).Nonempty := fun ω ↦ ⟨xstar ω, hxstar_mem ω, le_refl _⟩
  have hA_closed : ∀ ω, IsClosed (A ω) := fun ω ↦ by
    have h := (hF_cont ω).preimage_isClosed_of_isClosed hS_closed
      (isClosed_Ici (a := F ω (xstar ω)))
    convert h using 1
    ext x
    simp only [hA_def, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
  have hA_compact : ∀ ω, IsCompact (A ω) := fun ω ↦
    hS_compact.of_isClosed_subset (hA_closed ω) (hA_sub_S ω)
  have hA_max : ∀ ω x, x ∈ A ω → IsMaxOn (F ω) S x := fun ω x hx z hz ↦
    (hxstar_max ω hz).trans hx.2
  have hA_convex : ∀ ω, Convex ℝ (A ω) := fun ω ↦ (hF_conc ω).convex_ge (F ω (xstar ω))
  -- `bstar ω`: the unique `qReg`-minimizer over `A ω` (projection of the origin onto the argmax)
  have hbstar_ex : ∀ ω, ∃ z ∈ A ω, IsMinOn qReg (A ω) z := fun ω ↦
    (hA_compact ω).exists_isMinOn (hA_ne ω) qReg_continuous.continuousOn
  set bstar : Ω → (Fin m → ℝ) := fun ω ↦ (hbstar_ex ω).choose with hbstar_def
  have hbstar_A : ∀ ω, bstar ω ∈ A ω := fun ω ↦ (hbstar_ex ω).choose_spec.1
  have hbstar_min : ∀ ω, IsMinOn qReg (A ω) (bstar ω) := fun ω ↦ (hbstar_ex ω).choose_spec.2
  -- the regularized measurable maximizers `B n` (from the previous lemma, `ε = 1/(n+1)`)
  have hεpos : ∀ n : ℕ, (0:ℝ) < 1 / (n + 1) := fun n ↦
    one_div_pos.mpr (by exact_mod_cast Nat.succ_pos n)
  have hB : ∀ n : ℕ, ∃ b : Ω → (Fin m → ℝ), Measurable b ∧ (∀ ω, b ω ∈ S) ∧
      ∀ ω, IsMaxOn (fun x ↦ F ω x - (1 / (n + 1)) * qReg x) S (b ω) := fun n ↦
    exists_measurable_argmax_gEps F hF_meas hF_cont hF_conc (hεpos n)
  set B : ℕ → Ω → (Fin m → ℝ) := fun n ↦ (hB n).choose with hB_def
  have hB_meas : ∀ n, Measurable (B n) := fun n ↦ (hB n).choose_spec.1
  have hB_mem : ∀ n ω, B n ω ∈ S := fun n ω ↦ (hB n).choose_spec.2.1 ω
  have hB_max : ∀ (n : ℕ) ω, IsMaxOn (fun x ↦ F ω x - (1 / (n + 1)) * qReg x) S (B n ω) :=
    fun n ω ↦ (hB n).choose_spec.2.2 ω
  -- `B n ω → bstar ω`: the Tikhonov maximizers converge to the projection
  have hconv : ∀ ω, Tendsto (fun n ↦ B n ω) atTop (𝓝 (bstar ω)) := by
    intro ω
    apply hS_compact.tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall fun n ↦ hB_mem n ω)
    intro z hz_mem hz_cluster
    obtain ⟨ψ, hψ_lim, hψ_top⟩ := hz_cluster.exists_seq_tendsto
    have hε_lim : Tendsto (fun n : ℕ ↦ (1:ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hFcont_z : ContinuousWithinAt (F ω) S z := (hF_cont ω) _ hz_mem
    have hBψ_in : Tendsto (fun j ↦ B (ψ j) ω) atTop (𝓝[S] z) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hψ_lim
        (Filter.Eventually.of_forall fun j ↦ hB_mem _ ω)
    have hFz : Tendsto (fun j ↦ F ω (B (ψ j) ω)) atTop (𝓝 (F ω z)) :=
      Filter.Tendsto.comp hFcont_z hBψ_in
    -- (a) the cluster point `z` is an `F`-maximizer (it lies in `A ω`)
    have hz_in_A : z ∈ A ω := by
      refine ⟨hz_mem, ?_⟩
      have hLB : ∀ n : ℕ, F ω (xstar ω) - (1 / (n + 1)) * qReg (xstar ω) ≤ F ω (B n ω) := by
        intro n
        have h1 : F ω (xstar ω) - (1 / (n + 1)) * qReg (xstar ω)
            ≤ F ω (B n ω) - (1 / (n + 1)) * qReg (B n ω) := hB_max n ω (hxstar_mem ω)
        have h2 : (0:ℝ) ≤ (1 / (n + 1)) * qReg (B n ω) := mul_nonneg (hεpos n).le (hqReg_nonneg _)
        linarith
      have hRHS : Tendsto (fun j ↦ F ω (xstar ω) - (1 / ((ψ j : ℝ) + 1)) * qReg (xstar ω)) atTop
          (𝓝 (F ω (xstar ω))) := by
        have h0 : Tendsto (fun j ↦ (1 / ((ψ j : ℝ) + 1)) * qReg (xstar ω)) atTop
            (𝓝 (0 * qReg (xstar ω))) := (hε_lim.comp hψ_top).mul tendsto_const_nhds
        simpa using tendsto_const_nhds.sub h0
      exact le_of_tendsto_of_tendsto' hRHS hFz fun j ↦ hLB (ψ j)
    -- (b) the cluster point `z` minimizes `qReg` over `A ω`
    have hz_min : IsMinOn qReg (A ω) z := by
      intro w hw
      have hqle : ∀ n, qReg (B n ω) ≤ qReg w := by
        intro n
        have h1 : F ω w - (1 / (n + 1)) * qReg w
            ≤ F ω (B n ω) - (1 / (n + 1)) * qReg (B n ω) := hB_max n ω (hA_sub_S ω hw)
        have h2 : F ω (B n ω) ≤ F ω w := hA_max ω w hw (hB_mem n ω)
        have h3 : (1 / (n + 1)) * qReg (B n ω) ≤ (1 / (n + 1)) * qReg w := by linarith
        exact le_of_mul_le_mul_left h3 (hεpos n)
      have hqz : Tendsto (fun j ↦ qReg (B (ψ j) ω)) atTop (𝓝 (qReg z)) := by
        have h := (qReg_continuous.tendsto z).comp hψ_lim
        exact h
      exact le_of_tendsto hqz (Filter.Eventually.of_forall fun j ↦ hqle (ψ j))
    -- uniqueness of the projection
    exact (qReg_strictConvexOn.subset (hA_sub_S ω) (hA_convex ω)).eq_of_isMinOn
      hz_min (hbstar_min ω) hz_in_A (hbstar_A ω)
  refine ⟨bstar, measurable_of_tendsto_metrizable hB_meas (tendsto_pi_nhds.mpr hconv),
    fun ω ↦ hA_sub_S ω (hbstar_A ω), fun ω ↦ hA_max ω (bstar ω) (hbstar_A ω)⟩

end MeasurableArgmax

/-!
## Monotone convergence of the conditional-optimal growth rate (Cover–Thomas §16.5)

For an increasing filtration `ℱ` of the market's past, the conditional log-optimal portfolio at
stage `k` (past-`ℱ k`-measurable) has an expected growth `condOptGrowth k`. Conditioning on more
past information increases the optimal growth, so `condOptGrowth` is monotone; bounded above by a
market-regularity envelope, it converges to its supremum `condOptGrowthInfty = W_∞`. This sets up
the definitions the Algoet–Cover sandwich consumes: `W_∞` is an increasing limit of
integrals `∫ log(bstar k · X) ∂μ`, each of which is a Birkhoff spatial mean.
-/

section CondOptimalGrowth

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {m : ℕ}

/-- Per-epoch log return of a causal portfolio `bstar` (past-measurable, hence `ω`-dependent)
under price relatives `X`: `log (∑ j, bstar ω j · X ω j)`. For a constant portfolio this
specializes to `stationaryLogReturn X b`. -/
noncomputable def causalLogReturn (X : Ω → Fin m → ℝ) (bstar : Ω → Fin m → ℝ) : Ω → ℝ :=
  fun ω ↦ Real.log (∑ j, bstar ω j * X ω j)

/-- Expected growth of the stagewise conditional log-optimal portfolio: at stage `k`, the expected
log return `∫ log (bstar k · X) ∂μ` of the past-measurable portfolio `bstar k`. By
`integral_condExp` this equals `∫ μ[log (bstar k · X) | ℱ k] ∂μ`, the mean conditional-optimal
growth rate. -/
noncomputable def condOptGrowth (μ : Measure Ω) (X : Ω → Fin m → ℝ)
    (bstar : ℕ → Ω → Fin m → ℝ) : ℕ → ℝ :=
  fun k ↦ ∫ ω, causalLogReturn X (bstar k) ω ∂μ

/-- Infinite-past optimal growth `W_∞ := ⨆ k, condOptGrowth k`: the supremum of the increasing
sequence of conditional-optimal expected growths. -/
noncomputable def condOptGrowthInfty (μ : Measure Ω) (X : Ω → Fin m → ℝ)
    (bstar : ℕ → Ω → Fin m → ℝ) : ℝ :=
  ⨆ k, condOptGrowth μ X bstar k

/-- Integrable envelope for the simplex log returns: `∑ j |log (X ω j)|` dominates
`|log (∑ j, b j · X ω j)|` uniformly over portfolios `b` in the simplex. -/
private noncomputable def logEnvelope (X : Ω → Fin m → ℝ) (ω : Ω) : ℝ :=
  ∑ j, |Real.log (X ω j)|

/-- Conditional growth objective at stage `k`: the expected log return of a fixed portfolio `b`
against the regular conditional law `condExpKernel μ (ℱ k) ω`. Applying the measurable-argmax
gateway to `b ↦ condGrowthObjective μ ℱ X k ω b` selects the conditional log-optimal portfolio. -/
private noncomputable def condGrowthObjective [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) (X : Ω → Fin m → ℝ) (k : ℕ) (ω : Ω)
    (b : Fin m → ℝ) : ℝ :=
  ∫ y, Real.log (∑ j, b j * X y j) ∂(condExpKernel μ (ℱ k) ω)

-- Each price relative is positive: from `hpos` at the vertex portfolios `Pi.single j 1`.
private theorem market_pos {X : Ω → Fin m → ℝ}
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j) (ω : Ω) (j : Fin m) :
    0 < X ω j := by
  have h := hpos ω (Pi.single j 1) (single_mem_stdSimplex ℝ j)
  rwa [Finset.sum_eq_single j (fun i _ hij ↦ by rw [Pi.single_eq_of_ne hij, zero_mul])
    (fun hj ↦ absurd (Finset.mem_univ j) hj), Pi.single_eq_same, one_mul] at h

-- The envelope dominates the simplex log returns pointwise.
private theorem logReturn_abs_le_envelope {X : Ω → Fin m → ℝ} [Nonempty (Fin m)]
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j) (ω : Ω)
    {b : Fin m → ℝ} (hb : b ∈ stdSimplex ℝ (Fin m)) :
    |Real.log (∑ j, b j * X ω j)| ≤ logEnvelope X ω := by
  have hXpos : ∀ j, 0 < X ω j := fun j ↦ market_pos hpos ω j
  have hb0 : ∀ j, 0 ≤ b j := hb.1
  have hbsum : ∑ j, b j = 1 := hb.2
  have hS : (0:ℝ) < ∑ j, b j * X ω j := hpos ω b hb
  set mx := Finset.univ.sup' Finset.univ_nonempty (X ω) with hmx_def
  set mn := Finset.univ.inf' Finset.univ_nonempty (X ω) with hmn_def
  -- convex-combination bounds
  have hSmx : (∑ j, b j * X ω j) ≤ mx := by
    calc (∑ j, b j * X ω j) ≤ ∑ j, b j * mx :=
          Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left
            (Finset.le_sup' (X ω) (Finset.mem_univ j)) (hb0 j)
      _ = (∑ j, b j) * mx := by rw [Finset.sum_mul]
      _ = mx := by rw [hbsum, one_mul]
  have hSmn : mn ≤ (∑ j, b j * X ω j) := by
    calc mn = (∑ j, b j) * mn := by rw [hbsum, one_mul]
      _ = ∑ j, b j * mn := by rw [Finset.sum_mul]
      _ ≤ ∑ j, b j * X ω j :=
          Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left
            (Finset.inf'_le (X ω) (Finset.mem_univ j)) (hb0 j)
  have hmn_pos : (0:ℝ) < mn := by
    rw [hmn_def, Finset.lt_inf'_iff]
    exact fun j _ ↦ hXpos j
  -- log monotonicity gives the two-sided bound
  have hlogSmn : Real.log mn ≤ Real.log (∑ j, b j * X ω j) := Real.log_le_log hmn_pos hSmn
  have hlogSmx : Real.log (∑ j, b j * X ω j) ≤ Real.log mx := Real.log_le_log hS hSmx
  -- both endpoints are dominated by the envelope
  have hmn_le : |Real.log mn| ≤ logEnvelope X ω := by
    obtain ⟨j0, _, hj0⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin m)) (X ω)
    rw [hmn_def, hj0]
    exact Finset.single_le_sum (f := fun j ↦ |Real.log (X ω j)|)
      (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j0)
  have hmx_le : |Real.log mx| ≤ logEnvelope X ω := by
    obtain ⟨j1, _, hj1⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin m)) (X ω)
    rw [hmx_def, hj1]
    exact Finset.single_le_sum (f := fun j ↦ |Real.log (X ω j)|)
      (fun j _ ↦ abs_nonneg _) (Finset.mem_univ j1)
  -- assemble `|log S| ≤ max (|log mn|) (|log mx|) ≤ envelope`
  refine le_trans (abs_le.mpr ⟨?_, ?_⟩) (max_le hmn_le hmx_le)
  · refine le_trans ?_ hlogSmn
    rw [neg_le]
    exact le_trans (neg_le_abs _) (le_max_left _ _)
  · exact le_trans hlogSmx (le_trans (le_abs_self _) (le_max_right _ _))

-- The envelope is `μ`-integrable, obtained from `hint` at the vertex portfolios.
private theorem logEnvelope_integrable (μ : Measure Ω) {X : Ω → Fin m → ℝ}
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ) :
    Integrable (logEnvelope X) μ := by
  unfold logEnvelope
  refine integrable_finsetSum _ fun j _ ↦ ?_
  have hc : Integrable (causalLogReturn X (fun _ ↦ Pi.single j 1)) μ :=
    hint _ measurable_const fun _ ↦ single_mem_stdSimplex ℝ j
  have heq : causalLogReturn X (fun _ ↦ Pi.single j (1 : ℝ)) = fun ω ↦ Real.log (X ω j) := by
    funext ω
    simp only [causalLogReturn]
    congr 1
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [Pi.single_eq_of_ne hij, zero_mul])
      (fun hj ↦ absurd (Finset.mem_univ j) hj), Pi.single_eq_same, one_mul]
  rw [heq] at hc
  exact hc.abs

-- Pointwise concavity of the log return in the portfolio, on the simplex.
private theorem logReturn_concaveOn {X : Ω → Fin m → ℝ}
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j) (ω : Ω) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin m)) (fun b ↦ Real.log (∑ j, b j * X ω j)) := by
  refine ⟨convex_stdSimplex ℝ (Fin m), ?_⟩
  intro x hx y hy a b ha hb hab
  have hLx : (0:ℝ) < ∑ j, x j * X ω j := hpos ω x hx
  have hLy : (0:ℝ) < ∑ j, y j * X ω j := hpos ω y hy
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr hLx)
    (Set.mem_Ioi.mpr hLy) ha hb hab
  have hlin : ∑ j, (a • x + b • y) j * X ω j
      = a • (∑ j, x j * X ω j) + b • (∑ j, y j * X ω j) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp only [smul_eq_mul] at hconc ⊢
  rw [hlin]
  exact hconc

-- Pointwise continuity of the log return in the portfolio, on the simplex.
private theorem logReturn_continuousOn {X : Ω → Fin m → ℝ}
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j) (ω : Ω) :
    ContinuousOn (fun b ↦ Real.log (∑ j, b j * X ω j)) (stdSimplex ℝ (Fin m)) := by
  apply ContinuousOn.log
  · exact (continuous_finsetSum _ fun j _ ↦
      (continuous_apply j).mul continuous_const).continuousOn
  · exact fun b hb ↦ (hpos ω b hb).ne'

-- Measurability of the conditional growth objective in `ω`, with respect to `ℱ k`.
private theorem condGrowthObjective_measurable [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {X : Ω → Fin m → ℝ} (hX : Measurable X) (k : ℕ)
    (b : Fin m → ℝ) : Measurable[ℱ k] (fun ω ↦ condGrowthObjective μ ℱ X k ω b) := by
  unfold condGrowthObjective
  have hf : StronglyMeasurable (fun y ↦ Real.log (∑ j, b j * X y j)) :=
    (Real.measurable_log.comp (Finset.measurable_sum _ fun j _ ↦
      measurable_const.mul ((measurable_pi_apply j).comp hX))).stronglyMeasurable
  exact hf.integral_condExpKernel.measurable

-- On the good set (envelope integrable against the conditional law) each simplex log return is
-- integrable against the conditional law.
private theorem logReturn_integrable_kernel [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {X : Ω → Fin m → ℝ} [Nonempty (Fin m)]
    (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j) (k : ℕ) {ω : Ω}
    (hω : Integrable (logEnvelope X) (condExpKernel μ (ℱ k) ω))
    {b : Fin m → ℝ} (hb : b ∈ stdSimplex ℝ (Fin m)) :
    Integrable (fun y ↦ Real.log (∑ j, b j * X y j)) (condExpKernel μ (ℱ k) ω) := by
  refine Integrable.mono' hω
    ((Real.measurable_log.comp (Finset.measurable_sum _ fun j _ ↦
      measurable_const.mul ((measurable_pi_apply j).comp hX))).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun y ↦ by
    rw [Real.norm_eq_abs]; exact logReturn_abs_le_envelope hpos y hb

-- On the good set the objective is continuous in `b` on the simplex (dominated convergence).
private theorem condGrowthObjective_continuousOn [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {X : Ω → Fin m → ℝ} [Nonempty (Fin m)]
    (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j) (k : ℕ) {ω : Ω}
    (hω : Integrable (logEnvelope X) (condExpKernel μ (ℱ k) ω)) :
    ContinuousOn (condGrowthObjective μ ℱ X k ω) (stdSimplex ℝ (Fin m)) := by
  unfold condGrowthObjective
  refine continuousOn_of_dominated
    (F := fun (b : Fin m → ℝ) y ↦ Real.log (∑ j, b j * X y j)) (bound := logEnvelope X)
    (fun b _ ↦ ?_) (fun b hb ↦ ?_) hω
    (Filter.Eventually.of_forall fun y ↦ logReturn_continuousOn hpos y)
  · exact (Real.measurable_log.comp (Finset.measurable_sum _ fun j _ ↦
      measurable_const.mul ((measurable_pi_apply j).comp hX))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs]; exact logReturn_abs_le_envelope hpos y hb

-- On the good set the objective is concave in `b` on the simplex.
private theorem condGrowthObjective_concaveOn [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {X : Ω → Fin m → ℝ} [Nonempty (Fin m)]
    (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j) (k : ℕ) {ω : Ω}
    (hω : Integrable (logEnvelope X) (condExpKernel μ (ℱ k) ω)) :
    ConcaveOn ℝ (stdSimplex ℝ (Fin m)) (condGrowthObjective μ ℱ X k ω) := by
  unfold condGrowthObjective
  refine integral_concaveOn_of_integrand_ae
    (f := fun y (b : Fin m → ℝ) ↦ Real.log (∑ j, b j * X y j)) (convex_stdSimplex ℝ (Fin m))
    (Filter.Eventually.of_forall fun y ↦ logReturn_concaveOn hpos y)
    (fun b hb ↦ logReturn_integrable_kernel μ ℱ hX hpos k hω hb)

-- Crux (kernel properness): an `ℱ k`-measurable function is `condExpKernel`-a.e. equal to
-- its value at `ω`, for `μ`-a.e. `ω`.
private theorem condExpKernel_ae_const [StandardBorelSpace Ω] [Nonempty Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) (k : ℕ) {c : Ω → Fin m → ℝ}
    (hc : StronglyMeasurable[ℱ k] c) :
    ∀ᵐ ω ∂μ, c =ᵐ[condExpKernel μ (ℱ k) ω] (fun _ ↦ c ω) := by
  classical
  have hm : (ℱ k) ≤ m0 := ℱ.le k
  have hcm : Measurable[ℱ k] c := hc.measurable
  have hcm0 : Measurable c := (hc.mono hm).measurable
  -- a countable topological basis of the value space `Fin m → ℝ`
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis (Fin m → ℝ)
  -- for each basis element `U`, `c ω ∉ U` forces `κ_ω (c⁻¹ U) = 0`, for `μ`-a.e. `ω`
  have hkey : ∀ U ∈ B, ∀ᵐ ω ∂μ,
      c ω ∉ U → condExpKernel μ (ℱ k) ω (c ⁻¹' U) = 0 := by
    intro U hU
    have hUopen : IsOpen U := hB.isOpen hU
    have hs_m : MeasurableSet[ℱ k] (c ⁻¹' U) := hcm hUopen.measurableSet
    have hs0 : MeasurableSet (c ⁻¹' U) := hcm0 hUopen.measurableSet
    have hcond : μ⟦c ⁻¹' U | ℱ k⟧ = (c ⁻¹' U).indicator (fun _ ↦ (1:ℝ)) :=
      condExp_of_stronglyMeasurable hm (stronglyMeasurable_const.indicator hs_m)
        ((integrable_const (1:ℝ)).indicator hs0)
    have heq : (fun ω ↦ (condExpKernel μ (ℱ k) ω).real (c ⁻¹' U)) =ᵐ[μ]
        (c ⁻¹' U).indicator (fun _ ↦ (1:ℝ)) := by
      rw [← hcond]; exact condExpKernel_ae_eq_condExp hm hs0
    filter_upwards [heq] with ω hω hcω
    have hnotmem : ω ∉ c ⁻¹' U := fun h ↦ hcω h
    have hind0 : (c ⁻¹' U).indicator (fun _ ↦ (1:ℝ)) ω = 0 :=
      Set.indicator_of_notMem hnotmem _
    rw [hind0] at hω
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hω
  -- intersect the countable family into a single co-null set
  have hkeyall : ∀ᵐ ω ∂μ,
      ∀ U ∈ B, c ω ∉ U → condExpKernel μ (ℱ k) ω (c ⁻¹' U) = 0 :=
    (ae_ball_iff hBc).mpr hkey
  filter_upwards [hkeyall] with ω hω
  -- the complement of `{c ω}` is a countable union of basis sets missing `c ω`
  have hOopen : IsOpen ({c ω}ᶜ : Set (Fin m → ℝ)) := isOpen_compl_singleton
  have hnull : condExpKernel μ (ℱ k) ω (c ⁻¹' ({c ω}ᶜ)) = 0 := by
    rw [hB.open_eq_sUnion' hOopen, Set.preimage_sUnion]
    refine (measure_biUnion_null_iff (Set.Countable.mono (Set.sep_subset _ _) hBc)).mpr ?_
    intro U hU
    exact hω U hU.1 (fun hcU ↦ (hU.2 hcU) rfl)
  have hset : {y | ¬ (c y = c ω)} = c ⁻¹' ({c ω}ᶜ) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  change ∀ᵐ y ∂(condExpKernel μ (ℱ k) ω), c y = c ω
  rw [ae_iff, hset]
  exact hnull

-- Pull-out identity: the conditional expectation of the log return of an `ℱ k`-measurable
-- portfolio `c` is the objective evaluated at `c ω`.
private theorem condExp_causalLogReturn_eq [StandardBorelSpace Ω] [Nonempty Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {X : Ω → Fin m → ℝ}
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ) (k : ℕ) {c : Ω → Fin m → ℝ}
    (hc : StronglyMeasurable[ℱ k] c) (hcs : ∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) :
    μ[causalLogReturn X c | ℱ k] =ᵐ[μ] fun ω ↦ condGrowthObjective μ ℱ X k ω (c ω) := by
  have hc_int : Integrable (causalLogReturn X c) μ := hint c (hc.mono (ℱ.le k)).measurable hcs
  have h1 := condExp_ae_eq_integral_condExpKernel (ℱ.le k) hc_int
  have hconst := condExpKernel_ae_const μ ℱ k hc
  filter_upwards [h1, hconst] with ω hω1 hωc
  rw [hω1]
  unfold condGrowthObjective causalLogReturn
  refine integral_congr_ae ?_
  filter_upwards [hωc] with y hy
  rw [hy]

/-- Existence of a stagewise conditional log-optimal portfolio sequence: for each stage `k` there
is a past-`ℱ k`-measurable simplex portfolio `bstar k` whose conditional growth dominates, in
conditional expectation given `ℱ k`, that of every `ℱ k`-measurable simplex competitor `c`. This
is the conditional (past-measurable) form of the measurable-argmax gateway
`exists_measurable_argmax_on_stdSimplex`, applied to the conditional growth objective
`b ↦ ∫ y, log (b · X y) ∂(condExpKernel μ (ℱ k) ω)`, the expected log-return against the regular
conditional law given `ℱ k`. The `hpos`/`hint` hypotheses are market-regularity preconditions
(positivity for the `log` domain, integrability of simplex log-returns); `[StandardBorelSpace Ω]`
`[Nonempty Ω]` make the regular conditional distribution `condExpKernel` available. The gateway is
fed a good-set patch of the objective (the true objective where the envelope `∑ⱼ |log Xⱼ|` is
`condExpKernel`-integrable, `0` off that co-null set) so that continuity and concavity in `b` hold
for every `ω`; the conditional dominance then follows from the pull-out identity
`μ[log (c · X) | ℱ k] ω = ∫ y, log (c ω · X y) ∂(condExpKernel μ (ℱ k) ω)`, obtained because an
`ℱ k`-measurable `c` is `condExpKernel`-a.e. constant.

@audit:ok -/
theorem exists_condLogOptimalSeq [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X : Ω → Fin m → ℝ) [Nonempty (Fin m)]
    (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ) :
    ∃ bstar : ℕ → Ω → Fin m → ℝ,
      (∀ k, StronglyMeasurable[ℱ k] (bstar k)) ∧
      (∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m)) ∧
      (∀ (k : ℕ) (c : Ω → Fin m → ℝ), StronglyMeasurable[ℱ k] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ℱ k] ≤ᵐ[μ] μ[causalLogReturn X (bstar k) | ℱ k]) := by
  classical
  -- envelope measurability
  have hlogEnv_meas : Measurable (logEnvelope X) := by
    apply Finset.measurable_sum
    intro j _
    have hXj : Measurable (fun ω ↦ X ω j) := (measurable_pi_apply j).comp hX
    exact (Real.measurable_log.comp hXj).abs
  -- good set at stage `k`: the envelope is integrable against the conditional law `κ_ω`
  set g : ℕ → Ω → Prop :=
    fun k ω ↦ ∫⁻ y, ‖logEnvelope X y‖ₑ ∂(condExpKernel μ (ℱ k) ω) < ∞
  have hg_meas : ∀ k, MeasurableSet[ℱ k] {ω | g k ω} :=
    fun k ↦ (hlogEnv_meas.enorm.lintegral_kernel) measurableSet_Iio
  have hg_ae : ∀ k, ∀ᵐ ω ∂μ, g k ω := by
    intro k
    filter_upwards [(logEnvelope_integrable μ hint).condExpKernel_ae (m := ℱ k)] with ω hω
    exact hasFiniteIntegral_iff_enorm.mp hω.2
  have hgood_int : ∀ k ω, g k ω → Integrable (logEnvelope X) (condExpKernel μ (ℱ k) ω) :=
    fun k ω hg ↦ ⟨hlogEnv_meas.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr hg⟩
  -- the patched objective is everywhere measurable, continuous and concave
  have hFmeas : ∀ k (b : Fin m → ℝ),
      Measurable[ℱ k] (fun ω ↦ if g k ω then condGrowthObjective μ ℱ X k ω b else 0) :=
    fun k b ↦ Measurable.ite (hg_meas k) (condGrowthObjective_measurable μ ℱ hX k b)
      measurable_const
  have hFcont : ∀ k ω, ContinuousOn
      (fun z ↦ if g k ω then condGrowthObjective μ ℱ X k ω z else 0)
      (stdSimplex ℝ (Fin m)) := by
    intro k ω
    by_cases hg : g k ω
    · simp only [if_pos hg]
      exact condGrowthObjective_continuousOn μ ℱ hX hpos k (hgood_int k ω hg)
    · simp only [if_neg hg]
      exact continuousOn_const
  have hFconc : ∀ k ω, ConcaveOn ℝ (stdSimplex ℝ (Fin m))
      (fun z ↦ if g k ω then condGrowthObjective μ ℱ X k ω z else 0) := by
    intro k ω
    by_cases hg : g k ω
    · simp only [if_pos hg]
      exact condGrowthObjective_concaveOn μ ℱ hX hpos k (hgood_int k ω hg)
    · simp only [if_neg hg]
      exact concaveOn_const _ (convex_stdSimplex ℝ (Fin m))
  -- the measurable-argmax gateway, with ambient σ-algebra `ℱ k`
  have hsel : ∀ k, ∃ b : Ω → Fin m → ℝ, Measurable[ℱ k] b ∧
      (∀ ω, b ω ∈ stdSimplex ℝ (Fin m)) ∧
      ∀ ω, IsMaxOn (fun z ↦ if g k ω then condGrowthObjective μ ℱ X k ω z else 0)
        (stdSimplex ℝ (Fin m)) (b ω) := by
    intro k
    exact @exists_measurable_argmax_on_stdSimplex Ω (ℱ k) m _
      (fun ω z ↦ if g k ω then condGrowthObjective μ ℱ X k ω z else 0)
      (hFmeas k) (hFcont k) (hFconc k)
  choose bstar hbstar_meas hbstar_mem hbstar_max using hsel
  refine ⟨bstar, fun k ↦ (hbstar_meas k).stronglyMeasurable, hbstar_mem, ?_⟩
  intro k c hc hcs
  have hc_eq := condExp_causalLogReturn_eq μ ℱ hint k hc hcs
  have hbstar_eq := condExp_causalLogReturn_eq μ ℱ hint k
    (hbstar_meas k).stronglyMeasurable (hbstar_mem k)
  filter_upwards [hc_eq, hbstar_eq, hg_ae k] with ω h1 h2 hgood
  rw [h1, h2]
  have hmax := hbstar_max k ω (hcs ω)
  simp only [Set.mem_setOf_eq] at hmax
  rw [if_pos hgood, if_pos hgood] at hmax
  exact hmax

/-- Monotonicity of the conditional-optimal expected growth: conditioning on more past
information (larger `k`) can only increase the optimal expected growth. The `hdom` conditional
optimality is a property of the constructed selection `bstar` (supplied by
`exists_condLogOptimalSeq`), and monotonicity is derived from it via `integral_condExp` and
`integral_mono_ae` — not assumed.

@audit:ok -/
theorem condOptGrowth_monotone (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X : Ω → Fin m → ℝ) (bstar : ℕ → Ω → Fin m → ℝ)
    (hmeas : ∀ k, StronglyMeasurable[ℱ k] (bstar k))
    (hsimplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    (hdom : ∀ (k : ℕ) (c : Ω → Fin m → ℝ), StronglyMeasurable[ℱ k] c →
      (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      μ[causalLogReturn X c | ℱ k] ≤ᵐ[μ] μ[causalLogReturn X (bstar k) | ℱ k]) :
    Monotone (condOptGrowth μ X bstar) := by
  apply monotone_nat_of_le_succ
  intro k
  -- `bstar k` is `ℱ (k+1)`-measurable (`ℱ` increasing), so it is a legal competitor at stage `k+1`.
  have hmeas_k1 : StronglyMeasurable[ℱ (k + 1)] (bstar k) :=
    (hmeas k).mono (ℱ.mono (Nat.le_succ k))
  have hle : ℱ (k + 1) ≤ m0 := ℱ.le (k + 1)
  -- Conditional optimality of `bstar (k+1)` dominates the competitor `bstar k`.
  have hdom_k : μ[causalLogReturn X (bstar k) | ℱ (k + 1)]
      ≤ᵐ[μ] μ[causalLogReturn X (bstar (k + 1)) | ℱ (k + 1)] :=
    hdom (k + 1) (bstar k) hmeas_k1 (hsimplex k)
  -- Integrate the pointwise conditional dominance; `∫ μ[f | ℱ] = ∫ f` collapses both sides.
  calc condOptGrowth μ X bstar k
      = ∫ ω, (μ[causalLogReturn X (bstar k) | ℱ (k + 1)]) ω ∂μ := (integral_condExp hle).symm
    _ ≤ ∫ ω, (μ[causalLogReturn X (bstar (k + 1)) | ℱ (k + 1)]) ω ∂μ :=
        integral_mono_ae integrable_condExp integrable_condExp hdom_k
    _ = condOptGrowth μ X bstar (k + 1) := integral_condExp hle

/-- Boundedness above of the conditional-optimal expected growth, from a uniform expected-return
bound `hUB` (a market-regularity/integrability precondition: expected simplex log-returns are
bounded by a common constant).

@audit:ok -/
theorem condOptGrowth_bddAbove (μ : Measure Ω) (X : Ω → Fin m → ℝ)
    (bstar : ℕ → Ω → Fin m → ℝ)
    (hsimplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    (hintb : ∀ k, Integrable (causalLogReturn X (bstar k)) μ)
    (hUB : ∃ C : ℝ, ∀ c : Ω → Fin m → ℝ, (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ → ∫ ω, causalLogReturn X c ω ∂μ ≤ C) :
    BddAbove (Set.range (condOptGrowth μ X bstar)) := by
  obtain ⟨C, hC⟩ := hUB
  refine ⟨C, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact hC (bstar k) (hsimplex k) (hintb k)

/-- The conditional-optimal expected growth converges monotonically to the infinite-past optimal
growth `W_∞` (Cover–Thomas §16.5). There is a stagewise conditional log-optimal portfolio
sequence `bstar` (past-measurable, dominating all past-measurable competitors) whose expected
growth `condOptGrowth` is monotone, bounded above, and converges to its supremum
`condOptGrowthInfty = W_∞`. The monotone-convergence conclusion is proved, not assumed:
monotonicity from the conditional optimality of `bstar`, boundedness from the regularity envelope
`hUB`, convergence via `tendsto_atTop_ciSup`. The stagewise conditional log-optimal selection is
supplied by `exists_condLogOptimalSeq`. The Algoet–Cover sandwich consumes
`bstar`/`condOptGrowth`/`condOptGrowthInfty` for `(1/n) log S*_n → W_∞`.

@audit:ok -/
theorem exists_condOptGrowth_tendsto_condOptGrowthInfty [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X : Ω → Fin m → ℝ) [Nonempty (Fin m)]
    (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ)
    (hUB : ∃ C : ℝ, ∀ c : Ω → Fin m → ℝ, (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ → ∫ ω, causalLogReturn X c ω ∂μ ≤ C) :
    ∃ bstar : ℕ → Ω → Fin m → ℝ,
      (∀ k, StronglyMeasurable[ℱ k] (bstar k)) ∧
      (∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m)) ∧
      (∀ (k : ℕ) (c : Ω → Fin m → ℝ), StronglyMeasurable[ℱ k] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ℱ k] ≤ᵐ[μ] μ[causalLogReturn X (bstar k) | ℱ k]) ∧
      Tendsto (condOptGrowth μ X bstar) atTop (𝓝 (condOptGrowthInfty μ X bstar)) := by
  obtain ⟨bstar, hmeas, hsimplex, hdom⟩ := exists_condLogOptimalSeq μ ℱ X hX hpos hint
  have hintb : ∀ k, Integrable (causalLogReturn X (bstar k)) μ := fun k ↦
    hint (bstar k) ((hmeas k).mono (ℱ.le k)).measurable (hsimplex k)
  refine ⟨bstar, hmeas, hsimplex, hdom, ?_⟩
  have h_mono := condOptGrowth_monotone μ ℱ X bstar hmeas hsimplex hdom
  have h_bdd := condOptGrowth_bddAbove μ X bstar hsimplex hintb hUB
  exact tendsto_atTop_ciSup h_mono h_bdd

end CondOptimalGrowth

end InformationTheory.Shannon.Portfolio
