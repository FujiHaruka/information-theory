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
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
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

-- Each simplex coordinate is at most `1` (nonnegative and summing to `1`).
private theorem stdSimplex_component_le_one {x : Fin m → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin m)) (j : Fin m) : x j ≤ 1 :=
  hx.2 ▸ Finset.single_le_sum (fun i _ ↦ hx.1 i) (Finset.mem_univ j)

-- Stagewise conditional-expectation portfolio: the `ℱ k`-conditional expectation, taken
-- coordinatewise, of the infinite-past optimal portfolio `g`.
private noncomputable def condExpPortfolio (μ : Measure Ω) (ℱ : Filtration ℕ m0)
    (g : Ω → Fin m → ℝ) (k : ℕ) (ω : Ω) : Fin m → ℝ :=
  fun j ↦ (μ[fun ω' ↦ g ω' j | ℱ k]) ω

open Classical in
-- The stagewise conditional-expectation portfolio patched to be simplex-valued everywhere: it
-- equals `condExpPortfolio` on the (co-null) good set where the latter lands in the simplex, and a
-- fixed simplex vertex elsewhere. This makes it a legal `ℱ k`-measurable simplex competitor.
private noncomputable def condExpPortfolioPatched [Nonempty (Fin m)] (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) (g : Ω → Fin m → ℝ) (k : ℕ) (ω : Ω) : Fin m → ℝ :=
  if condExpPortfolio μ ℱ g k ω ∈ stdSimplex ℝ (Fin m) then condExpPortfolio μ ℱ g k ω
  else Pi.single (Classical.arbitrary (Fin m)) 1

/-- Gateway identity for the stationary-market `W_∞` AEP (Cover–Thomas §16.5): the growth-rate
integral of the infinite-past (`⨆ k, ℱ k`) conditional log-optimal portfolio `bstarInf` equals the
increasing limit `W_∞ = condOptGrowthInfty` of the stagewise conditional-optimal growths. This is
the identity that lets the Algoet–Cover sandwich for `(1/n) log S*_n → W_∞` reduce to a direct
Birkhoff application.

Two inclusions bracket the value. The upper inclusion `condOptGrowthInfty ≤ ∫ log (bstarInf · X)`
uses that each `bstar k` is `⨆ j, ℱ j`-measurable (the filtration is increasing) and hence a legal
competitor against `bstarInf` at the infinite-past level; integrating the conditional dominance
collapses both conditional expectations to their integrals. The lower inclusion
`∫ log (bstarInf · X) ≤ condOptGrowthInfty` approximates `bstarInf` by its stagewise conditional
expectations `c_k := μ[bstarInf | ℱ k]` (coordinatewise), which are `ℱ k`-measurable and a.e.
simplex-valued (conditional expectation preserves nonnegativity and the unit coordinate sum);
patched to be everywhere simplex-valued they are legal stage-`k` competitors, so
`∫ log (c_k · X) ≤ condOptGrowth k ≤ condOptGrowthInfty`. Lévy's upward theorem
(`Integrable.tendsto_ae_condExp`) gives `c_k → bstarInf` a.e., and dominated convergence (envelope
`∑ⱼ |log Xⱼ|`) passes the bound to the limit.

`bstarInf` and its `⨆ j, ℱ j`-conditional dominance are received as hypotheses (constructed
separately, e.g. by instantiating `exists_condLogOptimalSeq` at the constant filtration
`fun _ ↦ ⨆ j, ℱ j`); this proves only the identity, not the existence. The `hpos`/`hint`
hypotheses are market-regularity preconditions.

@audit:ok -/
theorem condOptGrowthInfty_eq_integral_infPast [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X : Ω → Fin m → ℝ) [Nonempty (Fin m)]
    (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ)
    (bstar : ℕ → Ω → Fin m → ℝ)
    (hbstar_meas : ∀ k, StronglyMeasurable[ℱ k] (bstar k))
    (hbstar_simplex : ∀ k ω, bstar k ω ∈ stdSimplex ℝ (Fin m))
    (hbstar_dom : ∀ (k : ℕ) (c : Ω → Fin m → ℝ), StronglyMeasurable[ℱ k] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ℱ k] ≤ᵐ[μ] μ[causalLogReturn X (bstar k) | ℱ k])
    (bstarInf : Ω → Fin m → ℝ)
    (hInf_meas : StronglyMeasurable[⨆ j, ℱ j] bstarInf)
    (hInf_simplex : ∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m))
    (hInf_dom : ∀ (c : Ω → Fin m → ℝ), StronglyMeasurable[⨆ j, ℱ j] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ⨆ j, ℱ j] ≤ᵐ[μ] μ[causalLogReturn X bstarInf | ⨆ j, ℱ j]) :
    ∫ ω, causalLogReturn X bstarInf ω ∂μ = condOptGrowthInfty μ X bstar := by
  classical
  have hsup_le : (⨆ j, ℱ j) ≤ m0 := iSup_le ℱ.le
  -- Direction 1 (upper): `condOptGrowth k ≤ ∫ log (bstarInf · X)` for every `k`.
  have hUpper : ∀ k, condOptGrowth μ X bstar k ≤ ∫ ω, causalLogReturn X bstarInf ω ∂μ := by
    intro k
    have hmeas_inf : StronglyMeasurable[⨆ j, ℱ j] (bstar k) :=
      (hbstar_meas k).mono (le_iSup (fun j ↦ ℱ j) k)
    calc condOptGrowth μ X bstar k
        = ∫ ω, causalLogReturn X (bstar k) ω ∂μ := rfl
      _ = ∫ ω, (μ[causalLogReturn X (bstar k) | ⨆ j, ℱ j]) ω ∂μ := (integral_condExp hsup_le).symm
      _ ≤ ∫ ω, (μ[causalLogReturn X bstarInf | ⨆ j, ℱ j]) ω ∂μ :=
          integral_mono_ae integrable_condExp integrable_condExp
            (hInf_dom (bstar k) hmeas_inf (hbstar_simplex k))
      _ = ∫ ω, causalLogReturn X bstarInf ω ∂μ := integral_condExp hsup_le
  have hbdd : BddAbove (Set.range (condOptGrowth μ X bstar)) :=
    ⟨∫ ω, causalLogReturn X bstarInf ω ∂μ, by rintro _ ⟨k, rfl⟩; exact hUpper k⟩
  have h1 : condOptGrowthInfty μ X bstar ≤ ∫ ω, causalLogReturn X bstarInf ω ∂μ :=
    ciSup_le hUpper
  -- Direction 2 (lower): `∫ log (bstarInf · X) ≤ condOptGrowthInfty`.
  have hLower : ∫ ω, causalLogReturn X bstarInf ω ∂μ ≤ condOptGrowthInfty μ X bstar := by
    -- `bstarInf` regularity: measurable, integrable and `⨆ ℱ`-measurable coordinates.
    have hInf_sm : StronglyMeasurable bstarInf := hInf_meas.mono hsup_le
    have hInf_int : ∀ j, Integrable (fun ω ↦ bstarInf ω j) μ := by
      intro j
      refine Integrable.mono' (integrable_const (1:ℝ))
        ((measurable_pi_apply j).comp hInf_sm.measurable).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg ((hInf_simplex ω).1 j)]
      exact stdSimplex_component_le_one (hInf_simplex ω) j
    have hInf_sm_sup : ∀ j, StronglyMeasurable[⨆ n, ℱ n] (fun ω ↦ bstarInf ω j) := fun j ↦
      ((measurable_pi_apply j).comp hInf_meas.measurable).stronglyMeasurable
    -- The stagewise conditional-expectation portfolio is `ℱ k`-measurable.
    have hc_meas : ∀ k, StronglyMeasurable[ℱ k] (condExpPortfolio μ ℱ bstarInf k) := by
      intro k
      have hM : Measurable[ℱ k] (condExpPortfolio μ ℱ bstarInf k) :=
        (@measurable_pi_iff Ω (Fin m) (fun _ : Fin m ↦ ℝ) (ℱ k) inferInstance
          (condExpPortfolio μ ℱ bstarInf k)).mpr fun j ↦ stronglyMeasurable_condExp.measurable
      exact hM.stronglyMeasurable
    -- It is a.e. simplex-valued (conditional expectation preserves nonnegativity and unit sum).
    have hc_ae_simplex : ∀ k, ∀ᵐ ω ∂μ,
        condExpPortfolio μ ℱ bstarInf k ω ∈ stdSimplex ℝ (Fin m) := by
      intro k
      have hnn : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ condExpPortfolio μ ℱ bstarInf k ω j := by
        rw [ae_all_iff]
        intro j
        exact condExp_nonneg (Filter.Eventually.of_forall fun ω ↦ (hInf_simplex ω).1 j)
      have hfun_eq : (∑ j : Fin m, fun ω' : Ω ↦ bstarInf ω' j) = (fun _ : Ω ↦ (1:ℝ)) := by
        funext ω'
        simp only [Finset.sum_apply]
        exact (hInf_simplex ω').2
      have hcondsum := condExp_finsetSum (μ := μ) (m := ℱ k) (s := (Finset.univ : Finset (Fin m)))
        (f := fun (j : Fin m) (ω' : Ω) ↦ bstarInf ω' j) (fun j _ ↦ hInf_int j)
      rw [hfun_eq, condExp_const (ℱ.le k) (1:ℝ)] at hcondsum
      filter_upwards [hnn, hcondsum] with ω hω_nn hω_sum
      refine ⟨hω_nn, ?_⟩
      show ∑ j, (μ[fun ω' ↦ bstarInf ω' j | ℱ k]) ω = 1
      simp only [Finset.sum_apply] at hω_sum
      exact hω_sum.symm
    -- Lévy's upward theorem: `c_k → bstarInf` a.e., coordinatewise.
    have hc_conv : ∀ᵐ ω ∂μ, ∀ j,
        Tendsto (fun k ↦ condExpPortfolio μ ℱ bstarInf k ω j) atTop (𝓝 (bstarInf ω j)) := by
      rw [ae_all_iff]
      intro j
      exact (hInf_int j).tendsto_ae_condExp (hInf_sm_sup j)
    -- The patched portfolio is an everywhere-simplex `ℱ k`-measurable competitor.
    have hcp_meas : ∀ k, StronglyMeasurable[ℱ k] (condExpPortfolioPatched μ ℱ bstarInf k) := by
      intro k
      unfold condExpPortfolioPatched
      exact StronglyMeasurable.ite ((hc_meas k).measurable
        (isClosed_stdSimplex (𝕜 := ℝ) (ι := Fin m)).measurableSet)
        (hc_meas k) stronglyMeasurable_const
    have hcp_simplex : ∀ k ω, condExpPortfolioPatched μ ℱ bstarInf k ω ∈ stdSimplex ℝ (Fin m) := by
      intro k ω
      unfold condExpPortfolioPatched
      by_cases h : condExpPortfolio μ ℱ bstarInf k ω ∈ stdSimplex ℝ (Fin m)
      · rw [if_pos h]; exact h
      · rw [if_neg h]; exact single_mem_stdSimplex ℝ (Classical.arbitrary (Fin m))
    have hcp_ae_eq : ∀ k, ∀ᵐ ω ∂μ,
        condExpPortfolioPatched μ ℱ bstarInf k ω = condExpPortfolio μ ℱ bstarInf k ω := by
      intro k
      filter_upwards [hc_ae_simplex k] with ω hω
      show condExpPortfolioPatched μ ℱ bstarInf k ω = condExpPortfolio μ ℱ bstarInf k ω
      unfold condExpPortfolioPatched
      exact if_pos hω
    -- Stagewise bound: `∫ log (cp_k · X) ≤ condOptGrowth k ≤ condOptGrowthInfty`.
    have hstage : ∀ k, ∫ ω, causalLogReturn X (condExpPortfolioPatched μ ℱ bstarInf k) ω ∂μ
        ≤ condOptGrowthInfty μ X bstar := by
      intro k
      have hstage_k : ∫ ω, causalLogReturn X (condExpPortfolioPatched μ ℱ bstarInf k) ω ∂μ
          ≤ condOptGrowth μ X bstar k := by
        calc ∫ ω, causalLogReturn X (condExpPortfolioPatched μ ℱ bstarInf k) ω ∂μ
            = ∫ ω, (μ[causalLogReturn X (condExpPortfolioPatched μ ℱ bstarInf k) | ℱ k]) ω ∂μ :=
              (integral_condExp (ℱ.le k)).symm
          _ ≤ ∫ ω, (μ[causalLogReturn X (bstar k) | ℱ k]) ω ∂μ :=
              integral_mono_ae integrable_condExp integrable_condExp
                (hbstar_dom k (condExpPortfolioPatched μ ℱ bstarInf k) (hcp_meas k) (hcp_simplex k))
          _ = ∫ ω, causalLogReturn X (bstar k) ω ∂μ := integral_condExp (ℱ.le k)
      exact le_trans hstage_k (le_ciSup hbdd k)
    -- Dominated convergence passes the bound to the limit.
    have hconv_ae : ∀ᵐ ω ∂μ, Tendsto
        (fun k ↦ causalLogReturn X (condExpPortfolioPatched μ ℱ bstarInf k) ω) atTop
        (𝓝 (causalLogReturn X bstarInf ω)) := by
      have hcp_eq_all : ∀ᵐ ω ∂μ, ∀ k, condExpPortfolioPatched μ ℱ bstarInf k ω
          = condExpPortfolio μ ℱ bstarInf k ω := ae_all_iff.mpr hcp_ae_eq
      filter_upwards [hc_conv, hcp_eq_all] with ω hconv hcpeq
      have hSumTo : Tendsto (fun k ↦ ∑ j, condExpPortfolio μ ℱ bstarInf k ω j * X ω j) atTop
          (𝓝 (∑ j, bstarInf ω j * X ω j)) :=
        tendsto_finsetSum _ fun j _ ↦ (hconv j).mul tendsto_const_nhds
      have hpos_inf : 0 < ∑ j, bstarInf ω j * X ω j := hpos ω (bstarInf ω) (hInf_simplex ω)
      have hLogTo : Tendsto
          (fun k ↦ Real.log (∑ j, condExpPortfolio μ ℱ bstarInf k ω j * X ω j)) atTop
          (𝓝 (Real.log (∑ j, bstarInf ω j * X ω j))) :=
        (Real.continuousAt_log hpos_inf.ne').tendsto.comp hSumTo
      have heq : (fun k ↦ causalLogReturn X (condExpPortfolioPatched μ ℱ bstarInf k) ω)
          = (fun k ↦ Real.log (∑ j, condExpPortfolio μ ℱ bstarInf k ω j * X ω j)) := by
        funext k
        simp only [causalLogReturn, hcpeq k]
      rw [heq]
      exact hLogTo
    have hdct : Tendsto
        (fun k ↦ ∫ ω, causalLogReturn X (condExpPortfolioPatched μ ℱ bstarInf k) ω ∂μ) atTop
        (𝓝 (∫ ω, causalLogReturn X bstarInf ω ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (logEnvelope X)
        (fun k ↦ ?_) (logEnvelope_integrable μ hint) (fun k ↦ ?_) hconv_ae
      · exact (Real.measurable_log.comp (Finset.measurable_sum _ fun j _ ↦
          ((measurable_pi_apply j).comp ((hcp_meas k).mono (ℱ.le k)).measurable).mul
            ((measurable_pi_apply j).comp hX))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs]
          exact logReturn_abs_le_envelope hpos ω (hcp_simplex k ω)
    exact le_of_tendsto hdct (Filter.Eventually.of_forall hstage)
  exact le_antisymm hLower h1

/-- Existence of an infinite-past (`⨆ j, ℱ j`) conditional log-optimal portfolio `bstarInf`:
instantiate `exists_condLogOptimalSeq` at the constant filtration `Filtration.const ℕ (⨆ j, ℱ j)`
(every stage is the infinite past) and read off stage `0`.

@audit:ok -/
theorem exists_infPast_condLogOptimal [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (X : Ω → Fin m → ℝ)
    [Nonempty (Fin m)] (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ) :
    ∃ bstarInf : Ω → Fin m → ℝ, StronglyMeasurable[⨆ j, ℱ j] bstarInf ∧
      (∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m)) ∧
      (∀ c : Ω → Fin m → ℝ, StronglyMeasurable[⨆ j, ℱ j] c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ⨆ j, ℱ j] ≤ᵐ[μ] μ[causalLogReturn X bstarInf | ⨆ j, ℱ j]) := by
  obtain ⟨b, hmeas, hsimplex, hdom⟩ :=
    exists_condLogOptimalSeq μ (Filtration.const ℕ (⨆ j, ℱ j) (iSup_le ℱ.le)) X hX hpos hint
  exact ⟨b 0, hmeas 0, fun ω ↦ hsimplex 0 ω, fun c hc hcs ↦ hdom 0 c hc hcs⟩

/-- A fixed infinite-past conditional log-optimal portfolio `bstarInf` achieves the optimal growth
rate `W_∞ = condOptGrowthInfty` as the almost-sure Birkhoff time average of its per-epoch log
return under a measure-preserving ergodic shift `T` (Cover–Thomas §16.5). The optimal
sequence `bstar` and its infinite-past companion `bstarInf` are constructed internally
(`exists_condOptGrowth_tendsto_condOptGrowthInfty` and `exists_infPast_condLogOptimal`) and their
conditional-dominance properties are established, so the conclusion carries no optimization
hypothesis; `hpos`/`hint`/`hUB`/`hT`/`hT_erg` are market-regularity/ergodicity preconditions.
The specialization of `ℱ` to the market-past filtration and `T` to the shift (giving the verbatim
CT 16.5.1 statement) is a downstream framing step.

@audit:ok -/
theorem stationaryInfPast_logOptimal_growth_tendsto_condOptGrowthInfty
    [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    (ℱ : Filtration ℕ m0) (X : Ω → Fin m → ℝ) [Nonempty (Fin m)] (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ)
    (hUB : ∃ C : ℝ, ∀ c : Ω → Fin m → ℝ, (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ → ∫ ω, causalLogReturn X c ω ∂μ ≤ C) :
    ∃ (bstar : ℕ → Ω → Fin m → ℝ) (bstarInf : Ω → Fin m → ℝ),
      Measurable bstarInf ∧ (∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m)) ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n ↦
        (∑ i ∈ Finset.range (n + 1), causalLogReturn X bstarInf (T^[i] ω)) / (n + 1 : ℝ))
        atTop (𝓝 (condOptGrowthInfty μ X bstar))) := by
  obtain ⟨bstar, hb_meas, hb_simplex, hb_dom, _htends⟩ :=
    exists_condOptGrowth_tendsto_condOptGrowthInfty μ ℱ X hX hpos hint hUB
  obtain ⟨bstarInf, hInf_meas, hInf_simplex, hInf_dom⟩ :=
    exists_infPast_condLogOptimal μ ℱ X hX hpos hint
  have hbstarInf_measurable : Measurable bstarInf := (hInf_meas.mono (iSup_le ℱ.le)).measurable
  have hid : ∫ ω, causalLogReturn X bstarInf ω ∂μ = condOptGrowthInfty μ X bstar :=
    condOptGrowthInfty_eq_integral_infPast μ ℱ X hX hpos hint bstar hb_meas hb_simplex hb_dom
      bstarInf hInf_meas hInf_simplex hInf_dom
  have hbirk := birkhoff_ergodic_ae hT hT_erg (hint bstarInf hbstarInf_measurable hInf_simplex)
  refine ⟨bstar, bstarInf, hbstarInf_measurable, hInf_simplex, ?_⟩
  filter_upwards [hbirk] with ω hω
  rw [← hid]
  exact hω

-- Slope limit `log (1 + λ t) / λ → t` as `λ → 0`: the derivative of `λ ↦ log (1 + λ t)` at `0`.
private theorem log_slope_tendsto_nhdsWithin (t : ℝ) :
    Tendsto (fun lam : ℝ ↦ Real.log (1 + lam * t) / lam) (𝓝[≠] (0 : ℝ)) (𝓝 t) := by
  have hd : HasDerivAt (fun x : ℝ ↦ Real.log (1 + x * t)) t 0 := by
    have h1 : HasDerivAt (fun x : ℝ ↦ 1 + x * t) t 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const t).const_add 1
    simpa using h1.log (by norm_num)
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  refine hslope.congr' ?_
  filter_upwards with lam
  rw [slope_def_field]
  simp

-- Two-sided bound on the slope: `log (1 + t) ≤ log (1 + λ t) / λ ≤ t` for `λ ∈ (0, 1]`, `t > -1`.
-- Upper bound is the tangent inequality `log x ≤ x − 1`; lower bound is concavity of `log`.
private theorem log_slope_bounds {t : ℝ} (ht : -1 < t) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam ≤ 1) :
    Real.log (1 + t) ≤ Real.log (1 + lam * t) / lam ∧ Real.log (1 + lam * t) / lam ≤ t := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have harg : (0 : ℝ) < 1 + lam * t := by nlinarith [mul_pos hlam0 h1t]
  constructor
  · rw [le_div_iff₀ hlam0]
    have hconc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr one_pos)
      (Set.mem_Ioi.mpr h1t) (by linarith : (0 : ℝ) ≤ 1 - lam) (le_of_lt hlam0)
      (by ring : (1 - lam) + lam = 1)
    simp only [Real.log_one, smul_eq_mul, mul_zero, zero_add] at hconc
    have he : (1 - lam) * 1 + lam * (1 + t) = 1 + lam * t := by ring
    rw [he] at hconc
    linarith [hconc]
  · rw [div_le_iff₀ hlam0]
    have := Real.log_le_sub_one_of_pos harg
    nlinarith [this]

-- An `m`-measurable conditional expectation whose set-integral over every `m`-measurable set is
-- nonpositive is a.e. nonpositive. Reduces `≤ᵐ` on `μ` to `≤ᵐ` on the trimmed measure `μ.trim`.
private theorem condExp_nonpos_of_forall_setIntegral_nonpos {α : Type*}
    {mα m0α : MeasurableSpace α} (hmα : mα ≤ m0α) (ν : @MeasureTheory.Measure α m0α)
    [IsFiniteMeasure ν] {f : α → ℝ} (hf : Integrable f ν)
    (H : ∀ s, MeasurableSet[mα] s → ∫ ω in s, f ω ∂ν ≤ 0) :
    ν[f | mα] ≤ᵐ[ν] 0 := by
  refine ae_le_of_ae_le_trim (hm := hmα) ?_
  refine ae_le_of_forall_setIntegral_le
    (integrable_condExp.trim hmα stronglyMeasurable_condExp) (integrable_zero _ _ _) ?_
  intro s hs _
  simp only [Pi.zero_apply, integral_zero]
  rw [← setIntegral_trim hmα stronglyMeasurable_condExp hs, setIntegral_condExp hmα hf hs]
  exact H s hs

/-- Conditional Kuhn–Tucker inequality for the infinite-past (`⨆ j, ℱ j`) conditional log-optimal
portfolio `bstarInf` (Cover–Thomas §16.5, Route M). For every `⨆ j, ℱ j`-measurable simplex
competitor `c`, the conditional expectation of the one-step wealth ratio
`(∑ⱼ cⱼ Xⱼ) / (∑ⱼ bstarInfⱼ Xⱼ)` given the infinite past is at most `1`. This is the multiplicative
form of the additive dominance `hInf_dom` — the one-step supermartingale bound at the heart of the
growing-memory wealth-ratio process.

The additive-to-multiplicative passage is the perturbation/first-order argument: for `λ ∈ (0, 1]`
the convex mix `bλ := (1 − λ) bstarInf + λ c` is a legal `⨆ j, ℱ j`-measurable simplex competitor,
so `hInf_dom bλ` gives `μ[log ((∑ bλ·X)/(∑ bstarInf·X)) | ⨆ ℱ] ≤ᵐ 0`, i.e.
`μ[log (1 + λ (r − 1)) | ⨆ ℱ] ≤ᵐ 0` where `r` is the wealth ratio. Dividing by `λ` and letting
`λ → 0` (dominated convergence, since `log r ≤ log (1 + λ (r − 1))/λ ≤ r − 1`) yields
`μ[r − 1 | ⨆ ℱ] ≤ᵐ 0`, hence `μ[r | ⨆ ℱ] ≤ᵐ 1`. The `hint_coord` hypothesis (integrability of the
coordinate ratios `Xᵢ / (∑ bstarInf·X)`) is a market-regularity precondition, mirroring the fixed-`b`
Kuhn–Tucker theorem `stationaryLogReturn_integral_le_of_kuhnTucker`; it makes the wealth ratio `r`
integrable so the conditional expectation is genuine. `hpos`/`hint` are the market-regularity
positivity/integrability preconditions; `[StandardBorelSpace Ω] [Nonempty Ω]` are inherited for
compatibility with the infinite-past filtration constructions. -/
theorem condKuhnTucker_infPast [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (X : Ω → Fin m → ℝ)
    [Nonempty (Fin m)] (hX : Measurable X)
    (hpos : ∀ ω, ∀ b ∈ stdSimplex ℝ (Fin m), 0 < ∑ j, b j * X ω j)
    (hint : ∀ c : Ω → Fin m → ℝ, Measurable c → (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
      Integrable (causalLogReturn X c) μ)
    (bstarInf : Ω → Fin m → ℝ) (hInf_meas : StronglyMeasurable[⨆ j, ℱ j] bstarInf)
    (hInf_simplex : ∀ ω, bstarInf ω ∈ stdSimplex ℝ (Fin m))
    (hint_coord : ∀ i, Integrable (fun ω ↦ X ω i / (∑ j, bstarInf ω j * X ω j)) μ)
    (hInf_dom : ∀ (c : Ω → Fin m → ℝ), StronglyMeasurable[⨆ j, ℱ j] c →
        (∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) →
        μ[causalLogReturn X c | ⨆ j, ℱ j] ≤ᵐ[μ] μ[causalLogReturn X bstarInf | ⨆ j, ℱ j])
    (c : Ω → Fin m → ℝ) (hc : StronglyMeasurable[⨆ j, ℱ j] c)
    (hcs : ∀ ω, c ω ∈ stdSimplex ℝ (Fin m)) :
    μ[fun ω ↦ (∑ j, c ω j * X ω j) / (∑ j, bstarInf ω j * X ω j) | ⨆ j, ℱ j] ≤ᵐ[μ] 1 := by
  classical
  have hm : (⨆ j, ℱ j) ≤ m0 := iSup_le ℱ.le
  have hSb_pos : ∀ ω, 0 < ∑ j, bstarInf ω j * X ω j :=
    fun ω ↦ hpos ω (bstarInf ω) (hInf_simplex ω)
  have hSc_pos : ∀ ω, 0 < ∑ j, c ω j * X ω j := fun ω ↦ hpos ω (c ω) (hcs ω)
  have hXpos : ∀ ω j, 0 < X ω j := fun ω j ↦ market_pos hpos ω j
  set r : Ω → ℝ := fun ω ↦ (∑ j, c ω j * X ω j) / (∑ j, bstarInf ω j * X ω j) with hr_def
  have hr_pos : ∀ ω, 0 < r ω := fun ω ↦ div_pos (hSc_pos ω) (hSb_pos ω)
  have hc_m : Measurable c := (hc.mono hm).measurable
  have hbInf_m : Measurable bstarInf := (hInf_meas.mono hm).measurable
  have hr_meas : Measurable r := by
    rw [hr_def]
    exact (Finset.measurable_sum _ fun j _ ↦
        ((measurable_pi_apply j).comp hc_m).mul ((measurable_pi_apply j).comp hX)).div
      (Finset.measurable_sum _ fun j _ ↦
        ((measurable_pi_apply j).comp hbInf_m).mul ((measurable_pi_apply j).comp hX))
  -- `r` is integrable: `0 ≤ r ω ≤ ∑ᵢ Xᵢ / (∑ bstarInf·X)`, and the bound is integrable via `hint_coord`.
  have hr_int : Integrable r μ := by
    have hbound_int : Integrable (fun ω ↦ ∑ i, X ω i / (∑ j, bstarInf ω j * X ω j)) μ :=
      integrable_finsetSum Finset.univ fun i _ ↦ hint_coord i
    refine Integrable.mono' hbound_int
      hr_meas.aestronglyMeasurable (Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hr_pos ω))]
    change (∑ j, c ω j * X ω j) / (∑ j, bstarInf ω j * X ω j)
      ≤ ∑ i, X ω i / (∑ j, bstarInf ω j * X ω j)
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [mul_div_assoc]
    exact mul_le_of_le_one_left (le_of_lt (div_pos (hXpos ω i) (hSb_pos ω)))
      (stdSimplex_component_le_one (hcs ω) i)
  -- Core reduction: `μ[r − 1 | ⨆ ℱ] ≤ᵐ 0`.
  have hkey : μ[fun ω ↦ r ω - 1 | ⨆ j, ℱ j] ≤ᵐ[μ] 0 := by
    refine condExp_nonpos_of_forall_setIntegral_nonpos hm μ (hr_int.sub (integrable_const 1)) ?_
    intro s hs
    -- Perturbation scale `λ_n = 1/(n+1) ↓ 0` and convex competitors `bLam n`.
    set lam : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hlam_def
    have hlam_pos : ∀ n, 0 < lam n := fun n ↦ by rw [hlam_def]; positivity
    have hlam_le : ∀ n, lam n ≤ 1 := fun n ↦ by
      rw [hlam_def, div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hlam_tendsto : Tendsto lam atTop (𝓝[≠] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun n ↦ (hlam_pos n).ne'⟩
    set bLam : ℕ → Ω → Fin m → ℝ :=
      fun n ω j ↦ (1 - lam n) * bstarInf ω j + lam n * c ω j with hbLam_def
    have hbLam_simplex : ∀ n ω, bLam n ω ∈ stdSimplex ℝ (Fin m) := fun n ω ↦
      convex_stdSimplex ℝ (Fin m) (hInf_simplex ω) (hcs ω)
        (by linarith [hlam_le n]) (le_of_lt (hlam_pos n)) (by ring)
    have hbLam_meas : ∀ n, StronglyMeasurable[⨆ j, ℱ j] (bLam n) := by
      intro n
      have heq : bLam n = fun ω ↦ (1 - lam n) • bstarInf ω + lam n • c ω := by
        funext ω j; simp [hbLam_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [heq]
      exact (hInf_meas.const_smul (1 - lam n)).add (hc.const_smul (lam n))
    have hbLam_ratio : ∀ n ω, ∑ j, bLam n ω j * X ω j
        = (∑ j, bstarInf ω j * X ω j) * (1 + lam n * (r ω - 1)) := by
      intro n ω
      have hSc_eq : ∑ j, c ω j * X ω j = r ω * (∑ j, bstarInf ω j * X ω j) := by
        have hne : (∑ j, bstarInf ω j * X ω j) ≠ 0 := ne_of_gt (hSb_pos ω)
        rw [hr_def]; field_simp
      have hexpand : ∑ j, bLam n ω j * X ω j
          = (1 - lam n) * (∑ j, bstarInf ω j * X ω j) + lam n * (∑ j, c ω j * X ω j) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ ↦ by simp only [hbLam_def]; ring
      rw [hexpand, hSc_eq]; ring
    have hbLam_pos : ∀ n ω, 0 < ∑ j, bLam n ω j * X ω j :=
      fun n ω ↦ hpos ω (bLam n ω) (hbLam_simplex n ω)
    have h_arg_pos : ∀ n ω, 0 < 1 + lam n * (r ω - 1) := by
      intro n ω
      have heq : 1 + lam n * (r ω - 1) = (1 - lam n) + lam n * r ω := by ring
      rw [heq]; nlinarith [mul_pos (hlam_pos n) (hr_pos ω), hlam_le n]
    have h_logdiff : ∀ n ω, causalLogReturn X (bLam n) ω - causalLogReturn X bstarInf ω
        = Real.log (1 + lam n * (r ω - 1)) := by
      intro n ω
      unfold causalLogReturn
      rw [hbLam_ratio n ω, Real.log_mul (ne_of_gt (hSb_pos ω)) (ne_of_gt (h_arg_pos n ω))]
      ring
    have hbn_int : ∀ n, Integrable (causalLogReturn X (bLam n)) μ := fun n ↦
      hint (bLam n) ((hbLam_meas n).mono hm).measurable (hbLam_simplex n)
    have hbInf_int : Integrable (causalLogReturn X bstarInf) μ :=
      hint bstarInf hbInf_m hInf_simplex
    -- Each perturbed log-ratio integral over `s` is nonpositive (from the additive dominance).
    have hgn_setint_nonpos : ∀ n,
        ∫ ω in s, Real.log (1 + lam n * (r ω - 1)) / lam n ∂μ ≤ 0 := by
      intro n
      rw [integral_div]
      refine div_nonpos_iff.mpr (Or.inr ⟨?_, le_of_lt (hlam_pos n)⟩)
      have heq : ∫ ω in s, Real.log (1 + lam n * (r ω - 1)) ∂μ
          = ∫ ω in s, causalLogReturn X (bLam n) ω ∂μ
            - ∫ ω in s, causalLogReturn X bstarInf ω ∂μ := by
        rw [← integral_sub (hbn_int n).integrableOn hbInf_int.integrableOn]
        refine setIntegral_congr_ae (hm _ hs) (Eventually.of_forall fun ω _ ↦ ?_)
        rw [← h_logdiff n ω]
      rw [heq, sub_nonpos, ← setIntegral_condExp hm (hbn_int n) hs,
        ← setIntegral_condExp hm hbInf_int hs]
      exact setIntegral_mono_ae integrable_condExp.integrableOn integrable_condExp.integrableOn
        (hInf_dom (bLam n) (hbLam_meas n) (hbLam_simplex n))
    -- Dominated convergence: the perturbed integrals converge to `∫ₛ (r − 1)`.
    have hlogr_int : Integrable (fun ω ↦ Real.log (r ω)) μ := by
      have heq : (fun ω ↦ Real.log (r ω))
          = fun ω ↦ causalLogReturn X c ω - causalLogReturn X bstarInf ω := by
        funext ω
        simp only [hr_def]
        unfold causalLogReturn
        rw [Real.log_div (ne_of_gt (hSc_pos ω)) (ne_of_gt (hSb_pos ω))]
      rw [heq]
      exact (hint c hc_m hcs).sub hbInf_int
    have hgn_conv : Tendsto
        (fun n ↦ ∫ ω in s, Real.log (1 + lam n * (r ω - 1)) / lam n ∂μ) atTop
        (𝓝 (∫ ω in s, (r ω - 1) ∂μ)) := by
      set G : Ω → ℝ := fun ω ↦ |Real.log (r ω)| + |r ω - 1| with hG_def
      have hG_int : Integrable G μ :=
        hlogr_int.abs.add (hr_int.sub (integrable_const 1)).abs
      have hgn_meas : ∀ n, Measurable (fun ω ↦ Real.log (1 + lam n * (r ω - 1)) / lam n) :=
        fun n ↦ ((Real.measurable_log.comp (measurable_const.add
          (measurable_const.mul (hr_meas.sub measurable_const)))).div measurable_const)
      refine tendsto_integral_of_dominated_convergence G
        (fun n ↦ (hgn_meas n).aestronglyMeasurable.restrict) hG_int.integrableOn
        (fun n ↦ ?_) ?_
      · refine ae_restrict_of_ae (Eventually.of_forall fun ω ↦ ?_)
        rw [Real.norm_eq_abs]
        obtain ⟨hlo, hhi⟩ := log_slope_bounds (t := r ω - 1) (by linarith [hr_pos ω])
          (hlam_pos n) (hlam_le n)
        have hlo' : Real.log (r ω) ≤ Real.log (1 + lam n * (r ω - 1)) / lam n := by
          have hh : (1 : ℝ) + (r ω - 1) = r ω := by ring
          rwa [hh] at hlo
        rw [abs_le]
        refine ⟨?_, ?_⟩
        · have h1 := neg_abs_le (Real.log (r ω))
          have h2 := abs_nonneg (r ω - 1)
          simp only [hG_def]; linarith [hlo']
        · have h1 := le_abs_self (r ω - 1)
          have h2 := abs_nonneg (Real.log (r ω))
          simp only [hG_def]; linarith [hhi]
      · refine ae_restrict_of_ae (Eventually.of_forall fun ω ↦ ?_)
        exact (log_slope_tendsto_nhdsWithin (r ω - 1)).comp hlam_tendsto
    exact le_of_tendsto hgn_conv (Eventually.of_forall hgn_setint_nonpos)
  -- Assemble: `μ[r | ⨆ ℱ] =ᵐ μ[r − 1 | ⨆ ℱ] + 1 ≤ᵐ 1`.
  have hr_eq : (fun ω ↦ r ω - 1) + (fun _ ↦ (1 : ℝ)) = r := by funext ω; simp
  have hadd := condExp_add (μ := μ) (f := fun ω ↦ r ω - 1) (g := fun _ ↦ (1 : ℝ))
    (hr_int.sub (integrable_const 1)) (integrable_const 1) (⨆ j, ℱ j)
  rw [hr_eq, condExp_const hm (1 : ℝ)] at hadd
  filter_upwards [hadd, hkey] with ω hω hk
  rw [hω]
  simp only [Pi.add_apply, Pi.one_apply]
  simp only [Pi.zero_apply] at hk
  linarith

end CondOptimalGrowth

end InformationTheory.Shannon.Portfolio
