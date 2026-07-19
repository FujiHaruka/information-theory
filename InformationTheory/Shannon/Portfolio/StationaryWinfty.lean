import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Bases
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

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

open MeasureTheory Filter Topology Set
open scoped BigOperators

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
precondition: for `m = 0` the simplex is empty and no selection into it exists. -/
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

end InformationTheory.Shannon.Portfolio
