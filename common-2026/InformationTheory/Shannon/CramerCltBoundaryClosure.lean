import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.Portmanteau
import InformationTheory.Draft.Shannon.InfinitePiTiltedChangeOfMeasure

/-!
# Cramér / Chernoff CLT-boundary closure

This file closes the **boundary case** `a = m` (= tilted mean = `deriv (cgf Y μ₀) lam`)
of the residual window predicate `IsTiltedWindowEventuallyLarge`, the only piece left
after the change-of-measure machinery (Phases 1–3 of the parent
`infinitepi-tilted-rn-discharge`) is discharged. The interior case
`a < m < a + ε` is handled by the existing two-sided LLN squeeze
(`tiltedWindow_eventually_large_of_interior`); the boundary case requires a CLT
refinement, supplied here.

## Outline (plan `cramer-chernoff-clt-closure-moonshot-plan`)

* **Phase 1** — `gaussianReal_Ici_eq_half` (Gaussian median, symmetry-by-map). CLOSED.
* **Phase 3** — apply the CLT `tendstoInDistribution_inv_sqrt_mul_sum_sub` to the tilted
  ambient, with the existing `iIndepFun` / `IdentDistrib` / bounded plumbing and a
  self-built `HasLaw id (gaussianReal 0 v.toNNReal)` witness.
* **Phase 2** — portmanteau half-line bridge: `frontier (Ici 0) = {0}` is null under
  `gaussianReal 0 v` (`noAtoms`), so the CLT weak convergence transfers to the half-line
  mass.
* **scaling** — the window event `{m·n ≤ ∑Y}` is the `S_n`-preimage of `Ici 0`, which
  identifies the CLT half-line mass with `P{m·n ≤ ∑Y}`.
* **Phase 4** — `tiltedWindow_eventually_large_of_boundary`: the window mass
  `P{m·n ≤ ∑Y} − P{(m+ε)·n ≤ ∑Y}` tends to `1/2 − 0 = 1/2 ≥ 1/4` (the second term
  vanishes by the one-sided LLN).
* **Phase 5** — a relaxed `∃C>0` window predicate + a new reduction to
  `IsMeasureInfinitePiTiltedEq`, discharged at `a = m`.
* **Phase 6** — Cramér end-to-end lower bound at the interior point
  `a = deriv (cgf Y μ₀) lam`, with the residual hypothesis removed.
-/

namespace InformationTheory.Shannon.CramerCltBoundary

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

/-- The centred Gaussian `𝒩(0, v)` (with `v ≠ 0`) assigns mass exactly `1/2` to the
half-line `{x | 0 ≤ x}`. Symmetry-by-map: `x ↦ -x` swaps the two closed half-lines and
fixes `gaussianReal 0 v`. -/
theorem gaussianReal_Ici_eq_half {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v {x : ℝ | (0 : ℝ) ≤ x} = 1 / 2 := by
  set μ : Measure ℝ := gaussianReal 0 v with hμ
  -- The half-line `{x | 0 ≤ x}` as `Set.Ici 0`.
  have hIci : {x : ℝ | (0 : ℝ) ≤ x} = Set.Ici (0 : ℝ) := by
    ext x; simp [Set.mem_Ici]
  -- Step 1: symmetry-by-map gives equal mass on the two half-lines.
  have hsymm : μ (Set.Ici (0 : ℝ)) = μ (Set.Iic (0 : ℝ)) := by
    -- `x ↦ -x` fixes `gaussianReal 0 v` (`gaussianReal_map_neg`, `-0 = 0`).
    have hmap : μ.map (fun x : ℝ ↦ -x) = μ := by
      rw [hμ, gaussianReal_map_neg, neg_zero]
    have hpre : (fun x : ℝ ↦ -x) ⁻¹' Set.Ici (0 : ℝ) = Set.Iic (0 : ℝ) := by
      ext x; simp [Set.mem_Iic]
    calc μ (Set.Ici (0 : ℝ))
        = (μ.map (fun x : ℝ ↦ -x)) (Set.Ici (0 : ℝ)) := by rw [hmap]
      _ = μ ((fun x : ℝ ↦ -x) ⁻¹' Set.Ici (0 : ℝ)) :=
          Measure.map_apply (by fun_prop) measurableSet_Ici
      _ = μ (Set.Iic (0 : ℝ)) := by rw [hpre]
  -- Step 2: union = univ, intersection = {0}.
  have hunion : Set.Ici (0 : ℝ) ∪ Set.Iic (0 : ℝ) = Set.univ := by
    rw [Set.union_comm]; exact Set.Iic_union_Ici
  have hinter : Set.Ici (0 : ℝ) ∩ Set.Iic (0 : ℝ) = {(0 : ℝ)} := by
    rw [Set.Ici_inter_Iic, Set.Icc_self]
  have hsingleton : μ ({(0 : ℝ)} : Set ℝ) = 0 := by
    haveI : NoAtoms μ := noAtoms_gaussianReal hv
    exact measure_singleton 0
  -- Step 3: `measure_union_add_inter` ⇒ `2 * μ(Ici 0) = 1`, ENNReal arithmetic.
  have htwo : 2 * μ (Set.Ici (0 : ℝ)) = 1 := by
    have hadd := measure_union_add_inter (μ := μ) (Set.Ici (0 : ℝ))
      (t := Set.Iic (0 : ℝ)) measurableSet_Iic
    rw [hunion, hinter, hsingleton, add_zero, ← hsymm, measure_univ] at hadd
    rw [two_mul, ← hadd]
  have hhalf : μ (Set.Ici (0 : ℝ)) = 1 / 2 := by
    rw [ENNReal.eq_div_iff (by norm_num) (by norm_num), mul_comm, ← htwo, mul_comm]
  rw [hIci]; exact hhalf

/-! ## Phase 3 — CLT applied to the tilted ambient -/

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- **Gaussian self-law witness** (Phase 3): the identity map on `ℝ` has law
`gaussianReal 0 w` under `gaussianReal 0 w`. Supplies the `HasLaw Y (gaussianReal 0 …)`
argument of the CLT with the trivial witness `(ℝ, gaussianReal 0 w, id)`. -/
theorem gaussianReal_hasLaw_id {w : ℝ≥0} :
    HasLaw (id : ℝ → ℝ) (gaussianReal 0 w) (gaussianReal 0 w) where
  aemeasurable := aemeasurable_id
  map_eq := Measure.map_id

/-- **Half-line mass tends to the Gaussian median** (Phase 3 CLT + Phase 2 portmanteau +
scaling). The tilted-ambient mass (ℝ≥0∞-valued) of the half-line
`{ω | m·n ≤ ∑_{i<n} Y(ω i)}` (at the tilted mean `m = ∫ Y ∂tilted`) converges to the
Gaussian mass `gaussianReal 0 v.toNNReal (Ici 0)`.

Route: apply `tendstoInDistribution_inv_sqrt_mul_sum_sub` to `X i ω := Y (ω i)` under the
tilted ambient (with the self-built `gaussianReal_hasLaw_id` witness and the existing
`iIndepFun` / `IdentDistrib` / bounded plumbing); take its `.tendsto` field; feed it to the
portmanteau half-line lemma (`frontier (Ici 0) = {0}`, null under `noAtoms`); identify the
window event with the `S_n`-preimage of `Ici 0` via `Measure.map_apply`. -/
theorem tilted_halfline_tendsto_gaussian
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))]) :
    Tendsto
      (fun n : ℕ =>
        (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
          {ω : ℕ → Ω₀ |
            (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n
              ≤ ∑ i ∈ Finset.range n, Y (ω i)})
      atTop
      (𝓝 (gaussianReal 0
          (Var[fun ω : ℕ → Ω₀ => Y (ω 0);
              Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))]).toNNReal
        (Set.Ici (0 : ℝ)))) := by
  haveI hP : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    Cramer.Discharge.isProbabilityMeasure_infinitePi_tilted_of_bounded hY h_bdd lam
  set P : Measure (ℕ → Ω₀) :=
    Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) with hPdef
  set X : ℕ → (ℕ → Ω₀) → ℝ := fun i ω => Y (ω i) with hXdef
  set v : ℝ := Var[fun ω : ℕ → Ω₀ => Y (ω 0); P] with hvdef
  -- `P[X 0] = m := ∫ Y ∂tilted`.
  have hmean : P[X 0] = ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) :=
    Cramer.Discharge.integral_eval_under_infinitePi_tilted hY h_bdd lam
  -- CLT ingredients.
  have hindep : iIndepFun X P := Cramer.Discharge.iIndepFun_tilted_ambient hY h_bdd lam
  have hident : ∀ i : ℕ, IdentDistrib (X i) (X 0) P P :=
    fun i => Cramer.Discharge.identDistrib_tilted_ambient hY h_bdd lam i
  -- `MemLp (X 0) 2 P` from boundedness.
  have hMemLp : MemLp (X 0) 2 P := by
    obtain ⟨M, hM⟩ := h_bdd
    refine memLp_of_bounded (a := -M) (b := M) ?_ ?_ 2
    · exact Filter.Eventually.of_forall (fun ω => by
        have := hM (ω 0)
        rw [abs_le] at this
        exact ⟨this.1, this.2⟩)
    · exact (hY.comp (measurable_pi_apply 0)).aestronglyMeasurable
  -- The CLT witness: `id : ℝ → ℝ` has law `gaussianReal 0 v.toNNReal` under itself.
  have hY_law : HasLaw (id : ℝ → ℝ) (gaussianReal 0 v.toNNReal) (gaussianReal 0 v.toNNReal) :=
    gaussianReal_hasLaw_id
  -- Apply the CLT.
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (P := P) (P' := gaussianReal 0 v.toNNReal)
    (X := X) (Y := (id : ℝ → ℝ)) hY_law hMemLp hindep hident
  -- Extract the `.tendsto` field (weak convergence in `ProbabilityMeasure ℝ`).
  have htend := hclt.tendsto
  -- Portmanteau half-line: frontier (Ici 0) is null under the Gaussian.
  have hbdry : (gaussianReal 0 v.toNNReal) (frontier (Set.Ici (0 : ℝ))) = 0 := by
    haveI : NoAtoms (gaussianReal 0 v.toNNReal) :=
      noAtoms_gaussianReal (by
        rw [hvdef] at hVar ⊢
        exact (Real.toNNReal_pos).2 hVar |>.ne')
    rw [frontier_Ici, measure_singleton]
  -- The limit measure in `htend` is `(gaussianReal 0 v.toNNReal).map id`; identify with itself.
  have hlim_eq : (gaussianReal 0 v.toNNReal).map (id : ℝ → ℝ) = gaussianReal 0 v.toNNReal :=
    Measure.map_id
  -- Portmanteau gives the half-line mass convergence (ℝ≥0∞-valued).
  have hnull : ((gaussianReal 0 v.toNNReal).map (id : ℝ → ℝ)) (frontier (Set.Ici (0 : ℝ))) = 0 := by
    rw [hlim_eq]; exact hbdry
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    htend (E := Set.Ici (0 : ℝ)) hnull
  -- Simplify the coercions: `μs n` mass = `(P.map S_n)(Ici 0)`, limit = `(P'.map id)(Ici 0)`.
  simp only [ProbabilityMeasure.coe_mk] at hport
  rw [hlim_eq] at hport
  -- Scaling: `(P.map S_n)(Ici 0) = P{m·n ≤ ∑Y}` for every `n`.
  refine hport.congr (fun n => ?_)
  -- `S_n` is measurable.
  have hSmeas : Measurable
      (fun ω : ℕ → Ω₀ => (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, X k ω - n * P[X 0])) := by
    apply Measurable.const_mul
    apply Measurable.sub _ measurable_const
    exact Finset.measurable_sum _ (fun k _ => hY.comp (measurable_pi_apply k))
  rw [Measure.map_apply hSmeas measurableSet_Ici]
  -- Preimage identity: `S_n ∈ Ici 0 ⟺ m·n ≤ ∑Y`.
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_setOf_eq, hXdef]
  rw [hmean]
  -- `0 ≤ (√n)⁻¹·(∑Y − n·m) ⟺ m·n ≤ ∑Y`.
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hsqrt : (0 : ℝ) < (Real.sqrt n)⁻¹ := by
      apply inv_pos.2
      exact Real.sqrt_pos.2 (by exact_mod_cast hn)
    rw [mul_nonneg_iff_of_pos_left hsqrt, sub_nonneg, mul_comm]

/-! ## Phase 2 + scaling — half-line mass tends to `1/2` -/

/-- **Half-line mass tends to `1/2`** (Phase 1 median applied to the Gaussian half-line
limit). The tilted-ambient `.real`-mass of `{ω | m·n ≤ ∑_{i<n} Y(ω i)}` tends to `1/2`. -/
theorem tilted_halfline_tendsto_half
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))]) :
    Tendsto
      (fun n : ℕ =>
        (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ |
            (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n
              ≤ ∑ i ∈ Finset.range n, Y (ω i)})
      atTop (𝓝 (1 / 2)) := by
  set v : ℝ := Var[fun ω : ℕ → Ω₀ => Y (ω 0);
    Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))] with hvdef
  -- The Gaussian half-line mass is exactly `1/2` (Phase 1, `Ici 0 = {x | 0 ≤ x}`).
  have hmedian : gaussianReal 0 v.toNNReal (Set.Ici (0 : ℝ)) = 1 / 2 := by
    have hset : Set.Ici (0 : ℝ) = {x : ℝ | (0 : ℝ) ≤ x} := by
      ext x; simp [Set.mem_Ici]
    rw [hset]
    exact gaussianReal_Ici_eq_half (by
      rw [hvdef] at hVar
      exact (Real.toNNReal_pos).2 hVar |>.ne')
  -- ℝ≥0∞ → ℝ via `toReal`, limit `(1/2 : ℝ≥0∞).toReal = 1/2`.
  have hgauss := tilted_halfline_tendsto_gaussian hY h_bdd lam hVar
  rw [← hvdef] at hgauss
  have htoReal := (ENNReal.tendsto_toReal (a := gaussianReal 0 v.toNNReal (Set.Ici (0 : ℝ)))
    (by rw [hmedian]; exact (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤))).comp hgauss
  rw [hmedian] at htoReal
  have hlim : ((1 : ℝ≥0∞) / 2).toReal = (1 / 2 : ℝ) := by
    rw [ENNReal.toReal_div]; norm_num
  rw [hlim] at htoReal
  -- `Measure.real s = (μ s).toReal`, so the two functions agree.
  exact htoReal

/-! ## Phase 4 — window mass eventually `≥ 1/4` at the boundary -/

/-- **Boundary window largeness** (Phase 4). At the boundary `a = m` (= tilted mean),
the tilted infinite-product window mass `{ω | m·n ≤ ∑Y < (m+ε)·n}` is eventually `≥ 1/4`.
The lower half-line tends to `1/2` (Phase 2 + scaling + median); the upper half-line at
`m + ε > m` vanishes by the one-sided LLN; their difference tends to `1/2 ≥ 1/4`. -/
theorem tiltedWindow_eventually_large_of_boundary
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))]) :
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 4 ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ |
            (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i)
                < ((∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) + ε) * n} := by
  haveI hP : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))) :=
    Cramer.Discharge.isProbabilityMeasure_infinitePi_tilted_of_bounded hY h_bdd lam
  set P : Measure (ℕ → Ω₀) :=
    Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)) with hPdef
  set m : ℝ := ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) with hmdef
  -- Lower half-line, upper half-line, window events.
  set L : ℕ → Set (ℕ → Ω₀) := fun n =>
    {ω : ℕ → Ω₀ | m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} with hLdef
  set U : ℕ → Set (ℕ → Ω₀) := fun n =>
    {ω : ℕ → Ω₀ | (m + ε) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} with hUdef
  set W : ℕ → Set (ℕ → Ω₀) := fun n =>
    {ω : ℕ → Ω₀ | m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
      ∧ ∑ i ∈ Finset.range n, Y (ω i) < (m + ε) * n} with hWdef
  -- Measurability of the partial-sum events.
  have hsum_meas : ∀ n : ℕ, Measurable (fun ω : ℕ → Ω₀ => ∑ i ∈ Finset.range n, Y (ω i)) :=
    fun n => Finset.measurable_sum _ (fun i _ => hY.comp (measurable_pi_apply i))
  have hL_meas : ∀ n, MeasurableSet (L n) := fun n =>
    measurableSet_le measurable_const (hsum_meas n)
  have hU_meas : ∀ n, MeasurableSet (U n) := fun n =>
    measurableSet_le measurable_const (hsum_meas n)
  -- Lower half-line mass → 1/2.
  have hlower : Tendsto (fun n : ℕ => P.real (L n)) atTop (𝓝 (1 / 2)) :=
    tilted_halfline_tendsto_half hY h_bdd lam hVar
  -- Upper half-line mass → 0, dominated by the LLN bad set `{ε ≤ |S̄_n − m|}`.
  have hupper : Tendsto (fun n : ℕ => P.real (U n)) atTop (𝓝 0) := by
    have hbad := Cramer.Discharge.tilted_lln_in_probability_real
      (μ₀ := μ₀) hY h_bdd lam (ε := ε) hε
    rw [← hPdef, ← hmdef] at hbad
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad ?_ ?_
    · exact Eventually.of_forall (fun n => measureReal_nonneg)
    · -- `U n ⊆ {ε ≤ |S̄_n − m|}` for `n ≥ 1`.
      filter_upwards [eventually_ge_atTop 1] with n hn
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      simp only [hUdef, Set.mem_setOf_eq] at hω
      simp only [Set.mem_setOf_eq]
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hge : m + ε ≤ (∑ i ∈ Finset.range n, Y (ω i)) / n := (le_div_iff₀ hnpos).mpr hω
      rw [le_abs]
      left; linarith [hge]
  -- Window mass = lower mass − upper mass (since `U n ⊆ L n`).
  have hWeq : ∀ n, P.real (W n) = P.real (L n) - P.real (U n) := by
    intro n
    have hsub : U n ⊆ L n := by
      intro ω hω
      simp only [hUdef, Set.mem_setOf_eq] at hω
      simp only [hLdef, Set.mem_setOf_eq]
      have : m * n ≤ (m + ε) * n := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp
        · have hnpos : (0 : ℝ) ≤ n := by positivity
          nlinarith [hε.le, hnpos]
      linarith [hω, this]
    have hWLU : W n = L n \ U n := by
      ext ω
      simp only [hWdef, hLdef, hUdef, Set.mem_setOf_eq, Set.mem_diff, not_le]
    rw [hWLU, measureReal_diff hsub (hU_meas n) (measure_ne_top _ _)]
  -- Window mass → 1/2 − 0 = 1/2.
  have hwindow : Tendsto (fun n : ℕ => P.real (W n)) atTop (𝓝 (1 / 2)) := by
    have h := hlower.sub hupper
    rw [sub_zero] at h
    exact h.congr (fun n => (hWeq n).symm)
  -- Eventually `≥ 1/4`.
  exact hwindow.eventually_const_le (by norm_num)

/-! ## Phase 5 — relaxed window predicate + boundary discharge -/

/-- **Relaxed residual window predicate** (Phase 5). The `1/2` threshold of the existing
`IsTiltedWindowEventuallyLarge` is relaxed to an existential constant `∃ C > 0`. This
absorbs the boundary `1/4` of `tiltedWindow_eventually_large_of_boundary` while keeping
the reduction to `IsMeasureInfinitePiTiltedEq` intact. -/
def IsTiltedWindowEventuallyLargeC (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
  ∀ a ε : ℝ, 0 < ε →
    ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n}

/-- **Per-instance change-of-measure half-line lower bound** (Phase 5 core). At a single
threshold `a` and `ε > 0`, eventual largeness `C ≤ tilted-window mass` lifts (via the
finite-level change-of-measure `change_of_measure_lower_bound_pi` and the cylinder lift)
to the un-tilted half-line lower bound `C·exp(-n(λa - Λ + λε)) ≤ P{a·n ≤ ∑Y}`. This is the
per-`(a, ε)` body shared by the relaxed `∀a` reduction and the boundary liminf bridge. -/
theorem tilted_window_lower_to_halfline
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) (hlam : 0 ≤ lam)
    (a ε : ℝ) {C : ℝ} {n : ℕ}
    (hn : C ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
        {ω : ℕ → Ω₀ | a * (n : ℝ) ≤ ∑ i ∈ Finset.range n, Y (ω i)
          ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n}) :
    C * Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
      ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
          {ω : ℕ → Ω₀ | a * (n : ℝ) ≤ ∑ i ∈ Finset.range n, Y (ω i)} := by
  haveI hp : IsProbabilityMeasure (μ₀.tilted (fun ω => lam * Y ω)) :=
    Cramer.isProbabilityMeasure_tilted_of_bounded hY h_bdd lam
  -- Cylinder lift, un-tilted side: half-line event.
  have hPE : MeasurableSet {r : ℝ | a * (n : ℝ) ≤ r} :=
    measurableSet_le measurable_const measurable_id
  have hlift_E := Cramer.Discharge.infinitePi_partialSum_event_eq_pi (ν := μ₀) hY n
      (fun r => a * (n : ℝ) ≤ r) hPE
  -- Cylinder lift, tilted side: window event.
  have hPW : MeasurableSet {r : ℝ | a * (n : ℝ) ≤ r ∧ r < (a + ε) * n} :=
    (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)
  have hlift_W := Cramer.Discharge.infinitePi_partialSum_event_eq_pi
      (ν := μ₀.tilted (fun ω => lam * Y ω)) hY n
      (fun r => a * (n : ℝ) ≤ r ∧ r < (a + ε) * n) hPW
  -- Phase 3 change-of-measure at the finite level.
  have hcm := Cramer.Discharge.change_of_measure_lower_bound_pi
    (n := n) (μ₀ := μ₀) hY h_bdd a ε lam hlam
  have hfin_E : (Measure.pi (fun _ : Fin n => μ₀))
      {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i)} ≠ ⊤ := (measure_ne_top _ _)
  have hcm_real :
      Real.exp (-(n : ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
          * (Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω))).real
              {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i) ∧ ∑ i, Y (x i) < (a + ε) * n}
        ≤ (Measure.pi (fun _ : Fin n => μ₀)).real
              {x : Fin n → Ω₀ | a * n ≤ ∑ i, Y (x i)} := by
    have h := ENNReal.toReal_mono hfin_E hcm
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))] at h
  -- Cylinder lift identifies the un-tilted half-line `.real`.
  have hE_real : (Measure.infinitePi (fun _ : ℕ => μ₀)).real
        {ω : ℕ → Ω₀ | a * (n : ℝ) ≤ ∑ i ∈ Finset.range n, Y (ω i)}
      = (Measure.pi (fun _ : Fin n => μ₀)).real
          {x : Fin n → Ω₀ | a * (n : ℝ) ≤ ∑ i, Y (x i)} := by
    rw [measureReal_def, measureReal_def, hlift_E]
  -- Cylinder lift identifies the tilted window `.real`.
  have hW_real : (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
        {ω : ℕ → Ω₀ | a * (n : ℝ) ≤ ∑ i ∈ Finset.range n, Y (ω i)
          ∧ ∑ i ∈ Finset.range n, Y (ω i) < (a + ε) * n}
      = (Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω))).real
          {x : Fin n → Ω₀ | a * (n : ℝ) ≤ ∑ i, Y (x i) ∧ ∑ i, Y (x i) < (a + ε) * n} := by
    rw [measureReal_def, measureReal_def, hlift_W]
  rw [hE_real]
  refine le_trans ?_ hcm_real
  rw [mul_comm C]
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
  rw [hW_real] at hn
  exact hn

/-- **Relaxed reduction** (Phase 5). The relaxed window predicate implies the full
n-letter RN-deriv predicate `IsMeasureInfinitePiTiltedEq`, by the same change-of-measure
lower bound as `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge`, threading the existential
constant `C` instead of the fixed `1/2`.

This is a genuine *implication* (a reduction tool). Its hypothesis
`IsTiltedWindowEventuallyLargeC` is the relaxed `∀a∀ε` window predicate; it is *false in
general* (for `a` far from the tilted mean the window has vanishing mass) and is satisfiable
only at the boundary threshold. Phase 6 therefore bypasses this `∀a` predicate and uses the
per-`(a, ε)` core `tilted_window_lower_to_halfline` directly at `a = m`. -/
theorem isMeasureInfinitePiTiltedEq_of_tiltedWindowLargeC
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) (hlam : 0 ≤ lam)
    (h_res : IsTiltedWindowEventuallyLargeC μ₀ Y lam) :
    Cramer.Discharge.IsMeasureInfinitePiTiltedEq μ₀ Y lam := by
  intro a ε hε
  obtain ⟨C, hCpos, hev⟩ := h_res a ε hε
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hev] with n hn
  exact tilted_window_lower_to_halfline hY h_bdd lam hlam a ε hn

/-! ## Phase 6 — Cramér end-to-end lower bound at the interior optimal tilt -/

/-- **Per-`ε` boundary liminf lower bound** (Phase 6 core). At the boundary `a = m`
(= tilted mean `∫ Y ∂tilted`), for each `ε > 0`, the half-line tail rate is eventually
bounded below by `(1/n)·log((1/4)·exp(-n(λm - Λ + λε)))`, whose limit is
`-(λm - Λ + λε)`. By `liminf_le_liminf`, `-(λm - Λ + λε) ≤ liminf (1/n)·log P{m·n ≤ ∑Y}`. -/
theorem boundary_liminf_lower_of_eps
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) (hlam : 0 ≤ lam)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))])
    {ε : ℝ} (hε : 0 < ε)
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ |
              (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n
                ≤ ∑ i ∈ Finset.range n, Y (ω i)}))) :
    -(lam * (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) - cgf Y μ₀ lam + lam * ε)
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ |
                (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n
                  ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop := by
  set m : ℝ := ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) with hmdef
  -- The lower envelope `g_ε`.
  set g : ℕ → ℝ := fun n =>
    (1 / (n : ℝ)) * Real.log ((1 / 4 : ℝ)
      * Real.exp (-(n : ℝ) * (lam * m - cgf Y μ₀ lam + lam * ε)))
    with hgdef
  -- `g n → -(λm - Λ + λε)`.
  have hg_tendsto : Tendsto g atTop (𝓝 (-(lam * m - cgf Y μ₀ lam + lam * ε))) := by
    have hg_eq : ∀ n : ℕ, 1 ≤ n → g n
        = (1 / (n : ℝ)) * Real.log (1 / 4) - (lam * m - cgf Y μ₀ lam + lam * ε) := by
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [hgdef]
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
      field_simp
      ring
    -- `(1/n)·log(1/4) → 0`, so `g n → 0 - (...) = -(...)`.
    have h0 : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (1 / 4)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (Real.log (1 / 4)))
      simpa [div_eq_mul_inv, mul_comm] using this
    have hfull : Tendsto
        (fun n : ℕ => (1 / (n : ℝ)) * Real.log (1 / 4) - (lam * m - cgf Y μ₀ lam + lam * ε))
        atTop (𝓝 (0 - (lam * m - cgf Y μ₀ lam + lam * ε))) :=
      h0.sub tendsto_const_nhds
    rw [zero_sub] at hfull
    refine hfull.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [hg_eq n hn]
  -- Eventually `g n ≤ RHS_n`.
  have hev_le : ∀ᶠ n : ℕ in atTop,
      g n ≤ (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}) := by
    -- Window largeness `≥ 1/4` at the boundary, lifted to the half-line.
    have hwin := tiltedWindow_eventually_large_of_boundary hY h_bdd lam hε hVar
    rw [← hmdef] at hwin
    filter_upwards [hwin, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    -- Half-line lower bound `(1/4)·exp(...) ≤ P{m·n ≤ ∑Y}`.
    have hhalf := tilted_window_lower_to_halfline hY h_bdd lam hlam m ε hn
    -- Both sides positive; `log` monotone; multiply by `(1/n) > 0`.
    have hexp_pos : (0 : ℝ) <
        (1 / 4 : ℝ) * Real.exp (-(n : ℝ) * (lam * m - cgf Y μ₀ lam + lam * ε)) := by
      positivity
    have hP_pos : (0 : ℝ) < (Measure.infinitePi (fun _ : ℕ => μ₀)).real
        {ω : ℕ → Ω₀ | m * n ≤ ∑ i ∈ Finset.range n, Y (ω i)} :=
      lt_of_lt_of_le hexp_pos hhalf
    simp only [hgdef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.log_le_log hexp_pos hhalf
  -- `liminf` monotone.
  have hbnd : (Filter.atTop : Filter ℕ).IsBoundedUnder (· ≥ ·) g :=
    hg_tendsto.isBoundedUnder_ge
  calc -(lam * m - cgf Y μ₀ lam + lam * ε)
      = liminf g atTop := hg_tendsto.liminf_eq.symm
    _ ≤ _ := liminf_le_liminf hev_le hbnd h_coboundedBelow

/-- **Cramér lower bound, boundary closure** (Phase 6). At the interior optimal tilt
`a = m = ∫ Y ∂tilted` (= `deriv (cgf Y μ₀) lam`, the boundary of the residual window), the
asymptotic upper-tail rate is bounded below by the per-`lam` Chernoff exponent
`-(λm - Λ)`. The residual largeness hypothesis is **removed** — the boundary window mass is
supplied internally by the CLT (`tiltedWindow_eventually_large_of_boundary`). Only the
regularity preconditions remain: boundedness, non-degeneracy `0 < Var`, and the cobounded
hypothesis on the rate sequence (a precondition shared with `cramer_lower`). The `ε → 0⁺`
limit collapses the per-`ε` bounds `boundary_liminf_lower_of_eps` to the sharp exponent. -/
theorem cramer_lower_boundary
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) (hlam : 0 ≤ lam)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))])
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ |
              (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n
                ≤ ∑ i ∈ Finset.range n, Y (ω i)}))) :
    -(lam * (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) - cgf Y μ₀ lam)
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ |
                (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n
                  ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop := by
  set m : ℝ := ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) with hmdef
  -- `ε → 0⁺`: collapse the per-`ε` bounds.
  refine le_of_forall_sub_le (fun δ hδ => ?_)
  rcases eq_or_lt_of_le hlam with hlam0 | hlampos
  · -- `lam = 0`: the per-`ε` bound is exactly `-(0·m - Λ) = Λ ≤ liminf` (any `ε`).
    have h := boundary_liminf_lower_of_eps hY h_bdd lam hlam hVar (ε := 1) one_pos
      h_coboundedBelow
    rw [← hmdef] at h
    have heq : -(lam * m - cgf Y μ₀ lam + lam * 1)
        = -(lam * m - cgf Y μ₀ lam) := by rw [← hlam0]; ring
    rw [heq] at h
    linarith [h]
  · -- `lam > 0`: pick `ε = δ / lam`, so `lam * ε = δ`.
    have hεpos : (0 : ℝ) < δ / lam := div_pos hδ hlampos
    have h := boundary_liminf_lower_of_eps hY h_bdd lam hlam hVar (ε := δ / lam) hεpos
      h_coboundedBelow
    rw [← hmdef] at h
    have hlamε : lam * (δ / lam) = δ := by field_simp
    rw [hlamε] at h
    have heq : -(lam * m - cgf Y μ₀ lam + δ) = -(lam * m - cgf Y μ₀ lam) - δ := by ring
    rw [heq] at h
    exact h

/-- **Cramér lower bound, boundary closure — consumer form** (Phase 6 end-to-end). The
infinitePi-side restatement of `cramer_lower_boundary` matching the conclusion shape of
`Cramer.Discharge.cramer_lower_phaseC_partial_discharge`: the cgf is written on the
coordinate-eval family `Y ∘ eval 0` under the un-tilted product, and the threshold is the
optimal tilt `a = deriv (cgf (Y∘eval 0) (infinitePi μ₀)) lam`. The optimal-tilt hypothesis
`h_deriv` (the same regularity precondition carried by the consumer root after the
2026-06-11 def-fix) pins `a = m = ∫ Y ∂tilted` via `tiltedMean_eq_deriv_cgf` and the
cgf-eval bridge, so the residual largeness hypothesis is **removed**: the boundary window
mass is supplied internally by the CLT. This is the unconditional internal-point form
targeted by the parent W-3 retreat line. -/
theorem cramer_lower_boundary_unconditional
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (a lam : ℝ) (hlam : 0 ≤ lam)
    (h_deriv : deriv (cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
        (Measure.infinitePi (fun _ : ℕ => μ₀))) lam = a)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))])
    (h_coboundedBelow : Filter.IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}))) :
    -(lam * a
        - cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
            (Measure.infinitePi (fun _ : ℕ => μ₀)) lam)
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            ((Measure.infinitePi (fun _ : ℕ => μ₀)).real
              {ω : ℕ → Ω₀ | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)})) atTop := by
  -- The cgf on the coordinate-eval family equals the base cgf (as functions of `t`).
  have hcgf_fun : cgf (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀)) = cgf Y μ₀ := by
    funext t
    exact Cramer.Discharge.cgf_eval_eq_cgf_base hY 0 t
  -- Hence `a = deriv (cgf Y μ₀) lam = ∫ Y ∂tilted = m`.
  have ham : a = ∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω)) := by
    rw [← h_deriv, hcgf_fun]
    exact (Cramer.Discharge.tiltedMean_eq_deriv_cgf hY h_bdd lam).symm
  -- Rewrite the goal at `a = m`, then identify the cgf, and apply the boundary lower bound.
  subst ham
  rw [hcgf_fun]
  exact cramer_lower_boundary hY h_bdd lam hlam hVar h_coboundedBelow

end InformationTheory.Shannon.CramerCltBoundary
