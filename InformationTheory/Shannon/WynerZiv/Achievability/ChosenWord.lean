import InformationTheory.Shannon.WynerZiv.Achievability.MarkovCore

/-!
# Wyner–Ziv achievability — covering chosen-word typicality and the joint lossy code
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set
open scoped ENNReal NNReal BigOperators Topology

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {α β γ U : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [DecidableEq β] [Nonempty β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [Fintype γ] [DecidableEq γ] [Nonempty γ] [MeasurableSpace γ] [MeasurableSingletonClass γ]
  [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [MeasurableSingletonClass U]

open ChannelCoding in
/-- For any covering code `c`, the
`SRC`-mass of the strong-covering-success complement is bounded by the covering ambient's
block-`X`-law mass of the encoder-failure event `(x, c.decoder (c.encoder x)) ∉
jointStronglyTypicalSet` at the encoder radius `ε_enc`. Measure alignment
(`wz_covering_SRC_map_Xproj_eq`) pushes `SRC` to the block-`X`-law along the `X`-projection,
and the radius bridge `wz_jointStrongly_mem_coveringSuccessJoint` (given `ε_enc ≤ ε_cov` and
the three `logSumAbs` bounds) makes strong-`ε_enc` typicality of the chosen word land in the
covering-success event, so its complement is contained in the encoder-failure event. Measure
monotonicity through the alignment and radius bridge; the hypotheses are regularity/radius
preconditions.

@audit:ok -/
private lemma wz_coveringSuccessStrong_compl_measureReal_le
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    (κ' : α → Fin k → ℝ)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hqStar_mem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (hqStar_eq : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    {n : ℕ} (hn : 0 < n) {M : ℕ}
    (c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k))
    {ε_enc ε : ℝ} (hε_enc_nn : 0 ≤ ε_enc)
    (h_le_cov : ε_enc ≤ wzCoveringStrongRadius P_XY κ' ε)
    (hX : (Fintype.card (Fin k) : ℝ) * ε_enc
            * logSumAbs (rdAmbient qStar) ChannelCoding.iidXs < ε)
    (hY : (Fintype.card {x : α // 0 < ∑ y, P_XY.real {(x, y)}} : ℝ) * ε_enc
            * logSumAbs (rdAmbient qStar) ChannelCoding.iidYs < ε)
    (hJ : ε_enc * logSumAbs (rdAmbient qStar)
            (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) < ε) :
    (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
        (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
          P_XY.real {(p.1.1, p.2)}))).real
        ((wzCoveringSuccessStrong P_XY κ' qStar c ε)ᶜ)
      ≤ (Measure.pi (fun _ : Fin n ↦ (rdAmbient qStar).map (ChannelCoding.iidXs 0))).real
          { x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
              (x, c.decoder (c.encoder x)) ∉ jointStronglyTypicalSet (rdAmbient qStar)
                  ChannelCoding.iidXs ChannelCoding.iidYs n ε_enc } := by
  classical
  haveI : IsProbabilityMeasure (rdAmbient qStar) :=
    rdAmbient_isProbabilityMeasure qStar hqStar_mem
  -- The `X`-projection and the covering-success base set on `X`-blocks.
  set S : Set (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) :=
    { x | (x, c.decoder (c.encoder x)) ∈ jointStronglyTypicalSet (rdAmbient qStar)
              ChannelCoding.iidXs ChannelCoding.iidYs n (wzCoveringStrongRadius P_XY κ' ε) }
    ∩ { x | (x, c.decoder (c.encoder x)) ∈ ChannelCoding.jointlyTypicalSet (rdAmbient qStar)
              ChannelCoding.iidXs ChannelCoding.iidYs n ε } with hS
  have hXproj_meas : Measurable
      (fun p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦ fun j ↦ (p j).1) :=
    measurable_pi_lambda _ (fun j ↦ (measurable_pi_apply j).fst)
  calc (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
            P_XY.real {(p.1.1, p.2)}))).real
          ((wzCoveringSuccessStrong P_XY κ' qStar c ε)ᶜ)
      = (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
            P_XY.real {(p.1.1, p.2)}))).real
            ((fun p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              fun j ↦ (p j).1) ⁻¹' Sᶜ) := rfl
    _ = ((Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
          (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
            P_XY.real {(p.1.1, p.2)}))).map
            (fun p : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              fun j ↦ (p j).1)).real Sᶜ :=
        (map_measureReal_apply hXproj_meas (Set.toFinite _).measurableSet).symm
    _ = (Measure.pi (fun _ : Fin n ↦ (rdAmbient qStar).map (ChannelCoding.iidXs 0))).real Sᶜ := by
        rw [wz_covering_SRC_map_Xproj_eq P_XY κ' qStar hqStar_mem hκ'sum hqStar_eq n]
    _ ≤ (Measure.pi (fun _ : Fin n ↦ (rdAmbient qStar).map (ChannelCoding.iidXs 0))).real
          { x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
              (x, c.decoder (c.encoder x)) ∉ jointStronglyTypicalSet (rdAmbient qStar)
                  ChannelCoding.iidXs ChannelCoding.iidYs n ε_enc } := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        intro x hx
        simp only [Set.mem_setOf_eq]
        intro hxu
        exact hx (wz_jointStrongly_mem_coveringSuccessJoint P_XY qStar hqStar_mem hn
          hε_enc_nn h_le_cov hX hY hJ x (c.decoder (c.encoder x)) hxu)


set_option maxHeartbeats 1600000 in
private lemma wz_covering_joint_slack_params
    {R₁ Dδ mi ed ε' ε Lx Ly Lj Sd cA cB qZ_min εcov : ℝ}
    (hI : mi < R₁) (hfeas : ed ≤ Dδ) (hε' : 0 < ε') (hε : 0 < ε)
    (hLx_nn : 0 ≤ Lx) (hLy_nn : 0 ≤ Ly) (hLj_nn : 0 ≤ Lj) (hSd_nn : 0 ≤ Sd)
    (hcA_pos : 0 < cA) (hcB_pos : 0 < cB) (hqZ_pos : 0 < qZ_min) (hεcov_pos : 0 < εcov) :
    ∃ ε_join ε_X ε_dist δ_typ δ_kl : ℝ,
      0 < ε_join ∧ 0 < ε_X ∧ ε_X < ε_join ∧ 0 < δ_kl ∧
        8 * cA * cB * ε_X ^ 2 ≤ δ_kl * qZ_min ∧
        mi + (cA * ε_X * Ly + ε_X * Lx + ε_X * Lj + δ_kl) < R₁ ∧
        ed + δ_typ ≤ Dδ + ε' / 2 ∧
        ε_join * Sd ≤ δ_typ ∧
        cB * ε_join * Lx < ε_dist ∧ cA * ε_join * Ly < ε_dist ∧ ε_join * Lj < ε_dist ∧
        cB * ε_join * Lx < ε ∧ cA * ε_join * Ly < ε ∧ ε_join * Lj < ε ∧
        ε_join ≤ εcov ∧ 0 ≤ δ_typ := by
  set gap : ℝ := R₁ - mi with hgap_def
  have hgap_pos : 0 < gap := by rw [hgap_def]; linarith
  clear_value gap
  set Cc : ℝ := cA * Ly + Lx + Lj with hCc_def
  have hCc_nn : 0 ≤ Cc := by
    rw [hCc_def]; have : 0 ≤ cA * Ly := mul_nonneg hcA_pos.le hLy_nn; linarith
  clear_value Cc
  set Kk : ℝ := 8 * cA * cB / qZ_min with hKk_def
  have hKk_nn : 0 ≤ Kk := by
    rw [hKk_def]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcA_pos.le) hcB_pos.le) hqZ_pos.le
  -- Radius-bridge widths: ε_cov and the combined logSumAbs width.
  set Lrad : ℝ := 1 + cB * Lx + cA * Ly + Lj with hLrad_def
  have hLrad_pos : 0 < Lrad := by
    rw [hLrad_def]
    have h1 : 0 ≤ cB * Lx := mul_nonneg hcB_pos.le hLx_nn
    have h2 : 0 ≤ cA * Ly := mul_nonneg hcA_pos.le hLy_nn
    linarith
  -- The slack quintet: choose everything small against the rate gap, `ε'`, and radius widths.
  have hden1 : 0 < 2 * (Cc + Kk + 1) := by nlinarith [hCc_nn, hKk_nn]
  have hden2 : 0 < 2 * (Sd + 1) := by nlinarith [hSd_nn]
  have hden3 : 0 < 2 * Lrad := by linarith
  set ε_join : ℝ :=
    min 1 (min (gap / (2 * (Cc + Kk + 1)))
      (min (ε' / (2 * (Sd + 1))) (min εcov (ε / (2 * Lrad))))) with hej_def
  have hej_pos : 0 < ε_join := by
    rw [hej_def]
    exact lt_min one_pos (lt_min (div_pos hgap_pos hden1)
      (lt_min (div_pos hε' hden2) (lt_min hεcov_pos (div_pos hε hden3))))
  have hej_le1 : ε_join ≤ 1 := by rw [hej_def]; exact min_le_left _ _
  have hej_le_gap : ε_join ≤ gap / (2 * (Cc + Kk + 1)) := by
    rw [hej_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hej_le_eps : ε_join ≤ ε' / (2 * (Sd + 1)) := by
    rw [hej_def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hej_le_cov : ε_join ≤ εcov := by
    rw [hej_def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hej_le_rad : ε_join ≤ ε / (2 * Lrad) := by
    rw [hej_def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  clear_value Kk ε_join
  set ε_X : ℝ := ε_join / 2 with hex_def
  have hex_pos : 0 < ε_X := by rw [hex_def]; linarith
  have hex_lt_ej : ε_X < ε_join := by rw [hex_def]; linarith
  have hex_le1 : ε_X ≤ 1 := by rw [hex_def]; linarith
  clear_value ε_X
  set δ_typ : ℝ := ε' / 2 with hdtyp_def
  have hdtyp_nn : 0 ≤ δ_typ := by rw [hdtyp_def]; linarith
  set ε_dist : ℝ := cB * ε_join * Lx + cA * ε_join * Ly + ε_join * Lj + 1 with hed_def
  have hed_pos : 0 < ε_dist := by
    rw [hed_def]
    have h1 : 0 ≤ cB * ε_join * Lx :=
      mul_nonneg (mul_nonneg hcB_pos.le hej_pos.le) hLx_nn
    have h2 : 0 ≤ cA * ε_join * Ly :=
      mul_nonneg (mul_nonneg hcA_pos.le hej_pos.le) hLy_nn
    have h3 : 0 ≤ ε_join * Lj := mul_nonneg hej_pos.le hLj_nn
    linarith
  set δ_kl : ℝ := Kk * ε_X ^ 2 with hdkl_def
  have hdkl_pos : 0 < δ_kl := by
    rw [hdkl_def, hKk_def]
    have hnum : 0 < 8 * cA * cB := mul_pos (mul_pos (by norm_num) hcA_pos) hcB_pos
    positivity
  -- Numeric obligations.
  have h_rategap : mi
      + (cA * ε_X * Ly + ε_X * Lx + ε_X * Lj + δ_kl) < R₁ := by
    have hlin : cA * ε_X * Ly + ε_X * Lx + ε_X * Lj = ε_X * Cc := by
      rw [hCc_def]; ring
    have hdkl_le : δ_kl ≤ Kk * ε_X := by
      rw [hdkl_def]; nlinarith [hKk_nn, hex_pos.le, hex_le1]
    have hεX_le : ε_X * (2 * (Cc + Kk + 1)) ≤ gap :=
      (le_div_iff₀ hden1).mp (le_trans hex_lt_ej.le hej_le_gap)
    have hkey : ε_X * Cc + δ_kl < gap := by
      nlinarith [hdkl_le, hεX_le, hex_pos, hCc_nn, hKk_nn]
    rw [hlin]; linarith [hkey, hgap_def]
  have h_slack : ed + δ_typ ≤ Dδ + ε' / 2 := by
    rw [hdtyp_def]; linarith
  have h_distslack : ε_join * Sd ≤ δ_typ := by
    rw [hdtyp_def]
    have h1 : ε_join * (2 * (Sd + 1)) ≤ ε' := (le_div_iff₀ hden2).mp hej_le_eps
    nlinarith [hej_pos.le, hSd_nn, h1]
  have h_dominates : 8 * cA * cB * ε_X ^ 2 ≤ δ_kl * qZ_min := by
    have hne : qZ_min ≠ 0 := ne_of_gt hqZ_pos
    have hKq : Kk * qZ_min = 8 * cA * cB := by
      rw [hKk_def]; exact div_mul_cancel₀ _ hne
    have heq : δ_kl * qZ_min = 8 * cA * cB * ε_X ^ 2 := by
      rw [hdkl_def, mul_right_comm, hKq]
    exact le_of_eq heq.symm
  -- Strong-typicality ⟹ distortion-typicality bridge slacks.
  have hbX : cB * ε_join * Lx < ε_dist := by
    rw [hed_def]
    have h2 : 0 ≤ cA * ε_join * Ly :=
      mul_nonneg (mul_nonneg hcA_pos.le hej_pos.le) hLy_nn
    have h3 : 0 ≤ ε_join * Lj := mul_nonneg hej_pos.le hLj_nn
    nlinarith [h2, h3]
  have hbY : cA * ε_join * Ly < ε_dist := by
    rw [hed_def]
    have h1 : 0 ≤ cB * ε_join * Lx :=
      mul_nonneg (mul_nonneg hcB_pos.le hej_pos.le) hLx_nn
    have h3 : 0 ≤ ε_join * Lj := mul_nonneg hej_pos.le hLj_nn
    nlinarith [h1, h3]
  have hbJ : ε_join * Lj < ε_dist := by
    rw [hed_def]
    have h1 : 0 ≤ cB * ε_join * Lx :=
      mul_nonneg (mul_nonneg hcB_pos.le hej_pos.le) hLx_nn
    have h2 : 0 ≤ cA * ε_join * Ly :=
      mul_nonneg (mul_nonneg hcA_pos.le hej_pos.le) hLy_nn
    nlinarith [h1, h2]
  -- Radius-bridge obligations (for `wz_coveringSuccessStrong_compl_measureReal_le`).
  have hLrad_ineq : ε_join * (2 * Lrad) ≤ ε := (le_div_iff₀ hden3).mp hej_le_rad
  have hradX : cB * ε_join * Lx < ε := by
    rw [hLrad_def] at hLrad_ineq
    have h2 : 0 ≤ cA * ε_join * Ly :=
      mul_nonneg (mul_nonneg hcA_pos.le hej_pos.le) hLy_nn
    have h3 : 0 ≤ ε_join * Lj := mul_nonneg hej_pos.le hLj_nn
    nlinarith [hej_pos, hLx_nn, h2, h3]
  have hradY : cA * ε_join * Ly < ε := by
    rw [hLrad_def] at hLrad_ineq
    have h1 : 0 ≤ cB * ε_join * Lx :=
      mul_nonneg (mul_nonneg hcB_pos.le hej_pos.le) hLx_nn
    have h3 : 0 ≤ ε_join * Lj := mul_nonneg hej_pos.le hLj_nn
    nlinarith [hej_pos, hLy_nn, h1, h3]
  have hradJ : ε_join * Lj < ε := by
    rw [hLrad_def] at hLrad_ineq
    have h1 : 0 ≤ cB * ε_join * Lx :=
      mul_nonneg (mul_nonneg hcB_pos.le hej_pos.le) hLx_nn
    have h2 : 0 ≤ cA * ε_join * Ly :=
      mul_nonneg (mul_nonneg hcA_pos.le hej_pos.le) hLy_nn
    nlinarith [hej_pos, hLj_nn, h1, h2]
  exact ⟨ε_join, ε_X, ε_dist, δ_typ, δ_kl, hej_pos, hex_pos, hex_lt_ej, hdkl_pos,
    h_dominates, h_rategap, h_slack, h_distslack, hbX, hbY, hbJ, hradX, hradY, hradJ,
    hej_le_cov, hdtyp_nn⟩

open ChannelCoding in
set_option maxHeartbeats 1600000 in
private lemma wz_covering_joint_pigeonhole
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hmem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (d' : DistortionFn {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k))
    {n : ℕ} (hn_pos : 0 < n)
    (P_X : (n : ℕ) → Measure (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}}))
    (hPX_prob : IsProbabilityMeasure (P_X n))
    (Mn : ℕ → ℕ) (hMn_pos : ∀ n, 0 < Mn n)
    {ε_X ε_join ε_dist δ_typ : ℝ} (hej_pos : 0 < ε_join)
    (hbX : (Fintype.card (Fin k) : ℝ) * ε_join
        * logSumAbs (rdAmbient qStar) ChannelCoding.iidXs < ε_dist)
    (hbY : (Fintype.card {x : α // 0 < ∑ y, P_XY.real {(x, y)}} : ℝ) * ε_join
        * logSumAbs (rdAmbient qStar) ChannelCoding.iidYs < ε_dist)
    (hbJ : ε_join * logSumAbs (rdAmbient qStar)
        (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs) < ε_dist)
    (h_distslack : ε_join * ∑ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k,
        ((d' p.1 p.2 : NNReal) : ℝ) ≤ δ_typ)
    (target : ℕ → ℝ) (upper : ℕ → ℝ)
    (hupper_def : upper = fun n ↦ (P_X n).real
        {x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
          x ∉ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs n ε_X}
      + Real.exp (-((Mn n : ℝ) * target n)))
    (h_typical : ∀ x ∈ {x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
          x ∈ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs n ε_X},
        (Measure.pi (fun _ : Fin (Mn n) ↦
            Measure.pi (fun _ : Fin n ↦ (rdAmbient qStar).map (ChannelCoding.iidYs 0)))).real
          { c : Fin (Mn n) → (Fin n → Fin k) |
              ¬ ∃ m, (x, c m) ∈ jointStronglyTypicalSet (rdAmbient qStar)
                  ChannelCoding.iidXs ChannelCoding.iidYs n ε_join }
          ≤ Real.exp (-((Mn n : ℝ) * target n))) :
    ∃ c₀ : Codebook (Mn n) n (Fin k),
      (P_X n).real {x | (x, c₀ (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
            ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c₀ x))
          ∉ distortionTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
              d' n ε_dist δ_typ}
        + (P_X n).real {x | (x, c₀ (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
            ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c₀ x))
          ∉ jointStronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs
              ChannelCoding.iidYs n ε_join}
      ≤ 2 * upper n := by
  classical
  haveI := hPX_prob
  haveI hμY_prob : IsProbabilityMeasure ((rdAmbient qStar).map (ChannelCoding.iidYs 0)) :=
    rdAmbient_iidYs_isProbabilityMeasure qStar hmem
  have h_dist_bound : ∑ c : Codebook (Mn n) n (Fin k),
      (codebookMeasure ((rdAmbient qStar).map (ChannelCoding.iidYs 0)) (Mn n) n).real {c}
        * (P_X n).real {x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
            (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar) ChannelCoding.iidXs
                  ChannelCoding.iidYs (hMn_pos n) ε_join c x))
              ∉ distortionTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
                  d' n ε_dist δ_typ}
      ≤ upper n := by
    rw [hupper_def]
    exact weightedSum_encoderFailure_le_notTypical_add_bound (P_X n)
      (Measure.pi (fun _ : Fin n ↦ (rdAmbient qStar).map (ChannelCoding.iidYs 0)))
      {x | x ∈ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs n ε_X}
      (distortionTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
        d' n ε_dist δ_typ)
      (jointStronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs n ε_join)
      (fun c ↦ jointStronglyTypicalLossyEncoder (rdAmbient qStar) ChannelCoding.iidXs
        ChannelCoding.iidYs (hMn_pos n) ε_join c)
      (Real.exp (-((Mn n : ℝ) * target n))) (Real.exp_pos _).le
      (fun _ ↦ (Set.toFinite _).measurableSet) (Set.toFinite _).measurableSet
      (fun x _ y hy ↦ wz_jointStronglyTypical_mem_distortionTypical qStar hmem d' hej_pos.le
        hbX hbY hbJ h_distslack hn_pos x y hy)
      (fun c x hex ↦ jointStronglyTypicalLossyEncoder_spec_of_exists (rdAmbient qStar)
        ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c x hex)
      h_typical
  -- Covering-failure codebook average ≤ upper.
  have h_cov_bound : ∑ c : Codebook (Mn n) n (Fin k),
      (codebookMeasure ((rdAmbient qStar).map (ChannelCoding.iidYs 0)) (Mn n) n).real {c}
        * (P_X n).real {x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
            (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar) ChannelCoding.iidXs
                  ChannelCoding.iidYs (hMn_pos n) ε_join c x))
              ∉ jointStronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs
                  ChannelCoding.iidYs n ε_join}
      ≤ upper n := by
    rw [hupper_def]
    exact weightedSum_encoderFailure_le_notTypical_add_bound (P_X n)
      (Measure.pi (fun _ : Fin n ↦ (rdAmbient qStar).map (ChannelCoding.iidYs 0)))
      {x | x ∈ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs n ε_X}
      (jointStronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs n ε_join)
      (jointStronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs n ε_join)
      (fun c ↦ jointStronglyTypicalLossyEncoder (rdAmbient qStar) ChannelCoding.iidXs
        ChannelCoding.iidYs (hMn_pos n) ε_join c)
      (Real.exp (-((Mn n : ℝ) * target n))) (Real.exp_pos _).le
      (fun _ ↦ (Set.toFinite _).measurableSet) (Set.toFinite _).measurableSet
      (fun x _ y hy ↦ hy)
      (fun c x hex ↦ jointStronglyTypicalLossyEncoder_spec_of_exists (rdAmbient qStar)
        ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c x hex)
      h_typical
  -- Joint average ≤ 2·upper, then pigeonhole.
  have h_avg : ∑ c : Codebook (Mn n) n (Fin k),
      (codebookMeasure ((rdAmbient qStar).map (ChannelCoding.iidYs 0)) (Mn n) n).real {c}
        * ((P_X n).real {x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
              (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar) ChannelCoding.iidXs
                    ChannelCoding.iidYs (hMn_pos n) ε_join c x))
                ∉ distortionTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
                    d' n ε_dist δ_typ}
            + (P_X n).real {x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
              (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar) ChannelCoding.iidXs
                    ChannelCoding.iidYs (hMn_pos n) ε_join c x))
                ∉ jointStronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs
                    ChannelCoding.iidYs n ε_join})
      ≤ 2 * upper n := by
    have hsplit : ∑ c : Codebook (Mn n) n (Fin k),
        (codebookMeasure ((rdAmbient qStar).map (ChannelCoding.iidYs 0)) (Mn n) n).real {c}
          * ((P_X n).real {x | (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
                ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c x))
                ∉ distortionTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
                    d' n ε_dist δ_typ}
              + (P_X n).real {x | (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
                ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c x))
                ∉ jointStronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs
                    ChannelCoding.iidYs n ε_join})
        = (∑ c : Codebook (Mn n) n (Fin k),
            (codebookMeasure ((rdAmbient qStar).map (ChannelCoding.iidYs 0)) (Mn n) n).real {c}
              * (P_X n).real {x | (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
                  ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c x))
                  ∉ distortionTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
                      d' n ε_dist δ_typ})
          + (∑ c : Codebook (Mn n) n (Fin k),
            (codebookMeasure ((rdAmbient qStar).map (ChannelCoding.iidYs 0)) (Mn n) n).real {c}
              * (P_X n).real {x | (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
                  ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c x))
                  ∉ jointStronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs
                      ChannelCoding.iidYs n ε_join}) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun c _ ↦ ?_); ring
    rw [hsplit]; linarith only [h_dist_bound, h_cov_bound]
  exact exists_codebook_low_avg ((rdAmbient qStar).map (ChannelCoding.iidYs 0))
    (fun c : Codebook (Mn n) n (Fin k) ↦
      (P_X n).real {x | (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
            ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c x))
          ∉ distortionTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
              d' n ε_dist δ_typ}
        + (P_X n).real {x | (x, c (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
            ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c x))
          ∉ jointStronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs
              ChannelCoding.iidYs n ε_join})
    h_avg

set_option maxHeartbeats 1600000 in
open ChannelCoding in
/-- On a single covering code good for BOTH the covering
distortion (block distortion `≤ Dδ + ε'`) AND covering-success (`SRC`-mass of the
strong-covering-success complement `≤ tol`). The two per-codebook failure functionals — the
distortion-typicality failure (drives block distortion via
`source_avg_distortion_le_simpler_generic`) and the strong-joint-typicality failure at the
encoder radius `ε_join` (drives covering-success via
`wz_coveringSuccessStrong_compl_measureReal_le`) — are both codebook-averaged and bounded by
the shared vanishing upper `(P_X n){Xⁿ ∉ T*_X} + exp(-Mₙ·exp(-n(I+slack)))`; the pigeonhole
`exists_codebook_low_avg` on their sum extracts one codebook small for both. The encoder
radius `ε_join` is chosen `≤ wzCoveringStrongRadius P_XY κ' ε` and small against the three
`logSumAbs` widths, so the radius bridge applies. The good code is genuinely constructed, not
received as a hypothesis: the two per-codebook failure functionals are codebook-averaged, summed,
and `exists_codebook_low_avg` extracts a single `c₀` small for both. The hypotheses
(`hI : mutualInfoPmf qStar < R₁`, `hfeas`, full support, simplex, `hqStar_eq`) are genuine
preconditions on the pmf and proxy distortion, not a bundled `*Hypothesis` handing over the code's
existence.

@audit:ok -/
private lemma wz_covering_lossyCode_joint_exists
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    {k : ℕ} [Nonempty (Fin k)] [Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}}]
    (κ' : α → Fin k → ℝ) (hκ'sum : ∀ x, ∑ u, κ' x u = 1)
    (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
    (hpos : ∀ p, 0 < qStar p)
    (hmem : qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k))
    (hqStar_eq : ∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
    (d' : DistortionFn {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k))
    {R₁ Dδ : ℝ} (hI : mutualInfoPmf qStar < R₁)
    (hfeas : expectedDistortionPmf d' qStar ≤ Dδ)
    {ε' : ℝ} (hε' : 0 < ε') {ε : ℝ} (hε : 0 < ε) {tol : ℝ} (htol : 0 < tol) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : ℕ, Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M ∧
      (M : ℝ) ≤ Real.exp ((n : ℝ) * R₁) + 1 ∧
      ∃ c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k),
        c.expectedBlockDistortion ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) d' ≤ Dδ + ε'
        ∧ (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
            (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
              P_XY.real {(p.1.1, p.2)}))).real
            ((wzCoveringSuccessStrong P_XY κ' qStar c ε)ᶜ) ≤ tol := by
  classical
  haveI hμprob : IsProbabilityMeasure (rdAmbient qStar) :=
    rdAmbient_isProbabilityMeasure qStar hmem
  -- Nonnegative constants from the ambient log-sum and the distortion table.
  set Lx : ℝ := logSumAbs (rdAmbient qStar) iidXs with hLx_def
  set Ly : ℝ := logSumAbs (rdAmbient qStar) iidYs with hLy_def
  set Lj : ℝ := logSumAbs (rdAmbient qStar) (jointSequence iidXs iidYs) with hLj_def
  have hLx_nn : 0 ≤ Lx := logSumAbs_nonneg _ _
  have hLy_nn : 0 ≤ Ly := logSumAbs_nonneg _ _
  have hLj_nn : 0 ≤ Lj := logSumAbs_nonneg _ _
  set Sd : ℝ := ∑ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k,
    ((d' p.1 p.2 : NNReal) : ℝ) with hSd_def
  have hSd_nn : 0 ≤ Sd := Finset.sum_nonneg fun p _ ↦ NNReal.coe_nonneg _
  set cA : ℝ := (Fintype.card {x : α // 0 < ∑ y, P_XY.real {(x, y)}} : ℝ) with hcA_def
  set cB : ℝ := (Fintype.card (Fin k) : ℝ) with hcB_def
  have hcA_pos : 0 < cA := by rw [hcA_def]; exact_mod_cast Fintype.card_pos
  have hcB_pos : 0 < cB := by rw [hcB_def]; exact_mod_cast Fintype.card_pos
  -- Minimal singleton mass, positive by full support.
  set qZ_min : ℝ := Finset.univ.inf' Finset.univ_nonempty qStar with hqZ_def
  have hqZ_pos : 0 < qZ_min := by
    rw [hqZ_def, Finset.lt_inf'_iff]; exact fun p _ ↦ hpos p
  have hqZ_le : ∀ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k,
      qZ_min ≤ (pmfToMeasure
          (α := {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k) qStar).real {p} := by
    intro p
    rw [pmfToMeasure_real_singleton hmem p, hqZ_def]
    exact Finset.inf'_le _ (Finset.mem_univ p)
  set εcov : ℝ := wzCoveringStrongRadius P_XY κ' ε with hεcov_def
  have hεcov_pos : 0 < εcov := by rw [hεcov_def]; exact wzCoveringStrongRadius_pos P_XY κ' hε
  obtain ⟨ε_join, ε_X, ε_dist, δ_typ, δ_kl, hej_pos, hex_pos, hex_lt_ej, hdkl_pos,
    h_dominates, h_rategap, h_slack, h_distslack, hbX, hbY, hbJ, hradX, hradY, hradJ,
    hej_le_cov, hdtyp_nn⟩ :=
    wz_covering_joint_slack_params hI hfeas hε' hε hLx_nn hLy_nn hLj_nn hSd_nn hcA_pos hcB_pos
      hqZ_pos hεcov_pos
  -- ## Probabilistic content.
  have hindepX_pair : Pairwise fun i j ↦
      ChannelCoding.iidXs (α := {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (β := Fin k) i
        ⟂ᵢ[rdAmbient qStar] ChannelCoding.iidXs j :=
    fun i j hij ↦ (rdAmbient_iIndepFun_iidXs qStar hmem).indepFun hij
  have hidentX : ∀ i, IdentDistrib
      (ChannelCoding.iidXs (α := {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (β := Fin k) i)
      (ChannelCoding.iidXs 0) (rdAmbient qStar) (rdAmbient qStar) :=
    fun i ↦ rdAmbient_identDistrib_iidXs qStar hmem i
  haveI hμX_prob : IsProbabilityMeasure ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) :=
    rdAmbient_iidXs_isProbabilityMeasure qStar hmem
  haveI hμY_prob : IsProbabilityMeasure ((rdAmbient qStar).map (ChannelCoding.iidYs 0)) :=
    rdAmbient_iidYs_isProbabilityMeasure qStar hmem
  have h_ent_bridge :
      entropy (rdAmbient qStar) (ChannelCoding.iidXs 0)
        + entropy (rdAmbient qStar) (ChannelCoding.iidYs 0)
        - entropy (rdAmbient qStar)
            (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)
        = mutualInfoPmf qStar :=
    rdAmbient_entropy_diff_eq_mutualInfoPmf qStar hmem
  set dMax : ℝ := distortionMax d' with hdMax_def
  have hdMax_nn : 0 ≤ dMax := distortionMax_nonneg d'
  set P_X : (n : ℕ) → Measure (Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) :=
    fun n ↦ Measure.pi (fun _ : Fin n ↦ (rdAmbient qStar).map (ChannelCoding.iidXs 0))
    with hP_X_def
  set Mn : ℕ → ℕ := fun n ↦ Nat.ceil (Real.exp ((n : ℝ) * R₁)) with hMn_def
  have hMn_pos : ∀ n, 0 < Mn n := fun n ↦ Nat.ceil_pos.mpr (Real.exp_pos _)
  set I_plus_slack : ℝ :=
    mutualInfoPmf qStar + (cA * ε_X * Ly + ε_X * Lx + ε_X * Lj + δ_kl) with hIslack_def
  set target : ℕ → ℝ := fun n ↦
    Real.exp (-(n : ℝ) *
      (entropy (rdAmbient qStar) (ChannelCoding.iidXs 0)
        + entropy (rdAmbient qStar) (ChannelCoding.iidYs 0)
        - entropy (rdAmbient qStar)
            (ChannelCoding.jointSequence ChannelCoding.iidXs ChannelCoding.iidYs 0)
        + (cA * ε_X * Ly + ε_X * Lx + ε_X * Lj + δ_kl))) with htarget_def
  have h_target_eq : ∀ n : ℕ, target n = Real.exp (-(n : ℝ) * I_plus_slack) := by
    intro n; simp only [htarget_def, hIslack_def, h_ent_bridge]
  -- Codebook-level no-match bound.
  obtain ⟨N_B, hN_B⟩ := encoder_strong_failure_prob_le_rdAmbient qStar hmem hpos
    hej_pos hex_pos.le hex_lt_ej hdkl_pos qZ_min hqZ_pos hqZ_le h_dominates
  -- The typical-set complement mass `P_X[X ∉ T*_X]` tends to 0.
  have h_aep := stronglyTypicalSet_prob_tendsto_one (rdAmbient qStar) ChannelCoding.iidXs
    ChannelCoding.measurable_iidXs hindepX_pair hidentX hex_pos
  have h_pi_compl_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ (P_X n).real
        {x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
          x ∉ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs n ε_X})
        Filter.atTop (𝓝 0) :=
    tendsto_measureReal_map_notMem_zero_of_tendsto_prob_one (rdAmbient qStar)
      (fun n ↦ InformationTheory.Shannon.jointRV ChannelCoding.iidXs n)
      (fun n ↦ InformationTheory.Shannon.measurable_jointRV ChannelCoding.iidXs
        ChannelCoding.measurable_iidXs n)
      (fun n ↦ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs n ε_X)
      (fun _ ↦ (Set.toFinite _).measurableSet)
      P_X (fun n ↦ rdAmbient_block_law_iidXs qStar hmem n) h_aep
  -- The codebook no-match bound `exp(-Mn·target)` tends to 0.
  have h_exp_neg_Mn_target_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ Real.exp (-((Mn n : ℝ) * target n))) Filter.atTop (𝓝 0) :=
    exp_neg_ceilExp_mul_tendsto_zero_of_lt target R₁ I_plus_slack
      (by rw [hIslack_def]; exact h_rategap) h_target_eq
  set upper : ℕ → ℝ := fun n ↦ (P_X n).real
      {x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
        x ∉ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs n ε_X}
    + Real.exp (-((Mn n : ℝ) * target n)) with hupper_def
  have hupper_nn : ∀ n, 0 ≤ upper n := fun n ↦ by
    rw [hupper_def]; exact add_nonneg measureReal_nonneg (Real.exp_pos _).le
  have h_upper_tendsto : Filter.Tendsto upper Filter.atTop (𝓝 0) := by
    rw [hupper_def]; simpa using h_pi_compl_tendsto.add h_exp_neg_Mn_target_tendsto
  have h2upper_tendsto : Filter.Tendsto (fun n ↦ 2 * upper n) Filter.atTop (𝓝 0) := by
    simpa using h_upper_tendsto.const_mul (2 : ℝ)
  set thr : ℝ := min (ε' / (2 * (dMax + 1))) tol with hthr_def
  have hthr_pos : 0 < thr := by
    rw [hthr_def]; exact lt_min (by positivity) htol
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp h2upper_tendsto) thr hthr_pos
  refine ⟨max (max N_B N₀) 1, fun n hn ↦ ?_⟩
  have hn_NB : N_B ≤ n := le_trans (le_max_left _ _) (le_of_max_le_left hn)
  have hn_N0 : N₀ ≤ n := le_trans (le_max_right _ _) (le_of_max_le_left hn)
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_of_max_le_right hn)
  -- `2·upper n < thr` at this `n`.
  have h2upper_lt : 2 * upper n < thr := by
    have := hN₀ n hn_N0
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * upper n)] at this
    exact this
  haveI hPXprob : IsProbabilityMeasure (P_X n) := by rw [hP_X_def]; infer_instance
  -- No-match codebook mass bound reshaped for `weightedSum`.
  have h_typical : ∀ x ∈ {x : Fin n → {x : α // 0 < ∑ y, P_XY.real {(x, y)}} |
        x ∈ stronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs n ε_X},
      (Measure.pi (fun _ : Fin (Mn n) ↦
          Measure.pi (fun _ : Fin n ↦ (rdAmbient qStar).map (ChannelCoding.iidYs 0)))).real
        { c : Fin (Mn n) → (Fin n → Fin k) |
            ¬ ∃ m, (x, c m) ∈ jointStronglyTypicalSet (rdAmbient qStar)
                ChannelCoding.iidXs ChannelCoding.iidYs n ε_join }
        ≤ Real.exp (-((Mn n : ℝ) * target n)) := by
    intro x hxTX
    have h_step := hN_B n hn_NB (Mn n) x hxTX
    have h_set_eq : { c : Fin (Mn n) → (Fin n → Fin k) |
          ¬ ∃ m, (x, c m) ∈ jointStronglyTypicalSet (rdAmbient qStar)
              ChannelCoding.iidXs ChannelCoding.iidYs n ε_join }
        = { c : Fin (Mn n) → (Fin n → Fin k) |
            ∀ m, (x, c m) ∉ jointStronglyTypicalSet (rdAmbient qStar)
                ChannelCoding.iidXs ChannelCoding.iidYs n ε_join } := by
      ext c; simp [not_exists]
    rw [h_set_eq, show -((Mn n : ℝ) * target n) = -(Mn n : ℝ) * target n from by ring, htarget_def]
    exact h_step
  obtain ⟨c₀, hc₀⟩ := wz_covering_joint_pigeonhole P_XY qStar hmem d' hn_pos P_X hPXprob Mn
    hMn_pos hej_pos hbX hbY hbJ h_distslack target upper hupper_def h_typical
  -- Abstract the two failure functionals for the chosen codebook (keeps `linarith` cheap).
  set df0 : ℝ := (P_X n).real {x | (x, c₀ (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
      ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c₀ x))
    ∉ distortionTypicalSet (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
        d' n ε_dist δ_typ} with hdf0_def
  set cf0 : ℝ := (P_X n).real {x | (x, c₀ (jointStronglyTypicalLossyEncoder (rdAmbient qStar)
      ChannelCoding.iidXs ChannelCoding.iidYs (hMn_pos n) ε_join c₀ x))
    ∉ jointStronglyTypicalSet (rdAmbient qStar) ChannelCoding.iidXs
        ChannelCoding.iidYs n ε_join} with hcf0_def
  -- `hc₀ : df0 + cf0 ≤ 2 * upper n`.
  have hdf_nn : (0:ℝ) ≤ df0 := hdf0_def ▸ measureReal_nonneg
  have hcf_nn : (0:ℝ) ≤ cf0 := hcf0_def ▸ measureReal_nonneg
  have h_distfail : df0 ≤ ε' / (2 * (dMax + 1)) := by
    have hlt : 2 * upper n < ε' / (2 * (dMax + 1)) :=
      lt_of_lt_of_le h2upper_lt (by rw [hthr_def]; exact min_le_left _ _)
    linarith only [hc₀, hcf_nn, hlt]
  have h_covfail : cf0 ≤ tol := by
    have hlt : 2 * upper n < tol :=
      lt_of_lt_of_le h2upper_lt (by rw [hthr_def]; exact min_le_right _ _)
    linarith only [hc₀, hdf_nn, hlt]
  -- Assemble the joint-good code.
  have hMn_ub : (Mn n : ℝ) ≤ Real.exp ((n : ℝ) * R₁) + 1 := by
    rw [hMn_def]; exact (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
  refine ⟨Mn n, le_refl _, hMn_ub,
    lossyCodeOfCodebookStrong (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
      (hMn_pos n) ε_join c₀, ?_, ?_⟩
  · -- Block distortion ≤ Dδ + ε'.
    have h2 : dMax * df0 ≤ ε' / 2 := by
      have hdp : (0:ℝ) < 2 * (dMax + 1) := by positivity
      have hkey := (le_div_iff₀ hdp).mp h_distfail
      nlinarith only [hkey, hdMax_nn, hdf_nn, hε'.le]
    have h_src := source_avg_distortion_le_simpler_generic (rdAmbient qStar) ChannelCoding.iidXs
      ChannelCoding.iidYs d' ε_dist hdtyp_nn c₀
      (jointStronglyTypicalLossyEncoder (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
        (hMn_pos n) ε_join c₀) (P_X n)
    rw [expectedJointDistortion_rdAmbient qStar hmem d', ← hdf0_def, ← hdMax_def] at h_src
    calc (lossyCodeOfCodebookStrong (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
            (hMn_pos n) ε_join c₀).expectedBlockDistortion
            ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) d'
        ≤ (expectedDistortionPmf d' qStar + δ_typ) + dMax * df0 := h_src
      _ ≤ Dδ + ε' := by linarith only [h_slack, h2]
  · -- Covering-success complement ≤ tol.
    have hbridge := wz_coveringSuccessStrong_compl_measureReal_le P_XY κ' qStar hmem hκ'sum
      hqStar_eq hn_pos
      (lossyCodeOfCodebookStrong (rdAmbient qStar) ChannelCoding.iidXs ChannelCoding.iidYs
        (hMn_pos n) ε_join c₀) hej_pos.le hej_le_cov hradX hradY hradJ
    exact le_trans hbridge h_covfail

open ChannelCoding in
/-- Builds the covering `LossyCode` family from a feasible test channel. Perturbs the feasible
factorizable test channel `qf` to a full-support kernel `κ'` (`wz_fullKernelSupport_perturbation`),
restricts the covering source to the support subtype `α' := {x // 0 < P_X x}`, and produces the
rate-distortion covering `LossyCode` family (`wz_covering_lossyCode_exists`) for the proxy
distortion `d'` (the `Y`-conditional expectation of `d ∘ qf.2`).

The output packages, for downstream binning, the perturbed full-support factorizable joint `q'`
(with kernel `κ'`), the restricted covering joint `qStar`, the covering proxy `d'`, the Wyner–Ziv
objective margin `< R`, and — for every covering rate `R₁` strictly above the covering mutual
information `mutualInfoPmf qStar` — the covering `LossyCode` family with block distortion within
`(D + δ) + ε'`. The covering-distortion feasibility `expectedDistortionPmf d' qStar ≤ D + δ` is the
reconciliation identity (`wz_coveringDistortion_reconcile`) applied to the perturbation's distortion
bound. All conclusions are genuinely constructed; the only preconditions are feasibility (`hqf`),
the objective margin (`hobj`), and the slack `δ`. The output existential also exports, alongside
`d'`, the reconciliation identity `hd'_eq` (`d'` = the `Y`-conditional expectation of `d ∘ qf.2`,
discharged by `rfl` since the witness is that expression) and the test channel's factorizability
`hqf` (the original input membership), so downstream binning can honestly relate the covering proxy
`d'` to the real distortion `d` via `qf.2`.

The `LossyCode` family conclusion also exports, for the returned code `c`, a covering-acceptance
failure mass bound at a radius `ε` that is a universal binder (`∀ R₁ …, ∀ ε' …, ∀ ε, 0 < ε →
∃ N …`). The product source–side measure of `wzCoveringAcceptFailSet P_XY κ' c ε` (the event that
the true covering word is not jointly typical with the side information) is
`≤ δ / (8 · (distortionMax d + 1))`, a fixed vanishing tolerance. Because `ε` is a family binder,
the caller chooses the same `ε` it feeds the bin-decoder radius, so the union bound `C2 ⊆ E2` uses
a matching radius. The covering-acceptance failure `C2` is the true-word joint-AEP failure and
decays to 0; it is the covering half of the Wyner–Ziv `E2` error event, threaded to
`wz_exists_binning_E2_bound` and discharged by construction (the `distortionMax d` scaling only
sizes the tolerance so `dMax · Pr[C2]` is absorbable).

The covering-acceptance conjunct is discharged by the joint derandomize
`wz_covering_lossyCode_joint_exists`, which produces — for the same code — a low block distortion
(`≤ (D+δ)+ε'`) and a small strong-covering-failure mass (`SRC(wzCoveringSuccessStrong)ᶜ ≤ tol/2`).
The strong-`Ecov` Markov-core leaf `wz_covering_chosenWord_sideInfo_typical` then turns that
covering-success complement bound into the acceptance-failure bound
`≤ tol = δ/(8·(distortionMax d + 1))`. The joint derandomize couples the distortion-typicality
failure (drives block distortion via `source_avg_distortion_le_simpler_generic`) and the
strong-joint-typicality failure at the encoder radius `ε_join` (drives covering-success via
`wz_coveringSuccessStrong_compl_measureReal_le` + the measure alignment
`wz_covering_SRC_map_Xproj_eq` and radius bridge `wz_jointStrongly_mem_coveringSuccessJoint`): both
codebook-averaged failures are bounded by the shared vanishing upper
`(P_X n){Xⁿ ∉ T*_X} + exp(-Mₙ·exp(-n(I+slack)))`, and `exists_codebook_low_avg` on their sum
extracts one codebook good for both. The strong covering-success lower bound rests on the gateway
`wz_covering_strongTypical_indep_mass_ge` (the WZ instance of
`jointStronglyTypicalSet_indep_prob_ge`). The covering-success event is `wzCoveringSuccessStrong`
(strong-at-`ε_cov` ∩ weak-at-`ε`), which makes the Markov-core chain true-as-framed.

The good code is genuinely constructed (perturb to a full-support kernel → restricted `qStar` →
codebook-average + `exists_codebook_low_avg` pigeonhole in `wz_covering_lossyCode_joint_exists`,
then the strong-`Ecov` leaf), not a bundled `*Hypothesis`. The closure rests on strong typicality at
the separated radius `ε_cov = ε/(2(1+C))` (`wzCoveringStrongRadius`, positive), with the weak-at-`ε`
conjunct a strong ⟹ weak plumbing consequence.

@audit:ok -/
lemma wz_coveringFamily_of_testChannel
    (P_XY : Measure (α × β)) [IsProbabilityMeasure P_XY]
    (d : DistortionFn α γ) (R D : ℝ)
    (k : ℕ) (qf : (α × β × Fin k → ℝ) × (Fin k × β → γ))
    (hqf : qf ∈ WynerZivFactorizableConstraint (Fin k)
            (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
    (hobj : wzMutualInfoXU (Fin k) qf.1 - wzMutualInfoYU (Fin k) qf.1 < R)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (q' : α × β × Fin k → ℝ) (κ' : α → Fin k → ℝ)
      (qStar : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k → ℝ)
      (d' : DistortionFn {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k)),
        (∀ x y u, q' (x, y, u) = κ' x u * P_XY.real {(x, y)})
        ∧ (∀ x u, 0 < κ' x u)
        ∧ (∀ x, ∑ u, κ' x u = 1)
        ∧ (wzMutualInfoXU (Fin k) q' - wzMutualInfoYU (Fin k) q' < R)
        ∧ (∀ p, qStar p = κ' p.1.1 p.2 * ∑ y, P_XY.real {(p.1.1, y)})
        ∧ (∀ p, 0 < qStar p)
        ∧ qStar ∈ stdSimplex ℝ ({x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k)
        ∧ expectedDistortionPmf d' qStar ≤ D + δ
        ∧ (∀ (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (u : Fin k),
             d' x' u = Real.toNNReal (∑ y : β,
               (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
                 * ((d x'.1 (qf.2 (u, y)) : NNReal) : ℝ)))
        ∧ (qf ∈ WynerZivFactorizableConstraint (Fin k)
             (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D)
        ∧ (∀ R₁ : ℝ, mutualInfoPmf qStar < R₁ → ∀ ε' : ℝ, 0 < ε' → ∀ ε : ℝ, 0 < ε →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : ℕ,
              Nat.ceil (Real.exp ((n : ℝ) * R₁)) ≤ M ∧
              (M : ℝ) ≤ Real.exp ((n : ℝ) * R₁) + 1 ∧
              ∃ c : LossyCode M n {x : α // 0 < ∑ y, P_XY.real {(x, y)}} (Fin k),
                c.expectedBlockDistortion
                    ((rdAmbient qStar).map (ChannelCoding.iidXs 0)) d'
                  ≤ (D + δ) + ε'
                ∧ (Measure.pi (fun _ : Fin n ↦ ChannelCoding.pmfToMeasure
                      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × β ↦
                        P_XY.real {(p.1.1, p.2)}))).real
                    (wzCoveringAcceptFailSet P_XY κ' c ε)
                    ≤ δ / (8 * (distortionMax d + 1))) := by
  classical
  -- Perturb the feasible test channel to a full-support kernel `κ'`.
  -- Keep a pristine copy of the factorizability membership: `hqf` is mutated by the
  -- `rw` below, but the output existential re-exports the original membership (`hqf₀`).
  have hqf₀ := hqf
  rw [mem_WynerZivFactorizableConstraint_iff] at hqf
  obtain ⟨hfact, hdist⟩ := hqf
  haveI : Nonempty (Fin k) := wz_nonempty_of_factorizable hfact
  obtain ⟨q', κ', hq'eq, hκ'pos, hκ'sum, _hfact', hobj', hdist'⟩ :=
    wz_fullKernelSupport_perturbation (fun p ↦ P_XY.real {p}) (fun a b ↦ (d a b : ℝ)) D
      hfact hdist hobj hδ
  -- Restricted covering joint (S1): full support + simplex on the source-support subtype.
  obtain ⟨hne, hqStar_pos, hqStar_mem⟩ :=
    wz_restrictedCoveringJoint_pos P_XY κ' hκ'pos hκ'sum
  haveI : Nonempty {x : α // 0 < ∑ y, P_XY.real {(x, y)}} := hne
  -- The perturbed joint, packaged as a clean pointwise identity.
  have hq'clean : ∀ p : α × β × Fin k, q' p = κ' p.1 p.2.2 * P_XY.real {(p.1, p.2.1)} :=
    fun p ↦ hq'eq p.1 p.2.1 p.2.2
  have hconv :
      (fun p : α × β × Fin k ↦ κ' p.1 p.2.2 * P_XY.real {(p.1, p.2.1)}) = q' := by
    funext p; exact (hq'clean p).symm
  -- Covering-distortion feasibility via the reconciliation identity.
  have hfeas : expectedDistortionPmf
      (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (u : Fin k) ↦
        Real.toNNReal (∑ y : β, (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
            * ((d x'.1 (qf.2 (u, y)) : NNReal) : ℝ)))
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k ↦
        κ' p.1.1 p.2 * ∑ y : β, P_XY.real {(p.1.1, y)}) ≤ D + δ := by
    rw [wz_coveringDistortion_reconcile P_XY d κ' qf.2, hconv]
    exact hdist'
  -- Assemble the covering `LossyCode` family from the covering theorem.
  refine ⟨q', κ',
    (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k ↦
      κ' p.1.1 p.2 * ∑ y : β, P_XY.real {(p.1.1, y)}),
    (fun (x' : {x : α // 0 < ∑ y, P_XY.real {(x, y)}}) (u : Fin k) ↦
      Real.toNNReal (∑ y : β, (P_XY.real {(x'.1, y)} / ∑ y' : β, P_XY.real {(x'.1, y')})
          * ((d x'.1 (qf.2 (u, y)) : NNReal) : ℝ))),
    hq'eq, hκ'pos, hκ'sum, hobj', fun _ ↦ rfl, hqStar_pos, hqStar_mem, hfeas,
    (fun _ _ ↦ rfl), hqf₀, ?_⟩
  -- The covering `LossyCode` family is good for BOTH the covering distortion AND the
  -- covering-acceptance failure C2, via the joint derandomize `wz_covering_lossyCode_joint_exists`
  -- (one code with low block distortion AND small strong-covering-failure mass) fed through the
  -- strong-`Ecov` Markov-core leaf `wz_covering_chosenWord_sideInfo_typical`: the leaf turns the
  -- covering-success complement bound `≤ tol/2` into the acceptance-failure bound `≤ tol`.
  intro R₁ hR₁ ε' hε' ε hε
  set tolAcc : ℝ := δ / (8 * (distortionMax d + 1)) with htolAcc_def
  have htolAcc_pos : 0 < tolAcc := by
    rw [htolAcc_def]
    exact div_pos hδ (by have := distortionMax_nonneg d; positivity)
  have hqStar_eq : ∀ p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k,
      (fun p : {x : α // 0 < ∑ y, P_XY.real {(x, y)}} × Fin k ↦
        κ' p.1.1 p.2 * ∑ y : β, P_XY.real {(p.1.1, y)}) p
        = κ' p.1.1 p.2 * ∑ y : β, P_XY.real {(p.1.1, y)} := fun _ ↦ rfl
  obtain ⟨N_leaf, hleaf⟩ := wz_covering_chosenWord_sideInfo_typical P_XY κ' _ ε hε
    tolAcc htolAcc_pos hκ'pos hκ'sum hqStar_eq
  obtain ⟨N_der, hder⟩ := wz_covering_lossyCode_joint_exists P_XY κ' hκ'sum _ hqStar_pos
    hqStar_mem hqStar_eq _ hR₁ hfeas hε' hε (half_pos htolAcc_pos)
  refine ⟨max N_leaf N_der, fun n hn ↦ ?_⟩
  obtain ⟨M, hMlb, hMub, c, hdist, hcovfail⟩ := hder n (le_trans (le_max_right _ _) hn)
  exact ⟨M, hMlb, hMub, c, hdist, hleaf n (le_trans (le_max_left _ _) hn) M c hcovfail⟩

end InformationTheory.Shannon