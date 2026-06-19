import InformationTheory.Shannon.EPI.Case1.SmoothingLimit
import InformationTheory.Shannon.EPI.Stam.SupplyTwoTime
import InformationTheory.Shannon.EPI.G2.ConvEntropyMonotone

namespace InformationTheory.Shannon.EPIInfiniteVarianceTruncation

open MeasureTheory Filter Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1SmoothingLimit
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAdd_comm)
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The truncation set `truncSet X Y n := {ω | |X ω| ≤ n ∧ |Y ω| ≤ n}`, a rectangular event
truncating both components simultaneously. It is monotone increasing in `n : ℕ` and exhausts the
whole space. -/
def truncSet (X Y : Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | |X ω| ≤ (n : ℝ) ∧ |Y ω| ≤ (n : ℝ)}

theorem measurableSet_truncSet {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (n : ℕ) :
    MeasurableSet (truncSet X Y n) := by
  have hXm : MeasurableSet {ω | |X ω| ≤ (n : ℝ)} :=
    measurableSet_le hX.abs measurable_const
  have hYm : MeasurableSet {ω | |Y ω| ≤ (n : ℝ)} :=
    measurableSet_le hY.abs measurable_const
  exact hXm.inter hYm

theorem truncSet_mono {X Y : Ω → ℝ} : Monotone (truncSet X Y) := by
  intro n m hnm ω hω
  have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  exact ⟨hω.1.trans hnm', hω.2.trans hnm'⟩

theorem iUnion_truncSet (X Y : Ω → ℝ) : ⋃ n, truncSet X Y n = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro ω
  obtain ⟨nX, hnX⟩ := exists_nat_ge (|X ω|)
  obtain ⟨nY, hnY⟩ := exists_nat_ge (|Y ω|)
  refine Set.mem_iUnion.2 ⟨max nX nY, ?_, ?_⟩
  · exact hnX.trans (by exact_mod_cast le_max_left nX nY)
  · exact hnY.trans (by exact_mod_cast le_max_right nX nY)

/-- The conditioning measure `condTrunc P X Y n := P[· | truncSet X Y n]`. For large `n` the mass
`P (truncSet X Y n)` is positive, so this is a probability measure. -/
noncomputable def condTrunc (P : Measure Ω) (X Y : Ω → ℝ) (n : ℕ) : Measure Ω :=
  ProbabilityTheory.cond P (truncSet X Y n)

theorem measure_truncSet_tendsto_one (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (_hX : Measurable X) (_hY : Measurable Y) :
    Tendsto (fun n => P (truncSet X Y n)) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := P) (truncSet_mono (X := X) (Y := Y))
  rw [iUnion_truncSet X Y, measure_univ] at h
  exact h

theorem eventually_measure_truncSet_pos (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    ∀ᶠ n in atTop, P (truncSet X Y n) ≠ 0 := by
  have h := measure_truncSet_tendsto_one P hX hY
  have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) :=
    isOpen_ne.mem_nhds one_ne_zero
  exact h.eventually_mem h_nhds

theorem isProbabilityMeasure_condTrunc (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (_hX : Measurable X) (_hY : Measurable Y) {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) :
    IsProbabilityMeasure (condTrunc P X Y n) := by
  unfold condTrunc
  exact ProbabilityTheory.cond_isProbabilityMeasure hpos

/-- Independence is preserved by joint conditioning: `IndepFun X Y P` implies
`IndepFun X Y (condTrunc P X Y n)`, since the conditioning event `X⁻¹[-n, n] ∩ Y⁻¹[-n, n]` is
rectangular. -/
theorem indepFun_condTrunc (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P) {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) :
    IndepFun X Y (condTrunc P X Y n) := by
  classical
  -- `truncSet X Y n = X ⁻¹' Sn ∩ Y ⁻¹' Sn` with `Sn = {r | |r| ≤ n}` measurable.
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn :=
    measurableSet_le measurable_norm measurable_const
  have hs_eq : truncSet X Y n = X ⁻¹' Sn ∩ Y ⁻¹' Sn := rfl
  have hs_meas : MeasurableSet (truncSet X Y n) := measurableSet_truncSet hX hY n
  -- mass of the conditioning set factors: `P s = P(X⁻¹Sn) * P(Y⁻¹Sn)`.
  have h_mass : P (truncSet X Y n) = P (X ⁻¹' Sn) * P (Y ⁻¹' Sn) := by
    rw [hs_eq]; exact hXY.measure_inter_preimage_eq_mul Sn Sn hSn_meas hSn_meas
  have hPXSn_ne : P (X ⁻¹' Sn) ≠ 0 := by
    intro h0; apply hpos; rw [h_mass, h0, zero_mul]
  have hPYSn_ne : P (Y ⁻¹' Sn) ≠ 0 := by
    intro h0; apply hpos; rw [h_mass, h0, mul_zero]
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  -- abbreviations
  have hXAm : MeasurableSet (X ⁻¹' A) := hX hA
  have hYBm : MeasurableSet (Y ⁻¹' B) := hY hB
  have hXASn : MeasurableSet (X ⁻¹' (A ∩ Sn)) := hX (hA.inter hSn_meas)
  have hYBSn : MeasurableSet (Y ⁻¹' (B ∩ Sn)) := hY (hB.inter hSn_meas)
  -- LHS: `(condTrunc)(X⁻¹A ∩ Y⁻¹B)`.
  have hLHS : (condTrunc P X Y n) (X ⁻¹' A ∩ Y ⁻¹' B)
      = (P (truncSet X Y n))⁻¹ * (P (X ⁻¹' (A ∩ Sn)) * P (Y ⁻¹' (B ∩ Sn))) := by
    unfold condTrunc
    rw [cond_apply hs_meas P]
    congr 1
    -- `s ∩ (X⁻¹A ∩ Y⁻¹B) = X⁻¹(A∩Sn) ∩ Y⁻¹(B∩Sn)`.
    have h_inter : truncSet X Y n ∩ (X ⁻¹' A ∩ Y ⁻¹' B)
        = X ⁻¹' (A ∩ Sn) ∩ Y ⁻¹' (B ∩ Sn) := by
      rw [hs_eq]; ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [h_inter]
    exact hXY.measure_inter_preimage_eq_mul (A ∩ Sn) (B ∩ Sn)
      (hA.inter hSn_meas) (hB.inter hSn_meas)
  -- `(condTrunc)(X⁻¹A) = (P s)⁻¹ * P(X⁻¹(A∩Sn)) * P(Y⁻¹Sn)`.
  have hcondX : (condTrunc P X Y n) (X ⁻¹' A)
      = (P (truncSet X Y n))⁻¹ * (P (X ⁻¹' (A ∩ Sn)) * P (Y ⁻¹' Sn)) := by
    unfold condTrunc
    rw [cond_apply hs_meas P]
    congr 1
    have h_inter : truncSet X Y n ∩ X ⁻¹' A = X ⁻¹' (A ∩ Sn) ∩ Y ⁻¹' Sn := by
      rw [hs_eq]; ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [h_inter]
    exact hXY.measure_inter_preimage_eq_mul (A ∩ Sn) Sn (hA.inter hSn_meas) hSn_meas
  -- `(condTrunc)(Y⁻¹B) = (P s)⁻¹ * P(X⁻¹Sn) * P(Y⁻¹(B∩Sn))`.
  have hcondY : (condTrunc P X Y n) (Y ⁻¹' B)
      = (P (truncSet X Y n))⁻¹ * (P (X ⁻¹' Sn) * P (Y ⁻¹' (B ∩ Sn))) := by
    unfold condTrunc
    rw [cond_apply hs_meas P]
    congr 1
    have h_inter : truncSet X Y n ∩ Y ⁻¹' B = X ⁻¹' Sn ∩ Y ⁻¹' (B ∩ Sn) := by
      rw [hs_eq]; ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [h_inter]
    exact hXY.measure_inter_preimage_eq_mul Sn (B ∩ Sn) hSn_meas (hB.inter hSn_meas)
  -- finite-ness needed for cancellation.
  have hPs_ne : P (truncSet X Y n) ≠ ∞ := measure_ne_top P _
  have hPXSn_top : P (X ⁻¹' Sn) ≠ ∞ := measure_ne_top P _
  have hPYSn_top : P (Y ⁻¹' Sn) ≠ ∞ := measure_ne_top P _
  rw [hLHS, hcondX, hcondY, h_mass]
  -- algebraic identity in ℝ≥0∞.
  set a := P (X ⁻¹' (A ∩ Sn))
  set b := P (Y ⁻¹' (B ∩ Sn))
  set c := P (X ⁻¹' Sn)
  set d := P (Y ⁻¹' Sn)
  -- goal: `(c*d)⁻¹ * (a*b) = ((c*d)⁻¹ * (a*d)) * ((c*d)⁻¹ * (c*b))`.
  have hcd_cancel : (c * d)⁻¹ * (c * d) = 1 :=
    ENNReal.inv_mul_cancel (mul_ne_zero hPXSn_ne hPYSn_ne)
      (ENNReal.mul_ne_top hPXSn_top hPYSn_top)
  calc (c * d)⁻¹ * (a * b)
      = ((c * d)⁻¹ * (c * d)) * ((c * d)⁻¹ * (a * b)) := by rw [hcd_cancel, one_mul]
    _ = ((c * d)⁻¹ * (a * d)) * ((c * d)⁻¹ * (c * b)) := by ring

/-- Absolute continuity is preserved by conditioning truncation: `(P.map X) ≪ volume` implies
`((condTrunc P X Y n).map X) ≪ volume`, composing `cond_absolutelyContinuous` with monotonicity of
`Measure.map`. -/
theorem map_condTrunc_absolutelyContinuous (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (_hX : Measurable X) {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ_ac : (P.map Z) ≪ volume) {n : ℕ} :
    ((condTrunc P X Y n).map Z) ≪ volume := by
  have h_cond : condTrunc P X Y n ≪ P := ProbabilityTheory.cond_absolutelyContinuous
  exact (h_cond.map hZ).trans hZ_ac

/-- Pushing the jointly-conditioned measure `condTrunc P X Y n` forward along a component `Z`
(`Z = X` or `Z = Y`) reduces to single-component conditioning:
`(condTrunc P X Y n).map Z = cond (P.map Z) {r | |r| ≤ n}`. The partner mass `P (Y⁻¹ Sn)` from the
independence factoring `P (truncSet) = P (X⁻¹ Sn) · P (Y⁻¹ Sn)` cancels.
@audit:ok -/
theorem map_condTrunc_eq_cond_map (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y) {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    (condTrunc P X Y n).map Z
      = ProbabilityTheory.cond (P.map Z) {r : ℝ | |r| ≤ (n : ℝ)} := by
  classical
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn :=
    measurableSet_le measurable_norm measurable_const
  have hs_eq : truncSet X Y n = X ⁻¹' Sn ∩ Y ⁻¹' Sn := rfl
  have hs_meas : MeasurableSet (truncSet X Y n) := measurableSet_truncSet hX hY n
  -- mass of the conditioning set factors.
  have h_mass : P (truncSet X Y n) = P (X ⁻¹' Sn) * P (Y ⁻¹' Sn) := by
    rw [hs_eq]; exact hXY.measure_inter_preimage_eq_mul Sn Sn hSn_meas hSn_meas
  have hPXSn_ne : P (X ⁻¹' Sn) ≠ 0 := by
    intro h0; apply hpos; rw [h_mass, h0, zero_mul]
  have hPYSn_ne : P (Y ⁻¹' Sn) ≠ 0 := by
    intro h0; apply hpos; rw [h_mass, h0, mul_zero]
  have hPs_top : P (truncSet X Y n) ≠ ∞ := measure_ne_top P _
  have hPXSn_top : P (X ⁻¹' Sn) ≠ ∞ := measure_ne_top P _
  have hPYSn_top : P (Y ⁻¹' Sn) ≠ ∞ := measure_ne_top P _
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  -- The two halves of the argument are symmetric in `X ↔ Y`. We prove a generic
  -- statement parametrised by which component plays the role of `Z`, using the
  -- partner mass `P (W ⁻¹' Sn)` (`W` = the other component) which cancels out.
  refine Measure.ext (fun A hA => ?_)
  -- RHS: `cond (P.map Z) Sn A = (P (Z⁻¹Sn))⁻¹ * P (Z⁻¹(Sn ∩ A))`.
  have hRHS : (ProbabilityTheory.cond (P.map Z) Sn) A
      = (P (Z ⁻¹' Sn))⁻¹ * P (Z ⁻¹' (Sn ∩ A)) := by
    rw [ProbabilityTheory.cond_apply hSn_meas (P.map Z) A,
      Measure.map_apply hZmeas hSn_meas,
      Measure.map_apply hZmeas (hSn_meas.inter hA), Set.preimage_inter]
  -- LHS: `(condTrunc P X Y n).map Z A = condTrunc P X Y n (Z⁻¹A)`.
  rw [Measure.map_apply hZmeas hA]
  unfold condTrunc
  rw [ProbabilityTheory.cond_apply hs_meas P, hRHS]
  rcases hZ with rfl | rfl
  · -- Z = X (subst makes `X` the surviving name `Z`): partner `P(Y⁻¹Sn)` cancels.
    -- `truncSet Z Y n ∩ Z⁻¹A = Z⁻¹(Sn ∩ A) ∩ Y⁻¹Sn`.
    have h_inter : truncSet Z Y n ∩ Z ⁻¹' A = Z ⁻¹' (Sn ∩ A) ∩ Y ⁻¹' Sn := by
      rw [hs_eq]; ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto
    rw [h_inter, hXY.measure_inter_preimage_eq_mul (Sn ∩ A) Sn (hSn_meas.inter hA) hSn_meas,
      h_mass]
    -- `(c*d)⁻¹ * (a*d) = c⁻¹ * a`  with `a = P(Z⁻¹(Sn∩A)), c = P(Z⁻¹Sn), d = P(Y⁻¹Sn)`.
    rw [ENNReal.mul_inv (Or.inl hPXSn_ne) (Or.inl hPXSn_top)]
    rw [mul_comm (P (Z ⁻¹' (Sn ∩ A))) (P (Y ⁻¹' Sn)), ← mul_assoc, mul_assoc _ _ (P (Y ⁻¹' Sn))]
    rw [ENNReal.inv_mul_cancel hPYSn_ne hPYSn_top, mul_one]
  · -- Z = Y (subst makes `Y` the surviving name `Z`): partner `P(X⁻¹Sn)` cancels.
    -- `truncSet X Z n ∩ Z⁻¹A = X⁻¹Sn ∩ Z⁻¹(Sn ∩ A)`.
    have h_inter : truncSet X Z n ∩ Z ⁻¹' A = X ⁻¹' Sn ∩ Z ⁻¹' (Sn ∩ A) := by
      rw [hs_eq]; ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage]; tauto
    rw [h_inter, hXY.measure_inter_preimage_eq_mul Sn (Sn ∩ A) hSn_meas (hSn_meas.inter hA),
      h_mass]
    -- `(c*d)⁻¹ * (c*b) = d⁻¹ * b`  with `b = P(Z⁻¹(Sn∩A)), c = P(X⁻¹Sn), d = P(Z⁻¹Sn)`.
    rw [ENNReal.mul_inv (Or.inl hPXSn_ne) (Or.inl hPXSn_top),
      mul_mul_mul_comm (P (X ⁻¹' Sn))⁻¹ (P (Z ⁻¹' Sn))⁻¹ (P (X ⁻¹' Sn)) (P (Z ⁻¹' (Sn ∩ A))),
      ENNReal.inv_mul_cancel hPXSn_ne hPXSn_top, one_mul]

/-- The Radon–Nikodym derivative of a measure conditioned on a positive-mass set `s` is the
indicator-restricted density scaled by the normalizing constant:
`(cond μ s).rnDeriv volume =ᵐ (μ s)⁻¹ · 1_s · μ.rnDeriv volume`.
@audit:ok -/
theorem rnDeriv_cond_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Set ℝ}
    (hs : MeasurableSet s) (hpos : μ s ≠ 0) :
    (ProbabilityTheory.cond μ s).rnDeriv volume
      =ᵐ[volume] fun x => (μ s)⁻¹ * s.indicator (μ.rnDeriv volume) x := by
  have hr : (μ s)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hpos
  -- `cond μ s = (μ s)⁻¹ • μ.restrict s`, so its rnDeriv equals the scaled restrict rnDeriv.
  have h1 : (ProbabilityTheory.cond μ s).rnDeriv volume
      =ᵐ[volume] (μ s)⁻¹ • (μ.restrict s).rnDeriv volume := by
    show ((μ s)⁻¹ • μ.restrict s).rnDeriv volume =ᵐ[volume] (μ s)⁻¹ • (μ.restrict s).rnDeriv volume
    exact Measure.rnDeriv_smul_left_of_ne_top (μ.restrict s) volume hr
  -- `(μ.restrict s).rnDeriv volume =ᵐ s.indicator (μ.rnDeriv volume)`.
  have h2 : (μ.restrict s).rnDeriv volume =ᵐ[volume] s.indicator (μ.rnDeriv volume) :=
    Measure.rnDeriv_restrict μ volume hs
  refine h1.trans ?_
  filter_upwards [h2] with x hx
  simp only [Pi.smul_apply, hx, smul_eq_mul]

/-- Per-`n` finite second moment `Integrable ((Z ·)²) (condTrunc P X Y n)`. Since `condTrunc` is
supported on `truncSet`, the component `Z = X` or `Z = Y` is bounded by `n`, so its second moment
is bounded. -/
theorem integrable_sq_condTrunc (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {Z : Ω → ℝ} {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) (hZ : Z = X ∨ Z = Y) :
    Integrable (fun ω => (Z ω) ^ 2) (condTrunc P X Y n) := by
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  have hZ_meas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  -- `condTrunc`-a.e. ω lies in truncSet, so `|Z ω| ≤ n`, hence `Z ω ^ 2 ∈ [0, n^2]`.
  have h_mem : ∀ᵐ ω ∂(condTrunc P X Y n), ω ∈ truncSet X Y n := by
    unfold condTrunc
    exact ProbabilityTheory.ae_cond_mem (measurableSet_truncSet hX hY n)
  refine Integrable.of_mem_Icc 0 ((n : ℝ) ^ 2) (hZ_meas.pow_const 2).aemeasurable ?_
  filter_upwards [h_mem] with ω hω
  have hZ_le : |Z ω| ≤ (n : ℝ) := by rcases hZ with rfl | rfl; exacts [hω.1, hω.2]
  constructor
  · positivity
  · calc (Z ω) ^ 2 = |Z ω| ^ 2 := (sq_abs (Z ω)).symm
      _ ≤ (n : ℝ) ^ 2 := by gcongr

/-- Per-`n` finite differential entropy of a component: `Integrable (negMulLog (rnDeriv ·)) volume`
for `(condTrunc P X Y n).map Z`. The entropy integrability of the conditioned marginal
`condTrunc.map Z = cond (P.map Z) Sn` is derived from that of `P.map Z` (the precondition
`hZ_ent`) via the conditional density formula. This re-supplies the `hX_ent` / `hY_ent` arguments
of the finite-variance black box.
@audit:ok -/
theorem integrable_negMulLog_map_condTrunc (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y)
    (_hZ_ac : (P.map Z) ≪ volume)
    (hZ_ent : Integrable (fun x => Real.negMulLog ((P.map Z).rnDeriv volume x).toReal) volume)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    Integrable
      (fun x => Real.negMulLog (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal) volume := by
  classical
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn :=
    measurableSet_le measurable_norm measurable_const
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  haveI : IsProbabilityMeasure (P.map Z) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  -- positive mass of `Sn` under `P.map Z` (so that `cond` is the genuine conditioning).
  have hSn_pos : (P.map Z) Sn ≠ 0 := by
    rw [Measure.map_apply hZmeas hSn_meas]
    -- `P (Z⁻¹Sn)` is one of the two factors of `P (truncSet X Y n)`.
    have hfac : P (truncSet X Y n) = P (X ⁻¹' Sn) * P (Y ⁻¹' Sn) := by
      show P (X ⁻¹' Sn ∩ Y ⁻¹' Sn) = _
      exact hXY.measure_inter_preimage_eq_mul Sn Sn hSn_meas hSn_meas
    rcases hZ with rfl | rfl
    · intro h0; apply hpos; rw [hfac, h0, zero_mul]
    · intro h0; apply hpos; rw [hfac, h0, mul_zero]
  -- bridge (A): the pushforward of the conditioning equals single-component conditioning.
  rw [map_condTrunc_eq_cond_map P hX hY hXY hZ hpos]
  -- abbreviations: `m = (P.map Z) Sn`, `q x = ((P.map Z).rnDeriv volume x).toReal`.
  set m : ℝ≥0∞ := (P.map Z) Sn with hm_def
  set q : ℝ → ℝ := fun x => ((P.map Z).rnDeriv volume x).toReal with hq_def
  have hm_ne_top : m ≠ ∞ := measure_ne_top _ _
  -- cond density formula (B): rewrite the integrand a.e.
  have h_rn : (ProbabilityTheory.cond (P.map Z) Sn).rnDeriv volume
      =ᵐ[volume] fun x => m⁻¹ * Sn.indicator ((P.map Z).rnDeriv volume) x :=
    rnDeriv_cond_eq (P.map Z) hSn_meas hSn_pos
  -- target integrand `=ᵐ` the indicator-split form.
  -- `q` itself is integrable (probability measure, finite, toReal rnDeriv).
  have hq_int : Integrable q volume := Measure.integrable_toReal_rnDeriv
  -- the two pieces, both restricted to `Sn`:
  --   piece1 = negMulLog (m.toReal⁻¹) • (q · 1_Sn)   [from `y * negMulLog x` term]
  --   piece2 = (m.toReal⁻¹) • (negMulLog q · 1_Sn)   [from `x * negMulLog y` term]
  set c : ℝ := (m⁻¹).toReal with hc_def
  have h_inner : Integrable
      (fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)) volume := by
    have h1 : Integrable (fun x => q x * Real.negMulLog c) volume := hq_int.mul_const _
    have h2 : Integrable (fun x => c * Real.negMulLog (q x)) volume := hZ_ent.const_mul c
    exact h1.add h2
  have h_split : Integrable
      (fun x => Sn.indicator (fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)) x)
      volume := h_inner.indicator hSn_meas
  refine h_split.congr ?_
  -- a.e. identification of the indicator-split form with the original integrand.
  filter_upwards [h_rn] with x hx
  show Sn.indicator (fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)) x
      = Real.negMulLog (((ProbabilityTheory.cond (P.map Z) Sn).rnDeriv volume x).toReal)
  rw [hx]
  by_cases hxs : x ∈ Sn
  · rw [Set.indicator_of_mem hxs (f := fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)),
      ENNReal.toReal_mul,
      Set.indicator_of_mem hxs (f := (P.map Z).rnDeriv volume)]
    show q x * Real.negMulLog c + c * Real.negMulLog (q x) = Real.negMulLog (c * q x)
    exact (Real.negMulLog_mul c (q x)).symm
  · rw [Set.indicator_of_notMem hxs
      (f := fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)),
      Set.indicator_of_notMem hxs (f := (P.map Z).rnDeriv volume)]
    simp only [mul_zero, ENNReal.toReal_zero, Real.negMulLog_zero]

/-- The absolutely continuous measure `(condTrunc P X Y n).map Z` is recovered as
`volume.withDensity (ofReal ∘ r)` from the real density `r := (rnDeriv ·).toReal`, via
`withDensity_rnDeriv_eq` together with `ofReal ∘ toReal = id` on the a.e.-finite rnDeriv.
@audit:ok -/
theorem map_condTrunc_withDensity_toReal_rnDeriv (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {Z : Ω → ℝ} (_hZ : Measurable Z)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0)
    (hZ_ac : ((condTrunc P X Y n).map Z) ≪ volume) :
    (condTrunc P X Y n).map Z
      = volume.withDensity
        (fun x => ENNReal.ofReal (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal) := by
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  haveI : IsProbabilityMeasure ((condTrunc P X Y n).map Z) :=
    Measure.isProbabilityMeasure_map _hZ.aemeasurable
  have hcongr : (fun x => ENNReal.ofReal (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal)
      =ᵐ[volume] ((condTrunc P X Y n).map Z).rnDeriv volume := by
    filter_upwards [((condTrunc P X Y n).map Z).rnDeriv_lt_top volume] with x hx
    exact ENNReal.ofReal_toReal hx.ne
  rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hZ_ac]

/-- The conditioned sum density is the convolution of the conditioned marginal densities: the
rnDeriv of the law of `X + Y` under `condTrunc P X Y n` equals
`convDensityAdd p_n q_n` a.e., where `p_n := (condTrunc.map X).rnDeriv volume |>.toReal` and
`q_n := (condTrunc.map Y).rnDeriv volume |>.toReal`. Obtained by applying `indepSum_density_ae`
with `condTrunc P X Y n` in place of `P` (independence from `indepFun_condTrunc`, absolute
continuity from `map_condTrunc_absolutelyContinuous`).
@audit:ok -/
theorem rnDeriv_map_condTrunc_sum_ae (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    ((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume
      =ᵐ[volume] fun x => ENNReal.ofReal
        (convDensityAdd (fun y => ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal)
          (fun y => ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal) x) := by
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  -- a.c. of the three pushforwards.
  have hXac_n : ((condTrunc P X Y n).map X) ≪ volume :=
    map_condTrunc_absolutelyContinuous P hX hX hX_ac
  have hYac_n : ((condTrunc P X Y n).map Y) ≪ volume :=
    map_condTrunc_absolutelyContinuous P hX hY hY_ac
  have hXYac_n : ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) ≪ volume := by
    have hsum_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume := by
      -- the sum law is a.c. since it is the convolution of two a.c. laws.
      have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
        rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
      rw [hconv]
      exact Measure.conv_absolutelyContinuous hY_ac
    have h_cond : condTrunc P X Y n ≪ P := ProbabilityTheory.cond_absolutelyContinuous
    exact (h_cond.map (hX.add hY)).trans hsum_ac
  -- density witnesses.
  set pX : ℝ → ℝ := fun y => ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal with hpX
  set pY : ℝ → ℝ := fun y => ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal with hpY
  set pXY : ℝ → ℝ := fun y => ((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume y
    |>.toReal with hpXY
  -- measurability + non-negativity of the toReal rnDerivs.
  have hpX_meas : Measurable pX := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpY_meas : Measurable pY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpXY_meas : Measurable pXY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x => ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x => ENNReal.toReal_nonneg
  have hpXY_nn : ∀ x, 0 ≤ pXY x := fun x => ENNReal.toReal_nonneg
  -- withDensity laws.
  have hpX_law : (condTrunc P X Y n).map X
      = volume.withDensity (fun x => ENNReal.ofReal (pX x)) :=
    map_condTrunc_withDensity_toReal_rnDeriv P hX hY hX hpos hXac_n
  have hpY_law : (condTrunc P X Y n).map Y
      = volume.withDensity (fun x => ENNReal.ofReal (pY x)) :=
    map_condTrunc_withDensity_toReal_rnDeriv P hX hY hY hpos hYac_n
  have hpXY_law : (condTrunc P X Y n).map (fun ω => X ω + Y ω)
      = volume.withDensity (fun x => ENNReal.ofReal (pXY x)) :=
    map_condTrunc_withDensity_toReal_rnDeriv P hX hY (hX.add hY) hpos hXYac_n
  -- integrability of the marginal densities.
  have hpX_int : Integrable pX volume := Measure.integrable_toReal_rnDeriv
  have hpY_int : Integrable pY volume := Measure.integrable_toReal_rnDeriv
  -- lmasses: `∫⁻ ofReal(pW) = (condTrunc.map W) univ`.
  have hlmass : ∀ (W : Ω → ℝ) (pW : ℝ → ℝ),
      (condTrunc P X Y n).map W = volume.withDensity (fun x => ENNReal.ofReal (pW x))
      → (∫⁻ x, ENNReal.ofReal (pW x) ∂volume) = ((condTrunc P X Y n).map W) Set.univ := by
    intro W pW hlaw
    rw [hlaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hpX_lmass : (∫⁻ x, ENNReal.ofReal (pX x) ∂volume) = 1 := by
    rw [hlmass X pX hpX_law]
    haveI : IsProbabilityMeasure ((condTrunc P X Y n).map X) :=
      Measure.isProbabilityMeasure_map hX.aemeasurable
    exact measure_univ
  have hpY_lmass : (∫⁻ x, ENNReal.ofReal (pY x) ∂volume) = 1 := by
    rw [hlmass Y pY hpY_law]
    haveI : IsProbabilityMeasure ((condTrunc P X Y n).map Y) :=
      Measure.isProbabilityMeasure_map hY.aemeasurable
    exact measure_univ
  have hpXY_lmass : (∫⁻ x, ENNReal.ofReal (pXY x) ∂volume) ≠ ⊤ := by
    rw [hlmass (fun ω => X ω + Y ω) pXY hpXY_law]
    exact measure_ne_top _ _
  -- a.e. identity: `pXY =ᵐ convDensityAdd pX pY` (general convolution density).
  have hkey : pXY =ᵐ[volume] convDensityAdd pX pY :=
    EPIStamSupplyTwoTime.indepSum_density_ae (P := condTrunc P X Y n) X Y hX hY
      (indepFun_condTrunc P hX hY hXY hpos)
      pX pY pXY hpX_nn hpX_meas hpY_nn hpY_meas hpX_law hpY_law hpXY_law
      hpXY_nn hpXY_meas hpX_int hpY_int hpXY_lmass hpX_lmass hpY_lmass
  -- transport to the rnDeriv: `rnDeriv =ᵐ ofReal pXY =ᵐ ofReal (convDensityAdd pX pY)`.
  have hrn_ofReal : ((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume
      =ᵐ[volume] fun x => ENNReal.ofReal (pXY x) := by
    filter_upwards
      [((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv_lt_top volume] with x hx
    exact (ENNReal.ofReal_toReal hx.ne).symm
  filter_upwards [hrn_ofReal, hkey] with x hx hkx
  rw [hx, hkx]

/-- Compact support of the sum law: since `condTrunc P X Y n` is concentrated on `truncSet`
(both components bounded by `n`), the push-forward law of `X + Y` is concentrated on
`Icc (-(2n)) (2n)`, i.e. `(condTrunc.map (X + Y)) (Icc (-(2n)) (2n))ᶜ = 0`.
@audit:ok -/
theorem map_condTrunc_sum_concentrated (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {n : ℕ}
    (_hpos : P (truncSet X Y n) ≠ 0) :
    ((condTrunc P X Y n).map (fun ω => X ω + Y ω))
      (Set.Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)))ᶜ = 0 := by
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY _hpos
  rw [Measure.map_apply (hX.add hY) (measurableSet_Icc.compl)]
  -- `condTrunc (truncSetᶜ) = 0` (concentrated on `truncSet`).
  have h_trunc_compl : (condTrunc P X Y n) (truncSet X Y n)ᶜ = 0 := by
    have h_mem : ∀ᵐ ω ∂(condTrunc P X Y n), ω ∈ truncSet X Y n := by
      unfold condTrunc
      exact ProbabilityTheory.ae_cond_mem (measurableSet_truncSet hX hY n)
    rw [ae_iff] at h_mem
    exact h_mem
  -- the preimage of `(Icc)ᶜ` is contained in `(truncSet)ᶜ`.
  refine measure_mono_null (fun ω hω => ?_) h_trunc_compl
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc] at hω ⊢
  -- if `ω ∈ truncSet`, then `|X ω + Y ω| ≤ 2n`, contradicting `ω ∉ Icc`.
  intro hmem
  have hXle : |X ω| ≤ (n : ℝ) := hmem.1
  have hYle : |Y ω| ≤ (n : ℝ) := hmem.2
  have hsum : |X ω + Y ω| ≤ 2 * (n : ℝ) := by
    calc |X ω + Y ω| ≤ |X ω| + |Y ω| := abs_add_le _ _
      _ ≤ (n : ℝ) + (n : ℝ) := by linarith
      _ = 2 * (n : ℝ) := by ring
  rw [abs_le] at hsum
  exact hω ⟨by linarith [hsum.1], by linarith [hsum.2]⟩

theorem aestronglyMeasurable_convKernel_ofReal_mul {p g : ℝ → ℝ}
    (hp : Measurable p) (hg : Measurable g) :
    AEStronglyMeasurable (fun q : ℝ × ℝ => p q.2 * g (q.1 - q.2)) (volume.prod volume) :=
  ((hp.comp measurable_snd).mul
    (hg.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable

theorem lintegral_lintegral_convKernel_ofReal_eq_mul {p g : ℝ → ℝ}
    (hp : Measurable p) (hp_nn : ∀ x, 0 ≤ p x) (hg : Measurable g) (_hg_nn : ∀ w, 0 ≤ g w) :
    ∫⁻ z, ∫⁻ x, ENNReal.ofReal (p x * g (z - x)) ∂volume ∂volume
      = (∫⁻ x, ENNReal.ofReal (p x) ∂volume) * (∫⁻ w, ENNReal.ofReal (g w) ∂volume) := by
  -- swap to `∫⁻ x ∫⁻ z`, translate `z ↦ z + x`, factor.
  have hswap : ∫⁻ z, ∫⁻ x, ENNReal.ofReal (p x * g (z - x)) ∂volume ∂volume
      = ∫⁻ x, ∫⁻ z, ENNReal.ofReal (p x * g (z - x)) ∂volume ∂volume := by
    rw [lintegral_lintegral_swap]
    exact ((hp.comp measurable_snd).mul
      (hg.comp (measurable_fst.sub measurable_snd))).ennreal_ofReal.aemeasurable
  rw [hswap]
  -- inner integral over `z`: pull out `ofReal (p x)`, translate.
  have hgz_meas : ∀ x : ℝ, Measurable (fun z => ENNReal.ofReal (g (z - x))) := fun x =>
    (hg.comp (measurable_id.sub_const x)).ennreal_ofReal
  have hinner : ∀ x, ∫⁻ z, ENNReal.ofReal (p x * g (z - x)) ∂volume
      = ENNReal.ofReal (p x) * ∫⁻ w, ENNReal.ofReal (g w) ∂volume := by
    intro x
    calc ∫⁻ z, ENNReal.ofReal (p x * g (z - x)) ∂volume
        = ∫⁻ z, ENNReal.ofReal (p x) * ENNReal.ofReal (g (z - x)) ∂volume := by
          apply lintegral_congr; intro z; rw [ENNReal.ofReal_mul (hp_nn x)]
      _ = ENNReal.ofReal (p x) * ∫⁻ z, ENNReal.ofReal (g (z - x)) ∂volume :=
          lintegral_const_mul _ (hgz_meas x)
      _ = ENNReal.ofReal (p x) * ∫⁻ w, ENNReal.ofReal (g w) ∂volume := by
          rw [lintegral_sub_right_eq_self (fun w => ENNReal.ofReal (g w)) x]
  simp_rw [hinner]
  rw [lintegral_mul_const _ hp.ennreal_ofReal]

theorem integrable_convKernel_of_lintegral_ne_top {p g : ℝ → ℝ}
    (hp : Measurable p) (hp_nn : ∀ x, 0 ≤ p x)
    (hp_lint : ∫⁻ x, ENNReal.ofReal (p x) ∂volume = 1)
    (hg : Measurable g) (hg_nn : ∀ w, 0 ≤ g w)
    (hg_fin : (∫⁻ w, ENNReal.ofReal (g w) ∂volume) ≠ ∞) :
    Integrable (fun q : ℝ × ℝ => p q.2 * g (q.1 - q.2)) (volume.prod volume) := by
  refine ⟨aestronglyMeasurable_convKernel_ofReal_mul hp hg, ?_⟩
  have hnn : ∀ᵐ q : ℝ × ℝ ∂(volume.prod volume), 0 ≤ p q.2 * g (q.1 - q.2) :=
    Filter.Eventually.of_forall (fun q => mul_nonneg (hp_nn _) (hg_nn _))
  rw [hasFiniteIntegral_iff_ofReal hnn,
    lintegral_prod _ (aestronglyMeasurable_convKernel_ofReal_mul hp hg).aemeasurable.ennreal_ofReal,
    lintegral_lintegral_convKernel_ofReal_eq_mul hp hp_nn hg hg_nn, hp_lint, one_mul]
  exact lt_of_le_of_ne le_top hg_fin

private theorem ae_section_integrable_convKernel {pn g : ℝ → ℝ}
    (hpn_meas : Measurable pn) (hpn_nn : ∀ x, 0 ≤ pn x)
    (hpn_lint : ∫⁻ x, ENNReal.ofReal (pn x) ∂volume = 1)
    (hg_meas : Measurable g) (hg_nn : ∀ x, 0 ≤ g x)
    (hg_fin : (∫⁻ w, ENNReal.ofReal (g w) ∂volume) ≠ ∞) :
    ∀ᵐ z ∂volume, Integrable (fun x => pn x * g (z - x)) volume :=
  (integrable_convKernel_of_lintegral_ne_top hpn_meas hpn_nn hpn_lint
    hg_meas hg_nn hg_fin).prod_right_ae

private theorem jensen_convDensityAdd_le_section_integral {pn qn : ℝ → ℝ}
    (hpn_meas : Measurable pn) (hpn_nn : ∀ x, 0 ≤ pn x)
    (hqn_meas : Measurable qn) (hqn_nn : ∀ x, 0 ≤ qn x)
    (hpn_lint : ∫⁻ x, ENNReal.ofReal (pn x) ∂volume = 1)
    (hsec_qn : ∀ᵐ z ∂volume, Integrable (fun x => pn x * qn (z - x)) volume)
    (hsec_Cq : ∀ᵐ z ∂volume,
      Integrable (fun x => pn x * max (qn (z - x) * Real.log (qn (z - x))) 0) volume)
    (hsec_Cm : ∀ᵐ z ∂volume,
      Integrable (fun x => pn x * max (-(qn (z - x) * Real.log (qn (z - x)))) 0) volume) :
    ∀ᵐ z ∂volume, max ((fun t => t * Real.log t) (EPIConvDensity.convDensityAdd pn qn z)) 0
      ≤ ∫ x, pn x * max (qn (z - x) * Real.log (qn (z - x))) 0 ∂volume := by
  classical
  set φ : ℝ → ℝ := fun t => t * Real.log t with hφ_def
  have hφ_meas : Measurable φ := measurable_id.mul (Real.measurable_log.comp measurable_id)
  set μX : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (pn x)) with hμX_def
  haveI hμXP : IsProbabilityMeasure μX := by
    refine ⟨?_⟩
    rw [hμX_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hpn_lint]
  filter_upwards [hsec_qn, hsec_Cq, hsec_Cm] with z hzqn hzCq hzCm
  -- abbreviation `f x = qn (z - x)`.
  set f : ℝ → ℝ := fun x => qn (z - x) with hf_def
  have hf_meas : Measurable f := hqn_meas.comp (measurable_const.sub measurable_id)
  have hf_nn : ∀ x, 0 ≤ f x := fun _ => hqn_nn _
  have hpnofReal_meas : Measurable (fun x => ENNReal.ofReal (pn x)) := hpn_meas.ennreal_ofReal
  have hpnofReal_lt : ∀ᵐ x ∂volume, ENNReal.ofReal (pn x) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  -- `convDensityAdd pn qn z = ∫ x, f x ∂μX`.
  have hμX_smul : ∀ (h : ℝ → ℝ),
      ∫ x, h x ∂μX = ∫ x, pn x * h x ∂volume := by
    intro h
    rw [hμX_def, integral_withDensity_eq_integral_toReal_smul hpnofReal_meas hpnofReal_lt]
    apply integral_congr_ae; filter_upwards with x
    rw [ENNReal.toReal_ofReal (hpn_nn x), smul_eq_mul]
  -- `f` and the two positive/negative halves are integrable w.r.t. `μX`.
  have hf_int : Integrable f μX := by
    rw [hμX_def, integrable_withDensity_iff_integrable_smul' hpnofReal_meas hpnofReal_lt]
    refine hzqn.congr ?_
    filter_upwards with x; rw [ENNReal.toReal_ofReal (hpn_nn x), smul_eq_mul]
  have hCqf_int : Integrable (fun x => max (φ (f x)) 0) μX := by
    rw [hμX_def, integrable_withDensity_iff_integrable_smul' hpnofReal_meas hpnofReal_lt]
    refine hzCq.congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hpn_nn x), smul_eq_mul]
  have hCmf_int : Integrable (fun x => max (-(φ (f x))) 0) μX := by
    rw [hμX_def, integrable_withDensity_iff_integrable_smul' hpnofReal_meas hpnofReal_lt]
    refine hzCm.congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hpn_nn x), smul_eq_mul]
  -- `φ ∘ f = (φ∘f)⁺ - (φ∘f)⁻`, hence integrable.
  have hφf_eq : (fun x => φ (f x)) = fun x => max (φ (f x)) 0 - max (-(φ (f x))) 0 := by
    funext x
    rcases le_or_gt 0 (φ (f x)) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -(φ (f x)) ≤ 0)]; ring
    · rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(φ (f x)))]; ring
  have hφf_int : Integrable (fun x => φ (f x)) μX := by
    rw [hφf_eq]; exact hCqf_int.sub hCmf_int
  -- Jensen:  `φ (∫ f ∂μX) ≤ ∫ φ∘f ∂μX`.
  have hjz : φ (∫ x, f x ∂μX) ≤ ∫ x, φ (f x) ∂μX := by
    have := Real.convexOn_mul_log.map_integral_le
      (μ := μX) (f := f) (g := φ)
      Real.continuous_mul_log.continuousOn
      isClosed_Ici
      (Filter.Eventually.of_forall (fun x => hf_nn x))
      hf_int hφf_int
    simpa only [hφ_def] using this
  -- `convDensityAdd pn qn z = ∫ x, pn x * f x ∂volume = ∫ x, f x ∂μX`.
  have hrz_eq : EPIConvDensity.convDensityAdd pn qn z = ∫ x, f x ∂μX := by
    rw [hμX_smul f]; rfl
  -- `φ (cda z) ≤ ∫ φ∘f ∂μX ≤ ∫ Cq∘f ∂μX = ∫ x, pn x * Cq (z-x) ∂vol`.
  have hstep1 : φ (EPIConvDensity.convDensityAdd pn qn z) ≤ ∫ x, φ (f x) ∂μX := by
    rw [hrz_eq]; exact hjz
  have hstep2 : (∫ x, φ (f x) ∂μX) ≤ ∫ x, max (φ (f x)) 0 ∂μX :=
    integral_mono hφf_int hCqf_int (fun x => le_max_left _ _)
  have hstep3 : (∫ x, max (φ (f x)) 0 ∂μX)
      = ∫ x, pn x * max (qn (z - x) * Real.log (qn (z - x))) 0 ∂volume := by
    rw [hμX_smul (fun x => max (φ (f x)) 0)]
  have hCq_int_z : (0 : ℝ) ≤ ∫ x, pn x * max (qn (z - x) * Real.log (qn (z - x))) 0 ∂volume :=
    integral_nonneg (fun x => mul_nonneg (hpn_nn x) (le_max_right _ _))
  show max (φ (EPIConvDensity.convDensityAdd pn qn z)) 0 ≤ _
  exact max_le (by rw [← hstep3]; exact le_trans hstep1 hstep2) hCq_int_z

/-- The negative part `(negMulLog r)⁻ = max (-(negMulLog r)) 0` of `negMulLog` of the conditioned
sum density `r := (condTrunc.map (X + Y)).rnDeriv volume |>.toReal` (the convolution `p_n ∗ q_n`)
is `volume`-integrable. This is the genuine core of the per-`n` finite-entropy lemma (the positive
part is immediate from compact support and `negMulLog_le_one_sub_self`).

Since `p_n · volume` is a probability measure and `t ↦ t log t` is convex, the integral form of
Jensen's inequality gives `(r z · log r z)⁺ ≤ ∫ x, p_n x · (q_n (z - x) · log q_n (z - x))⁺ dx`,
and Tonelli with translation invariance bounds `∫⁻ z (r log r)⁺` by `1 · C < ∞`, where
`C = ∫ (q_n log q_n)⁺ < ∞` is the negative part of the integrable `negMulLog q_n`.

The hypothesis `hY_ent` is essential: a convolution of two singular densities can be unbounded, so
finiteness of the negative part requires entropy-type control rather than absolute continuity and
independence alone (the proof uses only `hY_ent`).
@audit:ok -/
theorem integrable_negPart_negMulLog_map_condTrunc_sum (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P)
    (_hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    Integrable
      (fun x => max (-(Real.negMulLog
        (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) 0) volume := by
  classical
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  -- marginal densities of the conditioned components, and the sum density `r`.
  set pn : ℝ → ℝ := fun y => ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal with hpn_def
  set qn : ℝ → ℝ := fun y => ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal with hqn_def
  set ν := (condTrunc P X Y n).map (fun ω => X ω + Y ω) with hν_def
  set r : ℝ → ℝ := fun x => (ν.rnDeriv volume x).toReal with hr_def
  -- `φ t = t log t = -(negMulLog t)`.  Goal integrand is `max (φ (r ·)) 0`.
  set φ : ℝ → ℝ := fun t => t * Real.log t with hφ_def
  have hφ_eq : ∀ t, -(Real.negMulLog t) = φ t := by
    intro t; show -(-t * Real.log t) = t * Real.log t; ring
  -- basic measurability / nonnegativity.
  have hr_meas : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hr_nn : ∀ x, 0 ≤ r x := fun _ => ENNReal.toReal_nonneg
  have hpn_meas : Measurable pn := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hqn_meas : Measurable qn := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpn_nn : ∀ x, 0 ≤ pn x := fun _ => ENNReal.toReal_nonneg
  have hqn_nn : ∀ x, 0 ≤ qn x := fun _ => ENNReal.toReal_nonneg
  have hφ_meas : Measurable φ := measurable_id.mul (Real.measurable_log.comp measurable_id)
  -- target integrand `G z := max (φ (r z)) 0`.
  set G : ℝ → ℝ := fun z => max (φ (r z)) 0 with hG_def
  have hG_nn : ∀ z, 0 ≤ G z := fun _ => le_max_right _ _
  have hG_meas : Measurable G := (hφ_meas.comp hr_meas).max measurable_const
  have hgoal_eq : (fun x => max (-(Real.negMulLog
      (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) 0) = G := by
    funext z; rw [hG_def]; simp only [hφ_eq, hr_def, hν_def]
  rw [hgoal_eq]
  -- `r =ᵐ convDensityAdd pn qn` (sum density identity).
  have hr_conv : r =ᵐ[volume] EPIConvDensity.convDensityAdd pn qn := by
    have h := rnDeriv_map_condTrunc_sum_ae P hX hY hX_ac hY_ac hXY hpos
    filter_upwards [h] with x hx
    show (ν.rnDeriv volume x).toReal = EPIConvDensity.convDensityAdd pn qn x
    rw [hν_def, hx, ENNReal.toReal_ofReal]
    exact integral_nonneg (fun t => mul_nonneg (hpn_nn t) (hqn_nn _))
  -- `pn · vol` is a probability measure (since `∫ pn = 1`).
  have hpn_law : (condTrunc P X Y n).map X
      = volume.withDensity (fun x => ENNReal.ofReal (pn x)) :=
    map_condTrunc_withDensity_toReal_rnDeriv P hX hY hX hpos
      (map_condTrunc_absolutelyContinuous P hX hX hX_ac)
  haveI hpnP : IsProbabilityMeasure ((condTrunc P X Y n).map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  set μX : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (pn x)) with hμX_def
  haveI hμXP : IsProbabilityMeasure μX := hpn_law ▸ hpnP
  -- `pn`'s lintegral is `1`.
  have hpn_lint : ∫⁻ x, ENNReal.ofReal (pn x) ∂volume = 1 := by
    have hu : μX Set.univ = 1 := measure_univ
    rwa [hμX_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hu
  -- `qn`'s entropy integrand is integrable (the genuine use of `hY_ent`).
  have hqn_ent_int : Integrable (fun x => Real.negMulLog (qn x)) volume :=
    integrable_negMulLog_map_condTrunc P hX hY hXY (Or.inr rfl) hY_ac hY_ent hpos
  -- the two halves of `φ ∘ qn`:  `Cq = (φ qn)⁺`,  `Cm = (φ qn)⁻`,  both integrable.
  set Cq : ℝ → ℝ := fun w => max (φ (qn w)) 0 with hCq_def
  set Cm : ℝ → ℝ := fun w => max (-(φ (qn w))) 0 with hCm_def
  have hCq_nn : ∀ w, 0 ≤ Cq w := fun _ => le_max_right _ _
  have hCm_nn : ∀ w, 0 ≤ Cm w := fun _ => le_max_right _ _
  have hCq_meas : Measurable Cq := (hφ_meas.comp hqn_meas).max measurable_const
  have hCm_meas : Measurable Cm := ((hφ_meas.comp hqn_meas).neg).max measurable_const
  have hCq_int : Integrable Cq volume := by
    have heq : Cq = fun w => max ((-(fun x => Real.negMulLog (qn x))) w) 0 := by
      funext w; show max (φ (qn w)) 0 = max (-(Real.negMulLog (qn w))) 0
      rw [hφ_eq]
    rw [heq]; exact hqn_ent_int.neg.pos_part
  have hCm_int : Integrable Cm volume := by
    have heq : Cm = fun w => max ((fun x => Real.negMulLog (qn x)) w) 0 := by
      funext w; show max (-(φ (qn w))) 0 = max (Real.negMulLog (qn w)) 0
      rw [← hφ_eq, neg_neg]
    rw [heq]; exact hqn_ent_int.pos_part
  -- finiteness of `C = ∫⁻ ofReal (Cq) = ∫⁻ ofReal ((φ qn)⁺)`.
  set C : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (Cq w) ∂volume with hC_def
  have hC_lt_top : C < ∞ := by
    have hfin := hCq_int.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hCq_nn)] at hfin
    rw [hC_def]; exact hfin
  -- ============================================================================
  -- a.e.-`z` section integrabilities, from global product integrability of the
  -- convolution kernels (`integrable_convKernel_of_lintegral_ne_top`).
  -- ============================================================================
  -- the three section facts (a.e. `z`), for `g ∈ {qn, Cq, Cm}`.
  have hqn_lint : ∫⁻ w, ENNReal.ofReal (qn w) ∂volume = 1 := by
    have hlaw : (condTrunc P X Y n).map Y
        = volume.withDensity (fun x => ENNReal.ofReal (qn x)) :=
      map_condTrunc_withDensity_toReal_rnDeriv P hX hY hY hpos
        (map_condTrunc_absolutelyContinuous P hX hY hY_ac)
    haveI : IsProbabilityMeasure ((condTrunc P X Y n).map Y) :=
      Measure.isProbabilityMeasure_map hY.aemeasurable
    have h1 : ((condTrunc P X Y n).map Y) Set.univ = 1 := measure_univ
    rwa [hlaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  have hCm_fin : (∫⁻ w, ENNReal.ofReal (Cm w) ∂volume) ≠ ∞ := by
    have hfin := hCm_int.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hCm_nn)] at hfin
    exact hfin.ne
  have hsec_qn := ae_section_integrable_convKernel hpn_meas hpn_nn hpn_lint
    hqn_meas hqn_nn (by rw [hqn_lint]; exact ENNReal.one_ne_top)
  have hsec_Cq := ae_section_integrable_convKernel hpn_meas hpn_nn hpn_lint
    hCq_meas hCq_nn (by rw [← hC_def]; exact hC_lt_top.ne)
  have hsec_Cm := ae_section_integrable_convKernel hpn_meas hpn_nn hpn_lint
    hCm_meas hCm_nn hCm_fin
  -- ============================================================================
  -- per-`z` Jensen bound:  `G z ≤ ∫ x, pn x * Cq (z - x) ∂volume`  (a.e. `z`).
  -- ============================================================================
  have hjensen : ∀ᵐ z ∂volume, G z ≤ ∫ x, pn x * Cq (z - x) ∂volume := by
    have hbound := jensen_convDensityAdd_le_section_integral hpn_meas hpn_nn hqn_meas hqn_nn
      hpn_lint hsec_qn hsec_Cq hsec_Cm
    filter_upwards [hr_conv, hbound] with z hz hzb
    show max (φ (r z)) 0 ≤ _
    rw [hz]
    exact hzb
  -- ============================================================================
  -- assemble:  `∫⁻ ofReal G ≤ ∫⁻ z ∫⁻ x ofReal (pn x * Cq (z-x)) = 1·C < ∞`.
  -- ============================================================================
  refine ⟨hG_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG_nn)]
  -- `∫⁻ ofReal G ≤ ∫⁻ z, ofReal (∫ x, pn x * Cq (z-x)) = ∫⁻ z ∫⁻ x ofReal (...)`.
  calc ∫⁻ z, ENNReal.ofReal (G z) ∂volume
      ≤ ∫⁻ z, ENNReal.ofReal (∫ x, pn x * Cq (z - x) ∂volume) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [hjensen] with z hz
        exact ENNReal.ofReal_le_ofReal hz
    _ ≤ ∫⁻ z, ∫⁻ x, ENNReal.ofReal (pn x * Cq (z - x)) ∂volume ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [hsec_Cq] with z hz
        calc ENNReal.ofReal (∫ x, pn x * Cq (z - x) ∂volume)
            = ∫⁻ x, ENNReal.ofReal (pn x * Cq (z - x)) ∂volume := by
              rw [ofReal_integral_eq_lintegral_ofReal hz
                (Filter.Eventually.of_forall (fun x => mul_nonneg (hpn_nn x) (hCq_nn _)))]
          _ ≤ _ := le_refl _
    _ = (∫⁻ x, ENNReal.ofReal (pn x) ∂volume) * (∫⁻ w, ENNReal.ofReal (Cq w) ∂volume) :=
        lintegral_lintegral_convKernel_ofReal_eq_mul hpn_meas hpn_nn hCq_meas hCq_nn
    _ = C := by rw [hpn_lint, one_mul, hC_def]
    _ < ∞ := hC_lt_top

/-- Per-`n` finite differential entropy of the sum: the density
`r := (condTrunc.map (X + Y)).rnDeriv volume |>.toReal` (the convolution `p_n ∗ q_n`, supported on
`[-2n, 2n]`) has integrable `negMulLog`, via a positive/negative-part split. The positive part is
bounded using `negMulLog_le_one_sub_self` and integrability of `r`; the negative part is the
preceding lemma. This re-supplies the `hent_sum` argument of the finite-variance black box.
@audit:ok -/
theorem integrable_negMulLog_map_condTrunc_sum (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    Integrable
      (fun x => Real.negMulLog
        (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume := by
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  set ν := (condTrunc P X Y n).map (fun ω => X ω + Y ω) with hν_def
  have hsum_meas : Measurable (fun ω => X ω + Y ω) := hX.add hY
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  set r : ℝ → ℝ := fun x => (ν.rnDeriv volume x).toReal with hr_def
  have hr_meas : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hr_nn : ∀ x, 0 ≤ r x := fun x => ENNReal.toReal_nonneg
  -- `r` is itself integrable (probability measure, toReal rnDeriv).
  have hr_int : Integrable r volume := Measure.integrable_toReal_rnDeriv
  -- compact support: `r =ᵐ Icc.indicator r` (rnDeriv vanishes a.e. off `[-2n, 2n]`).
  set I : Set ℝ := Set.Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)) with hI_def
  have hI_meas : MeasurableSet I := measurableSet_Icc
  have hr_supp : r =ᵐ[volume] I.indicator r := by
    -- off `I`, the measure `ν` of `Iᶜ` is 0, so its density `r` vanishes a.e. there.
    have hconc : ν Iᶜ = 0 := map_condTrunc_sum_concentrated P hX hY hpos
    have hac : ν ≪ volume := by
      rw [hν_def]; exact map_condTrunc_absolutelyContinuous P hX hsum_meas (by
        have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
          rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
        rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac)
    -- `∫⁻_{Iᶜ} rnDeriv = ν Iᶜ = 0`, so `rnDeriv = 0` a.e. on `Iᶜ`.
    have hlint : ∫⁻ x in Iᶜ, ν.rnDeriv volume x ∂volume = 0 := by
      rw [Measure.setLIntegral_rnDeriv hac]; exact hconc
    have hrn_zero : ∀ᵐ x ∂volume, x ∈ Iᶜ → ν.rnDeriv volume x = 0 := by
      have := (setLIntegral_eq_zero_iff hI_meas.compl
        (Measure.measurable_rnDeriv ν volume)).mp hlint
      filter_upwards [this] with x hx hmem
      exact hx hmem
    filter_upwards [hrn_zero] with x hx
    by_cases hxI : x ∈ I
    · rw [Set.indicator_of_mem hxI]
    · rw [Set.indicator_of_notMem hxI, hr_def]
      simp only [hx hxI, ENNReal.toReal_zero]
  -- positive part `g₁ := max (negMulLog r) 0`: bounded by `Icc.indicator 1` a.e.
  set g₁ : ℝ → ℝ := fun x => max (Real.negMulLog (r x)) 0 with hg₁_def
  set g₂ : ℝ → ℝ := fun x => max (-(Real.negMulLog (r x))) 0 with hg₂_def
  have hr_negMulLog_meas : Measurable (fun x => Real.negMulLog (r x)) :=
    Real.continuous_negMulLog.measurable.comp hr_meas
  have hg₁_meas : AEStronglyMeasurable g₁ volume :=
    (hr_negMulLog_meas.max measurable_const).aestronglyMeasurable
  -- `g₁ ≤ I.indicator 1` a.e.: off `I`, `r = 0` so `negMulLog 0 = 0`, `g₁ = 0`;
  --  on `I`, `negMulLog r ≤ 1 - r ≤ 1` (since `r ≥ 0`).
  have hbound_int : Integrable (I.indicator (fun _ => (1 : ℝ))) volume :=
    (integrableOn_const (s := I) (μ := volume) measure_Icc_lt_top.ne).integrable_indicator hI_meas
  have hg₁_le : ∀ᵐ x ∂volume, ‖g₁ x‖ ≤ I.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hr_supp] with x hx
    have hg₁_nn : 0 ≤ g₁ x := le_max_right _ _
    rw [Real.norm_of_nonneg hg₁_nn]
    by_cases hxI : x ∈ I
    · rw [Set.indicator_of_mem hxI]
      refine max_le ?_ (by norm_num)
      calc Real.negMulLog (r x) ≤ 1 - r x := Real.negMulLog_le_one_sub_self (hr_nn x)
        _ ≤ 1 := by linarith [hr_nn x]
    · -- off `I`: `r x = (I.indicator r) x = 0`, so `negMulLog 0 = 0`, `g₁ x = 0`.
      rw [Set.indicator_of_notMem hxI]
      have hrx0 : r x = 0 := by rw [hx, Set.indicator_of_notMem hxI]
      rw [hg₁_def]; simp only [hrx0, Real.negMulLog_zero, max_self, le_refl]
  have hg₁_int : Integrable g₁ volume :=
    Integrable.mono' hbound_int hg₁_meas hg₁_le
  -- negative part `g₂` integrable (the genuine core, supplied by the negPart lemma).
  have hg₂_int : Integrable g₂ volume :=
    integrable_negPart_negMulLog_map_condTrunc_sum P hX hY hX_ac hY_ac hXY hX_ent hY_ent hpos
  -- `negMulLog r = g₁ - g₂` pointwise (`a = a⁺ - a⁻`).
  have hsplit : (fun x => Real.negMulLog (r x)) = fun x => g₁ x - g₂ x := by
    funext x
    simp only [hg₁_def, hg₂_def]
    rcases le_or_gt 0 (Real.negMulLog (r x)) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith : -(Real.negMulLog (r x)) ≤ 0)]; ring
    · rw [max_eq_right h.le, max_eq_left (by linarith : 0 ≤ -(Real.negMulLog (r x)))]; ring
  rw [show (fun x => Real.negMulLog (ν.rnDeriv volume x).toReal)
      = fun x => Real.negMulLog (r x) from rfl, hsplit]
  exact hg₁_int.sub hg₂_int

/-! ### Per-n entropy power inequality (wiring to the finite-variance black box) -/

/-- Per-`n` finite-variance entropy power inequality: supplying all regularity to the black box
`entropyPowerExt_add_ge_of_finite_variance` gives, for each positive-mass `n`,
`Nₑ(P_n.map (X + Y)) ≥ Nₑ(P_n.map X) + Nₑ(P_n.map Y)`.
@audit:ok -/
theorem entropyPowerExt_condTrunc_add_ge (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt ((condTrunc P X Y n).map X)
        + entropyPowerExt ((condTrunc P X Y n).map Y) := by
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  exact entropyPowerExt_add_ge_of_finite_variance (condTrunc P X Y n) X Y hX hY
    (indepFun_condTrunc P hX hY hXY hpos)
    (map_condTrunc_absolutelyContinuous P hX hX hX_ac)
    (map_condTrunc_absolutelyContinuous P hX hY hY_ac)
    (integrable_sq_condTrunc P hX hY hpos (Or.inl rfl))
    (integrable_sq_condTrunc P hX hY hpos (Or.inr rfl))
    (integrable_negMulLog_map_condTrunc P hX hY hXY (Or.inl rfl) hX_ac hX_ent hpos)
    (integrable_negMulLog_map_condTrunc P hX hY hXY (Or.inr rfl) hY_ac hY_ent hpos)
    (integrable_negMulLog_map_condTrunc_sum P hX hY hX_ac hY_ac hXY hX_ent hY_ent hpos)

/-- Generalized Gibbs (cross-entropy lower bound): for probability measures with `μ ≪ ν` and
`μ ≪ volume`, `differentialEntropy μ ≤ -∫ x, log (ν.rnDeriv volume x).toReal ∂μ`. It follows from
`(klDiv μ ν).toReal ≥ 0` and the log-likelihood-ratio decomposition `toReal_klDiv_of_measure_eq`.
This generalizes the Gaussian-reference template `differentialEntropy_le_gaussian_of_variance_le`
to an arbitrary reference `ν`.
@audit:ok -/
theorem differentialEntropy_le_cross_entropy {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ_ac : μ ≪ volume) (_hν_ac : ν ≪ volume) (hμν : μ ≪ ν)
    (hμ_ent : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume)
    (h_cross_int : Integrable
      (fun x => Real.log ((ν.rnDeriv volume x).toReal)) μ) :
    differentialEntropy μ ≤ - ∫ x, Real.log ((ν.rnDeriv volume x).toReal) ∂μ := by
  -- `(klDiv μ ν).toReal = ∫ llr μ ν ∂μ ≥ 0`.
  have h_meas_eq : μ Set.univ = ν Set.univ := by simp
  have h_kl_eq : (klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ :=
    toReal_klDiv_of_measure_eq hμν h_meas_eq
  have h_kl_nn : (0 : ℝ) ≤ ∫ x, llr μ ν x ∂μ := h_kl_eq ▸ ENNReal.toReal_nonneg
  -- rnDeriv chain: `μ.rnDeriv ν * ν.rnDeriv vol =ᵐ[μ] μ.rnDeriv vol`.
  have h_rn_chain_vol : μ.rnDeriv ν * ν.rnDeriv volume =ᵐ[volume] μ.rnDeriv volume :=
    Measure.rnDeriv_mul_rnDeriv hμν
  have h_rn_chain_μ : μ.rnDeriv ν * ν.rnDeriv volume =ᵐ[μ] μ.rnDeriv volume :=
    hμ_ac.ae_le h_rn_chain_vol
  have h_rn_μν_pos : ∀ᵐ x ∂μ, 0 < μ.rnDeriv ν x := Measure.rnDeriv_pos hμν
  have h_rn_μν_lt_top : ∀ᵐ x ∂μ, μ.rnDeriv ν x < ∞ :=
    hμν.ae_le (Measure.rnDeriv_lt_top μ ν)
  have h_rn_μvol_pos : ∀ᵐ x ∂μ, 0 < μ.rnDeriv volume x := Measure.rnDeriv_pos hμ_ac
  have h_rn_νvol_lt_top : ∀ᵐ x ∂μ, ν.rnDeriv volume x < ∞ :=
    hμ_ac.ae_le (Measure.rnDeriv_lt_top ν volume)
  -- llr decomposition: `llr μ ν x = log (μ.rnDeriv vol).toReal - log (ν.rnDeriv vol).toReal`.
  have h_llr_decomp : ∀ᵐ x ∂μ,
      llr μ ν x = Real.log ((μ.rnDeriv volume x).toReal)
        - Real.log ((ν.rnDeriv volume x).toReal) := by
    filter_upwards [h_rn_chain_μ, h_rn_μν_pos, h_rn_μν_lt_top, h_rn_μvol_pos, h_rn_νvol_lt_top]
      with x h_chain h_μν_pos h_μν_lt_top h_μvol_pos h_νvol_lt_top
    -- `μ.rnDeriv vol x = μ.rnDeriv ν x * ν.rnDeriv vol x`.
    have h_combine : μ.rnDeriv volume x = μ.rnDeriv ν x * ν.rnDeriv volume x := by
      rw [← h_chain]; rfl
    have hμν_real_pos : 0 < (μ.rnDeriv ν x).toReal :=
      ENNReal.toReal_pos h_μν_pos.ne' h_μν_lt_top.ne
    -- `ν.rnDeriv vol x > 0` μ-a.e.: from `0 < μ.rnDeriv vol x = μ.rnDeriv ν x * ν.rnDeriv vol x`.
    have hν_vol_ne : ν.rnDeriv volume x ≠ 0 := by
      intro h0
      rw [h_combine, h0, mul_zero] at h_μvol_pos
      exact lt_irrefl 0 h_μvol_pos
    have hν_vol_pos : 0 < (ν.rnDeriv volume x).toReal :=
      ENNReal.toReal_pos hν_vol_ne h_νvol_lt_top.ne
    show Real.log ((μ.rnDeriv ν x).toReal)
        = Real.log ((μ.rnDeriv volume x).toReal) - Real.log ((ν.rnDeriv volume x).toReal)
    rw [h_combine, ENNReal.toReal_mul,
      Real.log_mul hμν_real_pos.ne' hν_vol_pos.ne']
    ring
  -- `∫ log (μ.rnDeriv vol x).toReal ∂μ = - h(μ)`.
  have h_int_log_μ_eq :
      ∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ = - differentialEntropy μ := by
    have h_pull : ∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ
        = ∫ x, (μ.rnDeriv volume x).toReal • Real.log ((μ.rnDeriv volume x).toReal) ∂volume := by
      rw [integral_rnDeriv_smul (μ := μ) (ν := volume) hμ_ac
        (f := fun x => Real.log ((μ.rnDeriv volume x).toReal))]
    rw [h_pull]
    unfold differentialEntropy
    rw [show -∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume
        = ∫ x, -Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume from (integral_neg _).symm]
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [smul_eq_mul, Real.negMulLog_def]
    ring
  -- `∫ log (μ.rnDeriv vol).toReal ∂μ` integrable on μ (= -negMulLog pulled back).
  have h_int_log_μ : Integrable (fun x => Real.log ((μ.rnDeriv volume x).toReal)) μ := by
    rw [← integrable_rnDeriv_smul_iff (μ := μ) (ν := volume) hμ_ac
      (f := fun x => Real.log ((μ.rnDeriv volume x).toReal))]
    refine (hμ_ent.neg).congr (Filter.Eventually.of_forall fun x => ?_)
    show -Real.negMulLog ((μ.rnDeriv volume x).toReal)
        = (μ.rnDeriv volume x).toReal • Real.log ((μ.rnDeriv volume x).toReal)
    simp only [smul_eq_mul, Real.negMulLog_def]
    ring
  -- `∫ llr μ ν ∂μ = ∫ log (μ.rnDeriv vol).toReal ∂μ - ∫ log (ν.rnDeriv vol).toReal ∂μ`.
  have h_split : ∫ x, llr μ ν x ∂μ
      = ∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ
        - ∫ x, Real.log ((ν.rnDeriv volume x).toReal) ∂μ := by
    rw [← integral_sub h_int_log_μ h_cross_int]
    exact integral_congr_ae h_llr_decomp
  -- assemble: `0 ≤ -h(μ) - ∫ log (ν.rnDeriv vol).toReal ∂μ` ⟹ result.
  rw [h_split, h_int_log_μ_eq] at h_kl_nn
  linarith

end InformationTheory.Shannon.EPIInfiniteVarianceTruncation
