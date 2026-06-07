/-
# 無限分散 a.c. 古典 EPI — conditioning truncation ルート (route T)

`entropyPowerExt_add_ge_infinite_variance` (`EPICase1SmoothingLimit.lean:1407`,
`@residual(wall:epi-infinite-variance-classical)`) の genuine closure を目指す moonshot
の skeleton (Phase 1)。両 a.c. + 両有限微分エントロピー + 無限分散の独立和に対する古典
entropy power inequality `Nₑ(X+Y) ≥ Nₑ(X) + Nₑ(Y)` を、有限分散 EPI 黒箱
`entropyPowerExt_add_ge_of_finite_variance` (`:1351`, sorryAx-free) を conditioning 切詰
`X_n := X | {|X|≤n ∧ |Y|≤n}` に適用して R→∞ で繋ぐルート T で構築する。

## Approach (route T, Phase 0 で確定)

`P_n := P[| {ω | |X ω| ≤ n ∧ |Y ω| ≤ n}]` (両成分同時 conditioning) は:
- compact support (両成分有界) → 有限 2 次モーメント (有限分散) + 有限微分エントロピー
- a.c. 保存 (`cond_absolutelyContinuous` + `Measure.map` の a.c. mono)
- 独立性保存 (joint 矩形事象 `X⁻¹[-n,n] ∩ Y⁻¹[-n,n]` での conditioning は `IndepFun X Y` を保つ)

ゆえに各 n で黒箱 EPI が立つ: `Nₑ(P_n.map (X+Y)) ≥ Nₑ(P_n.map X) + Nₑ(P_n.map Y)`。

最終 assembly (clean limsup chain, moment 非依存):
1. 黒箱 per n: `N(P_n.map(X+Y)) ≥ N(P_n.map X) + N(P_n.map Y)`。
2. crux usc: `N(P.map(X+Y)) ≥ limsup_n N(P_n.map(X+Y))` (Gibbs + cross-entropy DCT)。
3. RHS 収束: `N(P_n.map X) → N(P.map X)`, `N(P_n.map Y) → N(P.map Y)`。
4. 合成: `N(P.map(X+Y)) ≥ limsup N(P_n.map(X+Y)) ≥ lim[N(P_n.map X)+N(P_n.map Y)]
   = N(P.map X)+N(P.map Y)`。

crux usc は Gibbs step (`(klDiv (P_n.map(X+Y)) (P.map(X+Y))).toReal ≥ 0`、in-tree template
`differentialEntropy_le_gaussian_of_variance_le` を Gaussian → 一般参照 generalize) +
cross-entropy DCT (優関数 `p_n∗q_n ≤ C²(p∗q)`、`tendsto_integral_of_dominated_convergence`)。
分散発散は red herring (固定参照 = p∗q で moment 非依存に閉じる)。

## skeleton 注記 (Phase 1)

本 file は全 signature + `:= by sorry` の skeleton。各 `sorry` は
`@residual(plan:epi-infinite-variance-truncation-plan)` (buildable な未完成、wall でない)。
fill は別 Phase で dispatch。helper は plan §推奨分解 (1-6) に対応。

設計判断:
- **R の型**: `n : ℕ`、切詰集合 `{|X|≤n ∧ |Y|≤n}` (monotone over n、`atTop` filter で
  monotone/dominated convergence が素直、在庫 B8b と整合)。
- **conditioning API**: `ProbabilityTheory.cond P s = (P s)⁻¹ • P.restrict s`
  (`ConditionalProbability.lean:74`)。a.c. 保存は `cond_absolutelyContinuous` (`:183`)。
- **構成手段**: 素朴 indicator truncation `1_{|X|≤n}·X` は law に atom を作り a.c. を壊す
  (在庫 §E #2 隠れ難所)。conditioning で迂回。
- **Measure.conv 非使用**: 黒箱は RV 形 `P.map (fun ω => X ω + Y ω)` で動く。畳込みは
  `P_n.map (X+Y)` に暗黙に含まれ、`Measure.conv` を明示展開しない。
- **独立性保存**: 黒箱は `IndepFun X Y P_n` を要求。同時 conditioning で矩形事象ゆえ保存
  (helper `indepFun_cond_truncSet`)。
-/
import InformationTheory.Shannon.EPICase1SmoothingLimit
import InformationTheory.Shannon.EPIStamSupplyTwoTime
import InformationTheory.Shannon.EPIG2ConvEntropyMonotone

namespace InformationTheory.Shannon.EPIInfiniteVarianceTruncation

open MeasureTheory Filter Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1SmoothingLimit
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd convDensityAdd_comm)
open scoped ENNReal NNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **切詰集合** `truncSet X Y n := {ω | |X ω| ≤ n ∧ |Y ω| ≤ n}` (両成分同時切詰、
矩形事象)。`n : ℕ` で monotone increasing、`⋃ n = univ` (各 ω で `|X ω|, |Y ω|` 有限)。 -/
def truncSet (X Y : Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | |X ω| ≤ (n : ℝ) ∧ |Y ω| ≤ (n : ℝ)}

/-- 切詰集合は可測 (X, Y 可測から). -/
theorem measurableSet_truncSet {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (n : ℕ) :
    MeasurableSet (truncSet X Y n) := by
  have hXm : MeasurableSet {ω | |X ω| ≤ (n : ℝ)} :=
    measurableSet_le hX.abs measurable_const
  have hYm : MeasurableSet {ω | |Y ω| ≤ (n : ℝ)} :=
    measurableSet_le hY.abs measurable_const
  exact hXm.inter hYm

/-- 切詰集合の単調性 (`n ≤ m → truncSet X Y n ⊆ truncSet X Y m`)。 -/
theorem truncSet_mono {X Y : Ω → ℝ} : Monotone (truncSet X Y) := by
  intro n m hnm ω hω
  have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  exact ⟨hω.1.trans hnm', hω.2.trans hnm'⟩

/-- 切詰集合の和集合は全体 (`⋃ n, truncSet X Y n = univ`)。各 ω で `|X ω|, |Y ω|` が
有限ゆえ十分大きい n で含まれる (`exists_nat_ge`). -/
theorem iUnion_truncSet (X Y : Ω → ℝ) : ⋃ n, truncSet X Y n = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro ω
  obtain ⟨nX, hnX⟩ := exists_nat_ge (|X ω|)
  obtain ⟨nY, hnY⟩ := exists_nat_ge (|Y ω|)
  refine Set.mem_iUnion.2 ⟨max nX nY, ?_, ?_⟩
  · exact hnX.trans (by exact_mod_cast le_max_left nX nY)
  · exact hnY.trans (by exact_mod_cast le_max_right nX nY)

/-- **conditioning 確率測度** `P_n := P[| truncSet X Y n]`。十分大きい n で
`P (truncSet X Y n) > 0` (和集合が全体ゆえ measure → 1) なので probability measure。 -/
noncomputable def condTrunc (P : Measure Ω) (X Y : Ω → ℝ) (n : ℕ) : Measure Ω :=
  ProbabilityTheory.cond P (truncSet X Y n)

/-! ### Helper 1 — truncation 構成 + regularity (plan §推奨分解 1) -/

/-- `P (truncSet X Y n) → 1` (n→∞、和集合が全体 + `IsProbabilityMeasure`)。
ゆえに十分大きい n で `P (truncSet X Y n) ≠ 0`。 -/
theorem measure_truncSet_tendsto_one (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    Tendsto (fun n => P (truncSet X Y n)) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := P) (truncSet_mono (X := X) (Y := Y))
  rw [iUnion_truncSet X Y, measure_univ] at h
  exact h

/-- 十分大きい n では `P (truncSet X Y n) ≠ 0` (measure → 1)。
以降の per-n 補題は `n ≥ N₀` (positive mass) で立てる。 -/
theorem eventually_measure_truncSet_pos (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) :
    ∀ᶠ n in atTop, P (truncSet X Y n) ≠ 0 := by
  have h := measure_truncSet_tendsto_one P hX hY
  have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) :=
    isOpen_ne.mem_nhds one_ne_zero
  exact h.eventually_mem h_nhds

/-- `condTrunc P X Y n` は確率測度 (positive mass の n で)。 -/
theorem isProbabilityMeasure_condTrunc (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) :
    IsProbabilityMeasure (condTrunc P X Y n) := by
  unfold condTrunc
  exact ProbabilityTheory.cond_isProbabilityMeasure hpos

/-- **独立性保存**: `IndepFun X Y P` → `IndepFun X Y (condTrunc P X Y n)`。
同時 conditioning が矩形事象 `X⁻¹[-n,n] ∩ Y⁻¹[-n,n]` ゆえ独立性を保つ。
honest: 結論 `IndepFun` を仮説 `IndepFun` から導く regularity 保存補題。 -/
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

/-- **a.c. 保存**: `(P.map X) ≪ volume` → `((condTrunc P X Y n).map X) ≪ volume`。
`cond_absolutelyContinuous` (`(condTrunc) ≪ P`) + `Measure.map` の a.c. mono で合成。 -/
theorem map_condTrunc_absolutelyContinuous (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ_ac : (P.map Z) ≪ volume) {n : ℕ} :
    ((condTrunc P X Y n).map Z) ≪ volume := by
  have h_cond : condTrunc P X Y n ≪ P := ProbabilityTheory.cond_absolutelyContinuous
  exact (h_cond.map hZ).trans hZ_ac

/-- **marginal density bridge (linchpin)**: 同時 conditioning した測度 `condTrunc P X Y n`
を成分 `Z` (= X or Y) で push-forward すると、**単成分 conditioning** に帰着する:
`(condTrunc P X Y n).map Z = cond (P.map Z) {r | |r| ≤ n}`。
既証明 `indepFun_condTrunc` と同じ独立 factoring (`P(truncSet) = P(X⁻¹Sn)·P(Y⁻¹Sn)`、
他成分の mass `P(Y⁻¹Sn)` が相殺) を再利用する。
honest: 結論は測度等式、仮説は独立性 + measurability + positive mass (regularity)。 -/
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

/-- **cond density formula**: probability measure `μ` を可測集合 `s` (positive mass) で
conditioning した測度の Radon-Nikodym 微分は、indicator でカットしたものに正規化定数を
掛けた形: `(cond μ s).rnDeriv volume =ᵐ (μ s)⁻¹ · 1_s · μ.rnDeriv volume`。
`cond μ s = (μ s)⁻¹ • μ.restrict s` の scalar mul + restrict の rnDeriv で組立。 -/
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

/-! ### Helper 2 — per-n regularity 供給 (plan §推奨分解 2) -/

/-- **per-n 有限 2 次モーメント** `Integrable ((Z ·)²) (condTrunc P X Y n)`。
`condTrunc` は `truncSet ⊆ {|X|≤n ∧ |Y|≤n}` に supported → Z = X or Y は有界 (`|Z|≤n`)
→ 2 次モーメント有界。`MemLp 2` 自動 (compact support)。在庫 §D `IndepFun.variance_add`
の `MemLp 2` 前提を満たすための核。 -/
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

/-- **per-n 有限微分エントロピー (各成分)** `Integrable (negMulLog (rnDeriv ·)) volume` for
`(condTrunc P X Y n).map Z`。compact support → bounded density → integrable。
黒箱 `entropyPowerExt_add_ge_of_finite_variance` の `hX_ent`/`hY_ent` 引数を再供給。 -/
theorem integrable_negMulLog_map_condTrunc (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y)
    (hZ_ac : (P.map Z) ≪ volume)
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

/-- **density witness の withDensity 法則** (補助): a.c. probability measure `condTrunc.map Z`
の rnDeriv を toReal した実関数 `r := (rnDeriv ·).toReal` が、その measure を `withDensity`
で復元する: `(condTrunc P X Y n).map Z = volume.withDensity (ofReal ∘ r)`。
a.c. ゆえ `withDensity_rnDeriv_eq` で復元 + a.e. finite rnDeriv で `ofReal ∘ toReal = id`。 -/
theorem map_condTrunc_withDensity_toReal_rnDeriv (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {Z : Ω → ℝ} (hZ : Measurable Z)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0)
    (hZ_ac : ((condTrunc P X Y n).map Z) ≪ volume) :
    (condTrunc P X Y n).map Z
      = volume.withDensity
        (fun x => ENNReal.ofReal (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal) := by
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  haveI : IsProbabilityMeasure ((condTrunc P X Y n).map Z) :=
    Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hcongr : (fun x => ENNReal.ofReal (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal)
      =ᵐ[volume] ((condTrunc P X Y n).map Z).rnDeriv volume := by
    filter_upwards [((condTrunc P X Y n).map Z).rnDeriv_lt_top volume] with x hx
    exact ENNReal.ofReal_toReal hx.ne
  rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hZ_ac]

/-- **conv density 同定 (再利用可能)**: 独立和 `X+Y` を同時 conditioning した測度
`condTrunc P X Y n` で push-forward した法則の rnDeriv は、各成分の周辺密度
`p_n := (condTrunc.map X).rnDeriv vol |>.toReal`, `q_n := (condTrunc.map Y).rnDeriv vol |>.toReal`
の畳込み `convDensityAdd p_n q_n` に a.e. 一致する。`indepSum_density_ae`
(`EPIStamSupplyTwoTime.lean:101`、一般・sorryAx-free) を `condTrunc P X Y n` を P と読み替えて
適用。独立は `indepFun_condTrunc`、a.c. は `map_condTrunc_absolutelyContinuous`、
prob measure は `isProbabilityMeasure_condTrunc`。

honest: 結論は a.e. 測度等式、仮説は独立 + measurability + a.c. + positive mass (regularity)。
本 helper は #3 (crux usc) の優関数構成でも再利用する。 -/
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

/-- **compact support of the sum law**: `condTrunc P X Y n` は `truncSet` (両成分有界
`|X|≤n ∧ |Y|≤n`) に concentrated ゆえ、和 `X+Y` の push-forward 法則は区間
`Icc (-(2n)) (2n)` に concentrated: `(condTrunc.map(X+Y)) (Icc (-(2n)) (2n))ᶜ = 0`。 -/
theorem map_condTrunc_sum_concentrated (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) :
    ((condTrunc P X Y n).map (fun ω => X ω + Y ω))
      (Set.Icc (-(2 * (n : ℝ))) (2 * (n : ℝ)))ᶜ = 0 := by
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
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

/-- **負部 (`{r>1}` 上の `r log r`) の可積分性**: 和の密度 `r := (condTrunc.map(X+Y)).rnDeriv
vol |>.toReal` (= `p_n ∗ q_n`、convolution) の `negMulLog` の負部
`(negMulLog r)⁻ = max (-(negMulLog r)) 0 = (r log r)⁺` の `volume`-可積分性。
これが #2 の真の核 (正部は compact support + `negMulLog_le_one_sub_self` で即)。

機構: convolution `r(z) = ∫ p_n(x) q_n(z-x) dx` で `t ↦ t log t` は凸ゆえ Jensen の積分版
(`ConvexOn.map_integral_le`) で各 z 点ごとに `r(z) log r(z) ≤ ∫ p_n(x) q_n(z-x) log q_n(z-x) dx`、
Fubini (`integral_integral_swap`) で積分すると `∫ (r log r)⁺ ≤ ∫ q_n (log q_n)⁺ < ∞`
(後者は `condTrunc.map Y` の `negMulLog` 可積分 `integrable_negMulLog_map_condTrunc` Z=Y から)。

honest: 結論は可積分性 (regularity)。仮説は a.c. + measurability + positive mass。
和エントロピー可積分性 (= #2 の結論) を仮説で受けていない (非循環・非バンドル)。

park 状態 (L-IVT-4 escape、2026-06-07): #2 (`integrable_negMulLog_map_condTrunc_sum`) は
正部 (compact support `map_condTrunc_sum_concentrated` + `negMulLog_le_one_sub_self` で
`Integrable.mono'`、genuine) と本負部 lemma の honest split で完成 (`negMulLog r = g₁ - g₂`)。
本負部 lemma 単独が残課題。Jensen+Fubini ルートの素材は確認済 (`ConvexOn.map_integral_le`
on probability measure `p_n·volume`、`Real.convexOn_mul_log`、`self_sub_one_le_n` で下界、
`integral_integral_swap`、右辺有限性は `integrable_negMulLog_map_condTrunc` Z=Y) が、各 z
点の Jensen 前提 (`Integrable (q_n(z-·)) (p_n·vol)` + `Integrable (q_n(z-·)·log q_n(z-·))
(p_n·vol)` を a.e. z で) 供給 + Fubini の uncurry `Integrable (p_n x · (q_n(z-x)·log q_n(z-x)))
(vol.prod vol)` 供給が当該セッション規模 (100+ 行) を超えたため park。仮説束化での sorry 回避は
していない (signature は本来の可積分性結論のまま)。 -/
theorem integrable_negPart_negMulLog_map_condTrunc_sum (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    Integrable
      (fun x => max (-(Real.negMulLog
        (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) 0) volume := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **per-n 和の有限微分エントロピー** (`hent_sum` 再供給)。compact support の和 X+Y の
密度 `r := (condTrunc.map(X+Y)).rnDeriv vol |>.toReal` (= `p_n ∗ q_n`、support [-2n,2n]) の
`negMulLog` 可積分性を正部/負部分解で。正部 `{r≤1}` は `negMulLog_le_one_sub_self` + `r` 可積分
(probability measure の toReal rnDeriv)、負部 `{r>1}` は `h(condTrunc.map(X+Y)) ≥ h(condTrunc.map X)
> -∞` から。黒箱 `entropyPowerExt_add_ge_of_finite_variance` は `hent_sum` を明示引数で要求。 -/
theorem integrable_negMulLog_map_condTrunc_sum (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P)
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
    integrable_negPart_negMulLog_map_condTrunc_sum P hX hY hX_ac hY_ac hXY hpos
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

/-! ### Helper 黒箱配線 — per-n EPI -/

/-- **per-n 有限分散 EPI** (黒箱 `entropyPowerExt_add_ge_of_finite_variance` への配線)。
helper 1/2 で全 regularity を供給し、各 n (positive mass) で
`Nₑ(P_n.map(X+Y)) ≥ Nₑ(P_n.map X) + Nₑ(P_n.map Y)` を得る。 -/
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
    (integrable_negMulLog_map_condTrunc_sum P hX hY hX_ac hY_ac hXY hpos)

/-! ### Helper 3 — 優関数 + generalized Gibbs (plan §推奨分解 3) -/

/-- **generalized Gibbs (cross-entropy 下界)**: a.c. な `μ ≪ ν` (ともに probability) で
`differentialEntropy μ ≤ -∫ x, log (ν.rnDeriv volume x).toReal ∂μ` (cross-entropy)。
`(klDiv μ ν).toReal ≥ 0` (klDiv は ℝ≥0∞ 値、`ENNReal.toReal_nonneg` で型自明) +
`toReal_klDiv_of_measure_eq` の llr 分解から。in-tree template
`differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520`) の
Gaussian 参照 ν を一般参照に generalize した版。 -/
theorem differentialEntropy_le_cross_entropy {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ_ac : μ ≪ volume) (hν_ac : ν ≪ volume) (hμν : μ ≪ ν)
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

/-! ### Helper 4 — crux usc (plan §推奨分解 4, genuine sub-wall 候補) -/

/-- **crux usc (微分エントロピー版)**: `limsup_n h(P_n.map(X+Y)) ≤ h(P.map(X+Y))`。
Gibbs step (`differentialEntropy_le_cross_entropy` で h(P_n.map(X+Y)) を cross-entropy
`-∫(p_n∗q_n)log(p∗q)` で上から抑える) + cross-entropy DCT (優関数 `C²(p∗q)|log(p∗q)|`、
和の有限微分エントロピーで可積分、`tendsto_integral_of_dominated_convergence` で
`→ -∫(p∗q)log(p∗q) = h(p∗q)`)。本 moonshot の核。 -/
theorem differentialEntropy_condTrunc_sum_limsup_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    Filter.limsup
      (fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop
      ≤ differentialEntropy (P.map (fun ω => X ω + Y ω)) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **crux usc (entropyPower 版)**: `limsup_n Nₑ(P_n.map(X+Y)) ≤ Nₑ(P.map(X+Y))`。
微分エントロピー版 (`differentialEntropy_condTrunc_sum_limsup_le`) を `entropyPowerExt`
= `exp (2·h)` の単調連続変換で lift。 -/
theorem entropyPowerExt_condTrunc_sum_limsup_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    Filter.limsup
      (fun n => entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop
      ≤ entropyPowerExt (P.map (fun ω => X ω + Y ω)) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-! ### Helper 5 — RHS 収束 (plan §推奨分解 5) -/

/-- **RHS 収束 (微分エントロピー版)**: `h(P_n.map Z) → h(P.map Z)` (各成分)。
恒等式 `-∫ p_n log p_n = -(1/m_n)∫_{truncSet} p log p + log m_n`、第 1 項は固定可積分
`p log p` の growing-set monotone/dominated convergence、第 2 項は `m_n → 1` → `log m_n → 0`。
moment 非依存 (固定可積分関数 `p log p` のみ)。 -/
theorem differentialEntropy_map_condTrunc_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ_ac : (P.map Z) ≪ volume)
    (hZ_ent : Integrable (fun x => Real.negMulLog ((P.map Z).rnDeriv volume x).toReal) volume) :
    Tendsto (fun n => differentialEntropy ((condTrunc P X Y n).map Z)) atTop
      (𝓝 (differentialEntropy (P.map Z))) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **RHS 収束 (entropyPower 版)**: `Nₑ(P_n.map Z) → Nₑ(P.map Z)`。
微分エントロピー版を `entropyPowerExt = exp (2·h)` の連続変換で lift。 -/
theorem entropyPowerExt_map_condTrunc_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ_ac : (P.map Z) ≪ volume)
    (hZ_ent : Integrable (fun x => Real.negMulLog ((P.map Z).rnDeriv volume x).toReal) volume) :
    Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map Z)) atTop
      (𝓝 (entropyPowerExt (P.map Z))) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-! ### Helper 6 — headline 法則版 + assembly (plan §推奨分解 6, Phase 4) -/

/-- **headline (法則版)**: 無限分散 a.c. 古典 EPI。
per-n 黒箱 EPI (`entropyPowerExt_condTrunc_add_ge`) + crux usc
(`entropyPowerExt_condTrunc_sum_limsup_le`) + RHS 収束
(`entropyPowerExt_map_condTrunc_tendsto` ×2) を R→∞ で合成:
`N(X)+N(Y) = lim RHS_n ≤ limsup LHS_n ≤ N(X+Y)`。

⚠ 本版は和の有限微分エントロピー `hent_sum` を crux usc に渡すため明示引数で受ける
(wall theorem 側 signature には無い)。assembly で wall body から供給する設計
(compact support 経由 or 別途確立)。`hent_sum` は regularity precondition (有限微分
エントロピー)、結論を encode しない load-bearing でない。

独立 honesty audit 2026-06-07 (skeleton 段階、signature honesty + classification):
`hent_sum` は load-bearing でなく regularity precondition と確認 (core-reconstruction:
和エントロピー=+∞ なら Nₑ(P.map(X+Y))=⊤ で EPI 自明ゆえ、`hent_sum`=有限 は route T 適用
領域を切り出す前提であって EPI 不等式を encode しない)。⚠Phase 4 接続課題: wall theorem
`:1407` の仮説は global `hX_ent`/`hY_ent` (各成分) で `hent_sum` (和) を持たないため、
assembly では `hent_sum` を各成分の有限 entropy + a.c. から **genuine 導出** する必要がある
(両成分有限 entropy ⊬ 和有限 entropy は自明でない)。この導出が詰まっても `hent_sum` を
wall theorem の新規仮説に**昇格させない** (= signature load-bearing 化、tier 5)。詰まる
場合は当該導出補題に `sorry` + `@residual` で park。 -/
theorem entropyPowerExt_add_ge_infinite_variance_truncation
    (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

end InformationTheory.Shannon.EPIInfiniteVarianceTruncation
