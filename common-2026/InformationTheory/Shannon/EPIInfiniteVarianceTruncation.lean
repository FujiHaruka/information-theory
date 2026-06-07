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
honest: 結論は測度等式、仮説は独立性 + measurability + positive mass (regularity)。
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

/-- **cond density formula**: probability measure `μ` を可測集合 `s` (positive mass) で
conditioning した測度の Radon-Nikodym 微分は、indicator でカットしたものに正規化定数を
掛けた形: `(cond μ s).rnDeriv volume =ᵐ (μ s)⁻¹ · 1_s · μ.rnDeriv volume`。
`cond μ s = (μ s)⁻¹ • μ.restrict s` の scalar mul + restrict の rnDeriv で組立。
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
黒箱 `entropyPowerExt_add_ge_of_finite_variance` の `hX_ent`/`hY_ent` 引数を再供給。
honest: `hZ_ent` (= `P.map Z` のエントロピー可積分) は上流 regularity precondition、
別測度 `condTrunc.map Z = cond (P.map Z) Sn` のエントロピー可積分を cond density formula
経由で genuine 導出 (結論を encode しない load-bearing でない、sorryAx-free)。
@audit:ok -/
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
a.c. ゆえ `withDensity_rnDeriv_eq` で復元 + a.e. finite rnDeriv で `ofReal ∘ toReal = id`。
@audit:ok -/
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
本 helper は #3 (crux usc) の優関数構成でも再利用する。
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

/-- **compact support of the sum law**: `condTrunc P X Y n` は `truncSet` (両成分有界
`|X|≤n ∧ |Y|≤n`) に concentrated ゆえ、和 `X+Y` の push-forward 法則は区間
`Icc (-(2n)) (2n)` に concentrated: `(condTrunc.map(X+Y)) (Icc (-(2n)) (2n))ᶜ = 0`。
@audit:ok -/
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
していない (signature は本来の可積分性結論のまま)。

独立 honesty audit 2026-06-07: honest_residual 確認。(1) 非循環: 結論は和密度 negMulLog の
負部可積分性、仮説は `hX_ac`/`hY_ac` (各成分 a.c.) + `hXY` (独立) + `hpos` (positive mass) のみ
= regularity precondition、結論型 ≢ 仮説型。(2) 非バンドル: 和エントロピー可積分性 (= 結論) を
仮説で受けていない。(3) classification: `plan:epi-infinite-variance-truncation-plan` の plan 実在
(docs/shannon/、19KB) + closure 素材 `ConvexOn.map_integral_le` / `MeasureTheory.integral_integral_swap`
は Mathlib 既存 (loogle 確認) ゆえ wall でなく plan 分類が妥当 (buildable)、右辺有限性は
`integrable_negMulLog_map_condTrunc` (Z=Y, sorryAx-free) が供給可。
@residual(plan:epi-infinite-variance-truncation-plan) -/
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
> -∞` から。黒箱 `entropyPowerExt_add_ge_of_finite_variance` は `hent_sum` を明示引数で要求。

独立 honesty audit 2026-06-07: body genuine。(1) signature に和エントロピー仮説 sneak なし
= `hX_ac`/`hY_ac`/`hXY`/`hpos` のみ (= 結論である和エントロピー可積分性を仮説で受けていない、
循環/load-bearing でない、最重要チェック PASS)。(2) body は正部 `g₁` を compact support
(`map_condTrunc_sum_concentrated`) + `negMulLog_le_one_sub_self` で genuine 構成 + 負部 `g₂` を
#7 `integrable_negPart_negMulLog_map_condTrunc_sum` に委譲 + `negMulLog r = g₁ - g₂` split。
(3) `#print axioms` = transitive sorry は #7 由来 1 本のみ (body 自体の独自 sorry なし)。
honest_residual (transitive: #7 の plan).
@residual(plan:epi-infinite-variance-truncation-plan) -/
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
`Nₑ(P_n.map(X+Y)) ≥ Nₑ(P_n.map X) + Nₑ(P_n.map Y)` を得る。

独立 honesty audit 2026-06-07: body は黒箱への genuine 配線 (黒箱が要求する 8 regularity 引数
= indep/a.c.×2/2次モーメント×2/各成分 entropy×2/和 entropy をすべて helper 1/2 で供給)。
signature の `hX_ent`/`hY_ent` は黒箱の各成分有限エントロピー precondition を `condTrunc.map` 側に
再供給するための regularity precondition (`integrable_negMulLog_map_condTrunc` 経由)、結論 (per-n EPI
不等式) を encode しない load-bearing でない。transitive sorry は #8→#7 由来 1 本のみ (body 独自
sorry なし)。honest_residual (transitive: #7 の plan).
@residual(plan:epi-infinite-variance-truncation-plan) -/
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
Gaussian 参照 ν を一般参照に generalize した版。
@audit:ok -/
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

/-! ### Helper 3' — P 版 conv density 同定 + crux usc の解析核 sub-helper -/

/-- **P 版 conv density 同定**: `(P.map(X+Y)).rnDeriv =ᵐ ofReal (convDensityAdd pX pY)`
(`pX := (P.map X).rnDeriv vol |>.toReal`, `pY := (P.map Y).rnDeriv vol |>.toReal`)。
`rnDeriv_map_condTrunc_sum_ae` の `condTrunc P X Y n` を `P` に読み替えた版。
`indepSum_density_ae` を `P` 自体に適用。
honest: 結論は a.e. 測度等式、仮説は独立 + measurability + a.c. (regularity)。
@audit:ok -/
theorem rnDeriv_map_sum_ae (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P) :
    (P.map (fun ω => X ω + Y ω)).rnDeriv volume
      =ᵐ[volume] fun x => ENNReal.ofReal
        (convDensityAdd (fun y => (P.map X).rnDeriv volume y |>.toReal)
          (fun y => (P.map Y).rnDeriv volume y |>.toReal) x) := by
  -- a.c. of the sum law.
  have hXYac : (P.map (fun ω => X ω + Y ω)) ≪ volume := by
    have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
      rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
    rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac
  -- density witnesses.
  set pX : ℝ → ℝ := fun y => (P.map X).rnDeriv volume y |>.toReal with hpX
  set pY : ℝ → ℝ := fun y => (P.map Y).rnDeriv volume y |>.toReal with hpY
  set pXY : ℝ → ℝ := fun y => (P.map (fun ω => X ω + Y ω)).rnDeriv volume y |>.toReal with hpXY
  have hpX_meas : Measurable pX := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpY_meas : Measurable pY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpXY_meas : Measurable pXY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x => ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x => ENNReal.toReal_nonneg
  have hpXY_nn : ∀ x, 0 ≤ pXY x := fun x => ENNReal.toReal_nonneg
  -- withDensity laws (a.c. probability ⇒ recovered by `withDensity_rnDeriv_eq`).
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  haveI : IsProbabilityMeasure (P.map (fun ω => X ω + Y ω)) :=
    Measure.isProbabilityMeasure_map (hX.add hY).aemeasurable
  have mk_law : ∀ (W : Ω → ℝ) (pW : ℝ → ℝ), Measurable W → (P.map W) ≪ volume
      → pW = (fun y => (P.map W).rnDeriv volume y |>.toReal)
      → P.map W = volume.withDensity (fun x => ENNReal.ofReal (pW x)) := by
    intro W pW hWmeas hWac hpW_eq
    haveI : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hWmeas.aemeasurable
    have hcongr : (fun x => ENNReal.ofReal (pW x))
        =ᵐ[volume] (P.map W).rnDeriv volume := by
      filter_upwards [(P.map W).rnDeriv_lt_top volume] with x hx
      rw [hpW_eq]; exact ENNReal.ofReal_toReal hx.ne
    rw [withDensity_congr_ae hcongr, Measure.withDensity_rnDeriv_eq _ _ hWac]
  have hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)) :=
    mk_law X pX hX hX_ac hpX
  have hpY_law : P.map Y = volume.withDensity (fun x => ENNReal.ofReal (pY x)) :=
    mk_law Y pY hY hY_ac hpY
  have hpXY_law : P.map (fun ω => X ω + Y ω)
      = volume.withDensity (fun x => ENNReal.ofReal (pXY x)) :=
    mk_law (fun ω => X ω + Y ω) pXY (hX.add hY) hXYac hpXY
  have hpX_int : Integrable pX volume := Measure.integrable_toReal_rnDeriv
  have hpY_int : Integrable pY volume := Measure.integrable_toReal_rnDeriv
  -- lmasses.
  have hlmass : ∀ (W : Ω → ℝ) (pW : ℝ → ℝ),
      P.map W = volume.withDensity (fun x => ENNReal.ofReal (pW x))
      → (∫⁻ x, ENNReal.ofReal (pW x) ∂volume) = (P.map W) Set.univ := by
    intro W pW hlaw
    rw [hlaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hpX_lmass : (∫⁻ x, ENNReal.ofReal (pX x) ∂volume) = 1 := by
    rw [hlmass X pX hpX_law]; exact measure_univ
  have hpY_lmass : (∫⁻ x, ENNReal.ofReal (pY x) ∂volume) = 1 := by
    rw [hlmass Y pY hpY_law]; exact measure_univ
  have hpXY_lmass : (∫⁻ x, ENNReal.ofReal (pXY x) ∂volume) ≠ ⊤ := by
    rw [hlmass (fun ω => X ω + Y ω) pXY hpXY_law]; exact measure_ne_top _ _
  have hkey : pXY =ᵐ[volume] convDensityAdd pX pY :=
    EPIStamSupplyTwoTime.indepSum_density_ae (P := P) X Y hX hY hXY
      pX pY pXY hpX_nn hpX_meas hpY_nn hpY_meas hpX_law hpY_law hpXY_law
      hpXY_nn hpXY_meas hpX_int hpY_int hpXY_lmass hpX_lmass hpY_lmass
  have hrn_ofReal : (P.map (fun ω => X ω + Y ω)).rnDeriv volume
      =ᵐ[volume] fun x => ENNReal.ofReal (pXY x) := by
    filter_upwards [(P.map (fun ω => X ω + Y ω)).rnDeriv_lt_top volume] with x hx
    exact (ENNReal.ofReal_toReal hx.ne).symm
  filter_upwards [hrn_ofReal, hkey] with x hx hkx
  rw [hx, hkx]

/-- **marginal mass の正値性 (factoring)**: `P (truncSet X Y n) ≠ 0` → 各成分の周辺
mass `(P.map Z) {r | |r| ≤ n} ≠ 0` (Z = X or Y)。独立 factoring
`P(truncSet) = P(X⁻¹Sn)·P(Y⁻¹Sn)` の片側因子が `(P.map Z) Sn` に一致。

独立 honesty audit 2026-06-07 PASS: 結論 = 周辺 mass 非零、仮説 = `IndepFun`/measurability/
positive mass (regularity precondition)、結論型 ≢ 仮説型 (非循環)。core bundle なし (非バンドル)。
sufficiency: 独立 factoring `measure_inter_preimage_eq_mul` で `P(truncSet)=P(X⁻¹Sn)·P(Y⁻¹Sn)`、
片因子=0 なら積=0 で `hpos` と矛盾 → genuine follow。`#print axioms` sorryAx-free。@audit:ok -/
theorem map_measure_truncBall_ne_zero (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y) {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    (P.map Z) {r : ℝ | |r| ≤ (n : ℝ)} ≠ 0 := by
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn :=
    measurableSet_le measurable_norm measurable_const
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  rw [Measure.map_apply hZmeas hSn_meas]
  have hfac : P (truncSet X Y n) = P (X ⁻¹' Sn) * P (Y ⁻¹' Sn) := by
    show P (X ⁻¹' Sn ∩ Y ⁻¹' Sn) = _
    exact hXY.measure_inter_preimage_eq_mul Sn Sn hSn_meas hSn_meas
  rcases hZ with rfl | rfl
  · intro h0; apply hpos; rw [hfac, h0, zero_mul]
  · intro h0; apply hpos; rw [hfac, h0, mul_zero]

/-- **per-n 周辺密度の優関数 (single component)**: 固定 `n₀` (positive mass) に対し、
`n₀ ≤ n` (ゆえ positive mass) で cond 周辺密度 `p_n := (condTrunc.map Z).rnDeriv vol |>.toReal`
が定数倍 `C_Z · pZ` で上から抑えられる (`pZ := (P.map Z).rnDeriv vol |>.toReal`,
`C_Z := ((P.map Z) {|r|≤n₀})⁻¹.toReal`)。機構: `map_condTrunc_eq_cond_map` で単成分
conditioning に帰着 → `rnDeriv_cond_eq` で `p_n =ᵐ (m_n)⁻¹ · 1_Sn · pZ`、indicator + m_n 単調性
(`Sn₀ ⊆ Sn` → `m_n ≥ m_{n₀}` → `m_n⁻¹ ≤ m_{n₀}⁻¹ = C_Z`) で上界。

独立 honesty audit 2026-06-07 PASS: 結論 = 周辺密度の優関数不等式 (a.e.)、仮説 = `IndepFun`/
measurability/`n₀≤n`/positive mass `hpos₀` (regularity precondition)、結論型 ≢ 仮説型 (非循環)。
core bundle なし (非バンドル)。sufficiency: cond density formula で `p_n =ᵐ m⁻¹·1_Sn·pZ`、
`m₀≤m` (`Sn₀⊆Sn`, `measure_mono`) → `m⁻¹≤m₀⁻¹` → `(m⁻¹).toReal≤(m₀⁻¹).toReal`、
indicator 両 case (x∈Sn: m⁻¹·pZ ≤ C_Z·pZ / x∉Sn: 0 ≤ C_Z·pZ) で follow。`m₀≠0` (positive mass)
ゆえ `m₀⁻¹≠∞` (退化境界悪用なし)。`#print axioms` sorryAx-free。@audit:ok -/
theorem condTrunc_marginal_density_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y) {n₀ n : ℕ} (hn : n₀ ≤ n)
    (hpos₀ : P (truncSet X Y n₀) ≠ 0) :
    ∀ᵐ x ∂volume,
      (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal
        ≤ (((P.map Z) {r : ℝ | |r| ≤ (n₀ : ℝ)})⁻¹).toReal
          * ((P.map Z).rnDeriv volume x).toReal := by
  classical
  set Sn₀ : Set ℝ := {r : ℝ | |r| ≤ (n₀ : ℝ)} with hSn₀_def
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn₀_meas : MeasurableSet Sn₀ := measurableSet_le measurable_norm measurable_const
  have hSn_meas : MeasurableSet Sn := measurableSet_le measurable_norm measurable_const
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  haveI : IsProbabilityMeasure (P.map Z) :=
    Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  -- positive mass at level `n₀` and `n` (the latter by monotone `Sn₀ ⊆ Sn`).
  have hpos_n : P (truncSet X Y n) ≠ 0 := by
    intro h0; exact hpos₀ (measure_mono_null (truncSet_mono hn) h0)
  have hm₀_ne : (P.map Z) Sn₀ ≠ 0 := map_measure_truncBall_ne_zero P hX hY hXY hZ hpos₀
  have hm_ne : (P.map Z) Sn ≠ 0 := map_measure_truncBall_ne_zero P hX hY hXY hZ hpos_n
  set m₀ : ℝ≥0∞ := (P.map Z) Sn₀ with hm₀_def
  set m : ℝ≥0∞ := (P.map Z) Sn with hm_def
  have hm₀_top : m₀ ≠ ∞ := measure_ne_top _ _
  -- `m₀ ≤ m` (Sn₀ ⊆ Sn), hence `m⁻¹ ≤ m₀⁻¹`, hence `(m⁻¹).toReal ≤ (m₀⁻¹).toReal`.
  have hSn₀_sub : Sn₀ ⊆ Sn := by
    intro r hr
    have hnn : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact le_trans hr hnn
  have hm_le : m₀ ≤ m := measure_mono hSn₀_sub
  have hinv_le : m⁻¹ ≤ m₀⁻¹ := ENNReal.inv_le_inv.mpr hm_le
  have hC_bound : (m⁻¹).toReal ≤ (m₀⁻¹).toReal :=
    ENNReal.toReal_mono (ENNReal.inv_ne_top.mpr hm₀_ne) hinv_le
  -- cond density formula: `(condTrunc.map Z).rnDeriv =ᵐ (cond (P.map Z) Sn).rnDeriv`.
  rw [map_condTrunc_eq_cond_map P hX hY hXY hZ hpos_n]
  have h_rn : (ProbabilityTheory.cond (P.map Z) Sn).rnDeriv volume
      =ᵐ[volume] fun x => m⁻¹ * Sn.indicator ((P.map Z).rnDeriv volume) x :=
    rnDeriv_cond_eq (P.map Z) hSn_meas hm_ne
  filter_upwards [h_rn] with x hx
  rw [hx]
  set pZx : ℝ := ((P.map Z).rnDeriv volume x).toReal with hpZx_def
  have hpZx_nn : 0 ≤ pZx := ENNReal.toReal_nonneg
  by_cases hxs : x ∈ Sn
  · rw [Set.indicator_of_mem hxs (f := (P.map Z).rnDeriv volume), ENNReal.toReal_mul]
    -- `(m⁻¹).toReal * pZx ≤ (m₀⁻¹).toReal * pZx`.
    exact mul_le_mul_of_nonneg_right hC_bound hpZx_nn
  · rw [Set.indicator_of_notMem hxs (f := (P.map Z).rnDeriv volume), mul_zero,
      ENNReal.toReal_zero]
    exact mul_nonneg ENNReal.toReal_nonneg hpZx_nn

/-- **sub-helper A — 優関数 `p_n∗q_n ≤ C·(p∗q)`** (pointwise a.e. `z`、`C = C_X·C_Y`)。
固定 `n₀` (positive mass) に対し、`n ≥ n₀` で各成分の cond 密度
`p_n := (condTrunc.map X).rnDeriv vol |>.toReal` が `C_X · pX` で上から抑えられ
(`m_{X,n}⁻¹` の単調性、`C_X := (m_{X,n₀})⁻¹.toReal`)、同様に `q_n ≤ C_Y · qY`。convolution
単調性で `p_n∗q_n ≤ C_X·C_Y·(pX∗qY)`。`C := C_X·C_Y`。

**Genuine fill (2026-06-07, sorryAx-free)**: Step 1 各成分優関数 = helper
`condTrunc_marginal_density_le` (`map_condTrunc_eq_cond_map` で単成分 conditioning に帰着
→ `rnDeriv_cond_eq` の indicator 形 + `m_n` 単調性 `measure_mono`/`ENNReal.inv_le_inv`)。
Step 2 各 z の畳込み単調性 = `integral_mono_of_nonneg` (LHS 可積分不要、RHS 可積分のみ)。
per-z RHS 可積分性 (`∀ᵐ z, Integrable (x ↦ pX x · pY (z−x))`) は 2D 可積分性
`integrable_prod_iff'` (layout `f (z,x) = pX x · pY (z−x)`、`convKernel_envelope_integrable`
`FisherInfoV2DeBruijnAssembly.lean:791` を転用) + `Integrable.prod_right_ae` で genuine 供給
(park 不要、session 内に閉じた)。Y 成分 bound の `q_n(z−x) ≤ C_Y qY(z−x)` への変換は
測度保存写像 `x ↦ z − x` (`Measure.measurePreserving_sub_left`) の
`QuasiMeasurePreserving.ae` で transport。

honest: 結論は優関数不等式 (a.e. pointwise bound)。仮説は a.c. + measurability + positive mass。
和エントロピー可積分性 (結論) を仮説で受けていない。

独立 honesty audit 2026-06-07 PASS (fresh auditor、self-audit 不可ゆえ独立判定): genuine fill
proof-done。(1) 非循環: 結論は `∃ C, p_n∗q_n ≤ C·(p∗q)` (優関数不等式)、仮説は
`hX_ac`/`hY_ac`/`hXY`/`hpos₀` (= regularity precondition)、結論型 ≢ 仮説型。
(2) 非バンドル: usc 不等式や和エントロピー可積分性 (= 親 route T 結論) を仮説で受けていない。
依存 helper (`condTrunc_marginal_density_le`/`map_condTrunc_eq_cond_map`/`rnDeriv_cond_eq`) も
core を bundle しない genuine 補題。(3) sufficiency: 「各成分 bound `p_n ≤ C_Z·pZ` (m_n⁻¹ 単調)
+ 各 z の畳込み単調性 (`integral_mono_of_nonneg`)」から優関数不等式が follow。`C = C_X·C_Y`
は `hpos₀` (positive mass `m₀≠0`) ゆえ `m₀⁻¹≠∞` → finite positive (退化境界悪用なし、
`(∞).toReal=0` の degenerate に落ちない)。(4) `#print axioms` = `[propext, Classical.choice,
Quot.sound]` (sorryAx-free、body 独自 sorry 0、機械確認)。0 sorry / 0 residual = proof done。
@audit:ok -/
theorem convDensity_condTrunc_le_const_mul (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) {n₀ : ℕ}
    (hpos₀ : P (truncSet X Y n₀) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ᵐ z ∂volume,
      convDensityAdd (fun y => ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal)
        (fun y => ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal) z
        ≤ C * convDensityAdd (fun y => (P.map X).rnDeriv volume y |>.toReal)
            (fun y => (P.map Y).rnDeriv volume y |>.toReal) z := by
  classical
  -- marginal densities of `P` (probability measures, a.c. ⇒ integrable toReal rnDeriv).
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  set pX : ℝ → ℝ := fun y => ((P.map X).rnDeriv volume y).toReal with hpX_def
  set pY : ℝ → ℝ := fun y => ((P.map Y).rnDeriv volume y).toReal with hpY_def
  have hpX_meas : Measurable pX := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpY_meas : Measurable pY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x => ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x => ENNReal.toReal_nonneg
  have hpX_int : Integrable pX volume := Measure.integrable_toReal_rnDeriv
  have hpY_int : Integrable pY volume := Measure.integrable_toReal_rnDeriv
  -- constants.
  set C_X : ℝ := (((P.map X) {r : ℝ | |r| ≤ (n₀ : ℝ)})⁻¹).toReal with hCX_def
  set C_Y : ℝ := (((P.map Y) {r : ℝ | |r| ≤ (n₀ : ℝ)})⁻¹).toReal with hCY_def
  have hCX_nn : 0 ≤ C_X := ENNReal.toReal_nonneg
  have hCY_nn : 0 ≤ C_Y := ENNReal.toReal_nonneg
  refine ⟨C_X * C_Y, mul_nonneg hCX_nn hCY_nn, ?_⟩
  -- Step 2 prerequisite: for a.e. `z`, the convolution slice `x ↦ pX x · pY (z - x)`
  -- is integrable. Established via 2D integrability + `Integrable.prod_right_ae`.
  -- Layout: `f (z, x) = pX x · pY (z - x)` (first coord `z`, second coord `x`). This is the
  -- `convKernel_envelope_integrable` shape (`FisherInfoV2DeBruijnAssembly.lean:791`) with
  -- `K = pY` and the kernel-density being `pX`.
  have hslice_int : ∀ᵐ z ∂volume, Integrable (fun x => pX x * pY (z - x)) volume := by
    -- the 2D integrand `f (z, x) = pX x · pY (z - x)`.
    set f : ℝ × ℝ → ℝ := fun p => pX p.2 * pY (p.1 - p.2) with hf_def
    have hf_meas : AEStronglyMeasurable f (volume.prod volume) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => pX p.2) (volume.prod volume) :=
        (hpX_meas.comp measurable_snd).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => pY (p.1 - p.2)) (volume.prod volume) := by
        have hsub : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := measurable_fst.sub measurable_snd
        exact (hpY_meas.comp hsub).aestronglyMeasurable
      exact h1.mul h2
    have hf_int : Integrable f (volume.prod volume) := by
      rw [integrable_prod_iff' hf_meas]
      refine ⟨?_, ?_⟩
      · -- for each `x`, `z ↦ pX x · pY (z − x)` is integrable (`pX x` constant).
        refine Filter.Eventually.of_forall (fun x => ?_)
        exact (hpY_int.comp_sub_right x).const_mul (pX x)
      · -- `x ↦ ∫ z ‖pX x · pY(z−x)‖ dz = ‖pX x‖ · (∫‖pY‖)` is integrable.
        have heq : (fun x => ∫ z, ‖f (z, x)‖ ∂volume)
            = (fun x => ‖pX x‖ * ∫ z, ‖pY z‖ ∂volume) := by
          funext x
          simp only [hf_def, norm_mul]
          rw [integral_const_mul]
          congr 1
          rw [← integral_sub_right_eq_self (fun z => ‖pY z‖) x]
        rw [heq]
        exact (hpX_int.norm.mul_const _)
    -- slice over the second coord `x` for fixed first `z`.
    exact hf_int.prod_right_ae
  -- the eventual filter: `n ≥ n₀` (positive mass automatic by monotonicity).
  rw [Filter.eventually_atTop]
  refine ⟨n₀, fun n hn => ?_⟩
  -- per-component density bounds (a.e. `x`).
  have hbX : ∀ᵐ x ∂volume,
      (((condTrunc P X Y n).map X).rnDeriv volume x).toReal ≤ C_X * pX x :=
    condTrunc_marginal_density_le P hX hY hXY (Or.inl rfl) hn hpos₀
  have hbY : ∀ᵐ y ∂volume,
      (((condTrunc P X Y n).map Y).rnDeriv volume y).toReal ≤ C_Y * pY y :=
    condTrunc_marginal_density_le P hX hY hXY (Or.inr rfl) hn hpos₀
  -- abbreviations for the conditioned marginal densities.
  set pnX : ℝ → ℝ := fun y => (((condTrunc P X Y n).map X).rnDeriv volume y).toReal with hpnX_def
  set pnY : ℝ → ℝ := fun y => (((condTrunc P X Y n).map Y).rnDeriv volume y).toReal with hpnY_def
  have hpnX_nn : ∀ x, 0 ≤ pnX x := fun x => ENNReal.toReal_nonneg
  have hpnY_nn : ∀ x, 0 ≤ pnY x := fun x => ENNReal.toReal_nonneg
  -- combine slice integrability + transported `Y` bound over a.e. `z`.
  filter_upwards [hslice_int] with z hz_int
  -- transport the `Y` bound through the measure-preserving map `x ↦ z - x`.
  have hbY_z : ∀ᵐ x ∂volume, pnY (z - x) ≤ C_Y * pY (z - x) :=
    (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving.ae hbY
  -- the integrand bound `pnX x · pnY (z−x) ≤ (C_X·C_Y)·(pX x · pY (z−x))` a.e. `x`.
  have hfg : (fun x => pnX x * pnY (z - x))
      ≤ᵐ[volume] fun x => (C_X * C_Y) * (pX x * pY (z - x)) := by
    filter_upwards [hbX, hbY_z] with x hxX hxY
    have h1 : pnX x * pnY (z - x) ≤ (C_X * pX x) * (C_Y * pY (z - x)) :=
      mul_le_mul hxX hxY (hpnY_nn (z - x)) (le_trans (hpnX_nn x) hxX)
    calc pnX x * pnY (z - x)
        ≤ (C_X * pX x) * (C_Y * pY (z - x)) := h1
      _ = (C_X * C_Y) * (pX x * pY (z - x)) := by ring
  -- nonnegativity of the LHS integrand.
  have hf_nn : (0 : ℝ → ℝ) ≤ᵐ[volume] fun x => pnX x * pnY (z - x) :=
    Filter.Eventually.of_forall (fun x => mul_nonneg (hpnX_nn x) (hpnY_nn (z - x)))
  -- integrability of the RHS integrand.
  have hgi : Integrable (fun x => (C_X * C_Y) * (pX x * pY (z - x))) volume :=
    hz_int.const_mul (C_X * C_Y)
  -- integral monotonicity, then pull out the constant.
  have hmono : (∫ x, pnX x * pnY (z - x) ∂volume)
      ≤ ∫ x, (C_X * C_Y) * (pX x * pY (z - x)) ∂volume :=
    integral_mono_of_nonneg hf_nn hgi hfg
  rw [integral_const_mul] at hmono
  -- rewrite both sides as `convDensityAdd`.
  show convDensityAdd pnX pnY z ≤ (C_X * C_Y) * convDensityAdd pX pY z
  simpa only [convDensityAdd] using hmono

/-- **fixed-`n` 版 sub-helper A**: 単一 `n` (positive mass `hpos`) で優関数
`convDensityAdd pnX pnY ≤ C · convDensityAdd pX pY` (a.e. `z`)。A 本体
`convDensity_condTrunc_le_const_mul` の `n₀ := n`・`n = n` 特殊化を、`atTop` の eventually
wrapper を介さず単一 `n` で直接供給する (各成分 bound `condTrunc_marginal_density_le` を
`hn = le_refl n` で呼び、A の Step 2 畳込み単調性 `integral_mono_of_nonneg` を再利用)。
C'/D は固定 `n` でこの bound を要求するため、本 helper で eventually 抽出の閾値依存を回避する。
honest: 結論は優関数不等式 (a.e. bound)、仮説は a.c. + measurability + positive mass
(regularity precondition)。和エントロピー可積分性 (= 親結論) を仮説で受けていない。
@audit:ok -/
theorem convDensityAdd_condTrunc_le_const_mul_at (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) {n : ℕ}
    (hpos : P (truncSet X Y n) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ z ∂volume,
      convDensityAdd (fun y => ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal)
        (fun y => ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal) z
        ≤ C * convDensityAdd (fun y => (P.map X).rnDeriv volume y |>.toReal)
            (fun y => (P.map Y).rnDeriv volume y |>.toReal) z := by
  classical
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  set pX : ℝ → ℝ := fun y => ((P.map X).rnDeriv volume y).toReal with hpX_def
  set pY : ℝ → ℝ := fun y => ((P.map Y).rnDeriv volume y).toReal with hpY_def
  have hpX_meas : Measurable pX := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpY_meas : Measurable pY := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x => ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x => ENNReal.toReal_nonneg
  have hpX_int : Integrable pX volume := Measure.integrable_toReal_rnDeriv
  have hpY_int : Integrable pY volume := Measure.integrable_toReal_rnDeriv
  set C_X : ℝ := (((P.map X) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal with hCX_def
  set C_Y : ℝ := (((P.map Y) {r : ℝ | |r| ≤ (n : ℝ)})⁻¹).toReal with hCY_def
  have hCX_nn : 0 ≤ C_X := ENNReal.toReal_nonneg
  have hCY_nn : 0 ≤ C_Y := ENNReal.toReal_nonneg
  refine ⟨C_X * C_Y, mul_nonneg hCX_nn hCY_nn, ?_⟩
  -- slice integrability `∀ᵐ z, Integrable (x ↦ pX x · pY (z − x))`.
  have hslice_int : ∀ᵐ z ∂volume, Integrable (fun x => pX x * pY (z - x)) volume := by
    set f : ℝ × ℝ → ℝ := fun p => pX p.2 * pY (p.1 - p.2) with hf_def
    have hf_meas : AEStronglyMeasurable f (volume.prod volume) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => pX p.2) (volume.prod volume) :=
        (hpX_meas.comp measurable_snd).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => pY (p.1 - p.2)) (volume.prod volume) := by
        have hsub : Measurable (fun p : ℝ × ℝ => p.1 - p.2) := measurable_fst.sub measurable_snd
        exact (hpY_meas.comp hsub).aestronglyMeasurable
      exact h1.mul h2
    have hf_int : Integrable f (volume.prod volume) := by
      rw [integrable_prod_iff' hf_meas]
      refine ⟨?_, ?_⟩
      · refine Filter.Eventually.of_forall (fun x => ?_)
        exact (hpY_int.comp_sub_right x).const_mul (pX x)
      · have heq : (fun x => ∫ z, ‖f (z, x)‖ ∂volume)
            = (fun x => ‖pX x‖ * ∫ z, ‖pY z‖ ∂volume) := by
          funext x
          simp only [hf_def, norm_mul]
          rw [integral_const_mul]
          congr 1
          rw [← integral_sub_right_eq_self (fun z => ‖pY z‖) x]
        rw [heq]
        exact (hpX_int.norm.mul_const _)
    exact hf_int.prod_right_ae
  -- per-component density bounds (a.e. `x`), at the fixed level `n` (`n₀ = n`, `hn = le_refl`).
  have hbX : ∀ᵐ x ∂volume,
      (((condTrunc P X Y n).map X).rnDeriv volume x).toReal ≤ C_X * pX x :=
    condTrunc_marginal_density_le P hX hY hXY (Or.inl rfl) (le_refl n) hpos
  have hbY : ∀ᵐ y ∂volume,
      (((condTrunc P X Y n).map Y).rnDeriv volume y).toReal ≤ C_Y * pY y :=
    condTrunc_marginal_density_le P hX hY hXY (Or.inr rfl) (le_refl n) hpos
  set pnX : ℝ → ℝ := fun y => (((condTrunc P X Y n).map X).rnDeriv volume y).toReal with hpnX_def
  set pnY : ℝ → ℝ := fun y => (((condTrunc P X Y n).map Y).rnDeriv volume y).toReal with hpnY_def
  have hpnX_nn : ∀ x, 0 ≤ pnX x := fun x => ENNReal.toReal_nonneg
  have hpnY_nn : ∀ x, 0 ≤ pnY x := fun x => ENNReal.toReal_nonneg
  filter_upwards [hslice_int] with z hz_int
  have hbY_z : ∀ᵐ x ∂volume, pnY (z - x) ≤ C_Y * pY (z - x) :=
    (Measure.measurePreserving_sub_left volume z).quasiMeasurePreserving.ae hbY
  have hfg : (fun x => pnX x * pnY (z - x))
      ≤ᵐ[volume] fun x => (C_X * C_Y) * (pX x * pY (z - x)) := by
    filter_upwards [hbX, hbY_z] with x hxX hxY
    have h1 : pnX x * pnY (z - x) ≤ (C_X * pX x) * (C_Y * pY (z - x)) :=
      mul_le_mul hxX hxY (hpnY_nn (z - x)) (le_trans (hpnX_nn x) hxX)
    calc pnX x * pnY (z - x)
        ≤ (C_X * pX x) * (C_Y * pY (z - x)) := h1
      _ = (C_X * C_Y) * (pX x * pY (z - x)) := by ring
  have hf_nn : (0 : ℝ → ℝ) ≤ᵐ[volume] fun x => pnX x * pnY (z - x) :=
    Filter.Eventually.of_forall (fun x => mul_nonneg (hpnX_nn x) (hpnY_nn (z - x)))
  have hgi : Integrable (fun x => (C_X * C_Y) * (pX x * pY (z - x))) volume :=
    hz_int.const_mul (C_X * C_Y)
  have hmono : (∫ x, pnX x * pnY (z - x) ∂volume)
      ≤ ∫ x, (C_X * C_Y) * (pX x * pY (z - x)) ∂volume :=
    integral_mono_of_nonneg hf_nn hgi hfg
  rw [integral_const_mul] at hmono
  show convDensityAdd pnX pnY z ≤ (C_X * C_Y) * convDensityAdd pX pY z
  simpa only [convDensityAdd] using hmono

/-- **sub-helper B — 各点収束 `p_n∗q_n → p∗q`** (a.e. `z`)。
`p_n → pX` a.e. (`m_{X,n} → 1`, `1_Sn → 1`)、`q_n → qY` a.e.、convolution 内 DCT
(被積分関数収束 + 優関数 `C²·pX(x)qY(z-x)` 可積分) で各 `z` で
`p_n∗q_n(z) → pX∗qY(z)`。

honest: 結論は各点収束。仮説は a.c. + measurability。和エントロピー可積分性 (結論) を
仮説で受けていない。

独立 honesty audit 2026-06-07: honest_residual。(1) 非循環: 結論は a.e. 各点収束
`p_n∗q_n → p∗q`、仮説は a.c. + measurability の regularity precondition、結論型 ≢ 仮説型。
(2) 非バンドル: usc 結論を仮説で受けていない。(3) classification: plan slug 実在、収束は
DCT (`tendsto_integral_of_dominated_convergence`、優関数 A) で buildable、plan 分類が妥当。
@residual(plan:epi-infinite-variance-truncation-plan) -/
theorem convDensity_condTrunc_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) :
    ∀ᵐ z ∂volume, Tendsto
      (fun n => convDensityAdd (fun y => ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal)
        (fun y => ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal) z) atTop
      (𝓝 (convDensityAdd (fun y => (P.map X).rnDeriv volume y |>.toReal)
          (fun y => (P.map Y).rnDeriv volume y |>.toReal) z)) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **cross-entropy 列** `RHS_n := -∫ log(ν 密度) ∂μ_n` (`μ_n := condTrunc.map(X+Y)`,
`ν := P.map(X+Y)`)。crux usc の Gibbs 上界 + DCT 収束先を結ぶ補助量。

独立 honesty audit 2026-06-07: honest 補助量 def (退化定義悪用なし)。RHS の本体は
cross-entropy `H(μ_n, ν) = -∫ log(ν の Lebesgue 密度) ∂μ_n` (truncated 測度 μ_n を極限測度 ν
の log 密度で積分) という意味のある量で、Gibbs 出口補題 `differentialEntropy_le_cross_entropy`
の RHS `-∫ log(ν.rnDeriv vol).toReal ∂μ` と literal に一致 (#6 で消費)。usc 不等式 (結論) や
`:True` / vacuous shape を encode していない。`Prop` を返さず `ℝ`-値の honest 補助量。@audit:ok -/
noncomputable def crossEntropySeq (P : Measure Ω) (X Y : Ω → ℝ) (n : ℕ) : ℝ :=
  - ∫ x, Real.log ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal
      ∂((condTrunc P X Y n).map (fun ω => X ω + Y ω))

/-- **sub-helper C' — cross-entropy 可積分性 (per-n)**: `Integrable (log ν 密度) μ_n`
(`ν := P.map(X+Y)`, `μ_n := condTrunc.map(X+Y)`)。`∫|log ν 密度| dμ_n ≤ C²∫|log ν 密度|(p∗q)
< ∞` (優関数 sub-helper A + 和エントロピー可積分 `hent_sum`)。Gibbs sub-helper C の
`h_cross_int` 前提を供給。

honest: 結論は可積分性 (regularity)。仮説は a.c. + measurability + 和エントロピー可積分
(regularity)。usc 結論を仮説で受けていない。

独立 honesty audit 2026-06-07: honest_residual。(1) 非循環: 結論は cross-entropy 被積分関数の
可積分性 `Integrable (log ν 密度) μ_n`、仮説は a.c. + measurability + `hent_sum` (= regularity)、
結論型 ≢ 仮説型。(2) 非バンドル: usc 結論を仮説で受けていない。`hent_sum` は優関数経由で
可積分性供給に使う precondition。(3) classification: plan slug 実在、`∫|log ν|dμ_n ≤ C²∫|log ν|(p∗q)`
は優関数 A + `hent_sum` で buildable、plan 分類が妥当。
@residual(plan:epi-infinite-variance-truncation-plan) -/
theorem crossEntropy_integrable_condTrunc_sum (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    Integrable
      (fun x => Real.log ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)
      ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) := by
  classical
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  have hsum_meas : Measurable (fun ω => X ω + Y ω) := hX.add hY
  set ν := P.map (fun ω => X ω + Y ω) with hν_def
  set μn := (condTrunc P X Y n).map (fun ω => X ω + Y ω) with hμn_def
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  haveI : IsProbabilityMeasure μn := Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  -- a.c. of the conditioned sum law (used for the pull-back).
  have hν_ac : ν ≪ volume := by
    have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
      rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
    rw [hν_def, hconv]; exact Measure.conv_absolutelyContinuous hY_ac
  have hμn_ac : μn ≪ volume := map_condTrunc_absolutelyContinuous P hX hsum_meas hν_ac
  -- pull back the integrability to `volume` via the rnDeriv smul characterisation.
  set g : ℝ → ℝ := fun x => Real.log ((ν.rnDeriv volume x).toReal) with hg_def
  rw [← integrable_rnDeriv_smul_iff (μ := μn) (ν := volume) hμn_ac (f := g)]
  -- abbreviations: marginal/sum densities.
  set pnX : ℝ → ℝ := fun y => ((condTrunc P X Y n).map X).rnDeriv volume y |>.toReal with hpnX_def
  set pnY : ℝ → ℝ := fun y => ((condTrunc P X Y n).map Y).rnDeriv volume y |>.toReal with hpnY_def
  set pX : ℝ → ℝ := fun y => (P.map X).rnDeriv volume y |>.toReal with hpX_def
  set pY : ℝ → ℝ := fun y => (P.map Y).rnDeriv volume y |>.toReal with hpY_def
  have hpX_nn : ∀ x, 0 ≤ pX x := fun x => ENNReal.toReal_nonneg
  have hpY_nn : ∀ x, 0 ≤ pY x := fun x => ENNReal.toReal_nonneg
  have hpnX_nn : ∀ x, 0 ≤ pnX x := fun x => ENNReal.toReal_nonneg
  have hpnY_nn : ∀ x, 0 ≤ pnY x := fun x => ENNReal.toReal_nonneg
  -- `(μn.rnDeriv vol).toReal =ᵐ convDensityAdd pnX pnY`.
  have hμn_dens : (fun x => (μn.rnDeriv volume x).toReal)
      =ᵐ[volume] fun x => convDensityAdd pnX pnY x := by
    have h := rnDeriv_map_condTrunc_sum_ae P hX hY hX_ac hY_ac hXY hpos
    filter_upwards [h] with x hx
    have hconv_nn : 0 ≤ convDensityAdd pnX pnY x :=
      integral_nonneg (fun y => mul_nonneg (hpnX_nn y) (hpnY_nn (x - y)))
    rw [hμn_def, hx, ENNReal.toReal_ofReal hconv_nn]
  -- `(ν.rnDeriv vol).toReal =ᵐ convDensityAdd pX pY`.
  have hν_dens : (fun x => (ν.rnDeriv volume x).toReal)
      =ᵐ[volume] fun x => convDensityAdd pX pY x := by
    have h := rnDeriv_map_sum_ae P hX hY hX_ac hY_ac hXY
    filter_upwards [h] with x hx
    have hconv_nn : 0 ≤ convDensityAdd pX pY x :=
      integral_nonneg (fun y => mul_nonneg (hpX_nn y) (hpY_nn (x - y)))
    rw [hν_def, hx, ENNReal.toReal_ofReal hconv_nn]
  -- the fixed-`n` dominating bound `convDensityAdd pnX pnY ≤ C · convDensityAdd pX pY` (a.e.).
  obtain ⟨C, hC_nn, hbound_conv⟩ :=
    convDensityAdd_condTrunc_le_const_mul_at P hX hY hXY hX_ac hY_ac hpos
  -- bound function on `volume`: `C · |negMulLog ((ν.rnDeriv vol).toReal)|`.
  set bnd : ℝ → ℝ := fun x => C * |Real.negMulLog ((ν.rnDeriv volume x).toReal)| with hbnd_def
  have hbnd_int : Integrable bnd volume := hent_sum.abs.const_mul C
  -- measurability of the pulled-back integrand.
  have hF_meas : AEStronglyMeasurable
      (fun x => (μn.rnDeriv volume x).toReal • g x) volume := by
    refine ((Measure.measurable_rnDeriv μn volume).ennreal_toReal.aestronglyMeasurable.smul ?_)
    exact ((Real.measurable_log.comp
      (Measure.measurable_rnDeriv ν volume).ennreal_toReal)).aestronglyMeasurable
  refine Integrable.mono' hbnd_int hF_meas ?_
  filter_upwards [hμn_dens, hν_dens, hbound_conv] with x hxμn hxν hxbd
  -- pointwise: `‖(μn.rnDeriv).toReal • g‖ ≤ C · |negMulLog ((ν.rnDeriv).toReal)|`.
  -- `hxμn : (μn.rnDeriv).toReal = convDensityAdd pnX pnY x`,
  -- `hxν  : (ν.rnDeriv).toReal  = convDensityAdd pX pY x`.
  have hr_nn : (0 : ℝ) ≤ (ν.rnDeriv volume x).toReal := ENNReal.toReal_nonneg
  rw [smul_eq_mul, norm_mul, Real.norm_of_nonneg (ENNReal.toReal_nonneg)]
  -- `(μn.rnDeriv).toReal ≤ C · (ν.rnDeriv).toReal` from the convolution bound.
  have hstep : (μn.rnDeriv volume x).toReal ≤ C * (ν.rnDeriv volume x).toReal := by
    rw [hxμn, hxν]; exact hxbd
  -- `(ν.rnDeriv).toReal · |log| = |negMulLog ((ν.rnDeriv).toReal)|`.
  have hr_log : (ν.rnDeriv volume x).toReal * ‖g x‖
      = |Real.negMulLog ((ν.rnDeriv volume x).toReal)| := by
    have hgx : g x = Real.log ((ν.rnDeriv volume x).toReal) := rfl
    rw [hgx, Real.norm_eq_abs, Real.negMulLog_eq_neg, abs_neg, abs_mul, abs_of_nonneg hr_nn]
  calc (μn.rnDeriv volume x).toReal * ‖g x‖
      ≤ (C * (ν.rnDeriv volume x).toReal) * ‖g x‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    _ = C * ((ν.rnDeriv volume x).toReal * ‖g x‖) := by ring
    _ = C * |Real.negMulLog ((ν.rnDeriv volume x).toReal)| := by rw [hr_log]
    _ = bnd x := by rw [hbnd_def]

/-- **sub-helper C — per-n Gibbs 上界**: `∀ᶠ n, h(μ_n) ≤ RHS_n`
(`RHS_n = crossEntropySeq P X Y n`)。`differentialEntropy_le_cross_entropy`
(`μ = μ_n`, `ν = P.map(X+Y)`) に per-n regularity (μ_n a.c.、μ_n ≪ ν、μ_n 有限 entropy #2、
cross-entropy 可積分 C' `crossEntropy_integrable_condTrunc_sum`) を供給。

genuine Gibbs 配線: μ_n a.c. (`map_condTrunc_absolutelyContinuous`)、ν a.c.
(conv abs continuous)、μ_n ≪ ν (`cond_absolutelyContinuous` の `.map`)、μ_n 有限 entropy
(#2 `integrable_negMulLog_map_condTrunc_sum`)、cross-entropy 可積分 (C') を
`differentialEntropy_le_cross_entropy` に供給。body 独自 sorry なし (transitive: C' + #2)。

honest: 結論は per-n 不等式 (Gibbs)。仮説は a.c. + measurability + 和エントロピー可積分
(regularity)。usc 結論を仮説で受けていない。

独立 honesty audit 2026-06-07: honest_residual (transitive: C'/#2 park)。(1) 非循環: 結論は
per-n Gibbs 不等式 `h(μ_n) ≤ crossEntropySeq`、仮説は `hX_ac`/`hY_ac`/`hXY`/`hent_sum`
(= regularity precondition)、結論型 ≢ 仮説型。(2) 非バンドル (最重点): usc 不等式 (= 親結論)
を `*Hypothesis` predicate に bundle していない。`hent_sum` (和の有限微分エントロピー) は
C' の cross 可積分性供給に使う regularity precondition で load-bearing でない (per-n Gibbs
不等式を encode しない)。(3) body は genuine Gibbs 配線: 出口補題 `differentialEntropy_le_cross_entropy`
(自身 sorryAx-free、klDiv≥0 `toReal_klDiv_of_measure_eq` + llr 分解の genuine 証明) に
μ_n a.c. (`map_condTrunc_absolutelyContinuous`)/ν a.c./μ_n≪ν (`cond_absolutelyContinuous.map`)/
μ_n 有限 entropy (#2)/cross 可積分 (C') を機械供給。body 独自 sorry なし。(4) `#print axioms`
= transitive sorryAx は C' (`crossEntropy_integrable_condTrunc_sum`) + #2 由来のみ
(2026-06-07 機械確認)。plan slug 実在。
@residual(plan:epi-infinite-variance-truncation-plan) -/
theorem differentialEntropy_condTrunc_sum_le_crossEntropy (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    ∀ᶠ n in atTop,
      differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω))
        ≤ crossEntropySeq P X Y n := by
  have hsum_meas : Measurable (fun ω => X ω + Y ω) := hX.add hY
  have hν_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume := by
    have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
      rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
    rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac
  filter_upwards [eventually_measure_truncSet_pos P hX hY] with n hpos
  haveI : IsProbabilityMeasure (condTrunc P X Y n) :=
    isProbabilityMeasure_condTrunc P hX hY hpos
  haveI : IsProbabilityMeasure ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) :=
    Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  haveI : IsProbabilityMeasure (P.map (fun ω => X ω + Y ω)) :=
    Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  -- regularity facts for the Gibbs lemma.
  have hμ_ac : ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) ≪ volume :=
    map_condTrunc_absolutelyContinuous P hX hsum_meas hν_ac
  have hμν : ((condTrunc P X Y n).map (fun ω => X ω + Y ω))
      ≪ (P.map (fun ω => X ω + Y ω)) := by
    have h_cond : condTrunc P X Y n ≪ P := ProbabilityTheory.cond_absolutelyContinuous
    exact h_cond.map hsum_meas
  have hμ_ent : Integrable
      (fun x => Real.negMulLog
        (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume :=
    integrable_negMulLog_map_condTrunc_sum P hX hY hX_ac hY_ac hXY hpos
  have hcross : Integrable
      (fun x => Real.log ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)
      ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) :=
    crossEntropy_integrable_condTrunc_sum P hX hY hXY hX_ac hY_ac hent_sum hpos
  exact differentialEntropy_le_cross_entropy hμ_ac hν_ac hμν hμ_ent hcross

/-- **sub-helper D — cross-entropy 列の収束**: `RHS_n → h(ν)` (`ν = P.map(X+Y)`)。
`RHS_n = ∫ (-log ν 密度)·(p_n∗q_n) dvol` (μ_n 密度経由で vol に pull back)、各点収束
(sub-helper B `p_n∗q_n → p∗q`) + 優関数 `|log ν 密度|·C²(p∗q)` 可積分
(sub-helper A + `hent_sum`) で `tendsto_integral_of_dominated_convergence` →
`-∫(p∗q)log(p∗q) = h(ν)`。

honest: 結論は数列の収束。仮説は a.c. + measurability + 和エントロピー可積分 (regularity)。
usc 結論を仮説で受けていない。

独立 honesty audit 2026-06-07: honest_residual。(1) 非循環: 結論は `RHS_n → h(ν)` (数列収束)、
仮説は a.c. + measurability + `hent_sum` (= regularity)、結論型 ≢ 仮説型。(2) 非バンドル:
usc 不等式や h(ν) の値を仮説に bundle していない (収束先 h(ν) は結論内で導出、仮説で受けない)。
(3) classification: plan slug 実在、`RHS_n = ∫(-log ν)·(p_n∗q_n)` の各点収束 (B) + 優関数 (A+hent_sum)
で DCT 収束 → buildable、plan 分類が妥当。
@residual(plan:epi-infinite-variance-truncation-plan) -/
theorem crossEntropySeq_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    Tendsto (fun n => crossEntropySeq P X Y n) atTop
      (𝓝 (differentialEntropy (P.map (fun ω => X ω + Y ω)))) := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

/-- **crux usc 微分エントロピー版の有界性副産物**: `h(P_n.map(X+Y))` (= `h(μ_n)`) の列が
`atTop` で上に有界 (`IsBoundedUnder (≤)`、genuine: Gibbs C + DCT D から) かつ下から co-有界
(`IsCoboundedUnder (≤)`、compact support fibre 下界、park)。crux usc 本体
(`differentialEntropy_condTrunc_sum_limsup_le`) の limsup 比較 + exp-lift
(`entropyPowerExt_condTrunc_sum_limsup_le`) の `Monotone.map_limsup_of_continuousAt` で
`bdd_above`/`cobdd` 前提を供給する。

genuine: 上界 (`.1`) は sub-helper C (`h(μ_n) ≤ RHS_n`) + sub-helper D (`RHS_n → h(ν)` →
`IsBoundedUnder`) + `IsBoundedUnder.mono_le` で genuine 組立。co-有界 (`.2`、下界) のみ
fibre 下界解析が当該セッション規模を超え park (body 内 1 sorry)。

honest: 結論は列の有界性 (regularity)。仮説は a.c. + measurability + 和エントロピー可積分
(regularity precondition)。usc 不等式 (結論) を仮説で受けていない。

独立 honesty audit 2026-06-07: honest_residual (部分 fill: 上界 genuine / 下界 park)。
(1) 非循環: 結論は `IsBoundedUnder ∧ IsCoboundedUnder` (有界性ペア)、仮説は regularity precondition、
結論型 ≢ 仮説型。(2) 部分 fill 確認: 上界 `.1` (`IsBoundedUnder`) は body 内で genuine 組立
(Gibbs C `h(μ_n) ≤ RHS_n` + D 収束 `hD.isBoundedUnder_le` + `.mono_le hC`、独自 sorry なし、
transitive のみ)、co-有界 `.2` (`IsCoboundedUnder` = 下界) のみ body 内 1 sorry で park
(compact-support fibre 下界解析がセッション規模超)。(3) 非バンドル: usc 不等式 (親結論) を
仮説で受けていない。上界が #9 で load-bearing に使われるが genuine fill なので問題なし
(park は co-bound 側のみ)。(4) plan slug 実在。inner sorry に `@residual` コメント付。
@residual(plan:epi-infinite-variance-truncation-plan) -/
theorem differentialEntropy_condTrunc_sum_bddUnder (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    IsBoundedUnder (· ≤ ·) atTop
        (fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω)))
      ∧ IsCoboundedUnder (· ≤ ·) atTop
        (fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) := by
  refine ⟨?_, ?_⟩
  · -- bounded above: from Gibbs (C) `h(μ_n) ≤ RHS_n` + RHS_n bounded (D converges).
    have hC : ∀ᶠ n in atTop,
        differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω))
          ≤ crossEntropySeq P X Y n :=
      differentialEntropy_condTrunc_sum_le_crossEntropy P hX hY hXY hX_ac hY_ac hent_sum
    have hD : Tendsto (fun n => crossEntropySeq P X Y n) atTop
        (𝓝 (differentialEntropy (P.map (fun ω => X ω + Y ω)))) :=
      crossEntropySeq_tendsto P hX hY hXY hX_ac hY_ac hent_sum
    exact hD.isBoundedUnder_le.mono_le hC
  · -- cobounded below: compact-support fibre lower bound (genuine analytic core, parked).
    -- @residual(plan:epi-infinite-variance-truncation-plan)
    sorry

/-! ### Helper 4 — crux usc (plan §推奨分解 4, genuine sub-wall 候補) -/

/-- **crux usc (微分エントロピー版)**: `limsup_n h(P_n.map(X+Y)) ≤ h(P.map(X+Y))`。
Gibbs step (`differentialEntropy_le_cross_entropy` で h(P_n.map(X+Y)) を cross-entropy
`-∫(p_n∗q_n)log(p∗q)` で上から抑える) + cross-entropy DCT (優関数 `C²(p∗q)|log(p∗q)|`、
和の有限微分エントロピーで可積分、`tendsto_integral_of_dominated_convergence` で
`→ -∫(p∗q)log(p∗q) = h(p∗q)`)。本 moonshot の核。

genuine assembly (2026-06-07): limsup chain `limsup h(μ_n) ≤ limsup RHS_n = h(ν)` を
sub-helper C (`differentialEntropy_condTrunc_sum_le_crossEntropy`、per-n Gibbs) +
sub-helper D (`crossEntropySeq_tendsto`、RHS 収束) + boundedness
(`differentialEntropy_condTrunc_sum_bddUnder`) を black box として genuine 組立。
解析核 (Gibbs 前提供給 / DCT) は C/D に局所化、本 body の独自 sorry なし
(transitive sorry は C/D/boundedness の plan park)。

honest: signature の `hent_sum` は regularity precondition (有限微分エントロピー)、結論
(usc 不等式) を encode しない。body は C/D/boundedness を呼ぶ限り genuine。

独立 honesty audit 2026-06-07: honest_residual (genuine assembly, transitive: C'/D/boundedness park)。
(1) 非循環: 結論は `limsup h(μ_n) ≤ h(ν)`、仮説は `hX_ac`/`hY_ac`/`hXY`/`hent_sum`
(= regularity precondition)、結論型 ≢ 仮説型。(2) 非バンドル (最重点): usc 結論を sub-helper の
仮説に bundle せず、limsup chain を機械配線。`Filter.limsup_le_limsup hC hcobdd hRHS_bdd` の
引数向きを Mathlib signature (`h : u ≤ᶠ v` / `hu : IsCoboundedUnder u` / `hv : IsBoundedUnder v`)
と照合: u = h_seq, v = crossEntropySeq、hC (∀ᶠ h_seq ≤ RHS)・hcobdd (h_seq の cobdd =
boundedness の `.2`)・hRHS_bdd (D 収束 → RHS bdd above) で全引数の向き・型整合。`_ = hν`
は `hD.limsup_eq` (D の収束先)。(3) sufficiency: `limsup h_seq ≤ limsup RHS_n = h(ν)` は
per-n Gibbs (C) + RHS 収束 (D) から semantic に follow (差分形/比形の取り違えなし、単調 push 不使用)。
`hent_sum` は load-bearing でなく precondition。body 独自 sorry なし。(4) `#print axioms` =
transitive sorryAx は C'/D/boundedness の plan park 由来のみ (2026-06-07 機械確認、本 body は genuine)。
@residual(plan:epi-infinite-variance-truncation-plan) -/
theorem differentialEntropy_condTrunc_sum_limsup_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    Filter.limsup
      (fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop
      ≤ differentialEntropy (P.map (fun ω => X ω + Y ω)) := by
  set h_seq : ℕ → ℝ :=
    fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) with hseq_def
  set hν : ℝ := differentialEntropy (P.map (fun ω => X ω + Y ω)) with hhν_def
  -- sub-helper C: `h_seq n ≤ RHS_n` eventually.
  have hC : ∀ᶠ n in atTop, h_seq n ≤ crossEntropySeq P X Y n :=
    differentialEntropy_condTrunc_sum_le_crossEntropy P hX hY hXY hX_ac hY_ac hent_sum
  -- sub-helper D: `RHS_n → hν`.
  have hD : Tendsto (fun n => crossEntropySeq P X Y n) atTop (𝓝 hν) :=
    crossEntropySeq_tendsto P hX hY hXY hX_ac hY_ac hent_sum
  -- boundedness of `h_seq`.
  obtain ⟨_hbdd, hcobdd⟩ :=
    differentialEntropy_condTrunc_sum_bddUnder P hX hY hXY hX_ac hY_ac hent_sum
  -- `RHS_n` is bounded above (it converges).
  have hRHS_bdd : IsBoundedUnder (· ≤ ·) atTop (fun n => crossEntropySeq P X Y n) :=
    hD.isBoundedUnder_le
  -- `limsup h_seq ≤ limsup RHS_n = hν`.
  calc Filter.limsup h_seq atTop
      ≤ Filter.limsup (fun n => crossEntropySeq P X Y n) atTop :=
        Filter.limsup_le_limsup hC hcobdd hRHS_bdd
    _ = hν := hD.limsup_eq

/-- **crux usc (entropyPower 版)**: `limsup_n Nₑ(P_n.map(X+Y)) ≤ Nₑ(P.map(X+Y))`。
微分エントロピー版 (`differentialEntropy_condTrunc_sum_limsup_le`) を `entropyPowerExt`
= `ENNReal.ofReal (exp (2·h))` の単調連続変換で lift。

機構 (`g h := ofReal(exp(2h))`、単調連続):
- per-n: `Nₑ(μ_n) = g(h(μ_n))` (`μ_n` a.c. `map_condTrunc_absolutelyContinuous` + 有限
  entropy #2 `integrable_negMulLog_map_condTrunc_sum`、`entropyPowerExt_of_ac_integrable`)。
- limit: `Nₑ(ν) = g(h(ν))` (ν a.c. + `hent_sum`)。
- `limsup Nₑ(μ_n) = limsup (g∘h(μ_n)) = g(limsup h(μ_n))`
  (`Monotone.map_limsup_of_continuousAt`、有界性は `differentialEntropy_condTrunc_sum_bddUnder`)
  `≤ g(h(ν)) = Nₑ(ν)` (g 単調 + #3 `differentialEntropy_condTrunc_sum_limsup_le`)。

`hent_sum` は regularity precondition (有限微分エントロピー)、結論を encode しない。

独立 honesty audit 2026-06-07: honest_residual (genuine exp-lift, transitive: #3/C'/D/boundedness park)。
(1) 非循環: 結論は `limsup Nₑ(μ_n) ≤ Nₑ(ν)`、仮説は regularity precondition のみ、結論型 ≢ 仮説型。
(2) 非バンドル: usc 結論を bundle せず、単調連続 lift `g h := ofReal(exp(2h))` で #3 (微分エントロピー版)
を持ち上げ。per-n rewrite `Nₑ(μ_n) = g(h(μ_n))` は出口補題 `entropyPowerExt_of_ac_integrable`
(自身 `@audit:ok`、sorryAx-free、退化定義悪用なし = a.c.+有限 entropy で `ofReal(exp(2h))` を返す
genuine 式) を μ_n a.c. (`hac_n`) + #2 有限 entropy に適用、limit rewrite も同補題。`g` 単調連続
(`hg_mono`/`hg_cont`) で `Monotone.map_limsup_of_continuousAt` (boundedness `hbdd`/`hcobdd` 供給) →
`g(limsup h_seq) ≤ g(hν) = Nₑ(ν)`、最後の `≤` は g 単調 + #3 (`differentialEntropy_condTrunc_sum_limsup_le`)。
(3) sufficiency: exp lift は単調連続変換ゆえ #3 の usc 不等式から semantic に follow (g 単調で向き保存)。
body 独自 sorry なし。(4) `#print axioms` = transitive sorryAx は #3/C'/D/boundedness park 由来のみ
(2026-06-07 機械確認)。
@residual(plan:epi-infinite-variance-truncation-plan) -/
theorem entropyPowerExt_condTrunc_sum_limsup_le (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hent_sum : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    Filter.limsup
      (fun n => entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop
      ≤ entropyPowerExt (P.map (fun ω => X ω + Y ω)) := by
  set ν := P.map (fun ω => X ω + Y ω) with hν_def
  have hsum_meas : Measurable (fun ω => X ω + Y ω) := hX.add hY
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hsum_meas.aemeasurable
  have hν_ac : ν ≪ volume := by
    rw [hν_def]
    have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
      rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
    rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac
  -- the continuous monotone lift `g h := ofReal (exp (2 h))`.
  set g : ℝ → ℝ≥0∞ := fun h => ENNReal.ofReal (Real.exp (2 * h)) with hg_def
  have hg_mono : Monotone g := by
    intro a b hab
    exact ENNReal.ofReal_mono (Real.exp_le_exp.mpr (by linarith))
  have hg_cont : Continuous g :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  -- abbreviations.
  set h_seq : ℕ → ℝ :=
    fun n => differentialEntropy ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) with hseq_def
  set hν : ℝ := differentialEntropy ν with hhν_def
  -- per-n rewrite: `Nₑ(μ_n) = g (h_seq n)` eventually.
  have hper_n : ∀ᶠ n in atTop,
      entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) = g (h_seq n) := by
    filter_upwards [eventually_measure_truncSet_pos P hX hY] with n hpos
    have hac_n : ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) ≪ volume := by
      have hconv : P.map (fun ω => X ω + Y ω) = (P.map X) ∗ (P.map Y) := by
        rw [show (fun ω => X ω + Y ω) = X + Y from rfl, hXY.map_add_eq_map_conv_map hX hY]
      have h_cond : condTrunc P X Y n ≪ P := ProbabilityTheory.cond_absolutelyContinuous
      exact (h_cond.map hsum_meas).trans (by rw [hconv]; exact Measure.conv_absolutelyContinuous hY_ac)
    have hent_n : Integrable
        (fun x => Real.negMulLog
          (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume :=
      integrable_negMulLog_map_condTrunc_sum P hX hY hX_ac hY_ac hXY hpos
    rw [entropyPowerExt_of_ac_integrable hac_n hent_n]
  -- limit rewrite: `Nₑ(ν) = g hν`.
  have hlim_eq : entropyPowerExt ν = g hν :=
    entropyPowerExt_of_ac_integrable hν_ac hent_sum
  -- boundedness for the monotone-continuous limsup push.
  obtain ⟨hbdd, hcobdd⟩ :=
    differentialEntropy_condTrunc_sum_bddUnder P hX hY hXY hX_ac hY_ac hent_sum
  -- `limsup Nₑ(μ_n) = limsup (g ∘ h_seq)`.
  have hcongr : Filter.limsup
      (fun n => entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop
      = Filter.limsup (fun n => g (h_seq n)) atTop :=
    Filter.limsup_congr hper_n
  rw [hcongr, hlim_eq]
  -- `limsup (g ∘ h_seq) = g (limsup h_seq)` via the continuous-monotone push.
  have hpush : g (Filter.limsup h_seq atTop) = Filter.limsup (fun n => g (h_seq n)) atTop :=
    hg_mono.map_limsup_of_continuousAt h_seq (hg_cont.continuousAt) hbdd hcobdd
  rw [← hpush]
  -- `g (limsup h_seq) ≤ g hν` by monotonicity + the differential-entropy usc (#3).
  refine hg_mono ?_
  exact differentialEntropy_condTrunc_sum_limsup_le P hX hY hXY hX_ac hY_ac hent_sum

/-! ### Helper 5 — RHS 収束 (plan §推奨分解 5) -/

/-- **growing-set entropy 分解恒等式**: probability measure `μ` (a.c.+有限 entropy) を
成長する切詰集合 `Sn := {|r|≤n}` で conditioning した測度の微分エントロピーは
`h(cond μ Sn) = (m_n.toReal)⁻¹ · ∫ Sn.indicator (negMulLog ∘ q) ∂vol + log (m_n.toReal)`
(`m_n := μ Sn`, `q x := (μ.rnDeriv vol x).toReal`)。
`rnDeriv_cond_eq` (cond density formula) + `negMulLog_mul` + density の Sn 積分 = measure。 -/
theorem differentialEntropy_cond_decomp (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (hpos : μ {r : ℝ | |r| ≤ (n : ℝ)} ≠ 0)
    (hac : μ ≪ volume)
    (hent : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) :
    differentialEntropy (ProbabilityTheory.cond μ {r : ℝ | |r| ≤ (n : ℝ)})
      = ((μ {r : ℝ | |r| ≤ (n : ℝ)}).toReal)⁻¹
          * ∫ x, ({r : ℝ | |r| ≤ (n : ℝ)}).indicator
              (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) x ∂volume
        + Real.log ((μ {r : ℝ | |r| ≤ (n : ℝ)}).toReal) := by
  classical
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn :=
    measurableSet_le measurable_norm measurable_const
  set m : ℝ≥0∞ := μ Sn with hm_def
  have hm_ne_top : m ≠ ∞ := measure_ne_top _ _
  set q : ℝ → ℝ := fun x => ((μ.rnDeriv volume x).toReal) with hq_def
  have hq_meas : Measurable q := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hq_int : Integrable q volume := Measure.integrable_toReal_rnDeriv
  set c : ℝ := (m⁻¹).toReal with hc_def
  -- cond density formula: rewrite the cond rnDeriv a.e.
  have h_rn : (ProbabilityTheory.cond μ Sn).rnDeriv volume
      =ᵐ[volume] fun x => m⁻¹ * Sn.indicator (μ.rnDeriv volume) x :=
    rnDeriv_cond_eq μ hSn_meas hpos
  -- `differentialEntropy (cond μ Sn) = ∫ Sn.indicator (q · negMulLog c + c · negMulLog q)`.
  have h_ent_eq : differentialEntropy (ProbabilityTheory.cond μ Sn)
      = ∫ x, Sn.indicator
          (fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)) x ∂volume := by
    unfold differentialEntropy
    refine integral_congr_ae ?_
    filter_upwards [h_rn] with x hx
    rw [hx]
    by_cases hxs : x ∈ Sn
    · rw [Set.indicator_of_mem hxs
          (f := fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)),
        ENNReal.toReal_mul, Set.indicator_of_mem hxs (f := μ.rnDeriv volume)]
      show Real.negMulLog (c * q x) = q x * Real.negMulLog c + c * Real.negMulLog (q x)
      exact Real.negMulLog_mul c (q x)
    · rw [Set.indicator_of_notMem hxs
          (f := fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)),
        Set.indicator_of_notMem hxs (f := μ.rnDeriv volume)]
      simp only [mul_zero, ENNReal.toReal_zero, Real.negMulLog_zero]
  rw [h_ent_eq]
  -- split the indicator integral into the two terms.
  have hsplit : (fun x => Sn.indicator
      (fun x => q x * Real.negMulLog c + c * Real.negMulLog (q x)) x)
      = fun x => Sn.indicator (fun x => q x * Real.negMulLog c) x
        + Sn.indicator (fun x => c * Real.negMulLog (q x)) x := by
    funext x
    by_cases hxs : x ∈ Sn
    · simp only [Set.indicator_of_mem hxs]
    · simp only [Set.indicator_of_notMem hxs, add_zero]
  rw [hsplit]
  -- integrability of the two indicator pieces.
  have h1_int : Integrable (fun x => Sn.indicator (fun x => q x * Real.negMulLog c) x) volume :=
    (hq_int.mul_const (Real.negMulLog c)).indicator hSn_meas
  have h2_int : Integrable (fun x => Sn.indicator (fun x => c * Real.negMulLog (q x)) x) volume :=
    (hent.const_mul c).indicator hSn_meas
  rw [integral_add h1_int h2_int]
  -- first term: `∫ Sn.indicator (q · negMulLog c) = negMulLog c · (μ Sn).toReal`.
  have h_term1 : ∫ x, Sn.indicator (fun x => q x * Real.negMulLog c) x ∂volume
      = Real.negMulLog c * m.toReal := by
    rw [integral_indicator hSn_meas]
    rw [show (fun x => q x * Real.negMulLog c) = (fun x => Real.negMulLog c * q x) from by
      funext x; ring]
    rw [MeasureTheory.integral_const_mul]
    rw [Measure.setIntegral_toReal_rnDeriv hac Sn, measureReal_def]
  -- second term: `∫ Sn.indicator (c · negMulLog q) = c · ∫ Sn.indicator (negMulLog q)`.
  have h_term2 : ∫ x, Sn.indicator (fun x => c * Real.negMulLog (q x)) x ∂volume
      = c * ∫ x, Sn.indicator (fun x => Real.negMulLog (q x)) x ∂volume := by
    rw [integral_indicator hSn_meas, integral_indicator hSn_meas]
    rw [MeasureTheory.integral_const_mul]
  rw [h_term1, h_term2]
  -- `negMulLog c · m.toReal = log m.toReal` and `c = m.toReal⁻¹`.
  have hm_pos : 0 < m.toReal := ENNReal.toReal_pos hpos hm_ne_top
  have hc_eq : c = (m.toReal)⁻¹ := by
    rw [hc_def, ENNReal.toReal_inv]
  -- `negMulLog c * m.toReal = -c * log c * m.toReal = log m.toReal`.
  have h_negc : Real.negMulLog c * m.toReal = Real.log m.toReal := by
    have h1 : Real.negMulLog c = -c * Real.log c := rfl
    rw [h1, hc_eq, Real.log_inv]
    field_simp
  rw [h_negc, hc_eq]
  ring

/-- **RHS 収束 (微分エントロピー版)**: `h(P_n.map Z) → h(P.map Z)` (各成分)。
恒等式 `-∫ p_n log p_n = -(1/m_n)∫_{truncSet} p log p + log m_n`、第 1 項は固定可積分
`p log p` の growing-set monotone/dominated convergence、第 2 項は `m_n → 1` → `log m_n → 0`。
moment 非依存 (固定可積分関数 `p log p` のみ)。

⚠ signature 追加: bridge `map_condTrunc_eq_cond_map` を使うため `hZ : Z = X ∨ Z = Y`
(成分制約) + `hXY` (独立性) が必要 (旧 `hZ : Measurable Z` を置換、可測性は `hZ` から導出)。
両者とも structural/regularity precondition (結論 = entropy 収束を encode しない)。 -/
theorem differentialEntropy_map_condTrunc_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y)
    (hZ_ac : (P.map Z) ≪ volume)
    (hZ_ent : Integrable (fun x => Real.negMulLog ((P.map Z).rnDeriv volume x).toReal) volume) :
    Tendsto (fun n => differentialEntropy ((condTrunc P X Y n).map Z)) atTop
      (𝓝 (differentialEntropy (P.map Z))) := by
  classical
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  haveI : IsProbabilityMeasure (P.map Z) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hZmeas.aemeasurable
  -- abbreviations: `Sn n = {|r| ≤ n}`, `m_n = (P.map Z) (Sn n)`, `p x = ((P.map Z).rnDeriv vol x).toReal`.
  set Sn : ℕ → Set ℝ := fun n => {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : ∀ n, MeasurableSet (Sn n) := fun n =>
    measurableSet_le measurable_norm measurable_const
  set p : ℝ → ℝ := fun x => ((P.map Z).rnDeriv volume x).toReal with hp_def
  -- the `Sn n` are monotone increasing and exhaust `ℝ`.
  have hSn_mono : Monotone Sn := by
    intro a b hab r hr
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    exact le_trans hr hab'
  have hSn_union : ⋃ n, Sn n = Set.univ := by
    rw [Set.eq_univ_iff_forall]; intro r
    obtain ⟨k, hk⟩ := exists_nat_ge (|r|)
    exact Set.mem_iUnion.2 ⟨k, hk⟩
  -- `m_n = (P.map Z) (Sn n) → 1`.
  have hm_tendsto : Tendsto (fun n => (P.map Z) (Sn n)) atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := P.map Z) hSn_mono
    rw [hSn_union, measure_univ] at h
    exact h
  -- eventually `(P.map Z) (Sn n) ≠ 0` and `P (truncSet X Y n) ≠ 0`.
  have hSn_pos_ev : ∀ᶠ n in atTop, (P.map Z) (Sn n) ≠ 0 := by
    have h_nhds : {x : ℝ≥0∞ | x ≠ 0} ∈ 𝓝 (1 : ℝ≥0∞) := isOpen_ne.mem_nhds one_ne_zero
    exact hm_tendsto.eventually_mem h_nhds
  have hpos_ev : ∀ᶠ n in atTop, P (truncSet X Y n) ≠ 0 :=
    eventually_measure_truncSet_pos P hX hY
  -- `m_n.toReal → 1`.
  have hmreal_tendsto : Tendsto (fun n => ((P.map Z) (Sn n)).toReal) atTop (𝓝 (1 : ℝ)) := by
    have := (ENNReal.tendsto_toReal (ENNReal.one_ne_top)).comp hm_tendsto
    simpa using this
  -- `c_n := (m_n.toReal)⁻¹ → 1`.
  have hc_tendsto : Tendsto (fun n => ((P.map Z) (Sn n)).toReal⁻¹) atTop (𝓝 1) := by
    have := (continuousAt_inv₀ (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hmreal_tendsto
    simpa using this
  -- `log m_n.toReal → log 1 = 0`.
  have hlogm_tendsto : Tendsto (fun n => Real.log ((P.map Z) (Sn n)).toReal) atTop (𝓝 0) := by
    have := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hmreal_tendsto
    simpa [Real.log_one] using this
  -- `∫ Sn.indicator (negMulLog ∘ p) → ∫ negMulLog ∘ p = h(P.map Z)` via DCT.
  have hint_tendsto :
      Tendsto (fun n => ∫ x, (Sn n).indicator
          (fun x => Real.negMulLog (p x)) x ∂volume) atTop
        (𝓝 (∫ x, Real.negMulLog (p x) ∂volume)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun x => |Real.negMulLog (p x)|) ?_ ?_ ?_ ?_
    · -- AEStronglyMeasurable of each indicator term.
      intro n
      refine (Measurable.aestronglyMeasurable ?_)
      exact (Real.continuous_negMulLog.measurable.comp
        ((Measure.measurable_rnDeriv _ _).ennreal_toReal)).indicator (hSn_meas n)
    · -- bound integrable.
      exact hZ_ent.abs
    · -- pointwise bound: `‖Sn.indicator (negMulLog p) x‖ ≤ |negMulLog p x|`.
      intro n
      refine Filter.Eventually.of_forall (fun x => ?_)
      by_cases hxn : x ∈ Sn n
      · rw [Set.indicator_of_mem hxn, Real.norm_eq_abs]
      · rw [Set.indicator_of_notMem hxn]; simp [abs_nonneg]
    · -- pointwise limit: for each x, eventually `x ∈ Sn n`, so indicator → value.
      refine Filter.Eventually.of_forall (fun x => ?_)
      obtain ⟨k, hk⟩ := exists_nat_ge (|x|)
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Filter.eventually_ge_atTop k] with n hn
      have hxn : x ∈ Sn n := le_trans hk (by exact_mod_cast hn)
      rw [Set.indicator_of_mem hxn]
  -- the integral equals `h(P.map Z)` (= `∫ negMulLog p`).
  have hint_eq : (∫ x, Real.negMulLog (p x) ∂volume) = differentialEntropy (P.map Z) := rfl
  rw [← hint_eq]
  -- now assemble: the RHS sequence `c_n · term + log m_n` tends to `∫ negMulLog p`,
  -- and eventually equals `h(condTrunc.map Z)`.
  have hRHS_tendsto : Tendsto (fun n => ((P.map Z) (Sn n)).toReal⁻¹
      * (∫ x, (Sn n).indicator (fun x => Real.negMulLog (p x)) x ∂volume)
      + Real.log ((P.map Z) (Sn n)).toReal) atTop
      (𝓝 (∫ x, Real.negMulLog (p x) ∂volume)) := by
    have hmul : Tendsto (fun n => ((P.map Z) (Sn n)).toReal⁻¹
        * ∫ x, (Sn n).indicator (fun x => Real.negMulLog (p x)) x ∂volume) atTop
        (𝓝 (1 * ∫ x, Real.negMulLog (p x) ∂volume)) :=
      hc_tendsto.mul hint_tendsto
    have := hmul.add hlogm_tendsto
    simpa using this
  refine hRHS_tendsto.congr' ?_
  filter_upwards [hpos_ev, hSn_pos_ev] with n hpos hSn_pos
  rw [map_condTrunc_eq_cond_map P hX hY hXY hZ hpos,
    differentialEntropy_cond_decomp (P.map Z) hSn_pos hZ_ac hZ_ent]

/-- **RHS 収束 (entropyPower 版)**: `Nₑ(P_n.map Z) → Nₑ(P.map Z)`。
微分エントロピー版を `entropyPowerExt = exp (2·h)` の連続変換で lift。

⚠ signature 追加: 微分エントロピー版 (`differentialEntropy_map_condTrunc_tendsto`) と
per-n 有限 entropy (`integrable_negMulLog_map_condTrunc`、Z=X/Y で適用) のため
`hZ : Z = X ∨ Z = Y` + `hXY` が必要 (旧 `hZ : Measurable Z` を置換)。
structural/regularity precondition。 -/
theorem entropyPowerExt_map_condTrunc_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    {Z : Ω → ℝ} (hZ : Z = X ∨ Z = Y)
    (hZ_ac : (P.map Z) ≪ volume)
    (hZ_ent : Integrable (fun x => Real.negMulLog ((P.map Z).rnDeriv volume x).toReal) volume) :
    Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map Z)) atTop
      (𝓝 (entropyPowerExt (P.map Z))) := by
  have hZmeas : Measurable Z := by rcases hZ with rfl | rfl; exacts [hX, hY]
  -- the differential-entropy version.
  have hdiff := differentialEntropy_map_condTrunc_tendsto P hX hY hXY hZ hZ_ac hZ_ent
  -- the continuous exp-lift map `g h := ofReal (exp (2h))`.
  have hcont : Continuous (fun h : ℝ => ENNReal.ofReal (Real.exp (2 * h))) :=
    ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  -- limit side: `Nₑ (P.map Z) = ofReal (exp (2 h(P.map Z)))`.
  have hlim_eq : entropyPowerExt (P.map Z)
      = ENNReal.ofReal (Real.exp (2 * differentialEntropy (P.map Z))) :=
    entropyPowerExt_of_ac_integrable hZ_ac hZ_ent
  rw [hlim_eq]
  -- lift the differential-entropy tendsto through `g`, then `Tendsto.congr'` over the
  -- eventual positive-mass set where `Nₑ (condTrunc.map Z) = ofReal (exp (2 h))`.
  have hlifted := (hcont.tendsto (differentialEntropy (P.map Z))).comp hdiff
  refine hlifted.congr' ?_
  filter_upwards [eventually_measure_truncSet_pos P hX hY] with n hpos
  -- per-n: `(condTrunc.map Z) ≪ vol` and finite entropy ⟹ `Nₑ = ofReal (exp (2h))`.
  have hac_n : ((condTrunc P X Y n).map Z) ≪ volume :=
    map_condTrunc_absolutelyContinuous P hX hZmeas hZ_ac
  have hent_n : Integrable
      (fun x => Real.negMulLog (((condTrunc P X Y n).map Z).rnDeriv volume x).toReal) volume :=
    integrable_negMulLog_map_condTrunc P hX hY hXY hZ hZ_ac hZ_ent hpos
  show ENNReal.ofReal (Real.exp (2 * differentialEntropy ((condTrunc P X Y n).map Z)))
      = entropyPowerExt ((condTrunc P X Y n).map Z)
  exact (entropyPowerExt_of_ac_integrable hac_n hent_n).symm

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
  -- Goal: `Nₑ(P.map X) + Nₑ(P.map Y) ≤ Nₑ(P.map(X+Y))`.
  rw [ge_iff_le]
  -- (1) RHS 収束: `Nₑ(P_n.map X) + Nₑ(P_n.map Y) → Nₑ(P.map X) + Nₑ(P.map Y)`.
  have hX_tendsto :
      Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map X)) atTop
        (𝓝 (entropyPowerExt (P.map X))) :=
    entropyPowerExt_map_condTrunc_tendsto P hX hY hXY (Or.inl rfl) hX_ac hX_ent
  have hY_tendsto :
      Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map Y)) atTop
        (𝓝 (entropyPowerExt (P.map Y))) :=
    entropyPowerExt_map_condTrunc_tendsto P hX hY hXY (Or.inr rfl) hY_ac hY_ent
  have hRHS_tendsto :
      Tendsto (fun n => entropyPowerExt ((condTrunc P X Y n).map X)
          + entropyPowerExt ((condTrunc P X Y n).map Y)) atTop
        (𝓝 (entropyPowerExt (P.map X) + entropyPowerExt (P.map Y))) :=
    hX_tendsto.add hY_tendsto
  -- (2) per-n 不等式 (eventually): `Nₑ(P_n.map X) + Nₑ(P_n.map Y) ≤ Nₑ(P_n.map(X+Y))`.
  have hper_n :
      ∀ᶠ n in atTop,
        entropyPowerExt ((condTrunc P X Y n).map X)
            + entropyPowerExt ((condTrunc P X Y n).map Y)
          ≤ entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω)) := by
    filter_upwards [eventually_measure_truncSet_pos P hX hY] with n hpos
    exact entropyPowerExt_condTrunc_add_ge P hX hY hXY hX_ac hY_ac hX_ent hY_ent hpos
  -- (3) limsup chain.
  calc
    entropyPowerExt (P.map X) + entropyPowerExt (P.map Y)
        = Filter.limsup (fun n => entropyPowerExt ((condTrunc P X Y n).map X)
            + entropyPowerExt ((condTrunc P X Y n).map Y)) atTop :=
          hRHS_tendsto.limsup_eq.symm
    _ ≤ Filter.limsup
          (fun n => entropyPowerExt ((condTrunc P X Y n).map (fun ω => X ω + Y ω))) atTop :=
          Filter.limsup_le_limsup hper_n
    _ ≤ entropyPowerExt (P.map (fun ω => X ω + Y ω)) :=
          entropyPowerExt_condTrunc_sum_limsup_le P hX hY hXY hX_ac hY_ac hent_sum

end InformationTheory.Shannon.EPIInfiniteVarianceTruncation
