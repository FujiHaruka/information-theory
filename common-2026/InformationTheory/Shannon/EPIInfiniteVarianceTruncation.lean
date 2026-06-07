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

namespace InformationTheory.Shannon.EPIInfiniteVarianceTruncation

open MeasureTheory Filter Real ProbabilityTheory
open InformationTheory.Shannon
open InformationTheory.Shannon.EntropyPowerInequality
open InformationTheory.Shannon.EPICase1SmoothingLimit
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

/-- **per-n 和の有限微分エントロピー** (`hent_sum` 再供給)。compact support の和 X+Y も
有界密度 → integrable。黒箱 `entropyPowerExt_add_ge_of_finite_variance` は `hent_sum` を
明示引数で要求するので必須 (wall theorem 側には無い、在庫 §D)。 -/
theorem integrable_negMulLog_map_condTrunc_sum (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume) (hXY : IndepFun X Y P)
    {n : ℕ} (hpos : P (truncSet X Y n) ≠ 0) :
    Integrable
      (fun x => Real.negMulLog
        (((condTrunc P X Y n).map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume := by
  -- @residual(plan:epi-infinite-variance-truncation-plan)
  sorry

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
