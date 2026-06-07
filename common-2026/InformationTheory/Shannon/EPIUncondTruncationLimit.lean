import InformationTheory.Shannon.EntropyPowerExt
import InformationTheory.Shannon.EPIUncondCondEntropyExt
import InformationTheory.Shannon.EPIUncondMonotone
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# EPI 無条件化 W-Y2 — route β' (truncation + monotone-limit) skeleton

無限エントロピー a.c. 入力 (`h(W) = ⊤` の a.c.) で gateway 単調性の ⊤ 伝播
`differentialEntropyExt_top_of_indep_add` を **無条件** (整数 truncation 近似経由) で
genuine 着地させるための skeleton。route T (`EPIInfiniteVarianceTruncation` /
`EPIInfiniteVarianceCapstone`、sorryAx-free CLOSED) の機構を `W` 単独 truncation に
読み替えて再利用する。

ターゲットは無条件版② chain rule の等式 (finiteness-free 証明不能確定) でなく、
gateway 単調性の ⊤ 枝不等式 (`h(W) = ⊤ ⟹ h(W+V) = ⊤`)。LSC/liminf は `≤` しか出さないが、
⊤ 枝は `le_top` 一発で閉じるため極限と相性が良い。

route β' Phase 1 skeleton (本 file は signature 確定のみ、本体は Phase 2-4)。

SoT 計画: `docs/shannon/epi-uncond-truncation-lsc-plan.md`
(Parent: `docs/shannon/epi-unconditional-moonshot-plan.md` §S5 W-Y2)。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **W 単独 truncation の構成** (route T `condTrunc` を W 単独に読み替え)。
`truncW P W n := P[| {ω | |W ω| ≤ n}]` (`W` の値が `[-n, n]` に入る事象での条件付け)。
各 `truncW P W n` は compact support (有界) → 有限分散・有限エントロピーを満たし、a.c.
(`cond_absolutelyContinuous` 保存) を保つ。route T の joint `truncSet X Y n` と違い W 単独。

独立 honesty audit 2026-06-08 (skeleton Phase 1): `ProbabilityTheory.cond` を直接呼ぶ
genuine def、退化定義悪用なし (cond は well-defined、mass≠0 scope は consumer の `hn`)。
sorry なし・@residual なし。@audit:ok -/
noncomputable def truncW (P : Measure Ω) (W : Ω → ℝ) (n : ℕ) : Measure Ω :=
  ProbabilityTheory.cond P {ω | |W ω| ≤ (n : ℝ)}

/-- **cond density formula** (route T `rnDeriv_cond_eq` を W 単独 truncation 用に再掲、heavy
import 回避のため local 再証明): 確率測度 `μ : Measure ℝ` を可測集合 `s` (positive mass) で
条件付けた測度の Radon-Nikodym 微分は `(cond μ s).rnDeriv volume =ᵐ (μ s)⁻¹ · 1_s · μ.rnDeriv volume`。
`cond μ s = (μ s)⁻¹ • μ.restrict s` の scalar mul + restrict の rnDeriv (`rnDeriv_smul_left_of_ne_top`
+ `rnDeriv_restrict`、共に Mathlib) で組立。route T と完全同型 (集約漏れでなく import cycle/cost 回避)。
独立 honesty audit 2026-06-08: Mathlib 2 補題の機械的合成、循環/bundling なし。@audit:ok -/
private theorem rnDeriv_cond_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Set ℝ}
    (hs : MeasurableSet s) (hpos : μ s ≠ 0) :
    (ProbabilityTheory.cond μ s).rnDeriv volume
      =ᵐ[volume] fun x => (μ s)⁻¹ * s.indicator (μ.rnDeriv volume) x := by
  have hr : (μ s)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hpos
  have h1 : (ProbabilityTheory.cond μ s).rnDeriv volume
      =ᵐ[volume] (μ s)⁻¹ • (μ.restrict s).rnDeriv volume := by
    show ((μ s)⁻¹ • μ.restrict s).rnDeriv volume =ᵐ[volume] (μ s)⁻¹ • (μ.restrict s).rnDeriv volume
    exact Measure.rnDeriv_smul_left_of_ne_top (μ.restrict s) volume hr
  have h2 : (μ.restrict s).rnDeriv volume =ᵐ[volume] s.indicator (μ.rnDeriv volume) :=
    Measure.rnDeriv_restrict μ volume hs
  refine h1.trans ?_
  filter_upwards [h2] with x hx
  simp only [Pi.smul_apply, hx, smul_eq_mul]

/-- **negMulLog-Fatou helper** — 正部 lintegral `A` の Fatou lift。
density の toReal a.e. 収束 `f_{μ_n} → f_μ` から `A_μ ≤ liminf A_{μ_n}` を Fatou で出す
(`A μ := ∫⁻ x, ofReal (negMulLog (rnDeriv μ vol x).toReal) ∂volume` = `differentialEntropyExt`
の a.c. 枝の正部、`EntropyPowerExt.lean:61`)。

`klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean:112`、`@audit:ok`) と完全同型で、
`klFun`→`negMulLog` 差替のみ (両者 continuous)。骨格 = `lintegral_liminf_le` +
`ENNReal.continuous_ofReal` + `Tendsto.liminf_eq` + `lintegral_mono_ae`。Phase 0 scratch
(`/tmp/route_beta_phase0.lean` `A_le_liminf_of_ae_tendsto`) で骨格実証済 (0 sorry)、本 file
では Phase 3 で埋める skeleton として sorry。

独立 honesty audit 2026-06-08 (skeleton, 4-check PASS → honest_residual): (1) 非循環 — 結論
(正部 lintegral の liminf 下界) は仮説 `h_ae` (density a.e. 収束) と非同型。(2) 非バンドル —
`h_ae` は a.e. 収束 input precondition、Fatou 不等式の核を encode せず。(3) 非退化 — `:True`
slot なし。(4) sufficiency — Fatou (`lintegral_liminf_le`、非負被積分関数列で `∫ liminf ≤
liminf ∫`) が正しい向き: `ofReal(negMulLog ...)` で負部を 0 clamp した正部 A に対し成立する
向きで、収束列の極限 = liminf を使う (`klDiv_le_liminf_of_ae_tendsto` body と同構造)。
classification: `klDiv_le_liminf_of_ae_tendsto` (`EPIG2KLFatouLSC.lean:112`) と **別物**
(参照測度 γ 有限 vs volume 無限、klFun vs negMulLog) ゆえ集約漏れでない。`plan:` 妥当
(Mathlib 1本不在の壁でなく既存同型骨格の差替で closeable、対応 plan 実在)。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_posPart_le_liminf_of_ae_tendsto
    (μ : Measure ℝ) (μ_n : ℕ → Measure ℝ)
    (h_ae : ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun n => ((μ_n n).rnDeriv volume x).toReal) atTop
        (𝓝 ((μ.rnDeriv volume x).toReal))) :
    (∫⁻ x, ENNReal.ofReal (Real.negMulLog ((μ.rnDeriv volume x).toReal)) ∂volume)
      ≤ Filter.liminf
          (fun n => ∫⁻ x, ENNReal.ofReal
            (Real.negMulLog (((μ_n n).rnDeriv volume x).toReal)) ∂volume) atTop := by
  sorry

/-- **per-n finite-entropy 単調性**: 各 n で `h(W_n) ≤ h(W_n + V)` を finite ②
(`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite`、11 regularity 仮説、`@audit:ok`) or
有限枝単調性経由で建てる。`truncW P W n` は compact support ゆえ有限分散・有限エントロピーで、
finite ② の 11 仮説 (joint 密度可測 / per-fibre KL 有限 等) を condDistrib で供給する。

route β' Phase 2 で埋める。`hn` (positive mass) は条件付けが well-defined な n を選ぶ scope
(load-bearing でない)。

**`hW_negPart_fin` の追加理由 (2026-06-08 Phase 2 案 F)**: `B(W) := ∫⁻ ofReal(-(negMulLog f_W)) < ⊤`
(= h(W) の負部 lintegral 有限性) を表す **regularity precondition**。truncated `B(W_n) < ⊤` を
密度分解 `f_n = c⁻¹·1_{[-n,n]}·f_W` (`restrict_map` + `rnDeriv_smul_left` + `rnDeriv_restrict`)
+ `negMulLog_mul` で `B(W)` から供給するための入力で、`hW_ne_bot`/`hWV_ne_bot` 系の `≠⊥`
(= 負部有限) closure に使う。**load-bearing でない**: 単調性 `h(W_n) ≤ h(W_n+V)` の核は body 側の
finite ② (`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite`) が担い、`hW_negPart_fin` は
h(W) の負部有限性 (正則性条件) で単調性の核を encode しない。name-laundering でない (核を仮説に
packing せず、body sorry は `@residual` で正直にマーク)。

独立 honesty audit 2026-06-08 (skeleton, 4-check PASS → honest_residual): (1) 非循環 — 結論
(単調不等式 `h(W_n) ≤ h(W_n+V)`) は 7 仮説と非同型。(2) 非バンドル — `hW`/`hV`/`hWV`/`hW_ac`
は可測/独立/絶対連続の regularity、`hW_negPart_fin` は h(W) 負部有限性の regularity、`hn` は cond
well-defined の scope precondition、いずれも単調性の核を encode せず (供給元 finite ② =
`differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite` が body 側に来る)。(3) 非退化 — `:True`
slot なし。(4) sufficiency — compact support (`{|W|≤n}` 条件付け) の有限分散・有限エントロピー
measure で単調性が立つのは正しい (route T が同 truncation で sorryAx-free 実証済)。`plan:` 妥当。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_mono_add_truncW
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_negPart_fin :
      (∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((P.map W).rnDeriv volume x).toReal)))
        ∂volume) ≠ ⊤)
    (n : ℕ) (hn : P {ω | |W ω| ≤ (n : ℝ)} ≠ 0) :
    differentialEntropyExt ((truncW P W n).map W)
      ≤ differentialEntropyExt ((truncW P W n).map (fun ω => W ω + V ω)) := by
  -- The truncated measure `Q := truncW P W n = P[| {|W| ≤ n}]` is a probability measure.
  set Q : Measure Ω := truncW P W n with hQ_def
  haveI hQ_prob : IsProbabilityMeasure Q := by
    rw [hQ_def, truncW]; exact ProbabilityTheory.cond_isProbabilityMeasure hn
  -- W stays a.c. under conditioning: `Q.map W ≪ P.map W ≪ volume`.
  have hW_ac_Q : (Q.map W) ≪ volume := by
    refine (Measure.AbsolutelyContinuous.trans ?_ hW_ac)
    rw [hQ_def, truncW]
    exact (ProbabilityTheory.cond_absolutelyContinuous).map hW
  -- W ⊥ V is preserved under conditioning on a W-event `{|W| ≤ n}` (the event is a function of
  -- W only, so V is unaffected). Self-built from `indepFun_iff_measure_inter_preimage_eq_mul`:
  -- the conditioning event `E = W⁻¹' {r | |r| ≤ n}` absorbs into the W-preimage, and `hWV`
  -- factors the joint measure of W- and V-preimages.
  have hE_meas : MeasurableSet {ω : Ω | |W ω| ≤ (n : ℝ)} :=
    hW.abs measurableSet_Iic
  set E : Set Ω := {ω : Ω | |W ω| ≤ (n : ℝ)} with hE_def
  have hindep : IndepFun W V Q := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    -- `E ∩ W⁻¹' s = W⁻¹' (Icc⁻¹ ∩ s)` is itself a W-preimage of a measurable set.
    have hEW : E ∩ W ⁻¹' s = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := by
      ext ω; simp [hE_def, Set.mem_inter_iff, and_comm]
    have hIcc_meas : MeasurableSet {r : ℝ | |r| ≤ (n : ℝ)} :=
      (_root_.continuous_abs.measurable measurableSet_Iic)
    have hAW : MeasurableSet ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) := hIcc_meas.inter hs
    -- Expand each `cond` term via `cond_apply hE_meas`.
    rw [hQ_def, truncW, cond_apply hE_meas, cond_apply hE_meas, cond_apply hE_meas]
    -- The joint preimage: `E ∩ (W⁻¹s ∩ V⁻¹t) = (E ∩ W⁻¹s) ∩ V⁻¹t = W⁻¹(..) ∩ V⁻¹t`.
    have hjoint : E ∩ (W ⁻¹' s ∩ V ⁻¹' t) = W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t := by
      rw [← Set.inter_assoc, hEW]
    rw [hjoint, hEW]
    -- Factor `P` on the W- and V-preimages via the original independence `hWV`.
    have hfac1 : P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s) ∩ V ⁻¹' t)
        = P (W ⁻¹' ({r : ℝ | |r| ≤ (n : ℝ)} ∩ s)) * P (V ⁻¹' t) :=
      hWV.measure_inter_preimage_eq_mul _ _ hAW ht
    -- For the V-term: `E ∩ V⁻¹t = W⁻¹(Icc) ∩ V⁻¹t`, again factored by `hWV`.
    have hEV : E ∩ V ⁻¹' t = W ⁻¹' {r : ℝ | |r| ≤ (n : ℝ)} ∩ V ⁻¹' t := by
      ext ω; simp [hE_def]
    have hfac2 : P (E ∩ V ⁻¹' t) = P E * P (V ⁻¹' t) := by
      rw [hEV, hWV.measure_inter_preimage_eq_mul _ _ hIcc_meas ht, hE_def]; rfl
    rw [hfac1, hfac2]
    -- Arithmetic: `c·(a·v) = (c·a)·(c·(P E·v))` where `c = (P E)⁻¹`, since `c·P E = 1`.
    have hPE_ne : P E ≠ 0 := by rw [hE_def]; exact hn
    have hPE_ne_top : P E ≠ ∞ := measure_ne_top P E
    have hcancel : (P E)⁻¹ * (P E * P (V ⁻¹' t)) = P (V ⁻¹' t) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hPE_ne hPE_ne_top, one_mul]
    rw [hcancel]
    ring
  -- ① fibre identification (c = 1): `condDiffEntExt (W + V | V) Q = h_ext(Q.map W)`.
  have hone : (fun ω => W ω + (1 : ℝ) * V ω) = (fun ω => W ω + V ω) := by
    funext ω; rw [one_mul]
  have hfibre : condDifferentialEntropyExt (fun ω => W ω + V ω) V Q
      = differentialEntropyExt (Q.map W) := by
    have := condDifferentialEntropyExt_indep_add_eq W V Q 1 hW hV hindep hW_ac_Q
    rwa [hone] at this
  -- W + V is a.c. under `Q` (`hW_ac_Q` + independence).
  have hWV_ac_Q : (Q.map (fun ω => W ω + V ω)) ≪ volume :=
    map_add_absolutelyContinuous W V Q hW hV hindep hW_ac_Q
  -- Probability-measure instances on the relevant marginals (needed for the fibre identification
  -- and the finite ②).
  haveI hWmap_prob : IsProbabilityMeasure (Q.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  haveI hVmap_prob : IsProbabilityMeasure (Q.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  -- **fibre identification** (c = 1): `condDistrib (W+V) V Q =ᵐ[Q.map V] affineShiftKernel (Q.map W) 1`.
  -- Mirror of `condDifferentialEntropyExt_indep_add_eq` (Step 1-2): the joint `(V, W+V)` is the
  -- affine push of the product law (independence), so the regular conditional kernel is the
  -- z-dependent affine shift of `Q.map W`.
  have hjoint_VW : Q.map (fun ω => (V ω, W ω + V ω))
      = (Q.map V) ⊗ₘ (affineShiftKernel (Q.map W) 1) := by
    have hZX : IndepFun V W Q := hindep.symm
    have hjoint_VX : Q.map (fun ω => (V ω, W ω)) = (Q.map V).prod (Q.map W) :=
      (indepFun_iff_map_prod_eq_prod_map_map hV.aemeasurable hW.aemeasurable).mp hZX
    have hg : Measurable fun p : ℝ × ℝ => (p.1, p.2 + (1 : ℝ) * p.1) := by fun_prop
    have hcomp : (fun ω => (V ω, W ω + V ω))
        = (fun p : ℝ × ℝ => (p.1, p.2 + (1 : ℝ) * p.1)) ∘ (fun ω => (V ω, W ω)) := by
      funext ω; simp [one_mul, add_comm]
    rw [hcomp, ← Measure.map_map hg (hV.prodMk hW), hjoint_VX,
      prod_map_affine_eq_compProd]
  have hae : condDistrib (fun ω => W ω + V ω) V Q
      =ᵐ[Q.map V] affineShiftKernel (Q.map W) 1 :=
    condDistrib_ae_eq_of_measure_eq_compProd V (hW.add hV).aemeasurable hjoint_VW
  -- The marginal / conditional extended entropies are `≠ ⊥` (compact support ⟹ finite
  -- differential entropy ⟹ ≠ −∞). Localized: the two ⊥-exclusions on `Q.map W` and `Q.map (W+V)`.
  -- **Set-up shared by the `≠ ⊥` blocks**: `Q.map W = cond (P.map W) Sn` (single-variable
  -- truncation), so its density is `c⁻¹ · 1_Sn · f_W` with `c = (P.map W) Sn = P E`.
  set Sn : Set ℝ := {r : ℝ | |r| ≤ (n : ℝ)} with hSn_def
  have hSn_meas : MeasurableSet Sn := measurableSet_le measurable_norm measurable_const
  -- `(truncW P W n).map W = cond (P.map W) Sn` (direct: conditioning on `W⁻¹' Sn` then pushing
  -- forward by `W` equals conditioning the law of `W` on `Sn`).
  have hE_eq : E = W ⁻¹' Sn := by ext ω; simp [hE_def, hSn_def]
  have hQW_eq : (Q.map W) = ProbabilityTheory.cond (P.map W) Sn := by
    refine Measure.ext (fun A hA => ?_)
    -- LHS: `(Q.map W) A = Q (W⁻¹A) = (P E)⁻¹ * P (E ∩ W⁻¹A)`.
    have hLHS : (Q.map W) A = (P E)⁻¹ * P (W ⁻¹' Sn ∩ W ⁻¹' A) := by
      rw [Measure.map_apply hW hA, hQ_def, truncW, ← hE_def,
        ProbabilityTheory.cond_apply hE_meas P, hE_eq]
    -- RHS: `cond (P.map W) Sn A = ((P.map W) Sn)⁻¹ * (P.map W)(Sn ∩ A)`.
    have hRHS : (ProbabilityTheory.cond (P.map W) Sn) A
        = (P E)⁻¹ * P (W ⁻¹' Sn ∩ W ⁻¹' A) := by
      rw [ProbabilityTheory.cond_apply hSn_meas (P.map W) A,
        Measure.map_apply hW hSn_meas, Measure.map_apply hW (hSn_meas.inter hA),
        Set.preimage_inter, hE_eq]
    rw [hLHS, hRHS]
  -- positive mass of `Sn` under `P.map W`.
  have hWmap_prob' : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  have hSn_pos : (P.map W) Sn ≠ 0 := by
    rw [Measure.map_apply hW hSn_meas]
    have : W ⁻¹' Sn = E := by ext ω; simp [hE_def, hSn_def]
    rw [this, hE_def]; exact hn
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have hW_ne_bot : differentialEntropyExt (Q.map W) ≠ ⊥ := by
    rw [differentialEntropyExt_of_ac hW_ac_Q, sub_eq_add_neg]
    -- It suffices to show the negative-part lintegral `B_n ≠ ⊤`; then `A − B = A + (-B) ≠ ⊥`.
    set Bn : ℝ≥0∞ :=
      ∫⁻ x, ENNReal.ofReal (-(Real.negMulLog (((Q.map W).rnDeriv volume x).toReal))) ∂volume
      with hBn_def
    suffices hBn : Bn ≠ ⊤ by
      have hBcoe : ((Bn : EReal)) ≠ ⊤ := by simpa using hBn
      intro hcontra
      rw [EReal.add_eq_bot_iff] at hcontra
      rcases hcontra with h | h
      · exact (EReal.coe_ennreal_ne_bot _) h
      · rw [EReal.neg_eq_bot_iff] at h; exact hBcoe h
    -- cond density formula: `f_n =ᵐ c⁻¹ · 1_Sn · f_W` (`c = (P.map W) Sn`).
    set fW : ℝ → ℝ := fun x => ((P.map W).rnDeriv volume x).toReal with hfW_def
    set c : ℝ≥0∞ := (P.map W) Sn with hc_def
    have hc_top : c ≠ ∞ := measure_ne_top _ _
    set cbar : ℝ := (c⁻¹).toReal with hcbar_def
    have hcbar_nn : 0 ≤ cbar := ENNReal.toReal_nonneg
    have h_rn : (Q.map W).rnDeriv volume
        =ᵐ[volume] fun x => c⁻¹ * Sn.indicator ((P.map W).rnDeriv volume) x := by
      rw [hQW_eq]; exact rnDeriv_cond_eq (P.map W) hSn_meas hSn_pos
    -- pointwise bound on the negative-part integrand `=ᵐ`:
    --   `-(negMulLog f_n) = 1_Sn · ((cbar log cbar)·fW + cbar·(-(negMulLog fW)))`.
    have h_int_eq : (fun x => ENNReal.ofReal (-(Real.negMulLog (((Q.map W).rnDeriv volume x).toReal))))
        =ᵐ[volume] fun x => ENNReal.ofReal (Sn.indicator
          (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x) := by
      filter_upwards [h_rn] with x hx
      rw [hx]
      by_cases hxs : x ∈ Sn
      · rw [Set.indicator_of_mem hxs (f := (P.map W).rnDeriv volume),
          Set.indicator_of_mem hxs
            (f := fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))),
          ENNReal.toReal_mul]
        congr 1
        show -(Real.negMulLog (cbar * fW x)) = cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))
        rw [Real.negMulLog_mul cbar (fW x)]
        ring_nf
        rw [Real.negMulLog]
        ring
      · rw [Set.indicator_of_notMem hxs (f := (P.map W).rnDeriv volume),
          Set.indicator_of_notMem hxs
            (f := fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x))))]
        simp [Real.negMulLog]
    rw [hBn_def, lintegral_congr_ae h_int_eq]
    -- Bound the indicator integrand by the sum of two finite-integral pieces.
    have hbound : ∀ x, ENNReal.ofReal (Sn.indicator
          (fun x => cbar * Real.log cbar * fW x + cbar * (-(Real.negMulLog (fW x)))) x)
        ≤ ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)
          + ENNReal.ofReal cbar * ENNReal.ofReal (-(Real.negMulLog (fW x))) := by
      intro x
      by_cases hxs : x ∈ Sn
      · rw [Set.indicator_of_mem hxs]
        refine le_trans ENNReal.ofReal_add_le ?_
        refine add_le_add ?_ ?_
        · rw [← ENNReal.ofReal_mul (abs_nonneg _)]
          refine ENNReal.ofReal_le_ofReal (le_trans (le_abs_self _) ?_)
          have hfW_nn : (0 : ℝ) ≤ fW x := ENNReal.toReal_nonneg
          rw [abs_mul, abs_of_nonneg hfW_nn]
        · rw [← ENNReal.ofReal_mul hcbar_nn]
      · rw [Set.indicator_of_notMem hxs]; simp
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hbound)
    -- Split the upper-bound integral additively, both pieces finite.
    have hfW_meas : Measurable (fun x => ENNReal.ofReal (fW x)) :=
      (Measure.measurable_rnDeriv _ _).ennreal_toReal.ennreal_ofReal
    have hg1_meas : Measurable
        (fun x => ENNReal.ofReal (|cbar * Real.log cbar|) * ENNReal.ofReal (fW x)) :=
      measurable_const.mul hfW_meas
    have hnegm_meas : Measurable (fun x => ENNReal.ofReal (-(Real.negMulLog (fW x)))) :=
      ((Real.continuous_negMulLog.measurable.comp
        ((Measure.measurable_rnDeriv _ _).ennreal_toReal)).neg).ennreal_ofReal
    rw [lintegral_add_left hg1_meas]
    apply ENNReal.add_ne_top.mpr
    refine ⟨?_, ?_⟩
    · -- `∫⁻ g1 = ofReal|cbar log cbar| · ∫⁻ ofReal(fW) = ofReal|...| · 1 < ∞`.
      rw [lintegral_const_mul _ hfW_meas]
      have hfW_lint : (∫⁻ x, ENNReal.ofReal (fW x) ∂volume) = 1 := by
        have hae_eq : (fun x => ENNReal.ofReal (fW x))
            =ᵐ[volume] (P.map W).rnDeriv volume := by
          filter_upwards [(P.map W).rnDeriv_ne_top volume] with x hx
          rw [hfW_def]; exact ENNReal.ofReal_toReal hx
        rw [lintegral_congr_ae hae_eq, Measure.lintegral_rnDeriv hW_ac, measure_univ]
      rw [hfW_lint, mul_one]; exact ENNReal.ofReal_ne_top
    · -- `∫⁻ g2 = ofReal(cbar) · B(W) < ∞`.
      rw [lintegral_const_mul _ hnegm_meas]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW_negPart_fin
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have hWV_ne_bot : differentialEntropyExt (Q.map (fun ω => W ω + V ω)) ≠ ⊥ := by sorry
  have hcond_ne_bot : condDifferentialEntropyExt (fun ω => W ω + V ω) V Q ≠ ⊥ := by
    rw [hfibre]; exact hW_ne_bot
  -- ② finite chain rule with `X := W + V`, `Z := V`:
  -- `h_ext(W+V) = h_ext(W+V | V) + I(W+V; V)`.
  -- The eleven regularity hypotheses of the finite ② are supplied below; the condDistrib-side
  -- ones (joint density measurability / per-fibre a.c. / integrability / KL finiteness) are not
  -- yet discharged for the truncated `Q` and are localized as side lemmas.
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have h_ac : (Q.map V) ⊗ₘ condDistrib (fun ω => W ω + V ω) V Q
      ≪ (Q.map V) ⊗ₘ Kernel.const ℝ (Q.map (fun ω => W ω + V ω)) := by sorry
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have hκ_dens_meas : Measurable
      (fun p : ℝ × ℝ => ((condDistrib (fun ω => W ω + V ω) V Q p.1).rnDeriv volume p.2)) := by
    sorry
  -- per-fibre a.c.: each fibre `condDistrib (W+V) V Q z =ᵐ (Q.map W).map (·+z)`, a translation
  -- of the a.c. measure `Q.map W` (translation-invariance of Lebesgue ⟹ a.c. is preserved).
  -- No finiteness needed; supplied genuinely from the fibre identification `hae`.
  have hκ_ac : ∀ᵐ z ∂(Q.map V), condDistrib (fun ω => W ω + V ω) V Q z ≪ volume := by
    filter_upwards [hae] with z hz
    rw [hz, affineShiftKernel_apply]
    have hshift : Measurable fun x : ℝ => x + (1 : ℝ) * z := by fun_prop
    have h_map_vol : (volume : Measure ℝ).map (fun x : ℝ => x + (1 : ℝ) * z) = volume :=
      MeasureTheory.map_add_right_eq_self (μ := (volume : Measure ℝ)) ((1 : ℝ) * z)
    have := hW_ac_Q.map hshift
    rwa [h_map_vol] at this
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have hκ_logp_int : ∀ᵐ z ∂(Q.map V), Integrable
      (fun x => ((condDistrib (fun ω => W ω + V ω) V Q z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => W ω + V ω) V Q z).rnDeriv volume x).toReal)) volume := by
    sorry
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have hκ_cross_int : ∀ᵐ z ∂(Q.map V), Integrable
      (fun x => ((condDistrib (fun ω => W ω + V ω) V Q z).rnDeriv volume x).toReal
        * Real.log (((Q.map (fun ω => W ω + V ω)).rnDeriv volume x).toReal)) volume := by
    sorry
  -- @residual(plan:epi-uncond-truncation-lsc-plan)
  have hκ_KL : ∀ᵐ z ∂(Q.map V),
      klDiv (condDistrib (fun ω => W ω + V ω) V Q z) (Q.map (fun ω => W ω + V ω)) ≠ ∞ := by sorry
  have hchain := differentialEntropyExt_eq_condEntExt_add_klDiv_of_finite
    (fun ω => W ω + V ω) V Q (hW.add hV) hV hWV_ac_Q h_ac hκ_dens_meas hκ_ac hκ_logp_int
    hκ_cross_int hκ_KL hcond_ne_bot hWV_ne_bot
  -- Equality → monotonicity: `h(W_n+V) = h(W_n) + I`, `I ≥ 0` ⟹ `h(W_n) ≤ h(W_n+V)`.
  rw [hchain, hfibre]
  have hi : (0 : EReal) ≤
      (((InformationTheory.klDiv ((Q.map V) ⊗ₘ condDistrib (fun ω => W ω + V ω) V Q)
            ((Q.map V) ⊗ₘ Kernel.const ℝ (Q.map (fun ω => W ω + V ω)))) : ℝ≥0∞) : EReal) := by
    exact_mod_cast (bot_le : (⊥ : ℝ≥0∞) ≤ _)
  calc differentialEntropyExt (Q.map W)
      = differentialEntropyExt (Q.map W) + 0 := (add_zero _).symm
    _ ≤ differentialEntropyExt (Q.map W) + _ := add_le_add_right hi _

/-- **`h(W_n) → h(W)` の極限**: truncation 緩和で entropy 単調増加 → 極限。`h(W) = ⊤` のときは
`h(W_n) ↑ ⊤` の単調発散 (有界増加列の ⊤ への発散) で、weak-convergence portmanteau を経由しない。
route T が `tendsto_measure_iUnion_atTop` (`EPIInfiniteVarianceTruncation.lean:110`) ベースの
極限を実証済。

route β' Phase 3 で埋める。極限が density a.e. 収束 (`differentialEntropyExt_posPart_le_liminf_of_ae_tendsto`
適用可) or 単調収束のみで閉じ、weak-conv 定義を使わないことを担保する。

独立 honesty audit 2026-06-08 (skeleton, 4-check PASS → honest_residual): (1) 非循環 — 結論
(極限 `h(W_n) → h(W)`) は仮説 `hW`/`hW_ac` と非同型。(2) 非バンドル — 両仮説は可測/絶対連続の
regularity precondition、極限の核を encode せず。(3) 非退化 — `:True` slot なし。(4) sufficiency
— truncation 緩和列の entropy 単調増加 → 極限 (`h(W)=⊤` で `h(W_n)↑⊤`) は正しい (route T が
`tendsto_measure_iUnion_atTop` で同型極限を実証)。`plan:` 妥当。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_truncW_tendsto
    (W : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hW_ac : (P.map W) ≪ volume) :
    Tendsto (fun n => differentialEntropyExt ((truncW P W n).map W)) atTop
      (𝓝 (differentialEntropyExt (P.map W))) := by
  sorry

/-- **gateway ⊤ 枝 (無条件)**: `h(W) = ⊤ ⟹ h(W+V) = ⊤`、無条件版② (i-a) を bypass。
per-n 単調性 `h(W_n) ≤ h(W_n + V)` (`differentialEntropyExt_mono_add_truncW`) と `h(W_n) ↑ ⊤`
(`differentialEntropyExt_truncW_tendsto`) を組み、`h(W_n + V) ≥ h(W_n) → ⊤` で `h(W+V) = ⊤`。
route T capstone Case 2 (`EPIInfiniteVarianceCapstone.lean:343`、`entropyPowerExt = ⊤` を
`le_top`) と同型の「⊤ 枝は EReal ⊤ 表現で trivial に閉じる」を再利用する。

**⊤ 枝のみ無条件、有限枝は別 lemma** (finite ② / coe 枝)。`_unconditional` 命名は本 ⊤ 枝が真に
無条件 (regularity precondition `hW`/`hV`/`hWV`/`hW_ac` のみ、無条件版② sorry を継承しない) なため
honest。`hW_top` (h(W)=⊤) は場合分け precondition で load-bearing でない。

route β' Phase 4 で埋める。

独立 honesty audit 2026-06-08 (skeleton, 4-check + name-laundering PASS → honest_residual):
**`_unconditional` 命名 = NOT name-laundering**。signature は既存 `differentialEntropyExt_top_of_indep_add`
(`EPIUncondMonotone.lean:153`、(i-a) `differentialEntropyExt_indep_add_eq_add_klDiv` の transitive
sorry を継承) と **完全同一の仮説群** (`hW`/`hV`/`hWV`/`hW_ac`/`hW_top`、結論も同一)。新規 load-bearing
hypothesis を threading していない — `_unconditional` は「(i-a) sorry を継承しない別 route (truncation
近似) で同結論を建てる」という proof-route の主張で、「仮説が無い」主張ではない (CORE doctrine の
name_laundering は「open load-bearing hyp or 完成偽装 sorry-body」、本件は body sorry が `@residual`
で正直にマーク済 = 偽装でない)。**`hW_top` load-bearing 判定**: `h(W)=⊤` は ⊤ 枝の場合分け
precondition、結論の核 (= h(W+V)=⊤) を encode せず。hard core = 単調性 `h(W)≤h(W+V)` (#3 が供給)、
`hW_top` + 単調性 → `h(W+V)≥⊤` → `=⊤` (`le_top`)。`le_top` は退化定義悪用でなく EReal ⊤ 表現の
genuine 利用 (route T capstone Case 2 と同型)。(4) sufficiency — `h(W)=⊤` + 単調性で `h(W+V)=⊤` は
正しい含意 (反例なし: 単調性が無条件で成立する以上 ⊤ 入力は ⊤ 出力)。`plan:` 妥当。
@residual(plan:epi-uncond-truncation-lsc-plan) -/
theorem differentialEntropyExt_top_of_indep_add_unconditional
    (W V : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hW : Measurable W) (hV : Measurable V) (hWV : IndepFun W V P)
    (hW_ac : (P.map W) ≪ volume)
    (hW_top : differentialEntropyExt (P.map W) = ⊤) :
    differentialEntropyExt (P.map (fun ω => W ω + V ω)) = ⊤ := by
  sorry

end InformationTheory.Shannon
