import InformationTheory.Shannon.EPIUncondMixedCase
import InformationTheory.Shannon.EPICase1SmoothingLimit

/-!
# EPI 無条件化 — case-1 dispatch (Pivot B Phase 3)

`docs/shannon/epi-finitevar-smoothing-limit-plan.md` の Phase 3。`EPIUncondMixedCase.lean`
の 4-case dispatch (`entropyPowerExt_add_ge_dispatch_skeleton`) と case-1 named wall
(`entropyPowerExt_add_ge_finite_ac`) を本 file に集約する。

**なぜ別 file か (import cycle 回避)**: case-1 の両 a.c. 古典 EPI は有限分散 sub-case を
`EPICase1SmoothingLimit.entropyPowerExt_add_ge_of_finite_variance` (smoothing-limit closure、
sorryAx-free) に delegate したい。しかし `EPICase1SmoothingLimit` は (transitive に
`EPIDensityForm → EPICase1RatioLimit → EPIUncondMixedCase` 経由で) `EPIUncondMixedCase` の
低レベル補題 (`map_add_absolutelyContinuous` / `differentialEntropy_add_ge_of_indep`) を import
している。したがって `EPIUncondMixedCase` 自身に `import EPICase1SmoothingLimit` を足すと
import cycle (Lean は "already been declared" で拒否、機械確認 2026-06-06)。dispatch +
case-1 wall を両 file (`EPIUncondMixedCase` + `EPICase1SmoothingLimit`) の **下流** に置くこと
で cycle を断ち、delegation を成立させる。dispatch の in-tree code consumer は 0 件
(`rg` で確認、docs 言及のみ) ゆえ移動の影響は最小。

**case-1 (両 a.c.) の有限分散 / 無限分散 分解**: case-1 古典 EPI を分散の有無で 2 分:
* **有限分散**: `entropyPowerExt_add_ge_of_finite_variance` (smoothing-limit、genuine) に
  delegate。残る transitive sorry は和の有限微分エントロピー (`hent_sum`) のみ
  (`@residual(plan:epi-finitevar-smoothing-limit-plan)`)。
* **無限分散**: `entropyPowerExt_add_ge_infinite_variance` (Lieb-Young / Brascamp-Lieb 不在の
  genuine Mathlib 壁、`@residual(wall:epi-infinite-variance-classical)`)。

旧 bundled `wall:epi-finite-entropy-ac-classical` (両 a.c. 有限エントロピー古典 EPI の 1 本
sorry) は本 file で有限分散枝 (smoothing closure、残 hent_sum のみ) + 無限分散枝 (named wall)
の 2 本に **分解**された。`entropyPowerExt_add_ge_finite_ac` 自身は delegation のみで own sorry
を持たず、transitive sorry は hent_sum [plan] + infinite-variance [wall] の 2 本。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **case 1 残核 — 両 a.c. + 両有限エントロピーの classical EPI**。

両 a.c. かつ両入力が有限微分エントロピー (negMulLog density 可積分) のとき EPI
`N(X+Y) ≥ N(X) + N(Y)`。これは古典 EPI そのもの。有限分散 / 無限分散で `by_cases` 分割:

* **有限分散** (`hfv : Integrable (·²) X ∧ Integrable (·²) Y`):
  `EPICase1SmoothingLimit.entropyPowerExt_add_ge_of_finite_variance` (smoothing→正則化 limit
  closure、sorryAx-free) に delegate。唯一の追加入力 = 和の有限微分エントロピー `hent_sum`
  (`negMulLog ((P.map (X+Y)).rnDeriv volume ·).toReal` 可積分)。これは X+Y の有限微分エントロピー
  regularity precondition であって EPI を encode しない。残 transitive sorry は hent_sum 1 本
  (`@residual(plan:epi-finitevar-smoothing-limit-plan)`)。
* **無限分散** (`¬ hfv`):
  `EPICase1SmoothingLimit.entropyPowerExt_add_ge_infinite_variance` (Lieb-Young / Brascamp-Lieb
  不在の genuine Mathlib 壁、`@residual(wall:epi-infinite-variance-classical)`) に delegate。

本補題自身は delegation のみで own sorry 0、signature honest (`hX_ent`/`hY_ent` は有限微分
エントロピー regularity precondition、結論を encode しない)。transitive sorry は hent_sum [plan]
+ infinite-variance [wall] の 2 本。旧 bundled `wall:epi-finite-entropy-ac-classical` の分解先。
@residual(plan:epi-finitevar-smoothing-limit-plan,wall:epi-infinite-variance-classical) -/
theorem entropyPowerExt_add_ge_finite_ac
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  by_cases hfv : Integrable (fun ω => (X ω) ^ 2) P ∧ Integrable (fun ω => (Y ω) ^ 2) P
  · -- 有限分散: smoothing-limit closure に delegate。
    obtain ⟨h_mom_X, h_mom_Y⟩ := hfv
    have hent_sum : Integrable (fun x => Real.negMulLog
        (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume := by
      -- 和 X+Y の有限微分エントロピー (regularity precondition、EPI を encode しない)。
      -- @residual(plan:epi-finitevar-smoothing-limit-plan)
      sorry
    exact EPICase1SmoothingLimit.entropyPowerExt_add_ge_of_finite_variance
      P X Y hX hY hXY hX_ac hY_ac h_mom_X h_mom_Y hX_ent hY_ent hent_sum
  · -- 無限分散: genuine Mathlib 壁 (Lieb-Young / Brascamp-Lieb)。
    exact EPICase1SmoothingLimit.entropyPowerExt_add_ge_infinite_variance
      P X Y hX hY hXY hX_ac hY_ac hX_ent hY_ent hfv

/-- **Phase 5 — 3-case 判定 dispatch スケルトン**.

`P.map X ≪ volume` / `P.map Y ≪ volume` の 4 分岐で組む:
* 両 a.c. (**case 1**): named wall `entropyPowerExt_add_ge_finite_ac` (両有限エントロピーの
  classical EPI、有限分散 = smoothing closure / 無限分散 = named wall に分解) に置換。
  threaded `hX_ent`/`hY_ent` を再利用。
* X a.c. ∧ Y 特異 (case 2): `entropyPowerExt_mixed_add_ge` (+ X+Y path の integrability + `hX_ent`/`hW_ent`)。
* Y a.c. ∧ X 特異 (case 2 対称): `entropyPowerExt_mixed_add_ge_symm` (+ Y+X path の integrability + `hY_ent`/`hWyx_ent`)。
* 両特異 (case 3): `entropyPowerExt_singular_add_ge` (型自明、RHS=0)。

case 3 (両特異) 枝は `entropyPowerExt_singular_add_ge` 直接呼出で genuine に閉じる。
case 2 (X a.c. ∧ Y 特異) / case 2 対称 (Y a.c. ∧ X 特異) の 2 枝は、Phase 4 補題
`entropyPowerExt_mixed_add_ge` / `_symm` を **8 integrability + 2 finite-entropy precondition
つきで直接呼出** する。これらの integrability / finite-entropy は path 依存の honest regularity
precondition (X+Y path / Y+X path の a.c. 密度 + fibre regularity + 有限微分エントロピー、
**NOT load-bearing**)。case 1 枝 (両 a.c.) は named wall `entropyPowerExt_add_ge_finite_ac` 呼出に
delegate (threaded `hX_ent`/`hY_ent` を再利用)。

**全 4 枝 genuine か named wall delegation** (case 3 は vacuous でなく特異測度のエントロピーパワーが
真に 0、case 2 の前提は load-bearing でなく regularity precondition を Phase 4 補題に threading
するのみ、case 1 は named wall に delegation)。新 finite-entropy 前提 4 本は honest regularity
precondition (load-bearing でない)。dispatch 自身は own sorry 0、transitive sorry は case-1
named wall 由来 (hent_sum [plan] + infinite-variance [wall])。 -/
theorem entropyPowerExt_add_ge_dispatch_skeleton
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    -- case 2 (X a.c. ∧ Y 特異) 用 X+Y path の 8 integrability regularity precondition (NOT load-bearing)
    (h_ac : (P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P
        ≪ (P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω)))
    (h_int : Integrable
      (llr ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P)
        ((P.map Y) ⊗ₘ Kernel.const ℝ (P.map (fun ω => X ω + Y ω))))
      ((P.map Y) ⊗ₘ condDistrib (fun ω => X ω + Y ω) Y P))
    (hκ_v : ∀ᵐ z ∂(P.map Y),
      condDistrib (fun ω => X ω + Y ω) Y P z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(P.map Y), Integrable
      (fun x => ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => X ω + Y ω) Y P z)) (P.map Y))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => X ω + Y ω) Y P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) ∂volume) (P.map Y))
    (h_logq_int : Integrable
      (fun x => Real.log (((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal))
      (P.map (fun ω => X ω + Y ω)))
    -- case 2 対称 (Y a.c. ∧ X 特異) 用 Y+X path の 8 integrability regularity precondition (NOT load-bearing)
    (h_ac_symm : (P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P
        ≪ (P.map X) ⊗ₘ Kernel.const ℝ (P.map (fun ω => Y ω + X ω)))
    (h_int_symm : Integrable
      (llr ((P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P)
        ((P.map X) ⊗ₘ Kernel.const ℝ (P.map (fun ω => Y ω + X ω))))
      ((P.map X) ⊗ₘ condDistrib (fun ω => Y ω + X ω) X P))
    (hκ_v_symm : ∀ᵐ z ∂(P.map X),
      condDistrib (fun ω => Y ω + X ω) X P z ≪ volume)
    (hκ_logp_int_symm : ∀ᵐ z ∂(P.map X), Integrable
      (fun x => ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int_symm : ∀ᵐ z ∂(P.map X), Integrable
      (fun x => ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int_symm : Integrable
      (fun z => differentialEntropy (condDistrib (fun ω => Y ω + X ω) X P z)) (P.map X))
    (h_cross_int_symm : Integrable
      (fun z => ∫ x, ((condDistrib (fun ω => Y ω + X ω) X P z).rnDeriv volume x).toReal
        * Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal) ∂volume) (P.map X))
    (h_logq_int_symm : Integrable
      (fun x => Real.log (((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal))
      (P.map (fun ω => Y ω + X ω)))
    -- case 1 (両 a.c.) + case 2 / 対称 用 finite-entropy regularity precondition (NOT load-bearing)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hWyx_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => Y ω + X ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  by_cases hX_ac : P.map X ≪ volume
  · by_cases hY_ac : P.map Y ≪ volume
    · -- case 1 (両 a.c.): named wall `entropyPowerExt_add_ge_finite_ac` に delegation。
      exact entropyPowerExt_add_ge_finite_ac X Y P hX hY hXY hX_ac hY_ac hX_ent hY_ent
    · -- case 2 (X a.c. ∧ Y 特異): Phase 4 補題を 8 integrability + 2 finite-entropy precondition つきで直接呼出。
      exact entropyPowerExt_mixed_add_ge X Y P hX hY hXY hX_ac hY_ac h_ac h_int hκ_v
        hκ_logp_int hκ_cross_int h_fibreEnt_int h_cross_int h_logq_int hX_ent hW_ent
  · by_cases hY_ac : P.map Y ≪ volume
    · -- case 2 対称 (Y a.c. ∧ X 特異): Phase 4 対称版を Y+X path integrability + 2 finite-entropy つきで直接呼出。
      exact entropyPowerExt_mixed_add_ge_symm X Y P hX hY hXY hY_ac hX_ac h_ac_symm h_int_symm
        hκ_v_symm hκ_logp_int_symm hκ_cross_int_symm h_fibreEnt_int_symm h_cross_int_symm
        h_logq_int_symm hY_ent hWyx_ent
    · -- case 3 (両特異): 型自明、RHS=0。
      exact entropyPowerExt_singular_add_ge X Y P hX_ac hY_ac

end InformationTheory.Shannon
