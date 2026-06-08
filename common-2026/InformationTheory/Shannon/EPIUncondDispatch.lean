import InformationTheory.Shannon.EPIUncondMixedCase
import InformationTheory.Shannon.EPICase1SmoothingLimit
import InformationTheory.Shannon.EPIInfiniteVarianceCapstone

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
  delegate。和の有限微分エントロピー `hW_ent` precondition を threading するのみで own sorry
  なし (`hW_ent` は `hX_ent`/`hY_ent` と同階層の regularity precondition、EPI を encode しない)。
* **無限分散**: `EPIInfiniteVarianceTruncation.entropyPowerExt_add_ge_infinite_variance`
  (route T = conditioning truncation で **genuine closure 済、sorryAx-free**、capstone
  `EPIInfiniteVarianceCapstone.lean`)。旧 Lieb-Young / Brascamp-Lieb 壁は FALSE WALL だった。

旧 bundled `wall:epi-finite-entropy-ac-classical` (両 a.c. 有限エントロピー古典 EPI の 1 本
sorry) は本 file で有限分散枝 (smoothing closure) + 無限分散枝 (route T closure) の 2 本に
**分解 + 両枝 genuine closure** された。`entropyPowerExt_add_ge_finite_ac` 自身は delegation のみで
own sorry 0、両枝とも sorryAx-free ゆえ transitive sorry も 0 (proof-done)。
-/

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory
open InformationTheory.Shannon.EntropyPowerInequality
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **case 1 残核 — 両 a.c. + 両有限エントロピーの classical EPI**。

両 a.c. かつ両入力が有限微分エントロピー (negMulLog density 可積分) のとき EPI
`N(X+Y) ≥ N(X) + N(Y)`。これは古典 EPI そのもの。有限分散 / 無限分散で `by_cases` 分割:

* **有限分散** (`hfv : Integrable (·²) X ∧ Integrable (·²) Y`):
  `EPICase1SmoothingLimit.entropyPowerExt_add_ge_of_finite_variance` (smoothing→正則化 limit
  closure、sorryAx-free) に delegate。X+Y の有限微分エントロピー `hW_ent`
  (`negMulLog ((P.map (X+Y)).rnDeriv volume ·).toReal` 可積分) を threading するのみ。これは
  `hX_ent`/`hY_ent` と同階層の regularity precondition であって EPI を encode しない
  (**NOT load-bearing**)。本枝に own sorry は無い。
* **無限分散** (`¬ hfv`):
  `EPIInfiniteVarianceTruncation.entropyPowerExt_add_ge_infinite_variance` (route T =
  conditioning truncation で **genuine closure 済、sorryAx-free**、capstone
  `EPIInfiniteVarianceCapstone.lean`) に delegate。

本補題自身は delegation のみで own sorry 0、signature honest (`hX_ent`/`hY_ent`/`hW_ent` は
有限微分エントロピー regularity precondition、結論を encode しない)。両枝 (有限分散 smoothing /
無限分散 route T) とも sorryAx-free ゆえ **transitive sorry も 0 (proof-done)**。旧 bundled
`wall:epi-finite-entropy-ac-classical` の分解先。

無限分散枝の closure 経緯: 旧 wall slug `epi-infinite-variance-classical` は「Lieb-Young
sharp Young / Brascamp-Lieb 必須」を前提とした壁判定だったが、**FALSE WALL** と判明
(2026-06-07)。route T (両成分同時 conditioning による compact-support 切詰 → 有限分散 EPI 黒箱
再利用 → R→∞ で Gibbs + cross-entropy DCT による usc) で sharp Young を経ずに genuine closure。

独立 honesty audit 2026-06-07 (commit 452ea1b、`hW_ent` threading 化): `hW_ent` は
regularity precondition で **NOT load-bearing** と確認 (core-reconstruction test PASS — 「X+Y の
negMulLog density 可積分」単独では結論不等式 `N(X+Y)≥N(X)+N(Y)` を含意しない)。実消費は
delegation 先 `entropyPowerExt_add_ge_of_finite_variance` で `IsHeatFlowEndpointRegular.hpX_ent`
field (endpoint 連続性入力 = regularity) + `entropyPowerExt=ofReal(entropyPower)` 橋渡しのみ
(不等式 core は smoothing-limit machinery が供給)。`hX_ent`/`hY_ent` と同型・同階層 (出力側で
あることは honesty を変えない)。delegation 先 `hent_sum` 引数型と verbatim 一致。

独立 honesty audit 2026-06-07 (commit c9103c6、無限分散枝を capstone に rewire): tier-1 認定。
4-check 全 PASS — (1) 非循環 (genuine by_cases delegation)、(2) 非バンドル (`hX_ent`/`hY_ent`/`hW_ent`
は有限微分エントロピー regularity precondition、core-reconstruction test で「negMulLog density 可積分
単独 ⊬ 結論不等式」確認、不等式 core は両 delegation 先 machinery が供給)、(3) 非退化 (具体的 EPI
不等式)、(4) sufficiency (両枝とも delegation 先 signature と引数 verbatim 一致)。無限分散枝の
delegation 先 `EPIInfiniteVarianceTruncation.entropyPowerExt_add_ge_infinite_variance` は本監査で
独立 tier-1 認定済 (capstone)、旧 wall slug `epi-infinite-variance-classical` は FALSE WALL 解消
(route T genuine closure、active residual 0 件 grep 確認)。両枝 sorryAx-free ゆえ transitive sorry 0、
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (本監査機械再確認) で proof done。@audit:ok -/
theorem entropyPowerExt_add_ge_finite_ac
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPowerExt (P.map (fun ω => X ω + Y ω))
      ≥ entropyPowerExt (P.map X) + entropyPowerExt (P.map Y) := by
  by_cases hfv : Integrable (fun ω => (X ω) ^ 2) P ∧ Integrable (fun ω => (Y ω) ^ 2) P
  · -- 有限分散: smoothing-limit closure に delegate。和の有限微分エントロピー `hW_ent` は
    -- hX_ent/hY_ent と同階層の regularity precondition を threading するだけ。
    obtain ⟨h_mom_X, h_mom_Y⟩ := hfv
    exact EPICase1SmoothingLimit.entropyPowerExt_add_ge_of_finite_variance
      P X Y hX hY hXY hX_ac hY_ac h_mom_X h_mom_Y hX_ent hY_ent hW_ent
  · -- 無限分散: route T (conditioning truncation) で genuine closure 済 (sorryAx-free)。
    exact EPIInfiniteVarianceTruncation.entropyPowerExt_add_ge_infinite_variance
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

**全 4 枝 genuine か delegation** (case 3 は vacuous でなく特異測度のエントロピーパワーが
真に 0、case 2 の前提は load-bearing でなく regularity precondition を Phase 4 補題に threading
するのみ、case 1 は named wall に delegation)。新 finite-entropy 前提 4 本は honest regularity
precondition (load-bearing でない)。dispatch 自身は own sorry 0、case-1 無限分散枝が route T で
genuine closure 済 (2026-06-07) ゆえ **transitive sorry も 0 (proof-done)**。

独立 honesty audit 2026-06-07 (commit 452ea1b): case-1 への `hW_ent` threading (line 165) は
headline 既存引数の再利用で、新 defect を上流に積んでいないと確認 (`hW_ent` は regularity
precondition、honest)。

独立 honesty audit 2026-06-07 (commit c9103c6、case-1 無限分散 delegation 先を capstone に rewire):
tier-1 認定。4-check 全 PASS — (1) 非循環 (4-case by_cases delegation)、(2) 非バンドル (16
integrability + 4 finite-entropy は path 依存 regularity precondition、いずれも結論不等式 core を
渡さず: case 1 は `entropyPowerExt_add_ge_finite_ac` に delegate、case 2/2-symm は Phase 4 補題に
thread、case 3 は型自明)、(3) 非退化 (case 3 両特異は `entropyPowerExt_singular_add_ge` = 特異測度の
エントロピーパワー真に 0 → RHS=0、退化悪用でなく正しい値、sanity gate `entropyPowerExt_dirac=0`
確認済の既 `@audit:ok` decl に delegate)、(4) sufficiency (全 4 枝で delegation 先引数と一致)。case-1
無限分散枝が capstone 経由で genuine closure 済 (FALSE WALL 解消) ゆえ transitive sorry 0、
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (本監査機械再確認) で proof done。@audit:ok

**@audit:superseded-by(entropyPowerExt_add_ge_unconditional)**: 本 skeleton は 21 precondition
(case2/2symm 用 16 integrability + case-1/case2 用 5 finite-entropy) を取るが、2026-06-08 Phase 5
endgame で method-Y gateway 経由の完全無条件版 `entropyPowerExt_add_ge_unconditional`
(`EPIUncondDispatchFull.lean`、`hX hY hXY` のみ、precondition 0、sorryAx-free、独立監査 all-OK) が
別建てされ canonical headline となった。本 skeleton は proof-done の consumer 0 leaf として残置
(削除しないが新規利用は無条件版を推奨)。 -/
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
      exact entropyPowerExt_add_ge_finite_ac X Y P hX hY hXY hX_ac hY_ac hX_ent hY_ent hW_ent
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

/-- **実数版 EPI — a.c. + 有限微分エントロピー前提版 (proof-done)**。

両入力 `X`, `Y` が独立、各 push-forward 測度が Lebesgue 測度に絶対連続 (a.c.) かつ
有限微分エントロピー (negMulLog density 可積分) のとき、実数版エントロピーパワー不等式
`N(X+Y) ≥ N(X) + N(Y)` が成立 (`entropyPower : Measure ℝ → ℝ`、`exp(2·h(μ))`)。

前提 `hX_ac`/`hY_ac` (a.c.)・`hX_ent`/`hY_ent`/`hW_ent` (有限微分エントロピー = negMulLog
density 可積分) は **regularity precondition であって NOT load-bearing**。EPI 不等式の core は
拡張版 `entropyPowerExt_add_ge_finite_ac` (ℝ≥0∞ 値、有限分散 = smoothing closure / 無限分散 =
route T closure、両枝 sorryAx-free) が供給する。本補題が行うのは ℝ≥0∞→ℝ の型変換のみ:
各 a.c.+可積分枝で `entropyPowerExt μ = ENNReal.ofReal (Real.exp (2·h μ)) = ENNReal.ofReal
(entropyPower μ)` (`entropyPowerExt_of_ac_integrable`) を使い、ℝ≥0∞ 不等式を ℝ 不等式に剥がす。

対比: 現 headline `entropy_power_inequality` (`EntropyPowerInequality.lean:289`) は `h_stam`
+ 未証明橋 `stamToEPIBridge_holds` を transitive 消費し proof-done でない。本補題は a.c.+有限
エントロピー前提つきだが own sorry 0 かつ transitive sorry 0 で **sorryAx-free** (proof-done)。

命名 `_of_ac` は前提 (a.c.) を反映する記述的命名 (name laundering でない)。

独立 honesty audit 2026-06-07 (commit 64d21ae): tier-1 認定。4-check 全 PASS —
(1) 非循環 (結論 ℝ 版 EPI ≢ いずれの仮説、body は ℝ≥0∞ 版取得 + 型変換、`:= h` でない)、
(2) 非バンドル (core-reconstruction test: `hX_ac`/`hY_ac` (a.c.)・`hX_ent`/`hY_ent`/`hW_ent`
(有限微分エントロピー = negMulLog density 可積分) を全 grant しても EPI 不等式は手に入らない —
superadditivity の核は delegation 先 `entropyPowerExt_add_ge_finite_ac` (tier-1、両枝 sorryAx-free)
が供給。前提はいずれも `*Hypothesis` predicate でなく結論と同型でもない regularity precondition)、
(3) 非退化 (具体的 EPI 不等式、`:True` slot なし。旧 `entropyPower (Dirac)=1` 退化トラップは a.c.
前提が Dirac を構造的に排除するため不発、退化悪用でなく正当なスコープ制限)、(4) sufficiency
(delegation 先 `entropyPowerExt_add_ge_finite_ac` と引数 verbatim 一致、型変換は非負実数上の
`ENNReal.ofReal` order-preserving bijection で出口形ミスマッチなし、反例は delegation 先の反例に
帰着し同定理 sorryAx-free ゆえ不在)。`#print axioms entropy_power_inequality_of_ac` =
`[propext, Classical.choice, Quot.sound]` (本監査機械再確認、transitive sorry 0) で proof done。@audit:ok -/
theorem entropy_power_inequality_of_ac
    (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hX_ac : (P.map X) ≪ volume) (hY_ac : (P.map Y) ≪ volume)
    (hX_ent : Integrable (fun x => Real.negMulLog ((P.map X).rnDeriv volume x).toReal) volume)
    (hY_ent : Integrable (fun x => Real.negMulLog ((P.map Y).rnDeriv volume x).toReal) volume)
    (hW_ent : Integrable
      (fun x => Real.negMulLog ((P.map (fun ω => X ω + Y ω)).rnDeriv volume x).toReal) volume) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  -- W = X+Y も a.c. (X a.c. ∧ 独立 ⟹ X+Y a.c.)
  have hW_ac : (P.map (fun ω => X ω + Y ω)) ≪ volume :=
    map_add_absolutelyContinuous X Y P hX hY hXY hX_ac
  -- ℝ≥0∞ 版 EPI を取得
  have hineq := entropyPowerExt_add_ge_finite_ac X Y P hX hY hXY hX_ac hY_ac hX_ent hY_ent hW_ent
  -- 3 項を ofReal (exp (2h)) = ofReal (entropyPower) に書換
  rw [entropyPowerExt_of_ac_integrable hW_ac hW_ent,
    entropyPowerExt_of_ac_integrable hX_ac hX_ent,
    entropyPowerExt_of_ac_integrable hY_ac hY_ent] at hineq
  -- RHS の ofReal a + ofReal b を ofReal (a+b) にまとめる
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)] at hineq
  -- entropyPower 定義を展開し、目標を ofReal 版不等式に直して hineq に一致させる
  rw [ge_iff_le, entropyPower, entropyPower, entropyPower,
    ← ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)]
  exact hineq

end InformationTheory.Shannon
