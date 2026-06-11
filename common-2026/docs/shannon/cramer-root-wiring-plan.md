# Cramér: root sorry 配線 サブ計画

> **Parent**: [`cramer-chernoff-clt-closure-moonshot-plan.md`](cramer-chernoff-clt-closure-moonshot-plan.md) §判断ログ #4「残件 (未達でなく配線制約)」
>
> **在庫**: [`cramer-root-wiring-inventory.md`](cramer-root-wiring-inventory.md)(調査1 root B transport / 調査2 root A cycle-break、全 file:line 実測・verbatim signature 済)
> **settled facts**: [`cramer-facts.md`](cramer-facts.md)(headline sorryAx-free / median Mathlib 不在 / root closed-but-unwired)

## 進捗

- [ ] Phase M0 — 配線対象 signature + cycle edge + 逆依存の最終 verbatim 固定 📋 → [inventory](cramer-root-wiring-inventory.md)
- [ ] Phase A — root A cycle-break + `hVar` thread + headline discharge 📋
- [ ] Phase B — root B transport reduction + `hVar` 追加で discharge 📋

## ゴール / Approach

### Goal(完成判定)

親 moonshot で達成済の sorryAx-free headline
`InformationTheory.Shannon.CramerCltBoundary.cramer_lower_boundary_unconditional`
(`InformationTheory/Shannon/CramerCltBoundaryClosure.lean:588`、infinitePi 版 Cramér 下界、
内部最適 tilt `a = deriv cgf lam` で residual largeness hypothesis 除去済、`@audit:ok`)を使い、
上流に残る **2 つの root sorry** を proof done (0 sorry / 0 @residual) で discharge する:

- **root A** = `Cramer.Discharge.cramer_lower_phaseC_partial_discharge`
  (`Draft/Shannon/CramerLC2PhaseC.lean:147`、sorry @ :165)。infinitePi 版、結論形が headline と
  **verbatim 一致**(un-tilted product, `Y ∘ eval 0`)。
- **root B** = `Cramer.cramer_lower`(`Draft/Shannon/Cramer.lean:469`、sorry @ :483)。一般 iid
  `X : ℕ → Ω → ℝ` on bounded `μ`、headline より一般。

### Approach(overall strategy / shape of solution)

**全体像** — headline は両 root の **下流**(forward 依存グラフ実測:headline は root A・root B
どちらにも非依存、sorryAx-free)。そのまま in-place で `exact headline` を書くと **import cycle**
(`CramerLC2PhaseC` ← `InfinitePiTiltedChangeOfMeasure` ← headline file の edge)。よって配線は
**cycle-break(モジュール再配置)+ precondition gap 埋め(`hVar` 追加)+ transport(root B のみ)**
の 3 要素。

```
[現状の import DAG(在庫 §import DAG)]
  Cramer.lean(root B)
     └→ LC2Discharge → LC2DischargeExt
  CramerLC2PhaseC.lean(root A, IsMeasureInfinitePiTiltedEq def)
     ↑ imports both
  InfinitePiTiltedChangeOfMeasure.lean  ──(この edge が cycle 原因)── imports CramerLC2PhaseC
     └→ CramerCltBoundaryClosure.lean(headline)

[root A 配線(Phase A)= cycle-break]
  a1. IsMeasureInfinitePiTiltedEq def + InfinitePiTilted 内 7 theorem(計 8 decl)を
      新上流モジュール CramerBoundaryUpstream.lean(仮)へ hoist。
      新モジュールの import 土台 = MeasurePiTiltedFactorization(Cramér 連鎖から独立)
      + LC2DischargeExt(+ Cramer helper)。CramerLC2PhaseC は import しない。
  a2. CramerLC2PhaseC → 新上流 → headline file の一直線 DAG にし、headline を
      CramerLC2PhaseC から import 可能化(cycle 消滅)。
  a3. root A signature に hVar(非退化分散 precondition)を追加、逆依存 2 decl に thread。
  a4. root A body の sorry を `exact cramer_lower_boundary_unconditional …` で discharge。

[root B 配線(Phase B)= transport reduction]
  iid joint law = 共通周辺の infinitePi(iIndepFun_iff_map_fun_eq_infinitePi_map, Mathlib)
  → IdentDistrib.map_eq で各周辺統一 → event 移送(Measure.map_apply +
    infinitePi_partialSum_event_eq_pi)→ cgf transport ~10 行 self-build
    (cgf_eval_eq_cgf_base 同手法、mgf_id_map/mgf_map 経由)。
  + root B signature に hVar 追加 → headline へ落として discharge。
```

**root A 配線の核心は「配線だけでは閉じない 1 点」**(在庫 §調査2 最大想定難所):headline は
`hVar : 0 < Var[Y∘eval 0; infinitePi (μ₀.tilted (lam·Y))]` を precondition に要求するが、
**root A の現 signature に `hVar` が無い**。よって「import 並べ替え + `exact headline`」だけでは型が
合わない。root A / root B に `hVar` を **precondition として追加**するのが必須。これは headline 自身が
持つ regularity precondition と同形で、**非退化分散は Cramér 境界論法に本質的**(退化 `v=0` では
Gaussian median 1/2 / 窓質量 1/4 下界が崩れる、親 plan §退化処理)。よって load-bearing core ではなく
honesty 上 OK。`hVar` 追加 = root の generality を僅かに狭める(定数 RV を除外、数学的に正当)。

**Mathlib-shape-driven note**(CLAUDE.md §):headline の結論形は **root A と verbatim 一致**するよう
親 Phase 6 で設計済(`Y ∘ eval 0` 表記・un-tilted product・閾値 `a`)。よって root A 側で結論を
書き換える bridge は不要(`hVar` 追加と import 解決だけで `exact` が通る)。root B は一般 `μ` →
infinitePi への transport が要るが、cgf transport は in-project 前例 `cgf_eval_eq_cgf_base` の変奏で
新規 bridge lemma 自作を最小化する。

### `hVar` の honesty / 退化境界チェック(撤退判定の前提)

- `hVar` は **precondition(regularity)であり load-bearing core ではない**(headline の `@audit:ok`
  監査でも precondition 判定済、在庫 §honesty 注記)。root に追加するのは hypothesis bundling でなく
  正則性追加。
- **退化境界チェック**(着手時に再確認、predicate が degenerate でのみ壊れるか):`v = 0`(tilted
  ambient で `Y` が a.e. 定数)のとき median 1/2 / 窓質量 1/4 が崩れる(親 plan §退化処理で実証済)。
  非退化前提は Cramér 非自明領域(`Λ* > 0`)では `Λ'' = iteratedDeriv 2 cgf > 0` で文脈自動充足
  (`variance_tilted_mul`)。よって `hVar` 要求は仕様上正当で、**「root レベルで `hVar` 供給不能」=
  退化点除外でしかない**(撤退ライン L-WIRE2 参照)。

### 規模見積もり(Phase 別)

| Phase | 自作要素 | 種別 | 推定行数 |
|---|---|---|---|
| M0 | signature / cycle edge / 逆依存 最終確認 | 調査のみ | 0 |
| A | 新上流モジュール作成 + 8 decl hoist(import 再配線)+ `hVar` thread(逆依存 2)+ `exact` 1 行 | 配線(新規証明ゼロ) | **新規 ~30-60(うち証明 0、移動 + import + signature)** |
| B | transport reduction(joint law → event 移送 → cgf 橋 ~10 行)+ `hVar` 追加 + headline 落とし | 組立 + self-build ~10-15 | **~50-90** |
| | **合計** | — | **~80-150** |

> hoist 自体(Phase A a1-a2)は **既存 0-sorry decl の移動 + import 編集のみで新規証明ゼロ**。
> リスクは「移動先 module が別 cycle を露呈しないか」(在庫で MeasurePiTiltedFactorization は
> CramerLC2PhaseC 非 import を実測済 → 別 cycle なしの公算高、M0 で最終確認)。

### 1 unit 完遂か分割か

**判定:Phase A → Phase B の順で 1 unit で chain**。Phase A(root A)は結論 verbatim 一致で
`hVar` 追加 + cycle-break のみ = 最短経路、先に閉じる。Phase B(root B)は transport が要る分だけ
重いので後。**Phase A 単独 closure(root B は sorry 据置)も部分達成として明示**(撤退ライン
L-WIRE3)。cycle-break が別 cycle を露呈 or hoist で olean 連鎖が壊れる兆候が出たら L-WIRE1 へ。

## Phase M0 — 配線対象 signature + cycle edge + 逆依存 最終 verbatim 固定 📋

proof-log: no(調査のみ)

### スコープ

在庫 §調査1/2 に全 verbatim あり。Phase A 着手直前に以下を Read / script で **最終確認**(配線は
1 文字違いで型が落ちるので verbatim 必須):

- [ ] **headline** `cramer_lower_boundary_unconditional`(`CramerCltBoundaryClosure.lean:588`)の
  引数順 = `hY, h_bdd, a, lam, hlam, h_deriv, hVar, h_coboundedBelow` と結論形を Read で固定。
  特に `hVar` の形 `0 < Var[fun ω => Y(ω 0); infinitePi (μ₀.tilted (fun ω => lam*Y ω))]`。
- [ ] **root A** `cramer_lower_phaseC_partial_discharge`(`CramerLC2PhaseC.lean:147`、sorry @ :165)の
  現 signature(`hY_meas, h_bdd, a, lam, hlam, _h_deriv, h_coboundedBelow` = **`hVar` 無し**)と
  結論が headline と verbatim 一致することを Read で再確認。`_h_deriv` の underscore(現状 unused、
  配線後 headline へ渡すので active 化する)。
- [ ] **root B** `cramer_lower`(`Cramer.lean:469`、sorry @ :483)の signature
  (`_h_indep, _h_meas, _h_ident, _h_bdd, a, lam, hlam, _h_deriv, h_coboundedBelow` = **`hVar` 無し**)。
  結論が一般 `μ.real {ω | a·n ≤ ∑ X i ω}` で **infinitePi でない**(transport 要)ことを固定。
- [ ] **cycle edge** 確認:`InfinitePiTiltedChangeOfMeasure.lean` の import 行に `CramerLC2PhaseC`
  があり、その理由が `IsMeasureInfinitePiTiltedEq` 消費(在庫 §cycle の原因)であることを再確認。
- [ ] **hoist 対象 8 decl** の現 file:line を Read で固定(在庫 §hoist 表):
  `infinitePi_partialSum_event_eq_pi`(:141)/ `change_of_measure_lower_bound_pi`(:191)/
  `IsTiltedWindowEventuallyLarge`(:284)/ `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge`(:296)/
  `tiltedWindow_eventually_tendsto_one`(:427)/ `tiltedWindow_eventually_large_of_interior`(:494)/
  `tiltedMean_eq_deriv_cgf`(:520)[以上 InfinitePiTiltedChangeOfMeasure.lean]+
  `IsMeasureInfinitePiTiltedEq`(def, `CramerLC2PhaseC.lean:102`)。
  移動先 module の import 土台 = `MeasurePiTiltedFactorization` + `LC2DischargeExt`(+ `Cramer` helper)が
  `CramerLC2PhaseC` を import していない(別 cycle なし)ことを `^import InformationTheory` grep で再確認。
- [ ] **transport 鍵 lemma**(在庫 §調査1)の verbatim:`iIndepFun_iff_map_fun_eq_infinitePi_map`
  (`Mathlib/Probability/Independence/InfinitePi.lean:79`、`StandardBorelSpace` 不要)/
  `IdentDistrib.map_eq` / `infinitePi_partialSum_event_eq_pi` / `mgf_id_map`(:219)/ `mgf_map`(:214)/
  in-project 前例 `cgf_eval_eq_cgf_base`(`Cramer/LC2Discharge.lean:65`)。
- [ ] **逆依存の実値**(`dep_consumers.sh` 実測、本 plan 起草時に確定):
  - root A: **2 decl / 2 file** — `cramer_lower_legendre_phaseC_partial_discharge`
    (`CramerLC2PhaseC.lean:167`)、`cramer_lower_phaseC_residual_discharge`
    (`InfinitePiTiltedChangeOfMeasure.lean:357`)。`hVar` thread 先。
  - root B: **1 decl / 1 file** — `cramer_lower_legendre`(`Cramer.lean:485`)。`hVar` thread 先。
    (在庫散文は「root B: 2」だが `dep_consumers.sh` 実測は 1。実値を採用。)

### Done 条件

- 上記 verbatim が確定し、Phase A skeleton(新 module + hoist + signature 改変)が正確に書ける。
- hoist 移動先 module に別 cycle が無いことを機械確認。

## Phase A — root A cycle-break + `hVar` thread + headline discharge 📋

proof-log: yes(cycle-break の import 再配線で olean stale / 別 cycle 露呈の落とし穴を記録)

### a1. 新上流モジュール作成 + 8 decl hoist

- [ ] 新 file `InformationTheory/Shannon/CramerBoundaryUpstream.lean`(仮、最終名は M0 で確定)を作成。
  import 土台 = `MeasurePiTiltedFactorization`(`integral_exp_sum_pi_eq_pow` 等の下流ヘルパ供給)+
  `LC2DischargeExt`(`tilted_lln_*` / `isProbabilityMeasure_infinitePi_tilted_of_bounded`)
  (+ 必要なら `Cramer` helper)。**`CramerLC2PhaseC` は import しない**。
- [ ] 8 decl を **旧 file から新 file へ移動**(各 mover の旧→新 file):
  | decl | 旧 file:line | 新 file |
  |---|---|---|
  | `IsMeasureInfinitePiTiltedEq`(def) | `CramerLC2PhaseC.lean:102` | `CramerBoundaryUpstream.lean` |
  | `infinitePi_partialSum_event_eq_pi` | `InfinitePiTiltedChangeOfMeasure.lean:141` | 同上 |
  | `change_of_measure_lower_bound_pi` | `InfinitePiTiltedChangeOfMeasure.lean:191` | 同上 |
  | `IsTiltedWindowEventuallyLarge`(def) | `InfinitePiTiltedChangeOfMeasure.lean:284` | 同上 |
  | `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge` | `InfinitePiTiltedChangeOfMeasure.lean:296` | 同上 |
  | `tiltedWindow_eventually_tendsto_one` | `InfinitePiTiltedChangeOfMeasure.lean:427` | 同上 |
  | `tiltedWindow_eventually_large_of_interior` | `InfinitePiTiltedChangeOfMeasure.lean:494` | 同上 |
  | `tiltedMean_eq_deriv_cgf` | `InfinitePiTiltedChangeOfMeasure.lean:520` | 同上 |
  > 下流ヘルパ ~15 decl(`integral_exp_sum_pi_eq_pow` / `iIndepFun_tilted_ambient` / `tilted_lln_*` 等、
  > 在庫 §牽引ヘルパ表)は **移動不要**(現位置の MeasurePiTiltedFactorization / LC2Discharge /
  > LC2DischargeExt / Cramer から新上流が import 可能)。
- [ ] `InfinitePiTiltedChangeOfMeasure.lean` の import から `CramerLC2PhaseC` を除去し、代わりに
  `CramerBoundaryUpstream` を import(`IsMeasureInfinitePiTiltedEq` をそこから取る)。
- [ ] **検証点**:`lake build InformationTheory.Shannon.CramerBoundaryUpstream` で新 module が clean、
  `lake env lean InformationTheory/Draft/Shannon/InfinitePiTiltedChangeOfMeasure.lean` で旧 file が
  hoist 後も clean(stale olean は `lake build` で refresh)。

### a2. CramerLC2PhaseC → 新上流 → headline の一直線化

- [ ] `CramerLC2PhaseC.lean` を `CramerBoundaryUpstream` に依存(import)させ、`IsMeasureInfinitePiTiltedEq`
  をそこから取る(自前 def を削除、または新 module の def を re-export 経由)。
- [ ] headline file `CramerCltBoundaryClosure.lean` の import を整理し、新 DAG
  `CramerBoundaryUpstream → CramerLC2PhaseC → CramerCltBoundaryClosure`(または headline を
  CramerLC2PhaseC が import 可能な位置)で **cycle 消滅**を確認。
- [ ] **検証点**:`lake build InformationTheory` で全 module 連鎖が clean(cycle error なし)。
  cycle が消えたことを `lake env lean InformationTheory/Draft/Shannon/CramerLC2PhaseC.lean` の
  「headline を import できる」状態で確認。

### a3. root A signature に `hVar` 追加 + 逆依存 2 decl に thread

- [ ] root A `cramer_lower_phaseC_partial_discharge` に headline と同形の `hVar` を precondition 追加:
  `(hVar : 0 < Var[fun ω : ℕ → Ω₀ => Y (ω 0); infinitePi (fun _ => μ₀.tilted (fun ω => lam * Y ω))])`。
  既存 `_h_deriv` を `h_deriv`(active)化(headline に渡すため)。
- [ ] 逆依存 **2 decl** に `hVar` を thread(M0 実測):
  - `cramer_lower_legendre_phaseC_partial_discharge`(`CramerLC2PhaseC.lean:167`)— root A を呼ぶ箇所に
    `hVar` を渡し、自 signature にも `hVar` 追加(さらにその下流 `cramer_tendsto_phaseC_partial_discharge`
    が legendre 版を呼ぶなら entry_point まで連鎖、M0 の dep-chain で確認)。
  - `cramer_lower_phaseC_residual_discharge`(`InfinitePiTiltedChangeOfMeasure.lean:357`)— 同様に thread。
- [ ] **honesty 確認**:`hVar` は precondition(非退化)で load-bearing core でない(§`hVar` の honesty)。
  hypothesis bundling になっていない(窓質量の核は headline が CLT で内部供給、root は `exact` のみ)。
- [ ] **検証点**:`lake env lean InformationTheory/Draft/Shannon/CramerLC2PhaseC.lean` +
  `…/InfinitePiTiltedChangeOfMeasure.lean` が signature 改変後も clean(sorry 警告は a4 前なので許容)。

### a4. root A の sorry を headline で discharge

- [ ] root A body を
  `exact cramer_lower_boundary_unconditional hY_meas h_bdd a lam hlam h_deriv hVar h_coboundedBelow`
  で埋める(結論 verbatim 一致なので `exact` 一発、引数順は M0 で固定済)。
- [ ] **検証点**:`lake env lean InformationTheory/Draft/Shannon/CramerLC2PhaseC.lean` clean(0 sorry)。
  `#print axioms cramer_lower_phaseC_partial_discharge` = `[propext, Classical.choice, Quot.sound]`
  (sorryAx-free)。逆依存 2 decl + entry_point `cramer_tendsto_phaseC_partial_discharge` も transitive
  に sorry 消滅を `#print axioms` で確認。
- [ ] cramer-facts.md の「root closed-but-unwired」行を更新候補としてマーク(facts.md 編集は別、本 plan は
  リンクのみ。配線完了後に facts 更新を別タスクで)。

### Done 条件

- root A が 0 sorry / sorryAx-free、cycle 消滅、逆依存 2 + entry_point が transitive に sorry 消滅。
- `lake build InformationTheory` clean。

## Phase B — root B transport reduction + `hVar` 追加で discharge 📋

proof-log: yes(cgf transport self-build と joint-law 移送の型クラス整合を記録)

### スコープ

root B `cramer_lower`(一般 iid `X : ℕ → Ω → ℝ` on bounded `μ`)を headline(infinitePi 版)へ
transport で落とす。在庫 §調査1 の 3 段 transport:

- [ ] **B-1 joint law = infinitePi**:`iIndepFun_iff_map_fun_eq_infinitePi_map`
  (`Mathlib/Probability/Independence/InfinitePi.lean:79`、`[IsProbabilityMeasure μ]` のみ、
  `StandardBorelSpace` 不要)+ `_h_meas` で
  `μ.map (fun ω i => X i ω) = infinitePi (fun i => μ.map (X i))`。
- [ ] **B-2 各周辺統一**:`(h_ident i).map_eq : μ.map (X i) = μ.map (X 0)` で
  `infinitePi (fun i => μ.map (X i)) = infinitePi (fun _ => μ.map (X 0))`。以降 `ν := μ.map (X 0)` を
  共通周辺とする infinitePi product 上で議論。
- [ ] **B-3 event 移送**:root B の event `{ω | a·n ≤ ∑ X i ω}` を joint map `g := fun ω i => X i ω` で
  引き戻し(`Measure.map_apply g_meas event_meas`)→ 座標 event `{x : ℕ→ℝ | a·n ≤ ∑ x i}` へ。
  `infinitePi_partialSum_event_eq_pi`(in-project、座標恒等 `Y = id`、`ν = μ.map (X 0)`)で扱う。
- [ ] **B-4 cgf transport(~10 行 self-build)**:`cgf (X 0) μ t = cgf id (μ.map (X 0)) t`
  (= headline 側 `cgf (fun x => x 0) (infinitePi ν) t` 経由)を `cgf = Real.log ∘ mgf` 展開 +
  `mgf_id_map`(:219)/ `mgf_map`(:214)で自作。**in-project 前例 `cgf_eval_eq_cgf_base`
  (`Cramer/LC2Discharge.lean:65`)が同型の移送を実装済**なので、その変奏(eval を `μ.map (X 0)` 側へ
  向ける)で書く。新規 bridge lemma は最小。
- [ ] **B-5 `hVar` 追加**:root B signature に headline 同形の `hVar` を precondition 追加
  (`0 < Var[Y∘eval 0; infinitePi (ν.tilted …)]` 相当を transport 後の座標で表現)。
  逆依存 **1 decl**(`cramer_lower_legendre`、`Cramer.lean:485`、M0 実測)に thread。
  > **generality 注記**:root B は「一般 iid・degenerate(定数 X)も許す」ので `hVar` 追加は
  > generality を僅かに狭める(constant RV 除外)。数学的に正当(Cramér 下界は退化点で別扱い)。
- [ ] **B-6 discharge**:transport で結論を headline 形に書き換え `cramer_lower_boundary_unconditional` を
  落として root B の sorry を埋める。

### 落とし穴

- (i) joint map `g := fun ω i => X i ω : Ω → (ℕ → ℝ)` の可測性(`measurable_pi_lambda` + `_h_meas`)。
- (ii) `Measure.map_apply` の可測前提(`Measurable g`, `MeasurableSet {x | a·n ≤ ∑ x i}`)。
- (iii) cgf transport の `AEMeasurable` 前提(`mgf_id_map` は `AEMeasurable X μ`、`_h_meas` から)。
- (iv) `hVar` を transport 後の座標 `infinitePi ν` 上の分散として書く際の `ν = μ.map (X 0)` の往復
  (tilted も `ν.tilted` で表現、headline の `μ₀.tilted` と整合させる)。

### 検証点 / Done 条件

- [ ] `lake env lean InformationTheory/Draft/Shannon/Cramer.lean` clean(0 sorry)。
- [ ] `#print axioms cramer_lower` = `[propext, Classical.choice, Quot.sound]`(sorryAx-free)。
- [ ] 逆依存 `cramer_lower_legendre` も transitive に sorry 消滅。
- [ ] `lake build InformationTheory` clean。

## ファイル構成

```
InformationTheory/Shannon/
  CramerBoundaryUpstream.lean            ← Phase A a1 で新規(8 decl hoist 先、新規証明ゼロ)
  CramerCltBoundaryClosure.lean          ← 既存(headline、変更なし or import 整理のみ)
InformationTheory/Draft/Shannon/
  CramerLC2PhaseC.lean                   ← root A(:147)。hVar 追加 + body discharge + import 再配線
  InfinitePiTiltedChangeOfMeasure.lean   ← 7 decl 抜けて hoist、import 再配線、逆依存 thread
  Cramer.lean                            ← root B(:469)。transport + hVar 追加 + body discharge
  MeasurePiTiltedFactorization.lean      ← 既存(変更なし、新上流の import 土台)
InformationTheory/Shannon/Cramer/
  LC2Discharge.lean / LC2DischargeExt.lean ← 既存(変更なし、下流ヘルパ供給)
InformationTheory.lean                          ← 新 module の import 1 行追記
docs/shannon/
  cramer-root-wiring-inventory.md        ← 既存(在庫、verdict GO)
  cramer-root-wiring-plan.md             ← 本ファイル
```

## 撤退ライン

> sorry 禁止。詰まったら最小 residual を `sorry + @residual(<class>:<slug>)` で抜く(hypothesis
> bundling 禁止)。撤退 slug は **L-WIRE1〜**。proof-pivot-advisor トリガ:下記いずれか発動判断時。

**L-WIRE1**(cycle-break で別 cycle 露呈 / hoist で olean 連鎖が壊れる):8 decl の移動先
`CramerBoundaryUpstream` が想定外に上流 file を import 要求し別 cycle が出た場合 → hoist 集合を
**最小化**(headline が真に forward 依存する decl のみに絞る)、または `IsMeasureInfinitePiTiltedEq` def
**1 個だけ**を最小 module に切り出して cycle edge を断つ(残り 7 theorem は別解決)。それでも閉じなければ
root A body を `sorry + @residual(plan:cramer-root-wiring-plan)` 据置、cycle-break 構造だけ publish
(後退ゼロ:headline は既に sorryAx-free)。

**L-WIRE2**(`hVar` が root レベルで供給不能と判明):**まず退化境界チェック**(`v = 0` でのみ壊れるか、
§`hVar` の honesty 退化境界チェックで再確認)。`hVar` が degenerate(定数 RV)でしか壊れないなら
precondition 追加は正当 → 続行。もし `hVar` が非退化点でも導けない構造的問題(transport 後の座標で
分散表現が headline の `μ₀.tilted` 形と一致しない等)なら、root に `hVar` を **precondition として明示
追加**(headline と同形、honesty OK)。それでも型が合わなければ当該 root を
`sorry + @residual(plan:cramer-root-wiring-plan)` 据置。**`hVar` を load-bearing predicate に bundle
するのは禁止**(honesty defect)。

**L-WIRE3**(Phase A は閉じたが Phase B transport の型クラス不整合 / cgf 橋が詰まる):
**部分達成 = root A のみ closure、root B は sorry 据置**。root B body を
`sorry + @residual(plan:cramer-root-wiring-plan)` で残し、transport の B-1〜B-4 を進めた範囲まで
publish(joint-law 移送 lemma を別 helper として切り出せれば後続の足場)。root A closure 単独でも
entry_point `cramer_tendsto_phaseC_partial_discharge` が sorryAx-free 化する価値があり後退ゼロ。

**最悪着地**(両 root とも閉じない):cycle-break の module 再配置(Phase A a1-a2)だけ publish し、
両 root body は `sorry + @residual(plan:cramer-root-wiring-plan)` 据置。cycle 解消は後続配線の前提整備
として価値があり、headline の sorryAx-free 性は不変(後退ゼロ)。

**現時点判断**:Phase A(root A、verbatim 一致 + cycle-break + `hVar` 追加)を先に 1 unit で狙う。
cycle-break が割れたら即 Phase B(transport)へ。両方割れる前提で full closure(~80-150 行、新規証明ほぼ
ゼロ、`hVar` thread と transport self-build ~10-15 行が実質)。

## 判断ログ

> 書く頻度:Phase 終了時 / 設計変更 / 撤退判定。append-only。決着済 entry は削除(git が履歴)。

1. **2026-06-11 起草**:親 moonshot §判断ログ #4「残件(未達でなく配線制約)」を closure する子 plan として
   起草。在庫 `cramer-root-wiring-inventory.md`(調査1 root B transport は wall でない / 調査2 root A
   cycle-break footprint = 8 decl hoist)を受け、**cycle-break(モジュール再配置)+ `hVar` precondition
   追加 + root B transport** の 3 要素で両 root を配線する方針。
   - **最重要落とし穴(両 root 共通)**:headline は `hVar`(非退化分散 precondition)を要求するが
     root A / root B の signature に `hVar` が無い → import 並べ替えだけでは閉じない。`hVar` を
     precondition として追加 + 逆依存に thread が必須。これは regularity precondition で honesty OK
     (load-bearing core でない、headline 自身が同 hyp を持つ)。
   - **逆依存の実値**(`dep_consumers.sh` 実測):root A = **2 decl / 2 file**
     (`cramer_lower_legendre_phaseC_partial_discharge` / `cramer_lower_phaseC_residual_discharge`)、
     root B = **1 decl / 1 file**(`cramer_lower_legendre`)。在庫散文「root B: 2」は実測 1 に訂正、
     実値を採用(`rg` でなく `dep_consumers.sh` の term-level)。
   - **行番号の注記**:在庫 / 親バナーは root A を `:147`(decl)/ `:165`(sorry)と記載(本 plan 起草時
     Read で一致確認)。`dep_consumers.sh` の target 行表示 `:111`(root A)/ `:441`(root B)は
     docstring 先頭行で、decl 行(:147 / :469)とずれる(script は docstring 込みで decl head を取る)。
     配線時は decl 行(root A :147 / root B :469)を基準にする。
