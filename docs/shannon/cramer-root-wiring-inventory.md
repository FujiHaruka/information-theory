# Cramér root-sorry wiring — Mathlib/in-project API inventory

> 親プラン: `docs/shannon/cramer-chernoff-clt-closure-moonshot-plan.md`(両 root の `@residual` 行き先)/ `docs/shannon/cramer-lc2-discharge-moonshot-plan.md`。
> 本ファイルは **plan/impl をしない在庫調査専用**。コード一切編集なし。
> 全 file:line は本コミット時点で実測。再検証コマンドを各節に添付。

## 一行サマリ

**調査 1 (root B transport)**: 鍵補題 `iIndepFun_iff_map_fun_eq_infinitePi_map` が Mathlib に **既存**(joint law = 共通周辺分布の infinitePi)。event-transport は in-project `infinitePi_partialSum_event_eq_pi` が既存。cgf transport だけ Mathlib に専用補題なし(`cgf_map` Found 0)だが `mgf_id_map`+`Real.log` 経由で ~10 行の self-build。**root B は transport で discharge 可能(wall ではない)**。

**調査 2 (root A cycle-break)**: hoist すべき decl は **2 個の独立した def/theorem(`IsMeasureInfinitePiTiltedEq` + 新規上流モジュール)+ 既存ヘルパ群**。headline は forward 依存グラフ上 **root A にも root B にも依存しない**(機械確認済 / sorryAx-free `[propext, Classical.choice, Quot.sound]`)。最大の想定難所は **headline が `hVar`(非退化分散)を要求するのに root A シグネチャに `hVar` が無い** 点 — root A を headline で埋めるには `hVar` を新たに供給する必要がある(load-bearing precondition gap)。

---

## 対象 root sorry(再掲)

| root | 完全修飾名 | file:line | body | generality |
|---|---|---|---|---|
| **A** | `InformationTheory.Shannon.Cramer.Discharge.cramer_lower_phaseC_partial_discharge` | `InformationTheory/Shannon/Cramer/LC2PhaseC.lean:147` | `sorry`(:165) | infinitePi 版・headline と同 generality |
| **B** | `InformationTheory.Shannon.Cramer.cramer_lower` | `InformationTheory/Shannon/Cramer/Cramer.lean:469` | `sorry`(:483) | 一般 iid `X : ℕ → Ω → ℝ` on bounded `μ`・headline より一般 |

headline(sorryAx-free, `@audit:ok`):
`InformationTheory.Shannon.CramerCltBoundary.cramer_lower_boundary_unconditional`
@ `InformationTheory/Shannon/CramerCltBoundaryClosure.lean:588`

> 再検証: `lake env lean` で `#print axioms cramer_lower_boundary_unconditional` →
> `depends on axioms: [propext, Classical.choice, Quot.sound]`(sorryAx 不在、本セッションで実測)。

import DAG(実測, `^import InformationTheory` grep):
```
Cramer.lean ──────────────► LC2Discharge.lean ──► LC2DischargeExt.lean
   (root B)                       │ cgf_eval_eq_cgf_base       │ tilted_lln_*
   │                              ▼                            ▼
   │                       CramerLC2PhaseC.lean  ◄───────── (imports both)
   │                          (root A,  IsMeasureInfinitePiTiltedEq def)
   │                              │
MeasurePiTiltedFactorization.lean │  (← Meta.EntryPoint のみ, Cramer 連鎖から独立)
   │                              ▼
   └────────────► InfinitePiTiltedChangeOfMeasure.lean ──► CramerCltBoundaryClosure.lean
                     (6 hoist decls)  ▲                         (headline)
                     imports CramerLC2PhaseC ──┘  ← この edge が cycle 原因
```

---

## 調査 1 結論 — root B transport は成立(wall ではない)

root B(一般 iid `cramer_lower`)を headline(infinitePi 版)へ落とす reduction は、以下 3 段の transport で組める。鍵 3 補題はすべて既存(うち 1 つ Mathlib、2 つ in-project)、欠けているのは cgf transport の薄い橋(~10 行)のみ。

### A. iid joint law = 共通周辺分布の infinitePi(**Mathlib 既存・鍵**)

| 概念 | Mathlib API | file:line | 状態 | root B での扱い |
|---|---|---|---|---|
| **iid joint = infinitePi** | `iIndepFun_iff_map_fun_eq_infinitePi_map` | `Mathlib/Probability/Independence/InfinitePi.lean:79` | ✅ 既存 | **transport の中核**。`iIndepFun X μ → μ.map (fun ω i => X i ω) = infinitePi (fun i => μ.map (X i))` |
| AEMeasurable 版 | `iIndepFun_iff_map_fun_eq_infinitePi_map₀` | `Mathlib/Probability/Independence/InfinitePi.lean:43` | ✅ 既存 | 可測性が AEMeasurable しか無いとき |
| HasLaw 版 | `iIndepFun.hasLaw_infinitePi` | `Mathlib/Probability/Independence/InfinitePi.lean:84` | ✅ 既存 | 別形(`HasLaw (fun ω i => X i ω) (infinitePi μ) P`) |
| identical-distrib で各周辺を統一 | `IdentDistrib.map_eq`(構造体フィールド) | `Mathlib/Probability/IdentDistrib.lean:76` | ✅ 既存 | `(h_ident i).map_eq : μ.map (X i) = μ.map (X 0)` で `infinitePi (fun i => μ.map (X i)) = infinitePi (fun _ => μ.map (X 0))` |

**`iIndepFun_iff_map_fun_eq_infinitePi_map` verbatim**(`Mathlib/Probability/Independence/InfinitePi.lean:79-81`):
```
variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {X : Π i, Ω → 𝓧 i}

lemma iIndepFun_iff_map_fun_eq_infinitePi_map (mX : ∀ i, Measurable (X i)) :
    iIndepFun X P ↔ P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i))
```
- 型クラス前提(section variable から): `[MeasurableSpace Ω]`, `[IsProbabilityMeasure P]`, `∀ i, MeasurableSpace (𝓧 i)`。
- root B では `ι = ℕ`, `𝓧 i = ℝ`, `P = μ`。`[IsProbabilityMeasure μ]` は root B 既存、`∀ i, MeasurableSpace ℝ` は instance。
- **`StandardBorelSpace` は不要**(出力側コドメインに何も課されない。`ℝ` でも一般 `𝓧 i` でも可)。← この補題は型クラス事故の心配が薄い。
- `mX : ∀ i, Measurable (X i)` は root B の `_h_meas` から直接。

**`IdentDistrib.map_eq` verbatim**(`Mathlib/Probability/IdentDistrib.lean:76`, 構造体 `IdentDistrib` のフィールド):
```
map_eq : Measure.map f μ = Measure.map g ν
```
root B では `(h_ident i) : IdentDistrib (X i) (X 0) μ μ` から `(h_ident i).map_eq : μ.map (X i) = μ.map (X 0)`。

### B. partial-sum event を infinitePi-測度から移す(**in-project 既存**)

| 概念 | in-project API | file:line | 状態 | root B での扱い |
|---|---|---|---|---|
| **partial-sum event 移送** | `infinitePi_partialSum_event_eq_pi` | `InformationTheory/Shannon/Cramer/InfinitePiTiltedChangeOfMeasure.lean:141` | ✅ 既存(hoist 対象でもある) | `infinitePi {ω | P(∑ Y(ω i))} = Measure.pi (Fin n) {x | P(∑ Y(x i))}` |
| measure pushforward一般 | `MeasureTheory.Measure.map_apply` | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean`(可測写像で event を引き戻し) | ✅ 既存 | joint map で `μ.real {ω | a·n ≤ ∑ X i ω}` ↔ 座標 event `infinitePi.real {x | a·n ≤ ∑ x i}` を架橋 |

**`infinitePi_partialSum_event_eq_pi` verbatim**(`InfinitePiTiltedChangeOfMeasure.lean:141-147`):
```
theorem infinitePi_partialSum_event_eq_pi {ν : Measure Ω₀} [IsProbabilityMeasure ν]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (n : ℕ) (P : ℝ → Prop)
    (hP : MeasurableSet {r : ℝ | P r}) :
    (Measure.infinitePi (fun _ : ℕ => ν))
        {ω : ℕ → Ω₀ | P (∑ i ∈ Finset.range n, Y (ω i))}
      = (Measure.pi (fun _ : Fin n => ν))
          {x : Fin n → Ω₀ | P (∑ i, Y (x i))}
```
- 型クラス前提: `[IsProbabilityMeasure ν]`。
- root B では joint law 移送後にこの形へ落ち、座標 sum event の測度を扱える。

> **root B 用の event-transport の組み方**: root B の event `{ω | a·n ≤ ∑ i ∈ range n, X i ω}` は `μ` 上。joint map `g := fun ω i => X i ω : Ω → (ℕ → ℝ)` の preimage が座標 event `{x : ℕ→ℝ | a·n ≤ ∑ i ∈ range n, x i}` なので `Measure.map_apply g_meas event_meas` で `μ {ω | ...} = (μ.map g) {x | ...}`。これに A 節の `= infinitePi (fun _ => μ.map (X 0))` を rw。`infinitePi` 上の event は座標恒等 `Y = id` の `infinitePi_partialSum_event_eq_pi`(ν = μ.map (X 0))で扱える。

### C. cgf transport(**Mathlib 専用補題なし → ~10 行 self-build**)

root B の rate は `cgf (X 0) μ lam`、headline は `cgf (fun ω => Y(ω 0)) (infinitePi μ₀) lam`。transport には `cgf (X 0) μ = cgf id (μ.map (X 0))` 型の橋が要る。

| 概念 | API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `mgf id (μ.map X) = mgf X μ` | `mgf_id_map` | `Mathlib/Probability/Moments/Basic.lean:219` | ✅ 既存 | cgf 橋の素材 |
| `mgf X (μ.map Y) = mgf (X∘Y) μ` | `mgf_map` | `Mathlib/Probability/Moments/Basic.lean:214` | ✅ 既存 | 同上 |
| `mgf X μ = mgf Y μ'`(IdentDistrib) | `mgf_congr_identDistrib` | `Mathlib/Probability/Moments/Basic.lean:227` | ✅ 既存 | `mgf (X i) μ = mgf (X 0) μ` |
| **`cgf_id_map` / `cgf_map`** | — | — | ❌ **Mathlib 不在**(`cgf, Measure.map` loogle → `cgf_gaussianReal` のみ) | `cgf = Real.log ∘ mgf` 展開 + `mgf_id_map`/`mgf_map` で ~5–10 行 self-build。in-project 前例 `cgf_eval_eq_cgf_base`(`LC2Discharge.lean:65`)がまさに同手法 |

**`mgf_id_map` verbatim**(`Mathlib/Probability/Moments/Basic.lean:219`):
```
lemma mgf_id_map (hX : AEMeasurable X μ) : mgf id (μ.map X) = mgf X μ
```
**`mgf_map` verbatim**(`Mathlib/Probability/Moments/Basic.lean:214-216`):
```
lemma mgf_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {Y : Ω' → Ω} {X : Ω → ℝ}
    (hY : AEMeasurable Y μ) {t : ℝ} (hX : AEStronglyMeasurable (fun ω ↦ exp (t * X ω)) (μ.map Y)) :
    mgf X (μ.map Y) t = mgf (X ∘ Y) μ t
```

**in-project 前例 `cgf_eval_eq_cgf_base`**(`InformationTheory/Shannon/Cramer/LC2Discharge.lean:65-69`)— 全く同型の cgf 移送を 20 行弱で実装済:
```
lemma cgf_eval_eq_cgf_base
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (i : ℕ) (t : ℝ) :
    cgf (fun ω : ℕ → Ω₀ => Y (ω i)) (Measure.infinitePi (fun _ : ℕ => μ₀)) t
      = cgf Y μ₀ t
```
→ root B 用 cgf 橋は `cgf (X 0) μ t = cgf id (μ.map (X 0)) t`(= `cgf (fun x => x 0) (infinitePi (μ.map (X 0))) t` 経由)を同手法で書く。

### 二段階・結論形再検索(wall でないことの裏取り)

`cgf_map` Found 0 を受けて以下を確認(過大評価防止):
- **`ProbabilityTheory.cgf, MeasureTheory.Measure.map`** → `Found one`(`cgf_gaussianReal` のみ、汎用 transport 無し)。
- **`ProbabilityTheory.cgf, Filter.liminf, MeasureTheory.Measure.infinitePi`** → **`Found 0`**(Mathlib に「cgf+liminf+infinitePi の Cramér 下界一括」は存在しない — 当然、これは本プロジェクトの定理)。
- テンプレ補題: in-project `cgf_eval_eq_cgf_base`(`LC2Discharge.lean:65`)が結論形 `cgf (… ∘ eval) (infinitePi …) t = cgf … t` を既に持つ。root B 橋はその `eval` を `μ.map (X 0)` 側へ向けた変奏で、**自作見積 ~10 行**。

> 再検証コマンド:
> ```
> ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "ProbabilityTheory.iIndepFun, MeasureTheory.Measure.infinitePi"
> ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "ProbabilityTheory.cgf, MeasureTheory.Measure.map"
> ./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "ProbabilityTheory.cgf, Filter.liminf, MeasureTheory.Measure.infinitePi"
> ```

### root B transport — 判定とリスク

**判定: transport で discharge 可能(wall ではない)。** 鍵 transport `iIndepFun_iff_map_fun_eq_infinitePi_map` は Mathlib 既存・型クラス事故なし。

ただし以下 2 点が load-bearing precondition gap(headline 適用時に新規供給が要る):
1. **`hVar`(非退化分散)**: headline `cramer_lower_boundary_unconditional` は `(hVar : 0 < Var[fun ω => Y(ω 0); infinitePi (μ₀.tilted (lam·Y))])` を要求。root B `cramer_lower` のシグネチャに `hVar` は **無い**。→ root B を headline で埋めるには (a) root B シグネチャに `hVar` 相当を追加するか、(b) root B の bounded 仮定 + 非退化を別途導く必要。**ここが root B 配線の最大難所**(transport そのものより precondition 整合)。
2. **`h_coboundedBelow`**: root B も headline も同形で持つ(整合)。`h_deriv`(最適 tilt)も両者にある(def-fix #24 で root B にも追加済)。

> **honesty 注記**: `hVar` は「非退化 precondition」であり load-bearing core ではない(headline の `@audit:ok` 監査でも precondition 判定)。root B に `hVar` を追加するのは hypothesis bundling ではなく regularity precondition 追加で OK。ただし root B は「一般 iid・degenerate(定数 X)も許す」ので、`hVar` 追加は **generality を僅かに狭める**(constant RV を除外)— これは数学的に正当(Cramér 下界は退化点で別扱い)。

---

## 調査 2 結論 — root A cycle-break footprint

### cycle の原因(1 edge)

`InfinitePiTiltedChangeOfMeasure.lean` が `CramerLC2PhaseC.lean`(root A の置き場)を import している唯一の理由は **`IsMeasureInfinitePiTiltedEq` def を使うため**(下記消費者リスト)。headline は `InfinitePiTilted` の下流なので、root A を in-place で `exact headline` 埋めすると import cycle。

### hoist すべき decl(headline が forward 依存する `Discharge.*` 群、実測)

headline `cramer_lower_boundary_unconditional` の forward 依存グラフ(`dep_graph.sh`)に現れる `InformationTheory.Shannon.Cramer.Discharge.*`(= 上流に持ち上げ対象):

| decl | 現 file:line | kind | 備考 |
|---|---|---|---|
| `infinitePi_partialSum_event_eq_pi` | `InfinitePiTiltedChangeOfMeasure.lean:141` | theorem | event 移送(調査1でも使用) |
| `change_of_measure_lower_bound_pi` | `InfinitePiTiltedChangeOfMeasure.lean:191` | theorem | 有限 change-of-measure 下界 |
| `IsTiltedWindowEventuallyLarge` | `InfinitePiTiltedChangeOfMeasure.lean:284` | def | window predicate |
| `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge` | `InfinitePiTiltedChangeOfMeasure.lean:296` | theorem | `IsMeasureInfinitePiTiltedEq` の producer |
| `tiltedWindow_eventually_large_of_interior` | `InfinitePiTiltedChangeOfMeasure.lean:494` | theorem | tilted-LLN window(最重量、下記ヘルパ群を牽引) |
| `tiltedMean_eq_deriv_cgf` | `InfinitePiTiltedChangeOfMeasure.lean:520` | theorem | cgf 微分 = tilted mean 橋 |
| `tiltedWindow_eventually_tendsto_one` | `InfinitePiTiltedChangeOfMeasure.lean:427` | theorem | LLN window → 1 |
| **`IsMeasureInfinitePiTiltedEq`(def)** | `CramerLC2PhaseC.lean:102` | def | **cycle 解消の核** — `InfinitePiTilted` と headline 双方が消費 |
| `cgf_eval_eq_cgf_base` | `LC2Discharge.lean:65` | lemma | cgf-eval 橋(調査1とも共通) |

**牽引される下流ヘルパ(`tiltedWindow_eventually_large_of_interior` / `change_of_measure_lower_bound_pi` の forward 依存、全て `Discharge.*` or `Cramer.*`、root A 非依存)**:

| decl | 現 file:line |
|---|---|
| `integral_exp_sum_pi_eq_pow` | `MeasurePiTiltedFactorization.lean:112` |
| `lintegral_pi_prod` | `MeasurePiTiltedFactorization.lean:50` |
| `pi_tilted_sum_eq_pi_tilted` | `MeasurePiTiltedFactorization.lean:126` |
| `setLIntegral_pi_prod_factor` | `MeasurePiTiltedFactorization.lean:79` |
| `iIndepFun_tilted_ambient` | `Cramer/LC2Discharge.lean:87` |
| `identDistrib_tilted_ambient` | `Cramer/LC2Discharge.lean:100` |
| `isProbabilityMeasure_infinitePi_tilted_of_bounded` | `Cramer/LC2DischargeExt.lean:87` |
| `pairwise_indepFun_tilted_ambient` | `Cramer/LC2DischargeExt.lean:101` |
| `integrable_eval_under_infinitePi_tilted` | `Cramer/LC2DischargeExt.lean:113` |
| `integral_eval_under_infinitePi_tilted` | `Cramer/LC2DischargeExt.lean:134` |
| `tilted_lln_ae` | `Cramer/LC2DischargeExt.lean:168` |
| `tilted_lln_in_probability` | `Cramer/LC2DischargeExt.lean:209` |
| `tilted_lln_in_probability_real` | `Cramer/LC2DischargeExt.lean:241` |
| `integrable_exp_mul_of_bounded`(Cramer.lean helper) | `Cramer.lean:100` |
| `isProbabilityMeasure_tilted_of_bounded`(Cramer.lean helper) | `Cramer.lean:366` |

> これら下流ヘルパは既に `MeasurePiTiltedFactorization` / `LC2Discharge` / `LC2DischargeExt` / `Cramer` に居り、これらは **`CramerLC2PhaseC` を import していない**(`MeasurePiTiltedFactorization` は `Meta.EntryPoint` のみ、`LC2Discharge`/`LC2DischargeExt`/`Cramer` も `CramerLC2PhaseC` 非 import)。よって**移動が必要なのは `InfinitePiTiltedChangeOfMeasure.lean` 内に居る 7 decl + `IsMeasureInfinitePiTiltedEq` def の計 8 decl のみ**。下流ヘルパ群は現位置のまま新上流モジュールから import できる。

### root A 非依存の機械確認(必須チェック)

headline が sorryAx-free である以上、hoist 対象は root A に依存しないはず。実測で確認:

| 確認 | コマンド | 結果 |
|---|---|---|
| 各 hoist decl の forward graph に root A が出るか | `dep_graph.sh <decl>` → grep `cramer_lower_phaseC_partial_discharge` | **7 decl すべて 0 hit**(非依存) |
| headline の forward graph に root A が出るか | `dep_graph.sh cramer_lower_boundary_unconditional` → grep | **0 hit** |
| headline の forward graph に root B (`Cramer.cramer_lower`) が出るか | 同上 | **無し**(`Cramer.cramer_lower*` 不在) |
| headline 自体の sorryAx | `#print axioms cramer_lower_boundary_unconditional` | `[propext, Classical.choice, Quot.sound]`(sorryAx 不在) |

> 再検証コマンド:
> ```
> lake build InformationTheory   # root olean refresh(必須: stale だと未知 decl 扱い)
> bash scripts/dep_graph.sh InformationTheory.Shannon.CramerCltBoundary.cramer_lower_boundary_unconditional
> rg -c "cramer_lower_phaseC_partial_discharge" dep_graph.dot   # → 0
> ```

### `IsMeasureInfinitePiTiltedEq` / root A の消費者(逆依存、実測)

`dep_consumers.sh` 実測(signature 変更 / 移動時に touch が要る decl):

**`IsMeasureInfinitePiTiltedEq`(def)— direct consumers 3 / 3 file**:
- `InformationTheory/Shannon/Cramer/LC2PhaseC.lean:303` `isMeasureInfinitePiTiltedEq_iff`
- `InformationTheory/Shannon/Cramer/InfinitePiTiltedChangeOfMeasure.lean:291` `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge`
- `InformationTheory/Shannon/CramerCltBoundaryClosure.lean:408` `isMeasureInfinitePiTiltedEq_of_tiltedWindowLargeC`(**headline ファイル内**)

→ def を上流に hoist すると、この 3 消費者の参照は新モジュール import で解決(うち 2 は移動先と同居 or 下流)。

**root A `cramer_lower_phaseC_partial_discharge` — direct consumers 2 / 2 file**:
- `InformationTheory/Shannon/Cramer/LC2PhaseC.lean:167` `cramer_lower_legendre_phaseC_partial_discharge`
- `InformationTheory/Shannon/Cramer/InfinitePiTiltedChangeOfMeasure.lean:357` `cramer_lower_phaseC_residual_discharge`

→ root A 本体は移動しない(現位置で埋める)。これら 2 消費者は root A を埋めれば自動的に sorryAx 消える(transitive)。

> 再検証コマンド:
> ```
> bash scripts/dep_consumers.sh InformationTheory.Shannon.Cramer.Discharge.IsMeasureInfinitePiTiltedEq
> bash scripts/dep_consumers.sh InformationTheory.Shannon.Cramer.Discharge.cramer_lower_phaseC_partial_discharge
> ```

### cycle-break の見立て

**推奨手順(配線のみ、新規証明なし)**:
1. `IsMeasureInfinitePiTiltedEq` def + `InfinitePiTilted` 内 7 decl(計 8)を新規上流モジュール
   `InformationTheory/Shannon/CramerBoundaryUpstream.lean`(仮)へ移す。
   import: `MeasurePiTiltedFactorization` + `LC2DischargeExt`(+ `Cramer` helper)— **`CramerLC2PhaseC` は import しない**。
2. `CramerLC2PhaseC.lean` をこの新上流モジュールに依存させ(import)、その下流に `CramerCltBoundaryClosure.lean`(headline)を置く。
3. headline を `CramerLC2PhaseC` から import 可能になるので、root A の body を
   `exact cramer_lower_boundary_unconditional hY h_bdd a lam hlam h_deriv hVar h_coboundedBelow`
   で埋める。

**ただし配線だけでは閉じない 1 点(最大想定難所)**:
- headline は `hVar`(`0 < Var[…tilted…]`)を要求するが root A シグネチャに `hVar` が **無い**。
  → root A を `exact headline` で埋めるには `hVar` を root A シグネチャに追加するか、root A の `h_bdd`(boundedness)から非退化を導く補助が要る。後者は「bounded ⇒ 非退化」ではない(定数 Y は bounded かつ Var=0)ので、**`hVar` 相当の precondition 追加が現実的**。これは headline と同じ regularity precondition で、honesty 上 OK(load-bearing core ではない)。root A の def-fix #24(`h_deriv` 追加)と同型の signature 拡張。
  → この `hVar` 追加は root A の 2 消費者
    (`cramer_lower_legendre_phaseC_partial_discharge`, `cramer_lower_phaseC_residual_discharge`)へ
    thread が必要(逆依存 2 decl、上記実測)。

---

## まとめ

- **調査 1**: root B transport は **成立(wall ではない)**。鍵 `iIndepFun_iff_map_fun_eq_infinitePi_map`(Mathlib 既存・`StandardBorelSpace` 不要)+ in-project `infinitePi_partialSum_event_eq_pi` + cgf 橋 ~10 行 self-build。最大難所は transport ではなく `hVar` precondition 整合。
- **調査 2**: hoist 集合は **8 decl**(`IsMeasureInfinitePiTiltedEq` def + `InfinitePiTilted` 内 7 decl)。下流ヘルパ ~15 decl は移動不要(現位置で import 可)。headline は root A・root B どちらにも非依存(機械確認 + sorryAx-free 実測)。cycle-break は配線で原理的に可能、ただし `hVar` を root A へ thread する signature 拡張が必須。
- **共通の想定難所**: 両 root とも headline の `hVar`(非退化分散 precondition)を新規供給する必要がある。これは hypothesis bundling ではなく regularity precondition で honesty 上 OK だが、root A の逆依存 2 decl への thread を伴う。
