# 無条件 EPI Phase 3 case-1 (両 a.c.) 隠れ壁調査 — density-witness 在庫

> 親計画: `docs/shannon/` 系 EPI 無条件化 line。assembly 対象は
> `isStamToEPIScalingHyp_of_stam_debruijn` (`InformationTheory/Shannon/EPIStamToBridge.lean:1324`)。
> 本ファイルは inventory のみ (read-only 調査、コード編集なし)。

## 一行サマリ

**case-1 (両 a.c.) EPI core は「真に一般 a.c.」では閉じない。verdict = (b) 有限分散等の追加 regularity を隠し持つ。** density witness の 8 field のうち 4 field (`hpX_law`/`hpX_int`/`hpX_mass`) は a.c.+確率測度から自動だが、`hpX_mom` (有限 2 次 moment = 有限分散) と `hpX_ent` (有限微分エントロピー) は **a.c. だけからは出ない** (heavy-tail / concentrated 反例)。さらに instance は **生の入力 `P.map X`** に課されており、heat-flow 平滑後の測度ではない (verdict (c) 不成立)。Mathlib に「a.c. ⟹ 有限分散」「density ⟹ negMulLog 可積分」の橋は **存在しない** (loogle `Found 0 declarations`、project 内でも当該 lemma `negMulLog_integrable_of_density` は false-as-stated として削除済)。

**重要訂正**: 親 brief の「7 field × 3 = 21 density-witness」は実コードと不一致。実 structure は **8 density field** (`hpX_ent` を含む) を持ち、assembly 3 instance × 8 = **24 density sorry** が正しい (assembly docstring `:1307-1309` の "7 fields" 列挙が `hpX_ent` を脱落)。

---

## 主対象の最終形 (再掲)

assembly (`EPIStamToBridge.lean:1324`):

```lean
theorem isStamToEPIScalingHyp_of_stam_debruijn
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {X Y : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : Measurable X) (hY : Measurable Y)
    (h_noise : ...IsStamScalingNoiseHyp X Y P)
    (h_reg : ...) (h_pos_stam : ...) :
    IsStamToEPIScalingHyp X Y P
```

body 内の 3 instance (`EPIStamToBridge.lean:1413, 1419, 1425`):

```lean
have h_endpt_X : IsHeatFlowEndpointRegular X Z_X P := { ..., pX := sorry, ... }       -- 生 P.map X
have h_endpt_Y : IsHeatFlowEndpointRegular Y Z_Y P := { ..., pX := sorry, ... }       -- 生 P.map Y
have h_endpt_sum : IsHeatFlowEndpointRegular (X+Y) (Z_X+Z_Y) P := { ..., pX := sorry } -- 生 P.map (X+Y)
```

これら 3 instance が `csiszarLogRatioGap_antitoneOn_Ici_zero` (`:1438`) に渡り、その内部で
wall lemma `heatFlowEntropyPower_continuousWithinAt_zero` の `t = 0⁺` endpoint を充足するために消費される。

---

## A. `IsHeatFlowEndpointRegular` 7+1 field verbatim 表

定義: `InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:488-503`

```lean
structure IsHeatFlowEndpointRegular {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] where
  hX_meas : Measurable X
  hZ_meas : Measurable Z
  hXZ_indep : IndepFun X Z P
  v_Z : ℝ≥0
  hv_Z_pos : 0 < v_Z
  hZ_law : P.map Z = gaussianReal 0 v_Z
  pX : ℝ → ℝ
  hpX_nn : ∀ x, 0 ≤ pX x
  hpX_meas : Measurable pX
  hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x))
  hpX_int : Integrable pX volume
  hpX_mass : (∫ y, pX y ∂volume) = 1
  hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume
  hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume
```

| field | 型 (verbatim) | 意味 | 一般 a.c. で自動? |
|---|---|---|---|
| `hX_meas` | `Measurable X` | 入力可測性 | ✅ assembly では `hX` から (precondition) |
| `hZ_meas` | `Measurable Z` | 雑音可測性 | ✅ `hZX_meas` 等から |
| `hXZ_indep` | `IndepFun X Z P` | 入力⊥雑音 | ✅ `hXZX` 等から (noise model 供給) |
| `v_Z` | `ℝ≥0` | 雑音分散 | ✅ literal (1/1/2) |
| `hv_Z_pos` | `0 < v_Z` | 雑音分散正 | ✅ `one_pos`/`two_pos` |
| `hZ_law` | `P.map Z = gaussianReal 0 v_Z` | 雑音 = 𝒩(0,v) | ✅ `hZX_law` / `gaussianReal_add_gaussianReal_of_indepFun` から genuine 充足済 |
| `pX` | `ℝ → ℝ` | 入力密度関数 | **▲ a.c. なら存在 (Radon-Nikodym)。但し取り出すには下記 hpX_law が要る** |
| `hpX_nn` | `∀ x, 0 ≤ pX x` | 密度非負 | ✅ a.c. の R-N 微分は a.e. ≥ 0 (`pX` を非負版に取れる) |
| `hpX_meas` | `Measurable pX` | 密度可測 | ✅ R-N 微分は可測 |
| `hpX_law` | `P.map X = volume.withDensity (ENNReal.ofReal ∘ pX)` | **入力法則の a.c. 性そのもの** | **= a.c. の定義。一般 a.c. でちょうど成立** |
| `hpX_int` | `Integrable pX volume` | `pX ∈ L¹(volume)` | ✅ 確率密度なら `∫pX=1<∞` かつ `pX≥0` で L¹ |
| `hpX_mass` | `(∫ y, pX y ∂volume) = 1` | 全質量 1 | ✅ `IsProbabilityMeasure P` + a.c. から |
| `hpX_mom` | `Integrable (fun y => y ^ 2 * pX y) volume` | **有限 2 次 moment = 有限分散** | **❌ a.c. だけでは出ない (Cauchy/heavy-tail 反例)** |
| `hpX_ent` | `Integrable (fun x => Real.negMulLog (pX x)) volume` | **有限微分エントロピー h(X)** | **❌ a.c.+有限分散でも出ない (project 内で false-as-stated 確認済)** |

**field 数訂正**: 13 field 中、density 関連は `pX`/`hpX_nn`/`hpX_meas`/`hpX_law`/`hpX_int`/`hpX_mass`/`hpX_mom`/`hpX_ent` の **8 個** (前 6 = noise/measurability 系)。assembly では noise/measurability 系 5 field (`hX_meas`..`hZ_law`) を genuine 充足、**8 density field を sorry** にしている (`:1416-1417` 等)。よって assembly 全体の density sorry は **3 × 8 = 24** (brief の 21 は `hpX_ent` 脱落による過小)。

---

## B. 対象測度の特定 — 生入力 vs 平滑後 (最重要 verdict)

### 根拠 1: instance は生 `P.map X` に課される

assembly body (`EPIStamToBridge.lean:1413`):
```lean
have h_endpt_X : IsHeatFlowEndpointRegular X Z_X P := { ... }
```
第 1 引数 = 生の `X` (= 元の入力確率変数)。structure の `hpX_law` field (`:499`) は
`P.map X = volume.withDensity (ENNReal.ofReal ∘ pX)` を要求 — これは **生の入力法則 `P.map X`** の a.c. 性。
heat-flow 平滑された `X + √t Z` の法則ではない。

`EPIG2ConvEntropyMonotone.lean:426` のコメントも verbatim: 「`pX` is identified with the density of `μ.map X`」(= 生入力)。

### 根拠 2: wall lemma の endpoint は t→0⁺ で平滑が消える点

wall lemma (`EPIG2HeatFlowContinuity.lean:581`):
```lean
theorem heatFlowEntropyPower_continuousWithinAt_zero
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_endpt : IsHeatFlowEndpointRegular X Z P) :
    ContinuousWithinAt
      (fun t : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      (Set.Ioi (0 : ℝ)) 0
```
結論は `t = 0` での **右連続性**。t→0⁺ で平滑項 `√t·Z → 0` が消え、極限点の測度は **生 `P.map X`**。
だから wall lemma は「平滑後の良い測度」ではなく **生入力 `X` の密度・moment・entropy** を要求する
(平滑が regularity を供給してくれるのは interior t>0 のみで、endpoint では効かない)。

### verdict (B)

**3 instance はすべて生の入力測度 `P.map X` / `P.map Y` / `P.map (X+Y)` に課される。heat-flow 平滑後の測度ではない。** よって brief 仮説 (c)「平滑で witness 自動充足」は **成立しない**。endpoint continuity が本質的に生入力の regularity を要求する構造。

---

## C. 一般 a.c. での充足可能性 — field 別判定

### 自動で出る 6 field (a.c. + 確率測度から)

`hpX_law` (a.c. そのもの) → `pX`/`hpX_nn`/`hpX_meas` (R-N 微分) → `hpX_int`/`hpX_mass` (確率密度の L¹/質量)。
これらは「a.c. 確率測度」の定義をほどくだけ。Mathlib の R-N 機構 (`Measure.rnDeriv` / `withDensity_rnDeriv_eq` 系) で供給可能 (本調査では橋 lemma の file:line までは未確定、自動性は数学的に明らか)。

### 出ない 2 field

**`hpX_mom` (有限分散)** — a.c. だけでは **不成立**。反例: Cauchy 分布は密度 `1/(π(1+x²))` を持つ a.c. 確率測度だが `∫ y²·pX = +∞`。一般 heavy-tail 密度は有限分散を持たない。

**`hpX_ent` (有限微分エントロピー)** — a.c. + 有限分散でも **不成立**。これは project 内で明示的に確認済の事実:

> `EPIG2HeatFlowContinuity.lean:481-487` (structure docstring):
> 「Plan Phase 5-F: a 14th field `hpX_ent` ... was added. ... It replaces the former
> **false-as-stated** `negMulLog_integrable_of_density` lemma (which **claimed entropy
> finiteness followed from L¹ + second moment; a concentrated density refutes that**).」

つまりプロジェクトは「L¹+2次moment ⟹ negMulLog 可積分」を**偽**と判定し、その lemma を削除して
`hpX_ent` を独立の precondition field に昇格させた。一般 a.c. では `hpX_ent` は追加仮説。

### Mathlib 橋の loogle 確認 (すべて `Found 0 declarations`)

| 探した橋 | loogle query | 結果 |
|---|---|---|
| withDensity ⟹ 有限 2 次 moment | `MeasureTheory.Measure.withDensity, MeasureTheory.Integrable (fun y => y ^ 2 * _)` | **Found 0 declarations** |
| density ⟹ negMulLog 可積分 | `MeasureTheory.Integrable (fun x => Real.negMulLog _)` | **Found 0 declarations** |
| Mathlib に fisherInfo / 微分エントロピー概念 | `ProbabilityTheory.fisherInfo` / `.fisherInformation` / `.differentialEntropy` | **unknown identifier** (Mathlib 不在、project-local `FisherInfoV2.fisherInfoOfDensityReal` のみ) |

→ 「a.c. + 有限 Fisher info ⟹ 有限分散」のような救済橋も Mathlib には無い (そもそも Fisher info が Mathlib 不在)。

---

## D. 既存の充足例 (Gaussian 限定)

| witness | file:line | 充足対象 | 一般化に要るもの |
|---|---|---|---|
| `isBlachmanConvReady_gaussianPDFReal {mX mY : ℝ} {vX vY : ℝ≥0} (hvX : vX ≠ 0) (hvY : vY ≠ 0)` | `EPIBlachmanGaussianWitness.lean:344` | `IsBlachmanConvReady (gaussianPDFReal mX vX) (gaussianPDFReal mY vY)` (別 structure、density route 用) | **Gaussian 密度限定**。`@audit:ok` sorryAx-free |
| `isRegularDensityV2_gaussianPDFReal` | `EPIBlachmanGaussianWitness.lean:720, 739` (参照) | `IsRegularDensityV2 (gaussianPDFReal ...)` | Gaussian 限定 |

**`IsHeatFlowEndpointRegular` を充足する既存 instance lemma は存在しない** (`rg` で 0 件: assembly 内の `{ ... }` literal 直書きのみ、しかも density field は全 sorry)。Gaussian 入力に対してすら `IsHeatFlowEndpointRegular` の named witness は未整備。一般 a.c. 入力に対する instance は当然存在しない。

一般化に要るもの:
1. a.c. → R-N 密度供給 (6 field、Mathlib R-N 機構でほぼ機械的)。
2. `hpX_mom` (有限分散): **追加仮説 `∫ y²·pX < ∞` を主定理 signature に明示**するしかない (a.c. から導けない)。
3. `hpX_ent` (有限エントロピー): 同上、**追加仮説**。`hpX_mom` からも導けない (project 確認済)。

---

## 主要前提条件ボックス (事故源)

- **wall lemma `heatFlowEntropyPower_continuousWithinAt_zero` 自体は `@audit:ok` / sorryAx-free** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`、2026-06-05 sandwich closure)。**壁は wall lemma の証明側ではなく、その入力 `IsHeatFlowEndpointRegular` の供給側 (= assembly の density sorry)**。
- `hpX_law` は「P.map X が **volume に対して** a.c.」を要求 (Lebesgue 基準)。離散/特異入力 (Dirac, 離散測度) は density witness を持たないので、case-1 (両 a.c.) の前提そのもの。case-2/3 (片方/両方 singular) はこの witness 自体が存在しない → 別 case 扱い。
- `hpX_ent` は `Integrable (negMulLog ∘ pX) volume` であって `Integrable (pX · log pX)` の片側ではない。`negMulLog x = -x log x` は `x→0⁺` と `x→∞` の両裾で可積分性が問題になる — 有界 support でない一般密度では非自明。

---

## 自作が必要な要素 (優先度順)

1. **主定理 signature への `hpX_mom` / `hpX_ent` 追加仮説の明示** (最優先・設計判断)
   - a.c. から導けない 2 field を「隠す」と load-bearing hypothesis bundling 化のリスク。precondition として **明示的に X/Y の有限分散・有限エントロピーを仮定**するのが honest。
   - 工数: signature 変更のみ。但し「無条件」の看板は **下りる** (条件付き — 有限分散・有限エントロピー a.c. 入力)。
2. **a.c. → 6 自動 field の供給 lemma** (`acDensityWitness_of_haveDensity` 的補題)
   - 推奨実装: `Measure.HaveLebesgueDensity` / `rnDeriv` から `pX := (P.map X).rnDeriv volume |>.toReal` を取り、6 field を機械的に。
   - 工数: 中 (R-N の toReal 往復、`ENNReal.ofReal ∘ toReal` の a.e. 一致処理)。落とし穴: `rnDeriv` は `ℝ≥0∞` 値、structure は `ℝ→ℝ` 密度 → `toReal` 変換で `hpX_law` の `ENNReal.ofReal (pX x)` 整合に a.e. 補正が要る。
3. **`hpX_mom` / `hpX_ent` を仮定から構成する bridge は書かない** (書けない)
   - これらは Mathlib 壁ではなく **数学的に偽の含意** (a.c. ⇏ 有限分散)。橋を求めるのは誤り。

---

## Mathlib 壁の列挙 (`@residual(wall:...)` 対象か)

| 候補 | 真に Mathlib 不在か | 判定 |
|---|---|---|
| a.c. → 有限 2 次 moment | loogle `Found 0 declarations` | **壁ではない** — 偽の含意 (Cauchy 反例)。`@residual` 不可、追加仮説で対応 |
| density → negMulLog 可積分 | loogle `Found 0 declarations` + project 内で false-as-stated 削除済 | **壁ではない** — 偽の含意 (concentrated density 反例)。追加仮説で対応 |
| a.c. → R-N density witness (6 field) | Mathlib R-N 機構あり | **壁ではない** — 自作 plumbing (shared sorry 不要、数行) |

**真の Mathlib 壁は無い。** density-witness sorry は (a) 6 field = 自作 plumbing、(b) 2 field = 数学的に追加仮説必須、のいずれかで、`wall:` 分類は不適切。現 assembly の `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` 分類は **正しい** (Mathlib 壁ではなく、入力分布モデルを strengthen する plan 側の課題)。shared sorry 補題化の候補でもない (壁でないため)。

---

## 隠れ壁 verdict (最重要)

**verdict = (b) case-1 a.c. EPI は有限分散・有限エントロピーの追加 regularity を隠し持つ。**

- (a) 真に一般 a.c. で閉じる → **否**。`hpX_mom`/`hpX_ent` が a.c. から出ない (反例あり)。
- (b) 有限分散等の追加 regularity を隠し持つ → **是**。これが正答。
- (c) heat-flow 平滑で witness 自動充足 → **否**。instance は生 `P.map X` に課され、endpoint t→0⁺ で平滑が消えるため生入力の regularity を本質的に要求 (§B 根拠 1,2)。

**「無条件」EPI の射程への影響**: case-1 を閉じても得られるのは
**「a.c. かつ有限分散かつ有限微分エントロピーな入力に対する EPI」**であって、純粋な「一般 a.c. EPI」ではない。
看板を「無条件」とするなら、これは誇張 (under-hypothesized / name-laundering リスク)。
正直な命名は `epi_ac_finiteVariance_finiteEntropy` 等。
ただし教科書 EPI (Stam/Blachman) も通常 **有限分散 (or 有限 Fisher info) を暗黙に仮定**するので、
「textbook EPI の標準前提」と整合すると割り切る道はある — その場合 plan 側で
「無条件 = 退化 case (Dirac 等) を除く全 a.c. + 標準 moment 前提」と射程を **明文化**すべき。

---

## 撤退ラインへの距離

親 plan の撤退ラインは本調査の入力に含まれていない (brief 未供給) が、本 verdict は以下を要請:

- **新規撤退ライン提案**: 「case-1 を『一般 a.c. EPI』として閉じる」目標は達成不能 (verdict (b))。
  縮退案 = 「a.c. + `hpX_mom` + `hpX_ent` を明示前提とする conditional EPI」に目標を縮退し、
  その 2 前提を主定理 signature に **可視の仮説**として残す (sorry ではなく honest precondition)。
- **発動 = yes** (「無条件」を字義通り取る場合)。射程は「退化 case を除く有限分散・有限エントロピー a.c. 入力」に縮退。

---

## 着手 skeleton (a.c. → 6 自動 field 供給補題のみ; 2 field は仮説に残す)

```lean
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import InformationTheory.Shannon.EPIG2HeatFlowContinuity

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {X Z : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- a.c. 入力 + 雑音データ + 有限分散・有限エントロピー (この 2 つは a.c. から出ない追加前提) から
    `IsHeatFlowEndpointRegular` を組む。6 field は R-N から自動、`hpX_mom`/`hpX_ent` は明示仮説。 -/
theorem isHeatFlowEndpointRegular_of_ac
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (v : ℝ≥0) (hv : 0 < v) (hZ_law : P.map Z = gaussianReal 0 v)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)        -- ← a.c. から出ない追加前提
    (hpX_ent : Integrable (fun x => Real.negMulLog (pX x)) volume) -- ← a.c. から出ない追加前提
    : IsHeatFlowEndpointRegular X Z P := by
  sorry  -- @residual(plan:epi-uncond-ac) -- hpX_int/hpX_mass を R-N から導出、残りは hyp 直渡し

end InformationTheory.Shannon
```

注: `hpX_int` / `hpX_mass` は `hpX_law` + `IsProbabilityMeasure P` から導けるので仮説に出さず body で構成。
`hpX_mom` / `hpX_ent` は a.c. から出ないため signature の可視仮説として残す (sorry に隠さない = honest)。
