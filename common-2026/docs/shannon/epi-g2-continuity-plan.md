# Shannon EPI: G2 連続性壁 攻略サブ計画

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §G2 / 撤退ライン **L-Concl-A-θ**
> **消費 inventory**: [`epi-g2-continuity-inventory.md`](epi-g2-continuity-inventory.md)（DCT / 連続性 API verbatim 在庫）
> **消費 pivot**: [`epi-g2-continuity-pivot.md`](epi-g2-continuity-pivot.md)（proof-pivot-advisor 診断 — 但し difference 版限定の判定、下記参照）

> **RESULT (2026-06-03) — GATE NO-GO = 真 Mathlib 壁確定 (独立 honesty audit OK)**:
> Phase G2-2-b の go/no-go GATE を実装試行で撃った結果 **NO-GO**。DCT 機構
> (`MeasureTheory.continuousWithinAt_of_dominated`) は Mathlib に在るが、t=0⁺ 近傍一様
> integrable pointwise majorant が `IsDeBruijnRegularityHyp` の available field
> (`pX_nn`/`pX_meas`/`pX_law`/`pX_mom`) から組めない (既存 envelope `convDensityAdd_logFactor_poly_majorant`
> 系は全て `s∈Ioo(t/2,2t)` fixed-t で定数が t→0⁺ 発散)。共有壁補題
> `heatFlowEntropyPower_continuousOn` (`EPIG2HeatFlowContinuity.lean:78`、full `ContinuousOn (Ici 0)`、
> 1 sorry + `@residual(wall:heatflow-continuity)`) に集約し、ratio/差分 2 consumer を genuine 結線
> (自身 sorry なし)。誤分類 `@residual(plan:...)` → `wall:heatflow-continuity` 訂正、audit-tags.md
> Wall register に登録。**proof done に進めるには Mathlib 側の vanishing-Gaussian entropy 連続性
> machinery が必要** (現状は upstream wall)。設計判断: 当初 endpoint-only `ContinuousWithinAt` 案は
> consumer が measurability/indep hyp を持たず interior genuine 抽出を呼べないため full `ContinuousOn`
> 1-sorry に再設計 (G2-1 内部 genuine 化を部分断念)。

## 進捗

- [ ] G2-0 共有補題 signature 決定（在庫 + consumer 結論型 verbatim 照合）📋
- [ ] G2-1 内部 `Ioi 0` 連続性（易、単独 ship 可）📋
- [ ] G2-2 端点 `t=0⁺` DCT 連続性（難、本丸、go/no-go GATE 内蔵）📋
- [ ] G2-3 共有補題を 2 consumer に wire + slug 統一 📋

## ゴール / Approach

**ゴール**: `csiszarLogRatioGap_continuousOn`（`EPIStamToBridge.lean:1030`、ratio 版）の
`sorry` を genuine 化し、R-5-c（`csiszarLogRatioGap_antitoneOn_Ici_zero`、`:1059`）を
本物にする。本連続性は `:1098` で `antitoneOn_of_deriv_nonpos` の `hf` 引数として
**live に消費される**（verbatim 確認済、確定事実 1）。

**Approach（全体戦略）**:
3 つの `entropyPower (P.map (X + √t·Z))` 項に共通する解析核を、1 本の共有 sorry 補題
`heatFlowEntropyPower_continuousWithinAt`（仮称、inventory 着地 skeleton 名）に集約する。
ratio 版 `csiszarLogRatioGap_continuousOn` と差分版 `csiszarGap1Source_continuousOn`
（`:1173`）はいずれもこの 1 本を consume する設計（audit-tags.md「共有 Mathlib 壁: shared
sorry 補題パターン」採用、inventory 気づき採用）。これにより壁 1 件 = `sorry` 1 件に集約され、
consumer 側 file は壁が閉じれば全て genuine 化する。

連続性は `ContinuousOn (Set.Ici 0)` を 2 ケースに分解する:
- **内部 `Ioi 0`**: 既存 genuine 資産 `csiszarGap1Source_differentiableOn_interior`（`:1186`、
  `sorry` 無し、verbatim 確認済）+ `DifferentiableOn.continuousOn` で無料。ratio 版も
  `csiszarLogRatioGap_differentiableOn_interior`（`:1099` で呼ばれている既存補題）から同様に出る。
- **端点 `t=0⁺`**: 密度レベル DCT（`MeasureTheory.continuousWithinAt_of_dominated`、inventory
  category 3 で verbatim、5 前提完備）。唯一の難所は **t=0⁺ 近傍で `negMulLog f_t` を t 非依存
  に支配する integrable majorant `g` の構成**。これが本計画の go/no-go GATE（G2-2-b）。

**2 つの recon の判定割れの裁定**（確定事実 1 に従う）:
advisor pivot は「non-load-bearing → 再分類のみ」と判定したが、これは **差分版**
（`csiszarGap1Source_*`、D6 削除済で dead）に限った trace に基づく誤適用。ratio 版
（R-5-c 経由）は live consumer を持つ（`:1098`、verbatim 確認済）ため pivot の「投資不要」結論は
**ratio 版には適用しない**。inventory は「DCT 機構完備・bound 構成が唯一の核・自作可能」と
判定。本計画は inventory のルートを採り、bound 構成を **実装試行で go/no-go 決着** させる。

## 確定事実（verbatim 確認済、本計画前提）

1. **load-bearing（ratio 版）**: `csiszarLogRatioGap_continuousOn`（`:1030`）は
   `csiszarLogRatioGap_antitoneOn_Ici_zero`（`:1059`）の body `:1098` で
   `antitoneOn_of_deriv_nonpos` の `hf` 引数として live 消費（Read 確認）。閉じれば R-5-c genuine 化。
2. **差分版は dead**: `csiszarGap1Source_antitoneOn_Ici_zero`（D6）は削除済（`:1206-1213` の
   削除注記を Read 確認）。よって差分版連続性 `csiszarGap1Source_continuousOn`（`:1173`）は
   live consumer ゼロ。pivot の non-load-bearing 判定はこの版に対しては正しい。
3. **未解決は端点 t=0 の 1 点のみ**: 内部 `t>0` は `csiszarGap1Source_differentiableOn_interior`
   （`:1186`、`sorry` 無し、Read 確認）+ `HasDerivAt.continuousAt` で無料。
4. **境界値（直感ではなく Read 確認、CLAUDE.md 数値 verbatim 義務）**:
   - `entropyPower μ := Real.exp (2 * differentialEntropy μ)`（`EntropyPowerInequality.lean:101-102`）。
   - `differentialEntropy μ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume`
     （`DifferentialEntropy.lean:45-46`）。**negMulLog 形（rnDeriv の toReal を引数に）**。
   - `differentialEntropy (Measure.dirac m) = 0`（`DifferentialEntropy.lean:155-156`）
     → `entropyPower (dirac) = exp 0 = 1`。直感「−∞ / 0」は誤り。
   - `gaussianReal μ 0 = Measure.dirac μ`（`Real.lean:207`）。**端点 t=0 で Dirac に潰れるのは
     noise factor のみ**。`csiszarGap1Source` の各 entropyPower 引数 `P.map(X+√0·Z) = P.map X` は
     元測度の push-forward で退化しない。端点で gap が退化定数化する事故（L-DBD 型）は起きない。
5. **regularity hyp が供給する密度witness（Read 確認）**: `IsDeBruijnRegularityHyp`
   （`EPIStamDischarge.lean:250`）は `reg_at : ∀ t, 0<t → IsRegularDeBruijnHypV2`、後者
   （`FisherInfoV2DeBruijn.lean:204`）が `pX`（X の Lebesgue 密度 witness、4 field）+ `density_t`
   + conv-pin（`density_t = convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩)`、`:234-258`）を持つ。
   **`reg_at` / `density_t` は `0 < t` 限定**。t=0 の密度 witness は `pX` 自身（`pX_law :
   P.map X = withDensity (ofReal∘pX)`、`:233`）。

## Phase G2-0 — 共有補題 signature 決定 📋

bound 構成に着手する前に、共有補題の正確な signature を 1 度で確定する（mid-proof pivot 防止、
CLAUDE.md「Mathlib-shape-driven Definitions」）。

- [ ] **0-a** `entropyPower` / `differentialEntropy` 実定義の再確認（確定事実 4 で済、negMulLog 形・
  rnDeriv の toReal 引数を skeleton に反映）。
- [ ] **0-b** consumer 2 箇所の要求結論型を verbatim 照合:
  - ratio 版 `csiszarLogRatioGap_continuousOn`（`:1037-1040`）: 結論
    `ContinuousOn (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t) (Set.Ici 0)`。
  - 差分版 `csiszarGap1Source_continuousOn`（`:1180`）: 結論
    `ContinuousOn (fun t => csiszarGap1Source X Y Z_X Z_Y P t) (Set.Ici 0)`。
  - 両者とも `csiszar*Gap = entropyPower 項の log / sub or sub` 合成。共有補題は **単一項**
    `t ↦ entropyPower (P.map (X + √t·Z))` の `ContinuousWithinAt (Set.Ici 0) 0` を出す形に切る
    （inventory skeleton `heatFlowEntropyPower_continuousWithinAt` の結論型を踏襲）。外側合成
    （log/exp/sub）は inventory category 4（全て既存、`ContinuousOn.log`/`.sub`/`Real.continuous_exp`）
    で consumer 側に組む。
- [ ] **0-c** 共有補題の **引数（regularity precondition）決定**:
  - `(X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]` + `h_reg : IsDeBruijnRegularityHyp X Z P`。
  - 注意: consumer は項ごとに `(X+Y, Z_X+Z_Y)` / `(X, Z_X)` / `(Y, Z_Y)` の 3 組で呼ぶため、
    共有補題は **汎用の `(X, Z)` で立て**、consumer 側が 3 回 instantiate する。
  - **load-bearing 禁止確認**: `h_reg` は密度 regularity（`pX`/`density_t`/tail 等の precondition）
    であって連続性の核を bundle しない。連続性結論を hyp に含めない（仮説束化禁止、CLAUDE.md）。
- [ ] **0-d** 当て先 Mathlib lemma の完全 namespace を skeleton コメントに固定（下記 G2-1/G2-2 で列挙）。

成果物: `InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean`（新規 file）の skeleton
（補題 signature + `:= by sorry`）。`proof-log: no`（signature 決定のみ）。

## Phase G2-1 — 内部 `Ioi 0` 連続性（易、単独 ship 可）📋

- [ ] **1-a** atom: `t ↦ entropyPower (P.map (X+√t·Z))` の `ContinuousAt`（`0 < t`）。
  - 当て先: 各項の HasDerivAt は consumer 側既存補題 `csiszarGap1Source_hasDerivAt`
    （`EPIStamToBridge.lean:476`、`{t} (ht : 0<t)` → Ioi 0、genuine）/
    `csiszarLogRatioGap_hasDerivAt`（`:682`）。これは **gap 全体** の導関数。
  - 共有補題レベルでは単項の連続性が要るが、内部は consumer 側 differentiableOn 資産で済むため、
    **共有補題は端点専用**（`ContinuousWithinAt ... 0`）に絞り、内部は consumer が
    `csiszarGap1Source_differentiableOn_interior`（`:1186`、genuine）+
    `DifferentiableOn.continuousOn`（`Mathlib/Analysis/Calculus/FDeriv/Basic.lean:658`）で組むのが最安。
- [ ] **1-b** atom: `ContinuousOn (Ioi 0)` 化。当て先:
  - `DifferentiableOn.continuousOn`（`Mathlib/Analysis/Calculus/FDeriv/Basic.lean:658`）:
    `(h : DifferentiableOn ℝ f s) : ContinuousOn f s`。`interior (Ici 0) = Ioi 0`（`interior_Ici`）。
  - `ContinuousAt.continuousWithinAt`（Mathlib `Topology`）で interior 点を `ContinuousOn` に編入。
- [ ] **1-c** ratio 版でも同型（`csiszarLogRatioGap_differentiableOn_interior` は `:1099` で
  既に呼ばれている既存補題、Read で genuine 確認すること）。

**段階 ship**: G2-1 は既存 genuine 資産の機械的合成のみで `sorry` なしに到達可能なら、
G2-2 と独立に **単独 commit**（type-check done、CLAUDE.md DoD）。但し最終的に `ContinuousOn (Ici 0)`
は端点込みなので、G2-1 単独では補題は完成せず、内部部分達成として honest に分離公開（仮説束化禁止）。
`proof-log: yes`（既存資産の合成可否を記録）。

## Phase G2-2 — 端点 `t=0⁺` DCT 連続性（本丸、go/no-go GATE）📋

唯一の真の analytic content。3 sub-atom に分解し、**2-b が GATE**。

### G2-2-a — DCT 適用形（5 前提 verbatim 列挙）

当て先: `MeasureTheory.continuousWithinAt_of_dominated`
（`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:440`、inventory category 3 verbatim）。

```
{F : X → α → G} {x₀ : X} {bound : α → ℝ} {s : Set X}
  (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ)
  (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a)
  (bound_integrable : Integrable bound μ)
  (h_cont : ∀ᵐ a ∂μ, ContinuousWithinAt (fun x => F x a) s x₀)
  : ContinuousWithinAt (fun x => ∫ a, F x a ∂μ) s x₀
```

instantiation:
- `X := ℝ`（パラメータ `t` の空間、`[TopologicalSpace] [FirstCountableTopology]` 充足）、`x₀ := 0`、
  `s := Set.Ici 0`、`G := ℝ`（`[NormedAddCommGroup] [NormedSpace ℝ]` 充足）、`μ := volume`。
- `F t x := Real.negMulLog (f_t x)`、`f_t x := ((P.map (fun ω => X ω + √t·Z ω)).rnDeriv volume x).toReal`。
  - **t=0 の f_0 = `(P.map X).rnDeriv volume x`.toReal**（noise 消滅、確定事実 4）。t>0 では
    conv-pin（確定事実 5）で `f_t = convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩)` と同定できる。
- [ ] **2-a-1** `hF_meas`: 各 `f_t` の AE strongly measurable。供給元: `IsDeBruijnRegularityHyp` の
  `pX_meas`（`:230`）+ conv の可測性（`measurable_gaussianPDFReal` は Assembly で既使用、`:178`）。
  negMulLog は連続なので `.comp`。
- [ ] **2-a-2** `h_cont`: a.e. `x` で `t ↦ negMulLog (f_t x)` が `t=0⁺` で `ContinuousWithinAt`。
  conv-pin の `convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩) x` は `t→0⁺` で `pX x` に各点収束
  （Gaussian heat kernel が Dirac に弱収束、但し **各点 conv 値の収束は要証明** — Assembly に
  既存があるか rg で確認、無ければ自作 atom）。negMulLog 連続合成。

### G2-2-b — bound 構成 sub-problem（go/no-go GATE）★

t=0⁺ 近傍一様 integrable majorant `g` の構成。**ここが本計画の決着点**。

- [ ] **2-b-1** available regularity の棚卸し（Read 済資産）:
  - `gaussianPDFReal_le_prefactor'`（`Assembly.lean:146-148`、Read 確認）:
    `gaussianPDFReal 0 v u ≤ (Real.sqrt (2*π*v))⁻¹`。**この prefactor は v=t→0⁺ で `+∞` に発散**。
    → conv 密度 `f_t x ≤ (sqrt(2πt))⁻¹` という sup bound は **t 非依存 majorant を与えない**
    （t→0 で blow up）。これが inventory が懸念した「Dirac 接近で密度が尖る」事故の正体。
  - `convDensityAdd_negMulLog_integrable`（Assembly、`@audit:ok`、audit-tags.md
    `entropy-finiteness` CLOSED 記載）: **固定 t>0** での `Integrable (negMulLog (pX∗g_t))`。
    t 非依存ではない。
  - `convDensityAdd_logFactor_poly_majorant` + `gaussGradMaj`（Assembly、CLOSED 記載）:
    **固定 t** の polynomial / gradient envelope。t-uniform かどうかは未確認。
- [ ] **2-b-2** **GATE 判定**: 上記から t=0⁺ 近傍一様の integrable `g` が組めるか:
  - **候補 A（majorant が pX 側で取れる）**: noise が消えるだけで `P.map X` 側は退化しない
    （確定事実 4）。`negMulLog (pX∗g_t)` を `negMulLog pX` 近傍 + Gaussian-tail で t 非依存に
    支配できれば go。conv は `‖pX∗g_t‖₁ = ‖pX‖₁`（mass 保存）なので **L¹ レベルでは一様**だが、
    `continuousWithinAt_of_dominated` は **pointwise ‖F t x‖ ≤ bound x** を要求するため L¹ 一様では
    不十分。pointwise t-uniform envelope が要る。
  - **候補 B（envelope `max` 形）**: Assembly の `_chain_domination` envelope（`:103`、`s=t` で
    使用、Read 確認）/ `convDensityAdd_logFactor_poly_majorant` が `s ∈ [0,t]` 一様形に
    一般化できるか。`gaussianPDFReal 0 ⟨max s 0,_⟩`（`:99/111`）という `max s 0` clamp は既に
    s≤0 を 0 に潰す設計で、端点近傍 envelope の素地がある。これが `s∈[0,δ]` 一様 integrable に
    なるか実装試行。
  - **不足の特定**: 候補 A/B いずれも組めない場合、足りないのは「conv 密度の **時間一様
    pointwise integrable envelope**」= Mathlib にも InformationTheory にも無い真壁。
- [ ] **2-b-3** **go/no-go 決定（GATE 出力）**:
  - **go（bound が available regularity から組める）** → 2-a/2-c を埋めて共有補題 genuine 化、
    plan-closable。`@residual` 不要（proof done 方向）。
  - **no-go（組めない = 真壁確定）** → 共有補題 body を `sorry` + `@residual(wall:heatflow-continuity)`
    に再分類（下記撤退ライン）。classification 訂正（現 `plan:` slug → `wall:`）を併せて実施。

`proof-log: yes`（GATE 判定の根拠 = どの regularity field が bound を供給した/しなかったかを記録、
次セッションの誤投資防止）。

### G2-2-c — 外側合成（exp / log / sub）

GATE が go の場合のみ。当て先（inventory category 4、全て既存）:
- `Real.continuous_exp`（`exp(2·h)` の外側、無条件）。
- `ContinuousWithinAt.const_mul`（`2·∫`）。
- ratio 版のみ `ContinuousOn.log`（`Log/Basic.lean:491`、`∀ x∈s, f x ≠ 0` を `entropyPower_pos`
  `EntropyPowerInequality.lean:108`（`@audit:ok`）+ `add_pos` で供給）。
- `ContinuousOn.sub`（`Mathlib/Topology/ContinuousOn`）。

## Phase G2-3 — 共有補題を 2 consumer に wire + slug 統一 📋

- [ ] **3-a** ratio 版 `csiszarLogRatioGap_continuousOn`（`:1030`）の body を、共有補題
  `heatFlowEntropyPower_continuousWithinAt` を 3 組 instantiate（`(X+Y,Z_X+Z_Y)`/`(X,Z_X)`/`(Y,Z_Y)`）
  + 外側 log/sub 合成 + 内部 differentiableOn 合成、で書き換え。
- [ ] **3-b** 差分版 `csiszarGap1Source_continuousOn`（`:1173`）も同共有補題で wire。
  **但し確定事実 2**: 差分版は live consumer ゼロ（dead code）。GATE が go なら genuine 化して残す。
  **GATE が no-go**（共有補題が `sorry` 残置）なら、差分版は dead なので
  `@audit:retract-candidate(no-live-consumer)`（advisor pivot atom-3 提案）を付与し削除候補とする
  （別 task、本計画では retract 候補マークのみ）。
- [ ] **3-c** **slug 統一**: 現状 ratio 版・差分版とも
  `@residual(plan:epi-stam-to-conclusion-phaseA-plan)`（誤分類: plan 1 本では閉じない真壁の
  可能性を含意せず）。GATE 結果で分岐:
  - go → `@residual` 除去（genuine、`@audit:ok` は独立 auditor が付与）。
  - no-go → `@residual(wall:heatflow-continuity)` に統一（共有補題 1 本のみが保持、consumer 側は
    補題呼び出しのみで `@residual` を持たず proof-done 判定可能、audit-tags.md「共有 Mathlib 壁」）。
- [ ] **3-d** 新 file を `InformationTheory.lean` に import 1 行追加。

`proof-log: no`（wire は機械的）。

## 撤退ライン

**L-G2-1（端点 bound 不成立 = 真壁確定）**: G2-2-b GATE で t=0⁺ 一様 integrable majorant が
available regularity（`IsDeBruijnRegularityHyp` の `pX`/`density_t`/conv envelope）から **当該
セッションで組めない** 場合。honest 撤退手順（CLAUDE.md「sorry を書けない箇所での対処順序」第一選択
= shared sorry 補題への退避、tier 2）:

1. 共有補題 `heatFlowEntropyPower_continuousWithinAt` の **signature は本来の結論型のまま保持**
   （`ContinuousWithinAt ... (Set.Ici 0) 0`、仮説束化禁止 — 連続性結論を hyp に含めない）。
2. body を `sorry`。docstring 末尾に `@residual(wall:heatflow-continuity)`。
3. consumer 2 箇所は共有補題を呼ぶだけ（`@residual` を持たない、壁 file のみ未完成）。
4. **audit-tags.md「Wall name register」に `heatflow-continuity` 行を新規追記**（loogle で 0 件
   再確認の上、inventory が `entropyPower`/`differentialEntropy` 連続性は Mathlib・InformationTheory
   双方不在と既確認）。semantic 区別: 既存 `debruijn-integration`（積分形）/ `fisher-finiteness`
   （score 2乗可積分、CLOSED）/ `entropy-finiteness`（固定 t の log-factor 可積分、CLOSED）と異なり、
   本壁は **conv 密度の時間一様 pointwise integrable envelope**（端点連続性専用）。
5. 共有 sorry 補題は **shared wall lemma 新規追加** に該当 → orchestrator は独立 honesty audit
   （`honesty-auditor`）を起動（CLAUDE.md「Independent honesty audit」起動条件）。

**L-G2-2（GATE が go だが exp/log 外側合成で詰まる）**: 想定低（全て既存 API、inventory
category 4）。詰まったら端点 atom のみ `sorry` + `@residual(wall:heatflow-continuity)`、内部
G2-1 は genuine 部分達成として分離公開（honest 命名）。

### 推奨次手（2026-06-04 更新）

de Bruijn genuine 化後の 4 角度再評価（判断ログ #3）を踏まえた、次に G2 を attack する際の
**推奨アタック順**（proof-pivot-advisor 気づき）:

- **次手: full DCT（R5 Vitali）より先に「sum 項片側 USC」ルートを撃つ**。判断ログ #3 の
  「3 項 → sum 項 1 個」reduction が genuine に成立するため、`differentialEntropy` の sum 項
  `t→0⁺` **上半連続性（USC）** のみを攻める片側ルートが、R5 Vitali（full DCT、特大 150–250 行、
  既存 `epi-g2-main-closure-inventory.md` 参照）の両側 majorant より弱い片側条件で済む可能性がある。
  USC 攻略は Fatou（`lintegral` の LSC、Mathlib `VitaliCaratheodory.lean` に 4 件）で直接攻める。
- **最初の GATE = reverse-Fatou 障害を撃つ**: ただし判断ログ #3 の reverse-Fatou 障害
  （`φ(p)=−p log p` の上界 `1/e` が無限測度 `volume` 上で非可積分）が **最初の GATE** になる。
  この GATE を最初に撃ち、抜けられなければ R5 Vitali（full DCT）に戻る。
- **規模見積り不変**: いずれのルートでも multi-session 規模は変わらない。本壁は de Bruijn
  genuine 化後も残る唯一の真 Mathlib 壁（`wall:heatflow-continuity`）であり、closure には
  Mathlib 側の vanishing-Gaussian entropy 連続性 machinery が要る。

## 段階 ship（DoD 2 段階）

- **G2-1（内部、易）**: 既存 genuine 資産の機械的合成。単独 commit 可（type-check done）。
  最終補題は端点込みなので G2-1 単独では未完成、内部部分達成として honest 分離。
- **G2-2 が 1 session 超**: 端点 atom を `sorry` + `@residual(wall:heatflow-continuity)` で
  type-check done、commit して次セッション引き継ぎ。
- **proof done**: 共有補題 + 2 consumer が全て 0 `sorry` / 0 `@residual`、独立 auditor が
  `@audit:ok` 付与。moonshot 集計対象。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2 recon の判定割れの裁定（起草時）**: advisor pivot「non-load-bearing → 再分類のみ」は
   差分版（D6 削除済 dead）に限った trace。ratio 版は `:1098` で live 消費（確定事実 1、Read 確認）
   のため pivot 結論を ratio 版に適用せず、inventory ルート（DCT + bound 構成）を採用。bound 構成の
   go/no-go は G2-2-b GATE で実装試行決着とする（inventory「自作可能」と pivot「真壁」の割れを
   コードで決める）。
2. **prefactor blow-up の発見（起草時、Read 確認）**: `gaussianPDFReal_le_prefactor'`
   （`Assembly.lean:146`）の sup bound `(sqrt(2πt))⁻¹` は t→0⁺ で発散するため、素朴な sup-majorant
   は t-uniform にならない。GATE の核は「pointwise t-uniform envelope を pX 側 / `max s 0` clamp
   envelope から組めるか」に縮退する。L¹ mass 保存（`‖pX∗g_t‖₁=‖pX‖₁`）は一様だが DCT は pointwise
   bound 要求なので不十分、という drift 注意点を G2-2-b に明記。

3. **de Bruijn genuine 化後の G2 迂回再評価（2026-06-04、全 NO-GO）**: EPI 壁の最新 honest state
   が変わった（per-time de Bruijn `FisherInfoV2.deBruijn_identity_v2` /
   `debruijnIdentityV2_holds_assembled` が sorryAx-free 化、`wall:debruijn-integration` /
   `wall:stam-step2-density` が CLOSED 化、commit `5ca9b14`、audit-tags.md register 更新済）。これにより
   EPI で残る真 Mathlib 壁は **G2 `wall:heatflow-continuity` 唯一**。この新 state を前提に、既存
   `epi-g2-main-closure-inventory.md` の代替 6 ルートとは異なる新角度で G2 迂回を 4 角度
   再評価（proof-pivot-advisor 再評価 + orchestrator 独立検算）。**全角度 NO-GO だが reduction
   の一部は genuine に成立**:

   - **角度1 — de Bruijn FTC 直接積分ルート: NO-GO**。genuine per-time de Bruijn を
     `t∈(0,∞)` で FTC 積分し
     `differentialEntropy(X+√T·Z) − differentialEntropy(X+√ε·Z) = ∫_ε^T (1/2)J dt` を得て
     `ε→0⁺` 極限を狙う案。**致命的障害**: Fisher bound は `gaussianConv_fisher_le_inv_var`
     （`FisherConvBound.lean:405`、`J(t) ≤ 1/t` のみ）で、被積分 `(1/2)J(t)` の majorant
     `1/(2t)` が **t=0⁺ で非可積分**（`∫_0 1/t dt = log T − log ε → +∞`）。de Bruijn が
     出さない「`J(t)` の t→0⁺ 可積分 majorant（= entropy が有限極限に収束）」が要り、これは
     entropy 端点連続性と同値の情報量。FTC は内部を genuine に積分するだけで端点情報を生成しない。

   - **角度2/3 — antitone 端点を片側半連続に弱化: 理論上 reduction 成立、closure には至らず**
     （orchestrator 独立検算、記録価値あり）:
     - antitone 引数は `r(0) ≥ r(1) = 0` を `AntitoneOn r (Ici 0)` の 0/1 評価で得る。
       `r(0) ≥ 0` には full continuity 不要で **`r` の t=0 での上半連続性（USC）のみで十分**
       （USC ⟹ `r(0) ≥ limsup_{t→0⁺} r(t) ≥ liminf ≥ 0`、∵ `r(t)≥0` on (0,1] は interior
       antitone + `r(1)=0` で genuine）。
     - `r = log eP_sum − log(eP_X + eP_Y)` の USC を分解: log eP_sum の USC = `h_sum` の USC、
       `−log(eP_X+eP_Y)` の USC = `h_X`,`h_Y` の **LSC**。
     - **de Bruijn 単調性で X,Y 項は無料化**: de Bruijn `dh/dt = (1/2)J ≥ 0` ⟹ `h` は `t`
       単調増加。単調増加関数 `g` は `g(0) ≤ g(0⁺)` なので **LSC は t=0 で自動成立**（易しい
       方向）。よって `h_X`,`h_Y` 項の必要条件（LSC）は monotonicity から free。
     - **残る壁は sum 項の USC のみ**: `h_sum` の USC = `g(0) ≥ g(0⁺)` =（単調性 `g(0)≤g(0⁺)`
       と合わせて）`g(0)=g(0⁺)` = **連続性そのもの**。すなわち 3 項 full continuity が **sum 項
       1 個の連続性（USC）に縮小**するが、sum 項の連続性は既存共有壁補題と同難度。
     - **reverse-Fatou で USC を出せるか: NO-GO**。`φ(p)=−p log p` は `φ ≤ 1/e` で上から有界
       だが、`1/e` は `volume`（無限測度）上で非可積分のため reverse-Fatou（上からの dominated
       convergence）が効かない。USC は依然 time-uniform 可積分性を要し壁を移送するのみ。

   **結論**: de Bruijn genuine 化後も G2 端点連続性は不可避。**ただし「3 項 → sum 項 1 個」
   reduction は genuine に成立**するので、将来 closure を attack する際は (a) `h_X`,`h_Y` を
   monotonicity-LSC で free にし、(b) sum 項のみ USC/連続性を attack する形に共有壁補題
   `heatFlowEntropyPower_continuousWithinAt` の使われ方を組み替えられる（wall sorry 件数は 1 の
   ままだが invocation が sum 項に集約され、X/Y 項が genuine 化）。

---

## Route B — machinery 自前構築（2026-06-04 再フレーム + crux 分離）

> ユーザー選択（2026-06-04）: 仮説強化（route A）ではなく **machinery 自前構築**。ただし
> 「弱収束 machinery」の literal な解釈は誤りで、実体は L¹ mollifier 収束 + negMulLog 一様可積分性。
> 本セクションは route B の正しい形と、単独 closure 可否を分ける crux を確定する。

### B-0 再フレーム（確定事実、verbatim 由来）

1. **弱収束は entropyPower 収束を与えない**（inventory category 1）: 微分エントロピーは弱収束で
   **下半連続止まり**。「分散→0 ガウス畳み込みで元測度に弱収束」を作っても端点 entropyPower 収束は
   出ない。→ 弱収束 machinery は端点 closure に対して **non-load-bearing**。攻めるのは密度レベルの
   強収束。
2. **真に必要な 2 層**:
   - **層1 L¹ mollifier 収束**: `f_t := convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩)` が
     `t→0⁺` で `pX` に **L¹ 収束**（近似単位元）。手持ち `pX` 正則性（L¹ 非負可測 + 2次モーメント）
     から **genuine 構築可能**と見込む。部品: `tendsto_convDensityAdd_gaussian_zero`
     （`EPIConvDensityRegular.lean:148`）、`convDensityAdd_*`（`FisherInfoV2DeBruijnAssembly.lean`
     多数）。
   - **層2 negMulLog 一様可積分性**: 層1 の L¹ 収束を `∫ negMulLog f_t → ∫ negMulLog pX` に持ち上げ。
     `continuousWithinAt_of_dominated` の t 非依存 integrable majorant が必要。**これが真の壁**
     （`wall:heatflow-continuity` の本体）。per-t 版 `convDensityAdd_negMulLog_integrable`
     （`FisherInfoV2DeBruijnAssembly.lean:2529`、private、固定 t）は既存 — 壁は「t→0 一様化」一点。

### B-crux（2026-06-04 独立再確認で sharpen — FTC ショートカット否定）

> **当初仮説（撤回）**: 「`integrable_deriv`（∫_0^T J<∞）+ de Bruijn 積分恒等式で FTC ショートカット、
> DCT 不要で端点連続性が出る」。→ **循環のため否定**。以下が verbatim 根拠。

**FTC ショートカットが循環する理由（確定事実、Read 確認）**:
`debruijnIntegrationIdentity_holds`（`FisherInfoV2DeBruijnGenuine.lean:85`、genuine sorryAx-free）は
`h(X+√T·Z) − h(X) = ∫_{Ioo 0 T} (1/2)J dt` を出すが、前提 `h_path : IsDeBruijnPathRegular X Z P T`
（`FisherInfoV2DeBruijn.lean:331`）の **`cont` フィールドが**

```
cont : ContinuousOn (fun s => differentialEntropy (P.map (gaussianConvolution X Z s))) (Set.Icc 0 T)
```

= **G2 端点連続性そのもの**（`Icc 0 T` は端点 0 込み）。積分恒等式は FTC
（`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`、:115）に `h_path.cont` を渡して閉じている。
よって積分恒等式で端点連続性を出すのは「証明したい連続性を仮定する」循環。**de Bruijn 積分形は genuine
だが端点連続性 `.cont` を内包しており、G2 より閉じてはいない（G2 と結合）**。

**内部導関数 + 可積分性だけでは端点連続性が出ない（確定、反例）**:
- 内部 `HasDerivAt f f'` on `Ioo 0 T`（genuine、`debruijnIdentityV2_holds_assembled`）+ `f'`
  interval-integrable on `[0,T]`（`integrable_deriv`）だけでは端点 `ContinuousWithinAt (Ioi 0) 0` は
  **derive できない**。反例: `f(t)=0 (t>0), f(0)=1` は内部導関数 0（可積分）だが端点不連続。
  端点連続性は内部微分情報の外の追加解析内容。
- de Bruijn 単調性 `f'=(1/2)J≥0` で `lim_{t→0⁺} f(t) = L` の **存在**は無料（単調 + `f'` 可積分 ⇒
  `f(ε)=f(T)−∫_ε^T f'→f(T)−∫_0^T f'=L` 有限）。だが `L = f(0) = h(X)`（= 連続性）は壁。
  `f(T)−∫_0^T f' = h(X)` は積分恒等式の端点版で、上記循環。

**したがって route B の真の解析内容（DCT/半連続性に戻る）**: L¹ mollifier 収束 `f_t→pX`（層1、作れる）
を `∫ negMulLog f_t → ∫ negMulLog pX`（= `L=h(X)`）に持ち上げる段が本丸。持ち上げには (i) negMulLog の
t→0 一様可積分性（DCT、GATE NO-GO の majorant）か、(ii) エントロピー汎関数の mollification 下での
半連続性（`-p log p` の凹性 + L¹ 収束、Mathlib 未整備）のいずれか。**どちらも hard analytic content で
1-session スコープ外、moonshot**。

**裁定済み GO/NO-GO**: 端点連続性は内部微分 + `integrable_deriv` から **free では出ない**（NO-GO 追認、
sharper 根拠）。残る genuine 前進は B-1（mollifier L¹ 収束、下記）のみ。本丸 B-2 は moonshot。

### B-1〜B-3 実装分解（B-crux が GO の場合）

- **B-1 L¹ mollifier 収束補題**（genuine、crux と独立に着手可・再利用資産）:
  `Filter.Tendsto (fun t => ∫ x, |convDensityAdd pX g_t x − pX x| ∂volume) (𝓝[>] 0) (𝓝 0)`。
  近似単位元。既存 `convDensityAdd` 部品で組む。**crux の結果に依らず正しいので先行 ship 候補**。
- **B-2 一様 majorant 構成**（crux GO 前提）: `integrable_deriv` 由来の有限性から
  `g : ℝ→ℝ`, `Integrable g volume`, `∀ᶠ t in 𝓝[>]0, ∀ᵐ x, ‖negMulLog (f_t x)‖ ≤ g x` を構成。
  **本丸**。NO-GO なら B-2 は不可 → 仮説強化（route A 合流）。
- **B-3 共有壁補題 closure**: `heatFlowEntropyPower_continuousWithinAt_zero`
  （`EPIG2HeatFlowContinuity.lean:137`）の `sorry` を B-1 + B-2 + `continuousWithinAt_of_dominated`
  で genuine 化。consumer（ratio/差分）は既に genuine 結線済なので壁 closure で EPI が前進。

### 撤退口（route B）

- B-crux NO-GO（悪い inhabitant 残存）→ `heatFlowEntropyPower_continuousWithinAt_zero` の signature を
  仮説強化版に再設計（`IsDeBruijnRegularityHyp` に regularity field 1 つ追加 or 端点専用 hyp）。
  **load-bearing 化禁止**（連続性結論を hyp に bundle しない、追加は negMulLog 一様可積分 = precondition）。
  signature 変更につき独立 honesty audit 起動（CLAUDE.md 起動条件「signature 変更で honesty 意味が変わる」）。
- B-2 が当該セッション（〜120 行）で組めない → 現 `sorry + @residual(wall:heatflow-continuity)` 維持、
  B-1 のみ genuine 先行 ship（部分前進、仮説束化なし）。
