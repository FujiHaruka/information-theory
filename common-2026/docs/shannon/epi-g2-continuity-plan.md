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
