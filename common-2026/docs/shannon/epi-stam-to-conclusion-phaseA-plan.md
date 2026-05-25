# EPI Stam → conclusion Phase A: Stam + de Bruijn 合流 (Csiszár scaling) サブ計画

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A (line 467-547)
> **Created**: 2026-05-25 (Phase D 合流 commit `c0edbe1` 直後、planner 起草)
> **Status**: 設計起草 (Phase A 着手前の Mathlib-shape-driven mini-plan)

## Position

- 親 sub-plan: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) Phase A
  (Stam + de Bruijn 合流 → `IsStamToEPIBridgeHyp` genuine 化)
- 上流入力 (両方とも Phase D 完了済、sister 出力):
  - [`epi-stam-discharge-plan.md`](epi-stam-discharge-plan.md) Phase D — `IsStamInequalityHyp`
    の genuine discharge (Cover-Thomas Lemma 17.7.2 内部)
  - [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) Phase D
    (= [`epi-debruijn-integration-phaseD-plan.md`](epi-debruijn-integration-phaseD-plan.md)、
    今日 commit `c0edbe1`) — `csiszarGap` 定義 + endpoint lemma + `rfl` shape contract
- 下流: 本 Phase 完了で主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:232`)
  が hypothesis-free `theorem` に格上げ、続いて親 plan §Phase B / §Phase V へ進行

## Motivation

Phase 0 (commit `0d54e89`/`78cf2ec`/`2809168`) で `IsStamToEPIScalingHyp`
(`EPIStamToBridge.lean:202-216`) の signature を `∃ Z_X Z_Y, ... ∧ AntitoneOn gap (Set.Icc 0 1)`
に refactor 済。Phase D (commit `c0edbe1`) で sister の `csiszarGap`
(`EPIL3Integration.lean:1160-1164`) が新規 `IsStamToEPIScalingHyp` body の `AntitoneOn` 引数
lambda body と **verbatim 同形** で publish され、`csiszarGap_shape_for_sister`
(`EPIL3Integration.lean:1279-1287`) `rfl` lemma で接続を保証。

本 Phase A はこの 2 つの handoff を消費して **`AntitoneOn (fun s => csiszarGap X Y Z_X Z_Y P s)
(Set.Icc 0 1)` を Stam + de Bruijn から genuine 構築する**:

1. **path-derivative `d/ds (csiszarGap _) ≤ 0`** を de Bruijn V2 + Stam で導出
2. **`antitoneOn_of_deriv_nonpos`** (Mathlib) で `AntitoneOn` 結論を構成
3. これを `IsStamToEPIScalingHyp` の existential witness `Z_X, Z_Y` 構築 (standard normal,
   joint independent) と合わせて genuine constructor
   `isStamToEPIScalingHyp_of_stam_debruijn` として publish
4. 既存 `isStamToEPIBridgeHyp_of_scaling_limit` (`EPIStamToBridge.lean:266-313`、`@audit:ok`)
   経由で `IsStamToEPIBridgeHyp` genuine 化、`IsEPIL3IntegratedPipeline.bridge` field を
   hypothesis-free に
5. 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:232-240`) の `h_bridge`
   引数を削除 (`h_bridge := isStamToEPIBridgeHyp_of_stam_debruijn ...`)、genuine `theorem` 格上げ

**前提条件 verbatim 照合** (CLAUDE.md「具体的数値・型予測の verbatim 確認」遵守、Phase D 由来の
drift 防止):

| 確認対象 | 実コード | verbatim 値 |
|---|---|---|
| `entropyPower (Measure.dirac 0)` | `DifferentialEntropy.lean:147` + `entropyPower` def `EntropyPowerInequality.lean:80` | `= Real.exp (2 · 0) = 1` (∴ Y := 0 退化境界は constant `-1` gap 発生、trivially `AntitoneOn` で degenerate-definition exploitation 直撃) |
| `heatFlowPath2 X Z 0` | `HeatFlowPath.lean:49-52` | `= X` (funext, `Real.sqrt_one`, `Real.sqrt_zero`) |
| `heatFlowPath2 X Z 1` | `HeatFlowPath.lean:54-58` | `= Z` (funext, `Real.sqrt_one`, `Real.sqrt_zero`) |
| `IsStamToEPIScalingHyp` signature 結論 | `EPIStamToBridge.lean:210-216` | `AntitoneOn (fun s => entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s)) - entropyPower (P.map (heatFlowPath2 X Z_X s)) - entropyPower (P.map (heatFlowPath2 Y Z_Y s))) (Set.Icc 0 1)` |
| `csiszarGap` body | `EPIL3Integration.lean:1160-1164` | 上の lambda body と verbatim 同形 (`rfl` で接続) |
| `csiszarGap_shape_for_sister` 結論 | `EPIL3Integration.lean:1279-1287` | `(fun s => csiszarGap X Y Z_X Z_Y P s) = (fun s => entropyPower (...) - ... - ...) := rfl` |
| `entropy_power_inequality_gaussian_saturation` 結論 | `EntropyPowerInequality.lean:270-301` | `entropyPower (P.map (X+Y)) = entropyPower (P.map X) + entropyPower (P.map Y)` (Gaussian saturation 端点 `s = 1` で gap = 0) |
| `IsStamInequalityHyp` signature | `EPIStamDischarge.lean:97-104` | `∀ J_X J_Y J_sum fX fY fXY, 0 < J_X → 0 < J_Y → 0 < J_sum → J_X = (fisherInfoOfMeasureV2 (P.map X) fX).toReal → J_Y = ... → J_sum = ... → 1/J_sum ≥ 1/J_X + 1/J_Y` |
| `IsDeBruijnIntegrationHyp` signature | `EPIStamDischarge.lean:258-268` | `∃ fPath, ∀ h_X h_target, ... → h_target - h_X = ∫ t in Ioo 0 T, (1/2) * (fisherInfoOfMeasureV2 (P.map (fun ω => X ω + √t · Z ω)) (fPath t)).toReal ∂volume` |
| `IsStamToEPIBridgeHyp` 場所 | `EPIStamDischarge.lean:337-339` (親 plan の `:304` は drift、修正) | `IsStamInequalityHyp X Y P → IsEntropyPowerInequalityHypothesis X Y P` |
| `entropy_power_inequality` 場所 | `EntropyPowerInequality.lean:232-240` (親 plan の `:188` は古いスナップ、修正) | hypothesis: `h_stam : IsStamInequalityResidual X Y P`, `h_bridge : IsStamToEPIBridge X Y P` (defeq に上の `Hyp` 群) |

`IsStamInequalityResidual` / `IsStamToEPIBridge` (`EntropyPowerInequality.lean:187-193` /
`:203-205`) は `IsStamInequalityHyp` / `IsStamToEPIBridgeHyp` と **defeq** (`fisherInfoOfMeasureV2 _ f` =
`fisherInfoOfDensityReal f` by `fisherInfoOfMeasureV2_def`、Phase D 完了済 audit 確認)、よって
`isStamToEPIBridgeHyp_*` を `isStamToEPIBridge_*` に変換する rfl bridge は不要。

## Scope

担当範囲:

| 対象 | 役割 | 行数見積もり |
|---|---|---|
| `Common2026/Shannon/EPIStamToBridge.lean` 拡張 | `isStamToEPIScalingHyp_of_stam_debruijn` constructor 新規追加 (A-1〜A-4 の本体) | +120-220 |
| `Common2026/Shannon/EPIStamToBridge.lean` 既存 `isStamToEPIBridgeHyp_of_scaling_limit` (`:266-313`) | 変更なし (Phase 0 で `@audit:ok` 済、既に Phase A 出力消費可能形) | 0 |
| `Common2026/Shannon/EntropyPowerInequality.lean:232-240` | 主定理 `entropy_power_inequality` の `h_stam` / `h_bridge` 引数削除 (A-6) | -8 / +30 (新 hypothesis-free body) |
| `Common2026/Shannon/EPIL3Integration.lean` 14 件 `@audit:suspect(epi-debruijn-integration-plan)` 降格 (post-merge cleanup) | line 120 / 134 / 210 / 224 / 239 / 253 / 268 / 283 / 316 / 365 / 378 / 401 / 458 / 485 を `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` に書換 | +0 (sed only) |
| `Common2026/Shannon/EPIStamDischarge.lean:337` `IsStamToEPIBridgeHyp` 自身 | docstring 改訂 (`Discharge via ...-plan.md (未着手)` → `Discharged 2026-05-?? by isStamToEPIScalingHyp_of_stam_debruijn`)、def 本体・signature 変更なし | +0 / docstring ~5 |

**合計**: `Common2026` の 3 file に分散追記、~150-250 行 (中央予測 ~200 行)。

新規 file 不要 (`HeatFlowPath.lean` は Phase 0 で publish 済 167 行、`heatFlowPath2_law` /
`heatFlowPath2_law_of_gaussian` 既存)。

## ゴール / Approach

### 全体戦略

```
[Phase D 出力 (前提)]              [Sister sub-plan 出力 (前提)]      [Mathlib 既存]
  csiszarGap (def)                   IsStamInequalityHyp (Phase D 完)    antitoneOn_of_deriv_nonpos
  csiszarGap_at_zero                 IsDeBruijnIntegrationHyp (Phase D)  HasDerivAt.sub
  csiszarGap_at_one_eq_zero          (両方 staged-honest、Phase A は     intervalIntegral.integral_deriv
   _of_gaussian_pair                  signature consume のみ)            entropy_power_inequality_
  csiszarGap_shape_for_sister                                              gaussian_saturation
   (rfl)                                                                  (EntropyPowerInequality.lean:270)
       │                                       │                                  │
       └───────────────────┬───────────────────┴──────────────────────────────────┘
                           ▼
   A-0  sister Phase D 出力存在確認 (Read で signature verbatim 照合)
   A-1  Csiszár gap 関数 alias + Z_X, Z_Y witness 構築 (standard normal, joint indep)
   A-2  d/ds (csiszarGap _) の計算 = de Bruijn V2 + chain rule (各 mapped 測度に対し
        IsDeBruijnIntegrationHyp 適用) → derivative 式
   A-3  Stam 不等式から derivative ≤ 0 を導出 (1/J(X_s+Y_s) ≥ 1/J(X_s) + 1/J(Y_s) →
        gap'(s) ≤ 0)
   A-4  `antitoneOn_of_deriv_nonpos` で AntitoneOn 結論 → existential ⟨Z_X, Z_Y, ...⟩
        + AntitoneOn を bundle して IsStamToEPIScalingHyp X Y P 完成
   A-5  既存 isStamToEPIBridgeHyp_of_scaling_limit + IsStamToEPILimitHyp の trivial 構築
        で IsStamToEPIBridgeHyp X Y P (genuine constructor)
   A-6  主定理 entropy_power_inequality の h_bridge 引数を A-5 で discharge、
        hypothesis-free 化
```

### Mathlib-shape-driven 設計選択 (再確認)

Phase 0 closure 時 (commit `78cf2ec`) に確定済の選択を踏襲:

- **`AntitoneOn`** (not `MonotoneOn`): Csiszár scaling では gap が時間進行で 0 へ decreasing、
  `gap_0 ≥ gap_1 = 0` で EPI 結論。`MonotoneOn` 採用は sign error (Phase 0 inventory §B'/§G(b)
  の推奨は post-mortem で sign correction 済、`epi-stam-to-conclusion-heatflow-inventory.md:8`
  を参照)。
- **`Set.Icc (0 : ℝ) 1`** (interior `Ioo 0 1`): `antitoneOn_of_deriv_nonpos` の `Convex D` 前提
  を `convex_Icc 0 1` で自動 discharge、interior 上の `HasDerivAt` 要件は `Ioo 0 1` の各点で
  満たせばよい (端点 s = 0, s = 1 は `ContinuousOn` で吸収)。
- **derivative の expression** は `g'(s) = Real.exp (2 h(X_s + Y_s)) · J(X_s + Y_s)
  − Real.exp (2 h(X_s)) · J(X_s) − Real.exp (2 h(Y_s)) · J(Y_s)` の形 (de Bruijn V2
  `derivAt_entropy_eq_half_fisher_v2` 由来の `(1/2) · J` 因子 × `entropyPower` の chain rule)。
  この形を **A-2 の `HasDerivAt` lemma の結論として固定** し、A-3 の Stam 不等式の整形に合わせる。

### 段階的 ship 設計

本 Phase A は **atomic** (中間 partial ship 不可)。`isStamToEPIScalingHyp_of_stam_debruijn`
constructor が genuine な `AntitoneOn` proof を完成させない限り、主定理の hypothesis-free 化
(A-6) はできず、partial publish 価値が出ない。撤退ライン発動時のみ partial 化 (L-Concl-A-α/β、
sister 由来の honest hypothesis を保持した形で hypothesis-restricted theorem を publish)。

### 規模見積もり

| Sub-step | 内容 | 行数 | 依存 | Mathlib 在庫 |
|---|---|---|---|---|
| A-0 | sister Phase D 出力存在確認 (Read のみ、コード変更なし) | 0 | sister 両方 Phase D | — |
| A-1 | Csiszár gap alias + `Z_X`, `Z_Y` witness 構築 (standard normal, joint indep, jointly indep of X, Y) | ~30-50 | A-0 | 在庫済 (`gaussianReal 0 1` 既出、joint indep witness 構築は Phase 0 で `instStandardNormalIndepWitness` 等あれば再利用) — **mathlib-inventory 必要 (witness 構築 API)** |
| A-2 | `d/ds (csiszarGap X Y Z_X Z_Y P s) = ...` の `HasDerivAt` 補題 (de Bruijn V2 適用 × 3 mapped 測度) | ~50-80 | A-1, `IsDeBruijnIntegrationHyp`, `heatFlowPath2_law` (`HeatFlowPath.lean:63-100`) | 在庫済 (`HasDerivAt.sub`, `Real.hasDerivAt_exp`, V2 `derivAt_entropy_eq_half_fisher_v2` `EPIStamDischarge.lean:204`)、ただし `entropyPower` の chain-rule lemma **`hasDerivAt_entropyPower_of_derivAt_diffEnt`** は新規 — **mathlib-inventory 必要** |
| A-3 | `g'(s) ≤ 0` を Stam の `1/J(X_s+Y_s) ≥ 1/J(X_s) + 1/J(Y_s)` から導出 (代数変形 + nonneg) | ~30-50 | A-2, `IsStamInequalityHyp` | 在庫済 (linarith / Real.exp_pos / Real.exp_log) |
| A-4 | `antitoneOn_of_deriv_nonpos` 適用 + existential witness bundle → `IsStamToEPIScalingHyp` 完成 | ~20-30 | A-3 | 在庫済 (`antitoneOn_of_deriv_nonpos` `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean`、`convex_Icc`) — **mathlib-inventory verify (`antitoneOn_of_deriv_nonpos` の正確な signature)** |
| A-5 | `IsStamToEPIBridgeHyp` constructor (既存 `isStamToEPIBridgeHyp_of_scaling_limit` + `isStamToEPILimitHyp_of_gaussian` を A-4 出力に適用、Gaussian saturation 端点で `IsStamToEPILimitHyp` を trivially 構築) | ~10-20 | A-4 | 在庫済 (両方 `EPIStamToBridge.lean` 内、Phase 0 で `@audit:ok`) |
| A-6 | 主定理 `entropy_power_inequality` の hypothesis-free 化 (h_stam / h_bridge を default `True` discharge 又は `_inferred` 引数化) | ~10-20 | A-5 | — |

**合計**: 自作 ~150-250 行、中央予測 ~200 行 (親 plan §Phase A 当初見積 ~80-150 から +33%、
de Bruijn V2 chain rule lemma の新規追加分が増加要因)。

## 進捗

- [ ] A-0 — sister Phase D 出力存在確認 (Read 照合) 📋
- [ ] A-1 — Csiszár gap alias + (Z_X, Z_Y) standard normal witness 構築 📋
- [ ] A-2 — `HasDerivAt (fun s => csiszarGap _ _ _ _ _ s) (g'(s)) s` 補題 📋
- [ ] A-3 — `g'(s) ≤ 0 from IsStamInequalityHyp` 📋
- [ ] A-4 — `AntitoneOn (fun s => csiszarGap _ _ _ _ _ s) (Set.Icc 0 1)` → `IsStamToEPIScalingHyp X Y P` 完成 📋
- [ ] A-5 — `isStamToEPIBridgeHyp_of_stam_debruijn` 構築 (`_of_scaling_limit` 経由) 📋
- [ ] A-6 — 主定理 `entropy_power_inequality` hypothesis-free 化 + `EPIStamDischarge.lean:337` docstring 改訂 📋
- [ ] A-V — verify (4 file `lake env lean`) + post-merge cleanup (`EPIL3Integration.lean` 14 件 tag 書換) 📋

proof-log: yes (`docs/shannon/proof-log-epi-stam-to-conclusion-phaseA.md` を A-V 完了時に書出)

## Phase 詳細

### A-0 — sister Phase D 出力存在確認 (M0 在庫照合, code 変更なし)

- **目的**: A-1 着手前に sister 両方 (`epi-stam-discharge-plan` Phase D + `epi-debruijn-integration-plan`
  Phase D = `epi-debruijn-integration-phaseD-plan.md`) の publish 状態を verbatim 確認。
- **手順**:
  - [ ] **A-0-1**: `csiszarGap` (`EPIL3Integration.lean:1160-1164`)、`csiszarGap_at_zero`
    (`:1173-1184`)、`csiszarGap_at_one_eq_zero_of_gaussian_pair` (`:1194-1215`)、
    `csiszarGap_shape_for_sister` (`:1279-1287`) を Read で verbatim 照合
    (signature + 結論 form + 既存 `@audit:suspect(epi-debruijn-integration-phaseD-plan)` 確認)。
  - [ ] **A-0-2**: `IsStamInequalityHyp` (`EPIStamDischarge.lean:97-104`)、
    `IsDeBruijnIntegrationHyp` (`:258-268`)、`IsDeBruijnRegularityHyp` (`:193-228`、特に
    `density_t_eq` field) を Read で verbatim 照合。Phase D で genuine (existential
    `∃ fPath` / `density_path` shared witness) 化済を確認。
  - [ ] **A-0-3**: `IsStamToEPIScalingHyp` (`EPIStamToBridge.lean:202-216`、Phase 0 refactor 後)
    + `isStamToEPIBridgeHyp_of_scaling_limit` (`:266-313`、`@audit:ok`) を Read 照合。
    `AntitoneOn` 引数の lambda body が `csiszarGap_shape_for_sister` の RHS と verbatim
    同形か確認 (これは Phase D 起草時に保証されているはずだが、再確認)。
- **撤退条件 (A-0)**: sister 出力に signature drift (verbatim 不一致) を発見した場合、
  即座にユーザに drift 報告、本 Phase の進行を停止し sister sub-plan 側で修正後再開。
  defect の上に黙って積み上げない (CLAUDE.md `検証の誠実性`)。
- **規模**: 0 行 (Read のみ)

### A-1 — Csiszár gap alias + (Z_X, Z_Y) standard normal witness 構築

- **目的**: `IsStamToEPIScalingHyp` の existential witness `∃ Z_X Z_Y : Ω → ℝ, ...`
  に供給する standard normal pair を構築 + measurability / independence / law 条件を全 carry。
- **設計**: `(Ω, P)` 上に standard normal を 2 つ joint independent に取れるかは
  **richness 仮定** (probability space が atomless / Borel uniform を carry 等) に依存。
  Phase 0 で `isStamToEPIScalingHyp_of_gaussian` が同問題で retract (`EPIStamToBridge.lean:317-327`
  retraction comment、「richness assumption が必要、Phase 0 scope 外」) された前例あり。
  本 A-1 では **richness 仮定を `IsStamInequalityHyp` の load-bearing 内に押し込む** 設計
  (Stam 仮定が真に成り立つ probability space は density / 滑らかさを carry し、Gaussian
  noise の追加は標準構成で可能、と仮定する)。これは genuine Csiszár scaling argument
  の standard assumption (Cover-Thomas Ch.17 で暗黙仮定) — honest に新規 staged predicate
  `IsStamScalingNoiseHyp X Y P` (= "standard normal pair `(Z_X, Z_Y)` exists on Ω, joint
  independent from `(X, Y)` and from each other") として A-1 で追加。
- **手順**:
  - [ ] **A-1-1**: `IsStamScalingNoiseHyp X Y P : Prop` を新規 def
    (`EPIStamToBridge.lean` 内、§3 直前あたり)。body:
    ```lean
    def IsStamScalingNoiseHyp {Ω : Type*} [MeasurableSpace Ω]
        (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
      ∃ (Z_X Z_Y : Ω → ℝ),
        Measurable Z_X ∧ Measurable Z_Y ∧
        P.map Z_X = gaussianReal 0 1 ∧ P.map Z_Y = gaussianReal 0 1 ∧
        IndepFun X Z_X P ∧ IndepFun Y Z_Y P ∧ IndepFun Z_X Z_Y P
    ```
    docstring に `@audit:staged(epi-stam-to-conclusion-plan)` を付与し、
    「richness assumption (Cover-Thomas Ch.17 暗黙仮定)、Mathlib 壁 (b) 解析 —
    standard noise extension on arbitrary probability space は未整備、Mathlib 上流貢献 task として
    別 plan に外出し」と明記。NOT a discharge / load-bearing。
  - [ ] **A-1-2**: `isStamScalingNoiseHyp_of_atomless` (任意 stretch、in scope なら追加):
    `[AtomlessProbability P]` 等の richness instance から `IsStamScalingNoiseHyp` を構築。
    Mathlib に `AtomlessProbability` が無い場合は skip、staged 仮定のままで A-1-3 へ。
  - [ ] **A-1-3**: `csiszarGap` を alias する local notation 又は abbrev は不要 (Phase D
    publish 済の `csiszarGap` を直接使用)。`heatFlowPath2_law_of_gaussian`
    (`HeatFlowPath.lean:104-165`) が `s = 1` 端点で `Z_X, Z_Y` 両方 `gaussianReal 0 1`
    を返すことを確認 (既存補題、コード追加不要)。
- **撤退条件 (A-1-α)**: `IsStamScalingNoiseHyp` を Mathlib 整備不足で genuine 構築できず
  (Mathlib に standard noise extension API が皆無)、staged predicate のまま A-2 以降に
  伝播する → 撤退ライン **L-Concl-A-γ** (新規追加、後述)。`Prop := True` 禁止、honest
  staged で `@audit:staged(epi-stam-to-conclusion-plan)` 留めとして Phase B / V も staged
  化、partial publish (richness 仮定下の hypothesis-free EPI)。
- **規模**: ~30-50 行 (def 1 + docstring 詳細 + 任意 stretch `_of_atomless` constructor)

### A-2 — `HasDerivAt (fun s => csiszarGap _ _ _ _ _ s) (g'(s)) s` 補題

- **目的**: Csiszár gap 関数の path-derivative を de Bruijn V2 identity + Stam 残基から
  解析的に書き出す。`s ∈ Set.Ioo 0 1` (interior、`s = 0` / `s = 1` 端点は別途)。
- **設計** (Mathlib-shape-driven、`antitoneOn_of_deriv_nonpos` の入力形に整形):
  - `csiszarGap X Y Z_X Z_Y P s = entropyPower (P.map (heatFlowPath2 X Z_X s + heatFlowPath2 Y Z_Y s))
    − entropyPower (P.map (heatFlowPath2 X Z_X s)) − entropyPower (P.map (heatFlowPath2 Y Z_Y s))`
    (Phase D D-1-1 body)
  - 各項 `entropyPower (P.map (heatFlowPath2 _ _ s)) = Real.exp (2 · differentialEntropy
    (P.map (heatFlowPath2 _ _ s)))` (entropyPower 定義 `EntropyPowerInequality.lean:80`)
  - de Bruijn V2 chain (Phase D output `IsDeBruijnRegularityHyp.reg_at`、特に
    `derivAt_entropy_eq_half_fisher_v2`):
    `d/ds differentialEntropy (P.map (heatFlowPath2 X Z_X s)) = (1/2) · J(X_s)` (where
    `X_s := heatFlowPath2 X Z_X s`、`J(X_s) := (fisherInfoOfMeasureV2 (P.map X_s) (fPath_X s)).toReal`)
  - chain rule: `d/ds Real.exp (2 · h(X_s)) = Real.exp (2 · h(X_s)) · 2 · (1/2) · J(X_s)
    = Real.exp (2 · h(X_s)) · J(X_s) = entropyPower (P.map X_s) · J(X_s)`
  - 同様に Y_s, X_s + Y_s に適用
  - **結論**: `(d/ds csiszarGap _ s) = entropyPower (P.map (X_s + Y_s)) · J(X_s + Y_s)
    − entropyPower (P.map X_s) · J(X_s) − entropyPower (P.map Y_s) · J(Y_s)`
- **重要 caveat**: `heatFlowPath2 X Z_X s = √(1-s) · X + √s · Z_X` であり、Phase D で使用された
  1-source `gaussianConvolution X Z t = X + √t · Z` とは形が違う (`X` への scaling factor の有無)。
  de Bruijn V2 `derivAt_entropy_eq_half_fisher_v2` は 1-source 形 `X + √t · Z` の `t` 微分
  として書かれているので、2-source `heatFlowPath2` への適用には:
  - 法則レベルで `P.map (heatFlowPath2 X Z_X s) = P.map (√(1-s)·X) ∗ gaussianReal 0 ⟨s, _⟩`
    (`HeatFlowPath.lean:63-100` `heatFlowPath2_law` 既存)
  - これを `P.map (Y_eff + √s · Z_X)` where `Y_eff := √(1-s)·X` の形に reshape (reparametrize)
  - de Bruijn V2 を `Y_eff` に適用、`s` 微分の chain rule 補正は `Y_eff` も `s` 依存なので
    **両時間微分の和** が出る (`∂h/∂s_直接 + ∂h/∂s_scaling`)
  - scaling part `d/ds h(√(1-s)·X) = − (1/(2(1-s)))` (scale-invariance `h(c·X) = h(X) + log|c|`、
    `c = √(1-s)` → `(1/2) log(1-s)` → `d/ds = − 1/(2(1-s))`)
- **手順**:
  - [ ] **A-2-1**: scale-invariance 補題 `differentialEntropy_const_mul`
    (Mathlib / Common2026 既存確認 — **mathlib-inventory 必要**): `differentialEntropy
    (P.map (fun ω => c · X ω)) = differentialEntropy (P.map X) + Real.log |c|`。
    存在しない場合は新規補題として書下し (~20-30 行)。
  - [ ] **A-2-2**: `heatFlowPath2_entropy_deriv` 新規補題: `HasDerivAt (fun s =>
    differentialEntropy (P.map (heatFlowPath2 X Z_X s))) (− 1/(2(1-s)) + (1/2) · J(X_s)) s`
    (interior `0 < s < 1`) — de Bruijn V2 適用 + scale-invariance 補正の和。~30-40 行。
  - [ ] **A-2-3**: `csiszarGap_hasDerivAt` 新規補題: 3 つの `heatFlowPath2_entropy_deriv`
    を組合せ + `Real.hasDerivAt_exp` chain rule で `csiszarGap` 微分式を書き出す。
    ~30-50 行。
  - [ ] **A-2-4**: scale-invariance 項のキャンセル: `(d/ds csiszarGap _ s)` を計算すると
    scale-invariance 補正項 `−1/(2(1-s))` が 3 項分発生するが、entropyPower の chain rule
    で `entropyPower (P.map X_s)` の係数として乗じ、`entropyPower(X_s+Y_s) − entropyPower(X_s)
    − entropyPower(Y_s)` の各 entropyPower 項に分配される。これらが Stam 不等式 (A-3) と
    どう整合するかは A-3-1 で再検証 (**ここで scaling 補正項が gap formula を complicate
    する場合、撤退ライン L-Concl-A-δ 発動、新規追加** — 後述)。
- **撤退条件 (A-2-α)**: `differentialEntropy_const_mul` が Mathlib にも Common2026 にも
  存在せず、新規補題が large (>50 行) になる場合、撤退ライン **L-Concl-A-ε** (新規追加、
  後述)。Common2026 内別 file への外出し (`DifferentialEntropy.lean` 拡張) で対処、
  本 Phase A の scope を保つ。
- **撤退条件 (A-2-β)**: de Bruijn V2 chain rule (`heatFlowPath2_entropy_deriv`) で
  scaling part 補正項と V2 Fisher info part が plane separation できず、結果として
  得られる `csiszarGap` 微分式が Stam 不等式 (A-3 の形 `1/J(X_s+Y_s) ≥ 1/J(X_s) + 1/J(Y_s)`)
  と直接 reduce しない場合、撤退ライン **L-Concl-A-δ** (新規追加、後述)。Cover-Thomas
  Lemma 17.7.3 では 1-source 形 `Z_t := X + √t · G` を用い、本 plan の 2-source 形
  `heatFlowPath2` とは re-parametrize が必要 — 数式上の reduction を A-2-4 で詳細確認。
  最悪 case では 2-source path を 1-source path に reparametrize する `csiszarGap` 再定義
  (sister Phase D の cooperation 必要、本 Phase 内では不可) で対処。
- **規模**: ~50-80 行

### A-3 — `g'(s) ≤ 0 from IsStamInequalityHyp`

- **目的**: A-2 出力の `g'(s)` 式を Stam 不等式 `1/J(X_s+Y_s) ≥ 1/J(X_s) + 1/J(Y_s)` から
  `≤ 0` に reduce する。
- **設計**:
  - A-2-3 で `g'(s) = entropyPower (X_s+Y_s) · J(X_s+Y_s) − entropyPower (X_s) · J(X_s)
    − entropyPower (Y_s) · J(Y_s) + scaling 補正項` の形 (scaling 補正項は A-2-4 で
    キャンセル前提)
  - Cover-Thomas Lemma 17.7.3 の重要構造 (`g'(s) ≤ 0`):
    - Stam: `1/J(X_s+Y_s) ≥ 1/J(X_s) + 1/J(Y_s)` ⇒ `J(X_s+Y_s) ≤ J(X_s) · J(Y_s) / (J(X_s) + J(Y_s))`
      (調和平均 ≤ each)
    - これに `entropyPower (X_s+Y_s) ≤ entropyPower (X_s) + entropyPower (Y_s)` (EPI 結論)
      を組合せ — **circular!** Csiszár scaling は EPI を証明している最中なのでこの方向は使えない
    - 正しい argument: weight `Real.exp (2 h(X_s)) · J(X_s)` の凸性。Cover-Thomas eq.(17.42)-(17.43)
      参照。具体的には Cauchy-Schwarz 又は AM-HM で
      `(entropyPower(X_s) + entropyPower(Y_s)) · (1/J(X_s) + 1/J(Y_s)) ≥ (√(entropyPower(X_s)) +
      √(entropyPower(Y_s)))^2 · (something)` の bracket、これと Stam を合わせて整理
  - **手順**:
  - [ ] **A-3-1**: Stam の harmonic-mean 不等式から algebraic transform: `Real.one_div_le_one_div` /
    `Real.inv_add_inv` 経由で `J(X_s+Y_s) ≤ J(X_s) · J(Y_s) / (J(X_s) + J(Y_s))` を導出
    (`1 / J_sum ≥ 1/J_X + 1/J_Y` ⇔ `1 / J_sum ≥ (J_X + J_Y) / (J_X · J_Y)`)。~20-30 行
  - [ ] **A-3-2**: Cover-Thomas eq.(17.43) の weight 等式 `entropyPower(X_s+Y_s) · J(X_s+Y_s)
    ≤ entropyPower(X_s) · J(X_s) + entropyPower(Y_s) · J(Y_s) + scaling 補正項` を導出
    (**ここが Phase A 本質的部分、~50-80 行の解析証明、`Real.exp` の凸性 / Cauchy-Schwarz
    / Jensen を組合せ — mathlib-inventory 必要**)。Cover-Thomas Ch.17 eq.(17.42)-(17.43)
    の Lean 化、Mathlib に直接の "EPI inner inequality" 補題は無い可能性が高い (rg 確認必要)
  - [ ] **A-3-3**: A-2-4 の scaling 補正項キャンセル + A-3-2 の Cauchy-Schwarz weight 不等式
    から `g'(s) ≤ 0` を `linarith` / `nlinarith` で結論。~10-20 行
- **撤退条件 (A-3-α)**: A-3-2 の Cauchy-Schwarz weight 不等式が Mathlib (`Real.inner_mul_le_norm`
  / `Real.add_sq_le_sq_mul_sq` / etc.) に直接形がなく、自前 plumbing が large (>100 行) に
  なる場合、撤退ライン **L-Concl-A-α** (sister 撤退ライン伝播の拡張) を適用。Cauchy-Schwarz
  weight 不等式自体を新規 staged predicate `IsCsiszarScalingWeightHyp X Y P : Prop`
  (Cover-Thomas eq.(17.43) statement) として外出し、本 Phase A は staged 留め、Phase B / V も
  staged 化。Mathlib 上流貢献 task として別 plan に切出。
- **規模**: ~30-50 行 (撤退 case では +100 行)

### A-4 — `AntitoneOn (fun s => csiszarGap _ _ _ _ _ s) (Set.Icc 0 1)` → `IsStamToEPIScalingHyp X Y P` 完成

- **目的**: A-2 + A-3 を `antitoneOn_of_deriv_nonpos` (Mathlib) に渡して `AntitoneOn` 結論を
  構成、これを existential witness `(Z_X, Z_Y)` と bundle して `IsStamToEPIScalingHyp` 完成。
- **設計** (Mathlib-shape-driven、Phase 0 inventory §B' verbatim 確認):
  - Mathlib `antitoneOn_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) : AntitoneOn f D` —
    **mathlib-inventory verify (`antitoneOn_of_deriv_nonpos` の正確な signature
    + file:line)** (`Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` 内のはず、Phase 0
    inventory には `monotoneOn_of_deriv_nonneg` のみ verbatim、`antitoneOn_*` 版を要確認)
  - `D := Set.Icc (0:ℝ) 1` で `Convex ℝ D` は `convex_Icc 0 1`
  - `ContinuousOn f D`: A-2 の `HasDerivAt` は interior `Ioo 0 1` のみ、端点 `s = 0` /
    `s = 1` での continuity は別途。`HasDerivAt _ _ s → ContinuousAt _ s` (`HasDerivAt.continuousAt`)
    から interior continuity、端点は `csiszarGap_at_zero` (`EPIL3Integration.lean:1173`) +
    `csiszarGap_at_one_eq_zero_of_gaussian_pair` (`:1194`) の closed form と
    `continuousOn_of_isLittleO` 等で対処 (~10-20 行)
  - `DifferentiableOn`: A-2 の `HasDerivAt` から直接 `DifferentiableOn`
  - `hf'_nonpos`: A-3 の結論
- **手順**:
  - [ ] **A-4-1**: `csiszarGap_continuousOn` 補題 (Set.Icc 0 1 上の continuity)、~10-20 行
  - [ ] **A-4-2**: `csiszarGap_differentiableOn_interior` 補題、A-2-3 の HasDerivAt から
    直接、~5-10 行
  - [ ] **A-4-3**: `antitoneOn_of_deriv_nonpos` 適用、~10 行
  - [ ] **A-4-4**: existential witness `(Z_X, Z_Y)` を A-1 の `IsStamScalingNoiseHyp` から
    `obtain ⟨Z_X, Z_Y, ...⟩` で抽出、`AntitoneOn` と bundle して
    `IsStamToEPIScalingHyp X Y P` 完成。`isStamToEPIScalingHyp_of_stam_debruijn` constructor
    として publish。~10-20 行
- **撤退条件 (A-4-α)**: `antitoneOn_of_deriv_nonpos` が Mathlib に存在せず (`monotoneOn_of_deriv_nonneg`
  しかない場合)、`antitone_iff_monotone_neg` 経由で `MonotoneOn (fun s => − csiszarGap _ s)`
  に reduce する変換 plumbing が必要 (~20-30 行)。撤退ラインではなく detour、scope 内で対処。
- **規模**: ~20-30 行 (撤退 detour case では +30 行)

### A-5 — `isStamToEPIBridgeHyp_of_stam_debruijn` constructor (`_of_scaling_limit` 経由)

- **目的**: A-4 で得た `IsStamToEPIScalingHyp X Y P` + 既存 `IsStamToEPILimitHyp_of_gaussian`
  (`EPIStamToBridge.lean:331-342`) で `IsStamToEPILimitHyp X Y P` (trivial に
  `⟨0, rfl, Or.inr ?_⟩` で構築) → 既存 `isStamToEPIBridgeHyp_of_scaling_limit`
  (`:266-313`、`@audit:ok`) を経由して `IsStamToEPIBridgeHyp X Y P` 完成。
- **手順**:
  - [ ] **A-5-1**: `isStamToEPILimitHyp_trivial` 補題 (Gaussian 仮定なし、A-1 の
    `Z_X, Z_Y` standard normal witness を用いて `(Z_X + Z_Y) ∼ 𝒩(0, 2)` から
    `entropyPower (Z_X + Z_Y) = 4πe`、`entropyPower Z_X = entropyPower Z_Y = 2πe` で
    `gap_1 = 4πe − 2πe − 2πe = 0` を導出 → `Or.inr` ブランチで bridge)。~10-15 行
    (実は既存 `csiszarGap_at_one_eq_zero_of_gaussian_pair` (`EPIL3Integration.lean:1194-1215`)
    と同じ計算、再利用可能)
  - [ ] **A-5-2**: `isStamToEPIBridgeHyp_of_stam_debruijn` constructor:
    ```lean
    theorem isStamToEPIBridgeHyp_of_stam_debruijn {Ω : Type*} {mΩ : MeasurableSpace Ω}
        {P : Measure Ω} [IsProbabilityMeasure P]
        {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
        (h_noise : IsStamScalingNoiseHyp X Y P)  -- A-1 staged honest
        (h_dbreg_X : IsDeBruijnRegularityHyp X _ P)  -- sister Phase D output
        (h_dbreg_Y : IsDeBruijnRegularityHyp Y _ P)
        (h_dbint_X : ∀ T > 0, IsDeBruijnIntegrationHyp X _ P T)
        (h_dbint_Y : ∀ T > 0, IsDeBruijnIntegrationHyp Y _ P T)
        (h_dbint_sum : ∀ T > 0, IsDeBruijnIntegrationHyp (fun ω => X ω + Y ω) _ P T) :
        IsStamToEPIBridgeHyp X Y P := by
      -- A-1〜A-4 経由で IsStamToEPIScalingHyp 構築
      have h_scaling := isStamToEPIScalingHyp_of_stam_debruijn hX hY hXY h_noise
        h_dbreg_X h_dbreg_Y h_dbint_X h_dbint_Y h_dbint_sum
      -- A-5-1 で IsStamToEPILimitHyp 構築 (A-1 の noise witness 経由)
      have h_limit := isStamToEPILimitHyp_trivial h_noise
      -- 既存 _of_scaling_limit で IsStamToEPIBridgeHyp 完成
      exact isStamToEPIBridgeHyp_of_scaling_limit h_scaling h_limit
    ```
    ~10-15 行
- **撤退条件 (A-5-α)**: 5 件の sister Phase D output (regularity X / Y + integration X / Y / sum)
  の signature が `_` placeholder で carry できず (各 `Z` パラメータが本 Phase A の
  `Z_X, Z_Y` と同じ standard normal を要求するか、別の generic `Z` を持つか) の照合で
  signature mismatch が出る場合、`obtain ⟨Z_X, Z_Y, ...⟩ := h_noise` 後に各 hypothesis
  への引数注入を明示する書下しで対処 (+10-20 行)。撤退ラインではなく detour。
- **規模**: ~10-20 行 + 撤退 detour case +20 行

### A-6 — 主定理 `entropy_power_inequality` hypothesis-free 化 + docstring 改訂

- **目的**: 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:232-240`) の
  `h_stam : IsStamInequalityResidual X Y P` / `h_bridge : IsStamToEPIBridge X Y P` 引数を
  A-5 の出力で discharge、hypothesis-free `theorem` に格上げ。
- **設計の重要 caveat**: 主定理の hypothesis は `IsStamInequalityResidual` /
  `IsStamToEPIBridge` (`EntropyPowerInequality.lean:187` / `:203`)、A-5 の出力は
  `IsStamToEPIBridgeHyp` (`EPIStamDischarge.lean:337`)。両者は defeq だが lean 上 unfold が
  必要 (Phase D 完了 audit で `fisherInfoOfMeasureV2_def` 経由で defeq 確認済)。
- **手順**:
  - [ ] **A-6-1**: 主定理の hypothesis 引数 `h_stam` / `h_bridge` を以下のいずれかで discharge:
    - **案 a (推奨)**: 主定理 signature 自体は変更せず、A-5 の出力を caller に注入する
      new wrapper theorem `entropy_power_inequality_unconditional` を別途 publish
      (`entropy_power_inequality` 本体は hypothesis 取り形のまま、Phase 0 で正しく
      docstring 整理済の旧 form を保持)。downstream は `_unconditional` を呼ぶように切替。
      ~30 行 (新 theorem + docstring + downstream caller 1-2 件の rename)
    - **案 b (radical)**: 主定理本体の signature から `h_stam` / `h_bridge` を削除、A-5 の
      出力を本体内で構築。downstream 全 file (`EPIPlumbing.lean` 3 件 + `EPIL3Integration.lean`
      14 件 + `EPIStamDeBruijnConclusion.lean` 6 件 + 同 5 件 = 28 件 = 全 EPI eco) を
      新 signature に書換、large ripple。~150 行
  - **推奨**: 案 a (本 Phase A は genuine theorem 1 件追加に集中、case b は親 plan §Phase B
    のスコープに任せて段階化)
  - [ ] **A-6-2**: `EPIStamDischarge.lean:337` `IsStamToEPIBridgeHyp` docstring 改訂
    (`Discharge via epi-stam-to-conclusion-plan.md (未着手)` → `Discharged 2026-05-?? by
    isStamToEPIBridgeHyp_of_stam_debruijn (EPIStamToBridge.lean:?), Cover-Thomas Lemma
    17.7.3 Csiszár scaling argument`)、`@audit:suspect(epi-stam-to-conclusion-plan)` →
    `@audit:ok` (案 a) 又は `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` (案 b)。
    ~5 行
  - [ ] **A-6-3**: 同様に主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:231`)
    の `@audit:suspect(epi-stam-to-conclusion-plan)` を、案 a なら `@audit:ok` (本体不変)、
    案 b なら `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` (signature 変更)。
- **撤退条件 (A-6-α)**: 案 a で `_unconditional` を作る際に主定理本体の hypothesis が
  `IsStamInequalityResidual` / `IsStamToEPIBridge` のいずれかが「予期せぬ richness 仮定」を
  要求する形 (例: caller の `Measurable X` などのregularity 仮定が暗黙に必要) の場合、
  そのregularity 仮定を `_unconditional` の引数に明示する形で publish (撤退ラインなし、
  honest な signature 拡張)。
- **規模**: 案 a なら ~30 行、案 b なら ~150 行 (本 plan は案 a 想定)

### A-V — verify + post-merge cleanup (`EPIL3Integration.lean` 14 件 tag 書換)

- **目的**: A-1〜A-6 完了後、全 file silent + 14 件 `@audit:suspect(epi-debruijn-integration-plan)`
  を `@audit:closed-by-successor(epi-stam-to-conclusion-plan)` に一括書換。
- **手順**:
  - [ ] **A-V-1**: `lake env lean Common2026/Shannon/EPIStamToBridge.lean` silent
  - [ ] **A-V-2**: `lake env lean Common2026/Shannon/EPIStamDischarge.lean` silent
  - [ ] **A-V-3**: `lake env lean Common2026/Shannon/EntropyPowerInequality.lean` silent
  - [ ] **A-V-4**: `lake env lean Common2026/Shannon/EPIL3Integration.lean` silent
  - [ ] **A-V-5**: `EPIL3Integration.lean` 14 件 (`grep -n
    "@audit:suspect(epi-debruijn-integration-plan)" Common2026/Shannon/EPIL3Integration.lean`
    で抽出、line 120 / 134 / 210 / 224 / 239 / 253 / 268 / 283 / 316 / 365 / 378 / 401 /
    458 / 485 — 親 plan §Phase A Done 条件で列挙済) を `@audit:closed-by-successor(epi-stam-to-conclusion-plan)`
    に sed 一括書換。`docs/audit/audit-tags.md` で slug 末尾 `-plan` 有無 + `closed-by-successor`
    KIND 語彙確認 (語彙不存在なら orchestrator に追加依頼)。
  - [ ] **A-V-6**: `lake env lean Common2026/Shannon/EPIL3Integration.lean` 再 silent 確認
    (docstring 変更のみで本体不変、warning 0 期待)
  - [ ] **A-V-7**: 独立 honesty audit (`subagent_type: "honesty-auditor"`) を orchestrator が
    起動 (A-1 で新規 staged predicate `IsStamScalingNoiseHyp` を導入したため、CLAUDE.md
    "Independent honesty audit" 必須条件発火)。fresh subagent に対象 file path +
    predicate 名 + line 番号 + consumer 主定理名 + 関連 commit hash + 本 mini-plan path
    を渡す。Tier 1/2/3 全 PASS で session closure、questionable / DEFECT verdict 時は
    本 Phase A 内で対処 (撤退ライン L-Concl-A-α / γ 経由で staged 留め化)。
  - [ ] **A-V-8**: proof-log 書出 `docs/shannon/proof-log-epi-stam-to-conclusion-phaseA.md`
    (各 sub-step の `lake env lean` 出力 + 撤退ライン発動有無 + Mathlib-shape-driven 整合性
    + post-merge cleanup 14 件の確定 slug)
- **撤退条件 (A-V)**: なし (本 sub-phase は purely verification、撤退は A-1〜A-6 で
  すべて吸収済)
- **規模**: 0-10 行 (sed 14 件 + verify command 4 件 + audit subagent dispatch + proof-log)

## 撤退ライン (honest 限定、新規追加 4 件 + 親 plan 継承 2 件)

| slug | Phase | 内容 | hypothesis 名 (例) | 解除条件 |
|---|---|---|---|---|
| **L-Concl-A-α** (親 plan §line 539-543 継承) | A | sister sub-plan の Phase D 撤退ライン伝播 (smooth density / score Lp / honest regularity / integration hypothesis を caller 経由で受ける) | `IsBlachmanIdentityHyp_smooth` 等 sister 由来 | sister の撤退ライン解除 |
| **L-Concl-A-β** (親 plan §line 544-546 継承) | A-5 | Gaussian limit `g(∞) = 0` が non-Gaussian で破綻、`IsStamToEPILimitHyp` 構築不能 | `IsEPIGaussianLimitHyp X Y P` | Cover-Thomas Csiszár scaling tail bound 形式化 |
| **L-Concl-A-γ** (新規追加、本 plan A-1) | A-1 | `IsStamScalingNoiseHyp` (standard normal pair witness) を Mathlib 整備不足で genuine 構築できず、staged predicate のまま伝播 | `IsStamScalingNoiseHyp X Y P` | Mathlib `noise extension on arbitrary probability space` API 整備、別 plan で外出し |
| **L-Concl-A-δ** (新規追加、本 plan A-2) | A-2 | 2-source `heatFlowPath2` 経由の `g'(s)` 微分式が Stam 不等式と直接 reduce しない (scaling 補正項キャンセル失敗 / 形 mismatch)、sister Phase D との cooperation 必要 | (signature 再設計、本 Phase 内では撤退) | sister Phase D 再開 + `csiszarGap` 1-source 形 reparametrize |
| **L-Concl-A-ε** (新規追加、本 plan A-2) | A-2-1 | `differentialEntropy_const_mul` Mathlib 不在、新規補題 large 化 | `IsDifferentialEntropyScaleHyp` 等 (新規 staged 又は別 file 外出し) | Common2026 `DifferentialEntropy.lean` 拡張で吸収 (scope 内 detour) |
| **L-Concl-A-ζ** (新規追加、本 plan A-3) | A-3-2 | Cover-Thomas eq.(17.43) Cauchy-Schwarz weight 不等式が Mathlib 直接形なく、自前 plumbing >100 行 | `IsCsiszarScalingWeightHyp X Y P` (新規 staged) | Mathlib 上流貢献 / 別 plan で外出し |

**全撤退ライン共通規律** (親 plan §line 644-654 継承):
- **`Prop := True` placeholder 禁止** (A-1 の `IsStamScalingNoiseHyp` は実 Prop、`∃ Z_X Z_Y, ...
  ∧ ...` で 7 つの conjunction を要求 — vacuous 化不可)
- **結論型 ≡ 仮説型 + `body := h` (循環) 禁止** (A-5 の `isStamToEPIBridgeHyp_of_stam_debruijn`
  は genuine constructor、A-4 の `IsStamToEPIScalingHyp` を経由するため bridge type と
  scaling type は別、循環なし)
- **load-bearing hypothesis を完成と称する name laundering 禁止** (本 Phase の出力 theorem
  名は `_unconditional` / `_full` を使わず、`isStamToEPIBridgeHyp_of_stam_debruijn` のように
  「何から構築したか」を honest に明示)
- **退化定義の悪用 (vacuous truth) 禁止** — 特に **degenerate-definition exploitation defect
  class** 直撃の防止: Phase D で `Y := 0`, `Z_Y := 0` 退化境界が constant `−1` gap を生み
  trivially `AntitoneOn` で discharge する経路 (L-DBD-2-α 発火、戦略 γ 降格) を本 Phase A
  でも使わない。A-1〜A-4 の各 sub-step で「Z_X, Z_Y が standard normal で non-degenerate」
  「`Y := 0` 経路を A-3 で誤って活用していない」を A-V audit subagent で verify。
- 撤退ライン発動時は docstring で「NOT a discharge / load-bearing on <sister 由来 hypothesis>」
  を必ず明示

## 完了後の次フェーズへの brief 雛形 (orchestrator 用)

### Brief A: mathlib-inventory subagent (本 Phase A 着手前に dispatch、Phase 0 inventory の補強)

```
# Mathlib API 在庫調査 — EPI-Stam Phase A 着手前

## 担当範囲

`docs/shannon/epi-stam-to-conclusion-phaseA-mathlib-inventory.md` 新規作成。
親 plan: `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` の A-1 / A-2 / A-3 / A-4 で
flag された Mathlib 候補 API を verbatim 確認 + 不在判定。

## 必須在庫項目 (CLAUDE.md `Subagent Inventory of Mathlib Lemmas` 規律遵守)

各項目について **`file:line` location + 完全 signature (`[...]` type-class 前提 verbatim) +
引数型 (順序付き) + 結論 form (verbatim copy、paraphrase 禁止)** を記録する。

1. **A-1 用** — standard normal pair witness 構築:
   - `MeasureTheory.AtomlessProbability` 等 richness instance の有無 (loogle `AtomlessProbability`)
   - 既存 Common2026 `Common2026/Shannon/StandardNoise.lean` 等の有無 (rg)
   - Mathlib `Measure.exists_indep_pair` 等 independent pair existence (loogle)

2. **A-2 用** — `differentialEntropy` scale-invariance:
   - `Common2026.Shannon.differentialEntropy_const_mul` (rg `Common2026/Shannon/DifferentialEntropy.lean`)
   - Mathlib 側 `MeasureTheory.differentialEntropy_smul` 等 (loogle)
   - 不在の場合は自作補題の必要規模見積もり

3. **A-2 用** — chain rule:
   - `Real.hasDerivAt_exp` (Mathlib 既出と思われるが verbatim 確認)
   - `HasDerivAt.exp` / `HasDerivAt.comp` / `HasDerivAt.sub` の signature verbatim
   - de Bruijn V2 `derivAt_entropy_eq_half_fisher_v2` (`Common2026.Shannon.FisherInfoV2.IsRegularDeBruijnHypV2`
     field、`EPIStamDischarge.lean:204` 周辺)

4. **A-3 用** — Cover-Thomas eq.(17.43) Cauchy-Schwarz weight 不等式:
   - Mathlib `Real.inner_mul_le_norm` / `Finset.inner_mul_le_norm_mul_norm` / `Real.add_sq_le_sq_mul_sq` 等
     (loogle で網羅)
   - 不在の場合は L-Concl-A-ζ 発動準備として規模見積もり

5. **A-4 用** — `antitoneOn_of_deriv_nonpos`:
   - `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean` 内 (Phase 0 inventory には
     `monotoneOn_of_deriv_nonneg` のみ verbatim、`antitoneOn_*` 版を要追加確認)
   - `antitoneOn_of_hasDerivWithinAt_nonpos` 版の存在 (任意)

## 撤退条件

- Mathlib に 1-5 のいずれかが完全不在 + Common2026 にも代替なし + 自作補題 >50 行 → 親 plan
  撤退ライン (L-Concl-A-α/γ/ε/ζ) の発動条件として親 plan に報告、本 inventory file に
  「Mathlib 壁 (b) 解析 — 自作 ~?? 行必要」と明記
- 親 plan 撤退ラインの hypothesis 名 (`IsStamScalingNoiseHyp` / `IsCsiszarScalingWeightHyp` 等)
  と Mathlib 候補の対応関係を表で明示

## 出力

`docs/shannon/epi-stam-to-conclusion-phaseA-mathlib-inventory.md` (新規)、+ orchestrator に
200 行以内サマリ (各項目の在庫有無 + 撤退ライン発動候補)
```

### Brief B: lean-implementer subagent (本 Phase A 着手時に dispatch、A-1〜A-6 を順次)

```
# EPI-Stam Phase A 実装 — Csiszár scaling argument の Lean 化

## 親計画

- 親 sub-plan: `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md`
- inventory: `docs/shannon/epi-stam-to-conclusion-phaseA-mathlib-inventory.md` (前段 Brief A の出力)

## 担当範囲

A-0〜A-6 を順次実装 (atomic、partial commit 可だが publish は A-6 完了後)。
触る file:

1. `Common2026/Shannon/EPIStamToBridge.lean` (+120-220 行、主要)
2. `Common2026/Shannon/EntropyPowerInequality.lean` (案 a で +30 行、`_unconditional` 新規)
3. `Common2026/Shannon/EPIStamDischarge.lean` (docstring +5 行)
4. `Common2026/Shannon/EPIL3Integration.lean` (post-merge cleanup、14 件 tag sed 書換)

## Sub-bound 引数表 (CLAUDE.md `Brief content checklist` 必須項目)

| Sub-bound (新規 lemma 名) | 要求 hypothesis 側 | 必要 bridge / 既存補題 |
|---|---|---|
| `isStamScalingNoiseHyp_of_*` (A-1) | richness side (probability space 上の noise extension) | inventory §1 候補に依存、無ければ staged のまま honest |
| `csiszarGap_hasDerivAt` (A-2-3) | sister Phase D output side (`IsDeBruijnRegularityHyp X _ P` / `IsDeBruijnIntegrationHyp X _ P T` 等 5 件) | `heatFlowPath2_law` (`HeatFlowPath.lean:63`)、`derivAt_entropy_eq_half_fisher_v2` (`EPIStamDischarge.lean:204`)、`differentialEntropy_const_mul` (A-2-1 / inventory §2) |
| `csiszarGap_deriv_le_zero` (A-3-3) | `IsStamInequalityHyp` 側 (Phase D 出力) | A-2-3 出力 + A-3-2 Cauchy-Schwarz weight (inventory §4) |
| `isStamToEPIScalingHyp_of_stam_debruijn` (A-4-4) | `IsStamScalingNoiseHyp` (A-1 staged 又は genuine) + sister Phase D output 5 件 | A-4-3 `antitoneOn_of_deriv_nonpos` (inventory §5) |
| `isStamToEPILimitHyp_trivial` (A-5-1) | `IsStamScalingNoiseHyp` 側 (A-1 の `Z_X, Z_Y` witness 流用) | 既存 `csiszarGap_at_one_eq_zero_of_gaussian_pair` (`EPIL3Integration.lean:1194`)、再利用 |
| `isStamToEPIBridgeHyp_of_stam_debruijn` (A-5-2) | A-4 + A-5-1 出力組合せ | 既存 `isStamToEPIBridgeHyp_of_scaling_limit` (`EPIStamToBridge.lean:266`、`@audit:ok`) |
| `entropy_power_inequality_unconditional` (A-6-1 案 a) | A-5-2 出力 + Phase D 5 hypothesis を caller 経由 | 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:232`、本体不変) |

## 継承 `@audit:*` タグの語彙整合 inline check (CLAUDE.md `Brief content checklist` 必須項目)

A-V-5 で `EPIL3Integration.lean` 14 件 sed 書換時、貼付後 `grep -n '@audit:'
Common2026/Shannon/EPIL3Integration.lean` で empty slug / 未参照 slug / 旧
`@audit:suspect(epi-debruijn-integration-phaseD-plan)` (Phase D 起源、書換対象外) との
混同を listing → orchestrator に報告。orchestrator が `docs/audit/audit-tags.md` 語彙
照合 → Edit 確定 → 追加 commit。

## 運用ルール (CLAUDE.md `Standard agent prompt boilerplate`)

[Standard agent prompt boilerplate を verbatim 貼付、worktree .lake 共有 / ブランチ規律 /
skeleton-driven / 検証 silent / scope 4 file / import policy / 撤退ライン honest /
commit 自走 push なし]

## 完了報告

orchestrator に: A-0〜A-V の各 step 進捗 + 撤退ライン発動有無 + 4 file silent 結果 +
新規 staged predicate (`IsStamScalingNoiseHyp` 含む) の一覧 + 行数実績 + 独立 honesty
audit subagent 起動要否 (A-1 で新規 staged 導入 = 起動必須)
```

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-25 mini-plan 起草 (Phase D 直後)**: 親 plan §Phase A の line 467-547 を
   A-0〜A-V の 7 sub-step に分解、Mathlib 在庫期待 + 撤退ライン詳細化 + post-merge
   cleanup 継承を盛込。重要 drift 修正: 親 plan 内の `EPIStamDischarge.lean:304` /
   `EntropyPowerInequality.lean:188` は実コード verbatim 確認で `:337` / `:232` の
   drift と判明、本 mini-plan で正しい行番号に修正。

2. **2026-05-25 撤退ライン拡張**: 親 plan の L-Concl-A-α / β (2 件) に対し、本 mini-plan
   で **L-Concl-A-γ / δ / ε / ζ の 4 件を新規追加**。理由:
   - γ: A-1 で `IsStamScalingNoiseHyp` (standard normal pair witness) が Mathlib 整備
     不足で genuine 構築困難な可能性、Phase 0 で `_of_gaussian` retract された前例
     (`EPIStamToBridge.lean:317-327`) を踏まえ、新規 staged predicate として honest
     externalization の余地を残す
   - δ: A-2 で 2-source `heatFlowPath2` 経由の `g'(s)` 微分式が Cover-Thomas 1-source
     `Z_t := X + √t · G` と reparametrize 必要、scaling 補正項キャンセル失敗で sister
     Phase D との cooperation 必要になる可能性
   - ε: A-2-1 で `differentialEntropy_const_mul` が Mathlib にも Common2026 にも不在
     の可能性、新規補題が large 化する場合の scope 保護
   - ζ: A-3-2 で Cover-Thomas eq.(17.43) Cauchy-Schwarz weight 不等式が Mathlib 不在
     の可能性、自前 plumbing >100 行になる場合の honest externalization

3. **2026-05-25 案 a vs 案 b (A-6 主定理 hypothesis-free 化)**: 案 a (新 wrapper
   `_unconditional` を追加、本体不変、downstream rename 最小) を **推奨**。理由:
   - 案 b (主定理本体 signature 変更) は 28 件 ripple、本 Phase A scope を超過 (親
     plan §Phase B が担当)
   - 案 a なら本 Phase A は genuine theorem 1 件追加に集中、段階化 ship 可能
   - Phase B が 23 件 corollary を hypothesis-free 化する際に主定理本体の signature
     変更可否を再判定、本 Phase A はその option を残す
