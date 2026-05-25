# EPI Stam → EPI conclusion — merge / conclusion plan

> **Status**: 未着手 (Phase 設計済、2026-05-24 Wave 2 planner 起草)。本 plan は実装未着手だが
> Phase 0 / A / B / V の設計レベル shape が確定済。
> **Created**: 2026-05-24 (Wave 1.5 item #8、`epi-moonshot-plan` 76 件 slug 分割)。
> **Parent (history)**: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (PASS-THROUGH publish 済、
> 撤退ライン L-EPI3 = EPI 結論そのものの genuine discharge を本 sub-plan が担当)。

## Position

- 親 moonshot: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (Phase A-E publish 済、L-EPI3
  hypothesis pass-through)
- 関連 sub-plan (上流入力):
  - [`epi-stam-discharge-plan.md`](./epi-stam-discharge-plan.md) — L-EPI1 (Stam inequality)
    上流入力 (Phase D 出力)
  - [`epi-debruijn-integration-plan.md`](./epi-debruijn-integration-plan.md) — L-EPI2
    (de Bruijn integration) 上流入力 (Phase D 出力)
- 関連 wall plan: [`fisher-info-moonshot-plan.md`](./fisher-info-moonshot-plan.md) / V2 系

## Motivation

EPI moonshot は L-EPI3 (EPI 結論自身) を `IsEntropyPowerInequalityHypothesis` predicate
hypothesis pass-through 形で publish (`EntropyPowerInequality.lean:168` 真 Prop、本体は
`:= h_epi` で着地 `:188`)。Stam (L-EPI1) + de Bruijn integration (L-EPI2) → EPI conclusion の
合流部、および Phase E 補助 corollary 群 (multi-arg, monotonicity, scaling, log-form) の
genuine 化が本 sub-plan の責務。

`epi-moonshot-plan.md` §Approach で「`stam → ∫_0^∞ deBruijn → EPI`」を予告しており、本 sub-plan
は **Stam + de Bruijn の合成 → EPI conclusion の組み立て + 露出 corollary** に集中する
(Stam 内部 / de Bruijn 内部の本格 discharge は sister sub-plan に委譲)。

**EPIPlumbing.lean 3 件先行 close 機会**: 本 file の 3 件 (`entropy_power_inequality_normalized`
`:181` / `entropy_power_inequality_four_arg` `:212` / `two_differentialEntropy_ge_log_sum` `:249`)
は **既存 `entropy_power_inequality` (L-EPI3 hypothesis 取り) を reshape したもの**で、
sister sub-plan の output 不要、`Real.exp_*` / `Real.log_*` の配線のみで closure 可。
**Phase 0 として先行 close 候補**。

**前提条件 (重要)**: V2 Fisher info 経路 (4 sub-predicate `@audit:suspect(fisher-info-moonshot-plan)`
状態) は sister sub-plan を介して本 plan に影響。本 plan の Phase A は sister sub-plan
(Stam discharge + de Bruijn integration) の Phase D 出力に依存 = **sister 待ち**。
Phase 0 と Phase B 一部 (EntropyPowerInequality.lean reshape) は **独立着手可**。

## Scope

担当 file 群 (W1-B `wave1-plan-sync-epi-bm.md` ベース):

| file | 役割 | suspect 件数 | LoC |
|---|---|---|---|
| `Common2026/Shannon/EPIStamStep3Body.lean` | Stam Step 3 body (Lagrange multiplier / λ 最適化) | 9 | 391 |
| `Common2026/Shannon/EPIStamDeBruijnConclusion.lean` | Stam + de Bruijn → conclusion 合流 | 6 | 377 |
| `Common2026/Shannon/EntropyPowerInequality.lean` | EPI 主定理 + Phase E corollary (multi-arg / log-form / scaling) | 5 | 420 |
| `Common2026/Shannon/EPIPlumbing.lean` | EPI plumbing (normalized form / four-arg / `Real.exp` ↔ log 等価変換) | 3 | 319 |

**合計**: 23 件 suspect / 1507 LoC 既存 (sub-plan 起動時の closure target)。Phase 0/A/B で
増分予想 ~260-430 行。

- **Mathlib 壁 4 分類**:
  - Stam + de Bruijn の合成自体は (a) 定義整合 + (c) 配線中心 — sister sub-plan が discharge
    すれば本 sub-plan は medium ROI (Mathlib `Real.exp_*` / `Real.log_*` の配線で済む corollary
    が多い)。
  - `EPIPlumbing.lean` 3 件は **high ROI** (log-form 等価変換、L-EPI3 連鎖から trivial)。
  - `EntropyPowerInequality.lean` の Phase E corollary 群は medium (Phase E の plan §D
    multi-arg / scaling 設計と対応)。
  - `EPIStamStep3Body.lean` Lagrange optimization は medium (Mathlib `optimal_lambda` 系
    発掘で進む)。
- **Tier**: 3 (long-term、ただし `EPIPlumbing.lean` 3 件は単独で先行 close 可能 — Wave 1.5 後の
  早期 high-ROI 候補)。

## Closure criteria

- 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:188`) から L-EPI3 hypothesis
  引数を削除 (genuine discharge)、`IsEntropyPowerInequalityHypothesis` 自身を `theorem` に格上げ。
- Phase E corollary 群 (multi-arg / scaling / log-form / normalized / four-arg) を全て
  genuine 化、`@audit:suspect(epi-stam-to-conclusion-plan)` を `@audit:ok` に降格 (23 件)。
- 連鎖効果: sister sub-plan (`epi-stam-discharge-plan` 39 + `epi-debruijn-integration-plan` 14)
  の closure と組み合わせて EPI エコシステム全 76 件 close。

## ゴール / Approach

### 全体戦略

**EPI 結論** (Cover-Thomas Theorem 17.7.3):
```
exp(2/n · h(X+Y)) ≥ exp(2/n · h(X)) + exp(2/n · h(Y))
```
n = 1 (本 file の射程):
```
exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))
```

合流 path (Csiszár scaling argument):
```
[Stam: 1/J(X+Y) ≥ 1/J(X) + 1/J(Y)]     ←── epi-stam-discharge-plan Phase D
                  +
[de Bruijn integ: h_target - h_X = ∫ J(X_t) dt]  ←── epi-debruijn-integration-plan Phase D
                  ↓
            [Csiszár scaling]
            X → λ·X, Y → (1-λ)·Y
            scale-invariance + heat-flow path
                  ↓
       g(t) := entropyPower (X+Y+√t·Z) - entropyPower (X+√t·Z) - entropyPower (Y+√t·Z)
       g'(t) ≤ 0  (from Stam + de Bruijn)
       g(∞) = 0   (Gaussian limit)
       =>  g(0) ≤ 0  =>  EPI
```

**鍵となる構造選択** (Mathlib-shape-driven):

- **`entropyPower μ := Real.exp (2 * differentialEntropy μ)`** (`EntropyPowerInequality.lean:80`):
  `Real.exp_pos` / `Real.exp_log` / `Real.exp_add` の結論形に直結。
- **`Real.exp_log`** + **`Real.log_exp`**: log-form / exp-form の equivalence で多数の corollary
  を機械的に導出。
- **`Real.exp_le_exp`** (`x ≤ y ↔ exp x ≤ exp y`): normalized form (Cover-Thomas
  `(2πe)⁻¹ · entropyPower`) への scaling は単純 multiply。
- **既存 `entropy_power_inequality_gaussian_saturation`** (`EntropyPowerInequality.lean:226`):
  Gaussian 限定 full discharge、本 plan の Phase B では Gaussian case を **既存** として再利用。

### Approach 図

```
[Sister sub-plan outputs (前提)]                  [Mathlib 既存 (utility)]
  ────────────────────────                          ──────────────────
  IsStamInequalityHyp (Stam genuine)               Real.exp / Real.log
  IsDeBruijnIntegrationHyp (de Bruijn genuine)     Real.exp_pos / Real.exp_log / Real.log_exp
  IsStamToEPIBridgeHyp (Csiszár scaling)           Real.add_le_add / nonneg arithmetic
                                                   gaussianReal_add_gaussianReal_of_indepFun

       ▲                                                  ▲
       │ sister 待ち (本 plan Phase A 入口)                │ 配線中心
       │                                                  │
       └──────────────────────┬───────────────────────────┘
                              ▼
              Phase 0 — EPIPlumbing 3 件先行 close (high ROI、独立着手可)
                              ▼
              Phase A — Stam + de Bruijn 合流 skeleton (sister 待ち)
                              ▼
              Phase B — Phase E corollary 各種 genuine 化
                              ▼
              Phase V — verify + Common2026.lean 編入
                              ▼
              EPI エコシステム 76 件 全 closure
```

### 段階的 ship 設計 (Tier 0 / 1 / 2)

- **Tier 0 (high ROI, 独立着手可)** = Phase 0: `EPIPlumbing.lean` 3 件先行 close。
  partial publish 価値あり (normalized form / four-arg / log-form 等が `@audit:ok` に降格)。
- **Tier 1 (sister 一部完了で着手可)** = Phase 0 + B 一部: `EntropyPowerInequality.lean`
  Phase E corollary 5 件のうち scaling / monotonicity / multi-arg 形 (L-EPI3 hypothesis を
  受け取って reshape する形)。
- **Tier 2 (sister 完了待ち)** = Phase 0 + A + B 全部: Stam + de Bruijn 合流 → L-EPI3 genuine
  化、主定理 `entropy_power_inequality` を `theorem` に格上げ、`EPIStamStep3Body.lean` 9 件 +
  `EPIStamDeBruijnConclusion.lean` 6 件 closure。

### 規模見積もり

| Phase | 自作要素 | 想定行数 | 依存 |
|---|---|---|---|
| 0 | EPIPlumbing 3 件先行 close (normalized / four-arg / log-form) | ~30-50 | 独立 |
| A | Stam + de Bruijn 合流 skeleton (Csiszár scaling) | ~80-150 | sister 両方 |
| B | Phase E corollary 各種 (multi-arg, scaling, log, Lagrange) | ~150-250 | sister 両方 |
| V | verify + Common2026.lean 編入 + roadmap | ~5-10 | — |
| **合計** | | **~265-460** | |

中央予測 **~350 行**。`EPIStamStep3Body.lean` + `EPIStamDeBruijnConclusion.lean` +
`EntropyPowerInequality.lean` + `EPIPlumbing.lean` (合計 1507 行) に分散追記。

---

## 進捗

- [x] Phase 0 — `IsStamToEPIScalingHyp` defect cleanup (prerequisite, sister/A/B 全 block) ✅ 2026-05-25 (commits `0d54e89` / `78cf2ec` / `2809168`)
- [x] Phase 0-Plumbing — `EPIPlumbing.lean` 3 件先行 close (high ROI、独立着手可) ✅ 2026-05-25 (prior commit `f150cdc` + `5f923e4`)
- [ ] Phase A — Stam + de Bruijn 合流 skeleton (sister 待ち、Phase 0 完了前提) 📋
- [ ] Phase B — Phase E corollary 各種 genuine 化 (Phase 0 完了前提) 📋
- [ ] Phase V — verify (`lake env lean ...`) + Common2026.lean 編入 📋

proof-log: yes (各 Phase 完了時に `docs/shannon/proof-log-epi-stam-to-conclusion-phase-*.md`)

---

## Phase 0 — `IsStamToEPIScalingHyp` defect cleanup (prerequisite) 📋

> **新規追加 (2026-05-25)**: Wave 3 second batch (`0fe2ad4`) で発見された
> `IsStamToEPIScalingHyp` の launder 疑いを cleanup する prerequisite Phase。
> Phase A / B より先に処理する必要 (Phase A の合流定理は本 predicate を `scaling`
> field として bundle するため、本 phase の signature 確定後でないと Phase A が
> 着手できない)。Phase 0-Plumbing は本 phase と独立、並列着手可。

### Phase 0.A — Defect analysis

**対象**: `IsStamToEPIScalingHyp` (`Common2026/Shannon/EPIStamToBridge.lean:147-154`)

**現状 body** (audit:suspect(epi-stam-to-conclusion-plan) 付与済、`:138-146`):

```lean
def IsStamToEPIScalingHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  IsStamInequalityHyp X Y P →
    ∀ (g0 g1 : ℝ),
      g0 = entropyPower (P.map (fun ω => X ω + Y ω))
            - entropyPower (P.map X) - entropyPower (P.map Y) →
      g1 = 0 →
      g0 ≥ g1
```

**Launder 機構** (5-8 行解説):

1. 第 4 引数 `g1 = 0` は equation hypothesis として **固定値 0** が渡される。
2. 第 3 引数 `g0` は equation hypothesis で gap 式に固定される。
3. 結論 `g0 ≥ g1` は両 substitution 後に `entropyPower (X+Y) − entropyPower X
   − entropyPower Y ≥ 0` に reduce。
4. これは **EPI 結論そのもの** (`IsEntropyPowerInequalityHypothesis` の body と等価)。
5. `IsStamInequalityHyp X Y P →` のため 厳密には「Stam を仮定したら EPI」だが、
   それは bridge predicate (`IsStamToEPIBridgeHyp`) と同じ shape — つまり本
   predicate は **bridge を `(g0, g1)` 経由で wrap した cosmetic alias** に過ぎず、
   "Csiszár scaling-monotonicity step" を独立に carry していない。
6. 結果として `isStamToEPIBridgeHyp_of_scaling_limit` (`:196-211`) は `h_scaling`
   を `(gap, 0) rfl rfl` で 1 度 apply して EPI に到着するが、これは **bridge を
   bridge から導く循環の cosmetic wrapping**。
7. 命名 `IsStamToEPIScalingHyp` は Cover-Thomas Lemma 17.7.3 の Csiszár scaling
   構造 (heat-flow path 上の `g(t)` monotone) の存在を suggest するが、type には
   その構造が無い (`g1 = 0` 固定で path-endpoint との非自明な接続が消える)。

**Discovery context**: Wave 3 second batch (commit `0fe2ad4`, 2026-05-25)、
EPI-Stam agent が `@audit:suspect(epi-stam-to-conclusion-plan)` を付与
(`:138-146` の docstring 内)。

**Consumer 影響範囲** (`Common2026/Shannon/EPIStamToBridge.lean` 内):

| line | 役割 | 性質 |
|---|---|---|
| `:147-154` | def 本体 (defect 当該) | refactor 対象 |
| `:196-211` `isStamToEPIBridgeHyp_of_scaling_limit` | scaling + limit → bridge | signature 連動 |
| `:222-244` `isStamToEPIScalingHyp_of_gaussian` | Gaussian 退化 discharge | 退化 proof 書き直し |
| `:278` `IsEPIScalingDecomposedPipeline.scaling` field | pipeline structure field | structure 連動 |
| `:341-352` `isStamToEPIScalingHyp_symm` | symmetry 補題 | signature 連動 |
| `:406` `isStamToEPIScalingHyp_*` (匿名で 1 件) | discharge variant | signature 連動 |
| `:447-465` `entropyPower_add_ge_of_scaling_*` (2 件) | scaling から EPI 抽出 | signature 連動 |
| `:476-492` `isStamToEPIScalingHyp_cast` (関数引数 cast) | (X', Y') への移送 | signature 連動 |
| `:504` `isStamToEPIScalingHyp_*` (discharge variant) | discharge variant | signature 連動 |
| `:553-566` `entropyPower_add_ge_of_pipeline_*` (2 件) | pipeline から EPI 抽出 | signature 連動 |
| `:650` `IsEPIPipelineBundle` field (anonymous record) | bundle field | bundle 連動 |
| その他 docstring 言及 (`:31`, `:72`, `:85`, `:165`, `:185`) | doc 5 件 | 説明文更新 |

`Common2026/Shannon/EPIStamDeBruijnConclusion.lean:114` — docstring で
「`IsStamToEPIScalingHyp` は coarse で gap monotone を smuggle」と既に明記。
これは defect 発見前から本 file 設計者が気付いていた suggestion (本 Phase で
genuine 化すれば本 docstring の批判が正当な改善に変わる)。

**合計 consumer**: 関数本体 15+ 件 + docstring 5+ 件 = **20+ 件 ripple**、
signature 変更は **大規模 ripple**。

### Phase 0.B — Refactor design (両案併記、推奨明示)

**案 1: signature 全面 refactor (Csiszár scaling content 追加) [推奨]**

第 2 引数 `g1` を **path endpoint 値の explicit parameter** に格上げ、または
heat-flow path `s ∈ [0, 1]` 上の monotonicity を直接 carry する形に書き換える。
スケッチ (textbook 直訳でなく Mathlib-shape-driven、要 M0 で `Monotone` /
`MonotoneOn` / `HasDerivAt` の結論形を再確認):

```lean
-- スケッチ (def の確定は Phase 0.C-2 の M0 在庫調査後)
def IsStamToEPIScalingHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ (s : ℝ), 0 ≤ s → s ≤ 1 →
    let X_s := heatFlowPath s X      -- 新規 def (Phase 0.C-1)
    let Y_s := heatFlowPath s Y
    let gap_s := entropyPower (P.map (fun ω => X_s ω + Y_s ω))
                  - entropyPower (P.map X_s) - entropyPower (P.map Y_s)
    -- 主張: s ↦ gap_s が non-decreasing (Csiszár scaling)
    -- もしくは: gap_0 ≥ gap_1 (path endpoint 比較)
    -- Mathlib `Monotone` / `MonotoneOn` 結論形を採用
    sorry
```

- **必要 Mathlib API** (M0 在庫): `Monotone`, `MonotoneOn`, `HasDerivAt`,
  `MonotoneOn.le_of_le_endpoint` 等
- **新規定義**: `heatFlowPath : ℝ → (Ω → ℝ) → (Ω → ℝ)` (heat-flow OU semigroup の
  finite-time evolution、`s ↦ √(1−s) · X + √s · Z` の形で独立 Gaussian Z を mixing)
- **Csiszár scaling 内容**: `gap'(s) ≥ 0` を Stam (`1/J(X+Y) ≥ 1/J(X) + 1/J(Y)`)
  + de Bruijn (`d/ds h(X_s) = (1/2) J(X_s)`) から導出 — これが genuine な
  scaling-monotonicity step
- **Consumer ripple**: 全 15+ 件で `h_scaling` の使い方が変わる
  - `isStamToEPIBridgeHyp_of_scaling_limit`: 新 signature では `h_scaling 0 ...`
    から path-endpoint 経由で EPI を取り出す
  - Gaussian 退化 `isStamToEPIScalingHyp_of_gaussian`: 退化 monotone (常に `gap ≡ 0`)
  - `_symm` / `_cast`: 新 signature に従って書き直し
  - `IsEPIScalingDecomposedPipeline.scaling`: structure 連動更新
- **規模**: ~300-500 行 (heat-flow path 定義 + monotone 証明 + consumer 全更新 +
  Phase 0.C で 6 sub-phase 分割)
- **長所**: defect 真に解消、Phase A 合流定理が genuine な scaling content を
  受け取れる
- **短所**: 規模大、M0 在庫調査 + heat-flow path 定義の新規追加が必要

**案 2: signature を bridge 等価 alias と honest 命名する (cosmetic launder の開示)**

`IsStamToEPIScalingHyp` を `IsStamToEPIBridgeAliasViaGapWrap` 等にリネーム、
docstring に「現状は bridge と equivalent な cosmetic wrap」と honest 明記。

- 機構的修正なし、命名整合 + docstring 補強のみ
- consumer ripple: 名前変更 only (Edit replace_all 1 発で済む)
- 規模: ~30 行 (rename + docstring)
- **長所**: 低リスク、Phase A 着手を block しない
- **短所**: defect の honest **開示** であって**解消**ではない、Phase A の
  scaling discharge は依然として bridge 直接証明と等価で、本来の Csiszár scaling
  argument の構造分解は実現しない

**推奨**: **案 1** (genuine Csiszár scaling 化)。理由:

1. EPI 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:188`) の
   genuine theorem 格上げが本 sub-plan の最終目標であり、`IsStamToEPIScalingHyp`
   が bridge と等価の launder 状態のままだと **`IsEPIScalingDecomposedPipeline`
   の structure 分解が cosmetic** にしかならない (`scaling : IsStamToEPIScalingHyp
   X Y P` field が bridge field と区別不能)。
2. Phase A の合流定理 (Csiszár scaling argument) は本 predicate を **genuine な
   monotonicity step** として bundle する設計、案 2 だと Phase A の合流定理自体
   が cosmetic alias を経由する構造になる。
3. 案 2 は **暫定 stop-gap** として並走可 (Phase 0 完了前に Phase 0-Plumbing
   3 件先行 close を進める間、命名 honest 化だけ先に commit する)。

### Phase 0.C — Implementation sub-phases (案 1 採用時)

- [ ] **0.C-1: heat-flow path 定義 (M0 在庫調査 + 新規 def)** 📋
  - M0: `Mathlib` 内の OU semigroup / heat semigroup / Gaussian convolution
    既存 API を loogle 調査 (`Mathlib.Probability.ProbabilityMassFunction.Constructions`,
    `MeasureTheory.Gaussian` 系)
  - `Common2026/Shannon/HeatFlowPath.lean` 新規 file or 既存
    `Common2026/Shannon/EPIStamToBridge.lean` 冒頭に追加 (規模次第)
  - `heatFlowPath s X := √(1-s) · X + √s · Z_X` (Z_X は独立 Gaussian)
  - 基本性質: `heatFlowPath 0 X = X` (a.e.)、`heatFlowPath 1 X = Z_X` (Gaussian)
  - 規模: ~80-120 行
- [ ] **0.C-2: 新 `IsStamToEPIScalingHyp` signature 確定 + 関連 docstring 整備** 📋
  - Mathlib-shape-driven: `Monotone` / `MonotoneOn` 結論形を 1-3 候補比較
  - `@audit:suspect(epi-stam-to-conclusion-plan)` → 新 def に伴い再判定
    (genuine になれば `@audit:ok`、staged ありなら `@audit:staged`)
  - 規模: ~30-50 行 (def + docstring + 基本性質 lemma 1-2 件)
- [ ] **0.C-3: Gaussian 退化 `isStamToEPIScalingHyp_of_gaussian` 新 signature 版** 📋
  - 新 signature では Gaussian case は `gap_s ≡ 0` (退化 monotone)
  - 既存 `entropy_power_inequality_gaussian_saturation` (`EntropyPowerInequality.lean:226`)
    を path 各 s で apply
  - 規模: ~40-60 行 (新規) — 既存 `:222-244` 23 行を置き換え
- [ ] **0.C-4: 残 14 consumer の sequential update** 📋
  - 各 consumer (`_symm` / `_cast` / pipeline field / `entropyPower_add_ge_of_*` 等)
    を新 signature に書き直し
  - 順序: pure variant (`_symm` / `_cast`) → discharge variant (`_of_*`) →
    composition (pipeline field / bundle field)
  - 規模: ~100-150 行 (各 5-15 行 × 14 件)
- [ ] **0.C-5: `IsEPIScalingDecomposedPipeline` structure update + 全 instance 検証** 📋
  - structure field 新 signature 連動
  - 全 instance / construction (`isEPIScalingDecomposedPipeline_of_*` 等) 更新
  - 規模: ~40-60 行
- [ ] **0.C-6: 全 file の `lake env lean` silent 検証** 📋
  - `Common2026/Shannon/EPIStamToBridge.lean` (本体)
  - `Common2026/Shannon/EPIStamDeBruijnConclusion.lean` (docstring 言及 + 下流)
  - `Common2026/Shannon/EntropyPowerInequality.lean` (主定理 path、間接)
  - `Common2026/Shannon/EPIL3Integration.lean` (pipeline bundle 経由)
  - 必要なら `lake build Common2026.Shannon.EPIStamToBridge` で olean 再生成
  - `Common2026.lean` import 追加 (HeatFlowPath.lean を新規追加した場合のみ)

### Phase 0.D — Sister plan 影響

- 本 sub-plan の **Phase A / B / V は Phase 0 完了後に restart** (現状 Phase A
  は sister 待ち state、Phase 0 完了で sister 待ちの shape が確定する)
- sister sub-plan (`epi-stam-discharge-plan` / `epi-debruijn-integration-plan`)
  自身は本 Phase 0 と独立 (sister は `IsStamInequalityHyp` / de Bruijn integration
  hypothesis を扱い、本 defect predicate は touch しない)
- Phase 0-Plumbing 3 件は本 Phase 0 と独立 (EPIPlumbing は L-EPI3 hypothesis
  pass-through で `IsStamToEPIScalingHyp` を経由しない)、**並列着手可**
- `docs/shannon/epi-moonshot-plan.md` の 76 件 closure 計画は変更なし
  (本 Phase 0 は 1 predicate の signature refactor、closure 数は不変)

### Done 条件

- `IsStamToEPIScalingHyp` の新 signature が genuine な Csiszár scaling 内容を
  carry (案 1 採用時) — `@audit:suspect(epi-stam-to-conclusion-plan)` → `@audit:ok`
  に降格 (Phase A 完了で全 chain が genuine になった時点)
- 20+ consumer 全件 silent `lake env lean`
- Honest auditor (`subagent_type: "honesty-auditor"`) が新 def を全 OK 判定
  (新 staged predicate を導入する場合は orchestrator 必須起動)
- Phase A / B 着手可能な状態 (新 signature 確定 + structure 連動完了)

### 撤退ライン (honest 限定)

- **L-Concl-0Sc-α** (許容、案 1 → 案 2 退避): heat-flow path 定義 / Csiszár
  scaling discharge が想定外に大規模化 (>800 行) または Mathlib OU semigroup
  API が不足し新規大量 plumbing が必要と判明した場合、**案 2 (cosmetic alias
  rename + docstring honest 化)** に退避。docstring で「現状は bridge と
  equivalent な cosmetic wrap、genuine Csiszár scaling 化は未着手」を明示、
  `@audit:staged(epi-stam-to-conclusion-plan)` 留め。Phase A は alias 経由で
  進められるが、Phase B / V の最終 `@audit:ok` 降格は不可、partial publish。
- **L-Concl-0Sc-β** (許容、heat-flow path Mathlib 壁): Mathlib に OU
  semigroup / Gaussian convolution の必要 API が皆無で本 sub-plan で plumbing
  を build するのが本筋を外れる場合、heat-flow path を抽象 hypothesis
  (`IsHeatFlowPathExistsHyp X Y P : Prop`) として stage、honest 命名 +
  load-bearing 明示。`@audit:residual(epi-stam-to-conclusion-plan-heatflow)`
  付与し、Mathlib 上流貢献 task として外出し。
- **L-Concl-0Sc-γ** (defect 発見時の停止): Phase 0.C-1 の M0 在庫調査中、
  または consumer update 中に既存コード (sister sub-plan 出力含む) に新たな
  honesty defect を発見した場合、即座にユーザに defect 報告、本 Phase の進行を
  停止し orchestrator に honest-auditor 起動を依頼。**defect の上に黙って積み
  上げない** (CLAUDE.md `検証の誠実性` 規律)。

### proof-log

`docs/shannon/proof-log-epi-stam-to-conclusion-phase-0.md` を Phase 0.C 完了時に
書き出し (M0 在庫調査結果 + heat-flow path 定義の Mathlib-shape 整合性 +
consumer update 順序 + 各 consumer の `lake env lean` 出力)。

---



### スコープ

`EPIPlumbing.lean` 内 3 件の `@audit:suspect(epi-stam-to-conclusion-plan)`:

1. `entropy_power_inequality_normalized` (`:181`) — Cover-Thomas `(2πe)⁻¹` normalization form:
   `N(X+Y) ≥ N(X) + N(Y)` where `N(μ) := (2πe)⁻¹ · entropyPower μ`
2. `entropy_power_inequality_four_arg` (`:212`) — 4-arg chain form (5 変数のうち 2 つを束ねた形)
3. `two_differentialEntropy_ge_log_sum` (`:249`) — log-form: `2 h(X+Y) ≥ log(entropyPower X +
   entropyPower Y)`

これらは **既存 `entropy_power_inequality` (`EntropyPowerInequality.lean:188`、L-EPI3
hypothesis 取り) を reshape したもの**で、sister sub-plan の output 不要、`Real.exp_*` /
`Real.log_*` の配線のみで closure 可。

### Approach

**独立着手可** = sister sub-plan の closure を待たずに本 Phase 0 のみ着手して partial publish
できる。`entropy_power_inequality` を呼び出す側 (L-EPI3 hypothesis を caller が供給) なので、
本 phase は **hypothesis pass-through を継続したまま** corollary 形を整える。

closure 規律: `@audit:suspect(epi-stam-to-conclusion-plan)` → **`@audit:ok`** に降格できるのは
**caller が L-EPI3 hypothesis を供給した時点で genuine** な corollary に変わる場合。実際には
本 Phase 0 では caller の供給は未だなので **`@audit:staged(epi-stam-to-conclusion-plan)` に
昇格 (Prop は実 Prop、本体は hypothesis pass-through 形)** が正しい流儀。Phase A 完了で sister
output から L-EPI3 を導出すると **`@audit:ok`** に降格。

### Done 条件

- `EPIPlumbing.lean` 3 件の docstring を `@audit:suspect(epi-stam-to-conclusion-plan)` から
  `@audit:staged(epi-stam-to-conclusion-plan)` に書き換え (本体は既に hypothesis pass-through
  形で genuine reshape 済み)
- `lake env lean Common2026/Shannon/EPIPlumbing.lean` clean (0 sorry / 0 warning)
- 本 Phase は **既存コードの defect が無いことを確認 + 監査タグ整理**が主目的、コード追加は最小限

### ステップ

- [ ] **0-1**: `EPIPlumbing.lean` 3 件の現状コードを Read で確認、L-EPI3 hypothesis pass-through
      の体裁が genuine reshape か確認
- [ ] **0-2**: 3 件の `@audit:suspect` を `@audit:staged` に書き換え (本体修正なし、タグのみ)
- [ ] **0-3**: `lake env lean EPIPlumbing.lean` clean
- [ ] **0-4** (任意 stretch): 既存 EPIPlumbing 3 件に並び corollary を追加
      (e.g. `entropy_power_inequality_symm` symmetric form)、~10-20 行

### 撤退ライン

- **L-Concl-0-α** (本来不要): EPIPlumbing 3 件の本体が hypothesis pass-through 形でなく
  独立証明を要求している場合 (Read で defect 発見) → 即座にユーザに defect 報告、
  本 Phase の進行を停止し orchestrator に honest-auditor 起動を依頼。**defect の上に黙って
  積み上げない** (CLAUDE.md `検証の誠実性` 規律)。

---

## Phase A — Stam + de Bruijn 合流 skeleton (sister 待ち) 📋

> **Phase 0 完了前提**: 本 Phase の合流定理は `IsStamToEPIScalingHyp` を
> `IsEPIScalingDecomposedPipeline.scaling` field として bundle するため、Phase 0
> の signature refactor 完了 (または 0Sc-α 退避での cosmetic alias 確定) が
> 前提。Phase 0 が L-Concl-0Sc-α に退避した場合、本 Phase A の出力も `@audit:staged`
> 留めとなる。

### スコープ

sister sub-plan (`epi-stam-discharge-plan` Phase D 出力 + `epi-debruijn-integration-plan`
Phase D 出力) の closure を **入力**として、`IsStamToEPIBridgeHyp` (`EPIStamDischarge.lean:304`)
を genuine 化 + `IsEPIL3IntegratedPipeline` (`EPIL3Integration.lean:105`) を genuine
construct。

これにより `IsEntropyPowerInequalityHypothesis` (`EntropyPowerInequality.lean:168`、L-EPI3
真 Prop) が hypothesis-free に取れる = 主定理 `entropy_power_inequality` `:188` が genuine
theorem に格上げ。

### Approach (Csiszár scaling argument)

Cover-Thomas Lemma 17.7.3 の Csiszár scaling:

1. **scale-invariance**: `entropyPower (P.map (c · X)) = c² · entropyPower (P.map X)`
   (既存 `EPIPlumbing.lean:130-152` `entropyPower_map_mul_const` 経由)
2. **heat-flow path 上の gap 関数**:
   ```
   g(t) := entropyPower (P.map (X+Y+√t·Z)) - entropyPower (P.map (X+√t·Z))
                                           - entropyPower (P.map (Y+√t·Z))
   ```
3. **`g'(t)` の計算** (de Bruijn integration + Stam の組合せ):
   ```
   g'(t) = exp(2 h(X+Y+√t·Z)) · 2 · (1/2) J(X+Y+√t·Z) - similar terms
         = exp(2 h(...)) · J(...)
   ```
   Stam `1/J(X+Y_t) ≥ 1/J(X_t) + 1/J(Y_t)` と Cauchy-Schwarz で `g'(t) ≤ 0` を導出。
4. **`g(∞) = 0`** (Gaussian limit、`entropyPower (gaussianReal) = 2πe v`、X_t, Y_t, X+Y_t の
   各分散が `t` に比例 → 比率が 0 に収束)
5. **`g(0) ≤ g(∞) = 0`** (monotone decreasing) → **EPI**: `g(0) ≤ 0` = EPI 結論

### Done 条件

- `IsStamToEPIBridgeHyp X Y P` (`EPIStamDischarge.lean:304`、`IsStamInequalityHyp → L-EPI3`)
  を genuine 化 (Csiszár scaling argument)
- `IsEPIL3IntegratedPipeline X Y P` (`EPIL3Integration.lean:105`、Stam + bridge bundle)
  を sister output から genuine construct
- 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:188`) を L-EPI3 hypothesis
  なしに `theorem` 格上げ
- `EPIStamDeBruijnConclusion.lean` 6 件 + `EPIStamStep3Body.lean` 9 件 + `EntropyPowerInequality.lean`
  5 件のうち main theorem を含む 1 件を `@audit:ok` 降格

### ステップ

- [ ] **A-0**: sister 両方の Phase D 完了確認 (orchestrator に進捗確認)
- [ ] **A-1**: `g(t)` 定義 + 基本性質 (positivity / continuity / boundary value):
  ~30-50 行
- [ ] **A-2**: `g'(t) ≤ 0` の証明 (Stam + de Bruijn integration):
  ~50-80 行
- [ ] **A-3**: `g(∞) = 0` の Gaussian limit:
  ~30-50 行
- [ ] **A-4**: `g(0) ≤ 0` から EPI 結論 (`Real.exp_le_exp` 等):
  ~20-30 行
- [ ] **A-5**: `IsStamToEPIBridgeHyp` を genuine theorem に:
  ~20-30 行
- [ ] **A-6**: 主定理 `entropy_power_inequality` を hypothesis-free 化:
  ~10-20 行

### 撤退ライン

- **L-Concl-A-α** (許容): sister sub-plan の Phase D 撤退ライン (L-Stam-D-α / L-DB-D-α/β) が
  発動した場合、本 Phase A も対応する partial discharge に下がる。具体的には sister の
  honest hypothesis (`IsBlachmanIdentityHyp_smooth` 等) を caller 経由で受ける形になり、
  本 Phase A の出力も "smooth density 限定" の partial EPI になる。`Prop := True` 禁止、
  honest 命名 (`entropy_power_inequality_under_smooth_density` 等) で明示。
- **L-Concl-A-β** (許容): Gaussian limit `g(∞) = 0` が non-Gaussian で破綻する場合、
  Gaussian saturation limit hypothesis を追加。これは Csiszár scaling argument 自体の
  Cover-Thomas での標準仮定なので honest と扱う。

---

## Phase B — Phase E corollary 各種 genuine 化 📋

> **Phase 0 完了前提** (Phase A 経由で): Phase B の `@audit:ok` 降格は Phase A
> 主定理 genuine 化に依存、Phase A は Phase 0 完了に依存。Phase 0 が
> L-Concl-0Sc-α 退避の場合、本 Phase の corollary も partial 化 (L-Concl-B-α
> 経路)。

### スコープ

`EntropyPowerInequality.lean` Phase E corollary 5 件 (multi-arg / scaling / log-form /
normalized / 4-arg) + `EPIStamStep3Body.lean` 9 件 (Lagrange optimization) +
`EPIStamDeBruijnConclusion.lean` 残り 5 件 (合流系統 corollary) の genuine 化。

Phase 0 で `@audit:staged` に降格した 3 件 (EPIPlumbing) と合わせて、Phase A 完了 (主定理
genuine 化) を受けて **caller 側で L-EPI3 hypothesis を供給する形** から **genuine theorem
に格上げ** する作業。

### Approach

Phase A 完了で `entropy_power_inequality` 主定理が hypothesis-free になっているので、
Phase E corollary 群は **主定理を hypothesis-free に呼び出して reshape** することで genuine
化。具体的に:

- `entropy_power_inequality_normalized` (`EPIPlumbing.lean:181`): `N(X+Y) ≥ N(X) + N(Y)`
  形 = `entropyPower` を `(2πe)⁻¹` で割っただけ → 主定理から直接導出
- `entropy_power_inequality_four_arg` (`EPIPlumbing.lean:212`): 4-arg = 主定理 2 回適用
- `two_differentialEntropy_ge_log_sum` (`EPIPlumbing.lean:249`): log-form =
  `Real.log_le_log` / `Real.log_exp` で書き直し
- `entropy_power_inequality_log_form_integrated` (`EPIL3Integration.lean`): 同上
- multi-arg / scaling / monotonicity: 主定理を induction で n 段 / monotone でリフト
- `EPIStamStep3Body.lean` 9 件 Lagrange optimization 系: Phase A の `g'(t) ≤ 0` 計算で
  使われる Lagrange multiplier 補題群、`stam_lambda_min` + 既存補助補題で discharge

### Done 条件

- 5 + 9 + 6 (合計 20 件) すべて `@audit:ok` 降格 (Phase 0 の 3 件 + 本 Phase の 20 件 = 23 件全)
- `lake env lean` clean on 全 4 file

### ステップ

- [ ] **B-1**: EPIPlumbing 3 件を `@audit:staged` から `@audit:ok` に降格 (Phase A の主定理
      genuine 化を受けて hypothesis-free に書き換え):
  ~10-15 行
- [ ] **B-2**: EntropyPowerInequality.lean Phase E corollary 5 件 (multi-arg / scaling /
      monotonicity / normalized / log-form) を genuine 化:
  ~80-120 行
- [ ] **B-3**: EPIStamStep3Body.lean 9 件 (Lagrange optimization) の `@audit:suspect` を
      `@audit:ok` に降格 (Phase A での Csiszár scaling argument で使った Lagrange 補題群
      を Phase A 完了で genuine):
  ~30-50 行
- [ ] **B-4**: EPIStamDeBruijnConclusion.lean 残り 5 件 (合流系統 corollary) genuine 化:
  ~30-50 行

### 撤退ライン

- **L-Concl-B-α** (許容、Phase A 撤退ライン依存): Phase A-α (sister 撤退ライン伝播) が発動した
  場合、本 Phase の corollary も "smooth density 限定 / Gaussian 限定" の partial 化に下がる。
  `@audit:ok` ではなく `@audit:staged` に留まる corollary が出る可能性 → honest 命名で明示。

---

## Phase V — verify + Common2026.lean 編入 📋

### スコープ

- `lake env lean Common2026/Shannon/EPIPlumbing.lean` clean
- `lake env lean Common2026/Shannon/EntropyPowerInequality.lean` clean
- `lake env lean Common2026/Shannon/EPIStamStep3Body.lean` clean
- `lake env lean Common2026/Shannon/EPIStamDeBruijnConclusion.lean` clean
- `Common2026.lean` import 確認 (既に全 file import 済み)
- `docs/textbook-roadmap.md` Ch.17 EPI 行を最終 `[x]` に
- `docs/shannon/epi-moonshot-plan.md` の split-into 注記を更新 (23 件 closure 完了 = EPI
  エコシステム 76 件 全 closure 完了)

### Done 条件

- 上記 4 file 全て `lake env lean` clean
- 23 件 `@audit:suspect(epi-stam-to-conclusion-plan)` → `@audit:ok` 降格完了
- EPI エコシステム合計 76 件全 closure 完了 (sister 39 + 14 + 本 23)

---

## 撤退ライン総覧 (honest 限定)

| slug | Phase | 内容 | hypothesis 名 (例) | 解除条件 |
|---|---|---|---|---|
| L-Concl-0Sc-α | 0 | scaling refactor 案 1 → 案 2 退避 (cosmetic alias rename) | (rename only) | Mathlib OU/heat-flow API 整備後 case 1 再着手 |
| L-Concl-0Sc-β | 0 | heat-flow path Mathlib 壁時の hypothesis 化 | `IsHeatFlowPathExistsHyp X Y P` | Mathlib 上流貢献 task 完了 |
| L-Concl-0Sc-γ | 0 | M0 / consumer update 中の defect 発見停止 | (defect report) | orchestrator が honest-auditor 起動 |
| L-Concl-0-α | 0-Plumbing | EPIPlumbing 3 件に defect 発見時の停止 | (defect report) | orchestrator が honest-auditor 起動 |
| L-Concl-A-α | A | sister 撤退ライン伝播 (smooth density / score Lp) | sister 由来 honest hypothesis | sister の撤退ライン解除 |
| L-Concl-A-β | A | Gaussian limit `g(∞) = 0` の non-Gaussian 拡張 | `IsEPIGaussianLimitHyp X Y P` | Cover-Thomas Csiszár scaling tail bound 形式化 |
| L-Concl-B-α | B | A-α 伝播の corollary partial discharge | partial corollary は `@audit:staged` 留め | A-α 解除 |

**全撤退ライン共通規律**:
- **`Prop := True` placeholder 禁止** (現状 sister の L-EPI1 / L-EPI2 が `:= True`、本 plan
  Phase A で必ず実 Prop 化 or genuine theorem 化)
- **結論型 ≡ 仮説型 + `body := h` (循環) 禁止** (主定理を hypothesis-free 化する際、L-EPI3
  hypothesis pass-through から本物の `theorem` への昇格を確認、`def IsEntropyPowerInequalityHypothesis
  := entropy_power_inequality conclusion` のような循環は禁止)
- **load-bearing hypothesis を完成と称する name laundering 禁止** (`*_discharged` /
  `*_full` 命名を使わない、特に Phase A 完了時に主定理を `entropy_power_inequality_unconditional`
  のような名前にせず、元の `entropy_power_inequality` のまま hypothesis 引数のみ削除する)
- 撤退ライン発動時は docstring で「NOT a discharge / load-bearing on <sister 由来 hypothesis>」
  を必ず明示

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-24 Wave 2 planner Phase 起草**: stub plan (75 行、Phase 設計未起草) に Phase
   0 / A / B / V を埋め込み。`EPIPlumbing.lean` 3 件は **既存 `entropy_power_inequality`
   (L-EPI3 hypothesis 取り) を reshape したもの**で sister 待ち不要 + `Real.exp_*` /
   `Real.log_*` 配線のみで closure 可、**Phase 0 として先行 close** することを確定。
   ただし Phase 0 単独では caller の L-EPI3 hypothesis 供給は未だなので **`@audit:staged`
   昇格** が正しい流儀、Phase A 完了で `@audit:ok` 降格。
2. **2026-05-24 sister 依存関係明示**: Phase A は sister 両方 (Stam + de Bruijn) の Phase D
   完了待ち。Phase 0 と Phase B 一部 (EntropyPowerInequality reshape) は独立着手可。
   sister の撤退ライン (L-Stam-D-α / L-DB-D-α/β) は本 plan の Phase A 撤退ライン
   (L-Concl-A-α) として伝播。
3. **2026-05-25 Phase 0 新規追加 (scaling defect cleanup)**: Wave 3 second batch
   (commit `0fe2ad4`) で発見された `IsStamToEPIScalingHyp`
   (`Common2026/Shannon/EPIStamToBridge.lean:147-154`) の launder 疑い defect
   (`g1 = 0` 固定で predicate が EPI 結論そのものに reduce、"Csiszár scaling-
   monotonicity step" の構造を carry しない cosmetic wrap) の cleanup を
   prerequisite Phase 0 として追加。既存 Phase 0 (EPIPlumbing 3 件) は
   `Phase 0-Plumbing` にリネーム (本文 touch せず)、新 Phase 0 と独立並列着手
   可。Phase A / B は新 Phase 0 の signature 確定後に restart。推奨案 = **案 1**
   (genuine Csiszár scaling 化、`s ∈ [0,1]` 上の `Monotone gap_s` で carry、
   ~300-500 行)、stop-gap 案 = **案 2** (cosmetic alias rename + docstring
   honest 化、~30 行)。consumer ripple は EPIStamToBridge.lean 内 15+ 件 +
   `EPIStamDeBruijnConclusion.lean:114` docstring 言及 1 件。撤退ライン
   L-Concl-0Sc-α/β/γ を新設。
4. **2026-05-25 Phase 0 closure (案 1 完遂、AntitoneOn 確定)**: orchestrator
   pattern で 4 stage 並列実行 → Phase 0 完了。実装内訳:
   - Stage 1 並列: heat-flow inventory (`docs/shannon/epi-stam-to-conclusion-heatflow-inventory.md`、撤退ライン 3 件全非該当、案 1 確定) + Phase 0-Plumbing 確認 (prior commit `f150cdc`/`5f923e4` で実質完了済)
   - Stage 2 (Phase 0.C-1, commit `0d54e89`): `HeatFlowPath.lean` 新規 6 lemma 132 行 (F.1 全件)、既存 `gaussianConvolution` 1-source 形を 2-source 拡張
   - Stage 2-bis (Phase 0.C-2~5, commit `78cf2ec`): `IsStamToEPIScalingHyp` signature を `∃ Z_X Z_Y, ... ∧ AntitoneOn gap (Set.Icc 0 1)` に refactor + 6 件 retract + 6 件 body rewrite (+252/-163 行)。**`AntitoneOn`** が正しい符号 (inventory §G(b) の `MonotoneOn` 推奨は sign error、Csiszár scaling は gap monotone decreasing で `gap_0 ≥ gap_1 = 0`)。retract 一覧: `isStamToEPIScalingHyp_of_gaussian` / `_of_epi` / `_of_fisherInfoReal_zero` / `isEPIScalingDecomposedPipeline_of_epi` / `_of_gaussian` / `entropy_power_inequality_gaussian_via_scaling_decomposition` (新 signature 下で genuine discharge 不可、consumer 0 件で retract 安全)
   - Stage 4 (commit `2809168`): Independent honesty audit (fresh `general-purpose` subagent、CORE doctrine inline) → Tier 1/2 PASS、Tier 3 questionable で tag `staged(<plan-slug>)` → `suspect(<plan-slug>)` に refine (`audit-tags.md` 語彙: SLUG は plan slug、`staged(WALL)` ではない)。最終 verdict **PASS**。`IsStamToEPILimitHyp` の launder は scaling refactor 効果を **打ち消さない** (consumer で `_h_limit` discard / `_of_scaling` direct path) → Phase 0' 緊急度 **LOW**。
   - **規模実績**: 自作 ~580 行 (見積もり ~265-460 中央 ~350 の +66%、heat-flow path skeleton + signature refactor + 6 file silent verify + audit docstring)、撤退ライン発動 0 件
   - **次段**: Phase A (Stam + de Bruijn 合流 skeleton) は sister 両方 (`epi-stam-discharge-plan` Phase D + `epi-debruijn-integration-plan` Phase D) の出力待ち、Phase 0' (limit launder cleanup) は LOW priority で後日
