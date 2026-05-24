# EPI de Bruijn integration — discharge plan

> **Status**: 未着手 (Phase 設計済、2026-05-24 Wave 2 planner 起草)。本 plan は実装未着手だが
> Phase A–V の設計レベル shape が確定済。
> **Created**: 2026-05-24 (Wave 1.5 item #8、`epi-moonshot-plan` 76 件 slug 分割)。
> **Parent (history)**: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (PASS-THROUGH publish 済、
> 撤退ライン L-EPI2 = de Bruijn integration の genuine discharge を本 sub-plan が担当)。

## Position

- 親 moonshot: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (Phase A-E publish 済、L-EPI2
  hypothesis pass-through)
- 関連 sub-plan:
  - [`epi-stam-discharge-plan.md`](./epi-stam-discharge-plan.md) — L-EPI1 (Stam inequality) sister
  - [`epi-stam-to-conclusion-plan.md`](./epi-stam-to-conclusion-plan.md) — Stam + de Bruijn →
    EPI conclusion 合流部
- 関連 wall plan:
  - [`fisher-info-moonshot-plan.md`](./fisher-info-moonshot-plan.md) (V1) / V2 系
    (V2 経路で `deBruijn_identity_v2` 系が genuine 化途上、4 sub-predicate `@audit:suspect`)
  - [`fisher-info-gaussian-discharge-moonshot-plan.md`](./fisher-info-gaussian-discharge-moonshot-plan.md)

## Motivation

EPI moonshot は L-EPI2 (de Bruijn integration) を `IsDeBruijnIntegrationHypothesis` predicate
hypothesis pass-through 形で publish (`Prop := True` placeholder)。実際の de Bruijn integration の
本格 discharge は本 sub-plan の責務。

`Common2026/Shannon/EPIL3Integration.lean` には EPI L3 integrated pipeline が pass-through
composition で集約されており、**上流 1 件 (`epi_l3_of_integrated_pipeline` 等) が genuine 化
すると全 14 件下流が連鎖閉する構造**になっている (本 sub-plan 担当 14 件 = `EPIL3Integration.lean`
全 audit tags)。

**前提条件 (重要)**: V2 Fisher info 経路 (`FisherInfoV2.lean`, `FisherInfoV2DeBruijn.lean`,
`FisherInfoV2DeBruijnBody.lean`, `FisherInfoV2HeatFlowBody.lean`) は 4 sub-predicate
(`IsHeatSpatialDerivHyp` / `IsHeatTimeDerivHyp` / `IsHeatFlowConvolutionHyp` / `IsIBPHypothesis`)
decomposition は publish 済 (`@audit:suspect(fisher-info-moonshot-plan)`)。本 sub-plan は
**V2 経路の sub-predicate 形を所与として** de Bruijn integration の積分恒等式 `∫_0^∞` 部を
埋める設計。V2 の sub-predicate 自身は `fisher-info-moonshot-plan` 側 (別 wall plan)。並行可。

**`EPIL3Integration.lean` の slug ズレ注記**: 14 件は `@audit:suspect(epi-debruijn-integration-plan)`
だが、predicate `IsEPIL3IntegratedPipeline` (`EPIL3Integration.lean:105`) は **`IsStamInequalityHyp`
+ `IsStamToEPIBridgeHyp`** を bundle しており、`IsDeBruijnIntegrationHyp` 自身は直接消費せず
**`IsStamToEPIBridgeHyp` 経由で間接消費**する設計。これは「Stam → EPI bridge は de Bruijn
integration で構成される」という Cover-Thomas Lemma 17.7.3 の Csiszár scaling argument の
スコープ整合。本 plan は `IsStamToEPIBridgeHyp` discharge を Phase C で扱い (de Bruijn 積分による
gap 単調性)、14 件 closure を達成する。

## Scope

担当 file 群 (W1-B `wave1-plan-sync-epi-bm.md` ベース):

| file | 役割 | suspect 件数 | LoC |
|---|---|---|---|
| `Common2026/Shannon/EPIL3Integration.lean` | EPI L3 integrated pipeline (de Bruijn 積分経路の集約 file) | 14 | 500 |

**合計**: 14 件 suspect (sub-plan 起動時の closure target)。Phase A-D で増分予想 ~400-600 行。

- **Mathlib 壁 4 分類**: (b) 解析 — heat-equation IBP (integration by parts in time) +
  `intervalIntegral.integral_deriv` の unbounded interval 版 (Mathlib `Found 0`) が壁。
  V2 Fisher info の sub-predicate `IsIBPHypothesis` 経由で外出し可。
- **Tier**: 3 (long-term)。`fisher-info-moonshot-plan` V2 経路の進捗に依存。
- **連鎖クローズ**: L3 integration pipeline の上流 1 declaration genuine 化で 14 件一斉 close
  (W1-B 報告書「EPI L3 integrated pipeline の上流 1 件 close → 14 件連鎖閉」)。

## Closure criteria

- 各 declaration から de Bruijn-hypothesis 引数を削除 (genuine discharge)、
  `IsDeBruijnIntegrationHypothesis` (`EntropyPowerInequality.lean:152`、`Prop := True`
  placeholder) を本 plan の `IsDeBruijnIntegrationHyp` (genuine signature,
  `EPIStamDischarge.lean:177`) で置換、最終的には完全 discharge。
- `@audit:suspect(epi-debruijn-integration-plan)` を `@audit:ok` に降格 (14 件)。
- 連鎖効果: `epi-stam-to-conclusion-plan` 経由で EPI conclusion 23 件と連鎖閉。

## ゴール / Approach

### 全体戦略

**de Bruijn identity** (Cover-Thomas Lemma 17.7.2):
```
(d/dt) h(X + √t · Z) = (1/2) · J(X + √t · Z)    where Z ~ 𝒩(0,1), X ⊥ Z
```

**de Bruijn integration identity** (本 sub-plan の核心):
```
h(N(0, Var X + T)) - h(X)
  = ∫_0^T (1/2) · J(X + √t · Z) dt
```

すなわち X と (同分散の) Gaussian の差動エントロピーの差は、heat-flow path に沿った
Fisher information の半分の積分。これを `T → ∞` で取ることで EPI gap の積分表現が得られる。

証明は 4 段:
1. **heat-flow density** (`X_t := X + √t · Z` の密度が heat equation を満たす)
2. **time-derivative of entropy** (de Bruijn identity、V2 deBruijn は既に publish 済)
3. **integration over (0, T)** (FTC 適用、本 sub-plan の主作業)
4. **reduction to L-EPI3 form** (`IsStamToEPIBridgeHyp` の出口形式に整形)

**鍵となる構造選択** (Mathlib-shape-driven):

- **V2 deBruijn の sub-predicate decomposition**: `IsHeatFlowConvolutionHyp` + `IsHeatTimeDerivHyp`
  + `IsHeatSpatialDerivHyp` + `IsIBPHypothesis` で V2 deBruijn identity を組み立てる経路
  (`FisherInfoV2DeBruijn.lean:240` `deBruijn_identity_v2_of_heat_subhyp` 既存)。
- **`gaussianConvolution`** (`FisherInfoV2DeBruijn.lean` 内 abbrev): `P.map (fun ω => X ω + √t · Z ω)`
  の隠蔽。本 plan の全積分恒等式はこれを `t` で動かす形。
- **`intervalIntegral.integral_deriv` 系**: bounded interval 版のみ (`Found 0` for unbounded)、
  unbounded interval (`Set.Ioi 0`) に持ち上げるには tail 解析 (`Filter.Tendsto`) + Lebesgue
  ドミネート + `MeasureTheory.integral_iUnion` 等のパッチワーク。
- **Gaussian saturation case の独立性**: `entropy_power_inequality_gaussian_saturation`
  (`EntropyPowerInequality.lean:226`) は既に full discharge (Gaussian 限定、de Bruijn 不要)。
  本 sub-plan の Phase D は **non-Gaussian general case** の bridge discharge に集中。

### Approach 図

```
[V2 Fisher info sub-predicate decomp (前提)]    [Mathlib 既存 (利用)]
  ──────────────────────────────────              ──────────────────
  IsHeatSpatialDerivHyp                            intervalIntegral.integral_deriv
  IsHeatTimeDerivHyp                               HasDerivAt.integral_*
  IsHeatFlowConvolutionHyp                         tail-vanishing for Gaussian
  IsIBPHypothesis                                  gaussianReal_add_gaussianReal_of_indepFun

       ▲                                                  ▲
       │ V2 deBruijn body discharge (既存)                │ FTC + tail analysis
       │                                                  │
       └──────────────────────┬───────────────────────────┘
                              ▼
              Phase A — heat-flow density + IBP inventory ~30-50 行
                              ▼
              Phase B — time-derivative of entropy (V2 deBruijn wrap) ~150-250 行
                              ▼
              Phase C — integration over (0, ∞) (FTC + tail) ~150-250 行
                              ▼
              Phase D — reduction to L-EPI3 form (`IsStamToEPIBridgeHyp` 入口) ~50-80 行
                              ▼
              Phase V — verify + Common2026.lean 編入
                              ▼
              de Bruijn integration (genuine) → epi-stam-to-conclusion 入口
```

### 段階的 ship 設計 (Tier 0 / 1 / 2)

- **Tier 0** (Phase A + B 一部): V2 sub-predicate decomp の wrap + de Bruijn identity の
  family-level lift。partial publish 価値あり (`IsRegularDeBruijnHypV2` を `EPIL3Integration.lean`
  に編入)。
- **Tier 1** (Phase A + B + C): bounded interval `(0, T)` 上での integration identity 完成。
  `IsDeBruijnIntegrationHyp X Z P T` を bounded `T` で genuine discharge、`T → ∞` 部だけ残す。
- **Tier 2** (Phase A + B + C + D): unbounded interval `(0, ∞)` + L-EPI3 form 出口。
  `IsStamToEPIBridgeHyp` への接続完成、14 件全 closure。

### 規模見積もり

| Phase | 自作要素 | 想定行数 |
|---|---|---|
| A | heat-flow density + IBP inventory + V2 sub-predicate wrap | ~30-50 |
| B | time-derivative of entropy (V2 deBruijn を family-level に lift) | ~150-250 |
| C | integration over `(0, T)` → `(0, ∞)` (FTC + tail) | ~150-250 |
| D | reduction to L-EPI3 form (`IsStamToEPIBridgeHyp` 入口) | ~50-80 |
| V | verify + Common2026.lean 編入 + roadmap | ~5-10 |
| **合計** | | **~385-640** |

中央予測 **~500 行**。`EPIL3Integration.lean` は既に 500 行あるので、合計 **~900-1140 行** 規模
で着地予想。

---

## 進捗

- [ ] Phase A — heat-flow density + IBP inventory 📋
- [ ] Phase B — time-derivative of entropy (V2 deBruijn family-level lift) 📋
- [ ] Phase C — integration over `(0, T)` → `(0, ∞)` 📋
- [ ] Phase D — reduction to L-EPI3 form 📋
- [ ] Phase V — verify (`lake env lean ...`) + Common2026.lean 編入 📋

proof-log: yes (各 Phase 完了時に `docs/shannon/proof-log-epi-debruijn-integration-phase-*.md` を残す)

---

## Phase A — heat-flow density + IBP inventory 📋

### スコープ

Mathlib + V2 Fisher info 経路の在庫確認:

- **Mathlib `MeasureTheory.gaussianPdfReal`** (Gaussian density verbatim signature) —
  既存 `FisherInfoV2.lean` で利用済、本 plan は再利用
- **Mathlib `Convolution`** — `Mathlib.Analysis.Convolution` の verbatim signature 確認、
  特に `convolution_assoc` / `Differentiable.convolution` 系の有無
- **V2 sub-predicate** (`FisherInfoV2DeBruijnBody.lean:240` `deBruijn_identity_v2_of_heat_subhyp`
  経路): `IsHeatSpatialDerivHyp` / `IsHeatTimeDerivHyp` / `IsHeatFlowConvolutionHyp` /
  `IsIBPHypothesis` の signature を本 plan で wrap 可能か確認
- **Mathlib `intervalIntegral`**: bounded vs unbounded interval API の boundary 整理

### Approach

Phase A は本格コードを書かず inventory 文書 (`epi-debruijn-integration-mathlib-inventory.md` 新規)
を作る (orchestrator に `mathlib-inventory` agent を起動する依頼候補)。
本 plan の Phase B 以降に必要な Mathlib lemma の verbatim signature を `[...]` typeclass
prerequisites verbatim で記録 (CLAUDE.md `Subagent Inventory of Mathlib Lemmas` 規律)。

### Done 条件

- `docs/shannon/epi-debruijn-integration-mathlib-inventory.md` 新規 (~200-400 行)
- V2 sub-predicate decomp の本 plan re-export 経路が明確化
- Phase B/C の各補題の Mathlib 起源が確定 (Phase B 着手後に "lemma X が見つからない" で逆戻り
  しないため)

### ステップ

- [ ] **A-1**: Mathlib `Mathlib.Analysis.Convolution` 系の verbatim signature 採取
      (`Differentiable.convolution`, `convolution_assoc`, `convolution_comm` 等)
- [ ] **A-2**: V2 sub-predicate (`FisherInfoV2DeBruijnBody.lean:140-180` 推定) の signature
      verbatim 採取、本 plan で wrap する形式の整理
- [ ] **A-3**: Mathlib `intervalIntegral.integral_deriv_eq_sub` / `intervalIntegral.integral_*`
      系の verbatim signature 採取 (bounded interval 用)
- [ ] **A-4**: Mathlib `MeasureTheory.integral_iUnion_disjoint_of_summable` 等の
      unbounded interval 持ち上げ API 確認
- [ ] **A-5**: heat-equation の Mathlib API 在庫 (`Mathlib.Analysis.PDE.*` があるか確認、なければ
      self-contained heat kernel 計算が必要)

### 撤退ライン

- **L-DB-A-α** (許容): Mathlib `Convolution` API が薄く `Differentiable.convolution` が
  見つからない場合 → V2 `IsHeatFlowConvolutionHyp` (sub-predicate) を本 plan で再利用、
  独立した self-contained 補題を書かない。これは既存 V2 経路の sub-predicate decomposition
  を最大限活用する設計判断。

---

## Phase B — time-derivative of entropy (V2 deBruijn family-level lift) 📋

### スコープ

V2 `deBruijn_identity_v2` (`FisherInfoV2DeBruijn.lean:262`、`HasDerivAt` 形 publish 済) を
**`IsRegularDeBruijnHypV2 X Z P t` を `∀ t > 0` に lift** した family 形に持ち上げる。
これは本 sub-plan が直接消費する `IsDeBruijnRegularityHyp X Z P` (`EPIStamDischarge.lean:143`)
の構築。

### Approach

V2 deBruijn identity は per-time-point の `HasDerivAt`:
```
HasDerivAt (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
           ((1/2) * fisherInfoOfDensityReal h_reg.density_t)
           t
```

これを **family-level** に lift し:
1. `IsDeBruijnRegularityHyp X Z P` (`EPIStamDischarge.lean:143-158`) の `reg_at : ∀ t > 0,
   IsRegularDeBruijnHypV2 X Z P t` を構築
2. `integrable_deriv` (derivative の `(0, ∞)` 上 integrable 条件) を `density_path : ℝ → ℝ → ℝ`
   形で構築

**Gaussian 限定**: `IsRegularDeBruijnHypV2_of_gaussian` (Gaussian 限定で hypothesis-free 構築可、
既存 `deBruijn_identity_v2_gaussian` 経路) を本 plan で publish。一般 `X` の family 形は
honest hypothesis `IsHeatFlowFamilyHyp X Z P` で外出し (Phase D 撤退ライン)。

### Done 条件

- `IsDeBruijnRegularityHyp X Z P` を Gaussian 限定で genuine 構築 (`_of_gaussian` wrapper)
- `density_path` の存在条件を明確化 (Gaussian なら `density_path t = gaussianPDFReal m (v+t)`)
- `IsHeatFlowFamilyHyp X Z P` honest hypothesis 形 (一般 `X` の family lift) を導入、
  `Prop := True` 禁止、本物の family-level regularity 仮定

### ステップ

- [ ] **B-1**: `density_path_gaussian` の構築:
  ```
  noncomputable def density_path_gaussian (m : ℝ) (v : ℝ≥0) : ℝ → ℝ → ℝ :=
    fun t x => gaussianPDFReal m ⟨v + t, _⟩ x
  ```
  ~10-15 行
- [ ] **B-2**: family-level regularity `∀ t > 0, IsRegularDeBruijnHypV2 X Z P t` の Gaussian
      限定 構築:
  ~50-80 行
- [ ] **B-3**: `integrable_deriv` Gaussian case (`∫_{(0,∞)} (1/(v+t)) dt = ∞` で divergent だが
      `h(N(0, v+t)) - h(X)` が finite limit を持つ条件で逃げる、Gaussian の場合は厳密):
  ~30-50 行
- [ ] **B-4**: `IsDeBruijnRegularityHyp_of_gaussian` の完成 (Gaussian 限定 hypothesis-free):
  ~30-50 行
- [ ] **B-5**: 一般 `X` 用 `IsHeatFlowFamilyHyp X Z P` honest hypothesis 形の導入
      (Phase D で discharge、本 phase では signature のみ):
  ~30-50 行

### 撤退ライン

- **L-DB-B-α** (許容): heat-flow path の family-level regularity が `Convolution` API 不足で
  組めない場合 → V2 `IsHeatFlowConvolutionHyp X Z P p` (sub-predicate、既存) を hypothesis
  として残す **honest pass-through**。docstring で "load-bearing on V2 sub-predicate" 明示。
- **L-DB-B-β** (許容): time-derivative の `HasDerivAt` の `t` 連続性が壁の場合
  (`IsHeatTimeDerivHyp p Δp` で外出し、既存 V2 sub-predicate)。

---

## Phase C — integration over (0, T) → (0, ∞) 📋

### スコープ

**本 sub-plan の核心 Phase**。`IsDeBruijnIntegrationHyp X Z P T`
(`EPIStamDischarge.lean:177-186`、V2 keyed genuine signature) を完成:

```
h_target - h_X = ∫_(0,T) (1/2) * fisherInfoOfDensityReal (fPath t) dt
```

**Step 1**: bounded `T` で FTC 適用:
```
h(N(0, Var X + T)) - h(X) = ∫_0^T (d/dt) h(X + √t·Z) dt = ∫_0^T (1/2) J(X + √t·Z) dt
```
Mathlib `intervalIntegral.integral_deriv_eq_sub` (有界 interval) を適用、
`HasDerivAt` は Phase B の family-level lift から供給。

**Step 2**: `T → ∞` の極限を取る (tail analysis):
```
∫_0^∞ (1/2) J(X_t) dt = h(N(0, ∞)) - h(X) = ∞ - h(X) = ∞    -- divergent
```
これは textbook では「`T → ∞` で `J(X+√T·Z) → 0` だが ∫ J(X_t) dt 自体は発散」とされており、
**EPI 経由で意味を持つのは gap 形** (`g(t) := h_target(t) - h(X+Y_t)` 等の差)。
本 phase では **bounded T 形を完成 + gap 形への bridge** を準備。

### Approach

`intervalIntegral.integral_deriv_eq_sub` の verbatim:
```lean
theorem intervalIntegral.integral_deriv_eq_sub {f : ℝ → E}
    (h_diff : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (h_int : IntervalIntegrable f' volume a b) :
    ∫ x in a..b, f' x = f b - f a
```

Step-by-step:
1. `f t := differentialEntropy (P.map (gaussianConvolution X Z t))`
2. `f' t := (1/2) * fisherInfoOfDensityReal (density_path t)` (Phase B から)
3. `f T - f 0 = ∫_0^T f' t dt`
4. `f 0 = differentialEntropy (P.map X)` (`√0 · Z = 0` で `gaussianConvolution X Z 0 = X`)
5. `f T = differentialEntropy (P.map (X + √T·Z))` = Gaussian 限定なら closed form

`T → ∞` への持ち上げは:
- Mathlib `MeasureTheory.integral_iUnion_eq_lim` 等で `(0, T) → (0, ∞)` の monotone convergence
- tail analysis: Gaussian 限定で `lim_{T→∞} h(X+√T·Z) = ∞` を確認、gap 形でのみ意味
- gap 形 (`epi-stam-to-conclusion-plan` 側で扱う) への bridge を Phase D で

### Done 条件

- `IsDeBruijnIntegrationHyp X Z P T` を bounded `T` で genuine discharge (Gaussian 限定)
- `T → ∞` の極限 bridge は honest hypothesis `IsDeBruijnTailHyp` で外出し (Phase D で扱う)
- `EPIL3Integration.lean` 14 件のうち bounded-T part を `@audit:ok` に降格

### ステップ

- [ ] **C-1**: bounded interval FTC 適用 (`intervalIntegral.integral_deriv_eq_sub` 経由):
  ~50-80 行
- [ ] **C-2**: `f 0 = differentialEntropy (P.map X)` boundary case (`√0 · Z = 0`、
      `gaussianConvolution X Z 0 = X` を `Real.sqrt_zero` で展開):
  ~20-30 行
- [ ] **C-3**: `f T` の Gaussian closed form (Gaussian X 限定で
      `differentialEntropy (P.map (X + √T·Z)) = (1/2) log (2πe (v + T))`):
  ~30-50 行
- [ ] **C-4**: `IsDeBruijnIntegrationHyp X Z P T` の bounded T genuine discharge
      (Gaussian 限定):
  ~30-50 行
- [ ] **C-5**: 一般 `X` 用の honest hypothesis `IsDeBruijnTailHyp X Z P` 導入
      (`T → ∞` 部分、Phase D で扱う):
  ~20-40 行

### 撤退ライン

- **L-DB-C-α** (許容): IBP (integration by parts in time) が Mathlib gap → V2 sub-predicate
  `IsIBPHypothesis X Z P p t` (既存) で外出し、本 plan は signature pass-through。
- **L-DB-C-β** (許容): `T → ∞` の極限 (tail analysis) が non-Gaussian で破綻 → `IsDeBruijnTailHyp`
  honest hypothesis で外出し、Phase D で扱う。Gaussian 限定 closure は許容。

---

## Phase D — reduction to L-EPI3 form (`IsStamToEPIBridgeHyp` 入口) 📋

### スコープ

Phase C の出力 (`IsDeBruijnIntegrationHyp` bounded T discharge) を **`IsStamToEPIBridgeHyp`**
(`EPIStamDischarge.lean:304`、`IsStamInequalityHyp → IsEntropyPowerInequalityHypothesis`、
Csiszár scaling) **の入口**として整形。これが `EPIL3Integration.lean` の
`IsEPIL3IntegratedPipeline` (`:105`) が要求する形。

### Approach

`IsStamToEPIBridgeHyp` の中身 (Csiszár scaling argument):
```
Given Stam: 1/J(X+Y) ≥ 1/J(X) + 1/J(Y)
Apply de Bruijn integration along heat-flow path,
Use scaling X → λ·X, Y → (1-λ)·Y, integrate λ ∈ [0,1],
=> exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y)) = EPI
```

具体的には:
1. `g(t) := entropyPower (P.map (X+Y+√t·Z)) - entropyPower (P.map (X+√t·Z)) - entropyPower (P.map (Y+√t·Z))`
2. de Bruijn integration で `g'(t) = -(1/2) · scaling factor` を計算 (`g'(t) ≤ 0` を Stam から)
3. `g(∞) = 0` (Gaussian limit、`exp(2 h(N_∞)) = 2πe · σ²_∞` の scaling)
4. `g(0) ≤ g(∞) = 0` → EPI gap ≤ 0 → EPI 結論

これは `epi-stam-to-conclusion-plan` (sister) の Phase A と密接、本 sub-plan は **de Bruijn
integration 部の出口 (`IsDeBruijnIntegrationHyp` を genuine 化 → `IsStamToEPIBridgeHyp` に渡す
形式に整形)** に集中、Csiszár scaling 全体は sister 担当。

### Done 条件

- `IsDeBruijnIntegrationHypothesis` (`EntropyPowerInequality.lean:152`、`Prop := True`
  placeholder) を本 plan の `IsDeBruijnIntegrationHyp` で完全置換、または bridge
  `isDeBruijnIntegrationHypothesis_of_deBruijnIntegrationHyp` を publish
- `EPIL3Integration.lean` 14 件全て `@audit:ok` 降格
- `IsStamToEPIBridgeHyp` への入口形式が整い、sister sub-plan `epi-stam-to-conclusion-plan`
  の Phase A 入口に渡せる

### ステップ

- [ ] **D-1**: `gap` 関数 `g(t)` の定義 + 基本性質:
  ~30-50 行
- [ ] **D-2**: Phase C 出力 (`IsDeBruijnIntegrationHyp` bounded T) を `g(t)` の積分表現に
      reshape:
  ~20-30 行
- [ ] **D-3**: `EPIL3Integration.lean` 14 件の `@audit:suspect` を `@audit:ok` に降格:
  ~10-20 行 (主に rewrite + bridge 適用)
- [ ] **D-4**: `IsStamToEPIBridgeHyp` への入口 lemma を sister sub-plan に export:
  ~10-20 行

### 撤退ライン

- **L-DB-D-α** (許容、Phase C/B 撤退ライン依存): Phase C-β (tail analysis) が発動した場合、
  `g(∞) = 0` の証明が `IsDeBruijnTailHyp` honest hypothesis 経由になる。これは Csiszár scaling
  全体の closure を `epi-stam-to-conclusion-plan` の Phase A 撤退ラインに依存させる。
- **L-DB-D-β** (許容): `g'(t) ≤ 0` の証明 (Stam → 単調性) は sister sub-plan
  (`epi-stam-discharge-plan`) の Phase D 出力に依存。並行作業の場合は本 plan の Phase D は
  Stam discharge plan 完了待ち。

---

## Phase V — verify + Common2026.lean 編入 📋

### スコープ

- `lake env lean Common2026/Shannon/EPIL3Integration.lean` clean (0 errors / 0 sorry /
  警告最小限)
- `Common2026.lean` import 確認 (既に import 済み)
- `docs/textbook-roadmap.md` T2-D de Bruijn 行を `[x]` に
- `docs/shannon/epi-moonshot-plan.md` の split-into 注記を更新 (14 件 closure 完了)

### Done 条件

- `EPIL3Integration.lean` `lake env lean` clean
- 14 件 `@audit:suspect(epi-debruijn-integration-plan)` → `@audit:ok` 降格完了
- sister sub-plan `epi-stam-to-conclusion-plan` 側の Phase A 入口に bridge 完成

---

## 撤退ライン総覧 (honest 限定)

| slug | Phase | 内容 | hypothesis 名 (例) | 解除条件 |
|---|---|---|---|---|
| L-DB-A-α | A | `Convolution` API 不足時、V2 sub-predicate に丸投げ | `IsHeatFlowConvolutionHyp` (V2 既存) | Mathlib `Differentiable.convolution` PR |
| L-DB-B-α | B | family-level regularity の `Convolution` 不足 | `IsHeatFlowConvolutionHyp` (V2 既存) | 上と同じ |
| L-DB-B-β | B | time-derivative の `HasDerivAt` 連続性が壁 | `IsHeatTimeDerivHyp p Δp` (V2 既存) | Mathlib heat-equation PR |
| L-DB-C-α | C | IBP in time の Mathlib gap | `IsIBPHypothesis X Z P p t` (V2 既存) | Mathlib IBP for time PR |
| L-DB-C-β | C | `T → ∞` tail analysis (non-Gaussian) | `IsDeBruijnTailHyp X Z P` (新規 honest) | Gaussian 限定 closure or Cover-Thomas tail bound |
| L-DB-D-α | D | C-β 発動時の Csiszár scaling closure 依存 | sister `epi-stam-to-conclusion-plan` Phase A 撤退ライン | sister 完了 |
| L-DB-D-β | D | Stam (sister) 完了待ち | sister `epi-stam-discharge-plan` Phase D 出力 | sister 完了 |

**全撤退ライン共通規律**:
- **`Prop := True` placeholder 禁止** (現状 `IsDeBruijnIntegrationHypothesis` が
  `:= True`、Phase D で **必ず** 実 Prop 化 or bridge で置換)
- **結論型 ≡ 仮説型 + `body := h` (循環) 禁止**
- **load-bearing hypothesis を完成と称する name laundering 禁止**
- 撤退ライン発動時は docstring で「NOT a discharge / load-bearing on <V2 sub-predicate or
  honest hypothesis>」を必ず明示

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-05-24 Wave 2 planner Phase 起草**: stub plan (68 行、Phase 設計未起草) に Phase
   A-V を埋め込み。V2 sub-predicate decomposition (`IsHeatSpatialDerivHyp` /
   `IsHeatTimeDerivHyp` / `IsHeatFlowConvolutionHyp` / `IsIBPHypothesis`) が既に publish 済
   (`@audit:suspect(fisher-info-moonshot-plan)` 状態) を確認 → 本 plan は V2 sub-predicate
   を所与として積分恒等式部に集中。V2 Fisher info 経路の closure は本 plan の前提として明記、
   並行可。
2. **2026-05-24 slug ズレ注記**: `EPIL3Integration.lean` 14 件は
   `@audit:suspect(epi-debruijn-integration-plan)` だが、predicate
   `IsEPIL3IntegratedPipeline` は **`IsStamInequalityHyp` + `IsStamToEPIBridgeHyp`**
   bundle で `IsDeBruijnIntegrationHyp` を直接消費せず **`IsStamToEPIBridgeHyp` 経由で間接消費**
   する設計と確定。これは「Stam → EPI bridge は de Bruijn integration で構成される」という
   Cover-Thomas Lemma 17.7.3 の Csiszár scaling argument のスコープ整合であり、slug 設計は維持
   (Phase D で `IsStamToEPIBridgeHyp` の de Bruijn 部入口を担当)。
