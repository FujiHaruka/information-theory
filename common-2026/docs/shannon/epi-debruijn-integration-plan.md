# EPI de Bruijn integration — discharge plan

> **Status**: Tier 0 + Tier 1 (Gaussian-only) 着地 (2026-05-25 Wave 3 second batch,
> commit `0fe2ad4`)。Phase A inventory + Phase B/C の Gaussian 枝が landing 済、Phase D
> (`IsStamToEPIBridgeHyp` 入口) + 一般 `X` への拡張は未着手。**同 session で upstream
> defect 3 件発見** → §「Upstream defects (2026-05-25)」参照。Tier 2 着手は defect
> 修正完了後に restart。
> **Created**: 2026-05-24 (Wave 1.5 item #8、`epi-moonshot-plan` 76 件 slug 分割)。
> **Parent (history)**: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (PASS-THROUGH publish 済、
> 撤退ライン L-EPI2 = de Bruijn integration の genuine discharge を本 sub-plan が担当)。
> **Mathlib inventory**: [`epi-debruijn-integration-mathlib-inventory.md`](./epi-debruijn-integration-mathlib-inventory.md)
> (Wave 3 first batch 起草、Phase A 在庫 ~294 行、Phase B-C 自作必須範囲明示)。

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

- [x] Phase A — heat-flow density + IBP inventory ✅ (Wave 3 first batch, inventory file `epi-debruijn-integration-mathlib-inventory.md` 起草、~294 行)
- [x] Phase B — time-derivative of entropy (V2 deBruijn family-level lift) ✅ Gaussian 限定 (Wave 3 second batch, commit `0fe2ad4`、`EPIL3Integration.lean` +467 行) — 一般 `X` 拡張は load-bearing hypothesis `IsHeatFlowFamilyHyp` (`@audit:staged(epi-heat-flow-family-regularity)`, `EPIL3Integration.lean:572`) 経由で外出し
- [x] Phase C — integration over `(0, T)` ✅ Gaussian 限定 bounded-T (Wave 3 second batch); `(0, T) → (0, ∞)` tail lift は Wave 3 third batch で `IsDeBruijnTailHyp` 導入を試みたが、同 session 独立 audit が DEFECT verdict (`defect(epi-debruijn-tail-vacuous-and-empty)`) を出し **retract**。tail-analysis externalization は plan-level pending task (Phase C-5、`h_inf : EReal` lift + `Z_law` 追加 refactor 待ち、§「Upstream defects」Defect #3)
- [ ] Phase D — reduction to L-EPI3 form 📋 (defect 修正完了後に着手)
- [ ] Phase V — verify (`lake env lean ...`) + Common2026.lean 編入 🚧 (`Common2026.lean` 編入は完了、14 件 `@audit:suspect` 降格は Phase D 完了待ち)

proof-log: yes (各 Phase 完了時に `docs/shannon/proof-log-epi-debruijn-integration-phase-*.md` を残す)

### Tier 0/1 着地サマリ (2026-05-25 Wave 3 second batch, commit `0fe2ad4`)

- **Tier 0** (V2 sub-predicate wrap + de Bruijn identity の family-level lift): 達成
- **Tier 1** (bounded `T` integration identity, Gaussian 限定): 達成
- **Tier 2** (unbounded `(0, ∞)` + L-EPI3 form 出口、14 件全 closure): 未達 (defect 修正後 restart)
- **新規 staged predicate**: `IsHeatFlowFamilyHyp` (1 件、`@audit:staged(epi-heat-flow-family-regularity)` 維持)
  - `IsDeBruijnTailHyp` (Wave 3 third batch で signature 修正試行) は同 session closure 独立 audit で **DEFECT verdict + retract**。詳細 §「Upstream defects」Defect #3

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
- `T → ∞` の極限 bridge は元 `IsDeBruijnTailHyp` で外出し予定だったが Wave 3 third batch closure audit が retract、Phase C-5 再設計 (EReal lift + Z_law 追加) 待ち
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
      (`T → ∞` 部分、Phase D で扱う) — **Wave 3 third batch で試行、独立 audit が
      DEFECT verdict (vacuous-bypass via `Z = 0` + `h_inf : ℝ` で semantically
      empty) を出し retract**。再導入は `h_inf : EReal` (or `ℝ≥0∞`) lift +
      `Z_law : P.map Z = gaussianReal 0 1` field 追加が前提:
  ~40-60 行 (元見積 +20、EReal lift API ripple 込み)

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
  `g(∞) = 0` の証明は元 `IsDeBruijnTailHyp` honest hypothesis 経由を想定していたが、
  当該 predicate は Wave 3 third batch closure audit で retract 済 — 再導入 (EReal lift +
  Z_law) 完了まで `g(∞) = 0` は Gaussian 限定 closure or Cover-Thomas tail bound 経由
  で迂回する必要。Csiszár scaling 全体の closure は依然 `epi-stam-to-conclusion-plan`
  の Phase A 撤退ラインに依存。
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

## Upstream defects discovered 2026-05-25 (Wave 3 second batch)

実装 session (commit `0fe2ad4`) と直後の独立 audit で、本 plan の核心 hypothesis 3 件が
**predicate signature レベルで偽** (degenerate witness で trivially 満たされる) と判明。
すべて `@audit:defect(false-statement)` / `@audit:defect(degenerate)` 付与済、修正は
Wave 3 third batch で並行進行中。Phase B/C の Gaussian 着地は影響を受けないが、
**Tier 2 (一般 `X` への拡張) は本 defect 修正完了が前提**。

### Defect #1 — `IsDeBruijnIntegrationHyp` (Phase C の核心 predicate)

- **File:line**: `Common2026/Shannon/EPIStamDischarge.lean:177`
- **タグ**: `@audit:defect(false-statement)` `@audit:suspect(epi-debruijn-integration-plan)`
- **旧 signature** (要約):
  ```
  ∀ (h_X h_target : ℝ) (fPath : ℝ → ℝ → ℝ), ...
  ```
  (`∀ fPath` で任意の path family に対し integration identity を主張)
- **退化機構**: `fisherInfoOfMeasureV2 _ f = fisherInfoOfDensity f` は labelling
  arg `μ` を無視する **defeq** (`FisherInfoV2.lean:100`)。さらに `fisherInfoOfDensity 0 = 0`
  なので `fPath := fun _ _ ↦ 0` を選ぶと RHS integrand が恒等 0、LHS も自明な
  Gaussian saturation で trivially 成立 → predicate 偽。
- **修正方針**: `∀ fPath` → `∃ fPath` (存在量化)。これにより heat-flow path が
  存在することの主張に変わり、退化 path での trivial 成立を排除。
- **修正主体**: Wave 3 third batch、Agent A1 (進行中)

### Defect #2 — `IsDeBruijnRegularityHyp.integrable_deriv` (Phase B の出力)

- **File:line**: `Common2026/Shannon/EPIStamDischarge.lean:143`
- **タグ**: `@audit:defect(false-statement)` `@audit:suspect(epi-debruijn-integration-plan)`
- **旧 field**:
  ```
  Integrable f' (volume.restrict (Set.Ioi 0))
  ```
- **退化機構**: Gaussian でも heat-flow Fisher info derivative は `f'(t) = 1/(2(v+t))`
  形を持ち、これを `Set.Ioi 0` (unbounded) で integrate すると logarithmically 発散 →
  `HasFiniteIntegral` 条件が **Gaussian でも満たされない**。すなわち predicate が要求する
  field が「Gaussian も含めて誰も供給できない」状態、形式上は偽でなくとも witness 不在で
  load-bearing として無効。
- **修正方針**: `IntervalIntegrable f' volume 0 T` (bounded-T window)。Phase C bounded-T
  FTC と整合し、Gaussian で実際に充足可能になる。
- **修正主体**: Wave 3 third batch、Agent A1 (進行中)

### Defect #3 — `IsDeBruijnTailHyp` (Phase C-5 honest hypothesis) — **retracted**

- **File:line**: 元 `Common2026/Shannon/EPIL3Integration.lean:589` (現在は撤回コメント)
- **タグ**: 元 `@audit:staged(epi-debruijn-tail)` + `@audit:defect(degenerate)` →
  Wave 3 third batch closure audit verdict `@audit:defect(epi-debruijn-tail-vacuous-and-empty)` → predicate 自体を retract
- **初期 defect (Wave 3 second batch 認定)**: 旧 field 構成では
  `h_inf := h_X` + `fPath_tail := fun _ _ ↦ 0` で trivially 充足。LHS は `0`、
  RHS は `fisherInfoOfDensity 0 = 0` (`FisherInfoV2.lean:100`) により `0` となるため
  `tail_eq` が自明成立 → load-bearing として無効。
- **第一次修正試行 (Wave 3 third batch, Agent A2)**: `Filter.Tendsto (fun T => h(X+√T·Z)) atTop (𝓝 h_inf)` field を追加して `h_inf` を path の真の極限に縛ろうとした。
- **closure audit DEFECT verdict (2 重 defect)**:
  1. **Vacuous-bypass channel が依然 open**: structure に `Z_law : P.map Z = gaussianReal 0 1` が無いため、`Z := fun _ ↦ 0` を選ぶと `gaussianConvolution X Z T = X` pointwise → heat-flow entropy は定数関数 → `tail_limit` は `tendsto_const_nhds` で trivial 成立、`fPath_tail := 0` も collapse → 退化 instance survive。
  2. **Semantically empty even after `Z_law`**: `Z ∼ 𝒩(0,1)` 仮定下では `h(X+√T·Z) → +∞` (Gaussian sub-entropy 下界 `(1/2)log(2πe·T)`) → `Tendsto _ atTop (nhds h_inf)` for `h_inf : ℝ` は essentially uninhabited → predicate ≡ `False` → 任意 consumer が vacuously OK で discharge content ゼロ。
- **closure 対応**: predicate 撤回。consumer 0 件 (§12 docstring 言及のみ) で Lean impact 無し。`EPIL3Integration.lean` 該当領域に retraction コメント残置 (`(retracted 2026-05-25, Wave 3 third batch independent audit)`)。
- **再導入条件 (将来 Phase C-5 honest re-introduction)**:
  - `h_inf : ℝ` → `h_inf : EReal` (or `ℝ≥0∞`) lift で `+∞` 極限を表現可能化
  - `Z_law : P.map Z = gaussianReal 0 1` field 追加で `Z = 0` bypass 封鎖
  - 上記 2 件揃ったら独立 audit 再受検

### 共通機構 — defect 根源

3 件すべてが **`fisherInfoOfDensity 0 = 0`** (`FisherInfoV2.lean:100`) を退化機構として
利用している。**同 session 内で 2 件独立 defect (#1 と #3) がこの 1 機構から生まれた**
→ 設計レベルの脆弱性。Phase D / Tier 2 restart 時の新規 predicate 設計では下記
checklist を必ず適用する。

---

## Defect prevention checklist (本 plan 専用)

V2 Fisher info 経路を消費する predicate を本 plan で **新規導入** / **signature
更新** する際、以下を必ず手元で検算してから commit:

1. **`fisherInfoOfDensity 0 = 0` 退化 instance 検算**
   - 新規 predicate の RHS / integrand に `fisherInfoOfMeasureV2 _ f` または
     `fisherInfoOfDensity f` が出現する場合、`f := 0` (恒等 0 density) と退化 path
     (`fPath := fun _ _ ↦ 0` 等) を代入して predicate が trivially 成立しないか
     紙の上で確認。trivially 成立する場合は predicate 偽 → signature 変更必須。
2. **V2 API の defeq cosmetic illusion 警告**
   - `fisherInfoOfMeasureV2 μ f` は `μ` arg を **無視する defeq** (`FisherInfoV2.lean:100`、
     EPI-DB agent Wave 3 second batch 気づき)。「measure-keyed」claim は cosmetic、
     `μ` を変えても結論は変わらない。`∀ μ` 量化や `μ` 依存 RHS の設計は意味を持たないので
     `μ` を arg から除くか、V2 ではなく measure-aware な別 API を選ぶ。
3. **`∀ vs ∃` パリティ確認**
   - integration identity 系 predicate で `∀ fPath, ... fPath ...` 形 (path-universal)
     を採用する場合、退化 path で trivially 成立しないか必ず確認。退化耐性のない場合は
     `∃ fPath` (path-existential) に切替。
4. **限界条件の Mathlib 充足可能性チェック**
   - `Integrable` / `HasFiniteIntegral` を field に置く場合、Gaussian instance でも
     実際に充足できるか紙で確認 (defect #2 のように Gaussian でも発散するなら predicate
     witness 不在で load-bearing 無効)。bounded-T 形に逃げる選択肢を常に検討。

これら 4 項目を満たさない predicate を本 plan が commit した場合、
**独立 audit subagent が catch する** が、設計段階で防げるなら防ぐ (audit は二段目、
inline 防御が一段目、CLAUDE.md 「検証の誠実性」)。

---

## 撤退ライン総覧 (honest 限定)

| slug | Phase | 内容 | hypothesis 名 (例) | 解除条件 |
|---|---|---|---|---|
| L-DB-A-α | A | `Convolution` API 不足時、V2 sub-predicate に丸投げ | `IsHeatFlowConvolutionHyp` (V2 既存) | Mathlib `Differentiable.convolution` PR |
| L-DB-B-α | B | family-level regularity の `Convolution` 不足 | `IsHeatFlowConvolutionHyp` (V2 既存) | 上と同じ |
| L-DB-B-β | B | time-derivative の `HasDerivAt` 連続性が壁 | `IsHeatTimeDerivHyp p Δp` (V2 既存) | Mathlib heat-equation PR |
| L-DB-C-α | C | IBP in time の Mathlib gap | `IsIBPHypothesis X Z P p t` (V2 既存) | Mathlib IBP for time PR |
| L-DB-C-β | C | `T → ∞` tail analysis (non-Gaussian) | ~~`IsDeBruijnTailHyp X Z P` (新規 honest)~~ — Wave 3 third batch closure audit が retract、Phase C-5 再設計 (EReal lift + Z_law) 待ち | Gaussian 限定 closure or Cover-Thomas tail bound or `EReal` lift refactor |
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
3. **2026-05-25 Wave 3 first batch — Phase A inventory 完了**: `mathlib-inventory` agent
   起動で `epi-debruijn-integration-mathlib-inventory.md` (~294 行) 起草。Phase A の Done 条件
   (`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` の verbatim signature、V2
   sub-predicate decomp の本 plan re-export 経路、Mathlib `Convolution` API 在庫) を満たす。
   Phase B/C 着手の前提整備完了。
4. **2026-05-25 Wave 3 second batch — Tier 0/1 (Gaussian-only) landing** (commit `0fe2ad4`):
   `EPIL3Integration.lean` に +467 行、Phase B (V2 deBruijn の family-level lift) + Phase C
   (bounded-T FTC) の Gaussian 枝を着地。一般 `X` 拡張は load-bearing hypothesis
   `IsHeatFlowFamilyHyp` (`@audit:staged(epi-heat-flow-family-regularity)`) で外出し、
   `T → ∞` lift は honest hypothesis `IsDeBruijnTailHyp` (`@audit:staged(epi-debruijn-tail)`)
   で外出し。**新規 staged predicate 2 件**は session 内に独立 audit subagent
   (`honesty-auditor`) で検証 → 後者は `@audit:defect(degenerate)` 認定 (退化機構: `h_inf := h_X`
   + `fPath_tail := 0` で trivial 成立)。
5. **2026-05-25 同 session — upstream defect 3 件発見** (§「Upstream defects」詳細):
   `IsDeBruijnIntegrationHyp` (Phase C 核心) + `IsDeBruijnRegularityHyp.integrable_deriv`
   (Phase B 出力) + `IsDeBruijnTailHyp` (Phase C-5) の 3 件が **predicate signature レベルで
   false / degenerate**。共通根源: `fisherInfoOfDensity 0 = 0` 退化機構。修正は Wave 3
   third batch で並行進行 (Agent A1 = #1+#2、Agent A2 = #3)。**Phase D 着手 + Tier 2 restart
   は本 defect 修正完了が前提** — 修正完了 commit を待って Phase B/C を真の体で再起動する。
6. **2026-05-25 V2 API 設計上の注記**: EPI-DB agent が同 session で
   `fisherInfoOfMeasureV2 _μ f = fisherInfoOfDensity f` (`μ` arg を無視する **defeq**) を
   再確認。V2 API の「measure-keyed」claim は **cosmetic illusion**。将来 V2 → V3
   refactor 候補として記録 (本 plan のスコープ外、`fisher-info-moonshot-plan` 側の判断
   ログに転記推奨)。Defect prevention checklist 項目 2 で本 plan 内の予防策化済。
7. **2026-05-25 Wave 3 third batch closure audit — `IsDeBruijnTailHyp` 撤回**:
   defect #3 修正 (`tail_limit : Tendsto ... atTop (nhds h_inf)` field 追加) を Agent A2
   が試行したが、closure 独立 audit (fresh subagent, CORE 内蔵) が **2 重 defect** で
   `DEFECT` verdict: (a) `Z_law` 不在で `Z := 0` bypass survive、(b) `h_inf : ℝ` で
   Gaussian heat-flow 発散を表現不能 → 構造的 vacuous。orchestrator が consumer 0 件を
   確認のうえ撤回。`EPIL3Integration.lean` 該当位置に retraction コメント残置、再導入は
   `h_inf : EReal` lift + `Z_law` 追加が前提 (Phase C-5 step 工数 +20 行に上方修正)。
   `IsDeBruijnIntegrationHyp` (defect #1) と `IsDeBruijnRegularityHyp.integrable_deriv`
   (defect #2) は staged 着地 (前者 OK、後者 questionable で `@audit:caveat(...)` 付与)。
   教訓: 「結合体に縛り field を 1 つ足せば vacuous-bypass 閉じる」は不十分、構造体
   field 間の独立 existential / `Z` 自体の制約 / 型の表現力 (ℝ vs EReal) の 3 軸を
   同時にチェックする必要。Defect prevention checklist に項目 5 (Z 自体の制約) +
   項目 6 (`h : ℝ` vs `EReal` 表現力) 追記を将来 Wave で検討。
