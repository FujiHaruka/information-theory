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

- [ ] Phase 0 — `EPIPlumbing.lean` 3 件先行 close (high ROI、独立着手可) 📋
- [ ] Phase A — Stam + de Bruijn 合流 skeleton (sister 待ち) 📋
- [ ] Phase B — Phase E corollary 各種 genuine 化 📋
- [ ] Phase V — verify (`lake env lean ...`) + Common2026.lean 編入 📋

proof-log: yes (各 Phase 完了時に `docs/shannon/proof-log-epi-stam-to-conclusion-phase-*.md`)

---

## Phase 0 — `EPIPlumbing.lean` 3 件先行 close (high ROI、独立着手可) 📋

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
| L-Concl-0-α | 0 | EPIPlumbing 3 件に defect 発見時の停止 | (defect report) | orchestrator が honest-auditor 起動 |
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
