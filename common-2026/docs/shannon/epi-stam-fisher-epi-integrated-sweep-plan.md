# EPI/Stam + FisherInfo + EntropyPowerInequality — 統合 sweep ムーンショット計画 🌙

> **Plan slug**: `epi-stam-fisher-epi-integrated-sweep`
> **Status**: Phase 2.A 完了 (`c0edc35`、no-op launder 判定、defect marker で acknowledge) / Phase 2.C 完了 (A3 pivot で `@audit:ok` 昇格) / Phase 2.B active。Cover-Thomas Ch.17 Inequalities + 部分 Ch.8 Differential Entropy を対象とする **4 cluster 統合 sweep**。
> **Created**: 2026-05-27
> **Parent (umbrella)**: 該当 family-level moonshot は存在せず、本 plan が integrated sweep の親計画として機能する。EPI/Stam family の従来 plan 群 (`epi-moonshot-plan` / `epi-stam-discharge-plan` / `epi-stam-to-conclusion-*-plan` / `epi-debruijn-integration-*-plan` / `fisher-info-sorry-migration-plan` / `fisher-info-moonshot-plan` / `fisher-info-gaussian-discharge-moonshot-plan` / `parallel-gaussian-moonshot-plan`) は **all referenced as upstream inputs / closure routes**。本 plan は umbrella で、各 cluster Phase の出力は既存 plan の Phase 状態に逆参照される。

## Context

### 起動契機

Phase A 完了 (commit `20ee48b`、`stamToEPIBridge_holds` shared sorry 補題 + `entropy_power_inequality_unconditional` hypothesis-free wrapper publish 済) で `fisher-info-sorry-migration-plan` Phase 0「Case α (全降格)」が解禁。同 plan の再起動条件 3 件のうち (1) Phase A 完了は達成、(2) 統合 plan 起草 + (3) `IsRegularDeBruijnHypV2` field restructuring は本 plan で実施。

### 4 cluster 構成 (依存方向: 上流 ← 下流)

```
[Cluster D] EntropyPowerInequality + DeBruijn integration (主定理露出 + 補助 corollary)
                ▲
[Cluster C] EPI/Stam — bridge + scaling + discharge (38/39 ok + Phase A 完了 + 内部残置 sorry 3)
                ▲
[Cluster B] FisherInfo cluster (Phase A 解禁、tier 5 defect 5 件 + suspect 5 件)
                ▲
[Cluster A] ParallelGaussianPerCoord (sweep 統合判断対象、独立 candidate)
```

依存は上流から下流 (Cluster B sorry が closure すると Cluster C/D に transitive sorry 解消が伝播)。Cluster A は独立 candidate で、Phase 0 で統合 / 独立を判定。

### Cluster 別 tag inventory (2026-05-27 baseline、cluster 合計)

| cluster | suspect | staged | closed-by-succ | defect | retract-cand | @residual | sorry |
|---|---:|---:|---:|---:|---:|---:|---:|
| **B (FisherInfo cluster、7 file)** | 5 | 0 | 0 | 0 | 0 | 0 | 2 |
| **C (EPI/Stam、9 file)** | 17 | 8 | 0 | 0 | 21 | 9 | 18 |
| **D (EntropyPowerInequality、1 file)** | 0 | 0 | 3 | 2 | 2 | 1 | 7 |
| **B+C+D total** | **22** | **8** | **3** | **2** | **23** | **10** | **27** |

Cluster A (独立 candidate、`ParallelGaussianPerCoordRegularity.lean`) は `@residual` 1 件のみ。Phase 起動時に該当 cluster の per-file 内訳を `rg -c` で verbatim 再取得。

カウント note:
- `@audit:retract-candidate` 23 件は Phase A cleanup (`e7b779e` / `20ee48b`) 産物の bookkeeping (tier 3)、本 sweep 移行対象外
- `@audit:closed-by-successor` 3 件は Cluster D defect 2 件 + `isStamToEPIBridge_of_epi`、Phase 3 で migrate
- `@audit:staged(epi-debruijn-regularity)` (`EPIStamDischarge.lean:146`) は structure refactor 済 honest、touch せず

### tier 5 defect (Cluster B 5 件 + Cluster D 2 件) — Phase A で自動解消せず

verbatim (2026-05-27)。Cluster B 5 件は **Phase A 完了で自動解消しない** (Phase A は EPI 主定理 path のみ touch、上流 predicate signature 不変)、Phase 2 で構造的処理必須。Cluster D 2 件は Phase 3 で migrate。

| # | declaration | file:line | 構造 | 処遇 |
|---|---|---|---|---|
| 1 | `IsIBPHypothesis` (def) | `FisherInfoV2DeBruijnBody.lean:184` | `:= HasDerivAt ... (1/2 * fisherInfoOfDensityReal (p t)) t` literal alias | Phase 2 |
| 2 | `deBruijn_identity_v2_of_heat_flow` | `FisherInfoV2DeBruijnBody.lean:209` | body `:= h_ibp` (#1 unfold) | Phase 2 |
| 3 | `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` (field) | `FisherInfoV2DeBruijn.lean:195` | field 型 = 結論型 verbatim、load-bearing | Phase 2 (本 sweep 最大 step) |
| 4 | `deBruijn_identity_v2` | `FisherInfoV2DeBruijn.lean:227` | body `:= h_reg.derivAt_entropy_eq_half_fisher_v2` (#3 抽出) | Phase 2 |
| 5 | `deBruijn_identity_v2_of_heat_subhyp` | `FisherInfoV2HeatFlowBody.lean:240` | transitive forward to #2 | Phase 2 |
| D1 | `IsStamInequalityHypothesis := True` | `EntropyPowerInequality.lean:144` | `@audit:defect(prop-true)` `@audit:closed-by-successor(epi-stam-discharge-plan)`、`IsStamInequalityResidual` 代替済 | Phase 3 retract or alias |
| D2 | `IsDeBruijnIntegrationHypothesis := True` | `EntropyPowerInequality.lean:160` | `@audit:defect(prop-true)` `@audit:closed-by-successor(epi-debruijn-integration-plan)`、consumer 要 verbatim 確認 | Phase 3 retract or alias |

### Wall 集約方針

`docs/audit/audit-tags.md` Wall name register との関係:
- **`wall:stam`** (登録済) — EPI/Stam family primary owner。`EPIStamToBridge.lean` 9 件 `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` の wall 集約 vs plan-slug 維持は Phase 1 で再判定。
- **`wall:debruijn-integration`** (登録済、commit `23dae39`) — Phase 2 で L1 `debruijnIdentityV2_holds` が genuine closure point。
- **`wall:fisher-info-score-zero`** — 新規 promote 留保 (Phase 2.C で「不要」確定、A3 pivot 参照)。
- `epi-n-dim` は本 sweep 外 (1-dim EPI のみ)。

### Honesty バー

主要バー = 全 13 file **type-check done** (`lake env lean` 0 errors、`sorry` は `@residual(<class>:<slug>)` 付き) で commit/push 可。proof done は本 sweep 範囲外 (上流 `wall:stam` が残るため)。進行中に新規 tier 5 defect を発見したら即フラグ (CLAUDE.md「検証の誠実性」)。

## Approach

### 全体戦略

統合 sweep を選ぶ理由 (`fisher-info-sorry-migration-plan` の Pattern G escalate「単独 sweep 禁止」結論の実行 plan):

- **olean cascade**: `IsRegularDeBruijnHypV2` structure refactor は Cluster C の active consumer 14 件に signature ripple。分離だと Phase ごとに refresh round-trip、統合だと最後 1 回。
- **wall 集約は cluster 横断**: `wall:stam` / `wall:debruijn-integration` の集約先は 13 file の consumer 構造を見ないと判定不能。
- **tier 5 defect 5 件は同一構造**: `IsRegularDeBruijnHypV2` field / `IsIBPHypothesis` literal alias / `:= h_ibp` 循環の同一 family。
- **Phase A momentum**: shared sorry 補題の設計判断を `stamToEPIBridge_holds` と同時期に行うのが整合的。

回避策: Phase 1/2/3 を sequential、Phase 内部の独立 declaration は worktree 並列。1 session = 1 Phase が無理なら sub-step 分割 + handoff 跨ぎ。

### Phase 依存関係

Phase 1 (C) → Phase 2 (B) → Phase 3 (D) は **sequential 必須** (Cluster 跨ぎ並列禁止): Cluster B の `IsRegularDeBruijnHypV2` refactor が Cluster C の active consumer に ripple するため、Phase 1 で anchor 固定後に Phase 2 で refactor、Phase 3 で主定理層を整理。Phase V は最終検証。Phase 内部の **declaration 独立 sub-step は worktree 並列可** (Phase 2 のみ literal alias chain の連鎖で sequential 必須)。

### wall 集約方針 + tier 5 第一選択ルート

- `wall:stam` (登録済): EPI/Stam family primary。Phase 1 で `EPIStamToBridge.lean` 9 件の集約 vs plan-slug 維持を再判定。
- `wall:debruijn-integration` (登録済 `23dae39`): Phase 2 で L1 `debruijnIdentityV2_holds` が genuine closure point。
- `wall:fisher-info-score-zero`: A3 pivot で **不要確定**。
- 第一選択 (定義書換) ルート: tier 5 defect は Mathlib `HasDerivAt` 結論形に整合させる方針 — load-bearing field の核は shared sorry 補題 (`@residual(wall:...)`) に分離、regularity precondition は structure に残す。判定軸の詳細 → Phase 2 §「判定軸」。

### 規模見積もり

中央予測 ~1000 行 / 7 session、Phase 2 が支配 (~500-900 行 / 3-5 session)。段階的 ship: Tier 1 = Phase 1+3 (FisherInfo refactor 無しで完結)、Tier 2 = 全 Phase。

---

## Phase 0 — verbatim inventory + Cluster A 判定 + wall 集約初期判定 📋

> docs-only Phase。Context 節の verbatim tag inventory 表 + tier 5 defect 表で完了済 (本 plan 起草 commit 内)。

残 step:
- Cluster A (ParallelGaussianPerCoord) 統合 / 独立 / skip 判定: **default 独立** (Cluster B/C/D との signature 連動薄い、`fisher-info-sorry-migration-plan` Round 4 candidate も別 sweep)、`ParallelGaussianPerCoordRegularity.lean` 1 `@residual` + parallel-gaussian-* plan の Phase 進捗を verbatim 確認後に最終確定 → Phase 6 セクション。
- wall 集約初期判定: `wall:stam` は EPI/Stam family primary owner で保持、`EPIStamToBridge.lean` 9 件は plan-slug 維持 default (Phase 1 で再判定)、`wall:debruijn-integration` / `wall:fisher-info-score-zero` は新規 promote 留保 (Phase 2/3 で判定 — 後者は A3 pivot で不要確定)。

**L-INT-0-α**: Cluster A 統合が strictly necessary と判明 → Phase 4/5 追加、規模見積もり update。default 独立で発火確率低。

---

## Phase 1 — Cluster C (EPI/Stam) sweep 📋

主要対象: **suspect 17 件** (`EPIStamStep3Body.lean` 7 = Lagrange optimization + `EPIStamToBridge.lean` 1 `IsStamToEPIScalingHyp:147` + `EPIL3Integration.lean` 9 = `epi-debruijn-integration-*` slug 混在) の sorry-based migration。`EPIStamToBridge.lean` 9 `@residual` + sorry 14 + staged 2 件 (`EPIStamDischarge.lean` 既 refactor 済) は Phase A 残置の slug 整合確認のみ。他 5 file は touch せず。Phase 起動時に Phase 0 inventory 表で verbatim 再確認。

並列 dispatch: Step3Body 7 件は worktree 並列可 (3 group)、EPIL3Integration 9 件は file 共有のため single dispatch、ToBridge は single。

Done: suspect 17 件 migration 完了 + 9 file `lake env lean` 0 errors + 各 sorry に `@residual` + honesty-auditor PASS。

撤退ライン:
- **L-INT-1-α**: Step3Body 7 件が `stamToEPIBridge_holds` で transitive 解消 → `@audit:ok` 昇格 (strict honest、発火確率低)
- **L-INT-1-β**: `IsStamToEPIScalingHyp` retract が大規模 ripple → 延期 + sorry-based 残置
- **L-INT-1-γ**: 新規 tier 5 defect 発見 → 停止 + honest-auditor 起動依頼

---

## Phase 2 — Cluster B (FisherInfo cluster) refactor 📋

> **Phase 1 完了前提** (Cluster C の anchor 固定)。本 Phase は **本 sweep の最大規模 step**、`IsRegularDeBruijnHypV2` structure refactor + tier 5 defect 5 件 sequential 処理。

### スコープ (verbatim)

**対象 file (7 file、Phase 0 inventory 表 Cluster B より)**:

| file | suspect | sorry | Phase 2 処遇 |
|---|---:|---:|---|
| `FisherInfo.lean` | 1 | 0 | `integral_logDeriv_pdf_eq_zero` (`:113`) suspect → **`@audit:ok` 昇格** (2026-05-27 Phase 2.C honesty audit verdict、A3 pivot)。body は 13 行 genuine proof + `integral_deriv_eq_zero` field は regularity 帰結 (load-bearing core ではない) と判定 |
| `FisherInfoV2.lean` | 1 | 0 | `integral_logDeriv_density_eq_zero` (`:151`) V2 analog、同上 (`@audit:ok` 昇格) |
| `FisherInfoV2DeBruijn.lean` | 1 | 0 | `deBruijn_identity_v2` (`:227+`) tier 5 defect (load-bearing field 抽出)、structure refactor + sorry-based migration |
| `FisherInfoV2DeBruijnBody.lean` | 1 | 2 | `IsIBPHypothesis` def 書換 + `deBruijn_identity_v2_of_heat_flow` tier 5 defect 解消、既存 sorry 2 件は `@residual` 付与 verify |
| `FisherInfoV2HeatFlowBody.lean` | 1 | 0 | `deBruijn_identity_v2_of_heat_subhyp` tier 5 defect (transitive literal alias) 解消 |
| `FisherDeBruijnGaussianWitness.lean` | 0 | 0 | touch せず (FisherInfo cluster の Gaussian witness、Phase 2 refactor の consumer side) |
| `FisherInfoGaussian.lean` | 0 | 0 | touch せず |

### Approach (sequential、tier 5 defect 5 件を 1 declaration ずつ処理)

Phase 2.A は実施済 (commit `c0edc35`)、独立 audit (`a6ae83b`) で no-op launder と判定 → defect marker で acknowledge、本 Phase 2.B で candidate 2 (field 削除) に逆転。経緯 → 判断ログ。

#### Phase 2.B スコープ表 (verbatim line 確認済、2026-05-27)

| # | declaration | file:line | 現状 body | pattern 分類 | foundation で同時解消? |
|---|---|---|---:|---|:---:|
| F1 | `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` (structure field) | `FisherInfoV2DeBruijn.lean:204-208` | `HasDerivAt (...) ((1/2) * fisherInfoOfDensityReal density_t) t` (field = 結論型 verbatim) | **load-bearing field bundling** (foundation step、structure 改変) | **本 step 自身** |
| L1 | `debruijnIdentityV2_holds` (Phase 2.A shared sorry 補題) | `FisherInfoV2DeBruijn.lean:258-268` | body `sorry`、結論型 ≡ F1 field 型 verbatim | **no-op launder** (Phase 2.A 産物、`@audit:defect(launder)`) | **yes** — F1 削除後は本 lemma が genuine wall closure point に昇格、または retract |
| L2 | `deBruijn_identity_v2` (sweep の主定理) | `FisherInfoV2DeBruijn.lean:292-302` | `debruijnIdentityV2_holds X Z hX hZ hXZ ht h_reg` (L1 経由、Phase 2.A 産物) | **1 段 indirection 経由 launder** (Phase 2.A 産物) | **yes** — L1 が genuine 化すれば本 wrapper は honest pass-through |
| L3 | `deBruijn_identity_v2_of_heat_flow` (body bridge) | `FisherInfoV2DeBruijnBody.lean:209-221` | `h_ibp` (literal alias unfold、`IsIBPHypothesis := HasDerivAt ...`) | **literal alias `:= h_ibp` 循環** (元 tier 5 defect 2) | **yes** — F1 削除と同時に shared sorry 補題経由に書換 |
| L4 | `IsRegularDeBruijnHypV2.ofHeatFlow` (constructor、auditor 追加発見) | `FisherInfoV2DeBruijnBody.lean:229-240` | `derivAt_entropy_eq_half_fisher_v2 := h_ibp` (constructor 内 literal alias、field 設定 spot) | **constructor 内 literal alias** (F1 削除で field 自体消失) | **yes** — F1 削除で本 field 設定 line が消失、constructor signature 縮小 |
| D1 | `IsIBPHypothesis` (def) | `FisherInfoV2DeBruijnBody.lean:184-190` | `:= HasDerivAt (...) ((1/2) * fisherInfoOfDensityReal (p t)) t` (def 自身が結論型 = literal alias) | **predicate-form literal alias** (元 tier 5 defect 1) | **partial** — L3 / L4 consumer が削除されれば retract 可、ただし `FisherDeBruijnGaussianWitness.lean:43/51` 残存 consumer 注意 |
| D5 | `deBruijn_identity_v2_of_heat_subhyp` (transitive bridge) | `FisherInfoV2HeatFlowBody.lean:221-234` | `deBruijn_identity_v2_of_heat_flow X Z hX hZ hXZ ht (... h_ibp) ...` (transitive literal alias 経由) | **transitive literal alias** (元 tier 5 defect 5) | **yes** — L3 解消で transitive 解消 |
| D5' | `IsRegularDeBruijnHypV2.ofHeatSubhyp` (constructor、D5 と対) | `FisherInfoV2HeatFlowBody.lean:239-250` | `IsRegularDeBruijnHypV2.ofHeatFlow ... h_ibp` (L4 経由 transitive、auditor 追加発見) | **transitive constructor literal alias** | **yes** — L4 縮小 (field 消失) で signature 自動修正 |

合計 8 declaration に touch (F1 + L1-L4 launder + D1 + D5/D5' transitive)。

#### Approach 3 段 (sequential、foundation を最初に置く)

- **段 1 (foundation)**: F1 field 削除 + L4 constructor 縮小 + L1 audit docstring の `@audit:defect(launder)` 削除 (L1 は F1 削除で genuine wall closure point に昇格、`@residual(wall:debruijn-integration)` のみ残す)。F1 削除で `IsRegularDeBruijnHypV2` structure は `Z_law` + `density_t` のみに縮小。
- **段 2**: L2 → L3 → D5 → D5' を **sequential** 1 declaration = 1 dispatch + 1 commit (literal alias chain 逆順、4 dispatch)。L3 signature が下流に ripple するため並列禁止。L2 は honest pass-through (`@audit:ok` 候補)、L3 は `IsIBPHypothesis` literal alias 維持 + D1 を retract candidate に。
- **段 3**: D1 (`IsIBPHypothesis` def) は alias 維持 + `@audit:retract-candidate(name-laundering-alias)` 付与 (`FisherDeBruijnGaussianWitness.lean:43/51` 残存 consumer のため完全 retract は本 sweep 外、L-INT-2-β)。

並列 dispatch: Wave 2-A = 段 1 single dispatch、Wave 2-B = 段 2 sequential 4 dispatch、Wave 2-C = 段 3 + Phase 2.C と file 別並列可。

#### Phase 2.C — `integral_logDeriv` 2 件 (実施済、A3 pivot で `@audit:ok` 昇格)

2026-05-27 A3 pivot: 当初 shared sorry 補題化設計を reject、`@audit:suspect` → `@audit:ok` 直接昇格 (`FisherInfo.lean:111` / `FisherInfoV2.lean:149`)。body 12-13 行 genuine proof + field が regularity 帰結 (Phase 2.A engine substitution と非同型) のため。詳細 → 判断ログ entry 3。

### 判定軸 — load-bearing vs regularity 帰結 (Phase 2.A vs 2.C で確立)

shared sorry 補題化または field 削除を判断する前に verbatim check:

1. shared sorry 補題の **結論型** と structure **field 型** を verbatim 取得
2. 両者が **engine substitution** (`density_t` → `h_reg.density_t` 等の trivial rename) のみで一致 → load-bearing core、field 削除 / shared 補題化禁止 (Phase 2.A no-op launder 同型)
3. 間に non-trivial bridge (pointwise positivity / FTC step / etc) があり、field が conclusion を **strictly weaker な形で** bundle → regularity 帰結、現状維持で OK (Phase 2.C 同型)

Phase 2.B foundation 段 1 では `derivAt_entropy_eq_half_fisher_v2` field 型と `debruijnIdentityV2_holds` 結論型が verbatim 一致と確認済 (`FisherInfoV2DeBruijn.lean:204` vs `:264`) → field 削除のみが genuine refactor と確定。

### 撤退ライン (Phase 2)

- **L-INT-2-α**: F1 field 削除中に Phase A `density_t_eq` pin 不整合 or Cluster C consumer ripple 許容外 (5 件直接抽出 + 1 件 Gaussian witness lift、計 6+ 件) → field 削除中止、8 declaration 全件残置 + tier 5 marker (L1 docstring の `@audit:defect(launder)` + `@audit:retract-candidate(launder)` 維持、後続 plan 委譲)。Done 条件は「F1 削除完了」ではなく「8 declaration honesty 状態が暫定マーカーで明示済」に retreat。
- **L-INT-2-β**: L2/L3/D5/D5' のうち N 件のみ closure、残置分は `@audit:defect(launder)` / `@audit:retract-candidate(name-laundering-alias)` 明示。
- **L-INT-2-δ**: foundation 段 1 で field 削除断行中に Phase 1 anchor (Cluster C suspect/sorry 整理) と signature 衝突 → Phase 1 への一時 revert + 再 anchor 設定。

### Done 条件 (Phase 2)

- 段 1-3 完了 + launder pattern 撲滅 (下記 `rg` で 0 hit) + Cluster B 5 file `lake env lean` 0 errors
- Cluster C consumer ripple 確認: F1 field 削除で `EPIStamToBridge.lean` (3 件 field 抽出 → `deBruijn_identity_v2` 呼出書換) + `EPIL3Integration.lean:678` (Gaussian witness lift constructor の field 設定書換) で 0 errors、`EPIStamDeBruijnConclusion.lean:144` / `FisherDeBruijnGaussianWitness.lean` は touch せずに済むか確認
- honesty-auditor 独立 audit PASS (特に L1 が no-op launder から genuine closure point に昇格したか verbatim check)

検証 bash (段別検証は `lake env lean Common2026/Shannon/<file>.lean` を該当 file ごとに、段 1 後は `lake build Common2026.Shannon.FisherInfoV2DeBruijn` で olean refresh):

```bash
# launder pattern 撲滅確認 (Done 条件)
rg -n ':= h_ibp|:= h_reg\.derivAt_entropy_eq_half_fisher_v2' Common2026/Shannon/Fisher*.lean
# 0 hit が Done 条件
```

---

### Phase 3 pre-launch audit (2026-05-27)

> docs-only fresh pass、実装変更なし。Phase 2.B/2.C verdict 反映漏れ (forgotten-sweep) を 3 declaration について verbatim 確認、3 sub-step default を update。

#### 3 declaration consumer 表 (verbatim、`Common2026/Shannon/EntropyPowerInequality.lean`)

**D1 — `IsStamInequalityHypothesis` (`:144`)**

```lean
def IsStamInequalityHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop := True
```

docstring tag: `@audit:defect(prop-true)` + `@audit:closed-by-successor(epi-stam-discharge-plan)`。

| consumer 種別 | file:line | 性質 |
|---|---|---|
| 定義 (本体) | `EntropyPowerInequality.lean:144` | def 自身 |
| docstring 言及 (本体) | `EntropyPowerInequality.lean:37, 67` | 自己説明 (Roadmap-style listing) |
| **実 call site (結論型)** | `EPIStamDischarge.lean:111-116` | `isStamInequalityHypothesis_of_stamInequalityHyp` bridge wrapper、結論型に登場、body は `trivial` |
| docstring 言及 (consumer) | `EPIStamDischarge.lean:48, 109` | bridge wrapper 周辺の説明散文 |

実 call site = **1 件のみ** (EPIStamDischarge.lean:111 の bridge wrapper の結論型)、body は `trivial` で `:= True` を悪用している honest bridge。新規 `IsStamInequalityResidual` (`EntropyPowerInequality.lean:197+`) が genuine 代替として既に存在し、`entropy_power_inequality` 主定理 (`:259`) は新方の hypothesis を取る形に既に migrate 済。retract 時の影響は (a) bridge wrapper 1 件削除 + (b) 自己説明 docstring 文言修正のみ。

**D2 — `IsDeBruijnIntegrationHypothesis` (`:160`)**

```lean
def IsDeBruijnIntegrationHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop := True
```

docstring tag: `@audit:defect(prop-true)` + `@audit:closed-by-successor(epi-debruijn-integration-plan)`。

| consumer 種別 | file:line | 性質 |
|---|---|---|
| 定義 (本体) | `EntropyPowerInequality.lean:160` | def 自身 |
| docstring 言及 (本体) | `EntropyPowerInequality.lean:41, 67` | 自己説明 |
| **実 call site (引数型)** | `EPIStamDischarge.lean:745` | `epi_via_stam_main_eq` の `_h_db : IsDeBruijnIntegrationHypothesis X Y P` (アンダースコア prefix = unused) |
| docstring 言及 (consumer) | `EPIStamDischarge.lean:299, 448` | 他 wrapper の vacuity 説明散文 |

実 call site = **1 件のみ + unused** (`_h_db` underscore prefix)。`epi_via_stam_main_eq` の body (`:748`) は `entropy_power_inequality P X Y hX hY hXY h_stam` で `_h_db` を使わない。retract 時の影響は (a) `epi_via_stam_main_eq` の引数 1 件削除 + (b) 自己説明 docstring 修正のみ。**D1 より retract 安全度高い**。

**R — `entropy_power_inequality_gaussian_saturation` (`:295`)**

```lean
theorem entropy_power_inequality_gaussian_saturation
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      = entropyPower (P.map X) + entropyPower (P.map Y)
```

docstring tag: なし (`@audit:ok` 候補だが未付与、body は genuine 22 行)。

| consumer 種別 | file:line | 性質 |
|---|---|---|
| 定義 | `EntropyPowerInequality.lean:295` | 本体 |
| 実 call site | `EntropyPowerInequality.lean:339` | `isEntropyPowerInequalityHypothesis_of_gaussian` 内部 rewrite (同一 file) |
| 実 call site | `EPIStamDischarge.lean:419, 595` | 2 件 |
| 実 call site | `EPIStamToBridge.lean:312, 1122` | 2 件 |
| 実 call site | `EPIL3Integration.lean:377, 1145` | 2 件 |
| 実 call site | `EPIStamDeBruijnConclusion.lean:274` | 1 件 |
| docstring 言及 | `EPIL3Integration.lean:47, 361, 1116, 1121` | 4 件 (説明散文) |
| docstring 言及 | `EPIStamStep12Body.lean:330` / `EPIStamInequalityBody.lean:301` / `EPIStamStep3Body.lean:284` / `EPIStamDischarge.lean:312, 319` / `EPIStamToBridge.lean:45, 70, 1013, 1102` / `EPIStamDeBruijnConclusion.lean:259` | 説明散文 (合計 11 件) |

実 call site = **8 件 (5 file 横断、本体除く)**、docstring 言及 **15+ 件**。`entropyPower_gaussian_additivity` を rg で全件検索 → **0 hit** (命名衝突なし、Phase 2 で preconditioning な別 declaration 追加無し)。

#### Phase 2.B/2.C verdict 反映漏れ check (forgotten-sweep)

- **D1 docstring の successor 参照** (`@audit:closed-by-successor(epi-stam-discharge-plan)`): `docs/shannon/epi-stam-discharge-plan.md` 存在確認済 (`ls docs/shannon/` で hit)。Phase 2 で path 変更なし。**PASS**。
- **D2 docstring の successor 参照** (`@audit:closed-by-successor(epi-debruijn-integration-plan)`): `docs/shannon/epi-debruijn-integration-plan.md` 存在確認済。さらに Phase 2.B で `debruijnIdentityV2_holds` shared sorry 補題 (`wall:debruijn-integration`、`FisherInfoV2DeBruijn.lean:245`) が genuine wall closure point として確立 (本 plan §Phase 2.B 段 1 で foundation 段が field 削除断行を default)。Phase 2.B 完了後は D2 の `:= True` を **`wall:debruijn-integration` 集約 path 経由の代替 predicate** に書換える option が増える (現状は successor plan 委譲)。**PASS** (option 増加は upside、defect ではない)。
- **R rename 衝突** (`entropyPower_gaussian_additivity`): rg で 0 hit、Phase 2 で preconditioning 済の同名 declaration なし。**PASS**。

forgotten-sweep verdict: **3 件全 PASS、DEFECT なし**。

副次気付き: D2 の現 successor plan は `epi-debruijn-integration-plan` だが、Phase 2.B で `wall:debruijn-integration` 集約が完成すれば D2 retract path を「successor plan 待ち」から「Phase 2.B 派生 (shared sorry 補題 alias)」に切替可能。Phase 3.B default を update する根拠 (下記)。

#### 3 sub-step 戦略提案 (verbatim consumer 数を反映)

- **3.A (D1)**: **retract 断行を維持**。実 call site 1 件 (bridge wrapper、body `trivial`)、新方 `IsStamInequalityResidual` 代替済。edit 量: D1 def 削除 (3 行) + bridge wrapper `isStamInequalityHypothesis_of_stamInequalityHyp` 削除 (6 行) + docstring 言及 3 箇所修正 (5 行) = **~15 行**。撤退ライン L-INT-3-α (alias 維持) 発火確率は低 (consumer 1 件で alias 維持の利益薄い)。

- **3.B (D2)**: **retract 断行に default 更新** (元 default「consumer 数次第」から強化)。実 call site 1 件かつ **unused underscore** (`_h_db`)、Phase 2.B `wall:debruijn-integration` 集約が successor plan 完成より早く achieve される見込で代替 predicate 書換の動機が薄れた。edit 量: D2 def 削除 (3 行) + `epi_via_stam_main_eq` 引数削除 + 該当 caller (もし `epi_via_stam_main_eq` を直接呼ぶ場所があれば) 修正 = **~10 行** (caller 0 件なら 5 行)。撤退ライン L-INT-3-α 発火確率は **D1 より低い** (unused argument 削除は型 ripple 0)。

- **3.C (R rename)**: **rename を延期 default に弱化** (元 default「consumer 数 < 10 で断行、大なら延期」、verbatim 確認後 = 実 call site 8 件 + docstring 言及 15+ 件 = 計 23+ 件)。8 < 10 で機械的には断行範囲だが docstring 言及まで含めると更新箇所 23+ 件、Phase 3 規模を 30 行 → 80-120 行に膨張させる。さらに Cover-Thomas Ch.17 用語整合は本 sweep の primary objective ではなく **`docs/textbook-roadmap.md` Ch.17 frontier 行 update のついで作業** (Phase V Done 条件にすでに含まれる)。**default = 延期 + docstring に "rename pending (Phase V 後、Ch.17 frontier sweep で実施)" 1 行追加**。撤退ライン L-INT-3-β を新規 default (発火 = 延期実行) に格上げ。

#### 並列可否評価

3 sub-step は **同一 file** (`EntropyPowerInequality.lean`) を編集。3.A/3.B は def 削除 + docstring 修正、3.C は (延期なら) docstring 1 行追加のみ。並列 3 worktree dispatch は (a) 3 worktree merge コスト + (b) 同一 file 3 並列の git conflict 解消コスト + (c) Mathlib 5 GB symlink × 3 のメリットが薄い (実 edit 量計 ~25-30 行)。**sequential single agent dispatch (1 agent で 3.A → 3.B → 3.C 順次) を推奨**。worktree 不要 (3.A は 3.B/3.C と独立だが、file 1 つで edit 量小さく、orchestrator merge step を 1 回に圧縮できる)。所要時間: ~1 session で完結見込。

#### 結論 (Phase 3 Wave 2 dispatch 推奨パターン)

**single agent sequential dispatch** (`lean-implementer` 1 件、worktree なし、main 直接編集)。3.A retract + 3.B retract + 3.C 延期 docstring 1 行で `EntropyPowerInequality.lean` 1 file の全 sub-step を 1 commit で完結。

---

## Phase 3 — Cluster D (EntropyPowerInequality) sweep 📋

> Phase 2 完了前提。`EntropyPowerInequality.lean` 1 file のみ。

3 sub-step (互いに独立、並列 3 dispatch 可):

- **3.A**: `IsStamInequalityHypothesis := True` (`:144`、`@audit:defect(prop-true) + @audit:closed-by-successor(epi-stam-discharge-plan)`) → retract 断行 default。`IsStamInequalityResidual` (`:197+`) が代替済、bridge wrapper `isStamInequalityHypothesis_of_stamInequalityHyp` (`EPIStamDischarge.lean:111`) 1 件のみ consumer。retract 不可なら literal alias + `@audit:retract-candidate(name-laundering-alias)`。
- **3.B**: `IsDeBruijnIntegrationHypothesis := True` (`:160`、同 defect kind) → consumer 数を `rg` で確認、0 件なら retract、1+ 件なら Phase 2 の `IsRegularDeBruijnHypV2` 経由代替 predicate に書換。
- **3.C**: `entropy_power_inequality_gaussian_saturation` (`:295`) を `entropyPower_gaussian_additivity` に rename 検討 (Cover-Thomas Ch.17 用語整合、textbook-roadmap Ch.17 frontier 記載)。consumer 数 < 10 で断行、大なら延期。

Done: 2 件 `Prop := True` migration (or retract) 完了 + rename 結論記録 + `lake env lean` 0 errors + honesty-auditor PASS。

撤退ライン:
- **L-INT-3-α**: retract 不可 → alias 維持 + `@audit:retract-candidate(name-laundering-alias)`
- **L-INT-3-β**: rename consumer 大規模 → 延期 + docstring に「rename pending」
- **L-INT-3-γ**: 新規 tier 5 defect 発見 → 停止

---

## Phase 6 — Cluster A (ParallelGaussianPerCoord) 統合判定 📋

default **独立 (skip)** = 本 sweep 外、`parallel-gaussian-moonshot-plan.md` Phase 進行で継続。Phase 0 step 3 で `ParallelGaussianPerCoordRegularity.lean` 1 `@residual` + parallel-gaussian-* 4 plan の Phase 進捗を Read して signature 連動 (`IsRegularDeBruijnHypV2` / `IsStamInequalityResidual` 経由) を確認、連動あれば Phase 4/5 として統合。

---

## Phase V — 全 13 file 検証 + honesty-auditor × 3 cluster 並列 audit 📋

検証: 全 13 file (条件付き Cluster A で 14 件) の `lake env lean` 0 errors、`sorry` は `@residual` 付き。file 一覧は本文末「検証手順」bash 内に verbatim。

audit: Cluster B / C / D それぞれに `honesty-auditor` を fresh dispatch (file 所有権分離、worktree 不要)。出力 200 行以内サマリ + 必要なら docstring refine (code が SoT)。

撤退ライン:
- **L-INT-V-α**: 1 cluster partial closure → 別 sweep に分割
- **L-INT-V-β**: audit verdict questionable → session 中に refine、DEFECT なら sorry-based 書換

Done: 全 file 検証 PASS + audit PASS + `Common2026.lean` import 確認 + 判断ログに closure entry (Phase 別件数集計) + 既存親 plan 群の進捗ブロック update + `docs/textbook-roadmap.md` Ch.17 EPI frontier 行 update。

---

## 全撤退ライン共通規律

各 Phase の撤退ラインは per-Phase 節参照。共通禁止事項:
- `Prop := True` placeholder / 結論型 ≡ 仮説型 `:= h` 循環 / load-bearing hyp 完成詐称 (`*_discharged` 命名等) / 退化定義悪用 (`density_path := 0` 等) を新規導入しない。既存 defect は本 sweep で migrate (sorry-based or retract)。

---

## 検証手順

Phase 別: 該当 Cluster の file (Phase 1 = Cluster C 9 file / Phase 2 = Cluster B 7 file / Phase 3 = Cluster D 1 file) を `lake env lean` 個別実行。signature 改変後は `lake build Common2026.Shannon.<refactored-file>` で olean refresh。

Phase V 統合 final:

```bash
# 全 13 file (条件付き 14 file)、ファイル名は Phase V スコープ節参照
for f in FisherInfo FisherInfoV2 FisherInfoV2DeBruijn FisherInfoV2DeBruijnBody \
         FisherInfoV2HeatFlowBody FisherDeBruijnGaussianWitness FisherInfoGaussian \
         EPIStamDischarge EPIStamToBridge EPIStamInequalityBody EPIStamStep12Body \
         EPIStamStep3Body EPIStamDeBruijnConclusion EPIL3Integration EPIPlumbing \
         StamGaussianBound EntropyPowerInequality; do
  lake env lean Common2026/Shannon/$f.lean
done

# 残課題集計 + 分類漏れ + deprecated タグ残置確認 (audit-tags.md recipe)
rg "@residual" Common2026/Shannon/ | wc -l
rg -o "@residual\([a-z]+:" Common2026/Shannon/ | sort | uniq -c | sort -rn
rg '@audit:suspect\(|@audit:staged\(|@audit:defer\(|@audit:closed-by-successor\(|🟢ʰ' \
  Common2026/Shannon/EPI*.lean Common2026/Shannon/Fisher*.lean \
  Common2026/Shannon/Stam*.lean Common2026/Shannon/EntropyPowerInequality.lean
```

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

4. **2026-05-27 — Phase 3 + Phase V closure (Cluster B/C/D 独立 audit 全 PASS、統合 sweep 終了)**:
   - Phase 3 Wave 2 (commit `8eaa0fb`): Cluster D `:= True` 2 件 retract (D1 `IsStamInequalityHypothesis` + D2 `IsDeBruijnIntegrationHypothesis`) + 3.C rename 延期 (consumer 23+ occurrence、`entropyPower_gaussian_additivity` への rename は Ch.17 frontier sweep 別 plan に切出、plain Lean コメント明示)。`@audit:defect(prop-true)` 2 件 tier 5 解消
   - Phase V audit (3 cluster 並列、`honesty-auditor` × 3、touch file 独立):
     - **Cluster B** (7 file): defect 0、書込 0、Phase 2.B foundation 段 1 (a)-(d) 全 verdict OK (F1 field 削除 + `debruijnIdentityV2_holds` genuine wall closure + `deBruijn_identity_v2` honest pass-through Pattern C 許容 + `IsIBPHypothesis` retract-candidate 妥当)、Phase 2.C `integral_logDeriv` 2 件 `@audit:ok` 維持妥当
     - **Cluster C** (9 file): defect 0、書込 0、Phase 3 Wave 2 retract verdict OK (`epi_via_stam_main_eq` 引数削除 + bridge wrapper 削除 + type-check pass)、§Phase 1 sweep verdict = **打ち切り推奨** (incidental migration で suspect 17→4 縮減済、残 tier 4 legacy 10 declarations は別 family sweep target)
     - **Cluster D** (1 file): defect 0、書込 **9 件 `@audit:ok` 昇格** (`entropyPower_pos` / `_nonneg` / `_gaussianReal` / `entropy_power_inequality` + `_exp_form` + `_log_form` / `entropy_power_inequality_gaussian_saturation` / `isEntropyPowerInequalityHypothesis_of_gaussian` / `entropyPower_map_add_const`)、Phase 3 Wave 2 Done 条件達成
   - 全 17 file `lake env lean` 0 errors (sorry warning は既存 `@residual` 付き、新規 sorry 0)
   - **統合 sweep 終了**: tier 5 defect 全解消 (Cluster B/C/D 全件 0)、§Phase V Done 条件達成。残 frontier:
     - Phase 1 残置 tier 4 legacy 10 declarations (Cluster C、緊急性 LOW、別 family sweep target)
     - 3.C R rename (Ch.17 frontier sweep 別 plan)
     - Cluster A (`ParallelGaussianPerCoord`) は独立 candidate のまま (default skip 維持、L-INT-0-α 未発火)
     - incidental: `isStamToEPIBridge_of_epi` (consumer 0 件) は Phase A 完了時に retract、`IsStamInequalityResidual` Stam wall hyp 漏れ構造は closure plan 対応、stale doc reference 4 件 (`FisherInfoV2DeBruijn.lean:245` 旧 field 名参照 in Cluster C 4 file) は後続 doc-sweep backlog

3. **2026-05-27 — Phase 2.C を A3 pivot (`@audit:suspect` → `@audit:ok` 直接昇格)**:
   - 当初設計 (shared sorry 補題化) を proof-pivot-advisor + honesty-auditor verdict で reject。`integral_logDeriv` 2 件は body 12-13 行 genuine + field 側は regularity 帰結 (Phase 2.A engine substitution と非同型) → 直接 `@audit:ok` 昇格で対応、structure refactor / wall promote / Cluster C ripple すべて不要

2. **2026-05-27 — Phase 2.B 強化版へ pivot (Phase 2.A no-op launder verdict 反映)**:
   - Phase 2.A 実装 (commit `c0edc35`、candidate 1 default: shared sorry 補題 `debruijnIdentityV2_holds` 経由) → 独立 audit verdict (commit `a6ae83b`) = DEFECT (no-op launder): 結論型 ≡ field 型 verbatim、`exact h_reg.field` で trivial 閉じる、`wall:debruijn-integration` 未到達
   - 決定: Phase 2.A 現状維持 (defect marker で acknowledge) + Phase 2.B を強化版に pivot、L-INT-2-α の retreat 方向を逆転 (candidate 2 = field 削除を default)
   - スコープ拡大: 元 tier 5 defect 5 件 + Phase 2.A 産物 (L1/L2) + auditor 追加発見 2 件 (L4/D5') = 8 declaration touch
   - 規模見積もり update: Phase 2 ~500-900 行 / 3-5 session に上方修正

1. **2026-05-27 — 本 plan 起草 (Phase 0 完了)**:
   - Phase A 完了 (`20ee48b`) で FisherInfo cluster sorry-based migration 解禁、`fisher-info-sorry-migration-plan` の Pattern G escalate「単独 sweep 禁止」結論の実行 plan として起草
   - 4 cluster 構成確定 + Phase 分割 sequential (C → B → D) 固定 + Cluster A default 独立 (skip)、規模見積もり ~1000 行 / 7 session

---

## 関連 Files

- SoT: `docs/audit/audit-tags.md` + `docs/audit/sorry-migration-runbook.md`
- 親 / 前提 plan: `docs/shannon/epi-stam-discharge-plan.md` (38/39 ok)、`epi-stam-to-conclusion-plan.md` (Phase A 完了 `20ee48b`)、`epi-stam-to-conclusion-phaseA-plan.md`、`fisher-info-sorry-migration-plan.md` (Phase 0 全降格判定の解禁)
- 周辺 plan: `epi-debruijn-integration-plan.md` / `-phaseD-plan.md`、`epi-debruijn-regularity-refactor-plan.md`、`fisher-info-moonshot-plan.md`、`fisher-info-gaussian-discharge-moonshot-plan.md`、`parallel-gaussian-*` 4 件 (Cluster A 独立 candidate)
- roadmap: `docs/textbook-roadmap.md` (Ch.17 EPI frontier、Phase 3.C rename 対象)
- Cluster 主 file: `Common2026/Shannon/EntropyPowerInequality.lean` (D anchor)、`EPIStamDischarge.lean` / `EPIStamToBridge.lean` / `EPIL3Integration.lean` (C)、`FisherInfoV2DeBruijn.lean` / `FisherInfoV2DeBruijnBody.lean` / `FisherInfoV2HeatFlowBody.lean` (B tier 5 defect 所在)

## 計数 — Phase 0 baseline

- `@audit:suspect`: 22 件 (Cluster B 5 + Cluster C 17)、`@audit:staged`: 8 件、`@audit:retract-candidate`: 23 件 (Phase A cleanup 産物 bookkeeping)、`@audit:closed-by-successor`: 3 件、`@audit:defect`: 2 件 (Cluster D 2 `Prop := True`)、新規 sorry: 0、`@residual`: 10 件、tier 5 defect 未解消: 5 件 (Cluster B、Phase 2 で構造解消)

Phase V Done 時の予測 (中央): 新規 sorry 30+、`@residual` 25+、shared sorry 補題 1-2 件新規 (`debruijnIdentityV2_holds`、`wall:fisher-info-score-zero` は A3 pivot で不要確定)、tier 5 defect 全 5 件解消、touch .lean 13-14 file、commit 7-12 件、session 5-10 件。
