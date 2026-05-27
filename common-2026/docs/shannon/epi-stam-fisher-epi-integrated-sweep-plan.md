# EPI/Stam + FisherInfo + EntropyPowerInequality — 統合 sweep ムーンショット計画 🌙

> **Plan slug**: `epi-stam-fisher-epi-integrated-sweep`
> **Status**: 起草直後 (2026-05-27)。Phase A 完了 (`20ee48b`、`stamToEPIBridge_holds` shared sorry 補題 + `entropy_power_inequality_unconditional` hypothesis-free wrapper publish 済) によって `FisherInfo cluster` の Phase A 共存ブロックが解除されたことを契機に起草される、Cover-Thomas Ch.17 Inequalities + 部分 Ch.8 Differential Entropy を対象とする **4 cluster 統合 sweep**。
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

### Cluster 別 verbatim tag inventory (2026-05-27、Bash で `rg -c` 実行結果を貼付)

| file | suspect | staged | closed-by-succ | defect | retract-cand | @residual | sorry | 🟢ʰ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| **Cluster B (FisherInfo cluster)** | | | | | | | | |
| `FisherInfo.lean` | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `FisherInfoV2.lean` | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `FisherInfoV2DeBruijn.lean` | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `FisherInfoV2DeBruijnBody.lean` | 1 | 0 | 0 | 0 | 0 | 0 | 2 | 0 |
| `FisherInfoV2HeatFlowBody.lean` | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `FisherDeBruijnGaussianWitness.lean` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `FisherInfoGaussian.lean` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **Cluster C (EPI/Stam)** | | | | | | | | |
| `EPIStamDischarge.lean` | 0 | 2 | 0 | 0 | 0 | 0 | 1 | 0 |
| `EPIStamToBridge.lean` | 1 | 2 | 0 | 0 | 2 | 9 | 14 | 0 |
| `EPIStamInequalityBody.lean` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `EPIStamStep12Body.lean` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `EPIStamStep3Body.lean` | 7 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `EPIStamDeBruijnConclusion.lean` | 0 | 0 | 0 | 0 | 4 | 0 | 0 | 0 |
| `EPIL3Integration.lean` | 9 | 3 | 0 | 0 | 15 | 0 | 2 | 0 |
| `EPIPlumbing.lean` | 0 | 1 | 0 | 0 | 0 | 0 | 1 | 0 |
| `StamGaussianBound.lean` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| **Cluster D (EntropyPowerInequality)** | | | | | | | | |
| `EntropyPowerInequality.lean` | 0 | 0 | 3 | 2 | 2 | 1 | 7 | 0 |
| **Cluster A (ParallelGaussianPerCoord — 独立候補)** | | | | | | | | |
| `ParallelGaussianPerCoordRegularity.lean` | 0 | 0 | 0 | 0 | 0 | 1 | (要再確認) | 0 |
| **Cluster B+C+D total** | **22** | **8** | **3** | **2** | **23** | **10** | **27** | **0** |

**カウント note**:
- `@audit:retract-candidate` 23 件は Phase A cleanup (`e7b779e` / `20ee48b`) で導入された **bookkeeping** (削除候補マーカー、`load-bearing-predicate` 理由)、tier 3 で本 sweep の移行対象外。ただし sweep 進行中に `retract` を実際に断行する場面で touch する可能性。
- `@audit:closed-by-successor` 3 件は `EntropyPowerInequality.lean` の `IsStamInequalityHypothesis := True` / `IsDeBruijnIntegrationHypothesis := True` / `isStamToEPIBridge_of_epi` で、tier 5 `@audit:defect(prop-true)` 併用済 (本 plan Phase 3 で sorry-based migration 対象、ただし subtle case)。
- `@audit:staged(epi-debruijn-regularity)` (EPIStamDischarge `:146`) は **structure refactor 済**で staged 留め (load-bearing structure carries genuine `HasDerivAt` content)、本 sweep の主要 migration 対象ではない。

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

### Phase 分割の依存方向 (sequential 必須、cluster 跨ぎ並列禁止)

```
Phase 0 (verbatim inventory + tier 5 defect 確定 + Cluster A 統合 / 独立判定)
   │   docs-only、本 session の出力
   ▼
Phase 1 (Cluster C — EPI/Stam) — sweep の前段、Cluster B refactor の consumer 範囲確定
   │   Cluster B の signature 改変が Cluster C の active consumer に ripple するので、
   │   Cluster C の現状 sorry / suspect / staged を先に整理して「Cluster B refactor 後に
   │   どの shape で受け取り直すか」の anchor を固める。
   ▼
Phase 2 (Cluster B — FisherInfo cluster) — tier 5 defect 5 件 + suspect 5 件
   │   `IsRegularDeBruijnHypV2` structure refactor + 5 件 signature 改変。
   │   Phase 1 で anchor が固まった shape を target に書き換え。
   ▼
Phase 3 (Cluster D — EntropyPowerInequality + DeBruijn integration)
   │   `IsStamInequalityHypothesis := True` / `IsDeBruijnIntegrationHypothesis := True`
   │   の sorry-based migration。`entropy_power_inequality_gaussian_saturation` rename 検討。
   ▼
Phase 6 (Cluster A — ParallelGaussianPerCoord) — 独立判断、Phase 0 で統合 / 独立を確定
   │   統合の場合は Phase 4 / 5 として組み込み、独立の場合は別 plan に外出し。
   ▼
Phase V (全 13 file `lake env lean` + honesty-auditor × 3 cluster 並列 audit)
```

**cluster 跨ぎ並列の禁止理由**: Phase 1 と Phase 2 を並列にすると、Phase 2 の `IsRegularDeBruijnHypV2` refactor が Phase 1 の `EPIStamDeBruijnConclusion` / `EPIL3Integration` の現状 sorry / suspect 整理と signature 衝突。Phase 1 完了 (anchor 固定) → Phase 2 (refactor) → Phase 3 (主定理露出層整理) の sequential が strictly necessary。

### Phase 内部の並列度判断

Phase 内部の **declaration 独立 sub-step** は **並列 (worktree + .lake symlink)** 可:

- **Phase 1 並列可**: `EPIStamStep3Body.lean` 7 件 (Lagrange optimization) は互いに独立、`EPIStamToBridge.lean` 内の 9 `@residual` も互いに独立な sub-step として並列可。
- **Phase 2 sequential 必須**: tier 5 defect 5 件は **連鎖** (defect 1 → 2 → 3 → 4 → 5 で literal alias chain)、refactor は **1 declaration ずつ sequential**。`IsRegularDeBruijnHypV2` structure refactor → `IsIBPHypothesis` def 書換 → 各 consumer signature 書換 → 検証、を **1 session = 1 declaration** で進める。
- **Phase 3 並列可**: `IsStamInequalityHypothesis` + `IsDeBruijnIntegrationHypothesis` + `entropy_power_inequality_gaussian_saturation` rename は独立 sub-step として並列可。
- **Phase V audit 並列**: 3 cluster 別 honesty-auditor を並列 dispatch (`isolation` 省略 OK、docs-only agent)、file 所有権で衝突回避。

### wall 集約戦略

- Phase 1: `EPIStamToBridge.lean` 9 件 `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` の wall 集約 vs plan-slug 維持を再判定 (同 wall declaration が 2+ family で再利用される予兆あれば集約)。
- Phase 2: `wall:debruijn-integration` の L1 closure point 確立 (登録済、commit `23dae39`)。
- Phase 2.C: `wall:fisher-info-score-zero` 新規 promote 留保 → **不要確定** (A3 pivot、Phase 2.C 内参照)。

### 第一選択 (定義書換) ルートの確認 — CLAUDE.md「Mathlib-shape-driven Definitions」遵守

tier 5 defect 5 件の置換型は **Mathlib `HasDerivAt` 結論形に整合** させる方針:

- **`IsIBPHypothesis` 書換**: `def IsIBPHypothesis ... : Prop := HasDerivAt (...) (...) t` のまま literal alias を維持するのではなく、性質を **別 theorem** `isIBPHypothesis_holds` (body `sorry` + `@residual(wall:debruijn-integration)`) に分離。`isIBPHypothesis_iff` (`Iff.rfl`) は廃止候補。
- **`IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field 書換**: structure field を `derivAt_entropy_eq_half_fisher_v2 : HasDerivAt ... ((1/2) * fisherInfoOfDensityReal density_t) t` 形のまま **残す** (regularity precondition として honest)、ただし `deBruijn_identity_v2` body が `h_reg.derivAt_entropy_eq_half_fisher_v2` の直接抽出にならないよう、別 shared sorry 補題 `debruijnIdentityV2_holds` (body `sorry` + `@residual(wall:debruijn-integration)`) を間に挟む。
- **`deBruijn_identity_v2` body 書換**: `:= h_reg.derivAt_entropy_eq_half_fisher_v2` → `debruijnIdentityV2_holds X Z P t h_reg` の呼び出し形 (shared sorry 補題経由)。

**判定の一言** (CLAUDE.md): 「その仮説は前提条件 (regularity) か、それとも証明の核心 (load-bearing) か」。
- `IsRegularDeBruijnHypV2.density_t` / `Z_law` / `density_path` / `density_t_eq` field → **regularity precondition** (Phase A の structure refactor で `density_t_eq` pin が確立済、retain OK)
- `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field → **load-bearing** (de Bruijn identity の結論を field として bundle)、本 sweep で structure 内に残すが consumer (`deBruijn_identity_v2` body) は shared sorry 補題経由に変える

### 段階的 ship 設計 (Tier 0 / 1 / 2)

- **Tier 0 (Phase 0 docs-only)**: 本 plan + verbatim inventory + tier 5 defect 確定 + Cluster A 統合 / 独立判定。docs-only commit (本 session で完了)。
- **Tier 1 (Phase 1 + Phase 3)**: Cluster C + Cluster D の sweep (FisherInfo refactor 無しで完結する範囲)。`EPIStamStep3Body.lean` 7 件 Lagrange + `EPIStamToBridge.lean` 9 `@residual` + `EntropyPowerInequality.lean` 2 `Prop := True` の処理。partial publish 価値あり (`@audit:suspect` 7 件 → `@residual` 移行 + 2 件 `Prop := True` → sorry-based)。
- **Tier 2 (Phase 1 + Phase 2 + Phase 3 + Phase V)**: FisherInfo cluster structure refactor 完遂 + 13 file 全 `lake env lean` clean + honesty-auditor 3 cluster pass。

### 規模見積もり (中央予測)

~1000 行 / 7 session。Phase 2 が支配的 (~500-900 行 / 3-5 session、強化版で上方修正済)。

## 進捗

- [ ] Phase 0 — verbatim inventory + tier 5 defect 確定 + Cluster A 判定 + wall 集約初期判定 📋
- [ ] Phase 1 — Cluster C (EPI/Stam) sweep: suspect 7 + `@residual` 9 + staged 2 整合 📋
- [ ] Phase 2 — Cluster B (FisherInfo) refactor: tier 5 defect 5 件 + structure refactor 📋
- [ ] Phase 3 — Cluster D (EntropyPowerInequality) sweep: 2 `Prop := True` migration + rename 検討 📋
- [ ] Phase 6 — Cluster A (ParallelGaussianPerCoord) — Phase 0 判定次第 (default skip) 📋
- [ ] Phase V — 全 13 file `lake env lean` + honesty-auditor × 3 cluster 並列 audit 📋

proof-log: yes (各 Phase 完了時に `docs/shannon/proof-log-epi-stam-fisher-epi-integrated-sweep-phase-<N>.md`)

---

## Phase 0 — verbatim inventory + Cluster A 判定 + wall 集約初期判定 📋

> docs-only Phase。Context 節の verbatim tag inventory 表 + tier 5 defect 表で完了済 (本 plan 起草 commit 内)。

残 step:
- Cluster A (ParallelGaussianPerCoord) 統合 / 独立 / skip 判定: **default 独立** (Cluster B/C/D との signature 連動薄い、`fisher-info-sorry-migration-plan` Round 4 candidate も別 sweep)、`ParallelGaussianPerCoordRegularity.lean` 1 `@residual` + parallel-gaussian-* plan の Phase 進捗を verbatim 確認後に最終確定 → Phase 6 セクション。
- wall 集約初期判定: `wall:stam` は EPI/Stam family primary owner で保持、`EPIStamToBridge.lean` 9 件は plan-slug 維持 default (Phase 1 で再判定)、`wall:debruijn-integration` / `wall:fisher-info-score-zero` は新規 promote 留保 (Phase 2/3 で判定 — 後者は A3 pivot で不要確定)。

**L-INT-0-α**: Cluster A 統合が strictly necessary と判明 → Phase 4/5 追加、規模見積もり update。default 独立で発火確率低。

---

## Phase 1 — Cluster C (EPI/Stam) sweep 📋

### スコープ (verbatim、Phase 0 inventory に依拠)

**対象 file (9 file、Phase 0 inventory 表 Cluster C より)**:

| file | suspect | staged | `@residual` | sorry | Phase 1 処遇 |
|---|---:|---:|---:|---:|---|
| `EPIStamDischarge.lean` | 0 | 2 | 0 | 1 | staged 2 件確認 (refactor 済 honest)、sorry 1 件は Phase A 残置確認 |
| `EPIStamToBridge.lean` | 1 | 2 | 9 | 14 | suspect 1 件 sorry-based migration、`@residual` 9 件 + sorry 14 件は Phase A 残置の整理 (`epi-stam-to-conclusion-phaseA-plan` slug 整合性確認) |
| `EPIStamInequalityBody.lean` | 0 | 0 | 0 | 0 | touch せず (`@audit:ok` 状態維持) |
| `EPIStamStep12Body.lean` | 0 | 0 | 0 | 0 | touch せず |
| `EPIStamStep3Body.lean` | 7 | 0 | 0 | 0 | 7 件 suspect → sorry-based migration (各 declaration `@audit:suspect(epi-stam-to-conclusion-plan)` → `@residual(plan:epi-stam-to-conclusion-plan)` + signature 確認 + body sorry 化) |
| `EPIStamDeBruijnConclusion.lean` | 0 | 0 | 0 | 0 | `@audit:retract-candidate(load-bearing-predicate)` 4 件は bookkeeping、touch せず |
| `EPIL3Integration.lean` | 9 | 3 | 0 | 2 | suspect 9 件 sorry-based migration、staged 3 件 (csiszar / epi-debruijn-integration / epi-heat-flow-family-regularity) 整合確認、sorry 2 件は Phase A 残置確認 |
| `EPIPlumbing.lean` | 0 | 1 | 0 | 1 | staged 1 件 (epi-stam-to-conclusion-plan) 整合確認、sorry 1 件は Phase A 残置 |
| `StamGaussianBound.lean` | 0 | 0 | 0 | 0 | touch せず |

**Phase 1 主要 migration 対象**: **suspect 17 件** (EPIStamStep3Body 7 + EPIL3Integration 9 + EPIStamToBridge 1)。

### Approach

- **sub-step A**: `EPIStamStep3Body.lean` 7 件 sorry-based migration (Lagrange optimization)。各 declaration の **load-bearing hypothesis 解除** → body sorry → `@residual(plan:epi-stam-to-conclusion-plan)` 付与。各 declaration は互いに独立で **並列 dispatch 可** (worktree + .lake symlink boilerplate、`lean-implementer` × 7、または 2-3 group に分けて batch)。

- **sub-step B**: `EPIL3Integration.lean` 9 件 suspect の slug 整合性確認 + sorry-based migration。slug は混在 (`epi-debruijn-integration-plan` 1 件 + `epi-debruijn-tail-reintroduction-plan` 2 件 + `epi-debruijn-integration-phaseD-plan` 5 件 + `epi-debruijn-integration-plan` 1 件)、Phase A 完了の sister cleanup 委譲 (`epi-stam-to-conclusion-plan.md` Phase A Done 条件で「14 件一括書換 → `closed-by-successor(epi-stam-to-conclusion-plan)`」と既述) との整合性を確認。

- **sub-step C**: `EPIStamToBridge.lean` suspect 1 件 (`IsStamToEPIScalingHyp` `:147`) は `epi-stam-discharge-plan.md` で「retract candidate sister」と既述、本 sweep で **retract 断行** or **sorry-based 残置** を判定。9 `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` は Phase A 内部残置 (proof-log-epi-stam-to-conclusion-phase-a.md 由来) なので、Phase A 完了 commit の slug 整合確認のみ。

- **sub-step D**: staged 2 件 (`epi-debruijn-regularity` / `epi-debruijn-integration`) は EPIStamDischarge `:146 / :248` で structure refactor 済 honest、touch せず (load-bearing structure が genuine `HasDerivAt` content を carry)。

### Phase 1 並列 dispatch 設計 (orchestrator brief)

- **Wave 1-A**: `EPIStamStep3Body.lean` 7 件 を 3 group に分け、`lean-implementer` × 3 並列 dispatch (worktree + .lake symlink、boilerplate 全項目)。各 brief は CLAUDE.md「Brief content checklist」遵守 (sub-bound 引数表 + 継承タグ語彙整合 inline check)。
- **Wave 1-B**: `EPIL3Integration.lean` 9 件は file 共有のため **single dispatch** (`lean-implementer` 1 件、worktree 省略)、または file 内 declaration 群を 2-3 commit に分割。
- **Wave 1-C**: `EPIStamToBridge.lean` suspect 1 件 + `@residual` 9 件 slug 整合性確認 = **single dispatch**。

### Done 条件

- suspect 17 件全件、`@residual(plan:<slug>)` (slug は本 plan / `epi-stam-to-conclusion-plan` / Phase A 由来から選択) 形式に migration 完了
- 9 file 全 `lake env lean` 0 errors
- 各 sorry に `@residual(<class>:<slug>)` 付き (tier 2 honest)
- honesty-auditor (`subagent_type: "honesty-auditor"`) を fresh dispatch、Phase 1 cluster 全件 verdict PASS (新規 sorry 17+ 件、起動条件全該当)

### 撤退ライン

- **L-INT-1-α** (許容): `EPIStamStep3Body.lean` 7 件のうち、Phase A の `stamToEPIBridge_holds` shared sorry 補題で transitive 解消する declaration が含まれることが判明 → suspect → `@residual` migration の代わりに **既存 shared sorry 補題経由の closure**。docstring で「`stamToEPIBridge_holds` 経由で closure 済」と honest 明示、`@audit:ok` 昇格 (本来の sweep より strict honest)。発火確率 低 (Phase A は EPI 主定理 path のみ通過、Lagrange optimization は別経路)。
- **L-INT-1-β** (許容): `IsStamToEPIScalingHyp` retract 断行が consumer 20+ 件に大規模 ripple → **retract 延期**、sorry-based 残置で migrate のみ。docstring で「retract 延期、closure 後の cleanup task として記録」明示。
- **L-INT-1-γ** (defect 発見時の停止): Phase 1 進行中に新規 tier 5 defect (`Prop := True` / 循環 `:= h` / load-bearing hyp / 退化定義悪用 / name laundering) を発見 → 即座にユーザに defect 報告、本 Phase の進行を停止し orchestrator に honest-auditor 起動依頼。CLAUDE.md「検証の誠実性」"見つけた側" inline policy 遵守。

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

#### Phase 2.A — `IsRegularDeBruijnHypV2` structure refactor (実施済、no-op launder と判定)

実装 (commit `c0edc35`、candidate 1 = structure 保持 + shared sorry 補題 `debruijnIdentityV2_holds` 経由) → 独立 audit (commit `a6ae83b`) で no-op launder と判定 (結論型 ≡ F1 field 型 verbatim、`exact h_reg.field` で trivial 閉じる)。defect marker で acknowledge して現状維持、本 Phase 2.B で candidate 2 (field 削除) を default 採用に逆転。

#### Phase 2.B — foundation (F1 field 削除) + 4 launder cleanup + tier 5 defect 連鎖解消

> Phase 2.A (commit `c0edc35`、candidate 1: structure 保持 + shared sorry 補題経由) は独立 audit (commit `a6ae83b`) で no-op launder と判定 → defect marker で acknowledge して現状維持、本 Phase 2.B で field 削除 default に逆転。経緯 → 判断ログ。

##### スコープ表 (verbatim line 確認済、2026-05-27)

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

合計 8 declaration に touch (F1 1 + L1-L4 = 4 launder + D1 1 + D5 + D5' = 2 transitive)。元 plan §Phase 2.B の 5 件 (defect 1-5) は本表で D1 / L3 / F1 / L2 / D5 に対応、4 launder cleanup (L1-L4) のうち L1-L2 は Phase 2.A 産物の重複処理、L3-L4 は元 defect 2 + 追加発見の合流。

#### Approach 強化版 (3 段、sequential、foundation を最初に置く)

##### 段 1 — foundation: F1 field 削除 + L4 constructor 縮小 + L1 retract

**F1 削除**: `IsRegularDeBruijnHypV2` structure を以下に縮小 — `Z_law : P.map Z = gaussianReal 0 1` + `density_t : ℝ → ℝ`。`derivAt_entropy_eq_half_fisher_v2` field は **削除**。L-INT-2-α (元 plan の「candidate 2 (field 削除) → candidate 1 retreat」) は Phase 2.A no-op launder verdict で **方向逆転**: candidate 2 (field 削除) を default、retreat 先は「field 削除困難時に complete sorry-based migration で 8 declaration を残置」。

**L4 縮小**: `IsRegularDeBruijnHypV2.ofHeatFlow` constructor から `derivAt_entropy_eq_half_fisher_v2 := h_ibp` 行を削除 (field 自体消失で自動的に). `(h_ibp : IsIBPHypothesis X Z P p t)` 引数も削除候補 (constructor の他 field 設定で `h_ibp` を使わないなら、L3 と L4 が別関数になる)。

**L1 retract**: `debruijnIdentityV2_holds` は Phase 2.A audit verdict で no-op launder と判定済。F1 field 削除後は、本 shared sorry 補題が genuine wall closure point (heat eq + IBP + dominated bound の Mathlib 不在) に昇格。**選択肢 A** (default): L1 を残置 + body `sorry` + `@residual(wall:debruijn-integration)` を維持 (audit docstring の `@audit:defect(launder)` は削除、genuine wall に昇格)、L2 / L3 / D5 / D5' の closure point として共有。**選択肢 B**: L1 を削除し L2 body を直接 `sorry` + `@residual(wall:debruijn-integration)` (shared 集約しない)、L3 / D5 / D5' も個別 sorry。集約効率上 default は A。

##### 段 2 — launder declaration cleanup (L2 / L3 / D5 / D5')

F1 削除 + L1 status 固定後の sequential 順序:

1. **L2** (`deBruijn_identity_v2` body): F1 削除で signature は `HasDerivAt ... ((1/2) * fisherInfoOfDensityReal h_reg.density_t) t` (RHS は `density_t` field 経由のみ残存)。body は `debruijnIdentityV2_holds X Z hX hZ hXZ ht h_reg` (選択肢 A) — honest pass-through に昇格 (`@audit:ok` 候補)。
2. **L3** (`deBruijn_identity_v2_of_heat_flow` body): 現 `h_ibp` literal alias を、F1 削除版 `IsRegularDeBruijnHypV2` を構成 + `debruijnIdentityV2_holds` 呼出に書換。signature は `... (h_heat : IsHeatFlowDensity X Z P p) (h_ibp : IsIBPHypothesis X Z P p t) : HasDerivAt (...) ((1/2) * fisherInfoOfDensityReal (p t)) t`、body は `h_ibp` の literal alias (D1 def による) を解消して `IsIBPHypothesis` def を unfold + `debruijnIdentityV2_holds` 呼出。**選択肢 (i)** literal alias を維持しつつ `IsIBPHypothesis` を **retract candidate** にする (D1 への対処へ pivot)、**選択肢 (ii)** L3 を完全削除 (consumer は `FisherDeBruijnGaussianWitness` 経由のみ、L1/L2 path に統合)。Phase 2.B では選択肢 (i) を default。
3. **D5** (`deBruijn_identity_v2_of_heat_subhyp`): L3 解消後の新 signature 経由に書換。transitive、機械的。
4. **D5'** (`IsRegularDeBruijnHypV2.ofHeatSubhyp`): L4 (constructor 縮小) と signature 整合確認、`h_ibp` 引数の扱いを統一。

##### 段 3 — D1 (`IsIBPHypothesis` def) 処遇判定

D1 は `def IsIBPHypothesis ... := HasDerivAt ... ((1/2) * fisherInfoOfDensityReal (p t)) t` の literal alias predicate。L3 / D5 / D5' / `FisherDeBruijnGaussianWitness.lean:43/51` の 4 consumer が残る (前 3 件は段 2 で書換、後者は touch せず該当 file の Phase 2 処遇は「touch せず」)。

- 全 consumer が段 2 で書換完了かつ `FisherDeBruijnGaussianWitness` を touch しないなら、**`@audit:retract-candidate(name-laundering-alias)` を付与し alias 維持** (本 sweep では retract 断行しない、後続 plan に委譲)。
- 完全 retract は Phase 2.B scope 外 (Gaussian witness file への ripple が Cluster B/C 境界を越え本 sweep 規模超過)、L-INT-2-β に該当。

#### wall residual closure point — F1 削除後

F1 field 削除によって L1 `debruijnIdentityV2_holds` body の `@residual(wall:debruijn-integration)` が genuine wall closure point に昇格 (no-op launder verdict 解消、audit docstring の `@audit:defect(launder)` のみ削除)。Wall register 登録 (commit `23dae39`) 維持。`IsIBPHypothesis` direct (D1) は literal alias predicate にすぎず closure point に使うと Phase 2.A と同型の no-op 再発、L1 が正しい anchor。

### Phase 2 並列 dispatch 設計 (強化版) — **sequential 厳守**

- **Wave 2-A (foundation 段 1)**: F1 削除 + L4 縮小 + L1 status 固定 (audit docstring 整理 + `@audit:defect(launder)` 削除) = **single dispatch** (`lean-implementer` 1 件、worktree 省略可、`Common2026/Shannon/FisherInfoV2DeBruijn.lean` + `FisherInfoV2DeBruijnBody.lean` 2 file 連動 touch)。
- **Wave 2-B (cleanup 段 2)**: L2 → L3 → D5 → D5' を **sequential** 1 declaration = 1 dispatch + 1 commit (literal alias chain 逆順、4 dispatch)。並列禁止理由: L3 signature が L2 / D5 / D5' すべてに ripple、間に LSP 同期境界を入れないと型 mismatch 連鎖。
- **Wave 2-C (段 3 + Cluster B 残)**: D1 処遇判定 (alias 維持 + `@audit:retract-candidate` 付与、本 sweep では retract せず) は L2-D5' commit と合流して 1 dispatch + Phase 2.C (`FisherInfo.lean:127` / `FisherInfoV2.lean:157` `integral_logDeriv` 2 件) と並列可 (file 別)。

> **foundation 段 1 を最初に sequential**: F1 削除が L1-L4 signature の prerequisite。並列にすると olean refresh round-trip が L1-L4 dispatch 毎に発生 (`lake build Common2026.Shannon.FisherInfoV2DeBruijn` 4 回)。foundation 1 dispatch で signature が確定すれば後続段は signature 安定下で進行。

#### Phase 2.C — `FisherInfo.lean:113` / `FisherInfoV2.lean:151` `integral_logDeriv` 2 件 sweep

> **2026-05-27 A3 pivot**: 当初設計 (shared sorry 補題化) を reject、`@audit:suspect` → `@audit:ok` 直接昇格に pivot。`wall:fisher-info-score-zero` 新規 promote 不要。Phase 2.A 教訓の過剰一般化を避けた判断。

##### 改訂内容

- `FisherInfo.lean:111` / `FisherInfoV2.lean:149` の `@audit:suspect(fisher-info-moonshot-plan)` → `@audit:ok` 置換 + Gaussian instance discharge 参照を docstring に追記
- structure refactor / shared sorry 補題追加 / Wall register 追記 / Cluster C ripple すべて不要

##### A3 採用根拠 (verdict サマリ)

- **body は genuine 12-13 行 proof**: pointwise `logDeriv f · f = deriv f` (positivity) → `integral_congr_ae` → `integral_deriv_eq_zero` field 呼出
- **field は regularity 帰結 (not load-bearing)**: `Differentiable + Tendsto atBot/atTop (nhds 0) + Integrable (deriv f)` から FTC + tail-vanishing で導出可、Cover-Thomas 17.7 核心ではなく FTC step のみ bundle
- **Gaussian instance で genuine discharge 済**: `isRegularDensity_gaussianReal_of_law` (`FisherInfoGaussian.lean:280`) で 7 field 全て hypothesis-free 構築、`integral_deriv_gaussianPDFReal_eq_zero` (closed form ~45 行)
- **Phase 2.A 非同型**: Phase 2.A は `density_t` engine substitution のみで `exact h_reg.field` 1 段 trivial closure。本 Phase は positivity-keyed pointwise bridge を間に挟むので engine substitution **不成立**

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

### Done 条件 (Phase 2、強化版)

- **段 1**: F1 field 削除 + L4 constructor 縮小 + L1 status 固定 (audit docstring の `@audit:defect(launder)` 削除、`@residual(wall:debruijn-integration)` のみ残す) 完了
- **段 2**: L2 / L3 / D5 / D5' 4 件で launder pattern (`exact h_reg.field` / `:= h_ibp` / 1 段 indirection alias) **0 件** (`rg -n ':= h_ibp\|:= h_reg\.derivAt\|debruijnIdentityV2_holds.*h_reg$' Common2026/Shannon/Fisher*.lean` で 0 hit)
- **段 3**: D1 (`IsIBPHypothesis`) に `@audit:retract-candidate(name-laundering-alias)` 付与済 (本 sweep では retract せず、alias 維持)
- **Cluster B 5 file 全 `lake env lean` 0 errors** (FisherInfo / FisherInfoV2 / FisherInfoV2DeBruijn / FisherInfoV2DeBruijnBody / FisherInfoV2HeatFlowBody)
- **Cluster C consumer ripple 確認**: `lake build Common2026.Shannon.FisherInfoV2DeBruijn` で olean refresh → `EPIStamToBridge.lean` (3 件 `(h_reg.reg_at t ht).derivAt_entropy_eq_half_fisher_v2` 抽出 → `deBruijn_identity_v2` 呼出に書換) + `EPIStamDeBruijnConclusion.lean:144` (density_t access のみ、ripple なし確認) + `EPIL3Integration.lean:678` (Gaussian witness lift constructor、F1 field 削除で `derivAt_entropy_eq_half_fisher_v2 := ?_` 行削除 → `h_deriv` 由来の代替 closure path に書換) + `FisherDeBruijnGaussianWitness.lean` (touch せずに済むか確認、必要なら incidental 追記) で 0 errors
- **honesty-auditor 独立 audit**: 新規 sorry / signature 改変 / structure refactor を fresh dispatch で audit、verdict PASS。特に L1 が **no-op launder から genuine wall closure point に昇格したか** を verbatim check 必須 (F1 field 削除で結論型 ≡ field 型の冗長性が消えた、と confirm)

### 検証手順 (Phase 2、強化版)

```bash
# 段 1 完了時
lake env lean Common2026/Shannon/FisherInfoV2DeBruijn.lean
lake env lean Common2026/Shannon/FisherInfoV2DeBruijnBody.lean
lake build Common2026.Shannon.FisherInfoV2DeBruijn  # olean refresh

# 段 2 完了時 (各 declaration commit 後に逐次)
lake env lean Common2026/Shannon/FisherInfoV2DeBruijn.lean
lake env lean Common2026/Shannon/FisherInfoV2DeBruijnBody.lean
lake env lean Common2026/Shannon/FisherInfoV2HeatFlowBody.lean

# Cluster C ripple
lake env lean Common2026/Shannon/EPIStamToBridge.lean
lake env lean Common2026/Shannon/EPIStamDeBruijnConclusion.lean
lake env lean Common2026/Shannon/EPIL3Integration.lean
lake env lean Common2026/Shannon/FisherDeBruijnGaussianWitness.lean

# launder pattern 撲滅確認 (段 2 + 段 3 完了時)
rg -n ':= h_ibp' Common2026/Shannon/Fisher*.lean
rg -n ':= h_reg\.derivAt_entropy_eq_half_fisher_v2' Common2026/Shannon/
# 両方とも 0 hit が Done 条件
```

---

## Phase 3 — Cluster D (EntropyPowerInequality) sweep 📋

> **Phase 2 完了前提** (Cluster B structure refactor 完了)。

### スコープ

**対象 file (1 file、Phase 0 inventory 表 Cluster D より)**:

| file | suspect | closed-by-succ | defect | retract-cand | `@residual` | sorry | Phase 3 処遇 |
|---|---:|---:|---:|---:|---:|---:|---|
| `EntropyPowerInequality.lean` | 0 | 3 | 2 | 2 | 1 | 7 | 2 件 `@audit:defect(prop-true)` の sorry-based migration + `entropy_power_inequality_gaussian_saturation` rename 検討 |

### Approach

#### Phase 3.A — `IsStamInequalityHypothesis := True` migration

- 現状 (`EntropyPowerInequality.lean:144-145`): `def IsStamInequalityHypothesis ... : Prop := True`
- tag: `@audit:defect(prop-true)` `@audit:closed-by-successor(epi-stam-discharge-plan)`
- 第一選択 (定義書換): `IsStamInequalityResidual` (line 197+) が **既に publish 済** で genuine residual 形を carry している。本 declaration は **retract candidate** (consumer は `isStamInequalityHypothesis_of_stamInequalityHyp` `:111` の bridge wrapper 1 件のみ、`isEntropyPowerInequalityHypothesis_of_gaussian` `:331` 内で `IsEntropyPowerInequalityHypothesis` 経由消費)、本 sweep で **retract 断行** が default
- 書換: `IsStamInequalityHypothesis` def を削除 (consumer の bridge wrapper も削除)、または `def IsStamInequalityHypothesis := IsStamInequalityResidual` (literal alias) + `@audit:retract-candidate(name-laundering-alias)` (defect 1 と同じ defect kind、tier 5 で暫定残置)
- **判定基準**: consumer の bridge wrapper `isStamInequalityHypothesis_of_stamInequalityHyp` (`EPIStamDischarge.lean:111`) を retract できれば断行、wrapper が EPI/Stam の API contract で残っている場合は alias 維持

#### Phase 3.B — `IsDeBruijnIntegrationHypothesis := True` migration

- 現状 (`EntropyPowerInequality.lean:160-161`): `def IsDeBruijnIntegrationHypothesis ... : Prop := True`
- tag: `@audit:defect(prop-true)` `@audit:closed-by-successor(epi-debruijn-integration-plan)`
- consumer 確認 (`rg -n 'IsDeBruijnIntegrationHypothesis' Common2026/`): verbatim 確認後判定
- consumer 0 件なら **retract 断行**、1+ 件あれば Phase 2 の `IsRegularDeBruijnHypV2` 経由の代替 predicate に書換

#### Phase 3.C — `entropy_power_inequality_gaussian_saturation` rename 検討

- 現状 (`EntropyPowerInequality.lean:295`): Gaussian case で **等号成立** `entropyPower (P.map (X+Y)) = entropyPower (P.map X) + entropyPower (P.map Y)` を full discharge
- Cover-Thomas Ch.17 で「Gaussian は EPI 等号成立」が headline、name `_gaussian_saturation` は誤解を招く可能性 (saturation = 「飽和して上限に達する」のニュアンス、textbook では「等号成立」は additivity)
- 候補 rename: `entropyPower_gaussian_additivity` (textbook-roadmap Ch.17 frontier 記載項目)
- consumer 数: `rg -n 'entropy_power_inequality_gaussian_saturation' Common2026/` で verbatim 確認、rename 影響範囲評価
- **判定**: consumer 数が小 (< 10 件) なら本 sweep で rename 断行、consumer 数が大なら **rename 延期** (`@audit:rename-candidate` 等の bookkeeping tag を新規 register、または旧 name `def entropy_power_inequality_gaussian_saturation := entropyPower_gaussian_additivity` で alias 経由)

### Phase 3 並列 dispatch 設計

- Phase 3.A + 3.B + 3.C は互いに独立、**並列 3 dispatch 可** (worktree + .lake symlink、`lean-implementer` × 3)

### Done 条件

- 2 件 `Prop := True` placeholder の sorry-based migration (or retract 断行) 完了
- rename 検討の結論 (実施 / 延期) が記録 (実施した場合は consumer 全件書換)
- `EntropyPowerInequality.lean` `lake env lean` 0 errors
- honesty-auditor 新規 sorry / signature 改変を独立 audit

### 撤退ライン

- **L-INT-3-α** (許容、retract 延期): `IsStamInequalityHypothesis` / `IsDeBruijnIntegrationHypothesis` の consumer が 1+ 件で完全 retract 不可 → alias 維持 + `@audit:retract-candidate(name-laundering-alias)` 付与で暫定残置 (tier 5)、後続 plan で alias 解消 task として記録
- **L-INT-3-β** (許容、rename 延期): `entropy_power_inequality_gaussian_saturation` rename の consumer 数が大規模 (10+ 件 or 別 family 跨ぎ) → rename 延期、本 sweep では docstring に「rename pending」明示のみ
- **L-INT-3-γ** (defect 発見時の停止): Phase 3 進行中に新規 tier 5 defect を発見 → 即フラグ、本 Phase 停止

---

## Phase 6 — Cluster A (ParallelGaussianPerCoord) 統合判定 📋

default **独立 (skip)** = 本 sweep 外、`parallel-gaussian-moonshot-plan.md` Phase 進行で継続。Phase 0 step 3 で `ParallelGaussianPerCoordRegularity.lean` 1 `@residual` + parallel-gaussian-* 4 plan の Phase 進捗を Read して signature 連動 (`IsRegularDeBruijnHypV2` / `IsStamInequalityResidual` 経由) を確認、連動あれば Phase 4/5 として統合。

---

## Phase V — 全 13 file `lake env lean` + honesty-auditor × 3 cluster 並列 audit 📋

### スコープ

- **検証 file (13 file)**:
  - Cluster B (7 file): `FisherInfo.lean` / `FisherInfoV2.lean` / `FisherInfoV2DeBruijn.lean` / `FisherInfoV2DeBruijnBody.lean` / `FisherInfoV2HeatFlowBody.lean` / `FisherDeBruijnGaussianWitness.lean` / `FisherInfoGaussian.lean`
  - Cluster C (9 file): `EPIStamDischarge.lean` / `EPIStamToBridge.lean` / `EPIStamInequalityBody.lean` / `EPIStamStep12Body.lean` / `EPIStamStep3Body.lean` / `EPIStamDeBruijnConclusion.lean` / `EPIL3Integration.lean` / `EPIPlumbing.lean` / `StamGaussianBound.lean`
  - Cluster D (1 file): `EntropyPowerInequality.lean`
  - Cluster A (条件付き、1 file): `ParallelGaussianPerCoordRegularity.lean` — Phase 0 判定で統合した場合のみ
- 各 file `lake env lean` 0 errors (sorry warning は許容、各 sorry は `@residual` 付き)
- `Common2026.lean` import 確認 (新規 file `Common2026/Shannon/FisherInfoV2Walls.lean` / `Common2026/Shannon/FisherInfoWalls.lean` 等を Phase 2 で publish した場合、import 1-2 行追加)

### honesty-auditor 起動 (Independent honesty audit、CLAUDE.md 必須)

- **本 sweep の honesty-auditor 起動条件**: 新規 sorry 30+ 件 + signature 改変 40+ 件 + predicate 削除 5+ 件 + 共有 sorry 補題新規追加 (`debruijnIdentityV2_holds` / `integral_logDeriv_pdf_eq_zero_holds`) + `@audit:suspect` / `@audit:staged` の sorry-based 移行 → **全条件該当**、起動必須
- **3 cluster 並列 dispatch**: Cluster B / C / D それぞれに `subagent_type: "honesty-auditor"` を fresh dispatch (file 所有権分離、Cluster B agent は FisherInfo* / FisherDeBruijn* / Cluster C agent は EPI* / Stam* / Cluster D agent は EntropyPowerInequality.lean)、worktree 不要 (docs-only agent、CLAUDE.md「Exception — planner / docs-only agents」)
- 各 audit 出力: 200 行以内サマリ + (必要なら) docstring 内 `@residual` / `@audit:*` タグ refine (Edit 経由、code が SoT)

### 撤退ライン (Phase V)

- **L-INT-V-α** (許容、partial closure): 1 cluster (例: Cluster B の Phase 2.A candidate 1 にも詰まった場合) のみ完了で残りは別 sweep に分割 → partial publish、Phase V の `@audit:ok` 全件昇格は **本 sweep の Done 条件外** であることを再確認 (本 sweep の Done は type-check done、proof done ではない)
- **L-INT-V-β** (許容、honesty-auditor verdict が questionable): `<class>:<slug>` の classification refine を session 中に処理、追加 patch commit。verdict が DEFECT なら session 中に rewrite (sorry-based に書換)、撤回不可なら本 sweep の closure を遅延

### Done 条件

- 13 file (条件付き 14 file) 全 `lake env lean` 0 errors
- honesty-auditor × 3 cluster verdict PASS (or questionable で session 中に refine 済)
- `Common2026.lean` import 確認
- 本 plan の判断ログに「本 sweep closure」エントリ追記 (Phase 別 sorry 数 / `@residual` 数 / `@audit:ok` 昇格件数 / tier 5 defect 解消件数 / wall promote 件数を verbatim 集計)
- 既存 plan (epi-stam-discharge-plan / epi-stam-to-conclusion-plan / fisher-info-sorry-migration-plan / fisher-info-moonshot-plan / epi-debruijn-integration-plan / epi-moonshot-plan) の進捗ブロック update (本 sweep Phase 進行で closure した declaration の `@audit:ok` 昇格 / sorry-based 移行件数を反映)
- `docs/textbook-roadmap.md` Ch.17 EPI frontier 行 update (rename 実施した場合は `entropyPower_gaussian_additivity` で記述)

---

## 撤退ライン総覧 (honest 限定)

| slug | Phase | 内容 | hypothesis 名 (例) / retreat 動作 | 解除条件 |
|---|---|---|---|---|
| L-INT-0-α | 0 | Cluster A 統合判定で「strictly necessary」と判明、Phase 4/5 追加 | — | Phase 0 step 3 判定 |
| L-INT-1-α | 1 | `EPIStamStep3Body.lean` 7 件のうち `stamToEPIBridge_holds` で transitive 解消 → `@audit:ok` 昇格 | (strict honest) | Phase A consumer chain 確認 |
| L-INT-1-β | 1 | `IsStamToEPIScalingHyp` retract 延期、sorry-based 残置で migrate のみ | (alias 維持) | 後続 cleanup task |
| L-INT-1-γ | 1 | Phase 1 進行中に新規 tier 5 defect 発見、停止 | — | orchestrator が honest-auditor 起動 |
| L-INT-2-α | 2 | `IsRegularDeBruijnHypV2` structure refactor candidate 2 (field 削除) で詰まり → candidate 1 (structure 保持 + shared sorry 補題経由) に retreat | (`density_t_eq` pin 整合性で field 保持) | candidate 1 で 5 defect 全 closure 達成 |
| L-INT-2-β | 2 | tier 5 defect 5 件のうち N 件のみ closure、残置分は `@audit:defect(launder)` / `@audit:retract-candidate(load-bearing-predicate)` 暫定マーカー | (tier 5 暫定残置) | 後続 plan で完全 closure |
| L-INT-2-γ | 2 | `wall:debruijn-integration` 新規 promote 留保、`wall:stam` に集約 | (wall 集約) | 別 family で `debruijn-integration` を独立参照する事例が出現 |
| L-INT-3-α | 3 | `IsStamInequalityHypothesis` / `IsDeBruijnIntegrationHypothesis` の retract 延期、alias 維持 | `@audit:retract-candidate(name-laundering-alias)` | 後続 plan で alias 解消 |
| L-INT-3-β | 3 | `entropy_power_inequality_gaussian_saturation` rename 延期 | (docstring 「rename pending」明示のみ) | consumer 数が縮減した時点 |
| L-INT-3-γ | 3 | Phase 3 進行中に新規 tier 5 defect 発見、停止 | — | orchestrator が honest-auditor 起動 |
| L-INT-V-α | V | 1 cluster partial closure、残りは別 sweep に分割 | — | 別 sweep の起動 |
| L-INT-V-β | V | honesty-auditor verdict が questionable → session 中に docstring refine | — | refine commit |

**全撤退ライン共通規律**:
- **`Prop := True` placeholder 禁止** (Phase 3 で 2 件残存している `@audit:defect(prop-true)` は tier 5 暫定マーカー、本 sweep で sorry-based or retract に migrate 必須)
- **結論型 ≡ 仮説型 + `body := h` (循環) 禁止** (Phase 2 tier 5 defect 5 件はすべて循環構造、本 sweep で構造的に解消)
- **load-bearing hypothesis を完成と称する name laundering 禁止** (`*_discharged` / `*_full` / `*_unconditional` 命名を新規導入しない、Phase A で publish 済 `entropy_power_inequality_unconditional` は既存 wrapper として retain)
- **退化定義悪用 禁止** (`density_path := 0` 等の退化境界 case を突いた vacuous instance は Phase A の `density_t_eq` pin で構造的排除済、本 sweep で同種の退化境界悪用を新規導入しない)

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
