# EPI/Stam + FisherInfo + EntropyPowerInequality — 統合 sweep ムーンショット計画 🌙

> **Plan slug**: `epi-stam-fisher-epi-integrated-sweep`
> **Status**: 起草直後 (2026-05-27)。Phase A 完了 (`20ee48b`、`stamToEPIBridge_holds` shared sorry 補題 + `entropy_power_inequality_unconditional` hypothesis-free wrapper publish 済) によって `FisherInfo cluster` の Phase A 共存ブロックが解除されたことを契機に起草される、Cover-Thomas Ch.17 Inequalities + 部分 Ch.8 Differential Entropy を対象とする **4 cluster 統合 sweep**。
> **Created**: 2026-05-27
> **Parent (umbrella)**: 該当 family-level moonshot は存在せず、本 plan が integrated sweep の親計画として機能する。EPI/Stam family の従来 plan 群 (`epi-moonshot-plan` / `epi-stam-discharge-plan` / `epi-stam-to-conclusion-*-plan` / `epi-debruijn-integration-*-plan` / `fisher-info-sorry-migration-plan` / `fisher-info-moonshot-plan` / `fisher-info-gaussian-discharge-moonshot-plan` / `parallel-gaussian-moonshot-plan`) は **all referenced as upstream inputs / closure routes**。本 plan は umbrella で、各 cluster Phase の出力は既存 plan の Phase 状態に逆参照される。

## Context

### 起動契機 (Phase A 完了による FisherInfo 解禁)

`docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` Phase A が 2026-05-27 (commit `20ee48b`) で完了し、以下が確立された:

- `Common2026/Shannon/EntropyPowerInequality.lean:230` `stamToEPIBridge_holds` — shared sorry 補題、`@residual(plan:epi-stam-to-conclusion-plan)` 集約済
- `Common2026/Shannon/EntropyPowerInequality.lean:259` `entropy_power_inequality` — `IsStamInequalityResidual` を取る genuine residual 形主定理 (load-bearing predicate ではない)
- `Common2026/Shannon/EntropyPowerInequality.lean:295` `entropy_power_inequality_gaussian_saturation` — Gaussian case full discharge
- `Common2026/Shannon/EntropyPowerInequality.lean:331` `isEntropyPowerInequalityHypothesis_of_gaussian` — Gaussian 経由 L-EPI3 hypothesis-free
- (位置は要 verbatim 確認) `entropy_power_inequality_unconditional` — hypothesis-free wrapper publish 済 (commit `3db3a9e`)

これにより、`fisher-info-sorry-migration-plan` が Phase 0 で「Case α (全降格)」と判定して保留していた **FisherInfo cluster の sorry-based migration** が起動可能な状態になった。同 plan の「再起動条件 3 件」のうち (1) Phase A 完了は達成、(2) 統合 plan 起草 + (3) `IsRegularDeBruijnHypV2` field restructuring は **本 plan で実施**。

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

### tier 5 defect — Phase A 完了による解消可否判定 (重要)

`fisher-info-sorry-migration-plan.md` で identify された tier 5 defect 5 件の現状 (verbatim 確認、2026-05-27):

| # | declaration | file:line | 構造 | Phase A 完了で解消? | 本 sweep 処遇 |
|---|---|---|---|---|---|
| 1 | `IsIBPHypothesis` (def) | `FisherInfoV2DeBruijnBody.lean:184-190` | `:= HasDerivAt ((1/2) * fisherInfoOfDensityReal (p t)) t` (literal alias to conclusion) | **No** — predicate def 自身が結論型と同一 (Phase A は EPI 主定理 path のみ通過)、Cluster B 内で signature 改変必須 | **Phase 2 (Cluster B) で sorry-based migration** |
| 2 | `deBruijn_identity_v2_of_heat_flow` (theorem) | `FisherInfoV2DeBruijnBody.lean:209-221` | body `:= h_ibp` (literal alias unfold)、結論型 ≡ `IsIBPHypothesis` 展開形 | **No** — defect 1 の literal alias を直接利用、defect 1 解消の前提 | **Phase 2 で sorry-based migration** |
| 3 | `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` (structure field) | `FisherInfoV2DeBruijn.lean:195-249` | structure field が結論型 (`HasDerivAt`) 直接、load-bearing structure field bundling | **No** — Phase A は `reg_at` field を hypothesis 形で消費し続ける、refactor 必要 (本 plan の最大規模 step) | **Phase 2 で structure refactor + sorry-based migration** |
| 4 | `deBruijn_identity_v2` (theorem) | `FisherInfoV2DeBruijn.lean:227+` | body `:= h_reg.derivAt_entropy_eq_half_fisher_v2` (load-bearing field 抽出) | **No** — defect 3 の field 抽出、defect 3 解消の前提 | **Phase 2 で sorry-based migration** |
| 5 | `deBruijn_identity_v2_of_heat_subhyp` (theorem) | `FisherInfoV2HeatFlowBody.lean:240-249` | body forward to defect 2 (transitive literal alias) | **No** — defect 2 解消で transitive 解消 | **Phase 2 で sorry-based migration (transitive)** |

**結論**: tier 5 defect 5 件は **Phase A 完了で自動解消しない** (Phase A は EPI 主定理 path に shared sorry 補題 + bridge wrapper を導入したが、上流 FisherInfo の predicate signature には触れていない)。本 sweep Phase 2 で **構造的に 5 件すべて signature 改変 + sorry-based migration** が必要。

### `@audit:defect(prop-true)` 2 件の現状 (Cluster D)

| declaration | file:line | tag | 解消可否 |
|---|---|---|---|
| `IsStamInequalityHypothesis := True` | `EntropyPowerInequality.lean:144-145` | `@audit:defect(prop-true)` `@audit:closed-by-successor(epi-stam-discharge-plan)` | **Phase 3 で第一選択 (定義書換 → sorry 化)** — `epi-stam-discharge-plan` が closure plan の旧名、本 sweep では本 declaration を retract (`IsStamInequalityResidual` が代替済) または sorry-based 書換 |
| `IsDeBruijnIntegrationHypothesis := True` | `EntropyPowerInequality.lean:160-161` | `@audit:defect(prop-true)` `@audit:closed-by-successor(epi-debruijn-integration-plan)` | **Phase 3 で同様処理** — Phase A 完了で consumer 0 (verbatim 確認要)、retract 安全か再 verify |

### Wall name register との関係

`docs/audit/audit-tags.md` Wall name register 既登録の関連 wall:

- **`stam`** — Stam の不等式 (Blachman score-of-convolution identity)、Fisher 情報の畳み込み、Ch.17 EPI
  - 本 sweep Phase 1 (EPI/Stam cluster) の主要 shared wall 候補。`EPIStamStep3Body.lean` 7 件 suspect + `EPIStamToBridge.lean` 9 件 `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` + `EntropyPowerInequality.lean:230` `stamToEPIBridge_holds` shared sorry 補題 (既存 `@residual(plan:epi-stam-to-conclusion-plan)`) を `wall:stam` に集約 / 整合判断。
  - `EPIStamToBridge.lean` 内 9 件は **already in plan-slug 形式** (`@residual(plan:epi-stam-to-conclusion-phaseA-plan)`)、wall 集約と plan 集約のどちらが honest か Phase 1 で判定。
- `epi-n-dim` — 多次元 EPI / n-dim Prékopa-Leindler の slice 解析的 readiness、Ch.17 BM
  - 本 sweep scope **外** (1-dim EPI に集中)。

**新規 wall promote candidate** (本 sweep 進行中に評価):
- `wall:debruijn-integration` — heat-flow path 上の `(d/dt) h(Z_t) = (1/2) J(Z_t)` integration identity。Cluster B `IsRegularDeBruijnHypV2` の core claim 候補 (現在 `@residual(plan:epi-debruijn-integration-plan)` 想定)。Phase 2 で `wall:stam` への合流 / 独立 promote を判定。
- `wall:fisher-info-score-zero` — `∫ logDeriv f · f = 0` (score expectation vanishes)。`FisherInfo.lean:127` + `FisherInfoV2.lean:157` の core claim 候補。集約検討対象 (現状は同 wall への集約も plan-slug 維持もどちらも honest)。

### 検証強度・honesty バー (CLAUDE.md 「Definition of Done」2-tier + 「検証の誠実性」)

- **本 sweep の主要バー**: 全 13 file が **type-check done** (`lake env lean` 0 errors、`sorry` は `@residual(<class>:<slug>)` 付き) で commit/push 可。
- **proof done バー**: 本 sweep の範囲では達成しない (上流 Mathlib 壁 `wall:stam` が残るため)。Cluster B/C/D の `@audit:ok` 全件昇格は **本 sweep の Done 条件ではない**。
- **honesty defect 検出**: 本 sweep 進行中に新規 tier 5 defect (load-bearing hypothesis bundling / `Prop := True` / 循環 `:= h` / 退化定義悪用 / name laundering) を発見したら、**作る側でも見つけた側でも即フラグ**。silent fix 禁止。

## Approach

### 全体戦略

**統合 sweep が最 honest という Round 4 sweep Wave 4-A planner 判断の再確認**:

`fisher-info-sorry-migration-plan` (2026-05-26) は 4 cluster 統合 sweep を「**EPI/Stam family と統合判断必要、本 plan を単独で進めることは禁止**」と Pattern G escalate 結論。本 plan はその統合判断の実行 plan。

**cluster 分離 sweep の問題点** (本 plan で統合を選ぶ理由):

1. **cluster 境界跨ぎの olean refresh cascade**: Cluster B (FisherInfo) の `IsRegularDeBruijnHypV2` structure refactor は Cluster C (EPIStamDischarge / EPIStamDeBruijnConclusion / EPIStamToBridge / EPIL3Integration) の active consumer chain 全件に signature ripple。分離 sweep だと「Cluster B sweep → 14 consumer 全件で olean 不整合 → `lake build` で olean refresh の round-trip」を Phase ごとに繰り返す。統合だと最後の 1 回で済む。
2. **shared wall lemma の集約判断は cluster 横断**: `wall:stam` / `wall:debruijn-integration` / `wall:fisher-info-score-zero` の集約先選択は 13 file 全体の consumer 構造を見ないと honest 集約できない。Cluster B 単独で `IsIBPHypothesis` を `@residual(wall:debruijn-integration)` に向けても、Cluster C の `EPIStamDeBruijnConclusion` consumer が `wall:stam` に揃えたい場合に再集約が必要。
3. **Phase A 完了直後の momentum**: `stamToEPIBridge_holds` shared sorry 補題が確立されたタイミングで、同種の shared sorry 補題 (`debruijnIdentityV2_holds` 等) を導入する設計判断を一気に行うのが整合的。Phase A 後しばらく経つと wrapper の docstring drift が起きる。
4. **tier 5 defect 5 件は同一構造**: defect 1-5 はすべて `IsRegularDeBruijnHypV2` field / `IsIBPHypothesis` literal alias / `:= h_ibp` 循環の **同一 family of defects**。1 件 fix は次の 1 件と signature と consumer chain を共有するため、5 件を分離して直すと毎回 olean refresh + downstream consumer fix の round-trip が増える。

**統合 sweep の問題点と回避策**:

- **規模が大きい (~40+ declarations、13 file)**: Phase 1/2/3 を **sequential** に進めて 1 Phase = 1 cluster scope で contain。各 Phase 内部の独立 declaration は **並列 (worktree + .lake symlink)** で dispatch。
- **session 数が嵩む**: 1 session で 1 Phase を完走できない場合、各 Phase は内部で sub-step に分解して `lean-implementer` を逐次 dispatch、`handoff.md` で session 跨ぎを管理。

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

統合 sweep の Phase 進行に従って:

- **Phase 1 完了時**: `EPIStamToBridge.lean` 9 件 `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` + `EntropyPowerInequality.lean:229` `@residual(plan:epi-stam-to-conclusion-plan)` の集約判定。
  - 候補 A: `wall:stam` 1 件に全集約 (Cover-Thomas Ch.17 内容上は同 wall)
  - 候補 B: plan-slug 維持 (closure plan として `epi-stam-to-conclusion-plan` が active、wall 化は postpone)
  - **判定基準**: 同 wall declaration が 2+ family で再利用される予兆があれば A、無ければ B。Phase 0 verbatim inventory で他 family 参照を確認。
- **Phase 2 完了時**: `wall:debruijn-integration` を新規 promote するか、`wall:stam` に合流するかを判定 (Cluster B の core claim を集約するため)。
- **Phase 3 完了時**: `wall:fisher-info-score-zero` の promote 判定 (`FisherInfo.lean:127` / `FisherInfoV2.lean:157` の `∫ logDeriv f · f = 0` 集約候補)。

### tier 5 defect 5 件の Phase A 完了による自動解消可否 — verbatim 結論

(Context 節 tier 5 defect 表を再掲、結論のみ):

**自動解消件数: 0 件 / 5 件**。Phase A は EPI 主定理 path に shared sorry 補題を導入したのみで、上流 FisherInfo cluster の predicate signature には触れていない。tier 5 defect 5 件は **本 sweep Phase 2 で構造的に sorry-based migration が必要**。

### 第一選択 (定義書換) ルートの確認 — CLAUDE.md「Mathlib-shape-driven Definitions」遵守

tier 5 defect 5 件の置換型は **Mathlib `HasDerivAt` 結論形に整合** させる方針:

- **`IsIBPHypothesis` 書換**: `def IsIBPHypothesis ... : Prop := HasDerivAt (...) (...) t` のまま literal alias を維持するのではなく、性質を **別 theorem** `isIBPHypothesis_holds` (body `sorry` + `@residual(wall:debruijn-integration)`) に分離。`isIBPHypothesis_iff` (`Iff.rfl`) は廃止候補。
- **`IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field 書換**: structure field を `derivAt_entropy_eq_half_fisher_v2 : HasDerivAt ... ((1/2) * fisherInfoOfDensityReal density_t) t` 形のまま **残す** (regularity precondition として honest)、ただし `deBruijn_identity_v2` body が `h_reg.derivAt_entropy_eq_half_fisher_v2` の直接抽出にならないよう、別 shared sorry 補題 `debruijnIdentityV2_holds` (body `sorry` + `@residual(wall:debruijn-integration)`) を間に挟む。
- **`deBruijn_identity_v2` body 書換**: `:= h_reg.derivAt_entropy_eq_half_fisher_v2` → `debruijnIdentityV2_holds X Z P t h_reg` の呼び出し形 (shared sorry 補題経由)。

**判定の一言** (CLAUDE.md): 「その仮説は前提条件 (regularity) か、それとも証明の核心 (load-bearing) か」。
- `IsRegularDeBruijnHypV2.density_t` / `Z_law` / `density_path` / `density_t_eq` field → **regularity precondition** (Phase A の structure refactor で `density_t_eq` pin が確立済、retain OK)
- `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field → **load-bearing** (de Bruijn identity の結論を field として bundle)、本 sweep で structure 内に残すが consumer (`deBruijn_identity_v2` body) は shared sorry 補題経由に変える

### 「4 cluster 統合の正当性」最終整理 (vs cluster 分離 sweep の trade-off)

| trade-off 軸 | 統合 sweep (本 plan) | cluster 分離 sweep (`fisher-info-sorry-migration-plan` 単独再起動 / EPI/Stam 単独 / EntropyPowerInequality 単独) |
|---|---|---|
| **olean refresh round-trip** | 最後 1 回 (Phase V) | Cluster B → Cluster C で 1 回 + Cluster C → Cluster D で 1 回 = 計 2-3 回 |
| **shared wall lemma 集約判断** | 13 file 全体を見て 1 度判定 | Cluster ごとに判定 → 後で再集約 (`wall:stam` 候補 lemma が cluster 横断 reuse 時に migrate cost) |
| **tier 5 defect 5 件処理** | Phase 2 で 1 session sequential 完走 | Cluster B sweep で 1 件 fix → Cluster C ripple → Cluster B 戻る、の round-trip |
| **session 数** | ~5-10 session (本 plan 全体) | Cluster B 単独 3-5 session + Cluster C 単独 5-8 session + Cluster D 単独 1-2 session = 9-15 session |
| **plan/handoff 数** | 本 plan 1 + 既存 plan の Phase 状態 update のみ | 3 plan の再起動 + 各 plan の sister 待ち管理 |
| **honesty audit** | Phase V で 3 cluster 並列 audit (1 session) | 各 cluster 完了時に独立 audit (3 session) |
| **撤退 cost** | Cluster B Phase 2 で詰まったら sister plan に戻れる (撤退ライン整備) | Cluster C / D の sweep が Cluster B 待ちで stale 化 |

**結論**: 統合 sweep は session 数で約 40-50% 削減、olean refresh で 2-3 倍効率、shared wall 集約判断が 1 度で済む。`fisher-info-sorry-migration-plan` の Pattern G escalate (「単独 sweep 禁止」) を満たす唯一の整合 path。

### 段階的 ship 設計 (Tier 0 / 1 / 2)

- **Tier 0 (Phase 0 docs-only)**: 本 plan + verbatim inventory + tier 5 defect 確定 + Cluster A 統合 / 独立判定。docs-only commit (本 session で完了)。
- **Tier 1 (Phase 1 + Phase 3)**: Cluster C + Cluster D の sweep (FisherInfo refactor 無しで完結する範囲)。`EPIStamStep3Body.lean` 7 件 Lagrange + `EPIStamToBridge.lean` 9 `@residual` + `EntropyPowerInequality.lean` 2 `Prop := True` の処理。partial publish 価値あり (`@audit:suspect` 7 件 → `@residual` 移行 + 2 件 `Prop := True` → sorry-based)。
- **Tier 2 (Phase 1 + Phase 2 + Phase 3 + Phase V)**: FisherInfo cluster structure refactor 完遂 + 13 file 全 `lake env lean` clean + honesty-auditor 3 cluster pass。

### 規模見積もり

| Phase | 自作要素 | 想定行数 | session 数 |
|---|---|---|---|
| 0 | 本 plan 起草 + Phase 0 verbatim inventory + Cluster A 判定 | ~80-100 KB (本 plan) | 1 |
| 1 | Cluster C (EPI/Stam) sweep: 7 suspect → sorry 移行 + 9 `@residual` 整理 + 2 staged 整合 | ~150-300 | 1-2 |
| 2 | Cluster B (FisherInfo) refactor: tier 5 defect 5 件 + `IsRegularDeBruijnHypV2` structure refactor + consumer ripple | ~400-700 | 2-4 |
| 3 | Cluster D (EntropyPowerInequality) sweep: 2 `Prop := True` 移行 + rename 検討 | ~80-150 | 1 |
| 6 (cond.) | Cluster A (ParallelGaussianPerCoord) — Phase 0 判定次第 | (未定、~50-200) | 0-1 |
| V | 13 file `lake env lean` + 3 cluster 並列 audit + post-merge cleanup | ~30-80 | 1 |
| **合計** | | **~660-1430** | **5-10** |

中央予測 **~1000 行 / 7 session**。

## 進捗

- [ ] Phase 0 — verbatim inventory + tier 5 defect 確定 + Cluster A 判定 + wall 集約初期判定 📋
- [ ] Phase 1 — Cluster C (EPI/Stam) sweep: suspect 7 + `@residual` 9 + staged 2 整合 📋
- [ ] Phase 2 — Cluster B (FisherInfo) refactor: tier 5 defect 5 件 + structure refactor 📋
- [ ] Phase 3 — Cluster D (EntropyPowerInequality) sweep: 2 `Prop := True` migration + rename 検討 📋
- [ ] Phase 6 — Cluster A (ParallelGaussianPerCoord) — Phase 0 判定次第 (default skip) 📋
- [ ] Phase V — 全 13 file `lake env lean` + honesty-auditor × 3 cluster 並列 audit 📋

proof-log: yes (各 Phase 完了時に `docs/shannon/proof-log-epi-stam-fisher-epi-integrated-sweep-phase-<N>.md`)

---

## Phase 0 — verbatim inventory + tier 5 defect 確定 + Cluster A 判定 + wall 集約初期判定 📋

> **本 session で完了**。docs-only、`Common2026/*.lean` 触らない。

### スコープ

- 上記 Context 節の verbatim tag inventory 表 + tier 5 defect 表を Phase 0 出力として確定 (本 plan 内に既に貼付済)
- Cluster A (ParallelGaussianPerCoord) を統合 / 独立 / skip のいずれにするか判定
- wall 集約初期判定 (`wall:stam` 集約 vs plan-slug 維持) を Phase 1 入口の anchor として確定

### Phase 0 step

- [x] step 1 — verbatim tag inventory (Bash 実行結果) を本 plan Context 節に貼付済
- [x] step 2 — tier 5 defect 5 件の現状確認 (`rg -n 'IsIBPHypothesis|IsRegularDeBruijnHypV2'` + `rg -n ':= h_ibp\|:= Iff.rfl'` 実行、結果を tier 5 defect 表に整理済)
- [ ] step 3 — Cluster A (ParallelGaussianPerCoord) の現状確認 (`ParallelGaussianPerCoordRegularity.lean` 1 `@residual` の verbatim 内容を確認、parallel-gaussian-moonshot-plan / parallel-gaussian-l-pg0-discharge / l-pg1-discharge / chain-rule-plan の Phase 進捗を Read)、**判定**: default は **独立** (Cluster B/C/D との signature 連動が薄い、`fisher-info-sorry-migration-plan` も Round 4 candidate として Cluster A を別 sweep に置いていた)。判定根拠 + 統合する場合の Phase 4/5 sketch を Phase 6 セクションに記録。
- [ ] step 4 — wall 集約初期判定: `wall:stam` 既存 register が EPI/Stam family を primary owner として保持しているため、`EPIStamToBridge.lean` 9 件は **plan-slug 維持** が default (Phase 1 で再判定)。`wall:debruijn-integration` / `wall:fisher-info-score-zero` は **新規 promote 留保** (Phase 2/3 で判定)。
- [ ] step 5 — 本 plan を commit (`epi-stam-fisher-epi-integrated-sweep` docs-only 起草)

### Done 条件

- 本 plan が起草 + commit 済
- Cluster A 判定が記録済 (default 独立、統合する場合の Phase 番号も記録)
- wall 集約初期判定が記録済 (Phase 1 入口の anchor として)

### 撤退ライン

- **L-INT-0-α** (許容): Cluster A 判定で「統合が strictly necessary」と判明した場合 (例: ParallelGaussianPerCoord の sorry が Cluster B/C 連動で transitive 解消する場合)、Phase 4 / 5 として組み込み、本 plan の規模見積もりを更新。**default は独立** で進めるため発火確率低。

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

#### Phase 2.A — `IsRegularDeBruijnHypV2` structure refactor (本 Phase の foundation step)

**現状** (`FisherInfoV2DeBruijn.lean:195-249`、verbatim):
- `density_path : ℝ → ℝ → ℝ` field (Phase A で top-level に格上げ済、`density_t_eq` pin あり)
- `reg_at : ∀ t : ℝ, 0 < t → IsRegularDeBruijnHypV2 X Z P t` field (recursive structure reference、honest precondition)
- `derivAt_entropy_eq_half_fisher_v2 : HasDerivAt ... ((1/2) * fisherInfoOfDensityReal density_t) t` field — **load-bearing**、`deBruijn_identity_v2` body の核

**Refactor 方針** (CLAUDE.md「Mathlib-shape-driven Definitions」第一選択、sorry を proof body に逃がす):

候補 1: structure field をそのまま保持 + shared sorry 補題経由
- structure 全 field 保持 (regularity precondition として honest)
- `deBruijn_identity_v2` body を `h_reg.derivAt_entropy_eq_half_fisher_v2` 直接抽出から **shared sorry 補題** `debruijnIdentityV2_holds X Z P t h_reg` 経由に変更
- shared sorry 補題に sorry 集中、`@residual(wall:debruijn-integration)` or `@residual(wall:stam)` (Phase 2 で wall 集約判断)

候補 2: structure field 削除
- `derivAt_entropy_eq_half_fisher_v2` field を削除 (regularity precondition では無いと判定)
- `IsRegularDeBruijnHypV2` を regularity-only (`density_path` / `Z_law` / `density_t` / `density_t_eq`) に縮小
- `deBruijn_identity_v2` を `(h_reg : IsRegularDeBruijnHypV2 X Z P t)` 取って body sorry に書換、`@residual(wall:debruijn-integration)`

**判定基準**: Phase A の `density_t_eq` pin が「`density_path := 0` 退化境界排除」のために load-bearing として残されている (`EPIStamDischarge.lean:163-193` docstring verbatim)。candidate 2 で field 削除すると pin との整合性が崩れる可能性。**default は candidate 1** (structure 保持 + shared sorry 補題経由)。

**Phase 2.A Done 条件**: shared sorry 補題 `debruijnIdentityV2_holds` を `FisherInfoV2DeBruijn.lean` 内 (または新規 `Common2026/Shannon/FisherInfoV2Walls.lean`) に publish、`@residual(wall:debruijn-integration)` 付与 (新規 wall promote 判断 → audit-tags.md Wall name register に追記)。

#### Phase 2.B — foundation step (field 削除) + 4 launder declaration cleanup + tier 5 defect 連鎖解消 (強化版、2026-05-27)

> **本 Phase 2.B は Phase 2.A の no-op launder verdict (DEFECT、commit `a6ae83b`) を受けた強化版**。Phase 2.A は candidate 1 (structure 保持 + shared sorry 補題経由) を default 採用したが、独立 audit verdict で「結論型 ≡ `derivAt_entropy_eq_half_fisher_v2` field、`exact h_reg.derivAt_entropy_eq_half_fisher_v2` で trivially 閉じる → field 抽出を 1 段 indirection で隠しただけ、`wall:debruijn-integration` に突き当たっていない」と判定された (`FisherInfoV2DeBruijn.lean:240-256` audit docstring verbatim)。
> ユーザー決定 (2026-05-27): Phase 2.A は **defect marker `a6ae83b` で acknowledge して現状維持**、Phase 2.B で **(a) `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field 削除 + (b) 4 launder declaration cleanup + (c) tier 5 defect 連鎖解消 を同時実施** する強化方針に pivot。

##### 強化版スコープ表 (verbatim、本 plan update 前に Read で line/body 確認済 2026-05-27)

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

#### wall residual 付与先の移動 — F1 削除後の正しい closure point

Phase 2.A audit verdict (`FisherInfoV2DeBruijn.lean:243-247` audit docstring verbatim): 「load-bearing 負荷は依然 `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field に bundle されたまま」。**F1 削除によって、`wall:debruijn-integration` 残余は L1 `debruijnIdentityV2_holds` body の `sorry` に genuine 集約される** (no-op launder から genuine wall closure に昇格)。

- **移動前** (Phase 2.A): `@residual(wall:debruijn-integration)` は L1 body 内、ただし audit verdict で「no-op launder」判定 (= wall に届いていない)
- **移動後** (Phase 2.B foundation step 完了時): `@residual(wall:debruijn-integration)` は L1 body 内のまま、ただし F1 field 削除によって **genuine wall closure point に昇格** (audit docstring の `@audit:defect(launder)` 部分は削除、`@residual(wall:debruijn-integration)` のみ残る)
- audit-tags.md Wall name register の `debruijn-integration` 登録 (commit `23dae39`) は **維持** (本 update でも問題なし、wall 自体は genuine Mathlib 壁として正当)

> **1 階層下 (`IsIBPHypothesis` direct) ではなく、L1 (`debruijnIdentityV2_holds`) が closure point**。理由: F1 field 削除後の `IsRegularDeBruijnHypV2` は regularity-only (Z_law + density_t) になり、`debruijnIdentityV2_holds` body が「regularity から HasDerivAt 結論を導く」genuine heat-eq + IBP wall に直接突き当たる。`IsIBPHypothesis` direct (D1) は literal alias predicate にすぎず、wall closure point として使うと再び launder の risk (Phase 2.A と同型の no-op pattern)。

### Phase 2 並列 dispatch 設計 (強化版) — **sequential 厳守**

- **Wave 2-A (foundation 段 1)**: F1 削除 + L4 縮小 + L1 status 固定 (audit docstring 整理 + `@audit:defect(launder)` 削除) = **single dispatch** (`lean-implementer` 1 件、worktree 省略可、`Common2026/Shannon/FisherInfoV2DeBruijn.lean` + `FisherInfoV2DeBruijnBody.lean` 2 file 連動 touch)。
- **Wave 2-B (cleanup 段 2)**: L2 → L3 → D5 → D5' を **sequential** 1 declaration = 1 dispatch + 1 commit (literal alias chain 逆順、4 dispatch)。並列禁止理由: L3 signature が L2 / D5 / D5' すべてに ripple、間に LSP 同期境界を入れないと型 mismatch 連鎖。
- **Wave 2-C (段 3 + Cluster B 残)**: D1 処遇判定 (alias 維持 + `@audit:retract-candidate` 付与、本 sweep では retract せず) は L2-D5' commit と合流して 1 dispatch + Phase 2.C (`FisherInfo.lean:127` / `FisherInfoV2.lean:157` `integral_logDeriv` 2 件) と並列可 (file 別)。

> **foundation 段 1 を最初に sequential**: F1 削除が L1-L4 signature の prerequisite。並列にすると olean refresh round-trip が L1-L4 dispatch 毎に発生 (`lake build Common2026.Shannon.FisherInfoV2DeBruijn` 4 回)。foundation 1 dispatch で signature が確定すれば後続段は signature 安定下で進行。

#### Phase 2.C — `FisherInfo.lean:113` / `FisherInfoV2.lean:151` `integral_logDeriv` 2 件 sweep

> **2026-05-27 A3 pivot**: 当初の「shared sorry 補題化 + sorry-based migration」設計は **reject** (proof-pivot-advisor + 独立 honesty-auditor verdict、Phase 2.A no-op launder verdict の過剰一般化を回避)。実際の closure 経路は **`@audit:suspect` → `@audit:ok` 昇格** (Phase 1.B/1.C パターン)。`wall:fisher-info-score-zero` 新規 promote は不要、`audit-tags.md` Wall register への追記も不要。

##### A3 採用根拠 (verdict サマリ、2026-05-27 honesty audit)

- **V1 (body genuine)**: `integral_logDeriv_pdf_eq_zero` (`FisherInfo.lean:117-129`) は 13 行 genuine proof (pointwise `logDeriv f · f = deriv f` via positivity (`logDeriv_apply` + `div_mul_cancel₀`) → `integral_congr_ae` → `h_reg.integral_deriv_eq_zero` field 呼出)。`integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:152-162`) も同 12 行 genuine。`:= h` 循環 / `:True` slot / 退化定義悪用 すべて非該当
- **V2 (field is regularity 帰結、not load-bearing core)**: `IsRegularDensity.integral_deriv_eq_zero` / `IsRegularDensityV2.integral_deriv_eq_zero` は `Differentiable ℝ f` + `Tendsto f atBot/atTop (nhds 0)` + `Integrable (deriv f) volume` から FTC + tail-vanishing で導出可能 (Mathlib improper integral lemma 経由)。**Cover-Thomas 17.7 の核心 (score expectation vanishes)** ではなく、その「FTC step」のみを bundle (conclusion は pointwise bridge `logDeriv f · f = deriv f` を追加で内包、field は strictly weaker)。CLAUDE.md「前提条件 (regularity) か証明の核心 (load-bearing) か」軸で前者
- **V3 (Gaussian instance で genuine discharge 済)**: `isRegularDensity_gaussianReal_of_law` (`FisherInfoGaussian.lean:280-292`) で 7 field 全てを hypothesis-free 構築、`integral_deriv_eq_zero := integral_deriv_gaussianPDFReal_eq_zero m hv` (closed form ~45 行 at `:231-276`)。`sorry` / `@residual` / `@audit` marker 全て不在
- **V4 (Phase 2.A 非同型)**: Phase 2.A は `derivAt_entropy_eq_half_fisher_v2` field を engine substitution のみ (`density_t` → `h_reg.density_t` trivial rename) で `exact h_reg.field` 1 段 trivial closure = no-op launder DEFECT。Phase 2.C は `logDeriv f · f` ↔ `deriv f` の positivity-keyed pointwise bridge 13 行を間に挟むため engine substitution **不成立**、no-op launder には該当しない (別カテゴリの「Mathlib 壁が field 内に押し込まれた legacy」)

##### 改訂内容 (本 Phase 2.C closure 実装)

- **`FisherInfo.lean:111`** `@audit:suspect(fisher-info-moonshot-plan)` → `@audit:ok` 置換、`integral_deriv_eq_zero` field docstring に Gaussian instance discharge 参照を追記
- **`FisherInfoV2.lean:149`** 同上 (`@audit:ok` 置換 + field docstring 拡張)
- structure refactor / Gaussian instance 修正 / shared sorry 補題追加 / Wall register 追記 すべて **不要**
- consumer ripple (Cluster C 等) も **不要**

##### Phase 2.A 教訓の一般化リスク (本 pivot で確立した先制検出ルール)

Phase 2.A no-op launder verdict (engine substitution only な field rename を tier 5 認定 + 削除断行) を **全 `@audit:suspect` field に一般化すべきではない**。verbatim 先制検出:

1. shared sorry 補題化を検討する **前** に、対象 declaration の **現 body が genuine proof 完成済か** check (line count + pointwise bridge / non-trivial step の有無)
2. Mathlib 壁 4 分類 (d)「実は閉鎖済」を wall として promote しないため、当該 field が **Gaussian / 具体例で genuine discharge 済か** verify (Gaussian instance の closure 状態 check)
3. `:= h_reg.field` 1 段 trivial closure の場合のみ Phase 2.A 同型 launder と認定、それ以外は別カテゴリ (load-bearing vs regularity 帰結 軸で判定)

本ルールは `docs/audit/audit-tags.md` Phase 2.A 教訓セクションに反映候補 (future commit)。

##### `IsRegularDensity(V2).integral_deriv_eq_zero` field の取扱 (load-bearing 判定軸の精緻化)

- `derivAt_entropy_eq_half_fisher_v2` (Phase 2.A、load-bearing) と `integral_deriv_eq_zero` (Phase 2.C、regularity 帰結) の判定差は **「conclusion type と field type が strictly な engine substitution で一致するか」**
- `derivAt_entropy_eq_half_fisher_v2`: 主定理結論型と field 型が `density_t` rename のみで一致 → load-bearing
- `integral_deriv_eq_zero`: conclusion `∫ logDeriv f · f = 0` と field `∫ deriv f = 0` の間に positivity-keyed pointwise bridge 13 行 → regularity 帰結 (strictly weaker)
- 判定軸統一: 「field が conclusion を **strictly weaker な形で** bundle するなら regularity 帰結」、「**結論そのもの (rename のみ)** を bundle するなら load-bearing core」

### 判定基準 update — Phase 2.A 教訓を反映した先制検出ルール

**Phase 2.A audit verdict から学んだ「結論型 ≡ field 型」launder の先制検出**:

shared sorry 補題化を行う **前** に、以下を必ず verbatim check:

1. shared sorry 補題の **結論型** (`HasDerivAt ... t`) を verbatim 取得
2. 該当 structure field の **field 型** を verbatim 取得
3. 両者が **engine substitution** (`density_t` → `h_reg.density_t` 等の trivial 置換) のみで一致するなら、shared 補題化は **no-op launder** (load-bearing field の indirection 隠蔽) と判定 → shared 補題化禁止、第一選択 (定義書換 = field 削除) を選ぶ

Phase 2.A はこの check を怠った結果 no-op launder を生成。Phase 2.B foundation 段 1 では verbatim 確認段階で `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field の型と `debruijnIdentityV2_holds` 結論型が verbatim 一致と確認済 (本 update の Read で再確認、`FisherInfoV2DeBruijn.lean:204-208` vs `:264-267`) → **field 削除のみが genuine refactor** と確定。

### 撤退ライン (Phase 2、強化版で update)

- **L-INT-2-α update** (許容、方向逆転): 元 plan は「candidate 2 (field 削除) → candidate 1 (structure 保持) retreat」だったが、Phase 2.A no-op launder verdict で **candidate 2 (field 削除) を default 採用** に逆転。retreat 方向も逆転 → **L-INT-2-α 新方向**: F1 field 削除中に Phase A `density_t_eq` pin との不整合 (削除予定 file が `EPIStamDischarge.lean:163-193` `density_t_eq` pin docstring と矛盾) または Cluster C consumer ripple が許容外 (5 件 `(h_reg.reg_at t ht).derivAt_entropy_eq_half_fisher_v2` 直接抽出 + 1 件 Gaussian witness lift constructor、計 6+ 件で signature 連鎖修正) → **field 削除中止、tier 5 marker 付与で 8 declaration 全件残置**。L1 audit docstring の `@audit:defect(launder)` + `@audit:retract-candidate(launder)` を維持、後続 plan に委譲。本 sweep の Done 条件は「F1 field 削除完了」ではなく「8 declaration の honesty 状態が tier 5 暫定マーカーで明示済」に retreat。
- **L-INT-2-β update** (許容、partial closure): L2 / L3 / D5 / D5' のうち N 件のみ closure、残置分は `@audit:defect(launder)` / `@audit:retract-candidate(name-laundering-alias)` で明示。元 L-INT-2-β と同趣旨だが defect 番号を 8 declaration に拡張。
- **L-INT-2-γ** (撤退、`wall:debruijn-integration` 新規 promote 留保): **本 update では発火しない** — wall は既に commit `23dae39` で register 済。Phase 2.B では wall promote judgment は確定済として進行、本 ライン は historical reference として残置。
- **L-INT-2-δ** (新規、許容): foundation 段 1 で field 削除を断行したが、Cluster C `EPIStamToBridge.lean:554/561/569` の 3 件 (`(h_reg_*.reg_at t ht).derivAt_entropy_eq_half_fisher_v2`) を `deBruijn_identity_v2` 呼出 (L2 経由) に書換中、Phase 1 anchor (Cluster C suspect/sorry 整理) と signature 衝突 → Phase 1 anchor を先に固定済前提で進行、衝突発生時は Phase 1 への一時 revert + 再 anchor 設定。

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

> **Phase 0 で判定**。default は **独立 (skip)** = 本 sweep 外。

### Phase 0 step 3 で判定する内容

- `ParallelGaussianPerCoordRegularity.lean` の 1 `@residual` の verbatim 内容を確認
- `parallel-gaussian-moonshot-plan.md` / `parallel-gaussian-l-pg0-discharge-moonshot-plan.md` / `parallel-gaussian-l-pg1-discharge-plan.md` / `parallel-gaussian-chain-rule-plan.md` の Phase 進捗を Read
- ParallelGaussianPerCoord の declaration が Cluster B / C / D と signature 連動するか確認 (典型: `parallel-gaussian-l-pg0-discharge` が `IsRegularDeBruijnHypV2` 経由で Cluster B に依存している場合 / `IsStamInequalityResidual` 経由で Cluster D に依存している場合)

**統合判定** (Phase 0 step 3 完了時に確定):

- **default (独立)**: Cluster A は本 sweep 外、別 plan (`parallel-gaussian-moonshot-plan` Phase 進行) として継続。本 plan の Phase 6 は skip。
- **統合の場合**: Phase 4 (Cluster A の sweep step) / Phase 5 (Cluster A audit step) として組み込み、本 plan の規模見積もりを update。

### default skip 時の Phase 6 記述

Phase 6 = skip、`parallel-gaussian-moonshot-plan.md` に Round 5 以降の起動条件 (本 sweep Phase 2 完了 + Cluster A 単独 sweep 価値が confirmed) を反映。

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

## 検証手順 (Phase 別 + 統合 final)

### Phase 別検証

各 Phase 完了時に:

```bash
# Phase 1 完了時 (Cluster C 9 file)
for f in EPIStamDischarge EPIStamToBridge EPIStamInequalityBody EPIStamStep12Body \
         EPIStamStep3Body EPIStamDeBruijnConclusion EPIL3Integration EPIPlumbing StamGaussianBound; do
  lake env lean Common2026/Shannon/$f.lean
done

# Phase 2 完了時 (Cluster B 7 file)
for f in FisherInfo FisherInfoV2 FisherInfoV2DeBruijn FisherInfoV2DeBruijnBody \
         FisherInfoV2HeatFlowBody FisherDeBruijnGaussianWitness FisherInfoGaussian; do
  lake env lean Common2026/Shannon/$f.lean
done

# Phase 3 完了時 (Cluster D 1 file)
lake env lean Common2026/Shannon/EntropyPowerInequality.lean
```

各 Phase 完了時に `lake build Common2026.Shannon.<refactored-file>` で olean refresh (CLAUDE.md「After upstream edits, dependents may need olean refresh」)。

### 統合 final 検証 (Phase V)

```bash
# 全 13 file (条件付き 14 file)
for f in $(cat <<EOF
FisherInfo
FisherInfoV2
FisherInfoV2DeBruijn
FisherInfoV2DeBruijnBody
FisherInfoV2HeatFlowBody
FisherDeBruijnGaussianWitness
FisherInfoGaussian
EPIStamDischarge
EPIStamToBridge
EPIStamInequalityBody
EPIStamStep12Body
EPIStamStep3Body
EPIStamDeBruijnConclusion
EPIL3Integration
EPIPlumbing
StamGaussianBound
EntropyPowerInequality
EOF
); do
  lake env lean Common2026/Shannon/$f.lean
done

# 残課題集計 (audit-tags.md「残課題集計」recipe)
rg "@residual" Common2026/Shannon/ | wc -l
rg -o "@residual\([a-z]+:" Common2026/Shannon/ | sort | uniq -c | sort -rn

# tag 無し sorry の検出 (audit-tags.md「分類漏れ」)
for f in $(rg -l "\bsorry\b" Common2026/Shannon/EPI*.lean Common2026/Shannon/Fisher*.lean Common2026/Shannon/Stam*.lean Common2026/Shannon/Entropy*.lean); do
  rg -q "@residual" "$f" || echo "$f"
done

# deprecated タグ残置確認 (audit-tags.md「Deprecated」)
rg '@audit:suspect\(|@audit:staged\(|@audit:defer\(|@audit:closed-by-successor\(|🟢ʰ' \
  Common2026/Shannon/EPI*.lean Common2026/Shannon/Fisher*.lean Common2026/Shannon/Stam*.lean \
  Common2026/Shannon/EntropyPowerInequality.lean
```

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

2. **2026-05-27 — Phase 2.B 強化版へ pivot (Phase 2.A no-op launder verdict 反映)**:
   - Phase 2.A 実装 (commit `c0edc35`、candidate 1 default: structure 保持 + shared sorry 補題 `debruijnIdentityV2_holds` 経由) の独立 honesty audit verdict (commit `a6ae83b`) = **DEFECT (no-op launder)**: `debruijnIdentityV2_holds` 結論型 ≡ `IsRegularDeBruijnHypV2.derivAt_entropy_eq_half_fisher_v2` field 型 verbatim、`exact h_reg.derivAt_entropy_eq_half_fisher_v2` で trivially 閉じる → field 抽出を 1 段 indirection で隠しただけ、`wall:debruijn-integration` には突き当たっていない、wall classification 誤指定 (`FisherInfoV2DeBruijn.lean:240-256` audit docstring verbatim)
   - ユーザー決定 (本 update セッション): 選択肢 A 採用 = Phase 2.A 現状維持 (defect marker `a6ae83b` で acknowledge) + Phase 2.B を強化版に pivot
   - **L-INT-2-α 方向逆転**: 元 plan は「candidate 2 (field 削除) → candidate 1 (structure 保持) retreat」だったが、Phase 2.A 実証で candidate 1 が no-op launder と判明 → Phase 2.B foundation step では **candidate 2 (F1 field 削除) を default 採用**、retreat 方向は「field 削除困難時に 8 declaration 全件残置 + tier 5 暫定マーカー」に逆転
   - **強化スコープ**: 元 tier 5 defect 5 件 (defect 1-5 = D1 / L3 / F1 / L2 / D5) に加え、Phase 2.A 産物 (L1 `debruijnIdentityV2_holds` + L2 `deBruijn_identity_v2`) + auditor 追加発見 2 件 (L4 `IsRegularDeBruijnHypV2.ofHeatFlow:240` constructor 内 `derivAt_entropy_eq_half_fisher_v2 := h_ibp` + D5' `IsRegularDeBruijnHypV2.ofHeatSubhyp:239+` transitive) を合流、合計 **8 declaration に touch**
   - **3 段 sequential**: foundation 段 1 (F1 削除 + L4 縮小 + L1 status 固定) → 段 2 cleanup (L2 → L3 → D5 → D5' sequential) → 段 3 (D1 `@audit:retract-candidate` 付与で alias 維持、本 sweep では retract せず)
   - **wall residual 付与先**: F1 field 削除によって L1 `debruijnIdentityV2_holds` body の `@residual(wall:debruijn-integration)` が **no-op launder から genuine wall closure point に昇格** (1 階層下 `IsIBPHypothesis` direct ではなく、L1 が新 closure point)。audit-tags.md Wall name register の `debruijn-integration` 登録 (commit `23dae39`) は維持
   - **判定基準 update**: Phase 2.A no-op launder 教訓から「shared sorry 補題化前に **結論型 ≡ field 型 verbatim check** で先制検出」ルールを Approach 内に追加。Phase 2.B foundation 段 1 では本 update 起草時に Read で `FisherInfoV2DeBruijn.lean:204-208` (field 型) vs `:264-267` (L1 結論型) を verbatim 一致確認済 → field 削除のみが genuine refactor と確定
   - **Cluster C ripple 評価**: F1 field 削除で `EPIStamToBridge.lean:554/561/569` 3 件 + `EPIL3Integration.lean:678` Gaussian witness lift constructor 1 件 + `FisherInfoV2DeBruijnBody.lean:240` constructor 内 field 設定 1 件 = 計 5 件で signature 連鎖修正、各 consumer は `deBruijn_identity_v2` (L2 経由) 呼出で吸収可。`EPIStamDeBruijnConclusion.lean:144` は `density_t` access のみで ripple なし確認済
   - **規模見積もり update**: Phase 2 は元 ~400-700 行 / 2-4 session から、強化版で **~500-900 行 / 3-5 session** に上方修正 (8 declaration touch + Cluster C 5 consumer ripple + L1 audit docstring 整理)

1. **2026-05-27 — 本 plan 起草 (Phase 0 完了)**:
   - 起動契機: Phase A 完了 (`20ee48b`、`stamToEPIBridge_holds` shared sorry 補題 + `entropy_power_inequality_unconditional` hypothesis-free wrapper publish 済) によって、`fisher-info-sorry-migration-plan` が Phase 0 で「Case α (全降格)」と判定して保留していた FisherInfo cluster の sorry-based migration が起動可能な状態になった
   - 統合 sweep が最 honest という Round 4 sweep Wave 4-A planner 判断 (`fisher-info-sorry-migration-plan` の Pattern G escalate 結論「単独 sweep 禁止、EPI/Stam family と統合判断必要」) を再確認
   - 4 cluster 構成 (Cluster A = ParallelGaussianPerCoord 独立候補、Cluster B = FisherInfo、Cluster C = EPI/Stam、Cluster D = EntropyPowerInequality) の依存方向 (上流 ← 下流) を確定、Phase 分割を sequential (Phase 1 = C → Phase 2 = B → Phase 3 = D) で固定
   - tier 5 defect 5 件の Phase A 完了による自動解消可否を verbatim 確認: **自動解消件数 0 件 / 5 件**、Phase 2 で構造的に 5 件すべて signature 改変 + sorry-based migration が必要
   - Cluster A (ParallelGaussianPerCoord) は **default 独立 (skip)**、Phase 0 step 3 で再判定
   - wall 集約初期判定: `wall:stam` は EPI/Stam family を primary owner で保持、`EPIStamToBridge.lean` 9 件は plan-slug 維持 (Phase 1 で再判定)、`wall:debruijn-integration` / `wall:fisher-info-score-zero` は **新規 promote 留保** (Phase 2/3 で判定)
   - Phase A 完了直後の momentum で同種の shared sorry 補題 (`debruijnIdentityV2_holds` / `integral_logDeriv_pdf_eq_zero_holds`) を導入する設計判断を一気に行うのが整合的、と判断
   - 規模見積もり: ~660-1430 行 / 5-10 session、中央予測 ~1000 行 / 7 session

---

## 関連 Files (本 plan 起草時 + 進行中に参照)

- `docs/audit/audit-tags.md` — SoT (語彙 + Wall name register + Honesty 階層)
- `docs/audit/sorry-migration-runbook.md` — Step 1-4 手順 + Pattern A-J
- `docs/shannon/epi-stam-discharge-plan.md` — 38/39 ok 完了済、本 plan Phase 1 の参照
- `docs/shannon/epi-stam-to-conclusion-plan.md` — Phase 0 完了 + Phase A 完了 (`20ee48b`)、本 plan の起動契機
- `docs/shannon/epi-stam-to-conclusion-phaseA-plan.md` — Phase A mini-plan、本 plan Phase 1 の `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` 9 件の slug 由来
- `docs/shannon/epi-debruijn-integration-plan.md` / `epi-debruijn-integration-phaseD-plan.md` — Cluster C `EPIL3Integration.lean` の suspect 由来 plan
- `docs/shannon/epi-debruijn-regularity-refactor-plan.md` — `EPIStamDischarge.lean:194` `IsDeBruijnRegularityHyp` structure refactor 履歴
- `docs/shannon/fisher-info-sorry-migration-plan.md` — 2026-05-26 Phase 0 全降格判定、本 plan の前提
- `docs/shannon/fisher-info-moonshot-plan.md` — Cluster B の moonshot
- `docs/shannon/fisher-info-gaussian-discharge-moonshot-plan.md` — Gaussian discharge 系
- `docs/shannon/parallel-gaussian-moonshot-plan.md` / `parallel-gaussian-l-pg0-discharge-moonshot-plan.md` / `parallel-gaussian-l-pg1-discharge-plan.md` / `parallel-gaussian-chain-rule-plan.md` — Cluster A 独立 candidate の現状確認用
- `docs/textbook-roadmap.md` — Ch.17 EPI frontier 記載、Phase 3.C rename 検討対象 (`entropyPower_gaussian_additivity`)
- `Common2026/Shannon/EntropyPowerInequality.lean` — Cluster D 主 file、Phase A 完了の anchor
- `Common2026/Shannon/EPIStamDischarge.lean` / `EPIStamToBridge.lean` / `EPIL3Integration.lean` — Cluster C 主 file
- `Common2026/Shannon/FisherInfoV2DeBruijn.lean` / `FisherInfoV2DeBruijnBody.lean` / `FisherInfoV2HeatFlowBody.lean` — Cluster B tier 5 defect 5 件の所在

## 計数 — Phase 0 完了時の現状 verdict (本 sweep 全体の baseline)

| 項目 | Phase 0 baseline | Phase V Done 条件 (本 sweep closure 時) |
|---|---:|---:|
| 新規 sorry 数 (本 sweep で導入) | 0 (Phase 0 docs-only) | 30+ (見積もり) |
| `@residual` 数 (本 sweep で付与) | 0 | 25+ (見積もり、shared sorry 補題集約後) |
| shared sorry 補題 新規追加 | 0 | 2 (`debruijnIdentityV2_holds` + `integral_logDeriv_pdf_eq_zero_holds`、または `wall:stam` 集約により 1) |
| structure refactor 数 | 0 | 1 (`IsRegularDeBruijnHypV2` candidate 1 採用 default) |
| tier 5 defect 解消件数 | 0 | 5 (Phase 2 完了時、structure refactor + literal alias chain 5 件全解消) |
| `@audit:suspect` → sorry-based 移行件数 | 0 | 22 (Cluster B 5 + Cluster C 17) |
| `@audit:staged` 件数の変化 | 8 件 baseline | structure refactor 経由で減少予想 (Phase A `epi-debruijn-regularity` は honest として retain) |
| `@audit:retract-candidate` 件数の変化 | 23 件 baseline | retract 断行 candidate (`IsStamToEPIScalingHyp` 等) で減少予想、ただし retract 延期分は維持 |
| wall promote 件数 | 0 | 0-2 (`wall:debruijn-integration` + `wall:fisher-info-score-zero` 新規 candidate、judgment 次第) |
| touch する .lean file 数 | 0 (Phase 0 docs-only) | 13-14 (条件付き) |
| touch する .md file 数 | 1 (本 plan のみ) | 1 + 既存 plan 進捗 update 6-8 件 |
| commit 数 | 1 (本 plan 起草) | 7-12 (Phase 別 sub-step commit) |
| session 数 | 1 (Phase 0) | 5-10 (本 sweep 全体) |
