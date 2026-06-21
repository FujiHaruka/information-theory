# EPI-Stam Cluster C — true sorry-based migration plan (Path 1)

**Status**: CLOSED ✅ — Cluster C の declaration-level load-bearing predicate を Tier 3 → Tier 2 (sorry + `@residual`) へ全件移行完了 (Phase V 独立 honesty audit 全 OK)。EPI family の実 sorry は route-T 後継で 0。(Stam Step 2: re-scope candidate — see 要点)
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-moonshot-plan.md`](epi-moonshot-plan.md)
> + [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md)
> + [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md)
>
> **Sister precedent**: [`awgn-m5-sorry-migration-plan.md`](awgn-m5-sorry-migration-plan.md) (AWGN M5、同型 Path 1)

## 要点

declaration-level load-bearing predicate を Honesty 階層 Tier 3 (`@audit:retract-candidate(load-bearing-predicate)`、bookkeeping) → Tier 2 (`sorry` + `@residual`、honest 撤退口) に格上げする「真の sorry-based migration」。AWGN M5 sister との最大の相違 = EPI-Stam の Mathlib 壁は既に shared sorry 補題化済みのため、Route B は「新規 wall file 新設」でなく「既存 wall lemma を consumer body から呼ぶ」。

**3 ルート分類 (再開時の設計枠組み)**:
- Route A — predicate 純削除 (hypothesis-form active consumer 0 の empty-consumers)。
- Route B — 既存 shared wall lemma に委任。de Bruijn 系 → `debruijnIdentityV2_holds` (debruijn-integration 壁、現 CLOSED) / Stam-scaling 系 → `stamToEPIBridge_holds` (legacy Stam route 削除済) or Phase A `csiszarGap_antitoneOn_*`。**regularity precondition (`Measurable`/`IndepFun`/`IsProbabilityMeasure`/Gaussian law) は残す** (load-bearing ではない)。
- Route C — bundle `IsEPIL3IntegratedPipeline` の `bridge` field を非 load-bearing 化 (bundle structure は残し field のみ除去)、consumer は `stamToEPIBridge_holds` を内部呼出。

**着地内容**: scope = 6 file (`EPIL3Integration` / `EPIStamToBridge` / `EPIStamDischarge` / `EntropyPowerInequality` + 構成子 file `EPIStamDeBruijnConclusion` / `EPIStamInequalityBody`、ripple `EPIPlumbing` / `HeatFlowPath`)。3 並列 Group (pipeline bundle / Stam-scaling / de Bruijn) で landing。新規 shared sorry 補題 4 件補充、新規 wall file 0 / 新規 wall name 0 (デフォルト plan slug `epi-stam-to-conclusion-phaseA-plan` で揃え、`docs/audit/audit-tags.md` 無変更)。

**Stam Step 2 re-scope candidate**: Stam-scaling 系の convex Fisher bound は **Rioul 2011 §II-C** (score-conditional-mean identity + total variance decomposition) で ~100 行 density-level computation の見積りあり (従来 ~300 行 PR 級より小) → roadmap Ch.17 行。

撤退ライン (履歴): L-EPISC-0-honest-defect (scope 拡張) / L-EPISC-1-α (de Bruijn 積分形補題補充) / L-EPISC-2-β (#3 phaseA-plan slug 委任) / L-EPISC-3-α (bridge field 非 load-bearing 化、採用方針) / L-EPISC-4-γ (新規 wall file 新設、不発) / L-EPISC-5-honest-defect (新規 defect 段階完了)。
