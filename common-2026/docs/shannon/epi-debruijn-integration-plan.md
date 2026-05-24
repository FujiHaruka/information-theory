# EPI de Bruijn integration — discharge plan (stub)

> **Status**: 未着手 (sub-plan stub)。本 body / Phase 設計は別 session で `lean-planner`
> agent が起草する。
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
    (V2 経路で `deBruijn_identity_v2` 系が genuine 化途上)
  - [`fisher-info-gaussian-discharge-moonshot-plan.md`](./fisher-info-gaussian-discharge-moonshot-plan.md)

## Motivation

EPI moonshot は L-EPI2 (de Bruijn integration) を `IsDeBruijnIntegrationHypothesis` predicate
hypothesis pass-through 形で publish。実際の de Bruijn integration の本格 discharge は本
sub-plan の責務。

`Common2026/Shannon/EPIL3Integration.lean` には EPI L3 integrated pipeline が pass-through
composition で集約されており、上流 1 件 (`epi_l3_of_integrated_pipeline` 等) が genuine 化
すると全 19 件下流 (うち本 sub-plan 担当の 14 件 + 他経路 5 件) が連鎖閉する構造になっている。

## Scope (将来の起草向けメモ)

担当 file 群 (W1-B `wave1-plan-sync-epi-bm.md` ベース):

| file | 役割 | suspect 件数 |
|---|---|---|
| `Common2026/Shannon/EPIL3Integration.lean` | EPI L3 integrated pipeline (de Bruijn 積分経路の集約 file) | 14 |

**合計**: 14 件 suspect (sub-plan 起動時の closure target)。
**他経路**: 同 file の残り 5 件 (Phase E 補助 corollary multi-arg / monotonicity / scaling /
log-form) は `epi-stam-to-conclusion-plan` 側に分類されている可能性あり (起草時に再確認)。

- Mathlib 壁 4 分類のうち主分類: (b) 解析 — heat-equation IBP (integration by parts in time)
  が Mathlib に直接対応 lemma 不在。Fisher info V2 + heat flow density の sub-predicate
  decomposition (`IsHeatSpatialDerivHyp` / `IsHeatTimeDerivHyp` / `IsHeatFlowConvolutionHyp` /
  `IsIBPHypothesis`) を経由する必要がある。
- Tier: 3 (long-term)。`fisher-info-moonshot-plan` V2 経路の進捗に依存。
- 連鎖クローズ: L3 integration pipeline の上流 1 declaration genuine 化で 14 件一斉 close
  (W1-B 報告書「EPI L3 integrated pipeline の上流 1 件 close → 19 件連鎖閉」)。

## Closure criteria

- 各 declaration から de Bruijn-hypothesis 引数を削除 (genuine discharge)、
  `IsDeBruijnIntegrationHypothesis` 自身を `theorem` に格上げ。
- `@audit:suspect(epi-debruijn-integration-plan)` を `@audit:ok` に降格 (14 件)。
- 連鎖効果: `epi-stam-to-conclusion-plan` 経由で EPI conclusion 23 件と連鎖閉。

## TODO

- [ ] `lean-planner` で Phase 設計 (Phase A: heat-flow density + IBP inventory →
      Phase B: time-derivative of entropy → Phase C: integration over (0, ∞) → Phase D:
      reduction to L-EPI3 form → Phase V: verify)
- [ ] `mathlib-inventory` で Mathlib の `MeasureTheory.integral_deriv_*` 系 + heat kernel
      API (`MeasureTheory.gaussianPdfReal`, `Convolution`) の在庫確認
- [ ] V2 Fisher info (`FisherInfoV2DeBruijn.lean` / `FisherInfoV2HeatFlowBody.lean`) の
      sub-predicate decomposition との接続点を明確化
