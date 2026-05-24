# EPI Stam → EPI conclusion — merge / conclusion plan (stub)

> **Status**: 未着手 (sub-plan stub)。本 body / Phase 設計は別 session で `lean-planner`
> agent が起草する。
> **Created**: 2026-05-24 (Wave 1.5 item #8、`epi-moonshot-plan` 76 件 slug 分割)。
> **Parent (history)**: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (PASS-THROUGH publish 済、
> 撤退ライン L-EPI3 = EPI 結論そのものの genuine discharge を本 sub-plan が担当)。

## Position

- 親 moonshot: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (Phase A-E publish 済、L-EPI3
  hypothesis pass-through)
- 関連 sub-plan:
  - [`epi-stam-discharge-plan.md`](./epi-stam-discharge-plan.md) — L-EPI1 (Stam inequality)
    上流入力
  - [`epi-debruijn-integration-plan.md`](./epi-debruijn-integration-plan.md) — L-EPI2
    (de Bruijn integration) 上流入力
- 関連 wall plan: `fisher-info-moonshot-plan.md` / V2 系

## Motivation

EPI moonshot は L-EPI3 (EPI 結論自身) を `IsEntropyPowerInequalityHypothesis` predicate
hypothesis pass-through 形で publish。Stam (L-EPI1) + de Bruijn integration (L-EPI2) →
EPI conclusion の合流部、および Phase E 補助 corollary 群 (multi-arg, monotonicity, scaling,
log-form) の genuine 化が本 sub-plan の責務。

`epi-moonshot-plan.md` §C で「`stam → ∫_0^∞ deBruijn → EPI`」を予告しており、本 sub-plan
は **Stam + de Bruijn の合成 → EPI conclusion の組み立て + 露出 corollary** に集中する
(Stam 内部 / de Bruijn 内部の本格 discharge は sister sub-plan に委譲)。

## Scope (将来の起草向けメモ)

担当 file 群 (W1-B `wave1-plan-sync-epi-bm.md` ベース):

| file | 役割 | suspect 件数 |
|---|---|---|
| `Common2026/Shannon/EPIStamStep3Body.lean` | Stam Step 3 body (Lagrange multiplier / λ 最適化) | 9 |
| `Common2026/Shannon/EPIStamDeBruijnConclusion.lean` | Stam + de Bruijn → conclusion 合流 | 6 |
| `Common2026/Shannon/EntropyPowerInequality.lean` | EPI 主定理 + Phase E corollary (multi-arg / log-form / scaling) | 5 |
| `Common2026/Shannon/EPIPlumbing.lean` | EPI plumbing (normalized form / four-arg / `Real.exp` ↔ log 等価変換) | 3 |

**合計**: 23 件 suspect (sub-plan 起動時の closure target)。

- Mathlib 壁 4 分類のうち主分類:
  - Stam + de Bruijn の合成自体は (a) 定義整合 + (c) 配線中心 — sister sub-plan が discharge
    すれば本 sub-plan は medium ROI (Mathlib `Real.exp_*` / `Real.log_*` の配線で済む corollary
    が多い)。
  - `EPIPlumbing.lean` 3 件は high ROI (log-form 等価変換、L-EPI3 連鎖から trivial)。
  - `EntropyPowerInequality.lean` の Phase E corollary 群は medium (Phase E の plan §D
    multi-arg / scaling 設計と対応)。
  - `EPIStamStep3Body.lean` Lagrange optimization は medium (Mathlib `optimal_lambda` 系
    発掘で進む)。
- Tier: 3 (long-term、ただし `EPIPlumbing.lean` 3 件は単独で先行 close 可能 — Wave 1.5 後の
  早期 high-ROI 候補)。

## Closure criteria

- 主定理 `entropy_power_inequality` から L-EPI3 hypothesis 引数を削除 (genuine discharge)、
  `IsEntropyPowerInequalityHypothesis` 自身を `theorem` に格上げ。
- Phase E corollary 群 (multi-arg / scaling / log-form / normalized / four-arg) を全て
  genuine 化、`@audit:suspect(epi-stam-to-conclusion-plan)` を `@audit:ok` に降格 (23 件)。
- 連鎖効果: sister sub-plan (`epi-stam-discharge-plan` 39 + `epi-debruijn-integration-plan` 14)
  の closure と組み合わせて EPI エコシステム全 76 件 close。

## TODO

- [ ] `lean-planner` で Phase 設計 (Phase A: Stam + de Bruijn 合成の skeleton →
      Phase B: Phase E corollary 各種 (normalized / four-arg / multi-arg / log-form /
      scaling) の genuine 化 → Phase V: verify)
- [ ] `EPIPlumbing.lean` 3 件 (high ROI) を先行 close する Phase 0 を検討
      (`entropy_power_inequality_normalized`, `entropy_power_inequality_four_arg`,
      `two_differentialEntropy_ge_log_sum`)
- [ ] `EPIStamStep3Body.lean` の Lagrange multiplier 経路 (Mathlib `optimal_lambda` 系)
      の inventory を sister `epi-stam-discharge-plan` と協調して取る
