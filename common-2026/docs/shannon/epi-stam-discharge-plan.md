# EPI Stam inequality — discharge plan (stub)

> **Status**: 未着手 (sub-plan stub)。本 body / Phase 設計は別 session で `lean-planner`
> agent が起草する。
> **Created**: 2026-05-24 (Wave 1.5 item #8、`epi-moonshot-plan` 76 件 slug 分割)。
> **Parent (history)**: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (PASS-THROUGH publish 済、
> 撤退ライン L-EPI1+L-EPI2+L-EPI3 全採用、本 sub-plan は L-EPI1 = Stam inequality の genuine
> discharge を担当)。

## Position

- 親 moonshot: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (Phase A-E publish 済、L-EPI1
  hypothesis pass-through)
- 関連 sub-plan:
  - [`epi-debruijn-integration-plan.md`](./epi-debruijn-integration-plan.md) — L-EPI2
    (de Bruijn integration) sister
  - [`epi-stam-to-conclusion-plan.md`](./epi-stam-to-conclusion-plan.md) — Stam + de Bruijn →
    EPI conclusion 合流部
- 関連 wall plan: `fisher-info-moonshot-plan.md` / V2 系 (Stam inverse-Fisher は Fisher info
  V2 経路の上流)

## Motivation

EPI moonshot は L-EPI1 (Stam inequality) を `IsStamInequalityHypothesis` predicate
hypothesis pass-through 形で publish。実際の Stam inequality discharge は本 sub-plan の
責務。Stam の核心 (`1/J(X+Y) ≥ 1/J(X) + 1/J(Y)`) を Cauchy-Schwarz + λ-optimization
+ score convolution で構成し、Fisher info の inverse 形 inequality を確立する。

## Scope (将来の起草向けメモ)

担当 file 群 (W1-B `wave1-plan-sync-epi-bm.md` ベース):

| file | 役割 | suspect 件数 |
|---|---|---|
| `Common2026/Shannon/EPIStamDischarge.lean` | Stam discharge 主 follow-up | 15 |
| `Common2026/Shannon/EPIStamToBridge.lean` | Stam scaling decomposition + bridge wrappers | 14 |
| `Common2026/Shannon/EPIStamInequalityBody.lean` | Stam inequality body (Cauchy-Schwarz + AM-GM) | 5 |
| `Common2026/Shannon/EPIStamStep12Body.lean` | Stam Step 1+2 body (score convolution + Cauchy-Schwarz) | 5 |

**合計**: 39 件 suspect (sub-plan 起動時の closure target)。

- Mathlib 壁 4 分類のうち主分類: (b) 解析 — Stam inverse-Fisher inequality は Mathlib に
  対応 lemma が不在 (Fisher info 自体が V2 経路で genuine 化途上、V1 は representative-dependence
  flaw)。本 sub-plan は V2 Fisher info 経路に依存。
- Tier: 3 (long-term)。Stam 単独の Phase A inventory + Phase B-D 解析 (Cauchy-Schwarz λ
  optimization + score convolution) が必要。
- 副入力: `EPIStamInequalityBody.lean` 内に既に `stam_lambda_min` / `stam_inverse_form_of_harmonic_mean`
  等の補助補題が用意されており、これらの connecting 経路の整理が Phase B の主タスク。

## Closure criteria

- 各 declaration から Stam-hypothesis 引数を削除 (genuine discharge)、`IsStamInequalityHypothesis`
  自身を `theorem` に格上げ。
- `@audit:suspect(epi-stam-discharge-plan)` を `@audit:ok` に降格 (39 件 + Step3/Conclusion
  経路含めれば連鎖閉)。
- 連鎖効果: `epi-stam-to-conclusion-plan` 経由で EPI conclusion 23 件と連鎖閉 (合計 62 件)。

## TODO

- [ ] `lean-planner` で Phase 設計 (Phase A: Cauchy-Schwarz + AM-GM inventory →
      Phase B: score convolution → Phase C: λ-optimization → Phase D: inverse-Fisher
      合成 → Phase V: verify)
- [ ] `mathlib-inventory` で Mathlib の `MeasureTheory.integral_mul_le_L2_norm_mul_L2_norm`
      系 + Fisher info V2 経路の在庫確認を先行
- [ ] V2 Fisher info との接続点 (`FisherInfoV2.lean` の export) を明確化
