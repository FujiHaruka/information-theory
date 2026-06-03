# Prékopa–Leindler inequality — induction discharge plan (stub)

> **Status**: 未着手 (Tier 3 stub)。実 body は別 session で `lean-planner` agent が起草する。
> **Created**: 2026-05-24 (orphan suspect cleanup, defect-inventory-2026-05-24.md Wave 0)。

## Position

- 対象定理: `InformationTheory/Shannon/BrunnMinkowskiFunctional.lean:210`
  `theorem prekopa_leindler_inequality`
- 当該 tag: `@audit:suspect(prekopa-leindler-induction-plan)` (line 209)
- 親 moonshot: [`brunn-minkowski-moonshot-plan.md`](./brunn-minkowski-moonshot-plan.md)
- 関連 plan: [`brunn-minkowski-closure-plan.md`](./brunn-minkowski-closure-plan.md),
  [`brunn-minkowski-from-epi-discharge-plan.md`](./brunn-minkowski-from-epi-discharge-plan.md)

## Motivation

`prekopa_leindler_inequality` (Cover-Thomas Theorem 17.9.5) は本 plan で genuine
discharge 対象。現在は `h_pl_assumed : IsPrekopaLeindlerHyp f g h λ intF intG intH`
を load-bearing hyp として取り、body は `h_pl_assumed.bound` の field 適用。
hypothesis 自身が結論を主張する circular shape。

1 次元特殊 case は既に `BrunnMinkowskiLayerCakeBody` / `BrunnMinkowskiPLBody` 内で
discharged 済 (`isPrekopaLeindlerHyp_of_layercake` 等が L-PL1 を construct する経路を提供)。
本 plan の主担当は **n 帰納の本格化**: `n` に関する帰納 + 1-dim Hölder 経路で
高次元 L-PL1 を構成する。

## Scope (将来の起草向けメモ)

- Mathlib 壁 4 分類のうち主分類: (b) 解析 (Hölder + 帰納) + (a) 定義整合 (multi-dim
  Lebesgue 積分の slicing と product measure の bridge)。
- Tier: 3 (long-term; brunn-minkowski-closure-plan の主入力)。

## Closure criteria

- `theorem prekopa_leindler_inequality` から `h_pl_assumed` 引数を削除 (genuine
  discharge)、`IsPrekopaLeindlerHyp` 自身を `theorem` に格上げ。
- `@audit:suspect(prekopa-leindler-induction-plan)` を `@audit:ok` に降格。
- 連鎖効果: BrunnMinkowskiClosure 系の suspect 30 件のうち、L-PL 直依存分が close
  可能になる (closure 計画側で具体マップを取る)。

## TODO

- [ ] `lean-planner` で Phase 設計 (1-dim base case → n → n+1 induction step の skeleton
      → product measure 上の slice 化補題 inventory)
- [ ] `mathlib-inventory` で Mathlib の `MeasureTheory.Measure.prod` slicing /
      Tonelli / Hölder n-variable の在庫確認を先行
