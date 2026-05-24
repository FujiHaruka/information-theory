# AWGN MI bridge — `mutualInfoOfChannel` ↔ `h(Y) − h(Y|X)` plan (stub)

> **Status**: 未着手 (Tier 3 stub)。実 body は別 session で `lean-planner` agent が起草する。
> **Created**: 2026-05-24 (orphan suspect cleanup, defect-inventory-2026-05-24.md Wave 0)。

## Position

- 対象定理: `Common2026/Shannon/AWGN.lean:123` `theorem mutualInfoOfChannel_gaussianInput_closed_form`
- 当該 tag: `@audit:suspect(awgn-mi-bridge-plan)` (line 122)
- 親 moonshot: [`awgn-moonshot-plan.md`](./awgn-moonshot-plan.md)
- 関連 plan: `awgn-mi-decomp-plan.md` (隣接 MI 分解), `awgn-converse-aux-plan.md`

## Motivation

`mutualInfoOfChannel_gaussianInput_closed_form` は AWGN F-2 hypothesis form で、Gaussian
入力下の channel mutual information を `(1/2) log(1 + P/N)` の閉形式に集約する。
現在 `h_bridge` という hypothesis として「`mutualInfoOfChannel` (Mathlib の KL form) =
`h(Y) − h(Y|X)` (textbook 形)」の bridge identity を取り、その後は
`differentialEntropy_gaussianReal` の純粋算術で `(1/2) log(1+P/N)` を導く。

`h_bridge` は本 plan で discharge 対象。

## Scope (将来の起草向けメモ)

- Mathlib 壁 4 分類のうち主分類: (a) 定義整合 — Mathlib の `mutualInfoOfChannel` は
  generic KL form (`KL(joint ‖ marginal⊗channel)`); 一方 textbook 公式は
  `h(Y) − h(Y|X)` 形。両者の identity は `Y ∼ 𝒩(0, P+N)` (Y marginal の Gaussian 性) +
  `Y|X=x ∼ 𝒩(x, N)` (channel の AWGN 性) で成立するが、Mathlib 側の `mutualInfoOfChannel`
  ↔ `differentialEntropy` bridge は現状未提供 (Csiszar 関連の inventory 結果に依存)。
- Tier: 3 (long-term residual; achievability F-1 が先)。
- `awgn-converse-aux-plan` 側 Gaussian Y_i bound と同じ Gaussian MI 解析を共有可能。

## Open questions

- bridge `mutualInfoOfChannel = h(Y) − h(Y|X)` は Mathlib の `condMutualInfo` /
  `condEntropy` の対応物が必要。`Common2026.Shannon.differentialEntropy` (現在 Shannon
  family 内 def) と Mathlib `MeasureTheory.Entropy` の橋渡しの形が未確定。
- `Common2026.Shannon.differentialEntropy` を Mathlib 形に rewrite するか、
  bridge lemma を増やすか、設計判断が要る。

## Closure criteria

- `h_bridge` 引数を `theorem mutualInfoOfChannel_gaussianInput_closed_form` から削除
  (genuine discharge)、または別の `IsAwgnGaussianMIBridge` staged predicate に振り替え。
- `@audit:suspect(awgn-mi-bridge-plan)` を `@audit:ok` または `@audit:staged(...)` に降格。

## TODO

- [ ] `lean-planner` で Phase 設計 (`Common2026.Shannon.differentialEntropy` の Mathlib
      対応物 inventory を mathlib-inventory に先行依頼するのが筋)
