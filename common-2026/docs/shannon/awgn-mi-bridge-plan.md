# AWGN MI bridge — `mutualInfoOfChannel` ↔ `h(Y) − h(Y|X)` plan (stub)

> **Status (2026-05-28)**: density chain-rule (per-channel decomposition) 壁が shared sorry
> `contChannelMIDecomp_holds` (`AwgnWalls.lean`、`@residual(wall:awgn-mi-decomp)`) **1 本に集約済**
> (commit `9ccbb67`)。`docs/audit/audit-tags.md` Wall name register に `awgn-mi-decomp` 追記済。
> ②③ (`IsContChannelMIDecompHyp` / `IsAwgnMIDecomp`) は genuine discharge 確認済。
> **残**: ① per-letter bridge (`AWGNConverse.lean` `h_mi_bridge_per_letter`、
> `@residual(plan:awgn-mi-bridge-plan)`) は mixture→compProd 因子分解 plumbing 待ちで残置。
> honesty audit (commit `5c5d94d`) で `mutualInfoOfChannel_gaussianInput_closed_form` がまだ
> `h_bridge` load-bearing と判明 (incidental-migration follow-up、本 plan に未折込)。
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

- ② ③ (per-channel decomposition / density chain-rule): **達成済** — `contChannelMIDecomp_holds`
  (`AwgnWalls.lean`、`@residual(wall:awgn-mi-decomp)`) に集約、`IsContChannelMIDecompHyp` /
  `IsAwgnMIDecomp` は genuine discharge。
- ① per-letter bridge: `h_mi_bridge_per_letter` 引数を `AWGNConverse.lean` から削除
  (genuine discharge)、mixture→compProd 因子分解 plumbing が必要。`@residual(plan:awgn-mi-bridge-plan)`
  の closure 担当。
- `mutualInfoOfChannel_gaussianInput_closed_form` の `h_bridge` 引数を削除 (incidental-migration
  follow-up、honesty audit `5c5d94d` で load-bearing と確認、本 plan に未折込)。

## TODO

- [x] density chain-rule 壁を shared sorry `contChannelMIDecomp_holds` に集約 (`9ccbb67`)、
      `awgn-mi-decomp` register 追記済
- [ ] ① per-letter bridge の mixture→compProd 因子分解 plumbing
- [ ] `mutualInfoOfChannel_gaussianInput_closed_form` の `h_bridge` load-bearing 解消
      (incidental-migration follow-up)
