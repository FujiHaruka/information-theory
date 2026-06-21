# AWGN MI bridge — `mutualInfoOfChannel` ↔ `h(Y) − h(Y|X)` plan (stub)

**Status**: CLOSED ✅ (2026-06-11、genuine) — per-letter bridge + density chain-rule すべて genuine discharge 済。詳細は下のブロック。

> **Status (2026-06-11)**: **CLOSED (genuine)**。① per-letter bridge は
> `awgn_per_letter_mi_bridge_genuine` (`AWGN/Converse.lean:552`、`@audit:ok`) で genuine 化済
> (mixture→compProd 因子分解 + generic continuous-channel MI chain rule asset + 混合 log-density
> 可積分性 + fibre entropy 平行移動不変)。`awgn_converse` body はその呼出に置換され、
> file scope 0 sorry。②③ (density chain-rule) も genuine discharge 済。
> → settled-facts は [`awgn-facts.md`](awgn-facts.md) を SoT とする。
> **Created**: 2026-05-24 (orphan suspect cleanup, defect-inventory-2026-05-24.md Wave 0)。

## Position

- 対象定理 (closure 済): per-letter bridge `awgn_per_letter_mi_bridge_genuine` (`InformationTheory/Shannon/AWGN/Converse.lean:552`、`@audit:ok`)
- 残作業 (converse とは独立): closed-form MI bridge `mutualInfoOfChannel_gaussianInput_closed_form'` (`InformationTheory/Shannon/AWGN/MIClosedForm.lean`) の `h_bridge` load-bearing 解消。旧 bare 形 `mutualInfoOfChannel_gaussianInput_closed_form` (旧 `AWGN.lean`) は retire 済
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
  `condEntropy` の対応物が必要。`InformationTheory.Shannon.differentialEntropy` (現在 Shannon
  family 内 def) と Mathlib `MeasureTheory.Entropy` の橋渡しの形が未確定。
- `InformationTheory.Shannon.differentialEntropy` を Mathlib 形に rewrite するか、
  bridge lemma を増やすか、設計判断が要る。

## Closure criteria

- ② ③ (per-channel decomposition / density chain-rule): **達成済 (genuine)** —
  `IsContChannelMIDecompHyp` / `IsAwgnMIDecomp` は genuine discharge。
- ① per-letter bridge: **達成済 (genuine)** — `awgn_per_letter_mi_bridge_genuine`
  (`AWGN/Converse.lean:552`、`@audit:ok`)。`h_mi_bridge_per_letter` は `awgn_converse`
  signature から落ち、body はその genuine bridge 呼出に置換。
- `mutualInfoOfChannel_gaussianInput_closed_form` の `h_bridge` (closed-form MI bridge、
  achievability/headline 側): converse closure とは独立の残作業。

## TODO

- [x] density chain-rule (②③) genuine discharge
- [x] ① per-letter bridge genuine 化 (`awgn_per_letter_mi_bridge_genuine`、commit `9d5edf1` + 監査 `34e58e7`)
- [ ] `mutualInfoOfChannel_gaussianInput_closed_form` の `h_bridge` load-bearing 解消
      (incidental-migration follow-up、converse とは独立)
