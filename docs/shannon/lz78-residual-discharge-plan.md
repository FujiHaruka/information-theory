# T4-A LZ78 漸近最適性 — 残 chain-hyp discharge 実装サブ計画 🌙

**Status**: CLOSED ✅ — LZ78 (Ch.13) は 🟢 within scope。本 plan が狙った 2 chain-hyp (`IsLZ78AchievabilityChainHyp` / `IsLZ78ConverseChainHyp`) の genuine discharge は M3/M4 research-level として scope-out (参照していた `LZ78FinalGlue` / `LZ78ConverseDischarge` / `LZ78SMBSandwich` 系は scope-out 削除済)。
**SoT**: `docs/textbook-roadmap.md` Ch.13。詳細履歴は git。

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md)
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」(Cover–Thomas Ch.13.5, Thm 13.5.3)

## 要点
- achievability crux = per-path parsing factorization。`blockRV` が射影で compProd 構造を持たないため cylinder 集合分解の手組み一択 (compProd telescoping 経路は適用先構造が無く実行不可)。L-LZ1 の counting 層は genuine 完成、残るは counting 量 n を `-log Pₙ` に差し替える橋のみ。
- converse は SMB 流用不可・bitLength 下界も建てず Kraft 経由一択。pointwise `2^{-lz} ≤ Pₙ` は per-path で偽 (universality)、averaged/Shannon-code 代用 → a.s. lift が健全経路。
