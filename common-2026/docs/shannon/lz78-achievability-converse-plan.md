# T4-A LZ78 achievability + converse 組合せ核心 full-closure ムーンショット計画 🌙

**Status**: CLOSED ✅ — LZ78 (Cover-Thomas Ch.13) は 🟢 within scope (M1 converse + headline done)。本 plan が狙った achievability/converse の per-path 組合せ核心 (Eq.13.124 / 13.130) は M3/M4 research-level として scope-out。
**SoT**: `docs/textbook-roadmap.md` Ch.13。詳細履歴は git。

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md)
> - [`lz78-ziv-inequality-discharge-moonshot-plan.md`](./lz78-ziv-inequality-discharge-moonshot-plan.md)
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A LZ78 漸近最適性」(Ch.13)

## 要点
- per-path Ziv `c·log c ≤ -log Pₙ{x}` の crux は parsing factorization (telescoping)。`blockRV` が単純射影で kernel/compProd 構造を持たないため、cylinder 手組み (または kernel 層 additive 注入) が要り、M3/M4 upstream 扱い。
- converse は SMB 流用では閉じず Kraft 経由一択 — pointwise Shannon-code 経路 (`2^{-lz} ≤ Pₙ`) は LZ78 universality ゆえ per-path で偽、averaged Kraft → ergodic a.s. lift のみ健全。
