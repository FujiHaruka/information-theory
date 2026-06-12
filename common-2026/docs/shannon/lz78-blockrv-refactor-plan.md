# T4-A LZ78 漸近最適性 完遂 — blockRV/StationaryProcess kernel 層 サブ計画 🌙

**Status**: CLOSED ✅ — LZ78 (Ch.13) は 🟢 within scope。本 plan が狙った kernel 層 additive 注入による無仮定 distinct headline (両 per-path primitive の genuine 構成) は M3/M4 research-level として scope-out。
**SoT**: `docs/textbook-roadmap.md` Ch.13。詳細履歴は git。

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md)
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」(Cover–Thomas Ch.13.5, Thm 13.5.3)

## 要点
- parsing factorization `Pₙ{x} = ∏ⱼ qⱼ` を阻む根本原因は `blockRV` の射影性 (shift T + 単一観測 X のみ、kernel/compProd/disintegration 構造なし)。kernel 層を additive に注入する設計は Ch.4 を破壊せず可能 (構築サイト 0、全 consumer read-only) だが、ergodic + finite alphabet だけから kernel 層を genuine 構成する部分が M3/M4 upstream。
- kernel compatibility を「仮定だけ」で置くのは name laundering になる — 構成不能なら isolated honest hyp として明示する設計だった。
