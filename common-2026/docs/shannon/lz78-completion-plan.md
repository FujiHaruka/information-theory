# T4-A LZ78 漸近最適性 — 標準B完遂 実装サブ計画 🌙

**Status**: CLOSED ✅ — LZ78 (Ch.13) は 🟢 within scope。本 plan が狙った base-2 distinct headline の 2 primitive (distinct-phrase 組合せ Ziv / averaged Kraft converse) の genuine discharge は M3/M4 research-level として scope-out。
**SoT**: `docs/textbook-roadmap.md` Ch.13。詳細履歴は git。

> **Parent**:
> - [`lz78-moonshot-plan.md`](./lz78-moonshot-plan.md)
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 4 — T4-A. LZ78 漸近最適性」(Cover–Thomas Ch.13.5, Thm 13.5.3)

## 要点
- Ziv 上界の正しい route は distinct phrases を SET として stratum 別に log-sum を打つ組合せ論 (Cover–Thomas 13.5.5)。counting `c·log c ≤ K·n` は分布非依存の constant rate であり `-log Pₙ` (分布依存) とは別量 — 両者を繋ぐ bridge は無い (route (b) 不採用)。crux は per-stratum sub-distribution `∑ qⱼ ≤ 1`。telescoping の罠 (全 path で `∑ qⱼ ≈ c ≠ 1`) は stratum 別分解で回避。
- converse は averaged Kraft (`entropyD_le_expectedLength_of_kraft`) → Birkhoff a.s. lift 一択。pointwise `2^{-lz} ≤ Pₙ` は LZ78 universality ゆえ偽。`hreg` (full-support cylinder 正値) は退化分布で a.s. 化できないため明示 regularity 仮説 (load-bearing でない)。
