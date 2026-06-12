# Huffman 2-hypothesis vertical reduction — 集約計画 🌙

**Status**: CLOSED ✅ — Huffman 強形最適性 (`huffmanLength_optimal`, Cover-Thomas 5.8.1) は cost-level pivot で genuine 達成済。本 plan が discharge target としていた per-symbol depth identity (2 hypothesis → vertical-reduction primitive 経由) は FALSE と確定し、別経路で closure。
**SoT**: `docs/textbook-roadmap.md` Ch.5 (max-entropy は Ch.12)。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A''. Huffman 最適性 (2 hypothesis 完全 discharge)」
> - [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md)
> - [`huffman-optimality-moonshot-plan.md`](./huffman-optimality-moonshot-plan.md)
> - [`huffman-t1apprime-partial-moonshot-plan.md`](./huffman-t1apprime-partial-moonshot-plan.md)

## 要点

- スラグ `huffman-2hyp-vertical-reduction` は今もコード側の `@residual(plan:huffman-2hyp-vertical-reduction)` (vertical-reduction wrapper / extractor 群) が参照しているため残す。これらは現在 dead な縦分解経路 (cost-level pivot で superseded) の bookkeeping。
- per-symbol depth identity (`HuffmanMergedIdentificationHypothesis` / `MergedHuffmanAuxIdentHypothesis`) は universal statement として FALSE。決定的 colex tie-break の merge 不安定性が根本原因。
- pivot: tie-invariant な cost-level merge identity (cost は確率多重集合のみで決まり label/carrier 非依存) で genuine closure。後続は `huffman-cost-level-optimality-plan.md`。
