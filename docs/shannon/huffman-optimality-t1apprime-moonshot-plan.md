# T1-A'' Huffman 最適性 (2 hypothesis 完全 discharge) ムーンショット計画 🌙

**Status**: CLOSED ✅ — 本 plan が target とした 2 hypothesis の直接 discharge は到達せず (per-symbol depth identity が FALSE と確定)。Hyp1 (swap normalization) は genuine discharge 済、強形 `huffmanLength_optimal` (Cover-Thomas 5.8.1、無条件) は別経路 (cost-level pivot) で genuine 達成済。
**SoT**: `docs/textbook-roadmap.md` Ch.5 (max-entropy は Ch.12)。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A''. Huffman 最適性 (2 hypothesis 完全 discharge)」
> - 先行 (T1-A 完了): [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md)
> - 直接前任 (T1-A' 完了, weak form publish): [`huffman-optimality-moonshot-plan.md`](./huffman-optimality-moonshot-plan.md)

## 要点

- Goal だった 2 hypothesis discharge のうち、Hyp2 系 (`HuffmanMergedIdentificationHypothesis` / per-symbol depth identity) は universal statement として FALSE と機械検証で確定 (決定的 colex tie-break の merge 不安定性)。
- 計画していた縦分解 (`EqualizingPermHypothesis` 等のさらなる analytic hypothesis 化) も dead-end。実装は当初 Phase A (bubble sort metric + shortening) / Phase B (Subtype-lift Multiset bridging) の規模超過で no-op 維持されていた。
- 強形 closure は per-symbol identity を経由せず、tie-invariant な cost-level merge 漸化式 (cost は確率多重集合のみで決まり label/carrier 非依存) で達成。後続は `huffman-cost-level-optimality-plan.md`。
