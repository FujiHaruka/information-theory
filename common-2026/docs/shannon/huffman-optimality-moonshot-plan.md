# T1-A' Huffman 最適性 (sibling property + 任意 `l` 比較) ムーンショット計画 🌙

**Status**: CLOSED ✅ — weak form `huffmanLength_optimal_with_hypotheses` (2 hypothesis 引数受け取り) + `exists_sibling_min_pair` を publish。元 2 hypothesis の discharge は T1-A'' へ送り、最終的に cost-level pivot で genuine 強形 `huffmanLength_optimal` が達成済 (weak-form wrapper は superseded)。
**SoT**: `docs/textbook-roadmap.md` Ch.5 (max-entropy は Ch.12)。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A'. Huffman 最適性 (sibling property + 任意 `l` 比較)」
> - 先行 (T1-A 完了): [`huffman-moonshot-plan.md`](./huffman-moonshot-plan.md)
> **後続**: [`huffman-optimality-t1apprime-moonshot-plan.md`](./huffman-optimality-t1apprime-moonshot-plan.md) (T1-A'')

## 要点

- 設計の core: T1-A の `huffmanLength` を黒箱 reuse し、merged 型は Subtype `{ x : α // x ≠ b }` (Mathlib type-class auto-derive、Quotient 経路は不採用)。`Fintype.card α` 上 `Nat.strong_induction_on` で n→n-1 縮約。
- weak form に落ちた経緯: 2-step swap 単独では任意 Kraft-feasible `l` を `l a = l b` に normalize できない反例 (`l = (3,1,2)`) があり、full binary tree (Kraft = 1) shortening が要る。また sibling 単独では merged-measure identification に不足し min-prob 強化が要る。両者を 2 hypothesis として外出しした。
