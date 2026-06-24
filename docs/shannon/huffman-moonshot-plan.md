# T1-A Huffman 最適性 ムーンショット計画 🌙

**Status**: CLOSED ✅ — Phase 3 完遂。`huffmanLength` の本物構成 (Multiset + `huffmanStep` Subtype/`HuffmanGrouping` invariant)、`huffmanLength_pos`、Kraft 充足、prefix code 副系を publish。主定理 optimality は後続 (T1-A' / cost-level pivot) で達成。
**SoT**: `docs/textbook-roadmap.md` Ch.5 (max-entropy は Ch.12)。詳細履歴は git。

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-A. Huffman 最適性 📋」
> **後続**: [`huffman-optimality-moonshot-plan.md`](./huffman-optimality-moonshot-plan.md) (T1-A')、[`huffman-optimality-t1apprime-moonshot-plan.md`](./huffman-optimality-t1apprime-moonshot-plan.md) (T1-A'')

## Phase 構成 (frozen、後続 doc が参照)

- Phase 1 — skeleton。Phase 2 — `huffmanLength` 構成。**Phase 3 — Kraft 充足 + 副系 (本 plan の DoD、達成済)**。
- Phase 4-5 (sibling property + 主定理 optimality) は本 plan scope-out → T1-A' へ分離。

## 要点

- 設計の core: `α → ℕ` 語長関数を主役にし、prefix code への昇格は既存 `exists_prefix_code_of_kraft` の黒箱呼び出し 1 件に閉じる。HuffmanTree inductive は不採用。
- 構成は `Multiset.strongInductionOn` ではなく `Nat.strongRec on s.card` を採用 (merge step `merged ::ₘ erase erase` が subset でないため Multiset の `<` が壊れる — plan §C-5 の当初設計が実装不可だった教訓)。
- `huffmanStep` は `Classical.choose` を裸書きすると `unfold` が opaque term を弾くため、spec を戻り値 Subtype に焼き込む (C-6)。Kraft 充足は `kraftPerGroup` 不変量 + `huffmanLengthAux_const_on_group` 経由。
