# AWGN converse: C-5 transitive MI 有限性 bridge mini-plan

**Status**: CLOSED ✅ — converse の transitive MI 有限性 bridge を closure (per-letter MI ne_top → Finset.sum → X^n → W、Markov DPI 経由)。
**SoT**: `docs/shannon/awgn-facts.md` (achievement table) + `docs/textbook-roadmap.md` Ch.9。詳細履歴は git。

> **Parent**: [`awgn-converse-aux-plan.md`](awgn-converse-aux-plan.md) §「Phase C」C-5 項

## 要点 (将来作業で再利用しうる路)
- 戦略: per-letter MI `≠ ∞` を `klDiv_ne_top` (AC + integrable llr) で立て、`ENNReal.sum_ne_top` で `∑ᵢ ≠ ∞` → `mutualInfo_le_of_markov` (ENNReal 形) + `ne_top_of_le_ne_top` で W 側へ伝播。
- 退化境界 trap: Real 形 chain rule `(jointMIXnYn).toReal ≤ ∑ .toReal` からの ENNReal-lift は `toReal_le_toReal` が両側 ne_top 前提のため構造的に循環で不可 → ENNReal 形 bound を別途要する。per-letter ne_top は M1 結果 `.toReal ≤ R` から直接出ない (independent klDiv route が必要)。
