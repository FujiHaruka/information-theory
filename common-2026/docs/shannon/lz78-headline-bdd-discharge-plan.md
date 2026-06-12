# LZ78 headline: boundedness 2 件 internal discharge サブ計画

**Status**: CLOSED ✅ — LZ78 (Ch.13) は 🟢 within scope (headline done)。boundedness 2 件 (`h_bdd_above` / `h_bdd_below`) の internal discharge は bit-layer counting envelope で elementary に完結。残る `h_lower` / `h_upper` (Cover-Thomas Eq.13.124 / 13.130) は M3/M4 research-level として scope-out 維持。
**SoT**: `docs/textbook-roadmap.md` Ch.13。詳細履歴は git。

> **Parent**: `docs/textbook-roadmap.md` §13 Ch.13 LZ78

## 要点
- boundedness は `c(n) = O(n/log n)` 計数包絡 × per-phrase `bitLength = O(log n)` = rate `=O 1` で elementary に discharge できる雑用。これを internal 化して hypothesis 表面積を 4 → 2 に縮小する設計。M3/M4 scope-out は撤回しない。
- 削除済 file の旧 §4 headline は load-bearing predicate (`Is*ChainHyp`) bundling の tier-5 defect。本 plan は当該 defect を継承せず raw `∀ᵐ ω ∂μ, ...` hypothesis 形のみで構成する方針だった。
