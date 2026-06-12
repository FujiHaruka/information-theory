# Channel coding strong converse (E-1) ムーンショット計画 🌙

**Status**: CLOSED ✅ — Verdú-Han 情報密度型の単発下界 (`1 - avgPe ≤ exp γ + tail`) を任意 code・任意 reference Q で publish。
**SoT**: `docs/textbook-roadmap.md` Ch.7。詳細履歴は git。

## 要点 (任意, ≤5 行)
- 採用経路: 情報密度 (information density) 下界 — Markov ineq + 集合分解の 2 段、Strong Stein の LLR-typicality plumbing を再利用 (Wolfowitz sphere packing / Strong typicality joint form は却下、長い)。
- asymptotic `Pe → 1` (WLLN-on-LLR 接続) は scope-deferred。`highLLRSet` の補集合が `steinTypicalSet` 系に reduce する経路で後続 plan に接続可能。
- 単発下界は任意の入力分布 (i.i.d./非 i.i.d.) に適用可、Pinsker/Stein/Sanov と並ぶ「Wolfowitz 鍵不等式」の Lean 化。
