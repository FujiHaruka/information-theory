# Shannon コード Kraft 逆向き (B-8') ムーンショット計画 🌙

**Status**: CLOSED ✅ — `exists_prefix_code_of_kraft` (Kraft 充足 ⟹ prefix code 存在、McMillan 逆形 / Cover-Thomas 5.2.1) を genuine publish。Shannon-Fano D-進数構成。
**SoT**: `docs/textbook-roadmap.md` Ch.5。詳細履歴は git。

## 要点

- 採用構成: D-進数 (Shannon-Fano) — sort-by-length → 累積和 `slotStart` → `toBaseDLen` で base-`D` MSB-first 固定長表現。Greedy with set-of-used-prefixes は state 管理が重く不採用。
- `Nat.digits` (Mathlib) は LSB-first / 可変長で `IsPrefix` との接続が悪く不採用、独自 `toBaseDLen` (MSB-first / 固定長 / `Fin D` valued) で補題数を抑えた。
- prefix code は構造体化せず述語形 (`Function.Injective` + `IsPrefixFree`) で完結。Mathlib に prefix code 構造体は無い (`UniquelyDecodable` + `kraft_mcmillan_inequality` のみ)、本実装は独立。
- `hl : ∀ a, 0 < l a` は API 整合のため残すが proof では未使用 (長さ 0 の空 list は trivially prefix で prefix-free を壊すための仕様上の前提)。
