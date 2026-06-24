# 最大エントロピー ムーンショット計画 🌙 (B-6)

**Status**: CLOSED ✅ — `entropy_le_log_card` + 等号条件 `entropy_eq_log_card_iff` を genuine publish。KL identity `klDiv (μ.map X) (uniformOn univ) = log |α| - entropy` 経由。
**SoT**: `docs/textbook-roadmap.md` Ch.12。詳細履歴は git。

## 要点

- 設計の core: 既存 `klDiv` 上に薄い 3 段 (identity → `klDiv ≥ 0` で上界 → `klDiv_eq_zero_iff` で等号) で乗せる。`P ≪ uniformOn univ` は各 singleton mass `1/|α| > 0` から automatic。
- `klDiv_discrete_toReal_eq_sum` (Bridge.lean) は private だが、`Q = uniformOn` 特化形では `toReal_klDiv_of_measure_eq` 直接ルートが最短。
