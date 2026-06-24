# Sanov LDP B 形 (B-1') ムーンショット計画 🌙

**Status**: CLOSED ✅ — Sanov LDP B 形 upper bound (Cover-Thomas Thm 11.4.1 main statement) を `InformationTheory/Shannon/SanovLDP.lean` で publish 完了。equality 形は別 plan `sanov-ldp-equality-plan.md` で完成済。既存 A 形 (`Sanov.lean`) と並立。
**SoT**: `docs/shannon/cramer-facts.md` + `docs/textbook-roadmap.md` Ch.11。詳細履歴は git。

## 要点 (≤5 行)
- 核アイデア: A 形 type-class upper bound を `𝒫_n` 上の有限 union に拡張するだけで LDP upper bound が出る。多項係数 (`Nat.multinomial`) 経路は不要。
- polynomial type 数 `(n+1)^|α|` を `log(n+1)/n → 0` (`Real.isLittleO_log_id_atTop`) で潰して eventually upper bound に。
- 集合 `E` は型 index レベル (`∀ n, Finset (TypeCountIndex α n)`) で与える設計 (probability-simplex topology 案件は equality 側に押し付け)。
- 採用 path: A 形 (Stein per-point ratio) の index 形書き直し。`c a = 0` letter の境界処理は `x ∈ T_c ⇒ c (x i) ≥ 1` 観察で自動。
