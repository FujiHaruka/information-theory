# Han Phase D ロードマップ: subset average → Shearer 🌙

**Status**: CLOSED ✅ — Han 1978 subset average 形（`subset_average_chain`）+ Shearer の不等式（`shearer_inequality`）+ subset infrastructure を実装。Phase 0/A/B/C 全完了（累計 8 主定理）。
**SoT**: `docs/textbook-roadmap.md` Ch.17 Han。詳細履歴は git。

> **Parent (本体)**: [`han-moonshot-plan.md`](han-moonshot-plan.md)
> **Mathlib inventory**: [`han-phase-d-mathlib-inventory.md`](han-phase-d-mathlib-inventory.md)

## 要点 (≤5 行)
- D-1（subset average）と D-2（Shearer）は engine を共有: subset 版 chain rule + subset 版 conditioning monotonicity の 2 本。Phase A で一度作り 2 用途で擦る。
- `jointEntropySubset μ Xs S`（`S : Finset (Fin n)`）導入。`han_inequality_subset` は `Finset.orderEmbOfFin` + `entropy_measurableEquiv_comp` で既存 `han_inequality` に帰着。
- Phase B 二重和 reindex（`∑_{|S|=k+1}∑_{i∈S} f(S\{i}) = (n-k)∑_{|T|=k} f(T)`）は `sum_finset_product'` + `sum_bij'` テンプレで圧縮。
- Shearer は Han 本体を呼ばず engine（chain rule + monotonicity）のみで構成。`condEntropy_nonneg` は Mathlib/project に無く手書き（再利用なら別ファイル切り出し検討）。
