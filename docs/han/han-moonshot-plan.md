# Han 不等式・ムーンショット計画 🌙

**Status**: CLOSED ✅ — Han の不等式（補集合形）`han_inequality` + `jointEntropy_chain_rule` を実装。Phase 0/A/B/C 全完了。
**SoT**: `docs/textbook-roadmap.md` Ch.17 Han。詳細履歴は git。

> **Mathlib inventory**: [`han-mathlib-inventory.md`](han-mathlib-inventory.md)
> **後継**: [`han-phase-d-plan.md`](han-phase-d-plan.md)（subset average → Shearer）

## 要点 (≤5 行)
- 既存 `InformationTheory/Shannon` API への薄いラッパーで通す方針（`jointEntropy` = `entropy` の `Fin n → α` 特殊化）。主内容は `mutualInfo_*` / chain rule から導出。
- 退化ケース `n = 0, 1` も同じ証明で通り、当初の `hn : 1 ≤ n` 仮定は不要と判明（削除）。
- 山場は Phase A の中間補題 `condMutualInfo_eq_condEntropy_sub_condEntropy` と Phase B の `Fin n` induction。Pi 値 RV の measurability instance は自動発火。
- 浮き上がった共通 plumbing: `MeasurableEquiv.piCongrLeft` + `sumPiEquivProdPi` + `funUnique` の 3 点セット、`entropy_measurableEquiv_comp`。
