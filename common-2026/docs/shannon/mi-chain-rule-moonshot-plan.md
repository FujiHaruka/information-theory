# MI chain rule ムーンショット計画 🌙 (B-7)

**Status**: CLOSED ✅ — 一般 n 変数 chain rule `mutualInfo_chain_rule_fin` + i.i.d. corollary `mutualInfo_iid_eq_nsmul` (`I(X^n;Y^n) = n·I(X_0;Y_0)`) を publish。B-3 (channel coding achievability) の前段補題。
**SoT**: `docs/textbook-roadmap.md` Ch.2 (MI chain rule)。詳細履歴は git。

## 要点 (任意, ≤5 行)
- Phase A: `mutualInfo` の左引数 MeasurableEquiv 不変性 (`klDiv_map_measurableEquiv` を `e × id` で持ち上げ) → Pi reshape の基盤。
- Phase B (一般 chain rule): Han `jointEntropy_chain_rule` と対称な induction (`piFinSuccAbove` + 既存 2 変数 `mutualInfo_chain_rule` + IH + `Fin.sum_univ_castSucc`)。
- Phase C (i.i.d.): chain rule 経由でなく product 測度 KL 加法性で直接 (condMI=MI reduction の二度手間を回避)。仮定は「same-source の n コピー」形に簡略化。
- Inventory: [`mi-chain-rule-inventory.md`](mi-chain-rule-inventory.md)。
