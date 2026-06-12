# Shannon: Wyner–Ziv Phase 2.x — load-bearing predicate residue removal

**Status**: CLOSED ✅ — Wyner-Ziv main (achievability + converse) の scope-out に伴い、対象だった `WynerZiv{ConverseChain,BinningCovering,CoveringBody,PackingBody,BinningBody}.lean` 系 flat ファイルは削除済。signature 上の load-bearing predicate hypothesis を除去する honesty 強化対象は消滅 (作業自体は当時完遂済、commit 履歴は git)。

**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**: [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md)

## 要点 (将来再利用しうる手順のみ)

- Round 1 が body のみ sorry retreat (signature に load-bearing predicate 残置 = 半 honest) だった状態を、signature からも predicate を除去して tier 2 化する設計。predicate definition は cross-family Relay 保護のため残し、`@audit:retract-candidate(load-bearing-predicate)` 付与のみとする方針 (Option A)。
- 境界判定 (`le_antisymm` 合成 / probability bound) は load-bearing でなく pure forwarder / regularity と判定され、body constructive 復元で proof done に到達しうる、という判断軸だった。
- 全 declaration が signature 改変を伴うため、commit 前に olean refresh (Pattern A) が必須。caller drift は散文 transitive 明示で扱い、即興 vocabulary 禁止 (Pattern C)。
