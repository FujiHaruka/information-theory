# Shannon: WynerZiv — tier 5 defect 3 件 discharge plan

**Status**: CLOSED ✅ — 対象だった 3 件の tier 5 defect (`wyner_ziv_achievability_rate` / `wyner_ziv_achievability_existence` / `wyner_ziv_converse_rate`) は Wyner-Ziv main の scope-out に伴い `WynerZiv{Achievability,Converse}.lean` ごと削除済。signature rewrite で tier 2 化する対象は消滅。

**SoT**: `docs/textbook-roadmap.md` Ch.15。詳細履歴は git。

> **Parent**: [`wyner-ziv-moonshot-plan.md`](wyner-ziv-moonshot-plan.md) (statement-level publish 完了済の後追い)

## 要点 (将来再利用しうる手順のみ)

- BM Wave 6 と同型の sweep 設計: 既存 signature が precondition 不在 / hypothesis ≡ conclusion で defect の場合、consumer 0 件を確認した上で linkage hypothesis (regularity 形) を signature に追加し、body `sorry` + 既存 plan slug の `@residual` で tier 2 化する。
- 案比較の判断軸: (a) signature rewrite (採用) / (b) retract-candidate 化 (publish 必須の wrapper には不適) / (c) tag 書換のみ (false-statement には意味的に不可、stale circular tag には可)。
- linkage hyp が conclusion-as-hypothesis でないこと (`R > R_WZ` から `R_WZ ≤ R` を `le_of_lt` で lift する形は型が厳密に異なる constructive bridge) を inline で確認する。`<` から `≤` の lift が trivial なら proof done 候補。
