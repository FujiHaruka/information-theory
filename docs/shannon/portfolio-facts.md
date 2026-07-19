# Portfolio (log-optimal) settled-facts ledger

> family `portfolio` の確定事実の**単一の真実源**。フォーマット規約 → `CLAUDE.md`「Plan / docs hygiene」。
> 再導出が高コストな事実のみ記録。sorry 数 / axiom status / decl 存在は **キャッシュしない**
> (`#print axioms` / `scripts/sig_view.ts --sorry` / `rg` で都度)。
> confidence: `machine` (axiom/sorry 機械検証、再検証コマンド必須) / `loogle-neg` (Found 0、query 併記) /
> `human-judgment` (解析的壁判断、低信頼)。

| claim | confidence | 再検証コマンド | last-verified (commit) | notes |
|---|---|---|---|---|
| 有限和版 `ConcaveOn.sum`（凹関数の有限和は凹）は Mathlib 不在 | loogle-neg | `loogle "ConcaveOn.sum"` → Found 0 | `cea0b16e` | 唯一の Mathlib gap。`Basic.lean` 内で自作 `concaveOn_finset_sum`（`Finset.cons_induction` + base `concaveOn_const` + step `ConcaveOn.add`、~10 行）で充足。Mathlib PR 余地あり |
| portfolio 4 headline すべて proof-done sorryAx-free（`competitive_optimality` / `growthRate_concaveOn` / `logOptimal_of_kuhnTucker` / `kuhnTucker_of_logOptimal`、`Shannon/Portfolio/Basic.lean`） | machine | `#print axioms InformationTheory.Shannon.Portfolio.competitive_optimality`（他 3 も同様）= `[propext, Classical.choice, Quot.sound]` + `lake env lean InformationTheory/Shannon/Portfolio/Basic.lean`（silent） | `cea0b16e` | 独立 honesty-auditor PASS で 4 定理とも `@audit:ok`。壁ゼロで在庫予測どおり着地、撤退ライン不発 |
| forward KT (`kuhnTucker_of_logOptimal`) は price-relative 非負性 `X a i ≥ 0` を要さない | machine | `Basic.lean` の当該証明が `hXnn` を参照しないこと（FDeriv/tangent-cone 論法は X の符号に非依存）。skeleton の `hXnn` は削除済 | `cea0b16e` | honesty-auditor が「theorem-hypothesis 削除は monotone-safe、falseness risk なし」と検証。`competitive_optimality` は skeleton どおり `hXnn`/`hpos` を保持 |
