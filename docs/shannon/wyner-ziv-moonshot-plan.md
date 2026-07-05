# T3-D Wyner–Ziv lossy distributed coding ムーンショット計画 🌙

**Status**: ACTIVE 🚧 — **operational main attack in progress** (2026-07-05 再開)。Wyner–Ziv main theorem (Cover–Thomas Thm 15.9.1 achievability + converse) の operational code ↔ R_WZ(D) closure を子サブ計画 [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md) で攻める。**feasibility CONFIRMED**: converse gateway atom (heterogeneous Csiszár `csiszar_sum_identity_hetero`) が sorryAx-free で proved (commit `b780f782`、`InformationTheory/Shannon/WynerZiv/ConverseGateway.lean:48`) = converse は pure plumbing 公算大。**情報側 R_WZ(D) は完成済 (`InformationTheory/Shannon/WynerZiv/` 5 file、0 sorry、下記保存 record)**。

> **注記 (roadmap 整合)**: textbook-roadmap Ch.15 の「Wyner–Ziv main scope-out」行は **operational main の closure まで維持** (attack ≠ scope 再開の確定)。roadmap 書換は closure 達成後の別判断。

**SoT**: `docs/textbook-roadmap.md` Ch.15 + 子計画 [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md)。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-D. Wyner–Ziv (Cover–Thomas Ch.15.9)」

## Sub-plan 一覧 (子への backlink、plan_lint 双方向照合対象)

| 子サブ計画 | scope | 状態 |
|---|---|---|
| [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md) | operational main (achievability + converse、Thm 15.9.1) | ACTIVE 🚧 — M0 gateway + P1 proof-done (`fdbae7f9`) + P2 converse scaffold type-check done & audit PASS (`32b69c9f`/`521b5225`、headline hU_card 訂正済) / **残: P2 single-letterization core (~400-700行) + P3 achievability** |
| [`wynerziv-sorry-migration-plan.md`](wynerziv-sorry-migration-plan.md) | 旧 flat file の sorry-based 移行 | (履歴、git 参照) |

## 情報側 完成 record (保存、再利用しうる設計)

- **完成済 live asset**: R_WZ(D) 情報側 (`InformationTheory/Shannon/WynerZiv/` の `Basic` / `FactorizableRate` / `ConditionalEntropyConvexity` / `ObjectiveConvexity` / `RateMonotonicity`、convexity body `wynerZivCondEntDiffConvex_holds` 含む、0 sorry)。converse gateway `ConverseGateway.lean` (`csiszar_sum_identity_hetero`、sorryAx-free) も追加済。
- 採った形: source-coding 系 (`R(D)`) と distributed-coding 系 (Slepian-Wolf) の hybrid。auxiliary alphabet `U` を `Fintype` として引数で受け、cardinality bound (`|U| ≤ |α|+1`、Carathéodory reduction) は別 plan へ分離 (子計画 deferred、slug `wz-auxiliary-cardinality-bound`)。
- converse は Csiszár's sum identity + `R_WZ(D)` 凸性を骨格 (`rate_distortion_converse_n_letter_singleLetter`) クローンで組む (子計画 P2)。**hypothesis pass-through は取らない** — 撤退口は `sorry + @residual(plan:…)` のみ (子計画 撤退ライン)。
- **StandardBorel 訂正 (2026-07-05 実測)**: `condMutualInfo` の `[StandardBorelSpace]` 要求は `[Fintype + MSC]` から `#synth` で **自動 derive** する (旧 record の「自動で出ない → `attribute [local instance]` file 限定発火」は誤り)。明示追加は `[Nonempty]` のみ = local-instance 設計不要 (子計画 型クラス設定)。
