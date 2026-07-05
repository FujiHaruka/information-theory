# T3-D Wyner–Ziv lossy distributed coding ムーンショット計画 🌙

**Status**: ACTIVE 🚧 — **operational main attack in progress**。Wyner–Ziv main theorem (Cover–Thomas Thm 15.9.1 achievability + converse) の operational code ↔ R_WZ(D) closure を子サブ計画 [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md) で攻める。**converse single-letterisation core (witness `wz_converse_perletter_witness`、sub2/sub3 含む) CLOSED (leg 8、sorryAx-free + 独立監査 PASS)**。残 converse own-sorry は **1 本 = 左端点右連続 `wynerZivRate_le_of_forall_pos_add_endpoint` (`Converse.lean:1773`、Carathéodory route L1/L2/L3、slug `wz-auxiliary-cardinality-bound`)**。**Goal の残り半分 = achievability P3 (binning+covering、未着手)**。次 leg 群は endpoint L1 か P3 を選ぶ。真ルートは `Uᵢ=(J,Y_{\i})` + conditional-MI chain (Csiszár `csiszar_sum_identity_hetero` は本ルート orphaned、真 gateway = `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ`、子計画 判断ログ #2)。**情報側 R_WZ(D) は完成済 (`InformationTheory/Shannon/WynerZiv/` 5 file、0 sorry、下記保存 record)**。

> **注記 (roadmap 整合)**: textbook-roadmap Ch.15 の「Wyner–Ziv main scope-out」行は **operational main の closure まで維持** (attack ≠ scope 再開の確定)。roadmap 書換は closure 達成後の別判断。

**SoT**: `docs/textbook-roadmap.md` Ch.15 + 子計画 [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md)。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-D. Wyner–Ziv (Cover–Thomas Ch.15.9)」

## Sub-plan 一覧 (子への backlink、plan_lint 双方向照合対象)

| 子サブ計画 | scope | 状態 |
|---|---|---|
| [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md) | operational main (achievability + converse、Thm 15.9.1)。goal object = **reshape 後 `wynerZivRate`** (全有限補助 alphabet 上 inf) | ACTIVE 🚧 — M0 gateway + P1 proof-done (`fdbae7f9`) + **P2 converse single-letterisation core CLOSED (leg 8)**: DPI 非負 / time-sharing 基盤 (`wzRateValueSet_timeShare_mem`+`_avg_mem`+`_weightedSum_mem`+`wynerZivRate_convex_in_D`) / headline body / feasible-point landing `wz_converse_feasible_point` / **witness `wz_converse_perletter_witness` の 5 sub-lemma 全** (sub2 `95f4abc5`/`321abbc6`、sub3+atom `wz_inputs_cond_indep` `72a9077e`/`021d7732`、gateway `wz_perletter_markov` `4eb1a788`) すべて sorryAx-free + 独立監査 PASS。**残: P2 own-sorry 1 本 (左端点右連続 `wynerZivRate_le_of_forall_pos_add_endpoint` [`Converse.lean:1773`、Carathéodory L1/L2/L3、slug `wz-auxiliary-cardinality-bound`]) + P3 achievability (未着手、Goal の残り半分)** |
| [`wynerziv-sorry-migration-plan.md`](wynerziv-sorry-migration-plan.md) | 旧 flat file の sorry-based 移行 | (履歴、git 参照) |

## 情報側 完成 record (保存、再利用しうる設計)

- **完成済 live asset**: R_WZ(D) 情報側 (`InformationTheory/Shannon/WynerZiv/` の `Basic` / `FactorizableRate` / `ConditionalEntropyConvexity` / `ObjectiveConvexity` / `RateMonotonicity`、convexity body `wynerZivCondEntDiffConvex_holds` 含む、0 sorry)。converse gateway `ConverseGateway.lean` (`csiszar_sum_identity_hetero`、sorryAx-free) も追加済。
- 採った形: source-coding 系 (`R(D)`) と distributed-coding 系 (Slepian-Wolf) の hybrid。情報側 rate は固定-`U` の `wynerZivRateFactorizable U` を持つ。**reshape (`4532bd48`)**: operational headline は代わりに `wynerZivRate` (全有限補助 alphabet `Fin k` 上 inf、union-of-images `sInf`、`FactorizableRate.lean:636`) を目標にする — 固定-`U` は小さい `U` で false-as-framed だったが inf-over-all で source から解消。Carathéodory reduction (`wynerZivRate = wynerZivRateFactorizable (Fin (|α|+1))`) は critical path から外れた cosmetic equivalence (slug `wz-auxiliary-cardinality-bound`、現時点 file 不要)。
- converse は `R_WZ(D)` 凸性 + 骨格 (`rate_distortion_converse_n_letter_singleLetter`) クローンで組み、reshape 後は large auxiliary を `wynerZivRate_le_of_feasible` で feasible 点に着地 (子計画 P2)。**single-letterisation witness `wz_converse_perletter_witness` (真ルート `Uᵢ=(J,Y_{\i})` + conditional-MI chain、真 gateway = `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ`) は leg 8 で CLOSED** (sub2/sub3/gateway、sorryAx-free + 独立監査 PASS)。Csiszár `csiszar_sum_identity_hetero` は本ルート orphaned (sorryAx-free 維持、削除せず、wall ではない)。broadcast-channel `bc_input_singleletterize` テンプレは不採用。**hypothesis pass-through は取らない** — 撤退口は `sorry + @residual(plan:…)` のみ (子計画 撤退ライン)。
- **StandardBorel 訂正 (2026-07-05 実測)**: `condMutualInfo` の `[StandardBorelSpace]` 要求は `[Fintype + MSC]` から `#synth` で **自動 derive** する (旧 record の「自動で出ない → `attribute [local instance]` file 限定発火」は誤り)。明示追加は `[Nonempty]` のみ = local-instance 設計不要 (子計画 型クラス設定)。
