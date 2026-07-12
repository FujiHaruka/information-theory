# T3-D Wyner–Ziv lossy distributed coding ムーンショット計画 🌙

**Status**: DONE ✅ (Leg 15) — **WZ operational main theorem FULLY CLOSED (achievability + converse、両 headline sorryAx-free + 独立監査 PASS)**。converse (P2) leg 11、achievability (P3) leg 15 で closure。詳細 → 子 [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md) / 孫 [`wz-markov-core-plan.md`](wz-markov-core-plan.md)。
> **WZ main theorem CLOSED** (Cover–Thomas Thm 15.9.1 achievability + converse)。**converse (P2)**: `wyner_ziv_converse` sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`、`@audit:ok`、leg 11、own-sorry ゼロ)。**achievability (P3)**: `wyner_ziv_achievability` sorryAx-free (`@audit:ok`)。E∘BD reduction (top-level `wz_goodCode_exists_of_testChannel`、署名不変 = #9 crux) → S3-S7 + D/(B) 分解 (leg 15-19) → D3 honest 化 (子 Leg 0-E) → C2 covering-acceptance を strong-Ecov build で全閉 (孫 Atom E-F、radius separation `ε_cov=ε/(2(1+C))`、Markov-core chain 5 decl `@audit:ok`、Leg 13) → covering atom `wz_coveringFamily_of_testChannel` を joint-derandomize で閉 (孫 Atom G、r14 `3a31e08c`+`9f5c7afc`) → Atom H docs/wiring (r15、root import + README Ch.15)。C2 chain は当初 weak typicality で FALSE-AS-FRAMED (`1ddc2887`、label-swap 反例) → strong-Ecov で TRUE-as-framed 化。情報側 R_WZ(D) は完成済 (`InformationTheory/Shannon/WynerZiv/` 全 file、0 sorry、下記保存 record)。

> **注記 (roadmap 整合)**: WZ operational main は **closure 達成** (両 headline sorryAx-free、Leg 15)。textbook-roadmap Ch.15 の「Wyner–Ziv main scope-out」行は attack 中の暫定表記なので、closed の反映 (scope-out → CLOSED) が **follow-up タスク**として残る。

**SoT**: `docs/textbook-roadmap.md` Ch.15 + 子計画 [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md)。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-D. Wyner–Ziv (Cover–Thomas Ch.15.9)」

## Sub-plan 一覧 (子への backlink、plan_lint 双方向照合対象)

| 子サブ計画 | scope | 状態 |
|---|---|---|
| [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md) | operational main (achievability + converse、Thm 15.9.1)。goal object = **reshape 後 `wynerZivRate`** (全有限補助 alphabet 上 inf) | DONE ✅ — **operational main FULLY CLOSED**: converse `wyner_ziv_converse` (leg 11、sorryAx-free、`@audit:ok`) + achievability `wyner_ziv_achievability` (leg 15、sorryAx-free、`@audit:ok`) 両 headline + 独立監査 PASS。P2 = single-letterisation core (leg 4-11、route C support-reduction `wz_support_reduce`)、P3 = E∘BD → S3-S7/D/(B) 分解 → strong-Ecov Markov-core chain 5 decl (孫 Atom E-F、Leg 13) → covering atom joint-derandomize (孫 Atom G、r14) → Atom H docs/wiring (r15、root import + README Ch.15)。詳細 → 子 plan。 |
| [`wynerziv-sorry-migration-plan.md`](wynerziv-sorry-migration-plan.md) | 旧 flat file の sorry-based 移行 | (履歴、git 参照) |

## 情報側 完成 record (保存、再利用しうる設計)

- **完成済 live asset**: R_WZ(D) 情報側 (`InformationTheory/Shannon/WynerZiv/` の `Basic` / `FactorizableRate` / `ConditionalEntropyConvexity` / `ObjectiveConvexity` / `RateMonotonicity`、convexity body `wynerZivCondEntDiffConvex_holds` 含む、0 sorry)。converse gateway `ConverseGateway.lean` (`csiszar_sum_identity_hetero`、sorryAx-free) も追加済。
- 採った形: source-coding 系 (`R(D)`) と distributed-coding 系 (Slepian-Wolf) の hybrid。情報側 rate は固定-`U` の `wynerZivRateFactorizable U` を持つ。**reshape (`4532bd48`)**: operational headline は代わりに `wynerZivRate` (全有限補助 alphabet `Fin k` 上 inf、union-of-images `sInf`、`FactorizableRate.lean:636`) を目標にする — 固定-`U` は小さい `U` で false-as-framed だったが inf-over-all で source から解消。Carathéodory support-reduction (`wynerZivRate = wynerZivRateFactorizable (Fin (|α|+3))` = L1 `wynerZivRate_eq_factorizable_finK` + core `wz_support_reduce`) は endpoint route の critical path 上だったが **leg 11 で FULLY CLOSED sorry-free** (route C、K=`|α|+3`、bare ambient Carathéodory + entropy-mixture identity gateway `wzKernelObjective_eq_blockSum`)。
- converse は `R_WZ(D)` 凸性 + 骨格 (`rate_distortion_converse_n_letter_singleLetter`) クローンで組み、reshape 後は large auxiliary を `wynerZivRate_le_of_feasible` で feasible 点に着地 (子計画 P2)。**operational converse `wyner_ziv_converse` は leg 11 で sorryAx-free (`#print axioms` = `[propext, Classical.choice, Quot.sound]`、独立監査 `@audit:ok`)** = converse own-sorry ゼロ。single-letterisation witness `wz_converse_perletter_witness` (真ルート `Uᵢ=(J,Y_{\i})` + conditional-MI chain、真 gateway = `iIndepFun → Markov Uᵢ−Xᵢ−Yᵢ`) は leg 8、endpoint L1/L2/L3 は leg 9-10、最後の kernel support-reduction core `wz_support_reduce` は leg 11 で CLOSED。Csiszár `csiszar_sum_identity_hetero` は本ルート orphaned (sorryAx-free 維持、削除せず、wall ではない)。broadcast-channel `bc_input_singleletterize` テンプレは不採用。**hypothesis pass-through は取らない** — 撤退口は `sorry + @residual(plan:…)` のみ (子計画 撤退ライン)。
- **StandardBorel 訂正 (2026-07-05 実測)**: `condMutualInfo` の `[StandardBorelSpace]` 要求は `[Fintype + MSC]` から `#synth` で **自動 derive** する (旧 record の「自動で出ない → `attribute [local instance]` file 限定発火」は誤り)。明示追加は `[Nonempty]` のみ = local-instance 設計不要 (子計画 型クラス設定)。
