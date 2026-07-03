# T3-C Broadcast Channel (degraded) Capacity Region ムーンショット計画 🌙

**Status**: CLOSED ✅ — degraded BC capacity region (Cover–Thomas Thm 15.6.2) は **converse + achievability 両側 genuine closure 済**: converse headline `bc_converse` (auxiliary-variable 容量領域 membership、核 `bc_input_singleletterize` / `bc_singleletterize_bound₁`、L-BC2 再開) + achievability headline `bc_achievability` (superposition inner bound、2026-07-03 relay closure) がともに `@audit:ok`・`InformationTheory.lean` 登録済 (子 [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md) / [`bc-achievability-plan.md`](bc-achievability-plan.md)、`#print axioms` sorryAx-free)。achievability の最終ゲート = degradedness superadditivity `bc_degraded_infoJoint_ge` (`bcInfo₁+bcInfo₂ ≤ bcInfoJoint`) を stochastic Markov `U→Y₁→Y₂` 自作 + 既存 DPI `mutualInfo_le_of_markov` で closure (撤退スロット L-BC1/L-BC3 未使用)。一般 (non-degraded) BC + Marton (L-BC5) は scope-out 継続 (textbook-roadmap Ch.15)。
**SoT**: `docs/textbook-roadmap.md` Ch.15 + 子 plan。詳細履歴は git。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-C. Broadcast Channel (degraded) (Cover–Thomas Ch.15.6)」

## 要点 (再利用しうる設計判断)

- **T3-B MAC を verbatim 雛形**として domain/codomain swap + auxiliary RV `U` 圧縮で導出: `BroadcastChannel := Kernel α (β₁ × β₂)`、`BroadcastCode` は encoder un-curry (1 joint) + decoder 2 分離、`InBCCapacityRegion` は 2 inequality bundle (`R₂ ≤ I_u`, `R₁ ≤ I_xy`)。BC は 2 receiver 非対称ゆえ region `swap` は無効 (mono のみ)。
- **撤退ライン L-BC1〜L-BC5** (frozen slug、他 plan が参照): L-BC1 joint typicality multi-receiver body / L-BC2 Fano + chain rule **(再開 → genuine closure 済、子 [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md)、headline `bc_converse`、Route B = entropy-difference / term-by-term degradedness)** / L-BC3 inner bound existence pass-through / L-BC4 outer bound `InBCCapacityRegion` pass-through / L-BC5 一般 (non-degraded) BC + Marton / Körner-Marton は完全 scope-out。
- rate-bound 系の proof done closure は子 plan [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md) 参照。

## Sub-plan 一覧 (backlink — plan_lint 双方向照合点)

| 子 plan | 担当 | 状態 |
|---|---|---|
| [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md) | L-BC2 degraded converse single-letterization (`bc_converse` / `bc_input_singleletterize`、Route B) | CLOSED ✅ (genuine、`@audit:ok`、root 登録済) |
| [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md) | BC rate-bound declaration の defect → genuine signature rewrite | CLOSED ✅ |
| [`bc-achievability-plan.md`](bc-achievability-plan.md) | BC (degraded) achievability = superposition inner bound (`bc_achievability`、Cover–Thomas Thm 15.6.2 達成側) | CLOSED ✅ (genuine、`bc_achievability` `@audit:ok`、`#print axioms` sorryAx-free、root+README Ch.15 登録済) — two-tier superposition random coding (E0 vanishing typicality-LLN + per-receiver Bonferroni + averaged swap + two-tier pigeonhole + ε-selection)、最終ゲート `bc_degraded_infoJoint_ge` (degradedness superadditivity `bcInfo₁+bcInfo₂ ≤ bcInfoJoint`) を stochastic Markov `U→Y₁→Y₂` 自作 + DPI で closure。撤退スロット L-BC1/L-BC3 未使用 |
