# T3-C Broadcast Channel (degraded) Capacity Region ムーンショット計画 🌙

**Status**: degraded ✅ CLOSED / 一般 BC (Marton inner bound) ✅ CLOSED — degraded BC capacity region (Cover–Thomas Thm 15.6.2) は **converse + achievability 両側 genuine closure 済**: converse headline `bc_converse` (auxiliary-variable 容量領域 membership、核 `bc_input_singleletterize` / `bc_singleletterize_bound₁`、L-BC2 再開) + achievability headline `bc_achievability` (superposition inner bound、2026-07-03 relay closure) がともに `@audit:ok`・`InformationTheory.lean` 登録済 (子 [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md) / [`bc-achievability-plan.md`](bc-achievability-plan.md)、`#print axioms` sorryAx-free)。achievability の最終ゲート = degradedness superadditivity `bc_degraded_infoJoint_ge` (`bcInfo₁+bcInfo₂ ≤ bcInfoJoint`) を stochastic Markov `U→Y₁→Y₂` 自作 + 既存 DPI `mutualInfo_le_of_markov` で closure (撤退スロット L-BC1/L-BC3 未使用)。**L-BC5 (一般 BC + Marton) はユーザー指示で解除** → 子 [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) で追跡し、**Phase 0–8 完了 = headline `marton_achievability` (EGK Thm 8.3、private message のみ) が proof-done**。bookkeeping (README 定理表 / proof-log / WZ 再配線) まで消化して子 plan は CLOSED、生きた撤退ラインは 0。Körner–Marton は scope-out 継続 (textbook-roadmap Ch.15)。**一般 BC の外界フレームは進行中** (下記「後続」)。
**SoT**: `docs/textbook-roadmap.md` Ch.15 + 子 plan。詳細履歴は git。

**後続 (進行中)**: 一般 BC の足場は子 [`bc-general-region-plan.md`](bc-general-region-plan.md) で
Phase 1 (操作的容量領域 = 主語) / Phase 3 (協調外界) / Phase 4a (UV 単一文字化、floating 形) まで
到達し、挟み込み `martonRegion ⊆ bcCapacityRegion ⊆ bcOuterRegionCoop` が成立。本線は **Phase 4b
(UV 外界の集合化 + 操作的包含 `bcCapacityRegion ⊆ bcOuterRegionUV`)** で、符号から ambient 測度を
構成する橋 (MAC の `TimeSharingConverse/Bridge.lean` + `Assembly.lean` 相当) が要る。**M0 在庫が完了**
([`bc-uv-operational-inventory.md`](bc-uv-operational-inventory.md)) し、実装は 8 step (S1–S8、≈ 1370 行、
Mathlib 側の穴ゼロ) に分解済。一般 BC 容量領域の特徴づけ自体は未解決問題なので、内外一致は計画の Phase 外。

> **Parent**:
> - [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 3 — T3-C. Broadcast Channel (degraded) (Cover–Thomas Ch.15.6)」

## 要点 (再利用しうる設計判断)

- **T3-B MAC を verbatim 雛形**として domain/codomain swap + auxiliary RV `U` 圧縮で導出: `BroadcastChannel := Kernel α (β₁ × β₂)`、`BroadcastCode` は encoder un-curry (1 joint) + decoder 2 分離、`InBCCapacityRegion` は 2 inequality bundle (`R₂ ≤ I_u`, `R₁ ≤ I_xy`)。BC は 2 receiver 非対称ゆえ region `swap` は無効 (mono のみ)。
- **撤退ライン L-BC1〜L-BC5** (frozen slug、他 plan が参照): L-BC1 joint typicality multi-receiver body / L-BC2 Fano + chain rule **(再開 → genuine closure 済、子 [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md)、headline `bc_converse`、Route B = entropy-difference / term-by-term degradedness)** / L-BC3 inner bound existence pass-through / L-BC4 outer bound `InBCCapacityRegion` pass-through / L-BC5 一般 (non-degraded) BC + Marton / Körner-Marton は完全 scope-out **(Marton 部分は解除・達成 → 子 [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) の headline `marton_achievability`。Körner–Marton は scope-out 継続)**。
- rate-bound 系の proof done closure は子 plan [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md) 参照。

## Sub-plan 一覧 (backlink — plan_lint 双方向照合点)

| 子 plan | 担当 | 状態 |
|---|---|---|
| [`bc-degraded-converse-plan.md`](bc-degraded-converse-plan.md) | L-BC2 degraded converse single-letterization (`bc_converse` / `bc_input_singleletterize`、Route B) | CLOSED ✅ (genuine、`@audit:ok`、root 登録済) |
| [`broadcast-channel-signature-rewrite-plan.md`](broadcast-channel-signature-rewrite-plan.md) | BC rate-bound declaration の defect → genuine signature rewrite | CLOSED ✅ |
| [`bc-achievability-plan.md`](bc-achievability-plan.md) | BC (degraded) achievability = superposition inner bound (`bc_achievability`、Cover–Thomas Thm 15.6.2 達成側) | CLOSED ✅ (genuine、`bc_achievability` `@audit:ok`、`#print axioms` sorryAx-free、root+README Ch.15 登録済) — two-tier superposition random coding (E0 vanishing typicality-LLN + per-receiver Bonferroni + averaged swap + two-tier pigeonhole + ε-selection)、最終ゲート `bc_degraded_infoJoint_ge` (degradedness superadditivity `bcInfo₁+bcInfo₂ ≤ bcInfoJoint`) を stochastic Markov `U→Y₁→Y₂` 自作 + DPI で closure。撤退スロット L-BC1/L-BC3 未使用 |
| [`bc-general-region-plan.md`](bc-general-region-plan.md) | 一般 BC 容量領域フレーム (操作的容量領域の定義 → 協調外界 → UV outer bound → 一致クラス拡張) | 進行中 🚧 — Phase 1 ✅ (`BCAchievable` / `bcCapacityRegion` / `marton_region_subset_capacity`) / Phase 3 ✅ (`bcOuterRegionCoop` / `bc_capacity_subset_coop`、Wolfowitz strong converse の対偶で ambient 構成を迂回) / Phase 4a ✅ (`bc_uv_converse` = Nair–El Gamal 単一文字化 4 本の floating 形 headline、**degradedness 前提なし**、核は新規自作 `csiszar_sum_identity_cond`)。**本線 = Phase 4b 🚧** (集合化 + 操作的包含、符号→ambient 橋 + 単一文字還元)。**M0 在庫 ✅** ([`bc-uv-operational-inventory.md`](bc-uv-operational-inventory.md)) — 実装は S1–S8 の 8 step (≈ 1370 行 = MAC 実績 2191 行の 6 割強、Mathlib 側の穴ゼロ = `@residual(wall:…)` 候補なし)、設計 2 件は決着 (単一文字還元 = 案 A 補助変数吸収 / 結合 memoryless = 構成側、`OuterBoundUV.lean` の署名は無改変)。Phase 2 は park 可、Phase 5 のクラス定義は 4b と独立。撤退 L-BCO1 不発動 / L-BCO2/3 据置 / **L-BCO4 不発動見込み** / **L-BCO5・L-BCO6 新設** (補助変数の型統一 / 退化レート被覆) |
| [`marton-inner-bound-plan.md`](marton-inner-bound-plan.md) | L-BC5 解除 = 一般 (non-degraded) BC の Marton inner bound (EGK Thm 8.3、private message のみ) | CLOSED ✅ (**Phase 0–8 完了**) — `marton_achievability` (`Marton/Achievability.lean`、`@[entry_point]` + `@audit:ok`、`#print axioms` sorryAx-free、root+README Ch.15 登録済) が厳密不等号 3 本 `R₁<I(V₁;Y₁)` / `R₂<I(V₂;Y₂)` / `R₁+R₂<I(V₁;Y₁)+I(V₂;Y₂)−I(V₁;V₂)` の達成可能性を無条件に与える (入力は一般カーネル `K : Kernel (V₁×V₂) α` 形。決定的 `x=f(v₁,v₂)` 版は full support 前提と両立せず直接の系にはならない)。機構: 抽象 second-moment 核 + 共分散の鋭化 (sum-rate 制約の要) + Fourier–Motzkin + mutual covering の weak/strong 両版 + 受信機ごとに分岐する 3 本入れ子の半径 + 3 段アンサンブルを 2 段 pigeonhole へ再結合。生きた撤退ラインは 0。Phase 8 bookkeeping (README 定理表 / [proof-log](../proof-logs/proof-log-marton-inner-bound.md) / WZ `Concentration.lean` を `Shannon/ConditionalAEP.lean` へ再配線) まで消化済 |
