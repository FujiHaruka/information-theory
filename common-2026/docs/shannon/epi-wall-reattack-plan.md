# EPI 残り 2 壁 re-attack — gateway atom 起点の本気攻略 サブ計画

**Status**: CLOSED ✅ — 壁1 (stam-step2-density) は density route で完成 (`@audit:ok`)、壁2 (per-time de Bruijn) は NO-GO 真壁確定で後継 `epi-debruijn-pertime-closure` に移管。積分形 `debruijnIntegrationIdentity_holds` は構造的 closure。`plan:epi-wall-reattack-plan` slug は `EPI/Stam/DeBruijnConclusion.lean` に、`wall:debruijn-integration` slug は `FisherInfo/V2DeBruijn.lean` になお生存。
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-moonshot-plan.md`](epi-moonshot-plan.md)
> **関連 sub-plans**: [`epi-stam-discharge-plan.md`](epi-stam-discharge-plan.md) / [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) / [`epi-stam-fisher-epi-integrated-sweep-plan.md`](epi-stam-fisher-epi-integrated-sweep-plan.md) / [`epi-debruijn-pertime-closure-plan.md`](epi-debruijn-pertime-closure-plan.md)

## 要点

2 壁を gateway atom 起点で攻略した。

- **壁1 (EPI density route) = 完成**: 当初「Blachman = ~300 行 PR 級真壁 (condExp disintegration)」診断を density route が概念ごと解体。鍵 = `fisherInfoOfMeasureV2 _μ f = fisherInfoOfDensity f` (`rfl`、measure 引数を捨てる) で goal が純密度上の解析命題に collapse → condExp/condDistrib/disintegration 一切不要、確率重み上の点ごと明示 Bochner ∫ だけで closure。capstone `convex_fisher_bound_gaussian_via_density_route` + Gaussian witness `isBlachmanConvReady_gaussianPDFReal` (19 field genuine) で非vacuousness 機械確証。**教訓**: 「Mathlib 壁」判定は別ルート (density pivot) で再確認してから受け入れる。gateway GO は Phase 3 GO を意味しない。

- **壁2 (per-time de Bruijn `debruijnIdentityV2_holds`) = NO-GO 真壁 parked**: 壁1 を解体した rfl pivot は壁2 に効かない (`differentialEntropy μ` が `μ.rnDeriv volume` 経由で measure 本体に依存し density に collapse しない)。heat/Fokker/semigroup/PDE 全 loogle ヒットなし。`wall:debruijn-integration` (code 生存) が正しい honest state、closure は後継 `epi-debruijn-pertime-closure` (density-route 自作で迂回) に移管。

- **積分形 `debruijnIntegrationIdentity_holds` = 構造的 closure**: FTC reduction + per-time 壁各点呼出、新 `structure IsDeBruijnPathRegular` precondition、transitive `wall:debruijn-integration` 委任。

凍結 retreat-line slug (外部参照あり、保持): L-EPIW-1〜4 系 (gateway 微分可能性 / cross-term measurability / Blachman 真壁 / score 可積分性 / 3-pre adapter / 3d-3e atom / per-time 真壁・積分形 FTC)。完了 Phase の retreat line は発火せず (歴史)。
