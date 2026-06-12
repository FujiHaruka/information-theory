# EPI Stam wall consolidation — load-bearing predicate 全廃計画

**Status**: CLOSED ✅ — Stam chain の load-bearing predicate を単一 shared wall (`stam_step2_density_wall`) 委任に集約し全廃、Step3Body の孤立 island (predicate 2 + structure + theorem 群) を削除。残壁は後継 `epi-wall-reattack-plan` が density route で解体 (`IsStamCauchySchwarzOptimal` の false-statement defect 是正)。EPI family の実 sorry は route-T 後継で 0。(Stam Step 2: re-scope candidate — see 要点)
**SoT**: `docs/shannon/ch17-inequalities-status.md` + `docs/shannon/epi-facts.md` + `docs/textbook-roadmap.md` Ch.17。詳細履歴は git。

> **Parent**: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md)
> **Sister**: [`epi-stam-to-conclusion-plan.md`](./epi-stam-to-conclusion-plan.md) / [`epi-stam-discharge-plan.md`](./epi-stam-discharge-plan.md)

## 要点

Stam chain の load-bearing predicate (`IsStamTotalExpectation`、h_conv 経由の `IsStamScoreConvolution` load-bearing 化) を全廃し、regularity 前提のみの単一 shared sorry 補題への委任に集約する honesty 是正 (proof-done 前進ではない)。

**集約の理想形 (再開時の構造)**:
```
regularity (P prob / X,Y measurable / IndepFun)
  └─ shared sorry 補題 (regularity → IsStamCauchySchwarzOptimal)
       └─ isStamInequalityHyp_via_body (isStamScoreConvolution_intro …) _  ── genuine arithmetic
            → IsStamInequalityHyp X Y P  ── @audit:ok 可
```

**verbatim 確認済の key findings (再開時の判断材料)**:
- (C1) `h_conv` は dead hypothesis (body 未使用、cosmetic slot)。
- (C2) `IsStamScoreConvolution` は honest discharged (λ-witness 存在、`isStamScoreConvolution_intro` で無条件構成可、not load-bearing)。
- (C3) `IsStamTotalExpectation` は genuine load-bearing (∀λ convex Fisher bound = 証明の核心)。
- (C4) 既に honest 代替経路が `entropy_power_inequality_via_body` に wired 済 (Step3Body chain を通らず regularity → shared wall → arithmetic で `IsStamInequalityHyp` に到達)。
- (C5) Step3Body chain は end-to-end から孤立 island (cross-file consumer 0)。公開主定理は別経路 (`IsStamInequalityResidual` → `entropy_power_inequality_unconditional`)。

**Stam Step 2 re-scope candidate**: convex Fisher bound (Step 2) は **Rioul 2011 §II-C** (score-conditional-mean identity + total variance decomposition) で ~100 行 density-level computation の見積りあり (従来 ~300 行 PR 級より小) → roadmap Ch.17 行 + `ch17-inequalities-status.md`。なお実態は (b) 解析壁ではなく predicate signature drift (`IsStamCauchySchwarzOptimal` が convolution 関係を喪失した tractable な述語 redesign) と後続で再診断済。

撤退ライン (履歴): L-CONS-1 (h_conv が実は使用) / L-CONS-2 (structure hidden consumer → field 置換に縮退) / L-CONS-3 (regularity 上流不足) / L-CONS-4 (sister plan 方針衝突、本計画の shared wall 委任 vs genuine analytic 証明)。
