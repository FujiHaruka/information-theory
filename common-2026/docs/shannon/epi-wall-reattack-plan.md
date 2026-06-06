# EPI 残り 2 壁 re-attack — gateway atom 起点の本気攻略 サブ計画

> **Parent**: [`epi-moonshot-plan.md`](epi-moonshot-plan.md) (Ch.17 一般 EPI)
> **関連 sub-plans**: [`epi-stam-discharge-plan.md`](epi-stam-discharge-plan.md) / [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) / [`epi-stam-fisher-epi-integrated-sweep-plan.md`](epi-stam-fisher-epi-integrated-sweep-plan.md) / [`epi-debruijn-pertime-closure-plan.md`](epi-debruijn-pertime-closure-plan.md) (壁2 後継)
> **Inventory**: [`epi-wall-reattack-inventory.md`](epi-wall-reattack-inventory.md)
> **Created**: 2026-05-30 (Wave 1 独立再評価)

## 状態サマリ

2 壁 (壁1 stam-step2-density / 壁2 debruijn-integration) を gateway atom 起点で攻略。**壁1 = density
route で完成、壁2 = NO-GO 真壁確定で parked**。

- **壁1 (EPI density route) = 完成 ✅** (Phase 0-3e 全 `@audit:ok` sorryAx-free)。当初「Blachman = ~300 行
  PR 級真壁」診断を density route が概念ごと解体 (判断ログ A)。capstone `convex_fisher_bound_gaussian_via_density_route`
  + Gaussian witness `isBlachmanConvReady_gaussianPDFReal` (19 field genuine) で非vacuousness 機械確証済。
- **壁2 (per-time de Bruijn `debruijnIdentityV2_holds`) = NO-GO 真壁 parked** (Phase 4、L-EPIW-4-α)。
  `differentialEntropy μ := ∫ negMulLog(μ.rnDeriv volume)` が measure 本体依存で density-collapse 不可
  (壁1 を解体した rfl pivot が効かない)、heat/Fokker/semigroup/PDE 全 loogle Found 0。`sorry` +
  `@residual(wall:debruijn-integration)` 据置が正しい honest state。closure は後継 plan
  `epi-debruijn-pertime-closure` (density-route 自作で迂回) に移管。
- **積分形 `debruijnIntegrationIdentity_holds` = 構造的 closure ✅** (FTC reduction + per-time 壁各点呼出、
  新 `structure IsDeBruijnPathRegular` precondition、local 0 sorry / transitive `wall:debruijn-integration`)。

## 進捗 (Phase 別、完了済 anchor)

- [x] Phase 0 — 在庫確定 + 壁 signature verbatim 照合 ✅
- [x] Phase 1 — gateway atom `convDensity_add_differentiable` = GATE GO ✅ (`@audit:ok`)
- [x] Phase 2 — cross-term orthogonality `score_cross_term_eq_zero` ✅ (gateway 非依存、`@audit:ok`)
- [x] Phase 3-pre — 3+1 述語 signature pivot ✅ (軸1 `hconv` + `IsRegularDensityV2` + `∫=1` 注入、軸2 廃止、false-statement defect 除去、4 述語 `@audit:ok`)
- [x] Phase 3a — `convDensityAdd_hasDerivAt_of_regular` (`EPIConvDensity.lean:186`) genuine ✅
- [x] Phase 3b — S2 `symm_deriv_integral_eq` + S3 `score_conv_eq_weighted_integral` (Blachman score 表現、condExp 不使用) ✅ (新 file `EPIBlachmanDensity.lean`)
- [x] Phase 3c — atom A + S4 `score_sq_le_weighted_integral` (Jensen) + `convex_fisher_bound` genuine ✅
- [x] Phase 3d — assemble `stam_step2_density_wall` genuine ✅ (案 b' = `IsBlachmanConvReady` bundle + `convex_fisher_bound_of_ready`、`IsStamCauchySchwarzOptimal` が SOUND と確定)
- [x] Phase 3e — Gaussian witness `IsBlachmanConvReady (gaussian)(gaussian)` proven inhabitant ✅ (新 file `EPIBlachmanGaussianWitness.lean`)
- [x] 2 honest sorry 完済 ✅: `isBlachmanConvReady_symm` (reflection transport) + `isStamInequalityHyp_via_body` (owner-level pivot、`=ᵐ`→pointwise 強化 + `IsBlachmanConvReady` bundle、8-file ripple)
- [~] Phase 4 — 壁2 = NO-GO 真壁 parked (上記)。積分形 closure ✅。

### 残 active (低優先)

- [ ] **predicate-level Gaussian wiring** — ほぼ moot。pivot 監査が Gaussian 経路は `IsStamInequalityHyp` を
  witness 構築せず `entropyPower_gaussian_additivity` 直通と確認、非vacuousness も witness で確証済。
- [ ] **F prep** (`_hX/_hZ/_hXZ` signature 復元) = caller 都合で見送り (caller `csiszarGap1Source_hasDerivAt`
  が `IsDeBruijnRegularityHyp` bundle しか持たない)。per-time 壁 closure 着手時に caller 側で設計要。
- [ ] **`IsIBPHypothesis`** (`FisherInfoV2DeBruijnBody.lean:199`) = tier-4 name-laundering retract-candidate
  (load-bearing でない、consumer `_h_ibp` unused 化済)。当該 file touch 時に incidental 削除候補。

## wall slug 状態

- `wall:stam-step2-density` = 壁1 の canonical slug (audit-tags.md register 登録済)。コード現状は
  `wall:stam-blachman` (register 未登録) — **当該 file touch 時に slug 统一是正** (判断ログ B)。ただし壁1 は
  density route で closure 済のため、残コード `@residual` は successor 経由で解消されうる。
- `wall:debruijn-integration` = 壁2 (per-time、parked、successor = epi-debruijn-pertime-closure)。
- `wall:stam-pdf-identification` = 軸2 measure-keyed 述語の `HasDensityReal` marker (Phase 3-pre、軸2 廃止で moot)。

## 凍結 retreat-line slug index

外部参照あり (`textbook-roadmap.md` / `epi-blachman-density-route-inventory.md` /
`epi-3predicate-pivot-scoping.md`) ゆえ slug 名を保持。完了 Phase の retreat line は発火せず (歴史)。

| slug | Phase | 役割 (発火条件) |
|---|---|---|
| L-EPIW-1-α, L-EPIW-1-β | 1 | gateway `⋆ₗ` 微分可能性が組めない / Gaussian-tail dominated 充足超過 (不発、GATE GO) |
| L-EPIW-2-α | 2 | `IndepFun.comp` の score 合成 measurability 詰まり (不発) |
| L-EPIW-3-α, L-EPIW-3-β | 3 | Blachman 真壁確定 → honest sorry 据置 (density route で解体、不発) |
| L-EPIW-3-密度-α, L-EPIW-3-密度-β | 3 | score 可積分性 signature 漏れ / precondition gap (案 b で解消) |
| L-EPIW-3pre-α, L-EPIW-3pre-β | 3-pre | 隠れ construct site 出現時の adapter / defeq 破れ |
| L-EPIW-3d-α, L-EPIW-3d-β, L-EPIW-3d-γ | 3d | atom Cong deriv-ae / atom Pos / atom Bdd-f 詰まり |
| L-EPIW-3e-α, L-EPIW-3e-β, L-EPIW-3e-γ, L-EPIW-3e-δ | 3e | linchpin a.e.→pointwise / shear 組立 / private 解消副作用 / sup 自作 |
| L-EPIW-4-α, L-EPIW-4-β | 4 | per-time 真壁確定 (発火、parked) / 積分形 FTC 詰まり (不発、closure 済) |

## honesty 規律

詰まれば `sorry` + `@residual(<class>:<slug>)` (tier 2)。**禁止** (tier 5): `*Hypothesis`/`Is...Hyp`
predicate に核を bundle / `Prop := True` slot / 循環 `:= h` / 退化定義悪用。regularity hyp
(measurability / independence / `IsProbabilityMeasure` / Gaussian tail dominated) は precondition なので保持 OK。
新規 `sorry`+`@residual` commit が出たら orchestrator が独立 honesty audit 起動。

## 判断ログ (key lessons のみ)

決着済 entry (Wave 1 共通根 / Phase 3-pre 設計 / 3c-fin / 3d / 3e の実装経緯) は削除 (git 履歴 + コード SoT)。

- **A. density route が「PR 級真壁」を解体** (2026-05-30): 当初 proof-pivot-advisor が壁1 を「~300 行
  PR 級 unscoped wall (condExp disintegration)」と真壁確定したが、これは**抽象 condExp 経路限定の過大判定**。
  `fisherInfoOfMeasureV2 _μ f = fisherInfoOfDensity f` (`rfl`、measure 引数を捨てる) により goal が純密度上の
  解析命題に collapse → condExp/condDistrib/disintegration **一切不要**、確率重み上の点ごと明示積分 (Blachman
  を明示 Bochner ∫ だけで建てる) で density route closure。**教訓**: 「Mathlib 壁」判定は別ルート (density
  pivot) で再確認してから受け入れる (CLAUDE.md「Mathlib 壁判定は独立 pivot」の実例)。「gateway が score の
  解析的 (logDeriv) 表現まで建つ」と「Blachman closure 可能」は別物 — gateway GO は Phase 3 GO を意味しない。
- **B. 壁2 は density-collapse 不可で真壁** (2026-05-31, proof-pivot-advisor): 壁1 を解体した rfl pivot
  (`fisherInfoOfMeasureV2 = fisherInfoOfDensity`) は壁2 に効かない — `differentialEntropy μ` が
  `μ.rnDeriv volume` 経由で measure 本体に依存し density に collapse しないため。heat/Fokker/semigroup/PDE
  全 loogle Found 0。NO-GO 真壁確定、successor plan で density-route 自作迂回。
