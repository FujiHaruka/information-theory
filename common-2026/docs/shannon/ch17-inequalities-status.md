# Ch.17 Inequalities — ステータス (textbook-roadmap から分離)

> `docs/textbook-roadmap.md` の Ch.17 行が肥大化したため分離 (2026-06-01)。
> roadmap 側は 1 行サマリ + 本ファイルへのポインタのみ。Ch.17 の詳細状態はここが SoT。
> コード内の `@audit:*` / `@residual` タグが最終 SoT であることは不変 (`docs/audit/audit-tags.md`)。

## 現状サマリ (1 行)

**一般 EPI headline (`entropy_power_inequality`) を除き Ch.17 は publishable。** 残る唯一の frontier は
一般 EPI の genuine closure で、本セッション (2026-06-01) に A-5 頂点の caller 供給 precondition 4 種
すべてに genuine producer が揃った。残るは A-5 配線 + 上流の Stam→結論壁。

## proof-done (genuine, sorryAx-free)

- Han / HanD / Shearer / LoomisWhitney / BrascampLieb / Polymatroid / Pinsker (+sharp) / Hypercube /
  StamGaussianBound / HeatFlowPath ✅
- Stam Step 1 honest discharge ✅
- `entropyPower_gaussian_additivity` + `entropyPower_pos/nonneg/gaussianReal` 等 (Gaussian EPI =
  variance additivity) ✅
- CT 17.9 Minkowski determinant: Gaussian additivity から導出可能 (新規 ✅ promote 候補)

## frontier = 一般 EPI headline closure のみ

headline `entropy_power_inequality` (`EntropyPowerInequality.lean:287`) は **proof done ではない**
(transitive wall 経由で sorryAx 依存)。一般 EPI / log・exp form / `epi_via_stam_main` 等 12 件の
`@audit:ok` は 2026-05-30 の `#print axioms` sweep で誤付与と判明し降格済 (genuine sorryAx-free は
Gaussian additivity 系のみ)。

### active な独立壁 (slug census は stale 重複・supersede を含むので注意)

| slug | 性質 | 状態 |
|---|---|---|
| `plan:epi-stam-to-conclusion-plan` / `-phaseA-plan` | Stam→結論本線 (joint independence / continuity / rescale) | 本線、一部 owner 別 |
| `wall:debruijn-integration` / `plan:epi-debruijn-pertime-closure` | per-time de Bruijn | session 8 で大半 genuine closed、census は stale |
| `wall:fisher-finiteness` | conv の Fisher 有限性 | conv-with-Gaussian 分は `gaussianConv_fisher_le_inv_var` で閉鎖 |
| `wall:stam-blachman` | score の**確率的 (condExp) 表現** = Blachman 恒等式 | **最深・未確定** (下記) |
| `wall:csiszar` | Csiszár ratio monotonicity | session 10 で R-3 等 genuine (`@audit:ok`) |

### 最新進捗 (2026-06-01, session 11) — A-5 producer 層 landing

EPI A-5 頂点 `isStamToEPIScalingHyp_of_stam_debruijn` (`EPIStamToBridge.lean:1287`) の `h_pos_stam`
バンドルが要求する 4 種 path-density precondition を、`convDensityAdd pX g_t` 形に対し genuine 生成する
producer を全て実装 (全 0-sorry / sorryAx-free / 独立監査 `@audit:ok`)。新規 file 5 本:

| precondition | producer (file) | 結果 |
|---|---|---|
| 共通基盤 gateway | `EPIConvDensityGaussianGateway.lean` | `convDensityAdd_*_of_integrable_smoothKernel` (fX を Integrable のみに弱化) |
| (1) `IsRegularDensityV2` | `EPIConvDensityRegular.lean` | `isRegularDensityV2_convDensityAdd_gaussian` 6 field 全 genuine (tail も DCT で閉鎖) |
| (2) `∫ = 1` | `EPIConvDensityNormalization.lean` | `integral_convDensityAdd_gaussian_eq_one` (Mathlib `integral_convolution`) |
| (3) assoc / interchange | `EPIConvDensityAssoc.lean` | `convDensityAdd_assoc` + bridge `(pX∗g_t)∗(pY∗g_t)=(pX∗pY)∗g_{2t}` (10 補題) |
| (4) `IsBlachmanConvReady` | `EPIBlachmanGeneralDensity.lean` | `isBlachmanConvReady_convDensityAdd_gaussian` **19/19 field genuine** (int_fisherZ は (3) bridge で variance-2t に lift し閉鎖) |

inventory `epi-blachman-general-density-inventory.md` の ~700-1100 行見積 producer 層が全 landing、
真の Mathlib 壁 0 件で確定。

### 残作業と見通し

1. **A-5 配線** (近接、tractable、~150-250 行): 4 producer を `h_pos_stam` バンドルに供給。
   **着手前に variance bookkeeping を verbatim 照合**: `h_reg_sum.density_t` の conv-pin は variance-t
   kernel に pin する一方、和の noise `Z_X+Z_Y ~ N(0,2)` の真の密度は variance-2t — `pX_sum` witness の
   構成を確定しないと precondition (3) の同定経路が drift しうる ([[feedback_independent_wall_recheck]])。
2. **上流壁** (中距離、plan 所有): `epi-stam-to-conclusion-phaseA-plan` の joint 4-tuple independence
   (`hXYZXY`, `EPIStamToBridge.lean:1343`、noise model 強化が closure)、G2 continuity、rescale。
3. **最深・未確定** (`wall:stam-blachman`): score の確率的 (condExp) 表現 `s_Z = E[s_X | X+Y=z]`。
   density route で in-house closeable の可能性と、disintegration 橋が真の Mathlib PR 級 (~300 行
   multi-file) に戻るリスクの両方が記録されている (L-EPIW-3-α/4-α)。**ここが in-house で割れるか
   Mathlib PR 待ちかが一般 EPI closure 可否の分岐点**。

**ETA は数値で出せない**: この frontier は「~100 行」→「~300 行 PR 級」→「false-statement defect」→
「scoped multi-session path」→「producer 層 landing」と繰り返し再分類されてきた (下記履歴)。
近接の A-5 配線は数セッション、最深壁の可否は次の再評価で見える段階。

## 診断履歴 (壁の再分類経緯、時系列)

ハードに得た「壁判定の誤りやすさ」の記録。要約のみ (詳細は git history + 各 plan)。

- **当初 (Rioul 2011 §II-C)**: Stam Step 2 を「~100 行 density 計算」と見積もり。
- **2026-05-30 scope-out 確定**: 「Fisher/score/density 計算が Mathlib 全不在の (a)+(b) 混合壁 ~300 行
  PR 級」と判定し scope-out。`IsStamCauchySchwarzOptimal` を shared sorry `stam_step2_density_wall`
  (`@residual(wall:stam-step2-density)`) に降格。
- **2026-05-30 wall 集約**: load-bearing predicate `IsStamTotalExpectation` / `IsStamScoreConvolution`
  を全廃、孤立 island (predicate 2 + structure + theorem ~12) 削除、残 sorry を単一 wall に収束。
- **2026-05-30 再 attack (判断 #17)**: scope-out 診断の **部分是正**。(i) gateway 基盤
  (`convDensity_add_differentiable` + `score_cross_term_eq_zero`) は genuine 構築可能と判明
  (`hasDerivAt_integral_of_dominated_loc_of_deriv_le` で `HasCompactSupport` 不適合を回避)。
  (ii) `wall:stam-step2-density` は真壁ではなく **tier-5 false-statement defect** — `IsStamCauchySchwarzOptimal`
  が密度を無制約全称量化 + `fisherInfoOfMeasureV2` measure 無視で `fXY=fX⋆fY` 制約欠落 → FALSE
  (反例 fX=fY=𝒩(0,1)/J=1, fXY=𝒩(0,1/100)/J=100; `100≤1/2` 偽、closed-form
  `fisherInfoOfDensity(𝒩 m v).toReal=1/v` で verbatim 検算)。同型 defect 計 3 述語、`@audit:defect(false-statement)
  @audit:closed-by-successor(epi-wall-reattack-plan)` 是正。判断 #14/#15 の「真の (b) 解析壁」診断は
  (e) scaffolding-was-false へ是正。
- **2026-05-30 (続) density route 格下げ**: `fisherInfoOfMeasureV2 _μ f = fisherInfoOfDensity f`
  (`FisherInfoV2DeBruijn.lean:86` `rfl`、measure 無視) 発見 → target が純密度命題に collapse、抽象
  condExp/condDistrib/disintegration 不要。条件付き密度を Bochner ∫ で明示書下す **scoped multi-session
  path** に格下げ (unscoped PR 壁ではない)。
- **2026-05-30 (続々) Blachman に既知の真壁なし**: density route で `convDensityAdd_hasDerivAt_of_regular`
  (3a GATE) / `EPIBlachmanDensity.lean` の S2/S3/S4 (Blachman score 表現を condExp 不使用で明示 Bochner ∫
  だけで構築、Jensen `ConvexOn.map_integral_le` 込み) を全て genuine 0-sorry / sorryAx-free / `@audit:ok`。
  独立監査が `wall:stam-blachman` を `plan:` に誤分類訂正 (Jensen+Tonelli+repo lemma で closable)。
- **2026-06-01 (session 11) producer 層 landing**: 上記「最新進捗」。A-5 caller 供給 precondition 4 種に
  genuine producer 全揃え。Stam-Blachman の最深壁の手前まで genuine 化。

**一貫する教訓**: 「壁」は証明戦略に紐付く。`fisherInfoOfMeasureV2` の measure 無視で target が純密度命題に
collapse し、抽象 condExp 経路の壁を明示積分経路が回避した。loogle 0 件は壁の必要条件であって十分条件でない
([[feedback_independent_wall_recheck]])。tier-1 `@audit:ok` 付与は `#print axioms` 必須
(file-local `rg sorry` は transitive sorry を捕捉できず、conditional wrapper と headline-routing wrapper が
同型 signature でも proof-done 状態が逆になる)。

## plan / file ポインタ

- plan: `docs/shannon/epi-blachman-general-density-plan.md` (producer 層、G/P1-P4 全 ✅、A-5 配線のみ残)、
  `epi-stam-to-conclusion-plan` / `-phaseA-plan` (Stam→結論本線)、`epi-wall-reattack-plan.md` (壁再 attack)、
  `epi-csiszar-ratio-reframe-plan.md` (Csiszár ratio)、`epi-debruijn-pertime-closure` (per-time de Bruijn)。
- inventory: `docs/shannon/epi-blachman-general-density-inventory.md` (4 precondition feasibility map)。
- 主要 file: `EntropyPowerInequality.lean:287` (headline)、`EPIStamToBridge.lean:1287-1345` (A-5 バンドル +
  `:1343` hXYZXY sorry)、`FisherInfoV2DeBruijn.lean:204-267` (`density_t_eq` conv-pin)、producer 5 file (上表)。
- 退避済 handoff: `.claude/handoff-2026-06-01-session11.md` (session 11 詳細、next step = A-5 配線)。
