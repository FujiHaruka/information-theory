# Ch.17 Inequalities — ステータス (textbook-roadmap から分離)

> `docs/textbook-roadmap.md` の Ch.17 行が肥大化したため分離 (2026-06-01)。
> roadmap 側は 1 行サマリ + 本ファイルへのポインタのみ。Ch.17 の詳細状態はここが SoT。
> コード内の `@audit:*` / `@residual` タグが最終 SoT であることは不変 (`docs/audit/audit-tags.md`)。

## 現状サマリ (2026-06-10 destale — 一般 EPI **CLOSED**)

**Ch.17 は一般 EPI も含め全て publishable。scope 内 frontier は 0 件。**
**一般 EPI は 2026-06-08 に完成** (`epi-unconditional-moonshot-plan` 完了、roadmap 判断ログ #18):

- **完全無条件版** `entropyPowerExt_add_ge_unconditional` (`EPI/Unconditional/DispatchFull.lean`、
  ℝ≥0∞ 値 `entropyPowerExt`、precondition = 可測+独立のみ、**sorryAx-free**、`@audit:ok`)。
  **3-case dispatch** (両 a.c. / 混合 / 両特異) で組み、case-1 a.c. 枝の無限分散部は 2026-06-07 に
  「無限分散 a.c. 壁」を FALSE WALL と判定 → **route T (truncation+Gibbs+DCT)** で closure。
- **実数 a.c.+有限版** `entropy_power_inequality_of_ac` (sorryAx-free)。実数は型壁 (`EReal.exp_coe` が
  a.c.+有限を要する) で完全無条件化不可、これが実数 headline の honest 限界。
- **密度版** `entropy_power_inequality_of_density` (sorryAx-free、3-noise lift + two-time route)。

再検証レシピ + 最後に通った commit は **`epi-facts.md` 行 25/27/28/29 が SoT** (本ファイルにキャッシュしない)。

> ⚠ **2026-06-10 注記**: 下記「frontier = 一般 EPI headline closure のみ」「残作業 Route A/B」「active 独立壁」
> の各節は **2026-06-06 時点 (無条件化完成前) の記述で obsolete**。一般 EPI は上記の通り別ルート (無条件
> dispatch + route T) で closure 済み — Stam-bridge `stamToEPIBridge_holds` を closure する Route A/B は
> **textbook goal の達成には不要**になった。`stamToEPIBridge_holds` は legacy Cover-Thomas 露出
> `entropy_power_inequality` (実数・`h_stam` 仮説形) を保つためだけに残る 1 sorry で、コード側は
> `@audit:superseded-by(epi-unconditional-moonshot-plan)` 付与済。以下の旧記述は履歴として残置 (参照しない)。

## proof-done (genuine, sorryAx-free)

- Han / HanD / Shearer / LoomisWhitney / BrascampLieb / Polymatroid / Pinsker (+sharp) / Hypercube /
  StamGaussianBound / HeatFlowPath ✅
- Stam Step 1 honest discharge ✅
- `entropyPower_gaussian_additivity` + `entropyPower_pos/nonneg/gaussianReal` 等 (Gaussian EPI =
  variance additivity) ✅
- CT 17.9 Minkowski determinant: Gaussian additivity から導出可能 (新規 ✅ promote 候補)

## ~~frontier = 一般 EPI headline closure のみ~~ (obsolete 2026-06-06、§現状サマリ参照)

> この節以降は無条件化完成前 (2026-06-06) の記述。一般 EPI は別ルートで CLOSED 済 (§現状サマリ)。履歴として残置。

headline `entropy_power_inequality` (`EntropyPowerInequality.lean:287`) は **proof done ではない**
(transitive wall 経由で sorryAx 依存)。一般 EPI / log・exp form / `epi_via_stam_main` 等 12 件の
`@audit:ok` は 2026-05-30 の `#print axioms` sweep で誤付与と判明し降格済 (genuine sorryAx-free は
Gaussian additivity 系のみ)。

### active な独立壁 (2026-06-06 実測 destale、`#print axioms` 裏取り済)

| slug | 性質 | 状態 (2026-06-06) |
|---|---|---|
| `plan:epi-stam-to-conclusion-plan` (`stamToEPIBridge_holds`) | Stam→EPI bridge | **唯一の active 残壁** (sorry)。旧 closure route = difference 形 (G1/G3 + de Bruijn bridge) は判断 #8 で削除済。生存 route = ratio 形 + two-time |
| `wall:stam-blachman` | score の condExp 表現 = Blachman 恒等式 | **CLOSED** (Stam 側に吸収、`isStamInequalityHyp_of_primitives:176` が sorryAx-free。旧「最深・未確定」は obsolete) |
| `wall:heatflow-continuity` / `approx-identity-L1` (G2) | heat-flow path 連続性 √t→0⁺ | **CLOSED** (2026-06-05、`heatFlowEntropyPower_continuousWithinAt_zero:583` sorryAx-free。plan の「真 Mathlib 壁 2026-06-03」は stale) |
| `wall:debruijn-integration` / `plan:epi-debruijn-pertime-closure` | per-time de Bruijn | 大半 genuine。ただし `isDeBruijnRegularityHyp_of_methodX_unitnoise` (`EPICase1RatioLimit.lean`) は **sorryAx-present** (t-可測性 residual `:2041`)。bridge closure の上流前提として要評価 |
| `wall:fisher-finiteness` | conv の Fisher 有限性 | conv-with-Gaussian 分は `gaussianConv_fisher_le_inv_var` で閉鎖 |
| `wall:csiszar` | Csiszár ratio monotonicity | genuine (`csiszarLogRatioGap_deriv_le_zero` `@audit:ok`)。bridge closure の主機構 |

### ⚠ 旧進捗 (2026-06-01, session 11) — A-5 producer 層 landing【route は判断 #8 で削除済】

> **無効化注記 (2026-06-06)**: 下記 A-5 頂点 `isStamToEPIScalingHyp_of_stam_debruijn` は判断 #8 で
> **dead として削除済** (difference 形 bridge route 全体の放棄)。ただし下層 producer 5 file の大半
> (`isRegularDensityV2_convDensityAdd_gaussian` 14 uses, `convDensityAdd_assoc` 5 uses 等) は別経路で
> live に再利用されているため file 自体は温存。A-5 頂点への配線だけが dead。以下は履歴として残す。

EPI A-5 頂点 `isStamToEPIScalingHyp_of_stam_debruijn` (旧 `EPIStamToBridge.lean:1287`、**削除済**) の `h_pos_stam`
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

### 残作業と見通し (2026-06-06 再評価、`proof-pivot-advisor` Route A/B feasibility verdict)

残壁は `stamToEPIBridge_holds` **1 個のみ**。これを閉じる 2 route を評価した:

- **Route A — two-time terminal で bridge を bypass** (当初 user 選好): `entropyPower_add_ge_case1_of_regular_twotime`
  (`EPICase1TwoTime.lean:1620`、sorryAx-free) を pure primitives から discharge し、bridge 非経由の無条件 EPI を組む。
  **advisor verdict = NOT cheaper**: (i) terminal の `h_stam_supply` (per-time harmonic Stam) は **load-bearing**
  (regularity でなく証明の核)、これを primitives 化 = Stam→EPI bridge の別形再実装。(ii) terminal の de Bruijn 前提
  producer `isDeBruijnRegularityHyp_of_methodX_unitnoise` 自体が **sorryAx-present** ⟹ 「wire すれば終わり」は誤り、
  上流に未閉 sorry。(iii) noise richness は lift (`EPINoiseExtension.lean`、sorryAx-free) で解決可だが lift 結論側
  EPI を仮説に取るため楽さに寄与せず。⟹ Route A は Route B と同じ analytic core に collapse + bundle 数が多い。
- **Route B — `stamToEPIBridge_holds` を ratio 形で in-place closure** (advisor 推奨): 生存 genuine 機構
  `csiszarLogRatioGap_deriv_le_zero` (`@audit:ok`) + G2 closure 済 (path 連続性が揃った) で bridge を直接埋める。
  1 sorry に集約、上流 regularity 供給は依然必要だが分散しない。

**決定 (2026-06-06)**: 次の実作業 = **Route B**。最初の 1 手 = `csiszarLogRatioGap_deriv_le_zero` から
`stamToEPIBridge_holds` の結論 (`IsStamInequalityResidual → IsEntropyPowerInequalityHypothesis`) までの結線で
**G2 closure 後にいま欠けている中間補題を 1 個特定する probe** (`EntropyPowerInequality.lean:251` 周辺)。
小さければ Route B 続行、大きければ `epi-debruijn-pertime-closure` を先行 (両 route 共通 dependency)。

**未処理の honesty flag (要独立 audit、別タスク)**: advisor が `methodX` 兄弟 (`EPICase1RatioLimit.lean:1498`) の
`h_pos_stam` を per-time load-bearing hypothesis (tier-5 兆候) として記録。現タスク外だが honesty-auditor の対象候補。

**ETA は数値で出せない**: この frontier は繰り返し再分類されてきた (下記履歴)。現状は「残壁 1 個に局在 +
genuine 機構が揃った」段階で、Route B probe が次の実測ポイント。

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
- **2026-06-06 残壁 1 個局在確定 + A-5 route 削除 + G2/Blachman closed 確認** (`#print axioms` 実測):
  (i) `entropy_power_inequality_via_stamDeBruijn` (`:214`、pure primitives) の唯一 transitive sorry =
  `stamToEPIBridge_holds` のみと確定。Stam 側 `isStamInequalityHyp_of_primitives` (`:176`) は sorryAx-free
  ⟹ `wall:stam-blachman`「最深・未確定」は **obsolete (CLOSED)**。(ii) G2 `wall:heatflow-continuity` も
  sorryAx-free 確認 (2026-06-05 closure) ⟹ plan の「真 Mathlib 壁 2026-06-03」タグ stale。(iii) bridge の旧
  closure route (difference 形 G1/G3 + de Bruijn bridge A-5) は判断 #8 で dead 削除済。生存 route = ratio 形 +
  two-time。`proof-pivot-advisor` が Route A (two-time bypass) vs Route B (bridge in-place) を評価 → **Route B 推奨**
  (Route A は load-bearing Stam 包装替え + sorryAx-present producer 依存で collapse)。**教訓: 壁タグは
  `#print axioms` で定期 destale せよ — 既に閉じた壁を避けて route を遠回りする事故が起きる**。

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
- 主要 file (2026-06-06 更新): `EntropyPowerInequality.lean:251` (`stamToEPIBridge_holds` = 唯一の残壁) /
  `:289` (headline)、`EPIStamDeBruijnConclusion.lean:176` (`isStamInequalityHyp_of_primitives` sorryAx-free) /
  `:214` (`entropy_power_inequality_via_stamDeBruijn` 無条件本体、唯一 sorry = bridge)、
  `EPICase1TwoTime.lean:1620` (two-time terminal sorryAx-free)、`EPIStamToBridge.lean` の ratio line
  `csiszarLogRatioGap_deriv_le_zero` (`@audit:ok`、Route B 主機構)。
  **削除済 (判断 #8、参照しない)**: `isStamToEPIScalingHyp_of_stam_debruijn` / difference 形 `csiszarGap1Source*` /
  `csiszarGap_antitoneOn_Icc_zero_one`。
- 次 session の実作業 = **Route B probe** (上記「残作業」参照)。`epi-case1-twotime-restructure-plan.md` は全 Phase
  CLOSED (判断 #9)。
