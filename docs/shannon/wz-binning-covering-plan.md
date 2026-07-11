# Wyner–Ziv achievability: D3 binning + covering closure サブ計画

> **Parent**: [`wyner-ziv-main-plan.md`](wyner-ziv-main-plan.md) §P3 D3 split-out

**Status**: ACTIVE 🚧 — 残 sorry は **D3 `wz_perN_covering_binning_code` 唯一** (`rg -n 'lemma wz_perN_covering_binning_code'` で位置、`@residual(plan:wz-binning-covering)`)。**Leg 0/A/B/C DONE** (sorry-free、`a59e37cb`/`dfdf3e42`/`02ea97d7`/`25629b0a`): Leg 0 δ-split (budget 軸 honest 化、honesty-auditor PASS) / Leg A two-ambient regularity API / Leg B source-marginal identity / Leg C distortion-decomposition bridge (`wz_expectedBlockDistortion_le_of_badSet` + `wz_covering_binning_distortion_decomp`)。**⚠ D3 は再び `@audit:defect(false-statement)`**: Leg C で **第2 under-hypothesization 軸** 判明 — `d'`(proxy)/`qf` が無関係 opaque param で `d'=𝔼_{Y|X}[d∘qf.2]` (`wz_coveringDistortion_reconcile`) を encode する仮説なし → `d':=0` 反例で結論不従。Leg 0 監査は budget 軸のみ検証しこの軸を暗黙仮定していた。**次の本線 = Leg C.5 (D3 に `hd'_eq`+`hqf` を precondition threading、δ-split 同型の非 bundling fix) → 独立監査 → Leg D**。WZ achievability 全体の残 sorry はこの D3 1 本のみ (S1-S7 / D1 / D2 / (B) / gateway 1-2 は全て CLOSED sorry-free、legs 12-19)。

**再検証** (prose にキャッシュしない): `scripts/sig_view.ts --sorry InformationTheory/Shannon/WynerZiv/Achievability.lean` / `#print axioms wyner_ziv_achievability`。

## 進捗

- [x] Leg 0 — δ-split 署名修正 (D3 honest 化、tier-5 fix、5-decl file-contained ripple) ✅ (`a59e37cb`、独立監査 PASS)
- [x] Leg A — two-ambient WZ-joint 構成 (pure regularity) ✅ (`dfdf3e42`、sorry-free)
- [x] Leg B — α'→α source-measure 変数変換 lemma (medium) ✅ (`02ea97d7`、sorry-free)
- [x] Leg C — WZ distortion-decomposition bridge (解析コア) ✅ (`25629b0a`、bridge 2本 sorry-free)。**finding: D3 に第2 under-hyp 軸 → Leg C.5 へ**
- [ ] Leg C.5 — D3 署名 reconciliation 修正 (`hd'_eq` + `hqf` threading、第2 tier-5 fix、**Leg D 前**) 📋
- [ ] Leg D — derandomize + squeeze glue → D3 sorryAx-free closure (**C.5 後**) 📋

## ゴール / Approach

### Goal

親 §P3 の唯一の残 sorry である D3 `wz_perN_covering_binning_code` (Achievability.lean:2054、sorry L2082) を、**まず δ-split で honest 化** (Leg 0、false-as-framed 訂正) した上で **genuine closure** (Leg A-D)、WZ achievability headline `wyner_ziv_achievability` を sorryAx-free (`[propext, Classical.choice, Quot.sound]`) へ到達させる。

D3 の署名 (現状、Achievability.lean:2054-2080、δ-split 前):

```lean
-- hfeas : expectedDistortionPmf d' qStar ≤ D + δ            -- ← Leg 0 で ≤ D + δ/2 に締める
-- hcov₁ : … c.expectedBlockDistortion (…) d' ≤ (D + δ) + ε'  -- ← Leg 0 で ≤ (D + δ/2) + ε' に締める
-- 結論: ∃ N, ∀ n, ∃ c : WynerZivCode (codebookSize R n) n α β γ,
--         N ≤ n → c.expectedBlockDistortion P_XY d ≤ D + δ   -- ← 不変 (δ/2 を誤差に予約)
```

### Approach (overall strategy / shape of solution)

解の全体像は 4 段:

1. **署名を honest 化 (Leg 0、δ-split)** — D3 の `hfeas`/`hcov₁` の target を `D + δ/2` に締め、`δ/2` を WZ 誤差項に予約する (RD 姉妹定理 `rate_distortion_achievability` の明示 slack 仮説 `h_slack` と同型)。これは precondition の締めであって bundling ではない: covering atom `wz_covering_lossyCode_exists` (Achievability.lean:709) は任意 target `≤ D` を受けて `≤ target + ε'` を返す flexible atom ゆえ、target `D + δ/2` は genuinely achievable。
2. **閉じた error 事象確率 atom を実 distortion に橋渡し** — error 事象確率の閉じた atom 群 (S5a covering-failure / S5b codebook-restricted confusion / D2 codeword mass upper bound / (B) binning collision / gateway-2 E3 covering-acceptance) を、**two-ambient WZ-joint 構成 (Leg A)** + **α'→α 測度変換 (Leg B)** + **distortion-decomposition bridge (Leg C)** で `wzCodeOfCoveringBinning` の実 `expectedBlockDistortion P_XY d` に接続する。
3. **derandomize + squeeze (Leg D)** — per-n error 確率 (E1+E2+E3) → 0 を double derandomization で決定的 codebook + binning に固定し、squeeze で残 distortion excess を `δ/2` に押さえて `≤ D + δ` を得る。
4. **伝播** — D3 body の sorry が消えると、Achievability.lean 内の上流 chain (D `wz_perDelta_covering_binning_eventual` → S6 → `wz_perDelta_codes_exist` → `wz_goodCode_exists_of_testChannel` → headline) が transitive sorryAx を失い、`wyner_ziv_achievability` が sorryAx-free になる。

**未構築の load-bearing コア 3 つ** (leg-20 finding、`wzCodeOfCoveringBinning` は def+docstring 以外に消費者ゼロ = error 確率 atom を実 distortion に橋渡しする bridge が未着手):

- **(i) distortion-decomposition bridge** (Leg C、解析コア): `(wzCodeOfCoveringBinning …).expectedBlockDistortion P_XY d ≤ (expectedDistortionPmf d' qStar + δ_typ) + distortionMax d · (P[E1]+P[E2])`。RD `source_avg_distortion_le_simpler` (AchievabilityAsymptoticFailureDecay.lean:203) の bin-decoder 版 — S4 `wzBinTypicalDecoder` (Achievability.lean:1072) は bin member のみ探索するので RD flat-codebook 版から再構築要。
- **(ii) two-ambient 構成** (Leg A、regularity): D3 仮説に Ω / iid RV は無い。covering ambient `rdAmbient qStar` (Xs=iidXs, Us=iidYs) が S5a / covering-acceptance を、別の (U,Y) ambient が S5b / decoder-confusion を駆動する。同一 3-var `q'` の 2 marginal (共有 U-marginal で coupling)、rate split `R = I(X;U) − I(Y;U)` が 2 指数を分ける。regularity は `rdAmbient_*` / `measurable_iid*` (AchievabilityAmbientMeasure.lean:153-235) で discharge。
- **(iii) α'→α source-measure 変数変換** (Leg B): 既存 `wz_expectedBlockDistortion_source_agree` (Achievability.lean:551) は同一 `P_XY` 下の 2 α-code 比較 (null-set) のみで、iid ambient (α' = `{x // 0 < P_X x}`) から `Measure.pi P_XY` (α×β) への測度変換は未提供 → 新 lemma 要。

## Leg 詳細

### Leg 0 — δ-split 署名修正 (D3 honest 化)

**proof-log**: no (署名 literal 締め + call-site 変更 + 5-decl chain 再監査、mechanical)

- **修正内容**: D3 / D `wz_perDelta_covering_binning_eventual` (2142) / S6 `wz_perDelta_covering_binning` (2224) の 3 署名で `hfeas` を `≤ D + δ/2`、`hcov`/`hcov₁` の target を `≤ (D + δ/2) + ε'` に締める。**結論 `≤ D + δ` は 3 署名とも不変** (δ/2 を誤差に予約)。covering data を供給する `wz_perDelta_codes_exist` (2284) は `wz_coveringFamily_of_testChannel` を `δ/2` (`half_pos hδ`) で呼ぶ **call-site 変更のみ** (署名不変、conclusion `≤ D + δ`)。`wz_coveringFamily_of_testChannel` (955) は δ generic ゆえ **署名不変**、δ/2 を渡すと出力 bound が自動で `D + δ/2` になる (@audit:ok 保持)。
- **ripple (機械確認済、file-contained)**: 触れる 5-decl chain = `wz_coveringFamily_of_testChannel:955` / `wz_perDelta_covering_binning_eventual:2142` / D3 `wz_perN_covering_binning_code:2054` / S6 `wz_perDelta_covering_binning:2224` / `wz_perDelta_codes_exist:2284`。**この 5 decl はいずれも Achievability.lean 内でのみ参照** (`rg -l` で cross-file consumer 0、root olean stale ゆえ `dep_consumers.sh` は不可、text-level 確認)。よって blast radius は Achievability.lean 単一ファイル。`wz_goodCode_exists_of_testChannel:2424` + `wz_diagonalize_slack` は δ を内部導入するため **不変** (per-δ 結論が `≤ D + δ` のまま)。
- **honesty**: D3 の `@audit:defect(false-statement)` + `@audit:closed-by-successor(wz-binning-covering)` は **署名 tighten 後に除去** (body が sorry のままでも、署名が honest = TRUE-as-framed になった時点で defect tag を外し `@residual(plan:wz-binning-covering)` 単独に戻す)。δ-split は precondition の締め (bundling でない、上記 Approach 1)。修正後、chain の @audit:ok (`wz_coveringFamily_of_testChannel`) + tier-2 (D/S6/`wz_perDelta_codes_exist` の δ/2 threading) が honest かを **独立 honesty-auditor 1 pass** (orchestrator-mandatory: 既存 @audit:ok の honesty-relevant 署名変更)。
- **撤退**: 署名 tighten が過度に invasive なら D3 body は `sorry + @residual(plan:wz-binning-covering)` 維持だが、**`@audit:defect(false-statement)` は署名が honest 化するまで除去禁止**、かつ **Leg 0 未完のまま Leg C の body fill に進まない** (偽 statement を fill することになる)。

### Leg A — two-ambient WZ-joint 構成 (pure regularity)

**proof-log**: no (regularity plumbing、再開根拠不要)

- **目標**: D3 body 内で 2 つの ambient を構成 — covering ambient `rdAmbient qStar` (`(…).map (iidXs 0)` = X 側、`iidYs` = U 側) が S5a covering-failure / gateway-2 covering-acceptance を、別の (U,Y) side-info ambient が S5b decoder-confusion / D2 codeword mass を駆動。同一 3-var `q'` の 2 marginal (`wzMarginalXU` / `wzMarginalYU`) で、共有 U-marginal を通じ coupling。gateway atom の i.i.d. bundle (`iIndepFun` / `IdentDistrib` / `hpos*` / `hmarg_X/Y`) を regularity として discharge。
- **消費 atom** (AchievabilityAmbientMeasure.lean、verbatim): `rdAmbient:153` / `rdAmbient_isProbabilityMeasure:156` / `rdAmbient_map_iidXs:165` / `rdAmbient_map_iidYs:174` / `rdAmbient_map_jointSequence:183` / `rdAmbient_iidXs_isProbabilityMeasure:191` / `rdAmbient_iidYs_isProbabilityMeasure:199` / `expectedJointDistortion_rdAmbient:216`。親 §B4 / gap #2 の two-ambient subtlety。
- **撤退**: stall 時 sub-lemma を signature 維持のまま `sorry + @residual(plan:wz-binning-covering)`。regularity を `*Hypothesis` に bundle しない。
- **依存**: Leg 0 と独立 (regularity は署名 δ に依存しない) ゆえ Leg 0 の次に着手 (δ-split 修正から最も独立)。

### Leg B — α'→α source-measure 変数変換 lemma

**proof-log**: yes (測度変換の枠組みは再開根拠に保存)

- **目標**: 新 lemma — iid ambient `(rdAmbient qStar).map (iidXs 0)` (α' = `{x // 0 < ∑ y P_XY(x,y)}` 上) の block distortion を `Measure.pi P_XY` (α×β 上) の `expectedBlockDistortion` に変換。既存 `wz_expectedBlockDistortion_source_agree` (551) は同一 `P_XY` 下の 2 α-code 比較 (null-set transport) のみで α'-ambient → `Measure.pi P_XY` の測度変換は無い。
- **消費 atom**: `wz_expectedBlockDistortion_source_agree:551` (α-code 側 null-set transport)、`wzLiftSupportCode:1450` (S7、α'→α support lift)、`measurePreserving_eval` coordinate marginal。
- **撤退**: `sorry + @residual(plan:wz-binning-covering)`。
- **依存**: Leg 0 / A と独立 (medium)。

### Leg C — WZ distortion-decomposition bridge (解析コア)

**proof-log**: yes (解析コア、再開根拠に必須)

- **目標** (上記 Approach (i)): `(wzCodeOfCoveringBinning …).expectedBlockDistortion P_XY d ≤ (expectedDistortionPmf d' qStar + δ_typ) + distortionMax d · (P[E1]+P[E2])`。RD `source_avg_distortion_le_simpler` (AchievabilityAsymptoticFailureDecay.lean:203) の bin-decoder 版を再構築 (S4 `wzBinTypicalDecoder:1072` は bin member 限定探索)。
- **消費 atom**: `source_avg_distortion_le_simpler` (AchievabilityAsymptoticFailureDecay.lean:203)、S3 `wzCodeOfCoveringBinning:1056` / S4 `wzBinTypicalDecoder:1072`、閉じた error atom S5a `wz_covering_failure_prob_le:1133` / S5b `wz_codebook_confusion_expectation_le:1254` / D2 `wz_covering_codeword_sideInfo_mass_le:1807` / (B) `wzIndexBinningMeasure_collision:1504` / gateway-2 E3 `wz_covering_sideInfo_mass_ge:144`。Leg A の two-ambient error 確率が入力。
- **honesty**: distortion-shape 整合 (被覆歪 X↔U proxy `d'` vs WZ 実歪 X↔γ + side-info) は body に置く load-bearing subtlety、`*Hypothesis`/`*Reduction` に bundle 禁止。
- **撤退**: `sorry + @residual(plan:wz-binning-covering)`。
- **依存**: **Leg 0 の δ-split 修正後** (honest 署名 `hfeas ≤ D+δ/2` を前提に proxy budget へ δ/2 slack を確保してから解析)。Leg A の two-ambient 出力を消費。

### Leg C.5 — D3 署名 reconciliation 修正 (第2 tier-5 fix、Leg D 前)

**proof-log**: no (署名 threading + call-site discharge + 再監査、mechanical、Leg 0 と同型)

- **finding (Leg C、2026-07-11)**: D3 `wz_perN_covering_binning_code` / D `wz_perDelta_covering_binning_eventual` / S6 `wz_perDelta_covering_binning` は `d'` (covering proxy `DistortionFn α' (Fin k)`) と `qf` (test channel + reconstruction) を **無関係な opaque param** として受け、実構築での `d' = 𝔼_{Y|X}[d ∘ qf.2]` (`wz_coveringDistortion_reconcile:872`) を encode する仮説を欠く。`qf` も `WynerZivFactorizableConstraint` 無し。→ `d':=0` で `hfeas`/`hcov₁` 自明成立・実歪 `d` 結論不従 = **under-hypothesized (false-as-framed 第2軸)**。**Leg 0 δ-split 監査は budget 軸のみ検証し reconciliation を暗黙仮定していた** (監査の穴)。
- **FIX (非 load-bearing precondition threading、δ-split 同型)**: `hd'_eq : ∀ x' u, d' x' u = Real.toNNReal (∑ y, (P_XY.real{(x'.1,y)} / ∑ y', P_XY.real{(x'.1,y')}) · (d x'.1 (qf.2 (u,y))))` (= `wz_coveringDistortion_reconcile`) + `hqf : qf ∈ WynerZivFactorizableConstraint (Fin k) …` を **D3/D/S6/`wz_perDelta_codes_exist` に threading**。これらは `hfact_eq`/`hqStar_eq` と同種の **definitional/regularity precondition** (proof の核を bundle しない)。caller `wz_coveringFamily_of_testChannel` (`d'` をこの形で定義、`hqf` 保持) が **construction で discharge**。ripple は Leg 0 と同型 (Achievability.lean file-contained)。
- **honesty**: 修正後、D3 の `@audit:defect(false-statement)` + `@audit:closed-by-successor` を除去 (署名が honest 化)。**上流 chain (@audit:ok の `wz_coveringFamily_of_testChannel` 含む) への波及ゆえ独立 honesty-auditor 1 pass** (orchestrator-mandatory)。この監査は budget 軸 (Leg 0) と reconciliation 軸 (Leg C.5) の両方 + **他に隠れた under-hyp 軸が無いか**を確認する (Leg 0 監査の穴を踏まえ網羅的に)。
- **撤退**: threading が invasive なら D3 body は `sorry` 維持、ただし `@audit:defect` は署名 honest 化まで除去禁止、Leg D の assembly に進まない。
- **依存**: Leg C 後、**Leg D 前** (Leg D の bridge 実体化に `hd'_eq` が要る)。

### Leg D — derandomize + squeeze glue → D3 closure

**proof-log**: yes (最終組立、再開根拠)

- **目標**: Leg A + B + C を D3 結論 `∃N ∀n≥N …≤ D+δ` に組み上げ sorryAx-free closure。per-n error 確率 (E1+E2+E3) → 0 を double derandomization で決定的 codebook + binning に固定し、squeeze で残 distortion excess を δ/2 に押さえる。
- **消費 atom**: derandomize `exists_codebook_low_avg` (AchievabilityCodebookMatchProbability.lean:138) / `exists_pair_le_of_binning_integral_le` (SlepianWolf/FullRateRegion/PairBound.lean:848)、squeeze `source_avg_distortion_le_simpler:203`、exponent tendsto `ceil_exp_mul_exp_neg_tendsto_atTop` / `exp_neg_tendsto_zero_of_tendsto_atTop` / `wz_tendsto_exp_mul_codebookSize_inv`、S7 `wzLiftSupportCode:1450` + `wz_expectedBlockDistortion_source_agree:551` (Leg B 経由)。
- **撤退**: `sorry + @residual(plan:wz-binning-covering)`。
- **依存**: **A + B + C 完了後**。Leg D 完了で D3 body sorry 消滅 → 上流 chain が sorryAx-free に伝播 (Approach 4)。

## 撤退ライン / honesty (集約)

- **撤退口は `sorry + @residual(plan:wz-binning-covering)` のみ** (class は **`plan` 固定**)。WZ の gap は Mathlib gap でなく in-project atom の未実装 (親 §200、inventory §8) ゆえ **`wall` は使わない** (誤分類)。slug は本 plan filename stem `wz-binning-covering` に一致。
- **bundling 禁止**: covering 下界 / error 確率 / decoder-correctness を `*Hypothesis`/`*Reduction`/`IsXxxClaim` predicate に bundle しない。`Prop := True` slot 禁止、退化定義悪用禁止。regularity hyp (full-support / `IsProbabilityMeasure` / 可測性 / `iIndepFun` / `Nonempty` / uniform message) は precondition で OK。
- **δ-split は precondition 締めであって bundling でない**: `hfeas`/`hcov₁` を `D + δ/2` に締めるのは、任意 target `≤ D` を受ける flexible な covering atom (`wz_covering_lossyCode_exists:709`) に対する要求を「genuinely achievable な値」に締めるだけ。誤差項 `δ/2` は AEP 指数 (S5a/S5b/D2/(B)) が → 0 を保証する実解析 work であり、仮説に encode しない (RD `h_slack` mirror)。
- **Leg 0 の上流波及**: δ-split は Achievability.lean 内 5-decl chain (うち @audit:ok = `wz_coveringFamily_of_testChannel`) に波及するので、修正完了時に **独立 honesty-auditor 1 pass** (orchestrator-mandatory)。
- **headline signature 不変 (crux、親 #9 継承)**: `wz_goodCode_exists_of_testChannel` / `wyner_ziv_achievability` の signature に full-support 仮説を追加しない。support-restriction は proof-internal (subtype α' 経由、D3 body 内)。

## settled-facts (minimal、再導出可能なものは都度 `#print axioms` / `rg`)

- **D3 false-as-framed 判定 (leg-20、機械確認済 human-judgment)**: exact `≤ D+δ` は budget 使い切りで偽。反例 — `expectedDistortionPmf d' qStar = D+δ` (摂動を full δ に調律)、`distortionMax d = D+δ+η` (η>0, generic 非定数 d)、generic 正の P[error] → WZ 歪 = `(D+δ)+η·P[error](n) > D+δ` ∀n ゆえ `∃N∀n≥N …≤ D+δ` が全 hyp 成立下で fail。姉妹定理 `rate_distortion_achievability` (AchievabilityStrongTypicality.lean:184) は exact D+δ に到達せず `≤ D+ε'` 止まりで、明示 slack 仮説 `expectedDistortionPmf + δ_typ ≤ D+ε'/2` (L118/L202) が ε'/2 を誤差項に予約している (cross-check)。confidence: human-judgment (機械確認済、leg-20 独立監査 OVERTURN)。
- **δ-split fix が honest な根拠**: (a) precondition 締め — covering atom `wz_covering_lossyCode_exists:709` は任意 target `≤ D` を受けて `≤ target + ε'` を返す flexible atom ゆえ target `D + δ/2` は genuinely achievable、(b) non-load-bearing — 予約された `δ/2` は error 指数 (S5a/S5b/D2/(B)) が → 0 の実解析 work で仮説化しない。confidence: human-judgment (RD `h_slack` mirror)。
- **δ-split ripple = Achievability.lean file-contained**: 5-decl chain (`wz_coveringFamily_of_testChannel:955` / D:2142 / D3:2054 / S6:2224 / `wz_perDelta_codes_exist:2284`) は全て Achievability.lean 内でのみ参照 (cross-file consumer 0)。confidence: machine (`rg -l` 確認、root olean stale ゆえ `dep_consumers.sh` 代替)。

(再導出可能なもの = sorryAx-free / decl 存在 / D3 sorry の有無 はキャッシュしない。`#print axioms wyner_ziv_achievability` / `scripts/sig_view.ts --sorry` で都度。)

## 判断ログ

append-only。決着済 entry は削除 (git が履歴)、active のみ残す。≤ 10 entry。

1. **Leg 0 (δ-split) を最初に + honesty gate (active、本線)**: D3 は budget 使い切りで false-as-framed (leg-20)。FIX = δ-split (`hfeas`/`hcov₁` の target を `D+δ/2` に締め `δ/2` を誤差に予約、RD `h_slack` mirror)。ripple は Achievability.lean 内 5-decl chain (機械確認: cross-file consumer 0)、`∃N∀n` conclusion shape 不変。**Leg 0 完了 (署名 honest 化 + `@audit:defect(false-statement)` 除去) 前に Leg C の body fill に進まない** (偽 statement を fill しないため)。完了時に上流 @audit:ok の再監査を独立 honesty-auditor 1 pass。これは親 #11 under-hypothesization トラップの family 再発 (free-budget exact 結論版)。
2. **two-ambient subtlety (Leg A、親 §B4/#10 継承)**: TWO ambients — covering ambient `rdAmbient qStar` (S5a/E3 駆動) と (U,Y) side-info ambient (S5b/D2 駆動) は同一 3-var `q'` の 2 marginal で、共有 U-marginal を通じ rate split `R = I(X;U) − I(Y;U)` が一貫。regularity は `rdAmbient_*` で discharge (bundle しない)。
3. **E2 = codebook-restricted confusion が WZ の真の核 (親 #10 継承、settled)**: gateway-1 (SW exponent H(U|Y)) では消えず、S5b `wz_codebook_confusion_expectation_le:1254` (codebook 限定、CLOSED sorry-free) が WZ rate `I(X;U)−I(Y;U)` で E2 を駆動。Leg C が消費 (この atom は既に閉じている、Leg では再証明しない)。
4. **D3 第2 under-hypothesization 軸 (Leg C finding、2026-07-11、active、本線)**: δ-split (Leg 0) は budget 軸を直したが、D3/D/S6 は `d'`(proxy)/`qf` を無関係 opaque param として受け `d'=𝔼_{Y|X}[d∘qf.2]` (`wz_coveringDistortion_reconcile`) を欠く → `d':=0` 反例で結論不従 = false-as-framed 第2軸。**Leg 0 の独立監査がこの軸を見落とした** (budget のみ検証し reconciliation を暗黙仮定)。教訓: under-hyp は複数軸を持ちうる、監査は「全 param が結論に semantically 効くか」を param ごとに確認せよ (単一軸の refute で満足しない)。FIX = `hd'_eq`+`hqf` を precondition threading (Leg C.5、δ-split 同型の非 bundling、caller discharge)。修正後の再監査は両軸 + 残存軸網羅を要求。D3 に `@audit:defect(false-statement)` 再付与済 (Leg C commit 後)。cause:false-statement。これは親 #11 under-hyp family トラップの再発 (今回は proxy↔real distortion の未 threading 版)。
