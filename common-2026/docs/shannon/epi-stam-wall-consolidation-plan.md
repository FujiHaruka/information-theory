# EPI Stam wall consolidation — load-bearing predicate 全廃計画

> **Parent**: [`epi-moonshot-plan.md`](./epi-moonshot-plan.md) (L-EPI1/L-EPI3 honesty 是正)
> **Sister**: [`epi-stam-to-conclusion-plan.md`](./epi-stam-to-conclusion-plan.md) (旧 `@residual` 発行元) /
> [`epi-stam-discharge-plan.md`](./epi-stam-discharge-plan.md) (Step12 chain の publish 元)
> **Status**: 起草完了 (2026-05-30)、着手待ち。

<!--
状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
判断ログ append-only。
-->

## 進捗

- [x] Phase 0 — verbatim 在庫確認 (本計画の Context が SoT、再確認は実装時) ✅(計画段階で実施済 + 実装時再 grep でも consumer 0 確認)
- [x] Phase 1 — `EPIStamStep3Body.lean` load-bearing predicate 載せ替え ✅(`isStamInequalityHyp_via_step3` を regularity → `stam_step2_density_wall` 委任に書換、`@residual(wall:stam-step2-density)`。`IsStamFisherCoupling`/`IsStamTotalExpectation`/`isStamTotalExpectation_symm`/`isStamFisherCoupling_of_totalExpectation`/`stam_step3_of_step1_step2`/`isStamCauchySchwarzOptimal_of_coupling`/`stam_step3_to_step4_optimal`/`step3_chain_eq_body_chain` 削除)
- [x] Phase 2 — `EPIStamDeBruijnConclusion.lean` consumer 書換 ✅(`isStamInequalityHyp_of_primitives` を regularity 版に + `@residual(wall:stam-step2-density)`。structure `IsEPIStamDeBruijnPipeline` + helper 7 件削除、`entropy_power_inequality_via_stamDeBruijn` を regularity 版に)
- [x] Phase 3 — dead hypothesis `h_conv` drop ✅(`stam_inequality_via_predicate_optimal`/`isStamInequalityHyp_via_body`/`isStamInequalityHyp_via_body_to_pipeline` から削除、consumer `entropy_power_inequality_via_body`/`isStamInequalityHyp_of_step12` の cosmetic 呼出簡約。`IsStamScoreConvolution` def + `_intro` は `@audit:ok` 維持で残置)
- [x] Phase 4 — `IsStamTotalExpectation` / `IsStamFisherCoupling` deprecate ✅(両 def 削除済 — Phase 1 で consumer 0 確認後に削除。§5 Gaussian saturation 群は参照無し確認済)
- [ ] Phase 5 — 独立 honesty audit + `@audit:retract-candidate` 再判定 📋 (orchestrator が起動)

proof-log: no (honesty 是正のみ、新規 analytic 証明なし。各 Phase の判断は本計画判断ログに追記)

## ゴール / Approach

### ゴール

Stam chain に残る **load-bearing predicate** (`IsStamTotalExpectation`, および h_conv 経由で
混入する `IsStamScoreConvolution` の load-bearing 化) を全廃し、単一 honest shared sorry 補題
`stam_step2_density_wall` (regularity 前提のみ) への委任に集約する。これは **proof-done 前進では
なく honesty 是正** — tier-3/4 load-bearing wrapper を tier-2 (sorry + `@residual(wall:...)`) に
降格させ、`@audit:retract-candidate(load-bearing-predicate)` で bookkeeping されている declaration
群を「shared wall への正規呼び出し」に置換する。

### Context — verbatim 確認結果 (2026-05-30、実コード照合済)

CLAUDE.md「具体的数値・型予測の verbatim 確認」に従い、orchestrator brief の主張を全て実コードで
照合した。結論を先に列挙する:

**(C1) `h_conv` 未使用は TRUE。** `EPIStamInequalityBody.lean:297` `stam_inequality_via_predicate_optimal`
の body (`:308-310`) は `h_le := h_cs_opt ...` を取り `stam_inverse_form_of_harmonic_mean hJX hJY hJsum h_le`
を返すだけ。`h_conv : IsStamScoreConvolution X Y P` は引数に居るが body で一度も参照されない (dead
hypothesis)。`isStamInequalityHyp_via_body` (`:318`) も `h_conv` `h_cs_opt` 両方を前者へ forward する
が、最終的に使われるのは `h_cs_opt` のみ。**`h_conv` は cosmetic slot で drop 可能。**

**(C2) `IsStamScoreConvolution` は load-bearing predicate ではなく honest discharged (tier-1)。**
`EPIStamInequalityBody.lean:115` の def は「∃ lam ∈ [0,1], lam = J_Y/(J_X+J_Y)」という λ-witness 存在
だけを要求し、`isStamScoreConvolution_intro` (`:131`, `@audit:ok`) で **無条件構成済** (`positivity` +
`div_le_one`)。つまり `IsStamScoreConvolution` を引数に取る theorem でも、その実体は無条件に供給できる
ため証明の核心を抱えない。docstring (`:110-112`) が「**not load-bearing**」と明示。よって `h_conv`
は (C1) で未使用かつ (C2) で無条件構成可能 = **二重に害が無い** cosmetic argument。`@audit:ok` 維持で
良いが、未使用引数として signature から落とすのが cleaner。

**(C3) `IsStamTotalExpectation` は genuine load-bearing。** `EPIStamStep3Body.lean:140` の def は
「∀λ ∈ [0,1], J_sum ≤ λ²J_X + (1-λ)²J_Y」を要求 (= `IsStamCondExpCSHyp` と同型の ∀λ convex Fisher
bound)。これを引数に取る 4 theorem (下表) は全て body `sorry` + `@residual(plan:epi-stam-to-conclusion-plan)`
で、predicate が証明の核心 (Step 2-3 解析核) を抱える load-bearing 形。判定軸「regularity precondition
か証明の核心か」→ **証明の核心**。tier-4 寄り (旧 `@audit:retract-candidate(load-bearing-predicate)`
で bookkeeping 中)。

**(C4) 既に honest な代替経路が wired 済。** これが最重要発見。`stam_step2_density_wall`
(`EPIStamInequalityBody.lean:283`, `@residual(wall:stam-step2-density)`) が regularity 前提のみで
`IsStamCauchySchwarzOptimal X Y P` を返す shared sorry 補題として **既に存在し、かつ既に使われている**:
`entropy_power_inequality_via_body` (`:477`) が `:484` で `stam_step2_density_wall P X Y hX hY hXY` を
呼び、`:485` で `isStamInequalityHyp_via_body (isStamScoreConvolution_intro X Y P) h_cs_opt` に渡して
genuine `IsStamInequalityHyp` を得る。つまり **Step3Body chain (`IsStamTotalExpectation` 経由) を
通らずに、regularity → shared wall → genuine arithmetic → `IsStamInequalityHyp` の経路が成立済**。

**(C5) Step3Body chain は parallel/redundant、外部 consumer 0。** `IsStamFisherCoupling`
(`EPIStamStep3Body.lean:112`, `:= IsStamCauchySchwarz` の def-equal alias) は **EPIStamStep3Body.lean
内でしか参照されない** (定義 + 生成 2 箇所のみ、cross-file consumer 0、`rg` 確認済)。
`isStamInequalityHyp_via_step3` / `isStamInequalityHyp_of_primitives` / `IsEPIStamDeBruijnPipeline`
の cross-file consumer も 0 (`rg` で EntropyPowerInequality / EPIStamToBridge を grep → ヒット無し)。
公開 EPI 主定理 `entropy_power_inequality` (`EntropyPowerInequality.lean:261`) は別経路
(`IsStamInequalityResidual` → `entropy_power_inequality_unconditional` @ `EPIStamToBridge.lean:1105`)
を使う。**Step3Body chain 全体が end-to-end からは到達不能な孤立 island。**

**(C6) sister plan との整合。** `EPIStamStep3Body.lean` + `EPIStamDeBruijnConclusion.lean` の
load-bearing 群は sister `epi-stam-to-conclusion-plan` (Scope 表で両 file を所管、合計 23 件 suspect) が
`@residual(plan:epi-stam-to-conclusion-plan)` で発行している。本計画は sister の closure target を
「genuine analytic 証明を埋める」から「shared wall 委任で predicate を全廃する」へ **方針変更** する
提案。矛盾点は判断ログ #1 に明記。

### Approach — 集約の全体像

**理想形 (load-bearing predicate ゼロ)**:

```
regularity (P prob / X,Y measurable / IndepFun)
  └─ stam_step2_density_wall              ── shared sorry, @residual(wall:stam-step2-density)
       → IsStamCauchySchwarzOptimal X Y P
            └─ isStamInequalityHyp_via_body (isStamScoreConvolution_intro …) _   ── genuine arithmetic
                 → IsStamInequalityHyp X Y P                                       ── @audit:ok 可
```

この経路は (C4) で既に `entropy_power_inequality_via_body` に wired 済。本計画は **Step3Body chain の
4 theorem を、自前 `IsStamTotalExpectation` 仮説の代わりにこの shared wall 経路に載せ替える** ことで
load-bearing 仮説を除去する。各 theorem の結論型は変えず (signature の honesty を保つ)、仮説部だけを
`IsStamTotalExpectation` → regularity (`Measurable` / `IndepFun` / `IsProbabilityMeasure`) に差し替え、
body を shared wall 呼び出し or 既存 arithmetic 適用に書き換える。

**`IsStamFisherCoupling` (中間型) の扱い** (C5 より): 外部 consumer が無く、`IsStamCauchySchwarz` の
def-equal alias に過ぎないので、本計画では **deprecate (削除 or `@audit:retract-candidate`)** を第一
候補とする (Phase 4)。`isStamCauchySchwarzOptimal_of_coupling` (`:230`) の結論型は
`stam_step2_density_wall` と**完全に同一** (`IsStamCauchySchwarzOptimal X Y P`) なので、この theorem は
shared wall への 1 行 alias に縮約できる。

**fallback (部分集約)**: もし `EPIStamDeBruijnConclusion` の structure `IsEPIStamDeBruijnPipeline` を
参照する hidden consumer が判明した場合 (現状 (C5) では 0)、structure 自体は残し `totalExp` field を
regularity bundle に置換する Phase 2 縮退版を採る。撤退ライン参照。

## Phase 1 — `EPIStamStep3Body.lean` load-bearing predicate 載せ替え 📋

対象 4 theorem + 1 helper。**載せ替え表** (現 signature → 新 signature):

| # | theorem (line) | 現 hyp | 新 signature | 新 body | 結論型変化 |
|---|---|---|---|---|---|
| 1 | `isStamCauchySchwarzOptimal_of_coupling` (230) | `h_te : IsStamTotalExpectation` | `(P)[IsProbabilityMeasure P](X Y)(hX hY hXY)` | `stam_step2_density_wall P X Y hX hY hXY` (結論型一致、1 行) | なし |
| 2 | `stam_step3_to_step4_optimal` (246) | `h_te` | regularity 4 引数 | `(stam_step2_density_wall …) J_X J_Y …` を展開 (= `IsStamCauchySchwarzOptimal` を ∀-instantiate) | なし |
| 3 | `stam_step3_of_step1_step2` (206) | `h_conv + h_te` → `IsStamFisherCoupling` | regularity (h_conv drop) | `IsStamFisherCoupling := IsStamCauchySchwarz`、`isStamCauchySchwarz_of_condExpCSHyp` 経路 or shared wall の existence 弱化形へ縮約 | なし (中間型は Phase4 で deprecate 検討) |
| 4 | `isStamInequalityHyp_via_step3` (269) | `h_conv + h_te` → `IsStamInequalityHyp` | regularity (h_conv drop) | `isStamInequalityHyp_via_body (isStamScoreConvolution_intro X Y P) (stam_step2_density_wall P X Y hX hY hXY)` | なし |
| 5 | `isStamTotalExpectation_symm` (162) | `h : IsStamTotalExpectation` → `IsStamTotalExpectation Y X` | (Phase4 で predicate 自体 deprecate なら削除) | — | 予定削除 |

- [ ] #4 `isStamInequalityHyp_via_step3` を最優先で載せ替え (これが arithmetic deliverable、`@audit:ok` 化目標)
- [ ] #1 #2 を shared wall instantiate に書換
- [ ] #3 中間型 `IsStamFisherCoupling` 経由を維持するか直結するか Phase4 判定に依存させる
- [ ] #5 helper は Phase4 の `IsStamTotalExpectation` 削除判定とセットで処理

**注意 (新規 load-bearing 混入防止)**: 載せ替え後の signature が regularity だけになっているか確認。
`stam_step2_density_wall` は `[IsProbabilityMeasure P]` を要求するので、`{P : Measure Ω}` の暗黙引数を
`(P : Measure Ω) [IsProbabilityMeasure P]` に格上げが必要。`Measurable X` `Measurable Y` `IndepFun X Y P`
も明示引数に追加。これらは全て regularity precondition (証明の核心ではない) なので honest。

## Phase 2 — `EPIStamDeBruijnConclusion.lean` consumer 書換 📋

対象 (verbatim 確認済、`:170` `:187` `:201` `:218` `:234` `:246` `:319` `:338`):

| declaration (line) | 現状 | 書換 |
|---|---|---|
| `isStamInequalityHyp_of_primitives` (171) | `h_conv + h_te` 引数、`@audit:retract-candidate(load-bearing-predicate)` | regularity 引数に置換、body = `isStamInequalityHyp_via_step3` (Phase1 #4 の新形) 呼び出し。`@audit:ok` 化 |
| structure `IsEPIStamDeBruijnPipeline` (187) field `convScore`/`totalExp` (190/192) | load-bearing predicate 2 field | **structure 削除が第一候補** (consumer 0、C5)。残す場合は regularity bundle 化 |
| `isStamInequalityHyp_of_stamDeBruijn` (201) | `h.convScore`/`h.totalExp` extract | structure 削除なら本 theorem も削除 |
| `isEPIL3IntegratedPipeline_of_stamDeBruijn` (218) | structure → `IsEPIL3IntegratedPipeline` | 同上、structure 削除なら regularity 直結版に |
| `entropy_power_inequality_via_stamDeBruijn` (234) | pipeline 引数の EPI、`@audit:retract-candidate` | 既に `entropy_power_inequality_via_body` (honest) が同等 → 削除 or honest 版へ forward |
| `isEPIStamDeBruijnPipeline_of_primitives` (246) / `_symm` (319) / `_congr` (328) / `_roundtrip` (338) | structure 操作 helper | structure 削除に伴い削除 |

- [ ] `isStamInequalityHyp_of_primitives` を regularity 版に書換 (consumer 0 確認後 signature 自由に変更可)
- [ ] structure `IsEPIStamDeBruijnPipeline` 削除可否を Phase 0 再 grep で最終確認 → 削除
- [ ] structure 依存 helper 群 (`:201` `:218` `:246` `:319` `:328` `:338`) を削除 or 縮約

**consumer breakage 分析**: (C5) より cross-file consumer 0。`entropy_power_inequality_via_stamDeBruijn`
(`:234`) は公開主定理 `entropy_power_inequality` に到達していない (主定理は `IsStamInequalityResidual`
経路、C5)。したがって本 Phase の削除は **end-to-end EPI 主定理を一切変えない** (孤立 island の除去)。
regularity 前提 (`IsProbabilityMeasure` / `Measurable` / `IndepFun`) は `entropy_power_inequality_via_body`
が既に同じ前提で通している (`:478-480`) ので、上流供給可能性は実証済。

## Phase 3 — dead hypothesis `h_conv` drop + `IsStamScoreConvolution` 整理 📋

- [ ] `stam_inequality_via_predicate_optimal` (`EPIStamInequalityBody.lean:297`) の `h_conv` 引数削除
  (body 未使用、C1)。consumer は `isStamInequalityHyp_via_body` のみ → 連動修正
- [ ] `isStamInequalityHyp_via_body` (`:318`) の `h_conv` 引数削除。consumer
  `isStamInequalityHyp_of_step12` (`EPIStamStep12Body.lean:306`) + `entropy_power_inequality_via_body`
  (`:485`) は `isStamScoreConvolution_intro X Y P` を cosmetic に渡しているので、引数削除に伴い該当
  呼び出し行を簡約
- [ ] `IsStamScoreConvolution` def + `isStamScoreConvolution_intro` は `@audit:ok` の honest discharged
  なので **残す** (将来 Blachman identity を genuine 化する際の reify 先)。ただし全 consumer から
  cosmetic 引数として剥がれた後は orphan になる可能性 → Phase 5 で retract 判定

**注意**: `h_conv` drop は signature 改変なので独立 honesty audit 起動条件に該当 (Phase 5)。

## Phase 4 — `IsStamTotalExpectation` / `IsStamFisherCoupling` deprecate 判定 📋

- [ ] `IsStamTotalExpectation` (`EPIStamStep3Body.lean:140`): Phase 1-2 完了後、本 predicate を引数に
  取る theorem が 0 になる → **def 自体を削除** が第一候補。Mathlib-shape 上は `IsStamCondExpCSHyp`
  (EPIStamStep12Body) と同型なので情報損失なし。残す理由が無ければ削除、`@audit:retract-candidate`
  で history record を残すのも可
- [ ] `IsStamFisherCoupling` (`:112`, `:= IsStamCauchySchwarz` alias): 外部 consumer 0 (C5)。
  alias なので削除して `IsStamCauchySchwarz` 直接参照に統一。`name-laundering-alias` の兆候は無い
  (`launder` ではなく単なる Step-3 別名) が、孤立した def-equal alias は cleanup 対象
- [ ] §5 Gaussian saturation 群 (`stam_coupling_saturates` 等、`:289+`) が `IsStamFisherCoupling` /
  `IsStamTotalExpectation` を参照していないか Phase 0 再 grep で確認してから削除

## Phase 5 — 独立 honesty audit + retract-candidate 再判定 📋

- [ ] 全 Phase 完了後、`subagent_type: "honesty-auditor"` を 1 件起動。監査対象: Phase1-2 で
  `@audit:ok` 化した declaration の signature honesty (regularity だけか、load-bearing 残存無いか) +
  `stam_step2_density_wall` 委任の classification 正しさ (`wall:stam-step2-density` が適切か)
- [ ] `@audit:retract-candidate(load-bearing-predicate)` で bookkeeping 中の declaration 群
  (`isStamInequalityHyp_of_primitives` 他、EPIStamDeBruijnConclusion 4 件 + EPIStamStep3Body) の
  retract-candidate を **解除** (削除 or `@audit:ok` に昇格)
- [ ] sister plan `epi-stam-to-conclusion-plan` の Scope 件数 (23 件) を本集約結果で更新依頼
  (planner 再 dispatch、本計画では sister 本文を編集しない)

## 退化ガード / honesty チェックリスト

集約後に以下が **生じていない** ことを Phase 5 で確認:

- 新たな load-bearing hyp 混入なし: 載せ替え後の全 signature は regularity (`IsProbabilityMeasure` /
  `Measurable` / `IndepFun`) のみ。`Is*Hypothesis` / `Is*Expectation` predicate を仮説に取らない
- 循環なし: shared wall `stam_step2_density_wall` の結論 `IsStamCauchySchwarzOptimal` を仮説に
  取り直して `:= h` で返す passthrough を作らない (Phase1 #1 は wall を **body で呼ぶ** ので循環でない)
- 退化定義悪用なし: 旧 §5 Gaussian の `exfalso`-on-`0 < J_X` 群は既に削除済 (`:278-287` RESOLVED) で
  再導入しない
- shared wall の regularity 前提を落とさない (audit-tags.md「⚠️ consolidate 時に regularity 前提を
  壁から落とさないこと」): `stam_step2_density_wall` は `[IsProbabilityMeasure P]` + `hX hY hXY` を
  引数に持つ。consumer 側はこれらを genuine に供給する (アンダースコア放置 = laundering 兆候)

## 撤退ライン

- **L-CONS-1 (h_conv が実は使用)**: (C1) で未使用と確認済だが、万一 transitive な型推論で
  `h_conv` が必要だった場合 → Phase 3 を skip し、`isStamScoreConvolution_intro X Y P` を cosmetic
  slot に渡し続ける (現状の `entropy_power_inequality_via_body:485` と同じ honest 形)。集約自体は成立
- **L-CONS-2 (structure hidden consumer)**: Phase 0 再 grep で `IsEPIStamDeBruijnPipeline` consumer が
  発見された場合 → Phase 2 を structure 削除でなく field 置換 (regularity bundle) に縮退。structure は
  残すが `totalExp : IsStamTotalExpectation` field を削除し、derive 側で shared wall を呼ぶ
- **L-CONS-3 (regularity 上流不足)**: (C4) で `entropy_power_inequality_via_body` が同じ regularity で
  通っているため上流供給は実証済。万一 Step3Body の特定 consumer が `IsProbabilityMeasure` を持たない
  context にいた場合 → その consumer 自体が孤立 (C5) なので削除して回避。集約は全廃で完了
- **L-CONS-4 (sister plan 方針衝突)**: sister `epi-stam-to-conclusion-plan` が「genuine analytic 証明で
  Step3Body を埋める」方針を保持したい場合 → 本計画の shared wall 委任は sister と排他。orchestrator
  判断で どちらか一方を採る (本計画推奨理由 = analytic 証明は Mathlib 壁で長期、wall 委任は即 honest 化)

## 判断ログ

1. **sister `epi-stam-to-conclusion-plan` との方針差**: sister は `EPIStamStep3Body.lean` +
   `EPIStamDeBruijnConclusion.lean` を「genuine Step-3 analytic 証明 (total-expectation IBP) を埋めて
   `@audit:ok` 化」する方針で 23 件を `@residual(plan:epi-stam-to-conclusion-plan)` 発行している。本計画は
   (C4)(C5) の発見 — 既に `stam_step2_density_wall` 経由の honest 経路が wired 済かつ Step3Body chain は
   end-to-end から孤立 — を根拠に、analytic 証明を埋めるのではなく **shared wall 委任 + 孤立 island 除去**
   で honesty を達成する。両者は排他なので orchestrator が方針確定する必要あり (撤退ライン L-CONS-4)。
   矛盾は「同じ declaration の closure 手段が 2 通り」である点のみで、最終状態 (load-bearing 全廃) は一致。

2. **`@residual(wall:stam-step2-density)` が正規 closure target**: 集約後の残 sorry は
   `stam_step2_density_wall` 1 本に収束する。audit-tags.md の wall register に既登録済
   (`stam-step2-density` 行)、`stam` (inverse harmonic-mean 結論形) と semantic 区別済。本集約で新規 wall
   追加は不要。proof-done は Mathlib に score-of-convolution condExp 表現が入るまで long-term。
