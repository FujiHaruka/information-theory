# Shannon EPI: case-1 sum-noise N(0,2) 構造改変 successor サブ計画

> **Parent**: [`epi-case1-debruijn-producer-plan.md`](epi-case1-debruijn-producer-plan.md) §PB-4 / L-Sum-struct
> **Predecessor**: [`epi-case1-sum-producer-plan.md`](epi-case1-sum-producer-plan.md) (sum producer、`Z_law` を `@audit:defect(false-statement)` で park)
> **Status**: ⛔ **GS-A3' GATE REFUTED (2026-06-06、機械実証)**。factor-2 ratio-Stam arith は harmonic Stam + positivity から閉じない (`ProbeGSA3.lean` constructive counterexample、proof-log §GS-A3' probe)。**全 single-t route (B-τ/c/case-A/b-2) が REFUTED** — 単一共有-t object が variance-2 非対称 (sum 項 `2·J_sum`) を吸収できないのが共通根本。欠けている ingredient は non-local co-monotonicity `(J_X−J_Y)(N_X·J_X−N_Y·J_Y)≥0` (weight 調整でなく真の追加解析核 or two-time reparametrization restructure)。**sum producer の `Z_law` defect park は honest resting state として維持。** 旧 Status の「factor-2 = 壁でない bounded genuine」は楽観だった (機械実証で撤回)。詳細は冒頭「## 確定状態」section。
> **Scope**: docs-only (本 plan); 触る予定の実装 file は per-step 節に列挙
> **proof-log**: yes (`docs/shannon/proof-log-epi-case1-genvar-struct.md`、GS-1 probe + GS-A0 probe 結果記録済)
> **撤退口 slug**: `@residual(plan:epi-case1-debruijn-genvar-struct-plan)`
> (sum producer `EPICase1SumProducer.lean:166` の `@audit:closed-by-successor(epi-case1-debruijn-genvar-struct-plan)` が指す先)

---

## ⛔ GS-A3' GATE REFUTED (2026-06-06 後刻、機械実証 — 本 section が最優先 superseding)

> **本ブロックが全文書中で最優先**。下の「## 確定状態」5点 (GS-A3' を「壁でない bounded genuine」と
> 楽観した版) は **GS-A3' minimal probe で REFUTED**。doctrine「楽観主張も必ず実機械検証」に従い probe
> したところ、optimism が機械実証で覆った。

**機械実証 (`ProbeGSA3.lean`、`lake env lean` EXIT=0、proof-log §GS-A3' probe に verbatim)**:
1. **factor-2 ratio arith は閉じない (REFUTED)**: variance-2 sum で `d/dt log N_sum = 2·J_sum` に
   なると、arith core が要求する `2·J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y) ≤ 0` は **harmonic Stam +
   positivity から FALSE**。constructive counterexample (`J_X=2,J_Y=1,J_sum=2/3,N_X=1,N_Y=3`、Stam 等号
   成立だが結論 `1/12 > 0`) が型検査で通る。`hN_sum` lift を正しい factor で書き直すこと自体は可能だが、
   その先の `csiszar_ratio_deriv_le_zero_arith` factor-2 版が **証明不能**。
2. **欠けている ingredient = non-local co-monotonicity**: factor-2 arith は追加仮説
   `(J_X−J_Y)(N_X·J_X−N_Y·J_Y) ≥ 0` を足せば閉じる (theorem 3 で機械確認)。これは `J_i` と `N_i·J_i`
   の co-monotonicity = heat-flow family の **non-local 性質**で、Stam でも isoperimetric でも出ない。
3. **全 single-t route が REFUTED**: これは B-τ/c/case-A が失敗したのと **同一根本** = 単一共有-t object
   が variance-2 非対称 (sum 項 `2·J_sum` vs component `J_i`) を吸収できない。文献 Stam/Blachman EPI は
   X,Y を**別時刻**で摂動して factor-2 を解消する (reparametrization) が、consumer `csiszarLogRatioGap`
   は単一-t hardcode でこれを表現できない (B-τ refuted の理由そのもの)。
4. **honest resting state**: sum producer `Z_law` defect park (`EPICase1SumProducer.lean`、
   `@audit:defect(false-statement)` + `@audit:closed-by-successor`) を**そのまま維持**。EPI case-1 sum
   frontier は「単一-t object では閉じない deeper obstruction」。旧 plan の「壁でない」は機械実証で撤回。
5. **次の genuine route 候補** (どちらも未着手、tractability 未確認): (1) co-monotonicity
   `(J_X−J_Y)(N_X·J_X−N_Y·J_Y)≥0` を heat-flow family で独立 lemma 化できるか調査 (研究級 wall の可能性)、
   (2) two-time reparametrization で consumer chain を restructure (route c、~93 site、旧判定 tractable
   でない) を再評価。**weight 調整 (L-GS-A3'-weight) では済まない**ことが確定。

---

## 確定状態 (2026-06-06、機械実証で固定 — ⛔ 上の GS-A3' GATE REFUTED ブロックに superseded)

> ⚠ **この 5点 section は GS-A3' を「壁でない bounded genuine」と楽観した版で、上の「⛔ GS-A3' GATE
> REFUTED」ブロックに superseded されている**。歴史的経緯として残置。factor-2 の tractability 主張
> (点 3-4) は機械実証で覆った。route 比較の事実 (B-τ/case-A REFUTE、variance-2 intrinsic) は有効。

> この section は plan が thrash した経緯 (B-τ 本命 → REFUTE → case-A CONDITIONAL-GO → REFUTE) を
> **機械実証で確定した定説に固定**する。以下 5 点が現在の確定状態であり、本文の旧 route 記述
> (B-τ / case-A の楽観・悲観) と矛盾する場合は **本 section が優先**する。これ以上 route を増減させない。

1. **B-τ・case-A の両 route は REFUTED (機械実証)**。
   - **B-τ** (unit-noise W + 時間 reparam τ=2t): GS-1 probe item 4d で desync REFUTE (sum 項が time 2t で
     評価され X/Y 項 time t と単一共有 t に結合不能)。
   - **case-A** (advisor の「ratio core 無改変・`J_sum` v_Z 不変」shortcut): **GS-A0 probe で機械 REFUTE**
     (`proof-log-epi-case1-genvar-struct.md` §GS-A0 probe、2026-06-06)。advisor は
     **`fisherInfoOfMeasureV2` (measure-keyed wrapper、第1引数無視、`FisherInfoV2DeBruijn.lean:81`) と
     `fisherInfoOfDensityReal` (de Bruijn 微分・ratio core が実際に使う density-direct、第2引数 load-bearing)
     を取り違えた**。誤読の元は stale docstring `EPIStamToBridge.lean:892-893` (削除済 D3 difference-gap
     context を参照、live ratio core は density-direct)。

2. **probe の機械実証** (上記 case-A REFUTE の決め手):
   - **PROBE 1c**: `convDensityAdd pX g_t = convDensityAdd pX g_{2t}` は `rfl` 失敗 (carrier-t density ≠
     carrier-2t density)。`gaussianConvolution_rescale_eq` (`EPICase1RatioLimit.lean:1765`) は **path 関数
     恒等式**で density 関数 (`fisherInfoOfDensityReal` の引数) に届かない。→ carrier rescale 同定は Fisher
     値レベルに **届かない**。
   - **PROBE 3b**: v_sum=2 で sum 項 de Bruijn 微分 = `(2/2)·J_sum = J_sum`。consumer の hardcoded `2·` lift
     と衝突し `ring` が `eP·J_sum = eP·J_sum·2` 矛盾に帰着。desync は `csiszarLogRatioGap_hasDerivAt` の
     `hN_sum` lift (`EPIStamToBridge.lean:790-803`) の hardcoded `(1/2)` cancellation。

3. **真の作業 = factor-2 ratio-Stam 再導出 (GS-A3'、load-bearing 解析核)**。`Z_law=unit` の false は
   consumer の **de Bruijn 微分値の factor** に load-bearing (false unit が sum 項を `(1/2)·J_sum` と誤らせる、
   真値は variance-2 で `J_sum`)。closure には **2 consumer lemma を正しい factor で再導出**する:
   - **(a)** `csiszarLogRatioGap_hasDerivAt` の `hN_*` entropy-power lift (`EPIStamToBridge.lean:766-803`、
     sum 項 factor を `(1/2)` から正しい値 `(v_sum/2)·J_sum = J_sum` に)。
   - **(b)** `α²≤α` arith weights (`csiszar_ratio_deriv_le_zero_arith`、正しい factor で harmonic Stam が
     ≤0 を保つか)。

4. **classification — 壁でない / trivial でない**。これは **標準 de Bruijn EPI の真の数学** (sum 微分=`J`
   (variance 2)、component=`(1/2)·J`(unit)、harmonic Stam `1/J(X+Y)≥1/J(X)+1/J(Y)` が正しい factor 込みで
   EPI を出す) であり **Mathlib 壁ではない** (EPI は真の定理)。同時に advisor の trivial shortcut でもない
   (case-A は機械 REFUTE 済)。→ **bounded だが genuine な再導出** (2 consumer lemma に集中、plumbing は機械的)。

5. **plumbing は機械的** (probe item f)。GS-A1'/A2' (v_Z field 追加 + `density_t_eq` carrier `t·v_Z`、
   `_entropy_eq`/`_fisher_match` を既存 general `pPath_eq_convDensityAdd` `FisherInfoV2DeBruijnPerTime.lean:215`
   経由で一般化、13-file consumer は X/Y `v_Z:=1` で carrier definitionally 回復) は機械的。非機械的部分は
   GS-A3' の 2 consumer lemma に局在。

**次手 = GS-A3' の最小 probe** (最初の1手): `csiszarLogRatioGap_hasDerivAt` の sum 項 lift を正しい factor
(sum=`J_sum`、component=`(1/2)·J`) で書き直し、`α²≤α` harmonic-Stam arith が補正 factor で ≤0 を保つかを
skeleton で機械確認。**plumbing (GS-A1'/A2') に投資する前に GS-A3' の解析核 tractability を確認** (risk 順序)。
通れば全体 closure 確実、通らねば weight 構造の調整が要る範囲を sizing。

## 現状要約 (handoff、2026-06-06 GS-A0 probe で case-A REFUTE 後)

> ⚠ 上の「## 確定状態」section が superseding 要約。本節はその詳細展開。

**現状 = case-A REFUTED (機械実証)。真の closure = factor-2 ratio-Stam 再導出 (GS-A3'、load-bearing
解析核、壁でない・trivial でない)。plumbing は機械的。** 直前 planner が `proof-pivot-advisor` の case-A
gate 判定を「CONDITIONAL-GO・ratio core 無改変再利用可」と書いたのは **誤り**だった。GS-A0 probe
(`proof-log-epi-case1-genvar-struct.md` §GS-A0 probe、6 `example` 型確認) が advisor の case-A shortcut を
**機械 REFUTE** した。

**advisor の取り違え (case-A が誤りだった根本原因)**: advisor は「`fisherInfoOfMeasureV2` が measure 引数を
無視するから `J_sum` は v_Z 不変、ratio core 無改変」と主張したが、これは **2 つの Fisher 関数の取り違え**:
- `fisherInfoOfMeasureV2 (_μ) f := fisherInfoOfDensity f` (`FisherInfoV2DeBruijn.lean:81`) — measure-keyed
  wrapper、**第1引数 (measure) を無視**。
- `fisherInfoOfDensityReal` — de Bruijn 微分値・ratio core が **実際に使う density-direct 関数**、
  **第2引数 (density 関数) が load-bearing**。
advisor は前者の「measure 無視」を後者に誤適用した。**誤読の元は stale docstring
`EPIStamToBridge.lean:892-893`** (削除済 D3 difference-gap context を参照し「3 Fisher rfl が成立するのは
`fisherInfoOfMeasureV2` が measure 引数を無視するから」と書くが、live ratio core
`csiszarLogRatioGap_deriv_le_zero` `:895` は density-direct `fisherInfoOfDensityReal` を使う)。

**機械実証 (probe verbatim)**:
1. **PROBE 1a**: `fisherInfoOfMeasureV2 μ f = fisherInfoOfDensity f` は `rfl` ✅ — measure 無視は real。
   **だが無視するのは第1引数 (measure)、density witness `f` (第2引数) は full load-bearing**。
2. **PROBE 1c (KEY)**: `convDensityAdd pX g_t = convDensityAdd pX g_{2t}` は **`rfl` 失敗**
   (carrier-t density ≠ carrier-2t density)。`gaussianConvolution_rescale_eq`
   (`EPICase1RatioLimit.lean:1765`) は **path 関数恒等式** (`X+√(t·v)·(Z/√v) = X+√t·Z`) で density 関数
   (`fisherInfoOfDensityReal` の引数) に **届かない**。→ carrier rescale 同定は Fisher 値レベルに **届かない**
   (案A の核 = carrier rescale 同定が機械 REFUTE)。
3. **PROBE 2**: `fisherInfoOfDensityReal (convDensityAdd pX g_t) = fisherInfoOfDensityReal (convDensityAdd pX g_{2t})`
   は `rfl`/`simp` で閉じない (2 引数が PROBE-1c の非 defeq density、Gaussian-conv 密度の Fisher 値は carrier に
   genuine 依存、`J(pX∗g_t)≤1/t`)。→ **`J_sum` v_Z 不変は機械 REFUTE**。
4. **PROBE 3b (make-or-break)**: v_sum=2 で sum 項 de Bruijn 微分 = `(2/2)·J_sum = J_sum`。consumer の
   hardcoded `2·` lift と衝突し `ring` が `eP·J_sum = eP·J_sum·2` (verbatim machine output) 矛盾に帰着。
   desync は ratio core ではなく **1 level 上の** `csiszarLogRatioGap_hasDerivAt` の `hN_sum` lift
   (`EPIStamToBridge.lean:790-803`) の hardcoded `(1/2)` cancellation に局在。

**真の作業 (GS-A3'、復活)**: 「Assembly 局所 carrier rescale 同定で ratio core 無改変再利用」(案A) **ではなく**、
**factor-2 ratio-Stam 再導出** = **2 consumer lemma を正しい factor で再導出**する (詳細 §確定状態 3):
- (a) `csiszarLogRatioGap_hasDerivAt` の `hN_*` entropy-power lift (`EPIStamToBridge.lean:766-803`) を
  per-term `v_i` factor (sum: `(v_sum/2)·J`、X/Y: `(1/2)·J`) で書き直す。
- (b) `csiszar_ratio_deriv_le_zero_arith` の harmonic-Stam `α²≤α` weights を factor-2 sum numerator で再導出。
これは **標準 de Bruijn EPI の真の数学** (壁でない、EPI は真の定理)、かつ advisor の trivial shortcut でもない
(case-A 機械 REFUTE)。**bounded だが genuine な再導出** (2 consumer lemma に集中)。

**`Z_law=unit` の false は load-bearing**: probe trace で `Z_law=unit` の false が consumer の **de Bruijn
微分値の factor** に load-bearing と確定 (false unit が sum 項を `(1/2)·J_sum` と誤らせる、真値は variance-2 で
`J_sum`)。case-A の「ratio core 無改変・`J_sum` v_Z 不変」は **PROBE 1c/2/3b で全て REFUTE**。

**次手 = GS-A3' の最小 probe** (最初の1手、risk 順序): `csiszarLogRatioGap_hasDerivAt` の sum 項 lift を
正しい factor (sum=`J_sum`、component=`(1/2)·J`) で書き直し、`α²≤α` harmonic-Stam arith が補正 factor で ≤0 を
保つかを skeleton で機械確認。**plumbing (GS-A1'/A2') に投資する前に GS-A3' の解析核 tractability を確認**。
通れば全体 closure 確実、通らねば weight 構造の調整が要る範囲を sizing。defect park (`Z_law` の
`@audit:defect(false-statement)` + `@audit:closed-by-successor(...)`、`EPICase1SumProducer.lean:166`) は本 wave
進行中**維持** (本 plan が closure owner、slug 正当、GS-A3' closure まで)。

## 進捗

- [x] Q-CORE 結線決着 (v_Z が de Bruijn 微分値→ratio core arith に到達するか実コード verbatim) — 本 plan 内で完了
- [x] ~~GS-0 在庫 (reparam ルート資産 verbatim 確認)~~ — GS-1 probe inventory で完了 (proof-log §Inventory) ✅
- [x] ~~GS-1 採用ルート確定 (B-τ vs b-2 vs c)~~ — 🔄 **B-τ/c REFUTED、b-2 が唯一 path に確定** (probe machine-verified、判断ログ 5/6/7) ✅
- [x] ~~GS-A0 `proof-pivot-advisor` gate (case-A CONDITIONAL-GO)~~ — 🔄 **case-A REFUTED (GS-A0 probe で機械実証)**: advisor の「ratio core 無改変・`J_sum` v_Z 不変」shortcut は `fisherInfoOfMeasureV2`/`fisherInfoOfDensityReal` 取り違えに基づく誤り、PROBE 1c/2/3b で REFUTE (判断ログ 8/9) ✅
- [x] ~~**GS-A3' (gate、load-bearing 解析核)**: factor-2 ratio-Stam 再導出~~ — ⛔ **REFUTED (2026-06-06 機械実証)**: factor-2 arith `2·J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y) ≤ 0` は harmonic Stam + positivity から FALSE (`ProbeGSA3.lean` counterexample、proof-log §GS-A3' probe)。欠けているのは weight でなく non-local co-monotonicity `(J_X−J_Y)(N_X·J_X−N_Y·J_Y)≥0`。全 single-t route blocked。GS-A1'〜A5' (plumbing/結線) は **着手中止** (gate 不通過) ✅
- [ ] GS-A1' `IsRegularDeBruijnHypV2` の `v_Z` field 追加 (`Z_law : gaussianReal 0 v_Z` + `density_t_eq` carrier `t·v_Z`)、13-file consumer の v_Z:=1 補完 breakage 実測 (plumbing、機械的見込み) 📋
- [ ] GS-A2' `_entropy_eq`/`_fisher_match` の general-variance 化 (`pPath_eq_convDensityAdd` general v_Z `FisherInfoV2DeBruijnPerTime.lean:215` 経由、plumbing、機械的) 📋
- [ ] GS-A4' sum producer `Z_law` defect→genuine (v_Z:=2 で `hZXZY_law` 直接)、他 field 再利用、残1 (integrable_deriv t-可測性) park との関係確定 📋
- [ ] GS-A5' PB-6 wrapper `_full` 結線 + GS-V verify (`lake env lean`) + 独立 honesty audit (`honesty-auditor`) PASS 📋
- ~~GS-A0' carrier rescale 同定 probe (案A、ratio core 無改変再利用前提)~~ — **削除** (PROBE 1c で carrier rescale が Fisher 値に届かないと機械 REFUTE、判断ログ 9) 🔄

---

## 文脈 (確定背景)

### 何が blocker か

case-1 EPI の解析核は完全 genuine (handoff)。残る headline blocker は
**sum noise `Z_X+Z_Y ∼ 𝒩(0,2)`** (独立標準正規 2 つの和、variance 2) を de Bruijn
regularity structure が受容できないこと。

sum producer (`EPICase1SumProducer.lean`) は他 field
(pX_sum series / density / `integrable_deriv` の bound 部) を genuine に埋めたが、
`reg_at .Z_law` field のみ `@audit:defect(false-statement)` で park 中。`Z_law` field は
unit-hardcode `P.map (Z_X+Z_Y) = gaussianReal 0 1` を要求し、真の law は
`gaussianReal 0 2` (`EPICase1SumProducer.lean:155-161` で `hZXZY_law` として導出)。
**`gaussianReal 0 1 ≠ gaussianReal 0 2`** なので、producer の真の (充足可能な) 仮説下で
`Z_law` obligation は **uninhabitable** (独立監査 2026-06-06 機械確認)。これは plan-residual
ではなく false-statement defect であり、本 plan が **structure 改変で genuine 化**する対象。

### 予測でなく実コードで確定済の事実 (前提とせよ)

1. **de Bruijn identity は `Z_law` の値を消費する** (Q-CORE 決着、§Q-CORE 詳細)。
   `debruijnIdentityV2_holds_assembled` (`FisherInfoV2DeBruijnAssembly.lean:3543`) は
   `_entropy_eq` (`:3437`) と `_fisher_match` (`:3485`) の 2 sub-lemma が
   `hZ_law : P.map Z = gaussianReal 0 1` を **hardcode 引数で取り**、内部で
   `pPath_eq_convDensityAdd ... (1 : ℝ≥0) ... hZ_law` (`:3452`) を呼んで「path
   `X+√s·Z` の真の density (variance carrier `s·v_Z`)」を「`_chain` (`:3397`) が解析する
   density (variance carrier `s`)」に同定する。**v_Z=1 だからこそ `s·v_Z = s` で carrier が
   一致**する (`:3460` `hwit1 : s·1 = s`)。
2. **`_chain` は density-level・v_Z-agnostic** (`:3397-3414`、`pX` のみ引数、noise 不参照、
   density carrier `s` を自前で持つ純解析)。残2 plan の「`_chain` が v_Z-agnostic」主張は **正しい**。
3. **しかし `Z_law` を `gaussianReal 0 2` に開くと carrier が drift する**:
   `_entropy_eq` の `pPath_eq_convDensityAdd` 呼出が `s·v_Z = s·2 ≠ s` を返し、path の真の
   density (carrier `s·2`) と `_chain` が消費する density (carrier `s`) が **一致しなくなる**。
   整合させるには general-variance 版 `_entropy_eq_genvar` を作るしかなく、そこで de Bruijn
   微分値が `(1/2)·J(convDensityAdd pX g_{s·v_Z})` (carrier `s·v_Z`) になり、fork-sizing
   `(v_Z/2)·J` 偽化と **同一機構** で ratio core を壊す。
4. **prior art `IsHeatFlowEndpointRegular` は ratio core を偽化していない理由**:
   この structure (`EPIG2HeatFlowContinuity.lean:488`、general `v_Z` field +
   `hZ_law : gaussianReal 0 v_Z`) は sum に `v_Z := 2` を渡して構成済
   (`EPIStamToBridge.lean:1447-1452`)。だが `csiszarLogRatioGap_antitoneOn_Ici_zero`
   (`EPIStamToBridge.lean:1085`) はこれを **端点連続性専用** (`heatFlowEntropyPower_continuousWithinAt_zero`、
   t=0⁺ への収束) としてのみ消費し、**Fisher 微分値 (ratio core arith) には到達させない**。
   ratio core が消費するのは `IsDeBruijnRegularityHyp` の `(h_reg_*.reg_at t ht).density_t` の
   Fisher 値 (`EPIStamToBridge.lean:712-721`) であって、`IsHeatFlowEndpointRegular` の v_Z は
   連続性 (値ではなく収束) にしか使われない。**両 structure が同一 consumer に共存できるのは、
   v_Z 一般を許す方 (`IsHeatFlowEndpointRegular`) が arith に到達しないから**。
   → `IsRegularDeBruijnHypV2` の v_Z 一般化は `IsHeatFlowEndpointRegular` の v_Z 一般化と
   **異なる** (前者は arith に到達、後者は到達しない)。prior art は v_Z 一般化が安全な証拠には
   **ならない** — 安全なのは「連続性 structure の v_Z」だけで「微分値 structure の v_Z」ではない。

### Q-CORE の結論 (本 plan の設計を決める)

**残2 plan の「Z_law を一般化しても微分値を触らず density を unit-W pin すれば偽化回避」は
`_entropy_eq` の hardcode `(1:ℝ≥0)` を見落としている**。`density_t` を unit-W 形に pin しても、
`_entropy_eq`/`_fisher_match` が `Z_law` の値で「path の真の density」を同定する以上、
`Z_law = gaussianReal 0 2` と「density_t が carrier `s` (unit-W)」は **型整合しない**
(path の真の density は carrier `s·2`、`_fisher_match` の `density_t_eq` 等式が `s` carrier の
convDensityAdd を要求するので矛盾)。

→ (起草時の結論) **正しい道は値一般化 (案A / b-2 naive) でも density-pin だけ (残2 plan) でもなく、
time-reparam で carrier を unit に戻すこと** (fork-sizing 案C / 案B+τ reparam)、本 plan のルート (B-τ)。

> **⚠ 2026-06-06 訂正 (判断ログ 5/6/7)**: この Q-CORE 起草時の B-τ 結論は GS-1 probe で **REFUTE**。
> time-reparam `τ=2t` は sum 項の de Bruijn 微分を X/Y 項から **desync** させ、antitone 証明の単一共有 t
> 結合を壊す (B-τ NO-GO)。Q-CORE が正しく示したのは「v_Z は ratio core arith に到達する」「density-pin
> だけでは救えない」までで、**救済策が reparam (B-τ) という結論が誤り**だった。variance-2 は coupling に
> intrinsic で回避不能 (§解析核判定 (i))、唯一の道は general-variance 正面受容 (b-2) + factor-2
> ratio-Stam 再導出。本節以降の B-τ 記述は歴史的経緯として残置 (§候補ルートで B-τ/c を取消線化済)。

---

## ゴール / Approach

### ゴール

sum producer `isDeBruijnRegularityHyp_sum_of_methodX_unitnoise`
(`EPICase1SumProducer.lean:88`) の `Z_law` field の `@audit:defect(false-statement)` park を
**genuine 化**し、`IsDeBruijnRegularityHyp (X+Y) (Z_X+Z_Y) P` を sum noise N(0,2) で本物に供給する。
これにより case-1 final wrapper `_full` (PB-6) が de Bruijn group を前提から消し、headline EPI
case-1 が proof done (残1 integrable_deriv t-可測性 closure と協調すれば
`[propext, Classical.choice, Quot.sound]`) に届く。

### Approach (全体形、2026-06-06 改訂 — route b-2 確定後)

**訂正の経緯**: 旧 Approach は route (B-τ) (unit-noise W + 時間 τ=2t reparam) を本命としていたが、
GS-1 probe (machine-verified) で **B-τ NO-GO** が確定した (判断ログ 5)。W 置換の reparam `τ=2t` が
sum 項の de Bruijn 微分 (carrier 2t) を X/Y 項 (time t) から **desync** させ、antitone 証明
`csiszarLogRatioGap_hasDerivAt` (`EPIStamToBridge.lean:699`) が要求する **単一共有 t** の 3 成分結合を
表現不能にする。wrapper-W 化 (route c) も antitone target `csiszarLogRatioGap`
(`EPIL3Integration.lean:1380`) が sum noise を `Z_X+Z_Y` + 単一 t で hardcode するため不可。
→ **唯一 surviving honest path = route (b-2) general-variance de Bruijn surgery**。

> **⚠ 2026-06-06 case-A REFUTE 後の確定 (判断ログ 8/9)**: 直前 planner が GS-A0 advisor gate を
> 「CONDITIONAL-GO・ratio core 無改変・Assembly 局所 carrier rescale 同定」(案A) と書いたが、これは
> **GS-A0 probe で機械 REFUTE**された (PROBE 1c/2/3b)。advisor の case-A は **`fisherInfoOfMeasureV2`
> (measure 無視、第1引数) と `fisherInfoOfDensityReal` (density-direct、第2引数 load-bearing) の取り違え**
> に基づく誤り (誤読の元は stale docstring `EPIStamToBridge.lean:892-893`、削除済 D3 context 参照)。
> de Bruijn 微分値・ratio core は density-direct `fisherInfoOfDensityReal` を density 関数に **直接** 適用し、
> `:81` の measure 無視は **この path に乗らない**。carrier rescale 同定 (`gaussianConvolution_rescale_eq`
> `:1765`) は **path 関数恒等式**で density 関数に届かず (PROBE 1c `rfl` 失敗)、`J_sum` v_Z 不変は機械 REFUTE
> (PROBE 2/3b)。→ **ratio core 無改変再利用は不可**、真の作業は **factor-2 ratio-Stam 再導出** (2 consumer
> lemma) に戻る。以下の核心は確定後の案 (GS-A3' を gate に置く)。

**核心 (確定)** = sum noise の variance 2 を **回避しようとせず** (B-τ/c はこれを試みて desync で失敗)、
de Bruijn structure を general-variance 化し、**2 consumer lemma の de Bruijn 微分値 factor を正しく再導出**する:
1. `IsRegularDeBruijnHypV2.Z_law` を `gaussianReal 0 v_Z` (+ `v_Z` field)、`density_t_eq` を carrier `t·v_Z`
   に開く (plumbing、GS-A1')。
2. `_entropy_eq`/`_fisher_match` を `pPath_eq_convDensityAdd` general v_Z (`FisherInfoV2DeBruijnPerTime.lean:215`、
   carrier `s·v_Z`) 経由で一般化 (plumbing、GS-A2')。
3. **load-bearing 解析核 (GS-A3'、最初に着手すべき gate)** = **factor-2 ratio-Stam 再導出**。2 consumer lemma:
   - (a) `csiszarLogRatioGap_hasDerivAt` の `hN_*` entropy-power lift (`EPIStamToBridge.lean:766-803`) を
     per-term factor (sum: `(v_sum/2)·J = J`、X/Y: `(1/2)·J`) で書き直す。現コードは sum 項も `(1/2)·J`
     hardcode で `2·` lift と cancel するが、variance-2 sum では真値 `J_sum` が `eP·J_sum·2` の spurious
     factor 2 を生み `ring` が落ちる (PROBE 3b)。
   - (b) `csiszar_ratio_deriv_le_zero_arith` の harmonic-Stam `α²≤α` weights を factor-2 sum numerator で再導出。
4. X/Y instance は v_Z:=1 補完で 13-file consumer site を patch (plumbing、carrier definitionally 回復)。

**何が genuine に閉じるか / 真の作業は何か**:
- de Bruijn identity の density-level core (`_chain`) は **v_Z-agnostic で既に genuine** (Q-CORE 事実 2)。
- **真の作業 = GS-A3' の 2 consumer lemma factor-2 再導出** (load-bearing 解析核)。これは **標準 de Bruijn
  EPI の真の数学** (sum 微分=`J`(variance 2)、component=`(1/2)·J`(unit)、harmonic Stam が正しい factor 込みで
  EPI を出す) であり **Mathlib 壁ではない** (EPI は真の定理)、同時に advisor の trivial shortcut でもない
  (case-A 機械 REFUTE)。**bounded だが genuine な再導出**。
- structure surgery (GS-A1'/A2'、v_Z field + Assembly v_Z 化) は **plumbing** (probe item f で機械的確認)、
  13-file consumer は機械的 v_Z:=1 補完で吸収される見込み。

**risk 順序 (最重要)**: 非機械的部分は **GS-A3' の 2 consumer lemma に局在** (probe item f 確認)。
**plumbing (GS-A1'/A2') に投資する前に GS-A3' の解析核 tractability を確認** — `csiszarLogRatioGap_hasDerivAt`
の sum 項 lift を正しい factor で書き直し、`α²≤α` harmonic-Stam arith が補正 factor で ≤0 を保つかを skeleton で
機械確認する (最初の1手)。通れば全体 closure 確実、通らねば weight 構造の調整が要る範囲を sizing。

**段階構成 (確定)**:
- **GS-A3'** (最初の1手、最初に着手すべき gate): factor-2 ratio-Stam 再導出 (load-bearing 解析核、2 consumer lemma)。
- **GS-A1'** structure surgery (v_Z field 追加、consumer breakage 実測、plumbing)。
- **GS-A2'** `_entropy_eq`/`_fisher_match` general-variance 化 (plumbing)。
- **GS-A4'** sum producer `Z_law` defect→genuine 差し替え (v_Z:=2) + 残1 park 整理。
- **GS-A5'** PB-6 wrapper 結線 + verify/監査。
- ~~案A GS-A0' carrier rescale 同定~~ — **削除** (PROBE 1c で機械 REFUTE)。

**撤退口**: GS-A3' の factor-2 再導出が現 weight 構造で閉じなければ → weight 構造の調整が要る範囲を sizing し、
当該 phase を `sorry` + `@residual(plan:epi-case1-debruijn-genvar-struct-plan)` で park (signature は本来証明
したい general-variance 形を保つ、honest tier-2 residual)。これは **bounded な weight 再設計** であって別 route
ではない (variance-2 受容は唯一の path、§解析核判定 (i))。`*Hypothesis` predicate に核を bundling する撤退は
禁止 (CLAUDE.md「検証の誠実性」)。defect park 恒久化 (案D) は **非推奨** (解析核は wall でなく標準 EPI 数学)。

---

## Q-CORE 詳細 — v_Z が ratio core arith に到達するか (実コード結線、本 plan の価値の中心)

### (1) `IsRegularDeBruijnHypV2` の各 field の v_Z 依存 (verbatim、`FisherInfoV2DeBruijn.lean:205-268`)

| field | 型 | v_Z 依存 |
|---|---|---|
| `Z_law` | `P.map Z = gaussianReal 0 1` (`:210`) | **unit hardcode** (v_Z=1 固定) |
| `density_t` | `ℝ → ℝ` (`:212`) | 値は構成側が決める (carrier は `density_t_eq` で pin) |
| `pX` series (`pX`/`pX_nn`/`pX_meas`/`pX_law`) (`:227-234`) | X 自身の Lebesgue 密度 witness | v_Z 非依存 (noise 不参照) |
| `density_t_eq` | `density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x` (`:260-261`) | **carrier `t` hardcode** (v_Z=1 を前提に `s·1=s` で carrier=t) |
| `pX_mom` | `Integrable (y²·pX)` (`:268`) | v_Z 非依存 |

**結論**: `Z_law` と `density_t_eq` の **2 field が v_Z=1 を hardcode**。`density_t_eq` の RHS は
`gaussianPDFReal 0 ⟨t,_⟩` (carrier `t`)。これは「path `X+√t·Z` の真の density は carrier `t·v_Z`」と
**v_Z=1 のときだけ一致**する。

### (2) de Bruijn identity (`_chain`/`_entropy_eq`/`_fisher_match`) の v_Z 結線

- **`_chain`** (`FisherInfoV2DeBruijnAssembly.lean:3397-3414`): 引数は `pX` 系のみ、**noise 不参照**。
  結論の density carrier は `gaussianPDFReal 0 ⟨max s 0,_⟩` (= variance `s`、自前)。**v_Z-agnostic**。
- **`_entropy_eq`** (`:3437-3473`): `hZ_law : P.map Z = gaussianReal 0 1` を **hardcode 引数で取り**
  (`:3440`)、内部 `pPath_eq_convDensityAdd X Z ... (1 : ℝ≥0) one_pos hZ_law ...` (`:3452`) で
  path の真の density を carrier `s·1 = s` に同定 (`:3460-3462` `hwit1`)。**v_Z=1 hardcode**。
- **`_fisher_match`** (`:3485-3500`): `_hZ_law : gaussianReal 0 1` を取る (`:3488`、underscore)。
  `density_t_eq` の carrier `⟨t, ht.le⟩` (= `t`) で `density_t` を convDensityAdd と同定。**v_Z=1 hardcode**。
- **`_assembled`** (`:3543-3587`): 上記 3 つを `h_reg.Z_law` (= unit) で叩いて
  `(1/2)·fisherInfoOfDensityReal h_reg.density_t` を返す。

`pPath_eq_convDensityAdd` 自身 (`FisherInfoV2DeBruijnPerTime.lean:215-224`) は **general v_Z 受容**
(`v_Z : ℝ≥0` 引数、結論 density carrier `s·v_Z`)。だが `_entropy_eq` が **v_Z:=1 を hardcode で
instantiate** しているため、`_assembled` 全体は v_Z=1 でしか genuine に組まない。

### (3) consumer が何の微分値を見るか (ratio core への到達、`EPIStamToBridge.lean:699-838`)

`csiszarLogRatioGap_hasDerivAt` (`:699`) は X/Y/sum 3 成分で `deBruijn_identity_v2` を呼び
(`:730/738/747`)、各 `(1/2)·J((h_reg_*.reg_at t ht).density_t)` を得る (`:728/736/745`)。lift で
`2·(1/2)=1` で `(1/2)` が一律 cancel (`:773/785/799`)、ratio-gap 微分値は
`J_sum − (N_X·J_X+N_Y·J_Y)/(N_X+N_Y)` (`:712-721`)。`csiszarLogRatioGap_deriv_le_zero` (`:895`) が
plain harmonic Stam から ≤0 を出す (`:843-848`、weights `α²≤α`)。

**到達結線**: ratio core arith が消費するのは `density_t` の **Fisher 値**。`density_t` の値は
`density_t_eq` (carrier `t·v_Z`) と `_fisher_match` で決まる。よって **`Z_law` の v_Z は
`_entropy_eq`/`density_t_eq` の carrier 経由で `density_t` の Fisher 値を決め、ratio core arith に
到達する**。v_Z≠1 にすると carrier が `t·v_Z` に drift し、`J(convDensityAdd pX g_{t·v_Z})` が
各成分で非一律 factor を持ち、harmonic Stam (項毎 factor 非不変) を偽化する (fork-sizing Q1)。

→ **Q-CORE 答え: v_Z は ratio core arith に到達する**。残2 plan の「微分値を触らず density-pin で
偽化回避」は不可 (`_entropy_eq` hardcode が `Z_law` 値と density carrier を結びつけている)。
~~唯一の道は path/time の reparam で carrier を unit に戻すこと (ルート B-τ)~~ — **2026-06-06 訂正: この
reparam (B-τ) 結論は probe で REFUTE (上記 ⚠ 注 / 判断ログ 5)。v_Z が arith 到達するのは正しいが、
救済は reparam でなく general-variance 正面受容 (b-2) + factor-2 ratio-Stam 再導出**。

### prior art の機械検証 — 共存が v_Z 安全の証拠にならない理由

`IsHeatFlowEndpointRegular` (general v_Z) と `IsDeBruijnRegularityHyp` (unit、ratio core 経由) は
`csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085-1098`) で **同時に受け取られ、
sum は前者に v_Z=2 を渡して共存**している (`:1447-1452`)。だがこの共存は v_Z 一般化が「安全」な
証拠に **ならない**: `IsHeatFlowEndpointRegular` の v_Z は **端点連続性専用**
(`heatFlowEntropyPower_continuousWithinAt_zero`、収束) で **ratio core arith (Fisher 微分値) に
到達しない**。一方 `IsDeBruijnRegularityHyp` の v_Z は (3) のとおり arith に到達する。
2 structure の v_Z は **役割が別** (連続性 vs 微分値) なので、前者の v_Z=2 共存は後者の v_Z 一般化を
正当化しない。残2 plan の M0' 観察 (prior art = ルート b 根拠) は **この役割差を見落としている**。

---

## 解析核判定 — variance-2 intrinsic + factor-2 ratio-Stam の真偽 (本 plan の中心価値、次 session risk 順序を規定)

### (i) variance-2 は proof に intrinsic (回避不能、実コード verbatim 裏取り)

標準 de Bruijn EPI の coupling
`(X+Y)+√t·(Z_X+Z_Y) = (X+√t·Z_X)+(Y+√t·Z_Y) = X_t+Y_t` が成立するには、sum noise が
**必ず `Z_X+Z_Y` (variance 2)** でなければならない。fresh unit `Z_S ∼ 𝒩(0,1)` を sum 項に使うと
この coupling が壊れ、X_t と Y_t の Fisher 比較 (ratio-Stam) ができない。

**実コード裏取り** (verbatim):
- `csiszarLogRatioGap` (`EPIL3Integration.lean:1382`) の sum path は
  `fun ω => X ω + Y ω + Real.sqrt t * (Z_X ω + Z_Y ω)` — sum noise が **literal に `Z_X+Z_Y`**
  (variance 2)、X/Y path は `X+√t·Z_X` / `Y+√t·Z_Y` で **同一の単一 t**。これが coupling
  `X_t+Y_t` そのもの。
- `csiszarLogRatioGap_deriv_le_zero` の `h_conv_id` (`EPIStamToBridge.lean:919-922`) は sum density
  `(h_reg_sum.reg_at t ht).density_t` を **carrier-t の X-density と Y-density の `convDensityAdd`** に
  同定する: `density_t x = convDensityAdd ((h_reg_X.reg_at t ht).density_t) ((h_reg_Y.reg_at t ht).density_t) x`。
  carrier-t の 2 密度の convolution は **carrier-2t** — これは coupling
  `(X+√t·Z_X)+(Y+√t·Z_Y)` の density で、sum noise が `Z_X+Z_Y` (variance 2) でなければ成立しない。

→ **variance-2 は回避不能**。だからこそ B-τ/c (variance-2 を unit W に置換して回避しようとする route)
が desync で失敗した (W は coupling を壊す)。**variance-2 を正面から受容する general-variance
structure (b-2) が本質的に必要**。

### (ii) 解析核は wall か — GS-A0 probe で case-A REFUTE、factor-2 再導出が真の load-bearing core (2026-06-06 確定)

> **⚠ case-A REFUTE 後 (判断ログ 9)**: 直前 planner は本節を「factor-2 ratio-Stam 新規再導出は過大評価、
> ratio core 無改変再利用可」(案A) と framing したが、**GS-A0 probe で機械 REFUTE**された。advisor の
> 「`fisherInfoOfMeasureV2` measure 無視 ⟹ `J_sum` v_Z 不変」は **`fisherInfoOfMeasureV2` (第1引数=measure
> 無視) と `fisherInfoOfDensityReal` (de Bruijn 微分・ratio core が使う density-direct、第2引数 load-bearing)
> の取り違え**で誤り (誤読の元は stale docstring `EPIStamToBridge.lean:892-893`、削除済 D3 context 参照)。
> de Bruijn 微分値は `fisherInfoOfDensityReal` を density 関数に直接適用し (`:81` measure 無視は path 外)、
> carrier rescale (`gaussianConvolution_rescale_eq` `:1765`) は path 関数恒等式で density に届かず
> (PROBE 1c `rfl` 失敗)、`J_sum` v_Z 不変は機械 REFUTE (PROBE 2/3b)。→ **真の load-bearing 解析核は
> factor-2 ratio-Stam 再導出** (2 consumer lemma) に戻る。以下は wall か tractable かの判定。fork-sizing
> (a)/(b) 切り分けは引き続き load-bearing。

**factor-2 ratio-Stam bound の再導出 (GS-A3')** が真の load-bearing 解析核。これが「真の EPI 数学
(genuine 証明可能)」か「wall」かの区別が次 session の risk 順序を決める。**結論: naive 値据置一般化と正しい
factor 再導出は別物で、後者は真であるはず (EPI は真の定理)、ただし genuine 証明を要する**。
**壁でない (標準 EPI 数学)、同時に advisor の trivial shortcut でもない (case-A 機械 REFUTE)** → bounded だが
genuine な再導出 (2 consumer lemma に集中)。下記 fork-sizing (a)/(b) 切り分けが load-bearing。

**fork-sizing の偽化主張がどちらを指すか — 実コード verbatim 再確認**:
fork-sizing doc (`epi-case1-debruijn-producer-fork-sizing.md` Q1、`:32-40`) は「案A-corrected =
値据置で `(1/2)·J_i → (v_Z_i/2)·J_i` に変える」と各成分に **非一律 factor** (X→v_X, Y→v_Y,
sum→v_X+v_Y、v_X≠v_Y) が乗り、`csiszarLogRatioGap_deriv_le_zero` (`EPIStamToBridge.lean:895`) の
arith core (`csiszar_ratio_deriv_le_zero_arith`、α²≤α weights) が **破れる**と判定した。

**この偽化主張が指すのは「naive 値据置一般化」**: fork-sizing は `(1/2)·J` の値をそのまま
`(v_Z/2)·J` に **据え置き換える**だけで、ratio core の **harmonic-Stam weights を再導出しない**場合を
評価している。現コード `csiszarLogRatioGap_deriv_le_zero` (`EPIStamToBridge.lean:895`) は全成分 unit
(`(1/2)·J`) 前提の harmonic-Stam (`h_blachman : IsBlachmanConvReady`、`α²≤α` weights) で、これに
factor だけ後付けすると weight が合わず偽になる、というのが fork-sizing Q1。

**b-2 が指すのは「正しい factor で再導出した harmonic-Stam」**: sum 項が variance-2 noise
(`d/dt h((X+Y)+√t·(Z_X+Z_Y))` で carrier `t·2`) のとき、**正しい微分値**は `(2/2)·J_sum = J_sum`
(carrier scale 2)。これを weight に正しく織り込んで harmonic-Stam を再構成すれば、得られるのは
**真の EPI の Stam 不等式** (`1/J(X+Y) ≥ 1/J(X)+1/J(Y)` 系、Blachman score-of-convolution) であり、
**EPI は真の定理なので真であるはず**。fork-sizing が偽化したのは「値据置のまま weight 据置」した naive
版であって、「正しい factor で weight ごと再導出」した版ではない。

**fork-sizing (a)/(b) 切り分け (load-bearing、advisor の偽化主張の正しい読み)**:
- fork-sizing Q1 (`epi-case1-debruijn-producer-fork-sizing.md:32-40`) が偽化を主張したのは
  **(a) 値据置 naive 化** (`(1/2)·J_i → (v_Z_i/2)·J_i` と値を据置換え) で非一律 factor が残り
  `α²≤α` weight が破れる場合。
- fork-sizing は **(b)「正しい factor の再導出が wall」とは言っていない**。
- (a)/(b) 切り分けの示すこと: **(a) naive 値据置は偽 (weight が破れる)**、**(b) 正しい factor で weight
  ごと再導出すれば真** (= 真の EPI Stam 不等式、genuine 証明可能)。これが GS-A3' の作業内容。

**判定の一言 (case-A REFUTE 後の確定、2026-06-06)**:
- **factor-2 再導出が必要** — case-A の「ratio core 無改変」は PROBE 1c/2/3b で機械 REFUTE。consumer の
  `hN_sum` lift (`:790-803`) は sum 項を `(1/2)·J_sum` で hardcode し `2·` lift と cancel するが、
  variance-2 sum の真値 `J_sum` は `eP·J_sum·2` の spurious factor 2 を生み `ring` が落ちる (PROBE 3b)。
- **真の作業 = 2 consumer lemma の factor-2 再導出** (`hN_*` lift `:766-803` + `α²≤α` arith)。これは
  Assembly 局所の carrier rescale 同定 (案A、PROBE 1c で REFUTE) **では閉じない**。

**risk 順序 (next session GATE)**: 非機械的部分は **GS-A3' の 2 consumer lemma に局在** (probe item f)。
これを **最初の1手**に置き、`csiszarLogRatioGap_hasDerivAt` の sum 項 lift を正しい factor で書き直し
`α²≤α` arith が ≤0 を保つか skeleton で機械確認する。**plumbing (GS-A1'/A2') に投資する前に GS-A3' の
tractability を確認**。通れば全体 closure 確実、通らねば weight 構造の調整が要る範囲を sizing (bounded、
別 route でない)。defect park 恒久化 (案D) は **非推奨** (解析核は wall でなく標準 EPI 数学)。

## 候補ルートの列挙と sizing (2026-06-06 改訂 — B-τ/c REFUTED 後)

### ~~ルート (B-τ) — unit-noise W + 時間 reparam τ=t·v_Z~~ — **REFUTED (GS-1 probe machine-verified)**

**REFUTE 理由** (probe item 4d、`proof-log-epi-case1-genvar-struct.md` §Machine-verified):
W 置換に必要な reparam `τ = 2t` が、sum path `X+Y+√t·(Z_X+Z_Y)` を W-path の time `2t`
(`X+Y+√(2t)·W`) として再表現する。その de Bruijn 微分は `h_reg_W.reg_at (2t)` に座り、
`(1/2)·J(density_t @ 2t)` を **time 2t で評価**する。一方 X/Y 項の微分は time t (`h_reg.reg_at t`)。
antitone 証明 `csiszarLogRatioGap_hasDerivAt` (`EPIStamToBridge.lean:699`) は **3 成分すべてを単一
共有 t** で取るため、sum だけ別 time (2t) にできない (**desync**)。W-producer の `reg_at-at-2t` を
shared-t 結合に入れるには consumer の `(1/2)·J` arithmetic が持たない `2·` chain factor が要る。
probe item 4d がこの desync を型レベルで確認。

**producer 側は genuine だった**: W-law `P.map ((Z_X+Z_Y)/√2) = gaussianReal 0 1` は
`gaussianReal_add_gaussianReal_of_indepFun` → `gaussianReal_map_div_const` で ~15 行で閉じる
(probe item 1)、W-producer も clean に構成 (item 2)、`reg_at .Z_law` obligation も W で genuine 充足
(item 3a)。だが **consumer 側が W を受容できない** (item 4d desync) ため producer が genuine でも全体が
通らない。**`Z_law=unit` の false は consumer の微分 arithmetic に load-bearing** (probe で
`EPIStamToBridge.lean:747` → `debruijnIdentityV2_holds_assembled` が false unit `Z_law` を消費して
variance-2 sum 項の `(1/2)` factor を得ると trace 確定)。W はこの false を time-desync に移すだけで
除去しない。

### ~~ルート (c) — wrapper を unit-noise W で restate~~ — **不可 (antitone object の単一-t signature で表現不能)**

**不可理由** (probe Blast radius 節): antitone target `csiszarLogRatioGap`
(`EPIL3Integration.lean:1380`) は sum noise を `Z_X+Z_Y` + 単一 t で **hardcode**。W 化は sum 項に
別 time (2t) を要求するが、`csiszarLogRatioGap` の単一-t signature では「sum 項だけ別 time」を表現
できない。mechanical noise rename でなく、antitone object の **時間変数 restructuring** (sum path の
time を X/Y path から分離) が必要で、これは ~93 sum-path sites (3 consumer file + endpoint lemmas
+ saturation pillar) に伝播する。**tractable な wrapper rename ではない**。

### ルート (b-2) — `IsRegularDeBruijnHypV2` general-variance surgery — **唯一 surviving honest path** ✓

**内容**: §Approach 核心 (b-2) のとおり。`Z_law` を `gaussianReal 0 v_Z` (+ v_Z field) に開き、
`density_t_eq` の carrier を `⟨t·v_Z,_⟩` に開き、`_entropy_eq`/`_fisher_match` を
`pPath_eq_convDensityAdd` general v_Z 経由で一般化し、**factor-2 ratio-Stam を sum 項込みで再導出**。
X/Y instance は v_Z:=1 補完。

**B-τ/c との違い**: B-τ/c は variance-2 を unit W に **置換して回避**しようとして desync で失敗した。
b-2 は variance-2 を **回避せず正面から受容**する (general-variance structure)。§解析核判定 (i) のとおり
variance-2 は coupling に intrinsic なので、回避は原理的に不可能、受容が唯一の道。

**解析核 (case-A REFUTE 後の確定)**: load-bearing 解析核 = **factor-2 ratio-Stam 再導出** (2 consumer
lemma)。直前 planner の案A「ratio core 無改変再利用・Assembly 局所 carrier rescale 同定」は GS-A0 probe で
機械 REFUTE (PROBE 1c carrier rescale が density に届かず / PROBE 2/3b `J_sum` v_Z 不変が偽、判断ログ 9)。
真の作業は `csiszarLogRatioGap_hasDerivAt` の `hN_*` lift (`:766-803`) + `α²≤α` arith を正しい factor で
再導出する (壁でない・trivial でない標準 EPI 数学)。

**blast radius (実測済、`EPICase1SumProducer.lean:18` header / proof-log §What genuine closure)**:
`IsRegularDeBruijnHypV2` consumer = **13 file / 50+ 件** (`rg -c IsRegularDeBruijnHypV2`)。
`Z_law` + `density_t_eq` の carrier を general-variance 化すると全 consumer に v_Z:=1 補完 patch が
要る。consumer patch が機械的に済むか各証明が carrier `t` に load-bearing 依存して書換要かは GS-A1 で
`lake env lean` 実測 (撤退ライン L-GS-blast)。

**prior art `pPath_eq_convDensityAdd`**: general v_Z 版 (`FisherInfoV2DeBruijnPerTime.lean:215`、
`(v_Z:ℝ≥0)` 引数、carrier `s·v_Z`) が **既に in-tree** — これが b-2 の唯一の real asset
(GS-A2 で `_entropy_eq`/`_fisher_match` から呼ぶ)。`IsHeatFlowEndpointRegular` の general-v_Z 共存は
**役割別** (端点連続性専用で arith 非到達、Q-CORE prior art 節) なので b-2 の安全証拠にはならない。

### ルート比較表 (改訂後)

| 観点 | (b-2) genvar surgery ✓ | ~~(B-τ) W + τ reparam~~ REFUTED | ~~(c) wrapper-W~~ 不可 |
|---|---|---|---|
| 状態 | **唯一 surviving honest path** | **REFUTED** (probe item 4d desync) | **不可** (単一-t signature) |
| variance-2 の扱い | **正面受容** (general-variance) | unit W に置換 (回避) → desync | unit W に置換 → 単一-t 不能 |
| `Z_law` 型整合 | carrier `t·v_Z` で一般化、genuine | W で genuine だが consumer 不受容 | — |
| ratio core | **factor-2 再導出が必要** (`hN_*` lift `:766-803` + `α²≤α` arith、案A 無改変再利用は PROBE 1c/2/3b で REFUTE) | reparam で carrier 2t、desync | sum 項別 time、表現不能 |
| structure 改変 | `Z_law` general-var (plumbing) + 2 consumer lemma factor-2 再導出 (解析核) | なし (producer 側のみ) | なし |
| 影響範囲 | 13 file consumer (plumbing 機械的 v_Z:=1 補完) + 2 consumer lemma (解析核局在) | producer ~15 行だが consumer 不受容 | ~93 sum-path sites の time 再構成 |
| de Bruijn core | `_entropy_eq`/`_fisher_match` v_Z 化 (plumbing) + `hN_*` factor-2 再導出 (解析核) | `_assembled` 無改変だが消費不能 | — |
| prior art | `pPath_eq_convDensityAdd` general v_Z `:215` (plumbing 基盤、in-tree) | PB-2 path-id (item 4d で desync 露呈) | — |
| 推奨 | **唯一 path** | 廃止 | 廃止 |

**推奨 = (b-2、確定)**: variance-2 が coupling に intrinsic (§解析核判定 (i)) なので回避不能、
general-variance 受容が唯一の道。**case-A REFUTE 後**: 解析核 = factor-2 ratio-Stam 再導出 (2 consumer
lemma、壁でない標準 EPI 数学)。案A の「ratio core 無改変再利用・carrier rescale 同定」は GS-A0 probe で機械
REFUTE (PROBE 1c/2/3b)。次手は GS-A3' の最小 probe (sum 項 lift factor-2 書き直し + arith ≤0 機械確認、
plumbing に投資する前)。

---

## Phase 詳細 (2026-06-06 改訂 — route b-2、case-A REFUTE 後の確定、GS-A3' を gate に置く)

> 旧 GS-0〜GS-V (B-τ 前提) は probe で REFUTE。GS-A0 advisor gate の case-A (CONDITIONAL-GO・ratio core
> 無改変・carrier rescale 同定) は **GS-A0 probe で機械 REFUTE** (PROBE 1c/2/3b、判断ログ 9)。案A の GS-A0'
> (carrier rescale 同定 probe) は **削除**。真の load-bearing 解析核 = **factor-2 ratio-Stam 再導出**
> (2 consumer lemma) を **GS-A3' として最初の gate** に置く。phase 順: **GS-A3' (gate、解析核)** → A1'
> (v_Z field plumbing) → A2' (Assembly v_Z 化 plumbing) → A4' (sum producer Z_law genuine) → A5' (wrapper
> 結線 + verify/監査)。

### ~~GS-A0 — `proof-pivot-advisor` gate / GS-A0' carrier rescale 同定 probe (案A)~~ — 🔄 **case-A REFUTED (GS-A0 probe 機械実証)**

advisor の case-A gate (CONDITIONAL-GO、ratio core 無改変・`J_sum` v_Z 不変・carrier rescale 同定) は
**GS-A0 probe で機械 REFUTE** された (判断ログ 9、`proof-log-epi-case1-genvar-struct.md` §GS-A0 probe)。
advisor の取り違え = **`fisherInfoOfMeasureV2` (measure 無視、第1引数、`FisherInfoV2DeBruijn.lean:81`) と
`fisherInfoOfDensityReal` (de Bruijn 微分・ratio core が使う density-direct、第2引数 load-bearing) の混同**
(誤読の元は stale docstring `EPIStamToBridge.lean:892-893`、削除済 D3 context 参照)。機械実証:
- **PROBE 1c**: `convDensityAdd pX g_t = convDensityAdd pX g_{2t}` は `rfl` 失敗。carrier rescale
  (`gaussianConvolution_rescale_eq` `:1765`) は path 関数恒等式で density に届かない。
- **PROBE 2/3b**: `J_sum` v_Z 不変は偽 (Gaussian-conv 密度の Fisher 値は carrier 依存、v_sum=2 で `2·` lift と
  cancel せず `eP·J_sum·2` の spurious factor 2、`ring` 落ち)。
→ **ratio core 無改変再利用は不可、carrier rescale 同定 (案A GS-A0') は機械 REFUTE**。真の作業は
factor-2 ratio-Stam 再導出 (GS-A3')。L-GS-A0-wall (壁送り) は依然 **発動 NO** (factor-2 再導出は標準 EPI
数学、壁でない)。

### GS-A3' — factor-2 ratio-Stam 再導出 (最初に着手すべき gate、load-bearing 解析核)

**スコープ (最初の1手、risk 順序)**: plumbing (GS-A1'/A2'、13-file surgery) に投資する前に、load-bearing
解析核 = **factor-2 ratio-Stam 再導出**が現 weight 構造で閉じるかを最小 probe する。非機械的部分はこの
2 consumer lemma に局在 (probe item f)。

**2 consumer lemma (正しい factor で再導出)**:
- **(a) `csiszarLogRatioGap_hasDerivAt` の `hN_*` entropy-power lift** (`EPIStamToBridge.lean:766-803`)。現コードは
  X/Y/sum 全成分を `(1/2)·J` hardcode (`h_val` の `2 * ((1/2) * J)` 形、`:771/784/799`) で `2·` lift と
  `(1/2)` cancel するが、variance-2 sum 項は de Bruijn 微分の真値が `(v_sum/2)·J_sum = (2/2)·J_sum = J_sum`
  になり `2·` lift で `eP·J_sum·2` の spurious factor 2 を生む (PROBE 3b)。`hN_sum` の `h_val` を per-term
  factor (sum: `(v_sum/2)·J`、X/Y: `(1/2)·J`) で書き直す。
- **(b) `csiszar_ratio_deriv_le_zero_arith` の `α²≤α` harmonic-Stam weights** (`csiszarLogRatioGap_deriv_le_zero`
  `:895` が呼ぶ arith core、`:843-848` 付近)。sum numerator が factor-2 (variance-2 で sum 項 `J_sum`、X/Y は
  unit `(1/2)·J`) になったとき harmonic Stam `1/J(X+Y) ≥ 1/J(X)+1/J(Y)` が補正 factor 込みで ≤0 を保つか再導出。

**最小 probe (最初の1手)**:
- [ ] `csiszarLogRatioGap_hasDerivAt` の sum 項 lift (`hN_sum` `:790-803`) を正しい factor (sum=`J_sum`、
  component=`(1/2)·J`) で書き直した skeleton を作り、`ring` が通るか型確認 (現コードの `2 * ((1/2) * J_sum)` を
  variance-2 真値に合わせる)
- [ ] `csiszar_ratio_deriv_le_zero_arith` (`α²≤α` weights) が factor-2 sum numerator で ≤0 を保つか
  skeleton で機械確認 (`nlinarith`/`α²≤α` weight 再導出)
- [ ] 通れば 2 consumer lemma の factor-2 再導出が tractable と確定 → GS-A1' (plumbing) に進む

**Done 条件 / 分岐**:
- **通る (factor-2 で arith ≤0 を保つ)** → 解析核 tractable 確定、GS-A1' に進む。全体 closure 確実。
- **通らない** → weight 構造の調整が要る範囲を sizing。当該 phase を `sorry` +
  `@residual(plan:epi-case1-debruijn-genvar-struct-plan)` で park (signature は本来の general-variance 形を
  保つ、honest tier-2)。これは **bounded な weight 再設計** であって別 route ではない (L-GS-A2'-rescale →
  L-GS-A3'-weight、撤退ライン参照)。**`*Hypothesis` predicate に核を bundling する撤退は禁止**。判断ログに記録。

### GS-A1' — `IsRegularDeBruijnHypV2` に `v_Z` field 追加 (plumbing)

**スコープ** (GS-A3' gate 通過後): `IsRegularDeBruijnHypV2` (`FisherInfoV2DeBruijn.lean:205-268`) に
`v_Z` field を追加し、`Z_law` を `gaussianReal 0 v_Z` (`:210` の unit hardcode を開く)、`density_t_eq` を
carrier `t·v_Z` に開く (`:260-261`)。13-file consumer site の v_Z:=1 補完 breakage を実測 (plumbing、機械的
見込み — probe item f で `pPath_eq_convDensityAdd` general v_Z 既存 + X/Y `v_Z:=1` carrier definitionally
回復を確認済)。

- [ ] skeleton: `v_Z` field 追加 + `Z_law : gaussianReal 0 v_Z` + `density_t_eq` carrier `t·v_Z` 一般化
  (`:= by sorry` で型枠)
- [ ] 13 file consumer (`rg -c IsRegularDeBruijnHypV2`) の v_Z:=1 補完 breakage を `lake env lean` で実測
  — 機械的補完 (X/Y instance に `v_Z := 1`、`s·1=s` simp で carrier 回復) で通るか per-file 記録
- [ ] consumer patch (v_Z:=1 補完) を機械的に適用、breakage が機械的補完で吸収される範囲を確定

**撤退ライン (L-GS-blast)**: consumer breakage が想定 (13 file、機械的見込み) を **大幅に**超え各証明が
load-bearing 依存で書換要 → surgery を分割するか、structure 拡張でなく **新 general-variance structure を
別途定義** (新旧並存) する route に escalate (判断ログに記録)。probe item f で「13-file consumer は機械的
v_Z:=1 補完で吸収」見込みなので大幅超過の懸念は **低い**。

**Done 条件**: structure 一般化 type-check done、consumer breakage が v_Z:=1 補完で吸収される範囲を確定。

### GS-A2' — `_entropy_eq`/`_fisher_match` の general-variance 化 (plumbing)

**スコープ**: `debruijnIdentityV2_holds_assembled_entropy_eq` (`FisherInfoV2DeBruijnAssembly.lean:3437`、
`hZ_law : gaussianReal 0 1` hardcode + 内部 `pPath_eq_convDensityAdd ... (1:ℝ≥0) ...` `:3452`) と
`_fisher_match` (`:3485`) を `pPath_eq_convDensityAdd` general v_Z (`FisherInfoV2DeBruijnPerTime.lean:215`、
carrier `s·v_Z`) 経由で一般化する。これにより de Bruijn 微分値が `(v_Z/2)·J(convDensityAdd pX g_{s·v_Z})`
となり (carrier `s·v_Z`)、その factor が GS-A3' で再導出した 2 consumer lemma に正しく流れる。**これは
plumbing** (`pPath_eq_convDensityAdd` general v_Z は既存 in-tree、`:3452` の `(1:ℝ≥0)` を `v_Z` に開くだけ)。

- [ ] `_entropy_eq` general-variance 版: `:3452` の `pPath_eq_convDensityAdd ... (1:ℝ≥0) ...` を `... v_Z ...`
  に開き、path 真の density を carrier `s·v_Z` で取り出す (`hwit1 : s·v_Z` に一般化)
- [ ] `_fisher_match` general-variance 版: `density_t_eq` carrier `t·v_Z` (GS-A1') で `density_t` を
  convDensityAdd と同定 (`:3485-3500`)
- [ ] `_chain` (`:3397-3414`、v_Z-agnostic、無改変) との結線確認 (`_chain` は noise 不参照、Q-CORE 事実 2)
- [ ] `debruijnIdentityV2_holds_assembled` (`:3543`) が general-variance 3 sub を組み、de Bruijn 微分値の
  per-term factor (sum: `(v_sum/2)·J`、X/Y: `(1/2)·J`) が GS-A3' の `hN_*` lift に正しく流れることを確認、
  X/Y consumer は v_Z=1 で従来形に縮退
- [ ] **GS-A3' の `hN_*` lift / arith が GS-A1'/A2' の general-variance 微分値を消費して genuine に閉じる**
  ことを確認 (GS-A3' gate が通っていれば結線は機械的)

**Done 条件**: de Bruijn identity が general v_Z で type-check done、de Bruijn 微分値の per-term factor が
GS-A3' の 2 consumer lemma に流れる、X/Y は v_Z=1 で従来形に縮退。

### GS-A4' — sum producer `Z_law` defect→genuine 差し替え + 残1 park 整理

**スコープ**: GS-A3'/A1'/A2' で general-variance de Bruijn + factor-2 ratio-Stam が genuine になったら、
sum producer
`isDeBruijnRegularityHyp_sum_of_methodX_unitnoise` (`EPICase1SumProducer.lean:88`) の `Z_law` field
park (`:151-168`、`@audit:defect(false-statement)`) を genuine に差し替え (sum noise `Z_X+Z_Y` の
真の law `gaussianReal 0 2` を v_Z=2 field で受容、§解析核判定 (i) のとおり variance-2 を正面受容)。

**最小コスト経路 (auditor 指摘踏襲)**: sum producer の他 field (pX_sum series `:110-148` / density
`:137-148` / `density_t_eq` `:169-174` / `integrable_deriv` bound `:175-219`) は **genuine で保持
価値あり**。本 plan は `Z_law` field を defect park から genuine に差し替え + v_Z field 充足、他 field
は無改変再利用。

- [ ] sum producer 返り値を general-variance structure (v_Z:=2) に整合させ、`Z_law` を
  `P.map (Z_X+Z_Y) = gaussianReal 0 2` で genuine に閉じる (`hZXZY_law` `:155-161` を直接使用)
- [ ] docstring の `@audit:defect(false-statement)` + `@audit:closed-by-successor(...)` を除去
- [ ] 他 field (pX_sum series / density / density_t_eq / integrable_deriv bound) の再利用結線確認

**残1 (integrable_deriv t-可測性) park との関係 (GS-A4' で classification 整理)**: sum producer
`integrable_deriv` (`:200-219`) は bound 部 (PB-2b Fisher 単調性) genuine、唯一 **t-可測性**
(`logDeriv (convDensityAdd …)` lintegral の parameter measurability、`:206-210`) が `sorry` +
`@residual(...)` で park。これは X/Y producer 残1 (`EPICase1RatioLimit.lean:2041` 付近) と **同型障害**
(Mathlib parameter-measurability gap)、本 plan scope 外。`Z_law` closure 後も残る別障害。

- [ ] t-可測性 sorry の `@residual` を整理: `Z_law` closure 後の状態に合わせ、compound から
  defect 由来の `plan:epi-case1-sum-producer-plan` を外し t-可測性 owner に揃える
- [ ] 残1 (X/Y producer t-可測性) と sum の t-可測性が同一 closure に乗るか (同型なら共有補題候補)

**Done 条件**: `Z_law` genuine (defect 除去)、他 field 無改変再利用、t-可測性 park の residual
classification を `Z_law` closure 後の状態に更新。

### GS-A5' — PB-6 wrapper `_full` 結線 + verify/監査

**スコープ**: PB-6 最終 wrapper (`entropyPower_add_ge_case1_of_methodX_unitnoise` or `_full`、未作成、
Phase C wrapper `EPICase1RatioLimit.lean:1498` の後継) への結線順序を general-variance surgery 反映で
更新し、verify + 独立 honesty audit。

**結線順序 (残1 + 本 plan 解決後)**:
1. **残1** (X/Y producer t-可測性、別 plan) → X/Y producer genuine
2. **本 plan** (sum producer `Z_law` genuine、general-variance v_Z=2) → sum producer genuine
   (t-可測性は残1 依存)
3. **PB-5** `h_pos_stam` producer (Stam/Blachman genuine 既存配線、sum がここに刺さる)
4. **PB-6** 最終 wrapper `_full`: X/Y producer (v_Z=1) + sum producer (本 plan、v_Z=2) +
   `IsHeatFlowEndpointRegular` 3 本 (既存 general v=1/v=1/v=2、`EPIStamToBridge.lean:1435-1452`) +
   `h_pos_stam` (PB-5) を注入。general-variance de Bruijn group と `IsHeatFlowEndpointRegular` の
   v_Z 役割 (微分値 vs 連続性) が整合することを確認 (Q-CORE prior art 節)
5. **PB-7** `IsIBPHypothesis` (`FisherInfoV2DeBruijnBody.lean:209`、死 alias) retract

**verify + 独立 honesty audit**:
- [ ] touched file 全件 `lake env lean` silent
- [ ] sum producer + general-variance de Bruijn + factor-2 ratio-Stam + 最終 wrapper を `#print axioms` で
  確認 (残1 t-可測性 park があれば `sorryAx` 残存 = type-check done、`Z_law` genuine 化で defect 消滅)
- [ ] **独立 honesty audit** (`honesty-auditor` subagent) 起動 (`Z_law` defect → genuine の signature
  意味変化 + general-variance structure surgery + 2 consumer lemma factor-2 再導出で honesty 意味が変わる →
  CLAUDE.md「Independent honesty audit」起動条件)
- [ ] audit verdict 確認:
  - `Z_law : P.map (Z_X+Z_Y) = gaussianReal 0 2` が genuine (v_Z=2 で真の law 受容、defect 解消)
  - **2 consumer lemma の factor-2 再導出 (`hN_*` lift `:766-803` + `α²≤α` arith) が genuine** (正しい
    per-term factor で harmonic Stam が ≤0、case-A の「ratio core 無改変」は PROBE 1c/2/3b で REFUTE 済 →
    §解析核判定 (ii) / 判断ログ 9)
  - de Bruijn 微分値の per-term factor (sum: `(v_sum/2)·J`、X/Y: `(1/2)·J`) が consumer に正しく流れ、
    spurious factor 2 (PROBE 3b) が解消されている
  - general-variance structure の v_Z field が load-bearing でなく regularity 一般化として正当
  - factor-2 再導出が `*Hypothesis` bundling でなく genuine な weight 再導出 (核を仮説に抱えていない)
  - wrapper の結論 `N(X+Y)≥N(X)+N(Y)` が不変
  - sum producer の他 field が regularity precondition のまま
  - 残1 (t-可測性) park の residual classification が正しい

**Done 条件**: 全 silent + audit verdict 全 OK (or questionable-resolved-inline)。headline proof done
条件 (残1 t-可測性 + 本 plan の factor-2 ratio-Stam 再導出 GS-A3' + general-variance plumbing GS-A1'/A2'
すべて genuine) を明示。

---

## 撤退ライン (2026-06-06 改訂 — case-A REFUTE 後、factor-2 再導出 = 真の解析核)

- **L-GS-A0-wall (Mathlib 壁送り)** — **発動 NO (確定)**: factor-2 ratio-Stam 再導出は **標準 de Bruijn
  EPI の真の数学** (sum 微分=`J`(variance 2)、component=`(1/2)·J`(unit)、harmonic Stam が正しい factor 込みで
  EPI を出す、EPI は真の定理) であり **Mathlib 壁ではない**。同時に advisor の trivial shortcut (case-A、
  ratio core 無改変) でもない (PROBE 1c/2/3b で機械 REFUTE)。よって「全体 park 恒久化 + textbook 別 phase
  送り」(案D) は **非推奨**。本 line は発動せず。
- **L-GS-A3'-weight (GS-A3' gate 段階、bounded、別 route でない)**: factor-2 ratio-Stam 再導出の 2 consumer
  lemma (`hN_*` lift `:766-803` + `α²≤α` arith) が現 weight 構造で閉じない (補正 factor で harmonic-Stam が
  ≤0 を保てない) → weight 構造の調整が要る範囲を sizing し、当該 phase を `sorry` +
  `@residual(plan:epi-case1-debruijn-genvar-struct-plan)` で park (signature は本来の general-variance 形を
  保つ、honest tier-2 residual)。これは **bounded な weight 再設計** であって別 route ではない (variance-2
  受容は唯一の path、§解析核判定 (i))。**`*Hypothesis` predicate に核を bundling する撤退は禁止**
  (CLAUDE.md「検証の誠実性」)。次 wave 繰り越し。
- **L-GS-blast (GS-A1' 段階)**: structure surgery の consumer breakage (13 file、plumbing) が機械的 v_Z:=1
  補完で吸収されず各証明が load-bearing 依存で大幅に書換要 → surgery を分割するか、既存 unit structure を残し
  **新 general-variance structure を別途定義** (新旧並存) する route に escalate (判断ログに記録)。probe item f
  で「13-file consumer は機械的 v_Z:=1 補完で吸収」見込みなので大幅超過の懸念は **低い**。
- **L-GS-A2'-plumbing (GS-A2' 段階)**: `_entropy_eq`/`_fisher_match` の general-variance 化 (plumbing、
  `pPath_eq_convDensityAdd` general v_Z 経由) が詰まる → 当該 phase を `sorry` +
  `@residual(plan:epi-case1-debruijn-genvar-struct-plan)` で park (signature は本来の general-variance 形を
  保つ、honest tier-2 residual)。GS-A3' (解析核 gate) が通っていれば結線は機械的なので発動確率は低い。
  **`*Hypothesis` predicate に核を bundling する撤退は禁止**。次 wave 繰り越し。
- **L-GS-integrable (GS-A4' 段階)**: 残1 (integrable_deriv t-可測性) は本 plan scope 外。`Z_law`
  closure 後も sum producer は t-可測性 park を残す → headline proof done は残1 closure と協調が必要。
  本 plan 単独では sum producer type-check done (Z_law genuine + t-可測性 park) 止まり。

## genuine closure 可能な範囲 / 別 phase 送りの境界

- **genuine closure 可能 (本 plan scope、case-A REFUTE 後の確定)**: sum noise N(0,2) の `Z_law` 型
  不充足を (b-2) general-variance surgery で解消 (`Z_law : P.map (Z_X+Z_Y) = gaussianReal 0 2` を
  v_Z=2 で受容、GS-A4')、かつ **factor-2 ratio-Stam 再導出** (`hN_*` lift `:766-803` + `α²≤α` arith を
  per-term factor で再導出、GS-A3' load-bearing 解析核) + general-variance plumbing (GS-A1'/A2')。
  factor-2 再導出は **標準 EPI 数学で壁でない**、案A の「ratio core 無改変・carrier rescale 同定」は GS-A0
  probe で機械 REFUTE (PROBE 1c/2/3b)。variance-2 は coupling に intrinsic (§解析核判定 (i)) なので回避せず
  正面受容。
- **解析核 wall 送り (案D) は非推奨**: factor-2 ratio-Stam 再導出は標準 de Bruijn EPI の真の数学
  (壁でない、EPI は真の定理)。defect park 恒久化 + textbook 別 phase 送りは **採らない**。唯一の
  リスクは GS-A3' gate で現 weight 構造が補正 factor を吸収できない場合のみ (bounded、weight 再設計、
  L-GS-A3'-weight)。
- **残1 依存 (本 plan では閉じない、別 plan へ)**: sum/X/Y producer の `integrable_deriv` t-可測性
  (`logDeriv (convDensityAdd …)` lintegral の parameter measurability)。Mathlib gap、別 owner。
  `Z_law` closure 後も残る別障害。
- **別 phase / textbook 最終版送り**: X/Y producer の `integrable_deriv` bound (PB-2b Fisher 単調性) が
  依存する regular-density + bounded-deriv precondition の general L¹ への緩和 (approximation)。残2 plan
  §境界と同じく textbook 最終版で別 phase。

---

## 参考 file (verbatim file:line)

- `InformationTheory/Shannon/EPICase1SumProducer.lean:88` — sum producer
  `isDeBruijnRegularityHyp_sum_of_methodX_unitnoise` (`Z_law` field を `@audit:defect(false-statement)`
  `:151-168` で park、本 plan が genuine 化する対象)
- `InformationTheory/Shannon/EPICase1SumProducer.lean:110-219` — 再利用可能 genuine field
  (pX_sum series / density / density_t_eq / integrable_deriv bound、`Z_law` 以外保持)
- `InformationTheory/Shannon/EPICase1SumProducer.lean:141-142` — sum producer `density_t` =
  `convDensityAdd pXS (gaussianPDFReal 0 ⟨t, ht.le⟩)` (**carrier `t`**、X/Y producer と同型。注意:
  general-variance 化後は de Bruijn 微分値が carrier `t·v_Z` (v_Z=2 で `2t`) の density の Fisher 値に
  なる — PROBE 1c/2 で carrier-t と carrier-2t の density は非 defeq・Fisher 値が異なると機械確認、
  この carrier drift が GS-A3' factor-2 再導出を要求する)
- `InformationTheory/Shannon/EPICase1SumProducer.lean:200-219` — `integrable_deriv` (bound genuine、
  t-可測性 `:206-210` park、残1 同型、GS-A4' で classification 整理)
- `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:205-268` — `IsRegularDeBruijnHypV2`
  structure (`Z_law : gaussianReal 0 1` `:210` + `density_t_eq` carrier `t` `:260-261` が
  v_Z=1 hardcode、Q-CORE field 表)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3437-3473` —
  `debruijnIdentityV2_holds_assembled_entropy_eq` (`hZ_law : gaussianReal 0 1` hardcode `:3440`、
  内部 `pPath_eq_convDensityAdd ... (1:ℝ≥0) ...` `:3452`、carrier `s·1=s` `:3460`、**v_Z 結線の核心**)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3485-3500` —
  `debruijnIdentityV2_holds_assembled_fisher_match` (`density_t_eq` carrier `⟨t,_⟩` で同定、v_Z=1 hardcode)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3397-3414` —
  `debruijnIdentityV2_holds_assembled_chain` (density-level、**v_Z-agnostic**、noise 不参照、
  残2 plan の「_chain は v_Z-agnostic」主張は正しい)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:3543-3587` —
  `debruijnIdentityV2_holds_assembled` (3 sub を `h_reg.Z_law` で叩く、v_Z=1 でのみ genuine)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:215-224` —
  `pPath_eq_convDensityAdd` (**general v_Z 受容**、carrier `s·v_Z`、reparam τ=s·v_Z の基盤)
- `InformationTheory/Shannon/FisherInfoV2DeBruijnGenuine.lean:51-61` — `deBruijn_identity_v2`
  (consumer、`(1/2)·J(h_reg.density_t)` を返す)
- `InformationTheory/Shannon/EPIStamToBridge.lean:699-838` — `csiszarLogRatioGap_hasDerivAt`
  (X/Y/sum 3 成分の `density_t` Fisher を消費、`(1/2)` cancel `:773/785/799`、ratio-gap 微分値
  `:712-721`、**v_Z が arith に到達する結線**)
- `InformationTheory/Shannon/EPIStamToBridge.lean:766-803` — `csiszarLogRatioGap_hasDerivAt` の `hN_*`
  entropy-power lift (X/Y/sum 全成分が `h_val` 内で `2 * ((1/2) * J)` hardcode、`:771/784/799`)。
  **GS-A3' factor-2 再導出の対象 (a)**: variance-2 sum 項は真値 `(v_sum/2)·J_sum = J_sum` で `2·` lift と
  cancel せず `eP·J_sum·2` の spurious factor 2 (PROBE 3b `ring` 落ち) → `hN_sum` を per-term factor で書直し
- `InformationTheory/Shannon/EPIStamToBridge.lean:895` — `csiszarLogRatioGap_deriv_le_zero`
  (harmonic Stam ratio core、現状 全成分 unit 前提)。`csiszar_ratio_deriv_le_zero_arith` (`α²≤α` weights、
  `:843-848` 付近) が **GS-A3' factor-2 再導出の対象 (b)**: factor-2 sum numerator で ≤0 を保つか再導出。
  ⚠ `:876-893` の @audit:ok docstring 末尾「3 Fisher rfl が成立するのは `fisherInfoOfMeasureV2` measure
  無視 `:81` から」は **削除済 D3 difference-gap context を参照する stale 記述** (live `:895` は density-direct
  `fisherInfoOfDensityReal` を使う)。**advisor の case-A 取り違えの誤読源** (判断ログ 9、§参考 file 末尾 stale
  docstring 指摘)。将来当該 file touch 時に 1 行訂正候補 (incidental)
- `InformationTheory/Shannon/FisherInfoV2DeBruijn.lean:81` — `fisherInfoOfMeasureV2 (_μ) f :=`
  `fisherInfoOfDensity f` (**第1引数 measure を無視するが、第2引数 density witness `f` は full load-bearing**)。
  ⚠ advisor の case-A はこの measure 無視を de Bruijn 微分・ratio core が使う density-direct
  `fisherInfoOfDensityReal` に誤適用した (取り違え、PROBE 1a/0 で機械確認)。`J_sum` は density (第2引数) に
  依存し carrier `t·v_Z` で v_Z 依存する (PROBE 2、case-A REFUTE)
- `InformationTheory/Shannon/EPIStamToBridge.lean:1085-1098` —
  `csiszarLogRatioGap_antitoneOn_Ici_zero` (`IsDeBruijnRegularityHyp` 3本 + `IsHeatFlowEndpointRegular`
  3本を同時消費、prior art 共存点)
- `InformationTheory/Shannon/EPIStamToBridge.lean:1435-1452` — `IsHeatFlowEndpointRegular` producer
  (X→v_Z=1 / Y→v_Z=1 / **sum→v_Z=2 を直接渡す** prior art、端点連続性専用で arith 非到達)
- `InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:488-503` — `IsHeatFlowEndpointRegular`
  structure (`v_Z : ℝ≥0` field + `hZ_law : gaussianReal 0 v_Z`、general-variance だが連続性専用)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1765` — `gaussianConvolution_rescale_eq`
  (`:1778` `map_gaussianConvolution_rescale_eq`、in-tree、@audit:ok、sorryAx-free single `rw`)。
  ⚠ **案A (carrier rescale 同定で ratio core 無改変再利用) は PROBE 1c で機械 REFUTE**: これは
  **path 関数恒等式** (`X+√(t·v)·(Z/√v) = X+√t·Z`) で `fisherInfoOfDensityReal` が消費する **density 関数に
  届かない** (carrier-t と carrier-2t density は非 defeq、`rfl` 失敗)。GS-A3' factor-2 再導出には使えない。
  general-variance plumbing (GS-A1'/A2') の path-level 同定には依然 in-tree asset (旧 plan `~:1769`、
  proof-log `:1766`、verbatim `:1765`)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1498` — Phase C wrapper
  `entropyPower_add_ge_case1_of_methodX` (PB-6 `_full`/`_unitnoise` の前身)
- `InformationTheory/Shannon/EPICase1RatioLimit.lean:1913` —
  `isDeBruijnRegularityHyp_of_methodX_unitnoise` (X/Y producer、pX series plumbing を W=sum noise に流用)
- `InformationTheory/Shannon/EPIL3Integration.lean:1380-1385` — antitone target `csiszarLogRatioGap`
  (sum path `X+Y+√t·(Z_X+Z_Y)` literal `Z_X+Z_Y`、X/Y と単一共有 t — **variance-2 が coupling に
  intrinsic な証拠**、§解析核判定 (i))
- `InformationTheory/Shannon/EPIStamToBridge.lean:919-922` — `csiszarLogRatioGap_deriv_le_zero` の
  `h_conv_id` (sum density を carrier-t の X/Y density の `convDensityAdd` = carrier-2t に同定、
  **variance-2 intrinsic の決定的裏取り**)
- `docs/shannon/proof-log-epi-case1-genvar-struct.md` — **GS-1 probe 結果** (B-τ NO-GO machine-verified、
  item 4d desync、`Z_law` load-bearing trace、b-2 = surviving path、GS-0 inventory) + **GS-A0 probe 結果**
  (§GS-A0 probe、6 `example`、case-A REFUTE: PROBE 1c carrier rescale が density に届かず / PROBE 2/3b
  `J_sum` v_Z 不変が偽 / advisor の `fisherInfoOfMeasureV2`/`fisherInfoOfDensityReal` 取り違え + stale
  docstring `:892-893` 誤読源、item f で plumbing 機械的・2 consumer lemma が解析核と確認)
- `EPIStamToBridge.lean:892-893` (将来 touch 時の incidental 訂正候補) — @audit:ok docstring 末尾の
  「3 Fisher rfl が成立するのは `fisherInfoOfMeasureV2` measure 無視 `:81` から」が **削除済 D3 difference-gap
  context を参照する stale 記述**。live ratio core `csiszarLogRatioGap_deriv_le_zero` (`:895`) は
  density-direct `fisherInfoOfDensityReal` を使い、この docstring が advisor の case-A 取り違えを誘導した
  (判断ログ 9)。当該 file を touch する際に 1 行訂正する (本 plan scope 外、incidental)
- `docs/shannon/epi-case1-sum-producer-plan.md` — predecessor plan (sum producer、`Z_law` defect park、
  ルート (a)/(b)/(c) sizing、§問題の核心)
- `docs/shannon/epi-case1-debruijn-producer-fork-sizing.md` — 案A OUT (Q1 ratio 偽化 = **naive 値据置
  一般化が偽**、§解析核判定 (ii) で b-2 の「正しい factor 再導出」と区別) / 案C (reparam) は B-τ で
  REFUTE 済
- `docs/shannon/epi-case1-debruijn-producer-plan.md` — 親 plan (PB-1〜PB-7、残1 設計)
- `docs/audit/audit-tags.md` — `@residual` 語彙 (compound syntax) / `@audit:defect` / `@audit:closed-by-successor`

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **2026-06-06 起草時 — Q-CORE を実コード結線で決着 (本 plan の中心価値)**: 残2 plan の主張
   「Z_law を一般化しても微分値を触らず density を unit-W pin すれば ratio core 偽化を回避」を実機械で
   検証し **不可** と確定。決め手は `debruijnIdentityV2_holds_assembled_entropy_eq`
   (`FisherInfoV2DeBruijnAssembly.lean:3437`) が `hZ_law : gaussianReal 0 1` を **hardcode 引数で取り**、
   内部 `pPath_eq_convDensityAdd ... (1:ℝ≥0) ...` (`:3452`) で path の真の density (carrier `s·v_Z`) を
   `_chain` が解析する density (carrier `s`) に同定していること (`:3460` `hwit1 : s·1=s`)。
   `Z_law = gaussianReal 0 2` にすると carrier `s·2 ≠ s` で drift し、de Bruijn 微分値が
   `(1/2)·J(convDensityAdd pX g_{s·2})` になって ratio core (`:895`、harmonic Stam 項毎 factor 非不変) を
   偽化する。`_chain` 自身は v_Z-agnostic (`:3397`、noise 不参照) なので残2 plan の「_chain は
   density-level」主張は正しいが、`_entropy_eq`/`_fisher_match` の hardcode が `Z_law` 値と density
   carrier を結びつけており、density-pin だけでは救えない。→ **v_Z は ratio core arith に到達する**
   (Q-CORE 答え)。

2. **2026-06-06 — prior art `IsHeatFlowEndpointRegular` 共存は v_Z 安全の証拠にならないと判定**: 残2 plan
   は `IsHeatFlowEndpointRegular` (general v_Z、sum に v_Z=2、`EPIStamToBridge.lean:1447`) の共存を
   ルート (b) の根拠としたが、`csiszarLogRatioGap_antitoneOn_Ici_zero` (`:1085`) はこの structure を
   **端点連続性専用** (`heatFlowEntropyPower_continuousWithinAt_zero`、収束) としてのみ消費し、Fisher
   微分値 (ratio core arith) に到達させない。`IsDeBruijnRegularityHyp` の v_Z は (判断ログ 1 のとおり)
   arith に到達する。2 structure の v_Z は **役割が別** (連続性 vs 微分値) なので、前者の v_Z=2 共存は
   後者の v_Z 一般化を正当化しない。残2 plan の M0' 観察はこの役割差を見落としている。

3. **2026-06-06 — ルート (B-τ) を本命に (fork-sizing 案C と一致)**: Q-CORE 結線で値一般化 (案A/b-2 naive)
   が数学的に通らないことが確定したので、唯一の honest route は **W unit reparam + 時間 τ=t·v_Z で
   chain factor 打消し** (fork-sizing `:67-88` 案C / 案B+τ)。残2 plan が (a) を「path-id は noise law
   救えないので OUT」と判定したのは **wrapper が `Z_X+Z_Y` を thread する形を固定したまま**の判定で、
   (B-τ) は **wrapper noise-W 化** (ルート c を内包) で `Z_law : P.map W = gaussianReal 0 1` を
   genuine に閉じる。W は真に unit なので de Bruijn core (`_assembled`) を無改変で使え、carrier τ で
   ratio core を偽化させない。代償は wrapper noise-W 化 (結論不変、noise は補助変数)。**最終確定は
   GS-1 skeleton で reparam bridge が `Z_law` の noise law 主張を W に切り替えられるか実機械裏取り必須**。

4. **2026-06-06 — sum producer は `Z_law` field 1 個差し替えが最小コスト (auditor 指摘踏襲)**: 他 field
   (pX_sum series / density / density_t_eq / integrable_deriv bound) は genuine で保持価値あり。本 plan は
   `Z_law` defect park (`@audit:defect(false-statement)`) を genuine に差し替えるだけで、他 field 無改変
   再利用。`integrable_deriv` t-可測性 park (残1 同型) は本 plan scope 外で、`Z_law` closure 後も残る
   別障害として GS-A4 で classification を整理。

5. **2026-06-06 — GS-1 probe で route (B-τ) を REFUTE (machine-verified、本改訂の核心)**: B-τ
   (unit-noise `W := (Z_X+Z_Y)/√2 ∼ 𝒩(0,1)` を de Bruijn structure に渡し時間 `τ=2t` reparam) を
   `example` skeleton 6 本で型確認 (実行後 revert、詳細 `proof-log-epi-case1-genvar-struct.md`)。
   **producer 側は genuine** (W-law `P.map W = gaussianReal 0 1` が `gaussianReal_add_gaussianReal_of_indepFun`
   → `gaussianReal_map_div_const` で ~15 行、item 1; W-producer clean 構成 item 2; `reg_at .Z_law`
   obligation も W で genuine 充足 item 3a) だが、**consumer 側が W を受容できない** (item 4d desync)。
   決め手 = W 置換の reparam `τ=2t` が sum path を W-path の time 2t として再表現し、その de Bruijn 微分が
   `h_reg_W.reg_at (2t)` に座って **time 2t で評価**される一方、X/Y 項は time t (`h_reg.reg_at t`)。
   antitone 証明 `csiszarLogRatioGap_hasDerivAt` (`EPIStamToBridge.lean:699`) は 3 成分を **単一共有 t** で
   取るため sum だけ別 time にできず、`reg_at-at-2t` を shared-t 結合に入れるには consumer の `(1/2)·J`
   arithmetic が持たない `2·` chain factor が要る (item 4d、型レベル確認)。さらに probe trace で
   `Z_law=unit` の false が **consumer の微分 arithmetic に load-bearing** と確定 (`:747` →
   `debruijnIdentityV2_holds_assembled` が false unit `Z_law` を消費して variance-2 sum 項の `(1/2)`
   factor を得る)。W はこの false を除去せず time-desync に移すだけ。→ **B-τ NO-GO**、旧 Approach の
   B-τ 本命判定を撤回。

6. **2026-06-06 — route (c) wrapper-W 化も不可 (単一-t signature)**: antitone target `csiszarLogRatioGap`
   (`EPIL3Integration.lean:1380`) は sum path を `X+Y+√t·(Z_X+Z_Y)` (sum noise literal `Z_X+Z_Y`、X/Y と
   同一の単一 t) で **hardcode**。W 化は sum 項に別 time (2t) を要求するが、単一-t signature では「sum
   項だけ別 time」を表現できない。mechanical noise rename でなく antitone object の時間変数 restructuring
   が要り ~93 sum-path sites (3 consumer file + endpoint lemmas + saturation pillar) に伝播。tractable な
   wrapper rename ではないので route c も廃止。

7. **2026-06-06 — route (b-2) general-variance surgery が唯一 surviving honest path に確定 + 解析核の
   wall-vs-tractable 判定を crisp 化**: variance-2 は coupling `(X+Y)+√t·(Z_X+Z_Y) = X_t+Y_t` に
   **intrinsic** (実コード裏取り: `csiszarLogRatioGap` sum path `:1382` が literal `Z_X+Z_Y`、
   `csiszarLogRatioGap_deriv_le_zero` の `h_conv_id` `EPIStamToBridge.lean:919-922` が sum density を
   carrier-t の X/Y density の `convDensityAdd` = carrier-2t に同定)。fresh unit `Z_S` では coupling が
   壊れ Fisher 比較不能 → variance-2 回避は原理的に不可、**正面受容する general-variance structure (b-2)
   が本質的に必要**。解析核 = **factor-2 ratio-Stam 再導出**。fork-sizing Q1 (`:32-40`) の偽化主張は
   「naive 値据置一般化」(値 `(1/2)·J → (v_Z/2)·J` のみ変えて harmonic-Stam weight 据置) を指すと実コード
   再確認 (`csiszarLogRatioGap_deriv_le_zero` `:895` は全成分 unit 前提の `α²≤α` weights)。b-2 が指すのは
   「正しい factor で weight ごと再導出した harmonic-Stam」= 真の EPI の Stam 不等式
   (`1/J(X+Y) ≥ 1/J(X)+1/J(Y)`、Blachman) で **真であるはず**だが genuine 証明を要する。両者を §解析核判定
   (ii) に明記。ただし「真であるはず」は EPI 一般論からの推定で現有資産から factor-2 版が genuine に
   再導出できるかは未確認 → **GS-A0 で `proof-pivot-advisor` gate を最初に置き、解析核が現有資産で閉じるか
   在庫横断確認 + 機械検証で裏取りしてから 13-file surgery に着手する** risk 順序を採用 (解析核が真と
   確認できてから plumbing に投資)。GS phase を GS-A0〜A5 に再構成。`Z_law` defect park
   (`EPICase1SumProducer.lean:166`) は本 wave 進行中維持 (本 plan が closure owner、slug 正当)。

8. **2026-06-06 — GS-A0 `proof-pivot-advisor` gate = CONDITIONAL-GO (案A、re-scoped)。13-file surgery +
   factor-2 ratio-Stam 新規再導出 (解析核 wall 候補) の risk framing が過大評価と確定 (実コード機械裏取り)**:
   旧 plan は route (b-2) の load-bearing 解析核を「factor-2 ratio-Stam の **新規再導出**」(値据置 naive 化で
   非一律 factor が残り `α²≤α` weight が破れるので、正しい factor で weight ごと再構成する genuine 証明が
   必要、壁候補) と framing し、GS-A0 で `proof-pivot-advisor` gate を置いて在庫横断で tractability を
   確認する設計だった。advisor の実コード機械裏取りで以下 4 事実が確定し、framing が過大評価と判明:
   (1) **`fisherInfoOfMeasureV2 (_μ) f := fisherInfoOfDensity f`** (`FisherInfoV2DeBruijn.lean:81`、verbatim
   確認済) が measure 引数を**完全無視** → ratio-Stam が消費する `J_sum` は `density_t` のみ依存、`Z_law` の
   v_Z に**非依存**。
   (2) sum producer `density_t` は **carrier `t`** (`EPICase1SumProducer.lean:141-142`、verbatim 確認済、
   `convDensityAdd pXS (gaussianPDFReal 0 ⟨t, ht.le⟩)`) → consumer が見る `J_sum` は carrier-t 密度の Fisher
   値で、plan が恐れた carrier-2t drift は **consumer が消費する density には起きない**。
   (3) **ratio-Stam core `csiszarLogRatioGap_deriv_le_zero` (`EPIStamToBridge.lean:895`) は既に
   genuine・@audit:ok・sorryAx-free** (verbatim 確認済、`:876-893` docstring が「RATIO form IS closable
   from plain harmonic Stam」+「3 Fisher rfl が成立するのは `fisherInfoOfMeasureV2` measure 無視 `:81`
   から」と明記、2026-06-01 独立監査記録)。`h_conv_id` (`:919-922`、verbatim 確認済) が sum density を
   `convDensityAdd(X@t)(Y@t)` (coupling `X_t+Y_t` の真密度) に同定、`h_stam` の plain harmonic Stam から
   `α²≤α` arith で ≤0。**factor-2 は既に正しく織込み済** (sum 密度 = 2 carrier-t 密度の convolution =
   variance 加法性)、`(1/2)` は全項一律 cancel (`:773/785/799`)。**非一律 factor 問題は発生していない**。
   (4) **唯一の defect = `Z_law` field 単体** (`EPICase1SumProducer.lean:166`)。consumer の `J_sum` 値には
   load-bearing でない。load-bearing なのは `deBruijn_identity_v2` 内部で sum 項の微分値 = `(1/2)·J_sum` を
   proof する箇所だけ (`_entropy_eq` が `hZ_law:gaussianReal 0 1` を hardcode、`Assembly:3437/3452`)。
   **fork-sizing 偽化の (a)/(b) 切り分け = (a)**: fork-sizing Q1 (`:32-40`) は「**値据置 naive 化**
   (`(1/2)·J_i→(v_Z_i/2)·J_i` と値を据置換え) で非一律 factor が残り `α²≤α` が破れる」(= (a)) を指すので
   あって、「(b) 正しい factor の再導出が wall」とは言っていない。旧 plan は (a) を (b) に **読替えて**
   surgery 規模 (factor-2 ratio-Stam 新規再導出 = 解析核 wall 候補) を過大評価していた。
   **再 scope (案A)**: 真の作業は「factor-2 ratio-Stam 新規再導出」**ではなく**、`_entropy_eq`/`_fisher_match`
   を general-variance 化し、内部の carrier-`s·v_Z` path density を `gaussianConvolution_rescale_eq`
   (`EPICase1RatioLimit.lean:1765`、in-tree、@audit:ok) で carrier-`s` の `density_t` witness と **同じ
   Fisher 値**に同定する密度同定 (Assembly 局所)。**ratio-Stam core (`:895`) は無改変で再利用** (入力
   `h_conv_id`/`h_stam` は density-level、v_Z 非参照)。13-file consumer は density-level に閉じるため大半が
   機械的 v_Z:=1 補完で吸収される見込み (L-GS-blast 大幅超過の懸念は低い)。旧 GS-A3「factor-2 ratio-Stam
   再導出」を **削除**、GS phase を GS-A0' probe (carrier rescale 同定の型確認、最初の1手) → A1' (v_Z field
   追加) → A2' (Assembly v_Z 化 + carrier rescale 同定、ratio core 無改変) → A3' (sum producer `Z_law`
   genuine) → A4' (wrapper 結線 + verify/監査) に再構成。**L-GS-A0-wall は発動 NO** (advisor 確定)、defect
   park 恒久化 (案D) も非推奨。新リスクは GS-A0' probe の carrier rescale 同定が通らない場合のみ (現時点 low、
   L-GS-A0'-rescale)。`Z_law` defect park (`EPICase1SumProducer.lean:166`) は本 wave 進行中維持。

9. **2026-06-06 — GS-A0 probe が case-A (CONDITIONAL-GO 案A) を機械 REFUTE。真の load-bearing 解析核 =
   factor-2 ratio-Stam 再導出 (壁でない・trivial でない) に確定 (entry 8 を訂正)**: entry 8 の案A
   (「ratio core `:895` 無改変再利用・`J_sum` v_Z 不変・Assembly 局所 carrier rescale 同定で閉じる」) は
   GS-A0 probe (`proof-log-epi-case1-genvar-struct.md` §GS-A0 probe、6 `example` 型確認、実行後 revert) で
   **NO-GO** と機械実証された。**advisor の取り違え (case-A が誤りだった根本原因)**: advisor は
   **`fisherInfoOfMeasureV2` (measure-keyed wrapper、第1引数=measure 無視、`FisherInfoV2DeBruijn.lean:81`) と
   `fisherInfoOfDensityReal` (de Bruijn 微分値・ratio core が実際に使う density-direct 関数、第2引数=density
   関数が load-bearing) を取り違えた**。誤読の元は stale docstring `EPIStamToBridge.lean:892-893` (削除済 D3
   difference-gap context を参照、live ratio core `:895` は density-direct を使う)。機械実証 (probe verbatim):
   (1) **PROBE 1a**: `fisherInfoOfMeasureV2 μ f = fisherInfoOfDensity f` は `rfl` ✅ だが無視するのは第1引数
   (measure)、density witness `f` (第2引数) は full load-bearing。
   (2) **PROBE 1c (KEY)**: `convDensityAdd pX g_t = convDensityAdd pX g_{2t}` は **`rfl` 失敗** (carrier-t ≠
   carrier-2t density)。`gaussianConvolution_rescale_eq` (`:1765`) は **path 関数恒等式**で density 関数
   (`fisherInfoOfDensityReal` の引数) に **届かない** → 案A の核 (carrier rescale 同定) は機械 REFUTE。
   (3) **PROBE 2**: `fisherInfoOfDensityReal (convDensityAdd pX g_t) = ... g_{2t}` は `rfl`/`simp` で閉じない
   (Gaussian-conv 密度の Fisher 値は carrier 依存、`J(pX∗g_t)≤1/t`) → **`J_sum` v_Z 不変は機械 REFUTE**。
   (4) **PROBE 3b (make-or-break)**: v_sum=2 で sum 項 de Bruijn 微分 = `(2/2)·J_sum = J_sum`、consumer の
   hardcoded `2·` lift と衝突し `ring` が `eP·J_sum = eP·J_sum·2` (verbatim machine output) 矛盾に帰着。desync は
   ratio core (`:895`) ではなく **1 level 上の** `csiszarLogRatioGap_hasDerivAt` の `hN_sum` lift
   (`EPIStamToBridge.lean:790-803`) の hardcoded `(1/2)` cancellation に局在。
   **entry 8 の誤り箇所**: entry 8 (2)「consumer の `J_sum` は carrier-t で v_Z 非依存」は誤り — PROBE 2 で
   general-variance 後の de Bruijn 微分値は carrier `t·v_Z` (=2t) の density の Fisher 値になり v_Z 依存。
   entry 8 (3)「factor-2 は既に正しく織込み済・無改変再利用」も誤り — PROBE 3b で variance-2 sum 項は
   spurious factor 2 を生み consumer arithmetic が落ちる。entry 8 の fork-sizing (a)/(b) 切り分け自体は正しい
   ((a) 値据置 naive 化が偽、(b) 正しい factor 再導出が真) が、entry 8 は「再導出が不要 (既に織込み済)」と結論
   して (b) をスキップしたのが誤り。**確定状態 (機械実証で固定、これ以上 route を振らない)**: 真の作業 =
   **factor-2 ratio-Stam 再導出** = 2 consumer lemma ((a) `hN_*` lift `:766-803` per-term factor + (b)
   `α²≤α` arith factor-2 sum numerator)。これは **標準 de Bruijn EPI の真の数学** (sum 微分=`J`(variance 2)、
   component=`(1/2)·J`(unit)、harmonic Stam が正しい factor 込みで EPI を出す、EPI は真の定理) で **Mathlib
   壁ではない**、同時に advisor の trivial shortcut (case-A) でもない (機械 REFUTE)。plumbing (GS-A1'/A2'、
   13-file v_Z field + Assembly v_Z 化) は機械的 (probe item f、`pPath_eq_convDensityAdd` general v_Z 既存 +
   X/Y `v_Z:=1` carrier definitionally 回復)。非機械的部分は 2 consumer lemma に局在。GS phase を再構成:
   **GS-A3' (最初の1手 gate、factor-2 再導出)** → A1' (v_Z field plumbing) → A2' (Assembly v_Z 化 plumbing) →
   A4' (sum producer `Z_law` genuine) → A5' (wrapper 結線 + verify/監査)。案A GS-A0' (carrier rescale 同定
   probe) は **削除** (PROBE 1c で REFUTE)。次手 = GS-A3' 最小 probe (sum 項 lift を正しい factor で書直し +
   `α²≤α` arith が ≤0 を保つか機械確認、plumbing に投資する前に解析核 tractability 確認)。**L-GS-A0-wall は
   依然 発動 NO** (factor-2 再導出は標準 EPI 数学、壁でない)、defect park 恒久化 (案D) も非推奨。唯一のリスク =
   GS-A3' gate で現 weight 構造が補正 factor を吸収できない場合 (bounded な weight 再設計、別 route でない、
   L-GS-A3'-weight)。`Z_law` defect park (`EPICase1SumProducer.lean:166`) は本 wave 進行中維持 (GS-A3' closure
   まで、slug 正当)。stale docstring `EPIStamToBridge.lean:892-893` は当該 file touch 時の incidental 訂正候補
   (本 plan scope 外、参考 file 末尾に記録)。
