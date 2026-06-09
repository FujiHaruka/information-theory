# EPI case-1 difference G3 closure サブ計画 🌙

> **Parent**: [`epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md) §Phase 3 (a.c. EPI core / case 1)
> 関連: [`epi-csiszar-ratio-reframe-plan.md`](epi-csiszar-ratio-reframe-plan.md) (G1 ratio, R-3‴ 案 B = closure 雛形),
> [`epi-stam-to-conclusion-phaseA-plan.md`](epi-stam-to-conclusion-phaseA-plan.md) (現 sorry の owner plan),
> [`epi-richness-route-b-plan.md`](epi-richness-route-b-plan.md) (joint-indep lift route-B B2),
> [`epi-blachman-general-density-recheck-inventory.md`](epi-blachman-general-density-recheck-inventory.md) (false-wall verdict, Blachman producer 在庫),
> [`epi-method-y-lsc-recheck.md`](epi-method-y-lsc-recheck.md) (方針 Y genuine walled → 方針 X 確定).

記法: moonshot-plan-template と同じ (状態絵文字 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更, ~~取り消し線~~, 判断ログ append-only)。

---

## 進捗

- [x] Phase 0 — M0 在庫照合 ✅ (joint-indep = `indepFun_prodMk_prodMk`+`comp` self-derive 判明、判断ログ 5)
- [~] Phase 1 — honest signature: 🔄 **新ルートに pivot** (judgment 7-9)。saturation を difference でなく **ratio+scaling squeeze** で。precondition は `IsRescaledPathRegular` bundle に集約済
- [~] ~~Phase 2/3 (旧 difference G3)~~ — 🔄 **park** (judgment 6: ratio carrier ⊬ difference target、sufficiency gap)。新ルートが代替
- [x] **Phase 3' (新) — ratio+scaling saturation architecture ✅ genuine 完成** (`EPICase1RatioLimit.lean`、4 decl 全 `@audit:ok`、0 sorry、sorryAx-free、独立監査 2 回 PASS)。entropic CLT 回避を達成。§1 `epi_of_csiszarLogRatioGap_tendsto` / §2 `entropyPower_path_scaling` / §3 `entropyPower_rescaled_path_tendsto` (squeeze) / §4 `csiszarLogRatioGap_tendsto_zero_atTop` (主定理 `R(t)→0`)
- [ ] **Phase B — precondition 供給** 📋: (i) `IsRescaledPathRegular` discharge (a.c.+方針X regularity から)、(ii) ratio antitone (`csiszarLogRatioGap_antitoneOn_Ici_zero:1085`) の precondition 供給 = `hXYZXY` self-derive (judgment 5) + 3×`IsHeatFlowEndpointRegular` (density-witness、方針X) + `h_pos_stam` (Blachman = `isBlachmanConvReady_convDensityAdd_gaussian` 供給)
- [ ] **Phase C — headline 結線** 📋: ratio antitone + `csiszarLogRatioGap_tendsto_zero_atTop` + `epi_of_csiszarLogRatioGap_tendsto` → case-1 EPI → `stamToEPIBridge_holds` / dispatch skeleton case-1 枝。方針X precondition thread、`#print axioms` 検証、honest 命名 (bare `_unconditional` 禁止)

proof-log: Phase 2/3/4/5 は完了時に `docs/shannon/proof-log-epi-case1-g3-phase-*.md`。Phase 0/1 は proof-log: no (調査・設計のみ)。

---

## ゴール / Approach

**最終到達点**: headline `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:254`) を、**方針 X** (a.c. × 2 + 有限分散 + 有限微分エントロピーを honest precondition) の下で sorryAx-free 化する。これにより case 1 (両 a.c. = 古典 EPI、有限分散・有限エントロピー入力) が genuine closure し、親 umbrella Phase 3 の「両ルート walled」park が解除される。

### 前提の更新 (本計画の出発点、verbatim 検証済)

1. **`wall:blachman-general-density` は FALSE WALL**。一般密度 Blachman producer `isBlachmanConvReady_convDensityAdd_gaussian` (`EPIBlachmanGeneralDensity.lean:224`、19/19 field genuine、sorryAx-free) が実在し、per-`t` の `IsBlachmanConvReady (conv pX g_t) (conv pY g_t)` を任意 a.c. 密度から供給する。詳細 → recheck inventory。**case 1 を block する Mathlib 壁は無い**。
2. **ratio t→∞ 経路は NO-GO** (entropic CLT 壁)。**difference G3 経路** (`heatFlowPath2 = √(1−s)X + √s Z`、s=1 で pure Gaussian → `entropyPower_gaussian_additivity` genuine) が正しいアーキ。bridge body は ratio 化してはいけない (pure-Gaussian 端点喪失)。
3. **方針 Y (有限分散も除く) は genuine walled** (entropy LSC が Mathlib 不在 + klFun-Fatou と向き逆)。⇒ **honest 到達目標は方針 X**。

### Approach (解の全体形 — 4 つの柱)

**柱 A: difference G3 carrier は既に genuine、残るは rescale assembly のみ。**
`csiszarGap_antitoneOn_Icc_zero_one` (`EPIStamToBridge.lean:1270`, sorry) は genuine ratio antitone `csiszarLogRatioGap_antitoneOn_Ici_zero` (`:1085`, **sorryAx-free body**) を carrier 引数に取る。その sorry body は ratio antitone (Ici 0) を `csiszarGap_eq_one_source_via_rescale` (`EPIL3Integration.lean:1482`, genuine 等式) で 2-source difference antitone (Icc 0 1) に持ち上げる純粋 assembly。Mathlib 壁なし。

**柱 B: joint-indep `hXYZXY` は under-hyp (signature 問題) であって Mathlib 壁でない。**
`IndepFun (X+Y) (Z_X+Z_Y) P` は pairwise (`X⊥Z_X`, `Y⊥Z_Y`, `Z_X⊥Z_Y`) からは出ない (4-tuple joint が要る)。**2026-06-09 実態**: `iIndepFun.indepFun_add_add` は現 Mathlib 不在と確定 (決定ログ 5)、`IsStamScalingNoiseHyp` richness predicate は削除済 → 解決は **`hXYZXY` を threaded hypothesis 化** (`ToBridge.lean:240`)、供給は caller が 4-tuple/5-tuple `iIndepFun` を product 構造から構成し `indepFun_prodMk_prodMk`+`comp` で group 和の独立を自己導出 (決定ログ 5 の機構、`EPIDensityForm` の 3-noise lift で実装)。lift route-B B2 (`indepFun_add_add_on_lift`) は DEAD (decl 削除)。

**柱 C: honest precondition は `hpX_mom` (有限分散) + `hpX_ent` (有限エントロピー) のみを thread。**
`IsHeatFlowEndpointRegular` (`EPIG2HeatFlowContinuity.lean:488`) の 8 density-witness field のうち、`pX`/`hpX_nn`/`hpX_meas`/`hpX_law`/`hpX_int`/`hpX_mass` の 6 field は **a.c. + 確率測度から R-N 自動** (case 1 の a.c. 前提で導出可能)。残 2 field `hpX_mom`/`hpX_ent` は a.c. から出ない (方針 X の honest precondition)。これを caller 供給 regularity precondition として signature に thread する。**load-bearing bundling 禁止** — Stam core は producer 側 genuine、consumer は regularity precondition のみ。

**柱 D: `stamToEPIScaling_holds` の over-claim を honest 化。**
`stamToEPIScaling_holds:214` は `measurable X, Y` のみで `IsStamToEPIScalingHyp X Y P` を主張する (前提ゼロ over-claim、無限分散入力で偽の疑い)。Phase 1 で honest 版 signature を確定し、Phase 4 で precondition を追加する (または `isStamToEPIScalingHyp_of_stam_debruijn` 経由構成に置換し、shared sorry を撤去)。

---

## verbatim 確認済の事実 (signature 抽出、predict せず Read 済)

### F1 — G3 rescale carrier は genuine

`csiszarLogRatioGap_antitoneOn_Ici_zero` (`EPIStamToBridge.lean:1085-1166`):
- 結論: `AntitoneOn (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t) (Set.Ici 0)`。
- body は interior `Ioi 0` を `antitoneOn_of_deriv_nonpos` + R-2 (`csiszarLogRatioGap_hasDerivAt`) + R-3 (`csiszarLogRatioGap_deriv_le_zero`) で genuine、端点 `0` を `csiszarLogRatioGap_continuousWithinAt_zero` で insert。**自 sorry 無し** (R-3‴ 案 B closure 済、reframe plan 判断ログ 9, `@audit:ok`)。
- per-`t` bundle `h_pos_stam` が `IsBlachmanConvReady (density_t X) (density_t Y)` を要求 → これは F4 の一般密度 producer で供給可能。

### F2 — `csiszarGap_eq_one_source_via_rescale` の 6 引数 (verbatim)

`EPIL3Integration.lean:1482-1514`。`{s : ℝ} (hs : s ∈ Set.Ico 0 1)` 付きで rescale 等式
`csiszarGap X Y Z_X Z_Y P s = (1 − s) * csiszarGap1Source X Y Z_X Z_Y P (s/(1−s))` を返す。
要求する 6 caller-side 仮説 (rescale パラメータ `√(s/(1−s))`):

| 引数 | 型 (verbatim) |
|---|---|
| `h_ac_sum` | `(P.map (fun ω => X ω + Y ω + Real.sqrt (s/(1−s)) * (Z_X ω + Z_Y ω))) ≪ (volume : Measure ℝ)` |
| `h_ac_X` | `(P.map (fun ω => X ω + Real.sqrt (s/(1−s)) * Z_X ω)) ≪ volume` |
| `h_ac_Y` | `(P.map (fun ω => Y ω + Real.sqrt (s/(1−s)) * Z_Y ω)) ≪ volume` |
| `h_int_sum` | `Integrable (fun x => Real.negMulLog (((P.map (…sum…)).rnDeriv volume x).toReal)) volume` |
| `h_int_X` | `Integrable (fun x => Real.negMulLog (((P.map (…X…)).rnDeriv volume x).toReal)) volume` |
| `h_int_Y` | `Integrable (fun x => Real.negMulLog (((P.map (…Y…)).rnDeriv volume x).toReal)) volume` |

3 ≪ + 3 negMulLog-rnDeriv-integrable。各 `s ∈ Ico 0 1` ごとに供給を要する。**結論は等式 (不等式でない)** → 一方向しか効かないことに注意 (rescale 簿記 `(1−s)`)。

### F3 — `IsHeatFlowEndpointRegular` の 14 field (verbatim)

`EPIG2HeatFlowContinuity.lean:488-503`。`(X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]` 上の structure:

regularity 6 field (a.c. precondition で自動): `hX_meas`, `hZ_meas`, `hXZ_indep`, `v_Z : ℝ≥0`, `hv_Z_pos`, `hZ_law : P.map Z = gaussianReal 0 v_Z`。

density-witness 8 field: `pX : ℝ → ℝ`, `hpX_nn`, `hpX_meas`, `hpX_law : P.map X = volume.withDensity (ofReal ∘ pX)`, `hpX_int : Integrable pX volume`, `hpX_mass : ∫ pX = 1`, **`hpX_mom : Integrable (fun y => y^2 * pX y) volume`** (有限分散), **`hpX_ent : Integrable (negMulLog ∘ pX) volume`** (有限エントロピー)。

⚠ assembly consumer の docstring (`EPIStamToBridge.lean:1307-1309`) は「7 field」と記載するが実 structure は **8 density field** (上記)。consumer site (`:1416`/`:1422`/`:1429`) の sorry も各 8 件 = **計 24 density-witness sorry** (3 instance × 8)。docstring が stale。

### F4 — 一般密度 Blachman producer (false wall を打ち砕く)

`isBlachmanConvReady_convDensityAdd_gaussian` (`EPIBlachmanGeneralDensity.lean:224`):
入力 = pX/pY の regularity (nonneg / Measurable / Integrable / `0 < mass` / `mass = 1`)、`[...]` 型クラス前提無し。結論 = `IsBlachmanConvReady (convDensityAdd pX g_t) (convDensityAdd pY g_t)`。19/19 field genuine、sorryAx-free。F1 の per-`t` bundle の `IsBlachmanConvReady` field を供給する。

### ~~F5 — joint-indep lift 後継 (route-B B2)~~ DEAD (2026-06-09)

~~`indepFun_add_add_on_lift` / `entropy_power_inequality_via_lift` (2-noise lift `Ω×ℝ×ℝ`)~~ — **削除済** (commit `4cd6b12`、external consumer 0)。route-B B2 は不採用 (決定ログ 5 でルート I = in-place 自己導出に確定)。現 3-noise route (`EPIDensityForm`) は base への張替を `entropy_power_inequality_via_lift3` で行い、和 vs 和の独立性は body 内 5-tuple `iIndepFun` から `indepFun_prodMk`/`indepFun_prodMk_prodMk` で抽出 (lift helper 不要)。

### F6 — Mathlib joint-indep lemma (index hit、要 implementer verbatim 確認)

loogle index に `ProbabilityTheory.iIndepFun.indepFun_add_add` (from `Mathlib.Probability.Independence.Basic`) がヒット (Found one)。**ただし現 checkout の Mathlib source では grep 不一致** (index が別 snapshot / 自動生成の疑い) → **本 planner は verbatim signature を抽出できなかった**。`【要 implementer 確認】`: (a) declaration が現 Mathlib に実在するか、(b) signature が `iIndepFun [X, Y, Z_X, Z_Y]` 形 (4-tuple joint) から `IndepFun (X+Y) (Z_X+Z_Y)` を返すか、(c) 型クラス前提 (`[...]`)。実在すれば柱 B の in-place route が成立。

---

## Phase 0 — M0 在庫照合 📋

proof-log: no。コード非編集、verbatim 照合のみ。

- [ ] **0-a**: F6 の `iIndepFun.indepFun_add_add` を **現 Mathlib source で verbatim 確認** (`rg` で declaration を探し、signature + `[...]` 前提を抽出)。見つからなければ近傍 (`iIndepFun.indepFun_add_left/right`, `indepFun_add_add`) を loogle + Read で代替候補化。
- [ ] **0-b**: 6 AC/integrability (F2) の供給元在庫: a.c. 入力 `P.map X ≪ volume` + Gaussian smoothing から `P.map (X + √r·Z) ≪ volume` を出す in-house lemma の有無 (`EPIConvDensity*` / `FisherInfoV2DeBruijn` 系)。`density_t_eq` (`FisherInfoV2DeBruijn.lean:259-260` 付近、`density_t` = `convDensityAdd pX gaussian` pin) が ≪ + negMulLog-integrable を per-`t` 供給するか確認。
- [ ] **0-c**: `IsHeatFlowEndpointRegular` の 6 regularity field が a.c. + 確率測度から自動導出可能か (R-N witness 構成: `Measure.rnDeriv` + `withDensity_rnDeriv_eq` 系)。`hpX_mom`/`hpX_ent` が a.c. のみから **出ない** ことを反例 (heavy-tail a.c. 密度) で再確認 (方針 X precondition の正当化)。
- [x] **0-d** (moot 2026-06-09): ~~`IsStamScalingNoiseHyp` を 4-tuple `iIndepFun` 形に強化 / richness lemma `stamScalingNoise_exists_on_lift` の在庫~~ — predicate + richness lemma 共に削除済。実際の供給は caller 側 inline 自己導出 (決定ログ 5、`EPIDensityForm` 3-noise lift)。

撤退ライン: 0-a で `iIndepFun.indepFun_add_add` が現 Mathlib に **不在** と確定し、かつ近傍 lemma での in-place 導出も infeasible なら、Phase 2 は **lift route-B B2 一択** に確定 (撤退でなく分岐確定)。

---

## Phase 1 — honest signature 確定 📋

proof-log: no。設計のみ。

case 1 closure 後の各 declaration が持つべき **最小 precondition 集合** を確定する。`load-bearing bundling 禁止` を判定軸に、各 precondition が regularity (前提条件) か core (証明核心) かを 1 件ずつ分類。

- [ ] **1-a**: headline `stamToEPIBridge_holds` の honest 版 signature。現状 `IsStamInequalityResidual → IsEntropyPowerInequalityHypothesis` を任意 `X Y P` で主張。方針 X では a.c. × 2 (`P.map X ≪ volume`, `P.map Y ≪ volume`) + `hpX_mom`/`hpX_ent` × {X, Y, X+Y} を precondition に追加する形を確定。`IsHeatFlowEndpointRegular` 丸ごと thread vs `hpX_mom`/`hpX_ent` だけ抜き出し の判定 (推奨: structure 丸ごと thread だと 6 regularity field を caller が組む負担、抜き出しだと structure 再構成の負担 — Phase 0-c の自動導出可否で決める)。
- [ ] **1-b**: `stamToEPIScaling_holds:214` の over-claim 修正方針を 2 択で確定:
  - **(α) precondition 追加**: signature に a.c. + 有限分散/エントロピー precondition を加え、body を `isStamToEPIScalingHyp_of_stam_debruijn` 経由構成に置換 (shared sorry 撤去)。
  - **(β) shared sorry 維持 + classification 訂正**: signature を honest 化 (precondition 追加) しつつ body は sorry のまま `@residual(plan:epi-case1-difference-g3-closure-plan)` に再分類。
  推奨は (α) (over-claim を構造的に消す)。(α) が consumer blast radius 大なら (β) を暫定。
- [ ] **1-c**: precondition の thread 経路 DAG を確定。現 chain: `isStamToEPIScalingHyp_of_stam_debruijn` (`:1324`) → `isStamToEPIBridgeHyp_of_scaling` (`:239`, `@audit:ok`) → headline。各 hop で precondition が regularity のまま透過することを確認 (core を hyp に変えない)。

honesty 判定の言明 (本 plan の不変条件): **Stam core 不等式 (`1/J_sum ≥ 1/J_X + 1/J_Y`) は producer 側 (`stam_step2_density_wall` 経由, `@audit:ok`) で genuine。consumer に渡す precondition は regularity (a.c. / 有限分散 / 有限エントロピー / measurability / IndepFun) のみ**。`IsStamInequalityResidual` / `IsStamToEPIBridge` の predicate を仮説として渡して body 機械展開する形 (load-bearing bundling) は禁止 — これらは reduction (`residual → 結論`) であって hyp bundle でない (`@audit:ok` 既判定) ので現状維持。

---

## Phase 2 — joint-indep `hXYZXY` 閉鎖 ✅ 実態整合 (2026-06-09)

proof-log: yes (`proof-log-epi-case1-g3-phase-2.md`)。

> **2026-06-09 整合済 — 両ルートの decl は削除、`hXYZXY` は threaded hypothesis 化**:
> 下記 ルート I/II の判定 (Phase 0-a) は **決定ログ 5 で ルート I (in-place 自己導出) に確定**したが、
> その後の two-time route 載せ替えで実装が分岐した結果:
> - **`hXYZXY` は sorry でなく threaded hypothesis** になった (`ToBridge.lean:240` 等で
>   `(hXYZXY : IndepFun (X+Y) (Z_X+Z_Y) P)` を引数で受ける honest independence precondition)。
> - **richness predicate `IsStamScalingNoiseHyp` は削除済** (commit `4cd6b12`、code 内残存は削除履歴の
>   docstring 2 件のみ) → ルート I の「predicate 強化」案は moot。
> - **ルート II (lift route-B B2) は DEAD**: `indepFun_add_add_on_lift` / `entropy_power_inequality_via_lift`
>   削除済、`epi-richness-route-b-plan` は CLOSED stub。
> - **live な供給機構 = 決定ログ 5 の自己導出**: caller (例 `EPIDensityForm.entropy_power_inequality_of_density`
>   の 3-noise lift) が 5-tuple `iIndepFun` を product 構造から inline 構成 (`Measure.pi_eq`) し、
>   `indepFun_prodMk_prodMk` + `indepFun_prodMk` で group 独立を抽出して `hXYZXY` 相当 (sum vs noise) を
>   genuine に供給する。`iIndepFun.indepFun_add_add` は現 Mathlib 不在 (決定ログ 5) ゆえ grouping 経由。

下記は当時のルート判定 (履歴、新規着手では上記実態を参照):

### ~~ルート I — in-place under-hyp 修正~~ (decl 削除で moot、自己導出機構のみ live)

- ~~2-I-a/b/c: `IsStamScalingNoiseHyp` 4-tuple 強化 + `iIndepFun.indepFun_add_add` 導出~~ — predicate 削除済。
  自己導出 (`indepFun_prodMk_prodMk`+`comp`、決定ログ 5) は caller 側 inline で live。

### ~~ルート II — lift route-B B2 再配線~~ (DEAD、decl 削除)

- ~~2-II-a/b/c~~ — `indepFun_add_add_on_lift` / `entropy_power_inequality_via_lift` 削除済、route-B plan CLOSED。

blast radius: lift 空間配線は headline chain 全体に波及 (大)。ルート I が成立するなら I を優先。

撤退ライン: 両ルートとも当該 session で infeasible なら `hXYZXY` を `sorry` + `@residual(plan:epi-case1-difference-g3-closure-plan)` で維持 (現 owner `epi-stam-to-conclusion-phaseA-plan` から本 plan に再分類)。signature は本来の `IndepFun (X+Y) (Z_X+Z_Y) P` を保つ。

---

## Phase 3 — G3 rescale assembly 📋

proof-log: yes (`proof-log-epi-case1-g3-phase-3.md`)。

対象: `csiszarGap_antitoneOn_Icc_zero_one` body sorry (`EPIStamToBridge.lean:1289`)。carrier `_h_1source_anti` (genuine ratio antitone, Ici 0) を使い、6 AC/integrability を s∈Ico 0 1 で供給して 2-source difference antitone (Icc 0 1) に持ち上げる。

- [ ] **3-a**: `_h_1source_anti` carrier を body で **実使用** (現状 unused、type-only swap)。ratio antitone (Ici 0) を `csiszarGap_eq_one_source_via_rescale` (F2 等式) 経由で difference 形に変換。M0-3 の scale-invariance (`(1−s)` が log 内で相殺、reframe plan 判断ログ 3) を使い ratio→difference を結ぶ。
- [ ] **3-b**: 6 AC/integrability (F2 の `h_ac_sum/X/Y`, `h_int_sum/X/Y`) を **per-`s ∈ Ico 0 1`** で供給。供給元は Phase 0-b の在庫 (a.c. 入力 + Gaussian smoothing で `P.map (X + √(s/(1−s))·Z) ≪ volume` + negMulLog-rnDeriv-integrable)。これらは a.c. precondition + 一般密度 producer (F4) チェーンから derive 可能なはず — 各 `s` で `r = s/(1−s) > 0` (s∈Ico 0 1 で `1−s > 0`) なので `√r·Z` smoothing が効く。
- [ ] **3-c**: s=1 端点接続。Icc 0 1 の右端 `s=1` は Ico に含まれない (rescale 等式は `s∈Ico 0 1` 限定、`1−s` が分母) → 端点は別途 `csiszarGap_at_one_eq_zero_of_gaussian_pair` (difference 版の genuine Gaussian saturation、`entropyPower_gaussian_additivity` 経由) + 連続性 (`AntitoneOn.insert` 系) で接続。**ここが difference アーキの肝** (s=1 で pure Gaussian → saturate、ratio の t→∞ 壁を回避)。
- [ ] **3-d**: Icc 0 1 全域の `AntitoneOn` を `AntitoneOn (Ico 0 1)` (rescale + ratio carrier) + 端点 `1` insert で組む。

**Mathlib 壁なし、純 assembly。** Stam core も Blachman も新規壁を踏まない (F1/F4 が genuine 供給)。

検算 (Phase 0 で確定すべき): F2 の 6 AC/integrability が「case 1 a.c. precondition + Blachman producer」から本当に per-`s` 供給可能か。`【要 implementer 確認】` 供給に追加 lemma が要る場合 (例: a.c. → smoothed a.c. の Mathlib 不在部) は wall 候補化し `@residual(wall:...)` を検討。現時点の見立ては「`density_t` pin チェーンで供給可能」(Phase 0-b)。

撤退ライン: 6 AC/integrability の per-`s` 供給に Mathlib 壁が露見した場合のみ、当該 AC を `sorry` + `@residual(plan:epi-case1-difference-g3-closure-plan)` で局所化 (carrier antitone と s=1 端点は genuine に保つ)。

---

## Phase 4 — `stamToEPIScaling_holds` honest 化 + 24 density-witness thread 📋

proof-log: yes (`proof-log-epi-case1-g3-phase-4.md`)。

- [ ] **4-a**: 24 density-witness sorry (`EPIStamToBridge.lean:1416-1430`、3 × `IsHeatFlowEndpointRegular` の 8 field) のうち、a.c.-自動の 6 field (`pX`/`hpX_nn`/`hpX_meas`/`hpX_law`/`hpX_int`/`hpX_mass`) を R-N witness 構成 (Phase 0-c) で genuine 化。`P.map X ≪ volume` → `pX := (P.map X).rnDeriv volume |>.toReal` + `withDensity_rnDeriv_eq` で `hpX_law` 等。
- [ ] **4-b**: `hpX_mom`/`hpX_ent` の 2 field × 3 instance = 6 件を **caller 供給 precondition** に thread (Phase 1-a の signature)。`X+Y` instance の `hpX_mom`/`hpX_ent` は X, Y の有限分散・有限エントロピーから convolution 経由で導出するか、これも precondition にするかを判定 (有限分散は加法的 → X+Y の分散は X, Y から自動、有限エントロピーは convolution が entropy を下げないので注意 — Phase 0 で要確認)。
- [ ] **4-c**: `stamToEPIScaling_holds:214` を Phase 1-b の verdict (α/β) に従って honest 化。(α) なら body を `isStamToEPIScalingHyp_of_stam_debruijn` 経由構成に置換し shared sorry 撤去、(β) なら signature に precondition 追加 + sorry を本 plan slug に再分類。
- [ ] **4-d**: `EPIStamToBridge.lean:1307-1309` の stale docstring (「21 density-witness / 7 field」) を「24 density-witness / 8 field」に訂正 (incidental)。

撤退ライン: a.c.-自動 6 field の R-N witness 構成に詰まったら当該 field を `sorry` + `@residual(plan:epi-case1-difference-g3-closure-plan)` で局所化。`hpX_mom`/`hpX_ent` は precondition なので sorry 不要 (caller 供給)。

---

## Phase 5 — headline discharge + `#print axioms` 検証 📋

proof-log: yes (`proof-log-epi-case1-g3-phase-5.md`)。

- [ ] **5-a**: headline `stamToEPIBridge_holds` を Phase 1-a の honest signature (方針 X precondition 付き) で genuine discharge。chain: scaling 述語 (`stamToEPIScaling_holds` honest 版) → `isStamToEPIBridgeHyp_of_scaling` (`@audit:ok`) → bridge。
- [ ] **5-b**: case 1 entry point (`entropy_power_inequality_unconditional` の case 1 ブランチ、umbrella Phase 5 の `entropyPowerExt_add_ge_dispatch_skeleton`) を headline 経由で配線。case 1 sorry が消えることを確認。
- [ ] **5-c**: `#print axioms stamToEPIBridge_holds` (+ case 1 ブランチ) が `[propext, Classical.choice, Quot.sound]` (sorryAx-free) であることを機械確認。残 sorry が方針 X precondition のみ (load-bearing でない regularity) であることを確認。
- [ ] **5-d**: 独立 honesty-auditor 起動 (orchestrator 責務、CLAUDE.md「Independent honesty audit」)。新規 `sorry` 除去 + signature honesty + precondition classification を fresh subagent で verify。

撤退ライン: headline が方針 X precondition で閉じても、case 1 が真の `_unconditional` (precondition ゼロ) にならない点は **方針 X の honest 限界** (方針 Y は genuine walled)。`*_unconditional` 命名は禁止 (name laundering)、`*_of_finite_variance` 等の honest 命名を使う。

---

## 依存順序 DAG (並列可能性)

```
Phase 0 (M0 照合) ──┬─→ Phase 1 (signature 確定) ──┐
                    │                              ├─→ Phase 4 (density-witness + over-claim) ─→ Phase 5 (headline)
                    ├─→ Phase 2 (joint-indep) ─────┤
                    └─→ Phase 3 (G3 rescale) ──────┘
```

- **Phase 2 と Phase 3 は独立並列可能** (joint-indep 閉鎖と G3 rescale は別 declaration、Phase 0 完了後)。並列 implementer dispatch 候補。
- Phase 3 は Phase 2 の `hXYZXY` を carrier antitone (`csiszarLogRatioGap_antitoneOn_Ici_zero`) の引数に取るが、**carrier は既に genuine** で `hXYZXY` を hyp として受け取る形 (`:1090`) → Phase 3 は `hXYZXY` を仮定として使え、Phase 2 の完了を待たずに並列着手可。最終結線 (Phase 5) で両者を合流。
- **Phase 4 は Phase 1 (signature) + Phase 2 (`hXYZXY` for X+Y instance の `hXZ_indep`) に依存**。
- Phase 1 は Phase 0 完了後すぐ着手可 (設計のみ)。
- **並列推奨**: Phase 0 完了 → {Phase 1, Phase 2, Phase 3} を並列 → Phase 4 → Phase 5。

---

## 撤退ライン共通規律

- 各 Phase の撤退口は `sorry` + `@residual(plan:epi-case1-difference-g3-closure-plan)` のみ (本 slug に統一)。`@residual` slug は本 plan filename stem (`epi-case1-difference-g3-closure-plan`) に揃える。現 owner `epi-stam-to-conclusion-phaseA-plan` の sorry は本 plan が引き取る (再分類)。
- **禁止**: `*Hypothesis` predicate に Stam core を bundling / `Prop := True` slot / 仮説型≡結論の `:= h` / 退化定義悪用。precondition は regularity (a.c. / 有限分散 / 有限エントロピー / measurability / IndepFun) のみ。
- 6 AC/integrability の供給に **真の** Mathlib 壁が露見した場合のみ新 wall 候補化 (loogle 0 件確認 → audit-tags.md register 追記)。現時点の見立ては「壁なし、assembly」。
- 方針 X precondition (`hpX_mom`/`hpX_ent`/a.c.) は **honest 到達点** であり撤退ではない (方針 Y は genuine walled、method-y-lsc-recheck 確定)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-06-05 起草) false-wall 発見を受けて case 1 difference G3 closure plan を起草**: 親 umbrella Phase 3 の「両ルート walled」park は 2 つの誤前提に立っていた — (i) `wall:blachman-general-density` が false wall (一般密度 producer `isBlachmanConvReady_convDensityAdd_gaussian` 実在、recheck inventory)、(ii) difference G3 が「削除済 false-as-framed D3/D6 のもつれ」という判定は誤りで、実際は genuine ratio antitone carrier (`csiszarLogRatioGap_antitoneOn_Ici_zero`, sorryAx-free) + rescale assembly のみ (reframe plan 判断ログ 10 の verbatim 訂正)。⇒ case 1 の真の残壁は **entropic CLT でも Blachman でもなく、(a) 6 AC/integrability の per-`s` uniform 供給 + s=1 端点接続 = pure assembly、(b) joint-indep under-hyp、(c) density-witness の precondition thread** に分解される。方針 Y は genuine walled (method-y-lsc-recheck) ゆえ honest 到達目標は **方針 X** (a.c. + 有限分散 + 有限エントロピー precondition)。
2. **(2026-06-05) `stamToEPIScaling_holds:214` の over-claim を honesty 懸念として明示**: 前提ゼロ (`measurable X, Y` のみ) で `IsStamToEPIScalingHyp` を主張する shared sorry は、genuine assembly が regularity precondition を要するのに無前提主張 = over-claim の疑い (無限分散入力で偽)。Phase 1-b で honest 版 signature を確定し Phase 4-c で修正 (precondition 追加 or `_of_stam_debruijn` 経由構成への置換)。黙認せず構造的に消す方針。
3. **(2026-06-05) joint-indep `hXYZXY` の 2 ルート判定を Phase 0-a に委譲**: Mathlib `iIndepFun.indepFun_add_add` が loogle index にヒットするが現 checkout source で grep 不一致 → planner は verbatim signature を抽出不能、implementer に verbatim 確認を委譲 (`【要 implementer 確認】`)。実在すれば in-place under-hyp 修正 (ルート I、`IsStamScalingNoiseHyp` を 4-tuple joint に強化)、不在なら lift route-B B2 (ルート II、`indepFun_add_add_on_lift` genuine)。blast radius は I < II (lift 配線は headline chain 全体波及) ゆえ I 優先。
4. **(2026-06-05) F3 docstring stale を記録**: assembly consumer docstring (`EPIStamToBridge.lean:1307-1309`) は「21 density-witness / 7 field」と記すが実 structure `IsHeatFlowEndpointRegular` は **8 density field** (`hpX_ent` 含む)、consumer sorry は **24 件** (3×8)。Phase 4-d で incidental 訂正。fabricate 防止のため本 plan は実 structure (`EPIG2HeatFlowContinuity.lean:488-503`) を SoT とする。

6. **(2026-06-05、Phase 3 implementer sufficiency finding) difference G3 carrier は target に対し insufficient**: `csiszarGap_antitoneOn_Icc_zero_one` の carrier `_h_1source_anti` は **ratio** 形 `AntitoneOn(csiszarLogRatioGap)(Ici 0)` だが、target は **difference** 形 `AntitoneOn(eP(sum)−eP(X)−eP(Y))(Icc 0 1)`。rescale 等式 `csiszarGap_eq_one_source_via_rescale` は difference-2-source を difference-**1**-source に繋ぐのみで ratio には繋がらない。`csiszarGap1Source(t) = (N_X+N_Y)·(exp R(t)−1)` で `N_X+N_Y` が t 増加 ⇒ `antitone(ratio) ⊬ antitone(difference)` (sufficiency gap、honesty check 4 で検出)。genuine な difference-1-source antitone (旧 D6) は false-as-framed D3 依存で削除済・後継なし。⇒ **difference G3 経路 (本 plan の当初 Phase 3) は現 carrier 設計では closure 不能**。`csiszarGap_antitoneOn_Icc_zero_one:1289` の sorry は `@residual(plan:epi-case1-difference-g3-closure-plan)` に再分類 (commit `cc6da87`)。Blachman false-wall 発見は per-`t` precondition には効くが、headline closure はこの ratio↔difference 接合点で別途 block。

7. **(2026-06-05、orchestrator 新ルート発見 = ratio + スケーリング挟み撃ち、要独立検証→実装) entropic CLT を回避する飽和ルート**: difference を経由せず、**genuine ratio antitone を直接使う**。`epi_of_csiszarLogRatioGap_zero_nonneg` (genuine) より `R(0) ≥ 0 ⟹ EPI`。`csiszarLogRatioGap_antitoneOn_Ici_zero` (genuine, Ici 0) より `R(0) ≥ R(t) ∀t≥0`。よって `R(t) → 0 (t→∞)` を示せば `R(0) ≥ lim = 0`。**核心**: `R(t)→0` は entropic CLT 不要で、スケーリング恒等式 `entropyPower_map_mul_const` (`N(μ.map(·*c))=c²N(μ)`, c=√t) により `N(law(X+√t·Z)) = t·N(law(X/√t+Z))`。R(t) の t 因子が log 内で相殺し `R(t) = log N(W_sum(t)) − log(N(W_X(t))+N(W_Y(t)))`、`W_X(t)=X/√t+Z_X` 等。各 `N(W(t))` は **挟み撃ちで収束**: (下界) `N(W_X(t))=N(Z_X+X/√t) ≥ N(Z_X)` (独立ノイズ加算で entropy 増、**case-2 補題 `differentialEntropy_add_ge_of_indep` (EPIUncondMixedCase.lean、genuine)**)、(上界) `N(W_X(t)) ≤ 2πe·(Var X/t + 1)` (**最大エントロピー `differentialEntropy_le_gaussian_of_variance_le`**、`Var(W_X(t))=Var X/t+1 → 1`)。⇒ `N(W_X(t)) → N(Z_X)`、同様に W_Y/W_sum。`N(Z_X+Z_Y)=N(Z_X)+N(Z_Y)` (`entropyPower_gaussian_additivity`、Z 標準正規) より `R(∞)=0`。**この挟み撃ちが entropic CLT を不要にする鍵** (分布収束→entropy 収束の一般持ち上げでなく、独立ノイズ単調性 + 分散→1 の max-ent で両側 bound)。`Var X < ∞` = **方針 X precondition** (整合)。Blachman 発見はここで genuine に効く (case-2 補題の 8 integrability は Gaussian 平滑 W path で Blachman/entropy-finiteness CLOSED 機械から供給)。**要独立検証**: 各 ingredient の verbatim signature + case-2 補題 precondition の供給可能性 + parametrization 整合。検証後 Phase 3 を本ルートに差替え (旧 difference G3 は park)。

8. **(2026-06-05、独立 advisor 検証) 新 ratio+scaling 挟み撃ちルートを Partial GO で確認 → Phase 3 を本ルートに差替え (旧 difference G3 park)**: proof-pivot-advisor が判断ログ 7 のルートを verbatim 検証。**verdict: genuine かつ entropic CLT 回避を確認**。全 ingredient 実在 (verbatim、file:line):
   - `entropyPower_map_mul_const` (`EPIPlumbing.lean:136`、genuine。要 `[IsProbabilityMeasure]`/`c≠0`/`h_ent_int` = 非スケール law の entropy 可積分性)
   - `csiszarLogRatioGap` path 形 = `X+√t·Z` (`EPIL3Integration.lean:1380`、W 簡約方向と整合)、`csiszarLogRatioGap_at_zero` (`:1391` genuine)、`epi_of_csiszarLogRatioGap_zero_nonneg` (`EPIStamToBridge.lean:985` genuine)
   - 下界 `differentialEntropy_add_ge_of_indep` (`EPIUncondMixedCase.lean:76` `@audit:ok`、ただし 8 integrability precondition)
   - 上界 `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:520` genuine、要 `μ≪volume`/`h_ent_int`)、分散加法性 `IndepFun.variance_add` (Mathlib)
   - `entropyPower_gaussian_additivity` (`EntropyPowerInequality.lean:333` `@audit:ok`) で `R(∞)=0`
   - squeeze `tendsto_of_tendsto_of_tendsto_of_le_of_le` + `ge_of_tendsto` (Mathlib、確認済)
   - **architectural win**: 本ルートは ブロック中の `csiszarGap_antitoneOn_Icc_zero_one` (difference、判断ログ 6) を **critical path から完全に bypass** し、genuine ratio antitone (`csiszarLogRatioGap_antitoneOn_Ici_zero:1085`) + 新 limit lemma で `R(0)≥lim R(t)=0` を直接組む。旧 NO-GO (`epi-case1-ratio-limit-plan.md`) は √t スケーリング簡約を omit した over-pessimism。本ルートは file 内 `EPIStamToBridge.lean:1275-1276` の "route (b)" として既に名前だけ存在していた。
   - **relocated wall (honest)**: step 3/4 が要する W-path (`Z + input/√t` = Gaussian 平滑) の entropy 可積分性 + 8 fibre integrability は、既存 21 density-witness sorry (`IsHeatFlowEndpointRegular`、`@residual(plan:epi-stam-to-conclusion-phaseA-plan)`) と同 family。a.c. は `map_add_absolutelyContinuous` (EPIUncondMixedCase) / `Measure.conv_absolutelyContinuous` で供給可能だが、`P.map(Z+input/√t)` を `convDensityAdd` 形に同定する bridge + entropy 可積分性 (`wall:entropy-finiteness` CLOSED 資産 `convDensityAdd_negMulLog_integrable`) の配線は要 implementer 確認。これらは **regularity precondition (方針 X、非 load-bearing)** ゆえ honest 撤退口は `sorry + @residual(plan:...)`。
   - **実装プラン (advisor 推奨)**: (1) NEW `csiszarLogRatioGap_tendsto_zero_atTop : Tendsto (R ·) atTop (𝓝 0)` = genuine 新解析補題 (scaling 簡約 ×3 + t 因子相殺 `Real.log_mul` + squeeze + Gaussian 加法性)。(2) NEW `epi_of_csiszarLogRatioGap_tendsto` = antitone + `R(t)→0` ⟹ `R(0)≥0` (order limit)、`epi_of_csiszarLogRatioGap_zero_nonneg` に chain。(3) ratio antitone は reuse。**第一歩** = (1) を skeleton 化し scaling 簡約の have を別 sorry に、t 因子相殺 `log(t·N)−log(t·N')=log N−log N'` (`Real.log_mul`, t>0, N>0、`entropyPower_pos`) の type-check を確認。per-t integrability は honest precondition として signature に thread (供給は後続 or sorry+@residual)。
   - advisor 気づき (t=1 ショートカット `csiszarLogRatioGap_at_one_eq_zero`) は **Gaussian 入力限定** (一般入力で `X+Z_X` 非 Gaussian ⇒ R(1)>0、Cramér) ゆえ dead end (reframe plan R-4 で既 refuted)。t→∞ squeeze が正道。

9. **(2026-06-05、implementer landing + orchestrator 依存分析) 解析核 landing + case-1 が regularity plumbing に還元**: implementer が `InformationTheory/Shannon/EPICase1RatioLimit.lean` を新規 landing (commit `32235a6`)。**4 declaration 中 3 つ own-body 0 sorry (genuine)**: `epi_of_csiszarLogRatioGap_tendsto` (order limit → EPI)、`entropyPower_path_scaling` (scaling 相殺核、`Measure.map_map` + `entropyPower_map_mul_const` + `Real.sq_sqrt`)、`csiszarLogRatioGap_tendsto_zero_atTop` (主定理、t 因子相殺 `Real.log_mul` + 3-path 極限合成 + Gaussian 加法性 + log 連続性)。**残 sorry 1 件** = §3 `entropyPower_rescaled_path_tendsto` (per-path squeeze、`@residual(plan:epi-case1-difference-g3-closure-plan)`)。**entropic CLT NO-GO を覆す saturation architecture が genuine に landing**。
   - **依存分析 (orchestrator、ratio antitone signature `:1085-1122` verbatim)**: 新ルートは genuine ratio antitone `csiszarLogRatioGap_antitoneOn_Ici_zero` を carrier に使うが、それは **`hXYZXY` (joint-indep) + 3×`IsHeatFlowEndpointRegular` (density-witness、`hpX_mom`/`hpX_ent` = 方針X) + `h_pos_stam` per-t bundle (Fisher 正値 + Stam + RegularDensity + ∫=1 + conv-id + `IsBlachmanConvReady`)** を hypothesis として要求 (lemma 自体は genuine、precondition thread)。⇒ **新ルートは OLD difference route の sorry を bypass せず継承する**。だが決定的差: 削除済 false difference-1-source antitone への依存が消え (sufficiency gap 解消)、s=1 端点 (= entropic CLT) が **genuine な R(t)→0 squeeze に置換**された。
   - **⇒ case-1 closure は entropic CLT 壁から「regularity plumbing」に還元**: 残るは全て方針X regularity の供給/thread であって Mathlib 壁でない: (A) §3 squeeze closure (case-2 補題 8 fibre integrability + max-ent `h_ent_int` + `IndepFun A B` + 有限 Var A)、(B) ratio antitone の precondition 供給 (`hXYZXY` = self-derive ルート I 判断ログ 5、density-witness = a.c.+方針X、`h_pos_stam` の Blachman = false-wall 解消で供給可 `isBlachmanConvReady_convDensityAdd_gaussian`)、(C) headline 結線 (Phase 5、ratio antitone + R(t)→0 + `epi_of_csiszarLogRatioGap_tendsto` → EPI、方針X precondition thread)。
   - **残 roadmap (依存順)**: §3 squeeze (A) → ratio antitone precondition 供給 (B) → headline 結線 (C)。(A)(B) は独立並列可。全て honest regularity、entropic CLT 不要。

5. **(2026-06-05、orchestrator Phase 0-a 実施) F6 verdict 確定 = ルート I (in-place 自己導出)**: 現 Mathlib checkout (rev `043e9e0413`、`.lake/packages/mathlib/Mathlib/Probability/Independence/Basic.lean`) を直接 grep — `iIndepFun.indepFun_add_add` / `indepFun_add_left/right` は **全て不在** (loogle index は新 snapshot 由来で source と不一致、planner の F6 懸念が的中)。乗法版 `iIndepFun.indepFun_mul_mul` (`:913`) は存在するが加法版なし。**ただし grouping machinery は現 source にあり**: `iIndepFun.indepFun_prodMk_prodMk` (`:862`)、`iIndepFun.indepFun_finset` (`:839`)、`IndepFun.comp` (`:799`)。⇒ 4-tuple `iIndepFun ![X, Y, Z_X, Z_Y] P` を {X,Y}/{Z_X,Z_Y} に group 分割 (`indepFun_prodMk_prodMk`) → 各 group を和 `(a,b)↦a+b` に `IndepFun.comp` で写す自己導出で `IndepFun (X+Y) (Z_X+Z_Y) P` が得られる (absent な `indepFun_add_add` に依存しない)。**Phase 2 はルート I 確定** (lift route-B B2 は不要、blast radius 小)。要件 = `IsStamScalingNoiseHyp` を 4-tuple `iIndepFun` 供給形に強化 + EPI 前提 `X⊥Y` を thread (case-1 EPI は元々 `hXY` を持つので自然)。`indepFun_prodMk_prodMk` の verbatim signature (`[...]` 前提) は実装時に Read で確認 (本 verdict は declaration 実在 + grouping 経路成立まで)。
