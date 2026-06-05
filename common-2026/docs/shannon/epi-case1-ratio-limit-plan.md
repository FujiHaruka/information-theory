# EPI case 1 (両 a.c. = 古典 EPI): ratio chain の t→∞ 極限経路 feasibility 査定

> **Parent**: [`epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md) §Phase A-close
>   (headline `stamToEPIBridge_holds` の hard core = case 1 両 a.c.)。
> **関連**: [`epi-csiszar-ratio-reframe-plan.md`](epi-csiszar-ratio-reframe-plan.md)
>   (ratio atom R-2/R-3/R-4/R-5 の SoT、判断ログ 10 = 本査定の発端)。
> **slug**: `epi-case1-ratio-limit-plan`。
>   GO なら新規 atom `csiszarLogRatioGap_tendsto_zero_atTop` の `@residual` slug を本 slug に揃える。

<!--
記法: moonshot-plan-template と同じ (状態絵文字 📋/🚧/✅/🔄、~~取り消し線~~、判断ログ append-only)。
proof-log: no (本ファイルは feasibility 査定 + 条件付き設計。実装着手時に別途 proof-log)。
-->

---

## ⛔ Feasibility verdict — **NO-GO (case 1 park 継続)**

**結論**: ratio chain の「t→∞ 極限経路」で case 1 (両 a.c. = 古典 1-D EPI) を閉じる路は、**真の Mathlib
壁 (= 新 wall `entropy-power-clt-limit` 候補) に直撃するため当該経路では closure 不能**。case 1 は
park 継続を推奨する。本線は **S2 → Phase 5 (difference-form の G3 rescale 6-AC/integrability 供給)** に
集中させるのが正しい (理由 → §「park 継続 + 本線推奨の根拠」)。

**最大の根拠 (= brief 問い 1 の答え)**:

- 欠けている極限補題 `csiszarLogRatioGap X Y Z_X Z_Y P t → 0 (t→∞)` は、数学的には **真** (convolution
  path `X+√t·Z` は t→∞ で Gaussian が支配 → 漸近 Gaussian → entropy power が EPI 等号に漸近)。
  **しかしその証明には「entropy power / 微分エントロピーの t→∞ 漸近収束」が要り、これが Mathlib にも
  in-tree にも不在の genuine 壁**である (verbatim 確認、§問い 1)。
- Mathlib が供給する中心極限定理 (`Mathlib/Probability/CentralLimitTheorem.lean`,
  `tendstoInDistribution_inv_sqrt_mul_sum_sub`) は **convergence in distribution (分布収束、Lévy /
  特性関数経由) のみ**。**微分エントロピー / entropy power の収束は与えない**。entropy は分布収束に対し
  連続でない (lower-semicontinuous でしかなく、漸近 Gaussian でも entropy が極限に収束する保証は別途
  上界 + 下界 sandwich を要する) ため、CLT を引いても `r(t)→0` は出ない。
- これは「選択 (big) を blocked (hard) と偽る」誤用ではない: loogle で
  `InformationTheory.Shannon.entropyPower, Filter.Tendsto` = **0 件**、
  `InformationTheory.Shannon.differentialEntropy, Filter.Tendsto` = **0 件** (2026-06-05 確認)。
  in-tree の `differentialEntropy_gaussianReal_heat_path` (`FisherInfoV2DeBruijn.lean:412`) は
  **X が既に Gaussian の場合限定** の閉形であり、一般 (非 Gaussian) input の convolution には適用不可。
  一般 input の `h(X+√t·Z)` は finite t で閉形を持たず、その t→∞ 漸近も machinery 不在。

verdict は NO-GO だが、本査定は **「park 継続の積極的根拠 + 本線リソース集中の判断材料」を確定する正の
出力**である (brief の「NO-GO は valid な出力」)。

---

## 査定対象と背景 (2026-06-05 確定事実、verbatim 確認済)

### case 1 = headline の hard core

case 1 (両 a.c.) EPI = headline `stamToEPIBridge_holds` (`EntropyPowerInequality.lean:249`) の hard core。
現状の **difference-form 経路** は詰まっている (親 plan §re-assessment G1〜G4 + 判断ログ 10):

- 現アーキ: assembly `isStamToEPIScalingHyp_of_stam_debruijn` (`EPIStamToBridge.lean:1324`) が
  difference-form scaling predicate を作り、bridge body `isStamToEPIBridgeHyp_of_scaling`
  (`:235`、`@audit:ok`) が difference antitone から EPI を復元。
- 詰まり: difference-form の G3 rescale `csiszarGap_antitoneOn_Icc_zero_one` (`:1270`、`sorry`
  `@residual(plan:epi-stam-to-conclusion-phaseA-plan)`) は rescale 恒等式
  `csiszarGap_eq_one_source_via_rescale` 経由で `s∈Ico 0 1` ごとに 6 AC/integrability 仮説を供給する組立を
  要する (verbatim: `:1270-1290` の body は `sorry`、carrier 引数 `_h_1source_anti` は ratio antitone に
  型 swap 済だが body 内では未使用 = type-only swap)。

### ratio chain は genuine atom が 3 本揃っている (verbatim 確認)

| atom | file:line | 状態 (verbatim) | 結論形 |
|---|---|---|---|
| ratio antitone | `EPIStamToBridge.lean:1085` | `csiszarLogRatioGap_antitoneOn_Ici_zero`、genuine assembly。**`AntitoneOn (… csiszarLogRatioGap …) (Set.Ici 0)`** (= 全 ray `[0,∞)`)。transitive に G2 continuity 壁 (R-5-b) + plain-Stam 抽出 (R-3) を継承するが assembly 自体は genuine | `AntitoneOn (fun t => csiszarLogRatioGap X Y Z_X Z_Y P t) (Set.Ici 0)` |
| ratio→EPI 橋 | `EPIStamToBridge.lean:985` | `epi_of_csiszarLogRatioGap_zero_nonneg`、**genuine — no sorry, no load-bearing hypotheses** (docstring `:984` verbatim)。`Real.log_le_log_iff` で `r(0)≥0 ⟺ EPI` | `0 ≤ csiszarLogRatioGap … 0 → eP(X+Y) ≥ eP X + eP Y` |
| ratio t=0 値 | `EPIL3Integration.lean:1391` | `csiszarLogRatioGap_at_zero`、genuine (`unfold` + `Real.sqrt_zero` simp) | `csiszarLogRatioGap … 0 = log(eP(X+Y)) − log(eP X + eP Y)` |

これらを直列すると EPI 復元路は:

```
csiszarLogRatioGap_antitoneOn_Ici_zero  (AntitoneOn (Ici 0))
        │   r(0) ≥ r(t)  ∀ t ≥ 0   (antitone)
        │
   [MISSING]  r(t) → 0  as t → ∞    ◀──── 欠けている唯一の atom
        │
        ▼   r(0) ≥ lim r(t) = 0  ⇒  r(0) ≥ 0
epi_of_csiszarLogRatioGap_zero_nonneg  →  EPI  (genuine)
```

antitone の domain が `Set.Ici 0` (全 ray) である点は **t→∞ 経路に好都合** (closed interval `Icc 0 1` では
ない)。antitone + 極限 `lim_{t→∞} r(t)=0` から `r(0) ≥ 0` は純 order 議論で出る。**唯一の欠落は
`csiszarLogRatioGap_tendsto_zero_atTop` 1 本**。

### なぜ t=1 でなく t→∞ か (verbatim 確認、reframe plan 判断ログ 10)

`csiszarLogRatioGap_at_one_eq_zero` (`EPIL3Integration.lean:1426`) は端点 `t=1` で `r(1)=0` を出すが、
**`hLawX : P.map (X+Z_X) = gaussianReal m₁ v₁` / `hLawY` を要求** = `X+Z_X`・`Y+Z_Y` が **Gaussian で
あることが前提** (verbatim: `:1432-1433` の hLawX/hLawY binder)。一般入力 `X,Y` では `X+Z_X` は非 Gaussian
→ `r(1)=0` は一般入力で成立しない (consumer 0 件、bridge 適用不能)。convolution path `X+√t·Z` は **t→∞ で
しか saturate しない** (t=1 は pure Gaussian 端点ではない)。よって case 1 を ratio で閉じるには
`t=1` でなく **`t→∞`** の極限補題が必須。これが本査定の核心問い。

---

## 査定核心 — 3 問の verdict

### 問い 1 — `csiszarLogRatioGap … t → 0 (t→∞)` は Mathlib で示せるか? ⛔ **NO (genuine 壁)**

**数学的真偽**: 真。convolution path `X+√t·Z` (Z 標準正規) は t→∞ で variance-t Gaussian が支配し、
正規化後 (`/√t`) 漸近標準 Gaussian。entropy power の scaling
(`entropyPower_map_mul_const`、`EPIPlumbing.lean:32`、`eP(μ.map(·*c)) = c²·eP μ`) で `c²=1/t` 因子を
整理すると、3 path がいずれも漸近的に同一 Gaussian に支配され `N_sum/(N_X+N_Y) → 1`、よって
`r(t) = log N_sum − log(N_X+N_Y) → log 1 = 0`。これは古典 EPI の standard heat-flow saturation 議論。

**Mathlib 道具立ての査定** (verbatim 確認):

| 必要な道具 | Mathlib / in-tree 在庫 | 判定 |
|---|---|---|
| (a) entropy power / 微分エントロピーの **t→∞ 漸近収束** (`differentialEntropy(P.map(X+√t Z)) − (1/2)log(2πe t) → 0` 等) | **不在**。loogle `InformationTheory.Shannon.entropyPower, Filter.Tendsto` = 0 件 / `… differentialEntropy, Filter.Tendsto` = 0 件 (2026-06-05) | ⛔ 壁 |
| (b) 漸近 Gaussian / scaling (中心極限定理的) | `Mathlib/Probability/CentralLimitTheorem.lean` `tendstoInDistribution_inv_sqrt_mul_sum_sub` は **分布収束のみ** (Lévy 連続性 / 特性関数経由)。**entropy / entropy power の収束は与えない** | △ 分布収束はあるが entropy 収束には不十分 |
| (c) 一般 input の `h(X+√t·Z)` 閉形 (finite t) | **不在**。in-tree `differentialEntropy_gaussianReal_heat_path` (`FisherInfoV2DeBruijn.lean:412`) は **X が既に Gaussian 限定** (`gaussianReal m (v+⟨s,_⟩)` の入力前提)。非 Gaussian convolution に適用不可 | ⛔ 壁 |

**致命傷 = entropy の分布収束に対する非連続性**: 仮に Mathlib CLT で `P.map((X+√t Z)/√t) → 𝒩(0,1)`
(分布収束) が取れても、**微分エントロピーは分布収束に対して連続でない** (一般には下半連続性しかない)。
`r(t)→0` を出すには `h(X+√t Z) − h(Gaussian) → 0` の収束が要り、これは分布収束より strictly strong な
**entropy 収束 (= max-entropy 上界 + 下界 sandwich を t-一様に取る)** を要求する。この entropy 収束は
Mathlib・in-tree 双方に machinery 不在 (上記 (a)(c))。

→ **新 wall 候補 `entropy-power-clt-limit`** (一般 input の convolution path に対する entropy power の
t→∞ Gaussian-saturation 収束)。これは EPI G2 端点連続性 (`wall:heatflow-continuity`、CLOSED) や
`approx-identity-L1` (CLOSED) とは別 semantic: 後者は **t→0⁺** の端点収束 (Gaussian 核が消えて pX に戻る)、
本壁は **t→∞** の漸近 Gaussian saturation (Gaussian 核が支配)。方向が逆で、t→∞ 側は CLT-grade の
entropy 収束を要する点で質的に重い (G2 端点が approx-identity だったのに対し、t→∞ は entropic CLT)。

**verdict**: ⛔ **genuine 壁**。case 1 を ratio t→∞ 経路で閉じるのは moonshot 規模 (entropic CLT を
in-tree で構築する作業) であり、現 frontier の closure 経路として推奨しない。

### 問い 2 — richness (noise 存在) は供給できるか? ✅ **YES (route-B B2 trigger 発火済)**

ratio antitone `csiszarLogRatioGap_antitoneOn_Ici_zero` (`:1085`) は引数に noise witness
(Z_X, Z_Y standard normal + joint indep) を要する。供給元 = `epi-richness-route-b-plan` (B1 done、
lift machinery 4 lemma 全 `@audit:ok`)。

**重要**: route-B plan は「B2 trigger = G2 closure」と書いていた (同 plan 判断ログ 1)。**G2
(`wall:heatflow-continuity` / `approx-identity-L1` / `cond-diff-entropy`) は 2026-06-05 に全 CLOSED**
(`docs/audit/audit-tags.md` Wall name register 確認)。よって **route-B B2 trigger は既に発火している** —
in-place re-wire で偽 W2 を完全除去できる条件が整った。richness は本査定の NO-GO 要因ではない (✅ 供給可)。

> ⚠ これは本査定の副次発見 (気づき欄参照)。richness 自体は case 1 のボトルネックではないが、B2 trigger
> 発火は richness/headline ラインの状態更新を要する事実。

### 問い 3 — density witness (a.c. core 前提) は供給できるか? ✅ **YES (regularity precondition として honest)**

case 1 は両 a.c. なので入力 density witness は a.c. 仮定から供給可能。傘 plan 柱 3
(`IsHeatFlowEndpointRegular` の 8 field を a.c.+有限分散+有限エントロピーから) として、方針 X regularity
precondition で honest に残せる (load-bearing でない、`isStamToEPIScalingHyp_of_stam_debruijn` docstring
`:1316-1319` で「a.c. 入力の density witness は genuine precondition、Measurable X + IsProbabilityMeasure
からは導出不能」と既に `@audit` 分類済)。✅ 供給可。

**3 問総合**: 問い 2/3 は ✅ 供給可。**唯一の閉塞は問い 1 (t→∞ entropy 収束壁)**。ratio chain の他の
部品は全て揃っているのに、t→∞ 極限 1 本が moonshot 規模の壁であるため、経路全体が NO-GO。

---

## park 継続 + 本線推奨の根拠

### なぜ case 1 ratio t→∞ を park 継続するか

1. **t→∞ entropy 収束は entropic CLT 級の独立 moonshot**。問い 1 の壁
   (`entropy-power-clt-limit` 候補) は分布収束 (Mathlib 既存) から entropy 収束への持ち上げを要し、
   一般 input の微分エントロピー漸近形を in-tree で構築する大工事。現 frontier の closure 1 本のコストとして
   見合わない。
2. **difference-form 側に既に正しいアーキがある**。reframe plan 判断ログ 10 の verbatim 訂正の通り、
   一般入力の genuine saturation は **difference-form** (`heatFlowPath2 X Z s = √(1-s)X+√s Z`、s=1 で
   pure `Z` → `entropyPower_gaussian_additivity` genuine、`EntropyPowerInequality.lean:331`) が正しい
   アーキで、それが現 bridge body `isStamToEPIBridgeHyp_of_scaling` (`@audit:ok`) の経路。difference は
   `Icc 0 1` の **有限端点 s=1** で pure Gaussian に到達するため t→∞ 極限を要さない。ratio はこの
   pure-Gaussian 端点を持たない (t=1 が Gaussian でない、問い 1 冒頭) ため、t→∞ に追いやられ壁に当たる。
3. **ratio atom は無駄にならない**。R-2/R-3/R-4-b/R-5-c は genuine closed のまま残り、将来 entropic CLT が
   Mathlib に入った時点で本経路を復活できる (park = 削除ではない)。

### なぜ本線を S2 → Phase 5 (difference G3 rescale) に集中させるか

case 1 の headline closure の残ボトルネックは **G3 rescale** = `csiszarGap_antitoneOn_Icc_zero_one`
(`EPIStamToBridge.lean:1270`、`sorry`)。これは:

- difference アーキ (s=1 で pure Gaussian saturation、t→∞ 不要) に乗っており、壁は **`s∈Ico 0 1`
  ごとの 6 AC/integrability 仮説の uniform 供給** = assembly 作業 (reframe plan 判断ログ 10 の選択肢 (a))。
- 親 plan の closure target G3 として既に scope 化済 (§Phase A-close G3 行)。
- t→∞ entropy 収束壁を **回避する** (difference は finite 端点)。

よって本線は **difference-form G3 rescale の 6-AC/integrability 供給 (= 親 plan Phase A-close G3 /
S2→Phase 5)** に集中するのが、t→∞ 壁を踏まずに case 1 headline へ最短で寄与する。ratio t→∞ は park。

---

## Approach (NO-GO のため設計は park、復活時の条件付き設計のみ記載)

本 verdict は NO-GO のため end-to-end closure の実装設計は起こさない。**将来 entropic CLT 壁
(`entropy-power-clt-limit`) が closure された場合の復活設計**を条件付きで残す (park からの reactivation
ガイド)。

### 復活時の全体形 (条件: `csiszarLogRatioGap_tendsto_zero_atTop` が genuine 化された後)

新規 atom 1 本を建てれば end-to-end が閉じる:

```lean
-- 新規 atom (現状は entropic CLT 壁、NO-GO の主因)
theorem csiszarLogRatioGap_tendsto_zero_atTop
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Y Z_X Z_Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_ac_X : …)   -- case 1 両 a.c. precondition (問い 3、honest regularity)
    (h_ac_Y : …)
    (h_noise : …)  -- route-B 供給 (問い 2、✅)
    … :
    Filter.Tendsto (fun t : ℝ => csiszarLogRatioGap X Y Z_X Z_Y P t)
      Filter.atTop (nhds 0)
```

end-to-end 組立 (3 既存 genuine atom + 新規 1 本):

1. `csiszarLogRatioGap_antitoneOn_Ici_zero` (`:1085`) で `AntitoneOn (Ici 0)`。
2. antitone + `csiszarLogRatioGap_tendsto_zero_atTop` で `r(0) ≥ lim_{t→∞} r(t) = 0`
   (order 議論: antitone なら `r(0) ≥ r(t) ∀t≥0`、極限を取れば `r(0) ≥ 0`。
   Mathlib `ge_of_tendsto` / `le_of_tendsto_of_tendsto` 系で機械的)。
3. `epi_of_csiszarLogRatioGap_zero_nonneg` (`:985`、genuine) で `r(0) ≥ 0 → EPI`。

これは **difference を完全回避** する genuine 経路 (implementer option 1、2026-06-05) — bridge body を
ratio 化せず (reframe plan 判断ログ 10 の禁止事項 = pure-Gaussian 端点喪失を避ける)、**headline を ratio-form
で別途組む** (`IsStamToEPIScalingHyp` を経由せず `epi_of_csiszarLogRatioGap_zero_nonneg` から直接 EPI 結論)。

### 復活時に bridge を difference のまま使うか ratio で別組みか

- **ratio で別組み** (推奨、上記)。bridge body `isStamToEPIBridgeHyp_of_scaling` (difference 用、`@audit:ok`)
  は触らず、ratio 経路は `epi_of_csiszarLogRatioGap_zero_nonneg` から EPI を直接出す独立路として組む。
  difference bridge の pure-Gaussian 端点アーキを壊さない (reframe 判断ログ 10 の教訓)。
- richness (問い 2) は route-B lift machinery、density (問い 3) は a.c. precondition から供給。

### 復活トリガー

`docs/audit/audit-tags.md` Wall name register に `entropy-power-clt-limit` が CLOSED で入った時点
(= 一般 input convolution の t→∞ entropy 収束が in-tree genuine 化)。それまで本 plan は park。

---

## 撤退ライン

本 plan は査定 plan であり、NO-GO verdict 自体が撤退状態。実装には着手しない。

- **L-Case1-Limit-α (発火済、2026-06-05)**: ratio t→∞ 経路は entropic CLT 壁
  (`entropy-power-clt-limit` 候補) に直撃 → **NO-GO 確定、case 1 park 継続**。新規 sorry 導入なし
  (実装着手前の構造判定、commit は docs のみ)。本線は difference G3 rescale (親 plan Phase A-close G3)
  に集中。
- **共通禁止** (CLAUDE.md 検証の誠実性): 仮に将来実装する場合も `csiszarLogRatioGap_tendsto_zero_atTop`
  を **load-bearing hypothesis として bundle してはいけない** (= entropy 収束の核を `*Hypothesis`
  predicate に抱えさせて headline を「閉じた」と称する name laundering)。t→∞ 壁が残るなら
  `sorry` + `@residual(wall:entropy-power-clt-limit)` で honest に残す (新 wall は loogle 0件確認 +
  register 追記が promote 手続き、別 wave)。

---

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-06-05 起草) ratio t→∞ 経路を NO-GO 査定、case 1 park 継続を推奨**: reframe plan 判断ログ 10
   (case1 ratio reframe で `t=1` 端点が Gaussian 前提のため一般入力に不成立、t→∞ が必須と判明) を発端に、
   ratio chain end-to-end closure の唯一の欠落 `csiszarLogRatioGap_tendsto_zero_atTop` の feasibility を
   査定。verbatim 確認した 3 genuine atom (`csiszarLogRatioGap_antitoneOn_Ici_zero` `:1085` AntitoneOn
   `Ici 0` / `epi_of_csiszarLogRatioGap_zero_nonneg` `:985` genuine no-load-bearing /
   `csiszarLogRatioGap_at_zero` `EPIL3Integration.lean:1391` genuine) は揃っているが、t→∞ 極限が
   **entropic CLT 級の genuine 壁** (Mathlib CLT は分布収束のみ、entropy 収束は不在; loogle
   `entropyPower/differentialEntropy, Filter.Tendsto` = 0件; in-tree heat-path entropy 形は Gaussian 入力
   限定) と判明。entropy は分布収束に非連続 (下半連続のみ) のため CLT を引いても `r(t)→0` は出ない。
   → **NO-GO**。新 wall 候補 `entropy-power-clt-limit` (t→∞ 漸近 Gaussian saturation、G2 端点
   `approx-identity-L1` の t→0⁺ とは方向逆 + entropic CLT-grade で質的に重い)。
2. **(2026-06-05) 本線推奨 = difference-form G3 rescale**: difference アーキ (`heatFlowPath2 = √(1-s)X+√s Z`、
   s=1 pure Gaussian → `entropyPower_gaussian_additivity` genuine) は **finite 端点で saturate** するため
   t→∞ 壁を踏まない (reframe plan 判断ログ 10 の verbatim 訂正と整合)。case 1 headline の残ボトルネックは
   G3 rescale `csiszarGap_antitoneOn_Icc_zero_one` (`:1270` sorry) の 6 AC/integrability uniform 供給
   (assembly) であり、これが t→∞ を回避する最短路。本線リソースを親 plan Phase A-close G3 (S2→Phase 5) に
   集中させる。ratio atom は park (削除せず、entropic CLT 壁 closure 時に reactivate)。
3. **(2026-06-05、副次発見) route-B B2 trigger 発火**: 問い 2 査定中に確認 — `epi-richness-route-b-plan`
   が「B2 trigger = G2 closure」と書いていたが (同 plan 判断ログ 1)、G2 系 3 wall
   (`heatflow-continuity` / `approx-identity-L1` / `cond-diff-entropy`) は 2026-06-05 に全 CLOSED
   (`audit-tags.md` 確認)。よって route-B B2 (in-place re-wire で偽 W2 完全除去) の trigger は発火済。
   richness 自体は case 1 NO-GO 要因ではないが、richness/headline ラインの状態更新を要する事実として記録。
