# EPI A-5 caller-supplied precondition closure: general-density Blachman producers サブ計画

> **Parent**: [`epi-stam-to-conclusion-phaseA-plan.md`](epi-stam-to-conclusion-phaseA-plan.md) §A-5
>   (`isStamToEPIBridgeHyp_of_stam_debruijn` / `EPIStamToBridge.lean:1287-1322`)
> **Spec (SoT)**: [`epi-blachman-general-density-inventory.md`](epi-blachman-general-density-inventory.md)
>   — 4 項目 (1)(2)(3)(4) の feasibility map + verbatim signature。本 plan は重複転記せず参照する。
> **Created**: 2026-06-01 (R-3‴ closure 直後、A-5 `h_pos_stam` バンドルへの 4 precondition localize を受けて)
> **proof-log**: yes (P4 の 🔴 9 field は Fisher 有限性近傍で失敗確率が高く判断ログ必須。G/P1-P3 は no で可)

## Context

R-3‴ closure (2026-06-01) は EPI チェーン頂点 A-5 の `h_pos_stam` per-`t` バンドル
(`EPIStamToBridge.lean:1287-1322`) に 4 種の **path-density regularity precondition** を
caller 供給として localize した。各 `(Z_X, Z_Y, t>0)` に対し、ターゲット密度は **Gaussian ではなく**
`(h_reg_X.reg_at t ht).density_t = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)`
(`IsRegularDeBruijnHypV2.density_t_eq`、`FisherInfoV2DeBruijn.lean:259-260`)。`pX` は X の任意密度
(Gaussian とは限らない)で、`IsRegularDeBruijnHypV2` が供給する pX regularity は
`pX_nn` / `pX_meas` / `pX_law` / `pX_mom` (第2モーメント `∫ y²·pX < ∞`) の **4 件のみ**。

4 項目 (inventory §「A-5 で充足すべき 4 項目」、行 `1309-1321`):

| # | precondition | inventory verdict |
|---|---|---|
| (1) | `IsRegularDensityV2 density_X ∧ IsRegularDensityV2 density_Y` | in-house closeable (~150 行 + gateway variant) |
| (2) | `∫ density_X = 1 ∧ ∫ density_Y = 1` | in-house closeable (~40-70 行) |
| (3) | `density_sum = convDensityAdd density_X density_Y` | in-house closeable (~120-200 行) |
| (4) | `IsBlachmanConvReady density_X density_Y` | in-house 工数壁 (~400-700 行、最重) |

**inventory の総合判定: 真の Mathlib 壁は 0 件**、4 項目すべて in-house で closeable。各 producer が landing
すれば A-5 の caller-supplied precondition を genuine に discharge し、EPI end-to-end closure に近づく。
本 plan はこの inventory を Phase 化し、撤退ライン + 進捗ログ骨格を与える役割。

## Approach (overall strategy / shape of solution)

**全体形状**: 共通基盤 gateway 先行 → 軽い (2)→(1) で normalization/解析パターン確立 → (3) 並行 → (4) 最後。

```
            ┌─────────────────────────────────────────────┐
   Phase G  │ EPIConvDensityGaussianGateway.lean            │  共通基盤
            │ pX integrable-only + Gaussian-kernel-smooth    │  (P1/P4 の 🟡 group が依存)
            │ 版 derivative gateway                          │
            └───────────────┬─────────────────────────────┘
                            │
        ┌──────────────┬────┴───────────┬──────────────────┐
        ▼              ▼                 ▼                  ▼
   Phase P2        Phase P1          Phase P3           Phase P4
  Normalization  IsRegularDensityV2  assoc/pPath      IsBlachmanConvReady
  ∫ conv = 1     producer (1)        同定 (3)           producer (4)  ← 最重
   (2)              ▲ (P2 の Fubini       (G と独立、         ▲ (G + P1 + P2 を再利用)
                     pattern 再利用)      並行可)
```

**中核戦略 = Gaussian kernel smoothness 遺伝**。ターゲットは常に「任意密度 `pX` と Gaussian heat kernel
`g_t` の畳み込み」`convDensityAdd pX g_t`。`pX` 自身には smoothness が無い (`IsRegularDeBruijnHypV2` は
`pX_nn/meas/law/mom` のみ供給) ため、微分・有界性・正値性・可積分性はすべて **Gaussian factor 側の
smoothness が遺伝する**ことで構成する (`∂_z ∫ pX(x)·g(z-x) = ∫ pX(x)·g'(z-x)`、微分は Gaussian factor が担う)。
Mathlib の `HasCompactSupport.contDiff_convolution_right` は Gaussian が compact support を持たないため
使えないが、これは既存 in-house parametric-integral gateway (`EPIConvDensity.lean`) で迂回済の既知パターン
(inventory §「Mathlib 壁の列挙」)。

**地雷 (G が存在する理由、inventory §「主要前提条件ボックス」)**: 既存 gateway
`convDensityAdd_hasDerivAt_of_regular` (`EPIConvDensity.lean:187`) は `hregX : IsRegularDensityV2 fX` を
**fX 側にも要求** (`hX_cont := hregX.diff.continuous` を内部使用、`:198`)。`fX := pX` には
`IsRegularDensityV2` が供給されないため、現 signature では直接使えない。→ Phase G で「`fX` integrable-only +
`fY := g_t` smooth-kernel」版 gateway を新規に組み、微分を Gaussian factor に寄せる。これが (1)(4) 共通の前提。

**各 producer の意味 (honesty)**: producer 群は load-bearing hyp 化ではなく **honest な precondition 充足**。
4 項目はすべて regularity/integrability/boundedness/positivity であり、conv-Fisher 不等式の核は
`convex_fisher_bound` body に genuine に存在する (`EPIBlachmanDensity.lean:695-711` の `@audit:ok` 監査が
「core を bundle しない」を確認済、inventory §(4) verdict)。各 producer の signature は本来形を保ち、
詰まったら `sorry` + `@residual` で抜く (仮説束化禁止)。

**段階的 ship**: G→P2→P1→P3 は独立に type-check done で commit 可。P4 は最重で、1 session に収まらない場合は
下記撤退ラインで縮退する。

## Scope (5 file、orchestrator 決定済の layout — 変更しない)

| Phase | file | 役割 |
|---|---|---|
| G | `InformationTheory/Shannon/EPIConvDensityGaussianGateway.lean` (新規) | `pX` integrable-only + Gaussian-kernel-smooth 版 derivative gateway |
| P2 | `InformationTheory/Shannon/EPIConvDensityNormalization.lean` (新規) | (2) `∫ convDensityAdd pX g_t = 1` |
| P3 | `InformationTheory/Shannon/EPIConvDensityAssoc.lean` (新規) | (3) `convDensityAdd_assoc` + X⊥Y 一般版 `pPath` + 同定 |
| P1 | `InformationTheory/Shannon/EPIConvDensityRegular.lean` (新規) | (1) `IsRegularDensityV2 (convDensityAdd pX g_t)` producer |
| P4 | `InformationTheory/Shannon/EPIBlachmanGeneralDensity.lean` (新規) | (4) 非 Gaussian `IsBlachmanConvReady` producer |

各 Phase landing 時に `InformationTheory.lean` へ import 1 行追加。import policy: pinpoint (`import Mathlib` 禁止)。

## 進捗

- [x] **G  共通基盤 gateway** (pX integrable-only + Gaussian-kernel-smooth derivative) ✅ `d29d73a` 0-sorry `@audit:ok`
- [x] **P2 `∫ convDensityAdd pX g_t = 1`** 正規化 producer ✅ `be23622` 0-sorry sorryAx-free `@audit:ok` (Mathlib `integral_convolution` ルート)
- [x] **P1 `IsRegularDensityV2 (convDensityAdd pX g_t)`** producer ✅ `68d3ac4` 6 field 全 genuine sorryAx-free `@audit:ok` (tail も DCT で閉鎖、retreat 無し)
- [x] **P3 `convDensityAdd_assoc` + interchange bridge** ✅ `b3b0356` 10 補題 `@audit:ok` (Mathlib `convolution_assoc` 経由、有界性を第三因子のみに弱める設計)
- [x] **P4 非 Gaussian `IsBlachmanConvReady` producer** ✅ `23ba687`+`b3b0356` **19/19 field genuine** sorryAx-free `@audit:ok` (`int_fisherZ` は P3 interchange bridge で variance-2t に lift し閉鎖)
- [ ] A-5 配線: 4 producer を `h_pos_stam` バンドルに供給、A-5 を genuine discharge 📋 ← **次セッションの本丸**

> **G/P1/P2/P3/P4 全 landing 完了 (2026-06-01)。4 precondition (1)(2)(3)(4) 全てに genuine producer が揃った。** 残るは A-5 配線のみ。
> 依存順だった `G → P2 → P1 → (P3 並行) → P4 → A-5 配線`、実績は P3 が P4 の `int_fisherZ` 閉鎖に load-bearing だったため `…→ P4(18/19) → P3 → P4(19/19) → A-5 配線` の順で進行。

## Phase 詳細

### Phase G — 共通基盤 gateway (`EPIConvDensityGaussianGateway.lean`)

- **目標 signature**: `convDensityAdd_hasDerivAt_of_gaussianKernel` —
  `fX := pX` (可積分のみ、`Integrable pX volume`)、`fY := g_t` (Gaussian PDF、smooth kernel) で
  `HasDerivAt (convDensityAdd pX g_t) (∫ x, pX x * deriv g_t (z - x) ∂volume) z`。
  微分を Gaussian factor 側に寄せ、`pX` smoothness を要求しない。
- **依存**: なし (基盤)。
- **工数見積**: ~80-120 行。
- **主要部品**: 既存 gateway body `EPIConvDensity.lean:245-263` の `h_diff` field 雛形流用
  (`HasDerivAt (fun z => pX x * g_t(z-x))` を Gaussian factor の `HasDerivAt` から組む)、
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (`ParametricIntegral.lean`、積分記号下微分)。
  Gaussian kernel `deriv` 有界 envelope。
- **落とし穴**: dominated convergence の dominating function を Gaussian `deriv` envelope (`pX(x)·sup|g'|`)
  で立てる。`pX` 可積分性が dominating の可積分性を担保する。

### Phase P2 — 正規化 producer (`EPIConvDensityNormalization.lean`)

- **目標 signature**: `convDensityAdd_gaussianKernel_integral_eq_one` —
  `∫ z, convDensityAdd pX g_t z ∂volume = 1`、前提 `pX_nn` + `Integrable pX volume` + `∫ pX = 1` + `0 < t`。
- **依存**: G なし (Fubini ルート独立)。最初に着手して Fubini/normalization パターンを確立、P1 に再利用。
- **工数見積**: ~40-70 行。
- **主要部品**: Fubini 直接ルート推奨 — `integral_integral_swap` で
  `∫_z ∫_x pX(x)·g(z-x) = ∫_x pX(x)·(∫_z g(z-x)) = ∫_x pX(x)·1 = 1`。reflection 不変性
  `integral_sub_right_eq_self` で `∫_z g(z-x) = ∫ g`、`integral_gaussianPDFReal_eq_one`
  (`Mathlib/.../Gaussian/Real.lean:121`) で `∫ g = 1`。可積分性は `convDensityAdd_integrand_integrable` +
  `convKernel_envelope_integrable` (`FisherInfoV2DeBruijnAssembly.lean:787`、private — 同 file 不可なら
  re-export 要)。
- **落とし穴**: `integral_convolution` (`Convolution.lean:843`) ルートは `⋆[L,ν]` ↔ `convDensityAdd`
  (Bochner `∫`) の bridge を要する上 `[CompleteSpace _]` 型クラス前提が付くため、Fubini 直接ルートのほうが
  `convDensityAdd` 定義に近い (inventory §(2))。

### Phase P1 — `IsRegularDensityV2` producer (`EPIConvDensityRegular.lean`)

- **目標 signature**: `isRegularDensityV2_convDensityAdd_gaussianKernel` —
  `IsRegularDensityV2 (convDensityAdd pX g_t)`、前提は `pX_nn/meas/law/mom` 相当 + `0 < t`。
- **依存**: G (`diff` field)、P2 (`integral_deriv_eq_zero` の Fubini パターン再利用)。
- **工数見積**: ~150 行。
- **field 別部品** (inventory §(1) 表):
  - `diff` ← Phase G gateway を `∀ z₀` 量化で `Differentiable` 化。
  - `pos` ← `convDensityAdd_pos` (`FisherInfoV2DeBruijnPerTime.lean:786`、`@audit:ok`、まさに conv-with-Gaussian 形)。
  - `tail_bot` / `tail_top` ← **新規** (~40-60 行): dominated convergence + Gaussian envelope で
    Gaussian decay 遺伝。
  - `integrable_deriv` ← `convKernel_envelope_integrable` を `K := deriv g_t` で (private、re-export 要)。
  - `integral_deriv_eq_zero` ← **新規** (~30 行): FTC + tail vanishing (`FisherInfoGaussian.lean:231-292`
    の Gaussian 版が雛形、`tail_*` 依存)。
- **落とし穴**: `diff`/`pos` は `@audit:ok` で完備。`pX` 側に `IsRegularDensityV2 pX` は供給されない
  (循環リスク回避のため G gateway が pX smoothness を要求しないことが前提)。

### Phase P3 — assoc / pPath 同定 (`EPIConvDensityAssoc.lean`)

- **目標 signature**: `density_sum = convDensityAdd density_X density_Y` の同定補題群。具体形は
  `density_sum = convDensityAdd (convDensityAdd pX g_t) (convDensityAdd pY g_t)`。
- **依存**: G と独立 (代数 + Fubini 中心)、P2/P1 と並行可。
- **工数見積**: ~120-200 行。
- **部品** (inventory §(3) 内訳):
  - (3a) 和の密度 = 畳み込み: `pPath_eq_convDensityAdd` (`FisherInfoV2DeBruijnPerTime.lean:198`) は
    **X⊥Gaussian 専用** → X⊥Y 一般版を新規に組む (`IndepFun.pdf_add_eq_lconvolution_pdf` の
    density-level bridge、`convDensityAdd_gaussian_closed_form` body `EPIBlachmanGaussianWitness.lean:179-`
    の `h_lconv_pt` 雛形)。
  - (3b) 結合則: `convDensityAdd_comm` (`EPIConvDensity.lean:45`、`@audit:ok`) は有るが
    **`convDensityAdd_assoc` 不在** → 新規 (Fubini + reflection、~60-100 行)。
  - (3c) Gaussian variance 整合: `gaussianReal_add_gaussianReal_of_indepFun` (`Real.lean:624`) +
    `convDensityAdd_gaussian_closed_form` (`EPIBlachmanGaussianWitness.lean:168`) で
    heat kernel variance `t + t` の算術整合。
- **落とし穴**: (3c) の variance 算術 — Z_X, Z_Y iid `gaussianReal 0 1`、`√t·Z_X + √t·Z_Y` 経由で
  `t + t = 2t`。variance 整合が drift しやすい (inventory §「主要前提条件ボックス」)。

### Phase P4 — 非 Gaussian `IsBlachmanConvReady` producer (`EPIBlachmanGeneralDensity.lean`)

- **目標 signature**: `isBlachmanConvReady_convDensityAdd_gaussian` —
  `IsBlachmanConvReady (convDensityAdd pX g_t) (convDensityAdd pY g_t)`、前提は
  `pX_nn/meas/law/mom` + `pY_*` 相当 + `0 < t`。現 producer
  `isBlachmanConvReady_gaussianPDFReal` (`EPIBlachmanGaussianWitness.lean:335`) は両入力 Gaussian 専用、
  非 Gaussian 用は 0 件 (inventory §(4))。
- **依存**: G (gateway variant)、P1 (`IsRegularDensityV2`)、P2 (normalization)、P3 (同定) すべて再利用。
- **工数見積**: ~400-700 行 (最重)。
- **19 field の攻略順** (inventory §(4) field 分類表):
  - **✅ 自動遺伝 2 件**: `int_fX` / `int_fY` (P2 の Fubini で `pX` 可積分から)。
  - **🟡 Gaussian smoothness 遺伝 8 件** (先に潰す、各 ~20-40 行):
    `bdd_fX/bdd_fX'/bdd_fY/bdd_fY'` (Gaussian sup / deriv 有界遺伝)、`pos_pZ` (`convDensityAdd_pos` の
    2 段 conv 版)、`int_X/int_Y` (`bdd_*` + 可積分 → `bdd_mul`、`convKernel_envelope` 流用)、
    `cond_int` (`condDensityX` 定義依存)。
  - **🔴 `pX/pY` 追加 regularity を要する 9 件** (本体、各 ~60-100 行):
    `int_W/int_Wsq` (`scoreWeight` の `logDeriv` 含む — conv の logDeriv 有界性)、
    `int_inner` (inner integral の `z`-可積分性、`pX_mom` が効く)、
    `int_fisherX/int_fisherY/int_fisherZ` (conv の Fisher 情報量有限性、Stam 核心近傍)、
    `int_prod1/2/3` (`volume.prod volume` 上 Tonelli、Gaussian 版 `measurePreserving_prod_sub_swap` shear
    `EPIBlachmanGaussianWitness.lean:320-326` 雛形)。
- **落とし穴 (最重要)**: 🔴 group の `int_fisher*` は **conv の logDeriv² 可積分 = Fisher 有限性**で、
  `pX_mom` (第2モーメント)だけでは出ない。conv-with-Gaussian smoothness が logDeriv を抑えるが定量評価が要る
  (inventory §(4)「不足 field」)。ここが Stam の核心近傍で慎重さが要る箇所。詰まったら **(各 field を
  個別に) `sorry` + `@residual` で抜く** (核を bundle しない、honest)。

### A-5 配線 — 4 producer を `h_pos_stam` バンドルに供給

- P1-P4 の producer を `EPIStamToBridge.lean:1287-1322` の `h_pos_stam` per-`t` バンドルに供給し、
  caller-supplied precondition を genuine discharge。
- これで A-5 `isStamToEPIBridgeHyp_of_stam_debruijn` の 4 項目が caller 供給ではなく producer 経由で閉じ、
  EPI end-to-end closure に近づく。

## 撤退ライン

inventory §「撤退ラインへの距離」の結論を踏襲: **新規撤退ライン発動は不要** (4 項目とも in-house で
closeable、真の Mathlib 壁 0 件)。既存の `@residual(plan:epi-stam-to-conclusion-phaseA-plan)` の枠内で吸収可。

**縮退案 (撤退ラインではない)**: P4 が ~400-700 行で **1 session に収まらない**場合、
`isBlachmanConvReady_convDensityAdd_gaussian` を **単一 shared sorry 補題**に集約し
(`EPIBlachmanGeneralDensity.lean` に 1 件、`docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題
パターン」)、A-5 wrapper からそれを呼ぶ形に縮退する。

- 撤退口は `sorry` + `@residual(plan:epi-blachman-general-density-plan)`。
- **signature は本来形を保つ** (`IsBlachmanConvReady (convDensityAdd pX g_t) (convDensityAdd pY g_t)` のまま、
  前提は `pX_nn/meas/law/mom` + `pY_*` + `0 < t` の regularity precondition のみ)。
- **仮説束化は禁止** — `*Hypothesis` predicate に 19 field の核を bundle しない。19 field は
  regularity/integrability/boundedness/positivity であり precondition であって load-bearing ではないが、
  それらを 1 つの predicate に畳んで「仮説として渡す」形にもしない (shared sorry 補題の body に `sorry` で残す)。
- これは **縮退であって新規撤退ラインではない** (signature 本来形保持、A-5 を type-check done で先に通すための
  分割)。closure 担当は本 plan 自身 (`@residual(plan:epi-blachman-general-density-plan)` の slug = 本 file の
  stem) なので、後続 session が同 plan の枠で P4 の 🔴 group を順次 close する。

同様に P3 の X⊥Y 一般 pPath / `convDensityAdd_assoc` が当該 session で詰まった場合も、本来形 signature を保った
shared sorry 補題に残し `@residual(plan:epi-blachman-general-density-plan)` を付す (仮説束化禁止)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

(各 Phase landing 時にここへ追記する。proof-log: P4 の 🔴 9 field は別途
`docs/shannon/proof-log-epi-blachman-general-density.md` に詳細記録。)
