# EPI 残り 2 壁 re-attack — gateway atom 起点の本気攻略 サブ計画

> **Parent**: [`epi-moonshot-plan.md`](epi-moonshot-plan.md) (Ch.17 一般 EPI)
> **関連 parent sub-plans**: [`epi-stam-discharge-plan.md`](epi-stam-discharge-plan.md) / [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) / [`epi-stam-fisher-epi-integrated-sweep-plan.md`](epi-stam-fisher-epi-integrated-sweep-plan.md)
> **Inventory (Wave 1)**: [`epi-wall-reattack-inventory.md`](epi-wall-reattack-inventory.md)
> **Created**: 2026-05-30 (Wave 1 独立再評価 = proof-pivot-advisor + mathlib-inventory 収束結論を消費)

---

## ⚠ 最重要 — Phase 1 = go/no-go GATE

**本 plan の全体は Phase 1 (gateway atom `convDensity_add_differentiable`) の Done 判定に
gate される。** Phase 順序を取り違えて壁2 (Phase 4) を先に dispatch したり、Phase 1 を飛ばして
壁1 本体 (Phase 3) に着手すると **空回りする** (どちらも gateway が供給する density 微分可能性 +
score 表現を消費するため)。

- **Phase 1 GO** (gateway atom が type-check done で建つ) → Phase 2/3/4 へ進み 2 壁を直列 closure。
- **Phase 1 NO-GO** (`⋆ₗ` / convolution 密度の点ごと微分可能性が概念ごと組めない、または Gaussian
  tail dominated 充足が 1 セッション超過) → **真壁確定診断**として `@residual(wall:conv-score-smooth)` /
  `@residual(wall:debruijn-heat-eq)` の honest sorry 据置に戻し、診断を docstring 散文化して撤退。
  Phase 2 (cross-term orthogonality) のみ gateway 非依存なので独立に拾える。

go/no-go の決定的判定基準は §Phase 1 末尾「Done 条件 / go-no-go gate」参照。

## 進捗

- [x] Phase 0 — 在庫確定 + 壁 signature verbatim 照合 ✅
- [x] Phase 1 — **gateway atom `convDensity_add_differentiable` = GATE GO ✅** (genuine, 0 sorry, sorryAx-free, 独立監査 `@audit:ok`)
- [x] Phase 2 — cross-term orthogonality `score_cross_term_eq_zero` = genuine ✅ (0 sorry, `@audit:ok`)
- [x] **Phase 3-pre — 3+1 述語 signature pivot 完了 ✅** (2026-05-30、軸1 `hconv` + `IsRegularDensityV2` + 正規化 `∫=1`、軸2 廃止)。
      false-statement defect 除去、4 述語 `@audit:ok`、`stam_step2_density_wall` → `@residual(wall:stam-blachman)` 格下げ。独立 honesty 監査 ALL OK (Gaussian witness で非 vacuous 確認)。新規 sorry 0。
- [~] **Phase 3 — 密度レベル明示積分経路 = scoped multi-session path 📋 (2026-05-30 再評価で「真壁確定」から格下げ、判断ログ #4)**。
      旧「真壁確定 (~300 行 PR 級 unscoped wall)」は **抽象 condExp 経路限定の過大判定**だった。独立 proof-pivot-advisor (density pivot 検証) が決定的事実を発見: `fisherInfoOfMeasureV2 _μ f = fisherInfoOfDensity f` (`FisherInfoV2DeBruijn.lean:86-87`, `rfl`、measure 引数を捨てる) により `stam_step2_density_wall:376` の goal は**純粋に密度上の解析命題** `(fisherInfoOfDensity fXY).toReal ≤ J_X·J_Y/(J_X+J_Y)` (with `fXY =ᵐ convDensityAdd fX fY`, `IsRegularDensityV2 fX/fY`, `∫fX=∫fY=1`) に collapse する。**抽象 condExp/condDistrib/disintegration は一切不要**。密度レベル明示積分経路 (Phase 3a–3d に分解、各 atom shared sorry 補題 + 段階 ship) で攻略を再開する。条件付き Cauchy-Schwarz を**確率重み `p_{X|Z}(x|z) := fX(x)fY(z-x)/p_Z(z)` 上の点ごと積分**として明示書き下し、condExp の disintegration 橋を概念ごと回避。
  - [x] **Phase 3a — GATE = GO ✅ (2026-05-30、L-EPIW-3-α 不発)**。`convDensityAdd_hasDerivAt_of_regular` (`EPIConvDensity.lean:186`) を **genuine 完成** (0 sorry, sorryAx-free, `@audit:ok`)。gateway 7 hyp (特に支配項 `h_bound` Gaussian-tail dominated) を `IsRegularDensityV2 fX/fY` + 追加 3 precondition (`hX_int : Integrable fX` / `hY_bdd : ∃M,∀w,|fY w|≤M` / `hY'_bdd : ∃M,∀w,|deriv fY w|≤M`、いずれも Gaussian 充足の regularity、load-bearing でない) から discharge。`h_bound` は `bound x := MY'·|fX x|` (z 非依存) で PR 級を回避、可積分性は `hX_int.abs.const_mul` 1 行。`hnormX/hnormY` (∫=1) は GATE 段では不要 → より弱い `Integrable fX` に絞った。独立 honesty 監査 ALL OK (3 hyp = factor 個別 regularity、循環なし、Gaussian witness 非 vacuous)。**残作業**: Gaussian instance が `hY_bdd/hY'_bdd/hX_int` を充足する discharge 補題 (consumer 側、Phase 3b/3c で必要時)。S2 対称導関数恒等式は未着手 (Phase 3b へ)。
  - [x] **Phase 3b — S2 + S3 genuine ✅ (2026-05-30、独立監査 @audit:ok)**。新 file `EPIBlachmanDensity.lean`。`symm_deriv_integral_eq` (S2、`∫deriv fX·fY(z-·)=∫fX·deriv fY(z-·)`、gateway 両順序適用 + `HasDerivAt.unique` + 併進置換 — IBP 経路 (b) より圧倒的に短い) + `score_conv_eq_weighted_integral` (**S3 核心 = Blachman score 表現 `logDeriv(convDensityAdd) z = ∫ scoreWeight·condDensityX`**、condExp/condDistrib/disintegration **一切不使用**を body+import の rg で確認) + `condDensityX_integral_eq_one` + def `condDensityX`/`scoreWeight`。全 genuine 0-sorry/sorryAx-free。**density-route pivot が実証された** (Blachman を明示 Bochner ∫ だけで建てられる)。precondition: 対称版 boundedness `hX_bdd/hX'_bdd/hY_bdd/hY'_bdd` + `Integrable fX/fY` + `0<convDensityAdd` (Gaussian 充足、load-bearing でない)。
  - [~] **Phase 3c — atom A genuine ✅ / S4・convex_bound は plan-closable (真壁なし確定) 📋**。`fisherInfoOfDensity_toReal_eq_integral` (atom A、lintegral↔Bochner 橋) = **genuine 0-sorry @audit:ok**。`score_sq_le_weighted_integral` (S4) + `convex_fisher_bound` は現状 sorry だが、**独立監査が `wall:stam-blachman` → `@residual(plan:epi-wall-reattack-plan)` に誤分類訂正**: S4 は確率測度 `volume.withDensity(condDensityX)` 上の Jensen `ConvexOn.map_integral_le` (`Mathlib Analysis/Convex/Integral.lean:199`, `[IsProbabilityMeasure]`、mass=1 は 3b で済) で **closable**、convex_bound は S4 + Tonelli (`integral_integral_swap` 実在) + cross-term=0 (`integral_logDeriv_density_eq_zero` repo) + atom A で closable。**🎯 density route に既知の真の Mathlib 壁は残っていない** — 当初「Blachman = PR 級真壁」診断を density route が概念ごと解体。残りは実装 + Phase 3d の precondition gap。
  - [x] **Phase 3c-cont — S4 genuine ✅ (@audit:ok)**。`score_sq_le_weighted_integral` を Jensen `ConvexOn.map_integral_le` via 確率測度 `volume.withDensity(ofReal∘condDensityX)` (mass=1 は 3b、`integral_withDensity_eq_integral_toReal_smul₀` で ∫ 往復) で genuine closure、sorryAx-free 独立監査 OK。**予測した解析核がついに genuine 化**。`convex_fisher_bound` は step (a) per-z S4 適用 + (b) `condDensityX·p_Z=fX·fY(z-·)` 約分まで genuine、残 sorry = (c) Tonelli order-swap + (d) 3 項評価 (`λ²J_X+(1-λ)²J_Y`, cross=0) のみ、`@residual(plan:epi-wall-reattack-plan)` (closable, 真壁なし、precondition は全 regularity)。
  - [x] **Phase 3c-fin — `convex_fisher_bound` genuine ✅ (2026-05-30、独立監査 @audit:ok)**。残 sorry (Tonelli `integral_integral_swap` 3 件 + 3 項評価 + cross=0) を `convex_fisher_term1/2/cross` 補助補題で genuine closure。結論 `(fisherInfoOfDensity (convDensityAdd fX fY)).toReal ≤ lam²·(fisherInfoOfDensity fX).toReal + (1-lam)²·(fisherInfoOfDensity fY).toReal` (`EPIBlachmanDensity.lean:538`)、0-sorry/sorryAx-free。**density route の解析核は完全に揃った**。残 = Phase 3d の precondition 整合のみ。
- [ ] Phase 3d — assemble: `stam_step2_density_wall` (`EPIStamInequalityBody.lean:376`) の sorry を genuine 充足 📋。**決定済 (判断ログ #6、下記 §Phase 3d): 案 b' = `IsStamCondExpCSHyp` 経由**。詳細 + proof skeleton + 新規 atom リストは下記 §Phase 3d 参照。precondition gap (L-EPIW-3-密度-β: `deriv f` 有界 + 高階 integrability) は **案 b (lockstep 述語 + `IsStamCauchySchwarzOptimal`/`IsStamCondExpCSHyp` に boundedness/integrability hyp 追加)** で解消。案 a (構造 field 追加) は構築サイト 0 件で ripple ゼロだが Gaussian instance 未 wire のため非 vacuousness の検証点を増やす — 比較表は §Phase 3d。
- [ ] Phase 4 — 壁2 (per-time de Bruijn + FTC 積分形) 📋 (advisor: 同根 apparatus 依存で Phase 3 と並走しても空回り高リスク、heat eq IBP = L-EPIW-4-α 真壁可能性高)

## ⚠ Phase 3-pre — 3+1 述語 signature pivot (実装可能粒度) 📋

**proof-log: yes** (`epi-wall-reattack-proof-log.md` に追記)。

### Context (要点)

`stam_step2_density_wall` (`EPIStamInequalityBody.lean:359`、生成先 `IsStamCauchySchwarzOptimal`
`:269`) は `@audit:defect(false-statement)`。target predicate `IsStamCauchySchwarzOptimal` が密度
`fX fY fXY : ℝ→ℝ` を **無制約に全称量化** し、(軸1) `fXY = convDensityAdd fX fY` 制約欠落 + (軸2)
`fisherInfoOfMeasureV2 _μ f := fisherInfoOfDensity f` が measure 引数を捨てる (`FisherInfoV2.lean:89` /
`FisherInfoV2DeBruijn.lean` の `n_def : n μ f = fisherInfoOfDensity f := rfl`) ため `P.map X` との
紐づけも無い → 命題が **FALSE** (反例 `fX=fY=𝒩(0,1)` `J=1` RHS=1/2 / `fXY=𝒩(0,1/100)` `J_sum=100`;
`100 ≤ 1/2` 偽、closed-form `1/v` 検算済)。同型 defect が **3 述語**: `IsStamCauchySchwarzOptimal`
(`:269`) + `IsStamCondExpCSHyp` (`EPIStamStep12Body.lean:200`) + `IsStamInequalityResidual`
(`EntropyPowerInequality.lean:190`)。**第 4 の ripple 対象** = `IsStamInequalityHyp`
(`EPIStamDischarge.lean:100`)、これは別 def だが `IsStamInequalityResidual` と
`fisherInfoOfMeasureV2_def` 経由の defeq で結ばれ、3 箇所の `exact` が依存する (decision B)。本 Phase は
4 述語を pivot して predicate の結論を TRUE-in-principle にし、genuine Blachman 核を honest wall
として `stam_step2_density_wall` の `sorry` に残す。Blachman 壁の closure ではなく **defect 除去**。

### Approach

> **2026-05-30 reconcile (独立 proof-pivot-advisor verdict 反映)**: 当初設計の **軸2 (measure-keyed
> 密度同定 hyp `HasDensityReal`) は廃止**。理由 (verbatim 根拠付き、§判断ログ #3): (a) `fisherInfoOfMeasureV2
> _μ f := fisherInfoOfDensity f` (`FisherInfoV2.lean:77`/`:89`, `rfl`) が measure を捨てる以上、`J` は
> density のみで決まり `fX = pdf(P.map X)` は結論に **寄与しない冗長 hyp**。(b) 接続予定だった
> `fisherInfoOfMeasureV2_eq_of_pdf_ae_eq` は **実在しない** (`rg`/loogle "unknown identifier")。よって
> `HasDensityReal` を抽象 `Prop` で足すと consumer が witness 供給不能 → 述語が **vacuously satisfiable**
> → 除去対象の false-statement defect を **degenerate-exploit defect (新 tier-5) にすり替えるだけ**。
> 代わりに採用するのは **軸1 (畳み込み) + 密度性 regularity (既存 `IsRegularDensityV2` + 正規化 `∫=1`)**。

pivot は 1 つの構造手術を 4 述語に複製する: **畳み込み関係 + 密度性 regularity を `∀`-body の hyp として
注入** (全 4 述語、同形)。注入する hyp は 3 種:

- **軸1 (畳み込み)**: `hconv : fXY =ᵐ[volume] convDensityAdd fX fY`。`fXY` を `fX,fY` の畳み込みに縛る
  (反例 `fXY=𝒩(0,1/100)` を排除する核)。
- **密度性 (Stam の確率密度前提)**: `hregX : IsRegularDensityV2 fX` / `hregY : IsRegularDensityV2 fY`
  (既存 structure `FisherInfoV2.lean:124`、`diff`/`pos`/`tail_bot`/`tail_top`/`integrable_deriv`/
  `integral_deriv_eq_zero` を bundle、Gaussian が充足) + 正規化 `hnormX : ∫ x, fX x ∂volume = 1` /
  `hnormY : ∫ x, fY x ∂volume = 1` (`IsRegularDensityV2` に正規化 field は無いので別 hyp)。任意関数
  (負値・非正規化) だと Blachman/Stam は崩れるため、確率密度性は genuine precondition。

`IsRegularDensityV2 fXY` / `hnormXY` は `hconv` から導出可能 (畳み込みが密度性を保存) なので **注入しない**
(冗長回避、Phase 3 本体で `hconv` 経由で使う)。3 種とも *regularity precondition* であり、不等式の核
(`sorry`) ではない。measure-keyed (Optimal/CondExpCSHyp) と density-keyed (Residual/Hyp) で **対称**
(軸2 廃止で非対称は消えた)。measure-keyed の `X Y P` は density-level Stam の interpretive label に留まる。

第 4 の `IsStamInequalityHyp` は `IsStamInequalityResidual` と **別 def** (measure-keyed
`(fisherInfoOfMeasureV2 _ _).toReal` vs density-keyed `fisherInfoOfDensityReal`) だが、両者は
`fisherInfoOfMeasureV2_def` 経由で defeq とされ 3 箇所の `exact` がこの defeq に依存する。Residual
だけ pivot すると defeq が破れるので、**Hyp も同じ hyp を注入して lockstep で pivot** する (decision B、
bridge lemma より cheap)。

実装順 (decision C、advisor verdict で修正): 実依存は `IsStamCondExpCSHyp → (stamCauchySchwarzOptimal_of_condExpCSHyp,
`Step12:257`) → IsStamCauchySchwarzOptimal → (isStamInequalityHyp_via_body) → IsStamInequalityHyp`。
よって **`IsStamCondExpCSHyp` が最上流** = 制約注入の起点。推奨順: **段1 = CondExpCSHyp → 段2 = Optimal**
(of_condExpCSHyp の `linarith` は ∀λ→λ* 抜き出しで新 hyp は透過、引数 append のみ) → **段3 =
Residual + Hyp** (density-keyed 独立、defeq lockstep)。各 step 終了時 `lake env lean` 緑、1 commit/step。

### A. 各述語に注入する制約 (verbatim Lean target)

記法: `convDensityAdd := InformationTheory.Shannon.EPIConvDensity.convDensityAdd`
(`EPIConvDensity.lean:39`、body `fun z => ∫ x, pX x * pY (z - x) ∂volume`、型 `(ℝ→ℝ)→(ℝ→ℝ)→(ℝ→ℝ)`)。
`IsRegularDensityV2 := Common2026.Shannon.FisherInfoV2.IsRegularDensityV2`
(`FisherInfoV2.lean:124`、structure、field `diff`/`pos`/`tail_bot`/`tail_top`/`integrable_deriv`/
`integral_deriv_eq_zero` — **正規化 field 無し**)。

**注入する 3 種 hyp** (全 4 述語 同形、軸2 廃止で対称):

```
(hregX : IsRegularDensityV2 fX) → (hregY : IsRegularDensityV2 fY) →   -- 密度性 (Gaussian 充足)
(hnormX : ∫ x, fX x ∂volume = 1) → (hnormY : ∫ x, fY x ∂volume = 1) → -- 正規化
(hconv : fXY =ᵐ[MeasureTheory.volume] convDensityAdd fX fY) →          -- 軸1 畳み込み
```

`fXY` 側の `IsRegularDensityV2 fXY` / `hnormXY` は注入しない (`hconv` から導出可能、Phase 3 で使用)。

| 述語 | file:line | keying | 注入 hyp | 註 |
|---|---|---|---|---|
| `IsStamCondExpCSHyp` | `EPIStamStep12Body.lean:200` | measure | `hregX hregY hnormX hnormY hconv` | **最上流**、段1、注入の起点 |
| `IsStamCauchySchwarzOptimal` | `EPIStamInequalityBody.lean:269` | measure | 同形 | 段2、CondExpCSHyp から伝播 |
| `IsStamInequalityResidual` | `EntropyPowerInequality.lean:190` | density | 同形 | 段3、density-keyed 独立 |
| `IsStamInequalityHyp` | `EPIStamDischarge.lean:100` | measure | 同形 (Residual と defeq lockstep) | 段3 |

配置: 3 つの Fisher 同定 hyp (`J_X = …` `J_Y = …` `J_sum = …`) の **後**、最終結論 (`J_sum ≤ …` /
`1/J_sum ≥ …` / `∀ lam, …`) の **前** に `hregX hregY hnormX hnormY hconv` を append。この順序で
consumer の `intro …` / `exact h …` 呼出は中間に 5 引数を append するだけの機械的編集になる (Optimal の
最終結論は `J_sum ≤ J_X*J_Y/(J_X+J_Y)`、CondExpCSHyp は `∀ lam, 0≤lam → lam≤1 → J_sum ≤ lam^2*J_X +
(1-lam)^2*J_Y`、verbatim 確認済)。density-keyed/measure-keyed で hyp は完全同形 (軸2 廃止)。

**新規 def は導入しない**: 軸2 廃止により `HasDensityReal` placeholder は不要。注入はすべて既存
`IsRegularDensityV2` + 標準 `=ᵐ` / `∫` で書ける。`L-EPIW-3pre-β` (`HasDensityReal` 不成立) も廃止 (下記 D)。

### B. 第 4 ripple 対象 `IsStamInequalityHyp` の扱い — 決定

**決定: Residual と lockstep で軸1 pivot、bridge lemma は足さない (ただし L-EPIW-3pre-α 時のみ adapter)。**
`IsStamInequalityHyp` (`EPIStamDischarge.lean:100`) は `IsStamInequalityResidual`
(`EntropyPowerInequality.lean:190`) と **別 def** (前者 measure-keyed `(fisherInfoOfMeasureV2 _ _).toReal`、
後者 density-keyed `fisherInfoOfDensityReal`)。両者は `fisherInfoOfMeasureV2_def`
(`FisherInfoV2DeBruijn.lean`、`n μ f = fisherInfoOfDensity f := rfl`) 経由で reducibly defeq とされ、
3 箇所の `exact` がこの defeq に依存する (scoping §honesty L216 verbatim)。

Residual に 5 hyp を注入すると、それを持たない `IsStamInequalityHyp` との `∀`-chain 長が変わり
defeq が破れて下記 3 `exact` が型不一致になる。よって **Hyp にも同位置に同 5 hyp を注入** して
chain 長を揃え defeq を維持する。両者完全同形 (軸2 廃止で `hid*` 非対称は消えた)。

defeq 依存 site と pivot 後の挙動:

| site | file:line | 現 body | pivot 後 |
|---|---|---|---|
| `epi_via_stam_main` | `EPIStamDischarge.lean:440` (`:445` の `exact`) | `entropy_power_inequality P X Y hX hY hXY h_stam` (`h_stam : IsStamInequalityHyp`, defeq で Residual 引数に流す) | **生存** — 両 def に同 `hconv` が入り chain 長一致、defeq 維持。`h_stam` 構築側 (caller) が `hconv` を供給する必要が生じる (下記リスク) |
| `entropy_power_inequality_unconditional` | `EPIStamToBridge.lean:1100-1102` (`:1119` の `exact h_bridge h_stam`) | `h_stam : IsStamInequalityResidual` を `h_bridge : IsStamToEPIBridgeHyp` (Hyp 消費) に defeq で渡す | **生存** — 同上、両 def lockstep なら defeq 維持 |
| `epil3IntegratedPipeline` 経路 | `EPIL3Integration.lean:156` (`:160` の `exact … h_pipeline.stam`) | `h_pipeline.stam : IsStamInequalityHyp` を `entropy_power_inequality` (Residual 引数) に defeq で渡す | **生存** — 同上 |

**bridge lemma 不要の条件**: 上記 3 site は全て *pass-through* (defeq で型を合わせて渡すだけ、Residual/Hyp
値を **construct** しない)。`rg IsStamInequalityResidual` で確認した construct site は
`entropy_power_inequality` (`:265`, headline, `h_stam` を引数で受けて bridge へ pass) /
`entropy_power_inequality_exp_form` (`:278`) / §D Gaussian (`:393`) / `EPIPlumbing.lean:192,267` /
`EPIStamToBridge.lean:1109` — **全て consumer が引数で受け取る pass-through**、construct site 0。よって
両 def lockstep pivot で defeq 維持できれば bridge lemma 不要。**リスク**: pivot 後これら headline
consumer の hypothesis `(h_stam : IsStamInequalityResidual X Y P)` は pivot 済 (= `hconv` を内部に持つ)
predicate を要求するので、headline を呼ぶ最終 user が `hconv` を供給することになる (これは正しい —
EPI を主張するには `X+Y` の密度が `X,Y` 密度の畳み込みである regularity が要る)。implementation で
隠れ construct site が出たら、`IsStamInequalityHyp` には触れず `stam_residual_pivot_bridge : (旧
Residual) → (新 Residual)` adapter を 1 本足す方向に退避 (L-EPIW-3pre-α)。

### C. 実装順序 (各 step 終了時 type-check 緑、1 commit/step)

依存方向 (advisor verdict 確定): `CondExpCSHyp` (最上流) → `Optimal` → `Residual`/`Hyp`。注入する 5 hyp
`hregX hregY hnormX hnormY hconv` は全 4 述語 同形。

**Step 1 — `IsStamCondExpCSHyp` (最上流、注入起点)。**
1. `EPIStamStep12Body.lean` に `import Common2026.Shannon.EPIConvDensity` 追加 (cycle 無し:
   EPIConvDensity は `FisherInfoV2` のみ依存の葉 module、scoping §2 確定)。`IsRegularDensityV2` は
   `FisherInfoV2` 由来で import 済のはず (未 import なら追加)。
2. `IsStamCondExpCSHyp` (`:200`) に 5 hyp 注入。
3. 同 file consumer 透過 (全 pass-through、`fXY` instantiate 無し — scoping §1 確定):
   `:215 isStamCauchySchwarz_of_condExpCSHyp` / `:227 _congr` / `:234 _symm` /
   `:257 stamCauchySchwarzOptimal_of_condExpCSHyp` (intro 後 `h … ` に 5 hyp append、`linarith` は
   ∀λ→λ* 抜き出しで透過) / `:278 _of_step12` / `:299 isStamInequalityHyp_of_step12` /
   `:313 isStamCauchySchwarz_of_step12`。各 `intro … exact h …` に 5 hyp を中間 append。
4. 緑 gate: `lake env lean Common2026.Shannon.EPIStamStep12Body`。Commit。

**Step 2 — `IsStamCauchySchwarzOptimal`。**
1. `EPIStamInequalityBody.lean` に `import Common2026.Shannon.EPIConvDensity` 追加。
2. `IsStamCauchySchwarzOptimal` (`:269`) に 5 hyp 注入 (CondExpCSHyp と同形 → `of_condExpCSHyp` chain
   の hyp shape 一致)。
3. `stam_step2_density_wall` (`:359`): signature が制約付き結論を要求、body は `sorry` 据置。タグは
   decision D (実装後の独立 audit が書換)。
4. 同 file consumer 透過 (全 pass-through): `:387 stam_inequality_via_predicate_optimal` /
   `:410 isStamInequalityHyp_via_body` / `:463 isStamCauchySchwarz_of_optimal` /
   `:503 isStamCauchySchwarzOptimal_of_lambda_optimal` / `:532 _to_pipeline` /
   `:574 entropy_power_inequality_via_body`。各 `intro … exact h …` に 5 hyp を中間 append。
   **sub-bound 引数表**: 5 つの新引数は全て predicate の `∀`-body から素直に流れ、capacity 側分離は無い
   (`P_cb`/`P_target` 型の sub-bound 分岐は本 predicate 群に無し)。
5. 緑 gate: `lake env lean Common2026.Shannon.EPIStamInequalityBody` + transitive
   (`EPIStamStep3Body` `:121 isStamInequalityHyp_via_step3` / `EPIStamDeBruijnConclusion` `:169/203`)。
   `stam_convex_fisher_bound_gaussian` (`StamGaussianBound.lean:77`) は別系 = ripple 不要。Commit。

**Step 3 — `IsStamInequalityResidual` + `IsStamInequalityHyp` (density-keyed 独立、defeq lockstep)。**
1. `EntropyPowerInequality.lean` に `import Common2026.Shannon.EPIConvDensity` 追加。
2. `IsStamInequalityResidual` (`:190`) に 5 hyp 注入。
3. `IsStamInequalityHyp` (`EPIStamDischarge.lean:100`) に同形注入 (chain 長を Residual と一致させ
   `fisherInfoOfMeasureV2_def` defeq を維持)。
4. defeq 3 site (`EPIStamDischarge.lean:445` / `EPIStamToBridge.lean:1119` / `EPIL3Integration.lean:160`)
   + headline consumer (`EntropyPowerInequality.lean:265/278/393`, `EPIPlumbing.lean:192/267`,
   `EPIStamToBridge.lean:1109`) を `intro`/引数に 5 hyp append で透過。
5. 緑 gate: `lake env lean` を `EntropyPowerInequality` / `EPIStamDischarge` / `EPIStamToBridge` /
   `EPIL3Integration` / `EPIPlumbing` に。olean refresh 注意 (CLAUDE.md「After upstream edits」)。Commit。

### D. Done 条件 / タグ遷移

- **Done (type-check)**: 4 述語が制約付き signature に pivot、ripple 先全 type-check done (0 errors、
  `sorry` warning 可)。
- **タグ遷移 (pivot 後、実装者でなく独立 honesty audit が適用)**: `stam_step2_density_wall` の
  `@audit:defect(false-statement)` → `sorry` + `@residual(wall:stam-blachman)` に **格下げ予定**。
  根拠: `hconv` + 密度性 (`hreg*`/`hnorm*`) 注入で反例 (無関係密度 / 非畳み込み `fXY`) が排除され結論が
  FALSE でなくなる → honest wall。同様に
  4 述語 def の `@audit:defect(false-statement)` marker も除去予定 (def が sound になる)。実際のタグ
  書換は audit subagent が「結論がもはや反証不能」を確認した上で行う (plan には「格下げ予定」と記す)。
- **本 Phase が閉じないもの**: Blachman/Stam 不等式そのものは `sorry` 据置 (`wall:stam-blachman`)。本
  Phase は defect 除去であって Blachman closure (Phase 3) ではない。

### honesty 規律 (再掲)

注入する hyp (`hconv` 畳み込み関係 / `hreg*` 密度性 / `hnorm*` 正規化) は **regularity precondition** —
どの密度が admissible かを述べるのであり、不等式が成り立つ *理由* ではない。不等式の核は
`stam_step2_density_wall` の `sorry` 内に全て残る。これは **完成偽装の仮説束化ではない** — predicate の
結論を **真**にして `sorry` を原理的に discharge 可能にするだけ。`sorry` は visible かつ honest
(`wall:stam-blachman`)。明示禁止: 核を `hconv`/`hreg*` に潰す / 何かを `:True` にする / 充足不能な
decorative hyp を足して述語を vacuous にする (= 廃止した軸2 `HasDensityReal` の dead-hyp 落とし穴)。

### 撤退ライン

- **L-EPIW-3pre-α** — ripple が 1 セッション超 (隠れ `Residual` construct site 出現、または
  `HasDensityReal` の `withDensity` body が measurability 義務を引き込む): 述語を **1 つずつ** pivot し、
  旧/新 shape 間に `stam_residual_pivot_bridge` adapter wrapper を挟む。当該 turn は最後の緑
  `lake env lean` 状態で停止、未 pivot 述語の `@audit:defect(false-statement)` タグは据置、pivot 済 vs
  deferred を報告。**file を half-pivot で赤のまま残さない。**
- **L-EPIW-3pre-β** — `HasDensityReal` の honest body (`withDensity`) がこの Phase 内で安価に type-check
  しない: opaque `Prop` placeholder として `@residual(wall:stam-pdf-identification)` を付して進む。軸2
  carrier は honest な forward-declared wall になり Step 2 を block しない。

## Position / Motivation / Scope

### 対象 2 壁 (Wave 1 確定)

- **壁1 `wall:stam-step2-density`** — `Common2026/Shannon/EPIStamInequalityBody.lean:283`
  `stam_step2_density_wall`。独立 `X, Y` の条件付き Cauchy-Schwarz から convex Fisher bound
  `J(Z) ≤ J(X)·J(Y)/(J(X)+J(Y))` (`IsStamCauchySchwarzOptimal`)。regularity (measurability /
  independence / probability measure) は honest hyp として既に保持、analytic core が `sorry`。
- **壁2 `wall:debruijn-integration`** — `Common2026/Shannon/FisherInfoV2DeBruijn.lean:245`
  `debruijnIdentityV2_holds` (per-time 微分形) + `:310` `debruijnIntegrationIdentity_holds`
  (積分形)。de Bruijn 恒等式 `(d/dt) h(X+√t·Z) = (1/2)·J(X+√t·Z)`。

### 共通根 (Wave 1 決定 1)

両壁は同一の foundational apparatus に帰着する: **独立和の畳み込み密度 `p_Z = p_X ⋆ p_Y` を
点ごと微分可能にし、その score `logDeriv p_Z` を condExp `E[s_X | X+Y=z]` (Blachman 恒等式) /
Fisher info に接続する apparatus**。

- 壁1 は `s_Z(z) = E[s_X(X) | X+Y=z]` (Blachman) で convex Fisher bound を出す。
- 壁2 は per-time `p_t = p_X ⋆ heatKernel_t` の `logDeriv` を Fisher info に紐付け、heat eq
  IBP で `(d/dt)h = (1/2)J` を出す。

両方とも「畳み込み密度の点ごと微分可能性 + その logDeriv 表現」を gateway atom として消費する。

### scope-out からの差し戻し条件 (「本気で攻める」の意味)

過去 inventory は 2 壁を「Fisher/score/density 計算 Mathlib 全不在」で scope-out した。本 plan は
gateway atom `convDensity_add_differentiable` を起点に **直列攻略を試行**し、以下で分岐する:

- **gateway が建てば差し戻し**: scope-out を撤回し、Phase 2/3/4 で 2 壁を genuine closure に向かわせる。
- **`⋆ₗ` 微分可能性で詰まれば真壁確定**: scope-out 判断を確定として honest sorry 据置に戻す。
  この場合「なぜ tractable でなかったか」の診断 (どの dominated 仮定が Gaussian tail self-build で
  詰まったか) を当該 wall docstring に散文で残し、後続が同じ探索を繰り返さないようにする。

### Scope (新規 + 既存拡張)

| 対象 file | 役割 | Phase |
|---|---|---|
| `Common2026/Shannon/EPIConvDensity.lean` (新規) | gateway atom `convDensity_add_differentiable` + logDeriv 表現 | Phase 1 |
| `Common2026/Shannon/EPIScoreCrossTermOrth.lean` (新規) | cross-term orthogonality (inventory §着手 skeleton) | Phase 2 |
| `Common2026/Shannon/EPIStamInequalityBody.lean` (既存拡張) | `stam_step2_density_wall:283` 本体充足 | Phase 3 |
| `Common2026/Shannon/FisherInfoV2DeBruijn.lean` (既存拡張) | per-time `:245` + 積分形 `:310` 充足 + `_hX/_hZ/_hXZ` signature 復元 | Phase 4 |

`@residual` slug: gateway 失敗時は既存 wall slug (`wall:conv-score-smooth` / `wall:stam-blachman` /
`wall:debruijn-heat-eq`、register 既登録) に据置く。新規 plan slug は本 file stem
`epi-wall-reattack-plan` を `@residual(plan:epi-wall-reattack-plan)` で参照可。

## ゴール / Approach

**解の全体形**: 共通 density apparatus を gateway atom で建て、壁1 (条件付き Blachman → convex
Fisher bound) を先に閉じ、壁2 (per-time de Bruijn density witness → FTC 積分形は Gaussian テンプレ
一般化) を後に閉じる。**直列** shape (壁1 → 壁2、逆順不可)。

```
                  ┌──────────────────────────────────────────────────┐
   Phase 1 GATE   │ convDensity_add_differentiable                    │
   (DECISIVE)     │   p_Z(z) = ∫ p_X(x)·p_Y(z-x) dx を点ごと微分可能 │
                  │   + logDeriv p_Z 表現 (起点: ParametricIntegral   │
                  │     hasDerivAt_integral_of_dominated_loc...)      │
                  └───────────────┬──────────────────┬───────────────┘
                                  │                  │
              ┌───────────────────┘                  └───────────────────┐
              ▼ (density witness +                          ▼ (per-time density
                logDeriv → score)                              witness p_t)
   ┌──────────────────────────┐                   ┌──────────────────────────────┐
   │ 壁1 (Phase 3, density route)│                 │ 壁2 (Phase 4)                │
   │ 明示積分 (condExp 不使用) │                   │ per-time de Bruijn           │
   │  s_Z = ∫ W_λ·p_{X|Z} dx  │                   │   (d/dt)h = (1/2)J            │
   │ + 点ごと CS (integral_mul │                   │   ← heat eq IBP (真壁可能性高)│
   │   _le_Lp_mul_Lq)         │                   │ + FTC 積分形                 │
   │ + Tonelli + cross=0(Ph2) │ ◀── 直列依存 ──   │   ← bounded_T_ftc_gaussian   │
   │ ⇒ convex Fisher bound    │     (壁2 の per-     │     一般化 (~60-100行)      │
   └──────────────────────────┘     time witness は  └──────────────────────────────┘
                                     壁1 apparatus を
   ┌──────────────────────────┐     消費)
   │ cross-term orth (Phase 2)│
   │   ∫ (s_X∘X)(s_Y∘Y)=0     │  ← gateway 非依存、Phase 1 と並行着手可
   │   condExp_indep_eq +     │
   │   IndepFun.integral_mul  │
   └──────────────────────────┘
```

**各壁が共通 apparatus のどこを消費するか**:

- 壁1 (Phase 3, **density route / condExp 不使用**) = gateway の `convDensityAddDeriv`/導関数表現 + Phase 2
  cross-term (`∫ fX' = 0`) + score を確率重み `p_{X|Z}(x|z) := fX(x)fY(z-x)/p_Z(z)` 上の明示積分
  `s_Z = ∫ W_λ·p_{X|Z}` で書き下し、点ごと積分 Cauchy-Schwarz (`integral_mul_le_Lp_mul_Lq_of_nonneg`) +
  Tonelli (`lintegral_lintegral_swap`) + p_Z 約分 → `λ²J_X+(1-λ)²J_Y` → λ最適化 (`stam_lambda_min`)。
  **`ConvexOn.map_condExp_le` / `integral_condExp` / disintegration は使わない** (旧 condExp 経路の残骸、
  §Phase 3 参照)。
- 壁2 (Phase 4) = gateway の per-time 特殊化 (`p_t = p_X ⋆ heatKernel_t`) の density witness +
  heat eq IBP (`integral_mul_deriv_eq_deriv_mul_of_integrable`、inventory §5) + Gaussian テンプレ
  `bounded_T_ftc_gaussian` (`EPIL3Integration.lean:937-985`、`@audit:ok`) の一般化。

**Wave 1 が確定した tractability の格下げ/格上げ** (Approach に効く):

- cross-term orthogonality は **真壁ではない** — `condExp_indep_eq`
  (`ConditionalExpectation.lean:42`) + `IndepFun.integral_mul_eq_mul_integral`
  (`Integration.lean:247`) + 既存 `integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:155`)
  で ~20-40 行。過去 inventory の `Found 0` は loogle bare-identifier query の false-negative。
- FTC 積分形は **Gaussian テンプレ同型が既に存在** — per-time de Bruijn さえ建てば ~60-100 行。
- genuine に不在で self-build 必須: (i) `⋆ₗ` 微分可能性 (`HasCompactSupport.*` 系 6 件は compact
  support 要求で Gaussian heat kernel 不適合)、(ii) heat eq density の IBP (`Mathlib.Analysis.PDE.*`
  不在)、(iii) 条件付き Blachman score 表現 (`condExp ∧ IndepFun` 同時 = loogle Found 0)。

**段階的 ship**: Phase 2 は gateway 非依存で単体 genuine 完成可 (atomic に ship)。Phase 1/3/4 は
gateway gate に従属、Phase 1 NO-GO 時は Phase 2 のみ回収して残りは sorry 据置のまま撤退。

## Phase 0 — 在庫確定 + 壁 signature verbatim 照合 📋

- [ ] Wave 1 inventory (`epi-wall-reattack-inventory.md`) の apparatus 1-10 テーブルを SoT として確認。
- [ ] gateway 起点 `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
      (`Mathlib/.../ParametricIntegral.lean:289`) の完全 signature を verbatim 照合
      (`[...]` type-class prereq + dominated 仮定の引数型を inventory に未収録なら追記依頼)。
- [ ] 壁 declaration の現 signature verbatim 確認 (済、本 plan 起草時):
      `stam_step2_density_wall:283` (regularity hyp `hX hY hXY` 保持済) /
      `debruijnIdentityV2_holds:245` (`X Z` + `IsRegularDeBruijnHypV2`、`_hX/_hZ/_hXZ` は **削除済**、
      forward-looking note `:234` 参照) / `debruijnIntegrationIdentity_holds:310` (存在形 `fPath`)。
- [ ] Gaussian テンプレ `bounded_T_ftc_gaussian` (`EPIL3Integration.lean:937-985`、`@audit:ok`) の
      結論 shape を verbatim 確認 (Phase 4 の一般化対象、shape contract を pin)。

proof-log: no (照合のみ)。

**Done 条件**: gateway 起点 lemma の dominated 仮定が inventory に verbatim 記録されている +
4 壁 declaration の現 signature を照合済。

## Phase 1 — gateway atom `convDensity_add_differentiable` (DECISIVE GATE) 📋

**この Phase の Done 判定が plan 全体の go/no-go gate。**

### 目標

独立 `X, Y` の和の pdf `p_Z(z) = ∫ x, p_X(x) · p_Y(z-x) ∂volume` が **点ごと微分可能** +
その `logDeriv p_Z` を condExp 接続可能な形で表現する gateway atom を建てる。両壁の唯一の共通
foundational helper。

### skeleton (sub-lemma を `:= by sorry` で列挙)

```lean
-- Common2026/Shannon/EPIConvDensity.lean (新規)
namespace InformationTheory.Shannon.EPIConvDensity

/-- 畳み込み密度の積分形 (sum density = ∫ p_X · p_Y(·-x))。Mathlib-shape-driven:
    結論を Bochner `∫` 形で述べ、ParametricIntegral lemma の結論形に合わせる。 -/
def convDensityAdd (pX pY : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ x, pX x * pY (z - x) ∂volume

/-- sub-1: 被積分関数の z 偏微分の dominated bound (Gaussian tail) — regularity hyp 群で pin。 -/
theorem convDensityAdd_dominated_deriv ... : ... := by sorry  -- @residual(wall:conv-score-smooth)

/-- sub-2: 点ごと HasDerivAt (起点: hasDerivAt_integral_of_dominated_loc_of_deriv_le)。 -/
theorem convDensityAdd_hasDerivAt ... : HasDerivAt (convDensityAdd pX pY) ... z := by
  sorry  -- @residual(wall:conv-score-smooth)

/-- sub-3: logDeriv 表現 (score of convolution の出発点、Blachman/Fisher 接続先)。 -/
theorem convDensityAdd_logDeriv ... : logDeriv (convDensityAdd pX pY) z = ... := by
  sorry  -- @residual(wall:conv-score-smooth)

/-- gateway atom: differentiable + logDeriv をまとめた公開 API。 -/
theorem convDensity_add_differentiable ... : ... := by sorry  -- @residual(...)
end ...
```

### dominated 仮定の pin 方法 (load-bearing bundling 禁止に注意)

`hasDerivAt_integral_of_dominated_loc_of_deriv_le` 適用には「z 近傍で被積分関数の z 偏微分が
可積分関数で上から押さえられる」dominated 仮定が要る。これを **regularity hyp として引数に pin**
する (Gaussian / 重テールでない密度クラスの precondition、honest hyp)。

- ✅ OK (regularity precondition): `pX pY` が Gaussian tail bound を満たす (`∃ C, |∂_z (pX x · pY (z-x))| ≤ g x ∧ Integrable g`)、`Measurable` / `Integrable pX` / `Integrable pY`。
- ❌ 禁止 (load-bearing): 「`convDensityAdd` が微分可能である」を `Is...Hyp` predicate として
  仮定に取って body を機械展開だけにする。これは結論の核を仮説に bundle する honesty defect
  (CLAUDE.md「検証の誠実性」)。詰まったら gateway atom body を `sorry` + `@residual` で残す。

### 撤退ライン

| slug | 内容 | 撤退口 |
|---|---|---|
| **L-EPIW-1-α** | Gaussian tail dominated 充足の自前構築 (`convDensityAdd_dominated_deriv`) が 1 セッション超過 | sub-lemma body `sorry` + `@residual(wall:conv-score-smooth)` 据置、Phase 全体 NO-GO 判定 |
| **L-EPIW-1-β** | `⋆ₗ` / convolution 密度の点ごと微分可能性が概念ごと組めない (`HasCompactSupport` 不適合の回避 = truncation + dominated convergence が PR 級) | gateway atom body `sorry` + `@residual(wall:conv-score-smooth)`、scope-out 確定診断を docstring 散文化、Phase 1 NO-GO |

### Done 条件 / go-no-go gate (★ plan 全体の判定点)

- **GO** = `convDensity_add_differentiable` (gateway atom) が **type-check done** で建つ
  (sub-1〜sub-3 のうち core の微分可能性 + logDeriv 表現が genuine、残るは regularity-only の
  dominated 仮定 pin のみ)。→ Phase 2/3/4 へ進む。
- **NO-GO** = L-EPIW-1-β 発火 (convolution 密度の点ごと微分可能性が truncation self-build で
  1 セッション超過 or 概念ごと組めない)。→ scope-out 確定、Phase 2 のみ独立回収、残り sorry 据置。

判定の決め手は **sub-2 `convDensityAdd_hasDerivAt` が genuine に閉じるか**。ここが
`HasCompactSupport` 不適合の壁 (inventory §3 ★) を truncation で迂回できるかの一点。dominated
仮定 (sub-1) は regularity pin で吸収できるので gate ではない。sub-2 が真壁なら NO-GO。

概算規模: 80-200 行 (sub-2 の truncation + dominated convergence が支配項)。

proof-log: yes。

## Phase 2 — cross-term orthogonality (self-buildable 確定部、gateway 非依存) 📋

honesty 補正部。**Phase 1 と独立に着手可能** (gateway 不要)。Wave 1 が「真壁ではない」と確定した部品。

### skeleton (inventory §着手 skeleton をそのまま使用)

```lean
-- Common2026/Shannon/EPIScoreCrossTermOrth.lean (新規)
/-- Score cross-term orthogonality (full-expectation version).
    独立 X,Y、mean-zero score。NOT a discharge of Blachman identity. -/
theorem score_cross_term_eq_zero
    {X Y : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {sX sY : ℝ → ℝ}
    (hXY : IndepFun X Y P)
    (hsX : AEStronglyMeasurable (fun ω => sX (X ω)) P)
    (hsY : AEStronglyMeasurable (fun ω => sY (Y ω)) P)
    (hmeanX : ∫ ω, sX (X ω) ∂P = 0) :
    ∫ ω, sX (X ω) * sY (Y ω) ∂P = 0 := by
  -- IndepFun.comp hXY → IndepFun.integral_fun_mul_eq_mul_integral → rw [hmeanX]; ring
  sorry  -- genuine に閉じる想定 (gateway 非依存)、詰まれば @residual(plan:epi-wall-reattack-plan)
```

### 組み方 (Mathlib 既存物)

1. `IndepFun X Y P` → `IndepFun (sX∘X) (sY∘Y) P` を `IndepFun.comp` で出す (plumbing 主)。
2. `IndepFun.integral_mul_eq_mul_integral` (`Integration.lean:247`、または姉妹
   `IndepFun.integral_fun_mul_eq_mul_integral:253`) で `∫ (sX∘X)(sY∘Y) = E[sX∘X]·E[sY∘Y]`。
3. `hmeanX : E[sX∘X] = 0` (repo `integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:155`) /
   `FisherInfoV2.n` / `n_pdf_eq_zero_gaussian` から供給) で `= 0`。

### false-negative 訂正 (同 commit)

過去 inventory (`epi-stam-condexp-score-discharge-mathlib-inventory.md:149`) の
`unknown identifier 'condExp_indep'` false-negative claim を docstring / inventory で訂正する
(`condExp_indep_eq` は `ConditionalExpectation.lean:42` に **実在**、loogle bare-identifier query の
失敗だった)。Wave 1 inventory §2 が SoT。

### Done 条件 / 撤退ライン

- **Done**: `score_cross_term_eq_zero` が 0 sorry / 0 residual (genuine 完成、独立 audit pass → `@audit:ok`)。
- 撤退ライン **L-EPIW-2-α**: `IndepFun.comp` の score 合成 measurability で予想外に詰まる場合のみ
  `sorry` + `@residual(plan:epi-wall-reattack-plan)`。確率低 (部品揃い確定)。

概算規模: 20-40 行。proof-log: yes。

## Phase 3 — 壁1 本体: 密度レベル明示積分経路 (condExp 不使用) 📋

> **2026-05-30 全面書換 (density pivot)**: 旧 Phase 3 は「真壁確定 (~300 行 PR 級 unscoped wall)」
> だった。だが独立 proof-pivot-advisor (density pivot 検証) が **`fisherInfoOfMeasureV2 _μ f =
> fisherInfoOfDensity f` (`FisherInfoV2DeBruijn.lean:86-87`, `rfl`、measure 引数を捨てる)** を起点に、
> `stam_step2_density_wall:376` の goal が**純粋に密度上の解析命題**に collapse する事実を発見。
> 前 advisor の「PR 級」判定は**抽象 condExp 経路限定**で、密度レベル明示経路はそれを概念ごと回避する。
> よって Phase 3 を「真壁」から **scoped multi-session path** に格下げ、本書換でその explicit route を
> authoritative 戦略として固定する。**`epi-blachman-density-route-inventory.md` の S1 disintegration /
> S3 `ConvexOn.map_condExp_le` / S4 `integral_condExp` は旧 condExp 経路の残骸で本経路とずれている** —
> inventory からは **API 部品 (積分 Cauchy-Schwarz / Tonelli / IBP / λ最適化) のみ消費**し、condExp 系の
> 戦略記述は採らない。

**Phase 1 GO (gateway `convDensityAdd_hasDerivAt`/`convDensityAdd_logDeriv` `@audit:ok`) + Phase 2 Done
(`score_cross_term_eq_zero` `@audit:ok`) + Phase 3-pre Done (4 述語 pivot 済、`hconv` 制約注入済) を前提**。
`stam_step2_density_wall` (`EPIStamInequalityBody.lean:376`) の `sorry` body を充足する。

### Approach (密度レベル明示積分経路 — condExp 不使用、orchestrator 検算済の骨子)

**鍵となる collapse**: `IsStamCauchySchwarzOptimal X Y P` の goal は (Phase 3-pre pivot 済 signature で)
`J_sum = (fisherInfoOfMeasureV2 (P.map (X+Y)) fXY).toReal` を含むが、`fisherInfoOfMeasureV2_def`
(`:86-87`, `rfl`) で measure 引数が捨てられるため `J_sum = (fisherInfoOfDensity fXY).toReal`。
`hconv : fXY =ᵐ[volume] convDensityAdd fX fY` 制約下、goal は**純粋に密度上の解析命題**
`(fisherInfoOfDensity fXY).toReal ≤ J_X·J_Y/(J_X+J_Y)` に縮約する。**抽象 condExp/condDistrib は不要**。

以下、`p_X := fX`, `p_Y := fY`, `p_Z(z) := convDensityAdd fX fY z = ∫ x, fX x · fY (z-x) ∂volume`。

1. **畳み込み密度の導関数表現** (gateway 消費): `p_Z'(z) = ∫ x, fX x · fY'(z-x) dx`
   (gateway `convDensityAddDeriv` `EPIConvDensity.lean:64` = `fun z x => pX x · deriv pY (z-x)`、
   `convDensityAdd_hasDerivAt` `:86` が `HasDerivAt (convDensityAdd pX pY) (∫ x, convDensityAddDeriv pX pY z₀ x) z₀`)。
2. **対称導関数恒等式 (S2)**: `∫ x, fX'(x)·fY(z-x) dx = ∫ x, fX(x)·fY'(z-x) dx = p_Z'(z)`
   (全直線 IBP `integral_mul_deriv_eq_deriv_mul_of_integrable` `IntegralEqImproper.lean:1318` + 1-D 変数変換
   `integral_sub_left_eq_self` / `integral_comp_sub_left` 系)。
3. **score 表現 (condExp 不要)**: 任意 `λ∈[0,1]` で
   `W_λ(x,z) := λ·(fX'(x)/fX(x)) + (1-λ)·(fY'(z-x)/fY(z-x))` とおくと、確率重み
   `p_{X|Z}(x|z) := fX(x)·fY(z-x)/p_Z(z)` (`∫ x, p_{X|Z}(x|z) dx = 1`) に対し
   `∫ x, W_λ(x,z)·fX(x)·fY(z-x) dx = λ·p_Z'(z) + (1-λ)·p_Z'(z) = p_Z'(z)` (step 2 の両表現が両項を与える)。
   よって score `s_Z(z) = p_Z'(z)/p_Z(z) = ∫ x, W_λ(x,z)·p_{X|Z}(x|z) dx`。**これは condExp の disintegration
   ではなく、明示的に書いた確率重み積分**。
4. **点ごと Cauchy-Schwarz (S3、condExp 不要)**: 確率重み `p_{X|Z}` に対し
   `s_Z(z)² = (∫ x, W_λ·p_{X|Z})² ≤ (∫ x, W_λ²·p_{X|Z})·(∫ x, p_{X|Z}) = ∫ x, W_λ²·p_{X|Z}`
   (Mathlib 積分 CS `integral_mul_le_Lp_mul_Lq_of_nonneg` `Bochner/Basic.lean:1237` を p=q=2 で、または
   `inner_mul_le_norm_mul_norm` 系)。**`ConvexOn.map_condExp_le` は使わない** (inventory S3 の condExp 版は本経路外)。
5. **積分 + Tonelli + p_Z 約分 (S4)**:
   `J_sum = ∫ z, s_Z(z)²·p_Z(z) dz ≤ ∫ z, (∫ x, W_λ(x,z)²·fX(x)·fY(z-x) dx) dz` (`p_{X|Z}·p_Z = fX·fY(z-x)`
   で `p_Z` 約分)。Tonelli (`integral_integral_swap` `Integral/Prod.lean:532`、または `∫⁻` 版
   `lintegral_lintegral_swap` `Measure/Prod.lean:1058`) で `(x,z)` 順序交換 + `W_λ²` 展開:
   - **第 1 項** `λ²·∫ x, (fX'/fX)²·fX·[∫ z, fY(z-x) dz] dx = λ²·∫ x, (fX')²/fX dx·1 = λ²·J_X`
     (`∫ z, fY(z-x) dz = ∫ fY = 1` を `hnormY` + 併進不変で)。
   - **第 2 項** `(1-λ)²·J_Y` (変数変換 `z-x ↦ y`、`hnormX`)。
   - **cross 項** `2λ(1-λ)·(∫ fX')·(∫ fY') = 0` (`∫ fX' = 0` 正規化密度の境界消失、Phase 2
     `score_cross_term_eq_zero` `EPIScoreCrossTermOrth.lean:45` で genuine 済 + `integral_logDeriv_density_eq_zero`
     `FisherInfoV2.lean:158` で `∫ logDeriv f · f = 0`)。
   ⇒ `J_sum ≤ λ²·J_X + (1-λ)²·J_Y` (任意 `λ∈[0,1]`)。
6. **λ 最適化 (S5、完済)**: `λ = J_Y/(J_X+J_Y)` で `stam_lambda_min` (`EPIStamInequalityBody.lean:204`,
   `@audit:ok`) + `stam_lambda_lower_bound` (`:216`, `@audit:ok`) により
   `J_sum ≤ J_X·J_Y/(J_X+J_Y)` = `IsStamCauchySchwarzOptimal` の結論。

**この経路が condExp を使わない帰結 (撤退ラインに効く)**: inventory が flag した「`condExp_ae_eq_integral_condDistrib_id`
の `[StandardBorelSpace]` / score `Integrable f μ` 前提が `IsStamCauchySchwarzOptimal` signature に漏れる」
懸念 (L-EPIW-3-密度-α) は **condExp 経路前提だった** ので本経路では発生しない。score 表現は step 3 で
明示積分として書き下すため、`condDistrib`/`StandardBorelSpace` 依存が一切無い。

### Phase 3 の atom 分解 (案 E pivot + 案 G staged shared sorry 補題)

advisor の A/B/C 分解を採用、multi-session 着手可能粒度に。各 atom は **shared sorry 補題化**し、未完は
`sorry` + `@residual` で type-check done commit (proof done は全 atom 完成時)。推奨実装 file は
`Common2026/Shannon/EPIBlachmanConvScore.lean` (新規、inventory 着手 skeleton の file 名を流用、ただし
**結論型は condExp ではなく上記 explicit route の各 step**)。

| atom | step | 内容 | 規模見積 | 支配項 / hard part |
|---|---|---|---|---|
| **Phase 3a (GATE)** | gateway hyp 充足 + S2 | atom B の土台 = gateway `convDensityAdd_hasDerivAt` (`:86`) の **regularity hyp 7 本** (`hs`/`hF_meas`/`hF_int`/`hF'_meas`/`h_bound`/`bound_integrable`/`h_diff`) を `IsRegularDensityV2 fX/fY` + 正規化から discharge 可能か独立検証。+ 対称導関数恒等式 (step 2)。 | 検証 + 40-80 行 | **`h_bound` (Gaussian-tail dominated)** が新 PR 級 self-build か否か = GO/NO-GO。dominated bound を regularity から導けるか |
| **Phase 3b** | S3 score + S4 CS | score 表現 (step 3、確率重み `p_{X|Z}` 明示積分) + 点ごと Cauchy-Schwarz (step 4)。 | 60-120 行 | score 表現の `p_Z` 約分 + 確率重み正規化 `∫ p_{X|Z} = 1` の plumbing |
| **Phase 3c** | S4 Tonelli + 3 項 | Tonelli 積分 (step 5) + 3 項評価 (`J_X`/`J_Y`/cross=0) + **lintegral↔Bochner 橋 (atom A)**: `(fisherInfoOfDensity f).toReal = ∫ (logDeriv f)²·f` (`integral_eq_lintegral_of_nonneg_ae` + 可積分性副条件)。 | 80-150 行 | **Tonelli の積測度上可積分性副条件** (`Integrable (uncurry …) (volume.prod volume)`) — `∫⁻` 版に揃えれば非負性で回避可、Bochner 版なら self-build。lintegral↔Bochner の `.toReal` 往復 |
| **Phase 3d** | assemble | `stam_step2_density_wall` (`:376`) の `sorry` を 3a–3c の補題で genuine 充足 (S5 λ 最適化は既済呼出のみ)。 | 30-60 行 | 各 atom の signature 整合 (hyp の流れ込み) |

支配項 (advisor): **atom B (Phase 3a) の gateway hyp 充足** + **atom C (Phase 3c) の Tonelli 可積分性副条件**
が hard part。L-EPIW-3-α は atom B の `h_bound` が PR 級なら発火。

### per-atom Mathlib API 在庫 (inventory から API 部品のみ引用、verbatim 前提付き)

inventory のうち **S1 disintegration / condExp 系は採らない**。以下は explicit route で実消費する API:

- **Phase 3a (gateway hyp + S2)**:
  - gateway `EPIConvDensity.convDensityAdd_hasDerivAt` (`EPIConvDensity.lean:86`) — 7 hyp:
    `hs : s ∈ nhds z₀` / `hF_meas : ∀ᶠ z in nhds z₀, AEStronglyMeasurable (fun x => pX x * pY (z - x)) volume` /
    `hF_int : Integrable (fun x => pX x * pY (z₀ - x)) volume` /
    `hF'_meas : AEStronglyMeasurable (fun x => convDensityAddDeriv pX pY z₀ x) volume` /
    `h_bound : ∀ᵐ x ∂volume, ∀ z ∈ s, ‖convDensityAddDeriv pX pY z x‖ ≤ bound x` /
    `bound_integrable : Integrable bound volume` /
    `h_diff : ∀ᵐ x ∂volume, ∀ z ∈ s, HasDerivAt (fun z => pX x * pY (z - x)) (convDensityAddDeriv pX pY z x) z`
    → 結論 `HasDerivAt (convDensityAdd pX pY) (∫ x, convDensityAddDeriv pX pY z₀ x ∂volume) z₀`。
    **Phase 3a の検証対象 = この 7 hyp を `IsRegularDensityV2 fX/fY` + `hnormX/hnormY` から discharge できるか。**
  - S2 IBP `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable` (`IntegralEqImproper.lean:1318`):
    型クラス前提 `{A : Type*} [NormedRing A] [NormedAlgebra ℝ A]` (`A = ℝ` で充足)。引数 `hu`/`hv`
    (tsupport 上 `HasDerivAt`) + `huv'`/`hu'v`/`huv` (3 つの `Integrable`、score×密度積の可積分性 =
    regularity precondition)。結論 `∫ (x : ℝ), u x * v' x = - ∫ (x : ℝ), u' x * v x`。
  - 併進不変 `MeasureTheory.integral_sub_left_eq_self` (`Group/Integral.lean`、gateway `convDensityAdd_comm` で
    使用実績あり) — `z-x` 置換。
- **Phase 3b (S3 score + CS)**:
  - 積分 Cauchy-Schwarz `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` (`Bochner/Basic.lean:1237`):
    型クラス前提 `{α : Type*} [MeasurableSpace α] {μ : Measure α}` (本補題は `f g : α → ℝ`)。引数
    `hpq : p.HolderConjugate q` / `hf_nonneg : 0 ≤ᵐ[μ] f` / `hg_nonneg : 0 ≤ᵐ[μ] g` /
    `hf : MemLp f (ENNReal.ofReal p) μ` / `hg : MemLp g (ENNReal.ofReal q) μ`。結論
    `∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q)`。**p=q=2 で CS**。
    (重み付き CS は `f = W_λ·√p_{X|Z}`, `g = √p_{X|Z}` の取り方、または `∫⁻` 版 `ENNReal.lintegral_mul_le_Lp_mul_Lq`)。
- **Phase 3c (S4 Tonelli + 3 項 + lintegral↔Bochner)**:
  - Tonelli `MeasureTheory.lintegral_lintegral_swap` (`Measure/Prod.lean:1058`、**`∫⁻` 版優先 = 可積分性不要**):
    型クラス前提 `[SFinite μ]` + section `[SFinite ν]` (`volume` は SFinite で充足)。引数
    `hf : AEMeasurable (uncurry f) (μ.prod ν)`。結論 `∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν`。
  - Bochner 版 `MeasureTheory.integral_integral_swap` (`Integral/Prod.lean:532`): 両 measure SFinite +
    引数 `hf : Integrable (uncurry f) (μ.prod ν)` (**この可積分性副条件が atom C の hard part**)。結論
    `∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν`。
  - cross 項 `∫ fX' = 0`: `FisherInfoV2.integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:158`,
    `@audit:ok`、結論 `∫ x, logDeriv f x * f x ∂volume = 0`) + Phase 2 `score_cross_term_eq_zero`
    (`EPIScoreCrossTermOrth.lean:45`, `@audit:ok`)。
  - lintegral↔Bochner 橋 (atom A): `J = (fisherInfoOfDensity f).toReal = (∫⁻ ofReal((logDeriv f)²·f)).toReal`
    と Bochner `∫ (logDeriv f)²·f` の往復 = `integral_eq_lintegral_of_nonneg_ae` + 非負性 + 可積分性副条件
    (`fisherInfoOfDensity` `FisherInfoV2.lean:89` / `fisherInfoOfDensityReal` `:103`)。
- **Phase 3d (assemble)**: S5 λ 最適化 `stam_lambda_min` (`EPIStamInequalityBody.lean:204`, `@audit:ok`) +
  `stam_lambda_lower_bound` (`:216`, `@audit:ok`) は既済呼出のみ (0 行 self-build)。

### 撤退ライン

| slug | 内容 | 撤退口 |
|---|---|---|
| **L-EPIW-3-α** | atom B (Phase 3a) の gateway hyp `h_bound` (Gaussian-tail dominated) が `IsRegularDensityV2` から導けず新 PR 級 self-build = **honest sorry 据置継続** (この場合のみ撤退) | `stam_step2_density_wall` body `sorry` + `@residual(wall:stam-blachman)` 据置 (regularity hyp は維持、honesty defect 化させない)。未完 atom も各 shared sorry 補題に `sorry` + `@residual(wall:stam-blachman)` で type-check done、完成 atom (3b/3c の Mathlib 部品揃いパート) は genuine ship |
| **L-EPIW-3-密度-α** | inventory が flag した「score 可積分性が `IsStamCauchySchwarzOptimal` signature に漏れる」懸念。**ただし本経路は condExp を使わないので `StandardBorelSpace`/`condExp_ae_eq_integral_condDistrib_id` の signature 漏れは発生しない** (この懸念は condExp 経路前提だった) | 本経路では原則発火しない。万一 atom C の Tonelli 可積分性副条件が `IsStamCauchySchwarzOptimal` の hyp に新規漏れする場合のみ、該当副条件を `IsRegularDensityV2` から導く plumbing で吸収 (regularity precondition なので signature 後退ではない)。導けなければ当該 atom のみ `sorry` + `@residual(wall:stam-blachman)` |
| **L-EPIW-3-密度-β** (Phase 3b 着手で実観測 → **2026-05-30 決定済、判断ログ #6 + §Phase 3d**) | **precondition gap**: density route は `deriv f` 有界 (`hX'_bdd/hY'_bdd`) + 14 個の高階 integrability を要求するが target predicate `IsStamCauchySchwarzOptimal` は `IsRegularDensityV2` (= `deriv f` 有界を含意しない、`Differentiable` は連続導関数すら不保証) + `∫=1` + `hconv` しか供給しない。`f` 有界は連続+tail→0 から導出可、**`deriv f` 有界は導けない**のが gap の核 | **決定 = 案 b (述語に boundedness/integrability hyp 追加)**。`stam_step2_density_wall` の追加 theorem 仮説で thread する案 c は **不可** (predicate は任意 regular density を量化 → 任意 regular density に deriv 有界を要求すると false 仮定)。案 a (`IsRegularDensityV2` に field 追加) は構築サイト 0 件で ripple 実質ゼロだが Gaussian instance 未 wire で非 vacuousness の検証点が増える。**いずれも honesty 上は precondition 追加であって signature 後退ではない** (Gaussian witness 非 vacuous、ただし非 vacuousness の最終確証は Gaussian instance wiring = closure 条件)。比較表 + proof skeleton + 新規 atom は §Phase 3d。導出/整合が 1 セッション超なら当該 atom のみ `sorry` + `@residual(wall:stam-step2-density)` |
| **L-EPIW-3-β** | S5 λ 最適化が `linarith` 吸収不可で >50 行 | 発動見込みなし (`stam_lambda_min` 既済 `@audit:ok`)。万一の場合 step 6 のみ `sorry` + `@residual(plan:epi-wall-reattack-plan)` |

**honesty 規律**: 注入済 hyp (`hconv` 畳み込み / `hregX/hregY` 密度性 / `hnormX/hnormY` 正規化) は
**regularity precondition** であって不等式の核ではない。step 1-6 の analytic core を `Is...Hyp` predicate に
bundle して `:= h` 機械展開で抜くのは禁止 (tier 5 load-bearing)。詰まれば必ず `sorry` +
`@residual(wall:stam-blachman)`。score 表現を確率重み積分で明示するため、core を condExp predicate に
潰す誘惑は構造的に発生しない。

概算規模: 全 atom 合計 ~210-410 行 (atom B の gateway hyp 充足 + atom C の Tonelli 可積分性副条件が
支配項)。proof-log: yes (`epi-wall-reattack-proof-log.md` に per-atom 追記)。

## Phase 3d — assemble: `stam_step2_density_wall` を genuine 充足 📋

> closure 対象: `Common2026/Shannon/EPIStamInequalityBody.lean:376` `stam_step2_density_wall`
> (現 `@residual(wall:stam-step2-density)` の `sorry`、結論 `IsStamCauchySchwarzOptimal X Y P`)。
> 解析核は `convex_fisher_bound` (`EPIBlachmanDensity.lean:538`, `@audit:ok`) で完成済。残るは
> **predicate と density route の precondition 整合のみ**。

### Context (verbatim 確認済の事実)

- **解析核 = 完成**: `convex_fisher_bound` (`EPIBlachmanDensity.lean:538`、23 引数) は genuine
  0-sorry `@audit:ok`。結論 `(fisherInfoOfDensity (convDensityAdd fX fY)).toReal ≤
  lam²·(fisherInfoOfDensity fX).toReal + (1-lam)²·(fisherInfoOfDensity fY).toReal`。
- **`fisherInfoOfMeasureV2 _μ f = fisherInfoOfDensity f`** (`FisherInfoV2DeBruijn.lean:86-87`,
  `rfl`、measure 引数を捨てる)。`IsStamCauchySchwarzOptimal` の `J_X/J_Y/J_sum` 定義式は
  この rfl で `fisherInfoOfDensity` に潰れる。
- **`fisherInfoOfDensity f = ∫⁻ x, ofReal((logDeriv f x)²)·ofReal(f x)`**
  (`FisherInfoV2.lean:89-90`、lintegral 形)。`fisherInfoOfDensity` の ae-congruence は
  lintegral レベルの `lintegral_congr_ae` (Mathlib 存在確認済) を要するが、被積分関数に
  `logDeriv fXY` が入るため `fXY =ᵐ convDensityAdd` から `logDeriv fXY =ᵐ logDeriv (convDensityAdd …)`
  への ae 持ち上げが必要 (`logDeriv = deriv / f`、`Filter.EventuallyEq.deriv` 存在確認済だが
  deriv の ae 等式は点ごと等式より弱く、一般には deriv が ae-congruent でない ⇒ **atom 化が必要、要 verbatim**)。
- **lockstep 述語**: `IsStamCauchySchwarzOptimal` (`EPIStamInequalityBody.lean:278`、結論
  `J_sum ≤ J_X·J_Y/(J_X+J_Y)`) と **同形の sibling** `IsStamCondExpCSHyp`
  (`EPIStamStep12Body.lean:210`、結論 `∀λ∈[0,1], J_sum ≤ λ²J_X+(1-λ)²J_Y`) が既存。後者は
  `convex_fisher_bound` の結論と **完全一致** (∀λ 凸上界形)。`stamCauchySchwarzOptimal_of_condExpCSHyp`
  (`:282`, `@audit:ok`) が `IsStamCondExpCSHyp → IsStamCauchySchwarzOptimal` を `stam_lambda_min`
  経由で既に橋渡し済。`isStamCauchySchwarz_of_condExpCSHyp` (`:231`) / `isStamCondExpCSHyp_symm`
  (`:252`) / `isStamCondExpCSHyp_congr` (`:245`) も同述語の consumer。

### 実測値 (gap 決定の根拠)

| 計測項目 | 実測値 | 出典 (verbatim) |
|---|---|---|
| `IsRegularDensityV2` **構築サイト** (`⟨…⟩` / `.mk` / `isRegularDensityV2_*` 生成補題) | **0 件** | `rg 'IsRegularDensityV2' Common2026/` 全件が hypothesis (consumption) のみ。構築補題・anonymous ctor・`{ diff := … }` ゼロ |
| `IsRegularDensityV2` の Gaussian instance wiring | **未 wire (0 件)** | `FisherInfoGaussian`/`FisherInfoV2Gaussian` に `IsRegularDensityV2` 構築なし。`FisherInfoV2.lean:316-323` は「V1 → V2 induces」の散文 note のみ (補題未実装) |
| `IsRegularDensityV2` field projection (消費、field 追加で壊れない) | `.diff/.pos/.tail_*/.integrable_deriv/.integral_deriv_eq_zero` 計 **12 箇所** | `rg -o '\.diff\|\.pos\|…'`。全て read-only projection、field 追加で非破壊 |
| `IsStamCauchySchwarzOptimal` の producer | **2 件** | `stam_step2_density_wall:380` (target) + `stamCauchySchwarzOptimal_of_condExpCSHyp:284` (condExp route) |
| `IsStamCauchySchwarzOptimal` の consumer (hypothesis 形) | `stam_inequality_via_predicate_optimal:406` + `:437` + `:490` + `:562` (= EPI 本線への橋) | `rg 'IsStamCauchySchwarzOptimal'` |
| lockstep 同形述語 (`convDensityAdd` block 共有) | `IsStamCondExpCSHyp` (`Step12Body:210`) / `IsStamCauchySchwarz` (`InequalityBody:156`) / `IsStamScoreConvolution` (`:116`) + 関連 wrapper | `rg 'IsRegularDensityV2 fX →'` 該当 4 file |

**実測の含意**: `IsRegularDensityV2` の構築サイト 0 件 ⇒ 案 a の field 追加は既存コードに **ripple ゼロ**
(consumer 12 件は projection のみで非破壊、新 field を埋める構築サイトが存在しないので「埋め漏れ」も発生しない)。
しかし構築サイト 0 件 = **どの witness も存在しない** = Gaussian instance が未実装。これは案 a/b 共通の
closure 前提 (下記 Approach の非 vacuousness 節)。

### Approach (決定: 案 b' = `IsStamCondExpCSHyp` 経由 + boundedness/integrability hyp は述語に追加)

**全体形**: `stam_step2_density_wall` の body を、まず **∀λ 凸上界形 `IsStamCondExpCSHyp X Y P`** を
genuine に構築し、既存 `@audit:ok` 橋 `stamCauchySchwarzOptimal_of_condExpCSHyp` で
`IsStamCauchySchwarzOptimal X Y P` に変換する 2 段構成にする。`convex_fisher_bound` の結論
(`J_sum ≤ λ²J_X+(1-λ)²J_Y`) が `IsStamCondExpCSHyp` の body と **completely 一致**するため、λ 最適化
(`stam_lambda_min`) を自前で書かず既存橋に委譲できる (step 7-8 が 1 補題呼び出しに圧縮)。

**precondition gap の解消 = 案 b**: density route が要求する `deriv f` 有界 (`hX'_bdd/hY'_bdd`) +
14 integrability を、`IsStamCondExpCSHyp` (+ それを消費する `IsStamCauchySchwarzOptimal`、および
sibling `IsStamCauchySchwarz`) の **量化された hypothesis として追加**する。理由 (verbatim 確認済の
構造的制約):

- predicate は **任意の** regular density `fX fY` を量化する (`∀ fX fY fXY, … → IsRegularDensityV2 fX
  → …`)。よって「`deriv f` 有界」を `stam_step2_density_wall` の **追加 theorem 仮説**として渡す案 c は
  **false 仮定** — 任意 regular density が有界導関数を持つわけではない (有界でない反例が `IsRegularDensityV2`
  を満たしうる)。案 c は honesty defect (degenerate/false-hypothesis 系)、**採らない**。
- 不足 regularity を置けるのは **predicate 内 (案 b)** か **`IsRegularDensityV2` structure 内 (案 a)** のみ。
- 案 a vs 案 b の比較:

| 軸 | 案 a (`IsRegularDensityV2` に `deriv_bdd` + integrability field 追加) | **案 b (述語に hyp 追加) ← 採用** |
|---|---|---|
| ripple (既存コード) | 構築サイト 0 件 ⇒ 実質ゼロ。consumer 12 件 projection 非破壊 | lockstep 述語 (`IsStamCondExpCSHyp`/`IsStamCauchySchwarzOptimal`/`IsStamCauchySchwarz` + consumer wrapper 群) の量化ブロックに hyp 追加 = Phase 3-pre の 4 述語 pivot と **同型操作** (既に 1 度実施・成功) |
| 影響範囲 | structure field は EPI 以外 (FisherInfoV2 closed-form 等) の `IsRegularDensityV2` 利用にも波及 (semantic に過剰) | EPI Stam チェーン局所に閉じる。`integral_logDeriv_density_eq_zero` 等の非 Stam consumer は無傷 |
| semantic 妥当性 | `deriv f` 有界・高階 integrability は「regular density の定義」ではなく「**畳み込み Fisher 解析に必要な追加 regularity**」⇒ structure に入れると定義の意味が肥大 | 「Stam Step 2-3 を density route で閉じるための precondition」として **使う場所に置く**のが正しい局所化 |
| 非 vacuousness 検証 | field 追加で既存 0 witness 状態が悪化 (Gaussian instance 未 wire のまま新 field 要求) | 既存 4 述語 pivot precedent と同じ Gaussian witness 議論で済む (述語 hyp は構築 obligation を Gaussian instance に集約、§非 vacuousness) |

採用根拠: **案 b は影響が EPI Stam チェーン局所に閉じ、semantic に「使う場所に precondition を置く」原則
(CLAUDE.md regularity-as-precondition) と整合**。案 a は ripple こそゼロだが structure 定義の意味を
肥大させ、非 Stam consumer (FisherInfoV2 closed-form) に無関係な field を背負わせる。Phase 3-pre で
4 述語 pivot を成功させた precedent があり、案 b の lockstep pivot は既知の安全操作。

**非 vacuousness (案 b の honesty 担保 = closure 条件)**: 案 b で述語に追加する boundedness/integrability
hyp は **load-bearing でない regularity precondition** だが、その非 vacuousness は「Gaussian witness が
全 hyp を同時に満たす」ことに依存する。現状 `IsRegularDensityV2` の Gaussian instance すら未 wire
(構築サイト 0 件) なので、**Phase 3d closure の最終条件 = Gaussian instance が新 boundedness/integrability
hyp 群を含む全 precondition を discharge する補題 (`isStamCondExpCSHyp_of_gaussian` 相当) の実装**。これを
下流 task として明示し、Phase 3d 自体の `sorry` 解消 (= `stam_step2_density_wall` body が
`convex_fisher_bound` 適用で 0-sorry) と非 vacuousness 確証 (Gaussian instance) を 2 段で扱う。**Gaussian
instance 未完の間は predicate hyp が vacuously satisfiable な懸念を独立 honesty audit に明示**すること。

### proof skeleton (`stam_step2_density_wall` body、案 b' 採用)

各 step に **[genuine 可能] / [新規 atom 要] / [撤退口]** を付す。

```
theorem stam_step2_density_wall … : IsStamCauchySchwarzOptimal X Y P := by
  -- 案 b': まず ∀λ 凸上界 IsStamCondExpCSHyp を建てて既存橋で optimal へ
  apply stamCauchySchwarzOptimal_of_condExpCSHyp   -- (EPIStamStep12Body:282, @audit:ok)
  -- goal: IsStamCondExpCSHyp X Y P
  intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def
    hregX hregY hnormX hnormY hconv  -- (案 b 後: + 新 boundedness/integrability hyp)
  intro lam hlam0 hlam1
  -- goal: J_sum ≤ lam²·J_X + (1-lam)²·J_Y
```

1. **`apply stamCauchySchwarzOptimal_of_condExpCSHyp` + `intro`** — [genuine 可能]。`IsStamCondExpCSHyp`
   の量化 (J/f/正規化/hconv/λ) を展開。**案 b の hyp 追加はこの量化ブロックに入る** (`IsStamCondExpCSHyp`
   def 自体を pivot)。
2. **J_X/J_Y/J_sum の `fisherInfoOfMeasureV2_def` (rfl) rewrite** — [genuine 可能]。`hJX_def : J_X =
   (fisherInfoOfMeasureV2 (P.map X) fX).toReal` を `rw [fisherInfoOfMeasureV2_def] at hJX_def` で
   `J_X = (fisherInfoOfDensity fX).toReal` に。J_Y/J_sum 同様。`fisherInfoOfMeasureV2_def`
   (`FisherInfoV2DeBruijn.lean:86`, rfl) verbatim 確認済。
3. **`hconv : fXY =ᵐ convDensityAdd fX fY` で J_sum の fXY を convDensityAdd に置換** —
   **[新規 atom 要 — atom Cong]**。`(fisherInfoOfDensity fXY).toReal = (fisherInfoOfDensity
   (convDensityAdd fX fY)).toReal` の ae-congruence。`fisherInfoOfDensity` は `∫⁻ ofReal((logDeriv
   f)²)·ofReal(f)` なので `lintegral_congr_ae` (確認済) で被積分関数 ae 等式に帰着するが、`logDeriv fXY
   =ᵐ logDeriv (convDensityAdd …)` が **deriv の ae 持ち上げ**を要する。点ごと等式なら `logDeriv` も点ごと
   等しいが、`=ᵐ` のみだと一般に deriv は ae-congruent でない。**要 verbatim 検討**: (i) `convex_fisher_bound`
   は密度引数を `convDensityAdd fX fY` で受けるので、`fXY =ᵐ convDensityAdd` を `J_sum` 計算に通すには
   atom Cong が必須。(ii) 撤退口: atom Cong が deriv ae 問題で詰まる場合、`IsStamCondExpCSHyp` の hconv を
   **点ごと等式 `∀x, fXY x = convDensityAdd fX fY x`** に強める pivot (regularity precondition 強化、
   Gaussian saturation では実際に点ごと一致するので非 vacuous) を検討。これは案 b と同じ述語 pivot 操作。
   → Mathlib API 当て先予測: `MeasureTheory.lintegral_congr_ae` (確認済) + `Filter.EventuallyEq.deriv`
   (確認済、ただし条件付き)。**verbatim 前提**。
4. **convDensityAdd 正値 `hpZ : ∀z, 0 < convDensityAdd fX fY z` の供給** —
   **[新規 atom 要 — atom Pos]**。`convex_fisher_bound` は `hpZ` を引数に要求。`fX,fY > 0`
   (`hregX.pos`/`hregY.pos`) + integrable から `convDensityAdd fX fY z = ∫ x, fX x·fY(z-x) > 0` を導く
   補題。Mathlib 当て先予測: `MeasureTheory.integral_pos_of_integrable_nonneg_nonzero`
   (loogle 確認済、`Bochner/Basic`) — 被積分 `fX·fY(z-·) ≥ 0` a.e. + integrable + ≠0 a.e. から `> 0`。
   integrable は `hint_X`/`hint_Y` 系から、`≠ 0` a.e. は `pos` から。**verbatim 前提**。撤退口: 詰まれば
   `hpZ` を `IsStamCondExpCSHyp` 述語の追加 precondition に格上げ (案 b の枠内、Gaussian 充足)。
5. **f / deriv f 有界 (`hX_bdd/hX'_bdd/hY_bdd/hY'_bdd`) の供給** — [案 b で述語 hyp として供給]。
   `f` 有界 (`hX_bdd/hY_bdd`) は連続 (`hreg.diff.continuous`) + tail→0 (`hreg.tail_*`) から compact 上 max
   + 外側 ~0 で **導出可能** (atom Bdd-f、下記)。`deriv f` 有界 (`hX'_bdd/hY'_bdd`) は **`IsRegularDensityV2`
   から導けない** ⇒ **案 b の boundedness hyp として `IsStamCondExpCSHyp` に追加**。
   - **[新規 atom 要 — atom Bdd-f]** (任意): `f` 有界を連続+tail から導く補題。詰まれば deriv 有界と同様に
     述語 hyp に格上げ (案 b、honesty 上 precondition 追加)。Mathlib 当て先: `IsCompact.exists_bound_of_continuousOn`
     + tail の `Tendsto … (nhds 0)` から外側評価。**verbatim 前提**。
6. **14 個の integrability の供給** — [大半 案 b で述語 hyp、一部 regularity 由来]。`convex_fisher_bound`
   の引数: `hX_int/hY_int` (Integrable fX/fY)、per-z `hint_X/hint_Y/hcond_int/hint_W/hint_Wsq`、
   `hint_inner`、`hint_fisherX/Y/Z`、prod `hint_prod1/2/3`。分類表:

   | precondition | `IsRegularDensityV2` から導出可? | 供給方法 |
   |---|---|---|
   | `hX_int/hY_int : Integrable fX/fY` | △ (`∫=1` + nonneg + 連続から、ただし integrable 自体は別命題) | 述語 hyp 追加 (案 b) が安全。`hnormX:∫=1` は density が integrable な前提を含意するが Lean では別途要 |
   | `hX_bdd/hY_bdd` | ○ (連続+tail、atom Bdd-f) | 導出 or 述語 hyp |
   | `hX'_bdd/hY'_bdd` (deriv 有界) | **✗** (`Differentiable` は連続導関数すら不保証) | **述語 hyp 必須 (案 b 核)** |
   | `hpZ` (0 < convDensityAdd) | ○ (atom Pos、fX,fY>0+integrable) | 導出 (atom Pos) |
   | per-z `hint_X/hint_Y` (Integrable deriv·factor) | ✗ (deriv の積の可積分性、有界×integrable が要る) | 述語 hyp (案 b)、deriv 有界 hyp に依存 |
   | `hcond_int` (Integrable condDensityX) | △ | 述語 hyp |
   | `hint_W/hint_Wsq` (scoreWeight·condDensityX) | ✗ (logDeriv の積) | 述語 hyp (案 b) |
   | `hint_inner` (∫inner·p_Z) | ✗ | 述語 hyp |
   | `hint_fisherX/Y/Z` (logDeriv²·f、Fisher 被積分) | ✗ (Fisher info の Bochner 可積分性、J<∞ 相当) | 述語 hyp (案 b)。**J_X/J_Y/J_sum > 0 が finite を含意するが Lean では別途 Integrable が要る** |
   | `hint_prod1/2/3` (積測度 uncurry) | ✗ (Tonelli 副条件) | 述語 hyp (案 b) |

   **撤退口**: integrability hyp 群を述語に追加すると `IsStamCondExpCSHyp` の signature が肥大する。
   honesty 上は全て regularity/可積分性 precondition (core を bundle しない) なので OK だが、**独立 honesty
   audit で「14 hyp が core を漏らさないこと」を再確認**すること (`convex_fisher_bound` の `@audit:ok`
   監査が既に「none bundles the inequality core」を確認済 — その引数群をそのまま述語に上げる操作なので
   honesty は保たれるが、predicate 化で見かけ上 load-bearing に見えやすい点を audit brief に明示)。
   1 セッションで全 14 thread が無理なら当該 integrability を `sorry` 化せず、**未供給の hyp を残した
   部分適用**で `convex_fisher_bound` を呼べないため、その場合は body 全体を `sorry` +
   `@residual(wall:stam-step2-density)` 据置 (atom 単位の部分 ship は不可、assemble は all-or-nothing)。
7. **`convex_fisher_bound` を一般 λ で適用** — [genuine 可能]。step 2-6 で全 23 引数を供給し、結論
   `(fisherInfoOfDensity (convDensityAdd fX fY)).toReal ≤ lam²·(fisherInfoOfDensity fX).toReal +
   (1-lam)²·(fisherInfoOfDensity fY).toReal` を得る。step 2 の rewrite で `J_X = (fisherInfoOfDensity
   fX).toReal` 等が成立しているので `J_sum ≤ lam²·J_X + (1-lam)²·J_Y` に書き換わる = `IsStamCondExpCSHyp`
   の goal。**案 b' のため λ 最適化 (`stam_lambda_min`) は step 1 の `stamCauchySchwarzOptimal_of_condExpCSHyp`
   が内部で実行済** ⇒ ここで自前 λ* 代入 (`λ = J_Y/(J_X+J_Y)`) は **不要**。
8. **(案 b' では step 8 消滅)** — 旧 brief の `stam_lambda_min` 直接適用 + harmonic-mean 変換は
   `stamCauchySchwarzOptimal_of_condExpCSHyp` (`:282`、内部で `stam_lambda_min` 呼出済 `@audit:ok`) に
   委譲済。`stam_step2_density_wall` body 側で λ* を扱わない分、**genuine 化の表面積が縮小** (∀λ 形を
   作るだけで optimal 形は既存橋が保証)。

### 新規 atom リスト (Phase 3d で実装、各 Mathlib 当て先予測 — verbatim 前提)

| atom | 内容 | Mathlib API 当て先 (予測、verbatim 前提) | genuine 見込み / 撤退口 |
|---|---|---|---|
| **atom Cong** | `fisherInfoOfDensity` の ae-congruence: `fXY =ᵐ g ⇒ (fisherInfoOfDensity fXY).toReal = (fisherInfoOfDensity g).toReal` | `MeasureTheory.lintegral_congr_ae` (✓存在) + `Filter.EventuallyEq.deriv` (✓存在、条件付き)。deriv の ae 持ち上げが核 | deriv ae で詰まれば hconv を点ごと等式に強化 (述語 pivot、案 b 枠内、Gaussian 点ごと一致で非 vacuous) |
| **atom Pos** | `convDensityAdd fX fY z > 0` from `fX,fY>0` + integrable | `MeasureTheory.integral_pos_of_integrable_nonneg_nonzero` (✓loogle、`Bochner/Basic`) | 詰まれば `hpZ` を述語 precondition に格上げ |
| **atom Bdd-f** (任意) | `f` 有界 from 連続+tail→0 | `IsCompact.exists_bound_of_continuousOn` 系 + tail 評価 | 詰まれば `hX_bdd/hY_bdd` を述語 hyp に格上げ (案 b、deriv 有界と並置) |
| **述語 pivot (案 b)** | `IsStamCondExpCSHyp` (+ `IsStamCauchySchwarzOptimal` + `IsStamCauchySchwarz` lockstep) に `deriv f` 有界 + 14 integrability hyp 追加 | (Mathlib 不要、signature pivot)。Phase 3-pre 4 述語 pivot と同型 | hyp 追加で consumer (`isStamCauchySchwarz_of_condExpCSHyp:231` 等) が壊れたら同 commit で hyp を thread。1 セッション超なら撤退口 = body `sorry` 据置 |
| **Gaussian instance (closure 条件、下流 task)** | `isStamCondExpCSHyp_of_gaussian` 相当: Gaussian density が新 boundedness/integrability hyp 群 + 既存 `IsRegularDensityV2` を全 discharge | `differentiable_gaussianPDFReal` / Gaussian tail / closed-form `fisherInfoOfDensity_gaussianPDFReal` (✓repo) | Phase 3d の `sorry` 解消とは別 task。非 vacuousness の最終確証点 |

### Done 条件 / proof-log

- **type-check done** (commit OK): `IsStamCondExpCSHyp`/`IsStamCauchySchwarzOptimal`/`IsStamCauchySchwarz`
  への hyp 追加 (案 b pivot) 後、全 consumer file (`EPIStamStep12Body`/`EPIStamInequalityBody`/
  `EPIStamDischarge`/`EntropyPowerInequality`/`EPIStamStep3Body`/`EPIStamDeBruijnConclusion`) が
  `lake env lean` 0 errors。未供給 integrability があれば該当 declaration のみ `sorry` +
  `@residual(wall:stam-step2-density)`。
- **proof done** (`stam_step2_density_wall` 0-sorry): atom Cong/Pos genuine + step 5-6 の全 14 hyp が
  述語経由で供給 + `convex_fisher_bound` 適用成功 + `stamCauchySchwarzOptimal_of_condExpCSHyp` 橋。
  この時点で `@residual(wall:stam-step2-density)` を外し、独立 honesty audit (案 b の hyp 群が core を
  漏らさないこと + Gaussian instance の vacuousness 懸念) pass で `@audit:ok`。
- **非 vacuousness 確証** (Gaussian instance wiring): 下流 task、Phase 3d の `sorry` 解消とは分離。
  closure 条件として handoff に明示。
- proof-log: **yes** (`epi-wall-reattack-proof-log.md` に per-atom + 述語 pivot ripple を追記)。

### 撤退ライン (Phase 3d 固有、上表 L-EPIW-3-* に追補)

| slug | 内容 | 撤退口 |
|---|---|---|
| **L-EPIW-3d-α** | atom Cong (`fisherInfoOfDensity` ae-congr) が deriv の ae 持ち上げで詰まる | hconv を `IsStamCondExpCSHyp` 述語内で **点ごと等式 `∀x, fXY x = convDensityAdd fX fY x`** に強化 (述語 pivot、Gaussian saturation で点ごと一致 = 非 vacuous)。それでも詰まれば body `sorry` + `@residual(wall:stam-step2-density)` 据置 |
| **L-EPIW-3d-β** | 案 b の述語 hyp 追加で lockstep consumer (6 file) の修正が 1 セッション超 | 部分 pivot は consumer 破壊で commit 不能 ⇒ 該当 declaration を `sorry` 化して type-check done を維持、`@residual(wall:stam-step2-density)`。pivot 自体は 1 commit で完遂が原則 (Phase 3-pre 4 述語 pivot precedent) |
| **L-EPIW-3d-γ** | 14 integrability hyp を述語に上げた結果、独立 honesty audit が「load-bearing 化」を疑う | `convex_fisher_bound` の `@audit:ok` 監査 (「none bundles the inequality core」) を根拠に、上げる hyp は全て可積分性/有界性 precondition である旨を audit brief に明示。core (凸不等式) は `convex_fisher_bound` body 内で genuine に組まれており predicate hyp は供給材料のみ |

> **`@residual` slug 注記**: 本壁の正規 slug は `wall:stam-step2-density` (audit-tags.md register L57 に登録済)。
> コード現状は `@residual(wall:stam-blachman)` (旧 slug、register 未登録) ⇒ Phase 3d touch 時に
> `stam-step2-density` へ incidental 統一 (本 plan の進捗 L31/L612 等で `stam-blachman` 表記が残る箇所も
> 同時是正)。

## Phase 4 — 壁2 (per-time de Bruijn + FTC 積分形) 📋

**Phase 1 GO を前提** (per-time density witness を消費)。`debruijnIdentityV2_holds`
(`FisherInfoV2DeBruijn.lean:245`) + `debruijnIntegrationIdentity_holds` (`:310`) の充足。

### 前提整備 — `_hX/_hZ/_hXZ` signature 復元 (forward-looking note `:234` の option a)

`debruijnIdentityV2_holds` は Phase 2.B で `Measurable X` / `Measurable Z` / `IndepFun X Z P` を
signature から syntactically 削除済 (`:234` forward-looking note 参照)。これらは heat eq IBP の
wall content に **semantic に必要な regularity hyp**。Phase 4 着手時の前提整備として:

- [ ] **option a 採用** (note 推奨、load-bearing bundling 観点): `_hX` / `_hZ` / `_hXZ` を
      underscore-prefixed args として signature に復元 + caller `csiszarGap1Source_hasDerivAt`
      ripple。option b (`IsRegularDeBruijnHypV2` に field bundle) は predicate に regularity を
      抱えさせる方向なので不採用。

### 組み方

1. **per-time 微分形** (`:245`): gateway (Phase 1) を `p_t = p_X ⋆ heatKernel_t` に特殊化した
   density witness で `logDeriv p_t` を Fisher info に紐付け、heat eq `∂_t p_t = (1/2)∂_xx p_t` +
   IBP (`integral_mul_deriv_eq_deriv_mul_of_integrable`、inventory §5) で
   `(d/dt)h = (1/2)·J`。← heat eq IBP が **真壁可能性高** (Mathlib.Analysis.PDE.* 不在)。
2. **FTC 積分形** (`:310`): per-time `HasDerivAt` を FTC で積分。Gaussian テンプレ
   `bounded_T_ftc_gaussian` (`EPIL3Integration.lean:937-985`、`@audit:ok`、同型完全閉) を
   一般 `X` に一般化。per-time (step 1) が建てば ~60-100 行。

### 撤退ライン

| slug | 内容 | 撤退口 |
|---|---|---|
| **L-EPIW-4-α** | heat eq density の IBP (step 1) が Mathlib PDE 不在で self-build PR 級 | `debruijnIdentityV2_holds` body `sorry` + `@residual(wall:debruijn-heat-eq)` 据置 (regularity hyp `_hX/_hZ/_hXZ` 復元済で維持) |
| **L-EPIW-4-β** | FTC 積分形 (step 2) の一般 `X` 積分可能性が Gaussian テンプレ一般化で carry されず | `debruijnIntegrationIdentity_holds` body `sorry` + `@residual(wall:debruijn-integration)` 据置、per-time (step 1) が建てば step 1 のみ genuine ship |

**honesty 規律**: heat eq / IBP を predicate に bundle 禁止。per-time が真壁なら honest sorry 据置。

概算規模: per-time (step 1) 100-200 行 (heat eq IBP self-build、L-EPIW-4-α 発火確率高) +
FTC 積分形 (step 2) 60-100 行 (テンプレ一般化、step 1 後)。proof-log: yes。

## 全 Phase 通じた honesty 規律

- 詰まれば **`sorry` + `@residual(<class>:<slug>)`** で抜く (tier 2、唯一の正規撤退口)。
- **禁止** (tier 5、CLAUDE.md「検証の誠実性」): `*Hypothesis` / `Is...Hyp` predicate に証明の核を
  bundle / `Prop := True` slot / 仮説型≡結論の `:= h` 循環 / 退化定義悪用 (`Y:=0` で trivially 成立)。
- regularity hyp (measurability / independence / `IsProbabilityMeasure` / Gaussian tail dominated)
  は **precondition なので引数保持 OK** (load-bearing ではない)。
- 新規 `sorry` + `@residual` 導入 commit が出たら orchestrator が独立 honesty audit subagent を起動
  (CLAUDE.md「Independent honesty audit」)。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正時。append-only。

1. **2026-05-30 起草 (Wave 1 結論消費)**: proof-pivot-advisor + mathlib-inventory が独立収束した
   4 確定事項を plan に固定。
   - **両壁共通根**: 壁1 (stam-step2-density) / 壁2 (debruijn-integration) は同一 apparatus
     (独立和畳み込み密度の点ごと微分可能性 + score logDeriv 表現) に帰着。
   - **Phase 直列順 (壁1 → 壁2)**: 壁2 の per-time density witness は壁1 apparatus を消費するため
     逆順不可。並列は壁2 空回り。Phase 1 (gateway) が両壁の共通従属点。
   - **gateway atom = 決定的判定**: `convDensity_add_differentiable` が建つか `⋆ₗ` 微分可能性で
     詰まるかが tractable/真壁の go/no-go gate (sub-2 `convDensityAdd_hasDerivAt` が判定の決め手、
     `HasCompactSupport` 不適合を truncation 迂回できるか)。Phase 1 NO-GO なら scope-out 確定。
   - **cross-term false-negative 補正**: 過去 inventory が cross-term orthogonality を `Found 0` で
     壁認定していたのは loogle bare-identifier query の失敗。`condExp_indep_eq`
     (`ConditionalExpectation.lean:42`) + `IndepFun.integral_mul_eq_mul_integral`
     (`Integration.lean:247`) + `integral_logDeriv_density_eq_zero` (`FisherInfoV2.lean:155`) で
     ~20-40 行 self-buildable。Phase 2 として gateway 非依存に分離、同 commit で inventory 訂正。
   - 起草時 verbatim 確認: `stam_step2_density_wall:283` (regularity hyp 保持済) /
     `debruijnIdentityV2_holds:245` (`_hX/_hZ/_hXZ` 削除済 + forward-looking note `:234`) /
     `debruijnIntegrationIdentity_holds:310` (存在形 fPath)。Gaussian テンプレ
     `bounded_T_ftc_gaussian` (`EPIL3Integration.lean:937-985` `@audit:ok`) の存在は Wave 1 結論で
     確認 (Phase 4 step 2 の一般化対象)。

2. **2026-05-30 Phase 3-pre 設計確定 (§A–D 書換、scoping doc 消費)**: `epi-3predicate-pivot-scoping.md`
   の consumer/import グラフ + verbatim 行番号を SoT として Phase 3-pre を実装可能粒度に確定。
   - **3+1 述語**: scoping が `IsStamInequalityHyp` (`EPIStamDischarge.lean:100`) を第 4 ripple と特定。
     これは `IsStamInequalityResidual` と **別 def** (measure-keyed vs density-keyed) だが
     `fisherInfoOfMeasureV2_def` 経由 defeq で 3 `exact` (`EPIStamDischarge.lean:445` /
     `EPIStamToBridge.lean:1119` / `EPIL3Integration.lean:160`) が依存。
   - **decision B**: Residual を軸1 pivot すると defeq が破れるので Hyp も同 `hconv` で lockstep pivot。
     3 site は全 pass-through (construct site 0、scoping §1) → bridge lemma 不要、隠れ construct 出現時のみ
     adapter (L-EPIW-3pre-α)。
   - **軸2 = 抽象 Prop carrier**: `fisherInfoOfMeasureV2_eq_of_pdf_ae_eq` は Mathlib/Common2026 とも不在
     (`rg` exit 1 verbatim 確認) → rewrite 不能、`HasDensityReal` marker (`withDensity` honest body or
     opaque + `@residual(wall:stam-pdf-identification)`) を measure-keyed 2 述語に carry。density-keyed
     Residual/Hyp は軸1 のみ (非対称)。
   - **順序**: Residual+Hyp (step1, 軸1 lockstep) → Optimal+CondExpCSHyp (step2, 軸1+2 lockstep)、各 step
     緑 gate + 1 commit。cycle 無し (EPIConvDensity は FisherInfoV2 のみ依存の葉、scoping §2)。
   - **タグ**: pivot 後 `@audit:defect(false-statement)` → `@residual(wall:stam-blachman)` 格下げ予定
     (反例消失 = 結論 TRUE-in-principle)。書換は実装後の独立 audit が実施。pivot は defect 除去であって
     Blachman 壁 closure (Phase 3) ではない。注入 hyp は regularity precondition、核は `sorry` 据置。

3. **2026-05-30 Phase 3 真壁確定 (proof-pivot-advisor 独立 RO verdict)**: Phase 3 本体着手を見送り、
   `stam_step2_density_wall` の `sorry`+`@residual(wall:stam-blachman)` を honest wall として確定据置
   (L-EPIW-3-α 発火)。
   - **判定**: gateway `convDensityAdd_logDeriv` (`EPIConvDensity.lean:113`) は score の**解析的 (logDeriv)
     表現**まで genuine に到達。だが Stam closure に要るのは score の**確率的 (condExp) 表現**
     `s_Z(z)=E[s_X|X+Y=z]` (Blachman 恒等式)。両者を繋ぐ橋 (同時分布 `ℝ×ℝ` + `X+Y` sub-σ-algebra への
     disintegration + Fubini で積分) は Mathlib にも repo にも hook 皆無 = 約 300 行 multi-file self-build
     = PR 級。「`f(convDensityAdd …)` を `condExp …` に変える bridge を探している」= CLAUDE.md
     「Mathlib-shape-driven」の赤フラグそのもの。
   - **既存 Mathlib lemma 照合**: `condDistrib` (51) / `condExp` (171) / `condVar_ae_le_condExp_sq`
     (条件付き Jensen 実体、`CondVar.lean:127`) / `condExp_ae_eq_integral_condDistrib_id` は**実在**するが、
     `pdf`/`logDeriv`/`fisherInfoOfDensity` に結びつける hook が一切ない (`fisherInfo` loogle unknown
     identifier、`Stam|Blachman|score_conv` rg 0 hit)。gateway があっても disintegration step1 は丸ごと残る。
   - **教訓 (proof-log 候補)**: gateway が score の解析的 (logDeriv) 表現まで建っても、Stam closure に要るのは
     score の確率的 (condExp) 表現であり、両者を繋ぐ Blachman 恒等式が核 — 「score 表現済」と「Blachman
     closure 可能」は別物、**gateway GO は Phase 3 GO を意味しない**。
   - **signature は健全**: predicate は Phase 3-pre pivot 済で sound、`hconv` 制約 + regularity
     precondition のみ、load-bearing 無し。`sorry` は tier-2 = 最も honest なマーカー。closure は後続 PR
     scope に切出し。case D (現状維持) 確定、案 C (bridge 直接 self-build ~300 行) は CLAUDE.md
     「50 行超は定義側を疑え」の遥か上で非推奨。

4. **2026-05-30 Phase 3 「真壁確定」是正 → 密度レベル明示積分経路に格下げ (§Phase 3 全面書換)**:
   判断ログ #3 の「Phase 3 真壁確定 (~300 行 PR 級 unscoped wall)」は **density route 未評価による過大
   判定**だった。独立 proof-pivot-advisor (density pivot 検証) が決定的事実を発見し scoped multi-session
   path に格下げ、§Phase 3 を explicit density route で全面書換。
   - **collapse の根拠 (verbatim)**: `fisherInfoOfMeasureV2 _μ f = fisherInfoOfDensity f`
     (`FisherInfoV2DeBruijn.lean:86-87`, `fisherInfoOfMeasureV2_def`, `rfl`、measure 引数を無視) により
     `stam_step2_density_wall:376` の goal は**純粋に密度上の解析命題** `(fisherInfoOfDensity fXY).toReal
     ≤ J_X·J_Y/(J_X+J_Y)` (with `fXY =ᵐ convDensityAdd fX fY`, `IsRegularDensityV2 fX/fY`, `∫fX=∫fY=1`)
     に collapse する。**抽象 condExp/condDistrib/disintegration は一切不要**。判断ログ #3 の「~300 行 PR 級」
     は**抽象 condExp 経路限定**で、密度レベル明示経路はそれを概念ごと回避する。
   - **採用戦略 = 密度レベル明示積分経路 (condExp 不使用)**: 条件付き Cauchy-Schwarz を**確率重み
     `p_{X|Z}(x|z) := fX(x)fY(z-x)/p_Z(z)` 上の点ごと明示積分** `s_Z(z) = ∫ x, W_λ(x,z)·p_{X|Z}(x|z) dx`
     として書き下す (§Approach step 1-6)。`epi-blachman-density-route-inventory.md` の S1 disintegration /
     S3 `ConvexOn.map_condExp_le` / S4 `integral_condExp` は**旧 condExp 経路の残骸**で本経路とずれており
     採らない。inventory からは **API 部品 (積分 CS `integral_mul_le_Lp_mul_Lq_of_nonneg` / Tonelli
     `lintegral_lintegral_swap` / IBP `integral_mul_deriv_eq_deriv_mul_of_integrable` / λ最適化
     `stam_lambda_min`) のみ消費**。
   - **atom 分解 (案 E pivot + 案 G staged shared sorry 補題)**: Phase 3a (GATE、gateway 7 hyp 充足検証
     + S2 対称導関数恒等式) → 3b (S3 score 表現 + S4 点ごと CS) → 3c (S4 Tonelli + 3 項 + lintegral↔Bochner
     橋) → 3d (assemble)。各 atom shared sorry 補題化、未完は `sorry`+`@residual(wall:stam-blachman)` で
     type-check done commit、proof done は全 atom 完成時。
   - **支配項 (advisor)**: atom B (Phase 3a) の gateway hyp `h_bound` (Gaussian-tail dominated) 充足 +
     atom C (Phase 3c) の Tonelli 可積分性副条件が hard part。`h_bound` が PR 級なら L-EPIW-3-α 発火 =
     honest sorry 据置継続 (この場合のみ撤退)。
   - **L-EPIW-3-密度-α の是正**: inventory が flag した「score 可積分性が `IsStamCauchySchwarzOptimal`
     signature に漏れる」懸念は **condExp 経路前提**で、本経路は condExp を使わないため
     `StandardBorelSpace`/`condExp_ae_eq_integral_condDistrib_id` の signature 漏れは発生しない。
   - **起草時 verbatim 確認**: `fisherInfoOfMeasureV2_def` (`FisherInfoV2DeBruijn.lean:86-87`, `rfl`) /
     `stam_step2_density_wall` (`EPIStamInequalityBody.lean:376`) / gateway 7 hyp
     (`convDensityAdd_hasDerivAt` `EPIConvDensity.lean:86-97`) / `convDensityAddDeriv` (`:64`) /
     S2 IBP (`IntegralEqImproper.lean:1318`) / 積分 CS (`Bochner/Basic.lean:1237`) / Tonelli
     (`Measure/Prod.lean:1058` / `Integral/Prod.lean:532`) / cross=0
     (`integral_logDeriv_density_eq_zero` `FisherInfoV2.lean:158`, `score_cross_term_eq_zero`
     `EPIScoreCrossTermOrth.lean:45`) / λ最適化 (`stam_lambda_min` `:204` / `stam_lambda_lower_bound` `:216`)
     を Read で照合済。

5. **2026-05-30 Phase 3c-fin 完済 (`convex_fisher_bound` genuine)**: 残 sorry (Tonelli order-swap 3 件
   + 3 項評価 + cross=0) を `convex_fisher_term1/2/cross` 補助補題で genuine closure。`convex_fisher_bound`
   (`EPIBlachmanDensity.lean:538`) は 23 引数 (regularity + 有界性 + 14 integrability + `hpZ`) で結論
   `(fisherInfoOfDensity (convDensityAdd fX fY)).toReal ≤ lam²·(fisherInfoOfDensity fX).toReal +
   (1-lam)²·(fisherInfoOfDensity fY).toReal`、0-sorry/sorryAx-free/独立監査 `@audit:ok`。**density route の
   解析核は完全に完成** — 当初「Blachman = PR 級真壁」診断を density route が概念ごと解体した最終証跡。残るは
   Phase 3d の precondition 整合のみ。

6. **2026-05-30 Phase 3d precondition gap 決定 (L-EPIW-3-密度-β 解消、§Phase 3d 追加)**: planner 決定として
   **案 b (lockstep 述語に boundedness/integrability hyp 追加) + 案 b' (`IsStamCondExpCSHyp` 経由 assemble)**
   を採用。
   - **案 c 排除 (verbatim 確認)**: predicate `IsStamCauchySchwarzOptimal` (`:278`) / `IsStamCondExpCSHyp`
     (`:210`) は **任意の** regular density `fX fY` を量化する (`∀ fX fY, … → IsRegularDensityV2 fX → …`)。
     よって「`deriv f` 有界」を `stam_step2_density_wall` の追加 theorem 仮説として thread する案 c は **false
     仮定** (有界でない deriv を持つ regular density が反例) ⇒ honesty defect、不可。不足 regularity は
     predicate 内 (案 b) か structure 内 (案 a) のみ置ける。
   - **案 a vs 案 b 実測**: `IsRegularDensityV2` **構築サイト 0 件** (`rg` 全件 hypothesis、anonymous ctor /
     `.mk` / 生成補題ゼロ)、Gaussian instance **未 wire**、field projection 消費 12 件 (非破壊)。案 a は
     ripple 実質ゼロだが (i) structure 定義の意味を肥大させ非 Stam consumer (FisherInfoV2 closed-form) に
     無関係 field を背負わせる、(ii) Gaussian instance 未 wire で非 vacuousness 検証点を増やす。**案 b** は
     影響を EPI Stam チェーン局所に閉じ、Phase 3-pre 4 述語 pivot と同型操作 (既に成功済)、「使う場所に
     precondition を置く」原則と整合 ⇒ 採用。
   - **案 b' assemble route 発見**: `convex_fisher_bound` の結論 (`J_sum ≤ λ²J_X+(1-λ)²J_Y`) が既存 sibling
     述語 `IsStamCondExpCSHyp` (`Step12Body:210`, ∀λ 形) の body と **完全一致**、かつ
     `stamCauchySchwarzOptimal_of_condExpCSHyp` (`:282`, `@audit:ok`) が `IsStamCondExpCSHyp →
     IsStamCauchySchwarzOptimal` を `stam_lambda_min` 経由で既に橋渡し済。⇒ `stam_step2_density_wall` body は
     ∀λ 形 `IsStamCondExpCSHyp` を建てるだけでよく、λ 最適化 (旧 brief step 8) は既存橋に委譲 = genuine 化の
     表面積が縮小。
   - **新規 atom**: atom Cong (`fisherInfoOfDensity` ae-congr、`lintegral_congr_ae` + deriv ae 持ち上げ —
     deriv ae が核、撤退口 = hconv を点ごと等式に強化) / atom Pos (`convDensityAdd > 0`、
     `integral_pos_of_integrable_nonneg_nonzero` loogle 確認) / atom Bdd-f (任意、連続+tail から `f` 有界)。
     全て Mathlib API 当て先予測は **verbatim 前提**。
   - **closure 条件 (非 vacuousness)**: 案 b の述語 hyp 群は load-bearing でない regularity precondition だが、
     非 vacuousness の最終確証は **Gaussian instance (`isStamCondExpCSHyp_of_gaussian` 相当) が新
     boundedness/integrability hyp + 既存 `IsRegularDensityV2` を全 discharge する補題**に依存。これは
     Phase 3d の `sorry` 解消とは別の下流 task。Gaussian instance 未完の間は独立 honesty audit に
     vacuousness 懸念を明示すること。
   - **slug 統一**: 本壁の正規 slug = `wall:stam-step2-density` (audit-tags.md register 登録済)。コード現状
     `@residual(wall:stam-blachman)` (register 未登録) ⇒ Phase 3d touch 時に統一是正。
