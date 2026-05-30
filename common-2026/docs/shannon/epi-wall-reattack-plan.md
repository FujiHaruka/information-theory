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
- [ ] Phase 3 — 壁1 本体 (条件付き Blachman → convex Fisher bound) 📋 ← **次の一手** (着手前に proof-pivot-advisor で tractability 判定推奨)
- [ ] Phase 4 — 壁2 (per-time de Bruijn + FTC 積分形) 📋

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
   │ 壁1 (Phase 3)            │                   │ 壁2 (Phase 4)                │
   │ 条件付き Blachman        │                   │ per-time de Bruijn           │
   │   s_Z = E[s_X|X+Y=z]     │                   │   (d/dt)h = (1/2)J            │
   │ + ConvexOn.map_condExp_le│                   │   ← heat eq IBP (真壁可能性高)│
   │ + integral_condExp       │                   │ + FTC 積分形                 │
   │ + cross-term (Phase 2)   │ ◀── 直列依存 ──   │   ← bounded_T_ftc_gaussian   │
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

- 壁1 (Phase 3) = gateway の `logDeriv p_Z` 表現 + Phase 2 の cross-term + Mathlib 既存
  `ConvexOn.map_condExp_le` (条件付き Jensen) + `integral_condExp` (total expectation)。
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

## Phase 3 — 壁1 本体 (条件付き Blachman → convex Fisher bound) 📋

**Phase 1 GO + Phase 2 Done を前提**。`stam_step2_density_wall` (`EPIStamInequalityBody.lean:283`)
の `sorry` body を充足。

### 組み方

1. gateway (Phase 1) の `logDeriv (convDensityAdd pX pY)` 表現から条件付き score 表現
   `s_Z(z) = E[s_X(X) | X+Y=z]` (Blachman 恒等式) を導く。← ここが genuine に不在の核
   (`condExp ∧ IndepFun` 同時補題 = loogle Found 0)、disintegration 経由の self-build。
2. `ConvexOn.map_condExp_le` (条件付き Jensen、Mathlib 既存) で
   `s_Z(z)² ≤ E[(λ s_X + (1-λ) s_Y)² | X+Y=z]`。
3. `integral_condExp` (total expectation、Mathlib 既存) + Phase 2 cross-term で積分して
   `J(Z) ≤ λ²·J(X) + (1-λ)²·J(Y)`。
4. λ 最適化 (`λ = J(Y)/(J(X)+J(Y))`) で `J(Z) ≤ J(X)·J(Y)/(J(X)+J(Y))` =
   `IsStamCauchySchwarzOptimal` の結論。

### 撤退ライン

| slug | 内容 | 撤退口 |
|---|---|---|
| **L-EPIW-3-α** | Blachman 条件付き score 表現 (step 1) の disintegration self-build が PR 級 | `stam_step2_density_wall` body `sorry` + `@residual(wall:stam-blachman)` 据置 (regularity hyp は維持、honesty defect 化させない) |
| **L-EPIW-3-β** | λ 最適化の algebraic transform が `linarith` 吸収不可で >50 行 | step 4 のみ `sorry` + `@residual(plan:epi-wall-reattack-plan)`、step 1-3 は genuine 部分 ship |

**honesty 規律**: Blachman identity を `Is...Hyp` predicate に bundle して `:= h` 機械展開で
抜くのは禁止 (tier 5 load-bearing)。詰まれば必ず `sorry` + `@residual(wall:stam-blachman)`。

概算規模: 100-250 行 (step 1 Blachman 表現が支配項、L-EPIW-3-α 発火確率高)。proof-log: yes。

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
