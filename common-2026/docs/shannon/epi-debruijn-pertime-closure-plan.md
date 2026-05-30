# EPI per-time de Bruijn identity — closure サブ計画

> **Parent**: [`epi-debruijn-integration-plan.md`](epi-debruijn-integration-plan.md) §Phase B
> (撤退ライン L-EPI2 = de Bruijn integration の genuine discharge、per-time wall は
> その下流の解析核)。grandparent: [`epi-moonshot-plan.md`](epi-moonshot-plan.md)。
> **Inventory**: [`epi-debruijn-pertime-reattack-inventory.md`](epi-debruijn-pertime-reattack-inventory.md)。
> **Wall SoT**: `Common2026/Shannon/FisherInfoV2DeBruijn.lean:245` (`debruijnIdentityV2_holds`)。

<!--
記法は subplan-template と同じ (状態絵文字 📋🚧✅🔄 / 取り消し線 / 判断ログ append-only)。
plan filename stem = `epi-debruijn-pertime-closure` → 再分類後の `@residual(plan:epi-debruijn-pertime-closure)` slug と一致。
-->

## 進捗

- [ ] Phase 0 — signature pivot (false→true、最小先行 closure) 📋
- [ ] Phase 1 — density 同定 (`pPath_eq_convDensityAdd`) 📋 → [inventory §8 優先1](epi-debruijn-pertime-reattack-inventory.md)
- [ ] Phase 2 — heat equation per-density (`∂_s pPath`) 📋 → [inventory §8 優先2 / §3 軸2]
- [ ] Phase 3 — entropy parametric diff (`(d/ds)∫negMulLog`) 📋 → [inventory §8 優先3 / §2 軸1]
- [ ] Phase 4 — 無限区間 IBP (logDeriv→Fisher) 📋 → [inventory §8 優先4-5 / §4 軸3]
- [ ] Phase 5 — capstone congr + `@audit:ok` 移行 📋

## ゴール / Approach

**ゴール**: EPI moonshot の唯一の残壁 `debruijnIdentityV2_holds`
(`Common2026/Shannon/FisherInfoV2DeBruijn.lean:245`、現 `@residual(wall:debruijn-integration)`) を
一般 `X` で genuine 化し、`@audit:ok` に到達する (Gaussian case は `deBruijn_identity_v2_gaussian`
で既に genuine)。

### 背景 — 壁の現状と Wave 1 結論

- **現 signature は FALSE statement** (Wave 1 proof-pivot-advisor が反例確定)。
  `IsRegularDeBruijnHypV2` (`:200`) は 2 field (`Z_law` + `density_t : ℝ → ℝ` **unpinned**)。
  結論 RHS が `(1/2) * fisherInfoOfDensityReal h_reg.density_t` で `density_t` 任意なので、
  `density_t := 0` で RHS=0 だが真値 `1/(2(v+t)) ≠ 0` (Gaussian) → `HasDerivAt` 一意性に矛盾。
  judgment #17 の Stam 述語と同型 false-statement defect。現状 `@residual(wall:debruijn-integration)`
  は「証明不能な false statement の隠れ蓑」(tier 5 寄り、`sorry` で型は通るが真には埋まらない)。
- **解析核は真壁ではない** (inventory §0/§12)。5 軸中 4 軸が Mathlib/repo 完備
  (parametric diff 軸1 / 無限区間 IBP 軸3 / rnDeriv↔withDensity 軸4 / convolution density 軸5
  = `EPIConvDensity.lean` の `@audit:ok` sorryAx-free 資産)。唯一の真の不在は Gaussian
  heat semigroup closed-form (`"heat"`/`"Mehler"`/`"OrnsteinUhlenbeck"`/`"FokkerPlanck"`
  すべて `Found 0`) だが density-route で迂回可。**自作見積 ~250 行** (最大コスト = heat eq
  per-density ~80-120 行)。
- **再分類提案**: 壁は「hard absence」ではなく「big plumbing」。Phase 0 で signature を
  true 化した後は `@residual(wall:debruijn-integration)` → `@residual(plan:epi-debruijn-pertime-closure)`
  への書換が妥当 (auditor 判断事項、本 plan は所見提示。最終書換は Phase 0 の honesty 監査で確定)。

### Approach (解の全体形)

2 段構え。**まず Phase 0 で false→true な signature pivot を先行する。** これは honesty 上
必須 — 現 signature は density witness が unpinned ゆえ反例を持つ偽命題で、`sorry` がどれだけ
残っていても「埋まりえない」。`IsRegularDeBruijnHypV2` に `density_t` を当該 pushforward の
実 density に pin する field を 1 本足せば命題は真になり、以降の解析核 (Phase 1+) が初めて
「埋まりうる sorry」になる。pin field は density witness を「証明の核心」化せず**前提条件
(regularity)** として持たせる — `density_t = (rnDeriv).toReal` という外形等式は core
(`HasDerivAt`) を bundle しないため load-bearing ではない。同時に Phase 2.B 段 1 の
forward-looking 負債 (`Measurable X`/`Measurable Z`/`IndepFun X Z P` 削除済) も復元する。

**Phase 1+ は density-route 経由の解析核** を atom 分解で積む: pushforward density =
`convDensityAdd p_X (Gaussian density at √s)` の同定 → 時刻微分 `∂_s pPath` の heat equation
検証 (`convDensityAdd` 枠の s-転用 + Gaussian factor chain rule) → entropy 積分の parametric
diff (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) → 無限区間 IBP
(`integral_mul_deriv_eq_deriv_mul_of_integrable`) で logDeriv→Fisher → 最終 congr。各 atom
は inventory verbatim の Mathlib/repo lemma に plumbing。多セッション scope。

**なぜ pivot 先行か**: (a) honesty — false statement の隠れ蓑を解消し、`sorry` が tier 2
(埋まりうる honest 残課題) になる。(b) 前提整備 — 解析核 (Phase 1-4) は `density_t` が実 density
であることを前提に書ける (pin が無いと各 atom が「どの密度か」を毎回再特定する必要がある)。

---

## Phase 0 — signature pivot (false→true、最小先行 closure) 📋

> **完了基準**: type-check done (`sorry` 据置だが命題が true statement に)。**独立 honesty
> 監査対象** (signature 改変 + false→true 化 = 起動条件「signature 変更で honesty 意味が変わる」)。
> proof done は Phase 5 まで持ち越し。

### 0-a. `IsRegularDeBruijnHypV2` に density-pin field 追加

`FisherInfoV2DeBruijn.lean:200-207` の structure に 1 field 追加:

```lean
structure IsRegularDeBruijnHypV2 ... (t : ℝ) where
  Z_law : P.map Z = gaussianReal 0 1
  density_t : ℝ → ℝ
  -- NEW: density witness を当該時刻 t の pushforward 実 density に pin する。
  density_t_eq : ∀ x,
    density_t x = ((P.map (gaussianConvolution X Z t)).rnDeriv volume x).toReal
```

- これにより `density_t := 0` 反例が排除され (`rnDeriv` 実値 ≠ 0)、命題が true 化。
- **load-bearing でない根拠** (監査向け): pin は density witness の**外形等式** (`= rnDeriv.toReal`)
  であり、`HasDerivAt`/Fisher info の core は bundle しない。`Z_law` と同じ regularity
  precondition の系列。CLAUDE.md「load-bearing hypothesis bundling」判定軸「前提条件 (regularity)
  か証明の核心 (load-bearing) か」→ 前者。
- **数値 verbatim 確認済**: 下流 `EPIStamDischarge.lean:271 density_t_eq`
  (`(reg_at t ht).density_t = density_path t`) と `IsDeBruijnPathRegular.reg_t`
  (`FisherInfoV2DeBruijn.lean:343-344`、`h_reg.density_t = fPath t`) は既に「density_t を外部
  witness に pin」する形を持つ。本 field はそれを「実 density」に固定する内側 pin で、設計と整合。

### 0-b. `Measurable`/`IndepFun` の forward-looking 負債復元

`debruijnIdentityV2_holds` (`:245`) の wall content (heat eq + IBP on density of
`P.map (X + √t Z)`) に semantic 必要な regularity hyp を復元 (`:232-242` の forward-looking
note 参照)。**案 (a) underscore-prefixed args 推奨** (CLAUDE.md load-bearing 観点、note も (a)
推奨):

```lean
theorem debruijnIdentityV2_holds
    {Ω : Type*} {_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X Z : Ω → ℝ)
    (_hX : Measurable X) (_hZ : Measurable Z) (_hXZ : IndepFun X Z P)  -- NEW (案 a)
    {t : ℝ} (_ht : 0 < t)
    (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t) t := by
  sorry  -- @residual(plan:epi-debruijn-pertime-closure) ← Phase 0 で wall→plan 再分類
```

- 案 (b) (`IsRegularDeBruijnHypV2` に `meas_X`/`meas_Z`/`indep_XZ` field bundle) は不採用 —
  structure consumer の ripple が広く、underscore-prefix の方が局所的。

### 0-c. 下流 ripple file (各 file の touch 内容)

| file:line | declaration | touch 内容 |
|---|---|---|
| `FisherInfoV2DeBruijn.lean:200` | `IsRegularDeBruijnHypV2` | field `density_t_eq` 追加 (0-a) |
| `FisherInfoV2DeBruijn.lean:245` | `debruijnIdentityV2_holds` | `_hX/_hZ/_hXZ` args 追加 (0-b)、`@residual` を `wall:` → `plan:epi-debruijn-pertime-closure` 書換、docstring forward-looking note を「復元済」に更新 |
| `FisherInfoV2DeBruijn.lean:272` | `deBruijn_identity_v2` | pass-through。`_hX/_hZ/_hXZ` を引数に追加して `debruijnIdentityV2_holds X Z _hX _hZ _hXZ ht h_reg` に追従 (signature 追従のみ) |
| `FisherInfoV2DeBruijn.lean:343` | `IsDeBruijnPathRegular.reg_t` | `reg_t` が `∃ h_reg, h_reg.density_t = fPath t` を返す → 新 field `density_t_eq` を満たす witness 構成が必要。`fPath t` を実 density に取れば自動充足、または `reg_t` の existential 内で `density_t_eq` を提供 |
| `FisherInfoV2DeBruijn.lean:377` | `debruijnIntegrationIdentity_holds` | pass-through (`:400` で `debruijnIdentityV2_holds X Z ht h_reg` call)。`_hX/_hZ/_hXZ` を `h_path` 経由 or 引数追加で thread。signature 追従のみ |
| `EPIL3Integration.lean:686-694` | `...gaussian` 系 constructor | structure literal `{ Z_law := ...; density_t := gaussianPDFReal ... }` に `density_t_eq` field 追加。Gaussian case は `density_t = gaussianPDFReal m (v+t)` が実 density に一致する補題で充足 (`gaussianConvolution_law` + Gaussian PDF = rnDeriv)。`_hX/_hZ/_hXZ` は当 constructor が既に受けている (`:680-681`) ので thread 可 |
| `EPIStamDischarge.lean:260-272` | `reg_at` / `density_t_eq` (top-level) | top-level `density_t_eq` (`:271`) は既に `(reg_at t ht).density_t = density_path t` 形。新 structure field `density_t_eq` と整合確認 (二重 pin にならないよう、`reg_at` が返す V2 hyp の内側 pin と top-level pin の関係を docstring 更新)。signature 追従中心 |

> ripple 全 file で `lake env lean <file>` 0 errors (type-check done) を確認。Gaussian
> constructor (`EPIL3Integration.lean:692`) の `density_t_eq` 充足が新規 `sorry` を生むなら
> それも `@residual(plan:epi-debruijn-pertime-closure)` でマーク (Gaussian density = rnDeriv
> 同定は Phase 1 の density 同定の Gaussian 特殊形)。

---

## Phase 1 — density 同定 `pPath_eq_convDensityAdd` 📋

> inventory §8 優先1 (~40-60 行)。新 file `FisherInfoV2DeBruijnPerTime.lean` (inventory §11
> skeleton) に着手。

- `P.map (gaussianConvolution X Z s)` の density が `convDensityAdd p_X (gaussian density √s)`
  に一致することを示す。
- 使用 Mathlib/repo lemma (inventory verbatim):
  - `MeasureTheory.map_eq_withDensity_pdf` (`Mathlib/Probability/Density.lean`、軸4)
  - `MeasureTheory.Measure.rnDeriv_withDensity` (`.../Lebesgue.lean`、結論 `=ᵐ[volume]`、軸4)
  - `Common2026.Shannon.convDensityAdd` (`EPIConvDensity.lean:40`、Bochner ∫ 形、軸5)
- 落とし穴 (inventory §5/§7): 独立和の密度 = 畳み込みの Mathlib 直結 lemma 不在 →
  `convDensityAdd` (Bochner ∫) との shape 整合を repo 側で立てる。`rnDeriv_withDensity` は
  ae 等式 → pointwise が要る箇所は `HasDerivAt.congr_of_eventuallyEq` 経由。
- **撤退ライン L-PT-β** (許容、inventory §10): repo bridge が ~60 行超 → density 同定を別
  lemma に切出し独立 `@residual(plan:epi-debruijn-pertime-closure)` 化 (本体 wall とは別 atom)。
  honest sorry 据置で type-check done を保つ。

## Phase 2 — heat equation per-density `∂_s pPath` 📋

> inventory §8 優先2 (~80-120 行、**本 plan 最大コスト**)。軸2 (Gaussian heat semigroup)
> Mathlib 全不在 → density-route 自作で迂回。

- `∂_s pPath s x = (1/2) ∂²_x pPath s x` (heat equation per-density) を density-route で。
- 軸2 closed-form 不在 (`"heat"` Found 0) のため、Gaussian factor `pY = gaussianPDFReal 0 ⟨s,_⟩`
  の `s`-依存微分を chain rule + `convDensityAddDeriv` (`EPIConvDensity.lean:64`) で自作。
- 使用: `Real.deriv_negMulLog`/`Real.deriv2_negMulLog`
  (`.../Log/NegMulLog.lean`、軸2 補)、`convDensityAdd_hasDerivAt` (`EPIConvDensity.lean:86`、
  `@audit:ok` sorryAx-free、ただし**z (空間) 微分専用** — s-微分への転用が本 Phase の核)。
- 落とし穴 (inventory §5/§7): `convDensityAdd_hasDerivAt` は z-微分。s-微分へ転用時 Gaussian
  factor の s-依存性を別 chain rule で剥がす (軸2 不在部接続)。
- **撤退ライン L-PT-α** (許容、inventory §10): `convDensityAdd` 経由でも ~120 行超で当該
  session で書けない → per-time wall を **Gaussian case genuine (既存) + 一般 `X` は
  `sorry + @residual(plan:epi-debruijn-pertime-closure)` 維持**。**禁止**: `IsRegularDeBruijnHypV2`
  に density witness の regularity field を bundle して `sorry` を消す (load-bearing 化リスク、
  `density_t` を「証明の核心」化しない — Phase 0 の pin は外形等式に留め core を bundle しない)。

## Phase 3 — entropy parametric diff `(d/ds)∫negMulLog(pPath)` 📋

> inventory §8 優先3 (~30-50 行)。軸1 完備。

- `entropy = ∫ x, negMulLog (pPath s x) ∂volume` (`differentialEntropy_eq_integral_density`
  `DifferentialEntropy.lean:65`、軸4) に書下し、`s`-微分を parametric integral diff で。
- 核 lemma (inventory §2 verbatim): `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  (`Mathlib/Analysis/Calculus/ParametricIntegral.lean:289`)。
  型クラス `[RCLike 𝕜]` → `𝕜 := ℝ`、`E := ℝ`、`H := ℝ` 明示。
  結論: `Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀`。
- 落とし穴 (inventory §2/§7): `bound : ℝ → ℝ` の `Integrable bound μ` (Gaussian-tail
  dominating function) は **load-bearing でない regularity precondition**。Phase 0 で復元した
  `_hX/_hZ/_hXZ` から供給。`h_diff` は per-`x` 被積分関数の微分を量化 — 積分そのものの微分を
  仮定しない (load-bearing bundling 回避)。`differentialEntropy_eq_integral_density` は
  `hf_nn : ∀ x, 0 ≤ f x` 必須、`μ ≪ volume` 暗黙要求 (`_ht : 0 < t` が Gaussian smoothing
  で AC 保証)。
- **撤退ライン L-PT-γ** (許容、新規): dominating function 構成 (Gaussian-tail bound の
  `Integrable`) が Mathlib 不在で PR 級と判明 → bound 補題を別 `@residual` 化、honest sorry
  据置で type-check done。

## Phase 4 — 無限区間 IBP (logDeriv→Fisher) 📋

> inventory §8 優先4-5 (~30-50 + ~20-30 行)。軸3 完備 (**新規発見**: 無限区間 IBP は PRESENT、
> 旧 inventory「bounded only」は誤り)。

- de Bruijn 計算 `∫ negMulLog'(p)·∂_s p →IBP→ -(1/2)∫ (∂_x p)²/p` を無限区間 IBP で。
- 核 lemma (inventory §4 verbatim): `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`
  (`Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1318`、境界項消去版、`A := ℝ` で
  `[NormedRing ℝ][NormedAlgebra ℝ ℝ][CompleteSpace ℝ]` 自動)。結論:
  `∫ x, u x * v' x = - ∫ x, u' x * v x`。境界項残す場合は `:1307` `..._eq_deriv_mul`
  (`= b' - a' - ∫ u' v`)。
- 続いて `∫ (logDeriv p)²·p = fisherInfoOfDensity p .toReal` shape congr:
  `convDensityAdd_logDeriv` (`EPIConvDensity.lean:113`、`@audit:ok`) + `fisherInfoOfDensity`
  unfold (`FisherInfoV2.lean:89/103`)。
- 落とし穴 (inventory §4/§7): `hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x` は **support
  全域** の `HasDerivAt` → density `p` の global `C¹` regularity 要 (zero set / 非可微点で
  破綻しうる)。境界項 `Tendsto (u*v) atBot/atTop (𝓝 0)` は Gaussian-tail decay 前提、一般 `X`
  は別証明。`u*v` は `Pi.mul` (pointwise)。
- **撤退ライン L-PT-δ** (許容、新規): `tsupport` 全域 `HasDerivAt` (global `C¹`) または
  tail decay の一般 `X` 証明が ~50 行超 → 当該 sub-step を別 `@residual` 化、honest sorry 据置。

## Phase 5 — capstone congr + `@audit:ok` 移行 📋

> proof done 到達点。

- Phase 1-4 の atom を assemble し RHS を `(1/2) * fisherInfoOfDensityReal h_reg.density_t`
  に一致させる最終 congr (inventory §1 段7、`.toReal` / `logDeriv` vs `(∂_x p)/p` 同定)。
- `debruijnIdentityV2_holds` の body から `sorry` 除去 → 0 sorry / 0 @residual。
- `#print axioms debruijnIdentityV2_holds` で `sorryAx` 非依存確認 →
  `@residual(plan:epi-debruijn-pertime-closure)` を `@audit:ok` に書換。
- **独立 honesty 監査** 必須 (新規 genuine 化 = 起動条件)。
- 下流 `debruijnIntegrationIdentity_holds` (`:377`) は transitive 依存のみ → 本壁 closure で
  自動 genuine 化 (consumer 側 `@residual` 不要、type-check 経由 transitive 追跡)。EPI moonshot
  唯一の残壁が閉じる。

---

## 撤退ライン (L-* マーカー集約)

各 Phase の honest 撤退口。すべて **sorry + `@residual`** 維持 / 仮説束化禁止。

| マーカー | Phase | 発動条件 | 撤退後の状態 |
|---|---|---|---|
| **L-PT-β** | 1 | density 同定 repo bridge ~60 行超 | 別 lemma 切出し独立 `@residual(plan:epi-debruijn-pertime-closure)`、type-check done 維持 |
| **L-PT-α** | 2 | heat eq per-density ~120 行超で session 内不可 | Gaussian case genuine (既存) + 一般 `X` は `sorry + @residual` 維持。**禁止**: density regularity field を bundle して sorry 消去 |
| **L-PT-γ** | 3 | Gaussian-tail dominating function `Integrable` が PR 級 | bound 補題を別 `@residual` 化、honest sorry 据置 |
| **L-PT-δ** | 4 | `tsupport` 全域 `HasDerivAt` / tail decay の一般 `X` 証明 ~50 行超 | 当該 sub-step 別 `@residual` 化、honest sorry 据置 |

**全 Phase 共通の禁止事項**: `IsRegularDeBruijnHypV2` に `HasDerivAt`/Fisher core を bundle
する撤退 (load-bearing、`density_t` を証明の核心化)、`:True` slot、循環 `:= h`、退化定義悪用。
詰まったら必ず `sorry` + `@residual(plan:epi-debruijn-pertime-closure)` (tier 2) で抜く。

> inventory §10 の所見: 既存撤退ライン (L-EPI2 / L-FV2DB-C) は **発動しない** — むしろ
> 「Mathlib 不在」根拠を縮小する所見 (無限区間 IBP PRESENT 発見)。L-FV2DB-C
> (`FisherInfoV2DeBruijnBody.lean:63`) の「IBP の bounded/unbounded 形が無い」根拠は部分的に
> 誤りで、記述更新を推奨 (本 plan の Phase 4 で実証)。

## 検証

| Phase | 完了基準 | 独立監査要否 |
|---|---|---|
| 0 | type-check done (全 ripple file `lake env lean` 0 errors)、命題 false→true | **要** (signature 改変 + false→true + wall→plan 再分類、起動条件該当) |
| 1-4 | type-check done (各 atom)。`sorry` 残置は `@residual(plan:epi-debruijn-pertime-closure)` タグ付き | 新規 shared sorry 補題追加時のみ要 |
| 5 | proof done (`debruijnIdentityV2_holds` 0 sorry / 0 @residual、`#print axioms` で sorryAx 非依存) | **要** (新規 genuine 化、`@audit:ok` 付与判定) |

- inner loop は `lake env lean Common2026/Shannon/FisherInfoV2DeBruijnPerTime.lean`
  (新 file) + ripple file 個別。`lake build` は使わない (CLAUDE.md「Verification」)。
- Phase 0 で structure field 追加 → 下流 olean refresh が必要なら
  `lake build Common2026.Shannon.FisherInfoV2DeBruijn` 1 回。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **Phase 0 先行 + wall→plan 再分類の根拠** (起草時, 2026-05-31): Wave 1 独立再評価で現
   `debruijnIdentityV2_holds` signature が FALSE statement (density_t unpinned 反例
   `density_t := 0`) と確定。`@residual(wall:debruijn-integration)` は false statement の隠れ蓑
   (tier 5 寄り) なので、解析核 (Phase 1+) より先に signature pivot を Phase 0 として独立工程化。
   inventory §0/§12 の「hard absence ではなく big plumbing」所見に従い、Phase 0 完了時に
   `wall:` → `plan:epi-debruijn-pertime-closure` へ再分類 (最終確定は Phase 0 独立監査)。
2. **density-pin は外形等式に留める** (起草時): Phase 0-a の `density_t_eq` は
   `density_t x = (rnDeriv).toReal` の外形等式とし、`HasDerivAt`/Fisher core は bundle しない
   (load-bearing 回避)。CLAUDE.md「load-bearing hypothesis bundling」判定軸で regularity
   precondition 側。下流 `EPIStamDischarge.lean:271` / `IsDeBruijnPathRegular.reg_t:343` が
   既に「density_t を外部 witness に pin」する設計を持つため ripple 整合 (verbatim 確認済)。
3. **`Measurable`/`IndepFun` は案 (a) underscore-prefixed args** (起草時): Phase 2.B 段 1
   forward-looking note (`FisherInfoV2DeBruijn.lean:232-242`) の (a)/(b) 二案のうち (a) 採用。
   structure field bundle (b) は consumer ripple が広い。Phase 0-b で復元、Phase 3 の
   dominating function 供給に使用。
