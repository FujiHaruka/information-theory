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

- [x] Phase 0 — signature pivot (false→true、最小先行 closure) ✅ (commit `138bc49`/`42f8a85`、独立監査 honest 確認、wall→plan 再分類確定)
- [x] Phase 1 — density 同定 ✅: **1a `gaussianConvolution_law_conv` genuine ✅** (`@audit:ok`)。**1b `pPath_eq_convDensityAdd` + bridge genuine ✅** (Wave3、commit `6f675ca`、`@audit:ok`、sorryAx 非依存。`Measurable pX` regularity hyp 追加で可測性 gap、`Integrable pX` 導出 + `gaussianPDFReal_le_prefactor` 上界で可積分性 gap を closure。両 narrow sorry 解消)
- [x] Phase 2 — heat equation per-density ✅: kernel 群 7 件 + **main body `heatFlow_density_heat_equation` genuine closure ✅** (Wave6、commit `68f80e2`、`@audit:ok`、sorryAx 非依存)。σ-積分記号下微分 + spatial 2nd diff の pathDeriv2 同定を gateway lemma で genuine に lift (σ-近傍 `Set.Ioo (s/2)(2s)` で発散回避)。追加 domination/integrability hyp は全て per-y 被積分関数 regularity (Wave7 監査 core-reconstruction で load-bearing 否定)。3 pin 不変
- [x] Phase 3 — entropy parametric diff ✅: `entropy_hasDerivAt_via_parametric` genuine ✅ (Wave1、`@audit:ok`)
- [x] Phase 4 — 無限区間 IBP ✅: 4a `debruijn_ibp_step` + 4b `fisher_from_logDeriv` genuine ✅ (`@audit:ok`)
- [~] Phase 5 — capstone assembly 🔄 (Wave6-9): **structure 拡張 (`IsRegularDeBruijnHypV2` に pX-witness 4 field) ✅ `@audit:ok`** (Wave6)。**assembly = 新 file `FisherInfoV2DeBruijnAssembly.lean`** (import 循環回避)。`debruijnIdentityV2_holds_assembled` (元 wall と同 signature) を **6 genuine atom 合成で genuine 配線** ✅ (Wave8、7 段全て型整合確認)、`_entropy_eq` (段1-2) genuine `@audit:ok`。**残 2 named gap (honest sorry、`plan:`、load-bearing なし、Wave9 監査確認)**: `_chain` (段2-7 解析核の具体 Gaussian-tail domination/integrability/`tsupport` C¹ 構成 = deferred PR 級) / `_fisher_match` (段1+7 の `logDeriv` a.e. 同定 = density_t を pPath t に pointwise 一致させる representative 設計要)。元 `debruijnIdentityV2_holds` は wall sorry 据置 (assembled 版へのポインタ docstring 追記済)

> **進捗サマリ (2026-05-31 orchestrator session、Wave1-9)**: atom file を 6 並列実装 (worktree) + 独立監査 4 round + 設計 planner 1 で前進。**全 6 atom genuine 化完了 (atom file 0 sorry / 全 `@audit:ok`)** — session 開始の 4 honest sorry を全消化 + Phase 2 main (最大コスト) も closure。structure を pX-witness 拡張、capstone assembly を新 file で **genuine 配線** (6 atom 合成が型整合で成立を実証)。`debruijnIdentityV2_holds_assembled` は **monolithic wall を 6 genuine atom + 2 named plan-closable gap に構造化**。
>
> **残課題 (次 session、proof done まで)**:
> 1. **`_chain` (assembly 段2-7 解析核)**: Phase 3 (entropy parametric diff)・Phase 2 (heat eq)・Phase 4a (IBP)・Phase 4b (fisher) を**具体 instantiation で繋ぐ**ための Gaussian-tail domination/integrability/`tsupport` 全域 C¹ 構成。6 atom は genuine 済なので Mathlib 壁ではなく plumbing (deferred PR 級、~150-300 行)。`Integrable.mul_bdd` + `gaussianPDFReal_le_prefactor` 同型の domination 構成が主コスト。
> 2. **`_fisher_match` (assembly 段1+7)**: `fisherInfoOfDensityReal h_reg.density_t = fisherInfoOfDensityReal (pPath t)` を closure。`density_t =ᵐ pPath t` (a.e.) のみでは `logDeriv` (= `deriv/f`、a.e. 不変でない) が一致しない真の gap → **`density_t_eq` pin を「pPath t の smooth representative」に強化する設計判断** が要る (structure 再設計 or representative 選択)。`_fisher_match` を先に攻めるとこの設計が確定する。
> 3. 両 gap closure → `debruijnIdentityV2_holds_assembled` 0 sorry → `#print axioms` sorryAx 非依存 → 独立監査 → `@audit:ok` で **EPI moonshot (Ch.17 一般 EPI) の per-time 壁が proof done**。

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
- 下流 `debruijnIntegrationIdentity_holds` (`:419`) は transitive 依存のみ → 本壁 closure で
  自動 genuine 化 (consumer 側 `@residual` 不要、type-check 経由 transitive 追跡)。EPI moonshot
  唯一の残壁が閉じる。

詳細設計は次節「## Phase 5 詳細設計」。

---

## Phase 5 詳細設計 (assembly + Phase 2 main closure に要する structure 拡張)

> 2026-05-31 起草 (lean-planner)。verbatim 確認済 file:
> `FisherInfoV2DeBruijn.lean:200-295/379-393/419-431`、
> `FisherInfoV2DeBruijnPerTime.lean:69-525` (全 atom)、
> `EPIL3Integration.lean:678-706`、`EPIStamDischarge.lean:251-286`、
> `EPIConvDensity.lean:40-158`。

### Approach (Phase 5 の解の全体形)

`debruijnIdentityV2_holds` の body を atom (`pPath_eq_convDensityAdd` →
`entropy_hasDerivAt_via_parametric` → `heatFlow_density_heat_equation` →
`debruijn_ibp_step` → `fisher_from_logDeriv`) の合成として組む。assembly の障害は
**「atom が要求する witness/regularity hyp を `IsRegularDeBruijnHypV2` が供給できない」**
こと。現 structure は時刻 `t` の密度 witness `density_t : ℝ → ℝ` (+ pin `density_t_eq`) しか
持たず、Phase 1b `pPath_eq_convDensityAdd` が要求する **X 自身の Real 密度 witness `pX`** と
**その `withDensity` 法等式 `hpX_law`** を持たない。

解の全体形は **2 軸**:

1. **`IsRegularDeBruijnHypV2` を `pX`-witness 付きに拡張** (§5A)。`density_t` (時刻 t 密度) は
   assembly 後の RHS `fisherInfoOfDensityReal density_t` 用に残し、`pX` (X 密度) を Phase 1b
   入力用に追加する。両者は **Phase 1b の結論 (`density_t =ᵐ convDensityAdd pX g_t`)** で
   橋渡しされる — この橋渡しを新 field `density_t_conv` として持たせ、assembly 段 1 を
   1 行に圧縮する。
2. **Phase 2 main `heatFlow_density_heat_equation` に domination/integrability regularity hyp を
   追加** (§5B)。現 body sorry が隠している 2 つの「∫ 越し微分」step (σ方向 + spatial 2nd diff)
   を genuine に閉じるための被積分関数レベル domination を、Phase 3 の `bound`/`hbound_int`/`hb`/
   `hdiff` と同型で main signature に出す。これらは拡張 structure の `pX` から供給する。

両軸とも **honesty 制約**: 追加 field / hyp は **regularity / definitional pin であって
load-bearing でない** (X が密度 `pX` を持つ + その外形等式、被積分関数の微分・有界性のみ。
`HasDerivAt`/Fisher core = 結論を bundle しない)。判定軸を各項目に付す (§5A-3 / §5B-2)。

> **重要 (verbatim 確認で判明した想定外)**: 本タスク brief は「Phase 0 structure 拡張が未着手」
> と仮定していたが、**Phase 0 は既にコード上 closed**。`IsRegularDeBruijnHypV2`
> (`:200-226`) は既に 3 field (`Z_law` / `density_t` / `density_t_eq`)、`debruijnIdentityV2_holds`
> (`:285-295`) は既に `_hX/_hZ/_hXZ` args 持ち、両者 `@audit:ok` (signature true 化済)。
> したがって §5A の structure 拡張は **Phase 0 の `density_t_eq` pin の上に `pX` 系 field を
> 積む増分**であり、false→true pivot のやり直しではない。

---

### §5A. `IsRegularDeBruijnHypV2` 拡張 — `pX`-witness 追加

#### 5A-1. 現 structure (verbatim, `FisherInfoV2DeBruijn.lean:200-226`)

```lean
structure IsRegularDeBruijnHypV2 {Ω : Type*} [MeasurableSpace Ω]
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (t : ℝ) where
  Z_law : P.map Z = gaussianReal 0 1
  density_t : ℝ → ℝ
  density_t_eq : ∀ x,
    density_t x = ((P.map (gaussianConvolution X Z t)).rnDeriv volume x).toReal
```

`density_t` は **時刻 t の pushforward 密度** (assembly 後の RHS
`fisherInfoOfDensityReal density_t` のキー)。`pX` (X 自身の密度) は不在。

#### 5A-2. 拡張案 — 追加 4 field

Phase 1b `pPath_eq_convDensityAdd` (`FisherInfoV2DeBruijnPerTime.lean:192-201` verbatim) が
要求する witness を field 化する。verbatim signature:

```lean
theorem pPath_eq_convDensityAdd
    (X Z : Ω → ℝ) (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z P)
    (hZ_law : P.map Z = gaussianReal 0 1)
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x)))
    {s : ℝ} (hs : 0 < s) :
    (P.map (gaussianConvolution X Z s)).rnDeriv volume
      =ᵐ[volume] fun z => ENNReal.ofReal (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) z)
```

→ 追加 field:

```lean
structure IsRegularDeBruijnHypV2 ... (t : ℝ) where
  Z_law : P.map Z = gaussianReal 0 1
  density_t : ℝ → ℝ
  density_t_eq : ∀ x,
    density_t x = ((P.map (gaussianConvolution X Z t)).rnDeriv volume x).toReal
  -- NEW: X 自身の Real 密度 witness (Phase 1b 入力)
  pX : ℝ → ℝ
  pX_nn : ∀ x, 0 ≤ pX x
  pX_meas : Measurable pX
  pX_law : P.map X = volume.withDensity (fun x => ENNReal.ofReal (pX x))
  -- NEW: density_t と pX の関係 (Phase 1b の結論を pointwise 密度形に降ろした pin)
  density_t_conv : ∀ x,
    density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, le_of_lt (by exact_mod_cast ?)⟩) x
```

> **`density_t_conv` の `⟨t, _⟩` 引数の注意**: Phase 1b の Gaussian variance witness は
> `⟨s, hs.le⟩ : ℝ≥0` (`hs : 0 < s`)。structure 内では `t` の正値性が field として直接無いため、
> `density_t_conv` 単体では `⟨t, _⟩` を作れない。2 案:
> - **案 A (推奨)**: `density_t_conv` を `0 < t` を仮定する全称形にしない (structure は
>   固定 `t` で量化済だが `0 < t` は持たない)。代わりに `density_t_conv` を
>   「`∀ (ht : 0 < t) x, density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x`」と
>   して `ht` を field-internal に受ける (consumer は `_ht` を渡せる)。
> - **案 B**: structure に `ht_pos : 0 < t` field を足す。ただし `debruijnIdentityV2_holds` は
>   既に `_ht : 0 < t` を別引数で受けており (`:289`)、二重持ちになるので非推奨。
> 案 A 採用。`density_t_conv : ∀ (ht : 0 < t), ∀ x, density_t x = convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x`。

#### 5A-3. honesty 判定 (各追加 field、監査向け)

| field | regularity か load-bearing か | 根拠 (core-reconstruction test) |
|---|---|---|
| `pX` (data) | regularity (bare data) | 密度関数そのもの。`HasDerivAt`/Fisher を含まない。`density_t` と同列の bare witness |
| `pX_nn` | regularity precondition | 密度の非負性。確率密度の自明な性質 |
| `pX_meas` | regularity precondition | 可測性。Phase 1b で `hpX_meas.ennreal_ofReal` に使う (`FisherInfoV2DeBruijnPerTime.lean:222`)。`Z_law` と同列 |
| `pX_law` | regularity precondition (外形等式) | `P.map X = withDensity (ofReal∘pX)` は「X が密度 pX を持つ」という外形等式。判定軸「前提条件か証明の核心か」→ 前者。`density_t_eq` (`= rnDeriv.toReal`) と同型の pin |
| `density_t_conv` | regularity / definitional pin (外形等式) | `density_t =ᵐ convDensityAdd pX g_t` の pointwise 形。**これは Phase 1b の結論そのもの** — load-bearing 化リスクを精査要 (下記 ⚠) |

⚠ **`density_t_conv` の load-bearing リスク精査**: `density_t_conv` は Phase 1b
`pPath_eq_convDensityAdd` の結論 (`rnDeriv =ᵐ ofReal∘convDensityAdd`) を `.toReal` 経由で
pointwise 密度等式に降ろしたもの。これを field 化すると「Phase 1b の結論を仮説に逃がす」=
load-bearing に見えうる。**判定**: Phase 1b は **既に genuine (`@audit:ok`, 0 sorry)** で
ある (`FisherInfoV2DeBruijnPerTime.lean:178-229`)。よって `density_t_conv` を field 化しても
「未証明の核心を仮説化する」のではなく「**既に証明済の補題の結論を structure 経由で
再供給する**」だけ。これは load-bearing 化ではない (核心は本物の sorry に残っていない)。
**ただし honesty 上より clean な代替**:

- **案 (i) 推奨 — field 化せず assembly body で `pPath_eq_convDensityAdd` を直接呼ぶ**。
  structure に `pX`/`pX_nn`/`pX_meas`/`pX_law` の 4 field だけ足し、`density_t_conv` は
  **足さない**。assembly 段 1 で `h_reg.pX`/`h_reg.pX_law` 等を `pPath_eq_convDensityAdd` に
  渡して `density_t =ᵐ convDensityAdd ...` を**その場で導出**する (`density_t_eq` (rnDeriv pin)
  + Phase 1b 結論 + `ENNReal.toReal_ofReal` で合成)。これなら Phase 1b 結論を field に
  bundle せず、honesty 上最も clean。
- **案 (ii) — `density_t_conv` を field 化**。assembly が 1 行短くなるが、上記 ⚠ の説明
  docstring が必須。

**§5A 最終推奨 = 案 (i)**: 追加 field は `pX`/`pX_nn`/`pX_meas`/`pX_law` の **4 つのみ**
(全て純 regularity)。`density_t_conv` は field 化せず assembly body で導出。これにより
structure 拡張は「X 密度 witness の regularity precondition 追加」だけになり、Phase 1b 結論の
bundle 疑義を完全に回避する。

#### 5A-4. 現 `density_t_eq` との二重 pin 関係の整理

拡張後、`density_t` は 2 つの pin を持つ:

- `density_t_eq` : `density_t x = (rnDeriv (P.map (X+√t·Z)) volume x).toReal` (時刻 t 密度 = 実 rnDeriv)
- (案 (i) では body 導出) `density_t =ᵐ convDensityAdd pX g_t` (Phase 1b 経由)

両者は **同じ密度の 2 表現** (rnDeriv 形 vs convolution 形) であり、Phase 1b
`pPath_eq_convDensityAdd` が `rnDeriv =ᵐ ofReal∘convDensityAdd` で結ぶ。整合性:
`density_t_eq` (rnDeriv.toReal) と Phase 1b (rnDeriv =ᵐ ofReal∘conv) を合成すると
`density_t =ᵐ (ofReal∘conv).toReal = conv` (非負性 + `ENNReal.toReal_ofReal`)。**矛盾しない、
むしろ assembly 段 1 = この合成**。docstring に「`density_t` は rnDeriv pin (`density_t_eq`)
と conv 表現 (Phase 1b) の 2 表現を持ち、両者は Phase 1b で a.e. 一致」と明記。

---

### §5B. Phase 2 main `heatFlow_density_heat_equation` の regularity hyp 形

#### 5B-1. 現 signature (verbatim, `FisherInfoV2DeBruijnPerTime.lean:412-426`)

```lean
theorem heatFlow_density_heat_equation
    (pX : ℝ → ℝ)
    (pPath pathDeriv1 pathDeriv2 : ℝ → ℝ → ℝ)
    (hpPath : ∀ (σ : ℝ) (hσ : 0 < σ),
      pPath σ = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩))
    (hpathDeriv1 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pPath σ ξ) (pathDeriv1 σ y) y)
    (hpathDeriv2 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pathDeriv1 σ ξ) (pathDeriv2 σ y) y)
    {s : ℝ} (hs : 0 < s) (x : ℝ) :
    HasDerivAt (fun σ : ℝ => pPath σ x) ((1/2) * pathDeriv2 s x) s := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)
```

現状の 3 pin (`hpPath`/`hpathDeriv1`/`hpathDeriv2`) は definitional pin (どの関数が
`pPath`/`pathDeriv1`/`pathDeriv2` *である*か)。残 gap (body docstring `:400-409` verbatim):
**(i) σ-積分記号下微分** `∂_σ pPath x = ∫ pX·∂_σ g_σ`、**(ii) spatial 2nd diff の `pathDeriv2`
同定** `pathDeriv2 s x = ∫ pX·∂²_x g_σ`。各 step に Gaussian-tail domination `Integrable`
構成が要る (~80+ 行)。kernel 群 7 件 (`kernel_{x_deriv1,x_deriv2,sigma_deriv,heat_eq}` 等、
`:242-361`、全 `@audit:ok`) で `∂_σ g_σ = (1/2)∂²_u g_σ` は genuine 済 → 残るは ∫ 越し lift。

#### 5B-2. 追加 hyp 設計 (Phase 3 / gateway atom と同型)

「∫ 越し微分」を genuine に閉じるには `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(gateway lemma) を **σ方向** と **spatial 方向** で 2 回適用する。各適用に必要な hyp は
`convDensityAdd_hasDerivAt` (`EPIConvDensity.lean:86-104` verbatim、`@audit:ok`) の 7 hyp 群と
同型。main signature に追加すべき hyp (**σ方向 lift 用**):

```lean
    -- σ方向 domination: ∂_σ (pX y · g_σ(x-y)) を σ-近傍で支配する integrable bound
    (boundσ : ℝ → ℝ) (hboundσ_int : Integrable boundσ volume)
    (hFσ_meas : ∀ᶠ σ in nhds s,
      AEStronglyMeasurable (fun y => pX y * heatFlow_density_heat_equation_kernel σ (x - y)) volume)
    (hFσ_int : Integrable (fun y => pX y * heatFlow_density_heat_equation_kernel s (x - y)) volume)
    (hFσ'_meas : AEStronglyMeasurable
      (fun y => pX y * ((1/2) * (heatFlow_density_heat_equation_kernel s (x-y) * ((x-y)^2/s^2 - 1/s)))) volume)
    (hbσ : ∀ᵐ y ∂volume, ∀ σ ∈ Set.Ioi (0:ℝ),
      ‖pX y * ((1/2) * (heatFlow_density_heat_equation_kernel σ (x-y) * ((x-y)^2/σ^2 - 1/σ)))‖ ≤ boundσ y)
    -- spatial 方向 domination (pathDeriv2 同定用): 同型を spatial 2nd deriv で
    (boundξ : ℝ → ℝ) (hboundξ_int : Integrable boundξ volume)
    (hbξ : ∀ᵐ y ∂volume, ‖pX y * (heatFlow_density_heat_equation_kernel s (x-y) * ((x-y)^2/s^2 - 1/s))‖ ≤ boundξ y)
```

> 上記 hyp 名/形は **設計骨子** であり、実装時に gateway lemma の正確な引数順 (`hs`/`hF_meas`/
> `hF_int`/`hF'_meas`/`h_bound`/`bound_integrable`/`h_diff`) に 1:1 で並べ直す。被積分関数の
> σ微分値は kernel 群 `heatFlow_density_heat_equation_kernel_sigma_deriv` (`:307-310` verbatim、
> `(1/2)·g_σ·(u²/σ²-1/σ)`)、spatial 2nd は `_x_deriv2` (`:286-298`、`g_σ·(u²/σ²-1/σ)`) を使う。
> `h_diff` (per-y 被積分関数の σ微分の `HasDerivAt`) は kernel `_sigma_deriv` を `pX y ·` でスケール
> して供給 (`.const_mul`)。

#### 5B-3. honesty 判定 (各追加 hyp、監査向け)

| hyp | regularity か load-bearing か | 根拠 |
|---|---|---|
| `boundσ`/`hboundσ_int` | regularity precondition | Gaussian-tail dominating function の integrability。Phase 3 `bound`/`hbound_int` (`:449-450` verbatim) と同型、gateway lemma の `bound_integrable` 引数 |
| `hFσ_meas`/`hFσ_int`/`hFσ'_meas` | regularity precondition | 被積分関数 + その σ微分の (ae)可測性 / 基点可積分性。gateway lemma の `hF_meas`/`hF_int`/`hF'_meas` |
| `hbσ`/`hbξ` | regularity precondition | **per-y 被積分関数** の σ微分 / spatial 2nd deriv の有界性 (domination)。**結論 (heat eq) を仮定していない** — `∂_σ pPath = (1/2)∂²_x pPath` という integral-level 等式は body で gateway lemma から *導出* される。判定軸: per-x/per-y の微分・有界性のみ = 前提条件 |
| `boundξ`/`hboundξ_int` | regularity precondition | spatial 方向 domination の integrable bound |

⚠ **load-bearing 回避の核**: heat eq 結論 `∂_σ pPath = (1/2)∂²_x pPath` を hyp 化**しない**
(L-PT-α の禁止事項)。追加 hyp は全て **被積分関数レベルの domination/integrability** であり、
kernel-level heat eq (`kernel_heat_eq`, genuine) を gateway lemma で ∫ 越しに lift する際の
*前提条件*。判定軸「前提条件 (regularity) か証明の核心 (load-bearing) か」→ 前者。Phase 3
`entropy_hasDerivAt_via_parametric` が同型の hyp 群で `@audit:ok` を得ている (`:448-464`) のが
honesty 上の precedent。

#### 5B-4. 拡張 structure からの供給

assembly (§5C 段 4) で Phase 2 を呼ぶとき、上記 domination hyp を拡張 structure の `pX` から
供給する。`boundσ`/`boundξ` は `pX y · (Gaussian-tail factor の上界)` の形 — `pX` 可積分
(`hpX_int` を Phase 1b 同様 `pX_law` + 確率測度から導出) × Gaussian factor 上界
(`gaussianPDFReal_le_prefactor` / `_x_deriv2` の closed form 有界性) で `Integrable.mul_bdd`
(Phase 1b bridge `:164-171` と同型)。**ただし**: σ微分 factor `(u²/σ²-1/σ)` は σ→0 で発散する
ため、σ-近傍を `Set.Ioi 0` でなく `Set.Ioo (s/2) (2s)` 等のコンパクト近傍に取り直して上界を
有限化する必要がありうる (実装時の落とし穴、L-PT-α 範囲)。**撤退ライン L-PT-α 維持**: この
domination 構成が ~80+ 行で session 内不可なら main body `sorry` + `@residual` 据置。

---

### §5C. Phase 5 assembly のステップ列 (擬似 Lean)

`debruijnIdentityV2_holds` body (`FisherInfoV2DeBruijn.lean:285-295`) を atom で組む。
現 signature (verbatim):

```lean
theorem debruijnIdentityV2_holds
    (X Z : Ω → ℝ) (_hX : Measurable X) (_hZ : Measurable Z) (_hXZ : IndepFun X Z P)
    {t : ℝ} (_ht : 0 < t) (h_reg : IsRegularDeBruijnHypV2 X Z P t) :
    HasDerivAt (fun s => differentialEntropy (P.map (gaussianConvolution X Z s)))
      ((1/2) * fisherInfoOfDensityReal h_reg.density_t) t := by
```

assembly 擬似コード (段ごと):

```lean
  -- 段 1: density 同定 (Phase 1b)。h_reg.pX/pX_law から density_t の conv 表現を得る。
  have h_dens : ∀ s, 0 < s →
      (P.map (gaussianConvolution X Z s)).rnDeriv volume
        =ᵐ[volume] fun z => ENNReal.ofReal (convDensityAdd h_reg.pX (gaussianPDFReal 0 ⟨s,_⟩) z) :=
    fun s hs => pPath_eq_convDensityAdd X Z _hX _hZ _hXZ h_reg.Z_law
      h_reg.pX h_reg.pX_nn h_reg.pX_meas h_reg.pX_law hs
  -- pPath s := convDensityAdd h_reg.pX (gaussianPDFReal 0 ⟨s,_⟩) と置く。
  -- density_t =ᵐ pPath t は h_dens t _ht + density_t_eq (rnDeriv pin) + toReal_ofReal で合成 (§5A-4)。

  -- 段 2: entropy = ∫ negMulLog density (DifferentialEntropy lemma)。
  --   differentialEntropy_eq_integral_density (DifferentialEntropy.lean:65) で
  --   h(P.map (X+√s·Z)) = ∫ x, negMulLog (pPath s x) ∂volume に書下し。
  --   要 hf_nn (density 非負 = convDensityAdd 非負 from pX_nn, gaussian_nn) + μ ≪ volume (s>0 で AC)。
  have h_ent_eq : ∀ s, 0 < s →
      differentialEntropy (P.map (gaussianConvolution X Z s)) = ∫ x, negMulLog (pPath s x) ∂volume := ...

  -- 段 3: parametric diff (Phase 3)。entropy の s-微分を ∫ 越しに。
  --   entropy_hasDerivAt_via_parametric pPath entDeriv bound (hbound_int ...) (hmeas ...) ...
  --   結論: HasDerivAt (fun s => ∫ negMulLog (pPath s x)) (∫ entDeriv t x) t。
  --   entDeriv t x := (d/ds) negMulLog (pPath s x)|_{s=t} = negMulLog'(pPath t x) · ∂_s pPath t x。
  have h_param : HasDerivAt (fun s => ∫ x, negMulLog (pPath s x) ∂volume)
      (∫ x, entDeriv t x ∂volume) t := entropy_hasDerivAt_via_parametric pPath entDeriv bound ...

  -- 段 4: heat eq で ∂_σ pPath → (1/2) ∂²_x pPath (Phase 2)。
  --   heatFlow_density_heat_equation h_reg.pX pPath pathDeriv1 pathDeriv2 hpPath hpathDeriv1 hpathDeriv2
  --     (+ §5B domination hyp、h_reg.pX から供給) hs x。
  --   → ∂_s pPath t x = (1/2) pathDeriv2 t x。これを entDeriv に代入して
  --     ∫ entDeriv t x = ∫ negMulLog'(pPath t x) · (1/2) pathDeriv2 t x。
  have h_heat : ∀ x, HasDerivAt (fun σ => pPath σ x) ((1/2) * pathDeriv2 t x) t :=
    fun x => heatFlow_density_heat_equation h_reg.pX pPath pathDeriv1 pathDeriv2 ... _ht x

  -- 段 5: IBP (Phase 4a)。∫ negMulLog'(p)·∂_s p →IBP→ -(1/2)∫ ∂_x(negMulLog'∘p)·∂_s p
  --   = (1/2)∫ (∂_x p)²/p (negMulLog'' chain + sign)。
  --   debruijn_ibp_step u v u' v' hu hv huv' hu'v huv で u=negMulLog'∘p, v=∂_s p 等を置く。
  have h_ibp : ∫ x, u x * v' x = - ∫ x, u' x * v x := debruijn_ibp_step u v u' v' ...

  -- 段 6: fisher congr (Phase 4b)。∫ (logDeriv p)²·p = fisherInfoOfDensityReal p。
  --   fisher_from_logDeriv (pPath t) hp_nn hint。
  have h_fisher : ∫ x, (logDeriv (pPath t) x)^2 * pPath t x ∂volume
      = fisherInfoOfDensityReal (pPath t) := fisher_from_logDeriv (pPath t) ...

  -- 段 7: 最終 congr。RHS を (1/2) * fisherInfoOfDensityReal h_reg.density_t に一致。
  --   ∫ entDeriv t = (1/2)∫(∂_x p)²/p (段 5) = (1/2) fisherInfoOfDensityReal (pPath t) (段 6)
  --   = (1/2) fisherInfoOfDensityReal h_reg.density_t (density_t =ᵐ pPath t from 段 1
  --     + fisherInfoOfDensityReal の =ᵐ congr)。
  --   h_param (段 3) の deriv 値を rewrite chain で RHS に一致させ、
  --   h_ent_eq (段 2) で LHS の関数を entropy に戻して結論。
  rw [...] -- congr chain
  exact h_param.congr ... -- or convert
```

#### 各段の atom 仮説 discharge 対応表

| 段 | atom | atom が要求する主要仮説 | discharge 元 |
|---|---|---|---|
| 1 | `pPath_eq_convDensityAdd` | `hX/hZ/hXZ` | `_hX/_hZ/_hXZ` (`debruijnIdentityV2_holds` args) |
| 1 | 〃 | `hZ_law` | `h_reg.Z_law` |
| 1 | 〃 | `pX/hpX_nn/hpX_meas/hpX_law` | **拡張 structure `h_reg.pX`/`.pX_nn`/`.pX_meas`/`.pX_law` (§5A)** |
| 1 | 〃 | `hs : 0 < s` | `_ht` (s = t) |
| 1 | density_t↔pPath 合成 | — | `h_reg.density_t_eq` (rnDeriv pin) + 段1結論 + `toReal_ofReal` (§5A-4) |
| 2 | `differentialEntropy_eq_integral_density` | `hf_nn` (density 非負) | `convDensityAdd` 非負 = `h_reg.pX_nn` + `gaussianPDFReal_nonneg` |
| 2 | 〃 | `μ ≪ volume` | `_ht : 0 < t` (Gaussian smoothing で AC、Phase 1b の `hv_ne` 経由) |
| 3 | `entropy_hasDerivAt_via_parametric` | `bound`/`hbound_int` (Gaussian-tail) | `h_reg.pX` から構成 (`Integrable.mul_bdd` 同型) |
| 3 | 〃 | `hmeas`/`hint`/`hderiv_meas` | 被積分関数 (ae)可測性 / 基点可積分性、`pX_meas` + kernel 可測性 |
| 3 | 〃 | `hb`/`hdiff` (per-x 微分・有界) | kernel 群 + `pX` domination |
| 4 (Ph2) | `heatFlow_density_heat_equation` | `hpPath`/`hpathDeriv1`/`hpathDeriv2` (定義 pin) | `pPath`/`pathDeriv1`/`pathDeriv2` の定義から (`hpPath` = `convDensityAdd h_reg.pX g_σ` 一致、`rfl`/`Phase 1b`) |
| 4 (Ph2) | 〃 | §5B domination hyp (`boundσ`/`hbσ` 等) | **拡張 structure `h_reg.pX` から構成 (§5B-4)** |
| 5 | `debruijn_ibp_step` | `hu`/`hv` (tsupport 全域 `HasDerivAt`) | density `pPath t` の global C¹ (`convDensityAdd_hasDerivAt` 経由、L-PT-δ) |
| 5 | 〃 | `huv'`/`hu'v`/`huv` (integrability) | Gaussian-tail integrability、`h_reg.pX` domination |
| 6 | `fisher_from_logDeriv` | `hp_nn` (density 非負) | `convDensityAdd` 非負 = `pX_nn` + gaussian_nn |
| 6 | 〃 | `hint` (integrability) | Fisher 被積分関数の integrability、L-PT-δ 範囲 |
| 7 | (最終 congr) | — | 段1-6 の have を rewrite chain で結合 |

> **assembly の最大コスト段 = 段 4 (Phase 2 main、L-PT-α)**。Phase 2 main が honest sorry の
> 間は assembly 全体も transitive sorry (段 4 の `heatFlow_density_heat_equation` body 経由)。
> したがって **Phase 5 proof done は Phase 2 main closure に gated**。Phase 2 main を sorry の
> まま assembly を組んでも `debruijnIdentityV2_holds` は段 4 の transitive sorry を持つため
> `@audit:ok` には到達しない (type-check done 止まり)。**推奨着手順**: §5A structure 拡張 +
> Gaussian constructor ripple (§5D) を先行 (type-check done で commit) → §5B Phase 2 main hyp
> 追加 + domination 構成 (L-PT-α 解除トライ) → §5C assembly → §5 capstone congr + `@audit:ok`。

---

### §5D. consumer ripple 表 (structure 拡張で影響する file:line)

§5A の structure 拡張 (`pX`/`pX_nn`/`pX_meas`/`pX_law` の 4 field 追加) は
`IsRegularDeBruijnHypV2` の **constructor / structure literal を持つ全 site** に ripple する。
verbatim 確認した影響箇所:

| file:line | declaration | touch 内容 | 新 field 充足方法 |
|---|---|---|---|
| `FisherInfoV2DeBruijn.lean:200` | `IsRegularDeBruijnHypV2` (structure) | 4 field 追加 (§5A-2) + docstring に「`pX` 系は regularity precondition、二重 pin 整理 §5A-4」追記 | — |
| `FisherInfoV2DeBruijn.lean:285` | `debruijnIdentityV2_holds` | body assembly (§5C)。signature 不変 (新 field は `h_reg` 経由で取得) | — |
| `FisherInfoV2DeBruijn.lean:313` | `deBruijn_identity_v2` | pass-through (`:323` で `debruijnIdentityV2_holds X Z hX hZ hXZ ht h_reg` call)。**signature 不変** (新 field は `h_reg` に内包) | — (追従不要) |
| `FisherInfoV2DeBruijn.lean:379` | `IsDeBruijnPathRegular` (structure) | `reg_t` field (`:385`) が返す `∃ h_reg : IsRegularDeBruijnHypV2, h_reg.density_t = fPath t` の existential witness 構成が新 field 込みになる。**構造変更不要** (existential 内で h_reg を作る consumer が新 field を埋める) | — (consumer 側) |
| `FisherInfoV2DeBruijn.lean:419` | `debruijnIntegrationIdentity_holds` | pass-through (`:443` で `debruijnIdentityV2_holds X Z hX hZ hXZ ht.1 h_reg` call、h_reg は `h_path.reg_t` 由来)。**signature 不変** | — (追従不要) |
| `EPIL3Integration.lean:678` | `isRegularDeBruijnHypV2_family_of_gaussian` | structure literal (`:693-706`) に 4 field 追加。Gaussian case の `pX` = `gaussianPDFReal m v` (X ∼ 𝒩(m,v) の密度) | 下記詳細 |
| `EPIStamDischarge.lean:251` | `IsDeBruijnIntegrationHyp` (structure) の `reg_at` field (`:260`) | `reg_at : ∀ t, 0<t → IsRegularDeBruijnHypV2 X Z P t` の witness が新 field 込みに。**構造変更不要** (witness は `isRegularDeBruijnHypV2_family_of_gaussian` 経由 → そこで充足) | — (上流 constructor 側) |

#### Gaussian constructor (`EPIL3Integration.lean:693-706`) の新 field 充足

現 literal (verbatim, `:693-706`):

```lean
exact
  { Z_law := hZ_law
    density_t := gaussianPDFReal m (v + ⟨t, ht.le⟩)
    density_t_eq := by sorry }   -- 既存 @residual(plan:epi-debruijn-pertime-closure)
```

> **verbatim 確認で判明した想定外**: Gaussian constructor の `density_t_eq` は既に
> `by sorry` + `@residual(plan:epi-debruijn-pertime-closure)` (`:701-706`)。brief は「新 field を
> どう埋めるか」を問うが、**既存 `density_t_eq` 自体がまだ sorry** であり、これも Phase 1 の
> Gaussian 特殊形 (`gaussianConvolution_law_of_gaussian` + Gaussian rnDeriv) で closure 待ち。

拡張後の literal:

```lean
exact
  { Z_law := hZ_law
    density_t := gaussianPDFReal m (v + ⟨t, ht.le⟩)
    density_t_eq := by sorry   -- @residual(plan:epi-debruijn-pertime-closure) (既存)
    -- NEW fields (Gaussian case):
    pX := gaussianPDFReal m v                          -- X ∼ 𝒩(m,v) の密度
    pX_nn := fun x => gaussianPDFReal_nonneg m v x      -- genuine
    pX_meas := measurable_gaussianPDFReal m v           -- genuine
    pX_law := by                                        -- P.map X = withDensity (ofReal∘gaussianPDFReal m v)
      rw [_hX_law]                                       --   = gaussianReal m v
      exact gaussianReal_of_var_ne_zero m _hv }          --   genuine (要 v ≠ 0、_hv 既受)
```

- `pX := gaussianPDFReal m v` (数値 verbatim 確認: X ∼ 𝒩(m,v) の Lebesgue 密度 = `gaussianPDFReal m v`、
  Phase 1b の `gaussianReal_of_var_ne_zero` と整合)。
- `pX_nn` / `pX_meas` は Mathlib 直結 (`gaussianPDFReal_nonneg` / `measurable_gaussianPDFReal`、
  Phase 1b でも使用 `:167-170`)。
- `pX_law` は `_hX_law : P.map X = gaussianReal m v` (`:683` verbatim、既受) +
  `gaussianReal_of_var_ne_zero m _hv` (`𝒩(m,v) = withDensity (gaussianPDF m ⟨v,_⟩)`) で genuine。
  **`gaussianPDF` (ENNReal 版) vs `ofReal∘gaussianPDFReal` の shape 整合**に注意 (Phase 1b
  `:220` `gaussianReal_of_var_ne_zero 0 hv_ne` の使い方を参照、`gaussianPDF` 定義が
  `ofReal∘gaussianPDFReal` か別形かを verbatim 確認してから埋める)。
- `_hv : v ≠ 0` (`:682` 既受) を `pX_law` で使う (現状 underscore-prefix なので使用時に rename か
  `_hv` のまま参照)。**ripple 注意**: `_hv` を使うと unused→used になり underscore 外す edit が要る。

> 4 新 field のうち `pX`/`pX_nn`/`pX_meas`/`pX_law` は Gaussian case で **全て genuine 充足可**
> (新規 sorry を生まない)。既存の `density_t_eq := by sorry` は不変 (Phase 1 Gaussian 特殊形で別途
> closure)。したがって structure 拡張による Gaussian constructor の新規 sorry は **0 件**。

#### 非 Gaussian consumer

verbatim grep (`rg "IsRegularDeBruijnHypV2"`) で確認した structure literal を持つ site は
**Gaussian constructor 1 件のみ** (`isRegularDeBruijnHypV2_family_of_gaussian`)。他の言及
(`reg_at`/`reg_t`/`density_t` field 参照) は全て **field 抽出 (pass-through)** であり literal
構成ではないため、4 field 追加で type-check が壊れるのは Gaussian constructor のみ。EPIStamDischarge
`reg_at` (`:260`) と FisherInfoV2DeBruijn `reg_t` (`:385`) は existential/関数で
`IsRegularDeBruijnHypV2` を *返す* が、その witness 生成は最終的に Gaussian constructor に
帰着する (非 Gaussian の独立 constructor は現状不在) ため、ripple は Gaussian constructor 1 点に
集約。

---

### §5E. Phase 5 詳細設計の撤退ライン整合

§5B の Phase 2 main domination 構成は **既存 L-PT-α を維持** (~80+ 行で session 内不可なら
main body `sorry` 据置)。§5A structure 拡張 + §5D Gaussian ripple は L-PT-α と独立に先行可
(type-check done)。assembly §5C は Phase 2 main に transitive gated (上記 §5C 末尾の注記)。

**全 Phase 共通禁止事項 (再掲・本詳細設計に適用)**: §5A の `pX` 系 4 field は純 regularity
(load-bearing でない、§5A-3)。§5B の domination hyp は per-y 被積分関数の微分・有界性のみ
(heat eq 結論を hyp 化しない、§5B-3)。`density_t_conv` の field 化は案 (i) で回避
(Phase 1b 結論を bundle しない)。詰まったら `sorry` + `@residual(plan:epi-debruijn-pertime-closure)`
(tier 2)。

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
4. **Phase 5 詳細設計起草 + Phase 0 完了済の verbatim 確認** (2026-05-31, lean-planner):
   §Phase 5 詳細設計 (§5A-5E) を起草。verbatim 確認で **Phase 0 は既にコード上 closed** と判明
   (`IsRegularDeBruijnHypV2:200-226` が既に `density_t_eq` 持ち `@audit:ok`、
   `debruijnIdentityV2_holds:285-295` が既に `_hX/_hZ/_hXZ` 持ち `@audit:ok`)。本 plan §Phase 0
   本文は已完了工程の記述。したがって structure 拡張は false→true pivot のやり直しではなく
   `density_t_eq` pin の上に `pX` 系 field を積む増分。
5. **structure 拡張 = `pX` 系 4 field のみ、`density_t_conv` は field 化しない (案 (i))**
   (2026-05-31): Phase 1b `pPath_eq_convDensityAdd` が要求する `pX`/`pX_nn`/`pX_meas`/`pX_law` を
   `IsRegularDeBruijnHypV2` に追加 (全て純 regularity、§5A-3)。`density_t` と `pX` の関係
   (`density_t =ᵐ convDensityAdd pX g_t`) は **field 化せず** assembly body で `pPath_eq_convDensityAdd`
   (既 genuine `@audit:ok`) を直接呼んで導出する。理由: Phase 1b の結論を field に bundle すると
   load-bearing 疑義 (既証明補題の再供給だが honesty 上 clean でない)。案 (i) で Phase 1b 結論の
   bundle を完全回避 (§5A-3 ⚠)。
6. **Phase 2 main domination hyp は Phase 3 / gateway atom と同型 (load-bearing でない)**
   (2026-05-31): `heatFlow_density_heat_equation` の残 gap (∫ 越し σ微分 + spatial 2nd diff 同定) を
   genuine 化するため main signature に per-y 被積分関数 domination hyp (`boundσ`/`hbσ`/`boundξ`/`hbξ`
   等) を追加 (§5B-2)。heat eq 結論 `∂_σ pPath = (1/2)∂²_x pPath` は **hyp 化しない** (L-PT-α 禁止
   事項)、被積分関数レベルの微分・有界性のみ。precedent = Phase 3 `entropy_hasDerivAt_via_parametric`
   が同型 hyp 群で `@audit:ok` (§5B-3)。σ微分 factor `(u²/σ²-1/σ)` の σ→0 発散に注意 (コンパクト
   σ-近傍を取る、実装時 L-PT-α 範囲、§5B-4)。
7. **consumer ripple は Gaussian constructor 1 点に集約、新規 sorry 0 件** (2026-05-31):
   `rg "IsRegularDeBruijnHypV2"` verbatim 確認で structure literal を持つ site は
   `isRegularDeBruijnHypV2_family_of_gaussian` (`EPIL3Integration.lean:678`) のみ。他は全て field
   抽出 pass-through。Gaussian case の `pX` = `gaussianPDFReal m v` (X∼𝒩(m,v) 密度)、4 新 field は
   全て genuine 充足可 (`gaussianPDFReal_nonneg`/`measurable_gaussianPDFReal`/`gaussianReal_of_var_ne_zero`)。
   ただし既存 `density_t_eq := by sorry` (`:706`) は不変 (Phase 1 Gaussian 特殊形で別途 closure 待ち、
   想定外発見)。`_hv : v≠0` を `pX_law` で使うため underscore 外す edit 要 (§5D)。
8. **Phase 5 proof done は Phase 2 main closure に gated** (2026-05-31): assembly §5C 段 4 が
   `heatFlow_density_heat_equation` を呼ぶため、Phase 2 main が honest sorry の間は
   `debruijnIdentityV2_holds` も transitive sorry。着手順 = §5A 拡張 + §5D ripple 先行 (type-check
   done で commit) → §5B Phase 2 main hyp + domination (L-PT-α 解除トライ) → §5C assembly →
   capstone congr + `@audit:ok`。
