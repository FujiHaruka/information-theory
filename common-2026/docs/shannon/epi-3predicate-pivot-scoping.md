# EPI 3述語 signature pivot — consumer/import scoping (read-only)
Date: 2026-05-30

> READ-ONLY 調査。コード未編集。すべて verbatim 引用 + file:line (現 HEAD 19d5446)。

## 0. ブリーフ前提の照合結果 (先に読む)

ブリーフの主要前提は **概ね正しい**。訂正点は 2 つだけ:

- **line 番号が一部 stale**。実 file:line で確定した正値:
  - `IsStamCauchySchwarzOptimal` = `EPIStamInequalityBody.lean:269` ✅ (一致)
  - `IsStamCondExpCSHyp` = `EPIStamStep12Body.lean:200` ✅ (一致)
  - `IsStamInequalityResidual` = `EntropyPowerInequality.lean:190` ✅ (一致)
  - `stam_step2_density_wall` = **`EPIStamInequalityBody.lean:359`** (ブリーフは「:359」と書きつつ別所で Step12Body と混同していたが、実体は **InequalityBody** にある)
  - `stam_inequality_via_predicate_optimal` = **`EPIStamInequalityBody.lean:387`** ✅
  - `stamCauchySchwarzOptimal_of_condExpCSHyp` = **`EPIStamStep12Body.lean:257`** ✅
  - `isStamCauchySchwarz_of_condExpCSHyp` = **`EPIStamStep12Body.lean:215`** ✅
- **`convDensityAdd` は実在する** (ブリーフが `EPIConvDensity.convDensityAdd` と呼ぶもの)。`EPIConvDensity.lean:39` `noncomputable def convDensityAdd (pX pY : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ x, pX x * pY (z - x) ∂volume`。ブリーフ語の `convDensityAdd` で正しい。

**defect 種別はブリーフ通り false-statement**。3 述語とも `fX fY fXY : ℝ → ℝ` を **無制約全称量化** し、`fXY = convDensityAdd fX fY` の handle を持たない。反例 (`stam_step2_density_wall` docstring `:323-326` verbatim): `fX=fY=gaussianPDFReal 0 1` (`J_X=J_Y=1`, RHS `=1/2`)、`fXY=gaussianPDFReal 0 (1/100)` (`J_sum=100`) で `100 ≤ 1/2` False。**かつ** `fisherInfoOfMeasureV2 μ f` は measure 引数を無視 (= `fisherInfoOfDensity f`) なので density も `P.map X/Y/(X+Y)` に tie されていない (docstring `:320-322`)。

---

## 1. consumer グラフ

### 定義 (3 述語、verbatim 結論)

| 述語 | 定義 file:line | 結論 (= 述語 body) verbatim |
|---|---|---|
| `IsStamCauchySchwarzOptimal X Y P` | `EPIStamInequalityBody.lean:269` | `∀ (J_X J_Y J_sum : ℝ) (fX fY fXY : ℝ → ℝ), 0 < J_X → 0 < J_Y → 0 < J_sum → J_X = (…fisherInfoOfMeasureV2 (P.map X) fX).toReal → J_Y = (…(P.map Y) fY).toReal → J_sum = (…(P.map (X+Y)) fXY).toReal → J_sum ≤ J_X * J_Y / (J_X + J_Y)` (:271-276) |
| `IsStamCondExpCSHyp X Y P` | `EPIStamStep12Body.lean:200` | 同 3 Fisher = 定義 + `∀ lam, 0 ≤ lam → lam ≤ 1 → J_sum ≤ lam^2 * J_X + (1 - lam)^2 * J_Y` (:202-208) |
| `IsStamInequalityResidual X Y P` | `EntropyPowerInequality.lean:190` | `∀ … fX fY fXY, 0<J_X→0<J_Y→0<J_sum→ J_X = fisherInfoOfDensityReal fX → J_Y = fisherInfoOfDensityReal fY → J_sum = fisherInfoOfDensityReal fXY → 1 / J_sum ≥ 1 / J_X + 1 / J_Y` (:192-196) |

`IsStamCauchySchwarzOptimal` / `IsStamCondExpCSHyp` は **measure-keyed** `fisherInfoOfMeasureV2 (P.map _) f` を、`IsStamInequalityResidual` は **density-keyed** `fisherInfoOfDensityReal f` を使う (後者は import-cycle 回避のため、§2 参照)。

### 全参照 (定義以外) — 生成/消費 + instantiate

| 述語 | 参照 file:line | declaration | 生成/消費 | instantiate (verbatim) |
|---|---|---|---|---|
| `IsStamCauchySchwarzOptimal` | `EPIStamInequalityBody.lean:359` | `stam_step2_density_wall` | **生成** (結論=述語) | body `sorry` (:364)。`@audit:defect(false-statement)`。 |
| 〃 | `EPIStamInequalityBody.lean:387` | `stam_inequality_via_predicate_optimal` | **消費** (`h_cs_opt`) | `intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def; have h_le := h_cs_opt J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def; exact stam_inverse_form_of_harmonic_mean hJX hJY hJsum h_le` (:397-399) — 12 引数を `intro` して順に丸渡し。 |
| 〃 | `EPIStamInequalityBody.lean:410` | `isStamInequalityHyp_via_body` | **消費** (`h_cs_opt`) | `intro … (12 args); exact stam_inequality_via_predicate_optimal h_cs_opt J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def` (:415-417)。 |
| 〃 | `EPIStamInequalityBody.lean:463` | `isStamCauchySchwarz_of_optimal` | **消費** (`h`) | `intro … (12 args); refine ⟨J_Y/(J_X+J_Y), …⟩; … have h_le := h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def; linarith [h_min]` (:468-481)。 |
| 〃 | `EPIStamInequalityBody.lean:503` | `isStamCauchySchwarzOptimal_of_lambda_optimal` | **生成** | `intro … (12 args); have h_bd := h … ; linarith [h_min]` (:514-517) — λ-witness hyp `h` から生成。 |
| 〃 | `EPIStamInequalityBody.lean:532` | `isStamInequalityHyp_via_body_to_pipeline` | **消費** (`h_cs_opt`) | `{ stam := isStamInequalityHyp_via_body h_cs_opt }` (:537) 丸渡し。 |
| 〃 | `EPIStamInequalityBody.lean:574` | `entropy_power_inequality_via_body` | **消費** (内部生成→消費) | `have h_cs_opt := stam_step2_density_wall P X Y hX hY hXY; have h_stam := isStamInequalityHyp_via_body h_cs_opt; exact epi_via_stam_main P X Y X hX hY hXY h_stam h_bridge` (:581-583) — **wall を内部呼出**、load-bearing hyp は持たない。 |
| 〃 | `EPIStamStep12Body.lean:257` | `stamCauchySchwarzOptimal_of_condExpCSHyp` | **生成** (結論=述語) | `intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def; … have h_bd := h … (J_Y/(J_X+J_Y)) …; have h_min := stam_lambda_min hJX hJY; linarith [h_bd, h_min]` (:260-268) — `IsStamCondExpCSHyp` から optimal λ で生成。 |
| 〃 | `EPIStamStep12Body.lean:278` | `stamCauchySchwarzOptimal_of_step12` | **生成** | `stamCauchySchwarzOptimal_of_condExpCSHyp h_cs` (:283) 丸渡し。 |
| `IsStamCondExpCSHyp` | `EPIStamStep12Body.lean:215` | `isStamCauchySchwarz_of_condExpCSHyp` | **消費** (`h`) | `intro J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def; … exact h J_X J_Y J_sum fX fY fXY hJX hJY hJsum hJX_def hJY_def hJsum_def (J_Y/(J_X+J_Y)) (by positivity) (by …)` (:218-223) — 12 引数 + λ + 2 bound を渡す。 |
| 〃 | `EPIStamStep12Body.lean:227` | `isStamCondExpCSHyp_congr` | **消費/生成** | `subst hX; subst hY; exact h` (:230) — congruence。 |
| 〃 | `EPIStamStep12Body.lean:234` | `isStamCondExpCSHyp_symm` | **消費/生成** | `intro J_Y J_X … lam hlo hhi; … have hbd := h J_X J_Y J_sum fX fY fXY … (1 - lam) …; linarith` (:237-243) — X/Y swap + λ↦1-λ。 |
| 〃 | `EPIStamStep12Body.lean:257` | `stamCauchySchwarzOptimal_of_condExpCSHyp` | **消費** (`h`) | 上記参照 (生成 Optimal / 消費 CondExp の両方)。 |
| 〃 | `EPIStamStep12Body.lean:278` | `stamCauchySchwarzOptimal_of_step12` | **消費** (`h_cs`) | `stamCauchySchwarzOptimal_of_condExpCSHyp h_cs` (:283)。 |
| 〃 | `EPIStamStep12Body.lean:299` | `isStamInequalityHyp_of_step12` | **消費** (`h_cs`) | `isStamInequalityHyp_via_body (stamCauchySchwarzOptimal_of_step12 h_conv h_cs)` (:304-305)。 |
| 〃 | `EPIStamStep12Body.lean:313` | `isStamCauchySchwarz_of_step12` | **消費** (`h_cs`) | `isStamCauchySchwarz_of_condExpCSHyp h_cs` (:318)。 |
| `IsStamInequalityResidual` | `EntropyPowerInequality.lean:208` | `IsStamToEPIBridge` (def) | **消費** (定義の antecedent) | `IsStamInequalityResidual X Y P → IsEntropyPowerInequalityHypothesis X Y P` (:208)。 |
| 〃 | `EntropyPowerInequality.lean:223` | `stamToEPIBridge_holds` | (生成 Bridge、Residual を間接消費) | body `sorry` (:226)、`@residual(plan:epi-stam-to-conclusion-plan)`。Residual を hyp に取らず Bridge 全体を生成。 |
| 〃 | `EntropyPowerInequality.lean:261` | `entropy_power_inequality` | **消費** (`h_stam`) | `stamToEPIBridge_holds X Y P h_stam` (:268) — `h_stam : IsStamInequalityResidual` を bridge に適用。 |
| 〃 | `EntropyPowerInequality.lean:278` | `entropy_power_inequality_exp_form` | **消費** (`h_stam`) | `have h := entropy_power_inequality P X Y hX hY hXY h_stam; simpa [entropyPower] using h` (:287-288)。 |
| 〃 | `EntropyPowerInequality.lean:393` | (§D Gaussian corollary, `h_stam`) | **消費** | `h_stam : IsStamInequalityResidual X Y P` を引数に取る (:393)。 |
| 〃 | `EPIPlumbing.lean:192` | (consumer, `h_stam`) | **消費** | `(h_stam : IsStamInequalityResidual X Y P)` 引数 (:192)。 |
| 〃 | `EPIPlumbing.lean:267` | (consumer, `h_stam`) | **消費** | `(h_stam : IsStamInequalityResidual X Y P)` 引数 (:267)。 |
| 〃 | `EPIStamToBridge.lean:1109` | (bridge consumer, `h_stam`) | **消費** | `(h_stam : IsStamInequalityResidual X Y P)` 引数 (:1109)。 |

### 既知 ripple 候補の所在確定 (ブリーフ列挙、rg 確定)

| ブリーフ名 | 実在? | 実 file:line + 述語との関係 |
|---|---|---|
| `stam_inequality_via_predicate_optimal` | ✅ | `EPIStamInequalityBody.lean:387`。`IsStamCauchySchwarzOptimal` 消費。 |
| `stamCauchySchwarzOptimal_of_condExpCSHyp` | ✅ | `EPIStamStep12Body.lean:257`。CondExp 消費 → Optimal 生成。 |
| `isStamCauchySchwarz_of_condExpCSHyp` | ✅ | `EPIStamStep12Body.lean:215`。CondExp 消費。 |
| `entropy_power_inequality_via_body` | ✅ | `EPIStamInequalityBody.lean:574`。wall 内部呼出。 |
| `stam_convex_fisher_bound_gaussian` | ✅ | `StamGaussianBound.lean:77`。**3 述語を参照しない** (V2-keyed Gaussian closed-form、別系)。ブリーフ「ripple 候補」だが実 ripple は **無い** — docstring の散文参照のみ。 |
| `isStamInequalityHyp_via_step3` | ✅ | `EPIStamStep3Body.lean:121`。body `isStamInequalityHyp_via_body (stam_step2_density_wall P X Y hX hY hXY)` (:125) — wall を内部呼出、`IsStamCauchySchwarzOptimal` を間接消費。 |
| `isStamInequalityHyp_of_primitives` | ✅ | `EPIStamDeBruijnConclusion.lean:169`。body `isStamInequalityHyp_via_step3 P X Y hX hY hXY` (:174)。 |
| `entropy_power_inequality_via_stamDeBruijn` | ✅ | `EPIStamDeBruijnConclusion.lean:203`。body `{ stam := isStamInequalityHyp_of_primitives P X Y hX hY hXY }` (:211)。 |
| `stam_step2_density_wall` | ✅ | `EPIStamInequalityBody.lean:359`。`IsStamCauchySchwarzOptimal` 生成 (sorry)。 |

**ripple 結論**: consumer は **全て** 12 引数の `intro … exact h …` 透過 or 丸渡し or `{ stam := … }` record build。`fXY` に具体値を渡して quantifier を閉じる consumer は **皆無**。pivot で述語に `(hconv : fXY =ᵐ[volume] convDensityAdd fX fY)` + density regularity を追加すると、**producer 側 3 つ** (`stam_step2_density_wall` :359、`stamCauchySchwarzOptimal_of_condExpCSHyp` :257 経由の chain、`isStamInequalityResidual` の wall) の証明義務が genuine 化し、**consumer 側** は `intro` リストに新 hyp 1 つ追加 + `exact h … hconv` で透過する。`stam_convex_fisher_bound_gaussian` は別系で ripple 不要。

---

## 2. import グラフ + cycle 判定 (最重要)

### 各 file の import 行 (verbatim、`InformationTheory.*` のみ抜粋 + EPIConvDensity)

```
EPIConvDensity.lean:
  import InformationTheory.Shannon.FisherInfoV2          ← InformationTheory 依存はこれ 1 本のみ
  import Mathlib.Analysis.Calculus.ParametricIntegral
  import Mathlib.Analysis.Calculus.LogDeriv

EntropyPowerInequality.lean:
  import InformationTheory.Meta.EntryPoint
  import InformationTheory.Shannon.DifferentialEntropy
  import InformationTheory.Shannon.FisherInfo
  import InformationTheory.Shannon.FisherInfoV2
  (+ Mathlib)
  ※ FisherInfoV2DeBruijn を import しない / EPIConvDensity を import しない

EPIStamInequalityBody.lean:
  import InformationTheory.Shannon.EntropyPowerInequality
  import InformationTheory.Shannon.EPIPlumbing
  import InformationTheory.Shannon.EPIStamDischarge
  import InformationTheory.Shannon.EPIL3Integration
  import InformationTheory.Shannon.FisherInfoV2
  import InformationTheory.Shannon.FisherInfoV2DeBruijn   ← 既に DeBruijn を import 済
  import InformationTheory.Shannon.FisherInfoGaussian
  import InformationTheory.Shannon.DifferentialEntropy
  (+ Mathlib)
  ※ EPIConvDensity を import しない

EPIStamStep12Body.lean:
  import InformationTheory.Shannon.EPIStamDischarge
  import InformationTheory.Shannon.EPIStamInequalityBody   ← InequalityBody を import 済 (述語の依存元)
  import InformationTheory.Shannon.FisherInfoV2
  import InformationTheory.Shannon.FisherInfoV2DeBruijn
  (+ Mathlib Tactic)
  ※ EPIConvDensity を import しない

FisherInfoV2DeBruijn.lean:
  import InformationTheory.Shannon.FisherInfoV2          ← InformationTheory 依存はこれ 1 本のみ
  (+ Mathlib)
```

### EPIConvDensity の依存方向 (cycle 判定の核心)

- **EPIConvDensity は `InformationTheory.Shannon.FisherInfoV2` のみ** に依存 (+ Mathlib)。3 述語 file・EntropyPowerInequality・FisherInfoV2DeBruijn のいずれも **import しない**。葉に近い module。
- `InformationTheory.lean` で EPIConvDensity は **最後尾 :206** (`import InformationTheory.Shannon.EPIScoreCrossTermOrth` の次)。root aggregator 順は依存を表さないが、最後尾 = 「誰も EPIConvDensity を import していない」傍証。

### cycle 判定 (3 述語ごと)

| pivot 先 file | 追加 import | cycle? | 根拠 |
|---|---|---|---|
| `EntropyPowerInequality` | `import InformationTheory.Shannon.EPIConvDensity` | **CYCLE!** | **EPIConvDensity → FisherInfoV2、EntropyPowerInequality → FisherInfoV2** は OK だが、**EPIConvDensity を EntropyPowerInequality が import すると、EPIConvDensity が EntropyPowerInequality を (推移的に) import し返さないか?** → EPIConvDensity の依存は FisherInfoV2 のみで EntropyPowerInequality を引かない。よって **実は cycle にならない**。ただし下記「真の cycle 源」を参照。 |
| `EPIStamInequalityBody` | `import …EPIConvDensity` | **NO cycle** | InequalityBody → (EntropyPowerInequality, FisherInfoV2DeBruijn, …)。EPIConvDensity → FisherInfoV2 のみ。InequalityBody を EPIConvDensity が引かない。一方向。 |
| `EPIStamStep12Body` | `import …EPIConvDensity` | **NO cycle** | Step12Body → InequalityBody → …。EPIConvDensity は誰も引き返さない。 |

**3 述語とも `import InformationTheory.Shannon.EPIConvDensity` 追加で cycle は生じない。** EPIConvDensity は FisherInfoV2 のみに依存する葉 module で、EPI 系を一切 import しない。

### docstring の cycle 注記 — verbatim + 実体検証

`EntropyPowerInequality.lean:187-189` (verbatim):
```
(Density-keyed `fisherInfoOfDensityReal` is used here rather than the measure-keyed
`fisherInfoOfMeasureV2` to keep this base file free of an import cycle through
`FisherInfoV2DeBruijn`; the two agree by `fisherInfoOfMeasureV2_def`.)
```

**実体**: この注記は **`FisherInfoV2DeBruijn` 経由の cycle** を警戒している (EPIConvDensity ではない)。確認:
- `fisherInfoOfMeasureV2` は `FisherInfoV2.lean:74` 定義 (`Measure ℝ → (ℝ→ℝ) → ℝ≥0∞`)。`fisherInfoOfDensityReal` は `FisherInfoV2.lean:11-12` (`(f:ℝ→ℝ):ℝ := ∫ x, (deriv f x)^2 / f x`)。両者 **同じ FisherInfoV2 file** にある。
- ではなぜ "cycle through FisherInfoV2DeBruijn"? — measure-keyed `fisherInfoOfMeasureV2 (P.map X)` を **EntropyPowerInequality で genuine に使う**には、`P.map X` の density を取り出す measure-theoretic 補題が必要で、それらが `FisherInfoV2DeBruijn` に集約されている。EntropyPowerInequality (base file, root import :114) が FisherInfoV2DeBruijn (:140, より後) を import すると、**FisherInfoV2DeBruijn → … → EntropyPowerInequality** の逆流 (FisherInfoV2DeBruijn は現状 FisherInfoV2 のみ依存だが、将来 EPI 系補題を引くと cycle) を避けるため、`IsStamInequalityResidual` は density-keyed の自己完結形 `fisherInfoOfDensityReal` を採用した、という設計。
- **EPIConvDensity も同じ理由で安全**: EPIConvDensity → FisherInfoV2 のみ。EntropyPowerInequality が EPIConvDensity を import しても、EPIConvDensity は EntropyPowerInequality を引き返さない。**FisherInfoV2DeBruijn の cycle 警戒線とは独立**。

### cycle 回避策の要否
**不要**。3 述語とも `import InformationTheory.Shannon.EPIConvDensity` を追加して `convDensityAdd` を直接参照でき、cycle は生じない。`IsStamInequalityResidual` は density-keyed (`fisherInfoOfDensityReal fXY`) なので、convolution 制約 `fXY =ᵐ[volume] convDensityAdd fX fY` は `fisherInfoOfDensityReal (convDensityAdd fX fY)` と整合し、FisherInfoV2DeBruijn を経由しないので注記の制約にも抵触しない。

---

## 3. convDensityAdd signature (pivot 制約の型整合)

`EPIConvDensity.lean` 実定義 (verbatim):
```
namespace InformationTheory.Shannon.EPIConvDensity          -- :31
open MeasureTheory Real                                      -- :33
noncomputable def convDensityAdd (pX pY : ℝ → ℝ) : ℝ → ℝ := -- :39
  fun z => ∫ x, pX x * pY (z - x) ∂volume                   -- :40
```

- 型: `convDensityAdd : (ℝ → ℝ) → (ℝ → ℝ) → (ℝ → ℝ)` ✅ ブリーフ想定と一致。
- namespace: `InformationTheory.Shannon.EPIConvDensity` ✅ ブリーフ通り。
- 引数名は `pX pY` (3 述語の `fX fY` と同型 `ℝ → ℝ`)。
- `volume` の扱い: 本体は `∫ x, … ∂volume` と **明示的に `volume` を指定** (Lebesgue on ℝ)。`open MeasureTheory` が namespace 冒頭 `:33` にある。
- pivot 制約 `fXY =ᵐ[volume] InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY` は **型整合する** (`=ᵐ[volume]` = `Filter.EventuallyEq (ae volume)`、両辺 `ℝ → ℝ`)。3 述語 file は `volume` を使うため `MeasureTheory.volume` 完全修飾 or `open MeasureTheory` が要る (EntropyPowerInequality / Step12Body の現 import で `MeasureTheory` は到達可能)。

関連既存 gateway 定理 (pivot で score-of-convolution に使える、全て `@audit:ok` sorryAx-free):
- `convDensityAdd_hasDerivAt` (:65)、`convDensityAdd_logDeriv` (:92)、`convDensity_add_differentiable` (:119) — いずれも regularity precondition (`hs/hF_meas/hF_int/hF'_meas/h_bound/bound_integrable/h_diff` の 7 hyp) を honest に取り、`convDensityAdd` の差分可能性 + `logDeriv` (score) 表現を導く。Blachman route の gateway。

---

## 4. pivot 後「真」になる根拠 (設計妥当性、証明不要)

Stam の数学的内容 = `J(p_X ⋆ p_Y) ≤ harmonic mean`、すなわち optimal CS 形 `J_sum ≤ J_X·J_Y/(J_X+J_Y)` (`IsStamCauchySchwarzOptimal` の結論) / 逆数形 `1/J_sum ≥ 1/J_X + 1/J_Y` (`IsStamInequalityResidual` の結論)。

1. **genuine 化の機序**: 現状の反例 (`fXY=gaussianPDFReal 0 (1/100)`, `J_sum=100`) は「`fXY` が `fX,fY` の convolution でない」ことに依存する。`fXY =ᵐ[volume] convDensityAdd fX fY` を hyp に注入すると、この反例は **排除される** (`convDensityAdd (N(0,1)) (N(0,1)) = N(0,2)`, `J=1/2`, RHS `1/2` で等号 = 真)。任意の `fX,fY` で `J(conv) ≤ harmonic` は Blachman 1965 の真の不等式 → `positivity`/`le_refl` では閉じず Blachman score-of-convolution 恒等式 (Mathlib 未収載、`stam_step2_density_wall` docstring `:287-292` で 0 hit 確認済) を要する。よって `sorry` が honest wall `wall:stam-blachman` (or `wall:stam-step2-density`) に転換。

2. **`IsStamInequalityResidual` × `fisherInfoOfDensityReal` 整合**: `IsStamInequalityResidual` は `fisherInfoOfDensityReal fXY = ∫ (deriv fXY)²/fXY` (`:11-12`) を使う。`convDensityAdd fX fY : ℝ → ℝ` は density を返すので `fisherInfoOfDensityReal (convDensityAdd fX fY)` が型整合 ✅。`fisherInfoOfMeasureV2` を経由しない (= FisherInfoV2DeBruijn 不要) ので import-cycle 注記とも整合。convolution 制約 `fXY =ᵐ convDensityAdd fX fY` から `fisherInfoOfDensityReal fXY = fisherInfoOfDensityReal (convDensityAdd fX fY)` を ae 等値 (deriv/積分の ae 不変性) で導くのは genuine な補題で、Blachman wall に内包される。

3. **`stam_step2_density_wall` が honest wall になる根拠**: 現 docstring (`:342-356`) が「universally FALSE → defect、`@audit:defect(false-statement)`」と自己診断済。pivot で antecedent `IsStamCauchySchwarzOptimal` に convolution 制約が入れば、`:323-326` の反例が消え、`sorry` body は「真だが Mathlib 未収載 Blachman 恒等式」を残すだけ → `@audit:defect(false-statement)` → `@residual(wall:stam-blachman)` に再分類可能。`IsStamCondExpCSHyp` / `IsStamInequalityResidual` も同一反例 (`:265-267`) なので同時 pivot が必要。

設計妥当性: pivot は数学的に正しい (false → true 転換)。3 述語は同一 defect・同一反例を共有し、measure-keyed (Optimal/CondExp) vs density-keyed (Residual) の差を除けば pivot 形は同型。

---

## サマリ — pivot 実装順序の推奨 + cycle リスク + 撤退ライン

### 実装順序 (推奨、producer→consumer 一方向で cycle 無し)
1. **`EPIStamInequalityBody.lean`** (`import InformationTheory.Shannon.EPIConvDensity` 追加): `IsStamCauchySchwarzOptimal` (:269) に `(hconv : fXY =ᵐ[volume] EPIConvDensity.convDensityAdd fX fY)` + density regularity を注入。producer `stam_step2_density_wall` (:359) は `sorry` のまま (false-statement → genuine wall に再分類)。consumer (`stam_inequality_via_predicate_optimal` :387 / `isStamInequalityHyp_via_body` :410 / `_of_optimal` :463 / `_of_lambda_optimal` :503 / `_to_pipeline` :532 / `entropy_power_inequality_via_body` :574) は `intro`/引数に `hconv` 1 つ追加して透過。
2. **`EPIStamStep12Body.lean`** (同 import): `IsStamCondExpCSHyp` (:200) に同制約注入。consumer 6 件 (:215/:227/:234/:257/:278/:299/:313) は `hconv` 透過。`stamCauchySchwarzOptimal_of_condExpCSHyp` (:257) が CondExp→Optimal を繋ぐので両述語の制約が一致している必要あり (同一 `hconv` shape)。
3. **`EntropyPowerInequality.lean`** (同 import): `IsStamInequalityResidual` (:190) に `fXY =ᵐ[volume] convDensityAdd fX fY` 注入 (density-keyed なので `fisherInfoOfDensityReal (convDensityAdd …)` で整合)。consumer (`IsStamToEPIBridge` :208 / `entropy_power_inequality` :261 / `_exp_form` :278 / §D :393 / `EPIPlumbing` :192,:267 / `EPIStamToBridge` :1109) は `hconv` 透過。
4. **transitive consumer** (`EPIStamStep3Body.lean:121` `isStamInequalityHyp_via_step3`、`EPIStamDeBruijnConclusion.lean:169/203`): wall を内部呼出すだけなので、wall signature に `hconv` precondition が増えれば呼出側で供給。

`stam_convex_fisher_bound_gaussian` (`StamGaussianBound.lean:77`) は **別系**、ripple 不要 (3 述語非参照)。

### cycle リスク
**ゼロ。** EPIConvDensity は `FisherInfoV2` のみに依存する葉 module で、EPI 系 file を一切 import しない (root :206 最後尾)。3 述語 file への `import InformationTheory.Shannon.EPIConvDensity` は純粋に additive。docstring `:187-189` の cycle 警戒は **FisherInfoV2DeBruijn** 経由のものでEPIConvDensity とは独立。olean refresh のみ注意 (CLAUDE.md「After upstream edits」)。

### 撤退ライン L-EPIW-3pre-α 該当性
**該当しない (GO 方向)** — cycle が撤退条件なら本 pivot は安全。注意点:
- **3 述語同時 pivot 必須**: `stamCauchySchwarzOptimal_of_condExpCSHyp` (:257) が CondExp→Optimal を繋ぐため、`IsStamCauchySchwarzOptimal` と `IsStamCondExpCSHyp` の `hconv` shape が一致しないと chain が破れる。Residual は density-keyed で他 2 つと Fisher-info keying が異なる (measure-keyed vs density-keyed) ので、`hconv` (`fXY =ᵐ convDensityAdd fX fY`) は共通だが Fisher 引数の bridge (`fisherInfoOfMeasureV2_def` :89) が要る。
- **consumer ripple は小さい**: 全 consumer が 12-arg 透過/丸渡し/record build。`fXY` を instantiate する consumer は皆無 → `hconv` 1 つ追加の機械的 ripple。
- **wall の再分類**: `stam_step2_density_wall` (:359) は現 `@audit:defect(false-statement)`。pivot 後 `@residual(wall:stam-blachman)` (genuine Mathlib wall) に。`stamToEPIBridge_holds` (:223, `@residual(plan:epi-stam-to-conclusion-plan)`) は別 wall で pivot 対象外。

### honesty 所見 (即フラグ)
- 3 述語とも現状 `@audit:defect(false-statement)` 明示済 (tier 5、自己診断済)。pivot は正規の owner-task で、defect の上に積む形ではない。
- **defeq 連鎖の落とし穴**: `IsStamInequalityResidual` (density-keyed) と `IsStamInequalityHyp` (`EPIStamDischarge.lean:100`、measure-keyed `(fisherInfoOfMeasureV2 _ _).toReal`) は `fisherInfoOfMeasureV2_def` 経由で **reducibly defeq** とされ、`EPIStamToBridge.lean:1100-1102` / `EPIStamDischarge.lean:440` / `EPIL3Integration.lean:156` / `EPIStamStep3Body` の `entropy_power_inequality P X Y hX hY hXY h_pipeline.stam` 等で `exact` が この defeq に依存している。Residual だけ pivot して `IsStamInequalityHyp` を pivot しないと **この defeq が破れ**、上記 `exact` が型不一致になる。Residual を pivot するなら `IsStamInequalityHyp` (EPIStamDischarge.lean:100) も同形に pivot するか、bridge を明示補題化する必要がある (ブリーフの 3 述語に `IsStamInequalityHyp` は含まれないが、defeq 連鎖の都合で **第 4 の ripple 対象**になりうる)。
- `IsStamInequalityResidual` の `fisherInfoOfMeasureV2` が measure 引数を無視する設計 (`fisherInfoOfMeasureV2 μ f` が μ に依存しない、docstring `:320-322`) は、measure-keyed 述語 (Optimal/CondExp) でも density が `P.map X` に tie されない第 2 の defect 源。pivot で convolution 制約だけ足しても、measure-keyed 2 述語は「density が P.map に対応」する制約も別途要る (docstring `:335-336` が `+ density regularity tying fX,fY,fXY to pdf(P.map X/Y/(X+Y))` と明記)。density-keyed の Residual はこの第 2 制約が不要 → **Residual の pivot が最も clean**、最初に着手すると良い。
