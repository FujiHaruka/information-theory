# T2-D EPI (Entropy Power Inequality) — Mathlib + InformationTheory 在庫

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 2 — T2-D.
> Entropy Power Inequality」
>
> **Status (2026-05-19)**: Phase 0 (inventory) drafted. EPI 本体 (Cover-Thomas
> 17.7.3) は **Mathlib 完全不在** (entropyPower / Stam / Brunn-Minkowski entropy
> form 全て unknown identifier、`loogle "EntropyPower"` で確認)。本 plan は
> **hypothesis pass-through 形 (L-EPI1+L-EPI2+L-EPI3)** で publish するための
> 在庫精査。
>
> **裏目標**: T2-F 既存 publish (`FisherInfo.lean` の `IsRegularDeBruijnHyp` /
> `deBruijn_identity` / `fisherInfoReal`、L-F1+L-F2 hypothesis pass-through
> 形) を上流として再利用、`fisherInfo` の representative-dependence flaw
> (FisherInfoGaussian の判断ログ参照) を直視せず、**`IsFisherInfoFor μ J`
> 等の predicate を別途立て、`fisherInfo` の値表に踏み込まない**。
>
> **方針**: textbook の 2 経路 (de Bruijn integration / Brunn-Minkowski) のうち
> **de Bruijn 経路**を採用 — 既に `FisherInfo.lean` が de Bruijn signature を
> hypothesis predicate 形で publish 済み、上流接続が直接できる。
> Brunn-Minkowski は T2-E の seed として別途扱う。

## §A — Mathlib 在庫 (確認済 hit / negative)

### A.1 Gaussian distribution (使う側)

| ID | 位置 | full signature | 用途 |
|---|---|---|---|
| `MeasureTheory.gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:?` | `gaussianReal (m : ℝ) (v : ℝ≥0) : Measure ℝ` | EPI の Gaussian saturation case |
| `gaussianReal_conv_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:613` | `theorem gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} : (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | independent sum の law (saturating case 用) |
| `gaussianReal_add_gaussianReal_of_indepFun` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:624` | `theorem ... {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) : P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | Gaussian saturation の rigorous statement |
| `IsProbabilityMeasure` instance for `gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | `instance : IsProbabilityMeasure (gaussianReal m v)` | inference のみ |

### A.2 Independence / sum measurability (再利用)

| ID | 位置 | full signature | 用途 |
|---|---|---|---|
| `ProbabilityTheory.IndepFun` | `Mathlib/Probability/Independence/Basic.lean` | `def IndepFun {Ω : Type*} {β γ : Type*} [_mβ : MeasurableSpace β] [_mγ : MeasurableSpace γ] {_mΩ : MeasurableSpace Ω} (X : Ω → β) (Y : Ω → γ) (μ : Measure Ω) : Prop` | `X ⟂ Y` の標準 |
| `Measurable.add` | `Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean` | `theorem Measurable.add ... : Measurable (fun ω => X ω + Y ω)` | `X + Y` の m-measurability |

### A.3 Real analysis (使う側)

| ID | 位置 | full signature | 用途 |
|---|---|---|---|
| `Real.exp_log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:58` | `theorem exp_log (hx : 0 < x) : exp (log x) = x` | EPI 形 `exp(2h)` ↔ entropy power 変換 |
| `Real.exp_pos` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` | `theorem exp_pos (x : ℝ) : 0 < exp x` | positivity for `entropyPower` |
| `Real.exp_add` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` | `theorem exp_add (x y : ℝ) : exp (x + y) = exp x * exp y` | (任意 / sub-goal で) |
| `Real.exp_le_exp` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` | monotone | corollary 用 |
| `Real.log_le_log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | mono on `(0, ∞)` | corollary 用 |
| `Real.log_mul` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | `log (a * b) = log a + log b` (a, b > 0) | Gaussian closed form 展開時 |

### A.4 Negative results (loogle で確認、Mathlib 不在)

| ID | 検索 | 結論 |
|---|---|---|
| `EntropyPower` | `loogle "EntropyPower"` | unknown identifier → **Mathlib 不在** |
| Stam-like inequality | `rg "Stam"` in `.lake/packages/mathlib/Mathlib/Probability` | 0 hit |
| `entropy_power` / `entropy_power_inequality` | `rg` Mathlib 全体 | 0 hit |
| Brunn-Minkowski (entropy form) | `rg "brunn"` Mathlib | 0 hit |

**結論**: EPI に関係する Fisher info → Stam inequality → de Bruijn integration → EPI の上流チェーンは Mathlib に存在しない。本 plan は **statement-level hypothesis pass-through 形**で publish するしかない。

## §B — InformationTheory 在庫 (再利用予定 / 上流)

### B.1 `DifferentialEntropy.lean` (1010 行、再利用)

| ID | 位置 | full signature | 用途 |
|---|---|---|---|
| `differentialEntropy` | `InformationTheory/Shannon/DifferentialEntropy.lean:42` | `noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` | EPI の `h(·)` の本体 |
| `differentialEntropy_gaussianReal` | `InformationTheory/Shannon/DifferentialEntropy.lean:406` | `theorem (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : differentialEntropy (gaussianReal m v) = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | Gaussian saturation case で EPI 等号性確認 |
| `differentialEntropy_le_gaussian_of_variance_le` | `InformationTheory/Shannon/DifferentialEntropy.lean:510` | (Phase D 主定理) | EPI ↔ Gaussian saturating case の橋渡し (本 plan では使わず) |
| `differentialEntropy_eq_gaussian_iff` | `InformationTheory/Shannon/DifferentialEntropy.lean:659` | (max entropy equality case) | (任意) |

### B.2 `FisherInfo.lean` (236 行、上流 pass-through 接続)

| ID | 位置 | full signature | 用途 (本 plan) |
|---|---|---|---|
| `fisherInfo` | `InformationTheory/Shannon/FisherInfo.lean:58` | `noncomputable def fisherInfo (μ : Measure ℝ) : ℝ≥0∞ := ...` | **本 plan 内では値に踏み込まない** (representative-dependence flaw あり、後続 plan で再定義) |
| `fisherInfoReal` | `InformationTheory/Shannon/FisherInfo.lean:93` | `noncomputable def fisherInfoReal (μ : Measure ℝ) : ℝ := (fisherInfo μ).toReal` | 同上、値依存しない |
| `IsRegularDensity` | `InformationTheory/Shannon/FisherInfo.lean:134` | `structure IsRegularDensity {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (P : Measure Ω) [HasPDF X P volume]` | L-EPI の regularity hypothesis として再利用 |
| `IsRegularDeBruijnHyp` | `InformationTheory/Shannon/FisherInfo.lean:200` | `structure IsRegularDeBruijnHyp {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [HasPDF X P volume] (t : ℝ) : Prop` | EPI の de Bruijn 経路 derivAt-step に上流接続 |
| `deBruijn_identity` | `InformationTheory/Shannon/FisherInfo.lean:223` | `theorem deBruijn_identity ... (h_reg : IsRegularDeBruijnHyp X Z P t) : HasDerivAt (fun s => differentialEntropy (P.map (fun ω => X ω + Real.sqrt s * Z ω))) ((1/2) * (fisherInfo (P.map (fun ω => X ω + Real.sqrt t * Z ω))).toReal) t` | 本 plan の de Bruijn 経路で **statement-level に名前露出のみ** (本体 derivation には使わない) |

**重要**: `fisherInfo` の値表 (`= 1/v` for Gaussian 等) は FisherInfoGaussian で blocked。
本 plan では **`IsFisherInfoFor μ J : Prop`** という abstract predicate で `J` を
hypothesis 側で抱える形にし、`fisherInfo μ` の数値判定には**踏み込まない**。

### B.3 `ParallelGaussian.lean`, `ShannonHartley.lean` (idiom 参考、import なし)

- `parallelGaussianChannel` + L-WF1/L-WF2/L-PG1 の三本立て hypothesis pass-through
  pattern (`docs/shannon/parallel-gaussian-moonshot-plan.md`)
- `bandlimitedAwgnCapacity` + L-SH1/L-SH2/L-SH3 の三本立て (`docs/shannon/`)

これらと同じ流儀で `entropyPower` + `entropy_power_inequality` を 3-hypothesis 形で公開する。

## §C — 本 plan で「自作 / 新定義」になるもの

### C.1 EPI 主定理に必要な定義

| 新定義 | 想定形 | 行数 |
|---|---|---|
| `entropyPower (X : Ω → ℝ) (P : Measure Ω) : ℝ` | `:= Real.exp (2 * differentialEntropy (P.map X))` (1-dim 限定、`(2πe)⁻¹ · exp(2h(X))` の `(2πe)⁻¹` 係数は **省略**、Cover-Thomas 17.7.3 の `N(X)` ではなく `e^{2h(X)}` 形で発信) | ~5-10 |
| `entropyPowerMeasure (μ : Measure ℝ) : ℝ` | `:= Real.exp (2 * differentialEntropy μ)` (measure 側形) | ~5-10 |
| `entropyPower_pos` | `0 < entropyPower X P` | ~3 (`Real.exp_pos`) |
| `entropyPowerMeasure_pos` | `0 < entropyPowerMeasure μ` | ~3 |
| `entropyPower_eq_exp_two_differentialEntropy` (unfold) | rfl-変種 | ~3 |
| `entropyPower_gaussianReal` | `entropyPowerMeasure (gaussianReal m v) = 2 * Real.pi * Real.exp 1 * v` (using `differentialEntropy_gaussianReal`) | ~10-15 |

### C.2 撤退ライン predicate (L-EPI1 / L-EPI2 / L-EPI3 候補)

| predicate | 想定形 | 役割 | discharge plan |
|---|---|---|---|
| `IsEntropyPowerStamHypothesis (X Y : Ω → ℝ) (P : Measure Ω)` | `∃ stamData : ..., StamInequality data` | Stam inequality (`J(X+Y)⁻¹ ≥ J(X)⁻¹ + J(Y)⁻¹`、Fisher info の inverse 形) を hypothesis 化 | Mathlib gap、別 plan `epi-stam-discharge-plan.md` |
| `IsEntropyPowerDeBruijnHypothesis (X Y Z : Ω → ℝ) (P : Measure Ω)` | `∀ t > 0, IsRegularDeBruijnHyp (X+Y) Z P t` | de Bruijn integration を hypothesis 化 (本 plan で同 file の `IsRegularDeBruijnHyp` を再利用) | T2-F `deBruijn_identity` で signature だけ既に提供 |
| `IsEntropyPowerInequalityHypothesis (X Y : Ω → ℝ) (P : Measure Ω)` | `Real.exp (2 * differentialEntropy (P.map (X+Y))) ≥ Real.exp (2 * differentialEntropy (P.map X)) + Real.exp (2 * differentialEntropy (P.map Y))` | **EPI 結論そのもの**を hypothesis bundle 化 | Stam + de Bruijn 積分の合成、別 plan |

**設計判断**: 本 plan は **L-EPI3 statement-level pass-through pattern** で publish する。
L-EPI1+L-EPI2 は signature 露出のみで本体では使わない (T2-B / T2-C / T3-D / T3-F の流儀と同型)。

### C.3 主定理 signature (Cover-Thomas 17.7.3 — Theorem 17.7.3)

```lean
namespace InformationTheory.Shannon.EntropyPowerInequality

/-- L-EPI3: EPI 結論そのものを hypothesis として bundle. 本 plan の核心 retreat. -/
def IsEntropyPowerInequalityHypothesis {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  Real.exp (2 * differentialEntropy (P.map (fun ω => X ω + Y ω)))
    ≥ Real.exp (2 * differentialEntropy (P.map X))
      + Real.exp (2 * differentialEntropy (P.map Y))

theorem entropy_power_inequality {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_epi : IsEntropyPowerInequalityHypothesis X Y P) :
    Real.exp (2 * differentialEntropy (P.map (fun ω => X ω + Y ω)))
      ≥ Real.exp (2 * differentialEntropy (P.map X))
        + Real.exp (2 * differentialEntropy (P.map Y)) :=
  h_epi
```

加えて Cover-Thomas 17.7.3 の **「Gaussian saturation case の equality」** を corollary として publish:

```lean
/-- Gaussian saturation case: 等号成立 (X, Y それぞれが Gaussian なら EPI は等号)。 -/
theorem entropy_power_inequality_gaussian_saturation
    (m₁ m₂ : ℝ) (v₁ v₂ : ℝ≥0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y P)
    (hLawX : P.map X = gaussianReal m₁ v₁) (hLawY : P.map Y = gaussianReal m₂ v₂) :
    Real.exp (2 * differentialEntropy (P.map (fun ω => X ω + Y ω)))
      = Real.exp (2 * differentialEntropy (P.map X))
        + Real.exp (2 * differentialEntropy (P.map Y))
```

→ **これは `gaussianReal_add_gaussianReal_of_indepFun` + `differentialEntropy_gaussianReal`
  + `Real.exp_log` の合成で fully discharge 可能** (Mathlib + InformationTheory 既存 API のみ、~30-60 行)。

## §D — 撤退ライン (採用予定)

### D.1 L-EPI1 (Stam inequality hypothesis)

- **形**: `IsStamInequalityHypothesis X Y P J_X J_Y J_sum : Prop := (1 / J_sum) ≥ (1 / J_X) + (1 / J_Y)` (1-dim, Fisher info inverse formal)
- **適用**: 主定理 signature の `h_stam` 引数 — **本体では使わない**、signature 露出のみ
- **discharge plan**: 別 plan `epi-stam-discharge-plan.md` (Fisher convolution + score variance argument、~500-1000 行)
- **役割**: textbook 完全 derivation pathway を signature に保持

### D.2 L-EPI2 (de Bruijn integration hypothesis)

- **形**: `IsDeBruijnIntegrationHypothesis X Y Z P : Prop := ∀ t ∈ [0, ∞), (heat flow + integration identity)` (T2-F `IsRegularDeBruijnHyp` の `(X+Y) Z` 形 family)
- **適用**: 主定理 signature の `h_debruijn` 引数 — 本体では使わない
- **discharge plan**: 別 plan `epi-debruijn-integration-plan.md` (T2-F 再利用、~300-500 行)
- **役割**: heat flow path から EPI 等価形を取り出す bridge を signature 化

### D.3 L-EPI3 (EPI conclusion hypothesis, **核心**)

- **形**: `IsEntropyPowerInequalityHypothesis X Y P : Prop := exp(2h(X+Y)) ≥ exp(2h(X)) + exp(2h(Y))`
- **適用**: 主定理 signature の `h_epi` 引数 — **主定理本体は `:= h_epi` の 1 行で済む**
- **discharge plan**: L-EPI1 + L-EPI2 の合成、別 plan `epi-stam-to-conclusion-plan.md`
- **役割**: 本 plan の核心 — publish 可能な最短 retreat。L-EPI1+L-EPI2 を signature に保持しつつ、本体は L-EPI3 単独で着地

**adoption**: L-EPI1 + L-EPI2 + L-EPI3 三本立て採用 (T2-B / T2-C / T3-F と同流儀)。
**追加** L-EPI0 (Gaussian saturation case): これは **discharge 可能** (§C.3 §後段の corollary
が `gaussianReal_add_gaussianReal_of_indepFun` + `differentialEntropy_gaussianReal` で
組める) ので **撤退ラインに含めず、本 plan 内で full discharge**。

## §E — リスクテーブル

| # | リスク | 確率 | 影響 | 緩和策 |
|---|---|---|---|---|
| 1 | `entropyPower` 命名衝突 (Mathlib に同名識別子) | 低 | namespace 衝突 | Mathlib 確認済 (`loogle "EntropyPower"` で unknown)、本 plan の namespace `InformationTheory.Shannon.EntropyPowerInequality` 内で定義 |
| 2 | Gaussian saturation case の `Real.exp_log` 引数 vs `Real.log_pos` の取り回しで詰まる | 低 | corollary 規模 +20-30 行 | `2πe v > 0` の positivity を `by positivity` で組む |
| 3 | `IndepFun` 形の `X + Y` vs `fun ω => X ω + Y ω` 形不一致 | 低 | minor compile error | `Pi.add_apply` / `Function.add_def` で正規化 |
| 4 | `IsEntropyPowerInequalityHypothesis` の signature が universe-polymorphic で型ずれ | 低 | minor | `{Ω : Type*}` で統一、`[mΩ : MeasurableSpace Ω]` は明示 |
| 5 | `P.map (X + Y)` と `P.map (fun ω => X ω + Y ω)` の表記揺れで `rw` 不発 | 中 | hypothesis form の微調整必要 | 全て `fun ω => X ω + Y ω` 形で統一 (Mathlib `IndepFun.map_add_eq_map_conv_map₀'` と整合) |

## §F — Skeleton 予想規模

| 要素 | 行数 |
|---|---|
| imports + namespace + docstring | ~80 |
| `entropyPower`, `entropyPowerMeasure` + positivity + unfold + gaussianReal closed form | ~80-120 |
| L-EPI1/L-EPI2/L-EPI3 predicates + docstrings | ~80-100 |
| 主定理 `entropy_power_inequality` (L-EPI3 適用、本体 `:= h_epi`) | ~30-50 |
| **Gaussian saturation case** corollary (full discharge、Mathlib + InformationTheory 既存のみ) | ~50-80 |
| 補助 corollary 群 (monotonicity, multi-arg pass-through, scaling) | ~100-200 |
| 合計 (Tier 2 = 全 corollary 込) | **~420-630** |
| Tier 1 (主定理 + Gaussian sat + α-component) | **~300-450** |

中央予測 **~500 行**。`roadmap` 「~800-1200 行」より小さく着地 (T2-F が独立 publish 済ゆえ、本 plan は EPI 本体に集中可)。

## §G — Skeleton 概形 (Phase A 着手前 reference)

```lean
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.FisherInfo
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

namespace InformationTheory.Shannon.EntropyPowerInequality

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal Topology

/-! ## §A — entropyPower 定義 + 基本性質 -/
noncomputable def entropyPower (μ : Measure ℝ) : ℝ := ...
theorem entropyPower_pos : ... := ...
theorem entropyPower_gaussianReal : ... := ...

/-! ## §B — L-EPI1/2/3 predicates -/
def IsStamInequalityHypothesis ...
def IsDeBruijnIntegrationHypothesis ...
def IsEntropyPowerInequalityHypothesis ...

/-! ## §C — 主定理 (L-EPI3 適用形) -/
theorem entropy_power_inequality ... := h_epi

/-! ## §D — Gaussian saturation case (full discharge) -/
theorem entropy_power_inequality_gaussian_saturation ... := by ...

/-! ## §E — 補助 corollary 群 -/
theorem entropyPower_nonneg ...
theorem entropyPower_eq_iff_gaussian_sat (任意) ...

end InformationTheory.Shannon.EntropyPowerInequality
```

## §H — 判断ログ要点 (Phase 0 確定)

1. **判断 #1**: de Bruijn 経路採用 (vs Brunn-Minkowski 経路)。理由: T2-F
   `IsRegularDeBruijnHyp` + `deBruijn_identity` が既に publish 済 (signature 露出
   形)、Brunn-Minkowski は T2-E seed として独立扱い (Mathlib `Convex` /
   `volume`-form の整備済の度合いに依存)。
2. **判断 #2**: L-EPI1 + L-EPI2 + L-EPI3 三本立て採用。L-EPI3 が核心、本体は
   `:= h_epi`。L-EPI1 + L-EPI2 は signature 露出のみで discharge plan への
   bridge 確保。
3. **判断 #3**: Gaussian saturation case **(L-EPI0 候補)** は **本 plan 内で
   full discharge** (`gaussianReal_add_gaussianReal_of_indepFun` +
   `differentialEntropy_gaussianReal` + `Real.exp_log` 合成で ~50-80 行)。
   撤退ラインに含めない。
4. **判断 #4**: `fisherInfo` の値表 (representative-dependence flaw あり) には
   踏み込まない。`IsFisherInfoFor μ J : Prop := True` 形 abstract predicate も
   一時的に立てるが、本 plan 主定理の signature には登場させない (L-EPI3
   形が `fisherInfo` 露出を一切しないため不要)。
5. **判断 #5**: `entropyPower` の定義は **`Real.exp (2 * differentialEntropy μ)`**
   形を採用 (Cover-Thomas Ch.17 の `N(X) = (2πe)⁻¹ · e^{2h(X)}` ではなく
   `(2πe) · N(X) = e^{2h(X)}` 形)。理由: シード仕様の主定理 signature
   `exp(2 h(X+Y)) ≥ exp(2 h(X)) + exp(2 h(Y))` と直結し、`(2πe)` 倍数の
   付け替えを corollary で扱える (Mathlib-shape-driven)。
