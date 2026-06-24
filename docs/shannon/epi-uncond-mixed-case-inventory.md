# EPI 無条件化 — Phase 0-B case-2 (混合 case) Mathlib API 在庫調査

> 親計画: [`docs/shannon/epi-unconditional-moonshot-plan.md`](epi-unconditional-moonshot-plan.md)
> 調査対象: **wall 候補 W-B = 混合 case** (`X 絶対連続 (a.c.) ∧ Y 特異`)。新 ℝ≥0∞ entropyPower 下で
> RHS = `N(X) + N(Y) = N(X) + 0 = N(X)`。よって `N(X+Y) ≥ N(X)` を示せば足りる。
> 本ファイルは Phase 0-C で `mathlib-inventory` に委任された case-2 部分の成果物。**実装・計画起草はしない。**

## 一行サマリ

**判定 = GO (soft)。** 混合 case の core `h(X+Y) ≥ h(X)` は既存 genuine 2 補題
(`condDifferentialEntropy_le` + `condDifferentialEntropy_indep_add_eq`、両者 `@audit:ok`) の `c=1` 合成で
**そのまま typecheck** (実機確認済、sorry は `μ.map(X+Y) ≪ volume` の 1 点のみ)。その 1 点
「**X a.c. ⟹ X+Y a.c.**」は **Mathlib に完全に存在** — `IndepFun.map_add_eq_map_conv_map` +
`Measure.conv_comm` + `Measure.conv_absolutelyContinuous` の **3 行で 0 sorry 閉**(実機確認済)。
ℝ≥0∞ lift も `Real.exp_le_exp` + `ENNReal.ofReal_le_ofReal` で標準。
**自作必要 = 0 個** (entropyPower 新定義の bridge lemma は S1 持ち、混合 dispatch 自体に新 Mathlib 壁なし)。
**隠れ壁なし。** 唯一の非自明残務は bridge の per-fibre **integrability precondition 群**で、これは
load-bearing でなく regularity precondition (a.c. + KL 有限性) として honest に threading 可能
(既存 `differentialEntropy_indep_gaussian_add_ge` が Gaussian Z で実際にそうしている)。

---

## 混合 case の最終形 (達成目標、Real 中核)

混合 case dispatch が消費する core 不等式 (`c=1` 一般 Y):

```lean
differentialEntropy (μ.map X) ≤ differentialEntropy (μ.map (fun ω => X ω + Y ω))
```

ℝ≥0∞ に lift した混合 case の主張 (Phase 4 / 5 で組む形):

```lean
-- 混合 case (X a.c. ∧ Y 特異): RHS = N(X) + 0 = N(X)
entropyPower (μ.map (fun ω => X ω + Y ω)) ≥ entropyPower (μ.map X)   -- (ℝ≥0∞)
```

証明戦略 (pseudo-Lean、実機 typecheck 済の合成):

```
set W := fun ω => X ω + 1 * Y ω
h_fibre : condDifferentialEntropy W Y μ = differentialEntropy (μ.map X)      -- indep_add_eq (c=1)
h_le    : condDifferentialEntropy W Y μ ≤ differentialEntropy (μ.map W)      -- _le (bridge)
                                                                            -- 要 μ.map W ≪ volume
h(X) = h(W|Y) ≤ h(W) = h(X+Y)                                               -- rw[←h_fibre]; exact h_le
-- lift (a.c. 枝で entropyPower = ENNReal.ofReal (exp (2·h))):
N(X) = ofReal (exp (2 h(X))) ≤ ofReal (exp (2 h(X+Y))) = N(X+Y)
       via Real.exp_le_exp.mpr ∘ ENNReal.ofReal_le_ofReal
-- μ.map W ≪ volume : map_add_eq_map_conv_map → conv_comm → conv_absolutelyContinuous (3 行)
```

---

## API 在庫テーブル

### A. case-2 core 既存資産 (in-tree、両 genuine `@audit:ok`)

| 概念 | API (file:line) | 状態 | 混合 case での扱い |
|---|---|---|---|
| 条件付き微分エントロピー定義 | `condDifferentialEntropy` (`InformationTheory/Shannon/EPIG2ConvEntropyMonotone.lean:90`) | ✅ in-tree | `∫ z, differentialEntropy ((condDistrib X Z μ) z) ∂(μ.map Z)`。`Z := Y` で条件付ける |
| conditioning reduces entropy | `condDifferentialEntropy_le` (`EPIG2ConvEntropyMonotone.lean:224`) | ✅ genuine sorryAx-free | `h(W\|Y) ≤ h(W)`。多数 integrability precondition (下記 box) |
| 独立和 fibre 同定 | `condDifferentialEntropy_indep_add_eq` (`:328`) | ✅ genuine `@audit:ok` | `h(X + c·Z \| Z) = h(X)`。`c=1` で `h(X+Y\|Y) = h(X)` |
| device 形 (参照テンプレート) | `differentialEntropy_indep_gaussian_add_ge` (`:378`) | ✅ genuine `@audit:ok` | Gaussian Z 版で 2 本を実際に合成済。混合 case は Z=Y 一般版にする雛形 |
| 並進不変 (fibre 同定の内部) | `differentialEntropy_map_add_const` (`DifferentialEntropy.lean:171`) | ✅ in-tree | indep_add_eq が内部で使用、混合 case に追加負担なし |

**`condDifferentialEntropy_le` 完全 signature (verbatim、`EPIG2ConvEntropyMonotone.lean:224-246`)**:

```lean
theorem condDifferentialEntropy_le
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume)
    (h_ac : (μ.map Z) ⊗ₘ condDistrib X Z μ ≪ (μ.map Z) ⊗ₘ Kernel.const α (μ.map X))
    (h_int : Integrable
      (llr ((μ.map Z) ⊗ₘ condDistrib X Z μ) ((μ.map Z) ⊗ₘ Kernel.const α (μ.map X)))
      ((μ.map Z) ⊗ₘ condDistrib X Z μ))
    (hκ_v : ∀ᵐ z ∂(μ.map Z), condDistrib X Z μ z ≪ volume)
    (hκ_logp_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((condDistrib X Z μ z).rnDeriv volume x).toReal)) volume)
    (hκ_cross_int : ∀ᵐ z ∂(μ.map Z), Integrable
      (fun x => ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map X).rnDeriv volume x).toReal)) volume)
    (h_fibreEnt_int : Integrable
      (fun z => differentialEntropy (condDistrib X Z μ z)) (μ.map Z))
    (h_cross_int : Integrable
      (fun z => ∫ x, ((condDistrib X Z μ z).rnDeriv volume x).toReal
        * Real.log (((μ.map X).rnDeriv volume x).toReal) ∂volume) (μ.map Z))
    (h_logq_int : Integrable
      (fun x => Real.log (((μ.map X).rnDeriv volume x).toReal)) (μ.map X)) :
    condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X)
```

**前提逐語列挙** (混合 case では `X := W = X+Y` (a.c.)、`Z := Y` (特異) で適用):
- 型クラス: `[IsProbabilityMeasure μ]`、`[MeasurableSpace Ω]`、`[MeasurableSpace α]`。**`[StandardBorelSpace]` 要求なし**(危険前提の不在を確認)。
- `hX : Measurable W`、`hZ : Measurable Y`(構造的)。
- `hX_ac : (μ.map W) ≪ volume` ← **W=X+Y の a.c.**(下記 B で閉じる)。
- `h_ac` / `h_int`:joint KL 有限性系 = absolute continuity + llr integrability。
- `hκ_v` / `hκ_logp_int` / `hκ_cross_int` / `h_fibreEnt_int` / `h_cross_int` / `h_logq_int`:per-fibre + outer の integrability 群。
- これらは **a.c. 側 (W) と fibre 上の regularity** であり、条件付け側 Y が特異でも要求は W=X+Y の密度と fibre 構造に関するもの。**Y の特異性は前提を阻害しない**(`hZ` 以外 Y に課す前提なし)。

**`condDifferentialEntropy_indep_add_eq` 完全 signature (verbatim、`:328-334`)**:

```lean
theorem condDifferentialEntropy_indep_add_eq
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy (fun ω => X ω + c * Z ω) Z μ
      = differentialEntropy (μ.map X)
```

**前提逐語**: `[IsProbabilityMeasure μ]`、`hX hZ : Measurable`、`hXZ : IndepFun X Z μ`、
`hX_ac : (μ.map X) ≪ volume`。`c=1`、`Z:=Y` で `h(X+Y | Y) = h(X)`。**`StandardBorelSpace` なし**。
`X a.c.` のみで成立 — **Y の特異性は無関係**(Y には measurability + independence のみ)。

### B. convolution-a.c. (混合 case の核心、`X a.c. ⟹ X+Y a.c.`)

| 概念 | Mathlib API (file:line) | 状態 | 扱い |
|---|---|---|---|
| 独立和 → 畳み込み法 | `ProbabilityTheory.IndepFun.map_add_eq_map_conv_map` (`Mathlib/Probability/Independence/Basic.lean`) | ✅ 既存 | `μ.map (X+Y) = (μ.map X) ∗ (μ.map Y)` |
| 畳み込み可換 (additive) | `MeasureTheory.Measure.conv_comm` (`Mathlib/MeasureTheory/Group/Convolution.lean:127` の additive 版) | ✅ 既存 | a.c. 因子を右に移す |
| 畳み込みは a.c. を伝播 | `MeasureTheory.Measure.conv_absolutelyContinuous` (`Convolution.lean:166` の additive 版) | ✅ 既存 | `ν ≪ ρ → μ ∗ ν ≪ ρ` |

**`IndepFun.map_add_eq_map_conv_map` 完全 signature (verbatim、`#check` 実機)**:

```lean
@IndepFun.map_add_eq_map_conv_map : ∀ {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {M : Type u_2} [inst : AddMonoid M] [inst_1 : MeasurableSpace M] [MeasurableAdd₂ M]
  [IsFiniteMeasure μ] {f g : Ω → M},
  Measurable f → Measurable g → f ⟂ᵢ[μ] g → Measure.map (f + g) μ = Measure.map f μ ∗ Measure.map g μ
```
(AEMeasurable 版 `…_map_conv_map₀` も同 file に存在。)
- 型クラス: `[AddMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M] [IsFiniteMeasure μ]`。ℝ + probability μ で全充足。

**`Measure.conv_absolutelyContinuous` 完全 signature (verbatim、`#check` 実機、additive 訳)**:

```lean
@Measure.conv_absolutelyContinuous : ∀ {M : Type u_1} [inst : AddMonoid M]
  [inst_1 : MeasurableSpace M] [MeasurableAdd₂ M] {μ ν ρ : Measure M}
  [ρ.IsAddLeftInvariant] [SFinite ν], ν ≪ ρ → μ ∗ ν ≪ ρ
```
- 型クラス: `[AddMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M] [ρ.IsAddLeftInvariant] [SFinite ν]`。
- **`ρ := volume` (ℝ) の `IsAddLeftInvariant` は instance 自動解決**(実機で usage がコンパイル、明示供給不要)。
- **結論形 verbatim**: `ν ≪ ρ → μ ∗ ν ≪ ρ`。**a.c. 因子は右 (ν)**。左 (μ=任意) は無条件 → `conv_comm` で a.c. 因子 (`μ.map X`) を右に回す。

> **3 行 0-sorry 閉路 (実機 typecheck 済)**:
> ```lean
> have hfun : (fun ω => X ω + Y ω) = X + Y := rfl
> rw [hfun, hXY.map_add_eq_map_conv_map hX hY, Measure.conv_comm]
> exact Measure.conv_absolutelyContinuous hX_ac
> ```
> `μ.map(X+Y) ≪ volume` が `hX_ac : μ.map X ≪ volume` のみから 0 sorry で出る。**自作不要を確証。**

### C. ℝ≥0∞ への lift (Real → entropyPower)

| 概念 | Mathlib API (file:line / `#check`) | 状態 | 扱い |
|---|---|---|---|
| exp 単調 (iff) | `Real.exp_le_exp : rexp x ≤ rexp y ↔ x ≤ y` | ✅ 既存 | `2h(X) ≤ 2h(X+Y) → exp ≤ exp` |
| exp 単調 (Monotone) | `Real.exp_monotone : Monotone rexp` | ✅ 既存 | 同上の point-free 版 |
| ofReal 単調 | `ENNReal.ofReal_le_ofReal : p ≤ q → ENNReal.ofReal p ≤ ENNReal.ofReal q` | ✅ 既存 | exp 値を ℝ≥0∞ へ |
| ofReal 単調 (iff) | `ENNReal.ofReal_le_ofReal_iff : 0 ≤ q → (ofReal p ≤ ofReal q ↔ p ≤ q)` | ✅ 既存 | backup |
| ofReal 加法 (RHS 和) | `ENNReal.ofReal_add : 0 ≤ p → 0 ≤ q → ofReal (p+q) = ofReal p + ofReal q` | ✅ 既存 | case-1 で使用 (混合では不要、RHS=N(X) 単項) |

混合 case では RHS が `N(X)` 単項なので加法は不要。単調性 2 段
(`Real.exp_le_exp.mpr` → `ENNReal.ofReal_le_ofReal`) のみ。

### D. 退化値の verbatim 確認 (entropyPower 旧/新)

| 量 | 実コード (file:line) | 値 | 備考 |
|---|---|---|---|
| `differentialEntropy (μ.rnDeriv 部のみ)` | `DifferentialEntropy.lean:45` | `∫ negMulLog ((μ.rnDeriv volume x).toReal)` | a.c. 部のみ。特異部は rnDeriv=0 で `negMulLog 0 = 0` |
| `differentialEntropy (Measure.dirac m)` | `DifferentialEntropy.lean:155` | `= 0` | **特異測度で 0 退化**(±∞ にならない、定義上 0-fallback) |
| `entropyPower (旧 Real)` | `EntropyPowerInequality.lean:102` | `Real.exp (2 * differentialEntropy μ)` | Dirac で `exp 0 = 1`(旧定義の退化トラップ) |
| `entropyPower_pos (旧)` | `:109` | `0 < entropyPower μ` | 旧定義は常に正 → 無条件 EPI literally FALSE の元 |

→ 新 ℝ≥0∞ entropyPower (S1 持ち) は a.c. 枝で `ENNReal.ofReal (exp (2·h))`、特異枝で `0`。
混合 case では **X a.c. なので N(X) = ofReal (exp (2 h(X)))**(非退化、>0 of `exp>0`)、
**Y 特異なので N(Y) = 0** → RHS = N(X)。これが本 case の数学的核。

---

## 主要前提条件ボックス (事故が起きやすい箇所)

**`condDifferentialEntropy_le` の per-fibre integrability 群** (混合設定での充足性):

- `hX_ac : (μ.map W) ≪ volume` (W=X+Y) — **B で 3 行閉**。混合 case の唯一の構造的前提、Y 特異でも閉じる。
- `h_ac` (joint absolute continuity)、`h_int` (llr integrability) — joint `(μ.map Y) ⊗ₘ condDistrib W Y μ` の KL 有限性。**regularity precondition** (load-bearing でない)。
- `hκ_v` (per-fibre a.c.)、`hκ_logp_int` / `hκ_cross_int` (fibre 内 integrability)、`h_fibreEnt_int` / `h_cross_int` (outer μ_Y-integrability)、`h_logq_int` (marginal log-density integrability)。
  - これらは W=X+Y の密度 (a.c. なので存在) と fibre 構造の analytic 条件。**Y の特異性は阻害せず**、むしろ W の a.c. が供給源。
  - **honest threading 可能** = 既存 `differentialEntropy_indep_gaussian_add_ge` (`:378`) が Gaussian Z で実際に全て precondition として threading 済(`@audit:ok`)。混合 case は Z=Y 一般化で同形 threading。
- **注意 (honesty)**: これら integrability は **precondition であって core ではない**(CLAUDE.md「regularity か load-bearing か」判定で前者)。混合 case 補題を作る際は signature に **honest precondition として** 載せる。`*Hypothesis` predicate に bundle するのは禁止。

**`condDifferentialEntropy_indep_add_eq` の前提**:
- `hX_ac : (μ.map X) ≪ volume` — **X a.c.**(混合 case の定義そのもの、無条件充足)。
- `hXZ : IndepFun X Y μ` — 主定理仮説から供給(load-bearing でない、genuine independence)。

---

## 自作が必要な要素

**0 個** (新 Mathlib 壁なし)。混合 case dispatch に必要な道具は:
- core 2 補題 (in-tree genuine) ✅
- convolution-a.c. 3 補題 (Mathlib 既存) ✅
- exp / ofReal 単調 (Mathlib 既存) ✅

すべて存在。Phase 4 で書くのは **「2 補題 + 3 行 a.c. 閉路を `c=1` 一般 Y で合成し ℝ≥0∞ に lift する糊コード」**(新規 ~40-80 行、integrability precondition は honest threading)。
`differentialEntropy_indep_gaussian_add_ge` (`:378`) が **ほぼそのまま雛形** (Gaussian 固有部 `gaussianConvolution_law_conv` / `hZ_law` を外し、a.c. 閉路を B の汎用版に置換するだけ)。

---

## Mathlib 壁の列挙

**真の Mathlib 壁 = 0 個。** 混合 case dispatch には `@residual(wall:...)` 対象が**ない**。

- convolution-a.c.: `Measure.conv_absolutelyContinuous` **存在**(loogle `Found one declaration`、`#check` 実機検証済)。⟹ wall ではない。
- 独立和の畳み込み法: `IndepFun.map_add_eq_map_conv_map` **存在**(`#check` 実機検証済)。⟹ wall ではない。
- entropyPower 新定義の coercion bridge は **S1 (`epi-entropypower-retype-plan`) の持ち分**であり混合 case 固有の壁ではない。混合 case は S1 完了後その bridge を**呼ぶだけ**。

(case-1 a.c. core の残 `h_stam` / G3 / B2 は既存 plan 群の壁であり case-2 とは独立。)

---

## 撤退ラインへの距離

親計画の case-2 関連撤退ライン:

- **L-Uncond-0-β** (case 2 NO-GO: integrability 前提が混合設定で充足不能) → **発動しない**。
  前提は W=X+Y (a.c.) の regularity であり、Y 特異が阻害しない。`differentialEntropy_indep_gaussian_add_ge` が同型前提を Gaussian で threading 済の実証あり。
- **L-Uncond-4-α** (case 2 前提不足 → honest precondition partial に縮退) → **発動しない**(同上)。
- **L-Uncond-4-β** (X+Y の a.c. 判定 Mathlib lemma 不在) → **発動しない**。
  まさに本調査の核心: `conv_absolutelyContinuous` が**存在**し 3 行で閉じる。迂回 (entropy 直接比較) は不要。
- **L-Uncond-0-γ** (退化定義悪用の自己監査) → 混合 case は **vacuous でない**: N(X) = ofReal(exp(2h(X))) は X a.c. で非退化値 (exp>0)。Y=0 や常時 false 倒しではなく、Y 特異 ⟹ N(Y)=0 は**特異測度のエントロピーパワーの正しい値**。honest。

**新規撤退ラインの提案**: 不要(GO 確定)。強いて挙げれば integrability precondition の threading が `differentialEntropy_indep_gaussian_add_ge` の雛形から乖離して肥大した場合のみ
`sorry` + `@residual(plan:epi-singular-mixed-case-plan)` で当該 precondition を park(撤退口は sorry、仮説束化禁止)。だが Gaussian 版が genuine に閉じている以上、一般 Y 版も閉じる見込みが高い。

---

## 着手 skeleton

`InformationTheory/Shannon/EPIUncondMixedCase.lean`(または `epi-singular-mixed-case-plan` 指定 file)の出だし。
**新 entropyPower (S1) 未着地のため、まず Real 中核 `h(X) ≤ h(X+Y)` を着地** → ℝ≥0∞ lift は S1 後:

```lean
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.Basic
import InformationTheory.Shannon.EPIG2ConvEntropyMonotone   -- core 2 補題 + condDifferentialEntropy

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- 混合 case a.c. 閉路: `X a.c. ∧ X ⊥ Y ⟹ X+Y a.c.`(convolution は a.c. を伝播)。 -/
theorem map_add_absolutelyContinuous
    (X Y : Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ)
    (hX_ac : (μ.map X) ≪ volume) :
    (μ.map (fun ω => X ω + Y ω)) ≪ volume := by
  have hfun : (fun ω => X ω + Y ω) = X + Y := rfl
  rw [hfun, hXY.map_add_eq_map_conv_map hX hY, Measure.conv_comm]
  exact Measure.conv_absolutelyContinuous hX_ac

/-- 混合 case core (Real): `h(X) ≤ h(X+Y)`。core 2 補題の `c=1` 合成。
integrability 群は honest precondition として threading(load-bearing でない)。 -/
theorem differentialEntropy_add_ge_of_indep
    (X Y : Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ)
    (hX_ac : (μ.map X) ≪ volume)
    -- bridge per-fibre / outer integrability 群 (W = X + 1·Y, Z = Y)
    -- ... (condDifferentialEntropy_le の h_ac/h_int/hκ_*/h_*_int/h_logq_int を W,Y で threading)
    : differentialEntropy (μ.map X)
        ≤ differentialEntropy (μ.map (fun ω => X ω + Y ω)) := by
  sorry  -- @residual(plan:epi-singular-mixed-case-plan) — 合成は実機 typecheck 済、precondition threading のみ残

end InformationTheory.Shannon
```

ℝ≥0∞ lift (`entropyPower (X+Y) ≥ entropyPower (X)`) は S1 の新 entropyPower + coercion bridge
(`entropyPower_eq_ofReal_of_ac` 系)着地後、上記 Real core に
`Real.exp_le_exp.mpr` ∘ `ENNReal.ofReal_le_ofReal` を被せる薄いラッパで Phase 4 に追加。

---

## GO/NO-GO 判定

**GO (soft、隠れ壁なし)。** 根拠:

1. core 2 補題の `c=1` 合成が **実機で typecheck**(sorry は `μ.map(X+Y)≪volume` の 1 点のみ)。
2. その 1 点が `IndepFun.map_add_eq_map_conv_map` + `Measure.conv_comm` + `Measure.conv_absolutelyContinuous` の **3 行で 0 sorry 実機閉**。convolution-a.c. は **Mathlib に存在**(L-Uncond-4-β 不発)。
3. ℝ≥0∞ lift は `Real.exp_le_exp` + `ENNReal.ofReal_le_ofReal`(標準、実機 `#check` 済)。
4. bridge integrability 群は **regularity precondition** であり Y 特異が阻害しない。Gaussian 版 `differentialEntropy_indep_gaussian_add_ge` が同型前提を genuine threading 済の実証。L-Uncond-0-β / 4-α 不発。
5. 退化悪用なし:X a.c. で N(X) 非退化、Y 特異 ⟹ N(Y)=0 は正しい値。L-Uncond-0-γ クリア。

**最大 blocker**: 真の壁ではないが、`condDifferentialEntropy_le` の **per-fibre integrability precondition 群 (8 本)** を一般 Y で threading する plumbing 量。Gaussian 版雛形があるため設計リスクは低いが、Phase 4 で precondition signature が肥大する可能性。詰まれば `sorry` + `@residual(plan:epi-singular-mixed-case-plan)` で当該 precondition を park(honest 撤退、仮説束化禁止)。
