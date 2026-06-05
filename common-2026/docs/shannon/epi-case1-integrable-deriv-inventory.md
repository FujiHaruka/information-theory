# EPI case-1 `integrable_deriv` — 設計選択 (b) のための API surface 在庫

> 対象: `isDeBruijnRegularityHyp_of_methodX_unitnoise` (`InformationTheory/Shannon/EPICase1RatioLimit.lean:1913`) の `integrable_deriv` フィールド。
> 親 plan: `docs/shannon/epi-case1-debruijn-producer-plan.md`、`@residual(plan:epi-case1-debruijn-producer-plan)`。
> 設計選択 (b): X の precondition を「regular density + bounded derivative」に強化し、`fisherInfoOfDensity_convDensityAdd_le`（PB-2b, 着地済）を直接適用 → 定数 majorant で `IntervalIntegrable`。

## 一行サマリ

設計 (b) の閉じ筋は **API surface としては既存率 ~85%**。最大の朗報は **項目1 の「橋渡し」が新規 bridge 不要**（`fisherInfoOfMeasureV2 _μ f = fisherInfoOfDensity f` が `rfl`、measure 引数は捨てられる → 法則密度の整合 verbatim 確認は **不要**）。残る真の自作要素は **2 件**: (A) `t ↦ J(density_t).toReal` の **t-可測性**（`Measure.integrableOn_of_bounded` が要求、別解析障害）、(B) 各 `t∈[0,T]` で `g_t := gaussianPDFReal 0 t.toNNReal` に対し `IsRegularDensityV2 g_t` + `IsBlachmanConvReady pX g_t` を供給する witness（前者は既存、後者は **pX 側 6 field が producer precondition 強化で要追加**）。**撤退ライン発動: NO**（producer の `@residual` は plan-class、設計 (b) は plan 内 closure ルートであり Mathlib 壁ではない）。最も危険な発見: PB-2b の `IsBlachmanConvReady` は **19 field**、うち pX 側の `int_prod1/2/3`（2D Tonelli, 非分離）等は Gaussian witness では shear 変数変換で閉じたが、**一般 regular pX に対しては Gaussian 限定の closed-form を経由できず**、producer に渡す追加 precondition の field 数が大きい。

---

## 主定理の最終形（再掲）

`integrable_deriv` フィールド (`EPIStamDischarge.lean:282-288` verbatim):

```
integrable_deriv :
  ∀ T : ℝ, 0 < T →
    IntervalIntegrable
      (fun t : ℝ => (1/2)
        * (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2
            (P.map (fun ω => X ω + Real.sqrt t * Z ω)) (density_path t)).toReal)
      volume 0 T
```

producer 文脈 (`EPICase1RatioLimit.lean:1948-1949`):
`density_path t = convDensityAdd pX (gaussianPDFReal 0 t.toNNReal)`、`pX = fun x => ((P.map X).rnDeriv volume x).toReal`。

設計 (b) pseudo-Lean（閉じ筋）:

```lean
intro T hT
-- (0) 橋渡し: fisherInfoOfMeasureV2 _ f = fisherInfoOfDensity f  (rfl)
simp only [fisherInfoOfMeasureV2_def]   -- 整合 verbatim 確認は不要
-- (1) 各 t∈[0,T] で uniform bound:  J(convDensityAdd pX g_t) ≤ J(pX)
--     via fisherInfoOfDensity_convDensityAdd_le  (要 IsRegularDensityV2 pX/g_t, norm, IsBlachmanConvReady pX g_t)
-- (2) 定数 C := (1/2)*(J pX).toReal は h_fisher_X で有限
-- (3) t-可測性 (AEStronglyMeasurable on Ι 0 T)  ← 真の自作 (A)
-- (4) intervalIntegrable_iff + Measure.integrableOn_of_bounded で閉じる
```

---

## API 在庫テーブル

### 項目1. 橋渡し `fisherInfoOfMeasureV2 (P.map ...) (density_path t)` ↔ `fisherInfoOfDensity (density_path t)`

| 概念 | Mathlib/IT API | file:line | 状態 | 設計 (b) での扱い |
|---|---|---|---|---|
| V2 measure-keyed Fisher の def | `InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2` | `FisherInfoV2DeBruijn.lean:81` | ✅ 既存 | `noncomputable def fisherInfoOfMeasureV2 (_μ : Measure ℝ) (f : ℝ → ℝ) : ℝ≥0∞ := fisherInfoOfDensity f`。**measure 引数 `_μ` は捨てられる** |
| unfold lemma | `fisherInfoOfMeasureV2_def` | `FisherInfoV2DeBruijn.lean:90` | ✅ 既存 (`@[entry_point]`) | 結論 verbatim: `fisherInfoOfMeasureV2 μ f = fisherInfoOfDensity f` (`:= rfl`)。型クラス前提なし |

**重大な単純化**: brief 項目1 は「density_path t が P.map(X+√t·Z) の真の密度であることが (b) の隠れた前提」と懸念したが、`fisherInfoOfMeasureV2` の定義が **第1引数 measure を完全に無視** する（`:= fisherInfoOfDensity f`）ため、`integrable_deriv` の integrand は `(1/2)·(fisherInfoOfDensity (density_path t)).toReal` に **rfl で簡約**する。よって **法則と密度の整合性（conv-pin の真偽）は (b) のこのフィールド閉鎖には一切不要**。新規 bridge: **0 本**。

> 注意（誠実性): この「measure 引数を捨てる」設計は意図的（V1 の representative-dependence flaw 回避、`FisherInfoV2.lean:81-88`）。`integrable_deriv` フィールドの値は density witness のみに依存し、それが本当に法則密度かは `density_t_eq` + `reg_at` 側で担保される構造。(b) の閉鎖はこの分離を利用するのみで、退化定義悪用には当たらない（J 値は density witness の解析量として well-defined）。

### 項目2. `fisherInfoOfDensity_convDensityAdd_le`（PB-2b, 単調性の主役）と前提

| 概念 | IT API | file:line | 状態 | 設計 (b) での扱い |
|---|---|---|---|---|
| 単調性 lemma | `fisherInfoOfDensity_convDensityAdd_le` | `EPICase1RatioLimit.lean:1820` | ✅ 着地済 (sorryAx-free) | uniform bound の中核 |

完全 signature (verbatim, `EPICase1RatioLimit.lean:1820-1829`):
```
theorem fisherInfoOfDensity_convDensityAdd_le
    (fX fY : ℝ → ℝ)
    (hregX : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fX)
    (hregY : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2 fY)
    (hnormX : ∫ x, fX x ∂MeasureTheory.volume = 1)
    (hnormY : ∫ x, fY x ∂MeasureTheory.volume = 1)
    (hready : InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady fX fY) :
    (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
        (InformationTheory.Shannon.EPIConvDensity.convDensityAdd fX fY)).toReal
      ≤ (InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity fX).toReal
```
型クラス前提: なし（`fX fY : ℝ → ℝ` のみ、measure 引数なし）。設計 (b) では `fX := pX`, `fY := g_t = gaussianPDFReal 0 t.toNNReal`。

### 項目3. `IsRegularDensityV2 (gaussianPDFReal 0 t)` witness

| 概念 | IT API | file:line | 状態 | 前提 |
|---|---|---|---|---|
| Gaussian regular 密度 witness | `isRegularDensityV2_gaussianPDFReal` | `EPIBlachmanGaussianWitness.lean:283` | ✅ 既存 | `{m : ℝ} {v : ℝ≥0} (hv : v ≠ 0)` → `IsRegularDensityV2 (gaussianPDFReal m v)` |

完全 signature (verbatim):
```
theorem isRegularDensityV2_gaussianPDFReal {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    IsRegularDensityV2 (gaussianPDFReal m v)
```
**前提注意**: `v ≠ 0`（分散正）。設計 (b) では `v = t.toNNReal`、`t > 0` ⇒ `t.toNNReal ≠ 0`（`Real.toNNReal_eq_zero` / `Real.coe_toNNReal` で導出可、producer は既に `EPICase1RatioLimit.lean:1964-1965` で `t.toNNReal = ⟨t, ht.le⟩` を扱っている）。**fX 側（pX）の `IsRegularDensityV2` は producer の一般 pX には成立せず**（差分; → §自作要素）。

`IsRegularDensityV2` の field（`FisherInfoV2.lean:124-138`, verbatim）— pX 側に producer 強化で要求される 6 field:
- `diff : Differentiable ℝ f`
- `pos : ∀ x, 0 < f x`
- `tail_bot : Filter.Tendsto f Filter.atBot (nhds 0)`
- `tail_top : Filter.Tendsto f Filter.atTop (nhds 0)`
- `integrable_deriv : Integrable (deriv f) volume`
- `integral_deriv_eq_zero : ∫ x, deriv f x ∂volume = 0`

### 項目4. 正規化 `∫ pX = 1` / `∫ g_t = 1`

| 概念 | Mathlib/IT API | file:line | 状態 | 設計 (b) での扱い |
|---|---|---|---|---|
| Gaussian 正規化 | `ProbabilityTheory.integral_gaussianPDFReal_eq_one` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:121` | ✅ 既存 | `(μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : ∫ x, gaussianPDFReal μ v x = 1`。`hnormY` 供給 |
| pX 正規化 `∫ pX = 1` | — | — | ❌ 要導出（既存素材あり） | `P.map X = withDensity (ofReal∘pX)` (`hpX_law`, `EPICase1RatioLimit.lean:1927`) + `IsProbabilityMeasure P` から `∫ pX = (P.map X) univ = 1`。10〜20 行 plumbing（`integral_toReal_rnDeriv` / `Measure.integral_toReal_rnDeriv` 系、loogle 要確認） |

正規化 `∫ pX = 1` は producer 内に既存補題なし（grep 0 件）が、`hpX_law` + 確率測度から導出可能。`hnormX` として `fisherInfoOfDensity_convDensityAdd_le` に渡す。

### 項目5. 定数 majorant → IntervalIntegrable

| 概念 | Mathlib API | file:line | 状態 | 設計 (b) での扱い |
|---|---|---|---|---|
| interval ↔ IntegrableOn 橋 | `intervalIntegrable_iff_integrableOn_Ioc_of_le` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:121` | ✅ 既存 | `(hab : a ≤ b) : IntervalIntegrable f μ a b ↔ IntegrableOn f (Ioc a b) μ` |
| interval ↔ IntegrableOn (uIoc) | `intervalIntegrable_iff` | 同 `:85` | ✅ 既存 | `IntervalIntegrable f μ a b ↔ IntegrableOn f (Ι a b) μ`（型クラス前提なし） |
| 有界 majorant → IntegrableOn | `MeasureTheory.Measure.integrableOn_of_bounded` | `Mathlib/MeasureTheory/Integral/IntegrableOn.lean:649` | ✅ 既存 | **`AEStronglyMeasurable f μ` を要求**（下記 verbatim） |
| 有界 majorant (別形) | `MeasureTheory.IntegrableOn.of_bound` | 同 `:174` | ✅ 既存 | `(hs : μ s < ∞) {f} (hf : AEStronglyMeasurable f (μ.restrict s)) (C : ℝ) (hfC : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C)` |
| 定数の interval-integrability | `intervalIntegrable_const` | 同 (IntervalIntegral) `:164` | ✅ 既存 | `[IsLocallyFiniteMeasure μ] {c : E} (hc : ‖c‖ₑ ≠ ⊤ := by finiteness) : IntervalIntegrable (fun _ => c) μ a b` |

`Measure.integrableOn_of_bounded` 完全 signature (verbatim, `:649-652`):
```
lemma Measure.integrableOn_of_bounded {f : α → E} (s_finite : μ s ≠ ∞)
    (f_mble : AEStronglyMeasurable f μ) {M : ℝ} (f_bdd : ∀ᵐ a ∂(μ.restrict s), ‖f a‖ ≤ M) :
    IntegrableOn f s μ
```
（`{α : Type*} [MeasurableSpace α] {μ : Measure α} {E} [NormedAddCommGroup E]` 等の暗黙 instance、`s_finite : μ s ≠ ∞`）

**判定（majorant 経路）**: 定数 `C` で被 majorize するルートは `IntervalIntegrable.mono` では **不可**（`mono` (`:246`) は `[[c,d]] ⊆ [[a,b]]` + `μ ≤ ν` の domain/measure 単調性であって pointwise bound ではない）。正しい経路は **`intervalIntegrable_iff_integrableOn_Ioc_of_le` → `Measure.integrableOn_of_bounded`**。これは **被 majorize 関数 `t ↦ (1/2)·J(density_t).toReal` の `AEStronglyMeasurable` を必須要求**する。

### 項目6. `convDensityAdd` と heat-flow density の整合（conv-pin）

| 概念 | IT API | file:line | 状態 | 設計 (b) での扱い |
|---|---|---|---|---|
| `convDensityAdd` def | `EPIConvDensity.convDensityAdd` | `EPIConvDensity.lean:42` | ✅ 既存 | `fun z => ∫ x, pX x * pY (z - x) ∂volume` |
| conv-pin（density = 法則密度）`pPath_eq_convDensityAdd` | `IsRegularDeBruijnHypV2` 文脈 | `FisherInfoV2DeBruijn.lean:216` 言及 | （別 field） | **項目1 により (b) のこのフィールドには不要**。`reg_at`/`density_t_eq` 側で担保 |

設計 (b) のフィールド閉鎖には conv-pin の真偽は **無関係**（項目1 参照）。conv-pin は `density_t_eq` フィールド（producer `:1962-1966`, 既に `rfl`/NNReal 等式で genuine 充足済）と `reg_at` 側の責務。

---

## 主要前提条件ボックス

- **`fisherInfoOfDensity_convDensityAdd_le` (PB-2b)** — 前提: `IsRegularDensityV2 fX`, `IsRegularDensityV2 fY`, `∫ fX = 1`, `∫ fY = 1`, `IsBlachmanConvReady fX fY`。**型クラス前提なし**。設計 (b) では `fX := pX`（一般 L¹ 密度 → regular でない）が **直接の障害**。
- **`isRegularDensityV2_gaussianPDFReal`** — 前提: `v ≠ 0`。`v = t.toNNReal`, `t > 0` で OK。fY（Gaussian）側はこれで供給。
- **`Measure.integrableOn_of_bounded`** — 前提: `μ s ≠ ∞`（`Ioc 0 T` は volume 有限 OK）, **`AEStronglyMeasurable f μ`**（← t-可測性、真の障害）, `∀ᵐ ‖f‖ ≤ M`（uniform bound から供給）。
- **`integral_gaussianPDFReal_eq_one`** — 前提: `v ≠ 0`。fY 正規化に使用。
- **`IsBlachmanConvReady pX g_t`** — **19 field**（`EPIBlachmanDensity.lean:712-761`）。すべて `Integrable`/有界/正値の regularity field（load-bearing でない、`@audit:ok`）。Gaussian × Gaussian は `isBlachmanConvReady_gaussianPDFReal`（`:344`）で既存だが、**一般 pX × Gaussian の witness は不在**（→ 自作要素・壁列挙）。

---

## 自作が必要な要素（優先度順）

1. **`t`-可測性 `AEStronglyMeasurable (fun t => J(density_t).toReal) (volume.restrict (Ι 0 T))`** — 真の解析障害。`density_t = convDensityAdd pX (gaussianPDFReal 0 t.toNNReal)` の `t`-依存を通した `fisherInfoOfDensity`（lintegral）の `t`-可測性。Mathlib に直接 lemma なし（lintegral の parameter 可測性は `Measurable.lintegral_prod_right` 系が必要だが、被積分関数 `logDeriv (convDensityAdd ...)` の `(t,x)`-jointly measurability が前提）。**工数感: 中〜大（30〜80 行）**。落とし穴: `logDeriv` は `deriv f / f`、`convDensityAdd` の `t`-微分可能性と `t`-連続性を経由する必要。
2. **producer precondition 強化（設計 (b) の本体）** — `X` の入力 precondition に `IsRegularDensityV2 pX`（6 field）+ `IsBlachmanConvReady pX g_t`（pX 側 field）を追加。`fisherInfoOfDensity_convDensityAdd_le` を `fX := pX`, `fY := g_t` で適用するために必須。**工数感: signature 拡張 + witness 供給。`IsBlachmanConvReady pX g_t` の 19 field のうち pX のみに依存する field（`int_fX/bdd_fX/bdd_fX'/int_fisherX`）は precondition、g_t に依存する field（`int_fY/bdd_fY/bdd_fY'/int_fisherY`）は Gaussian で既存導出可、混合 field（`pos_pZ/int_X/int_Y/cond_int/int_W/int_Wsq/int_inner/int_fisherZ/int_prod1/2/3`）は pX × Gaussian の解析が必要で重い**。落とし穴: Gaussian × Gaussian witness（`isBlachmanConvReady_gaussianPDFReal`）は `convDensityAdd_gaussian_closed_form` を経由して混合 field を閉じているが、**一般 pX ではこの closed-form が使えない** → 混合 field は別途 score-of-convolution 解析。
3. **`∫ pX = 1`** — `hpX_law` + `IsProbabilityMeasure P` から導出。**工数感: 小（10〜20 行）**。落とし穴: `withDensity` / `rnDeriv` の `.toReal` 積分と測度 mass の橋渡し（`MeasureTheory.integral_toReal_rnDeriv` 系を loogle 要確認）。
4. **uniform bound の組立** — 各 `t∈[0,T]` で `(1/2)·J(density_t).toReal ≤ (1/2)·J(pX).toReal =: C`、`h_fisher_X` で `C < ∞`。項目2+3 が揃えば 5〜15 行。

---

## Mathlib 壁の列挙（真の不在）

設計 (b) のルート上に **純粋な Mathlib 壁（`@residual(wall:...)` 対象）は無い**。すべて IT 内自作 or producer precondition 強化で閉じる構造。ただし以下 2 点が「IT 不在（一般化された自作要素）」:

- **`@residual` 候補なし（壁ではない）**: `IsBlachmanConvReady pX g_t` の一般 pX × Gaussian witness は IT に不在だが、これは「Mathlib 壁」ではなく **設計 (b) が producer precondition として X 側に bundle する regularity 群**（load-bearing でない、`Integrable`/有界/正値のみ）。よって sorry 化ではなく **precondition 追加で閉じる**のが正道（CLAUDE.md「regularity hyp は precondition なので OK」）。
- **t-可測性（自作要素1）**: Mathlib に「lintegral-defined Fisher の parameter 可測性」直接 lemma は不在。loogle 確認: `Measurable (fun t => ∫⁻ x, ... ∂volume)` 型の汎用補題は `Measurable.lintegral_prod_right'`（`Mathlib/MeasureTheory/Constructions/Prod/Basic.lean`）等の素材はあるが、`logDeriv (convDensityAdd ...)` の joint measurability を組む必要があり **bridge 自作**。これは「壁」ではなく plumbing。

> **shared sorry 補題化**: 不要（設計 (b) は sorry を残さず precondition 強化 + plumbing で閉じる方針のため）。万一 t-可測性が想定外に重い場合のみ、`integrable_deriv` を `sorry + @residual(plan:epi-case1-debruijn-producer-plan)` のまま残す（現状維持）。

loogle 確認結果（壁判定の裏取り）:
- 一般密度の Fisher 単調性 / Blachman: `Found 0 declarations`（Mathlib `fisherInfo`/`Blachman` API は不在、producer docstring `:1877-1879` でも確認済）。これは IT 側の `fisherInfoOfDensity_convDensityAdd_le` で代替済（壁ではない）。

---

## 撤退ラインへの距離

親 plan `docs/shannon/epi-case1-debruijn-producer-plan.md` の `@residual(plan:...)` は **「producer の `integrable_deriv` を plan 内 closure ルートで閉じる」** を意味し、Mathlib 壁宣言ではない（auditor が `:1903` で「Mathlib analytic wall → under-hypothesized に CLASSIFICATION REFINED」と確定済）。

**撤退ライン発動: NO**。

- 設計 (b)（precondition 強化）は plan が用意した正規 closure ルートの一つ。
- producer docstring `:1880-1881` が明示的に「**or a strengthened input-regularity precondition on X (regular density + bounded derivative) so PB-2b applies directly**」を設計 (b) として挙げており、本在庫はそれが API surface 上 **実現可能**（既存率 ~85%）と裏取りした。
- 残障害（t-可測性）は「plan 内 plumbing」であって新規撤退ラインを要しない。万一 t-可測性が 1〜2 週間で閉じない場合のみ、`integrable_deriv` を現状の sorry のまま park 継続（既存撤退口 `@residual(plan:...)` 維持、新規仮説束化は禁止）。

---

## 着手 skeleton

producer 既存ファイル `InformationTheory/Shannon/EPICase1RatioLimit.lean` の `integrable_deriv` フィールド（`:1961` の `?_`）を埋める形。設計 (b) は **producer signature 拡張**を伴うため、新 precondition を追加した producer の skeleton（出だし、20〜30 行）:

```lean
-- (設計 (b): producer に regular-density precondition を追加)
noncomputable def isDeBruijnRegularityHyp_of_methodX_unitnoise
    (X Z_X : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hX : Measurable X) (hZX : Measurable Z_X) (hXZX : IndepFun X Z_X P)
    (hZX_law : P.map Z_X = gaussianReal 0 1)
    (hX_ac : (P.map X) ≪ volume) (h_mom_X : Integrable (fun ω => (X ω) ^ 2) P)
    (h_fisher_X : InformationTheory.Shannon.FisherInfoV2.fisherInfoOfDensity
        (fun x => ((P.map X).rnDeriv volume x).toReal) ≠ ∞)
    -- 設計 (b) 追加 precondition (regularity, NOT load-bearing):
    (hreg_pX : InformationTheory.Shannon.FisherInfoV2.IsRegularDensityV2
        (fun x => ((P.map X).rnDeriv volume x).toReal))
    (hnorm_pX : ∫ x, ((P.map X).rnDeriv volume x).toReal ∂volume = 1)
    (hready_pX : ∀ v : ℝ≥0, v ≠ 0 → InformationTheory.Shannon.EPIBlachmanDensity.IsBlachmanConvReady
        (fun x => ((P.map X).rnDeriv volume x).toReal) (gaussianPDFReal 0 v)) :
    InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z_X P := by
  -- ... (既存 pX 構築は :1921-1959 のまま) ...
  · -- integrable_deriv フィールド (:1967 以降を置換):
    intro T hT
    simp only [InformationTheory.Shannon.FisherInfoV2.fisherInfoOfMeasureV2_def]  -- 橋渡し (項目1)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le]
    refine MeasureTheory.Measure.integrableOn_of_bounded
      (by simp [measure_Ioc_lt_top.ne]) ?_meas
      (M := (1/2) * (fisherInfoOfDensity pX).toReal) ?_bdd
    case _meas => sorry  -- @residual(plan:epi-case1-debruijn-producer-plan) — t-可測性 (自作要素1)
    case _bdd =>
      -- 各 t∈Ioc 0 T で  J(convDensityAdd pX g_t) ≤ J(pX)  via fisherInfoOfDensity_convDensityAdd_le
      sorry  -- uniform bound 組立 (自作要素4; PB-2b 適用)
```

> skeleton 注: 追加 precondition `hready_pX` は X 側の regularity bundle（`Integrable`/有界/正値の 19-field 群を pX × 任意 Gaussian で要求）であり load-bearing でない。実際の producer 改修では `hready_pX` をさらに pX-only field（precondition）と g_t-依存 field（Gaussian witness から導出）に分解するのが望ましい（§自作要素2 の落とし穴参照）。t-可測性の sorry は plan-class residual として正規。
