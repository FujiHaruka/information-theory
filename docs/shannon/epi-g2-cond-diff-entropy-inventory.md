# EPI G2 — 条件付き differential entropy 分解 API 在庫調査

> 親計画: [`docs/shannon/epi-g2-general-sandwich-moonshot-plan.md`](epi-g2-general-sandwich-moonshot-plan.md)
> 対象: `InformationTheory/Shannon/EPIG2ConvEntropyMonotone.lean` の 2 つの `sorry + @residual(wall:cond-diff-entropy)` 補題の genuine 化
> 調査日: 2026-06-04（loogle index `2026-05-10`、Mathlib pin = `.lake/packages/mathlib`）

## 一行サマリ

**Phase 1 (β) の 2 補題が要求する API のうち、低レベル primitive（`condDistrib`・disintegration・KL・IndepFun・`Kernel.map`・`compProd`・shift 不変性）は実体ベースでほぼ 100% 既存。ただし「2 つの高レベル橋」だけが Mathlib 不在：(1) 連続版相互情報量 `I(X;Z) = h(X) − h(X|Z)` の差分形（`mutualInfo` は `Found 0`、差分=KL 等式も不在）、(2) z 依存アフィン kernel `κ z := (μ.map X).map (· + c·z)` を `(μ.map Z)⊗ₘκ` として組む compProd 同定（off-the-shelf なし、組立は可能）。** 補題 2（fibre 同定）は **buildable**（部品完備、自作 plumbing のみ）。補題 1（conditioning reduces）は **部分的**（KL 非負は型で自明だが、KL ↔ differential entropy 差分の橋が真壁＝自作必須）。自作必要要素 5 件。撤退ライン発動 = **no**（最も近い L 線にも触れない）。

---

## 主定理の最終形（再掲）

`EPIG2ConvEntropyMonotone.lean:88-94`（補題 1）・`:121-129`（補題 2）。両者とも現状 `sorry`。

```lean
-- 補題 1: conditioning reduces entropy
theorem condDifferentialEntropy_le
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z) (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy X Z μ ≤ differentialEntropy (μ.map X)

-- 補題 2: independent-sum fibre identification
theorem condDifferentialEntropy_indep_add_eq
    {Ω : Type*} [MeasurableSpace Ω] (X Z : Ω → ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy (fun ω => X ω + c * Z ω) Z μ
      = differentialEntropy (μ.map X)
```

定義（同 file `:72-75`）:
```lean
noncomputable def condDifferentialEntropy
    {Ω α} [MeasurableSpace Ω] [MeasurableSpace α]
    (X : Ω → ℝ) (Z : Ω → α) (μ : Measure Ω) [IsFiniteMeasure μ] : ℝ :=
  ∫ z, differentialEntropy ((condDistrib X Z μ) z) ∂(μ.map Z)
```

証明戦略 pseudo-Lean（補題 2、buildable 経路）:
```
-- joint を product 経由でアフィン写像 g(z,x)=(z, x+c·z) の押し出しに
have hjoint : μ.map (fun ω => (Z ω, X ω + c·Z ω))
            = ((μ.map Z).prod (μ.map X)).map g       -- indepFun_iff_map_prod + map_map
-- product を z 依存アフィン kernel の compProd に書換
have hcp : ((μ.map Z).prod (μ.map X)).map g
         = (μ.map Z) ⊗ₘ κ  where κ z := (μ.map X).map (· + c·z)  -- ★自作 plumbing
-- 一意性: condDistrib (X+c·Z) Z μ =ᵐ κ
have hae := condDistrib_ae_eq_of_measure_eq_compProd Z hAEmeas (hjoint.trans hcp)
-- fibre 各点で shift 不変性 → h(X)
calc ∫ z, h(condDistrib ... z) ∂μ_Z
   = ∫ z, h((μ.map X).map (· + c·z)) ∂μ_Z   -- hae で書換 (integral_congr_ae)
   = ∫ z, h(μ.map X) ∂μ_Z                   -- differentialEntropy_map_add_const (各 z)
   = h(μ.map X)                             -- integral_const, IsProbabilityMeasure μ_Z
```

---

## 群 1 — condDistrib 基盤と disintegration

> source: `Mathlib/Probability/Kernel/CondDistrib.lean`。namespace `ProbabilityTheory`。

### ★引数順・型クラス前提（verbatim 確認、最重要）

ファイル冒頭 variable block（`:54-56`）verbatim:
```
variable {α β Ω F : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [Nonempty Ω] [NormedAddCommGroup F] {mα : MeasurableSpace α} {μ : Measure α}
  [IsFiniteMeasure μ] {X : α → β} {Y : α → Ω}
```

def 本体（`:64-66`）verbatim:
```lean
noncomputable irreducible_def condDistrib {_ : MeasurableSpace α} [MeasurableSpace β]
    (Y : α → Ω) (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : Kernel β Ω :=
  (μ.map fun a => (X a, Y a)).condKernel
```

**引数順 = `condDistrib Y X μ`（"Y given X"、出力側 Y が第 1 引数）。** in-tree def は `condDistrib X Z μ` と呼んでいるので Mathlib 側へは `Y := X, X := Z` で対応する：
- 出力側 `Ω`-role = in-tree の `X : Ω → ℝ` → codomain `ℝ` → `[StandardBorelSpace ℝ] [Nonempty ℝ]` 自動成立 ✅
- 条件付け側 `β`-role = in-tree の `Z : Ω → α` → codomain `α` → StandardBorel **不要**
- `μ` には `[IsFiniteMeasure μ]`（in-tree は `IsProbabilityMeasure` で strictly stronger、OK）

→ **fano Phase 3 と同じ「StandardBorel は出力側に課されるが、出力が `ℝ` なので自動」構造。in-tree signature の型クラス前提は honest（drift なし）。**

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| 正則条件付き分布 | `condDistrib (Y : α → Ω) (X : α → β) (μ : Measure α) : Kernel β Ω`、前提 `[MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] {mα : MeasurableSpace α} [MeasurableSpace β] [IsFiniteMeasure μ]` | `CondDistrib.lean:64` | ✅ 既存 | in-tree def の中核。引数順 `Y X μ` |
| Markov kernel instance | `instance [MeasurableSpace β] : IsMarkovKernel (condDistrib Y X μ)` | `CondDistrib.lean:68` | ✅ 既存 | 各 fibre が確率測度（fibre h 積分の well-def 化に使用） |
| disintegration 等式 | `compProd_map_condDistrib (hY : AEMeasurable Y μ) : (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)` | `CondDistrib.lean:82` | ✅ 既存 | 向き = `(μ.map X) ⊗ₘ condDistrib = μ.map (X,Y)`（条件付け側 X が左因子） |
| 一意性（可測版） | `condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (hX : Measurable X) (hY : Measurable Y) {κ : Kernel β Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ) : condDistrib Y X μ =ᵐ[μ.map X] κ` | `CondDistrib.lean:147` | ✅ 既存 | **補題 2 の心臓**。joint を compProd で書ければ condDistrib = その kernel a.e. |
| 一意性（AEMeasurable 版） | `condDistrib_ae_eq_of_measure_eq_compProd (X : α → β) (hY : AEMeasurable Y μ) {κ : Kernel β Ω} [IsFiniteKernel κ] (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ) : condDistrib Y X μ =ᵐ[μ.map X] κ` | `CondDistrib.lean:163` | ✅ 既存 | 同上の弱前提版（`X` は明示引数、`Y` のみ AEMeasurable で可） |
| 一意性 iff | `condDistrib_ae_eq_iff_measure_eq_compProd (X : α → β) (hY : AEMeasurable Y μ) (κ : Kernel β Ω) [IsFiniteKernel κ] : (condDistrib Y X μ =ᵐ[μ.map X] κ) ↔ μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ` | `CondDistrib.lean:177` | ✅ 既存 | 必要なら双方向 |
| 点評価 | `condDistrib_apply_of_ne_zero [MeasurableSingletonClass β] (hY : Measurable Y) (x : β) (hX : μ.map X {x} ≠ 0) (s : Set Ω) : condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s)` | `CondDistrib.lean:75` | ✅ 既存 | `[MeasurableSingletonClass β]` 要求（連続 Z では不使用） |
| 可測性 | `measurable_condDistrib (hs : MeasurableSet s) : Measurable[mβ.comap X] fun a => condDistrib Y X μ (X a) s` | `CondDistrib.lean:107` | ✅ 既存 | fibre 積分の可測性に補助 |
| condDistrib of independent pair (= const kernel) | — | — | ❌ **Found 0** (`condDistrib (Kernel.const _ _)` パターン 0 match) | 独立時 `condDistrib X Z μ = const (μ.map X)` の既製補題なし。補題 2 では一意性経由で迂回 |

**所見**: 群 1 は補題 1・2 の土台として完備。disintegration（`compProd_map_condDistrib`）と一意性（`condDistrib_ae_eq_of_measure_eq_compProd`）が両方あり、in-tree def の型クラス前提も honest。**真壁なし。** 注意点 1 つ：disintegration の向きは `(μ.map X) ⊗ₘ condDistrib Y X μ`（条件付け側が左因子）なので、補題 2 で組む joint も `μ.map (fun ω => (Z ω, X+c·Z ω))`（**Z が第 1 座標**）の順に揃える必要がある。in-tree def の `condDistrib X Z μ` ↔ Mathlib `Y:=X, X:=Z` 対応下で左因子 = `μ.map Z`、これは docstring の経路記述と整合。

---

## 群 2 — 相互情報量 / KL non-negativity bridge（補題 1 用）

> source: `Mathlib/InformationTheory/KullbackLeibler/{Basic,ChainRule}.lean`。namespace `InformationTheory`。

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| 連続版相互情報量 `mutualInfo` | — | — | ❌ **Found 0**（`"mutualInfo"` 名前検索 / `mutualInfo` 識別子検索とも 0） | **真壁**。`I(X;Z)` 概念が Mathlib に存在しない |
| KL ダイバージェンス | `klDiv (μ ν : Measure α) : ℝ≥0∞ := if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) else ∞` | `KullbackLeibler/Basic.lean:57` | ✅ 既存 | **`ℝ≥0∞`-valued**。`namespace InformationTheory`、`klDiv` ではなく `InformationTheory.klDiv` |
| KL 非負 | — (型で自明) | — | ✅ 自明 | `klDiv : ℝ≥0∞` なので `0 ≤ klDiv μ ν` は `bot_le` / `zero_le`。専用補題不要 |
| KL = 0 iff | `klDiv_eq_zero_iff` | `Basic.lean`（loogle 検出） | ✅ 既存 | 等号条件（補題 1 では不要） |
| KL toReal | `toReal_klDiv (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) ...` | `Basic.lean` | ✅ 既存 | `.toReal` 版（非負も `ENNReal.toReal_nonneg`） |
| KL chain rule (left) | `klDiv_compProd_left : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` | `ChainRule.lean:182` | ✅ 既存 | 同一 kernel 因子の消去 |
| KL chain rule (add) | `klDiv_compProd_eq_add : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` | `ChainRule.lean:204` | ✅ 既存 | compProd 上の KL 分解 |
| `klDiv(joint ‖ product) = h(X) − h(X\|Z)` 橋 | — | — | ❌ **不在** | `differentialEntropy` と `klDiv` を結ぶ等式は in-tree にも Mathlib にも無し |
| differential entropy ↔ condDistrib 既製関係 | — | — | ❌ **Found 0**（`differentialEntropy, condDistrib` 同時言及 0） | 連続版 condEntropy 自体 Mathlib 不在（in-tree def が唯一） |

**所見**: 群 2 が補題 1 の弱点。KL の実体・非負性（型自明）・chain rule は揃うが、**「`I(X;Z) = h(X) − h(X|Z)` という差分形」「`klDiv(joint ‖ product)` を differential entropy 差分に変換する等式」が Mathlib にも in-tree にも存在しない**（`mutualInfo` = Found 0、bridge = 不在）。これが `@residual(wall:cond-diff-entropy)` の真の正体。補題 1 を genuine 化するには、(a) joint = `μ_Z ⊗ₘ condDistrib`・product = `μ_Z.prod μ_X` を組み、(b) `klDiv(joint‖product).toReal = h(μ.map X) − condDifferentialEntropy X Z μ`（連続版相互情報量＝KL）を自作し、(c) `0 ≤ klDiv` から従わせる、という 3 段の bridge を全部 in-tree で建てる必要がある。**決定的不在あり（真壁、ただし closeable）。**

---

## 群 3 — アフィン pushforward と独立性（補題 2 用）

> source: `Mathlib/Probability/Independence/Basic.lean`、`Mathlib/MeasureTheory/Measure/Map.lean`、`Mathlib/Probability/Kernel/Composition/{MapComap,MeasureCompProd,Lemmas}.lean`、`Mathlib/MeasureTheory/Group/Arithmetic.lean`。

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| IndepFun ⇔ joint = product | `indepFun_iff_map_prod_eq_prod_map_map {mβ mβ'} [IsFiniteMeasure μ] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : f ⟂ᵢ[μ] g ↔ μ.map (fun ω ↦ (f ω, g ω)) = (μ.map f).prod (μ.map g)` | `Independence/Basic.lean:701` | ✅ 既存 | **補題 2 step 1**。`[IsFiniteMeasure μ]` 要求（`IsProbabilityMeasure` で充足）。順序 = `(f ω, g ω)` → `f = Z, g = X` で `(Z, X)` joint |
| IndepFun ⇔ (SigmaFinite 版) | `indepFun_iff_map_prod_eq_prod_map_map' (hf hg) (σf : SigmaFinite (μ.map f)) (σg : SigmaFinite (μ.map g)) : ...` | `Independence/Basic.lean:685` | ✅ 既存 | 上の弱前提版（バックアップ） |
| map 合成 | `Measure.map_map {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)` | `Measure/Map.lean:202` | ✅ 既存 | アフィン写像 `g` を product 上に押し出す。両 Measurable 要 |
| add-const 可測 | `MeasurableAdd.measurable_add_const` | `Group/Arithmetic.lean`（loogle 検出） | ✅ 既存 | `(· + y)` の可測性（`ℝ` は `MeasurableAdd`） |
| アフィン `g(z,x)=(z,x+c·z)` 可測 | — (組立) | — | ⚠️ 自作（自明） | `measurable_fst`・`measurable_snd`・`measurable_const.mul`・`.add` の合成。数行 |
| Kernel.map | `Kernel.map (κ : Kernel α β) (f : β → γ) : Kernel α γ := if hf : Measurable f then mapOfMeasurable κ f hf else 0` | `Kernel/Composition/MapComap.lean:63` | ✅ 既存 | fibre kernel 構成の出口（ただし z 依存 shift には不十分、下記） |
| Kernel.map 点評価 | `Kernel.map_apply (κ : Kernel α β) (hf : Measurable f) (a : α) : map κ f a = (κ a).map f` | `MapComap.lean:74` | ✅ 既存 | — |
| Kernel.map Markov 保存 | `Kernel.IsMarkovKernel.map` | `MapComap.lean`（loogle 検出） | ✅ 既存 | `IsFiniteKernel κ` 取得に必要 |
| product = compProd const | `Measure.compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] : μ ⊗ₘ (Kernel.const α ν) = μ.prod ν` | `Composition/MeasureCompProd.lean:141` | ✅ 既存 | product を const kernel の compProd に。`κ` が **z 非依存なら**直接適用可 |
| compProd through kernel-map | `Measure.compProd_map [SFinite μ] [IsSFiniteKernel κ] {f : β → γ} (hf : Measurable f) : μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f)` | `Composition/Lemmas.lean:120` | ✅ 既存 | ★但し `f : β → γ`（**z 非依存**、`Prod.map id f` 形）。z 依存 shift `x ↦ x + c·z` には**そのまま使えない** |
| z 依存アフィン kernel の compProd 同定 | — | — | ❌ **off-the-shelf なし** | **補題 2 の自作中核**。`((μ.map Z).prod (μ.map X)).map g = (μ.map Z) ⊗ₘ κ`（`κ z := (μ.map X).map (· + c·z)`）を組む。`compProd_map` は z 非依存しか扱えないため、`Measure.ext` + `compProd_apply` + `prod_apply` から手で示すか、kernel-map 経由の reparametrise を自作 |
| 平行移動不変性（in-tree） | `differentialEntropy_map_add_const {μ : Measure ℝ} (hμ : μ ≪ volume) [SigmaFinite μ] (y : ℝ) : differentialEntropy (μ.map (· + y)) = differentialEntropy μ` | `InformationTheory/Shannon/DifferentialEntropy.lean:171` | ✅ 既存（in-tree） | **補題 2 の fibre 同定の出口**。`hμ : μ ≪ volume`（= `hX_ac` から）+ `SigmaFinite`（確率測度から）要求 |

**所見**: 群 3 は補題 2 の部品が**ほぼ完備**。`indepFun_iff` → `map_map` → `condDistrib_ae_eq_of_measure_eq_compProd` → fibre `differentialEntropy_map_add_const` の鎖が全て存在。**唯一の自作は「z 依存アフィン kernel `κ z := (μ.map X).map (· + c·z)` を product の押し出しと一致させる compProd 同定」**（`compProd_map` が z 非依存しか扱えないため）。これは `Measure.ext` + `compProd_apply`/`prod_apply` での measure-theoretic plumbing（~30-60 行見積）であり、**真壁ではなく自作可能**。補題 2 は buildable。

---

## 主要前提条件ボックス（前提事故が起きやすい lemma）

- **`condDistrib Y X μ`**: 出力側 `Ω`-role に `[StandardBorelSpace Ω] [Nonempty Ω]`、`μ` に `[IsFiniteMeasure μ]`、`β`-role に `[MeasurableSpace β]`。in-tree では出力 = `ℝ`（StandardBorel・Nonempty 自動）、`μ = IsProbabilityMeasure`（IsFiniteMeasure を含意）→ **追加前提 0、honest**。引数順 `Y X μ` を `X Z μ` と取り違えると左右因子が逆転（in-tree は正しく対応済）。
- **`compProd_map_condDistrib (hY : AEMeasurable Y μ)`**: 結論 `(μ.map X) ⊗ₘ condDistrib Y X μ = μ.map (X,Y)`。左因子は**条件付け側** `μ.map X`。補題 2 で joint を組むとき第 1 座標 = 条件付け変数 `Z` に揃える。
- **`condDistrib_ae_eq_of_measure_eq_compProd (X) (hY : AEMeasurable Y μ) {κ} [IsFiniteKernel κ] (hκ)`**: `κ` に `[IsFiniteKernel κ]` 必須。自作 `κ z := (μ.map X).map (· + c·z)` は Markov（`IsMarkovKernel.map` 経由）→ IsFiniteKernel。a.e. 等号は `μ.map X` 上（= 条件付け側の law 上）で出る点に注意（in-tree def の積分は `μ.map Z` 上 → 対応 OK）。
- **`indepFun_iff_map_prod_eq_prod_map_map [IsFiniteMeasure μ] (hf hg : AEMeasurable)`**: `IsFiniteMeasure` 要（充足）。`f, g` は AEMeasurable で可（`Measurable` から従う）。
- **`differentialEntropy_map_add_const (hμ : μ ≪ volume) [SigmaFinite μ]`**: fibre 各 z で `μ := μ.map X`、`hμ := hX_ac`、`SigmaFinite` は確率測度から。shift 量 `y := c·z`。**`hX_ac : μ.map X ≪ volume` が load-bearing precondition**（regularity、bundle ではない）。
- **`klDiv : ℝ≥0∞`**: 非負は型で自明だが、`.toReal` を取ると `klDiv = ∞` の場合 `toReal = 0` に潰れる。補題 1 で KL を実数差分に変換する際は `klDiv_ne_top` 系（`μ ≪ ν ∧ Integrable (llr)`）の有限性を別途確保しないと bridge が degenerate に潰れるリスク。

---

## 自作が必要な要素（優先度順）

1. **【補題 2・最優先】z 依存アフィン kernel の compProd 同定**
   `((μ.map Z).prod (μ.map X)).map g = (μ.map Z) ⊗ₘ κ`、`g(z,x)=(z, x+c·z)`、`κ z := (μ.map X).map (· + c·z)`。
   推奨実装: `Measure.ext` + `Measure.compProd_apply` + `Measure.prod_apply` + `Measure.map_apply` で矩形集合上に分解、または `κ` を `Kernel.comap`/`Kernel.map` で構成して `compProd_apply` を直接計算。`compProd_map`（`Lemmas.lean:120`）は z 非依存 `f` 限定なので転用不可。工数 ~40-60 行、落とし穴 = `g` の可測性と矩形 generator 上の等号から全体等号への持ち上げ。
2. **【補題 2】アフィン写像 `g` / fibre shift `(· + c·z)` の可測性補題**（自明、数行）。
3. **【補題 2】fibre 同定後の積分書換**: `condDistrib_ae_eq_of_measure_eq_compProd` の a.e. 等号を `integral_congr_ae` で `condDifferentialEntropy` 定義の積分に流し込む + `differentialEntropy_map_add_const` を各 z で適用 + `integral_const`（確率測度）。工数 ~15-25 行。
4. **【補題 1・真壁】連続版相互情報量 = KL 等式**
   `condDifferentialEntropy X Z μ = differentialEntropy (μ.map X) − (klDiv (μ.map (Z,X)) ((μ.map Z).prod (μ.map X))).toReal` 相当。Mathlib に `mutualInfo` 不在のため**新規概念の in-tree 構築**。これが `@residual(wall:cond-diff-entropy)` の核心で、`llr`（log-likelihood ratio）と `negMulLog` 積分・disintegration を結ぶ計算が要る。工数大（~150-300 行、別 Phase 相当）。落とし穴 = `klDiv = ∞` 退化 case の処理（`hX_ac` だけでは joint の積分可能性を保証しない）。
5. **【補題 1】KL 非負からの結論**: 上の等式が建てば `0 ≤ klDiv.toReal`（`ENNReal.toReal_nonneg`）で 1 行。等式が壁。

---

## Mathlib 壁の列挙（真壁、`@residual(wall:cond-diff-entropy)` 対象）

| wall | 内容 | loogle 確認 | shared sorry 集約 |
|---|---|---|---|
| **連続版相互情報量 `mutualInfo`** | `I(X;Z)` 概念自体が Mathlib 不在 | `"mutualInfo"` → **Found 0 declarations whose name contains "mutualInfo"** | ✅ 既に `EPIG2ConvEntropyMonotone.lean` の `condDifferentialEntropy_le` に `wall:cond-diff-entropy` で集約済（shared sorry 補題） |
| **KL ↔ differential entropy 差分の橋** | `klDiv(joint‖product).toReal = h(X) − h(X\|Z)` 等式が不在 | `differentialEntropy, ProbabilityTheory.condDistrib` 同時言及 → **Found 0** | 同上 wall に集約。補題 1 genuine 化＝この橋の構築 |

**補題 2 側に真壁はなし** — z 依存アフィン kernel の compProd 同定は off-the-shelf 不在だが組立可能（自作 plumbing であって Mathlib 壁ではない）。現状 `condDifferentialEntropy_indep_add_eq` も `wall:cond-diff-entropy` を負っているが、**本調査の結論として補題 2 は wall ではなく buildable**（下記 §結論で再分類提案）。

`@residual` の class は既存どおり `wall:cond-diff-entropy`（EPI-line-wide / textbook-wide な shared asset として 1 file に集約、`plan:` ではなく `wall:` が適切 — 既存 docstring の 2026-06-04 honesty audit 判定と整合）。

---

## 撤退ラインへの距離

親計画 `epi-g2-general-sandwich-moonshot-plan.md` の Phase 1 (β) 関連撤退ライン:
- 「Phase 1 (β) が `condDistrib` 機構の不足で buildable でない場合 → β を断念し別経路」相当の L 線。

判定: **発動しない（no）**。
- `condDistrib` 機構（群 1）は完備、補題 2 は部品完備で buildable。
- 補題 1 の真壁（mutualInfo 不在）は既に `wall:cond-diff-entropy` の `sorry + @residual` として正規撤退口で処理済 — type-check done を維持しており、撤退ラインの「断念」条件には該当しない（撤退口 = sorry は許容、仮説束化していない）。
- 最も近い L 線（β 経路の構造的破綻）にも触れない：β の数学的骨格（conditioning reduces + fibre 同定）は両方とも in-tree 構築可能と確認。

縮退案の新規撤退ライン（保険、発動時のみ）:
- **補題 1 の mutualInfo=KL bridge が当該 Phase で建たない場合** → 補題 1 は `wall:cond-diff-entropy` sorry のまま据え置き、**補題 2（buildable）だけ先に genuine 化**して Phase 1 (β) を「conditioning-reduces を仮定した条件付き完成」に縮退。撤退口は sorry + `@residual`（仮説束化禁止）。

---

## 着手 skeleton

`InformationTheory/Shannon/EPIG2ConvEntropyMonotone.lean` は既存。本調査の追加 helper は同 file 内に置く想定（shared sorry 補題集約の方針を維持）。新規 helper の出だし:

```lean
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import InformationTheory.Shannon.DifferentialEntropy

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- z 依存アフィン kernel `κ z := (μ.map X).map (· + c·z)`。補題 2 の compProd 同定用。 -/
noncomputable def affineShiftKernel (νX : Measure ℝ) (c : ℝ) : Kernel ℝ ℝ :=
  Kernel.map (Kernel.const ℝ νX) (fun _ => 0)  -- ★z 依存 shift に要改設計、placeholder

/-- 自作中核: product の押し出し = z 依存アフィン kernel の compProd。 -/
theorem prod_map_affine_eq_compProd
    (νZ νX : Measure ℝ) [SFinite νZ] [SFinite νX] (c : ℝ) :
    (νZ.prod νX).map (fun p => (p.1, p.2 + c * p.1))
      = νZ ⊗ₘ (affineShiftKernel νX c) := by
  sorry  -- @residual(plan:epi-g2-cond-diff-entropy-fibre)  ← buildable, 真壁ではない

/-- 補題 2 本体（再掲、buildable 化後は genuine proof に置換）。 -/
theorem condDifferentialEntropy_indep_add_eq
    (X Z : Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hX_ac : (μ.map X) ≪ volume) :
    condDifferentialEntropy (fun ω => X ω + c * Z ω) Z μ
      = differentialEntropy (μ.map X) := by
  sorry  -- @residual(wall:cond-diff-entropy) → 再分類候補 plan:...-fibre

end InformationTheory.Shannon
```

> 注: `affineShiftKernel` の z 依存 shift（`(· + c·z)` が z で変わる）は `Kernel.const` + `Kernel.map` の単純合成では表現できない。`Kernel.comap`/`mapOfMeasurable` で `fun z => (νX).map (· + c·z)` を直接 bundle するか、`Kernel.map (Kernel.const ℝ νX) g` の `g` を 2 引数 `(z, x) ↦ x + c·z` にして prodMkLeft 経由で z を引き込む設計が要る。skeleton の placeholder は要再設計（最優先自作要素 1）。

---

## §結論

| 補題 | 判定 | 根拠 | 自作要素 |
|---|---|---|---|
| **補題 1 `condDifferentialEntropy_le`**（conditioning reduces） | **部分的（真壁あり）** | KL 実体・非負（型自明）・chain rule は既存だが、`mutualInfo`=Found 0 かつ `I=h−h|=KL` 差分橋が in-tree/Mathlib 双方不在 | 自作 4・5（mutualInfo=KL 等式の in-tree 構築、~150-300 行、別 Phase 相当） |
| **補題 2 `condDifferentialEntropy_indep_add_eq`**（fibre 同定） | **buildable** | `indepFun_iff` → `map_map` → `condDistrib_ae_eq_of_measure_eq_compProd` → `differentialEntropy_map_add_const` の鎖が全て既存。真壁なし | 自作 1（z 依存アフィン kernel compProd 同定、~40-60 行）・2・3 |

**自作必要要素**: 5 件（優先度順 §自作が必要な要素）。うち補題 2 を閉じるのは 1・2・3（plumbing、buildable）、補題 1 を閉じるのは 4・5（真壁、別 Phase）。

**既存率**: 部品実体ベースで群 1 = 100%・群 2 = KL/chain rule は 100% だが bridge 概念は 0%・群 3 = 95%（z 依存 compProd 同定のみ自作）。**高レベル橋（mutualInfo / fibre compProd 同定）2 件を除けば primitive はほぼ完備。**

**撤退ライン発動**: no。

**再分類提案**: `condDifferentialEntropy_indep_add_eq`（補題 2）の `@residual` は現状 `wall:cond-diff-entropy` だが、本調査で **buildable（真壁ではない）と判明**したので `plan:<fibre-closure-slug>` への再分類が honest。補題 1 のみ真の `wall:cond-diff-entropy` として残すのが正確（独立 honesty audit で要確認）。
