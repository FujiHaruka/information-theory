# EPI richness 壁 (G4/W2) — noise-extension Mathlib 在庫調査

> 親計画: [`docs/shannon/epi-stam-to-conclusion-plan.md`](epi-stam-to-conclusion-plan.md)
> §re-assessment 表 G4/W2 行 + 撤退ライン L-Concl-A-richness / L-Concl-A-γ。
> 調査対象 declaration: `IsStamScalingNoiseHyp` / `stamScalingNoise_exists`
> (`InformationTheory/Shannon/EPIStamToBridge.lean:358` / `:388`)、
> G4 joint indep `sorry` (`EPIStamToBridge.lean:1360`)。
> 形式参照点: [`shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md)。

---

## 総合 verdict

**部分的に可能。richness 壁の「Mathlib に noise-extension constructor が無い」という現状記述は不正確 — 必要な product-measure 構成 API (積拡張・座標独立・iIndepFun_pi・sum 独立・lift law 保存) は Mathlib に全て存在する。** したがって「任意確率空間上に独立 standard normal pair が存在する」という素朴な存在主張は、**新しい空間 `Ω × ℝ × ℝ`(measure `P.prod (gaussianReal 0 1).prod (gaussianReal 0 1)` または `Measure.pi`)を構成し、座標射影を witness にする**ことで Mathlib API のみから genuine に証明できる。`indepFun_prod` / `iIndepFun_pi` / `map_prod_map` / `map_fst_prod` / `IndepFun.comp` / `gaussianReal` の `IsProbabilityMeasure` instance が揃っている。

**ただし真の残壁は別の場所にある。** `IsStamScalingNoiseHyp X Y P` および全 EPI consumer chain は **固定された単一の `(Ω, P)` 上に** `Z_X, Z_Y : Ω → ℝ` が存在することを要求する(`P.map Z_X = gaussianReal 0 1`、`IndepFun X Z_X P` 等、すべて元の `P` でキー)。product 構成が産むのは**別の空間** `Ω × ℝ²` 上の measure であり、`(Ω, P)` 自体を拡張する API は実在しない(`MeasureTheory.IsAtomless` 風 richness instance が Mathlib 不在、これは plan の記述どおり)。

→ **2 通りの closure 経路**があり、どちらを採るかで残壁が変わる:

- **経路 A(in-place richness instance):** `(Ω, P)` が atomless / 十分豊か という instance を仮定して、その上に独立 gaussian を構成。**この instance も constructor も Mathlib 不在** → これは真の壁(richness precondition 据置が正しい)。
- **経路 B(statement-level re-mapping、推奨):** `entropy_power_inequality` は `entropyPower (P.map X)` という **law-only 量**のみを結論し、`IsStamInequalityResidual` は **carrier に一切依存しない**(後述、密度キー)。よって「lift 空間 `Ω×ℝ²` で EPI を証明 → `entropyPower ((P.prod ν).map (X∘fst)) = entropyPower (P.map X)` で `(Ω,P)` に transport」が成立する。この経路では richness 壁は **完全に閉じられる**(Mathlib API のみ、self-written transport lemma 1 本)。残るのは transport lemma の plumbing(50〜100 行)であり、Mathlib 壁ではない。

**結論:** plan の現判定「noise extension が Mathlib 不在なら richness を honest precondition として signature に残す」(L-Concl-A-richness)は **経路 A 前提では正しいが、経路 B では発動不要**。G4/W2 は「真の Mathlib 壁」ではなく「**statement の carrier を lift 空間に張り替える設計判断**」の問題。撤退ライン発動は **回避可能**。

---

## 主定理の最終形(再掲)

```lean
-- headline (EntropyPowerInequality.lean:287)
theorem entropy_power_inequality {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (h_stam : IsStamInequalityResidual X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y)
```

G4/W2 が出てくる中間 closure(`isStamToEPIScalingHyp_of_stam_debruijn`, `:1291`)は固定 `(Ω,P)` 上で:

```lean
-- W2: 任意確率空間上に独立 standard-normal pair が存在
theorem stamScalingNoise_exists (X Y : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsStamScalingNoiseHyp X Y P := by sorry   -- EPIStamToBridge.lean:388

-- IsStamScalingNoiseHyp (EPIStamToBridge.lean:358) — 全 conjunct が P でキー
def IsStamScalingNoiseHyp (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ (Z_X Z_Y : Ω → ℝ),
    Measurable Z_X ∧ Measurable Z_Y ∧
    P.map Z_X = gaussianReal 0 1 ∧ P.map Z_Y = gaussianReal 0 1 ∧
    IndepFun X Z_X P ∧ IndepFun Y Z_Y P ∧ IndepFun Z_X Z_Y P

-- G4: 4-tuple joint indep を pairwise から導く sorry (EPIStamToBridge.lean:1360)
have hXYZXY : IndepFun (fun ω => X ω + Y ω) (fun ω => Z_X ω + Z_Y ω) P := by sorry
```

経路 B の pseudo-Lean(transport の骨子):

```lean
-- lift 空間 Ω' := Ω × ℝ × ℝ, ν := gaussianReal 0 1, P' := P.prod (ν.prod ν)
-- X' := X ∘ fst,  Z_X' := (·.2.1),  Z_Y' := (·.2.2)
-- 1) IsStamScalingNoiseHyp X' Y' P' を product API で構成 (経路 B では W2 が消える)
-- 2) lift 上で既存 EPI chain を回し EPI on P' を得る
-- 3) entropyPower (P'.map X') = entropyPower (P.map X)  -- map_map + map_fst_prod
--    IsStamInequalityResidual X Y P = IsStamInequalityResidual X' Y' P'  -- carrier-free, defeq
-- 4) transport で entropy_power_inequality on (Ω,P) を結論
```

---

## 軸 1 — 確率空間の積拡張

| 概念 | Mathlib API | file:line | 状態 | 用途 |
|---|---|---|---|---|
| 積測度 | `MeasureTheory.Measure.prod` | `MeasureTheory/Measure/Prod.lean`(定義) | ✅ | lift 空間 `Ω×ℝ²` の測度本体 |
| 積が確率測度 | `MeasureTheory.Measure.prod.instIsProbabilityMeasure` | `Prod.lean:322` | ✅ | `[IsProbabilityMeasure P']` 自動導出 |
| fst 射影 law | `MeasureTheory.Measure.map_fst_prod` | `Prod.lean:254` | ✅ | lift で X law 保存の核 |
| snd 射影 law | `MeasureTheory.Measure.map_snd_prod` | `Prod.lean:262` | ✅ | 同(Z 側) |
| fst measure-preserving | `MeasureTheory.measurePreserving_fst` | `Prod.lean:258` | ✅ | `[IsProbabilityMeasure ν]` 要、transport |
| snd measure-preserving | `MeasureTheory.measurePreserving_snd` | `Prod.lean:265` | ✅ | `[IsProbabilityMeasure μ]` 要 |
| fst marginal (prob) | `MeasureTheory.Measure.fst_prod` | `Prod.lean:1107` | ✅ | `[IsProbabilityMeasure ν]` 要 |
| 有限 Pi 積測度 | `MeasureTheory.Measure.pi` | (Mathlib `MeasureTheory/Constructions/Pi`) | ✅ | 4 座標を一気に張る別ルート |

verbatim signature(主要):

```lean
-- Prod.lean:322
instance prod.instIsProbabilityMeasure {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ.prod ν)

-- Prod.lean:254
@[simp] lemma map_fst_prod : Measure.map Prod.fst (μ.prod ν) = (ν univ) • μ
-- (確率測度文脈では ν univ = 1 で μ に等しい; measurePreserving_fst が one_smul 済形を供給)

-- Prod.lean:258
lemma _root_.MeasureTheory.measurePreserving_fst [IsProbabilityMeasure ν] :
    MeasurePreserving Prod.fst (μ.prod ν) μ
```

---

## 軸 2 — 積測度上の independence

| 概念 | Mathlib API | file:line | 状態 | 用途 |
|---|---|---|---|---|
| 2 座標独立(prod) | `ProbabilityTheory.indepFun_prod` | `Probability/Independence/Basic.lean:751` | ✅ | `(X∘fst) ⟂ (Y∘snd)` on `μ.prod ν` の核 |
| 2 座標独立(AE 版) | `ProbabilityTheory.indepFun_prod₀` | `Basic.lean:762` | ✅ | AEMeasurable 版 |
| n 座標独立(pi) | `ProbabilityTheory.iIndepFun_pi` | `Basic.lean:784` | ✅ | **4-tuple joint indep の核**(G4 の真の当て先) |
| 独立 ↔ map prod | `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map` | `Basic.lean`(`[IsFiniteMeasure μ]`) | ✅ | 独立性 → 結合分布因子化 |
| 合成保存 | `ProbabilityTheory.IndepFun.comp` | `Basic.lean:799` | ✅ | グループ化(pair を 1 座標に潰す) |
| 合成保存(AE) | `ProbabilityTheory.IndepFun.comp₀` | `Basic.lean:805` | ✅ | 同 |
| 対称性 | `ProbabilityTheory.IndepFun.symm` | `Basic.lean:735` | ✅ | swap |
| 和 vs 単独 | `ProbabilityTheory.iIndepFun.indepFun_finsetSum_of_notMem` | `Basic.lean:981` 近傍(`to_additive` of `indepFun_finsetProd_of_notMem`) | ✅ | `∑ vs 単独`(下記注意) |
| `map_prod_map` | `MeasureTheory.Measure.map_prod_map` | `Prod.lean:825` | ✅ | 因子化結合分布の押し出し |

verbatim signature:

```lean
-- Basic.lean:751
lemma indepFun_prod (mX : Measurable X) (mY : Measurable Y) :
    (fun ω ↦ X ω.1) ⟂ᵢ[μ.prod ν] (fun ω ↦ Y ω.2)
-- context: {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
--          {X : Ω → 𝓧} {Y : Ω' → 𝓨}  [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

-- Basic.lean:784
lemma iIndepFun_pi (mX : ∀ i, AEMeasurable (X i) (μ i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ)
-- context: {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
--          {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
--          {𝓧 : ι → Type*} [∀ i, MeasurableSpace (𝓧 i)] {X : (i : ι) → Ω i → 𝓧 i}

-- Basic.lean:799
theorem IndepFun.comp {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : f ⟂ᵢ[μ] g) (hφ : Measurable φ) (hψ : Measurable ψ) :
    (φ ∘ f) ⟂ᵢ[μ] ψ ∘ g
```

---

## 軸 3 — standard normal の存在 / 構成

| 概念 | Mathlib API | file:line | 状態 | 用途 |
|---|---|---|---|---|
| `gaussianReal` 定義 | `ProbabilityTheory.gaussianReal` | `Probability/Distributions/Gaussian/Real.lean:200` | ✅ | 標準正規 measure(`μ=0, v=1`) |
| 確率測度 instance | `ProbabilityTheory.instIsProbabilityMeasureGaussianReal` | `Gaussian/Real.lean:209` | ✅ | lift 因子が確率測度 |
| `map id` 恒等 | `MeasureTheory.Measure.map_id` | `MeasureTheory/Measure/Map.lean:193` | ✅ | `(gaussianReal 0 1).map id = gaussianReal 0 1`(座標 witness の law) |

```lean
-- Gaussian/Real.lean:200
def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ
-- Gaussian/Real.lean:209
instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v)
-- Map.lean:193
theorem map_id : map id μ = μ
```

**標準正規確率変数の「存在」の言い方**: Mathlib に「任意空間上に gaussian 確率変数が存在」という直接補題は無い(plan の loogle 0-hit は正しい)。しかし lift 空間 `… × ℝ`(因子 `gaussianReal 0 1`)上では **座標射影 `Prod.snd` がそのまま standard-normal witness**:`((P.prod ν).map Prod.snd) = ν = gaussianReal 0 1`(`map_snd_prod` + `one_smul`)。Pi 版なら `(Measure.pi μ).map (eval i)` が `μ i` に等しい(`measurePreserving_eval`)。

---

## 軸 4 — lift した X, Y の law 保存

| 概念 | Mathlib API | file:line | 状態 | 用途 |
|---|---|---|---|---|
| 写像合成 | `MeasureTheory.Measure.map_map` | `MeasureTheory/Measure/Map.lean:202` | ✅ | `(P'.map fst).map X = P'.map (X∘fst)` |
| fst 射影 law | `map_fst_prod` / `measurePreserving_fst` | `Prod.lean:254/258` | ✅ | `(P.prod ν).map fst = P` |
| 積写像押し出し | `MeasureTheory.Measure.map_prod_map` | `Prod.lean:825` | ✅ | 結合分布の因子化 |

```lean
-- Map.lean:202
theorem map_map {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    (μ.map f).map g = μ.map (g ∘ f)
-- Prod.lean:825
theorem map_prod_map {δ} [MeasurableSpace δ] {f : α → β} {g : γ → δ}
    (μa : Measure α) (μc : Measure γ) [SFinite μa] [SFinite μc]
    (hf : Measurable f) (hg : Measurable g) :
    (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc)
```

**law-only 不変性の根拠**: `entropyPower : Measure ℝ → ℝ`(`EntropyPowerInequality.lean:101`)は **measure を引数に取る law-only 量**。`X' := X ∘ Prod.fst : Ω×ℝ² → ℝ` に対し
`P'.map X' = (P'.map Prod.fst).map X = P.map X`(`map_map` + `measurePreserving_fst.map_eq`)。
よって `entropyPower (P'.map X') = entropyPower (P.map X)`。transport の linchpin はこの 1 行。

---

## 軸 5 — `IsStamScalingNoiseHyp` の実 signature(field 単位)

`EPIStamToBridge.lean:358`、verbatim:

```lean
def IsStamScalingNoiseHyp {Ω : Type*} [MeasurableSpace Ω]
    (X Y : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ (Z_X Z_Y : Ω → ℝ),
    Measurable Z_X ∧ Measurable Z_Y ∧
    P.map Z_X = gaussianReal 0 1 ∧ P.map Z_Y = gaussianReal 0 1 ∧
    IndepFun X Z_X P ∧ IndepFun Y Z_Y P ∧ IndepFun Z_X Z_Y P
```

| field | 内容 | 供給? |
|---|---|---|
| `Measurable Z_X` / `Measurable Z_Y` | 可測性 | ○ |
| `P.map Z_X = gaussianReal 0 1` ×2 | 各 Z が標準正規(law-keyed、`P` 固定) | ○ |
| `IndepFun X Z_X P` | X⊥Z_X(pairwise) | ○ |
| `IndepFun Y Z_Y P` | Y⊥Z_Y(pairwise) | ○ |
| `IndepFun Z_X Z_Y P` | Z_X⊥Z_Y(pairwise) | ○ |
| **`IndepFun (X+Y) (Z_X+Z_Y) P`** | sum vs sum joint indep | **✗ 不在(= G4)** |
| **4-tuple `iIndepFun [X,Y,Z_X,Z_Y] P`** | joint(X⊥Y も含む) | **✗ 不在** |

**plan の「pairwise のみ / joint 不在」記述は正しい。** `IsStamScalingNoiseHyp` は 3 つの pairwise しか供給せず、`IndepFun (X+Y) (Z_X+Z_Y)`(G4, `:1360`)に必要な joint structure を持たない。

**新構成で joint まで供給できるか**: lift 空間で `iIndepFun_pi`(4 座標 `[X∘fst, Y∘fst, Z_X, Z_Y]`)を使えば **4-tuple joint indep が直接出る**。ただし注意:`iIndepFun_pi` は各座標を**独立な Pi 因子**に対応させるので、元の `(X, Y)` を 1 つの因子 `Ω` に同居させると `X ⊥ Y` までは出ない(これは正しい — 元の `IndepFun X Y P` は caller の `hXY` から来る別物)。設計は `Ω × ℝ × ℝ`(3 因子:`Ω` に `(X,Y)` 同居、`ℝ` 2 個が `Z_X, Z_Y`)。この 3 因子上で:
- `Z_X ⊥ Z_Y`: `indepFun_prod`(2 つの `ℝ` 因子)
- `(X,Y) ⊥ (Z_X, Z_Y)`: `indepFun_prod`(`Ω` 因子 vs `ℝ²` 因子)→ `IndepFun.comp` で射影
- `(X+Y) ⊥ (Z_X+Z_Y)`: 上記から `iIndepFun_pi`(`Ω, ℝ, ℝ` の 3 因子)→ 和の独立性

**sum-vs-sum 補題に関する注意(在庫の穴 1 個)**: Mathlib source(rev `043e9e04`)には `iIndepFun.indepFun_finsetSum_of_notMem`(**和 vs 単独**)はあるが、`(X+Y) vs (Z_X+Z_Y)` の **和 vs 和**直接補題は **source に無い**(loogle index は新しい rev を指しており `indepFun_add_add` を返すが、現コンパイル対象 source には未収録 — 下記「残壁」参照)。和 vs 和は `indepFun_iff_map_prod_eq_prod_map_map` + `iIndepFun_pi` の結合分布因子化から **self-derive 可能**(10〜30 行)。

---

## 主要前提条件ボックス

- **`indepFun_prod` / `indepFun_prod₀`**: `[IsProbabilityMeasure μ] [IsProbabilityMeasure ν]` **両方**要。lift 因子が確率測度であること(gaussian は ✅、元 `P` も `[IsProbabilityMeasure P]`)。
- **`iIndepFun_pi`**: `[Fintype ι]` + `[∀ i, IsProbabilityMeasure (μ i)]`。各 Pi 因子が確率測度。引数は `AEMeasurable`(`Measurable` から自動)。
- **`measurePreserving_fst`**: `[IsProbabilityMeasure ν]`(**右**因子が確率測度)で初めて `map fst = μ`。確率でないと `ν univ • μ` の係数が残る(`map_fst_prod` の素の形)。transport で `one_smul` を消すのにこの instance が必須。
- **`map_prod_map`**: `[SFinite μa] [SFinite μc]`(確率測度は SFinite なので OK)+ 両写像 `Measurable`。
- **`IsStamInequalityResidual` の carrier 非依存性(transport の鍵)**: 定義(`EntropyPowerInequality.lean:209`)は `∀ J_X J_Y J_sum (fX fY fXY : ℝ→ℝ), …` と **抽象密度のみ**を量化し、本体は `X, Y, P` を**一度も参照しない**。→ `IsStamInequalityResidual X Y P` と `IsStamInequalityResidual X' Y' P'` は **defeq**(carrier-free)。transport で仮説書き換え不要。これは経路 B を大幅に軽くする決定的事実。

---

## 自作が必要な要素(優先度順 / 経路 B 前提)

1. **lift 構成補題 `stamScalingNoise_exists`(W2 closure)** — `Ω × ℝ × ℝ` 上で `indepFun_prod` ×2 + `IndepFun.comp` で 3 pairwise を構成、座標 law は `map_snd_prod` 系。**ただし元の `(Ω,P)` 上の existential ではなく lift 上**になる点が経路選択の分岐。in-place(経路 A)では構成不能 → richness instance 必要。工数:lift 上なら 40〜80 行。落とし穴:`IsStamScalingNoiseHyp` は `P` 固定 existential なので、lift で構成したものを `(Ω,P)` の existential に詰め直すには **statement 側を lift 形に張り替える**(`stamScalingNoise_exists` の結論を `P'` 版にする)必要。これが経路 B の本質。
2. **sum-vs-sum 独立補題 `indepFun_add_of_iIndepFun4`(G4 closure)** — `iIndepFun [Xfst, Yfst, Z_X, Z_Y] P'` から `IndepFun (Xfst+Yfst) (Z_X+Z_Y) P'`。`indepFun_iff_map_prod_eq_prod_map_map` 経由 or グループ化 `IndepFun.comp`。工数:10〜30 行。落とし穴:Mathlib source に和 vs 和直接補題が無い(index にはある)→ 因子化経由で自作。
3. **EPI transport lemma `entropy_power_inequality_of_lift`(経路 B 本体)** — lift 空間で得た EPI を `(Ω,P)` に降ろす。核は `entropyPower (P'.map (X∘fst)) = entropyPower (P.map X)`(`map_map` + `measurePreserving_fst`)×3(X, Y, X+Y)+ `IsStamInequalityResidual` の defeq transport。工数:50〜100 行。落とし穴:`(X∘fst) + (Y∘fst) = (X+Y)∘fst` の関数等式整理、`P'.map ((X+Y)∘fst) = P.map (X+Y)` の rewrite チェーン。
4. **(経路 A を採る場合のみ)richness instance `[AtomlessLike (Ω,P)]`** — Mathlib **完全不在**。自作するなら標準 Borel + 非原子性から gaussian 構成、推定 150〜300 行 + 上流還元級。**非推奨**(経路 B が圧倒的に軽い)。

---

## Mathlib 壁の列挙(真に不在)

| wall | 内容 | loogle 確認 | 経路 B で残る? |
|---|---|---|---|
| `wall:in-place-noise-extension` | `(Ω,P)` **自体**を拡張して独立 gaussian を載せる constructor / `IsAtomless` 風 richness instance | `MeasureTheory.IsAtomless` → unknown id; `ProbabilityTheory.exists_iIndepFun` → unknown id; `exists_measurable_indepFun` → unknown id(plan 記載と一致、2026-05-25 再現) | **残らない**(経路 B は空間を張り替えるので in-place 不要) |
| (和 vs 和独立) | `IndepFun (f+g) (h+k)` from 4-tuple `iIndepFun` | source rev `043e9e04` に **不在**(`indepFun_add_add` は loogle index の**新しい** rev のみ、grep 0 hit) | self-derive 可(壁ではない、軸 2 注意参照) |

**真の Mathlib 壁は `wall:in-place-noise-extension` 1 個のみ**、かつ経路 B ではそもそも踏まない。`stamScalingNoise_exists` / G4 の現 `sorry` は「真に不在」ではなく「**設計上 in-place existential を選んだために発生した self-fillable plumbing**」。

**shared sorry 集約**: 現状 `stamScalingNoise_exists`(`:388`)が shared sorry として richness を 1 点集約済(`@residual(plan:epi-stam-to-conclusion-phaseA-plan)`)、G4(`:1360`)が同根 slug を継承。経路 B 採用時は **両者とも genuine 化できる**(集約先が消える)。集約状態は適切。

---

## 撤退ラインへの距離

親計画の **L-Concl-A-richness**(「noise extension Mathlib 不在 → richness を honest precondition 化」)/ **L-Concl-A-γ**(`stamScalingNoise_exists` の `sorry` 帰属):

- **経路 A(in-place)を採るなら発動する** — Mathlib に richness instance/constructor が無いのは事実。
- **経路 B(re-mapping)を採るなら発動不要** — 必要 API が全て揃っており、richness を precondition に残さず genuine closure できる。

**判定: 発動は回避可能(経路 B 推奨)。** plan の「richness を honest precondition として残す」は **保守的すぎる**。`entropyPower` が law-only かつ `IsStamInequalityResidual` が carrier-free という 2 事実(本調査で verbatim 確認)により、statement-level の lift-and-transport が成立する。

**縮退案(経路 B が想定外に重かった場合の新撤退ライン提案)**:
- **L-Concl-A-richness'**: transport lemma の関数等式整理が `simp`/`fun_prop` で割れない場合、lift 空間版 EPI(`entropy_power_inequality_on_product`、結論を `P'.map` 形で述べる)を **honest な中間定理**として publish し、`(Ω,P)` 版への降下を `sorry` + `@residual(plan:…)` で残す(仮説束化はしない)。撤退口は sorry のみ。

---

## 着手 skeleton

```lean
-- InformationTheory/Shannon/EPINoiseExtension.lean (新規、経路 B)
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import InformationTheory.Shannon.EntropyPowerInequality
import InformationTheory.Shannon.EPIStamToBridge

namespace InformationTheory.Shannon.EPINoiseExtension

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable (X Y : Ω → ℝ)

/-- lift 空間 `Ω × ℝ × ℝ`(`Z_X, Z_Y` 因子は標準正規)。 -/
noncomputable abbrev liftMeasure : Measure (Ω × ℝ × ℝ) :=
  P.prod ((gaussianReal 0 1).prod (gaussianReal 0 1))

/-- lift 上で X law が保存される(transport の linchpin)。 -/
theorem entropyPower_map_comp_fst_eq (hX : Measurable X) :
    entropyPower ((liftMeasure P).map (fun p => X p.1)) = entropyPower (P.map X) := by
  sorry -- @residual(plan:epi-stam-to-conclusion-phaseA-plan): map_map + measurePreserving_fst

/-- lift 空間で `IsStamScalingNoiseHyp`(P' 版)を product API のみで構成。 -/
theorem stamScalingNoise_exists_on_lift :
    IsStamScalingNoiseHyp (fun p => X p.1) (fun p => Y p.1) (liftMeasure P) := by
  sorry -- @residual(plan:epi-stam-to-conclusion-phaseA-plan): indepFun_prod + map_snd_prod

/-- 4-tuple joint indep（和 vs 和、G4 closure）を lift 上で。 -/
theorem indepFun_add_add_on_lift (hX : Measurable X) (hY : Measurable Y) :
    IndepFun (fun p => X p.1 + Y p.1)
             (fun p => p.2.1 + p.2.2) (liftMeasure P) := by
  sorry -- @residual(plan:epi-stam-to-conclusion-phaseA-plan): iIndepFun_pi + 因子化

/-- 経路 B 本体: lift EPI を (Ω,P) に降ろす。 -/
theorem entropy_power_inequality_via_lift
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P) (h_stam : IsStamInequalityResidual X Y P) :
    entropyPower (P.map (fun ω => X ω + Y ω))
      ≥ entropyPower (P.map X) + entropyPower (P.map Y) := by
  sorry -- @residual(plan:epi-stam-to-conclusion-phaseA-plan): transport via entropyPower_map_comp_fst_eq ×3

end InformationTheory.Shannon.EPINoiseExtension
```

---

## まとめ

- インベントリ: **`docs/shannon/epi-richness-noise-inventory.md`**(本ファイル)
- 軸 1–5 の Mathlib API は **既存率 100%(構成 primitive レベル)** — `indepFun_prod` / `iIndepFun_pi` / `map_prod_map` / `map_fst_prod` / `gaussianReal` instance / `map_map` / `IndepFun.comp` 全て source 確認済
- **真の Mathlib 壁は `wall:in-place-noise-extension` 1 個のみ**、かつ **経路 B(re-mapping)では踏まない**
- 自作必要: lift law 保存 + sum-vs-sum 独立 + EPI transport の **3 lemma(self-fillable、~100〜200 行)**
- 撤退ライン L-Concl-A-richness は **経路 B で発動回避可能**
