# Wyner–Ziv `WynerZivCondEntDiffConvex` discharge — Mathlib API inventory

> Phase 着手前 Mathlib API 在庫調査 (2026-05-20)。対象は `InformationTheory/Shannon/WynerZivObjectiveConvexityBody.lean:212` の primitive predicate `WynerZivCondEntDiffConvex` を 0-sorry まで discharge できるか。
>
> 同種文書: [`shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md), [`../fano/fano-mathlib-inventory.md`](../fano/fano-mathlib-inventory.md)。

## 一行サマリ

**Verdict (b)。** core を直接当てる Mathlib 高レベル補題は **0% 存在** (`klDiv` の joint convexity も `perspective` 関数も log-sum 不等式も Mathlib 不在を loogle で確認)。しかし discharge に必要な**素材 (negMulLog 凹性 + Jensen + 自前 log-sum 不等式) は 100% 既存**で、決定打となる `log_sum_inequality_negMulLog` (Real 値・有限・negMulLog 形・**完全証明済**) が **`InformationTheory/Fano/DPI.lean:44`** に既にある。これを per-`u` に当てて組み立てる路線で自前 **150〜300 行** 見込み。撤退ライン (joint-convexity-of-KL が Mathlib 不在) は**踏み抜く** が、InformationTheory 内に等価な自前部品があるため**致命傷ではない**。

---

## 主定理の最終形 (再掲)

`InformationTheory/Shannon/WynerZivObjectiveConvexityBody.lean:212`:

```lean
def WynerZivCondEntDiffConvex (P_XY : α × β → ℝ) : Prop :=
  ∀ q₁ q₂ : α × β × U → ℝ,
    IsWynerZivFactorizable U P_XY q₁ →
    IsWynerZivFactorizable U P_XY q₂ →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      (wzJointEntYU U (a • q₁ + b • q₂) - wzJointEntXU U (a • q₁ + b • q₂))
        ≤ a * (wzJointEntYU U q₁ - wzJointEntXU U q₁)
          + b * (wzJointEntYU U q₂ - wzJointEntXU U q₂)
```

ここで `wzJointEntXU U q = ∑ p:α×U, negMulLog (wzMarginalXU U q p)` (= H(X,U)),
`wzJointEntYU U q = ∑ p:β×U, negMulLog (wzMarginalYU U q p)` (= H(Y,U))。
要するに `H(m_YU) − H(m_XU) = I(X;U|Y)` が factorisable joint の凸結合に沿って convex (≤)。

### 証明戦略 (pseudo-Lean, 6〜10 行)

```text
-- 1. m := a•q₁ + b•q₂ の各 marginal は affine: m_XU(m) = a•m_XU(q₁) + b•m_XU(q₂), 同 m_YU.
--    (wzMarginalXU/YU は q について線形 = ∑ の中身が線形)
-- 2. 目標 ⇔  ∑_u [ (∑_y negMulLog m_YU(y,u)) − (∑_x negMulLog m_XU(x,u)) ]  が convex in m
--    各 u block について m_XU(x,u) = ∑_y q(x,y,u),  m_YU(y,u) = ∑_x q(x,y,u),
--    かつ ∑_x m_XU(x,u) = ∑_y m_YU(y,u) = P_U(u) (Fubini, §2 既証).
-- 3. 差 H(m_YU)−H(m_XU) は u 固定で「条件付き相対エントロピーの符号反転」: 各 u について
--    [ ∑_x negMulLog m_XU − ∑_y negMulLog m_YU ] = -KL-like。これが concave in (m_XU,m_YU 同時) を
--    log_sum_inequality_negMulLog (Fano/DPI.lean:44) で per-(y,u) atom に当てて示す。
-- 4. 凸結合の不等式は a,b 重みで二点 Jensen に縮約 (s=q₁ block, t=q₂ block) → linarith / nlinarith.
```

注意: `negMulLog` 単体は **concave** なので `H` 単体の凹性からは出ない。差 `H(m_YU)−H(m_XU)` の凸性は **joint-convexity-of-relative-entropy / log-sum 不等式が真の核**。log-sum 不等式は per-atom 凹性 (negMulLog) を「重み付き Jensen + perspective 変換 `m·negMulLog(x/m)`」で集約したもの。

---

## A. `negMulLog` / `x·log x` の凸凹性 (Mathlib, 全て既存)

ファイル `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean`。

| 概念 | Mathlib API | file:line | 状態 | core での扱い |
|---|---|---|---|---|
| `negMulLog` 定義 | `Real.negMulLog` | NegMulLog.lean (def) | 既存 | block の被加数。`negMulLog x = -x*log x` |
| negMulLog concave | `Real.concaveOn_negMulLog` | `NegMulLog.lean:227` | 既存 | log-sum 不等式の Jensen 入力 |
| negMulLog strict concave | `Real.strictConcaveOn_negMulLog` | `NegMulLog.lean:224` | 既存 | (strict 版が要れば) |
| x·log x convex | `Real.convexOn_mul_log` | `NegMulLog.lean:144` | 既存 | klFun 凸性の素材 |
| x·log x strict convex | `Real.strictConvexOn_mul_log` | `NegMulLog.lean:137` | 既存 | 同上 |
| negMulLog 連続 | `Real.continuous_negMulLog` | NegMulLog.lean | 既存 | block 連続性 (既に InformationTheory で活用) |
| negMulLog ≤ 1−x | `Real.negMulLog_le_one_sub_self` | `NegMulLog.lean:234` | 既存 | 必要なら上界評価 |
| negMulLog 乗法則 | `Real.negMulLog_mul` | `NegMulLog.lean:177` | 既存 | `negMulLog(x*y)=y·negMulLog x + x·negMulLog y` |

**signature 逐語:**

```lean
-- NegMulLog.lean:227
lemma Real.concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog
-- NegMulLog.lean:224
lemma Real.strictConcaveOn_negMulLog : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog
-- NegMulLog.lean:144
lemma Real.convexOn_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x)
```

引数: いずれも explicit 引数なし (純粋 `ConcaveOn/ConvexOn` 命題)。型クラス前提なし (具体型 `ℝ`)。

> 注: `Real.add_mul_log_le` という名前の補題は **存在しない** (loogle `Found 0`)。`Real.convexOn_mul_log` が該当機能。

---

## B. relative entropy / KL の joint convexity (Mathlib: **不在**)

| 概念 | Mathlib API | file:line | 状態 | core での扱い |
|---|---|---|---|---|
| `klDiv` (measure 値) | `InformationTheory.klDiv` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean` (def) | 既存 (但し型不適合) | **使えない**: `(μ ν : Measure α) → ℝ≥0∞`、本 core は `(α×β×U → ℝ)` の pmf 形 |
| `klDiv` の `ConvexOn` 形 | — | — | ❌ **不在** | loogle `"klDiv","ConvexOn"` → 0 (klDiv は measure 値で ConvexOn の `Module` 形に乗らない) |
| `klFun` 定義 | `InformationTheory.klFun` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:53` | 既存 | `klFun x = x*log x + 1 - x` |
| `klFun` strict convex | `InformationTheory.strictConvexOn_klFun` | `KLFun.lean:62` | 既存 | per-atom 凸性 (CsiszarProjection で活用済) |
| `klFun` convex | `InformationTheory.convexOn_klFun` | `KLFun.lean:67` | 既存 | 同上 |
| `klFun` convex on Ioi | `InformationTheory.convexOn_Ioi_klFun` | `KLFun.lean:71` | 既存 | full-support 版 |
| `klFun` 連続 | `InformationTheory.continuous_klFun` | `KLFun.lean:76` | 既存 | — |
| `klFun` 非負 | `InformationTheory.klFun_nonneg` | `KLFun.lean:149` | 既存 | — |

**signature 逐語:**

```lean
-- KLFun.lean:62
lemma InformationTheory.strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun
-- KLFun.lean:67
lemma InformationTheory.convexOn_klFun : ConvexOn ℝ (Ici 0) klFun
-- KLFun.lean:53
noncomputable def InformationTheory.klFun (x : ℝ) : ℝ := x * log x + 1 - x
```

> **重要**: `klFun` は **1 変数** 凸関数。これだけでは KL の **joint (2変数同時) convexity** は出ない。`(p,q) ↦ p log(p/q)` の joint convexity = perspective convexity が本 core の核だが、それを直接与える Mathlib 補題は無い (§D, §C 参照)。

---

## C. log-sum 不等式 (Mathlib: **不在** / InformationTheory: **既存・完全証明済**)

| 概念 | API | file:line | 状態 | core での扱い |
|---|---|---|---|---|
| log-sum 不等式 (Mathlib) | — | — | ❌ **不在** | loogle `"log_sum"` → `Real.posLog_sum` のみ (無関係: log の正部分の和) |
| **log-sum 不等式 (InformationTheory, negMulLog 形)** | `InformationTheory.log_sum_inequality_negMulLog` | **`InformationTheory/Fano/DPI.lean:44`** | ✅ **既存・proven** | **本 core discharge の決定打** |
| perspective 変換 (negMulLog 形) | `InformationTheory.mul_negMulLog_div` | `InformationTheory/Fano/BinaryJensen.lean:43` | ✅ **既存・proven** | log-sum 内部で per-atom 変換に使う |

**signature 逐語 (最重要):**

```lean
-- InformationTheory/Fano/DPI.lean:44
lemma log_sum_inequality_negMulLog {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (h_ac : ∀ i ∈ s, b i = 0 → a i = 0) :
    ∑ i ∈ s, (Real.negMulLog (a i) + a i * Real.log (b i))
      ≤ Real.negMulLog (∑ i ∈ s, a i)
          + (∑ i ∈ s, a i) * Real.log (∑ i ∈ s, b i)
```

引数 (順): `{ι : Type*}` (instance暗黙), `s : Finset ι`, `a b : ι → ℝ`, `ha hb h_ac : 仮定3つ`。
型クラス前提: **なし** (純 `Finset` + `ℝ`, namespace `InformationTheory`)。`Fintype ι` すら不要 (任意 `Finset s`)。

```lean
-- InformationTheory/Fano/BinaryJensen.lean:43
lemma mul_negMulLog_div (m x : ℝ) (hm : m ≠ 0) :
    m * Real.negMulLog (x / m) = Real.negMulLog x + x * Real.log m
```

引数 (順): `m x : ℝ`, `hm : m ≠ 0`。型クラス前提: なし。namespace `InformationTheory`。

> この 2 補題は `InformationTheory/Fano/DPI.lean` で **DPI (`condEntropy_le_pushforward_condEntropy`, `:184`)** を per-fiber 集約で証明するのに既に使われている (`:217` で fiber `F` に当てている)。本 core では fiber の代わりに **per-`u` block** に同じ engine を当てる。**先行事例として証明テンプレートが既にある**のが大きい。

---

## D. perspective 関数の凸性 (Mathlib: **不在**)

| 概念 | API | file:line | 状態 | core での扱い |
|---|---|---|---|---|
| perspective `(x,t)↦t·f(x/t)` の joint convex | — | — | ❌ **不在** | loogle `"perspective"` → `Found 0`; `rg perspective Mathlib/Analysis/Convex/` → 0 件 |
| `ConvexOn.perspective` | — | — | ❌ **不在** | loogle 該当 0 |

**結論**: perspective convexity は Mathlib に**全く無い**。本 core を「KL の joint convexity を perspective として一般に証明」する路線を取ると **完全自前 (数百行)**。**代わりに `log_sum_inequality_negMulLog` を使えば perspective を一般証明せず per-atom で済む** (§C・verdict 参照)。

---

## E. finite-sum Jensen / ConvexOn 道具 (Mathlib, 全て既存)

ファイル `Mathlib/Analysis/Convex/Jensen.lean`, `Mathlib/Analysis/Convex/Function.lean`。

| 概念 | Mathlib API | file:line | 状態 | core での扱い |
|---|---|---|---|---|
| 凹 Jensen (Finset.sum 形) | `ConcaveOn.le_map_sum` | `Jensen.lean:73` | 既存 | log-sum 内部 (Fano で使用済) |
| 凸 Jensen (Finset.sum 形) | `ConvexOn.map_sum_le` | `Jensen.lean:67` | 既存 | (二点 Jensen で十分なら不要) |
| 凹 Jensen (centerMass) | `ConcaveOn.le_map_centerMass` | `Jensen.lean:61` | 既存 | — |
| ConvexOn 和 | `ConvexOn.add` | `Function.lean:193` | 既存 | block 合成 |
| StrictConvexOn − ConcaveOn | `StrictConvexOn.sub_concaveOn` | `Function.lean:849` | 既存 | klFun 凸性導出に内部使用 |
| ConvexOn.smul (nonneg scalar) | `ConvexOn.smul` | `Mathlib/Analysis/Convex/Function.lean` (`"ConvexOn","smul"` 群) | 既存 | 重み付け |

> **`ConvexOn.le_sum` / `ConvexOn.inner_smul_le_map_sum` / `ConvexOn.smul_le_sum` という名前は存在しない** (loogle で確認: `ConvexOn`+`sum` は `map_sum_le` / `map_add_sum_le` の系列のみ)。Finset 版 Jensen の正式名は **`ConvexOn.map_sum_le` / `ConcaveOn.le_map_sum`**。

**signature 逐語:**

```lean
-- Jensen.lean:73 (section variable: [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
--   [AddCommGroup E] [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
--   [Module 𝕜 E] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]
--   {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E})
theorem ConcaveOn.le_map_sum (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    (∑ i ∈ t, w i • f (p i)) ≤ f (∑ i ∈ t, w i • p i)

-- Jensen.lean:67 (同 section)
theorem ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i)

-- Function.lean:193 (section variable: [IsOrderedAddMonoid β] [SMul 𝕜 E]
--   [DistribMulAction 𝕜 β] {s : Set E} {f g : E → β}; outer: [Semiring 𝕜] [PartialOrder 𝕜]
--   [AddCommMonoid E] [AddCommMonoid β] [PartialOrder β])
theorem ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f + g)

-- Function.lean:849 (section variable: [AddCommGroup β] [PartialOrder β]
--   [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β] {s : Set E} {f g : E → β}; outer ring 系)
theorem StrictConvexOn.sub_concaveOn (hf : StrictConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g)
```

> ℝ では `[IsStrictOrderedModule ℝ ℝ]` 等は自動で揃うので、`ConcaveOn.le_map_sum` を `negMulLog` (`s = Set.Ici 0`) に当てるのは Fano/DPI.lean:99 で実証済。

---

## F. 既存 InformationTheory 資産 (再利用最優先)

| 概念 | API | file:line | 状態 | core での扱い |
|---|---|---|---|---|
| **log-sum 不等式** | `log_sum_inequality_negMulLog` | `InformationTheory/Fano/DPI.lean:44` | ✅ proven | **核 engine** (§C) |
| **perspective per-atom 変換** | `mul_negMulLog_div` | `InformationTheory/Fano/BinaryJensen.lean:43` | ✅ proven | log-sum 補助 |
| log-sum を per-block 集約する型 | `condEntropy_le_pushforward_condEntropy` (証明本体) | `InformationTheory/Fano/DPI.lean:184` | ✅ proven (構造のみ参照) | **集約テンプレート** (fiber→u block に翻訳) |
| pmf 形 KL (1変数凸) | `klDivPmf` + `klDivPmf_strictConvexOn_left` | `InformationTheory/Shannon/CsiszarProjection.lean:55,93` | ✅ proven | **1変数凸のみ**。joint convexity ではない → 直接は使えないが per-atom klFun 凸の使い方の手本 |
| pmf 形 MI (entropy 形) | `mutualInfoPmf` | `InformationTheory/Shannon/RateDistortionAchievability.lean:261` | ✅ 既存 | core の上位 `wzMutualInfo*` の本体定義 |
| R(D) 凸性 (joint-KL を **仮定で**取り回し) | `rateDistortionFunction_convexOn` | `InformationTheory/Shannon/RateDistortionConvexity.lean:136` | ⚠ proven **but** `h_klDiv_conv` を **hypothesis 化** | **前例: この codebase は joint-KL 凸性を一度も自前 discharge していない** (docstring `:135`「specializations can discharge ... via log-sum inequality」と明記) |

> **決定的観測**: `RateDistortionConvexity.lean:25-26` のコメントは「`klDiv` の joint convexity が Mathlib 不在で ~500 行 gap、Phase B 主補題は **joint convexity を hypothesis** として publish」と明言。つまり**本 core は、この codebase がこれまで一貫して避けてきた joint-convexity-of-KL を、初めて pmf 形・有限・Real 値で実際に証明する作業**。ただし R(D) は measure 値で詰んだのに対し、**本 core は pmf 形 (Real 値・有限) なので `log_sum_inequality_negMulLog` がそのまま当たる** ── これが measure 形では使えなかった抜け道。

---

## G. frame 定義の転記 (planner 用)

| 定義 | file:line | 形 |
|---|---|---|
| `wzMarginalXY` | `InformationTheory/Shannon/WynerZiv.lean:94` | `(q : α × β × U → ℝ) : α × β → ℝ := fun p => ∑ u, q (p.1, p.2, u)` |
| `wzMarginalXU` | `InformationTheory/Shannon/WynerZiv.lean:98` | `(q : α × β × U → ℝ) : α × U → ℝ := fun p => ∑ y, q (p.1, y, p.2)` |
| `wzMarginalYU` | `InformationTheory/Shannon/WynerZiv.lean:102` | `(q : α × β × U → ℝ) : β × U → ℝ := fun p => ∑ x, q (x, p.1, p.2)` |
| `wzMutualInfoXU` | `InformationTheory/Shannon/WynerZiv.lean:107` | `:= mutualInfoPmf (wzMarginalXU U q)` |
| `wzMutualInfoYU` | `InformationTheory/Shannon/WynerZiv.lean:112` | `:= mutualInfoPmf (wzMarginalYU U q)` |
| `marginalFst` | `InformationTheory/Shannon/RateDistortionAchievability.lean:121` | `(q : α × β → ℝ) : α → ℝ := fun a => ∑ b, q (a, b)` |
| `marginalSnd` | `InformationTheory/Shannon/RateDistortionAchievability.lean:125` | `(q : α × β → ℝ) : β → ℝ := fun b => ∑ a, q (a, b)` |
| `mutualInfoPmf` | `InformationTheory/Shannon/RateDistortionAchievability.lean:261` | `:= (∑ a, negMulLog (marginalFst q a)) + (∑ b, negMulLog (marginalSnd q b)) − (∑ p, negMulLog (q p))` |
| `wzJointEntXU` | `InformationTheory/Shannon/WynerZivObjectiveConvexityBody.lean:78` | `:= ∑ p : α × U, negMulLog (wzMarginalXU U q p)` |
| `wzJointEntYU` | `InformationTheory/Shannon/WynerZivObjectiveConvexityBody.lean:83` | `:= ∑ p : β × U, negMulLog (wzMarginalYU U q p)` |
| `IsWynerZivFactorizable` | `InformationTheory/Shannon/WynerZivConvexityBody.lean:97` | `(P_XY q) : Prop := ∃ κ : α → U → ℝ, (∀ x u, 0 ≤ κ x u) ∧ (∀ x, ∑ u, κ x u = 1) ∧ (∀ x y u, q (x,y,u) = κ x u * P_XY (x,y))` |
| `IsWynerZivFactorizable_convex_combination` | `InformationTheory/Shannon/WynerZivConvexityBody.lean:253` | 凸結合が factorisable を保つ (assembly で既に使用) |

frame 全体の section variable: `{α β : Type*} [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]` + `(U : Type*) [Fintype U] [MeasurableSpace U]`。`[MeasurableSpace _]` は定義上は不使用だが section に付いている (`set_option linter.unusedSectionVars false`)。**`[DecidableEq _]` は core 自体には不要** (rate wrapper のみ要求)。

---

## 主要前提条件ボックス (前提事故が起きやすい所)

- **`log_sum_inequality_negMulLog`** (`Fano/DPI.lean:44`):
  - 仮定 `ha : ∀ i ∈ s, 0 ≤ a i`, `hb : ∀ i ∈ s, 0 ≤ b i`, **`h_ac : ∀ i ∈ s, b i = 0 → a i = 0`** (絶対連続性)。
  - 本 core で `a = m_YU(·,u)` (or block), `b = m_XU(·,u)` 等に当てる際、**`b i = 0 → a i = 0` を毎回示す**必要。factorisable joint では `q ≥ 0` (κ ≥ 0, P_XY ≥ 0) から marginal 非負は出るが、`h_ac` は marginal 同士の絶対連続性で、**factorisation 構造 (`m_YU(y,u) = ∑_x κ(u|x)P_XY(x,y)`, `m_XU(x,u)=κ(u|x)P_X(x)`) を使って per-atom に落とす作業が要る**。ここが最大の前提事故ポイント。
  - `Fintype ι` 不要 / 任意 `Finset s` で OK。型クラス前提ゼロ。

- **`Real.concaveOn_negMulLog`** (`NegMulLog.lean:227`): 定義域 **`Set.Ici (0:ℝ)`**。Jensen 適用時 `hmem : ∀ i ∈ t, p i ∈ Set.Ici 0` (= 点が非負) を毎回供給。marginal 比 `a i / b i ≥ 0` を `div_nonneg` で出す (Fano:94 の手本)。

- **`P_XY` の符号/正規化**: core 自体は `P_XY` の pmf 性 (`stdSimplex`) を**前提に取っていない** (`WynerZivCondEntDiffConvex` の signature は `P_XY : α × β → ℝ` のみ)。が、`IsWynerZivFactorizable` 経由で `q ≥ 0` は出る (`κ ≥ 0`)。`P_XY ≥ 0` は **`IsWynerZivFactorizable` から自動では出ない** (κ は確率核だが P_XY の符号は別)。**marginal 非負 / 絶対連続の証明で `P_XY ≥ 0` が要るなら、core の signature に `P_XY ≥ 0` 仮定追加 or factorisable から引き出す必要** → planner 要検討の前提リスク。

- **affine 性 (`a • q₁ + b • q₂` の marginal)**: `wzMarginalXU/YU` は `q` について線形 (`∑` の中身が `q` 評価の線形結合)。`a • q₁ + b • q₂` の marginal = `a • (marginal q₁) + b • (marginal q₂)` は **`Finset.sum_add_distrib` + `Finset.mul_sum`** で出る (Mathlib 既存)。前提事故は少ないが、`Pi.add_apply`/`Pi.smul_apply` の unfold を忘れると詰む (CsiszarProjection:112 に手本)。

---

## 自作が必要な要素 (優先度順)

1. **`marginal_affine` 補題群 (最優先, 容易)** — `wzMarginalXU U (a•q₁+b•q₂) = a•wzMarginalXU U q₁ + b•wzMarginalXU U q₂` (XU/YU 各)。`Finset.sum_add_distrib`, `Finset.mul_sum`, `Pi.*_apply`。**各 5〜15 行, 計 ~30 行**。
2. **per-`u` block 凸性補題** — 固定 `u` で `(∑_x negMulLog m_XU(x,u)) − (∑_y negMulLog m_YU(y,u))` が `(m_XU(·,u), m_YU(·,u))` の凸結合に沿って convex。これを `log_sum_inequality_negMulLog` を当てて示す。**最大の項。Fano/DPI.lean:203-227 の per-fiber 集約が直接の手本**。`h_ac` の供給が肝。**80〜150 行**。
3. **block 集約 → 全体凸性** — per-`u` を `∑_u` で集約し二点 Jensen に縮約。`Finset.sum_le_sum` + `linarith/nlinarith`。**30〜60 行**。
4. **`h_ac` (絶対連続性) supply 補題** — factorisation `q = κ·P_XY` から `m_XU=0 → m_YU 関連=0` 等を per-atom に。**20〜40 行** (前提リスク大、ここで詰まる可能性)。

合計見積もり: **150〜300 行**。落とし穴: (a) `h_ac` を factorisation から正しく落とす, (b) `P_XY ≥ 0` 前提の有無, (c) `negMulLog` 定義域 `Ici 0` の `hmem` 供給, (d) `a•q₁+b•q₂` の `Pi` unfold。

---

## 撤退ラインへの距離

親計画 (`WynerZivObjectiveConvexityBody.lean:48-56` の §撤退ライン) は:

> `WynerZivCondEntDiffConvex` は **discharge しない** ─ irreducible analytic core (joint-convexity-of-KL) として carried。周辺は全 discharge 済。

加えて codebase 全体の暗黙撤退ライン (`RateDistortionConvexity.lean:25`) は **「joint-convexity-of-KL は Mathlib 不在 ~500 行 gap → hypothesis 化」**。

**判定: この撤退ラインを「踏み抜く」挑戦**。本タスクは「carried predicate を実際に証明する」= 撤退ラインの**逆方向**。

- **踏み抜けるか**: ✅ **致命傷ではない**。R(D) で詰んだのは **measure 形** (`klDiv : Measure → ℝ≥0∞`, perspective 凸性が必要で Mathlib 不在)。本 core は **pmf 形 (Real 値・有限)** で、`log_sum_inequality_negMulLog` が**そのまま当たる** (measure 形では当たらなかった抜け道)。Fano/DPI に集約テンプレートも既存。
- **新規撤退ライン (縮退案)**: もし per-`u` block 凸性で `h_ac` の factorisation 落とし込みが破綻 → **`WynerZivCondEntDiffConvex` を `P_XY ∈ stdSimplex` + `P_XY` full-support (`∀ p, 0 < P_XY p`) を追加仮定した版** `WynerZivCondEntDiffConvex_pos` に縮退して discharge し、full-support 版を publish。full support なら `h_ac` が自明 (分母 > 0) になり最大の前提リスクが消える。閉包極限での一般化は別補題に後回し。

---

## 着手 skeleton

`InformationTheory/Shannon/WynerZivCondEntDiffConvexDischarge.lean` の出だし:

```lean
import InformationTheory.Shannon.WynerZivObjectiveConvexityBody
import InformationTheory.Fano.DPI          -- log_sum_inequality_negMulLog
import InformationTheory.Fano.BinaryJensen -- mul_negMulLog_div
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Algebra.BigOperators.Field

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory InformationTheory
open Real Set Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

variable {α β : Type*}
variable [Fintype α] [Fintype β] [MeasurableSpace α] [MeasurableSpace β]
variable (U : Type*) [Fintype U] [MeasurableSpace U]

/-- marginal は `q` について affine: 凸結合の marginal = marginal の凸結合 (XU). -/
lemma wzMarginalXU_smul_add (a b : ℝ) (q₁ q₂ : α × β × U → ℝ) :
    wzMarginalXU U (a • q₁ + b • q₂)
      = a • wzMarginalXU U q₁ + b • wzMarginalXU U q₂ := by
  sorry

/-- marginal affine (YU). -/
lemma wzMarginalYU_smul_add (a b : ℝ) (q₁ q₂ : α × β × U → ℝ) :
    wzMarginalYU U (a • q₁ + b • q₂)
      = a • wzMarginalYU U q₁ + b • wzMarginalYU U q₂ := by
  sorry

/-- per-`u` block 凸性: `log_sum_inequality_negMulLog` を fiber 代わりの u block に当てる. -/
lemma wzCondEntDiff_block_convex
    (P_XY : α × β → ℝ) {q₁ q₂ : α × β × U → ℝ}
    (hq₁ : IsWynerZivFactorizable U P_XY q₁)
    (hq₂ : IsWynerZivFactorizable U P_XY q₂)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (u : U) :
    True := by  -- 実際の不等式形は planner 確定。block per-u の ≤ を述べる
  sorry

/-- **Lemma-15.9 core の discharge.** -/
theorem wynerZivCondEntDiffConvex_discharge (P_XY : α × β → ℝ) :
    WynerZivCondEntDiffConvex U P_XY := by
  intro q₁ q₂ hq₁ hq₂ a b ha hb hab
  sorry

end InformationTheory.Shannon
```

---

## 実現可能性 verdict

**(b) Mathlib + 既存 InformationTheory 部品の組み立てでいける。**

組み立て路線 (1 パラグラフ): core `H(m_YU) − H(m_XU)` の凸性は、(i) `wzMarginalXU/YU` が `q` について affine であること (Mathlib の `Finset.sum_add_distrib`/`Finset.mul_sum` で自前 ~30 行) を使って凸結合を marginal の凸結合に翻訳し、(ii) 各 `u` block について差 `(∑_x negMulLog m_XU(x,u)) − (∑_y negMulLog m_YU(y,u))` の凸性を **`InformationTheory/Fano/DPI.lean:44` の `log_sum_inequality_negMulLog`** (Real 値・有限・negMulLog 形・**完全証明済**, `mul_negMulLog_div` 補助) を **per-`u` block に当てて** 示し (Fano の per-fiber DPI 証明 `:184-227` がそのままテンプレート)、(iii) `∑_u` で集約して二点 Jensen に縮約 (`Finset.sum_le_sum` + `nlinarith`) する。Mathlib の `klDiv` joint convexity も `perspective` 凸性も log-sum 不等式も**不在** (loogle で全て `Found 0` 確認) だが、それらの **per-atom 等価物は InformationTheory 内に既証**で、measure 形 (`klDiv : ℝ≥0∞`) で詰んだ R(D) 凸性と違い本 core は **pmf 形 (Real・有限) なので log-sum 不等式がそのまま当たる**。

**Mathlib gap で詰む経路の警告**: 「KL の joint convexity を perspective として一般証明」する路線を取ると Mathlib 不在で数百行に膨らむ (R(D) が ~500 行 gap で hypothesis 化したのと同じ罠)。**必ず `log_sum_inequality_negMulLog` を per-atom で当てる路線**を取ること。最大の残リスクは `log_sum_inequality_negMulLog` の **`h_ac` (絶対連続性 `b i = 0 → a i = 0`) を factorisation `q = κ·P_XY` から per-atom に落とす**ところ。ここが破綻したら **full-support `P_XY` 追加仮定版に縮退** (撤退ライン §縮退案) すれば `h_ac` が自明化して確実に通る。自前見積もり **150〜300 行**、full-support 縮退なら **下振れ ~120 行**。
