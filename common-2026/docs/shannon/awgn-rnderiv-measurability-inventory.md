# AWGN fibre-rnDeriv joint-measurability — feasibility inventory

> **Goal**: discharge the two residual honest hypotheses of `isContChannelMIDecompHyp_awgn` /
> `isAwgnMIDecomp_of_densitySplit` (`Common2026/Shannon/ContChannelMIDecomp.lean` ~L421 / ~L496):
> `h_meas_fibre : Measurable (fun z : ℝ × ℝ => ((awgnChannel N h_meas) z.1).rnDeriv volume z.2)`
> and `h_int_fibre_joint`. Both reduce to the **measure-form parameterized Gaussian rnDeriv**
> `fun z => (gaussianReal z.1 N).rnDeriv volume z.2`.
>
> Read-only feasibility study (no implementation). Sibling docs: `awgn-mi-decomp-plan.md`,
> `shannon-mathlib-inventory.md`.

## 一行サマリ

`gaussianPDFReal`/`rnDeriv_gaussianReal` の **per-fixed-mean** API は完備だが、Mathlib に
**(mean, point) 2 変数の joint measurability/continuity も、measure-form rnDeriv の joint
measurability も、s-finite 版 `rnDeriv_eq_rnDeriv_measure` も全て存在しない**（loogle で
それぞれ `0 match`／`Found 0 declarations` 確認済）。**決定的事実 (Q3)**: 消費側
`llr_compProd_prod_split` は `h_meas_fibre` を **everywhere-`MeasurableSet`** 生成
(`measurableSet_eq_fun` → `Measure.ae_compProd_of_ae_ae`) に使うため、`AEMeasurable` への
緩和は **そのままでは不可**。ただし AWGN では真の PDF `(x,y) ↦ gaussianPDFReal x N y` が
**everywhere `=` (a.e. ではない)** な閉形式で、しかも 2 変数 `Measurable`／`Continuous` を
`fun_prop` で即構成できるため、**Route B（AWGN 専用 PDF 経路）が最も安く genuine に達成可能**。

---

## 主対象の最終形（再掲）

```lean
-- ContChannelMIDecomp.lean:421 (同型が :496 にも)
theorem isContChannelMIDecompHyp_awgn
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (hPN : P.toNNReal + N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas)
    (h_meas_fibre :
      Measurable (fun z : ℝ × ℝ => ((awgnChannel N h_meas) z.1).rnDeriv volume z.2))  -- ★ residual #1
    (h_int_fibre_joint :
      Integrable (fun z =>
          Real.log (((awgnChannel N h_meas) z.1).rnDeriv volume z.2).toReal)
        ((gaussianReal 0 P.toNNReal) ⊗ₘ (awgnChannel N h_meas))) :                    -- ★ residual #2
    IsContChannelMIDecompHyp (gaussianReal 0 P.toNNReal) (awgnChannel N h_meas)
```

Discharge 戦略 (Route B, pseudo-Lean):
```lean
-- W z.1 = awgnChannel N h_meas z.1 = gaussianReal z.1 N        (awgnChannel_apply, rfl/simp)
-- rnDeriv_gaussianReal: (gaussianReal m N).rnDeriv vol =ᵐ[vol] gaussianPDF m N   (a.e. only!)
-- 1) everywhere-Measurable fibre PDF g(x,y) := gaussianPDFReal x N y  -- 2-var, NEW lemma, fun_prop
-- 2) bridge: ∀ x, (gaussianReal x N).rnDeriv vol =ᵐ[gaussianReal x N] gaussianPDF x N
--    transported from vol via gaussianReal_absolutelyContinuous  (already done at :382)
-- 3) h_meas_fibre: NOT directly Measurable (rnDeriv is only a.e.-determined) →
--    instead RESTATE consumer to accept the PDF g (everywhere Measurable) OR
--    feed an a.e.-rewritten predicate.  KEY: consumer needs everywhere-MeasurableSet (Q3).
-- 4) h_int_fibre_joint: compProd-integrability of log∘PDF; compose existing
--    integrable_log_gaussianPDFReal_gaussianReal (:358) over the fibres via integral_compProd.
```

---

## A. Gaussian rnDeriv / PDF 在庫テーブル (Q1, Q2)

すべて `Mathlib/Probability/Distributions/Gaussian/Real.lean`。型クラス前提・結論形 verbatim。

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| 実 PDF (1 変数) | `gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ := (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))` | `Real.lean:48` | ✅ | mean `μ` は **固定パラメータ**（入力でない） |
| ENNReal PDF | `gaussianPDF (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gaussianPDFReal μ v x)` | `Real.lean:157` | ✅ | rnDeriv との比較対象 |
| toReal 橋 | `toReal_gaussianPDF {μ : ℝ} {v : ℝ≥0} (x : ℝ) : (gaussianPDF μ v x).toReal = gaussianPDFReal μ v x` (`@[simp]`) | `Real.lean:166` | ✅ | residual #2 の log 内変換に使用（既に :390 で利用） |
| **rnDeriv = PDF (a.e.!)** | `rnDeriv_gaussianReal (μ : ℝ) (v : ℝ≥0) : ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v` | `Real.lean:240` | ✅ (但 `=ᵐ[vol]`) | **CRUCIAL: 結論は `=ᵐ[volume]` であって everywhere `=` でない**。型クラス前提なし |
| withDensity 表現 | `gaussianReal_of_var_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : gaussianReal μ v = volume.withDensity (gaussianPDF μ v)` | `Real.lean:203` | ✅ | **everywhere `=`**（measure 同士）。`v ≠ 0` 必須（`v=0` は `dirac μ`） |
| PDF 1 変数 measurable | `measurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDFReal μ v)` (`@[fun_prop]`) | `Real.lean:72` | ✅ | **点 `x` のみ**。mean 固定 |
| PDF 1 変数 strongly meas | `stronglyMeasurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) : StronglyMeasurable (gaussianPDFReal μ v)` (`@[fun_prop]`) | `Real.lean:77` | ✅ | 同上 |
| ENNReal PDF measurable | `measurable_gaussianPDF (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDF μ v)` (`@[fun_prop]`) | `Real.lean:186` | ✅ | 点 `x` のみ |
| 各 fibre ≪ vol | `gaussianReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : gaussianReal μ v ≪ volume` | `Real.lean:228` | ✅ | a.e.（vol）→ a.e.（gaussianReal）転送に使用（既に :383） |
| PDF 正値/有限 | `gaussianPDFReal_pos`, `gaussianPDF_pos`, `gaussianPDF_lt_top` | `Real.lean:61/170/174` | ✅ | toReal の log を扱う際の補助 |

### Q1 回答
- `(gaussianReal m v).rnDeriv volume` の陽形は **`rnDeriv_gaussianReal` (`:240`) が唯一**。結論は
  **`=ᵐ[volume]` (= `=ₐₛ`)** であって `=` でない。型クラス前提なし、`v` への条件なし
  （`v=0` は両辺 0 として処理）。
- `gaussianReal m v = volume.withDensity (gaussianPDF m v)` は **`gaussianReal_of_var_ne_zero` (`:203`)
  で everywhere `=`**、ただし **`v ≠ 0` 必須**（`v=0` は `Measure.dirac μ`）。AWGN では `N ≠ 0`
  (`hN`) なので問題なし。

### Q2 回答（決定的に否定）
- **`fun z : ℝ × ℝ => gaussianPDFReal z.1 N z.2` の joint measurable / continuous lemma は Mathlib に不在**。
  - loogle `Continuous (Function.uncurry ProbabilityTheory.gaussianPDFReal)` → **`Found 0 declarations`**。
  - 既存 `measurable_gaussianPDFReal` (`:72`) は `Measurable (gaussianPDFReal μ v)`（mean 固定の 1 変数）。
- **ただし自作は安価**：`gaussianPDFReal` の定義 (`:48`) は
  `(√(2*π*v))⁻¹ * rexp (-(x-μ)^2/(2*v))`。`(x, μ) ↦` で見ると `μ` は減算項に多項式的に入るだけ。
  `Measurable.const_mul (((measurable_fst.sub measurable_snd …)).pow … ).exp` あるいは
  `fun_prop`／`Continuous` 合成で **2 変数 `Measurable`（さらに `Continuous`）が直ちに構成可能**。
  これが Route B の自作素材（推定 5〜15 行）。`ENNReal.ofReal` で `gaussianPDF` 版も自動。

---

## B. measure-form vs kernel-form rnDeriv 在庫テーブル (Q4)

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| measure rnDeriv measurable（点のみ） | `Measure.measurable_rnDeriv (μ ν : Measure α) : Measurable <| μ.rnDeriv ν` | `MeasureTheory/Measure/Decomposition/Lebesgue.lean:100` | ✅ | **点引数のみ**。measure 引数 `μ` に対する measurability ではない |
| kernel rnDeriv joint measurable | `Kernel.measurable_rnDeriv (κ η : Kernel α γ) : Measurable (fun p : α × γ ↦ rnDeriv κ η p.1 p.2)` (`@[fun_prop]`) | `Probability/Kernel/RadonNikodym.lean:236` | ✅ | **joint だが kernel-form**。前提 `[IsFiniteKernel _]` 不要（生 measurability） |
| kernel→measure rnDeriv 橋 | `Kernel.rnDeriv_eq_rnDeriv_measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)` | `Probability/Kernel/RadonNikodym.lean:506` | ⚠️ | **`=ᵐ[η a]` のみ**。前提（下記）が致命的 |
| measure rnDeriv 連鎖律 | `Measure.rnDeriv_mul_rnDeriv'` | (RadonNikodym, 既に :146 で利用) | ✅ | density 砕きで使用済 |

### `Kernel.rnDeriv_eq_rnDeriv_measure` の型クラス前提（verbatim, **両方必要**）
`Probability/Kernel/RadonNikodym.lean` の `variable` スコープ:
- `variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {κ η : Kernel α γ}` (`:81`)
- `variable [IsFiniteKernel η]` (`:486`, `section Unique`)
- `variable [IsFiniteKernel κ] {a : α}` (`:504`)
- `lemma rnDeriv_eq_rnDeriv_measure : rnDeriv κ η a =ᵐ[η a] ∂(κ a)/∂(η a)` (`:506`)

⇒ **`[IsFiniteKernel κ]` と `[IsFiniteKernel η]` の両方を要求**。

### `Kernel.const` の有限性インスタンス（verbatim）
`Probability/Kernel/Basic.lean`:
- `instance const.instIsFiniteKernel {μβ : Measure β} [IsFiniteMeasure μβ] : IsFiniteKernel (const α μβ)` (`:197`)
- `instance const.instIsSFiniteKernel {μβ : Measure β} [SFinite μβ] : IsSFiniteKernel (const α μβ)` (`:201`)
- `instance const.instIsMarkovKernel {μβ : Measure β} [hμβ : IsProbabilityMeasure μβ] : IsMarkovKernel (const α μβ)` (`:205`)
- `lemma isSFiniteKernel_const [Nonempty α] {μβ : Measure β} : IsSFiniteKernel (const α μβ) ↔ SFinite μβ` (`:216`)

### Q4 回答
- **`Kernel.const ℝ volume` は `IsSFiniteKernel`**（`volume : Measure ℝ` は σ-finite ⇒ `SFinite` ⇒
  `const.instIsSFiniteKernel`）だが **`IsFiniteKernel` ではない**（`volume univ = ∞`、`IsFiniteMeasure volume`
  は偽）。
- `rnDeriv_eq_rnDeriv_measure` は **`[IsFiniteKernel η]` を要求**するため `η := Kernel.const ℝ volume` には
  **不適用**。これが文書化された障害（ContChannelMIDecomp.lean:407–414）の正体。
- **s-finite / σ-finite 版の `rnDeriv_eq_rnDeriv_measure` は Mathlib に不在**（`RadonNikodym.lean` 内の
  全 callsite が `[IsFiniteKernel]` スコープ内）。`Kernel.measurable_rnDeriv` (`:236`) は前提なしで joint
  measurable だが **kernel-form** で、それを measure-form に移すのにこの不在の橋が要る（循環）。
- measure-form rnDeriv の **joint** measurability も不在: loogle
  `Measurable (fun (_ : _ × _) => MeasureTheory.Measure.rnDeriv _ _ _)` → **`0 match`**。
  `gaussianReal` の mean 引数 measurability も不在: loogle
  `Measurable (fun (_ : ℝ) => ProbabilityTheory.gaussianReal _ _)` → **`Found 0 declarations`**。

---

## C. 消費側の使われ方（Q3 — DECISIVE）

`llr_compProd_prod_split` の **正確な signature**（`ContChannelMIDecomp.lean:171`、`section variable`
で `{p : Measure ℝ} [IsProbabilityMeasure p] {W : Kernel ℝ ℝ} [IsMarkovKernel W]` を継承）:

```lean
theorem llr_compProd_prod_split
    (q : Measure ℝ) [IsProbabilityMeasure q]
    (hWx_q : ∀ x, W x ≪ q) (hq_vol : q ≪ volume)
    (h_joint_ac : (p ⊗ₘ W) ≪ p.prod q)
    (h_meas_fibre : Measurable (fun z : ℝ × ℝ => (W z.1).rnDeriv volume z.2)) :   -- ★ argument in question
    (fun z => llr (p ⊗ₘ W) (p.prod q) z)
      =ᵐ[p ⊗ₘ W]
    (fun z => Real.log ((W z.1).rnDeriv volume z.2).toReal
                - Real.log (q.rnDeriv volume z.2).toReal)
```

→ 引数型は **`Measurable (...)`**（`AEMeasurable` ではない）、w.r.t. なし（everywhere）。

### `h_meas_fibre` の使用箇所（proof L195–199、verbatim）
```lean
    refine Measure.ae_compProd_of_ae_ae ?_ ?_
    · refine measurableSet_eq_fun ?_ ?_
      · exact (Kernel.measurable_rnDeriv W (Kernel.const ℝ q)).ennreal_toReal.log
      · exact (h_meas_fibre.ennreal_toReal.log).sub
          (((Measure.measurable_rnDeriv q volume).comp measurable_snd).ennreal_toReal.log)
```

- `Measure.ae_compProd_of_ae_ae` (`Probability/Kernel/Composition/MeasureCompProd.lean:113`) signature:
  `(hp : MeasurableSet {x | p x}) (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b)) : ∀ᵐ x ∂(μ ⊗ₘ κ), p x`
  → **第 1 引数は everywhere `MeasurableSet {x | p x}`**（a.e./null-measurable ではない）。
- `measurableSet_eq_fun` (`MeasureTheory/MeasurableSpace/Constructions.lean:1015`):
  `[MeasurableEq β] {f g : α → β} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x = g x}`
  → **両関数とも everywhere `Measurable`** を要求。
- `h_meas_fibre` は `g(z) := log ((W z.1).rnDeriv vol z.2).toReal` の everywhere measurability に直結。

### Q3 回答（決定的）
- **現状の `llr_compProd_prod_split` は `h_meas_fibre` を everywhere-`MeasurableSet` 生成に使う**
  ため、**そのまま `AEMeasurable` に緩めることは不可**。`Measure.ae_compProd_of_ae_ae` に
  `NullMeasurableSet`/`AEMeasurable` 版は **Mathlib に不在**（`CompProd.lean` の `ae_compProd_*`
  は全て everywhere `MeasurableSet` 前提）。
- ⇒ **a.e.-PDF 等式（`rnDeriv_gaussianReal`）だけでは `h_meas_fibre` を直接埋められない**。
  rnDeriv は a.e.-determined なので「fixed mean ごとの a.e. 等式」しか出ず、everywhere-joint
  `Measurable` には届かない（文書化された循環）。
- **ただし AWGN では脱出路あり（Route B）**: 真の fibre 密度 `g(x,y) := gaussianPDFReal x N y` は
  **everywhere `Measurable`（2 変数、自作 5〜15 行）** で、かつ `(W x).rnDeriv vol =ᵐ g(x,·)`
  ではなく `(gaussianReal x N).rnDeriv vol =ᵐ[vol] gaussianPDF x N` を **per-x** に持つ。
  これを使い、**消費側を `g` で書き換えた特化版 `llr_compProd_prod_split_gaussian` を作る**か、
  あるいは消費側引数を `(h_meas_fibre : Measurable g) (h_fibre_eq : ∀ x, (W x).rnDeriv vol =ᵐ[W x] g (x,·))`
  に **緩和（everywhere measurable な代理 `g` + per-fibre a.e. 等式）** すれば、`measurableSet_eq_fun`
  には `g` の everywhere measurability を渡し、a.e. 等式は `ae_compProd_of_ae_ae` の第 2 引数
  （`∀ᵐ a, ∀ᵐ b, ...`）側で消化できる。**この緩和は consumer の 3〜8 行改修で済む見込み**。

---

## D. residual #2（`h_int_fibre_joint`）在庫テーブル (Q5)

| 概念 | Mathlib / project API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| fibre log PDF integrable（per-x） | `integrable_log_gaussianPDFReal_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (m' : ℝ) (v' : ℝ≥0) : Integrable (fun y => Real.log (gaussianPDFReal m v y)) (gaussianReal m' v')` | `ContChannelMIDecomp.lean:358` | ✅(project) | 各 fibre `gaussianReal x N` 上の被積分関数積分可能性 |
| log rnDeriv integrable（per-x, measure-form） | `integrable_log_rnDeriv_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Integrable (fun y => Real.log ((gaussianReal m v).rnDeriv volume y).toReal) (gaussianReal m v)` | `ContChannelMIDecomp.lean:377` | ✅(project) | **既にこの lemma が a.e.-PDF 橋を per-x で実行している**（:382–391） |
| toReal PDF log 同定 | `toReal_gaussianPDF`, `rnDeriv_gaussianReal`, `gaussianReal_absolutelyContinuous` | `Real.lean:166/240/228` | ✅ | per-x 橋の素材（:382–390 で使用済） |
| compProd 上の積分→Fubini | `Measure.integral_compProd` / `MeasureTheory.Integrable.compProd` 系 | `Probability/Kernel/Composition/...` | ✅ | per-fibre integrable + bound から joint integrable を組む |
| 2 次モーメント integrable | `integrable_sq_sub_gaussianReal (m m' : ℝ) (v' : ℝ≥0)` | `ContChannelMIDecomp.lean:341` | ✅(project) | log PDF = c₀ + c₁(y−m)² 展開の有限性 |

### Q5 回答
- residual #2 は **rnDeriv を PDF に同定できれば素材は揃う**。具体的合成:
  1. `(W z.1) = gaussianReal z.1 N`（`awgnChannel_apply`, rfl）。
  2. per-fibre: `integrable_log_rnDeriv_gaussianReal z.1 hN` が
     `Integrable (fun y => log ((gaussianReal z.1 N).rnDeriv vol y).toReal) (gaussianReal z.1 N)` を与える
     （**既存・genuine**）。
  3. これを **`p ⊗ₘ W` 上の joint integrability** に持ち上げるには `Measure.integrable_compProd_iff`
     系 + per-fibre bound（log PDF = 定数 + 2 次形式、`integrable_sq_sub_gaussianReal`）が必要。
     被積分関数は z.1 にも依存するため、`integral_compProd`/`Integrable.compProd` の measurability
     前提（= residual #1 と同じ joint-measurable 障害）に再び突き当たる。
- ⇒ **residual #2 は residual #1（joint measurability）が解ければほぼ機械的**。両者が「同一の
  Mathlib gap に pin されている」という文書化（:409）と整合。Route B で #1 を解くと #2 も同経路
  （everywhere-measurable PDF 代理 `g` 上で `integral_compProd` を発火）で落ちる。

---

## 主要前提条件ボックス（前提事故が起きやすい lemma）

- **`rnDeriv_gaussianReal` (`Real.lean:240`)**: 結論は **`=ₐₛ`（= `=ᵐ[volume]`）であって everywhere `=` ではない**。
  ここを everywhere と誤認すると joint-`Measurable` が一見作れてしまうが実際は作れない（gap の本質）。
- **`gaussianReal_of_var_ne_zero` (`Real.lean:203`)**: everywhere `=` だが **`v ≠ 0` 必須**。AWGN は `hN : N ≠ 0` で OK。
- **`Kernel.rnDeriv_eq_rnDeriv_measure` (`RadonNikodym.lean:506`)**: **`[IsFiniteKernel κ]` AND `[IsFiniteKernel η]`**。
  `η = Kernel.const ℝ volume` は `IsSFiniteKernel` 止まりで **適用不可**。
- **`Measure.ae_compProd_of_ae_ae` (`MeasureCompProd.lean:113`)**: 第 1 引数は **everywhere `MeasurableSet`**。
  null-/AE- 版なし ⇒ consumer の `AEMeasurable` 緩和を阻む（Q3 の核）。
- **`measurableSet_eq_fun` (`Constructions.lean:1015`)**: `[MeasurableEq β]` + 両関数 everywhere `Measurable`。
- **`Measure.measurable_rnDeriv` (`Lebesgue.lean:100`)**: `(μ ν : Measure α)` 固定の **点引数のみ** measurable。
  measure / mean パラメータに対する measurability ではない。

---

## 自作が必要な要素（優先度順）

1. **`measurable_gaussianPDFReal_uncurry`（2 変数 joint measurability）** — *最優先・最安*。
   `Measurable (fun z : ℝ × ℝ => gaussianPDFReal z.1 N z.2)`（さらに `Continuous` も可）。
   実装: 定義 `:48` を展開し `fun_prop`／`Measurable.const_mul (… .exp)` 合成。`ENNReal.ofReal` で
   `gaussianPDF` 版も導出。**工数: 5〜15 行**。落とし穴: `√(2*π*v)` は定数（`x,μ` に非依存）なので
   `const_mul` で外せる — `μ` が入るのは `(x-μ)^2` 項のみ。
2. **consumer の緩和 / 特化** — `llr_compProd_prod_split` を AWGN PDF 代理 `g` で書ける形に。
   2 案: (a) **特化版** `llr_compProd_prod_split_gaussian`（`W = awgnChannel`, `g = gaussianPDFReal`
   を直書き、everywhere-measurable `g` を `measurableSet_eq_fun` に渡す）、(b) **汎用緩和**
   （引数を `(g : ℝ×ℝ → ℝ) (hg_meas : Measurable g) (hg_eq : ∀ x, (W x).rnDeriv vol =ᵐ[W x] fun y => g (x,y))`
   に置換）。**工数: (a) 30〜60 行 / (b) 20〜40 行（既存 proof の measurableSet 構成 3〜8 行差替）**。
   落とし穴: `ae_compProd_of_ae_ae` の第 2 引数（`∀ᵐ a, ∀ᵐ b`）で per-fibre a.e. 等式
   `(W x).rnDeriv vol =ᵐ g(x,·)` を消化する筋に組み替える必要（Kernel.rnDeriv 経路を捨てる）。
3. **`h_meas_fibre` 自体は「埋まらない」と受容** — measure-form rnDeriv の everywhere joint
   measurability は **作れない**（rnDeriv が a.e.-determined）。代わりに上記 2 で消費側を
   PDF 代理 `g` に切り替えるのが正攻法。
4. **residual #2 の joint integrability 接続** — `integrable_log_rnDeriv_gaussianReal`（per-x, 既存）
   + `integral_compProd`/`Integrable.compProd` を、2 で作る everywhere-measurable 代理上で発火。
   **工数: 20〜50 行**。落とし穴: `integrable_compProd_iff` は AEStronglyMeasurable（joint）を要求 ⇒
   ここでも代理 `g` の everywhere measurability が効く。

---

## 撤退ラインへの距離

親計画 `awgn-mi-decomp-plan.md`（`§段 2 AWGN instance`、L155–172）の見立て:
> 段 2 (AWGN instance) 🟢 unconditional 見込み。honest #1–#6 は全て Gaussian 事実で discharge 可。
> Phase 7 で `rnDeriv_gaussianReal` で `(W x).rnDeriv vol = gaussianPDFReal x N` を同定。

**判定: 撤退ラインに「触れるが、Route B で発動を回避できる」。**

- 親計画は「`rnDeriv_gaussianReal` で `(W x).rnDeriv vol = gaussianPDFReal x N` を同定」と
  **everywhere `=` を暗黙に仮定**していたが、実際は **`=ᵐ[vol]`** であり、**joint-`Measurable` には
  届かない**（本調査の最重要発見）。この点で親計画の Phase 7 見積りは楽観的すぎた。
- ただし **撤退（honest pass-through 据え置き = Route C）は不要**。Route B（everywhere-measurable
  PDF 代理 `g` + consumer 緩和）で genuine discharge が **追加 ~60〜120 行**で達成可能。
- **新規撤退ライン提案（縮退案）**: 「Route B の consumer 緩和（自作要素 2）が 1〜2 日で書けない
  場合は、`h_meas_fibre`/`h_int_fibre_joint` を **AWGN 専用 named hypothesis のまま** publish し
  （現状）、Route B を別 follow-up plan `awgn-rnderiv-discharge-plan.md` に切り出す」。
  これは現状（2 honest hyp 残）からの **後退ではなく現状維持** なので安全。

---

## 着手 skeleton（`Common2026/Shannon/ContChannelMIDecomp.lean` 拡張、Route B）

```lean
-- 既存 imports に追加不要（Gaussian/Real, Kernel/Composition は既に間接 import 済のはず。
-- 不足時のみ): import Mathlib.Probability.Distributions.Gaussian.Real

namespace InformationTheory.Shannon.AWGN
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

/-- **2-variable (joint) measurability of the Gaussian pdf** (Route B linchpin).
`(x, y) ↦ gaussianPDFReal x N y` is measurable as a map `ℝ × ℝ → ℝ`. From the closed
form `(√(2πN))⁻¹ * exp(−(y−x)²/(2N))`; `fun_prop` over `measurable_fst`/`measurable_snd`. -/
theorem measurable_gaussianPDFReal_uncurry (N : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ => gaussianPDFReal z.1 N z.2) := by
  sorry

/-- ENNReal version (joint measurable `gaussianPDF`). -/
theorem measurable_gaussianPDF_uncurry (N : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ => gaussianPDF z.1 N z.2) := by
  sorry

/-- **AWGN-specialized Bayes density split** (consumer relaxation, Route B).
Replaces the un-fillable measure-form `h_meas_fibre` by the everywhere-measurable pdf
proxy `g := gaussianPDFReal · N ·` plus the per-fibre a.e. identity from `rnDeriv_gaussianReal`. -/
theorem llr_compProd_prod_split_gaussian
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0) (hPN : P.toNNReal + N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N)
    (h_out : IsAwgnOutputGaussian P N h_meas) :
    (fun z => InformationTheory.Shannon.ChannelCoding.llr
        (gaussianReal 0 P.toNNReal ⊗ₘ awgnChannel N h_meas)
        ((gaussianReal 0 P.toNNReal).prod (outputDistribution _ (awgnChannel N h_meas))) z)
      =ᵐ[gaussianReal 0 P.toNNReal ⊗ₘ awgnChannel N h_meas]
    (fun z => Real.log (gaussianPDFReal z.1 N z.2)
                - Real.log ((outputDistribution _ (awgnChannel N h_meas)).rnDeriv volume z.2).toReal) := by
  sorry

/-- residual #2 discharged via per-fibre integrability + compProd lift. -/
theorem integrable_log_fibre_pdf_compProd
    (P : ℝ) (N : ℝ≥0) (hN : N ≠ 0)
    (h_meas : IsAwgnChannelMeasurable N) :
    Integrable (fun z => Real.log (gaussianPDFReal z.1 N z.2))
      (gaussianReal 0 P.toNNReal ⊗ₘ awgnChannel N h_meas) := by
  sorry

end InformationTheory.Shannon.AWGN
```

---

## FEASIBILITY VERDICT

**Route B（AWGN 専用 `gaussianPDF` everywhere-measurable 代理 + consumer 緩和）が最も安く、かつ
genuine に達成可能。** Route A（汎用 s-finite kernel rnDeriv 橋）は Mathlib に s-finite 版
`rnDeriv_eq_rnDeriv_measure` が無く、`Kernel.const ℝ volume` が `IsFiniteKernel` を満たさない以上、
**Mathlib upstream PR 級の作業（新 lemma + 既存 `[IsFiniteKernel]` 証明の s-finite 一般化、数百行）**
になり対費用効果が悪い。Route C（honest 据え置き）は後退で不要。

Route B が成立する根拠: AWGN の真の fibre 密度は **閉形式 `gaussianPDFReal x N y` で、2 変数
everywhere `Measurable`（自作 5〜15 行）**。Q3 で確定した障害は「`Measure.ae_compProd_of_ae_ae` が
everywhere-`MeasurableSet` を要求し、measure-form rnDeriv は a.e.-determined なので everywhere-joint
`Measurable` を直接作れない」点だが、これは **measurableSet 構成に rnDeriv ではなく everywhere-measurable
代理 `g` を渡し、a.e. 等式は `ae_compProd_of_ae_ae` の `∀ᵐ a, ∀ᵐ b` 側で消化する**よう consumer を
組み替えれば回避できる（`rnDeriv_gaussianReal` の per-x a.e. 等式 + `gaussianReal_absolutelyContinuous`
は既に `integrable_log_rnDeriv_gaussianReal` で実証済の経路）。residual #2 も同代理上で
`integral_compProd` 発火に帰着し、per-fibre `integrable_log_rnDeriv_gaussianReal`（既存）から落ちる。

**行数見積り（中央値）**: joint-measurable PDF ~10 行 + consumer 緩和/特化 ~30〜60 行 +
residual #2 接続 ~20〜50 行 = **合計 ~60〜120 行**、1〜2 日。**最大リスク**は consumer 緩和で
`Kernel.rnDeriv` 経路（現 proof の `measurableSet_eq_fun` 第 1 関数が `Kernel.measurable_rnDeriv`）を
PDF 代理経路に組み替える plumbing。これが想定超過なら新規撤退ライン（follow-up plan へ切り出し、
現状の 2 honest hyp 維持）で安全に逃げられる。
