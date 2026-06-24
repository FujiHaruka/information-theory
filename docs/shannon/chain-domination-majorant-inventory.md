# `_chain_domination` Gaussian-tail majorant — Mathlib/repo API 在庫

> 対象 sorry: `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:133-144`
> `debruijnIdentityV2_holds_assembled_chain_domination` (`@residual(plan:epi-debruijn-pertime-closure)`)。
> 親計画: `docs/shannon/epi-debruijn-pertime-closure-plan.md` (§Phase 5-G L-PT-γ)。
> docs-only 調査。Lean compile / コード編集 / commit はしていない。

## 一行サマリ

majorant 構成に要る **汎用 API（積の可積分化・多項式×Gaussian integrability・log 上界）は ~90% Mathlib 既存** だが、被支配量の **2 因子それぞれの explicit closed-form 上界**（① 畳み込み密度 `p_s x` の下界 → `-log p_s x` の多項式上界、② `deriv(deriv(convDensityAdd ...))` の Gaussian-tail 上界）は **Mathlib にも repo にも不在**。この 2 つが真の self-written gap で、majorant 構成コストの核心（plan 見積 ~120-180 行）。撤退ライン発動: **no**（このまま `plan:` 残置が正当、wall 化不要）。

## 主定理の最終形（再掲）

```lean
private theorem debruijnIdentityV2_holds_assembled_chain_domination
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      (∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖(- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩) x) - 1)
            * ((1/2) * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩))) x)‖
          ≤ bound x) := by sorry
```

被支配量 = **積** `LogFactor(s,x) · ((1/2)·Hess(s,x))`:
- `LogFactor(s,x) := - log (p_s x) - 1`、`p_s x := convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩) x`。`s ∈ Ioo(t/2,2t)` で `s > t/2 > 0`。`p_s x → 0`（裾）で `log → -∞`、`-log p_s x ~ x²/(2s)`（多項式増大）。
- `Hess(s,x) := deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s,_⟩))) x` = `∂²_x p_s x`。Gaussian 裾で超多項式減衰。

擬 Lean 戦略（majorant 構成）:
```text
-- 1. s を Ioo(t/2,2t) で固定窓に閉じ込め（s>0, s有界、prefactor有界）→ s一様定数を取る
-- 2. Hess(s,x) = ∫ y, pX y · ∂²_x g_s(x-y) を heat-eq atom STEP D の同定形で書く
--    ∂²_x g_s(u) = g_s(u)·(u²/s² - 1/s)  (heatFlow_..._kernel_x_deriv2)
-- 3. |Hess(s,x)| ≤ ∫ pX y · prefactor·exp(-(x-y)²/2s)·((x-y)²/s²+1/s)  -- Gaussian超多項式上界 [GAP②]
-- 4. p_s x ≥ (lower Gaussian bound)  ⇒  -log p_s x ≤ poly(x)            -- 畳込下界    [GAP①]
--    log_le_sub_one_of_pos / one_sub_inv_le_log_of_pos で log を多項式に変換
-- 5. bound x := poly(x) · (Gaussian-tail of Hess)  -- 積。 x² 多項式 × Gaussian = integrable
--    integrable_rpow_mul_exp_neg_mul_sq で integrable 化
-- 6. Integrable.mono' で被支配量 ≤ bound を ∃ 提示
```

---

## A. 積の可積分化 / 有界因子吸収（汎用、全 ✅ 既存）

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| 可積分 × 有界 = 可積分 | `theorem Integrable.mul_bdd {f g : α → 𝕜} {c : ℝ} (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ) (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ c) : Integrable (fun x => f x * g x) μ` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1070` | ✅ 既存 | repo 先例 (`PerTime.lean:170`) と同じ。Gaussian 因子を prefactor で有界化して積 integrable 化 |
| 有界 × 可積分 = 可積分 | `theorem Integrable.bdd_mul {f g : α → 𝕜} {c : ℝ} (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) : Integrable (fun x => f x * g x) μ` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1063` | ✅ 既存 | `mul_bdd` の左右逆。被支配量の因子順に応じて使い分け |
| majorant による可積分性 (核心) | `theorem Integrable.mono' {f : α → β} {g : α → ℝ} (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : Integrable f μ` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:100` | ✅ 既存 | `bound` が integrable & 被支配量 ≤ bound を示せれば即終了。**ただし本 sorry は `Integrable bound` を ∃ 提示するだけなので、被支配量自身の Integrable は不要 — `bound` 自身が integrable であればよい**（本定理は domination majorant の存在のみ要求） |
| `‖f‖ ≤ g` 経由 (別形) | `theorem Integrable.mono'_enorm {f : α → ε} {g : α → ℝ≥0∞} (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ g a) : Integrable f μ` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:96` | ✅ 既存 | enorm 版。今回は不要、reference のみ |

注意（型クラス）: `Integrable.mul_bdd` / `bdd_mul` は `𝕜` が `[RCLike 𝕜]`（または NormedRing/NormedField — 該当 section の `variable` で `[NormedAddCommGroup 𝕜] [NormedRing 𝕜] ...`）を要求。`ℝ` で自動充足。`α` 側は `[MeasurableSpace α]` + `μ : Measure α`。本ケースは `α = ℝ`, `μ = volume` で全充足。

---

## B. 多項式 × Gaussian の Lebesgue integrability（汎用、全 ✅ 既存）

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `x^s·exp(-b x²)` 可積分 (全 ℝ) | `theorem integrable_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) : Integrable fun x : ℝ => x ^ s * exp (-b * x ^ 2)` | `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:109` | ✅ 既存 | majorant の最終 integrability。`s = 2` (= `x²·Gaussian`)、`s = 0` 等で使う。**`x ^ s` は `rpow`**（`s : ℝ`）。`Found 1` (loogle) |
| `x·exp(-b x²)` 可積分 | `theorem integrable_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) : Integrable fun x : ℝ => x * exp (-b * x ^ 2)` | `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:147` | ✅ 既存 | 1次項。`integrable_rpow_..._sq hb (by simp : (-1:ℝ)<1)` から導出 |
| `exp(-b x²)` 可積分 | `theorem integrable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) : Integrable fun x : ℝ => exp (-b * x ^ 2)` | `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:128` | ✅ 既存 | 0次項。基礎ブロック |
| 半直線版 (補助) | `theorem integrableOn_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) : IntegrableOn (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) (Ioi 0)` | `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean:104` | ✅ 既存 | `Ioi 0` 限定。全直線版が直接使えるので通常不要 |

注意: `integrable_pow_mul_gaussian` は **存在しない**（loogle: `unknown identifier`、`Found 0`）。`pow`（`ℕ`指数）版は無く、`rpow` 版 `integrable_rpow_mul_exp_neg_mul_sq` を `s := (n:ℝ)` で使う。`x²` を作るには `x^(2:ℝ) = x^2` の `rpow_natCast` / `rpow_two` 橋渡しが要る（軽微、Mathlib 内 `rpow_two` 既存）。`b` には variance `1/(2s)` 由来の正定数を入れる（`s ∈ Ioo(t/2,2t)` で `b = 1/(2·2t) = 1/(4t) > 0` 等、s一様下界から）。

---

## C. `log` の多項式上界（汎用、全 ✅ 既存）— `-log p_s x` を抑える

| 概念 | Mathlib API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `log x ≤ x - 1` | `theorem Real.log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ x - 1` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:306` | ✅ 既存 | log の上界。**ただし `-log` の制御には下向き不等式が要る**（下記） |
| `1 - x⁻¹ ≤ log x` | `lemma Real.one_sub_inv_le_log_of_pos {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ log x` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:311` | ✅ 既存 | **これが核心**: `- log x ≤ x⁻¹ - 1`。`x = p_s x` に適用 → `-log p_s x ≤ (p_s x)⁻¹ - 1`。`p_s x ≥ c·exp(-x²/c')` 下界（GAP①）があれば `(p_s x)⁻¹ ≤ c⁻¹·exp(x²/c')` で **超多項式爆発**になる点に注意（下記落とし穴） |
| `-x⁻¹ ≤ log x` | `lemma Real.neg_inv_le_log {x : ℝ} (hx : 0 ≤ x) : -x⁻¹ ≤ log x` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:321` | ✅ 既存 | `log` の下界（= `-log` 上界 `log x⁻¹ ≤ ...`）。reference |
| `x + 1 ≤ exp x` | `theorem Real.add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x` | `Mathlib/Analysis/Complex/Exponential.lean:646` | ✅ 既存 | `log_le_sub_one_of_pos` の素 |

**落とし穴（重大）**: `one_sub_inv_le_log_of_pos` 経由で `-log p_s x ≤ (p_s x)⁻¹ - 1` を使うと、`p_s x` の下界が Gaussian `c·exp(-x²/c')` のとき `(p_s x)⁻¹ ~ exp(+x²/c')` で **majorant が非可積分に爆発**する。正しい majorant は **`-log p_s x ≤ (1/2)log(2π s) + x²/(2s) + |log上界|` の直接多項式上界**（`p_s x ≥ c·exp(-x²/2s)` の log を取って `-log p_s x ≤ -log c + x²/(2s)`）。これは `Real.log_le_log` (`Basic.lean:150`) + `Real.log_exp` + 下界 GAP① を組み合わせる必要があり、`one_sub_inv` 直適用は誤路。majorant 設計時に **`-log` を `x²` 多項式に落とす経路は「下界の log を取る」であって「inv 上界」ではない**。

---

## D. 畳み込み密度 `p_s x` の下界（GAP①、❌ Mathlib/repo 不在）

| 概念 | Mathlib/repo API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| `gaussianPDFReal` 正値 | `lemma ProbabilityTheory.gaussianPDFReal_pos (μ : ℝ) (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) : 0 < gaussianPDFReal μ v x` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:61` | ✅ 既存 | 核 factor の正値。`p_s x > 0` の素材だが、**畳込全体の explicit 下界ではない** |
| `gaussianPDFReal` 非負 | `lemma ProbabilityTheory.gaussianPDFReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ gaussianPDFReal μ v x` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:66` | ✅ 既存 | 同上 |
| `gaussianPDFReal` 上界 (prefactor) | `private theorem gaussianPDFReal_le_prefactor (μ : ℝ) (v : ℝ≥0) (x : ℝ) : gaussianPDFReal μ v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹` | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:115` | ✅ 既存 (repo, `@audit:ok`) | **上界のみ**（exp ≤ 1）。下界には使えない |
| **畳込密度の下界 `p_s x ≥ c·exp(-(x²)/c')`** | — | — | ❌ **不在** (Mathlib + repo 共に) | **GAP①**。loogle `MeasureTheory.convolution, \|- _ ≤ _` → `convolution_mono_right_of_nonneg` / `dist_convolution_le` のみ（畳込密度の Gaussian 下界なし）。`gaussianPDFReal` の下界 lemma も無い |
| `def convDensityAdd` | `noncomputable def convDensityAdd (pX pY : ℝ → ℝ) : ℝ → ℝ := fun z => ∫ x, pX x * pY (z - x) ∂volume` | `InformationTheory/Shannon/EPIConvDensity.lean:40` | ✅ 既存 (定義) | 下界証明の対象 |

**GAP① 詳細**: `p_s x = ∫ y, pX y · g_s(x-y)` の下界が要る。教科書的下界は「`pX` がある有界区間に質量を持つ ⇒ `g_s` の値で下から押さえる」で `p_s x ≥ c·exp(-(|x|+R)²/2s)` 型。だが Mathlib に畳込下界 lemma が無く、repo にも無い。これを self-write する必要がある（`gaussianPDFReal_pos` + `integral_mono` + `pX` の質量正値から構成、~40-60 行）。**`pX` が full-support でないと一様下界が取れない退化点に注意** — `pX` の質量集合に依存する `c, R` を ∃ で出すか、`hpX_int` から probability density である事実（質量 1）を使う。

---

## E. `deriv (deriv (convDensityAdd ...))` の閉形 & Gaussian-tail 上界（GAP②、部分 ✅ / 核心 ❌）

| 概念 | repo API | file:line | 状態 | 扱い |
|---|---|---|---|---|
| 畳込 2nd-deriv の積分同定 (heat-eq atom STEP D) | `theorem heatFlow_density_heat_equation (pX pPath pathDeriv1 pathDeriv2 : ℝ → ℝ → ℝ) (hpPath : ∀ (σ : ℝ) (hσ : 0 < σ), pPath σ = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩)) (hpathDeriv1 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pPath σ ξ) (pathDeriv1 σ y) y) (hpathDeriv2 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pathDeriv1 σ ξ) (pathDeriv2 σ y) y) {s : ℝ} (hs : 0 < s) (x : ℝ) (boundσ : ℝ → ℝ) (hboundσ_int : Integrable boundσ volume) ... (boundξ1 boundξ2 : ℝ → ℝ) ... : HasDerivAt (fun σ : ℝ => pPath σ x) ((1/2) * pathDeriv2 s x) s` | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:422` | ✅ 既存 (`@audit:ok`) | STEP D が `pathDeriv2 s x = ∫ y, pX y · g_s(x-y)·((x-y)²/s² - 1/s)` を同定（行 607-614）。**この同定形を流用すれば `deriv(deriv(...))` の積分形が手に入る** が、`pathDeriv2` を `deriv(deriv(...))` に橋渡しする `HasDerivAt.deriv` 経由の identification が要（plumbing） |
| kernel 2nd-deriv 閉形 | `theorem heatFlow_density_heat_equation_kernel_x_deriv2 {σ : ℝ} (hσ : 0 < σ) (u : ℝ) : HasDerivAt (fun ξ : ℝ => heatFlow_density_heat_equation_kernel σ ξ * (-(ξ / σ))) (heatFlow_density_heat_equation_kernel σ u * (u ^ 2 / σ ^ 2 - 1 / σ)) u` | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:290` | ✅ 既存 (`@audit:ok`) | `∂²_u g_σ(u) = g_σ(u)·(u²/σ² - 1/σ)`。被積分核の closed form。上界 `\|...\| ≤ prefactor·exp·(u²/σ²+1/σ)` の素 |
| kernel σ↔spatial agreement | `theorem heatFlow_density_heat_equation_kernel_eq {σ : ℝ} (hσ : 0 < σ) (u : ℝ) : heatFlow_density_heat_equation_kernel σ u = gaussianPDFReal 0 ⟨σ, hσ.le⟩ u` | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:254` | ✅ 既存 (`@audit:ok`) | explicit kernel ↔ `gaussianPDFReal` 橋渡し |
| **`\|∂²_x p_s x\| ≤ Gaussian-tail majorant(s,x)`** | — | — | ❌ **不在** | **GAP②**。`∫ y, pX y·g_s(x-y)·((x-y)²/s²-1/s)` の `x` についての Gaussian-tail 上界（`s`一様、`Ioo(t/2,2t)`）を `\|...\| ≤ C·exp(-x²/c')·poly(x)` で出す lemma が無い。kernel closed form（E2）+ `Integrable.mul_bdd`（A）+ `integral_mono`/三角不等式から self-write（~50-80 行） |

**GAP② 詳細**: 被支配量の Hess 因子を `deriv(deriv(convDensityAdd ...))` のまま扱うと裸の `deriv` で上界が取れない。まず `heatFlow_density_heat_equation` STEP D の同定形（`pathDeriv2 s x = ∫ y, pX y · g_s(x-y)·((x-y)²/s²-1/s)`）に `deriv(deriv(...)) = pathDeriv2 s x` を `HasDerivAt.deriv` で橋渡しし（atom が `pathDeriv1/2` を抽象 `ℝ→ℝ→ℝ` で取るので、`pPath := convDensityAdd ...`、`pathDeriv1 := deriv (convDensityAdd ...)`、`pathDeriv2 := deriv (deriv (convDensityAdd ...))` を instantiate する必要 — それ自体が `hpathDeriv1`/`hpathDeriv2` の `HasDerivAt` precondition discharge を要求し、これは plan L-PT-δ と同じ full-support C¹ wall に触れる）、その後 `|∫| ≤ ∫|·|` + kernel 上界 で Gaussian-tail majorant に落とす。

---

## F. `∃ bound` 構成パターン precedent（✅ atom 内に実例あり）

| 概念 | repo precedent | file:line | 状態 | 扱い |
|---|---|---|---|---|
| 同型 domination hyp 群の消費形 | `heatFlow_density_heat_equation` の `boundσ`/`boundξ1`/`boundξ2` 群 (`hbσ`/`hbξ1`/`hbξ2`: `∀ᵐ y, ∀ σ∈Ioo(s/2,2s), ‖pX y·...‖ ≤ boundσ y`) | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:436-468` | ✅ 既存 (`@audit:ok`) | **これは「`bound y` を仮説で受け取って `hasDerivAt_integral_of_dominated_loc_of_deriv_le` に渡す」消費側**。本 sorry は逆に **`∃ bound` を構成して供給する側**。供給側 precedent は atom 内には無い（atom は供給を呼び元に委ねている = まさに L-PT-γ の残コスト）。本 sorry が atom の `boundσ`/`bound...` の供給責任を負う |
| ガウス被積分核の `‖·‖ ≤ c` 有界化 | `pPath_eq_convDensityAdd_lconvolution_bridge` 内 `hint` (`hpX_int.mul_bdd ... gaussianPDFReal_le_prefactor`) | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:168-175` | ✅ 既存 (`@audit:ok`) | **積 integrable 化の repo 既製レシピ**。majorant の Gaussian 因子吸収をこれと同型で組める |
| 並列積分の domination 構成 | `hasDerivAt_integral_of_dominated_loc_of_deriv_le {F F' : ℝ → α → E} (bound : α → ℝ) (hF'_int)... ` | `Mathlib/Analysis/Calculus/ParametricIntegral.lean:289` | ✅ 既存 | gateway。bound を `∃` で受ける形は呼び元（= 本 sorry）が満たす |

---

## 主要前提条件ボックス（前提事故注意）

- **`Integrable.mul_bdd` / `bdd_mul`** (`Integrable.lean:1070`/`1063`): `f`/`g : α → 𝕜`、`𝕜` は当該 section の NormedRing 系（`ℝ` 充足）。有界側に `AEStronglyMeasurable` + `∀ᵐ, ‖·‖ ≤ c` の **2 条件**。可測性を落とすと型エラー。`c` は明示引数（`(c := ...)`）で渡すのが repo 慣行（`PerTime:170`）。
- **`integrable_rpow_mul_exp_neg_mul_sq`** (`GaussianIntegral.lean:109`): 指数は **`rpow`**（`x ^ (s:ℝ)`、`hs : -1 < s`）かつ **`b > 0`**。`x^2`（`ℕ`乗）を作るには `rpow_two`/`rpow_natCast` 橋渡し必須。`pow` 版は存在しない。
- **`one_sub_inv_le_log_of_pos`** (`Log/Basic.lean:311`): `0 < x` 必須。**`-log` の inv 上界経由は majorant 爆発（落とし穴 §C）**。正路は「下界の log を取る」= `log_le_log` + `Real.log_exp`。
- **`heatFlow_density_heat_equation`** (`PerTime.lean:422`): `pPath`/`pathDeriv1`/`pathDeriv2` を抽象 `ℝ→ℝ→ℝ` で取り、3 definitional pin (`hpPath`/`hpathDeriv1`/`hpathDeriv2`) + σ/spatial domination 群 (`boundσ`/`boundξ1`/`boundξ2` + 各 `Integrable`/`AEStronglyMeasurable`/`∀ᵐ ≤ bound`) を要求。これらは **regularity precondition**（load-bearing ではない、`@audit:ok` 確認済）。本 sorry が atom の 2nd-deriv 同定形を借りるなら、これら domination 群（特に GAP②）を自前供給する責任が連鎖する。
- **`gaussianPDFReal_pos`** (`Gaussian/Real.lean:61`): `hv : v ≠ 0` 必須。`s > 0` なので `⟨s,_⟩ ≠ 0` を `NNReal.eq` 経由で出す（atom 内 `hv_ne` 先例 `PerTime:207`）。

---

## 自作が必要な要素（優先度順）

1. **【最優先・核心】GAP① 畳込密度 Gaussian 下界 `p_s x ≥ c·exp(-(x²)/c')`** (~40-60 行)
   推奨: `pX` の質量（`hpX_int` の probability density 性、`∫ pX = 1`）から「`pX` が正質量を持つ有界区間 `[−R,R]`」を取り、`p_s x = ∫ pX y·g_s(x-y) ≥ ∫_{[−R,R]} pX y·g_s(x-y) ≥ (inf_{y∈[−R,R]} g_s(x-y))·(mass)` で下から押さえる。`g_s(x-y) ≥ prefactor·exp(-(|x|+R)²/2s)`。落とし穴: `pX` が full-support でないと `c` が `pX` 依存 → `∃ c R` で出す。`integral_mono_of_nonneg` + `gaussianPDFReal_pos`。`s ∈ Ioo(t/2,2t)` で `s` 一様化（prefactor/exp の s 依存を `s ≤ 2t`/`s ≥ t/2` で抑える）。
2. **【最優先・核心】GAP② Hess の Gaussian-tail 上界 `|∂²_x p_s x| ≤ C·exp(-x²/c')·poly(x)`** (~50-80 行)
   推奨: `heatFlow_density_heat_equation` STEP D 同定形（`PerTime:607`）の `∫ y, pX y·g_s(x-y)·((x-y)²/s²-1/s)` を借用 → `|∫| ≤ ∫ pX y·g_s(x-y)·|(x-y)²/s²-1/s|` → kernel 上界 (`gaussianPDFReal_le_prefactor` E2 系) で Gaussian-tail。`deriv(deriv(...)) = pathDeriv2` の橋渡しで atom の `hpathDeriv1/2` precondition（full-support C¹）に触れる ⇒ **plan L-PT-δ wall と共有**。
3. **【中】log-多項式変換 wiring** (~20-30 行): GAP① の下界 → `-log p_s x ≤ -log c + x²/(2s)`（`log_le_log` + `Real.log_exp` + `log_mul`）。落とし穴 §C を踏まない正路。
4. **【低】最終 majorant 組立 + `Integrable bound`** (~30-40 行): `bound x := (poly(x))·(C·exp(-x²/c')·poly(x))` を `integrable_rpow_mul_exp_neg_mul_sq` で integrable 化（`rpow_two` 橋渡し含む）。`∀ᵐ x, ∀ s∈Ioo, ‖積‖ ≤ bound x` を三角不等式 + GAP①②で。

工数感: 全体 ~150-200 行（plan 見積 120-180 と整合、橋渡し plumbing 込みで上振れ）。

---

## Mathlib 壁の列挙（真の不在）

| wall | 内容 | loogle 確認 | 集約候補 |
|---|---|---|---|
| 畳込密度 Gaussian 下界 (GAP①) | `convDensityAdd pX g_s x ≥ c·exp(-x²/c')` | `MeasureTheory.convolution, \|- _ ≤ _` → `convolution_mono_right_of_nonneg`/`dist_convolution_le` のみ（下界なし）。`gaussianPDFReal` 下界 lemma も `Found 0` | repo 内製。畳込下界は **EPI/Fisher family 横断で再利用価値** — 共有 sorry 補題化推奨（`docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」）。ただし `plan:` 分類のまま（PR 級だが same-family closeable、新 wall 名は不要） |
| Hess Gaussian-tail 上界 (GAP②) | `\|deriv(deriv(convDensityAdd ...))\| ≤ Gaussian-tail` | `Integrable (fun _ => _ ^ _ * gaussianPDFReal _ _ _)` 直接 lemma なし。畳込 2nd-deriv 上界 `Found 0` | repo 内製。L-PT-δ（IBP step の full-support C¹ wall）と precondition 共有 — **集約推奨**（`debruijnIdentityV2_holds_assembled_chain_ibp_fisher_ibp_step` と同じ `pathDeriv2` 同定 plumbing を共有 helper に切り出すと二重実装回避） |

両 GAP とも **`plan:epi-debruijn-pertime-closure` の射程内**（same-family の analytic plumbing、Mathlib に new-concept wall を立てる必要はない）。`wall:fisher-finiteness`（`Assembly:177`）のような「Mathlib に概念自体が無い」型ではなく、「explicit closed-form 上下界を自分で書く」型の作業 gap。

---

## 撤退ラインへの距離

- 親計画 `epi-debruijn-pertime-closure-plan.md` の撤退ライン（L-PT-γ/δ が PR 級に膨れた場合の縮退）に **触れるが発動しない**。本 sorry は既に `@residual(plan:...)` の正規撤退口にあり、signature は本来証明したい形（`∃ bound, Integrable ∧ ∀ᵐ domination`）を保持、load-bearing hyp 無し（`hpX_*` は全て regularity precondition）。現状が honest tier 2 で安定。
- **撤退ライン発動: no**。GAP①②は self-write 可能（不可能な Mathlib 概念欠落ではない）。majorant 構成が想定超過した場合の縮退案として「`bound` を `Ioo(t/2,2t)` でなく単点 `t` の近傍にさらに狭める」「`pX` に full-support / bounded-support の追加 regularity 仮説を足す」が考えられるが、後者は load-bearing にならない範囲（`pX` の台に関する regularity）に留める限り許容。現時点で縮退提案を新撤退ラインとして立てる必要なし。

---

## 着手 skeleton（参考、20-30 行）

```lean
import InformationTheory.Shannon.FisherInfoV2DeBruijnPerTime

namespace InformationTheory.Shannon.FisherInfoV2

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)

-- GAP① 畳込密度 Gaussian 下界（self-written, 共有 sorry 補題候補）
private theorem convDensityAdd_gaussian_lower
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    {s : ℝ} (hs : 0 < s) :
    ∃ c R : ℝ, 0 < c ∧
      ∀ x, c * Real.exp (-(|x| + R) ^ 2 / (2 * s)) ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)  -- GAP①

-- GAP② Hess Gaussian-tail 上界（self-written, L-PT-δ と precondition 共有）
private theorem convDensityAdd_hess_tail_bound
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {s : ℝ} (hs : 0 < s) :
    ∃ C c' : ℝ, 0 < c' ∧
      ∀ x, ‖deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))) x‖
        ≤ C * (1 + x ^ 2) * Real.exp (-x ^ 2 / c') := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)  -- GAP②

-- 本体: GAP①(→ -log 多項式) × GAP②(Gaussian-tail) の積を integrable majorant に組む
private theorem debruijnIdentityV2_holds_assembled_chain_domination
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      (∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖(- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s, _⟩) x) - 1)
            * ((1/2) * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s, _⟩))) x)‖
          ≤ bound x) := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)
```

(skeleton はあくまで構成イメージ。GAP①② を補題化し本体を `Integrable.mono'` 不要の直接 `∃ bound` 構成で組む。`s` 一様化のため bound の `c'`/`C` を `Ioo(t/2,2t)` 端点 `t/2 ≤ s ≤ 2t` で評価する処理が本体に入る。)
