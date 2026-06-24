# EPI 2 壁 re-attack — Mathlib API 在庫 re-verification

> **対象**: Ch.17 一般 EPI の残り 2 壁 (壁1 `stam-step2-density` / 壁2 `debruijn-integration`)
> を discharge するのに必要な Mathlib apparatus の **「0 hit」claim を今の Mathlib で再確認**する。
> 過去 inventory が「Fisher/score/density 計算 Mathlib 全不在」と結論し scope-out した根拠を
> spot-check し、誤りがあれば是正、正しければ確定させる。
>
> **調査日**: 2026-05-30 (mathlib-inventory subagent 1 ターン、loogle index `2026-05-09` snapshot)。
> **このファイルは inventory 専用 (差分 re-verification)。実装 / 計画起草はしない。**
>
> **先行 inventory** (本ファイルが再検証する「0 hit」を含む):
> - `epi-stam-condexp-score-discharge-mathlib-inventory.md` (condExp×IndepFun cross-term `Found 0`)
> - `epi-stam-blachman-discharge-inventory.md` (Stam/Blachman/score-of-conv `Found 0`)
> - `fisher-info-mathlib-inventory.md` (Fisher info / de Bruijn 名前 `unknown identifier`)
> - `epi-debruijn-integration-mathlib-inventory.md` (FTC/IBP/heat 系)
> - `epi-debruijn-tail-mathlib-inventory.md` (EReal tail 系、PRESENT 多数)

---

## 再検証サマリ — 各 apparatus (1-10) の現状

凡例: ✅ あり / ❌ 確定不在 (loogle 0 hit) / 🟡 部分的 (限定形あり / 一般なし)。
**★ = 過去 inventory の「0 hit」claim が今回 spot-check で覆った / 精緻化された項目**。

### 壁1 (stam-step2-density)

| # | apparatus | 状態 | 1 行 |
|---|---|---|---|
| 1 | Gaussian convolution density (sum density = conv) | 🟡 部分的 | `IndepFun.pdf_add_eq_lconvolution_pdf'` あり (a.e. `⋆ₗ` 形)、Gaussian closed-form `gaussianReal_conv_gaussianReal` あり。**pointwise smooth 形は不在** |
| 2 | score function (`logDeriv`) / score of convolution | 🟡 部分的 | `logDeriv := deriv f / f` あり (score と定義同形)。**convolution の `logDeriv` は `Found 0`** |
| 3 | conditional expectation wrt sum σ-algebra | ✅ あり | `condExp` (253 lemmas) + condDistrib↔condExp + total expectation すべて既存 |
| 4 | Fisher information convolution (Stam/Blachman) | ❌ 確定不在 | `"Fisher" Found 0` / `"Blachman" Found 0` / `"Stam" Found 0` (91 hit は全て `Std.Time.Timestamp` 誤検出) |
| 5 | joint law on ℝ×ℝ + Fubini + cross-term | ✅ あり **★** | `IndepFun.integral_mul_eq_mul_integral` (`E[XY]=E[X]E[Y]`) + **`condExp_indep_eq`** (`E[f\|m₂]=E[f]` 独立時) が**両方存在** — 過去 `condExp_indep unknown identifier` claim は **誤り** |

### 壁2 (debruijn-integration)

| # | apparatus | 状態 | 1 行 |
|---|---|---|---|
| 6 | heat semigroup / Gaussian conv path 微分 | 🟡 部分的 **★** | heat semigroup 名前 `"heat" Found 0`。だが **`HasCompactSupport.hasDerivAt_convolution_right` 存在** (compact support 要、Gaussian 不適合)。repo `gaussianConvolution` 経路は law 計算で迂回済 |
| 7 | de Bruijn / Blachman / Stam by name | ❌ 確定不在 | `"Bruijn" Found 0` / `"Blachman" Found 0` / `"Fisher" Found 0` |
| 8 | FTC for interval integral along path | ✅ あり | `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` (bounded) + `MeasureTheory.integral_deriv_mul_eq_sub` (improper) 既存 |
| 9 | IBP (integration by parts) | ✅ あり | `intervalIntegral.integral_mul_deriv_eq_deriv_mul` + `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable` (improper) 既存 |
| 10 | differentialEntropy の微分 (= de Bruijn そのもの) | ❌ 確定不在 (Mathlib) / 🟡 repo Gaussian | Mathlib に entropy↔Fisher の微分 lemma なし。repo `FisherInfoV2DeBruijn` で Gaussian case のみ bridged |

### scope-out 根拠だった「0 hit」が今も 0 か — verdict

- **真に 0 のまま (確定不在)**: Fisher info / Stam / Blachman / de Bruijn の **named API** (#4, #7) と、
  **convolution の `logDeriv` / `lconvolution` の微分可能性** (#2, #6 の核)、**heat semigroup** (#6 名前)。
  これらは 2026-05-09 snapshot でも `Found 0`。scope-out の最深層の根拠は **依然 valid**。
- **覆った / 精緻化された ★ (3 件)**:
  1. **`MeasureTheory.condExp_indep_eq` は存在する** (#5) — `epi-stam-condexp-score` inventory:149 の
     `unknown identifier 'condExp_indep'` は **誤検出** (bare identifier query が失敗しただけ。string-literal
     query `"condExp", "Indep"` で 6 件ヒット、うち `condExp_indep_eq` が cross-term orthogonality の核)。
  2. **`IndepFun.integral_mul_eq_mul_integral` は存在する** (#5) — cross-term `E[s_X(X)·s_Y(Y)]=0` の
     全期待値版部品。`epi-stam-condexp-score` inventory:176 が「自作可能」と予測した通り、**部品は揃っている**
     (条件付きレベルでなく全積分レベルなら Mathlib 既存物で組める)。
  3. **convolution の微分可能性は `HasCompactSupport.*` 形で存在する** (#6) — `epi-debruijn-tail`/
     `epi-stam-blachman` の `Differentiable, lconvolution → Found 0` は `lconvolution` (ℝ≥0∞ 値) に限れば
     正しいが、**Bochner `convolution` (`⋆[L,μ]`) には `HasDerivAt`/`ContDiff` lemma が 6 件存在**。
     ただし **smooth 側の factor に `HasCompactSupport` を要求** — Gaussian heat kernel は compact support
     を持たないため**そのままでは適用不可**。これは「0 hit」から「適用条件不一致」への格下げ (依然 self-build 要)。

**結論**: scope-out の中核根拠 (Fisher/Stam/Blachman/de Bruijn 不在 + 畳み込み密度の smooth/score 接続不在)
は **valid のまま**。ただし「cross-term orthogonality が `Found 0` で組めない」という壁1 の補助 claim は
**過大評価で、Mathlib 既存物 (`condExp_indep_eq` + `IndepFun.integral_mul_eq_mul_integral`) で組める**。
これは Ch.8/Ch.9 の「壁→self-buildable」前科と同型の補正。

---

## 詳細テーブル — ヒット補題の構造化記録 + 0 hit query 逐語

### §1. 名前 spot-check (named API の確定不在)

| query (loogle string-literal) | 結果 verbatim | 判定 |
|---|---|---|
| `"Fisher"` | `Found 0 declarations whose name contains "Fisher".` | ❌ 確定不在 |
| `"Bruijn"` | `Found 0 declarations whose name contains "Bruijn".` | ❌ 確定不在 |
| `"Blachman"` | `Found 0 declarations whose name contains "Blachman".` | ❌ 確定不在 |
| `"Stam"` | `Found 91 declarations whose name contains "Stam".` (全件 `Std.Time.Timestamp` — false positive) | ❌ 実質不在 |
| `"heat"` | `Found 0 declarations whose name contains "heat".` | ❌ 確定不在 |
| `"score"` | `Found 132 declarations whose name contains "score".` (全件 `Nat.toDigits` / `underscore` — false positive) | ❌ 実質不在 |
| `"gaussianConvolution"` | `Found 0 declarations whose name contains "gaussianConvolution".` (= repo 専用名、Mathlib になし) | repo 内のみ |

### §2. ★ cross-term orthogonality 部品 (壁1 #5 — 過去「Found 0」が覆った核心)

**`MeasureTheory.condExp_indep_eq`** — 独立 σ-algebra 上の条件付き期待値が定数 `E[f]` に潰れる。

- **file:line**: `Mathlib/Probability/ConditionalExpectation.lean:42`
- **section 変数 (verbatim, `:37-38`)**:
  `{Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {m₁ m₂ m : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → E}`
- **完全 signature (verbatim)**:
  ```lean
  theorem condExp_indep_eq (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m) [SigmaFinite (μ.trim hle₂)]
      (hf : StronglyMeasurable[m₁] f) (hindp : Indep m₁ m₂ μ) : μ[f | m₂] =ᵐ[μ] fun _ => μ[f]
  ```
- **引数型 (順)**: `hle₁ : m₁ ≤ m` (explicit), `hle₂ : m₂ ≤ m` (explicit),
  `[SigmaFinite (μ.trim hle₂)]` (instance), `hf : StronglyMeasurable[m₁] f` (explicit),
  `hindp : Indep m₁ m₂ μ` (explicit)。
- **結論 form (verbatim)**: `μ[f | m₂] =ᵐ[μ] fun _ => μ[f]`
- **discharge での扱い**: Blachman cross-term `E[s_X(X)·s_Y(Y) | σ(X+Y)]` を扱う際、`s_X(X)` が
  `σ(X)`-可測で `σ(Y)` と独立な部分の崩しに使える。**`epi-stam-condexp-score` inventory:149 の
  `unknown identifier 'condExp_indep'` claim を覆す。**

**`ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral`** — Bochner 積分版 `E[XY]=E[X]E[Y]`。

- **file:line**: `Mathlib/Probability/Independence/Integration.lean:247`
- **section 変数 (verbatim, `:39-40`)**:
  `{Ω 𝕜 : Type*} [RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → 𝕜}`
- **完全 signature (verbatim)**:
  ```lean
  lemma IndepFun.integral_mul_eq_mul_integral
      (hXY : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
      μ[X * Y] = μ[X] * μ[Y]
  ```
- **引数型 (順)**: `hXY : X ⟂ᵢ[μ] Y` (= `IndepFun X Y μ`, explicit),
  `hX : AEStronglyMeasurable X μ` (explicit), `hY : AEStronglyMeasurable Y μ` (explicit)。
- **結論 form (verbatim)**: `μ[X * Y] = μ[X] * μ[Y]`
- **姉妹**: `IndepFun.integral_fun_mul_eq_mul_integral` (`:253`, 結論 `∫ ω, X ω * Y ω ∂μ = μ[X] * μ[Y]`)。
- **discharge での扱い**: cross-term orthogonality 全期待値版 `∫ (s_X∘X)(s_Y∘Y) dP = E[s_X∘X]·E[s_Y∘Y] = 0`
  を、repo 既存の score-mean-zero (`FisherInfoV2.n` / `n_pdf_eq_zero_gaussian`) と組んで割れる。**部品揃い**。

**`ProbabilityTheory.condVar_ae_le_condExp_sq`** — 条件付き Jensen `(E[g\|m])² ≤ E[g²\|m]` の実体 (既出だが再確認)。

- **file:line**: `Mathlib/Probability/CondVar.lean:127`
- **完全 signature (verbatim)**:
  ```lean
  lemma condVar_ae_le_condExp_sq (hm : m ≤ m₀) [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
      Var[X; μ | m] ≤ᵐ[μ] μ[X ^ 2 | m]
  ```
- **結論 form (verbatim)**: `Var[X; μ | m] ≤ᵐ[μ] μ[X ^ 2 | m]`
- **前提**: `[IsFiniteMeasure μ]` + `hX : MemLp X 2 μ` (score の L² 性、Gaussian 以外で非自明)。

### §3. ★ convolution 微分可能性 (壁2 #6 — 過去「Found 0」が「適用条件不一致」へ格下げ)

| query | 結果 verbatim | 判定 |
|---|---|---|
| `Differentiable, MeasureTheory.lconvolution` | `Found 0 declarations mentioning Differentiable and MeasureTheory.lconvolution.` | ❌ lconvolution (ℝ≥0∞ 値) は微分可能性 lemma なし |
| `Differentiable, MeasureTheory.convolution` | `Found 0 declarations mentioning Differentiable and MeasureTheory.convolution.` | (Differentiable 名では 0) |
| `ContDiff, MeasureTheory.convolution` | `Found 6 declarations` (下記) | 🟡 **存在 (compact support 要)** |
| `HasDerivAt, MeasureTheory.convolution` | `Found 2 declarations` (下記) | 🟡 **存在 (compact support 要)** |

ヒット 6 件 (全て `Mathlib.Analysis.Calculus.ContDiff.Convolution`):
`HasCompactSupport.contDiff_convolution_right/left`, `HasCompactSupport.hasDerivAt_convolution_right/left`,
`HasCompactSupport.hasFDerivAt_convolution_right/left`。

**`HasCompactSupport.hasDerivAt_convolution_right`** — convolution の微分 = factor の微分との convolution。

- **file:line**: `Mathlib/Analysis/Calculus/ContDiff/Convolution.lean:115`
- **section 変数 (verbatim, `:108-113`)**:
  `[NormedSpace ℝ F] [NormedSpace 𝕜 F] {f₀ : 𝕜 → E} {g₀ : 𝕜 → E'} {n : ℕ∞}`
  `(L : E →L[𝕜] E' →L[𝕜] F) {μ : Measure 𝕜} [IsAddLeftInvariant μ] [SFinite μ]`
  (上流 section: `[RCLike 𝕜]` 系 + `[NormedAddCommGroup E/E'/F]` 等、`𝕜=ℝ`, `E=E'=F=ℝ` で充足)
- **完全 signature (verbatim)**:
  ```lean
  theorem _root_.HasCompactSupport.hasDerivAt_convolution_right (hf : LocallyIntegrable f₀ μ)
      (hcg : HasCompactSupport g₀) (hg : ContDiff 𝕜 1 g₀) (x₀ : 𝕜) :
      HasDerivAt (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀
  ```
- **引数型 (順)**: `hf : LocallyIntegrable f₀ μ` (explicit),
  `hcg : HasCompactSupport g₀` (explicit) ⚠, `hg : ContDiff 𝕜 1 g₀` (explicit), `x₀ : 𝕜` (explicit)。
- **結論 form (verbatim)**: `HasDerivAt (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀`
- **致命的前提**: `hcg : HasCompactSupport g₀` — **smooth 側 factor が compact support を持つ必要**。
  de Bruijn で要る smooth factor は **Gaussian heat kernel** `gaussianPDFReal 0 t` で **compact support
  を持たない** → **そのままでは使えない**。`Differentiable, convolution → Found 0` の精緻化:
  「smooth + compact support」は有るが「smooth + (decay only, non-compact)」は無い。
  Gaussian kernel に適用するには truncation + tail control の self-build が要る (PR 級)。

### §4. score-of-convolution / Fisher info convolution (壁1 #2,#4 / 壁2 #7,#10 — 確定不在)

| 概念 | query | 結果 verbatim | 判定 |
|---|---|---|---|
| convolution の logDeriv (score) | (`logDeriv` ∘ conv は名前なし、概念 query) | `lconvolution` 微分可能性 `Found 0` 経由で間接確認 | ❌ 不在 |
| Fisher info named | `"Fisher"` | `Found 0` | ❌ 不在 |
| Stam/Blachman 不等式 | `"Stam"` / `"Blachman"` | `Found 0` (Stam 91 全 false positive) | ❌ 不在 |
| condExp × IndepFun を同時に言う lemma | `MeasureTheory.condExp, ProbabilityTheory.IndepFun` | `Found 0 declarations mentioning MeasureTheory.condExp and ProbabilityTheory.IndepFun.` | ❌ **直結 lemma は不在** (但し §2 `condExp_indep_eq` が `Indep m₁ m₂` 形で代替供給) |

**注**: `condExp + IndepFun` の subterm 同時 query は `Found 0` のまま (= `IndepFun` を引数に取る condExp lemma は
なし)。だが `condExp_indep_eq` は `Indep m₁ m₂ μ` (σ-algebra 独立) を取るので **query には引っかからないが
機能的に cross-term を供給する**。loogle subterm query の盲点 (predicate 形が `IndepFun` でなく `Indep` σ-algebra)。

### §5. FTC / IBP (壁2 #8,#9 — 既存確認)

| 概念 | Mathlib API | file:line | 結論 form (verbatim) | 状態 |
|---|---|---|---|---|
| bounded FTC | `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` | `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1141` | `∫ y in a..b, f' y = f b - f a` | ✅ |
| improper FTC (Ioi/deriv-mul) | `MeasureTheory.integral_deriv_mul_eq_sub` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1296` | (`= sub` 形、IBP の左半) | ✅ |
| IBP (bounded) | `intervalIntegral.integral_mul_deriv_eq_deriv_mul` | `Mathlib/.../IntervalIntegral/IntegrationByParts.lean` | — | ✅ |
| **IBP (improper, ℝ 全体)** | `MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable` | `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1318` | (下記) | ✅ |

**`MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable`** (de Bruijn IBP step の本命):

- **file:line**: `Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean:1318`
- **section 変数 (verbatim, `:1292`)**: `{A : Type*} [NormedRing A] [NormedAlgebra ℝ A]` (`A=ℝ` で充足。
  なお同 declaration は `[CompleteSpace A]` を **要求しない** — `:1326` の `variable [CompleteSpace A]` は
  この lemma の **後** に宣言)
- **完全 signature (verbatim)**:
  ```lean
  theorem integral_mul_deriv_eq_deriv_mul_of_integrable
      (hu : ∀ x ∈ tsupport v, HasDerivAt u (u' x) x)
      (hv : ∀ x ∈ tsupport u, HasDerivAt v (v' x) x)
      (huv' : Integrable (u * v')) (hu'v : Integrable (u' * v)) (huv : Integrable (u * v)) :
      ∫ (x : ℝ), u x * v' x = - ∫ (x : ℝ), u' x * v x
  ```
- **結論 form (verbatim)**: `∫ (x : ℝ), u x * v' x = - ∫ (x : ℝ), u' x * v x`
- **前提注意**: `hu`/`hv` は **`tsupport` 上の `HasDerivAt`** を要求 (台外は自由)。
  de Bruijn の `u := log p_t`, `v := p_t` 適用時、`p_t > 0` a.e. なら `tsupport v = ℝ` 全体 →
  `log p_t` の全点微分可能性が必要 (Gaussian convolution は全 support なのでここが効く)。

### §6. Gaussian convolution closed-form (壁1 #1 / 壁2 #6 — Gaussian 限定で既存)

| 概念 | Mathlib API | file:line | 結論 form (verbatim) | 状態 |
|---|---|---|---|---|
| Gaussian ∗ Gaussian | `ProbabilityTheory.gaussianReal_conv_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:613` | `(gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | ✅ |
| 独立 Gaussian 和 = Gaussian | `gaussianReal_add_gaussianReal_of_indepFun` | `Mathlib/.../Gaussian/Real.lean:624` | `P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | ✅ |
| sum density = lconvolution density | `IndepFun.pdf_add_eq_lconvolution_pdf'` | `Mathlib/Probability/Density.lean:349` | `pdf (X + Y) ℙ μ =ᵐ[μ] pdf X ℙ μ ⋆ₗ[μ] pdf Y ℙ μ` | 🟡 (a.e. + `⋆ₗ` 非微分) |

(これらは先行 inventory `fisher-info` §F / `epi-stam-blachman` §2A で verbatim 記録済。再 query で存在再確認のみ。)

---

## 主要前提条件ボックス (前提事故注意)

- **`condExp_indep_eq` (`ConditionalExpectation.lean:42`)**: `[SigmaFinite (μ.trim hle₂)]` +
  `hf : StronglyMeasurable[m₁] f` + `hindp : Indep m₁ m₂ μ`。
  **注意 1**: predicate が `Indep m₁ m₂ μ` (σ-algebra 独立) であって `IndepFun X Y μ` ではない →
  `IndepFun.indep_comap` 系で σ-algebra 独立に変換する 1 ステップが要る。
  **注意 2**: `[CompleteSpace E]` が section 必須 (`E=ℝ` で自動)。`f` は `m₁`-可測 (score `s_X∘X` は `σ(X)`-可測)。
- **`IndepFun.integral_mul_eq_mul_integral` (`Integration.lean:247`)**: `[RCLike 𝕜]` (`𝕜=ℝ` 自動) +
  `hX hY : AEStronglyMeasurable`。`X*Y` の integrability は **結論に明示されないが** Bochner 積分の慣行
  (非可積分なら両辺 0) で吸収。cross-term = 0 を出すには `E[s_X∘X]=0` (repo `n` 系) と組む。
- **`HasCompactSupport.hasDerivAt_convolution_right` (`ContDiff/Convolution.lean:115`)**:
  `hcg : HasCompactSupport g₀` が **致命的前提** — Gaussian heat kernel は compact support なし。
  `[IsAddLeftInvariant μ] [SFinite μ]` (`μ=volume` 自動)。**この lemma は de Bruijn には直接使えない**
  (truncation self-build 必須)。
- **`integral_mul_deriv_eq_deriv_mul_of_integrable` (`IntegralEqImproper.lean:1318`)**:
  `tsupport` 上の `HasDerivAt` 2 本 + 可積分性 3 本 (`u*v'`, `u'*v`, `u*v`)。Gaussian convolution は
  全 support → `log p_t` の全点微分可能性 (= `p_t > 0` 全点) が要件化。
- **`condVar_ae_le_condExp_sq` (`CondVar.lean:127`)**: `hX : MemLp X 2 μ` (score の L²)。Gaussian は OK、
  重テール密度で破れる。

---

## 自作が必要な要素 (優先度順、再検証後)

1. **【核・依然 PR 級】Blachman score-of-convolution `s_Z = E[s_X | σ(X+Y)]`** (壁1 #2 / 壁2 #7) —
   Mathlib に named API なし、convolution の smooth/score 接続も `HasCompactSupport` 制約で不適合。
   `condExp_ae_eq_integral_condDistrib` (既存) で枠は出るが `s_Z` が `logDeriv` of conv density である
   事実が gap。**工数 100-250 行 + regularity 多数**。再検証後も評価不変。
2. **【中・部品揃った】cross-term orthogonality `∫ (s_X∘X)(s_Y∘Y) dP = 0`** (壁1 #5) —
   **★ 再検証で格下げ**: `IndepFun.integral_mul_eq_mul_integral` (`:247`) + repo `n_pdf_eq_zero` /
   `n_pdf_eq_zero_gaussian` で **全期待値版は Mathlib + repo 既存物で組める**。`IndepFun (s_X∘X) (s_Y∘Y)`
   を `IndepFun.comp` で出す plumbing が主。**工数 20-40 行**。1 セッション可。
3. **【中・部品揃った】条件付き cross-term崩し** (壁1 #5 条件付き版) —
   **★** `condExp_indep_eq` (`:42`) で `E[s_X∘X | σ(X+Y)]` の独立部分を崩せる (過去「不在」claim 覆る)。
   ただし `σ(X)` と `σ(X+Y)` は **独立でない** ため直接適用不可 — disintegration 経由が要る。**工数 40-80 行**。
4. **【核・依然不在】Fisher info ↔ pdf 橋 + V1→V2 張り替え** (壁1 #4) — `fisherInfo` V1 が Gaussian で
   `0` に退化する flaw、V2 `fisherInfoOfDensity` を `P.map X` の pdf に紐付ける lemma が repo 不在。
   **工数 50-120 行 + 述語 pivot**。再検証後も不変。
5. **【核・依然不在】Gaussian heat kernel convolution の微分** (壁2 #6) —
   **★ 再検証で「0 hit」→「compact support 制約」へ格下げ**だが、Gaussian kernel が compact support を
   持たないため `HasCompactSupport.hasDerivAt_convolution_right` をそのまま使えない。truncation +
   dominated convergence で `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (既存) 経由の self-build。
   **工数 80-200 行**。

---

## Mathlib 壁の列挙 (真に不在、`@residual(wall:<name>)` 対象)

各 wall に loogle 確認結果を添える。**共有 sorry 補題への集約推奨を明記**
(詳細 → `docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」)。

| wall slug | 内容 | loogle 確認 | 共有集約 |
|---|---|---|---|
| `wall:fisher-info-named` | Mathlib に Fisher information の定義・named lemma が皆無 | `"Fisher" → Found 0` | repo `fisherInfo`/`fisherInfoOfDensity` で内製済 (Mathlib 壁ではなく repo 内 V1/V2 二重定義問題) |
| `wall:stam-blachman` | Stam 不等式 / Blachman score-of-convolution identity が皆無 | `"Stam"/"Blachman" → Found 0` | **shared sorry 補題化推奨** — 壁1#2/#4 と壁2#7 が同一の measure-theoretic コアに帰着、複数 file に散在中 (`IsStamScoreConvolution`=`True`, `IsStamTotalExpectation` 等) |
| `wall:conv-score-smooth` | 畳み込み密度の pointwise smooth 表現 + その `logDeriv` (= score of conv) | `Differentiable, lconvolution → Found 0`; conv の `HasDerivAt` は `HasCompactSupport` 制約で Gaussian 不適合 | **shared sorry 補題化推奨** — de Bruijn (壁2) と Blachman (壁1) が共有 |
| `wall:debruijn-heat-eq` | `∂_t p_t = (1/2)∂_xx p_t` (Gaussian heat equation) + entropy↔Fisher 微分 | `"heat" → Found 0`; `Mathlib.Analysis.PDE.*` 不在 (先行 inventory 確認) | repo `FisherInfoV2DeBruijn` で Gaussian case bridged、一般は honest hyp 外出し |

**`wall:cross-term-orthogonality` は wall から除外** (★ 再検証で取り下げ) — `condExp_indep_eq` +
`IndepFun.integral_mul_eq_mul_integral` で組めるため真の Mathlib 壁ではない (= 選択 big、not blocked hard)。
過去 inventory が `Found 0` で壁認定していたのは loogle bare-identifier query の失敗による誤判定。

---

## 撤退ラインへの距離

親計画 (`epi-stam-discharge-plan.md` / `epi-debruijn-integration-plan.md` / `epi-moonshot-plan.md`)
の既宣言撤退ライン:

- **L-S12-C** (未採用 = full condExp-of-score measure-theoretic discharge): 壁1。**既発動 (predicate pass-through)**。
- **L-Stam-CS / L-Stam-Conv / L-Stam-Opt** (`EPIStamInequalityBody.lean:47`): **既発動**。
- **L-DB-C-α** (IBP Mathlib gap) / **L-DB-C-β** (`T→∞` tail non-Gaussian): 壁2。**β は EReal lift で Gaussian closure 済**。

**判定: 本 re-verification は新規撤退ライン発動を要しない (調査のみ、実装せず)。**
ただし重要な**前提修正**:

- 過去「cross-term orthogonality は `Found 0` で壁、unconditional EPI は最深撤退ラインの手前で着地」
  という評価のうち、**cross-term orthogonality (壁1 #5) は撤退対象から外れる** — `condExp_indep_eq` +
  `IndepFun.integral_mul_eq_mul_integral` で genuine に組めるため。これにより壁1 の self-build スコープが
  わずかに縮小 (自作要素 2,3 が「不在」→「部品揃い」)。
- ただし **EPI 全体の撤退判定は不変**: 真の root primitive (`wall:stam-blachman` = Blachman score-of-conv +
  Fisher↔pdf 橋) と `wall:conv-score-smooth` は依然 self-build 必須で PR 級。cross-term が組めても、それを
  食う Blachman identity 本体が無ければ壁1 は閉じない。**縮退案 (Gaussian closed-form, L-S12-C′) は引き続き
  唯一の 1 セッション GO 経路**。

---

## 着手 skeleton (★ cross-term orthogonality = 最 tractable な新規 sub-target)

`InformationTheory/Shannon/EPIScoreCrossTermOrth.lean` (新規) の出だし。
**注: 本ファイルは inventory 専用。以下は実装サブエージェント向け参考 skeleton であり、本調査では実装しない。**

```lean
import InformationTheory.Shannon.FisherInfoV2
import Mathlib.Probability.Independence.Integration   -- IndepFun.integral_mul_eq_mul_integral
import Mathlib.Probability.ConditionalExpectation      -- condExp_indep_eq
import Mathlib.Probability.Density

/-!
# Score cross-term orthogonality (toward Blachman / Stam)

`E[s_X(X) · s_Y(Y)] = 0` for independent `X, Y` with mean-zero scores. This is the
one Stam/Blachman sub-piece that re-verification (2026-05-30) found to be
Mathlib-buildable: `IndepFun.integral_mul_eq_mul_integral` (Integration.lean:247)
+ repo score-mean-zero (`FisherInfoV2.n` / `n_pdf_eq_zero_gaussian`). Earlier
inventories mis-flagged this as `Found 0`.

NOT the Blachman identity itself (`wall:stam-blachman`) — that remains a self-build
wall (score-of-convolution `s_Z = E[s_X | σ(X+Y)]`, PR-grade). This file only
supplies the cross-term lemma the Blachman expansion consumes.
-/

namespace InformationTheory.Shannon.EPIScoreCrossTermOrth

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Score cross-term orthogonality (full-expectation version).**
For independent `X, Y` whose score functions `sX, sY` have zero mean, the
cross-term `∫ sX(X ω) · sY(Y ω) dP = 0`. Built from
`IndepFun.integral_mul_eq_mul_integral` + mean-zero scores; NOT a discharge of
the Blachman identity (which stays `@residual(wall:stam-blachman)`). -/
theorem score_cross_term_eq_zero
    {X Y : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {sX sY : ℝ → ℝ}
    (hXY : IndepFun X Y P)
    (hsX : AEStronglyMeasurable (fun ω => sX (X ω)) P)
    (hsY : AEStronglyMeasurable (fun ω => sY (Y ω)) P)
    (hmeanX : ∫ ω, sX (X ω) ∂P = 0) :
    ∫ ω, sX (X ω) * sY (Y ω) ∂P = 0 := by
  sorry  -- IndepFun.comp hXY → IndepFun.integral_fun_mul_eq_mul_integral → rw [hmeanX]; ring

end InformationTheory.Shannon.EPIScoreCrossTermOrth
```

> 注: `hmeanX` は repo の `FisherInfoV2.n` / `n_pdf_eq_zero_gaussian` から供給 (score 期待値 0)。
> この sub-target は **1 セッション可** (20-40 行)。ただし Blachman identity 本体 (`wall:stam-blachman`)
> は別 file の self-build wall として `sorry + @residual` で残る。

---

## orchestrator への含意

**genuine に不在で self-build 必須 (Mathlib 壁、`@residual(wall:...)` 対象)**:
`wall:stam-blachman` (Stam/Blachman named + score-of-convolution identity)、
`wall:conv-score-smooth` (畳み込み密度の pointwise smooth + logDeriv — Bochner conv の `HasDerivAt` は
`HasCompactSupport` 制約で Gaussian kernel に不適合)、`wall:debruijn-heat-eq` (Gaussian heat equation +
entropy↔Fisher 微分)。これらは Ch.17 一般 EPI の 2 壁の **核** であり、再検証後も valid。**`wall:stam-blachman`
と `wall:conv-score-smooth` は壁1/壁2 で共有されるため shared sorry 補題化を推奨** (現状複数 file に散在)。

**Mathlib にあって組める (過去「壁」評価が ★ で覆った)**: cross-term orthogonality (`condExp_indep_eq` +
`IndepFun.integral_mul_eq_mul_integral`)、FTC/IBP (bounded + improper 両方既存)、conditional Jensen
(`condVar_ae_le_condExp_sq`)、Gaussian closed-form convolution。**最も危険な誤りの是正**: 過去 inventory が
`condExp_indep` を `unknown identifier` で「不在」認定していたが、これは loogle の bare-identifier query が
存在しない名前で失敗しただけで、string-literal query で `MeasureTheory.condExp_indep_eq` が**実在する**。
cross-term orthogonality は真の Mathlib 壁ではなく **選択 (big)、組めば 20-40 行 / 1 セッション**。ただし
これが組めても壁1/壁2 全体は `wall:stam-blachman` 本体が閉じない限り完成しない — **2 壁の scope-out 判断は
維持、ただし「cross-term も壁」という補助 claim は撤回**。GO する場合の最 tractable な新規 sub-target は
`score_cross_term_eq_zero` (上記 skeleton)。
