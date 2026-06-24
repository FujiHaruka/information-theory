# EPI de Bruijn GAP② 案B (finite-2nd-moment + joint domination) — Mathlib/repo API 在庫

> **対象**: `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean` の `_chain_domination`
> (`:618`、現 `@audit:defect(false-statement)` + `@residual(plan:epi-debruijn-pertime-closure)`)
> が要求する σ-derivand domination を、分離積 (GAP① log-factor × GAP② Gaussian-Hessian) を捨てて
> **真の σ-derivand 積を joint で dominate** する案B (finite-2nd-moment + joint domination) の在庫。
> 親計画: `docs/shannon/epi-debruijn-pertime-closure-plan.md` (§Phase 5-G, 判断ログ #13/#15)。
> 隣接: `docs/shannon/chain-domination-majorant-inventory.md` (旧 GAP①×GAP② 分離積の在庫、案B では破棄)、
> `docs/shannon/fisher-finiteness-closure-plan.md` (`convDensityAdd_fisher_integrable` の Stam 壁)。
> **docs-only 調査**。Lean compile / コード編集 / commit はしていない。

## 一行サマリ

案B joint domination のクロージャに必要な API のうち **汎用 measure-theory / Gaussian-integral 部品は ~85% Mathlib 既存**だが、joint domination の核 (σ-derivand `(-log p_s)·∂²p_s` の積分有限性) は **`J(X+√sZ) ≤ 1/s` 型の Stam convolution Fisher bound に帰着** し、これは Mathlib / repo ともに不在 (`fisherInfo`/`Blachman` loogle = `Found 0`)。**critical overlap verdict: 案B 固有壁は `convDensityAdd_fisher_integrable` の `wall:fisher-finiteness` (`:715`) と core を共有する** — 同じ Stam-bound 壁。**自作必要 = 実質 1 壁 (shared sorry 補題 `gaussianConv_fisher_le_inv_var` への集約推奨)**。**撤退ライン発動: no** (案B は `_chain_domination` の defect 形を真命題に戻す方向、現 `plan:` の正規撤退口に整合)。

---

## 主定理の最終形 (再掲) — 案B が埋めるべき `_chain_domination`

現コード (`FisherInfoV2DeBruijnAssembly.lean:618-629`、verbatim、現 defect 形):

```lean
private theorem debruijnIdentityV2_holds_assembled_chain_domination
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      (∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖(- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s, _⟩) x) - 1)
            * ((1/2) * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s, _⟩))) x)‖
          ≤ bound x) := by sorry
```

被支配量 = σ-derivand `g(s,x) = LogFactor(s,x) · ((1/2)·Hess(s,x))`:
- `LogFactor(s,x) = - log (p_s x) - 1`、`Hess(s,x) = ∂²_x p_s x`、`p_s = convDensityAdd pX g_s`。

**STATEMENT 自体は真** (独立監査 `:604-606` verbatim 確認): 真の積 `(-log p_s)·∂²p_s` は finite-2nd-moment pX で Lebesgue 可積分。**ただし GAP①×GAP② 分離積では証明不可** — GAP① log-factor 単独は `~x²` (非可積分)、honest な Hessian 上界は polynomial-tail pX で `~1/x²` (Gaussian-tail でない) なので分離積 majorant `~const` が非可積分 (判断ログ #13)。

擬 Lean 戦略 (案B joint、分離積を経由しない):

```text
-- 案B-i (entropy-finiteness 経由、推奨): bound を直接構成せず、σ-derivand の
--   ∫|g(s,x)| dx < ∞ を「Fisher 有限 J(p_s) ≤ 1/s + entropy 有限」に帰着。
-- 1. |g(s,x)| = |(-log p_s - 1)·(1/2)∂²p_s|。IBP (debruijn_ibp_step) 後の真の値は
--    ∫(-log p_s -1)·∂²p_s = ∫(logDeriv p_s)²·p_s = J(p_s) (Fisher info)。
-- 2. J(p_s) ≤ J(√s·Z) = 1/s  (Stam convolution Fisher bound) ← 核壁、fisher-finiteness と共有
-- 3. s ∈ Ioo(t/2,2t) で s ≥ t/2 → J(p_s) ≤ 2/t、s-一様有限上界。
-- 4. ∃ bound: dominated-convergence gateway が要求するのは bound の存在のみ。
--    joint bound を「s-一様 Gaussian-window 上の |g(s,x)| そのものの integrable envelope」で。
```

> **重要 (`_chain_domination` の consumer 確認、verbatim)**: `_chain_domination` の `∃ bound` は
> `_chain_parametric` (`:850`) が `entropy_hasDerivAt_via_parametric` atom (Ioo-version、`hb`/`hdiff`
> を `Set.Ioo (t/2)(2*t)` で量化) の **domination hyp** に供給する。atom は per-`x` 被積分関数の σ微分
> を domination する `bound` を要求し、それは「σ-derivand の積分越し微分」を正当化する dominated-
> convergence の前提。**bound は `‖g(s,x)‖ ≤ bound x` (∀ s∈Ioo) を満たす integrable envelope であれば
> 何でもよい** — Gaussian-tail 形でなくてよい (defect の本質は「Gaussian-tail を主張した」ことであり、
> envelope の存在自体は真)。

---

## A. 真の σ-derivand 積の構造と Mathlib 表現 (joint、軸1)

### A-1. `∂²_x (pX ∗ g_s)` の同定 (heat-eq STEP D、repo 既存)

| 概念 | API | file:line | 状態 | 案B での扱い |
|---|---|---|---|---|
| 畳込 2nd-deriv の積分同定 | `theorem heatFlow_density_heat_equation (pX pPath pathDeriv1 pathDeriv2 : ℝ → ℝ → ℝ) (hpPath : ∀ (σ : ℝ) (hσ : 0 < σ), pPath σ = convDensityAdd pX (gaussianPDFReal 0 ⟨σ, hσ.le⟩)) (hpathDeriv1 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pPath σ ξ) (pathDeriv1 σ y) y) (hpathDeriv2 : ∀ σ y : ℝ, HasDerivAt (fun ξ => pathDeriv1 σ ξ) (pathDeriv2 σ y) y) {s : ℝ} (hs : 0 < s) (x : ℝ) (boundσ ... boundξ1 boundξ2 : ℝ → ℝ) ... : HasDerivAt (fun σ : ℝ => pPath σ x) ((1/2) * pathDeriv2 s x) s` | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:422` | ✅ 既存 (`@audit:ok`) | STEP D が `pathDeriv2 s x = ∫ y, pX y·g_s(x-y)·((x-y)²/s² - 1/s)` を同定。`deriv(deriv(convDensityAdd ...)) = pathDeriv2` の橋渡しは `hpathDeriv1/2` の `HasDerivAt` precondition (full-support C¹) 経由 |
| kernel 2nd-deriv 閉形 | `theorem heatFlow_density_heat_equation_kernel_x_deriv2 {σ : ℝ} (hσ : 0 < σ) (u : ℝ) : HasDerivAt (fun ξ : ℝ => heatFlow_density_heat_equation_kernel σ ξ * (-(ξ / σ))) (heatFlow_density_heat_equation_kernel σ u * (u ^ 2 / σ ^ 2 - 1 / σ)) u` | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:290` | ✅ 既存 (`@audit:ok`) | `∂²_u g_σ(u) = g_σ(u)·(u²/σ²-1/σ)`。被積分核閉形 |
| `convDensityAddDeriv` 定義 | `noncomputable def convDensityAddDeriv (pX pY : ℝ → ℝ) : ℝ → ℝ → ℝ := fun z x => pX x * deriv pY (z - x)` | `InformationTheory/Shannon/EPIConvDensity.lean:64` | ✅ 既存 | z-微分被積分核 |
| **`∂²_x(pX∗g_s) = pX∗∂²_x g_s` の Mathlib 直結 lemma** | — | — | ❌ **不在** | loogle `HasDerivAt (MeasureTheory.convolution _ _ _ _)` → **Found 2、両方 `HasCompactSupport.hasDerivAt_convolution_{right,left}` (compact support 前提)**。g_s は compact support でない → Mathlib convolution-微分 API は直接適用不可。repo は heat-eq STEP D 経由で自作迂回 (上記) |

### A-2. σ-derivand の積分有限性 = Fisher 有限性 (joint の核、IBP 経由)

| 概念 | API | file:line | 状態 | 案B での扱い |
|---|---|---|---|---|
| de Bruijn IBP step (`∫(-log p-1)·∂²p = ∫(logDeriv p)²·p`) | `theorem debruijn_ibp_step ...` (atom) | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:693` | ✅ 既存 (`@audit:ok`) | σ-derivand の積分値を Fisher 形に変換。**joint domination の概念的根拠** (積分値 = J(p_s)) |
| `∫(logDeriv p)²·p = fisherInfoOfDensityReal p` | `theorem fisher_from_logDeriv ...` (atom) | `InformationTheory/Shannon/FisherInfoV2DeBruijnPerTime.lean:721` | ✅ 既存 (`@audit:ok`) | logDeriv² 形 → Fisher 値。`hint : Integrable ((logDeriv p)²·p)` を要求 (= fisher-finiteness 壁) |
| logDeriv 表現 (score of conv) | `theorem convDensityAdd_logDeriv (pX pY : ℝ → ℝ) (z₀ : ℝ) {s : Set ℝ} {bound : ℝ → ℝ} (hs : s ∈ nhds z₀) (hF_meas : ...) (hF_int : Integrable (fun x => pX x * pY (z₀ - x)) volume) (hF'_meas : ...) (h_bound : ...) (bound_integrable : Integrable bound volume) (h_diff : ...) : logDeriv (convDensityAdd pX pY) z₀ = (∫ x, convDensityAddDeriv pX pY z₀ x ∂volume) / convDensityAdd pX pY z₀` | `InformationTheory/Shannon/EPIConvDensity.lean:113` | ✅ 既存 (`@audit:ok`) | `logDeriv p_s(z) = (∫ pX·g_s'(z-x))/p_s(z)` (Blachman 接続点) |
| **`J(pX∗g_s) ≤ 1/s` (Stam convolution Fisher bound)** | — | — | ❌ **不在** | **案B の核壁**。下記 §C (fisher-finiteness と同一壁) |

---

## B. 案B domination envelope 構成の汎用部品 (Mathlib、全 ✅ 既存)

| 概念 | Mathlib API | file:line | 状態 | 案B での扱い |
|---|---|---|---|---|
| majorant による可積分性 | `theorem Integrable.mono' {f : α → β} {g : α → ℝ} (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : Integrable f μ` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:100` | ✅ 既存 | envelope integrability。本 sorry は `∃ bound` 存在のみ要求 |
| 可積分 × 有界 = 可積分 | `theorem Integrable.mul_bdd {f g : α → 𝕜} {c : ℝ} (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ) (hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ c) : Integrable (fun x => f x * g x) μ` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1070` | ✅ 既存 | repo 先例 `PerTime.lean:170`。Gaussian factor を prefactor で有界化 |
| 有界 × 可積分 = 可積分 | `theorem Integrable.bdd_mul {f g : α → 𝕜} {c : ℝ} (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) : Integrable (fun x => f x * g x) μ` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1063` | ✅ 既存 | 因子順違い |
| 有限 lintegral → Integrable | `theorem MeasureTheory.lintegral_ofReal_ne_top_iff_integrable {f : α → ℝ} (hf : AEMeasurable f μ) (hf' : 0 ≤ᵐ[μ] f) : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ ↔ Integrable f μ` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean` (loogle `Found 13`、`lintegral_ofReal_ne_top_iff_integrable` 該当) | ✅ 既存 | Fisher 有限 `< ⊤` → 被積分関数 Integrable の round-trip (entropy-finiteness 経由のとき) |
| `x^k·exp(-b x²)` 可積分 (repo bridge) | `private theorem integrable_natPow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (k : ℕ) : Integrable (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) volume` | `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:120` | ✅ 既存 (`@audit:ok`) | poly×Gaussian envelope の最終 integrability (Mathlib `integrable_rpow_mul_exp_neg_mul_sq` `GaussianIntegral.lean:109` の `rpow`→`pow` bridge) |
| `convDensityAdd` 上界 (prefactor) | `private theorem convDensityAdd_le_prefactor (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1) {s : ℝ} (hs : 0 < s) (x : ℝ) : convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x ≤ (Real.sqrt (2 * Real.pi * (⟨s, hs.le⟩ : ℝ≥0)))⁻¹` | `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:160` | ✅ 既存 (`@audit:ok`) | `p_s ≤ pref` 一様上界 |
| `convDensityAdd` Gaussian 下界 (s-一様 R) | `private theorem convDensityAdd_lower_bound_gaussian_uniformR (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1) : ∃ R : ℝ, 0 < R ∧ ∀ (s : ℝ) (hs : 0 < s) (x : ℝ), (1/2) * gaussianPDFReal 0 ⟨s, hs.le⟩ (|x| + R) ≤ convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩) x` | `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:217` | ✅ 既存 (`@audit:ok`) | `p_s ≥ (1/2)g_s(|x|+R)` 一様下界。GAP① log majorant の素 (`-log p_s ≤ A+Bx²`) — 案B でも log-factor 上界に再利用可 |
| log factor 多項式 majorant (GAP①、genuine) | `private theorem convDensityAdd_logFactor_poly_majorant (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (_hpX_meas : Measurable pX) (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1) {t : ℝ} (ht : 0 < t) : ∃ A B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) → ‖- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s, _⟩) x) - 1‖ ≤ A + B * x ^ 2` | `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:333` | ✅ 既存 (`@audit:ok`, 0 sorry) | **案B でも生きる**: log factor の `~x²` 上界は真。問題は GAP② 側だった。joint では「log² との積を Fisher 経由で抑える」ので、この `~x²` 上界が `(logDeriv)²` の代替として `J(p_s)` finiteness と組み合わさる |

---

## C. 案B の核壁: Stam convolution Fisher bound (❌ Mathlib/repo 不在) — fisher-finiteness と共有

| 概念 | Mathlib/repo API | file:line | 状態 | 案B での扱い |
|---|---|---|---|---|
| **`fisherInfoOfDensity (pX∗g_s) ≤ 1/s`** (Stam) | — | — | ❌ **不在** | **案B の核壁**。loogle `"fisherInfo"` / `"Blachman"` / `"deBruijn"` = いずれも `Found 0 declarations`。Mathlib に Fisher info 概念自体が無い |
| Fisher integrability wall (consumer) | `private theorem convDensityAdd_fisher_integrable (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX) (hpX_int : Integrable pX volume) {t : ℝ} (ht : 0 < t) : Integrable (fun x => (logDeriv (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩)) x)^2 * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x) volume` | `InformationTheory/Shannon/FisherInfoV2DeBruijnAssembly.lean:715` | ❌ sorry (`@residual(wall:fisher-finiteness)`) | **★案B が共有する壁** (下記 overlap verdict)。本壁は `J(X+√tZ)≤1/t` の有限性に依拠 |
| Stam 算術核 (両 Gaussian) | `theorem stam_fisher_arith (a b lam : ℝ) (ha : 0 < a) (hb : 0 < b) (hlo : 0 ≤ lam) (hhi : lam ≤ 1) : 1 / (a + b) ≤ lam ^ 2 / a + (1 - lam) ^ 2 / b` | `InformationTheory/Shannon/StamGaussianBound.lean:58` | ✅ 既存 (`@entry_point`) | building block。density 一般化の λ 最適化に再利用 (一般 pX には直接使えない) |
| Gaussian 凸 Fisher 上界 (両 Gaussian instance) | `theorem stam_convex_fisher_bound_gaussian (m₁ m₂ : ℝ) {v₁ v₂ : ℝ≥0} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (lam : ℝ) (hlo : 0 ≤ lam) (hhi : lam ≤ 1) : (fisherInfoOfMeasureV2 (gaussianReal (m₁ + m₂) (v₁ + v₂)) (gaussianPDFReal (m₁ + m₂) (v₁ + v₂))).toReal ≤ lam ^ 2 * (fisherInfoOfMeasureV2 (gaussianReal m₁ v₁) (gaussianPDFReal m₁ v₁)).toReal + (1 - lam) ^ 2 * (fisherInfoOfMeasureV2 (gaussianReal m₂ v₂) (gaussianPDFReal m₂ v₂)).toReal` | `InformationTheory/Shannon/StamGaussianBound.lean:77` | ✅ 既存 (`@entry_point`, genuine) | **両被加数 Gaussian instance のみ** — 一般 pX (X+√sZ) には使えない (X が任意密度)。building block 止まり |
| repo Stam predicate 群 | `IsStamScoreConvolution` / `IsStamCauchySchwarz` / `IsStamInequalityHyp` (`EPIStamInequalityBody.lean` / `EPIStamStep3Body.lean`) | — | ⚠ predicate pass-through | load-bearing predicate を仮説に取る wrapper。density-level genuine な `J(X+Z)≤J(Z)` 補題は **repo 不在** (fisher-finiteness plan `:52-59` verbatim 確認済) |

**核壁の内容**: 案B の joint domination は最終的に「σ-derivand の積分越し微分を正当化する integrable envelope」を要求するが、その envelope の存在 ⇔ σ-derivand `(-log p_s)·∂²p_s` が s-一様に積分可能 ⇔ (IBP 後) `J(p_s) = ∫(logDeriv p_s)²·p_s < ∞` ⇔ `J(X+√sZ) ≤ 1/s`。**この `J(X+√sZ) ≤ 1/s` が Mathlib/repo 不在の真壁**。

---

## 主要前提条件ボックス (前提事故注意)

- **`heatFlow_density_heat_equation`** (`PerTime.lean:422`): `pPath`/`pathDeriv1`/`pathDeriv2` を抽象 `ℝ→ℝ→ℝ` で取り、3 definitional pin + σ/spatial domination 群 (`boundσ`/`boundξ1`/`boundξ2` + 各 `Integrable`/`AEStronglyMeasurable`/`∀ᵐ ≤ bound`) を要求。全て regularity precondition (`@audit:ok`)。`deriv(deriv(convDensityAdd...)) = pathDeriv2` 橋渡しは `hpathDeriv1/2` の `HasDerivAt` (full-support C¹) discharge を要求 → **L-PT-δ wall に触れる** (案B でも IBP step 経由で残る)。
- **`fisher_from_logDeriv`** (`PerTime.lean:721`, `@audit:ok`): `hp_nn : ∀ x, 0 ≤ p` + `hint : Integrable ((logDeriv p)²·p)` を要求。`hint` が **= fisher-finiteness 壁** verbatim。case A の vacuous-genuine 罠を避けるため、案B では `hint` を honest sorry 壁 (`convDensityAdd_fisher_integrable`) から供給 (load-bearing でない、lemma call)。
- **`Integrable.mono'`** (`Integrable.lean:100`): `f : α → β` (NormedAddCommGroup)、`g : α → ℝ`、`hf : AEStronglyMeasurable f μ` + `h : ∀ᵐ, ‖f a‖ ≤ g a`。envelope の AEStronglyMeasurable を落とすと型エラー。
- **`lintegral_ofReal_ne_top_iff_integrable`** (loogle `Found 13` 該当、`Integrable.lean`): `hf : AEMeasurable f μ` + `hf' : 0 ≤ᵐ[μ] f` 必須。Fisher 有限 → 被積分関数 Integrable の round-trip に使うとき AEMeasurable `(logDeriv p_s)²·p_s` が要 (`deriv p_s / p_s` の可測性、`convDensityAdd_hasDerivAt` 経由で point ごと、全 x 可測性に追加補題が要る場合あり)。
- **`gaussianPDFReal_pos`** (Mathlib `Gaussian/Real.lean:61`): `hv : v ≠ 0` 必須。`s > 0` から `⟨s,_⟩ ≠ 0` を `NNReal.eq` 経由 (atom 先例 `PerTime:207`)。
- **`hpX_mom : Integrable (fun y => y² * pX y)`** (現 `_chain_domination:621`): 案B の finite-2nd-moment 前提。**load-bearing でない regularity** (de Bruijn 標準前提)。case A defect の本質は「`hpX_mom` を足しても Gaussian-tail 結論が偽」だったが、案B では結論を Gaussian-tail にせず joint envelope 存在のみ要求するので `hpX_mom` が genuine に効く (∫pX(y)(x-y)²dy の有限性に 1st/2nd moment が要る)。

---

## 自作が必要な要素 (優先度順)

1. **【最優先・核心】Stam convolution Fisher bound `gaussianConv_fisher_le_inv_var`** (~150-250 行 PR 級)
   `fisherInfoOfDensity (convDensityAdd pX g_s) ≤ ENNReal.ofReal (1/s)`。引数は regularity のみ (`hpX_nn`/`hpX_meas`/`hpX_int`/`hs`)。**= fisher-finiteness plan の R-A 補題そのもの** (`docs/shannon/fisher-finiteness-closure-plan.md:162`)。density-level score-of-convolution Cauchy-Schwarz が PR 最重量部 (`stam-step2-density` 核と重複可能性、plan で判定保留)。`stam_fisher_arith` (算術核) + V2 Gaussian 閉形 `J(𝒩(0,s))=1/s` (`FisherInfoV2DeBruijn.lean:100`) が building block。**shared sorry 補題化推奨** (下記)。

2. **【高】σ-derivand → Fisher 有限性の橋渡し (joint envelope 構成)** (~60-100 行)
   `J(p_s) ≤ 1/s` から「σ-derivand `(-log p_s)·(1/2)∂²p_s` の s-一様 integrable envelope」を構成。IBP step (`debruijn_ibp_step`) で積分値を Fisher 形に変換した上で、`_chain_parametric` が要求する dominated-convergence の bound を組む。**落とし穴**: envelope は積分値の有限性だけでなく per-`x` pointwise の `‖g(s,x)‖ ≤ bound x` (∀ s∈Ioo) が要る — Fisher 有限性は ∫ レベルなので、pointwise envelope には `convDensityAdd_logFactor_poly_majorant` (log の `~x²`) × `∂²p_s` の honest polynomial-tail 上界 (`~(1+x²)` ではなく `∫pX(y)g_s(x-y)(x-y)²dy` の 1st/2nd-moment 有限性経由の polynomial bound) を組む。これは Gaussian-tail でなく **polynomial × Gaussian-from-g_s** で integrable (case A が誤ったのは「prefactor で Gaussian を落とした」点。落とさず `g_s(x-y)` の Gaussian を保持すれば polynomial moment と合わせて integrable)。

3. **【中】`∂²_x p_s` の honest polynomial-moment 上界** (~40-60 行)
   `‖∂²_x p_s x‖ ≤ ∫ pX(y)·g_s(x-y)·|(x-y)²/s²-1/s| dy`。`g_s(x-y)` の Gaussian を**保持**し (prefactor で落とさない)、`(x-y)²` を 1st/2nd-moment (`hpX_mass`/`hpX_mom`) で展開 → finite-coefficient × Gaussian-convolution。これが case A 監査の指摘した正路 (`:509-511` keep-Gaussian route)。ただし keep-Gaussian route は MGF `∫pX(y)exp(xy/s)dy < ∞` を要求する箇所があり (case A 監査 `:509`)、これを回避するため **積分値 (Fisher) レベルで閉じる案B-i (entropy-finiteness 経由) が pointwise envelope より安全**。

4. **【低】Step 3 plumbing (有限性 → Integrable)** (~30-40 行、Mathlib 既存)
   `lintegral_ofReal_ne_top_iff_integrable` 系で Fisher 有限 → 被積分関数 Integrable。純 plumbing。

工数感: 核壁 (#1) を除けば ~130-200 行。核壁 #1 が PR 級 (~150-250 行) だが **fisher-finiteness と共有** なので案B 単独の追加コストは #2-4 (~130-200 行)。

---

## ★critical overlap verdict — fisher-finiteness 壁との共有

> **⚠ 訂正 (2026-05-31, 判断ログ #17, proof-pivot-advisor mpmath 検算)**: 下記の「1壁3consumer」は
> **誤り**。`_chain_domination` は Fisher 壁を**必要としない** — joint envelope の pointwise integrability は
> Tonelli + g_s モーメント + finite 2nd moment で独立に閉じ (`∫(A+Bx²)hessBound = ∫pX(y)K(y)dy`、K は
> y-degree2)、`J(p_s)≤1/s` を経由しない。IBP→Fisher は**積分値**側の話で dominated-convergence gateway が
> 要求する **pointwise envelope** には不適用。正しい overlap = **「1壁2consumer」**:
> `gaussianConv_fisher_le_inv_var` の consumer は `convDensityAdd_fisher_integrable` + `_chain_ibp_fisher` の
> 2 件のみ。以下の verdict 本文は当該訂正を反映して読むこと (fisher 壁自体は fisher-finiteness 単独 closure に
> 依然必要なので壁は残る、ただし `_chain_domination` consumer は除外)。

**verdict (訂正前、上記注記参照): 共有する (SAME Stam-bound wall)。**

根拠 (2 行):
1. 案B joint domination の σ-derivand 積分有限性は、IBP (`debruijn_ibp_step`、`@audit:ok`) で `∫(-log p_s -1)·∂²p_s = ∫(logDeriv p_s)²·p_s = J(p_s)` に変換され、有限性は `J(p_s) ≤ J(√sZ) = 1/s` に帰着する。
2. これは `convDensityAdd_fisher_integrable` (`:715`, `@residual(wall:fisher-finiteness)`) が依拠する `J(X+√tZ) ≤ 1/t` と**同一の Stam convolution Fisher bound** (時刻が `t` 固定 vs `s ∈ Ioo` 一様という違いのみ、後者は `s ≥ t/2` で `J(p_s) ≤ 2/t` に一様化)。

**帰結 (orchestration)**: 案B と fisher-finiteness は **shared sorry 補題 1 本 `gaussianConv_fisher_le_inv_var`** (fisher-finiteness plan `:162` の R-A 補題、引数 regularity のみ、結論 `fisherInfoOfDensity (convDensityAdd pX g_s) ≤ ENNReal.ofReal (1/s)`) で **両方 gate できる**。`convDensityAdd_fisher_integrable` (Step 3 plumbing) と `_chain_domination` (joint envelope 構成) は両方ともこの 1 補題を lemma call する consumer になる。`docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」(`:396`) に従い、壁を 1 補題に集約 (新 file `InformationTheory/Shannon/FisherConvBound.lean` 候補、fisher-finiteness plan R-A skeleton 通り)。

**注意 (誤った非共有判定の回避)**: case A の分離積 (GAP①×GAP②) は Fisher 経由を使わず pointwise Gaussian-tail を主張したため fisher 壁と「別物」に見えた。案B が分離積を捨てて joint (= Fisher 経由) に切り替えたことで、初めて fisher 壁との core 共有が露呈する。この共有の発見が案B 採用の最大の orchestration メリット (壁の重複排除)。

---

## 案B の壁分類 (named wall 列挙)

| named wall | 内容 | 分類 | 共有 |
|---|---|---|---|
| **Stam convolution Fisher bound** (`J(pX∗g_s)≤1/s`) | density-level score Cauchy-Schwarz → 凸 Fisher 上界 → λ→0 | **(c) 自作壁 (PR 級)** | **fisher-finiteness (`wall:fisher-finiteness`) と core 共有** → shared sorry 補題 `gaussianConv_fisher_le_inv_var` 1 本で両 gate |
| de Bruijn IBP step preconditions (`tsupport`=ℝ C¹) | `debruijn_ibp_step` atom の full-support C¹ + 3 integrability hyp | **(b) repo atom 既存、precondition 自作 (plan)** | `_chain_ibp_fisher_ibp_step` (`:750`, `plan:`, L-PT-δ) と共有。atom の `Integrable(u'*v)` precondition が fisher-finiteness と overlap (既に code 注記 `:745-747`) |
| σ-derivand chain rule (negMulLog ∘ p_s) | per-`x` chain rule | **(b) repo 既存** | `_chain_entDeriv_formula` (§5G-1, genuine `@audit:ok`) |
| parametric diff gateway | `hasDerivAt_integral_of_dominated_loc_of_deriv_le` | **(a) Mathlib 実在** | `entropy_hasDerivAt_via_parametric` atom (`@audit:ok`、Ioo-version) |
| poly×Gaussian / log majorant / prefactor 部品 | §B の全 lemma | **(a) Mathlib + (b) repo 既存** | 全 `@audit:ok` |

**集計**: (a) Mathlib 実在 = 2 (parametric gateway + §B Gaussian-integral 部品群)、(b) repo 実在 = 4 (heat-eq STEP D / IBP atom / fisher_from_logDeriv / chain rule + §B repo bridges)、**(c) 自作壁 (PR 級) = 1 (Stam convolution Fisher bound、fisher-finiteness と共有)**。

---

## 撤退ラインへの距離

- 親計画 `epi-debruijn-pertime-closure-plan.md` の撤退ライン L-PT-γ (domination が PR 級) に **触れるが発動しない**。案B は `_chain_domination` の現 defect 形 (`@audit:defect(false-statement)`) を **真命題 + honest sorry** に戻す方向の作業で、現 `@residual(plan:epi-debruijn-pertime-closure)` の正規撤退口に整合する (load-bearing hyp なし、`hpX_*` は全 regularity)。
- **撤退ライン発動: no**。案B の核壁は fisher-finiteness と共有の self-write 可能壁 (Mathlib 概念欠落だが PR で埋まる)。縮退案を新撤退ラインとして立てる必要なし。
- ただし **defect 解消の前提条件**: `_chain_domination` の現 `@audit:defect(false-statement)` マーカー (case A の GAP②false-statement に依拠) は、案B 実装で **GAP② (`convDensityAdd_deriv2_tail_majorant`, `:528`, Gaussian-tail false) を捨て、joint envelope (Fisher 経由 polynomial×Gaussian-from-g_s) に置換する** ことで初めて消える。GAP② を残したまま joint を積むと vacuous-genuine 罠 (監査 `:603` 既指摘) を再発するので、**実装時 GAP② declaration は撤回 or polynomial-majorant に書換 (Gaussian-tail 結論を削除)** が必須 (撤退口 = sorry + `@residual`、Gaussian-tail false 結論の据置は禁止)。

---

## 案B 推奨 skeleton 構造の素案 (planner への申し送り)

**joint envelope を 2 named sub-lemma + 1 shared 壁に分解** (分離積 GAP①×GAP② は破棄):

```lean
import InformationTheory.Shannon.FisherInfoV2DeBruijnPerTime

namespace InformationTheory.Shannon.FisherInfoV2

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ENNReal NNReal
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)

-- 【核壁・共有】Stam convolution Fisher bound (= fisher-finiteness R-A 補題)
-- 新 file InformationTheory/Shannon/FisherConvBound.lean に集約推奨 (fisher-finiteness と 1 本共有)
theorem gaussianConv_fisher_le_inv_var
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {s : ℝ} (hs : 0 < s) :
    fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      ≤ ENNReal.ofReal (1 / s) := by
  sorry -- @residual(wall:fisher-finiteness)  ← shared、両 family で reuse

-- 【sub-lemma 1】σ-derivand の honest polynomial-moment 上界 (Gaussian 保持、prefactor で落とさない)
-- ‖∂²_x p_s x‖ ≤ ∫ pX(y)·g_s(x-y)·|(x-y)²/s²-1/s| dy → 1st/2nd moment 展開で finite-coeff × Gaussian-conv
private theorem convDensityAdd_deriv2_poly_moment_majorant
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      ∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s, _⟩))) x‖ ≤ bound x := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)  ← GAP② を Gaussian-tail から polynomial-moment に書換

-- 【本体】joint domination: log-factor (~x², GAP① genuine 既存) × Hess (poly-moment envelope)
-- の積が integrable。case A 分離積の罠を避けるため product の integrability を
-- 「log の x² × ∂²p の integrable envelope」ではなく「σ-derivand 積分値 = J(p_s) 有限」経由で確認
private theorem debruijnIdentityV2_holds_assembled_chain_domination
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    ∃ bound : ℝ → ℝ, Integrable bound volume ∧
      (∀ᵐ x ∂volume, ∀ s : ℝ, (hs : s ∈ Set.Ioo (t/2) (2*t)) →
        ‖(- Real.log (convDensityAdd pX (gaussianPDFReal 0 ⟨s, _⟩) x) - 1)
            * ((1/2) * deriv (deriv (convDensityAdd pX (gaussianPDFReal 0 ⟨s, _⟩))) x)‖
          ≤ bound x) := by
  sorry -- @residual(plan:epi-debruijn-pertime-closure)
```

**分解判断 (joint bound 1 本 vs Fisher経由+entropy経由の2本)**:
- **推奨 = sub-lemma 1 (deriv2 polynomial-moment envelope) + 既存 GAP① log majorant の積、本体で product integrability を §B `integrable_natPow_mul_exp_neg_mul_sq` で組む**。case A との違いは sub-lemma 1 が **Gaussian-tail (`exp(-x²/c')`、false) でなく `g_s(x-y)` の Gaussian を畳込内に保持した polynomial-moment envelope (true)** を出す点。`∫pX(y)g_s(x-y)(x-y)²dy` の x-依存は `g_s` の Gaussian decay × moment poly で integrable。
- joint で「積の integrability を一気に」やる代替もあるが、log の `~x²` × Hess の honest envelope の product が integrable であることの確認に Fisher 値 (`J(p_s)<∞`) を経由するのが最も clean (#1 核壁を 1 度通せば pointwise envelope の存在も保証される)。**実装で sub-lemma 1 の polynomial-moment envelope が log の `~x²` を吸収して integrable になるか (= product が真に integrable か) は、Fisher finiteness で先に積分値有限を確認してから pointwise envelope を逆算する設計を推奨** (case A の「pointwise Gaussian-tail を主張して破綻」を避ける)。

---

## 着手 skeleton (新 file 候補、20-30 行)

> 案B 実装は既存 `FisherInfoV2DeBruijnAssembly.lean` の `_chain_domination` body 書換 + GAP②
> declaration の polynomial-moment 化 (Gaussian-tail 結論削除) + 新 shared 壁 `FisherConvBound.lean`
> の 3 箇所。下記は shared 壁 file の出だし。

```lean
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.FisherInfoV2
import InformationTheory.Shannon.FisherInfoV2DeBruijn  -- V2 Gaussian 閉形 J(𝒩(0,s))=1/s
import InformationTheory.Shannon.StamGaussianBound      -- stam_fisher_arith

namespace InformationTheory.Shannon.FisherInfoV2

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open InformationTheory.Shannon.EPIConvDensity (convDensityAdd)

/-- **Shared Mathlib wall: Stam convolution Fisher bound** `J(pX ∗ g_s) ≤ 1/s`.
任意確率密度 pX (重い裾含む) で成立。fisher-finiteness と案B joint domination の core を共有。
@residual(wall:fisher-finiteness) -/
theorem gaussianConv_fisher_le_inv_var
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) {s : ℝ} (hs : 0 < s) :
    fisherInfoOfDensity (convDensityAdd pX (gaussianPDFReal 0 ⟨s, hs.le⟩))
      ≤ ENNReal.ofReal (1 / s) := by
  sorry -- @residual(wall:fisher-finiteness)

end InformationTheory.Shannon.FisherInfoV2
```

(独立 honesty 監査必須: 新規 shared sorry 補題追加 + `_chain_domination` / `convDensityAdd_fisher_integrable` の body 書換は CLAUDE.md「Independent honesty audit」起動条件該当。`gaussianConv_fisher_le_inv_var` が load-bearing でない (regularity 引数のみ、結論 = 有限上界) こと、両 consumer が壁を lemma call で受けていることを fresh auditor が確認。GAP② の Gaussian-tail false 結論が撤回 or polynomial-moment 化されたことも確認。)
