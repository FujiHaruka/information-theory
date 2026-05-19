# Chernoff / Hoeffding (T1-B + T1-D) Mathlib + Common2026 inventory

> Source materials: roadmap `docs/textbook-roadmap.md` §T1-B (lines 126–133) + §T1-D (lines 144–150).
> Predecessor inventories: `docs/shannon/stein-mathlib-inventory.md`,
> `docs/shannon/stein-converse-mathlib-inventory.md`,
> `docs/shannon/strong-stein-mathlib-inventory.md`,
> `docs/shannon/sanov-mathlib-inventory.md`,
> `docs/shannon/pinsker-mathlib-inventory.md`.

## 一行サマリ

**T1-B Chernoff + T1-D Hoeffding 一括着手のために必要な API のうち、実体は 90% 既存
(Mathlib `Measure.tilted` family + Common2026 Stein/Sanov plumbing + Mathlib `inner_le_Lp_mul_Lq_of_nonneg`/`geom_mean_le_arith_mean_weighted` 完備)。
自作は 4 種 (Chernoff exponent `chernoffInfo P Q`、Hoeffding tradeoff `hoeffdingE2 α P Q`、
Chernoff exponent 凸性 + min 達成性、Sanov-LDP → Chernoff/Hoeffding 橋渡し補題) のみ。
撤退ラインは「Mathlib `Measure.tilted` の Boolean tilt 形 `μ.tilted (λ • llrPmf)` を Pi 測度に持ち上げる
plumbing が想定以上に肥大化した場合」に新規追加すべき。proof-log の「Stein/Sanov plumbing から 70-80% 再利用」
主張は (a) Sanov LDP 上限/下限 + (b) Stein-typical set / steinOptimalBeta 機構 (c) `klDivSumForm`
の 3 系列に分解すれば達成可能と見積もる。**

| 数値 | 値 |
|---|---|
| 既存 API カバレッジ (実体ベース) | **約 90%** (Mathlib + Common2026) |
| 自作必要な top-level | **4 種** (`chernoffInfo`, `hoeffdingE2`, `chernoffInfo_continuous_in_lam` + `min` 達成性, Sanov→Chernoff bridge) |
| roadmap 規模見積もり (600-900 行) の妥当性 | **整合**: ~700 行を中央予測 (T1-B ~450 + T1-D ~250) |
| 撤退ライン発動 (現時点) | **No** (現状 plumbing 想定内) |

---

## 主定理の最終形 (再掲、roadmap §T1-B / §T1-D より)

### T1-B Chernoff Information

教科書 statement (Cover-Thomas 11.9.1):

```
P_e^{(n)}  ≐  exp(-n · C(P₁, P₂))
where  C(P₁, P₂) := -min_{λ ∈ [0,1]} log ∑_x P₁(x)^λ P₂(x)^{1-λ}
```

Lean 風 signature (Common2026 既存 convention に合わせる):

```lean
namespace InformationTheory.Shannon.Chernoff

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Pointwise tilted weight `P₁(x)^λ · P₂(x)^{1-λ}` (Cover-Thomas 11.9.1). -/
noncomputable def chernoffTilt (P₁ P₂ : Measure α) (lam : ℝ) (x : α) : ℝ :=
  (P₁.real {x}) ^ lam * (P₂.real {x}) ^ (1 - lam)

/-- The Chernoff information `C(P₁, P₂)`: minimum over `λ ∈ [0,1]` of
`-log ∑_x P₁(x)^λ P₂(x)^{1-λ}`. -/
noncomputable def chernoffInfo (P₁ P₂ : Measure α) : ℝ :=
  -Real.log (sInf ((fun lam => ∑ x : α, chernoffTilt P₁ P₂ lam x) '' Set.Icc (0:ℝ) 1))
  -- (alternative: write via `iInf_image` once min-attainment is proved)

theorem chernoff_lemma  -- Cover-Thomas 11.9.1
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P₁ P₂ : Measure α) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P₁)
    (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P₁))
    (hPpos : ∀ x : α, 0 < P₁.real {x}) (hQpos : ∀ x : α, 0 < P₂.real {x}) :
    -- Bayes-error decay rate equals Chernoff information.
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (bayesErrorMin P₁ P₂ n))
      atTop (𝓝 (chernoffInfo P₁ P₂))
```

### T1-D Hoeffding Type I/II tradeoff exponent

教科書 statement:

```
任意 α ∈ [0, D(P₁‖P₂)] に対し
E₂(α)  :=  min_{Q : D(Q‖P₁) ≤ α} D(Q‖P₂)
```

Lean 風 signature:

```lean
/-- Hoeffding tradeoff exponent `E₂(α)`: minimum `D(Q‖P₂)` over the closed sublevel
set `{Q : pmf | D(Q‖P₁) ≤ α}`. -/
noncomputable def hoeffdingE2 (P₁ P₂ : α → ℝ) (alpha : ℝ) : ℝ :=
  sInf (klDivPmf · P₂ '' {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha})

theorem hoeffding_tradeoff_lemma
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_le : alpha ≤ klDivPmf P₁ P₂) :
    -- For any α-level test ⟨achievable Type I exponent ≤ alpha⟩,
    -- best Type II exponent equals hoeffdingE2 alpha P₁ P₂.
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (steinTypeII_at_level P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha))
```

### 証明戦略 (pseudo-Lean, T1-B/T1-D 共通)

```text
1.  T_λ := tiltedPmf P₁ P₂ λ  -- mediator distribution
        := chernoffTilt P₁ P₂ λ x / Z(λ)
        where Z(λ) := ∑ x, chernoffTilt P₁ P₂ λ x          (Mathlib `Measure.tilted` 経由)
2.  klDivPmf T_λ P₁ = ⟨log-derivative form⟩, klDivPmf T_λ P₂ = ⟨log-derivative form⟩
        (Mathlib `integral_llr_tilted_left`/`integral_llr_tilted_right`)
3.  -log Z(λ) = λ · klDivPmf T_λ P₁ + (1-λ) · klDivPmf T_λ P₂
        (algebraic identity from tilted-llr expansion)
4.  Chernoff lower bound:
    P_e^{(n)} ≥ (1/2) · min(P₁^n(B^c), P₂^n(B))
              ≥ exp(-n · chernoffInfo) · poly(n)     (Sanov LDP per-tilt + matching error sets)
5.  Chernoff upper bound (likelihood-ratio test):
    P_e^{(n)} ≤ exp(-n · chernoffInfo)             (multiplicative Chernoff via tilt)
6.  Hoeffding E₂(α) attained at T_λ* where λ* solves
        klDivPmf T_λ P₁ = α   ⇒   E₂(α) = klDivPmf T_λ* P₂.
        (Lagrange duality, but easier: monotonicity of klDivPmf T_λ P₂ in λ + IVT.)
```

---

## API 在庫テーブル

### A. Exponential tilting (Chernoff / Hoeffding の中核 mediator)

| 概念 | Mathlib API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| Exponentially tilted measure | `Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α := μ.withDensity (fun x => ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))` — `Mathlib/MeasureTheory/Measure/Tilted.lean:42` | ✅ 既存 | **Chernoff exponent の mediator 分布の核**。`f := lam • llrPmf P₁ P₂` で T_λ を構築 |
| Tilted is probability measure | `lemma isProbabilityMeasure_tilted [NeZero μ] (hf : Integrable (fun x ↦ exp (f x)) μ) : IsProbabilityMeasure (μ.tilted f)` — `Tilted.lean:126` | ✅ 既存 | mediator T_λ が確率測度であることの確認 (Fintype + full support から自動) |
| Tilted absolutely continuous | `lemma tilted_absolutelyContinuous (μ : Measure α) (f : α → ℝ) : μ.tilted f ≪ μ` — `Tilted.lean:280` | ✅ 既存 | T_λ ≪ P₁ (klDivPmf 計算の入口) |
| Reverse absolute continuity | `lemma absolutelyContinuous_tilted (hf : Integrable (fun x ↦ exp (f x)) μ) : μ ≪ μ.tilted f` — `Tilted.lean:283` | ✅ 既存 | P₁ ≪ T_λ (双方向対称性) |
| Compose tilts | `lemma tilted_tilted (hf : Integrable (fun x ↦ exp (f x)) μ) (g : α → ℝ) : (μ.tilted f).tilted g = μ.tilted (f + g)` — `Tilted.lean:251` | ✅ 既存 | T_λ from P₁ vs T_λ from P₂ の連結に利用 |
| Integral against tilt | `lemma integral_tilted (f : α → ℝ) (g : α → E) : ∫ x, g x ∂(μ.tilted f) = ∫ x, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ` — `Tilted.lean:230` | ✅ 既存 | klDivPmf T_λ · を展開する step |
| Integral exp against tilt | `lemma integral_exp_tilted (f g : α → ℝ) : ∫ x, exp (g x) ∂(μ.tilted f) = (∫ x, exp ((f + g) x) ∂μ) / ∫ x, exp (f x) ∂μ` — `Tilted.lean:236` | ✅ 既存 | CGF chain `Λ(λ₁+λ₂) = Λ(λ₁) + ⟨Λ_under_tilt(λ₂)⟩` |
| RN derivative right tilt | `lemma rnDeriv_tilted_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hf : Integrable (fun x ↦ exp (f x)) ν) : ...` — `Tilted.lean:314` | ✅ 既存 | klDiv (μ ‖ ν.tilted f) の展開 |
| RN derivative left tilt | `lemma rnDeriv_tilted_left {ν : Measure α} [SigmaFinite μ] [SigmaFinite ν] (hfν : AEMeasurable f ν) : ...` — `Tilted.lean:342` | ✅ 既存 | klDiv (μ.tilted f ‖ ν) の展開 |

### B. Log-likelihood ratio under tilt (Mathlib `LogLikelihoodRatio`)

| 概念 | Mathlib API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| Log-likelihood ratio | `noncomputable def llr (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal` — `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean:37` | ✅ 既存 | Stein.lean の `llrPmf P Q` と互換 (我々の form は finite-alphabet ver) |
| LLR identity (tilted left) | `lemma llr_tilted_left [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν) : (llr (μ.tilted f) ν) =ᵐ[μ] fun x ↦ f x - log (∫ z, exp (f z) ∂μ) + llr μ ν x` — `LogLikelihoodRatio.lean:177` | ✅ 既存 | **Chernoff exponent 核**: `llr (T_λ ‖ P₂) = f - log Z + llr (P₁ ‖ P₂)` |
| Integral LLR tilted left | `lemma integral_llr_tilted_left [IsProbabilityMeasure μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ) (hfμ : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν) : ∫ x, llr (μ.tilted f) ν x ∂μ = ∫ x, llr μ ν x ∂μ + ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ)` — `LogLikelihoodRatio.lean:202` | ✅ 既存 | klDivPmf T_λ P₂ の数値展開直書き (一発で `λ·D + ⟨f⟩ - log Z` 形に) |
| LLR identity (tilted right) | `lemma llr_tilted_right [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : Integrable (fun x ↦ exp (f x)) ν) : (llr μ (ν.tilted f)) =ᵐ[μ] fun x ↦ -f x + log (∫ z, exp (f z) ∂ν) + llr μ ν x` — `LogLikelihoodRatio.lean:216` | ✅ 既存 | 対称ケース |
| Integral LLR tilted right | `lemma integral_llr_tilted_right [IsProbabilityMeasure μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν) (h_int : Integrable (llr μ ν) μ) : ∫ x, llr μ (ν.tilted f) x ∂μ = ∫ x, llr μ ν x ∂μ - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν)` — `LogLikelihoodRatio.lean:238` | ✅ 既存 | klDivPmf P₁ T_λ の展開 |
| Integrable LLR tilted | `lemma integrable_llr_tilted_left [IsFiniteMeasure μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ) (hfμ : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν) : Integrable (llr (μ.tilted f) ν) μ` — `LogLikelihoodRatio.lean:195` | ✅ 既存 | tilted LLR の integrability 自動証明 |

### C. Mathlib KL divergence + KLFun (T1-B/D の `klDiv (T_λ ‖ P_i)` の素材)

| 概念 | Mathlib API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| KL divergence definition | `noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞ := if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) else ∞` — `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` | ✅ 既存 | Hoeffding `E₂(α) := min D(Q‖P₂)` の被最適化対象 |
| toReal of KL on probabilities | `lemma toReal_klDiv_of_measure_eq (h : μ ≪ ν) (h_eq : μ univ = ν univ) : (klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ` — `Basic.lean:164` (with `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` from section, line 146) | ✅ 既存 | Real 値の klDiv 計算口 |
| KL via klFun integral | `lemma klDiv_eq_lintegral_klFun_of_ac (h_ac : μ ≪ ν) : klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν` — `Basic.lean:138` (with `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`) | ✅ 既存 | f-divergence 形 |
| klFun definition | `def klFun (x : ℝ) : ℝ := x * log x + 1 - x` — `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:50-55` (klFun_apply, `Set.Ici 0` 上の `klFun_nonneg`) | ✅ 既存 | T_λ の凸性引数 |
| klFun strict convexity | `lemma strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun` — `KLFun.lean:62` | ✅ 既存 | Hoeffding `E₂` 一意性 / Csiszar projection 再利用 |
| klFun continuity | `lemma continuous_klFun : Continuous klFun` — `KLFun.lean:76` | ✅ 既存 | `klDivPmf P Q` の `P` 連続性 (既に `Common2026/Shannon/CsiszarProjection.lean:71` で利用) |
| klFun nonneg | `lemma klFun_nonneg (hx : 0 ≤ x) : 0 ≤ klFun x` — `KLFun.lean:149` | ✅ 既存 | Hoeffding `E₂(α) ≥ 0` |
| KL chain rule | `theorem klDiv_compProd_eq_add (μ ν : Measure α) (κ η : Kernel α β) : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)` — `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204` | ✅ 既存 | n-IID 化に `Measure.pi` 経由で使う (Stein.lean:643 `klDiv_pi_eq_n_smul` 系の流用) |
| KL ⊗ left invariance | `lemma klDiv_compProd_left (μ ν : Measure α) (κ : Kernel α β) : klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) = klDiv μ ν` — `ChainRule.lean:182` (`@[simp]`) | ✅ 既存 | Common2026 `MutualInfo.lean:88` `klDiv_prod_const_left` で既に再利用済 |
| KL eq zero iff | `lemma klDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] : klDiv μ ν = 0 ↔ μ = ν` — `Basic.lean:377` (with `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`) | ✅ 既存 | E₂(α=0) = D(P₁‖P₂) の端点 (degenerate case) |

### D. Common2026 Stein / Sanov / LLR plumbing (proof-log 70-80% 主張の実体)

#### D-1. Stein 系 (`Common2026/Shannon/Stein.lean`)

| 概念 | Common2026 API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| Pointwise LLR pmf | `noncomputable def llrPmf (P Q : Measure α) : α → ℝ := fun x => Real.log (P.real {x}) - Real.log (Q.real {x})` — `Stein.lean:53` | ✅ 既存 | **Chernoff: `lam • llrPmf P₁ P₂` を `Measure.tilted` の引数 `f` として使う** |
| Per-symbol LLR | `noncomputable def logLikelihoodRatio (P Q : Measure α) (Xs : ℕ → Ω → α) (i : ℕ) : Ω → ℝ` — `Stein.lean:61` | ✅ 既存 | n-IID Chernoff の per-letter argument |
| LLR measurability | `lemma measurable_llrPmf (P Q : Measure α) : Measurable (llrPmf P Q)` — `Stein.lean:57` (with `[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]`) | ✅ 既存 | tilt 引数の measurability |
| LLR integrability | `lemma integrable_logLikelihoodRatio (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure α) (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (i : ℕ) : Integrable (logLikelihoodRatio P Q Xs i) μ` — `Stein.lean:79` (`[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]`) | ✅ 既存 | `Measure.tilted` の Integrable 前提を満たす |
| Mean LLR under P = KL | `theorem integral_logLikelihoodRatio_under_P (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hMap : μ.map (Xs 0) = P) (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) : ∫ ω, logLikelihoodRatio P Q Xs 0 ω ∂μ = (klDiv P Q).toReal` — `Stein.lean:97` | ✅ 既存 | E_P[LLR] = D(P‖Q) (Chernoff の λ=1 端点) |
| Stein strong law (2 dist) | `theorem stein_strong_law (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hMap : μ.map (Xs 0) = P) (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) : ...` — `Stein.lean:185` | ✅ 既存 | Chernoff lower bound での AEP 機構 |
| Stein typicality (P side) | `theorem steinTypicalSet_P_prob_tendsto_one ... → Tendsto ... atTop (𝓝 1)` — `Stein.lean:275` | ✅ 既存 | T_λ 上の typicality set 作り直しの prototype |
| Stein Q-side mass bound | `theorem steinTypicalSet_Q_prob_le (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPpos : ∀ x : α, 0 < P.real {x}) (hQpos : ∀ x : α, 0 < Q.real {x}) (n : ℕ) (ε : ℝ) : ((Measure.pi (fun _ : Fin n => Q)) (steinTypicalSet P Q n ε)).toReal ≤ Real.exp (-((n : ℝ) * ((klDiv P Q).toReal - ε)))` — `Stein.lean:341` | ✅ 既存 | **Chernoff upper bound の per-tilt 量推定の direct template** |
| stein_achievability | `theorem stein_achievability ...` — `Stein.lean:488` | ✅ 既存 | Hoeffding の Type II 側 lower bound の参考 |
| stein_converse_finite_n | `theorem stein_converse_finite_n ...` — `Stein.lean:975` | ✅ 既存 | Hoeffding Type II upper bound (Type I level alpha 固定) |
| steinOptimalBeta | `noncomputable def steinOptimalBeta (P Q : Measure α) (n : ℕ) (ε : ℝ) : ℝ := sInf (steinBetaSet P Q n ε)` — `Stein.lean:1146` | ✅ 既存 | `hoeffdingE2 alpha` の n-変動形 |
| Stein lemma sandwich | `theorem stein_lemma ... (klDiv P Q).toReal ≤ liminf ... ∧ limsup ... ≤ (klDiv P Q).toReal / (1 - ε)` — `Stein.lean:1390` | ✅ 既存 | T1-D Hoeffding の Type I 端点 |
| Stein strong lemma | `theorem stein_strong_lemma ... Tendsto ... (𝓝 (klDiv P Q).toReal)` — `StrongStein.lean:498` | ✅ 既存 | Hoeffding strict `Tendsto` version (再利用) |

#### D-2. Sanov 系 (`Common2026/Shannon/Sanov.lean`, `SanovLDP.lean`, `SanovLDPEquality.lean`)

| 概念 | Common2026 API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| Type class | `noncomputable def typeClass (P : Measure α) (n : ℕ) : Set (Fin n → α) := { x | ∀ a : α, (typeCount x a : ℝ) = (n : ℝ) * P.real {a} }` — `Sanov.lean:54` | ✅ 既存 | Chernoff 下界での Sanov LDP 起動点 |
| TypeCountIndex | `abbrev TypeCountIndex (α : Type*) [Fintype α] (n : ℕ) : Type _ := α → Fin (n+1)` — `SanovLDP.lean:55` | ✅ 既存 | E_n family (Chernoff: T_λ 近傍の type 全体) |
| typeClassByCount | `def typeClassByCount {n : ℕ} (c : α → ℕ) : Set (Fin n → α)` — `SanovLDP.lean:82` | ✅ 既存 | Sanov 経路の primitive |
| klDivSumForm | `noncomputable def klDivSumForm (P Q : Measure α) : ℝ := ∑ a : α, P.real {a} * (Real.log (P.real {a}) - Real.log (Q.real {a}))` — `Sanov.lean:73` | ✅ 既存 | Real 値 klDiv (Chernoff exponent の reformulation 出口) |
| klDivSumForm = (klDiv).toReal | `theorem klDivSumForm_eq_toReal_klDiv (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQpos : ∀ a : α, 0 < Q.real {a}) : klDivSumForm P Q = (klDiv P Q).toReal` — `Sanov.lean:252` | ✅ 既存 | Mathlib klDiv との bridge |
| klDivSumForm_ofVec | `noncomputable def klDivSumForm_ofVec (p q : α → ℝ) : ℝ` — `KLDivContinuous.lean:31` | ✅ 既存 | `(p, q)` formal version (vec 入力、Hoeffding `klDivPmf` と同形) |
| klDivSumForm_ofVec continuity | `theorem klDivSumForm_ofVec_continuous (q : α → ℝ) (hq : ∀ a, 0 < q a) : Continuous (fun p : α → ℝ => klDivSumForm_ofVec p q)` — `KLDivContinuous.lean:45` | ✅ 既存 | **Hoeffding `E₂(α)` 連続性 + 最適化対象の閉性に必須** |
| klDivIndex | `noncomputable def klDivIndex (c : α → ℕ) (n : ℕ) (Q : Measure α) : ℝ` — `SanovLDP.lean:97` | ✅ 既存 | Per-type exponent (Chernoff/Hoeffding の sum-over-types で使う) |
| Sanov A-form upper | `theorem typeClass_Qn_le_klDiv (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPpos : ∀ a : α, 0 < P.real {a}) (hQpos : ∀ a : α, 0 < Q.real {a}) (hPQ : P ≪ Q) (n : ℕ) : ((Measure.pi (fun _ : Fin n => Q)) (typeClass P n)).toReal ≤ Real.exp (-((n : ℝ) * (klDiv P Q).toReal))` — `Sanov.lean:305` | ✅ 既存 | **Chernoff upper bound: T_λ 側 mass の `exp(-n D(T_λ‖P_i))` 上限** |
| Sanov LDP upper bound | `theorem sanov_ldp_upper_bound (Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a : α, 0 < Q.real {a}) (E : ∀ n, Finset (TypeCountIndex α n)) (D : ℝ) (h_min : ∀ n c, c ∈ E n → D ≤ klDivIndex (fun a => (c a : ℕ)) n Q) {ε : ℝ} (hε : 0 < ε) : ∃ N₀, ∀ n ≥ N₀, ...` — `SanovLDP.lean:471` (simplified) | ✅ 既存 | Hoeffding 上限の核 |
| Sanov LDP equality | `theorem sanov_ldp_equality (Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a : α, 0 < Q.real {a}) (P : α → ℝ) (hP_prob : (∑ a, P a) = 1) (hP_full : ∀ a, 0 < P a) (E : ∀ n, Finset (TypeCountIndex α n)) (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n) (h_minimizer : ∀ n, ∀ c ∈ E n, klDivSumForm_ofVec P (fun a => Q.real {a}) ≤ klDivIndex (fun a => (c a : ℕ)) n Q) : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (((Measure.pi (fun _ : Fin n => Q)) (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal)) atTop (𝓝 (-(klDivSumForm_ofVec P (fun a => Q.real {a}))))` — `SanovLDPEquality.lean:1243` | ✅ 既存 | **Chernoff lower bound: P = T_λ にとってこの式で `exp(-n · D(T_λ ‖ P_i))` の下限を取る** |
| Rounded type index | `noncomputable def roundedTypeIndex (P : α → ℝ) (n : ℕ) : TypeCountIndex α n` — `SanovLDPEquality.lean:111` | ✅ 既存 | T_λ 近傍 type の標準 construction (再利用) |

#### D-3. Csiszar projection (`Common2026/Shannon/CsiszarProjection.lean`)

| 概念 | Common2026 API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| klDivPmf (Real value) | `noncomputable def klDivPmf (P Q : α → ℝ) : ℝ := ∑ a : α, Q a * klFun (P a / Q a)` — `CsiszarProjection.lean:55` | ✅ 既存 | **Hoeffding E₂(α) の被最適化 functional** (定義そのもの) |
| klDivPmf nonneg | `lemma klDivPmf_nonneg (P Q : α → ℝ) (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) : 0 ≤ klDivPmf P Q` — `CsiszarProjection.lean:61` | ✅ 既存 | E₂(α) ≥ 0 |
| klDivPmf continuity in P | `lemma continuous_klDivPmf_left (Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) : Continuous (fun P : α → ℝ => klDivPmf P Q)` — `CsiszarProjection.lean:71` | ✅ 既存 | Hoeffding 制約集合上での連続性 |
| klDivPmf strict convexity in P | `lemma klDivPmf_strictConvexOn_left (Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) : StrictConvexOn ℝ (stdSimplex ℝ α) (fun P : α → ℝ => klDivPmf P Q)` — `CsiszarProjection.lean:93` | ✅ 既存 | E₂(α) の達成点 (T_λ*) の一意性 |
| Compact-from-simplex | `lemma isCompact_of_subset_stdSimplex {K : Set (α → ℝ)} (hK_closed : IsClosed K) (hK_sub : K ⊆ stdSimplex ℝ α) : IsCompact K` — `CsiszarProjection.lean:165` | ✅ 既存 | `{Q : D(Q‖P₁) ≤ α}` のコンパクト化 (extreme value) |
| Csiszar projection 存在 | `theorem csiszar_projection_exists {K : Set (α → ℝ)} {Q : α → ℝ} (hK_closed : IsClosed K) (hK_sub : K ⊆ stdSimplex ℝ α) (hK_ne : K.Nonempty) (hQ_pos : ∀ a, 0 < Q a) : ∃ Qstar ∈ K, IsMinOn (fun P => klDivPmf P Q) K Qstar` — `CsiszarProjection.lean:172` | ✅ 既存 | **Hoeffding `min` 達成性 (K := {Q : D(Q‖P₁) ≤ α}) — 直接適用可** |
| Csiszar projection 一意性 | `theorem csiszar_projection_unique ...` — `CsiszarProjection.lean:186` | ✅ 既存 | E₂(α) 達成点の一意性 |
| Csiszar Pythagorean | `theorem csiszar_pythagoras_inequality ... klDivPmf P Q ≥ klDivPmf P Qstar + klDivPmf Qstar Q` — `CsiszarProjection.lean:449` | ✅ 既存 | Hoeffding の Lagrange 経路で活躍 (Cover-Thomas 11.6.1) |

### E. Convex / extreme-value / continuity infrastructure (Mathlib)

| 概念 | Mathlib API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| Extreme value (min) | `theorem IsCompact.exists_isMinOn [ClosedIicTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x` — `Mathlib/Topology/Order/Compact.lean:228` | ✅ 既存 | `hoeffdingE2` の `sInf → min` 引き換え (`CsiszarProjection` でも既に使用) |
| ConvexOn exp | `theorem convexOn_exp : ConvexOn ℝ univ exp` — `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:63` | ✅ 既存 | Chernoff exponent の `λ ↦ log Z(λ)` 凸性 (CGF) |
| StrictConcaveOn log on Ioi 0 | `theorem strictConcaveOn_log_Ioi : StrictConcaveOn ℝ (Ioi 0) log` — `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:67` | ✅ 既存 | Chernoff `-log Z(λ)` の凹形再構成 (note: `chernoffInfo := -min`, equivalent to `max` of concave function) |
| ConvexOn rpow | `theorem convexOn_rpow {p : ℝ} (hp : 1 ≤ p) : ConvexOn ℝ (Ici 0) fun x : ℝ ↦ x ^ p` — `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:207` | ✅ 既存 | rpow 単項の凸性 (補助) |
| ConvexOn klFun | `lemma convexOn_klFun : ConvexOn ℝ (Ici 0) klFun` — `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:67` | ✅ 既存 | Hoeffding `E₂` 一意化、Csiszar の延長 |

### F. Real `rpow` + `log` algebra (Chernoff exponent の式変形素材)

| 概念 | Mathlib API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| `rpow_natCast` | `theorem Real.rpow_natCast (x : ℝ) (n : ℕ) : x ^ (n : ℝ) = x ^ n` — `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:62` | ✅ 既存 | n-IID で `P^λ` を sum-of-powers に展開 |
| `rpow_zero` | `theorem Real.rpow_zero (x : ℝ) : x ^ (0 : ℝ) = 1` — `Pow/Real.lean:120` | ✅ 既存 | 端点 λ=0 |
| `rpow_one` | `theorem Real.rpow_one (x : ℝ) : x ^ (1 : ℝ) = x` — `Pow/Real.lean:148` | ✅ 既存 | 端点 λ=1 |
| `rpow_add` | `theorem Real.rpow_add (hx : 0 < x) (y z : ℝ) : x ^ (y + z) = x ^ y * x ^ z` — `Pow/Real.lean:207` | ✅ 既存 | Chernoff exponent の indicator factor 化 |
| `rpow_mul` | `theorem Real.rpow_mul {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z` — `Pow/Real.lean:412` | ✅ 既存 | tilt power の reshape |
| `log_rpow` | `theorem Real.log_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : log (x ^ y) = y * log x` — `Pow/Real.lean:490` | ✅ 既存 | `log P^λ = λ · log P` (chernoff exponent の核) |
| `rpow_le_rpow` | `theorem Real.rpow_le_rpow {x y z : ℝ} (h : 0 ≤ x) (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z` — `Pow/Real.lean:546` | ✅ 既存 | monotonicity (tilt mass 推定) |
| `rpow_nonneg` | `theorem Real.rpow_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ x ^ y` — `Pow/Real.lean:163` | ✅ 既存 | positivity in chernoffTilt |
| `rpow_pos_of_pos` | `theorem Real.rpow_pos_of_pos {x : ℝ} (hx : 0 < x) (y : ℝ) : 0 < x ^ y` — `Pow/Real.lean:116` | ✅ 既存 | full-support 下の strict positivity |

### G. Hölder inequality + AM-GM (Chernoff `log ∑ P₁^λ P₂^{1-λ}` 操作)

| 概念 | Mathlib API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| Real Hölder (Finset) | `theorem Real.inner_le_Lp_mul_Lq_of_nonneg (hpq : HolderConjugate p q) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) : ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q)` — `Mathlib/Analysis/MeanInequalities.lean:776` | ✅ 既存 | **Chernoff exponent 上界の核**: `∑ P₁^λ P₂^{1-λ} ≤ (∑ P₁)^λ (∑ P₂)^{1-λ} = 1` (degenerate case proof template, real case via `HolderConjugate (1/λ) (1/(1-λ))`) |
| Real AM-GM weighted | `theorem Real.geom_mean_le_arith_mean_weighted (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) : ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i` — `Mathlib/Analysis/MeanInequalities.lean:130` | ✅ 既存 | `T_λ(x) · log(P₁(x)/P₂(x))` の AM-GM 系評価 |
| NNReal Hölder (Finset) | `theorem NNReal.inner_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q : ℝ} (hpq : p.HolderConjugate q) : ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q)` — `MeanInequalities.lean:478` | ✅ 既存 | NNReal route (fallback) |

### H. n-IID infrastructure (`Common2026/Shannon/Stein.lean` の Pi 仕組み + Mathlib `Measure.pi`)

| 概念 | API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| `Measure.pi` for finite-alphabet IID | `Mathlib/MeasureTheory/Constructions/Pi.lean` (Stein.lean 既使用) | ✅ 既存 | n-IID `P^n` |
| `Measure.pi_singleton` | (used in Stein.lean:372) | ✅ 既存 | per-point joint mass の積形 |
| `klDiv_pi_zero` | `theorem klDiv_pi_zero (P Q : Measure α) : klDiv (Measure.pi (fun _ : Fin 0 => P)) (Measure.pi (fun _ : Fin 0 => Q)) = 0` — `Stein.lean:643` | ✅ 既存 | n=0 端点 |
| `klDiv_pi_succ` | `theorem klDiv_pi_succ (n : ℕ) (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : klDiv (Measure.pi (fun _ : Fin (n+1) => P)) (Measure.pi (fun _ : Fin (n+1) => Q)) = klDiv P Q + klDiv (Measure.pi (fun _ : Fin n => P)) (Measure.pi (fun _ : Fin n => Q))` — `Stein.lean:656` | ✅ 既存 | 帰納推移 |
| `klDiv_pi_eq_n_smul` | `theorem klDiv_pi_eq_n_smul (n : ℕ) (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : klDiv (Measure.pi (fun _ : Fin n => P)) (Measure.pi (fun _ : Fin n => Q)) = n • klDiv P Q` — `Stein.lean:713` | ✅ 既存 | **D(T_λ^n ‖ P_i^n) = n · D(T_λ ‖ P_i)** (Chernoff の n-IID 換算) |
| `jointRV` | (Stein.lean 既存) | ✅ 既存 | n-letter sample にして `μ.map (jointRV Xs n) = P^n` |

### I. Asymptotic / `\doteq` (T1-B Chernoff statement の表現)

| 概念 | Common2026 API / file:line | 状態 | T1-B/D での扱い |
|---|---|---|---|
| `DotEq` (= `\doteq`) | `def DotEq (a b : ℕ → ℝ) : Prop := (fun n : ℕ => Real.log (a n) - Real.log (b n)) =o[atTop] (fun n : ℕ => (n : ℝ))` — `Common2026/InformationTheory/Asymptotic.lean:43` (notation `a ≐ b` in scoped `InformationTheory.Asymptotic`) | ✅ 既存 | **T1-B Chernoff statement** `P_e^{(n)} ≐ exp(-n · chernoffInfo)` を expose する notation |
| `DotEq.refl/symm/trans` | `Asymptotic.lean:49/57/66` | ✅ 既存 | Chernoff statement の同等変形 |
| `DotEq.mul / inv` | `Asymptotic.lean:78/100` | ✅ 既存 | polynomial-factor の吸収 |
| `dotEq_iff_tendsto_log_div` | `lemma dotEq_iff_tendsto_log_div (a b : ℕ → ℝ) (hPos : ∀ n, 0 < a n ∧ 0 < b n) : a ≐ b ↔ Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (a n / b n)) atTop (𝓝 0)` — `Asymptotic.lean:116` | ✅ 既存 | Chernoff `Tendsto` ↔ `≐` の往復 |
| `exp_decay_N_of_pos` | `theorem exp_decay_N_of_pos {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') : ∃ N : ℕ, ∀ n ≥ N, Real.exp (-(n : ℝ) * g) < ε'` — `Asymptotic.lean:148` | ✅ 既存 | rate-extraction wrapper |

---

## 重要な前提条件 (事故が起きやすい lemma の type-class verbatim)

以下、Mathlib API の `[...]` 型クラス前提を **そのまま** 列挙する。T1-B/D 主定理に持ち込む際、これらは
**hidden assumption** として主定理 signature に伝播する。

### `Measure.tilted` family の前提

- `tilted_apply (μ : Measure α) [SFinite μ] (f : α → ℝ) (s : Set α) : ...`
  → **`[SFinite μ]`** が常に必要 (Fintype α なら `Measure.finite ⇒ SFinite`、Probability ⇒ Finite ⇒ SFinite で自動)
- `isProbabilityMeasure_tilted [NeZero μ] (hf : Integrable (fun x ↦ exp (f x)) μ) : IsProbabilityMeasure (μ.tilted f)`
  → **`[NeZero μ]` + `Integrable (exp ∘ f) μ`** が tilt 結果が probability measure になる前提
- `tilted_tilted (hf : Integrable (fun x ↦ exp (f x)) μ) (g : α → ℝ) : (μ.tilted f).tilted g = μ.tilted (f + g)`
  → `Integrable` 仮定が必要

**Fintype α + full support** (∀ x, 0 < P.real {x}) の場合: `Integrable (exp ∘ (lam • llrPmf P₁ P₂)) P₁`
は **自動** (`Integrable.of_finite` の伝播)。`[NeZero P₁]` は `IsProbabilityMeasure P₁` から従う。

### `Measure.pi` の前提

- `Measure.pi_singleton` (Stein.lean で利用): `[Fintype ι] [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]` 系の制約
  → 我々の T1-B/D 設定 (Fintype α + MeasurableSingletonClass α) で自動

### `klDiv` family の前提

- `klDiv_eq_lintegral_klFun_of_ac` は **`[IsFiniteMeasure μ] [IsFiniteMeasure ν]`** が必要 (section 全体に `variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]`, Basic.lean:108-146)
- `toReal_klDiv_of_measure_eq` も同上
- `klDiv_eq_zero_iff` **`[IsFiniteMeasure μ] [IsFiniteMeasure ν]`** が必要 (Basic.lean:377)
- **`klDiv_compProd_left`** は `[SigmaFinite μ] [SigmaFinite ν]` (Markov kernel `κ`) 暗黙

### `llr_tilted_left/right` の前提

- **`llr_tilted_left` の verbatim 前提**:
  `[SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν)`
  → `hfν` (ν 側 measurable も) を見落とすと proof が割れない
- **`integral_llr_tilted_left` の前提**:
  `[IsProbabilityMeasure μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ) (hfμ : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν)`
  → `[IsProbabilityMeasure μ]` (tilted source) を要求。**T1-B では我々の `μ = P₁` は `IsProbabilityMeasure` を仮定済みでクリア**

### Csiszar projection の前提 (Hoeffding の min 達成性に直接使う)

- `csiszar_projection_exists` の前提:
  `(hK_closed : IsClosed K) (hK_sub : K ⊆ stdSimplex ℝ α) (hK_ne : K.Nonempty) (hQ_pos : ∀ a, 0 < Q a)`
  → **`K := {Q ∈ stdSimplex | klDivPmf Q P₁ ≤ alpha}`** の閉性は `continuous_klDivPmf_left` + `IsClosed.preimage` で OK
  → **空でない**: `P₁ ∈ K` (since `klDivPmf P₁ P₁ = 0 ≤ alpha`、ただし `klDivPmf_self` の確認補題が必要 — `klFun_one = 0` から従う、自作補題 1 本)

### Hölder (Real) の前提

- `Real.inner_le_Lp_mul_Lq_of_nonneg (hpq : HolderConjugate p q) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)`
  → `HolderConjugate (1/λ) (1/(1-λ))` の構成補題: `1/(1/λ) + 1/(1/(1-λ)) = λ + (1-λ) = 1`、ただし `λ ∈ (0,1)` で **両端開** 要求あり (`HolderConjugate p q := 1 < p ∧ 1/p + 1/q = 1`)
  → λ = 0 / λ = 1 端点はそれぞれ `rpow_zero` / `rpow_one` で直接処理する別 case 必要

---

## 自作が必要な要素

優先度順、推奨実装、工数感、落とし穴。

### 自作 1: `chernoffTilt`, `chernoffPartition (Z(λ))`, `chernoffInfo` の定義 + 基本性質 (最優先)

**推奨実装** (Mathlib-shape driven):

```lean
/-- The Chernoff weight function `f_λ(x) := lam · log(P₁(x)) + (1-lam) · log(P₂(x))`,
i.e., `log (chernoffTilt P₁ P₂ lam x)`. This is the `f` we pass into `Measure.tilted`. -/
noncomputable def chernoffLogTilt (P₁ P₂ : Measure α) (lam : ℝ) : α → ℝ :=
  fun x => lam * Real.log (P₁.real {x}) + (1 - lam) * Real.log (P₂.real {x})

/-- The tilted-distribution mediator T_λ. -/
noncomputable def chernoffMediator (P₁ P₂ : Measure α) (lam : ℝ) : Measure α :=
  P₁.tilted (fun x => lam • (llrPmf P₂ P₁ x))
  -- = T_λ where T_λ(x) ∝ P₁(x)^(1-λ) · P₂(x)^λ
  -- (note convention swap: choose orientation to align with Mathlib's `Measure.tilted` of P₁)

/-- The Chernoff partition function Z(λ) := ∑_x P₁(x)^λ · P₂(x)^(1-λ). -/
noncomputable def chernoffZ (P₁ P₂ : Measure α) (lam : ℝ) : ℝ :=
  ∑ x : α, (P₁.real {x}) ^ lam * (P₂.real {x}) ^ (1 - lam)

/-- Chernoff information. -/
noncomputable def chernoffInfo (P₁ P₂ : Measure α) : ℝ :=
  -(sInf ((Real.log ∘ chernoffZ P₁ P₂) '' Set.Icc (0:ℝ) 1))
```

**戦略選択の理由**: `Measure.tilted` の signature `μ.tilted f := μ.withDensity (exp ∘ f / Z)` に合わせ、
`f := lam • llrPmf P₂ P₁` を渡せば exp(f) = (P₂/P₁)^λ になり、tilt 結果は P₁(x)·(P₂/P₁)^λ / Z = P₁^{1-λ}·P₂^λ/Z。
これで Mathlib の `integral_llr_tilted_left/right` が **そのまま** klDivPmf T_λ P₁ / klDivPmf T_λ P₂ を展開する。

**工数感**: 4 つの def + 5-6 補題 (continuity in λ, convexity of `log Z(λ)`, `Z(0) = Z(1) = 1`, `chernoffInfo ≥ 0`, etc.) で **~150-180 行**。

**落とし穴**:
1. `chernoffZ` を `∑ x : α, ...` 形 (Mathlib `chernoffTilt`) で書くか、`(P₁.tilted (lam • llrPmf P₂ P₁)) Set.univ` 形 (tilted-measure normalization) で書くかで下流補題が変わる。**`chernoffTilt` 形を main、tilted 形は equiv 補題で繋ぐ** のが推奨。Mathlib `tilted_apply'` を経由した時の `ENNReal.ofReal` 反転に注意 (CsiszarProjection でも同様の経路を踏んでいる)。
2. λ ∈ [0,1] の閉区間 vs 開区間: 端点処理を分けるか、`rpow_zero/rpow_one` で degenerate 化するか。Mathlib `HolderConjugate` は `1 < p` を要求するので、端点は別 case (但し chernoffInfo 達成点は内部で取る公算大、`logZ` 凸性 + 端点で `logZ = 0` から)。

### 自作 2: `chernoffInfo_attained` (`min` 達成性 + `chernoffInfo ≥ 0`)

**推奨実装**:

```lean
/-- `logZ(λ)` is convex on `[0,1]`. -/
lemma convexOn_chernoffLogZ (P₁ P₂ : Measure α)
    (hP₁ : ∀ x, 0 < P₁.real {x}) (hP₂ : ∀ x, 0 < P₂.real {x}) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (Real.log ∘ chernoffZ P₁ P₂) := by
  sorry

/-- `chernoffInfo` is attained at some `λ* ∈ [0,1]`. -/
theorem chernoffInfo_attained (P₁ P₂ : Measure α)
    (hP₁ : ∀ x, 0 < P₁.real {x}) (hP₂ : ∀ x, 0 < P₂.real {x}) :
    ∃ lam ∈ Set.Icc (0:ℝ) 1,
      chernoffInfo P₁ P₂ = -(Real.log (chernoffZ P₁ P₂ lam)) :=
  -- IsCompact.exists_isMinOn (isCompact_Icc) + continuous_logZ
  sorry
```

**工数感**: 凸性の証明 (Hölder + `convexOn_exp` + `log` concavity の組み合わせ) ~80 行 + 達成性 ~30 行 = **~110 行**。

**落とし穴**:
- `logZ(λ) = log ∑_x P₁^λ P₂^{1-λ}` の凸性は **Hölder 不等式** から従う (`Z(αλ₁ + βλ₂) ≤ Z(λ₁)^α · Z(λ₂)^β`、α + β = 1) → 対数で `log Z(αλ₁ + βλ₂) ≤ α log Z(λ₁) + β log Z(λ₂)`。Mathlib `Real.inner_le_Lp_mul_Lq_of_nonneg` の **`HolderConjugate (1/α) (1/β)`** 構築で end-point ε > 0 開区間 に閉じ込め、両端は連続拡張で。

### 自作 3: Sanov-LDP → Chernoff lower bound bridge

**推奨実装**:

```lean
/-- For each `λ ∈ [0,1]`, the tilted measure `T_λ` is in the type-class limit of
the "matching error set" for Bayes test, giving the Chernoff lower bound. -/
theorem chernoff_lower_bound (P₁ P₂ : Measure α) (hP₁ : ∀ x, 0 < P₁.real {x})
    (hP₂ : ∀ x, 0 < P₂.real {x}) :
    Tendsto (fun n => -((1:ℝ)/n) * Real.log (bayesErrorMin P₁ P₂ n))
      atTop (atTop ⊓ 𝓟 (Set.Iic (chernoffInfo P₁ P₂))) :=  -- limsup ≤ chernoffInfo
  -- Use sanov_ldp_equality for each tilt λ, combine with the matching-set argument
  -- (Cover-Thomas 11.9.1)
  sorry
```

**戦略**: each fixed `λ` で `T_λ` 周りの type class neighborhood を `E_n^λ ⊆ TypeCountIndex α n` として組み、
`sanov_ldp_equality` を `P := T_λ` で適用 → `(1/n) log Q^n(⋃_E_n^λ) → -klDivPmf T_λ P_i` の Tendsto を取得 →
"matching" 引数で chernoff exponent に到達。

**工数感**: ~120-150 行 (per-tilt Sanov 起動 ~50 + matching-set 議論 ~70 + asymptotic 結合 ~30)。

**落とし穴**:
- `sanov_ldp_equality` の input `h_minimizer : ∀ n c ∈ E n, klDivSumForm_ofVec P (Q.real ∘ singleton) ≤ klDivIndex c n Q` を、each `λ` での `T_λ` minimizer 性として準備する必要がある。**KL の strict convexity から `T_λ` が unique minimizer であることは Csiszar projection plumbing で既に保証** (`csiszar_projection_unique`, `CsiszarProjection.lean:186`)。これを `(c/n) ∈ E_n^λ` への翻訳で繋ぐ。

### 自作 4: Hoeffding `hoeffdingE2` + `tradeoff_lemma`

**推奨実装**:

```lean
/-- Hoeffding tradeoff exponent. -/
noncomputable def hoeffdingE2 (P₁ P₂ : α → ℝ) (alpha : ℝ) : ℝ :=
  sInf (klDivPmf · P₂ '' {Q ∈ stdSimplex ℝ α | klDivPmf Q P₁ ≤ alpha})

/-- `hoeffdingE2` is attained (Csiszar projection on the sublevel set). -/
theorem hoeffdingE2_attained (P₁ P₂ : α → ℝ)
    (hP₁ : ∀ a, 0 < P₁ a) (hP₂ : ∀ a, 0 < P₂ a)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) :
    ∃ Qstar ∈ ({Q ∈ stdSimplex ℝ α | klDivPmf Q P₁ ≤ alpha}),
      hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂ := by
  -- The set is closed (preimage of closed Iic under continuous klDivPmf · P₁)
  -- and nonempty (P₁ itself: klDivPmf P₁ P₁ = 0 ≤ alpha).
  -- Use csiszar_projection_exists with the modified objective klDivPmf · P₂.
  sorry

/-- Hoeffding tradeoff. -/
theorem hoeffding_tradeoff (P₁ P₂ : α → ℝ) (hP₁ : ∀ a, 0 < P₁ a) (hP₂ : ∀ a, 0 < P₂ a)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_le : alpha ≤ klDivPmf P₁ P₂) :
    Tendsto (fun n => -((1:ℝ)/n) * Real.log (steinTypeII_at_level (P₁) (P₂) n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha)) :=
  sorry
```

**工数感**: 達成性 ~60 行 + 連続性 ~30 行 + tradeoff Tendsto ~80 行 = **~170 行**。

**落とし穴**:
- `klDivPmf · P₁` の連続性 (`continuous_klDivPmf_left`, `CsiszarProjection.lean:71`) は **`hQ_pos : ∀ a, 0 < Q a`** を要求 (我々の P₁ の full support 仮定で OK)
- 連続性から `{Q | klDivPmf Q P₁ ≤ alpha}` は閉集合になるが、**`continuous_klDivPmf_left` は P を変数として `Q` を fixed second arg として連続性**。我々が必要なのは「Q を変数として `klDivPmf Q P₁` が連続」なので、**`continuous_klDivPmf_left` の引数順を逆にした版** (or それ自身) を使う。CsiszarProjection.lean の `continuous_klDivPmf_left (Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) : Continuous (fun P : α → ℝ => klDivPmf P Q)` の `(P, Q)` の意味付けに注意: ここでは「Q が reference, P が変数」なので **そのまま使える** (我々の `P := Q (variable)`, `Q := P₁ (reference)`)。
- Csiszar projection の reference は `Q := P₂` で取り直して `minimize klDivPmf Q P₂`、制約集合は `K := {Q ∈ stdSimplex | klDivPmf Q P₁ ≤ alpha}`。一発適用ではないので **slight modification of `csiszar_projection_exists`** が必要 (constraint set が `klDivPmf · P₁ ≤ alpha` で定義される閉凸集合になっていることを示す compose)。

### 自作 5 (補助): `klDivPmf_self_eq_zero` (Hoeffding 制約集合の nonempty 用)

```lean
/-- `klDivPmf P P = 0` when P is a probability pmf with full support. -/
lemma klDivPmf_self_eq_zero (P : α → ℝ) (hP : ∀ a, 0 < P a) :
    klDivPmf P P = 0 := by
  unfold klDivPmf
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [div_self (hP a).ne']
  rw [klFun_one]
  ring
```

**工数感**: 5 行 (直接 `klFun_one = 0` から)。

---

## 撤退ラインへの距離

roadmap 既存撤退ラインは `docs/textbook-roadmap.md` §T1-B (line 133) の規模 ~400-600 行と
§T1-D (line 150) の規模 ~200-300 行 (合算 600-900 行)。

### 判定

- **発動しない** (現時点): Mathlib `Measure.tilted` + `LogLikelihoodRatio` (tilted-llr identities) 完備 ⇒ Chernoff exponent の per-tilt 計算は **自前再構築ゼロ**
- Sanov LDP equality (`Common2026/Shannon/SanovLDPEquality.lean:1243`) が Chernoff lower bound に **直接** 流用可能
- Csiszar projection (`Common2026/Shannon/CsiszarProjection.lean`) が Hoeffding `min` 達成性に **直接** 流用可能
- 規模見積もり: **自作 1~5 合計 ~515-565 行** + skeleton/imports/comment **+ 100-150 行** = **~615-715 行**、roadmap 中央予測 (700) と整合

### 新規撤退ライン (提案)

以下を新規撤退ラインとして追加:

1. **Mathlib `Measure.tilted` を `Measure.pi (fun _ : Fin n => P)` 上で **直接** 持ち上げる plumbing が 200 行を超えた場合**
   → 縮退案: **n-IID Chernoff statement を `klDivPmf` 自前形に閉じ込め**、Mathlib `tilted` は per-letter まで使い (`P₁.tilted f`)、n-letter `P₁^n` への持ち上げは `klDiv_pi_eq_n_smul` (`Stein.lean:713`) で済ます。
2. **Chernoff `log Z(λ)` の凸性証明が 100 行を超えた場合 (Hölder のうまい持ち込みに失敗)**
   → 縮退案: `(1-λ) D(T_λ ‖ P₁) + λ D(T_λ ‖ P₂) = -log Z(λ)` 形 (Mathlib `integral_llr_tilted_left/right` から自動展開) を **definition** として採用し、凸性は KL の (P_λ vs P) 形 jointly convex 補題 (Mathlib にあれば) から導く。
3. **Hoeffding `tradeoff_lemma` の Type I 側 achievability で `stein_achievability` をそのまま転用しようとして DPI 等の hidden 仮定で詰まる場合 (1 週間以上)**
   → 縮退案: T1-D を **「`hoeffdingE2` 自身の variational expression のみ」** にスコープ縮退、achievability の n-IID Tendsto は T1-B Chernoff 完了後の派生補題に押し出し別 plan に。

---

## 着手 skeleton

`Common2026/Shannon/Chernoff.lean` (T1-B + T1-D 一括):

```lean
import Common2026.Shannon.Stein
import Common2026.Shannon.StrongStein
import Common2026.Shannon.SanovLDPEquality
import Common2026.Shannon.CsiszarProjection
import Common2026.Shannon.KLDivContinuous
import Common2026.InformationTheory.Asymptotic
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Analysis.MeanInequalities         -- Real.inner_le_Lp_mul_Lq_of_nonneg
import Mathlib.Analysis.Convex.SpecificFunctions.Basic  -- convexOn_exp, convexOn_rpow

/-!
# T1-B Chernoff Information + T1-D Hoeffding Tradeoff (一括)

Cover-Thomas Theorem 11.9.1 (Chernoff) + Theorem 11.7.3-style (Hoeffding tradeoff).

## 主定理

* `chernoffInfo P₁ P₂` — Chernoff information = `-min_λ log ∑ P₁^λ P₂^{1-λ}`
* `chernoff_lemma` — Bayesian error の指数収束: `-((1/n) log P_e^(n)) → chernoffInfo`
* `hoeffdingE2 P₁ P₂ α` — Type I/II tradeoff exponent
* `hoeffding_tradeoff` — `hoeffdingE2` が n-IID 設定で達成される

## 設計 (mathlib-shape driven)

* Chernoff mediator T_λ は Mathlib `Measure.tilted P₁ (λ • llrPmf P₂ P₁)` で取る
* `integral_llr_tilted_left/right` で `D(T_λ ‖ P_i)` を **closed-form** に展開
* Sanov LDP (`sanov_ldp_equality`) を per-tilt に呼んで Chernoff lower bound
* Csiszar projection (`csiszar_projection_exists`) で Hoeffding `min` 達成性
-/

namespace InformationTheory.Shannon.Chernoff

open MeasureTheory ProbabilityTheory InformationTheory Real Filter
open InformationTheory.Shannon
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Phase A — Chernoff exponent definitions -/

/-- log-tilt vector `f_λ(x) := log( P₁(x)^λ · P₂(x)^{1-λ} / P₁(x) ) = λ · llrPmf P₂ P₁ x`. -/
noncomputable def chernoffLogTilt (P₁ P₂ : Measure α) (lam : ℝ) : α → ℝ :=
  fun x => lam * (llrPmf P₂ P₁ x)

/-- The Chernoff mediator T_λ. Probability measure on α with density
`(P₂/P₁)^λ / Z(λ)` w.r.t. P₁; equivalently, T_λ(x) ∝ P₁(x)^{1-λ} · P₂(x)^λ. -/
noncomputable def chernoffMediator (P₁ P₂ : Measure α) (lam : ℝ) : Measure α :=
  P₁.tilted (chernoffLogTilt P₁ P₂ lam)

/-- Chernoff partition function. -/
noncomputable def chernoffZ (P₁ P₂ : Measure α) (lam : ℝ) : ℝ :=
  ∑ x : α, (P₁.real {x}) ^ (1 - lam) * (P₂.real {x}) ^ lam

/-- Chernoff information. -/
noncomputable def chernoffInfo (P₁ P₂ : Measure α) : ℝ :=
  -(sInf ((Real.log ∘ chernoffZ P₁ P₂) '' Set.Icc (0:ℝ) 1))

/-! ## Phase B — Hoeffding tradeoff -/

/-- Hoeffding tradeoff exponent. -/
noncomputable def hoeffdingE2 (P₁ P₂ : α → ℝ) (alpha : ℝ) : ℝ :=
  sInf (klDivPmf · P₂ '' {Q | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha})

/-! ## Phase C — main theorems -/

/-- **Chernoff lemma** (Cover-Thomas Theorem 11.9.1).
Bayesian error decays exponentially with rate equal to Chernoff information. -/
theorem chernoff_lemma
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P₁ P₂ : Measure α) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (hP₁_pos : ∀ x : α, 0 < P₁.real {x}) (hP₂_pos : ∀ x : α, 0 < P₂.real {x})
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    (hMap : μ.map (Xs 0) = P₁)
    (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P₁)) :
    -- Bayes-error exponent equals Chernoff info.
    Filter.Tendsto
      (fun n : ℕ => -((1:ℝ)/n) * Real.log (sorry : ℝ))  -- bayesErrorMin to be defined
      Filter.atTop
      (𝓝 (chernoffInfo P₁ P₂)) := by
  sorry

/-- **Hoeffding tradeoff lemma**: optimal Type II exponent at Type I level `α`. -/
theorem hoeffding_tradeoff
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : (∑ a, P₁ a) = 1) (hP₂_sum : (∑ a, P₂ a) = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_le : alpha ≤ klDivPmf P₁ P₂) :
    Filter.Tendsto
      (fun n : ℕ => -((1:ℝ)/n) * Real.log (sorry : ℝ))  -- steinTypeII_at_level to be defined
      Filter.atTop
      (𝓝 (hoeffdingE2 P₁ P₂ alpha)) := by
  sorry

end InformationTheory.Shannon.Chernoff
```

(20-30 行のはずが定義 + 主定理 2 つ ⇒ 〜80 行スケルトンになる。実装 plan の Phase 構造に合わせて
1 file or `Chernoff.lean` + `HoeffdingTradeoff.lean` の 2 ファイル分割は plan 担当が決める)

---

## 「Phase X で使う API のうち N% が Mathlib に既存」(ratio)

分母 (T1-B + T1-D 主証明 path で実際に使う API): 約 35 項目
- Mathlib Tilted/LLR family: 9 項目 (A 群 + B 群)
- Mathlib KL/KLFun family: 7 項目 (C 群)
- Mathlib rpow/log/Hölder/convex: 10 項目 (E + F + G 群)
- Common2026 Stein/Sanov/Csiszar plumbing: 9 項目 (D 群 hot path)

分子 (既存): 35 項目
- 全項目が既存 (Mathlib + Common2026)

→ **既存率 100%** (実体ベース)。Common2026 Stein/Sanov plumbing の **再利用率は roadmap 主張の 70-80% と整合**:
- Stein 系: `llrPmf`, `logLikelihoodRatio`, `steinTypicalSet_*`, `steinOptimalBeta`, `klDiv_pi_eq_n_smul` の 5 種を 70-80% 再利用
- Sanov 系: `klDivSumForm`, `klDivIndex`, `sanov_ldp_equality`, `roundedTypeIndex` の 4 種を 60-70% 再利用 (Chernoff/Hoeffding は P を `T_λ`/`Q*` に reset するため per-`λ` 起動)
- Csiszar 系: `klDivPmf`, `csiszar_projection_exists`, `csiszar_pythagoras_inequality` の 3 種を **Hoeffding** で 90% 再利用

ただし **自作 4-5 種 (top-level def + bridge 補題群) で `chernoffInfo`/`hoeffdingE2` を新規 publish するため、生コード行数の意味では「既存 plumbing : 自作 = 5 : 1」程度**。

---

## 主要発見 (危険な点)

### 危険 1: `Mathlib.MeasureTheory.Measure.Tilted` の `[SFinite μ]` requirement (verbatim)

`tilted_apply` (`Tilted.lean:105`) は `[SFinite μ]` を要求。我々の `μ := P₁` は `IsProbabilityMeasure ⇒ IsFiniteMeasure ⇒ SFinite` で自動だが、**`Measure.pi (fun _ : Fin n => P₁)` の SFinite を確認**する必要がある (Stein.lean では既に通している路線、追加対応は不要だが「`SFinite (Measure.pi ...)` の自動 derive が落ちる」と LSP が泣く可能性あり)。

### 危険 2: `integral_llr_tilted_left` の `[IsProbabilityMeasure μ]` (verbatim, LogLikelihoodRatio.lean:202)

主定理で `μ := P₁` (我々は IsProbabilityMeasure を持っている) なら通るが、**もし途中で `Measure.pi (fun _ => P₁)^n` を tilt したくなる**と n-IID の prob measure 化 (Mathlib `IsProbabilityMeasure (Measure.pi ...)`) の derivation を補助で書く必要がある (1-2 行で済む見込みだが、忘れがち)。

### 危険 3: Mathlib `HolderConjugate` の **両端開** (`1 < p`)

Chernoff exponent の Hölder 帰着で `HolderConjugate (1/λ) (1/(1-λ))` を構築するが、**λ = 0 または λ = 1 では `1/λ = ∞` で `HolderConjugate` のインスタンスを作れない** (Mathlib 定義: `1 < p ∧ 1/p + 1/q = 1`)。
→ 対策: λ ∈ Set.Ioo 0 1 で Hölder 起動 + 端点 `rpow_zero` / `rpow_one` で直接 `Z(0) = 1`, `Z(1) = 1` を計算する別 case 分岐。Chernoff exponent `-log Z(0) = -log Z(1) = 0` で `chernoffInfo ≥ 0` の境界。

### 危険 4: `csiszar_projection_exists` の `IsClosed K` 仮定 (CsiszarProjection.lean:172)

Hoeffding `K := {Q ∈ stdSimplex ℝ α | klDivPmf Q P₁ ≤ alpha}` の閉性は **`continuous_klDivPmf_left P₁ ...`** から `IsClosed.preimage` で従うが、**「klDivPmf の引数順」**に注意: CsiszarProjection の `continuous_klDivPmf_left (Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) : Continuous (fun P : α → ℝ => klDivPmf P Q)` は `(P 変数, Q reference)` の意味付け。我々の Hoeffding の `klDivPmf Q P₁` は `(Q 変数, P₁ reference)` なので **そのままマッチ**。

### 危険 5 (発見的): `chernoffMediator` を `Measure.tilted P₁ ...` と `Measure.tilted P₂ ...` のどちらで取るか

- `T_λ := P₁.tilted (lam • llrPmf P₂ P₁)` の場合 ⇒ `T_λ(x) = P₁(x) · exp(lam · (log P₂ - log P₁)) / Z = P₁(x)^{1-λ} P₂(x)^λ / Z`
- `T_λ := P₂.tilted ((1-lam) • llrPmf P₁ P₂)` の場合 ⇒ 同じ結果

**両者は同じ T_λ**だが、`integral_llr_tilted_left` を呼ぶ際の `μ`, `ν`, `f` の取り方が変わる。下流の klDivPmf 展開で **どちらの form を使うとブッチ折れがないか**は実装 phase での試行で確認すべし (現時点では「`P₁.tilted (lam • llrPmf P₂ P₁)`」推奨、`integral_llr_tilted_left` 経由で `klDiv (T_λ ‖ P₁) = lam · klDiv P₂ P₁ - log Z(λ)` 形が出る)。

---

## まとめ

- **Mathlib `Measure.tilted` family + Mathlib `LogLikelihoodRatio.llr_tilted_*` の存在は致命的に大きい**: Chernoff exponent の数学的本質 (tilted distribution + log-partition function の closed-form) が **全部** Mathlib に揃っている
- **Common2026 既存 plumbing 再利用率 70-80% (proof-log 主張)** は **実態は分野毎に変動** (Csiszar 90% / Sanov 60-70% / Stein 70-80%) するが、合算では妥当
- **自作量 ~500-600 行 + plumbing ~100-200 行**で **T1-B + T1-D 一括 600-800 行** が現実的
- 撤退ライン現時点 **発動なし**、新規撤退ライン 3 件を追加提案

着手 ready。次は plan 起草。
