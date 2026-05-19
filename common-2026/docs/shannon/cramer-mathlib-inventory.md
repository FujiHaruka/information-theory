# T1-C Cramér's Theorem — Mathlib + Common2026 在庫調査

> Tier 1 roadmap T1-C ([Cover-Thomas Ch.11.4/11.6] Cramér の大偏差定理) のための inventory。
> 入力指示: `docs/shannon/cramer-mathlib-inventory.md` 新規作成、既存基盤 (Sanov LDP equality + Chernoff Tier 0 + IID infrastructure) からどこまで再利用できるかを構造化テーブルで書き出す。

## 一行サマリ

**Mathlib に `cgf` / `mgf` / `Measure.tilted` / `iIndepFun.cgf_sum` / `measure_ge_le_exp_cgf` (= Chernoff bound = Cramér upper bound の直接形) が完備**で、Cramér upper bound (`limsup (1/n) log P[\bar S_n ≥ a] ≤ -Λ^*(a)`) は **30〜80 行で書ける**。一方 **Legendre transform / convex conjugate / LargeDeviationPrinciple は Mathlib に 0 件** で、`Λ^*` は完全自作 (10〜30 行)。lower bound (Cramér achievability) は tilted-measure 法を直接 (Sanov を経由せずに) 書く方が安く、**自前 KL-of-tilted 補題 1 件と LLN を要する** 中規模工数。合計 **300〜400 行** が現実的見積もり (roadmap 下限寄り)。**撤退ラインは発動しない**。`Λ^*` 自前定義は単純な `sSup` で取れ、Sanov を contraction principle で reshape する経路よりも直接 `cgf`/`tilted` 経路の方が短い。

---

## 主定理の最終形 (再掲) + 証明戦略

### 目的の statement (finite-alphabet specialization, Cover-Thomas Theorem 11.4.1)

```lean
/-- **Cramér's theorem (upper bound, finite-alphabet IID)**:
    For IID `X_i : Ω → ℝ` taking values in a finite set, the sample mean's
    upper tail decays exponentially with rate at least `Λ^*(a)`. -/
theorem cramer_upper
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_int : ∀ t, Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
    (a : ℝ) (h_a : 0 < legendre (cgf (X 0) μ) a) :
    limsup (fun n : ℕ =>
      (1 / (n : ℝ)) * Real.log
        (μ.real {ω | (a : ℝ) ≤ (∑ i ∈ Finset.range n, X i ω) / n})) atTop
      ≤ -legendre (cgf (X 0) μ) a
```

ここで `legendre f a := sSup ((fun λ : ℝ => λ * a - f λ) '' Set.univ)` (Mathlib 不在、自前定義)。

### 証明戦略 (pseudo-Lean, 8 行)

```
-- Upper bound (Cramér 11.4.1):
let Λ := cgf (X 0) μ                              -- Mathlib: Probability.Moments.Basic:125
have h_sum_cgf : cgf (∑ i ∈ range n, X i) μ t
    = ∑ i ∈ range n, cgf (X i) μ t                -- iIndepFun.cgf_sum (file:line below)
  = n * Λ t                                       -- via identDistrib + n-fold sum
have h_chernoff :
    μ.real {ω | n*a ≤ ∑ i, X i ω}
      ≤ Real.exp (-t * (n*a) + cgf (∑ i, X i) μ t)  -- measure_ge_le_exp_cgf
  = Real.exp (-n * (t*a - Λ t))                    -- 上 2 行合成
-- take log, divide by n, take limsup, take sup over t ≥ 0
exact limsup_le_iff.mpr fun ε hε => ⟨..., ...⟩
```

### Lower bound (Cramér achievability) — 別 theorem として publish

```lean
theorem cramer_lower
    ... (a : ℝ) (h_a_int : a ∈ interior {... reachable by tilted ...}) :
    -legendre (cgf (X 0) μ) a
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            (μ.real {ω | (a : ℝ) ≤ (∑ i ∈ Finset.range n, X i ω) / n})) atTop
```

戦略: tilted measure `μ_λ := μ.tilted (λ * X 0 ·)` で `X 0` の平均は `deriv Λ λ`。`λ` を `deriv Λ λ = a` で選ぶと tilted の下で LLN により `\bar S_n → a` (Mathlib `ProbabilityTheory.tendsto_average_of_iid` or 等価系) で `μ_λ([n*a ≤ ∑ X]) → 1`。change-of-measure (Radon-Nikodym from `Measure.tilted`) で `μ` 側に戻すと `≥ exp(-n * (λ*a - Λ λ))` を得る。`λ*a - Λ λ = legendre Λ a` (最適化条件)。

---

## API 在庫テーブル

### A. **CGF / MGF 系 (Mathlib `Probability.Moments.Basic`)** — Cramér upper bound の核

| 補題 / 定義 | file:line | Full signature (verbatim) | Phase での扱い |
|---|---|---|---|
| **`mgf` 定義** | `Mathlib/Probability/Moments/Basic.lean:121` | `def mgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ := μ[fun ω => exp (t * X ω)]` | MGF 定義。`X : Ω → ℝ` のみ (finite-alphabet `α` を経由しない、直接 `Ω` 上の random variable) |
| **`cgf` 定義** | `Mathlib/Probability/Moments/Basic.lean:125` | `def cgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ := log (mgf X μ t)` | **`Λ(λ) := log E[exp(λ X)]` そのもの**。Cramér rate function の素材 |
| `mgf_nonneg` | `Basic.lean:180` | `theorem mgf_nonneg : 0 ≤ mgf X μ t` | (variable section) — 前提無し |
| `mgf_pos` | `Basic.lean:201` | `theorem mgf_pos [IsProbabilityMeasure μ] (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) : 0 < mgf X μ t` | 確率測度 + integrability 前提 |
| `mgf_zero` | `Basic.lean:165` | `theorem mgf_zero [IsProbabilityMeasure μ] : mgf X μ 0 = 1` | |
| `cgf_zero` | `Basic.lean:171` | `theorem cgf_zero [IsZeroOrProbabilityMeasure μ] : cgf X μ 0 = 0` (`@[simp]`) | `Λ(0) = 0` |
| `exp_cgf` | `Basic.lean:211` | `lemma exp_cgf [hμ : NeZero μ] (hX : Integrable (fun ω ↦ exp (t * X ω)) μ) : exp (cgf X μ t) = mgf X μ t` | log↔exp 往復 |
| `mgf_id_map` | `Basic.lean:219` | `lemma mgf_id_map (hX : AEMeasurable X μ) : mgf id (μ.map X) = mgf X μ` | finite-alphabet 経由でも書けることの bridge |
| `mgf_congr_identDistrib` | `Basic.lean:227` | `lemma mgf_congr_identDistrib {Ω' ...} {Y : Ω' → ℝ} (h : IdentDistrib X Y μ μ') : mgf X μ = mgf Y μ'` | IID で全 `i` の MGF が等しい (h_ident 経由) |

### B. **CGF / MGF 加法性 — IID 和** (Mathlib `Probability.Moments.Basic` IndepFun section)

| 補題 | file:line | Full signature (verbatim) | Phase での扱い |
|---|---|---|---|
| **`iIndepFun.cgf_sum`** | `Basic.lean:393` | `theorem iIndepFun.cgf_sum {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i)) {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) : cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, cgf (X i) μ t` | **Cramér 主役**: `cgf(∑ X_i) = ∑ cgf(X_i) = n · Λ(t)` (`h_ident` 合成) |
| `iIndepFun.cgf_sum₀` | `Basic.lean:383` | `iIndepFun X μ → (∀ i, AEMeasurable (X i) μ) → ... → cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, cgf (X i) μ t` | aemeasurable 版 |
| `iIndepFun.mgf_sum` | `Basic.lean:378` | `iIndepFun X μ → (∀ i, Measurable (X i)) → mgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, mgf (X i) μ t` | product 形 (cgf 経由で sum 形に出来る) |
| `mgf_sum_of_identDistrib` | `Basic.lean:417` | `{X : ι → Ω → ℝ} {s : Finset ι} {j : ι} (h_meas : ∀ i, Measurable (X i)) (h_indep : iIndepFun X μ) (hident : ∀ i ∈ s, ∀ j ∈ s, IdentDistrib (X i) (X j) μ μ) (hj : j ∈ s) (t : ℝ) : mgf (∑ i ∈ s, X i) μ t = mgf (X j) μ t ^ #s` | **`mgf(n-sum) = mgf(X_0)^n` 直接形**。Cramér 5 行短縮可能 |
| `IndepFun.cgf_add` | `Basic.lean:308` | `(h_indep : X ⟂ᵢ[μ] Y) (h_int_X : Integrable (fun ω => exp (t * X ω)) μ) (h_int_Y : Integrable (fun ω => exp (t * Y ω)) μ) : cgf (X + Y) μ t = cgf X μ t + cgf Y μ t` | 2 変数版 (帰納的に `iIndepFun.cgf_sum` が依存) |

⚠ **前提注意 (`iIndepFun.cgf_sum`)**:
- `[IsProbabilityMeasure μ]` は **明示的には書かれていない** が、`iIndepFun` の前提が暗黙に `IsProbabilityMeasure μ` を含む (証明内部で `h_indep.isProbabilityMeasure` を活用、`Basic.lean:366`)。
- `Integrable (fun ω => exp (t * X i ω)) μ` は **各 `i` で必要**。IID `IdentDistrib` 仮定下でも `h_int 0` から `h_int i` への移行は自前で書く必要 (簡単に `(h_ident i).integrable_iff` で出来る、`Probability.IdentDistrib`)。

### C. **Chernoff bound (= Cramér upper bound の単項版)** (Mathlib `Probability.Moments.Basic` Chernoff section)

| 補題 | file:line | Full signature (verbatim) | Phase での扱い |
|---|---|---|---|
| **`measure_ge_le_exp_cgf`** | `Basic.lean:461` | `theorem measure_ge_le_exp_cgf [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t) (h_int : Integrable (fun ω => exp (t * X ω)) μ) : μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε + cgf X μ t)` | **Cramér upper bound そのもの** (sample mean を `X := ∑ X_i` に代入、`ε := n * a`、結果を `(1/n) log` 取って `t` で sup) |
| `measure_le_le_exp_cgf` | `Basic.lean:469` | `[IsFiniteMeasure μ] (ε : ℝ) (ht : t ≤ 0) (h_int : Integrable (fun ω => exp (t * X ω)) μ) : μ.real {ω | X ω ≤ ε} ≤ exp (-t * ε + cgf X μ t)` | 下尾用 (Cramér の `a < E[X]` 側) |
| `measure_ge_le_exp_mul_mgf` | `Basic.lean:429` | 同型 mgf 形 (`exp (-t * ε) * mgf X μ t`) | 上の素 |
| `measure_le_le_exp_mul_mgf` | `Basic.lean:451` | 下尾 mgf 形 | |

⚠ **前提注意**: `[IsFiniteMeasure μ]` 必要 (確率測度なら自動)。`ht : 0 ≤ t` は upper tail 用 (`t < 0` で書くと Markov の向きが逆)。

### D. **MGF analyticity / cgf 微分** (Mathlib `Probability.Moments.MGFAnalytic`)

| 補題 | file:line | Full signature (verbatim) | Phase での扱い |
|---|---|---|---|
| `analyticOnNhd_cgf` | `Mathlib/Probability/Moments/MGFAnalytic.lean:176` | `lemma analyticOnNhd_cgf : AnalyticOnNhd ℝ (cgf X μ) (interior (integrableExpSet X μ))` | `Λ` が解析的 ⇒ 連続 ⇒ Legendre `sSup` の達成性 |
| `deriv_cgf` | `MGFAnalytic.lean:188` | `lemma deriv_cgf (h : v ∈ interior (integrableExpSet X μ)) : deriv (cgf X μ) v = μ[fun ω ↦ X ω * exp (v * X ω)] / mgf X μ v` | `Λ'(λ)` 評価 (lower bound の tilted-mean に必要) |
| `deriv_cgf_zero` | `MGFAnalytic.lean:200` | `lemma deriv_cgf_zero (h : 0 ∈ interior (integrableExpSet X μ)) : deriv (cgf X μ) 0 = μ[X] / μ.real Set.univ` | `Λ'(0) = E[X]` (上下端点判定) |
| `iteratedDeriv_two_cgf_eq_integral` | `MGFAnalytic.lean:239` | `lemma iteratedDeriv_two_cgf_eq_integral (h : v ∈ interior (integrableExpSet X μ)) : iteratedDeriv 2 (cgf X μ) v = μ[fun ω ↦ (X ω - deriv (cgf X μ) v) ^ 2 * exp (v * X ω)] / mgf X μ v` | `Λ''(λ) = Var_{μ_λ}[X] ≥ 0` ⇒ `Λ` 凸 ⇒ `Λ^*` 上 lsc |
| `continuousOn_mgf` | `MGFAnalytic.lean:137` | `lemma continuousOn_mgf : ContinuousOn (mgf X μ) (interior (integrableExpSet X μ))` | bounded support なら全 ℝ で integrable ⇒ 全 ℝ で連続 |

### E. **`integrableExpSet`** (MGF 定義域、Mathlib `Probability.Moments.IntegrableExpMul`)

| 補題 | file:line | Full signature (verbatim) | Phase での扱い |
|---|---|---|---|
| **`integrableExpSet` 定義** | `Mathlib/Probability/Moments/IntegrableExpMul.lean:113` | `def integrableExpSet (X : Ω → ℝ) (μ : Measure Ω) : Set ℝ := {t | Integrable (fun ω ↦ exp (t * X ω)) μ}` | MGF が well-defined な `t` の範囲 |
| `convex_integrableExpSet` | `IntegrableExpMul.lean:120` | `lemma convex_integrableExpSet : Convex ℝ (integrableExpSet X μ)` | interval 性 (Cramér の Legendre 双対が well-defined な領域) |
| `integrable_of_mem_integrableExpSet` | `IntegrableExpMul.lean:116` | `lemma integrable_of_mem_integrableExpSet (h : t ∈ integrableExpSet X μ) : Integrable (fun ω ↦ exp (t * X ω)) μ` | `h_int` を作る helper |

⚠ **finite-alphabet `X : α → ℝ` の場合**: `α` finite ⇒ `Ω = α^ℕ` 上 `X i := f ∘ proj i` で `f : α → ℝ` 有界 ⇒ `exp (t * X i ω)` も有界 ⇒ **全 `t : ℝ` で integrable** (`integrable_of_bounded`)。すなわち `integrableExpSet X μ = univ` で `interior = univ` も自動。これは Cramér finite-alphabet specialization では **integrability 仮定をスッキリ落とせる**ことを意味する。

### F. **`Measure.tilted` (指数 tilting)** (Mathlib `MeasureTheory.Measure.Tilted` + `Probability.Moments.Tilted`)

| 補題 | file:line | Full signature (verbatim) | Phase での扱い |
|---|---|---|---|
| **`Measure.tilted` 定義** | `Mathlib/MeasureTheory/Measure/Tilted.lean:42` | `noncomputable def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α := μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))` | lower bound 用 reference measure |
| `isProbabilityMeasure_tilted` | `MeasureTheory/Measure/Tilted.lean:126` | `lemma isProbabilityMeasure_tilted [NeZero μ] (hf : Integrable (fun x ↦ exp (f x)) μ) : IsProbabilityMeasure (μ.tilted f)` | tilted は確率測度 |
| `tilted_absolutelyContinuous` | `MeasureTheory/Measure/Tilted.lean:280` | `lemma tilted_absolutelyContinuous (μ : Measure α) (f : α → ℝ) : μ.tilted f ≪ μ` | change-of-measure 用 |
| `absolutelyContinuous_tilted` | `MeasureTheory/Measure/Tilted.lean:283` | `lemma absolutelyContinuous_tilted (hf : Integrable (fun x ↦ exp (f x)) μ) : μ ≪ μ.tilted f` | 両方向 AC |
| `rnDeriv_tilted_left_self` | `MeasureTheory/Measure/Tilted.lean:360` | `lemma rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ) : (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ)` | RN derivative 形 |
| `log_rnDeriv_tilted_left_self` | `MeasureTheory/Measure/Tilted.lean:366` | `lemma log_rnDeriv_tilted_left_self [SigmaFinite μ] (hf : Integrable (fun x ↦ exp (f x)) μ) : ...` | log-RN 形 (KL 計算に必要) |
| `tilted_mul_apply_cgf` | `Mathlib/Probability/Moments/Tilted.lean:59` | `lemma tilted_mul_apply_cgf [SFinite μ] (s : Set Ω) (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) : μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ` | tilted 測度の `s`-mass を cgf で書く |
| `integral_tilted_mul_self` | `Probability/Moments/Tilted.lean:132` | `lemma integral_tilted_mul_self (ht : t ∈ interior (integrableExpSet X μ)) : (μ.tilted (t * X ·))[X] = deriv (cgf X μ) t` | **tilted 平均 = `Λ'(t)`**。lower bound の根幹 (`λ^*` 選び方) |
| `variance_tilted_mul` | `Probability/Moments/Tilted.lean:159` | `lemma variance_tilted_mul (ht : t ∈ interior (integrableExpSet X μ)) : Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t` | tilted 分散 = `Λ''(t)` |

⚠ **重要な「不在」**: `Mathlib` には **`klDiv (μ.tilted (λ * X ·)) μ = λ * (μ.tilted ...)[X] - cgf X μ λ` という KL-of-tilted 恒等式が存在しない**。これは Cramér lower bound (tilted 経路) で必須なので **自前 10〜30 行**。素材は揃っている (`log_rnDeriv_tilted_left_self` + `klDiv` の RN-form 定義)。loogle 確認: `Found 0 declarations mentioning MeasureTheory.Measure.tilted and InformationTheory.klDiv`。

### G. **IID infrastructure (Mathlib + Common2026)**

| 補題 | file:line | Full signature (verbatim) | Phase での扱い |
|---|---|---|---|
| **`iIndepFun_infinitePi`** | `Mathlib/Probability/Independence/InfinitePi.lean:103` | `lemma iIndepFun_infinitePi {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)} {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)] {X : (i : ι) → Ω i → 𝓧 i} (mX : ∀ i, Measurable (X i)) : iIndepFun (fun i ω ↦ X i (ω i)) (infinitePi P)` | IID measure 構築 |
| `Measure.infinitePi` | `Mathlib/Probability/ProductMeasure.lean:?` | `(P : (i : ι) → Measure (Ω i)) → Measure (∀ i, Ω i)` | n-IID の自然な ambient |
| `Measure.infinitePi_map_eval` | (同上) | `(i : ι) → (Measure.infinitePi P).map (fun ω => ω i) = P i` | 各座標の周辺は `P i` |
| **`iidAmbientMeasure`** | `Common2026/Shannon/IIDProductInput.lean:48` | `noncomputable def iidAmbientMeasure (p : Measure α) (W : Channel α β) : Measure (ℕ → α × β) := Measure.infinitePi (fun _ : ℕ => jointDistribution p W)` | **既存 IID infrastructure** (channel coding 用、Cramér では Channel を identity に specialize) |
| `iidAmbient_iIndepFun_iidXs` | `IIDProductInput.lean:169` | `iIndepFun (fun i : ℕ => iidXs i) (iidAmbientMeasure p W)` | `Xs` の IID |
| `iidAmbient_identDistrib_iidXs` | `IIDProductInput.lean:136` | `IdentDistrib (iidXs i) (iidXs 0) (iidAmbientMeasure p W) (iidAmbientMeasure p W)` | 同分布 |

⚠ **Cramér 専用 ambient の必要性**: 既存 `iidAmbientMeasure` は `α × β` (channel I/O ペア) 用。Cramér では `Y` チャンネル出力不要なので、**より軽い ambient `Measure.infinitePi (fun _ : ℕ => p)` を直接使う**べき (~10 行 plumbing)。`jointDistribution p (Channel.constLaw ν)` で潰す手もあるが冗長。

### H. **Sanov LDP equality (既存 Common2026)** — Cramér への bridge 経路

| 補題 | file:line | Full signature (verbatim) | Phase での扱い |
|---|---|---|---|
| **`sanov_ldp_equality`** | `Common2026/Shannon/SanovLDPEquality.lean:1243` | `theorem sanov_ldp_equality (Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a : α, 0 < Q.real {a}) (P : α → ℝ) (hP_prob : (∑ a, P a) = 1) (hP_full : ∀ a, 0 < P a) (E : ∀ n, Finset (TypeCountIndex α n)) (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n) (h_minimizer : ∀ n, ∀ c ∈ E n, klDivSumForm_ofVec P (fun a => Q.real {a}) ≤ klDivIndex (fun a => (c a : ℕ)) n Q) : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (((Measure.pi (fun _ : Fin n => Q)) (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal)) atTop (𝓝 (-(klDivSumForm_ofVec P (fun a => Q.real {a}))))` | **Sanov LDP**: 経験分布の **集合形** `Q^n(⋃ T_c)` の指数。Cramér の sample-mean 形ではない |
| `sanov_ldp_lower_bound_pointwise` | `SanovLDPEquality.lean:1071` | lower (liminf ≥ -D) | 分離して使えるか確認要 |
| `sanov_ldp_upper_bound` | `Common2026/Shannon/SanovLDP.lean:471` | `theorem sanov_ldp_upper_bound (Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a : α, 0 < Q.real {a}) (E : ∀ n, Finset (TypeCountIndex α n)) (D : ℝ) (hD : ∀ n, ∀ c ∈ E n, D ≤ klDivIndex (fun a => (c a : ℕ)) n Q) {ε : ℝ} (hε : 0 < ε) : ∃ N, ∀ n ≥ N, 0 < n → 0 < ((Measure.pi (fun _ : Fin n => Q)) (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal → (1 / (n : ℝ)) * Real.log (...) ≤ -D + ε` | Sanov upper |
| `klDivSumForm_ofVec` | `Common2026/Shannon/KLDivContinuous.lean:31` | `noncomputable def klDivSumForm_ofVec (p q : α → ℝ) : ℝ := ∑ a : α, p a * (Real.log (p a) - Real.log (q a))` | finite-alphabet KL |

**Sanov → Cramér bridge の難しさ (重要発見)**:
教科書では Cramér = Sanov の contraction principle (push-forward によるrate function 計算) と説明される。しかし **既存 `sanov_ldp_equality` は集合形** `Q^n(⋃ c ∈ E n, T_c)` で、ここから sample mean 形 `Q^n({x | a ≤ (∑ f(x_i))/n})` への reshape は:
1. `E n := {c | a ≤ ∑ a' * (c a' / n) for f := id}` の取り方を決め (textbook E n は `a` の閉集合 `{p | E_p[f] ≥ a}` の rounded 化)
2. `klDivSumForm_ofVec P (Q.real ∘ singleton)` を `Λ^*(a)` に置換する `inf_{p : E_p[f] ≥ a} KL(p ‖ Q) = Λ^*(a)` の同一視 (Donsker-Varadhan 双対公式) を別補題で書く
の **2 段階の reshape が必要**で、各々 ~80〜150 行。一方 **`cgf` 直接経路 (Chernoff + tilted)** は ~80〜120 行で終わる。**結論: Sanov 経由でなく直接経路を採用** (roadmap 「contraction principle 経由 reshape」は不推奨)。

### I. **Chernoff Tier 0 既存 (Common2026)** — Cramér rate function との関係

| 補題 | file:line | Full signature (verbatim) | Phase での扱い |
|---|---|---|---|
| **`chernoffZSum`** | `Common2026/Shannon/Chernoff.lean:61` | `noncomputable def chernoffZSum (P₁ P₂ : α → ℝ) (lam : ℝ) : ℝ := ∑ a : α, (P₁ a) ^ (1 - lam) * (P₂ a) ^ lam` | **Chernoff partition function `Z(λ)`**。textbook 11.9.1 形 |
| `chernoffInfo` | `Common2026/Shannon/Chernoff.lean:67` | `noncomputable def chernoffInfo (P₁ P₂ : α → ℝ) : ℝ := -(sInf ((fun lam : ℝ => Real.log (chernoffZSum P₁ P₂ lam)) '' Set.Icc (0:ℝ) 1))` | hypothesis testing 用 (Cramér とは別物だが Legendre 達成性証明の参考にできる) |
| `chernoffZSum_continuous` | `Chernoff.lean:124` | `Continuous (fun lam : ℝ => chernoffZSum P₁ P₂ lam)` | Legendre `sSup` 達成性のテンプレ |
| `chernoffInfo_attained` | `Chernoff.lean:161` | `∃ lam ∈ Set.Icc (0:ℝ) 1, chernoffInfo = -log Z(lam)` | compact + continuous `IsCompact.exists_sInf_image_eq` |

⚠ **`chernoffZSum` ≠ `mgf`**: textbook `Z(λ) = ∑ P₁^{1-λ} P₂^λ` は **2 つの分布の Chernoff information** の partition function。Cramér の `Λ(λ) = log E_μ[exp(λ X)] = log ∑_a P(a) exp(λ f(a))` (`X = f ∘ id` for finite-alphabet) **とは別物**。流用不可。だが **`chernoffInfo_attained` の `IsCompact.exists_sInf_image_eq` 戦略は `legendre Λ a` の sSup 達成性 (Λ 連続 + コンパクト Icc) でそのまま再利用可能**。

### J. **Legendre transform / Convex conjugate** — Mathlib 在庫

| 名前 | file:line | 状態 | Phase での扱い |
|---|---|---|---|
| `Legendre`, `legendre`, `convexConjugate`, `Fenchel.conjugate` 等 | — | ❌ **Mathlib 完全不在** (loogle: `Legendre` の hit は全て数論 `legendreSym` (二次剰余記号))、`Fenchel`/`ConvexConjugate` は `Found 0 declarations` | **自前定義 ~10 行**: `noncomputable def legendre (Λ : ℝ → ℝ) (a : ℝ) : ℝ := sSup ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)` |
| `LargeDeviationPrinciple`, `RateFunction` | — | ❌ **Mathlib 完全不在** (`rg -nl "LDP\|LargeDeviation\|RateFunction"` for `.lake/packages/mathlib/Mathlib/Probability/`: 0 hits) | LDP の抽象 framework は無いので、Cramér は **生 `limsup`/`liminf` 不等式 + `Tendsto` 形**で書く |
| `Real.sSup_image_*` 系 | (Mathlib) | ✅ | `sSup` 達成性プラミング |
| `IsCompact.exists_sInf_image_eq` | Mathlib | ✅ | `chernoffInfo_attained` で実証 (上記 I) — `legendre` 達成性に同様に使用 |

### K. **LLN — Cramér lower bound 用** (Mathlib `Probability.IdentDistrib` + `Probability.StrongLaw`)

| 補題 | file:line | Full signature (verbatim) | Phase での扱い |
|---|---|---|---|
| `ProbabilityTheory.strong_law_ae` 系 | Mathlib `Probability/StrongLaw.lean` | (要 verify; integrability + IID 前提) | tilted 下で `\bar S_n → E_{μ_λ}[X] = Λ'(λ)` |
| `ProbabilityTheory.tendsto_average_of_iid` 風名前 | — (要 loogle) | | (下記参照) |

**LLN 確認 (要追加調査)**: tilted 経路の lower bound で `μ_{λ^*}( a - ε ≤ \bar S_n ≤ a + ε) → 1` を `λ^*` を `Λ'(λ^*) = a` で取って LLN 適用する箇所が要。Mathlib `Probability/StrongLaw` 系 (strong law of large numbers) は **完備**だが、tilted measure 下で IID を再構築 (`(μ.tilted ...)^∞ ≠ (μ^∞).tilted (∑ ...)` の架橋) が必要で、これは~50 行の plumbing が見込まれる。

簡略代替: lower bound を **弱形 (in-probability LLN, Markov)** で書く ⇒ tilted 下の分散 `Λ''(λ^*)` を Chebyshev で打って `1 - o(1)` を得る。Mathlib `MeasureTheory.measure_le_of_variance_le` 風で可能。

---

## 主要前提条件ボックス (型クラス verbatim)

Cramér の主要 lemma を呼ぶ時の前提を 1 箇所に集約。`[...]` 部分は **verbatim 引用**:

- **`measure_ge_le_exp_cgf`** (Mathlib `Basic.lean:461`):
  - `[IsFiniteMeasure μ]` 要求。確率測度 + 有限なら OK。
  - `(ht : 0 ≤ t)` (upper tail 用)、`(h_int : Integrable (fun ω => exp (t * X ω)) μ)` 必須。
- **`iIndepFun.cgf_sum`** (Mathlib `Basic.lean:393`):
  - **暗黙の `[IsProbabilityMeasure μ]`** (証明内部で `h_indep.isProbabilityMeasure` を活用、`Basic.lean:387`)。
  - `(h_meas : ∀ i, Measurable (X i))` および `{s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ)`。
- **`integral_tilted_mul_self`** (Mathlib `Tilted.lean:132`):
  - `(ht : t ∈ interior (integrableExpSet X μ))` — **`interior` 必須**。境界点では成立しない。finite-alphabet では `integrableExpSet = univ` で `interior = univ` なので問題なし。
- **`Measure.tilted`** (Mathlib `Tilted.lean:42`):
  - `noncomputable def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α` — 型クラス前提なし (`f` integrable でなければ `0` 測度返却)。
- **`isProbabilityMeasure_tilted`** (Mathlib `Tilted.lean:126`):
  - `[NeZero μ]` 要求。確率測度なら OK (`IsProbabilityMeasure.toNeZero` instance あり)。

⚠ **finite-alphabet specialization 経由で前提を一掃**:
教科書 T1-C は IID `X_i` を `Ω → ℝ` で取るが、**`α` finite + `f : α → ℝ` + `X i = f ∘ (proj i)` で書くと**、`X_i` は有界 ⇒ 全 `t` で `exp (t * X_i)` integrable ⇒ `integrableExpSet = univ` ⇒ `interior = univ`。`[IsProbabilityMeasure (μ : Measure (α^ℕ))]` も `Measure.infinitePi` で自動。**Cramér finite-alphabet 形は前提が極めて軽い**。

---

## 自作が必要な要素 (優先度順、推奨実装 + 工数 + 落とし穴)

### 自前 1: `legendre` 定義 + 基本性質 (★最優先)

```lean
noncomputable def legendre (Λ : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)
```

- **規模**: 定義 1 行 + 非負性 (`legendre Λ a ≥ -Λ 0 + 0 = 0` ⇐ `Λ 0 = 0` (`cgf_zero`)) + 連続性 + Legendre 不等式 `lam * a - Λ lam ≤ legendre Λ a`、合計 **~30〜60 行**
- **落とし穴**:
  - `sSup` は `BddAbove` でないと `0` 返却。`Λ` が下に有界でない (`X` が unbounded) と `legendre` が `+∞` になり扱いに困る。**finite-alphabet で `X` 有界 ⇒ `Λ` 全 ℝ で有限 ⇒ `legendre` も Jensen で `≥ 0` 有限**で安全。
  - `legendre` を `ENNReal` で書く誘惑があるが、negative 値も入れたければ `EReal` または `WithBot ℝ`。**今回は `ℝ` 値で finite-alphabet specialization に絞る** (最も軽い)。
  - 達成性 (∃ `λ^*`, `legendre Λ a = λ^* * a - Λ λ^*`) は `Λ` 凸 + 連続 + coercive で取れる (`IsCompact.exists_sSup_image_eq` 風) が **最初の publish では不要**、別補題に分離。

### 自前 2: Cramér rate `cramerRate` (= `legendre cgf`) のラッパ

```lean
noncomputable def cramerRate (X : Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ :=
  legendre (cgf X μ) a
```

- **規模**: ~5 行。型推論を楽にするだけ。
- **落とし穴**: なし。

### 自前 3: KL-of-tilted 恒等式 (★lower bound 用)

```lean
lemma klDiv_tilted_eq (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (lam : ℝ)
    (h_int : Integrable (fun ω => Real.exp (lam * X ω)) μ) :
    (klDiv (μ.tilted (lam * X ·)) μ).toReal
      = lam * (μ.tilted (lam * X ·))[X] - cgf X μ lam
```

- **規模**: ~30〜50 行。素材は `log_rnDeriv_tilted_left_self` + `klDiv` の RN-form 定義 + `integral_tilted_mul_self`。
- **落とし穴**:
  - `klDiv` Mathlib 定義は `∫⁻ x, klFun (μ.rnDeriv ν) ∂ν` (`ℝ≥0∞` 値)。`toReal` に落とすため `finite KL` 確認 (`klDiv (tilted μ) μ < ⊤`、tilted は AC で OK)。
  - `Integrable` 前提が散らかる。Mathlib `Tilted.lean` の補題群を頼って軽くできるか要 plumbing。

### 自前 4: Cramér upper bound 主定理

```lean
theorem cramer_upper
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_int : ∀ t, Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
    (a : ℝ) :
    limsup (fun n : ℕ =>
      (1 / (n : ℝ)) * Real.log
        (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop
      ≤ -legendre (cgf (X 0) μ) a
```

- **規模**: ~80〜120 行 (`iIndepFun.cgf_sum` + `measure_ge_le_exp_cgf` + `sup λ ≥ 0 (λ a - Λ λ)` 不等式)。
- **落とし穴**:
  - **`a ≥ E[X]`** の場合のみ非自明 (それ以外は upper bound trivial)。境界条件を `legendre Λ a` の非負性で吸収できるか確認。
  - `cgf (∑ X_i) μ t = ∑ cgf (X_i) μ t` を `IdentDistrib` で `= n * cgf X μ t` に潰す部分は `Finset.sum_const + nsmul`。
  - **`legendre Λ a = sSup_{λ ∈ ℝ}` だが、Chernoff bound は `λ ≥ 0` のみ** (upper tail)。`λ < 0` で `t λ - Λ λ` を考えてもそれは lower tail。**`legendre_pos_part` `:= sSup_{λ ≥ 0} (λ a - Λ λ)` の分離が必要かも**、または `a ≥ E[X]` 仮定下で `sSup = sSup_{λ ≥ 0}` を別 lemma で示す (凸最大化の標準結果)。

### 自前 5: Cramér lower bound 主定理 (achievability)

```lean
theorem cramer_lower
    ... (a : ℝ) (h_lam : ∃ lam : ℝ, lam ≥ 0 ∧ deriv (cgf (X 0) μ) lam = a) :
    -legendre (cgf (X 0) μ) a
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop
```

- **規模**: ~120〜180 行。
- **戦略**:
  1. `λ^*` を `Λ'(λ^*) = a` で取る (`h_lam` 仮定)。
  2. `μ_{λ^*} := μ.tilted (λ^* * X 0 ·)` 構築。
  3. Tilted 下で `\bar S_n^μ_{λ^*} → a` (LLN 弱形 + tilted 平均 = `Λ'(λ^*) = a` from `integral_tilted_mul_self`)。
  4. Change-of-measure: `μ({a ≤ \bar S_n}) ≥ ∫_{a ≤ \bar S_n - ε} exp(-λ^* ∑X + n Λ(λ^*)) dμ_{λ^*}` (RN 経由)。
  5. 指数を取り `(1/n) log` で `≥ -λ^* a + Λ(λ^*) + o(1) = -legendre Λ a + o(1)`。
- **落とし穴**:
  - **n-IID tilted: `(μ^∞).tilted (∑ λ X i)` vs `(μ.tilted (λ X)) ^∞`**。前者は不便 (ambient 全体への tilting)、後者を作って use したい。**Mathlib に `infinitePi (μ.tilted) = (infinitePi μ).tilted ?` が無い**ので自前 ~30 行。
  - LLN を tilted 下で適用するには `μ.tilted` 下でも `iIndepFun` を再証明 (tilting は AC で independence を保つが、Mathlib に直接 lemma があるか要 loogle)。

### 自前 6 (optional): Cramér Tendsto 形 sandwich

```lean
theorem cramer_tendsto
    ... :
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (μ.real {ω | (a : ℝ) * n ≤ ∑ X_i ω}))
      atTop (𝓝 (-legendre (cgf (X 0) μ) a))
```

- **規模**: ~10 行 (上 2 つを `tendsto_of_le_liminf_of_limsup_le` で sandwich)。
- **存在条件**: `a` が `Λ'` の像の内点 (`E[X] < a < ess sup X`) + Λ regular。

---

## 撤退ラインへの距離

### 親計画の現在の撤退ライン候補 (`docs/shannon/shannon-moonshot-plan.md` Tier 1 想定)

T1-C は roadmap 「~300〜500 行」「Sanov LDP 完成からほぼ含意」と設定。本 inventory で **発動するか**:

- **撤退 NOT 発動**: ✅
  - Mathlib `cgf`, `iIndepFun.cgf_sum`, `measure_ge_le_exp_cgf`, `Measure.tilted` が完備 ⇒ 主部品は全て存在。
  - Legendre transform は自作だが ~30〜60 行で済む。
  - 既存 Sanov LDP は **使わない** (むしろ reshape が高コスト) — Sanov 経由の経路は不採用、`cgf`/`tilted` 直接経路を採用。
- **新たに浮上する制約 (撤退の縮退案として明記推奨)**:
  - **L-C1**: lower bound (achievability) で苦戦したら、**upper bound のみ publish** で打ち切り (~150 行)。Cover-Thomas でも upper bound は単独で有用 (Chernoff bound の n-IID 強化)。
  - **L-C2**: tilted 下 LLN の plumbing (n-IID tilted の独立性 + tilted 強収束) が当初予想より重ければ、**lower bound を仮定形** (`hypothesis : ∃ N, ∀ n ≥ N, μ_{λ^*}({|S̄_n - a| ≤ ε}) ≥ 1/2`) で publish。
  - **L-C3**: finite-alphabet specialization (`X = f ∘ (proj i)` for `f : α → ℝ`) に絞る。一般 `X : Ω → ℝ` 形は `integrableExpSet` 関連の plumbing が増えて +100 行。**最初は finite-alphabet 専用形で publish**。

### 規模見積もりの再評価

- roadmap 「300〜500 行」 vs 本 inventory 「**300〜400 行**」(upper + lower + Legendre 自作含む)
- 内訳: Legendre 自作 ~50、KL-of-tilted ~30、Cramér upper 主定理 ~120、Cramér lower 主定理 ~150、ambient + n-IID tilted plumbing ~50、tendsto sandwich ~10。
- **roadmap 下限寄り (350 行) が現実的**。upper だけで切るなら ~200 行、lower 込みで ~350 行。

---

## 着手 skeleton (`Common2026/Shannon/Cramer.lean`)

```lean
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import Common2026.InformationTheory.Asymptotic
-- intentionally NOT importing Common2026.Shannon.Sanov*: direct cgf/tilted route

/-!
# Cramér's theorem (T1-C, finite-alphabet specialization)

Cover-Thomas Theorem 11.4.1 specialized to finite-alphabet IID. Direct route via
`cgf` + `Measure.tilted`, not via Sanov contraction (cf. `cramer-mathlib-inventory.md`).

## 主定義
* `legendre Λ a := sSup ((fun lam => lam * a - Λ lam) '' univ)` — Mathlib 不在の Legendre 変換
* `cramerRate X μ a := legendre (cgf X μ) a` — Cramér rate function

## 主定理
* `cramer_upper`  — `limsup (1/n) log P[\bar S_n ≥ a] ≤ -cramerRate X μ a`
* `cramer_lower`  — achievability (tilted-measure 経路)
* `cramer_tendsto` (optional) — sandwich
-/

namespace InformationTheory.Shannon.Cramer

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Legendre transform** of `Λ : ℝ → ℝ` at `a`: `Λ^*(a) := sup_λ (λ·a − Λ(λ))`. -/
noncomputable def legendre (Λ : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)

/-- **Cramér rate function**. -/
noncomputable def cramerRate (X : Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ :=
  legendre (cgf X μ) a

lemma legendre_nonneg (Λ : ℝ → ℝ) (hΛ0 : Λ 0 = 0) (a : ℝ)
    (h_bdd : BddAbove ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)) :
    0 ≤ legendre Λ a := by sorry

lemma cgf_sum_eq_nsmul {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_int : ∀ t, Integrable (fun ω => Real.exp (t * X 0 ω)) μ) (t : ℝ) (n : ℕ) :
    cgf (∑ i ∈ Finset.range n, X i) μ t = (n : ℝ) * cgf (X 0) μ t := by sorry

lemma klDiv_tilted_eq (X : Ω → ℝ) [IsProbabilityMeasure μ] (lam : ℝ)
    (h_int : Integrable (fun ω => Real.exp (lam * X ω)) μ) :
    (InformationTheory.klDiv (μ.tilted (lam * X ·)) μ).toReal
      = lam * (μ.tilted (lam * X ·))[X] - cgf X μ lam := by sorry

/-- **Cramér upper bound** (finite-alphabet IID specialization). -/
theorem cramer_upper [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_int : ∀ t, Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
    (a : ℝ) :
    limsup (fun n : ℕ =>
      (1 / (n : ℝ)) * Real.log
        (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop
      ≤ -cramerRate (X 0) μ a := by sorry

/-- **Cramér lower bound** (achievability, tilted-measure proof). -/
theorem cramer_lower [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_int : ∀ t, Integrable (fun ω => Real.exp (t * X 0 ω)) μ)
    (a : ℝ) (h_lam : ∃ lam : ℝ, 0 ≤ lam ∧ deriv (cgf (X 0) μ) lam = a) :
    -cramerRate (X 0) μ a
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop := by sorry

end InformationTheory.Shannon.Cramer
```

---

## 既存率推定 (一覧)

- **Mathlib 既存**: CGF / MGF / tilted / Chernoff bound / IID cgf-sum / IdentDistrib / Measure.infinitePi — **80%** が直接呼べる
- **Common2026 既存**: IID infrastructure (`IIDProductInput`, 簡略形を取れば部分流用)、Asymptotic `DotEq`、Chernoff `IsCompact.exists_sInf_image_eq` テンプレ — **10%** 補助
- **自作必須**: Legendre transform 定義 + 性質、KL-of-tilted、Cramér 主定理 2 本 — **10%** (= 自作要 ~6 件、合計 300〜400 行)

**最終結論**: roadmap 「300〜500 行」「Sanov LDP からほぼ含意」 → 修正 **「300〜400 行」「Sanov LDP は使わず `cgf`/`tilted` 直接経路」**。撤退ライン発動なし、ただし lower bound 苦戦時の縮退案 L-C1〜L-C3 を予防的に明記推奨。
