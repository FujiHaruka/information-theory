# T3-A Constrained Maximum Entropy — Mathlib + InformationTheory 在庫調査

> 親計画: textbook roadmap T3-A (`docs/textbook-roadmap.md:206-213`)。
>
> 既存基盤: `MaxEntropy.lean` (269 行) + `CsiszarProjection.lean` (488 行) + `DifferentialEntropy.lean` Phase D (Gaussian max-entropy with variance 制約 ~250 行)。

## 一行サマリ

**完全に既存。** Mathlib `Measure.tilted` が exponential family そのもの (Esscher 形 `exp(f x) / ∫ exp f ∂μ`)、`Csiszar I-projection` は本リポに完成、`DifferentialEntropy.lean Phase D` に variance 制約版の Gibbs 流証明テンプレが既にある。**KKT は不要** — `tilted` を ansatz として与え、`klDiv (μ.tilted ⟨λ, f⟩) ν` の identity に Gibbs `klDiv ≥ 0` を当てれば finite-alphabet 版 T3-A は写経で完了。Lagrange API (`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`) も入手可。**実体 ~80%、自作必要 5-7 件、撤退ライン発動なし**。規模見積もり 400-700 行は**過大評価で、~250-350 行**が妥当。

最大の発見: `differentialEntropy_le_gaussian_of_variance_le` (`DifferentialEntropy.lean:510`) と `differentialEntropy_eq_gaussian_iff` (`DifferentialEntropy.lean:659`) が**変数 = `(x-m)²` を取り `λ = -1/(2v)` とした T3-A の特例**を Bochner 経由で既に書ききっている。T3-A の **finite-alphabet 版 (Ch.12 教科書記述)** はこれを `volume` → `count measure` に書き換えて pmf 形に縮めた**等価な構造**を持つ。**Mathlib-shape-driven の観点では `Measure.tilted` をそのまま reference 分布として採用**、ψ(λ) := `log (∫ exp ⟨λ, f⟩ ∂ν₀)` を `Real.log (mgf …)` 経由で定義するのが最短。

---

## 主定理候補シグネチャ (再掲 / 検討用)

教科書 (Cover-Thomas Ch.12) の核となる statement は **3 通り**に切れる。本在庫調査は **(A) finite-alphabet pmf 形** が最短かつ既存 API 親和的と判定。

### (A) Finite-alphabet pmf 形 (推奨)

```lean
theorem maxEntropy_constrained_eq_tilted_pmf
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    {k : ℕ} (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X)
    /- 制約: 𝔼[f_i(X)] = c_i -/
    (h_constraint : ∀ i : Fin k, ∫ ω, f i (X ω) ∂μ = c i)
    /- exponential family ansatz: ∃ λ : Fin k → ℝ で構成 -/
    (λ : Fin k → ℝ)
    (h_λ_constraint : ∀ i : Fin k,
       (∫ x, f i x ∂(((uniformOn (Set.univ : Set α)).tilted (fun x => ∑ i, λ i * f i x)))) = c i) :
    entropy μ X ≤
      -((∑ i, λ i * c i) - Real.log (∫ x, Real.exp (∑ i, λ i * f i x)
          ∂(uniformOn (Set.univ : Set α))))
```

戦略 (pseudo-Lean):
```
have hKL : 0 ≤ (klDiv (μ.map X) p_star).toReal     -- Gibbs (klDiv ENNReal nonneg + toReal)
rw [toReal_klDiv_of_measure_eq hac h_meas_eq]      -- = ∫ llr (μ.map X) p_star ∂(μ.map X)
-- llr (μ.map X) p_star x = log P(x) - log p_star(x)
--                        = log P(x) - (∑ i, λ i * f i x - ψ(λ) - log U(x))
-- (`U := uniformOn univ`, `p_star := U.tilted ⟨λ,f⟩`)
-- ∫ = -H(P) - log|α| - 𝔼[∑ λ i * f i X] + ψ(λ) - log|α|  ... の形整理
-- 制約 h_constraint で 𝔼[f i X] = c i 代入
linarith   -- ⟹ entropy μ X ≤ ψ(λ) - ∑ λ i * c i (+ log|α| 項相殺)
```

### (B) Csiszar I-projection 経由 (代替)

`CsiszarProjection.lean` の existing API に乗せる。`K := {P ∈ stdSimplex | ∀ i, ∑ a, P a * f i a = c i}` (closed convex sublevel) を引数化し、`csiszar_projection_exists` + `csiszar_projection_unique` で **最小化元 P\* の存在 + 一意性**を一発で取り、`csiszar_pythagoras_inequality` から `D(P‖U) = D(P‖P\*) + D(P\*‖U)` を引いて main 不等式に変換。**メリット**: KL ベース、`stdSimplex` 上の既存閉凸集合議論を再利用。**デメリット**: Csiszar の `K` 引数 (制約集合) の closedness/nonemptyness を別途証明 (~30 行)。

### (C) Lagrange multipliers 形 (Mathlib full)

`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt` (`Mathlib/Analysis/Calculus/LagrangeMultipliers.lean:108`) を直接 entropy `H : (Fin n → ℝ) → ℝ` (pmf simplex 上) に適用。**問題**: H の **`HasStrictFDerivAt` を `∑ p_i = 1` 制約境界点で示すのが面倒** + 内部のみで成り立つため境界で必要 (`p_i = 0` の atom) なら追加議論。**避けるべき**。本在庫調査では Lagrange は **参考枠**として置く。

---

## API 在庫テーブル

### A. Exponential family / Esscher tilting (`Mathlib/MeasureTheory/Measure/Tilted.lean`)

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| **`Measure.tilted`** | `Tilted.lean:42` | `noncomputable def Measure.tilted (μ : Measure α) (f : α → ℝ) : Measure α := μ.withDensity (fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ))` | **核**: `p^*(x) ∝ exp(f x)` の Mathlib 表現。`f := fun x => ∑ i, λ i * f i x` で多重 constraint 対応 |
| **`isProbabilityMeasure_tilted`** | `Tilted.lean:126` | `[NeZero μ] (hf : Integrable (fun x ↦ exp (f x)) μ) : IsProbabilityMeasure (μ.tilted f)` | tilted 測度が確率測度になる条件 (integrability + base ≠ 0) |
| **`tilted_apply'`** | `Tilted.lean:101` | `(μ : Measure α) (f : α → ℝ) {s : Set α} (hs : MeasurableSet s) : μ.tilted f s = ∫⁻ a in s, ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) ∂μ` | singleton 評価 `(μ.tilted f) {x}` 取得 |
| **`tilted_absolutelyContinuous`** | `Tilted.lean:280` | `(μ : Measure α) (f : α → ℝ) : μ.tilted f ≪ μ` | `p^* ≪ ν₀` 自動。`klDiv P p^*` の `≪` 条件はここから |
| **`absolutelyContinuous_tilted`** | `Tilted.lean:283` | `(hf : Integrable (fun x ↦ exp (f x)) μ) : μ ≪ μ.tilted f` | 逆方向。両側 AC が直接出るのが嬉しい |
| **`integral_tilted`** | `Tilted.lean:230` | `(f : α → ℝ) (g : α → E) : ∫ x, g x ∂(μ.tilted f) = ∫ x, (exp (f x) / ∫ x, exp (f x) ∂μ) • (g x) ∂μ` | tilted 測度上の期待値 ↔ base 測度上の重み付き積分 |
| **`integral_exp_tilted`** | `Tilted.lean:236` | `(f g : α → ℝ) : ∫ x, exp (g x) ∂(μ.tilted f) = (∫ x, exp ((f + g) x) ∂μ) / ∫ x, exp (f x) ∂μ` | `mgf` 同士の比。`f, g` 線形ならば cgf 加法則 |
| **`tilted_tilted`** | `Tilted.lean:251` | `(hf : Integrable (fun x ↦ exp (f x)) μ) (g : α → ℝ) : (μ.tilted f).tilted g = μ.tilted (f + g)` | exponential family は tilting で閉じる。**Lagrange パラメータ更新** |
| **`rnDeriv_tilted_left_self`** | `Tilted.lean:360` | `[SigmaFinite μ] (hf : AEMeasurable f μ) : (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ)` | `rnDeriv` の閉形 |
| **`log_rnDeriv_tilted_left_self`** | `Tilted.lean:366` | `[SigmaFinite μ] (hf : Integrable (fun x ↦ exp (f x)) μ) : (fun x ↦ log ((μ.tilted f).rnDeriv μ x).toReal) =ᵐ[μ] fun x ↦ f x - log (∫ x, exp (f x) ∂μ)` | **核**: `log p^* - log ν₀ = ⟨λ,f⟩ - ψ(λ)`。これが `llr` の閉形を与える |

**注 (前提)**: `[SigmaFinite μ]`, `Integrable (fun x ↦ exp (f x)) μ` が要となる。Finite-alphabet 上の `uniformOn (univ : Set α)` はもちろん両方を満たす (Fintype + 確率測度 → SigmaFinite + bounded f → integrable exp f)。

### B. Log-partition function ψ(λ) (cgf / mgf 経由)

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| **`ProbabilityTheory.mgf`** | `Probability/Moments/Basic.lean:121` | `def mgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ := μ[fun ω => exp (t * X ω)]` | scalar case (`f` 1 つ) |
| **`ProbabilityTheory.cgf`** | `Probability/Moments/Basic.lean:125` | `def cgf (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ := log (mgf X μ t)` | scalar log-partition |
| `hasDerivAt_mgf` | `Probability/Moments/MGFAnalytic.lean:62` | `(h : t ∈ interior (integrableExpSet X μ)) : HasDerivAt (mgf X μ) (μ[fun ω ↦ X ω * exp (t * X ω)]) t` | ψ'(λ) = 𝔼_λ[X]。**Lagrange 矛盾用** |
| `analyticOn_mgf` | `Probability/Moments/MGFAnalytic.lean` (defs L70+) | mgf is analytic on integrability interval | 凸性証明の基盤 |
| `ConvexOn.cgf` / `cgf_convex` | — | **❌ Mathlib に不在** (`rg + loogle` 共に 0 件) | **自作 (~30 行)** が必要なら。ただし T3-A 本体には**不要** — Gibbs 直接ルート |

**重要**: 多重制約 `f : Fin k → α → ℝ` 版の log-partition `ψ(λ) := log (∫ exp (∑ i, λ i * f i x) ∂ν₀)` は Mathlib に**専用名なし**。`Real.log (∫ x, Real.exp (∑ i, λ i * f i x) ∂ν₀)` を素で書くか、ローカル `def psi (λ : Fin k → ℝ) : ℝ := …` で導入する。

### C. KL divergence — Csiszar 既存 (`InformationTheory/Shannon/CsiszarProjection.lean`)

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| **`klDivPmf`** | `CsiszarProjection.lean:55` | `noncomputable def klDivPmf (P Q : α → ℝ) : ℝ := ∑ a : α, Q a * klFun (P a / Q a)` | finite-alphabet KL (Real 形) |
| `klDivPmf_nonneg` | `CsiszarProjection.lean:61` | `(P Q : α → ℝ) (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) : 0 ≤ klDivPmf P Q` | Gibbs (Real 形) |
| `continuous_klDivPmf_left` | `CsiszarProjection.lean:71` | `(Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) : Continuous (fun P : α → ℝ => klDivPmf P Q)` | 連続性 (compactness 議論用) |
| **`klDivPmf_strictConvexOn_left`** | `CsiszarProjection.lean:93` | `(Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) : StrictConvexOn ℝ (stdSimplex ℝ α) (fun P : α → ℝ => klDivPmf P Q)` | **一意性の核**。T3-A (B) 経路でそのまま再利用 |
| **`csiszar_projection_exists`** | `CsiszarProjection.lean:172` | `{K : Set (α → ℝ)} {Q : α → ℝ} (hK_closed : IsClosed K) (hK_sub : K ⊆ stdSimplex ℝ α) (hK_ne : K.Nonempty) (hQ_pos : ∀ a, 0 < Q a) : ∃ Qstar ∈ K, IsMinOn (fun P => klDivPmf P Q) K Qstar` | **存在性そのまま**: K に constraint sublevel を入れる |
| **`csiszar_projection_unique`** | `CsiszarProjection.lean:186` | `{K : Set (α → ℝ)} {Q : α → ℝ} (hK_conv : Convex ℝ K) (hK_sub : K ⊆ stdSimplex ℝ α) (hQ_pos : ∀ a, 0 < Q a) {Qstar Qstar' : α → ℝ} (hQs : Qstar ∈ K) (hQs' : Qstar' ∈ K) (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar) (hmin' : IsMinOn (fun P => klDivPmf P Q) K Qstar') : Qstar = Qstar'` | **一意性そのまま** |
| **`csiszar_pythagoras_inequality`** | `CsiszarProjection.lean:449` | `{K : Set (α → ℝ)} {Q : α → ℝ} (hK_conv : Convex ℝ K) (hK_sub : K ⊆ stdSimplex ℝ α) (hQ_sum : ∑ a, Q a = 1) (hQ_pos : ∀ a, 0 < Q a) {Qstar : α → ℝ} (hQs : Qstar ∈ K) (hQs_pos : ∀ a, 0 < Qstar a) (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar) {P : α → ℝ} (hP : P ∈ K) (hP_pos : ∀ a, 0 < P a) : klDivPmf P Q ≥ klDivPmf P Qstar + klDivPmf Qstar Q` | **(B) 経路の核**: 制約集合への projection が exponential family |
| `csiszar_first_order_condition` | `CsiszarProjection.lean:295` | (1 次条件 — 上の証明内部で使用) | optimality 用、変数 reuse 可能 |

### D. KL divergence — Mathlib Measure 形 (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`)

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| `klDiv` | `Basic.lean:57` | `noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞ := if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) else ∞` | (A) 経路で `klDiv (μ.map X) (U.tilted …)` |
| **`klDiv_self`** | `Basic.lean:78` | `(μ : Measure α) [SigmaFinite μ] : klDiv μ μ = 0` (`@[simp]`) | 補助 |
| `klDiv_ne_top` | `Basic.lean:103` | `(hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) : klDiv μ ν ≠ ∞` | `toReal` 経由の前提保証 |
| **`toReal_klDiv_of_measure_eq`** | `Basic.lean:164` | `(h : μ ≪ ν) (h_eq : μ univ = ν univ) : (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ` | **核 (A 経路)**: 確率測度同士なら無条件で integral 形に |
| `toReal_klDiv_eq_integral_klFun` | `Basic.lean:170` | `(h : μ ≪ ν) : (klDiv μ ν).toReal = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν` | klFun 形 (Sanov 用) |
| **`klDiv_eq_zero_iff`** | `Basic.lean:377` | `[IsFiniteMeasure μ] [IsFiniteMeasure ν] : klDiv μ ν = 0 ↔ μ = ν` | **uniqueness の核**: entropy = ψ(λ) - ⟨λ,c⟩ で等号 ⟺ μ.map X = tilted |
| `klDiv_eq_lintegral_klFun_of_ac` | `Basic.lean:138` | `(h_ac : μ ≪ ν) : klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν` | lintegral 経路 |
| `mul_log_le_klDiv` | `Basic.lean:360` | `(μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ENNReal.ofReal (μ.real univ * log (μ.real univ / ν.real univ) + ν.real univ - μ.real univ) ≤ klDiv μ ν` | log-sum 風下界 (使う見込み低) |

**注 (`llr` ⇄ `Real.log rnDeriv` の翻訳)**: `llr μ ν x := Real.log (μ.rnDeriv ν x).toReal` (定義)。 `Tilted.lean:366` の `log_rnDeriv_tilted_left_self` で `llr P (μ.tilted f)` の閉形が直接出る。

### E. 既存 InformationTheory — 完全に再利用可能なテンプレ

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| **`entropy`** | `InformationTheory/Shannon/Bridge.lean:43` | `noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})` | 主定理 LHS |
| `entropy_nonneg` | `InformationTheory/Shannon/Bridge.lean:47` | `(μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (hXs : Measurable Xs) : 0 ≤ entropy μ Xs` | 補助 |
| **`klDiv_uniformOn_univ_toReal_eq`** | `InformationTheory/Shannon/MaxEntropy.lean:123` | `(μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) : (klDiv (μ.map X) (uniformOn (Set.univ : Set α))).toReal = Real.log (Fintype.card α) - entropy μ X` | **T3-A 制約なし (uniform) 退化形**。`f := 0` で T3-A から出るはず |
| **`entropy_le_log_card`** | `InformationTheory/Shannon/MaxEntropy.lean:229` | `(μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) : entropy μ X ≤ Real.log (Fintype.card α)` | uniform 制約退化形 |
| **`entropy_eq_log_card_iff`** | `InformationTheory/Shannon/MaxEntropy.lean:241` | `(μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) : entropy μ X = Real.log (Fintype.card α) ↔ μ.map X = uniformOn (Set.univ : Set α)` | 退化形 uniqueness |
| **`differentialEntropy_le_gaussian_of_variance_le`** | `InformationTheory/Shannon/DifferentialEntropy.lean:510` | `{μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ)) (h_var_int : Integrable (fun x => (x - m)^2) μ) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) : differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | **T3-A の連続版・variance 制約特例**。証明テンプレ写経で finite-alphabet 版が書ける (~150 行) |
| **`differentialEntropy_eq_gaussian_iff`** | `InformationTheory/Shannon/DifferentialEntropy.lean:659` | `{μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ = (v : ℝ)) (h_var_int : Integrable (fun x => (x - m)^2) μ) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) : differentialEntropy μ = (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v) ↔ μ = gaussianReal m v` | uniqueness テンプレ (klDiv_eq_zero_iff 経由) |
| **`klDivSumForm`** | `InformationTheory/Shannon/Sanov.lean:73` | `noncomputable def klDivSumForm (P Q : Measure α) : ℝ := ∑ a : α, P.real {a} * (Real.log (P.real {a}) - Real.log (Q.real {a}))` | Measure 形 sum 形 KL (T3-A pmf ↔ measure 翻訳橋) |
| `klDivSumForm_eq_toReal_klDiv` | `InformationTheory/Shannon/Sanov.lean:252` | (前提付き; `P ≪ Q`, full support) | sum 形と `(klDiv P Q).toReal` の同値性 (private 確認要) |
| **`klDivPmf_self_eq_zero`** | `InformationTheory/Shannon/Chernoff.lean:252` | `(P : α → ℝ) (hP_pos : ∀ a, 0 < P a) : klDivPmf P P = 0` | `tilted` 自身の KL = 0 用 |

### F. Constraint set / stdSimplex (`Mathlib/Analysis/Convex/StdSimplex.lean`)

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| **`stdSimplex`** | `StdSimplex.lean:35` | `def stdSimplex : Set (ι → 𝕜) := { f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }` | pmf 空間そのもの |
| **`convex_stdSimplex`** | `StdSimplex.lean:42` | `[IsOrderedRing 𝕜] : Convex 𝕜 (stdSimplex 𝕜 ι)` | (B) 経路で `K` の凸性 |
| **`isCompact_stdSimplex`** | `StdSimplex.lean:187` | `[CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] : IsCompact (stdSimplex 𝕜 ι)` | 制約集合 K のコンパクト性 (closed subset of compact) |
| `isClosed_stdSimplex` | `StdSimplex.lean:178` (defs L178+) | (closed under product topology) | K の closedness |
| `stdSimplex_subset_Icc` | `StdSimplex.lean:74` | `[IsOrderedAddMonoid 𝕜] : stdSimplex 𝕜 ι ⊆ Icc 0 1` | atom mass bounds |
| **`isCompact_of_subset_stdSimplex`** | `InformationTheory/Shannon/CsiszarProjection.lean:165` | `{K : Set (α → ℝ)} (hK_closed : IsClosed K) (hK_sub : K ⊆ stdSimplex ℝ α) : IsCompact K` | 制約集合のコンパクト性 (一発) |

### G. Extreme value theorem (`Mathlib/Topology/Order/Compact.lean`)

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| **`IsCompact.exists_isMinOn`** | `Compact.lean:228` | `[ClosedIicTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x` | 存在性 (B 経路で再利用済) |
| `IsCompact.exists_isMaxOn` | `Compact.lean:246` | (双対) | uniform 退化形 (entropy 最大化を直接取る場合) |
| `IsCompact.exists_sInf_image_eq_and_le` | `Compact.lean:405` | (sInf 実現) | 既存 hoeffdingE2 で使用済テンプレ |

### H. Lagrange multipliers (`Mathlib/Analysis/Calculus/LagrangeMultipliers.lean`)

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| `IsLocalExtrOn.range_ne_top_of_hasStrictFDerivAt` | `LagrangeMultipliers.lean:46` | `(hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) : (f'.prod φ').range ≠ ⊤` | geometry 形 |
| `IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt` | `LagrangeMultipliers.lean:62` | `(hextr : IsLocalExtrOn φ {x | f x = f x₀} x₀) (hf' : HasStrictFDerivAt f f' x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) : ∃ (Λ : Module.Dual ℝ F) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ ∀ x, Λ (f' x) + Λ₀ • φ' x = 0` | 単一 constraint 形 |
| **`IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt`** | `LagrangeMultipliers.lean:108` | `{ι : Type*} [Fintype ι] {f : ι → E → ℝ} {f' : ι → StrongDual ℝ E} (hextr : IsLocalExtrOn φ {x | ∀ i, f i x = f i x₀} x₀) (hf' : ∀ i, HasStrictFDerivAt (f i) (f' i) x₀) (hφ' : HasStrictFDerivAt φ φ' x₀) : ∃ (Λ : ι → ℝ) (Λ₀ : ℝ), (Λ, Λ₀) ≠ 0 ∧ (∑ i, Λ i • f' i) + Λ₀ • φ' = 0` | **multi constraint 形**。φ := entropy, f i := `∑ p_a * f_i(a)`、x₀ := tilted pmf で適用 |
| `IsLocalExtrOn.linear_dependent_of_hasStrictFDerivAt` | `LagrangeMultipliers.lean:131` | (linear dependence 形) | 同上の双対 |

**注 (KKT は不在)**: ファイル先頭 (`LagrangeMultipliers.lean:22-24`) に `TODO: Formalize Karush-Kuhn-Tucker theorem` と明記。**Mathlib に KKT は無い**。ただし T3-A では equality constraint のみで inequality は entropy ≤ log|α| の境界処理に縮約できるため、KKT は**不要**。

**現実的判断**: Lagrange API を T3-A で使うと、`HasStrictFDerivAt` の連鎖 (entropy on simplex の Frechet 微分) を別途 ~150 行書く必要があり、**直接 Gibbs 経路 (A) の方が圧倒的に短い**。Lagrange は教科書記述との対応説明用 docstring に留めるのが最善。

### I. Convex analysis (`Mathlib/Analysis/Convex/`)

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| `convexOn_exp` | `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:63` | `ConvexOn ℝ univ exp` | exp 凸性 |
| `strictConvexOn_exp` | `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:41` | `StrictConvexOn ℝ univ exp` | strict 版 |
| `strictConcaveOn_log_Ioi` | `Mathlib/Analysis/Convex/SpecificFunctions/Basic.lean:67` | `StrictConcaveOn ℝ (Ioi 0) log` | log 凹性 (entropy 凹性源) |
| **`Real.concaveOn_negMulLog`** | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:227` | `ConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog` | **entropy 凹性の per-term 源** |
| **`Real.strictConcaveOn_negMulLog`** | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:224` | `StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog` | **uniqueness 直接源**: entropy 厳密凹 |
| `convexOn_mul_log` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:144` | `ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x)` | klFun 凸性の源 |
| `strictConvexOn_mul_log` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:137` | `StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x)` | strict 版 |
| **`InformationTheory.convexOn_klFun`** | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean` (使用例: Csiszar) | `ConvexOn ℝ (Set.Ici (0 : ℝ)) klFun` | KL 凸性源 |
| **`InformationTheory.strictConvexOn_klFun`** | 同上 | `StrictConvexOn ℝ (Set.Ici (0 : ℝ)) klFun` | KL strict 凸性 (Csiszar uniqueness) |
| **`ConcaveOn.le_map_sum`** (Jensen) | `Mathlib/Analysis/Convex/Jensen.lean:73` | `(hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) : (∑ i ∈ t, w i • f (p i)) ≤ f (∑ i ∈ t, w i • p i)` | Jensen 凹版 |
| **`StrictConcaveOn.lt_map_sum`** | `Mathlib/Analysis/Convex/Jensen.lean:147` | `(hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hp : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k) : ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i)` | strict Jensen (uniqueness の代替経路) |
| `StrictConcaveOn.map_sum_eq_iff` | `Mathlib/Analysis/Convex/Jensen.lean` (defs L165+) | (equality case) | uniqueness 直接式 |

### J. Real.exp / Real.log 補助

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| `Real.exp_log` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | `(hx : 0 < x) : Real.exp (Real.log x) = x` | `p^*(x) = exp(...)` ↔ `log p^* = ...` |
| `Real.log_exp` | 同上 | `(x : ℝ) : Real.log (Real.exp x) = x` | 同上 |
| `Real.exp_sum` | `Mathlib/Analysis/Complex/Exponential.lean` | `(s : Finset ι) (f : ι → ℝ) : Real.exp (∑ i ∈ s, f i) = ∏ i ∈ s, Real.exp (f i)` | exponential family 因子化 (使用見込み低) |
| `Real.log_mul` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | `(hx : x ≠ 0) (hy : y ≠ 0) : Real.log (x * y) = Real.log x + Real.log y` | log 加法 |
| `Real.log_div` | 同上 | `(hx : x ≠ 0) (hy : y ≠ 0) : Real.log (x / y) = Real.log x - Real.log y` | llr 計算で頻用 |

### K. Variational characterization (`klDiv ≥ ∫ f - log ∫ exp f`)

| 概念 | 状態 |
|---|---|
| **Donsker-Varadhan 形** `klDiv μ ν = sup_{f bounded} (∫ f ∂μ - log ∫ exp f ∂ν)` | ❌ Mathlib 不在 (`rg + loogle` で確認、`Tilted.lean:14-19` のコメントが variational expression の動機を述べているのみ) |
| 片側 `∫ f ∂μ - log ∫ exp f ∂ν ≤ klDiv μ ν` (Gibbs から直接) | ❌ Mathlib 不在。**自作 ~50 行**で可 (rnDeriv_tilted_left_self + log_rnDeriv_tilted_left_self + Gibbs) |
| `entropy P = inf_Q (-𝔼_P[log Q])` (cross entropy 形) | ❌ Mathlib 不在。**自作 ~30 行** (klDiv 非負を変形) |

**判断**: T3-A 本体には Donsker-Varadhan を**呼ばない方が短い**。経由するなら別 plan / 別ファイル (`docs/shannon/variational-form-*`) に切り出すべき。

### L. ENNReal / measureReal / 補助

| API | file:line | signature (verbatim) | Phase 扱い |
|---|---|---|---|
| `ENNReal.toReal_nonneg` | (`Mathlib.Data.ENNReal.Real`) | `0 ≤ x.toReal` | Gibbs から `≥ 0` 抽出 |
| `MeasureTheory.integral_fintype` | (`Mathlib.MeasureTheory.Integral.Bochner.Basic`) | `(h : Integrable f μ) [Fintype α] [MeasurableSingletonClass α] : ∫ a, f a ∂μ = ∑ a, μ.real {a} • f a` | Fintype 上の Bochner ↔ 有限和 |
| `MeasureTheory.lintegral_fintype` | 同上 (lintegral 版) | (同形) | 補助 |
| `MeasureTheory.Measure.withDensity_rnDeriv_eq` | (`MeasureTheory.Decomposition.RadonNikodym`) | `ν.withDensity (μ.rnDeriv ν) = μ` when `μ ≪ ν` | rnDeriv 恒等 |
| `Measure.isProbabilityMeasure_map` | (`MeasureTheory.Measure.Map`) | `(hX : AEMeasurable X μ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (μ.map X)` | `μ.map X` 自動 IsProbability |

---

## 主要前提条件ボックス (事故の起きやすい lemma)

- **`Measure.tilted f` の `IsProbabilityMeasure` 化**: `isProbabilityMeasure_tilted` (`Tilted.lean:126`) は `[NeZero μ]` **と** `Integrable (fun x ↦ exp (f x)) μ` の**両方**を要求。有限 alphabet では自明 (uniform は nonzero、`exp` は bounded) だが、infinite alphabet ↑ サポートでも書きたければ `hf` 仮説を明示しないと sorry になる。
- **`Csiszar projection` の前提リスト**: `csiszar_projection_exists` は `hQ_pos : ∀ a, 0 < Q a` (**reference Q の full support**) を要求。`uniformOn (Set.univ : Set α)` は OK だが、`uniformOn (S : Set α)` (subset) を Q に使うと **`Q a = 0` for `a ∉ S` で前提崩れ**。T3-A で support 制約を入れる場合は **Q を制限した tilted 形に再定義**するか、`a ∈ S` で restrict した sub-simplex に持っていく。
- **`klDiv_eq_zero_iff` の `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`**: 両側 finite 前提。確率測度なら自動だが、有限とは限らない base ν₀ (counting measure on infinite set など) を取ると**ここで詰む**。T3-A finite-alphabet 版では問題なし。
- **`toReal_klDiv_of_measure_eq` の `μ univ = ν univ`**: 確率測度同士なら自動だが、`uniformOn univ` と `tilted` 比で `tilted` 側が `tilted_of_not_integrable` で 0 測度になる場合 (= integrability が崩れた場合) に `μ univ ≠ ν univ` の罠あり。`isProbabilityMeasure_tilted` を必ず先に確保。
- **`Real.log` と `Finset.sum`** の交換: `Real.log ∘ Finset.sum` は線形にならない (`Real.log_prod` はあるが `Real.log_sum` は無い、log-sum-exp は別物)。ψ(λ) 内部の `Real.log (∫ x, Real.exp (∑ i, λ i * f i x) ∂U)` を per-term 分解しようとすると詰む。**そのまま integral を保持**。
- **`Tilted` の `rnDeriv` 翻訳の `=ᵐ` (a.e. equality)**: `rnDeriv_tilted_left_self` 等は `=ᵐ[μ]` (μ-a.e.) であり、pointwise 等式ではない。**`filter_upwards`** で hypothesis を取り出すパターンを忘れずに。

---

## 自作が必要な要素

優先度順:

### (1) `psi_λ` (log-partition) 定義 + 連続性 + 凸性 — ~30-50 行 ⭐
**推奨**:
```lean
noncomputable def psi (f : Fin k → α → ℝ) (ν₀ : Measure α) (λ : Fin k → ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (∑ i, λ i * f i x) ∂ν₀)
```
**用途**: T3-A 主定理の RHS。`mgf` を多変数化したもの。凸性は `convexOn_exp` + Jensen で手書き。
**落とし穴**: `λ ↦ ∫ exp(⟨λ,f⟩) ∂ν₀` の凸性は `ConvexOn` 不在のため self-derive。Holder/log-convexity 経由 ~50 行。**T3-A 本体には不要** (`λ` は ansatz で外から与えるため)、凸性は uniqueness 用の付加補題。

### (2) `klDiv (μ.map X) (ν₀.tilted ⟨λ, f⟩)` の閉形 — ~40 行 ⭐⭐
**推奨**:
```lean
lemma toReal_klDiv_map_tilted_eq_entropy_form
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X)
    (ν₀ : Measure α) [IsProbabilityMeasure ν₀]
    (hac : μ.map X ≪ ν₀)
    (f : Fin k → α → ℝ) (λ : Fin k → ℝ)
    (h_int : Integrable (fun x => Real.exp (∑ i, λ i * f i x)) ν₀) :
    (klDiv (μ.map X) (ν₀.tilted (fun x => ∑ i, λ i * f i x))).toReal
      = (klDiv (μ.map X) ν₀).toReal
        - (∑ i, λ i * ∫ ω, f i (X ω) ∂μ)
        + psi f ν₀ λ
```
**用途**: T3-A の核となる algebraic identity。`log_rnDeriv_tilted_left_self` + `toReal_klDiv_of_measure_eq` + `integral_map` + `Finset.sum_*` の組み合わせ。**ここが T3-A 全体の重力中心**。

### (3) 主定理 `maxEntropy_constrained_le_psi_minus_inner` — ~80-120 行 ⭐⭐⭐
**推奨**: (A) finite-alphabet pmf 形シグネチャ (上記)。証明は:
- (a) `klDiv ≥ 0` (`ENNReal.toReal_nonneg`)
- (b) (2) の identity で展開
- (c) `klDiv (μ.map X) ν₀ = -H(X) + log|α|` (`klDiv_uniformOn_univ_toReal_eq` 再利用) — ν₀ = uniform の場合
- (d) `h_constraint` 代入
- (e) `linarith`

### (4) Uniqueness `entropy = ψ - ⟨λ,c⟩ ↔ μ.map X = ν₀.tilted ⟨λ,f⟩` — ~60-80 行 ⭐⭐
**推奨**: `klDiv_eq_zero_iff` を (2) の identity に被せるだけ。`differentialEntropy_eq_gaussian_iff` の証明 (`DifferentialEntropy.lean:659-787`) が**ほぼそのまま写経**できるテンプレ。

### (5) (B) Csiszar projection 経由の alternative — ~80-120 行 ⭐
**推奨**: 制約集合 `K := {P ∈ stdSimplex | ∀ i, ∑ a, P a * f i a = c i}` を引数化、`csiszar_projection_*` の hypothesis を埋める。**メリット**: KL 最小化として exponential family を `def` ではなく **theorem 経由**で出せる (教科書の "I-projection = exponential family" 形対応)。**デメリット**: pmf 形と tilted 形の翻訳補題 (~30 行) が追加で必要。

### (6) `psi` の凸性 (uniqueness 強化用) — ~50-80 行 ⭐
T3-A 本体には不要だが、双対 `ψ*` (Legendre transform) を入れて Fenchel-Young 形式に持っていきたい場合に必要。本 inventory のスコープ外。

**自作合計 (T3-A 必須分)**: 約 **210-290 行**。

---

## 撤退ラインへの距離

親計画 (`docs/textbook-roadmap.md:206-213`) の見積もり **400-700 行は過大**。実体率約 80% (既存テンプレ写経 + 自作 4 件) で **~250-350 行**が現実的。

### 撤退ラインに**触れない**

- **KKT 不在問題**: 親計画が「Lagrange 双対性 + KKT ~200」と書いているが、本調査で **KKT は不要**と判明 (Gibbs 直接ルートで equality constraint は十分扱える)。撤退発動なし。
- **`Measure.tilted` 不在問題**: **存在する** (`Tilted.lean:42`)。Esscher 形そのまま使える。
- **Csiszar projection 不在問題**: **`CsiszarProjection.lean` で完成済**。alternative proof として乗せられる。

### 撤退ライン候補 (発動はしないが、注意したい点)

- **`cgf_convex` 不在**: scalar 1 変数の cgf 凸性ですら Mathlib に無い。多変数 ψ(λ) の凸性を**主定理に書き込まない**設計に寄せる (uniqueness は `klDiv_eq_zero_iff` 経由で取れるので、ψ の凸性は補題スコープ)。
- **Variational form (Donsker-Varadhan) 不在**: T3-A に必要なら**別計画に切り出す**こと推奨。本 inventory では呼ばない設計。
- **Lagrange 経由 (C) を採用しない理由**: `entropy : (Fin n → ℝ) → ℝ` の `HasStrictFDerivAt` を `stdSimplex` の境界 (`p_a = 0`) で取り扱う議論が**~150 行膨らむ**。Mathlib-shape-driven で (A) 経路採用。

### 縮退案 (もしも (2) の identity が予想より重かった場合)

**新規撤退ライン提案**: 制約 `k = 1` (単一 mean constraint → exponential 分布) のみで commit。`Fin k` を `Unit` 相当に縮約することで Finset 走査が消え、~150 行で T3-A scalar 版 ("`𝔼[f(X)] = c` 下で `H` 最大 ⟺ `μ.map X ∝ exp(λ * f)`") が publish 可能。教科書 Ex. 12.1 (Boltzmann factor) 単独 publish になる。

---

## 既存率推定

| 構成要素 | 既存度 |
|---|---|
| Exponential family ansatz | ✅ 100% (`Measure.tilted`) |
| Log-partition ψ(λ) | 🟡 50% (`mgf`/`cgf` は scalar のみ、多変数版は self-derive) |
| Csiszar projection 経路 (B) | ✅ 100% (InformationTheory) |
| KL ≥ 0 (Gibbs) | ✅ 100% (`klDiv` ENNReal nonneg) |
| KL identity (`tilted` 展開) | ❌ 0% (自作 ~40 行) |
| Bochner / Fintype 積分翻訳 | ✅ 100% |
| Uniqueness (`klDiv = 0 ↔ equal`) | ✅ 100% (`klDiv_eq_zero_iff`) |
| Lagrange multipliers | ✅ 100% but **不使用推奨** |
| KKT | ❌ Mathlib 不在、**不要** |
| Variational form (Donsker-Varadhan) | ❌ Mathlib 不在、**不使用推奨** |
| Variance constraint 特例テンプレ | ✅ 100% (`DifferentialEntropy.lean` Phase D) |

**総合既存率: ~80%**。自作必要は ~5-7 件、すべて **既存テンプレ写経** or **Mathlib 補題 plumbing** で済む小規模ピース。

---

## 規模見積もり再評価

| 親計画 | 本調査 |
|---|---|
| Lagrange 双対性 + KKT ~200 | **不要** (Gibbs 経路) |
| Exponential family characterization + uniqueness ~200-300 | (3) + (4) で **~140-200** |
| Csiszar projection 経由 alternative ~100-200 | (5) で **~80-120** (optional) |
| (追加) `psi` 定義 + `klDiv tilted` identity | (1) + (2) で **~70-90** |
| **合計** | **(A) のみ ~210-290 / (A)+(B) 両方 ~290-410** |

親計画の **400-700 行 → 実体 ~250-350 行** (A 経路のみ採用)。**(A)+(B) 両搭載でも ~300-400 行**。安全マージン込み **~350 行が現実的天井**。

---

## 着手 skeleton (`InformationTheory/Shannon/MaxEntropyConstrained.lean`)

```lean
import InformationTheory.Shannon.MaxEntropy
import InformationTheory.Shannon.CsiszarProjection
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Constrained Maximum Entropy (Cover-Thomas Ch.12) — T3-A

有限アルファベット `α` 上の確率変数 `X : Ω → α` について、制約
`𝔼[f_i(X)] = c_i` (`i = 1..k`) のもとで Shannon entropy `H(X)` を最大化する
分布は exponential family (Boltzmann-Gibbs)
`p^*(x) ∝ exp (∑ i, λ_i · f_i(x))` で表現される。

## 主定理

* `psi`            — 多変数 log-partition: `ψ(λ) := log (∫ exp ⟨λ, f⟩ ∂ν₀)`
* `toReal_klDiv_map_tilted_eq` — algebraic identity (T3-A の核)
* `maxEntropy_constrained_le_psi_minus_inner`
                   — 主定理 (上界): `H(X) ≤ ψ(λ) - ⟨λ, c⟩ + log|α|` 形
* `maxEntropy_constrained_eq_iff_tilted`
                   — uniqueness: 等号 ⟺ `μ.map X = ν₀.tilted ⟨λ, f⟩`

## 戦略 (Approach)

`Mathlib/MeasureTheory/Measure/Tilted.lean` の `Measure.tilted` を exponential
family の reference 表現に採用。証明は **Gibbs (`klDiv ≥ 0`) 直接ルート**:

  0 ≤ KL(μ.map X ‖ ν₀.tilted ⟨λ,f⟩)
    = KL(μ.map X ‖ ν₀) - ⟨λ, 𝔼[f(X)]⟩ + ψ(λ)     -- (1) 主 identity
    = (log|α| - H(X)) - ⟨λ, c⟩ + ψ(λ)             -- ν₀ = uniform, 制約代入
  ∴ H(X) ≤ log|α| + ψ(λ) - ⟨λ, c⟩
  等号 ⟺ KL = 0 ⟺ μ.map X = ν₀.tilted ⟨λ,f⟩       -- klDiv_eq_zero_iff

`Measure.tilted` の `rnDeriv` 閉形 (`log_rnDeriv_tilted_left_self`,
`Tilted.lean:366`) が `llr` 計算を直線化、KKT / Lagrange multipliers は
**不要** (textbook 12.1 の Lagrangian 議論は `λ` ansatz を外から与えれば回避可)。
-/

namespace InformationTheory.Shannon.MaxEntropyConstrained

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {k : ℕ}

/-- Multi-variate log-partition function (Helmholtz free energy):
`ψ(λ) := log (∫ exp (∑ i, λ_i · f_i x) ∂ν₀)`. -/
noncomputable def psi (f : Fin k → α → ℝ) (ν₀ : Measure α) (λ : Fin k → ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (∑ i, λ i * f i x) ∂ν₀)

/-- Algebraic identity (T3-A の核): `KL(μ.map X ‖ ν₀.tilted ⟨λ,f⟩)` を
`KL(μ.map X ‖ ν₀)` と constraint expectation で分解。 -/
theorem toReal_klDiv_map_tilted_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X)
    (ν₀ : Measure α) [IsProbabilityMeasure ν₀]
    (hac : μ.map X ≪ ν₀)
    (f : Fin k → α → ℝ) (λ : Fin k → ℝ)
    (h_int : Integrable (fun x => Real.exp (∑ i, λ i * f i x)) ν₀) :
    (klDiv (μ.map X) (ν₀.tilted (fun x => ∑ i, λ i * f i x))).toReal
      = (klDiv (μ.map X) ν₀).toReal
        - (∑ i, λ i * ∫ ω, f i (X ω) ∂μ)
        + psi f ν₀ λ := by
  sorry

/-- **T3-A 主定理 (上界)**: 制約 `𝔼[f_i(X)] = c_i` 下で、任意の Lagrange parameter
`λ : Fin k → ℝ` で `H(X) ≤ log|α| + ψ(λ) - ⟨λ, c⟩`。 -/
theorem maxEntropy_constrained_le_psi_minus_inner
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X)
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (h_constraint : ∀ i : Fin k, ∫ ω, f i (X ω) ∂μ = c i)
    (λ : Fin k → ℝ)
    (h_int : Integrable
      (fun x => Real.exp (∑ i, λ i * f i x))
      (uniformOn (Set.univ : Set α))) :
    entropy μ X
      ≤ Real.log (Fintype.card α) + psi f (uniformOn (Set.univ : Set α)) λ
        - (∑ i, λ i * c i) := by
  sorry

/-- **T3-A uniqueness**: 上界等号成立 ⟺ `μ.map X = ν₀.tilted ⟨λ, f⟩`。 -/
theorem maxEntropy_constrained_eq_iff_tilted
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X)
    (f : Fin k → α → ℝ) (c : Fin k → ℝ)
    (h_constraint : ∀ i : Fin k, ∫ ω, f i (X ω) ∂μ = c i)
    (λ : Fin k → ℝ)
    (h_int : Integrable
      (fun x => Real.exp (∑ i, λ i * f i x))
      (uniformOn (Set.univ : Set α))) :
    entropy μ X
      = Real.log (Fintype.card α) + psi f (uniformOn (Set.univ : Set α)) λ
        - (∑ i, λ i * c i)
      ↔ μ.map X = (uniformOn (Set.univ : Set α)).tilted
                    (fun x => ∑ i, λ i * f i x) := by
  sorry

end InformationTheory.Shannon.MaxEntropyConstrained
```

`InformationTheory.lean` への追加行:
```lean
import InformationTheory.Shannon.MaxEntropyConstrained
```

---

## 判断ログ

- (2026-05-19, 初版) 親計画見積もり 400-700 行は **過大** と判定。`Measure.tilted` + Csiszar projection の既存度を見落としていた可能性。
- KKT は Mathlib 不在 (`LagrangeMultipliers.lean:22-24` で TODO 明記) だが、Gibbs 直接ルートで **不要**。撤退ライン非発動。
- Variational characterization (Donsker-Varadhan) は本 inventory **スコープ外**。別計画 (`docs/shannon/variational-form-*`) として将来切り出すこと推奨。
- `differentialEntropy_le_gaussian_of_variance_le` (DifferentialEntropy.lean:510) が **variance 制約版 T3-A の連続特例** として既に完成しているため、本ファイル (finite-alphabet) は**証明テンプレを写経できる**。リスク最小。
