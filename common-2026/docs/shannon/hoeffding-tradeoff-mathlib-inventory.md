# Hoeffding tradeoff (T1-D) Mathlib + InformationTheory inventory

> Source materials: roadmap `docs/textbook-roadmap.md` §T1-D (lines 144–150),
> sibling plan `docs/shannon/chernoff-hoeffding-moonshot-plan.md` (Phase D / E),
> sibling inventory `docs/shannon/chernoff-hoeffding-mathlib-inventory.md`.
> Existing Lean assets:
> - `InformationTheory/Shannon/Chernoff.lean` (1066 行, Tier 0 + Phase C achievability publish 済)
> - `InformationTheory/Shannon/CsiszarProjection.lean` (487 行, exists + unique + Pythagorean)
> - `InformationTheory/Shannon/Stein.lean` (1481 行, `steinOptimalBeta` Measure 経路)
> - `InformationTheory/Shannon/StrongStein.lean` (641 行, strict Tendsto for Type II)
> - `InformationTheory/Shannon/SanovLDPEquality.lean` (1243 行, sanov_ldp_equality Tendsto 形)

## 一行サマリ

**T1-D `hoeffdingE2` 自体の定義 + min 達成性 + 一意性 + 非負性 + 制約集合操作は `InformationTheory/Shannon/Chernoff.lean` で既に publish 済 (Tier 0 + Phase D 残)。残るは「Tendsto 形 `hoeffding_tradeoff` (n-IID Type II at Type I level `alpha` の指数収束 rate = `hoeffdingE2 P₁ P₂ alpha`)」のみ。これを実現するのに必要な Mathlib + InformationTheory API は実体ベース 100% 既存 (Sanov LDP equality + Stein typicality template + Csiszar projection + KL strict convexity)、自作必要なのは 4 種 (`steinTypeII_at_level` n-IID Type II at level `alpha` の pmf 形定義 + Qstar minimizer 性 + Sanov LDP per-Qstar 起動 + tradeoff sandwich wrapper)、合計 ~250-350 行。撤退ライン L-S1 (兄弟 plan で発動済) を本 plan に**正式 import** し、achievability/converse 分離スコープで進めるのが安全。**

| 数値 | 値 |
|---|---|
| 既存 API カバレッジ (実体ベース) | **約 100%** (Mathlib + InformationTheory plumbing 完備) |
| 既存 publish 済 (InformationTheory/Shannon/Chernoff.lean) | `hoeffdingE2`, `hoeffdingE2_attained`, `hoeffdingE2_nonneg`, `hoeffdingE2_unique`, `hoeffdingConstraintSet`, `hoeffdingConstraintSet_isClosed`, `hoeffdingConstraintSet_nonempty` |
| 自作必要な top-level | **4 種** (`steinTypeII_at_level` pmf 形 / Qstar minimizer / Sanov per-Qstar / tradeoff sandwich) |
| 規模見積もり (roadmap 200-300 行) の妥当性 | **整合**: ~250-350 行 (achievability ~120-150 + converse ~80-100 + wrapper ~40-50) |
| 撤退ライン L-S1 ((tradeoff Tendsto 形を T1-B converse と一緒に defer) | **既に発動済** (兄弟 plan 判断ログ #8); 本 plan は L-S1 を正式 import |

---

## 主定理の最終形 (再掲, roadmap §T1-D + sibling plan §ゴール)

教科書 statement (Cover-Thomas 11.7.x / Hoeffding tradeoff curve):

```
任意 alpha ∈ [0, D(P₁‖P₂)] に対し
E₂(alpha)  :=  min_{Q : D(Q‖P₁) ≤ alpha} D(Q‖P₂)

n-IID Type II error at Type I level alpha:
β_n(alpha) := inf { Q^n s | MeasurableSet s, P^n s^c ≤ alpha (per-IID 形は別) }

達成性: -(1/n) log β_n(alpha) → E₂(alpha)  (n → ∞)
```

Lean 風 signature (兄弟 plan §ゴールから verbatim):

```lean
namespace InformationTheory.Shannon.Chernoff

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- Hoeffding tradeoff exponent (既に Chernoff.lean:265 で publish 済). -/
noncomputable def hoeffdingE2 (P₁ P₂ : α → ℝ) (alpha : ℝ) : ℝ :=
  sInf ((fun Q : α → ℝ => klDivPmf Q P₂) ''
    {Q : α → ℝ | Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha})

/-- n-IID Type II error of the optimal level-`alpha` test (pmf 形). -/
noncomputable def steinTypeII_at_level_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : ℝ :=
  sInf { β : ℝ | ∃ s : Finset (Fin n → α),
    (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha ∧
    β = ∑ x ∈ s, ∏ i, P₂ (x i) }
  -- alternative: lift to Measure 経路 (Stein.lean:1139 `steinBetaSet` を流用 + pmfToMeasure bridge)

/-- **Hoeffding tradeoff lemma**: optimal Type II exponent equals `hoeffdingE2`. -/
theorem hoeffding_tradeoff
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : (∑ a, P₁ a) = 1) (hP₂_sum : (∑ a, P₂ a) = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_le : alpha ≤ klDivPmf P₁ P₂) :
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha))
```

### 証明戦略 (pseudo-Lean)

```text
1. Qstar が達成: hoeffdingE2_attained で ∃ Qstar ∈ K, E₂(α) = klDivPmf Qstar P₂
2. minimizer 性: ∀ Q ∈ stdSimplex with c_n/n ∈ "type around Qstar",
     klDivSumForm_ofVec Qstar (P₂.real ∘ singleton) ≤ klDivIndex c n P₂
   (これは Csiszar projection + Pythagoras から従う: Qstar is unique minimizer in K)
3. Sanov LDP equality 起動 (Qstar 周りの type class neighborhood E_n^* で):
     (1/n) log (P₂^n (⋃ T_c)) → -klDivSumForm Qstar P₂ = -E₂(α)
4. Type I level alpha 制御: ⋃ T_c は P₁^n 質量で 1 に近い (Qstar が K 内、constraint α 満たす)
     → P₁^n((⋃ T_c)^c) ≤ alpha eventually
5. つまり ∃ test (rejection region = (⋃ T_c)^c) で Type I ≤ alpha かつ Type II = P₂^n(⋃ T_c)
   ⇒ -(1/n) log β_n(alpha) ≥ -(1/n) log P₂^n(⋃ T_c) → E₂(α) (achievability)
6. Converse: Stein-style typicality 上界 (`steinTypicalSet_Q_prob_le` template) と
   Pythagorean inequality (`csiszar_pythagoras_inequality`) で
   -(1/n) log β_n(alpha) ≤ E₂(α) + δ (limsup)
7. sandwich → Tendsto
```

---

## API 在庫テーブル

### A. 既存 publish 済 (InformationTheory/Shannon/Chernoff.lean) — Phase D Tier 0 + Phase D 残

| 概念 | API | file:line | signature (verbatim) | T1-D での扱い |
|---|---|---|---|---|
| `hoeffdingE2` 定義 | `hoeffdingE2 (P₁ P₂ : α → ℝ) (alpha : ℝ) : ℝ` | `InformationTheory/Shannon/Chernoff.lean:265` | `noncomputable def hoeffdingE2 (P₁ P₂ : α → ℝ) (alpha : ℝ) : ℝ := sInf ((fun Q : α → ℝ => klDivPmf Q P₂) '' {Q : α → ℝ \| Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha})` (under `variable {α : Type*} [Fintype α] [DecidableEq α]`) | **そのまま再利用** |
| Hoeffding 制約集合 | `hoeffdingConstraintSet (P₁ : α → ℝ) (alpha : ℝ) : Set (α → ℝ)` | `Chernoff.lean:271` | `def hoeffdingConstraintSet (P₁ : α → ℝ) (alpha : ℝ) : Set (α → ℝ) := {Q : α → ℝ \| Q ∈ stdSimplex ℝ α ∧ klDivPmf Q P₁ ≤ alpha}` | そのまま再利用 (Tendsto 形では `Qstar ∈ this set` を回す) |
| 制約集合 non-empty | `hoeffdingConstraintSet_nonempty` | `Chernoff.lean:276` | `lemma hoeffdingConstraintSet_nonempty (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₁_sum : ∑ a, P₁ a = 1) (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) : (hoeffdingConstraintSet P₁ alpha).Nonempty` | そのまま再利用 |
| 制約集合 ⊆ stdSimplex | `hoeffdingConstraintSet_subset_stdSimplex` | `Chernoff.lean:286` | `lemma hoeffdingConstraintSet_subset_stdSimplex (P₁ : α → ℝ) (alpha : ℝ) : hoeffdingConstraintSet P₁ alpha ⊆ stdSimplex ℝ α` | そのまま再利用 |
| 制約集合 IsClosed | `hoeffdingConstraintSet_isClosed` | `Chernoff.lean:293` | `lemma hoeffdingConstraintSet_isClosed (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (alpha : ℝ) : IsClosed (hoeffdingConstraintSet P₁ alpha)` | そのまま再利用 |
| min 達成性 | `hoeffdingE2_attained` | `Chernoff.lean:310` | `theorem hoeffdingE2_attained (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (hP₁_sum : ∑ a, P₁ a = 1) (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) : ∃ Qstar ∈ hoeffdingConstraintSet P₁ alpha, hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂` | **Qstar 取り出しの core lemma** |
| 非負性 | `hoeffdingE2_nonneg` | `Chernoff.lean:339` | `theorem hoeffdingE2_nonneg (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (hP₁_sum : ∑ a, P₁ a = 1) (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) : 0 ≤ hoeffdingE2 P₁ P₂ alpha` | 補助 |
| min 達成点一意性 | `hoeffdingE2_unique` | `Chernoff.lean:585` | `theorem hoeffdingE2_unique (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a) (_hP₁_sum : ∑ a, P₁ a = 1) (alpha : ℝ) (_h_alpha_nn : 0 ≤ alpha) {Q₁ Q₂ : α → ℝ} (hQ₁_mem : Q₁ ∈ hoeffdingConstraintSet P₁ alpha) (hQ₂_mem : Q₂ ∈ hoeffdingConstraintSet P₁ alpha) (hQ₁_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Q₁ P₂) (hQ₂_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Q₂ P₂) : Q₁ = Q₂` | minimizer Qstar が "well-defined" な唯一の点であることに使う (Sanov per-Qstar 起動の minimizer 性立証で) |
| `klDivPmf P P = 0` | `klDivPmf_self_eq_zero` | `Chernoff.lean:254` | `lemma klDivPmf_self_eq_zero (P : α → ℝ) (hP_pos : ∀ a, 0 < P a) : klDivPmf P P = 0` | constraint set non-empty 用 |

### B. Csiszar projection plumbing (`InformationTheory/Shannon/CsiszarProjection.lean`)

| 概念 | API | file:line | signature (verbatim) | T1-D での扱い |
|---|---|---|---|---|
| `klDivPmf` | `klDivPmf (P Q : α → ℝ) : ℝ` | `CsiszarProjection.lean:55` | `noncomputable def klDivPmf (P Q : α → ℝ) : ℝ := ∑ a : α, Q a * klFun (P a / Q a)` (under `variable {α : Type*} [Fintype α] [DecidableEq α]`) | **被最適化 functional** (`E₂(α) = min D(Q‖P₂)`) |
| `klDivPmf` 連続性 (左変数) | `continuous_klDivPmf_left` | `CsiszarProjection.lean:71` | `lemma continuous_klDivPmf_left (Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) : Continuous (fun P : α → ℝ => klDivPmf P Q)` | constraint set 閉性 (既に Chernoff.lean:293 で使用) |
| `klDivPmf` strict convexity (左変数) | `klDivPmf_strictConvexOn_left` | `CsiszarProjection.lean:93` | `lemma klDivPmf_strictConvexOn_left (Q : α → ℝ) (hQ_pos : ∀ a, 0 < Q a) : StrictConvexOn ℝ (stdSimplex ℝ α) (fun P : α → ℝ => klDivPmf P Q)` | Qstar 一意性 (既に Chernoff.lean:585 で使用) + minimizer 性で再利用 |
| `klDivPmf` 非負性 | `klDivPmf_nonneg` | `CsiszarProjection.lean:61` | `lemma klDivPmf_nonneg (P Q : α → ℝ) (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) : 0 ≤ klDivPmf P Q` | 補助 |
| 閉サブシンプレックスのコンパクト性 | `isCompact_of_subset_stdSimplex` | `CsiszarProjection.lean:165` | `lemma isCompact_of_subset_stdSimplex {K : Set (α → ℝ)} (hK_closed : IsClosed K) (hK_sub : K ⊆ stdSimplex ℝ α) : IsCompact K` | constraint set コンパクト化 (既に Chernoff.lean:310 で使用) |
| 存在 (Csiszar projection) | `csiszar_projection_exists` | `CsiszarProjection.lean:172` | `theorem csiszar_projection_exists {K : Set (α → ℝ)} {Q : α → ℝ} (hK_closed : IsClosed K) (hK_sub : K ⊆ stdSimplex ℝ α) (hK_ne : K.Nonempty) (hQ_pos : ∀ a, 0 < Q a) : ∃ Qstar ∈ K, IsMinOn (fun P => klDivPmf P Q) K Qstar` | 既に Chernoff.lean:310 で使用 (IsMinOn 形は Tendsto wrapper でも直接使う) |
| 一意性 (Csiszar projection) | `csiszar_projection_unique` | `CsiszarProjection.lean:186` | `theorem csiszar_projection_unique {K : Set (α → ℝ)} {Q : α → ℝ} (hK_conv : Convex ℝ K) (hK_sub : K ⊆ stdSimplex ℝ α) (hQ_pos : ∀ a, 0 < Q a) {Qstar Qstar' : α → ℝ} (hQs : Qstar ∈ K) (hQs' : Qstar' ∈ K) (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar) (hmin' : IsMinOn (fun P => klDivPmf P Q) K Qstar') : Qstar = Qstar'` | **Tendsto 形での Qstar 同定** (sanov_ldp_equality の minimizer 仮定整理に使う) |
| Pythagorean inequality | `csiszar_pythagoras_inequality` | `CsiszarProjection.lean:449` | `theorem csiszar_pythagoras_inequality {K : Set (α → ℝ)} {Q : α → ℝ} (hK_conv : Convex ℝ K) (hK_sub : K ⊆ stdSimplex ℝ α) (hQ_sum : ∑ a, Q a = 1) (hQ_pos : ∀ a, 0 < Q a) {Qstar : α → ℝ} (hQs : Qstar ∈ K) (hQs_pos : ∀ a, 0 < Qstar a) (hmin : IsMinOn (fun P => klDivPmf P Q) K Qstar) {P : α → ℝ} (hP : P ∈ K) (hP_pos : ∀ a, 0 < P a) : klDivPmf P Q ≥ klDivPmf P Qstar + klDivPmf Qstar Q` | **Sanov per-Qstar 起動の minimizer 仮定**を出す核 (Cover-Thomas 11.6.1 の本質) |
| sum-form での klDivPmf | `klDivPmf_eq_log_diff_sum` | `CsiszarProjection.lean:231` | `lemma klDivPmf_eq_log_diff_sum {P Q : α → ℝ} (hP_sum : ∑ a, P a = 1) (hQ_sum : ∑ a, Q a = 1) (hP_pos : ∀ a, 0 < P a) (hQ_pos : ∀ a, 0 < Q a) : klDivPmf P Q = ∑ a : α, P a * (Real.log (P a) - Real.log (Q a))` | `klDivSumForm` との互換 (Sanov LDP との bridge) |

### C. Sanov LDP equality (`InformationTheory/Shannon/SanovLDPEquality.lean`)

| 概念 | API | file:line | signature (verbatim) | T1-D での扱い |
|---|---|---|---|---|
| `TypeCountIndex` | `TypeCountIndex (α : Type*) [Fintype α] (n : ℕ) : Type _` | `SanovLDP.lean:55` | `abbrev TypeCountIndex (α : Type*) [Fintype α] (n : ℕ) : Type _ := α → Fin (n+1)` | Qstar 近傍 type の構文 |
| `typeClassByCount` | `typeClassByCount {n : ℕ} (c : α → ℕ) : Set (Fin n → α)` | `SanovLDP.lean:82` | `def typeClassByCount {n : ℕ} (c : α → ℕ) : Set (Fin n → α) := ...` | Sanov 経路 primitive |
| `klDivIndex` | `klDivIndex (c : α → ℕ) (n : ℕ) (Q : Measure α) : ℝ` | `SanovLDP.lean:97` | `noncomputable def klDivIndex (c : α → ℕ) (n : ℕ) (Q : Measure α) : ℝ := ∑ a : α, ((c a : ℝ) / n) * (Real.log ((c a : ℝ) / n) - Real.log (Q.real {a}))` (under `variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`) | per-type exponent (sanov LDP equality の minimizer 仮定で使う) |
| `roundedTypeIndex` | `roundedTypeIndex (P : α → ℝ) (n : ℕ) : TypeCountIndex α n` | `SanovLDPEquality.lean:111` | `noncomputable def roundedTypeIndex (P : α → ℝ) (n : ℕ) : TypeCountIndex α n := ...` | Qstar 近傍 type の標準 construction (Phase E `Qstar` 周りの neighborhood E_n^* に使う) |
| `klDivSumForm_ofVec` | `klDivSumForm_ofVec (p q : α → ℝ) : ℝ` | `KLDivContinuous.lean:31` | `noncomputable def klDivSumForm_ofVec (p q : α → ℝ) : ℝ := ...` (formal pmf-pmf form) | `klDivPmf Qstar P₂` との bridge (Csiszar の `klDivPmf` ↔ Sanov の `klDivSumForm_ofVec` の互換) |
| `sanov_ldp_equality` | `sanov_ldp_equality` | `SanovLDPEquality.lean:1243` | `theorem sanov_ldp_equality (Q : Measure α) [IsProbabilityMeasure Q] (hQpos : ∀ a : α, 0 < Q.real {a}) (P : α → ℝ) (hP_prob : (∑ a, P a) = 1) (hP_full : ∀ a, 0 < P a) (E : ∀ n, Finset (TypeCountIndex α n)) (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n) (h_minimizer : ∀ n, ∀ c ∈ E n, klDivSumForm_ofVec P (fun a => Q.real {a}) ≤ klDivIndex (fun a => (c a : ℕ)) n Q) : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (((Measure.pi (fun _ : Fin n => Q)) (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal) atTop (𝓝 (-(klDivSumForm_ofVec P (fun a => Q.real {a}))))` | **T1-D 主機械** (Qstar 周辺の type class neighborhood E_n^* で Q := P₂ で起動 → -E₂(α) への収束) |

### D. Stein typicality (`InformationTheory/Shannon/Stein.lean`)

| 概念 | API | file:line | signature (verbatim) | T1-D での扱い |
|---|---|---|---|---|
| `llrPmf` (pointwise log-likelihood) | `llrPmf (P Q : Measure α) : α → ℝ` | `Stein.lean:53` | `noncomputable def llrPmf (P Q : Measure α) : α → ℝ := fun x => Real.log (P.real {x}) - Real.log (Q.real {x})` (under `variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]`) | Qstar 周辺の typicality set 構築の primitive |
| `logLikelihoodRatio` | `logLikelihoodRatio (P Q : Measure α) (Xs : ℕ → Ω → α) (i : ℕ) : Ω → ℝ` | `Stein.lean:61` | `noncomputable def logLikelihoodRatio (P Q : Measure α) (Xs : ℕ → Ω → α) (i : ℕ) : Ω → ℝ := fun ω => llrPmf P Q (Xs i ω)` | n-IID per-letter argument |
| `steinTypicalSet` | `steinTypicalSet (P Q : Measure α) (n : ℕ) (ε : ℝ) : Set (Fin n → α)` | `Stein.lean:257` | `noncomputable def steinTypicalSet (P Q : Measure α) (n : ℕ) (ε : ℝ) : Set (Fin n → α) := {x \| \|((1:ℝ)/n) * ∑ i, llrPmf P Q (x i) - (klDiv P Q).toReal\| < ε}` | Qstar 周りの typicality set template |
| `steinTypicalSet_P_prob_tendsto_one` | `theorem ...` | `Stein.lean:275` | `theorem steinTypicalSet_P_prob_tendsto_one (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hMap : μ.map (Xs 0) = P) (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P)) (hPpos : ∀ x : α, 0 < P.real {x}) (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) : Tendsto (fun n : ℕ => ((Measure.pi (fun _ : Fin n => P)) (steinTypicalSet P Q n ε)).toReal) atTop (𝓝 1)` | typicality set 上の P 質量 → 1 (Type I error 制御の素材) |
| `steinTypicalSet_Q_prob_le` | `theorem ...` | `Stein.lean:341` | `theorem steinTypicalSet_Q_prob_le (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPpos : ∀ x : α, 0 < P.real {x}) (hQpos : ∀ x : α, 0 < Q.real {x}) (n : ℕ) (ε : ℝ) : ((Measure.pi (fun _ : Fin n => Q)) (steinTypicalSet P Q n ε)).toReal ≤ Real.exp (-((n : ℝ) * ((klDiv P Q).toReal - ε)))` | typicality set 上の Q 質量上界 (Qstar に流用) |
| `stein_achievability` | `theorem ...` | `Stein.lean:488` | `theorem stein_achievability (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hMap : μ.map (Xs 0) = P) (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P)) (hPpos : ∀ x : α, 0 < P.real {x}) (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ n : ℕ in atTop, ∃ s : Set (Fin n → α), MeasurableSet s ∧ ((Measure.pi (fun _ : Fin n => P)) sᶜ).toReal ≤ ε ∧ (klDiv P Q).toReal - δ ≤ -((1 : ℝ) / n) * Real.log ((Measure.pi (fun _ : Fin n => Q)) s).toReal` | **Hoeffding tradeoff achievability の template** (Qstar に置き換え + α-level 制約調整で流用) |
| `klDiv_pi_eq_n_smul` | `theorem ...` | `Stein.lean:713` | `theorem klDiv_pi_eq_n_smul (n : ℕ) (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : klDiv (Measure.pi (fun _ : Fin n => P)) (Measure.pi (fun _ : Fin n => Q)) = n • klDiv P Q` | `D(Qstar^n ‖ P_i^n) = n · D(Qstar ‖ P_i)` (Sanov LDP per-Qstar 起動の minimizer 性整理用) |
| `steinBetaSet` (Measure 経路) | `steinBetaSet (P Q : Measure α) (n : ℕ) (ε : ℝ) : Set ℝ` | `Stein.lean:1139` | `noncomputable def steinBetaSet (P Q : Measure α) (n : ℕ) (ε : ℝ) : Set ℝ := { β : ℝ \| ∃ (s : Set (Fin n → α)), MeasurableSet s ∧ ((Measure.pi (fun _ : Fin n => P)) sᶜ).toReal ≤ ε ∧ β = ((Measure.pi (fun _ : Fin n => Q)) s).toReal }` | **Measure 経路の Type II at level ε set** (もし pmf 経路と独立に Measure 形を main 形にするなら、これを Hoeffding の `steinTypeII_at_level` の **direct template** として流用可能。Stein.lean は P, Q が `Measure α` で書かれているので、pmf ↔ Measure bridge が必要) |
| `steinOptimalBeta` (Measure 経路) | `steinOptimalBeta (P Q : Measure α) (n : ℕ) (ε : ℝ) : ℝ` | `Stein.lean:1146` | `noncomputable def steinOptimalBeta (P Q : Measure α) (n : ℕ) (ε : ℝ) : ℝ := sInf (steinBetaSet P Q n ε)` | Measure 経路 optimal Type II (Hoeffding tradeoff の "n-IID 最適化対象" は本質的にこれと同型) |
| `exp_le_steinOptimalBeta` | `lemma ...` | `Stein.lean:1261` | `lemma exp_le_steinOptimalBeta (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPpos : ∀ x : α, 0 < P.real {x}) (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {n : ℕ} (hn : 0 < n) : Real.exp (-((n : ℝ) * ((klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε))))) ≤ steinOptimalBeta P Q n ε` | converse-side 下界 (Hoeffding の Type II tradeoff converse の template: P → Qstar に置き換え) |
| `steinOptimalBeta_log_le_of_converse` | `theorem ...` | `Stein.lean:1286` | `theorem steinOptimalBeta_log_le_of_converse (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPpos : ∀ x : α, 0 < P.real {x}) (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {n : ℕ} (hn : 0 < n) : -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε) ≤ (klDiv P Q).toReal / (1 - ε) + Real.log 2 / ((n : ℝ) * (1 - ε))` | Stein converse の per-`ε` 形 (Hoeffding tradeoff converse の per-Qstar 形に Qstar 置換で流用) |
| `steinOptimalBeta_log_ge_of_achievability` | `theorem ...` | `Stein.lean:1314` | `theorem steinOptimalBeta_log_ge_of_achievability (μ : Measure Ω) [IsProbabilityMeasure μ] (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (hMap : μ.map (Xs 0) = P) (hMapJoint : ∀ n, μ.map (jointRV Xs n) = Measure.pi (fun _ : Fin n => P)) (hPpos : ∀ x : α, 0 < P.real {x}) (hPQ : P ≪ Q) (hQpos : ∀ x : α, 0 < Q.real {x}) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) : ∀ᶠ n : ℕ in atTop, (klDiv P Q).toReal - δ ≤ -((1 : ℝ) / n) * Real.log (steinOptimalBeta P Q n ε)` | Stein achievability の per-`ε` 形 (Hoeffding achievability の per-Qstar 形に Qstar 置換で流用) |
| `stein_lemma` | `theorem ...` | `Stein.lean:1390` | `theorem stein_lemma ...` (sandwich `liminf ≥ K ∧ limsup ≤ K/(1-ε)`) | sandwich 構造のテンプレ (T1-D wrapper の skeleton) |

### E. Mathlib 数論 / 不等式 / 連続性 (兄弟 inventory の F+G+H で既に整理済、再掲)

| 概念 | Mathlib API | file:line | signature (verbatim) | T1-D での扱い |
|---|---|---|---|---|
| `klDiv` (Mathlib) | `klDiv (μ ν : Measure α) : ℝ≥0∞` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` | `noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞ := if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) else ∞` | (Sanov LDP との bridge: `klDivSumForm_eq_toReal_klDiv`) |
| `klFun` (Mathlib) | `klFun (x : ℝ) : ℝ` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:50` | `def klFun (x : ℝ) : ℝ := x * Real.log x + 1 - x` (under no special variable) | `klDivPmf` の core |
| `klFun_one` | `lemma ...` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:59` | `lemma klFun_one : klFun 1 = 0 := by simp [klFun]` | `klDivPmf_self_eq_zero` の核 (既使用) |
| `strictConvexOn_klFun` | `lemma ...` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:62` | `lemma strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun` | `klDivPmf_strictConvexOn_left` の核 |
| `klFun_nonneg` | `lemma ...` | `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:149` | `lemma klFun_nonneg (hx : 0 ≤ x) : 0 ≤ klFun x` | `klDivPmf_nonneg` の核 |
| `convex_stdSimplex` | `theorem ...` | `Mathlib/Analysis/Convex/StdSimplex.lean:42` | `theorem convex_stdSimplex [IsOrderedRing 𝕜] : Convex 𝕜 (stdSimplex 𝕜 ι) := by ...` (under `variable {𝕜 : Type*} {ι : Type*} [Semiring 𝕜] [Fintype ι]`) | constraint set 凸性 (Qstar 一意性で既使用) |
| `isClosed_stdSimplex` | `theorem ...` | `Mathlib/Analysis/Convex/StdSimplex.lean:179` | `theorem isClosed_stdSimplex : IsClosed (stdSimplex 𝕜 ι)` (under `variable {𝕜 : Type*} [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜] {ι : Type*} [Fintype ι]`) | constraint set 閉性 (既使用) |
| `isCompact_stdSimplex` | `theorem ...` | `Mathlib/Analysis/Convex/StdSimplex.lean:187` | `theorem isCompact_stdSimplex [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] : IsCompact (stdSimplex 𝕜 ι) := IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex 𝕜 ι) (stdSimplex_subset_Icc 𝕜)` | constraint set コンパクト性 (既使用) |
| `IsCompact.exists_isMinOn` | `theorem ...` | `Mathlib/Topology/Order/Compact.lean:228` | `theorem IsCompact.exists_isMinOn [ClosedIicTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x` (under `variable {α : Type*} {β : Type*} [TopologicalSpace α] [LinearOrder α] [TopologicalSpace β]`) | Qstar 取り出し (既使用) |
| `IsCompact.exists_sInf_image_eq` | `theorem ...` | `Mathlib/Topology/Order/Compact.lean:417` | `theorem IsCompact.exists_sInf_image_eq [ClosedIicTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, sInf (f '' s) = f x` | `hoeffdingE2 = klDivPmf Qstar P₂` 形での Qstar 取り出し (既使用) |

### F. Asymptotic / log-rate notation (`InformationTheory/InformationTheory/Asymptotic.lean`)

| 概念 | API | file:line | signature (verbatim) | T1-D での扱い |
|---|---|---|---|---|
| `DotEq` notation | `DotEq (a b : ℕ → ℝ) : Prop` | `Asymptotic.lean:43` | `def DotEq (a b : ℕ → ℝ) : Prop := (fun n : ℕ => Real.log (a n) - Real.log (b n)) =o[atTop] (fun n : ℕ => (n : ℝ))` | tradeoff `β_n(α) ≐ exp(-n · E₂(α))` の corollary (Tendsto wrapper の "≐" 形派生) |
| `dotEq_iff_tendsto_log_div` | `lemma ...` | `Asymptotic.lean:116` | `lemma dotEq_iff_tendsto_log_div (a b : ℕ → ℝ) (hPos : ∀ n, 0 < a n ∧ 0 < b n) : a ≐ b ↔ Tendsto (fun n : ℕ => (1 / (n : ℝ)) * Real.log (a n / b n)) atTop (𝓝 0)` | Tendsto ⇔ ≐ 往復 |
| `exp_decay_N_of_pos` | `theorem ...` | `Asymptotic.lean:148` | `theorem exp_decay_N_of_pos {g ε' : ℝ} (hg : 0 < g) (hε' : 0 < ε') : ∃ N : ℕ, ∀ n ≥ N, Real.exp (-(n : ℝ) * g) < ε'` | rate-extraction wrapper |

### G. Liminf/limsup machinery (Mathlib)

| 概念 | Mathlib API | file:line | signature (verbatim) | T1-D での扱い |
|---|---|---|---|---|
| `Filter.le_liminf_of_le` | `theorem ...` | `Mathlib/Order/LiminfLimsup.lean:145` | `theorem Filter.le_liminf_of_le {f : Filter β} {u : β → α} {a} (h₁ : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault) (h₂ : ∀ᶠ n in f, a ≤ u n) : a ≤ Filter.liminf u f` (under `variable {α β : Type*} [ConditionallyCompleteLinearOrder α]`) | achievability (`liminf ≥ E₂(α)`) (既に Chernoff.lean Phase C で使用) |
| `IsBoundedUnder.isCoboundedUnder_ge` | `theorem ...` | `Mathlib/Order/Filter/IsBounded.lean:233` | `theorem IsBoundedUnder.isCoboundedUnder_ge {u : γ → α} {l : Filter γ} [Preorder α] [NeBot l] (h : l.IsBoundedUnder (· ≤ ·) u) : l.IsCoboundedUnder (· ≥ ·) u := h.isCoboundedUnder_flip` | cobounded 仮定の解消 (既に Chernoff.lean:1018 で使用) |
| `tendsto_of_le_liminf_of_limsup_le` | `theorem ...` | `Mathlib/Topology/Order/LiminfLimsup.lean` (検索: `tendsto_of_le_liminf_of_limsup_le`) | (省略) sandwich `liminf ≥ a ∧ limsup ≤ a ⇒ Tendsto _ atTop (𝓝 a)` | Tendsto sandwich wrapper |

---

## 重要な前提条件 (事故が起きやすい lemma の type-class verbatim)

兄弟 inventory `chernoff-hoeffding-mathlib-inventory.md` §「重要な前提条件」と完全に重複するので大半は省略。T1-D **固有** の追加注意:

### `sanov_ldp_equality` の前提 verbatim (SanovLDPEquality.lean:1243)

```
(Q : Measure α) [IsProbabilityMeasure Q]
(hQpos : ∀ a : α, 0 < Q.real {a})
(P : α → ℝ) (hP_prob : (∑ a, P a) = 1)
(hP_full : ∀ a, 0 < P a)
(E : ∀ n, Finset (TypeCountIndex α n))
(h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n)
(h_minimizer : ∀ n, ∀ c ∈ E n,
  klDivSumForm_ofVec P (fun a => Q.real {a})
    ≤ klDivIndex (fun a => (c a : ℕ)) n Q)
```

**T1-D で `P := Qstar`, `Q := P₂` (Measure α) として起動する想定**。

- `[IsProbabilityMeasure Q]` → `P₂` を `α → ℝ` の pmf 形で持っているので **pmf → Measure** bridge (`Q := PMF.toMeasure Qstar` の類) が必要
- `hQpos : ∀ a, 0 < Q.real {a}` → P₂ が full-support であることから自動
- `(P : α → ℝ)` は **pmf 形のまま** (`Qstar : α → ℝ`)
- `h_in_E` の `roundedTypeIndex Qstar n ∈ E n` → 任意の `Qstar` で成り立つように `E n := {roundedTypeIndex Qstar n}` (singleton) を取れば trivial
- `h_minimizer` → ここが Hoeffding 固有の hot spot:

  **問題**: `klDivSumForm_ofVec Qstar (P₂.real ∘ singleton) ≤ klDivIndex (c/n) n P₂` を **per-`c`** で示す必要がある。`c ∈ E n` を singleton `{roundedTypeIndex Qstar n}` に取れば `c/n` は Qstar (rounding誤差付き) なので近似的に成立、ただし `≤` の向きで `Qstar` が **`P₂` への射影として最小値**である必要があるが、Hoeffding の Qstar は `klDivPmf · P₁ ≤ alpha` 制約下で `klDivPmf · P₂` を最小化する点で、これは **`P₂` への直接 Csiszar projection ではない** (制約付き)。
  → `csiszar_pythagoras_inequality` (CsiszarProjection.lean:449) で Qstar が `K` 内の Csiszar projection であることを使い、**Pythagoras** `klDivPmf P P₂ ≥ klDivPmf P Qstar + klDivPmf Qstar P₂` (`P ∈ K`) を立てて、`E n` を **`K` の近傍 type の和** に取り直すことで minimizer 仮定を整える、というのが Cover-Thomas 11.7 の議論。

→ **危険箇所 #1**: Sanov LDP per-Qstar 起動は **「`E n := K` 内の全 type」** の形になり、`h_minimizer` 仮定は `csiszar_pythagoras_inequality` 経由でしか出ない。**T1-B Chernoff converse で同じ問題を defer した撤退ライン L-S1 が本 plan でも継続発動** (兄弟 plan 判断ログ #8 参照)。

### `klDivPmf` ↔ `klDivSumForm_ofVec` bridge

両者は **同じ式** (`∑ a, P a · (log P a - log Q a)`) を計算しているが:

- `klDivPmf (P Q : α → ℝ) : ℝ := ∑ a, Q a * klFun (P a / Q a)` (Mathlib `klFun` 形, `CsiszarProjection.lean:55`)
- `klDivSumForm_ofVec (p q : α → ℝ) : ℝ := ∑ a, p a * (log (p a) - log (q a))` (sum-form, `KLDivContinuous.lean:31`)

→ `klDivPmf_eq_log_diff_sum` (CsiszarProjection.lean:231) が両者の互換を取る (`P, Q` 共に prob + full support 下で `klDivPmf P Q = klDivSumForm_ofVec P Q`). **T1-D で Sanov LDP 起動時の `klDivSumForm_ofVec` を `klDivPmf` 形で書き直す**のはこの bridge 1 本でクリア (~5 行)。

### `pmf ↔ Measure α` bridge

Sanov LDP `Q : Measure α` を要求するが、T1-D の本体は `P₁ P₂ : α → ℝ` (pmf 形)。Mathlib `PMF.toMeasure` 経路:

- `PMF.toMeasure : Measure α` (`Mathlib/Probability/ProbabilityMassFunction/Basic.lean:213`)
- `PMF.toMeasure_apply_eq_toMeasure_apply (p : PMF α) (s : Set α) (h : MeasurableSet s) : p.toMeasure s = ∑' x ∈ s, p x` (Mathlib 探索要)

→ **小型 helper** `pmfToMeasure (P : α → ℝ) (hP_prob : ∑ a, P a = 1) (hP_nn : ∀ a, 0 ≤ P a) : Measure α := Measure.sum (fun a => (P a).toNNReal • Measure.dirac a)` または `PMF.ofFintype` 経由で 1-2 補題で取れる (~10-20 行)。**新規撤退ライン候補** (Risk table 参照): この bridge plumbing が 50 行を超えたら全 plan を pmf 形 n-IID で書き直す (Sanov LDP を pmf 経路に乗せる helper を別 plan で書く)。

---

## 自作が必要な要素

優先度順、推奨実装、工数感、落とし穴。

### 自作 1 (核): `steinTypeII_at_level_pmf` の pmf 形定義 + 基本性質

**推奨実装** (Mathlib-shape driven; `steinBetaSet` Measure 経路の **pmf-mirror**):

```lean
/-- n-IID Type II error of the optimal level-`alpha` test, pmf 形.
The Type I error of a (pmf 形) test `s : Finset (Fin n → α)` (the "rejection region") at
sample `x` is `P₁^n(s) = ∑_{x ∈ s} ∏ i, P₁ (x i)` (probability of rejecting `H_0`). The
Type II error is `P₂^n(sᶜ) = 1 - ∑_{x ∈ s} ∏ i, P₂ (x i)` (probability of failing to
reject `H_1`). Convention: `steinBetaSet` (Measure 経路) defines β as
`P₂^n s` (test `s` = "accept H₀") with Type I `P₁^n sᶜ ≤ alpha`. We follow the same
convention. -/
noncomputable def steinBetaSet_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : Set ℝ :=
  { β : ℝ | ∃ (s : Finset (Fin n → α)),
      (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha ∧
      β = ∑ x ∈ s, ∏ i, P₂ (x i) }

noncomputable def steinTypeII_at_level_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : ℝ :=
  sInf (steinBetaSet_pmf P₁ P₂ n alpha)

/-- `1 ∈ steinBetaSet_pmf` (taking `s := univ`). -/
lemma one_mem_steinBetaSet_pmf (P₁ P₂ : α → ℝ) (hP₂_sum : ∑ a, P₂ a = 1) (n : ℕ)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) : (1 : ℝ) ∈ steinBetaSet_pmf P₁ P₂ n alpha

/-- `steinBetaSet_pmf` is bounded below by 0. -/
lemma steinBetaSet_pmf_bddBelow (P₁ P₂ : α → ℝ) (hP₂_nn : ∀ a, 0 ≤ P₂ a) (n : ℕ)
    (alpha : ℝ) : BddBelow (steinBetaSet_pmf P₁ P₂ n alpha)

/-- `steinTypeII_at_level_pmf P₁ P₂ n alpha ≥ 0`. -/
lemma steinTypeII_at_level_pmf_nonneg ...
```

**戦略選択の理由** (Mathlib-shape driven, CLAUDE.md §「Mathlib-shape-driven Definitions」):
- `steinBetaSet` (Measure 経路, `Stein.lean:1139`) の **構造をそのまま pmf 形に転写** すれば、Stein.lean の per-ε achievability/converse template が **Qstar 置換だけで** 流用できる
- `chernoffInfo` を pmf 経路で publish した既存 Chernoff.lean (1066 行) と signature が揃う

**工数感**: 定義 + 基本性質 (positivity, ≤ 1, 非空, bddBelow) ~40 行 + `pmfToMeasure` bridge ~20 行 = **~60 行**。

**落とし穴**:
1. **Finset vs Set 選択**: `s : Finset (Fin n → α)` で書くと `Finset.sum` で sum が直接計算できる (有限なので)、`s : Set (Fin n → α)` だと `MeasurableSet s` 仮定が要る (但し finite α なので automatic via DiscreteMeasurableSpace)。`Finset` で書くのが pmf 経路の流儀。
2. **Convention**: Stein.lean `steinBetaSet` は `β := P₂^n s` (test = "accept H₀") かつ `P₁^n sᶜ ≤ ε` (Type I = "reject H₀ when H₀ true")。Cover-Thomas 11.7 は `s := acceptance region` と `s := rejection region` で揺れる。**統一して `s = acceptance region for H₀`** (Stein.lean に合わせる) のが事故が少ない。
3. **Measure 経路へ吸い上げる別経路**: もし pmf 形を直接書くのが煩雑になったら、`Qstar` を `PMF.toMeasure` で Measure に lift して **Stein.lean の Measure 経路をそのまま流用** する。これは「自作 1 の pmf 形 vs 自作 1' の Measure 形」のスコープ判定なので、Phase 0 終了時の判断 (judgement log) で確定する。

### 自作 2 (本命): Qstar minimizer 性整理 (Sanov LDP 前提準備)

**推奨実装**:

```lean
/-- Qstar の **Sanov LDP per-Qstar 起動の minimizer 仮定** 整理. 
Csiszar Pythagoras (constraint set K is convex) を経由して
`E_n := {c : TypeCountIndex α n | (c/n : α → ℝ) ∈ K}` に対し
`klDivSumForm_ofVec Qstar (P₂.real ∘ singleton) ≤ klDivIndex c n P₂_meas`
を満たすことを示す. -/
lemma hoeffding_sanov_minimizer
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha)
    (P₂_meas : Measure α) [IsProbabilityMeasure P₂_meas]
    (h_P₂_meas : ∀ a, P₂_meas.real {a} = P₂ a)
    {Qstar : α → ℝ}
    (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
    (hQs_pos : ∀ a, 0 < Qstar a)
    (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂)
    (n : ℕ) (c : α → ℕ) (hc_in_K : (fun a => (c a : ℝ) / n) ∈ hoeffdingConstraintSet P₁ alpha)
    (hc_pos : ∀ a, 0 < (c a : ℝ)) :
    klDivSumForm_ofVec Qstar (fun a => P₂_meas.real {a})
      ≤ klDivIndex c n P₂_meas := by
  sorry
```

**戦略**: 
1. `hQs_min` + `hoeffdingE2_attained` の Qstar は `IsMinOn (fun P => klDivPmf P P₂) K Qstar`
2. `csiszar_pythagoras_inequality` を適用 (`K := hoeffdingConstraintSet P₁ alpha`, `Q := P₂`, `Qstar := Qstar`, `P := (c/n : α → ℝ)`):
   `klDivPmf (c/n) P₂ ≥ klDivPmf (c/n) Qstar + klDivPmf Qstar P₂`
3. `klDivPmf (c/n) P₂ = klDivIndex c n P₂_meas` (sum-form bridge)
4. `klDivPmf Qstar P₂ = klDivSumForm_ofVec Qstar (P₂.real ∘ singleton)` (sum-form bridge)
5. `klDivPmf (c/n) Qstar ≥ 0` (`klDivPmf_nonneg`)
6. 合成で `klDivSumForm_ofVec Qstar (P₂_meas.real ∘ ·) ≤ klDivIndex c n P₂_meas`

**工数感**: ~50-70 行 (Pythagoras 適用 + sum-form bridges + nonneg 足し算)。

**落とし穴**:
1. `hoeffdingConstraintSet P₁ alpha` の凸性は **`convex_stdSimplex` (Mathlib) + `klDivPmf · P₁` の凸性 (`klDivPmf_strictConvexOn_left.convexOn`)** で取れる。Chernoff.lean:585 (hoeffdingE2_unique 内) で既に local に展開している (~10 行) ので、その helper を **公開 lemma `hoeffdingConstraintSet_convex`** に切り出すと再利用しやすい (~5 行追加)。
2. `csiszar_pythagoras_inequality` は `hQs_pos : ∀ a, 0 < Qstar a` を要求する。Qstar は `hoeffdingE2_attained` から取り出すが、`Qstar a > 0` は **自動では出ない** (`Qstar ∈ stdSimplex` だけだと `Qstar a ≥ 0`)。**「Qstar の full-support 性」を別補題で示す**必要がある (KL の strict convexity + `P₁, P₂ > 0` から、Qstar が 0 を取る atom があれば `klDivPmf Qstar P₂` が無限大に発散 or `klDivPmf · P₂` の最小値ではなくなる、という反転論証で取れる ~15-20 行)。

### 自作 3 (achievability side): Sanov LDP per-Qstar 起動 + acceptance region 構築

**推奨実装**:

```lean
/-- Hoeffding tradeoff achievability: there exists an acceptance region
`s : Finset (Fin n → α)` with Type I error ≤ alpha and Type II error ≤ exp(-n · (E₂(α) - δ)).
Strategy: take `s := ⋃_{c ∈ K近傍} typeClassByCount c` and use sanov_ldp_equality. -/
theorem hoeffding_tradeoff_achievability
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) (h_alpha_le : alpha ≤ klDivPmf P₁ P₂)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ s : Finset (Fin n → α),
      (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha ∧
      hoeffdingE2 P₁ P₂ alpha - δ ≤
        -((1 : ℝ) / n) * Real.log (∑ x ∈ s, ∏ i, P₂ (x i)) := by
  sorry
```

**戦略**:
1. `Qstar := classical.some (hoeffdingE2_attained ...)` (constraint set 内 minimizer)
2. **acceptance region** := `Finset.image (fun c => typeClassByCount (c/n)) E_n^*` where `E_n^* := {c ∈ K の近傍 type}` (Qstar から rounded type で生成、`roundedTypeIndex Qstar n`)
3. **Type I 制御** (`P₁^n s ≥ 1 - alpha`): Sanov LDP for `P := P₁, Q := P₁`、自動的に `(c/n) ∈ K` の type に集中、`P₁^n (acceptance) → 1` (Stein typicality 様)
4. **Type II 上限** (`P₂^n s ≤ exp(-n · E₂(α))`): Sanov LDP `P := Qstar, Q := P₂` → `-(1/n) log P₂^n(acceptance) → E₂(α)`
5. eventually n で δ-loose 達成

**工数感**: ~120-150 行 (acceptance region 構築 + per-Qstar Sanov 起動 + Type I 制御 + δ-loose 化)。

**落とし穴**:
1. **Type I 制御の Sanov LDP は P₁ -> P₁ 自己呼び出し**だが、これは `klDivPmf P₁ P₁ = 0` から typeClass が `P₁` 周りに集中するという trivial な statement (大数の法則の AEP 版)。Mathlib にない可能性大、自前 ~30-40 行で補助補題化 (`p_n_typeclass_tendsto_one`)。
2. **acceptance region の measurability**: `Finset (Fin n → α)` で書けば `Set (Fin n → α) := {x | x ∈ acceptance}` の measurability は自動 (`Set.toFinite _).measurableSet`)。**pmf 形 vs Measure 形の切り替えタイミング**に注意。
3. **`Qstar` の存在仮定 + full-support 性**は自作 2 から (`hoeffdingE2_attained` + 別補題)。

### 自作 4 (converse side): Type II 下界 via typicality + Pythagoras

**推奨実装**:

```lean
/-- Hoeffding tradeoff converse: for any test with Type I ≤ alpha,
Type II ≥ exp(-n · (E₂(α) + δ)). 
Strategy: per-test, the typicality set around Qstar covers a positive fraction of P₁^n,
and on it P₂^n is upper-bounded by exp(-n · E₂(α)). Pythagoras forces Qstar to be the
"hardest to distinguish" Q in K. -/
theorem hoeffding_tradeoff_converse
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : Finset (Fin n → α)),
      (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha →
      -((1 : ℝ) / n) * Real.log (∑ x ∈ s, ∏ i, P₂ (x i)) ≤ hoeffdingE2 P₁ P₂ alpha + δ
```

**戦略**:
1. Stein.lean `steinTypicalSet_Q_prob_le` (Stein.lean:341) の **per-Qstar 流用**: `steinTypicalSet Qstar P₂ n ε` 上で `P₂^n ≤ exp(-n · (klDiv Qstar P₂ - ε))` (Qstar = P, P₂ = Q として読み替え)
2. typicality set + acceptance region の **重なり区域** に集中する type は Csiszar Pythagoras で `klDivPmf · P₂ ≥ klDivPmf Qstar P₂` を強制 → 任意の test で Type II 下界
3. ε → 0 で `hoeffdingE2 = klDiv Qstar P₂`

**工数感**: ~80-100 行 (Stein converse template 流用 + Pythagoras 適用)。

**落とし穴**:
1. `steinTypicalSet_Q_prob_le` は **Measure α 経路**。pmf ↔ Measure bridge を Phase 開始時に整地しないと `Qstar : α → ℝ` を `Qstar_meas : Measure α` に lift する step が散らかる。
2. **Stein converse の `(klDiv P Q).toReal / (1 - ε)` の `1 - ε` 因子** (Stein.lean:1286) が `hoeffdingE2` への converse 不等式に **bias** を与える可能性。strong Stein (`StrongStein.lean:498`, strict Tendsto 形) を流用すれば `1 - ε` 因子なしで通せる。

### 自作 5 (wrapper): tradeoff sandwich

**推奨実装**:

```lean
/-- **Hoeffding tradeoff lemma** (T1-D 主定理). -/
theorem hoeffding_tradeoff
    (P₁ P₂ : α → ℝ) [Nonempty α]
    (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂) :
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  -- liminf ≥ E₂(α): from achievability (自作 3)
  · sorry
  -- limsup ≤ E₂(α): from converse (自作 4)
  · sorry
```

**工数感**: ~40-50 行 (sandwich の上下を切り出して呼ぶだけ、ただし `IsCoboundedUnder` 仮定の解消で 10 行程度 plumbing)。

### 自作 6 (optional, 補助): `hoeffdingConstraintSet_convex` (公開 lemma 化)

既に Chernoff.lean:585 `hoeffdingE2_unique` 内部で実質的に展開しているが、本 plan で **公開 lemma** として切り出すと自作 2 で再利用できる。

```lean
lemma hoeffdingConstraintSet_convex
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (alpha : ℝ) :
    Convex ℝ (hoeffdingConstraintSet P₁ alpha) := by
  -- K = stdSimplex ∩ {Q | klDivPmf Q P₁ ≤ alpha}, both convex.
  sorry
```

**工数感**: ~10 行。

---

## 撤退ラインへの距離

roadmap 既存撤退ラインは `docs/textbook-roadmap.md` §T1-D (line 144-150) の規模 ~200-300 行。
兄弟 plan の撤退ライン L-S1 (T1-D Tendsto 形を T1-B converse と共有 plumbing で defer) は **既に発動済**。

### 判定

- **L-S1 発動継続**: 本 plan は L-S1 を正式 import (兄弟 plan 判断ログ #8 参照)。Phase A-D の publish 済成果 (`hoeffdingE2_attained` / `hoeffdingE2_unique` / `hoeffdingE2_nonneg`) を **保持** したまま、Tendsto 形のみを T1-D 単独 plan として publish する
- Sanov LDP equality (`sanov_ldp_equality`) + Stein achievability template + Csiszar projection + Pythagoras が **全て既存** ⇒ 自作量は ~250-350 行 (兄弟 plan 見積もり「T1-D 単独 200-300 行」と整合、ただし pmf ↔ Measure bridge 込みで +50 行)
- 規模見積もり: **自作 1〜5 合計 ~270-370 行** + skeleton/imports ~40 行 = **~310-410 行**

### 新規撤退ライン (本 plan 固有, 提案)

以下を新規撤退ラインとして追加すべき:

- **L-H1**: **pmf ↔ Measure bridge plumbing が 50 行を超えた場合**
  - 縮退案: pmf 形 `steinTypeII_at_level_pmf` を **直接** 自前 typicality set + 自前 Sanov LDP 経路で書く (Sanov LDP を pmf 経路に乗せる helper を別 plan で書く)。**pmf 形 Sanov LDP** は `SanovLDPEquality.lean` の Measure 形と本質的に同型なので、自前 reimplementation は不要だが、bridge を介さず直接 pmf 形 で `klDivPmf` を `klDivIndex` 形に reshape する経路に切り替え

- **L-H2**: **Csiszar Pythagoras 経由の minimizer 仮定立証が 80 行を超えた場合**
  - 縮退案: `csiszar_pythagoras_inequality` を直接呼ばず、Qstar minimizer 性を `klDivPmf_strictConvexOn_left` + `csiszar_projection_unique` で local に再構成 (Pythagoras 不等式の弱形だけで通せる場合がある)

- **L-H3**: **Stein converse template (`steinTypicalSet_Q_prob_le`) の Qstar 流用で `1 - ε` 因子の bias が `hoeffdingE2` への上界に伝播する場合**
  - 縮退案: Strong Stein (`StrongStein.lean:498` `stein_strong_lemma`, strict Tendsto 形) を直接流用、または `1 - ε` 因子を `ε → 0` 極限で吸収する追加 ε-外側ループを実装

- **L-H4** (兄弟 plan L-S1 と区別する scope-shrinkage ライン): **本 plan で「Tendsto 形」が組めない場合、`hoeffdingE2` の `variational expression` のみ publish**
  - 縮退案: `hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂` を **definition + uniqueness** で書き切り、`Tendsto` 形は次々セッションに defer。本 plan は `hoeffding-tradeoff-variational-plan.md` として close

---

## 着手 skeleton

`InformationTheory/Shannon/HoeffdingTradeoff.lean` (T1-D 単独 publish):

```lean
import InformationTheory.Shannon.Chernoff
import InformationTheory.Shannon.Stein
import InformationTheory.Shannon.StrongStein
import InformationTheory.Shannon.SanovLDPEquality
import InformationTheory.Shannon.CsiszarProjection
import InformationTheory.Shannon.KLDivContinuous
import InformationTheory.InformationTheory.Asymptotic
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Order.Compact

/-!
# T1-D Hoeffding tradeoff exponent (Tendsto 形主定理)

Cover-Thomas Theorem 11.7.x の **n-IID Type II at Type I level `alpha` の指数収束**:

```
-(1/n) log β_n(alpha) → hoeffdingE2 P₁ P₂ alpha
```

`hoeffdingE2`/`hoeffdingE2_attained`/`hoeffdingE2_unique` は **既に** `InformationTheory/Shannon/Chernoff.lean`
(Tier 0 + Phase D 残) で publish 済。本ファイルは **Tendsto 形** (Sanov LDP per-Qstar + Stein converse
template Qstar 流用) のみを publish する。

## 主定理

* `steinTypeII_at_level_pmf P₁ P₂ n alpha` — n-IID Type II error at Type I level alpha (pmf 形)
* `hoeffding_tradeoff_achievability` — `liminf ≥ hoeffdingE2`
* `hoeffding_tradeoff_converse` — `limsup ≤ hoeffdingE2`
* `hoeffding_tradeoff` — sandwich Tendsto 形

## 設計 (Mathlib-shape driven)

* `steinBetaSet_pmf` を `Stein.steinBetaSet` (Measure 経路) の pmf 形 mirror で定義
  → Stein.lean の per-ε template を Qstar 置換でそのまま流用可能
* Sanov LDP per-Qstar (`sanov_ldp_equality`) を `Q := P₂_meas` (Measure α への pmf lift) で起動
* Csiszar Pythagoras (`csiszar_pythagoras_inequality`) で Qstar の minimizer 性整理

## 撤退ライン

* L-S1 適用 (T1-B converse と共有 plumbing で defer されていた T1-D Tendsto 形を本 plan で publish)
* L-H1〜L-H4 (新規) は本ファイル §撤退ライン参照
-/

namespace InformationTheory.Shannon.HoeffdingTradeoff

set_option linter.unusedSectionVars false

open Set Real InformationTheory Filter MeasureTheory
open InformationTheory.Shannon.Chernoff InformationTheory.Shannon.CsiszarProjection
open InformationTheory.Shannon
open scoped BigOperators Topology ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]

/-! ## Phase A — pmf ↔ Measure bridge (helper) -/

/-- pmf 形 `P : α → ℝ` を Measure α に lift する.
`PMF.ofFintype` 経由で `PMF.toMeasure` を取ると `IsProbabilityMeasure` が自動付与される. -/
noncomputable def pmfToMeasure (P : α → ℝ)
    (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) : Measure α := by
  sorry  -- PMF.ofFintype + PMF.toMeasure

lemma pmfToMeasure_isProbabilityMeasure
    (P : α → ℝ) (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) :
    IsProbabilityMeasure (pmfToMeasure P hP_nn hP_sum) := by
  sorry

lemma pmfToMeasure_real_singleton
    (P : α → ℝ) (hP_nn : ∀ a, 0 ≤ P a) (hP_sum : ∑ a, P a = 1) (a : α) :
    (pmfToMeasure P hP_nn hP_sum).real {a} = P a := by
  sorry

lemma pmfToMeasure_pos
    (P : α → ℝ) (hP_pos : ∀ a, 0 < P a) (hP_sum : ∑ a, P a = 1) (a : α) :
    0 < (pmfToMeasure P (fun a => (hP_pos a).le) hP_sum).real {a} := by
  sorry

/-! ## Phase B — `steinTypeII_at_level_pmf` 定義 + 基本性質 -/

/-- n-IID Type II error set (pmf 形). -/
noncomputable def steinBetaSet_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : Set ℝ :=
  { β : ℝ | ∃ (s : Finset (Fin n → α)),
      (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha ∧
      β = ∑ x ∈ s, ∏ i, P₂ (x i) }

/-- Optimal Type II error (pmf 形). -/
noncomputable def steinTypeII_at_level_pmf (P₁ P₂ : α → ℝ) (n : ℕ) (alpha : ℝ) : ℝ :=
  sInf (steinBetaSet_pmf P₁ P₂ n alpha)

lemma one_mem_steinBetaSet_pmf
    (P₁ P₂ : α → ℝ) (hP₂_sum : ∑ a, P₂ a = 1)
    (n : ℕ) (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) :
    (1 : ℝ) ∈ steinBetaSet_pmf P₁ P₂ n alpha := by
  sorry

lemma steinBetaSet_pmf_bddBelow
    (P₁ P₂ : α → ℝ) (hP₂_nn : ∀ a, 0 ≤ P₂ a) (n : ℕ) (alpha : ℝ) :
    BddBelow (steinBetaSet_pmf P₁ P₂ n alpha) := by
  sorry

lemma steinTypeII_at_level_pmf_nonneg
    (P₁ P₂ : α → ℝ) (hP₂_nn : ∀ a, 0 ≤ P₂ a) (n : ℕ) (alpha : ℝ) :
    0 ≤ steinTypeII_at_level_pmf P₁ P₂ n alpha := by
  sorry

lemma steinTypeII_at_level_pmf_pos
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (n : ℕ) (hn : 0 < n) (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt_1 : alpha < 1) :
    0 < steinTypeII_at_level_pmf P₁ P₂ n alpha := by
  sorry  -- need: any test with Type I ≤ alpha < 1 has Type II > 0 (full-support Qstar)

/-! ## Phase C — Hoeffding constraint set 凸性 + Qstar full-support -/

lemma hoeffdingConstraintSet_convex
    (P₁ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (alpha : ℝ) :
    Convex ℝ (hoeffdingConstraintSet P₁ alpha) := by
  sorry  -- klDivPmf · P₁ is convex + stdSimplex is convex ⇒ intersection convex

lemma hoeffdingE2_minimizer_full_support
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂)
    {Qstar : α → ℝ}
    (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
    (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂) :
    ∀ a, 0 < Qstar a := by
  sorry  -- KL strict convexity + non-trivial alpha ⇒ Qstar full-support

/-! ## Phase D — Sanov LDP per-Qstar 起動 (minimizer 仮定整理) -/

lemma hoeffding_sanov_minimizer
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha)
    {Qstar : α → ℝ}
    (hQs_mem : Qstar ∈ hoeffdingConstraintSet P₁ alpha)
    (hQs_pos : ∀ a, 0 < Qstar a)
    (hQs_min : hoeffdingE2 P₁ P₂ alpha = klDivPmf Qstar P₂)
    (n : ℕ) (c : α → ℕ)
    (hc_in_K : (fun a => (c a : ℝ) / n) ∈ hoeffdingConstraintSet P₁ alpha)
    (hc_pos : ∀ a, 0 < (c a : ℝ)) :
    klDivSumForm_ofVec Qstar (fun a => P₂ a)
      ≤ klDivIndex c n (pmfToMeasure P₂ (fun a => (hP₂_pos a).le) hP₂_sum) := by
  sorry  -- Pythagoras + klDivPmf ↔ klDivSumForm bridges

/-! ## Phase E — Hoeffding tradeoff achievability (Sanov LDP per-Qstar + acceptance region) -/

theorem hoeffding_tradeoff_achievability
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ s : Finset (Fin n → α),
      (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha ∧
      hoeffdingE2 P₁ P₂ alpha - δ ≤
        -((1 : ℝ) / n) * Real.log (∑ x ∈ s, ∏ i, P₂ (x i)) := by
  sorry

/-! ## Phase F — Hoeffding tradeoff converse (Stein typicality template + Pythagoras) -/

theorem hoeffding_tradeoff_converse
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    (alpha : ℝ) (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ (s : Finset (Fin n → α)),
      (1 - ∑ x ∈ s, ∏ i, P₁ (x i)) ≤ alpha →
      -((1 : ℝ) / n) * Real.log (∑ x ∈ s, ∏ i, P₂ (x i))
        ≤ hoeffdingE2 P₁ P₂ alpha + δ := by
  sorry

/-! ## Phase G — 主定理 wrapper (sandwich Tendsto) -/

theorem hoeffding_tradeoff
    (P₁ P₂ : α → ℝ) (hP₁_pos : ∀ a, 0 < P₁ a) (hP₂_pos : ∀ a, 0 < P₂ a)
    (hP₁_sum : ∑ a, P₁ a = 1) (hP₂_sum : ∑ a, P₂ a = 1)
    {alpha : ℝ} (h_alpha_nn : 0 ≤ alpha) (h_alpha_lt : alpha < klDivPmf P₁ P₂) :
    Tendsto (fun n : ℕ => -((1:ℝ)/n) * Real.log (steinTypeII_at_level_pmf P₁ P₂ n alpha))
      atTop (𝓝 (hoeffdingE2 P₁ P₂ alpha)) := by
  sorry

end InformationTheory.Shannon.HoeffdingTradeoff
```

(80-150 行 skeleton: import + namespace + Phase A-G 各 sorry stub。実装で 250-350 行に膨らむ想定。)

---

## 「Phase X で使う API のうち N% が Mathlib に既存」

分母 (T1-D 主証明 path で実際に使う API): 約 30 項目

- 既存 publish 済 `hoeffdingE2`/`hoeffdingConstraintSet` family (8 項目, Chernoff.lean)
- Csiszar projection 系 (7 項目, CsiszarProjection.lean)
- Sanov LDP equality + plumbing (6 項目, SanovLDPEquality.lean + SanovLDP.lean + Sanov.lean + KLDivContinuous.lean)
- Stein typicality + Type II beta (5 項目, Stein.lean + StrongStein.lean)
- Mathlib (KLFun, ConjExponents, MeanInequalities, Compact, StdSimplex, ConvexFunctions, LiminfLimsup) (4 項目)

分子 (既存): 30 項目

→ **既存率 100%** (実体ベース)。Hoeffding tradeoff Tendsto 形のために **新たに必要な top-level def/theorem は 4-5 種** (`steinTypeII_at_level_pmf` / `hoeffding_sanov_minimizer` / `hoeffding_tradeoff_achievability` / `hoeffding_tradeoff_converse` / `hoeffding_tradeoff`)。

---

## 主要発見 (危険な点)

### 危険 1 (最重要): `csiszar_pythagoras_inequality` の `hQs_pos : ∀ a, 0 < Qstar a` 要件

**`csiszar_pythagoras_inequality`** (`CsiszarProjection.lean:449`) は **Qstar の full-support 性 (`∀ a, 0 < Qstar a`) を verbatim で要求** する。`hoeffdingE2_attained` (`Chernoff.lean:310`) から取り出される `Qstar ∈ hoeffdingConstraintSet P₁ alpha` は `Qstar ∈ stdSimplex` (= `∀ a, 0 ≤ Qstar a`) しか保証しない。

→ `hoeffdingE2_minimizer_full_support` (自作補題, ~15-20 行) を **新規** に書く必要あり: 「Qstar が一部 atom で 0 を取ると `klDivPmf Qstar P₂` が無限大 or 別の minimizer に劣後する」反転論証で full-support 性を導出。これがないと自作 2 / 3 / 4 全て破綻。

### 危険 2: Sanov LDP per-Qstar 起動の `E_n` 構成と `h_in_E` 仮定

`sanov_ldp_equality` (`SanovLDPEquality.lean:1243`) の `h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P n ∈ E n` は、`E_n` を **Qstar の rounded type を含む集合** に取ることで自動的に満たすが、acceptance region としては **Qstar の近傍 type **全部** を `E_n` に含める必要**がある (Type I 制御で `P₁^n(⋃_{c ∈ E_n} typeClassByCount c) → 1` を出すため)。

→ **`E_n := {c : TypeCountIndex α n | (c/n) ∈ hoeffdingConstraintSet P₁ alpha}`** で取るのが標準だが、ここで `(c/n) ∈ K` の Decidable 性 + Finset 化 + Sanov LDP の `minimizer` 仮定の per-`c` 整理が **plumbing 30-50 行** かかる。これが本 plan で最も「自前で書く部分」が膨らみやすい場所。

### 危険 3 (構造的): pmf ↔ Measure α bridge の方針判定 (Phase 開始時に確定)

`hoeffdingE2` は `α → ℝ` pmf 形で書かれているが、`sanov_ldp_equality` / `steinTypicalSet_Q_prob_le` / `klDivIndex` は **`Measure α` 形を要求** する。bridge を:
1. **bridge を全部書く** (`pmfToMeasure` + `pmfToMeasure_real_singleton` + `klDivPmf_eq_klDivSumForm_via_meas` ~30-40 行 + 各補題に lift)、
2. **pmf 形で全部書く** (`steinTypicalSet_pmf` 自作 + Sanov LDP pmf 経路の helper ~80-120 行)、
3. **Sanov LDP のみ Measure 経路に上げ、それ以外は pmf** (中間案)

のどれを取るかで本 plan の規模感が ±100 行変動する。**Phase 0 終了時の judgement log でいずれかに確定する**のが安全。

### 危険 4: Stein converse template の `1 - ε` 因子

`steinOptimalBeta_log_le_of_converse` (`Stein.lean:1286`) の上界は **`(klDiv P Q).toReal / (1 - ε)` 形** ('ε' は Type I level の Stein 内のパラメータ、Hoeffding の `alpha` ではない)。Hoeffding tradeoff の converse で `limsup ≤ E₂(α) + δ` を出す際、Stein converse の `1 - ε` 因子が `limsup ≤ E₂(α) / (1 - ε)` の形で `E₂(α)` を bias する可能性がある。

→ **strong Stein** (`StrongStein.lean:498`, strict Tendsto 形) を直接流用すれば `1 - ε` 因子なしで通せる (StrongStein は `1 - ε` の `ε → 0` 極限版を既に取り済)。**Phase F (converse) は Stein ではなく StrongStein を呼ぶ**ことを Phase 開始時に確定。

### 危険 5: Type I 制御の Sanov LDP for `P := P₁, Q := P₁` 自己呼び出し

acceptance region の Type I 制御 (`P₁^n(s) ≥ 1 - alpha`) は Sanov LDP を `P := P₁, Q := P₁` で起動するのが自然だが、これは `klDivPmf P₁ P₁ = 0` で発散する trivial case。Mathlib `sanov_ldp_equality` がこの degenerate case を扱えるか確認必要 (`(P : α → ℝ) (hP_full : ∀ a, 0 < P a)` の `hP_full` 仮定は `P := P₁` で成立するので問題なさそうだが、`h_minimizer` 仮定で `klDivSumForm_ofVec P₁ (P₁.real ∘ ·) ≤ klDivIndex c n P₁_meas` が `0 ≤ klDivIndex` (`klDivIndex_nonneg` 補題が要る) に帰着する)。

→ **大数の法則の AEP 版** (`p_n_typeclass_tendsto_one` 補助補題) を Sanov LDP 経由ではなく自前で書く方が短くなる可能性 (~30-40 行)。**Phase E 着手時に判定**。

---

## まとめ

- **T1-D の定義 + 達成性 + 一意性 + 非負性は publish 済** (`InformationTheory/Shannon/Chernoff.lean` Tier 0 + Phase D 残, 既に 0 sorry, library root 編入済). 残るは **Tendsto 形** のみ.
- **既存 plumbing 100% 揃っている** (Sanov LDP equality + Stein achievability/converse template + Csiszar projection + Pythagoras). 自作 4-5 種 ~270-370 行 + skeleton ~40 行 = **~310-410 行**
- **撤退ライン L-S1 を本 plan に正式 import** (兄弟 plan からの継続). 新規撤退ライン L-H1〜L-H4 を提案 (pmf ↔ Measure bridge / Csiszar Pythagoras / Stein converse `1 - ε` 因子 / Tendsto 形不可能時の variational expression 縮退)
- **最大の risk は 「Qstar full-support 性」 (自作 2 の核)** — `csiszar_pythagoras_inequality` の `hQs_pos` 要件を満たすために `hoeffdingE2_minimizer_full_support` を新規補題で書く必要があり、これは KL strict convexity + 反転論証で 15-20 行だが、見落とすと自作 2/3/4 全部破綻する
- 次の risk は **「Sanov LDP per-Qstar の `E_n` 構成 + minimizer 仮定の per-`c` 整理」** (自作 2 + 3 の plumbing で 30-50 行)
- **proof-log 主張「T1-B + T1-D 一括着手で 70-80% 再利用」は T1-D 単独でも有効** — Stein achievability/converse template + Sanov LDP equality + Csiszar machinery が完全に揃っているため、Qstar 置換だけで Tendsto 形まで到達できる見込み
