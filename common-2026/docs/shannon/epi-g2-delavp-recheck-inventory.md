# EPI G2 de la Vallée-Poussin wall — independent re-check inventory

> 対象壁: `@residual(wall:approx-identity-L1)`、2 witness park 中
> - `InformationTheory/Shannon/EPIVitaliUI.lean:536` `negMulLog_convDensity_indicatorTail_uniform` (indicator-tail 入力、`unifIntegrable_of` への直接素材)
> - `InformationTheory/Shannon/EPIVitaliUnifTight.lean:360` `negMulLog_convDensity_unifTight` (UnifTight witness)
>
> 目的: 「de la VP 壁を genuine に閉じる in-tree / Mathlib 部品が揃うか」を**独立に** verbatim 再確認する。本ファイルは inventory のみ。実装・計画起草はしない。

## 一行サマリ

**de la VP 壁を閉じる Mathlib 部品は揃わない。** loogle authoritative: `MeasureTheory.UnifIntegrable + ConvexOn` = **Found 0**、`Real.negMulLog + MeasureTheory.Integrable` = **Found 0**、Mathlib 全体で "Vallée-Poussin" 文字列 **0 file**。superlinear-moment 一様有界を組む素材は in-tree に **無い**（line-moment `∫x²f_n` の一様有界 `convDensityAdd_second_moment_unif_bdd` は genuine に存在するが、negMulLog tail を支配しない）。UI/UT を迂回する Scheffé ルートも Mathlib に **無い**（`tendsto_Lp_of_tendsto_ae` は UI **かつ** UT を入力に要求、`tendsto_integral_of_dominated_convergence` は thin-tail `pX` で存在しない integrable envelope を要求）。`deBruijn_deriv_nonneg` route も**この壁を閉じない**（後述）。

---

## 主定理の最終形（park 中 witness 再掲）

```lean
-- EPIVitaliUI.lean:536  (de la VP bridge core)
theorem negMulLog_convDensity_indicatorTail_uniform
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ n,
      eLpNorm
        ({ x | C ≤ ‖Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)‖₊ }.indicator
          (fun x => Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)))
        1 volume ≤ ENNReal.ofReal ε := by sorry

-- EPIVitaliUnifTight.lean:360  (UnifTight witness)
theorem negMulLog_convDensity_unifTight
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u)) :
    UnifTight (fun n => fun x =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)) 1 volume := by sorry
```

想定 closure 戦略（park された 2 つ）と本 inventory が判定する成否:

```
[戦略 maxent]   maxent (Step 3) で ∫ negMulLog f_n ≤ (1/2)log(2πe·v_n) ── 供給は「符号付き上界」のみ
                → de la VP は ∫ G(|negMulLog f_n|) ≤ M (G superlinear) を要求 ── gap、Mathlib 不在 ✗
[戦略 deBruijn] deBruijn_deriv_nonneg を s で積分して entropy monotone-in-s を in-tree 化
                → 積分版が in-tree 不在、かつ entropy 単調性は UnifTight (tail 一様性) を出さない ✗
[戦略 Scheffé]  L¹/ae 収束 → 積分収束で UI/UT を迂回
                → tendsto_Lp_of_tendsto_ae が UI+UT を入力要求、dom-conv が thin-tail で envelope 不在 ✗
```

---

## §A in-tree de Bruijn / entropy 単調性 / convDensityAdd 資産

| name | file:line | verbatim signature (結論型 verbatim) | genuine? | de la VP route で使えるか |
|---|---|---|---|---|
| `deBruijn_deriv_nonneg` | `EPIStamDeBruijnConclusion.lean:132` | `(f : ℝ → ℝ) : 0 ≤ (1 / 2 : ℝ) * fisherInfoOfDensityReal f` | genuine (`@entry_point`, body = `mul_nonneg`) | **✗** — 結論は **pointwise の符号 `g'(t) ≥ 0`** のみ。`differentialEntropy(P.map(X+√sZ))` が s で単調という命題ではなく、s 積分版も別 lemma も無い。UnifTight (tail の n-一様性) とは無関係 |
| `isEPIGapMonotoneHyp_discharge` | `EPIStamDeBruijnConclusion.lean:139` | `(f : ℝ → ℝ) : IsEPIGapMonotoneHyp f` where `IsEPIGapMonotoneHyp f := 0 ≤ (1/2)*fisherInfoOfDensityReal f` | genuine | ✗ — 上と同じ符号 predicate の言い換え |
| `deBruijn_gap_deriv_nonneg_gaussian` | `EPIStamDeBruijnConclusion.lean:260` | `(X Z : Ω → ℝ) (hX hZ) (hXZ : IndepFun X Z P) {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) (hX_law : P.map X = gaussianReal m v) (hZ_law : P.map Z = gaussianReal 0 1) {t : ℝ} (ht : 0 < t) : 0 ≤ (1 / 2 : ℝ) * fisherInfoOfMeasureV2Real (P.map (gaussianConvolution X Z t)) (gaussianPDFReal m (v + ⟨t, ht.le⟩))` 型クラス: `{_mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]` | genuine | ✗ — **Gaussian 専用** の符号、一般 L¹ `pX` には無効 |
| `convDensityAdd` (def) | `EPIConvDensity.lean:42` | `noncomputable def convDensityAdd (pX pY : ℝ → ℝ) : ℝ → ℝ := …` (= `pX ∗ pY`) | def | 入力定義 (壁の対象関数) |
| `convDensityAdd_second_moment` | `EPIVitaliUnifTight.lean:123` | `{pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX) (hpX_int : Integrable pX volume) (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) : ∫ x, x ^ 2 * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ∂volume = (∫ x, x ^ 2 * pX x ∂volume) + (∫ y, pX y ∂volume) * t` | **genuine `@audit:ok`** (sorryAx-free, 2026-06-04) | **△ 部分的** — **line-moment (2 次)** の equality。負 log の superlinear-moment は出ない |
| `convDensityAdd_second_moment_unif_bdd` | `EPIVitaliUnifTight.lean:288` | `{pX} (hpX_nn hpX_meas hpX_int hpX_mom) (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u)) : ∃ V : ℝ, ∀ n, ∫ x, x ^ 2 * convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x ∂volume ≤ V` | **genuine `@audit:ok`** (sorryAx-free) | **△** — `∫x²f_n` の **n-一様有界** は genuine に手に入る。だが「2 次モーメント tail」では `-f_n log f_n` tail を支配できない (§結論参照) |
| `convDensityAdd_negMulLog_integrable` | `FisherInfoV2DeBruijnAssembly.lean:2529` (pub: `EPIG2HeatFlowContinuity.lean:127`) | pub form `convDensityAdd_negMulLog_integrable_pub (pX) (hpX_nn hpX_meas hpX_int hpX_mass hpX_mom) (ht : 0 < t) : Integrable (fun x => Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t,ht.le⟩) x)) volume` (`hpX_mass : (∫ pX) = 1`) | **genuine `@audit:ok`** (entropy-finiteness wall CLOSED) | **△** — 各 **固定 n** で `negMulLog f_n` integrable。**n-一様 tail** は出さない (これが正に壁) |
| `differentialEntropy_convDensityAdd_gaussian_eq` | `EPIVitaliUI.lean:111` | `{pX} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX) {t : ℝ} (ht : 0 < t) : differentialEntropy (volume.withDensity (fun x => ENNReal.ofReal (convDensityAdd pX (gaussianPDFReal 0 ⟨t,ht.le⟩) x))) = ∫ x, Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t,ht.le⟩) x) ∂volume` | **genuine `@audit:ok`** (sorryAx-free) | ○ framing — entropy ↔ `∫ negMulLog f_n` の橋。maxent route の足場 |
| `integral_convDensityAdd_gaussian_eq_one` | `EPIConvDensityNormalization.lean:37` | `(pX : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (hpX_int : Integrable pX volume) (hpX_norm : ∫ x, pX x ∂volume = 1) : ∫ z, convDensityAdd pX (gaussianPDFReal 0 ⟨t,ht.le⟩) z ∂volume = 1` | **genuine `@audit:ok`** (sorryAx-free) | ○ framing — `f_n` が確率密度であること |
| `differentialEntropy_le_gaussian_of_variance_le` (maxent) | `DifferentialEntropy.lean:520` | `{μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ)) (h_var_int : Integrable (fun x => (x - m)^2) μ) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) : differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | genuine | **✗ for de la VP** — 供給は **符号付き上界** `h(μ_n) ≤ (1/2)log(2πe·v_n)`。`∫ |negMulLog f_n| ≤ M` でも `∫ G(|negMulLog f_n|) ≤ M` でもない (判断ログ 9 を独立に再確認) |

**§A 所見**: de Bruijn 系 (`deBruijn_deriv_nonneg` 他) は「Fisher 情報の非負性 → 導関数の符号 ≥ 0」を述べるだけで、**entropy monotone-in-s を結論する積分版が in-tree に存在しない**。仮に積分版を自作しても、得られるのは `s ↦ h(P.map(X+√sZ))` の単調性 (= 端点エントロピーの**値**の比較) であって、UnifTight が要求する「tail eLpNorm の **n-一様 smallness**」は出ない。de Bruijn route は本壁 (`wall:approx-identity-L1`) に対して**カテゴリが違う**。

---

## §B Mathlib UI / de la VP / Scheffé 資産

| name | file:line | verbatim signature (型クラス `[...]` verbatim) | loogle Found | indicator-tail / superlinear-moment 変換に使えるか |
|---|---|---|---|---|
| `MeasureTheory.unifIntegrable_of` | `Mathlib/MeasureTheory/Function/UniformIntegrable.lean:653` | `(hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ι → α → β} (hf : ∀ i, AEStronglyMeasurable (f i) μ) (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ENNReal.ofReal ε) : UnifIntegrable f p μ` — **`[IsFiniteMeasure μ]` 無し**（変数 scope 外、`volume` に適用可） | (上位 17 件中の 1) | **○ 入力ゲートウェイ**。indicator-tail 入力 `h` の形は witness `negMulLog_convDensity_indicatorTail_uniform` の結論と**完全一致**。だが入力 `h` を供給する補題が無い (= 壁本体) |
| `MeasureTheory.uniformIntegrable_of` | `Mathlib/.../UniformIntegrable.lean:808` | `[IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) …` | 1 | **✗** — `[IsFiniteMeasure μ]` 要求。`volume` は σ-finite だが finite でないので**使用不可** |
| `MeasureTheory.unifIntegrable_finite` | `Mathlib/.../UniformIntegrable.lean:444` | `[Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {f : ι → α → β} …` | 1 | ✗ — `[Finite ι]` 要求 (有限族用)。我々は `ι = ℕ` 無限 |
| `MeasureTheory.unifIntegrable_of_tendsto_Lp` | `Mathlib/.../UniformIntegrable.lean:553` | `(hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ) (hg : MemLp g p μ) (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ` | 1 | ✗ (循環) — 入力 `hfg` = `negMulLog f_n → negMulLog pX` の **L¹ 収束**。これは我々が UI/UT を経由して**出したい**もの。前提に置けば循環 |
| `MeasureTheory.unifIntegrable_of_tendsto_Lp_zero` | `Mathlib/.../UniformIntegrable.lean:539` | `(hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, MemLp (f n) p μ) (hfg : Tendsto (fun n => eLpNorm (f n) p μ) atTop (𝓝 0)) : UnifIntegrable f p μ` | 1 | ✗ — `eLpNorm (f n) → 0` を要求 (我々の `negMulLog f_n` は 0 に行かない) |
| de la Vallée-Poussin 定理 (superlinear/convex moment → UI) | — | — | **Found 0** (`UnifIntegrable, ConvexOn`) / "Vallée-Poussin" 文字列 **0 file** | **✗ Mathlib 不在** (authoritative)。superlinear/convex majorant 経由 UI 構成 lemma は存在しない |
| `MeasureTheory.tendsto_Lp_of_tendsto_ae` (Scheffé 代替候補) | `Mathlib/MeasureTheory/Function/UnifTight.lean:329` | `(hp : 1 ≤ p) (hp' : p ≠ ∞) {f : ℕ → α → β} {g : α → β} (haef : ∀ n, AEStronglyMeasurable (f n) μ) (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)` | 1 | **✗ for 迂回** — 入力に `hui : UnifIntegrable` **かつ** `hut : UnifTight` を要求。**まさに我々が park している 2 witness が入力**。UI/UT を迂回しない |
| `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae` | `Mathlib/.../UniformIntegrable.lean:519` | `[IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞) … (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ …) : Tendsto …` | 1 | ✗ — `[IsFiniteMeasure μ]` 要求 + UI 入力。`volume` に使えず |
| `MeasureTheory.tendsto_integral_of_L1` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:399` | `{ι} (f : α → G) (hfi : Integrable f μ) {F : ι → α → G} {l : Filter ι} (hFi : ∀ᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0)) : Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 <| ∫ x, f x ∂μ)` | 1 | ✗ (循環) — 入力 `hF` = `negMulLog f_n → negMulLog pX` の L¹ 収束。`tendsto_Lp_of_tendsto_ae` 経由でしか出ず、結局 UI+UT に戻る |
| `MeasureTheory.tendsto_integral_of_dominated_convergence` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean:57` | `{F : ℕ → α → G} {f : α → G} (bound : α → ℝ) (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ) (bound_integrable : Integrable bound μ) (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : Tendsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ)` | 1 | **✗** — UI/UT を迂回する**唯一の真の候補**だが、`bound` (integrable, `‖negMulLog f_n‖ ≤ bound` a.e. **n-一様**) を要求。thin-tail `pX` では `-log f_n(x)` が super-polynomial に増大し、integrable envelope `bound` が **存在しない** (§A の in-file note 318-358 と整合) |
| Scheffé の定理 | — | — | **0 file** (`Scheff` 文字列なし) | ✗ Mathlib 不在 |

**§B 所見**: `unifIntegrable_of` (`:653`, `[IsFiniteMeasure]`-free) への reduction は witness 内で既に genuine に行われており、残るのは indicator-tail 入力 `h` の供給。これを満たす **de la VP / superlinear-moment 補題は Mathlib に Found 0**。迂回候補 `tendsto_Lp_of_tendsto_ae` は UI+UT を入力に求めるため迂回にならず、`tendsto_integral_of_dominated_convergence` は n-一様 integrable envelope を求めるが thin-tail `pX` で存在しない。

---

## §C `Real.negMulLog` 上下界 + Markov

| name | file:line | verbatim signature / 結論型 | superlinear majorant に使えるか |
|---|---|---|---|
| `Real.negMulLog_nonneg` | `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean:174` | `{x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x` | △ — `x ≤ 1` 域での符号のみ |
| `Real.negMulLog_le_one_sub_self` | `Mathlib/.../Log/NegMulLog.lean:234` | `{x : ℝ} (h0 : 0 ≤ x) : x.negMulLog ≤ 1 - x` | **✗** — **上界** `≤ 1 - x` (1 次線形)。superlinear lower/majorant は出ない。`-x log x` の負側 (大 x で `x log x` の発散) を支配しない |
| `Real.negMulLog_eq_neg` | `Mathlib/.../Log/NegMulLog.lean:168` | `negMulLog = fun x ↦ -(x * log x)` | framing only |
| `Real.strictConvexOn` (`mul_log`) 系 | `Mathlib/.../Log/NegMulLog.lean:225` | `strictConvexOn_mul_log.neg` 経由 `ConcaveOn ℝ (Ici 0) negMulLog` 相当 | ✗ — 凹性は Jensen 上界に使えるが UI の tail には無関係 |
| `abs_negMulLog` / `le_negMulLog` / `negMulLog_le` | — | — | **rg/loogle ともに該当無し** (上記 4 つ以外に上下界補題なし) |
| **Mathlib `negMulLog` + `Integrable` 連携** | — | — | **loogle Found 0** (`Real.negMulLog, MeasureTheory.Integrable`)。「`negMulLog` の積分可積分性/tail 制御」を直接述べる Mathlib lemma は**皆無** |
| `MeasureTheory.mul_meas_ge_le_lintegral` | `Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean:57` | `{f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) : ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ` (測度非依存版 Markov) | ○ — tail 集合の **測度** を `∫⁻` で抑える素材。witness 内で実際に使用 (UnifTight の `s = Icc(-R)R` reduction)。だが「tail eLpNorm の n-一様 smallness」を出すには n-一様な `∫⁻` 有界が必要で、それが negMulLog では出ない (壁本体) |
| `MeasureTheory.mul_meas_ge_le_lintegral₀` | `Mathlib/.../Lebesgue/Markov.lean:50` | `{f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (ε : ℝ≥0∞) : ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ` | ○ 同上 (AEMeasurable 版) |

**§C 所見**: negMulLog の Mathlib 上下界は `≤ 1 - x` (上界) と `0 ≤ negMulLog` (`x ≤ 1` 域) のみ。**superlinear majorant `G(|negMulLog x|)` を組む下からの制御は無い**。Markov (`mul_meas_ge_le_lintegral`) は tail 測度を `∫⁻` で抑えるが、negMulLog の `∫⁻` を **n-一様**に抑える補題が欠落しているため tail eLpNorm の n-一様 smallness には届かない。

---

## 主要前提条件ボックス (前提事故注意)

- **`unifIntegrable_of` (`:653`)** — `[IsFiniteMeasure μ]` を**要求しない**。`volume` (σ-finite) に適用可。これが witness の reduction を成立させている要。**`uniformIntegrable_of` (大文字, `:808`) と取り違えると `[IsFiniteMeasure]` 要求が混入し volume で詰む**。
- **`tendsto_Lp_of_tendsto_ae` (`UnifTight.lean:329`)** — `[IsFiniteMeasure μ]` **無し**だが、入力に `hui : UnifIntegrable f p μ` **かつ** `hut : UnifTight f p μ` の**両方**を要求。Scheffé 迂回として誤読しやすいが、UI+UT を消費するので park 中の 2 witness を前提に置くだけ (= 迂回不成立)。
- **`tendsto_integral_of_dominated_convergence`** — `bound : α → ℝ` が `Integrable bound μ` **かつ** `∀ n, ‖F n‖ ≤ bound` a.e. (n-一様 envelope)。thin-tail `pX` で `-log f_n` が super-polynomial に増大 → envelope 不在 (§A in-file note と整合)。
- **`differentialEntropy_le_gaussian_of_variance_le` (maxent)** — `[IsProbabilityMeasure μ]` + `hμ : μ ≪ volume` + `hv : v ≠ 0` + mean/var/integrability。結論は **符号付き上界**であって絶対値・superlinear-moment ではない (de la VP gap の本質)。

---

## 自作が必要な要素 (優先度順)

1. **de la VP 補題そのもの (superlinear-moment → indicator-tail uniform)** — 最優先・最高難度。「`∃ G superlinear, sup_n ∫ G(|negMulLog f_n|) dvol < ∞` ⟹ indicator-tail eLpNorm n-一様 → 0」。Mathlib 完全不在 (loogle Found 0)。**だがそもそも入力の `sup_n ∫ G(|negMulLog f_n|) < ∞` を一般 L¹ `pX` で確保する手段が無い** (下記落とし穴) ので、補題を書いても入力が埋まらない。
2. **negMulLog tail bridge** `|negMulLog f_n(x)| ≲ f_n(x)·(1 + log-tail)` — §A in-file note (EPIVitaliUnifTight.lean:318-358) が genuine attempt で**反例を確定**: thin-tail `pX` で `f_n(x) ≳ exp(-c x²)` の下界が破れ、`-log f_n` が super-polynomial。`1 + x²` envelope **存在しない**。これは「自作で埋まる plumbing」ではなく**数学的に false な heuristic**。
3. **de Bruijn 積分版** `s ↦ differentialEntropy(P.map(X+√sZ))` の MonotoneOn — 自作可能性はあるが、出力は端点エントロピー**値**の比較で、UnifTight (tail の n-一様性) に**変換できない** (カテゴリ違い)。本壁には無効。

工数感: 1 と 2 は in-tree plumbing ではなく真の数学コンテンツ (moonshot 級)。3 は書けても本壁を閉じない。

---

## Mathlib 壁の列挙 (`@residual(wall:approx-identity-L1)` 対象)

| wall | 内容 | loogle 確認 (authoritative) |
|---|---|---|
| de la Vallée-Poussin / superlinear-moment → UnifIntegrable | superlinear/convex moment 一様有界から UI を構成する定理 | `MeasureTheory.UnifIntegrable, ConvexOn` = **Found 0** / "Vallée-Poussin" 文字列 **0 file** / Scheffé `Scheff` **0 file** |
| `negMulLog` の積分 tail 制御 | `negMulLog` の可積分性・tail eLpNorm を述べる Mathlib lemma | `Real.negMulLog, MeasureTheory.Integrable` = **Found 0** |
| n-一様 integrable envelope (dominated convergence 迂回用) | thin-tail `pX` で `‖negMulLog f_n‖ ≤ bound` (integrable, n-一様) | 数学的に**存在しない** (反例: thin-tail `pX`、§A note 318-358) |

**shared sorry 補題化**: 2 witness (`negMulLog_convDensity_indicatorTail_uniform` / `negMulLog_convDensity_unifTight`) は同一壁 `wall:approx-identity-L1` に park 中で、別 file (EPIVitaliUI / EPIVitaliUnifTight) に分散している。**shared sorry 補題への集約推奨** (詳細 → `docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」)。ただし両者は結論型が異なる (indicator-tail eLpNorm vs UnifTight) ため、共有素材は「negMulLog tail bridge」(自作 #2、現状反例で false) のレベルでしか括れない。**集約より先に、そもそもこの壁が closure 可能な数学命題かの再判定が要る** (下記撤退ライン)。

---

## 撤退ラインへの距離

親計画 `docs/shannon/` の EPI G2 closure plan は「de la VP wall = 真 moonshot」と既に確定済み (commit 634fc47: advisor NO-GO、precondition では閉じない、判断ログ 9)。本独立再調査はその判定を**追認**する:

- **撤退ライン発動: yes (追認)**。「唯一の将来ルート」とされた `deBruijn_deriv_nonneg` 積分 route は、本 inventory で**カテゴリ違い (entropy 値の単調性 ≠ tail の n-一様性) と確定**。de la VP / Scheffé / dominated-convergence の Mathlib 迂回も全て塞がっている。
- 縮退案 (新規撤退ラインとして提案): 2 witness を `sorry + @residual(wall:approx-identity-L1)` のまま **真 moonshot 壁として park 確定**し、shared sorry 補題に集約 (negMulLog tail bridge レベル) して bookkeeping を 1 本化する。**仮説束化は禁止** (撤退口は sorry + `@residual` のみ)。entropy-finiteness / second-moment / framing の周辺は既に genuine `@audit:ok` なので、壁は negMulLog tail bridge の 1 点に局所化済み。

---

## 着手 skeleton (park 確定形、新規実装はしない)

> 本壁は genuine closure 不能と再確認。skeleton は「2 witness を park したまま、共有壁 bookkeeping を 1 本化する」shared-lemma 形のみ示す (実装は別 task)。

```lean
-- InformationTheory/Shannon/EPIVitaliDeLaVPWall.lean (構想、未作成)
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import InformationTheory.Shannon.EPIConvDensity

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- **Shared de la Vallée-Poussin wall (approx-identity-L1).**
negMulLog tail bridge for `f_n = pX ∗ g_{u n}`: the n-uniform superlinear-moment
control of `negMulLog f_n` that both the indicator-tail (`unifIntegrable_of` input)
and the `UnifTight` witnesses reduce to. Mathlib-absent (loogle: `UnifIntegrable +
ConvexOn` = 0, `negMulLog + Integrable` = 0); the heuristic `|log f_n| ≲ 1 + x²`
is FALSE for thin-tailed `pX`. True moonshot — parked.
@residual(wall:approx-identity-L1) -/
theorem negMulLog_convDensity_delaVP_wall
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_bdd : BddAbove (Set.range u))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ n,
      eLpNorm
        ({ x | C ≤ ‖Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)‖₊ }.indicator
          (fun x => Real.negMulLog
            (convDensityAdd pX (gaussianPDFReal 0 ⟨u n, (hu_pos n).le⟩) x)))
        1 volume ≤ ENNReal.ofReal ε := by
  sorry  -- @residual(wall:approx-identity-L1)

end InformationTheory.Shannon
```

---

## §結論 (A/B/C 総合判定)

**de la VP 壁を閉じる in-tree / Mathlib 部品は揃わない。真 moonshot 確定 (independent 再調査で追認)。**

2 つの問いへの yes/no:

1. **superlinear-moment 一様有界を組む素材が in-tree にあるか → NO。** line-moment (`∫x²f_n` の n-一様有界 `convDensityAdd_second_moment_unif_bdd`) は genuine に存在するが、negMulLog の superlinear-moment `∫G(|negMulLog f_n|)` の一様有界を組む素材は無い。§A in-file note (EPIVitaliUnifTight.lean:318-358) の genuine attempt が示す通り、thin-tail `pX` で `-log f_n` が super-polynomial に発散し、line-moment では `-f_n log f_n` tail を支配できない (heuristic `|log f_n| ≲ 1+x²` が数学的に false)。maxent は符号付き上界のみで `∫|negMulLog f_n|` でも `∫G(|negMulLog f_n|)` でもない。

2. **UI/UT を迂回する Scheffé ルートが Mathlib にあるか → NO。** Scheffé は Mathlib 不在 (`Scheff` 文字列 0 file)。`tendsto_Lp_of_tendsto_ae` は UI **かつ** UT を入力に要求し迂回にならない。`tendsto_integral_of_L1` は L¹ 収束を前提に置き循環。`tendsto_integral_of_dominated_convergence` は n-一様 integrable envelope を要求するが thin-tail `pX` で存在しない。

loogle authoritative (Found 0 を明記): `MeasureTheory.UnifIntegrable, ConvexOn` = **Found 0**、`Real.negMulLog, MeasureTheory.Integrable` = **Found 0**、Mathlib 全体で "Vallée-Poussin" / "Scheff" 文字列 = **0 file**。`deBruijn_deriv_nonneg` route は pointwise 符号のみでカテゴリ違い (entropy 値単調性 ≠ tail n-一様性) のため本壁を閉じない。**撤退ライン発動: yes (追認)** — 2 witness は `@residual(wall:approx-identity-L1)` park 確定、shared sorry 補題化推奨。
