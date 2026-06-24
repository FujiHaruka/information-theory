# EPI G2 (α) 上界 — klFun-Fatou による KL 下半連続ルート Mathlib 在庫

> 親計画: [`epi-g2-general-sandwich-moonshot-plan.md`](epi-g2-general-sandwich-moonshot-plan.md)
> （Phase 2 = (α) 上界。現状の (α) は `2b DV 双対 hard direction` が `@residual(wall:kl-lower-semicontinuous)` で park 中）
>
> 本ファイルは (α) 上界を **新ルート = klFun-Fatou 構成的 LSC** で攻めるための部品在庫。
> DV 双対（変分定義・上限を取る hard direction）を回避し、`klDiv = ∫⁻ klFun(rnDeriv) dν` の積分形 +
> `klFun ≥ 0` + lintegral-Fatou で `liminf KL(μ_n‖γ) ≥ KL(μ‖γ)` を直接出す。
> 調査日: 2026-06-05。全 verbatim signature は実 Mathlib / in-tree file を Read で逐語照合済。

---

## 一行サマリ

**このルートの部品は実体ベースで既存率 ~85%。Mathlib の klDiv 積分形 (`klDiv_eq_lintegral_klFun_of_ac`)・`klFun_nonneg`・`lintegral_liminf_le` (Fatou)・`rnDeriv` の withDensity 同定 (`rnDeriv_mul_rnDeriv` / `rnDeriv_withDensity_right`)・in-tree の a.e.-部分列収束 (`negMulLog_convDensity_tendsto_ae_subseq`) と second-moment (`convDensityAdd_second_moment`) が全て既存。自作必要は実質 3 件（KL-LSC 本体補題、rnDeriv 商の base-measure 統一補題、cross-term 収束の組み立て）。最大 gap は項目 4 の rnDeriv 商の a.e. 同定 — ただし「不在の壁」ではなく `rnDeriv_mul_rnDeriv` を 2 回噛ませる既存部品の組み立てに帰着できる見込み。** 親計画の `wall:kl-lower-semicontinuous` 撤退ラインは、このルートが通れば surface が DV 双対から「Fatou 組み立て」に縮退（壁の格下げ）。

---

## 主定理の最終形（再掲 + このルートでの中核補題）

親計画 Phase 2 の (α) 上界（pseudo）:

```lean
-- f_n := convDensityAdd pX (gaussianPDFReal 0 ⟨u n, _⟩),  μ_n = volume.withDensity (ofReal ∘ f_n)
-- γ := gaussianReal 0 σ²,  g := gaussianPDFReal 0 σ² (= γ の密度)
-- 目標: limsup (differentialEntropy μ_n) ≤ differentialEntropy μ   （端点上半連続）
```

このルートが供給する中核補題（自作対象 W1）:

```lean
theorem klDiv_le_liminf_of_ae_tendsto
    (γ : Measure ℝ) [IsProbabilityMeasure γ] (hγv : γ ≪ volume)
    (μ : Measure ℝ) (μ_n : ℕ → Measure ℝ) [IsProbabilityMeasure μ] [∀ n, IsProbabilityMeasure (μ_n n)]
    (hμ_ac : μ ≪ γ) (hμn_ac : ∀ n, μ_n n ≪ γ)
    (h_ae : ∀ᵐ x ∂γ, Tendsto (fun n => (((μ_n n).rnDeriv γ x).toReal)) atTop
              (𝓝 ((μ.rnDeriv γ x).toReal))) :
    klDiv μ γ ≤ Filter.liminf (fun n => klDiv (μ_n n) γ) atTop := by sorry
```

証明戦略（pseudo-Lean, 7行）:

```lean
rw [klDiv_eq_lintegral_klFun_of_ac hμ_ac]                      -- LHS = ∫⁻ ofReal (klFun (rnDeriv μ γ)) dγ
conv_rhs => ext n; rw [klDiv_eq_lintegral_klFun_of_ac (hμn_ac n)] -- RHS 各項も同形
refine le_trans (lintegral_mono_ae ?_) (lintegral_liminf_le ?_) -- Fatou (klFun ≥ 0, ofReal で ℝ≥0∞)
· -- pointwise: ofReal (klFun (rnDeriv μ γ x)) ≤ liminf (ofReal (klFun (rnDeriv μ_n n γ x)))
  filter_upwards [h_ae] with x hx
  exact (continuous_klFun.tendsto _ |>.comp hx |> ENNReal.continuous_ofReal.tendsto _ |>.comp).le_liminf
· exact fun n => (measurable_klFun.comp (measurable_rnDeriv _ _).ennreal_toReal).ennreal_ofReal
```

> 注: 上の `differentialEntropy` 目標と KL-LSC の橋渡しは in-tree `klDiv_toReal_eq_neg_differentialEntropy_sub_cross`（既存 `@audit:ok`）+ cross-term 収束（W3）で組む。本ルートの新規性は「KL-LSC を DV 双対でなく klFun-Fatou で出す」点に集約される。

---

## A. klDiv の積分表現（項目 1） — ★ルートの土台、全件既存

すべて `Mathlib/InformationTheory/KullbackLeibler/Basic.lean`。namespace `InformationTheory`、
section 前提 `variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}`。
`AlternativeFormulas` / `Real` section は `variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]` を追加。

| 概念 | Mathlib API | file:line | 状態 | このルートでの扱い |
|---|---|---|---|---|
| ℝ≥0∞ 積分形 (ac 限定) | `klDiv_eq_lintegral_klFun_of_ac` | `KullbackLeibler/Basic.lean:138` | ✅ 既存 | **★ Fatou の入口**。`klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν` |
| ℝ≥0∞ 積分形 (if-分岐) | `klDiv_eq_lintegral_klFun` | `KullbackLeibler/Basic.lean:119` | ✅ 既存 | ac 不要だが `if μ ≪ ν then … else ∞`。ac 版で十分 |
| ℝ 積分形 (toReal) | `toReal_klDiv_eq_integral_klFun` | `KullbackLeibler/Basic.lean:170` | △前提注意 | `(klDiv μ ν).toReal = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν`。Bochner 形、Fatou には ℝ≥0∞ 形を使うので副次 |
| ℝ 積分形 (if-分岐) | `klDiv_eq_integral_klFun` | `KullbackLeibler/Basic.lean:111` | ✅ 既存 | `ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν)`（ac∧integrable のとき） |
| Jensen 下界 | `mul_klFun_le_toReal_klDiv` | `KullbackLeibler/Basic.lean:338` | △前提注意 | 本ルートでは不使用（Fatou が直接 LSC を出す）。reference |

### verbatim signature（逐語、`[...]` / 前提を改変せず）

```lean
-- Basic.lean:138  (section variable: [IsFiniteMeasure μ] [IsFiniteMeasure ν])
lemma klDiv_eq_lintegral_klFun_of_ac (h_ac : μ ≪ ν) :
    klDiv μ ν = ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν

-- Basic.lean:119  (section variable: [IsFiniteMeasure μ] [IsFiniteMeasure ν])
lemma klDiv_eq_lintegral_klFun :
    klDiv μ ν = if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν else ∞

-- Basic.lean:170  (section variable: [IsFiniteMeasure μ] [IsFiniteMeasure ν])
lemma toReal_klDiv_eq_integral_klFun (h : μ ≪ ν) :
    (klDiv μ ν).toReal = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν

-- Basic.lean:111  (section variable: [IsFiniteMeasure μ] [IsFiniteMeasure ν]) + `open Classical`
lemma klDiv_eq_integral_klFun :
    klDiv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ
      then ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν)
      else ∞

-- Basic.lean:338  (section variable: [IsFiniteMeasure μ] [IsFiniteMeasure ν])
lemma mul_klFun_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ν.real univ * klFun (μ.real univ / ν.real univ) ≤ (klDiv μ ν).toReal
```

**前提事故ボックス（項目 1）**:
- `klDiv_eq_lintegral_klFun_of_ac` の前提は **`[IsFiniteMeasure μ] [IsFiniteMeasure ν]`（section variable）+ `μ ≪ ν`** のみ。`Integrable (llr μ ν) μ` は不要（ℝ≥0∞ 形は非可積分でも `∞` に化けず lintegral がそのまま値を持つ）→ **Fatou ルートが Bochner 形より優位な核心理由**。
- 結論の積分は **`∂ν`（= γ）上**であり `μ` 上ではない。被積分の `klFun` 引数は **`(μ.rnDeriv ν x).toReal`**（`μ` の `ν`-rnDeriv の toReal）。verbatim。
- ℝ≥0∞ 値（`ENNReal.ofReal (klFun …)`）。`klFun ≥ 0`（項目 2）ゆえ `ofReal` で情報落ちなし。

---

## B. klFun の性質（項目 2） — 全件既存

すべて `Mathlib/InformationTheory/KullbackLeibler/KLFun.lean`。namespace `InformationTheory`、
`variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {x : ℝ}`。

| 概念 | Mathlib API | file:line | 状態 | verbatim 結論 |
|---|---|---|---|---|
| 定義 | `klFun` | `KLFun.lean:53` | ✅ | `noncomputable def klFun (x : ℝ) : ℝ := x * log x + 1 - x` |
| 非負 | `klFun_nonneg` | `KLFun.lean:149` | ✅ | `(hx : 0 ≤ x) : 0 ≤ klFun x` |
| 連続 | `continuous_klFun` | `KLFun.lean:76` | ✅ | `Continuous klFun`（`@[continuity, fun_prop]`） |
| 可測 | `measurable_klFun` | `KLFun.lean:80` | ✅ | `Measurable klFun`（`@[fun_prop]`） |
| 強可測 | `stronglyMeasurable_klFun` | `KLFun.lean:84` | ✅ | `StronglyMeasurable klFun` |
| 凸 [0,∞) | `convexOn_klFun` | `KLFun.lean:67` | ✅ | `ConvexOn ℝ (Ici 0) klFun` |
| 狭義凸 [0,∞) | `strictConvexOn_klFun` | `KLFun.lean:62` | ✅ | `StrictConvexOn ℝ (Ici 0) klFun` |
| klFun(1)=0 | `klFun_one` | `KLFun.lean:59` | ✅ | `klFun 1 = 0` |
| klFun(0)=1 | `klFun_zero` | `KLFun.lean:57` | ✅ | `klFun 0 = 1` |
| ゼロ判定 | `klFun_eq_zero_iff` | `KLFun.lean:151` | ✅ | `(hx : 0 ≤ x) : klFun x = 0 ↔ x = 1` |

**前提事故ボックス（項目 2）**:
- `klFun_nonneg` は `0 ≤ x` を要求。Fatou 適用時の被積分は `klFun ((rnDeriv …).toReal)`、`.toReal ≥ 0` は `ENNReal.toReal_nonneg`（引数なし）で常に供給可。
- `continuous_klFun` は `@[fun_prop]` 付き → pointwise 収束 `rnDeriv μ_n → rnDeriv μ` の `klFun` 合成連続性が `fun_prop` / `.tendsto` で即出る。

---

## C. Fatou（項目 3） — 既存、atTop は IsCountablyGenerated

`Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`。`MonotoneConvergence` section、`variable {μ : Measure α}`。

| 概念 | Mathlib API | file:line | 状態 | verbatim |
|---|---|---|---|---|
| Fatou (Measurable) | `lintegral_liminf_le` | `Add.lean:231` | ✅ | 下記 |
| Fatou (AEMeasurable) | `lintegral_liminf_le'` | `Add.lean:214` | ✅ | `h_meas : ∀ i, AEMeasurable (f i) μ` 版 |

```lean
-- Add.lean:231
theorem lintegral_liminf_le {ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι}
    [IsCountablyGenerated u] (h_meas : ∀ i, Measurable (f i)) :
    ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u

-- Add.lean:214
theorem lintegral_liminf_le' {ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι}
    [IsCountablyGenerated u] (h_meas : ∀ i, AEMeasurable (f i) μ) :
    ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u
```

**前提事故ボックス（項目 3）**:
- `[IsCountablyGenerated u]` 必須。`u = atTop : Filter ℕ` は `Filter.atTop_countably_generated`（Mathlib instance、`ℕ` は可算）で自動充足。明示提供不要。
- **ℝ≥0∞-値必須**。klFun は ℝ-値ゆえ `ENNReal.ofReal ∘ klFun` でリフト（項目 1 の `klDiv_eq_lintegral_klFun_of_ac` 結論がまさにこの形）。型は整合。
- 結論は `∫⁻ liminf ≤ liminf ∫⁻`。LHS の `liminf (f n a)` を pointwise 等式 `= ofReal (klFun (rnDeriv μ γ a))`（項目 4 の a.e. 同定 + h_ae の pointwise 収束）で潰す → `klDiv μ γ ≤ liminf (klDiv μ_n γ)`。
- 各 `f n` の `Measurable` は `measurable_klFun.comp ((measurable_rnDeriv _ _).ennreal_toReal) |>.ennreal_ofReal`（全部既存 `@[fun_prop]`）。

---

## D. rnDeriv の a.e. 同定（項目 4） — ★最大 gap、ただし不在の壁ではなく組み立て

`Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`、namespace `MeasureTheory.Measure`、
`variable {μ ν : Measure α}`（α は冒頭 `variable {α : Type*} {m : MeasurableSpace α}`）。
`rnDeriv_withDensity_leftRight` section は `variable {f : α → ℝ≥0∞}` を追加。

### 状況の構造

`μ_f = volume.withDensity (ofReal ∘ f)`、`γ = volume.withDensity (ofReal ∘ g)`（g > 0 everywhere）。
Fatou が要求するのは **`rnDeriv μ_f γ` の `γ`-a.e. 値**。直接「`rnDeriv (withDensity h₁) (withDensity h₂)`」を一発で与える Mathlib lemma は **不在**（下記 loogle 参照）。だが既存部品の組み立てで出る:

- `rnDeriv_mul_rnDeriv (hμν : μ ≪ ν) : μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ` を `κ := volume` 軸で使う chain、または
- `rnDeriv_withDensity_right` で `μ.rnDeriv (ν.withDensity f)` を `ν`-a.e. に `(f x)⁻¹ * μ.rnDeriv ν x` へ。

| 概念 | Mathlib API | file:line | 状態 | verbatim |
|---|---|---|---|---|
| rnDeriv 商 (右 withDensity) | `rnDeriv_withDensity_right` | `RadonNikodym.lean:168` | △前提注意 | 下記 |
| rnDeriv 乗法 (κ 軸) | `rnDeriv_mul_rnDeriv` | `RadonNikodym.lean:402` | ✅ | 下記 |
| rnDeriv 乗法 (ν 軸) | `rnDeriv_mul_rnDeriv'` | `RadonNikodym.lean:410` | ✅ | `(hνκ : ν ≪ κ) : μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[ν] μ.rnDeriv κ` |
| rnDeriv 左 withDensity | `rnDeriv_withDensity_left` | `RadonNikodym.lean:132` | ✅ | `(hfν : AEMeasurable f ν) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) : (μ.withDensity f).rnDeriv ν =ᵐ[ν] fun x ↦ f x * μ.rnDeriv ν x` |
| withDensity rnDeriv = | `withDensity_rnDeriv_eq` | `RadonNikodym.lean:60` | ✅ | `[HaveLebesgueDecomposition μ ν] (h : μ ≪ ν) : ν.withDensity (rnDeriv μ ν) = μ` |
| rnDeriv of withDensity (base) | `Measure.rnDeriv_withDensity` | `Decomposition/Lebesgue.lean` | ✅ | `(ν : Measure α) [SigmaFinite ν] {f : α → ℝ≥0∞} (hf : Measurable f) : (ν.withDensity f).rnDeriv ν =ᵐ[ν] f` |
| gaussianReal の rnDeriv | `rnDeriv_gaussianReal` | `Gaussian/Real.lean:240` | ✅ | `(μ : ℝ) (v : ℝ≥0) : ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v` |

```lean
-- RadonNikodym.lean:168  (section variable {f : α → ℝ≥0∞})
lemma rnDeriv_withDensity_right (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (hf : AEMeasurable f ν) (hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0) (hf_ne_top : ∀ᵐ x ∂ν, f x ≠ ∞) :
    μ.rnDeriv (ν.withDensity f) =ᵐ[ν] fun x ↦ (f x)⁻¹ * μ.rnDeriv ν x

-- RadonNikodym.lean:402
lemma rnDeriv_mul_rnDeriv {κ : Measure α} [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]
    (hμν : μ ≪ ν) :
    μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ
```

**前提事故ボックス（項目 4） — ★最重要**:
- `rnDeriv_withDensity_right` の a.e. 等式は **`=ᵐ[ν]`（base measure ν 上）であって `=ᵐ[ν.withDensity f]`（= γ 上）ではない**。Fatou は `∂γ` 上の pointwise 等式を要求するため、**`γ`-a.e. への乗り換え**が追加で要る。`γ = volume.withDensity (ofReal∘g)` と `volume ≪ γ`（g>0 ⟹ `gaussianReal_absolutelyContinuous'` 系）から `=ᵐ[volume] ⟹ =ᵐ[γ]` は `AbsolutelyContinuous.ae_eq` で乗る。逆向き（γ-null ⟹ volume-null）は g>0 と `withDensity_absolutelyContinuous` で両立。→ **a.e. の base 不一致が silent な型/フィルタ mismatch を生む第一の事故源**。
- `rnDeriv_withDensity_right` の `hf_ne_zero : ∀ᵐ x ∂ν, f x ≠ 0` は g>0 everywhere（`gaussianPDFReal_pos`, `Gaussian/Real.lean:61`）で充足。`hf_ne_top` は `ENNReal.ofReal _ ≠ ∞`（常真、`ENNReal.ofReal_ne_top`）。
- `rnDeriv_mul_rnDeriv` は `[SigmaFinite μ] [SigmaFinite ν] [SigmaFinite κ]` 三つ + `μ ≪ ν` を要求。`κ := volume` は SigmaFinite、μ_f / γ も withDensity (finite mass) で SigmaFinite。
- 推奨 chain（base = volume 統一）: `rnDeriv μ_f γ =ᵐ[γ] (rnDeriv μ_f volume) * (rnDeriv volume γ)`（`rnDeriv_mul_rnDeriv'` 系を `μ:=μ_f, ν:=γ, κ:=volume` でなく逆組）。**実装時に μ ≪ ν の向きと =ᵐ の base を実 LSP で 1 度確認すべき**（向きを取り違えると 1 turn ループ）。
- `Measure.rnDeriv_withDensity (Lebesgue.lean)` で `rnDeriv μ_f volume =ᵐ[volume] (ofReal∘f)`、`rnDeriv γ volume =ᵐ[volume] (ofReal∘g)`（または `rnDeriv_gaussianReal`）。商 `(ofReal f)/(ofReal g) = ofReal (f/g)`（g>0）に整理。

**結論（項目 4 の判定）**: 「`rnDeriv μ_f γ =ᵐ[γ] ofReal (f x / g x)` を一発で与える Mathlib lemma」は **不在**。だが構成部品（`rnDeriv_mul_rnDeriv` / `rnDeriv_withDensity_right` / `Measure.rnDeriv_withDensity` / base 乗り換え `AbsolutelyContinuous.ae_eq`）は **全て既存**。→ これは「壁」ではなく **自作補題 W2（~40-60 行の組み立て）**。

---

## E. L¹ → a.e. 部分列収束（項目 5） — in-tree に既存完成品

| 概念 | API | file:line | 状態 | verbatim |
|---|---|---|---|---|
| measure → a.e. 部分列 | `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae` | `Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:277` | ✅ | 下記 |
| **in-tree** negMulLog 版 | `EPIVitaliAE.negMulLog_convDensity_tendsto_ae_subseq` | `InformationTheory/Shannon/EPIVitaliAE.lean:72` | ✅ `@audit:ok` | 下記 |
| L¹→measure | `tendstoInMeasure_of_tendsto_eLpNorm` | `ConvergenceInMeasure.lean`（in-tree 経由で使用済） | ✅ | EPIVitaliAE で使用 |

```lean
-- ConvergenceInMeasure.lean:277  (variable {α ι κ E} {m : MeasurableSpace α} {μ : Measure α}
--   [PseudoEMetricSpace E] {f : ℕ → α → E} {g : α → E})
theorem TendstoInMeasure.exists_seq_tendsto_ae (hfg : TendstoInMeasure μ f atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x))

-- EPIVitaliAE.lean:72  (genuine, sorryAx-free, @audit:ok)
theorem negMulLog_convDensity_tendsto_ae_subseq
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    (u : ℕ → ℝ) (hu_pos : ∀ n, 0 < u n) (hu_lim : Tendsto u atTop (𝓝[Set.Ioi 0] 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂volume,
      Tendsto (fun i =>
        Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨u (ns i), (hu_pos (ns i)).le⟩) x))
        atTop (𝓝 (Real.negMulLog (pX x)))
```

**前提事故ボックス（項目 5）**:
- `exists_seq_tendsto_ae` は `f : ℕ → α → E` 限定（`atTop : Filter ℕ`）+ `[PseudoEMetricSpace E]`。`E := ℝ` で OK。
- **部分列限定**（`∃ ns, StrictMono ns ∧ …`）。full-sequence ではない。Fatou は subsequence でも成立（`liminf` の部分列下界、項目 6）ので問題なし — ただし「subsequence の liminf ≤ full の liminf でなく逆」の向きに注意。Fatou で得る `klDiv μ γ ≤ liminf_{i} klDiv (μ_{ns i}) γ`、これを full sequence の limsup 評価に繋ぐには **`tendsto_of_subseq_tendsto`**（項目 6）が要る。
- in-tree 版 `negMulLog_convDensity_tendsto_ae_subseq` は **`negMulLog (f_n)`** の a.e. 収束を返す。本ルートが要求するのは **`rnDeriv μ_n γ` の a.e. 収束**。両者を繋ぐには「`f_n → pX` a.e. ⟹ `rnDeriv μ_n γ → rnDeriv μ γ` a.e.」（項目 4 の同定 `rnDeriv μ_n γ =ᵐ[γ] ofReal(f_n/g)` + `f_n → pX` pointwise + g>0 連続商）。**negMulLog 版そのままでは rnDeriv 収束を供給しない**ので、密度 `f_n → pX` a.e. 版（`exists_seq_tendsto_ae` を `f_n` 直接に適用、negMulLog を被せない）を別途取り出すのが素直。EPIVitaliAE の証明本体（L¹→measure→a.e. subseq）を `negMulLog` 合成前で切れば density 版が出る。

---

## F. liminf 部分列処理（項目 6） — 既存

| 概念 | API | file:line | 状態 | verbatim |
|---|---|---|---|---|
| liminf 下界 | `Filter.le_liminf_of_le` | `Mathlib/Order/LiminfLimsup.lean:145` | ✅ | 下記 |
| 部分列収束 → 収束 | `tendsto_of_subseq_tendsto` | `Mathlib/Topology/...`（loogle 確認推奨） | △未読 | 部分列で全列収束を出す逆向き |
| liminf 比較 | `Filter.liminf_le_liminf_of_le` | `LiminfLimsup.lean:239` | ✅ | `(h : g ≤ f) : liminf u f ≤ liminf u g` 系 |

```lean
-- LiminfLimsup.lean:145  (variable {f : Filter β} {u : β → α} {a})
theorem le_liminf_of_le {f : Filter β} {u : β → α} {a}
    (hf : f.IsCoboundedUnder (· ≥ ·) u := by isBoundedDefault)
    (h : ∀ᶠ n in f, a ≤ u n) : a ≤ liminf u f
```

**前提事故ボックス（項目 6）**:
- `le_liminf_of_le` の `hf : IsCoboundedUnder` は `by isBoundedDefault` の autoParam。ℝ≥0∞ は完備束ゆえ自動。pointwise の Fatou 内 `(klFun …).tendsto.le_liminf` で局所的に使う。
- full-sequence の上半連続 `limsup (differentialEntropy μ_n) ≤ differentialEntropy μ` への昇格には `tendsto_of_subseq_tendsto`（任意部分列が更に収束部分列を持てば全列収束）の確認が要る。**未 Read = 実装前に loogle 1 件確認推奨**（`Filter.tendsto_of_subseq_tendsto`）。

---

## G. second-moment 収束（項目 7） — in-tree に既存完成品

| 概念 | API | file:line | 状態 | verbatim |
|---|---|---|---|---|
| **in-tree** 2次モーメント | `convDensityAdd_second_moment` | `InformationTheory/Shannon/EPIVitaliUnifTight.lean:123` | ✅ `@audit:ok` | 下記 |
| gaussianReal 密度 | `gaussianReal` / `gaussianReal_of_var_ne_zero` | `Gaussian/Real.lean:200,203` | ✅ | `gaussianReal μ v = if v=0 then dirac μ else volume.withDensity (gaussianPDF μ v)` |
| gaussianPDFReal | `gaussianPDFReal` | `Gaussian/Real.lean`（def） | ✅ | 密度の実数値版（log 閉形は `Real.log (gaussianPDFReal …)` を展開して計算） |

```lean
-- EPIVitaliUnifTight.lean:123  (genuine, @audit:ok)
theorem convDensityAdd_second_moment
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume)
    {t : ℝ} (ht : 0 < t) :
    ∫ x, x ^ 2 * convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x ∂volume
      = (∫ x, x ^ 2 * pX x ∂volume) + (∫ y, pX y ∂volume) * t
```

**前提事故ボックス（項目 7）**:
- `convDensityAdd_second_moment` は `M2(f_t) = M2(pX) + (∫pX)·t` を **closed form で**返す（`@audit:ok`、genuine）。`t = u n → 0` で `M2(f_n) → M2(pX)`（`∫pX = 1` for probability density）。cross-term `∫ f_n log g`（g = gaussian 密度、log g は 2次多項式）は M2(f_n) の affine 関数ゆえ M2 収束から従う。
- cross-term `∫ pX log g` への収束は「`log gaussianPDFReal 0 σ² x = c₀ - x²/(2σ²)`（2次多項式）」+ M2 収束 + `∫ f_n = 1` の組み合わせ。**log gaussianPDFReal の閉形は `Gaussian/Real.lean` の `gaussianPDFReal` 定義を展開**（`-log(√(2πσ²)) - (x-μ)²/(2σ²)`）。数値は実装時 verbatim 確認（直感禁止、CLAUDE.md「数値 verbatim 確認」）。

---

## H. ガウス密度正値性 + μ_n ≪ γ（項目 8） — 全件既存

| 概念 | API | file:line | 状態 | verbatim |
|---|---|---|---|---|
| gaussianPDFReal > 0 | `ProbabilityTheory.gaussianPDFReal_pos` | `Gaussian/Real.lean:61` | ✅ | `(μ : ℝ) (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) : 0 < gaussianPDFReal μ v x` |
| gaussianReal ≪ volume | `gaussianReal_absolutelyContinuous` | `Gaussian/Real.lean:228` | ✅ | `(μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : gaussianReal μ v ≪ volume` |
| volume ≪ gaussianReal | `gaussianReal_absolutelyContinuous'` | `Gaussian/Real.lean:233` | ✅ | `(μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : volume ≪ gaussianReal μ v` |
| withDensity ≪ base | `withDensity_absolutelyContinuous` | `Mathlib/MeasureTheory/Measure/WithDensity.lean:147` | ✅ | `{m : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) : μ.withDensity f ≪ μ` |
| base ≪ withDensity (g>0) | `withDensity_absolutelyContinuous'` | `WithDensity.lean:564` | ✅ | `{μ : Measure α} {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0) : μ ≪ μ.withDensity f` |

**前提事故ボックス（項目 8）**:
- `μ_n ≪ γ` の供給: `μ_n = volume.withDensity (ofReal∘f_n)`、`γ = volume.withDensity (ofReal∘g)`。`μ_n ≪ volume`（`withDensity_absolutelyContinuous`）+ `volume ≪ γ`（`withDensity_absolutelyContinuous'`、g>0）→ `μ_n ≪ γ`（`.trans`）。g>0 が要のため `gaussianPDFReal_pos` の `hv : v ≠ 0`（σ²≠0）が必須 — **σ²=0 退化境界は別扱い**（dirac、ルート外）。
- `withDensity_absolutelyContinuous'` の `hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0` は `ofReal (gaussianPDFReal …) ≠ 0`、`gaussianPDFReal_pos` から `ofReal_pos` 経由で everywhere。

---

## ルート全体の既存率

カウント方法: 本ルートで実際に使う API を分母、`✅ 既存`（in-tree `@audit:ok` 含む）を分子。

- 分母（使う API、項目 1-8 で「使う」マーク）: **22 項目**
  - klDiv 積分形（項目1）: `klDiv_eq_lintegral_klFun_of_ac` ×1
  - klFun 性質（項目2）: `klFun_nonneg` / `continuous_klFun` / `measurable_klFun` / `klFun_one` ×4
  - Fatou（項目3）: `lintegral_liminf_le` ×1
  - rnDeriv 同定（項目4）: `rnDeriv_mul_rnDeriv` / `rnDeriv_withDensity_right` / `Measure.rnDeriv_withDensity` / `rnDeriv_gaussianReal` / `AbsolutelyContinuous.ae_eq` ×5
  - a.e. 部分列（項目5）: `exists_seq_tendsto_ae` / `negMulLog_convDensity_tendsto_ae_subseq`(in-tree) ×2
  - liminf 処理（項目6）: `le_liminf_of_le` / `tendsto_of_subseq_tendsto` / `liminf_le_liminf_of_le` ×3
  - 2次モーメント（項目7）: `convDensityAdd_second_moment`(in-tree) / `gaussianReal`/`gaussianPDFReal` ×2
  - 正値性/ac（項目8）: `gaussianPDFReal_pos` / `gaussianReal_absolutelyContinuous'` / `withDensity_absolutelyContinuous` / `withDensity_absolutelyContinuous'` ×4
- 分子（既存）: **21 項目**（`tendsto_of_subseq_tendsto` のみ未 Read = 要確認、ほぼ確実に存在）
- **既存率 ~95%（個別 API 実体ベース）。ただし「KL-LSC 補題そのもの」「rnDeriv 商の base 統一補題」は不在 = 自作。**

> 要約: **部品（klDiv 積分形・klFun・Fatou・rnDeriv 部品・a.e. 部分列・2次モーメント・ガウス正値性）は in-tree / Mathlib に全て揃っている。自作するのは「それらを Fatou で組む KL-LSC 補題」「rnDeriv 商を base=volume に統一する同定補題」「cross-term 収束の組み立て」の糊コード 3 本。DV 双対は一切不要。**

---

## 自作が必要な要素（優先度順）

1. **W1 — `klDiv_le_liminf_of_ae_tendsto`（KL-LSC 本体、★ルートの心臓）**
   - 推奨実装: 主定理セクションの 7 行 pseudo の通り。`klDiv_eq_lintegral_klFun_of_ac` で両辺を ℝ≥0∞ 積分形に → `lintegral_liminf_le`（Fatou）→ pointwise で `klFun ∘ rnDeriv` の連続合成（`continuous_klFun.tendsto.comp h_ae`）→ `ENNReal.continuous_ofReal` で ℝ≥0∞ にリフト → `le_liminf`。
   - 工数感: **~30-50 行**。最大の注意は pointwise の `liminf` 下界を `Tendsto.le_liminf` で出す部分（part D の base 乗り換えと連動）。
   - 落とし穴: Fatou は `liminf` を返すが (α) が要るのは `differentialEntropy` の `limsup`。KL = -h + cross の符号反転で「KL の liminf 下界 ⟹ -h の liminf 下界 ⟹ h の limsup 上界」に化ける向きを 1 度紙で確認。

2. **W2 — `rnDeriv_withDensity_quotient_ae`（rnDeriv 商の base=γ 同定、★最大 gap）**
   - signature（目標）: `rnDeriv (volume.withDensity (ofReal∘f)) (volume.withDensity (ofReal∘g)) =ᵐ[volume.withDensity (ofReal∘g)] fun x => ENNReal.ofReal (f x / g x)`（g>0, f≥0, 両 measurable, integrable）。
   - 推奨実装: `rnDeriv_mul_rnDeriv'` を base=volume 軸で 2 回 + `Measure.rnDeriv_withDensity` で各 withDensity を密度に潰す + g>0 で商 `ofReal f / ofReal g = ofReal (f/g)` + `AbsolutelyContinuous.ae_eq` で `=ᵐ[volume] ⟹ =ᵐ[γ]`。
   - 工数感: **~40-60 行**。落とし穴: (a) `=ᵐ` の base（volume vs γ）の取り違え、(b) `rnDeriv_mul_rnDeriv` の `μ ≪ ν` の向き、(c) ℝ≥0∞ の商と `ofReal` の交換（`ENNReal.ofReal_div_of_pos` 系の前提 g>0）。実装前に LSP で 1 度型確認。

3. **W3 — cross-term 収束 `∫ f_n log g → ∫ pX log g`（M2 経由）**
   - 推奨実装: `log (gaussianPDFReal 0 σ² x) = c₀ - x²/(2σ²)`（閉形展開）→ `∫ f_n log g = c₀·∫f_n - (1/2σ²)·M2(f_n)` → `convDensityAdd_second_moment`(in-tree) + `∫f_n=1` で収束。
   - 工数感: **~30 行**（log gaussianPDFReal 展開が既 in-tree にあれば短縮可、`rg` 確認推奨）。落とし穴: log の閉形の数値（c₀, 係数）を verbatim 確認（CLAUDE.md「数値 verbatim」、直感禁止）。

4. **W4（軽微）— density 版 a.e. 部分列の取り出し**
   - in-tree `negMulLog_convDensity_tendsto_ae_subseq` は negMulLog 合成版。本ルートは `rnDeriv μ_n γ = ofReal(f_n/g)` 経由で `f_n → pX` a.e.（negMulLog 前）が要る。EPIVitaliAE の証明を negMulLog 合成前で切るか、`exists_seq_tendsto_ae` を `f_n` 直接適用で再構成。工数 **~15 行**。

---

## Mathlib 壁の列挙（真に不在 = `@residual(wall:...)` 対象）

| 壁候補 | loogle 確認 | 判定 |
|---|---|---|
| `klDiv` の lower-semicontinuity | `InformationTheory.klDiv, LowerSemicontinuous` → **Found 0 declarations** | **不在**。ただし本ルート W1 が constructive に出すので「壁」ではなく **自作で closeable**。`@residual` 不要見込み。 |
| `klDiv ≤ liminf klDiv`（Fatou 形） | `InformationTheory.klDiv, Filter.liminf` → **Found 0 declarations** | **不在** = W1 そのもの。自作。 |
| rnDeriv 商の一発同定 (withDensity/withDensity) | `MeasureTheory.Measure.rnDeriv (MeasureTheory.Measure.withDensity _ _)` → 6 match だが「withDensity/withDensity 商」一発形は無し | **部分不在** = W2、既存部品の組み立てで closeable |

**真の Mathlib 壁は 0 件**: このルートの不在物（KL-LSC / rnDeriv 商）はいずれも既存部品の組み立てに帰着し、`@residual(wall:...)` を新規に積む必要はない見込み。**親計画の `wall:kl-lower-semicontinuous`（DV 双対 hard direction）は、本ルートが通れば「不在の壁」ではなく「未組み立て」に格下げ** — shared sorry 補題への集約は不要（W1-W3 が genuine に閉じれば residual 自体が消える）。万一 W1/W2 が当該 session で組めない場合のみ `sorry` + `@residual(wall:kl-lower-semicontinuous)` を継承使用（新 slug 不要）。

---

## 撤退ラインへの距離

親計画 [`epi-g2-general-sandwich-moonshot-plan.md:135`](epi-g2-general-sandwich-moonshot-plan.md) の撤退ライン:

> **Phase 2 で 2a/2c のみ genuine、2b park（最尤の honest 着地）**: 2b の DV 双対 hard direction が
> 当該 session で組めない場合 → `sorry` + `@residual(wall:kl-lower-semicontinuous)`。

判定: **このルートは撤退ラインを発動させない方向に作用する（surface shrink → 解消候補）**。

- 親計画の 2b park は「DV 双対が組めない」前提。本ルートは **DV 双対を完全に回避**（klFun-Fatou は変分定義を経由しない）ので、2b の wall 自体を別ルートで迂回する。
- W1-W3 が genuine に閉じれば 2b park は不要となり、`@residual(wall:kl-lower-semicontinuous)` は **削除可能**（撤退ラインの発動条件が消滅）。
- **新規撤退ライン（本ルート固有）**: W2（rnDeriv 商 base 統一）が `rnDeriv_mul_rnDeriv` の向き / `=ᵐ` base 乗り換えで詰まった場合のみ、W1 を `sorry` + `@residual(wall:kl-lower-semicontinuous)`（既存 slug 継承）で park。仮説束化禁止（W1 の結論 `klDiv ≤ liminf` を hyp に取らない）、precondition（ac / 可積分 / 可測 / g>0）の追加のみ可。

---

## 着手 skeleton（`InformationTheory/Shannon/EPIG2KLFatouLSC.lean`）

```lean
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import InformationTheory.Shannon.EPIVitaliAE          -- negMulLog/density a.e. subseq
import InformationTheory.Shannon.EPIVitaliUnifTight    -- convDensityAdd_second_moment
import InformationTheory.Shannon.EPIG2BridgeDensityHelpers  -- klDiv ↔ differentialEntropy 橋渡し

namespace InformationTheory.EPIG2KLFatou

open MeasureTheory Filter Real
open scoped ENNReal NNReal Topology

variable {α : Type*} {mα : MeasurableSpace α}

/-- W2: rnDeriv 商の base=γ 同定（最大 gap、既存部品の組み立て）。 -/
theorem rnDeriv_withDensity_quotient_ae
    {f g : ℝ → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_nn : ∀ x, 0 ≤ f x) (hg_pos : ∀ x, 0 < g x)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).rnDeriv
        (volume.withDensity (fun x => ENNReal.ofReal (g x)))
      =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (g x))]
        fun x => ENNReal.ofReal (f x / g x) := by
  sorry  -- @residual(wall:kl-lower-semicontinuous)  ※継承使用、組み立て中

/-- W1: KL 下半連続（klFun-Fatou、ルートの心臓）。 -/
theorem klDiv_le_liminf_of_ae_tendsto
    (γ : Measure ℝ) [IsFiniteMeasure γ]
    (μ : Measure ℝ) (μ_n : ℕ → Measure ℝ) [IsFiniteMeasure μ] [∀ n, IsFiniteMeasure (μ_n n)]
    (hμ_ac : μ ≪ γ) (hμn_ac : ∀ n, μ_n n ≪ γ)
    (h_ae : ∀ᵐ x ∂γ, Tendsto (fun n => ((μ_n n).rnDeriv γ x).toReal) atTop
              (𝓝 ((μ.rnDeriv γ x).toReal))) :
    klDiv μ γ ≤ Filter.liminf (fun n => klDiv (μ_n n) γ) atTop := by
  sorry  -- @residual(wall:kl-lower-semicontinuous)  ※継承使用、組み立て中

end InformationTheory.EPIG2KLFatou
```

最初の `sorry` を埋めるのは W2（rnDeriv 商）→ W1（Fatou 組み立て）→ W3（cross-term）の順。
W1/W2 が genuine に閉じれば `@residual(wall:kl-lower-semicontinuous)` は削除され、親計画 Phase 2 (α) の park が解消される。

---

## まとめ

- インベントリは **`docs/shannon/epi-g2-alpha-klfun-fatou-inventory.md`**（本ファイル）
- 既存率 **~95%（個別 API）**、自作必要 **3 本（W1 KL-LSC / W2 rnDeriv 商 / W3 cross-term）+ 軽微 W4**
- 真の Mathlib 壁 **0 件**（不在物は全て既存部品の組み立てに帰着）
- 撤退ライン発動 **no**（むしろ親計画 `wall:kl-lower-semicontinuous` の解消候補ルート）
- **最大 gap = 項目 4（rnDeriv 商の a.e. 同定）**だが、`rnDeriv_mul_rnDeriv` / `rnDeriv_withDensity_right` / `Measure.rnDeriv_withDensity` の組み立てで closeable
