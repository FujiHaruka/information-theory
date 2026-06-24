# EPI G2 層2 (エントロピー汎関数への持ち上げ) — Mathlib + InformationTheory API 在庫

> 対象: `wall:heatflow-continuity` (`InformationTheory/Shannon/EPIG2HeatFlowContinuity.lean:137`
> `heatFlowEntropyPower_continuousWithinAt_zero`) の「層2」= **密度の L¹ 収束をエントロピー積分の収束に持ち上げる**部分の在庫。
> 親方針: file header GATE verdict (2026-06-03 NO-GO)。本ファイルは在庫調査のみ、実装・計画起草はしない。
> Shannon 側同種文書: [`shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md)。

## 一行サマリ

**層2 を閉じる machinery (DCT / L¹→積分 / Vitali) は Mathlib に完備で、しかも致命的だった有限測度制約は `UnifTight` 経路 (`MeasureTheory.tendsto_Lp_of_tendsto_ae`) で回避可能 = `volume` on ℝ でも使える。** だが層2 の入力である **(i) `f_t → pX` の L¹ 収束 (`t→0⁺`、層1)** と **(ii) `UnifIntegrable {f_t}` / 一様可積分性の witness** が `IsRegularDeBruijnHypV2` の L¹+二次モーメントだけからは導けず、そこが真の壁。ルートA (Vitali/L¹→積分) は machinery 既存・入力欠落、ルートB (Fatou 半連続) は**片側不等式しか出ず等号 pin に不足**。**核命題を閉じる最有力ルートは A** (層1 L¹ 収束 + 一様可積分性を別途自作)。撤退ライン (両ルートが `volume` で塞がれ moonshot) には **触れるが踏み抜かない** — A の machinery は通る、塞がりは入力 (層1 + UI) 側に局所化される。

---

## 主定理の最終形 (再掲)

```lean
-- EPIG2HeatFlowContinuity.lean:137 (verbatim, body = sorry + @residual(wall:heatflow-continuity))
theorem heatFlowEntropyPower_continuousWithinAt_zero
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X Z : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_reg : InformationTheory.Shannon.EPIStamDischarge.IsDeBruijnRegularityHyp X Z P) :
    ContinuousWithinAt
      (fun t : ℝ => entropyPower (P.map (fun ω => X ω + Real.sqrt t * Z ω)))
      (Set.Ioi (0 : ℝ)) 0
```

定義の連鎖 (verbatim 確認済):
- `entropyPower μ := Real.exp (2 * differentialEntropy μ)` (`EntropyPowerInequality.lean:102`)
- `differentialEntropy μ := ∫ x, Real.negMulLog ((μ.rnDeriv volume x).toReal) ∂volume` (`DifferentialEntropy.lean:45`)
- `convDensityAdd pX pY := fun z => ∫ x, pX x * pY (z - x) ∂volume` (`EPIConvDensity.lean:42`)

`Real.exp` (連続) を剥がし、密度 `f_t := convDensityAdd pX (gaussianPDFReal 0 ⟨t,_⟩)` (= `P.map(X+√t·Z)` の密度) で書くと、核は次の収束:

pseudo-Lean (証明戦略、ルートA):
```text
1. exp 合成を剥がす: Continuous Real.exp ∘ (核命題 t↦∫ negMulLog f_t ∂volume が t→0⁺ で連続)
2. 層1: t→0⁺ で f_t → pX in L¹(volume)            -- ❌ 既存補題なし (自作)
3. 一様可積分性: UnifIntegrable {negMulLog f_t} 1 volume  -- ❌ 既存補題なし (自作、UI+UnifTight)
4. Vitali (UnifTight 版): tendsto_Lp_of_tendsto_ae  -- ✅ Mathlib、[IsFiniteMeasure] 不要
   → eLpNorm (negMulLog f_t - negMulLog pX) 1 volume → 0
5. L¹→積分: tendsto_integral_of_L1'                 -- ✅ Mathlib、測度非依存
   → ∫ negMulLog f_t → ∫ negMulLog pX = differentialEntropy(P.map X)
6. ContinuousWithinAt 化 + exp 再合成
```

---

## カテゴリ 1 — Vitali 収束定理 / 一様可積分性 (ルートA: DCT/UI)

### ✅ 既存 (machinery)

| 概念 | Mathlib API | file:line | 状態 | G2 での扱い |
|---|---|---|---|---|
| `UnifIntegrable` 定義 | `MeasureTheory.UnifIntegrable` | `MeasureTheory/Function/UniformIntegrable.lean:67` | ✅ | `{negMulLog f_t}` の UI を主張する対象 |
| `UnifTight` 定義 | `MeasureTheory.UnifTight` | `MeasureTheory/Function/UnifTight.lean:59` | ✅ | **無限測度 Vitali に必須の追加仮説** |
| **L¹→積分 (核 bridge)** | `MeasureTheory.tendsto_integral_of_L1'` | `MeasureTheory/Integral/Bochner/Basic.lean:409` | ✅ | **ルートA step 5 主役** |
| L¹→積分 (lintegral 形) | `MeasureTheory.tendsto_integral_of_L1` | `Bochner/Basic.lean:399` | ✅ | 上の下層 |
| **Vitali (無限測度 OK)** | `MeasureTheory.tendsto_Lp_of_tendsto_ae` | `MeasureTheory/Function/UnifTight.lean:329` | ✅ | **ルートA step 4 主役。`[IsFiniteMeasure]` なし** |
| Vitali (有限測度限定) | `MeasureTheory.tendsto_Lp_finite_of_tendsto_ae` | `MeasureTheory/Function/UniformIntegrable.lean:519` | ✅ (但し finite) | `volume` では**使えない** (下記 box) |
| DCT (filter 形) | `MeasureTheory.tendsto_integral_filter_of_dominated_convergence` | `MeasureTheory/Integral/DominatedConvergence.lean:69` | ✅ | 一様可積分 majorant があれば代替経路 |
| DCT (sequence 形) | `MeasureTheory.tendsto_integral_of_dominated_convergence` | `DominatedConvergence.lean:57` | ✅ | 同上 |
| 連続性版 DCT | `MeasureTheory.continuousWithinAt_of_dominated` | `Bochner/Basic.lean:440` | ✅ | GATE が NO-GO 判定した直接経路 (uniform majorant 要求) |
| UI 構成 (L¹収束から) | `MeasureTheory.unifIntegrable_of_tendsto_Lp` | `UniformIntegrable.lean:553` | ✅ | step 2 が出れば step 3 を自動供給 (循環注意) |

#### 主要補題の verbatim signature

```lean
-- UnifTight.lean:329 — 無限測度で効く Vitali (front direction, a.e. 収束版)
theorem tendsto_Lp_of_tendsto_ae (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (haef : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)
-- 文脈 variable: {α β ι} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β] ...
-- ★ [IsFiniteMeasure μ] 無し。代わりに hut : UnifTight f p μ を要求。

-- Bochner/Basic.lean:409 — L¹ 収束 → 積分収束 (測度非依存、eLpNorm 形)
lemma tendsto_integral_of_L1' {ι} (f : α → G) (hfi : Integrable f μ) {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, F i x ∂μ) l (𝓝 (∫ x, f x ∂μ))
-- ★ [IsFiniteMeasure] / [SigmaFinite] 一切なし。l も汎用 Filter (t→0⁺ の 𝓝[Ioi 0] 0 に適用可)。

-- UnifTight.lean:59 — UnifTight 定義 (s : 有限測度集合の外で Lp ノルム小)
def UnifTight {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ≥0⦄, 0 < ε → ∃ s : Set α, μ s ≠ ∞ ∧ ∀ i, eLpNorm (sᶜ.indicator (f i)) p μ ≤ ε

-- UniformIntegrable.lean:519 — 有限測度限定 Vitali (★ volume では使えない)
theorem tendsto_Lp_finite_of_tendsto_ae [IsFiniteMeasure μ] (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g p μ)
    (hui : UnifIntegrable f p μ) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0)
```

> **無限測度判定 (致命的軸)**: `UnifTight.lean` のファイル header 自身が "version of Vitali's theorem that works also for spaces of infinite measure" と明記。`tendsto_Lp_of_tendsto_ae` (`:329`) と `tendsto_integral_of_L1'` (`:409`) はいずれも `[IsFiniteMeasure]` を要求しない。**`volume` on ℝ で使える。** 唯一の有限測度限定版 `tendsto_Lp_finite_of_tendsto_ae` (`:519`) は `volume` では適用不可だが、`UnifTight` 版が代替する。

> **ℕ-filter 注意**: `tendsto_Lp_of_tendsto_ae` は `f : ℕ → α → β` (sequence 限定)。`t→0⁺` は連続 filter なので、`t→0⁺` の任意列化 (sequential criterion `tendsto_iff_seq_tendsto` を `FirstCountableTopology ℝ` で) を 1 段噛ませる必要がある。`tendsto_integral_of_L1'` 側は汎用 `l : Filter` なので連続のまま乗る — **step 4 だけ列化が要る**のが落とし穴。

---

## カテゴリ 2 — 積分汎関数の半連続性 (ルートB: semicontinuity / Fatou)

### ⚠️ 部分的 (片側のみ)

| 概念 | Mathlib API | file:line | 状態 | G2 での扱い |
|---|---|---|---|---|
| Fatou (lintegral, liminf 形) | `MeasureTheory.lintegral_liminf_le` | `MeasureTheory/Integral/Lebesgue/Add.lean:231` | ✅ | `∫ liminf ≤ liminf ∫`、ℝ≥0∞ のみ・**片側** |
| Fatou (aemeasurable 形) | `MeasureTheory.lintegral_liminf_le'` | `Lebesgue/Add.lean:214` | ✅ | 上の弱仮定版 |
| 弱収束下の半連続 (Portmanteau) | `MeasureTheory.integral_le_liminf_integral_of_forall_isOpen_measure_le_liminf_measure` | `MeasureTheory/Measure/Portmanteau.lean:511` | ✅ | **弱収束専用、L¹ 収束には不適合** |
| 下半連続関数の積分近似 | `MeasureTheory.exists_lt_lowerSemicontinuous_integral_lt` | `Bochner/VitaliCaratheodory.lean` | ✅ | Vitali-Caratheodory、本件には間接的 |
| `negMulLog` 特化半連続性 | — | — | ❌ **不在** (loogle: `LowerSemicontinuous, Real.negMulLog` → Found 0) | — |

```lean
-- Lebesgue/Add.lean:231 — Fatou (ℝ≥0∞ 値、片側不等式のみ)
theorem lintegral_liminf_le {ι : Type*} {f : ι → α → ℝ≥0∞} {u : Filter ι}
    [IsCountablyGenerated u] (h_meas : ∀ i, Measurable (f i)) :
    ∫⁻ a, liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ a, f i a ∂μ) u
-- ★ 測度非依存 (volume OK)。だが ≤ のみ、等号は出ない。
```

> **ルートB 判定 = 等号 pin に不足**。`negMulLog` は `concaveOn (Set.Ici 0)` (`NegMulLog.lean:227`) なので、`∫ negMulLog f_t` の **上半連続** (limsup ≤ ∫ の凹 Jensen 系) なら期待できるが:
> - Fatou (`lintegral_liminf_le`) は ℝ≥0∞ 値・非負被積分関数の **liminf 片側**のみ。`negMulLog` は `x>1` で**負**になる (`negMulLog x = -x log x < 0`) ため ℝ≥0∞ Fatou に直接は乗らない (正部/負部分解が要る)。
> - 半連続は `h(P.map X) ≤ liminf h(f_t)` または `≥ limsup` の**片側**しか与えない。`ContinuousWithinAt` (= 両側 = 極限が値に一致) を pin するには上下両方が要る。**ルートB 単独では核命題 (連続性) を閉じられない。** A の L¹ 収束が等号を直接与えるので A が優位。
> - `negMulLog` 特化の半連続性補題は Mathlib にも InformationTheory にも不在 (Found 0)。

---

## カテゴリ 3 — `Real.negMulLog` の性質 (被積分関数)

### ✅ 既存 (豊富)

| 概念 | Mathlib API | file:line | 状態 | G2 での扱い |
|---|---|---|---|---|
| 定義 | `Real.negMulLog x := -x * log x` | `Analysis/SpecialFunctions/Log/NegMulLog.lean:164` | ✅ | 被積分関数本体 |
| 連続性 | `Real.continuous_negMulLog` | `NegMulLog.lean:186` | ✅ (`@[fun_prop]`) | step 6 / a.e. 連続性供給 |
| `negMulLog 0 = 0` | `Real.negMulLog_zero` | `NegMulLog.lean:170` | ✅ (`@[simp]`) | 台境界処理 |
| `negMulLog 1 = 0` | `Real.negMulLog_one` | `NegMulLog.lean:172` | ✅ (`@[simp]`) | — |
| 非負性 (`[0,1]` 上) | `Real.negMulLog_nonneg` | `NegMulLog.lean:174` | ✅ | `(h1 : 0 ≤ x) (h2 : x ≤ 1) → 0 ≤ negMulLog x` |
| **上界 `≤ 1 - x`** | `Real.negMulLog_le_one_sub_self` | `NegMulLog.lean:234` | ✅ | `(h0 : 0 ≤ x) → x.negMulLog ≤ 1 - x` |
| 凹性 | `Real.concaveOn_negMulLog` | `NegMulLog.lean:227` | ✅ | `ConcaveOn ℝ (Set.Ici 0) negMulLog`、ルートB の Jensen に必要 |
| 厳密凹 | `Real.strictConcaveOn_negMulLog` | `NegMulLog.lean:224` | ✅ | — |
| 導関数 | `Real.hasDerivAt_negMulLog` | `NegMulLog.lean:212` | ✅ | `(hx : x ≠ 0) → HasDerivAt negMulLog (-log x - 1) x` |

```lean
-- NegMulLog.lean:234 — 上界 (★ 1/e ではなく 1 - x。x≥0 全域で有効、x=1 で 0 タッチ)
lemma negMulLog_le_one_sub_self {x : ℝ} (h0 : 0 ≤ x) : x.negMulLog ≤ 1 - x
-- NegMulLog.lean:174 — 非負は [0,1] 限定。x > 1 では負。
lemma negMulLog_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x
```

> **`1/e` 上界は不在 / 不要**: ブリーフ想定の `negMulLog x ≤ 1/e` は Mathlib に直接の名前では無いが、`negMulLog_le_one_sub_self` (`≤ 1-x`) が上から押さえる。だが**下から**(負部) は `x>1` で `-x log x → -∞` のため**有界でない** → 単一の `t`-uniform 可積分 majorant が `negMulLog f_t` に存在しない、という GATE NO-GO の根拠と整合 (検証済)。被積分関数の符号構造そのものが DCT 直接適用を塞いでいる。

---

## カテゴリ 4 — mollifier / approximate identity の L¹ 収束 (層1 = B-1 の足場)

### ❌ 不在 (本件向き L¹ 収束) / ✅ 周辺素材

| 概念 | Mathlib / InformationTheory API | file:line | 状態 | G2 での扱い |
|---|---|---|---|---|
| bump 畳み込み収束 (pointwise/一様) | `convolution_tendsto_right` | `Mathlib/Analysis/Convolution.lean:787` | ✅ (但し pointwise/uniform) | **L¹ 収束ではない、一般 L¹ `pX` に不適合** |
| ContDiffBump 近似 | `ContDiffBump.convolution_tendsto_right` | `Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean` | ✅ (但し bump 限定) | gaussianPDF は ContDiffBump でない |
| `convDensityAdd` 定義 | `InformationTheory.Shannon.convDensityAdd` | `EPIConvDensity.lean:42` | ✅ | `f_t` の本体 (`∫ x, pX x * pY (z-x)`) |
| `convDensityAdd` 可換 | `convDensityAdd_comm` | `EPIConvDensity.lean:47` | ✅ | 補助 |
| 空間裾の収束 (`z→±∞`) | `tendsto_convDensityAdd_gaussian_zero` | `EPIConvDensityRegular.lean:148` | ✅ (但し `z→±∞`) | **`t→0⁺` ではなく `z→±∞`。層1 には使えない** |
| `negMulLog (convDensityAdd)` 可積分性 (固定 t) | `convDensityAdd_negMulLog_integrable` | `FisherInfoV2DeBruijnAssembly.lean:2529` (`private`) | ✅ (固定 t) | step 5 の `Integrable (F i)` を各 t で供給。`private` で file 外不可 |
| **`f_t → pX` の L¹ 収束 (`t→0⁺`)** | — | — | ❌ **不在 (真壁)** | **層1 の核、完全自作** |

```lean
-- EPIConvDensityRegular.lean:148 — ★ z→±∞ (空間裾) の収束。t→0⁺ ではない。誤用注意。
theorem tendsto_convDensityAdd_gaussian_zero {pX : ℝ → ℝ} {v : ℝ≥0}
    (hv : v ≠ 0) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_int : Integrable pX volume)
    {l : Filter ℝ} [l.IsCountablyGenerated]
    (hl : Filter.Tendsto (fun z : ℝ => z) l Filter.atTop ∨
          Filter.Tendsto (fun z : ℝ => z) l Filter.atBot) :
    Filter.Tendsto (convDensityAdd pX (gaussianPDFReal 0 v)) l (nhds 0)

-- FisherInfoV2DeBruijnAssembly.lean:2529 — 固定 t での可積分性 (private、L¹+二次モーメント前提)
private theorem convDensityAdd_negMulLog_integrable
    (pX : ℝ → ℝ) (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume) (hpX_mass : (∫ y, pX y ∂volume) = 1)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x =>
      Real.negMulLog (convDensityAdd pX (gaussianPDFReal 0 ⟨t, ht.le⟩) x)) volume
```

> **層1 (`f_t → pX` in L¹, `t→0⁺`) は Mathlib にも InformationTheory にも不在**。`convolution_tendsto_right` は (a) pointwise/uniform 収束で L¹ ではない、(b) bump/連続 kernel 前提で**一般 L¹ `pX`** に効かない。「ガウス分散→0 → 恒等近似 → L¹ 収束」の一般定理が Mathlib に無い。**これが層1 の真壁。** ただし数学的には標準事実 (近似恒等の L¹ 収束、Young 不等式 + 連続関数の L¹ 稠密 + translation continuity)。素材 (`MemLp.tendsto_Lp` / translation-continuity 系) は散在するが組み上げは未整備。

---

## カテゴリ 5 — differentialEntropy / entropyPower の既存連続性・半連続性 (再確認)

### ❌ 完全不在 (verbatim 否定記録)

| クエリ | 結果 |
|---|---|
| `rg "(Continuous\|ContinuousWithinAt\|ContinuousOn\|LowerSemicontinuous\|UpperSemicontinuous).*(differentialEntropy\|entropyPower)"` (InformationTheory 全体) | **0 件** (header コメント文字列のみヒット、補題なし) |
| `Continuous, InformationTheory.Shannon.differentialEntropy` (loogle) | index 未登録 (2026-05-10 build < 当該定義) → rg で代替確認、**0 件** |
| `LowerSemicontinuous, InformationTheory.Shannon.entropyPower` (loogle) | index 未登録 → rg で代替確認、**0 件** |
| `LowerSemicontinuous, Real.negMulLog` (loogle) | **Found 0 declarations** |

> loogle index は 2026-05-10 build で当該 InformationTheory 定義より古いため namespace 解決不可。rg フォールバックで確認した結果、`differentialEntropy` / `entropyPower` の連続性・半連続性補題は **InformationTheory にゼロ**。Mathlib 側には `differentialEntropy` / `entropyPower` 概念自体が無い (Shannon entropy infra 不在、`shannon-mathlib-inventory.md` 既述)。**file header の "loogle: 0 declarations" 記述は正確。**

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`tendsto_Lp_of_tendsto_ae` (UnifTight.lean:329)** — 無限測度 Vitali。要求: `(hp : 1 ≤ p)`, `(hp' : p ≠ ∞)`, `(haef : ∀ n, AEStronglyMeasurable (f n) μ)`, `(hg' : MemLp g p μ)`, **`(hui : UnifIntegrable f p μ)`**, **`(hut : UnifTight f p μ)`**, `(hfg : a.e. pointwise 収束)`。`f : ℕ → α → β` (**sequence 限定**)。`UnifIntegrable` + `UnifTight` が両方必要で、これらが層1 の外で**未供給** = 自作対象。
- **`tendsto_integral_of_L1'` (Bochner/Basic.lean:409)** — 測度・filter 非依存。要求: `(hfi : Integrable f μ)` (極限 `pX` 側の可積分性 = `pX` が L¹、`pX_law` から取れる), `(hFi : ∀ᶠ i in l, Integrable (F i) μ)` (各 `negMulLog f_t` 可積分 = `convDensityAdd_negMulLog_integrable` だが `private`), `(hF : eLpNorm 収束)`。**`private` 補題 `convDensityAdd_negMulLog_integrable` を file 跨ぎで使うには public 化 or 再証明が要る** (落とし穴)。
- **`continuousWithinAt_of_dominated` (Bochner/Basic.lean:440)** — GATE が NO-GO 判定した直接経路。要求: `(bound_integrable : Integrable bound μ)` + `(h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a, ‖F x a‖ ≤ bound a)` = **`t`-uniform 可積分 majorant**。`IsRegularDeBruijnHypV2` (L¹+二次モーメントのみ、L∞/連続性なし、`FisherInfoV2DeBruijn.lean:205-268` 全フィールド verbatim 確認済) から構成不可。負部 `-x log x` (x>1) が unbounded のため理論的にも単一 majorant 不存在。
- **`negMulLog` 符号構造** — `[0,1]` で非負・`x>1` で負・`x→∞` で `-∞`。DCT 直接適用 (majorant) を塞ぐ根本原因。L¹ 収束ルート (A) は majorant 不要なので回避できる。

---

## 自作が必要な要素 (優先度順)

1. **【最重要・真壁】層1: `f_t → pX` の L¹ 収束 (`t→0⁺`)** — `Tendsto (fun t => eLpNorm (convDensityAdd pX g_t - pX) 1 volume) (𝓝[Ioi 0] 0) (𝓝 0)`。近似恒等の標準事実だが Mathlib 未整備。工数感: **80〜150 行** (連続関数 L¹ 稠密 + translation continuity in L¹ + Young。`MemLp` 系素材は散在)。落とし穴: gaussianPDF は compact support でない (ContDiffBump 不可) ので tail 評価が要る。**ここが真の moonshot 候補。**
2. **【重要】`UnifIntegrable {negMulLog f_t} 1 volume` + `UnifTight`** — Vitali (step 4) の 2 仮説。`unifIntegrable_of_tendsto_Lp` (`:553`) は L¹ 収束から UI を出すが、それは `negMulLog f_t` の L¹ 収束を別途要する (= 1 と循環気味)。`UnifTight` は二次モーメント `pX_mom` から tail 評価で構成できる見込み (有限分散 → 遠方で密度小)。工数感: **40〜80 行**。
3. **【中】`convDensityAdd_negMulLog_integrable` の public 化** — 現状 `private` (`:2529`)。file 跨ぎ参照のため public alias or 共有 sorry 補題化。工数感: **5〜15 行** (純 plumbing)。
4. **【中】`t→0⁺` filter の sequential 化** — `tendsto_Lp_of_tendsto_ae` が `ℕ` sequence 限定なので、`FirstCountableTopology ℝ` の `tendsto_iff_seq_tendsto` で連続 filter を任意列に落とす bridge。工数感: **15〜30 行**。落とし穴: 列ごとに UI/UnifTight を供給する形に整える必要。
5. **【小】exp 合成 + ContinuousWithinAt 化** — `Real.continuous_exp.comp` + `tendsto_integral_of_L1'` の極限を `ContinuousWithinAt` に翻訳。工数感: **20〜40 行**。

合計工数感: **160〜315 行** (層1 が支配項)。

---

## Mathlib 壁の列挙 (`@residual(wall:...)` 対象)

| 壁 | 内容 | loogle/rg 確認 | 集約推奨 |
|---|---|---|---|
| `wall:heatflow-continuity` (既存) | `entropyPower`/`differentialEntropy` の `t→0⁺` 端点連続性 | `Continuous, differentialEntropy/entropyPower` → rg 0 件、Mathlib に概念不在 | 既存 shared sorry `heatFlowEntropyPower_continuousWithinAt_zero` に集約済 |
| 層1 L¹ 収束 (本調査で局所化) | 近似恒等 `convDensityAdd pX g_t → pX` in L¹ as `t→0⁺` | `convolution_tendsto_right` は pointwise/bump 限定、L¹ 一般版 0 件。`tendsto_convDensityAdd_gaussian_zero` は `z→±∞` で別物 | **新規 shared sorry 補題候補** (`approxIdentity_tendsto_L1` 等)。複数 EPI consumer で再利用見込み |
| `negMulLog` 半連続性 | `LowerSemicontinuous, Real.negMulLog` | **Found 0 declarations** | ルートB を採れば必要だが A 優先なら不要 |

> **集約方針**: 層2 全体は `wall:heatflow-continuity` の sorry 1 本に既に集約されている。層1 を別 shared sorry 補題に切り出すと、(a) 層2 の machinery (Vitali/L¹→積分) が genuine に閉じ、(b) 壁が「近似恒等の L¹ 収束」という**より小さく・より標準的・上流 PR 化しやすい**命題に縮小する。これは honesty gain (surface shrink) の正規パターン。詳細 → `docs/audit/audit-tags.md`「共有 Mathlib 壁: shared sorry 補題パターン」。

---

## 撤退ラインへの距離

親方針 (file header GATE verdict 2026-06-03 NO-GO) の撤退ライン:

> ルートA (Vitali/DCT) とルートB (semicontinuity) が**双方とも無限測度 `volume` で塞がれる**場合 → 真 moonshot (Mathlib PR or 100行超自作)。

**判定: 触れるが踏み抜かない (部分的)。**

- **ルートA machinery は `volume` で塞がれていない** — `tendsto_Lp_of_tendsto_ae` (UnifTight 版) + `tendsto_integral_of_L1'` がいずれも `[IsFiniteMeasure]` 不要。**本調査の最重要 positive 発見**。GATE が想定した「Vitali は有限測度限定」は `tendsto_Lp_finite_of_tendsto_ae` (`:519`) だけの話で、`UnifTight` 経路を見落としていた可能性。
- **塞がりは入力側に局所化** — 塞がっているのは machinery でなく層1 (L¹ 収束) + UI/UnifTight witness の**自作必要性**。これは「100行超自作」域だが「Mathlib PR 不可避」ではない (素材は散在するが存在する)。
- **ルートB は等号 pin 不足で核命題に到達できない** (片側半連続のみ) — A が優位。

**縮退案 (新規撤退ライン提案)**: 層1 L¹ 収束を 2 週間で書けない場合 → 層1 を独立 shared sorry 補題 `wall:approx-identity-L1` として切り出し、層2 (Vitali + L¹→積分 + exp) を genuine に閉じる。これにより `heatFlowEntropyPower_continuousWithinAt_zero` の sorry は「端点連続性全体」から「近似恒等の L¹ 収束」へ縮小 = honesty surface shrink。撤退口は sorry + `@residual(wall:approx-identity-L1)`、仮説束化禁止 (`*Hypothesis` predicate に L¹ 収束を bundle するのは load-bearing → 禁止)。

---

## 着手 skeleton

```lean
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Exp
import InformationTheory.Shannon.EPIConvDensity
import InformationTheory.Shannon.EPIConvDensityRegular
import InformationTheory.Shannon.DifferentialEntropy
import InformationTheory.Shannon.EntropyPowerInequality

namespace InformationTheory.Shannon

open MeasureTheory Real ProbabilityTheory Filter
open scoped ENNReal NNReal

/-- **層1 (真壁候補)** — 近似恒等の L¹ 収束: 分散 `t→0⁺` の Gaussian 核との畳み込み
`convDensityAdd pX g_t` が L¹(volume) で `pX` に収束。Mathlib `convolution_tendsto_right`
は pointwise/bump 限定で一般 L¹ `pX` に効かず、`tendsto_convDensityAdd_gaussian_zero` は
`z→±∞` で別物。標準事実だが Mathlib 未整備。
@residual(wall:approx-identity-L1) -/
theorem convDensityAdd_tendsto_L1_zero
    {pX : ℝ → ℝ} (hpX_nn : ∀ x, 0 ≤ pX x) (hpX_meas : Measurable pX)
    (hpX_int : Integrable pX volume)
    (hpX_mom : Integrable (fun y => y ^ 2 * pX y) volume) :
    Tendsto (fun t : ℝ =>
      eLpNorm (convDensityAdd pX (gaussianPDFReal 0 ⟨t, by positivity⟩) - pX) 1 volume)
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  sorry

/-- **層2 (machinery、genuine 化目標)** — 密度の L¹ 収束 → エントロピー積分の収束。
層1 を仮定すれば Mathlib の `tendsto_integral_of_L1'` (測度非依存) で閉じる。 -/
theorem differentialEntropy_tendsto_of_L1
    {pX : ℝ → ℝ} (hpX : Integrable pX volume) :
    -- 入力: 層1 の L¹ 収束 (convDensityAdd_tendsto_L1_zero) + 各 t の可積分性
    -- 結論: ∫ negMulLog f_t → ∫ negMulLog pX (= differentialEntropy(P.map X))
    True := by
  sorry  -- ルートA: tendsto_integral_of_L1' + sequential 化 (本体は genuine machinery)

end InformationTheory.Shannon
```

> skeleton は方向性提示のみ (planner/implementer の責務)。層2 の `True` placeholder は本ファイルでは形を示すためで、実装時は本来の `Tendsto (fun t => differentialEntropy ...) (𝓝[Ioi 0] 0) (𝓝 ...)` に置換すること (`:True` slot は honesty defect、本 inventory はコードでないため記述に留める)。
