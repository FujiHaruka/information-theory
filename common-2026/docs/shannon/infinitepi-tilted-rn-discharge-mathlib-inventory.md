# infinitePi-tilted RN (Chernoff/Cramér per-tilt) — Mathlib feasibility inventory

> Feasibility 調査 (2026-05-20)。撤退ライン参照元: `docs/textbook-roadmap.md` line 387–393
> (T1-C Cramér L-D3 撤退) + `docs/shannon/cramer-lc2-ext-moonshot-plan.md`。
> 在庫対象 gap: `Common2026/Shannon/CramerLC2PhaseC.lean:84` の `IsMeasureInfinitePiTiltedEq`
> と `Common2026/Shannon/ChernoffPerTiltDischarge.lean:136` の `IsBayesErrorPerTiltLowerBound`。
>
> 同種文書: `docs/shannon/cramer-mathlib-inventory.md`, `docs/shannon/chernoff-mathlib-inventory.md`。

## 一行サマリ

数学的核心 (`infinitePi × tilted` の n-letter RN-deriv 恒等式) を支える Mathlib API は
**single-coordinate 版が 100% 既存** (`tilted_mul_apply_cgf` が n=1 の RN-deriv 恒等式そのもの)
だが、**それを無限積/有限積に持ち上げる multiplicative bridge は 0% 既存** —
`Measure.pi`/`infinitePi` × `tilted` の互換性、`Measure.pi`/`prod` の `rnDeriv` 因子分解、
`Measure.pi`/`infinitePi` の絶対連続性、いずれも loogle で **`Found 0`** を確認。
verdict は **(c)** に近い **(b)/(c) 境界**: 部品は揃うが繋ぎが ~250–400 行の自前構築。
**PIVOT 推奨** (1 セッション完遂不可、過去の L-D3 撤退と整合)。

---

## 主定理の最終形 (再掲)

`Common2026/Shannon/CramerLC2PhaseC.lean:84` の pass-through 述語 (= 撤退で抽象化した Mathlib gap):

```lean
def IsMeasureInfinitePiTiltedEq (μ₀ : Measure Ω₀) (Y : Ω₀ → ℝ) (lam : ℝ) : Prop :=
  ∀ a ε : ℝ, 0 < ε → ∃ C > 0, ∀ᶠ n : ℕ in atTop,
      C * Real.exp (-(n:ℝ) * (lam * a - cgf Y μ₀ lam + lam * ε))
        ≤ (Measure.infinitePi (fun _ : ℕ => μ₀)).real
            {ω : ℕ → Ω₀ | (a:ℝ) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)}
```

これを 0-sorry で割るには、Cover-Thomas の Cramér change-of-measure 下界:

```text
-- pseudo-Lean: 真に証明すべき core (Mathlib gap `Measure.infinitePi_tilted_eq`)
-- 1. event E_n := {ω | a·n ≤ ∑_{i<n} Y(ωᵢ)} は range n 上の cylinder
-- 2. μ.real E_n = (Measure.pi (fun i:range n => μ₀)).real (finite event)      -- infinitePi_cylinder/infinitePi_pi
-- 3. (Measure.pi μ₀^n).tilted (∑ i, lam·Y∘eval i) = Measure.pi (fun _ => μ₀.tilted (lam·Y·))  -- ★ Mathlib gap (Found 0)
-- 4. ∀ s, μ.real s = ∫ rnDeriv ... ∂μ_tilt  with  rnDeriv = exp(lam·∑Y − n·Λ(lam))           -- ★ n-letter RN identity (Found 0)
-- 5. μ_tilt(E_n) → 1 (tilted LLN) は既存 CramerLC2DischargeExt.tilted_lln_in_probability_real
-- 6. 4×5 で change-of-measure 下界、定数 C と exp(-n(λa−Λ+λε)) を抽出
```

`ChernoffPerTiltDischarge.IsBayesErrorPerTiltLowerBound` (`:136`) は同じ核を pmf-level
(`bayesErrorMinPmf`) で抽象化しており、measure-theoretic な `infinitePi` を**経由していない**
(Sanov LDP 出力 `C·Z(λ)^n ≤ 2·bayesErrorMinPmf` の形)。よって Chernoff 側 0-sorry 化も
**同じ core (step 3+4)** を pmf→`Measure α` lift (`chernoffMediatorMeasure`, `:407` 既実装) 経由で
要求する。**両者は同根**。

---

## API 在庫テーブル

### A. `Measure.tilted` の n=1 RN-deriv / cgf 恒等式 (`Mathlib/Probability/Moments/Tilted.lean`, `Mathlib/MeasureTheory/Measure/Tilted.lean`)

| 概念 | Mathlib API | file:line | 状態 | 当 gap での扱い |
|---|---|---|---|---|
| **n=1 RN-deriv 恒等式 (cgf 形)** | `ProbabilityTheory.tilted_mul_apply_cgf` | `Mathlib/Probability/Moments/Tilted.lean:59` | ✅ 既存 | **core の n=1 版そのもの**。step 4 を 1-coordinate で実現 |
| tilted apply (cgf, 可測前提) | `ProbabilityTheory.tilted_mul_apply_cgf'` | `Tilted.lean:52` | ✅ | 可測版 |
| tilted apply (mgf 形) | `ProbabilityTheory.tilted_mul_apply_mgf` | `Tilted.lean:48` | ✅ | mgf 経路 |
| setIntegral tilted (cgf) | `ProbabilityTheory.setIntegral_tilted_mul_eq_cgf` | `Tilted.lean:112` | ✅ | 積分形 change-of-measure |
| **tilted の rnDeriv (自己基準)** | `MeasureTheory.rnDeriv_tilted_left_self` | `Mathlib/MeasureTheory/Measure/Tilted.lean:360` | ✅ | `(μ.tilted f).rnDeriv μ =ᵐ[μ] exp(f)/∫exp(f)` |
| log rnDeriv (自己基準) | `MeasureTheory.log_rnDeriv_tilted_left_self` | `Tilted.lean:366` | ✅ | `f − log∫exp(f)` 形 |
| tilted ≪ base | `MeasureTheory.tilted_absolutelyContinuous` | `Tilted.lean:280` | ✅ | step 4 の ac 前提 (1-coord) |
| base ≪ tilted | `MeasureTheory.absolutelyContinuous_tilted` | `Tilted.lean:283` | ✅ | 逆向き ac |
| tilted_tilted (合成) | `MeasureTheory.tilted_tilted` | `Tilted.lean:251` | ✅ | `(μ.tilted f).tilted g = μ.tilted (f+g)` |
| isProbabilityMeasure_tilted | `MeasureTheory.isProbabilityMeasure_tilted` | `Tilted.lean:126` | ✅ | tilted が確率測度 |

`tilted_mul_apply_cgf` 完全 signature (逐語):
```lean
lemma tilted_mul_apply_cgf [SFinite μ] (s : Set Ω) (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ
```
- 型クラス前提: `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {t : ℝ}` + `[SFinite μ]`
- 引数: `(s : Set Ω)`, `(ht : Integrable (fun ω ↦ exp (t * X ω)) μ)`
- 結論: `μ.tilted (t * X ·) s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ`

`rnDeriv_tilted_left_self` 完全 signature (逐語):
```lean
lemma rnDeriv_tilted_left_self [SigmaFinite μ] (hf : AEMeasurable f μ) :
    (μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ)
```
- 型クラス前提: `{α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}` + `[SigmaFinite μ]`
- 引数: `(hf : AEMeasurable f μ)`
- 結論: `(μ.tilted f).rnDeriv μ =ᵐ[μ] fun x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ)`

### B. `Measure.infinitePi` cylinder / restriction / pushforward (`Mathlib/Probability/ProductMeasure.lean`)

| 概念 | Mathlib API | file:line | 状態 | 当 gap での扱い |
|---|---|---|---|---|
| **cylinder の質量** | `MeasureTheory.Measure.infinitePi_cylinder` | `ProductMeasure.lean:514` | ✅ | step 2: `infinitePi μ (cylinder s S) = Measure.pi (fun i:s => μ i) S` |
| **box の質量** | `MeasureTheory.Measure.infinitePi_pi` | `ProductMeasure.lean:402` | ✅ | step 2 別経路: `= ∏ i∈s, μ i (t i)` |
| 有限 restrict pushforward | `MeasureTheory.Measure.infinitePi_map_restrict` | `ProductMeasure.lean:374` | ✅ | cylinder ↔ `Measure.pi` |
| 射影極限性 | `MeasureTheory.Measure.isProjectiveLimit_infinitePi` | `ProductMeasure.lean:363` | ✅ | uniqueness / Kolmogorov |
| **coord-wise map pushforward** | `MeasureTheory.Measure.infinitePi_map_pi` | `ProductMeasure.lean:482` | ✅ | `(infinitePi μ).map (fun x i => f i (x i)) = infinitePi (fun i => (μ i).map (f i))` — tilt 自体ではない |
| eval pushforward | `MeasureTheory.Measure.infinitePi_map_eval` | `ProductMeasure.lean:478` | ✅ | 既に CramerLC2Discharge で多用 |
| cylinder 上 lintegral | `MeasureTheory.lintegral_restrict_infinitePi` | `ProductMeasure.lean:576` | ✅ | step 4 を cylinder へ落とす |
| piFinset lintegral | `MeasureTheory.lintegral_infinitePi_of_piFinset` | `ProductMeasure.lean:595` | ✅ | finite-dep 関数の積分 |
| 有限版同一視 | `MeasureTheory.Measure.infinitePi_eq_pi` | `ProductMeasure.lean:509` | ✅ | `[Fintype ι]` で `Measure.pi` に一致 |
| 確率測度 instance | `MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi` | `ProductMeasure.lean:378` | ✅ | ただし beta-redex 不一致 (下記) |

`infinitePi_cylinder` 完全 signature (逐語):
```lean
lemma infinitePi_cylinder {s : Finset ι} {S : Set (Π i : s, X i)} (mS : MeasurableSet S) :
    infinitePi μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S
```
- 型クラス前提 (section variable): `{ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]`
  `(μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]`
- 引数: `{s : Finset ι}`, `{S : Set (Π i : s, X i)}`, `(mS : MeasurableSet S)`
- 結論: `infinitePi μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S`

`infinitePi_map_pi` 完全 signature (逐語):
```lean
lemma infinitePi_map_pi {Y : ι → Type*} [∀ i, MeasurableSpace (Y i)] {f : (i : ι) → X i → Y i}
    (hf : ∀ i, Measurable (f i)) :
    (infinitePi μ).map (fun x i ↦ f i (x i)) = infinitePi (fun i ↦ (μ i).map (f i))
```
- 結論: `(infinitePi μ).map (fun x i ↦ f i (x i)) = infinitePi (fun i ↦ (μ i).map (f i))`
- 注: これは push-forward of coord-wise *map*。**tilt は coord-wise map ではなく withDensity** なので
  直接は流用不可。tilt を「density 乗算」ではなく構成的に書くと無限積では破綻する。

### C. 独立 RV の mgf/cgf 加法性 (`Mathlib/Probability/Moments/Basic.lean`)

| 概念 | Mathlib API | file:line | 状態 | 当 gap での扱い |
|---|---|---|---|---|
| **mgf of sum (iid)** | `ProbabilityTheory.iIndepFun.mgf_sum` | `Basic.lean:378` | ✅ | `mgf (∑X) = ∏ mgf X` |
| **cgf of sum** | `ProbabilityTheory.iIndepFun.cgf_sum` | `Basic.lean:393` | ✅ | `cgf (∑X) = ∑ cgf X` → `= n·Λ(lam)` で exponent 同一視 |
| mgf sum (identDistrib) | `ProbabilityTheory.mgf_sum_of_identDistrib` | `Basic.lean:417` | ✅ | `mgf (∑X) = mgf X ^ #s` |
| **Chernoff 上界** | `ProbabilityTheory.measure_ge_le_exp_mul_mgf` | `Basic.lean:429` | ✅ | upper tail (Cramér *upper* 側、本 gap の逆向き) |
| mgf_map (push-forward) | `ProbabilityTheory.mgf_map` | (Moments/Basic) | ✅ | CramerLC2Discharge で `cgf_eval_eq_cgf_base` に既用 |

`iIndepFun.cgf_sum` 完全 signature (逐語):
```lean
theorem iIndepFun.cgf_sum {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    {s : Finset ι} (h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ) :
    cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, cgf (X i) μ t
```
- 型クラス前提: `{ι Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {t : ℝ}`
  (`iIndepFun X μ` 内部で `IsProbabilityMeasure μ` を導出)
- 引数: `(h_indep : iIndepFun X μ)`, `(h_meas : ∀ i, Measurable (X i))`,
  `{s : Finset ι}`, `(h_int : ∀ i ∈ s, Integrable (fun ω => exp (t * X i ω)) μ)`
- 結論: `cgf (∑ i ∈ s, X i) μ t = ∑ i ∈ s, cgf (X i) μ t`

### D. RN-deriv による change-of-measure 一般 API (`Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`)

| 概念 | Mathlib API | file:line | 状態 | 当 gap での扱い |
|---|---|---|---|---|
| **`setLIntegral_rnDeriv`** | `MeasureTheory.Measure.setLIntegral_rnDeriv` | `RadonNikodym.lean:333` | ✅ | `∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s` (if `μ ≪ ν`) — step 4 の汎用骨格 |
| setLIntegral_rnDeriv' | `MeasureTheory.Measure.setLIntegral_rnDeriv'` | `RadonNikodym.lean:328` | ✅ | `[HaveLebesgueDecomposition]` 版 |
| lintegral_rnDeriv | `MeasureTheory.Measure.lintegral_rnDeriv` | `RadonNikodym.lean:338` | ✅ | univ 版 |
| withDensity_apply | `MeasureTheory.withDensity_apply` | `Mathlib/MeasureTheory/Measure/WithDensity.lean` | ✅ | tilt = withDensity の apply |

`setLIntegral_rnDeriv` 完全 signature (逐語):
```lean
lemma setLIntegral_rnDeriv [HaveLebesgueDecomposition μ ν] [SFinite ν]
    (hμν : μ ≪ ν) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s
```
- 型クラス前提: `{α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}` + `[HaveLebesgueDecomposition μ ν] [SFinite ν]`
- 引数: `(hμν : μ ≪ ν)`, `{s : Set α}`, `(hs : MeasurableSet s)`
- 結論: `∫⁻ x in s, μ.rnDeriv ν x ∂ν = μ s`

### E. 不在確定 (loogle `Found 0` で authoritative に確認) — ★ これが gap の本体

| 探した概念 | loogle query | 結果 | 帰結 |
|---|---|---|---|
| **`Measure.pi` × `tilted` 互換** | `MeasureTheory.Measure.pi, MeasureTheory.Measure.tilted` | **`Found 0`** | 有限積の tilt 因子分解が無い (step 3 の有限版) |
| **`infinitePi` × `tilted` 互換** | `MeasureTheory.Measure.infinitePi, MeasureTheory.Measure.tilted` | **`Found 0`** | 無限積の tilt 因子分解が無い (step 3) |
| **`Measure.prod` × `tilted`** | `MeasureTheory.Measure.tilted, MeasureTheory.Measure.prod` | **`Found 0`** | 2-factor すら無い |
| **`Measure.pi` rnDeriv 因子分解** | `MeasureTheory.Measure.rnDeriv, MeasurableSpace.pi` | **`Found 0`** | product RN-deriv = ∏ rnDeriv が無い (step 4) |
| **`Measure.prod` rnDeriv** | `MeasureTheory.Measure.rnDeriv, MeasureTheory.Measure.prod` | **`Found 0`** | 2-factor RN すら無い |
| **`Measure.pi` × `withDensity`** | `MeasureTheory.Measure.pi, MeasureTheory.Measure.withDensity` | **`Found 0`** | withDensity の積分解が無い (tilt = withDensity なので致命) |
| **`Measure.pi` 絶対連続性** | `AbsolutelyContinuous, MeasurableSpace.pi, Measure.pi` | **`Found 0`** | `pi μ_tilt ≪ pi μ` が無い (step 4 の ac 前提) |
| **`infinitePi` 絶対連続性** | `infinitePi, AbsolutelyContinuous` | **`Found 0`** | 同上、無限版 |
| **`tilted (∑ ...)` 形** | `MeasureTheory.Measure.tilted _ (∑ _ ∈ _, _)` | **`Found 0`** | sum-exponent tilt の専用補題なし |
| **`tilted` × `map`** | `MeasureTheory.Measure.tilted, MeasureTheory.Measure.map` | **`Found 0`** | tilt と pushforward の交換則なし |
| Cramér / LDP / Sanov 定理本体 | (file 検索 `*cramer* *largedeviation* *chernoff*`) | **不在** | Mathlib に Cramér/LDP/Sanov 定理は存在しない |

---

## 主要前提条件ボックス (前提事故が起きやすい lemma)

- **`tilted_mul_apply_cgf` (n=1 RN 恒等式)**: `[SFinite μ]` + `Integrable (fun ω ↦ exp (t * X ω)) μ`。
  `Y` bounded なら exp も有界で integrable は自明 (CramerLC2Discharge で `isProbabilityMeasure_tilted_of_bounded` 経由)。
  **罠**: `μ = 0` の boundary を `rcases eq_zero_or_neZero` で潰す内部構造 — 直接呼び出しでは確率測度なので問題なし。
- **`infinitePi_cylinder`**: section variable で `[hμ : ∀ i, IsProbabilityMeasure (μ i)]` を要求。
  **罠 (実証済み)**: `μ i = (fun _ : ℕ => μ₀.tilted ...) i` の **beta-redex を instance synthesis が β-簡約しない** —
  `CramerLC2Discharge.lean:38-44` の Phase B blocker、`CramerLC2DischargeExt.lean:85`
  `isProbabilityMeasure_infinitePi_tilted_of_bounded` で `haveI` 二段重ねで迂回済み。
  無限積 tilt を扱う**全 step でこの迂回 lemma を haveI で先置きする必要**。
- **`setLIntegral_rnDeriv`**: `[HaveLebesgueDecomposition μ ν] [SFinite ν]` + `μ ≪ ν`。
  product 上の `HaveLebesgueDecomposition` / `μ_tilt^n ≪ μ^n` は **E 行の通り Mathlib 不在** —
  これを自前で立てる (`pi` の ac は coord-wise ac から従うが補題が無い)。
- **`iIndepFun.cgf_sum`**: `iIndepFun X μ` から `IsProbabilityMeasure μ` を内部導出。
  tilted ambient では `iIndepFun_tilted_ambient` (既存) で供給可。`h_int` (各 coord の exp-integrability) は
  bounded RV から従う。

---

## 自作が必要な要素 (優先度順)

1. **`Measure.pi` の有限 tilt 因子分解** (最重要・最大ピース) —
   `(Measure.pi (fun _:Fin n => μ₀)).tilted (fun x => ∑ i, lam * Y (x i)) = Measure.pi (fun _ => μ₀.tilted (lam*Y·))`。
   素材: `tilted = withDensity (ENNReal.ofReal (exp/∫exp))` + `withDensity` を `Measure.pi` 上で
   因子分解する補題が**無い** (E: `pi × withDensity = Found 0`)。`pi_pi` (`Constructions/Pi.lean`) +
   `exp_sum = ∏ exp` + Tonelli で組むが、`withDensity` の積分解 lemma 自体を先に立てる必要。
   **推定 120–200 行**。Mathlib PR 級。
2. **`Measure.pi` 絶対連続性 + RN-deriv 因子分解** —
   `Measure.pi μ_tilt ≪ Measure.pi μ` と `(pi μ_tilt).rnDeriv (pi μ) =ᵐ ∏ coord rnDeriv`。
   E 行で両方 `Found 0`。**推定 80–150 行**。
3. **無限積への持ち上げ** — 1+2 を `infinitePi_cylinder` / `lintegral_restrict_infinitePi` で
   cylinder 上に落とし、`infinitePi_eq_pi` を介して有限版に帰着。beta-redex 迂回 (haveI) を全所に。
   **推定 50–80 行**。
4. **change-of-measure 下界の抽出** — `setLIntegral_rnDeriv` + tilted LLN
   (`tilted_lln_in_probability_real`, 既存) で `μ_tilt(E_n) → 1` を使い `C·exp(-n(λa−Λ+λε))` を抽出。
   **推定 40–70 行**。step 5 の LLN 部分は既存。
5. **Chernoff 側の pmf↔Measure 橋** — `chernoffMediatorMeasure` (既存) を `infinitePi` に乗せ、
   1–4 を `bayesErrorMinPmf` 形に翻訳。`α` は `[Fintype]` なので `pi`/`infinitePi` は楽だが、
   `bayesErrorMinPmf` の n-letter 定義との突き合わせ bridge が追加で **60–100 行**。

**自前合計**: Cramér 側だけで ~290–500 行、Chernoff 側 +60–100 行。CLAUDE.md 既述の
「500+ 行 textbook 証明」見積もりと整合 (むしろ下限寄り)。

### 代替経路 (5) の評価: 「RN 恒等式を陽に書かず近道」できるか

- **不可**。`tilted` の RN-deriv (`rnDeriv_tilted_left_self`) + `lintegral_rnDeriv` だけで直接
  cylinder bound を出すには、結局 **product 上の rnDeriv (= ∏ coord)** が必要で、それが E 行の
  `Found 0`。`tilted_mul_apply_cgf` は n=1 では完璧だが、∑-exponent を ∏-density に展開する瞬間に
  「`Measure.pi` × `tilted`/`withDensity` 因子分解」が要り、近道は項目 1 に collapse する。
- `iIndepFun.cgf_sum` で exponent の `n·Λ(lam)` 同一視は無料 (既存) だが、これは「数値の同一視」で
  あって「測度の change-of-measure」ではない。下界を出す測度等式は項目 1 が不可避。

---

## 撤退ラインへの距離

親計画の撤退ライン (`docs/textbook-roadmap.md:387-393` T1-C L-D3 / `cramer-lc2-ext-moonshot-plan.md`):

> Phase C の n-letter RN-deriv 識別は Mathlib gap (`Measure.infinitePi_tilted_eq`)。
> 500+ 行構築。述語抽象で partial discharge し本体は別 plan defer。

**判定: 完全に踏み抜く (撤退ライン発動 = yes)**。

- 数学核心 (step 3+4 = `Measure.pi`/`infinitePi` × `tilted` 因子分解 + product RN-deriv) は
  Mathlib に **一切存在しない** (E 行 11 件すべて `Found 0` / 不在)。
- 既存の述語抽象 (`IsMeasureInfinitePiTiltedEq` / `IsBayesErrorPerTiltLowerBound`) は
  **正しい撤退**であり、これ以上の partial discharge は不可能 (述語の中身が core そのもの)。
- 1 セッション (= agent chain 1 周) では完遂不可。過去 judgement log の
  「~550 行 / 4-6 セッション、1 セッション完遂不可」評価 (textbook-roadmap:401 の Huffman 類似判定) と整合。

**新規撤退ライン (縮退案)**: もし将来着手するなら、いきなり `infinitePi` を狙わず、
**「有限版 `Measure.pi` tilt 因子分解 (項目 1)」を単独 Mathlib-PR 候補 lemma として publish** し、
`infinitePi` 持ち上げ (項目 3) は別 seed に分離。項目 1 が割れれば 2–4 は機械的に続く構造なので、
**項目 1 を最初の 1 セッションのゲート**にする。項目 1 が 1 セッションで割れなければ全体 PIVOT。

---

## 着手 skeleton (将来着手時の出発点、本調査では実装しない)

`Common2026/Shannon/InfinitePiTiltedRN.lean` の出だし案:

```lean
import Common2026.Shannon.CramerLC2DischargeExt
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Moments.Tilted
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Constructions.Pi

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal Function

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- **項目 1 (最大ピース・Mathlib gap)**: 有限積の tilt 因子分解。
`(Measure.pi (fun _ => μ₀)).tilted (∑-exponent) = Measure.pi (fun _ => μ₀.tilted (lam*Y·))`。
loogle 確認: `Measure.pi × tilted` / `Measure.pi × withDensity` ともに `Found 0`。 -/
lemma pi_tilted_sum_eq_pi_tilted
    {n : ℕ} {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    (Measure.pi (fun _ : Fin n => μ₀)).tilted
        (fun x => ∑ i, lam * Y (x i))
      = Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω)) := by
  sorry

/-- **項目 2**: 有限積の絶対連続性 + RN-deriv 因子分解。loogle `Found 0`。 -/
lemma pi_tilted_absolutelyContinuous
    {n : ℕ} {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    Measure.pi (fun _ : Fin n => μ₀.tilted (fun ω => lam * Y ω))
      ≪ Measure.pi (fun _ : Fin n => μ₀) := by
  sorry

/-- **主目標**: `CramerLC2PhaseC.IsMeasureInfinitePiTiltedEq` の 0-sorry 充足。
項目 1–4 + 既存 `tilted_lln_in_probability_real` の合成。 -/
theorem isMeasureInfinitePiTiltedEq_discharge
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    IsMeasureInfinitePiTiltedEq μ₀ Y lam := by
  sorry

end InformationTheory.Shannon.Cramer.Discharge
```

`Common2026.lean` への import 追加は実装完了後。
