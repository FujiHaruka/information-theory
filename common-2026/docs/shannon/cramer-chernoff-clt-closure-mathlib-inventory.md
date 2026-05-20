# Cramér / Chernoff CLT-boundary closure — Mathlib feasibility 在庫

> 調査対象: `IsTiltedWindowEventuallyLarge` の **CLT-boundary residual**
> (`a = tilted mean` の境界等号ケース) を 0-sorry まで閉じられるか。
> 親計画: [`infinitepi-tilted-rn-discharge-moonshot-plan.md`](infinitepi-tilted-rn-discharge-moonshot-plan.md)
> §撤退ライン **W-3** (residual predicate 縮約、sorry 禁止)。
> 同 family: [`shannon-mathlib-inventory.md`](shannon-mathlib-inventory.md)。

## 一行サマリ

**4 piece 中 3 piece は Mathlib + 既存足場でほぼ直結 (CLT 適用 plumbing / portmanteau half-line / residual 緩和)。残る 1 piece「Gaussian 半直線 = 1/2」だけが Mathlib 不在で自前 ~40-70 行。** CLT 本体・portmanteau・iid plumbing・variance-curvature link すべて既存。verdict: **GO** (1〜2 unit chain で full closure 可能、最大の詰まりは Gaussian median lemma の自作)。既存率 ≈ 80% / 自作必要 2 件 (Gaussian half-line + boundary 統合補題) / 撤退ライン発動 **no** (W-3 はすでに発動済 = residual 化が現状。本調査は residual を「境界も含めて埋める」上振れ方向)。

---

## 主目的の最終形 (再掲)

`Common2026/Shannon/InfinitePiTiltedChangeOfMeasure.lean` に既存の interior 補題:

```lean
theorem tiltedWindow_eventually_large_of_cgfDeriv_interior
    (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) {a ε : ℝ}
    (h_lo : a < deriv (cgf Y μ₀) lam) (h_hi : deriv (cgf Y μ₀) lam < a + ε) :
    ∀ᶠ n in atTop, (1:ℝ)/2 ≤ (infinitePi (μ₀.tilted (lam·Y))).real { window n }
```

を **境界 `a = deriv (cgf Y μ₀) lam` (= tilted mean `m`) を含む形** に拡張したい。
境界では interior の LLN-squeeze が効かない (片側だけ `< a+ε` が緩く、`a ≤` 側が等号)。
緩和済の最終ターゲットは `∃ C>0` 形 (`C = 1/4` 等):

```lean
-- 目標 (boundary 版): a = m のとき、窓質量が eventually ≥ C (>0)
theorem tiltedWindow_eventually_large_of_boundary
    (hY : Measurable Y) (h_bdd) (lam) {ε : ℝ} (hε : 0 < ε)
    (hVar : 0 < Var[fun ω => Y (ω 0); infinitePi (μ₀.tilted (lam·Y))]) :   -- 退化除外
    ∀ᶠ n in atTop, (1:ℝ)/4 ≤ (infinitePi (μ₀.tilted (lam·Y))).real
        { ω | m·n ≤ ∑_{i<n} Y(ω i) ∧ ∑ < (m+ε)·n }
```

### 証明戦略 (pseudo-Lean、a = m に固定)

```text
1. P := infinitePi (μ₀.tilted (lam·Y)); X i ω := Y (ω i); m := P[X 0]
2. iid: iIndepFun_tilted_ambient + identDistrib_tilted_ambient   -- 既存
3. MemLp (X 0) 2 P: memLp_of_bounded (bounded X 0)               -- Mathlib
4. CLT: tendstoInDistribution_inv_sqrt_mul_sum_sub               -- Mathlib
        ⇒ S_n := (√n)⁻¹·(∑ X k - n·m) →d gaussianReal 0 v.toNNReal
5. .tendsto field ⇒ Tendsto (P.map S_n) atTop (𝓝 (gaussianReal 0 v)) in ProbabilityMeasure
6. portmanteau: tendsto_measure_of_null_frontier_of_tendsto'
        E := {x | 0 ≤ x}, frontier E = {0}, noAtoms_gaussianReal ⇒ μ{0}=0
        ⇒ (P.map S_n){0≤·} → gaussianReal 0 v {0≤·}
7. 集合書換: {m·n ≤ ∑Y} = S_n⁻¹{0≤·}  (0 ≤ (√n)⁻¹(∑Y - n·m) ⟺ m·n ≤ ∑Y, n≥1)
        ⇒ P{m·n ≤ ∑Y} → gaussianReal 0 v {0≤·}
8. Gaussian median: gaussianReal 0 v {0≤·} = 1/2          -- ★ 自作 (Mathlib 不在)
9. P{m·n ≤ ∑Y} → 1/2;  P{(m+ε)n ≤ ∑Y} → 0 (LLN, 既存 tilted_lln)
        ⇒ 窓質量 = P{m·n≤∑Y} − P{(m+ε)n≤∑Y} → 1/2 ≥ 1/4 eventually
```

---

## API 在庫テーブル

### 1. Mathlib CLT (`Mathlib/Probability/CentralLimitTheorem.lean`)

| 概念 | Mathlib API | file:line | 状態 | 本調査での扱い |
|---|---|---|---|---|
| CLT (mean μ, var v, gaussianReal 0 v) | `tendstoInDistribution_inv_sqrt_mul_sum_sub` | `CentralLimitTheorem.lean:123` | ✅ 既存 | **主役**。下記 signature 厳守 |
| CLT (centered, var 1) | `tendstoInDistribution_inv_sqrt_mul_sum` | `CentralLimitTheorem.lean:79` | ✅ 既存 | sub 版が呼ぶ内部。直接は使わない |
| charFun 補題 | `charFun_inv_sqrt_mul_sum` | `:44` | ✅ | 不要 (CLT 内部) |

`tendstoInDistribution_inv_sqrt_mul_sum_sub` 完全 signature (逐語):

```lean
theorem tendstoInDistribution_inv_sqrt_mul_sum_sub
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : Measure Ω} {P' : Measure Ω'} {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P'
```

- 引数: `hY : HasLaw Y (gaussianReal 0 Var[X 0;P].toNNReal) P'` (limit 法則の証人 — `Y, Ω', P'` は自前で `gaussianReal` 上の id で供給可)、`hX : MemLp (X 0) 2 P`、`hindep : iIndepFun X P`、`hident : ∀ i, IdentDistrib (X i) (X 0) P P`。
- **型クラス前提**: `[IsProbabilityMeasure P] [IsProbabilityMeasure P']` のみ。`StandardBorelSpace` / `Countable` 等の重い前提は **無し** (codomain は ℝ で固定)。
- 結論形 (逐語): `TendstoInDistribution (fun n ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0])) atTop Y (fun _ ↦ P) P'`。
- **退化処理**: 本体 (`:130`) は `Var[X 0;P] = 0` を `tendstoInDistribution_of_identDistrib` で別処理 (極限が `gaussianReal 0 0` = dirac)。よって `v > 0` を要するのは **portmanteau の median 値 1/2** 側 (`v=0` だと `{0≤·}` 質量が 1 になり median ≠ 1/2)。`Var > 0` は別途 hypothesis として要求する (退化 Y は除外)。
- `Var[X 0; P]` 記法 = `ProbabilityTheory.variance (X 0) P` (notation `Var[·;·]`、`Mathlib/Probability/Moments/Variance.lean`)。

### 2. `TendstoInDistribution` 定義と portmanteau

| 概念 | Mathlib API | file:line | 状態 | 本調査での扱い |
|---|---|---|---|---|
| `TendstoInDistribution` 定義 | `MeasureTheory.TendstoInDistribution` | `MeasureTheory/Function/ConvergenceInDistribution.lean:64` | ✅ | weak conv = `ProbabilityMeasure` での `Tendsto` |
| `.tendsto` 射影 | `TendstoInDistribution.tendsto` | `:69` (structure field) | ✅ | **CLT → portmanteau の橋** |
| portmanteau half-line (ℝ≥0∞ 版) | `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'` | `MeasureTheory/Measure/Portmanteau.lean:333` | ✅ | **piece 6 主役** |
| portmanteau (NNReal 版) | `..._of_null_frontier_of_tendsto` | `Portmanteau.lean:350` | ✅ | toReal が要れば |
| frontier of Ici | `frontier_Ici` | `Topology/Order/DenselyOrdered.lean` | ✅ | `frontier (Ici a) = {a}` |

`TendstoInDistribution` 定義 (逐語、`:64`):

```lean
structure TendstoInDistribution [OpensMeasurableSpace E] (X : (i : ι) → Ω i → E) (l : Filter ι)
    (Z : Ω' → E) (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (μ' : Measure Ω' := by volume_tac) [IsProbabilityMeasure μ'] : Prop where
  forall_aemeasurable : ∀ i, AEMeasurable (X i) (μ i)
  aemeasurable_limit : AEMeasurable Z μ' := by fun_prop
  tendsto : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (forall_aemeasurable n)⟩) l
      (𝓝 ⟨μ'.map Z, Measure.isProbabilityMeasure_map aemeasurable_limit⟩)
```

`.tendsto` field は **まさに portmanteau が要求する `Tendsto μs L (𝓝 μ)` (`ProbabilityMeasure E`)** を提供。意味: 各 `μ n` の `X n` push-forward が limit の `Z` push-forward へ弱収束。`{μs i := ⟨(P).map (S_n), _⟩}`, `μ := ⟨P'.map Y, _⟩` で portmanteau を直接適用できる。

portmanteau lemma 完全 signature (逐語、`:333`):

```lean
theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' {Ω ι : Type*}
    {L : Filter ι} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    (μs_lim : Tendsto μs L (𝓝 μ)) {E : Set Ω} (E_nullbdry : (μ : Measure Ω) (frontier E) = 0) :
    Tendsto (fun i ↦ (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E))
```

- 型クラス前提: `[MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]`。**Ω = ℝ はこれら全て自動充足** (`ℝ` は `HasOuterApproxClosed` instance を持つ — pseudo-metric 空間)。`StandardBorelSpace` / `PolishSpace` 不要。
- 引数: `μs_lim : Tendsto μs L (𝓝 μ)` (= CLT `.tendsto`)、`E_nullbdry : (μ:Measure) (frontier E) = 0`。
- 結論形 (逐語): `Tendsto (fun i ↦ (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E))`。
- `E := {x | (0:ℝ) ≤ x} = Set.Ici 0` ⇒ `frontier E = {0}` (`frontier_Ici`) ⇒ `E_nullbdry` は `gaussianReal 0 v {0} = 0`、`noAtoms_gaussianReal` (`v≠0`) で即。

### 3. Gaussian 対称性 / 半直線質量

| 概念 | Mathlib API | file:line | 状態 | 本調査での扱い |
|---|---|---|---|---|
| `gaussianReal m v {x | a ≤ x} = 1/2` (median) | — | — | ❌ **不在** (loogle `Found 0` 確認済) | **★ 自作 piece 8** |
| Gaussian no atoms | `noAtoms_gaussianReal` | `Distributions/Gaussian/Real.lean:213` | ✅ | frontier null に使用 |
| 反転対称 (measure 形) | `gaussianReal_map_neg` | `Real.lean:330` | ✅ | **median 自作の核** |
| 反転対称 (HasLaw 形) | `gaussianReal_neg` | `Real.lean:383` | ✅ | 補助 |
| 質量 = PDF lintegral | `gaussianReal_apply` | `Real.lean:217` | ✅ | median 自作で積分式へ |
| 質量 = PDF integral | `gaussianReal_apply_eq_integral` | `Real.lean:221` | ✅ | 同上 |
| 絶対連続 (volume) | `gaussianReal_absolutelyContinuous` | `Real.lean:228` | ✅ | 補助 |
| `gaussianReal m v` 確率測度 | `instIsProbabilityMeasureGaussianReal` | `Real.lean:210` | ✅ | 全質量 1 |

verbatim 主要 2 本:

```lean
lemma noAtoms_gaussianReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) : NoAtoms (gaussianReal μ v)
lemma gaussianReal_map_neg : (gaussianReal μ v).map (fun x ↦ -x) = gaussianReal (-μ) v
```

**median 自作の見積もり (piece 8)**: `gaussianReal 0 v {0 ≤ ·} = 1/2` (v≠0)。
反転 `x ↦ -x` で `{0 ≤ ·} ↦ {· ≤ 0}`、`gaussianReal_map_neg` (μ=0 で固定点) ⇒
`gaussianReal 0 v {0 ≤ ·} = gaussianReal 0 v {· ≤ 0}`。両者の和は `{0≤·} ∪ {·≤0} = univ` (= 1)、交わり `{0}` は no atoms で 0。⇒ `2·(half-line) = 1` ⇒ `= 1/2`。
**落とし穴**: (i) ℝ≥0∞ 算術 (`2 * x = 1 → x = 1/2`、`ENNReal.eq_div_of...`)、(ii) `map` 下の measure 値の引き戻し (`Measure.map_apply` + 可測 `{0≤·}` の preimage が `{·≤0}`)、(iii) `{0≤·} ∪ {·≤0} = univ`・`∩ = {0}` の集合計算。推定 **40-70 行**。Gaussian cdf 経由 (`ProbabilityTheory.cdf`) は `cdf gaussian 1/2` lemma が `Found 0` なので **逆に高コスト** — symmetry-by-map 経路が最短。

### 4. tilted ambient の CLT 前提供給 (既存 `Common2026/Shannon/`)

| 概念 | 既存 API | file:line | 状態 | CLT への適合 |
|---|---|---|---|---|
| `iIndepFun (fun i ω => Y(ω i))` (tilted) | `iIndepFun_tilted_ambient` | `CramerLC2Discharge.lean:85` | ✅ 既存 | CLT `hindep` に **そのまま** |
| `IdentDistrib (X i) (X 0)` (tilted) | `identDistrib_tilted_ambient` | `CramerLC2Discharge.lean:98` | ✅ 既存 | CLT `hident` に **そのまま** |
| infinitePi tilted = 確率測度 | `isProbabilityMeasure_infinitePi_tilted_of_bounded` | `CramerLC2DischargeExt.lean:85` | ✅ 既存 | CLT `[IsProbabilityMeasure P]` |
| tilted = 確率測度 | `isProbabilityMeasure_tilted_of_bounded` | (Cramer.lean 系) | ✅ 既存 | 補助 |
| MemLp 2 (bounded → Lp) | `memLp_of_bounded` | `MeasureTheory/.../LpSeminorm/Basic.lean:557` | ✅ Mathlib | CLT `hX` |
| bounded eval family | `bounded_eval_family` | `CramerLC2Discharge.lean:167` | ✅ 既存 | MemLp の bound 供給 |
| tilted LLN (in prob, .real) | `tilted_lln_in_probability_real` | `CramerLC2DischargeExt.lean:236` | ✅ 既存 | piece 9 の `(m+ε)` 側 → 0 |

`iIndepFun_tilted_ambient` 完全 signature (逐語):

```lean
lemma iIndepFun_tilted_ambient
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) :
    iIndepFun (fun (i : ℕ) (ω : ℕ → Ω₀) => Y (ω i))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
```

`identDistrib_tilted_ambient` 完全 signature (逐語):

```lean
lemma identDistrib_tilted_ambient
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ) (i : ℕ) :
    IdentDistrib (fun ω : ℕ → Ω₀ => Y (ω i)) (fun ω : ℕ → Ω₀ => Y (ω 0))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
      (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω)))
```

**適合性**: CLT は `X : ℕ → Ω → ℝ` を要求。`X i := fun ω : ℕ → Ω₀ => Y (ω i)` がそのまま CLT の `X` (型 `ℕ → (ℕ → Ω₀) → ℝ`)。`iIndepFun_tilted_ambient` の結論は **`iIndepFun X P` と字面一致**、`identDistrib_tilted_ambient i` は `∀ i, IdentDistrib (X i) (X 0) P P` を `fun i => ...` で供給。**plumbing ギャップは無し** — 既存 plumbing でちょうど足りる。

### 5. 分散正値 (退化除外)

| 概念 | Mathlib API | file:line | 状態 | 本調査での扱い |
|---|---|---|---|---|
| `Var[X; tilted (t·X)] = iteratedDeriv 2 (cgf X μ) t` | `variance_tilted_mul` | `Probability/Moments/Tilted.lean:159` | ✅ Mathlib | cgf-curvature link |
| `evariance = 0 ↔ ae const` | `evariance_eq_zero_iff` | `Moments/Variance.lean:178` | ✅ Mathlib | 退化 ⟺ Y a.e. 定数 |
| `Var=0 ⇒ ae = mean` | `ae_eq_integral_of_variance_eq_zero` | `Moments/Variance.lean` | ✅ Mathlib | 退化処理 |
| `iteratedDeriv_two_cgf` | `iteratedDeriv_two_cgf` | `Moments/MGFAnalytic.lean` | ✅ Mathlib | cgf 二階微分 |

`variance_tilted_mul` (逐語、`:159`):

```lean
lemma variance_tilted_mul (ht : t ∈ interior (integrableExpSet X μ)) :
    Var[X; μ.tilted (t * X ·)] = iteratedDeriv 2 (cgf X μ) t
```

**扱い**: `v := Var[X 0; P]` (P=infinitePi tilted) は CLT の極限分散。`v > 0` を **hypothesis として要求** するのが最短 (median=1/2 が v>0 を要するため、退化 Y を仕様から除外)。`variance_tilted_mul` で `v = Var[Y; μ₀.tilted (lam·Y)] = iteratedDeriv 2 (cgf Y μ₀) lam` と同定でき、cgf 凸性 (Λ''>0) の言葉に翻訳可能だが **必須ではない**。注意: `variance_tilted_mul` の tilt 形 `(t * X ·)` は本プロジェクトの `(fun ω => lam * Y ω)` と一致。`integrableExpSet Y μ₀ = univ` (bounded ⇒ 既存 `tiltedMean_eq_deriv_cgf` 内で実証済) なので interior 前提は自動。**退化 (v=0) の場合は窓質量が境界で 0/1 ジャンプし `1/4` 下界が成立しない** — この 1 ケースは仕様から除外 (Cramér 非自明 rate function では Λ''>0 が常に成立)。

### 6. residual 緩和 (`1/2 → ∃C>0`)

| 概念 | 既存 API | file:line | 状態 | 本調査での扱い |
|---|---|---|---|---|
| residual predicate (∀a∀ε 形) | `IsTiltedWindowEventuallyLarge` | `InfinitePiTiltedChangeOfMeasure.lean:282` | ✅ 既存 (定義) | `1/2` ハードコード |
| W-3 reduction | `isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge` | `InfinitePiTiltedChangeOfMeasure.lean:293` | ✅ 既存 | C 利用箇所 |
| 下流 predicate | `IsMeasureInfinitePiTiltedEq` | `CramerLC2PhaseC.lean` | ✅ 既存 | `∃C>0` を要るだけ |

`isMeasureInfinitePiTiltedEq_of_tiltedWindowLarge` の内部 C 利用 (`:300-301`):

```lean
intro a ε hε
refine ⟨1 / 2, by norm_num, ?_⟩   -- C := 1/2 を抽出
filter_upwards [h_res a ε hε] with n hn   -- residual から 1/2 ≤ 窓質量
...
rw [hW_real] at hn; exact hn   -- 最後に「1/2 ≤ window.real」を使うだけ
```

**緩和判定**: 下流 `IsMeasureInfinitePiTiltedEq` の `a ε hε` ケースは `⟨C, 0<C, eventually (C ≤ ...)⟩` を返す形 (`:300-301` で `refine ⟨1/2, ..., ...⟩`)。よって residual を `∀a ε, 0<ε → ∃ C>0, ∀ᶠn, C ≤ 窓質量` (or 固定 `C=1/4`) に **一般化しても reduction 補題は通る** — 内部で C は `refine ⟨C, hC, _⟩` に流すだけ、`1/2` の特定値依存は無い。緩和コスト: 定義 + reduction 補題の `1/2 → C` 置換 **5-15 行**。境界ケースは `C := 1/4` で `1/2 → 1/4` の余裕を吸収。

---

## 主要前提条件ボックス

- **CLT (`tendstoInDistribution_inv_sqrt_mul_sum_sub`)**:
  - `[IsProbabilityMeasure P]`, `[IsProbabilityMeasure P']` のみ。重い空間前提なし (codomain ℝ 固定)。
  - `HasLaw Y (gaussianReal 0 Var[X 0;P].toNNReal) P'`: limit 法則は `.toNNReal` で渡る。witness `(Ω', P', Y)` は自前で `(ℝ, gaussianReal 0 v, id)` を立てる必要 (`HasLaw id (gaussianReal 0 v) (gaussianReal 0 v)` は `map id = self` で自明)。
  - `MemLp (X 0) 2 P`: bounded ⇒ `memLp_of_bounded` (要 `[IsFiniteMeasure P]`、確率測度で充足)。
  - `v=0` は CLT 内部で別処理されるが、**median=1/2 は v>0 を要する** ⇒ `Var>0` を外から要求 (退化 Y 除外)。

- **portmanteau (`tendsto_measure_of_null_frontier_of_tendsto'`)**:
  - `[OpensMeasurableSpace ℝ] [HasOuterApproxClosed ℝ]`: ℝ で自動。`StandardBorelSpace`/`PolishSpace` **不要**。
  - `E_nullbdry : μ (frontier E) = 0`: `E = Ici 0`, `frontier = {0}`, `noAtoms_gaussianReal (v≠0)` で。**v=0 だと no atoms が崩れ frontier null も崩れる** — ここでも v>0 必須。

- **集合書換 (piece 7)** (前提事故注意):
  - `{ω | m·n ≤ ∑Y} = (S_n)⁻¹ (Ici 0)` は `n ≥ 1` (√n > 0) でのみ成立。`0 ≤ (√n)⁻¹·(∑Y - n·m) ⟺ 0 ≤ ∑Y - n·m ⟺ m·n ≤ ∑Y`。`n=0` は eventually で捨てる。
  - `(P.map S_n) (Ici 0) = P ((S_n)⁻¹ (Ici 0))` は `Measure.map_apply` (要 `Measurable S_n` ∧ `MeasurableSet (Ici 0)`)。

- **既存 LLN (`tilted_lln_in_probability_real`)**: `(m+ε)` 側 `P{(m+ε)n ≤ ∑Y} → 0` を出すのに使う。窓質量 = 半直線(m) − 半直線(m+ε)。

---

## 自作が必要な要素 (優先度順)

1. **`gaussianReal_Ici_eq_half` (Gaussian median)** — `(v≠0) → gaussianReal 0 v {x | 0 ≤ x} = 1/2`。
   推奨実装: `gaussianReal_map_neg` (μ=0) で `{0≤·}` 質量と `{·≤0}` 質量を同定、和 = univ = 1、交わり `{0}` を `noAtoms` で 0、ℝ≥0∞ で `2x=1 ⇒ x=1/2`。**工数 40-70 行**。落とし穴: ℝ≥0∞ 算術 + `Measure.map_apply` の可測前提 + `{0≤·}∪{·≤0}=univ` の集合計算。**最大の詰まりどころ**。
2. **`tiltedWindow_eventually_large_of_boundary` (境界統合)** — piece 2-9 を繋ぐ本体補題。CLT 適用 (witness 構築 + 既存 plumbing 注入) + portmanteau + 集合書換 + median + LLN 引き算。**工数 70-120 行**。落とし穴: (i) `HasLaw id` witness の `gaussianReal 0 v.toNNReal` の `.toNNReal`/`ℝ≥0` 変換、(ii) `Var[X 0;P]` の `.toReal`/正値の往復、(iii) `S_n` 可測性 (eval ∘ sum の `fun_prop`)。
3. **residual predicate 緩和 (`1/2 → C`)** — 定義 `IsTiltedWindowEventuallyLarge` を `∃C>0` 形 (or `C=1/4` 固定) に書換 + reduction 補題 `:300` の `⟨1/2,...⟩ → ⟨C,...⟩`。**工数 5-15 行**。低リスク。
4. (オプション) **interior + boundary 統合** — 既存 interior 補題 (`a < m < a+ε`) と新 boundary 補題 (`a = m`) を場合分けで束ねて「`a ≤ m < a+ε` ⇒ 窓質量 eventually ≥ C」。**工数 15-30 行**。

---

## piece 別難度・推定行数

| piece | 難度 | 既存度 | 推定行数 |
|---|---|---|---|
| CLT tilted 適用 (witness + plumbing 注入) | (b) 組立 | plumbing 100% 既存 | 30-50 |
| portmanteau half-line (frontier null + 適用) | (b) 組立 | lemma 既存 | 20-35 |
| Gaussian 半直線 = 1/2 (median) | **(c) 一から** | **0% 既存** | **40-70** |
| residual 緩和 (1/2 → ∃C) | (a) ほぼ直接 | reduction 既存 | 5-15 |
| 集合書換 + LLN 引き算 (窓質量同定) | (b) 組立 | LLN 既存 | 20-40 |
| **合計 (full closure)** | — | ≈80% | **~120-210** |

---

## 撤退ラインへの距離

親計画 [`infinitepi-tilted-rn-discharge-moonshot-plan.md`](infinitepi-tilted-rn-discharge-moonshot-plan.md) §撤退ライン **W-3** (Phase 4 full discharge が割れない → residual predicate 縮約、sorry 禁止):

**判定: 撤退ライン発動 = no (むしろ撤退状態からの復帰方向)**。

- W-3 は**既に発動済**。現状コードは `IsTiltedWindowEventuallyLarge` residual predicate で着地し (sorry 0)、interior ケースのみ `tiltedWindow_eventually_large_of_cgfDeriv_interior` で discharge 済。
- 本調査は「residual の **境界ケースも CLT で埋めて predicate を実際に証明可能にする**」上振れ方向 ⇒ W-3 撤退をさらに踏み抜くのではなく、撤退から前進する。
- **新規撤退ライン提案 (CLT closure 用)**:
  - **L-CLT1**: Gaussian median (`gaussianReal_Ici_eq_half`) が ℝ≥0∞ 算術で 1 セッション詰まる → median を別 file の単独 PR-target 補題として切り出し、boundary 補題は `(hMedian : gaussianReal 0 v {0≤·} = 1/2)` を hypothesis pass-through で受ける (sorry なし、足場のみ publish)。
  - **L-CLT2**: CLT witness 構築 (`HasLaw id (gaussianReal ...)`) で `.toNNReal` 変換が詰まる → interior 補題のまま据え置き、boundary は predicate に残す (現 W-3 状態維持、後退ゼロ)。

---

## 着手 skeleton

`Common2026/Shannon/CramerCltBoundaryClosure.lean` (新規) の出だし:

```lean
import Common2026.Shannon.InfinitePiTiltedChangeOfMeasure
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Cramér / Chernoff CLT-boundary closure

Closes the boundary case `a = tilted mean` of `IsTiltedWindowEventuallyLarge`,
left open by the interior LLN-squeeze (`tiltedWindow_eventually_large_of_cgfDeriv_interior`).
Strategy: CLT (`tendstoInDistribution_inv_sqrt_mul_sum_sub`) + portmanteau half-line
(`tendsto_measure_of_null_frontier_of_tendsto'`) + Gaussian median (self-written).
-/

namespace InformationTheory.Shannon.Cramer.Discharge

open MeasureTheory ProbabilityTheory Real Filter
open scoped Topology BigOperators ENNReal

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]

/-- **Gaussian median**: a centered Gaussian puts mass `1/2` on the closed half-line
`{x | 0 ≤ x}`. Mathlib-absent; proved via `gaussianReal_map_neg` symmetry + `noAtoms`. -/
theorem gaussianReal_Ici_eq_half {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v {x : ℝ | (0 : ℝ) ≤ x} = 1 / 2 := by
  sorry

/-- **CLT-boundary window largeness** (`a = m := tilted mean`).
The tilted infinite-product window mass is eventually `≥ 1/4` at the CLT boundary,
when the tilted variance is non-degenerate. -/
theorem tiltedWindow_eventually_large_of_boundary
    {μ₀ : Measure Ω₀} [IsProbabilityMeasure μ₀]
    {Y : Ω₀ → ℝ} (hY : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (lam : ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hVar : (0 : ℝ) < Var[fun ω : ℕ → Ω₀ => Y (ω 0);
        Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))]) :
    ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) / 4 ≤ (Measure.infinitePi (fun _ : ℕ => μ₀.tilted (fun ω => lam * Y ω))).real
          {ω : ℕ → Ω₀ |
            (∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) * n ≤ ∑ i ∈ Finset.range n, Y (ω i)
            ∧ ∑ i ∈ Finset.range n, Y (ω i)
                < ((∫ ω, Y ω ∂(μ₀.tilted (fun ω => lam * Y ω))) + ε) * n} := by
  sorry

end InformationTheory.Shannon.Cramer.Discharge
```

`gaussianReal_Ici_eq_half` を最初に埋め (独立 piece)、続いて boundary 補題で既存 plumbing
(`iIndepFun_tilted_ambient` / `identDistrib_tilted_ambient` / `memLp_of_bounded`) を CLT に注入、
portmanteau → median → LLN 引き算で閉じる。
