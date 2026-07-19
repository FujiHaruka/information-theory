# Portfolio W∞ AEP (CT 16.5.1 完全形) — Mathlib / in-project API 在庫 (M0)

> **Parent plan (SoT)**: [`portfolio-stationary-woo-plan.md`](portfolio-stationary-woo-plan.md) — R1 可測選択 / R2 条件付き成長率単調収束 / R3 real-valued Algoet–Cover sandwich AEP。
> 本ファイルは M0 在庫成果物。実装 (`.lean`) は行わない。全署名は Mathlib / in-project ソースを Read して verbatim 確認済。

## 一行サマリ

**R1 (可測選択) と R3 (real-valued sandwich) の gateway 判定 = 「genuine Mathlib 壁は無い」。** 使う API のうち
**実体 (condExp・Lévy upward・conditional Jensen・compact 最大点存在・Birkhoff・liminf/limsup sandwich core・親 Leg B log-return テンプレ) はほぼ全て既存 (Mathlib + in-project)**。自作が要るのは **R1 の「Carathéodory 可測 argmax」1 点のみ** (Mathlib に ready lemma 不在 = `Found 0`、ただし部品完備で ~80–200 行の plumbing 自作、genuine 解析壁ではない)。**撤退ラインは M0 では発動しない。** 最危険所見: R1 の可測選択に `[StandardBorelSpace]` は不要 (simplex は有限次元 compact metric、部品は全て一般可測空間で発火) だが、**Lévy upward `tendsto_ae_condExp` は `[IsFiniteMeasure μ]` を要求** — 確率測度なので満たすが署名に明示継承される。

---

## 主定理の最終形 (plan からの再掲)

plan には Lean 署名の確定形は無い (sketch 段階)。M0 時点で見込む headline (R4 で確定):

```lean
-- CT 16.5.1 完全形: causal log-optimal 富の成長率 → W_∞ (無限過去条件付き成長率の増加極限)
theorem logOptimal_growth_tendsto_Winfty
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    (X : Ω → (Fin m → ℝ)) (bstar : Ω → (Fin m → ℝ))       -- R1: 可測 log-optimal 選択
    (hbstar_meas : Measurable bstar) (hbstar_simplex : ∀ ω, bstar ω ∈ stdSimplex ℝ (Fin m))
    (hint : Integrable (fun ω ↦ Real.log (∑ j, bstar ω j * X ω j)) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ (∑ i ∈ Finset.range (n+1), Real.log (∑ j, bstar (T^[i] ω) j * X (T^[i] ω) j)) / (n+1))
      atTop (𝓝 Winfty)                                     -- R2: Winfty = lim_k W*(X_0|past_k)
```

証明戦略 (pseudo-Lean、Algoet–Cover sandwich の real-valued 再構築):

```
-- R1: bstar ω := 無限過去条件付き法の下で growthRate を最大化する可測選択 (Carathéodory argmax)
-- R2: W*_k := condExp (μ[· | ℱ_k]) 経由の k 次条件付き成長率; k↑ で単調非減少 (conditional Jensen)
--     Winfty := ⨆ k, W*_k  (単調有界 ⟹ tendsto、または Lévy upward tendsto_ae_condExp)
-- R3 lower:  birkhoff_ergodic_ae を k 次条件付き log-return g_k := log(bstar_k · X) に適用
--            ⟹ (1/n)∑ log(bstar_k·X∘T^i) → ∫ g_k = W*_k          (親 Leg B と同型)
--     upper: 真の log-optimal 富 ≤ 各 k 近似富 (KT dominance) + R2 で Winfty へ
--     sandwich: W*_k ≤ liminf ≤ limsup ≤ Winfty, k↑ ⟹ tendsto_of_le_liminf_of_limsup_le
```

---

## Block 1 — `MeasureTheory.condExp` real-valued 条件付き期待 API

### 1A. condExp core + tower

| 概念 | Mathlib API (verbatim) | file:line | 状態 | R2 での扱い |
|---|---|---|---|---|
| 条件付き期待 (定義) | `noncomputable irreducible_def condExp (μ : Measure[m₀] α) (f : α → E) : α → E` (notation `μ[f \| m]`) | `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:100` | ✅ | `W*_k := μ[log-return \| ℱ_k]` 型で条件付き成長率を real-valued 定義 |
| tower / consistency | `condExp_condExp_of_le (hmm₂ : m ≤ m₂) (hm₂ : m₂ ≤ m₀) : μ[μ[f\|m₂]\|m] = μ[f\|m]` | `.../ConditionalExpectation/Basic.lean` | ✅ | k 増加時の入れ子条件付けを畳む (Lévy 証明の内部でも使用) |
| 積分保存 | `integral_condExp (hm : m ≤ m₀) : ∫ x, (μ[f\|m]) x ∂μ = ∫ x, f x ∂μ` | `.../ConditionalExpectation/Basic.lean` | ✅ | `∫ W*_k = ∫ log-return` (単調収束の可積分上界) |

**condExp の型クラス前提 (verbatim, Basic.lean:83, 86–90)**:
`variable {α β E 𝕜 : Type*} [RCLike 𝕜] {m m₀ : MeasurableSpace α} {μ : Measure α} {f g : α → E}` +
`[NormedAddCommGroup E]` + `[NormedSpace ℝ E]`。`E = ℝ` で全て自動発火。**`StandardBorelSpace` は不要。**
値は `m ≤ m₀ ∧ SigmaFinite (μ.trim hm) ∧ Integrable f μ` を満たさなければ `0` に落ちる (境界注意)。

### 1B. Lévy upward / 増加 σ-代数の martingale 収束 (R2 の中核候補)

| 概念 | Mathlib API (verbatim) | file:line | 状態 |
|---|---|---|---|
| **Lévy upward (a.e.)** | `theorem tendsto_ae_condExp (g : Ω → ℝ) : ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g \| ℱ n]) x) atTop (𝓝 ((μ[g \| ⨆ n, ℱ n]) x))` | `Mathlib/Probability/Martingale/Convergence.lean:426` | ✅ |
| L¹ martingale conv (a.e.) | `theorem Integrable.tendsto_ae_condExp (hg : Integrable g μ) (hgmeas : StronglyMeasurable[⨆ n, ℱ n] g) : ∀ᵐ x ∂μ, Tendsto (fun n => (μ[g \| ℱ n]) x) atTop (𝓝 (g x))` | `.../Martingale/Convergence.lean:360` | ✅ |
| Lévy upward (L¹) | `theorem tendsto_eLpNorm_condExp (g : Ω → ℝ) : Tendsto (fun n => eLpNorm (μ[g \| ℱ n] - μ[g \| ⨆ n, ℱ n]) 1 μ) atTop (𝓝 0)` | `.../Martingale/Convergence.lean:439` | ✅ |

**Lévy upward の型クラス前提 (verbatim)**: file-level `variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}`
(Convergence.lean:55) + `section L1Convergence` の `variable [IsFiniteMeasure μ] {g : Ω → ℝ}` (L243)。
⟹ **要件は `[IsFiniteMeasure μ]` と `ℱ : Filtration ℕ m0` のみ。`StandardBorelSpace` / `Polish` は不要。** `g : Ω → ℝ` real-valued。

> **向きの確認 (verbatim guard)**: CT 16.5.1 の `W_∞ = lim_k W*(X_0 | X_{-1..-k})` は k 増加で **条件付けを増やす** =
> σ-代数が `⨆` 方向に増加する **upward (増加) filtration**。⟹ Mathlib `tendsto_ae_condExp` (upward) が向きとして一致。
> 後述の in-project `BackwardMartingale.ae_tendsto` (`ℕᵒᵈ` 減少 filtration) は逆向きで、tail σ-代数を「無限過去そのもの」で
> 直接扱う別ルート。どちらを使うかは R2 実装で確定 (両在庫)。

### 1C. Conditional Jensen (条件付き成長率の単調性 → R2)

| 概念 | Mathlib API (verbatim) | file:line | 状態 |
|---|---|---|---|
| **conditional Jensen (凹)** | `theorem ConcaveOn.condExp_map_le (hm : m ≤ mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConcaveOn ℝ s φ) (hφ_cont : UpperSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) : μ[φ ∘ f \| m] ≤ᵐ[μ] φ ∘ μ[f \| m]` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean:193` | ✅ |
| conditional Jensen (凸) | `theorem ConvexOn.map_condExp_le (hm : m ≤ mα) [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) : φ ∘ μ[f \| m] ≤ᵐ[μ] μ[φ ∘ f \| m]` | `.../CondJensen.lean:168` | ✅ |

**CondJensen の型クラス前提 (verbatim, CondJensen.lean:33)**: `variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]`。
`ℝ` で自動発火。`log` は `Ioi 0` 上 concave かつ `UpperSemicontinuousOn` (連続) なので `s = Ici 0` / `Ioi 0` の閉版で適用可。

### 1D. Filtration / tail σ-代数 — in-project 使用例 (既に整備済)

| 概念 | in-project decl (verbatim) | file:line | 状態 |
|---|---|---|---|
| tail σ-代数 | `def tailSigma (T : Ω → Ω) : MeasurableSpace Ω` (= `⨅ n, comap T^[n]`) | `InformationTheory/Shannon/BackwardFiltration.lean:86` | ✅ 既存 |
| 減少 filtration | `def backwardFiltration ... : Filtration ℕᵒᵈ m₀` | `.../BackwardFiltration.lean:49` | ✅ 既存 |
| **backward martingale conv (a.e.)** | `theorem BackwardMartingale.ae_tendsto [IsProbabilityMeasure μ] (hf : Martingale f ℋ μ) (hf_int : Integrable (f (OrderDual.toDual 0)) μ) : ∃ g, StronglyMeasurable[⨅ n, ℋ (toDual n)] g ∧ ∀ᵐ ω ∂μ, Tendsto (fun n ↦ f (toDual n) ω) atTop (𝓝 (g ω))` | `InformationTheory/Shannon/BackwardMartingale.lean:766` | ✅ 既存 (自作済) |
| martingale = condExp | `theorem backwardMartingale_eq_condExp ...` | `.../BackwardMartingale.lean:95` | ✅ 既存 |

> **重要所見**: 本 family は既に `condExp` / `Filtration` / martingale 収束を **大量に使用済** —
> `BackwardMartingale.lean` (34 mentions)、`Probability/TwoSidedExtension/{Backward,LogCondIntegral,CondExpMeasurePreserving}.lean` (34/47/10 mentions)。
> **R2 の condExp インフラは新規機構ではなく、既存の two-sided extension / SMB 用 backward martingale の再利用面が広い。** R2 壁リスクは低。

---

## Block 2 — 可測選択 / 可測 argmax (R1 gateway、最優先)

### 2A. Compact 上の最大点存在 (存在は在庫)

| 概念 | Mathlib API (verbatim) | file:line | 状態 |
|---|---|---|---|
| **extreme value (連続 → max 存在)** | `theorem IsCompact.exists_isMaxOn [ClosedIciTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMaxOn f s x` | `Mathlib/Topology/Order/Compact.lean:246` | ✅ |
| USC → max 存在 | `theorem UpperSemicontinuousOn.exists_isMaxOn {s : Set α} (ne_s : s.Nonempty) (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) : ∃ x ∈ s, IsMaxOn f s x` | `Mathlib/Topology/Semicontinuity/Basic.lean:745` | ✅ |
| simplex compact | `theorem isCompact_stdSimplex [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] : IsCompact (stdSimplex 𝕜 ι)` (前提 `[Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]`, L31) | `Mathlib/Analysis/Convex/StdSimplex.lean:189` | ✅ |

⟹ **各 ω 固定で「max 点が存在する」ことは在庫で即出る** (`growthRate` の連続性 + `isCompact_stdSimplex`)。
核は「その max 点を ω に対し **可測に選ぶ**」= 可測 argmax。

### 2B. 可測 argmax / 可測選択 — Mathlib 探索結果

| 探索 (loogle / rg) | 結果 |
|---|---|
| `Measurable, IsMaxOn` (loogle) | **`Found 0 declarations mentioning IsMaxOn and Measurable.`** |
| `Measurable, IsMinOn` (loogle) | **`Found 0 declarations mentioning Measurable and IsMinOn.`** |
| Kuratowski–Ryll-Nardzewski / Jankov–von Neumann selection (`rg` in `Mathlib/MeasureTheory/Constructions/Polish/`) | 不在 (Polish/ に selection 定理無し。`Kuratowski.lean` は無関係な ℓ∞ 等長埋め込み) |
| `theorem *selection*` (`rg`) | `Finset.rado_selection` (compactness、可測選択ではない) のみ |
| `exists_measurable_*` (`rg`, MeasureTheory/Probability) | superset/subset/monotone 近似/extend のみ。可測 argmax 無し |

⟹ **Mathlib に「parametrized 連続/凹関数の compact 上可測 argmax」ready lemma は不在** (二段検索: conclusion-shape `Measurable+IsMaxOn` も `Found 0`)。

### 2C. 自作テンプレ (Carathéodory 可測選択、部品は完備)

`growthRate ρ_ω X` は `b` で連続・`ω` で可測 (Carathéodory 関数)。simplex は有限次元 compact **metric** (separable)。
標準の Carathéodory 可測選択 (full KRN より軽い、可算稠密経由) で `bstar : Ω → (Fin m → ℝ)` を構成可能。部品:

| 部品 | Mathlib API (verbatim) | file:line | 状態 |
|---|---|---|---|
| 可算 sup の可測性 | `protected theorem Measurable.iSup {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) : Measurable (fun b ↦ ⨆ i, f i b)` | `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean:909` | ✅ |
| `{f ≤ g}` 可測 | `theorem measurableSet_le {f g : δ → α} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {a \| f a ≤ g a}` | `.../BorelSpace/Order.lean:172` | ✅ |
| 可算稠密列 | `denseSeq X : ℕ → X` / `denseRange_denseSeq X` (separable metric) | `Mathlib/Topology/MetricSpace/PiNat.lean:1110` | ✅ |
| 可算稠密集合 | `exists_countable_dense X` | `Mathlib/Topology/Separation/...` (SeparableSpace) | ✅ |

**⚠️ 訂正 (R1 実装で判明)**: 上記「最小 index の可測選択列を組み、極限 (compact) で `bstar ω` へ」レシピは**収束しない** —
`M(ω)` への near-max 列は**値**は収束するが**点**は収束せず (tie 下で argmax index が跳ねる)、compact で取れるのは収束**部分**列のみ
で、その部分列と極限を ω について可測に取るのは full KRN が要る (Mathlib 不在、`BayesEstimator.lean` が selection 定理の
不在を明記)。**採用した構成 = 凹性前提を足した strictly-concave (Tikhonov) 正則化**: 各 `ε>0` で `F ω · − ε‖·‖²` は
**唯一**の最大点 `bEps ε ω` を持ち (`StrictConcaveOn.eq_of_isMaxOn`)、唯一性が「値-最大化列が唯一の argmax に収束」を保証する
ので near-max 列 (`Nat.find` + `Measurable.find`) が `bEps ε ω` に収束 → `measurable_of_tendsto_metrizable` で可測。
`ε→0` で argmax(F) 上の `‖·‖²`-最小点 (= 原点の射影) へ収束し、真の `F` 最大点かつ可測。**実装: `StationaryWinfty.lean`
`exists_measurable_argmax_on_stdSimplex`、proof-done sorryAx-free (~296 行)、追加前提は `[Nonempty (Fin m)]` (m≥1、空 simplex 排除)
+ `ConcaveOn` (regularity、`growthRate` が満たす)。**gateway 判定: genuine 解析壁なし、部品は在庫どおり完備、ただし工数は
~80–200 でなく ~290 行 (KRN 回避に凹性正則化の二重極限を要す)。**

---

## Block 3 — Algoet–Cover sandwich: alphabet 依存 vs 骨格

`SMB/AlgoetCover/Liminf.lean` / `SMB/McMillanBreiman.lean` の各補題を分類 (`[Fintype α] [DecidableEq α] [Nonempty α]` = Liminf.lean:28、pmf-`blockLogAvg` 依存かどうか)。

| 補題 | file:line | Fintype/pmf 依存? | decl lift 可? | pattern 再利用? |
|---|---|---|---|---|
| `tendsto_of_le_liminf_of_limsup_le` (**Mathlib**、sandwich 論理 core) | `Mathlib/Topology/Order/LiminfLimsup.lean:306` | **無 (完全一般)** | ✅ そのまま | ✅ **sandwich の心臓、直接 consume** |
| `shannon_mcmillan_breiman_of_sandwich` | `SMB/McMillanBreiman.lean:88` | 署名は `blockLogAvg`/`entropyRate`/`ErgodicProcess` 依存 (本体 logic は上を delegate) | ❌ | ✅ 4-仮説→tendsto の**組立パターン**を real-valued で写経 |
| `birkhoffAverage_pmfLogCondInfty_tendsto` | `SMB/AlgoetCover/Liminf.lean:144` | pmf 観測量 `pmfLogCondInfty` | ❌ | ✅ Birkhoff→時間平均の**適用パターン** (親 Leg B と同型) |
| `algoet_cover_liminf_bound` | `SMB/AlgoetCover/Liminf.lean:395` | `measurable_of_finite`/`firstBlockZ` 依存 | ❌ | △ liminf 下界を Birkhoff 収束量−誤差で挟む**構造**のみ |
| `liminf_blockLogAvgZ_ge_entropyRate` | `SMB/AlgoetCover/Liminf.lean:345` | 同上 (finite alphabet) | ❌ | △ liminf-sandwich 構造のみ |
| `blockLogAvgZ_bddAbove_ae` | `SMB/AlgoetCover/Liminf.lean:211` | finite alphabet (`measurable_of_finite`) | ❌ | △ block-avg 列の a.s. bddness を要する構造のみ |
| `MRatioLowerZ_le_sq_eventually` | `SMB/AlgoetCover/Liminf.lean:35` | **本質的に likelihood-ratio** (Markov+Borel-Cantelli on `MRatioLowerZ`) | ❌ | ✗ SMB 尤度比固有。portfolio の誤差項 (k 次 Markov 近似) は構造が別 |
| `blockLogAvgZ_ge_negLogQInftyZ_minus_error` | `SMB/AlgoetCover/Liminf.lean:108` | likelihood-ratio 誤差項 (`2 log n / n`) | ❌ | ✗ SMB 固有 |
| `blockLogAvg` (def) + `measurable_blockLogAvg` | `SMB/McMillanBreiman.lean:61,68` | pmf-`blockRV`、`measurable_of_finite` | ❌ | ✗ |
| `expected_blockLogAvg_eq` | `SMB/McMillanBreiman.lean:120` | finite 和への collapse | ❌ | ✗ |
| `birkhoff_ergodic_ae` (**in-project、Birkhoff 本体**) | `InformationTheory/Shannon/BirkhoffErgodic.lean:1000` | **無 (`f : Ω → ℝ` 一般)** | ✅ そのまま | ✅ **k 次条件付き log-return に直接適用** |

**結論 (Block 3)**: finite-alphabet SMB decl 群は **decl として lift 不可** (plan の判断ログ通り、機械確認済)。
しかし **sandwich を閉じる本質は 2 つの alphabet 非依存 core — Mathlib `tendsto_of_le_liminf_of_limsup_le` + in-project `birkhoff_ergodic_ae` — で、両方在庫。**
救えないのは尤度比誤差項 (`MRatioLowerZ*`/`blockLogAvgZ_ge_*`) のみで、これらは portfolio では **不要** (誤差は k 次 Markov 近似から出る別構造)。

---

## Block 4 — 親 Leg B reuse 面 (verbatim)

| decl (verbatim 署名) | file:line | R2/R3 が直接 consume? | 一般化が要る点 |
|---|---|---|---|
| `noncomputable def stationaryLogReturn (X : Ω → Fin m → ℝ) (b : Fin m → ℝ) : Ω → ℝ := fun ω ↦ Real.log (∑ j, b j * X ω j)` | `Portfolio/StationaryMarket.lean:53` | △ | **固定 `b` → ω 依存 `bstar ω`** に一般化。`fun ω ↦ log(∑ j, bstar ω j * X ω j)` で新 def が要る (b が定数でないので def 直接再利用不可) |
| `seqLogWealth_div_tendsto_stationary (μ : Measure Ω) [IsProbabilityMeasure μ] {T} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ) (X : Ω → Fin m → ℝ) (b : Fin m → ℝ) (hint : Integrable (stationaryLogReturn X b) μ) : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (∑ i ∈ range (n+1), stationaryLogReturn X b (T^[i] ω))/(n+1)) atTop (𝓝 (∫ ω, stationaryLogReturn X b ω ∂μ))` | `Portfolio/StationaryMarket.lean:66` | △ | **R3 が写経する Birkhoff テンプレ**。証明は `birkhoff_ergodic_ae` 1 行適用。R3 の k 次条件付き富は `g_k := log(bstar_k · X)` (bstar_k = 無限過去 σ-代数の可測関数) の形 ⟹ `g_k(T^[i] ω)` として Birkhoff **が適用可** (観測量固定)。decl は固定 b 用なので b→bstar 版を新規に書く |
| `stationaryLogReturn_integral_le_of_kuhnTucker (μ) [IsProbabilityMeasure μ] (X) (b bs : Fin m → ℝ) (hb : b ∈ stdSimplex ℝ (Fin m)) (hpos_b : ∀ ω, 0 < ∑ j, b j * X ω j) (hpos_bs : ∀ ω, 0 < ∑ j, bs j * X ω j) (hint_b) (hint_bs) (hint_coord : ∀ i, Integrable (fun ω ↦ X ω i/(∑ j, bs j*X ω j)) μ) (hKT : ∀ i, (∫ ω, X ω i/(∑ j, bs j*X ω j) ∂μ) ≤ 1) : ∫ ω, stationaryLogReturn X b ω ∂μ ≤ ∫ ω, stationaryLogReturn X bs ω ∂μ` | `Portfolio/StationaryMarket.lean:92` | ○ (無条件版) | **R3 upper bound の単文字版に直接 consume**: log-optimal `bs` が任意固定 `b` を dominate。**条件付き版** (`∫ ... ∂μ` → `μ[·\|ℱ_k]`) は conditional KT が要り、CondJensen + 条件付き積分で書き換え。単文字 unconditional はそのまま |
| `growthRate_concaveOn (p) (X) (hp : p ∈ stdSimplex ℝ α) (hpos : ...) : ConcaveOn ℝ (stdSimplex ℝ (Fin m)) (growthRate p X)` | `Portfolio/Basic.lean:139` | ○ | **R1 の凹性前提に直接 consume** (compact 最大点存在 + 可測 argmax の凹性入力)。`growthRate`/`wealthRelative` (Basic.lean:59,55) も reuse |

---

## Key-preconditions box (前提事故が起きやすい lemma)

- **`tendsto_ae_condExp` (Lévy upward)** — `[IsFiniteMeasure μ]` 必須 (確率測度で満たす); `ℱ : Filtration ℕ m0` (**upward = 増加**、W_∞ の向きと一致); `g : Ω → ℝ`; **`StandardBorelSpace`/`Polish` 不要**。極限は `μ[g \| ⨆ n, ℱ n]` (tail 条件付き)。
- **`Integrable.tendsto_ae_condExp`** — 上に加え `StronglyMeasurable[⨆ n, ℱ n] g` (`g` が tail-可測)。W_∞ を「無限過去可測な log-return の条件付き」で書く場合に必要。
- **`ConcaveOn.condExp_map_le` (conditional Jensen)** — `[SigmaFinite (μ.trim hm)]` (確率測度 + `m ≤ m₀` で成立); `UpperSemicontinuousOn φ s` (`log` は連続 OK); `IsClosed s` (`Ici 0` 閉); `∀ᵐ a, f a ∈ s`; `Integrable f μ` **かつ** `Integrable (φ∘f) μ` (両方要る)。`[CompleteSpace E]` (ℝ で OK)。
- **`IsCompact.exists_isMaxOn`** — `[ClosedIciTopology α]` (`α = ℝ` OK); `s.Nonempty`; `ContinuousOn f s`。可測性は保証しない (2C 自作が担う)。
- **`condExp` 境界注意** — `m ≤ m₀ ∧ SigmaFinite (μ.trim hm) ∧ Integrable f μ` を欠くと `μ[f\|m] = 0` に落ちる (`condExp_of_not_integrable` 等)。W*_k 定義時に可積分性を precondition で担保。
- **`birkhoff_ergodic_ae`** — `[IsProbabilityMeasure μ]`; `MeasurePreserving T μ μ`; `Ergodic T μ`; `Integrable f μ`。**観測量 `f` は ω の固定関数** (k 次条件付き log-return は「無限過去可測な bstar_k を X に食わせた固定関数」なので適用可)。

---

## 自作が必要な要素 (優先度順)

1. **[R1] Carathéodory 可測 argmax `bstar : Ω → (Fin m → ℝ)`** (最優先・gateway)
   - 推奨: 可算稠密 `denseSeq` 上の sup を `Measurable.iSup` で可測化 → `measurableSet_le` で近似選択列 → compact 極限。
   - 工数: **~80–200 行**。落とし穴: (a) `growthRate ρ_ω X b` の (ω,b) joint 可測性を先に確立 (条件付き法 ρ_ω の可測依存)、(b) sup が max に一致する連続性、(c) tie-breaking を可測に (最小 index)。
2. **[R2] 条件付き成長率 `W*_k := μ[log-return | ℱ_k]` の定義 + k 単調非減少**
   - 推奨: condExp + conditional Jensen (`ConcaveOn.condExp_map_le`)。単調有界 ⟹ `⨆ k` へ `tendsto`。工数: ~50–150 行。落とし穴: 単調性の向き (条件付け増 ⟹ growth 増) を coarse/fine 取り違えない (honesty guard)。
3. **[R3] real-valued sandwich `(1/n) log S*_n → W_∞`**
   - 推奨: 親 Leg B `seqLogWealth_div_tendsto_stationary` を b→bstar_k に一般化 (下界) + KT dominance + R2 (上界) + Mathlib `tendsto_of_le_liminf_of_limsup_le`。工数: ~150–350 行 (本計画の重心)。落とし穴: k 次近似の**上界誤差制御** (log-optimal ≤ k 近似 + 補正) が解析の心臓、単一既存 lemma には落ちない。
4. **[R3-支援] ω 依存 log-return def `fun ω ↦ log(∑ j, bstar ω j * X ω j)`** + 可積分性 (`E[log‖X_0‖]` 級上界)。工数: ~30 行。

---

## Mathlib 壁の列挙 (`@residual(wall:…)` 候補)

| 候補壁 | loogle 確認 | 判定 |
|---|---|---|
| **可測 argmax / 可測選択** (parametrized concave の compact 上) | `Measurable, IsMaxOn` → **`Found 0`**; `Measurable, IsMinOn` → **`Found 0`**; Polish selection 不在 | **genuine wall ではない** — 部品完備 (2C) の plumbing 自作 (~80–200 行)。**新 wall slug 不要**。撤退時は `sorry + @residual(plan:portfolio-stationary-woo-plan)` |
| real-valued SMB 級 sandwich | sandwich core (`tendsto_of_le_liminf_of_limsup_le`) + Birkhoff (`birkhoff_ergodic_ae`) は在庫 | **M0 では genuine Mathlib gap 露呈せず** — 新 wall slug 不要。上界誤差制御は解析実装 (plan の仕事)、Mathlib primitive 欠落ではない |

**M0 時点で新規 `@residual(wall:…)` を建てる根拠なし。** shared sorry-lemma consolidation も現段階では不要 (壁が確定していない)。
R3 の上界誤差制御が実装で genuine gap と確定した場合のみ、plan 撤退ライン (analytic core を `sorry` + 新 wall slug、組立骨格は救う) に従い新 slug を `docs/audit/audit-tags.md` register に追記。

---

## 撤退ラインへの距離 (plan の retreat lines)

plan の撤退ライン:
1. **R1/R2/R3 いずれか詰まり** → signature を target 形のまま body `sorry` + `@residual(plan:portfolio-stationary-woo-plan)` (load-bearing bundling 禁止)。
2. **R3 が genuine Mathlib gap (real-valued SMB) 確定** → analytic core を `sorry` + 新 `@residual(wall:<name>)` 分離、組立骨格は救う。

**判定 (M0): どちらも発動しない。**
- R1 は Mathlib ready lemma 不在だが部品完備の plumbing 自作で閉じる見込み (genuine 壁ではない) ⟹ ライン 1 は R1 実装が詰まった時のみの保険。
- R3 の sandwich core は在庫 (`tendsto_of_le_liminf_of_limsup_le` + `birkhoff_ergodic_ae` + 親 Leg B テンプレ) ⟹ ライン 2 の「genuine Mathlib gap」は M0 では見えない。
- **新規 degenerate fallback の追加は不要。** plan の 2 本の撤退 exit (`sorry` + `@residual`、仮説 bundling 無し) をそのまま維持。R3 gateway atom (real-valued sandwich が Birkhoff で閉じるかの早期実機判定) を回して初めてライン 2 の要否が確定する。

---

## Starting skeleton (`InformationTheory/Shannon/Portfolio/StationaryWinfty.lean` 出だし、R4 で命名確定)

```lean
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BirkhoffErgodic
import InformationTheory.Shannon.Portfolio.StationaryMarket
import InformationTheory.Shannon.Portfolio.Basic
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.StdSimplex

namespace InformationTheory.Shannon.Portfolio

open MeasureTheory Filter
open scoped BigOperators Topology ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {m : ℕ}

/-- ω 依存 (causal) portfolio の per-epoch log return `log (bstar ω · X ω)`. -/
noncomputable def causalLogReturn (X : Ω → Fin m → ℝ) (bstar : Ω → Fin m → ℝ) : Ω → ℝ :=
  fun ω ↦ Real.log (∑ j, bstar ω j * X ω j)

/-- R1 gateway: 条件付き log-optimal portfolio の可測選択 (Carathéodory 可測 argmax)。 -/
theorem exists_measurable_logOptimal_selection
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → Fin m → ℝ) /- + 条件付き法 ρ_ω の可測依存前提 -/ :
    ∃ bstar : Ω → Fin m → ℝ, Measurable bstar ∧ (∀ ω, bstar ω ∈ stdSimplex ℝ (Fin m)) := by
  sorry -- @residual(plan:portfolio-stationary-woo-plan) — R1 可測選択、部品 2C で自作

/-- CT 16.5.1 完全形 headline (R4 で確定): causal log-optimal 富の成長率 → W_∞。 -/
theorem logOptimal_growth_tendsto_Winfty
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    (X : Ω → Fin m → ℝ) (bstar : Ω → Fin m → ℝ)
    (hbstar_meas : Measurable bstar) (hbstar_simplex : ∀ ω, bstar ω ∈ stdSimplex ℝ (Fin m))
    (hint : Integrable (causalLogReturn X bstar) μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ (∑ i ∈ Finset.range (n + 1), causalLogReturn X bstar (T^[i] ω)) / (n + 1 : ℝ))
        atTop (𝓝 (∫ ω, causalLogReturn X bstar ω ∂μ)) := by
  sorry -- @residual(plan:portfolio-stationary-woo-plan) — R2 単調収束 + R3 sandwich で W_∞ 同定

end InformationTheory.Shannon.Portfolio
```

---

## Gateway verdict (要約)

### R1 — 可測選択 (measurable argmax)
**LIKELY-ABSENT (ready lemma)、ただし genuine 壁ではない。**
- Mathlib に「parametrized 凹/連続関数の compact 上可測 argmax」は不在 (`Measurable, IsMaxOn` / `Measurable, IsMinOn` ともに **`Found 0`**、Jankov–von Neumann / KRN selection も Polish/ に無し)。
- 存在 (`IsCompact.exists_isMaxOn`, `Topology/Order/Compact.lean:246`) + simplex compact (`isCompact_stdSimplex`) + 自作部品 (`Measurable.iSup` BorelSpace/Order.lean:909 / `measurableSet_le` L172 / `denseSeq` PiNat.lean:1110) は完備。
- **nearest template**: `IsCompact.exists_isMaxOn` (存在) + `Measurable.iSup` (可測化)。**自作見積 ~80–200 行** (Carathéodory 可算稠密版、full KRN 不要)。本 family 初の新規機構だが plumbing。

### R3 — real-valued sandwich AEP
**PRESENT (sandwich core は在庫)、genuine Mathlib gap は M0 で露呈せず。**
- sandwich 論理 core = Mathlib `tendsto_of_le_liminf_of_limsup_le` (`Topology/Order/LiminfLimsup.lean:306`、完全一般) + in-project `birkhoff_ergodic_ae` (`BirkhoffErgodic.lean:1000`、`f : Ω → ℝ` 一般) の 2 本、両在庫。
- 親 Leg B `seqLogWealth_div_tendsto_stationary` (`StationaryMarket.lean:66`) が「Birkhoff → 市場 log-return 時間平均」を既に実証済 = R3 が写経するテンプレ。
- finite-alphabet SMB decl 群 (`blockLogAvg`/`MRatioLowerZ*`/`algoet_cover_*`) は decl lift 不可だが **portfolio では不要** (救うべきは論理骨格のみ、それは上記 core で足りる)。
- **残る human-judgment (low-trust)**: k 次近似の**上界誤差制御** (log-optimal ≤ k 近似 + 補正) は単一既存 lemma に落ちず、R3 gateway atom の実機判定を待って初めて「Birkhoff で閉じるか」が確定。M0 段階では新 wall slug の根拠なし。

---

# R3 inventory — real-valued Algoet–Cover sandwich + increasing filtration

> R1+R2 = proof-done sorryAx-free (`StationaryWinfty.lean`)。本節は R3 の 2 obligation の在庫:
> **(a) 抽象 `ℱ : Filtration ℕ m0` を具体 market-past filtration で instantiate**、
> **(b) real-valued AEP `(1/n) log S*_n → W_∞` を Algoet–Cover sandwich で証明**。
> 全署名は Mathlib / in-project を Read して verbatim 確認済。

## 一行サマリ (R3)

**R3 の壁リスク判定 = (b) moderate–heavy self-build、genuine Mathlib primitive gap は無い。**
使う骨格 (sandwich core `tendsto_of_le_liminf_of_limsup_le` + Birkhoff `birkhoff_ergodic_ae` + 親 Leg B テンプレ
`seqLogWealth_div_tendsto_stationary` + R2 monotone-close) は**全て在庫**。
**最重要発見: `TwoSidedExtension/Backward.lean` は既に増加 (not antitone) past filtration `pastFiltration : Filtration ℕ (MeasurableSpace.pi)` を所有**、
向きは CT 16.5.1 と一致 (`pastSigma_mono` 証明済)。ただし **finite alphabet 専用の変数ブロックで宣言**され、
本体構成 (`pastSigma`/`iSup_pastSigma_eq_negPastSigma`) は Fintype-FREE (全 `omit`) ゆえ `α = Fin m → ℝ` で ~5 行再掲可。
**新規 self-build ≈ 2 点**: (i) 具体 filtration の instantiate + `(T,hT,hT_erg)` 正則性配線 (plumbing、壁でない)、
(ii) **上界の pathwise 誤差制御** (真の causal log-wealth ≤ k 次近似 + 消失誤差) = 解析の心臓、R3 gateway atom で
「Barron/Breiman 型 wealth-ratio martingale 自作 (~150–300 行) で閉じるか / genuine wall か」を早期判定。
**最危険所見**: R2 が `[StandardBorelSpace Ω]` を要求 → 具体空間 `ℤ → (Fin m → ℝ)` は `StandardBorelSpace.pi_countable`
(ℤ 可算 × `Fin m → ℝ` 標準 Borel) で発火するが、**ambient 測度 `μZ` と ergodic shift `ergodic_shiftZ` は Fintype 依存で
再利用不可** — R3 は `(μ,T,hT,hT_erg)` を親 Leg B と同様に**正則性仮説**として受ける (二側構成の deferral、load-bearing でない)。

## R3 主定理の見込み形 (R4 で確定)

```lean
-- 具体化: Ω = ℤ → (Fin m → ℝ)、T = 座標シフト、ℱ = pastFiltration、X = coord0
theorem logOptimal_growth_tendsto_Winfty
    (μ : Measure (∀ _ : ℤ, Fin m → ℝ)) [IsProbabilityMeasure μ]         -- pi 測度 (μZ を仮説化)
    (hT : MeasurePreserving shift μ μ) (hT_erg : Ergodic shift μ)        -- 定常エルゴード = 正則性仮説
    (X : (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ) (hX : Measurable X)          -- X = coord0
    /- + hpos / hint / hUB (R2 と同じ市場正則性) -/ :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n ↦ (∑ i ∈ Finset.range (n+1), causalLogReturn X (bstar i) (shift^[i] ω)) / (n+1))
      atTop (𝓝 (condOptGrowthInfty μ X bstar))         -- = W_∞ (R2 が同定)
```

証明戦略 (pseudo-Lean、SMB Algoet–Cover を real-valued へ写経):

```
-- (a) instantiate: ℱ := pastFiltration (α := Fin m → ℝ);  [StandardBorelSpace] ← pi_countable
--     R2 exists_condOptGrowth_tendsto_condOptGrowthInfty μ ℱ X … で bstar / W*_k / W_∞ を得る
-- (b-lower): birkhoff_ergodic_ae hT hT_erg (hint (bstar k)) を causalLogReturn X (bstar k) に適用
--            ⟹ (1/n)∑ log(bstar_k·X∘T^i) → condOptGrowth k = W*_k       (親 Leg B と同型)
--            真の causal ≥ k 近似 (bstar_k は ℱk-可測 = 過去のみ) ⟹ liminf(1/n log S*_n) ≥ W*_k
--            sup_k ⟹ liminf ≥ ⨆ W*_k = W_∞
-- (b-upper): (1/n) log S*_n ≤ (1/n)∑ log(bstar_k·X∘T^i) + err_k(n),  err_k(n) → 0 a.s.
--            ⟹ limsup ≤ W*_k  (per-k)、k↑ で W_∞ (R2 monotone-close = entropyRate_eq_lim の類似)
-- sandwich: tendsto_of_le_liminf_of_limsup_le (W_∞ ≤ liminf ∧ limsup ≤ W_∞)
```

## R3-A. 増加 market-past filtration (in-project 既存 = 最重要発見)

> **SMB two-sided extension が既に「増加 past filtration」を所有**。M0 の Block 1D は antitone な
> `backwardFiltration`/`tailSigma` のみ記録していたが、`TwoSidedExtension/Backward.lean` は別に
> **増加 `Filtration ℕ`** を持つ。plan 判断ログ 3 の「family は antitone のみ所有、増加は genuine 新規」は
> **部分的に誤り** — 構成は既存 (Fintype-free)、真に新規なのは real-alphabet ambient 測度のみ。

| 概念 | in-project decl (verbatim 署名) | file:line | 向き | R3 での扱い |
|---|---|---|---|---|
| **finite past σ-代数** | `@[reducible] def pastSigma (k : ℕ) : MeasurableSpace (∀ _ : ℤ, α) := cylinderEvents (X := fun _ : ℤ ↦ α) {i : ℤ \| -(k : ℤ) ≤ i ∧ i ≤ -1}` | `Backward.lean:64` | **増加** | `α := Fin m → ℝ` で再掲 (本体 Fintype-free)。`{-k ≤ i ≤ -1}` = 直近 k 過去 |
| **単調性 (増加の証明)** | `lemma pastSigma_mono : Monotone (pastSigma (α := α))` (`omit [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSingletonClass α] [IsProbabilityMeasure μ]`) | `Backward.lean:70` | — | **increasing 確定** (longer past = larger σ-algebra)。CT 16.5.1 の向きと一致 |
| **増加 filtration 本体** | `@[entry_point] def pastFiltration : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (∀ _ : ℤ, α)) where seq k := pastSigma k; mono' _ _ hij := pastSigma_mono hij; le' _ := cylinderEvents_le_pi` | `Backward.lean:84` | **増加** | **R2 の `ℱ : Filtration ℕ m0` に直接 instantiate 可** (m0 = `MeasurableSpace.pi`)。本体は `pastSigma`/`pastSigma_mono`/`cylinderEvents_le_pi` のみ参照 = Fintype-FREE (需要インスタンスは `[MeasurableSpace α]` のみ) |
| **無限過去 σ-代数** | `@[reducible] def negPastSigma : MeasurableSpace (∀ _ : ℤ, α) := cylinderEvents (X := fun _ : ℤ ↦ α) {i : ℤ \| i ≤ -1}` | `Backward.lean:97` | — | `⨆ k, pastSigma k` の閉形。W_∞ の tail 条件付け先 |
| **⨆ = 無限過去 (向き整合)** | `lemma iSup_pastSigma_eq_negPastSigma : ⨆ k : ℕ, pastSigma (α := α) k = negPastSigma (α := α)` (`omit [Fintype…] [IsProbabilityMeasure μ]`) | `Backward.lean:107` | — | R2 の `⨆ k, ℱ k` が無限過去に一致することを保証 (Fintype-free) |
| **座標0 (= X = 観測)** | `def coord0 : (∀ _ : ℤ, α) → α := fun x ↦ x 0` / `theorem measurable_coord0 : Measurable coord0` | `Backward.lean:144,149` | — | R3 の `X := coord0` (現在の市場観測)。`Fin m → ℝ` 値でそのまま |

**⚠️ 再利用境界 (Fintype 依存の分水嶺)**:

| 資産 | Fintype 依存? | R3 での扱い |
|---|---|---|
| `pastSigma` / `pastFiltration` / `negPastSigma` / `iSup_pastSigma_eq_negPastSigma` / `pastSigma_mono` / `coord0` | **無** (全 `omit` または未参照) | `α = Fin m → ℝ` で再掲 or 直接再利用。**plumbing** |
| **`μZ` (二側拡張測度)** (`Core.lean:296`) | **有** (finite-alphabet 射影族 `isProjectiveMeasureFamily_shiftedMarginal` + `stationaryContent_tendsto_zero` tightness + `ClosedCompactCylinders`) | **再利用不可**。R3 は pi 測度 `μ` + `MeasurePreserving shift`/`Ergodic shift` を**正則性仮説**として受ける (親 Leg B と同様) |
| **`measurePreserving_shiftZ` (`Core.lean:370`) / `ergodic_shiftZ` (`Core.lean:1045`)** | **有** (`p : ErgodicProcess μ α`、finite alphabet) | **再利用不可**。R3 の `hT`/`hT_erg` は仮説 (二側構成の deferral) |

**標準 Borel 発火 (R2 の新規前提)**: `StandardBorelSpace.pi_countable {ι : Type*} [Countable ι] {α : ι → Type*}
[∀ n, MeasurableSpace (α n)] [∀ n, StandardBorelSpace (α n)] : StandardBorelSpace (∀ n, α n)`
(`Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:150`、**instance**)。
`ι = ℤ` (Countable) × `α n = Fin m → ℝ` (有限 pi of ℝ ⟹ StandardBorel) ⟹ `∀ _ : ℤ, Fin m → ℝ` は `[StandardBorelSpace]`。
測度構造は `MeasurableSpace.pi` = `pastFiltration` の `m0` と一致。**R2 の `[StandardBorelSpace Ω]` + `[Nonempty Ω]` は発火する。**

## R3-B. Birkhoff 下界の再利用面 (親 Leg B + SMB テンプレ)

| decl (verbatim 署名) | file:line | R3 で直接 consume? | 備考 |
|---|---|---|---|
| **Birkhoff 本体** `theorem birkhoff_ergodic_ae {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ) {f : Ω → ℝ} (hf : Integrable f μ) : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ birkhoffAverageReal T f n ω) atTop (𝓝 (∫ x, f x ∂μ))` | `BirkhoffErgodic.lean:1000` | ✅ | `f := causalLogReturn X (bstar k)` (固定可積分観測量) で下界。`bstar k` が ℱk-可測 (= 過去のみ) でも `f` は ω の固定関数 ⟹ 適用可 |
| `noncomputable def birkhoffAverageReal (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ := fun ω ↦ (∑ i ∈ Finset.range (n + 1), f (T^[i] ω)) / (n + 1 : ℝ)` | `BirkhoffErgodic.lean:80` | ✅ | 正規化 `(n+1)`-項/`(n+1)`。R3 主定理の time-average 形と一致 |
| **親 Leg B テンプレ** `@[entry_point] theorem seqLogWealth_div_tendsto_stationary (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ) (X : Ω → (Fin m → ℝ)) (b : Fin m → ℝ) (hint : Integrable (stationaryLogReturn X b) μ) : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ (∑ i ∈ Finset.range (n + 1), stationaryLogReturn X b (T^[i] ω)) / (n + 1 : ℝ)) atTop (𝓝 (∫ ω, stationaryLogReturn X b ω ∂μ))` | `StationaryMarket.lean:66` | △ (写経) | **証明本体 2 行**: `filter_upwards [birkhoff_ergodic_ae hT hT_erg hint]`。R3 は `stationaryLogReturn X b` (固定 b) → `causalLogReturn X (bstar k)` (ω 依存 bstar) に一般化 = 新 decl。積分先 `∫ causalLogReturn X (bstar k) = condOptGrowth k = W*_k` |
| **SMB k 次条件付き Birkhoff** `theorem birkhoffAverage_pmfLogCondMarkov_tendsto` (署名は `pmfLogCondMarkov`/`ErgodicProcess` 依存) | `KMarkovApproximation.lean:119` | ✗ (finite) | R3 下界の**構造アナログ**: k 次条件付き量に Birkhoff → `conditionalEntropyTail k`。real-valued では `condOptGrowth k` へ写経 (decl lift 不可、pattern のみ) |
| **SMB 無限過去 Birkhoff** `theorem birkhoffAverage_pmfLogCondInfty_tendsto (μ) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) : ∀ᵐ x ∂(μZ …), Tendsto (fun n ↦ negLogQInftyZ … n x / n) atTop (𝓝 (entropyRate …))` | `Liminf.lean:144` | ✗ (finite) | 同上。`measurePreserving_shiftZ`+`ergodic_shiftZ`+`integrable_pmfLogCondInfty`+`birkhoff_ergodic_ae` の 4 部品組立 = R3 が写経する骨格 |

## R3-C. sandwich 骨格: alphabet 非依存 vs finite-essential (機械確認)

各 decl が `Fintype`/pmf を署名/本体で参照するかで判定。

| 補題 | file:line | Fintype/pmf 依存? | R3 再利用 |
|---|---|---|---|
| **`tendsto_of_le_liminf_of_limsup_le` (Mathlib、sandwich core)** `theorem … {f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminf u f) (hsup : limsup u f ≤ a) (h : …) (h' : …) : Tendsto u f (𝓝 a)` | `Mathlib/Topology/Order/LiminfLimsup.lean:306` | **無 (完全一般)** | ✅ **sandwich の心臓、直接 consume** (`a := W_∞`) |
| `Filter.limsup_le_limsup` / `ge_of_tendsto'` | Mathlib | 無 | ✅ per-k 上界を tendsto と比較 (Limsup.lean が実証済使用) |
| `Real.tendsto_pow_log_div_mul_add_atTop` (`log n / n → 0`) | Mathlib | 無 | ✅ 誤差項 `2 log n / n → 0` に使用 (Limsup.lean:80 が実証) |
| **R2 monotone-close** `exists_condOptGrowth_tendsto_condOptGrowthInfty` (`Tendsto (condOptGrowth) atTop (𝓝 condOptGrowthInfty)`) | `StationaryWinfty.lean:735` | 無 (real-valued) | ✅ SMB `entropyRate_eq_lim_condEntropy` の役割 = W*_k → W_∞。**R2 が既に所有** |
| `algoet_cover_limsup_bound` (per-k 上界 → k↑ close) | `Limsup.lean:125` | pmf (`blockLogAvg`/`entropyRate`) | ✗ decl / ✅ **組立 pattern** (per-k `limsup ≤ H_k` → `H_k → entropyRate` で close) を写経 |
| `algoet_cover_liminf_bound` (`entropyRate ≤ liminf blockLogAvg`) | `Liminf.lean:395` | pmf (`blockLogAvgZ`/`natProj`) | ✗ decl / ✅ 下界 pattern のみ |
| `limsup_blockLogAvg_le_condEntropyTail` (`limsup ≤ H_k`) | `Limsup.lean:66` | pmf (`blockLogAvg`/`negLogQk`) | ✗ decl / △ **nearest template** for R3 上界 (`limsup (1/n log S*_n) ≤ W*_k`) |
| `blockLogAvg_le_negLogQk_plus_error` (`blockLogAvg ≤ negLogQk/n + 2 log n/n`) | `Limsup.lean:26` | pmf (`negLogQk`) | ✗ | R3 上界誤差の**構造アナログ** (真値 ≤ k 近似 + `2 log n / n`) |
| **`MRatioUp_le_sq_eventually` (SMB 上界誤差の実体)** `(μ) [IsProbabilityMeasure μ] (p : StationaryProcess μ α) (k : ℕ) : ∀ᵐ ω, ∀ᶠ n, MRatioUp μ p k n ω ≤ ENNReal.ofReal ((n:ℝ)^2)` | `MarkovLikelihoodRatio.lean:697` | **本質的 (block 尤度比 + Markov + Borel-Cantelli p-series)** | ✗ **SMB 固有、portfolio では別構造** — wealth-ratio martingale が要る (下記自作) |
| `blockLogAvg`/`negLogQk`/`pmfLogCondMarkov`/`entropyRate`/`conditionalEntropyTail` (defs) | McMillanBreiman/KMarkov | pmf block prob (`measurable_of_finite`) | ✗ | R3 は `causalLogReturn`/`condOptGrowth`/`condOptGrowthInfty` (R2 既存) で代替 |

**結論 (R3-C)**: sandwich を閉じる 3 本の alphabet 非依存 core — Mathlib `tendsto_of_le_liminf_of_limsup_le` +
in-project `birkhoff_ergodic_ae` + **R2 `exists_condOptGrowth_tendsto_condOptGrowthInfty`** — は全在庫。
finite-alphabet SMB decl (`blockLogAvg`/`negLogQ*`/`MRatio*`/`algoet_cover_*`) は decl lift 不可だが、
**救うべきは論理骨格 (per-k 挟み込み → k↑ close) のみで、それは上記 core で足りる**。
救えないのは SMB 固有の上界誤差 `MRatioUp_le_sq_eventually` (block 尤度比) — portfolio の上界誤差は
**wealth-ratio martingale** (別構造、自作) から出る。

## R3-D. 上界: 真の causal log-optimal ≤ k 次近似 (最大 gap)

| 資産 | 状態 | R3 での使用可否 |
|---|---|---|
| **R2 条件付き優越** `exists_condLogOptimalSeq` の第 3 項: `∀ k c, StronglyMeasurable[ℱ k] c → (∀ ω, c ω ∈ stdSimplex …) → μ[causalLogReturn X c \| ℱ k] ≤ᵐ[μ] μ[causalLogReturn X (bstar k) \| ℱ k]` | ✅ 既存 (`StationaryWinfty.lean:600`) | **stage-wise 条件付き優越のみ** — 任意の ℱk-可測 simplex 競合 `c` に対する `μ[·\|ℱk]`-order。**pathwise wealth-ratio bound ではない** |
| **pathwise 上界** `limsup (1/n) log S*_n ≤ W*_k`(+ 誤差) | ❌ 不在 | R2 の条件付き優越 → pathwise limsup への変換に **新規 martingale/Barron 型論法**が要る (下記) |

**gap の正体**: R2 は「各段 k で `bstar_k` が全 ℱk-可測競合を条件付き優越」を与える (stage-wise, in-expectation)。
R3 上界が要するのは「真の causal 富 `S*_n` の time-average log が pathwise (a.s.) に `W*_k + o(1)` で抑えられる」。
この**変換 = wealth-ratio `S*_n / Ŝ_n^{(k)}` の super-martingale 性 + Borel-Cantelli (or Barron/Breiman)** で、
`MRatioUp_le_sq_eventually` の SMB 版 (block 尤度比) の**portfolio アナログ**。単一既存 lemma に落ちない = R3 の解析の心臓。

## Key-preconditions box (R3 で前提事故が起きやすい)

- **`birkhoff_ergodic_ae`** — `{μ} [IsProbabilityMeasure μ]`; `MeasurePreserving T μ μ`; `Ergodic T μ`; `{f : Ω → ℝ} Integrable f μ`。観測量 `f = causalLogReturn X (bstar k)` は**ω の固定関数** (bstar_k が過去可測でも可)。
- **`StandardBorelSpace.pi_countable`** — `[Countable ι]` (ℤ OK) + `[∀ n, StandardBorelSpace (α n)]` (各 `Fin m → ℝ` OK)。測度構造は `MeasurableSpace.pi`。R2 の `[StandardBorelSpace Ω] [Nonempty Ω]` を発火 (Nonempty: pi 空間は `Fin m → ℝ` が Nonempty ⟹ OK)。
- **R2 headline `exists_condOptGrowth_tendsto_condOptGrowthInfty`** — `[StandardBorelSpace Ω] [Nonempty Ω]`; `[IsProbabilityMeasure μ]`; `ℱ : Filtration ℕ m0`; `[Nonempty (Fin m)]` (m≥1); `hX : Measurable X`; `hpos`/`hint`/`hUB` (市場正則性)。**R3 は `ℱ := pastFiltration`、`m0 := MeasurableSpace.pi` で instantiate**。
- **`pastFiltration` 再利用** — 本体は `[MeasurableSpace α]` のみ需要 (Fintype 未参照)。`α = Fin m → ℝ` で再掲時、Lean が未使用 Fintype を auto-omit するか要確認 (最悪 ~5 行再宣言)。**ambient `μZ`/`ergodic_shiftZ` は Fintype 依存で再利用不可** (仮説化)。
- **`tendsto_of_le_liminf_of_limsup_le`** — `IsBoundedUnder (· ≤ ·)` / `(· ≥ ·)` は `isBoundedDefault` で自動、ただし `(1/n) log S*_n` の a.s. bddness を別途要する場合あり (SMB `blockLogAvgZ_bddAbove_ae` の類似)。

## 自作が必要な要素 (R3、優先度順)

1. **[R3-a、plumbing] 具体 filtration instantiate + 正則性配線** (~30–80 行)
   - `pastFiltration (α := Fin m → ℝ)` を再掲 (or 直接) → R2 `exists_condOptGrowth_tendsto_condOptGrowthInfty` に食わせる。
   - `[StandardBorelSpace (∀ _ : ℤ, Fin m → ℝ)]` を `pi_countable` で導出。`(μ, shift, hT, hT_erg)` を仮説化 (μZ/ergodic_shiftZ の代替)。
   - 落とし穴: `MeasurableSpace.pi` (pastFiltration の m0) と `pi_countable` の測度構造の syntactic 一致確認。**壁でない。**
2. **[R3-b-lower、写経] Birkhoff 下界** (~80–150 行)
   - 親 Leg B `seqLogWealth_div_tendsto_stationary` を b→bstar_k に一般化 → `(1/n)∑ log(bstar_k·X∘T^i) → W*_k`。
   - `liminf(1/n log S*_n) ≥ W*_k` (真の causal ≥ k 近似、bstar_k は過去可測) → sup_k で `≥ W_∞`。
   - 落とし穴: 「真の causal ≥ k 近似」の pathwise 不等式 (S*_n は各段 full-past 最適、Ŝ_n^{(k)} は k-past 最適)。
3. **[R3-b-upper、解析の心臓] pathwise 上界誤差制御** (~150–300 行、**最大リスク**)
   - `(1/n) log S*_n ≤ (1/n)∑ log(bstar_k·X∘T^i) + err_k(n)`、`err_k(n) → 0` a.s.
   - 実装候補: wealth-ratio `S*_n/Ŝ_n^{(k)}` の super-martingale + Ville/Doob + Borel-Cantelli (SMB `MRatioUp_le_sq_eventually` の portfolio 版)。
   - **nearest template**: `limsup_blockLogAvg_le_condEntropyTail` (`Limsup.lean:66`) — per-k `limsup ≤ H_k` を eventual bound + tendsto で。real-valued 版 `limsup(1/n log S*_n) ≤ W*_k + 0`。
   - 落とし穴: R2 の条件付き優越 (`μ[·\|ℱk]`-order) は stage-wise であり pathwise limsup へ直結しない (§R3-D)。
4. **[R3、close] sandwich** (~20 行): `tendsto_of_le_liminf_of_limsup_le` で `W_∞ ≤ liminf ∧ limsup ≤ W_∞` を突き合わせ。

## Mathlib / in-project 壁の列挙 (`@residual` 候補)

| 候補壁 | loogle / 機械確認 | 判定 |
|---|---|---|
| **増加 market-past filtration** | in-project `pastFiltration` (`Backward.lean:84`) 既存・増加・Fintype-free。`StandardBorelSpace.pi_countable` (Polish/Basic.lean:150) 発火 | **NOT a wall** — 構成既存、plumbing 自作 (~30–80 行)。**新 slug 不要** |
| **real-alphabet 二側拡張測度 `μZ` + ergodic shift** | in-project `μZ`/`ergodic_shiftZ` は Fintype 依存 (機械確認)。real-alphabet Kolmogorov 拡張は tightness を要す | **NOT a wall (回避)** — R3 は `(μ,T,hT,hT_erg)` を正則性仮説化 (親 Leg B 前例)。二側構成の deferral、genuine gap でない |
| **上界 pathwise 誤差制御** (真 causal ≤ k 近似 + 消失) | Mathlib: `Real.log`-ratio martingale AEP / Barron–Breiman は探索要 (下記)。in-project SMB `MRatioUp_le_sq_eventually` は block 尤度比 (portfolio に lift 不可) | **human-judgment (low-trust)** — wealth-ratio martingale 自作 (~150–300 行) で閉じる公算だが、Barron/Breiman 一般形が要れば genuine wall。**R3 gateway atom で実機判定**。M0/R3 在庫段階では新 slug の根拠なし |

**loogle 確認 (上界誤差の Mathlib 直接資産)**:
- `MeasureTheory.Martingale, Filter.limsup` 系 / general "log-likelihood-ratio AEP" は Mathlib に ready 形 **不在の見込み** (SMB を in-project 自作した事実が裏付け)。
- **要 gateway 実機**: 上界を `sorry` で残しつつ骨格を組み、pathwise 誤差 lemma を単独 atom で `lean-implementer` に投げて「wealth-ratio super-martingale + Borel-Cantelli で閉じるか / genuine wall か」を早期判定 (gateway-atom-first)。**M0/R3 在庫段階で wall 断定はしない** (loogle 0-hit 単独では不十分、in-project SMB pattern の写経可否が未確定)。

## 撤退ラインへの距離 (親 plan `portfolio-stationary-woo-plan.md`)

plan の撤退ライン:
1. **R1/R2/R3 のいずれか詰まり** → signature を target 形のまま body `sorry` + `@residual(plan:portfolio-stationary-woo-plan)` (load-bearing bundling 禁止)。
2. **R3 が genuine Mathlib gap (real-valued SMB) 確定** → analytic core を `sorry` + 新 `@residual(wall:<name>)` 分離、組立骨格は救う。

**判定 (R3 在庫時点)**:
- **ライン 1**: R3-a (plumbing) / R3-b-lower (写経) は詰まる公算低 (骨格在庫)。R3-b-upper が詰まれば**上界 lemma のみ**を `sorry` + `@residual(plan:portfolio-stationary-woo-plan)` で残し、sandwich consumer (骨格) は生かす。**degenerate fallback 追加不要** (plan の 2 exit を維持)。
- **ライン 2**: R3-b-upper の pathwise 誤差制御が gateway atom で「Barron/Breiman 一般形が要る = SMB 級 real-valued AEP の genuine gap」と確定した場合のみ発動 → analytic core (`limsup(1/n log S*_n) ≤ W*_k` の誤差 lemma) を `sorry` + **新 `@residual(wall:<slug>)`** で分離、上下界を仮定した sandwich 骨格 (`tendsto_of_le_liminf_of_limsup_le` consumer) は proof-done で救う。新 slug は `docs/audit/audit-tags.md` register へ。
- **積分核 / AEP 極限 / W_∞ を `*Hypothesis` predicate に抱えさせる形は禁止** (plan 正直性メモ)。retreat exit は `sorry` のみ。

## Starting skeleton (R3、`InformationTheory/Shannon/Portfolio/StationaryWinfty.lean` 追記 or 新 file)

```lean
import InformationTheory.Shannon.Portfolio.StationaryWinfty   -- R2 (condOptGrowth / 選択補題)
import InformationTheory.Shannon.Portfolio.StationaryMarket    -- 親 Leg B (Birkhoff テンプレ)
import InformationTheory.Shannon.BirkhoffErgodic               -- birkhoff_ergodic_ae
import InformationTheory.Probability.TwoSidedExtension.Backward -- pastFiltration (増加、要 Fintype-free 再掲確認)
import Mathlib.MeasureTheory.Constructions.Polish.Basic        -- StandardBorelSpace.pi_countable
import Mathlib.Topology.Order.LiminfLimsup                     -- tendsto_of_le_liminf_of_limsup_le

namespace InformationTheory.Shannon.Portfolio
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal ProbabilityTheory

variable {m : ℕ} [Nonempty (Fin m)]

/-- R3 上界の解析核: 真の causal log-optimal 富の時間平均 log は k 次近似 + 消失誤差で抑えられる。
    gateway atom (wealth-ratio martingale + Borel-Cantelli で閉じるか実機判定)。 -/
theorem causalLogWealth_limsup_le_condOptGrowth
    (μ : Measure (∀ _ : ℤ, Fin m → ℝ)) [IsProbabilityMeasure μ]
    (X : (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ)
    (bstar : ℕ → (∀ _ : ℤ, Fin m → ℝ) → Fin m → ℝ) (k : ℕ)
    /- + shift / hT / hT_erg / hpos / hint / 過去可測性前提 -/ :
    ∀ᵐ ω ∂μ, Filter.limsup
      (fun n ↦ (∑ i ∈ Finset.range (n+1), causalLogReturn X (bstar k) (shiftZ^[i] ω)) / (n+1 : ℝ))
      atTop ≤ condOptGrowth μ X bstar k := by
  sorry -- @residual(plan:portfolio-stationary-woo-plan) — R3-b-upper 解析の心臓、gateway atom

/-- CT 16.5.1 完全形 headline (R4 で命名確定): causal log-optimal 富の成長率 → W_∞。
    (a) pastFiltration で R2 を instantiate、(b) Algoet–Cover sandwich。 -/
theorem logOptimal_growth_tendsto_Winfty
    (μ : Measure (∀ _ : ℤ, Fin m → ℝ)) [IsProbabilityMeasure μ]
    /- (hT : MeasurePreserving shiftZ μ μ) (hT_erg : Ergodic shiftZ μ) + 市場正則性 -/ :
    True := by   -- 具体 signature は R4 で確定 (bstar は R2 選択補題から得る)
  trivial

end InformationTheory.Shannon.Portfolio
```

## Gateway verdict (R3、要約)

**壁リスク判定 = (b) moderate–heavy self-build、genuine Mathlib primitive gap 無し (R3-b-upper に human-judgment 残 1)。**
- **R3-a (増加 filtration instantiate)**: **NOT a wall**。`pastFiltration` (`Backward.lean:84`) が増加 `Filtration ℕ (MeasurableSpace.pi)` を既に所有 (Fintype-free)、`StandardBorelSpace.pi_countable` で R2 前提発火。ambient `μZ`/`ergodic_shiftZ` は Fintype 依存で `(μ,T,hT,hT_erg)` 仮説化 (親 Leg B 前例)。plumbing ~30–80 行。
- **R3-b-lower (Birkhoff 下界)**: **NOT a wall**。`birkhoff_ergodic_ae` + 親 Leg B `seqLogWealth_div_tendsto_stationary` (2 行証明) の写経、b→bstar_k 一般化。~80–150 行。
- **R3-b-upper (pathwise 上界誤差)**: **human-judgment (low-trust)、単一の R3 unknown**。R2 の条件付き優越は stage-wise であり pathwise limsup へ直結しない (§R3-D)。SMB `MRatioUp_le_sq_eventually` (block 尤度比) は portfolio に lift 不可 = wealth-ratio martingale 自作が要る。~150–300 行で閉じる公算だが、Barron/Breiman 一般形が要れば genuine wall。**次に解くべき gateway atom = `causalLogWealth_limsup_le_condOptGrowth` を単独 dispatch し、wealth-ratio super-martingale + Borel-Cantelli で閉じるか実機判定** (gateway-atom-first)。
