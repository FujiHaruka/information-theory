# T2-B Parallel Gaussian Channels + Water-filling のための Mathlib インフラ在庫調査

> 親 seed: [`docs/textbook-roadmap.md`](../textbook-roadmap.md) T2-B 項。
> 先行 seed: [`docs/shannon/awgn-moonshot-plan.md`](awgn-moonshot-plan.md) (T2-A AWGN
> 完成形、`AWGN.lean` + `AWGNAchievability.lean` + `AWGNConverse.lean` +
> `AWGNMain.lean` で `awgn_capacity_closed_form = (1/2) log(1+P/N)` を publish 済)。
>
> 出力先: Lean 実装は `InformationTheory/Shannon/ParallelGaussian/` ディレクトリ
> (当初 flat な `ParallelGaussian.lean` を予定していたが、実装は `Basic.lean` / `KKT.lean` /
> `PerCoord.lean` / `PerCoordRegularity.lean` / `Converse/*.lean` 等に展開された)。
> 規約: `CLAUDE.md` の "Subagent Inventory of Mathlib Lemmas" + "Mathlib-shape-driven
> Definitions" に従う。
>
> **Status (2026-05-19、着手前在庫 — 歴史的)**: 本ファイルは Phase 0 (在庫調査) の成果物。
> 以降のディレクトリ再編で `AWGN.lean`→`AWGN/Basic.lean`、`ChannelCoding.lean`→`ChannelCoding/Basic.lean`、
> `ParallelGaussian.lean`→`ParallelGaussian/` に移動済 (file:line は更新、本文の予定見積りは当時のまま)。
> T2-A AWGN の F-* hypothesis pass-through pattern を流用 + water-filling 特有の
> 新規撤退ライン L-WF1 / L-WF2 / L-PG1 を確定。Phase 1 (plan 起草) は
> [`parallel-gaussian-moonshot-plan.md`](parallel-gaussian-moonshot-plan.md) へ。

## 一行サマリ

**T2-A AWGN で publish 済の per-coordinate API (`awgnChannel`, `awgnCapacity`,
`mutualInfoOfChannel_gaussianInput_closed_form`, `awgn_capacity_closed_form`)
を、`Fin n` indexed の積 (`Measure.pi`) で並べたものに直接乗せられる**。
**Mathlib に water-filling 専用 lemma / KKT 充足性 / Lagrange 一意性のいずれも
不在**で、本 plan は **水位 `ν*` の KKT 性質 (一意性 + 充足) を hypothesis
pass-through 形 (L-WF1 + L-WF2)** で publish する。
**T2-A の F-* 連鎖は per-coordinate hypothesis (L-PG1)** に集約して signature
に渡す。閉形式主定理 `parallelGaussianCapacity P N = ∑ i, (1/2) log(1 + P_i^*/N_i)`
は L-WF1 + L-WF2 + L-PG1 の 3 本撤退発動で seed 規模 ~400-600 行内に着地予定。

---

## 主定理の最終形 (textbook-roadmap T2-B より再掲)

```lean
-- N : Fin n → ℝ≥0   (per-coordinate noise variance)
-- P : ℝ              (total power budget)
-- ν : ℝ              (water level, Lagrange multiplier)
-- waterFillingPower ν N i := max 0 (ν - N i)
-- parallelGaussianCapacity P N := sSup_{p : ∑_i ∫ x_i² ∂p_i ≤ P} I(p; W_parallel)

theorem parallel_gaussian_capacity_formula
    {n : ℕ} (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : ∀ i, IsAwgnChannelMeasurable (N i))
    (ν : ℝ)
    (h_kkt :       /- L-WF1: ν is a KKT optimal water level for (P, N) -/)
    (h_unique :    /- L-WF2: water-filling power vector is the unique optimizer -/)
    (h_per_coord : /- L-PG1: per-coordinate AWGN F-* hypothesis bundle -/) :
    parallelGaussianCapacity P N (parallelGaussianChannel N h_meas)
      = ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))
```

戦略 (pseudo-Lean):

```
-- Step 1: define parallelGaussianChannel via per-coordinate Gaussian noise
--         (Measure.pi over Fin n of gaussianReal x_i (N i))
-- Step 2: parallelGaussianCapacity P N := sSup_{∑ ∫ x_i² ∂p ≤ P} I(p; W_pg)
-- Step 3: per-coordinate decomposition:
--         I(X^n; Y^n) = ∑_i I(X_i; Y_i) (Mathlib に chain rule あり、F-* に集約)
-- Step 4: per-coordinate cap: I(X_i; Y_i) ≤ (1/2) log(1 + P_i / N_i)
--         (T2-A awgnCapacity_eq の per-coordinate 流用)
-- Step 5: power allocation: max_{∑ P_i ≤ P, P_i ≥ 0} ∑ (1/2) log(1 + P_i/N_i)
--         is reached at water-filling P_i^* = max 0 (ν - N_i) for the unique ν
-- Step 6: Step 5 = "Lagrange / KKT" 部分は Mathlib に直接 API なし
--         → L-WF1 (KKT 充足) + L-WF2 (一意性) の hypothesis pass-through で publish
```

---

## A. T2-A AWGN 完成形からの直接再利用 API

T2-A セッションで本日 publish された 4 ファイル合計 548 行を完全に活用する。
**signature と結論形を verbatim 転記する** (CLAUDE.md "Subagent Inventory"
規約: 結論形 verbatim、`[...]` 型クラス括弧省略禁止)。

### A.1 — `awgnChannel` kernel + `IsAwgnChannelMeasurable` (F-4 撤退ライン)

| 概念 | API | file:line | 状態 | T2-B での扱い |
|---|---|---|---|---|
| `IsAwgnChannelMeasurable` | `def IsAwgnChannelMeasurable (N : ℝ≥0) : Prop := Measurable (fun x : ℝ => gaussianReal x N)` | `InformationTheory/Shannon/AWGN/Basic.lean:66` | ✅ 既存 | per-coordinate `N i` で `∀ i, IsAwgnChannelMeasurable (N i)` を hypothesis pass-through |
| `awgnChannel` | `noncomputable def awgnChannel (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : InformationTheory.Shannon.ChannelCoding.Channel ℝ ℝ where toFun x := gaussianReal x N; measurable' := h_meas` | `AWGN.lean:73` | ✅ 既存 | 並列 channel の per-coordinate 構築に直接利用 |
| `awgnChannel_apply` | `@[simp] lemma awgnChannel_apply (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) (x : ℝ) : (awgnChannel N h_meas) x = gaussianReal x N` | `AWGN.lean:78` | ✅ 既存 | simp 用 |
| `awgnChannel.instIsMarkovKernel` | `instance awgnChannel.instIsMarkovKernel (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : IsMarkovKernel (awgnChannel N h_meas) where isProbabilityMeasure x := by show IsProbabilityMeasure (gaussianReal x N); infer_instance` | `AWGN.lean:82` | ✅ 既存 | `parallelGaussianChannel` も IsMarkovKernel を継承 |

### A.2 — `awgnCapacity` 定義 + 等号 (F-2 撤退ライン)

| 概念 | API | file:line | 状態 | T2-B での扱い |
|---|---|---|---|---|
| `awgnCapacity` | `noncomputable def awgnCapacity (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : ℝ := sSup ((fun p : Measure ℝ => (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel p (awgnChannel N h_meas)).toReal) '' { p : Measure ℝ | IsProbabilityMeasure p ∧ ∫ x, x^2 ∂p ≤ P })` | `AWGN.lean:179` | ✅ 既存 | `parallelGaussianCapacity` の per-coordinate 部品 |
| `awgnCapacity_eq` | `theorem awgnCapacity_eq (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (h_bridge_gauss : ...) (h_bdd : ...) (h_max_ent : ...) : awgnCapacity P N h_meas = (1/2) * Real.log (1 + P / (N : ℝ))` | `AWGN.lean:253-273` | ✅ 既存 (F-2 hypothesis form) | per-coordinate 等号を `h_per_coord` (L-PG1) hypothesis として渡す形で利用 |
| `mutualInfoOfChannel_gaussianInput_closed_form` | `theorem mutualInfoOfChannel_gaussianInput_closed_form (P N : ℝ≥0) (hP : (P : ℝ) ≠ 0) (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (h_bridge : (mutualInfoOfChannel (gaussianReal 0 P) (awgnChannel N h_meas)).toReal = differentialEntropy (gaussianReal 0 (P + N)) - differentialEntropy (gaussianReal 0 N)) : (mutualInfoOfChannel (gaussianReal 0 P) (awgnChannel N h_meas)).toReal = (1/2) * Real.log (1 + (P : ℝ) / (N : ℝ))` | `AWGN.lean:121-131` | ✅ 既存 | per-coordinate MI closed form の根拠 (本 plan では使わず、L-PG1 hypothesis 経由で完全に外出し) |
| `awgn_capacity_closed_form` (公開 corollary) | `theorem awgn_capacity_closed_form (P : ℝ) (hP : 0 ≤ P) (N : ℝ≥0) (hN : (N : ℝ) ≠ 0) (h_meas : IsAwgnChannelMeasurable N) (h_bridge_gauss : ...) (h_bdd : ...) (h_max_ent : ...) : awgnCapacity P N h_meas = (1/2) * Real.log (1 + P / (N : ℝ))` | `AWGNMain.lean:87-105` | ✅ 既存 | 同上、本 plan の `parallel_gaussian_capacity_formula` の `h_per_coord` (L-PG1) を組み立てる際の bundling reference |

### A.3 — `IsAwgnTypicalityHypothesis` / `IsAwgnConverseHypothesis` (F-1/F-3 撤退ライン)

| 概念 | API | file:line | 状態 | T2-B での扱い |
|---|---|---|---|---|
| `IsAwgnTypicalityHypothesis` | `def IsAwgnTypicalityHypothesis (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop := ∀ {R : ℝ}, 0 < R → R < (1/2) * Real.log (1 + P / (N : ℝ)) → ∀ {ε : ℝ}, 0 < ε → ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∃ (M : ℕ) (_hM_lb : Nat.ceil (Real.exp ((n : ℝ) * R)) ≤ M) (c : AwgnCode M n P), ∀ m, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal < ε` | `AWGNAchievability.lean:39-45` | ✅ 既存 (F-1) | 本 plan は capacity formula のみで achievability/converse 主定理は派生せず → 利用しない (将来 T2-B Tier 2 で並列 achievability/converse 公開時に流用) |
| `IsAwgnConverseHypothesis` | `def IsAwgnConverseHypothesis (P : ℝ) (N : ℝ≥0) (h_meas : IsAwgnChannelMeasurable N) : Prop := ∀ {M n : ℕ} (_hM : 2 ≤ M) (c : AwgnCode M n P), ∀ (Pe : ℝ) (_hPe : Pe = ((1 / M : ℝ) * ∑ m : Fin M, (c.toCode.errorProbAt (awgnChannel N h_meas) m).toReal)), Real.log M ≤ (n : ℝ) * ((1 / 2) * Real.log (1 + P / (N : ℝ))) + Real.binEntropy Pe + Pe * Real.log ((M : ℝ) - 1)` | `AWGNConverse.lean:56-64` | ✅ 既存 (F-3) | 同上 |

---

## B. Mathlib Gaussian / pi-measure 在庫 (T2-B 新規利用)

### B.1 — `Measure.pi` over `Fin n` (per-coordinate independent product)

| 概念 | Mathlib API | file:line | 状態 | T2-B での扱い |
|---|---|---|---|---|
| `Measure.pi` | `noncomputable def Measure.pi {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] : Measure (∀ i, α i)` | `Mathlib/MeasureTheory/Constructions/Pi.lean` (主定義箇所) | ✅ 既存 | `parallelGaussianChannel N` の per-coordinate Gaussian 積を `Measure.pi (fun i => gaussianReal (x i) (N i))` で構成 |
| `Measure.pi.instIsProbabilityMeasure` | (instance) `instance Measure.pi.instIsProbabilityMeasure [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (Measure.pi μ)` | `Mathlib/MeasureTheory/Constructions/Pi.lean` | ✅ 既存 | `parallelGaussianChannel` が Markov である自動推論に利用 |
| `MeasureTheory.Measure.pi_pi` | `lemma MeasureTheory.Measure.pi_pi {ι : Type*} {α : ι → Type*} [Fintype ι] [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (s : ∀ i, Set (α i)) (hs : ∀ i, MeasurableSet (s i)) : Measure.pi μ (Set.univ.pi s) = ∏ i, μ i (s i)` | `Mathlib/MeasureTheory/Constructions/Pi.lean` | ✅ 既存 | rectangular set 上の積分公式 (本 plan では capacity formula 主定理に直接は使わず、L-PG1 内部の `parallelGaussianCapacity` decomposition で参照) |

**注意**: `gaussianReal _ _ : Measure ℝ` は `IsProbabilityMeasure` 自動 instance (`Mathlib/Probability/Distributions/Gaussian/Real.lean:209` `instIsProbabilityMeasureGaussianReal`) ⇒ `SigmaFinite` 自動。`Measure.pi (fun i => gaussianReal (x i) (N i))` は型 OK。

### B.2 — 多次元 Gaussian + 加法 (per-coordinate `Y_i = X_i + Z_i`)

| 概念 | Mathlib API | file:line | 状態 | T2-B での扱い |
|---|---|---|---|---|
| `gaussianReal_conv_gaussianReal` | `lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} : (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:613` | ✅ 既存 | T2-A の閉形式の根拠。T2-B では per-coordinate に分解後直接利用 (L-PG1 内部) |
| `gaussianReal_add_gaussianReal_of_indepFun` | `lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P) (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) : P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂)` | `Real.lean:624` | ✅ 既存 | typed RV 形 (per-coordinate) |
| `stdGaussian` (`Fin n`) | `noncomputable def stdGaussian : Measure E` 前提 `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]` | `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean:66` | ✅ 既存 | T2-B では使わない (`Measure.pi` 形で per-coordinate 直書きするほうが MI chain rule に直結) |
| `map_pi_eq_stdGaussian` | `lemma map_pi_eq_stdGaussian : (Measure.pi (fun _ ↦ gaussianReal 0 1)).map (toLp 2) = stdGaussian (EuclideanSpace ℝ ι)` 前提 `[Fintype ι]` | `Multivariate.lean:137` | ✅ 既存 | 参考のみ (本 plan は `Measure.pi` 直書き) |
| `IsGaussian` クラス | `class IsGaussian {E} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] {mE : MeasurableSpace E} (μ : Measure E) : Prop` | `Mathlib/Probability/Distributions/Gaussian/Basic.lean:45` | ✅ 既存 | 参考のみ (本 plan は L-PG1 で per-coordinate 等号を hypothesis pass-through するため、IsGaussian instance は不要) |

### B.3 — `Finset.sum` + `max` (water-filling 数値計算)

| 概念 | Mathlib API | file:line | 状態 | T2-B での扱い |
|---|---|---|---|---|
| `Finset.sum_congr` | `lemma Finset.sum_congr {s₁ s₂ : Finset α} {f g : α → β} (h₁ : s₁ = s₂) (h₂ : ∀ x ∈ s₂, f x = g x) : ∑ x ∈ s₁, f x = ∑ x ∈ s₂, f x` | `Mathlib/Algebra/BigOperators/Basic.lean` | ✅ 既存 | water-filling sum 評価 |
| `Finset.sum_nonneg` | `lemma Finset.sum_nonneg {s : Finset α} {f : α → β} (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∑ i ∈ s, f i` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | ✅ 既存 | `waterFillingPower ν N i ≥ 0` の総和非負 |
| `max_eq_left` / `max_eq_right` | `lemma max_eq_left (h : b ≤ a) : max a b = a` / `lemma max_eq_right (h : a ≤ b) : max a b = b` | `Mathlib/Order/Lattice.lean` | ✅ 既存 | water-filling `max 0 (ν - N_i)` の場合分け |
| `le_max_left` / `le_max_right` | `lemma le_max_left (a b : α) : a ≤ max a b` / `lemma le_max_right (a b : α) : b ≤ max a b` | `Mathlib/Order/Lattice.lean` | ✅ 既存 | `0 ≤ max 0 (ν - N_i)` |
| `Real.log_one` | `theorem Real.log_one : Real.log 1 = 0` | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | ✅ 既存 | water-filling 非アクティブ座標 (`N_i ≥ ν` ⇒ `P_i^* = 0` ⇒ `log(1 + 0/N_i) = 0`) |

### B.4 — Lagrange / KKT (Mathlib gap 確認)

| 探索目標 | Mathlib API | 状態 | T2-B での扱い |
|---|---|---|---|
| KKT 条件 | (loogle 不在) — 一般凸最適化の KKT 補題は Mathlib 不在 | 🚫 不在 | **L-WF1 撤退ライン** (hypothesis pass-through 形) |
| Lagrange dual / saddle point | `Mathlib/Analysis/Convex/...` は基本凸性 + Jensen のみ、`saddle_point` 不在 | 🚫 不在 | 同上 |
| Water-filling / Bellman-Ford 等の組合せ最適化 | Mathlib 不在 | 🚫 不在 | **L-WF2 撤退ライン** (一意性 hypothesis) |
| `Finset.argmin` 上での `inverse_function` 一意性 | (本 plan では使わない、L-WF2 で hypothesis に集約) | 🚫 不在 | L-WF2 |

**判断**: Mathlib に water-filling / KKT / Lagrange 専用 API は不在。本 plan では
**L-WF1** (KKT 充足) + **L-WF2** (一意性) を hypothesis pass-through 形で publish。
Discharge は別 plan (`parallel-gaussian-kkt-plan.md` 等) に defer。

---

## C. InformationTheory 既存資産 (per-coordinate MI / chain rule)

### C.1 — `mutualInfoOfChannel` (本 plan で per-coordinate 利用)

| 概念 | API | file:line | 状態 | T2-B での扱い |
|---|---|---|---|---|
| `Channel α β := Kernel α β` | `abbrev Channel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] := Kernel α β` | `InformationTheory/Shannon/ChannelCoding/Basic.lean:50` | ✅ 既存 | `parallelGaussianChannel N : Channel (Fin n → ℝ) (Fin n → ℝ)` |
| `mutualInfoOfChannel p W` | `noncomputable def mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞ := klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` | `ChannelCoding.lean:84` | ✅ 既存 | per-coordinate MI と並列 MI の両方で利用 |
| `outputDistribution` | `noncomputable def outputDistribution (p : Measure α) (W : Channel α β) : Measure β := (jointDistribution p W).snd` | `ChannelCoding.lean:71` | ✅ 既存 | 並列出力分布 |

### C.2 — chain rule (parallel ⇒ per-coordinate 分解)

| 概念 | API | file:line | 状態 | T2-B での扱い |
|---|---|---|---|---|
| `condMutualInfo_chain_rule_X_2var` | `InformationTheory/Shannon/MIChainRule.lean` (chain rule 2 var 形) | `MIChainRule.lean` (調査要) | ✅ 既存 | 本 plan では使わず、L-PG1 内部に集約 (`I(X^n; Y^n) = ∑ I(X_i; Y_i)` は per-coordinate chain rule の memoryless specialization、L-PG1 hypothesis に bundle) |

**判断**: parallel ⇒ per-coordinate 分解部分は Mathlib + InformationTheory 既存 chain rule
で原理的には組めるが、本 plan の scope (~400-600 行) を超える可能性が高い。
**L-PG1 (per-coordinate AWGN F-* hypothesis bundle)** に含める。

### C.3 — `InformationTheory/Shannon/DifferentialEntropy.lean` (max-entropy)

| 概念 | API | file:line | 状態 | T2-B での扱い |
|---|---|---|---|---|
| `differentialEntropy_le_gaussian_of_variance_le` | `theorem differentialEntropy_le_gaussian_of_variance_le {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : μ ≪ volume) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (h_mean : ∫ x, x ∂μ = m) (h_var : ∫ x, (x - m)^2 ∂μ ≤ (v : ℝ)) (h_var_int : Integrable (fun x => (x - m)^2) μ) (h_ent_int : Integrable (fun x => Real.negMulLog ((μ.rnDeriv volume x).toReal)) volume) : differentialEntropy μ ≤ (1/2) * Real.log (2 * Real.pi * Real.exp 1 * v)` | `InformationTheory/Shannon/DifferentialEntropy.lean:510` | ✅ 既存 | per-coordinate max-entropy (本 plan では L-PG1 内部、本 plan の主定理 signature には現れない) |

---

## D. 自作必須 API (本 plan で実装)

優先度順、推定行数付き。

### D.1 — `parallelGaussianChannel : Fin n → ℝ≥0 → Channel (Fin n → ℝ) (Fin n → ℝ)`

**現状**: Mathlib + T2-A 不在。per-coordinate `gaussianReal` を `Measure.pi` で
束ねる必要あり。

**Mathlib-shape-driven 推奨実装**:

```lean
/-- AWGN-per-coordinate measurability hypothesis bundled over `Fin n`. -/
def IsParallelAwgnChannelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) : Prop :=
  ∀ i, IsAwgnChannelMeasurable (N i)

/-- Parallel Gaussian channel: input `x : Fin n → ℝ`, output `y i = x i + z i`
where `z i ∼ 𝒩(0, N i)` independent across coordinates. The output law is
`Measure.pi (fun i => gaussianReal (x i) (N i))`. -/
noncomputable def parallelGaussianChannel {n : ℕ}
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) :
    InformationTheory.Shannon.ChannelCoding.Channel (Fin n → ℝ) (Fin n → ℝ) where
  toFun x := Measure.pi (fun i => gaussianReal (x i) (N i))
  measurable' := by
    -- Strategy: `Measure.pi` の measurability は per-coordinate measurability から
    -- product 化される。Mathlib `Measure.measurable_pi_iff` 系を介す。
    -- 撤退ライン: もし 30-50 行で組めなければ、Channel 型を直接構築する代わりに
    -- 「per-coordinate awgnChannel の合成 (kernel.prod)」形を採用。
    sorry  -- A-1 で discharge
```

工数感: 30-80 行 (Mathlib `Measure.pi` の measurability 補題が m に対する
measurability を return するか確認要)。落とし穴: `Measure.pi` over `Fin n` で
`Measurable (fun x => Measure.pi (fun i => gaussianReal (x i) (N i)))` を組む
には `Kernel.pi` (per-coordinate kernel の積) を経由するのが王道。**規模超過リスク
が顕在化したら L-PG0 (parallel kernel measurability) を追加 hypothesis として
外出し**。

### D.2 — `waterFillingPower ν N : Fin n → ℝ`

**現状**: 純数値定義。

**実装**:

```lean
/-- Water-filling power allocation. Given a water level `ν` and noise vector
`N : Fin n → ℝ≥0`, the allocated power to coordinate `i` is `max 0 (ν - N_i)`.

Cover-Thomas Ch.9.4 Theorem 9.4.1. -/
noncomputable def waterFillingPower {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) : Fin n → ℝ :=
  fun i => max 0 (ν - (N i : ℝ))

@[simp] lemma waterFillingPower_apply {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) (i : Fin n) :
    waterFillingPower ν N i = max 0 (ν - (N i : ℝ)) := rfl

lemma waterFillingPower_nonneg {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) (i : Fin n) :
    0 ≤ waterFillingPower ν N i := by
  unfold waterFillingPower; exact le_max_left _ _
```

工数感: 15-25 行。

### D.3 — `parallelGaussianCapacity P N : ℝ`

**現状**: T2-A `awgnCapacity` の per-coordinate 拡張版。

**Mathlib-shape-driven 推奨定義**:

```lean
/-- Power-constrained parallel Gaussian channel capacity:
sSup of `I(p; W_parallel)` over probability measures `p` on `Fin n → ℝ` whose
total per-coordinate second moment is `≤ P`. -/
noncomputable def parallelGaussianCapacity {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) : ℝ :=
  sSup ((fun p : Measure (Fin n → ℝ) =>
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (parallelGaussianChannel N h_meas)).toReal) ''
        { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
            ∑ i, ∫ x, (x i)^2 ∂p ≤ P })
```

工数感: 20-30 行。

### D.4 — `parallel_gaussian_capacity_formula` 主定理 (L-WF1 + L-WF2 + L-PG1 採用形)

**実装**:

```lean
/-- **L-WF1 hypothesis** (KKT optimality of water level `ν`).
For the unconstrained water-filling problem `max ∑ (1/2) log(1+P_i/N_i) s.t. ∑P_i ≤ P, P_i ≥ 0`,
`ν` is a KKT-optimal Lagrange multiplier iff the total water-filling power equals `P`. -/
def IsWaterFillingKKT {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
  ∑ i, waterFillingPower ν N i = P

/-- **L-WF2 hypothesis** (uniqueness + optimality of water-filling).
The water-filling allocation achieves the supremum of the per-coordinate sum
`∑ (1/2) log(1 + P_i/N_i)` subject to `∑ P_i ≤ P, P_i ≥ 0`. -/
def IsWaterFillingOptimal {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
  ∀ (P' : Fin n → ℝ), (∀ i, 0 ≤ P' i) → (∑ i, P' i ≤ P) →
    ∑ i, (1/2) * Real.log (1 + P' i / (N i : ℝ))
      ≤ ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-- **L-PG1 hypothesis** (per-coordinate AWGN F-* bundle).
Bridges `parallelGaussianCapacity` to the per-coordinate sum
`∑ (1/2) log(1 + P_i^*/N_i)` for the (unique) water-filling allocation.
Encapsulates:
  (a) chain rule `I(X^n; Y^n) = ∑ I(X_i; Y_i)` for memoryless parallel channel,
  (b) per-coordinate F-2 MI bridge + max-entropy + bddAbove (i.e. `awgnCapacity_eq`
      applied per coordinate),
  (c) variance partition feasibility (`∑ Var(X_i) ≤ P ⇒ ∃ Var(X_i) = P_i^*` with
      `∑ P_i^* ≤ P`). -/
def IsParallelGaussianPerCoordReduction {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) (ν : ℝ) : Prop :=
  parallelGaussianCapacity P N h_meas
    = ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-- **Parallel Gaussian capacity closed form** (Cover-Thomas Theorem 9.4.1).

For parallel AWGN channels `Y_i = X_i + Z_i, Z_i ∼ 𝒩(0, N_i)` with total power
constraint `∑ E[X_i²] ≤ P`, the capacity is achieved by water-filling at
level `ν*` satisfying `∑_i max(0, ν* - N_i) = P`:

`C = ∑_i (1/2) log(1 + max(0, ν* - N_i) / N_i)`.

撤退ライン L-WF1 + L-WF2 + L-PG1 全採用形 (hypothesis pass-through 3 本)。
discharge は別 plan へ defer。 -/
theorem parallel_gaussian_capacity_formula {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (ν : ℝ)
    (h_kkt : IsWaterFillingKKT P N ν)
    (h_unique : IsWaterFillingOptimal P N ν)
    (h_per_coord : IsParallelGaussianPerCoordReduction P N h_meas ν) :
    parallelGaussianCapacity P N h_meas
      = ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) :=
  h_per_coord
```

工数感: 70-120 行 (定義 + main + corollary)。

---

## E. 撤退ライン (L-WF1, L-WF2, L-PG1, L-PG0)

T1-B Chernoff `L-S2` / T1-C Cramér `L-C2` / T2-F de Bruijn `L-F1+L-F2` /
T2-A AWGN F-1+F-2+F-3+F-4 と同型 pattern。

### L-WF1 (water-filling KKT condition hypothesis)

- **hypothesis**: `IsWaterFillingKKT P N ν := ∑ i, waterFillingPower ν N i = P`
- **意味**: ν が水位として "全電力 P を使い切る" KKT 条件を満たす
- **discharge plan**: 中間値定理 (`∑_i max(0, ν - N_i)` は ν の連続増加関数で
  ν → ∞ で → +∞、ν = min(N_i) で → 0) ⇒ `parallel-gaussian-kkt-plan.md` (Tier 3)
- **本 plan**: hypothesis pass-through 形で signature に含める

### L-WF2 (water-filling optimality hypothesis)

- **hypothesis**: `IsWaterFillingOptimal P N ν := ∀ P' ≥ 0 with ∑ P' ≤ P, ∑ (1/2) log(1+P'_i/N_i) ≤ ∑ (1/2) log(1+waterFillingPower ν N_i / N_i)`
- **意味**: water-filling 配分が `∑ (1/2) log(1+P_i/N_i)` の最大化解
- **discharge plan**: KKT + 強凸性 (`log` の凹性) ⇒ Lagrange 双対 ⇒ 同 Tier 3 plan
- **本 plan**: hypothesis pass-through

### L-PG1 (per-coordinate AWGN F-* hypothesis bundle)

- **hypothesis**: `IsParallelGaussianPerCoordReduction P N h_meas ν` =
  `parallelGaussianCapacity P N h_meas = ∑ i, (1/2) log(1 + waterFillingPower ν N i / N i)`
- **意味**: 「並列 channel capacity = per-coordinate AWGN capacity sum 評価」
  Bundle 内訳:
  (a) chain rule (memoryless parallel) `I(X^n;Y^n) = ∑ I(X_i;Y_i)`
  (b) per-coordinate F-2 MI bridge + F-2 max-entropy + F-2 bddAbove (i.e. `awgnCapacity_eq`)
  (c) variance partition feasibility (`∑ Var ≤ P ⇒ ∃ allocation`)
- **discharge plan**: `parallel-gaussian-chain-rule-plan.md` (Tier 3、InformationTheory
  既存 `MIChainRule` + `awgnCapacity_eq` 連鎖)
- **本 plan**: hypothesis pass-through。**主定理本体はこの hypothesis だけで
  `:= h_per_coord` で書ける** (KKT/optimality は補助 lemma 群で利用、主定理
  signature に L-WF1/L-WF2 は形式上含めるが本体は `h_per_coord` から直接)。

### L-PG0 (parallel kernel measurability, 任意)

- **hypothesis**: `IsParallelAwgnChannelMeasurable N := ∀ i, IsAwgnChannelMeasurable (N i)`
  または「`Measurable (fun x => Measure.pi (fun i => gaussianReal (x i) (N i)))`」
- **意味**: parallel channel kernel の measurability
- **discharge plan**: T2-A の F-4 と同パターン (T2-A awgn-kernel-measurability-plan
  の per-coordinate 拡張)
- **本 plan**: `IsParallelAwgnChannelMeasurable N := ∀ i, IsAwgnChannelMeasurable (N i)`
  と定義し、parallel kernel 構築時 (D.1) に discharge 試行。30-50 行で組めれば
  本 plan 内、超過すれば追加 hypothesis (`parallel_meas : Measurable ...`) として
  signature に外出し。

---

## F. 危険箇所 (Top 5)

| # | 危険箇所 | リスク | 緩和策 |
|---|---|---|---|
| 1 | `Measure.pi (fun i => gaussianReal (x i) (N i))` の x-measurability | 50-100 行に膨らむ可能性 | L-PG0 hypothesis 外出し or `Kernel.pi` 経由で組む |
| 2 | `waterFillingPower` の場合分けが冗長 (active/inactive coord) | `max 0 (ν - N_i)` の reasoning に case split が散発 | `waterFillingPower_active` / `_inactive` 補助 lemma を用意 |
| 3 | KKT の uniqueness/feasibility に Mathlib lemma 不在 | 200-400 行リスク | L-WF1 + L-WF2 で全外出し |
| 4 | per-coordinate chain rule `I(X^n;Y^n) = ∑ I(X_i;Y_i)` の memoryless specialization | Mathlib + InformationTheory 共に直接 lemma 不在の可能性 | L-PG1 hypothesis bundle に含める |
| 5 | `parallelGaussianCapacity` の `bddAbove` 証明 | Gaussian per-coordinate maxent 直接適用 ⇒ 50-100 行 | L-PG1 hypothesis 内部に bundle、本 plan signature 外 |

---

## G. 規模見積もり

| 自作要素 | 想定行数 | Phase | ファイル |
|---|---|---|---|
| D.1 `parallelGaussianChannel` + Markov instance + `IsParallelAwgnChannelMeasurable` | ~50-100 | A | `ParallelGaussian.lean` |
| D.2 `waterFillingPower` + 基本性質 (nonneg, sum_nonneg) | ~25-40 | A | `ParallelGaussian.lean` |
| D.3 `parallelGaussianCapacity` 定義 | ~25-40 | A | `ParallelGaussian.lean` |
| D.4 撤退ライン predicate (L-WF1, L-WF2, L-PG1) | ~70-100 | B | `ParallelGaussian.lean` |
| D.4 主定理 `parallel_gaussian_capacity_formula` (L-PG1 適用形) | ~30-50 | C | `ParallelGaussian.lean` |
| Corollary (water-filling 構造、active coord 数 etc.) | ~50-100 | D | `ParallelGaussian.lean` |
| skeleton + imports + docstring + namespace | ~80-120 | A-D | `ParallelGaussian.lean` |
| **合計** | **~330-550** | | |

中央予測 **~430 行** (roadmap 「400-600 行」中央寄り)。撤退ライン L-WF1 + L-WF2 +
L-PG1 全採用前提で **~330-450 行**。

---

## H. 着手 skeleton (Phase A 直前用、~70 行)

```lean
import InformationTheory.Shannon.AWGN
import InformationTheory.Shannon.AWGNMain
import InformationTheory.Shannon.ChannelCoding
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# T2-B: Parallel Gaussian Channels + Water-filling (Cover-Thomas Ch.9.4)
-/

namespace InformationTheory.Shannon.ParallelGaussian

set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators Topology

/-! ## D.1 — parallel channel kernel -/

def IsParallelAwgnChannelMeasurable {n : ℕ} (N : Fin n → ℝ≥0) : Prop :=
  ∀ i, InformationTheory.Shannon.AWGN.IsAwgnChannelMeasurable (N i)

noncomputable def parallelGaussianChannel {n : ℕ}
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) :
    InformationTheory.Shannon.ChannelCoding.Channel (Fin n → ℝ) (Fin n → ℝ) := sorry

/-! ## D.2 — water-filling power vector -/

noncomputable def waterFillingPower {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) : Fin n → ℝ :=
  fun i => max 0 (ν - (N i : ℝ))

@[simp] lemma waterFillingPower_apply {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) (i : Fin n) :
    waterFillingPower ν N i = max 0 (ν - (N i : ℝ)) := rfl

lemma waterFillingPower_nonneg {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) (i : Fin n) :
    0 ≤ waterFillingPower ν N i := le_max_left _ _

lemma waterFillingPower_sum_nonneg {n : ℕ} (ν : ℝ) (N : Fin n → ℝ≥0) :
    0 ≤ ∑ i, waterFillingPower ν N i := by
  exact Finset.sum_nonneg (fun i _ => waterFillingPower_nonneg ν N i)

/-! ## D.3 — capacity definition -/

noncomputable def parallelGaussianCapacity {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) : ℝ :=
  sSup ((fun p : Measure (Fin n → ℝ) =>
          (InformationTheory.Shannon.ChannelCoding.mutualInfoOfChannel
              p (parallelGaussianChannel N h_meas)).toReal) ''
        { p : Measure (Fin n → ℝ) | IsProbabilityMeasure p ∧
            ∑ i, ∫ x, (x i)^2 ∂p ≤ P })

/-! ## D.4 — 撤退ライン predicates -/

def IsWaterFillingKKT {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
  ∑ i, waterFillingPower ν N i = P

def IsWaterFillingOptimal {n : ℕ} (P : ℝ) (N : Fin n → ℝ≥0) (ν : ℝ) : Prop :=
  ∀ (P' : Fin n → ℝ), (∀ i, 0 ≤ P' i) → (∑ i, P' i ≤ P) →
    ∑ i, (1/2) * Real.log (1 + P' i / (N i : ℝ))
      ≤ ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

def IsParallelGaussianPerCoordReduction {n : ℕ} (P : ℝ)
    (N : Fin n → ℝ≥0) (h_meas : IsParallelAwgnChannelMeasurable N) (ν : ℝ) : Prop :=
  parallelGaussianCapacity P N h_meas
    = ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ))

/-! ## Main theorem -/

theorem parallel_gaussian_capacity_formula {n : ℕ}
    (P : ℝ) (hP : 0 < P) (N : Fin n → ℝ≥0) (hN : ∀ i, (N i : ℝ) ≠ 0)
    (h_meas : IsParallelAwgnChannelMeasurable N)
    (ν : ℝ)
    (h_kkt : IsWaterFillingKKT P N ν)
    (h_unique : IsWaterFillingOptimal P N ν)
    (h_per_coord : IsParallelGaussianPerCoordReduction P N h_meas ν) :
    parallelGaussianCapacity P N h_meas
      = ∑ i, (1/2) * Real.log (1 + waterFillingPower ν N i / (N i : ℝ)) :=
  h_per_coord

end InformationTheory.Shannon.ParallelGaussian
```

---

## I. Phase 0 で確定すべき判断 (判断ログ #1, #2 候補)

- **判断 #1 (L-PG0 採用形)**: parallel kernel measurability を
  `IsParallelAwgnChannelMeasurable N := ∀ i, IsAwgnChannelMeasurable (N i)` で取り、
  本 plan 内で `Kernel.pi` 経由で discharge を試行する (30-50 行内で組めれば成功)。
  超過したら `parallel_meas : Measurable (fun x => Measure.pi ...)` を追加
  hypothesis として signature に外出し。→ **Phase A 着手時に判定**。

- **判断 #2 (L-PG1 単独採用 vs L-WF1+L-WF2+L-PG1 三本立て)**:
  - **option (a)**: L-PG1 hypothesis 1 本のみ。本体は `:= h_per_coord` で済む。
    Cover-Thomas Theorem 9.4.1 の "water-filling 構造" 部分は corollary 群で
    別途明示。
  - **option (b)**: L-WF1 + L-WF2 + L-PG1 の 3 本。主定理 signature が
    "KKT + uniqueness + capacity 等号" の **textbook 完全形** を露出 (Cover-Thomas
    Theorem 9.4.1 の 3 主張すべてを signature で表現)。
  - **判断**: **option (b) 採用** (publish 価値最大化、judgement #2 で記録、
    `parallel_gaussian_capacity_formula` の主結論は `:= h_per_coord` だが、
    KKT + optimality の hypothesis を signature に露出させることで Cover-Thomas
    Theorem 9.4.1 の完全形に対応)。
