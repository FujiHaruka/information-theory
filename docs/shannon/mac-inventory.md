# MAC (Multiple Access Channel) capacity region — genuine-closure 在庫調査

> 対象: Cover–Thomas 2nd ed. **Theorem 15.3.1** (2-user DMC) を **標準B (proof done = 0 sorry / 0 @residual)** で達成するための Mathlib + in-project API 棚卸し。
> 親計画: [`mac-moonshot-plan.md`](mac-moonshot-plan.md) (旧 statement-level pass-through、CLOSED) / [`mac-l1-discharge-moonshot-plan.md`](mac-l1-discharge-moonshot-plan.md) (旧 partial discharge)。
> **本ファイルは実装も plan 起草もしない — 在庫調査のみ。**

## 一行サマリ

**converse 側 (Fano + chain rule で 3 不等式) はほぼ 100% in-project 既存 — `condMutualInfo` / `mutualInfo_chain_rule` / `condMutualInfo_chain_rule_X_2var` / `condMutualInfo_le_of_markov_joint` / 単一ユーザ memoryless 逆定理 `channel_coding_converse_general_memoryless_pure` がそのまま 2-user に持ち上がる plumbing。** 一方 **achievability 側は「3-way joint typical 集合」(既存単軸 `typicalSet` から iterated-pairing で降りる、構築可) と「3 本の *条件付き* independent-pair 確率下界」(単一ユーザ `jointlyTypicalSet_indep_prob_le` の条件付き一般化、これが真の analytic 核 = 唯一の重い gap) + 「4 誤り事象 Bonferroni + 2 codebook 平均化」(plumbing) に分解される。** 凸包 / closure of capacity region は Mathlib `convexHull` + `closedConvexHull` で表現可能 (gap でなく設計選択)。**genuine-closure を阻む真の analytic 壁は 1 つ: MAC per-event conditional AEP decay** (旧 register `joint-typicality-multi` の核)。

- in-project 既存率 (converse parts): ~95% (Fano + chain rule 完備、残りは 2-user 配線)
- in-project 既存率 (achievability parts): ~55% (typical-set machinery + union bound + codebook averaging は既存単一ユーザから降りる / 条件付き independent-pair 3 本は自作)
- 自作必須 (gateway 起点): **4 項目** (§D)。最有力 gateway atom = **`macJTS_indep_prob_le_X1`** (E1 条件付き independent-pair 下界、単一ユーザ `jointlyTypicalSet_indep_prob_le` の X1-fiber 条件付き版)

---

## 主定理の最終形 (genuine-closure target、再掲)

2-user DMC `W : Kernel (α₁ × α₂) β`、入力 `p₁(x₁) p₂(x₂)` (独立 product)。corner-point 述語 (削除済 scaffold の `InMACCapacityRegion` 形を踏襲):

```lean
-- corner-point form (single product input p₁ ⊗ p₂ の下での 3 不等式)
structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where
  bound₁   : R₁ ≤ I₁           -- I₁ = I(X₁; Y | X₂)
  bound₂   : R₂ ≤ I₂           -- I₂ = I(X₂; Y | X₁)
  boundSum : R₁ + R₂ ≤ Iboth   -- Iboth = I(X₁, X₂; Y)

-- achievability (inner bound、existence form)
theorem mac_achievability
    (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]
    (p₁ : Measure α₁) (p₂ : Measure α₂) [IsProbabilityMeasure p₁] [IsProbabilityMeasure p₂]
    (h_pos : … full-support …)
    {R₁ R₂ : ℝ} (h₁ : 0 < R₁) (h₂ : 0 < R₂)
    (hstrict : R₁ < I(X₁;Y|X₂) ∧ R₂ < I(X₂;Y|X₁) ∧ R₁+R₂ < I(X₁,X₂;Y))
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N, ∀ n ≥ N, ∃ (M₁ M₂ : ℕ) (_lb₁ : ⌈exp(n R₁)⌉ ≤ M₁) (_lb₂ : ⌈exp(n R₂)⌉ ≤ M₂)
      (c : MACCode M₁ M₂ n α₁ α₂ β), (c.averageErrorProb W).toReal < ε'

-- converse (outer bound、3 不等式)
theorem mac_converse … : InMACCapacityRegion R₁ R₂ I(X₁;Y|X₂) I(X₂;Y|X₁) I(X₁,X₂;Y)
```

genuine-closure 証明戦略 (擬似 Lean):

```
-- achievability (Cover-Thomas 15.65-15.84)
1. 2 codebook を独立 i.i.d. ~ p₁⊗p₂ で生成 (random codebook)
2. joint-typical decoder: (X₁(m₁), X₂(m₂), y) ∈ macJointlyTypicalSet なる一意 (m₁,m₂)
3. 4 誤り事象 Bonferroni: E0 (正解 not typ, P→1) + E1 (m₁ 誤, ≤ exp(-n(I(X₁;Y|X₂)-3ε)))
   + E2 (m₂ 誤, ≤ exp(-n(I(X₂;Y|X₁)-3ε))) + E3 (両誤, ≤ exp(-n(I(X₁,X₂;Y)-3ε)))
4. R₁<I₁ ∧ R₂<I₂ ∧ R₁+R₂<Iboth で全項 →0 → ∃ codebook で avgErr<ε' (random→deterministic)

-- converse (Cover-Thomas 15.85-15.97)
1. Fano: nRₖ ≤ I(X_k^n; Y^n | …) + nεₙ      -- fano_inequality_measure_theoretic
2. chain rule single-letterize: I(X₁^n;Y^n|X₂^n) ≤ ∑ᵢ I(X₁ᵢ;Yᵢ|X₂ᵢ)  -- condMutualInfo_chain_rule_X_2var
                                  I(X₁^n,X₂^n;Y^n) ≤ ∑ᵢ I(X₁ᵢ,X₂ᵢ;Yᵢ)  -- mutualInfo_chain_rule
3. memoryless: 各 letter で I(X₁ᵢ;Yᵢ|X₂ᵢ) ≤ I(X₁;Y|X₂) を取り、n⁻¹ で corner-point へ
```

---

## §A. in-project 流用資産

### A1. converse 部品 (Fano + chain rule、ほぼ完備)

| 概念 | API | file:line | 状態 | MAC での扱い |
|---|---|---|---|---|
| 測度論的条件付き MI `I(X;Y\|Z)` | `condMutualInfo (μ : Measure Ω) [IsFiniteMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞` | `InformationTheory/Shannon/CondMutualInfo.lean:59` | ✅ 既存 | corner cut rate `I₁ = I(X₁;Y\|X₂)` 等の定義の実体。Z=X₂ で直接使う |
| 条件付き MI 非負 | `condMutualInfo_nonneg … : 0 ≤ condMutualInfo μ Xs Yo Zc` | `CondMutualInfo.lean:69` | ✅ | rate 下界の符号管理 |
| 条件付き MI 有限 (finite α) | `condMutualInfo_ne_top [Fintype X] [MeasurableSingletonClass X] [Fintype Y] … [Fintype Z] … (μ) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs Yo Zc) (hXs hYo hZc) : condMutualInfo μ Xs Yo Zc ≠ ∞` | `CondMutualInfo.lean:320` | ✅ | chain rule の項相殺 (`ENNReal.add_le_add_iff_left`) に必須の finiteness |
| **MI chain rule** | `mutualInfo_chain_rule (μ) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs Yo Zc) (hXs hYo hZc) : mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` | `CondMutualInfo.lean:214` | ✅ | `I(X₁,X₂;Y) = I(X₂;Y) + I(X₁;Y\|X₂)` の核。sum-rate 分解 |
| 条件付き MI 対称 | `condMutualInfo_comm … : condMutualInfo μ Xs Yo Zc = condMutualInfo μ Yo Xs Zc` | `CondMutualInfo.lean:285` | ✅ | X-axis/Y-axis chain rule の橋渡し |
| **2-var X-axis 条件付き chain rule** | `condMutualInfo_chain_rule_X_2var (μ) [IsProbabilityMeasure μ] (X_RV X'_RV Yo Wc) (hX hX' hYo hWc) (hWcY_fin : mutualInfo μ Wc Yo ≠ ∞) : condMutualInfo μ (fun ω ↦ (X_RV ω, X'_RV ω)) Yo Wc = condMutualInfo μ X_RV Yo Wc + condMutualInfo μ X'_RV Yo (fun ω ↦ (Wc ω, X_RV ω))` | `ChannelCoding/ConverseMemorylessChainRule.lean:164` | ✅ | **MAC converse の single-letterize 主役**。X = X₁^{<i}, X' = X₁ᵢ で n-letter → ∑ per-letter |
| 2-var Y-axis 条件付き chain rule | `condMutualInfo_chain_rule_Y_2var … : condMutualInfo μ X_RV (fun ω ↦ (A ω, B ω)) Wc = condMutualInfo μ X_RV A Wc + condMutualInfo μ X_RV B (fun ω ↦ (Wc ω, A ω))` | `ConverseMemorylessChainRule.lean:243` | ✅ | 出力側分解。memoryless 出力の単一文字化 |
| 条件付き DPI (augmented Markov) | `condMutualInfo_le_of_markov_joint (μ) [IsProbabilityMeasure μ] (Xs Zc Yo Wc) (…meas) (hmarkov : IsMarkovChain μ (fun ω ↦ (Wc ω, Xs ω)) (fun ω ↦ (Wc ω, Zc ω)) Yo) (hWcYo_fin : mutualInfo μ Wc Yo ≠ ∞) : condMutualInfo μ Xs Yo Wc ≤ condMutualInfo μ Zc Yo Wc` | `ConverseMemorylessChainRule.lean:113` | ✅ | memoryless で per-letter `I(X₁ᵢ;Yᵢ\|X₂ᵢ)` を single-letter `I(X₁;Y\|X₂)` で上から抑える |
| 単一ユーザ memoryless 逆定理 (template) | `channel_coding_converse_general_memoryless_pure (μ) [IsProbabilityMeasure μ] (Msg encoder Ys decoder) (…meas) (hmarkov) (h_memo : IsMemorylessChannel …) (hMsg_uniform) (hcard : 2 ≤ Fintype.card M) (hMI_finite) : Real.log (Fintype.card M) ≤ (∑ i, (mutualInfo μ … i …).toReal) + binEntropy (errorProb …) + errorProb … * Real.log (Fintype.card M - 1)` | `ChannelCoding/ConverseMemoryless.lean:627` | ✅ | **MAC converse の直接ひな型**。3 corner-point 不等式は本定理の (条件付き) 3 インスタンス。`IsMemorylessChannel` / `per_letter_markov_of_memoryless` / `outputs_cond_indep_of_memoryless` も同 file (:66/:502/:554) |
| 測度論的 Fano 不等式 | `fano_inequality_measure_theoretic (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (decoder : Y → X) (hXs hYo hdec) (hcard : 2 ≤ Fintype.card X) : condEntropy μ Xs Yo ≤ binEntropy (errorProb μ Xs Yo decoder) + errorProb μ Xs Yo decoder * Real.log (Fintype.card X - 1)` | `InformationTheory/Fano/Measure.lean:269` | ✅ | 各 rate 不等式の Fano 項。`condEntropy`/`errorProb` も同 file (:83/:88) |
| iid MI 加法 `I(X^n;Y^n)=∑I(Xᵢ;Yᵢ)` | `mutualInfo_pi_eq_sum {n} (μ) [IsProbabilityMeasure μ] (Xs Ys : Fin n → Ω → _) (hXs hYs) (h_iid_joint h_iid_X h_iid_Y) : mutualInfo μ (fun ω i ↦ Xs i ω) (fun ω i ↦ Ys i ω) = ∑ i, mutualInfo μ (Xs i) (Ys i)` | `InformationTheory/Shannon/MIChainRule.lean:309` | ✅ | iid 入力時の single-letterize ショートカット (MAC 入力は codebook 由来で非 iid のため主軸は chain rule、本補題は補助) |

### A2. achievability 部品 (typical-set + union bound + codebook averaging)

| 概念 | API | file:line | 状態 | MAC での扱い |
|---|---|---|---|---|
| Code 構造体 (encoder×decoder) | `structure Code (M n : ℕ) (α β) [MeasurableSpace α] [MeasurableSpace β] where encoder : Fin M → (Fin n → α); decoder : (Fin n → β) → Fin M` | `ChannelCoding/Basic.lean:145` | ✅ | MAC は `MACCode` (encoder×2 + pair-decoder) に一般化要 (§C 参照) |
| pointwise 誤り確率 | `Code.errorProbAt (c) (W : Channel α β) (m) : ℝ≥0∞ := (Measure.pi (fun i ↦ W (c.encoder m i))) (c.errorEvent m)` | `Basic.lean:192` | ✅ | MAC: `Measure.pi (fun i ↦ W (enc₁ m₁ i, enc₂ m₂ i))`、`Fin M₁ × Fin M₂` 上 (§C の `MACCode.errorProbAt` がこの形で既出) |
| 平均誤り確率 ≤ 1 | `averageErrorProb_le_one [Nonempty β] (c) (W) [IsMarkovKernel W] : c.averageErrorProb W ≤ 1` | `Basic.lean:207` | ✅ | MAC 版は M₁·M₂ 正規化に直す (scaffold `MACCode.averageErrorProb` 既出) |
| **2-user joint typical 集合** | `jointlyTypicalSet (μ : Measure Ω) (Xs : ℕ → Ω → α) (Ys : ℕ → Ω → β) (n) (ε) : Set ((Fin n → α) × (Fin n → β))` (3 単軸 typicalSet の交差: X-, Y-, joint-axis) | `Basic.lean:281` | ✅ | **3-way 化のひな型**。MAC は `(X₁,X₂,Y)` の 3 系列を α₁×α₂×β 上の単軸 typicalSet に iterated-pairing で乗せ、4 単軸条件 (X₁,X₂,Y,joint) の交差として再定義 |
| JTS 濃度上界 (b) | `jointlyTypicalSet_card_le [Nonempty α] [Nonempty β] (μ) [IsProbabilityMeasure μ] (Xs Ys) (hXs hYs) (hpos) (n) {ε} (hε) : (card) ≤ Real.exp (n·(entropy μ (jointSequence Xs Ys 0) + ε))` | `Basic.lean:320` | ✅ | φ-injection で 3-tuple JTS を埋め込み `typicalSet_card_le` 適用。MAC でそのまま 3-axis 化可 (旧 `macJointlyTypicalSet_card_le` が実証済の手法) |
| JTS 正解確率→1 (a) | `jointlyTypicalSet_prob_tendsto_one [Nonempty α] [Nonempty β] (μ) [IsProbabilityMeasure μ] (Xs Ys) (hXs hYs) (hindepX hidentX hindepY hidentY hindepZ hidentZ) {ε} (hε) : Tendsto (fun n ↦ μ {ω \| (jointRV Xs n ω, jointRV Ys n ω) ∈ jointlyTypicalSet …}) atTop (𝓝 1)` | `Basic.lean:450` | ✅ | E0 (正解 pair が typical) の bound。MAC は 4 単軸 good event の交差 → `measure_inter3_tendsto_one` (private, :378) の 4-event 版に拡張 |
| **(c) independent-pair 確率上界** | `jointlyTypicalSet_indep_prob_le [Nonempty α] [Nonempty β] (μ) [IsProbabilityMeasure μ] (Xs Ys) (hXs hYs) (hindepX_full : iIndepFun (fun i ↦ Xs i) μ) (hidentX) (hindepY_full) (hidentY) (hposX hposY hposZ) (n) {ε} (hε) : (((μ.map (jointRV Xs n)).prod (μ.map (jointRV Ys n))).real (jointlyTypicalSet μ Xs Ys n ε)) ≤ Real.exp (n·((entropy μ (jointSequence Xs Ys 0) - entropy μ (Xs 0) - entropy μ (Ys 0)) + 3ε))` | `Basic.lean:540` | ✅ (単一ユーザ) / ❌ MAC 条件付き版が gap | **MAC 最重要のひな型**。単一ユーザは `exp(-n(I-3ε))`。MAC は **条件付き 3 本** (E1: X₁ だけ独立して typ → `exp(-n(I(X₁;Y\|X₂)-3ε))`; E2 対称; E3: X₁,X₂ 両独立 → `exp(-n(I(X₁,X₂;Y)-3ε))`) が必要 → §D-gap2 |
| rate ベース JTS 下界 | `jointlyTypicalSet_prob_ge_of_rate {β} … (μ) [IsProbabilityMeasure μ] (Xs Ys) (…) {ε} (hε) {η} (hη) : ∃ N, ∀ n ≥ N, 1 - η ≤ (μ {ω \| … ∈ jointlyTypicalSet …}).toReal` | `AEP/Rate.lean:391` | ✅ | E0 を `1-η` で押さえる closed-form N。MAC 3-axis 版に降ろす |
| random codebook 構造 | `Codebook (M n) (α) := Fin M → (Fin n → α)`; `jointTypicalDecoder`; `codebookToCode`; `codebookMeasure`; `random_codebook_average_le` | `Achievability/Core.lean:50,56,68,216` / `RandomCodebook.lean:1157` | ✅ (単一ユーザ) | MAC は **2 codebook (Codebook M₁ n α₁ × Codebook M₂ n α₂)** の独立積に一般化。`exists_codebook_le_avg` (Main.lean:47) の凸結合論法はそのまま 2-codebook 版に効く |
| per-codeword 誤り分解 (E1+E2) | `errorProbAt_le_E1_plus_E2 (μ Xs Ys) (W) [IsMarkovKernel W] (hM) {ε} (codebook m) : (…errorProbAt…).toReal ≤ (true-not-typ) + ∑ alias (alias-typ)` | `Achievability/Core.lean:83` | ✅ (単一ユーザ E1+E2) | MAC は **4-event Bonferroni** (E0+E1+E2+E3) に拡張。union-bound 構造は同型 (削除済 `mac_error_event_subset_bonferroni` が実証済の手法) → §D-gap3 |
| 単一ユーザ achievability headline | `channel_coding_achievability (W) [IsMarkovKernel W] (p) [IsProbabilityMeasure p] (hp_pos hW_pos) {R} (hR_pos hR) {ε'} (hε') : ∃ N, ∀ n ≥ N, ∃ M (_lb) (c : Code M n α β), (c.averageErrorProb W).toReal < ε'` | `Achievability/Main.lean:219` | ✅ | MAC achievability headline の構造ひな型 (1 rate → rate pair、1 codebook → 2 codebook、E1+E2 → E0..E3) |

### A3. 共通 (entropy / MI / measure 橋渡し)

| 概念 | API | file:line | 状態 | MAC での扱い |
|---|---|---|---|---|
| 離散 MI | `mutualInfo (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞ := klDiv (μ.map (fun ω ↦ (Xs ω, Yo ω))) ((μ.map Xs).prod (μ.map Yo))` | `MutualInfo.lean:36` | ✅ | corner cut rate の実体 (条件無しの I(X₂;Y) など) |
| MI 有限 | `mutualInfo_ne_top (μ) (Xs Yo) (hXs hYo) : mutualInfo μ Xs Yo ≠ ∞` | `MutualInfo.lean:174` | ✅ | chain rule 項相殺の finiteness 供給 |
| channel MI (kernel 形) | `mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞ := klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` | `Basic.lean:81` | ✅ | MAC 版 `mutualInfoOfMACChannel (p₁ p₂) (W)` を `klDiv ((p₁.prod p₂) ⊗ₘ W) …` で定義する起点 |
| entropy↔MI 3項橋 | `mutualInfoOfChannel_eq_HX_add_HY_sub_HZ …` | `Basic.lean:122` | ✅ | achievability 指数 `H(Z₀)-H(X₀)-H(Y₀) = -I` の MAC 条件付き類比に流用 |
| condDistrib / compProd / Measure.pi | Mathlib (§B 参照) | — | ✅ | corner cut rate を p₁⊗p₂⊗W から組む |

---

## §B. Mathlib 借用 API

| 概念 | Mathlib API | file:line | 状態 | MAC での扱い |
|---|---|---|---|---|
| 正則条件付き分布 | `condDistrib (Y : α → Ω) (X : α → β) (μ) : Kernel β Ω` | `Mathlib/Probability/Kernel/CondDistrib.lean:64` | ✅ | `condMutualInfo` の内部。出力側に `[StandardBorelSpace]` (finite alphabet で自動 derive) |
| compProd `μ ⊗ₘ κ` | `Measure.compProd` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:43` | ✅ | joint `p₁⊗p₂ ⊗ₘ W` の構成。`klDiv_compProd_eq_add` が chain rule の根拠 |
| **product measure on blocks** | `Measure.pi (m : ∀ i, Measure (α i)) : Measure (∀ i, α i)` | `Mathlib/MeasureTheory/Constructions/Pi.lean:212` (`irreducible_def pi`) | ✅ | memoryless block 出力 `Measure.pi (fun i ↦ W (enc₁ m₁ i, enc₂ m₂ i))`。`MACCode.errorProbAt` の実体 |
| kernel product `κ ×ₖ η` | `Kernel.prod` (`×ₖ`) | Mathlib `Probability/Kernel/Composition/` | ✅ | `condMutualInfo` 分母の積カーネル (既に `condMutualInfo` 内で使用) |
| **convexHull** | `convexHull (𝕜) : ClosureOperator (Set E)` | `Mathlib/Analysis/Convex/Hull.lean:46` | ✅ | full capacity region = `closure (convexHull ℝ (⋃ p₁ p₂, cornerRegion))` の凸包部 |
| **closed convex hull = closure∘convexHull** | `closedConvexHull_eq_closure_convexHull {s} : closedConvexHull 𝕜 s = closure (convexHull 𝕜 s)` | `Mathlib/Analysis/Convex/Topology.lean:332` (`closedConvexHull` 定義 :294) | ✅ | "closure of convex hull of corner points" を 1 演算子で表現可。**region 表現は gap でなく設計選択** (corner-point form のみ publish か full hull form か) |
| pushforward klDiv 不変 (MeasurableEquiv) | `klDiv_map_measurableEquiv` | Mathlib `InformationTheory/KullbackLeibler/` + in-project `MutualInfo.lean:47` | ✅ | reshape `(Fin n → α₁×α₂×β) ≃ (Fin n→α₁)×(Fin n→α₂)×(Fin n→β)` の klDiv 不変性 |
| `MeasurableEquiv.arrowProdEquivProdArrow` / `prodAssoc` / `prodComm` | Mathlib `MeasurableSpace` | — | ✅ | 3-tuple reshape の measurable equiv 群 (chain rule で多用される既存パターン) |
| iIndepFun (infinitePi) | `iIndepFun`, `iIndepFun_infinitePi` | Mathlib `Probability/Independence/` | ✅ | 2 codebook の独立性 + i.i.d. ambient (`iidAmbientMeasure` 既存パターン) |

**注**: Mathlib 側に「typical set / jointly typical」は完全不在 (loogle `typicalSet` / `jointlyTypical` = unknown identifier、§walls)。typical-set machinery は in-project (`InformationTheory/Shannon/AEP/`) が唯一の出所。

---

## §C. 削除済 scaffold の statement 形 (`common-2026/`、commit `f67ec8ab` で削除)

> **重要**: 削除済 scaffold は **旧 `Common2026` namespace** (現 `InformationTheory` への rename 前の別ツリー)。statement の **型の参考** にはなるが、**load-bearing hypothesis bundling + sorry の pass-through** であって proof done ではない。現 `InformationTheory` は当時より converse 機構 (`condMutualInfo_chain_rule_X_2var` 等) が充実しており genuine closure は当時より容易。

| 削除ファイル | 提供していた statement 形 | genuine 度 | 現タスクでの扱い |
|---|---|---|---|
| `MultipleAccessChannel.lean` (892行) | `MACChannel α₁ α₂ β := Kernel (α₁×α₂) β` (abbrev) / `structure MACCode (M₁ M₂ n α₁ α₂ β)` (encoder₁ encoder₂ decoder) / `MACCode.errorProbAt`/`averageErrorProb`/`decodingRegion`/`errorEvent`/`swap` / `structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop` (bound₁/bound₂/boundSum) + `mk'`/`iff_and`/`swap`/`mono`/`origin_mem` | 構造体・基本 lemma は genuine (型定義+単純性質) | **型をそのまま InformationTheory に再構築**。corner-point 不等式の数学的中身は scaffold では `mac_single_rate_bound₁/₂` が raw scalar hyp pass-through |
| `MACL1Discharge.lean` (544行) | `macJointlyTypicalSet` (3-way JTS) / `macJointlyTypicalSet_card_le` (実証明、φ-injection) / `macJointlyTypicalSet_prob_tendsto_one` (実証明、4 single-axis 交差) | typical-set machinery は **genuine** (単軸 typicalSet から降りる) | **achievability gap1 の既存解の参照**。本体 `mac_capacity_region_inner_bound_with_joint_typ_aep` (:534) は `sorry`+`@residual(plan:mac-l1-discharge-moonshot-plan)` (4-event body deferred) |
| `MACPerEventAEPDecay.lean` (445行) | `IsMACPerEventAEPDecay` (primitive 述語、"Mathlib gap passed through, not sorry") / `mac_E0_aep_decay_tendsto` / `mac_aggregate_decay_*` | E0 decay は genuine、**per-event conditional decay は primitive bundle** | **§D-gap2 の核がここに隠れていた**。"per-event AEP/rate decay = actual Mathlib gap" を述語で受けていた = load-bearing。genuine closure はこれを自作で開ける |
| `MACRandomCodebookAveraging.lean` (516行) | Bonferroni 4-event (E₀..E₃) `IsMACExpectationDecomp` / `mac_expected_error_le_of_decomp` / `IsMACRandomCodebookMarkov` / `mac_avg_error_exists_codebook` | 平均化の凸結合論法は genuine、**4-event 期待値分解は予測 bundle** | §D-gap3 (4-event 平均化) のひな型。単一ユーザ `random_codebook_average_le` と同型 |
| `MACL2Discharge.lean` / `MACFanoConverseBody.lean` / `MACBodyDischarge.lean` | `structure MACFanoBound`/`MACSingleFanoBound`/`MACPerLetterChain₁₂` (Prop bundle) / `mac_converse_fano_body*` / `mac_single_rate_bound₁/₂_with_fano` | **load-bearing predicate bundling (tier 4 defect)** + `sorry`+`@residual(plan:mac-bc-sorry-migration-plan)` | **converse は bundle を捨てて A1 の chain rule 機構で genuine 化**。`MACFanoEntropyData`/`*_of_measure` は測度実体への橋として参考 |
| `MACTimeSharingBody.lean` (447行) | `IsMACTimeSharingHyp` (pentagon convex hull) / `mac_timeShare_ratePair_mem` / `macPentagonRegion_*` | 幾何 (pentagon の凸結合) は genuine、time-sharing 統合は hyp pass-through | time-sharing/convex-hull は **L-MAC5 = scope-out**。corner-point form のみが genuine target。§B の `convexHull` 借用で必要なら別途 |
| `MACCornerAchievabilityBody.lean` (210行) | `mac_errorProbAt_le_one`/`mac_averageErrorProb_le_one`/`mac_averageErrorProb_ne_top`/`mac_jts_error_lt_of_bonferroni_lt`/`mac_jts_error_eventually_lt` | 誤り確率の基本性質は genuine | MAC error-prob 基本 lemma の再構築参照 |

---

## 主要前提の事故注意ボックス (型クラス前提 verbatim、黙って主定理に漏れ込む)

- **`condMutualInfo` / `mutualInfo_chain_rule` / `condMutualInfo_chain_rule_X_2var`** はいずれも出力 X/Y 側に **`[StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]`** を要求。MAC の α₁/α₂/β は `[Fintype] [DecidableEq] [Nonempty] [MeasurableSingletonClass]` を持てば instance chain `[Countable] [MeasurableSingletonClass] → [DiscreteMeasurableSpace] → [StandardBorelSpace]` で **自動 derive** (Fano Phase 3 で実証済の経路)。→ corner-point form では明示追加不要。**ただし条件付け側 Z (=X₂) の型クラスも揃える必要あり** (`condMutualInfo_ne_top` は Z にも `[Fintype Z] [MeasurableSingletonClass Z]`)。
- **`mutualInfo_chain_rule` は `[IsProbabilityMeasure μ]`** (`condMutualInfo` の def 自体は `[IsFiniteMeasure μ]` で済むが chain rule は probability 必須)。
- **chain rule の項相殺は finiteness `mutualInfo μ Wc Yo ≠ ∞` / `condMutualInfo … ≠ ∞` を hyp で要求** (`condMutualInfo_chain_rule_X_2var` の `hWcY_fin`、`condMutualInfo_le_of_markov_joint` の `hWcYo_fin`)。finite alphabet で `mutualInfo_ne_top`/`condMutualInfo_ne_top` から供給。**これを落とすと per-letter 相殺ができず single-letterize が止まる**。
- **achievability の (c) bound `jointlyTypicalSet_indep_prob_le` は `iIndepFun (fun i ↦ Xs i) μ` (full mutual independence) を要求** (pairwise では不足)。MAC 条件付き版でも 2 codebook の full independence + per-letter iid が必須。
- **`fano_inequality_measure_theoretic` は決定的 decoder `Y → X` 形** (randomized `Ω → X` は未対応)。MAC の joint decoder `(Fin n → β) → Fin M₁ × Fin M₂` は決定的なので適合。`2 ≤ Fintype.card X` (= 各 message 空間が non-degenerate) が必須。
- **`channel_coding_converse_general_memoryless_pure` は uniform message `μ.map Msg = (card M)⁻¹ • Measure.count` を要求**。MAC でも uniform message pair (M₁·M₂ 等確率) を ambient で組む必要あり。
- **`Measure.pi` は `irreducible_def`** — 直接 unfold できない。block 出力の評価は `Measure.pi_pi` 等の API 経由 (単一ユーザ `RandomCodebook.lean` の `block_law_*_eq_pi` がパターン)。

---

## §D. gap 一覧 (genuine-closure で一から建てる必要があるもの、優先度順)

> **§D が plan 起草 + gateway-atom-first 着手の起点。** 各 gap に予想規模 + gateway atom 候補。

### gap1 — 3-way joint typical 集合 + AEP + 濃度上界 (構築可、規模中)

- **内容**: `macJointlyTypicalSet μ X1s X2s Ys n ε : Set ((Fin n→α₁)×(Fin n→α₂)×(Fin n→β))` (4 単軸 typicalSet の交差: X₁-, X₂-, Y-, joint-axis)、`macJointlyTypicalSet_card_le`、`macJointlyTypicalSet_prob_tendsto_one`。
- **手法**: 既存 2-user `jointlyTypicalSet` (`Basic.lean:281`) の **iterated-pairing 3-axis 化**。3-tuple 系列を α₁×α₂×β 上の単軸 `typicalSet` に乗せ `typicalSet_card_le`/`typicalSet_prob_tendsto_one` を quote。`measure_inter3_tendsto_one` (private, :378) を 4-event 版へ拡張。
- **規模**: ~200-300 行 (削除済 `MACL1Discharge.lean` で genuine 実証済の手法、再構築)。
- **gateway atom**: `macJointlyTypicalSet_card_le` (φ-injection で 4-tuple → 単軸埋込)。**低リスク** (旧 scaffold で sorry-free 達成歴あり)。

### gap2 — 【最重要・真の analytic 核】3 本の *条件付き* independent-pair 確率下界

- **内容**: 単一ユーザ `jointlyTypicalSet_indep_prob_le` (`Basic.lean:540`、`exp(-n(I-3ε))`) の **条件付き 3 本**:
  - **E1 (X₁ だけ別 codeword)**: `(X̃₁, X₂, Y)` で X̃₁ ⟂ (X₂,Y) のとき JTS に入る確率 ≤ `exp(-n(I(X₁;Y|X₂) - 3ε))`
  - **E2 (X₂ だけ別)**: 対称、≤ `exp(-n(I(X₂;Y|X₁) - 3ε))`
  - **E3 (両方別 codeword)**: `(X̃₁, X̃₂, Y)` で (X̃₁,X̃₂) ⟂ Y のとき ≤ `exp(-n(I(X₁,X₂;Y) - 3ε))`
- **手法**: 単一ユーザは「product measure 上の JTS 質量 = ∑ over JTS の Q-product mass ≤ card·max-mass」。MAC の E1/E2 は **条件付き slice** (X₂ を固定して X₁-fiber 上の typical 質量を測る、Slepian-Wolf 風)。entropy 分解 `H(X₁,X₂,Y) - H(X₂) - H(X₁,Y...) ` の整理で指数が `I(X₁;Y|X₂)` になる。E3 は単一ユーザ (c) の直接 3-axis 類比。
- **規模**: ~400-600 行 (E1/E2 の条件付き fiber が新規。E3 は (c) の流用で軽い)。**genuine-closure の重心はここ**。
- **gateway atom**: **`macJTS_indep_prob_le_X1`** (E1、条件付き X₁-fiber 下界)。これが通れば E2 は対称、E3 は (c) 流用で連鎖。**まず lean-implementer に E1 atom 1 本を dispatch して通るか見る (gateway-atom-first)**。旧 `MACPerEventAEPDecay.IsMACPerEventAEPDecay` が primitive bundle で逃げていた箇所 = ここが真の gap。

### gap3 — 4-event Bonferroni union bound + 2-codebook random averaging (plumbing、規模中)

- **内容**: per-codeword pair 誤り ≤ E0 + E1 + E2 + E3 の union bound (`errorProbAt_le_E1_plus_E2` の 4-event 拡張)、2 codebook 独立積上の期待値 ≤ ∑ 各 event 期待値、`exists_codebook_le_avg` 凸結合で random→deterministic。
- **手法**: 単一ユーザ `Achievability/Core.lean:83` + `RandomCodebook.lean:1157` の同型拡張 (1 codebook → Codebook M₁ n α₁ × Codebook M₂ n α₂)。Fubini/IndepFun は既存パターン。
- **規模**: ~400-500 行 (大半が機械的拡張、削除済 `MACRandomCodebookAveraging.lean` がひな型)。
- **gateway atom**: `mac_errorProbAt_le_bonferroni4` (4-event subset)。**低リスク** (union bound は plumbing)。

### gap4 — converse single-letterize の 2-user 配線 (plumbing、規模小〜中)

- **内容**: Fano (`fano_inequality_measure_theoretic`) → chain rule (`condMutualInfo_chain_rule_X_2var` + `mutualInfo_chain_rule`) → memoryless per-letter DPI (`condMutualInfo_le_of_markov_joint`) → corner-point の 3 不等式。
- **手法**: 単一ユーザ `channel_coding_converse_general_memoryless_pure` (`ConverseMemoryless.lean:627`) の **条件付き 3 インスタンス**。A1 の道具は全部揃っている = **新規 analytic 核なし、純配線**。
- **規模**: ~300-500 行 (Markov chain 前提 `IsMemorylessChannel` の 2-user 版構築 + 3 不等式の組立)。
- **gateway atom**: `mac_converse_bound₁` (R₁ ≤ I(X₁;Y|X₂)、単一不等式)。**低リスク** (converse は in-project 機構で閉じる、§walls なし)。

---

## Mathlib 壁の列挙 (`@residual(wall:…)` 対象)

genuine-closure で **真に Mathlib 不在** なものは 1 family のみ:

| 壁 | loogle 確認 | register 状態 | 判定 |
|---|---|---|---|
| **多変数 joint typicality / per-event conditional AEP decay** (gap1+gap2 の Mathlib 不在部) | `typicalSet` = `unknown identifier 'typicalSet'` / `jointlyTypical` = `unknown identifier 'jointlyTypical'` (Mathlib に typical-set 概念ごと不在) | 既存 register **`joint-typicality-multi`** (audit-tags.md:77、Ch.15 MAC/BC/Relay) | typical-set machinery は in-project (`AEP/`) が出所。**single-axis は既存資産で完備**ゆえ「Mathlib 壁」というより in-project 自作 (gap1 は構築可、gap2 が重心)。**`@residual(wall:joint-typicality-multi)` を新規 `sorry` の暫定退避先として共有 sorry 補題化推奨** (gap2 の E1/E2/E3 を 3 本の sorry で開ける場合、`docs/audit/audit-tags.md`「Shared Mathlib walls」)。ただし **gateway-atom-first で E1 を試し、通れば壁ではなく genuine closure** (CLAUDE.md「壁判定は反証を 1 度試みる」)。 |

**convexHull / closure of capacity region は壁ではない** (Mathlib `convexHull` :46 + `closedConvexHull_eq_closure_convexHull` :332 完備、loogle `convexHull` = 147 declarations)。region の Lean 表現は corner-point form (`InMACCapacityRegion`) か full hull form かの **設計選択**であって gap でない (full hull は L-MAC5 = scope-out)。

**converse 側に壁なし** (Fano + chain rule + DPI すべて in-project 既存)。

---

## 撤退ラインへの距離

親計画 `mac-moonshot-plan.md` の撤退ライン (frozen slug L-MAC1〜L-MAC5):

- **L-MAC1** (multi-user joint typicality body): gap1 が **触れる**。gateway atom `macJointlyTypicalSet_card_le` で genuine 化を試行 → 旧 scaffold で sorry-free 達成歴あり、**発動見込み低**。
- **L-MAC2** (multi-user Fano + chain rule): gap4 が **触れるが発動しない**。当時 (scaffold 構築時) に無かった `condMutualInfo_chain_rule_X_2var` / `condMutualInfo_le_of_markov_joint` / `channel_coding_converse_general_memoryless_pure` が **現 InformationTheory に完備**。converse は純配線で genuine 化可 → **L-MAC2 撤退は overturn 候補** (旧判定は道具不在による過大評価)。
- **L-MAC3** (inner bound existence pass-through): gap2+gap3 が **触れる**。gap2 (条件付き independent-pair 3 本) が唯一の重い analytic 核。
- **L-MAC4** (outer bound `InMACCapacityRegion` pass-through): gap4 で genuine 化可、**発動しない見込み**。
- **L-MAC5** (time-sharing convex hull): **scope-out 維持**。corner-point form のみ genuine target。full hull は §B `convexHull` で将来対応 (本タスク対象外)。

**新規撤退ライン提案** (gap2 が重いため): gateway atom **`macJTS_indep_prob_le_X1` (E1 条件付き下界) を dispatch して通らない**場合 → E1/E2/E3 を **3 本の shared sorry 補題** `@residual(wall:joint-typicality-multi)` で開け、achievability headline を「3 本の per-event decay を hyp でなく **sorry 補題呼び出し**で受ける」形 (load-bearing hyp bundling 禁止、sorry + @residual が退避口) に縮退する。converse 側 (gap4) は壁なしゆえ単独で proof done 到達可能 → **converse を先に genuine closure し、achievability を後続 Phase に分離**する縮退も可。

---

## genuine-closure 着手のための starting skeleton

`InformationTheory/Shannon/MultipleAccessChannel.lean` (型 + headline) の出だし:

```lean
import InformationTheory.Shannon.ChannelCoding.Basic
import InformationTheory.Shannon.ChannelCoding.Achievability.Main
import InformationTheory.Shannon.CondMutualInfo
import InformationTheory.Shannon.ChannelCoding.ConverseMemoryless
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessChainRule
import InformationTheory.Fano.Measure
import Mathlib.Analysis.Convex.Topology   -- closedConvexHull (full region 用、scope 次第)

namespace InformationTheory.Shannon.MAC

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open scoped ENNReal NNReal BigOperators Topology

variable {α₁ α₂ β : Type*}
  [Fintype α₁] [DecidableEq α₁] [Nonempty α₁] [MeasurableSpace α₁] [MeasurableSingletonClass α₁]
  [Fintype α₂] [DecidableEq α₂] [Nonempty α₂] [MeasurableSpace α₂] [MeasurableSingletonClass α₂]
  [Fintype β]  [DecidableEq β]  [Nonempty β]  [MeasurableSpace β]  [MeasurableSingletonClass β]

/-- MAC kernel: Markov kernel from joint input `α₁ × α₂` to output `β`. -/
abbrev MACChannel (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] :=
  Kernel (α₁ × α₂) β

/-- MAC block code: two encoders + joint pair decoder. -/
structure MACCode (M₁ M₂ n : ℕ) (α₁ α₂ β : Type*)
    [MeasurableSpace α₁] [MeasurableSpace α₂] [MeasurableSpace β] where
  encoder₁ : Fin M₁ → (Fin n → α₁)
  encoder₂ : Fin M₂ → (Fin n → α₂)
  decoder  : (Fin n → β) → Fin M₁ × Fin M₂

/-- corner-point capacity region predicate (single product input p₁ ⊗ p₂). -/
structure InMACCapacityRegion (R₁ R₂ I₁ I₂ Iboth : ℝ) : Prop where
  bound₁   : R₁ ≤ I₁
  bound₂   : R₂ ≤ I₂
  boundSum : R₁ + R₂ ≤ Iboth

-- gap2 gateway atom (まず dispatch、gateway-atom-first):
-- E1 conditional independent-pair upper bound. 単一ユーザ jointlyTypicalSet_indep_prob_le の
-- X₁-fiber 条件付き版。通れば E2 対称 / E3 は (c) 流用。
-- theorem macJTS_indep_prob_le_X1 … : … ≤ Real.exp (n·(- I(X₁;Y|X₂) + 3ε)) := by sorry
-- @residual(wall:joint-typicality-multi)   ← gateway 不通時のみ shared sorry 化

-- converse headline (gap4、壁なし純配線で genuine 化目標):
-- theorem mac_converse … : InMACCapacityRegion R₁ R₂ I(X₁;Y|X₂) I(X₂;Y|X₁) I(X₁,X₂;Y) := by sorry

-- achievability headline (gap1+gap2+gap3):
-- theorem mac_achievability … : ∃ N, ∀ n ≥ N, ∃ M₁ M₂ … (c : MACCode …),
--   (c.averageErrorProb W).toReal < ε' := by sorry

end InformationTheory.Shannon.MAC
```

最初に dispatch すべきは **converse (gap4、壁なし)** と **gap2 gateway atom `macJTS_indep_prob_le_X1`** の 2 本。前者が proof done に最短、後者が achievability の重心を早期に判定する。
