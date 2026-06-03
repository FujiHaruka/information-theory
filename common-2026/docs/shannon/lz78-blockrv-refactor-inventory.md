# LZ78 blockRV refactor (Phase 0) — Mathlib API 在庫調査

> **支える計画**: [`lz78-blockrv-refactor-plan.md`](./lz78-blockrv-refactor-plan.md) Phase 0。
> 同種文書: [`shannon-mathlib-inventory.md`](./shannon-mathlib-inventory.md)（Phase 4 KL）、
> [`fano-mathlib-inventory.md`](../fano/fano-mathlib-inventory.md)。
>
> 本在庫の最重要目的 = **K2-a (ergodic + finite → stationary kernel 構成 + disintegration) の
> GO / NO-GO 判定**。CLAUDE.md「Subagent Inventory」基準（`file:line` + 完全 signature +
> `[...]` typeclass prereq verbatim + 結論形 verbatim）厳守。
> 全 typeclass / disintegration の事実は **scratch file を `lake env lean` で機械確認済**（§9）。

## 一行サマリ

**K2-a の最大の壁だった `[StandardBorelSpace (Fin n → α)]` は finite alphabet で完全に無料
（instance chain `MeasurableSingletonClass + Countable → DiscreteMeasurableSpace → StandardBorelSpace`
→ `pi_countable` を機械確認）。disintegration (`Measure.condKernel` / `condDistrib`) も
`Fin n → α` 上の有限 measure で genuine に組める。process 側 kernel の正しい道具は
`ProbabilityTheory.condDistrib`（後ろ向き Bayes ではなく `Y` given `X` の forward conditional、
`condDistrib_apply_of_ne_zero` が `condPhraseProb` の ratio 定義と shape 一致）。
Z-side 既存足場 (`condPhraseProb` / `IsLZ78PerPathParsingFactorization` / `blockProb_neg_log_eq_sum`)
は genuine で、残作業は `factor`/`pos` の proving のみ。converse 側の Kraft (`entropyD_le_expectedLength_of_kraft`)
+ Birkhoff (`birkhoff_ergodic_ae`) も揃う。**自作必要は kernel 層構成 + telescoping + slack 設計の
"組み立て" であって、Mathlib 不在の壁ではない。撤退ライン L-K は発動しない見込み。****既存率 ~90%
（素材レベル）、自作必要 5 件（すべて組み立て）、L-K 発動 NO（条件付き）。**

---

## 主定理の最終形（計画書より再掲）

```lean
theorem lz78_two_sided_optimality_distinct
    {α Ω : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => (lz78DistinctEncodingLength n
            (p.toStationaryProcess.blockRV n ω) : ℝ) / (n : ℝ))
        Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess)) := ...
```

K2-a の crux（kernel 層構成 + per-path factorization）の pseudo-Lean:

```text
-- K2-a: ergodic + finite alphabet だけから forward transition kernel を construct
let κ := condDistrib (obs m) (blockRV m) μ            -- Kernel (Fin m → α) α, StandardBorel 自動
have h_disint : (μ.map (blockRV m)) ⊗ₘ κ
                  = μ.map (fun ω => (blockRV m ω, obs m ω))   := compProd_map_condDistrib hY
-- stationarity (identDistrib_obs_zero) で κ を shift-invariant に固定 (一意性 eq_condKernel_of_…)
-- K2-b: Pₙ{x} を逐次 condDistrib_apply_of_ne_zero で開く (各因子 = prefix block prob ratio)
have h_factor : Pₙ.real {x} = ∏ⱼ condPhraseProb μ p n ω j   -- telescoping
-- K2-b の各 ratio が condDistrib_apply_of_ne_zero の (μ.map X {x})⁻¹ * μ.map(X,Y)({x}×ˢ s) と一致
-- → IsLZ78PerPathParsingFactorization.factor/pos を供給 (K3)
```

---

## §1. StandardBorelSpace 自動 derive（最重要、GO の前提）

**instance chain（すべて Mathlib、`lake env lean` で機械確認済 §9-A）**:

| 概念 | Mathlib API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| 離散 σ代数 派生 | `MeasurableSingletonClass.toDiscreteMeasurableSpace` | `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean:549` | ✅ 既存 | finite α の前段 |
| 離散 → StandardBorel | `standardBorelSpace_of_discreteMeasurableSpace` | `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:119` | ✅ 既存 | `StandardBorelSpace α` 無料 |
| 可算積 | `StandardBorelSpace.pi_countable` | `Mathlib/MeasureTheory/Constructions/Polish/Basic.lean:150` | ✅ 既存 | `StandardBorelSpace (Fin n → α)` 無料 |
| StandardBorel → 可算生成 | `countablyGenerated_of_standardBorel` | `.../Polish/Basic.lean:126` | ✅ 既存 | disintegration `CountablyGenerated` 充足 |
| StandardBorel → singleton 可測 | `measurableSingleton_of_standardBorel` | `.../Polish/Basic.lean:132` | ✅ 既存 | 補助 |

**signature verbatim**:

```lean
-- Defs.lean:549
instance (priority := 100) MeasurableSingletonClass.toDiscreteMeasurableSpace [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] : DiscreteMeasurableSpace α

-- Polish/Basic.lean:119
instance (priority := 100) standardBorelSpace_of_discreteMeasurableSpace [DiscreteMeasurableSpace α]
    [Countable α] : StandardBorelSpace α

-- Polish/Basic.lean:150
instance pi_countable {ι : Type*} [Countable ι] {α : ι → Type*} [∀ n, MeasurableSpace (α n)]
    [∀ n, StandardBorelSpace (α n)] : StandardBorelSpace (∀ n, α n)
```

**結論（機械確認）**: プロジェクトの `α`（`[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α]
[MeasurableSingletonClass α]`）に対し、`Fintype → Countable` が立つので

- `StandardBorelSpace α` … `by infer_instance` で通る
- `StandardBorelSpace (Fin n → α)` … `pi_countable`（`Fin n` は `Countable`）で `by infer_instance` で通る
- `Nonempty (Fin n → α)` … `[Nonempty α]` から `by infer_instance` で通る

**→ disintegration が要求する `[StandardBorelSpace Ω] [Nonempty Ω]` は finite alphabet block で完全に無料。**
これが Phase 0 最重要確認事項であり、**撤退ライン L-K の主要発動条件（StandardBorel 自動 derive で詰まる）は
クリア**。

> ⚠ **load-bearing 注意**: disintegration lemma の `[StandardBorelSpace Ω]` の `Ω` は
> **第二因子（観測値側）** であって、index 空間（第一因子）ではない。`condKernel : Measure (β × Ω)`
> の `Ω` が StandardBorel を要求し、`β`（履歴側）は `CountablyGenerated`（= StandardBorel から自動）
> でよい。block process では「次記号 α」「block 履歴 Fin m → α」とも StandardBorel なので両方 OK。

---

## §2. disintegration / condKernel / condDistrib

### 2-A. 測度の condKernel（後ろ向き Bayes 分解）

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| 測度 condKernel 定義 | `MeasureTheory.Measure.condKernel` | `Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean:361` | ✅ 既存 |
| 分解恒等式 | `MeasureTheory.Measure.IsCondKernel.disintegrate` / `ρ.disintegrate ρ.condKernel` | `Disintegration/Basic.lean:63` (`disintegrate`), instance `StandardBorel.lean:370` | ✅ 既存 |
| singleton での値 | `MeasureTheory.Measure.condKernel_apply_of_ne_zero` | `Disintegration/StandardBorel.lean:389` | ✅ 既存 |
| 一意性 | `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd` | `Disintegration/Unique.lean:82` | ✅ 既存 |

**signature verbatim（typeclass prereq 完全）**:

```lean
-- StandardBorel.lean:361  (variable で [MeasurableSpace α] {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ],
--                          かつ section 冒頭 :77 / Unique :35 の [StandardBorelSpace Ω] [Nonempty Ω])
noncomputable irreducible_def MeasureTheory.Measure.condKernel
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] : Kernel α Ω

-- Basic.lean:63  結論形 verbatim:
lemma MeasureTheory.Measure.IsCondKernel.disintegrate : ρ.fst ⊗ₘ ρCond = ρ
--   (instance ρ.IsCondKernel ρ.condKernel は StandardBorel.lean:370 で自動供給)

-- StandardBorel.lean:389  結論形 verbatim:
lemma MeasureTheory.Measure.condKernel_apply_of_ne_zero [MeasurableSingletonClass α]
    {x : α} (hx : ρ.fst {x} ≠ 0) (s : Set Ω) :
    ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)

-- Unique.lean:82  結論形 verbatim:
theorem ProbabilityTheory.eq_condKernel_of_measure_eq_compProd (κ : Kernel α Ω) [IsFiniteKernel κ]
    (hκ : ρ = ρ.fst ⊗ₘ κ) :
    ∀ᵐ x ∂ρ.fst, κ x = ρ.condKernel x
--   context (Unique.lean:34-39): [mα] [mΩ] [StandardBorelSpace Ω] [Nonempty Ω]
--                                {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]
```

### 2-B. condDistrib（process 側 forward conditional — **K2-a の正しい道具**）

> **計画 ★1 の精緻化**: 計画は disintegration 単独（経路 b）を「任意 measure の Bayes 後ろ向き分解で
> process の条件付き法則と一致する保証が無い」として不採用とした。これは正しいが、Mathlib には
> **process 側の forward conditional `condDistrib Y X μ`** が既にあり、これは「`Y` の `X` 条件付き法則」
> を `(μ.map(X,Y)).condKernel` として構成する（= 計画の経路 a が必要とする kernel そのもの）。
> `condDistrib_apply_of_ne_zero` の結論形が `condPhraseProb`（prefix block prob ratio）と shape 一致。

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| forward 条件付き分布 | `ProbabilityTheory.condDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean:64` | ✅ 既存 |
| disintegration 等式 | `ProbabilityTheory.compProd_map_condDistrib` | `CondDistrib.lean:82` | ✅ 既存 |
| singleton ratio 形 | `ProbabilityTheory.condDistrib_apply_of_ne_zero` | `CondDistrib.lean:75` | ✅ 既存 |
| Markov instance | `ProbabilityTheory.instIsMarkovKernelCondDistrib` | `CondDistrib.lean:68` | ✅ 既存 |

**signature verbatim（typeclass prereq 完全 — `Ω` の `[StandardBorelSpace] [Nonempty]` は file 冒頭 :54）**:

```lean
-- CondDistrib.lean:54  variable で全 lemma に効く:
variable {α β Ω F : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [Nonempty Ω] [NormedAddCommGroup F] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ]
  {X : α → β} {Y : α → Ω}

-- CondDistrib.lean:64
noncomputable irreducible_def condDistrib {_ : MeasurableSpace α} [MeasurableSpace β] (Y : α → Ω)
    (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : Kernel β Ω :=
  (μ.map fun a => (X a, Y a)).condKernel

-- CondDistrib.lean:82  結論形 verbatim:
lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) :
    (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)

-- CondDistrib.lean:75  結論形 verbatim (★ condPhraseProb と shape 一致):
lemma condDistrib_apply_of_ne_zero [MeasurableSingletonClass β]
    (hY : Measurable Y) (x : β) (hX : μ.map X {x} ≠ 0) (s : Set Ω) :
    condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s)
```

**機械確認済（§9-C）**: block process 設定（`X : Ω → (Fin n → α)`, `Y : Ω → α`）で
`compProd_map_condDistrib hY` と `condDistrib_apply_of_ne_zero hY x hX s` が両方 typecheck。
**→ K2-a の kernel 層は `condDistrib` で genuine に構成できる。**

---

## §3. joint law の factorization（compProd_apply 道具）

| 概念 | Mathlib API | file:line | 状態 |
|---|---|---|---|
| compProd 定義 | `MeasureTheory.Measure.compProd` (`⊗ₘ`) | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:43` | ✅ 既存 |
| 一般集合での値 | `MeasureTheory.Measure.compProd_apply` | `MeasureCompProd.lean:61` | ✅ 既存 |
| 矩形での値 | `MeasureTheory.Measure.compProd_apply_prod` | `MeasureCompProd.lean:69` | ✅ 既存 |
| lintegral 形 | `MeasureTheory.Measure.lintegral_compProd` | `MeasureCompProd.lean:183` | ✅ 既存 |

**signature verbatim（typeclass prereq 完全）**:

```lean
-- MeasureCompProd.lean:61  (variable: {μ : Measure α} {κ : Kernel α β})
lemma compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ

-- MeasureCompProd.lean:69  結論形 verbatim:
lemma compProd_apply_prod [SFinite μ] [IsSFiniteKernel κ]
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ ⊗ₘ κ) (s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ
```

> **Mathlib-shape 整合**: `condDistrib_apply_of_ne_zero` の `μ.map(X,Y)({x}×ˢs)` を
> `compProd_apply_prod`（matrix 形）で `∫⁻ a in {x}, κ a s ∂(μ.map X)` に開ける。singleton index
> `{x}` の lintegral は `(μ.map X {x}) * κ x s`（singleton 集中）に縮約 → ratio の telescoping が
> 純 measure-theoretic に閉じる。`condPhraseProb`（`prefixBlockProb m+1 / prefixBlockProb m`）の
> 既存 def とこの shape が一致するため、bridge 補題は不要（CLAUDE.md「Mathlib-shape-driven」red flag 回避）。

**telescoping の構造的補助（cylinder の `Fin succ` 分解）**:

| 概念 | Mathlib API | file:line | 状態 | 備考 |
|---|---|---|---|---|
| `Fin succ` 積同型 | `MeasurableEquiv.piFinSuccAbove` | `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean` | ✅ 既存 | `(Fin (n+1) → α) ≃ᵐ α × (Fin n → α)` 系 |
| 同 measure 保存 | `MeasureTheory.measurePreserving_piFinSuccAbove` | `Mathlib/MeasureTheory/Constructions/Pi.lean` | ✅ 既存 | block 増分の射影に使える可能性 |

> 注: telescoping の「block n+1 = block n × 次記号」の構造は `condDistrib (obs n) (blockRV n) μ` で
> 直接表現するのが本筋（`piFinSuccAbove` は補助）。

---

## §4. 既存足場（Z-side、`LZ78ZivEntropyBridge.lean`）

| 概念 | API | file:line | 状態 | Phase での扱い |
|---|---|---|---|---|
| parsing 境界長 | `parsingBoundary` | `LZ78ZivEntropyBridge.lean:133` | ✅ 既存 def | telescoping index |
| prefix block prob | `prefixBlockProb` | `:141` | ✅ 既存 def | `= (μ.map (blockRV m)).real {blockRV m ω}` |
| per-phrase 条件付き | `condPhraseProb` | `:158` | ✅ 既存 def | `= prefixBlockProb(m+1)/prefixBlockProb(m)` ★ condDistrib ratio と shape 一致 |
| factorization hyp | `IsLZ78PerPathParsingFactorization` | `:179` | ⚠ honest hyp（`factor`+`pos`） | K3 でこの body を proving |
| 加法 log 形 | `blockProb_neg_log_eq_sum` | `:206` | ✅ genuine（`Real.log_prod`） | Z-a で reuse |
| log-sum 不等式 | `log_sum_inequality` | `:63` | ✅ genuine（Jensen） | Z-a で reuse |
| blockLogAvg 復元 | `blockLogAvg_eq_neg_log_blockProb` | `:117` | ✅ genuine | Z-b bridge |

**`IsLZ78PerPathParsingFactorization` body verbatim（K3 の target）**:

```lean
structure IsLZ78PerPathParsingFactorization
    (μ : Measure Ω) (p : StationaryProcess μ α) : Prop where
  factor : ∀ (n : ℕ) (ω : Ω),
    (μ.map (p.blockRV n)).real {p.blockRV n ω}
      = ∏ j ∈ Finset.range
            (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length,
          condPhraseProb μ p n ω j
  pos : ∀ (n : ℕ) (ω : Ω) (j : ℕ),
    j ∈ Finset.range (lz78PhraseStrings (List.ofFn (p.blockRV n ω))).length →
      0 < condPhraseProb μ p n ω j
```

**接続**: K2-a の `condDistrib` kernel から K2-b で `Pₙ{x} = ∏ⱼ qⱼ` を出し、`qⱼ` を `condPhraseProb`
の def（prefix block prob ratio）に照合して `factor` を rw。`pos` は出現 prefix（`μ.map X {x} ≠ 0`）で
`condDistrib_apply_of_ne_zero` の正値性。既存 def を一切変えずに body を満たせる（Mathlib-shape OK）。

---

## §5. 2 primitive structure body（Phase Z/C の target、verbatim）

```lean
-- LZ78AchievabilityLimsup.lean:102
structure IsLZ78AchievabilityZivUpperBound
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (slack : ℕ → ℝ) : Prop where
  upper : ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ)
        ≤ blockLogAvg μ p n ω + slack n
  slack_tendsto : Filter.Tendsto slack Filter.atTop (𝓝 (0 : ℝ))

-- LZ78ConverseKraft.lean:106
structure IsLZ78ConverseCodingLowerBound
    (μ : Measure Ω) (p : StationaryProcess μ α)
    (lz78EncodingLength : ∀ n, (Fin n → α) → ℕ)
    (slack : ℕ → ℝ) : Prop where
  lower : ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop,
      blockLogAvg μ p n ω - slack n
        ≤ (lz78EncodingLength n (p.blockRV n ω) : ℝ) / (n : ℝ)
  slack_tendsto : Filter.Tendsto slack Filter.atTop (𝓝 (0 : ℝ))
```

両 primitive とも honest（型 ≠ 結論、`slack` 付き per-realization eventual + `slack_tendsto`、
docstring が load-bearing 明示）。Phase Z/C はこれを満たす instance を `slack` 明示構成で返す。
assembly 補題は既に genuine:
- `isLZ78AchievabilityChainHyp_of_zivUpperBound` (`LZ78AchievabilityLimsup.lean:144`) — limsup plumbing
- `isLZ78ConverseChainHyp_of_codingLowerBound` (`LZ78ConverseKraft.lean:147`) — liminf plumbing
- distinct 版 `isLZ78AchievabilityChainHyp_distinct` (`:204`) / `isLZ78ConverseChainHyp_distinct` (`:207`)

---

## §6. converse 側（13.130）— averaged Kraft → Birkhoff a.s. lift

> **honesty 注記（計画準拠）**: pointwise Shannon-code 経路（`2^{-lz} ≤ Pₙ`）は LZ78 universality ゆえ
> per-path で偽（`LZ78ConverseKraft.lean:103-105`）。**採らない。** averaged Kraft → ergodic lift 一択。

| 概念 | API | file:line | 状態 | typeclass prereq |
|---|---|---|---|---|
| Gibbs/Kraft 下界（期待値版） | `entropyD_le_expectedLength_of_kraft` | `InformationTheory/Shannon/ShannonCode.lean:164` | ✅ genuine | 下記 verbatim |
| Shannon 語長 Kraft 充足 | `shannonLength_kraft_le_one` | `ShannonCode.lean:129` | ✅ genuine | `1 < D`, `IsProbabilityMeasure P`, full-support |
| `D^{-l} ≤ P(a)` | `rpow_neg_shannonLength_le_real` | `ShannonCode.lean:106` | ✅ genuine | `1 < D`, `0 < P.real {a}` |
| `kraftSum`/`expectedLength`/`entropyD` def | — | `:59`/`:55`/`:45` | ✅ 既存 def | — |
| Birkhoff 個別エルゴード定理 | `birkhoff_ergodic_ae` | `InformationTheory/Shannon/BirkhoffErgodic.lean:1031` | ✅ genuine | 下記 verbatim |
| SMB a.s. 収束 | `shannon_mcmillan_breiman` | `InformationTheory/Shannon/SMBAlgoetCover.lean:2840` | ✅ genuine | 下記 verbatim |

**signature verbatim**:

```lean
-- ShannonCode.lean:164  (namespace InformationTheory.Shannon.ShannonCode,
--   variable {α} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α])
theorem entropyD_le_expectedLength_of_kraft
    {D : ℝ} (hD : 1 < D) (P : Measure α) [IsProbabilityMeasure P]
    (hP : ∀ a : α, 0 < P.real {a})
    (l : α → ℕ) (h_kraft : kraftSum D l ≤ 1) :
    entropyD D P ≤ expectedLength P l

-- BirkhoffErgodic.lean:1031  結論形 verbatim:
theorem birkhoff_ergodic_ae {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) (hT_erg : Ergodic T μ)
    {f : Ω → ℝ} (hf : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverageReal T f n ω)
      atTop (𝓝 (∫ x, f x ∂μ))

-- SMBAlgoetCover.lean:2840  結論形 verbatim:
theorem shannon_mcmillan_breiman
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ErgodicProcess μ α) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun n => blockLogAvg μ p.toStationaryProcess n ω)
      Filter.atTop (𝓝 (entropyRate μ p.toStationaryProcess))
```

**機械確認済（§9-B）**: `entropyD_le_expectedLength_of_kraft` は generic な finite type 上の Measure に
適用でき、`Measure (Fin n → α)` 上でそのまま typecheck（block pushforward `Pₙ = μ.map (blockRV n)` に適用可）。

**接続（C-a → C-b）**: distinct LZ78 が block レベルで prefix-free（`lz78PhraseStrings_nodup`
`LZ78GreedyLongestPrefix.lean:126`）→ `kraftSum D l ≤ 1` を block code `l` で立てる →
`entropyD_le_expectedLength_of_kraft` で `entropyD Pₙ ≤ expectedLength Pₙ l`（期待値版）→
**`birkhoff_ergodic_ae`（観測 `-log condPhraseProb` 系を可積分関数として）** で per-realization
eventual `blockLogAvg n ω - slack n ≤ lz/n` に持ち上げ。full-support `0 < Pₙ.real {x}` は a.s.
出現 block で扱う（regularity 範疇）。

---

## §7. 主要前提条件ボックス（前提事故が起きやすい lemma）

- **disintegration `ρ.disintegrate ρ.condKernel` / `condKernel_apply_of_ne_zero`**:
  - `[IsFiniteMeasure ρ]` … block pushforward `μ.map (blockRV n)` は `[IsProbabilityMeasure μ]` から
    自動（`Measure.map` of probability = probability ⊆ finite）。**OK**。
  - `[StandardBorelSpace Ω] [Nonempty Ω]`（**第二因子**）… finite alphabet で無料（§1 機械確認）。**OK**。
  - `[MeasurableSingletonClass α]`（`condKernel_apply_of_ne_zero` の **第一因子**）… プロジェクト前提に
    あり。**OK**。
  - 一意性 `eq_condKernel_of_measure_eq_compProd` は `[IsFiniteKernel κ]` を要求。`condDistrib` は
    `IsMarkovKernel`（⊆ finite）なので OK。stationarity で kernel を同定するときに使う。

- **`condDistrib` (CondDistrib.lean:54 variable)**:
  - `[StandardBorelSpace Ω] [Nonempty Ω]`（観測値側 `Ω = α` or block）… finite で無料。**OK**。
  - `[IsFiniteMeasure μ]`（土台測度）… probability から自動。**OK**。
  - `compProd_map_condDistrib` は `(hY : AEMeasurable Y μ)` を要求 — `measurable_obs`/`measurable_blockRV`
    （`Stationary.lean:77,85`）から `.aemeasurable` で供給。**OK**。
  - `condDistrib_apply_of_ne_zero` は `(hY : Measurable Y)` + `[MeasurableSingletonClass β]`（履歴側）を
    要求 — 両方 OK。

- **`entropyD_le_expectedLength_of_kraft` (ShannonCode.lean:164)**:
  - `(hP : ∀ a, 0 < P.real {a})`（**full-support**）… block pushforward では全 block が出現するとは
    限らない → **a.s. 出現 block に制限**して扱う（regularity 範疇、honest）。これは「核心」ではなく
    「前提条件」（CLAUDE.md 判定: full-support は regularity hyp で OK）。
  - `(h_kraft : kraftSum D l ≤ 1)`（**prefix-free / Kraft**）… これは converse の **核心**。
    `lz78PhraseStrings_nodup` から block code の prefix-free 性を genuine に立てる必要（Phase C-a の作業）。

- **`birkhoff_ergodic_ae` (BirkhoffErgodic.lean:1031)**:
  - `[IsProbabilityMeasure μ]` + `(hT : MeasurePreserving)` + `(hT_erg : Ergodic)` … `ErgodicProcess`
    の field（`measurePreserving` / `ergodic`）から直接供給。**OK**。
  - `(hf : Integrable f μ)` … lift する観測 `f` の可積分性を別途示す必要（finite alphabet なので
    有界 → 可積分は容易、ただし `-log condPhraseProb` の可積分性は要確認）。

---

## §8. 自作が必要な要素（優先度順 — すべて "組み立て"、Mathlib 不在の壁ではない）

1. **kernel 層構造 `KernelStationaryProcess`（案 K1-β、別構造）** — Phase K1。
   `condDistrib` を field として持つ別構造 or instance。`StationaryProcess` 不変。**~50–80 行**。
   落とし穴: `condPhraseProb` の既存 def（prefix block prob ratio）と field の結論形を
   `condDistrib_apply_of_ne_zero` shape で一致させる（噛み合わなければ L-K1 で typeclass 案に切替）。

2. **`kernelStationaryProcess_of_ergodic`（ergodic + finite → 実例構成、★crux）** — Phase K2-a。
   `condDistrib (obs m) (blockRV m) μ` で kernel を construct し、**stationarity
   (`identDistrib_obs_zero` `Stationary.lean:94`) で shift-invariant に固定**。
   `eq_condKernel_of_measure_eq_compProd`（一意性）で process の条件付き法則 = condDistrib を同定。
   **~150–250 行**。落とし穴: stationarity を「kernel の shift 不変性」に翻訳する補題が要る
   （Mathlib 直補題なし → identDistrib + condDistrib_congr で組む）。**ここが L-K 判定点だが、
   素材（condDistrib + 一意性 + identDistrib）はすべて揃っており、壁ではなく組み立て。**

3. **`blockProb_eq_prod_telescope`（telescoping factorization）** — Phase K2-b。
   `compProd_apply_prod` + `condDistrib_apply_of_ne_zero` を逐次適用し `Pₙ{x} = ∏ⱼ qⱼ`。
   singleton `{x}` を prefix 一致 cylinder の交わりで分解。zero-mass edge（未出現 prefix で `qⱼ = 0`、
   `log 0 = 0` 規約）+ `n = 0` edge を special-case。**~100–150 行**。

4. **slack の明示構成 + `slack_tendsto`（Z-b / C-b）** — Phase Z/C。
   counting envelope（`LZ78ZivCountingBody.lean:405`、`c = O(n/log n)`）+ bitLength overhead から
   slack を構成、Tendsto を genuine に。**各 ~50–100 行**。

5. **block prefix-free → Kraft 充足（C-a）** — Phase C。
   `lz78PhraseStrings_nodup`（`LZ78GreedyLongestPrefix.lean:126`）の延長で block code の `kraftSum ≤ 1`。
   **~80–120 行**。落とし穴: phrase レベル単射 → block レベル prefix-free の翻訳。

> **「自作 = 組み立て」の結論**: 上記 5 件はいずれも **Mathlib に素材が揃った組み立て** であり、
> Phase 4 KL inventory の DPI（Mathlib に DPI 補題が皆無で完全自作）とは異なり、
> 「不在の壁」ではない。

---

## §9. 機械確認ログ（`lake env lean` で検証した scratch、すべて silent = clean）

**A. StandardBorelSpace 自動 derive + disintegration（最重要）** — silent:
```lean
example : StandardBorelSpace α := by infer_instance                       -- ✅
example (n : ℕ) : StandardBorelSpace (Fin n → α) := by infer_instance     -- ✅
example (n : ℕ) : Nonempty (Fin n → α) := by infer_instance              -- ✅
example {β} [MeasurableSpace β] (ρ : Measure (β × (Fin 3 → α))) [IsFiniteMeasure ρ] :
    ρ.fst ⊗ₘ ρ.condKernel = ρ := ρ.disintegrate ρ.condKernel            -- ✅
```
（`α`: `[Fintype][DecidableEq][Nonempty][MeasurableSpace][MeasurableSingletonClass]`）

**B. Kraft 下界が `Fin n → α` measure に適用可** — silent:
```lean
example (n : ℕ) {D : ℝ} (hD : 1 < D) (P : Measure (Fin n → α)) [IsProbabilityMeasure P]
    (hP : ∀ a, 0 < P.real {a}) (l : (Fin n → α) → ℕ) (hk : kraftSum D l ≤ 1) :
    entropyD D P ≤ expectedLength P l :=
  entropyD_le_expectedLength_of_kraft hD P hP l hk                        -- ✅
```

**C. condDistrib disintegration + ratio が block 設定で typecheck** — silent:
```lean
example (μ : Measure Ω) [IsFiniteMeasure μ] (n : ℕ) (X : Ω → (Fin n → α)) (Y : Ω → α)
    (hY : AEMeasurable Y μ) :
    (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map (fun a => (X a, Y a)) :=
  compProd_map_condDistrib hY                                             -- ✅
example (μ : Measure Ω) [IsFiniteMeasure μ] (n : ℕ) (X : Ω → (Fin n → α)) (Y : Ω → α)
    (hY : Measurable Y) (x : Fin n → α) (hX : μ.map X {x} ≠ 0) (s : Set α) :
    condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s) :=
  condDistrib_apply_of_ne_zero hY x hX s                                  -- ✅
```

---

## §10. blast radius 再確認（計画 §blast radius の裏取り）

`rg` 全数確認（InformationTheory 全体）:
- `StationaryProcess.mk` / `ErgodicProcess.mk` / anonymous constructor / 全 field 供給サイト: **ゼロ**。
- 唯一のヒット `InformationTheory/Probability/TwoSidedExtension.lean:959`
  （`set q : StationaryProcess μ α := p.toStationaryProcess`）は **別名束縛**で構築ではない。
  **※ 計画は `InformationTheory/Shannon/TwoSidedExtension.lean` と記すが、実体は `InformationTheory/Probability/`
  配下**（計画のパス誤記、blast radius 結論は不変）。
- `where` のヒット（`Stationary.lean:45,115`、`LZ78ZivEntropyBridge.lean:180`）は構造**定義**で
  あって構築ではない。

**判定**: refactor は additive で Ch.4 非破壊。新規 `StationaryKernel.lean` 1 file 隔離 + 既存 file
末尾追記で blast radius が閉じる。`StationaryProcess` 定義はバイト単位で不変可能（案 K1-β）。

---

## §11. GO / NO-GO VERDICT（最重要）

| 判定軸 | 結論 | 根拠 |
|---|---|---|
| **(K2-a) finite α で StandardBorelSpace 自動 + ergodic→kernel 同定** | **GO（揃う + 一部組み立て要）** | StandardBorelSpace 自動 derive は §9-A 機械確認で完全クリア。kernel 同定は `condDistrib` + `eq_condKernel_of_measure_eq_compProd` + `identDistrib_obs_zero` の素材が揃う。**自作要 = stationarity → kernel shift 不変性の翻訳補題（組み立て、~150–250 行）** |
| **(Z) factorization `Pₙ=∏qⱼ` が disintegration で出るか** | **GO** | `compProd_apply_prod` + `condDistrib_apply_of_ne_zero`（§9-C 機械確認）の逐次適用で telescoping。既存 `condPhraseProb` def と shape 一致（bridge 不要）。自作要 = telescoping 集合分解 + zero-mass edge（~100–150 行） |
| **(C) averaged Kraft → Birkhoff a.s. lift** | **GO** | `entropyD_le_expectedLength_of_kraft`（§9-B 機械確認、block measure 適用可）+ `birkhoff_ergodic_ae` + `shannon_mcmillan_breiman` が揃う。自作要 = block prefix-free → Kraft（~80–120 行）+ ergodic lift の観測選択 + slack（~150–250 行） |

**総合 VERDICT: GO。** Phase 0 で最も恐れていた「`[StandardBorelSpace (Fin n → α)]` が自動 derive
されず disintegration が使えない」シナリオは **機械確認で否定**された。kernel 層は Mathlib の
`condDistrib` で genuine に構成でき、process 側 forward conditional として `condPhraseProb` の
ratio def と shape 一致する。**Mathlib 不在の壁は無く、残るのは組み立て負荷のみ。**

**撤退ライン L-K（kernel 構成が不能/過大）への距離 = 発動しない見込み（条件付き）**:
- L-K の主要発動条件①「`[StandardBorelSpace]` 自動 derive で詰まる」… **クリア（§9-A）**。
- L-K の発動条件②「ergodic→kernel が >400 行 / disintegration 一意性で詰まる」… 素材は揃うので
  詰まりにくいが、**stationarity → kernel shift 不変性の翻訳が読めない場合のみ残リスク**。
  この 1 点が >400 行に膨らんだ場合のみ L-K（`IsLZ78PerPathParsingFactorization` を isolated honest
  hyp に留める）。現状の評価では **発動しない**。
- 万一発動しても、achievability 側（Z）は factorization hyp を受けて残り genuine、converse 側（C）は
  独立に genuine 化可能（共有 crux なし）。honest hyp 2→1 の前進は確保される。

**推定規模**: 計画の規模見積（累計 ~820 行 / 520–1480）と整合。本在庫の精緻化で **K2-a の最大リスク
（StandardBorel）が消えた**ため、中央値寄り（~820 行）の着地確度が上がった。

---

## §12. Phase K1 着手 skeleton（`InformationTheory/Shannon/StationaryKernel.lean`）

```lean
import InformationTheory.Shannon.ShannonMcMillanBreiman
import InformationTheory.Shannon.LZ78ZivEntropyBridge
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Stationary-process kernel layer (LZ78 blockRV refactor, Phase K1–K3)

Additive kernel structure for `StationaryProcess` (it is left byte-for-byte
unchanged). The transition kernel is built from Mathlib's `condDistrib`
(forward conditional law of the next symbol given the block history), whose
`condDistrib_apply_of_ne_zero` ratio form matches `condPhraseProb`. Finite
alphabet makes `StandardBorelSpace (Fin n → α)` automatic, so the
disintegration machinery applies with no extra hypotheses.
-/

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

variable {α Ω : Type*}
variable [Fintype α] [DecidableEq α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace Ω]

/-- Kernel layer over a stationary process (案 K1-β, 別構造). Carries the
forward transition kernel (block history → next symbol) as a `condDistrib`,
plus a stationarity-compatibility field. `StationaryProcess` is unchanged. -/
structure KernelStationaryProcess (μ : Measure Ω) (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] where
  toStationaryProcess : StationaryProcess μ α
  -- transition kernel field + compatibility field (Phase K1 で確定):
  --   transKernel : ∀ m, Kernel (Fin m → α) α
  --   compatible  : ∀ m, (μ.map (toStationaryProcess.blockRV m)) ⊗ₘ transKernel m
  --                        = μ.map (fun ω => (blockRV m ω, obs m ω))

/-- ★crux (Phase K2-a): construct the kernel layer from ergodic + finite
alphabet ALONE, via `condDistrib` + stationarity (`identDistrib_obs_zero`)
+ disintegration uniqueness. L-K judgment point. -/
noncomputable def kernelStationaryProcess_of_ergodic
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    KernelStationaryProcess μ α := by sorry

/-- Phase K2-b: telescoping factorization `Pₙ{x} = ∏ⱼ qⱼ` from the kernel
layer, via `compProd_apply_prod` + `condDistrib_apply_of_ne_zero`. -/
theorem blockProb_eq_prod_telescope
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α)
    (n : ℕ) (ω : Ω) :
    (μ.map (p.toStationaryProcess.blockRV n)).real {p.toStationaryProcess.blockRV n ω}
      = ∏ j ∈ Finset.range
          (lz78PhraseStrings (List.ofFn (p.toStationaryProcess.blockRV n ω))).length,
        condPhraseProb μ p.toStationaryProcess n ω j := by sorry

/-- Phase K3: supply the existing honest hypothesis from the kernel layer. -/
theorem isLZ78PerPathParsingFactorization_of_kernel
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ErgodicProcess μ α) :
    IsLZ78PerPathParsingFactorization μ p.toStationaryProcess := by sorry

end InformationTheory.Shannon
```

> 注: 上の skeleton は K1 設計の **第一候補（案 K1-β）** の形。`KernelStationaryProcess` の field
> 確定（`transKernel`/`compatible` の正確な型）は Phase K1 で `condDistrib_apply_of_ne_zero` の
> 結論形に合わせて固定する（Mathlib-shape-driven）。`condPhraseProb` の既存 def と噛み合わなければ
> L-K1 で typeclass 案（K1-α）に切替。
