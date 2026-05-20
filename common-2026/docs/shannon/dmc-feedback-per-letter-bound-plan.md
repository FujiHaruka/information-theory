# DMC feedback per-letter bound (E-10') ムーンショット計画 🌙

E-10' は親 plan [`dmc-feedback-capacity-plan.md`](./dmc-feedback-capacity-plan.md) の "後継 deferred" 段。Cover-Thomas Thm 7.12 の "memoryless ⇒ per-letter inequality":

```
I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)
```

を **memoryless 性 + 因果性のみ**から導く純粋証明。これが 0 sorry で publish できれば、E-10 主定理 `channel_coding_feedback_converse` の `h_per_letter` 仮定が剥がれ、Cover-Thomas 7.12 が完全形で完走する。

## 進捗

- [x] Phase 0 — Mathlib API inventory ✅ (2026-05-13 起草時点で完了)
- [x] Phase A — `IsMemorylessFeedback` 述語 ✅ (2026-05-14、RV 順を chain rule conclusion 形に合わせて `(Y^{<i}, Msg)` 採用)
- [x] Phase B — CondMutualInfo.lean 拡張 ✅ (新規補題 0 行、既存資産で十分の見立て通り)
- [x] Phase C — `feedback_per_letter_bound` ✅ (2026-05-14、`mutualInfo_le_of_markov` 1 段 + chain rule + nonneg で完走)
- [x] Phase D — `channel_coding_feedback_converse_memoryless` ✅ (2026-05-14、既存 E-10 主定理に `h_per_letter` を construct して結論)

> 実態整合 (2026-05-20): DONE-HONEST-HYPS — `feedback_per_letter_bound` (`Common2026/Shannon/ChannelCodingFeedbackComplete.lean:116`、0 sorry) は `h_memo : IsMemorylessFeedback μ Msg Xs Ys` (γ-form Markov chain 述語、pass-through Prop でない) から per-letter 不等式を派生。主定理 `channel_coding_feedback_converse_memoryless` (`:171`) が E-10 主定理に `h_per_letter` を construct して完全形を結論。

**完了サマリ (2026-05-14)**: `Common2026/Shannon/ChannelCodingFeedbackComplete.lean` (198 行、4 declarations、0 sorry / 0 warning)。Plan 見積 280-400 行を ~50% 削減。Phase A の RV 順を `(Y^{<i}, Msg)` (chain rule LHS の `(Zc, Xs)` と一致) に揃えたことで Step 3 swap が 0 行に。CondMutualInfo.lean 新規補題 0 行 (既存 `IsMarkovChain` + `mutualInfo_le_of_markov` + `mutualInfo_chain_rule` + `mutualInfo_nonneg` のみ)。Cover-Thomas 7.12 が `h_per_letter` 仮説を剥がした完全形で完走。

## ゴール / Approach

**ゴール**: 親 plan `channel_coding_feedback_converse` の `h_per_letter` 仮定を **memoryless 性** + **因果性** から導出して剥がす。具体補題:

```
feedback_per_letter_bound :
  ∀ i : Fin n,
    Shannon.condMutualInfo μ Msg (Ys i)
        (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
      ≤ Shannon.mutualInfo μ (Xs i) (Ys i)
```

### Approach (3 段戦略)

memoryless 性は **`Y_i ⊥ (Msg, Y^{<i}) | X_i`** ⇔ "Y_i は X_i にのみ依存し (Msg, Y^{<i}) には依存しない" を意味する。これを **3 変数 Markov chain `(Msg, Y^{<i}) → X_i → Y_i`** に reformulate し、既存 `mutualInfo_le_of_markov` (`CondMutualInfo.lean:378`):

```
Markov chain `Xs → Zc → Yo` ⇒ I(Xs; Yo) ≤ I(Zc; Yo)
```

を `Xs := (Msg, Y^{<i})`、`Zc := X_i`、`Yo := Y_i` で **そのまま流用** すれば

```
I((Msg, Y^{<i}); Y_i) ≤ I(X_i; Y_i)    ... (★1)
```

が即出る。

**Step 2** (左辺の reduction): `I((Msg, Y^{<i}); Y_i) ≥ I(Msg; Y_i | Y^{<i})` を chain rule で示す:

```
I((Y^{<i}, Msg); Y_i) = I(Y^{<i}; Y_i) + I(Msg; Y_i | Y^{<i})  -- mutualInfo_chain_rule
                     ≥ I(Msg; Y_i | Y^{<i})                     -- I(Y^{<i}; Y_i) ≥ 0
```

**Step 3** (合成): Step 1 + Step 2 で `I(Msg; Y_i | Y^{<i}) ≤ I(X_i; Y_i)`。左 RV の順序合わせは `mutualInfo_map_left_measurableEquiv` (`MIChainRule.lean`) で。

### 規模見積

- **Phase 0**: 0 行 (調査のみ)
- **Phase A**: `IsMemorylessFeedback` 述語 + accessor lemma ~80-120 行
- **Phase B**: 0 行目標 (既存資産で十分の想定)
- **Phase C**: per-letter bound 本体 ~150-200 行
- **Phase D**: 主定理 `channel_coding_feedback_converse_memoryless` ~50-80 行
- 合計 **~280-400 行**、新規ファイル 1 つ (`Common2026/Shannon/ChannelCodingFeedbackComplete.lean`) または既存 `ChannelCodingFeedback.lean` に追記

### MVP scope と scope-deferred

**MVP scope (本 plan)**:
1. memoryless 性の formal 定式化 (`IsMemorylessFeedback` = 各 i で Markov chain)
2. `feedback_per_letter_bound` の 0 sorry 証明
3. 親 plan E-10 主定理を memoryless 仮定下で `h_per_letter` 抜き完全形に

**scope-deferred**:
1. **DMC capacity の存在** (`∃ p, mutualInfoOfChannel p W = C`): 本 plan では `C : ℝ≥0∞` を引数で受ける
2. **memoryless ⇒ 入力分布非依存の capacity 達成可能性** (feedback achievability)

## Phase 0 — Mathlib API inventory

### Mathlib API verbatim signature 記録

1. **`condDistrib`** (`Mathlib/Probability/Kernel/CondDistrib.lean:64`)
   ```
   noncomputable def condDistrib (Y : α → β) (X : α → γ) (μ : Measure α)
       [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] : Kernel γ β
   ```

2. **`compProd_map_condDistrib`** (`Mathlib/Probability/Kernel/CondDistrib.lean:82`)
   ```
   lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) :
       (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)
   ```

3. **`condDistrib_ae_eq_of_measure_eq_compProd`** (`Mathlib/Probability/Kernel/CondDistrib.lean:163`)
   ```
   lemma condDistrib_ae_eq_of_measure_eq_compProd
       (X : α → β) (hY : AEMeasurable Y μ) {κ : Kernel β Ω} [IsFiniteKernel κ]
       (hκ : μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ) :
       condDistrib Y X μ =ᵐ[μ.map X] κ
   ```

4. **`condDistrib_ae_eq_iff_measure_eq_compProd`** (`Mathlib/Probability/Kernel/CondDistrib.lean:177`)
   ```
   lemma condDistrib_ae_eq_iff_measure_eq_compProd
       (X : α → β) (hY : AEMeasurable Y μ) {κ : Kernel β Ω} [IsFiniteKernel κ] :
       (condDistrib Y X μ =ᵐ[μ.map X] κ) ↔ μ.map (fun x => (X x, Y x)) = μ.map X ⊗ₘ κ
   ```

5. **`Kernel.prodMkRight_apply`** (`Mathlib/Probability/Kernel/Composition/MapComap.lean:249`)
   ```
   @[simp] theorem prodMkRight_apply (κ : Kernel α β) (ca : α × γ) :
       prodMkRight γ κ ca = κ ca.fst := rfl
   ```

### 既存 Common2026 補題

1. **`Shannon.mutualInfo_chain_rule`** (`Common2026/Shannon/CondMutualInfo.lean:219`)
   ```
   theorem mutualInfo_chain_rule
       (μ : Measure Ω) [IsProbabilityMeasure μ]
       [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
       (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
       (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) :
       mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo
         = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc
   ```

2. **`Shannon.IsMarkovChain`** (`Common2026/Shannon/CondMutualInfo.lean:71`)
   ```
   def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ]
       [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
       (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop :=
     μ.map (fun ω => (Zc ω, Xs ω, Yo ω))
       = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))
   ```

3. **`Shannon.mutualInfo_le_of_markov`** (`Common2026/Shannon/CondMutualInfo.lean:378`)
   ```
   theorem mutualInfo_le_of_markov
       (μ : Measure Ω) [IsProbabilityMeasure μ]
       [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
       (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
       (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
       (hmarkov : IsMarkovChain μ Xs Zc Yo) :
       mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo
   ```

4. **`Shannon.mutualInfo_nonneg`** (`Common2026/Shannon/MutualInfo.lean:42`)
   - `0 ≤ mutualInfo μ Xs Yo`。Step 2 で使用。

5. **`Shannon.mutualInfo_map_left_measurableEquiv`** (`Common2026/Shannon/MIChainRule.lean:43`)
   - 左 RV を MeasurableEquiv で書き換える。Step 3 で `(Msg, Y^{<i})` ↔ `(Y^{<i}, Msg)` swap に使う可能性。

### Mathlib 不在 (本 plan で自作)

- **`IsMemorylessFeedback` 述語**: 「各 i で `IsMarkovChain μ (Msg, Y^{<i}) (Xs i) (Ys i)`」を表す。Phase A で自作 (~30 行)。

## Phase A — memoryless 性の formal 定式化

### 採用形

```lean
/-- memoryless DMC + causal feedback encoder の formal 表現:
  各時刻 i で、出力 Y_i は X_i にのみ依存し、(Msg, Y^{<i}) には依存しない。
  γ-form Markov chain `(Msg, Y^{<i}) → X_i → Y_i` で記述。 -/
def IsMemorylessFeedback
    {n : ℕ} (μ : Measure Ω)
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β) : Prop :=
  ∀ i : Fin n,
    IsMarkovChain μ
      (fun ω => (Msg ω, fun (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω))
      (Xs i) (Ys i)
```

### 因果性

`FeedbackCode` 構造の型レベルで既に enforced (`encoder i : Fin M → (Fin i.val → β) → α`)。追加の因果性 hypothesis は **不要**。

### Phase A — checklist

- [ ] (A.1) `IsMemorylessFeedback` def を `Common2026/Shannon/ChannelCodingFeedbackComplete.lean` 新規 file (または `ChannelCodingFeedback.lean` 追記) で導入
- [ ] (A.2) 各 i での `IsMarkovChain` を取り出す accessor lemma (5 行)

## Phase B — CondMutualInfo.lean 補助補題

調査結果: **既存 `mutualInfo_chain_rule` + `mutualInfo_le_of_markov` + `mutualInfo_nonneg` で必要十分**。Phase B は **0 行を目標**。

### Phase C 着手後の確認事項

- Phase C で local 証明が ~30 行を超えたら、`condMutualInfo_le_mutualInfo_pair`: `I(X; Y | Z) ≤ I((Z, X); Y)` を CondMutualInfo.lean に切り出し

## Phase C — per-letter bound 本体

### スコープ

```lean
theorem feedback_per_letter_bound
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hMsg : Measurable Msg)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_memo : IsMemorylessFeedback μ Msg Xs Ys) :
    ∀ i : Fin n,
      condMutualInfo μ Msg (Ys i)
          (fun ω (j : Fin i.val) => Ys ⟨j.val, j.isLt.trans i.isLt⟩ ω)
        ≤ mutualInfo μ (Xs i) (Ys i)
```

### 戦略 (Step 1-3)

i を fix、`L : Ω → M × (Fin i.val → β)` を `L ω := (Msg ω, fun j => Ys ⟨j.val, ..⟩ ω)`。

**Step 1**: `h_memo i : IsMarkovChain μ L (Xs i) (Ys i)` から `mutualInfo_le_of_markov`:
```
mutualInfo μ L (Ys i) ≤ mutualInfo μ (Xs i) (Ys i)    ... (★1)
```

**Step 2**: `mutualInfo_chain_rule` を `Xs := Msg, Yo := Ys i, Zc := Y^{<i}` で適用:
```
mutualInfo μ (fun ω => (Y^{<i} ω, Msg ω)) (Ys i)
  = mutualInfo μ (Y^{<i}) (Ys i) + condMutualInfo μ Msg (Ys i) (Y^{<i})
```
+ `mutualInfo_nonneg`:
```
condMutualInfo μ Msg (Ys i) (Y^{<i})
  ≤ mutualInfo μ (fun ω => (Y^{<i} ω, Msg ω)) (Ys i)    ... (★2)
```

**Step 3**: L = `(Msg, Y^{<i})` vs chain rule LHS `(Y^{<i}, Msg)` の swap (MeasurableEquiv 経由)。**または** Phase A 定式化を `(Y^{<i}, Msg)` 順に揃えれば 0 行。

合成: (★1) + (★2) + Step 3 swap で結論。

### Phase C — checklist

- [ ] (C.1) accessor: `h_memo i` から `IsMarkovChain` 取出し (5 行)
- [ ] (C.2) Step 1: `mutualInfo_le_of_markov` 直接適用 (~10 行)
- [ ] (C.3) Step 2: chain rule + `mutualInfo_nonneg` + `le_add_left` (~15 行)
- [ ] (C.4) Step 3: 左 RV swap 解消 (`mutualInfo_map_left_measurableEquiv` または Phase A 順序合わせ) (~15 行)
- [ ] (C.5) type class plumbing: `StandardBorelSpace (M × (Fin i.val → β))` 自動 derive 確認

## Phase D — 主定理 `channel_coding_feedback_converse_memoryless`

### スコープ

```lean
theorem channel_coding_feedback_converse_memoryless
    {n : ℕ} (C : ℝ≥0∞) (hC_finite : C ≠ ∞)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (h_memo : IsMemorylessFeedback μ Msg Xs Ys)
    (h_capacity : ∀ i : Fin n, Shannon.mutualInfo μ (Xs i) (Ys i) ≤ C)
    (hMsg_uniform :
      μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M) :
    Real.log (Fintype.card M) ≤
      (n : ℝ) * C.toReal +
        Real.binEntropy (MeasureFano.errorProb μ Msg (fun ω i => Ys i ω) decoder) +
        MeasureFano.errorProb μ Msg (fun ω i => Ys i ω) decoder *
          Real.log ((Fintype.card M : ℝ) - 1)
```

### 戦略

1. `feedback_per_letter_bound` を直接適用して `h_per_letter` を construct
2. 既存 `channel_coding_feedback_converse` (E-10 plan) に渡して結論

## 判断ログ

1. **memoryless 性の formal 化を `IsMarkovChain` 直接形に採用** (Phase A): kernel W への参照を持たない `IsMarkovChain` (γ-form) 形を採用。kernel 固定性は per-letter bound 自体には不要 (capacity bound 段で消費)。
2. **per-letter bound の証明経路を Markov reformulation 経由に統一** (Phase C): condEntropy 展開経路 (~300 行追加) を **却下**、既存 `mutualInfo_le_of_markov` 1 段 + chain rule + nonneg で完走 (新規補題 0 行)。
3. **W への参照を主定理から外す** (Phase D): `C : ℝ≥0∞` 引数形で抽象化、E-10 主定理と整合。

## 参考

- 親 plan: [`dmc-feedback-capacity-plan.md`](./dmc-feedback-capacity-plan.md)
- 兄弟 plan: [`channel-coding-converse-general-plan.md`](./channel-coding-converse-general-plan.md) — D-2 で同型の deferred bullet。本 plan の成果は D-2' でも転用可能
- moonshot template: [`docs/moonshot-plan-template.md`](../moonshot-plan-template.md)
