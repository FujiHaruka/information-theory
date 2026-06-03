# Channel coding converse — pure `IsMemorylessChannel` form via Strong wrapper (D-2'' γ-chain bridge) サブ計画

> **Parent**: [`channel-coding-converse-d2-doubleprime-plan.md`](./channel-coding-converse-d2-doubleprime-plan.md) (deferred), [`channel-coding-converse-general-d2-prime-plan.md`](./channel-coding-converse-general-d2-prime-plan.md)

## 進捗

- [x] Phase 0 — Mathlib / InformationTheory 在庫確認 (graphoid weak union / marginalize 経路) ✅
- [x] Phase A — bridge 補題 (`per_letter_markov_of_memoryless` + `outputs_cond_indep_of_memoryless`) ✅
- [x] Phase B — pure 主定理 `channel_coding_converse_general_memoryless_pure` ✅
- [x] Phase C — `InformationTheory.lean` import 追記 + smoke 検証 ✅

> 実態整合 (2026-05-20): DONE-HONEST-HYPS — 本サブ計画は完了済 (進捗マーカーが起草時の `[ ]` のまま stale だった)。証拠: `channel_coding_converse_general_memoryless_pure` (`InformationTheory/Shannon/ChannelCodingConverseMemorylessPure.lean:650`、0 sorry) は `h_memo : IsMemorylessChannel` のみを取り (pass-through Prop 仮説なし)、内部で `IsMemorylessChannelStrong` を bridge 補題 2 本で派生して `_strong` wrapper を呼ぶ。bridge `outputs_cond_indep_of_memoryless` (`:567`) は graphoid weak union (`isMarkovChain_weakUnion_left_to_conditioner`) + measurableEquiv reshape で実証 (vacuous でない)。`InformationTheory.lean:55` に import 済。これにより親 D-2'' の "deferred" を解消。

## 背景

D-2' (`ChannelCodingConverseGeneralComplete.lean`、578 行) は 3 仮説 (`h_yother_zero` / `h_split` / `h_markov_xprefix`) を Phase C 仮説として受け取る形で publish 済。
D-2'' (deferred) は `IsMemorylessChannel` (γ-form 単一 Markov chain `(X^{≠i}, Y^{≠i}) → X_i → Y_i`) からこれら 3 仮説を全て派生する純粋形を狙っていたが、

> `h_yother_zero` = `condMI(X_i; Y^{≠i} | (X^{<i}, Y_i)) = 0`
> は encoder 任意 (e.g. `X_1 := X_0` degenerate) では **数学的に偽**

と判明 (`ChannelCodingConverseGeneralStrong.lean:229-239` の architectural note 参照)。
そこで Strong 経路 (`ChannelCodingConverseGeneralStrong.lean`、Cover-Thomas Thm 7.9 のエントロピー劣加法による encoder-agnostic 経路) に切り替え、`channel_coding_converse_general_memoryless_strong` (272-321 行) を publish。これは

- `_h_memo : IsMemorylessChannel ...` (unused、historical compat のみ)
- `h_strong : IsMemorylessChannelStrong ...` (実体、2 つの Markov axiom)

の 2 つを受け取る。

**本サブ計画の射程**: `IsMemorylessChannel` **単独** で `IsMemorylessChannelStrong` を構成する bridge 補題を書き、それを介して既存 `_strong` の薄い wrapper として `channel_coding_converse_general_memoryless_pure` を publish する。`h_yother_zero` 由来の deferred は経路として bypass される (encoder-agnostic な Strong 経路を通すので encoder degenerate 反例にも頑健)。

## ゴール / Approach

### ゴール (主定理 signature)

```lean
theorem channel_coding_converse_general_memoryless_pure
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : Shannon.IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (h_memo : IsMemorylessChannel μ (fun i ω => encoder (Msg ω) i) Ys)
    (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : Shannon.mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (∑ i : Fin n, (Shannon.mutualInfo μ
        (fun ω => encoder (Msg ω) i) (Ys i)).toReal)
      + Real.binEntropy (errorProb ...)
      + errorProb ... * Real.log (Fintype.card M - 1)
```

D-2' / D-2'' 系の signature と一致、`h_strong` 仮説を消去した形。

### Approach (2 段戦略)

**Step 1 — Strong 化 bridge**: `IsMemorylessChannel` の γ-form Markov chain

```
(X^{≠i}, Y^{≠i}) → X_i → Y_i   ・・・(★)
```

から、`IsMemorylessChannelStrong` の 2 axiom を構成する。

- **A.1 `per_letter_markov_of_memoryless`**: `X^n → X_i → Y_i` を導く。
  (★) は `(X^{≠i}, Y^{≠i})` の左 RV、これを **graphoid marginalization** で `Y^{≠i}` を落として `X^{≠i} → X_i → Y_i` に縮める。次に `X^n = (X^{≠i}, X_i)` を `MeasurableEquiv` で bundle (γ-form の left は post-process 可)。
  実装上: 既存 `Shannon.isMarkovChain_map_left` (CondMutualInfo.lean:652) で post-process。
  marginalize 補題は **graphoid axiom そのものを γ-form `IsMarkovChain` 上で打つ必要がある**: 補題 `isMarkovChain_drop_right_in_left` (左 RV が pair `(A, B)` のときに `B` を落として左を `A` 単独にする) を新規追加。

- **A.2 `outputs_cond_indep_of_memoryless`**: `Y^{≠i} → X^n → Y_i` を導く。
  (★) を **graphoid weak union** で経路替え:
  ```
  Y_i ⊥ (X^{≠i}, Y^{≠i}) | X_i      -- (★) γ-form を symm
    ⟹ Y_i ⊥ Y^{≠i} | (X_i, X^{≠i})  -- weak union
    = Y_i ⊥ Y^{≠i} | X^n             -- bundle X^n
  ```
  これも γ-form `IsMarkovChain` 上の構造変換補題 `isMarkovChain_weakUnion_middle` (中央 RV に左 RV の一部を吸わせる) として新規。

**Step 2 — wrapper**: 既存 `channel_coding_converse_general_memoryless_strong` (`ChannelCodingConverseGeneralStrong.lean:272-321`) を A.1 + A.2 で構成した `IsMemorylessChannelStrong` 値で呼ぶ。本体 20-40 行。

### 配置

新規ファイル `InformationTheory/Shannon/ChannelCodingConverseMemorylessPure.lean` を推奨。

- 既存 `ChannelCodingConverseGeneralStrong.lean` および `ChannelCodingConverseGeneralComplete.lean` を touch しない方針 (signature 互換性 + olean 連鎖を温存)。
- `import InformationTheory.Shannon.ChannelCodingConverseGeneralStrong` 1 行のみ追加。
- bridge 補題 A.1 / A.2 は同ファイル内 (file-scoped `private` 可)、必要に応じて補助 `MeasurableEquiv` 構成も同居。

### 規模見積

| Phase | 内容 | 行数 |
|---|---|---|
| 0 | inventory | 0 |
| A | bridge `isMemorylessChannelStrong_of_isMemorylessChannel` + 内部 graphoid 補題 2 本 | 200-350 |
| B | pure 主定理 wrapper | 20-40 |
| C | `InformationTheory.lean` import 追記 + lake env lean smoke | 5 |
| **合計** | | **~230-400 行** |

**proof-log: yes** (graphoid 経路の構造変換が泥沼化リスク中、Phase A の plumbing 詳細を残す価値あり)。

## Phase 0 — Mathlib / InformationTheory 在庫確認

### 既存 InformationTheory API (再利用)

1. `Shannon.IsMarkovChain` (`CondMutualInfo.lean:71-76`) — γ-form 定義。
2. `Shannon.isMarkovChain_map_left` (`CondMutualInfo.lean:652-661`) — 左 RV の measurable 関数による post-processing。signature:
   ```
   ∀ (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (hXs hZc hYo : Measurable _)
       {f : X → X'} (hf : Measurable f)
       (hmarkov : IsMarkovChain μ Xs Zc Yo),
     IsMarkovChain μ (fun ω => f (Xs ω)) Zc Yo
   ```
3. `Shannon.IsMemorylessChannel` (`ChannelCodingConverseGeneralComplete.lean:92-99`) — `(X^{≠i}, Y^{≠i}) → X_i → Y_i`、`Subtype {j // j ≠ i}` 経由。
4. `IsMemorylessChannelStrong` (`ChannelCodingConverseGeneralStrong.lean:64-74`) — 2 axiom (per_letter_markov + outputs_cond_indep)、target 構造。
5. `channel_coding_converse_general_memoryless_strong` (`ChannelCodingConverseGeneralStrong.lean:272-321`) — wrapper の呼び出し先。
6. `Shannon.measurableEquivExtract` (`ChannelCodingConverseGeneralStrong.lean:90-96`) — `(Fin n → β) ≃ᵐ β × ({j // j ≠ i} → β)` reshape。Phase A での bundle に再利用可。
7. **(CondEntropyMemoryless.lean 内 private)** `isMarkovChain_swap` (line 316) — X↔Y endpoint swap、`isMarkovChain_map_right` (line 353) — 右 RV post-processing。Phase A の symm + post-process に再利用可だが **private** 表記、`ChannelCodingConverseMemorylessPure.lean` から見えないため再宣言が必要。

### Mathlib API 候補 (graphoid / marginalize / weak union)

- **不在予想**: `condIndepFun` レベルの "weak union" / "decomposition" / "contraction" axiom は Mathlib に存在しない (graphoid axiom は **probabilistic graphical models** ライブラリ非存在、`Mathlib/Probability/Independence/Conditional.lean` には `condIndepFun_iff_*` と `condIndepFun.symm` (symmetry axiom) のみ)。**要 loogle 確認**。
- **再利用候補**:
  - `condIndepFun_iff_map_prod_eq_prod_map_map` (`Conditional.lean` 周辺) — γ-form と直結
  - `Measure.compProd_map` / `Measure.compProd_congr` / `Kernel.map_prod_eq` — γ-form の RHS で plumbing
  - `MeasurableEquiv.piEquivPiSubtypeProd` / `MeasurableEquiv.prodAssoc` — `X^n = X_i × X^{≠i}` の MeasurableEquiv

### Phase 0 タスク

- [ ] (0.1) `loogle "condIndepFun, weak_union"` 等で graphoid 系の Mathlib 在庫を確認。
- [ ] (0.2) `loogle "IsMarkovChain"` / `rg "IsMarkovChain"` で InformationTheory 内既存補題を網羅。
- [ ] (0.3) `loogle "ProbabilityTheory.condDistrib_prod"` — 中央 RV `Zc` を `(Xs, Zc)` に格上げする経路の確認。
- [ ] (0.4) 既存 `isMarkovChain_swap` / `isMarkovChain_map_right` (CondEntropyMemoryless.lean、private) を移動 or 再宣言するかの判断 — 再宣言 (local) 推奨、上位 file の private 性を保つ。

## Phase A — bridge 補題 `isMemorylessChannelStrong_of_isMemorylessChannel`

### Phase A.0 — 補助 graphoid 補題

#### A.0.a `isMarkovChain_drop_right_in_left` (左 RV が pair `(A, B)` のときに `A` 単独に縮める)

```lean
theorem isMarkovChain_drop_right_in_left
    {A B : Type*} [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
                  [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace Y] [Nonempty Y]
    (As : Ω → A) (Bs : Ω → B) (Zc : Ω → Z) (Yo : Ω → Y)
    (hAs : Measurable As) (hBs : Measurable Bs)
    (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ (fun ω => (As ω, Bs ω)) Zc Yo) :
    IsMarkovChain μ As Zc Yo
```

**証明戦略**: `isMarkovChain_map_left` を `f := Prod.fst : A × B → A` に適用、`Measurable.fst = measurable_fst`。10-15 行。

**用途**: A.1 で (★) の `(X^{≠i}, Y^{≠i})` から `Y^{≠i}` を落として左を `X^{≠i}` 単独にする。

#### A.0.b `isMarkovChain_bundle_with_middle` (中央 RV `Zc` を左の sibling として bundle)

実は γ-form の構造上、Markov chain `As → Zc → Yo` から `(As, Zc) → Zc → Yo` への augment は `Zc` が中央なので **自明な joint factorization** で成立 (条件付き `Zc` 下では `Zc` 自身は定数)。

```lean
theorem isMarkovChain_bundle_left_middle
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Z]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    IsMarkovChain μ (fun ω => (Xs ω, Zc ω)) Zc Yo
```

**証明戦略**: γ-form の RHS は `(condDistrib (Xs, Zc) Zc μ) ×ₖ (condDistrib Yo Zc μ)`、第 1 因子は `condDistrib_prod_self` 系 (中央 RV を含む joint の条件付き分布は `Kernel.deterministic` で `Zc` 成分を固定) で展開する。**注意**: D-2'' deferred plan の Phase A.3 (deferred 理由: `Kernel.deterministic` plumbing が ~80-150 行で泥沼化) と同種の補題。

**実装代替案 (推奨)**: γ-form を直接展開せず、**LHS = RHS の measurable 関数押し出し** で示す。

```
μ.map (Zc, (Xs, Zc), Yo)
  = (μ.map (Zc, Xs, Yo)).map (id × ((· , Zc) ∘ fst) × id)
  -- = ((μ.map Zc) ⊗ₘ K_X ×ₖ K_Y).map ...
```

40-80 行と見積。

**用途**: A.1 で `X^{≠i} → X_i → Y_i` から `(X^{≠i}, X_i) → X_i → Y_i` への augment、その後 `(X^{≠i}, X_i) ↔ X^n` を MeasurableEquiv で reshape。

#### A.0.c **(可能性)** `isMarkovChain_weakUnion`

graphoid weak union を γ-form 上で 1 段で打つ汎用補題。

```
Y ⊥ (B, C) | Z   ⟹   Y ⊥ B | (C, Z)
```

の γ-form 翻訳:

```
IsMarkovChain μ (B, C) Z Y  ⟹  IsMarkovChain μ B (C, Z) Y
```

(γ-form symm + 中央 RV 拡張)。**証明複雑度: 不明** — Mathlib `condIndepFun` レベルに翻訳して `condIndepFun_iff_*` で条件付き分布の積分書き換えを行う必要があり、`[StandardBorelSpace Ω]` を要する可能性が高い。

**Phase 0 で要判断**: A.0.c を 1 本汎用補題として打つか、A.2 の証明内に local 展開するか。**初期方針**: A.2 の証明内で開く (signature 確定するまで API を切らない)。

### Phase A.1 — `per_letter_markov_of_memoryless i`: `X^n → X_i → Y_i`

i : Fin n を固定。`IsMemorylessChannel` の i 番目: Markov chain

```
(fun ω => ((Xother ω), (Yother ω))) → X_i → Y_i
```

ここで `Xother ω := fun (j : {j // j ≠ i}) => Xs j.val ω`、同様に `Yother`。

**Step 1**: `isMarkovChain_drop_right_in_left` で `Yother` を落とす ⟹
```
Markov μ Xother (Xs i) (Ys i)
```

**Step 2**: `isMarkovChain_bundle_left_middle` で `Xs i` を左に augment ⟹
```
Markov μ (fun ω => (Xother ω, Xs i ω)) (Xs i) (Ys i)
```

**Step 3**: `MeasurableEquiv` で `(Xother, X_i) ≃ᵐ X^n` を構成 (既存 `measurableEquivExtract` を `.symm` で利用、α 上の同型)、`isMarkovChain_map_left` で push。

```
Markov μ (fun ω j => Xs j ω) (Xs i) (Ys i)   -- これが per_letter_markov i
```

行数見積: ~50-80 行 (Step 3 の MeasurableEquiv plumbing が膨らみがち)。

### Phase A.2 — `outputs_cond_indep_of_memoryless i`: `Y^{≠i} → X^n → Y_i`

i : Fin n を固定。出発点は同じ:

```
Markov μ (fun ω => (Xother ω, Yother ω)) (Xs i) (Ys i)
```

**目標**:
```
Markov μ Yother (fun ω j => Xs j ω) (Ys i)
```

これは **中央 RV が `X_i` から `X^n` に拡大、かつ左 RV が `(Xother, Yother)` から `Yother` 単独に縮小** という二段変換。

**経路 (graphoid weak union)**:
出発点 γ-form は `Y_i ⊥ (Xother, Yother) | X_i` と読める (Markov chain ⇔ 条件付き独立)。weak union を適用:
```
Y_i ⊥ Yother | (Xother, X_i)
```

`(Xother, X_i) ≃ᵐ X^n` で reshape ⟹
```
Y_i ⊥ Yother | X^n
```

γ-form に戻すと:
```
Markov μ Yother X^n (Y_i)   -- これが outputs_cond_indep i
```

**実装戦略 (γ-form 直接、`[StandardBorelSpace Ω]` 不要を維持)**:

1. 出発点 (★) の γ-form を、joint `μ.map (X_i, Xother, Yother, Y_i)` と factored RHS で書く。
2. `Xother` を **中央 (条件付け側)** へ移す: weak union を γ-form で打つには、joint `μ.map ((Xother, X_i), Yother, Y_i)` で中央を `(Xother, X_i)` にした γ-form 表示が `IsMarkovChain μ Yother (Xother, X_i) Y_i` と等価であることを示す。
3. `MeasurableEquiv` で `(Xother, X_i) ≃ᵐ X^n` reshape。

**難所**: Step 2 は γ-form 定義式の **両側変形**:
- LHS = `μ.map (Zc, Xs, Yo)` を `μ.map ((Xother, X_i), Yother, Y_i)` の reshape として書く
- RHS = `(condDistrib Yother (Xother, X_i) μ) ×ₖ (condDistrib Y_i (Xother, X_i) μ)`

ここで重要観察: 出発点 (★) の RHS は

```
(condDistrib (Xother, Yother) X_i μ) ×ₖ (condDistrib Y_i X_i μ)
```

の積に分解。**(Xother, Yother) → X_i** が含むのは `Xother | X_i` と `Yother | (Xother, X_i)` の積分にさらに分解できる (chain rule for conditional distributions)。これにより:

```
condDistrib Y_i X_i μ = condDistrib Y_i (Xother, X_i) μ
```

(per-letter チャネル性、`condDistrib` の中央 RV を `Xother` で augment しても `X_i` のみに依存することを示す。これは `condDistrib_of_independent` 系の補題、要 Mathlib 探索)。

⟹ 結論として γ-form `IsMarkovChain μ Yother (Xother, X_i) Y_i` に到達。

**判断**: この経路は γ-form 直接展開で **40-80 行**、Step 2 の `condDistrib` 中央 augment 補題が Mathlib に直接あれば短く済むが、無ければ自作で +60 行。

**代替: `[StandardBorelSpace Ω]` 経由 β-form** — Mathlib `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight` (`Conditional.lean:867`) で β-form に翻訳、`condIndepFun.symm` 等の axiom を直接適用。短く済むが `[StandardBorelSpace Ω]` を主定理 signature に追加する必要。**現状の `_strong` も `[StandardBorelSpace Ω]` 不要なので、追加すると signature 互換性が崩れる**。要慎重判断。

行数見積: ~80-150 行 (Phase A の最難所)。

### Phase A.3 — bridge メイン定理 `isMemorylessChannelStrong_of_isMemorylessChannel`

```lean
theorem isMemorylessChannelStrong_of_isMemorylessChannel
    {n : ℕ}
    {α : Type*} [MeasurableSpace α] [Nonempty α] [StandardBorelSpace α]
    {β : Type*} [MeasurableSpace β] [Nonempty β] [StandardBorelSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (Ys : Fin n → Ω → β)
    (hXs : ∀ i, Measurable (Xs i)) (hYs : ∀ i, Measurable (Ys i))
    (h_memo : IsMemorylessChannel μ Xs Ys) :
    IsMemorylessChannelStrong μ Xs Ys
```

`⟨A.1, A.2⟩` の structure 構成。本体 5-10 行。

### Phase A — checklist

- [ ] A.0.a `isMarkovChain_drop_right_in_left` — `isMarkovChain_map_left` 経由、~15 行
- [ ] A.0.b `isMarkovChain_bundle_left_middle` — γ-form 押し出し or `condDistrib` plumbing、40-80 行
- [ ] A.1 `per_letter_markov_of_memoryless` — Drop + Bundle + MeasurableEquiv、50-80 行
- [ ] A.2 `outputs_cond_indep_of_memoryless` — graphoid weak union 経路、80-150 行
- [ ] A.3 bridge メイン (structure 構成、5-10 行)
- [ ] **proof-log**: A.0.b と A.2 の plumbing 試行錯誤、`condDistrib` 中央 augment 補題の有無、`[StandardBorelSpace Ω]` 追加判断の根拠を記録 (`docs/shannon/proof-log-d2-pure-ychain.md`)

## Phase B — pure 主定理 `channel_coding_converse_general_memoryless_pure`

### 実装

```lean
theorem channel_coding_converse_general_memoryless_pure
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Msg : Ω → M) (encoder : M → Fin n → α)
    (Ys : Fin n → Ω → β) (decoder : (Fin n → β) → M)
    (hMsg : Measurable Msg) (hYs : ∀ i, Measurable (Ys i))
    (hdecoder : Measurable decoder)
    (hmarkov : Shannon.IsMarkovChain μ Msg
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω))
    (h_memo : IsMemorylessChannel μ (fun i ω => encoder (Msg ω) i) Ys)
    (hMsg_uniform : μ.map Msg = (Fintype.card M : ℝ≥0∞)⁻¹ • Measure.count)
    (hcard : 2 ≤ Fintype.card M)
    (hMI_finite : Shannon.mutualInfo μ
      (fun ω => encoder (Msg ω)) (fun ω i => Ys i ω) ≠ ∞) :
    Real.log (Fintype.card M) ≤
      (∑ i : Fin n, (Shannon.mutualInfo μ
        (fun ω => encoder (Msg ω) i) (Ys i)).toReal)
      + Real.binEntropy (errorProb μ Msg (fun ω i => Ys i ω) decoder)
      + errorProb μ Msg (fun ω i => Ys i ω) decoder
        * Real.log ((Fintype.card M : ℝ) - 1) := by
  set Xs : Fin n → Ω → α := fun i ω => encoder (Msg ω) i with hXs_def
  have hXs_meas : ∀ i, Measurable (Xs i) := ...
  have h_strong : IsMemorylessChannelStrong μ Xs Ys :=
    isMemorylessChannelStrong_of_isMemorylessChannel μ Xs Ys hXs_meas hYs h_memo
  exact channel_coding_converse_general_memoryless_strong
    μ Msg encoder Ys decoder hMsg hYs hdecoder hmarkov h_memo h_strong
    hMsg_uniform hcard hMI_finite
```

行数見積: ~20-40 行 (本体 5 行 + `Xs` の measurable plumbing + 既存 `_strong` の引数の並び順吸収)。

### Phase B — checklist

- [ ] B.1 主定理 sig + body skeleton (sorry) を書いて lake env lean で型確認
- [ ] B.2 sorry を `isMemorylessChannelStrong_of_isMemorylessChannel` 呼出に置換
- [ ] B.3 lake env lean で clean (0 sorry / 0 error)

## Phase C — `InformationTheory.lean` import 追記 + smoke 検証

- [ ] C.1 `InformationTheory.lean` に `import InformationTheory.Shannon.ChannelCodingConverseMemorylessPure` を追記
- [ ] C.2 `lake env lean InformationTheory/Shannon/ChannelCodingConverseMemorylessPure.lean` で clean を確認
- [ ] C.3 `lake build InformationTheory.Shannon.ChannelCodingConverseMemorylessPure` で olean 確定 (依存 module の olean 更新確認)

## Risks / unknowns / 撤退ライン

### R1: A.0.b (`isMarkovChain_bundle_left_middle`) が `Kernel.deterministic` plumbing で泥沼化

D-2'' deferred plan の Phase A.3 と同種の難所。`condDistrib (Xs, Zc) Zc μ` が "Zc 成分は条件と一致、Xs 成分は `condDistrib Xs Zc μ`" という factorization になることを `Kernel.deterministic` で表現する経路が長くなる。

**撤退案 R1-a**: γ-form 押し出し直接経路 (`Measure.map_map` で LHS、`Measure.compProd_map` で RHS) なら 40 行で済む可能性。先にこちらを試す。

**撤退案 R1-b**: A.0.b の bundle 補題自体を **回避** し、A.1 で `X^{≠i} → X_i → Y_i` から **直接 `X^n → X_i → Y_i`** を `isMarkovChain_map_left` で post-process する。具体的には `f : X^{≠i} → X^n` を `j ↦ if j = i then default else x_j` で書けば `X^n` の `i` 成分が `default` になり望む形と一致しない (Xs i 成分が違う) ので **NG**。よってこの撤退案は破綻。bundle は必須。

### R2: A.2 (`outputs_cond_indep_of_memoryless`) の graphoid weak union 経路の長さ

γ-form 直接の Step 2 (`condDistrib Y_i (Xother, X_i) μ = condDistrib Y_i X_i μ`) が Mathlib に対応補題なしの場合、自作で +60 行。

**撤退案 R2-a**: `[StandardBorelSpace Ω]` を pure 主定理 signature に追加し β-form (`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`) 経由で graphoid axiom を直接適用。`_strong` signature が `[StandardBorelSpace Ω]` 不要であった互換性は崩れるが、bridge 補題に限定して仮定を追加する形で局所化可能 (主定理側は変えずに、bridge のみ `[StandardBorelSpace Ω]` を引数に取る形にすれば、主定理に instance を渡せばよい)。

**撤退案 R2-b (MVP)**: bridge の自前構築を諦め、ユーザ側に `IsMemorylessChannelStrong` を直接要求する形で publish。これは **scope 縮小 MVP**、既存 `_strong` を「rename」して "pure" として再 publish する。本サブ計画のゴールを完全には満たさないが、`IsMemorylessChannel` 由来でも `IsMemorylessChannelStrong` を **手動で構成して渡す** ことを caller に要求する形で互換性を保つ。

### R3: 既存 `isMarkovChain_swap` / `isMarkovChain_map_right` が CondEntropyMemoryless.lean の private で見えない

Phase A で graphoid 経路を打つ際に `isMarkovChain_swap` が必要になる可能性。

**対処**: ChannelCodingConverseMemorylessPure.lean 内で同名の `private lemma` を再宣言 (InformationTheory 全体の API 表面を増やさず、file-scoped で再利用)。CondMutualInfo.lean に昇格する案もあるが scope 拡大なので保留。

### R4: 規模見積誤差

230-400 行のレンジで見積もったが、A.2 の `condDistrib` 中央 augment 補題が最大の不確定要素。最悪ケースで **+150 行**、合計 ~550 行になる可能性 ~30%。

### 撤退ライン (最終)

R1 + R2 が想定以上に膨らみ、Phase A が 1 セッション内に収まらない場合:

1. **Phase A.1 のみ完了** (per_letter_markov_of_memoryless) して publish、Phase A.2 (outputs_cond_indep) は deferred として記録。pure 主定理は publish せず本 plan を半完了で deferred とする。
2. 上記 R2-b の MVP 案 (Strong を rename) を採用、`channel_coding_converse_general_memoryless_pure` を `_strong` の alias として publish (`h_memo` を `h_strong` から手動構成することは caller 責務)。これは **D-2'' 系列の最終撤退点**。

## 判断ログ

1. **`IsMemorylessChannel` から `IsMemorylessChannelStrong` を導出可能 (D-2'' deferred の bypass)**: 前回 D-2'' は `h_yother_zero` (encoder 任意で偽) で頓挫したが、Strong axiom (`per_letter_markov` + `outputs_cond_indep`) は `IsMemorylessChannel` の γ-form `(X^{≠i}, Y^{≠i}) → X_i → Y_i` から graphoid (marginalize + weak union) で **構造的に導出可能**。`h_yother_zero` を経由しないので encoder degenerate 反例にも頑健。**この観察が本計画の核心**。
2. **`ChannelCodingConverseGeneralStrong.lean` を touch しない方針**: 既存 file は (a) 既に 0 sorry / 0 warning、(b) `_strong` の signature が D-2' 互換性 (`_h_memo` を historical 引数として持つ) のため変更コストが高い。新規 file で wrapper 化する方が clean。
3. **`[StandardBorelSpace Ω]` を追加しない方針 (γ-form 直経路で行く)**: 既存 `_strong` も `[StandardBorelSpace Ω]` 不要であり、互換性のため pure も同条件で publish したい。Phase A.2 で β-form 経由が必要になった場合のみ撤退ライン R2-a に切替。
4. **既存 `isMarkovChain_swap` / `isMarkovChain_map_right` を CondMutualInfo.lean に昇格しない**: scope 拡大コスト > 再宣言コスト。`ChannelCodingConverseMemorylessPure.lean` 内に `private lemma` 再宣言で対応。将来 4 件以上の利用者が出れば再評価。
5. **proof-log を残す**: Phase A の graphoid 補題 (特に A.0.b と A.2) は plumbing が泥沼化リスク中、試行錯誤の記録が将来の同系 bridge (`isMemorylessFeedback` 系、Slepian-Wolf 等) で再利用可能。

## 参考

- 親 plan (deferred 含む): [`channel-coding-converse-d2-doubleprime-plan.md`](./channel-coding-converse-d2-doubleprime-plan.md)
- 親 plan (D-2' 完了): [`channel-coding-converse-general-d2-prime-plan.md`](./channel-coding-converse-general-d2-prime-plan.md)
- 既存実装: `InformationTheory/Shannon/ChannelCodingConverseGeneralStrong.lean` (272-321), `InformationTheory/Shannon/ChannelCodingConverseGeneralComplete.lean` (92-99)
- 補助 API: `InformationTheory/Shannon/CondMutualInfo.lean:652` (`isMarkovChain_map_left`), `InformationTheory/Shannon/CondEntropyMemoryless.lean:316,353` (private `isMarkovChain_swap`, `_map_right`)
- moonshot template: [`docs/moonshot-plan-template.md`](../moonshot-plan-template.md)
- subplan template: [`docs/subplan-template.md`](../subplan-template.md)
