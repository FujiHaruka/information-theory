# Channel coding converse — pure memoryless per-summand bound (D-2'') ムーンショット計画 🌙

(D-2'' / 親 plan [`channel-coding-converse-general-d2-prime-plan.md`](./channel-coding-converse-general-d2-prime-plan.md) の "後継 deferred"、2026-05-14 起草)

D-2'' は D-2' 完了 (`ChannelCodingConverseGeneralComplete.lean` 578 行、3 仮説 pass-through 形) の次の段。
Phase C/D で残された 3 仮説 `h_yother_zero` / `h_split` / `h_markov_xprefix` を **`IsMemorylessChannel` から内部派生**
して 1 仮定の "純粋" 形で publish する。

> 実態整合 (2026-05-20): SUPERSEDED — 本 plan は「B.2 (`h_yother_zero`) は `IsMemorylessChannel` 単独から派生不可」と結論し deferred したが、後継サブ計画 [`channel-coding-converse-memoryless-ychain-plan.md`](./channel-coding-converse-memoryless-ychain-plan.md) が `h_yother_zero` 経由を **bypass** する Strong 経路 (graphoid weak union) で pure 形を完成済。証拠: `channel_coding_converse_general_memoryless_pure` (`InformationTheory/Shannon/ChannelCodingConverseMemorylessPure.lean:650`、0 sorry) は `h_memo : IsMemorylessChannel` のみを取り、`IsMemorylessChannelStrong` を内部派生 (`per_letter_markov_of_memoryless` + `outputs_cond_indep_of_memoryless`) して既存 `_strong` wrapper を呼ぶ。下記「B.2 派生不可」の結論は経路選択の問題であり、最終結果としては SUPERSEDED。

## 進捗

- [x] Phase 0 — Mathlib API inventory ✅
- [~] Phase A — `CondMutualInfo.lean` 補助補題 3 本 (2/4 完了: left/middle reshape + Markov post-process、A.3 deferred)
- [ ] Phase B — 3 仮説の `IsMemorylessChannel` からの派生 (B.2 が `IsMemorylessChannel` 単独からは
  本質的に派生不可と判明、B.1/B.3 は Phase A.3 待ち)
- [ ] Phase C — `channel_coding_converse_general_memoryless_pure` 組み立て (deferred)

## ゴール / Approach

**ゴール (主定理 signature)**:

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
      (∑ i : Fin n, (Shannon.mutualInfo μ (fun ω => encoder (Msg ω) i) (Ys i)).toReal)
        + Real.binEntropy (errorProb …) + errorProb … * Real.log (Fintype.card M - 1)
```

**Approach (3 段戦略)**:

D-2' Phase C は `h_yother_zero` / `h_split` / `h_markov_xprefix` を Phase C 仮説に格上げした撤退ライン。
D-2'' はこれらを `IsMemorylessChannel` の Markov chain `(X^{≠i}, Y^{≠i}) → X_i → Y_i` から構造的に派生する。

**Step 1** (`h_markov_xprefix` 派生): `X^{<i}` は `X^{≠i}` の Prod.fst 系成分 ⇒ Markov chain 左 RV の
post-processing で `X^{<i} → X_i → Y_i`、その後さらに左 RV を `X_i` で augment して
`(X^{<i}, X_i) → X_i → Y_i`。

**Step 2** (`h_yother_zero` 派生): Markov chain `X_i → (X^{<i}, X^{>i}, Y_i) → Y^{≠i}` (memoryless の swap +
中央 augment) ⇒ `condMutualInfo_eq_zero_of_markov` で `condMI(X_i; Y^{≠i} | (X^{<i}, Y_i)) = 0`。

**Step 3** (`h_split` 派生): `Y^n = (Y_i, Y^{≠i})` reshape を `MeasurableEquiv.piFinSuccAbove i` で確立、
`condMutualInfo_chain_rule_Y_2var` (D-2' Phase B 既存) を適用、`condMI` の Y 引数 reshape 不変性で吸収。

### 規模見積

| Phase | 内容 | 行数 |
|---|---|---|
| 0 | inventory | 0 |
| A | CondMutualInfo 補助補題 3 本 (left post-proc / Y reshape / middle augment) | 180-260 |
| B | `IsMemorylessChannel` から 3 仮説への内部派生 | 120-180 |
| C | pure 形主定理組み立て | 40-60 |
| **合計** | | **~340-500 行** |

D-2' (578 行) + ~350 行 で `ChannelCodingConverseGeneralComplete.lean` は ~900-1000 行に。

## Phase 0 — Mathlib API inventory

### Mathlib (新規参照)

1. **`MeasurableEquiv.piFinSuccAbove`** (`Embedding.lean:560`) — `Fin (n+1) → α ≃ᵐ α × (Fin n → α (Fin.succAbove i j))`。
   D-2'' では特に `Y^n ≃ᵐ Y_i × Y^{≠i}` reshape の核。MIChainRule で既に複数回利用済 (`MIChainRule.lean:183`)。
2. **`MeasurableEquiv.piEquivPiSubtypeProd`** (`Embedding.lean:572`) — `(∀ i, π i) ≃ᵐ (∀ i : {i // p i}, π i) × ∀ i : {i // ¬p i}, π i`。
   D-2'' Phase B Step 1 で `X^{≠i} ≃ᵐ X^{<i} × X^{>i}` の経路として使う。
3. **`ProbabilityTheory.condDistrib_comp`** (`CondDistrib.lean:183`) —
   `condDistrib (f ∘ Y) X μ =ᵐ (condDistrib Y X μ).map f`。
   `IsMarkovChain` (γ-form) の左 RV 後処理を kernel レベルに移して証明する経路。
4. **`Measure.map_map`** + **`Measure.map_id`** — pushforward 計算の plumbing。

### 既存 InformationTheory 補題 (D-2' / E-10' inventory を再利用)

1. `Shannon.IsMarkovChain` (`CondMutualInfo.lean:71`)
2. `Shannon.mutualInfo_chain_rule` (`CondMutualInfo.lean:219`)
3. `Shannon.condMutualInfo_comm` (`CondMutualInfo.lean:295`)
4. `Shannon.condMutualInfo_eq_zero_of_markov` (`CondMutualInfo.lean:353`)
5. `Shannon.mutualInfo_le_of_markov` (`CondMutualInfo.lean:378`)
6. `Shannon.mutualInfo_map_left_measurableEquiv` / `_right` (`MIChainRule.lean:43, 75`)
7. **D-2' 新規** `condMutualInfo_chain_rule_X_2var` / `_Y_2var`
   (`ChannelCodingConverseGeneralComplete.lean:215, 295`) — Phase A 補題 1 と Phase B Step 3 で再利用

### D-2'' で新規

1. **`Shannon.condMutualInfo_map_left_measurableEquiv`** / **`_map_middle_measurableEquiv`** /
   **`_map_right_measurableEquiv`** (Phase A.1、~30-50 行 / 各) — `MeasurableEquiv` reshape の不変性 (3 引数)。
2. **`Shannon.isMarkovChain_map_left`** (Phase A.2、~30-50 行) — Markov 左 RV の post-processing (`f ∘`)。
3. **`Shannon.isMarkovChain_augment_left_with_middle`** (Phase A.3、~50-80 行) —
   `X → Z → Y` ⇒ `(X, Z) → Z → Y` (中央 RV を左に augment)。

## Phase A — CondMutualInfo.lean 補助補題 3 本

### 補題 A.1: `condMutualInfo_map_<arg>_measurableEquiv` (3 本)

```lean
theorem condMutualInfo_map_left_measurableEquiv
    {X' : Type*} [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X']
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z)
    (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc)
    (e : X ≃ᵐ X') :
    condMutualInfo μ (fun ω => e (Xs ω)) Yo Zc = condMutualInfo μ Xs Yo Zc
```

(Y / Z 版も同様。) `condMutualInfo` は `klDiv` で定義され、joint / marginal 両側に `MeasurableEquiv` を
かけるだけなので `mutualInfo_map_left_measurableEquiv` (MIChainRule.lean:43) と同型の証明
(`klDiv_map_measurableEquiv` + `condDistrib_map`)。

**用途**: Phase B Step 3 (`Y^n ↔ (Y_i, Y^{≠i})` reshape) + Step 2 (`X^{≠i} ↔ (X^{<i}, X^{>i})` reshape)。

### 補題 A.2: `isMarkovChain_map_left`

```lean
theorem isMarkovChain_map_left
    {X' : Type*} [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X']
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    {f : X → X'} (hf : Measurable f)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    IsMarkovChain μ (fun ω => f (Xs ω)) Zc Yo
```

**証明戦略**: `IsMarkovChain` γ-form `μ.map (Z, X, Y) = μ.map Z ⊗ ((condDistrib X Z μ) ×ₖ (condDistrib Y Z μ))`
の両辺に `Prod.map id (Prod.map f id)` を pushforward。LHS は `μ.map (Z, f∘X, Y)` (Measure.map_map)。
RHS は `condDistrib_comp` で `(condDistrib (f∘X) Z μ) = (condDistrib X Z μ).map f` に置換、
`Kernel.map_prodMkLeft` 系 plumbing。

**用途**: Phase B Step 1 (`X^{≠i} → X_i → Y_i` から `X^{<i} → X_i → Y_i` を Prod.fst で抽出)。

### 補題 A.3: `isMarkovChain_augment_left_with_middle`

```lean
theorem isMarkovChain_augment_left_with_middle
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y)
    (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo)
    (hmarkov : IsMarkovChain μ Xs Zc Yo) :
    IsMarkovChain μ (fun ω => (Xs ω, Zc ω)) Zc Yo
```

**証明戦略**: `Xs → Zc → Yo` の `condDistrib (Xs, Zc) Zc μ` は `condDistrib_prod_self` 系で
`(condDistrib Xs Zc μ) ×ₖ (Kernel.deterministic id _)` のような形に書ける (Mathlib 既存
`condDistrib_comp_self`)。これを γ-form Markov の RHS に挿入 → joint 側も Prod.map id (Prod.map Xs id) で
対応。**注意**: この補題は標準的な確率論結果だが Mathlib に直接対応するものが無いため自作。
代替路: 直接 condMI = 0 形で示し、`condMutualInfo_eq_zero_of_markov` を経由しない経路もある (要評価)。

**用途**: Phase B Step 1 後段 (`X^{<i} → X_i → Y_i` から `(X^{<i}, X_i) → X_i → Y_i` への augment)。
Phase B Step 2 でも `X_i → (X^{<i}, X^{>i}, Y_i) → Y^{≠i}` の中央 augment に再利用。

## Phase B — 3 仮説の `IsMemorylessChannel` からの派生

i : Fin n を固定。`Xother ω j := Xs j.val ω` for `j : {j // j ≠ i}`、同様に `Yother`、
`Xprefix ω j := Xs ⟨j.val, ...⟩ ω` for `j : Fin i.val`。

### B.1 — `h_markov_xprefix` 派生

```
IsMemorylessChannel ⇒ Markov (Xother, Yother) → X_i → Y_i              -- (h_memo i)
  ↓ A.1 + A.2 (左 RV `Prod.fst`、Xother のみ取り出す)
Markov Xother → X_i → Y_i
  ↓ A.1 + A.2 (Xother を MeasurableEquiv `piEquivPiSubtypeProd` で `Xprefix × Xsuffix` に reshape、
                 さらに `Prod.fst` で Xprefix を取り出す)
Markov Xprefix → X_i → Y_i
  ↓ A.3 (中央 X_i を左に augment)
Markov (Xprefix, X_i) → X_i → Y_i                                       -- = `h_markov_xprefix i`
```

行数見積: ~60-80 行。

### B.2 — `h_yother_zero` 派生

```
IsMemorylessChannel ⇒ Markov (Xother, Yother) → X_i → Y_i              -- (h_memo i)
```

ここから `condMI(X_i; Yother | (Xprefix, Y_i)) = 0` を導きたい。直接の Markov 形は
`X_i → (Xprefix, Y_i, …) → Yother` (X_i から見て他は全部条件で固定された下で独立)。

戦略: memoryless の Markov chain `(Xother, Yother) → X_i → Y_i` の Z↔X swap (Mathlib
`condIndepFun.symm` 同型) で `(Yother) → X_i → (Y_i, Xother)` 系を作り、さらに **conditional Markov**
形へ。実は単純な Markov chain の単独適用では足りず、**conditional independence**
`Yother ⫫ X_i ∣ (Xprefix, Y_i, Xsuffix)` 形を経由する必要がある (`condIndepFun_iff_condDistrib_...`)。

採用路: memoryless の元 Markov chain を **Y_i 側を変数 (condition argument 的に) shift** する補題
`condMutualInfo_eq_zero_of_markov` の **条件付き拡張版** を新規追加 (Phase A.3 の派生として
~50-80 行)。あるいは Phase B 内に local lemma として封じ込め。

代替: B-form Markov (`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`) を経由し、`[StandardBorelSpace Ω]` 仮定を
加える (D-2'' 主定理 signature を変更)。**判断**: D-2 / D-2' は `[StandardBorelSpace Ω]` 不要だったため
保つほうが望ましい → γ-form 直経路で行く。

行数見積: ~60-100 行 (難所)。

### B.3 — `h_split` 派生

Y-axis 2-var conditional chain rule (`condMutualInfo_chain_rule_Y_2var`、D-2' Phase B 既存) を
適用したいが LHS が `condMI(X_i; Y^n | Xprefix)`、RHS の Y 引数は `(Y_i, Yother)`。

戦略:
1. **A.1 (Y 引数 reshape)**: `condMI(X_i; Y^n | Xprefix) = condMI(X_i; (Y_i, Yother) | Xprefix)` を
   `MeasurableEquiv.piFinSuccAbove` 経由で。 ※ ただし `Y^n` の構造 `Fin n → β` と
   `Y_i × Y^{≠i}` の MeasurableEquiv は subtype 経由なので非自明 reshape。
   厳密には `Yother` の index `{j // j ≠ i}` と `Fin.succAbove i` 経由の `Fin (n-1) → β` を繋ぐ
   `Subtype.fintype` + `Fin.succAboveEquiv` の MeasurableEquiv を 1 個自作 (Phase A の延長、~30 行)。
2. **`condMutualInfo_chain_rule_Y_2var`** 適用: `I(X_i; (Y_i, Yother) | Xprefix) = I(X_i; Y_i | Xprefix) +
   I(X_i; Yother | (Xprefix, Y_i))`。
3. これで `h_split i` の RHS と一致。

行数見積: ~50-70 行。

### Phase B 行数合計: ~170-250 行。

## Phase C — pure 形主定理組み立て

`channel_coding_converse_general_memoryless_pure` を D-2' 既存
`channel_coding_converse_general_memoryless` を内部呼び出しする形で記述。Phase B の派生で
`h_yother_zero` / `h_split` / `h_markov_xprefix` を構築 (∀ i 形)、それらを既存定理に渡す。

行数見積: 40-60 行。

## Risks / unknowns

1. **B.2 (`h_yother_zero` 派生)** がもっとも不確実: γ-form Markov 単独からの簡潔な経路が無く、
   独立性条件付け化のため新規 Phase A 補題が増える可能性。**plan-時撤退ライン**: 必要なら
   `[StandardBorelSpace Ω]` を仮定して β-form 経由 (D-2 / D-2' との signature 整合性は犠牲)。
2. **`Yother` の index 型 `{j // j ≠ i}` と `Fin (n-1)` の MeasurableEquiv plumbing**: Mathlib に
   `Fin.succAboveEquiv` は `Equiv` レベルで存在するが `MeasurableEquiv` 版は自作要。Phase A の
   `MeasurableEquiv` 補助補題 1 本に統合可能。
3. **Phase A.3 (`isMarkovChain_augment_left_with_middle`)** が `Kernel.map_prodMkLeft` 系の plumbing
   で泥沼化する可能性: 直接 condMI = 0 形で示す代替経路 (DPI + chain rule 合成) を準備しておく。
4. **規模見積誤差**: 撤退ライン採用で D-2' が 578 行 (見積 430-600) でちょうど範囲。D-2'' は構造
   plumbing 主体なので overshoot しやすい (~500-700 行に膨らむ可能性 ~25%)。

## Mathlib inventory 必要箇所

- `MeasurableEquiv.piFinSuccAbove` (Embedding.lean:560) ✓
- `MeasurableEquiv.piEquivPiSubtypeProd` (Embedding.lean:572) ✓
- `ProbabilityTheory.condDistrib_comp` (CondDistrib.lean:183) ✓
- `ProbabilityTheory.condDistrib_comp_self` (CondDistrib.lean:196) ✓
- `Kernel.prodMkRight` / `prodMkLeft` 系 (Composition/MapComap.lean) — 要確認
- `Kernel.map_prod` / `Kernel.map_prodMkRight` の正確な signature を `loogle` で確認 (Phase A.2/A.3 plumbing)
- 不在予測: `IsMarkovChain` augment 系の純粋 Mathlib 補題は存在しない (InformationTheory で自作確認済)

## 判断ログ

1. **`[StandardBorelSpace Ω]` 不要を維持**: D-2 / D-2' 系の signature を保つ → γ-form 経路で全ステップ
   通す。B.2 で詰まる場合のみ撤退検討。
2. **Phase A 補助補題は `CondMutualInfo.lean` に追加 (D-2' は local section だった)**: D-2'' で
   3 本以上の汎用補題が増えるため公開 API として整備、将来 SlepianWolf binning や Strong Stein でも
   再利用可能性が高い。
3. **3 仮説派生は順序自由**: B.1 → B.2 → B.3 で書くが依存はなく並列可能。

### 2026-05-14 セッション 実装結果

**Phase A (部分完了)**:
- ✅ `condMutualInfo_map_left_measurableEquiv` (CondMutualInfo.lean, ~50 行) —
  joint side: `compProd_map_condDistrib` で `μ.map (Z, X, Y)` に翻訳して `Measure.map_map`、
  factored side: `condDistrib_comp` + `Kernel.map_prod_eq` + `Measure.compProd_map` plumbing。
- ✅ `condMutualInfo_map_middle_measurableEquiv` (~5 行) — `condMutualInfo_comm` 2 回経由で
  left に帰着。
- ⏸️ `condMutualInfo_map_right_measurableEquiv` — deferred (Z conditioner reshape は
  `condDistrib_ae_eq_of_measure_eq_compProd` + `Kernel.comap` plumbing で ~150 行と見積もる、
  D-2'' Phase B では Y/X reshape のみで足りるため後送り)。
- ✅ `isMarkovChain_map_left` (Phase A.2, ~30 行) — γ-form Markov 左 RV を `f ∘` で
  post-process。`condDistrib_comp` + `Measure.compProd_map` + `Kernel.map_prod_eq` の合成。
- ❌ `isMarkovChain_augment_left_with_middle` (Phase A.3) — **deferred**。
  `condDistrib (Xs, Zc) Zc μ` が `δ_z` を埋め込む形の kernel になり、`Kernel.deterministic`
  系の plumbing が泥沼化、~80-150 行と見積もる。

**Phase B/C (未着手)**:
- B.1 (`h_markov_xprefix` 派生) は A.3 を要する。
- **B.2 (`h_yother_zero` 派生) は `IsMemorylessChannel` 単独からは導出不可** (重要発見):
  分析の結果、`condMI(X_i; Y^{≠i} | (X^{<i}, Y_i)) = 0` は `(X^{≠i}, Y^{≠i}) → X_i → Y_i`
  Markov chain だけでは成立しない。`P(X_i, Y^{≠i} | X^{<i}, Y_i)` の積分形に X_i が暗黙に
  入るため。一般に X^n が i.i.d. or X^n の Markov 構造 (`Msg → X^n` の Markov-additive 構造)
  などの追加仮定が必要 (Cover-Thomas Thm 7.9 の textbook proof は subadditivity 経由で
  `I(X^n; Y^n) ≤ ∑ I(X_i; Y_i)` を導き、per-summand bound を経由しない)。
- 撤退ライン `[StandardBorelSpace Ω]` 採用でも本質的問題は解決しない (β-form でも
  同じ structural gap)。

**結論**: D-2'' の "pure" 化は `IsMemorylessChannel` の **強化** (Markov chain `Msg → X^n → Y^n`
の inclusion など) を要する。本セッションは Phase A の reshape API + Markov 左 post-processing
を整備するに留め、Pure 主定理は **deferred** とする。

**規模**: CondMutualInfo.lean 413 → 555 行 (+142 行、Phase A 部分)。
`ChannelCodingConverseGeneralComplete.lean` 不変 (578 行のまま)。
0 sorry / 0 warning (CondMutualInfo.lean の警告は pre-existing 2 件のみ、本セッションでは増えず)。

## 参考

- 親 plan: [`channel-coding-converse-general-d2-prime-plan.md`](./channel-coding-converse-general-d2-prime-plan.md)
- 兄弟 plan (E-10' 完成形): [`dmc-feedback-per-letter-bound-plan.md`](./dmc-feedback-per-letter-bound-plan.md)
- moonshot template: [`docs/moonshot-plan-template.md`](../moonshot-plan-template.md)
