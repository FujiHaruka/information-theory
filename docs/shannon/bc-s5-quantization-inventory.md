# BC S5 有限量子化 — M0 在庫

> 親 plan (SoT): [`bc-general-region-plan.md`](bc-general-region-plan.md) §Phase 5「等号 (less noisy)」
> S5 / §撤退ライン **L-BCO9** / §後続作業 F-12。前段の在庫:
> [`bc-lessnoisy-equality-inventory.md`](bc-lessnoisy-equality-inventory.md) §Q2-3。
> probe は `scratchpad/ProbeS5Quantize.lean` / `ProbeS5Claims.lean` / `ProbeS5Tail.lean` /
> `ProbeS5Finite.lean` / `ProbeS5Placement.lean` (すべて `lake env lean` silent)。

---

## 結論サマリ

- **Q1 = 3 本とも 真**。ただし claim 1 (`a_m ≥ a`) は **`IsUVChannelLaw` を落とすと偽**
  (反例あり、§Q1-D)。claim 2 / claim 3 はチャネル法の仮説を **1 本も要求しない**。
  3 本とも実 def に照らして検算済 (`uvInfoSum₂` が足す項は `condMutualInfo ν X Y₁ U` と**逐語同一**、
  `Bridge.lean:787`)。
- **Mathlib の壁 0 件 / プロジェクト側の壁も 0 件**。S5 の 9 obligation はすべて既存資産の合成で、
  **claim 1 は 56 行・claim 3 は 14 行・claim 2 の分解と裾補題は 45 行を実際に compile 通過させた**
  (§Q4)。自作するのは「既存部品の並べ替え」だけで、新しい数学は 0 行。
- **行数見積り ~280 行** (うち **147 行は probe で実測済**、残り ~130 行は plumbing)。
  親 plan の `~160 行` は**上方修正が要る**。step 内分割は §Q5。**L-BCO9 は不発動の見込み**。
- **最初に切るべきは S5-a (共有の有限性補題 3 本、~45 行)**。`mutualInfo_ne_top` が
  **両側 `[Fintype]` を要求する**ため `U = ℕ` のスロットには既存の有限性補題が 1 本も当たらず、
  ここを開ける `mutualInfo_ne_top_of_right` が claim 1 / claim 2 / `uvInfoSum₂ ν ≠ ∞` の
  **3 箇所すべてで前提**になる (§最も危ない発見)。

### 最も危ない発見 (1 行)

**`mutualInfo_ne_top` (`MutualInfo.lean:174`) は `[Fintype X]` と `[Fintype Y]` を両方要求する**ので、
外界の `ℕ` 補助を持つ `uvInfo₂ ν` / `uvInfoSum₂ ν` の有限性は in-repo の既存補題では**出ない**
(`condMutualInfo_ne_top` は条件付け側にも `[Fintype Z]` を要求、`CondMutualInfo.lean:320`)。
出口は「自明な Markov 鎖 `Xs → Yo → Yo` + DPI」で、`isMarkovChain_comp_conditioner_right`
(`CondEntropyMemoryless.lean:371`) を `f := id` で使う **5 行** (probe P3/§Q4 で実測)。
これを最初に置かないと、ENNReal の相殺 (`condMutualInfo_chain_rule_X_2var` の `hWcY_fin` /
`condMutualInfo_eq_of_leftInverse_cond` の `hfin`) が**すべて詰まる**。

---

## Q1 3 本の命題の真偽 — **3 本とも 真**

### Q1-A 実 def との照合 (逐語)

| 記号 | 実体 | file:line |
|---|---|---|
| `b` | `uvInfo₂ ν = mutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2)` | `OuterBoundUV/Bridge.lean:782` |
| `a` | `uvInfoSum₂ ν = uvInfo₂ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)` の**第 2 項** | `Bridge.lean:787` |
| 引数順 | `mutualInfo_chain_rule … : mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` ⟹ `condMutualInfo μ A B C = I(A;B∣C)` | `CondMutualInfo.lean:214` |

⟹ ブリーフの `a := I(X;Y₁∣U)` は **`condMutualInfo ν (·.2.2.1) (·.2.2.2.1) (·.1)` と逐語同一** ✅。

### Q1-B claim 1 `a_m ≥ a` — **真** (probe で全証明が compile、本体 56 行)

導出はブリーフどおりだが **1 点補正した**: 「`I(X;Y₁∣(U,U_m)) = I(X;Y₁∣U)`」を出す既存補題
`condMutualInfo_eq_of_leftInverse_cond` は**逆向き** (`f ∘ Zc` を `Zc` に落とす) なので
`f := fun u ↦ (qm m u, u)` / `g := Prod.snd` を渡す形になり、その `hfin` が
**`mutualInfo ν U Y₁ ≠ ∞` (`U = ℕ`)** を要求する。ここが §最も危ない発見の入口。

### Q1-C claim 2 `b - b_m ≤ ε_m` / claim 3 `ε_m → 0` — **真**

- claim 2 の連鎖律側 (`b = b_m + ∫⁻ t, I_{κ t}(U;Y₂)`) は `mutualInfo_compProd_eq_add_lintegral`
  **1 発**で出る (`tag := qm m` がそのまま `hrec` を満たす、probe 12 行)。ブリーフの
  「連鎖律 + 裾評価の 2 段」は**1 段に縮む**。
- 裾側は 4 部品に分解でき**全部 probe 済**: fiber 性 11 行 / 頭部スライスの a.s. 定数性 6 行 /
  定数の MI = 0 が 8 行 / 裾スライスの `≤ ofReal (log |β₂|)` が 17 行。
- claim 3 は `tendsto_measure_iInter_atTop` で **14 行** (probe 通過)。

### Q1-D 退化ケース 2 本 (**構造の違う 2 軸**)

| 軸 | 設定 | 予測 | 実際 |
|---|---|---|---|
| **量子化器が退化** | `m = 0` (`qm 0` は定数) | claim 1 は `I(X;Y₁∣U) ≤ I(X;Y₁)`。**Markov `U→X→Y₁` が無いと偽** (`Y₁ = X ⊕ U`, `U ⊥ X` 一様ビットで左辺 1 bit / 右辺 0)。claim 2 は `b ≤ 0 + ε₀`、`ε₀ = 1 · log\|β₂\|` | `claim1_a_le_am` は `m = 0` でも通る (`h : IsUVChannelLaw` を実際に使う)。`ε₀ = log\|β₂\|` は `I(U;Y₂) ≤ H(Y₂) ≤ log\|β₂\|` とちょうど整合 ✅ |
| **測度が退化** | `U ≡ 0` a.s. (Dirac)、`m ≥ 1` ⟹ `qm m` は台の上で単射 | `a_m = a` / `b_m = b` / `ε_m = ν{q \| m ≤ q.1} = 0` (等号で成立、緩くない) | 3 本とも等号で成立 ✅ |

⟹ **claim 1 の `IsUVChannelLaw` は飾りではなく本質的な構造前提**。ただし
「等号が成り立つ」型の述語ではなく外界の union の添字条件そのもの (判断ログ 9) なので
load-bearing hyp ではない。**claim 2 / claim 3 は `IsUVChannelLaw` も `W` も要求しない** (probe 実測)。

### Q1-E `ε_m` の具体値の逐語確認 (CLAUDE.md「数値予測の逐語確認」)

`entropy_le_log_card` の結論は逐語 `entropy μ X ≤ Real.log ↑(Fintype.card α)` (`#check` 出力)。
⟹ `ε_m := ν {q | m ≤ q.1} * ENNReal.ofReal (Real.log (Fintype.card β₂))`。
`m = 0` で `ε₀ = ofReal (log |β₂|)` (**0 ではない**)。`|β₂| = 1` なら全 `m` で `ε_m = 0`
(`Real.log 1 = 0`) で、実際 `Y₂` が定数なので `b = b_m = 0` と整合。

---

## Q2 資産表 (obligation 1–9)

**凡例**: ✅ 既存 (そのまま使える) / 🔧 既存部品の合成 (行数は probe 実測) / ❌ 不在。

### 1. 条件付き MI の連鎖律 — ✅ **既存、逐語一致**

| 宣言 | 逐語署名 | file:line |
|---|---|---|
| `condMutualInfo_chain_rule_X_2var` | `theorem condMutualInfo_chain_rule_X_2var {Ω : Type*} [MeasurableSpace Ω] {X X' Y W : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X'] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] [MeasurableSpace W] (μ : Measure Ω) [IsProbabilityMeasure μ] (X_RV : Ω → X) (X'_RV : Ω → X') (Yo : Ω → Y) (Wc : Ω → W) (hX : Measurable X_RV) (hX' : Measurable X'_RV) (hYo : Measurable Yo) (hWc : Measurable Wc) (hWcY_fin : Shannon.mutualInfo μ Wc Yo ≠ ∞) : Shannon.condMutualInfo μ (fun ω ↦ (X_RV ω, X'_RV ω)) Yo Wc = Shannon.condMutualInfo μ X_RV Yo Wc + Shannon.condMutualInfo μ X'_RV Yo (fun ω ↦ (Wc ω, X_RV ω))` (`omit [StandardBorelSpace W] [Nonempty W]`) | `ChannelCoding/ConverseMemorylessChainRule.lean:164` |
| Y 軸版 (S6 用) | `condMutualInfo_chain_rule_Y_2var … : condMutualInfo μ X_RV (fun ω ↦ (A ω, B ω)) Wc = condMutualInfo μ X_RV A Wc + condMutualInfo μ X_RV B (fun ω ↦ (Wc ω, A ω))`、`(hWcX_fin : mutualInfo μ Wc X_RV ≠ ∞)` | 同 `:243` |

⚠ **namespace は `InformationTheory.Shannon.ChannelCodingConverseGeneral`** (`Shannon` ではない)。
`open` が 1 行要る。ブリーフの「同値な形を探す」は不要 — **要求した形そのもの**が在る。

### 2. 条件付き MI の消滅 — ✅ 既存

`theorem condMutualInfo_eq_zero_of_markov (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (hXs : Measurable Xs) (_hZc : Measurable Zc) (hYo : Measurable Yo) (hmarkov : IsMarkovChain μ Xs Zc Yo) : condMutualInfo μ Xs Yo Zc = 0`
— `Shannon/CondMutualInfo.lean:339` (`@[entry_point]`)。

供給元 2 本: `IsUVChannelLaw.isMarkovChain_U_X_Y₁` (`OuterBoundUV/Region.lean:305`) と、
第 1 変数に後処理を載せる `isMarkovChain_map_left`
(`CondMutualInfo.lean:570`、逐語 `theorem isMarkovChain_map_left {X' : Type*} [MeasurableSpace X'] [StandardBorelSpace X'] [Nonempty X'] (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (hXs hZc hYo) {f : X → X'} (hf : Measurable f) (hmarkov : IsMarkovChain μ Xs Zc Yo) : IsMarkovChain μ (fun ω ↦ f (Xs ω)) Zc Yo`)。
`f := fun u ↦ (qm m u, u)` を渡すと `(U_m,U) → X → Y₁` が出て `I(U;Y₁∣(X,U_m)) = 0` に落ちる。

### 3. 「変数の関数を足しても不変」 — ✅ 既存 (3 形すべて)

| 用途 | 宣言 | file:line |
|---|---|---|
| `I(U;Y) = I((f U, U);Y)` | `lemma mutualInfo_eq_of_leftInverse {Ω γ A B : Type*} [MeasurableSpace Ω] [MeasurableSpace γ] [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → A) (Yo : Ω → γ) (hU hYo) {f : A → B} {g : B → A} (hf : Measurable f) (hg : Measurable g) (hgf : ∀ a, g (f a) = a) : mutualInfo μ (fun ω ↦ f (U ω)) Yo = mutualInfo μ U Yo` | `Shannon/CondMutualInfoMixture.lean:40` |
| `I(X;Y∣U) = I(X;Y∣(f U, U))` | `lemma condMutualInfo_eq_of_leftInverse_cond … (Xs : Ω → A) (Yo : Ω → B) (Zc : Ω → C) (hXs hYo hZc) {f : C → C'} {g : C' → C} (hf hg) (hgf : ∀ c, g (f c) = c) (hfin : mutualInfo μ Zc Yo ≠ ∞) : condMutualInfo μ Xs Yo (fun ω ↦ f (Zc ω)) = condMutualInfo μ Xs Yo Zc`。型クラスは `[MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [MeasurableSpace C] [MeasurableSpace C']` + `[IsProbabilityMeasure μ]` | 同 `:66` |
| 対の順序入替 (第 1 引数 / 条件付け) | `condMutualInfo_map_left_measurableEquiv (… ) (e : X ≃ᵐ X') : condMutualInfo μ (fun ω ↦ e (Xs ω)) Yo Zc = condMutualInfo μ Xs Yo Zc` / `condMutualInfo_map_cond_measurableEquiv {Z' : Type*} [MeasurableSpace Z'] (…) (e : Z ≃ᵐ Z') : condMutualInfo μ Xs Yo (fun ω ↦ e (Zc ω)) = condMutualInfo μ Xs Yo Zc` | `CondMutualInfo.lean:400` / `:508` (両方 `@[entry_point]`) |
| a.e. 一致での不変 | `lemma mutualInfo_congr_ae (μ : Measure Ω) {Xs Xs' : Ω → A} (Yo : Ω → B) (h : Xs =ᵐ[μ] Xs') : mutualInfo μ Xs Yo = mutualInfo μ Xs' Yo` | `CondMutualInfoMixture.lean:57` |

### 4. `ℕ` 上の裾 → 0 — ✅ Mathlib 既存

`theorem MeasureTheory.tendsto_measure_iInter_atTop [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι → Set α} (hs : ∀ i, NullMeasurableSet (s i) μ) (hm : Antitone s) (hf : ∃ i, μ (s i) ≠ ∞) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋂ n, s n)))`
— `Mathlib/MeasureTheory/Measure/MeasureSpace.lean:672`。
`s m := {q | m ≤ q.1}`、`⋂ = ∅`、`hf` は確率測度から。probe で 14 行。

### 5. MI をエントロピーで抑える — 🔧 **既存部品の合成 (17 行)**。素の形は ❌

| 部品 | 逐語署名 | file:line |
|---|---|---|
| `.toReal` 橋 | `theorem mutualInfo_eq_entropy_sub_condEntropy (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs hYo) : (mutualInfo μ Xs Yo).toReal = entropy μ Xs - InformationTheory.MeasureFano.condEntropy μ Xs Yo` (`omit [DecidableEq X]`)。**変数束は `{X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]` と `{Y : Type*} [MeasurableSpace Y]` = 第 1 引数だけ有限** | `Shannon/Bridge.lean:545` (変数束は `:34`–`:37`) |
| 条件付きエントロピー ≥ 0 | `theorem condEntropy_nonneg {W : Type*} [Fintype W] [Nonempty W] [MeasurableSpace W] [MeasurableSingletonClass W] {Y : Type*} [MeasurableSpace Y] (μ : Measure Ω) [IsProbabilityMeasure μ] (Ws : Ω → W) (Yo : Ω → Y) : 0 ≤ …` | `Shannon/Pi.lean:95` |
| 一様上界 | `theorem entropy_le_log_card {α} [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] {Ω} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) : entropy μ X ≤ Real.log ↑(Fintype.card α)` (`omit [DecidableEq α]`) | `MaxEntropy/Basic.lean:229` (`@[entry_point]`) |
| **有限性 (片側)** | ❌ 不在。`mutualInfo_ne_top` (`MutualInfo.lean:174`) は `[Fintype X]` **と** `[Fintype Y]`、`condMutualInfo_ne_top` (`CondMutualInfo.lean:320`) は `[Fintype X] [Fintype Y] [Fintype Z]` を要求 | — |
| 有限性の出口 | `lemma isMarkovChain_comp_conditioner_right {A' Z' W' : Type*} [MeasurableSpace A'] [MeasurableSpace Z'] [MeasurableSpace W'] [StandardBorelSpace A'] [Nonempty A'] [StandardBorelSpace W'] [Nonempty W'] (μ : Measure Ω) [IsProbabilityMeasure μ] (As : Ω → A') (Zc : Ω → Z') {f : Z' → W'} (hAs hZc hf) : IsMarkovChain μ As Zc (fun ω ↦ f (Zc ω))` を `f := id` で + `mutualInfo_le_of_markov` (`CondMutualInfo.lean:356`) | `CondEntropyMemoryless.lean:371` (`@[entry_point]`) |

⟹ 自作すべきは **`mutualInfo_ne_top_of_right` (5 行) + `mutualInfo_le_ofReal_log_card` (17 行)** の 2 本。
両方 probe 通過。**`uvInfoSum₂ ν ≠ ∞` (10 行) も同じ 2 本から出る** (probe `ProbeS5Finite`)。

### 6. `ν` を `(ν.map U_m) ⊗ₘ κ` に開く — ✅ 既存

| 宣言 | 逐語署名 | file:line |
|---|---|---|
| 分解 | `lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) : (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)`。変数束は `{α β Ω F : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [NormedAddCommGroup F] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ] {X : α → β} {Y : α → Ω}` + `{mβ : MeasurableSpace β}` | `Mathlib/Probability/Kernel/CondDistrib.lean:82` (変数束 `:54`/`:71`) |
| スライスの MI 分解 | `lemma condMutualInfo_compProd_fst_eq_lintegral [Countable T] [MeasurableSingletonClass T] (μ : Measure T) [IsProbabilityMeasure μ] (κ : Kernel T S) [IsMarkovKernel κ] {f : S → A} {g : S → B} (hf : Measurable f) (hg : Measurable g) : condMutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) Prod.fst = ∫⁻ t, mutualInfo (κ t) f g ∂μ`。型クラスは `[MeasurableSpace T] [MeasurableSpace S] [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]` | `Shannon/CondMutualInfoMixture.lean:102` |
| **S5 で実際に効く方** | `lemma mutualInfo_compProd_eq_add_lintegral [Countable T] [MeasurableSingletonClass T] (μ) [IsProbabilityMeasure μ] (κ) [IsMarkovKernel κ] {f g} (hf hg) {tag : A → T} (htag : Measurable tag) (hrec : ∀ᵐ p ∂(μ ⊗ₘ κ), tag (f p.2) = p.1) : mutualInfo (μ ⊗ₘ κ) (fun p ↦ f p.2) (fun p ↦ g p.2) = mutualInfo (μ ⊗ₘ κ) Prod.fst (fun p ↦ g p.2) + ∫⁻ t, mutualInfo (κ t) f g ∂μ` | 同 `:142` |
| fiber 性への変換 | `lemma ae_ae_of_ae_compProd [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop} (h : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) : ∀ᵐ a ∂μ, ∀ᵐ b ∂κ a, p (a, b)` | `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean:118` |
| 押し出しの transport | `lemma mutualInfo_map_comp (μ : Measure Ω) (T : Ω → Ω') (hT) (f : Ω' → A) (hf) (g : Ω' → B) (hg) : mutualInfo (μ.map T) f g = mutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω))` / `condMutualInfo_map_comp` (追加で `[StandardBorelSpace A] [Nonempty A] [StandardBorelSpace B] [Nonempty B] [IsProbabilityMeasure μ]`) | `ChannelCoding/CodeToAmbient.lean:435` / `:465` |

⚠ **`tag := qm m` が `hrec` をタダで満たす** — `μ ⊗ₘ κ` は `ν.map (fun q ↦ (qm m q.1, q))` なので
`ae_map_iff` で `rfl` に落ちる (probe `claim2_split`)。ブリーフの「連鎖律で `b - b_m = I(U;Y₂∣U_m)`」
を経由せず、**`b = b_m + ∫⁻` が 1 発で出る**。

### 7. 「条件付けの原子が 1 点なら MI が 0」 — 🔧 既存部品の合成 (8 行)

`theorem mutualInfo_eq_zero_iff_indep (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs hYo) : mutualInfo μ Xs Yo = 0 ↔ IndepFun Xs Yo μ`
(`Shannon/MutualInfo.lean:97`、`@[entry_point]`) +
`lemma ProbabilityTheory.indepFun_const_left {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsZeroOrProbabilityMeasure μ] (c : β) (X : Ω → β') : (fun _ ↦ c) ⟂ᵢ[μ] X`
(`Mathlib/Probability/Independence/Basic.lean:769`) + `mutualInfo_congr_ae`。probe 通過。

### 8. 量子化そのもの — 🔧 **写像は自作 3 行だが、外側の枠は既存**

名前検索 (`rg -ni "quantiz|truncat"`) のヒットは EPI / LZ78 / ArithmeticCoding のみで
**補助変数の有限量子化は 0 件**。loogle 側の 0-hit は §Q5 の表。**しかし外側の枠は既存**:

`def uvRelabel (e₁ : U → U') (e₂ : V → V') : U × V × α × β₁ × β₂ → U' × V' × α × β₁ × β₂ := fun q ↦ (e₁ q.1, e₂ q.2.1, q.2.2)` (`OuterBoundUV/Assembly.lean:134`、`[MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace U'] [MeasurableSpace V']`) + `measurable_uvRelabel` (`:138`) + スロット不変 4 本 `uvInfo₁_map_uvRelabel:143` / `uvInfo₂_map_uvRelabel:155` / `uvInfoSum₂_map_uvRelabel:175` / `uvInfoSum₁_map_uvRelabel:195`。逆向き (有限 → `ℕ`) の実例が `auxNatIndex` (`MartonBridge.lean:153`)。

⟹ **`uvRelabel` を再利用すること** (S5 の量子化法は `ν.map (uvRelabel (qm m) id)`)。
ただしスロット不変 4 本は `hd : ∀ v, d (e v) = v` (= 単射) を要求するので**量子化には当たらない**
(当たったら `a_m = a` になってしまう)。S5 が足すのは同じ 4 本の**不等式版 2 本**。
⚠ `uvInfoSum₂_map_uvRelabel` は `[Fintype U] [MeasurableSingletonClass U]` を要求する
(`mutualInfo_ne_top` を内部で使うため) ので `U = ℕ` には当たらない。obligation 5 の
`mutualInfo_ne_top_of_right` を入れると**この `[Fintype U]` は落とせる** (任意の整頓、§Q5)。

### 9. `IsUVChannelLaw.map_auxiliaries` — ✅ **そのまま使える (probe P1 で機械確認)**

`lemma IsUVChannelLaw.map_auxiliaries {U' V' : Type*} [MeasurableSpace U'] [MeasurableSpace V'] {W : BCChannel α β₁ β₂} [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) {f : U → U'} {g : V → V'} (hf : Measurable f) (hg : Measurable g) : IsUVChannelLaw W (ν.map fun q ↦ (f q.1, g q.2.1, q.2.2))`
— `OuterBoundUV/Region.lean:183` (`@audit:ok`)。

`f := qm m` / `g := id`、`hf := measurable_of_countable _` / `hg := measurable_id` で通る。
**単射性も `Fintype` も要求しない**ので量子化に無修正で当たる。証明本体は **1 行**。

---

## 前提が事故りやすい箇所 (key-preconditions box)

- **`mutualInfo_ne_top` / `condMutualInfo_ne_top` は全変数に `[Fintype]` を要求する**。`U = ℕ` の
  スロットには 1 本も当たらない ⟹ `mutualInfo_ne_top_of_right` を**最初に**入れる。
- **`condMutualInfo_chain_rule_X_2var` の `hWcY_fin` は条件付け側の MI** (`Wc := U_m` / `X` の
  どちらでも両側有限で OK)。一方 **`condMutualInfo_eq_of_leftInverse_cond` の `hfin` は
  `mutualInfo ν U Y₁`** = 量子化**前**の `ℕ` 側で、DPI (`isMarkovChain_U_X_Y₁`) 経由でしか出ない。
- **`compProd_map_condDistrib` は `[StandardBorelSpace Ω] [Nonempty Ω]` を 5 つ組全体に要求**。
  `ℕ × ℕ × α × β₁ × β₂` では instance chain で自動 (probe P0 で `inferInstance` 確認済)。
- **`Region.lean` の `section Transport` (Markov 鎖 3 本) は 5 型すべてに
  `[StandardBorelSpace _] [Nonempty _]` + `[IsProbabilityMeasure ν]` を要求**する。
  `map_auxiliaries` / `map_U_X_Y₁_Y₂` は要求しない (`[SFinite ν]` のみ)。
- **`condMutualInfo_chain_rule_X_2var` の namespace は
  `InformationTheory.Shannon.ChannelCodingConverseGeneral`**。`open` 忘れで「不在」に見える。
- **`bcSuperpositionRegionFullSupport` は全支持 `∀ x, 0 < pU.real {x}` を要求する**
  (`SuperpositionRegion.lean:178`)。量子化法の `U` 周辺は台に穴が空きうるので
  **S5 は全支持を作らない** — それは S7 の仕事。S5 の署名に全支持を混ぜないこと。

---

## Q3 S5 の成果物の署名案 (S6/S8 が消費する形)

### 置き場所: **新ファイル `InformationTheory/Shannon/BroadcastChannel/OuterBoundUV/Quantization.lean`**

import は次の 3 本 (**probe P6 で cycle 無しを機械確認**、`#check` 5 本が全部見えた):

```lean
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Assembly
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessChainRule
import InformationTheory.Shannon.MaxEntropy.Basic
```

- `Region.lean` に直接足すのは**不可** — `uvRelabel` は `Assembly.lean:134` にあり Region の**下流**。
- `Assembly.lean` に足すのも避ける (851 → ~1150 行)。`SuperpositionRegion.lean` は**不適** —
  `Classes` (⊃ `Achievability/`) と `MartonUnion` の下流で、S5 は達成側を 1 本も使わない。
  S8 が両方 import すればよい (Quantization は葉なので cycle なし)。
- **補助アルファベットの型は `ULift.{u_α} (Fin (m + 1))` を直書き**。
  `Marton.bcAuxAlphabet` (`MartonUnion.lean:52`) は `abbrev` = reducible な同義語なので S8 で
  型は一致する (S8 の第 1 step で `rfl` 確認)。universe は **α と同じ**に固定すること
  (`SuperpositionRegion.lean:42` の `α : Type u` と揃える。浮かせると S8 で
  `IsBCLessNoisy` の `∀ (U : Type u)` に当たらない)。

### `ε_m` の型: **`ℝ≥0∞`** (`.toReal` は S8 の最後だけ)

4 スロットが `ℝ≥0∞` で `uvRegion` が `.toReal` を取るのは領域の定義の中 (`Region.lean:363`)。
**S5 は `ℝ≥0∞` で閉じ、S8 が `ENNReal.toReal_add` で 1 回だけ降ろす**。

### 署名案 5 本

3 つの `def` (`uvQuantize` / `uvQuantizeLaw` / `uvQuantizeSlack`) は §skeleton に逐語で置いた。
消費側が使う定理は 4 本:

```lean
theorem uvQuantizeLaw_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (ℕ × ℕ × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) (m : ℕ) :
    IsUVChannelLaw W (uvQuantizeLaw ν m)

theorem uvInfo₂_le_uvQuantizeLaw (ν : Measure (ℕ × ℕ × α × β₁ × β₂))
    [IsProbabilityMeasure ν] (m : ℕ) :
    uvInfo₂ ν ≤ uvInfo₂ (uvQuantizeLaw ν m) + uvQuantizeSlack ν m

theorem uvInfoSum₂_le_uvQuantizeLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (ℕ × ℕ × α × β₁ × β₂)} [IsProbabilityMeasure ν]
    (h : IsUVChannelLaw W ν) (m : ℕ) :
    uvInfoSum₂ ν ≤ uvInfoSum₂ (uvQuantizeLaw ν m) + uvQuantizeSlack ν m

theorem tendsto_uvQuantizeSlack (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) [IsProbabilityMeasure ν] :
    Filter.Tendsto (uvQuantizeSlack ν) Filter.atTop (𝓝 0)
```

⚠ **仮説の非対称は意図的で、正しい** (probe 実測): `uvInfo₂` 側と `tendsto` 側は
`IsUVChannelLaw` も `W` も要らない (純粋な連鎖律 + 裾評価)。`uvInfoSum₂` 側だけが
`h : IsUVChannelLaw W ν` を要る — `a_m ≥ a` が Markov 鎖 `U → X → Y₁` に依存するため (§Q1-D)。
これを揃えて全部に `h` を付けると、S6 が使えない場面で無駄な前提を運ぶ。

前段在庫 §申し送りの「消費側で機械確認した結論形」との整合: `uvInfoSum₂` が足す項が
`condMutualInfo ν (·.2.2.1) (·.2.2.2.1) (·.1)` と逐語同一である点、`isMarkovChain_U_X_Y₁` が
そのまま DPI に載る点は本在庫でも再確認済 (食い違いなし)。

さらに S6/S8 が使う補助として **`uvInfoSum₂_ne_top` / `uvInfo₂_ne_top`** を public で置くこと
(`.toReal` を取る全ての段で要る。probe 実測 10 行)。

---

## Q4 probe (機械確認、すべて `lake env lean` silent)

scratchpad = `/private/tmp/claude-502/-Users-haruka-dev-lean-projects/abc83ceb-84f8-4f9f-b0e9-c9408d308cfe/scratchpad`。
`InformationTheory/` は 1 行も触っていない。

| probe | 内容 | 結果 | 実測行数 |
|---|---|---|---|
| **P0** | `StandardBorelSpace ℕ` / `StandardBorelSpace (ULift (Fin (m+1)))` / `Fintype (ULift (Fin (m+1)))` が `inferInstance` | ✅ 全部自動 | — |
| **P1** | `qm` を `IsUVChannelLaw.map_auxiliaries` に食わせて量子化後も `IsUVChannelLaw` | ✅ 本体 **1 行** | 1 |
| **P2–P5** | 連鎖律の当たり / `I(U;Y₁) ≠ ∞` を DPI で / 条件付け relabel / `I((U_m,U);Y₁∣X) = 0` | ✅ 4 本とも | 21 |
| **claim 1** | `condMutualInfo ν X Y₁ U ≤ condMutualInfo ν X Y₁ U_m` **完全証明** | ✅ | **56** |
| **claim 3** | 裾 `Tendsto (fun m ↦ ν {q \| m ≤ q.1}) atTop (𝓝 0)` **完全証明** | ✅ | 14 |
| **claim 2-a/b** | `(ν.map U_m) ⊗ₘ condDistrib id U_m ν = ν.map (fun q ↦ (U_m q, q))` (本体 **1 行**) と `b = b_m + ∫⁻ t, I_{κ t}(U;Y₂)` | ✅ | 13 |
| **claim 2-c/d** | 片側有限性 `mutualInfo_ne_top_of_right` と `mutualInfo μ Xs Yo ≤ ENNReal.ofReal (Real.log (Fintype.card B))` (`B` だけ有限) | ✅ | 22 |
| **claim 2-e/f/g** | a.s. 定数の変数は MI 0 / fiber 性 `∀ᵐ t, ∀ᵐ q ∂(κ t), qm m q.1 = t` / 頭部スライスで `U` が a.s. 定数 | ✅ | 25 |
| **finite** | `uvInfoSum₂ ν ≠ ∞` (`U = ℕ`) | ✅ | 10 |
| **P6** | 置き場所 (import 3 本) の cycle 無し + 必要な 5 宣言が可視 | ✅ | — |

**落ちた probe**: 初回に 3 件の型エラー。いずれも probe 側の書き方の問題で資産側ではないが、
1 本だけ実装時に再発するので逐語で残す —
`error: Invalid projection: Type of p.2 is not known; cannot resolve projection '1'`。
⟹ `Measure.ae_ae_of_ae_compProd` の `{p : α × β → Prop}` は暗黙なので
`(p := fun p : ULift.{u} (Fin (m + 1)) × (ℕ × ℕ × α × β₁ × β₂) ↦ …)` と**型を明示**しないと通らない。

---

## Q5 壁 / 撤退ライン / 行数

### Mathlib の壁 — **0 件** (5 leg 連続) / プロジェクト側の壁も **0 件**

`wall:` 候補なし。9 obligation すべてに機械確認済の経路がある。

| クエリ | 結果 | 影響 |
|---|---|---|
| loogle `InformationTheory.klDiv, Nat.min` | `Found 0 declarations` | 「MI = 量子化の上限」型の一般定理は Mathlib に無い。**要らない** — 裾評価で足りる |
| loogle `ℕ → Fin (_ + 1)` | `Found 4028 … Of these, 14 match` (すべて `Fin.last`/`castSucc`/`succ` 系) | 切詰め写像は Mathlib 不在。**自作 3 行**、probe 済 |
| loogle `InformationTheory.klDiv _ _ ≠ ⊤` | `klDiv_ne_top` / `klDiv_ne_top_iff` の 2 件 | 片側有限性は `klDiv` 経由でも出るが、DPI 経由 5 行の方が短い |
| `rg -ni "quantiz\|truncat"` (in-project) | 補助変数の量子化は 0 件 | 既存資産の見落としなし (§Q2-8 で `uvRelabel` は拾った) |

### L-BCO9 との距離 — **不発動の見込み**

発動条件は「S5 (有限量子化 + 裾評価) または S6 が閉じない」。**S5 側は 3 claim すべて probe で
実証**し閉塞要因は 0 件、残るのは plumbing (lintegral の指示関数評価 / 押し出しの transport /
スロット水準への包装) だけで、いずれも既存の rewrite チェーンの形。**S5 は sorry 無しで閉じられる**
(中間成果の量子化法 + 3 本の不等式は逆包含が閉じなくても単独で価値がある)。
⚠ **本在庫は S6 の判定材料を 1 件も持たない** — L-BCO9 の発動可否は S6 の時分割 (`Bool × U_m`)
側で改めて判定すること。退避が要るときの出口は親 plan どおり `bc_uv_subset_superposition` を
署名保持で `sorry` + `@residual(plan:bc-lessnoisy-converse-quantization)`。

### 行数見積り (step 内分割、**実測ベース**)

| step | 内容 | 見積り | 根拠 |
|---|---|---|---|
| **S5-0** | F-12 リネーム `IsUVChannelLaw.map_U_X_Y₁_Y₂` → `map_auxiliary_input_output` | ~2 | **direct consumer 0 decl / 0 file** (`dep_consumers.sh` 実測)。触るのは `Region.lean:251` (宣言) と `:42` (module doc) の 2 箇所のみ |
| **S5-a** | 共有の有限性 3 本 (`mutualInfo_ne_top_of_right` / `mutualInfo_le_ofReal_log_card` / `uvInfoSum₂_ne_top`) | ~45 | probe 実測 32 行 + docstring |
| **S5-b** | claim 1 `a ≤ a_m` (`ν` 上の形) | ~60 | **probe 実測 56 行** |
| **S5-c** | claim 2 裾評価 (分解 + fiber + スライス + lintegral 評価) | ~110 | 実測 38 行 + 未実測の lintegral 指示関数評価 ~50 + `ν {q\|m ≤ q.1}` との同定 ~10 |
| **S5-d** | スロット水準への包装 (`uvQuantizeLaw` の定義 / `IsUVChannelLaw` 保存 / 不等式 2 本、押し出し transport 込み) | ~50 | `uvInfo₂_map_uvRelabel` (`Assembly.lean:155`) の不等式版で雛形あり |
| **S5-e** | `uvQuantizeSlack` の定義 + claim 3 | ~20 | **probe 実測 14 行** |
| 計 | | **~287** | うち **147 行が probe 実測済** |

親 plan の `~160 行` は**約 1.8 倍に上方修正**。ただし S3 (見積 90 → 実測 41) / S4 (見積 140 → 実測 74)
の傾向どおり下振れるなら **230 行前後**に着地しうる。**帯は 230–290 行**。

**最初に切るべき**: **S5-a**。3 本とも BC 非依存の汎用補題で、S5-b / S5-c / S5-d の**すべてが前提**に
する。ここが 1 本でも欠けると ENNReal の相殺が全部詰まるので、gateway-atom として先に確定させる。

---

## 親 plan で書き換えが要る箇所 (編集は plan の担当)

1. **§Phase 5 S5 の行数 `(~160 行)` → `~280 行 (実測 147 行 + plumbing)`**。step 内分割は §Q5。
2. **§Phase 5 S5 の「部品は `entropy_le_log_card` + `condMutualInfo_compProd_fst_eq_lintegral` で
   全部既存」は 3/4 だけ正しい** — 裾評価で実際に効くのは
   `mutualInfo_compProd_eq_add_lintegral` (`:142`) の方 (`:102` ではない)。さらに
   **片側有限性 `mutualInfo_ne_top_of_right` が 3 箇所で前提**になる点が欠けている
   (`mutualInfo_ne_top` は両側 `[Fintype]` を要求)。
3. **「条件付き連鎖律は自作」相当の含意を消す** — `condMutualInfo_chain_rule_X_2var`
   (`ConverseMemorylessChainRule.lean:164`) が**要求どおりの形で既存**。前段在庫が「S5 予備」と
   していた `condMutualInfo_le_of_markov_joint` / `condMutualInfo_le_add_condMutualInfo` は
   **どちらも使わない**。
4. **§在庫 に `uvRelabel` 一族 (`Assembly.lean:134`–`:211`) の行が無い** — S5 / S6 / S7 が全部使う。
   `uvInfoSum₂_map_uvRelabel` が `[Fintype U]` を要求する制約も併記。
5. **§後続作業 F-12 に consumer 実測値** — `direct consumers 0 decl / 0 file`
   (`dep_consumers.sh`)、触るのは `Region.lean:251` と `:42` の 2 箇所。
6. **§撤退ライン L-BCO9 の判定粒度** — 「S5 または S6」の S5 側は本在庫で**不発動**が確定。
   発動判定は S6 側のみに残る (判断ログ 15「撤退ラインはどの宣言が止まるかまで降ろす」の適用)。
7. **§後続作業に 1 件追加候補** (任意): `uvInfoSum₂_map_uvRelabel` / `uvInfoSum₁_map_uvRelabel`
   の `[Fintype U]` / `[Fintype V]` は S5-a を入れると**落とせる**。数学は増えず署名が広がるだけ。

---

## 着手のための skeleton

```lean
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Assembly
import InformationTheory.Shannon.ChannelCoding.ConverseMemorylessChainRule
import InformationTheory.Shannon.MaxEntropy.Basic

/-!
# Broadcast channel — truncating the countable auxiliary of the UV outer region

(module doc の `## Main definitions` / `## Main statements` は §Q3 の 5 署名をそのまま並べる)
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon Filter
open InformationTheory.Shannon.ChannelCodingConverseGeneral
open scoped ENNReal Topology

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
variable {β₁ : Type*} [Fintype β₁] [Nonempty β₁] [MeasurableSpace β₁]
  [MeasurableSingletonClass β₁]
variable {β₂ : Type*} [Fintype β₂] [Nonempty β₂] [MeasurableSpace β₂]
  [MeasurableSingletonClass β₂]

/-- The truncating quantizer of the countable auxiliary, collapsing the tail to one letter. -/
def uvQuantize (m : ℕ) (u : ℕ) : ULift.{u_1} (Fin (m + 1)) := ULift.up ⟨min u m, by omega⟩

lemma measurable_uvQuantize (m : ℕ) : Measurable (uvQuantize.{u_1} m) := measurable_of_countable _

noncomputable def uvQuantizeLaw (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) (m : ℕ) :
    Measure (ULift.{u_1} (Fin (m + 1)) × ℕ × α × β₁ × β₂) :=
  ν.map (uvRelabel (uvQuantize m) id)

noncomputable def uvQuantizeSlack (ν : Measure (ℕ × ℕ × α × β₁ × β₂)) (m : ℕ) : ℝ≥0∞ :=
  ν {q | m ≤ q.1} * ENNReal.ofReal (Real.log (Fintype.card β₂))

theorem uvQuantizeLaw_isUVChannelLaw (W : BCChannel α β₁ β₂) [IsMarkovKernel W]
    {ν : Measure (ℕ × ℕ × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) (m : ℕ) :
    IsUVChannelLaw W (uvQuantizeLaw.{u_1} ν m) :=
  h.map_auxiliaries (measurable_uvQuantize m) measurable_id

end InformationTheory.Shannon.BroadcastChannel
```

⚠ skeleton の `sorry` は**着手用の穴であって撤退ではない** — 中身は probe 実測 5 行
(`ne_top_of_le_ne_top (mutualInfo_ne_top μ Yo Yo hYo hYo) (mutualInfo_le_of_markov μ Xs Yo Yo hXs hYo hYo (isMarkovChain_comp_conditioner_right μ Xs Yo hXs hYo measurable_id))`)。
実装時に `@residual` を付けないこと。
