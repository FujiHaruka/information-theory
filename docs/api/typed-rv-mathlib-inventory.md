# Typed RV API: 既存資産の在庫調査 (I-1 着手前)

> 教科書本文の `H(X)`, `H(X|Y)`, `I(X;Y)`, `D(X‖Y)` と一対一対応する外向き typed RV API を
> 整備する I-1 タスクの前段。**実装も計画起草もしない**。本ファイルは「いま何が既にあるか」を
> 構造化テーブルで列挙する。
>
> 採用済み設計 (ユーザー確認済み):
> - 引数形は `X : Ω → α`, `[MeasurableSpace Ω]`, `μ : Measure Ω`
> - internal 表現は変えない、bridge lemma + notation のみ追加 (opt-in)
> - 既存 callsite は migration しない

## 一行サマリ

**InformationTheory の measure-theoretic API は既に `Ω → α` 形 typed RV を引数に取って書かれている**。
すなわち `entropy`, `mutualInfo`, `condEntropy`, `condMutualInfo`, `IsMarkovChain`, `jointEntropy`,
`differentialEntropy` のうち離散 5 種は **`(μ : Measure Ω) → (Xs : Ω → α) → ...`** の形で
publish 済み。typed RV 形 API を新規に「定義する」必要は実質ない。**I-1 の実体は (a)
notation 宣言 + (b) ごく薄い alias 1〜2 個 + (c) 引数順揺れの確認** であり、bridge lemma の
新規追加もほぼゼロ近辺と見込まれる。

**乖離の度合いを定量的に**:

- entropy / mutualInfo / klDiv / condEntropy / condMutualInfo は **そのまま `H(X)` `I(X;Y)`
  の notation を被せられる**。引数順は **全て `μ` 先、RV 後**で統一されており、揺れなし。
- 一方 `differentialEntropy` だけは `(μ : Measure ℝ)` 引数で typed RV (`Ω → ℝ`) を取らない。
  ここだけ typed RV 形 alias を 1 本書く必要がある (`differentialEntropy μ X := DifferentialEntropy
  (μ.map X)` 的)。
- Mathlib 側は **typed RV 形の `H` / `I` / `D` を一切持たない**。`klDiv` のみ。`H` / `I` の
  ベース定義は InformationTheory だけが持つ (Mathlib に未上流)。
- Mathlib `IdentDistrib` は **typed RV 形そのもの** (`f : α → γ`, `g : β → γ`, `μ`, `ν` を
  受けて `μ.map f = ν.map g` を表明)。これを typed RV API の参照点にできる。
- `notation` / `scoped notation` は **InformationTheory 内に 1 つもない**。Mathlib `InformationTheory/`
  にも `H[X]` / `I[X;Y]` notation は不在。よって notation 設計は完全に新規。

**主な発見 (最も影響が大きい順)**:

1. 既存 internal API は 100% typed RV 形で書かれており、bridge lemma は新規にほぼ不要。
2. `condEntropy` は **`InformationTheory.Fano.Measure` namespace** に住んでいて、`InformationTheory.Shannon`
   namespace ではない (歴史的経緯)。typed RV alias で `Shannon.condEntropy` を作るか、
   そのまま `MeasureFano.condEntropy` を notation `H( X | Y )` に bind するか、設計判断が要る。
3. `condMutualInfo` / `IsMarkovChain` は **`[StandardBorelSpace X] [Nonempty X]
   [StandardBorelSpace Y] [Nonempty Y]` を要求する**。`mutualInfo` / `entropy` は要求しない。
   notation `I(X ; Y | Z)` が型クラス制約付きである点を docstring で明示する必要がある。
4. `differentialEntropy` は `(μ : Measure ℝ)` 形で typed RV を取らない。typed RV alias を
   1 本足す必要がある (最小規模の新規 def)。
5. `InformationTheory/Shannon/Bridge.lean` の `entropy` は `private` でない module-level `def` だが、
   **`InformationTheory.Fano.Measure.condEntropy` と同名衝突しない**ことを確認済み (前者は
   `InformationTheory.Shannon.entropy`, 後者は `InformationTheory.MeasureFano.condEntropy`)。

---

## A. InformationTheory 既存 typed RV API surface

### A-1. シャノンエントロピー / 条件付きエントロピー / 結合エントロピー

| 概念 | API (InformationTheory) | file:line | 引数順 | 戻り値 | 型クラス要件 (verbatim) |
|---|---|---|---|---|---|
| `H(X)` (有限) | `entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ` | `InformationTheory/Shannon/Bridge.lean:43` | `μ → Xs` | `ℝ` | `[Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]` (`Bridge.lean:38-39` の `variable` で section-wide), `[MeasurableSpace Ω]` (`Bridge.lean:37`) |
| `H(X) ≥ 0` | `entropy_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (hXs : Measurable Xs) : 0 ≤ entropy μ Xs` | `InformationTheory/Shannon/Bridge.lean:47` | `μ → Xs` | `Prop` | 上記 + `[IsProbabilityMeasure μ]` + `Measurable Xs` |
| `H(X \| Y)` (有限 X) | `def condEntropy (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) : ℝ` | `InformationTheory/Fano/Measure.lean:68` | `μ → Xs → Yo` | `ℝ` | `[Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]` (file-level variable `:58-59`), `[MeasurableSpace Y]` (`:60`), `[MeasurableSpace Ω]` (`:57`), `[IsFiniteMeasure μ]` |
| `H(Y \| X) ≤ H(Y)` | `entropy_ge_condEntropy (μ : Measure Ω) [IsProbabilityMeasure μ] (Ws : Ω → W) (Yo : Ω → Y) (hWs : Measurable Ws) (hYo : Measurable Yo) : condEntropy μ Ws Yo ≤ entropy μ Ws` | `InformationTheory/Shannon/SlepianWolf.lean:164` | `μ → Ws → Yo` | `Prop` | `[Fintype W] [DecidableEq W] [Nonempty W] [MeasurableSpace W] [MeasurableSingletonClass W]`, `[MeasurableSpace Y]`, `[IsProbabilityMeasure μ]` |
| Chain rule `H(X,Y) = H(X) + H(Y\|X)` | `entropy_pair_eq_entropy_add_condEntropy (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) : entropy μ (fun ω => (Xs ω, Yo ω)) = entropy μ Xs + InformationTheory.MeasureFano.condEntropy μ Yo Xs` | `InformationTheory/Shannon/Entropy.lean:41` | `μ → Xs → Yo` | `Prop` | `Bridge.lean` の variable block 全て (Fintype/DecEq/Nonempty/MS/MSClass × X,Y,Z) + `[IsProbabilityMeasure μ]` |
| Tower `H(X\|Y,Z)` | `condEntropy_tower` | `InformationTheory/Shannon/Entropy.lean:144` | `μ → Xs → Yo → Zo` | `Prop` | 同上 |
| Conditioning monotonicity | `condEntropy_le_condEntropy_of_pair` | `InformationTheory/Shannon/Entropy.lean:240` | `μ → Xs → Yo → Zo` | `Prop` | 同上 |
| Joint entropy (n-var) | `def jointEntropy (μ : Measure Ω) (Xs : Fin n → Ω → α) : ℝ` | `InformationTheory/Shannon/Han.lean:42` | `μ → Xs` | `ℝ` | `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]`, `[MeasurableSpace Ω]`, `{n : ℕ}` |
| n-var chain rule | `jointEntropy_chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) : jointEntropy μ Xs = ∑ i : Fin n, InformationTheory.MeasureFano.condEntropy μ (Xs i) (fun ω (j : Fin i.val) => Xs ⟨j.val, j.isLt.trans i.isLt⟩ ω)` | `InformationTheory/Shannon/Han.lean:56` | `μ → Xs` | `Prop` | 同上 + `[IsProbabilityMeasure μ]` |

**重要な制約 (verbatim)**:

- `entropy` / `condEntropy` / `jointEntropy` は値域 `X` (or `α`) に `[Fintype X] [DecidableEq X]
  [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]` の **5 型クラスセット** を要求。
  notation 設計時にこの 5 つを束ねたエイリアスクラス (`DiscreteAlphabet X` のような) を作るか、
  そのまま要求するか、判断が要る。
- `condEntropy` は **`InformationTheory.MeasureFano` namespace** に住んでいる。Shannon 系から
  使うときも `InformationTheory.MeasureFano.condEntropy μ Xs Yo` と書く必要があり、これが
  notation 設計のときに `open` か renaming で吸収する対象。
- 引数順は **すべて `μ → Xs → Yo (→ Zo)`** で揺れなし。

### A-2. 相互情報量 / 条件付き相互情報量

| 概念 | API (InformationTheory) | file:line | 引数順 | 戻り値 | 型クラス要件 (verbatim) |
|---|---|---|---|---|---|
| `I(X;Y)` (KL 形) | `noncomputable def mutualInfo (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : ℝ≥0∞` | `InformationTheory/Shannon/MutualInfo.lean:36` | `μ → Xs → Yo` | `ℝ≥0∞` | `[MeasurableSpace Ω]`, `[MeasurableSpace X]`, `[MeasurableSpace Y]` のみ (Fintype 不要) |
| `I(X;Y) ≥ 0` | `mutualInfo_nonneg (μ : Measure Ω) (Xs : Ω → X) (Yo : Ω → Y) : 0 ≤ mutualInfo μ Xs Yo` | `InformationTheory/Shannon/MutualInfo.lean:42` | `μ → Xs → Yo` | `Prop` | 同上 |
| `I(X;Y) = I(Y;X)` | `mutualInfo_comm (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) : mutualInfo μ Xs Yo = mutualInfo μ Yo Xs` | `InformationTheory/Shannon/MutualInfo.lean:93` | `μ → Xs → Yo` | `Prop` | 上記 + `[IsFiniteMeasure μ]` |
| `I(X;Y) = 0 ↔ indep` | `mutualInfo_eq_zero_iff_indep (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) : mutualInfo μ Xs Yo = 0 ↔ IndepFun Xs Yo μ` | `InformationTheory/Shannon/MutualInfo.lean:109` | `μ → Xs → Yo` | `Prop` | 上記 + `[IsProbabilityMeasure μ]` |
| `I(X;Y) ≠ ∞` (有限) | `mutualInfo_ne_top [Fintype X] [MeasurableSingletonClass X] [Fintype Y] [MeasurableSingletonClass Y] (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) : mutualInfo μ Xs Yo ≠ ∞` | `InformationTheory/Shannon/MutualInfo.lean:192` | `μ → Xs → Yo` | `Prop` | 上記 + `[Fintype X] [MeasurableSingletonClass X] [Fintype Y] [MeasurableSingletonClass Y]` + `[IsProbabilityMeasure μ]` |
| Bridge `I = H - H(\|·)` | `mutualInfo_eq_entropy_sub_condEntropy (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) : (mutualInfo μ Xs Yo).toReal = entropy μ Xs - InformationTheory.MeasureFano.condEntropy μ Xs Yo` | `InformationTheory/Shannon/Bridge.lean:588` | `μ → Xs → Yo` | `Prop` | `Bridge.lean:37-40` の variable block (Fintype/etc on X), `[MeasurableSpace Y]`, `[IsProbabilityMeasure μ]` |
| `I(X;f∘Y) ≤ I(X;Y)` (DPI) | `mutualInfo_le_of_postprocess (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) {f : Y → Z} (hf : Measurable f) : mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo` | `InformationTheory/Shannon/DPI.lean:139` | `μ → Xs → Yo → f` | `Prop` | `DPI.lean:34-37` の variable: `[MeasurableSpace Ω/X/Y/Z]`, `[IsFiniteMeasure μ]` |
| `I(X;Y\|Z)` (compProd 形) | `noncomputable def condMutualInfo (μ : Measure Ω) [IsFiniteMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) : ℝ≥0∞` | `InformationTheory/Shannon/CondMutualInfo.lean:46` | `μ → Xs → Yo → Zc` | `ℝ≥0∞` | `[MeasurableSpace Ω/X/Y/Z]`, `[IsFiniteMeasure μ]`, `[StandardBorelSpace X] [Nonempty X]`, `[StandardBorelSpace Y] [Nonempty Y]` |
| `I(X;Y\|Z) ≥ 0` | `condMutualInfo_nonneg ... : 0 ≤ condMutualInfo μ Xs Yo Zc` | `InformationTheory/Shannon/CondMutualInfo.lean:55` | `μ → Xs → Yo → Zc` | `Prop` | 同上 |
| Chain rule `I((Z,X);Y) = I(Z;Y) + I(X;Y\|Z)` | `mutualInfo_chain_rule (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) : mutualInfo μ (fun ω => (Zc ω, Xs ω)) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` | `InformationTheory/Shannon/CondMutualInfo.lean:219` | `μ → Xs → Yo → Zc` | `Prop` | 同上 + `[IsProbabilityMeasure μ]` (`IsFiniteMeasure` を強化) |
| `I(X;Y\|Z) = I(Y;X\|Z)` | `condMutualInfo_comm ...` | `InformationTheory/Shannon/CondMutualInfo.lean:295` | `μ → Xs → Yo → Zc` | `Prop` | 同上 |
| `condMutualInfo_ne_top` (有限) | `condMutualInfo_ne_top [Fintype X] [MeasurableSingletonClass X] [Fintype Y] [MeasurableSingletonClass Y] [Fintype Z] [MeasurableSingletonClass Z] ...` | `InformationTheory/Shannon/CondMutualInfo.lean:331` | `μ → Xs → Yo → Zc` | `Prop` | 上記 + Fintype/MSClass triples + `[StandardBorelSpace X/Y] [Nonempty X/Y]` |
| 3-項橋 `I=H+H-H` | `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy (joint : Measure (α × β)) [IsProbabilityMeasure joint] : (mutualInfo joint Prod.fst Prod.snd).toReal = entropy joint Prod.fst + entropy joint Prod.snd - entropy joint id` | `InformationTheory/Shannon/MIChainRule.lean:449` | `joint → Prod.fst → Prod.snd` | `Prop` | `[Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]` × `α, β`, `[IsProbabilityMeasure joint]` |
| n-var MI chain rule (Fin n) | `mutualInfo_chain_rule_fin` | `InformationTheory/Shannon/MIChainRule.lean:117` | `μ → Xs → Yo` | `Prop` | (詳細は file 内 — `[StandardBorelSpace]` 系を含む) |

**重要な制約 (verbatim, 事故になりやすい順)**:

- `condMutualInfo` / `IsMarkovChain` / `mutualInfo_chain_rule` などは **`[StandardBorelSpace X]
  [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]`** を要求。`Fintype` だけだと不足する場面が
  あり (`MeasurableSingletonClass` から自動 derive は効くケースが多いが、`Nonempty` は別)。
- `mutualInfo_chain_rule` は `[IsProbabilityMeasure μ]` 要求、`condMutualInfo` 本体は
  `[IsFiniteMeasure μ]` 止まり。notation を被せるだけだと `nonneg` 系では `IsFiniteMeasure`
  で十分だが、chain rule を使う際は強化が要る。
- `mutualInfo_eq_entropy_sub_condEntropy` の右辺は **`InformationTheory.MeasureFano.condEntropy`**
  であり、Shannon namespace ではない。typed RV 形に notation を被せる際、左辺と右辺で
  namespace が違うことを明示する必要がある。

### A-3. 独立 / Markov chain / IdentDistrib

| 概念 | API | file:line | 引数順 | 型クラス要件 (verbatim) |
|---|---|---|---|---|
| `IndepFun X Y μ` (Mathlib) | `IndepFun {β : Type*} {β' : Type*} [mβ : MeasurableSpace β] [mβ' : MeasurableSpace β'] {α : Type*} {_ : MeasurableSpace α} (f : α → β) (g : α → β') (μ : Measure α := by volume_tac) : Prop` | `Mathlib/Probability/Independence/Basic.lean:151` (notation `⟂ᵢ[μ]`) | `f → g → μ` | `[MeasurableSpace β] [MeasurableSpace β'] [MeasurableSpace α]` |
| `IdentDistrib X Y μ ν` (Mathlib) | `structure IdentDistrib (f : α → γ) (g : β → γ) (μ : Measure α := by volume_tac) (ν : Measure β := by volume_tac) : Prop where aemeasurable_fst : AEMeasurable f μ; aemeasurable_snd : AEMeasurable g ν; map_eq : Measure.map f μ = Measure.map g ν` | `Mathlib/Probability/IdentDistrib.lean:71` | `f → g → μ → ν` | `[MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]` |
| `IsMarkovChain X→Z→Y` (γ-form) | `def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop := μ.map (fun ω => (Zc ω, Xs ω, Yo ω)) = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))` | `InformationTheory/Shannon/CondMutualInfo.lean:71` | `μ → Xs → Zc → Yo` | 上記 |
| Markov ⇒ MI 不等式 | `mutualInfo_le_of_markov (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (hXs ...) (hmarkov : IsMarkovChain μ Xs Zc Yo) : mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo` | `InformationTheory/Shannon/CondMutualInfo.lean:378` | `μ → Xs → Zc → Yo` | 同上 |

**観察**: Mathlib の `IdentDistrib` は **典型的な typed RV 形** (`f : α → γ`, `g : β → γ`,
`μ : Measure α := by volume_tac`, `ν : Measure β := by volume_tac`)。引数順は **RV 先、測度後**
(default `volume_tac`)。これは InformationTheory の **測度先、RV 後** とは逆順だが、`volume_tac`
default のため typed RV 用 notation の参照点としては不適格。InformationTheory の引数順 `μ → Xs (→ Yo)` を
維持するのが筋。

### A-4. KL ダイバージェンス (Mathlib 直)

| 概念 | API | file:line | 引数順 | 型クラス要件 (verbatim) |
|---|---|---|---|---|
| `D(μ ‖ ν)` | `noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` | `μ → ν` | `{α : Type*} {mα : MeasurableSpace α}` |
| `D ≥ 0` | (signature 上自明、`ℝ≥0∞` 値) | — | — | — |
| `D(μ‖μ) = 0` | `klDiv_self (μ : Measure α) [SigmaFinite μ] : klDiv μ μ = 0` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:78` | `μ` | `[SigmaFinite μ]` |
| `D = ∞ ↔ not (≪) ∨ not Integrable` | `klDiv_eq_top_iff : klDiv μ ν = ∞ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ` | `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:94` | `μ → ν` | — |
| KL chain rule (compProd) | `klDiv_compProd_eq_add` | `Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean:204` (推定 — `MutualInfo.lean:20` で参照) | — | — |
| Pushforward 不変 | **不在 (InformationTheory 自作)** — `klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : klDiv (μ.map e) (ν.map e) = klDiv μ ν` | `InformationTheory/Shannon/MutualInfo.lean:52` | `e → μ → ν` | `[MeasurableSpace α] [MeasurableSpace β]`, `[IsFiniteMeasure μ] [IsFiniteMeasure ν]` |
| 一般 pushforward DPI | **不在 (InformationTheory 自作)** — `klDiv_map_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β} (hf : Measurable f) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : klDiv (μ.map f) (ν.map f) ≤ klDiv μ ν` | `InformationTheory/Shannon/DPI.lean:52` | `f → μ → ν` | 同上 |

**観察**: `klDiv` は **measure pair `(μ, ν)` を直接受け、typed RV は経由しない**。教科書の
`D(X‖Y) := D(μ_X ‖ μ_Y) = D(μ.map X ‖ μ.map Y)` 形 typed alias を 1 本書く必要がある。これが
**I-1 で唯一新規に必要な def** (`klDivRV μ ν X Y` 的)。それ以外の `H`, `I`, `H(|·)`, `I(;|·)`
は既存定義に notation を被せるだけで足りる。

### A-5. 微分エントロピー / 連続変数

| 概念 | API (InformationTheory) | file:line | 引数順 | 戻り値 | 型クラス要件 (verbatim) |
|---|---|---|---|---|---|
| `h(μ)` (微分エントロピー、測度直) | `noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ` | `InformationTheory/Shannon/DifferentialEntropy.lean:42` | `μ` | `ℝ` | — (`Measure ℝ` 固定) |

**観察**: `differentialEntropy` は **typed RV `X : Ω → ℝ` を取らない**唯一の主要 API。
typed RV 形 `differentialEntropy μ X := differentialEntropy (μ.map X)` の薄い alias を 1 本
書く必要がある (新規 def の唯一の確実な候補)。

### A-6. その他 typed RV 関連 (AEP / EntropyRate / IID)

| 概念 | API (InformationTheory) | file:line | 備考 |
|---|---|---|---|
| Block joint RV | `def jointRV (Xs : ℕ → Ω → α) (n : ℕ) : Ω → (Fin n → α)` | `InformationTheory/Shannon/AEP.lean:55` | typed RV を `Fin n` 並べる helper |
| Per-symbol log-likelihood | `noncomputable def logLikelihood (μ : Measure Ω) (Xs : ℕ → Ω → α) (i : ℕ) : Ω → ℝ` | `InformationTheory/Shannon/AEP.lean:85` | typed RV 形 (Ω → ℝ) |
| Entropy of i.i.d. block | `theorem entropy_jointRV_eq_n_smul (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i)) (hindep_full : iIndepFun (fun i => Xs i) μ) (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ) (n : ℕ) : entropy μ (jointRV Xs n) = (n : ℝ) * entropy μ (Xs 0)` | `InformationTheory/Shannon/AEP.lean:527` | typed RV 形そのまま |
| Block entropy (stationary) | `noncomputable def blockEntropy (μ : Measure Ω) (p : StationaryProcess μ α) (n : ℕ) : ℝ := entropy μ (p.blockRV n)` | `InformationTheory/Shannon/EntropyRate.lean:58` | `entropy` を typed RV 形で直接呼ぶ |
| Conditional entropy tail | `noncomputable def conditionalEntropyTail (μ : Measure Ω) [IsFiniteMeasure μ] (p : StationaryProcess μ α) (n : ℕ) : ℝ := InformationTheory.MeasureFano.condEntropy μ (p.obs n) (p.blockRV n)` | `InformationTheory/Shannon/EntropyRate.lean:63` | `condEntropy` を typed RV 形で直接呼ぶ |
| i.i.d. ambient (`ℕ → α × β`) | `noncomputable def iidAmbientMeasure (p : Measure α) (W : Channel α β) : Measure (ℕ → α × β)` | `InformationTheory/Shannon/IIDProductInput.lean:48` | typed RV 用 ambient measure |
| `iidXs / iidYs` | `def iidXs : ℕ → (ℕ → α × β) → α := fun i ω => (ω i).1` | `InformationTheory/Shannon/IIDProductInput.lean:60` | 座標射影 typed RV |

**観察**: AEP / EntropyRate / IID 関連は **既に typed RV 形で書かれている**。これらは I-1 で
新規 alias を被せる対象ではなく、新 notation の客先 (callsite) になる。callsite migration は
しないと採用済み判断にあるため、これらは現状維持。

---

## B. notation 慣習の確認

### B-1. InformationTheory 内 notation

**結論: InformationTheory 内には information theory 関連の `notation` / `scoped notation` 宣言が
ゼロ件**。`rg -n "^(notation|scoped notation|prefix|infix)" InformationTheory/` の結果は空。
よって I-1 で `H(X)` / `I(X;Y)` / `H(X | Y)` / `D(X ‖ Y)` の notation を新規導入する余地は
完全にクリア (既存記法との衝突がない)。

### B-2. Mathlib `InformationTheory/` notation

**結論: 不在**。`rg -n "notation" .lake/packages/mathlib/Mathlib/InformationTheory/` で
notation 宣言なし。

### B-3. Mathlib `Probability/Independence/` notation (参考)

| notation | 意味 | file:line |
|---|---|---|
| `X ⟂ᵢ[μ] Y` | `ProbabilityTheory.IndepFun X Y μ` | `Mathlib/Probability/Independence/Basic.lean:151` (`scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" μ "] " Y:50 => ProbabilityTheory.IndepFun X Y μ`) |
| `X ⟂ᵢ Y` | `ProbabilityTheory.IndepFun X Y volume` | `Mathlib/Probability/Independence/Basic.lean:154` |
| `X ⟂ᵢ[Z, hZ; μ] Y` | `condIndepFun` 系 | `Mathlib/Probability/Independence/Conditional.lean:164` |

**観察**: Mathlib `Probability` は **`scoped[ProbabilityTheory] notation3`** + 中括弧で測度を埋め込む
慣習。本プロジェクトの notation 設計に参照点として使える (precedence 50、`scoped` 名前空間)。

### B-4. `IdentDistrib` の typed RV 書式 (Mathlib)

`structure IdentDistrib (f : α → γ) (g : β → γ) (μ : Measure α := by volume_tac) (ν : Measure β := by volume_tac) : Prop`
(`Mathlib/Probability/IdentDistrib.lean:71`).

- RV 先 (`f`, `g`)、measure 後 (`μ`, `ν`)、`volume_tac` default
- InformationTheory の measure 先・RV 後と引数順が**逆**だが、`IdentDistrib` 自体は標準的に
  `IdentDistrib (Xs i) (Xs 0) μ μ` 形で使われており (例: `AEP.lean:139`, `:174`)、callsite で
  混乱は起きていない

---

## C. Mathlib bridge lemmas (pushforward 経由)

typed RV API → measure-theoretic API への橋渡しで使える Mathlib 補題。

### C-1. `Measure.map` 関連

| API | file:line | signature (verbatim) | 用途 |
|---|---|---|---|
| `Measure.map_apply_of_aemeasurable` | `Mathlib/MeasureTheory/Measure/Map.lean:156` | `theorem map_apply_of_aemeasurable (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)` | `μ.map X {s} = μ (X ⁻¹' s)` の基本 |
| `Measure.map_apply` | `Mathlib/MeasureTheory/Measure/Map.lean:160` | `theorem map_apply (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)` | 上記の Measurable 版 |
| `Measure.map_map` | `Mathlib/MeasureTheory/Measure/Map.lean` (検索ヒット) | `(μ.map f).map g = μ.map (g ∘ f)` (`Measurable` 仮定下) | RV の合成 (typed RV bridge での `e ∘ X` で頻出) |
| `Measure.isProbabilityMeasure_map` | `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:123` | `theorem Measure.isProbabilityMeasure_map {f : α → β} (hf : AEMeasurable f μ) : IsProbabilityMeasure (map f μ)` | `IsProbabilityMeasure μ → IsProbabilityMeasure (μ.map X)` |
| `Measure.isProbabilityMeasure_map_iff` | `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:134` | `theorem Measure.isProbabilityMeasure_map_iff {μ : Measure α} {f : α → β} (hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) ↔ IsProbabilityMeasure μ` | 逆方向 |

### C-2. 積分の pushforward

| API | file:line | signature (verbatim) | 用途 |
|---|---|---|---|
| `MeasureTheory.integral_map` | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1089` | `theorem integral_map {β} [MeasurableSpace β] {φ : α → β} (hφ : AEMeasurable φ μ) {f : β → G} (hfm : AEStronglyMeasurable f (Measure.map φ μ)) : ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ` | typed RV 形 `∫ f(X(ω)) dμ = ∫ y, f y d(μ.map X)` |
| `MeasureTheory.lintegral_map` | `Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean:27` | `theorem lintegral_map {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ` | ENNReal 版 |
| `MeasureTheory.lintegral_map_equiv` | `Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean:96` | `theorem lintegral_map_equiv (f : β → ℝ≥0∞) (g : α ≃ᵐ β) : ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, f (g a) ∂μ` | MeasurableEquiv 版 (前提弱) |
| `Integrable.comp_aemeasurable` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:361` | `theorem Integrable.comp_aemeasurable {f : α → α'} {g : α' → ε} (hg : Integrable g (Measure.map f μ)) (hf : AEMeasurable f μ) : Integrable (g ∘ f) μ` | typed RV bridge での integrability 移送 |
| `Integrable.comp_measurable` | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:365` | `theorem Integrable.comp_measurable {f : α → α'} {g : α' → ε} (hg : Integrable g (Measure.map f μ)) (hf : Measurable f) : Integrable (g ∘ f) μ` | Measurable 版 |

### C-3. `condDistrib` (条件分布; `condEntropy` の中枢)

| API | file:line | signature (verbatim) | 用途 |
|---|---|---|---|
| `condDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean:64` | `noncomputable irreducible_def condDistrib {_ : MeasurableSpace α} [MeasurableSpace β] (Y : α → Ω) (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : Kernel β Ω := (μ.map fun a => (X a, Y a)).condKernel` | typed RV pair から条件分布 kernel (引数順 RV 先、measure 後、Mathlib 慣習) |
| `compProd_map_condDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean:82` | `lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) : (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)` | 核分離公式 (typed RV bridge での主役) |
| `IsMarkovKernel (condDistrib Y X μ)` | `Mathlib/Probability/Kernel/CondDistrib.lean:68` | `instance [MeasurableSpace β] : IsMarkovKernel (condDistrib Y X μ)` | 各 fibre が確率測度 |
| `condDistrib_apply_of_ne_zero` | `Mathlib/Probability/Kernel/CondDistrib.lean:75` | `lemma condDistrib_apply_of_ne_zero [MeasurableSingletonClass β] (hY : Measurable Y) (x : β) (hX : μ.map X {x} ≠ 0) (s : Set Ω) : condDistrib Y X μ x s = (μ.map X {x})⁻¹ * μ.map (fun a => (X a, Y a)) ({x} ×ˢ s)` | 離散条件下での点値 |

**重要な制約 (verbatim)**:

- `condDistrib (Y : α → Ω) (X : α → β) (μ : Measure α) [IsFiniteMeasure μ] : Kernel β Ω`
- **`Y` (取り出す側) と `X` (条件側) の引数順**は Mathlib 流に **`Y → X → μ`**。InformationTheory の
  `condEntropy μ Xs Yo`、`mutualInfo μ Xs Yo` とは **意味的に逆**: InformationTheory の `condEntropy μ Xs Yo`
  は `H(Xs | Yo)` だが、Mathlib `condDistrib Xs Yo μ` が「`Yo` 条件下の `Xs` の分布」。
- 既存 InformationTheory コードは **正しくこの順序で使っている** (例: `InformationTheory/Fano/Measure.lean:70`
  で `condDistrib Xs Yo μ y` = `Y=y` 条件下の `Xs` の分布)。引数順は混乱しやすいが規約として
  固まっている。

### C-4. KL の typed 形 lemma (もし存在すれば)

**結論: Mathlib 側に typed RV 形 `klDiv (μ.map X) (μ.map Y)` の専用 lemma は不在**。`klDiv` は
あくまで `Measure → Measure → ℝ≥0∞` であり、pushforward の bridge は InformationTheory 自作の
`klDiv_map_measurableEquiv` (`MutualInfo.lean:52`) と `klDiv_map_le` (`DPI.lean:52`) で
代用している。typed RV 形 KL の notation `D(X ‖ Y) := klDiv (μ.map X) (μ_X) (μ_Y_via_Y)` 的な
定義を作る場合、これら自作 bridge を経由する。

---

## D. 主要前提条件ボックス (notation 設計時に事故になりやすい lemma の前提)

- **`condDistrib` の引数順は `(Y, X, μ)` で `H(Y | X)` を意味する** (Mathlib)。InformationTheory の
  `condEntropy μ Xs Yo` = `H(Xs | Yo)` で `condDistrib Xs Yo μ` を内部で呼ぶ。
  typed RV notation `H(X | Y)` をどちらの順序で展開するか、設計判断が要る。InformationTheory の
  既存 callsite (`Fano/Measure.lean`, `Shannon/Entropy.lean` 等) は `condEntropy μ Xs Yo` を
  「`Xs` を条件 `Yo` のもとで」と読んでいる。
- **`condMutualInfo` / `IsMarkovChain` / `mutualInfo_chain_rule` は `[StandardBorelSpace X]
  [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]`** を要求。離散 (`[Fintype X]
  [MeasurableSingletonClass X]`) の場合は自動 derive されるが、`Nonempty` は別に明示が要る。
- **`mutualInfo_chain_rule` / `mutualInfo_le_of_markov` / `condMutualInfo_ne_top` は
  `[IsProbabilityMeasure μ]`** を要求 (`IsFiniteMeasure` ではない)。本体 def は `IsFiniteMeasure`
  なので、notation を被せる際は仕様差を docstring で明示。
- **`entropy` / `condEntropy` / `jointEntropy` は値域に `[Fintype X] [DecidableEq X] [Nonempty X]
  [MeasurableSpace X] [MeasurableSingletonClass X]`** の 5 型クラスセット要求。typed RV notation
  `H(X)` を展開した瞬間にこの 5 つが要求される。
- **`klDiv` は値域に型クラス要求なし** だが、`klDiv μ ν = ∞` ↔ `not (μ ≪ ν) ∨ not Integrable
  (llr μ ν) μ` で、有限性は `[IsFiniteMeasure μ]` `[IsFiniteMeasure ν]` 等で別途確保しないと
  落ちる場面が多い (例: `klDiv_self` は `[SigmaFinite μ]` 要求)。
- **`condEntropy` は `InformationTheory.MeasureFano` namespace**, **`entropy` / `mutualInfo` /
  `condMutualInfo` は `InformationTheory.Shannon` namespace**。typed RV notation を `open`
  ベースで設計する際、両 namespace を `open` するか、または明示 prefix 付き notation を選ぶ
  必要がある。

---

## E. 「乖離の度合い」定量評価

I-1 で「typed RV 形」として publish したい外向き API のうち、**現状の InformationTheory が typed RV
形でそのまま提供しているもの**を分母とした既存率:

- **離散 `H(X)`** → ✅ `entropy μ Xs` 既存 (Bridge.lean:43)
- **離散 `H(X | Y)`** → ✅ `MeasureFano.condEntropy μ Xs Yo` 既存 (Fano/Measure.lean:68)
- **離散 `H(X₁, ..., Xₙ)`** → ✅ `jointEntropy μ Xs` 既存 (Han.lean:42)
- **`I(X ; Y)`** → ✅ `mutualInfo μ Xs Yo` 既存 (MutualInfo.lean:36)
- **`I(X ; Y | Z)`** → ✅ `condMutualInfo μ Xs Yo Zc` 既存 (CondMutualInfo.lean:46)
- **`X → Z → Y` Markov 述語** → ✅ `IsMarkovChain μ Xs Zc Yo` 既存 (CondMutualInfo.lean:71)
- **`D(X ‖ Y)`** → ❌ **不在**。Mathlib `klDiv μ ν` は measure pair 形のみ。typed alias を
  1 本書く必要 (`klDivRV μ ν X Y := klDiv (μ.map X) (ν.map Y)` 的)
- **微分エントロピー `h(X)`** → ⚠ `differentialEntropy μ_on_ℝ` のみ。typed RV `X : Ω → ℝ` を
  取る alias 1 本必要 (`differentialEntropy μ X := differentialEntropy (μ.map X)`)
- **`IdentDistrib X Y μ ν`** → ✅ Mathlib 直で typed RV 形 (`Mathlib/Probability/IdentDistrib.lean:71`)
- **`IndepFun X Y μ`** → ✅ Mathlib 直 (`Mathlib/Probability/Independence/Basic.lean`)
- **notation `H(X)` / `I(X;Y)` / `D(X‖Y)`** → ❌ **完全不在** (InformationTheory・Mathlib ともに)

**既存率**: 9 / 11 ≒ 82%。**新規必要分** は (a) `D(X‖Y)` typed alias 1 本、(b) `differentialEntropy
μ X` typed alias 1 本、(c) notation 一式 (5〜8 行)。bridge lemma の新規追加はゼロ件で済む見込み
(既存の `Measure.isProbabilityMeasure_map`, `compProd_map_condDistrib`, `MeasureTheory.integral_map`,
InformationTheory の `klDiv_map_measurableEquiv` で全部足りる)。

---

## F. 自作が必要な要素 (I-1 で書く対象、優先順位順)

1. **notation 設計と宣言** (5〜8 行)
   - `H(X)` / `H(X | Y)` / `I(X ; Y)` / `I(X ; Y | Z)` / `D(X ‖ Y)`
   - 推奨: `scoped[InformationTheory.Shannon] notation3 ...` (Mathlib 慣習)
   - 落とし穴: `H` / `I` / `D` は Mathlib・stdlib で衝突しやすい名前 (一文字 + `(` だが、
     既存 `H` 識別子は無いか確認が必要 — 確認は I-1 計画起草時)
   - precedence は Mathlib `IndepFun` の `notation3 X:50 " ⟂ᵢ[" μ "] " Y:50` に倣う

2. **`klDivRV` typed alias** (3〜5 行)
   - `noncomputable def klDivRV (μ : Measure Ω) (ν : Measure Ω') (X : Ω → α) (Y : Ω' → α) : ℝ≥0∞
     := klDiv (μ.map X) (ν.map Y)`
   - 落とし穴: 引数 `(μ, ν, X, Y)` の 4 つを揃えるか、`μ` 共通 (`klDivRV μ X Y := klDiv (μ.map X)
     (μ.map Y)`) 形にするか、設計判断が要る。教科書 `D(X‖Y)` は通常後者だが、`IdentDistrib` のような
     2 測度形を採るなら前者。

3. **`differentialEntropyRV` typed alias** (3 行)
   - `noncomputable def differentialEntropyRV (μ : Measure Ω) (X : Ω → ℝ) : ℝ := differentialEntropy
     (μ.map X)`

4. **同名衝突の確認**
   - `Shannon.entropy` / `Shannon.mutualInfo` / `MeasureFano.condEntropy` の 3 namespace に分散して
     いるため、notation を `open InformationTheory.Shannon` だけで全部触れるよう **`Shannon.condEntropy
     := MeasureFano.condEntropy` re-export** を書くか、notation 側で fully-qualified 名を使うか。

5. **(任意) `Shannon.H` / `Shannon.I` / `Shannon.D` の type-stable abbrev**
   - `abbrev H (μ : Measure Ω) (X : Ω → α) := entropy μ X` のような薄い alias を notation
     展開時の elaboration ヒントに使う。落とし穴: `H` は 1 文字識別子で衝突可能性高、設計判断要。

**工数感**: notation + 2 alias + 同名衝突解消で **数 10 行・1〜2 時間** 。bridge lemma 新規ゼロ
を維持できれば本タスクの本体はこれだけで終わる。逆に「`MeasureFano.condEntropy` を `Shannon`
namespace に移動」など namespace 再編に踏み込むなら工数 1 日級に膨れる (が、ユーザー判断
「internal 表現は変えない」とは整合しない方針なので、移動はしない)。

---

## G. 撤退ラインへの距離

本タスクには上位 plan 文書がまだ存在しない (I-1 計画起草前) ので、明示の撤退ラインなし。
ただし在庫調査の結果から見て、**典型的な「想定より乖離があった」発動シナリオは見えない**:

- bridge lemma 新規追加が必要だと判明 → 該当なし (既存 bridge で十分)
- typed RV 形にすると型クラスが膨らむ → `[Fintype X]` 等は既存 def の要求と同じ
- namespace 衝突 → `MeasureFano.condEntropy` の re-export で吸収可能 (1〜2 行)
- notation precedence / 衝突 → `H` / `I` / `D` の 1 文字衝突は要確認だが、`scoped` で囲めば
  影響範囲限定

**新規撤退ライン候補** (I-1 計画起草時に採用判断):

- **notation `H(X)` / `I(X;Y)` が `Std` や `Mathlib` の既存 `H` / `I` 識別子と衝突**して回避
  困難な場合 → notation を `Hₛ(X)` / `Iₛ(X;Y)` (添字付き) に縮退、または `entropy μ X` のまま
  callsite で呼ぶ既存形を維持
- **`klDivRV` の引数設計 (1 測度 or 2 測度) で既存 callsite が割れた**場合 → 教科書形 1 測度版
  `D(X‖Y) := klDiv (μ.map X) (μ.map Y)` のみ採用、2 測度版は **publish しない**

---

## H. I-1 着手 skeleton (参考)

> **編集境界**: 本ファイルは在庫調査のみ。skeleton は計画起草 (`lean-planner`) と実装
> (`lean-implementer`) の参考用としてだけ示す。本サブエージェントは Lean ファイルを書かない。

`InformationTheory/TypedRV.lean` (仮称) の出だし:

```lean
import InformationTheory.Shannon.Bridge          -- entropy
import InformationTheory.Shannon.MutualInfo      -- mutualInfo
import InformationTheory.Shannon.CondMutualInfo  -- condMutualInfo, IsMarkovChain
import InformationTheory.Fano.Measure            -- MeasureFano.condEntropy
import InformationTheory.Shannon.DifferentialEntropy
import Mathlib.InformationTheory.KullbackLeibler.Basic

namespace InformationTheory.Shannon

open MeasureTheory ProbabilityTheory MeasureFano

-- 1. Re-export: condEntropy を Shannon namespace で触れるようにする
/-- Re-export `MeasureFano.condEntropy` into the `Shannon` namespace
    so the notation `H(X | Y)` can be resolved here. -/
abbrev condEntropy := @InformationTheory.MeasureFano.condEntropy

-- 2. KL の typed RV alias
/-- Kullback–Leibler divergence between two random variables (typed RV form). -/
noncomputable def klDivRV
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {α : Type*} [MeasurableSpace α] (X Y : Ω → α) : ℝ≥0∞ :=
  klDiv (μ.map X) (μ.map Y)

-- 3. 微分エントロピーの typed RV alias
/-- Differential entropy of a real-valued random variable. -/
noncomputable def differentialEntropyRV
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  InformationTheory.Shannon.differentialEntropy (μ.map X)

-- 4. notation (要設計判断: precedence / scope / 1 文字衝突)
-- 暫定案 (Mathlib `IndepFun` の precedence 50 に倣う):
-- scoped[InformationTheory.Shannon] notation3 "H(" X:50 ")" => entropy _ X
-- scoped[InformationTheory.Shannon] notation3 "H(" X:50 " | " Y:50 ")" => condEntropy _ X Y
-- scoped[InformationTheory.Shannon] notation3 "I(" X:50 " ; " Y:50 ")" => mutualInfo _ X Y
-- scoped[InformationTheory.Shannon] notation3 "I(" X:50 " ; " Y:50 " | " Z:50 ")" => condMutualInfo _ X Y Z
-- scoped[InformationTheory.Shannon] notation3 "D(" X:50 " ‖ " Y:50 ")" => klDivRV _ X Y
-- (実態は notation3 で μ を `_` placeholder にできるか要確認。できなければ非 notation3 で
--  μ を明示する形に降ろす)

end InformationTheory.Shannon
```

---

## I. まとめ

- 既存 InformationTheory の measure-theoretic API は **すでに 100% typed RV 形** で書かれている
- 新規必要なのは **alias 2 個 (`klDivRV`, `differentialEntropyRV`) + notation 5〜8 行 + abbrev
  re-export 1 行** = ファイル 1 本 50 行以下
- **bridge lemma の新規追加はゼロ件**。Mathlib `Measure.map_apply`, `isProbabilityMeasure_map`,
  `integral_map`, `compProd_map_condDistrib` + InformationTheory `klDiv_map_measurableEquiv` で全部足りる
- 撤退ラインは現時点で発動シナリオ不明 (在庫の側に乖離なし)
- 最大の設計判断ポイント: (a) `H` / `I` / `D` の 1 文字 notation の precedence と衝突回避、
  (b) `condEntropy` の `MeasureFano` → `Shannon` re-export 要否、(c) `D(X‖Y)` の 1 測度 vs 2 測度

---

### 関連ファイル

- `InformationTheory/Shannon/Bridge.lean` — `entropy` 定義 + `mutualInfo ↔ entropy − condEntropy` 橋
- `InformationTheory/Shannon/MutualInfo.lean` — `mutualInfo` 定義 + KL pushforward 自作補題
- `InformationTheory/Shannon/CondMutualInfo.lean` — `condMutualInfo` / `IsMarkovChain` / chain rule
- `InformationTheory/Shannon/Entropy.lean` — chain rule / tower / conditioning monotonicity
- `InformationTheory/Shannon/Han.lean` — `jointEntropy` (n-var) + chain rule
- `InformationTheory/Shannon/DifferentialEntropy.lean` — measure-form 微分エントロピー
- `InformationTheory/Fano/Measure.lean` — `MeasureFano.condEntropy` / `errorProb` (Phase 3 達成)
- `InformationTheory/Shannon/DPI.lean` — `klDiv_map_le` (自作 pushforward DPI 核)
- `InformationTheory/Shannon/AEP.lean` — typed RV と `IdentDistrib` / `iIndepFun` の合流点
- `Mathlib/Probability/IdentDistrib.lean:71` — typed RV 形 `IdentDistrib` の参照点
- `Mathlib/Probability/Kernel/CondDistrib.lean:64` — Mathlib `condDistrib` (RV 順序の参照点)
- `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` — `klDiv` (measure pair 形)
