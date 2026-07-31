# BC Phase 5 — クラス定義新設のための在庫調査

> 親計画: [`bc-general-region-plan.md`](bc-general-region-plan.md) §Phase 5 (167–189 行)。
> 本ファイルは **クラス定義に着手する前の在庫**。Lean コードは一切編集していない。
> 逐語確認に使った probe は `scratchpad/probe{1..9}.lean` (repo 外)。すべて `lake env lean` EXIT=0。

## 一行サマリ

**Phase 5 の第一歩 (3 クラスの定義) に必要な素材は 100% 既存で、Mathlib 側に穴はゼロ。ただし「等号を述べる」段は現状の署名では *全チャネルで偽* になる** — `martonRegion` が第一象限制約を持ち `bcOuterRegionUV` が持たないため、`(-1,-1)` が外界にあって内界に無い (機械確認済)。さらに **semi-deterministic は `marton_achievability` の全支持仮説 `hW` と構造的に両立しない** (機械確認済) ので、plan が第一候補に挙げたクラスは**最後に回すべき**。攻略順の推奨は **less noisy → more capable → semi-deterministic**。

---

## 0. 逐語確認の結論 (先に危険なものから)

| # | 内容 | 判定 | 根拠 |
|---|---|---|---|
| **D1** | `bcOuterRegionUV W ⊆ martonRegion pV K W` は**どの `W` でも偽**。`(-1,-1)` は外界の元 (`_nonempty` + `_isLowerSet`) だが `martonRegion` の `0 ≤ p.1` を満たさない | **機械確認 (probe2, EXIT=0)** | `Region.lean:265` / `:317` vs `Operational.lean:123` |
| **D2** | semi-deterministic BC は `marton_achievability` / `marton_region_subset_capacity` の `hW : ∀ a b, 0 < (W a).real {b}` を**必ず破る** (`Y₁` が決定的 ⟹ 到達しない出力対の質量が 0) | **機械確認 (probe9, EXIT=0)** | `Marton/Achievability.lean:767` の `hW`、反例は既存の `uvBlindChannel` (`Region.lean:346`) |
| **D3** | 内界と外界で **`.toReal` の扱いは非対称** だが、危険なのは `.toReal` ではない。内界は `ℝ` (`entropy` の差) で `⊤` が原理的に起きず、外界は `ℝ≥0∞` の `.toReal` (`⊤ ↦ 0`) | **逐語確認** | `Bridge.lean:40` (`entropy : ℝ`) / `MutualInfo.lean:36` (`mutualInfo : ℝ≥0∞`) / `Region.lean:235` |
| **D4** | 補助変数の**座標規約が内外でクロスしている**。UV は「第 1 スロット ↔ 受信機 2 / 第 2 スロット ↔ 受信機 1」、Marton は「第 1 スロット ↔ 受信機 1」 | **逐語確認** | `Bridge.lean:777`/`:782` vs `Marton/Setup.lean:244`/`:252` |
| **D5** | `martonJointDistribution` の型は `IsUVChannelLaw` の第 2 引数の型と**完全一致**する (`Measure (V₁ × V₂ × α × β₁ × β₂)`)。内外を同じ添字で並べる橋が存在しうる | **機械確認 (probe8, EXIT=0)** | `Marton/Setup.lean:57` vs `Region.lean:102` |
| **D6** | plan の「Phase 2 は Phase 3–5 の前提ではない」は Phase 5 については**成り立たない**。`bcOuterRegionUV` は union だが `martonRegion` は 1 個の四辺形なので、等号は補助変数についての union を内界側にも要求する | 構造上の帰結 (D1 と独立) | plan:97 vs `Region.lean:245` |
| **D7** | `bc_degraded_converse` / `bc_achievability` は **direct consumer 0 件**。「既存に接続」は配線を新規に作ることを意味する | **`dep_consumers.sh` 実測** | Converse.lean:571 / Achievability/Assembly.lean:1093 |
| **D8** | `[Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]` から `StandardBorelSpace X` は**自動で出る**。BC 各ファイルの明示 `[StandardBorelSpace _]` は冗長 | **機械確認 (probe1, EXIT=0)** | — |

---

## 1. 既存 BC 資産の棚卸し

### 1-a. 主語と 2 つの領域 (Phase 5 が並べる対象)

| 資産 | file:line | 逐語シグネチャ (型クラス前提を省略しない) | 結論形 / 定義本体 |
|---|---|---|---|
| `BCChannel` | `BroadcastChannel/Basic.lean:37` | `abbrev BCChannel (α β₁ β₂ : Type*) [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] := Kernel α (β₁ × β₂)` | `Kernel α (β₁ × β₂)`。**`IsMarkovKernel` は abbrev には含まれず、使用側が `[IsMarkovKernel W]` を都度書く** |
| `BroadcastCode` | `Basic.lean:44` | `structure BroadcastCode (M₁ M₂ n : ℕ) (α β₁ β₂ : Type*) [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]` | field: `encoder : Fin M₁ × Fin M₂ → (Fin n → α)` / `decoder₁ : (Fin n → β₁) → Fin M₁` / `decoder₂ : (Fin n → β₂) → Fin M₂` |
| `BCAchievable` | `Operational.lean:53` | `def BCAchievable (W : BCChannel α β₁ β₂) (R₁ R₂ : ℝ) : Prop` (section var: `{α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]`) | `∀ ε' : ℝ, 0 < ε' → ∃ N : ℕ, ∀ n, N ≤ n → ∃ (M₁ M₂ : ℕ) (_ : ⌈Real.exp ((n : ℝ) * R₁)⌉₊ ≤ M₁) (_ : ⌈Real.exp ((n : ℝ) * R₂)⌉₊ ≤ M₂) (c : BroadcastCode M₁ M₂ n α β₁ β₂), (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε'` |
| `bcCapacityRegion` | `Operational.lean:68` | `def bcCapacityRegion (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ)` | `closure {p \| BCAchievable W p.1 p.2}` |
| **`martonRegion`** | `Operational.lean:121` | `def martonRegion (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ)` — section var (`Operational.lean:109`–`:114`): `{V₁ V₂ α β₁ β₂ : Type*}` それぞれに `[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _] [MeasurableSingletonClass _]`。**`StandardBorelSpace` は無い** | `{p \| 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ InMartonRegion p.1 p.2 (martonInfo₁ pV K W) (martonInfo₂ pV K W) (martonInfoV₁V₂ pV K W)}` ← **第一象限制約あり (D1 の原因)** |
| `InMartonRegion` | `Marton/Basic.lean:40` | `structure InMartonRegion (R₁ R₂ I₁ I₂ I₁₂ : ℝ) : Prop` | `bound₁ : R₁ ≤ I₁` / `bound₂ : R₂ ≤ I₂` / `boundSum : R₁ + R₂ ≤ I₁ + I₂ - I₁₂` |
| `marton_region_subset_capacity` | `Operational.lean:149` (`@[entry_point]`) | `(pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV] (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a}) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})` | `martonRegion pV K W ⊆ bcCapacityRegion W` |
| **`IsUVChannelLaw`** | `OuterBoundUV/Region.lean:102` | `def IsUVChannelLaw (W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂)) : Prop` — file var: `{α β₁ β₂ : Type*} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]`、section var (`:84`): `{U V : Type*} [MeasurableSpace U] [MeasurableSpace V]` | `ν.map (fun q ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) = (ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) ⊗ₘ W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)` |
| **`uvRegion`** | `Region.lean:233` | `def uvRegion {U V : Type*} [MeasurableSpace U] [MeasurableSpace V] (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : Set (ℝ × ℝ)` — section var (`:225`–`:227`): `[StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [Nonempty β₁] [StandardBorelSpace β₂] [Nonempty β₂]`。**`Fintype` は無い** | `{p \| InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}` ← **符号制約なし** |
| **`bcOuterRegionUV`** | `Region.lean:245` | `def bcOuterRegionUV (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ)` (同 section var) | `closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂)) (_ : IsUVChannelLaw W (ν : Measure (ℕ × ℕ × α × β₁ × β₂))), uvRegion (ν : Measure (ℕ × ℕ × α × β₁ × β₂)))` |
| `InBCOuterRegionUV` | `OuterBoundUV.lean:735` | `structure InBCOuterRegionUV (R₁ R₂ I₁ I₂ J₂ J₁ : ℝ) : Prop` | `bound₁ : R₁ ≤ I₁` / `bound₂ : R₂ ≤ I₂` / `sumBound₂ : R₁ + R₂ ≤ J₂` / `sumBound₁ : R₁ + R₂ ≤ J₁` |
| `bcOuterRegionUV_isLowerSet` | `Region.lean:265` | `(W : BCChannel α β₁ β₂) : IsLowerSet (bcOuterRegionUV W)` | 同左 |
| `bcOuterRegionUV_nonempty` | `Region.lean:317` | `(W : BCChannel α β₁ β₂) [IsMarkovKernel W] : (bcOuterRegionUV W).Nonempty` | 証人は `(0,0)` (証明本体で `uvConstLaw` を使用) |
| `bc_capacity_subset_uv` | `OuterBoundUV/Assembly.lean:839` (`@[entry_point]`) | `(W : BCChannel α β₁ β₂) [IsMarkovKernel W]` — section var (`Assembly.lean:659`–`:661`): `[Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]` + β₁/β₂ 同様 | `bcCapacityRegion W ⊆ bcOuterRegionUV W` |
| `bcOuterRegionCoop` | `OuterBound.lean:380` | `def bcOuterRegionCoop (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ)` | `{p \| p.1 ≤ capacity (Kernel.fst W) ∧ p.2 ≤ capacity (Kernel.snd W) ∧ p.1 + p.2 ≤ capacity W}` ← **周辺チャネル `Kernel.fst W` / `Kernel.snd W` の既存用例** |

### 1-b. 情報量スロット (内外で型も座標規約も違う)

| 資産 | file:line | 逐語シグネチャ | 結論形 / 本体 |
|---|---|---|---|
| `uvInfo₁` | `OuterBoundUV/Bridge.lean:777` | `noncomputable def uvInfo₁ (ν : Measure (U × V × α × β₁ × β₂)) : ℝ≥0∞` — section var (`:770`–`:773`): `{U V : Type*} [MeasurableSpace U] [MeasurableSpace V]` + `[StandardBorelSpace α] [Nonempty α]` + β₁/β₂ 同様 | `mutualInfo ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)` = **`I(V; Y₁)` — 第 2 スロットが受信機 1** |
| `uvInfo₂` | `Bridge.lean:782` | 同上 | `mutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2)` = **`I(U; Y₂)` — 第 1 スロットが受信機 2** |
| `uvInfoSum₂` | `Bridge.lean:787` | `noncomputable def uvInfoSum₂ (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : ℝ≥0∞` | `uvInfo₂ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)` = `I(U;Y₂) + I(X;Y₁\|U)` |
| `uvInfoSum₁` | `Bridge.lean:792` | 同上 | `uvInfo₁ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1)` = `I(V;Y₁) + I(X;Y₂\|V)` |
| `martonInfo₁` | `Marton/Setup.lean:244` | `noncomputable def martonInfo₁ (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : ℝ` | `entropy (martonJointDistribution pV K W) Prod.fst + entropy (…) (fun q ↦ q.2.2.2.1) - entropy (…) (fun q ↦ (q.1, q.2.2.2.1))` = **`I(V₁; Y₁)` — 第 1 スロットが受信機 1** |
| `martonInfo₂` | `Marton/Setup.lean:252` | 同上 `: ℝ` | `entropy (…) (fun q ↦ q.2.1) + entropy (…) (fun q ↦ q.2.2.2.2) - entropy (…) (fun q ↦ (q.2.1, q.2.2.2.2))` = `I(V₂; Y₂)` |
| `martonInfoV₁V₂` | `Marton/Setup.lean:262` | 同上 `: ℝ` | `entropy (…) Prod.fst + entropy (…) (fun q ↦ q.2.1) - entropy (…) (fun q ↦ (q.1, q.2.1))` = `I(V₁; V₂)` |
| `martonJointDistribution` | `Marton/Setup.lean:57` | `noncomputable def martonJointDistribution (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : Measure (V₁ × V₂ × α × β₁ × β₂)` | `(((pV ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map MeasurableEquiv.prodAssoc).map MeasurableEquiv.prodAssoc` |
| `bcJointDistribution` | `Achievability/Setup.lean:54` | `#check` 実測: `{U α β₁ β₂ : Type*} → [MeasurableSpace U] → [MeasurableSpace α] → [MeasurableSpace β₁] → [MeasurableSpace β₂] → Measure U → Kernel U α → BCChannel α β₁ β₂ → Measure (U × α × β₁ × β₂)`。**section var (`Setup.lean:31`–`:35`) は `Fintype`/`DecidableEq`/`Nonempty`/`MeasurableSingletonClass` も宣言しているが、この def は使っていない** | `((pU ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map MeasurableEquiv.prodAssoc` |
| `bcInfo₁` / `bcInfo₂` | `Achievability/Setup.lean:111` / `:100` | `#check` 実測 (`bcInfo₁`): `{U α β₁ β₂ : Type*} → [Fintype U] → [MeasurableSpace U] → [Fintype α] → [MeasurableSpace α] → [Fintype β₁] → [MeasurableSpace β₁] → [MeasurableSpace β₂] → Measure U → Kernel U α → BCChannel α β₁ β₂ → ℝ` | `I(X;Y₁\|U)` / `I(U;Y₂)` を 4 項・3 項の `entropy` 差で。**`ℝ` 値**。`entropy` の `∑` のため `Fintype` が 3 つ入る |
| `bcInfoJoint` | `Achievability/ErrorAnalysis.lean:929` | `noncomputable def bcInfoJoint (pU) (K) (W) : ℝ` | `I((U,X); Y₁)` の 3 項 `entropy` 差 |

**D4 の帰結**: `martonJointDistribution pV K W` を素朴に `uvRegion` に食わせると `uvInfo₁` は `I(V₂;Y₁)`、`uvInfo₂` は `I(V₁;Y₂)` を読む — **教科書の対応と逆**。橋を書くときは第 1・第 2 成分を入れ替える写像 `fun q ↦ (q.2.1, q.1, q.2.2)` を挟むこと。

### 1-c. degraded 資産と「floating 形」の実体

| 資産 | file:line | 逐語シグネチャ | 結論形 |
|---|---|---|---|
| **`IsBCDegraded`** | `Achievability/Setup.lean:45` | `def IsBCDegraded (W : BCChannel α β₁ β₂) : Prop` — section var は `Setup.lean:31`–`:35` (上記) | `∃ Q : Kernel β₁ β₂, IsMarkovKernel Q ∧ ∀ a : α, W a = ((W a).map Prod.fst).bind (fun y₁ ↦ (Q y₁).map (fun y₂ ↦ (y₁, y₂)))` ← **チャネルレベルの述語 (物理的 degradedness)。3 クラス定義の直接の雛形** |
| `bcMarkovChain_UX_Y₁_Y₂` | `Achievability/Assembly.lean:939` | `(pU : Measure U) [IsProbabilityMeasure pU] (K : Kernel U α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hdeg : IsBCDegraded W)` | `IsMarkovChain (bcJointDistribution pU K W) (fun q : U × α × β₁ × β₂ ↦ (q.1, q.2.1)) (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2)` |
| `bc_degraded_infoJoint_ge` | `Achievability/Assembly.lean:965` | 同上 (`hdeg : IsBCDegraded W`) | `bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W` |
| `bc_achievability` | `Achievability/Assembly.lean:1093` | `(pU) [IsProbabilityMeasure pU] (K) [IsMarkovKernel K] (W) [IsMarkovKernel W] (hpU : ∀ u : U, 0 < pU.real {u}) (hK : ∀ (u : U) (a : α), 0 < (K u).real {a}) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) (hdeg : IsBCDegraded W) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (_hR₂ : 0 < R₂) (hR₁lt : R₁ < bcInfo₁ pU K W) (hR₂lt : R₂ < bcInfo₂ pU K W) {ε' : ℝ} (hε' : 0 < ε')` | `∃ N : ℕ, ∀ n, N ≤ n → ∃ (M₁ M₂ : ℕ) (_hM₁ …) (_hM₂ …) (c : BroadcastCode M₁ M₂ n α β₁ β₂), (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε'` — **direct consumer 0 件** |
| `bc_degraded_converse` | `Converse.lean:571` | 下記「floating 形の実体」 | `InBCCapacityRegion (Real.log (M₁:ℝ)) (Real.log (M₂:ℝ)) ((∑ i, condMutualInfo μ (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i) (fun ω ↦ (W₂ ω, fun j : Fin i.val ↦ Y₂s ⟨j.val, _⟩ ω))).toReal + …Fano) ((∑ i, mutualInfo μ (fun ω ↦ (W₂ ω, fun j : Fin i.val ↦ Y₂s ⟨j.val,_⟩ ω)) (Y₂s i)).toReal + …Fano)` — **direct consumer 0 件** |
| `marton_achievability` | `Marton/Achievability.lean:767` | `(pV) [IsProbabilityMeasure pV] (K) [IsMarkovKernel K] (W) [IsMarkovKernel W] (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a}) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) {R₁ R₂ : ℝ} (hR₁lt …) (hR₂lt …) (hRsum …) {ε' : ℝ} (hε' : 0 < ε')` | `BCAchievable` の中身と同型 |

**`bc_degraded_converse` の「floating 形」とは具体的に何か (逐語)**:

```lean
theorem bc_degraded_converse
    [NeZero M₁] [NeZero M₂]
    (μ : Measure Ω) [IsProbabilityMeasure μ]                    -- ← 与えられた ambient
    (W₁ : Ω → Fin M₁) (W₂ : Ω → Fin M₂) (Y₁s : Fin n → Ω → β₁) (Y₂s : Fin n → Ω → β₂)
    (c : BroadcastCode M₁ M₂ n α β₁ β₂)
    (hW₁ : Measurable W₁) (hW₂ : Measurable W₂)
    (hY₁s : ∀ i, Measurable (Y₁s i)) (hY₂s : ∀ i, Measurable (Y₂s i))
    (hW₁_uniform : μ.map W₁ = (Fintype.card (Fin M₁) : ℝ≥0∞)⁻¹ • Measure.count)
    (hW₂_uniform : μ.map W₂ = (Fintype.card (Fin M₂) : ℝ≥0∞)⁻¹ • Measure.count)
    (h_indep : mutualInfo μ W₁ W₂ = 0)
    (h_memo : ∀ i : Fin n, IsMarkovChain μ (fun ω ↦ (W₂ ω, (…X^{≠i}, (Y₁^{≠i}, Y₂^{≠i})))) (fun ω ↦ c.encoder (W₁ ω, W₂ ω) i) (Y₁s i))
    (h_deg_block : ∀ i : Fin n, IsMarkovChain μ (Y₁s i)
        (fun ω ↦ (W₂ ω, fun (j : Fin i.val) ↦ Y₁s ⟨j.val, j.isLt.trans i.isLt⟩ ω))
        (fun ω (j : Fin i.val) ↦ Y₂s ⟨j.val, j.isLt.trans i.isLt⟩ ω))     -- ← degradedness はここ
    (hmarkov : IsMarkovChain μ (fun ω ↦ (W₂ ω, W₁ ω)) (fun ω ↦ (W₂ ω, fun j ↦ c.encoder (W₁ ω, W₂ ω) j)) (fun ω j ↦ Y₁s j ω))
    (hcard₁ : 2 ≤ M₁) (hcard₂ : 2 ≤ M₂) : …
```

- **floating 形の 2 つの意味**: (a) ambient `μ` を**構成せず引数で受ける**、(b) 結論が `InBCCapacityRegion (log M₁) (log M₂) …` の**メッセージレベル**で、`bcCapacityRegion W ⊆ _` の集合レベルではない。
- **重要な実測**: `bc_degraded_converse` の degradedness は `IsBCDegraded W` (チャネルレベル) **ではなく** `h_deg_block` = **ambient 上の per-letter Markov 鎖**。つまり **達成側 (`IsBCDegraded`) と逆側 (`h_deg_block`) で degradedness の表現が既に食い違っている**。Phase 5 で新クラスを 1 本の述語で定義するなら、両方に降ろす補題が要る。
- **4b の橋 (S1–S4) がどう繋がるか (実測)**: `bcConverseAmbient c W` (`Bridge.lean:141`) が `μ` を供給し、`bcConverseMsg₁_uniform` (`:229`) / `bcConverseMsg₂_uniform` (`:241`) / `bcConverse_mutualInfo_eq_zero` (`:253`) が uniform + 独立を、`bcConverse_memoryless₁/₂` (`:301`/`:348`) が `h_memo` を、`bcConverse_isMarkovChain₁/₂` (`:394`/`:428`) が `hmarkov` を出す。`bc_uv_converse_from_code` (`:562`, `@[entry_point]`) がその合成。
  **ただし `h_deg_block` に対応する補題は存在しない** (`bcConverse_deg*` は 0 hit)。degraded 側に橋を効かせるには **`IsBCDegraded W` → `bcConverseAmbient` 上の `h_deg_block`** を新規に書く必要がある。これが「4b の橋が degraded 側にも効く」の実際のコスト。

### 1-d. consumer 実測 (`scripts/dep_consumers.sh`)

| target | direct consumers |
|---|---|
| `Marton.martonRegion` | **1 decl / 1 file** — `Operational.lean:139 marton_region_subset_capacity` のみ |
| `bcCapacityRegion` | 4 decl / 3 file — `bc_capacityRegion_isClosed` / `marton_region_subset_capacity` / `bc_capacity_subset_coop` / `bc_capacity_subset_uv` |
| `bcOuterRegionUV` | 10 decl / 2 file — `Assembly.lean` の `*_point_mem` 5 本 + `bc_uv_quadrant_mem_of_achievable` + `bc_capacity_subset_uv`、`Region.lean` の `_isClosed`/`_isLowerSet`/`_nonempty` |
| `IsBCDegraded` | 3 decl / 1 file — `bcMarkovChain_UX_Y₁_Y₂` / `bc_degraded_infoJoint_ge` / `bc_achievability` |
| `bc_degraded_converse` | **0 decl / 0 file** |
| `bc_achievability` | **0 decl / 0 file** |

⟹ **`martonRegion` の第一象限制約を外す修正の波及は 1 decl**。しかもその 1 decl (`marton_region_subset_capacity`) の証明は `obtain ⟨-, -, hM⟩ := hp` (`Operational.lean:157`) で **符号成分を捨てている** ので、除去は証明を壊さない。

---

## 2. 3 クラスの定義形の設計材料

### 2-a. 「project に 0 hit」の確認 (名前検索 + 結論形検索の両方)

| 検索 | コマンド / クエリ | 結果 |
|---|---|---|
| 名前 (in-repo) | `rg -n -i 'lessnoisy\|less.noisy' --glob '*.lean'` | **0 hit** |
| 名前 (in-repo) | `rg -n -i 'morecapable\|more.capable' --glob '*.lean'` | **0 hit** |
| 名前 (in-repo) | `rg -n -i 'semideterministic\|semi.deterministic' --glob '*.lean'` | **0 hit** |
| 結論形 (in-repo) | `rg -n --pcre2 -U '(?:theorem\|lemma)\s+\w+[\s\S]{0,1200}?mutualInfo[\s\S]{0,300}?≤[\s\S]{0,300}?mutualInfo' --glob '*.lean' InformationTheory/` | 40 decl がヒットするが、**チャネルについて量化した比較述語は 0**。最近縁は DPI 3 本 (下表) |
| 結論形 (in-repo) | `rg -n --pcre2 'mutualInfo\s+\S+\s+(\S+)\s+\1'` (= `I(X;X)`) | **0 hit** — `mutualInfo_self_eq_entropy` は無い (§5-3) |
| 名前 (Mathlib, loogle) | `"mutualInfo"` | `Found 0 declarations whose name contains "mutualInfo".` |
| 名前 (Mathlib, loogle) | `"Degraded"` | `Found 0 declarations whose name contains "Degraded".` |
| 名前 (Mathlib, loogle) | `"lessNoisy"` | `Found 0` |
| 名前 (Mathlib, loogle) | `"Capable"` | `Found 0` |
| 名前 (Mathlib, loogle) | `"semiDeterministic"` | `Found 0` |
| 名前 (Mathlib, loogle) | `"Blackwell"` | `Found 0` (Blackwell 順序も無い) |
| 名前 (Mathlib, loogle) | `"roadcast"` | `Found 58` — 全部 `Std.Sync.Broadcast` (並行処理)。情報理論とは無関係 |
| 結論形 (Mathlib, loogle) | `InformationTheory.klDiv _ _ ≤ InformationTheory.klDiv _ _` | `Found one declaration mentioning …. Of these, 0 match your pattern(s).` |

**判定**: plan の「project 全体で 0 hit」は**正しい**。ただし *部品* は全部ある — 特に `Kernel.fst W` / `Kernel.snd W` が `bcOuterRegionCoop` (`OuterBound.lean:381`) で既に使われている点は、plan に記載が無い**在庫の見落とし**。

### 2-b. 証明を支配することになる既存補題 (結論形は逐語)

| # | 補題 | file:line | 逐語シグネチャ | **結論形 (逐語)** |
|---|---|---|---|---|
| L1 | `mutualInfo_le_of_markov` | `Shannon/CondMutualInfo.lean:356` | `(μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo) (hmarkov : IsMarkovChain μ Xs Zc Yo)` (file var: `{Ω X Y Z : Type*}` すべて `[MeasurableSpace _]`) | `mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo` |
| L2 | `mutualInfo_le_of_postprocess` | `Shannon/DPI.lean:123` | `(μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) {f : Y → Z} (hf : Measurable f)` | `mutualInfo μ Xs (f ∘ Yo) ≤ mutualInfo μ Xs Yo` |
| L3 | `condMutualInfo_le_of_markov_joint` | `ChannelCoding/ConverseMemorylessChainRule.lean:113` (`@[entry_point]`) | `(μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (Wc : Ω → W) (hXs) (hZc) (hYo) (hWc) (hmarkov : Shannon.IsMarkovChain μ (fun ω ↦ (Wc ω, Xs ω)) (fun ω ↦ (Wc ω, Zc ω)) Yo) (hWcYo_fin : Shannon.mutualInfo μ Wc Yo ≠ ∞)` (section var `:93`–`:97`: `{X Y Z W : Type*}` すべて `[MeasurableSpace _] [StandardBorelSpace _] [Nonempty _]`) | `Shannon.condMutualInfo μ Xs Yo Wc ≤ Shannon.condMutualInfo μ Zc Yo Wc` |
| L4 | `mutualInfo_toReal_eq_entropy_form` | `MultipleAccess/Reconciliation.lean:45` | `{Ω : Type*} [MeasurableSpace Ω] {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B] [DecidableEq B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → A) (g : Ω → B) (hf : Measurable f) (hg : Measurable g)` | `(mutualInfo μ f g).toReal = entropy μ f + entropy μ g - entropy μ (fun ω ↦ (f ω, g ω))` ← **`ℝ≥0∞` 側と `ℝ` 側 (`martonInfo*`/`bcInfo*`) を繋ぐ唯一の橋** |
| L5 | `mutualInfo_ne_top` | `Shannon/MutualInfo.lean:174` | `[Fintype X] [MeasurableSingletonClass X] [Fintype Y] [MeasurableSingletonClass Y] (μ : Measure Ω) [IsProbabilityMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs) (hYo)` | `mutualInfo μ Xs Yo ≠ ∞` — **両辺に `Fintype` を要求** |
| L6 | `condMutualInfo_ne_top` | `Shannon/CondMutualInfo.lean:320` | `[Fintype X] [MeasurableSingletonClass X] [Fintype Y] [MeasurableSingletonClass Y] [Fintype Z] [MeasurableSingletonClass Z] (μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs) (Yo) (Zc) (hXs) (hYo) (hZc)` | `condMutualInfo μ Xs Yo Zc ≠ ∞` — **条件付け側 `Z` にも `Fintype` を要求** |
| L7 | `mutualInfo_eq_of_leftInverse` | `Shannon/CondMutualInfoMixture.lean:40` | `{Ω γ A B : Type*} [MeasurableSpace Ω] [MeasurableSpace γ] [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → A) (Yo : Ω → γ) (hU) (hYo) {f : A → B} {g : B → A} (hf) (hg) (hgf : ∀ a, g (f a) = a)` | `mutualInfo μ (fun ω ↦ f (U ω)) Yo = mutualInfo μ U Yo` ← 補助アルファベット付け替えの土台 |
| L8 | `IsMarkovChain` | `Shannon/CondMutualInfo.lean:82` | `def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop` | `μ.map (fun ω ↦ (Zc ω, Xs ω, Yo ω)) = (μ.map Zc) ⊗ₘ ((condDistrib Xs Zc μ) ×ₖ (condDistrib Yo Zc μ))` |
| L9 | `mutualInfoOfChannel` | `ChannelCoding/Basic.lean:81` | `noncomputable def mutualInfoOfChannel (p : Measure α) (W : Channel α β) : ℝ≥0∞` | `klDiv (jointDistribution p W) (p.prod (outputDistribution p W))` |
| L10 | `Kernel.fst` / `Kernel.snd` (Mathlib) | `Mathlib/Probability/Kernel/Composition/MapComap.lean:409` / `:475` | `noncomputable def fst (κ : Kernel α (β × γ)) : Kernel α β := mapOfMeasurable κ Prod.fst measurable_fst` / `snd` 同様 | `Kernel α β` / `Kernel α γ`。**`instance IsMarkovKernel.fst` (`:431`) / `IsMarkovKernel.snd` (`:493`) があり instance 解決が自動** |
| L11 | `Measure.compProd_map` (Mathlib) | `Mathlib/Probability/Kernel/Composition/Lemmas.lean:120` | `lemma compProd_map [SFinite μ] [IsSFiniteKernel κ] {f : β → γ} (hf : Measurable f)` | `μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f)` ← チャネル語彙と結合法語彙を繋ぐ |
| L12 | `ENNReal.toReal_top` (Mathlib) | `Mathlib/Data/ENNReal/Basic.lean:277` | `@[simp] theorem toReal_top : ∞.toReal = 0 := rfl` | `∞.toReal = 0` |
| — | `Kernel.IsMarkovKernel.map` (Mathlib) | `Mathlib/.../MapComap.lean:118` | `lemma IsMarkovKernel.map (κ : Kernel α β) [IsMarkovKernel κ] (hf : Measurable f) : IsMarkovKernel (map κ f)` | **`lemma` であって `instance` ではない**。`W.map Prod.fst` を直接使うと instance 解決が失敗する (probe3 で確認)。⟹ **`Kernel.fst`/`Kernel.snd` を使うこと** |

### 2-c. 定義形の候補 (各 2 通り以上、すべて `lake env lean` で elaborate 確認済)

#### more capable — 候補 C1 (チャネル語彙) / 候補 B2 (結合法語彙)

```lean
-- C1: 周辺チャネルの相互情報量で比較 (probe4 でコンパイル確認)
def IsBCMoreCapable (W : BCChannel α β₁ β₂) : Prop :=
  ∀ p : Measure α, mutualInfoOfChannel p (Kernel.snd W) ≤ mutualInfoOfChannel p (Kernel.fst W)

-- B2: 1 個の結合法から 2 つの周辺を読む
def IsBCMoreCapable' (W : BCChannel α β₁ β₂) : Prop :=
  ∀ (p : Measure α) [IsProbabilityMeasure p],
    mutualInfo (p ⊗ₘ W) Prod.fst (fun q ↦ q.2.2) ≤ mutualInfo (p ⊗ₘ W) Prod.fst (fun q ↦ q.2.1)
```

| | 利点 | 欠点 |
|---|---|---|
| **C1** | `bcOuterRegionCoop` (`OuterBound.lean:381`) / `capacity` (`ShannonTheorem.lean:103`) と**同じ語彙**。`IsMarkovKernel.fst/snd` が instance なので前提が増えない。`capacity` 側の資産 (`exists_capacity_achiever` 等) がそのまま効く | Marton/degraded 側 (`bcJointDistribution` 上の `mutualInfo`) へ降ろすのに `Measure.compProd_map` (L11) 経由の橋が 1 本要る |
| **B2** | Marton/degraded 側の証明 (`bc_degraded_infoJoint_ge`) と同じ `mutualInfo μ f g` 形なので L1/L4 が直で効く | `capacity` 語彙と切れる。`p ⊗ₘ W` の `IsProbabilityMeasure` を毎回引き回す |

**推奨**: **C1 を定義とし、B2 を `*_iff` 補題として別に出す** (`mutualInfoOfChannel_eq_mutualInfo_prod` (`ChannelCoding/Basic.lean:92`) + L11 で ~30 行)。CLAUDE.md「Mathlib-shape-driven」の観点では、**支配する補題が `capacity` 側 (外界が簡単になる主張) なので C1 の結論形に合わせる**のが正しい。

#### less noisy — 候補 B (補助変数を型量化) / 候補 B′ (`ℕ` 固定)

```lean
-- B: 補助アルファベットを Type 0 で量化 (probe5/probe7 でコンパイル + gateway atom 確認)
def IsBCLessNoisy (W : BCChannel α β₁ β₂) : Prop :=
  ∀ (U : Type) [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U]
      [MeasurableSingletonClass U] (pU : Measure U) [IsProbabilityMeasure pU]
      (K : Kernel U α) [IsMarkovKernel K],
    mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.2)
      ≤ mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.1)

-- B′: 補助アルファベットを ℕ に固定 (bcOuterRegionUV の流儀、probe4 でコンパイル確認)
def IsBCLessNoisy' (W : BCChannel α β₁ β₂) : Prop :=
  ∀ (pU : Measure ℕ) (K : Kernel ℕ α),
    mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.2)
      ≤ mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.1)
```

| | 利点 | 欠点 |
|---|---|---|
| **B** | `bc_degraded_infoJoint_ge` / `bcMarkovChain_UX_Y₁_Y₂` に**そのまま差し込める** (gateway atom = probe5 で確認、~25 行)。教科書定義と 1:1 | 補助アルファベットが `Type 0` に固定される。`bc_degraded_infoJoint_ge` 側の `U : Type*` に当てるには `U : Type` 版の系が要る。**アルファベット `α β₁ β₂` は `Type*` のままで良い (probe6 で確認)** |
| **B′** | universe 問題ゼロ。`bcOuterRegionUV` の `ℕ` 固定と規約が揃う。**`bcJointDistribution` は `[Fintype U]` を要求しないので `U = ℕ` で型が付く** (`#check` 実測、下記) | 有限 `U` の主張に当てるたびに `mutualInfo_eq_of_leftInverse` (L7) 経由の付け替えが要る (~40 行)。`bc_degraded_infoJoint_ge` は `bcInfo₁/₂` を通すので `[Fintype U]` を要求する ⟹ B′ から直接は差し込めない |

**`#check` による逐語確認 (宣言行ではなく elaborate 結果)**:

```
@bcJointDistribution : {U α β₁ β₂ : Type*} → [MeasurableSpace U] → [MeasurableSpace α] →
  [MeasurableSpace β₁] → [MeasurableSpace β₂] →
  Measure U → Kernel U α → BCChannel α β₁ β₂ → Measure (U × α × β₁ × β₂)

@bcInfo₁ : {U α β₁ β₂ : Type*} → [Fintype U] → [MeasurableSpace U] → [Fintype α] →
  [MeasurableSpace α] → [Fintype β₁] → [MeasurableSpace β₁] → [MeasurableSpace β₂] →
  Measure U → Kernel U α → BCChannel α β₁ β₂ → ℝ
```

`Achievability/Setup.lean:31`–`:35` の section var は `[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _] [MeasurableSingletonClass _]` を宣言しているが、**`bcJointDistribution` が実際に取るのは `MeasurableSpace` だけ**、`bcInfo₁` は `entropy` の `∑` のために `Fintype U`/`Fintype α`/`Fintype β₁` を追加で取る。宣言行を読むだけでは分からない差なので、実装時も `#check` で確認すること。

**推奨**: **B**。B′ は型としては通るが、`bcInfo₁/₂` が `[Fintype U]` を要求するため `bc_degraded_infoJoint_ge` へ差し込むのに付け替え 1 段 (~40 行) が挟まる。B の universe 制約は `α β₁ β₂` には波及しない (probe6 で実測)。

**gateway atom (機械確認済, probe5)**: 定義 B から `bcInfo₁ pU K W + bcInfo₂ pU K W ≤ bcInfoJoint pU K W` (= `bc_degraded_infoJoint_ge` の結論) が、既存証明の**末尾を逐語で流用して ~25 行**で出る。差し替わるのは冒頭 4 行 (degradedness → Markov 鎖 → DPI) のみ。

**degraded ⊆ less noisy (機械確認済, probe7)**: `IsBCDegraded W → IsBCLessNoisy W` が `bcMarkovChain_UX_Y₁_Y₂` (`Assembly.lean:939`) + `isMarkovChain_map_left` + `isMarkovChain_swap` + L1 + `mutualInfo_comm` で **~25 行**。新規補助補題ゼロ。

#### semi-deterministic — 候補 D1 (kernel = dirac) / 候補 D2 (エントロピー消失)

```lean
-- D1: 受信機 1 の周辺チャネルが決定的 (probe4 でコンパイル確認)
def IsBCSemiDeterministic (W : BCChannel α β₁ β₂) : Prop :=
  ∃ f : α → β₁, ∀ a : α, Kernel.fst W a = Measure.dirac (f a)

-- D2: 条件付きエントロピーが消える形
def IsBCSemiDeterministic' (W : BCChannel α β₁ β₂) : Prop :=
  ∀ (p : Measure α) [IsProbabilityMeasure p],
    MeasureFano.condEntropy (p ⊗ₘ W) (fun q ↦ q.2.1) Prod.fst = 0
```

| | 利点 | 欠点 |
|---|---|---|
| **D1** | `IsBCDegraded` と同じ「∃ kernel + 各文字の等式」形なので既存の読み味と揃う。`Kernel.fst` は instance 完備。**反例チェックが安い** (`uvBlindChannel` で即座に確認できた) | 容量領域の記述に出てくる `H(Y₁)` / `H(Y₁\|U)` へ降ろすには「決定的写像の条件付きエントロピーは 0」という補題を自作 (§5-3) |
| **D2** | 容量領域の形 (`H(Y₁\|U)`) に近い | `MeasureFano.condEntropy` (`Fano/Measure.lean:84`) は `∫ … ∂(μ.map Yo)` 形の積分で、`Kernel` の等式より扱いにくい。`p` について量化する形は「クラス」としては冗長 (D1 から従う) |

**推奨**: **D1 を定義、D2 を系**。ただし §5 の通り semi-deterministic は攻略順で最後。

### 2-d. 「教科書の定義をそのまま転記するとどこで齟齬が出るか」(実測ベース)

1. **`ℝ≥0∞` vs `ℝ`**: 教科書は `I(U;Y₁) ≥ I(U;Y₂)` と書くが、in-project の `mutualInfo` は `ℝ≥0∞` (`MutualInfo.lean:36`)、内界の `martonInfo*`/`bcInfo*` は `ℝ` (`entropy` 差)。**`ℝ` で定義すると `.toReal` を挟むぶん `⊤` 情報が失われる**ので、クラス定義は `ℝ≥0∞` の `≤` で書き、`ℝ` へは `ENNReal.toReal_mono` + L4 で降ろすのが正しい向き (`bc_degraded_infoJoint_ge` が実際にその順序で書かれている)。
2. **条件付き版の引数順**: `condMutualInfo μ Xs Yo Zc` (`CondMutualInfo.lean:59`) は **`(対象1, 対象2, 条件)`** の順。教科書の `I(X;Y|U)` をそのまま写すと `condMutualInfo μ X Y U` で合っているが、`uvInfoSum₂` (`Bridge.lean:787`) が `condMutualInfo ν (q.2.2.1) (q.2.2.2.1) (q.1)` = `I(X;Y₁|U)` であることを毎回確認すること。
3. **`IsMarkovChain μ Xs Zc Yo` の引数順は `Xs → Zc → Yo`** で、真ん中が条件変数 (`CondMutualInfo.lean:82`)。教科書の `U → X → Y` を `IsMarkovChain μ U X Y` と書くのは正しい。ただし `mutualInfo_le_of_markov` (L1) の結論は `mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo` で**両端ではなく「始点 vs 中点」の比較**。DPI を使う向きを間違えやすい。
4. **`Kernel.map` の罠**: `W.map Prod.fst` は `IsMarkovKernel` の instance 解決に失敗する (probe3 で実測)。`Kernel.fst W` を使えば instance が付く (L10)。
5. **座標規約のクロス (D4)**: UV 側は「第 1 補助 ↔ 受信機 2」、Marton 側は「第 1 補助 ↔ 受信機 1」。クラス定義を UV に寄せるか Marton に寄せるかで補助変数の番号が入れ替わる。**`IsBCLessNoisy` は「受信機 1 の方が良い」= `I(U;Y₂) ≤ I(U;Y₁)` と書くのが degraded 側の既存資産 (`bc_degraded_infoJoint_ge`) と整合**する。

---

## 3. 教科書オブジェクトとの強度差分

### 3-a. 標準的な定義 (教科書の言葉で逐語)

| クラス | 出典 | 標準的な仮説 |
|---|---|---|
| **stochastically degraded** | Cover–Thomas §15.6.2 / El Gamal–Kim §5.1 | 「`p(y₂\|x) = Σ_{y₁} p(y₁\|x) p̃(y₂\|y₁)` なる `p̃` が存在する」— **周辺分布だけの条件**。in-project の `IsBCDegraded` (`Setup.lean:45`) は `W a = ((W a).map fst).bind …` = **physically degraded (結合法の条件)** で、こちらは strictly 強い |
| **less noisy** | Körner–Marton 1975/1977 | 「`U → X → (Y₁,Y₂)` を満たすすべての `p(u,x)` について `I(U;Y₁) ≥ I(U;Y₂)`」。`U` のアルファベットに制限なし (Carathéodory で `\|U\| ≤ \|X\|` に落とせる) |
| **more capable** | El Gamal 1979 | 「すべての `p(x)` について `I(X;Y₁) ≥ I(X;Y₂)`」。補助変数を含まない |
| **semi-deterministic** | Marton 1979 (Gelfand–Pinsker 1980 が deterministic 版) | 「`Y₁ = f(X)` が入力の決定的関数。`Y₂` は任意」 |

### 3-b. 包含関係と「弱い親戚」の危険 (**plan の対応との差分**)

```
degraded  ⊊  less noisy  ⊊  more capable
semi-deterministic  ——  上の鎖のどこにも入らない (直交)
```

- **`degraded ⊆ less noisy ⊆ more capable` は正しい**。前者は in-project で機械確認済 (probe7)。後者 (`less noisy ⊆ more capable`) は「`U = X` と取る」だけだが、**in-project では自明ではない**: `IsBCLessNoisy` (定義 B、`bcJointDistribution pU K W` 上) を `IsBCMoreCapable` (定義 C1、`mutualInfoOfChannel`) へ降ろすには L11 経由の語彙橋が要る。⟹ **3 クラスを同じ語彙で定義するか、橋を 1 本先に用意するか**の設計判断が要る。
- **semi-deterministic は鎖に入らない**。半決定的 BC は more capable とも less noisy とも限らない (`uvBlindChannel` は `Y₁` も `Y₂` も定数で両方向に degrade しうる退化例だが、一般には両立しない)。**plan/brief の「semi-deterministic はどこに位置するか」への答えは「どこにも位置しない・独立」**。

### 3-c. 既知の容量結果 (plan の主張の独立検証)

| クラス | 容量領域が既知か | 領域の形 | **plan の記述の判定** |
|---|---|---|---|
| degraded | ✅ (Bergmans/Gallager) | `R₁ ≤ I(X;Y₁\|U)`, `R₂ ≤ I(U;Y₂)` | — (既に閉じている) |
| **less noisy** | ✅ (Körner–Marton 1977) | degraded と**同じ** 2 制約 | plan「外界が UV より単純」→ **正しい**。UV の 4 制約が corner 2 本に落ちる |
| **more capable** | ✅ (El Gamal 1979) | `R₂ ≤ I(U;Y₂)`, `R₁+R₂ ≤ I(X;Y₁\|U)+I(U;Y₂)`, **`R₁+R₂ ≤ I(X;Y₁)`** の 3 制約 | plan「外界が UV より単純」→ **半分正しい**。制約は 4 → 3 に減るが、**新しい形の制約 `I(X;Y₁)` (補助変数を含まない) が入る**ので「単純化」ではなく「形が違う」。UV の `uvInfoSum₁` から `V = X` の特殊化で出せるので到達可能ではある |
| **semi-deterministic** | ✅ (Marton 1979) | `R₁ ≤ H(Y₁)`, `R₂ ≤ I(U;Y₂)`, `R₁+R₂ ≤ H(Y₁\|U)+I(U;Y₂)` | plan「Marton 内界 = 容量領域が既知」→ **文献としては正しい**。ただし §3-d の理由で **in-project では実現不能** |
| 出典の帰属 | — | — | plan「more capable / less noisy — (El Gamal 1979)」→ **less noisy は Körner–Marton (1975/1977)**。El Gamal 1979 は more capable。**帰属が 1 件誤り** |

### 3-d. 「弱い親戚」の危険 — in-project 実現時の強度差分 (CLAUDE.md textbook-object strength diff)

| # | 差分 | 影響 |
|---|---|---|
| **S1** | **`marton_achievability` は全支持 `hW : ∀ a b, 0 < (W a).real {b}` を要求する** (`Marton/Achievability.lean:767`)。semi-deterministic は定義上これを破る (**probe9 で機械確認**) | **semi-deterministic では `martonRegion pV K W ⊆ bcCapacityRegion W` が使えない**。plan が「Marton 内界 = 容量領域が既知」と書いたクラスが、内界の定理そのものを適用できないクラスになっている。攻略には `marton_achievability` から `hW` を外す (= 典型性議論の正値仮説を緩める) 大工事が要る |
| **S2** | in-project `martonRegion` は **private message のみ・(pV,K) 固定・union なし**。教科書の Marton 内界は補助アルファベットについての union (+ 共通メッセージ版は `W₀` 付き) | 等号を述べるには Phase 2 (union) が前提 (D6)。共通メッセージは Phase 5 の射程外で良い (3 クラスとも private message で容量領域が決まる) |
| **S3** | in-project `IsBCDegraded` は **physically degraded**。教科書の容量結果は stochastically degraded に対して成り立つ (容量領域は周辺分布にしか依らないので同じ) | 新クラスを `IsBCDegraded` の一般化として作る場合、**less noisy は結合法ではなく周辺分布の条件**なので、`IsBCDegraded → IsBCLessNoisy` は「強い前提から弱い結論」で問題ないが、逆向きの特殊化 (`IsBCLessNoisy` を degraded に戻す) は成立しない。plan の「degraded を新クラスの特殊化として接続」は **一方向 (degraded ⟹ 新クラス) にのみ意味がある** |
| **S4** | 半決定的容量領域の `H(Y₁)` は `martonRegion` では `I(V₁;Y₁)` (V₁ = Y₁ と取る) として現れる ⟹ **`I(X;X) = H(X)` が要る**。`rg` で in-repo 0 hit、Mathlib も `mutualInfo` 自体が 0 hit | §5-3 の自作項目 |

---

## 4. `.toReal` 非対称性の逐語確認 (plan 179–187 行の必須チェック)

### 4-a. 外界: 4 制約すべてが `.toReal` を通る (逐語)

`Region.lean:233`–`:236`:

```lean
def uvRegion {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : Set (ℝ × ℝ) :=
  {p | InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal
    (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}
```

`InBCOuterRegionUV R₁ R₂ I₁ I₂ J₂ J₁` の 4 field (`OuterBoundUV.lean:737`–`:743`) がそれぞれ `R₁ ≤ I₁` / `R₂ ≤ I₂` / `R₁ + R₂ ≤ J₂` / `R₁ + R₂ ≤ J₁` なので、**4 制約とも右辺が `.toReal`**。`⊤` のとき `ENNReal.toReal_top : ∞.toReal = 0` (`Mathlib/Data/ENNReal/Basic.lean:277`、`rfl`) により制約は `≤ 0` に強化される — plan の記述は**逐語で正しい**。

### 4-b. 内界: `.toReal` を**通らない** (plan の想定と違う)

`martonRegion` (`Operational.lean:121`) は `martonInfo₁/₂/V₁V₂ : ℝ` を直接使う。これらは `entropy` (`Bridge.lean:40`: `noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ := ∑ x : X, Real.negMulLog ((μ.map Xs).real {x})`) の**有限和の差**なので、`Fintype` 前提の下で常に有限実数。**`⊤` も `.toReal` も登場しない**。

⟹ **内外は非対称**。ただし非対称の中身は plan の想定 (「内界も `.toReal` を通しているか?」) とは異なり、**内界はそもそも `ℝ≥0∞` を経由していない**。橋は L4 (`mutualInfo_toReal_eq_entropy_form`) 1 本しかない。

### 4-c. `⊤` が実際に起きるか (`BCChannel` の型クラス前提を実測して判定)

| 対象 | 型クラス前提 (実測) | `⊤` の可能性 |
|---|---|---|
| `bc_capacity_subset_uv` (headline) | `Assembly.lean:659`–`:661`: `[Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]` + β₁/β₂ 同様 | 使う法はすべて有限補助 `Fin n × Fin M₂ × (Fin n → β₁) × (Fin n → β₂)` からの relabel なので L5/L6 が効く。**起きない** |
| `bcOuterRegionUV` (定義) | `Region.lean:225`–`:227`: `[StandardBorelSpace α] [Nonempty α]` + β₁/β₂ 同様。**`Fintype` なし**、補助は `ℕ` 固定 | `uvInfo₁ ν = mutualInfo ν (V:ℕ) (Y₁:β₁)` に **L5 は適用できない** (`Fintype ℕ` が無い)。`uvInfoSum₂` の条件付け側も `ℕ` なので **L6 も適用できない**。数学的には `I(V;Y₁) ≤ H(Y₁) < ∞` だが、**その片側有界性補題は in-repo に無い** (`rg` で確認) |
| `martonRegion` | `Operational.lean:109`–`:114`: 5 型すべて `[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _] [MeasurableSingletonClass _]` | **起きない** |

**既存実装がこの穴をどう回避しているか (実測)**: `bc_uv_mixture_point_mem` (`Assembly.lean:429`) は有限補助の法 `bcUVTimeShare c W` の上で L5 により有限性を出し、`uvRelabel` の**スロット不変性 4 本** (`uvInfo₁_map_uvRelabel` 等) で値ごと `ℕ` 側へ運んでいる。つまり **`ℕ` 上で有限性を示す必要が一度も生じない設計**になっている。

### 4-d. Phase 5 で効くかどうかの判定 — **plan の (i) は符号が逆**

| 軸 | plan の記述 | 実測に基づく判定 |
|---|---|---|
| 現状 (converse, 有限アルファベット) | 「無害」 | **正しい** |
| (i) 逆包含 (領域 ⊆ operational) | 「逆向きに効く」 | **符号が逆**。スロットが `⊤` なら `.toReal = 0` ⟹ その `uvRegion ν` は `{p \| p.1 ≤ 0 ∧ p.2 ≤ 0 ∧ …}` に**縮む**。union が縮む ⟹ 逆包含 `bcOuterRegionUV ⊆ _` は**易しくなる**。しかも非正レート対は `BCAchievable` (`bc_achievable_clamp_iff` 参照) なので実害ゼロ。**`.toReal` はここでは保護側に働く** (`ℝ≥0∞` 版に移すと逆に半平面全体が入って逆包含が偽になる) |
| (ii) `StandardBorelSpace` 側 (無限アルファベット) | 「外界が不当に狭くなって converse が偽になりうる」 | **正しい**。連続アルファベットで `I(V;Y₁) = ⊤` が起きうる法は実在し、そこで `.toReal = 0` に潰れると外界が容量領域を含まなくなる |
| **Phase 5 (3 クラスの等号)** | 記述なし | **効かない**。3 クラスとも有限アルファベット前提で扱う限り、内外どちらの側でも `⊤` は発生しない。**Phase 5 の障害は `.toReal` ではなく D1 (符号制約) と D6 (union)** |

---

## 5. 自作が要る要素 (優先順)

| # | 項目 | 推奨実装 | 規模感 | 落とし穴 |
|---|---|---|---|---|
| **5-1** | **`martonRegion` から第一象限制約を外す** (`Operational.lean:123` の `0 ≤ p.1 ∧ 0 ≤ p.2` を削除) | 定義の 1 行削除 + `marton_region_subset_capacity` の `obtain ⟨-, -, hM⟩` を `obtain hM` に | **~3 行**。consumer 実測 **1 decl / 1 file**、その 1 本は符号成分を既に捨てている | これをやらないと Phase 5 の等号が全チャネルで偽 (D1)。判断ログ 1 の「外界に符号制約を入れない」判断と**内界側で対称にする**だけ。**内界を広げる方向なので `marton_region_subset_capacity` は真のまま** (非正レートは達成可能) |
| **5-2** | **3 クラスの定義 + 包含 2 本** | `BroadcastChannel/Classes.lean` 新設 (§7 の skeleton)。`IsBCLessNoisy` (定義 B) / `IsBCMoreCapable` (定義 C1) / `IsBCSemiDeterministic` (定義 D1) + `IsBCDegraded → IsBCLessNoisy` (**probe7 で ~25 行を機械確認**) + `IsBCLessNoisy → IsBCMoreCapable` | **~150 行**。うち degraded⊆less noisy が 25 行 (確認済)、less noisy⊆more capable が語彙橋込みで ~60 行 | `IsBCLessNoisy` は補助を `Type 0` に固定する必要がある。`bc_degraded_infoJoint_ge` の `U : Type*` に当てるには `U : Type` 版の系を経由 |
| **5-3** | `mutualInfo_self_eq_entropy` : `(mutualInfo μ Xs Xs).toReal = entropy μ Xs` | L4 で `= 2·H(X) − H(X,X)`、`H(X,X) = H(X)` を `Measure.map` の対角像 + `entropy` の定義から | **~30 行** | in-repo **0 hit**、Mathlib **0 hit** (`mutualInfo` 自体が無い)。semi-deterministic の `R₁ ≤ H(Y₁)` に必須。`entropy` の `∑ x : X` は `Fintype X` を要求するので対角像の押し出しに注意 |
| **5-4** | `condEntropy μ (f ∘ Xs) Xs = 0` (決定的写像の条件付きエントロピー消失) | `MeasureFano.condEntropy` (`Fano/Measure.lean:84`) の被積分関数が `condDistrib` の Dirac になることを示す | **~40 行** | in-repo 0 hit。5-3 と併せて semi-deterministic の前提。`condDistrib` 経由なので `StandardBorelSpace` が要る |
| **5-5** | `IsUVChannelLaw W (martonJointDistribution pV K W)` + 座標入替 | `isUVChannelLaw_iff` (`Region.lean:123`) の右辺に `martonJointDistribution` の compProd 構成を当てる。座標は `fun q ↦ (q.2.1, q.1, q.2.2)` で入替 (D4) | **~80 行** | **型は完全一致 (probe8 で確認)**。これが内外を同じ添字で並べる橋になり、`mac_capacity_region_reconciliation` (`MultipleAccess/Reconciliation.lean:292`) の BC 版になる |
| **5-6** | `IsBCDegraded W` → `bcConverseAmbient c W` 上の `h_deg_block` | `bcConverse_memoryless₁` (`Bridge.lean:301`) と同じ `isMarkovChain_of_compProd_pi` パターン | **~120 行** | plan の「4b の橋が degraded 側にも効く」を実際に効かせるための欠けているピース。既存の `bcConverse_*` 4 本には degradedness 版が**無い** (0 hit) |
| **5-7** | 内界側の補助変数 union (`martonRegionUnion`) | Phase 2 item 1 (`Fin k` 固定 + `⋃ k`) | plan Phase 2 参照 | **Phase 5 の等号の前提 (D6)**。plan の「Phase 2 は Phase 3–5 の前提ではない」は挟み込みについてのみ正しい |

---

## 6. Mathlib の壁の列挙

**壁は 1 件も無い。** 3 クラスの定義段で Mathlib 側に自作が要る穴はゼロ (4b の M0 在庫と同じ結論)。

| 候補 | loogle 確認 | 判定 |
|---|---|---|
| Mathlib の相互情報量 | `"mutualInfo"` → `Found 0 declarations whose name contains "mutualInfo".` | **壁ではない** — in-project の `Shannon.mutualInfo` (`MutualInfo.lean:36`) が全面的に使われており、Mathlib 側に必要なものは `klDiv` (既存) だけ |
| Mathlib の degraded/BC クラス | `"Degraded"` → `Found 0` / `"lessNoisy"` → `Found 0` / `"Capable"` → `Found 0` / `"semiDeterministic"` → `Found 0` / `"Blackwell"` → `Found 0` | **壁ではない** — 情報理論のチャネル比較は Mathlib の射程外。in-project で定義するのが正しく、自作コストは §5-2 の ~150 行 |
| 周辺チャネルの取り出し | `ProbabilityTheory.IsMarkovKernel (ProbabilityTheory.Kernel.map _ _)` → 1 match (`Kernel.IsMarkovKernel.map`) | **既存**。しかも `Kernel.fst`/`Kernel.snd` には instance 版がある (L10) |
| 結合法とチャネルの語彙橋 | `MeasureTheory.Measure.compProd _ (ProbabilityTheory.Kernel.map _ _)` → 3 match、うち `Measure.compProd_map` | **既存** (L11) |

**共有 sorry 補題は不要**。`@residual(wall:…)` の対象になる項目は現時点でゼロ。

---

## 7. 撤退ラインとの距離

| slug | 発動条件 (plan:313–324) | 本在庫からの判定 |
|---|---|---|
| **L-BCO3** | 「Phase 5 の等号が Phase 4 の外界の形と噛み合わない」 → 退避先「クラス定義だけ入れて等号は defer」 | **触れる。ただし現時点では不発動でよい。** D1 (符号制約) は §5-1 の 3 行で解消でき、「外界の形と噛み合わない」わけではない。D6 (union) は Phase 2 を先に入れれば解消する。**噛み合わなさの本体は外界の形ではなく内界の形 (第一象限制約・union なし・全支持仮説)** なので、L-BCO3 の発動条件の文言が実態とずれている |
| **L-BCO2** | 「Phase 2 の型量化 union が universe 問題で詰む」 | **Phase 5 で先に触れる**。`IsBCLessNoisy` (定義 B) が補助アルファベットを `Type 0` に固定するのが実質的な L-BCO2 の前倒し。**probe5/probe6 で「アルファベット `α β₁ β₂` は `Type*` のまま、補助だけ `Type 0`」が通ることを確認済**なので、**不発動で進める** |

### 新しい撤退ラインの提案 (semi-deterministic 用)

現行の撤退ラインは S1 (semi-deterministic × 全支持仮説の非両立、probe9 で機械確認) をカバーしていない。以下を提案:

> **L-BCO7** — 発動条件: semi-deterministic BC の等号を狙う段で、`marton_achievability` の全支持仮説 `hW` が外せない。
> 退避先: **semi-deterministic は「クラス定義 + 上界 (外界) 側のみ」で止め、内界との等号は述べない**。外界側 (`bc_capacity_subset_uv` の特殊化) は `hW` を要求しないので単独で成立する。退避の出口は `sorry` + `@residual(plan:bc-semideterministic-fullsupport)` とし、**仮説束ね (`IsSemiDeterministicAchievable` のような述語) は取らない**。

---

## 8. 攻略順の推奨

### 推奨: **less noisy から着手する**

| 順位 | クラス | 根拠 (実測) |
|---|---|---|
| **1** | **less noisy** | (a) **gateway atom が通っている** — 定義 B から `bc_degraded_infoJoint_ge` の結論が既存証明の末尾流用 ~25 行で出る (probe5)。(b) **`degraded ⊆ less noisy` が新規補助補題ゼロで ~25 行** (probe7)。(c) 容量領域が degraded と**同じ形** (`InBCCapacityRegion` の 2 制約) なので、既存の `bc_degraded_converse` / `bc_achievability` の結論形をそのまま再利用できる。(d) `marton_achievability` の全支持仮説と両立する (degraded の全支持例が存在)。**既存資産の再利用率が最も高い** |
| **2** | **more capable** | (a) `Kernel.fst`/`Kernel.snd` + `mutualInfoOfChannel` + `capacity` が `bcOuterRegionCoop` (`OuterBound.lean:381`) で既に使われており、定義に必要な部品はゼロコスト。(b) ただし容量領域に **`R₁+R₂ ≤ I(X;Y₁)`** という新しい形の制約が入る (§3-c) ので、`InBCCapacityRegion` (2 制約) では受けきれず **3 制約の新 structure が要る**。(c) `less noisy ⊆ more capable` に語彙橋 (L11) が 1 本要る |
| **3** | **semi-deterministic** | (a) **`marton_achievability` の `hW` と構造的に非両立 (probe9 で機械確認)**。内界を適用できないので等号が閉じない。(b) 容量領域の記述に `H(Y₁)` / `H(Y₁\|U)` が出るため §5-3 / §5-4 の自作 2 本 (~70 行) が前提。(c) 定義自体 (D1) は 3 行で入るので、**定義だけ先に入れて等号は L-BCO7 で defer するのが honest** |

### 着手前に片付けるべき順序 (依存順)

```
5-1 martonRegion の符号制約除去 (~3 行、consumer 1)
  ↓
5-2 3 クラスの定義 + 包含 2 本 (~150 行)   ←★ ここまでが plan の「クラス定義の新設」
  ↓
5-5 IsUVChannelLaw at martonJointDistribution (~80 行)   ← 内外を同じ添字に載せる
  ↓
5-7 = Phase 2 (補助変数 union)   ← 等号の前提 (D6)
  ↓
less noisy の等号 → more capable の等号 → (semi-deterministic は L-BCO7)
```

---

## 9. 開始 skeleton

```lean
import InformationTheory.Shannon.BroadcastChannel.Achievability.Assembly
import InformationTheory.Shannon.ChannelCoding.ShannonTheorem

/-!
# Broadcast channel — comparison classes of the two receivers

Three classes of two-receiver broadcast channel on which the capacity region is known, stated so
that the degraded class of `IsBCDegraded` is the strongest of the chain.

## Main definitions

* `IsBCLessNoisy W` — every auxiliary carries at least as much information about the first
  output as about the second.
* `IsBCMoreCapable W` — every input law reaches the first receiver at least as fast as the
  second.
* `IsBCSemiDeterministic W` — the first receiver's output is a function of the input letter.

## Main statements

* `IsBCDegraded.isBCLessNoisy` — a physically degraded channel is less noisy.
* `IsBCLessNoisy.isBCMoreCapable` — a less noisy channel is more capable.
-/

namespace InformationTheory.Shannon.BroadcastChannel

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.ChannelCoding
open scoped ENNReal

variable {α β₁ β₂ : Type*}
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The first receiver is less noisy than the second: for every auxiliary variable feeding the
input letter, the first output carries at least as much information about the auxiliary as the
second does. -/
def IsBCLessNoisy (W : BCChannel α β₁ β₂) : Prop :=
  ∀ (U : Type) [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U]
      [MeasurableSingletonClass U] (pU : Measure U) [IsProbabilityMeasure pU]
      (K : Kernel U α) [IsMarkovKernel K],
    mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.2)
      ≤ mutualInfo (bcJointDistribution pU K W) Prod.fst (fun q ↦ q.2.2.1)

/-- The first receiver is more capable than the second: every input law reaches the first
receiver at a rate at least that of the second. -/
def IsBCMoreCapable (W : BCChannel α β₁ β₂) : Prop :=
  ∀ p : Measure α, mutualInfoOfChannel p (Kernel.snd W) ≤ mutualInfoOfChannel p (Kernel.fst W)

/-- The channel is semi-deterministic: the first receiver's output is a function of the input
letter, while the second output stays arbitrary. -/
def IsBCSemiDeterministic (W : BCChannel α β₁ β₂) : Prop :=
  ∃ f : α → β₁, ∀ a : α, Kernel.fst W a = Measure.dirac (f a)

theorem IsBCDegraded.isBCLessNoisy {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    (hdeg : IsBCDegraded W) : IsBCLessNoisy W := by
  sorry

theorem IsBCLessNoisy.isBCMoreCapable {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    (hln : IsBCLessNoisy W) : IsBCMoreCapable W := by
  sorry

end InformationTheory.Shannon.BroadcastChannel
```

**import の閉包について (判断ログ 11-(i) の適用)**: 上の skeleton は `bcJointDistribution` (`Achievability/Setup.lean:54`) と `bcMarkovChain_UX_Y₁_Y₂` (`Achievability/Assembly.lean:939`) の両方を引かざるを得ないので、`Achievability/Assembly.lean` を import する。`Kernel.fst`/`Kernel.snd` は Mathlib 側なので追加 import 不要。`mutualInfoOfChannel` / `capacity` のために `ChannelCoding/ShannonTheorem.lean` が要る (`capacity` を使わないなら `ChannelCoding/Basic.lean` で足りる — 実装時に**移動先が引かざるを得ない依存の閉包**で決めること)。`OuterBoundUV/Region.lean` は本 skeleton の範囲では不要 (§5-5 で必要になったら別ファイル)。

**`IsBCDegraded.isBCLessNoisy` の中身は probe7 で機械確認済**なので、skeleton 段階の `sorry` はすぐ埋まる。埋まらない場合の退避は `sorry` + `@residual(plan:bc-phase5-classes)`。

---

## 10. plan の記述と実測が食い違った点 (在庫予測の外れ、通算 11 件目以降)

| # | plan の記述 | 実測 | 影響 |
|---|---|---|---|
| **P1** | 「Phase 5 の等号を `martonRegion` と `bcOuterRegionUV` で直接並べられる」(plan:170–172) | **並べられない**。`martonRegion` の第一象限制約により `bcOuterRegionUV ⊆ martonRegion` は全チャネルで偽 (probe2) | §5-1 の 3 行修正が Phase 5 の最初のステップになる |
| **P2** | 「Phase 2 は Phase 3–5 の前提ではない」(plan:97) | **Phase 5 の等号については前提**。外界は union、内界は 1 個の四辺形 | Phase 2 を Phase 5 の前に入れるか、等号を「∃ pV K」形で述べるかの設計判断が要る |
| **P3** | 「semi-deterministic BC — Marton 内界 = 容量領域が既知」(plan:175) | **文献としては正しいが in-project では実現不能**。`marton_achievability` の `hW` が semi-deterministic と非両立 (probe9) | 攻略順で最後。L-BCO7 の新設を提案 |
| **P4** | 「more capable / less noisy — 外界が UV より単純 (El Gamal 1979)」(plan:176) | less noisy は**正しい** (2 制約)。more capable は 3 制約で**形が違う**。帰属は less noisy = Körner–Marton 1975/1977 | more capable には `InBCCapacityRegion` (2 field) ではなく 3 field の新 structure が要る |
| **P5** | 「`uvRegion` の `.toReal` が逆包含の段で逆向きに効く」(plan:183–186 の (i)) | **符号が逆**。`.toReal` の `⊤ ↦ 0` は外界を縮めるので逆包含は**易しくなる**。危険なのは (ii) の無限アルファベットのみ | Phase 5 (有限アルファベット) では `.toReal` は無関係 |
| **P6** | 「`bc_degraded_converse` 自身も floating 形なので 4b の橋 (S1–S4) が効く」(plan:178) | **そのままでは効かない**。`bc_degraded_converse` の degradedness は `h_deg_block` = ambient 上の per-letter Markov 鎖で、`bcConverse_*` の 4 本にはこれに対応する補題が**無い** (0 hit)。§5-6 の新規 ~120 行が要る | 「橋が効く」の実際のコストが plan の想定より大きい |
| **P7** | 「クラス定義は project に 0 hit」(plan:51, 173) | **述語としては正しい (0 hit を名前検索・結論形検索の両方で確認)**。ただし**部品は在庫にある**: `Kernel.fst W` / `Kernel.snd W` が `bcOuterRegionCoop` (`OuterBound.lean:381`) で既に使用済。plan の §在庫 にこの記載が無い | more capable の定義コストが plan の想定より小さい |
| **P8** | 「degraded を新クラスの特殊化として既存 `bc_degraded_converse` / `bc_achievability` に接続」(plan:177) | 両方とも **direct consumer 0 件** (`dep_consumers.sh` 実測)。「接続」は既存配線への合流ではなく**新規配線の作成** | 見積りは「接続」ではなく「新規実装」で立てるべき |
