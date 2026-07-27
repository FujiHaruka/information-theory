# BC 内外の橋 (`IsUVChannelLaw` at `martonJointDistribution`) — 在庫調査

> 親計画: [`bc-general-region-plan.md`](bc-general-region-plan.md) §Phase 5 「等号」/ §推奨実行順 /
> §撤退ライン L-BCO2 / L-BCO3 / L-BCO7。
> 本ファイルは**着手前の在庫**。`InformationTheory/` は 1 バイトも編集していない。
> 逐語確認に使った probe は scratchpad の `probe{1..7}.lean` (repo 外)。判定は本文に逐語で転記。

## 一行サマリ

**橋そのものに必要な API は 100% 既存で、Mathlib 側の穴はゼロ — gateway atom
`IsUVChannelLaw W (martonJointDistribution pV K W)` は `sorry` なしで実コンパイルした (約 50 行)。**
自作が要るのは 3 本 (座標入替の不変性 / 領域包含の情報量不等式 / 4 スロットの `.toReal` 同定) で、
いずれも既存語彙の組み合わせ。**ただし逆向き (UV 法 → Marton 領域) は機械確認で塞がっている** —
`bcOuterRegionUV` の union は補助を `ℕ` に固定しており、`martonInfo*` は `entropy` 経由で
`[Fintype V₁]` を要求するので `failed to synthesize instance Fintype ℕ` で落ちる (probe5 逐語)。

## 0. 前 leg (r5) の観察 3 件の判定

| # | 前 leg の観察 | 判定 | 根拠 |
|---|---|---|---|
| 1 | `martonJointDistribution pV K W` の型は `IsUVChannelLaw` の第 2 引数と完全一致 | **確認** (かつ**予測より強い**) | probe1 EXIT=0。さらに `#check` 実測で `martonJointDistribution` の必要インスタンスは `[MeasurableSpace _]` × 5 **のみ** — `Fintype` / `DecidableEq` / `Nonempty` / `MeasurableSingletonClass` は `Setup.lean:44`–`:49` の `variable` にはあるが def は使っていない |
| 2 | 座標規約が内外でクロス。`fun q ↦ (q.2.1, q.1, q.2.2)` を挟む必要がある | **確認**。入替写像も**この形で正しい** | probe3 の 4 例が EXIT=0。うち 2 例は `rfl` で「素朴に食わせると `I(V₂;Y₁)` / `I(V₁;Y₂)` を読む」を機械確認 |
| 3 | 内外の数値表現の橋は `mutualInfo_toReal_eq_entropy_form` **1 本のみ** | **半分覆った**。3 スロット (`martonInfo₁` / `martonInfo₂` / `martonInfoV₁V₂`) には確かに 1 本で足りる (probe4 EXIT=0)。**だが和レート制約には対応物が存在しない** — Marton は `I₁+I₂-I₁₂` 1 本、UV は `uvInfoSum₂` / `uvInfoSum₁` の 2 本で、**別の汎関数**。`.toReal` の橋では埋まらず情報量不等式の証明が要る (§5) |

**追加で覆ったもの (前 leg が触れていない)**:

- **(4) 橋は Marton 側の全支持仮説 `hpV` / `hK` / `hW` を 1 つも要求しない** (probe2 実測: 明示仮説は
  `pV` `K` `W` と `[IsProbabilityMeasure pV] [IsMarkovKernel K] [IsMarkovKernel W]` のみ)。
  ⟹ **L-BCO7 (semi-deterministic) のチャネルでも橋は成立する**。
- **(5) 逆向きは型で塞がっている** (§4-B)。plan の「等号は内界側にも union が要る」は正しいが、
  塞いでいるのは universe ではなく **`entropy` の `Fintype` 要求**。
- **(6) `mutualInfo_toReal_eq_entropy_form` は BC の import 閉包に既に居る** —
  `BroadcastChannel/Achievability/Setup.lean:6` が `MultipleAccess.Reconciliation` を import 済で、
  `Operational.lean` → `Marton.Achievability` → … → `Achievability/Setup` で推移的に届く
  (probe5 / probe7 の `#check` で機械確認)。MAC への新規 import は不要。

---

## 1. 内界側の資産 (逐語)

`variable` ブロック (`Marton/Setup.lean:44`–`:49`) は 5 つの型それぞれに
`[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _] [MeasurableSingletonClass _]`。
ただし `martonJointDistribution` は `#check` 実測でそのうち `MeasurableSpace` しか使っていない。

| 資産 | file:line | 逐語シグネチャ (`[...]` 省略なし) | 結論形 / 本体 (逐語) |
|---|---|---|---|
| `martonJointDistribution` | `Marton/Setup.lean:57` | `#check` 実測: `{V₁ V₂ α β₁ β₂ : Type*} → [MeasurableSpace V₁] → [MeasurableSpace V₂] → [MeasurableSpace α] → [MeasurableSpace β₁] → [MeasurableSpace β₂] → Measure (V₁ × V₂) → Kernel (V₁ × V₂) α → BCChannel α β₁ β₂ → Measure (V₁ × V₂ × α × β₁ × β₂)` | `(((pV ⊗ₘ K) ⊗ₘ (W.comap Prod.snd measurable_snd)).map MeasurableEquiv.prodAssoc).map MeasurableEquiv.prodAssoc` |
| `martonJointDistribution.instIsProbabilityMeasure` | `Marton/Setup.lean:63` | `(pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV] (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] : IsProbabilityMeasure (martonJointDistribution pV K W)` | instance。橋の全 step が黙って使う |
| `martonInfo₁` | `Marton/Setup.lean:244` | `noncomputable def martonInfo₁ (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : ℝ` | `entropy (martonJointDistribution pV K W) Prod.fst + entropy (…) (fun q ↦ q.2.2.2.1) - entropy (…) (fun q ↦ (q.1, q.2.2.2.1))` = **`I(V₁;Y₁)`、射影は `q.1` と `q.2.2.2.1`** |
| `martonInfo₂` | `Marton/Setup.lean:252` | 同上 `: ℝ` | `entropy (…) (fun q ↦ q.2.1) + entropy (…) (fun q ↦ q.2.2.2.2) - entropy (…) (fun q ↦ (q.2.1, q.2.2.2.2))` = **`I(V₂;Y₂)`、射影は `q.2.1` と `q.2.2.2.2`** |
| `martonInfoV₁V₂` | `Marton/Setup.lean:262` | 同上 `: ℝ` | `entropy (…) Prod.fst + entropy (…) (fun q ↦ q.2.1) - entropy (…) (fun q ↦ (q.1, q.2.1))` = `I(V₁;V₂)` |
| `entropy` (3 本の土台) | `Shannon/Bridge.lean:40` | `variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]` / `noncomputable def entropy (μ : Measure Ω) (Xs : Ω → X) : ℝ` | `∑ x : X, Real.negMulLog ((μ.map Xs).real {x})` ← **`Fintype X` が §4-B の閉塞の出所** |
| `InMartonRegion` | `Marton/Basic.lean:40` | `structure InMartonRegion (R₁ R₂ I₁ I₂ I₁₂ : ℝ) : Prop` | `bound₁ : R₁ ≤ I₁` / `bound₂ : R₂ ≤ I₂` / `boundSum : R₁ + R₂ ≤ I₁ + I₂ - I₁₂` |
| `martonRegion` | `Operational.lean:127` | `def martonRegion (pV : Measure (V₁ × V₂)) (K : Kernel (V₁ × V₂) α) (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ)` — section var (`Operational.lean:109`–`:114`): 5 型それぞれに `[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _] [MeasurableSingletonClass _]`。`StandardBorelSpace` なし | `{p \| InMartonRegion p.1 p.2 (martonInfo₁ pV K W) (martonInfo₂ pV K W) (martonInfoV₁V₂ pV K W)}` ← **`2c938fe0` 後、第一象限制約なし (逐語再確認済)** |
| `bc_strict_interior_achievable` | `Operational.lean:131` | `(pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV] (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a}) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) {R₁ R₂ : ℝ} (hR₁lt : R₁ < martonInfo₁ pV K W) (hR₂lt : R₂ < martonInfo₂ pV K W) (hRsum : R₁ + R₂ < martonInfo₁ pV K W + martonInfo₂ pV K W - martonInfoV₁V₂ pV K W)` | `BCAchievable W R₁ R₂` |
| `marton_region_subset_capacity` | `Operational.lean:154` (`@[entry_point]`) | `(pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV] (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a}) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b})` | `martonRegion pV K W ⊆ bcCapacityRegion W` |
| `marton_achievability` | `Marton/Achievability.lean:767` (`@[entry_point]`, `@audit:ok`) | `(pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV] (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K] (W : BCChannel α β₁ β₂) [IsMarkovKernel W] (hpV : ∀ v : V₁ × V₂, 0 < pV.real {v}) (hK : ∀ (v : V₁ × V₂) (a : α), 0 < (K v).real {a}) (hW : ∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) {R₁ R₂ : ℝ} (hR₁lt : R₁ < martonInfo₁ pV K W) (hR₂lt : R₂ < martonInfo₂ pV K W) (hRsum : R₁ + R₂ < martonInfo₁ pV K W + martonInfo₂ pV K W - martonInfoV₁V₂ pV K W) {ε' : ℝ} (hε' : 0 < ε')` | `∃ N : ℕ, ∀ n, N ≤ n → ∃ (M₁ M₂ : ℕ) (_hM₁ : ⌈Real.exp ((n : ℝ) * R₁)⌉₊ ≤ M₁) (_hM₂ : ⌈Real.exp ((n : ℝ) * R₂)⌉₊ ≤ M₂) (c : BroadcastCode M₁ M₂ n α β₁ β₂), (c.averageErrorProb₁ W).toReal < ε' ∧ (c.averageErrorProb₂ W).toReal < ε'` |

**内界側の「和の項」は 1 本のみ** — `InMartonRegion.boundSum` が `I₁ + I₂ - I₁₂` で、外界の
`uvInfoSum₂` / `uvInfoSum₁` に対応する独立した def は**存在しない** (`rg` 実測)。

---

## 2. 外界側の資産 (逐語)

file var (`Region.lean:76`–`:78`): `{α : Type*} [MeasurableSpace α]` / `{β₁ : Type*} [MeasurableSpace β₁]` /
`{β₂ : Type*} [MeasurableSpace β₂]`。`section ChannelLaw` var (`:84`): `{U V : Type*} [MeasurableSpace U] [MeasurableSpace V]`。
`section Region` var (`:225`–`:227`): `[StandardBorelSpace α] [Nonempty α] [StandardBorelSpace β₁] [Nonempty β₁] [StandardBorelSpace β₂] [Nonempty β₂]`。

| 資産 | file:line | 逐語シグネチャ | 結論形 / 本体 (逐語) |
|---|---|---|---|
| **`IsUVChannelLaw`** | `Region.lean:102` (`@audit:ok`) | `def IsUVChannelLaw (W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂)) : Prop` (上記 file var + section var) | `ν.map (fun q ↦ ((q.1, q.2.1, q.2.2.1), q.2.2.2)) = (ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) ⊗ₘ W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)` — **structure ではなく 1 本の合成積等式。第 1・第 2 スロットを区別しない (ブロックとして扱う) のが §3 の要点** |
| `isUVChannelLaw_iff` | `Region.lean:123` | `(W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂))` | `IsUVChannelLaw W ν ↔ ν = ((ν.map fun q ↦ (q.1, q.2.1, q.2.2.1)) ⊗ₘ W.comap (fun r : U × V × α ↦ r.2.2) (measurable_snd.comp measurable_snd)).map (fun z : (U × V × α) × (β₁ × β₂) ↦ (z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2))` |
| `IsUVChannelLaw.smul` | `Region.lean:145` (`@audit:ok`) | `{W : BCChannel α β₁ β₂} [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) (a : ℝ≥0∞)` | `IsUVChannelLaw W (a • ν)` |
| `IsUVChannelLaw.add` | `Region.lean:152` (`@audit:ok`) | `{W} [IsMarkovKernel W] {ν₁ ν₂ : Measure (U × V × α × β₁ × β₂)} [SFinite ν₁] [SFinite ν₂] (h₁ …) (h₂ …)` | `IsUVChannelLaw W (ν₁ + ν₂)` |
| `IsUVChannelLaw.finsetSum` | `Region.lean:160` | `{ι : Type*} {W} [IsMarkovKernel W] {ν : ι → Measure (U × V × α × β₁ × β₂)} [∀ i, IsFiniteMeasure (ν i)] (h : ∀ i, IsUVChannelLaw W (ν i)) (s : Finset ι)` | `IsUVChannelLaw W (∑ i ∈ s, ν i)` |
| **`IsUVChannelLaw.map_auxiliaries`** | `Region.lean:175` (`@audit:ok`) | `{U' V' : Type*} [MeasurableSpace U'] [MeasurableSpace V'] {W : BCChannel α β₁ β₂} [IsMarkovKernel W] {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) {f : U → U'} {g : V → V'} (hf : Measurable f) (hg : Measurable g)` | `IsUVChannelLaw W (ν.map fun q ↦ (f q.1, g q.2.1, q.2.2))` ← **`ℕ` 化に使う。入替は `f`/`g` の形に載らないので別補題が要る (§6-1)** |
| `IsUVChannelLaw.map_input_output` | `Region.lean:202` (`@audit:ok`) | `{W} [IsMarkovKernel W] {ν} [SFinite ν] (h : IsUVChannelLaw W ν)` | `ν.map (fun q ↦ (q.2.2.1, q.2.2.2)) = (ν.map fun q ↦ q.2.2.1) ⊗ₘ W` |
| `uvInfo₁` | `Bridge.lean:777` (`@audit:ok`) | `noncomputable def uvInfo₁ (ν : Measure (U × V × α × β₁ × β₂)) : ℝ≥0∞` — section var (`Bridge.lean:770`–`:773`): `{U V : Type*} [MeasurableSpace U] [MeasurableSpace V]` + `[StandardBorelSpace α] [Nonempty α]` + β₁/β₂ 同様 | `mutualInfo ν (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)` = **`I(V;Y₁)`、射影は `q.2.1` (第 2 スロット)** |
| `uvInfo₂` | `Bridge.lean:782` (`@audit:ok`) | 同上 | `mutualInfo ν (fun q ↦ q.1) (fun q ↦ q.2.2.2.2)` = **`I(U;Y₂)`、射影は `q.1` (第 1 スロット)** |
| `uvInfoSum₂` | `Bridge.lean:787` (`@audit:ok`) | `noncomputable def uvInfoSum₂ (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : ℝ≥0∞` | `uvInfo₂ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.1) (fun q ↦ q.1)` = `I(U;Y₂) + I(X;Y₁\|U)` |
| `uvInfoSum₁` | `Bridge.lean:792` (`@audit:ok`) | 同上 | `uvInfo₁ ν + condMutualInfo ν (fun q ↦ q.2.2.1) (fun q ↦ q.2.2.2.2) (fun q ↦ q.2.1)` = `I(V;Y₁) + I(X;Y₂\|V)` |
| `InBCOuterRegionUV` | `OuterBoundUV.lean:735` (`@audit:ok`) | `structure InBCOuterRegionUV (R₁ R₂ I₁ I₂ J₂ J₁ : ℝ) : Prop` | `bound₁ : R₁ ≤ I₁` / `bound₂ : R₂ ≤ I₂` / `sumBound₂ : R₁ + R₂ ≤ J₂` / `sumBound₁ : R₁ + R₂ ≤ J₁` |
| **`uvRegion`** | `Region.lean:233` (`@audit:ok`) | `def uvRegion {U V : Type*} [MeasurableSpace U] [MeasurableSpace V] (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν] : Set (ℝ × ℝ)` (section var = 上記 6 本)。**`Fintype` なし** | `{p \| InBCOuterRegionUV p.1 p.2 (uvInfo₁ ν).toReal (uvInfo₂ ν).toReal (uvInfoSum₂ ν).toReal (uvInfoSum₁ ν).toReal}` ← **`.toReal` は 4 スロット全部に入る** |
| **`bcOuterRegionUV`** | `Region.lean:245` (`@audit:ok`) | `def bcOuterRegionUV (W : BCChannel α β₁ β₂) : Set (ℝ × ℝ)` (同 section var) | `closure (⋃ (ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂)) (_ : IsUVChannelLaw W (ν : Measure (ℕ × ℕ × α × β₁ × β₂))), uvRegion (ν : Measure (ℕ × ℕ × α × β₁ × β₂)))` ← **補助は `ℕ` に固定 (§4-B の閉塞の相手側)** |
| `bcOuterRegionUV_isClosed` | `Region.lean:251` (`@audit:ok`) | `(W : BCChannel α β₁ β₂)` | `IsClosed (bcOuterRegionUV W)` |
| `bcOuterRegionUV_isLowerSet` | `Region.lean:265` (`@audit:ok`) | `(W : BCChannel α β₁ β₂)` | `IsLowerSet (bcOuterRegionUV W)` |
| `uvRegion_isLowerSet` | `Region.lean:255` (`@audit:ok`) | `{U V : Type*} [MeasurableSpace U] [MeasurableSpace V] (ν : Measure (U × V × α × β₁ × β₂)) [IsFiniteMeasure ν]` | `IsLowerSet (uvRegion ν)` |
| `bcOuterRegionUV_nonempty` | `Region.lean:317` (`@audit:ok`) | `(W : BCChannel α β₁ β₂) [IsMarkovKernel W]` | `(bcOuterRegionUV W).Nonempty` |
| **`bc_capacity_subset_uv`** | `Assembly.lean:839` (`@[entry_point]`, `@audit:ok`) | `(W : BCChannel α β₁ β₂) [IsMarkovKernel W]` — section var (`Assembly.lean:659`–`:661`): `[Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α]` + β₁ / β₂ 同様。file var は `{α : Type*} [MeasurableSpace α]` 等 | `bcCapacityRegion W ⊆ bcOuterRegionUV W` |
| `bcUVJointDistribution_isUVChannelLaw` | `Assembly.lean:72` (`@audit:ok`) | `(c : BroadcastCode M₁ M₂ n α β₁ β₂) (W : BCChannel α β₁ β₂) [IsMarkovKernel W] [NeZero M₁] [NeZero M₂] (i : Fin n)` — `section CodeLaw` var (`:69`): `[Nonempty β₁] [Nonempty β₂]` | `IsUVChannelLaw W (bcUVJointDistribution c W i)` ← **step 1 の直接の雛形 (本体 `:76`–`:121` の約 46 行)** |

---

## 3. 座標規約のクロス — 機械確認 (probe3、EXIT=0)

`rfl` で通った 2 例と `mutualInfo_map_comp` で通った 2 例により、下表は**機械確認済**。

| 側 | 情報量 | 読む座標 (逐語の射影) | 受信機 |
|---|---|---|---|
| UV | `uvInfo₁ ν` | `(fun q ↦ q.2.1)` × `(fun q ↦ q.2.2.2.1)` | **第 2 スロット ↔ 受信機 1** |
| UV | `uvInfo₂ ν` | `(fun q ↦ q.1)` × `(fun q ↦ q.2.2.2.2)` | **第 1 スロット ↔ 受信機 2** |
| UV | `uvInfoSum₂ ν` | 条件付けが `(fun q ↦ q.1)` | 第 1 スロットで条件付け |
| UV | `uvInfoSum₁ ν` | 条件付けが `(fun q ↦ q.2.1)` | 第 2 スロットで条件付け |
| Marton | `martonInfo₁` | `Prod.fst` × `(fun q ↦ q.2.2.2.1)` | **第 1 スロット ↔ 受信機 1** |
| Marton | `martonInfo₂` | `(fun q ↦ q.2.1)` × `(fun q ↦ q.2.2.2.2)` | **第 2 スロット ↔ 受信機 2** |
| Marton | `martonInfoV₁V₂` | `Prod.fst` × `(fun q ↦ q.2.1)` | 両スロット |

**素朴に食わせた場合の実測 (probe3、`rfl` で成立)**:

```lean
uvInfo₁ (martonJointDistribution pV K W)
  = mutualInfo (martonJointDistribution pV K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.1)  -- I(V₂;Y₁)
uvInfo₂ (martonJointDistribution pV K W)
  = mutualInfo (martonJointDistribution pV K W) (fun q ↦ q.1)   (fun q ↦ q.2.2.2.2)  -- I(V₁;Y₂)
```

**正しい入替写像は `fun q ↦ (q.2.1, q.1, q.2.2)` で合っている** (probe3、`mutualInfo_map_comp` 経由で成立):

```lean
uvInfo₁ ((martonJointDistribution pV K W).map (fun q ↦ (q.2.1, q.1, q.2.2)))
  = mutualInfo (martonJointDistribution pV K W) (fun q ↦ q.1)   (fun q ↦ q.2.2.2.1)  -- I(V₁;Y₁) ✓
uvInfo₂ ((martonJointDistribution pV K W).map (fun q ↦ (q.2.1, q.1, q.2.2)))
  = mutualInfo (martonJointDistribution pV K W) (fun q ↦ q.2.1) (fun q ↦ q.2.2.2.2)  -- I(V₂;Y₂) ✓
```

**重要な非対称性**: `IsUVChannelLaw` は第 1・第 2 スロットを `(q.1, q.2.1, q.2.2.1)` という
**ブロックとしてしか見ない**ので、入替は**述語の成否に影響しない** (§6-1 の入替不変性で機械確認)。
入替が要るのは**情報量スロットを読むときだけ**。⟹ **step 1 (橋の本体) は入替を挟まずに書ける**。

---

## 4. gateway atom — 両向きの実測

### 4-A. 順向き (Marton 法 → UV 添字): **通った。`sorry` ゼロ**

probe2 が `lake env lean` EXIT=0。証明本体は約 50 行で、使ったのは
`Measure.map_map` / `Measure.fst_compProd` / `Kernel.ext fun _ ↦ rfl` / `compProd_comap_map_prodMap` のみ。
**自作補助補題ゼロ**。要求インスタンスは以下だけ (Fintype / DecidableEq / StandardBorelSpace **不要**):

```lean
example (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsUVChannelLaw W (martonJointDistribution pV K W) := by …   -- EXIT=0
```

機構: `martonJointDistribution` の 2 段 `prodAssoc` と `IsUVChannelLaw` の分割写像を合成すると
`fun z : ((V₁ × V₂) × α) × (β₁ × β₂) ↦ (g z.1, z.2)` (`g` は左結合 → 右結合の並べ替え) に `rfl` で潰れる。
そこに `compProd_comap_map_prodMap` が**そのままの向きで**当たる。右辺は `Measure.fst_compProd` で
`pV ⊗ₘ K` に落ちる。

### 4-B. 逆向き (UV 法 → Marton 領域): **型で塞がっている (機械確認)**

probe5 の逐語エラー:

```
probe5.lean:27:2: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Fintype ℕ
Hint: Adding the command `deriving instance Fintype for Nat` may allow Lean to derive the missing instance.
```

出所: `bcOuterRegionUV` の union は `ν : ProbabilityMeasure (ℕ × ℕ × α × β₁ × β₂)` を走る
(`Region.lean:246`) 一方、`martonRegion` は `martonInfo*` 経由で `entropy` (`Shannon/Bridge.lean:40`,
`[Fintype X]` 必須) を呼ぶ。**`Measure.map` は universe をまたげるので universe 問題ではない** —
純粋に `Fintype` インスタンスの欠如。

**帰結**: 「UV 外界の任意の元を Marton 領域で覆う」= 等号の難しい向きは、
`martonInfo*` を `ℝ≥0∞` の `mutualInfo` 版に置き換える (定義 pivot) か、
補助アルファベットを有限に落とす (Carathéodory 型の濃度上界 = L-BCO2) かの**二択**。
`mutualInfo` / `condMutualInfo` は `[Fintype]` を要求しない (`MutualInfo.lean:30`–`:32` /
`CondMutualInfo.lean:48`–`:52` を逐語確認) ので、前者は型としては通る。

### 4-C. その他の実測 (probe3 / probe6)

| 主張 | 判定 |
|---|---|
| `IsUVChannelLaw W ν → IsUVChannelLaw W (ν.map (fun q ↦ (q.2.1, q.1, q.2.2)))` (入替不変性、一般形) | **証明が通った** (約 30 行、`compProd_comap_map_prodMap` + `Kernel.ext`)。仮説は `[IsMarkovKernel W] [SFinite ν]` のみ |
| `IsUVChannelLaw W ((martonJointDistribution …).map (fun q ↦ (e₂ q.1, e₁ q.2.1, q.2.2)))` (`ℕ` 化) | `IsUVChannelLaw.map_auxiliaries` **1 行で通る**。ただし higher-order unification が効かないので `(f := …) (g := …)` を明示すること (実測) |
| `uvRegion (martonJointDistribution pV K W)` が elaborate するか | **通る**。`StandardBorelSpace α` 等は `[Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]` から自動導出、`IsFiniteMeasure` は `instIsProbabilityMeasure` から |
| `martonRegion pV K W ⊆ bcOuterRegionUV W` が elaborate するか | **通る** (probe6、`sorry` 警告 1 件のみ)。目標の署名は型として健全 |
| `uvInfo₁_map_uvRelabel` を入替後の法に当てる | **通るが `IsProbabilityMeasure` インスタンスが自動で出ない**。`haveI … := Measure.isProbabilityMeasure_map (…).aemeasurable` の 1 行が要る (probe6 で実測・解消) |

---

## 5. 雛形の強さ diff — `mac_capacity_region_reconciliation` は**そのままでは使えない**

| 項目 | 実測 |
|---|---|
| file:line | `MultipleAccess/Reconciliation.lean:292` (`@[entry_point]`, `@audit:ok`) |
| 逐語シグネチャ | `theorem mac_capacity_region_reconciliation (R₁ R₂ : ℝ) (p₁ : Measure α₁) [IsProbabilityMeasure p₁] (p₂ : Measure α₂) [IsProbabilityMeasure p₂] (W : MACChannel α₁ α₂ β) [IsMarkovKernel W]` — section var (`:84`–`:90`): `{α₁ α₂ β : Type*}` それぞれに `[Fintype _] [DecidableEq _] [Nonempty _] [MeasurableSpace _] [MeasurableSingletonClass _] [StandardBorelSpace _]` |
| 結論形 (逐語) | `InMACCapacityRegion R₁ R₂ (macInfo₁ p₁ p₂ W) (macInfo₂ p₁ p₂ W) (macInfoBoth p₁ p₂ W) ↔ InMACCapacityRegion R₁ R₂ (condMutualInfo (macJointDistribution p₁ p₂ W) Prod.fst (fun q ↦ q.2.2) (fun q ↦ q.2.1)).toReal (condMutualInfo (macJointDistribution p₁ p₂ W) (fun q ↦ q.2.1) (fun q ↦ q.2.2) Prod.fst).toReal (mutualInfo (macJointDistribution p₁ p₂ W) (fun q ↦ (q.1, q.2.1)) (fun q ↦ q.2.2)).toReal` |

**強さ diff (先に取った)**:

| 軸 | MAC 雛形 | BC でやりたいこと | 差 |
|---|---|---|---|
| 主張の型 | **点ごとの `↔`** (`Prop ↔ Prop`)。集合の包含でも等号でもない | 添字集合への所属 (`IsUVChannelLaw`) + 集合の包含 | **別物** |
| 添字 | 内外が**同じ** `macJointDistribution p₁ p₂ W` を見る。添字合わせの問題が最初から無い | 内外で法の型は一致するが**添字集合が別** (`ℕ × ℕ` の union) | BC 固有 |
| 制約の本数 | 内外とも `InMACCapacityRegion` の **3 本で同数・同形**。3 本の `_eq_*_toReal` を `rw` するだけ (本体 2 行) | Marton 3 本 vs UV 4 本、**和の項の汎関数が違う** | BC 固有 |
| 座標 | 入替なし | 入替が要る (§3) | BC 固有 |

**判定**: 雛形として使えるのは **§5 の「`ℝ` 値の entropy 差 ↔ `ℝ≥0∞` の `.toReal`」を `rw` で潰す最後の
2 行のパターンだけ**。`mac_capacity_region_reconciliation` 自身は BC の橋の到達目標より**弱い**
(点ごとの言い換え ⊂ 添字合わせ + 包含)。判断ログ 11-(f) と同じ失敗 (雛形の到達目標を確認せずに使う) を
繰り返さないため、**参照するのは `Reconciliation.lean:305`–`:306` の 2 行だけ**と明記する。

### `mutualInfo_toReal_eq_entropy_form` — 1 本で足りるか

| 項目 | 実測 |
|---|---|
| file:line | `MultipleAccess/Reconciliation.lean:45` |
| 逐語シグネチャ | `lemma mutualInfo_toReal_eq_entropy_form {Ω : Type*} [MeasurableSpace Ω] {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype B] [DecidableEq B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → A) (g : Ω → B) (hf : Measurable f) (hg : Measurable g)` |
| 結論形 (逐語) | `(mutualInfo μ f g).toReal = entropy μ f + entropy μ g - entropy μ (fun ω ↦ (f ω, g ω))` |
| 要求する仮説 | `IsProbabilityMeasure μ` + 可測性 2 本 + 両アルファベットの `Fintype`/`DecidableEq`/`Nonempty`/`MeasurableSingletonClass`。**full support は不要 / `StandardBorelSpace` も不要** |
| direct consumer | **5 decl / 3 file** (`dep_consumers.sh` 実測): `Achievability/Assembly.lean:959` `bc_degraded_infoJoint_ge` / `Classes.lean:80` `bc_lessNoisy_infoJoint_ge` / `Reconciliation.lean:120` `:134` `:247` |

**判定: 3 スロットには足りる。和レートには足りない。**

probe4 (EXIT=0) が 3 本すべてを機械確認した:

```lean
(uvInfo₁ ((martonJointDistribution pV K W).map (fun q ↦ (q.2.1, q.1, q.2.2)))).toReal
  = martonInfo₁ pV K W                                                            -- ✓
(uvInfo₂ ((martonJointDistribution pV K W).map (fun q ↦ (q.2.1, q.1, q.2.2)))).toReal
  = martonInfo₂ pV K W                                                            -- ✓
(mutualInfo (martonJointDistribution pV K W) (fun q ↦ q.1) (fun q ↦ q.2.1)).toReal
  = martonInfoV₁V₂ pV K W                                                         -- ✓
```

いずれも `rw [uvInfo₁, mutualInfo_map_comp …, mutualInfo_toReal_eq_entropy_form …]` の後 `rfl`。
**1 本あたり 6 行**。

**足りない分**: `uvInfoSum₂` / `uvInfoSum₁` に対応する Marton 側の量が**存在しない**。
これは `.toReal` の橋ではなく**情報量不等式**の問題 (§6-2)。

---

## 6. 自作が要るもの (優先度順)

### 6-1. 入替不変性 `IsUVChannelLaw` (**実測済: 約 30 行、壁なし**)

```lean
lemma IsUVChannelLaw.swap_auxiliaries {W : BCChannel α β₁ β₂} [IsMarkovKernel W]
    {ν : Measure (U × V × α × β₁ × β₂)} [SFinite ν] (h : IsUVChannelLaw W ν) :
    IsUVChannelLaw W (ν.map fun q ↦ (q.2.1, q.1, q.2.2))
```

`IsUVChannelLaw.map_auxiliaries` (`Region.lean:175`) の**逐語の写経**で通る (probe3 で実コンパイル)。
`f`/`g` を別々に当てる形では入替が表せないので新規宣言が要るが、証明は `hφ` を
`fun r ↦ (r.2.1, r.1, r.2.2)` に差し替えるだけ。**置き場所は `Region.lean` の `section ChannelLaw`**
(既存 5 本の閉包性補題と同じ場所、追加 import ゼロ)。

**落とし穴**: `map_auxiliaries` の証明が使う `compProd_comap_map_prodMap` は
`InformationTheory.Shannon` 名前空間 (`CodeToAmbient.lean:346`)。`Region.lean` は既に import 済。

### 6-2. 領域包含の情報量不等式 (**本命の数学。予想 150–250 行**)

`martonRegion pV K W ⊆ uvRegion ((martonJointDistribution pV K W).map swap)` を示すには、
`InMartonRegion` の 3 本から `InBCOuterRegionUV` の 4 本を出す必要がある。
`bound₁` / `bound₂` は §5 の同定で**そのまま**。残る 2 本が非自明:

```
需要 A : martonInfo₁ + martonInfo₂ - martonInfoV₁V₂ ≤ (uvInfoSum₂ …).toReal
         ⟺ I(V₁;Y₁) - I(V₁;V₂) ≤ I(X;Y₁|V₂)
需要 B : martonInfo₁ + martonInfo₂ - martonInfoV₁V₂ ≤ (uvInfoSum₁ …).toReal
         ⟺ I(V₂;Y₂) - I(V₁;V₂) ≤ I(X;Y₂|V₁)
```

**真であることの経路 (壁ではない)** — 需要 A について、既存語彙だけで閉じる:

1. `mutualInfo_chain_rule` (`CondMutualInfo.lean:214`) を `Z := V₂`, `X := X`, `Y := Y₁` で:
   `I((V₂,X);Y₁) = I(V₂;Y₁) + I(X;Y₁|V₂)`
2. 同じ補題を `Z := V₂`, `X := V₁` で: `I((V₂,V₁);Y₁) = I(V₂;Y₁) + I(V₁;Y₁|V₂)`
3. `mutualInfo_le_of_markov` (`CondMutualInfo.lean:356`) を Markov 鎖 `(V₁,V₂) → (V₂,X) → Y₁` で:
   `I((V₂,V₁);Y₁) ≤ I((V₂,X);Y₁)`。この Markov 鎖は `IsUVChannelLaw` から出る (§6-1 の橋の帰結)
4. 1–3 と `condMutualInfo_ne_top` (`CondMutualInfo.lean:320`) の `ENNReal` 引き算で
   `I(V₁;Y₁|V₂) ≤ I(X;Y₁|V₂)`
5. `mutualInfo_chain_rule` をもう 1 度 (右引数側、`mutualInfo_comm` `CondMutualInfo.lean:285` 併用) で
   `I(V₁;Y₁) ≤ I(V₁;(V₂,Y₁)) = I(V₁;V₂) + I(V₁;Y₁|V₂)`

**壁宣言はしない** — 5 step すべてが in-project の既存 `@[entry_point]` 補題で、
テンプレ補題は `mutualInfo_le_of_markov` (結論形 `mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo`)。
コストは `ENNReal` ↔ `ℝ` の往復と `IsMarkovChain` の構成で、150–250 行の見積り。

**落とし穴**: 需要 A/B は `ℝ≥0∞` 側で示してから `.toReal` に落とすほうが安い
(`ENNReal.toReal_le_toReal` は有限性が要るので `condMutualInfo_ne_top` / `mutualInfo_ne_top` を確保)。
逆に `ℝ` 側で `martonInfo*` の entropy 差のまま扱うと `Fintype` は揃うが引き算の符号処理が増える。

### 6-3. 4 スロットの `.toReal` 同定 (**実測済: 1 本 6 行 × 3 = 約 25 行**)

§5 の 3 本 (`martonInfo₁` / `martonInfo₂` / `martonInfoV₁V₂`)。probe4 でコンパイル済。

### 6-4. `ℕ` 化と slot 保存 (**約 40 行**)

`Fintype.equivFin` で `V₁ → ℕ` / `V₂ → ℕ` を作り、`IsUVChannelLaw.map_auxiliaries` +
`uvInfo₁_map_uvRelabel` (`Assembly.lean:143`) / `uvInfo₂_map_uvRelabel` (`:155`) /
`uvInfoSum₂_map_uvRelabel` (`:175`) / `uvInfoSum₁_map_uvRelabel` (`:195`) を当てる。

逐語シグネチャ (代表 1 本、`[...]` 省略なし):

```lean
lemma uvInfo₁_map_uvRelabel (ν : Measure (U × V × α × β₁ × β₂)) [IsProbabilityMeasure ν]
    {e₁ : U → U'} {e₂ : V → V'} {d₂ : V' → V} (he₁ : Measurable e₁) (he₂ : Measurable e₂)
    (hd₂ : Measurable d₂) (h₂ : ∀ v, d₂ (e₂ v) = v) :
    uvInfo₁ (ν.map (uvRelabel e₁ e₂)) = uvInfo₁ ν
```

`section AuxRelabel` var (`Assembly.lean:129`–`:130`): `{U V U' V' : Type*}` + `[MeasurableSpace _]` × 4。
`uvInfoSum₂_map_uvRelabel` は追加で `section Sum` var (`:168`–`:171`) の
`[StandardBorelSpace α] [Nonempty α]` / `[Fintype β₁] [MeasurableSingletonClass β₁] [StandardBorelSpace β₁] [Nonempty β₁]` /
`[Fintype U] [MeasurableSingletonClass U]` を要求 (`omit` で `β₂` 系と `Fintype V` を落としている)。

**落とし穴 (実測で踏んだ)**:
- 左逆写像 `d₂ : ℕ → V₁` は `if h : k < Fintype.card V₁ then (Fintype.equivFin V₁).symm ⟨k, h⟩ else Classical.arbitrary V₁` で作る。`h₂` は `simp` で閉じる (probe6 実測)。
- **入替後の法に `IsProbabilityMeasure` インスタンスが自動で付かない**。
  `haveI : IsProbabilityMeasure ((martonJointDistribution …).map (fun q ↦ (q.2.1, q.1, q.2.2))) := Measure.isProbabilityMeasure_map (…).aemeasurable` が要る。
  ⟹ **入替後の法を名前付き `def` にして `instance` を 1 本添える**のが安い。

### 6-5. 補助語彙 — 在庫 (in-project を先に、そのあと Mathlib)

| 語彙 | file:line | 逐語シグネチャ | 使い所 |
|---|---|---|---|
| `compProd_comap_map_prodMap` | `ChannelCoding/CodeToAmbient.lean:346` (`@audit:ok`) | `lemma compProd_comap_map_prodMap {A A' B : Type*} [MeasurableSpace A] [MeasurableSpace A'] [MeasurableSpace B] (μ : Measure A) [SFinite μ] (κ : Kernel A' B) [IsMarkovKernel κ] {g : A → A'} (hg : Measurable g) : (μ ⊗ₘ κ.comap g hg).map (fun z ↦ (g z.1, z.2)) = (μ.map g) ⊗ₘ κ` | **step 1 と入替不変性の両方の心臓**。namespace は `InformationTheory.Shannon` |
| `mutualInfo_map_comp` | `CodeToAmbient.lean:435` | `lemma mutualInfo_map_comp {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) (T : Ω → Ω') (hT : Measurable T) (f : Ω' → A) (hf : Measurable f) (g : Ω' → B) (hg : Measurable g) : mutualInfo (μ.map T) f g = mutualInfo μ (fun ω ↦ f (T ω)) (fun ω ↦ g (T ω))` | 座標入替後のスロットを元の法の射影へ引き戻す。**probe3 / probe4 の主役** |
| `condMutualInfo_map_comp` | `CodeToAmbient.lean:465` | `{Ω Ω' A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A] [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B] [MeasurableSpace C] (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω') (hT : Measurable T) (f : Ω' → A) (hf : Measurable f) (g : Ω' → B) (hg : Measurable g) (h : Ω' → C) (hh : Measurable h)` | `uvInfoSum*` を入替後に読むとき。**`StandardBorelSpace` が 2 つ付く** |
| `mutualInfo_eq_of_leftInverse` | `CondMutualInfoMixture.lean:40` | `{Ω γ A B : Type*} [MeasurableSpace Ω] [MeasurableSpace γ] [MeasurableSpace A] [MeasurableSpace B] (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → A) (Yo : Ω → γ) (hU : Measurable U) (hYo : Measurable Yo) {f : A → B} {g : B → A} (hf : Measurable f) (hg : Measurable g) (hgf : ∀ a, g (f a) = a) : mutualInfo μ (fun ω ↦ f (U ω)) Yo = mutualInfo μ U Yo` | `ℕ` 化の slot 保存の土台 (`uvInfo₁_map_uvRelabel` が内部で使う) |
| `mutualInfo_map_left_measurableEquiv` | `MIChainRule.lean:35` (`@[entry_point]`) | `{X' : Type*} [MeasurableSpace X'] (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Yo : Ω → Y) (hXs : Measurable Xs) (hYo : Measurable Yo) (e : X ≃ᵐ X') : mutualInfo μ (fun ω ↦ e (Xs ω)) Yo = mutualInfo μ Xs Yo` | 上の**強い仮説版** (`MeasurableEquiv` 要求)。§後続作業 D-2 が subsume 対象と記録。橋では **`mutualInfo_map_comp` を優先**すべき (入替は `MeasurableEquiv` 化する必要がない) |
| `mutualInfo_chain_rule` | `CondMutualInfo.lean:214` (`@[entry_point]`) | `(μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Yo : Ω → Y) (Zc : Ω → Z) (hXs : Measurable Xs) (hYo : Measurable Yo) (hZc : Measurable Zc) : mutualInfo μ (fun ω ↦ (Zc ω, Xs ω)) Yo = mutualInfo μ Zc Yo + condMutualInfo μ Xs Yo Zc` | §6-2 の step 1/2/5 |
| `mutualInfo_le_of_markov` | `CondMutualInfo.lean:356` (`@[entry_point]`) | `(μ : Measure Ω) [IsProbabilityMeasure μ] [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) (hXs : Measurable Xs) (hZc : Measurable Zc) (hYo : Measurable Yo) (hmarkov : IsMarkovChain μ Xs Zc Yo) : mutualInfo μ Xs Yo ≤ mutualInfo μ Zc Yo` | §6-2 の step 3 (DPI)。**条件付き DPI は in-project に無いので、chain rule 2 本で挟む形を採る** |
| `IsMarkovChain` | `CondMutualInfo.lean:82` | `def IsMarkovChain (μ : Measure Ω) [IsFiniteMeasure μ] (Xs : Ω → X) (Zc : Ω → Z) (Yo : Ω → Y) : Prop` (γ 形 = 同時法の分解) | step 3 の仮説 |
| `condMutualInfo_ne_top` | `CondMutualInfo.lean:320` | — | `ENNReal` の引き算に要る有限性 |
| `mutualInfo_eq_entropy_add_entropy_sub_jointEntropy` | `MIChainRule.lean:420` | `(joint : Measure (α × β)) [IsProbabilityMeasure joint] : (mutualInfo joint Prod.fst Prod.snd).toReal = entropy joint Prod.fst + entropy joint Prod.snd - entropy joint id` | `mutualInfo_toReal_eq_entropy_form` の土台。**`Prod.fst`/`Prod.snd` 固定なので橋では直接使わない** |

**Mathlib 側 (loogle 実測)**:

| 語彙 | file:line | 逐語 | 使えるか |
|---|---|---|---|
| `MeasurableEquiv.prodComm` | `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:376` | `def prodComm : α × β ≃ᵐ β × α where toEquiv := .prodComm α β` | **不要**。入替対象は入れ子の第 1・第 2 成分なので `prodComm` 単体では形が合わない。生ラムダ + `compProd_comap_map_prodMap` で足りる (probe3 実測) |
| `MeasurableEquiv.prodAssoc` | 同 `:381` | `def prodAssoc : (α × β) × γ ≃ᵐ α × β × γ` | `martonJointDistribution` の定義に既出。step 1 では `rfl` で潰れるので明示操作は不要 |
| `MeasureTheory.Measure.compProd_map` | `Mathlib/Probability/Kernel/Composition/Lemmas.lean:120` | `lemma compProd_map [SFinite μ] [IsSFiniteKernel κ] {f : β → γ} (hf : Measurable f) : μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f)` | **向き違い (逐語確認)** — 動かすのは**第 2 成分**。第 1 成分を動かす版は Mathlib に無い (下記 0-hit)。r5 の観察を再確認 |
| `ProbabilityTheory.compProd_map_condDistrib` | `Mathlib/Probability/Kernel/CondDistrib.lean:82` | `lemma compProd_map_condDistrib (hY : AEMeasurable Y μ) : (μ.map X) ⊗ₘ condDistrib Y X μ = μ.map fun a ↦ (X a, Y a)` — namespace var (`:55`–`:57`): `{α β Ω F : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω] [NormedAddCommGroup F] {mα : MeasurableSpace α} {μ : Measure α} [IsFiniteMeasure μ] {X : α → β} {Y : α → Ω}` | **逆向き (§4-B) を狙う段でのみ**。`ν` から `K` を作り直すのに要る |

---

## 7. 配置と import の向き (逐語確認)

**import の向きは Marton → OuterBoundUV の一方通行**。実際の `import` 行 (`rg -n "^import"` 実測):

```
OuterBoundUV/Assembly.lean : Meta.EntryPoint / BroadcastChannel.Operational / BroadcastChannel.OuterBound
                             / OuterBoundUV.Bridge / OuterBoundUV.Region / Shannon.CondMutualInfoMixture
OuterBoundUV/Region.lean   : OuterBoundUV.Bridge / ChannelCoding.CodeToAmbient / Mathlib × 2
OuterBoundUV/Bridge.lean   : BroadcastChannel.Basic / BroadcastChannel.OuterBoundUV
                             / ChannelCoding.CodeToAmbient / CondEntropyMemoryless / CondMutualInfo
                             / CondMutualInfoMixture / MutualInfo
Operational.lean           : BroadcastChannel.Marton.Achievability          ← これ 1 本だけ
Marton/Setup.lean          : BroadcastChannel.Basic / Entropy / IIDProductInput.Basic
                             / AEP.Basic.Converse / Mathlib × 2
```

- **`OuterBoundUV/*.lean` が `Marton/*.lean` を import している** (`Assembly.lean:2` → `Operational.lean:1`
  → `Marton/Achievability.lean` → `Marton/ErrorAnalysis` → `Marton/Covering` → `Marton/Setup`)。
  逆向き (`Marton/*` → `OuterBoundUV/*`) は**ゼロ** (`rg -l` 実測: `OuterBoundUV` を import しているのは
  `OuterBoundUV.lean` / `OuterBoundUV/Bridge.lean` / `OuterBoundUV/Assembly.lean` / `OuterBoundUV/Region.lean` の 4 本のみ)。
- **⟹ import cycle のリスクはゼロ**。橋を新ファイルに置いても既存ファイルに置いても循環しない。
- **`Region.lean` には置けない** — `Region.lean` は `Marton` を import しておらず、
  `martonJointDistribution` に届かない。`Region.lean` に `Operational` を足すと
  `Region → Operational → Marton.Achievability → BC.Achievability.Assembly` という**重い依存が
  UV 領域定義の側に流れ込む** (`Assembly.lean` は既にそれを引いているので実害は Region 単体のビルドのみ)。推奨しない。

**推奨配置**: 新ファイル `InformationTheory/Shannon/BroadcastChannel/OuterBoundUV/MartonBridge.lean`、
**import は `InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Assembly` 1 本**。

probe7 (EXIT=0、error 0 件) が、この 1 本から下記 19 宣言すべてに `#check` が通ることを機械確認した:

```
martonJointDistribution / martonInfo₁ / martonRegion / marton_region_subset_capacity
IsUVChannelLaw / isUVChannelLaw_iff / IsUVChannelLaw.map_auxiliaries
uvInfo₁ / uvRegion / bcOuterRegionUV / uvRelabel / uvInfo₁_map_uvRelabel / uvInfoSum₁_map_uvRelabel
compProd_comap_map_prodMap / mutualInfo_map_comp
InformationTheory.Shannon.MAC.mutualInfo_toReal_eq_entropy_form
mutualInfo_chain_rule / mutualInfo_le_of_markov / bc_capacity_subset_uv
```

**判断ログ 11-(i) の教訓の適用**: import の必要性は consumer 表ではなく
**移動先が引かざるを得ない依存の閉包**で決まる。今回はその閉包が `Assembly` 1 本に畳まる。

**`InformationTheory.lean` への追記位置**: `:124` の
`import InformationTheory.Shannon.BroadcastChannel.Classes` の**直後** (BC ブロックの末尾、
`:123` の `OuterBoundUV.Assembly` より後であればよい)。

**代替**: `Assembly.lean` (851 行) に `section MartonBridge` を足す案もある。追加 import ゼロだが、
橋 4 本 + 領域包含で +250 行 ⟹ 1100 行になり `docs/rules/` の 1500 行ガイドには収まるものの、
分割 A で 1588 → 851 に落とした直後に再び膨らませることになる。**新ファイル推奨**。

---

## 8. 攻略順の提案

| step | 何を示すか | 予想行数 | 依存 |
|---|---|---|---|
| **S1** | `martonJointDistribution_isUVChannelLaw` — Marton 法が UV 法である (入替なし) | **50** (実測: probe2 が `sorry` なしで通った) | `compProd_comap_map_prodMap` / `Measure.fst_compProd` |
| **S2** | `IsUVChannelLaw.swap_auxiliaries` — 補助 2 スロットの入替不変性 (一般形) | **30** (実測: probe3 が通った)。置き場は `Region.lean` の `section ChannelLaw` | `map_auxiliaries` の写経 |
| **S3** | `martonUVLaw pV K W : Measure (ℕ × ℕ × α × β₁ × β₂)` の def + `IsProbabilityMeasure` instance + `IsUVChannelLaw` | 40 | S1 / S2 / `map_auxiliaries` / `Fintype.equivFin` |
| **S4** | 4 スロットの同定 3 本 (`martonInfo₁` / `martonInfo₂` / `martonInfoV₁V₂`) | **25** (実測: probe4 が通った) | `mutualInfo_map_comp` / `mutualInfo_toReal_eq_entropy_form` / `uvInfo*_map_uvRelabel` |
| **S5** | 需要 A / 需要 B の情報量不等式 (§6-2) | **150–250** ← 本命 | `mutualInfo_chain_rule` / `mutualInfo_le_of_markov` / `IsMarkovChain` の構成 |
| **S6** | `martonRegion pV K W ⊆ bcOuterRegionUV W` (`@[entry_point]` 候補) | 40 | S3–S5 + `subset_closure` |

**合計 335–435 行。S1–S4 (145 行) は既に scratchpad で全部コンパイルしている** ので、
実質の未知は S5 だけ。

**攻略の分割単位**: S1+S2 で 1 leg (橋の骨格、`@[entry_point]` なし)、S3+S4 で 1 leg、S5+S6 で 1 leg。
S5 で詰んだ場合の退避は `sorry` + `@residual(plan:bc-marton-uv-sum-bound)` で、
**S6 の署名は保ったまま**にする (述語への束ね禁止)。

**壁宣言はしていない** — CLAUDE.md の壁ガードを通した結果、S5 についても
(a) 二段階の結論形検索 (`rg -n -B6 "= entropy .*\+ entropy .*- entropy"` / `condMutualInfo.*≤`) を実施し、
(b) テンプレ補題 `mutualInfo_le_of_markov` (`CondMutualInfo.lean:356`) を名指しして
150–250 行の自作見積りを立てられたので、**壁ではなく「大きいが道のある実装」**と判定する。

---

## 9. Mathlib の壁 — **0 件**

| 候補 | loogle クエリ | 結果 | 判定 |
|---|---|---|---|
| 合成積の**第 1 成分**を写す恒等式 | `ProbabilityTheory.Kernel.comap, MeasureTheory.Measure.compProd, MeasureTheory.Measure.map` | **`Found 0 declarations`** | **壁ではない** — in-project `compProd_comap_map_prodMap` (`CodeToAmbient.lean:346`) が既に埋めており、S1 / S2 の両方がそれで通った (機械確認)。`cause:loogle-blind` の典型で、Mathlib 0-hit は結論に影響しない |
| `klDiv` ベースの条件付き情報量 | `ProbabilityTheory.condDistrib, InformationTheory.klDiv` | **`Found 0 declarations`** | **壁ではない** — `condMutualInfo` は in-project 自作 (`CondMutualInfo.lean:59`) で、必要な補題 (`mutualInfo_chain_rule` / `mutualInfo_le_of_markov` / `condMutualInfo_ne_top`) が揃っている |
| 積測度の入替 | `MeasurableEquiv.prodComm` → `Found 2` / `MeasurableEquiv.prodAssoc` → `Found 12` | 存在するが**不要** | 生ラムダで足りる (probe3 実測) |

**共有 sorry 補題の候補はゼロ** (壁が 0 件なので `docs/audit/audit-tags.md` の共有 sorry パターンの
出番はない)。

---

## 10. 撤退ラインとの距離

| slug | 触れるか | 発動するか | 根拠 |
|---|---|---|---|
| **L-BCO2** (Phase 2 の union が universe 問題で詰む) | **触れる。ただし発動条件の文言が実態とずれている** | **本 leg では不発動**。ただし**別の同格の閉塞が同じ位置にある** | S1–S6 はどれも union を取らないので、橋だけなら L-BCO2 に一切触れない。**等号の難しい向き** (UV 法 → Marton 領域) は §4-B の `Fintype ℕ` で塞がっており、これは universe 問題ではない ⟹ L-BCO2 の発動条件では拾えない。**新しい撤退ラインの提案は §11** |
| **L-BCO3** (等号が Phase 4 の外界の形と噛み合わない) | 触れる | **不発動** | 噛み合わなさの本体は plan §L-BCO3 の注記どおり内界側で、内訳は (i) 符号制約 = `2c938fe0` で解消 / (ii) union なし = Phase 2 / (iii) 全支持仮説 = L-BCO7。本 leg は **(iv) 座標規約のクロス**を追加で潰す。外界の形 (`IsUVChannelLaw` の特徴づけ、判断ログ 9) は**一切触らない** — S2 は `Region.lean` に補題を**足す**だけで既存 5 本の閉包性を壊さない |
| **L-BCO7** (semi-deterministic の全支持仮説 `hW`) | 触れる | **不発動、かつ緩む方向** | S1 の実測仮説は `[IsProbabilityMeasure pV] [IsMarkovKernel K] [IsMarkovKernel W]` のみで、`hpV` / `hK` / `hW` を**1 本も要求しない** (probe2)。⟹ **semi-deterministic チャネルでも橋は成立する**。L-BCO7 が止めているのは内界の**達成側** (`marton_achievability`) であって橋ではない |

---

## 11. 新しい撤退ラインの提案 (L-BCO8)

§4-B は既存のどの slug にも当たらない**新しい閉塞**なので、plan に 1 本足すことを推奨する
(slug 番号は plan 側で確定すること)。

| 項目 | 内容 |
|---|---|
| 発動条件 | 等号の逆包含 (`bcOuterRegionUV W ⊆ ⋃ martonRegion`) を書こうとした段で、`bcOuterRegionUV` の `ℕ` 補助を `martonInfo*` の `[Fintype]` 要求に合わせられない (Carathéodory 型の濃度上界が要る) |
| 機械確認 | probe5 の逐語エラー `failed to synthesize instance of type class Fintype ℕ` |
| 退避先 (degenerate fallback) | **順包含側だけで止める** — `martonRegion pV K W ⊆ bcOuterRegionUV W` (S6) は `Fintype` の側から `ℕ` へ**降りる**向きなので成立する。逆包含は `sorry` + `@residual(plan:bc-marton-uv-cardinality-bound)` で署名を保ったまま残す |
| 禁止事項 | `IsMartonCoverable` のような述語に「逆包含が成り立つ」を束ねて仮説で受ける形は取らない (CLAUDE.md tier 5) |
| 代替の攻め筋 (退避前に 1 度試す) | `martonInfo*` を `ℝ≥0∞` の `mutualInfo` / `condMutualInfo` 版に置き換える定義 pivot。`mutualInfo` は `[Fintype]` を要求しない (`MutualInfo.lean:30`–`:32` 逐語確認) ので型としては通る。ただし `marton_achievability` (`Marton/Achievability.lean:767`) が `martonInfo*` を仮説に持つため、`dep_consumers.sh` で波及を実測してから判断すること |

---

## 12. 出発点の骨格 (`OuterBoundUV/MartonBridge.lean`)

```lean
import InformationTheory.Meta.EntryPoint
import InformationTheory.Shannon.BroadcastChannel.OuterBoundUV.Assembly

/-!
# Broadcast channel — Marton's inner-bound law as a UV channel law

The inner and outer bounds of this development are stated over five-tuple laws of the same type,
`Measure (V₁ × V₂ × α × β₁ × β₂)`, but index the two auxiliaries in opposite order: the outer
information slots read the receiver-2 auxiliary first, the inner ones the receiver-1 auxiliary
first.  This file puts the two on one index by exhibiting the Marton joint law as a channel law
of `W` and reading the outer slots at the swapped law.

## Main statements

* `martonJointDistribution_isUVChannelLaw` — the Marton joint law is a channel law of `W`.
* `IsUVChannelLaw.swap_auxiliaries` — exchanging the two auxiliaries preserves a channel law.
* `marton_region_subset_uv` — Marton's inner bound sits inside the UV outer region.
-/

namespace InformationTheory.Shannon.BroadcastChannel.Marton

open MeasureTheory ProbabilityTheory InformationTheory.Shannon
open InformationTheory.Shannon.BroadcastChannel
open scoped ENNReal BigOperators

variable {V₁ V₂ α β₁ β₂ : Type*}
  [Fintype V₁] [DecidableEq V₁] [Nonempty V₁] [MeasurableSpace V₁] [MeasurableSingletonClass V₁]
  [Fintype V₂] [DecidableEq V₂] [Nonempty V₂] [MeasurableSpace V₂] [MeasurableSingletonClass V₂]
  [Fintype α] [DecidableEq α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β₁] [DecidableEq β₁] [Nonempty β₁] [MeasurableSpace β₁] [MeasurableSingletonClass β₁]
  [Fintype β₂] [DecidableEq β₂] [Nonempty β₂] [MeasurableSpace β₂] [MeasurableSingletonClass β₂]

/-- The Marton joint law is a channel law of `W`. -/
theorem martonJointDistribution_isUVChannelLaw
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    IsUVChannelLaw W (martonJointDistribution pV K W) := by
  sorry

@[entry_point]
theorem marton_region_subset_uv
    (pV : Measure (V₁ × V₂)) [IsProbabilityMeasure pV]
    (K : Kernel (V₁ × V₂) α) [IsMarkovKernel K]
    (W : BCChannel α β₁ β₂) [IsMarkovKernel W] :
    martonRegion pV K W ⊆ bcOuterRegionUV W := by
  sorry

end InformationTheory.Shannon.BroadcastChannel.Marton
```

**注**: `IsUVChannelLaw.swap_auxiliaries` は上のファイルではなく **`Region.lean` の
`section ChannelLaw` (`:142`–`:218` の閉包性 5 本の並び)** に置くのが正しい — `U V` を
`section` var で受けている一般形なので、`V₁ V₂` 固定の本ファイルには収まらない。
その 1 本だけ別ファイルへの patch になる (`Region.lean` は 474 行、追加後も余裕)。

**両ゲートの予告**: S1–S6 のどこかで `sorry` を残す場合は `honesty-auditor`、
`.lean` の宣言 / docstring を触るので必ず `style-auditor` が要る。
`## Main statements` に載る宣言に `@[entry_point]` を付けておくと
`internal-doc` ratchet と衝突しない (plan §後続作業 C-5 が `Classes.lean` で確立した既定手)。
