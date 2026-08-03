# (C2) 側の在庫 — 形式化の受け皿と `Thm7` 側対象 (T3 第 2 次 relay M0)

> **Parent plan**: [bc-open-problem-t3b-plan.md](bc-open-problem-t3b-plan.md)
>
> 確定事実の SoT = [`bc-facts.md`](bc-facts.md) の `## L2 (T3)` / `## L5 (T3)` 節。
> ⚠ **本ファイルはそこから値を複製しない — 参照する**。
> 前 relay の到達点 = [`bc-t3-cardinality-inventory.md`](bc-t3-cardinality-inventory.md) §17
> (⚠ **読むだけ。追記も書き換えもしない**)。
>
> **leg 冒頭宣言 (M0)**: 側 = (C2) / 動かすもの = (C2) 本体の形式化受け皿と `Thm7` 側対象の在庫を
> 結論形で確定し、(C2) の散文が立った瞬間にどこから Lean へ落ちるかを測る

---

## 0. 一行サマリ

**(C2) の受け皿は「無い」のではなく「配線されていない」。** 平面集合版の半計算可能性述語は
**既存の Mathlib 資産だけで今日そのまま書ける** (`IsCompact` + `REPred` + `Primcodable ℚ` +
`Metric.ball`。§8 のスケルトンは実際に出力 0 バイトで通る)。一方 `Thm7` 側の対象は
**in-project に 1 つも無く**、しかも既存の BC 領域 def とは **レートの次元が違う** (§2.4)。
⚠ **その次元をどちらに寄せるかは本 leg では決めない** (§2.5)。

本 leg の型検査 7 ファイル・100 項目のうち、**当初「無い」と出た 16 件のうち 15 件が偽陰性**だった —
原因は Mathlib の不足ではなく **import 閉包の外にあること (13 件)** と **root olean の陳腐化 (2 件)**
である (§9)。⚠ **§4.1 軸 1 の処方 (1 行の型検査で反証を試みる) がそのまま効いた形**である。

---

## 1. 問い A — 平面集合版の計算可能性述語の在庫

### 1.1 結論

- **in-project**: 集合版は **無い**。あるのは `ENNReal` 1 個に対するスカラー版だけで、
  それを集合へ適用しようとするとコンパイラが型不一致で拒否する (§9 R1、実測)。
  中間物 (`ℝ` 版 / ベクトル版 / `Finset` 版) も **無い**。
- **Mathlib**: 「計算可能距離空間」「半計算可能集合」を名前で持つ decl は **無い** (§6)。
  **しかし述語を書くのに要る部品は全部ある** — `REPred` (c.e. 述語)、`Primcodable ℚ`、
  `Metric.ball`、`Metric.IsCover` / `Metric.coveringNumber`、`Metric.hausdorffEDist`、
  `NonemptyCompacts` の Hausdorff 距離空間構造 (§1.3 / §1.4)。
- ⟹ **`IsEffectivelyCompactPlane` は自前で置くが、それは「Mathlib の壁」ではなく定義 1 本である**
  (§8 で実際に型検査済)。⚠ **その定義は `IsCompact s ∧ …` の 2 項**であって被覆の c.e. 性だけでは
  ない ([AH] Definition 2.4.1 逐語。§8 の警告)。

### 1.2 in-project 在庫 (スカラー版と、その周辺)

| 概念 | in-project の現物 | file:line | 逐語署名 (`#check` の出力) | (C2) での扱い |
|---|---|---|---|---|
| スカラーの計算可能性 | `IsComputableENNReal` | `InformationTheory/Shannon/Kolmogorov/OmegaNoncomputable.lean:78` | `InformationTheory.Kolmogorov.IsComputableENNReal : ENNReal → Prop` | **語義の手本**。本体は `∃ a : ℕ → ℕ, Computable a ∧ ∀ n, x ≤ (a n) * 2⁻¹^n + 2⁻¹^n ∧ (a n) * 2⁻¹^n ≤ x + 2⁻¹^n` (facts `## L5 (T3)` 行 4 が逐語の SoT) ⟹ **両側**近似である点に注意 (§1.5) |
| 同族 (floor 版) | `IsFloorComputableENNReal` | 同 `:89` | `InformationTheory.Kolmogorov.IsFloorComputableENNReal : ENNReal → Prop` | 片側化の先例ではない (下からの整数近似) |
| 橋渡し | `isComputableENNReal_of_floor` | 同 `:93` | `@…isComputableENNReal_of_floor : ∀ {x : ENNReal}, IsFloorComputableENNReal x → IsComputableENNReal x` | 参考 |
| 否定側テンプレート | `chaitinOmega_not_computable` | 同 `:589` | `…chaitinOmega_not_computable : ¬IsComputableENNReal …chaitinOmega` | T3-β の**証明の形**の実物 |
| 正例 | `isComputableENNReal_one` | 同 `:539` | `…isComputableENNReal_one : IsComputableENNReal 1` | 退化境界の確認用 |
| **集合版** | — | — | — | ❌ **不在**。§9 R1 でコンパイラが拒否 |
| **`ℝ` 版 / ベクトル版 / `Finset` 版** | — | — | — | ❌ **不在**。`Computable`/`Primrec`/`Partrec` を含む in-project 宣言は全 35 件で**すべて Kolmogorov 家系のスカラーまたは `ℕ`/`List` 上**であり、`ℝ`/`Set`/測度に触れるものは 0 件 (`rg` 実測) |

### 1.3 Mathlib 在庫 — 計算可能性の層 (c.e. 述語まで届く)

| 概念 | Mathlib API | file:line | 逐語署名 / 本体 | (C2) での扱い |
|---|---|---|---|---|
| 計算可能関数 | `Computable` | `Mathlib/Computability/Partrec.lean:240` | `@Computable : {α : Type u_1} → {σ : Type u_2} → [Primcodable α] → [Primcodable σ] → (α → σ) → Prop` | 近似列の計算可能性 |
| 決定可能述語 | `ComputablePred` | `Mathlib/Computability/RE.lean:129` | `@ComputablePred : {α : Type u_1} → [Primcodable α] → (α → Prop) → Prop` | Δ01 側。(C2) には**強すぎる** |
| **c.e. 述語 (Σ01)** | **`REPred`** | `Mathlib/Computability/RE.lean:157` | `def REPred {α} [Primcodable α] (p : α → Prop) := Partrec fun a => Part.assert (p a) fun _ => Part.some ()` | ⭐ **これが (C2) の受け皿の中核**。「有限有理被覆の集合が c.e.」をそのまま書ける |
| 部分計算可能 | `Partrec` | `Mathlib/Computability/Partrec.lean` | `@Partrec : {α} → {σ} → [Primcodable α] → [Primcodable σ] → (α →. σ) → Prop` | `REPred` の下地 |
| **有理数の符号化** | `Primcodable.ofDenumerable` + `Denumerable ℚ` | `Mathlib/Computability/Primrec/Basic.lean:139` / `Mathlib/Data/Rat/Denumerable.lean:30` | `Primcodable.ofDenumerable : (α : Type u_1) → [Denumerable α] → Primcodable α` (priority := 10) | ⭐ **`Primcodable ℚ` は導出可能** (§9 で実測)。`Primcodable (ℚ × ℚ × ℚ)` / `Primcodable (List ((ℚ×ℚ)×ℚ))` も自動で付く |
| 有限行列の符号化 | `Primcodable.finArrow` | `Mathlib/Computability/Primrec/Basic.lean` (instance) | `@Primcodable.finArrow : {α : Type u_1} → [Primcodable α] → {n : ℕ} → Primcodable (Fin n → α)` | 有理チャネル行列 `Fin m → Fin n → ℚ` に付く。⚠ **積を域にすると付かない** (`Fin 3 × Fin 4 → ℚ` は synth 失敗、§9 R8) ⟹ **カリー形で持つこと** |
| 実数の符号化 | — | — | — | ❌ 不在 (`Primcodable ℝ` synth 失敗、§9 R2/R3)。**これは壁ではなく正しい** — 計算可能解析は `ℝ` を符号化せず有理近似で扱う |

### 1.4 Mathlib 在庫 — 有限被覆 / Hausdorff の層 (結論形で数えた)

| 結論形 | Mathlib API | file:line | 逐語署名 / 結論 | (C2) での扱い |
|---|---|---|---|---|
| **有限被覆 (ε-網)** | `Metric.totallyBounded_iff` | `Mathlib/Topology/MetricSpace/Pseudo/Basic.lean:95` | `TotallyBounded s ↔ ∀ ε > 0, ∃ t, t.Finite ∧ s ⊆ ⋃ y ∈ t, Metric.ball y ε` | ⭐ **標的の結論形そのもの**。`t` を有理中心の `Finset` に取り替え、`ε := 2⁻¹^n` を計算可能列にすれば effective 版になる |
| 有限部分被覆 | `IsCompact.elim_finite_subcover` | `Mathlib/Topology/Compactness/Compact.lean:198` | `IsCompact s → ∀ (U : ι → Set X), (∀ i, IsOpen (U i)) → s ⊆ ⋃ i, U i → ∃ t, s ⊆ ⋃ i ∈ t, U i` | 添字 `ι` に計算可能性が乗らないので**そのままでは使えない**。有理球の族に固定して使う |
| コンパクト ⟹ 全有界 | `IsCompact.totallyBounded` | `Mathlib/Topology/UniformSpace/Cauchy.lean` | `IsCompact s → TotallyBounded s` | 周囲空間の全有界性 |
| **被覆述語** | `Metric.IsCover` | `Mathlib/Topology/MetricSpace/Cover.lean:48` | `@Metric.IsCover : {X : Type u_1} → [PseudoEMetricSpace X] → NNReal → Set X → Set X → Prop` (`def IsCover (ε : ℝ≥0) (s N : Set X) : Prop := SetRel.IsCover {(x, y) \| edist x y ≤ ε} s N`) | ⭐ **有限被覆を「集合 `N`」として持つ形**。c.e. 添字と結ぶ相手として最も近い |
| 被覆数 | `Metric.coveringNumber` / `Metric.externalCoveringNumber` | `Mathlib/Topology/MetricSpace/CoveringNumbers.lean:77` / `:71` | `@Metric.coveringNumber : {X} → [PseudoEMetricSpace X] → NNReal → Set X → ℕ∞` | 有効性の**定量化**が要るとき (⚠ (C2) には**不要** — 収束率は落ちる、facts `## L2 (T3)` 行 5) |
| 極小被覆の構成 | `Metric.minimalCover` / `Metric.isCover_minimalCover` / `Metric.finite_minimalCover` | 同 `:253` / `:261` / `:258` | `Metric.isCover_minimalCover : coveringNumber ε A ≠ ⊤ → Metric.IsCover ε A (Metric.minimalCover ε A)`、`Metric.finite_minimalCover : (Metric.minimalCover ε A).Finite` | 具体的な有限被覆を取り出す段 |
| 有限被覆の取り出し | `Metric.exists_set_encard_eq_coveringNumber` | 同 `:234` | `coveringNumber ε A ≠ ⊤ → ∃ C ⊆ A, C.Finite ∧ Metric.IsCover ε A C ∧ C.encard = Metric.coveringNumber ε A` | 同上 |
| **Hausdorff 距離** | `Metric.hausdorffEDist` | `Mathlib/Topology/MetricSpace/HausdorffDistance.lean:258` | `irreducible_def hausdorffEDist (s t : Set α) : ℝ≥0∞ := (⨆ x ∈ s, infEDist x t) ⊔ ⨆ y ∈ t, infEDist y s` | ⚠ **対称 = 両側**。§1.5 の落とし穴 |
| 片側の距離 | `Metric.infEDist` | 同 `:74` | `def infEDist (x : α) (s : Set α) : ℝ≥0∞` | 片側化するならこちら |
| 片側の近傍 | `Metric.thickening` / `Metric.cthickening` | `Mathlib/Topology/MetricSpace/Thickening.lean:51` / `:191` | `def thickening (δ : ℝ) (E : Set α) : Set α` | 「`s ⊆ δ-近傍 (t)`」の片側形 |
| **超空間** | `TopologicalSpace.NonemptyCompacts` + Hausdorff 距離 | `Mathlib/Topology/Sets/Compacts.lean` / `Mathlib/Topology/MetricSpace/Closeds.lean:256`, `:441` | `instance instEMetricSpace : EMetricSpace (NonemptyCompacts α)` / `instance NonemptyCompacts.instMetricSpace : MetricSpace (NonemptyCompacts α)` | コンパクト集合を「点」として扱う路。⚠ ただし §1.5 |
| 超空間の第二可算性 | `TopologicalSpace.NonemptyCompacts.instSecondCountableTopology` | `Mathlib/Topology/MetricSpace/Closeds.lean:281` | `instance [SecondCountableTopology α] : SecondCountableTopology (NonemptyCompacts α)` | 可算稠密族が取れる = 符号化の下地 |
| 超空間の完備性 | `Metric.Closeds.instCompleteSpace` / `NonemptyCompacts.isClosed_in_closeds` | 同 `:116` / `:276` | `IsClosed (Set.range TopologicalSpace.NonemptyCompacts.toCloseds)` | 極限操作が要るとき |
| 有理球による近似を **c.e. 添字集合**として述べた結論 | — | — | — | ❌ **Mathlib に不在** (§6 W1)。ただし §8 のとおり **既存部品で書ける** |

### 1.5 ⚠ 定義の向きの落とし穴 — 両側を選ぶと facts `## L2 (T3)` 行 5 (P1) が壊れる

**(C2) が要求するのは片側 (semicomputable = effectively compact = Π01) であって、両側 (computable
compact set) ではない**。両者を取り違えると、(C2) の同値形を支えている P1 (一様に半計算可能な可算族の
共通部分は半計算可能) が**そのまま偽になる**:

- スカラー版 `IsComputableENNReal` (`OmegaNoncomputable.lean:78`) は `x ≤ … + 2⁻ⁿ ∧ … ≤ x + 2⁻ⁿ` の
  **両側**近似である。その形をそのまま集合へ持ち上げる = Hausdorff 距離で `2⁻ⁿ` 精度、
  すなわち `Metric.hausdorffEDist` (`HausdorffDistance.lean:258` の本体が `⊔` = **対称**) を使う定義。
- ⚠ **そこで得られるのは「計算可能コンパクト集合」であり、共通部分で閉じない**。
  片側 (Π01) は c.e. 添字上の可算共通部分で閉じる (P1 の 2 行証明) が、両側はそうではない。
- ⟹ **受け皿は `REPred`「有限有理被覆が c.e.」で置く** (§8)。⚠ **`hausdorffEDist` から起こしてはならない**。
  ⚠ CLAUDE.md「Mathlib-shape-driven Definitions」がまさにこの形の事故を名指ししている
  — 教科書形 (スカラー版の逐語持ち上げ) を転記すると、消費する側の補題 (P1) が通らなくなる。

---

## 2. 問い B — `Thm7` 側の対象は in-project にあるか

### 2.1 結論

- **`Thm7` に当たる領域 def は in-project に 0 件** (facts `## L5 (T3)` 行 7 と一致。本 leg で
  `rg` + `#check` により再確認)。
- **既存の BC 領域 def は 8 本あり、全部 `Set (ℝ × ℝ)` = 2 レート**。⚠ **`Thm7` は
  レート三つ組 `(R₀, R₁, R₂)` についての定理**である (§2.4、一次文献逐語で確認) ⟹
  **受け皿の型が違う**。
- **`∀T_J` を表す型は要らない — 既存の `Kernel` と `bcAuxAlphabet` で書ける** (§9 で
  `⋃_p ⋂_{T_J} ⋃_{aux}` の入れ子が 0 error で elaborate)。
- **`min` を含む制約束も既存パターンの延長で書ける** (§9、`structure … : Prop` に `min` を入れて通した)。

### 2.2 in-project の領域 def — 逐語署名 (`#check` の実出力)

| 対象 | file:line | 逐語署名 (型クラス列を落とさない) |
|---|---|---|
| チャネル | `InformationTheory/Shannon/BroadcastChannel/Basic.lean:39` | `BCChannel (α β₁ β₂ : Type*) [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂] := Kernel α (β₁ × β₂)` |
| 達成可能性述語 | `Operational.lean:53` | `@…BCAchievable : {α β₁ β₂} → [MeasurableSpace α] → [MeasurableSpace β₁] → [MeasurableSpace β₂] → BCChannel α β₁ β₂ → ℝ → ℝ → Prop` |
| 容量領域 | `Operational.lean:68` | `@…bcCapacityRegion : {α β₁ β₂} → [MeasurableSpace α] → [MeasurableSpace β₁] → [MeasurableSpace β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)` (本体 `closure {p \| BCAchievable W p.1 p.2}`) |
| UV 外界 | `OuterBoundUV/Region.lean:425` | `@…bcOuterRegionUV : {α} → [MeasurableSpace α] → {β₁} → [MeasurableSpace β₁] → {β₂} → [MeasurableSpace β₂] → [StandardBorelSpace α] → [Nonempty α] → [StandardBorelSpace β₁] → [Nonempty β₁] → [StandardBorelSpace β₂] → [Nonempty β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)` |
| UV の 1 法則分 | `OuterBoundUV/Region.lean:413` | `@…uvRegion : … → {U V : Type*} → [MeasurableSpace U] → [MeasurableSpace V] → (ν : Measure (U × V × α × β₁ × β₂)) → [IsFiniteMeasure ν] → Set (ℝ × ℝ)` |
| 協調 (genie) 外界 | `OuterBound.lean:375` | `@…bcOuterRegionCoop : {α β₁ β₂} → [Fintype α] → [MeasurableSpace α] → [MeasurableSpace β₁] → [MeasurableSpace β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)` ⚠ **`Thm7` ではない** |
| Marton (1 指標) | `Operational.lean:127` | `@…Marton.martonRegion : {V₁ V₂ α β₁ β₂} → [Fintype V₁] → [MeasurableSpace V₁] → [Fintype V₂] → [MeasurableSpace V₂] → [MeasurableSpace α] → [Fintype β₁] → [MeasurableSpace β₁] → [Fintype β₂] → [MeasurableSpace β₂] → Measure (V₁ × V₂) → Kernel (V₁ × V₂) α → BCChannel α β₁ β₂ → Set (ℝ × ℝ)` |
| Marton (合併) | `MartonUnion.lean:73` | `@…Marton.martonRegionUnion : {α β₁ β₂} → [MeasurableSpace α] → [Fintype β₁] → [MeasurableSpace β₁] → [Fintype β₂] → [MeasurableSpace β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)` (本体 `closure (⋃ (k₁ k₂ : ℕ) (pV) (_) (K) (_), martonRegion pV K W)`) |
| Marton (基数有界) | `Marton/RegionCardinality.lean:270` | `@…Marton.martonRegionUnionBounded : {α β₁ β₂} → [Fintype α] → [MeasurableSpace α] → [Fintype β₁] → [MeasurableSpace β₁] → [Fintype β₂] → [MeasurableSpace β₂] → BCChannel α β₁ β₂ → Set (ℝ × ℝ)` ⭐ **前 relay の (C1) 側成果。基数を有限個に切った版** |
| 同 (外側だけ有界) | `Marton/RegionCardinality.lean:212` | `@…Marton.martonRegionUnionOuterBounded : (同上) → Set (ℝ × ℝ)` |
| 基数の上限 | `Marton/CardinalityBound.lean:435` | `…Marton.martonAuxBound : (α : Type u_1) → [Fintype α] → ℕ` (`:= Fintype.card α`) |
| 補助アルファベット | `MartonUnion.lean:67` | `…Marton.bcAuxAlphabet : ℕ → Type u_1` (`:= ULift.{u} (Fin (k+1))`) |
| 包含 (内界 ⟹ 容量) | `MartonFullSupport.lean:230` | `@…martonRegionUnion_subset_capacity : … (W : BCChannel α β₁ β₂) [IsMarkovKernel W], (∀ (a : α) (b : β₁ × β₂), 0 < (W a).real {b}) → martonRegionUnion W ⊆ bcCapacityRegion W` |
| 包含 (容量 ⟹ UV) | `OuterBoundUV/Assembly.lean:850` | `@…bc_capacity_subset_uv : … [Fintype α] [MeasurableSingletonClass α] [StandardBorelSpace α] [Nonempty α] … (W : BCChannel α β₁ β₂) [IsMarkovKernel W], bcCapacityRegion W ⊆ bcOuterRegionUV W` |

### 2.3 制約束のパターン — 「相互情報量の線形結合を領域として束ねる」既存形

in-project の定石は **抽象実数スロットを取る `structure … : Prop`** + `{p | InXxx p.1 p.2 (slots)}` +
`closure (⋃ …)` の 3 段である。現物は 4 本:

| 束 | file:line | 逐語 |
|---|---|---|
| `InMartonRegion` | `Marton/Basic.lean:40` | `structure InMartonRegion (R₁ R₂ I₁ I₂ I₁₂ : ℝ) : Prop where bound₁ : R₁ ≤ I₁; bound₂ : R₂ ≤ I₂; boundSum : R₁ + R₂ ≤ I₁ + I₂ - I₁₂` |
| `InBCOuterRegionUV` | `OuterBoundUV.lean:735` | `structure InBCOuterRegionUV (R₁ R₂ I₁ I₂ J₂ J₁ : ℝ) : Prop where bound₁ : R₁ ≤ I₁; bound₂ : R₂ ≤ I₂; sumBound₂ : R₁ + R₂ ≤ J₂; sumBound₁ : R₁ + R₂ ≤ J₁` |
| `InBCCapacityRegion` | `Basic.lean:213` | (2 レート・2 スロット) |
| `InMACCapacityRegion` | `MultipleAccess/Basic.lean:142` | (2 レート・3 スロット) |
| 補助変数つき法則 | `OuterBoundUV/Region.lean:116` | `def IsUVChannelLaw (W : BCChannel α β₁ β₂) (ν : Measure (U × V × α × β₁ × β₂)) : Prop` — **5 つ組の同時分布**を 1 本の測度として持ち、`.smul` / `.add` / `.finsetSum` / `.map_auxiliaries` / `.swap_auxiliaries` / Markov 連鎖の補題群 (`:159`–`:350`) が付いている |

⚠ **4 本とも `min` を含まない**。⚠ **`⋂` (族を渡る共通部分) で定義された領域は in-project に 0 件**
(`rg '⋂' InformationTheory/Shannon/BroadcastChannel/` のヒットは
`OuterBoundUV/Quantization.lean:338` の補助 1 行のみ) — 既存の 8 本はすべて `closure (⋃ …)` である。

### 2.4 ⚠ `Thm7` の逐語形と in-project との差分 4 点

一次文献 `auxrec.txt:1034-1084` (Theorem 7 全文) を本 leg で逐語再確認した。差分は 4 つ:

1. **レートが 3 本**。逐語: "Given a broadcast channel characterized by `T(y,z|x)` and any achievable
   **rate triple `(R₀, R₁, R₂)`**, one can find some input distribution `p(x)` such that **for any
   auxiliary channel `T_{J|X,Y,Z}`**, the following constraints are satisfied" (`:1034-1036`)。
   ⟹ 周囲空間は `Set (ℝ × ℝ × ℝ)`。⚠ **in-project の 8 本はすべて `Set (ℝ × ℝ)` (共通メッセージ
   `R₀` が無い)**。facts `## L2 (T3)` 行 5 / 行 6 の周囲空間 `[0, log|X|]³` はこの 3 レートのことである。
2. **制約が 9 本 + 等式 3 本 + 不等式 3 本、しかも入れ子の `min`**。(18a)–(18i) は
   `min{I(W;Y), I(Ŵ;Y), I(W;Z), I(W̃;Z)}` や
   `min{ I(W̃;Z) + min{0, I(W;Y) − I(W;Z)}, I(W̃;J) + I(Ŵ;Y) − I(Ŵ;J) }` の形 (`:1037-1071`)、
   witness 側に (19a)–(19c) の**等式**と (20a)–(20c) (`:1076-1082`)。
   ⚠ in-project の束は素の線形不等式 3〜4 本 (§2.3)。
3. **補助変数が 9 本**。同時分布は逐語
   `p_{U,V,W,Ũ,Ṽ,W̃,Û,V̂,Ŵ,X,Y,Z,J} = p_{U,V,W,X} p_{W̃,Ũ,Ṽ|X} p_{Ŵ,Û,V̂|X} T_{Y,Z|X} T_{J|X,Y,Z}`
   (`:1074`)。⚠ in-project の `IsUVChannelLaw` は **5 つ組**の法則 (補助 2 本) である。
   基数境界は逐語 "`|W|, |Ŵ|, |W̃| ≤ |X| + 6`, while `|U|, |V|, |Û|, |V̂|, |Ũ|, |Ṽ| ≤ |X| + 1`" (`:1083-1084`)
   で、**`J` には課されていない**。
4. **量化子の入れ子は `∃p ∀T_J ∃aux`** ⟹ 領域は **`⋃_p ⋂_{T_J} ⋃_{aux} S(W,p,T_J,aux)`**
   であって `⋂_{T_J} (⋃_p …)` ではない (facts `## L2 (T3)` 行 6 末尾の訂正が SoT)。
   ⚠ **両方の入れ子がコンパイラを通る**ので、型検査は取り違えを守ってくれない。
   本 leg で両者を書き、`⋃⋂ ⊆ ⋂⋃` の側だけが成り立つことを機械で確認した (§9 T4)。

### 2.5 ⚠ 未決の設計軸 — レートの次元をどちらに寄せるか (**本 leg では決めない**)

§2.4-1 で `Thm7` が 3 レート・in-project が 2 レートと確定したが、**どちらへ寄せるかは本 leg の
判断事項ではない**。⚠ 決めるには「[N13] の (C2) と Marton 最適性予想がそれぞれ 2 レート版と
3 レート版のどちらを主語にしているか」の一次文献 diff が要り、それ無しに選ぶのは
CLAUDE.md「textbook-object strength diff」が名指ししている事故形である。

**選択肢は 2 つ**:

- **(α) 3 レートで受け皿を新設** — `Set (ℝ × ℝ × ℝ)` の領域 def を立て、`Thm7` をそこへ載せる
  (型としては通る、§9 T5)。⚠ in-project の資産 (サンドイッチ 2 本ほか) との接続が別途要る。
- **(β) `R₀ = 0` スライスで既存 2 レート資産に載せる** — `Thm7` の 3 レート領域を `R₀ = 0` で切り、
  既存の `bcCapacityRegion` / `bcOuterRegionUV` と同じ平面で比べる。

**決めるのに要る実測** (⚠ **結論はここに書かない**。`$LIT` の所在は facts `## L2 (T3)` 節の前書きが
SoT で、消えていたら同節の指示どおり L0 / L1 節の URL から再生成する):

- `grep -in "common message\|R0\|three\|rate triple\|private message" $LIT/n13.txt` —
  [N13] が計算可能性を問うている容量領域が**共通メッセージを含むか**。(C2) の主語がここで決まる。
- `grep -in "R0\|common message\|rate triple" $LIT/li21.txt` — [Li21] §VIII の open problem
  (facts `## L3 (T3)` が (C2) と同一の穴と確定させたもの) の主語の次元。
- `grep -in "common message\|UVW\|R0" $LIT/auxrec.txt $LIT/sumofbc.txt` — Marton 最適性予想を
  述べている側の主語の次元 (facts `## L0 (T3)` 行 10 / `## L2 (T3)` の該当行が引いている箇所)。
- ⚠ **Geng らの Remark 1** (facts `## L1 (T3)` 節 F5 行に逐語がある。共通メッセージ版 UVW 外界も
  同時に劣最適になる、という記述) は**どちらの選択肢を採っても効く**ので、diff の材料にはなるが
  決め手にはならない。

**⚠ 落とすと事故になる点**: **(β) を採ると「スライスの effective compactness が 3 レート版から
従うか」が別途要る債務になる**。⚠ **自明ではない** — 半計算可能性は一般には切断で保たれるとは
限らず ((C2) が要求するのは片側の Π01 性なので、超平面との交わりが同じ被覆列で被覆できるかを
別に示す必要がある)、**「従う」と書いてはならない**。⟹ (β) は受け皿の新設を避ける代わりに
**この債務を買う**選択である。

---

## 3. 問い C — §17.4 項目 1 に要る材料 (段のリスト)

⚠ **見積り行数 / leg 数は書かない** (根拠のある実測が無い)。順序は依存関係の順。

**受け皿の段 (問い A 側)**

- (a) **有理球の型と、その指す平面集合** — `RatBall := (ℚ × ℚ) × ℚ` と `ratBallSet`。
  部品はすべて既存 (`Primcodable ℚ` 導出可 / `Metric.ball`)。
- (b) **平面集合の半計算可能性述語** —
  `IsCompact s ∧ REPred fun L : List RatBall ↦ s ⊆ ⋃ b ∈ L, ratBallSet b`。
  ⚠ **片側で置く** (§1.5) / ⚠ **`IsCompact` を落とさない** (§8)。
- (c) **一様版** — 指標 `ι` (`[Primcodable ι]`) について一様。`(∀ i, IsCompact (S i))` と
  `ι × List RatBall` 上の `REPred` の 2 項。
- (d) **チャネルの符号化** — ⚠ **ここが素直に落ちない段である**。`BCChannel α β₁ β₂ = Kernel α (β₁ × β₂)`
  には `Primcodable` が付かない (§9 R7 で実測)。`W` について一様と言うには
  **有理チャネル行列の型** (`Fin m → Fin n → ℚ` はカリー形なら `Primcodable`、§9 R8) を別に置き、
  それと `BCChannel` を結ぶ写像を作る段が要る。
- (e) **(C2) の言明** — 「`C` を共通部分にもつ一様半計算可能な外界の可算族の存在」。
  (b)(c)(d) がそろえば書ける (§8 は (d) を除いた指標一様版まで型検査済)。

**`Thm7` 側の段 (問い B 側)**

- (f) **3 レートの周囲空間へ上げるか、2 レートに射影するかの決定** (§2.4-1)。⚠ **これは技術ではなく
  設計の分岐**であり、**本 leg では決めない** — 未決の軸として §2.5 に立てた。
- (g) **9 本の補助変数を持つ同時分布の法則述語** — `IsUVChannelLaw` (5 つ組) の 12 変数版。
  既存の補題群 (`.map_auxiliaries` / Markov 連鎖) が**そのままの形では効かない**ことの確認が要る。
- (h) **`min` を含む 9 本 + 6 本の制約束** — §9 T3 で `min` 入りの束が elaborate することは確認済。
- (i) **`⋃_p ⋂_{T_J} ⋃_{aux}` の入れ子** — §9 T4 で型検査済。⚠ 入れ子の向きを取り違えない (§2.4-4)。
- (j) **`Thm7(W)` の effective compactness を (b)(c) の述語で述べる段** — facts `## L2 (T3)` 行 6 の
  散文 6 段を Lean へ。⚠ その 6 段は **(L-∃) / (L-∀) の量化子補題**を使う。
  Mathlib にも in-project にも無い (§6 W2)。

**⚠ 落とし穴として明示しておくもの**

- ⚠ 上のリストは**依存の順序であって難度の順序ではない**。(j) の (L-∀) は
  「computably overt」という**片側性の概念**を要求し、それは (b) とは別の述語である。
- ⚠ (f) の分岐が決まるまで、(g)〜(j) の受け皿の型は決まらない。

---

## 4. 前提の箱 — 事故になりやすい前提

- **`REPred` は `[Primcodable α]` を要求する**。`α` に `ℝ` / `Set (ℝ × ℝ)` / `NonemptyCompacts (ℝ × ℝ)`
  / `BCChannel …` を置くと**インスタンス合成で落ちる** (§9 R2 / R3 / R6 / R7 で実測)。
  ⟹ **c.e. の主語は常に有理・有限データ (`List RatBall` / `Fin m → Fin n → ℚ`) に置く**。
- **`Primcodable.finArrow` は域が `Fin n` のときだけ**。`Fin m × Fin n → ℚ` は付かない (§9 R8)
  ⟹ チャネル行列は**カリー形**で持つ。
- **`bcOuterRegionUV` は `[StandardBorelSpace α] [Nonempty α]` を 3 型分要求する**が
  `martonRegionUnion` は要求しない (§2.2 の逐語)。両者を同じ定理で使うなら**和集合**を宣言する
  (先例 = `bc_lessNoisy_capacity_eq_uv`、facts `## L5 (T3)` 行 6)。
- **`martonRegionUnionBounded` は `[Fintype α]` を追加で要求する** (`martonRegionUnion` は要求しない)。
  基数境界 `martonAuxBound α = Fintype.card α` が `Fintype α` に依存するため。
- **`Metric.hausdorffEDist` は対称**。片側が要るなら `Metric.infEDist` / `Metric.thickening` を使う (§1.5)。
- **Hausdorff 距離空間の instance は `Mathlib.Topology.MetricSpace.Closeds` にある**。
  `Mathlib.Topology.Sets.Compacts` だけを import すると型は見えるが距離が付かない (§9 で実測)。

---

## 5. 自前で置く要素 (優先度順)

1. **平面集合の半計算可能性述語** (§3 (a)(b)(c))。推奨実装は §8。
   ⚠ 落とし穴 = 両側で書くこと (§1.5) / **`IsCompact` の conjunct を落として述語を弱めること** (§8)。
2. **チャネルの符号化** (§3 (d))。⚠ 落とし穴 = `Kernel` に `Primcodable` を付けようとすること
   (実数値なので付かない。有理行列の別型を立てて写す)。
3. **3 レート領域への昇格 / 2 レートへの射影の決定** (§2.5、⚠ **未決**)。
   ⚠ 落とし穴 = 一次文献 diff を取らずに選ぶこと / 決めずに (g) 以降へ進むこと。
4. **12 変数の法則述語と `min` 入り制約束** (§3 (g)(h))。⚠ 落とし穴 = `IsUVChannelLaw` の補題群が
   そのまま効くと仮定すること。
5. **量化子補題 (L-∃) / (L-∀)** (§3 (j))。⚠ 落とし穴 = (L-∀) を (L-∃) と同型と見ること
   (overtness という別の片側性が要る)。

---

## 6. Mathlib 壁の列挙

⚠ **本 leg の範囲では、(C2) の受け皿について「Mathlib の壁」は 1 件も立たない**。
「無い」ものはあるが、いずれも**既存部品で書ける** (§8 が型検査で示している) ため、
`@residual(wall:…)` の対象ではなく**自前定義**の対象である。⟹ **共有 sorry 補題の推奨はしない**。

記録のために、名前で探して 0 だったものを挙げる (⚠ **生クエリの 0 を「無い」の根拠にしない** —
結論形クエリと `#check` を併記する。§4.2):

| 不在のもの | 生クエリ | 結論形 / `#check` による裏取り | 判定 |
|---|---|---|---|
| **W1 計算可能解析の層** (computable metric space / semicomputable set) | `Computable, Real` → `Found 0 declarations mentioning Real and Computable.` | `#check @Metric.IsEffectivelyCompact` / `@IsSemicomputable` / `@Metric.IsComputableSet` / `@ComputableMetricSpace` の 4 本すべて `unknown identifier` (§9 R4)。結論形側は `|- TotallyBounded _` が 33 件ヒットするが**どれも計算可能性を含まない** | **不在。ただし壁ではない** — §8 が既存部品だけで述語を構成している |
| W2 量化子補題 (L-∃) / (L-∀) | (該当する Mathlib 語彙が無いので生クエリ不能) | in-project も 0 件 (`rg -ni 'semicomput\|effectively compact\|computably'` → `Kolmogorov/OmegaNoncomputable.lean` の 4 行のみ、facts `## L5 (T3)` 行 5 が SoT) | **不在。自前** |
| W3 `Primcodable ℝ` | `Primcodable, Real` → `Found 0` | `#check (inferInstance : Primcodable ℝ)` → synth 失敗 (§9 R2/R3) | **不在で正しい** (計算可能解析は `ℝ` を符号化しない) |

⚠ **`Primcodable ℚ` を W に加えてはならない**。生クエリ `Primcodable, Rat` は
`Found 0 declarations mentioning Rat and Primcodable.` を返すが、**インスタンスは導出可能**である
(`Primcodable.ofDenumerable` + `Denumerable ℚ`)。⚠ **同じ形の偽陰性がもう 1 件**:
`TopologicalSpace.NonemptyCompacts, EMetric.hausdorffEdist` も `Found 0` だが、
`Closeds.lean:256` に instance が実在する。⟹ **§4.2 の 3 規約のうち「生クエリの 0 を根拠にしない」は
本 leg で 2 回実証された**。

---

## 7. 撤退ラインとの距離

- **§6-1 (M1 の gate が判定不能)** — 本 leg は触れない。M0 は gate だが判定対象は在庫であり、
  `t3-thm7-tightness` の GO/NO-GO には関与しない。**発火しない**。
- **§6-2 (M13 で層 3 に載せられる散文が 1 本も無い)** — ⚠ **距離が縮む方向の材料が出た**。
  facts `## L2 (T3)` 行 6 の散文 (`Thm7(W)` の effective compactness) は**そのままでは層 3 に載らない**
  — §2.4 の差分 4 点 (3 レート / 9 補助 / `min` / 入れ子) と §3 (j) の量化子補題が挟まるからである。
  ⚠ ただし **これは「載せられない」ではない** — 受け皿 (§8) が今日型検査を通ることは実測済で、
  詰まっているのは `Thm7` 側の対象の不在であって受け皿の不在ではない。**現時点では発火しない**。
- **§6-3 (20 leg 使い切り)** — 本 leg は M0 のみ。**発火しない**。
- **§6-4 (配分の撤退ライン)** — 本 leg の側は `(C2)` (gate)。可変枠 M2–M15 は未消化なので
  カウンタの入力は変わらない。**発火しない**。

**⚠ 新しい撤退ラインの提案はしない**。本 leg の結果は「受け皿が無い」ではなく
「受け皿は書けるが `Thm7` 側の対象が無い」であり、退避が要る形の未達には当たらない。

---

## 8. 出発点スケルトン

⚠ **下は本 leg で実際に `lake env lean` に通した内容である** (scratchpad `m0_fix.lean`、
**出力 0 バイト**)。⚠ **`InformationTheory/` へは書いていない** (在庫エージェントの編集境界)。

⚠ **`IsCompact` の conjunct を落としてはならない**。[AH] Definition 2.4.1 の逐語は
"Effectively compact, or semicomputable, if it **is compact and** the set
{ (i₁,…,i_n) ∈ N* : A ⊆ B_{i₁} ∪ … ∪ B_{i_n} } is c.e." (facts `## L2 (T3)` の該当行が SoT) で、
**compactness は定義の一部**である。落とすと述語が弱くなり (開球は 1 枚で自分を覆うので被覆集合が
自明に c.e.)、**(C2) が偽陽性で立つ** — (C2) は「そういう族が存在するか」なので、述語が弱いほど
存在が言いやすくなり、ゴールが勝手に緩む (プラン §0.1-2 / CLAUDE.md「under-hypothesized」)。

```lean
import InformationTheory.Shannon.BroadcastChannel.Operational
import Mathlib.Computability.RE
import Mathlib.Data.Rat.Denumerable

open InformationTheory.Shannon.BroadcastChannel

/-- A rational ball of the plane: rational center, rational radius. -/
abbrev RatBall := (ℚ × ℚ) × ℚ

/-- The plane ball named by a `RatBall`. -/
def ratBallSet (b : RatBall) : Set (ℝ × ℝ) :=
  Metric.ball (((b.1.1 : ℝ), (b.1.2 : ℝ)) : ℝ × ℝ) (b.2 : ℝ)

/-- Effectively compact (semicomputable) plane set: compact, and the finite rational covers
are c.e. -/
def IsEffectivelyCompactPlane (s : Set (ℝ × ℝ)) : Prop :=
  IsCompact s ∧ REPred fun L : List RatBall ↦ s ⊆ ⋃ b ∈ L, ratBallSet b

/-- The same, uniformly in a `Primcodable` index. -/
def IsUniformlyEffectivelyCompactPlane {ι : Type} [Primcodable ι] (S : ι → Set (ℝ × ℝ)) : Prop :=
  (∀ i, IsCompact (S i)) ∧
    REPred fun p : ι × List RatBall ↦ S p.1 ⊆ ⋃ b ∈ p.2, ratBallSet b

variable {α β₁ β₂ : Type} [MeasurableSpace α] [MeasurableSpace β₁] [MeasurableSpace β₂]

/-- (C2), index-uniform half only: a countable uniformly semicomputable family of outer bounds
whose intersection is the capacity region. -/
def C2IndexUniform (W : BCChannel α β₁ β₂) : Prop :=
  ∃ O : ℕ → Set (ℝ × ℝ),
    IsUniformlyEffectivelyCompactPlane O ∧
    (⋂ k, O k) = bcCapacityRegion W
```

⚠ **「各 `O k` が `C` を含む」を conjunct に足さない** — 共通部分の等式から従う (機械確認済:
`example (C) (O) (h : (⋂ k, O k) = C) (k) : C ⊆ O k := by rw [← h]; exact Set.iInter_subset O k`)。
冗長な conjunct は署名を読むときに「別の債務がある」と誤読させる。

⚠ **`C2IndexUniform` は (C2) そのものではない** — `W` についての一様性が抜けている (§3 (d))。
⚠ **これを (C2) の形式化と書いてはならない** (プラン §0.1-2)。

---

## 9. 反証を試みた型検査の一覧 (実測)

scratchpad 7 ファイル / 100 項目。⚠ **「無い」と書く前に必ず 1 行の型検査を書いた** (§4.1 軸 1)。

| # | 試した主張 | 結果 |
|---|---|---|
| R1 | スカラー版を平面集合に適用できる (`IsComputableENNReal (∅ : Set (ℝ × ℝ))`) | ❌ **拒否**: `Application type mismatch: The argument ∅ has type Set (ℝ × ℝ) but is expected to have type ENNReal` |
| R2 | `Computable` を `ℕ → Set (ℝ × ℝ)` に使える | ❌ **拒否**: `failed to synthesize Primcodable (Set (ℝ × ℝ))` |
| R3 | `ComputablePred` を `ℝ × ℝ` 上の述語に使える | ❌ **拒否**: `failed to synthesize Primcodable (ℝ × ℝ)` |
| R4 | Mathlib に名前で在る (`Metric.IsEffectivelyCompact` / `IsSemicomputable` / `Metric.IsComputableSet` / `ComputableMetricSpace`) | ❌ **4 本とも拒否**: `unknown identifier` |
| R5 | c.e. 述語の層は在る (`ComputablePred` / `Nat.Partrec` / `Partrec`) | ✅ **通った** (正の対照)。⚠ 名前は `REPred` であって `RePred` ではない (綴りで 1 回外した) |
| R6 | `Computable` を超空間の点列に使える | ❌ **拒否**: `failed to synthesize Primcodable (TopologicalSpace.NonemptyCompacts (ℝ × ℝ))` |
| R7 | チャネルを `Primcodable` として `W` 一様を書ける | ❌ **拒否**: `failed to synthesize Primcodable (BCChannel Bool Bool Bool)` |
| R8 | 有理チャネル行列を積の域で符号化できる | ❌ **拒否**: `failed to synthesize Primcodable (Fin 3 × Fin 4 → ℚ)`。⚠ **カリー形 `Fin 3 → Fin 4 → ℚ` は通る** |
| T1 | 有理球の有限リストの計算可能列が書ける | ✅ **通った** (`Computable (f : ℕ → List ((ℚ × ℚ) × ℚ))`) |
| T2 | Σ01 の被覆形が `Set (ℝ × ℝ)` について書ける | ✅ **通った** (被覆の c.e. 性の部分。⚠ これだけでは述語が弱い → T6) |
| T6 | [AH] Def 2.4.1 どおり `IsCompact` を conjunct に足した版と、その一様版 `(∀ i, IsCompact (S i)) ∧ REPred …` が書ける | ✅ **通った** (`m0_fix.lean`、**出力 0 バイト**)。§8 がこの形 |
| T7 | `(∀ k, C ⊆ O k)` は `(⋂ k, O k) = C` から従う (⟹ conjunct として冗長) | ✅ **通った** (`rw [← h]; exact Set.iInter_subset O k`、sorry なし) |
| T3 | `min` / 入れ子 `min` を含む制約束が既存パターンで書ける | ✅ **通った** (`structure InThm7Region … boundSum : R₀+R₁+R₂ ≤ min iWY iWZ + min (…) (…)`) |
| T4 | `⋃_p ⋂_{T_J} ⋃_{aux}` と `⋂_{T_J} ⋃_p ⋃_{aux}` の**両方**が elaborate し、成り立つ包含は前者 ⊆ 後者だけ | ✅ **両方通り、包含も証明できた** ⟹ ⚠ **型検査は入れ子の取り違えを守らない** (§2.4-4) |
| T5 | 3 レートの周囲空間 `Set (ℝ × ℝ × ℝ)` が使える | ✅ **通った** |

**⚠ 予想外に通ったもの (最優先の報告事項) — 当初 16 件の「拒否」のうち 15 件が偽陰性**

| 当初の拒否 | 真因 | 再試験の結果 |
|---|---|---|
| `Primcodable ℚ` / `Primcodable (ℚ × ℚ × ℚ)` / `Primcodable (List ((ℚ×ℚ)×ℚ))` | `import InformationTheory` の閉包に `Mathlib.Data.Rat.Denumerable` が無いだけ | ✅ **3 件とも通る** (`Primcodable.ofDenumerable` 経由) |
| `EMetricSpace` / `MetricSpace` / `SecondCountableTopology` on `NonemptyCompacts (ℝ × ℝ)` | 同上 (`Mathlib.Topology.MetricSpace.Closeds` が閉包外) | ✅ **3 件とも通る** |
| `Metric.IsCover` / `coveringNumber` / `externalCoveringNumber` / `minimalCover` / `isCover_minimalCover` / `finite_minimalCover` | 同上 (`Cover.lean` / `CoveringNumbers.lean` が閉包外) | ✅ **6 件とも通る** |
| `EMetric.NonemptyCompacts.isClosed_in_closeds` | 同上 | ✅ **通る** (deprecated 警告つき。新名は `TopologicalSpace.NonemptyCompacts.isClosed_in_closeds`) |
| `Marton.martonRegionUnionBounded` / `martonRegionUnionOuterBounded` | ⚠ **root olean の陳腐化** (`.lake/build/lib/lean/InformationTheory.olean` が当該モジュールの olean より古い) | ✅ **モジュールを直接 import すると通る** |
| `TopologicalSpace.NonemptyCompacts.dist_eq` | 名前が違う (`Metric` 名前空間側) | ❌ 唯一の真の外れ |

⚠ **root olean が陳腐化している** — `scripts/dep_*.sh` も root olean を読むので、
`lake build InformationTheory` で 1 度更新するまで「unknown declaration」を返しうる。
