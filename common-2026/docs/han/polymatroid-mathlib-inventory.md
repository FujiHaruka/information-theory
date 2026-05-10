# Polymatroid: Mathlib インベントリ サブ計画 (Phase 0)

> **Parent**: [`polymatroid-moonshot-plan.md`](polymatroid-moonshot-plan.md) §Phase 0
>
> **Status (2026-05-11):** 起草。loogle index (`.lake/build/loogle.index`) + Mathlib 直 grep
> でホットスポット 6 軸を機械的に確認した結果を記録。各候補補題は **CLAUDE.md「Subagent
> Inventory of Mathlib Lemmas」規約** (位置 / 完全シグネチャ / 引数 / 結論形 / 使い所) に
> 従って verbatim 記録する。

## 進捗

- [x] 軸 1: `Polymatroid` / `Submodular` (集合関数版) structure 不在の確認 ✅
- [x] 軸 2: `Fin 0 → α ≃ Unit` 系 (空集合からの Pi 値) ✅
- [x] 軸 3: 集合論的 reshape (Pi 値同値、`MeasurableEquiv.piFinsetUnion`) ✅
- [x] 軸 4: `jointEntropySubset_chain_rule` 流用形 (本 project 内) ✅
- [x] 軸 5: `condEntropy` non-increasing in conditioner (本 project / Mathlib) ✅
- [x] 軸 6: `jointEntropySubset_mono` 系の既存補題確認 (本 project) ✅

## ゴール / Approach

6 軸の調査結果を **Phase A skeleton (`Common2026/Shannon/Polymatroid.lean` の sorry-driven 出だし) が書ける状態** に持っていく。各軸で「Mathlib にあるか / ないか / 既存補題で代用可」の 1 行結論 + 採用する具体補題シグネチャを verbatim 記録。

### 結論サマリ

| 軸 | 結果 | Phase 影響 |
|---|---|---|
| (1) Polymatroid / 集合関数 Submodular structure | **Mathlib 不在を裏取り済み**。Matroid rank 文脈の補題のみ存在 | 本 plan の 3 性質単発で publish 可。structure 化は Phase D で判断 |
| (2) Empty Pi reshape | `Pi.uniqueOfIsEmpty` + `MeasurableEquiv.ofUniqueOfUnique` で自動発火、HanD chain rule base case と同じパターン | Phase A は写経で 15〜25 行 |
| (3) `S ∪ T = S ⊔ (T \ S)` Pi 値同値 | **Mathlib `MeasurableEquiv.piFinsetUnion` 直接利用可**。Phase D の自前 `subsetSplitMEquiv` を上流補題に置き換える選択肢あり | Phase B / C の reshape は Mathlib 標準 + Pi.lean で完結 |
| (4) Chain rule 流用形 | `jointEntropySubset_chain_rule` (HanD.lean) は order-prefix 形、本 plan で必要な「pair / triple 形」とは reshape 1 段ぶん違う。pair 形 `entropy_pair_eq_entropy_add_condEntropy` (Entropy.lean) を直接利用する方が短い | Phase C の chain 展開は **subset 版を呼ばず pair 版を 3 段** で済ます方針 |
| (5) Conditioning monotonicity | `condEntropy_le_condEntropy_of_pair` (Entropy.lean) が **直接** Phase C で使える形。`condEntropy_subset_anti` (HanD.lean) は subset 版だが本 plan には不要 | Phase C の核は pair 版で 1 行 |
| (6) Project 内 monotonicity 補題 | `jointEntropySubset_mono` 不在を確認 (Han Phase D / Loomis–Whitney 内に部分実装無し) | Phase B 必須、新規実装 |

## Phase 詳細

### 軸 1: `Polymatroid` / `Submodular` (集合関数版) structure

#### 結論 (1 行)

**Mathlib に集合関数版 `Polymatroid` / `Submodular` structure はいずれも不在を裏取り済み**。Matroid rank の文脈で submodularity 補題のみ立っている (本 plan のインスタンス登録対象には不適)。

#### 確認手順

```bash
export PATH=$HOME/.elan/bin:$PATH
./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Polymatroid"
# → unknown identifier 'Polymatroid'

./.lake/packages/loogle/.lake/build/bin/loogle --read-index .lake/build/loogle.index "Submodular"
# → unknown identifier 'Submodular'

rg -i "polymatroid|submodular" .lake/packages/mathlib/Mathlib/ -l
# → 0 件 (集合関数 structure として)
# → ヒット 3 ファイル: Mathlib/Combinatorics/Matroid/Rank/{Cardinal,ENat}.lean,
#                    Mathlib/Combinatorics/Additive/VerySmallDoubling.lean
```

#### Mathlib に存在する submodularity 補題 (参考、本 plan のインスタンス対象には不適)

##### `Matroid.eRk_inter_add_eRk_union_le`
- **位置**: `Mathlib/Combinatorics/Matroid/Rank/ENat.lean` (file 内コメント `/-! ### Submodularity -/` 節)
- **シグネチャ抜粋** (Matroid.eRk は `Set α → ℕ∞` 値、Phase Phase plan の `Finset _ → ℝ` とは型が違う):
  ```
  the function `M.eRk` is submodular.
  ```
- **使い所**: 本 plan では使わない (entropy は `ℝ` 値、Matroid rank は `ℕ∞` 値で統合不可)

##### `Matroid.cRk_inter_add_cRk_union_le`
- **位置**: `Mathlib/Combinatorics/Matroid/Rank/Cardinal.lean`
- **使い所**: 同上、本 plan では参考のみ

#### Phase 影響

- **Phase A〜C は予定通り進める**。3 性質単発 theorem で publish 価値あり
- **Phase D の structure 化判断**: 既存 `Polymatroid` がない以上、独立した structure 導入になる。本 plan 内で軽量 `def` (D-a) にするか、独立 plan に切り出す (D-b) かは Phase D 着手時に再評価。デフォルトは (D-b)
- **Mathlib upstream PR 候補**: `Polymatroid` structure + `Matroid.IsBase.toPolymatroid` (matroid rank → polymatroid) は副産物として Mathlib 候補だが、本 plan のスコープ外

---

### 軸 2: `Fin 0 → α ≃ Unit` 系 (空集合からの Pi 値)

#### 結論 (1 行)

**`Pi.uniqueOfIsEmpty` (Mathlib) で `(↥(∅ : Finset (Fin n)) → α)` は `Unique`、`Real.negMulLog_one = 0` で entropy = 0**。HanD chain rule base case (`Han.lean:64-85`) と同じパターンで写経可。

#### 採用候補

##### `Pi.uniqueOfIsEmpty`
- **位置**: `Mathlib/Logic/Unique.lean` (Pi instance 周辺)
- **シグネチャ** (確認済、verbatim):
  ```
  instance Pi.uniqueOfIsEmpty (β : α → Type*) [IsEmpty α] : Unique (∀ a, β a)
  ```
- **使い所**: `IsEmpty (↥(∅ : Finset (Fin n)))` から `Unique ((↥(∅ : Finset (Fin n))) → α)` を取り出す。empty Finset の subtype は `IsEmpty` (Mathlib `Finset.isEmpty_coe_sort` / `Finset.notMem_empty` 経由)

##### `MeasurableEquiv.ofUniqueOfUnique`
- **位置**: `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:365`
- **シグネチャ** (verbatim):
  ```
  /-- Any two types with unique elements are measurably equivalent. -/
  def ofUniqueOfUnique (α β : Type*) [MeasurableSpace α] [MeasurableSpace β]
      [Unique α] [Unique β] : α ≃ᵐ β where
    toEquiv := ofUnique α β
  ```
- **引数**: `α β : Type*` explicit, `[MeasurableSpace α] [MeasurableSpace β] [Unique α] [Unique β]` instance
- **結論形**: `α ≃ᵐ β`
- **使い所**: 直接の利用は不要。empty Pi 上の entropy 計算は Han.lean の base case 流儀 (`Fintype.sum_unique` + `negMulLog_one`) で書く方が短い

##### `Real.negMulLog_one` (代数 building block)
- **位置**: `Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean` 周辺
- **シグネチャ**:
  ```
  @[simp] theorem Real.negMulLog_one : Real.negMulLog 1 = 0
  ```
- **使い所**: Phase A の最後の代数。`(μ.map _).real {default} = 1` を示した後 1 行で潰す

#### Phase A skeleton 着手判定

**問題なし**。Han.lean chain rule base case (line 64-85) を写経し subset 版 (`(↥(∅ : Finset (Fin n)) → α)`) に書き換えるだけ。

万一 instance が未発火なら以下の workaround:
- `Finset.isEmpty_coe_sort.mpr Finset.notMem_empty` で `IsEmpty` を明示
- `(↥(∅ : Finset (Fin n)) → α)` を `MeasurableEquiv.ofUniqueOfUnique _ Unit` で `PUnit` に潰してから entropy 計算

---

### 軸 3: 集合論的 reshape (Pi 値同値)

#### 結論 (1 行)

**Mathlib `MeasurableEquiv.piFinsetUnion` (`.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:612`) が `Disjoint s t` 仮定で `((∀ i : s, π i) × ∀ i : t, π i) ≃ᵐ ∀ i : (s ∪ t : Finset δ'), π i` を直接提供**。Phase D `subsetSplitMEquiv` (HanD.lean:69) は本 plan では不要で、Mathlib 標準補題で reshape 可能。

#### 採用候補

##### `MeasurableEquiv.piFinsetUnion`
- **位置**: `Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:612`
- **シグネチャ** (verbatim):
  ```
  /-- The measurable equivalence `(∀ i : s, π i) × (∀ i : t, π i) ≃ᵐ (∀ i : s ∪ t, π i)`
    for disjoint finsets `s` and `t`. `Equiv.piFinsetUnion` as a measurable equivalence. -/
  def piFinsetUnion [DecidableEq δ'] {s t : Finset δ'} (h : Disjoint s t) :
      ((∀ i : s, π i) × ∀ i : t, π i) ≃ᵐ ∀ i : (s ∪ t : Finset δ'), π i :=
    letI e := Finset.union s t h
    MeasurableEquiv.sumPiEquivProdPi (fun b ↦ π (e b)) |>.symm.trans <|
      .piCongrLeft (fun i : ↥(s ∪ t) ↦ π i) e
  ```
- **引数**: `δ' : Type*` (implicit, with `[DecidableEq δ']`), `s t : Finset δ'` (implicit), `h : Disjoint s t` (explicit), `π : δ' → Type*` (implicit, with `[∀ a, MeasurableSpace (π a)]`)
- **結論形** (verbatim):
  ```
  ((∀ i : s, π i) × ∀ i : t, π i) ≃ᵐ ∀ i : (s ∪ t : Finset δ'), π i
  ```
- **使い所**: Phase B / C の核。`s = S`, `t = T \ S` で `Disjoint S (T \ S)` (= `Finset.disjoint_sdiff`) から発火。Phase B では 1 段、Phase C では `Disjoint (S ∩ T) (S \ T)` + `Disjoint ((S ∩ T) ∪ (S \ T)) (T \ S)` の 2 段で 3 ピース化

##### `Finset.disjoint_sdiff`
- **位置**: `Mathlib/Data/Finset/Basic.lean:271`
- **シグネチャ** (verbatim):
  ```
  theorem disjoint_sdiff : Disjoint s (t \ s) :=
    sdiff_disjoint.symm
  ```
- **引数**: `s t : Finset α` (implicit, おそらく semi-implicit)
- **結論形**: `Disjoint s (t \ s)`
- **使い所**: Phase B `T = S ⊔ (T \ S)` 分解で `Disjoint S (T \ S)` を取り出すために 1 行で

##### `Finset.disjoint_sdiff_inter`
- **位置**: `Mathlib/Data/Finset/Basic.lean:274`
- **シグネチャ** (verbatim):
  ```
  theorem disjoint_sdiff_inter (s t : Finset α) : Disjoint (s \ t) (s ∩ t) :=
    disjoint_of_subset_right inter_subset_right sdiff_disjoint
  ```
- **引数**: `s t : Finset α` (explicit)
- **結論形**: `Disjoint (s \ t) (s ∩ t)`
- **使い所**: Phase C で `S = (S ∩ T) ⊔ (S \ T)` 分解の disjoint 確認

##### `Finset.union_sdiff_of_subset`
- **位置**: `Mathlib/Data/Finset/SDiff.lean:72`
- **シグネチャ** (verbatim):
  ```
  theorem union_sdiff_of_subset (h : s ⊆ t) : s ∪ t \ s = t := by grind
  ```
- **引数**: `s t : Finset α` (implicit), `h : s ⊆ t` (explicit)
- **結論形**: `s ∪ t \ s = t`
- **使い所**: Phase B で `S ⊆ T` から `S ∪ (T \ S) = T` を取り出し、`piFinsetUnion` の出力 type `(↥(S ∪ (T \ S)) → α)` を `(↥T → α)` に cast するために必要

##### `Finset.inter_union_sdiff` (Phase C 用、要追加裏取り)
- **位置**: 推定 `Mathlib/Data/Finset/SDiff.lean` 周辺。`(S ∩ T) ∪ (S \ T) = S` の形。`union_sdiff_of_subset (Finset.inter_subset_left)` で導出可
- **使い所**: Phase C で `S = (S ∩ T) ⊔ (S \ T)` の cast。直接補題が無くても `union_sdiff_of_subset` 経由で 2〜3 行で出る

##### `Equiv.Finset.union` (低レベル代替、`piFinsetUnion` で隠蔽済)
- **位置**: `Mathlib/Data/Finset/Basic.lean:582`
- **シグネチャ** (verbatim):
  ```
  /-- The disjoint union of finsets is a sum -/
  def Finset.union (s t : Finset α) (h : Disjoint s t) :
      s ⊕ t ≃ (s ∪ t : Finset α) :=
    Equiv.setCongr (coe_union _ _) |>.trans (Equiv.Set.union (disjoint_coe.mpr h)) |>.symm
  ```
- **使い所**: `piFinsetUnion` の中で使われている低レベル equiv。本 plan で直接利用は不要

#### Phase D `subsetSplitMEquiv` との関係

`HanD.lean:69` の `subsetSplitMEquiv` は `T₁ ⊆ T₂` 仮定の下で `((↥T₁ → α) × (↥(T₂ \ T₁) → α)) ≃ᵐ (↥T₂ → α)` を構成 (Pi reshape 全 50 行強の自前定義)。**これと `MeasurableEquiv.piFinsetUnion` は機能的に同等** (前者は `T₁ ⊆ T₂` 仮定、後者は `Disjoint s t` 仮定で同じ Pi 値同値を作る)。

**判断**: 本 plan では Mathlib `piFinsetUnion` を直接採用。`HanD.lean` の `subsetSplitMEquiv` は HanD 内 private なので import 不可、再利用するには公開化が必要。Mathlib 版を使う方が import チェーンが軽い。

#### Phase 影響

Phase B / C の reshape 部分は Mathlib 標準補題 + `entropy_measurableEquiv_comp` (Pi.lean) で構成可。新規 `MeasurableEquiv` 自前実装は不要。

---

### 軸 4: `jointEntropySubset_chain_rule` 流用形

#### 結論 (1 行)

**`HanD.jointEntropySubset_chain_rule` (`HanD.lean:257`) は order-prefix 形 (`H(X_S) = ∑_{i ∈ S, ordered} H(X_i | X_{S∩<i})`) で、本 plan で必要な「pair / triple 形」とは reshape 1 段ぶん違う**。本 plan では subset 版 chain rule を呼ばず、`entropy_pair_eq_entropy_add_condEntropy` (Entropy.lean:41) を 2〜3 段ネストして展開する方が短い。

#### 採用候補

##### `InformationTheory.Shannon.entropy_pair_eq_entropy_add_condEntropy`
- **位置**: `Common2026/Shannon/Entropy.lean:41`
- **シグネチャ** (verbatim):
  ```
  theorem entropy_pair_eq_entropy_add_condEntropy
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Ω → X) (Yo : Ω → Y)
      (hXs : Measurable Xs) (hYo : Measurable Yo) :
      entropy μ (fun ω => (Xs ω, Yo ω))
        = entropy μ Xs + InformationTheory.MeasureFano.condEntropy μ Yo Xs
  ```
- **引数**: `μ : Measure Ω` explicit, `Xs : Ω → X` explicit, `Yo : Ω → Y` explicit, `hXs hYo : Measurable _` explicit; instance `[IsProbabilityMeasure μ]` + 標準 `[Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X] [MeasurableSingletonClass X]` × Y 同
- **結論形** (verbatim):
  ```
  entropy μ (fun ω => (Xs ω, Yo ω))
    = entropy μ Xs + InformationTheory.MeasureFano.condEntropy μ Yo Xs
  ```
- **使い所**:
  - Phase B: `H(X_T) = H((X_S, X_{T\S})) = H(X_S) + H(X_{T\S} | X_S)` (1 段適用)
  - Phase C: `H(X_S) = H(X_I) + H(X_A | X_I)`, `H(X_T) = H(X_I) + H(X_B | X_I)`, `H(X_{S∪T}) = H(X_I) + H(X_A | X_I) + H(X_B | X_I, X_A)` (1〜2 段ネスト)

##### `InformationTheory.Shannon.jointEntropySubset_chain_rule` (使わない方針、参考)
- **位置**: `Common2026/Shannon/HanD.lean:257`
- **シグネチャ抜粋**:
  ```
  jointEntropySubset μ Xs S
    = ∑ i ∈ S, condEntropy μ (Xs i) (fun ω (j : (S.filter (· < i))) => Xs j.val ω)
  ```
- **使い所**: 本 plan では呼ばない。order-prefix 形なので Phase C の 3-piece 分解とは別流儀。`entropy_pair_eq_entropy_add_condEntropy` の方が submodularity 証明には素直

#### Phase 影響

Phase C の各 entropy 展開は **`entropy_pair_eq_entropy_add_condEntropy` を 1〜2 段ネスト**で済ます。各 entropy 展開後に Pi 値 reshape (`entropy_measurableEquiv_comp`) を 1 段挟む形になる。`jointEntropySubset_chain_rule` を呼ぶのは Phase C の代替経路 (3-piece chain) に切り替えたときのみ。

---

### 軸 5: `condEntropy` non-increasing in conditioner

#### 結論 (1 行)

**`condEntropy_le_condEntropy_of_pair` (`Entropy.lean:240`) が Phase C で直接利用可能**。subset 版 (`condEntropy_subset_anti`, HanD.lean) は本 plan では呼ばない。

#### 採用候補

##### `InformationTheory.Shannon.condEntropy_le_condEntropy_of_pair`
- **位置**: `Common2026/Shannon/Entropy.lean:240`
- **シグネチャ** (verbatim):
  ```
  theorem condEntropy_le_condEntropy_of_pair
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : Ω → X) (Yo : Ω → Y) (Zo : Ω → Z)
      (hXs : Measurable Xs) (hYo : Measurable Yo) (hZo : Measurable Zo) :
      InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
        ≤ InformationTheory.MeasureFano.condEntropy μ Xs Yo
  ```
- **引数**: `μ` explicit, `Xs Yo Zo` explicit, `hXs hYo hZo : Measurable _` explicit; instance `[IsProbabilityMeasure μ]` + 標準 Fintype etc × X / Y / Z
- **結論形** (verbatim):
  ```
  InformationTheory.MeasureFano.condEntropy μ Xs (fun ω => (Yo ω, Zo ω))
    ≤ InformationTheory.MeasureFano.condEntropy μ Xs Yo
  ```
- **使い所**: Phase C の核。`X = X_B` (= `X_{T\S}`), `Y = X_I` (= `X_{S∩T}`), `Z = X_A` (= `X_{S\T}`) で発火、`H(X_B | X_I, X_A) ≤ H(X_B | X_I)` を 1 行で

##### `condEntropy_subset_anti` (使わない方針、参考)
- **位置**: `Common2026/Shannon/HanD.lean:328`
- **シグネチャ抜粋**:
  ```
  T₁ ⊆ T₂ ⟹
    condEntropy μ (Xs i) (fun ω (j : T₂) => Xs j.val ω)
      ≤ condEntropy μ (Xs i) (fun ω (j : T₁) => Xs j.val ω)
  ```
- **使い所**: 本 plan では使わない。subset 版で書くと Phase C の chain 展開と整合させる reshape が必要、pair 版直接の方が短い

#### Phase 影響

Phase C の conditioning monotonicity は `condEntropy_le_condEntropy_of_pair` を 1 回呼ぶだけ。reshape が pair 形と整合するように chain 展開を組むのが核となる。

---

### 軸 6: `jointEntropySubset_mono` 系の既存補題確認 (本 project)

#### 結論 (1 行)

**Common2026 内に `jointEntropySubset_mono` (target side monotonicity in `S`) 系の補題は不在**。Han Phase D ではあくまで `condEntropy_subset_anti` (conditioner side anti-monotonicity) のみで、target side は未実装。Loomis–Whitney の `jointEntropySubset_le_log_projectionExcept_card` も用途違い。Phase B で新規実装。

#### 確認手順

```bash
rg "jointEntropySubset_mono\|jointEntropySubset.*subset\|subset.*jointEntropySubset" Common2026/
# → 0 件 (定義側 jointEntropySubset_univ / chain_rule / except のみ)

rg "S ⊆ T.*jointEntropySubset\|jointEntropySubset μ Xs S ≤ jointEntropySubset" Common2026/
# → 0 件
```

#### 関連既存補題 (Phase B 実装時の参考)

##### `InformationTheory.Shannon.jointEntropySubset_univ`
- **位置**: `Common2026/Shannon/HanD.lean:121`
- **シグネチャ**:
  ```
  theorem jointEntropySubset_univ
      (μ : Measure Ω) (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
      jointEntropySubset μ Xs Finset.univ = jointEntropy μ Xs
  ```
- **使い所**: 本 plan では `S = univ` の特殊化が必要なら 1 行で利用可。直接の用途は限定的

##### `InformationTheory.Shannon.condEntropy_subset_anti`
- **位置**: `Common2026/Shannon/HanD.lean:328`
- **使い所**: 軸 5 で記録通り、本 plan では使わない

#### Phase 影響

Phase B `jointEntropySubset_mono` を新規実装。ルート α (`piFinsetUnion` で 1 段) を採用、30〜50 行見積。

---

## Phase A 着手時の不確実性ランク

| 項目 | 不確実性 | 対処 |
|---|---|---|
| `Pi.uniqueOfIsEmpty` の `(↥(∅ : Finset (Fin n)) → α)` への発火 | **低** | HanD chain rule base case (Han.lean:64-85) と同じパターン、`Fintype.sum_unique` + `negMulLog_one` で潰す |
| `Finset.isEmpty_coe_sort` 系 instance の自動発火 | **低** | `Subtype` instance の Mathlib 標準、未発火なら `Finset.notMem_empty` で明示 |
| `MeasurableEquiv.piFinsetUnion` の本 project context での発火 | **中** | Phase B 着手時に最小例 (`S = {0}`, `T = {0, 1}`) で smoke test。`[DecidableEq (Fin n)]` instance 必要 (自動発火見込み) |
| `Finset.union_sdiff_of_subset` 経由の type cast | **中** | `(↥(S ∪ (T \ S)) → α) = (↥T → α)` の defeq か `Eq.mpr` 1 段が必要。`congrArg` で迂回可 |
| Phase C 3-piece reshape の associativity (`((∩) ∪ (S\T)) ∪ (T\S) = S ∪ T`) | **中-高** | `Finset.union_assoc` + `union_sdiff_of_subset` 2 段で導く。詰まったら `Finset.disjoint_sdiff_inter` を片手に手動 ext |
| Phase C `H(X_{S∪T})` の triple chain 展開 | **中** | `entropy_pair_eq_entropy_add_condEntropy` を 2 段ネスト。`(X_I, X_A, X_B) ≃ ((X_I, X_A), X_B)` の MeasurableEquiv 1 段が必要 (Mathlib `MeasurableEquiv.prodAssoc` 系で 1 行) |

## 全体的な Phase A〜C 工数 (再見積もり)

シードカードの「1〜2 週間 / 300〜400 行」を以下に細分化:

| Phase | 当初見積 (シード) | 再見積 (inventory 後) |
|---|---|---|
| Phase 0 | 1 ターン | 1 ターン (本 ファイル + plan 反映) |
| Phase A | — | 1〜2 日 / 15〜25 行 (HanD base case 写経) |
| Phase B | — | 2〜3 日 / 30〜50 行 (`piFinsetUnion` + pair chain rule + `condEntropy ≥ 0`) |
| Phase C | — | 5〜7 日 / 150〜250 行 (3-piece reshape + 3 段 chain + linarith) |
| Phase D (オプション) | — | 0〜1 日 / 0〜40 行 (D-a 採用時のみ) |
| **合計** | 1〜2 週間 / 300〜400 行 | **1〜2 週間 / 195〜365 行** |

**要点**: シード見積の上限 (400 行) より下振れ可能性あり。Mathlib `MeasurableEquiv.piFinsetUnion` の発見が大きく、Phase D 流儀の自前 `subsetSplitMEquiv` (50 行強) の写経が不要になった。Phase C の 3-piece reshape が最大の不確実性で、ここで詰まると 250 行+ に拡張される懸念。

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。
