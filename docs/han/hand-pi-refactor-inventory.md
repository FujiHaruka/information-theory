# HanD / Pi reshape refactor: Mathlib インベントリ (Phase 0)

> **Parent**: [`hand-pi-refactor-plan.md`](hand-pi-refactor-plan.md) §Phase 0
>
> **Status (2026-05-11)**: 起草。loogle (`.lake/build/loogle.index`) + Mathlib 直 grep で
> `MeasurableEquiv.piFinsetUnion` 周辺をホットスポット 4 軸で機械的に確認した結果を記録。
> CLAUDE.md「Subagent Inventory of Mathlib Lemmas」規約 (位置 / 完全シグネチャ /
> 引数 / 結論形 / 使い所) に従う。

## 結論サマリ

| 軸 | 結果 | 影響 |
|---|---|---|
| (1) `MeasurableEquiv.piFinsetUnion` の存在と verbatim 形 | **存在を確認** (`.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:612`)。ただし premise は `Disjoint s t`、conclusion は `↥(s ∪ t)` 形 (bespoke は `T₁ ⊆ T₂` 形 + `↥T₂` 形) | 直接 drop-in は **不可**。Pi.lean 内に薄いラッパー (subset-form helper か apply lemma) を 1 本追加する形になる |
| (2) `Equiv.piFinsetUnion` 系 apply lemma | `piFinsetUnion_left` / `piFinsetUnion_right` (`Mathlib/Data/Finset/Basic.lean:641-654`) が `Equiv` 版に存在。`MeasurableEquiv` 版用の `coe` lemma は **不在** | `MeasurableEquiv.piFinsetUnion_apply` 系の薄いラッパーを 1 本書く必要あり (`coe_piFinsetUnion` でも可) |
| (3) Subset-from-Disjoint の橋渡し | `Finset.disjoint_sdiff` / `Finset.union_sdiff_of_subset` で `T₁ ⊆ T₂` ↔ `(T₁, T₂ \ T₁, Disjoint, T₁ ∪ (T₂ \ T₁) = T₂)` の往復は 2 行で可 | `condEntropy_subset_anti` (HanD) の call site は subset-form ラッパー経由にすれば現状の API を維持できる |
| (4) 既存 call site の数と shape | 4 ヶ所 (HanD `condEntropy_subset_anti` ×1, Polymatroid `jointEntropySubset_mono` / `jointEntropySubset_disjoint_union` / `condEntropy_reshape_disjoint_union` ×3)。**全て同じ pattern** (`let e := subsetSplitMEquiv h; have hbridge := subsetSplitMEquiv_apply h ...`) | 4 ヶ所すべてが共通 helper 経由に refactor 可能 |

## Phase 詳細

### 軸 1: `MeasurableEquiv.piFinsetUnion` の存在確認

#### 結論 (1 行)

**存在する (`.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:612`) が、premise / conclusion の shape が bespoke `subsetSplitMEquiv` と異なるため drop-in 不可**。Pi.lean に shape 変換 (`↥(s ∪ t)` → `↥T₂` の cast) ラッパーを 1 本追加する必要がある。

#### 採用候補

##### `MeasurableEquiv.piFinsetUnion`
- **位置**: `.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:612`
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
- **引数**:
  - implicit `δ' : Type*`, `[DecidableEq δ']`
  - implicit `s t : Finset δ'`
  - implicit `π : δ' → Type*`, `[∀ a, MeasurableSpace (π a)]`
  - explicit `h : Disjoint s t`
- **結論形** (verbatim):
  ```
  ((∀ i : s, π i) × ∀ i : t, π i) ≃ᵐ ∀ i : (s ∪ t : Finset δ'), π i
  ```
- **使い所**: refactor の中核。`s = T₁`, `t = T₂ \ T₁` で `Finset.disjoint_sdiff` を使うか、
  Polymatroid 内 `disjoint_union` 系では `s, t, U` を直接指定。

#### Bespoke `subsetSplitMEquiv` との shape 差分

| 観点 | bespoke `subsetSplitMEquiv` (Pi.lean) | Mathlib `MeasurableEquiv.piFinsetUnion` |
|---|---|---|
| premise | `T₁ ⊆ T₂` | `Disjoint s t` |
| conclusion 型 | `((↥T₁ → α) × (↥(T₂ \ T₁) → α)) ≃ᵐ (↥T₂ → α)` | `((↥s → α) × (↥t → α)) ≃ᵐ (↥(s ∪ t) → α)` |
| index 同型の引数 | `subsetIdxEquiv h : (↥T₁ ⊕ ↥(T₂ \ T₁)) ≃ ↥T₂` | `Equiv.Finset.union s t h : (↥s ⊕ ↥t) ≃ ↥(s ∪ t)` |
| 直接の caller 数 | 4 (HanD ×1, Polymatroid ×3) | 0 (本 project 未使用) |

**翻訳**: `(T₁ ⊆ T₂)` ↔ `(s := T₁, t := T₂ \ T₁, h := Finset.disjoint_sdiff, hU := Finset.union_sdiff_of_subset h : T₁ ∪ (T₂ \ T₁) = T₂)`。`↥(s ∪ t) = ↥T₂` の cast は `subst hU` (Polymatroid `jointEntropySubset_disjoint_union` で実証済) または `Finset.union_sdiff_of_subset` を `▸` で適用。

---

### 軸 2: `Equiv.piFinsetUnion` 系 apply lemma

#### 結論 (1 行)

**`Equiv.piFinsetUnion_left` / `Equiv.piFinsetUnion_right` (`Mathlib/Data/Finset/Basic.lean:641-654`) が pointwise 値を計算するが、`MeasurableEquiv` 版用の `coe` lemma (`coe_piFinsetUnion`) は不在**。Pi.lean に薄いブリッジ (`MeasurableEquiv.piFinsetUnion_apply_left` 等) を 1 本書く必要がある (`Equiv` 版の coe が defeq に同じなので proof は 1〜2 行)。

#### 採用候補

##### `Equiv.piFinsetUnion`
- **位置**: `.lake/packages/mathlib/Mathlib/Data/Finset/Basic.lean:635`
- **シグネチャ** (verbatim):
  ```
  /-- The type of dependent functions on the disjoint union of finsets `s ∪ t` is equivalent to the
    type of pairs of functions on `s` and on `t`. This is similar to `Equiv.sumPiEquivProdPi`. -/
  def piFinsetUnion {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι} (h : Disjoint s t) :
      ((∀ i : s, α i) × ∀ i : t, α i) ≃ ∀ i : (s ∪ t : Finset ι), α i :=
    let e := Equiv.Finset.union s t h
    sumPiEquivProdPi (fun b ↦ α (e b)) |>.symm.trans (.piCongrLeft (fun i : ↥(s ∪ t) ↦ α i) e)
  ```
- **使い所**: `MeasurableEquiv.piFinsetUnion` の coe が defeq にこれと同じ。本 project 内で
  Pi.lean の bridge lemma の RHS に置く。

##### `Equiv.piFinsetUnion_left`
- **位置**: `.lake/packages/mathlib/Mathlib/Data/Finset/Basic.lean:641`
- **シグネチャ** (verbatim):
  ```
  set_option backward.isDefEq.respectTransparency false in
  lemma piFinsetUnion_left {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι}
      (h : Disjoint s t) {f g} {i : ι} (hi : i ∈ s) (hi' : i ∈ s ∪ t) :
      piFinsetUnion α h (f, g) ⟨i, hi'⟩ = f ⟨i, hi⟩ := by
    simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
    rw! [Finset.union_symm_left h hi hi']
    rfl
  ```
- **引数**: `α : ι → Type*` explicit, `s t` implicit, `h : Disjoint s t` explicit, `f g` implicit,
  `i : ι` implicit, `hi : i ∈ s` explicit, `hi' : i ∈ s ∪ t` explicit
- **結論形** (verbatim):
  ```
  piFinsetUnion α h (f, g) ⟨i, hi'⟩ = f ⟨i, hi⟩
  ```
- **使い所**: `MeasurableEquiv.piFinsetUnion_apply` の bridge proof で「inl branch」を畳む。

##### `Equiv.piFinsetUnion_right`
- **位置**: `.lake/packages/mathlib/Mathlib/Data/Finset/Basic.lean:649`
- **シグネチャ** (verbatim):
  ```
  set_option backward.isDefEq.respectTransparency false in
  lemma piFinsetUnion_right {ι} [DecidableEq ι] (α : ι → Type*) {s t : Finset ι}
      (h : Disjoint s t) {f g} {i : ι} (hi : i ∈ t) (hi' : i ∈ s ∪ t) :
      Equiv.piFinsetUnion α h (f, g) ⟨i, hi'⟩ = g ⟨i, hi⟩ := by
    simp_rw [piFinsetUnion, sumPiEquivProdPi, piCongrLeft, piCongrLeft', trans_apply, coe_fn_symm_mk]
    rw! [Finset.union_symm_right h hi hi']
    rfl
  ```
- **使い所**: 同上、「inr branch」用。

##### `MeasurableEquiv.coe_sumPiEquivProdPi_symm`
- **位置**: `.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:591`
- **シグネチャ** (verbatim):
  ```
  theorem coe_sumPiEquivProdPi_symm (α : δ ⊕ δ' → Type*) [∀ i, MeasurableSpace (α i)] :
      ⇑(MeasurableEquiv.sumPiEquivProdPi α).symm = (Equiv.sumPiEquivProdPi α).symm := by rfl
  ```
- **使い所**: `MeasurableEquiv.piFinsetUnion` の coe が `Equiv.piFinsetUnion` の coe に
  defeq に等しいことを示す proof で 1 行。

##### `MeasurableEquiv.coe_piCongrLeft` (要追加裏取り、推定存在)
- **位置**: `.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean` 周辺
  (`piCongrLeft` 定義と同所)
- **使い所**: 同上、`piCongrLeft` の coe が `Equiv.piCongrLeft` の coe に defeq な確認。
  `rfl` で済むはず (本 project 内 `entropy_measurableEquiv_comp` 等で既に間接利用)

---

### 軸 3: Subset-from-Disjoint 橋渡し

#### 結論 (1 行)

**`Finset.disjoint_sdiff` (`Mathlib/Data/Finset/Basic.lean:271`) + `Finset.union_sdiff_of_subset` (`Mathlib/Data/Finset/SDiff.lean:72`) で `T₁ ⊆ T₂` ↔ `(Disjoint T₁ (T₂ \ T₁), T₁ ∪ (T₂ \ T₁) = T₂)` の往復が 2 行で可**。bespoke API (`subsetSplitMEquiv` の `T₁ ⊆ T₂` premise 形) を Pi.lean 内 subset-form ラッパーで温存できる。

#### 採用候補

##### `Finset.disjoint_sdiff`
- **位置**: `.lake/packages/mathlib/Mathlib/Data/Finset/Basic.lean:271`
- **シグネチャ** (verbatim):
  ```
  theorem disjoint_sdiff : Disjoint s (t \ s) :=
    sdiff_disjoint.symm
  ```
- **引数**: `s t : Finset α` (semi-implicit、`variable` で導入されている)
- **結論形**: `Disjoint s (t \ s)`
- **使い所**: subset-form ラッパーの内部で `Disjoint T₁ (T₂ \ T₁)` を 1 行で取り出す。

##### `Finset.union_sdiff_of_subset`
- **位置**: `.lake/packages/mathlib/Mathlib/Data/Finset/SDiff.lean:72`
- **シグネチャ** (verbatim):
  ```
  theorem union_sdiff_of_subset (h : s ⊆ t) : s ∪ t \ s = t := by grind
  ```
- **引数**: `s t : Finset α` (implicit), `h : s ⊆ t` (explicit)
- **結論形**: `s ∪ t \ s = t`
- **使い所**: subset-form ラッパーで `↥(T₁ ∪ (T₂ \ T₁)) → α` を `↥T₂ → α` に cast。

#### Phase 影響

subset-form ラッパー `subsetSplitMEquiv (T₁ ⊆ T₂)` を Pi.lean 内に **薄い 5〜10 行の def** として
温存することで、HanD `condEntropy_subset_anti` の call site を **無変更** で済ます選択肢が開く。
内部実装は `MeasurableEquiv.piFinsetUnion (Finset.disjoint_sdiff)` + `Finset.union_sdiff_of_subset` の cast 1 段。

---

### 軸 4: 既存 call site の数と shape

#### 結論 (1 行)

**4 ヶ所 (HanD ×1, Polymatroid ×3) すべてが同一 pattern (3 行スニペット `let e := subsetSplitMEquiv h; have hbridge := subsetSplitMEquiv_apply h ...; rw [← hbridge]`)**。共通リファクタが効く。

#### 詳細

##### Site 1: `InformationTheory/Shannon/HanD.lean:278` (`condEntropy_subset_anti`)
- **コンテキスト**: subset 版 conditioning monotonicity (`T₁ ⊆ T₂ ⟹ H(X_i | X_{T₂}) ≤ H(X_i | X_{T₁})`)
- **使い方**:
  ```
  let e := subsetSplitMEquiv (α := α) (n := n) hT     -- hT : T₁ ⊆ T₂
  have hbridge : (fun ω => e (XT₁ ω, XR ω))
      = fun ω (j : ↥T₂) => Xs j.val ω := by
    funext ω
    exact subsetSplitMEquiv_apply hT (fun k => Xs k ω)
  ```
- **下流**: `condEntropy_measurableEquiv_comp μ (Xs i) (hXs i) (fun ω => (XT₁ ω, XR ω)) ... e`
  に与えて `condEntropy μ (Xs i) (fun ω j : T₂ => ...)` を `condEntropy μ (Xs i) (XT₁, XR)` に reshape。
- **API 入力 shape**: `T₁ ⊆ T₂` (subset form 必須)。`Disjoint T₁ T₂` ではない
- **refactor 戦略**: subset-form ラッパー (Pi.lean の `subsetSplitMEquiv` を温存) で **無変更**

##### Site 2: `InformationTheory/Shannon/Polymatroid.lean:84` (`jointEntropySubset_mono`)
- **コンテキスト**: monotonicity (`S ⊆ T ⟹ H(X_S) ≤ H(X_T)`)
- **使い方**: Site 1 と同 pattern、`hT := h : S ⊆ T`
- **下流**: `entropy_measurableEquiv_comp` で entropy reshape → pair chain rule → `condEntropy_nonneg`
- **API 入力 shape**: `S ⊆ T` (subset form)
- **refactor 戦略**: subset-form ラッパーで **無変更**、または Polymatroid 内で
  `jointEntropySubset_disjoint_union` ヘルパー (Site 3) を直接呼ぶ簡略化も可
  (`hd := Finset.disjoint_sdiff`, `hU := Finset.union_sdiff_of_subset h` を 2 行作って渡す)

##### Site 3: `InformationTheory/Shannon/Polymatroid.lean:142` (`jointEntropySubset_disjoint_union`)
- **コンテキスト**: helper、premise が `Disjoint s t` + `s ∪ t = U`
- **使い方**: `hsU : s ⊆ U` を `hU ▸ Finset.subset_union_left` で derive、`htU : U \ s = t` を
  `hU` + disjoint で derive、subsetSplitMEquiv (subset form) を呼ぶ
- **下流**: 同 pattern (entropy reshape → pair chain rule)
- **API 入力 shape**: `Disjoint s t` + `s ∪ t = U` (Mathlib `piFinsetUnion` の native form)
- **refactor 戦略**: **Mathlib `MeasurableEquiv.piFinsetUnion` 直接利用へ書き換え** が最も clean。
  `subst hU` 一発で `↥(s ∪ t) → α` ↔ `↥U → α` の cast を消せる
  (現状 `subst htU` で逆方向 cast を消しているのと対称)

##### Site 4: `InformationTheory/Shannon/Polymatroid.lean:186` (`condEntropy_reshape_disjoint_union`)
- **コンテキスト**: helper、conditioner 側 reshape
- **使い方**: Site 3 と同じ derive
- **下流**: `condEntropy_measurableEquiv_comp` で conditioner reshape
- **API 入力 shape**: Site 3 と同
- **refactor 戦略**: Site 3 と同、Mathlib 直接利用に書き換え

#### Refactor の射程まとめ

| Site | 入力 shape | refactor 後の戦略 | 行数変化 |
|---|---|---|---|
| 1 (HanD `condEntropy_subset_anti`) | `T₁ ⊆ T₂` | 無変更 (subset-form ラッパー温存) | 0 |
| 2 (Polymatroid `jointEntropySubset_mono`) | `S ⊆ T` | 無変更 or `disjoint_union` ヘルパー直接呼び出しに簡略化 | 0 〜 -10 |
| 3 (Polymatroid `jointEntropySubset_disjoint_union`) | `Disjoint s t` + `s ∪ t = U` | Mathlib 直接 + `subst hU` | -5 〜 -10 |
| 4 (Polymatroid `condEntropy_reshape_disjoint_union`) | `Disjoint s t` + `s ∪ t = U` | 同上 | -5 〜 -10 |
| **Pi.lean 内** (`subsetIdxEquiv` 削除 + `subsetSplitMEquiv` を Mathlib ベースに薄く書き直し + `_apply_left/right` ブリッジ追加) | — | **-50 行 程度の純減** (50+ 行の自前 plumbing → 5〜15 行のラッパー) | **-30 〜 -45** (合計) |

---

## Phase 0 着手判定

**結論**: refactor は実装可能、ただし「drop-in」ではなく「**薄いラッパー (Pi.lean 内に 1〜2 本) を経由した置換**」となる。`MeasurableEquiv.piFinsetUnion` は subset 形ではなく disjoint union 形なので、subset-form 互換 API を Pi.lean に温存することで HanD の call site を無変更に保てる。

**主要不確実性ランク**:

| 項目 | 不確実性 | 対処 |
|---|---|---|
| `MeasurableEquiv.piFinsetUnion` の coe lemma 不在 | **低** | Pi.lean に `coe_piFinsetUnion` (`rfl` 1 行) または `_apply_left/right` (2〜4 行ずつ) を書く |
| `Equiv.piFinsetUnion_left/right` を `MeasurableEquiv` 版に持ち上げる際の defeq 周り | **中** | `MeasurableEquiv` の `coe_*` lemma が `rfl` で潰れるかを smoke test (Phase 1 着手最初の 30 分で確認) |
| Polymatroid `disjoint_union` ヘルパーの再設計で他の Phase C の依存が壊れないか | **中** | 既存テスト (現 `Polymatroid.lean` の `submodular` 本体) を `lake env lean` で再検証、call site の API は変えずに内部実装だけ swap |
| `subsetIdxEquiv` の独立利用箇所 | **低** | grep で 0 件確認済 (`subsetSplitMEquiv` の内部からのみ。削除して問題なし) |

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。
