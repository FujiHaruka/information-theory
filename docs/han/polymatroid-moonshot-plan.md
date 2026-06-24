# Polymatroid Axioms (Submodularity of Entropy) ムーンショット計画 🌙

**Status**: CLOSED ✅ — done (Ch.17 Polymatroid; Phase A–C 3 axioms proof done, 0 sorry; Phase D structure-ification split off to `polymatroid-structure-plan.md`).

> 実態整合 (2026-05-20): DONE-UNCOND — `jointEntropySubset_submodular` (`InformationTheory/Shannon/Polymatroid.lean:192`、3-piece disjoint 分解 + `condEntropy_le_condEntropy_of_pair` で実証、標準 binder のみ) + `jointEntropySubset_empty` / `jointEntropySubset_mono`。`lake env lean InformationTheory/Shannon/Polymatroid.lean` silent、0 sorry。Phase D は (D-b) で別 plan ([polymatroid-structure-plan.md](polymatroid-structure-plan.md)) 化済で実態一致。
> **Status (2026-05-11): Phase A〜C 完了 ✅ (288 行 / 0 sorry)。** Phase D は
> 計画通り (D-b) **別 plan に切り出し** (本 plan は 3 性質単発 theorem で close)。
> Han Phase D 完了 (`InformationTheory/Shannon/HanD*.lean` の 8 主定理が 0 sorry) と
> `InformationTheory/Shannon/Pi.lean` 切り出し直後、Loomis–Whitney
> ([`docs/shannon/loomis-whitney-moonshot-plan.md`](../shannon/loomis-whitney-moonshot-plan.md))
> 完了に続く 2 本目のムーンショット。
> Seed カード ([`docs/moonshot-seeds.md` Seed 2](../moonshot-seeds.md)) を母体に Phase 分解した。
>
> ゴールは entropy が **polymatroid rank function の 3 性質**
> (i) `H(X_∅) = 0`、(ii) monotonicity (`S ⊆ T ⇒ H(X_S) ≤ H(X_T)`)、(iii) submodularity
> (`H(X_{S∪T}) + H(X_{S∩T}) ≤ H(X_S) + H(X_T)`) を満たすことを Lean で証明し、
> Han Phase D の `jointEntropySubset` を polymatroid として位置付けることである。

## 進捗

- [x] Phase 0 — Mathlib + 既存 InformationTheory API インベントリ ✅ → [`polymatroid-mathlib-inventory.md`](polymatroid-mathlib-inventory.md)
- [x] Phase A — `jointEntropySubset_empty = 0` (空集合からの entropy) ✅
- [x] Phase B — monotonicity (`S ⊆ T ⇒ H(X_S) ≤ H(X_T)`) ✅
- [x] Phase C — submodularity (`H(X_{S∪T}) + H(X_{S∩T}) ≤ H(X_S) + H(X_T)`) ✅
- [x] Phase D (オプション) — **(D-b) 採用**: 独立 plan に切り出し、本 plan は 3 性質単発で close ✅

## ゴール / Approach

**ゴール**: 任意 `n : ℕ`, 有限 `α` 値 RV 族 `Xs : Fin n → Ω → α` に対し、`jointEntropySubset μ Xs : Finset (Fin n) → ℝ` が以下の 3 性質を満たすことを示す:

```
(i)   jointEntropySubset μ Xs ∅ = 0
(ii)  S ⊆ T → jointEntropySubset μ Xs S ≤ jointEntropySubset μ Xs T
(iii) jointEntropySubset μ Xs (S ∪ T) + jointEntropySubset μ Xs (S ∩ T)
       ≤ jointEntropySubset μ Xs S + jointEntropySubset μ Xs T
```

`InformationTheory/Shannon/Polymatroid.lean` (新規) で着地。`Polymatroid` structure 導入は Phase D で改めて判断する。

**Approach (戦略の shape)**:

1. **Phase A は trivial**: `S = ∅` のとき `(↥(∅ : Finset (Fin n)) → α)` は `IsEmpty` 上の Pi 値で `Unique`、`MeasurableEquiv.ofUniqueOfUnique` 経由で `entropy μ Xs = 0` (HanD chain rule の base case `n = 0` と同じパターン、写経で 15〜25 行)。
2. **Phase B は chain rule + monotonicity の合成**: `S ⊆ T` のとき `T \ S` の各要素を 1 個ずつ追加する induction、または直接 `T = S ⊔ (T \ S)` の disjoint 分解 + `MeasurableEquiv.piFinsetUnion` で `H(X_T) = H(X_S, X_{T\S}) ≥ H(X_S)` (= 「joint entropy は marginal entropy 以上」、Phase A `entropy_pair_eq_entropy_add_condEntropy` と `condEntropy_nonneg` で)。後者の方が短い。
3. **Phase C は 3 ピース disjoint 分解**: `S ∪ T = (S ∩ T) ⊔ (S \ T) ⊔ (T \ S)` の 3-disjoint 分解を 2 段の `MeasurableEquiv.piFinsetUnion` で構成。各 entropy を以下に変形:

   ```
   H(X_{S∪T}) = H(X_{S∩T}, X_{S\T}, X_{T\S})           -- 3-piece reshape
              = H(X_{S∩T}) + H(X_{S\T} | X_{S∩T})
                + H(X_{T\S} | X_{S∩T}, X_{S\T})        -- chain rule (3 段)
   H(X_S) = H(X_{S∩T}) + H(X_{S\T} | X_{S∩T})           -- S = (S∩T) ⊔ (S\T)
   H(X_T) = H(X_{S∩T}) + H(X_{T\S} | X_{S∩T})           -- T = (S∩T) ⊔ (T\S)
   H(X_{S∩T}) = H(X_{S∩T})                              -- 自明
   ```

   submodularity の差分:

   ```
   (H(X_S) + H(X_T)) - (H(X_{S∪T}) + H(X_{S∩T}))
     = H(X_{T\S} | X_{S∩T}) - H(X_{T\S} | X_{S∩T}, X_{S\T})
     ≥ 0   -- conditioning monotonicity (`condEntropy_le_condEntropy_of_pair`)
   ```

   **plumbing は Phase D の `subsetSplitMEquiv` 流儀をそのまま流用** (`HanD.lean:69-73` の `subsetSplitMEquiv` を `S ∩ T ↪ S` / `S ∩ T ↪ S ∪ T` / `S ⊔ (T \ S) = S ∪ T` の 3 通りで適用)。新規 `MeasurableEquiv` 構成は不要、Mathlib `MeasurableEquiv.piFinsetUnion` が直接効く。

4. **Phase D は判断保留**: Mathlib に `Polymatroid` structure / `Submodular` (集合関数) structure はいずれも不在 (Phase 0 で確認、軸 1)。Matroid rank の文脈で `Matroid.eRk_inter_add_eRk_union_le` のような submodularity 補題のみ存在。本 plan の core delivery は 3 性質単発 theorem で十分なので、structure 化は `Polymatroid` を新規導入する独立 plan として切り出すか、本 plan 内で軽量 `def` に留めるか Phase D 着手時に判断。

ファイル構成 (Phase C 終了時):

```
InformationTheory/Shannon/
  HanD.lean           ← 既存 (jointEntropySubset, subset chain rule, condEntropy_subset_anti)
  Pi.lean             ← 既存 (entropy/condEntropy MeasurableEquiv 不変性)
  Polymatroid.lean    ← 新規: jointEntropySubset_empty,
                        jointEntropySubset_mono,
                        jointEntropySubset_submodular
                        (+ Phase D で structure 化なら Polymatroid def + instance)
```

`InformationTheory.lean` (library root) に `import InformationTheory.Shannon.Polymatroid` を追記。

## Phase 0 — Mathlib + 既存 InformationTheory API インベントリ 📋

サブ計画: [`polymatroid-mathlib-inventory.md`](polymatroid-mathlib-inventory.md)

調査軸 (loogle / rg、negative も記録):

- [ ] **軸 1: `Polymatroid` / `Submodular` (集合関数版) structure** — Mathlib に集合関数 polymatroid / submodular structure が既存しているか。あれば本 plan で entropy をそのインスタンスとして登録する選択肢が開く
- [ ] **軸 2: `Fin 0 → α ≃ Unit` 系** (空集合からの Pi 値): `MeasurableEquiv.ofUniqueOfUnique`, `MeasurableEquiv.piUnique`, `Pi.uniqueOfIsEmpty`。Phase A の trivialization に使う
- [ ] **軸 3: 集合論的 reshape** (Pi 値同値): `S ∪ T = S ⊔ (T \ S)` 等を `((↥S → α) × (↥(T \ S) → α)) ≃ᵐ (↥(S ∪ T) → α)` に持ち上げる `MeasurableEquiv`。`MeasurableEquiv.piFinsetUnion`, `Equiv.Finset.union`, `Finset.disjoint_sdiff` 系
- [ ] **軸 4: `jointEntropySubset_chain_rule` 流用形** (本 project): submodularity 証明での `H(X_{S∪T}) - H(X_S)` 形変形に必要な chain rule 既存形の確認。Phase A `entropy_pair_eq_entropy_add_condEntropy` の subset 版 / pair 版での具体 invoke 形
- [ ] **軸 5: `condEntropy` non-increasing in conditioner** (本 project / Mathlib): 既存 `condEntropy_subset_anti` (HanD.lean) で submodularity に十分か、または `condEntropy_le_condEntropy_of_pair` (Entropy.lean) の別形が必要か。Phase C の核
- [ ] **軸 6: monotonicity の既存補題** (本 project): `jointEntropySubset_mono` のような `S ⊆ T` 形が既存していないか確認 (Han Phase D / Loomis–Whitney 内で部分実装されているかも)

各軸で「Mathlib にあるか / ないか / 既存補題で代用可」+ 採用シグネチャ verbatim を記録。`Done` 条件は **「Phase A skeleton (`InformationTheory/Shannon/Polymatroid.lean` の sorry-driven 出だし) が書ける状態」**。

## Phase A — `jointEntropySubset_empty = 0` 📋

ターゲット: `S = ∅` のとき entropy が 0。

### スコープ (skeleton)

```lean
namespace InformationTheory.Shannon

/-- Polymatroid axiom (i): empty subset entropy. -/
theorem jointEntropySubset_empty
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) :
    jointEntropySubset μ Xs ∅ = 0
```

### 鍵となる作業

- [ ] `(↥(∅ : Finset (Fin n)) → α)` が `Unique` (= `IsEmpty (↥∅)` から `Pi.uniqueOfIsEmpty`) を確認
- [ ] `entropy μ X = 0` for `X : Ω → β` with `[Unique β]` の補題を写経:
  - `HanD.lean` の chain rule base case (`n = 0` 分岐) で同じ流儀。`Fintype.sum_unique` + `μ {default} = 1` (probability measure 経由) + `Real.negMulLog_one = 0`
  - 既に Han.lean 内で使った 5〜10 行パターン
- [ ] `InformationTheory.lean` に `import InformationTheory.Shannon.Polymatroid` を追記
- [ ] `lake env lean InformationTheory/Shannon/Polymatroid.lean` で silent 化

### Done 条件

- `jointEntropySubset_empty` が 0 sorry
- Phase B 着手判定 (chain rule 流用形が Phase 0 軸 4 で確定済み)

### 工数感

1〜2 日 (15〜25 行)。HanD chain rule の base case 写経で済む。山場ナシ。

## Phase B — monotonicity 📋

ターゲット: `S ⊆ T → jointEntropySubset μ Xs S ≤ jointEntropySubset μ Xs T`。

### スコープ

```lean
/-- Polymatroid axiom (ii): monotonicity. -/
theorem jointEntropySubset_mono
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {S T : Finset (Fin n)} (h : S ⊆ T) :
    jointEntropySubset μ Xs S ≤ jointEntropySubset μ Xs T
```

### 証明骨格 (2 ルート、Phase 0 結果を見て選ぶ)

**ルート α (推奨、短い)**: `T = S ⊔ (T \ S)` の disjoint 分解を `MeasurableEquiv.piFinsetUnion` (Mathlib) で押し上げ、Phase A `entropy_pair_eq_entropy_add_condEntropy` を 1 段適用、`condEntropy ≥ 0` で結ぶ。

```
H(X_T) = H((X_S, X_{T\S}))                            -- piFinsetUnion reshape
       = H(X_S) + H(X_{T\S} | X_S)                    -- pair chain rule
       ≥ H(X_S)                                        -- condEntropy ≥ 0
```

`MeasurableEquiv.piFinsetUnion` (`.lake/packages/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Embedding.lean:612`) が **そのまま** `Disjoint S (T \ S)` (`Finset.disjoint_sdiff`) で発火するので、reshape は `entropy_measurableEquiv_comp` (Pi.lean) で 1 段、合計 30〜50 行見積。

**ルート β (代替)**: `Finset.induction_on` で `T \ S` の要素を 1 個ずつ追加する induction。各段で「1 元追加で entropy が増えない」を `condEntropy_le_condEntropy_of_pair` で示す。`HanD.lean` の `condEntropy_subset_anti` は **conditioner 側**の monotonicity だが、Phase B で必要なのは **target 側**の monotonicity (`H(X_S) ≤ H(X_S, X_x)`)。これは `condEntropy_le_condEntropy_of_pair` の dual で、`H(X_S, X_x) = H(X_S) + H(X_x | X_S) ≥ H(X_S)` から直接。ルート α より素直で plumbing 軽い。

→ **ルート α が短いと判断**。Phase 0 軸 3 で `MeasurableEquiv.piFinsetUnion` の取り回しを確認した上でルート α を採用、ハマったら β に切り替え。

### 鍵となる作業

- [ ] `Disjoint S (T \ S)` (Mathlib `Finset.disjoint_sdiff`) を確認
- [ ] `MeasurableEquiv.piFinsetUnion (fun _ => α) (Finset.disjoint_sdiff)` で `((↥S → α) × (↥(T \ S) → α)) ≃ᵐ (↥(S ∪ (T \ S)) → α)` を構成
- [ ] `S ∪ (T \ S) = T` (Mathlib `Finset.union_sdiff_of_subset h`) で cast。`(↥(S ∪ (T \ S)) → α) = (↥T → α)` の defeq か `MeasurableEquiv.cast` 1 段
- [ ] reshape 後の `(fun ω => (X_S ω, X_{T\S} ω))` を Phase A `entropy_pair_eq_entropy_add_condEntropy` に乗せる
- [ ] `condEntropy_nonneg`: `H(X_{T\S} | X_S) ≥ 0`。HanDShearer.lean が `unfold + integral_nonneg + Real.negMulLog_nonneg` で書いた pattern を再利用 (Phase 0 軸 5 で再利用可否確認、必要なら別 lemma に切り出し)
- [ ] linarith で結ぶ

### Done 条件

- `jointEntropySubset_mono` が 0 sorry
- ルート α / β 採否を判断ログに記録

### 工数感

2〜3 日 (30〜50 行 if ルート α、60〜80 行 if ルート β)。`piFinsetUnion` の cast / defeq 周りで詰まる可能性が中位リスク。

## Phase C — submodularity 📋

ターゲット: `H(X_{S∪T}) + H(X_{S∩T}) ≤ H(X_S) + H(X_T)`。Phase D の山場。

### スコープ

```lean
/-- Polymatroid axiom (iii): submodularity. -/
theorem jointEntropySubset_submodular
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S T : Finset (Fin n)) :
    jointEntropySubset μ Xs (S ∪ T) + jointEntropySubset μ Xs (S ∩ T)
      ≤ jointEntropySubset μ Xs S + jointEntropySubset μ Xs T
```

### 証明骨格

3 ピース disjoint 分解 `S ∪ T = (S ∩ T) ⊔ (S \ T) ⊔ (T \ S)` を経由する。Phase D `subsetSplitMEquiv` (`HanD.lean:69`) と同じ流儀。

```
記号: I := S ∩ T, A := S \ T, B := T \ S。
事実: S = I ⊔ A, T = I ⊔ B, S ∪ T = I ⊔ A ⊔ B (3-disjoint)。

各 entropy を chain rule で展開:
  H(X_S)    = H(X_I) + H(X_A | X_I)                           ─── (P1)
  H(X_T)    = H(X_I) + H(X_B | X_I)                           ─── (P2)
  H(X_{S∪T}) = H(X_I) + H(X_A | X_I) + H(X_B | X_I, X_A)      ─── (P3)
  H(X_{S∩T}) = H(X_I)                                          ─── (P4)

差を取る:
  (H(X_S) + H(X_T)) - (H(X_{S∪T}) + H(X_{S∩T}))
    = H(X_B | X_I) - H(X_B | X_I, X_A)
    ≥ 0     ─── conditioning monotonicity
```

### 鍵となる作業

- [ ] **3-disjoint 分解の Pi 値 `MeasurableEquiv` 構成** —
      `MeasurableEquiv.piFinsetUnion (fun _ => α) (Finset.disjoint_sdiff_inter S T)` で
      `((↥(S \ T) → α) × (↥(S ∩ T) → α)) ≃ᵐ (↥((S \ T) ∪ (S ∩ T)) → α)` を作る形を 2 段組む。
      または **Phase D の `subsetSplitMEquiv` を 2 回反復**して 3 ピース化:
      まず `S = (S ∩ T) ⊔ (S \ T)` で `S → ((S ∩ T) → α) × ((S \ T) → α)`、
      次に `S ∪ T = S ⊔ (T \ S)` で `(S ∪ T) → ((S → α) × ((T \ S) → α))`、
      最終的に `(S ∪ T) → ((S ∩ T) → α) × ((S \ T) → α) × ((T \ S) → α)` の 3 ピース等価。
      **新規 MeasurableEquiv は不要、Mathlib `piFinsetUnion` + Pi.lean `entropy_measurableEquiv_comp` で済む見込み**
- [ ] **各 entropy を chain rule で展開** —
      `H(X_S)`, `H(X_T)`, `H(X_{S∪T})` の 3 つを Phase A `entropy_pair_eq_entropy_add_condEntropy` で展開。`H(X_{S∪T})` は pair 形を 2 回入れ子にして 3 段 chain にする (= `H(I,A,B) = H(I) + H(A|I) + H(B|I,A)`)
- [ ] **conditioning monotonicity を 1 回適用** —
      `H(X_B | X_I, X_A) ≤ H(X_B | X_I)`。Phase A `condEntropy_le_condEntropy_of_pair` をそのまま (X = X_B, Y = X_I, Z = X_A の形)
- [ ] **代数で結ぶ** — 4 等式を立て、linarith 1 発で submodularity に着地
- [ ] `Disjoint (S ∩ T) (S \ T)` (`Finset.disjoint_sdiff_inter`) と `(S ∩ T) ∪ (S \ T) = S` (Mathlib `Finset.inter_union_sdiff` 系、要 Phase 0 確認) の 2 補題を確保

### Done 条件

- `jointEntropySubset_submodular` が `lake env lean InformationTheory/Shannon/Polymatroid.lean` で silent
- Phase A / B が活性化 (chain rule + reshape を本 Phase で fully exercise)
- Pi reshape が Phase D `subsetSplitMEquiv` 流儀の 2 段適用で済むか / 新規補助補題が必要か、判断ログに記録

### 工数感

5〜7 日 (150〜250 行)。Phase D `subsetSplitMEquiv` (50 行) 写経 + 3 ピース化 1 段増え + chain rule 3 段展開 + linarith。**最大リスクは 3-disjoint Pi reshape の`MeasurableEquiv` cast まわり** (`Disjoint`, `union` の associativity が effortlessly 通るか)。詰まったら Phase D 流儀の `subsetIdxEquiv` を 3-piece 版に手書き拡張 (40〜60 行追加)。

## Phase D (オプション) — `Polymatroid` structure 化判断 📋

### 着手判断のフロー

1. **Phase 0 軸 1 結果を確認**: Mathlib に `Polymatroid` / `Submodular` が
   - **既存している** → 本 plan の 3 性質をそのインスタンスとして登録する独立 PR 候補。Phase D 内で完結
   - **不在** → 本 plan で `Polymatroid` def を新規導入するかどうかは独立判断
2. **不在のときの選択肢**:
   - (D-a) 軽量 `def Polymatroid` (構造体: `rank : Finset ι → ℝ` + 3 公理 prop) を `InformationTheory/Shannon/Polymatroid.lean` 末尾に追加。`jointEntropySubset` を `Polymatroid` インスタンスとして登録する `noncomputable instance` を組む
   - (D-b) `Polymatroid` 自体を独立 plan に切り出し (Mathlib upstream PR 候補)、本 plan は 3 性質単発 theorem で close
3. **デフォルト**: (D-b)。本 plan の core delivery は 3 性質単発で十分、structure 化は副産物として Phase D 着手時に再評価。

### スコープ (D-a 採用時のみ)

```lean
/-- A polymatroid is a finite set together with a real-valued rank function
satisfying the three polymatroid axioms. -/
structure Polymatroid (ι : Type*) [DecidableEq ι] [Fintype ι] where
  rank : Finset ι → ℝ
  rank_empty : rank ∅ = 0
  rank_mono : ∀ {S T}, S ⊆ T → rank S ≤ rank T
  rank_submodular : ∀ S T, rank (S ∪ T) + rank (S ∩ T) ≤ rank S + rank T

/-- Entropy as a polymatroid rank function. -/
noncomputable def entropyPolymatroid
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    Polymatroid (Fin n) where
  rank S := jointEntropySubset μ Xs S
  rank_empty := jointEntropySubset_empty μ Xs
  rank_mono := jointEntropySubset_mono μ Xs hXs
  rank_submodular := jointEntropySubset_submodular μ Xs hXs
```

### Done 条件 (D-a 採用時)

- `Polymatroid` structure + `entropyPolymatroid` def が silent
- 不採用なら判断ログに「(D-b) で close」と記録

### 工数感

D-a なら 1 日 (20〜40 行、structure + instance のみ)。D-b なら 0 日 (判断ログ + close)。

## 失敗判定 / 撤退ライン

- **Phase 0 で Mathlib に `Polymatroid` 既存 / 集合関数 submodularity が generic に立っている** → 計画破棄、proof-log だけ取って Seed 3 (Slepian–Wolf) に乗り換え
- **Phase A の `(↥(∅ : Finset _) → α)` instance / Unique handling で詰まる** → `Fin 0 → α` の HanD chain rule base case を直接コピペで済ます (subset 一般版を諦め `S = (∅ : Finset (Fin n))` 専用補題にする)
- **Phase B の `MeasurableEquiv.piFinsetUnion` cast まわりで 3 日以上溶ける** → ルート β (induction on `T \ S`) に切り替え。HanD `condEntropy_subset_anti` 流の 1 元拡張 induction で 60〜80 行
- **Phase C の 3-disjoint Pi reshape で詰まる** → 2 ルート切り替え:
  - (i) Phase D `subsetSplitMEquiv` を 3-piece 版 (`subsetSplit3MEquiv`) に手書き拡張 (40〜60 行)
  - (ii) submodularity を「`H(X_{S∪T}) ≤ H(X_S) + H(X_T) - H(X_{S∩T})`」を avoid して、`I(X_S; X_T) = H(X_S) + H(X_T) - H(X_{S∪T})` (mutualInfo) 経由で書き直す。MutualInfo.lean の既存 plumbing を擦って `condMutualInfo` の chain rule で `I(X_{S\T}; X_{T\S} | X_{S∩T}) ≥ 0` から submodularity を出す代替経路。**ただし MutualInfo の subset 版が既存していないので 200+ 行になる懸念、撤退ラインとしてのみ**
- **Phase D で structure 化が予想外に重い** → (D-b) で close、proof-log で「Polymatroid structure 化は別 plan で」と記録

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

### 2026-05-11 Phase A〜C 完了, Phase D は (D-b) 採用

- **着地**: `InformationTheory/Shannon/Polymatroid.lean` 288 行 / 0 sorry / 0 warning。
  `lake build` 緑通過。インベントリ再見積 195〜365 行の範囲内。
- **Phase A**: HanD chain rule base case (`Han.lean:64-85`) の写経で `IsEmpty` 経由 →
  `Pi.uniqueOfIsEmpty` → `Real.negMulLog_one`。15 行で着地。リスクなし。
- **Phase B**: 計画ルート α (`piFinsetUnion` 経由) を採るつもりだったが、HanD.lean
  の `subsetSplitMEquiv` (T₁ ⊆ T₂ で同型を構成) が **本質的に同等** で plumbing が
  軽いと判断、`private` を外して再利用に切り替え。具体的には `subsetSplitMEquiv` /
  `subsetSplitMEquiv_apply` / `subsetIdxEquiv` の 3 つを公開化。Phase B 本体は 30 行。
- **Phase C** (山場): 計画通り 3 ピース disjoint 分解だが、計画懸念 1 (3-piece Pi
  reshape の cast まわり) を **「`s ∪ t = U` を引数で受ける `disjoint_union` 形 helper」**
  で吸収する戦略に変更。具体的には:
  - `jointEntropySubset_disjoint_union` (helper, ~30 行): `Disjoint s t` + `s ∪ t = U` →
    `H(X_U) = H(X_s) + H(X_t | X_s)`。`subst htU` 一発で `↥(U \ s) = ↥t` の cast を
    吸収できるのが鍵 (htU は `U \ s = t` 形で `t` を `U \ s` で置換可能)。
  - `condEntropy_reshape_disjoint_union` (helper, ~25 行): conditioner 側 reshape も同流儀。
  - submodular 本体 (~50 行): 上 2 helper を 3 回 + 1 回呼び、`condEntropy_le_condEntropy_of_pair`
    1 発 + `linarith` で着地。3-piece の associativity をひと括りで済む。
- **Phase D 判断**: Mathlib に `Polymatroid` 不在 (inventory 軸 1)、本 plan の core
  delivery (3 性質単発 theorem) で publish 価値あり、structure 化で得られる再利用先
  (Seed 4 / Seed 5) は本 plan のスコープ外。よって (D-b) 「別 plan に切り出し」を
  採用、本 plan はここで close。
- **観察**: 計画懸念 1 は `subst htU` 一発で消えた。`subsetSplitMEquiv` の `T₁ ⊆ T₂`
  形と `MeasurableEquiv.piFinsetUnion` の `Disjoint s t` 形は機能的に同値だが、
  proof の plumbing 上は **disjoint + union equality 両方を引数で受ける形** が
  一番扱いやすい (Finset 等式 cast を `subst` で消せるので)。今後 Pi 値 reshape
  系の helper を増やすときの設計指針になる。
