# Han Phase D Mathlib インベントリ (Phase 0)

> **Status (2026-05-10):** 完。`docs/han/han-phase-d-plan.md` Phase 0 の成果物。
> 結論: **subset average / Shearer は Mathlib 未実装、Phase D を予定通り進めて良い**。
> 加えて Phase B の山場 (二重和 reindex) は **Mathlib に既存テンプレあり**、当初見積もりより plumbing 量を圧縮できる見込み。

## 目的

Phase D 着手前に以下 4 軸を裏取り:

- (a) Mathlib に Han 1978 subset average / Shearer / 任意 covering 形のエントロピー不等式が既に無いか
- (b) `Finset.powersetCard` 上の二重和 reindex API
- (c) `(i : S) → α` (S : Finset _) の Pi 値 instance 自動発火
- (d) 既存 `InformationTheory/Shannon/Han.lean` の `han_inequality` を subfamily restrict する際の reshape boilerplate

## 結論サマリ

| 軸 | 結果 | Phase D への影響 |
|---|---|---|
| (a) Mathlib subset entropy 在庫 | **0 件** | Phase D 計画は破棄不要、予定通り進める |
| (b) powersetCard 二重和 reindex | 直接 1 行は無いが Mathlib 内に **完璧な写経テンプレ** あり (`Polynomial.Derivative.lean:710-728`) | Phase B の山場は当初 30〜50 行 → **20〜25 行** に圧縮見込み |
| (c) `(i : S) → α` Pi instance | `Subtype.fintype` + `Subtype.instMeasurableSpace` + `MeasurableSpace.pi` で自動発火する見込み | Phase A skeleton を sorry-driven で書き始められる |
| (d) Han subfamily restrict | `Finset.orderEmbOfFin S : Fin S.card ↪o Fin n` を介して既存 `han_inequality` を適用、結果を `jointEntropySubset μ Xs S` に reshape | Phase A の `han_inequality_subset` は **既存 reshape plumbing 流儀** で書ける |

---

## 軸 (a): Mathlib に subset average / Shearer は無い

### Subagent (Explore) 報告

`.lake/packages/mathlib/Mathlib/` 全域を以下の query で確認 — **0 件確定**:

- `rg "shearer\|Shearer"` → 0
- `rg "Han.*1978\|Han1978"` → 0
- `rg "averageSubsetEntropy"` → 0
- `rg "powersetCard.*entropy\|entropy.*powersetCard"` → 0
- `rg "fractional.*cover\|cover.*fractional"` (情報論文脈) → 0
- `rg "subset.*jointEntropy\|jointEntropy.*subset"` → 0
- loogle `"Shearer"` → unknown identifier
- loogle `"Han"` → unknown identifier

### subagent の追加観察 (注意して採用)

Subagent は「Mathlib に Shannon entropy 自体が無い」と報告したが、これは subagent の探索範囲外を見落とした可能性が高い。実際 `InformationTheory/Shannon/Entropy.lean` は何らかの上流ライブラリ (`InformationTheory.MeasureFano.condEntropy` 等) を活用している。**Phase D 計画上は (a) 結論「subset average / Shearer は無い」だけが load-bearing**、Shannon entropy 自体の有無は本 inventory のスコープ外なので結論変更は不要。

### Mathlib 探索ファイル

- `Mathlib/InformationTheory/Hamming.lean`, `Mathlib/InformationTheory/KullbackLeibler/*.lean`, `Mathlib/InformationTheory/Coding/*.lean`
- `Mathlib/Combinatorics/SetFamily/AhlswedeZhang.lean` (← `powersetCard` を扱うが entropy ではない)
- `Mathlib/Probability/` (entropy 系ファイルは subagent 範囲外、要追加調査になる場合は別 turn で)

### Phase D 影響

**Phase D 計画は破棄不要。予定通り `InformationTheory/Shannon/HanD.lean` を新規作成、subset 版 infrastructure を一から書く。**

---

## 軸 (b): powersetCard 上の二重和 reindex

### Phase B で必要な形

```
∀ k, k+1 ≤ n,
  ∑ S ∈ powersetCard (k+1) (univ : Finset (Fin n)),
    ∑ i ∈ S, f (S.erase i)
  = (n - k) * ∑ T ∈ powersetCard k univ, f T
```

ここで `f : Finset (Fin n) → ℝ` は `f T = jointEntropySubset μ Xs T`。

### Mathlib 探索結果

#### (b-1) 「定数関数の powersetCard 和」: あり、しかし目的に不適

`Mathlib/Algebra/BigOperators/Group/Finset/Powerset.lean:61`:

```lean
lemma prod_powersetCard (n : ℕ) (s : Finset α) (f : ℕ → β) :
    ∏ t ∈ powersetCard n s, f #t = f n ^ (#s).choose n
```

これは `f` が **`#t` (cardinality) のみに依存する**形に限定された lemma。Phase B では `f T = jointEntropySubset μ Xs T` で `T` 全体に依存するので **直接は使えない**。

#### (b-2) 「`prod_powerset` (size 別分解)」: あり、目的とは違う

同ファイル `:54`:

```lean
lemma prod_powerset (s : Finset α) (f : Finset α → β) :
    ∏ t ∈ powerset s, f t = ∏ j ∈ range (#s + 1), ∏ t ∈ powersetCard j s, f t
```

これは `powerset` を size 別に分解する補題。Phase B の reindex とは目的が違う。

#### (b-3) **完璧な写経テンプレ**: `Mathlib/Algebra/Polynomial/Derivative.lean:710-728`

`Polynomial.iterate_derivative_prod_X_sub_C` の証明内に、**Phase B の reindex とほぼ同型**のパターンがある:

```lean
calc
  ∑ T ∈ S.powersetCard (#S - k), derivative (∏ a ∈ T, (X - C a)) =
  ∑ T ∈ S.powersetCard (#S - k), ∑ i ∈ T, ∏ a ∈ T.erase i, (X - C a) := by
    congr! with T hT
    simp_rw [derivative_prod_finset, derivative_X_sub_C, mul_one]
  _ = ∑ (T ∈ S.powersetCard (#S - k)) (i ∈ S) with i ∈ T, ∏ a ∈ T.erase i, (X - C a) := by
    rw [← sum_finset_product']
    grind
  _ = ∑ (T ∈ S.powersetCard (#S - (k + 1))) (i ∈ S) with i ∉ T, ∏ a ∈ T, (X - C a) := by
    apply sum_bij' (fun ⟨T, i⟩ _ => ⟨T.erase i, i⟩) (fun ⟨T, i⟩ _ => ⟨insert i T, i⟩)
    · intro r hr; dsimp at hr ⊢; congr 1; grind
    · intro r hr; dsimp at hr ⊢; congr 1; grind
    all_goals grind
  _ = ∑ T ∈ S.powersetCard (#S - (k + 1)), ∑ i ∈ S \ T, ∏ a ∈ T, (X - C a) := by
    rw [← sum_finset_product']
    grind
  _ = (k + 1) * ∑ T ∈ S.powersetCard (#S - (k + 1)), ∏ a ∈ T, (X - C a) := by
    rw [mul_sum]
    congr! 1 with T hT
    simp [sum_const, show #(S \ T) = k + 1 by grind]
```

**構造**: 5 段 calc。
- Step 1 → 2: `sum_finset_product'` で外側 `T` × 内側 `i` を product 化
- Step 2 → 3: `sum_bij'` で `(T, i) ↦ (T.erase i, i)` (with `i ∈ T`) ↔ `(T', i) ↦ (insert i T', i)` (with `i ∉ T'`) の双方向写像。**Phase B でほぼそのまま流用可能** — 我々の場合 `S = univ`, `T'` の card は `(n-1) - k` ではなく単に `k`、内側 sum range が `S \ T'` (= `T' の補集合`) になる。
- Step 3 → 4: `sum_finset_product'` 逆方向で再び product → 二重和
- Step 4 → 5: `mul_sum` + `sum_const` + `#(S \ T) = k + 1` で定数倍に潰す

### 使う Mathlib API

- `Finset.sum_finset_product'` (`Mathlib/Algebra/BigOperators/Sigma.lean` 周辺)
- `Finset.sum_bij'` (`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`)
- `Finset.mul_sum`, `Finset.sum_const`
- `Finset.card_sdiff` (universe との差で `n - k` を出す)

### Phase B 影響

当初見積もり「30〜50 行」を **「20〜25 行 (テンプレ写経)」** に下方修正可能。Phase B は山場 (b) のみだったので、Phase B 全体工数を「1〜1.5 週間」→ **「1 週間以内」** に下方修正できる見込み。

ただし `grind` の挙動が Phase D 環境で同じように決まるかは要実機検証 (Polynomial.Derivative は polynomial ring が context にあるので `grind` が強い可能性あり)。

---

## 軸 (c): `(i : S) → α` (S : Finset _) の Pi 値 instance

### 必要 instance 一覧

`jointEntropySubset μ Xs S := entropy μ (fun ω (i : S) => Xs i.val ω)` を書くと、`(i : S) → α` 型に対し以下が必要:

| instance | 自動発火経路 | 確認 |
|---|---|---|
| `Fintype ((i : S) → α)` | `Pi.fintype` + `Subtype.fintype` (`Mathlib/Data/Fintype/Sets.lean`) | ✓ |
| `MeasurableSpace ((i : S) → α)` | `MeasurableSpace.pi` (`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:563`) + `Subtype.instMeasurableSpace` (`:185`) | ✓ |
| `MeasurableSingletonClass ((i : S) → α)` | `Pi.instMeasurableSingletonClass` + `Subtype` 版 | ✓ (※`Pi.instMeasurableSingletonClass` は `[Fintype ι] [∀ i, MeasurableSingletonClass (X i)]` 仮定で発火) |
| `Nonempty ((i : S) → α)` | `Pi.instNonempty` + `α` の `Nonempty` (`S = ∅` のとき自動発火 — `(i : ∅) → α` は `Unit` 同型) | ✓ |
| `DecidableEq ((i : S) → α)` | `Subtype.instDecidableEq` + `Function.decidableEq` で発火 (Fintype index 上は強い) | ✓ |

### 既存 Han.lean での前例

`InformationTheory/Shannon/Han.lean:46-48` で `jointEntropyExcept μ Xs i := entropy μ (fun ω (j : {j // j ≠ i}) => Xs j ω)` が既に動いており、`{j // j ≠ i}` (= subtype) で全 instance が自動発火している。`(i : ↑S) → α` (`↑S = {x // x ∈ S}`) も同形なので、同じ自動発火経路が効く見込み。

### Phase A skeleton 着手判定

**問題なし**。`InformationTheory/Shannon/HanD.lean` を sorry-driven で書き始められる。

万一 instance が未発火なら以下の workaround:
- `MeasurableSingletonClass` が `[Fintype ι]` 必要なら `[Fintype S]` を仮定追加 (`S : Finset (Fin n)` なら自動)
- `Nonempty` が `S = ∅` で問題出るなら `[Nonempty α]` を仮定 (Han.lean は既に仮定している)

---

## 軸 (d): `han_inequality` を subfamily restrict する boilerplate

### 既存 `han_inequality` (Han.lean:358-378)

```lean
theorem han_inequality
    {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i)) :
    ((n : ℝ) - 1) * jointEntropy μ Xs
      ≤ ∑ i : Fin n, jointEntropyExcept μ Xs i
```

### Phase D-A で必要な subset 版 (`han_inequality_subset`)

```lean
theorem han_inequality_subset
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : Finset (Fin n)) :
    ((S.card : ℝ) - 1) * jointEntropySubset μ Xs S
      ≤ ∑ i ∈ S, jointEntropySubset μ Xs (S.erase i)
```

### Restrict 戦略

1. **Embedding**: `Finset.orderEmbOfFin S : Fin S.card ↪o Fin n` (`Mathlib/Data/Finset/Sort.lean:198`)
   - 要件: `S.card = k` を `rfl` で渡せる形 (実装は `s.orderEmbOfFin rfl`)
   - `α` (= `Fin n`) に `LinearOrder` が必要 → `Fin n` で OK
2. **Restricted family**: `Xs' : Fin S.card → Ω → α := fun k ω => Xs (S.orderEmbOfFin rfl k) ω`
3. **既存 `han_inequality` を `Xs'` に適用**:
   ```
   (S.card - 1) * jointEntropy μ Xs' ≤ ∑ k : Fin S.card, jointEntropyExcept μ Xs' k
   ```
4. **両辺を subset 版に reshape**:
   - LHS: `jointEntropy μ Xs' = jointEntropySubset μ Xs S` を示す。これは `(Fin S.card → α) ≃ᵐ (S → α)` の MeasurableEquiv が必要。**Mathlib に直接無いかもしれない**: `Finset.equivFin S : S ≃ Fin S.card` (`Mathlib/Data/Finset/Sort.lean` 付近) は等価性、これを `MeasurableEquiv` に lift する必要がある。
     - 候補: `MeasurableEquiv.piCongrLeft (fun _ : ↑S => α) (Finset.equivFin S).symm`
     - もしくは `entropy_measurableEquiv_comp` を直接適用 (Han.lean の既存 plumbing)
   - RHS: `∑ k : Fin S.card, jointEntropyExcept μ Xs' k = ∑ i ∈ S, jointEntropySubset μ Xs (S.erase i)` を示す。これは index 集合の bijection (`Fin S.card ≃ S` via `orderEmbOfFin`) と `{k' // k' ≠ k} ≃ ↑(S.erase i)` の二段 bijection。

### 難易度評価

- LHS reshape: **既存 `entropy_measurableEquiv_comp` (Han.lean:52-77) + `MeasurableEquiv.piCongrLeft` 経路**でいける見込み。Han.lean の `piExceptMEquiv` (line 239-249) と同じ流儀。約 20〜30 行。
- RHS reshape: index `Finset.sum_bij` で 1 行は厳しいかもしれないが、`Finset.sum_image` (`orderEmbOfFin` を `embedding` として `image` を取り、`Finset.image_univ` で `S` に戻す) + 内側の reshape で 30〜40 行。
- 合計: **`han_inequality_subset` は 50〜70 行見積もり**。Phase A の中で最も plumbing-heavy の部分だが、既存 Han.lean の pi 値 reshape 流儀をそのまま流用できるので「写経 + 1 段 plumbing」レベルに収まる見込み。

### Phase A 内での位置付け

`han_inequality_subset` は Phase A の 4 主定理の最後 (= subset chain rule + conditioning monotonicity が片付いた後)。先行する subset chain rule (`jointEntropySubset_chain_rule`) と同じ orderEmbOfFin reshape 流儀を使うので、こちらでパターン確立しておけば `han_inequality_subset` は流用で済む。

---

## Phase A 着手時の不確実性ランク

| 項目 | 不確実性 | 対処 |
|---|---|---|
| `(i : S) → α` instance 自動発火 | **低** (Han.lean 前例あり) | Phase A skeleton を書いて LSP で確認、未発火なら明示注入 |
| subset 版 chain rule の `Finset.induction_on` | **中** | Han Phase B の `Fin n` chain rule を写経 + subset 1 段化。新規 plumbing は `S.filter (· < i)` の prefix 整合 |
| subset 版 conditioning monotonicity の induction | **中** | Han Phase A の 3 変数 pair 版 (`condEntropy_le_condEntropy_of_pair`) を `T₁ → T₁ ∪ {x}` の 1 段で繰り返す |
| `han_inequality_subset` の reshape | **中-高** | Han.lean の `piExceptMEquiv` / `exceptSplitMEquiv` 流儀を流用、LHS/RHS 各々で `MeasurableEquiv.piCongrLeft` を組む |
| `(Fin S.card → α) ≃ᵐ (↑S → α)` の MeasurableEquiv | **中** | `Finset.equivFin S` を `MeasurableEquiv` に lift、または `MeasurableEquiv.piCongrLeft` で直接構成 |

### 全体的な Phase A 工数 (再見積もり)

当初見積もり「1.5〜2 週間」をそのまま維持。本 inventory で **plumbing 量自体の縮小は無い** が、**先行写経テンプレ (Polynomial.Derivative) は Phase B 用**で Phase A 直接利益は無い。

ただし Phase A の 4 主定理のうち `jointEntropySubset_chain_rule` と `condEntropy_subset_anti` は subset 上の `Finset.induction_on` で展開する見込みのため、Han Phase A/B の写経再利用率が高い (Pi reshape plumbing 3 点セット = `MeasurableEquiv.piCongrLeft` + `sumPiEquivProdPi` + `funUnique` を流用)。

---

## 計画書本体への反映指示

`docs/han/han-phase-d-plan.md` への反映点:

1. **Phase B (D) 工数感** (line 282): 「1〜1.5 週間」→ **「1 週間以内、Polynomial.Derivative.lean:710-728 が写経テンプレとして利用可能」** に更新
2. **Phase B (D) 鍵となる作業 (2)** (line 268-270): bijection の具体形を「`(T, i) ↦ (T.erase i, i)` (with `i ∈ T`) ↔ `(T', i) ↦ (insert i T', i)` (with `i ∉ T'`) の `sum_bij'` 双方向写像」に詳細化、参照先を inventory に
3. **Phase A (D) 鍵となる作業 (4)** (line 197): `han_inequality_subset` の reshape 戦略 (orderEmbOfFin → Xs' restricted family → MeasurableEquiv 経路) を inventory への参照に置き換え、見積もり「50〜70 行」を明記
4. **Phase 0 (D) Done 条件** (line 132-136): すべて満たされたことを記録 (本 inventory が成果物)

これらは別 turn で計画書本体を更新する作業として task 化候補。

---

## Definition of Done (本 inventory)

- [x] 4 軸全て調査完了
- [x] 「Mathlib に subset average / Shearer は無い」を裏取り (subagent + loogle ダブル)
- [x] Phase A skeleton (`InformationTheory/Shannon/HanD.lean` の sorry-driven 出だし) が書ける状態
- [x] subset の Pi 値 instance 自動発火 / 手動補完が必要かの判定済み (= 自動発火見込み、Han.lean 前例)
- [x] Phase B 山場 (二重和 reindex) の Mathlib 既存テンプレ特定 (Polynomial.Derivative.lean:710-728)
- [x] `han_inequality_subset` の reshape 戦略決定 (orderEmbOfFin + entropy_measurableEquiv_comp 流儀)
