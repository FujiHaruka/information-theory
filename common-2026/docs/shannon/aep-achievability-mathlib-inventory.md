# Shannon: AEP Phase E (源符号化定理 achievability) Mathlib インベントリ サブ計画

> **Parent**: [`aep-achievability-plan.md`](aep-achievability-plan.md) §Phase 0
>
> 親 inventory:
> - [`aep-mathlib-inventory.md`](aep-mathlib-inventory.md) (AEP Phase A〜C 用、6 軸)
> - [`aep-source-coding-mathlib-inventory.md`](aep-source-coding-mathlib-inventory.md) (Phase D 用、5 軸)
>
> 本 inventory はその **delta** に絞る。Phase A〜C / D で確定済みの
> `Filter.liminf` / `iIndepFun` / `entropy_jointRV_eq_n_smul` /
> `MeasureFano.errorProb` / `Tendsto` 構成補助 等は再記載しない。
> Phase E で **新たに必要 / 親で未確定** の 4 軸のみを以下に記録。

<!--
雛形メモ: CLAUDE.md「Subagent Inventory of Mathlib Lemmas」規約に従う
- file:line / 完全署名 / 引数型 / 結論形 verbatim
- `[..]` プレリク鍵括弧は **必ず** verbatim 保持 (paraphrase 禁止)
- "無し" でも探索した query を記録 (negative grep / loogle 結果は資産)
-->

## 進捗

- [x] 軸 1: typical set の 3 性質 (現行 `Common2026/Shannon/AEP.lean` Phase B/C verbatim 引用)
- [x] 軸 2: `Finset` ↔ `Fin` 列挙 API (`Finset.equivFin`, `Set.Finite.toFinset` 系)
- [x] 軸 3: `M_n = 2^⌈nR⌉` 構成 + `Real.log (M_n) / n → R` 漸近 (`Nat.ceil` API)
- [x] 軸 4: errorProb の reuse (Phase D 形と Phase E achievability 形の整合)

## ゴール / Approach

AEP Phase E (achievability) 着手前に、4 軸で **新規自前構築量 vs Mathlib / Common2026 既存資産** を固定する。

**結論先取り**:

- **軸 1 (typical set 3 性質) は Phase A〜C で完備** ─ `measurableSet_typicalSet`、`typicalSet_card_le`、`typicalSet_prob_tendsto_one` の 3 本がすでに 0 sorry で立っている。Phase E は (a) `card_le` を encoder 構成の injectivity に、(b) `prob_tendsto_one` の補集合を error rate → 0 の核に直接利用する。
- **軸 2 (`Finset.equivFin`) は Mathlib に完備** ─ `Finset.equivFin : s ≃ Fin #s` (`noncomputable`) で `s : Finset α` を `Fin #s` に bijection。Phase E では `s := (typicalSet μ Xs n ε).toFinite.toFinset` に対して使う。**注意**: `s ≃ Fin #s` は `↑s` 型 (= subtype) 相手なので、`(Fin n → α)` 全体への encoder にするには **(a) typical 部分は equivFin で `Fin #s` 化、(b) 非 typical 部分は default index に潰す** の二段が必要。
- **軸 3 (`M_n = 2^⌈nR⌉`)** ─ `Nat.ceil` API は完備 (`Nat.le_ceil` / `Nat.ceil_le` / `Nat.ceil_lt_add_one`)。`Real.log (2^⌈nR⌉) / n → R · log 2` の漸近は `Real.log_pow` + `(⌈nR⌉ : ℝ) / n → R` (squeeze: `nR ≤ ⌈nR⌉ < nR + 1` で `(⌈nR⌉ : ℝ) / n - R ≤ 1/n → 0`) で組成。**判断**: 教科書通り `2^⌈nR⌉` を取るか、log 基底揃えのため `⌈Real.exp (n · R)⌉` を取るかは Phase B 着手時に判断 (後者なら `log` 1 回で済むが教科書からは離れる、前者なら `log 2` plumbing を払う)。**主路線は `Nat.ceil (Real.exp (n · R))`** で `log` 基底を揃える (Phase C 既存 `Real.log` plumbing と整合、教科書とのズレは別 lemma で `log_2` 換算)。
- **軸 4 (errorProb 再利用)** ─ Phase D の `errorProb μ (jointRV Xs n) (fun ω => c (jointRV Xs n ω)) d` 形 (= 自己復号 error rate) と完全一致。Phase E は **encoder/decoder を構築側で与える**ところが Phase D との対比 (Phase D は forall code → 結論、Phase E は exists code、結論)。

---

## 軸 1: typical set の 3 性質 (verbatim 再引用)

### `measurableSet_typicalSet` (Phase B)

- **file:line**: `Common2026/Shannon/AEP.lean:240`
- **完全署名 verbatim**:
  ```lean
  theorem measurableSet_typicalSet
      (μ : Measure Ω)
      (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
      MeasurableSet (typicalSet μ Xs n ε)
  ```
- **`[..]` プレリク verbatim**: section variable `[MeasurableSpace Ω]` `[Fintype α]` `[DecidableEq α]` `[Nonempty α]` `[MeasurableSpace α]` `[MeasurableSingletonClass α]` (= AEP.lean のファイル variable)
- **本 plan での用途**: encoder `c_n` の measurability 派生 (encoder = "if `x ∈ typicalSet` then `equivFin` index else default")、各 sub-block measurability の plumbing。Phase E では **`Set.Finite (typicalSet μ Xs n ε)`** (= ファイル内 `(typicalSet μ Xs n ε).toFinite` で常に成立、`Fin n → α` が Fintype) も同時に使う。

### `typicalSet_card_le` (Phase C size bound)

- **file:line**: `Common2026/Shannon/AEP.lean:257`
- **完全署名 verbatim**:
  ```lean
  theorem typicalSet_card_le
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
      (hpos : ∀ x : α, 0 < (μ.map (Xs 0)).real {x})
      (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      ((typicalSet μ Xs n ε).toFinite.toFinset.card : ℝ) ≤
        Real.exp ((n : ℝ) * (entropy μ (Xs 0) + ε))
  ```
- **`[..]` プレリク verbatim**: ファイル variable + `[IsProbabilityMeasure μ]`
- **本 plan での用途**: Phase E の **encoder 構成の core**: `M_n := Nat.ceil (Real.exp (n · R))` (rate `R > H + ε`) と組み合わせて `(typicalSet μ Xs n ε).toFinite.toFinset.card ≤ exp(n(H+ε)) ≤ exp(nR) ≤ M_n` で injection が立つ。**仮定 `hpos` は Phase E にも継承** (Phase C で固定済み、`Pmf` support 全体仮定)。

### `typicalSet_prob_tendsto_one` (Phase C 確率 → 1)

- **file:line**: `Common2026/Shannon/AEP.lean:375`
- **完全署名 verbatim**:
  ```lean
  theorem typicalSet_prob_tendsto_one
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
      (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
      (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
      {ε : ℝ} (hε : 0 < ε) :
      Tendsto
        (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ typicalSet μ Xs n ε})
        atTop
        (𝓝 1)
  ```
- **`[..]` プレリク verbatim**: ファイル variable + `[IsProbabilityMeasure μ]`
- **本 plan での用途**: **error rate → 0 の核**。error 事象 `{ω | d_n (c_n (X^n ω)) ≠ X^n ω}` を **`{ω | jointRV Xs n ω ∉ typicalSet μ Xs n ε}` の subset** で評価 (encoder/decoder を typical 集合上で正逆対応として構成、非 typical でのみ error が起こる設計)、`prob_tendsto_one` ⟹ `μ {ω | ... ∉ T} → 0` (補集合)、subset monotonicity で `error → 0`。**仮定**: `Pairwise IndepFun` (Phase A〜C と同じ)。Phase E の statement は Phase D に合わせ `iIndepFun` で受け、`iIndepFun.indepFun` で Pairwise に lift。

### 結論

**typical set 3 性質はすべて既存、新規構築ゼロ**。Phase E は **3 性質を直接組み合わせるだけ**。

---

## 軸 2: `Finset` ↔ `Fin` 列挙 API (encoder/decoder bijection の素材)

### `Finset.equivFin` (subtype の Fin 化)

- **file:line**: `.lake/packages/mathlib/Mathlib/Data/Fintype/EquivFin.lean:320`
- **完全署名 verbatim**:
  ```lean
  noncomputable def Finset.equivFin (s : Finset α) : s ≃ Fin #s :=
    Fintype.equivFinOfCardEq (Fintype.card_coe _)
  ```
- **`[..]` プレリク verbatim**: なし (ただし暗黙に `[DecidableEq α]` が `Finset` の subtype 構成で要 — 本 plan では `α := Fin n → α_0` で `[DecidableEq (Fin n → α_0)]` 自動 derive)
- **本 plan での用途**: encoder の core。`(typicalSet μ Xs n ε).toFinite.toFinset.equivFin : ↑((...).toFinite.toFinset) ≃ Fin (...).toFinite.toFinset.card`。**注意**: 戻り値は `Fin #s` (= `Fin (toFinset.card)`) であって `Fin M_n` ではない。`Fin (toFinset.card) → Fin M_n` には別途 `Fin.castLE` 系の embedding を組む (`toFinset.card ≤ M_n` を `typicalSet_card_le` から)。

### `Finset.equivFinOfCardEq` (cardinality を直接指定)

- **file:line**: `.lake/packages/mathlib/Mathlib/Data/Fintype/EquivFin.lean:325`
- **完全署名 verbatim**:
  ```lean
  noncomputable def Finset.equivFinOfCardEq {s : Finset α} {n : ℕ} (h : #s = n) : s ≃ Fin n :=
    Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h)
  ```
- **本 plan での用途**: 直接は使わない (cardinality は Phase E では一般に `≤` でしか触らない)、参考。

### `Set.Finite.toFinset` 周辺 API

- **file:line**: `.lake/packages/mathlib/Mathlib/Data/Set/Finite/Basic.lean:23` 以降
- **本 plan での用途**: `(typicalSet μ Xs n ε).toFinite.toFinset` は Phase C `typicalSet_card_le` で既出、API は完備 (`Set.Finite.mem_toFinset` 等)。`Set.Finite (typicalSet ...)` は `Fin n → α` が Fintype なので `Set.toFinite` で自動派生。

### `Fin.castLE` (`Fin n → Fin m` for `n ≤ m`)

- **file:line**: `.lake/packages/mathlib/Mathlib/Data/Fin/Basic.lean` (loogle で取得)
- **本 plan での用途**: `Fin (toFinset.card) ↪ Fin M_n` の embedding を `castLE` で 1 行構成。`toFinset.card ≤ M_n` は Phase E の core inequality (`typicalSet_card_le` + `M_n ≥ exp(n(H+ε))`)。

### 結論

**`Finset.equivFin` で typical 部分の bijection、`Fin.castLE` で `Fin M_n` への埋め込みが取れる**。encoder/decoder は以下の構造:

```
encoder c_n : (Fin n → α) → Fin M_n :=
  fun x =>
    if hx : x ∈ (typicalSet μ Xs n ε).toFinite.toFinset
    then Fin.castLE h_card_le ((toFinset.equivFin) ⟨x, hx⟩).val_lt_card.cast
    else 0  -- non-typical: default to 0

decoder d_n : Fin M_n → (Fin n → α) :=
  fun k =>
    if hk : k.val < (typicalSet μ Xs n ε).toFinite.toFinset.card
    then ((toFinset.equivFin).symm ⟨k.val, hk⟩).val
    else default  -- pad index: arbitrary
```

`d_n ∘ c_n = id` on `typicalSet`、外側は arbitrary。**error 事象 ⊆ {x ∉ typicalSet}**。

**plumbing 量**: encoder/decoder def + `d_n ∘ c_n = id on typical` の round-trip lemma + `error ⊆ ∁ typicalSet` の subset 補題。30〜60 行見積。

---

## 軸 3: `M_n` 構成 (`Nat.ceil (Real.exp (n · R))`)

### `Nat.le_ceil` / `Nat.ceil_lt_add_one`

- **file:line**: `.lake/packages/mathlib/Mathlib/Algebra/Order/Floor/Semiring.lean` (loogle で取得)
- **完全署名 (loogle 結果より):**
  - `Nat.le_ceil (x : α) : x ≤ Nat.ceil x` (where `α` is e.g. `ℝ` with `LinearOrderedSemifield`)
  - 関連: `Nat.ceil_lt_add_one` / `Nat.ceil_le` / `Nat.lt_ceil`
- **本 plan での用途**: `(M_n : ℝ) = (Nat.ceil (Real.exp (n · R)) : ℝ) ∈ [exp(nR), exp(nR) + 1)` の挟み込み。これから:
  - **encoder injectivity**: `(typicalSet ...).card ≤ exp(n(H+ε)) ≤ exp(nR) ≤ M_n` (要 `H + ε ≤ R`、Phase E の前提 `R > H` から `ε := (R − H) / 2` 等で確保)
  - **rate 漸近**: `Real.log (M_n) / n → R` ─ `log(exp(nR)) ≤ log(M_n) ≤ log(exp(nR) + 1)`、両辺 / n → R (上下挟み込み squeeze)。約 20〜40 行 plumbing

### `Real.log_pow` / `Real.log_exp` / `Real.exp_log`

- **既存 Common2026 利用前例**: `AEP.lean` Phase B (`Real.exp_log (hpos x)` で 1 行)、Phase D Phase B (`Real.log_pow` Step E)
- **本 plan での用途**: rate 漸近 `log (Nat.ceil (Real.exp (n · R))) / n → R` の組成。

### `tendsto_one_div_atTop_nhds_zero_nat`

- **既存 Phase D Phase C (C.1) で利用**: `1/n → 0` を組成、`Tendsto.add` / `Tendsto.const_sub` で `(log M_n / n) - R → 0` を構成。

### 結論

**`M_n := Nat.ceil (Real.exp (n · R))` は Mathlib `Nat.ceil` API で plumbing が完備**。rate 漸近 `log M_n / n → R` は 20〜40 行で組成可能。**判断**: `2^⌈nR⌉` (教科書形) ではなく `⌈exp(nR)⌉` を取るのは、Phase C 既存 `Real.exp` plumbing と整合させるため (`log 2` の換算 plumbing を回避)。

---

## 軸 4: errorProb の reuse (Phase D 形との整合)

### `MeasureFano.errorProb` (再掲、Phase D で確定済)

- **file:line**: `Common2026/Fano/Measure.lean:73`
- **本 plan での用途**: `errorProb μ (jointRV Xs n) (fun ω => c (jointRV Xs n ω)) d` 形を Phase D と完全に同形で使用。**Phase D は forall code で結論を出す、Phase E は exists code で同じ errorProb 形を構成**。

### Phase E 主定理の statement 形 (Phase D との対比)

```lean
-- Phase D (converse): forall code → liminf rate ≥ H
theorem source_coding_converse :
    entropy μ (Xs 0) ≤ Filter.liminf (fun n => Real.log (M n) / n) atTop

-- Phase E (achievability): exists code → error → 0 ∧ rate → R
theorem source_coding_achievability
    (hR : entropy μ (Xs 0) < R) :
    ∃ M : ℕ → ℕ, ∃ c : ∀ n, (Fin n → α) → Fin (M n),
       ∃ d : ∀ n, Fin (M n) → (Fin n → α),
      Tendsto (fun n => Real.log (M n : ℝ) / n) atTop (𝓝 R) ∧
      Tendsto (fun n => InformationTheory.MeasureFano.errorProb μ
                          (jointRV Xs n) (fun ω => c n (jointRV Xs n ω)) (d n))
              atTop (𝓝 0)
```

`errorProb` 表現は完全に同形、**rate 部分の Tendsto は Phase D が `liminf` で受けるのに対して Phase E は `Tendsto _ (𝓝 R)` で受ける** (achievability は具体構成なので exact rate)。

### 結論

**新規 formalism ゼロ、既存 `errorProb` を直接利用**。Phase D の statement 形と完全並行。

---

## 結論サマリ (各軸 1 行)

| 軸 | 結論 | Phase 影響 |
|---|---|---|
| 1 typical set 3 性質 | **Phase A〜C で完備**、3 本を encoder 構成 + error rate に直接利用 | 新規構築ゼロ |
| 2 `Finset.equivFin` + `Fin.castLE` | **Mathlib 完備**、subtype bijection + `Fin M_n` 埋め込みで encoder/decoder 組成 | encoder/decoder def + round-trip lemma で 30〜60 行 |
| 3 `Nat.ceil (Real.exp (n · R))` | **Mathlib 完備**、`Nat.le_ceil` + `Real.log_exp` + 既存 `1/n → 0` で rate 漸近組成 | rate Tendsto plumbing 20〜40 行 |
| 4 errorProb reuse | **Phase D と完全同形**、新規 formalism ゼロ | 主定理 statement で並行使用 |

---

## Phase E 着手判定

**GO**:

- 唯一の **不確実性** は **軸 2 (encoder の `if hx : x ∈ ...` 分岐の measurability + injectivity 補題)** で、これは `Set.toFinite.toFinset` のメンバーシップが `Fin n → α` Fintype + `MeasurableSingletonClass` で自動派生する範囲。前例として Phase B `measurableSet_typicalSet` で同種の `Set.toFinite` plumbing が通っている
- 軸 3 の `M_n` 構成は `Nat.ceil` API が完備、Stein converse Phase C 形 `Tendsto` squeeze と同形 plumbing
- 全体として **新規 plumbing は (a) encoder/decoder の構成 + (b) error rate ⊆ ∁ typicalSet の subset 補題 + (c) rate Tendsto + (d) error rate Tendsto**、4 ピースのみ
- 主路線は **standalone achievability statement** (Phase D とは別 theorem として並列に並べる)。**combined unified statement** (`liminf log M_n / n = entropy μ X` の両側等号) は **Phase F (deferred)** として切り出す

## Definition of Done (本 inventory)

- [x] 4 軸全て調査完了
- [x] typical set 3 性質の verbatim 署名 + `[..]` プレリク確定 (`Common2026/Shannon/AEP.lean` の現行コードから引用)
- [x] `Finset.equivFin` / `Finset.equivFinOfCardEq` の verbatim 署名確定、`Set.Finite.toFinset` 周辺 API 完備確認
- [x] `Nat.ceil` API + `Real.exp` / `Real.log` 周辺の Phase D 既存 plumbing 確認、rate 漸近の組成パス確定
- [x] errorProb は Phase D と同形で再利用、新規 formalism ゼロ
- [x] Phase E skeleton (`Common2026/Shannon/AEP.lean` 末尾 append、`source_coding_achievability` 主定理 + 補助 4 本) が書ける状態

## 判断ログ

書く頻度: 方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

<!-- 本 inventory はまだ起草段階。本体着手で発見があれば追記。 -->
