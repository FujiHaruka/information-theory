# Han Phase D ロードマップ: subset average → Shearer 🌙

> **Status (2026-05-10): 起草。** Han 不等式ムーンショット ([han-moonshot-plan.md](han-moonshot-plan.md)) Phase A/B/C 完了 (`Common2026/Shannon/Han.lean` zero sorry) を受けた後継。
>
> ゴールは **Han 1978 原論文の subset average 形 ($H_1 \ge H_2 \ge \cdots \ge H_n$)** をまず形式化し、続けて **Shearer の不等式** ($k$-cover 条件下 $k \cdot H(X_{[n]}) \le \sum_j H(X_{S_j})$) に lift すること。中間 abort 可能で、D-1 (subset average) 完了時点で publish 価値あり。

## Context

### モチベーション

Han 完了 (補集合形 $(n-1) H(X_{[n]}) \le \sum_i H(X_{[n]\setminus\{i\}})$) で `Common2026/Shannon/Han.lean` の主定理 + Pi 値 plumbing (`MeasurableEquiv.piCongrLeft` + `sumPiEquivProdPi` + `funUnique` 3 点セット、index 同型 `exceptIdxEquiv` / `fullIdxEquiv`) が整備された。**しかし subset 版 (`Finset (Fin n)` 上の jointEntropy) には踏み込んでいない** — Han の RHS は「特定の `i` を除いた」固定形だけだったため。

Phase D で `jointEntropySubset μ Xs S` (`S : Finset (Fin n)`) を導入すると以下が顕在化する:

1. **subset 上の plumbing** — `(i : S) → α` 型の Pi instance 自動発火 / `Finset.powersetCard` 上の二重和 re-index / `Finset.embedding` 経由の `han_inequality` 適用。Han の `{j // j ≠ i}` 補集合は subset の特殊形でしかなく、汎用版を作ることで以後の n 変数化テーマ全部に再利用できる
2. **D-1 / D-2 共通 engine** — 両者とも (a) subset 版 chain rule、(b) subset 版 conditioning monotonicity に分解できる。これは Han Phase A の 2 変数版を subset に格上げしたもの
3. **Han 本体を engine 呼び出しできるか確認** — D-1 の証明骨格は「各 $(k+1)$-subset で `han_inequality` を呼ぶ + 平均化」。Han の statement が subset 版の subgoal に綺麗にハマるか、subfamily restrict の boilerplate がどれだけ出るかが見どころ

### 最終到達点

**D-1: Han 1978 subset average 形 (連鎖):**

```lean
theorem subset_average_chain
    {n : ℕ}
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                [MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {k₁ k₂ : ℕ} (h1 : 1 ≤ k₁) (h12 : k₁ ≤ k₂) (h2 : k₂ ≤ n) :
    averageSubsetEntropy μ Xs k₂ ≤ averageSubsetEntropy μ Xs k₁
```

ここで `averageSubsetEntropy μ Xs k := (∑ S ∈ powersetCard k univ, jointEntropySubset μ Xs S) / (k * (n.choose k))` (= 文献 $H_k$)。

**D-2: Shearer の不等式 (整数 covering):**

```lean
theorem shearer_inequality
    {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                [MeasurableSpace α] [MeasurableSingletonClass α]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {ι : Type*} [Fintype ι]
    (S : ι → Finset (Fin n))
    {k : ℕ} (hk : ∀ i : Fin n, k ≤ (Finset.univ.filter (fun j => i ∈ S j)).card) :
    (k : ℝ) * jointEntropy μ Xs ≤ ∑ j : ι, jointEntropySubset μ Xs (S j)
```

### 非ゴール

- **D-3 異種類型 `Xs : ∀ i, Ω → α i`** — 別 plan に切り出し。Phase D ではホモジニアス (`α` 固定) のまま
- **fractional cover Shearer** — LP relaxation 形 ($k \in \mathbb{R}_{\ge 0}$ + 各 $i$ の被覆「重み和」が $\ge k$)。整数 covering で textbook 形は十分カバー
- **Brascamp-Lieb / log-Sobolev 系の続き** — Shearer の解析的一般化方向。情報理論の outside
- **subset average の strict 単調性** — 等号成立条件 ($X_i$ 独立等)。本 plan は弱単調 ($\le$) で打ち止め
- **Mathlib upstream PR** — 副産物として歓迎、能動的には追わない

---

## Approach

**4 段構成 (Phase 0 → A → B → C)。Phase A で「subset 版 entropy infrastructure」、Phase B で「D-1 = Han の連鎖系」、Phase C で「D-2 = Shearer」。**

```
Phase 0 (D) : Mathlib + 既存 Han API インベントリ            ← 1 ターン
              ──────────────────────────────────────────
Phase A (D) : subset 版 jointEntropy infrastructure         ← D-1 / D-2 共有 layer
              ──────────────────────────────────────────
Phase B (D) : D-1 subset average chain                      ← Han を engine 呼び出し
              ──────────────────────────────────────────
Phase C (D) : D-2 Shearer 🌙                                 ← 同 engine を別形に再演
```

### Approach の根幹: subset infrastructure を一度作って 2 用途で擦る

D-1 (subset average) と D-2 (Shearer) は statement の見た目が違うが、**証明の engine は同じ** ── (a) subset 版 chain rule $H(X_S) = \sum_{i \in S, \text{order}} H(X_i \mid X_{S \cap <i})$、(b) subset 版 conditioning monotonicity $H(X_i \mid X_{T_1}) \ge H(X_i \mid X_{T_2})$ ($T_1 \subseteq T_2$)、の 2 本に乗る。

Phase A でこの 2 本 + `jointEntropySubset` の定義を一度書き、Phase B / C でそれぞれ別の集約 (B = $\binom{n}{k+1}$ 平均化 / C = covering count aggregation) を被せる。

### D-1 と D-2 の関係: 並列ではなく Phase B → C の階段

| 候補 | 何を Han から引き継ぐか | 何が新規か |
|---|---|---|
| D-1 (Phase B) | `han_inequality` を **subset embedding 経由で適用** | $(k{+}1)$-subset 上の二重和 re-index ($\sum_{|S|=k+1}\sum_{i\in S} f(S\setminus\{i\}) = (n{-}k) \sum_{|T|=k} f(T)$)、$H_k$ 連鎖 |
| D-2 (Phase C) | engine (chain rule + conditioning monotonicity) のみ。Han 本体は呼ばない | 任意 covering family $S_j$ 上の直接 aggregation。Han が暗黙に依存していた「$|S| = n-1$ 固定」を解除 |

**Phase C が Phase B を strict subsume するわけではない** — Shearer から $H_k$ 連鎖は直接出ない (Shearer は「$H_k \ge H_n$ 全て」を出すが連鎖 $H_k \ge H_{k+1}$ は出ない)。なので「D-1 完了で打ち止め」も「D-1 + D-2 両方」も独立に publish 価値がある。

### Han 本体との比較: subset 版 chain rule の追加コスト

Han Phase B の `jointEntropy_chain_rule` は `Fin n` 全体に対する chain rule で、prefix `Fin i` で条件付ける形。subset 版は `Finset.sortedRange` (or `Finset.orderEmbOfFin`) 経由で「$S$ 内の最小→最大の順序」で induction を回す必要があるので Phase A B-2 (Han) より plumbing が 1 段重い。具体的には:

- subset chain rule: $H(X_S) = \sum_{i \in S} H(X_i \mid X_{S_{<i}})$ where $S_{<i} := \{j \in S : j < i\}$
- 証明: `Finset.induction_on` で `S` を 1 元ずつ追加、Han Phase A の 2 変数 `entropy_pair_eq_entropy_add_condEntropy` を各段で呼ぶ
- conditioning monotonicity (subset): `S_{<i} \subseteq T_{<i} \Rightarrow H(X_i \mid X_{T_{<i}}) \le H(X_i \mid X_{S_{<i}})` (= 「条件付けで減る」を Han Phase A の 3 変数 pair 版から induction で持ち上げ)

### ファイル構成 (Phase C 終了時)

```
Common2026/Shannon/
  Entropy.lean        ← 既存 (Phase A 主定理)
  Han.lean            ← 既存 (Phase B/C 主定理 + Pi reshape plumbing)
  HanD.lean           ← 新規: jointEntropySubset, subset chain rule,
                        subset_average_chain, shearer_inequality
```

`Common2026.lean` (library root) に `import Common2026.Shannon.HanD` を追記。

---

## Phase 0 (D): Mathlib + 既存 Han API インベントリ

### スコープ

- **Mathlib 側に subset average / Shearer / 任意 covering 形のエントロピー不等式が既に存在しないか確認** (`InformationTheory/Shannon/`、`InformationTheory/KullbackLeibler/`、`Combinatorics/Entropy*` 等)
- **既存 `Common2026/Shannon/Han.lean` の subset 適用耐性レビュー**:
  - `han_inequality` を `Xs ∘ Finset.orderEmbOfFin S` 等で subfamily restrict する際の boilerplate
  - `(i : S) → α` (`S : Finset (Fin n)`) の `Fintype` / `MeasurableSpace` / `MeasurableSingletonClass` instance 自動発火
  - 既存 `entropy_measurableEquiv_comp` を subset の reshape (例: `(i : S) → α ≃ᵐ Fin S.card → α`) に流用可能か
- **`Finset.powersetCard` 周辺の和の操作 API インベントリ**:
  - `Finset.sum_powersetCard_succ` / `Finset.sum_image_of_injective` 等で二重和を一発で `(n-k)` 倍に潰せるか
  - 必要なら `Finset.bij` で手動 reindex

### 成果物

- `docs/han/han-phase-d-mathlib-inventory.md` — 上記 3 軸の調査結果 + Phase A 着手時の不確実性ランク
- 本計画書への反映 (Approach / Phase A 節)

### Done 条件

- 「Mathlib に subset average / Shearer は無い」を裏取り済み (loogle + rg)
- Phase A skeleton (`Common2026/Shannon/HanD.lean` の sorry-driven 出だし) が書ける状態
- subset の Pi 値 instance 自動発火 / 手動補完が必要かの判定済み

### 工数感

1 ターン (10〜15 分)。subagent 1 本 + ローカル `loogle` / `rg`。

### 結果 (2026-05-10 完)

成果物 `docs/han/han-phase-d-mathlib-inventory.md`。要点:

- (a) **Mathlib に subset average / Shearer 不在** (subagent + loogle ダブル裏取り) — Phase D 計画は破棄不要
- (b) Phase B 二重和 reindex の **写経テンプレが Mathlib 内に存在**: `Mathlib/Algebra/Polynomial/Derivative.lean:710-728` (`sum_finset_product'` × 2 + `sum_bij'` の 5 段 calc)
- (c) `(i : S) → α` Pi instance は Han.lean の `{j // j ≠ i}` 前例から自動発火見込み — Phase A 着手判定は GO
- (d) `han_inequality_subset` は `Finset.orderEmbOfFin S` + `entropy_measurableEquiv_comp` (既存 plumbing) で 50〜70 行見積もり

これを受けた Approach / Phase A / Phase B への反映は本ファイルに反映済 (下記)。

---

## Phase A (D): subset 版 jointEntropy infrastructure

### スコープ

```lean
namespace InformationTheory.Shannon

variable {n : ℕ}
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
                    [MeasurableSpace α] [MeasurableSingletonClass α]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- 部分集合 `S : Finset (Fin n)` 上の joint entropy。 -/
noncomputable def jointEntropySubset
    (μ : Measure Ω) (Xs : Fin n → Ω → α) (S : Finset (Fin n)) : ℝ :=
  entropy μ (fun ω (i : S) => Xs i.val ω)

/-- subset 版 chain rule:
`H(X_S) = ∑ i ∈ S, H(X_i | X_{S ∩ {j : j < i}})`。 -/
theorem jointEntropySubset_chain_rule
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : Finset (Fin n)) :
    jointEntropySubset μ Xs S
      = ∑ i ∈ S,
          condEntropy μ (Xs i)
            (fun ω (j : (S.filter (· < i))) => Xs j.val ω)

/-- subset 版 conditioning monotonicity:
`T₁ ⊆ T₂ ⟹ H(X_i | X_{T₂}) ≤ H(X_i | X_{T₁})`。 -/
theorem condEntropy_subset_anti
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (i : Fin n) {T₁ T₂ : Finset (Fin n)} (hT : T₁ ⊆ T₂) :
    condEntropy μ (Xs i) (fun ω (j : T₂) => Xs j.val ω)
      ≤ condEntropy μ (Xs i) (fun ω (j : T₁) => Xs j.val ω)

/-- Han を subset に適用:
`|S| ≥ 1 ⟹ (|S| - 1) · H(X_S) ≤ ∑ i ∈ S, H(X_{S \ {i}})`。 -/
theorem han_inequality_subset
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : Finset (Fin n)) :
    ((S.card : ℝ) - 1) * jointEntropySubset μ Xs S
      ≤ ∑ i ∈ S, jointEntropySubset μ Xs (S.erase i)

end InformationTheory.Shannon
```

### 鍵となる作業

1. **`jointEntropySubset` の定義 + 基本性質** — `S = univ` で `jointEntropy` に一致 / `S = {i}` で `entropy μ (Xs i)` に一致 / `Equiv` reshape による invariance (Han Phase C の `entropy_measurableEquiv_comp` 流用)
2. **subset 版 chain rule** — `Finset.induction_on` で `S` を空集合から 1 元ずつ追加。Han Phase A の `entropy_pair_eq_entropy_add_condEntropy` を各段で呼ぶ。**最大の plumbing リスクは `S.filter (· < i)` 上の Pi 値と「`S` を 1 元拡張したときの prefix」の整合性**。Han Phase B `jointEntropy_chain_rule` の `Fin (n+1) → α` に対する induction は完了済みなので、それの subset generalization
3. **subset 版 conditioning monotonicity** — `T₂ = T₁ ∪ (T₂ \ T₁)` の 2 分解 + Han Phase A `condEntropy_le_condEntropy_of_pair` の subset 版 induction。要素を 1 つずつ T₁ に追加する induction が自然
4. **`han_inequality_subset` (Han の subset wrapper)** — `S` の `Finset.orderEmbOfFin S rfl : Fin S.card ↪o Fin n` で埋め込み → `Xs' k ω := Xs (orderEmbOfFin S rfl k) ω` を作って既存 `han_inequality` を `Xs'` に適用 → 両辺を subset 版に reshape (LHS = `(Fin S.card → α) ≃ᵐ (↑S → α)`、RHS = index `Finset.sum_bij`)。`Common2026/Shannon/Han.lean` の `entropy_measurableEquiv_comp` (line 52-77) と `piExceptMEquiv` 流儀をそのまま流用。**Phase A の山場 plumbing、見積もり 50〜70 行** (LHS reshape 20〜30 + RHS reshape 30〜40)。詳細: `docs/han/han-phase-d-mathlib-inventory.md` 軸 (d)

### Done 条件

- 上記 4 項目が `lake env lean Common2026/Shannon/HanD.lean` で silent
- `Common2026.lean` に `import Common2026.Shannon.HanD` 追記
- skeleton-driven で `jointEntropySubset` 定義 → `chain_rule` → `condEntropy_subset_anti` → `han_inequality_subset` の順に sorry を割る

### Status (2026-05-10)

**Phase A 完了** (HEAD `bbfa250`)。`Common2026/Shannon/HanD.lean` で 4 主定理すべて 0 sorry:

- `jointEntropySubset_univ` ─ `piCongrLeft` で `(↥univ → α) ≃ᵐ (Fin n → α)` を構成し
  `entropy_measurableEquiv_comp` で reshape (~ 25 行)
- `condEntropy_subset_anti` ─ `T₂ ↔ T₁ ⊔ (T₂ \ T₁)` の subset split MeasurableEquiv
  (`subsetSplitMEquiv` 補助) + `condEntropy_le_condEntropy_of_pair` を 1 度呼ぶ。induction 不要 (~ 35 行)
- `jointEntropySubset_chain_rule` ─ `Fin S.card ≃ ↥S` (orderIsoOfFin) で
  `jointEntropy_chain_rule μ Xs'` (Xs' k = Xs (orderEmb k)) を呼び、両辺を reshape。
  per-summand bridge (`Fin k.val ≃ ↥(S.filter (· < φ k))`) は別 helper に切り出し。
  RHS sum reindex は `Finset.sum_nbij` (~ 100 行 + helper)
- `han_inequality_subset` ─ 同じく `orderEmbOfFin` で `han_inequality` を呼び、両辺 reshape。
  per-summand bridge (`{j : Fin S.card // j ≠ k} ≃ ↥(S.erase (φ k))`) は
  `jointEntropyExcept_orderEmb_eq` helper に切り出し (~ 90 行 + helper)

副次成果: `condEntropy_measurableEquiv_comp` を `Han.lean` に追加 (conditioner 側 reshape の汎用補題、`H(Y, X) = H(Y) + H(X|Y)` 経由)。

ハマりどころ: (a) `Equiv` builder の field 内で `Fin k.val` への型推論がうまく行かず `refine` builder + `?_` placeholder への切り替えで解決。(b) `rw [← h]` で `vh : ↥(S.erase (φ k))` のような `k`-依存型がある場合に motive が壊れる → `congrArg` で迂回。

### 工数感

1.5〜2 週間予算 → **実績 1 セッション (約 4 時間) で Phase A 完**。山場の (4) `orderEmbOfFin` reshape と (2) chain rule subset 化が「Han Phase B の `entropy_measurableEquiv_comp` を index Equiv に乗せ替えるだけ」で済んだのが大きい。**Phase B / C の見積もりは大幅短縮可能**。

---

## Phase B (D): D-1 subset average chain

### スコープ

```lean
namespace InformationTheory.Shannon

/-- $H_k = (k \binom{n}{k})^{-1} \sum_{|S|=k} H(X_S)$。 -/
noncomputable def averageSubsetEntropy
    (μ : Measure Ω) (Xs : Fin n → Ω → α) (k : ℕ) : ℝ :=
  (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      jointEntropySubset μ Xs S) / (k * n.choose k)

/-- Han 1978 単発: $k \cdot S_{k+1} \le (n-k) \cdot S_k$ ($S_k = \sum_{|T|=k} H(X_T)$)。 -/
theorem subset_sum_step
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {k : ℕ} (hk : k + 1 ≤ n) :
    (k : ℝ) * (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (k+1),
                  jointEntropySubset μ Xs S)
      ≤ ((n - k) : ℝ) * (∑ T ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
                            jointEntropySubset μ Xs T)

/-- Han 1978 主定理: $H_k$ は $k$ について非増加。 -/
theorem subset_average_anti
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {k : ℕ} (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    averageSubsetEntropy μ Xs (k+1) ≤ averageSubsetEntropy μ Xs k

/-- 連鎖系: $H_{k_1} \ge H_{k_2}$ for $1 \le k_1 \le k_2 \le n$。 -/
theorem subset_average_chain
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    {k₁ k₂ : ℕ} (h1 : 1 ≤ k₁) (h12 : k₁ ≤ k₂) (h2 : k₂ ≤ n) :
    averageSubsetEntropy μ Xs k₂ ≤ averageSubsetEntropy μ Xs k₁

end InformationTheory.Shannon
```

### 証明骨格

```
∀ S, |S| = k+1 ⟹  k · H(X_S) ≤ ∑ i∈S, H(X_{S\{i}})            -- han_inequality_subset
∑_{|S|=k+1}    ⟹  k · S_{k+1} ≤ ∑_{|S|=k+1} ∑_{i∈S} H(X_{S\{i}})
                              = (n-k) · S_k                    -- 二重和 reindex
                                                                  (各 |T|=k は (n-k) 個の S=T∪{i} に出現)

H_k - H_{k+1} = S_k / (k · C(n,k)) - S_{k+1} / ((k+1) · C(n,k+1))
              = [(k+1) C(n,k+1) S_k - k C(n,k) S_{k+1}] / D
              = [(n-k) C(n,k) S_k - k C(n,k) S_{k+1}] / D       -- C(n,k+1)(k+1) = C(n,k)(n-k)
              = C(n,k) [(n-k) S_k - k S_{k+1}] / D ≥ 0
```

### 鍵となる作業

1. **`han_inequality_subset` を `|S| = k+1` で適用** — Phase A の wrapper をそのまま呼ぶ
2. **二重和 reindex** — `∑_{|S|=k+1} ∑_{i∈S} f(S \ {i}) = (n-k) ∑_{|T|=k} f(T)` を 5 段 calc で証明。**Phase B の山場 combinatorics、ただし Mathlib 内に写経テンプレあり**
   - **テンプレ**: `Mathlib/Algebra/Polynomial/Derivative.lean:710-728` (`iterate_derivative_prod_X_sub_C` 内)。構造: `sum_finset_product'` で外側 ` × i` を product 化 → `sum_bij'` で `(S, i) ↦ (S.erase i, i)` (with `i ∈ S`) ↔ `(T, i) ↦ (insert i T, i)` (with `i ∉ T`) の双方向写像 → `sum_finset_product'` 逆方向で再び二重和 → `mul_sum` + `sum_const` + `card_sdiff` で `(n-k)` 倍に潰す
   - 既存 Mathlib 側で `f` が `T` 全体に依存する形での 1 行補題は **無い** ことが Phase 0 で確定 (`Finset.sum_powersetCard` は cardinality 依存形のみ、`prod_powerset` は size 別分解)。**手動 `sum_bij'` + `sum_finset_product'` が必須**
   - 詳細: `docs/han/han-phase-d-mathlib-inventory.md` 軸 (b)
3. **`subset_sum_step` から `subset_average_anti` への代数** — `(k+1) · binomial(n,k+1) = (n-k) · binomial(n,k)` を `Nat.choose_succ_right_eq` 等で持ち、両辺の正規化定数を消す。`field_simp` + `ring`
4. **`subset_average_chain` (連鎖)** — `subset_average_anti` を `Nat.le_induction` で k₁ → k₂ まで反復

### Done 条件

- `subset_sum_step` / `subset_average_anti` / `subset_average_chain` が silent
- Phase A の `han_inequality_subset` を活性化 (主定理から呼ばれる)
- `(k+1) · binomial(n,k+1) = (n-k) · binomial(n,k)` 補題は Mathlib `Nat.choose_succ_right_eq` を直接使えるか確認 (使えなければ別補題として置く)

### 工数感

**1 週間以内 (Phase 0 で下方修正)**。Phase 0 (D) で `Polynomial.Derivative.lean:710-728` の写経テンプレを発見、二重和 reindex は 20〜25 行 (calc 5 段) に圧縮見込み。残りリスクは `grind` の挙動が Phase D 環境で同じく決まるか (Polynomial.Derivative では polynomial ring が context で `grind` が強い)。`grind` が決まらなければ手動展開 30〜40 行。

---

## Phase C (D): D-2 Shearer 🌙

### スコープ

```lean
namespace InformationTheory.Shannon

/-- Shearer の不等式 (整数 covering 形)。
`S : ι → Finset (Fin n)` が各 `i : Fin n` を少なくとも `k` 回被覆するとき:
$k \cdot H(X_{[n]}) \le \sum_j H(X_{S_j})$。 -/
theorem shearer_inequality
    {ι : Type*} [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : Fin n → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (S : ι → Finset (Fin n))
    {k : ℕ}
    (hk : ∀ i : Fin n,
      k ≤ (Finset.univ.filter (fun j : ι => i ∈ S j)).card) :
    (k : ℝ) * jointEntropy μ Xs
      ≤ ∑ j : ι, jointEntropySubset μ Xs (S j)

end InformationTheory.Shannon
```

### 証明骨格 (純 plumbing — Han 本体は呼ばない)

```
∀ j,  H(X_{S_j}) = ∑_{i ∈ S_j} H(X_i | X_{S_j ∩ <i})        -- subset 版 chain rule
                ≥ ∑_{i ∈ S_j} H(X_i | X_{<i})              -- conditioning monotonicity
                                                              (S_j ∩ <i ⊆ <i)

∑_{j ∈ ι} H(X_{S_j}) ≥ ∑_{j ∈ ι} ∑_{i ∈ S_j} H(X_i | X_{<i})
                    = ∑_{i ∈ Fin n} (cover_count i) · H(X_i | X_{<i})    -- 二重和入れ替え
                    ≥ k · ∑_{i ∈ Fin n} H(X_i | X_{<i})                  -- cover_count ≥ k かつ
                                                                            H(X_i | X_{<i}) ≥ 0
                    = k · H(X_{[n]})                                     -- Phase B (Han) chain rule
```

### 鍵となる作業

1. **`H(X_{S_j}) ≥ ∑_{i ∈ S_j} H(X_i | X_{<i})`** — Phase A の `jointEntropySubset_chain_rule` + `condEntropy_subset_anti` (`S_j ∩ <i ⊆ <i`) を 2 段適用。**condMI 経由ではなく chain rule + monotonicity を直接使う**
2. **二重和入れ替え** — `∑_{j ∈ ι} ∑_{i ∈ S_j} f(i) = ∑_{i ∈ Fin n} (cover_count i) · f(i)` を `Finset.sum_comm` + `Finset.sum_filter` + `Finset.smul_sum` で展開。**plumbing は Phase B の二重和より易しい (片側が `ι` で indexed `Finset` なので `mem_filter` が直接効く)**
3. **`cover_count i ≥ k` から `(cover_count i) · f(i) ≥ k · f(i)`** — `f(i) ≥ 0` (= `condEntropy_nonneg`、Han Phase A の中間補題で確立済) と `Nat.cast_le` の組み合わせ。`mul_le_mul_of_nonneg_right` 1 発
4. **最後の chain rule で $\sum_i H(X_i | X_{<i}) = H(X_{[n]})$** — Han Phase B `jointEntropy_chain_rule` をそのまま呼ぶ

### Done 条件

- `shearer_inequality` が `lake env lean Common2026/Shannon/HanD.lean` で silent
- Phase A の subset chain rule + monotonicity を活性化 (Han 本体は呼ばれない)
- $H(X_i \mid X_{<i}) \ge 0$ (= `condEntropy_nonneg`) が直接利用可能か確認 (Han Phase A の周辺で立っているはず)

### 工数感

1 週間予算。Phase A + B が片付けば組み合わせのみ。**最大リスクは (1) `S_j ∩ <i ⊆ <i` での `condEntropy_subset_anti` 適用時の Pi 値整合 plumbing**。Han Phase C の `han_single_bound` で扱った「補集合 ↔ prefix + suffix」の 1 段目が再演される形なので、proof-log 通りの reshape 手順が効くはず。

---

## 失敗判定 / 撤退ライン

- **Phase 0 で Mathlib に subset average / Shearer が既にあった**場合 → 計画破棄、proof-log だけ取って次テーマ (Slepian-Wolf converse 等) に乗り換え
- **Phase A の `(i : S) → α` instance / subset chain rule で 2 週間以上溶ける**場合 → subset 一般化を諦め、`{j // j ≠ i}` (Han 既存) と `{j // j < i}` (Han 既存) の 2 形だけで使える限定版 D-1 ($H_{n-1} \ge H_n$ 単発) で publish
- **Phase B の二重和 reindex で詰まる**場合 → 連鎖 ($H_k \ge H_{k+1}$ 一般 $k$) を諦め単発 $k=1$ ($H_1 \ge H_2$ = 「pairwise 平均が 1 変数平均以下」) で publish + Phase C 着手
- **Phase B 完了 / Phase C 着手前で打ち切り判断**: D-1 (Han 1978 textbook 主結果) 単独で publish 価値あり。proof-log を取って Phase C は後日とする
- **Phase C で詰まる**場合 → Shearer は別 plan に切り出し、本 plan は D-1 までで close
- どのケースも「D-2 に届かなかった」ではなく **「`Common2026/Shannon` の subset 化で詰まった具体ポイント」をデータとして残す**

---

## 当面の next step

1. ~~**Phase 0 (D)**~~ ✅ **完 (2026-05-10)**
2. ~~**Phase A skeleton + 4 sorry-fill**~~ ✅ **完 (2026-05-10、HEAD `bbfa250`)**。`Common2026/Shannon/HanD.lean` の 4 主定理すべて 0 sorry
3. ~~**Phase B (D-1 subset average chain)**~~ ✅ **完 (2026-05-10、HEAD `1088bfc`)**。`Common2026/Shannon/HanDAverage.lean` の 3 主定理 + 1 helper すべて 0 sorry
4. ~~**Phase C (D-2 Shearer)**~~ ✅ **完 (2026-05-10)**。`Common2026/Shannon/HanDShearer.lean` の `shearer_inequality` が 0 sorry。Phase D 完結 (累計 8 主定理 0 sorry)。
   - 戦略: Phase A chain rule + monotonicity を全部 `S = univ` 形に揃え、Phase B chain rule (`Fin i.val` 形) は呼ばずに reshape 1 段で済ませた。
   - `condEntropy_nonneg` は Mathlib にも本 project にも無かったので unfold して手書き (`integral_nonneg` + `Real.negMulLog_nonneg`)。再利用するなら別ファイルに切り出す検討余地あり。
