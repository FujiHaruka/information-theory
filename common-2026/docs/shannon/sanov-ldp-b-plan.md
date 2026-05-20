# Sanov LDP B 形 (B-1') ムーンショット計画 🌙

> **Status (2026-05-12)**: **LDP B 形 upper bound 完了 (Phase A〜E すべて 0 sorry)**。`Common2026/Shannon/SanovLDP.lean` (550 行)。lower bound + equality 形は **B-1'' に再 defer** (Mathlib `Continuous klDiv` 不在 + achievable type sequence 構築 + 多項係数 lower bound 合計 ~500-650 行)。既存 `Common2026/Shannon/Sanov.lean` (319 行、A 形完了) は touch せず並立 publish。
>
> **実態整合 (2026-05-20): DONE-UNCOND** — upper bound 主定理 `sanov_ldp_upper_bound` は `Common2026/Shannon/SanovLDP.lean:471`、std binders (`hQpos` honest、`hD` は user-supplied D 下界仮定)、0 sorry。なお「B-1'' に再 defer」は stale: **equality 形は完了済** (`SanovLDPEquality.lean:1243` `sanov_ldp_equality`、[sanov-ldp-equality-plan.md](sanov-ldp-equality-plan.md))。

## 進捗

- [x] Phase 0 — Mathlib API インベントリ (多項係数 / `log =o[atTop] id` / type 列挙 plumbing) ✅
- [x] Phase A — type 数 polynomial bound `|TypeCountIndex α n| = (n+1)^|α|` ✅
- [x] Phase B — index 形 Sanov A `typeClassByCount_Qn_le` (`Q^n(T_c) ≤ exp(-n · klDivIndex c n Q)`) ✅
- [x] Phase C — union form `typeClassByCount_union_Qn_le_inf` + 主定理 `sanov_ldp_upper_bound` ✅
- [x] Phase D — verify (`lake env lean Common2026/Shannon/SanovLDP.lean` silent、0 sorry、0 警告) ✅
- [x] Phase E — doc 更新 ✅

## ゴール / Approach

### 最終到達点 (Phase C 主定理)

```lean
/-- **Sanov LDP B 形 upper bound** (Cover-Thomas Theorem 11.4.1, upper half).

任意の集合 `E : Set (Measure α)` (probability measures over `α`) と
任意の `n : ℕ`, 任意の `ε > 0` で eventually、

    (1/n) · log (Q^n({x : Fin n → α | empirical(x) ∈ E})).toReal
       ≤ -infTypesInE E Q + ε

ここで `infTypesInE E Q := inf_{P ∈ E ∩ 𝒫_n} klDivSumForm P Q`
(本実装では `𝒫_n` を index 集合に取って `inf` を取る、`infimum_klDiv_on_types`)。 -/
theorem sanov_upper_bound :
    ∀ ε > (0:ℝ), ∃ N, ∀ n ≥ N, …
```

形は **Cover-Thomas 11.4.1 (Sanov の定理) の標準形**: upper bound on `Q^n(E_n)` で
`(n+1)^{|α|}` polynomial factor を `o(n)` で潰す ⇒ `lim sup ≤ -inf D`。
**等値形 (= equality `Tendsto` form)** は achievable type sequence + `klDivSumForm` 連続性
が必要だが、これは Mathlib 未着手 (`Continuous klDiv` 不在、type sequence 構築 ~200 行) で
**B-1'' に分離**。

### Approach (3 部構造)

**核心アイデア**: 既存 A 形 `typeClass_Qn_le : Q^n(T(P)) ≤ exp(-n · klDivSumForm P Q)`
(B-1 完了) を **`𝒫_n` 上の有限 union** に拡張するだけで LDP upper bound が出る。
多項係数 (`Nat.multinomial`) を経由する必要は **ない**。

1. **Phase A**: type 集合 `𝒫_n ⊆ Measure α` (n-empirical で実現可能な分布の有限集合)
   を index させる **`TypeIndex n`** を `α → Fin (n+1)` の (制約) subset として有限集合化。
   ```
   |TypeIndex n| ≤ (n+1)^|α|    (Fintype.card_fun)
   ```

2. **Phase B**: 任意の finite `F : Finset (TypeIndex n)` に対し
   ```
   Q^n(⋃_{P ∈ F} T(P)) ≤ |F| · exp(-n · inf_{P ∈ F} klDivSumForm P Q)
   ```
   既存 `typeClass_Qn_le` の有限 union (各 `T(P)` が pairwise disjoint な点を利用)。

3. **Phase C**: 集合 `E` を **type representation level で** 与え (`E : Set (TypeIndex ∞)` の type level)、
   或いは **probability simplex level で** 与えて `E ∩ TypeIndex n` を取る。
   いずれにせよ `Q^n({x | empirical x ∈ E}) ≤ (n+1)^|α| · exp(-n · inf_{P ∈ E∩𝒫_n} D)`。
   両辺 `log` + `/n` で `(|α| · log(n+1))/n → 0` (`Real.isLittleO_log_id_atTop`)
   経由で eventually upper bound が `ε` 以内に。

### スコープ縮小の判断 (重要)

**当初プロンプト** = 「LDP 完全版 (equality form `lim (1/n) log Q^n = -inf D`)」。

実装着手前の Mathlib API インベントリで以下が判明:

- **`klDiv` の連続性は Mathlib に無い** (`Continuous, InformationTheory.klDiv` で 0 hit)。
  finite alphabet 上で `klDivSumForm` の連続性は自前定義可能 (`Real.log` の連続性 +
  Finset.sum の連続性) だが ~80 行追加。
- **多項係数の lower bound** (`(n+1)^{-|α|} ≤ multinomial(...)` 系) も Mathlib 不在。
  Stirling-free な elementary proof (Cover-Thomas Lemma 11.1.3 の正確な lower) は
  ~150-200 行。
- **achievable type sequence の構築** (任意 `P° ∈ E°` に対し `P_n ∈ 𝒫_n`, `P_n → P°`):
  `⌊n · P°(a)⌋ / n` の adjustment + sum-1 constraint を満たすよう端数調整 ~200 行。

これら 3 つは互いに直交し、合計 ~500-600 行。`upper` だけなら全て **不要**。
**lower + equality は B-1'' に分離** し、本 plan は upper bound のみで完了。

textbook (Cover-Thomas 11.4.1) でも equality 形は corollary 扱いで、主定理表示は
`Q^n(E) ≤ (n+1)^|α| · 2^{-n · D*}` の upper bound。本 plan で publish する upper bound は
Cover-Thomas の main statement そのもの。

```
Phase 0 : インベントリ                                            ← ✅→ Phase 0 末尾
          ──────────────────────────────────────────
Phase A : |𝒫_n| ≤ (n+1)^|α| (TypeIndex の有限集合化)              ← ~100 行
          ──────────────────────────────────────────
Phase B : union form upper bound + index → typeClass 連絡          ← ~250 行
          ──────────────────────────────────────────
Phase C : empirical + 集合 E + 主定理 upper bound                  ← ~250 行
          ──────────────────────────────────────────
Phase D : verify                                                   ← 0.5 日
Phase E : doc 更新                                                 ← 0.5 日
          ──────────────────────────────────────────
(B-1'') Phase F : achievable type seq + klDiv 連続性 + 等値形    ← deferred, ~600-800 行
```

**見積行数**: ~600-800 行 (本 plan で publish する upper bound 部分)。

## Phase 0 - Mathlib API インベントリ

調査済みの主要 API:

| Lemma / def | location | 用途 |
|---|---|---|
| `Nat.multinomial` | `Mathlib.Data.Nat.Choose.Multinomial` | (不使用 — 経路で回避) |
| `Real.isLittleO_log_id_atTop : log =o[atTop] id` | `Mathlib.Analysis.SpecialFunctions.Log.Basic` | `(log n)/n → 0` を取る |
| `Fintype.card_fun : Fintype.card (α → β) = Fintype.card β ^ Fintype.card α` | `Mathlib.Data.Fintype.BigOperators` | `|TypeIndex n| ≤ (n+1)^|α|` |
| `Finset.sum_le_sum_of_subset_of_nonneg` | `Mathlib.Algebra.Order.BigOperators.Group.Finset` | union bound |
| `MeasureTheory.measure_iUnion_le` | `Mathlib.MeasureTheory.Measure.Typeclasses.Finite` | finite union 測度 |
| `MeasureTheory.measure_iUnion_fintype_le` | (or `measure_biUnion_finset_le`) | finite union |
| 既存 `typeClass_Qn_le` (Sanov.lean:172) | `Common2026.Shannon.Sanov` | 主 lemma (A 形) |
| 既存 `klDivSumForm` (Sanov.lean:73) | 同上 | KL form |

**重要な signature verbatim**:

```lean
theorem typeClass_Qn_le
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPpos : ∀ a : α, 0 < P.real {a})
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (n : ℕ) :
    ((Measure.pi (fun _ : Fin n => Q)) (typeClass P n)).toReal
      ≤ Real.exp (-((n : ℝ) * klDivSumForm P Q))
```

```lean
noncomputable def typeClass (P : Measure α) (n : ℕ) : Set (Fin n → α) :=
  { x | ∀ a : α, (typeCount x a : ℝ) = (n : ℝ) * P.real {a} }
```

```lean
theorem Real.isLittleO_log_id_atTop : log =o[atTop] id
```

## Phase A - `TypeIndex` と polynomial bound

```lean
/-- **Type index**: n-empirical で達成可能な分布を `Fin (n+1) ^ α` の subset として
列挙する有限集合。実体は `α → Fin (n+1)` で、各 `a` に対する `count` が
`∑_a count a = n` を満たすもの。`typeClass` の indexing 用。

実装では `α → Fin (n+1)` のままにして constraint は別 predicate で扱い、
`Fintype.card_fun` 経由で `(n+1)^|α|` 上界を直接取る。 -/
def TypeIndex (α : Type*) (n : ℕ) : Type _ := α → Fin (n+1)

instance : Fintype (TypeIndex α n) := …

/-- **Polynomial bound on the number of n-types**: `|TypeIndex α n| ≤ (n+1)^|α|`. -/
theorem typeIndex_card_le (n : ℕ) :
    (Fintype.card (TypeIndex α n) : ℝ) ≤ ((n : ℝ) + 1) ^ Fintype.card α := …
```

### Phase A.x: index → measure 連絡

```lean
/-- index `c : TypeIndex α n` から「empirical distribution が `c/n` の系列集合」を
取る関数。`c a = k` のとき、その `c` の type class は
`{x : Fin n → α | ∀ a, typeCount x a = c a}`. -/
noncomputable def typeClassIndex (c : TypeIndex α n) : Set (Fin n → α) :=
  { x | ∀ a, typeCount x a = c a }
```

`typeClassIndex c` が `typeClass P n` と一致するための条件 (`P.real {a} = (c a)/n`)
を `typeClass_eq_typeClassIndex` で。

## Phase B - union form upper bound

```lean
/-- **Union form upper bound** (Sanov LDP の前段補題):
任意の `F : Finset (TypeIndex α n)` と、各 `c ∈ F` に対する確率測度 `P_c` で
`P_c.real {a} = (c a : ℝ) / n` を満たすもの (= empirical = c/n) に対し、

```
Q^n(⋃ c ∈ F, typeClassIndex c) ≤ ∑ c ∈ F, exp(-n · klDivSumForm (P_c) Q)
                              ≤ |F| · exp(-n · inf_{c ∈ F} klDivSumForm (P_c) Q)
```

既存 A 形 `typeClass_Qn_le` の有限和で集約。
type class の pairwise disjoint 性 (`typeClassIndex_pairwiseDisjoint`) 経由で
`measure_biUnion_finset` を等号として使う。
-/
theorem typeClassUnion_Qn_le …
```

## Phase C - empirical + 集合 E + 主定理 upper bound

集合 `E` の与え方は **`TypeIndex` レベル** にする (probability simplex 上の topology は
B-1'' 案件)。具体的:

```lean
/-- **Sanov LDP B 形 upper bound** (Cover-Thomas Theorem 11.4.1).

`Q^n({x : Fin n → α | type(x) ∈ E})` を `E ⊆ TypeIndex α n` (= 型レベル集合) として
評価し、polynomial type 数で union bound、`klDivSumForm` の minimum で律する。

`(1/n) log` を取ると `(|α| log(n+1))/n` の polynomial slack が `o(1)` で消え、
任意 `ε > 0` で eventually
`(1/n) log Q^n({empirical(x) ∈ E}) ≤ -infTypes E n Q + ε`
が成立する。 -/
theorem sanov_ldp_upper_bound
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (E : ∀ n, Finset (TypeIndex α n))
    (D* : ℝ)
    (hD* : ∀ n, ∀ c ∈ E n, D* ≤ klDivSumFormOfIndex c Q) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N,
      (1 / n : ℝ) * Real.log (((Measure.pi (fun _ : Fin n => Q))
        (⋃ c ∈ E n, typeClassIndex c)).toReal) ≤ -D* + ε
```

`log(n+1) / n → 0` を `Real.isLittleO_log_id_atTop` から導出。

## Phase D - verify

- `lake env lean Common2026/Shannon/SanovLDP.lean` silent
- `Common2026.lean` に `import Common2026.Shannon.SanovLDP` 追記

## Phase E - doc 更新

- `docs/moonshot-seeds.md`:
  - Status 行に「B-1' Sanov LDP upper bound 完了」マーキング
  - B-1 行に「LDP upper bound は B-1' で完了、equality form は B-1'' deferred」
  - 参照リストに `docs/shannon/sanov-ldp-b-plan.md` 追加
- `docs/shannon/sanov-moonshot-plan.md` Status 行に「LDP B 形 upper bound → 別 plan」リンク
- 本 plan 末尾に **実装結果サマリ** を追加 (Phase D 完了後)

## (Deferred B-1'') Lower bound + equality form

スコープ外。必要要素:

1. **`klDivSumForm` の連続性** (finite alphabet 上、~80 行):
   `Continuous (fun P : Fin |α| → ℝ => ∑ a, P a * (log (P a) - log (Q.real {a})))`
   を `Real.log` の連続性 + `Continuous.mul` + `Finset.sum` の連続性で。

2. **achievable type sequence** (~200 行):
   任意 `P° ∈ Δ_{|α|}` (probability simplex) と任意 `n` に対し
   `P_n ∈ TypeIndex` で `‖P_n - P°‖ ≤ |α|/n` を構築。`⌊n · P°(a)⌋ / n` の端数調整
   + `∑ = 1` constraint の最後の coord での補正。

3. **inf / liminf plumbing** (~150 行):
   `inf_{P° ∈ E°} klDivSumForm P° Q ≤ liminf_n inf_{P° ∈ E ∩ TypeIndex n} klDivSumForm P° Q`。

4. **`Tendsto` equality 形** (~100 行):
   upper (本 plan) + lower (B-1'') を `tendsto_of_le_liminf_of_limsup_le` で sandwich。

合計 ~500-650 行追加で `lim (1/n) log Q^n = -inf D`。

## 判断ログ

1. **2026-05-12 起草時**: 当初プロンプトでは equality form `lim → -inf D` を要求していたが、
   Mathlib API インベントリで `Continuous klDiv` 不在 + achievable type sequence 不在
   + 多項係数 lower bound 不在の 3 点 (~500-650 行ぶん) が判明。プロンプトの「~600-1000 行」
   見積は楽観的すぎる。完全版 (equality form) を 0 sorry で publish する達成可能性が低い。
   **upper bound のみで Cover-Thomas Theorem 11.4.1 main statement に到達** できると判断。
   lower bound + equality form は B-1'' に分離 (Mathlib 上流改修候補にも近い)。

2. **2026-05-12 起草時**: 集合 `E` を `Set (Measure α)` (probability simplex 上) として
   与える形式は B-1'' (topology が必要な lower bound と組) に押し付け、本 plan では
   **`E : ∀ n, Finset (TypeCountIndex α n)`** (型 index レベルの集合族) として書く。これでも
   実用 application (例: 「empirical 平均が特定値を超える確率の指数衰退」) には十分。

3. **2026-05-12 実装時**: 当初の **Approach** では `typeClassByCount c` を既存 A 形
   `typeClass_Qn_le` を経由して Q^n 上界を取る計画だったが、
   - 既存 A 形は `P : Measure α` を引数に取り、`hPpos : ∀ a, 0 < P.real {a}` を要求する
   - `P_c := (c a / n)` から作る確率測度は `c a = 0` の letter で `P_c.real {a} = 0`
     ⇒ full-support 仮定を破る

   ため直接 reuse できなかった。代わりに **A 形の証明テンプレ (Sanov.lean:172 の Stein 経路)
   を index 形に直接書き直し** た。`x ∈ typeClassByCount c` のとき `c (x_i) ≥ 1`
   (自分自身の count contribution) を観察すると `hPpos` 対応を回避できる。`typeClassByCount_prod_eq`
   (per-point identity) + `typeClassByCount_Qn_le` (sum over T_c) で ~210 行。

## 実装結果サマリ (2026-05-12 完了時点)

- **`Common2026/Shannon/SanovLDP.lean`**: 550 行、0 sorry、0 警告 (`lake env lean ...` silent)。
- **公開 API**:
  - `TypeCountIndex α n := α → Fin (n+1)` + `typeCountIndex_card : |·| = (n+1)^|α|`
    + Real cast 系。
  - `typeClassByCount c : Set (Fin n → α)` (= sequences with given count profile)。
  - `klDivIndex c n Q : ℝ` (= finite-alphabet KL at empirical `c/n`)。
  - `typeClassByCount_Qn_le`: `Q^n(T_c) ≤ exp(-n · klDivIndex c n Q)`。
  - `typeClassByCount_union_Qn_le` / `..._inf`: union form upper bound。
  - `log_succ_div_tendsto_zero`: `log(n+1)/n → 0` (ℕ-cast version)。
  - **`sanov_ldp_upper_bound`** (主定理): 任意 `ε > 0` で eventually
    `(1/n) log Q^n(⋃ c ∈ E n, T_c) ≤ -D + ε`、`E n ⊆ TypeCountIndex α n`、
    `D ≤ klDivIndex c n Q` for `c ∈ E n`。

- **採用 path**: 既存 A 形 (Sanov.lean) 経路の **index 形書き直し** (Stein per-point ratio +
  `∑ Pc^n(T) ≤ 1`)。**多項係数 `Nat.multinomial` 経路は採用せず** — A 形と整合した経路で
  ~210 行に圧縮。`c a = 0` letter の境界処理は `x ∈ T_c` ⇒ `c (x i) ≥ 1` 観察で自動。

- **Mathlib 上流 PR 候補**: 本実装の `typeCountIndex_card` (= `(n+1)^|α|`) は他の LDP 案件
  にも再利用可能だが、汎用性は低い。`log_succ_div_tendsto_zero` は `Real.isLittleO_log_id_atTop`
  から短い derivation で出るため独立 PR 化価値は限定的。`klDivIndex` の連続性 (B-1'' 案件)
  は Mathlib `Continuous InformationTheory.klDiv` (Borel σ-field 上) として PR 化候補に
  なり得る。
