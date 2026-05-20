# Sanov LDP equality 形 (B-1'') ムーンショット計画 🌙

> **Status (2026-05-12)**: deferred カード起草、未着手。B-1' upper bound (`Common2026/Shannon/SanovLDP.lean` 550 行) が touch せず並立する想定。本 plan は **open set 上の Sanov LDP equality 形** (Cover-Thomas Theorem 11.4.1 完全形) を 0 sorry で publish する設計図。
>
> **実態整合 (2026-05-20): DONE-UNCOND** — Status 行の「未着手」は完全に stale。**全 Phase A〜F 実装済**: `Common2026/Shannon/KLDivContinuous.lean` (Phase A、0 sorry) + `Common2026/Shannon/SanovLDPEquality.lean` (1243+ 行、Phase B〜E、0 sorry)。主定理 `sanov_ldp_equality` は `SanovLDPEquality.lean:1243` に strict `Tendsto (… → 𝓝 (-D))` で discharge、std binders (`h_in_E`/`h_minimizer` は honest な achievable-seq / minimizer 仮定、pass-through なし)。下界補題 `sanov_ldp_lower_bound_pointwise` + 上界 `sanov_ldp_upper_bound` の sandwich で着地。両 file 0 `:=True`。

## 進捗

- [x] Phase 0 — Mathlib API インベントリ (`Continuous Real.log` / `Real.continuous_negMulLog` / `Nat.floor` / `tendsto_of_le_liminf_of_limsup_le`) ✅
- [x] Phase A — `klDivIndex` の連続性 (`Common2026/Shannon/KLDivContinuous.lean` 独立 file) ✅
- [x] Phase B — achievable type sequence (`roundedTypeIndex P n` と `klDivIndex_tendsto`) ✅
- [x] Phase C — `Q^n(T_c)` lower bound (多項係数 Stirling-free) ✅
- [x] Phase D — `liminf` 形 lower bound on open `E°` ✅
- [x] Phase E — Tendsto sandwich (B-1' upper + Phase D lower) → equality 形 ✅ (`sanov_ldp_equality` @ SanovLDPEquality.lean:1243)
- [x] Phase F — verify + doc 更新 ✅

## ゴール / Approach

### 採用 scope: 候補 [E1] 簡略形 (open set + single rounding sequence)

**主結果 statement** (Cover-Thomas Theorem 11.4.1 LDP equality, open set 形):

```lean
theorem sanov_ldp_equality
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (E : ∀ n, Finset (TypeCountIndex α n))
    (P° : α → ℝ)
    (hP°_prob : (∑ a, P° a) = 1 ∧ ∀ a, 0 ≤ P° a)
    (hP°_full : ∀ a, 0 < P° a)
    (h_achievable : ∀ n, 0 < n →
      roundedTypeIndex P° n ∈ E n)
    (D : ℝ) (hD_lower : D = klDivSumForm_ofVec P° Q)
    (hD_upper : ∀ n, ∀ c ∈ E n,
      klDivSumForm_ofVec P° Q ≤ klDivIndex (fun a => (c a : ℕ)) n Q) :
    Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * Real.log
        (((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal))
      atTop (𝓝 (-D))
```

すなわち、open set `E° ⊆ Δ_{|α|-1}` (probability simplex) を `E n := {c | c/n ∈ E°}` の型 index 形で書き、`P° ∈ E°` 上の minimizer に対して

```
(1/n) log Q^n(⋃ c ∈ E n, T_c)  →  -klDivSumForm P° Q  =  -inf_{P ∈ E°} klDivSumForm P Q
```

を取る。

### スコープ確定の判断 (起草時 2026-05-12)

候補 [E1] **完全 Sanov LDP equality on open set E**, 候補 [E2] **closed lim sup + open lim inf**, 候補 [E3] **single-point Tendsto** の 3 案で検討。
- [E3] は achievable rounding seq だけで終わり Mathlib `Real.continuous_negMulLog` + `klDivIndex` 連続性で ~300 行に収まるが、textbook の LDP equality form (open set 評価) には届かない。
- [E2] は B-1' (closed upper) + Phase D (open lower) を **別 statement** で publish。equality form ではない。
- [E1] は `E° ⊆ Δ` の open subset を `E n ⊆ TypeCountIndex α n` に変換する topology 引数が必要で、`P° = inf_{P ∈ E°} klDivSumForm` の minimizer 取得に `IsCompact` / `ContinuousOn.exists_isMinOn` が要る。

**採用**: [E1] **簡略形**。topology の重さを避けるため `E° ⊆ Δ` を陽に持たず、ユーザが `P° ∈ Δ`, `D = klDivSumForm P° Q`, `E n` が `roundedTypeIndex P° n` を eventually 含む + `∀ c ∈ E n, D ≤ klDivIndex c n Q` という 3 仮定で渡す形 (= Cover-Thomas 11.4.1 の open set 形を本 statement 1 つで覆う、ユーザが外で `E° := open ∩ {D ≥ ε}` で取る用)。**topology 上の inf / interior 取得は B-1''' に切り出し**。

### file 分割案

- `Common2026/Shannon/KLDivContinuous.lean` (新規, Phase A、~100-150 行) — `Continuous (klDivSumForm_ofVec · Q)` を `Real.negMulLog` 連続性で。Mathlib 上流 PR 候補。
- `Common2026/Shannon/SanovLDPEquality.lean` (新規, Phase B-E、~400-550 行) — achievable seq + lower bound + sandwich。`SanovLDP.lean` (B-1') / `KLDivContinuous.lean` (Phase A) を import で再利用。
- 既存 `Common2026/Shannon/SanovLDP.lean` (B-1', 550 行) は touch せず。

合計新規行数 ~500-700 行。

### 全体戦略 (4 部構造)

```
Phase 0 : Mathlib API インベントリ
          ──────────────────────────────────────────
Phase A : klDivIndex の連続性 (独立 file, Mathlib 上流候補)        ~100-150 行
          ──────────────────────────────────────────
Phase B : achievable type sequence (rounding + tendsto)            ~150-200 行
          ──────────────────────────────────────────
Phase C : Q^n(T_c) lower bound (多項係数 Stirling-free)             ~150-200 行
          ──────────────────────────────────────────
Phase D : liminf 形 lower bound on (∪_c T_c) for c ∈ E n           ~100-150 行
          ──────────────────────────────────────────
Phase E : tendsto sandwich (B-1' upper + Phase D lower)             ~50-80 行
          ──────────────────────────────────────────
Phase F : verify (lake env lean) + doc 更新                         0.5 日
```

## Phase 0 - Mathlib API インベントリ

ユーザ確定スコープに従い「**`Continuous InformationTheory.klDiv` が Mathlib 未着手の場合は本プロジェクト内で連続性補題を独立に証明**」を採用。loogle 確認 (2026-05-12):

```
$ loogle "Continuous, InformationTheory.klDiv"
Found 0 declarations mentioning Continuous and InformationTheory.klDiv.
```

⇒ **Mathlib に `Continuous klDiv` は無い** (B-1' 起草時の判断を再確認)。**自前** で `klDivSumForm` (or `klDivIndex` 経由) の連続性を `Real.negMulLog` continuity から組む。

調査済み主要 API (signature verbatim、`file:line` ベース):

| Lemma / def | location | 用途 |
|---|---|---|
| `Real.continuous_negMulLog : Continuous Real.negMulLog` | `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` | `negMulLog x = -x · log x` の連続性 (`x ≥ 0` で `x · log x` 連続、`x = 0` も extension 含む) |
| `Real.negMulLog_def : negMulLog x = -(x * log x)` | `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` | identity for unfolding |
| `Real.negMulLog_zero : negMulLog 0 = 0` | 同上 | boundary 0 handling |
| `Real.continuousAt_log : x ≠ 0 → ContinuousAt log x` | `Mathlib.Analysis.SpecialFunctions.Log.Basic` | `Q a > 0` 仮定で `log Q a` 連続 (`a` 固定) |
| `Real.continuousOn_log : ContinuousOn log {x | x ≠ 0}` | 同上 | parameterized form |
| `Continuous.log : Continuous f → (∀ x, f x ≠ 0) → Continuous (fun x => log (f x))` | 同上 | composition |
| `continuous_finset_sum : (∀ i ∈ s, Continuous (f i)) → Continuous (fun x => ∑ i ∈ s, f i x)` | `Mathlib.Topology.Algebra.Monoid` | finite sum 連続 |
| `Continuous.const_mul : Continuous f → Continuous (fun x => c * f x)` | `Mathlib.Topology.Algebra.Monoid.Defs` | `P a` × `log Q a` 部分 |
| `Continuous.mul : Continuous f → Continuous g → Continuous (fun x => f x * g x)` | 同上 | general mul |
| `Filter.Tendsto.const_mul : Tendsto f l (𝓝 b) → Tendsto (c * f ·) l (𝓝 (c * b))` | 同上 | 既存 SanovLDP `log_succ_div_tendsto_zero` で使用済 |
| `Nat.floor_le : 0 ≤ x → ↑⌊x⌋₊ ≤ x` | `Mathlib.Algebra.Order.Floor.Semiring` | `⌊n · P° a⌋ ≤ n · P° a` |
| `Nat.lt_floor_add_one : x < ↑⌊x⌋₊ + 1` | `Mathlib.Algebra.Order.Floor.Semiring` | `n · P° a < ⌊⌋ + 1` |
| `Nat.sub_one_lt_floor : x - 1 < ↑⌊x⌋₊` | 同上 (Nat.semiring) | corollary |
| `Nat.le_floor_iff : 0 ≤ x → (n ≤ ⌊x⌋₊ ↔ ↑n ≤ x)` | 同上 | |
| `tendsto_of_le_liminf_of_limsup_le` | `Mathlib.Topology.Order.LiminfLimsup` | sandwich: `b ≤ liminf` + `limsup ≤ b` ⇒ `Tendsto → b` |
| `Filter.le_liminf_of_le` / `Filter.limsup_le_of_le` | `Mathlib.Order.LiminfLimsup` | liminf / limsup bounds 構築 |
| `Filter.Tendsto.liminf_eq` / `Filter.Tendsto.limsup_eq` | 同上 | known tendsto から liminf/limsup |

調査済み既存プロジェクト API (`SanovLDP.lean`):

```lean
abbrev TypeCountIndex (α : Type*) [Fintype α] (n : ℕ) : Type _ := α → Fin (n+1)
def typeClassByCount {n : ℕ} (c : α → ℕ) : Set (Fin n → α)
noncomputable def klDivIndex (c : α → ℕ) (n : ℕ) (Q : Measure α) : ℝ
theorem typeClassByCount_Qn_le … : Q^n(T_c) ≤ exp(-n · klDivIndex c n Q)
theorem typeClassByCount_union_Qn_le_inf …
theorem sanov_ldp_upper_bound …
lemma typeCountIndex_card : Fintype.card (TypeCountIndex α n) = (n+1) ^ Fintype.card α
lemma log_succ_div_tendsto_zero : Tendsto (fun n => log (n+1) / n) atTop (𝓝 0)
```

調査済み既存プロジェクト API (`Sanov.lean`):

```lean
noncomputable def klDivSumForm (P Q : Measure α) : ℝ :=
  ∑ a : α, P.real {a} * (Real.log (P.real {a}) - Real.log (Q.real {a}))
```

**TBD**: `klDivSumForm` の入力を `Measure α` から `α → ℝ` に書き換えた変種 (`klDivSumForm_ofVec : (α → ℝ) → (α → ℝ) → ℝ`) を Phase A で定義する。これは `Measure α` 構造体の `topology` を介さずに `α → ℝ` の point-wise topology だけで連続性を取るため。既存 `klDivSumForm` (Measure 入力) との連絡は `klDivSumForm_eq_ofVec_pmf` (1-liner) を `Sanov.lean` を touch せずに本 file 内で publish。

## Phase A - `klDivIndex` の連続性 (新規 file `Common2026/Shannon/KLDivContinuous.lean`)

### 目標 statement

```lean
namespace InformationTheory.Shannon

/-- KL divergence in finite-alphabet **vector** form:
`klDivSumForm_ofVec p q := ∑ a, p a · (log (p a) - log (q a))`.

`Continuous` (on `p : α → ℝ` for fixed positive `q`) を取りやすい
書き方として、`Measure α` 入力から脱却。 -/
noncomputable def klDivSumForm_ofVec
    (p : α → ℝ) (q : α → ℝ) : ℝ :=
  ∑ a : α, p a * (Real.log (p a) - Real.log (q a))
```

主補題:

```lean
/-- **KL の `p` 上での連続性**: `q a > 0` for all a ⟹ `p ↦ klDivSumForm_ofVec p q` is
continuous on `α → ℝ`.

境界処理: `negMulLog : ℝ → ℝ` (≡ `λ x => -x · log x`, `negMulLog 0 = 0`) は ℝ 全域で連続
(`Real.continuous_negMulLog`)。`p a · log p a = -negMulLog (p a)`。なので
`p ↦ p a · log p a` は連続。`q a` 固定 ⟹ `log q a` は定数なので `p ↦ -p a · log q a` も連続。
合計 `p a · (log p a - log q a)` は連続、`Finset.sum` で連続。 -/
theorem klDivSumForm_ofVec_continuous
    (q : α → ℝ) (hq_pos : ∀ a, 0 < q a) :
    Continuous (fun p : α → ℝ => klDivSumForm_ofVec p q) := by
  sorry
```

### 証明 sketch

`α → ℝ` を `(α → ℝ)` topology (= `Pi` topology) で受ける。各成分 `p a` の `eval a : (α → ℝ) → ℝ` が連続 (`continuous_apply a`)。`p a · log p a = -(negMulLog (p a))` を `Real.negMulLog_def` で書き換え、`Real.continuous_negMulLog.comp (continuous_apply a)` で `p ↦ negMulLog (p a)` が連続。残りは `Continuous.neg`, `Continuous.mul_const`, `Continuous.sub`, `continuous_finset_sum` の plumbing。

**boundary 処理**:
- `p a = 0`: `negMulLog 0 = 0` (`Real.negMulLog_zero`), `0 · log q a = 0` ⇒ 寄与 0、連続性 OK。
- `q a = 0`: NG (`log 0 = 0` ad-hoc convention だが KL 自体が `+∞`)。**`hq_pos`** で除外。

**`klDivIndex c n Q` との連絡**:

```lean
/-- `klDivIndex` (B-1' で導入) と `klDivSumForm_ofVec` の橋渡し:
`klDivIndex c n Q = klDivSumForm_ofVec (fun a => c a / n) (fun a => Q.real {a})`. -/
lemma klDivIndex_eq_ofVec (c : α → ℕ) (n : ℕ) (Q : Measure α) :
    klDivIndex c n Q
      = klDivSumForm_ofVec (fun a => (c a : ℝ) / n) (fun a => Q.real {a}) := by
  rfl
```

(`def` の unfold で `rfl`、両定義の `∑ a, ...` が項単位で一致するため.)

行数見積: `KLDivContinuous.lean` ~100-150 行 (内 `klDivSumForm_ofVec_continuous` 本体 ~50 行 + helper / lemma 群 ~50-100 行).

**TBD**: `negMulLog_def : negMulLog x = -(x * log x)` で `p a * log p a = -negMulLog (p a)` の rewrite が `ring_nf` で取れるかをファイル side で確認、不可なら手動 `field_simp` + `neg_neg`)。

## Phase B - achievable type sequence (rounding)

### 目標 statement

```lean
/-- **Rounded type index**: 任意の確率ベクトル `P° : α → ℝ` (`∑ = 1`, `P° a ≥ 0`)
と `n : ℕ` (`0 < n`) に対し、`c : TypeCountIndex α n` を構成し、
`∑ a, c a = n` かつ各 `a` で `‖(c a : ℝ) / n - P° a‖ ≤ |α| / n` を満たす。

構成: 各 `a` に `c₀ a := ⌊n · P° a⌋` を取り、
余り `Δ := n - ∑ c₀ a` を **alphabet 順** の最初の `Δ` 個の letter に +1 ずつ分配。 -/
noncomputable def roundedTypeIndex (P° : α → ℝ) (n : ℕ) :
    TypeCountIndex α n :=
  sorry
```

主補題:

```lean
/-- **Rounding sum constraint**: `∑ a, roundedTypeIndex P° n a = n`. -/
lemma roundedTypeIndex_sum
    (P° : α → ℝ) (hP° : (∑ a, P° a) = 1) (hP°_nn : ∀ a, 0 ≤ P° a)
    (n : ℕ) (hn : 0 < n) :
    (∑ a, (roundedTypeIndex P° n a : ℕ)) = n := by sorry

/-- **Rounding distance bound**: `|c a / n - P° a| ≤ 1 / n`. -/
lemma roundedTypeIndex_dist_le
    (P° : α → ℝ) (hP° : (∑ a, P° a) = 1) (hP°_nn : ∀ a, 0 ≤ P° a)
    (n : ℕ) (hn : 0 < n) (a : α) :
    |((roundedTypeIndex P° n a : ℕ) : ℝ) / n - P° a| ≤ 1 / n := by sorry

/-- **Tendsto rounded type fraction**: `(roundedTypeIndex P° n a : ℝ) / n → P° a`. -/
lemma roundedTypeIndex_tendsto
    (P° : α → ℝ) (hP° : (∑ a, P° a) = 1) (hP°_nn : ∀ a, 0 ≤ P° a)
    (a : α) :
    Tendsto (fun n : ℕ => ((roundedTypeIndex P° n a : ℕ) : ℝ) / n) atTop (𝓝 (P° a)) :=
  by sorry

/-- **Tendsto rounded type vector** (`α → ℝ` 上で). -/
lemma roundedTypeIndex_tendsto_vec
    (P° : α → ℝ) (hP° : (∑ a, P° a) = 1) (hP°_nn : ∀ a, 0 ≤ P° a) :
    Tendsto (fun n : ℕ => (fun a => ((roundedTypeIndex P° n a : ℕ) : ℝ) / n))
      atTop (𝓝 P°) := by sorry

/-- **KL convergence via continuity** (Phase A の応用). -/
theorem klDivIndex_rounded_tendsto
    (Q : Measure α) (hQpos : ∀ a, 0 < Q.real {a})
    (P° : α → ℝ) (hP° : (∑ a, P° a) = 1) (hP°_nn : ∀ a, 0 ≤ P° a) :
    Tendsto (fun n : ℕ =>
        klDivIndex (fun a => (roundedTypeIndex P° n a : ℕ)) n Q)
      atTop (𝓝 (klDivSumForm_ofVec P° (fun a => Q.real {a}))) := by sorry
```

### 証明 sketch (`roundedTypeIndex` 構成)

1. 各 `a` で `c₀ a := ⌊(n : ℝ) · P° a⌋` (`Nat.floor` on `ℝ`、`n · P° a ≥ 0` で取れる)。
2. `Nat.floor_le` で `c₀ a ≤ n · P° a`, `Nat.lt_floor_add_one` で `n · P° a < c₀ a + 1`。
3. `∑ a, c₀ a ≤ ∑ a, n · P° a = n`、かつ `∑ a, c₀ a > n - |α|`。⇒ `Δ := n - ∑ c₀ a ∈ {0, 1, ..., |α|}`。
4. `Finset.univ.toList : List α` の先頭 `Δ` 要素を集合化 (`addList`)。each `a ∈ addList` に `+1`。
5. **TBD**: `c₀ a < n` の保証 (`c₀ a = n` で +1 すると `Fin (n+1)` 範囲外)。`Δ ≤ n - c₀ a` の場合分けで回避、~30 行。

### 距離 bound

各 `a` で `|c a - n · P° a| ≤ 1` ⇒ `|c a / n - P° a| ≤ 1/n`。`Tendsto` は `1/n → 0` で sandwich。

行数見積: ~150-200 行。

**TBD**: `Finset.univ.toList` の orderly な使用が `DecidableEq α` だけで OK か。代替案: `Finset.exists_subset_card_le` で `Δ` 個の subset を任意取得。

## Phase C - `Q^n(T_c)` lower bound (多項係数 Stirling-free)

### 判断: 多項係数 lower bound は **必須**

当初 single-point lower bound `Q^n(T_c) ≥ Q^n({x})` で十分かに見えたが、`Q^n({x}) = (∏ (c a / n)^(c a)) · exp(-n · klDivIndex)` に分解できる (既存 `typeClassByCount_prod_eq`)。`∏ (c/n)^c = exp(-n · H(c/n))` 形なので、目標 `-klDivIndex` に対して `H(c/n)` の余分項が出る。**多項係数 lower bound** `|T_c| ≥ (n+1)^{-|α|} · exp(n · H(c/n))` で相殺するのが正攻法。

### 目標 statement

```lean
/-- **Stirling-free multinomial lower bound** (Cover-Thomas 11.1.3):
`(c a) ! ≤ ?` 系の elementary inequality で
`|T_c| ≥ (n+1)^{-|α|} · n^n / ∏ (c a)^(c a)`. -/
theorem typeClassByCount_card_ge
    {n : ℕ} (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹ *
      ((n : ℝ) ^ n / ∏ a : α, ((c a : ℝ) ^ (c a)))
        ≤ (typeClassByCount (α := α) (n := n) c).toFinset.card := by sorry

/-- **Lower bound on `Q^n(T_c)` (key for Sanov lower)**:
`Q^n(T_c) ≥ (n+1)^{-|α|} · exp(-n · klDivIndex c n Q)`. -/
theorem typeClassByCount_Qn_ge
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    {n : ℕ} (hn : 0 < n) (c : α → ℕ) (hc_sum : (∑ a, c a) = n) :
    (((n : ℝ) + 1) ^ (Fintype.card α : ℕ))⁻¹ * Real.exp (-((n : ℝ) * klDivIndex c n Q))
      ≤ ((Measure.pi (fun _ : Fin n => Q)) (typeClassByCount (α := α) c)).toReal :=
  by sorry
```

### 証明 sketch

1. **Multinomial coefficient identity**: `|T_c| = n! / ∏ (c a)!` (`Finset.card_image_perm` 系).
2. **Stirling-free lower bound** (`(n+1)^{-|α|} · n^n / ∏ (c a)^(c a) ≤ n! / ∏ (c a)!`):
   - Cover-Thomas 11.1.3 proof: 任意の type `c'` で `(n choose c') ≥ (n choose c)` (where `c = type of x`).
   - そのため `1 = ∑_{c'} P_c^n(T_{c'}) ≥ |T(P_c)| · P_c^n(T_{c'})` を取り、`(n+1)^|α|` types で割って lower bound.
   - 実装で Mathlib 上の `Nat.multinomial` で書き直す or 自前 inductive 補題。
3. **`Q^n({x})` factorization**: `Q^n({x}) = ∏ a, Q.real {a} ^ (c a)` for `x ∈ T_c` (既存 `typeClassByCount_prod_eq` の subexpression).
4. **集計**: `Q^n(T_c) = |T_c| · ∏ Q(a)^c(a)`. 代入で `(n+1)^{-|α|} · exp(-n · klDivIndex)` 形.

行数見積: ~150-200 行 (multinomial Stirling-free が ~80-120 行 + Q^n 部分 ~30-50 行).

**TBD**: Mathlib `Nat.multinomial` の lemma 群を確認 (`Mathlib.Data.Nat.Choose.Multinomial`). Stirling-free lower bound は **存在しない** と予想 (loogle で `Nat.multinomial` 関連 lemma を再確認)、自前構築。Cover-Thomas 11.1.3 の proof (`1 ≥ |T(P_c)| · P_c^n(T_c)`) は **`P_c` を probability measure** として扱うが、`c a = 0` letter で `P_c.real {a} = 0` ⇒ B-1' で回避した full-support 問題が再発する可能性。代替案: **Sterling-free lower を `Nat.factorial` の elementary inequality** (`n! ≤ n^n`, `(c a)! ≥ 1`) のみで書き、`(n+1)^|α|` factor を `Δ` 段の段階的補正で。

## Phase D - liminf 形 lower bound (open set 形)

### 目標 statement

```lean
/-- **Sanov LDP lower bound (single-rounding sequence)**:
任意 `P° : α → ℝ` で eventually `roundedTypeIndex P° n ∈ E n` のとき、
`liminf_n (1/n) log Q^n(⋃ c ∈ E n, T_c) ≥ -klDivSumForm_ofVec P° (Q.real ∘ singleton)`. -/
theorem sanov_ldp_lower_bound_pointwise
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (P° : α → ℝ) (hP°_prob : (∑ a, P° a) = 1)
    (hP°_full : ∀ a, 0 < P° a)
    (E : ∀ n, Finset (TypeCountIndex α n))
    (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P° n ∈ E n) :
    -klDivSumForm_ofVec P° (fun a => Q.real {a})
      ≤ Filter.liminf (fun n : ℕ => (1 / (n : ℝ)) * Real.log
          (((Measure.pi (fun _ : Fin n => Q))
            (⋃ c ∈ E n, typeClassByCount (α := α)
              (fun a => (c a : ℕ)))).toReal)) atTop := by sorry
```

### 証明 sketch

1. `T_{c_n} ⊆ ⋃ c ∈ E n, T_c` (∵ `c_n = roundedTypeIndex P° n ∈ E n`).
2. Phase C lower bound: `Q^n(T_{c_n}) ≥ (n+1)^{-|α|} · exp(-n · klDivIndex c_n n Q)`.
3. ⇒ `(1/n) log Q^n(⋃) ≥ -|α| · log(n+1)/n - klDivIndex c_n n Q`.
4. `|α| · log(n+1)/n → 0` (B-1' 既存 `log_succ_div_tendsto_zero`).
5. `klDivIndex c_n n Q → klDivSumForm_ofVec P° Q` (Phase B `klDivIndex_rounded_tendsto`).
6. ⇒ `liminf (1/n) log Q^n(⋃) ≥ -klDivSumForm_ofVec P° Q`.

行数見積: ~100-150 行。

**TBD**: `T_{c_n}.Nonempty` の確認: `roundedTypeIndex P° n` の `∑ = n` 制約から explicit `x ∈ T_{c_n}` を構成 (~20 行、`Phase B` の `roundedTypeIndex_typeClass_nonempty` lemma として publish).

## Phase E - Tendsto sandwich (equality 形)

### 目標 statement

```lean
/-- **Sanov LDP equality form** (main theorem, simplified version). -/
theorem sanov_ldp_equality
    (Q : Measure α) [IsProbabilityMeasure Q]
    (hQpos : ∀ a : α, 0 < Q.real {a})
    (P° : α → ℝ) (hP°_prob : (∑ a, P° a) = 1)
    (hP°_full : ∀ a, 0 < P° a)
    (E : ∀ n, Finset (TypeCountIndex α n))
    (h_in_E : ∀ᶠ n : ℕ in atTop, roundedTypeIndex P° n ∈ E n)
    (h_minimizer : ∀ n, ∀ c ∈ E n,
      klDivSumForm_ofVec P° (fun a => Q.real {a})
        ≤ klDivIndex (fun a => (c a : ℕ)) n Q) :
    Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * Real.log
        (((Measure.pi (fun _ : Fin n => Q))
          (⋃ c ∈ E n, typeClassByCount (α := α) (fun a => (c a : ℕ)))).toReal))
      atTop (𝓝 (-(klDivSumForm_ofVec P° (fun a => Q.real {a})))) := by sorry
```

### 証明 sketch

1. B-1' `sanov_ldp_upper_bound` を呼び `limsup ≤ -D + ε` (任意 ε) ⇒ `limsup ≤ -D`.
2. Phase D `sanov_ldp_lower_bound_pointwise` で `liminf ≥ -D`.
3. `tendsto_of_le_liminf_of_limsup_le` で `Tendsto → -D`.

行数見積: ~50-80 行。

**TBD**: `h_meas_pos` (eventually positive measure of the union) は `T_{c_n} ⊆ ⋃` ⇒ `Q^n(⋃) ≥ Q^n(T_{c_n}) > 0` で自動取得。assumption として外す可能性 (整理 TBD).

## Phase F - verify + doc 更新

- `lake env lean Common2026/Shannon/KLDivContinuous.lean` silent.
- `lake env lean Common2026/Shannon/SanovLDPEquality.lean` silent.
- `Common2026.lean` に 2 つの import 追記.
- `docs/moonshot-seeds.md`:
  - B-1' 行に「LDP equality 形は B-1'' で完了」追記.
  - 参照リストに `docs/shannon/sanov-ldp-equality-plan.md` 追加.
- `docs/shannon/sanov-ldp-b-plan.md` Status 行に「equality form → B-1'' で完了」リンク.
- 本 plan 末尾に **実装結果サマリ** を追加.

## 見積行数まとめ

| Phase | 内容 | 行数 |
|---|---|---|
| 0 | Mathlib API インベントリ | 10 (本 plan のみ) |
| A | `klDivSumForm_ofVec` 連続性 (`KLDivContinuous.lean` 独立 file) | 100-150 |
| B | achievable type sequence (`roundedTypeIndex` + tendsto) | 150-200 |
| C | `Q^n(T_c)` lower bound (多項係数 Stirling-free) | 150-200 |
| D | `liminf` 形 open set lower bound | 100-150 |
| E | tendsto sandwich (equality 形主定理) | 50-80 |
| F | verify + doc | 0.5 日 |
| **合計** | | **~550-780 行** |

## 判断ログ

1. **2026-05-12 起草時 (本 plan)**: ユーザ確定スコープ「Mathlib 未着手なら本プロジェクト内で連続性補題を独立に証明」を採用。loogle で Mathlib `Continuous klDiv` 不在を再確認。Phase A は `KLDivContinuous.lean` 独立 file で publish (Mathlib 上流 PR 候補).

2. **2026-05-12 起草時**: scope を **候補 [E1] 簡略形** に確定。`P°` (minimizer) を **ユーザが外から渡す形** で statement を取り、topology 引数を避ける。完全 open set 形は B-1''' に残す.

3. **2026-05-12 起草時 (Phase C 判断)**: single-point lower bound `Q^n(T_c) ≥ Q^n({x})` だけでは `H(c/n)` 余分項が消えない。**多項係数 lower bound** `|T_c| ≥ (n+1)^{-|α|} · n^n / ∏ (c a)^(c a)` が必要、Phase C は ~150-200 行.

4. **2026-05-12 起草時**: `klDivSumForm` (Sanov.lean) は `Measure α` 入力。`α → ℝ` 入力の vector 形 `klDivSumForm_ofVec` を Phase A で再定義し、既存 `klDivSumForm` との連絡を 1-liner で取る. `klDivIndex` (SanovLDP.lean) は `klDivSumForm_ofVec` の特殊形として `rfl` で連絡.

## risk / fallback

- **R1: `klDivSumForm_ofVec` 連続性の boundary 処理**
  `p a = 0` で OK (`negMulLog` continuous at 0). `q a = 0` は `hq_pos` で除外。実装で `p a * log q a` の `p a = 0` 部分は `zero_mul` で自動.

- **R2: `roundedTypeIndex` の `∑ = n` 制約**
  `Δ := n - ∑ c₀ a ∈ {0, ..., |α|}` を取り、`Δ` 個の letter に +1。`Fin (n+1)` 範囲外 (`c a = n+1`) 回避は `c₀ a < n` の letter にのみ +1、~30 行追加.

- **R3: 多項係数 Stirling-free lower bound (~150 行)**
  Mathlib 上流に無い elementary 補題。書く価値あり (Mathlib PR 候補)。**fallback**: 多項係数を avoid して **scope を [E3] single-point Tendsto に縮小** (~80 行短縮).

- **R4: `Fintype.elems` の order 依存**
  `roundedTypeIndex` の `addList` 構成。`Finset.univ.toList` は `DecidableEq α` のみで取れる。letter 同定不要 (cardinality だけ使う) で OK.

- **R5: scope 過大化時の fallback (`[E3]` への縮小)**
  Phase C 多項係数 lower bound が 150 行超に膨らむ場合、scope を **[E3] single-point Tendsto** に縮小:
  ```
  -- E n := {roundedTypeIndex P° n} のみ.
  -- (1/n) log Q^n(T_{c_n}) → -klDivSumForm_ofVec P° Q.
  ```
  ~350-400 行で完結。textbook の equality form には届かないが、点別 Tendsto は LDP の最も elementary な形として publish 価値あり.

## 採用 path 要約

- file 分割: `KLDivContinuous.lean` + `SanovLDPEquality.lean` の 2 file.
- scope: **[E1] 簡略形** (`P°` を外部から渡す、open set topology 引数なし).
- Phase C: **多項係数 Stirling-free lower bound** 採用 (Mathlib 上流 PR 候補).
- 行数合計: ~550-780 行.

最大 TBD:
1. 多項係数 Stirling-free lower bound (`|T_c| ≥ (n+1)^{-|α|} · n^n / ∏ (c a)^(c a)`) の self-contained 証明 (Mathlib 不在、~150 行)。fallback として scope [E3] への縮小.
2. `roundedTypeIndex` 構成での `Fin (n+1)` 範囲制約 (`c₀ a = n` letter に +1 加えない条件の整理).
