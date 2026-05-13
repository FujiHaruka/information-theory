# Strong typicality (E-7) ムーンショット計画 🌙

> **シード由来**: `docs/moonshot-seeds.md` §E.E-7 (2026-05-13 起草)
> Cover-Thomas 11.2 — `A^{*n}_ε := {x^n : ∀ a, |(1/n) N(a|x^n) - P(a)| ≤ ε}`
> の 3 主定理 (`P^n(A^*) → 1`、size sandwich、joint version)。weak typicality
> (`AEP.lean` 1599 行) と並立、E-1 (Channel coding strong converse) / E-5
> (Slepian–Wolf achievability) の **共通前段**。

## 進捗

- [x] Phase 0 — 起草: 既存資産 / Mathlib API の棚卸し ✅
- [x] Phase 1 — `stronglyTypicalSet` 定義 + 基本 measurability ✅
- [x] Phase 2 — WLLN 経由の `P^n(A^*) → 1` ✅
- [x] Phase 3 — Strong → Weak bridge (entropy concentration) ✅
- [x] Phase 4 — Size sandwich (`card_le` + `card_ge_eventually`) ✅
- [x] Phase 5 — Common2026.lean 登録 + seeds.md 更新 ✅

## ゴール / Approach

**最終目標** (Cover-Thomas Theorem 11.2.1 strong typicality):
有限 alphabet `α` 上の i.i.d. 列 `Xs : ℕ → Ω → α`、各 letter `a ∈ α` の真確率
`P(a) = (μ.map (Xs 0)).real {a}` で:

1. `stronglyTypicalSet_prob_tendsto_one` —
   `μ {ω | jointRV Xs n ω ∈ A^*_ε^n} → 1` as `n → ∞`
2. `stronglyTypicalSet_card_le` (size 上界) —
   `(|A^*_ε^n| : ℝ) ≤ exp (n · (H(Xs 0) + ε·L))` where `L := ∑_a |log P(a)|`
3. `stronglyTypicalSet_card_ge_eventually` (size 下界、eventually-N 形) —
   `∀ η > 0, ∃ N, ∀ n ≥ N, (1-η) · exp(n · (H(Xs 0) - ε·L)) ≤ |A^*_ε^n|`

**戦略** (Mathlib-shape-driven definitions):

`A^*` 定義は **per-letter form** `∀ a, |(N(a|x^n) : ℝ)/n - P(a)| ≤ ε` (textbook 形)
を採用。理由:
- `Finset.sum` ベースの bound (`∑ a, |...| · |log P a| ≤ ε · ∑_a |log P a|`) と直接合う
- WLLN `strong_law_ae_real` を **letter 毎の indicator** `Y i := 𝟙(Xs i = a)` で n 本回し、
  union bound over `α` (finite) で全 letter 同時に押さえる
- `‖c/n - P‖_∞ ≤ ε` 形は同じ集合 (∀ a, … ≤ ε ⟺ sup_a … ≤ ε)、必要なら equivalence lemma

**Strong → Weak typicality bridge** (Phase 3 の核):
```
(∑_i pmfLog (x_i)) / n - H(P) = ∑_a ((N(a|x^n)/n) - P(a)) · (-log P(a))
```
Strong typical で `|N(a|x^n)/n - P(a)| ≤ ε` ⟹
`|(∑_i pmfLog)/n - H(P)| ≤ ε · ∑_a |log P(a)| = ε · L`。

即ち `x ∈ A^*_ε^n ⟹ x ∈ T_{ε·L}^n` (weak typical with adapted threshold)。
これで size sandwich (Phase 4) は `typicalSet_card_le` / `typicalSet_card_ge_eventually`
を `ε ← ε·L` で呼ぶだけ。

**Joint version は scope deferred の判断 (Phase 0)**: 主スコープ (~700 行) を超えるため、
本 plan では single-variable 形 (`α` 上) のみ publish。joint 形 `Fin n → α × β` 上の
`A^*(X,Y)` は **同じ definition shape を `α × β` で instantiate するだけ**で得られる
(`stronglyTypicalSet` は `α` generic)。joint typical ⟺ marginal typical の equivalence
は別 plan に分離 (E-5 Slepian–Wolf achievability の前段として独立に取得可能)。

## Phase 0 — 既存資産 / Mathlib API の棚卸し ✅

### 既存資産 (本 plan で再利用)

| 補題 / 定義 | ファイル | 形 |
|------|---------|-----|
| `typeCount` | `Sanov.lean:49` | `typeCount x a := #{i | x i = a}` |
| `pmfLog` | `AEP.lean:75` | `pmfLog μ Xs a := -Real.log (μ.map (Xs 0)).real {a}` |
| `jointRV` | `AEP.lean:55` | `jointRV Xs n ω i := Xs i ω` |
| `typicalSet` | `AEP.lean:229` | weak typical: `|(∑ pmfLog(x_i))/n - H| < ε` |
| `typicalSet_card_le` | `AEP.lean:257` | `\|T_ε^n\| ≤ exp(n(H+ε))` |
| `typicalSet_prob_tendsto_one` | `AEP.lean:375` | `μ {ω | jointRV ∈ T} → 1` |
| `typicalSet_card_ge_eventually` | `AEP.lean:1554` | `∃ N, ∀ n ≥ N, (1-η)·exp(n(H-ε)) ≤ \|T\|` |
| `strong_law_ae_real` | Mathlib `Probability.StrongLaw` | i.i.d. WLLN |
| `sum_fiberwise_of_maps_to'` | Mathlib `BigOperators` | `∑ a, ∑ i ∈ filter (x i = a), f a = ∑ i, f (x i)` |
| `tendstoInMeasure_of_tendsto_ae` | Mathlib `MeasureTheory.Function.ConvergenceInMeasure` | a.s. → in probability |

### Mathlib API (新規 import なし、`AEP.lean` の import で足りる)

- `Mathlib.Probability.StrongLaw` (既)
- `Mathlib.MeasureTheory.Function.ConvergenceInMeasure` (既)
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` (既、`AEP.lean` 経由)

## Phase 1 — `stronglyTypicalSet` 定義 + 基本 measurability ✅

```lean
/-- **Strongly typical set** (Cover-Thomas 11.2):
`A^*_ε^n := {x : Fin n → α | ∀ a, |(typeCount x a : ℝ) / n - P(a)| ≤ ε}`. -/
noncomputable def stronglyTypicalSet
    (μ : Measure Ω) (Xs : ℕ → Ω → α) (n : ℕ) (ε : ℝ) :
    Set (Fin n → α) :=
  { x | ∀ a : α, |(typeCount x a : ℝ) / n - (μ.map (Xs 0)).real {a}| ≤ ε }

theorem measurableSet_stronglyTypicalSet (μ Xs n ε) :
    MeasurableSet (stronglyTypicalSet μ Xs n ε) :=
  (Set.toFinite _).measurableSet
```

## Phase 2 — `stronglyTypicalSet_prob_tendsto_one` ✅

```lean
theorem stronglyTypicalSet_prob_tendsto_one
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hindep : Pairwise fun i j => Xs i ⟂ᵢ[μ] Xs j)
    (hident : ∀ i, IdentDistrib (Xs i) (Xs 0) μ μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ => μ {ω | jointRV Xs n ω ∈ stronglyTypicalSet μ Xs n ε})
      atTop (𝓝 1)
```

**証明戦略 (per-letter WLLN + union bound)**:
1. Per letter `a ∈ α`: define indicator `Y_a i ω := if Xs i ω = a then 1 else 0 : ℝ`.
2. `μ.map (Y_a 0)` の真平均 = `P(a)` (`integral_indicator` + `Measure.real`)。
3. `strong_law_ae_real` を `Y_a` 列に適用 → `(1/n) ∑ i, Y_a i ω → P(a)` a.s.
   - `tendstoInMeasure_of_tendsto_ae` で確率収束に変換
4. 各 `a` で `μ {ω | |(1/n) ∑ Y_a i ω - P(a)| > ε} → 0`.
5. `α` finite, union bound: `μ {ω | ∃ a, |...| > ε} → 0`.
6. 補集合に対応: `μ {ω | ∀ a, |...| ≤ ε} → 1`.
7. `(1/n) ∑ i, Y_a i ω = (typeCount (jointRV ω) a : ℝ) / n` の identity
   (`sum_fiberwise_of_maps_to'` で集約)。

## Phase 3 — Strong → Weak typicality bridge ✅

```lean
lemma stronglyTypical_implies_weakly_typical
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xs : ℕ → Ω → α) (hXs : ∀ i, Measurable (Xs i))
    (hpos : ∀ a : α, 0 < (μ.map (Xs 0)).real {a})
    (n : ℕ) {ε : ℝ}
    (x : Fin n → α) (hx : x ∈ stronglyTypicalSet μ Xs n ε) :
    |((∑ i : Fin n, pmfLog μ Xs (x i)) / n) - entropy μ (Xs 0)|
      ≤ ε * (∑ a : α, |Real.log ((μ.map (Xs 0)).real {a})|)
```

**証明**:
- `(∑ i, pmfLog (x_i))/n - H(P)`
  `= - (∑ i, log P(x_i))/n - (-∑_a P(a) · log P(a))`  (entropy / pmfLog 展開)
  `= ∑_a (P(a) - (typeCount x a / n)) · log P(a)`     (sum_fiberwise_of_maps_to')
- 三角不等式 + `|P(a) - typeCount x a / n| ≤ ε` (strong typical, `hx`)
- `entropy` definition expansion: `entropy μ (Xs 0) = -∑ a, P(a) · log P(a)`
  (Mathlib `entropy_eq_sum_negMulLog` 系 or AEP `integral_logLikelihood_zero` 経由)

`L := ∑ a, |log P(a)|` を有限 (alphabet 有限) で押さえれば weak typical
`|.../n - H| ≤ ε · L` が出る。

**注意**: `≤ ε · L` (closed) vs `< ε` (strict open) の差を吸収するため、weak typical
への変換は `ε' := 2 · ε · L` のような余裕を取って `< ε'` の strict 形に。

## Phase 4 — Size sandwich ✅

### 上界

```lean
theorem stronglyTypicalSet_card_le
    (μ Xs hXs) (hpos : ∀ a, 0 < (μ.map (Xs 0)).real {a})
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((stronglyTypicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
      ≤ Real.exp ((n : ℝ) * (entropy μ (Xs 0) + ε * logSumAbs μ Xs + (1 : ℝ)))
```

または **strict 形** で `ε' := ε · L + δ` を取り、Phase 3 で `≤ ε·L < ε'` を経由、
`typicalSet_card_le` を `ε ← ε'` で呼ぶ。

### 下界 (eventually-N 形)

```lean
theorem stronglyTypicalSet_card_ge_eventually
    (μ Xs hXs hindep_full hindep_pair hident)
    (hpos : ∀ a, 0 < (μ.map (Xs 0)).real {a})
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ N, ∀ n ≥ N,
      (1 - η) * Real.exp ((n : ℝ) * (entropy μ (Xs 0) - ε * logSumAbs μ Xs - 1))
        ≤ ((stronglyTypicalSet μ Xs n ε).toFinite.toFinset.card : ℝ)
```

Strong typical ⊆ weak typical (Phase 3 + `ε'`) なので **逆** に
`weak typical |T_{ε'}| ≤ |A^*_ε|` は **成立しない**。

正しい経路: `A^* ⊆ T_{ε·L+δ}` から `|A^*| ≤ |T_{ε·L+δ}|` で **上界** は `typicalSet_card_le` 経由。

**下界** は `μ(A^*) → 1` (Phase 2) を使い `μ(A^*) ≥ 1-η` eventually → `A^* ⊆ T_{ε·L+δ}`
中の質量 ≥ 1-η → `typicalSet_card_ge_eventually` の **論理を再現** (`A^*` 上の各点の
pmf 値が上界を持つことを Phase 3 経由で確保 → `μ(A^*) ≤ |A^*| · exp(-n(H-ε·L-δ))`).

## Phase 5 — 登録 + seeds.md 更新 ✅

- `Common2026.lean` に `import Common2026.Shannon.StrongTypicality` 追加。
- `docs/moonshot-seeds.md` E-7 行を ✅ + plan pointer に更新、冒頭サマリ文も同期。

## 判断ログ

1. **per-letter form vs sup-norm form**: 定義は per-letter (`∀ a, |…| ≤ ε`) を採用。
   理由は (a) WLLN を per-letter indicator で n 本回した結果の union bound に直接合う、
   (b) sup-norm `‖c/n - P‖_∞ ≤ ε` は per-letter と同じ集合 (∀ ⟺ sup) で本質差なし、
   (c) Mathlib `Pi.lpNorm` の plumbing を回避できる。

2. **`≤ ε` (closed) vs `< ε` (strict) の選択**: weak typical は `< ε` (strict)、
   strong typical は `≤ ε` (closed) を採用。理由は WLLN 出力 `μ {|…| ≥ ε} → 0` の
   補集合が `{|…| < ε}` であり、union bound 後 `{∀ a, |…| < ε} ⊆ {∀ a, |…| ≤ ε}` で
   確率 → 1 が単調に維持される。strict 形のままだと Phase 3 で weak typical (`< ε'`)
   への変換に余裕が必要で見通しが悪い。

3. **Joint version を scope-deferred**: 本 plan の `stronglyTypicalSet` は `α` generic、
   `α := α' × β` で instantiate すれば joint 形が直接得られる。marginal ↔ joint
   equivalence は別 plan (E-5 前段) に分離、本 plan では single-variable 形のみ publish。

4. **Strong → Weak bridge の精度損失 `ε · L`**: `L := ∑ a, |log P(a)|` は有限
   (alphabet 有限) だが `min_a P(a) → 0` で `L → ∞`。本 plan は `hpos` を仮定し
   `L` 有限を担保。`L` の値依存は size sandwich の指数誤差 `ε·L` に反映される (textbook
   と整合)。

## 実装完了 (2026-05-13)

`Common2026/Shannon/StrongTypicality.lean` (614 行) で全 5 Phase を **0 sorry** で publish。

### 公開された主要 lemma

| 補題 | 役割 | 行範囲 (概算) |
|------|------|----------|
| `stronglyTypicalSet` (def) | Per-letter form: `∀ a, |(typeCount x a : ℝ)/n - P(a)| ≤ ε` | Phase 1 |
| `measurableSet_stronglyTypicalSet` | 自動 measurability (finite ambient) | Phase 1 |
| `letterIndicator` (def) | `if Xs i ω = a then 1 else 0` | Phase 2 |
| `integral_letterIndicator` | `∫ Y_a 0 ∂μ = P(a)` (WLLN limit) | Phase 2 |
| `letterIndicator_inProbability` | Per-letter WLLN (in probability) | Phase 2 |
| `typeCount_eq_sum_indicator` | `(typeCount x a : ℝ) = ∑ i, indicator(x_i = a)` | Phase 2 |
| **`stronglyTypicalSet_prob_tendsto_one`** | `μ {ω | jointRV ∈ A^*_ε} → 1` | Phase 2 |
| `logSumAbs` (def) | `L := ∑ a, |log P(a)|` | Phase 3 |
| `weak_displacement_eq_strong_sum` | Bridge identity (weak displacement → strong sum) | Phase 3 |
| `stronglyTypical_implies_weakly_typical_bound` | `|.../n - H| ≤ ε · L` for strong typical | Phase 3 |
| `stronglyTypicalSet_subset_typicalSet` | `A^*_ε ⊆ T_{ε'}` for `ε·L < ε'` | Phase 3 |
| **`stronglyTypicalSet_card_le`** | `|A^*_ε| ≤ exp(n(H + ε·L + δ))` | Phase 4 |
| **`stronglyTypicalSet_card_ge_eventually`** | `(1-η)·exp(n(H - ε·L - δ)) ≤ |A^*_ε|` eventually | Phase 4 |

### 設計判断 (実装中に確認)

1. **`hε : 0 ≤ ε` 仮定 in `card_le`**: 当初 plan で `ε` の符号は未指定だったが、`logSumAbs` の
   非負性と組み合わせて `ε · L + δ > 0` を担保するため `0 ≤ ε` を追加。`ε < 0` の場合は
   `stronglyTypicalSet` が空 (`|.| ≥ 0 > ε`) で trivial だが、明示的に `0 ≤ ε` を要求した方が
   bound expression の正値性が一目瞭然。

2. **ENNReal 直接の squeeze**: `tendsto_of_tendsto_of_tendsto_of_le_of_le'` (apostrophe 形、
   eventually バージョン) を採用。`Filter.Eventually.of_forall` で pointwise 仮定を持ち上げる。
   `ENNReal.Tendsto.sub` も `Or.inr (by simp)` (右側 finiteness) で適用。

3. **per-letter form 採用が WLLN との合わせ**: WLLN は `letterIndicator Xs a i` 列に
   `strong_law_ae_real` を **letter ごとに独立に** n 本回す形になる。union bound (`measure_iUnion_fintype_le`)
   で全 letter 同時 concentration が出る。sup-norm form だと WLLN の適用方向が若干曲がる。

4. **`n > 0` 仮定 in `card_le` / bridge**: `weak_displacement_eq_strong_sum` で `/n` 除算が
   入るため `n > 0` 必須。card_le も同様。`card_ge_eventually` は eventually-N 形で
   `N := max N₀ 1` を取り `n ≥ 1` を担保。

5. **Joint version deferred**: `α` generic 設計を活用すれば `α := α' × β` 代入で
   `stronglyTypicalSet (μ := μ_{XY}) (Xs := joint)` が直接 joint strong typical 形に。
   marginal ↔ joint typical 同時成立の equivalence は E-5 (Slepian–Wolf achievability) の
   前段で別途必要、本 plan で取得せず E-5 plan へ送り。

### Mathlib gap (なし)

特に上流 PR 候補となる gap は発見されなかった。`strong_law_ae_real` / `tendstoInMeasure_of_tendsto_ae`
/ `tendsto_finsetSum` / `ENNReal.Tendsto.sub` / `measure_iUnion_fintype_le` の組み合わせで
完結。AEP `typicalSet_card_le` / `typicalSet_prob_le` の既存資産が **そのまま** Phase 4 で
呼べる shape だった (D-3 Phase G/H の `hpos` ベース定式化が再利用に直効きした)。

## 横断観察

- **E-5 Slepian–Wolf achievability への joint 形**: 本 plan の `stronglyTypicalSet` は
  `α` generic のため `Fin n → α × β` 上で再利用可能。E-5 で
  `jointlyStronglyTypicalSet := stronglyTypicalSet (μ := μ_{XY}) (Xs := (X, Y))` を
  instantiate するだけ。marginal ↔ joint typical 同時成立の equivalence は
  union-bound on `α × β` finite から導出。
- **E-1 Channel coding strong converse**: 強形 converse の `R > C ⟹ P_err > 1-ε` を
  strong typical 経路で証明する場合、receiver 側 `Y` の strong typical decoder
  (`A^*(Y) := {y | ∀ b, |N(b|y^n)/n - Q(b)| ≤ ε}`, `Q := output 分布`) と
  channel 上の joint strong typical を組み合わせる。本 plan の WLLN 経路は直接転用可能。
- **`logSumAbs` の bridge identity**: `L := ∑ a, |log P(a)|` を `negEntropy + |negEntropy|`
  形に書き直す機会 (signed log 分離)、ただし本 plan で必要なのは `L < ∞` のみで
  identity bridging は不要。
