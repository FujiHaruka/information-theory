# T2-E Brunn-Minkowski (entropy form) — Mathlib Inventory

Cover-Thomas Theorem 17.9.2 (Brunn-Minkowski の entropy 形) を Lean に持ち込む際に
利用可能な Mathlib lemma / 構造を確認したログ。

## 結論 (要旨)

- **Brunn-Minkowski そのものは Mathlib に不在**。
  - `loogle "BrunnMinkowski"` → `unknown identifier`。
  - `loogle "Brunn"` → `unknown identifier`。
- これにより T2-E は **statement-level pass-through publish** で着地する。
  本 plan は EPI (T2-D, `EntropyPowerInequality.lean`) の三本立て撤退
  (L-EPI1 + L-EPI2 + L-EPI3) と同流儀で
  **L-BM1 (EPI からの specialization) + L-BM2 (uniform = log vol)
  + L-BM3 (Minkowski sum 可測性)** の 3 本撤退で組む。

## API in scope

### Set arithmetic (Minkowski sum)

- `Set.add : Set α → Set α → Set α` (from `Mathlib.Algebra.Group.Pointwise.Set.Basic`)
  - pointwise `A + B := {a + b | a ∈ A, b ∈ B}`. 加群構造があれば自動。
- `Set.add_nonempty`, `Set.Nonempty.add` — 非空性は和に伝播。
- `Set.univ_add_univ`, `Set.add_empty`, `Set.empty_add` — 境界条件。

### Volume / Haar measure (`n`-dim)

- `MeasureTheory.Measure.addHaar` (from `Mathlib.MeasureTheory.Measure.Haar.Basic`)
  - 局所コンパクト位相加群上の左不変測度。`ℝ^n` 上では Lebesgue 測度
    `volume = MeasureTheory.volume` と一致 (係数差なし、`addHaar_eq_volume`)。
- `LinearMap.exists_map_addHaar_eq_smul_addHaar'` — affine 変換と Haar
  measure の関係 (本 plan では未使用、Phase E 拡張で参照可)。
- 本 plan は **`n`-dim Lebesgue 測度の値** を hypothesis として外から渡す
  形にし、Brunn-Minkowski の積分計算は L-BM 系で吸収する。

### Real.exp / Real.log / Real.rpow

- `Real.exp_pos : 0 < Real.exp x` — `entropyPower_nDim_pos` で利用。
- `Real.exp_log : 0 < x → Real.exp (Real.log x) = x` — entropy = log vol
  hypothesis の reverse direction で利用。
- `Real.rpow_natCast : x ^ (n : ℕ) = x ^ (n : ℝ)` — `|A|^{1/n}` 形と
  自然指数の橋渡し (本 plan では未使用、`exp ((2/n) h)` 形で吸収)。

### `differentialEntropy` 系 (Common2026 既存)

- `Common2026.Shannon.differentialEntropy : Measure ℝ → ℝ`
  - 1-D 限定。`Measure (Fin n → ℝ)` 上の n-dim differential entropy は
    **Common2026 には未定義**。EPI も `ℝ` 上のみ。
  - 結果: 本 plan の主定理は **`n`-dim differential entropy を
    abstract scalar `h : Measure (Fin n → ℝ) → ℝ` の signature 引数**
    として受け取り、その上の Brunn-Minkowski 性質を hypothesis 化する。
    Discharge plan で本物の n-dim entropy 定義に置換可能な signature を保つ。
  - これは EPI L-EPI3 と同流儀の predicate pass-through。

### Convexity

- `Convex` (from `Mathlib.Analysis.Convex.Basic`) — `ConvexBody` も別途。
  本 plan の系 (convex body Brunn-Minkowski) では `Convex ℝ A` を引数に取り、
  `volume A`, `volume B` の hypothesis から `|A+B|^{1/n} ≥ |A|^{1/n} + |B|^{1/n}`
  を導出する形。convex 条件自体は **本 file では使用しない**
  (uniform on convex body の entropy = log volume hypothesis に吸収される)。

## 撤退ライン 3 本

| ID  | predicate                                | 役割                                                                                    |
|-----|------------------------------------------|-----------------------------------------------------------------------------------------|
| L-BM1 | `IsBrunnMinkowskiEntropyHypothesis`     | EPI の n-dim 形 `e^{(2/n) h(X+Y)} ≥ e^{(2/n) h(X)} + e^{(2/n) h(Y)}` を直接 hypothesis 化。主定理本体はこれ単独で着地。 |
| L-BM2 | `IsUniformOnEntropyLogVolHypothesis`    | uniform 分布の entropy = log volume の事実を hypothesis 化。系 (convex body) で利用。               |
| L-BM3 | `IsMinkowskiSumMeasurableHypothesis`    | convex bodies `A, B` の Minkowski sum `A + B` の可測性を hypothesis 化。                       |

## 採用パターン

EPI (T2-D, 347 行) と同じ:

- `entropyPower_nDim n μ h := Real.exp ((2 / n) * h μ)` (`n`-dim entropy power)
- 主定理 `brunn_minkowski_entropy_inequality` は L-BM1 単独で `:= h_bm` 着地
- 系 `brunn_minkowski_convex_body`: L-BM1 + L-BM2 + L-BM3 を combine、
  uniform の hypothesis 経由で `|A+B|^{1/n} ≥ |A|^{1/n} + |B|^{1/n}` を導出
- positivity / scaling corollary を `Real.exp_pos` 系で full discharge
