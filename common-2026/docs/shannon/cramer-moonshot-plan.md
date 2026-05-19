# Cramér's Theorem ムーンショット計画 🌙 (T1-C)

<!--
雛形メモ (moonshot-plan-template.md より):
- 進捗ブロック: `- [ ] Phase 名 — 短い説明 状態絵文字 (関連ファイルへのリンク)` の形式
- 状態絵文字: 📋 未着手 / 🚧 進行中 / ✅ 完了 / 🔄 方針変更（判断ログ参照）
- 削除/廃止された Phase は ~~取り消し線~~ で残す（完全削除しない、過去参照のため）
- 判断ログは append-only。Phase 中の方針変更・撤退・当初仮定の修正を記録
-->

> **Parent**: [`textbook-roadmap.md`](../textbook-roadmap.md) §「Tier 1 — T1-C. Cramér's Theorem」
>
> **Predecessor (inventory)**: [`cramer-mathlib-inventory.md`](cramer-mathlib-inventory.md) (Mathlib 80% / Common2026 10% / 自作 10%、見積 300〜400 行)
>
> **Status (2026-05-19)**: 着手前。inventory 完了済、自作要素 5 件 (`legendre` 定義 + 基本性質 / `cramerRate` wrapper / KL-of-tilted 恒等式 / `cramer_upper` / `cramer_lower`) を確定。**Mathlib `cgf` + `Measure.tilted` 直接経路**を採用 (Sanov contraction principle 経由は不採用、判断ログ #1)。**finite-alphabet 系の `bounded RV` 仮定**で `integrableExpSet = univ` を確保 (`interior` 境界処理を回避、判断ログ #3)。
>
> **Goal**: 新規ファイル `Common2026/Shannon/Cramer.lean` で **Cover-Thomas Theorem 11.4.1** (Cramér の大偏差定理、IID 和の sample mean upper-tail rate = Legendre transform of CGF) を **`Tendsto` / `limsup` / `liminf` 形**で publish。
>
> **撤退ライン**: [L-C1] upper bound のみ publish / [L-C2] lower bound を仮定形で publish / [L-C3] finite-alphabet `α → ℝ` 専用形に限定 (詳細 §撤退ライン)。

## 進捗

- [x] Phase 0 — Mathlib + Common2026 API 在庫 ✅ → [`cramer-mathlib-inventory.md`](cramer-mathlib-inventory.md)
- [x] Phase A — `legendre` + `cramerRate` 定義 + 基本性質 + skeleton ✅ (Tier 0, 2026-05-19)
- [x] Phase B — Cramér upper bound (per-n Chernoff + log form + limsup form + Legendre form, i.i.d. strengthening) ✅ (Tier 1–3, 2026-05-19)
- [ ] Phase C — Cramér lower bound (tilted change of measure + tilted-下 LLN) 📋
- [ ] Phase D — 主定理 wrapper (`Tendsto` 形 sandwich + `Common2026.lean` 編入) 🔄 (Phase D-4 編入のみ Tier 0 で前倒し済、`Tendsto` sandwich は lower bound 完成後に defer)

## ゴール / Approach

### Goal (最終定理 signature)

新規ファイル `Common2026/Shannon/Cramer.lean` で 1〜3 主定理 publish:

```lean
namespace InformationTheory.Shannon.Cramer

/-- **Legendre transform** of `Λ : ℝ → ℝ` at `a`. Mathlib 不在 (自前定義)。 -/
noncomputable def legendre (Λ : ℝ → ℝ) (a : ℝ) : ℝ :=
  sSup ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)

/-- **Cramér rate function**: `I(a) := Λ^*(a) = legendre (cgf X μ) a`. -/
noncomputable def cramerRate (X : Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ :=
  legendre (cgf X μ) a

/-- **Cramér upper bound** (bounded-RV IID, Cover-Thomas 11.4.1 upper half). -/
theorem cramer_upper
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
    (a : ℝ) :
    limsup (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop
      ≤ -cramerRate (X 0) μ a

/-- **Cramér lower bound** (achievability, tilted change-of-measure). -/
theorem cramer_lower
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
    (a : ℝ) (h_lam : ∃ lam : ℝ, 0 ≤ lam ∧ deriv (cgf (X 0) μ) lam = a) :
    -cramerRate (X 0) μ a
      ≤ liminf (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop

/-- **Cramér tendsto** (optional, sandwich). -/
theorem cramer_tendsto ... :
    Tendsto (fun n : ℕ =>
        (1 / (n : ℝ)) * Real.log
          (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}))
      atTop (𝓝 (-cramerRate (X 0) μ a))

end InformationTheory.Shannon.Cramer
```

statement 形 (`Tendsto` 直書き vs `DotEq` corollary、achievability / converse split の粒度) は **Phase A 着手時の C-1 で確定**。既存 Stein/Sanov/Chernoff の流儀 (`Tendsto` を main + `DotEq` を corollary) に従う方針 (判断ログ #2)。

### Approach (overall strategy / shape of solution)

**戦略の shape**: Cover-Thomas 11.4 では **Cramér ⇐ Sanov の contraction principle** で導かれるが、本 plan では **Sanov 経由を採用しない**。代わりに **Mathlib `cgf` + `Measure.tilted` 直接経路**を採る:

1. **Upper bound = Chernoff bound の n-IID 強化**:
   - `iIndepFun.cgf_sum` (Mathlib `Probability/Moments/Basic.lean:393`) + `IdentDistrib` で `cgf (∑ X_i) μ t = n · cgf (X 0) μ t`
   - `measure_ge_le_exp_cgf` (Mathlib `Basic.lean:461`) を `X := ∑ X_i`, `ε := n · a`, `t := λ ≥ 0` で起動 → `μ.real {ω | n·a ≤ ∑ X_i ω} ≤ exp(-n · (λ·a - Λ(λ)))`
   - `(1/n) log` 取って `sup_{λ ≥ 0}` で `-legendre Λ a` (+ 後述 `legendre = sup_{λ≥0}` の `a ≥ E[X]` case 正当化)
   - **Mathlib の Chernoff bound がそのまま「Cramér upper bound の単項 + n-IID で繋ぐだけ」の構造**で、自前ロジックは **~80-120 行**。

2. **Lower bound = tilted-measure change-of-measure**:
   - `λ^*` を `Λ'(λ^*) = a` で取る (`h_lam` 仮定、bounded RV では `Λ` 全 ℝ で解析的 ⇒ `integrableExpSet = univ` ⇒ `deriv_cgf` (Mathlib `MGFAnalytic.lean:188`) 全域で使用可)
   - `μ_{λ^*} := μ.tilted (λ^* * X 0 ·)` 構築、`integral_tilted_mul_self` (Mathlib `Tilted.lean:132`) で `(μ_{λ^*})[X 0] = Λ'(λ^*) = a`
   - tilted 下で LLN (in-probability 弱形、Chebyshev with `variance_tilted_mul`) → `μ_{λ^*}({|S̄_n - a| ≤ ε}) → 1`
   - **change-of-measure (RN derivative from `tilted_apply'` + `rnDeriv_tilted_left_self`)** で `μ` 側に戻すと `μ({n·a ≤ ∑ X_i}) ≥ exp(-n · (λ^* · a - Λ(λ^*))) · (1 - o(1))`
   - 指数を取り `λ^* · a - Λ(λ^*) = legendre Λ a` (最適化条件) で完結。

3. **finite-alphabet specialization の役割** (judgement #3): **`X` 有界**仮定で `integrableExpSet X μ = univ`、`interior = univ` が無条件成立。これにより `deriv_cgf` / `integral_tilted_mul_self` / `variance_tilted_mul` の `(ht : t ∈ interior ...)` 前提を全て自明化、Phase B/C で `interior` 境界処理が **0 行で済む**。textbook の一般 RV 形 (unbounded、`integrableExpSet` の interior 境界処理 +100 行) は L-C3 の **撤退条件としてのみ**残し、最初の publish には含めない。

4. **Mathlib-shape-driven Legendre 定義**:
   - `legendre Λ a := sSup ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)` — Mathlib 不在 (loogle: `Legendre` の hit は数論 `legendreSym` のみ、`Fenchel`/`ConvexConjugate` 0 件)
   - 達成性は `chernoffInfo_attained` (`Chernoff.lean:161`) の **`IsCompact.exists_sSup_image_eq` 戦略を流用** (連続 `Λ` on compact `Icc` + sSup ↔ iSup 同一視)
   - **但し本 plan の publish 形では `legendre Λ a` の達成性 (`∃ λ^*, legendre Λ a = λ^* · a - Λ(λ^*)`) は仮定 (`h_lam`) として外出し** → 達成性証明は Tier 3 (一般形) で。

### Approach 図

```
Phase 0 : Mathlib + Common2026 API 在庫                       ← 完了済 (inventory)
          ──────────────────────────────────────────────
Phase A : skeleton + `legendre` + `cramerRate` 定義 + 基本性質 ← 0.5-0.75 session (1-1.5h)
                                                                = Tier 0 (~100 行) baseline
          ──────────────────────────────────────────────
Phase B : Cramér upper bound (Chernoff bound 直接)            ← 0.75-1 session (1.5-2h)
                                                                = Tier 1 (~250 行) L-C1 撤退ライン
          ←──── 撤退ライン L-C1 (upper のみ publish) ────────→
          ──────────────────────────────────────────────
Phase C : Cramér lower bound (tilted change-of-measure)       ← 1-1.5 session (2-3h)
                                                                = Tier 2 (~400 行) 理想形
          ←──── 撤退ライン L-C2 (lower 仮定形 publish) ──────→
          ──────────────────────────────────────────────
Phase D : 主定理 wrapper + Common2026 編入                    ← 0.25 session (0.5h)
```

### 段階的 ship 設計 (Tier 0 / 1 / 2 / 3)

- **Tier 0** (~100 行): `legendre` + `cramerRate` 定義 + `legendre_nonneg` (`Λ(0) = 0` ⇒ `legendre Λ a ≥ 0`) + `cgf_sum_eq_nsmul` 補題。Phase A 完了で発生。
- **Tier 1** (~250 行, L-C1 撤退ライン): + Cramér upper bound。Phase B 完了で発生 (publish 価値あり = Chernoff bound の n-IID 強化版)。
- **Tier 2** (~400 行, 理想): + Cramér lower bound (tilted change-of-measure)。Phase C 完了 = Cover-Thomas 11.4.1 完成形。
- **Tier 3** (stretch): general (non-bounded RV) 形、`legendre` 達成性 (`Λ` 凸 + 連続 + coercive 経由)、`cramer_tendsto` sandwich。**本 plan のスコープ外**、Tier 2 publish 後の派生 plan で。

### 規模見積もり (再掲、inventory より)

| 自作要素 | 想定行数 | Phase |
|---|---|---|
| `legendre` 定義 + `legendre_nonneg` + `cramerRate` wrapper | ~30-60 | A |
| `cgf_sum_eq_nsmul` (n-IID + IdentDistrib で n·cgf に潰す) | ~20-30 | A or B |
| Cramér upper bound `cramer_upper` 主定理 | ~80-120 | B |
| `klDiv_tilted_eq` (KL-of-tilted 恒等式) | ~30-50 | C |
| n-IID tilted ambient plumbing (`infinitePi (μ.tilted) = (infinitePi μ).tilted ?`) | ~30-50 | C |
| Cramér lower bound `cramer_lower` 主定理 | ~120-180 | C |
| `cramer_tendsto` sandwich (optional) | ~10 | D |
| skeleton + imports + docstring + namespace | ~30-50 | A |
| **合計** | **~350-540** | |

中央予測 **~400 行** (roadmap 「300-500 行」下限寄り)。撤退ライン L-C1 で Tier 1 止まりなら ~250 行。

### ファイル構成 (Phase D 完了想定)

```
Common2026/Shannon/
  Cramer.lean                ← 新規 (T1-C 一括 publish、~400 行)
  Chernoff.lean              ← 既存、変更なし (`chernoffInfo_attained` の `IsCompact.exists_sInf_image_eq`
                                  テンプレ流用、import なしで参考のみ — 互いに無依存に保つ)
Common2026/InformationTheory/
  Asymptotic.lean            ← 既存、変更なし (`DotEq` notation 利用、Phase D で optional corollary 用)
Common2026.lean              ← `import Common2026.Shannon.Cramer` を追記 (Phase D)
```

**Sanov 関連の不依存**: `SanovLDP.lean` / `SanovLDPEquality.lean` は **import しない** (判断ログ #1 経路選択により Sanov contraction principle を経由しない)。同様に `Stein.lean` / `CsiszarProjection.lean` も不要。**新規 import は Mathlib `Probability.Moments.*` + `Probability.Independence.InfinitePi` + `Probability.IdentDistrib` + `MeasureTheory.Measure.Tilted` のみ** (CLAUDE.md `Import Policy` 厳守、`import Mathlib` は使わない)。

## 依存関係

完了済 / 利用可:

- [x] **Mathlib `Probability.Moments.Basic`**: `mgf`, `cgf`, `mgf_zero`, `cgf_zero`, `mgf_pos`, `exp_cgf`, `mgf_id_map`, `mgf_congr_identDistrib`, `iIndepFun.cgf_sum`, `iIndepFun.cgf_sum₀`, `iIndepFun.mgf_sum`, `mgf_sum_of_identDistrib`, `IndepFun.cgf_add`, **`measure_ge_le_exp_cgf`** (Chernoff bound), `measure_le_le_exp_cgf`, `measure_ge_le_exp_mul_mgf`, `measure_le_le_exp_mul_mgf`
- [x] **Mathlib `Probability.Moments.MGFAnalytic`**: `analyticOnNhd_cgf`, `deriv_cgf`, `deriv_cgf_zero`, `iteratedDeriv_two_cgf_eq_integral`, `continuousOn_mgf`
- [x] **Mathlib `Probability.Moments.IntegrableExpMul`**: `integrableExpSet`, `convex_integrableExpSet`, `integrable_of_mem_integrableExpSet`
- [x] **Mathlib `Probability.Moments.Tilted`**: `tilted_mul_apply_cgf`, **`integral_tilted_mul_self`** (`Λ'(t)`), **`variance_tilted_mul`** (`Λ''(t)`)
- [x] **Mathlib `MeasureTheory.Measure.Tilted`**: `Measure.tilted`, `isProbabilityMeasure_tilted`, `tilted_absolutelyContinuous`, `absolutelyContinuous_tilted`, `rnDeriv_tilted_left_self`, `log_rnDeriv_tilted_left_self`
- [x] **Mathlib `Probability.Independence.*`**: `iIndepFun`, `iIndepFun_infinitePi`, `IdentDistrib`
- [x] **Mathlib `Probability.ProductMeasure`**: `Measure.infinitePi`, `Measure.infinitePi_map_eval`
- [x] **Mathlib `Probability.StrongLaw` 系**: LLN (Phase C で in-probability 弱形を Chebyshev で代替する場合は不要)
- [x] **Mathlib `Topology.Order.Compact`**: `IsCompact.exists_sSup_image_eq` (Tier 3 達成性用、Tier 2 では未使用)
- [x] `Common2026/InformationTheory/Asymptotic.lean` (`DotEq` notation、Phase D optional corollary 用)

**参考 (import しない)**:

- `Common2026/Shannon/Chernoff.lean` (`chernoffInfo_attained` の `IsCompact.exists_sInf_image_eq` 戦略はテンプレ流用するが、`chernoffZSum ≠ mgf` であり **互いに別物**)
- `Common2026/Shannon/SanovLDPEquality.lean`, `Common2026/Shannon/SanovLDP.lean` (経路選択により不使用、判断ログ #1)
- `Common2026/Shannon/IIDProductInput.lean` (より軽い `Measure.infinitePi (fun _ => μ)` を直接使う、in-place ~10 行 plumbing、判断ログ #4)

---

## Phase 0 — Mathlib + Common2026 API 在庫 ✅

完了 ([`cramer-mathlib-inventory.md`](cramer-mathlib-inventory.md), 441 行)。

主結論:

- **既存 API カバレッジ 80% (Mathlib) + 10% (Common2026 補助)**: `cgf` / `iIndepFun.cgf_sum` / `measure_ge_le_exp_cgf` / `Measure.tilted` / `integral_tilted_mul_self` / `variance_tilted_mul` で主要部品が完備
- **自作 5 件**: `legendre` 定義 (~10), `legendre_nonneg` (~20), `cgf_sum_eq_nsmul` (~25), Cramér upper (~100), KL-of-tilted (~40), Cramér lower (~150) — 合計 **~350-540 行**
- **撤退ライン現時点で発動なし**、新規撤退ライン 3 件 (L-C1〜L-C3) を本 plan に追加 (§撤退ライン)
- **Sanov contraction principle 経由は不採用** (reshape +120 行コスト回避、判断ログ #1)
- **finite-alphabet / bounded RV specialization** で `integrableExpSet = univ` 確保 → `interior` 境界処理を全て自明化 (判断ログ #3)

---

## Phase A — `legendre` + `cramerRate` 定義 + 基本性質 + skeleton 📋

### スコープ

`Cramer.lean` の skeleton を Write (全主定理 `:= by sorry`)、`legendre` / `cramerRate` 定義 + Tier 0 基本性質 (非負性、`legendre_apply_le`) を確定。

**proof-log**: yes (Tier 0 baseline publish 時点で `proof-log-cramer-tier0.md` を append)。

### Done 条件

- `Common2026/Shannon/Cramer.lean` 新規作成 + library root 編入準備 (`Common2026.lean` には Phase D で追記)
- `legendre Λ a := sSup ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)` 定義
- `cramerRate X μ a := legendre (cgf X μ) a` wrapper
- `legendre_apply_le` (`lam * a - Λ lam ≤ legendre Λ a` if BddAbove)
- `legendre_nonneg` (`Λ 0 = 0` 経由で `legendre Λ a ≥ 0` if BddAbove)
- `cgf_sum_eq_nsmul` (n-IID + IdentDistrib で `cgf (∑ X_i) μ t = n · cgf (X 0) μ t`)
- `lake env lean Common2026/Shannon/Cramer.lean` で Phase A 本体 + Phase B-D `sorry` skeleton が clean

### ステップ

- [ ] **A-0 skeleton**: 全主定理 + 補助補題を `:= by sorry` で並べた skeleton を Write、LSP 診断で type-check OK 確認 (CLAUDE.md "Skeleton-driven Development")。imports は §依存関係 の Mathlib リストのみ (Sanov 系 import しない)。

- [ ] **A-1 `legendre` 定義**:
  ```lean
  noncomputable def legendre (Λ : ℝ → ℝ) (a : ℝ) : ℝ :=
    sSup ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)
  ```
  - **落とし穴**: `sSup` は `BddAbove` でないと Mathlib では `0` 返却。`Λ` が下に有界でない (unbounded RV) と `legendre = +∞` 風で扱いに困るが、bounded RV では `Λ(λ) ≥ -|λ| · M + Λ(0)` で下に有界 ⇒ `lam * a - Λ lam` が `|lam|` 大で `-∞` に向かう ⇒ `sSup` 有限。Phase A では `legendre_bddAbove` を**仮定形** (hypothesis) で外出し、明示証明は L-C3 / Tier 3 で。

- [ ] **A-2 `cramerRate` wrapper**:
  ```lean
  noncomputable def cramerRate (X : Ω → ℝ) (μ : Measure Ω) (a : ℝ) : ℝ :=
    legendre (cgf X μ) a
  ```

- [ ] **A-3 `legendre_apply_le`**:
  ```lean
  lemma legendre_apply_le (Λ : ℝ → ℝ) (a : ℝ)
      (h_bdd : BddAbove ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ))
      (lam : ℝ) :
      lam * a - Λ lam ≤ legendre Λ a
  ```
  - `le_csSup h_bdd (Set.mem_image_of_mem _ (Set.mem_univ lam))` で 2 行。

- [ ] **A-4 `legendre_nonneg`**:
  ```lean
  lemma legendre_nonneg (Λ : ℝ → ℝ) (hΛ0 : Λ 0 = 0) (a : ℝ)
      (h_bdd : BddAbove ((fun lam : ℝ => lam * a - Λ lam) '' Set.univ)) :
      0 ≤ legendre Λ a
  ```
  - A-3 を `lam := 0` で起動 → `0 * a - Λ 0 = 0 ≤ legendre Λ a`。3-5 行。

- [ ] **A-5 `cgf_sum_eq_nsmul`** (Phase B の入口):
  ```lean
  lemma cgf_sum_eq_nsmul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
      (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
      (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
      (h_int : ∀ t i, Integrable (fun ω => Real.exp (t * X i ω)) μ)
      (t : ℝ) (n : ℕ) :
      cgf (∑ i ∈ Finset.range n, X i) μ t = (n : ℝ) * cgf (X 0) μ t
  ```
  - `iIndepFun.cgf_sum` (Mathlib `Basic.lean:393`) で `cgf (∑ X_i) μ t = ∑ i ∈ range n, cgf (X i) μ t`
  - `mgf_congr_identDistrib` (Mathlib `Basic.lean:227`) で各 `cgf (X i) μ t = cgf (X 0) μ t`
  - `Finset.sum_const` + `nsmul_eq_mul` で `n · cgf (X 0) μ t`
  - ~20-30 行 (`h_int i` から `Integrable (fun ω => exp (t * X i ω)) μ` を抜き出す plumbing 含む)

- [ ] **A-6 統合 verify**: `lake env lean Common2026/Shannon/Cramer.lean` clean。Phase B-D は `sorry` 残し。

### 工数感

~80-120 行 (skeleton ~50 + A-1 ~5 + A-2 ~5 + A-3 ~5 + A-4 ~5 + A-5 ~30)。0.5-0.75 session。

### 失敗時 fallback

- **`BddAbove` 仮定が散らかる**: `legendre` の return 型を `EReal` (`WithBot ℝ`) に変えて未境界形も飲み込む — **採用しない** (Mathlib `cgf : ℝ → ℝ` 形と signature 整合を保つ)。代わりに **bounded RV 仮定下で `legendre_bddAbove` を別補題** (~10 行) で先に確立し、Phase A 内では仮定として使い、Phase B 着手前に `legendre_bddAbove` を埋める。
- **`cgf_sum_eq_nsmul` の `h_int i` plumbing が肥大**: `IdentDistrib.integrable_iff` (Mathlib `Probability/IdentDistrib`) で `h_int 0` から `h_int i` を導出する補助 5 行を private に追加。

---

## Phase B — Cramér upper bound 📋

### スコープ

`measure_ge_le_exp_cgf` (Chernoff bound) を `X := ∑ X_i`, `ε := n · a`, `t := λ ≥ 0` で起動 → `(1/n) log` 取って `λ` で `sup` 取り、`limsup ≤ -cramerRate (X 0) μ a` を確立。**Tier 1 = L-C1 撤退ライン**。

**proof-log**: yes (Tier 1 publish 時点で `proof-log-cramer-tier1.md` を append)。

### Done 条件

- `cramer_upper` 主定理 `limsup ≤ -cramerRate (X 0) μ a` (signature §Goal 参照)
- (任意) `cramer_upper_dotEq` (`DotEq` 形 upper-only corollary)

### ステップ

- [ ] **B-1 statement 形確定** (judgement #2 で確定): `Tendsto` 直書きを main, `DotEq` を corollary に。`Asymptotic.lean:116` `dotEq_iff_tendsto_log_div` で往復。

- [ ] **B-2 Chernoff bound 単項起動**:
  ```lean
  lemma chernoff_bound_n_iid {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
      [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
      (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
      (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
      (h_int : ∀ t i, Integrable (fun ω => Real.exp (t * X i ω)) μ)
      (a : ℝ) (n : ℕ) (lam : ℝ) (h_lam : 0 ≤ lam) :
      μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω}
        ≤ Real.exp (-(n : ℝ) * (lam * a - cgf (X 0) μ lam))
  ```
  - `measure_ge_le_exp_cgf [IsFiniteMeasure μ]` で `≤ exp (-lam * (n*a) + cgf (∑ X_i) μ lam)`
  - A-5 `cgf_sum_eq_nsmul` で `cgf (∑ X_i) μ lam = n · cgf (X 0) μ lam`
  - 指数の引き算 + 因数化で `exp (-n · (lam · a - cgf (X 0) μ lam))`
  - `[IsFiniteMeasure μ]` は `IsProbabilityMeasure.toIsFiniteMeasure` instance で自動
  - **integrability**: bounded RV `|X i ω| ≤ M` ⇒ `exp (lam * X i ω) ≤ exp (|lam| · M)` で `Integrable` (定数関数で支配)。**`h_int` は実際は `h_bdd` から自動導出可能** → Phase B-3 で `h_int` を Phase B 内部で導出する補助 (~10 行) を作る (judgement #4 候補)。
  - ~30-40 行

- [ ] **B-3 `h_int` automation from `h_bdd`** (bounded RV ⇒ universal integrability):
  ```lean
  lemma integrable_exp_mul_of_bounded {Ω : Type*} [MeasurableSpace Ω]
      {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ}
      (hY_meas : Measurable Y) (h_bdd : ∃ M, ∀ ω, |Y ω| ≤ M) (t : ℝ) :
      Integrable (fun ω => Real.exp (t * Y ω)) μ
  ```
  - `|t * Y ω| ≤ |t| · M` ⇒ `exp (t * Y ω) ≤ exp (|t| · M)` (定数で支配)
  - `Measurable.exp` + `Measurable.const_mul` で measurability、`Integrable.of_bound_of_measurable` で integrability
  - ~10-15 行
  - これにより `cramer_upper` の signature から `h_int` を完全排除可能。**B-1 と合わせて signature を `h_bdd` のみに統一**するか judgement #5 で決定。

- [ ] **B-4 `(1/n) log` 取って `λ` で `sup`**:
  - B-2 から `μ.real {...} ≤ exp(-n · (lam · a - Λ(lam)))`
  - 両辺 `Real.log` (`μ.real {...} ≥ 0` のとき `log` 可、`μ.real {...} = 0` の場合は別 case で `-∞ ≤ ...` trivial)
  - `(1/n) log (μ.real {...}) ≤ -(lam · a - Λ(lam))`
  - A-3 `legendre_apply_le` で `lam · a - Λ(lam) ≤ legendre Λ a` ⇒ `-(lam · a - Λ(lam)) ≥ -legendre Λ a` (向き注意)
  - **但し**: ここで欲しいのは `(1/n) log (...) ≤ -legendre Λ a` だが、上の不等式は `≤ -(lam · a - Λ(lam))` で、`lam` を `sup` で動かして「最も小さい右辺」を取って sandwich する必要がある。具体的には:
    - `(1/n) log (...) ≤ inf_{lam ≥ 0} (-(lam · a - Λ(lam)))`
    - `inf_{lam ≥ 0} (-(lam · a - Λ(lam))) = -sup_{lam ≥ 0} (lam · a - Λ(lam))`
    - `a ≥ E[X]` のとき `sup_{lam ≥ 0} (lam · a - Λ(lam)) = sup_{lam ∈ ℝ} (lam · a - Λ(lam)) = legendre Λ a` (凸最大化の標準結果、`lam < 0` で `lam · a - Λ(lam) < 0 · a - Λ(0) = 0 ≤ legendre Λ a`)
  - **凸最大化補題** `legendre_eq_sup_nonneg` (~20-30 行) を A-3 の補強として追加:
    ```lean
    lemma legendre_eq_sup_nonneg (Λ : ℝ → ℝ) (a : ℝ) (h_E_le_a : Λ 0 = 0 ∧ a ≥ deriv Λ 0)
        (h_bdd : BddAbove ((fun lam : ℝ => lam * a - Λ lam) '' Set.Ici 0)) :
        legendre Λ a = sSup ((fun lam : ℝ => lam * a - Λ lam) '' Set.Ici 0)
    ```
    `a ≥ E[X] = Λ'(0)` 仮定下で `lam ≥ 0` 側の sup と全 `lam ∈ ℝ` の sup が一致 (凸関数の Legendre 双対)
  - `a < E[X]` case は `cramer_upper` が trivial (`a · n` が `S_n` の典型値より小 ⇒ `μ.real {...} ≈ 1`、対応する `legendre = 0`)。**`a ≥ E[X]` を仮定として追加するか trivial case で吸収するかは Phase B-4 着手時に判断 (judgement 候補)**。
  - ~30-50 行

- [ ] **B-5 `limsup` 形 wrap-up**:
  - B-4 から各 `n` で `(1/n) log (μ.real {...}) ≤ -legendre Λ a + 0 · (1/n)` (sup 取り終わった後は `n` 非依存)
  - `Filter.limsup_le_iff_of_eventually` で `limsup ≤ -legendre Λ a`
  - **`μ.real {ω | n · a ≤ S_n}` が 0 となる `n` の扱い**: `log 0 = 0` (Mathlib convention) でも `(1/n) · 0 = 0`、上界 `-legendre Λ a` が `≤ 0` 維持なら問題なし。`legendre Λ a ≥ 0` (A-4) で OK。
  - ~20-30 行

- [ ] **B-6 verify**: `lake env lean Common2026/Shannon/Cramer.lean` clean、Phase B 本体 0 sorry、Phase C-D は `sorry` 残し。**Tier 1 publish 候補時点** = L-C1 撤退ラインで切るならここで `Common2026.lean` 編入 (Phase D-4 を前倒し)。

### 工数感

~140-200 行 (B-2 ~40 + B-3 ~15 + B-4 ~50 + B-5 ~30 + plumbing ~20)。0.75-1 session。proof-log `yes`。

### 失敗時 fallback

- **B-4 の `a ≥ E[X]` 場合分けが肥大化**: `cramer_upper` の signature に `(h_a : a ≥ μ[X 0])` (`E_p[X 0]`) を仮定として追加。`a < E[X]` 形は trivial (upper bound `0 ≤ 1` を `log` 取って `(1/n) log 1 = 0 ≤ -0 = -legendre Λ (E[X]) = 0`) として別 trivial lemma で吸収。これは L-C3 への部分的縮退、main statement の generality を犠牲にしてでも publish 確度を優先。

---

## Phase C — Cramér lower bound (tilted change-of-measure) 📋

### スコープ

`λ^*` を `Λ'(λ^*) = a` で取り、tilted 測度 `μ_{λ^*} := μ.tilted (λ^* * X 0 ·)` 構築 → tilted 下 LLN で `μ_{λ^*}({|S̄_n - a| ≤ ε}) → 1` → change-of-measure で `μ` 側に戻して `liminf ≥ -cramerRate`。**Tier 2 = 理想形**。

**proof-log**: yes (Tier 2 publish 時点で `proof-log-cramer-tier2.md` を append)。

### Done 条件

- `cramer_lower` 主定理 `-cramerRate ≤ liminf ...` (signature §Goal 参照)
- `klDiv_tilted_eq` 補助補題 (KL-of-tilted 恒等式)

### ステップ

- [ ] **C-1 `klDiv_tilted_eq`** (in-essence KL-of-tilted 恒等式):
  ```lean
  lemma klDiv_tilted_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX_meas : Measurable X)
      (lam : ℝ) (h_int : Integrable (fun ω => Real.exp (lam * X ω)) μ) :
      ∫ ω, Real.log ((μ.tilted (fun ω' => lam * X ω')).rnDeriv μ ω).toReal ∂(μ.tilted (fun ω' => lam * X ω'))
        = lam * ∫ ω, X ω ∂(μ.tilted (fun ω' => lam * X ω')) - cgf X μ lam
  ```
  - `log_rnDeriv_tilted_left_self` (Mathlib `Tilted.lean:366`) で RN-log を `lam * X ω - cgf X μ lam` に展開
  - 線形性で右辺の `lam * (μ_lam)[X] - cgf X μ lam` に到達
  - **`klDiv` Mathlib (`ℝ≥0∞` 値) 直接形でなく `∫ log (rnDeriv)` 形で書く**。`klDiv` から `∫ log (rnDeriv)` への bridge が散らかるなら **後者 (積分形) のみ** で本 plan 内完結 → judgement candidate。
  - ~30-50 行

- [ ] **C-2 tilted の確率測度性 + 平均**:
  ```lean
  have h_tilted_prob : IsProbabilityMeasure (μ.tilted (fun ω => lam * X ω))
  have h_tilted_mean : ∫ ω, X ω ∂(μ.tilted (fun ω => lam * X ω)) = deriv (cgf X μ) lam
  ```
  - `isProbabilityMeasure_tilted` (Mathlib `Tilted.lean:126`) — bounded RV ⇒ `h_int` 全 `lam` で OK
  - `integral_tilted_mul_self` (Mathlib `Tilted.lean:132`) — `interior (integrableExpSet X μ)` 前提だが bounded RV では `integrableExpSet = univ` ⇒ `interior = univ` ⇒ 自明
  - ~15-25 行 (`integrableExpSet = univ` 補助補題 `integrableExpSet_univ_of_bounded` 込み、B-3 と兄弟)

- [ ] **C-3 tilted 下 LLN (in-probability 弱形)**:
  - **option (i)**: Mathlib `ProbabilityTheory.strong_law_ae` / `tendsto_average_of_iid` 系を tilted 下で使う
    - 困難: tilted measure 下で **n-IID 再構築** (`infinitePi (μ.tilted f) ?= (infinitePi μ).tilted (∑ f ∘ proj i)`)。Mathlib に直接 lemma があるか要 loogle。無ければ自前 ~30-50 行 plumbing。
  - **option (ii) (推奨)**: tilted 下分散 `Λ''(λ^*)` を `variance_tilted_mul` (Mathlib `Tilted.lean:159`) で取り、**Chebyshev 直接**で in-probability LLN を取る (弱形で十分):
    ```lean
    have h_var : Var[X 0; μ.tilted (lam * X 0 ·)] = iteratedDeriv 2 (cgf (X 0) μ) lam
    -- Chebyshev: μ_lam ({|S̄_n - a| ≥ ε}) ≤ Var / (n · ε²)
    -- → μ_lam ({|S̄_n - a| < ε}) → 1
    ```
    - bounded RV では `Λ''(λ^*)` 有限 (`X` 有界 ⇒ `Var[X]` 有界)
    - **n-IID tilted** の問題は同じ (`(infinitePi μ).tilted (∑ ...)` の n-IID 性) だが、Chebyshev は **分散の加法性 (independence) のみ要求** で **`Var[S_n^{μ_lam}] = n · Var[X 0; μ_lam]` が pointwise に成立すれば OK**。`iIndepFun.variance_sum` (Mathlib? — 要 loogle 確認、無ければ ~20-30 行 自前) で取れる想定。
  - ~50-80 行

- [ ] **C-4 change-of-measure (Radon-Nikodym)**:
  ```lean
  -- 主不等式:
  -- μ ({n*a ≤ S_n})
  --   ≥ ∫ ω ∈ {|S̄_n - a| ≤ ε} dμ
  --   = ∫ ω ∈ {...} (dμ / dμ_lam) dμ_lam
  --   = ∫ ω ∈ {...} exp(-lam * S_n + n * Λ(lam)) dμ_lam
  --   ≥ exp(-lam * n * (a + ε) + n * Λ(lam)) · μ_lam({...})
  --   ≥ exp(-n · (lam * a - Λ(lam) + lam * ε)) · (1 - δ)
  ```
  - `tilted_apply'` / `rnDeriv_tilted_left_self` で RN derivative を `(exp(lam * X) / mgf X μ lam)` 形に
  - n-letter 化: `rnDeriv ((infinitePi μ).tilted (∑ lam * X i)) (infinitePi μ) ∝ exp(lam * S_n) / mgf^n` (n-IID tilted plumbing、~30-50 行)
  - **`{|S̄_n - a| ≤ ε} ⊆ {n*a ≤ S_n + n*ε}` から `{n*(a-ε) ≤ S_n}` ⊆ {original set}` への containment**: ε を吸収させる順序が肝心
  - ~80-100 行

- [ ] **C-5 `liminf` 形 wrap-up**:
  - C-4 から `(1/n) log (μ.real {...}) ≥ -(lam * a - Λ(lam)) - lam * ε - (log (1 - δ)) / n`
  - `n → ∞` で右辺 → `-(lam * a - Λ(lam)) - lam * ε`
  - `lam := lam^*` (`Λ'(lam^*) = a` のもの) で `-(lam^* * a - Λ(lam^*)) = -legendre Λ a` (最適化条件)
  - `ε → 0` で `-legendre Λ a ≤ liminf ...`
  - 「`ε` を取って `n → ∞` を取って `ε → 0`」の二重極限を `Filter.liminf` の monotonicity で正当化
  - ~30-50 行

- [ ] **C-6 verify**: `lake env lean Common2026/Shannon/Cramer.lean` clean、Phase C 本体 0 sorry。

### 工数感

~200-300 行 (C-1 ~40 + C-2 ~20 + C-3 ~60 + C-4 ~80 + C-5 ~40)。1-1.5 session。proof-log `yes`。

### 失敗時 fallback

- **C-3 tilted 下 LLN の n-IID 再構築 (`infinitePi (μ.tilted) = (infinitePi μ).tilted ?`) が 1 session 以上**: 撤退ライン L-C2 発動 → `cramer_lower` の signature に **`h_lln : ∀ ε > 0, Tendsto (fun n => μ_lam ({ω | |S̄_n - a| < ε})) atTop (𝓝 1)` を仮定として追加**。tilted-LLN 整備は別 plan (`cramer-lln-plan.md`) に切り出し。本 plan の `cramer_lower` は **仮定形 publish** で先に着地。
- **C-4 RN-deriv の n-letter 化が `infinitePi` 上で `tilted` と非可換**: Mathlib に直接 lemma がなければ、**n-letter 形を `Measure.pi (fun _ : Fin n => μ)` で代替** (有限 IID 形に縮退、`Fin n` で十分)。`cramer_lower` の statement で `∑ i ∈ Finset.range n, X i` を `Fin n → ℝ` 経由で書き直し。これは asymptotic 結果に影響しない (各 `n` で `Fin n` 形と `ℕ` 形は equiv)。

---

## Phase D — 主定理 wrapper + library 編入 📋

### スコープ

`cramer_upper` (Phase B) + `cramer_lower` (Phase C) を sandwich して `cramer_tendsto` (optional) を作り、`Common2026.lean` に編入。

**proof-log**: no (skeleton 揃ったあとの整地)。

### Done 条件

- `cramer_tendsto` `Tendsto` 形 publish (Phase B + C sandwich)
- (任意) `cramer_dotEq` corollary (`μ.real {n*a ≤ S_n} ≐ exp(-n · cramerRate (X 0) μ a)`)
- `Common2026.lean` 更新 (`import Common2026.Shannon.Cramer`)
- `lake env lean Common2026/Shannon/Cramer.lean` clean (0 sorry, 0 warning)
- `lake env lean Common2026.lean` clean (library root)

### ステップ

- [ ] **D-1 `cramer_tendsto` sandwich**:
  ```lean
  theorem cramer_tendsto
      {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ)
      (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
      (h_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
      (h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M)
      (a : ℝ) (h_lam : ∃ lam : ℝ, 0 ≤ lam ∧ deriv (cgf (X 0) μ) lam = a) :
      Tendsto (fun n : ℕ =>
          (1 / (n : ℝ)) * Real.log
            (μ.real {ω | (a : ℝ) * n ≤ ∑ i ∈ Finset.range n, X i ω})) atTop
        (𝓝 (-cramerRate (X 0) μ a))
  ```
  - `tendsto_of_le_liminf_of_limsup_le` で `cramer_lower` + `cramer_upper` から `Tendsto`
  - ~10-15 行

- [ ] **D-2 `cramer_dotEq` corollary** (任意):
  - `dotEq_iff_tendsto_log_div` (`Asymptotic.lean:116`) 経由で `μ.real {...} ≐ exp(-n · cramerRate ...)` を提示
  - ~5-10 行

- [ ] **D-3 final verify**: `lake env lean Common2026/Shannon/Cramer.lean` clean (0 sorry, 0 warning)

- [ ] **D-4 library root 編入**:
  - `Common2026.lean` に `import Common2026.Shannon.Cramer` 追記
  - `lake env lean Common2026.lean` clean 確認
  - ~2-3 行

### 工数感

~30-50 行 (D-1 ~15 + D-2 ~10 + D-3 ~0 + D-4 ~3)。0.25 session。proof-log `no`。

### 失敗時 fallback

- **D-1 sandwich で `tendsto_of_le_liminf_of_limsup_le` の型が合わない (`liminf ≤ a ≤ limsup` 形と本 plan の `-cramerRate ≤ liminf` / `limsup ≤ -cramerRate` の向きが逆)**: `Filter.liminf_le_limsup` で挟むことができれば `Tendsto` に持ち上がる、Mathlib `Filter.tendsto_of_le_liminf_of_limsup_le` の正確な signature を Phase D 着手時に loogle 再確認。

---

## 撤退ライン

### Scope 縮小ライン (発動時に T1-C 完成形を縮小して publish)

- **L-C1**: **Cramér upper bound のみ publish** (~250 行, Tier 1)
  - 発動条件: Phase C で tilted change-of-measure の n-IID 化 (`(infinitePi μ).tilted (∑ ...)` の RN derivative) が **1 session 以上**詰まる
  - 縮退後: `cramer_upper` + `legendre_apply_le` + `legendre_nonneg` + (任意) `cramer_upper_dotEq` のみで publish。Cover-Thomas でも upper bound は **単独で有用** (Chernoff bound の n-IID 強化版 = "exponential tail bound" として実用)。`cramer_lower` は別 plan (`cramer-achievability-plan.md`) に切り出し。

- **L-C2**: **Cramér lower bound を仮定形 publish** (~350 行, Tier 1.5)
  - 発動条件: Phase C-3 (tilted 下 LLN) が組めない (Mathlib `infinitePi (tilted) = (infinitePi) tilted` 等の直接 lemma 不在で plumbing 100 行を超える)
  - 縮退後: `cramer_lower` の signature に **`h_lln : ∀ ε > 0, Tendsto (fun n => (μ.tilted (lam^* * X 0 ·))^∞ ({ω | |S̄_n - a| < ε})) atTop (𝓝 1)` を仮定として追加**。Cramér lower bound の statement は完成形だが、tilted-LLN 整備は defer (別 plan に切り出し、本 plan の補助補題でなく `cramer-tilted-lln-plan.md` などで)。

- **L-C3**: **finite-alphabet `α → ℝ` 専用形に限定** (~250 行, Tier 0.5)
  - 発動条件: 一般 `Ω → ℝ` bounded RV 形でも `integrableExpSet = univ` 自明化補助が散らかる (B-3 `integrable_exp_mul_of_bounded` の証明が 30 行を超える) など
  - 縮退後: ambient を `Ω := Fin n → α` (n-IID finite alphabet) に specialize、`X i := f ∘ (proj i)` for `f : α → ℝ`、Mathlib `Measure.pi (fun _ : Fin n => p)` を直接使う。**~50 行 plumbing で済む**が、statement の generality を犠牲。

### 自作 plumbing 肥大ライン (新規)

(inventory §自作 5 + 在庫 §危険 から本 plan に正式 import)

- **L-P1**: **`legendre` 自前定義の規模超過** (Tier 0 baseline で 60 行を超える、達成性 / 連続性 / 凸性 の証明が肥大化)
  - 縮退案: `legendre` の達成性 (`∃ λ^*, legendre Λ a = λ^* · a - Λ(λ^*)`) は **本 plan 内で証明しない**。`cramer_lower` の signature に `h_lam : ∃ lam, 0 ≤ lam ∧ deriv (cgf (X 0) μ) lam = a` 仮定として外出し (現状の plan signature と一致)。達成性証明は Tier 3 で `IsCompact.exists_sSup_image_eq` 経路 (`Chernoff.lean:161` chernoffInfo_attained と同型) で別 plan へ。

- **L-P2**: **`integral_tilted_mul_self` の `interior` 制約が想定外に詰まる** (bounded RV → `integrableExpSet = univ` の補助補題 `integrableExpSet_univ_of_bounded` が 30 行を超える)
  - 縮退案: `cramer_lower` の signature に `h_int_set : integrableExpSet (X 0) μ = Set.univ` を仮定として追加。bounded RV 仮定が radius `M` で `exp (t * X i ω) ≤ exp (|t| * M)` で支配される証明を **inline で 5 行**書く (整理は Tier 3 で)。

- **L-P3**: **`cgf` の `MeasureTheory` 名前空間衝突** (`InformationTheory.Shannon.Cramer` open scope と `MeasureTheory.cgf` の名前解決衝突)
  - 縮退案: `Cramer.lean` 内で `cgf` を fully qualified (`ProbabilityTheory.cgf`) で書く、または `open ProbabilityTheory` を local に追加 (Mathlib `Probability.Moments.Basic` の `cgf` 定義は `ProbabilityTheory` namespace 想定)。Phase A 着手時 (skeleton write 直後) に確認、衝突あれば judgement log に記録。

- **L-P4**: **1 session で完遂不能リスク** (Phase B + C を続けて 1 session 内で publish できない)
  - 縮退案: **Phase B (Tier 1) で 1 session 完結**を目標、Phase C は別 session に分離。Tier 1 baseline (~250 行) で L-C1 部分 publish 価値を確保。Tier 2 (Phase C, ~400 行) は 2nd session で独立に attack。判断ログで session 分割を記録。

---

## Risk table

| Risk | 発生確率 | 影響 | 緩和策 |
|---|---|---|---|
| **`legendre` 自前定義の規模超過** (Tier 0 baseline で 60 行超) | 低 | 低 (Phase A +20-30 行) | L-P1 発動で達成性証明を Tier 3 へ defer、`h_lam` 仮定で外出し (現状 plan 通り)。 |
| **`integral_tilted_mul_self` の `interior` 制約処理が `integrableExpSet = univ` 補助で肥大化** | 中 (inventory §危険 で特定済) | 中 (Phase C +30-50 行) | L-P2 発動、`h_int_set` 仮定で外出し。bounded RV 補助補題 `integrableExpSet_univ_of_bounded` は ~5-10 行で書ける見込み (Phase B-3 と兄弟、共用可能)。 |
| **`cgf` の `MeasureTheory` / `ProbabilityTheory` 名前空間衝突** | 中 (Mathlib `Probability.Moments.Basic` の namespace 確認要) | 低 (1-2 行 fix) | Phase A skeleton write 直後に `lake env lean` で確認、衝突あれば `open ProbabilityTheory` local + judgement log。 |
| **tilted 下 n-IID 再構築 (`infinitePi (μ.tilted) = (infinitePi μ).tilted ?`) が Mathlib に直接 lemma なし** | **高** (inventory §危険 で特定済) | **高** (Phase C +50-100 行 or L-C2 発動) | L-C2 発動で `h_lln` 仮定として外出し、tilted-LLN は別 plan へ。または Phase C-3 で Chebyshev 直接路 (option (ii)) を採用し、`iIndepFun.variance_sum` (要 loogle 確認) で n-IID 性を最小限に。 |
| **`measure_ge_le_exp_cgf` の `(h_int : Integrable ...)` 前提が `cramer_upper` の signature を汚染** | 中 | 低 (B-3 で `integrable_exp_mul_of_bounded` 自前補助で吸収) | B-3 補助補題 (~10-15 行) で `h_bdd → h_int` を導出、main signature から `h_int` を完全排除。判断ログ #4 候補。 |
| **`a ≥ E[X]` 場合分けが Phase B で肥大化** (`legendre_eq_sup_nonneg` の凸最大化補題が 30 行超) | 中 | 中 (Phase B +20-40 行) | B-4 fallback (`h_a : a ≥ μ[X 0]` 仮定として signature に追加) で `a < E[X]` trivial case を分離。statement の generality を犠牲にしてでも publish 確度を優先。 |
| **proof 規模が roadmap 上限 (500 行) を超える** | 低-中 | 中 (1 session で完走できない) | 撤退ライン L-C1〜L-C3 を Phase 単位で発動可能に設計済。Phase B 完了 (Tier 1, ~250 行) でも publish 価値あり (L-C1 縮退)。 |
| **Phase C-4 RN-deriv n-letter 化が `infinitePi` 上で詰まる** | 中-高 | 高 (Phase C +50-80 行 or L-C2 / L-C3 発動) | Phase C-4 fallback (`Measure.pi (fun _ : Fin n => μ)` 有限 IID 形に縮退) で n-letter 整地、`Fin n` 形で十分 (asymptotic 結果に影響なし)。 |
| **1 session で Tier 2 (Phase B + C) 完遂不能** | **中-高** | 中 (next session に持ち越し) | L-P4 発動: Tier 1 (Phase A + B) を session 1 で完遂、Tier 2 (Phase C) を session 2 へ分割。判断ログで session 分割を記録。 |

---

## 判断ログ

書く頻度: Phase 中の方針変更 / 撤退 / 当初仮定の修正があったとき。append-only。

1. **(2026-05-19) Sanov contraction principle 経路を不採用、Mathlib `cgf` + `Measure.tilted` 直接経路を採用**: roadmap §T1-C は「`SanovLDPEquality.lean` からほぼ含意」「Sanov LDP からの contraction principle 経由 reshape ~200 行」と見積もるが、inventory §H の **Sanov → Cramér bridge 難しさ分析** で「集合形 `Q^n(⋃ T_c)` から sample mean 形 `Q^n({x | a ≤ S̄_n})` への reshape が 2 段 (E_n 構成 + Donsker-Varadhan 双対) で各 80-150 行」と判明。一方 Mathlib `cgf` + `iIndepFun.cgf_sum` + `measure_ge_le_exp_cgf` + `Measure.tilted` が完備で、Cramér upper bound は **~80-120 行**、lower bound は **~120-180 行**で書ける。**Sanov を再利用しないことで -120 行**、加えて `SanovLDPEquality` / `SanovLDP` / `KLDivContinuous` / `CsiszarProjection` を **import 不要** で `Cramer.lean` を独立 file として保てる (CLAUDE.md `Import Policy` 厳守)。

2. **(2026-05-19) statement 形は `Tendsto` 直書きを main、`DotEq` を corollary に**: Common2026 既存 Stein / Sanov / Pinsker / Chernoff の主定理が全て `Tendsto` 直書き形を採用 (`stein_lemma`, `stein_strong_lemma`, `sanov_ldp_equality`, `chernoff_lemma` (T1-B plan の予定形))、Asymptotic.lean の `DotEq` は **wrapper notation** として後付け corollary 化する style が確立。本 plan も同 style: `cramer_upper` / `cramer_lower` / `cramer_tendsto` を main, `cramer_dotEq` を任意 corollary。Phase D で `dotEq_iff_tendsto_log_div` (`Asymptotic.lean:116`) を呼ぶだけで往復。

3. **(2026-05-19) finite-alphabet specialization (bounded RV) を採用、`integrableExpSet = univ` で `interior` 境界処理を回避**: inventory §E + §危険 1 で「`integral_tilted_mul_self` / `deriv_cgf` / `variance_tilted_mul` の `interior (integrableExpSet X μ)` 前提が一般 RV 形で +50-100 行 plumbing」「bounded RV では `integrableExpSet = univ` で `interior = univ` ⇒ 自明化」と特定済。本 plan は **`h_bdd : ∃ M, ∀ i ω, |X i ω| ≤ M` 仮定を signature に追加**して finite-alphabet (= textbook Cover-Thomas Theorem 11.4.1 の前提と同じ) に specialize。Tier 3 で一般 RV 形を別 plan (`cramer-general-plan.md`) に切り出す想定。

4. **(2026-05-19) `iidAmbientMeasure` (channel I/O ペア用) は使わず、`Measure.infinitePi (fun _ : ℕ => μ)` を直接使用**: inventory §G で「既存 `IIDProductInput.iidAmbientMeasure` は `α × β` (channel I/O ペア) 用で Cramér には冗長」「より軽い ambient `Measure.infinitePi (fun _ : ℕ => μ)` を直接使う」と推奨。本 plan の signature は `(X : ℕ → Ω → ℝ)` + `(h_indep : iIndepFun X μ)` の **`Ω` を抽象に保つ** 形を採用 (具体的 ambient `Ω := ℕ → α` などは caller 任せ)。これにより `IIDProductInput.lean` / `Channel.lean` の **import 不要**、`Cramer.lean` を独立 file として保てる (CLAUDE.md `Import Policy` 厳守)。
